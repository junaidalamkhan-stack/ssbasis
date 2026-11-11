"""
crosscheck_v11.py -- randomised comparison of the corrected library
ssbasis.lib (v1.1) with the independent checker sslib.py.

Rings: S[x,y] and S[x,y]/(m) for a monomial m in {x^2, xy, y^3},
S in {Q, F_3, Z/4, Z/6}; gradings: natural, or deg x = 1, deg y = 2.
For each case and each printed generator u of ker(pi):
  * u is Omega-homogeneous and pi(u) = 0 in R;
  * a printed lifting l satisfies psi(l) = 0 in R and Omega-LF(l) = u;
  * the verdict (lifting / no lifting) agrees with an exhaustive
    linear-algebra test;
  * for "NO lifting", the printed normal form w is nonzero in R and its
    leading form is NOT in S[LF(F)] (so it is not s-reducible);
and the printed u's generate ker(pi) in all degrees <= 8.
Usage: python3 crosscheck_v11.py NCASES SEED
"""
import random, subprocess, sys, os, re, tempfile
TLIM = 20
from sslib import *

HERE = os.path.dirname(os.path.abspath(__file__))
LIB = os.path.abspath(os.path.join(HERE, '..', 'ssbasis.lib'))
XN = ['x', 'y']
QUOT = {'none': [], 'x2': [(2, 0)], 'xy': [(1, 1)], 'y3': [(0, 3)]}
QSING = {'x2': 'x2', 'xy': 'xy', 'y3': 'y3'}

def rand_poly(mod, rng):
    p = {}
    for _ in range(rng.randint(1, 3)):
        a = rng.randint(0, 3); b = rng.randint(0, 3 - a)
        c = rng.randrange(1, mod) if mod else rng.choice([-3, -2, -1, 1, 2, 3])
        p[(a, b)] = p.get((a, b), 0) + c
    return clean(p, mod)

def ring_line(mod):
    if mod == 0: return 'ring r = 0,(x,y),dp;'
    if mod in (2, 3, 5, 7): return 'ring r = %d,(x,y),dp;' % mod
    return 'ring r = (integer,%d),(x,y),dp;' % mod

def lf_in_subalgebra(target, LF, D, mod, kill):
    """Is the homogeneous target (degree gamma) in S[LF] ?  S-span of pi(Y^alpha), deg alpha = gamma."""
    W = None
    gamma = None
    return None

def main():
    n = int(sys.argv[1]); seed = int(sys.argv[2])
    rng = random.Random(seed)
    cases = []
    while len(cases) < n:
        mod = rng.choice([0, 3, 4, 6])
        q = rng.choice(['none', 'x2', 'xy', 'y3'])
        W = rng.choice([[[1, 1]], [[1, 2]]])
        kill = QUOT[q]
        F = []
        for _ in range(rng.randint(1, 3)):
            p = quotient_reduce(rand_poly(mod, rng), mod, kill)
            if p and deg(p, W) != (0,):
                F.append(p)
        if F:
            cases.append((mod, q, W, F))
    out = ''
    timeouts = []
    for i, (mod, q, W, F) in enumerate(cases):
        lines = ['LIB "%s";' % LIB]
        lines.append('"@@CASE %d";' % i)
        lines.append(ring_line(mod))
        if q != 'none':
            lines.append('qring qq = std(ideal(%s));' % QSING[q])
        lines.append('ideal G = %s;' % ', '.join(fmt(f, XN) for f in F))
        lines.append('intmat W[1][2] = %d,%d;' % tuple(W[0]))
        lines.append('SSliftingTest(G, W);')
        if q != 'none':
            lines.append('kill qq;')
        lines.append('kill r;')
        lines.append('quit;')
        with tempfile.NamedTemporaryFile('w', suffix='.sing', delete=False) as fh:
            fh.write('\n'.join(lines)); path = fh.name
        try:
            out += subprocess.run(['Singular', '-q', path], capture_output=True, text=True, timeout=TLIM).stdout
        except subprocess.TimeoutExpired:
            timeouts.append(i)
        os.unlink(path)
    blocks = {int(b.split('\n', 1)[0]): b for b in out.split('@@CASE ')[1:]}
    st = dict(cases=0, quotient_cases=0, us=0, lifts=0, nolifts=0, mismatch=0, bad_lift=0,
              nonhom=0, bad_nf=0, gen_fail=0, errors=0)
    probs = []
    st['timeouts'] = len(timeouts)
    for i, (mod, q, W, F) in enumerate(cases):
        if i in timeouts:
            probs.append((i, 'timeout (%d s)' % TLIM, '')); continue
        blk = blocks.get(i, '')
        if 'RESULT' not in blk:
            st['errors'] += 1; probs.append((i, 'no result', blk[:300])); continue
        st['cases'] += 1
        if q != 'none': st['quotient_cases'] += 1
        kill = QUOT[q]
        m = len(F); yn = ['Y%d' % (j + 1) for j in range(m)]
        LF = [lead_form(f, W) for f in F]; D = [deg(f, W) for f in F]
        # parse
        L = blk.split('\n'); U = []
        for k, ln in enumerate(L):
            mt = re.match(r'^u\d+ = (.*?)\s+Omega', ln)
            if not mt: continue
            u = clean(parse(mt.group(1), yn), mod); U.append(u); st['us'] += 1
            if subst(u, LF, mod, 2, kill) != {} or not is_homog(u, D):
                st['nonhom'] += 1; probs.append((i, 'u not homogeneous in ker pi', mt.group(1)))
            indep, _ = liftable(u, F, D, mod, 2, kill)
            nxt = L[k + 1].strip()
            if nxt.startswith('lifting:'):
                st['lifts'] += 1
                l = clean(parse(nxt.split(':', 1)[1].strip(), yn), mod)
                if subst(l, F, mod, 2, kill) != {} or OLF(l, D) != u:
                    st['bad_lift'] += 1; probs.append((i, 'bad lifting', nxt))
                if not indep:
                    st['mismatch'] += 1; probs.append((i, 'lifts per Singular, not per checker', mt.group(1)))
            elif nxt.startswith('NO lifting'):
                st['nolifts'] += 1
                if indep:
                    st['mismatch'] += 1; probs.append((i, 'no lifting per Singular, lifts per checker', mt.group(1)))
                w = clean(parse(nxt.split('normal form', 1)[1].strip(), XN), mod)
                w = quotient_reduce(w, mod, kill)
                ok = bool(w)
                if ok:
                    g = deg(w, W); lw = lead_form(w, W)
                    try:
                        alphas = y_monomials_of_degree(D, g)
                    except ValueError:
                        alphas = []
                    imgs = [subst({a: 1}, LF, mod, 2, kill) for a in alphas]
                    mons = sorted({e for p in imgs + [lw] for e in p})
                    vecs = [[p.get(e, 0) for e in mons] for p in imgs]
                    b = [lw.get(e, 0) for e in mons]
                    if vecs and in_span(vecs, b, mod, len(mons)):
                        ok = False
                if not ok:
                    st['bad_nf'] += 1; probs.append((i, 'normal form is s-reducible or zero', nxt))
        for gdeg in range(1, 9):
            okg, a, b = kernel_generated_in_degree(U, LF, D, mod, 2, (gdeg,), kill)
            if not okg:
                st['gen_fail'] += 1; probs.append((i, 'ker pi not generated in degree %d' % gdeg, (a, b))); break
    print('seed', seed, st)
    for p in probs[:10]:
        print('PROBLEM', p, 'over', 'Q' if cases[p[0]][0]==0 else 'Z/%d' % cases[p[0]][0], 'quotient', cases[p[0]][1], 'W', cases[p[0]][2], 'F', [fmt(f, XN) for f in cases[p[0]][3]])

if __name__ == '__main__':
    main()
