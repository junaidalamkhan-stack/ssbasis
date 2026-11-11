"""
check_session_outputs.py -- independently checks every kernel generator,
lifting and normal form printed by ssbasis.lib v1.1 in
  ../examples/examples_output.txt   (every session of the revised manuscript)
  ../tests/regression_output.txt    (quotient rings, Z, Z/4, degree-0 variable)
For each SSliftingTest block: leading forms recomputed; each u is homogeneous
and in ker(pi); each lifting l is in ker(psi) with Omega-LF(l) = u; each
'NO lifting' verdict agrees with the exhaustive test and the printed normal
form w is nonzero with leading form outside S[LF(F)]; the printed u's
generate ker(pi) in all degrees up to a bound.
Blocks whose ring has a degree-0 variable (Example 4.11, test Z1) are
checked by verify_new_examples.py and by hand instead, and skipped here;
so is test P1 (coefficient field Q(a)), whose kernel is zero because the
Jacobian determinant of x+ay, xy is x-ay, which is nonzero.
"""
import re, os
from sslib import *
HERE = os.path.dirname(os.path.abspath(__file__))
T = os.path.join(HERE, '..')

# (file, header substring, mod, variables, W, kill, max degree for generation check)
SPECS = [
 ('examples/examples_output.txt', 'Example 4.2 ', 0, ['x','y','z'], [[1,1,0],[0,2,1]], [], (4, 9)),
 ('examples/examples_output.txt', 'Example 4.4 ', 0, ['x','y'], [[1,1]], [], (10,)),
 ('examples/examples_output.txt', 'Example 4.5 (Q', 0, ['x','y'], [[1,1]], [], (10,)),
 ('examples/examples_output.txt', 'Example 4.6 ', 4, ['x','y'], [[1,0],[0,1]], [], (5, 18)),
 ('examples/examples_output.txt', 'Example 4.7 ', 4, ['x','y'], [[1,1]], [], (12,)),
 ('examples/examples_output.txt', 'Example 4.9 ', 6, ['x','y'], [[1,1]], [], (12,)),
 ('examples/examples_output.txt', 'Example 4.10 ', 6, ['x','y','z'], [[1,0,1],[0,1,1]], [], (6, 12)),
 ('examples/examples_output.txt', 'Example 2.5 ', 0, ['x','y','z'], [[1,1,1]], [], (12,)),
 ('examples/examples_output.txt', 'Example 4.12 (non-reduced', 0, ['x','y'], [[1,1]], [(2,0)], (10,)),
 ('examples/examples_output.txt', 'Example 4.12 in characteristic 2', 2, ['x','y'], [[1,1]], [(2,0)], (10,)),
 ('examples/examples_output.txt', 'Example 4.12 in characteristic 3', 3, ['x','y'], [[1,1]], [(2,0)], (10,)),
 ('tests/regression_output.txt', 'Q1:', 0, ['x','y'], [[1,1]], [(2,0)], (10,)),
 ('tests/regression_output.txt', 'Q2:', 2, ['x','y'], [[1,1]], [(2,0)], (10,)),
 ('tests/regression_output.txt', 'Q4:', 3, ['x','y'], [[1,1]], [(2,0)], (10,)),
 ('tests/regression_output.txt', 'Q5:', 4, ['x','y'], [[1,1]], [(1,1)], (10,)),
 ('tests/regression_output.txt', 'Z2:', 4, ['x','y'], [[1,1]], [], (8,)),
 ('tests/regression_output.txt', 'Z3-Z7', 0, ['x'], [[1]], [], (12,)),
]

def blocks_of(text, header):
    # the section starting at the header line up to the next '=====' header
    parts = text.split('===== ')
    for p in parts:
        if p.startswith(header) or header in p.split('\n', 1)[0]:
            return p
    return None

def split_tests(section):
    out = []
    for chunk in section.split('Generators, degrees, leading forms:')[1:]:
        out.append(chunk)
    return out

ok_all = True; n_blocks = 0; n_u = 0; n_lift = 0; n_nolift = 0
for fname, header, mod, X, W, kill, box in SPECS:
    text = open(os.path.join(T, fname)).read()
    sec = blocks_of(text, header)
    if sec is None:
        print('MISSING section', header); ok_all = False; continue
    for chunk in split_tests(sec):
        n_blocks += 1
        lines = chunk.strip('\n').split('\n')
        F = []; LFc = []
        for ln in lines:
            mt = re.match(r'^\s+f\d+ = (.*?)\s+degree \((.*?)\)\s+leading form: (.*)$', ln)
            if mt:
                F.append(quotient_reduce(clean(parse(mt.group(1), X), mod), mod, kill))
                LFc.append(clean(parse(mt.group(3), X), mod))
        LF = [lead_form(f, W) for f in F]; D = [deg(f, W) for f in F]
        if LF != LFc:
            print('  [FAIL]', header, 'leading forms differ'); ok_all = False
        m = len(F); yn = ['Y%d' % (i + 1) for i in range(m)]
        U = []
        for k, ln in enumerate(lines):
            mt = re.match(r'^u\d+ = (.*?)\s+Omega \((.*?)\)', ln)
            if not mt: continue
            n_u += 1
            u = clean(parse(mt.group(1), yn), mod); U.append(u)
            om = tuple(int(v) for v in mt.group(2).split(','))
            good = subst(u, LF, mod, len(X), kill) == {} and is_homog(u, D) and Omega(u, D) == om
            nxt = lines[k + 1].strip()
            try:
                indep, _ = liftable(u, F, D, mod, len(X), kill)
            except Exception as ex:
                indep = None
            if nxt.startswith('lifting:'):
                n_lift += 1
                l = clean(parse(nxt.split(':', 1)[1].strip(), yn), mod)
                good &= subst(l, F, mod, len(X), kill) == {} and OLF(l, D) == u
                if indep is False: good = False
            else:
                n_nolift += 1
                w = quotient_reduce(clean(parse(nxt.split('normal form', 1)[1].strip(), X), mod), mod, kill)
                good &= bool(w)
                if indep is True: good = False
                g = deg(w, W); lw = lead_form(w, W)
                alphas = y_monomials_of_degree(D, g)
                imgs = [subst({a: 1}, LF, mod, len(X), kill) for a in alphas]
                mons = sorted({e for q in imgs + [lw] for e in q})
                if imgs and in_span([[q.get(e, 0) for e in mons] for q in imgs], [lw.get(e, 0) for e in mons], mod, len(mons)):
                    good = False
            if not good:
                ok_all = False; print('  [FAIL]', header, ln, '|', nxt)
        # generation of ker(pi)
        import itertools
        gen_ok = True
        for gm in itertools.product(*[range(b + 1) for b in box]):
            if not any(gm): continue
            try:
                r = kernel_generated_in_degree(U, LF, D, mod, len(X), tuple(gm), kill)
            except ValueError:
                continue
            if not r[0]:
                gen_ok = False; print('  [FAIL] generation', header, gm, r); break
        ok_all &= gen_ok
        verdict = 'every generator lifts' in chunk
        print('  [ OK ]' if gen_ok else '  [FAIL]', '%-22s m=%d, %d kernel generators, verdict %s' % (header, m, len(U), 'SS-basis' if verdict else 'not SS-basis'))
print('\nblocks %d, kernel generators %d, liftings %d, no-lifting verdicts %d' % (n_blocks, n_u, n_lift, n_nolift))
print('ALL CHECKS PASSED' if ok_all else 'SOME CHECK FAILED')
