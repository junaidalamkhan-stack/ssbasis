"""
sslib.py -- small, self-contained tools for checking SS-basis computations.

Everything is implemented from scratch (dict-based polynomials, exact
integer / rational arithmetic) so that the checks are independent of
Singular.  Coefficient rings supported:

    mod = 0   : the integers Z (or Q when Fractions appear)
    mod = n>1 : Z/nZ   (n need not be prime)

Polynomials are dicts {exponent tuple: coefficient}.  A grading is a weight
matrix W (list of rows); the degree of x^a is the tuple W.a, compared
lexicographically (Python tuple order), first row first -- this is the
convention of the manuscript and of the supplied Singular code.
"""
from fractions import Fraction
from itertools import product
from math import gcd
import re

# --------------------------------------------------------------------------
# basic polynomial arithmetic
# --------------------------------------------------------------------------

def norm(c, mod):
    return c % mod if mod else c

def clean(p, mod):
    out = {}
    for e, c in p.items():
        c = norm(c, mod)
        if c != 0:
            out[e] = c
    return out

def add(p, q, mod, s=1):
    r = dict(p)
    for e, c in q.items():
        r[e] = r.get(e, 0) + s * c
    return clean(r, mod)

def sub(p, q, mod):
    return add(p, q, mod, -1)

def scal(c, p, mod):
    return clean({e: c * v for e, v in p.items()}, mod)

def mul(p, q, mod):
    r = {}
    for e1, c1 in p.items():
        for e2, c2 in q.items():
            e = tuple(a + b for a, b in zip(e1, e2))
            r[e] = r.get(e, 0) + c1 * c2
    return clean(r, mod)

def one(n):
    return {tuple([0] * n): 1}

def power(p, k, mod, n):
    r = one(n)
    for _ in range(k):
        r = mul(r, p, mod)
    return r

def quotient_reduce(p, mod, kill):
    """Reduce modulo a monomial ideal given by a list of exponent tuples
    (used for R = S[x]/(monomials), e.g. K[x,y]/(x^2))."""
    if not kill:
        return p
    out = {}
    for e, c in p.items():
        if any(all(a >= b for a, b in zip(e, k)) for k in kill):
            continue
        out[e] = c
    return clean(out, mod)

def subst(P, images, mod, nx, kill=()):
    """Evaluate P in S[Y_1..Y_m] at Y_i -> images[i] (polys in nx variables)."""
    m = len(images)
    cache = {}
    def pw(i, k):
        if (i, k) not in cache:
            cache[(i, k)] = quotient_reduce(power(images[i], k, mod, nx), mod, kill)
        return cache[(i, k)]
    r = {}
    for e, c in P.items():
        t = one(nx)
        for i, k in enumerate(e):
            if k:
                t = quotient_reduce(mul(t, pw(i, k), mod), mod, kill)
        r = add(r, scal(c, t, mod), mod)
    return quotient_reduce(r, mod, kill)

# --------------------------------------------------------------------------
# gradings, degrees, leading forms
# --------------------------------------------------------------------------

def mdeg(e, W):
    return tuple(sum(w * a for w, a in zip(row, e)) for row in W)

def deg(p, W):
    return max(mdeg(e, W) for e in p) if p else None

def lead_form(p, W):
    d = deg(p, W)
    return {e: c for e, c in p.items() if mdeg(e, W) == d}

def is_homog(P, D):
    """P in S[Y], D = list of generator degrees (tuples)."""
    degs = {formal_deg(e, D) for e in P}
    return len(degs) <= 1

def formal_deg(alpha, D):
    k = len(D[0])
    return tuple(sum(a * d[j] for a, d in zip(alpha, D)) for j in range(k))

def Omega(P, D):
    return max(formal_deg(e, D) for e in P) if P else None

def OLF(P, D):
    g = Omega(P, D)
    return {e: c for e, c in P.items() if formal_deg(e, D) == g}

# --------------------------------------------------------------------------
# parsing polynomials written in Singular / plain notation
# --------------------------------------------------------------------------

_term_re = re.compile(r'([+-]?)([^+-]+)')

def parse(s, names):
    """Parse things like '3*Y1^2*Y3-Y2+4', 'xy3+2y', 'x^2*y-3', 'Y(1)*Y(2)'.
    names: list of variable names (single- or multi-character)."""
    s = s.replace(' ', '').replace('Y(', 'Y').replace(')', '')
    n = len(names)
    order = sorted(range(n), key=lambda i: -len(names[i]))
    poly = {}
    if s in ('', '0'):
        return poly
    for sign, body in _term_re.findall(s):
        coef = 1
        e = [0] * n
        rest = body.replace('*', '')
        m = re.match(r'^(\d+)(?:/(\d+))?', rest)
        if m:
            coef = int(m.group(1)) if m.group(2) is None else Fraction(int(m.group(1)), int(m.group(2)))
            rest = rest[m.end():]
        while rest:
            for i in order:
                nm = names[i]
                if rest.startswith(nm):
                    rest = rest[len(nm):]
                    m = re.match(r'^\^?(\d+)', rest)
                    k = 1
                    if m and not (len(nm) == 1 and nm.isalpha() and False):
                        # exponent: either '^k' or (short Singular form) digits
                        k = int(m.group(1))
                        rest = rest[m.end():]
                    e[i] += k
                    break
            else:
                raise ValueError('cannot parse %r in %r' % (rest, s))
        c = -coef if sign == '-' else coef
        poly[tuple(e)] = poly.get(tuple(e), 0) + c
    return {e: c for e, c in poly.items() if c != 0}

def fmt(p, names):
    if not p:
        return '0'
    def key(e):
        return (sum(e), e)
    parts = []
    for e in sorted(p, key=key, reverse=True):
        c = p[e]
        mono = '*'.join(nm + ('^%d' % k if k > 1 else '') for nm, k in zip(names, e) if k)
        if mono == '':
            s = str(c)
        elif c == 1:
            s = mono
        elif c == -1:
            s = '-' + mono
        else:
            s = '%s*%s' % (c, mono)
        parts.append(s)
    out = '+'.join(parts).replace('+-', '-')
    return out

# --------------------------------------------------------------------------
# linear algebra over Z/n (n arbitrary) via subgroup orders, and over Q / F_p
# --------------------------------------------------------------------------

def _xgcd(a, b):
    if b == 0:
        return (a, 1, 0) if a >= 0 else (-a, -1, 0)
    g, s, t = _xgcd(b, a % b)
    return g, t, s - (a // b) * t

def subgroup_order(vectors, n, length):
    """Order of the subgroup of (Z/n)^length generated by `vectors`.
    Howell-style elimination: unimodular row operations mod n, and after each
    pivot g in a column the row (n/g)*pivot is added back to the pool."""
    rows = [[v % n for v in vec] for vec in vectors]
    rows = [r for r in rows if any(r)]
    index = 1
    for j in range(length):
        piv = None
        others = []
        for r in rows:
            if r[j] % n == 0:
                others.append(r)
                continue
            if piv is None:
                piv = r
                continue
            a, b = piv[j], r[j]
            d, s, t = _xgcd(a, b)
            newp = [(s * x + t * y) % n for x, y in zip(piv, r)]
            newr = [((b // d) * x - (a // d) * y) % n for x, y in zip(piv, r)]
            piv = newp
            if any(newr):
                others.append(newr)
        if piv is None:
            index *= n
            rows = others
            continue
        a = piv[j]
        g, s, t = _xgcd(a, n)
        # new pivot s*piv + t*n*e_j  (entry g in column j)
        newp = [(s * x) % n for x in piv]
        newp[j] = g % n if g != n else 0
        extra = [((n // g) * x) % n for x in piv]       # (n/g)*old pivot
        extra2 = [((a // g) * x) % n for x in newp]     # consistency (in span)
        rest = [r for r in others if any(r)]
        if any(extra):
            rest.append(extra)
        # eliminate column j from the rest using newp (entry g divides all)
        cleaned = []
        for r in rest:
            if r[j] % n:
                q = (r[j] // g) if r[j] % g == 0 else None
                assert q is not None, 'gcd bookkeeping failed'
                r = [(x - q * y) % n for x, y in zip(r, newp)]
            if any(r):
                cleaned.append(r)
        # the multiple (n/g)*newp has zero in column j; keep it as well
        extra3 = [((n // g) * x) % n for x in newp]
        if any(extra3):
            cleaned.append(extra3)
        index *= g
        rows = cleaned
    return n ** length // index

def in_span_mod(vectors, b, n, length):
    return subgroup_order(vectors, n, length) == subgroup_order(list(vectors) + [b], n, length)

def rank_field(vectors, p=0):
    """Rank over Q (p=0) or F_p (p prime)."""
    rows = []
    for v in vectors:
        rows.append([Fraction(x) if p == 0 else x % p for x in v])
    if not rows:
        return 0
    ncol = len(rows[0])
    r = 0
    for j in range(ncol):
        pr = None
        for i in range(r, len(rows)):
            if rows[i][j] != 0:
                pr = i
                break
        if pr is None:
            continue
        rows[r], rows[pr] = rows[pr], rows[r]
        inv = (1 / rows[r][j]) if p == 0 else pow(rows[r][j], -1, p)
        rows[r] = [(x * inv) if p == 0 else (x * inv) % p for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][j] != 0:
                f = rows[i][j]
                rows[i] = [(x - f * y) if p == 0 else (x - f * y) % p
                           for x, y in zip(rows[i], rows[r])]
        r += 1
    return r

def in_span(vectors, b, mod, length):
    """mod = 0 means Q; prime p means F_p; composite n means Z/n."""
    if mod == 0:
        return rank_field(vectors, 0) == rank_field(list(vectors) + [b], 0)
    if all(mod % q for q in range(2, int(mod ** 0.5) + 1)):
        return rank_field(vectors, mod) == rank_field(list(vectors) + [b], mod)
    return in_span_mod(vectors, b, mod, length)

# --------------------------------------------------------------------------
# monomials of S[Y] by formal degree (positive N^k-gradings)
# --------------------------------------------------------------------------

def y_monomials_up_to(D, bound, strict=True):
    """All alpha with formal degree < bound (or <= if strict=False).
    Requires every generator degree to be lexicographically positive and,
    for termination, to have a positive FIRST coordinate when k>1 is used with
    a bound in the first coordinate (natural / weighted N-gradings)."""
    m = len(D)
    out = []
    def rec(i, alpha):
        if i == m:
            d = formal_deg(alpha, D)
            if (d < bound) if strict else (d <= bound):
                out.append(tuple(alpha))
            return
        k = 0
        while True:
            alpha.append(k)
            d = formal_deg(alpha + [0] * (m - i - 1), D)
            ok = (d < bound) if strict else (d <= bound)
            if not ok:
                alpha.pop()
                break
            rec(i + 1, alpha)
            alpha.pop()
            k += 1
            if k > 200:
                raise RuntimeError('unbounded fibre; grading not suitable')
    rec(0, [])
    return out

def y_monomials_of_degree(D, gamma):
    """All alpha with deg_F(alpha) == gamma exactly.  Uses componentwise bounds,
    valid because all generator degrees have non-negative coordinates
    (N^k-gradings given by non-negative weight matrices).  Generators of
    degree 0 would make the fibre infinite; they are rejected."""
    m = len(D)
    for d in D:
        if not any(d):
            raise ValueError('generator of degree 0: fibres are infinite')
    bounds = []
    for d in D:
        b = min(g // x for g, x in zip(gamma, d) if x > 0)
        bounds.append(b)
    out = []
    def rec(i, alpha, partial):
        if any(p > g for p, g in zip(partial, gamma)):
            return
        if i == m:
            if tuple(partial) == tuple(gamma):
                out.append(tuple(alpha))
            return
        for k in range(bounds[i] + 1):
            rec(i + 1, alpha + [k], [p + k * x for p, x in zip(partial, D[i])])
    rec(0, [], [0] * len(gamma))
    return out

def x_monomials_of_degree(W, nx, gamma, maxexp=60):
    out = []
    def rec(i, e):
        if i == nx:
            if mdeg(e, W) == gamma:
                out.append(tuple(e))
            return
        for k in range(maxexp):
            e.append(k)
            d = mdeg(e + [0] * (nx - i - 1), W)
            e.pop()
            # prune: every coordinate of a partial degree is a lower bound
            if any(dd > gg for dd, gg in zip(d, gamma)):
                break
            e.append(k)
            rec(i + 1, e)
            e.pop()
    rec(0, [])
    return out

# --------------------------------------------------------------------------
# liftability (independent of Groebner bases) for gradings with finite
# lower sets {alpha : deg_F(alpha) < gamma}
# --------------------------------------------------------------------------

def liftable(u, F, D, mod, nx, kill=()):
    """Decide whether the homogeneous u in ker(pi) admits a lifting, by linear
    algebra: u lifts  <=>  psi(u) is an S-combination of psi(Y^alpha) with
    deg_F(alpha) < Omega(u).  Returns (bool, combination-or-None)."""
    g = Omega(u, D)
    target = subst(u, F, mod, nx, kill)
    if not target:
        return True, {}
    alphas = y_monomials_up_to(D, g, strict=True)
    imgs = [subst({a: 1}, F, mod, nx, kill) for a in alphas]
    mons = sorted({e for p in imgs + [target] for e in p})
    vecs = [[p.get(e, 0) for e in mons] for p in imgs]
    b = [target.get(e, 0) for e in mons]
    return in_span(vecs, b, mod, len(mons)), None

# --------------------------------------------------------------------------
# generation of ker(pi) degree by degree
# --------------------------------------------------------------------------

def kernel_generated_in_degree(U, LF, D, mod, nx, gamma, kill=()):
    """Check that the degree-gamma component of ker(pi) equals the degree-gamma
    component of the ideal generated by U (U homogeneous).  Works over Z/n
    (any n), F_p and Q.  Returns (ok, |ker_gamma| or dim, |span| or dim)."""
    basis = y_monomials_of_degree(D, gamma)
    if not basis:
        return True, 0, 0
    idx = {a: i for i, a in enumerate(basis)}
    N = len(basis)
    # image of each basis monomial
    imgs = [subst({a: 1}, LF, mod, nx, kill) for a in basis]
    xmons = sorted({e for p in imgs for e in p})
    M = len(xmons)
    cols = [[p.get(e, 0) for e in xmons] for p in imgs]   # one vector per Y-monomial
    # multiples m*u of degree gamma
    gens = []
    for u in U:
        du = Omega(u, D)
        if not all(x >= y for x, y in zip(gamma, du)):
            continue
        rest_deg = tuple(x - y for x, y in zip(gamma, du))
        betas = [tuple([0] * len(D))] if not any(rest_deg) else y_monomials_of_degree(D, rest_deg)
        for beta in betas:
            prod_ = {}
            for e, c in u.items():
                ee = tuple(p + q for p, q in zip(e, beta))
                prod_[ee] = prod_.get(ee, 0) + c
            v = [0] * N
            for e, c in prod_.items():
                v[idx[e]] = c
            gens.append(v)
    if mod == 0 or all(mod % q for q in range(2, int(mod ** 0.5) + 1)):
        p = mod
        # dim ker = N - rank(image map); dim span = rank(gens)
        rk_img = rank_field(cols, p) if cols and M else 0
        dk = N - rk_img
        ds = rank_field(gens, p) if gens else 0
        return dk == ds, dk, ds
    n = mod
    img_order = subgroup_order(cols, n, M) if M else 1
    ker_order = n ** N // img_order
    span_order = subgroup_order(gens, n, N) if gens else 1
    return ker_order == span_order, ker_order, span_order
