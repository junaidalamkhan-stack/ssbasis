"""
controls.py -- negative and positive controls for the checks in sslib.py,
to make sure that a "pass" in verify_examples.py is meaningful.
Each control is EXPECTED to report the opposite of a pass.
Run: python3 controls.py
"""
from sslib import *

def gen_check(name, xn, mod, W, Fs, Us, box):
    F = [clean(parse(s, xn), mod) for s in Fs]
    LF = [lead_form(f, W) for f in F]
    D = [deg(f, W) for f in F]
    yn = ['Y%d' % (i + 1) for i in range(len(F))]
    U = [clean(parse(s, yn), mod) for s in Us]
    import itertools
    fails = []
    for g in itertools.product(*[range(b + 1) for b in box]):
        if not any(g):
            continue
        ok, a, b = kernel_generated_in_degree(U, LF, D, mod, len(xn), tuple(g))
        if not ok:
            fails.append((g, a, b))
    return fails

allgood = True
def expect(label, cond):
    global allgood
    allgood &= cond
    print(('  [control behaves as expected] ' if cond else '  [CONTROL FAILED] ') + label)

# 1. Ex 4.6 without the zero-divisor relation 2*Y3 must FAIL generation
f = gen_check('4.6 minus 2Y3', ['x', 'y'], 4, [[1, 0], [0, 1]],
              ['x*y^3+y^4', 'y^3+2*y', '2*x+y^3'], ['Y3^2', 'Y2*Y3+2*Y1'], (3, 9))
expect('Ex 4.6 without 2*Y3 is detected as NOT generating ker(pi) (first gap at %s)' % (f[0][0],), bool(f))

# 2. Ex 4.6 without Y3^2 must FAIL
f = gen_check('4.6 minus Y3^2', ['x', 'y'], 4, [[1, 0], [0, 1]],
              ['x*y^3+y^4', 'y^3+2*y', '2*x+y^3'], ['2*Y3', 'Y2*Y3+2*Y1'], (3, 9))
expect('Ex 4.6 without Y3^2 is detected (first gap at %s)' % (f[0][0],), bool(f))

# 3. Ex 4.3 with c4 = Y3^3 - Y4^2 removed must FAIL in degree 6
f = gen_check('4.3 minus c4', ['x', 'y'], 0, [[1, 1]],
              ['x+y', 'x*y', 'x^2-x', 'x^3-x'],
              ['Y2*Y3+Y3^2-Y1*Y4', 'Y1^2*Y3-Y2^2+Y3^2-2*Y1*Y4', 'Y1*Y3^2-Y2*Y4-Y3*Y4'], (8,))
expect('Ex 4.3 without Y3^3-Y4^2 is detected (first gap at %s)' % (f[0][0],), bool(f))

# 4. Ex 4.9 without 2*Y4 must FAIL in degree 1
f = gen_check('4.9 minus 2Y4', ['x', 'y'], 6, [[1, 1]],
              ['x^2+3*y', 'x*y+1', 'y^2+3*x', '3*x+3*y+1'],
              ['Y4^2+3*Y1+3*Y3', '5*Y1*Y3+Y2^2'], (6,))
expect('Ex 4.9 without 2*Y4 is detected (first gap at %s)' % (f[0][0],), bool(f))

# 5. Ex 4.9 with 2*Y4 replaced by 4*Y4 (= -2*Y4, same ideal) must PASS
f = gen_check('4.9 with 4Y4', ['x', 'y'], 6, [[1, 1]],
              ['x^2+3*y', 'x*y+1', 'y^2+3*x', '3*x+3*y+1'],
              ['4*Y4', 'Y4^2+3*Y1+3*Y3', '5*Y1*Y3+Y2^2'], (8,))
expect('Ex 4.9 with 4*Y4 in place of 2*Y4 still passes (same ideal)', not f)

# 6. liftable(): positive control (c2 of Ex 4.4 lifts) and negative (c1 does not)
F = [parse(s, ['x', 'y']) for s in ['x^2+y', 'x*y', 'y^2', 'y^3+y']]
D = [deg(g, [[1, 1]]) for g in F]
ok2, _ = liftable(parse('Y3^3-Y4^2', ['Y1', 'Y2', 'Y3', 'Y4']), F, D, 0, 2)
ok1, _ = liftable(parse('Y2^2-Y1*Y3', ['Y1', 'Y2', 'Y3', 'Y4']), F, D, 0, 2)
expect('liftable() says Y3^3-Y4^2 lifts in Ex 4.4', ok2)
expect('liftable() says Y2^2-Y1*Y3 does not lift in Ex 4.4', not ok1)

# 7. liftable() over Z/4: Ex 4.7 completed, Y2+3*Y3 lifts once 2x+2y is adjoined
F = [parse(s, ['x', 'y']) for s in ['x*y^3+y^4', 'y^3+2*y', '2*x+y^3', '2*x+2*y']]
D = [deg(g, [[1, 1]]) for g in F]
ok, _ = liftable(parse('Y2+3*Y3', ['Y1', 'Y2', 'Y3', 'Y4']), F, D, 4, 2)
expect('liftable() over Z/4 says Y2+3*Y3 lifts after completion of Ex 4.7', ok)

# 8. a deliberately wrong lifting must fail psi(l)=0
F = [parse(s, ['x', 'y', 'z']) for s in ['x*z^2+y+1', 'y*z+z', 'x*y*z^3+y^2*z', 'x*z^3+2*y*z+z', 'z+3']]
l = parse('Y1*Y5+Y2-Y4-3*Y1-Y5+2', ['Y1', 'Y2', 'Y3', 'Y4', 'Y5'])
expect('a perturbed lifting (constant 2 instead of 3) is rejected in Ex 4.1',
       subst(l, F, 0, 3) != {})

print('\nALL CONTROLS BEHAVE AS EXPECTED' if allgood else '\nSOME CONTROL FAILED')
