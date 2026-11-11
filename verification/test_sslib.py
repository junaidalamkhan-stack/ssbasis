# Brute-force self-test of subgroup_order (Howell elimination) against enumeration.
import random, itertools
from sslib import subgroup_order
random.seed(1)
def brute(vecs, n, L):
    S = {tuple([0]*L)}
    frontier = list(S)
    while frontier:
        new = []
        for s in frontier:
            for v in vecs:
                t = tuple((a+b) % n for a, b in zip(s, v))
                if t not in S:
                    S.add(t); new.append(t)
        frontier = new
    return len(S)
bad = 0
for trial in range(3000):
    n = random.choice([4, 6, 8, 9, 12, 2, 3])
    L = random.randint(1, 4)
    k = random.randint(0, 4)
    vecs = [[random.randrange(n) for _ in range(L)] for _ in range(k)]
    a, b = subgroup_order(vecs, n, L), brute(vecs, n, L)
    if a != b:
        bad += 1
        if bad < 5: print('MISMATCH', n, vecs, a, b)
print('trials 3000, mismatches', bad)
