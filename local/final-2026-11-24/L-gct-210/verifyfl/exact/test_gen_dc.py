import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
"""gen_dc.py must reproduce gen_n1s.py exactly when Nt = {3,4} (same case list, same variable names, same equation sets)."""
import exactlib as X, gen_n1s, gen_dc
p = 2147483629; ok = True
for mspec in ('m12m3', 'iso'):
    cs, m, W, P, Nt = gen_dc.setup(p, mspec)
    for k in (2, 3):
        A = gen_n1s.cases(k); Bc = gen_dc.cases(k, P, Nt); assert len(A) == len(Bc), (len(A), len(Bc))
        bad = 0
        for ca, cb in zip(A, Bc):
            n1, p1 = gen_n1s.build(p, mspec, ca); n2, p2 = gen_dc.build(p, mspec, cb)
            same = n1 == n2 and sorted(sorted(q.items()) for q in p1) == sorted(sorted(q.items()) for q in p2)
            if not same: bad += 1
        print(mspec, 'k =', k, ':', len(A), 'cases, mismatches:', bad); ok &= bad == 0
for mspec in ('p4a', 'p5a'):
    cs, m, W, P, Nt = gen_dc.setup(p, mspec)
    for k in (2, 3): print(mspec, 'P =', P, 'Nt =', Nt, 'k =', k, ':', len(gen_dc.cases(k, P, Nt)), 'cases')
print('ALL TESTS PASSED' if ok else 'SOME TEST FAILED')
