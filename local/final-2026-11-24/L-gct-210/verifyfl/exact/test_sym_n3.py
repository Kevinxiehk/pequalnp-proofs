import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
"""substitution test for gen_sym_n3: the exact two-column control K_2 (defect line (1,-1,0,0,0) = chart A at t = -1) satisfies every
equation of its case at mt = -1 and violates them at mt = 3; and the N-variables agree with gen_sym.build (k = 2)."""
import exactlib as X, random, gen_sym_n3, gen_sym, test_n3 as T
p = T.p; case = (2, 1, (0,), 0, 'ab', 'ab')
names, polys = gen_sym_n3.build(p, 'A', case, 0)
nN, pN = gen_sym.build(p, 'A', case)
assert names[:len(nN)] == nN, 'N-variable names differ from gen_sym.build'
ok = True
for tv, expect in ((p - 1, True), (3, False)):
    val = dict(T.val); val['mt'] = tv
    vv = {i: val[n] for i, n in enumerate(names)}
    sat = all(X.peval(q, vv, p) == 0 for q in polys); print('K_2 at mt = %d: satisfies all %d equations: %s (expected %s)' % (tv if tv < p // 2 else tv - p, len(polys), sat, expect)); ok &= sat == expect
print('ALL TESTS PASSED' if ok else 'SOME TEST FAILED')
