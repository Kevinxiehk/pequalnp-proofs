# (II,II,II): test column-triple rules for the simple S-test
import itertools, numpy as np
exec(open('/home/kevxhk/work/L-gct-210/leanzbf/t1_enum.py').read().split("random.seed(1)")[0])
np.random.seed(5)
from collections import Counter
triples = list(itertools.combinations(cols, 3))
stats = Counter(); cnt = 0
II = [s for s in STR if s[0] == 'II']
for s12 in II:
    for s13 in II:
        for s23 in II:
            if not ratio_ok(s12[2], s13[2], s23[2]): continue
            cnt += 1
            good = {S: stest(s12, s13, s23, S) for S in triples}
            anyg = any(good.values())
            def trans(st, S): return sorted(st[1][m] for m in S) == [1, 2, 3]
            for name, st in (('12', s12), ('13', s13), ('23', s23)):
                R = [S for S in triples if trans(st, S)]
                stats[(name, 'exists', bool(R))] += 1
                stats[(name, 'some good', any(good[S] for S in R), anyg)] += 1
            R3 = [S for S in triples if trans(s12, S) or trans(s13, S) or trans(s23, S)]
            stats[('any transversal good', any(good[S] for S in R3), anyg)] += 1
print('configs', cnt)
for k, v in sorted(stats.items(), key=str): print(k, v)
