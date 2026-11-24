import itertools, numpy as np
exec(open('/home/kevxhk/work/L-gct-210/leanzbf/t1_enum.py').read().split("random.seed(1)")[0])
np.random.seed(8)
from collections import Counter
triples = list(itertools.combinations(cols, 3))
II = [s for s in STR if s[0] == 'II']
stats = Counter()
def trans(st, S): return sorted(st[1][m] for m in S) == [1, 2, 3]
def nonconst(st, S): return len(set(st[1][m] for m in S)) > 1
for s12 in II:
    for s13 in II:
        for s23 in II:
            if not ratio_ok(s12[2], s13[2], s23[2]): continue
            good = {S: stest(s12, s13, s23, S) for S in triples}
            if not any(good.values()): continue
            th = s13[2][0] / (s12[2][0] * s23[2][0])
            treal = abs(th.imag) < 1e-9
            c12 = {m for m in cols if s12[1][m] == 1}; c13 = {m for m in cols if s13[1][m] == 1}; c23 = {m for m in cols if s23[1][m] == 1}
            cover = len(c12 | c13 | c23) == 5
            key = ('real' if treal else 'imag', 'cover' if cover else 'nocover')
            rules = {
              'T12nc': [S for S in triples if trans(s12, S) and nonconst(s13, S) and nonconst(s23, S)],
              'T13nc': [S for S in triples if trans(s13, S) and nonconst(s12, S) and nonconst(s23, S)],
              'T23nc': [S for S in triples if trans(s23, S) and nonconst(s12, S) and nonconst(s13, S)],
              'corner3': [S for S in triples if any(m in c12 for m in S) and any(m in c13 for m in S) and any(m in c23 for m in S)],
            }
            for name, R in rules.items():
                if R:
                    stats[key + (name, 'all good', all(good[S] for S in R))] += 1
                else:
                    stats[key + (name, 'empty')] += 1
for k, v in sorted(stats.items(), key=str): print(k, v)
