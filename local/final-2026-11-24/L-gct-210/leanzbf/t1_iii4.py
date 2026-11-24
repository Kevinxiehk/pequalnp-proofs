import itertools, numpy as np
exec(open('/home/kevxhk/work/L-gct-210/leanzbf/t1_enum.py').read().split("random.seed(1)")[0])
np.random.seed(6)
from collections import Counter
triples = list(itertools.combinations(cols, 3))
stats = Counter(); fails = Counter()
II = [s for s in STR if s[0] == 'II']
def trans(st, S): return sorted(st[1][m] for m in S) == [1, 2, 3]
def nonconst(st, S): return len(set(st[1][m] for m in S)) > 1
def has_rel(st, S):   # pair relation restricted to S nontrivial: some column in Q2 or Q3
    return any(st[1][m] in (2, 3) for m in S)
for s12 in II:
    for s13 in II:
        for s23 in II:
            if not ratio_ok(s12[2], s13[2], s23[2]): continue
            good = {S: stest(s12, s13, s23, S) for S in triples}
            if not any(good.values()): continue
            rules = {
              'T12': [S for S in triples if trans(s12, S)],
              'T12+nc13+nc23': [S for S in triples if trans(s12, S) and nonconst(s13, S) and nonconst(s23, S)],
              'T12+T13': [S for S in triples if trans(s12, S) and trans(s13, S)],
              'Tany+nc': [S for S in triples if (trans(s12, S) or trans(s13, S) or trans(s23, S)) and nonconst(s12, S) and nonconst(s13, S) and nonconst(s23, S)],
            }
            for name, R in rules.items():
                stats[(name, 'exists', bool(R))] += 1
                if R:
                    stats[(name, 'all good', all(good[S] for S in R))] += 1
                    stats[(name, 'some good', any(good[S] for S in R))] += 1
for k, v in sorted(stats.items(), key=str): print(k, v)
