import itertools, numpy as np
exec(open('/home/kevxhk/work/L-gct-210/leanzbf/t1_enum.py').read().split("random.seed(1)")[0])
np.random.seed(3)
triples = list(itertools.combinations(cols, 3))
from collections import Counter
stats = Counter()
for s12 in STR:
    if s12[0] != 'II': continue
    for s13 in STR:
        if s13[0] != 'II': continue
        for s23 in STR:
            if s23[0] != 'I' or not ratio_ok(s12[2], s13[2], s23[2]): continue
            optA = all((s12[1][m] == 1) == (s13[1][m] == 1) for m in cols)
            rule = [S for S in triples if sorted(s12[1][m] for m in S) == [1, 2, 3]]
            rule13 = [S for S in triples if sorted(s13[1][m] for m in S) == [1, 2, 3]]
            g = [stest(s12, s13, s23, S) for S in rule]
            g13 = [stest(s12, s13, s23, S) for S in rule13]
            stats[('A' if optA else 'B', 'R12 some', any(g))] += 1
            stats[('A' if optA else 'B', 'R12 all', all(g) if g else None)] += 1
            stats[('A' if optA else 'B', 'R12orR13 some', any(g) or any(g13))] += 1
for k, v in sorted(stats.items(), key=str): print(k, v)
