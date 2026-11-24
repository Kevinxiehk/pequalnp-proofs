import itertools, numpy as np
exec(open('/home/kevxhk/work/L-gct-210/leanzbf/t1_enum.py').read().split("random.seed(1)")[0])
np.random.seed(4)
triples = list(itertools.combinations(cols, 3))
from collections import Counter
stats = Counter(); fails = Counter()
for s12 in STR:
    if s12[0] != 'II': continue
    for s13 in STR:
        if s13[0] != 'II': continue
        for s23 in STR:
            if s23[0] != 'I' or not ratio_ok(s12[2], s13[2], s23[2]): continue
            optA = all((s12[1][m] == 1) == (s13[1][m] == 1) for m in cols)
            C23 = s23[1]
            def ok(S):
                return sorted(s12[1][m] for m in S) == [1, 2, 3] and 0 < len(C23 & set(S)) < 3
            rule = [S for S in triples if ok(S)]
            g = [stest(s12, s13, s23, S) for S in rule]
            stats[('A' if optA else 'B', 'some', any(g), 'all', all(g))] += 1
            for S, gg in zip(rule, g):
                if not gg:
                    fails[tuple((s12[1][m], s13[1][m], m in C23) for m in sorted(S, key=lambda m: s12[1][m]))] += 1
for k, v in sorted(stats.items(), key=str): print(k, v)
for k, v in fails.most_common(10): print('fail', k, v)
