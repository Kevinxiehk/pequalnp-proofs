import itertools, numpy as np
exec(open('/home/kevxhk/work/L-gct-210/leanzbf/t1_enum.py').read().split("random.seed(1)")[0])
np.random.seed(9)
from collections import Counter
triples = list(itertools.permutations(cols, 3))
II = [s for s in STR if s[0] == 'II']
fail = Counter(); okc = Counter()
def lab(st, m): return st[1][m]
for s12 in II:
    for s13 in II:
        for s23 in II:
            if not ratio_ok(s12[2], s13[2], s23[2]): continue
            for (p, q, s) in triples:
                if (lab(s12, p), lab(s12, q), lab(s12, s)) != (1, 2, 3): continue
                l13 = tuple(lab(s13, m) for m in (p, q, s)); l23 = tuple(lab(s23, m) for m in (p, q, s))
                if len(set(l13)) == 1 or len(set(l23)) == 1: continue
                g = stest(s12, s13, s23, (p, q, s))
                key = (l13, l23)
                (okc if g else fail)[key] += 1
both = set(fail) & set(okc)
print('patterns failing:', len(fail), 'passing:', len(okc), 'ambiguous:', len(both))
for k, v in sorted(fail.items()): print('FAIL', k, v, 'pass-count', okc.get(k, 0))
