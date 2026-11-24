import itertools, numpy as np
exec(open('/home/kevxhk/work/L-gct-210/leanzbf/t1_enum.py').read().split("random.seed(1)")[0])
np.random.seed(7)
from collections import Counter
triples = list(itertools.combinations(cols, 3))
II = [s for s in STR if s[0] == 'II']
st = Counter()
for s12 in II:
    for s13 in II:
        for s23 in II:
            if not ratio_ok(s12[2], s13[2], s23[2]): continue
            if any(stest(s12, s13, s23, S) for S in triples): continue
            c12 = frozenset(m for m in cols if s12[1][m] == 1)
            c13 = frozenset(m for m in cols if s13[1][m] == 1)
            c23 = frozenset(m for m in cols if s23[1][m] == 1)
            th = s13[2][0] / (s12[2][0] * s23[2][0])
            key = (len(c12), len(c13), len(c23), len(c12 & c13), len(c12 & c23), len(c13 & c23), len(c12 | c13 | c23),
                   'theta real' if abs(th.imag) < 1e-9 else 'theta imag')
            st[key] += 1
for k, v in sorted(st.items()): print(k, v)
