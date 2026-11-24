# For (II,II,I) configurations: column type = (lab12, lab13, side23). Which type-triples pass the simple S-test?
import itertools, numpy as np
exec(open('/home/kevxhk/work/L-gct-210/leanzbf/t1_enum.py').read().split("random.seed(1)")[0])
np.random.seed(2)
triples = list(itertools.combinations(cols, 3))
good_types = {}
def ctype(s12, s13, s23, m):
    t23 = (m in s23[1]) if s23[0] == 'I' else s23[1][m]
    return (s12[1][m], s13[1][m], t23, s12[2][m], s13[2][m])
nconf = 0; covered_by = {}
for s12 in STR:
    if s12[0] != 'II': continue
    for s13 in STR:
        if s13[0] != 'II': continue
        for s23 in STR:
            if s23[0] != 'I' or not ratio_ok(s12[2], s13[2], s23[2]): continue
            nconf += 1
            for S in triples:
                key = tuple(sorted(ctype(s12, s13, s23, m) for m in S))
                if key not in good_types:
                    good_types[key] = stest(s12, s13, s23, S)
print('configs', nconf, 'distinct type-triples', len(good_types), 'good', sum(good_types.values()))
# option split: corner sets equal (A) or complementary (B)
