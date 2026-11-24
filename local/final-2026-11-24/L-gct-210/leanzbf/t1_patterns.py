import itertools, numpy as np
exec(open('/home/kevxhk/work/L-gct-210/leanzbf/t1_enum.py').read().split("random.seed(1)")[0])
triples = list(itertools.permutations(cols, 3))
pats = set()
for s12 in STR:
    if s12[0] != 'II': continue
    for s13 in STR:
        if s13[0] != 'II': continue
        for s23 in STR:
            if s23[0] != 'I' or not ratio_ok(s12[2], s13[2], s23[2]): continue
            C23 = s23[1]
            for (p, q, s) in triples:
                if (s12[1][p], s12[1][q], s12[1][s]) != (1, 2, 3): continue
                if not (0 < len(C23 & {p, q, s}) < 3): continue
                pats.add((s12[2][p], tuple(s13[1][m] for m in (p, q, s)), tuple(s13[2][m] for m in (p, q, s)),
                          tuple((m in C23) for m in (p, q, s))))
print('local patterns (p in Q1, q in Q2, s in Q3 of pair 12; C23 splits S):', len(pats))
# up to complementing C23 and conjugation
red = set()
for (e12, l13, w13, c23) in pats:
    c = c23 if c23[0] else tuple(not x for x in c23)
    red.add((e12.imag > 0, l13, tuple((complex(w).imag > 0, complex(w).real) for w in w13), c))
print('up to C23 complement:', len(red))
