# Lemma B analysis: per Hall-case of (p,q,s) (26), allowed statuses of one extra column z; prune reasons; then pairs (x,y).
import itertools, ast
from collections import Counter
GEN = set()
for line in open('/home/kevxhk/work/L-gct-210/leanzbf/gen_t3p.log'):
    if line.startswith('(('):
        lab, x, sg, name = ast.literal_eval(line.strip()); GEN.add((lab, x))
LAB = {'Q': 2, 'B': 3, 'C': 1}
SW = {'Q': 'B', 'B': 'Q', 'C': 'C'}
def zval(st, sg): return {'Q': 0, 'B': 2, 'C': (1 if sg == 1 else 3)}[st]
def kval(c, sg): return (zval(c[1], sg[1]) - zval(c[2], sg[2]) - zval(c[0], sg[0])) % 4
def consistent(cols):
    for sg in itertools.product((1, -1), repeat=3):
        if len({kval(c, sg) for c in cols}) == 1: return True
    return False
def np_ok(cols, order):
    # all transversals of the distinguished pair among cols have a NON-passing CONSISTENT pattern (i.e. Hall holds)
    P = cols if order == '123' else [(c[1], c[0], SW[c[2]]) for c in cols]
    for i, j, k in itertools.permutations(range(len(P)), 3):
        if (P[i][0], P[j][0], P[k][0]) == ('C', 'Q', 'B'):
            T = [P[i], P[j], P[k]]
            pat = (tuple(LAB[t[1]] for t in T), tuple(LAB[t[2]] for t in T))
            if pat in GEN or not consistent(T): return False, (order, (i, j, k))
    return True, None
NP = []
S = list(itertools.product('CQB', repeat=3))
for sp in S:
    if sp[0] != 'C': continue
    for sq in S:
        if sq[0] != 'Q': continue
        for ss in S:
            if ss[0] != 'B': continue
            cols = [sp, sq, ss]
            if np_ok(cols, '123')[0]: NP.append(cols)
print('Hall cases for (p,q,s):', len(NP))
reasons = Counter(); allowed = {}
for ci, cols in enumerate(NP):
    al = []
    for z in S:
        c4 = cols + [z]
        ok1, w1 = np_ok(c4, '123'); ok2, w2 = np_ok(c4, '132')
        if not ok1: reasons['hall123'] += 1; continue
        if not ok2: reasons['hall132'] += 1; continue
        if not consistent(c4): reasons['ratio'] += 1; continue
        al.append(z)
    allowed[ci] = al
print('single extra column prune reasons:', dict(reasons), ' allowed total:', sum(len(v) for v in allowed.values()))
print('allowed per case:', [len(allowed[i]) for i in range(len(NP))])
r2 = Counter(); leaves = 0; leafinfo = []
for ci, cols in enumerate(NP):
    al = allowed[ci]
    for zx, zy in itertools.combinations_with_replacement(al, 2):
        c5 = cols + [zx, zy]
        ok1, _ = np_ok(c5, '123'); ok2, _ = np_ok(c5, '132')
        if not ok1: r2['hall123'] += 1; continue
        if not ok2: r2['hall132'] += 1; continue
        if not consistent(c5): r2['ratio'] += 1; continue
        if not all({c[t] for c in c5} == {'C', 'Q', 'B'} for t in range(3)): r2['incomplete'] += 1; continue
        leaves += 1; leafinfo.append((ci, zx, zy))
print('pair prune reasons (unordered pairs):', dict(r2), ' leaves:', leaves)
open('/home/kevxhk/work/L-gct-210/leanzbf/lemB_leaves.txt', 'w').write('\n'.join(repr((NP[ci], zx, zy)) for ci, zx, zy in leafinfo) + '\n')
# witness argument: each class Q13,B13,C13,Q23,B23,C23 must be realized by p,q,s or by an allowed extra status
print('--- witness check per case ---')
leafcases = {ci for ci, zx, zy in leafinfo}
idx13 = {'Q': 'Q13', 'B': 'B13', 'C': 'C13'}; idx23 = {'Q': 'Q23', 'B': 'B23', 'C': 'C23'}
for ci, cols in enumerate(NP):
    real = set()
    for c in cols + allowed[ci]:
        real.add(idx13[c[1]]); real.add(idx23[c[2]])
    missing = {'Q13', 'B13', 'C13', 'Q23', 'B23', 'C23'} - real
    print(ci, 'leafcase' if ci in leafcases else '        ', 'p,q,s =', cols, 'allowed =', allowed[ci], 'missing:', sorted(missing))
