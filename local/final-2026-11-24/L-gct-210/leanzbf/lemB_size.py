# size estimate for a generated Lemma B: statuses of p,q,s (canonical transversal), then x, y; prune by ratio consistency
# (one global sign choice) and by "some transversal passes" in row orders 123 / 132.
import itertools, ast
GEN = set()
for line in open('/home/kevxhk/work/L-gct-210/leanzbf/gen_t3p.log'):
    if line.startswith('(('):
        lab, x, sg, name = ast.literal_eval(line.strip()); GEN.add((lab, x))
LAB = {'Q': 2, 'B': 3, 'C': 1}
SW = {'Q': 'B', 'B': 'Q', 'C': 'C'}
def zval(st, sg): return {'Q': 0, 'B': 2, 'C': (1 if sg == 1 else 3)}[st]
def kval(s12, s13, s23, sg12, sg13, sg23):   # ratio exponent for one column: x13 = theta x23 x12
    return (zval(s13, sg13) - zval(s23, sg23) - zval(s12, sg12)) % 4
def consistent(cols, sg12, sg13, sg23):
    return len({kval(a, b, c, sg12, sg13, sg23) for (a, b, c) in cols}) == 1
def passes_any(cols):
    # order 123: transversal of pair 12 (C, Q, B in 12), pattern (13, 23)
    for order in ('123', '132'):
        if order == '123': P = [(c[0], c[1], c[2]) for c in cols]
        else: P = [(c[1], c[0], SW[c[2]]) for c in cols]
        for i, j, k in itertools.permutations(range(len(P)), 3):
            if (P[i][0], P[j][0], P[k][0]) == ('C', 'Q', 'B'):
                pat = (tuple(LAB[P[t][1]] for t in (i, j, k)), tuple(LAB[P[t][2]] for t in (i, j, k)))
                if pat in GEN: return True
    return False
def alive(cols):
    ok = any(consistent(cols, a, b, c) for a in (1, -1) for b in (1, -1) for c in (1, -1))
    return ok and not passes_any(cols)
S = list(itertools.product('CQB', repeat=3))
lvl = [0, 0, 0]
leaves = 0
base = []
for sp in S:
    if sp[0] != 'C': continue
    for sq in S:
        if sq[0] != 'Q': continue
        for ss in S:
            if ss[0] != 'B': continue
            cols = [sp, sq, ss]
            if alive(cols): base.append(cols)
lvl[0] = len(base)
for cols in base:
    for sx in S:
        c2 = cols + [sx]
        if not alive(c2): continue
        lvl[1] += 1
        for sy in S:
            c3 = c2 + [sy]
            if not alive(c3): continue
            # every label of each pair must occur (all three classes non-empty) at the end
            ok = all({c[t] for c in c3} == {'C', 'Q', 'B'} for t in range(3))
            if ok: lvl[2] += 1
print('alive after p,q,s:', lvl[0], ' after x:', lvl[1], ' leaves after y (classes complete):', lvl[2])
