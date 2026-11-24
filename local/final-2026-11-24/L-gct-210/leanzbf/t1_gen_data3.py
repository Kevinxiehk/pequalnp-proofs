# like t1_gen_data.py, but look for x0 whose tau-values vanish at all corner positions (j-free certificate)
exec(open('/home/kevxhk/work/L-gct-210/leanzbf/t1_gen_data.py').read().split("out = []")[0])
out = []
for lab13 in itertools.product((1, 2, 3), repeat=3):
    for c23 in itertools.product((0, 1), repeat=3):
        if len(set(c23)) == 1 or c23[0] == 0: continue
        for e12 in (1, -1):
            for e13 in (1, -1):
                w2 = [G(0, e12), G(1), G(-1)]
                w3 = [G(0, e13) if l == 1 else G(1 if l == 2 else -1) for l in lab13]
                rat = [w3[k] / w2[k] for k in range(3)]
                sgn = [(-1 if c23[k] else 1) for k in range(3)]
                th = rat[0] / G(sgn[0])
                if not all((rat[k] - th * G(sgn[k])).iszero() for k in range(3)): continue
                rel = []
                for i in range(3):
                    rel.append([Fr(1) if v // 3 == i else Fr(0) for v in range(9)])
                v = [Fr(0)] * 9; v[2] += 1; v[4] += 1; rel.append(v)
                v = [Fr(0)] * 9
                for k in range(3):
                    if lab13[k] == 3: v[k] += 1
                    if lab13[k] == 2: v[6+k] += 1
                rel.append(v)
                v = [Fr(0)] * 9
                for k in range(3):
                    if c23[k]: v[3+k] += 1; v[6+k] -= 1
                rel.append(v)
                piv, free, M = solve(rel)
                corners = [3]
                found = None
                for x0 in itertools.product(range(-3, 4), repeat=3):
                    tau = [sum((M[r][l] * x0[l] for l in range(3)), Fr(0)) for r in range(9)]
                    if any(tau[c] != 0 for c in corners): continue
                    X = [[G(tau[3*i+k]) / ([G(1)]*3, w2, w3)[i][k] for k in range(3)] for i in range(3)]
                    p = perm3(X)
                    if not p.iszero(): found = (x0, p); break
                out.append((lab13, c23, e12, e13, 'optA' if lab13[0] == 1 else 'optB', found))
for o in out: print(o)
