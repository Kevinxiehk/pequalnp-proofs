# Generator (II,II,II): one Lean core lemma per S-test-passing local pattern (lab13, sg13, lab23) on a pair-12 transversal (p corner, q in Q2^12, s in Q3^12).
import itertools, sys
from fractions import Fraction as Fr
def solve_rows(rows, rhs):   # find lambda with sum lambda_r rows[r] = rhs (exact; rows independent)
    n = len(rows); m = len(rhs)
    # build augmented system A^T lambda = rhs: m equations, n unknowns
    A = [[rows[r][e] for r in range(n)] + [rhs[e]] for e in range(m)]
    piv = []; rr = 0
    for c in range(n):
        k = next((i for i in range(rr, m) if A[i][c] != 0), None)
        if k is None: continue
        A[rr], A[k] = A[k], A[rr]; pv = A[rr][c]; A[rr] = [x / pv for x in A[rr]]
        for i in range(m):
            if i != rr and A[i][c] != 0:
                f = A[i][c]; A[i] = [x - f * y for x, y in zip(A[i], A[rr])]
        piv.append(c); rr += 1
    for i in range(rr, m): assert A[i][n] == 0, 'inconsistent'
    lam = [Fr(0)] * n
    for i, c in enumerate(piv): lam[c] = A[i][n]
    return lam
def nullsolve(rel):
    A = [r[:] for r in rel]; piv = []; r = 0
    for c in range(9):
        k = next((i for i in range(r, len(A)) if A[i][c] != 0), None)
        if k is None: continue
        A[r], A[k] = A[k], A[r]; pv = A[r][c]; A[r] = [x / pv for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c] != 0:
                f = A[i][c]; A[i] = [x - f * y for x, y in zip(A[i], A[r])]
        piv.append(c); r += 1
    free = [c for c in range(9) if c not in piv]
    M = [[Fr(0)] * len(free) for _ in range(9)]
    for l, f in enumerate(free): M[f][l] = Fr(1)
    for i, c in enumerate(piv):
        for l, f in enumerate(free): M[c][l] = -A[i][f]
    return free, M
def fmt(q):
    q = Fr(q)
    if q.denominator == 1: return str(q.numerator) if q >= 0 else f'({q.numerator})'
    return f'({q.numerator} / {q.denominator})'
def polymul(a, b):
    out = {}
    for i, x in a.items():
        for j, y in b.items(): out[i + j] = out.get(i + j, Fr(0)) + x * y
    return out
def tau(i, k): return f'κs {i} (cc (Sum.inl {k})) * t (rr (Sum.inl {i}), cc (Sum.inl {k}))'
lemmas = []; index = []
skipped = []
for lab in itertools.product((1, 2, 3), repeat=3):
    for x in itertools.product((1, 2, 3), repeat=3):
        for sg in (1, -1):
            if 1 not in lab and sg == -1: continue
            I = complex(0, 1)
            w2 = [I, 1, -1]
            w3 = [sg * I if l == 1 else (1 if l == 2 else -1) for l in lab]
            rat = [w3[k] / w2[k] for k in range(3)]
            okc = False
            for sg23 in (1, -1):
                w23 = [sg23 * I if l == 1 else (1 if l == 2 else -1) for l in x]
                th = rat[0] / w23[0]
                if all(abs(rat[k] - th * w23[k]) < 1e-12 for k in range(3)): okc = True
            if not okc: continue
            rels = []
            for i in range(3): rels.append([Fr(1) if v // 3 == i else Fr(0) for v in range(9)])
            v = [Fr(0)] * 9; v[2] += 1; v[4] += 1; rels.append(v)
            v = [Fr(0)] * 9
            for k in range(3):
                if lab[k] == 3: v[k] += 1
                if lab[k] == 2: v[6 + k] += 1
            rels.append(v)
            v = [Fr(0)] * 9
            for k in range(3):
                if x[k] == 3: v[3 + k] += 1
                if x[k] == 2: v[6 + k] += 1
            rels.append(v)
            free, M = nullsolve(rels)
            if len(free) != 3:
                skipped.append((lab, x, sg, 'rank')); continue
            # numerator coefficient (polynomial in j, as dict) of y_{ik} per unit tau0: and denominator text
            def num_poly(i, k):
                if i == 0: return {0: Fr(1)}
                if i == 1:
                    return {1: Fr(-1)} if k == 0 else ({0: Fr(1)} if k == 1 else {0: Fr(1)})
                l = lab[k]
                return {1: Fr(-sg)} if l == 1 else {0: Fr(1)}
            def den_text(i, k):
                kap = f'κs 0 (cc (Sum.inl {k}))'
                if i == 0: return kap
                if i == 1: return f'(c * {kap})' if k in (0, 1) else f'(-c * {kap})'
                l = lab[k]
                return f'(-c\' * {kap})' if l == 3 else f'(c\' * {kap})'
            def den_sign(i, k):
                if i == 1 and k == 2: return -1
                if i == 2 and lab[k] == 3: return -1
                return 1
            found = None
            for x0 in itertools.product(range(-3, 4), repeat=3):
                t0 = [sum((M[e][l] * x0[l] for l in range(3)), Fr(0)) for e in range(9)]
                P = {}
                for perm in itertools.permutations(range(3)):
                    term = {0: Fr(1)}
                    for i in range(3):
                        k = perm[i]
                        np_ = num_poly(i, k)
                        term = polymul(term, {d: c * t0[3 * i + k] * den_sign(i, k) for d, c in np_.items()})
                    for d, c in term.items(): P[d] = P.get(d, Fr(0)) + c
                A, B, C = P.get(0, Fr(0)), P.get(1, Fr(0)), P.get(2, Fr(0))
                a, b = A - C, B
                if a != 0 or b != 0:
                    found = (x0, t0, A, B, C, a, b); break
            if not found:
                skipped.append((lab, x, sg, 'perm0')); continue
            x0, t0, A, B, C, a, b = found
            name = f't3p_{"".join(map(str, lab))}_{"p" if sg == 1 else "m"}_{"".join(map(str, x))}'
            index.append((lab, x, sg, name))
            def wtext(l, k):
                kap = f'κs 0 (cc (Sum.inl {k}))'
                if l == 2: return f'c\' * {kap}'
                if l == 3: return f'-c\' * {kap}'
                return f'j * c\' * {kap}' if sg == 1 else f'-j * c\' * {kap}'
            r13 = [tau(0, k) for k in range(3) if lab[k] == 3] + [tau(2, k) for k in range(3) if lab[k] == 2]
            Lt = []
            Lt.append('set_option maxHeartbeats 1000000 in')
            Lt.append(f'theorem {name} {{L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)}} (hL : Lev 5 L)')
            Lt.append('    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)')
            Lt.append('    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)')
            Lt.append('    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)')
            Lt.append('    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)')
            Lt.append('    (c c\' j : ℂ) (hc : c ≠ 0) (hc\' : c\' ≠ 0) (hj : j * j = -1)')
            Lt.append('    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧')
            Lt.append('      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧')
            Lt.append('      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))')
            Lt.append(f'    (hw2 : κs 2 (cc (Sum.inl 0)) = {wtext(lab[0], 0)} ∧')
            Lt.append(f'      κs 2 (cc (Sum.inl 1)) = {wtext(lab[1], 1)} ∧')
            Lt.append(f'      κs 2 (cc (Sum.inl 2)) = {wtext(lab[2], 2)})')
            Lt.append('    (hrel : ∀ t ∈ blkL L rr cc,')
            Lt.append(f'      {tau(0, 2)} + {tau(1, 1)} = 0 ∧')
            Lt.append(f'      {" + ".join(r13)} = 0 ∧')
            r23 = [tau(1, k) for k in range(3) if x[k] == 3] + [tau(2, k) for k in range(3) if x[k] == 2]
            Lt.append(f'      {" + ".join(r23)} = 0) : False := by')
            Lt.append('  have hrs : ∀ t ∈ blkL L rr cc, ∀ i : Fin 3,')
            Lt.append('      κs i (cc (Sum.inl 0)) * t (rr (Sum.inl i), cc (Sum.inl 0)) +')
            Lt.append('        κs i (cc (Sum.inl 1)) * t (rr (Sum.inl i), cc (Sum.inl 1)) +')
            Lt.append('        κs i (cc (Sum.inl 2)) * t (rr (Sum.inl i), cc (Sum.inl 2)) = 0 := by')
            Lt.append('    intro t ht i')
            Lt.append('    obtain ⟨htL, ht0⟩ := (mem_blkL L rr cc t).mp ht')
            Lt.append('    have e := sum_supp3 cc (fun m => t (rr (Sum.inl i), m) * κs i m)')
            Lt.append('      (fun b => by simp only [ht0 i b, zero_mul])')
            Lt.append('    have f := hFK i t htL')
            Lt.append('    rw [dotL_apply] at f')
            Lt.append('    simp only [rowMap_apply] at f')
            Lt.append('    rw [f] at e')
            Lt.append('    linear_combination -e')
            Lt.append('  obtain ⟨a1, a2, a3⟩ := hw1')
            Lt.append('  obtain ⟨b1, b2, b3⟩ := hw2')
            Lt.append('  have n0 := hκs 0 (cc (Sum.inl 0))')
            Lt.append('  have n1 := hκs 0 (cc (Sum.inl 1))')
            Lt.append('  have n2 := hκs 0 (cc (Sum.inl 2))')
            Lt.append('  have hj0 := jsq_ne hj')
            Mlit = '![' + ', '.join('![' + ', '.join('![' + ', '.join(fmt(M[3 * i + k][l]) for l in range(3)) + ']' for k in range(3)) + ']' for i in range(3)) + ']'
            pil = '![' + ', '.join(str(f // 3) for f in free) + ']'
            pjl = '![' + ', '.join(str(f % 3) for f in free) + ']'
            x0l = '![' + ', '.join(fmt(v) for v in x0) + ']'
            def ytext(i, k):
                tv = t0[3 * i + k]
                np_ = num_poly(i, k)
                if 1 in np_:
                    coef = np_[1] * tv
                    num = f'j * {fmt(coef)}'
                else:
                    num = fmt(np_[0] * tv)
                return f'{num} / {den_text(i, k)}'
            Ylit = '![' + ', '.join('![' + ', '.join(ytext(i, k) for k in range(3)) + ']' for i in range(3)) + ']'
            Lt.append(f'  refine stest_lift3\' hL h9 rr cc h0 (fun i j => κs i (cc (Sum.inl j))) (fun i j => hκs i _)')
            Lt.append(f'    {Mlit}')
            Lt.append(f'    {pil} {pjl} ?_ {x0l}')
            Lt.append(f'    {Ylit} ?_ ?_')
            # hM
            Lt.append('  · intro t ht i j')
            Lt.append('    have R0 := hrs t ht 0')
            Lt.append('    have R1 := hrs t ht 1')
            Lt.append('    have R2 := hrs t ht 2')
            Lt.append('    obtain ⟨E12, E13, E23⟩ := hrel t ht')
            Lt.append('    rw [Fin.sum_univ_three]')
            Lt.append('    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases j with rfl | rfl | rfl')
            names = ['R0', 'R1', 'R2', 'E12', 'E13', 'E23']
            for i in range(3):
                for k in range(3):
                    e = 3 * i + k
                    rhs = [Fr(0)] * 9; rhs[e] += 1
                    for l in range(3): rhs[free[l]] -= M[e][l]
                    lam = solve_rows(rels, rhs)
                    terms = ' +\n        '.join(f'{fmt(M[e][l])} * ({tau(free[l] // 3, free[l] % 3)})' for l in range(3))
                    Lt.append(f'    · show {tau(i, k)} =')
                    Lt.append(f'        {terms}')
                    comb = ' + '.join(f'{fmt(lam[r])} * {names[r]}' for r in range(6) if lam[r] != 0)
                    Lt.append(f'      linear_combination {comb}' if comb else '      ring')
            # hy
            Lt.append('  · intro i j')
            Lt.append('    rw [Fin.sum_univ_three]')
            Lt.append('    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases j with rfl | rfl | rfl')
            for i in range(3):
                for k in range(3):
                    e = 3 * i + k
                    s = ' + '.join(f'{fmt(M[e][l])} * {fmt(x0[l])}' for l in range(3))
                    Lt.append(f'    · show ({s}) / κs {i} (cc (Sum.inl {k})) = {ytext(i, k)}')
                    kap = f'κs 0 (cc (Sum.inl {k}))'
                    corner = (i == 1 and k == 0) or (i == 2 and lab[k] == 1)
                    wname = None if i == 0 else (['a1', 'a2', 'a3'][k] if i == 1 else ['b1', 'b2', 'b3'][k])
                    if i == 0:
                        Lt.append('      ring')
                    elif not corner:
                        Lt.append(f'      rw [{wname}]')
                        Lt.append('      ring')
                    else:
                        cc_ = 'c' if i == 1 else 'c\''
                        hcc = 'hc' if i == 1 else 'hc\''
                        if i == 2 and sg == -1:
                            d1 = f'(mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hj0) {hcc}) n{k})'
                        else:
                            d1 = f'(mul_ne_zero (mul_ne_zero hj0 {hcc}) n{k})'
                        Lt.append(f'      rw [{wname}, div_eq_div_iff {d1} (mul_ne_zero {hcc} n{k})]')
                        Lt.append(f'      linear_combination ({fmt(t0[e])} * {cc_} * {kap}) * hj')
            # hperm
            Lt.append('  · intro h0\'')
            Lt.append(f'    have hP : (Matrix.of ({Ylit} : Fin 3 → Fin 3 → ℂ)).permanent *')
            Lt.append(f'        (c * c\' * κs 0 (cc (Sum.inl 0)) * κs 0 (cc (Sum.inl 1)) * κs 0 (cc (Sum.inl 2))) =')
            Lt.append(f'        {fmt(A)} + {fmt(B)} * j + {fmt(C)} * j ^ 2 := by')
            Lt.append('      rw [permanent_three]')
            Lt.append('      simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,')
            Lt.append('        Matrix.head_cons, Matrix.tail_cons]')
            Lt.append('      field_simp')
            Lt.append('      ring')
            Lt.append('    rw [h0\', zero_mul] at hP')
            NN = a * a + b * b
            Lt.append(f'    have hN : ({fmt(NN)} : ℂ) = 0 := by')
            Lt.append(f'      linear_combination (-({fmt(a)} - {fmt(b)} * j)) * hP + ({fmt(b)} ^ 2 - {fmt(C)} * ({fmt(a)} - {fmt(b)} * j)) * hj')
            Lt.append('    norm_num at hN')
            lemmas.append('\n'.join(Lt))
open('/home/kevxhk/work/L-gct-210/lean/zbf/r6_7.txt', 'w', encoding='utf-8').write('\n\n' + '\n\n'.join(lemmas) + '\n')
for e in index: print(e)
print(len(lemmas), 'lemmas')
from collections import Counter
print('skipped', Counter(s[3] for s in skipped))
for s in skipped: print('SKIP', s)
