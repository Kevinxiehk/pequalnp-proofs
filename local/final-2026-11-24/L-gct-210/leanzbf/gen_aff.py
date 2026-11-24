# Generator: affine (cube-test) core lemmas a3p_* via stest_affine -> lean/zbf/r7_5.txt
# pattern on the pair-12 transversal (p corner, q Q12, s B12): lab13, lab23 (1 = corner, 2 = Q, 3 = B), corner sign sg13 = +1.
import itertools, random
from fractions import Fraction as Fr
exec(open('/home/kevxhk/work/L-gct-210/leanzbf/gen_t1p.py').read().split('lemmas = []; index = []')[0])
def padd(a, b):
    out = dict(a)
    for k, v in b.items(): out[k] = out.get(k, Fr(0)) + v
    return {k: v for k, v in out.items() if v != 0}
def pscale(a, s): return {k: v * s for k, v in a.items() if v * s != 0}
def pmul(a, b):
    out = {}
    for i, x in a.items():
        for k, y in b.items(): out[i + k] = out.get(i + k, Fr(0)) + x * y
    return {k: v for k, v in out.items() if v != 0}
def pred(a):  # reduce mod j^2 + 1 -> (A, B)
    A = Fr(0); B = Fr(0)
    for d, v in a.items():
        r = d % 4
        if r == 0: A += v
        elif r == 1: B += v
        elif r == 2: A -= v
        else: B -= v
    return A, B
def pdivq(a):  # a = (A + B j) + (j^2 + 1) * Q ; return Q
    num = dict(a); q = {}
    while num and max(num) >= 2:
        d = max(num); v = num[d]
        q[d - 2] = q.get(d - 2, Fr(0)) + v
        num[d] = num[d] - v; num[d - 2] = num.get(d - 2, Fr(0)) - v
        num = {k: x for k, x in num.items() if x != 0}
    return {k: v for k, v in q.items() if v != 0}
def ptext(a):
    if not a: return '0'
    parts = []
    for d in sorted(a):
        mon = '' if d == 0 else (' * j' if d == 1 else f' * j ^ {d}')
        parts.append(f'{fmt(a[d])}{mon}')
    return '(' + ' + '.join(parts) + ')'
K = {0: Fr(1, 2), 1: Fr(-1, 2)}
def tauH(i, k): return f'κs {i} (cc (Sum.inl {k})) * hat 5 w (rr (Sum.inl {i}), cc (Sum.inl {k}))'
def gen(name, lab13, lab23, sg=1):
    rels = []; consts = []
    for i in range(3):
        rels.append([Fr(1) if v // 3 == i else Fr(0) for v in range(9)]); consts.append({0: Fr(1)})
    v = [Fr(0)] * 9; v[2] += 1; v[4] += 1; rels.append(v); consts.append(K)
    v = [Fr(0)] * 9
    for k in range(3):
        if lab13[k] == 3: v[k] += 1
        if lab13[k] == 2: v[6 + k] += 1
    rels.append(v); consts.append(K)
    v = [Fr(0)] * 9
    for k in range(3):
        if lab23[k] == 3: v[3 + k] += 1
        if lab23[k] == 2: v[6 + k] += 1
    rels.append(v); consts.append(K)
    free, M = nullsolve(rels)
    assert len(free) == 3, free
    # lambda per entry e, and N_e = sum lambda_r const_r
    lam = {}; Nv = {}
    for e in range(9):
        rhs = [Fr(0)] * 9; rhs[e] += 1
        for l in range(3): rhs[free[l]] -= M[e][l]
        lam[e] = solve_rows(rels, rhs)
        Nv[e] = {}
        for r in range(6): Nv[e] = padd(Nv[e], pscale(consts[r], lam[e][r]))
    # weights: row1 (j c, c, -c); row2 by lab13 (corner sg*j c', Q c', B -c')
    def num_extra(i, k):  # factor multiplying the numerator because of a j in the weight: y = tau/(w * kappa)
        if i == 1 and k == 0: return {1: Fr(-1)}           # 1/(j c) = -j/c
        if i == 2 and lab13[k] == 1: return {1: Fr(-sg)}     # 1/(sg j c') = -sg j / c'
        return {0: Fr(1)}
    def den_text(i, k):
        kap = f'κs 0 (cc (Sum.inl {k}))'
        if i == 0: return kap
        if i == 1: return f'(c * {kap})' if k in (0, 1) else f'(-c * {kap})'
        return f'(-c\' * {kap})' if lab13[k] == 3 else f'(c\' * {kap})'
    def den_sign(i, k):
        if i == 1 and k == 2: return -1
        if i == 2 and lab13[k] == 3: return -1
        return 1
    def entry_num(x0, e):  # numerator polynomial of tau_e at point (free = x0, c = 1)
        p = {}
        for l in range(3): p = padd(p, {0: M[e][l] * x0[l]})
        return padd(p, Nv[e])
    def perm_poly(x0):
        P = {}
        for perm in itertools.permutations(range(3)):
            term = {0: Fr(1)}
            for i in range(3):
                k = perm[i]; e = 3 * i + k
                term = pmul(term, pscale(pmul(entry_num(x0, e), num_extra(i, k)), den_sign(i, k)))
            P = padd(P, term)
        return P
    found = None
    cands = list(itertools.product(range(-2, 3), repeat=3))
    for x0 in cands:
        P0 = perm_poly(x0)
        for x1 in cands:
            if x1 <= x0: continue
            P1 = perm_poly(x1)
            D = padd(P0, pscale(P1, -1))
            A, B = pred(D)
            if A != 0 or B != 0:
                found = (x0, x1, P0, P1, D, A, B); break
        if found: break
    assert found
    x0, x1, P0, P1, D, A, B = found
    Q = pdivq(padd(D, {0: -A, 1: -B}))
    # check: D == A + B j + (j^2+1) Q
    chk = padd(padd(D, {0: -A, 1: -B}), pscale(pmul({2: Fr(1), 0: Fr(1)}, Q), -1))
    assert not chk, chk
    def wtext(l, k):
        kap = f'κs 0 (cc (Sum.inl {k}))'
        if l == 2: return f'c\' * {kap}'
        if l == 3: return f'-c\' * {kap}'
        return f'j * c\' * {kap}' if sg == 1 else f'-j * c\' * {kap}'
    def reltext(entries):
        return ' + '.join(tauH(i, k) for (i, k) in entries)
    r13 = [(0, k) for k in range(3) if lab13[k] == 3] + [(2, k) for k in range(3) if lab13[k] == 2]
    r23 = [(1, k) for k in range(3) if lab23[k] == 3] + [(2, k) for k in range(3) if lab23[k] == 2]
    Ktext = '((1 - j) / 2)'
    L = []
    L.append('set_option maxHeartbeats 2000000 in')
    L.append(f'theorem {name} {{L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)}} (hL : Lev 5 L)')
    L.append('    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)')
    L.append('    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)')
    L.append('    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)')
    L.append('    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)')
    L.append('    (hsum : ∀ i, dotL (κs i) 1 = 1)')
    L.append('    (c c\' j : ℂ) (hc : c ≠ 0) (hc\' : c\' ≠ 0) (hj : j * j = -1)')
    L.append('    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧')
    L.append('      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧')
    L.append('      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))')
    L.append(f'    (hw2 : κs 2 (cc (Sum.inl 0)) = {wtext(lab13[0], 0)} ∧')
    L.append(f'      κs 2 (cc (Sum.inl 1)) = {wtext(lab13[1], 1)} ∧')
    L.append(f'      κs 2 (cc (Sum.inl 2)) = {wtext(lab13[2], 2)})')
    L.append('    (hrel : ∀ w ∈ blockSpace L rr cc,')
    L.append(f'      {reltext([(0, 2), (1, 1)])} = w.1 * {Ktext} ∧')
    L.append(f'      {reltext(r13)} = w.1 * {Ktext} ∧')
    L.append(f'      {reltext(r23)} = w.1 * {Ktext}) : False := by')
    L.append('  have hrs : ∀ w ∈ blockSpace L rr cc, ∀ i : Fin 3,')
    L.append('      ' + ' +\n        '.join(tauH('i', k) for k in range(3)) + ' = w.1 := by')
    L += ['    intro w hw i',
          '    obtain ⟨hwL, hw0⟩ := (mem_blockSpace L rr cc w).mp hw',
          '    have e := sum_supp3 cc (fun m => hat 5 w (rr (Sum.inl i), m) * κs i m)',
          '      (fun b => by simp only [hat_apply, hw0 i b, zero_mul])',
          '    have f := hFK i w.2 hwL',
          '    have g := hsum i',
          '    rw [dotL_apply] at f g',
          '    simp only [rowMap_apply, Pi.one_apply, one_mul] at f g',
          '    have e3 : ∀ m, hat 5 w (rr (Sum.inl i), m) * κs i m =',
          '        w.1 * κs i m + w.2 (rr (Sum.inl i), m) * κs i m := fun m => by',
          '      rw [hat_apply]',
          '      ring',
          '    have e2 : ∑ m, hat 5 w (rr (Sum.inl i), m) * κs i m = w.1 := by',
          '      rw [Finset.sum_congr rfl (fun m _ => e3 m), Finset.sum_add_distrib, ← Finset.mul_sum, g, f,',
          '        mul_one, add_zero]',
          '    rw [e2] at e',
          '    linear_combination -e',
          '  obtain ⟨a1, a2, a3⟩ := hw1',
          '  obtain ⟨b1, b2, b3⟩ := hw2',
          '  have n0 := hκs 0 (cc (Sum.inl 0))',
          '  have n1 := hκs 0 (cc (Sum.inl 1))',
          '  have n2 := hκs 0 (cc (Sum.inl 2))',
          '  have hj0 := jsq_ne hj']
    Mlit = '![' + ', '.join('![' + ', '.join('![' + ', '.join(fmt(M[3 * i + k][l]) for l in range(3)) + ']' for k in range(3)) + ']' for i in range(3)) + ']'
    Nlit = '![' + ', '.join('![' + ', '.join(ptext(Nv[3 * i + k]) for k in range(3)) + ']' for i in range(3)) + ']'
    pil = '![' + ', '.join(str(f // 3) for f in free) + ']'
    pjl = '![' + ', '.join(str(f % 3) for f in free) + ']'
    def ylit(x0):
        def yt(i, k):
            e = 3 * i + k
            num = pmul(entry_num(x0, e), num_extra(i, k))
            return f'{ptext(num)} / {den_text(i, k)}'
        return '![' + ', '.join('![' + ', '.join(yt(i, k) for k in range(3)) + ']' for i in range(3)) + ']'
    Y0, Y1 = ylit(x0), ylit(x1)
    x0l = '![' + ', '.join(fmt(v) for v in x0) + ']'
    x1l = '![' + ', '.join(fmt(v) for v in x1) + ']'
    L.append('  refine stest_affine hL h9 rr cc h0 (fun i j => κs i (cc (Sum.inl j))) (fun i j => hκs i _)')
    L.append(f'    {Mlit}')
    L.append(f'    {Nlit}')
    L.append(f'    {pil} {pjl} ?_ {x0l} {x1l}')
    L.append(f'    {Y0}')
    L.append(f'    {Y1} ?_ ?_ ?_')
    L += ['  · intro w hw i j', '    have R0 := hrs w hw 0', '    have R1 := hrs w hw 1', '    have R2 := hrs w hw 2',
          '    obtain ⟨E12, E13, E23⟩ := hrel w hw', '    rw [Fin.sum_univ_three]',
          '    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases j with rfl | rfl | rfl']
    names = ['R0', 'R1', 'R2', 'E12', 'E13', 'E23']
    for i in range(3):
        for k in range(3):
            e = 3 * i + k
            terms = ' +\n        '.join(f'{fmt(M[e][l])} * ({tauH(free[l] // 3, free[l] % 3)})' for l in range(3))
            L.append(f'    · show {tauH(i, k)} =')
            L.append(f'        {terms} + {ptext(Nv[e])} * w.1')
            comb = ' + '.join(f'{fmt(lam[e][r])} * {names[r]}' for r in range(6) if lam[e][r] != 0)
            L.append(f'      linear_combination {comb}' if comb else '      ring')
    def hy_block(x0, Y):
        B = ['  · intro i j', '    rw [Fin.sum_univ_three]',
             '    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases j with rfl | rfl | rfl']
        for i in range(3):
            for k in range(3):
                e = 3 * i + k
                s = ' + '.join(f'{fmt(M[e][l])} * {fmt(x0[l])}' for l in range(3))
                num = pmul(entry_num(x0, e), num_extra(i, k))
                B.append(f'    · show ({s} + {ptext(Nv[e])}) / κs {i} (cc (Sum.inl {k})) = {ptext(num)} / {den_text(i, k)}')
                kap = f'κs 0 (cc (Sum.inl {k}))'
                corner = (i == 1 and k == 0) or (i == 2 and lab13[k] == 1)
                wname = None if i == 0 else (['a1', 'a2', 'a3'][k] if i == 1 else ['b1', 'b2', 'b3'][k])
                if i == 0:
                    B.append('      ring')
                elif not corner:
                    B.append(f'      rw [{wname}]')
                    B.append('      ring')
                else:
                    cc_ = 'c' if i == 1 else 'c\''
                    hcc = 'hc' if i == 1 else 'hc\''
                    if i == 2 and sg == -1:
                        d1 = f'(mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hj0) {hcc}) n{k})'
                    else:
                        d1 = f'(mul_ne_zero (mul_ne_zero hj0 {hcc}) n{k})'
                    base = ptext(entry_num(x0, e))
                    B.append(f'      rw [{wname}, div_eq_div_iff {d1} (mul_ne_zero {hcc} n{k})]')
                    B.append(f'      linear_combination ({base} * {cc_} * {kap}) * hj')
        return B
    L += hy_block(x0, Y0) + hy_block(x1, Y1)
    Dt = '(c * c\' * κs 0 (cc (Sum.inl 0)) * κs 0 (cc (Sum.inl 1)) * κs 0 (cc (Sum.inl 2)))'
    L += ['  · intro heq',
          f'    have hP0 : (Matrix.of ({Y0} : Fin 3 → Fin 3 → ℂ)).permanent * {Dt} = {ptext(P0)} := by',
          '      rw [permanent_three]',
          '      simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,',
          '        Matrix.head_cons, Matrix.tail_cons]',
          '      field_simp',
          '      ring',
          f'    have hP1 : (Matrix.of ({Y1} : Fin 3 → Fin 3 → ℂ)).permanent * {Dt} = {ptext(P1)} := by',
          '      rw [permanent_three]',
          '      simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,',
          '        Matrix.head_cons, Matrix.tail_cons]',
          '      field_simp',
          '      ring']
    NN = A * A + B * B
    ab = f'({fmt(A)} - {fmt(B)} * j)'
    L += [f'    have hN : ({fmt(NN)} : ℂ) = 0 := by',
          f'      linear_combination (-{ab}) * hP0 + {ab} * hP1 + ({ab} * {Dt}) * heq +',
          f'        ({fmt(B)} ^ 2 - {ab} * {ptext(Q)}) * hj',
          '    norm_num at hN']
    return '\n'.join(L), dict(free=free, x0=x0, x1=x1, A=A, B=B)
out = []
t1, i1 = gen('a3p_o1', (2, 1, 3), (2, 3, 1)); out.append(t1); print('o1', i1)
t2, i2 = gen('a3p_o2', (1, 2, 1), (1, 1, 2)); out.append(t2); print('o2', i2)
open('/home/kevxhk/work/L-gct-210/lean/zbf/r7_5.txt', 'w', encoding='utf-8').write('\n\n' + '\n\n'.join(out) + '\n')
print('written')
