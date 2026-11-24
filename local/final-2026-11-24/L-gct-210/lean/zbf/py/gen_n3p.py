import itertools, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_alg import *
# propositional sanity check of the final case analysis
def unsat():
    names=['p01','p02','p10','p12','p20','p21','S0','S1','S2']
    for vals in itertools.product([False,True],repeat=9):
        v=dict(zip(names,vals))
        ok = (v['p01'] or v['p02']) and (v['p10'] or v['p12']) and (v['p20'] or v['p21'])
        ok = ok and (not (v['p10'] and v['p20']) or v['S0'])
        ok = ok and (not (v['p01'] and not v['p02']) or v['S1']) and (not (v['p02'] and not v['p01']) or v['S2'])
        ok = ok and (not (v['p10'] and not v['p12']) or v['S0']) and (not (v['p12'] and not v['p10']) or v['S2'])
        ok = ok and (not (v['p20'] and not v['p21']) or v['S0']) and (not (v['p21'] and not v['p20']) or v['S1'])
        ok = ok and not (v['S0'] and v['S1']) and not (v['S0'] and v['S2']) and not (v['S1'] and v['S2'])
        ok = ok and not (v['S0'] and v['p01'] and v['p02']) and not (v['S1'] and v['p10'] and v['p12']) and not (v['S2'] and v['p20'] and v['p21'])
        if ok: return False
    return True
assert unsat()
out=[]
out.append('''def vec3 (a0 a1 a2 : ℂ) : Fin 3 → ℂ := fun i => if i = 0 then a0 else if i = 1 then a1 else a2

theorem vec3_0 (a0 a1 a2 : ℂ) : vec3 a0 a1 a2 0 = a0 := by simp [vec3]

theorem vec3_1 (a0 a1 a2 : ℂ) : vec3 a0 a1 a2 1 = a1 := by simp [vec3]

theorem vec3_2 (a0 a1 a2 : ℂ) : vec3 a0 a1 a2 2 = a2 := by simp [vec3]

def Bad (b W Y : Fin 3 × Fin 3 → ℂ) : Prop :=
  pm b ≠ 0 ∧ (∀ α β : Fin 3 → ℂ, pm (fun p => b p + α p.1 * W p + β p.2 * Y p) = pm b) ∧
    (∀ r, ∃ j, W (r, j) ≠ 0) ∧ ∀ j, ∃ i, Y (i, j) ≠ 0
''')
out.append('''theorem bad_expand {b W Y : Fin 3 × Fin 3 → ℂ} (h : Bad b W Y) (a0 a1 a2 c0 c1 c2 : ℂ) :
    %s =
      %s := by
  have h1 := h.2.1 (vec3 a0 a1 a2) (vec3 c0 c1 c2)
  simp only [pm, permanent_three, Matrix.of_apply, vec3_0, vec3_1, vec3_2] at h1
  linear_combination h1

theorem bad_pm {b W Y : Fin 3 × Fin 3 → ℂ} (h : Bad b W Y) :
    %s ≠ 0 := by
  have h1 := h.1
  simp only [pm, permanent_three, Matrix.of_apply] at h1
  intro h0
  exact h1 (by linear_combination h0)

theorem cancel_left {x y : ℂ} (hx : x ≠ 0) (h : x * y = 0) : y = 0 :=
  (mul_eq_zero.mp h).resolve_left hx
'''%(Ptext(VARS,frozenset()),pmtext(),pmtext()))
# X4c
z4={('W',0,1),('W',0,2)}
out.append('''theorem bad_X4c {b W Y : Fin 3 × Fin 3 → ℂ} (h : Bad b W Y) (hW01 : W (0, 1) = 0)
    (hW02 : W (0, 2) = 0) (hW00 : W (0, 0) ≠ 0) : W (1, 1) * Y (2, 2) = 0 := by
%s
%s
  have k2 : W (0, 0) * (W (1, 1) * Y (2, 2)) = 0 := by linear_combination k1
  exact cancel_left hW00 k2
'''%(hexp_block(z4,['hW01','hW02']),have_coef('k1',['a0','a1','c2'],z4)))
# X3c
z3={('W',0,1),('W',0,2),('W',1,0),('W',1,2)}
coefs3="\n".join(have_coef(n,S,z3) for n,S in [('k01',['a0','a1']),('k012',['a0','a1','a2']),('k01c',['a0','a1','c2']),('k0',['a0']),('k02',['a0','a2']),('k0c',['a0','c2']),('k02c',['a0','a2','c2']),('k1',['a1']),('k12',['a1','a2']),('k1c',['a1','c2']),('k12c',['a1','a2','c2']),('kc',['c2'])])
out.append('''theorem bad_X3c {b W Y : Fin 3 × Fin 3 → ℂ} (h : Bad b W Y) (hW01 : W (0, 1) = 0)
    (hW02 : W (0, 2) = 0) (hW10 : W (1, 0) = 0) (hW12 : W (1, 2) = 0) : False := by
  have hb := bad_pm h
  have hW00 : W (0, 0) ≠ 0 := by
    obtain ⟨j, hj⟩ := h.2.2.1 0
    rcases fin3_cases j with rfl | rfl | rfl
    · exact hj
    · exact absurd hW01 hj
    · exact absurd hW02 hj
  have hW11 : W (1, 1) ≠ 0 := by
    obtain ⟨j, hj⟩ := h.2.2.1 1
    rcases fin3_cases j with rfl | rfl | rfl
    · exact absurd hW10 hj
    · exact hj
    · exact absurd hW12 hj
%s
%s
  have hb22 : b (2, 2) = 0 := by
    have e : W (0, 0) * (W (1, 1) * b (2, 2)) = 0 := by linear_combination k01
    exact cancel_left hW11 (cancel_left hW00 e)
  have hW22 : W (2, 2) = 0 := by
    have e : W (0, 0) * (W (1, 1) * W (2, 2)) = 0 := by linear_combination k012
    exact cancel_left hW11 (cancel_left hW00 e)
  have hY22 : Y (2, 2) = 0 := by
    have e : W (0, 0) * (W (1, 1) * Y (2, 2)) = 0 := by linear_combination k01c
    exact cancel_left hW11 (cancel_left hW00 e)
  have e2 : b (1, 2) * W (2, 1) = 0 := by
    have e : W (0, 0) * (b (1, 2) * W (2, 1)) = 0 := by
      linear_combination k02 - W (0, 0) * b (1, 1) * hW22
    exact cancel_left hW00 e
  have e3 : Y (1, 2) * b (2, 1) = 0 := by
    have e : W (0, 0) * (Y (1, 2) * b (2, 1)) = 0 := by
      linear_combination k0c - W (0, 0) * b (1, 1) * hY22
    exact cancel_left hW00 e
  have e4 : Y (1, 2) * W (2, 1) = 0 := by
    have e : W (0, 0) * (Y (1, 2) * W (2, 1)) = 0 := by linear_combination k02c
    exact cancel_left hW00 e
  have f2 : b (0, 2) * W (2, 0) = 0 := by
    have e : W (1, 1) * (b (0, 2) * W (2, 0)) = 0 := by
      linear_combination k12 - b (0, 0) * W (1, 1) * hW22
    exact cancel_left hW11 e
  have f3 : Y (0, 2) * b (2, 0) = 0 := by
    have e : W (1, 1) * (Y (0, 2) * b (2, 0)) = 0 := by
      linear_combination k1c - b (0, 0) * W (1, 1) * hY22
    exact cancel_left hW11 e
  have f4 : Y (0, 2) * W (2, 0) = 0 := by
    have e : W (1, 1) * (Y (0, 2) * W (2, 0)) = 0 := by linear_combination k12c
    exact cancel_left hW11 e
  have g : Y (0, 2) * (b (1, 0) * b (2, 1) + b (1, 1) * b (2, 0)) +
      Y (1, 2) * (b (0, 0) * b (2, 1) + b (0, 1) * b (2, 0)) = 0 := by
    linear_combination kc - (b (0, 0) * b (1, 1) + b (0, 1) * b (1, 0)) * hY22
  have hrow2 : W (2, 0) ≠ 0 ∨ W (2, 1) ≠ 0 := by
    obtain ⟨j, hj⟩ := h.2.2.1 2
    rcases fin3_cases j with rfl | rfl | rfl
    · exact Or.inl hj
    · exact Or.inr hj
    · exact absurd hW22 hj
  have hcol2 : Y (0, 2) ≠ 0 ∨ Y (1, 2) ≠ 0 := by
    obtain ⟨i, hi⟩ := h.2.2.2 2
    rcases fin3_cases i with rfl | rfl | rfl
    · exact Or.inl hi
    · exact Or.inr hi
    · exact absurd hY22 hi
  by_cases hW21 : W (2, 1) = 0
  · have hW20 : W (2, 0) ≠ 0 := hrow2.resolve_right (not_not.mpr hW21)
    have hY02 : Y (0, 2) = 0 := (mul_eq_zero.mp f4).resolve_right hW20
    have hb02 : b (0, 2) = 0 := (mul_eq_zero.mp f2).resolve_right hW20
    have hY12 : Y (1, 2) ≠ 0 := hcol2.resolve_left (not_not.mpr hY02)
    have hb21 : b (2, 1) = 0 := cancel_left hY12 e3
    have hE : b (0, 1) * b (2, 0) = 0 := by
      have e : Y (1, 2) * (b (0, 1) * b (2, 0)) = 0 := by
        linear_combination g - (b (1, 0) * b (2, 1) + b (1, 1) * b (2, 0)) * hY02 -
          Y (1, 2) * b (0, 0) * hb21
      exact cancel_left hY12 e
    apply hb
    linear_combination (b (0, 0) * b (1, 1) + b (0, 1) * b (1, 0)) * hb22 +
      b (0, 0) * b (1, 2) * hb21 + b (1, 2) * hE +
      (b (1, 0) * b (2, 1) + b (1, 1) * b (2, 0)) * hb02
  · have hY12 : Y (1, 2) = 0 := (mul_eq_zero.mp e4).resolve_right hW21
    have hb12 : b (1, 2) = 0 := (mul_eq_zero.mp e2).resolve_right hW21
    have hY02 : Y (0, 2) ≠ 0 := hcol2.resolve_right (not_not.mpr hY12)
    have hb20 : b (2, 0) = 0 := cancel_left hY02 f3
    have hE : b (1, 0) * b (2, 1) = 0 := by
      have e : Y (0, 2) * (b (1, 0) * b (2, 1)) = 0 := by
        linear_combination g - Y (0, 2) * b (1, 1) * hb20 -
          (b (0, 0) * b (2, 1) + b (0, 1) * b (2, 0)) * hY12
      exact cancel_left hY02 e
    apply hb
    linear_combination (b (0, 0) * b (1, 1) + b (0, 1) * b (1, 0)) * hb22 +
      (b (0, 0) * b (2, 1) + b (0, 1) * b (2, 0)) * hb12 + b (0, 2) * hE +
      b (0, 2) * b (1, 1) * hb20
'''%(hexp_block(z3,['hW01','hW02','hW10','hW12']),coefs3))
# X1c
z1={('Y',1,0),('Y',2,0),('Y',1,1),('Y',2,1)}
coefs1="\n".join(have_coef(n,S,z1) for n,S in [('k1',['a1']),('k1c0',['a1','c0']),('k1c1',['a1','c1']),('k12',['a1','a2']),('k12c0',['a1','a2','c0']),('k12c1',['a1','a2','c1'])])
out.append('''theorem bad_X1c {b W Y : Fin 3 × Fin 3 → ℂ} (h : Bad b W Y) (hY10 : Y (1, 0) = 0)
    (hY20 : Y (2, 0) = 0) (hY11 : Y (1, 1) = 0) (hY21 : Y (2, 1) = 0) : False := by
  have hb := bad_pm h
  have hY00 : Y (0, 0) ≠ 0 := by
    obtain ⟨i, hi⟩ := h.2.2.2 0
    rcases fin3_cases i with rfl | rfl | rfl
    · exact hi
    · exact absurd hY10 hi
    · exact absurd hY20 hi
  have hY01 : Y (0, 1) ≠ 0 := by
    obtain ⟨i, hi⟩ := h.2.2.2 1
    rcases fin3_cases i with rfl | rfl | rfl
    · exact hi
    · exact absurd hY11 hi
    · exact absurd hY21 hi
%s
%s
  have hb02 : b (0, 2) ≠ 0 := by
    intro hb02
    have d0 : -(b (0, 0)) / Y (0, 0) * Y (0, 0) = -(b (0, 0)) := by field_simp
    have d1 : -(b (0, 1)) / Y (0, 1) * Y (0, 1) = -(b (0, 1)) := by field_simp
    apply hb
    linear_combination (-1 : ℂ) * hexp 0 0 0 (-(b (0, 0)) / Y (0, 0)) (-(b (0, 1)) / Y (0, 1)) 0 +
      (b (1, 1) * b (2, 2) + b (1, 2) * b (2, 1)) * d0 +
      (b (1, 0) * b (2, 2) + b (1, 2) * b (2, 0)) * d1 +
      (b (1, 0) * b (2, 1) + b (1, 1) * b (2, 0)) * hb02
  have i_b : W (1, 1) * b (2, 2) + W (1, 2) * b (2, 1) = 0 := by
    have e : Y (0, 0) * (W (1, 1) * b (2, 2) + W (1, 2) * b (2, 1)) = 0 := by
      linear_combination k1c0
    exact cancel_left hY00 e
  have ii_b : W (1, 0) * b (2, 2) + W (1, 2) * b (2, 0) = 0 := by
    have e : Y (0, 1) * (W (1, 0) * b (2, 2) + W (1, 2) * b (2, 0)) = 0 := by
      linear_combination k1c1
    exact cancel_left hY01 e
  have iii_b : W (1, 0) * b (2, 1) + W (1, 1) * b (2, 0) = 0 := by
    have e : b (0, 2) * (W (1, 0) * b (2, 1) + W (1, 1) * b (2, 0)) = 0 := by
      linear_combination k1 - b (0, 0) * i_b - b (0, 1) * ii_b
    exact cancel_left hb02 e
  have i_w : W (1, 1) * W (2, 2) + W (1, 2) * W (2, 1) = 0 := by
    have e : Y (0, 0) * (W (1, 1) * W (2, 2) + W (1, 2) * W (2, 1)) = 0 := by
      linear_combination k12c0
    exact cancel_left hY00 e
  have ii_w : W (1, 0) * W (2, 2) + W (1, 2) * W (2, 0) = 0 := by
    have e : Y (0, 1) * (W (1, 0) * W (2, 2) + W (1, 2) * W (2, 0)) = 0 := by
      linear_combination k12c1
    exact cancel_left hY01 e
  have iii_w : W (1, 0) * W (2, 1) + W (1, 1) * W (2, 0) = 0 := by
    have e : b (0, 2) * (W (1, 0) * W (2, 1) + W (1, 1) * W (2, 0)) = 0 := by
      linear_combination k12 - b (0, 0) * i_w - b (0, 1) * ii_w
    exact cancel_left hb02 e
  have key : ∃ lam : ℂ, b (2, 0) + -lam * W (2, 0) = 0 ∧ b (2, 1) + -lam * W (2, 1) = 0 ∧
      b (2, 2) + -lam * W (2, 2) = 0 := by
    obtain ⟨j2, hj2⟩ := h.2.2.1 2
    by_cases hA : W (1, 0) = 0
    · by_cases hB : W (1, 1) = 0
      · have hW12 : W (1, 2) ≠ 0 := by
          obtain ⟨j, hj⟩ := h.2.2.1 1
          rcases fin3_cases j with rfl | rfl | rfl
          · exact absurd hA hj
          · exact absurd hB hj
          · exact hj
        have hb21 : b (2, 1) = 0 :=
          cancel_left hW12 (by linear_combination i_b - b (2, 2) * hB)
        have hb20 : b (2, 0) = 0 :=
          cancel_left hW12 (by linear_combination ii_b - b (2, 2) * hA)
        have hW21 : W (2, 1) = 0 :=
          cancel_left hW12 (by linear_combination i_w - W (2, 2) * hB)
        have hW20 : W (2, 0) = 0 :=
          cancel_left hW12 (by linear_combination ii_w - W (2, 2) * hA)
        have hW22 : W (2, 2) ≠ 0 := by
          rcases fin3_cases j2 with rfl | rfl | rfl
          · exact absurd hW20 hj2
          · exact absurd hW21 hj2
          · exact hj2
        have d : b (2, 2) / W (2, 2) * W (2, 2) = b (2, 2) := by field_simp
        refine ⟨b (2, 2) / W (2, 2), ?_, ?_, ?_⟩
        · rw [hb20, hW20]
          ring
        · rw [hb21, hW21]
          ring
        · linear_combination (-1 : ℂ) * d
      · have hb20 : b (2, 0) = 0 :=
          cancel_left hB (by linear_combination iii_b - b (2, 1) * hA)
        have hW20 : W (2, 0) = 0 :=
          cancel_left hB (by linear_combination iii_w - W (2, 1) * hA)
        have hW21 : W (2, 1) ≠ 0 := by
          intro h0
          have hW22 : W (2, 2) = 0 :=
            cancel_left hB (by linear_combination i_w - W (1, 2) * h0)
          rcases fin3_cases j2 with rfl | rfl | rfl
          · exact hj2 hW20
          · exact hj2 h0
          · exact hj2 hW22
        have hx : b (2, 2) * W (2, 1) = b (2, 1) * W (2, 2) := by
          have e : W (1, 1) * (b (2, 2) * W (2, 1) - b (2, 1) * W (2, 2)) = 0 := by
            linear_combination W (2, 1) * i_b - b (2, 1) * i_w
          exact sub_eq_zero.mp (cancel_left hB e)
        have d : b (2, 1) / W (2, 1) * W (2, 1) = b (2, 1) := by field_simp
        refine ⟨b (2, 1) / W (2, 1), ?_, ?_, ?_⟩
        · rw [hb20, hW20]
          ring
        · linear_combination (-1 : ℂ) * d
        · have e : (b (2, 2) + -(b (2, 1) / W (2, 1)) * W (2, 2)) * W (2, 1) = 0 := by
            linear_combination hx - W (2, 2) * d
          exact (mul_eq_zero.mp e).resolve_right hW21
    · have hW20 : W (2, 0) ≠ 0 := by
        intro h0
        have hW22 : W (2, 2) = 0 :=
          cancel_left hA (by linear_combination ii_w - W (1, 2) * h0)
        have hW21 : W (2, 1) = 0 :=
          cancel_left hA (by linear_combination iii_w - W (1, 1) * h0)
        rcases fin3_cases j2 with rfl | rfl | rfl
        · exact hj2 h0
        · exact hj2 hW21
        · exact hj2 hW22
      have hx1 : b (2, 1) * W (2, 0) = b (2, 0) * W (2, 1) := by
        have e : W (1, 0) * (b (2, 1) * W (2, 0) - b (2, 0) * W (2, 1)) = 0 := by
          linear_combination W (2, 0) * iii_b - b (2, 0) * iii_w
        exact sub_eq_zero.mp (cancel_left hA e)
      have hx2 : b (2, 2) * W (2, 0) = b (2, 0) * W (2, 2) := by
        have e : W (1, 0) * (b (2, 2) * W (2, 0) - b (2, 0) * W (2, 2)) = 0 := by
          linear_combination W (2, 0) * ii_b - b (2, 0) * ii_w
        exact sub_eq_zero.mp (cancel_left hA e)
      have d : b (2, 0) / W (2, 0) * W (2, 0) = b (2, 0) := by field_simp
      refine ⟨b (2, 0) / W (2, 0), ?_, ?_, ?_⟩
      · linear_combination (-1 : ℂ) * d
      · have e : (b (2, 1) + -(b (2, 0) / W (2, 0)) * W (2, 1)) * W (2, 0) = 0 := by
          linear_combination hx1 - W (2, 1) * d
        exact (mul_eq_zero.mp e).resolve_right hW20
      · have e : (b (2, 2) + -(b (2, 0) / W (2, 0)) * W (2, 2)) * W (2, 0) = 0 := by
          linear_combination hx2 - W (2, 2) * d
        exact (mul_eq_zero.mp e).resolve_right hW20
  obtain ⟨lam, e0, e1, e2⟩ := key
  apply hb
  linear_combination (-1 : ℂ) * hexp 0 0 (-lam) 0 0 0 +
    (b (0, 0) * b (1, 1) + b (0, 1) * b (1, 0)) * e2 +
    (b (0, 0) * b (1, 2) + b (0, 2) * b (1, 0)) * e1 +
    (b (0, 1) * b (1, 2) + b (0, 2) * b (1, 1)) * e0
'''%(hexp_block(z1,['hY10','hY20','hY11','hY21']),coefs1))
open('/home/kevxhk/work/L-gct-210/lean/zbf/part3a.txt','w',encoding='utf-8').write("\n".join(out)+"\n")
print("written", sum(len(x) for x in out))
