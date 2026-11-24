import sympy as sp, pickle, re
Afin,Bb=pickle.load(open('s8c.pkl','rb'))
def L(e):
    s=sp.sstr(sp.expand(e)).replace('**','^')
    s=re.sub(r'\bu(\d)\b',r'uY Y \1',s)
    s=re.sub(r'\bp(\d)\b',r'col Y 2 \1',s)
    s=re.sub(r'\bq(\d)\b',r'col Y 3 \1',s)
    s=re.sub(r'\br(\d)\b',r'col Y 4 \1',s)
    s=re.sub(r'\bv(\d)\b',r'v \1',s)
    return s
txt=f'''
set_option maxRecDepth 20000 in
theorem c1R_x3c (K : Submodule ℂ M45) (hdef : DefLine K mTC) (v : V4) (hv1 : tau v = 0)
    (hv2 : ip v v = 0) (Y : M45) (hY : Y ∈ K) (Z : M45) (hZ : Z ∈ K) (hu : uY Z = 0) (a b : ℂ)
    (c2 : col Z 2 = a • v) (c3 : col Z 3 = b • v) (c4 : col Z 4 = (-(a + b)) • v) :
    4 * ((a * b + a * (-(a + b)) + b * (-(a + b))) * t3 (uY Y) v v + a * b * t3 v v (col Y 4)
      + a * (-(a + b)) * t3 v v (col Y 3) + b * (-(a + b)) * t3 v v (col Y 2)) = 0 := by
  have e1 := (TC5_deg_i K hdef (Y + Z) (K.add_mem hY hZ)).2.2.1
  have em := (TC5_deg_i K hdef (Y - Z) (K.sub_mem hY hZ)).2.2.1
  have e0 := (TC5_deg_i K hdef Y hY).2.2.1
  have hup : uY (Y + Z) = uY Y := by
    funext k
    have g := congrFun hu k
    simp only [uY, Pi.add_apply, Pi.zero_apply] at g ⊢
    linear_combination g
  have hum : uY (Y - Z) = uY Y := by
    funext k
    have g := congrFun hu k
    simp only [uY, Pi.sub_apply, Pi.zero_apply] at g ⊢
    linear_combination -g
  have hcp : ∀ j, col (Y + Z) j = col Y j + col Z j := fun j => rfl
  have hcm : ∀ j, col (Y - Z) j = col Y j - col Z j := fun j => rfl
  rw [hup, hcp, hcp, hcp, c2, c3, c4] at e1
  rw [hum, hcm, hcm, hcm, c2, c3, c4] at em
  simp only [X3c, tau, ip, t3, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 em e0 hv1 hv2 ⊢
  linear_combination e1 + em - 2 * e0 - ({L(Afin)}) * hv1 - ({L(Bb)}) * hv2
'''
open('../lean/fl/p5v.part','w').write(txt)
print('ok')
