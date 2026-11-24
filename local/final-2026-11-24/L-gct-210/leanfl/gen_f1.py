import sympy as sp, re
v=sp.symbols('v0:4'); w=sp.symbols('w0:4')
loc={f'v{i}':v[i] for i in range(4)}; loc.update({f'w{i}':w[i] for i in range(4)})
g=sum(a*b for a,b in zip(v,w))
gens=[sum(v), sum(w), sum(x**2 for x in v), sum(x**2 for x in w), sum(v[k]**2*w[k] for k in range(4)),
      3*sum(v[k]**2*w[k]**2 for k in range(4)) - g**2]
names=['h1','h2','h3','h4','h5','hq']
def rd(fn):
    txt=open(fn).read().replace('\n','')
    return [sp.expand(sp.sympify(p.replace('^','**'),locals=loc)) for p in txt.split(';') if p.strip()]
def L(e):
    s=sp.sstr(sp.expand(e)).replace('**','^')
    s=re.sub(r'\bv(\d)\b',r'v \1',s); s=re.sub(r'\bw(\d)\b',r'w \1',s)
    return s
out=[]
T=rd('sing12/f1_P.txt')
target=g**3*(v[0]*v[1]*v[2]*v[3])**2
assert sp.expand(sum(t*G for t,G in zip(T,gens))-target)==0
comb=' + '.join(f'({L(8*t)}) * {n}' for t,n in zip(T,names) if t!=0)
hdr='''(v w : V4) (h1 : tau v = 0) (h2 : tau w = 0) (h3 : ip v v = 0)
    (h4 : ip w w = 0) (h5 : t3 v v w = 0) (hq : 3 * t4 v v w w = ip v w ^ 2)'''
out.append(f'''
set_option maxRecDepth 20000 in
theorem F1_vprod {hdr} :
    8 * ((v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3) ^ 3 * (v 0 * v 1 * v 2 * v 3) ^ 2) = 0 := by
  simp only [tau, ip, t3, t4] at h1 h2 h3 h4 h5 hq
  linear_combination {comb}''')
for k in range(4):
    T=rd(f'sing12/f1_w{k}.txt')
    gk=gens+[v[k]]
    assert sp.expand(sum(t*G for t,G in zip(T,gk))-g**3*w[k]**2)==0
    comb=' + '.join(f'({L(8*t)}) * {n}' for t,n in zip(T,names+['hk']) if t!=0)
    out.append(f'''
set_option maxRecDepth 20000 in
theorem F1_w{k} {hdr} (hk : v {k} = 0) :
    8 * ((v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3) ^ 3 * w {k} ^ 2) = 0 := by
  simp only [tau, ip, t3, t4] at h1 h2 h3 h4 h5 hq
  linear_combination {comb}''')
out.append(f'''
theorem F1_zero_row {hdr} (hg : ip v w ≠ 0) : ∃ k, v k = 0 ∧ w k = 0 := by
  have hg3 : (v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3) ^ 3 ≠ 0 := pow_ne_zero 3 hg
  have sq : ∀ x : ℂ, 8 * ((v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3) ^ 3 * x ^ 2) = 0 → x = 0 := by
    intro x hx
    have hx' := (mul_eq_zero.mp hx).resolve_left (by norm_num)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ((mul_eq_zero.mp hx').resolve_left hg3)
  have hP := sq _ (F1_vprod v w h1 h2 h3 h4 h5 hq)
  rcases mul_eq_zero.mp hP with h | e3
  · rcases mul_eq_zero.mp h with h | e2
    · rcases mul_eq_zero.mp h with e0 | e1
      · exact ⟨0, e0, sq _ (F1_w0 v w h1 h2 h3 h4 h5 hq e0)⟩
      · exact ⟨1, e1, sq _ (F1_w1 v w h1 h2 h3 h4 h5 hq e1)⟩
    · exact ⟨2, e2, sq _ (F1_w2 v w h1 h2 h3 h4 h5 hq e2)⟩
  · exact ⟨3, e3, sq _ (F1_w3 v w h1 h2 h3 h4 h5 hq e3)⟩''')
open('../lean/fl/p5i.part','w').write('\n'.join(out)+'\n')
print('ok', sum(len(o) for o in out))
