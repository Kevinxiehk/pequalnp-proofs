import sympy as sp, re
x3,x4,x5,y3,y4,y5=sp.symbols('x3 x4 x5 y3 y4 y5')
loc={str(s):s for s in (x3,x4,x5,y3,y4,y5)}
def C(a,b,c): return (a+b)*(b+c)*(c+a)-a*b*c
gens=[C(x3,x4,x5),C(y3,y4,y5),C(x3+y3,x4+y4,x5+y5),C(x3-y3,x4-y4,x5-y5)]
names=['h1','h2','h3','h4']
def rd(fn):
    txt=open(fn).read().replace('\n','')
    return [sp.expand(sp.sympify(p.replace('^','**'),locals=loc)) for p in txt.split(';') if p.strip()]
def L(e): return sp.sstr(sp.expand(e)).replace('**','^')
mins={'34':x3*y4-x4*y3,'35':x3*y5-x5*y3,'45':x4*y5-x5*y4}
out=['''
set_option maxRecDepth 20000 in
theorem noline (x3 x4 x5 y3 y4 y5 : ℂ)
    (h1 : (x3 + x4) * (x4 + x5) * (x5 + x3) - x3 * x4 * x5 = 0)
    (h2 : (y3 + y4) * (y4 + y5) * (y5 + y3) - y3 * y4 * y5 = 0)
    (h3 : (x3 + y3 + (x4 + y4)) * (x4 + y4 + (x5 + y5)) * (x5 + y5 + (x3 + y3))
      - (x3 + y3) * (x4 + y4) * (x5 + y5) = 0)
    (h4 : (x3 - y3 + (x4 - y4)) * (x4 - y4 + (x5 - y5)) * (x5 - y5 + (x3 - y3))
      - (x3 - y3) * (x4 - y4) * (x5 - y5) = 0) :
    x3 * y4 - x4 * y3 = 0 ∧ x3 * y5 - x5 * y3 = 0 ∧ x4 * y5 - x5 * y4 = 0 := by''']
for k in ('34','35','45'):
    T=rd(f'sing13/z_{k}.txt')
    assert sp.expand(sum(t*g for t,g in zip(T,gens))-4*mins[k]**4)==0
    comb=' + '.join(f'({L(t)}) * {n}' for t,n in zip(T,names) if t!=0)
    out.append(f'  have e{k} : 4 * ({L(mins[k])}) ^ 4 = 0 := by\n    linear_combination {comb}')
out.append('''  have q : ∀ m : ℂ, 4 * m ^ 4 = 0 → m = 0 := by
    intro m hm
    have h := (mul_eq_zero.mp hm).resolve_left (by norm_num)
    exact pow_eq_zero_iff (n := 4) (by norm_num) |>.mp h
  refine ⟨?_, ?_, ?_⟩
  · have := q _ e34
    linear_combination this
  · have := q _ e35
    linear_combination this
  · have := q _ e45
    linear_combination this''')
open('../lean/fl/p5o.part','w').write('\n'.join(out)+'\n')
print('ok')
