import sympy as sp, pickle, re
v=sp.symbols('v0:4'); w=sp.symbols('w0:4'); g=sp.Symbol('g')
y=[v[k]*w[k] for k in range(4)]
def L(e):
    s=sp.sstr(sp.expand(e)) if not isinstance(e,str) else e
    s=s.replace('**','^')
    s=re.sub(r'\bv(\d)\b',r'v \1',s); s=re.sub(r'\bw(\d)\b',r'w \1',s)
    s=re.sub(r'(?<![A-Za-z_])g(?![A-Za-z_0-9])','ip v w',s)
    return s
def W(e):  # wrap
    return '('+L(e)+')'
# hypotheses as lhs-rhs
H={}
H['hs']=sum(y)-g; H['hv']=sum(v); H['hw']=sum(w)
H['sv']=sum(y[k]*v[k] for k in range(4)); H['sw']=sum(y[k]*w[k] for k in range(4))
def aeq(m): return y[m]-y[0]
def ane(m): return 6*(y[m]+y[0])-2*g
def check(goal,comb,extra):
    tot=sum(c*(extra[n] if n in extra else H[n]) for c,n in comb)
    r=sp.expand(goal-tot)
    assert r==0,(goal,comb,r)
def lc(comb):
    return ' + '.join(f'{W(c)} * {n}' for c,n in comb)
R=sp.Rational
out=[]
# E2 certificate lemma
cert=pickle.load(open('e2cert.pkl','rb'))
hn=['h1','h2','h3','h4','h5','h6']
out.append('''
theorem pair_E2 (v w : V4) (h1 : tau v = 0) (h2 : tau w = 0) (h3 : ip v v = 0) (h4 : ip w w = 0)
    (h5 : t3 v v w = 0) (h6 : t3 v w w = 0) (k : Fin 4) :
    6 * (v k * w k) ^ 2 - 2 * ip v w * (v k * w k) = 6 * (v 0 * w 0) ^ 2 - 2 * ip v w * (v 0 * w 0) := by
  simp only [tau, ip, t3] at h1 h2 h3 h4 h5 h6 ⊢
  fin_cases k
  · rfl''')
gs=sum(a*b for a,b in zip(v,w))
for k in (1,2,3):
    cs=cert[k]
    goal=f'6 * (v {k} * w {k}) ^ 2 - 2 * (v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3) * (v {k} * w {k}) = 6 * (v 0 * w 0) ^ 2 - 2 * (v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3) * (v 0 * w 0)'
    comb=' + '.join(f'({L(-c)}) * {hn[i]}' for i,c in enumerate(cs) if c!=0)
    out.append(f'  · show {goal}\n    linear_combination {comb}')
# pair_rel
out.append('''
theorem pair_rel (v w : V4) (h1 : tau v = 0) (h2 : tau w = 0) (h3 : ip v v = 0) (h4 : ip w w = 0)
    (h5 : t3 v v w = 0) (h6 : t3 v w w = 0) (hg : ip v w ≠ 0) :
    (∀ k, v k * w k = ip v w / 4) ∨
      (∃ k, v k = 0 ∧ w k = 0 ∧ ∀ m, m ≠ k → 3 * (v m * w m) = ip v w) := by
  have E := pair_E2 v w h1 h2 h3 h4 h5 h6
  have F1 : (v 1 * w 1 - v 0 * w 0) * (6 * (v 1 * w 1 + v 0 * w 0) - 2 * ip v w) = 0 := by
    linear_combination E 1
  have F2 : (v 2 * w 2 - v 0 * w 0) * (6 * (v 2 * w 2 + v 0 * w 0) - 2 * ip v w) = 0 := by
    linear_combination E 2
  have F3 : (v 3 * w 3 - v 0 * w 0) * (6 * (v 3 * w 3 + v 0 * w 0) - 2 * ip v w) = 0 := by
    linear_combination E 3
  have hs : v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3 = ip v w := rfl
  have hv : v 0 + v 1 + v 2 + v 3 = 0 := h1
  have hw : w 0 + w 1 + w 2 + w 3 = 0 := h2
  have sv : v 0 * w 0 * v 0 + v 1 * w 1 * v 1 + v 2 * w 2 * v 2 + v 3 * w 3 * v 3 = 0 := by
    have e : t3 v v w = 0 := h5
    simp only [t3] at e
    linear_combination e
  have sw : v 0 * w 0 * w 0 + v 1 * w 1 * w 1 + v 2 * w 2 * w 2 + v 3 * w 3 * w 3 = 0 := by
    have e : t3 v w w = 0 := h6
    simp only [t3] at e
    linear_combination e
  rcases mul_eq_zero.mp F1 with a1 | a1 <;> rcases mul_eq_zero.mp F2 with a2 | a2 <;>
    rcases mul_eq_zero.mp F3 with a3 | a3''')
import itertools
for pat in itertools.product([0,1],repeat=3):   # 0 = equal, 1 = other root; order matches rcases
    ex={f'a{m}':(aeq(m) if pat[m-1]==0 else ane(m)) for m in (1,2,3)}
    E=[m for m in (1,2,3) if pat[m-1]==0]; N=[m for m in (1,2,3) if pat[m-1]==1]
    if len(N)==0:
        goal=y[0]-g/4; comb=[(R(1,4),'hs')]+[(R(-1,4),f'a{m}') for m in E]; check(goal,comb,ex)
        s=f'  · left\n    have hy0 : v 0 * w 0 = ip v w / 4 := by\n      linear_combination {lc(comb)}\n    intro k\n    fin_cases k\n    · exact hy0'
        for m in (1,2,3):
            c2=[(1,f'a{m}'),(1,'hy0')]; ex2=dict(ex); ex2['hy0']=y[0]-g/4; check(y[m]-g/4,c2,ex2)
            s+=f'\n    · show v {m} * w {m} = ip v w / 4\n      linear_combination a{m} + hy0'
        out.append(s)
    elif len(N)==2:
        comb=[(3,f'a{E[0]}')]+[(R(1,2),f'a{m}') for m in N]+[(-3,'hs')]; check(g,comb,ex)
        out.append(f'  · exfalso\n    apply hg\n    linear_combination {lc(comb)}')
    else:
        if len(N)==1:
            j=N[0]
            c0=[(R(1,2),'hs')]+[(R(-1,2),f'a{m}') for m in E]+[(R(-1,12),f'a{j}')]
            check(y[0]-g/3,c0,ex); ex['hy0']=y[0]-g/3
            cj=[(R(1,6),f'a{j}'),(-1,'hy0')]; check(y[j],cj,ex); ex['hyj']=y[j]
            hy0s=f'v 0 * w 0 = ip v w / 3'
            tau_v=sum(v)-v[j]; tau_w=sum(w)-w[j]
            cv=[(-3,'sv'),(g,'hv'),(3*tau_v,'hy0')]+[(3*v[m],f'a{m}') for m in E]+[(3*v[j],'hyj')]
            cw=[(-3,'sw'),(g,'hw'),(3*tau_w,'hy0')]+[(3*w[m],f'a{m}') for m in E]+[(3*w[j],'hyj')]
        else:
            j=0
            c0=[(R(-1,2),'hs')]+[(R(1,12),f'a{m}') for m in N]
            check(y[0],c0,ex); ex['hy0']=y[0]; ex['hyj']=y[0]
            hy0s='v 0 * w 0 = 0'
            cv=[(-3,'sv'),(g,'hv'),(3*(v[0]-v[1]-v[2]-v[3]),'hy0')]+[(R(1,2)*v[m],f'a{m}') for m in N]
            cw=[(-3,'sw'),(g,'hw'),(3*(w[0]-w[1]-w[2]-w[3]),'hy0')]+[(R(1,2)*w[m],f'a{m}') for m in N]
        check(g*v[j],cv,ex); check(g*w[j],cw,ex)
        s=f'  · right\n    have hy0 : {hy0s} := by\n      linear_combination {lc(c0)}'
        if j!=0:
            s+=f'\n    have hyj : v {j} * w {j} = 0 := by\n      linear_combination {lc(cj)}'
        s+=f'\n    refine ⟨{j}, ?_, ?_, ?_⟩'
        s+=f'\n    · have e : ip v w * v {j} = 0 := by\n        linear_combination {lc(cv)}\n      exact (mul_eq_zero.mp e).resolve_left hg'
        s+=f'\n    · have e : ip v w * w {j} = 0 := by\n        linear_combination {lc(cw)}\n      exact (mul_eq_zero.mp e).resolve_left hg'
        s+='\n    · intro m hm\n      fin_cases m'
        for m in range(4):
            if m==j:
                s+='\n      · exact (hm rfl).elim'; continue
            if j!=0:
                cm=[(3,'hy0')] if m==0 else [(3,f'a{m}'),(3,'hy0')]
            else:
                cm=[(R(1,2),f'a{m}'),(-3,'hy0')]
            check(3*y[m]-g,cm,ex)
            s+=f'\n      · show 3 * (v {m} * w {m}) = ip v w\n        linear_combination {lc(cm)}'
        out.append(s)
open('/home/kevxhk/work/L-gct-210/lean/fl/p3a.part','w').write('\n'.join(out)+'\n')
print('ok')
