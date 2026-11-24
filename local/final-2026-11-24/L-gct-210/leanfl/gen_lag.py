import sympy as sp, re
v=sp.symbols('v0:4'); w=sp.symbols('w0:4'); u=sp.symbols('u0:4')
loc={}
for nm,s in (('v',v),('w',w),('u',u)):
    for i in range(4): loc[f'{nm}{i}']=s[i]
def rd(fn):
    txt=open(fn).read().replace('\n','')
    return [sp.expand(sp.sympify(p.replace('^','**'),locals=loc)) for p in txt.split(';') if p.strip()]
A=rd('sing12/s3_a.txt'); B=rd('sing12/s3_b.txt')
def gens(k0):
    g=[v[k0], w[k0], sum(v), sum(w), sum(x**2 for x in v), sum(x**2 for x in w),
       sum(v[i]*u[i] for i in range(4)), sum(w[i]*u[i] for i in range(4)), sum(u)]
    return g
names=['hvk','hwk','h1','h2','h3','h4','hu1','hu2','hu3']
def L(e):
    s=sp.sstr(sp.expand(e)).replace('**','^')
    for nm in 'vwu':
        s=re.sub(r'\b'+nm+r'(\d)\b',nm+r' \1',s)
    return s
G=sum(v[i]*w[i] for i in range(4))
out=[]
for k0 in range(4):
    others=[i for i in range(4) if i!=k0]
    a,b,c=others
    pi={3:k0,0:a,1:b,2:c}
    sub={}
    for i in range(4):
        sub[v[i]]=v[pi[i]]; sub[w[i]]=w[pi[i]]; sub[u[i]]=u[pi[i]]
    Ar=[sp.expand(t.xreplace(sub)) for t in A]; Br=[sp.expand(t.xreplace(sub)) for t in B]
    gk=gens(k0)
    assert sp.expand(sum(x*y for x,y in zip(Ar,gk))-G**2*(u[a]-u[b]))==0
    assert sp.expand(sum(x*y for x,y in zip(Br,gk))-G**2*(u[b]-u[c]))==0
    ca=' + '.join(f'({L(2*t)}) * {n}' for t,n in zip(Ar,names) if t!=0)
    cb=' + '.join(f'({L(2*t)}) * {n}' for t,n in zip(Br,names) if t!=0)
    out.append(f'''
theorem uconst_{k0} (v w u : V4) (hvk : v {k0} = 0) (hwk : w {k0} = 0) (h1 : tau v = 0) (h2 : tau w = 0)
    (h3 : ip v v = 0) (h4 : ip w w = 0) (hu1 : ip v u = 0) (hu2 : ip w u = 0) (hu3 : tau u = 0) :
    2 * ((v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3) ^ 2 * (u {a} - u {b})) = 0 ∧
      2 * ((v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3) ^ 2 * (u {b} - u {c})) = 0 := by
  simp only [tau, ip] at h1 h2 h3 h4 hu1 hu2 hu3
  refine ⟨?_, ?_⟩
  · linear_combination {ca}
  · linear_combination {cb}''')
open('../lean/fl/p5k.part','w').write('\n'.join(out)+'\n')
print('ok')
