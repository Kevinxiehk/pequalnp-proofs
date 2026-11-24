import sympy as sp, itertools, re
k=sp.Symbol('kap'); v=sp.symbols('v0:4')
A=sp.symbols('a1 a2 b1 b2 c1 c2 d1 d2')
vecs=[(A[0],A[1]),(A[2],A[3]),(A[4],A[5]),(A[6],A[7])]
Qk=lambda m,i: m[0]*v[i]+m[1]*v[i]**2
def L(e):
    s=sp.sstr(sp.expand(e)).replace('**','^')
    return re.sub(r'\bv(\d)\b',r'v \1',s)
def reduce_cert(expr):
    # expr polynomial in v; reduce v_i^4 -> kap; return (quotients per i, remainder)
    qs=[]; rem=sp.expand(expr)
    for i in range(4):
        q,rem=sp.div(rem, v[i]**4-k, v[i]); qs.append(sp.expand(q))
    return qs, sp.expand(rem)
h1=sum(v); h2=sum(vi**2 for vi in v); h3=sum(vi**3 for vi in v)
def split_rem(rem):
    # rem = const + c1*h1 + c2*h2 + c3*h3 with c's polynomials in v of low degree (we expect rem to be sum_i f(v_i) for f with monomials v^1,v^2,v^3)
    const=sp.expand(rem.subs({vi:0 for vi in v}))
    r=sp.expand(rem-const)
    # each remaining monomial is coef * v_i^e with e in 1,2,3 and coef free of v (since terms are sum_i of univariate)
    c={1:0,2:0,3:0}
    P=sp.Poly(r,*v)
    for mon,co in P.terms():
        nz=[e for e in mon if e>0]
        assert len(nz)==1, mon
        c[nz[0]]+=0  # placeholder
    # coefficient of v0^e must equal coefficient of v_i^e for symmetry
    cs={}
    for e in (1,2,3):
        cs[e]=sp.expand(P.coeff_monomial(v[0]**e))
    chk=sp.expand(r-cs[1]*h1-cs[2]*h2-cs[3]*h3)
    assert chk==0
    return const,cs
# t4 for pc
x,y,z,w=vecs
t4e=sum(Qk(x,i)*Qk(y,i)*Qk(z,i)*Qk(w,i) for i in range(4))
qs,rem=reduce_cert(t4e); const,cs=split_rem(rem)
ip=lambda p,q: 4*k*(p[1]*q[1])
FORMpc=sp.expand(-6*const+ip(x,y)*ip(z,w)+ip(x,z)*ip(y,w)+ip(x,w)*ip(y,z))
comb=' + '.join(f'({L(6*q)}) * hk {i}' for i,q in enumerate(qs))
extra=' + '.join(f'({L(6*cs[e])}) * h{e}\'' for e in (1,2,3) if cs[e]!=0)
pc_txt=f'''
set_option maxRecDepth 20000 in
theorem pc_Qv12 (v : V4) (kap : ℂ) (hk : ∀ i, v i ^ 4 = kap) (h1 : tau v = 0) (h2 : ip v v = 0)
    (h3 : t3 v v v = 0) (a1 a2 b1 b2 c1 c2 d1 d2 : ℂ) :
    pc (Qv v 0 a1 a2 0) (Qv v 0 b1 b2 0) (Qv v 0 c1 c2 0) (Qv v 0 d1 d2 0) = {L(FORMpc)} := by
  rw [pc_full, tau_Qv v h1 h2 h3, tau_Qv v h1 h2 h3, tau_Qv v h1 h2 h3, tau_Qv v h1 h2 h3]
  simp only [br]
  rw [ip_Qv v kap hk h1 h2 h3, ip_Qv v kap hk h1 h2 h3, ip_Qv v kap hk h1 h2 h3,
    ip_Qv v kap hk h1 h2 h3, ip_Qv v kap hk h1 h2 h3, ip_Qv v kap hk h1 h2 h3]
  have h1' := h1
  have h2' := h2
  have h3' := h3
  simp only [tau, ip, t3] at h1' h2' h3'
  simp only [t4, Qv]
  linear_combination -({comb}){(' - (' + extra + ')') if extra else ''}
'''
# X3c: 2 * sum over triples t3 (taus vanish)
def t3e(p,q,r): return sum(Qk(p,i)*Qk(q,i)*Qk(r,i) for i in range(4))
trip=[(x,y,z),(x,y,w),(x,z,w),(y,z,w)]
X3e=sp.expand(2*sum(t3e(*t) for t in trip))
qs3,rem3=reduce_cert(X3e); const3,cs3=split_rem(rem3)
FORMx=const3
comb3=' + '.join(f'({L(q)}) * hk {i}' for i,q in enumerate(qs3) if q!=0)
extra3=' + '.join(f'({L(cs3[e])}) * h{e}\'' for e in (1,2,3) if cs3[e]!=0)
x3_txt=f'''
set_option maxRecDepth 20000 in
theorem x3c_Qv12 (v : V4) (kap : ℂ) (hk : ∀ i, v i ^ 4 = kap) (h1 : tau v = 0) (h2 : ip v v = 0)
    (h3 : t3 v v v = 0) (a1 a2 b1 b2 c1 c2 d1 d2 : ℂ) :
    X3c (Qv v 0 a1 a2 0) (Qv v 0 b1 b2 0) (Qv v 0 c1 c2 0) (Qv v 0 d1 d2 0) = {L(FORMx)} := by
  simp only [X3c]
  rw [tau_Qv v h1 h2 h3, tau_Qv v h1 h2 h3, tau_Qv v h1 h2 h3, tau_Qv v h1 h2 h3]
  have h1' := h1
  have h2' := h2
  have h3' := h3
  simp only [tau, ip, t3] at h1' h2' h3'
  simp only [ip, t3, Qv]
  linear_combination {comb3 if comb3 else '0'}{(' + ' + extra3) if extra3 else ''}
'''
open('../lean/fl/p5aa.part','w').write(pc_txt+x3_txt)
print('pc:',FORMpc); print('x3c:',FORMx)
