import sympy as sp, itertools, re
k=sp.Symbol('kap'); v=sp.symbols('v0:4')
A=sp.symbols('a1 a3 b1 b3 c1 c3 d1 d3')
vecs=[(A[0],A[1]),(A[2],A[3]),(A[4],A[5]),(A[6],A[7])]
def ipc(x,y): return 4*k*(x[0]*y[1]+x[1]*y[0])
def t4c(*vs):
    tot=0
    for mask in itertools.product([0,1],repeat=4):
        j=sum(mask); term=1
        for vv,m in zip(vs,mask): term*=vv[m]
        tot+=term*{0:4*k,1:0,2:4*k**2,3:0,4:4*k**3}[j]
    return tot
x,y,z,w=vecs
FORM=sp.expand(-6*t4c(x,y,z,w)+ipc(x,y)*ipc(z,w)+ipc(x,z)*ipc(y,w)+ipc(x,w)*ipc(y,z))
# explicit: t4 = sum_k prod (m1 v_k + m3 v_k^3)
Qk=lambda m,i: m[0]*v[i]+m[1]*v[i]**3
t4e=sum(Qk(x,i)*Qk(y,i)*Qk(z,i)*Qk(w,i) for i in range(4))
# hk_i: v_i^4 - kap ; h2: sum v_i^2
# find q_i with prod - reduced = (v_i^4 - kap) q_i
cert_terms=[]; total=0
for i in range(4):
    P=sp.expand(Qk(x,i)*Qk(y,i)*Qk(z,i)*Qk(w,i))
    q,rem=sp.div(P, v[i]**4-k, v[i])
    cert_terms.append(sp.expand(q))
    total+=rem
# total should be 4kΠm1+... + (k*S1 + k^2*S3)*sum v^2
S2=sp.Symbol('S2')
# remainder as polynomial: separate sum v_i^2 part
h2=sum(vi**2 for vi in v)
rest=sp.expand(total)
c2=sp.expand(sp.cancel(sp.expand(rest - rest.subs({vi:0 for vi in v}))/1))
# rest = const + (coef)*h2 ? compute coef by dividing rest-const by h2
const=sp.expand(rest.subs({vi:0 for vi in v}))
qh,remh=sp.div(sp.expand(rest-const), h2, *v)
assert sp.expand(remh)==0
# identity: t4e = sum q_i (v_i^4-k) + qh*h2 + const ; and -6*const + ip-part == FORM
ippart=ipc(x,y)*ipc(z,w)+ipc(x,z)*ipc(y,w)+ipc(x,w)*ipc(y,z)
assert sp.expand(-6*const+ippart-FORM)==0
assert sp.expand(t4e - sum(q*(v[i]**4-k) for i,q in enumerate(cert_terms)) - qh*h2 - const)==0
def L(e):
    s=sp.sstr(sp.expand(e)).replace('**','^')
    s=re.sub(r'\bv(\d)\b',r'v \1',s)
    return s
comb=' + '.join(f'({L(6*q)}) * hk {i}' for i,q in enumerate(cert_terms))
txt=f'''
set_option maxRecDepth 20000 in
theorem pc_Qv13 (v : V4) (kap : ℂ) (hk : ∀ i, v i ^ 4 = kap) (h1 : tau v = 0) (h2 : ip v v = 0)
    (h3 : t3 v v v = 0) (a1 a3 b1 b3 c1 c3 d1 d3 : ℂ) :
    pc (Qv v 0 a1 0 a3) (Qv v 0 b1 0 b3) (Qv v 0 c1 0 c3) (Qv v 0 d1 0 d3) = {L(FORM)} := by
  rw [pc_full, tau_Qv v h1 h2 h3, tau_Qv v h1 h2 h3, tau_Qv v h1 h2 h3, tau_Qv v h1 h2 h3]
  simp only [br]
  rw [ip_Qv v kap hk h1 h2 h3, ip_Qv v kap hk h1 h2 h3, ip_Qv v kap hk h1 h2 h3,
    ip_Qv v kap hk h1 h2 h3, ip_Qv v kap hk h1 h2 h3, ip_Qv v kap hk h1 h2 h3]
  have h2' := h2
  simp only [ip] at h2'
  simp only [t4, Qv]
  linear_combination -({comb}) - ({L(6*qh)}) * h2'
'''
open('../lean/fl/p5x.part','w').write(txt)
print('ok', len(txt))
