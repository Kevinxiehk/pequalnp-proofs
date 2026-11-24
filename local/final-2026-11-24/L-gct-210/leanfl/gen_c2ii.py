import sympy as sp, re
v=list(sp.symbols('v0:4')); w=list(sp.symbols('w0:4')); c,g=sp.symbols('c g')
e=list(sp.symbols('e0:4'))
R=sp.Rational
def L(x):
    s=sp.sstr(sp.expand(x)).replace('**','^')
    s=re.sub(r'\bv(\d)\b',r'v \1',s); s=re.sub(r'\bw(\d)\b',r'w \1',s)
    s=re.sub(r'(?<![A-Za-z_])g(?![A-Za-z_0-9])','ip v w',s); return s
l3,l4,b=3*c/2,-c/2,1
y2=[l3*x for x in v]; y3=[l4*x for x in v]; y4=[b*x for x in w]
ip=lambda p,q:sum(x*y for x,y in zip(p,q)); t4=lambda p,q,r,s:sum(p[i]*q[i]*r[i]*s[i] for i in range(4))
Q=3*(t4(y2,y2,y3,y4)+t4(y3,y3,y2,y4)+t4(y4,y4,y2,y3))-(ip(y2,y3)*ip(y2,y4)+ip(y3,y2)*ip(y3,y4)+ip(y4,y2)*ip(y4,y3))
Q=sp.expand(Q)
target=R(3,16)*c**2*g**2
# express Q via yk = v_k w_k : substitute w_k = (g/4+e_k)/v_k (rational), simplify to polynomial
sub={w[k]:(g/4+e[k])/v[k] for k in range(4)}
P=sp.expand(sp.cancel(Q.subs(sub)))
P0=sp.expand(P.subs({x:0 for x in e}))
S=sum(x*x for x in v)
beta,rem=sp.div(sp.Poly(sp.expand(P0-target),*v),sp.Poly(S,*v))
assert rem.as_expr()==0, rem
beta=beta.as_expr()
# telescoping alphas
alphas=[]; prev=P0
cur={x:0 for x in e}
for k in range(4):
    cur[e[k]]=e[k]
    Pk=sp.expand(P.subs({x:cur[x] for x in e}))
    ak=sp.cancel((Pk-prev)/e[k]); alphas.append(sp.expand(ak)); prev=Pk
back={e[k]:v[k]*w[k]-g/4 for k in range(4)}
alphas=[sp.expand(a.subs(back)) for a in alphas]
# check
chk=sp.expand(Q-target-beta*S-sum(alphas[k]*(v[k]*w[k]-g/4) for k in range(4)))
print('check',chk)
cert=' + '.join(f'({L(alphas[k])}) * hchi {k}' for k in range(4))+f' + ({L(beta)}) * hv2'
open('c2ii.cert','w').write(cert)
print(len(cert))
