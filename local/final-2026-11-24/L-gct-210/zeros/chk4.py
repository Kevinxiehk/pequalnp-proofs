import numpy as np, sys
sys.path.insert(0,'/home/kevxhk/work/L-gct-086/smallcases'); import level
I=1j; chi=lambda a: np.array([I**(a*j) for j in range(4)])
def v(t): return chi(1)+t*chi(2)-t*t/2*chi(3)
rng=np.random.default_rng(3); th=rng.normal(size=5)+1j*rng.normal(size=5)
V=np.column_stack([v(t) for t in th])
om=np.array([np.prod([th[m]-th[a] for a in range(5) if a!=m]) for m in range(5)])
al,be=rng.normal(size=2)+1j*rng.normal(size=2); l=(al+be*th)/om
print('kernel check',abs(V@l).max())
Z=V*l[None,:]
A=(l**2*(1+th**4/4)).sum(); B=(l**2*th).sum(); C=(l**2*th**3).sum()
E3=(l**3*3*th*(4+th**4)).sum()
err=0
for m in range(5):
    P=level.Pk(np.delete(Z,m,axis=1))[0]
    pred=(2/3)*E3+l[m]*(8*B+4*th[m]*A+2*th[m]**2*C)-6*l[m]**3*th[m]*(4+th[m]**4)
    err=max(err,abs(P[3]-pred),abs(P[1]),abs(P[2]))
print('P3 deletion formula err',err)
# identity G(theta)=p^2 g^2 consequences: check the alpha*beta coefficient computation of A under 1/om^2 = p^2/(3 th (4+th^4))
print('sum over 5 pts of 2*th/th =',10,' -> coefficient (p^2/12)*10 = 5/6 p^2 != p^2')
# type IV g=4 polynomial f1 and type II pairs
for (a,b) in [(2,-2),(-2j,2),(-2,-2),(2j,2)]:
    r=np.roots([1,-a,b]); z=[np.round(v(x),6) for x in r]
    c=lambda t,u: 2*u+t+t*u**4/4+t*t*u**3/2
    print((a,b),'zero rows',[int(np.argmin(abs(x))) for x in z],'min|entry|',[float(np.round(abs(x).min(),9)) for x in z],'c,c',abs(c(r[0],r[1])),abs(c(r[1],r[0])))
