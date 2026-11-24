# verify2 round 7: numerical sanity of the coefficient identities used in verifyfl R5.9 (Props I-ALL, II-ALL).
# (1) ID8 bracket formula; (2) ID11 t^2-coefficients of T_c(Y+tZ) for all three placements; (3) T_n, T_n' in the m_a=m_b sub-case.
import numpy as np, itertools
rng=np.random.default_rng(7)
w=np.exp(2j*np.pi/3); zeta=np.array([1,w,w*w,0]); zb=np.array([1,w*w,w,0]); h=np.array([1,1,1,-3.]); one3=np.array([1,1,1,0.])
chi=lambda a: np.array([1j**(a*k) for k in range(4)])
tau=lambda x: x.sum()
ip=lambda x,y: (x*y).sum()
def br(y1,y2,y3,y4): return -6*tau(y1*y2*y3*y4)+ip(y1,y2)*ip(y3,y4)+ip(y1,y3)*ip(y2,y4)+ip(y1,y4)*ip(y2,y3)
# (1) ID8
p=rng.normal(size=4)+1j*rng.normal(size=4); r=rng.normal(size=4)+1j*rng.normal(size=4)
ys=[p[i]*chi(1)+r[i]*chi(3) for i in range(4)]
rhs=-24*(np.prod(p)+np.prod(r))+8*sum(p[list(Q)].prod()*r[[k for k in range(4) if k not in Q]].prod() for Q in itertools.combinations(range(4),2))
print('ID8 err',abs(br(*ys)-rhs))
def T(Y,c):
    cols=[j for j in range(5) if j!=c]
    return sum(tau(Y[:,a]*Y[:,b]*Y[:,d]) for a,b,d in itertools.combinations(cols,3))
def t2coef(Y,Z,c):
    ts=np.array([0.,1.,-1.,2.]); vals=np.array([T(Y+t*Z,c) for t in ts])
    A=np.vander(ts,4,increasing=True); return np.linalg.solve(A,vals)[2]
def randV():
    x=rng.normal(size=4)+1j*rng.normal(size=4); return x-x.mean()
worst=0
for (i,j,k,l,o) in itertools.permutations(range(5)):
    Y=np.array([randV() for _ in range(5)]).T
    mu,mup=rng.normal(size=2)+1j*rng.normal(size=2)
    Z=np.zeros((4,5),complex); Z[:,i]=mu*zeta; Z[:,j]=-mu*zeta; Z[:,k]=mup*zb; Z[:,l]=-mup*zb
    y=lambda q: Y[:,q]
    f={o: -mu**2*ip(zb,y(k)+y(l))-mup**2*ip(zeta,y(i)+y(j)),
       i: mu*mup*ip(one3,y(k)-y(l))-mup**2*ip(zeta,y(j)+y(o)),
       j: -mu*mup*ip(one3,y(k)-y(l))-mup**2*ip(zeta,y(i)+y(o)),
       k: -mu**2*ip(zb,y(o)+y(l))+mu*mup*ip(one3,y(i)-y(j)),
       l: -mu**2*ip(zb,y(o)+y(k))-mu*mup*ip(one3,y(i)-y(j))}
    for c in range(5): worst=max(worst,abs(t2coef(Y,Z,c)-f[c]))
print('ID11 worst err over 120 placements',worst)
# (3) m_a=m_b sub-case: Y = zb l^T, l=(1/2,1/2,-1,x,1-x); columns (a,b,c,n,n')=(0,1,2,3,4)
for x in [0.3,-1/3,4/3,2+1j]:
    l=np.array([.5,.5,-1,x,1-x]); Y=np.outer(zb,l)
    print('x',x,'T_n',np.round(T(Y,3),12),'formula',-3/4-9/4*(1-x),'T_nprime',np.round(T(Y,4),12),'formula',-3/4-9/4*x)
