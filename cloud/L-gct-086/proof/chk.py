import numpy as np, itertools, math
rng=np.random.default_rng(1)
def Pks(t):
    # P_k(t) via perm(J+x t) at n+1 points (Ryser), returns P_1..P_n
    n=t.shape[0]
    def perm(A):
        n=A.shape[0]; s=0
        for mask in range(1,1<<n):
            cols=[j for j in range(n) if mask>>j&1]
            s+=(-1)**len(cols)*np.prod(A[:,cols].sum(1))
        return s*(-1)**n
    xs=np.arange(n+1)*0.5+0.3
    vals=[perm(np.ones((n,n))+x*t) for x in xs]
    V=np.vander(xs,n+1,increasing=True)
    c=np.linalg.solve(V,np.array(vals))
    return np.array([c[k]/math.factorial(n-k) for k in range(n+1)])[1:]
def cent(m):
    return m-m.mean(0,keepdims=True)-m.mean(1,keepdims=True)+m.mean()
n=5
# check P2,P3,P4 formulas on DC t
t=cent(rng.normal(size=(n,n))+1j*rng.normal(size=(n,n)))
P=Pks(t)
p=lambda k:(t**k).sum()
r=(t**2).sum(1); c=(t**2).sum(0)
print("P2",P[1],p(2)/2," P3",P[2],2/3*p(3))
P4=1.5*p(4)-0.75*((r**2).sum()+(c**2).sum())+p(2)**2/8+0.25*np.trace((t@t.T)@(t@t.T))
print("P4",P[3],P4)
# u (x) W example: u = n-th roots of unity, w with sum 0 and w_n=0 -> DC level space dim n-2
def level_check(basis,trials=3):
    mx=0
    for _ in range(trials):
        x=rng.normal(size=len(basis))+1j*rng.normal(size=len(basis))
        t=sum(a*b for a,b in zip(x,basis))
        mx=max(mx,np.abs(Pks(t)).max()/np.abs(t).max()**2)
    return mx
u=np.exp(2j*np.pi*np.arange(n)/n)
W=[np.eye(n)[j]-np.eye(n)[j+1] for j in range(n-2)]  # sum 0, last entry 0
B=[np.outer(u,w) for w in W]
print("u(x)W level?",level_check(B), "DC?",max(np.abs(cent(b)-b).max() for b in B))
B2=B+[np.outer(w,u) for w in W]
print("u(x)W + W(x)u level?",level_check(B2))
B3=B+[np.outer(w,u.conj()) for w in W]
print("u(x)W + W(x)ubar level?",level_check(B3))
