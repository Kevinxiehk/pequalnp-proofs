"""exact check in Z[x]/Phi_N for small N (generic). usage as module."""
import itertools
def cyclotomic(N):
    # integer coefficients of Phi_N via polynomial division of x^N - 1
    from functools import reduce
    def polymul(a,b):
        r=[0]*(len(a)+len(b)-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b): r[i+j]+=x*y
        return r
    def polydiv(a,b):
        a=a[:]; q=[0]*(len(a)-len(b)+1)
        for i in range(len(a)-len(b),-1,-1):
            c=a[i+len(b)-1]//b[-1]; q[i]=c
            for j,y in enumerate(b): a[i+j]-=c*y
        return q
    P={}
    for d in range(1,N+1):
        if N%d: continue
        num=[-1]+[0]*(d-1)+[1]; den=[1]
        for e in P:
            if d%e==0: den=polymul(den,P[e])
        P[d]=polydiv(num,den)
    return P[N]
class Ring:
    def __init__(s,N): s.N=N; s.phi=cyclotomic(N); s.deg=len(s.phi)-1
    def red(s,c):
        c=list(c)
        while len(c)>s.deg:
            top=c.pop()
            if top:
                for i in range(s.deg): c[len(c)-s.deg+i]-=top*s.phi[i]
        return tuple(c+[0]*(s.deg-len(c)))
    def x(s,k): k%=s.N; v=[0]*(k+1); v[k]=1; return s.red(v)
    def add(s,a,b): return tuple(p+q for p,q in zip(a,b))
    def mul(s,a,b):
        r=[0]*(2*s.deg)
        for i,p in enumerate(a):
            if p:
                for j,q in enumerate(b):
                    if q: r[i+j]+=p*q
        return s.red(r)
    def zero(s): return tuple([0]*s.deg)
    def one(s): return s.red([1])
    def scal(s,a,k): return tuple(k*p for p in a)
def Pk(R,T,k):
    n=len(T); tot=R.zero()
    for rows in itertools.combinations(range(n),k):
        for cols in itertools.permutations(range(n),k):
            t=R.one()
            for i,c in zip(rows,cols):
                t=R.mul(t,T[i][c])
                if not any(t): break
            tot=R.add(tot,t)
    return tot
def comps(k,d):
    if d==1: yield (k,); return
    for i in range(k+1):
        for r in comps(k-i,d-1): yield (i,)+r
def check_level(R,basis):
    n=len(basis[0]); d=len(basis); out=[]
    for k in range(1,n+1):
        nb=0
        for a in comps(k,d):
            T=[[R.zero() for _ in range(n)] for _ in range(n)]
            for i in range(d):
                for r in range(n):
                    for c in range(n): T[r][c]=R.add(T[r][c],R.scal(basis[i][r][c],a[i]))
            if any(Pk(R,T,k)): nb+=1
        out.append((k,nb))
    return out
if __name__=='__main__':
    R=Ring(12)  # zeta12 = x ; i = x^3 ; z3 = x^4
    z3=lambda k:R.x(4*k); i4=lambda k:R.x(3*k); Z=R.zero(); O=R.one()
    u=[O,z3(2),z3(1),Z]; ub=[O,z3(1),z3(2),Z]
    chi=lambda k:[i4(k*j) for j in range(4)]
    B=[[[R.mul(u[r],chi(2)[c]) for c in range(4)] for r in range(4)],
       [[R.mul(ub[r],chi(1)[c]) for c in range(4)] for r in range(4)],
       [[R.mul(ub[r],chi(3)[c]) for c in range(4)] for r in range(4)]]
    rs=all(not any(R.add(R.add(b[r][0],b[r][1]),R.add(b[r][2],b[r][3]))) for b in B for r in range(4))
    cs=all(not any(R.add(R.add(b[0][c],b[1][c]),R.add(b[2][c],b[3][c]))) for b in B for c in range(4))
    print('n=4 example: DC',rs,cs,' P_k nonzero counts:',check_level(R,B))
    # sanity: a non-level variant
    B2=[[[R.mul(u[r],chi(1)[c]) for c in range(4)] for r in range(4)],[[R.mul(ub[r],chi(3)[c]) for c in range(4)] for r in range(4)]]
    print('sanity (u x chi1 + ub x chi3, expect P2 fail):',check_level(R,B2))
