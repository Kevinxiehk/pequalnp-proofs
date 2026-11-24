"""Exact arithmetic in Z[x]/Phi_15(x); zeta15 = x, w5 = x^3, z3 = x^5."""
import itertools
PHI=[1,-1,0,1,-1,1,0,-1,1]  # Phi_15 coefficients low->high: 1 - x + x^3 - x^4 + x^5 - x^7 + x^8
class C:
    __slots__=('c',)
    def __init__(self,c):
        c=list(c)+[0]*(8-len(c)) if len(c)<8 else list(c)
        # reduce
        while len(c)>8:
            top=c.pop()
            if top:
                for i in range(8): c[len(c)-8+i]-=top*PHI[i]
        self.c=c
    @staticmethod
    def x(k):
        k%=15; v=[0]*(k+1); v[k]=1; return C(v)
    def __add__(s,o):
        o=o if isinstance(o,C) else C([o]); return C([a+b for a,b in zip(s.c,o.c)])
    __radd__=__add__
    def __neg__(s): return C([-a for a in s.c])
    def __sub__(s,o): return s+(-(o if isinstance(o,C) else C([o])))
    def __mul__(s,o):
        o=o if isinstance(o,C) else C([o]); r=[0]*15
        for i,a in enumerate(s.c):
            if a:
                for j,b in enumerate(o.c):
                    if b: r[i+j]+=a*b
        return C(r)
    __rmul__=__mul__
    def iszero(s): return all(a==0 for a in s.c)
    def __repr__(s): return 'C(%s)'%s.c
ZERO=C([0]); ONE=C([1])
def w5(k): return C.x(3*k)
def z3(k): return C.x(5*k)
def perm(M):
    n=len(M); tot=ZERO
    for p in itertools.permutations(range(n)):
        t=ONE
        for i in range(n):
            t=t*M[i][p[i]]
            if t.iszero(): break
        tot=tot+t
    return tot
def Pk(T,k):
    n=len(T); tot=ZERO
    for R in itertools.combinations(range(n),k):
        for Cc in itertools.combinations(range(n),k):
            tot=tot+perm([[T[i][j] for j in Cc] for i in R])
    return tot
def compositions(k,d):
    if d==1: yield (k,); return
    for i in range(k+1):
        for r in compositions(k-i,d-1): yield (i,)+r
def check_level(basis):
    """all P_k (k=1..n) vanish identically on span(basis): evaluate homogeneous P_k at all
    nonneg integer points with |a| = k (unisolvent for degree-k forms)."""
    n=len(basis[0]); d=len(basis); bad=[]
    for k in range(1,n+1):
        nb=0
        for a in compositions(k,d):
            T=[[sum((basis[i][r][c]*a[i] for i in range(d)),ZERO) for c in range(n)] for r in range(n)]
            if not Pk(T,k).iszero(): nb+=1
        bad.append((k,nb))
    return bad
if __name__=='__main__':
    u=[ONE,z3(2),z3(1),ZERO,ZERO]; ub=[ONE,z3(1),z3(2),ZERO,ZERO]
    chi=lambda k:[w5(k*j) for j in range(5)]
    B=[[[u[i]*chi(1)[j] for j in range(5)] for i in range(5)],
       [[u[i]*chi(4)[j] for j in range(5)] for i in range(5)],
       [[ub[i]*chi(2)[j] for j in range(5)] for i in range(5)],
       [[ub[i]*chi(3)[j] for j in range(5)] for i in range(5)]]
    # DC check
    print('row sums zero',all(sum(b[i],ZERO).iszero() for b in B for i in range(5)),
          'col sums zero',all(sum((b[i][j] for i in range(5)),ZERO).iszero() for b in B for j in range(5)))
    print('P_k nonzero evaluations per k:',check_level(B))
