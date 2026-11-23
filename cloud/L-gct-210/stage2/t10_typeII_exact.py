# EXACT (Gaussian rationals) full cube test for ALL all-Type-II (2,2,2) triples: certificate = two points v1,v2 of Pi_S with
# ell != 0 and perm(v1) ell(v2)^3 != perm(v2) ell(v1)^3   (so perm_3 is not k ell^3 on Pi_S although ell != 0 there).
import sys, itertools
from fractions import Fraction as Fr
class G:
    __slots__=('a','b')
    def __init__(s,a=0,b=0): s.a=Fr(a); s.b=Fr(b)
    def __add__(s,o): o=o if isinstance(o,G) else G(o); return G(s.a+o.a,s.b+o.b)
    __radd__=__add__
    def __sub__(s,o): o=o if isinstance(o,G) else G(o); return G(s.a-o.a,s.b-o.b)
    def __rsub__(s,o): return G(o)-s
    def __neg__(s): return G(-s.a,-s.b)
    def __mul__(s,o): o=o if isinstance(o,G) else G(o); return G(s.a*o.a-s.b*o.b,s.a*o.b+s.b*o.a)
    __rmul__=__mul__
    def inv(s): d=s.a*s.a+s.b*s.b; return G(s.a/d,-s.b/d)
    def __truediv__(s,o): o=o if isinstance(o,G) else G(o); return s*o.inv()
    def iszero(s): return s.a==0 and s.b==0
    def __repr__(s): return '(%s+%si)'%(s.a,s.b)
Z=G(0); ONE=G(1); I=G(0,1)
def nullspace(M,nc):
    M=[[x if isinstance(x,G) else G(x) for x in r] for r in M]; piv=[]; r=0
    for c in range(nc):
        p=None
        for i in range(r,len(M)):
            if not M[i][c].iszero(): p=i; break
        if p is None: continue
        M[r],M[p]=M[p],M[r]; pv=M[r][c].inv(); M[r]=[x*pv for x in M[r]]
        for i in range(len(M)):
            if i!=r and not M[i][c].iszero():
                f=M[i][c]; M[i]=[x-f*y for x,y in zip(M[i],M[r])]
        piv.append(c); r+=1
        if r==len(M): break
    free=[c for c in range(nc) if c not in piv]; ns=[]
    for f in free:
        v=[Z]*nc; v[f]=ONE
        for i,c in enumerate(piv): v[c]=-M[i][f]
        ns.append(v)
    return ns,len(piv)
def perm3(A):
    s=Z
    for p in itertools.permutations(range(3)): s=s+A[0][p[0]]*A[1][p[1]]*A[2][p[2]]
    return s
def typeII(cells,eps):
    w=[(I*eps) if q==0 else (ONE if q==1 else G(-1)) for q in cells]
    return w,[1 if q==2 else 0 for q in cells],[1 if q==1 else 0 for q in cells],G(Fr(-1,2),Fr(eps,2))
def expo(cells,eps): return [(1 if eps==1 else 3) if q==0 else (0 if q==1 else 2) for q in cells]
def opts23(r):
    vals=sorted(set(r)); res=[]
    if len(vals)!=3: return res
    for b in vals:
        if (b+2)%4 in vals:
            a=[v for v in vals if v!=b and v!=(b+2)%4][0]; eps=1 if (a-b)%4==1 else -1
            res.append((tuple(0 if x==a else (1 if x==b else 2) for x in r),eps))
    return res
def test(s12,s13,s23):
    w2,A1,A2,y12=typeII(*s12); w3,B1,B3,y13=typeII(*s13); w23,C2,C3,y23=typeII(*s23)
    def F(rows):
        v=[Z]*15
        for i,vec in rows:
            for j in range(5): v[5*i+j]=vec[j] if isinstance(vec[j],G) else G(vec[j])
        return v
    one=[1]*5
    N=[F([(0,one),(1,[-1]*5)]),F([(0,one),(2,[-1]*5)]),F([(0,[G(A1[j])+y12 for j in range(5)]),(1,A2)]),
       F([(0,[G(B1[j])+y13 for j in range(5)]),(2,B3)]),F([(1,[G(C2[j])+y23 for j in range(5)]),(2,C3)])]
    u=[[ONE]*5,[x.inv() for x in w2],[x.inv() for x in w3]]
    for S in itertools.combinations(range(5),3):
        Sc=[c for c in range(5) if c not in S]
        rows=N+[[ONE if k==5*i+c else Z for k in range(15)] for i in range(3) for c in Sc]
        ns,rk=nullspace(rows,15)
        pts=[]
        cands=ns+[[x+y for x,y in zip(ns[a],ns[b])] for a in range(len(ns)) for b in range(a+1,len(ns))]+[[x+2*y for x,y in zip(ns[a],ns[b])] for a in range(len(ns)) for b in range(len(ns)) if a!=b]
        for v in cands:
            ell=Z
            for j in range(5): ell=ell+v[j]
            if ell.iszero(): continue
            A=[[v[5*i+j]*u[i][j] for j in S] for i in range(3)]
            pts.append((perm3(A),ell*ell*ell))
        for (p1,e1) in pts:
            for (p2,e2) in pts:
                if not (p1*e2-p2*e1).iszero(): return S
    return None
canon=[]
for comp in ((1,1,3),(1,3,1),(3,1,1),(1,2,2),(2,1,2),(2,2,1)):
    canon.append((tuple([0]*comp[0]+[1]*comp[1]+[2]*comp[2]),1))
structs=[(cells,eps) for cells in itertools.product(range(3),repeat=5) if len(set(cells))==3 for eps in (1,-1)]
tot=0; killed=0; surv=[]
for s12 in canon:
    e2=expo(*s12)
    for s13 in structs:
        e3=expo(*s13); r=[(e3[j]-e2[j])%4 for j in range(5)]
        for s23 in opts23(r):
            tot+=1
            if test(s12,s13,s23) is not None: killed+=1
            else: surv.append((s12,s13,s23))
print('all-Type-II triples (exact, Gaussian rationals):',tot,' killed by a non-cube certificate:',killed,' survivors:',len(surv))
for s in surv: print('  ',s)
