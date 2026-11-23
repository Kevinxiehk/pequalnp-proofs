# verify2 round 4: exact check of the four facts (s1)-(s4) used in stage2's Theorem FO-M* (R5-1), own code, rational arithmetic.
import itertools, random
from fractions import Fraction as Fr
def perm(M):
    n=len(M)
    if n==0: return Fr(1)
    if n==1: return M[0][0]
    return sum(M[0][j]*perm([r[:j]+r[j+1:] for r in M[1:]]) for j in range(n) if M[0][j]!=0)
def rref(rows):
    """rank and reduced rows (list of (pivot, row))"""
    rows=[r[:] for r in rows]; piv=[]; r=0; ncol=len(rows[0]) if rows else 0
    for c in range(ncol):
        p=next((i for i in range(r,len(rows)) if rows[i][c]!=0),None)
        if p is None: continue
        rows[r],rows[p]=rows[p],rows[r]; pv=rows[r][c]; rows[r]=[x/pv for x in rows[r]]
        for i in range(len(rows)):
            if i!=r and rows[i][c]!=0:
                f=rows[i][c]; rows[i]=[x-f*y for x,y in zip(rows[i],rows[r])]
        piv.append(c); r+=1
        if r==len(rows): break
    return r,piv,rows[:r]
def inspan(R,piv,v):
    v=v[:]
    for row,c in zip(R,piv):
        if v[c]!=0:
            f=v[c]; v=[x-f*y for x,y in zip(v,row)]
    return all(x==0 for x in v)
X={2:[1,0,0,-1],3:[1,-1,-1,1],4:[0,1,-1,0]}       # rows c,d,e = 2,3,4 on columns 1..4
def Nmat(a):                                       # a = dict row -> value
    return [[Fr(1)+(a[i]*X[i][j] if i in X else 0) for j in range(4)] for i in range(5)]
# (s1)
ok=True; rnd=random.Random(5)
for _ in range(20):
    a={i:Fr(rnd.randint(-9,9),rnd.randint(1,5)) for i in X}; N=Nmat(a)
    for i in range(5):
        if perm([N[k] for k in range(5) if k!=i])!=24: ok=False
print('(s1) all perm_4(N without row i) = 24 at 20 random rational a:',ok)
# coefficients of Q_k^{E_ij} as multilinear polynomials in (a_c,a_d,a_e): values on {0,1}^3 + Moebius inversion
subsets=[frozenset(s) for r in range(4) for s in itertools.combinations((2,3,4),r)]
def coeffs(i,j,k):
    val={}
    for S in subsets:
        N=Nmat({r:Fr(1 if r in S else 0) for r in X})
        val[S]=perm([[N[r][c] for c in range(4) if c!=j-1] for r in range(5) if r not in (i,k)])
    return {S:sum((-1)**(len(S)-len(T))*val[T] for T in subsets if T<=S) for S in subsets}
QC={(i,j,k):coeffs(i,j,k) for i in range(5) for j in range(1,5) for k in range(5) if i!=k}
def functional(k,S,with_tau):
    """linear functional on t (25 coordinates): coefficient of a^S in Q_k^t (+ (24/5) tau_0 if with_tau)"""
    v=[Fr(0)]*25
    for i in range(5):
        if i==k: continue
        for j in range(1,5): v[5*i+j]+=QC[(i,j,k)][S]
    if with_tau:
        for i in range(5): v[5*i]+=Fr(24,5)
    return v
# (s2)
print('(s2) Q_k does not involve a_k (k = c,d,e):',all(QC[(i,j,k)][S]==0 for (i,j,k) in QC for S in subsets if k in S))
E=frozenset()
cond_s3=[functional(k,S,S==E) for k in range(5) for S in subsets]
r3,p3,R3=rref(cond_s3); print('(s3) rank of the conditions "Q_k = -(24/5) tau_0 for all k":',r3,' => dim T_1(W_7) =',25-r3)
# W_7 and tau inside
def W7basis():
    B=[]
    for i in range(1,5):
        v=[Fr(0)]*25; v[0]=1; v[5*i]=-1; B.append(v)
    for i in X:
        v=[Fr(0)]*25
        for j in range(4): v[5*i+1+j]=Fr(X[i][j])
        B.append(v)
    return B
tau=[(Fr(1) if j==0 else Fr(0))-Fr(1,5) for i in range(5) for j in range(5)]
B8=W7basis()+[tau]
print('     W_7 + C tau has dim',rref(B8)[0],'and satisfies all conditions:',all(sum(x*y for x,y in zip(c,v))==0 for c in cond_s3 for v in B8))
# direct T_1(W_7) from cofactors at random rational points of W_7 (independent of the Q_k formulation)
def cofvec(U): return [perm([[U[r][c] for c in range(5) if c!=j] for r in range(5) if r!=i]) for i in range(5) for j in range(5)]
rows=[]
for _ in range(40):
    co=[Fr(rnd.randint(-5,5)) for _ in range(7)]; B=W7basis()
    U=[[Fr(1)+sum(co[m]*B[m][5*i+j] for m in range(7)) for j in range(5)] for i in range(5)]
    rows.append(cofvec(U))
print('     direct: dim T_1(W_7) from 40 cofactor vectors =',25-rref(rows)[0])
# (s4)
cond_T=[functional(k,S,S==E) for k in (2,3,4) for S in subsets]+[functional(k,S,S==E) for k in (0,1) for S in subsets if len(S)!=1]
rT,pT,RT=rref(cond_T); print("(s4) dim T' =",25-rT)
for k in (0,1):
    for s in (2,3,4):
        f=functional(k,frozenset([s]),False)
        print('     linear coefficient of Q_%s at a_%s vanishes identically on T\':'%('ab'[k],'..cde'[s]),inspan(RT,pT,f))
