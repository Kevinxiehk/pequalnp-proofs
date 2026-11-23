# verify2: EXACT structured counterexample search for N3'.
# Family: V_0 spanned by 4 independent elements among  E_c  (9 cells)  and  E_c +- E_c'  (c, c' in a common row or column) : 45 elements.
# perm(b + eta) = perm(b) on V_0  <=>  (i) tau(v,v',v'') = 0 on V_0  (ii) tau(b,v,v') = 0  (iii) tau(b,b,v) = 0,  tau = polarised perm_3.
# b matters only modulo V_0;  W := {b : (ii)} / V_0.  N3' says: the common zeros of the 4 quadrics (iii) on W lie in {perm(b) = 0}.
import itertools, numpy as np, sys, pickle, time
from fractions import Fraction as Fr
t0=time.time()
cells=[(i,j) for i in range(3) for j in range(3)]
els=[]
for c in range(9):
    v=np.zeros(9,dtype=np.int64); v[c]=1; els.append(v)
for a in range(9):
    for b in range(a+1,9):
        if cells[a][0]==cells[b][0] or cells[a][1]==cells[b][1]:
            for sg in (1,-1):
                v=np.zeros(9,dtype=np.int64); v[a]=1; v[b]=sg; els.append(v)
els=np.array(els); ne=len(els)
P3=list(itertools.permutations(range(3)))
def perm3(A):   # A[...,9]
    a=A.reshape(A.shape[:-1]+(3,3))
    return (a[...,0,0]*(a[...,1,1]*a[...,2,2]+a[...,1,2]*a[...,2,1])+a[...,0,1]*(a[...,1,0]*a[...,2,2]+a[...,1,2]*a[...,2,0])
           +a[...,0,2]*(a[...,1,0]*a[...,2,1]+a[...,1,1]*a[...,2,0]))
combos=np.array(list(itertools.combinations(range(ne),4)))
# (i): perm = 0 on V_0: test at integer points (cubic in 4 variables, degree <= 3 in each: grid {0,1,2,3}^4 minus trivial = exact criterion)
grid=np.array(list(itertools.product(range(4),repeat=4)),dtype=np.int64)   # 256 points determine a polynomial of degree <= 3 in each variable
ok=np.ones(len(combos),bool)
for start in range(0,len(combos),20000):
    V=els[combos[start:start+20000]]                # (m,4,9)
    pts=np.einsum('gk,mkc->mgc',grid,V)             # (m,256,9)
    ok[start:start+20000]=np.all(perm3(pts)==0,axis=1)
surv=combos[ok]
# independence
rk=np.array([np.linalg.matrix_rank(els[c].astype(float)) for c in surv])
surv=surv[rk==4]
print('elements',ne,' 4-subsets',len(combos),' with perm = 0 on the span and dim 4:',len(surv),' (%.0fs)'%(time.time()-t0))
# distinct spans
def rref_key(M):
    M=[[Fr(int(x)) for x in r] for r in M]; r=0
    for c in range(9):
        p=None
        for i in range(r,len(M)):
            if M[i][c]!=0: p=i; break
        if p is None: continue
        M[r],M[p]=M[p],M[r]; pv=M[r][c]; M[r]=[x/pv for x in M[r]]
        for i in range(len(M)):
            if i!=r and M[i][c]!=0:
                f=M[i][c]; M[i]=[x-f*y for x,y in zip(M[i],M[r])]
        r+=1
        if r==len(M): break
    return tuple(tuple(row) for row in M[:r])
spans={}
for c in surv:
    k=rref_key(els[c]); spans.setdefault(k,c)
print('distinct 4-dim spans V_0 inside {perm = 0}:',len(spans),' (%.0fs)'%(time.time()-t0))
pickle.dump([els[c] for c in spans.values()],open('/home/claude/work/L-gct-210/verify2/n3p_spans.pkl','wb'))
