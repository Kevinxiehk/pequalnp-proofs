# length of A/(D) = n - rank of multiplication-by-D, built by column recursion c_{t_v b'} = M_v c_{b'} from c_1 = NF(D).  mod p, exact.
import sys, numpy as np
pre=sys.argv[1]; P=int(sys.argv[2])
B=[tuple(int(x) for x in l.strip().split(',')) for l in open(pre+'.basis') if l.strip()]
n=len(B); idx={b:i for i,b in enumerate(B)}
def ev(s): return idx[tuple(int(x) for x in s.split(','))]
d=np.zeros(n,dtype=np.int64)
for l in open(pre+'.det'):
    s=l.split()
    if s: d[ev(s[1])]=(d[ev(s[1])]+int(s[0]))%P
M=[np.zeros((n,n),dtype=np.int64) for _ in range(12)]
for l in open(pre+'.mm'):
    s=l.split()
    if s: M[int(s[0])-1][ev(s[3]),int(s[1])-1]=int(s[2])%P
# sanity: M_v must commute (A is commutative) -- check a few pairs
for a,b in [(0,1),(3,7),(5,11),(2,9)]:
    assert not ((M[a]@M[b]-M[b]@M[a])%P).any(), 'noncommuting multiplication matrices'
# columns of multiplication by D: column for basis monomial b = D*b
one=idx[tuple([0]*12)]
col={one:d.copy()}
order=sorted(range(n),key=lambda i:sum(B[i]))
for i in order:
    if i in col: continue
    b=B[i]; v=next(k for k in range(12) if b[k]>0); bp=list(b); bp[v]-=1; j=idx[tuple(bp)]
    col[i]=(M[v]@col[j])%P
A=np.array([col[i] for i in range(n)],dtype=np.int64).T
# check: multiplication by D commutes with M_v
for v in (0,6,11): assert not ((M[v]@A-A@M[v])%P).any()
r=0; A=A.copy()
for c in range(n):
    nz=np.nonzero(A[r:,c])[0]
    if len(nz)==0: continue
    piv=r+nz[0]; A[[r,piv]]=A[[piv,r]]
    A[r]=(A[r]*pow(int(A[r,c]),P-2,P))%P
    colv=A[:,c].copy(); colv[r]=0; nzz=np.nonzero(colv)[0]
    if len(nzz): A[nzz]=(A[nzz]-np.outer(colv[nzz],A[r]))%P
    r+=1
    if r==n: break
print('%s: n=%d nnz(NF det)=%d rank(mult by det)=%d  LENGTH of Y+det in chart = %d'%(pre,n,int((d!=0).sum()),r,n-r))
