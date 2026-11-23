import sys; sys.path.insert(0,"/home/claude/work/L-gct-210/stage3")
from s3lib import *
# algebraic sanity of the P_2 incompatibility table (random instances) and of Theorem S3-A's independence step
rng=np.random.default_rng(5)
def P2(t):
    return 0.5*(t.sum()**2-(t.sum(1)**2).sum()-(t.sum(0)**2).sum()+(t**2).sum())
def P2brute(t):
    s=0
    for i,k in itertools.combinations(R5,2):
        for j,l in itertools.combinations(R5,2): s+=t[i,j]*t[k,l]+t[i,l]*t[k,j]
    return s
t=rng.normal(size=(5,5))+1j*rng.normal(size=(5,5)); print('P2 formula check %.1e'%abs(P2(t)-P2brute(t)))
def pol(x,y): return P2(x+y)-P2(x)-P2(y)
def Btype(a,b,j,l):
    q=rng.normal()+1j*rng.normal(); r=(1+q)/(q-1)   # p=1: (q-1)(r-1)=2
    s=-q*r; x=np.zeros((5,5),complex); x[a,j]=1; x[a,l]=q; x[b,j]=r; x[b,l]=s
    assert abs(x.sum())<1e-12 and abs(x[a,j]*x[b,l]+x[a,l]*x[b,j])<1e-12 and abs(P2(x))<1e-12
    return x*(rng.normal()+1j*rng.normal())
def Dtype(a,b,j):
    x=np.zeros((5,5),complex); x[a,j]=1; x[b,j]=-1; return x
print('(1) D-D sharing a row, different columns: |P2 pol| =%.3f (must be !=0);  same column: %.1e'%(abs(pol(Dtype(0,1,2),Dtype(0,3,4))),abs(pol(Dtype(0,1,2),Dtype(0,3,2)))))
print('(3) B-B disjoint rows: T=T\' %.3f, |T cap T\'|=1 %.3f, disjoint %.1e'%(abs(pol(Btype(0,1,0,1),Btype(2,3,0,1))),abs(pol(Btype(0,1,0,1),Btype(2,3,1,2))),abs(pol(Btype(0,1,0,1),Btype(2,3,2,3)))))
print('(4) B-B sharing a row, disjoint column pairs: %.3f'%abs(pol(Btype(0,1,0,1),Btype(0,2,2,3))))
print('(5) D-B disjoint rows: %.1e %.1e'%(abs(pol(Dtype(0,1,0),Btype(2,3,0,1))),abs(pol(Dtype(0,1,4),Btype(2,3,0,1)))))
print('(6) D-B sharing a row: j in T %.3f, j not in T %.3f'%(abs(pol(Dtype(0,1,0),Btype(0,2,0,1))),abs(pol(Dtype(0,1,4),Btype(0,2,0,1)))))
# independence: ten B-type elements on principal blocks [ab;ab]
X=np.array([Btype(a,b,a,b).reshape(-1) for a,b in PAIRS]); print('rank of ten principal-block B-type elements:',rank(X))
