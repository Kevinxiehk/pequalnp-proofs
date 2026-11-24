# Round 9: sanity checks of the moment classification of the twisted free column N of F4b (types C1, C3).
import numpy as np, itertools
rg=np.random.default_rng(5)
P5=np.array(list(itertools.permutations(range(5))))
def perm5(X): return X[np.arange(5)[None,:],P5].prod(axis=1).sum()
def perm(A):
    n=A.shape[0]
    if n==0: return 1.0
    P=np.array(list(itertools.permutations(range(n)))); return A[np.arange(n)[None,:],P].prod(axis=1).sum()
def prodA(vecs):   # product of vectors in the squarefree algebra: dict subset -> coeff
    k=len(vecs); return {S:perm(np.array([[v[j] for j in S] for v in vecs])) for S in itertools.combinations(range(5),k)}
def maxabs(d): return max(abs(x) for x in d.values())
def Nspace(y,p,w):
    B=[]
    for r in range(4):
        M=np.zeros((5,5),complex); M[r]=y[r]; M[4]=p; B.append(M)
    M=np.zeros((5,5),complex); M[4]=w; B.append(M); return np.array(B)
def levelerr(B,n=40):
    return max(abs(perm5(np.ones((5,5))+np.tensordot(rg.normal(size=len(B))+1j*rg.normal(size=len(B)),B,1))-120) for _ in range(n))
def checks(y,p,w,name):
    B=Nspace(y,p,w); e=levelerr(B)
    Y4=maxabs(prodA(list(y)))
    YU=max(maxabs(prodA([y[i] for i in T]+[u])) for T in itertools.combinations(range(4),3) for u in (w,p))
    # the formula perm(Y without column k) = 24 e4(v_k) - 6 s e3(v_k)
    s=y[0].sum(); f=0
    for k in range(5):
        v=y[:,k]; e3=sum(np.prod(v[list(T)]) for T in itertools.combinations(range(4),3)); e4=np.prod(v)
        f=max(f,abs(perm(np.delete(y,k,axis=1))-(24*e4-6*s*e3)))
    print('%-28s N-level err %.1e | Y_aY_bY_cY_d %.1e | y_T.{w,p} %.1e | formula err %.1e'%(name,e,Y4,YU,f))
e=np.eye(5)
# C3: k0=0, k1=1, k2=2, thin j=3, l=4; rows a (=0) and r1
for r1 in (1,2):
    c,yy=rg.normal()+1j*rg.normal(),rg.normal()+1j*rg.normal()
    y=np.array([e[0]]*4,complex); y[0]=e[0]-c*(e[1]+e[2])+c*(e[3]+e[4]); y[r1]=e[0]+yy*(e[1]-e[2])
    checks(y,-e[0]+0.7*(e[3]-e[4]),e[3]-e[4],'C3 r1=%d'%r1)
# C1-1: u_a with full support on columns 1..4, p' and w orthogonal to u_a and 1
u=rg.normal(size=4)+1j*rg.normal(size=4); u-=u.mean(); ua=np.concatenate([[0],u])
A=np.array([np.concatenate([[0],np.ones(4)]),ua]); 
ns=np.linalg.svd(np.concatenate([A,[[1,0,0,0,0]]]))[2][3:].conj()      # vectors with entry0 = 0, sum 0, <.,u_a> = 0 (bilinear)
pp=ns[0]; w=ns[1]
y=np.array([e[0]]*4,complex); y[0]=e[0]+ua
checks(y,-e[0]+pp,w,'C1-1 (u_a full support)')
# C1-2: u_a = al(e1-e2), u_c = be(e3-e4)
y=np.array([e[0]]*4,complex); y[0]=e[0]+1.3*(e[1]-e[2]); y[2]=e[0]-0.4j*(e[3]-e[4])
checks(y,-e[0],e[1]+e[2]-e[3]-e[4],'C1-2 (a,c)')
# negative control: C3 with a wrong p
y=np.array([e[0]]*4,complex); y[0]=e[0]-0.5*(e[1]+e[2])+0.5*(e[3]+e[4]); y[1]=e[0]+0.3*(e[1]-e[2])
checks(y,-e[0]+0.2*e[1]-0.2*e[2],e[3]-e[4],'control (wrong p)')
