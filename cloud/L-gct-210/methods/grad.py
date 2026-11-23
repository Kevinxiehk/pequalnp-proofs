import numpy as np, itertools, sys
n=5
P4=list(itertools.permutations(range(n-1)))
def perm4(A): return sum(A[0,p[0]]*A[1,p[1]]*A[2,p[2]]*A[3,p[3]] for p in P4)
def grad(X):
    g=np.zeros((n,n),dtype=complex)
    for i in range(n):
        for j in range(n):
            g[i,j]=perm4(np.delete(np.delete(X,i,0),j,1))
    return g.ravel()
def Wdim(B,samples=60,seed=0):
    rng=np.random.default_rng(seed); d=B.shape[0]
    G=[grad(np.ones((n,n))+np.tensordot(rng.normal(size=d)+1j*rng.normal(size=d),B.reshape(d,n,n),1)) for _ in range(samples)]
    s=np.linalg.svd(np.array(G),compute_uv=False); return int((s>1e-8*s[0]).sum())
def l080():
    basis=[]
    for a in range(3):
        t=np.zeros((n,n)); t[n-1,a]=1; t[n-1,n-2]=-1; basis.append(t.ravel())
    for b in range(n-1):
        t=np.zeros((n,n)); t[b,n-1]=1; t[n-1,n-1]=-1; basis.append(t.ravel())
    return np.array(basis,dtype=complex)
B=l080(); print('L080 d=7: dim W(L)=',Wdim(B),' (L perp in C^25 has dim',25-7,')')
U,S,Vh=np.linalg.svd(np.load('/home/claude/work/L-gct-086/smallcases/ext_w5_4.npy').reshape(7,25),full_matrices=False)
B4=Vh[:4]; print('k3m1 d=4: dim W=',Wdim(B4),' perp',21)
B3=np.load('/home/claude/work/L-gct-210/dc5/sol_d3_k234_s4.npy').reshape(-1,25); print('DC d=3 (dc5 file, check level!): dim W=',Wdim(B3),' perp',22)
# sub-spaces of L080
for k in range(1,7):
    print('L080 first',k,'basis vectors: dim W=',Wdim(B[:k]))
