# verify2: check verifyfl's saved isotropic examples with my own evaluation code (arrays loaded with allow_pickle=False).
import numpy as np, itertools
P4=list(itertools.permutations(range(4)))
def perm4(A): return sum(A[0,p[0]]*A[1,p[1]]*A[2,p[2]]*A[3,p[3]] for p in P4)
def perm5(A): return sum(np.prod([A[i,p[i]] for i in range(5)]) for p in itertools.permutations(range(5)))
def Cvec(Y):
    M=1+Y; return np.array([perm4(np.delete(M,j,axis=1)) for j in range(5)])
rng=np.random.default_rng(1)
def check(B):
    k=len(B)
    cs=np.array([Cvec(np.tensordot(rng.normal(size=k)+1j*rng.normal(size=k),B,1))-24 for _ in range(12)])
    sv=np.linalg.svd(cs,compute_uv=False); m=np.linalg.svd(cs)[2][0]; m=m/m[np.argmax(abs(m))]
    print('  dim',np.linalg.matrix_rank(B.reshape(k,20)),' singular values of the defect vectors:',np.round(sv[:3],8),' m ~',np.round(m,4),' <m,m> = %.1e, sum m = %.1e'%(abs(m@m),abs(m.sum())))
    split=[]
    for i in range(4):
        E=np.zeros((4,5),complex); E[i]=m
        r=np.linalg.lstsq(B.reshape(k,20).T,E.reshape(20),rcond=None)[0]
        if np.linalg.norm(B.reshape(k,20).T@r-E.reshape(20))<1e-7: split.append(i)
    G=B.sum(axis=1); u,s,vh=np.linalg.svd(G.T); r=int(np.sum(s>1e-9)); N=vh[r:].conj().T
    K=np.tensordot(N.T,B,1)
    worst=max(np.abs(Cvec(np.tensordot(rng.normal(size=len(K))+1j*rng.normal(size=len(K)),K,1))-24).max() for _ in range(6)) if len(K) else 0
    # the 5x5 space L(L') = L' (+) e_5 (x) {1, m}^perp : level?
    W=[w for w in np.linalg.svd(np.array([np.ones(5),m]))[2][2:].conj()]
    L=[np.vstack([Y,np.zeros((1,5))]) for Y in B]+[np.vstack([np.zeros((4,5)),w[None,:]]) for w in W]
    lev=max(abs(perm5(1+np.tensordot(rng.normal(size=len(L))+1j*rng.normal(size=len(L)),np.array(L),1))-120) for _ in range(4))
    print('  rows i with e_i m^T in the space (split):',split,'; rank of column sums',r,'; dim ker kappa',len(K),'; max |C - 24| on ker kappa: %.3g'%worst,'; 5x5 space L(L\') of dim',len(L),'level error %.1e'%lev)
for f in ('r3_iso_counterexample.npy','r3_iso4_s0.npy'):
    B=np.load('/home/claude/work/L-gct-210/verifyfl/'+f,allow_pickle=False); print(f,'shape',B.shape)
    for Bs in ([B] if B.ndim==3 else list(B)): check(Bs)
