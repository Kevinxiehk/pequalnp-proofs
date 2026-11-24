import numpy as np, itertools, sys
def per(M):
    n=M.shape[0]; return sum(np.prod([M[i,p[i]] for i in range(n)]) for p in itertools.permutations(range(n)))
def Pk(M,k):
    p,q=M.shape; return sum(per(M[np.ix_(R,C)]) for R in itertools.combinations(range(p),k) for C in itertools.combinations(range(q),k))
w3=np.exp(2j*np.pi/3); n1=np.array([1,w3,w3*w3]); n2=np.array([1,w3*w3,w3])/3
for f in sys.argv[1:]:
    B=np.load(f); d=len(B); rng=np.random.default_rng(11); worst=0; D=[]
    for t in range(40):
        Y=np.einsum('d,dab->ab',rng.normal(size=d)+1j*rng.normal(size=d),B)
        worst=max(worst,abs(Pk(Y,1)),abs(Pk(Y,2)),abs(Pk(Y,3)),abs(Y.sum(0)).max())
        D.append([2*Pk(np.delete(Y,j,axis=1),2)+Pk(np.delete(Y,j,axis=1),3) for j in range(5)])
    D=np.array(D); s=np.linalg.svd(D,compute_uv=False); e=int((s>1e-7*s[0]).sum())
    # (a,beta) coordinates: Y = n1 a^T + 3 n2 beta^T  -> a = (conj-free) solve
    M=np.stack([n1,3*n2],1)            # 3x2
    AB=[np.linalg.lstsq(M,Bk,rcond=None)[0] for Bk in B]   # each 2x5: rows a, beta
    Am=np.array([x[0] for x in AB]); Bm=np.array([x[1] for x in AB])
    ra=np.linalg.matrix_rank(Am,1e-8); rb=np.linalg.matrix_rank(Bm,1e-8)
    print('%s: fresh %.1e  e=%d  sv %s  r_a=%d r_b=%d'%(f,worst,e,np.round(s/s[0],6),ra,rb))
