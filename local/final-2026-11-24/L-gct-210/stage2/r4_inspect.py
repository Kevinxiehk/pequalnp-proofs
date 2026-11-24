import numpy as np, itertools
np.set_printoptions(precision=4,suppress=True,linewidth=220)
ex=np.load('/tmp/r4_block_examples.npy')
def perm(M):
    n=len(M); return sum(np.prod([M[i,p[i]] for i in range(n)]) for p in itertools.permutations(range(n)))
rg=np.random.default_rng(0)
for F in ex:
    types=[(int(sum(np.linalg.norm(F[j,i])>1e-6 for i in range(3))),int((np.linalg.svd(F[j],compute_uv=False)>1e-6).sum())) for j in range(5)]
    print('types',types)
    # level check
    w=0
    for _ in range(5):
        p=rg.normal(size=(3,2))+1j*rg.normal(size=(3,2)); p[2]=-p[0]-p[1]; t=np.zeros((5,5),complex)
        for i in range(3): t[2+i]=F[:,i,:]@p[i]
        w=max(w,abs(perm(np.ones((5,5))+t)-120))
    print(' level defect',w)
    if types[0]==(3,1):
        lam=F[:,0,:]                                  # forms of row c
        print(' forms of row c (lam_j):\n',lam)
        # proportionality classes of lam_j
        cl=[]; reps=[]
        for j in range(5):
            for k,r in enumerate(reps):
                if abs(lam[j,0]*r[1]-lam[j,1]*r[0])<1e-6: cl.append(k); break
            else: reps.append(lam[j]); cl.append(len(reps)-1)
        print(' classes of the lam_j:',cl)
        a=[(F[j,1,:]@lam[j].conj())/(lam[j]@lam[j].conj()) for j in range(5)]; b=[(F[j,2,:]@lam[j].conj())/(lam[j]@lam[j].conj()) for j in range(5)]
        print(' a=',np.array(a)); print(' b=',np.array(b))
        for i in range(3): print(' singular values of psi_%d:'%i,np.linalg.svd(F[:,i,:],compute_uv=False))
