import sys, itertools, time
import numpy as np
from scipy.optimize import least_squares
# N3': perm_3 constant (!= 0) on b + V_0  =>  dim V_0 <= 3.  Search for lineality spaces of dim d at base point b (Grassmannian chart).
P3=list(itertools.permutations(range(3)))
def perm3(A): return sum(A[...,0,p[0]]*A[...,1,p[1]]*A[...,2,p[2]] for p in P3)
def make(b,d,rng,nsamp=40):
    C=rng.normal(size=(nsamp,d))+1j*rng.normal(size=(nsamp,d)); k=perm3(b)
    def basis(x,piv):
        X=(x[:d*(9-d)]+1j*x[d*(9-d):]).reshape(d,9-d); Bm=np.zeros((d,9),complex)
        Bm[:,piv[:d]]=np.eye(d); Bm[:,piv[d:]]=X; return Bm
    def res(x,piv):
        eta=(C@basis(x,piv)).reshape(nsamp,3,3); r=perm3(b[None]+eta)-k
        return np.concatenate([r.real,r.imag])
    return basis,res
def search(b,d,starts,rng,tol=1e-9):
    basis,res=make(b,d,rng); found=0; best=1e9
    for s in range(starts):
        piv=rng.permutation(9); x0=rng.normal(size=2*d*(9-d))*0.7
        sol=least_squares(res,x0,args=(piv,),method='lm',max_nfev=4000)
        c=np.sqrt(2*sol.cost); best=min(best,c)
        if c<tol: found+=1
    return found,best
rng=np.random.default_rng(1)
J=np.ones((3,3),complex)
ex=np.array([[2,1,-1],[1,1,1],[0,1,-1]],complex)
# explicit 3-dim lineality space of the example in the notes: E_11, e_2 (0,1,1)^T, E_31
V0=np.zeros((3,3,3),complex); V0[0,0,0]=1; V0[1,1,1]=1; V0[1,1,2]=1; V0[2,2,0]=1
c=rng.normal(size=(50,3))+1j*rng.normal(size=(50,3)); print('explicit 3-dim lineality space at ex: max dev %.1e'%np.abs(perm3(ex[None]+np.einsum('nk,kab->nab',c,V0))-perm3(ex)).max())
bs={'J':J,'I':np.eye(3,dtype=complex),'ex':ex,'I+E31+E32':np.eye(3)+np.array([[0,0,0],[0,0,0],[1,1,0]],complex),
    'circ I+P':np.array([[1,1,0],[0,1,1],[1,0,1]],complex),'random1':rng.normal(size=(3,3))+1j*rng.normal(size=(3,3)),'random2':rng.normal(size=(3,3))+0j,
    'rows(1,1,0),(0,1,1),rnd':np.array([[1,1,0],[0,1,1],[0.3,-1.2,0.7]],complex)}
t0=time.time()
for name,b in bs.items():
    f3,b3=search(b,3,12,rng); f4,b4=search(b,4,25,rng)
    print('%-24s perm=%8.3f  dim3: found %2d/12 (best %.1e)   dim4: found %2d/25 (best residual %.2e)'%(name,abs(perm3(b)),f3,b3,f4,b4))
print('time %.1f s'%(time.time()-t0))
