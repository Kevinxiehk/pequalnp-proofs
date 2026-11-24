# seeded LM: column-centred 4x5 level space of dim 4 with defect inside an E-dim subspace, seeded at a saved basis.
# usage: python3 -I ccpolish.py FILE.npy E
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows')
import numpy as np
from clm import *
f=sys.argv[1]; E=int(sys.argv[2])
B0=np.load(f).reshape(-1,20); d=len(B0)
class PC(Problem):
    def __init__(self):
        Problem.__init__(self,4,d,'defect',E,seed=7,N=200)
        self.Rc=np.zeros((5,32))
        for j in range(5): self.Rc[j,1<<j]=1
    def fun(self,z,jac=True):
        out=Problem.fun(self,z,jac)
        # column sums: linear in Y -> G[:, single j] coefficients
        Zf=self.Zfull(z); X=(self.A@Zf).reshape(self.N,4,5)
        cs=X.sum(1)                                   # (N,5)
        if not jac: return np.concatenate([out,cs.ravel()])
        r,J=out
        dcs=np.zeros((self.N,5,20),complex)
        for j in range(5):
            for i in range(4): dcs[:,j,i*5+j]=1
        DP=dcs@self.Pi[d:].T
        JW=np.einsum('na,nrb->nrab',self.A,DP).reshape(self.N*5,self.nW)
        Jc=np.concatenate([JW,np.zeros((self.N*5,self.nvar-self.nW),complex)],1)
        return np.concatenate([r,cs.ravel()]),np.concatenate([J,Jc],0)
P=PC()
# initial z: express span(B0) in the chart of P: rows [I | W] Pi ; solve for W from B0 Pi^H
M=B0@P.Pi.conj().T            # d x 20 coordinates in the Pi basis
W=np.linalg.solve(M[:,:d],M[:,d:])
z0=np.concatenate([W.ravel(),np.zeros(P.nT,complex)])
# initial T: fit the defect space of B0 in the chart [I|T] Fb
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/handoff'); import oracle
rng=np.random.default_rng(0)
C=np.array([oracle.deletion_vector(np.einsum('d,dab->ab',rng.normal(size=d)+1j*rng.normal(size=d),B0.reshape(d,4,5))) for _ in range(30)])
Cc=C@P.Fd.T                    # coordinates in the 1^perp basis
u,s,vh=np.linalg.svd(Cc); top=vh[:E]   # E-dim approx defect space in coordinates (rows)
if E>0:
    T=np.linalg.solve(top[:,:E],top[:,E:]); z0[P.nW:]=T.ravel()
z,c=solve(P,z0=z0,iters=400,tol=1e-14)
Bz=P.basis(z); print('polished residual %.2e'%c, ' oracle:', oracle.analyse_4x5(Bz)[:3], ' colsum %.1e'%np.abs(Bz.sum(1)).max(), ' dist to seed %.2e'%np.linalg.norm(Bz.reshape(d,-1)-B0@np.linalg.lstsq(B0.T,Bz.reshape(d,-1).T,rcond=None)[0].T if False else 0))
import os; np.save(os.path.join("/home/kevxhk/work/L-gct-210/ncol/ccn",os.path.basename(f).replace(".npy","_pol_e%d.npy"%E)),Bz)
