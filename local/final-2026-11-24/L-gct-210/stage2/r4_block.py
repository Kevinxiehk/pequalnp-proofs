# General N2 block: X = {(psi_c(p_c); psi_d(p_d); psi_e(p_e)) : p_i in C^2, p_c+p_d+p_e = 0}, psi_i : C^2 -> C^5 linear (forms
# F[j,i,:] = entry (i,j) as a linear form). Level <=> P_1 = P_2 = P_3 = 0 on X. LM from random starts; classify solutions by the
# column types: for column j the 3x2 matrix M_j of the three forms: (number of nonzero rows, rank).
import sys, numpy as np
from scipy.optimize import least_squares
rg=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 1); NT=int(sys.argv[2]) if len(sys.argv)>2 else 40
PTS=rg.normal(size=(30,4))+1j*rg.normal(size=(30,4))
def elems(F,pts):
    pc=pts[:,:2]; pd=pts[:,2:]; pe=-pc-pd
    return np.stack([pc@F[:,0,:].T, pd@F[:,1,:].T, pe@F[:,2,:].T],axis=1)      # (npts,3,5)
def P123(t):
    s=t.sum(axis=2); g=np.einsum('nij,nkj->nik',t,t)
    P1=s.sum(axis=1); P2=s[:,0]*s[:,1]+s[:,0]*s[:,2]+s[:,1]*s[:,2]-g[:,0,1]-g[:,0,2]-g[:,1,2]
    P3=s[:,0]*s[:,1]*s[:,2]-s[:,0]*g[:,1,2]-s[:,1]*g[:,0,2]-s[:,2]*g[:,0,1]+2*(t[:,0]*t[:,1]*t[:,2]).sum(axis=1)
    return P1,P2,P3
def res(z):
    F=(z[:30]+1j*z[30:]).reshape(5,3,2); t=elems(F,PTS); P1,P2,P3=P123(t)
    r=np.concatenate([P1[:6],P2[:14],P3]); nr=[]
    for i in range(3):
        G=F[:,i,:].conj().T@F[:,i,:]; nr+=[G[0,0].real-1,G[1,1].real-1,G[0,1].real,G[0,1].imag]
    return np.concatenate([r.real,r.imag,nr])
def coltype(M,tol=1e-6):
    nzrows=tuple(int(np.linalg.norm(M[i])>tol) for i in range(3)); rk=int((np.linalg.svd(M,compute_uv=False)>tol).sum())
    return (sum(nzrows),rk)
if __name__=='__main__':
    stats={}; ex={}
    for trial in range(NT):
        z=rg.normal(size=60); s=least_squares(res,z,method='lm',xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=600)
        if np.linalg.norm(s.fun)>1e-9: stats['noconv']=stats.get('noconv',0)+1; continue
        F=(s.x[:30]+1j*s.x[30:]).reshape(5,3,2)
        key=tuple(sorted(coltype(F[j]) for j in range(5)))
        stats[key]=stats.get(key,0)+1; ex.setdefault(key,F); print(trial,key,flush=True)
    for k,v in sorted(stats.items(),key=lambda kv:-kv[1] if kv[0]!='noconv' else 1): print(v,k)
    np.save('/tmp/r4_block_examples.npy',np.array([ex[k] for k in ex if k!='noconv']))
