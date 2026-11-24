# As r4_N2full.py but with psi_d, psi_e forced INJECTIVE: Psi_d = Q_d expm(A_d), Q_d an orthonormal 2-frame (same for e); Psi_c = Q_c.
# A solution with a non-injective psi would need |A| -> infinity (reported as no convergence / large |A|).
import sys, itertools, numpy as np
from scipy.optimize import least_squares
from scipy.linalg import expm
rg=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 1); NT=int(sys.argv[2]) if len(sys.argv)>2 else 10
MODE=sys.argv[3] if len(sys.argv)>3 else 'full'      # 'full': level of M + G on L_a, L_b;  'level': level of M only;  'La': L_a only (level + G)
PERMS=np.array(list(itertools.permutations(range(5)))); P4=np.array(list(itertools.permutations(range(4))))
def perm5(A): return A[:,np.arange(5)[None,:],PERMS].prod(axis=2).sum(axis=1)
def perm4(A): return A[:,np.arange(4)[None,:],P4].prod(axis=2).sum(axis=1)
NP=90; PT=rg.normal(size=(NP,6))+1j*rg.normal(size=(NP,6)); PG=rg.normal(size=(12,5))+1j*rg.normal(size=(12,5))
if MODE=='La': PT[:,0]=0
def unpack(z):
    c=z[:52]+1j*z[52:]; Qc=c[:10].reshape(5,2); Qd=c[10:20].reshape(5,2); Ad=c[20:24].reshape(2,2); Qe=c[24:34].reshape(5,2); Ae=c[34:38].reshape(2,2)
    return Qc,Qd,Ad,Qe,Ae,c[38:43],c[43:48],c[48:50],c[50:52]
def maps(z):
    Qc,Qd,Ad,Qe,Ae,ra,rb,oa,ob=unpack(z); return Qc,Qd@expm(Ad),Qe@expm(Ae),ra,rb,oa,ob
def build(par,pts):
    Pc,Pd,Pe,ra,rb,oa,ob=par; sa=pts[:,0]; sb=pts[:,1]; qc=pts[:,2:4]; qd=pts[:,4:6]; qe=sa[:,None]*oa+sb[:,None]*ob-qc-qd
    return np.stack([sa[:,None]*ra, sb[:,None]*rb, qc@Pc.T, qd@Pd.T, qe@Pe.T],axis=1)
def res(z):
    par=maps(z); m=build(par,PT); r=[perm5(1+m)-120]
    if MODE!='level':
        for row in ((0,1) if MODE=='full' else (0,)):
            pts=np.zeros((12,6),complex); pts[:,1-row]=PG[:,0]; pts[:,2:]=PG[:,1:]
            x=np.delete(build(par,pts),row,axis=1)
            for j in range(5): r.append(perm4(np.delete(x,j,axis=2)))
    r=np.concatenate(r); Qc,Qd,Ad,Qe,Ae,ra,rb,oa,ob=unpack(z); nr=[]
    for Q in (Qc,Qd,Qe):
        G=Q.conj().T@Q; nr+=[G[0,0].real-1,G[1,1].real-1,G[0,1].real,G[0,1].imag]
    nr+=[np.vdot(ra,ra).real-1,np.vdot(rb,rb).real-1]
    return np.concatenate([r.real,r.imag,nr])
if __name__=='__main__':
    np.set_printoptions(precision=3,suppress=True,linewidth=220); nsol=0
    for trial in range(NT):
        z=rg.normal(size=104)*0.6; s=least_squares(res,z,method='lm',xtol=1e-14,ftol=1e-14,gtol=1e-14,max_nfev=2500)
        nrm=np.linalg.norm(s.fun); Pc,Pd,Pe,ra,rb,oa,ob=maps(s.x); sv=[np.linalg.svd(M,compute_uv=False) for M in (Pc,Pd,Pe)]
        tag='SOLUTION' if nrm<1e-8 else 'no convergence'
        if nrm<1e-8: nsol+=1; np.save('/tmp/r4_N2inj_%s_%d.npy'%(MODE,trial),s.x)
        print(trial,tag,'residual %.1e'%nrm,' sing. values Psi_d: %.1e %.1e  Psi_e: %.1e %.1e'%(sv[1][0],sv[1][1],sv[2][0],sv[2][1]),' |om_a|,|om_b| = %.1e %.1e'%(np.linalg.norm(oa),np.linalg.norm(ob)),flush=True)
    print('mode',MODE,': solutions',nsol,'of',NT)
