# Faster version of r4_N2inj.py: Psi_d = Q_d R_d, R_d = [[exp(x), y],[0, exp(z)]] (invertible), same for e; Psi_c = Q_c (gauge).
# Classify each solution: dims of single-column / single-row elements of M, row/column projection dims of M.
import sys, itertools, numpy as np
from scipy.optimize import least_squares
sys.path.insert(0,'/home/claude/work/L-gct-210/stage2'); from pairlib import rank
rg=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 1); NT=int(sys.argv[2]) if len(sys.argv)>2 else 10
MODE=sys.argv[3] if len(sys.argv)>3 else 'full'
PERMS=np.array(list(itertools.permutations(range(5)))); P4=np.array(list(itertools.permutations(range(4))))
def perm5(A): return A[:,np.arange(5)[None,:],PERMS].prod(axis=2).sum(axis=1)
def perm4(A): return A[:,np.arange(4)[None,:],P4].prod(axis=2).sum(axis=1)
NP=70; PT=rg.normal(size=(NP,6))+1j*rg.normal(size=(NP,6)); PG=rg.normal(size=(10,5))+1j*rg.normal(size=(10,5))
def R(c): return np.array([[np.exp(c[0]),c[1]],[0,np.exp(c[2])]])
def maps(z):
    c=z[:50]+1j*z[50:]; Qc=c[:10].reshape(5,2); Qd=c[10:20].reshape(5,2); Qe=c[23:33].reshape(5,2)
    return Qc,Qd@R(c[20:23]),Qe@R(c[33:36]),c[36:41],c[41:46],c[46:48],c[48:50],Qd,Qe
def build(par,pts):
    Pc,Pd,Pe,ra,rb,oa,ob=par[:7]; sa=pts[:,0]; sb=pts[:,1]; qc=pts[:,2:4]; qd=pts[:,4:6]; qe=sa[:,None]*oa+sb[:,None]*ob-qc-qd
    return np.stack([sa[:,None]*ra, sb[:,None]*rb, qc@Pc.T, qd@Pd.T, qe@Pe.T],axis=1)
def res(z):
    par=maps(z); m=build(par,PT); r=[perm5(1+m)-120]
    if MODE=='full':
        for row in (0,1):
            pts=np.zeros((10,6),complex); pts[:,1-row]=PG[:,0]; pts[:,2:]=PG[:,1:]
            x=np.delete(build(par,pts),row,axis=1)
            for j in range(5): r.append(perm4(np.delete(x,j,axis=2)))
    r=np.concatenate(r); nr=[]
    for Q in (par[0],par[7],par[8]):
        G=Q.conj().T@Q; nr+=[G[0,0].real-1,G[1,1].real-1,G[0,1].real,G[0,1].imag]
    nr+=[np.vdot(par[3],par[3]).real-1,np.vdot(par[4],par[4]).real-1]
    return np.concatenate([r.real,r.imag,nr])
def classify(z):
    par=maps(z); B=build(par,np.eye(6,dtype=complex)); F=B.reshape(6,25)
    zc=[6-rank(np.delete(B,j,axis=2).reshape(6,-1)) for j in range(5)]; zr=[6-rank(np.delete(B,i,axis=1).reshape(6,-1)) for i in range(5)]
    return dict(dimM=rank(F),single_col=zc,single_row=zr,rowproj=[rank(B[:,i,:]) for i in range(5)],colproj=[rank(B[:,:,j]) for j in range(5)])
if __name__=='__main__':
    nsol=0
    for trial in range(NT):
        z=rg.normal(size=100)*0.6; s=least_squares(res,z,method='lm',xtol=1e-14,ftol=1e-14,gtol=1e-14,max_nfev=int(sys.argv[4]) if len(sys.argv)>4 else 250)
        nrm=np.linalg.norm(s.fun); par=maps(s.x); sv=[np.linalg.svd(M,compute_uv=False)[-1] for M in par[:3]]
        if nrm<1e-8:
            nsol+=1; np.save('/tmp/r4_N2fast_%s_%s_%d.npy'%(MODE,sys.argv[1] if len(sys.argv)>1 else '1',trial),s.x)
            print(trial,'SOLUTION  smin(Psi_d,Psi_e) = %.1e %.1e'%(sv[1],sv[2]),classify(s.x),flush=True)
        else: print(trial,'no convergence, residual %.1e, smin %.1e %.1e'%(nrm,sv[1],sv[2]),flush=True)
    print('mode',MODE,': solutions',nsol,'of',NT)
