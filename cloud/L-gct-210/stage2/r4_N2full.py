# Family N2 (stage3 sec.16) WITHOUT any zero-freeness: necessary conditions on M = L_a + L_b (6-dim):
#   M = {(s_a rho_a; s_b rho_b; Psi_c q_c; Psi_d q_d; Psi_e q_e) : q_c+q_d+q_e = s_a om_a + s_b om_b},  Psi_i: C^2 -> C^5.
#   (1) perm(J + m) = 120 on M;  (2) all 4x4 subpermanents of the rows (b,c,d,e) vanish on L_a = M cap {s_a = 0} (chief RP9, a_a = 1),
#   and of the rows (a,c,d,e) on L_b.  LM from random starts; report solutions and their degeneracies.
import sys, itertools, numpy as np
from scipy.optimize import least_squares
rg=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 1); NT=int(sys.argv[2]) if len(sys.argv)>2 else 10
USEG=(len(sys.argv)<=3)
PERMS=np.array(list(itertools.permutations(range(5)))); P4=np.array(list(itertools.permutations(range(4))))
def perm5(A): return A[:,np.arange(5)[None,:],PERMS].prod(axis=2).sum(axis=1)       # A: (n,5,5)
def perm4(A): return A[:,np.arange(4)[None,:],P4].prod(axis=2).sum(axis=1)
NP=90; PT=rg.normal(size=(NP,6))+1j*rg.normal(size=(NP,6)); PG=rg.normal(size=(12,5))+1j*rg.normal(size=(12,5))
def unpack(z):
    c=z[:44]+1j*z[44:]; return c[:10].reshape(5,2),c[10:20].reshape(5,2),c[20:30].reshape(5,2),c[30:35],c[35:40],c[40:42],c[42:44]
def build(par,pts):
    Pc,Pd,Pe,ra,rb,oa,ob=par; sa=pts[:,0]; sb=pts[:,1]; qc=pts[:,2:4]; qd=pts[:,4:6]; qe=sa[:,None]*oa+sb[:,None]*ob-qc-qd
    return np.stack([sa[:,None]*ra, sb[:,None]*rb, qc@Pc.T, qd@Pd.T, qe@Pe.T],axis=1)
def res(z):
    par=unpack(z); m=build(par,PT); r=[perm5(1+m)-120]
    if USEG:
        for row in (0,1):
            pts=np.zeros((12,6),complex); pts[:,1-row]=PG[:,0]; pts[:,2:]=PG[:,1:]      # s_row = 0
            x=np.delete(build(par,pts),row,axis=1)                                        # (12,4,5)
            for j in range(5): r.append(perm4(np.delete(x,j,axis=2)))
    r=np.concatenate(r); Pc,Pd,Pe,ra,rb,oa,ob=par; G=Pc.conj().T@Pc
    nr=[G[0,0].real-1,G[1,1].real-1,G[0,1].real,G[0,1].imag,np.vdot(ra,ra).real-1,np.vdot(rb,rb).real-1]
    return np.concatenate([r.real,r.imag,nr])
if __name__=='__main__':
    np.set_printoptions(precision=3,suppress=True,linewidth=220)
    for trial in range(NT):
        z=rg.normal(size=88)*0.7; s=least_squares(res,z,method='lm',xtol=1e-14,ftol=1e-14,gtol=1e-14,max_nfev=3000)
        nrm=np.linalg.norm(s.fun)
        if nrm>1e-8: print(trial,'no convergence, residual %.2e'%nrm,flush=True); continue
        Pc,Pd,Pe,ra,rb,oa,ob=unpack(s.x)
        sv=[np.linalg.svd(M,compute_uv=False)[-1] for M in (Pc,Pd,Pe)]
        print(trial,'SOLUTION  min sing. values of Psi_c,d,e: %.2e %.2e %.2e'%tuple(sv),' |om_a|=%.2e |om_b|=%.2e'%(np.linalg.norm(oa),np.linalg.norm(ob)),
              ' zeros in rho_a:',[j for j in range(5) if abs(ra[j])<1e-6],' rho_b:',[j for j in range(5) if abs(rb[j])<1e-6],flush=True)
        np.save('/tmp/r4_N2full_%d.npy'%trial,s.x)
