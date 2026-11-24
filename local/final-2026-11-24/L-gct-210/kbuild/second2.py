import sys; sys.path.insert(0,'.')
from second import *
def generic_dc_level(seed):
    rng=np.random.default_rng(seed)
    # DC basis: (e_i - e_4)(e_j - e_4)^T, i,j<4
    B=np.array([np.outer(np.eye(5)[i]-np.eye(5)[4],np.eye(5)[j]-np.eye(5)[4]) for i in range(4) for j in range(4)])
    def res(z):
        c=z[:16]+1j*z[16:]; t=np.einsum('i,iab->ab',c,B); P=Pall(t[None])[0,2:]
        o=np.concatenate([P,[np.vdot(c,c)-1]]); return np.concatenate([o.real,o.imag,np.zeros(22)])
    r=least_squares(res,rng.normal(size=32),method='lm',xtol=1e-15,ftol=1e-15,max_nfev=3000)
    c=r.x[:16]+1j*r.x[16:]; t=np.einsum('i,iab->ab',c,B); return t,np.linalg.norm(res(r.x))
e=np.eye(5)
which=sys.argv[1]; ms=[int(x) for x in sys.argv[2].split(',')]; seeds=int(sys.argv[3])
if which=='T5':
    g,r=generic_dc_level(1); print('generic DC level element: residual %.1e, rank'%r,np.linalg.matrix_rank(g,1e-8)); report('T5 generic DC level element',[g],ms,seeds)
if which=='T4':
    a=np.array([1,2.5,-0.5+1j,-3-1j,0]); report('T4 a chi1^T, a sum-zero with a_4=0 (Wxv type)',[np.outer(a,chi(1))],ms,seeds)
if which=='T8':
    report('T8 (e0-e1)(chi1+chi2)^T [2-row DC level]',[np.outer(e[0]-e[1],chi(1)+chi(2))],ms,seeds)
if which=='K':
    Kb=[np.outer(u,chi(1)),np.outer(u,chi(4)),np.outer(ub,chi(2)),np.outer(ub,chi(3))]; report('K (4-dim)',Kb,ms,seeds)
if which=='ex1D':
    report('DC part of ex1: u(e0-e1)^T, ubar(e2-e3)^T',[np.outer(u,e[0]-e[1]),np.outer(ub,e[2]-e[3])],ms,seeds)
