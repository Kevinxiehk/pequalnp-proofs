# N2 experiment: does a 5-dim "V-twisted" space  L_a = {(mu rho; A_c v_c; A_d v_d; A_e v_e) : v_c+v_d+v_e = mu w}  (rows b,c,d,e; w = e_1 in V = C^2)
# exist with: level (4x5), (Q5 at u=J): perm_3 = 0 on P_c x P_d x P_e, (Qb): rho P_c P_d P_e = 0 in A_4,  rho != 0, A_i injective?
import itertools, sys, time
import numpy as np
from scipy.optimize import least_squares
PERMS=np.array(list(itertools.permutations(range(5))))
def perm5(M):            # M: (N,5,5)
    out=np.ones((M.shape[0],len(PERMS)),complex)
    for i in range(5): out*=M[:,i,PERMS[:,i]]
    return out.sum(1)
seed=int(sys.argv[1]) if len(sys.argv)>1 else 0
TLIM=float(sys.argv[2]) if len(sys.argv)>2 else 120
rng=np.random.default_rng(seed)
NS=150
PAR=(rng.normal(size=(NS,5))+1j*rng.normal(size=(NS,5)))*0.8      # mu, v_c(2), v_d(2)
TR=list(itertools.product(range(2),repeat=3))
EYE=np.eye(5)
def unpack(x):
    z=x[:35]+1j*x[35:]
    return z[:10].reshape(5,2),z[10:20].reshape(5,2),z[20:30].reshape(5,2),z[30:35]
def hard_res(x):
    Ac,Ad,Ae,rho=unpack(x); r=[]
    sc,sd,se=Ac.sum(0),Ad.sum(0),Ae.sum(0)
    r+=list(sc-sd)+list(sc-se)+[rho.sum()+sc[0]]
    # Q5 at J and Qb, via 5x5 permanents: rows [1 or rho; r1; r2; r3; 1 or e_m]
    M=np.ones((8*6,5,5),complex)
    for n,(ec,ed,ee) in enumerate(TR):
        for m in range(6):
            k=6*n+m
            M[k,1]=Ac[:,ec]; M[k,2]=Ad[:,ed]; M[k,3]=Ae[:,ee]
            if m<5: M[k,0]=rho; M[k,4]=EYE[m]
    r+=list(perm5(M))
    mu=PAR[:,0]; vc=PAR[:,1:3]; vd=PAR[:,3:5]; ve=-vc-vd; ve[:,0]+=mu
    M=np.ones((NS,5,5),complex)
    M[:,1,:]+=mu[:,None]*rho[None,:]; M[:,2,:]+=vc@Ac.T; M[:,3,:]+=vd@Ad.T; M[:,4,:]+=ve@Ae.T
    r+=list((perm5(M)-120)/30)
    return np.array(r)
def resid(x,soft=0.3):
    Ac,Ad,Ae,rho=unpack(x); r=list(hard_res(x))
    r.append(np.vdot(rho,rho)-1)                                                              # normalisation rho != 0
    for A in (Ac,Ad,Ae): r+=list((A.conj().T@A-np.eye(2)).ravel()*soft)                       # soft: keep A_i near isometries (injective)
    r=np.array(r); return np.concatenate([r.real,r.imag])
t0=time.time(); tried=0
x0=rng.normal(size=70); t1=time.time(); resid(x0); print('eval time %.4f s'%(time.time()-t1),flush=True)
while time.time()-t0<TLIM:
    tried+=1
    x0=rng.normal(size=70)*0.6
    sol=least_squares(resid,x0,method='lm',max_nfev=6000)
    h=np.abs(hard_res(sol.x)).max()
    Ac,Ad,Ae,rho=unpack(sol.x)
    sv=[np.linalg.svd(A,compute_uv=False) for A in (Ac,Ad,Ae)]
    print('start',tried,'cost %.2e'%sol.cost,'max hard resid %.1e'%h,'|rho| %.2f'%np.linalg.norm(rho),'min sv',np.round([s[1] for s in sv],3),'nfev',sol.nfev,flush=True)
    if h<1e-8:
        np.save('n2_La_sol_%d_%d.npy'%(seed,tried),sol.x)
print('time',round(time.time()-t0,1))
