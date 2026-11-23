# N2 necessary conditions, algebraic form (no sampling). Unknowns: A_c, A_d, A_e (5x2), rho (5), w (2)   [L_a = {(mu rho; A_c v_c; A_d v_d; A_e v_e): sum v = mu w}]
# Equations: P_1, P_2 of L_a; (Q5 at J): perm_3 = 0 on P_c x P_d x P_e; (E1 at J): p_3(rho, P_k, P_l) = 0; (Qb): rho P_c P_d P_e = 0 in A_4.
# (these imply that L_a is level).  Normalisations: A_c^H A_c = I (gauge GL(V)), |rho| = 1.  Question: solutions with A_d, A_e injective, w != 0, W != 0?
import itertools, sys, time
import numpy as np
from scipy.optimize import least_squares
PERMS=np.array(list(itertools.permutations(range(5))))
def perm5(M):
    out=np.ones((M.shape[0],len(PERMS)),complex)
    for i in range(5): out*=M[:,i,PERMS[:,i]]
    return out.sum(1)
seed=int(sys.argv[1]); TLIM=float(sys.argv[2]); rng=np.random.default_rng(seed)
TR=list(itertools.product(range(2),repeat=3)); EYE=np.eye(5)
def unpack(x):
    z=x[:37]+1j*x[37:]
    return z[:10].reshape(5,2),z[10:20].reshape(5,2),z[20:30].reshape(5,2),z[30:35],z[35:37]
def hard_res(x):
    Ac,Ad,Ae,rho,w=unpack(x); r=[]
    sc,sd,se=Ac.sum(0),Ad.sum(0),Ae.sum(0)
    r+=list(sc-sd)+list(sc-se)+[rho.sum()+sc@w]
    # basis of L_a: rows (b,c,d,e)
    Z=np.zeros(5,complex)
    B=[np.array([rho,Z,Z,Ae@w])]
    for k in range(2):
        B.append(np.array([Z,Ac[:,k],Z,-Ae[:,k]])); B.append(np.array([Z,Z,Ad[:,k],-Ae[:,k]]))
    B=np.array(B); S=B.sum(2)                       # (5 basis, 4 rows)
    G=np.einsum('pij,qkj->pqik',B,B)                # <xi^p_i, xi^q_k>
    for p in range(5):
        for q in range(p,5):
            val=0
            for i in range(4):
                for k in range(4):
                    if i!=k: val+=S[p,i]*S[q,k]-G[p,q,i,k]
            r.append(val)
    M=np.ones((8*6+12,5,5),complex)
    for n,(ec,ed,ee) in enumerate(TR):
        for m in range(6):
            k=6*n+m
            M[k,1]=Ac[:,ec]; M[k,2]=Ad[:,ed]; M[k,3]=Ae[:,ee]
            if m<5: M[k,0]=rho; M[k,4]=EYE[m]
    k=48
    for (X,Y) in ((Ac,Ad),(Ac,Ae),(Ad,Ae)):
        for e1 in range(2):
            for e2 in range(2):
                M[k,0]=rho; M[k,1]=X[:,e1]; M[k,2]=Y[:,e2]; k+=1
    r+=list(perm5(M))
    return np.array(r)
def resid(x):
    Ac,Ad,Ae,rho,w=unpack(x); r=list(hard_res(x))
    r.append(np.vdot(rho,rho)-1); r+=list((Ac.conj().T@Ac-np.eye(2)).ravel())
    r=np.array(r); return np.concatenate([r.real,r.imag])
def Wdim(Ac,Ad,Ae):
    rows=[]
    for (ec,ed,ee) in TR:
        y=[Ac[:,ec],Ad[:,ed],Ae[:,ee]]
        rows.append([sum(np.prod([y[i][K[p[i]]] for i in range(3)]) for p in itertools.permutations(range(3))) for K in itertools.combinations(range(5),3)])
    s=np.linalg.svd(np.array(rows),compute_uv=False); return int((s>1e-6*max(1,s[0])).sum()),s[0]
t0=time.time(); tried=0; good=0
while time.time()-t0<TLIM:
    tried+=1
    x0=rng.normal(size=74)*0.7
    sol=least_squares(resid,x0,method='lm',max_nfev=3000)
    h=np.abs(hard_res(sol.x)).max()
    Ac,Ad,Ae,rho,w=unpack(sol.x)
    sv=[np.linalg.svd(A,compute_uv=False)[1] for A in (Ac,Ad,Ae)]
    wd,ws=Wdim(Ac,Ad,Ae)
    tag='EXACT' if h<1e-9 else ''
    if h<1e-9: good+=1; np.save('n2_alg_sol_%d_%d.npy'%(seed,tried),sol.x)
    print('start',tried,'max hard resid %.1e'%h,'min sv',np.round(sv,3),'|w| %.3f'%np.linalg.norm(w),'dim W',wd,'(top sv %.2e)'%ws,tag,flush=True)
print('time',round(time.time()-t0,1),'starts',tried,'exact solutions',good)
