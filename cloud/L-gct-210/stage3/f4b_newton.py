# Round 8: F4b core, level conditions only, holomorphic LM with ANALYTIC Jacobian (cofactor permanents), generic affine normalisations.
# usage: python3 -I f4b_newton.py SEED TIMELIMIT [NSAMP]
import numpy as np, itertools, sys, time
seed=int(sys.argv[1]); TL=float(sys.argv[2]); NP=int(sys.argv[3]) if len(sys.argv)>3 else 850
rg=np.random.default_rng(1000+seed)
SG5=np.concatenate([np.ones((16,1)),np.array(list(itertools.product([1,-1],repeat=4)))],axis=1); SP5=SG5.prod(axis=1)
SG4=np.concatenate([np.ones((8,1)),np.array(list(itertools.product([1,-1],repeat=3)))],axis=1); SP4=SG4.prod(axis=1)
def perm5(X):
    N=X.shape[0]; S=(SG5@X.transpose(1,0,2).reshape(5,N*5)).reshape(16,N,5); return (S.prod(axis=2)*SP5[:,None]).sum(axis=0)/16.0
def perm4(X):
    N=X.shape[0]; S=(SG4@X.transpose(1,0,2).reshape(4,N*4)).reshape(8,N,4); return (S.prod(axis=2)*SP4[:,None]).sum(axis=0)/8.0
IDX=[[i for i in range(5) if i!=k] for k in range(5)]
def cof(X):
    N=X.shape[0]; C=np.empty((N,5,5),dtype=complex)
    for i in range(5):
        Xi=X[:,IDX[i],:]
        for j in range(5): C[:,i,j]=perm4(Xi[:,:,IDX[j]])
    return C
D=7; NU=50
T=np.zeros((D,NU,5,5))
for r in range(4):
    for j in range(5): T[r,r*5+j,r,j]=1; T[r,20+j,4,j]=1
for j in range(5):
    T[4,25+j,4,j]=1; T[5,30+j,0,j]=1; T[5,35+j,1,j]=1; T[6,40+j,2,j]=1; T[6,45+j,3,j]=1
Cc=(rg.normal(size=(NP,D))+1j*rg.normal(size=(NP,D)))*0.6
CT=np.einsum('nk,kmij->nmij',Cc,T).reshape(NP,NU,25)            # dX_n/dtheta_m
# normalisations: <r1,p> = 1, <r2,w> = 1, <r3,g_a> = 1, <r4,g_c> = 1, gauges <r5,p> = 0, <r6,g_b> = 0, <r7,g_d> = 0
def rv(): return rg.normal(size=5)+1j*rg.normal(size=5)
NORM=np.zeros((7,NU),dtype=complex); RHS=np.array([1,1,1,1,0,0,0],dtype=complex)
for row,(off) in enumerate([20,25,30,40,20,35,45]): NORM[row,off:off+5]=rv()
def FJ(th):
    X=np.ones((5,5))+np.einsum('nmq,m->nq',CT,th).reshape(NP,5,5)
    F=np.concatenate([(perm5(X)-120.0)/30.0, NORM@th-RHS])
    C=cof(X).reshape(NP,25); J=np.concatenate([np.einsum('nmq,nq->nm',CT,C)/30.0, NORM])
    return F,J
def solve(th,maxit=80):
    lam=1e-2; F,J=FJ(th); f=np.linalg.norm(F)
    for it in range(maxit):
        A=J.conj().T@J; g=J.conj().T@F
        for _ in range(8):
            try: d=np.linalg.solve(A+lam*np.eye(NU),g)
            except np.linalg.LinAlgError: lam*=10; continue
            F2,J2=FJ(th-d); f2=np.linalg.norm(F2)
            if f2<f: th=th-d; F,J,f=F2,J2,f2; lam=max(lam/5,1e-12); break
            lam*=5
        else: break
        if f<1e-12: break
    return th,f
def sv2(u,v):
    A=np.array([u/np.linalg.norm(u),v/np.linalg.norm(v)]); return np.linalg.svd(A,compute_uv=False)[1]
def rank(M,tol=1e-6):
    s=np.linalg.svd(np.atleast_2d(M),compute_uv=False); return int((s>tol*max(1,s[0])).sum())
def basis(th):
    return np.einsum('kmij,m->kij',T,th)
if __name__=='__main__':
    t0=time.time(); n=0; conv=0; nondeg=[]; kinds={}
    while time.time()-t0<TL:
        n+=1; th,f=solve((rg.normal(size=NU)+1j*rg.normal(size=NU))*0.7)
        if f<1e-9:
            conv+=1; v=th.reshape(10,5); nr=np.linalg.norm(v,axis=1)
            svs=[sv2(v[r],v[6+r]) for r in range(4)]+[sv2(v[4],v[5])]
            B=basis(th); dimM=rank(B.reshape(D,25))
            ok=min(svs)>1e-3 and nr[:4].min()>1e-3 and dimM==7
            key=('dim M %d'%dimM,'nondegenerate' if ok else 'degenerate','rank(y_a..y_d) %d'%rank(v[:4],1e-5))
            kinds[key]=kinds.get(key,0)+1
            if ok: nondeg.append(th)
    print('seed',seed,'starts',n,'converged',conv,'(%.0f s)'%(time.time()-t0))
    for k,c in sorted(kinds.items(),key=lambda t:-t[1]): print('  ',c,k)
    np.save('f4b_newton_nondeg_%d.npy'%seed,np.array(nondeg))
