# C1 multi-variant driver (unseeded / nc = one neutral column / seeded), their clm.py, errata sample sizes, polish + oracle
import os, sys, time, glob
os.environ.setdefault('OMP_NUM_THREADS','1'); os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from multiprocessing import Pool
import clm, oracle
from clm import Problem, G_and_loo, Rdel, shiftj, Q
NBY={3:140,4:140,5:160,6:260,7:420}
class PN(Problem):                      # rows/ncdef_search.py, with N passed
    def __init__(self,d,e,k,seed,N):
        Problem.__init__(self,4,d,'defect',e,seed=seed,N=N); self.k=k
    def fun(self,z,jac=True):
        N,d=self.N,self.d; n=4*Q
        Zf=self.Zfull(z); X=(self.A@Zf).reshape(N,4,Q); G,loo=G_and_loo(X)
        rx=np.einsum('ns,kjs->nkj',G,self.Rd)[:,:,:self.k].reshape(-1)
        if not jac: return np.concatenate([Problem.fun(self,z,False),rx])
        r,J=Problem.fun(self,z,True)
        dG=np.stack([np.stack([shiftj(loo[i],j) for j in range(Q)],1) for i in range(4)],1)
        dpk=np.einsum('nijs,kms->nkmij',dG,self.Rd[:,:self.k,:]).reshape(N,4*self.k,n)
        DP=dpk@self.Pi[d:].T
        JW=np.einsum('na,nrb->nrab',self.A,DP).reshape(N*4*self.k,self.nW)
        Jx=np.concatenate([JW,np.zeros((JW.shape[0],self.nvar-self.nW),complex)],1)
        return np.concatenate([r,rx]),np.concatenate([J,Jx],0)
def defect_basis(Z,e):                   # rows/seeded.py
    d=len(Z); rng=np.random.default_rng(3)
    A=rng.normal(size=(200,d))+1j*rng.normal(size=(200,d))
    X=np.einsum('nk,kab->nab',A,Z); G,_=G_and_loo(X)
    pk=np.einsum('ns,kjs->nkj',G,Rdel()).reshape(-1,5)
    u,s,vh=np.linalg.svd(pk); return vh[:e]
def start(P,Zs,Es,rng,scale=1.0):        # rows/seeded.py
    d,e=P.d,P.e; n=20
    Zm=Zs.reshape(len(Zs),n)
    extra=(rng.normal(size=(d-len(Zs),n))+1j*rng.normal(size=(d-len(Zs),n)))*scale/np.sqrt(n)
    Zm=np.concatenate([Zm,extra],0)
    AB=Zm@P.Pi.conj().T; W=np.linalg.solve(AB[:,:d],AB[:,d:])
    z=[W.ravel()]
    if e>0:
        E=Es if len(Es) else np.zeros((0,5),complex)
        E=E[:e]
        ex=rng.normal(size=(e-len(E),5))+1j*rng.normal(size=(e-len(E),5)); ex=ex-ex.mean(1)[:,None]
        E=np.concatenate([E,ex],0)
        Cc=E@P.Fd.T; T=np.linalg.solve(Cc[:,:e],Cc[:,e:]); z.append(T.ravel())
    return np.concatenate(z)
def one(job):
    kind,d,e,seed,extra=job
    N=NBY[d]
    if kind=='nc': P=PN(d,e,1,seed,N)
    else: P=Problem(4,d,'defect',e,seed=seed,N=N)
    z0=None
    if kind=='seeded':
        f,e_old,scale=extra; Zs=np.load(f); Es=defect_basis(Zs,e_old); z0=start(P,Zs,Es,P.rng,scale)
    z,c=clm.solve(P,z0=z0,iters=300 if kind=='seeded' else 250)
    Z=P.basis(z); sv=np.linalg.svd(Z.reshape(d,-1),compute_uv=False); cond=sv.max()/sv.min()
    if not (c<1e-9 and cond<1e6):
        if c<1e-5: np.save('near/%s_d%d_e%d_s%d.npy'%(kind,d,e,seed),Z)
        return (seed,c,None,None)
    z2,c2=clm.solve(P,z0=z,iters=500,tol=1e-13)
    if c2<c: z,c=z2,c2
    Z=P.basis(z)
    dim,lev,ee,dsv=oracle.analyse_4x5(Z)
    L=oracle.lift_to_5x5(Z); ldim=np.linalg.matrix_rank(L.reshape(len(L),-1)); llev=oracle.level_error_5x5(L)
    fn='hits/%s_d%d_e%d_s%d.npy'%(kind,d,e,seed); np.save(fn,Z)
    ok = dim==d and lev<1e-8 and llev<1e-8
    return (seed,c,fn,'%s res %.1e cond %.1e oracle (d,e)=(%d,%d) d-e=%d lev %.1e lift dim %d lift lev %.1e%s'%('CONFIRMED' if ok else 'UNCONFIRMED',c,cond,dim,ee,dim-ee,lev,ldim,llev,' extra=%s'%(extra,) if extra else ''))
def run(kind,d,e,s0,n,nproc,seedpat=None,e_old=None,tag=''):
    jobs=[]
    if kind=='seeded':
        files=sorted(sum([glob.glob(p) for p in seedpat.split(',')],[]))
        if not files: print('NO SEED FILES for',seedpat,flush=True); return
        for t in range(n): jobs.append((kind,d,e,s0+t,(files[t%len(files)],e_old,[1.0,0.3,3.0][t%3])))
    else:
        jobs=[(kind,d,e,s,None) for s in range(s0,s0+n)]
    t0=time.time(); res=[]; hits=0; conf=0; target=0
    with Pool(nproc) as pool:
        for k,(seed,c,fn,info) in enumerate(pool.imap_unordered(one,jobs,chunksize=1)):
            res.append(c)
            if fn:
                hits+=1; conf+=info.startswith('CONFIRMED')
                dme=int(info.split('d-e=')[1].split()[0])
                if info.startswith('CONFIRMED') and dme>=4: target+=1; print('!!! TARGET HIT (d-e>=4):',fn,info,flush=True)
                else: print('hit',fn,info,flush=True)
            if (k+1)%250==0: print('progress %s'%tag,k+1,'hits',hits,'confirmed',conf,'d-e>=4',target,'t=%.0f'%(time.time()-t0),flush=True)
    res=np.array(res)
    print('CASE %s kind=%s d=%d e=%d N=%d starts %d: hits %d, oracle-confirmed %d, confirmed with d-e>=4: %d; res<1e-5: %d; t=%.0f s'%(tag,kind,d,e,NBY[d],len(res),hits,conf,target,(res<1e-5).sum(),time.time()-t0),flush=True)
if __name__=='__main__':
    a=sys.argv[1:]
    kind,d,e,s0,n,nproc=a[0],int(a[1]),int(a[2]),int(a[3]),int(a[4]),int(a[5])
    if kind=='seeded': run(kind,d,e,s0,n,nproc,seedpat=a[6],e_old=int(a[7]),tag=a[8] if len(a)>8 else '')
    else: run(kind,d,e,s0,n,nproc,tag=a[6] if len(a)>6 else '')
