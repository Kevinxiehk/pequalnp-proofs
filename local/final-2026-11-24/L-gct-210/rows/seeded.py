import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows')
import numpy as np, time, glob
from clm import *
from rect import describe
def defect_basis(Z,e):
    d=len(Z); rng=np.random.default_rng(3)
    A=rng.normal(size=(200,d))+1j*rng.normal(size=(200,d))
    X=np.einsum('nk,kab->nab',A,Z); G,_=G_and_loo(X)
    pk=np.einsum('ns,kjs->nkj',G,Rdel()).reshape(-1,5)
    u,s,vh=np.linalg.svd(pk); return vh[:e]          # rows span the defect space (as row vectors p)
def start(P,Zs,Es,rng,scale=1.0):
    d,e=P.d,P.e; n=20
    Zm=Zs.reshape(len(Zs),n)
    extra=(rng.normal(size=(d-len(Zs),n))+1j*rng.normal(size=(d-len(Zs),n)))*scale/np.sqrt(n)
    Zm=np.concatenate([Zm,extra],0)
    AB=Zm@P.Pi.conj().T; W=np.linalg.solve(AB[:,:d],AB[:,d:])
    z=[W.ravel()]
    if e>0:
        E=Es if len(Es) else np.zeros((0,5),complex)
        ex=rng.normal(size=(e-len(E),5))+1j*rng.normal(size=(e-len(E),5)); ex=ex-ex.mean(1)[:,None]
        E=np.concatenate([E,ex],0)
        Cc=E@P.Fd.T; T=np.linalg.solve(Cc[:,:e],Cc[:,e:]); z.append(T.ravel())
    return np.concatenate(z)
if __name__=='__main__':
    pat=sys.argv[1]; e_old=int(sys.argv[2]); d=int(sys.argv[3]); e=int(sys.argv[4]); ntr=int(sys.argv[5]); tmax=float(sys.argv[6])
    files=sorted(glob.glob(pat)); t0=time.time(); nf=0; nt=0; best=[]
    for tr in range(ntr):
        if time.time()-t0>tmax: break
        f=files[tr%len(files)]; Zs=np.load(f); Es=defect_basis(Zs,e_old)
        P=Problem(4,d,'defect',e,seed=1000+tr); z0=start(P,Zs,Es,P.rng,scale=[1.0,0.3,3.0][tr%3])
        z,c=solve(P,z0=z0,iters=300); Z=P.basis(z); cond=np.linalg.cond(Z.reshape(d,-1)); nt+=1; best.append(c)
        if c<1e-9 and cond<1e6:
            nf+=1; print('FOUND',f,'trial',tr,'res %.1e cond %.1e'%(c,cond),'defect sv',np.array2string(defect_dim(Z)[:5],precision=1),flush=True)
            np.save('seed_d%d_e%d_t%d.npy'%(d,e,tr),Z)
    print('seeded %s (e_old=%d) -> (d,e)=(%d,%d): found %d of %d; smallest residuals %s; t=%.0f'%(pat,e_old,d,e,nf,nt,np.array2string(np.sort(best)[:4],precision=1),time.time()-t0),flush=True)
