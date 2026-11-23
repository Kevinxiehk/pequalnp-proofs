# 6-dim 4x5 level spaces with a DELETABLE ROW of free part u (Type DR(u)): M = e_3 (x) U (+) N, U u-dim in C^5, N (6-u)-dim in rows 0..2.
# usage: U SEED TMAX
import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/reg2'); sys.path.insert(0,'/home/claude/work/L-gct-210/stage2')
import numpy as np, time
from ext6 import F45, classify
from t import level_err
u=int(sys.argv[1]); seed=int(sys.argv[2]); tmax=float(sys.argv[3]); rg=np.random.default_rng(seed)
nN=6-u; nz=5*u+15*nN
def build(z):
    B=[]
    for a in range(u):
        m=np.zeros((4,5),complex); m[3,:]=z[5*a:5*a+5]; B.append(m)
    for a in range(nN):
        m=np.zeros((4,5),complex); m[:3,:]=z[5*u+15*a:5*u+15*a+15].reshape(3,5); B.append(m)
    return np.array(B)
def solve(iters=140,N=240):
    C=rg.normal(size=(N,6))+1j*rg.normal(size=(N,6))
    def res(z):
        B=build(z); G=B.reshape(6,20); Gm=G@G.conj().T-np.eye(6)
        return np.concatenate([F45(np.einsum('nk,kij->nij',C,B))-120, 3*Gm.ravel().real, 3*Gm.ravel().imag])
    z=(rg.normal(size=nz)+1j*rg.normal(size=nz))/3; r=res(z); c=np.linalg.norm(r); mu=1e-2
    for it in range(iters):
        h=1e-6; Jc=np.empty((len(r),2*nz),complex)
        for a in range(nz):
            zp=z.copy(); zp[a]+=h; Jc[:,a]=(res(zp)-r)/h; zp=z.copy(); zp[a]+=1j*h; Jc[:,nz+a]=(res(zp)-r)/h
        Jr=np.concatenate([Jc.real,Jc.imag],0); rr=np.concatenate([r.real,r.imag]); A=Jr.T@Jr; g=Jr.T@rr
        for _ in range(8):
            dx=np.linalg.solve(A+mu*np.eye(2*nz),-g); zn=z+dx[:nz]+1j*dx[nz:]; rn=res(zn); cn=np.linalg.norm(rn)
            if cn<c: z=zn; r=rn; c=cn; mu=max(mu/5,1e-12); break
            mu*=6
        else: break
        if c<1e-11: break
    return c,build(z)
t0=time.time(); k=0; res=[]
while time.time()-t0<tmax:
    c,B=solve(); k+=1; res.append(c)
    if c<1e-9 and np.linalg.matrix_rank(B.reshape(6,20),tol=1e-6)==6 and level_err(B)<1e-8:
        typ,desc=classify(B,rg); print('u=%d start %d: %s %s'%(u,k,typ,desc),flush=True); np.save('dr_u%d_s%d_%d.npy'%(u,seed,k),B)
print('u=%d: %d starts, residuals %s'%(u,k,np.array2string(np.sort(res),precision=1)))
