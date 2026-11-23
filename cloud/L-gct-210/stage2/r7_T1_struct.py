# Structure of T_1(X) for (2,4) solutions: intersections with natural coordinate subspaces of C^{5x5}.
import sys, glob, itertools, numpy as np
A=list(sys.argv); sys.argv=[A[0]]
exec(open('/home/claude/work/L-gct-210/stage2/r5_FO2.py').read().split("if __name__=='__main__':")[0])
rg=np.random.default_rng(1)
def T1(X):
    Mb=X.reshape(len(X),25); rows=[cof55(np.ones((5,5))+((rg.normal(size=len(X))+1j*rg.normal(size=len(X)))@Mb).reshape(5,5)) for _ in range(70)]
    u,s,vh=np.linalg.svd(np.array(rows)); r=int((s>1e-8*s[0]).sum()); return vh[r:].conj()
def dim_cap(T,mask):                     # dim of T_1 cap {matrices supported on mask}
    M=T[:,~mask.ravel()]; s=np.linalg.svd(M,compute_uv=False); return len(T)-int((s>1e-7).sum())
for f in sorted(glob.glob('/tmp/r7_fk24_*.npy')):
    B=np.load(f); X=np.zeros((5,5,5),complex); X[:,1:,:]=B; T=T1(X); out=[]
    m=np.zeros((5,5),bool); m[:,0]=True; out.append(('col0',dim_cap(T,m)))
    for i in range(5):
        m=np.zeros((5,5),bool); m[i,:]=True; out.append(('row%d'%i,dim_cap(T,m)))
    m=np.zeros((5,5),bool); m[3:,:]=True; out.append(('rows34',dim_cap(T,m)))
    m=np.zeros((5,5),bool); m[:,0]=True; m[3:,:]=True; out.append(('col0+rows34',dim_cap(T,m)))
    m=np.zeros((5,5),bool); m[1:,:]=True; out.append(('row0=0',dim_cap(T,m)))
    m=np.zeros((5,5),bool); m[:,0]=True; m[0,:]=True; out.append(('col0+row0',dim_cap(T,m)))
    # projections of T_1: row 0, rows 1,2 outside column 0
    def rk(M): s=np.linalg.svd(M,compute_uv=False); return int((s>1e-7).sum())
    Tm=T.reshape(len(T),5,5)
    print(f.split('/')[-1],'dim T_1 =',len(T),dict(out),' proj row0:',rk(Tm[:,0,:]),' rows1,2 on cols1-4:',rk(Tm[:,1:3,1:].reshape(len(T),-1)),flush=True)
