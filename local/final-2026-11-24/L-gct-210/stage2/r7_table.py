# Table of all saved candidates for L_r: (FO-r) projection, FO2 bound, (T2) distance, single-row/column dims. ALIVE = passes all three.
import sys, glob, numpy as np
A=list(sys.argv); sys.argv=[A[0]]
exec(open('/home/kevxhk/work/L-gct-210/stage2/r5_FO2.py').read().split("if __name__=='__main__':")[0])
exec(open('/home/kevxhk/work/L-gct-210/stage2/r6_T2.py').read().split("if __name__=='__main__':")[0])
rg=np.random.default_rng(1)
def rk(M):
    s=np.linalg.svd(M,compute_uv=False); return int((s>1e-7).sum())
def row(name,B):
    X=np.zeros((len(B),5,5),complex); X[:,1:,:]=B; Mb=X.reshape(len(X),25)
    rows=[cof55(np.ones((5,5))+((rg.normal(size=len(X))+1j*rg.normal(size=len(X)))@Mb).reshape(5,5)) for _ in range(70)]
    u,s,vh=np.linalg.svd(np.array(rows)); r=int((s>1e-8*s[0]).sum()); T=vh[r:].conj(); pr=rk(T.reshape(len(T),5,5)[:,0,:])
    n,rho,bd=FO2(X,rg); nt,err=T2test(B,rg)
    zr=max(len(B)-rk(np.delete(B,i,axis=1).reshape(len(B),-1)) for i in range(4)); zc=max(len(B)-rk(np.delete(B,j,axis=2).reshape(len(B),-1)) for j in range(5))
    alive=(pr==5 and bd>=9 and err<1e-8)
    print('%-22s z=%d z\'=%d | T_1 %2d, row proj %d | FO2 %d | (T2) %.0e | %s'%(name,zr,zc,len(T),pr,bd,err,'ALIVE' if alive else 'dead'),flush=True)
for f in sorted(glob.glob('/tmp/r5_Lr3_1_[12].npy')+glob.glob('/tmp/r6_census_*.npy')+glob.glob('/tmp/r6_fk_*.npy')+glob.glob('/tmp/r7_fk24_*.npy')):
    row(f.split('/')[-1],np.load(f))
def cross(a,b):
    Cst=np.array([[1,1,1,1,0,0,0,0],[0,0,0,0,1,1,1,1],[b,0,0,0]+list(a)],dtype=complex); u,s,vh=np.linalg.svd(Cst); out=[]
    for v in vh[3:].conj():
        M=np.zeros((4,5),complex); M[:,0]=v[:4]; M[0,1:]=v[4:]; out.append(M)
    return np.array(out)
for a,b,lab in (((1,2,3,5),1,'cross b=1'),((1,2,3,5),0,'cross b=0'),((1,1,1,1),1,'cross a in C1')):
    row(lab,cross(a,b))
