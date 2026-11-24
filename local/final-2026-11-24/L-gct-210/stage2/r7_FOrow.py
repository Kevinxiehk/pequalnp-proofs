# Refined first-order test (FO-r): if X = L_r for a row r with 4-dim projection of L, then L lies in T_1(X) and projects ONTO a 4-dim
# space in row r; so dim pi_r(T_1(X)) >= 4 is necessary.  (pi_r(T_1(X)) always contains (C(X) + C1)^perp and the vector 1.)
# Report dim T_1(X), dim pi_r(T_1(X)) and dim(T_1(X) cap {row r = 0}) for all saved candidates and for the cross spaces.
import sys, glob, itertools, numpy as np
A=list(sys.argv); sys.argv=[A[0]]
exec(open('/home/kevxhk/work/L-gct-210/stage2/r5_FO2.py').read().split("if __name__=='__main__':")[0])
rg=np.random.default_rng(1)
def T1(X):
    Mb=X.reshape(len(X),25); rows=[cof55(np.ones((5,5))+((rg.normal(size=len(X))+1j*rg.normal(size=len(X)))@Mb).reshape(5,5)) for _ in range(70)]
    u,s,vh=np.linalg.svd(np.array(rows)); r=int((s>1e-8*s[0]).sum()); return vh[r:].conj()
def rk(M):
    s=np.linalg.svd(M,compute_uv=False); return int((s>1e-7).sum())
def report(name,B):
    X=np.zeros((len(B),5,5),complex); X[:,1:,:]=B; T=T1(X); Tm=T.reshape(len(T),5,5); pr=rk(Tm[:,0,:])
    zr=[len(B)-rk(np.delete(B,i,axis=1).reshape(len(B),-1)) for i in range(4)]; zc=[len(B)-rk(np.delete(B,j,axis=2).reshape(len(B),-1)) for j in range(5)]
    print('%-24s single-row %s single-col %s: dim T_1 = %2d, dim of its row-r projection = %d  -> %s'%(name,zr,zc,len(T),pr,'DEAD at first order' if pr<4 else 'passes'),flush=True)
if __name__=='__main__':
    for f in sorted(glob.glob('/tmp/r5_Lr3_1_[12].npy')+glob.glob('/tmp/r6_census_*.npy')+glob.glob('/tmp/r6_fk_*.npy')+glob.glob('/tmp/r7_fk24_*.npy')):
        report(f.split('/')[-1],np.load(f))
    def cross(a,b):
        Cst=np.array([[1,1,1,1,0,0,0,0],[0,0,0,0,1,1,1,1],[b,0,0,0]+list(a)],dtype=complex); u,s,vh=np.linalg.svd(Cst); out=[]
        for v in vh[3:].conj():
            M=np.zeros((4,5),complex); M[:,0]=v[:4]; M[0,1:]=v[4:]; out.append(M)
        return np.array(out)
    for a,b,lab in (((1,2,3,5),1,'cross (1,2,3,5), b=1'),((1,2,3,5),0,'cross b = 0'),((1,1,1,1),1,'cross a in C1')):
        report(lab,cross(a,b))
