# Candidates X for L_r passing the first-order test (dim T_1(X) >= 9): is T_1(X) (or a 9-dim subspace of it containing X) a level space?
# For each saved X: basis of T_1(X); level defect of T_1(X); then the set of single directions t in T_1(X)/X with X + C t level
# (second/higher-order conditions), by sampling: residual of perm(J + x + s t) - 120.
import sys, glob, itertools, numpy as np
sys.argv=[sys.argv[0],'1','0','0']
src=open('/home/claude/work/L-gct-210/stage2/r5_Lr.py').read().split("if __name__=='__main__':")[0]
exec(src)
P5=np.array(list(itertools.permutations(range(5))))
def perm5(A): return A[...,np.arange(5)[None,:],P5].prod(axis=-1).sum(axis=-1)
def T1basis(B,npts=80):
    r2=np.random.default_rng(3); rows=[]
    for _ in range(npts):
        c=r2.normal(size=5)+1j*r2.normal(size=5); M=np.ones((5,5),complex); M[1:]+=np.tensordot(c,B,axes=1); rows.append(cof55(M))
    A=np.array(rows); u,s,vh=np.linalg.svd(A); r=int((s>1e-8*s[0]).sum()); return vh[r:].conj()      # rows: basis of the annihilator = T_1
np.set_printoptions(precision=3,suppress=True,linewidth=200)
r3=np.random.default_rng(11)
for f in sorted(glob.glob('/tmp/r5_Lr3_*.npy')):
    B=np.load(f); X=np.zeros((5,5,5),complex); X[:,1:,:]=B; T=T1basis(B); d=len(T)
    # check X inside T_1 and level defect of T_1
    proj=np.linalg.norm(X.reshape(5,25)-(X.reshape(5,25)@T.conj().T)@T)
    def defect(Vb,n=30):
        c=r3.normal(size=(n,len(Vb)))+1j*r3.normal(size=(n,len(Vb))); return abs(perm5(1+np.tensordot(c,Vb.reshape(len(Vb),5,5),axes=1))-120).max()
    print(f.split('/')[-1],' dim T_1 =',d,' X inside T_1 (distance %.1e)'%proj,' level defect of X: %.1e'%defect(X.reshape(5,25)),' level defect of T_1(X): %.2e'%defect(T))
