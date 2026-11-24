# Sanity of (FO-r) on the known level spaces: for every line (row or column) with 4-dim projection, the projection of T_1(L_r) to that
# line must be all of C^5.  Control: for lines with smaller projection the statement is not claimed (printed for information).
import sys, itertools, numpy as np
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/chief'); import core
A=list(sys.argv); sys.argv=[A[0]]
exec(open('/home/kevxhk/work/L-gct-210/stage2/r5_FO2.py').read().split("if __name__=='__main__':")[0])
rg=np.random.default_rng(1)
def rk(M,tol=1e-7):
    s=np.linalg.svd(M,compute_uv=False); return int((s>tol).sum())
for name,sp in core.SP.items():
    L=np.array([np.array(m,dtype=complex) for m in sp()]); d=len(L)
    for tr,Lt in (('row',L),('col',L.transpose(0,2,1))):
        for r in range(5):
            pr=rk(Lt[:,r,:])
            u,s,vh=np.linalg.svd(Lt[:,r,:]); coef=u[:,pr:].conj().T; Lr=np.tensordot(coef,Lt,axes=1)       # elements with zero line r
            if len(Lr)==0: continue
            Mb=Lr.reshape(len(Lr),25); rows=[cof55(np.ones((5,5))+((rg.normal(size=len(Lr))+1j*rg.normal(size=len(Lr)))@Mb).reshape(5,5)) for _ in range(70)]
            u2,s2,vh2=np.linalg.svd(np.array(rows)); rr=int((s2>1e-8*s2[0]).sum()); T=vh2[rr:].conj(); proj=rk(T.reshape(len(T),5,5)[:,r,:])
            if pr==4: print('%-11s %s %d: projection of L has dim 4, dim L_r = %d, dim T_1(L_r) = %2d, dim of its line-r projection = %d %s'%(name,tr,r,len(Lr),len(T),proj,'OK' if proj==5 else 'VIOLATION'),flush=True)
