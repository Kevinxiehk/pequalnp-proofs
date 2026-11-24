# FO2 / T2 / Omega for the (FO-r)-passing loci of the D0-4 families (case ii with d = 0): X = C kappa' + lift(Y), kappa' = (sg,-1-sg,0,1).
import sys, numpy as np
A_=list(sys.argv); sys.argv=[A_[0]]
exec(open('/home/kevxhk/work/L-gct-210/stage2/r8_caseB.py').read().split("if __name__=='__main__':")[0])
exec(open('/home/kevxhk/work/L-gct-210/stage2/r5_FO2.py').read().split("if __name__=='__main__':")[0])
exec(open('/home/kevxhk/work/L-gct-210/stage2/r6_T2.py').read().split("if __name__=='__main__':")[0])
def zdims(B):
    z=[]
    for i in range(4):
        mask=np.ones((4,5),bool); mask[i,:]=False; Mo=B[:,mask].T; z.append(len(B)-rk(Mo))
    zc=[]
    for j in range(5):
        mask=np.ones((4,5),bool); mask[:,j]=False; Mo=B[:,mask].T; zc.append(len(B)-rk(Mo))
    return z,zc
def mkii(Yb,sg,dd):
    B=[]; M=np.zeros((4,5),complex); M[0,0]=sg; M[1,0]=-1-sg; M[3,0]=1; B.append(M)
    for k,(p,q) in enumerate(Yb):
        M=np.zeros((4,5),complex); M[0,0]=dd[k]; M[1,0]=-dd[k]; M[2,0]=-np.sum(p); M[2,1:]=p; M[3,1:]=q; B.append(M)
    return np.array(B)
rg=np.random.default_rng(4); Z=np.zeros(4)
def run(name,B):
    X=np.zeros((5,5,5),complex); X[:,1:,:]=B; T=T1(X); pr=rk(T.reshape(len(T),5,5)[:,0,:]); n,r,bd=FO2(X,rg); t2=T2test(B,rg)
    z,zc=zdims(B)
    print('%-34s err %.0e rows %s z %s zcol %s dimT1 %d Omega %d FO2 (%d,%d,%d) T2 dist %.1e'%(name,check(B,rg),[rk(B[:,i,:]) for i in range(4)],z,zc,len(T),pr,n,r,bd,t2[1]),flush=True)
for cho in ('A','B'):
    Yb=[(np.ones(4),Z),(np.array([1,-1,0,0.]),Z),(Z,np.array([0,0,1,-1.]))]
    Yb.append((np.array([-1,-1,1,1.]),Z) if cho=='A' else (Z,np.array([1,1,-1,-1.])))
    for sg in (0.3+0.4j,-0.5,0.0):
        run('M_%s_ii d=0 sg=%s'%(cho,sg),mkii(Yb,sg,[0,0,0,0]))
