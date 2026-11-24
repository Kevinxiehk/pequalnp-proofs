# Robustness of FO2 and (T2) for survivor (S3) (D04 M_B_ii, d = 0): several seeds, exact-rational basis; plus rank profile of T_1.
import sys, numpy as np
A_=list(sys.argv); sys.argv=[A_[0]]
exec(open('/home/kevxhk/work/L-gct-210/stage2/r8_caseB.py').read().split("if __name__=='__main__':")[0])
exec(open('/home/kevxhk/work/L-gct-210/stage2/r5_FO2.py').read().split("if __name__=='__main__':")[0])
exec(open('/home/kevxhk/work/L-gct-210/stage2/r6_T2.py').read().split("if __name__=='__main__':")[0])
def S3(sg):
    B=np.zeros((5,4,5),complex); B[0,0,0]=sg; B[0,1,0]=-1-sg; B[0,3,0]=1
    B[1,2,:]=[-4,1,1,1,1]; B[2,2,:]=[0,1,-1,0,0]; B[3,3,:]=[0,0,0,1,-1]; B[4,3,:]=[0,1,1,-1,-1]; return B
for sg in (0.3+0.4j, 2.0, -3.0+1j):
    B=S3(sg); X=np.zeros((5,5,5),complex); X[:,1:,:]=B
    res=[]
    for seed in (11,12,13):
        rg=np.random.default_rng(seed); res.append(FO2(X,rg,npts=120,nm=6)); 
    t2=[T2test(B,np.random.default_rng(s))[1] for s in (21,22)]
    print('sg=%s  FO2 runs %s   T2 distances %s  level err %.1e'%(sg,res,['%.2f'%x for x in t2],check(B,np.random.default_rng(1))),flush=True)
