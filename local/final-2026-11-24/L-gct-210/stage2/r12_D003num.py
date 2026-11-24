# Numeric builder for D003_<Q0|P0>_<A|B>_3 (chart 3) as in r9_direct.py; tests Omega, FO2, single-row dims, FO2-joint (LM) at given params.
import sys, numpy as np
A_=list(sys.argv); sys.argv=[A_[0]]
exec(open('/home/kevxhk/work/L-gct-210/stage2/r8_caseB.py').read().split("if __name__=='__main__':")[0])
exec(open('/home/kevxhk/work/L-gct-210/stage2/r5_FO2.py').read().split("if __name__=='__main__':")[0])
def D003(pat,cho,r1,r2,k1,k2,u1):
    Z4=np.zeros(4); V=np.array([[1,0,r1,-1-r1],[0,1,r2,-1-r2]],complex)
    w=np.array([-r1*(3+r1+r2)+(1+r1)*(r1+r2-1),-r2*(3+r1+r2)+(1+r2)*(r1+r2-1),3+r1+r2,r1+r2-1],complex); e34=np.array([0,0,1,-1.])
    if pat=='Q0': Wb=[(V[0],Z4),(V[1],Z4)]; y3=(e34,Z4) if cho=='A' else (Z4,w)
    else: Wb=[(Z4,V[0]),(Z4,V[1])]; y3=(Z4,e34) if cho=='A' else (w,Z4)
    c1=np.array([1,-1,0,0.]); c2=np.array([-.5,-.5,1,0]); c3=np.array([-.5,-.5,0,1])
    B=[]
    for col in (c1-k1*c3, c2-k2*c3):
        M=np.zeros((4,5),complex); M[:,0]=col; B.append(M)
    for (p,q) in Wb:
        M=np.zeros((4,5),complex); M[2,1:]=p; M[3,1:]=q; B.append(M)
    M=np.zeros((4,5),complex); M[:,0]=u1*c3; M[2,1:]=y3[0]; M[3,1:]=y3[1]; B.append(M)
    return np.array(B)
def zd(B):
    z=[]
    for i in range(4):
        mask=np.ones((4,5),bool); mask[i,:]=False; z.append(len(B)-rk(B[:,mask].T))
    return z
rg=np.random.default_rng(5)
def run(name,B):
    X=np.zeros((5,5,5),complex); X[:,1:,:]=B; T=T1(X); pr=rk(T.reshape(len(T),5,5)[:,0,:]); n,r,bd=FO2(X,rg)
    s12=np.array([B[:,0,0],B[:,1,0]]); prop=rk(s12)<2
    print('%-40s err %.0e dimX %d rows %s z %s s-image dim %d dimT1 %d Omega %d FO2 (%d,%d,%d)'%(name,check(B,rg),rk(B.reshape(len(B),-1)),[rk(B[:,i,:]) for i in range(4)],zd(B),rk(s12),len(T),pr,n,r,bd),flush=True)
    return B
pts=[('pt[7] r=(0,0) k1=0 k2=1/2 u1=-1',(0,0,0,.5,-1)),('pt[2] r=(0,1) k1=0 k2=1/3 u1=0',(0,1,0,1/3,0)),
     ('comp[8] r=(-1/2,-1/2) k random u1=0',(-.5,-.5,0.37+0.2j,-1.3,0)),('comp[8] r=(-1/2,-1/2) k random2 u1=0',(-.5,-.5,-0.7,0.4+0.9j,0))]
for name,p in pts:
    B=D003('Q0','B',*p); run(name,B); np.save('/home/kevxhk/work/L-gct-210/stage2/r9/D003QB3_%s.npy'%name.split()[0].replace('[','').replace(']',''),B)
