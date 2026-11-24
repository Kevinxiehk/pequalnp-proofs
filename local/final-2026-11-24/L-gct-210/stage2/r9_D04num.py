# Numeric builder for the D04 families (same formulas as r9_direct.py) + Omega / FO2 / T2 / single-row dims at given parameters.
import sys, numpy as np
A_=list(sys.argv); sys.argv=[A_[0]]
exec(open('/home/kevxhk/work/L-gct-210/stage2/r8_caseB.py').read().split("if __name__=='__main__':")[0])
exec(open('/home/kevxhk/work/L-gct-210/stage2/r5_FO2.py').read().split("if __name__=='__main__':")[0])
exec(open('/home/kevxhk/work/L-gct-210/stage2/r6_T2.py').read().split("if __name__=='__main__':")[0])
def D04(pat,cho,case,r1=0,r2=0,F0=0,F3=0,sg=0.3):
    Z=np.zeros(4); V=np.array([[1,0,r1,-1-r1],[0,1,r2,-1-r2]],complex)
    w=np.array([-r1*(3+r1+r2)+(1+r1)*(r1+r2-1),-r2*(3+r1+r2)+(1+r2)*(r1+r2-1),3+r1+r2,r1+r2-1],complex); e34=np.array([0,0,1,-1.])
    if pat=='Q0': Wb=[(V[0],Z),(V[1],Z)]; y3=(e34,Z) if cho=='A' else (Z,w)
    elif pat=='P0': Wb=[(Z,V[0]),(Z,V[1])]; y3=(Z,e34) if cho=='A' else (w,Z)
    else: Wb=[(np.array([1,-1,0,0.]),Z),(Z,np.array([0,0,1,-1.]))]; y3=(np.array([-1,-1,1,1.]),Z) if cho=='A' else (Z,np.array([1,1,-1,-1.]))
    Yb=[(np.ones(4),Z)]+Wb+[y3]; ff=[F0,0,0,F3]; aa=[4,0,0,0]; B=[]
    M=np.zeros((4,5),complex)
    if case=='i': M[0,0]=1; M[1,0]=-1
    else: M[0,0]=sg; M[1,0]=-1-sg; M[3,0]=1
    B.append(M)
    for k,(p,q) in enumerate(Yb):
        M=np.zeros((4,5),complex)
        if case=='i': M[0,0]=-ff[k]/2; M[1,0]=-ff[k]/2; M[3,0]=ff[k]
        else: M[0,0]=ff[k]; M[1,0]=-ff[k]
        M[2,0]=-aa[k]; M[2,1:]=p; M[3,1:]=q; B.append(M)
    return np.array(B)
def zd(B):
    z=[]
    for i in range(4):
        mask=np.ones((4,5),bool); mask[i,:]=False; z.append(len(B)-rk(B[:,mask].T))
    return z
def run(name,B,rg=np.random.default_rng(2)):
    X=np.zeros((5,5,5),complex); X[:,1:,:]=B; T=T1(X); pr=rk(T.reshape(len(T),5,5)[:,0,:]); n,r,bd=FO2(X,rg); t2=T2test(B,rg)[1]
    print('%-40s err %.0e dimX %d rows %s z %s dimT1 %d Omega %d FO2 (%d,%d,%d) T2 %.1e'%(name,check(B,rg),rk(B.reshape(5,-1)),[rk(B[:,i,:]) for i in range(4)],zd(B),len(T),pr,n,r,bd,t2),flush=True)
if __name__=='__main__' or True:
    run('P0_B_i r1=r2=-1 f0=f3=2',D04('P0','B','i',-1,-1,2,2))
    run('P0_B_i r1=r2=0 f0=2 f3=-2',D04('P0','B','i',0,0,2,-2))
    run('M_A_i f0=f3=2 (S1, reference)',D04('M','A','i',F0=2,F3=2))
