# PROP families of Case B (NOTES-stage2 R10-2): numerical Omega / FO2 / (T2) / single-row & single-column dims.
#  D04-PROP:  X = C kappa'(sg) + e_3 (x) span{(-4;1'), (0;A)} + e_4 (x) (0; A^perp cap 1^perp),  kappa' = (sg,-1-sg,0,1) in column 0
#  D003-PROP: X = span(kappa0, kappa_l) + e_3 (x) (0;A) + e_4 (x) (0; A^perp cap 1^perp), kappa0 = (0,0,1,-1), kappa_l = (l1,l2,0,-l1-l2)
import sys, numpy as np
A_=list(sys.argv); sys.argv=[A_[0]]
exec(open('/home/kevxhk/work/L-gct-210/stage2/r8_caseB.py').read().split("if __name__=='__main__':")[0])
exec(open('/home/kevxhk/work/L-gct-210/stage2/r5_FO2.py').read().split("if __name__=='__main__':")[0])
exec(open('/home/kevxhk/work/L-gct-210/stage2/r6_T2.py').read().split("if __name__=='__main__':")[0])
rg=np.random.default_rng(int(A_[1]) if len(A_)>1 else 3)
one=np.ones(4)
def perp(vs):
    M=np.vstack([one]+list(vs)); u,s,vh=np.linalg.svd(M); r=int((s>1e-10).sum()); return vh[r:].conj()
def zd(B):
    z=[];zc=[]
    for i in range(4):
        mask=np.ones((4,5),bool); mask[i,:]=False; z.append(len(B)-rk(B[:,mask].T))
    for j in range(5):
        mask=np.ones((4,5),bool); mask[:,j]=False; zc.append(len(B)-rk(B[:,mask].T))
    return z,zc
def rowvec(i,v):
    M=np.zeros((4,5),complex); M[i]=v; return M
def run(name,B):
    X=np.zeros((len(B),5,5),complex); X[:,1:,:]=B; T=T1(X); pr=rk(T.reshape(len(T),5,5)[:,0,:]); n,r,bd=FO2(X,rg); t2=T2test(B,rg)[1]
    z,zc=zd(B)
    print('%-38s err %.0e dim %d rows %s z %s zcol %s dimT1 %d Omega %d FO2 (%d,%d,%d) T2 %.1e'%(name,check(B,rg),rk(B.reshape(len(B),-1)),[rk(B[:,i,:]) for i in range(4)],z,zc,len(T),pr,n,r,bd,t2),flush=True)
def D04P(Abasis,sg):
    B=[np.zeros((4,5),complex)]; B[0][0,0]=sg; B[0][1,0]=-1-sg; B[0][3,0]=1
    B.append(rowvec(2,np.r_[-4,one]))
    for a in Abasis: B.append(rowvec(2,np.r_[0,a]))
    for w in perp(Abasis): B.append(rowvec(3,np.r_[0,w]))
    return np.array(B)
def D003P(Abasis,l1,l2):
    B=[np.zeros((4,5),complex),np.zeros((4,5),complex)]; B[0][2,0]=1; B[0][3,0]=-1; B[1][0,0]=l1; B[1][1,0]=l2; B[1][3,0]=-l1-l2
    for a in Abasis: B.append(rowvec(2,np.r_[0,a]))
    for w in perp(Abasis): B.append(rowvec(3,np.r_[0,w]))
    return np.array(B)
P=perp([])          # basis of 1^perp
for t in range(2 if not (len(A_)>2 and A_[2]=='more') else 0):
    a1=rg.normal(size=3)@P; a2=rg.normal(size=3)@P; sg=rg.normal()+1j*rg.normal()
    run('D04-PROP dimA=1 random',D04P([a1],sg))
    run('D04-PROP dimA=2 random (z=3)',D04P([a1,a2],sg))
    run('D003-PROP dimA=1 random l',D003P([a1],1.0,rg.normal()+1j*rg.normal()))
    run('D003-PROP dimA=2 random l',D003P([a1,a2],1.0,rg.normal()+1j*rg.normal()))
if not (len(A_)>2 and A_[2]=='more'): run('D003-PROP dimA=1, l=(1,0)',D003P([np.array([1,-1,0,0.])],1.0,0.0))
if not (len(A_)>2 and A_[2]=='more'): run('D003-PROP dimA=1, l=(1,-1) (Case A)',D003P([np.array([1,-1,0,0.])],1.0,-1.0))
if len(A_)>2 and A_[2]=='more':
    for t in range(2):
        a1=rg.normal(size=3)@P; a2=rg.normal(size=3)@P
        run('D003-PROP dimA=1 random A, l=(1,0)',D003P([a1],1.0,0.0))
        run('D003-PROP dimA=1 random A, l=(1,-1)',D003P([a1],1.0,-1.0))
        run('D003-PROP dimA=2 random A, l=(1,0)',D003P([a1,a2],1.0,0.0))
        run('D003-PROP dimA=2 random A, l=(1,-1)',D003P([a1,a2],1.0,-1.0))
        run('D04-PROP dimA=1 random A, sg=0 (row1=0)',D04P([a1],0.0))
        run('D04-PROP dimA=1 random A, sg=-1 (row2=0)',D04P([a1],-1.0))
    np.save('/home/kevxhk/work/L-gct-210/stage2/r9/cand_D003P_l10.npy',D003P([np.array([1,-1,0,0.])],1.0,0.0))
    np.save('/home/kevxhk/work/L-gct-210/stage2/r9/cand_D003P_l1m1.npy',D003P([np.array([1,-1,0,0.])],1.0,-1.0))
    a1=rg.normal(size=3)@P; np.save('/home/kevxhk/work/L-gct-210/stage2/r9/cand_D003P_l10_randA.npy',D003P([a1],1.0,0.0))
