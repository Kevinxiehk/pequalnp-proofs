# Sanity check of LEMMA N0-W on Case-B points NOT built from the (N0) patterns: compute V_Omega (row-r projection of T_1 minus e_0) and
# test sum_j v_j p_j q_j = 0 on W = X cap {column 0 = 0, a = b = 0} for every v in V_Omega (should be ~0), and for a v NOT in V_Omega (control).
import sys, numpy as np
A_=list(sys.argv); sys.argv=[A_[0]]
exec(open('/home/kevxhk/work/L-gct-210/stage2/r8_caseB.py').read().split("if __name__=='__main__':")[0])
rg=np.random.default_rng(9)
def nulls(M,tol=1e-9):
    u,s,vh=np.linalg.svd(M); r=int((s>tol*max(s[0],1e-300)).sum()); return vh[r:].conj()
def test(name,mu,Ap,W):
    Y0=buildY0(np.array(Ap,complex),np.array(W,complex)); B=buildX(mu,Y0)
    X=np.zeros((5,5,5),complex); X[:,1:,:]=B; T=T1(X).reshape(-1,5,5)
    R0=T[:,0,:]                                         # row-0 parts of T_1 (rows of a spanning set)
    u,s,vh=np.linalg.svd(R0); r=int((s>1e-7).sum()); Om=vh[:r]   # basis of Omega (complex-conj conventions irrelevant for membership tests below)
    Om=(u[:, :r].conj().T@R0)                           # rows spanning Omega exactly
    # W: coefficients c with column 0 = 0 and a = b = 0
    cons=[B[:,i,0] for i in range(4)]+[B[:,2,1:].sum(1),B[:,3,1:].sum(1)]
    Wc=nulls(np.array(cons))
    worst_in=0; 
    for om in Om:
        v=om[1:]-om[0]*0                                  # Omega contains e_0; take the columns 1..4 part
        for _ in range(5):
            c=(rg.normal(size=len(Wc))+1j*rg.normal(size=len(Wc)))@Wc; xi=np.tensordot(c,B,axes=1)
            worst_in=max(worst_in,abs((v*xi[2,1:]*xi[3,1:]).sum())/max(1e-300,np.abs(xi).max()**2))
    # control: e_1 if not in Omega
    M=np.vstack([Om,np.eye(5)[1]]); inO=np.linalg.matrix_rank(M,tol=1e-7)==r
    ctl=0
    for _ in range(5):
        c=(rg.normal(size=len(Wc))+1j*rg.normal(size=len(Wc)))@Wc; xi=np.tensordot(c,B,axes=1)
        ctl=max(ctl,abs(xi[2,1]*xi[3,1])/max(1e-300,np.abs(xi).max()**2))
    print('%-34s dim Omega %d dim W %d  max|sum v_j p_j q_j| on W over v in Omega: %.1e   control p_1 q_1 (e_1 in Omega: %s): %.1e'%(name,r,len(Wc),worst_in,inO,ctl),flush=True)
test('S2 A=[[1,-1,0,0],[0,0,1,2]] mu=-1',-1,[[1,-1,0,0],[0,0,1,2]],np.zeros((2,2)))
test('S2 A=[[1,1,0,0],[0,0,1,1]] mu=0',0,[[1,1,0,0],[0,0,1,1]],np.zeros((2,2)))
test('S2 A=[[1,1,1,0],[0,0,0,1]] mu=-1',-1,[[1,1,1,0],[0,0,0,1]],np.zeros((2,2)))
test('S3s n=(0,1,1,1) mu=-1',-1,np.linalg.svd(np.array([[0,1,1,1.]]))[2][1:],np.zeros((3,3)))
test('S1 alpha=(1,0,0,0) mu=1',1,[[1,0,0,0]],np.zeros((1,1)))
