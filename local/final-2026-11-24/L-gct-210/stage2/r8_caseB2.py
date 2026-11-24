# Validate the reduced criterion [CRIT] (quadrics only) against the T_1 tool, and scan special members of Case B (B1).
#  (0,v) in Omega  <=>  exists e, x, y:  g_e = 0 on Y_0  and  4 E_v + s (P_e+Q_e) - 2 p_0 Q_e - 2 q_0 P_e = s (x a + y b) on Y_0,
#  g_e = sum_j e_j (2 p_j q_j - a q_j - b p_j),  E_v = 2 sum_j v_j p_j q_j + (1-mu) a (2 P_v + Q_v) + (1+mu) b (P_v + 2 Q_v).
import sys, itertools, numpy as np
A_=list(sys.argv); sys.argv=[A_[0]]
exec(open('/home/kevxhk/work/L-gct-210/stage2/r8_caseB.py').read().split("if __name__=='__main__':")[0])
sys.argv=A_
def crit2(mu,Y0,rg,tol=1e-9):
    P=np.array([y[0] for y in Y0]); Q=np.array([y[1] for y in Y0]); pts=rg.normal(size=(40,4))+1j*rg.normal(size=(40,4))
    p=pts@P; q=pts@Q; a=p.sum(1); b=q.sum(1); s=(1-mu)*a+(1+mu)*b; p0=-a-(1+mu)*b; q0=(mu-1)*a-b
    n=len(pts); S=np.zeros((2*n,10),complex)
    for j in range(4):
        S[:n,4+j]=2*p[:,j]*q[:,j]-a*q[:,j]-b*p[:,j]                                   # g_e
        S[n:,j]=4*(2*p[:,j]*q[:,j]+(1-mu)*a*(2*p[:,j]+q[:,j])+(1+mu)*b*(p[:,j]+2*q[:,j]))  # 4 E_v
        S[n:,4+j]=s*(p[:,j]+q[:,j])-2*p0*q[:,j]-2*q0*p[:,j]
    S[n:,8]=-s*a; S[n:,9]=-s*b
    r=lambda M: int((np.linalg.svd(M,compute_uv=False)>tol*np.linalg.svd(M,compute_uv=False)[0]).sum())
    dimE0=4-r(S[:n,4:8])
    return 1+(10-r(S))-(6-r(S[:,4:])), dimE0
if __name__=='__main__':
    rg=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 1)
    cn=lambda *sh: rg.normal(size=sh)+1j*rg.normal(size=sh)
    def run(name,mu,Ap,W):
        Y0=buildY0(np.array(Ap,complex),np.array(W,complex)); B=buildX(mu,Y0)
        rows=[rk(B[:,i,:]) for i in range(4)]; cols=[rk(B[:,:,j]) for j in range(5)]
        X=np.zeros((len(B),5,5),complex); X[:,1:,:]=B; T=T1(X); pr=rk(T.reshape(len(T),5,5)[:,0,:])
        c1=crit(mu,Y0,rg)[0]; c2,dE=crit2(mu,Y0,rg)
        print('%-36s err %.0e rows %s cols %s | dim Omega: T_1 tool %d, D_0 form %d, [CRIT] %d (dim E_0=%d, dim T_1=%d) %s'%(name,check(B,rg),rows,cols,pr,c1,c2,dE,len(T),'' if pr==c1==c2 else '  <-- MISMATCH'),flush=True)
    perp=lambda n: np.linalg.svd(np.array(n,complex)[None,:])[2][1:].conj()
    Z3=np.zeros((3,3))
    run('S2 random, mu random',cn(),cn(2,4),np.zeros((2,2)))
    run('S3s random n, mu=-1',-1,perp(cn(4)),Z3)
    for n in ([2,2,2,5],[2,2,5,5],[1,1,1,3],[1,1,0,4],[1,1,2,2],[1,1,1.5,2.5],[1,1,1,1.0001],[1,-1,2,5],[0,0,1,2],[0,1,1,1],[0,0,0,1],[1,1,-1,-1],[1,2,3,-6]):
        run('S3s n=%s mu=-1'%n,-1,perp(n),Z3)
    for n in ([2,2,2,5],[1,1,1,3],[1,1,2,2]):
        run('S3s n=%s mu=0.3 (iii fails)'%n,0.3,perp(n),Z3)
    for al in ([2,2,2,5],[1,1,1,3],[1,1,2,2],[1,0,0,0],[1,1,0,0]):
        run('S1 alpha=%s mu=1'%al,1,np.array([al],float),np.zeros((1,1)))
    for Ap in ([[1,0,0,0],[0,1,0,0]],[[1,1,0,0],[0,0,1,1]],[[1,-1,0,0],[0,0,1,2]],[[1,0,0,1],[0,1,0,1]],[[1,1,1,0],[0,0,0,1]],[[1,2,0,0],[0,0,1,0]]):
        for mu in (0,1,-1,0.37):
            run('S2 A=%s mu=%s'%(Ap,mu),mu,np.array(Ap,float),np.zeros((2,2)))
