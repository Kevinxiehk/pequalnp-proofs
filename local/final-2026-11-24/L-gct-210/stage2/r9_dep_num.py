# Numerical landscape for the open B(dep) sub-cases D0-4 (b = 0, dim Y = 4, (1',0) in Y) and D00 (a = b = 0), with the general T_1 tool.
# Prints dim Omega (row-r projection of T_1(X)); Omega = C^5 needs 5.  Also prints row ranks and single-row/column dims.
import sys, numpy as np
A_=list(sys.argv); sys.argv=[A_[0]]
exec(open('/home/kevxhk/work/L-gct-210/stage2/r8_caseB.py').read().split("if __name__=='__main__':")[0])
rg=np.random.default_rng(int(A_[1]) if len(A_)>1 else 7)
cn=lambda *sh: rg.normal(size=sh)+1j*rg.normal(size=sh)
K=np.ones((4,4))-np.eye(4); Ki=np.linalg.inv(K); one=np.ones(4)
def nullsp(M):
    u,s,vh=np.linalg.svd(np.atleast_2d(M)); r=int((s>1e-10).sum()); return vh[r:].conj()
def maxiso_containing_1(k,Wpar):
    """max isotropic Y (dim 4) of C^4xC^4 for p^T K q' + p'^T K q, containing (1,0); A' = p'(Y) of dim k (contains 1).
       returns list of 4 (p',q') vectors."""
    Ap=[one]+[cn(4) for _ in range(k-1)]; Ap=np.array(Ap)            # basis of A' (first = 1)
    G=Ap@Ap.T; D=np.linalg.solve(G,Ap)                                # dual basis inside span (bilinear)
    Wm=np.zeros((k,k),complex)
    if k==3: Wm[1,2]=Wpar; Wm[2,1]=-Wpar                              # 1 in the kernel of the skew form
    out=[]
    for i in range(k): out.append((Ap[i], Ki@(Wm[i]@D)))
    for n in nullsp(Ap): out.append((np.zeros(4,complex), Ki@n))
    return out
def iso_check(Y):
    return max(abs(p1@K@q2+p2@K@q1) for (p1,q1) in Y for (p2,q2) in Y)
def build(Ylist, col0):
    """Ylist: list of (p',q'); col0: list of (s1,s2,p0,q0) for each; returns (n,4,5) basis"""
    B=[]
    for (p,q),(s1,s2,p0,q0) in zip(Ylist,col0):
        M=np.zeros((4,5),complex); M[0,0]=s1; M[1,0]=s2; M[2,0]=p0; M[2,1:]=p; M[3,0]=q0; M[3,1:]=q; B.append(M)
    return np.array(B)
def summary(name,B):
    rows=[rk(B[:,i,:]) for i in range(4)]; X=np.zeros((len(B),5,5),complex); X[:,1:,:]=B; T=T1(X)
    pr=rk(T.reshape(len(T),5,5)[:,0,:]); e=check(B,rg)
    # single-row parts: dim of {x in X : x supported in row i}
    Bf=B.reshape(len(B),-1); z=[]
    for i in range(4):
        mask=np.ones((4,5),bool); mask[i,:]=False; Mo=B[:,mask].T   # coefficients c with sum c_k B_k zero outside row i
        z.append(len(B)-rk(Mo) if rk(Mo)<len(B) else 0)
    print('%-46s err %.0e dimX %d rows %s z %s dim T_1 %2d dim Omega %d%s'%(name,e,rk(Bf),rows,z,len(T),pr,'   <== 5' if pr==5 else ''),flush=True)
for trial in range(int(A_[2]) if len(A_)>2 else 2):
  # ---- D0-4 case (i): xi_d in X, lift: q0 = phi(y), s1 = s2 = -phi/2, p0 = -a
  for k in (1,2,3):
    for Wp in ([0] if k<3 else [0,cn()]):
        Y=maxiso_containing_1(k,Wp); assert iso_check(Y)<1e-9
        qf=np.array([y[1] for y in Y])                      # q' values on basis
        for phikind in ('in span q', 'generic'):
            if phikind=='in span q': lam=cn(4); phi=qf@lam      # phi = sum lam_j q'_j  (keeps q-row rank <= 3)
            else: phi=cn(4)
            col0=[(-ph/2,-ph/2,-y[0].sum(),ph) for y,ph in zip(Y,phi)]
            B=build([(np.zeros(4),np.zeros(4))]+Y,[(1,-1,0,0)]+col0)
            summary('D0-4(i) k=%d W=%s phi %s'%(k,'0' if Wp==0 else 'gen',phikind),B)
        # ---- case (ii): kappa' = (sig1, -1-sig1, 0, 1), lift q0 = 0, s1 = d, s2 = -d, p0 = -a
        sig=cn(); dv=cn(4)
        col0=[(dd,-dd,-y[0].sum(),0) for y,dd in zip(Y,dv)]
        B=build([(np.zeros(4),np.zeros(4))]+Y,[(sig,-1-sig,0,1)]+col0)
        summary('D0-4(ii) k=%d W=%s'%(k,'0' if Wp==0 else 'gen'),B)
  # ---- D00, dim Y = 2: X = column-0 space (s1+s2+p0+q0 = 0) + Y (2-dim isotropic in 1^perp x 1^perp)
  Pp=nullsp(one[None,:])            # basis of 1^perp (3 x 4)
  for kind in ('generic','Q0','P0','M'):
    if kind=='generic':
        # 2-dim isotropic: y1 random, y2 random in y1^perp (w.r.t. <p,q'>+<p',q>) and isotropic: solve numerically by a quadratic
        y1=(cn(3)@Pp,cn(3)@Pp)
        y1=(y1[0], y1[1]-((y1[0]@y1[1])/(Pp[0]@y1[0]+1e-30))*0)   # adjust: make y1 isotropic: <p,q> = 0
        p1=cn(3)@Pp; q1=cn(3)@Pp; c=(p1@q1); # make <p1,q1>=0 by modifying q1 along a vector u in 1^perp with <p1,u> != 0
        u=Pp[0]; q1=q1-c/(p1@u)*u; y1=(p1,q1)
        # y2 = (p2,q2) with <p1,q2>+<p2,q1> = 0 and <p2,q2> = 0
        p2=cn(3)@Pp; q2=cn(3)@Pp
        # linear condition: adjust q2 along u2 with <p1,u2> != 0
        u2=Pp[1]; q2=q2-((p1@q2+p2@q1)/(p1@u2))*u2
        # isotropy <p2,q2>=0 : move along direction (0,w) with <p1,w>=0, <p2,w>!=0
        W1=nullsp(np.vstack([one,p1])); w=W1[0]; q2=q2-((p2@q2)/(p2@w))*w
        Y=[y1,(p2,q2)]
    elif kind=='Q0': V=cn(2,3)@Pp; Y=[(V[0],np.zeros(4)),(V[1],np.zeros(4))]
    elif kind=='P0': V=cn(2,3)@Pp; Y=[(np.zeros(4),V[0]),(np.zeros(4),V[1])]
    else: Y=[(np.array([1,-1,0,0.]),np.zeros(4)),(np.zeros(4),np.array([0,0,1,-1.]))]
    col=[(1,-1,0,0),(-.5,-.5,1,0),(-.5,-.5,0,1)]
    B=build([(np.zeros(4),np.zeros(4))]*3+Y,col+[(0,0,0,0)]*2)
    summary('D00-2 %s'%kind,B)
  # ---- D00, dim Y = 3: Y max isotropic in 1^perp x 1^perp: Y = {(p, S p) : p in 1^perp}, S skew w.r.t. <,> on 1^perp (generic chart)
  for kind in ('generic','S=0'):
    if kind=='generic':
        Sm=cn(3,3); Gm=Pp@Pp.T; Sm=Sm-Sm.T          # q = sum_k (Sm @ coords) ... skew in the Gram metric
        Y=[]
        for i in range(3):
            p=Pp[i]; coef=np.linalg.solve(Gm,Sm[i]); q=coef@Pp; Y.append((p,q))
    else: Y=[(Pp[i],np.zeros(4)) for i in range(3)]
    if iso_check(Y)>1e-8: print('iso fail',kind,iso_check(Y)); continue
    # kernel: 2-dim subspace of the column-0 space; lift column-0 values generic
    cs=nullsp(np.array([[1,1,1,1.]]))   # basis of {s1+s2+p0+q0=0} (3 x 4)
    ker=cn(2,3)@cs; lift=[cn(3)@cs for _ in range(3)]
    B=build([(np.zeros(4),np.zeros(4))]*2+Y,[tuple(v) for v in ker]+[tuple(v) for v in lift])
    summary('D00-3 %s (kernel, lift generic)'%kind,B)
    ker=np.array([[1,-1,0,0],[0,0,1,-1.]]); lift=[(0,0,0,0)]*3
    B=build([(np.zeros(4),np.zeros(4))]*2+Y,[tuple(v) for v in ker]+lift)
    summary('D00-3 %s (kernel xi_d, p0=-q0; lift 0)'%kind,B)
