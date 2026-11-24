# Round 15: numerical exploration of SHAPE S2: Y = a (x) (1,1,1,1,-2) + b2 (x) (e_2 - e_4) + b3 (x) (e_3 - e_4), b_k = be_k w(tau_k), a in V.
# Line conditions (defect of t Y in C m0). Find solutions, local dimension (Jacobian rank), p_3(b_k), and relations between tau_2, tau_3.
import numpy as np, itertools, sys
seed,NS=int(sys.argv[1]),int(sys.argv[2]); HB=sys.argv[3] if len(sys.argv)>3 else ''; rg=np.random.default_rng(seed); I=1j
chi=[np.array([I**(k*r) for r in range(4)]) for k in range(4)]
w=lambda t: chi[1]+2*t*chi[2]-2*t*t*chi[3]
P4=list(itertools.permutations(range(4)))
def perm4(M): return sum(np.prod([M[r,p[r]] for r in range(4)]) for p in P4)
TS=np.array([0.31,0.77,-0.53,1.13,-0.91])
def Ymat(x):
    a=x[0]*chi[1]+x[1]*chi[2]+x[2]*chi[3]; b2=x[3]*w(x[4]); b3=x[5]*w(x[6])
    return np.outer(a,[1,1,1,1,-2])+np.outer(b2,[0,0,1,0,-1])+np.outer(b3,[0,0,0,1,-1])
def F(x):
    Y=Ymat(x); out=[]
    for t in TS:
        C=np.array([perm4(np.ones((4,4))+t*np.delete(Y,j,axis=1)) for j in range(5)])
        out+=[C[1]-C[0],C[2]-C[0],C[3]-C[0],C[4]+4*C[0]-120]
    out.append(np.array([0.3,-0.2,0.7])@x[:3]-1)                  # normalisation of the scale
    if '2' in HB: out.append(x[7]*x[3]-1)
    if '3' in HB: out.append(x[8 if '2' in HB else 7]*x[5]-1)
    return np.array(out)
def J(x,h=1e-7):
    f0=F(x); Jm=np.empty((len(f0),len(x)),complex)
    for i in range(len(x)):
        d=np.zeros(len(x),complex); d[i]=h; Jm[:,i]=(F(x+d)-f0)/h
    return f0,Jm
def lm(x,it=300):
    lam=1e-3; f,Jm=J(x); nf=np.linalg.norm(f)
    for _ in range(it):
        A=Jm.conj().T@Jm; g=Jm.conj().T@f; ok=False
        for _ in range(10):
            d=np.linalg.solve(A+lam*np.eye(len(x)),g); n2=np.linalg.norm(F(x-d))
            if n2<nf: x=x-d; lam=max(lam/4,1e-15); ok=True; break
            lam*=4
        if not ok: break
        f,Jm=J(x); nf=np.linalg.norm(f)
        if nf<1e-13: break
    return x,nf
for st in range(NS):
    x,nf=lm(rg.normal(size=7+len(HB))+1j*rg.normal(size=7+len(HB)))
    if nf<1e-10:
        Jm=J(x)[1][:21,:7]; rk=np.linalg.matrix_rank(Jm,1e-7*np.abs(Jm).max())
        b2=x[3]*w(x[4]); b3=x[5]*w(x[6])
        print('sol: res %.0e localdim<=%d  tau2 %s tau3 %s  |p3(b2)| %.1e |p3(b3)| %.1e  be2 %.2e be3 %.2e'%(nf,7-rk,np.round(x[4],4),np.round(x[6],4),abs(np.sum(b2**3))/np.linalg.norm(b2)**3,abs(np.sum(b3**3))/np.linalg.norm(b3)**3,abs(x[3]),abs(x[5])),flush=True)
    else: print('start %d res %.1e'%(st,nf),flush=True)
