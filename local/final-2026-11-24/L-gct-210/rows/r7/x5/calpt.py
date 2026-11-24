# find a numerical point of the X5 calibration (K + C Z(1,r): a (4,1)-type space of kernel type (2,2,1)) and save its basis for oracle.py
import numpy as np, itertools, sys
H=np.array([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]],dtype=complex)
P4=list(itertools.permutations(range(4)))
def perm(M): return sum(np.prod([M[i,p[i]] for i in range(4)]) for p in P4)
def C(Y):
    J=np.ones((4,5)); return np.array([perm((J+Y)[:,[c for c in range(5) if c!=j]])-24 for j in range(5)])
def build(u):
    a1,b1,mb,md,r=u; a2=b2=1
    nW=np.array([a1**2-a2**2,1j*(a1**2+a2**2),2*a1*a2]); pW=np.array([b1**2-b2**2,1j*(b1**2+b2**2),2*b1*b2])
    vW=np.cross(nW,pW); n4=H@nW; p4=H@pW; v4=H@vW
    lam=(1+mb)/(1-mb); mu=1/lam; kc=np.sqrt(4/3*(v4@v4)); m=np.array([1,mb,0,md,-1-mb-md])
    K1=np.outer(v4,[0,0,1,0,0]); K2=np.outer(n4,[1-lam,1+lam,0,0,0]); K3=np.outer(p4,[1-mu,1+mu,0,0,0])
    ph,et=1.0,r; A=kc*ph/4+ph*v4+et*n4; Z=np.outer(A,m); t=(lam-1)*et; Z[:,0]+=t*n4; Z[:,1]-=t*n4
    return np.array([K1,K2,K3,Z]),m
rng=np.random.default_rng(int(sys.argv[1]))
X=[rng.normal(size=4)+1j*rng.normal(size=4) for _ in range(12)]
SS=np.array([0.4,0.8,-0.6,1.1]); VM=np.linalg.inv(np.array([[s**k for k in range(1,5)] for s in SS]))
def res(u):
    B,m=build(u); out=[]
    for x in X:
        Y=np.tensordot(x,B,1); co=VM@np.array([C(s*Y) for s in SS])
        for k in (2,3): out.extend(co[k][1:]-co[k][0]*m[1:])
    return np.array(out)
best=None
for st in range(int(sys.argv[2])):
    u=rng.normal(size=5)+1j*rng.normal(size=5); lam_=1e-3; f=res(u); nf=np.linalg.norm(f)
    for it in range(80):
        if nf<1e-11: break
        Jm=np.zeros((len(f),5),dtype=complex)
        for k in range(5):
            e=np.zeros(5,dtype=complex); e[k]=1e-7; Jm[:,k]=(res(u+e)-f)/1e-7
        dx=np.linalg.solve(Jm.conj().T@Jm+lam_*np.eye(5),-Jm.conj().T@f); f2=res(u+dx)
        if np.linalg.norm(f2)<nf: u=u+dx; f=f2; nf=np.linalg.norm(f2); lam_=max(lam_/3,1e-12)
        else: lam_*=4
    B,m=build(u); nn=np.sum(H@np.array([u[0]**2-1,1j*(u[0]**2+1),2*u[0]])*(H@np.array([u[1]**2-1,1j*(u[1]**2+1),2*u[1]])))
    print('start %d res %.2e  <n,n2>=%.3g  m=%s'%(st,nf,abs(nn),np.round(m,4)),flush=True)
    if nf<1e-10 and abs(nn)>1e-3:
        np.save('x5cal_point_%d.npy'%st,B); print('saved x5cal_point_%d.npy'%st); break
