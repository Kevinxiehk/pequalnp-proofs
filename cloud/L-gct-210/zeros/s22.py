# structured LM: strongly level 4x5 L' = span(Y(u),Y(p)) + N, N 2-dim DC, S = s(L') = u^perp degenerate
import numpy as np, itertools, sys
from scipy.optimize import least_squares
seed=int(sys.argv[1]); ntr=int(sys.argv[2]); degen=int(sys.argv[3]) if len(sys.argv)>3 else 1
rng=np.random.default_rng(seed); NS=70
f=np.linalg.qr(np.array([[1,-1,0,0],[0,1,-1,0],[0,0,1,-1]],float).T)[0]  # 4x3 orthonormal basis of V4
# DC 4x5 basis (12)
dc=[]
for i in range(3):
    for j in range(4):
        t=np.zeros((4,5)); t[i,j]=1; t[i,4]-=1; t[3,j]-=1; t[3,4]+=1; dc.append(t.ravel())
dc=np.linalg.qr(np.array(dc).T)[0].T  # 12 x 20
Qn,_=np.linalg.qr(rng.normal(size=(12,12))+1j*rng.normal(size=(12,12)))
S=rng.normal(size=(NS,4))+1j*rng.normal(size=(NS,4))
P4=list(itertools.permutations(range(4)))
def e2(v): s=v.sum(-1); return (s*s-(v*v).sum(-1))/2
def e3(v): s=v.sum(-1); p2=(v*v).sum(-1); p3=(v**3).sum(-1); return (s**3-3*s*p2+2*p3)/6
def build(z):
    t=z[0]; X1=z[1:13]; X2=z[13:25]; C=z[25:45].reshape(2,10)
    if degen:
        u=(1-t*t)*f[:,0]+1j*(1+t*t)*f[:,1]+2*t*f[:,2]
        # p: vector perp u, independent: solve in span(f): take q=f[:,0] - (f0.u)/(w.u) * w with w chosen
        w=f[:,2]; q=f[:,0]-(f[:,0]@u)/(w@u)*w
        s1,s2=u,q
    else:
        s1=f[:,0]+t*f[:,1]; s2=f[:,2]
    Y1=np.zeros((4,5),complex); Y1[:,0]=s1; Y2=np.zeros((4,5),complex); Y2[:,0]=s2
    Y1=Y1.ravel()+X1@dc; Y2=Y2.ravel()+X2@dc
    Nb=np.hstack([np.eye(2),C])@Qn@dc
    return np.vstack([Y1,Y2,Nb])
def resz(z):
    B=build(z); Y=(S@B).reshape(-1,4,5); out=[]
    for j in range(5):
        Z=np.delete(Y,j,axis=2); out+= [e2(Z).sum(-1), e3(Z).sum(-1), sum(Z[:,0,p[0]]*Z[:,1,p[1]]*Z[:,2,p[2]]*Z[:,3,p[3]] for p in P4)]
    return np.concatenate(out)
def res(x):
    z=x[:45]+1j*x[45:]; r=resz(z); return np.concatenate([r.real,r.imag])
for tr in range(ntr):
    x0=rng.normal(size=90)*0.6
    sol=least_squares(res,x0,method='lm',max_nfev=8000,xtol=1e-15,ftol=1e-15,gtol=1e-15)
    z=sol.x[:45]+1j*sol.x[45:]; B=build(z); sv=np.linalg.svd(B,compute_uv=False)
    print('seed',seed,'tr',tr,'degen',degen,'cost %.2e'%sol.cost,'sv',np.round(sv,3),flush=True)
