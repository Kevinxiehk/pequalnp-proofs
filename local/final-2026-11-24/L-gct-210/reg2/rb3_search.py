# Round 11, target 1: numerical search for 6-dim level spaces containing a 3-dim ROW BLOCK  {e_3 w + e_0 B w : w in W}, W (3-dim) inside 1^perp,
# with rank B = 3 (mode 'r3': det(c R) = 1 for a random 4x3 R) -- versus the calibration mode 'r2' (w_1 in ker B: u_1 = 0, block = kernel line
# + 2-dim part).  Rows: r = 3 (x), j = 0 (y = B x), k = 1, l = 2.  M = <X_1,X_2,X_3, Z_1,Z_2,Z_3>, Z rows 0..2 free, z_3 in span(1, f_4).
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from ext6 import F45
mode=sys.argv[1]; seed=int(sys.argv[2]); nst=int(sys.argv[3])
rg=np.random.default_rng(seed)
f=np.array([[1 if c==i else (-1 if c==4 else 0) for c in range(5)] for i in range(4)],float)   # f_1..f_4 basis of 1^perp
NA=3; NC=12; NZ=17; N=NA+NC+3*NZ
def unpack(x):
    a=x[:NA]; c=x[NA:NA+NC].reshape(3,4); z=x[NA+NC:].reshape(3,NZ); return a,c,z
def build(x):
    a,c,z=unpack(x); El=[]
    for i in range(3):
        w=f[i]+a[i]*f[3]; u=c[i]@f
        E=np.zeros((4,5),complex); E[3]=w; E[0]=u; El.append(E)
    for m in range(3):
        E=np.zeros((4,5),complex); E[0]=z[m,0:5]; E[1]=z[m,5:10]; E[2]=z[m,10:15]; E[3]=z[m,15]*np.ones(5)+z[m,16]*f[3]; El.append(E)
    return np.array(El)
Cmb=rg.normal(size=(200,6))+1j*rg.normal(size=(200,6)); Lz=rg.normal(size=(3,NZ))+1j*rg.normal(size=(3,NZ)); Rr=rg.normal(size=(4,3))
def res(x):
    a,c,z=unpack(x); El=build(x); r=list(F45(np.einsum('nk,kij->nij',Cmb,El))-120)
    nz=(Lz@z.T)-np.eye(3); r+=list(nz.ravel())
    if mode=='r3': r.append(np.linalg.det(c@Rr)-1)
    else: r+=list(c[0])            # u_1 = 0
    return np.array(r)
found=0
for st in range(nst):
    x=rg.normal(size=N)+1j*rg.normal(size=N); rr=res(x); cst=np.linalg.norm(rr)
    for it in range(120):
        J=np.empty((len(rr),N),complex)
        for k in range(N):
            xp=x.copy(); xp[k]+=1e-7; J[:,k]=(res(xp)-rr)/1e-7
        lam=1e-3*np.abs(J).max()
        dx=np.linalg.solve(J.conj().T@J+lam*np.eye(N),-J.conj().T@rr)
        xn=x+dx; rn=res(xn)
        if np.linalg.norm(rn)<cst: x,rr,cst=xn,rn,np.linalg.norm(rn)
        else:
            dx=np.linalg.lstsq(J,-rr,rcond=None)[0]; xn=x+0.3*dx; rn=res(xn)
            if np.linalg.norm(rn)<cst: x,rr,cst=xn,rn,np.linalg.norm(rn)
            else: break
        if cst<1e-10: break
    El=build(x); a,c,z=unpack(x)
    d=np.linalg.matrix_rank(El.reshape(6,20),tol=1e-6); rk=np.linalg.matrix_rank(c,tol=1e-6)
    ok=cst<1e-8 and d==6
    found+=ok
    print('%s start %d: residual %.1e dim %d rank B %d %s'%(mode,st,cst,d,rk,'HIT' if ok else ''),flush=True)
    if ok: np.save('rb3_%s_%d_%d.npy'%(mode,seed,st),El)
print('%s: %d hits / %d starts'%(mode,found,nst))
