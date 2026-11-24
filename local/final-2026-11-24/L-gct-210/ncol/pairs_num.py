# numerical enumeration of product pairs (W_a, W_b) in Gr(2,5) chart (01,01): e_3|W_a = e_3|W_b = 0, B(W_a, W_b) = 0 (12 eq, 12 unknowns)
import numpy as np, itertools, sys, time
rng=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 0)
def basis(t):
    u1=np.array([1,0,t[0],t[1],t[2]],complex); u2=np.array([0,1,t[3],t[4],t[5]],complex); return u1,u2
def E3(x,y,z): # polarized e3 (symmetric trilinear) with E3(x,x,x) = e3(x)
    s=0
    for i,j,k in itertools.permutations(range(5),3): s+=x[i]*y[j]*z[k]
    return s/6
def F(t):
    a1,a2=basis(t[:6]); b1,b2=basis(t[6:])
    r=[E3(a1,a1,a1),E3(a1,a1,a2),E3(a1,a2,a2),E3(a2,a2,a2),E3(b1,b1,b1),E3(b1,b1,b2),E3(b1,b2,b2),E3(b2,b2,b2)]
    B=lambda a,b: a@b-a.sum()*b.sum()
    r+=[B(a1,b1),B(a1,b2),B(a2,b1),B(a2,b2)]
    return np.array(r)
def J(t,h=1e-7):
    f=F(t); M=np.zeros((12,12),complex)
    for k in range(12):
        d=np.zeros(12,complex); d[k]=h; M[:,k]=(F(t+d)-f)/h
    return M
sols=[]; t0=time.time(); N=int(sys.argv[2]) if len(sys.argv)>2 else 300
for trial in range(N):
    t=(rng.normal(size=12)+1j*rng.normal(size=12))
    for it in range(80):
        f=F(t)
        if np.linalg.norm(f)<1e-13: break
        try: dt=np.linalg.lstsq(J(t),-f,rcond=None)[0]
        except Exception: break
        lam=1.0
        while lam>1e-4 and np.linalg.norm(F(t+lam*dt))>np.linalg.norm(f): lam/=2
        t=t+lam*dt
        if np.abs(t).max()>1e6: break
    if np.linalg.norm(F(t))<1e-10 and np.abs(t).max()<1e5:
        if not any(np.linalg.norm(t-s)<1e-6 for s in sols): sols.append(t)
np.save('pairs_sols_%s.npy'%(sys.argv[1] if len(sys.argv)>1 else '0'),np.array(sols))
print('distinct solutions found:',len(sols),' trials',N,' t=%.0f'%(time.time()-t0))
