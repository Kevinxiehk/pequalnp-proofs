# local dimension of the solution set of an msolve system (integer coefficients mod P mapped to small integers) at LM solutions
import numpy as np, sys
f=sys.argv[1]; P=int(open(f).read().split('\n')[1]); nst=int(sys.argv[2])
L=open(f).read().split('\n'); names=L[0].split(','); pols=[q.strip() for q in ' '.join(L[2:]).split(',') if q.strip()]
idx={n:i for i,n in enumerate(names)}
def parse(s):
    T=[]
    for term in s.split('+'):
        fs=term.split('*'); c=int(fs[0]); c=c-P if c>P//2 else c; mon=[]
        for x in fs[1:]:
            if '^' in x: b,e=x.split('^'); mon.append((idx[b],int(e)))
            else: mon.append((idx[x],1))
        T.append((c,mon))
    return T
PP=[parse(q) for q in pols]
def F(x): return np.array([sum(c*np.prod([x[i]**e for i,e in mon]) for c,mon in T) for T in PP])
def Jac(x):
    J=np.zeros((len(PP),len(x)),complex)
    for r,T in enumerate(PP):
        for c,mon in T:
            for k,(i,e) in enumerate(mon):
                v=c*e*x[i]**(e-1)
                for k2,(i2,e2) in enumerate(mon):
                    if k2!=k: v*=x[i2]**e2
                J[r,i]+=v
    return J
rng=np.random.default_rng(1)
for st in range(nst):
    x=rng.normal(size=len(names))+1j*rng.normal(size=len(names)); lam=1e-3; fx=F(x); nf=np.linalg.norm(fx)
    for it in range(400):
        if nf<1e-12: break
        J=Jac(x); dx=np.linalg.lstsq(J.conj().T@J+lam*np.eye(len(x)),-J.conj().T@fx,rcond=None)[0]; f2=F(x+dx)
        if np.linalg.norm(f2)<nf: x=x+dx; fx=f2; nf=np.linalg.norm(f2); lam=max(lam/3,1e-14)
        else: lam*=4
    if nf<1e-10:
        sv=np.linalg.svd(Jac(x),compute_uv=False); rk=int(np.sum(sv>1e-8*sv[0]))
        print('solution res %.1e local dim %d (sv around cut: %s)'%(nf,len(x)-rk,np.array2string(sv[max(0,rk-2):rk+2],precision=2)),flush=True)
    else: print('no convergence %.1e'%nf,flush=True)
