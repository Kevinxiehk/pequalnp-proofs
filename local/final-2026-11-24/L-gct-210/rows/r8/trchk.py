import numpy as np, sys
I=np.eye(3)
for pat in ('++++','++--','----'):
    exec(open('deg2_4.py').read().split("cnt={}")[0].replace("seed,nst=int(sys.argv[1]),int(sys.argv[2]); pat=sys.argv[3] if len(sys.argv)>3 else None","seed,nst=3,0"))
    rng=np.random.default_rng(11); got=0
    for st in range(30):
        x=rng.normal(size=27)+1j*rng.normal(size=27); lam=1e-3; f=res(x); nf=np.linalg.norm(f)
        for it in range(300):
            if nf<1e-13: break
            J=np.zeros((len(f),27),complex)
            for k in range(27):
                e=np.zeros(27,complex); e[k]=1e-7; J[:,k]=(res(x+e)-f)/1e-7
            dx=np.linalg.lstsq(J.conj().T@J+lam*np.eye(27),-J.conj().T@f,rcond=None)[0]; f2=res(x+dx)
            if np.linalg.norm(f2)<nf: x=x+dx; f=f2; nf=np.linalg.norm(f2); lam=max(lam/3,1e-14)
            else: lam*=4
        if nf>1e-10: continue
        B=[x[9*k:9*k+9].reshape(3,3) for k in range(3)]; B.append(2*I-sum(B))
        rk=[int(np.sum(np.linalg.svd((I-M)/2,compute_uv=False)>1e-4)) for M in B]
        print(pat,'tr A =',np.round([np.trace((I-M)/2) for M in B],6),' ranks',rk); got+=1
        if got>=3: break
