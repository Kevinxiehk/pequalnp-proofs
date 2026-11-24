import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np, glob
from t import *
from a1 import embed
from a5 import rref_tol, onb
from a6 import T1
np.set_printoptions(precision=3,suppress=True,linewidth=200)
rg=np.random.default_rng(3)
fs=sorted(glob.glob('../rows/rc45.npy')+glob.glob('../rows/clm_p4_d6_*.npy')+glob.glob('../rows/nc_d6_*.npy')+glob.glob('../rows/seed_d6_*.npy'))
for f in fs:
    B0=np.load(f); R=rref_tol(onb(B0),1e-5); B=onb(R)
    if level_err(B)>1e-9: B=onb(B0); tag='raw'
    else: tag='lim'
    T=T1(embed(B),rg,tol=1e-6 if tag=='raw' else 1e-8)
    rho=T[:,4,:]; u,s,vh=np.linalg.svd(rho); r=int((s>1e-6).sum()); Om=vh[:r]      # rows span Omega (up to conj; fix below)
    Om=np.array([x for x in vh[:r]])
    # canonical: project 1 out, show remaining vector(s) normalized
    one=np.ones(5)/np.sqrt(5)
    # Omega as column space of rho^T: use rho rows directly
    U,S,Vh=np.linalg.svd(rho.T,full_matrices=False); basis=U[:,:r].T          # rows = basis vectors of Omega (true vectors)
    rest=basis-np.outer(basis@one,one); u2,s2,v2=np.linalg.svd(rest); z=v2[:r-1]
    out=[]
    for v in z:
        v=v/v[np.argmax(abs(v))]; out.append(np.array2string(v,precision=3,suppress_small=True))
    print('%-28s %s dimOmega=%d  Omega cap 1^perp-ish: %s'%(f.split('/')[-1],tag,r,' ; '.join(out)))
