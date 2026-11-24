# EC moves of the Type F line-kernels of ex2, ex3, fam2, s-family (N = part with zero row 3): equal (or proportional) columns of N ?
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/chief')
import numpy as np, itertools
from t import *
from a1 import embed, defect
from a5 import onb
from a6 import T1
from r5_FO2 import FO2
from ecmove import build
import core
np.set_printoptions(precision=3,suppress=True,linewidth=200)
rg=np.random.default_rng(0)
def Lr(B,r):
    m=np.ones((5,5),bool); m[r]=False
    S=sub_supported(B,m); rows=[i for i in range(5) if i!=r]
    return S[:,rows,:]
for name in ('ex2','ex3','fam2','fam.6+1.4i'):
    Bm=np.array([np.array(mm,dtype=complex) for mm in core.SP[name]()]); M=onb(Lr(Bm,4))
    fr=[i for i in range(4) if len(rowpart(M,[i]))==4]
    if not fr: print(name,'no free row'); continue
    i0=fr[0]; mk=np.ones((4,5),bool); mk[i0]=False; N=sub_supported(M,mk)
    # move free row to row 3 by swapping rows i0 and 3
    perm_rows=list(range(4)); perm_rows[i0],perm_rows[3]=perm_rows[3],perm_rows[i0]; N=N[:,perm_rows,:]
    cols=[np.abs(N[:,:,c]).max() for c in range(5)]
    eq=[(a,b) for a in range(5) for b in range(a+1,5) if np.abs(N[:,:,a]-N[:,:,b]).max()<1e-9]
    print('%s row 4 kernel: N dim %d, column norms %s, equal column pairs %s, column-projection ranks %s'%(name,len(N),np.array2string(np.array(cols),precision=2),eq,[rank(N[:,:,c]) for c in range(5)]))
    for (a,b) in eq[:3]:
        for i in (0,2):
            B=onb(build(N,a,b,i)); le=level_err(B,ntest=60)
            T=T1(embed(B),rg,npts=120); S=np.linalg.svd(T[:,4,:],compute_uv=False)
            print('     move (a,b)=(%d,%d) to row %d: level err %.0e dim T1 %d dim Omega %d FO2 %s'%(a,b,i,le,len(T),int((S>1e-8).sum()),FO2(embed(B),rg)))
