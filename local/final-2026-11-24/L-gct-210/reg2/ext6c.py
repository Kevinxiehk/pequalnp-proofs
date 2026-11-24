# second survey: 6-dim level spaces containing 3- or 4-dim level spaces taken from (a) random subspaces of Type F / NC spaces,
# (b) line-kernels of the 7-dim examples, (c) rows' strongly level (3,0) spaces.
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/chief')
import numpy as np, glob, time
from ext6 import *
import core
seed=int(sys.argv[1]); tmax=float(sys.argv[2]); which=sys.argv[3]
rg=np.random.default_rng(seed)
def Lr(B,r):
    m=np.ones((5,5),bool); m[r]=False
    S=sub_supported(B,m); rows=[i for i in range(5) if i!=r]
    return S[:,rows,:]
bases=[]
if which=='sub':
    srcs=[('rc45',np.load('../rows/rc45.npy')),('L080c0',np.load('M_L080_col0.npy')),('ex2r4',np.load('M_ex2_row4.npy'))]
    for f in ['nc_d6_k1_s23','nc_d6_k1_s4','seed_d6_e3_t4','nc_d6_k1_s21','clm_p4_d6_defect3_s12']:
        srcs.append((f,onb(rref_tol(onb(np.load('../rows/%s.npy'%f)),1e-5))))
    for name,B in srcs:
        for d in (3,3,2):
            C=rg.normal(size=(d,len(B)))+1j*rg.normal(size=(d,len(B))); bases.append(('%s sub%d'%(name,d),onb(np.einsum('kc,cab->kab',C,onb(B)))))
elif which=='ker':
    for name in ('L080','ex1','ex2','ex3','fam2'):
        Bm=np.array([np.array(mm,dtype=complex) for mm in core.SP[name]()])
        for tr,Bt in (('row',Bm),('col',Bm.transpose(0,2,1))):
            seen=set()
            for r in range(5):
                M=Lr(Bt,r)
                if len(M) in (3,4): bases.append(('%s %s %d'%(name,tr,r),onb(M)))
    for f in sorted(glob.glob('../rows/clm_p4_d3_*.npy')): bases.append((f.split('/')[-1],onb(np.load(f))))
t0=time.time(); tot={}
for name,M in bases:
    if time.time()-t0>tmax: print('time limit'); break
    E=E0(M,rg); D=complement(M,E); q=len(D); m=6-len(M)
    if q<=m: print('%-22s dim %d E0 %d: q<=m'%(name,len(M),len(E))); continue
    found={}; ntry=0
    for trial in range(5):
        if time.time()-t0>tmax: break
        c,B=solve_ext(M,D,m,rg,iters=150,N=300); ntry+=1
        if c<1e-9:
            typ,desc=classify(B,rg); found.setdefault(typ,[]).append(desc); tot[typ]=tot.get(typ,0)+1
    print('%-22s dim %d E0 %d (q=%d,m=%d): %d starts, found %s'%(name,len(M),len(E),q,m,ntry,{k:len(v) for k,v in found.items()}),flush=True)
    for k,v in found.items():
        if k=='OTHER':
            for dsc in sorted(set(v))[:4]: print('      ',k,dsc)
print('TOTAL',tot)
