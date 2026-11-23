"""Test of (C52): is every (5,2) space row-split (sum of single-row parts = defect plane)?  Searches seeded at NON-split (4,1) spaces
   and unseeded; classification of all hits."""
import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/rows')
import numpy as np, time, glob
from clm import *
from seeded import defect_basis, start
from r4_census import analyse
t0=time.time(); hits=[]
files=sorted(glob.glob('ns41/*.npy'))
for tr in range(40):
    if time.time()-t0>70: break
    Zs=np.load(files[tr%len(files)]); Es=defect_basis(Zs,1)
    P=Problem(4,5,'defect',2,seed=3000+tr); z,c=solve(P,z0=start(P,Zs,Es,P.rng,scale=[1.0,0.3,3.0][tr%3]),iters=300); Z=P.basis(z)
    if c<1e-9 and np.linalg.cond(Z.reshape(5,-1))<1e6:
        f='c52_seedns_%d.npy'%tr; np.save(f,Z); hits.append(f)
n1=len(hits); print('seeded at the two non-split (4,1) spaces -> (5,2): %d hits of %d'%(n1,tr+1),flush=True)
for s in range(200,260):
    if time.time()-t0>140: break
    P=Problem(4,5,'defect',2,seed=s); z,c=solve(P,iters=250); Z=P.basis(z)
    if c<1e-9 and np.linalg.cond(Z.reshape(5,-1))<1e6:
        f='c52_rand_%d.npy'%s; np.save(f,Z); hits.append(f)
print('unseeded (5,2): %d hits of %d'%(len(hits)-n1,s-199),flush=True)
tab={}
for f in hits:
    k=analyse(f); tab.setdefault(k,[]).append(f)
print('(d, e, u_i sorted, dim sum U_i, dim two-col part of C, dim(sum U_i + two-col), dim rad C, max zeta_ab, q_s, dim ker gamma): count')
for k in sorted(tab): print('  ',k,':',len(tab[k]),tab[k][:3])
