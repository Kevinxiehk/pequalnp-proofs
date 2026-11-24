import sys; sys.path.insert(0,"/home/kevxhk/work/L-gct-210/numerics/r2")
from spaces import *
from a6 import rref
import glob
np.set_printoptions(precision=3,suppress=True,linewidth=200)
fs=sorted(glob.glob('F_e2_blk_*.npy'))
Bs=[np.load(f) for f in fs]
for f,B in zip(fs,Bs):
    inv,dE,gap,gr=inv_full(B)
    print(f, 'dimE',dE,'gap %.1e/%.1e'%gap,'genrank',gr,'equiv to L080 %.1e'%equiv_angle_c(B,L080()),flush=True)
print('pairwise angles (no perms):',[[round(angle(a,b),3) for b in Bs] for a in Bs])
R,piv=rref(Bs[0][5:]) ; print('block part of first solution, rref pivots',piv)
for m in R: print(np.round(m[:3,:4],4))
