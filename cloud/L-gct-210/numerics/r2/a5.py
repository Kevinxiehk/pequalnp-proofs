import sys; sys.path.insert(0,"/home/claude/work/L-gct-210/numerics/r2")
from spaces import *
s0=np.load('sol7_ex1_d0_0.npy')
t0=time.time(); print('sol0 vs ex2 equiv angle %.1e'%equiv_angle(s0,ex2()), 'vs ex1 %.1e'%equiv_angle(s0,ex1()), 'ex1 vs ex2 %.1e'%equiv_angle(ex1(),ex2()), 'ex1 vs L080 %.1e'%equiv_angle(ex1(),L080()),f'{time.time()-t0:.0f}s')
