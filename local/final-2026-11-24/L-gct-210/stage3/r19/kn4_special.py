# Round 19: the special k_N = 4 member of z = (1,1,1,1,0): W = (e_0-e_1, e_2-e_3, (1,1,-1,-1,0), (1,1,1,1,-4)) on rows 0..3, row 4 none.
# Exact pair test over Q for every pair (r,k): third element xi of X_{rk} on rows {l, n, 4}; gauge xi_l[g_l] = 0, xi_n[g_n] = 0; charts XC.
import sys, itertools; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r18'); from pairtest import build
r,k,XC,P=int(sys.argv[1]),int(sys.argv[2]),sys.argv[3],sys.argv[4]
W={0:['1','-1','0','0','0'],1:['0','0','1','-1','0'],2:['1','1','-1','-1','0'],3:['1','1','1','1','-4']}
gauge={0:0,1:2,2:0,3:0}   # a coordinate where W[i] is nonzero
print(build(W,[],[],r,k,gauge,XC,P,'kn4'))
