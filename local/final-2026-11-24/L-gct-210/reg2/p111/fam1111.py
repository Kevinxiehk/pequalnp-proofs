# Round 11: the (1,1,1,1|1,1) solution family of incidence class S = 00000111 (reg2/p111, r11_incpat_1111_11_S00000111.log):
# u0, u1 in U = {w : w_0 = w_1 = 0, sum w = 0} with <u0,u1> = 0, u2 = (0,-3,1,1,1), u3 = (-4,1,1,1,1), x0 = (1,1,-2,0), x1 = (1,-1,0,0).
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from nc_num import report
from pieces import sub_supported
for a in (0.3+0.7j, 2.0, -1.5+0.2j):
    u0=np.array([0,0,-1-a,1,a]); # u1: orthogonal to u0 inside U: u1 = (0,0,-p-q,p,q) with 2pp'... solve <u0,u1>=0 with p=1
    # <u0,u1> = (1+a)(1+q) + 1 + a q = 0 -> q (1+a+a) = -(1+a) - 1 -> q = -(2+a)/(1+2a)
    q=-(2+a)/(1+2*a); u1=np.array([0,0,-1-q,1,q])
    B=np.zeros((6,4,5),complex); B[0][0]=u0; B[1][1]=u1; B[2][2]=[0,-3,1,1,1]; B[3][3]=[-4,1,1,1,1]; B[4][:,0]=[1,1,-2,0]; B[5][:,1]=[1,-1,0,0]
    report('fam1111 a=%s'%a,B)
    ar=[len(sub_supported(B,np.eye(4,dtype=bool)[i][:,None].repeat(5,1))) for i in range(4)]
    bc=[len(sub_supported(B,np.eye(5,dtype=bool)[c][None,:].repeat(4,0))) for c in range(5)]
    print('   single-row dims',ar,' single-column dims',bc,' rank',np.linalg.matrix_rank(B.reshape(6,-1)))
