# Round 20: the 3100|10000 R1 census family (dr35_u3_s41_116 / _29) in closed form.  Rows r0 = 0 (three lines U_0 = V cap u^perp),
# r1 = 1 (u = (1,w,w^2,0,0)), pair P,Q = 2,3 (G = (e_2 - e_3) (x) x), column line v = (0,-2,1,1) in column 3.  Numerical invariants.
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from nc_num import report
w=np.exp(2j*np.pi/3)
def rowel(i,v): m=np.zeros((4,5),complex); m[i]=v; return m
def colel(c,v): m=np.zeros((4,5),complex); m[:,c]=v; return m
u=np.array([1,w,w*w,0,0])
U0=[np.array([0,0,0,1,-1]),u,np.array([1,1,1,-3,0])]
for name,x in (('x = conj pattern (1,w^2,w)',np.array([1,w*w,w,0,0])),('x = u pattern (1,w,w^2)',u.copy())):
    G=np.zeros((4,5),complex); G[2]=x; G[3]=-x
    B=[rowel(0,b) for b in U0]+[rowel(1,u),colel(3,np.array([0,-2,1,1])),G]
    report('c3100 '+name,B)
    # dr35 comparison: also the variant with column line in column 4 (d) instead of 3
    B2=[rowel(0,b) for b in U0]+[rowel(1,u),colel(4,np.array([0,-2,1,1])),G]
    report('c3100 '+name+' col4',B2)
