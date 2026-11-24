# (1,1,1,1|2) case A numerics: u_1,u_2,u_3 = orthogonal frame (b,c,a) of H_4 with T = 0 (as in (2,1,1|2)(ii)), u_0 = (1,1,1,1,-4), V = {x_0 = 0} in column 4
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from nc_num import report, rowel, colel
from dr211b_num import member_g, cross4
rg=np.random.default_rng(5)
for k in range(4):
    a,b,c=member_g(rg); z=lambda v: np.concatenate([v,[0]])
    report('(1,1,1,1|2)A frame T=0 #%d'%k,[rowel(0,[1,1,1,1,-4]),rowel(1,z(b)),rowel(2,z(c)),rowel(3,z(a)),colel(4,[0,1,-1,0]),colel(4,[0,0,1,-1])])
b=np.array([1,-1,0,0],complex); c=np.array([1,1,-1,-1],complex); a=cross4(b,c); z=lambda v: np.concatenate([v,[0]])
report('(1,1,1,1|2)A b=(1,-1,0,0) c=(1,1,-1,-1)',[rowel(0,[1,1,1,1,-4]),rowel(1,z(b)),rowel(2,z(c)),rowel(3,z(a)),colel(4,[0,1,-1,0]),colel(4,[0,0,1,-1])])
b=np.array([1,-1,0,0],complex); c=np.array([0,0,1,-1],complex); a=cross4(b,c)
report('(1,1,1,1|2)A D-type',[rowel(0,[1,1,1,1,-4]),rowel(1,z(b)),rowel(2,z(c)),rowel(3,z(a)),colel(4,[0,1,-1,0]),colel(4,[0,0,1,-1])])
b=np.array([1,-1,0,0],complex); c=np.array([1,1,-2,0],complex); a=cross4(b,c)
report('(1,1,1,1|2)A Sigma-type',[rowel(0,[1,1,1,1,-4]),rowel(1,z(b)),rowel(2,z(c)),rowel(3,z(a)),colel(4,[0,1,-1,0]),colel(4,[0,0,1,-1])])
# T != 0 frame (should fail)
b=np.array([1,-1,1,-1],complex); c=np.array([1,1,-1,-1],complex); a=cross4(b,c)
report('(1,1,1,1|2)A T!=0',[rowel(0,[1,1,1,1,-4]),rowel(1,z(b)),rowel(2,z(c)),rowel(3,z(a)),colel(4,[0,1,-1,0]),colel(4,[0,0,1,-1])])
