import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/numerics')
from core import *
B=np.load('W5ext_dc0_e1.npy'); f,B2=polish(B); 
for X,nm in [(B,'raw'),(B2,'polished')]:
    dE,E,s=ext_space(X); print(nm,'fresh %.1e'%fresh_check(X),invariants(X),'extdim',dE,'sv around cut',s[25-dE-2:25-dE+1])
W=orth(weight_w5()); dE,E,s=ext_space(W); print('W5 extdim',dE,s[25-dE-2:25-dE+1])
np.save('S4_r1d3.npy',B2)
