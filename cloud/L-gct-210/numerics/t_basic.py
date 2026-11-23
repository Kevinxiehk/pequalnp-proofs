import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/numerics')
from core import *
B=L080(); print(report('L080',B)); print(' tangent', grass_tangent(B)[0])
W=weight_w5(); print(report('W5 weight',W)); print(' tangent', grass_tangent(W)[0])
import numpy as np
E=np.load('/home/claude/work/L-gct-086/smallcases/ext_w5_4.npy'); print(report('ext_w5_4 (old)',E))
f,E2=polish(E); print('polished res',f); print(report('ext_w5_4 polished',E2)); print(' tangent',grass_tangent(E2)[0])
np.save('/home/claude/work/L-gct-210/numerics/S7_w5ext.npy',E2)
