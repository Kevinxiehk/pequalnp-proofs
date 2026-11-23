import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/dc5')
import numpy as np
from ext import run
from tst import V, vk
init=[np.outer(a,vk(1)) for a in V[:3]]
f,T=run(init,4,[2,3,4,5],30,int(sys.argv[1]),100,eps=float(sys.argv[2]))
print('final',f)
