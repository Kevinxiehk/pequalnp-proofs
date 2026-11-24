import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/dc5')
import numpy as np
from ext import run
Tb=np.load(sys.argv[1]); seed=int(sys.argv[2])
f,T=run(list(Tb),6,[2,3],12,seed,110,eps=0.05)
print('final',f)
