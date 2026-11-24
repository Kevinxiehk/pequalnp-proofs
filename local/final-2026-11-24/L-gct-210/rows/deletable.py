import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/numerics')
import numpy as np, glob
from build7 import build
from core import fresh_check
for f in sorted(glob.glob(sys.argv[1]))[:4]:
    B,e=build(np.load(f)); out=[]
    for tr in (0,1):
        for r in range(5):
            C=B.copy()
            if tr: C[:,:,r]=0
            else: C[:,r,:]=0
            C=C[np.abs(C).reshape(len(C),-1).max(1)>1e-12]
            out.append('%s%d:%.0e'%('c' if tr else 'r',r,fresh_check(C)))
    print(f,' level error after zeroing a line:',' '.join(out))
