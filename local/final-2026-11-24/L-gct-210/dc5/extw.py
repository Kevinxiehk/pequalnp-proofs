import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/dc5')
import numpy as np
from ext import run
from weight import weight_dc
cfg={'L32':([1,2,0,4,3],[1,2,3,4,0],30,[2,3,4]),'L45':([1,2,3,0,4],[1,2,3,4,0],20,[1,2,3]),
     'P32':([1,2,0,4,3],[1,2,3,4,0],30,[2,3,4,6]),'P45':([1,2,3,0,4],[1,2,3,4,0],20,[1,2,3,4])}
name=sys.argv[1]; d=int(sys.argv[2]); ks=[int(c) for c in sys.argv[3]]; seed=int(sys.argv[4])
s,t,N,E=cfg[name]; B=weight_dc(s,t,N,E)
f,T=run(list(B),d,ks,12,seed,float(sys.argv[5]),eps=0.05)
print(name,'d',d,'ks',ks,'final',f); np.save(f'extw_{name}_d{d}_k{sys.argv[3]}.npy',T)
