import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/dc5')
import numpy as np
from ext import run
from tst import V, vk
from hess import hdims
init=[np.outer(a,vk(1)) for a in V]
K0=np.array(init).reshape(4,25); Q0=np.linalg.qr(K0.T)[0]
for seed,eps in [(1,0.01),(2,0.03),(3,0.06)]:
    f,T=run(init,4,[2,3,4],3,seed,30,eps=eps)
    Q=np.linalg.qr(T.reshape(4,25).T)[0]
    s=np.linalg.svd(Q0.conj().T@Q,compute_uv=False)
    print('eps',eps,'res %.1e'%f,'cos principal angles to Vxv',np.round(s,4), 'hess dims', hdims(T,[3,4]) if f<1e-9 else '')
