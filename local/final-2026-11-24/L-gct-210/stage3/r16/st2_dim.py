# local dimension of the stratum-(II) H-part solution set at the numerical solutions (Jacobian rank of the sampled system, normalisation incl.)
import numpy as np, sys, glob
sys.argv=['x','1','0','full']
exec(open('/home/kevxhk/work/L-gct-210/stage3/r16/st2_num.py').read().split('for st in range(NS):')[0])
for f in sorted(glob.glob('/home/kevxhk/work/L-gct-210/stage3/r16/st2num_full_*.npy')):
    x=np.load(f); f0,Jm=J(x,1e-8); s=np.linalg.svd(Jm,compute_uv=False)
    print(f.split('/')[-1],'res %.1e'%np.linalg.norm(f0),'sing.vals (smallest 8):',np.round(s[-8:],6),' n=',len(x))
