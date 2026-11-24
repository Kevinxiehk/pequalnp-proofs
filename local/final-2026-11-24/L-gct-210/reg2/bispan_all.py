import sys, glob; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
exec(open('/home/kevxhk/work/L-gct-210/reg2/bispan.py').read().split('res={}')[0])
files=sorted(glob.glob('../rows/clm_p4_d6_*.npy')+glob.glob('../rows/nc_d6_*.npy')+glob.glob('../rows/seed_d6_*.npy')+glob.glob('../rows/rc45.npy')+glob.glob('ec_*.npy')+glob.glob('ec2_*.npy')+glob.glob('Mstar2.npy')+glob.glob('M_*.npy')+glob.glob('dr_u3_*.npy')+glob.glob('linespan_other_*.npy')+glob.glob('ext_*.npy')+glob.glob('p21111_hit_*.npy'))
res={}
for f in files:
    B0=np.load(f)
    if B0.ndim!=3 or B0.shape[1:]!=(4,5): continue
    B=onb(B0)
    if len(B)!=6: continue
    R=onb(rref_tol(B,1e-5))
    if level_err(R,ntest=15)<1e-9: B=R; tag='lim'
    else: tag='raw'
    l1=spans(B,1); l2=spans(B,2); res.setdefault((l1==6,l2==6),[]).append(f)
    if l2<6: print('NOT bi-line spanned:',f,tag,'line',l1,'bi-line',l2)
for k,v in res.items(): print('line-spanned=%s bi-line-spanned=%s : %d'%(k[0],k[1],len(v)))
