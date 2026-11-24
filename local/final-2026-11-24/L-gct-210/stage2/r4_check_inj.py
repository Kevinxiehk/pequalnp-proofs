import sys, glob, numpy as np
sys.argv=[sys.argv[0],'1','0']
src=open('/home/kevxhk/work/L-gct-210/stage2/r4_weights.py').read().split("if __name__=='__main__':")[0]
exec(src)
np.set_printoptions(precision=4,suppress=True,linewidth=220)
for f in sorted(glob.glob('/tmp/r4_w_inj_*.npy')):
    z=np.load(f); key=analyse(z)
    if key[2]==2: continue
    s2=least_squares(res,z,method='lm',xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=4000); 
    for tag,zz in (('found',z),('polished',s2.x)):
        g,lam,sig=unpack(zz); fn=np.array([[abs(g[i,j])*np.linalg.norm(lam[j]) for j in range(5)] for i in range(3)])
        sm=[np.linalg.svd(np.array([g[i,j]*lam[j] for j in range(5)]),compute_uv=False)[-1] for i in range(3)]
        cr=np.array([[abs(lam[j,0]*lam[l,1]-lam[j,1]*lam[l,0])/(np.linalg.norm(lam[j])*np.linalg.norm(lam[l])+1e-300) for l in range(5)] for j in range(5)])
        print(f.split('_')[-1],tag,'residual %.1e'%np.linalg.norm(res(zz)),' min form norm %.2e'%fn.min(),' smin rows: %.1e %.1e %.1e'%tuple(sm),' |lam_j|:',np.round(np.linalg.norm(lam,axis=1),4),' key',analyse(zz)[1:4])
    print('   form norms |g_ij||lam_j| (polished):\n',fn); print('   normalised cross products of the lam_j (polished):\n',cr)
