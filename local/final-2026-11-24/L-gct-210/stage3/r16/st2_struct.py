import numpy as np, glob
def rk(A,t=1e-7):
    s=np.linalg.svd(np.atleast_2d(A),compute_uv=False); return int((s>t*max(1,s[0])).sum())
for f in sorted(glob.glob('st2num_full_*.npy')):
    h=np.load(f)[:15].reshape(3,5); s=h[2].sum(); k=h-s/2
    D=np.stack([h[0]-h[2],h[1]-h[2]],1); one=np.ones(5)
    Dp=np.column_stack([one,D])
    tests={'k_i o k_i in span(1,Delta)':[rk(np.column_stack([Dp,k[i]*k[i]]))-rk(Dp) for i in range(3)],
           'k_i in span(1,Delta)':[rk(np.column_stack([Dp,k[i]]))-rk(Dp) for i in range(3)],
           'dim span(1,k0,k1,k2)':rk(np.column_stack([one,k.T])),
           'dim span(1,k,k^2 all)':rk(np.column_stack([one,k.T,(k*k).T])),
           'zero entries':int((np.abs(h)<1e-8).sum()),
           'distinct column points':len({tuple(np.round(h[:,j],6)) for j in range(5)})}
    print(f.split('_')[-1],tests)
