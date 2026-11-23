import sys, numpy as np, itertools
sys.argv=[sys.argv[0],'1','0']
src=open('/home/claude/work/L-gct-210/stage2/r4_weights.py').read().split("if __name__=='__main__':")[0]
exec(src)
np.set_printoptions(precision=5,suppress=True,linewidth=220)
def perm(M):
    n=len(M); return sum(np.prod([M[i,p[i]] for i in range(n)]) for p in itertools.permutations(range(n)))
rg=np.random.default_rng(1)
for trial in range(120):
    z=rg.normal(size=54); s=least_squares(res,z,method='lm',xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=300)
    if trial not in (19,47): continue
    g,lam,sig=unpack(s.x); print('trial',trial,'residual %.1e'%np.linalg.norm(s.fun)); print(' g=\n',g); print(' lam=\n',lam); print(' sig=',sig)
    # proportionality of lam_j
    for j in range(5):
        print('  cross(lam_%d, lam_l):'%j,[round(abs(lam[j,0]*lam[l,1]-lam[j,1]*lam[l,0]),5) for l in range(5)],' cross with sigma: %.5f'%abs(lam[j,0]*sig[1]-lam[j,1]*sig[0]))
    # level check of X directly
    r2=np.random.default_rng(3); w=0
    for _ in range(6):
        p=r2.normal(size=(3,2))+1j*r2.normal(size=(3,2)); p[2]=-p[0]-p[1]; t=np.zeros((5,5),complex)
        for i in range(3): t[2+i]=g[i]*(lam@p[i])
        w=max(w,abs(perm(np.ones((5,5))+t)-120))
    print('  level defect of X: %.2e'%w, ' analyse:',analyse(s.x))
