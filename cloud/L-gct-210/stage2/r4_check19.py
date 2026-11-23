# The survey r4_weights.py lists solutions with pattern 111^5, injective, no single-column elements. Check them against Lemma N2-GEN:
# print the smallest |g_ij| and, after polishing with tighter tolerances, whether a weight tends to 0.
import sys, numpy as np
sys.argv=[sys.argv[0],'1','0']
src=open('/home/claude/work/L-gct-210/stage2/r4_weights.py').read().split("if __name__=='__main__':")[0]
exec(src)
np.set_printoptions(precision=5,suppress=False,linewidth=220)
rg=np.random.default_rng(1); shown=0
for trial in range(120):
    z=rg.normal(size=54); s=least_squares(res,z,method='lm',xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=300)
    if np.linalg.norm(s.fun)>1e-9: continue
    key=analyse(s.x)
    if key[0]==tuple([(1,1,1)]*5) and key[1] and key[2]==0:
        g,lam,sig=unpack(s.x); s2=least_squares(res,s.x,method='lm',xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=3000); g2,lam2,sig2=unpack(s2.x)
        # normalise column scaling: report |g_ij| relative to column max
        rel=abs(g)/abs(g).max(axis=0); rel2=abs(g2)/abs(g2).max(axis=0)
        print('trial',trial,' residual %.1e -> %.1e'%(np.linalg.norm(s.fun),np.linalg.norm(s2.fun)),' min relative |g|: %.2e -> %.2e'%(rel.min(),rel2.min()),' min |g| %.2e'%abs(g2).min(), ' col max',np.round(abs(g2).max(axis=0),3))
        shown+=1
        if shown==1: print(' |g| =\n',abs(g2)); print(' lam=\n',lam2,'\n sig=',sig2)
        if shown>=8: break
