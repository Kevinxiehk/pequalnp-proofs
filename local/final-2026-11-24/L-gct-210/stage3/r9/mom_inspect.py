import sys, numpy as np
sys.argv=['mom_search.py','12','0','0']
exec(open('/home/kevxhk/work/L-gct-210/stage3/r9/mom_search.py').read().split('sols={}; fl=[]')[0])
rg2=np.random.default_rng(12)
r1[:]=r1; x0=(rg.normal(size=30)+1j*rg.normal(size=30))*0.6
x,nf=lm(x0); y=x[:20].reshape(4,5); p=x[20:25]; w=x[25:30]
np.set_printoptions(precision=4,suppress=True,linewidth=150)
print('residual',nf); print('Y=\n',y); print('p=',p); print('w=',w)
print('rank [w;p] =',np.linalg.matrix_rank(np.array([w,p]),1e-8),' |p| =',np.linalg.norm(p))
print('Gram <y_r,y_s> =\n',y@y.T)
