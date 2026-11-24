# verify a numerical X0 solution at fresh random points; structure report
import numpy as np, itertools, glob, sys
def sig(M,m,cols):
    tot=0
    for R in itertools.combinations(range(M.shape[0]),m):
        for C in itertools.permutations(cols,m): tot=tot+np.prod([M[R[k],C[k]] for k in range(m)])
    return tot
def unpack(x):
    v1=np.r_[1,0,x[0:3]]; v2=np.r_[0,1,x[3:6]]; u1=np.array([x[6],x[7],1,0,x[8]]); u2=np.array([x[9],x[10],0,1,x[11]])
    w1,w2,t1,t2=x[12:17],x[17:22],x[22:27],x[27:32]; return v1,v2,u1,u2,w1,w2,t1,t2
rg=np.random.default_rng(99)
for f in sorted(glob.glob('/home/kevxhk/work/L-gct-210/stage3/r18/x0sol_*.npy')):
    x=np.load(f); v1,v2,u1,u2,w1,w2,t1,t2=unpack(x)
    err=0
    for _ in range(30):
        a,b,c,d=rg.normal(size=4)+1j*rg.normal(size=4)
        X=np.array([a*v1+b*v2,a*w1+b*w2,c*u1+d*u2,c*t1+d*t2]); err=max(err,max(abs(sig(X,m,range(5))) for m in (1,2,3,4)))
    rk=lambda *vs: np.linalg.matrix_rank(np.array(vs),1e-8)
    print(f.split('/')[-1],'fresh-point max|sigma| = %.1e'%err,' ranks: P_a',rk(v1,v2),'P_b',rk(w1,w2),'P_c',rk(u1,u2),'P_d',rk(t1,t2))
    for nm,vv in (('v1',v1),('v2',v2),('w1',w1),('w2',w2),('u1',u1),('u2',u2),('t1',t1),('t2',t2)): print('   ',nm,np.round(vv,4))
    # c-planes and their dims
    ca=np.array([v1+w1,v2+w2]); cc=np.array([u1+t1,u2+t2]); print('    dim c(P_a)',rk(*ca),' dim c(P_c)',rk(*cc),' <c_a,c_c>',np.round(np.abs(ca@cc.T).max(),8))
