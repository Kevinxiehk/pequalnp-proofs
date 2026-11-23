import sys,time,itertools; seed=int(sys.argv[1]); TL=float(sys.argv[2]); PP=int(sys.argv[3]); ID0=int(sys.argv[4]) if len(sys.argv)>4 else 0; sys.argv=['x','1','A','1','10','50']; sys.path.insert(0,"/home/claude/work/L-gct-210/stage3")
import numpy as np, f4b_core as F
from scipy.optimize import least_squares
# F4b core, FREE-COLUMN sub-family: y_r = e_1, p = -e_1 + p', w, g_r = q_r in C^{2345}.  PP=0: p' = 0.
ID=int(sys.argv[4]) if False else ID0
P4=np.array(list(itertools.permutations(range(4)))); P3l=list(itertools.permutations(range(3))); COLS=[[k for k in range(4) if k!=j] for j in range(4)]
def prod3f(a,b,c):
    return np.array([sum(a[C[s[0]]]*b[C[s[1]]]*c[C[s[2]]] for s in P3l) for C in COLS])
def vecs(x):
    z=(x[:24]+1j*x[24:]).reshape(6,4); v=np.zeros((10,5),dtype=complex)
    v[:4,0]=1; v[4,0]=-1
    if PP: v[4,1:]=z[5]
    v[5,1:]=z[4]; v[6:,1:]=z[:4]; return z,v
def res(x):
    z,v=vecs(x); B=F.basis(np.concatenate([v.ravel()]))[1]
    X=np.ones((5,5))+np.tensordot(F.C,B,axes=1); r=(F.perm5(X)-120.0)/30.0
    nr=np.sqrt((np.abs(z)**2).sum(axis=1))
    h=[3*max(0,0.3-nr[i]) for i in range(4)]
    ex=np.concatenate([0.1*z[5].real,0.1*z[5].imag]) if PP else np.concatenate([x[44:48],x[20:24]])
    out=[r.real,r.imag,np.array([nr[4]-1,nr[0]**2+nr[1]**2-2,nr[2]**2+nr[3]**2-2]),np.array(h),ex]
    if ID:
        q=z[:4]; t=[prod3f(q[i],q[j],q[k]) for (i,j,k) in itertools.combinations(range(4),3)]
        t+=[prod3f(q[0],q[1],z[4]),prod3f(q[2],q[3],z[4]),prod3f(q[0],q[1],z[5]),prod3f(q[2],q[3],z[5])]
        t.append(np.array([sum(q[0][s[0]]*q[1][s[1]]*q[2][s[2]]*q[3][s[3]] for s in P4)]))
        t=np.concatenate(t); out+=[t.real,t.imag]
    return np.concatenate(out)
P4=np.array(list(itertools.permutations(range(4)))); P3=np.array(list(itertools.permutations(range(3))))
def prod3(a,b,c):   # triple product in (A_N)_3, N = 4 columns
    M=np.array([a,b,c]); return np.array([sum(np.prod([M[i][[k for k in range(4) if k!=j][q[i]]] for i in range(3)]) for q in P3) for j in range(4)])
rng=np.random.default_rng(seed); T0=time.time(); n=0; ns=0; best=[]
while time.time()-T0<TL:
    n+=1; sol=least_squares(res,rng.normal(size=48)*0.6,method='lm',max_nfev=300); c=np.sqrt(2*sol.cost); best.append(c)
    if c<1e-8:
        ns+=1; z,v=vecs(sol.x); B=F.basis(v.ravel())[1]
        q=z[:4]; w=z[4]
        tri=[np.abs(prod3(q[i],q[j],q[k])).max() for (i,j,k) in itertools.combinations(range(4),3)]
        tw=[np.abs(prod3(q[0],q[1],w)).max(),np.abs(prod3(q[2],q[3],w)).max()]
        q4=abs(sum(np.prod([q[i][s[i]] for i in range(4)]) for s in P4))
        print('SOL',n,'cost %.1e'%c,'dim',F.rank(B.reshape(7,25)),'|q|',np.round(np.sqrt((np.abs(q)**2).sum(1)),2),'|p\'| %.2f'%np.linalg.norm(z[5] if PP else 0),
              ' (i) triples',np.round(tri,3),'q4 %.3f'%q4,' (ii),(iii) w-triples',np.round(tw,3),' rank q %d'%F.rank(q),'rank(q,w) %d'%F.rank(z[:5]),flush=True)
        np.save('f4b_fc_sol_%d_%d_%d_id%d.npy'%(seed,PP,n,ID),sol.x)
print('seed',seed,'PP',PP,'ID',ID,'starts',n,'solutions',ns,'residual quantiles',np.round(np.quantile(best,[0,0.1,0.5]),6),flush=True)
