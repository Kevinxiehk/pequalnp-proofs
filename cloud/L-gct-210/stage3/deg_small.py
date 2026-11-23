import sys,time,itertools; seed=int(sys.argv[1]); TL=float(sys.argv[2]); ID=int(sys.argv[3]); sys.argv=['x','1','A','1','10','50']; sys.path.insert(0,"/home/claude/work/L-gct-210/stage3")
import numpy as np, f4b_core as F
from scipy.optimize import least_squares
# Round 7, section 26 (B'): degenerate two-plane case (deg-1), main sub-case. Unknowns n,h,h',u,v,x in C^5, mu,mu',mu''.
# 7-dim space span(t,t',t'') (+) e_d (x) span(n,h) (+) e_e (x) span(n,h') level;  ID=1: Lemma DEG identities (X_a X_b X_c = 0 on span(t,t',t'')).
K3=list(itertools.combinations(range(5),3)); P3=list(itertools.permutations(range(3)))
def p3(a,b,c): return np.array([sum(a[S[s[0]]]*b[S[s[1]]]*c[S[s[2]]] for s in P3) for S in K3])
def unpack(xr):
    z=xr[:33]+1j*xr[33:]; V=z[:30].reshape(6,5); mu=z[30:]; n,h,hp,u,v,x=V
    tb,tc=u,mu[0]*n-u; t1c,t1a=v,mu[1]*n-v; t2a,t2b=x,mu[2]*n-x
    B=np.zeros((7,5,5),dtype=complex)
    B[0,1]=tb; B[0,2]=tc; B[1,2]=t1c; B[1,0]=t1a; B[2,0]=t2a; B[2,1]=t2b; B[3,3]=n; B[4,3]=h; B[5,4]=n; B[6,4]=hp
    return V,mu,(tb,tc,t1c,t1a,t2a,t2b),B
def sv(rows):
    A=np.array([r/np.linalg.norm(r) for r in rows]); return np.linalg.svd(A,compute_uv=False)[-1]
def res(xr):
    V,mu,(tb,tc,t1c,t1a,t2a,t2b),B=unpack(xr); n,h,hp,u,v,x=V
    X=np.ones((5,5))+np.tensordot(F.C,B,axes=1); r=(F.perm5(X)-120.0)/30.0
    nr=lambda y: np.linalg.norm(y)
    out=[r.real,r.imag,np.array([nr(n)-1,nr(h)-1,nr(hp)-1,nr(tb)**2+nr(tc)**2-2,nr(t1c)**2+nr(t1a)**2-2,nr(t2a)**2+nr(t2b)**2-2])]
    hg=[3*max(0,0.3-nr(y)) for y in (tb,tc,t1c,t1a,t2a,t2b)]+[3*max(0,0.3-sv([n,h,hp])),3*max(0,0.2-sv([B[0].ravel(),B[1].ravel(),B[2].ravel()]))]
    out.append(np.array(hg))
    if ID:
        t=np.concatenate([p3(t1a,tb,tc),p3(t2a,tb,tc),p3(t1a,tb,t1c),p3(t1a,t2b,t1c),p3(t2a,t2b,tc),p3(t2a,t2b,t1c),p3(t1a,t2b,tc)+p3(t2a,tb,t1c)])
        out+=[t.real,t.imag]
    return np.concatenate(out)
rng=np.random.default_rng(seed); T0=time.time(); k=0; ns=0; best=[]
np.set_printoptions(precision=3,suppress=True,linewidth=220)
while time.time()-T0<TL:
    k+=1; sol=least_squares(res,rng.normal(size=66)*0.6,method='lm',max_nfev=200); c=np.sqrt(2*sol.cost); best.append(c)
    if c<1e-8:
        ns+=1; V,mu,T,B=unpack(sol.x); n,h,hp,u,v,x=V
        print('SOL',k,'cost %.1e'%c,'dim',F.rank(B.reshape(7,25)),'mu',np.round(mu,3),'<h,h> %.3f <hp,hp> %.3f'%(abs(h@h),abs(hp@hp)),'<n,n> %.1e'%abs(n@n),
              'max|X_aX_bX_c| at t+t\'+t\'\': %.3f'%np.abs(p3(T[3]+T[4],T[0]+T[5],T[1]+T[2])).max(),flush=True)
        print(np.array([n,h,hp,u,v,x])); np.save('deg_small_sol_%d_%d_%d.npy'%(seed,ID,k),sol.x)
print('seed',seed,'ID',ID,'starts',k,'solutions',ns,'residual quantiles',np.round(np.quantile(best,[0,0.1,0.5]),5),flush=True)
