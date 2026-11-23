# (2,2,2) Type I triples with dim X_123 = 1: I_3^perp = N (5-dim) + C n*. Necessary conditions on nu = n*|K (K = kernel of
# f_1,f_2,f_3,g_12,g_13,g_23, 9-dim): for S with the six functionals independent on C^{3xS} and cubic c_S = perm|K_S != 0:
# nu|K_S = 0 or nu|K_S is a linear factor of c_S.  nu must not be the restriction of a functional supported on two rows.
# Numerical (float) survey over all pairs of partitions.
import sys, itertools, numpy as np; sys.path.insert(0,'/home/claude/work/L-gct-210/stage2')
from pairlib import nullspace, rank, perm
rng=np.random.default_rng(21)
def rnd(*k): return rng.normal(size=k)+1j*rng.normal(size=k)
def linfac3(cfun):
    lines=[(rnd(3),rnd(3)) for _ in range(2)]; pts=[]
    for p,d in lines:
        ss=np.array([0,1,2,3]); vals=np.array([cfun(p+s*d) for s in ss]); co=np.polyfit(ss,vals,3)
        if np.abs(co).max()<1e-9: return None
        pts.append([p+s*d for s in np.roots(co)])
    facs=[]
    for a in pts[0]:
        for b in pts[1]:
            lam=np.cross(a,b)                       # bilinear normal: lam.a = lam.b = 0
            if np.abs(lam).max()<1e-9: continue
            lam=lam/np.linalg.norm(lam)
            Hb=np.array([a,b]).T
            if all(abs(cfun(Hb@rnd(2)))<1e-7 for _ in range(4)) and not any(rank(np.array([lam,f]))==1 for f in facs): facs.append(lam)
    return facs
def analyse(d2,d3):
    d=[np.ones(5),np.array(d2,float),np.array(d3,float)]
    C={(0,1):(d[1]>0).astype(float),(0,2):(d[2]>0).astype(float),(1,2):(d[1]==d[2]).astype(float)}
    def F(rows):
        v=np.zeros((3,5),complex)
        for i,vec in rows: v[i]=vec
        return v.reshape(-1)
    one=np.ones(5)
    Fs=np.array([F([(0,one)]),F([(1,one)]),F([(2,one)])]+[F([(i,c),(ip,-c)]) for (i,ip),c in C.items()])
    K=nullspace(Fs)                                  # 15 x 9
    u=np.array(d)                                    # 1/w = w for signs
    cons=[]
    for S in itertools.combinations(range(5),3):
        Sc=[c for c in range(5) if c not in S]
        if rank(Fs[:,[i*5+c for i in range(3) for c in S]])<6: continue
        E=nullspace(K[[i*5+c for i in range(3) for c in Sc],:])
        if E.shape[1]!=3: continue
        def cfun(v,E=E,S=S):
            tau=(K@(E@v)).reshape(3,5); return perm((tau*u)[:,list(S)])
        facs=linfac3(cfun)
        if facs is None: continue
        cons.append((E,facs))                        # nu (9-vector, functional on K-coords) restricted: nu@E (3-vector)
    # forbidden subspaces: restrictions of functionals supported on two rows
    Rs=[]
    for (i,ip) in ((0,1),(0,2),(1,2)):
        M=np.zeros((10,15)); k=0
        for r in (i,ip):
            for j in range(5): M[k,r*5+j]=1; k+=1
        Rs.append(M@K)                               # 10 x 9 ; row space = R_{ii'}
    rr=[rank(R) for R in Rs]
    def trivial(V):                                  # V: 9 x d basis of nu-subspace
        if V.shape[1]==0: return True
        return any(rank(np.vstack([Rs[k],V.T]))==rr[k] for k in range(3))
    sols=[]
    def dfs(idx,V):
        if trivial(V): return
        if idx==len(cons): sols.append(V.shape[1]); return
        E,facs=cons[idx]
        dfs(idx+1,V@nullspace(E.T@V))
        for lam in facs:
            Pk=np.array([np.cross(lam,e) for e in np.eye(3)])        # rows c with lam.c = 0 (span 2-dim)
            dfs(idx+1,V@nullspace(Pk@E.T@V))
    dfs(0,np.eye(9,dtype=complex))
    return len(cons),sols
pats=[e for e in itertools.product([1,-1],repeat=5) if e[0]==1 and abs(sum(e))<5]
stats={}; ex=[]
for d2 in pats:
    for d3 in pats:
        if d3<=d2: continue
        nc,sols=analyse(d2,d3); key='no admissible n*' if not sols else 'n* possible'
        stats[key]=stats.get(key,0)+1
        if sols and len(ex)<8: ex.append((d2,d3,nc,len(sols),max(sols)))
print('Type I (2,2,2) triples, dim X_123 = 1:',stats); [print('  ',e) for e in ex]
