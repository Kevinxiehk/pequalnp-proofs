import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/split')
from core import *
B=np.load(sys.argv[1]); XA=B[:4]; XB=B[4:]
rng=np.random.default_rng(0)
for name,X,ax in (('A',XA,-1),('B',XB,-2)):
    cs=rnd((40,4),rng); T=np.einsum('ri,iab->rab',cs,X)
    P=Pk(T)
    c,al,be,g=decomp(T); v=al if name=='A' else be
    p3=(v**3).sum(-1); e3=np.array([sum(v[r,i]*v[r,j]*v[r,k] for i in range(5) for j in range(i+1,5) for k in range(j+1,5)) for r in range(40)])
    p2=(v**2).sum(-1)
    print(name,'P2 max',np.abs(P[:,2]).max(),' P3/p3 ratio spread', np.std(P[:,3]/p3), np.mean(P[:,3]/p3))
    # fit P3 to all cubic monomials in coefficients
    import itertools
    mons=list(itertools.combinations_with_replacement(range(4),3))
    Mx=np.array([[np.prod([cs[r,m] for m in mon]) for mon in mons] for r in range(40)])
    co,res,rk,sv=np.linalg.lstsq(np.column_stack([p3]),P[:,3],rcond=None)
    print('  fit P3 = lam*p3(alpha): lam',co,' resid',np.linalg.norm(P[:,3]-co[0]*p3)/np.linalg.norm(P[:,3]))
