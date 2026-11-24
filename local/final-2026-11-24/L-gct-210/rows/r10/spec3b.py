import numpy as np, itertools, sys
exec(open('spec3.py').read().split("H=np.array")[0])
# harmonic projection: H_3 = kernel of the Laplacian on cubics
def lap(m):  # Laplacian of monomial -> dict
    out={}
    for i in range(3):
        if m[i]>=2:
            mm=list(m); mm[i]-=2; out[tuple(mm)]=out.get(tuple(mm),0)+m[i]*(m[i]-1)
    return out
lin=[m for m in itertools.product(range(2),repeat=3) if sum(m)==1]
L=np.zeros((3,10))
for k,m in enumerate(mons):
    for mm,v in lap(m).items(): L[lin.index(mm),k]+=v
u,s,vh=np.linalg.svd(L); Hb=vh[3:].T          # basis of harmonic cubics (10x7)
def specH3(Bs):
    A=sum(pullback(B) for B in Bs); AH=np.linalg.lstsq(Hb,A@Hb,rcond=None)[0]; return np.linalg.eigvals(AH)
r2,r3=np.sqrt(2),np.sqrt(3)
def cx(a): return np.array([[0,-a[2],a[1]],[a[2],0,-a[0]],[-a[1],a[0],0]])
def rot(s,v): return (s*s-v@v)*np.eye(3)+2*np.outer(v,v)+2*s*cx(v)
s=[3/(2*r2),3/(2*r2),-r3/(2*r2),-r3/(2*r2)]; eps=[1,1,-1,-1]
v=[np.array([-0.5j,0,1/(2*r2)]),np.array([0.5j,0,1/(2*r2)]),np.array([0,0.5,-r3/(2*r2)]),np.array([0,-0.5,-r3/(2*r2)])]
for inv in (1,-1):
    Bs=[e*rot(si,inv*vi) for e,si,vi in zip(eps,s,v)]
    print('++-- orientation %+d: sum B - 2I err %.1e; eigenvalues on H_3:'%(inv,np.linalg.norm(sum(Bs)-2*np.eye(3))),np.round(np.sort_complex(specH3(Bs)),5))
# five columns: random degree-2 configurations, distance of the H_3-spectrum from 3
exec(open('/home/kevxhk/work/L-gct-210/rows/r8/deg2_5.py').read().split("cnt={}")[0].replace("seed,nst=int(sys.argv[1]),int(sys.argv[2])","seed,nst=5,0"))
rng=np.random.default_rng(21)
for st in range(8):
    x=rng.normal(size=36)+1j*rng.normal(size=36); lam=1e-3; f=res(x); nf=np.linalg.norm(f)
    for it in range(300):
        if nf<1e-13: break
        J=np.zeros((len(f),36),complex)
        for k in range(36):
            e=np.zeros(36,complex); e[k]=1e-7; J[:,k]=(res(x+e)-f)/1e-7
        dx=np.linalg.lstsq(J.conj().T@J+lam*np.eye(36),-J.conj().T@f,rcond=None)[0]; f2=res(x+dx)
        if np.linalg.norm(f2)<nf: x=x+dx; f=f2; nf=np.linalg.norm(f2); lam=max(lam/3,1e-14)
        else: lam*=4
    if nf>1e-10: continue
    B=[x[9*k:9*k+9].reshape(3,3) for k in range(4)]; B.append(3*np.eye(3)-sum(B))
    sg=''.join(sorted('+' if np.real(np.linalg.det(M))>0 else '-' for M in B))
    ev=specH3(B); print('5 columns',sg,' min |lambda - 3| on H_3 = %.3f'%min(abs(ev-3)))
