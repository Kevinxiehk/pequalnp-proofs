# verify2 round 5: verifyfl's blueprint fact used in Lemma 3C / NP: non-proportional isotropic v, v' in V = 1^perp of C^4 with
# tau(v^2 v') = tau(v v'^2) = 0 form exactly 7 unordered pairs of lines (4 "zeta" pairs with a common zero row, 3 conjugate chi pairs).
import numpy as np, itertools
chi1=np.array([1,1j,-1,-1j]); chi2=np.array([1,-1,1,-1]); chi3=np.array([1,-1j,-1,1j])
rng=np.random.default_rng(3)
Mo=rng.normal(size=(2,2))+1j*rng.normal(size=(2,2))          # random Moebius change so that no solution sits at infinity
def v(t):
    A=Mo[0,0]*t+Mo[0,1]; B=Mo[1,0]*t+Mo[1,1]
    return A*A*chi1+A*B*chi2-(B*B/2)*chi3                   # isotropic: <v,v> = 8 x z + 4 y^2 = -4 A^2 B^2 + 4 A^2 B^2 = 0
assert abs(np.sum(v(0.3+0.2j)**2))<1e-12 and abs(np.sum(v(0.3+0.2j)))<1e-12
def F(z):
    t,u=z; a=v(t); b=v(u)
    return np.array([np.sum(a*a*b),np.sum(a*b*b)])/(t-u)     # divide out the diagonal t = u (both vanish there to first order? keep generic)
def newton(z):
    for _ in range(80):
        f=F(z); 
        if np.linalg.norm(f)<1e-13: break
        J=np.empty((2,2),complex); h=1e-7
        for k in range(2):
            zp=z.copy(); zp[k]+=h; J[:,k]=(F(zp)-f)/h
        try: z=z-np.linalg.solve(J,f)
        except np.linalg.LinAlgError: return None
        if not np.all(np.isfinite(z)) or np.abs(z).max()>1e6: return None
    return z if np.linalg.norm(F(z))<1e-10 else None
sols=[]
for _ in range(4000):
    z=newton((rng.normal(size=2)+1j*rng.normal(size=2))*2)
    if z is None or abs(z[0]-z[1])<1e-6: continue
    if not any(np.abs(z-s).max()<1e-6 for s in sols): sols.append(z)
def line(t):
    x=v(t); x=x/np.abs(x).max(); k=[i for i in range(4) if abs(x[i])>1e-5][0]; return x/x[k]
pairs=set()
lines=[]
def lid(x):
    for i,l in enumerate(lines):
        if np.abs(l-x).max()<1e-6: return i
    lines.append(x); return len(lines)-1
for t,u in sols: pairs.add(frozenset((lid(line(t)),lid(line(u)))))
print('ordered solutions (t != u):',len(sols),'; unordered pairs of lines:',len(pairs),'; distinct lines involved:',len(lines))
for p in sorted(pairs,key=sorted):
    a,b=[lines[i] for i in sorted(p)]
    zc=[k for k in range(4) if abs(a[k])<1e-8 and abs(b[k])<1e-8]
    print('  pair: common zero rows %s, tau(a^3) = %.3f, tau(b^3) = %.3f, a = %s'%(zc,abs(np.sum(a**3)),abs(np.sum(b**3)),np.round(a,3)))
print('pairs pairwise disjoint:',all(len(p&q)==0 for p in pairs for q in pairs if p!=q))
