import numpy as np, itertools
w=np.exp(2j*np.pi/3); u=np.array([1,w,w*w]); ub=np.array([1,w*w,w])
def perm3(M): return sum(M[0,p[0]]*M[1,p[1]]*M[2,p[2]] for p in itertools.permutations(range(3)))
def P34(M):   # 3x4 'level' value: sum of the four 3x3 permanents of J + M
    return sum(perm3((1+M)[:,[c for c in range(4) if c!=k]]) for k in range(4))
def deletion_defects(Y):
    return np.array([P34(np.delete(Y,k,axis=1))-24 for k in range(5)])
r=0.37+0.21j
Z=np.outer(u,[1,-1,0,0,0]); Y0=np.outer(u,[1,0,0,0,0])+r*np.outer(ub,[1,1,0,0,0])
rng=np.random.default_rng(0); mx=0
for _ in range(10):
    x,y=rng.normal(size=2)+1j*rng.normal(size=2); mx=max(mx,np.abs(deletion_defects(x*Z+y*Y0)).max())
print('Pi_new: max |deletion defect| = %.2e'%mx)
# F1[1:1] for comparison
F=np.outer(u,[1,-1,0,0,0]); G=np.outer(ub,[1,1,0,0,0]); mx=0
for _ in range(10):
    x,y=rng.normal(size=2)+1j*rng.normal(size=2); mx=max(mx,np.abs(deletion_defects(x*F+y*G)).max())
print('F1[1:1]: max |deletion defect| = %.2e'%mx)
# formula check on random column-centred 3x4: coefficient of t^2 and t^3 in P34(tM) vs 2*3(ab - AB) and 6(e3a+e3b)
def e3(v): return sum(v[i]*v[j]*v[k] for i,j,k in itertools.combinations(range(len(v)),3))
a=rng.normal(size=4)+1j*rng.normal(size=4); b=rng.normal(size=4)+1j*rng.normal(size=4)
M=np.outer(u,a)+np.outer(ub,b)
ts=np.array([0.5,1.0,1.5,2.0]); vals=[P34(t*M)-24 for t in ts]
A_=np.vander(ts,4,increasing=True); co=np.linalg.solve(A_,vals)
print('t^2 coef %.4f%+.4fj  vs 2*3(ab-AB) = %s'%(co[2].real,co[2].imag, 2*3*((a*b).sum()-a.sum()*b.sum())))
print('t^3 coef %.4f%+.4fj  vs 6(e3a+e3b) = %s'%(co[3].real,co[3].imag, 6*(e3(a)+e3(b))))
# deletion-wise isotropic values for Pi_new at a random point
x,y=0.3+0.2j,-0.7+0.4j; Yp=x*Z+y*Y0
aa=Yp.T@ub/3; bb=Yp.T@u/3
for k in range(5):
    ak=np.delete(aa,k); bk=np.delete(bb,k)
    print(k,'P2-formula %.3e'%abs(3*((ak*bk).sum()-ak.sum()*bk.sum())),' P3-formula %.3e'%abs(6*(e3(ak)+e3(bk))))
