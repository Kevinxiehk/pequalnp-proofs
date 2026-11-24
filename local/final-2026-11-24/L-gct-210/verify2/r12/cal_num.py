# numerical calibration: find a point where all t-degree<=2 equations of my alpha1 supp-3 generator (pattern ++++, f0 chart, n = w(tau)) vanish
import sympy as sp, numpy as np, re
txt=open('E_cal.txt').read().replace('^','**').replace('\n','')
vs=sp.symbols('pa0 pa1 pa2 pb0 pb1 pb2 ph0 ph1 ph2 f1 f2 rho l1 qq tau'); I=sp.I
loc={str(v):v for v in vs}; loc['I']=I
polys=[sp.sympify(p,locals=loc) for p in txt.split(',') if p.strip() and p.strip()!='0']
print('equations',len(polys))
F=sp.lambdify([vs],polys,'numpy'); J=sp.lambdify([vs],sp.Matrix(polys).jacobian(vs),'numpy')
rng=np.random.default_rng(3); best=None
for start in range(40):
    x=rng.normal(size=len(vs))+1j*rng.normal(size=len(vs)); lam=1e-3
    for it in range(300):
        r=np.array(F(x),dtype=complex); Jm=np.array(J(x),dtype=complex)
        n0=np.linalg.norm(r)
        if n0<1e-13: break
        A=Jm.conj().T@Jm; g=Jm.conj().T@r
        dx=np.linalg.solve(A+lam*np.eye(len(vs)),-g)
        r1=np.array(F(x+dx),dtype=complex)
        if np.linalg.norm(r1)<n0: x=x+dx; lam=max(lam/3,1e-12)
        else: lam*=4
    res=np.linalg.norm(np.array(F(x),dtype=complex))
    if best is None or res<best[0]: best=(res,x)
    if res<1e-11: print('start',start,'converged: residual %.2e'%res,' rho=%s l1=%s'%(np.round(x[11],4),np.round(x[12],4))); break
print('best residual %.2e'%best[0])
