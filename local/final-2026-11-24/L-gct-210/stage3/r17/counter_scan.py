# Round 17: scan dim T_1 / FO2_0 over the counterexample family, incl. degenerate members (zero entries, repeated entries, special rho,
# disjoint supports, y o z = -z type). Indexing: 0-indexed rows 0..3 and columns 0..4; column 0 is the free column; y, z live on columns 1..4.
import sys, numpy as np
exec(open('/home/kevxhk/work/L-gct-210/stage3/r17/counter_t1.py').read().split('cases={')[0])
def fam(y):
    P=np.poly1d([0])
    for j in range(4):
        q=np.poly1d([y[j]])
        for k in range(4):
            if k!=j: q=q*np.poly1d([-1,y[k]])
        P=P+q
    out=[]
    for be in P.roots:
        if np.min(np.abs(y-be))>1e-6: out.append(y/(y-be))
    return out
rg=np.random.default_rng(3); res=[]
tests=[]
for rho in (0.7+0.2j,-0.5,2.0,1j):
    tests.append(('disjoint',rho,np.array([1,-1,0,0.]),np.array([0,0,1,-1.])))
    tests.append(('yoz=-z',rho,np.array([2,-1,-1,0.]),np.array([0,1,-1,0.])))
for t in range(6):
    y=rg.normal(size=4)+1j*rg.normal(size=4); 
    if t<2: y[3]=0
    if 2<=t<4: y[2]=y[1]
    y-=y.mean() if t>=2 else 0
    if t<2: y[:3]-=y[:3].mean()
    for z in fam(y)[:2]: tests.append(('random%d'%t,rg.normal()+1j*rg.normal(),y,z))
for nm,rho,y,z in tests:
    Z4=member(rho,y,z); B=np.zeros((5,5,5),complex); B[:,:4,:]=Z4
    ck=build7.check(B,n=3)
    if ck>1e-8: print(nm,'NOT LEVEL',ck); continue
    t=T1(B); n_,b0=fo2_0(B); res.append(b0)
    print('%-9s rho=%s  dim T_1 = %d (gaps %.0e/%.0e)  FO2_0 = %d'%(nm,np.round(rho,2),t[0],t[1],t[2],b0),flush=True)
print('MAX FO2_0 =',max(res))
