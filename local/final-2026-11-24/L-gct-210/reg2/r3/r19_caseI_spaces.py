# Round 19: build M = P_0 + N for each 3-dim linear component N of V_B (case (I), n = (1,2,3,-6,0), seed 1; r19_caseI_lift.log) and compute
# its numerical invariants: level error, dim, single-row/column parts, e, (dim T_1, rank q, FO2).
import sys, random, sympy as sp, numpy as np, re
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
src=open('/home/kevxhk/work/L-gct-210/reg2/r3/r3_cone.py').read()
pre=src.split("L=[]")[0]
sys.argv=['x','I','1,2,3,-6,0','1']; exec(pre)
from nc_num import report
from t import rowpart, colpart
from a5 import onb
P0=[]
for i in range(3):
    Z=np.zeros((4,5)); Z[3]=[float(x) for x in Wb[i]]; Z[0]=[float(x) for x in Bimg[i]]; P0.append(Z)
mm=[float(x) for x in m]
zp=['za','zg','p0','p1','p2','p3','p4','zl','zk','q0','q1','q2','q3','q4']
def Zmat(v):
    Z=np.zeros((4,5)); Z[3]=[v['za']+v['zg']*mm[k] for k in range(5)]; Z[1]=[v['p%d'%k] for k in range(5)]
    Z[2]=[v['zl']+(v['zk'] if k==4 else 0)-v['p%d'%k] for k in range(5)]; Z[0]=[v['q%d'%k] for k in range(5)]; return Z
log=open('/home/kevxhk/work/L-gct-210/reg2/evidence/logs/r19_caseI_lift.log').read()
for ci,line in enumerate([l for l in log.split('\n') if l.startswith('component')]):
    forms=[f.strip() for f in line.split('L = ')[1].split(', ')]
    syms=sp.symbols(' '.join(zp)); eqs=[sp.sympify(f) for f in forms]
    sol=sp.linsolve(eqs,syms); sol=list(sol)[0]; free=sorted(set().union(*[sp.sympify(s_).free_symbols for s_ in sol]),key=str)
    N=[]
    for f in free:
        v={str(s):float(sp.sympify(e).subs({g:(1 if g==f else 0) for g in free})) for s,e in zip(syms,sol)}; N.append(Zmat(v))
    B=np.array(P0+N,complex); Bo=onb(B)
    print('component %d: free %s  srow %s scol %s'%(ci+1,free,[len(rowpart(Bo,[i])) for i in range(4)],[len(colpart(Bo,[j])) for j in range(5)]),flush=True)
    for k,Z in enumerate(N): print('    N%d ='%k,np.round(Z,4).tolist())
    report('caseI comp %d'%(ci+1),B)
print('W basis',[list(map(str,w)) for w in Wb]); print('B images',[list(map(str,b)) for b in Bimg])
# rank of the row block P_0 modulo Lin(M) (Lin = single-row + single-column parts)
from pieces import sub_supported
for ci,line in enumerate([l for l in log.split('\n') if l.startswith('component')]):
    forms=[f.strip() for f in line.split('L = ')[1].split(', ')]
    syms=sp.symbols(' '.join(zp)); sol=list(sp.linsolve([sp.sympify(f) for f in forms],syms))[0]
    free=sorted(set().union(*[sp.sympify(s_).free_symbols for s_ in sol]),key=str); N=[]
    for f in free:
        v={str(s):float(sp.sympify(e).subs({g:(1 if g==f else 0) for g in free})) for s,e in zip(syms,sol)}; N.append(Zmat(v))
    Mo=onb(np.array(P0+N,complex)); parts=[]
    for i in range(4):
        mk=np.zeros((4,5),bool); mk[i]=True; parts+=list(sub_supported(Mo,mk))
    for c in range(5):
        mk=np.zeros((4,5),bool); mk[:,c]=True; parts+=list(sub_supported(Mo,mk))
    Lin=np.array([p.ravel() for p in parts]); e=np.linalg.matrix_rank(Lin,tol=1e-8)
    r=np.linalg.matrix_rank(np.concatenate([Lin,np.array([p.ravel() for p in P0])]),tol=1e-8)-e
    print('component %d: e = dim Lin(M) = %d, rank of P_0 modulo Lin(M) = %d'%(ci+1,e,r))
