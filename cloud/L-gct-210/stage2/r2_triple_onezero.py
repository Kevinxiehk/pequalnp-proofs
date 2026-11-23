# Round 2: (T1) for the first non-generic layer. Rows 1,2,3 with a = 1; kappa^1 has exactly one zero (column 0 =: j0),
# kappa^2, kappa^3 zero-free; all three pairs minimal; X_123 = 0.  Pairs (1,2),(1,3): Type I_0 (blocks E1, F1 inside E = {1,2,3,4});
# pair (2,3): Type I or II (zero-free).  Coordinates: tau_1(j) = kappa^1_j z_1j (j in E), tau_1(j0) = free coordinate,
# tau_i = kappa^i o z_i (i = 2,3).  EXACT test as in t5: some S with the six functionals independent on C^{3xS} and a kernel
# point with nonzero permanent  =>  contradiction with ZBF.
import sys, itertools; sys.path.insert(0,'/home/claude/work/L-gct-210/stage2')
from exactla import *
UNIT=[(1,0),(0,1),(-1,0),(0,-1)]
def gperm(tau,u,S):
    re=Fr(0); im=Fr(0)
    for p in itertools.permutations(range(3)):
        t=tau[0][p[0]]*tau[1][p[1]]*tau[2][p[2]]
        if t==0: continue
        e=(u[0][S[p[0]]]+u[1][S[p[1]]]+u[2][S[p[2]]])%4
        re+=t*UNIT[e][0]; im+=t*UNIT[e][1]
    return re,im
E=[1,2,3,4]
subsets=[tuple(s) for r in (1,2,3) for s in itertools.combinations(E,r)]
grid=[(1,2,3),(1,0,0),(0,1,0),(0,0,1),(1,1,0),(1,0,1),(0,1,1),(1,1,1),(2,1,0),(1,2,0),(2,0,1),(1,0,2),(0,2,1),(0,1,2),(1,-1,0),(1,0,-1),(0,1,-1),(1,-1,1),(1,1,-1),(-1,1,1)]+list(itertools.product(range(4),repeat=3))
stats={}; surv=[]
for E1 in subsets:
    E2=[j for j in E if j not in E1]
    w2=[0]*5                       # exponents of i: w2 = +1 on E1 and at j0, -1 on E2
    for j in E2: w2[j]=2
    for F1 in subsets:
        F2=[j for j in E if j not in F1]
        sgn3=[0]*5
        for j in F2: sgn3[j]=2     # w3 on E
        r=[(sgn3[j]-w2[j])%4 for j in E]          # w3/w2 on E (0 or 2)
        opts=[]
        if len(set(r))==2:
            Ep=[j for j in E if (sgn3[j]-w2[j])%4==0]; Em=[j for j in E if j not in Ep]
            opts.append(('I',[0]+Ep, 0)); opts.append(('I',Ep, 2))           # block D, exponent of w3(j0)
            for (Q2,Q3) in ((Ep,Em),(Em,Ep)):
                for eps in (1,3):
                    # w23 = (eps i at j0, 1 on Q2, -1 on Q3)*const ; on Q2 actual w3/w2 = r-value; eta = that value
                    eta=0 if Q2 is Ep else 2
                    opts.append(('II',(Q2,Q3),(eta+eps)%4))
        else:
            opts.append(('I',[0],(r[0]+2)%4))
        for o in opts:
            w3=list(sgn3); w3[0]=o[2]
            u=[[0]*5,[(-x)%4 for x in w2],[(-x)%4 for x in w3]]
            F=[]
            v=[0]*15
            for j in E: v[j]=1
            F.append(v)
            for i in (1,2):
                v=[0]*15
                for j in range(5): v[5*i+j]=1
                F.append(v)
            v=[0]*15
            for j in E1: v[j]=1
            for j in E2: v[5+j]=1
            F.append(v)
            v=[0]*15
            for j in F1: v[j]=1
            for j in F2: v[10+j]=1
            F.append(v)
            v=[0]*15
            if o[0]=='I':
                for j in o[1]: v[5+j]=1; v[10+j]=-1
            else:
                for j in o[1][1]: v[5+j]=1          # sum_{Q3} tau_2
                for j in o[1][0]: v[10+j]=1         # sum_{Q2} tau_3
            F.append(v)
            found=False; nS6=0
            for S in itertools.combinations(range(5),3):
                rows=[[f[5*i+j] for i in range(3) for j in S] for f in F]
                ns,rk=nullspace(rows,9)
                if rk<6: continue
                nS6+=1
                for (x,y,z) in grid:
                    tau=[[x*ns[0][3*i+k]+y*ns[1][3*i+k]+z*ns[2][3*i+k] for k in range(3)] for i in range(3)]
                    re,im=gperm(tau,u,S)
                    if re!=0 or im!=0: found=True; break
                if found: break
            key=(o[0],'killed' if found else 'SURVIVES'); stats[key]=stats.get(key,0)+1
            if not found: surv.append((E1,F1,o,nS6))
for k,v in sorted(stats.items()): print(k,v)
print('survivors:',len(surv)); [print('  ',s) for s in surv[:25]]
