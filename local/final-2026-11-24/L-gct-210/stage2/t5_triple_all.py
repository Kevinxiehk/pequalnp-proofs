# EXACT test of (2,2,2) triples: rows 1,2,3 (a=1, kappa without zeros), all three pairs minimal (Type I or II), X_123 = 0.
# tau-coordinates; units i^e; functionals with coefficients in {0,+-1}; kernel rational; perm in Gaussian rationals.
import sys, itertools; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
from exactla import *
def structs_all():
    out=[]
    for e in itertools.product([1,-1],repeat=5):
        if e[0]!=1 or abs(sum(e))==5: continue
        C=[1 if x==1 else 0 for x in e]
        out.append(('I',tuple(C),None, [0 if x else 2 for x in C], C, [-x for x in C]))
    for cells in itertools.product(range(3),repeat=5):
        if len(set(cells))<3: continue
        for eps in (1,-1):
            w=[(1 if eps==1 else 3) if q==0 else (0 if q==1 else 2) for q in cells]
            out.append(('II',cells,eps,w,[1 if q==2 else 0 for q in cells],[1 if q==1 else 0 for q in cells]))
    return out
def canon12():
    out=[]
    for C in ((1,0,0,0,0),(1,1,0,0,0)):
        out.append(('I',C,None,[0 if x else 2 for x in C],list(C),[-x for x in C]))
    for comp in ((1,1,3),(1,3,1),(3,1,1),(1,2,2),(2,1,2),(2,2,1)):
        cells=tuple([0]*comp[0]+[1]*comp[1]+[2]*comp[2])
        w=[1 if q==0 else (0 if q==1 else 2) for q in cells]
        out.append(('II',cells,1,w,[1 if q==2 else 0 for q in cells],[1 if q==1 else 0 for q in cells]))
    return out
def structs23(r):
    vals=sorted(set(r)); res=[]
    if len(vals)==2 and (vals[1]-vals[0])%4==2:
        C=[1 if x==vals[0] else 0 for x in r]; res.append(('I',C,[-x for x in C]))
    elif len(vals)==3:
        for b in vals:
            if (b+2)%4 in vals:
                # Q2 = cell(b), Q3 = cell(b+2)
                res.append(('II',[1 if x==(b+2)%4 else 0 for x in r],[1 if x==b else 0 for x in r]))
    return res
UNIT=[(1,0),(0,1),(-1,0),(0,-1)]
def gperm(tau,u,S):
    # perm over 3x3 of tau[i][k]*i^{u[i][S[k]]}; returns (re,im) Fractions
    re=Fr(0); im=Fr(0)
    for p in itertools.permutations(range(3)):
        t=tau[0][p[0]]*tau[1][p[1]]*tau[2][p[2]]
        if t==0: continue
        e=(u[0][S[p[0]]]+u[1][S[p[1]]]+u[2][S[p[2]]])%4
        re+=t*UNIT[e][0]; im+=t*UNIT[e][1]
    return re,im
grid=[(1,2,3),(1,0,0),(0,1,0),(0,0,1),(1,1,0),(1,0,1),(0,1,1),(1,1,1),(2,1,0),(1,2,0),(2,0,1),(1,0,2),(0,2,1),(0,1,2),(1,-1,0),(1,0,-1),(0,1,-1),(1,-1,1),(1,1,-1),(-1,1,1)]
grid+= [g for g in itertools.product(range(4),repeat=3)]
stats={}; surv=[]
for s12 in canon12():
    for s13 in structs_all():
        e2=s12[3]; e3=s13[3]; r=[(e3[j]-e2[j])%4 for j in range(5)]
        opts=structs23(r)
        key=(s12[0],s13[0])
        if not opts:
            stats[(key,'ratio inadmissible for a minimal pair (2,3)')]=stats.get((key,'ratio inadmissible for a minimal pair (2,3)'),0)+1; continue
        u=[[0]*5,[(-x)%4 for x in e2],[(-x)%4 for x in e3]]
        for o in opts:
            F=[]
            for i in range(3):
                v=[0]*15
                for j in range(5): v[5*i+j]=1
                F.append(v)
            v=[0]*15
            for j in range(5): v[j]=s12[4][j]; v[5+j]=s12[5][j]
            F.append(v)
            v=[0]*15
            for j in range(5): v[j]=s13[4][j]; v[10+j]=s13[5][j]
            F.append(v)
            v=[0]*15
            for j in range(5): v[5+j]=o[1][j]; v[10+j]=o[2][j]
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
            if found: stats[(key,'killed')]=stats.get((key,'killed'),0)+1
            else:
                stats[(key,'SURVIVES')]=stats.get((key,'SURVIVES'),0)+1; surv.append((s12[:3],s13[:3],o,nS6))
for k,v in sorted(stats.items()): print(k,v)
print('survivors:',len(surv),' types of the (2,3) pair among survivors:',sorted(set(s[2][0] for s in surv)))
