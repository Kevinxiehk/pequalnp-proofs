# TASK X5: rank q >= 3 on T_1 for EVERY member of (3,1|1,1) case A, chart x = (0,1,p,-1-p) [and chart '0': x = (0,0,1,-1)].
# Unknown lifts t_3 = (X3; e_3), t_4 = (X4; e_4) (X normalised by the pivots of gen_p311.py), d_0, tau = J - 5 e_4 1^T.
# S = span(d_0, tau, t_3, t_4) lies in T_1 (given the lifts exist: calibrations below), so rank(q_Y | T_1) >= rank(q_Y | S).
# Ideal: FO equations for both lifts + pivots + localisation + w^2+w+1 + all 3x3 minors of the 4x4 Gram matrices of q_Y (two Y).
# UNIT over Q  =>  for every member (on the chart) some 3x3 minor is nonzero: rank q >= 3, FO2 bound <= dim T_1 - 2 = 8.
import sys, itertools, subprocess; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
from famtool import *
chart=sys.argv[1] if len(sys.argv)>1 else '1'
JROW=int(sys.argv[2]) if len(sys.argv)>2 else 1
def basis(R,V):
    # (2,2|1,1) BB: U_0 = span(e0-e1, e0-e2) row 0; U_1 = span((-1,-1,-1,4,-1),(-1,-1,-1,-1,4)) row 1; x = (1,0,p,-1-p) col 3 [chart '1'] or
    # x = (0,0,1,-1) [chart '0']; x' = x' perp x inside {x_1 = 0, sum = 0} col 4
    c=R.const; Z=lambda: [[{} for _ in range(5)] for _ in range(4)]
    if chart=='1': x=[c(1),{},V('p'),add(c(-1),scal(V('p'),-1))]
    else: x=[{},{},c(1),c(-1)]
    xp=[add(x[2],x[3],-1),{},add(x[3],x[0],-1),add(x[0],x[2],-1)]
    Bs=[]
    tt=V('w')
    for w in ([c(1),c(-1),{},{},{}],[{},c(1),c(-1),{},{}]):
        Jw=[add(w[1],w[2],-1),add(w[2],w[0],-1),add(w[0],w[1],-1),{},{}]
        B=Z(); B[0]=list(w)
        for k in range(5):
            if Jw[k]: B[JROW][k]=mul(tt,Jw[k])
        Bs.append(B)
    for w in ([c(-1),c(-1),c(-1),c(4),c(-1)],[c(-1),c(-1),c(-1),c(-1),c(4)]):
        B=Z(); B[1]=list(w); Bs.append(B)
    B=Z()
    for i in range(4): B[i][3]=x[i]
    Bs.append(B)
    B=Z()
    for i in range(4): B[i][4]=xp[i]
    Bs.append(B)
    store['B']=Bs
    return Bs
store={}
F=Family(['w','p','z'],basis,6)   # w unused here (kept for the ring layout)
# target ring
an=['a%d%d'%(i,j) for i in range(4) for j in range(5)]; bn=['b%d%d'%(i,j) for i in range(4) for j in range(5)]
names=['w','p','z']+an+bn; R=Ring(names); V=R.var; one=R.const(1)
def conv(q,xmap,rho):
    """q: poly in F.names (w,p,z,x..,r..); substitute x_ij -> xmap[ij] (variable name), r_j -> rho[j]"""
    out={}
    for k,v in q.items():
        t=R.const(v)
        for idx,e in enumerate(k):
            if e==0: continue
            nm=F.names[idx]
            if nm in ('w','p','z'): f=V(nm)
            elif nm[0]=='x': f=V(xmap[nm[1:]])
            else: f=R.const(rho[int(nm[1:])])
            for _ in range(e): t=mul(t,f)
        out=add(out,t)
    return out
e3=[0,0,0,1,0]; e4=[0,0,0,0,1]
fo3=[conv(q,{n[1:]:'a'+n[1:] for n in F.xv},e3) for q in F.fo]
fo4=[conv(q,{n[1:]:'b'+n[1:] for n in F.xv},e4) for q in F.fo]
piv=['01','02','13','14','03' if chart=='1' else '23']
w_rel=R.const(0)
if chart=='1':
    loc_variants=[('x04',add(mul(V('z'),add(one,scal(V('p'),2))),R.const(-1)),'04'),('x24',add(mul(V('z'),add(R.const(-2),scal(V('p'),-1))),R.const(-1)),'24')]
else:
    loc_variants=[('x04',add(scal(V('z'),2),R.const(-1)),'04')]
# matrices over R: d_0, tau, t_3, t_4 (5x5)
def mat_t(prefix,rho):
    M=[[V(prefix+'%d%d'%(i,j)) for j in range(5)] for i in range(4)]; M.append([R.const(r) for r in rho]); return M
d0=[[R.const(0) for j in range(5)] for i in range(5)]
from fractions import Fraction
# use 4*d_0 to stay integral: rows: 3 (row 0), -1 (rows 1..3), 0 (row 4)
d0=[[R.const(3 if i==1 else (-1 if i<4 else 0)) for j in range(5)] for i in range(5)]
tau=[[R.const(1) for j in range(5)] for i in range(4)]+[[R.const(-4) for j in range(5)]]
# Hessian of perm at J + Y0, entries in Z[w,p]
P3=list(itertools.permutations(range(3)))
def perm3(A):
    tot={}
    for pp in P3:
        t=mul(mul(A[0][pp[0]],A[1][pp[1]]),A[2][pp[2]]); tot=add(tot,t)
    return tot
def to_R(q):   # poly in F.R (y.., w,p,z, x.., r..) without y -> R
    out={}
    for k,v in q.items():
        kk=k[6:]   # drop y exponents
        t=R.const(v)
        for idx,e in enumerate(kk):
            if e==0: continue
            nm=F.names[idx]; assert nm in ('w','p','z')
            for _ in range(e): t=mul(t,V(nm))
        out=add(out,t)
    return out
Bs=[[[to_R(e) if e else {} for e in row] for row in B] for B in store['B']]
def gram(yv):
    A=[[add(one,{}) for j in range(5)] for i in range(5)]
    for k,yk in enumerate(yv):
        for i in range(4):
            for j in range(5):
                if Bs[k][i][j]: A[i][j]=add(A[i][j],scal(Bs[k][i][j],yk))
    H={}
    for i in range(5):
        for k in range(i+1,5):
            rows=[r for r in range(5) if r not in (i,k)]
            for j in range(5):
                for l in range(5):
                    if j==l: continue
                    cols=[c for c in range(5) if c not in (j,l)]
                    v=perm3([[A[r][c] for c in cols] for r in rows]); H[(i,j,k,l)]=v; H[(k,l,i,j)]=v
    S=[d0,tau,mat_t('a',e3),mat_t('b',e4)]
    def q(T1_,T2_):
        tot={}
        for (i,j,k,l),h in H.items():
            if not T1_[i][j] or not T2_[k][l]: continue
            tot=add(tot,mul(h,mul(T1_[i][j],T2_[k][l])))
        return tot
    return [[q(S[a],S[b]) for b in range(4)] for a in range(4)]
minors=None
print('chart %s: %d FO eqs per lift'%(chart,len(fo3)),flush=True)
grams=[gram(yv) for yv in [(1,2,-1,3,1,-2),(2,-1,1,1,-3,1)]]
print('Gram entries built',flush=True)
elimvars=an+bn
for (pn,loc,pc) in loc_variants:
    pv=list(piv)+[pc,'20' if JROW!=2 else '30']
    zero=[V('a'+c) for c in pv]+[V('b'+c) for c in pv]
    base=fo3+fo4+zero+[loc,w_rel]
    lines=[to_str_Q(q,names) for q in base]; lines=[l for l in lines if l!='0']
    sc='ring R=0,(%s),(dp(%d),dp(3));\noption(redSB);\nideal I=%s;\nideal G=std(I);\n'%(','.join(an+bn+['w','p','z']),len(an+bn),',\n'.join(lines))
    sc+='ideal E=G[1..size(G)];\nideal Ewpz=eliminate(G,%s);\nprint("CAL elimination ideal (lifts exist where it vanishes):");print(std(Ewpz));\n'%('*'.join(elimvars))
    sc+='int ok=1; int k; for(k=1;k<=nvars(R)-3;k++){ if(deg(reduce(var(k),G),intvec(%s))>0){ok=0;} }\nprint("lifts unique (every a,b reduces to a poly in w,p,z):"); print(ok);\n'%(','.join(['1']*len(elimvars)+['0','0','0']))
    for gi,G in enumerate(grams):
        sc+='matrix Q%d[4][4];\n'%gi
        for a_ in range(4):
            for b_ in range(4):
                sc+='Q%d[%d,%d]=reduce(%s,G);\n'%(gi,a_+1,b_+1,to_str_Q(G[a_][b_],names) or '0')
    sc+='ideal Mi=minor(Q0,3)+minor(Q1,3);\nideal T=Ewpz+Mi;\nT=std(T);\nprint("rank<=2 locus ideal (UNIT = rank q >= 3 everywhere on the chart):");print(T);\nquit;\n'
    fn='/tmp/p311Ar_%s_%s.sing'%(chart,pn); open(fn,'w').write(sc)
    r=subprocess.run(['/usr/bin/Singular','-q'],stdin=open(fn),capture_output=True,text=True,timeout=1700)
    print('pivot',pn,':',' '.join(r.stdout.split())[:600],r.stderr[:300],flush=True)
