# Generic LIFT / GRAM certificate (round 9): rank q_Y >= 3 on T_1 for every member of a (deformed, possibly restricted) family.
#   usage: lift_gram.py FAMILY DEFO FIX RHO1 RHO2 DDIR [NPIV]
#     DEFO = none | kind,idx,tgt ; FIX = - | name:value,... ; RHO1/RHO2 = column indices k (rho = e_k, two elements of Omega other than 1);
#     DDIR = row,i | col,c (the extra E_0 direction d).
#   Unknown lifts t_s = (X_s; e_{RHO_s}) with X_s normalised at 7 numerically chosen pivots of M + C d (localised by z*Delta = 1); S = span(d, tau,
#   t_1, t_2) lies in T_1 (tau = J - 5 e_4 1^T); the ideal {FO equations of both lifts, pivots, localisation, level equations of the family,
#   all 3x3 minors of the Gram matrices of q_Y on S (two Y)} is computed by Singular; UNIT => rank q >= 3 wherever the lifts exist and the pivot
#   set is valid.  Also prints the elimination ideal "lifts exist" and checks uniqueness of the lifts.
import sys, subprocess, random, itertools; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
import numpy as np
from fractions import Fraction as Fr
fam,defo,fixs,r1,r2,ddir=sys.argv[1],sys.argv[2],sys.argv[3],int(sys.argv[4]),int(sys.argv[5]),sys.argv[6]; npiv=int(sys.argv[7]) if len(sys.argv)>7 else 2
DEFO2=None
for _a in sys.argv[8:]:
    if _a.startswith('defo2='): _k,_i,_t=_a[6:].split(','); DEFO2=(_k,int(_i),int(_t))
FIX=dict(kv.split(':') for kv in fixs.split(',')) if fixs!='-' else {}
src=open('/home/kevxhk/work/L-gct-210/reg2/gb/gen_rank.py').read(); cut=src.index('F=Family(params,bfn,d)')
sys.argv=['x',fam,'16','1','1']; exec(src[:cut])
base_bfn=bfn; P=[p for p in params if p not in FIX]
import math
def bfn0(R,V0):
    def V(n):
        if n in FIX:
            f=Fr(FIX[n]); return R.const(f) if f!=0 else {}
        return V0(n)
    Bs=base_bfn(R,V)
    for B in Bs:
        dens=[Fr(v).denominator for row in B for e in row if e for v in e.values()]
        L=1
        for dd in dens: L=L*dd//math.gcd(L,dd)
        for i in range(4):
            for j in range(5):
                if B[i][j]: B[i][j]={k:int(Fr(v)*L) for k,v in B[i][j].items()}
    return Bs
if defo!='none':
    kind,idx,tgt=defo.split(','); idx=int(idx); tgt=int(tgt)
    def support(B):
        cells=[(i,j) for i in range(4) for j in range(5) if B[i][j]]; return set(i for i,j in cells), set(j for i,j in cells)
    def dotv(a,b):
        t={}
        for x,y in zip(a,b):
            if x and y: t=add(t,mul(x,y))
        return t
    def _apply(Bs,kind,idx,tgt,t):
        grp=[k for k,B in enumerate(Bs) if (support(B)[1]=={idx} if kind=='col' else support(B)[0]=={idx})]
        v=[[Bs[g][i][idx] for i in range(4)] if kind=='col' else [Bs[g][idx][j] for j in range(5)] for g in grp]
        g11=dotv(v[0],v[0]); g12=dotv(v[0],v[1]); g22=dotv(v[1],v[1])
        Jv=[[add(mul(g12,v[0][k]) if v[0][k] else {}, mul(g11,v[1][k]) if v[1][k] else {},-1) for k in range(len(v[0]))],
            [add(mul(g22,v[0][k]) if v[0][k] else {}, mul(g12,v[1][k]) if v[1][k] else {},-1) for k in range(len(v[0]))]]
        return grp,Jv
    def bfnD(R,V):
        Bs=bfn0(R,V)
        specs=[(kind,idx,tgt,V('t'))]+([(DEFO2[0],DEFO2[1],DEFO2[2],V('t2'))] if DEFO2 else [])
        pre=[_apply(Bs,k_,i_,g_,t_) for (k_,i_,g_,t_) in specs]      # groups and J computed on the UNDEFORMED basis
        for (k_,i_,g_,t_),(grp,Jv) in zip(specs,pre):
            for n,g in enumerate(grp):
                for k in range(len(Jv[n])):
                    if Jv[n][k]:
                        if k_=='col': Bs[g][k][g_]=add(Bs[g][k][g_],mul(t_,Jv[n][k])) if Bs[g][k][g_] else mul(t_,Jv[n][k])
                        else: Bs[g][g_][k]=add(Bs[g][g_][k],mul(t_,Jv[n][k])) if Bs[g][g_][k] else mul(t_,Jv[n][k])
        return Bs
    P=P+['t']+(['t2'] if DEFO2 else []); BF=bfnD
else: BF=bfn0
F=Family(P+['z'],BF,d); npar=len(P)+1
levels=[{k[:npar]:v for k,v in q.items()} for q in F.level]
an=['a%d%d'%(i,j) for i in range(4) for j in range(5)]; bn=['b%d%d'%(i,j) for i in range(4) for j in range(5)]
names=an+bn+P+['z']; R=Ring(names); V=R.var; one=R.const(1)
def conv_par(q):   # poly in (P + z) -> R
    out={}
    for k,v in q.items():
        t=R.const(v)
        for e,nm in zip(k,P+['z']):
            for _ in range(e): t=mul(t,V(nm))
        out=add(out,t)
    return out
def conv(q,pref,rho):
    out={}
    for k,v in q.items():
        t=R.const(v)
        for idx_,e in enumerate(k):
            if e==0: continue
            nm=F.names[idx_]
            if nm in P or nm=='z': f=V(nm)
            elif nm[0]=='x': f=V(pref+nm[1:])
            else: f=R.const(1 if int(nm[1:])==rho else 0)
            for _ in range(e): t=mul(t,f)
        out=add(out,t)
    return out
fo1=[conv(q,'a',r1) for q in F.fo]; fo2=[conv(q,'b',r2) for q in F.fo]; lv=[conv_par(q) for q in levels]
Bs=BF(F.R,F.R.var)
def toR(q):   # poly in F.R (y.., P, z, x.., r..) -> R (no y, x, r)
    out={}
    for k,v in q.items():
        t=R.const(v)
        for idx_,e in enumerate(k[d:]):
            if e==0: continue
            nm=F.names[idx_]
            for _ in range(e): t=mul(t,V(nm))
        out=add(out,t)
    return out
BR=[[[toR(B[i][j]) if B[i][j] else {} for j in range(5)] for i in range(4)] for B in Bs]
kd,vd=ddir.split(','); vd=int(vd)
Dm=[[R.const(3 if i==vd else -1) for j in range(5)] for i in range(4)] if kd=='row' else [[R.const(4 if j==vd else -1) for j in range(5)] for i in range(4)]
span=BR+[Dm]
# numerical pivot sets
rg=np.random.default_rng(7); random.seed(7)
def ev(q,vals):
    sm=0
    for k,v in q.items():
        t=complex(v)
        for e,x in zip(k,vals): t*=x**e
        sm+=t
    return sm
cells=[(i,j) for i in range(4) for j in range(5)]
def pivset():
    vals=[0]*len(names)
    for nm in P: vals[names.index(nm)]=complex(rg.normal(),rg.normal())
    A=np.array([[ev(E[i][j],vals) if E[i][j] else 0 for (i,j) in cells] for E in span])
    order=list(range(len(span))); random.shuffle(order); rows=[]
    for k in order:
        if np.linalg.matrix_rank(A[rows+[k]],tol=1e-8)>len(rows): rows.append(k)
    cord=list(range(20)); random.shuffle(cord); cols=[]
    for c_ in cord:
        if np.linalg.matrix_rank(A[rows][:,cols+[c_]],tol=1e-8)>len(cols): cols.append(c_)
        if len(cols)==len(rows): break
    return rows,cols
def strq(q): return to_str_Q(q,names) if q else '0'
P3=list(itertools.permutations(range(3)))
def perm3(A_):
    tot={}
    for pp in P3: tot=add(tot,mul(mul(A_[0][pp[0]],A_[1][pp[1]]),A_[2][pp[2]]))
    return tot
def gram(yv):
    A_=[[one for j in range(5)] for i in range(5)]
    for k,yk in enumerate(yv):
        for i in range(4):
            for j in range(5):
                if BR[k][i][j]: A_[i][j]=add(A_[i][j],scal(BR[k][i][j],yk))
    H={}
    for i in range(5):
        for k in range(i+1,5):
            rows=[r for r in range(5) if r not in (i,k)]
            for j in range(5):
                for l in range(5):
                    if j==l: continue
                    cols=[c for c in range(5) if c not in (j,l)]; v_=perm3([[A_[r][c] for c in cols] for r in rows]); H[(i,j,k,l)]=v_; H[(k,l,i,j)]=v_
    d5=[row[:] for row in Dm]+[[{} for _ in range(5)]]
    tau=[[one]*5 for _ in range(4)]+[[R.const(-4)]*5]
    T1m=[[V('a%d%d'%(i,j)) for j in range(5)] for i in range(4)]+[[R.const(1 if j==r1 else 0) for j in range(5)]]
    T2m=[[V('b%d%d'%(i,j)) for j in range(5)] for i in range(4)]+[[R.const(1 if j==r2 else 0) for j in range(5)]]
    S=[d5,tau,T1m,T2m]
    def q(X,Y):
        tot={}
        for (i,j,k,l),h in H.items():
            if X[i][j] and Y[k][l]: tot=add(tot,mul(h,mul(X[i][j],Y[k][l])))
        return tot
    return [[q(S[a],S[b]) for b in range(4)] for a in range(4)]
ys=[(1,2,-1,3,1,-2,1,2,-1),(2,-1,1,1,-3,1,-1,1,2)]
grams=[gram(yv[:len(BR)]) for yv in ys]
print('%s %s %s: Gram matrices built'%(fam,defo,FIX),flush=True)
for ps in range(npiv):
    rows,cols=pivset()
    mat='matrix PM[%d][%d];\n'%(len(rows),len(cols))
    for a_,k in enumerate(rows):
        for b_,c_ in enumerate(cols):
            qq=span[k][cells[c_][0]][cells[c_][1]]
            if qq: mat+='PM[%d,%d]=%s;\n'%(a_+1,b_+1,strq(qq))
    zero=[V('a%d%d'%cells[c_]) for c_ in cols]+[V('b%d%d'%cells[c_]) for c_ in cols]
    base=fo1+fo2+zero+lv
    lines=[strq(q) for q in base]; lines=[l for l in lines if l!='0']
    el='*'.join(an+bn)
    sc='LIB "matrix.lib";\nring R=0,(%s),(dp(%d),dp(%d));\noption(redSB);\n%spoly Dl=det(PM);\nideal I=%s;\nI=I+(z*Dl-1);\nideal G=std(I);\n'%(','.join(names),len(an+bn),len(P)+1,mat,',\n'.join(lines))
    sc+='ideal E=eliminate(G,%s);\nprint("LIFTS EXIST where:");print(std(E));\n'%el
    sc+='int ok=1; int k; for(k=1;k<=%d;k++){ if(deg(reduce(var(k),G),intvec(%s))>0){ok=0;} }\nprint("lifts unique:"); print(ok);\n'%(len(an+bn),','.join(['1']*len(an+bn)+['0']*(len(P)+1)))
    for gi,G_ in enumerate(grams):
        sc+='matrix Q%d[4][4];\n'%gi
        for a_ in range(4):
            for b_ in range(4):
                sc+='Q%d[%d,%d]=reduce(%s,G);\n'%(gi,a_+1,b_+1,strq(G_[a_][b_]))
    sc+='ideal Mi=minor(Q0,3)+minor(Q1,3);\nideal T=E+Mi;\nT=std(T);\nprint("rank<=2 locus (UNIT = rank q >= 3 on this pivot chart):");print(T);\nprint("pivot minor (chart = Delta != 0):");print(Dl);\nquit;\n'
    fn='/tmp/lg_%s_%d.sing'%(fam,ps); open(fn,'w').write(sc)
    r=subprocess.run(['/usr/bin/Singular','-q'],stdin=open(fn),capture_output=True,text=True,timeout=1700)
    print('pivot set %d %s: %s'%(ps,[('x%d%d'%cells[c_]) for c_ in cols],' '.join(r.stdout.split())[:900]),flush=True)
