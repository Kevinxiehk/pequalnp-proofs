# Round 16 rewrite (verify2 COMPUTE-ERRATA [R]): exact dim T_1 and rank q_Y for ONE explicit space over Q(w), w^2+w+1 = 0, computed END-TO-END
# in the number field K = QQ<sqrt(-3)> with DomainMatrix (no symbolic simplification), plus a mod-p cross-check of rank q at two primes p = 1 mod 3
# (mod-p ranks are LOWER bounds for the char-0 rank once T_1 is fixed over K).  The round-15 version used sympy Matrix.rank on expressions in
# sqrt(-3) and OVERestimated rank q (5 instead of 4) -- do not use it.   usage: q_rank_exact.py FAMILY
import sys, itertools; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
import sympy as sp
from sympy.polys.matrices import DomainMatrix
from famtool import *
fam=sys.argv[1]; src=open('/home/kevxhk/work/L-gct-210/reg2/gb/gen_rank.py').read(); sys.argv=['x',fam,'16','1','1']
exec(src[:src.index('F=Family(params,bfn,d)')])
K=sp.QQ.algebraic_field(sp.sqrt(-3)); w=K.from_sympy((-1+sp.sqrt(-3))/2); one=K.one; zero=K.zero
def kpow(e): 
    r=one
    for _ in range(e): r=r*w
    return r
F=Family(params,bfn,d); names=F.names
pidx=[names.index(p) for p in params]; tv=['x%d%d'%(i,j) for i in range(4) for j in range(5)]+['r%d'%j for j in range(5)]; tidx=[names.index(t) for t in tv]
rows=[]
for q in F.fo:
    row=[zero]*25
    for k,v in q.items():
        lin=[a for a,ti in enumerate(tidx) if k[ti]]; assert len(lin)==1
        c=K.from_sympy(sp.Integer(v))
        for pi in pidx: c=c*kpow(k[pi])
        row[lin[0]]=row[lin[0]]+c
    rows.append(row)
A=DomainMatrix(rows,(len(rows),25),K)
N=A.nullspace().to_Matrix()            # rows = basis of the right kernel
nT=N.rows; print(fam,': dim T_1 =',nT,' (DomainMatrix over QQ<sqrt(-3)>)',flush=True)
Nk=[[K.from_sympy(N[a,b]) for b in range(25)] for a in range(nT)]
R0=Ring(list(params)); Bs=bfn(R0,R0.var)
def evb(q):
    r=zero
    for k,v in q.items(): r=r+K.from_sympy(sp.Integer(v))*kpow(k[0])
    return r
Bn=[[[evb(B[i][j]) if B[i][j] else zero for j in range(5)] for i in range(4)] for B in Bs]
for yv in ((1,2,-1,3,1,-2),(2,-1,1,1,-3,1),(1,-1,2,1,3,-2)):
    Y=[[sum((K.from_sympy(sp.Integer(c))*Bn[k][i][j] for k,c in enumerate(yv)),zero) for j in range(5)] for i in range(4)]
    A5=[[one+Y[i][j] for j in range(5)] for i in range(4)]+[[one]*5]
    H={}
    for i,k in itertools.combinations(range(5),2):
        for j in range(5):
            for l in range(5):
                if j==l: continue
                rr=[r for r in range(5) if r not in (i,k)]; cc=[c for c in range(5) if c not in (j,l)]
                pv=zero
                for p_ in itertools.permutations(range(3)): pv=pv+A5[rr[0]][cc[p_[0]]]*A5[rr[1]][cc[p_[1]]]*A5[rr[2]][cc[p_[2]]]
                H[(i,j,k,l)]=pv; H[(k,l,i,j)]=pv
    T=[[[Nk[a][5*i+j] if i<4 else Nk[a][20+j] for j in range(5)] for i in range(5)] for a in range(nT)]
    G=[[zero]*nT for _ in range(nT)]
    for a in range(nT):
        for b in range(nT):
            s_=zero
            for (i,j,kk,ll),h in H.items():
                ta=T[a][i][j]; tb=T[b][kk][ll]
                if ta!=zero and tb!=zero: s_=s_+h*ta*tb
            G[a][b]=s_
    rk=DomainMatrix(G,(nT,nT),K).rank()
    print('  Y =',yv,': rank q_Y on T_1 = %d (DomainMatrix over QQ<sqrt(-3)>)'%rk,flush=True)
