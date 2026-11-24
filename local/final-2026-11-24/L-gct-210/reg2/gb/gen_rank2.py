# gen_rank.py variant for families with nontrivial level relations: minors are selected greedily at NUMERICAL points ON the family
# (complex floats; the selection is only a guess, the certificate is the exact Singular computation over Q).
# Family '1111A': (1,1,1,1|2) case A: u_0 = (1,1,1,1,-4), u_1 = (b,0), u_2 = (c,0), u_3 = (cross4(b,c),0), V = {x_0 = 0, sum = 0} in column 4;
#   chart b = (1,b1,b2,-1-b1-b2) and c = (1,c1,c2,-1-c1-c2) [CH=0] or c = (c0,1,c2,-1-c0-c2) [CH=1].  Relations = the level equations (<b,c>, T).
import sys, random, subprocess, itertools; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2')
import numpy as np
from famtool import *
CH,r,K,seed=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]),int(sys.argv[4])
def det3(M):
    return add(add(mul(M[0][0],add(mul(M[1][1],M[2][2]),mul(M[1][2],M[2][1]),-1)),
                   mul(M[0][1],add(mul(M[1][0],M[2][2]),mul(M[1][2],M[2][0]),-1)),-1),
               mul(M[0][2],add(mul(M[1][0],M[2][1]),mul(M[1][1],M[2][0]),-1)))
def cross4(R,a,b,c):
    A_=[a,b,c]; out=[]
    for j in range(4):
        cols=[k for k in range(4) if k!=j]; out.append(scal(det3([[A_[i][k] for k in cols] for i in range(3)]),(-1)**j))
    return out
pn=['b1','b2','c1','c2'] if CH==0 else ['b1','b2','c0','c2']
def basis(R,V):
    c=R.const; b=[c(1),V('b1'),V('b2'),scal(add(add(c(1),V('b1')),V('b2')),-1)]
    if CH==0: cc=[c(1),V('c1'),V('c2'),scal(add(add(c(1),V('c1')),V('c2')),-1)]
    else: cc=[V('c0'),c(1),V('c2'),scal(add(add(c(1),V('c0')),V('c2')),-1)]
    a=cross4(R,[c(1)]*4,b,cc); Z=lambda: [[{} for _ in range(5)] for _ in range(4)]; Bs=[]
    B=Z(); B[0]=[c(1),c(1),c(1),c(1),c(-4)]; Bs.append(B)
    for i,v in ((1,b),(2,cc),(3,a)):
        B=Z(); B[i]=v+[{}]; Bs.append(B)
    B=Z(); B[1][4]=c(1); B[2][4]=c(-1); Bs.append(B)
    B=Z(); B[2][4]=c(1); B[3][4]=c(-1); Bs.append(B)
    return Bs
F=Family(pn,basis,6); np_=len(pn)
tv=F.xv+F.rv; idx={v:F.names.index(v) for v in tv}
Arows=[]
for q in F.fo:
    row=[{} for _ in tv]
    for k,v in q.items():
        lin=[t for t in tv if k[idx[t]]]; j=tv.index(lin[0]); kk=tuple(k[:np_]); row[j][kk]=row[j].get(kk,0)+v
    Arows.append(row)
lev=[{k[:np_]:v for k,v in q.items()} for q in F.level]
print('level equations %d, FO rows %d'%(len(lev),len(Arows)),flush=True)
# numerical points on the family: b random, c = c1 + s c2 in {1,b}^perp with T = 0, then normalised to the chart
from dr211b_num import member_g
rg=np.random.default_rng(seed)
def point():
    while True:
        a,b,c=member_g(rg); b=b/b[0]
        if CH==0: c=c/c[0]; return [b[1],b[2],c[1],c[2]]
        else: c=c/c[1]; return [b[1],b[2],c[0],c[2]]
def evalp(q,pt):
    s=0
    for k,v in q.items():
        t=complex(v)
        for e,x in zip(k,pt): t*=x**e
        s+=t
    return s
def greedy(pt):
    Ae=np.array([[evalp(q,pt) for q in row] for row in Arows]); order=list(range(len(Ae))); random.shuffle(order); rows=[]
    for i in order:
        if np.linalg.matrix_rank(Ae[rows+[i]],tol=1e-8*max(1,np.abs(Ae).max()))>len(rows): rows.append(i)
        if len(rows)==r: break
    sub=Ae[rows]; corder=list(range(25)); random.shuffle(corder); cols=[]
    for c in corder:
        if np.linalg.matrix_rank(sub[:,cols+[c]],tol=1e-8*max(1,np.abs(sub).max()))>len(cols): cols.append(c)
        if len(cols)==r: break
    return sorted(rows),sorted(cols)
random.seed(seed)
lines=['LIB "matrix.lib";','LIB "primdec.lib";','ring R=0,(%s),dp;'%','.join(pn),'option(redSB);','matrix A[%d][25];'%len(Arows)]
for a_,row in enumerate(Arows):
    for b_,q in enumerate(row):
        if q: lines.append('A[%d,%d]=%s;'%(a_+1,b_+1,to_str_Q(q,pn)))
lines.append('ideal I;')
for k in range(K):
    rs,cs=greedy(point())
    if len(rs)<r or len(cs)<r: print('rank < %d at a family point'%r); sys.exit()
    lines.append('I=I+det(submat(A,intvec(%s),intvec(%s)));'%(','.join(str(x+1) for x in rs),','.join(str(x+1) for x in cs)))
for q in lev: lines.append('I=I+(%s);'%to_str_Q(q,pn))
lines+=['I=std(I);','if(I[1]==1){print("UNIT");}else{print("dim");print(dim(I));list L=minAssGTZ(I);int i;for(i=1;i<=size(L);i++){print("COMP");print(L[i]);}}','quit;']
fn='/tmp/rank2_%d_%d.sing'%(CH,seed); open(fn,'w').write('\n'.join(lines)+'\n')
res=subprocess.run(['/usr/bin/Singular','-q'],stdin=open(fn),capture_output=True,text=True,timeout=1700)
print(' '.join(l for l in res.stdout.split('\n') if 'redefin' not in l)[:2500],res.stderr[:300])
