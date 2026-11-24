# Round 10, target 3: EXACT check of the remaining case of the rank bound for a 4-dim skew row block.
# M = P (+) <Z1, Z2>,  P = {e_3 w + e_0 K w : w in 1^perp},  K = 5x5 skew with K 1 = 0 (6 params k01..k23),
# Z = a e_3 1 + b e_0 1 + e_1 p + e_2 (lam 1 - p), lam = -a-b (all zeta_Z constant, z_0 constant by (1,1), z_3 normalised).
# <Z1,Z2> in reduced row echelon form w.r.t. the coordinates (a, b, p_0..p_4); first p-pivot moved to column 0 (or (0,1)) by S_5.
# Ideal: all level equations of M + (y*Pf - 1), Pf = k01 k23 - k02 k13 + k03 k12 (rank K = 4).  Singular over Q: UNIT = no such M.
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
from famtool import *
chart=sys.argv[1]; CALCOND=sys.argv[2] if len(sys.argv)>2 else 'y*(k01*k23-k02*k13+k03*k12)-1'
kn=['k01','k02','k03','k12','k13','k23']
zv={'A':['p10','p11','p12','p13','p14','p20','p21','p22','p23','p24'],
    'B':['b1','p11','p12','p13','p14','p21','p22','p23','p24'],
    'C':['p11','p12','p13','p14','p21','p22','p23','p24'],
    'D':['p12','p13','p14','p22','p23','p24']}[chart]
params=kn+zv
def bfn(R,V):
    c=R.const; K=[[{} for _ in range(5)] for _ in range(5)]
    for nm in kn:
        a,b=int(nm[1]),int(nm[2]); K[a][b]=V(nm); K[b][a]=scal(V(nm),-1)
    for a in range(4):
        s={}
        for b in range(4): s=add(s,K[a][b])
        K[a][4]=scal(s,-1); K[4][a]=s
    Bs=[]
    for m in range(4):
        Z=[[{} for _ in range(5)] for _ in range(4)]
        for j in range(5): Z[3][j]=c(1) if j==m else (c(-1) if j==4 else {})
        for i in range(5): Z[0][i]=add(K[i][m],K[i][4],-1)        # K (e_m - e_4)
        Bs.append(Z)
    def Zel(a,b,p):
        Z=[[{} for _ in range(5)] for _ in range(4)]; lam=scal(add(a,b),-1)
        for j in range(5): Z[3][j]=a; Z[0][j]=b; Z[1][j]=p[j]; Z[2][j]=add(lam,p[j],-1)
        return Z
    v=lambda n: V(n)
    if chart=='A': Z1=Zel(c(1),{},[v('p1%d'%j) for j in range(5)]); Z2=Zel({},c(1),[v('p2%d'%j) for j in range(5)])
    if chart=='B': Z1=Zel(c(1),v('b1'),[{}]+[v('p1%d'%j) for j in range(1,5)]); Z2=Zel({},{},[c(1)]+[v('p2%d'%j) for j in range(1,5)])
    if chart=='C': Z1=Zel({},c(1),[{}]+[v('p1%d'%j) for j in range(1,5)]); Z2=Zel({},{},[c(1)]+[v('p2%d'%j) for j in range(1,5)])
    if chart=='D': Z1=Zel({},{},[c(1),{}]+[v('p1%d'%j) for j in range(2,5)]); Z2=Zel({},{},[{},c(1)]+[v('p2%d'%j) for j in range(2,5)])
    return Bs+[Z1,Z2]
F=Family(params,bfn,6)
npar=len(params); lev=[{k[:npar]:v for k,v in q.items()} for q in F.level]; lev=[q for q in lev if q]
names=params+['y']; ext=lambda q:{k+(0,):v for k,v in q.items()}
Pf=to_str_Q({},names)
lines=[to_str_Q(ext(q),names) for q in lev]
lines.append(CALCOND)
fn='/tmp/sk3_%s_%d.sing'%(chart,len(sys.argv))
open(fn,'w').write('ring R=0,(%s),dp;\noption(redSB);\nideal I=%s;\nideal G=std(I);\nprint("chart %s: "+string(size(I))+" generators; std basis size "+string(size(G))+"; G[1] = "+string(G[1]));\nquit;\n'%(','.join(names),',\n'.join(lines),chart))
print('chart',chart,': level equations',len(lev),'variables',len(names),flush=True)
import subprocess,time; t0=time.time()
r=subprocess.run(['/usr/bin/Singular','-q'],stdin=open(fn),capture_output=True,text=True)
print(r.stdout.strip()[:600],r.stderr.strip()[:300]); print('time %.0f s'%(time.time()-t0))
