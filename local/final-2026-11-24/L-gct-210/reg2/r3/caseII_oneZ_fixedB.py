# Round 12, target 1, case (II): n = e3 - e4, W = {sum 0, w3 = w4}, B from bspace_II.py (params s, c3, c7, c11; rank 3 <=> s*(2c3+2c7-3c11) != 0).
# Rows: r = 3 (x = w), j = 0 (y = Bw), k = 1, l = 2.  ONE extra element Z: z_3 = za*1 + zg*n, z_1 = p, z_2 = zl*1 + zk*1_S - p, z_0 = q.
# Ideal: level equations of <X_w1, X_w2, X_w3, Z> + yy*s*(2c3+2c7-3c11) - 1, saturated by the Z coordinates (Z not 0).  Components of the
# admissible cone V_B of Z's.  Variable names avoid famtool's x%d%d / r%d / y%d.
import sys, subprocess; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
from famtool import *
from fractions import Fraction as Fr
zp=['za','zg','p0','p1','p2','p3','p4','zl','zk','q0','q1','q2','q3','q4']
import sys as _s
BV=[int(x) for x in _s.argv[1].split(',')]
params=zp
W=[[1,-1,0,0,0],[1,0,-1,0,0],[2,0,0,-1,-1]]
def bfn(R,V):
    c=R.const; s=c(BV[0]); n=[0,0,0,1,-1]
    a=[[Fr(-1,2),Fr(-1,2),1,0,0],[Fr(1,2),-1,Fr(1,2),0,0],[0,-1,1,0,0]]; beta=[c(BV[1]),c(BV[2]),c(BV[3])]
    Bs=[]
    for i in range(3):
        Z=[[{} for _ in range(5)] for _ in range(4)]
        Z[3]=[c(x) if x else {} for x in W[i]]
        Z[0]=[add(scal(s,2*a[i][k]) if a[i][k] else {}, scal(beta[i],2*n[k]) if n[k] else {}) for k in range(5)]   # 2*B w_i (scaled by 2)
        Bs.append(Z)
    Z=[[{} for _ in range(5)] for _ in range(4)]
    Z[3]=[add(V('za'),scal(V('zg'),n[k])) if n[k] else V('za') for k in range(5)]
    Z[1]=[V('p%d'%k) for k in range(5)]
    Z[2]=[add(add(V('zl'),V('zk') if k in (3,4) else {}),V('p%d'%k),-1) for k in range(5)]
    Z[0]=[V('q%d'%k) for k in range(5)]
    Bs.append(Z)
    return Bs
F=Family(params,bfn,4); np_=len(params)
lev=[{k[:np_]:v for k,v in q.items()} for q in F.level]; lev=[q for q in lev if q]
names=params+['yy']; ext=lambda q:{k+(0,):v for k,v in q.items()}
lines=[to_str_Q(ext(q),names) for q in lev]+['yy-1']
body='LIB "elim.lib";\nLIB "primdec.lib";\nring R=0,(%s),dp;\noption(redSB);\nideal I=%s;\nI=std(I);\nprint("before sat dim "+string(dim(I)));\nI=sat(I,ideal(%s));\nI=std(I);\nprint("after sat dim "+string(dim(I)));\nif(I[1]==1){print("EMPTY");quit;}\nlist L=minAssGTZ(I);int i;for(i=1;i<=size(L);i++){ideal G=std(L[i]); int nl=0; int k; for(k=1;k<=size(G);k++){if(deg(G[k])==1){nl++;}} print("COMP "+string(i)+" dim "+string(dim(G))+" degree "+string(mult(G))+" linear forms (incl. yy-1) "+string(nl)); kill G; kill nl; kill k;}\nquit;\n'%(','.join(names),',\n'.join(lines),','.join(zp))
import os; fn='/tmp/caseII_oneZ_%d.sing'%os.getpid(); open(fn,'w').write(body)
print('level equations:',len(lev),flush=True)
r=subprocess.run(['/usr/bin/Singular','-q'],stdin=open(fn),capture_output=True,text=True,timeout=1500)
print(r.stdout[:6000]); print(r.stderr[:500]); print("Singular exit code",r.returncode)
