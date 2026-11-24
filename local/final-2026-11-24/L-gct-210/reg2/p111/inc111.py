# Round 11, target 3: (1,1,1|1,1,1) incidence-support split.  M = <e_i u_i (i = 0,1,2), x_m e_m^T (m = 0,1,2)>, u_i in C^5, x_m in C^4,
# all sums 0.  P_2 mixed gives x_m[i] * u_i[m] = 0 (i, m in {0,1,2}); S[i][m] = 1 means x_m[i] = 0, else u_i[m] = 0.
# For an incidence matrix S: all level equations of M (famtool) + sum conditions, saturated by the coordinate ideal of every vector
# (u_i != 0, x_m != 0).  Prints dim of the result (-1 = EMPTY).  usage: inc111.py S (9 digits, row-major)  [Singular over Q]
import sys, subprocess, time; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
from famtool import *
S=[[int(sys.argv[1][3*i+m]) for m in range(3)] for i in range(3)]
U=[[None if (c<3 and S[i][c]==0) else 'u%d%d'%(i,c) for c in range(5)] for i in range(3)]
X=[[None if (i<3 and S[i][m]==1) else 'x%d%d'%(m,i) for i in range(4)] for m in range(3)]
params=[v for row in U for v in row if v]+[v for row in X for v in row if v]
def bfn(R,V):
    Bs=[]
    for i in range(3):
        Z=[[{} for _ in range(5)] for _ in range(4)]
        for c in range(5): Z[i][c]=V(U[i][c]) if U[i][c] else {}
        Bs.append(Z)
    for m in range(3):
        Z=[[{} for _ in range(5)] for _ in range(4)]
        for i in range(4): Z[i][m]=V(X[m][i]) if X[m][i] else {}
        Bs.append(Z)
    return Bs
F=Family(params,bfn,6); np_=len(params)
lev=[{k[:np_]:v for k,v in q.items()} for q in F.level]; lev=[q for q in lev if q]
lines=[to_str_Q(q,params) for q in lev]
for row in U: lines.append('+'.join(v for v in row if v) or '0')
for row in X: lines.append('+'.join(v for v in row if v) or '0')
lines=[l for l in lines if l!='0']
sats=[ ','.join(v for v in row if v) for row in U]+[','.join(v for v in row if v) for row in X]
if any(s=='' for s in sats): print('S=%s: some vector has no free coordinate -> EMPTY'%sys.argv[1]); sys.exit()
body='LIB "elim.lib";\nring R=0,(%s),dp;\noption(redSB);\nideal I=%s;\nI=std(I);\n'%(','.join(params),',\n'.join(lines))
for s in sats: body+='I=sat(I,ideal(%s));\nif(typeof(I)=="list"){I=I[1];}\nI=std(I);\nif(I[1]==1){print("EMPTY");quit;}\n'%s
body+='print("dim "+string(dim(I))); print(size(I));\nquit;\n'
fn='/tmp/inc111_%s.sing'%sys.argv[1]; open(fn,'w').write(body); t0=time.time()
r=subprocess.run(['/usr/bin/Singular','-q'],stdin=open(fn),capture_output=True,text=True,timeout=1200)
print('S=%s vars %d lev %d : %s  (%.0f s)'%(sys.argv[1],len(params),len(lev),' '.join(r.stdout.split())[:200],time.time()-t0),flush=True)
