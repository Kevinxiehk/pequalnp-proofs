# Pattern (3,1|2), incidence case (alpha) (the only one not covered by SP8(b), NOTES-reg2 9.4):
#   M(m) = e_0 (x) {w : sum w = 0, <m,w> = 0} (+) C e_1 m^T (+) {x e_4^T : x_0 = 0, sum x = 0},  m = (1, m1, m2, m3, 0), m3 = -1-m1-m2.
#   Basis of U_0 = {1,m}^perp: f_k = m_k e_0 - e_k + (1 - m_k) e_4 (k = 1,2,3).   Level for every m (no level equations).
#   Omega-test: rho_4 = 0, rho_0+..+rho_3 = 0 (complement of span(1,e_4)), chart rho_j = 1 (j = 0..3);
#   X normalised modulo M + C d_0 (row 0 deletable): pivots x01,x02,x03 (f_k), x10 (m^T), x24,x34 (V), x20 (d_0) -- constant pivots,
#   so NO localisation: the systems are plain affine systems over Q.   E_0-test: rho = 0, same pivots, chart x_ib = 1 (13 charts).
import sys, subprocess; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
from famtool import *
mode=sys.argv[1]
def basis(R,V):
    c=R.const; Z=lambda: [[{} for _ in range(5)] for _ in range(4)]
    m=[c(1),V('m1'),V('m2'),scal(add(add(c(1),V('m1')),V('m2')),-1),{}]
    Bs=[]
    for k in (1,2,3):
        B=Z(); B[0][0]=m[k]; B[0][k]=c(-1); B[0][4]=add(c(1),scal(m[k],-1)); Bs.append(B)
    B=Z()
    for j in range(5): B[1][j]=m[j]
    Bs.append(B)
    B5=Z(); B5[1][4]=c(1); B5[2][4]=c(-1)
    B6=Z(); B6[2][4]=c(1); B6[3][4]=c(-1)
    return Bs+[B5,B6]
F=Family(['m1','m2'],basis,6); W=F.W
print('level equations (must be 0):',len(F.level),flush=True)
def sing(polys,elim=None):
    lines=[to_str_Q(q,F.names) for q in polys]; lines=[l for l in lines if l!='0']
    if elim: body='ideal J=eliminate(I,%s);\nJ=std(J);\nprint(J);\nprint("FACTORS");\nint i; for(i=1;i<=size(J);i++){print(factorize(J[i]));}'%elim
    else: body='ideal G=std(I);\nprint(size(G));\nprint(G[1]);'
    script='ring R=0,(%s),dp;\noption(redSB);\nideal I=%s;\n%s\nquit;\n'%(','.join(F.names),',\n'.join(lines),body)
    open('/tmp/p312.sing','w').write(script)
    r=subprocess.run(['/usr/bin/Singular','-q'],stdin=open('/tmp/p312.sing'),capture_output=True,text=True,timeout=900)
    return ' '.join(r.stdout.split())
zero=['x01','x02','x03','x10','x24','x34','x20']
el='*'.join(F.xv+F.rv)
if mode=='om':
    s=W('r0')
    for j in (1,2,3): s=add(s,W('r%d'%j))
    for jr in range(4):
        print('rho_%d=1:'%jr,sing(F.fo+[W(v) for v in zero]+[W('r4'),s,F.eq('r%d'%jr,1)],el),flush=True)
    print('CAL rho=e_4:',sing(F.fo+[W(v) for v in zero]+[F.eq('r4',1)]+[W('r%d'%j) for j in range(4)],el)[:100],flush=True)
elif mode=='e0':
    res={}
    for xn in [v for v in F.xv if v not in zero]:
        out=sing(F.fo+[W(r) for r in F.rv]+[W(v) for v in zero]+[F.eq(xn,1)],el); res.setdefault(out,[]).append(xn)
    for k,v in res.items(): print('elimination ideal [%s] for charts %s'%(k[:300],v),flush=True)
    print('CAL x20=1 (d_0 released):',sing(F.fo+[W(r) for r in F.rv]+[W(v) for v in zero if v!='x20']+[F.eq('x20',1)],el)[:100])
