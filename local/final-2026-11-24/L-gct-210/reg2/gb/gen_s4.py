# Special curve Sigma_4 of pattern (2,1,1|2) case (ii): b = (1, s, -1-s, 0), c = b x 1 = (1+2s, -2-s, 1-s, 0), a = (1,1,1,-3).
# Omega-test with the 3-dim normalisation rho_0 = rho_4 = 0, rho_1+rho_2+rho_3 = 0 (complement of span(1, e_0, 1_{123})), charts
# rho_1 = 1 / rho_2 = 1; X normalised modulo M + C d_0 (pivots x00,x10,x20,x34,x01,x11,x2jc; z*c_jc = 1).  Over Q (Singular eliminate).
# Also an E_0-test on the curve (redundant with the family test) and the calibration rho = 1_{123} - 3 e_4 ... (must be non-unit).
import sys, subprocess; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
from famtool import *
def basis(R,V):
    c=R.const; s=V('s'); Z=lambda: [[{} for _ in range(5)] for _ in range(4)]
    b=[c(1),s,add(c(-1),scal(s,-1)),{}]; cc=[add(c(1),scal(s,2)),add(c(-2),scal(s,-1)),add(c(1),scal(s,-1)),{}]; a=[c(1),c(1),c(1),c(-3)]
    B1=Z(); B1[0][0]=c(4)
    for j in range(1,5): B1[0][j]=c(-1)
    B2=Z(); B3=Z(); B4=Z()
    for j in range(4): B2[0][1+j]=a[j]; B3[1][1+j]=b[j]; B4[2][1+j]=cc[j]
    B5=Z(); B5[1][0]=c(1); B5[2][0]=c(-1)
    B6=Z(); B6[2][0]=c(1); B6[3][0]=c(-1)
    return [B1,B2,B3,B4,B5,B6]
F=Family(['s','z'],basis,6); W=F.W
print('level equations (must be none):',len(F.level),flush=True)
cj={1:add(F.c(1),scal(W('s'),2)),2:add(F.c(-2),scal(W('s'),-1))}
def sing(polys,elim):
    lines=[to_str_Q(q,F.names) for q in polys]; lines=[l for l in lines if l!='0']
    script='ring R=0,(%s),dp;\noption(redSB);\nideal I=%s;\nideal J=eliminate(I,%s);\nJ=std(J);\nprint(J);\nprint("FACTORS");\nint i; for(i=1;i<=size(J);i++){print(factorize(J[i]));}\nquit;\n'%(','.join(F.names),',\n'.join(lines),elim)
    open('/tmp/s4.sing','w').write(script)
    r=subprocess.run(['/usr/bin/Singular','-q'],stdin=open('/tmp/s4.sing'),capture_output=True,text=True,timeout=600)
    return ' '.join(r.stdout.split())
el='*'.join(['z']+F.xv+F.rv)
for jc in (1,2):
    zero=['x00','x10','x20','x34','x01','x11','x2%d'%jc]
    base=F.fo+[add(mul(W('z'),cj[jc]),F.c(-1))]+[W(v) for v in zero]
    for jr in (1,2):
        print('jc=%d rho_%d=1:'%(jc,jr),sing(base+[W('r0'),W('r4'),add(add(W('r1'),W('r2')),W('r3')),F.eq('r%d'%jr,1)],el),flush=True)
    print('jc=%d CAL rho=(0,1,1,1,0):'%jc,sing(base+[W('r0'),W('r4'),F.eq('r1',1),F.eq('r2',1),F.eq('r3',1)],el)[:120],flush=True)
