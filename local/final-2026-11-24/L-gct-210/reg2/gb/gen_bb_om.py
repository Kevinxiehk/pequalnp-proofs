# Independent Omega/E_0 certificate (target 4) for the (2,2|1,1)BB curve: dim Omega <= 3 and dim E_0 <= 7 for every member, hence dim T_1 <= 10.
# Omega normalisation: rho_3 = rho_4 = 0, rho_0 + rho_1 + rho_2 = 0 (complement of span(e_3, e_4, 1_{012})), charts rho_0 = 1 / rho_1 = 1;
# X normalised modulo M + C d_1 (row 1 deletable): pivots x01, x02 (U_0), x13, x14 (U_1), x03 | x23 (x), x04 | x24 (x', localised), x20 (d_1).
import sys, subprocess; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
from famtool import *
chart=sys.argv[1]
def basis(R,V):
    c=R.const; Z=lambda: [[{} for _ in range(5)] for _ in range(4)]
    x=[c(1),{},V('p'),add(c(-1),scal(V('p'),-1))] if chart=='1' else [{},{},c(1),c(-1)]
    xp=[add(x[2],x[3],-1),{},add(x[3],x[0],-1),add(x[0],x[2],-1)]; Bs=[]
    for w in ([c(1),c(-1),{},{},{}],[c(1),{},c(-1),{},{}]):
        B=Z(); B[0]=list(w); Bs.append(B)
    for w in ([c(-1),c(-1),c(-1),c(4),c(-1)],[c(-1),c(-1),c(-1),c(-1),c(4)]):
        B=Z(); B[1]=list(w); Bs.append(B)
    B=Z()
    for i in range(4): B[i][3]=x[i]
    Bs.append(B)
    B=Z()
    for i in range(4): B[i][4]=xp[i]
    Bs.append(B)
    return Bs
F=Family(['p','z'],basis,6); W=F.W
def sing(polys,elim):
    lines=[to_str_Q(q,F.names) for q in polys]; lines=[l for l in lines if l!='0']
    open('/tmp/bbom.sing','w').write('ring R=0,(%s),dp;\noption(redSB);\nideal I=%s;\nideal J=eliminate(I,%s);\nJ=std(J);\nprint(J);\nquit;\n'%(','.join(F.names),',\n'.join(lines),elim))
    r=subprocess.run(['/usr/bin/Singular','-q'],stdin=open('/tmp/bbom.sing'),capture_output=True,text=True,timeout=900)
    return ' '.join(r.stdout.split())[:200]
el='*'.join(['z']+F.xv+F.rv)
xpent=[('04',add(F.c(1),scal(W('p'),2))),('24',add(F.c(-2),scal(W('p'),-1)))] if chart=='1' else [('04',F.c(2))]
for (pc,ent) in xpent:
    zero=['x01','x02','x13','x14','x03' if chart=='1' else 'x23','x'+pc,'x20']
    base=F.fo+[add(mul(W('z'),ent),F.c(-1))]+[W(v) for v in zero]
    for jr in (0,1):
        print('chart %s pivot %s Omega-test rho_%d=1:'%(chart,pc,jr),sing(base+[W('r3'),W('r4'),add(add(W('r0'),W('r1')),W('r2')),F.eq('r%d'%jr,1)],el),flush=True)
    print('  CAL rho=e_3:',sing(base+[F.eq('r3',1),W('r0'),W('r1'),W('r2'),W('r4')],el)[:60],flush=True)
    res={}
    for xn in [v for v in F.xv if v not in zero]:
        out=sing(base+[W(r) for r in F.rv]+[F.eq(xn,1)],el); res.setdefault(out,[]).append(xn)
    for k,v in res.items(): print('  E_0-test: [%s] for %d charts'%(k,len(v)),flush=True)
    print('  CAL d_1 released (x20 = 1):',sing(F.fo+[add(mul(W('z'),ent),F.c(-1))]+[W(v) for v in zero if v!='x20']+[W(r) for r in F.rv]+[F.eq('x20',1)],el)[:60],flush=True)
