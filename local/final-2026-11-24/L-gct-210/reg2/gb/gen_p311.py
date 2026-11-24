# Pattern (3,1|1,1) with ISOTROPIC m (NOTES-reg2 9.8): M = e_0 (x) {1,m}^perp (+) C e_1 m^T (+) C x e_c^T (+) C x' e_c'^T, x_0 = x'_0 = 0.
#  case A: m = (1, w, -1-w, 0, 0), w^2+w+1 = 0; c = 3, c' = 4; x = (0, x1, x2, -x1-x2), x' = (0, x2-x3, x3-x1, x1-x2) (= x cross 1 on rows 1..3);
#          charts x1 = 1 (x2 = p) and x1 = 0, x2 = 1.  Omega normalisation: complement of span(e_3, e_4, 1_{012}).
#  case B: m = (m0, m1, m2, m3, 0) isotropic sum-zero, c = 4 with x = (0,2,-1,-1), c' = 0 with x' = (0,0,1,-1); charts m0 = 1, (m0 = 0, m1 = 1).
#          Omega normalisation: complement of span(1, e_4).
#  X normalised modulo M + C d_0 (row 0 deletable); localisation z * (pivot entry) = 1 where the pivot entry is not constant.
import sys, subprocess; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
from famtool import *
case,chart=sys.argv[1],sys.argv[2]
def basis(R,V):
    c=R.const; Z=lambda: [[{} for _ in range(5)] for _ in range(4)]
    if case=='A':
        w=V('w'); m=[c(1),w,add(c(-1),scal(w,-1)),{},{}]
        if chart=='1': xs=[c(1),V('p')]
        else: xs=[{},c(1)]
        x=[{},xs[0],xs[1],scal(add(xs[0],xs[1]),-1)]
        xp=[{},add(x[2],x[3],-1),add(x[3],x[1],-1),add(x[1],x[2],-1)]
        cc,ccp=3,4
    else:
        if chart=='1': m=[c(1),V('m1'),V('m2'),scal(add(add(c(1),V('m1')),V('m2')),-1),{}]
        else: m=[{},c(1),V('m2'),scal(add(c(1),V('m2')),-1),{}]
        x=[{},c(2),c(-1),c(-1)]; xp=[{},{},c(1),c(-1)]; cc,ccp=4,0
    Bs=[]
    if case=='B' and chart=='0':
        # {1,m}^perp with m0 = 0, m1 = 1: g_k = m_k e_1 - e_k + (1-m_k) e_4 (k = 2,3), g_0 = e_0 - e_4
        for k in (2,3):
            B=Z(); B[0][1]=m[k]; B[0][k]=c(-1); B[0][4]=add(c(1),scal(m[k],-1)); Bs.append(B)
        B=Z(); B[0][0]=c(1); B[0][4]=c(-1); Bs.append(B)
    else:
        for k in (1,2,3):
            B=Z(); B[0][0]=m[k]; B[0][k]=c(-1); B[0][4]=add(c(1),scal(m[k],-1)); Bs.append(B)
    B=Z()
    for j in range(5): B[1][j]=m[j]
    Bs.append(B)
    B=Z()
    for i in range(4): B[i][cc]=x[i]
    Bs.append(B)
    B=Z()
    for i in range(4): B[i][ccp]=xp[i]
    Bs.append(B)
    return Bs
params={'A1':['w','p','z'],'A0':['w','z'],'B1':['m1','m2','z'],'B0':['m2','z']}[case+chart]
F=Family(params,basis,6); W=F.W
rel=[]
if case=='A': rel=[add(add(mul(W('w'),W('w')),W('w')),F.c(1))]
else:
    if chart=='1': mm=[F.c(1),W('m1'),W('m2'),scal(add(add(F.c(1),W('m1')),W('m2')),-1)]
    else: mm=[F.c(0),F.c(1),W('m2'),scal(add(F.c(1),W('m2')),-1)]
    q={}
    for v in mm: q=add(q,mul(v,v))
    rel=[q]
print('case %s chart %s: level equations %d'%(case,chart,len(F.level)),flush=True)
def sing(polys,elim):
    lines=[to_str_Q(q,F.names) for q in polys]; lines=[l for l in lines if l!='0']
    script='ring R=0,(%s),dp;\noption(redSB);\nideal I=%s;\nideal J=eliminate(I,%s);\nJ=std(J);\nprint(J);\nquit;\n'%(','.join(F.names),',\n'.join(lines),elim)
    open('/tmp/p311_%s%s.sing'%(case,chart),'w').write(script)
    r=subprocess.run(['/usr/bin/Singular','-q'],stdin=open('/tmp/p311_%s%s.sing'%(case,chart)),capture_output=True,text=True,timeout=900)
    return ' '.join(r.stdout.split())
el='*'.join(['z']+F.xv+F.rv)
# pivots: U_0 basis at x01,x02,x03 (A, B1) or x02,x03,x00 (B0); m^T at x10 (m0=1) or x11 (B0); column vectors; d_0 at x20 (A) / x21 (B)
if case=='A':
    xpent=[('x14',add(F.c(1),scal(W('p'),2))),('x24',add(F.c(-2),scal(W('p'),-1)))] if chart=='1' else [('x14',F.c(2))]
    base0=F.level+rel
    variants=[(['x01','x02','x03','x10','x13' if chart=='1' else 'x23',piv,'x20'],[add(mul(W('z'),ent),F.c(-1))]) for (piv,ent) in xpent]
    om_norm=[W('r3'),W('r4'),add(add(W('r0'),W('r1')),W('r2'))]; om_ch=['r0','r1']; cal=[W('r0'),W('r1'),W('r2'),F.eq('r3',1),W('r4')]
else:
    base0=F.level+rel
    zl=['x01','x02','x03','x10'] if chart=='1' else ['x02','x03','x00','x11']
    variants=[(zl+['x14','x20','x21'],[W('z')])]   # z unused: set z = 0 harmlessly by eliminating it
    om_norm=[W('r4'),add(add(add(W('r0'),W('r1')),W('r2')),W('r3'))]; om_ch=['r0','r1','r2','r3']; cal=[F.eq('r4',1),W('r0'),W('r1'),W('r2'),W('r3')]
for (zero,loc) in variants:
    base=base0+loc+F.fo+[W(v) for v in zero]
    for ch in om_ch: print('Omega-test pivots %s chart %s=1:'%(zero[5],ch),sing(base+om_norm+[F.eq(ch,1)],el)[:300],flush=True)
    print('  CAL Omega:',sing(base+cal,el)[:80],flush=True)
    res={}
    for xn in [v for v in F.xv if v not in zero]:
        out=sing(base+[W(r) for r in F.rv]+[F.eq(xn,1)],el); res.setdefault(out[:200],[]).append(xn)
    for k,v in res.items(): print('  E_0-test: [%s] for %d charts'%(k,len(v)),flush=True)
