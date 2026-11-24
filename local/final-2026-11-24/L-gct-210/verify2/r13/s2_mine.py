# verify2 r13: independent generator for stage3 LEMMA S2: Y = a (x) (1,1,1,1,-2) + b2 (x) (e_2 - e_4) + b3 (x) (e_3 - e_4) in standard
# coordinates of C^4 (a sum-zero), b2 = w(t2), b3 = be w(t3) (w(t) = chi_1 + 2t chi_2 - 2t^2 chi_3), line defect in C m0 (all t-coefficients).
# usage: MODE (neq|par|cal) ACHART (none|0|1|2)   neq: u be (t2-t3) = 1; par: t3 = t2, u be (be-1) = 1; cal: u be = 1 (must be non-unit)
import sys, itertools, sympy as sp
I=sp.I
chi=[[I**(k*r) for r in range(4)] for k in range(4)]
mode,ach=sys.argv[1],sys.argv[2]
q=lambda e: str(sp.expand(e)).replace('**','^')
def w(t): return ['(%s)+2*%s*(%s)-2*%s^2*(%s)'%(q(chi[1][r]),t,q(chi[2][r]),t,q(chi[3][r])) for r in range(4)]
a=['a0','a1','a2','(-a0-a1-a2)']
b2=w('t2'); b3=['be*(%s)'%x for x in w('t2' if mode=='par' else 't3')]
mm=[1,1,1,1,-2]
L=['ring R=(0,I),(a0,a1,a2,t2,t3,be,u,v,t),dp; minpoly=I^2+1;','matrix Y[4][5];']
for r in range(4):
    for j in range(5):
        e='(%d)*%s'%(mm[j],a[r])
        if j==2: e+='+(%s)'%b2[r]
        if j==3: e+='+(%s)'%b3[r]
        if j==4: e+='-(%s)-(%s)'%(b2[r],b3[r])
        L.append('Y[%d,%d]=%s;'%(r+1,j+1,e))
P4=list(itertools.permutations(range(4)))
for jd in range(5):
    cols=[c for c in range(5) if c!=jd]
    L.append('poly C%d=%s;'%(jd,'+'.join('*'.join('(1+t*Y[%d,%d])'%(r+1,cols[p[r]]+1) for r in range(4)) for p in P4)))
L.append('ideal D=C1-C0,C2-C0,C3-C0,C4+4*C0-120; ideal E; int k; int j; matrix M;')
L.append('for(k=1;k<=4;k++){ M=coef(D[k],t); for(j=1;j<=ncols(M);j++){E=E,M[2,j];} }')
rab={'neq':'u*be*(t2-t3)-1','par':'u*be*(be-1)-1','cal':'u*be-1'}[mode]
L.append('E=E,%s;'%rab)
if mode=='par': L.append('E=E,t3;')   # t3 unused
if ach!='none': L.append('E=E,v*a%s-1;'%ach)
else: L.append('E=E,v;')
L.append('ring R2=(0,I),(a0,a1,a2,t2,t3,be,u,v),dp; minpoly=I^2+1; ideal E=imap(R,E); E=simplify(E,2); option(redSB); ideal G=std(E);')
L.append('printf("S2MINE %s achart %s: dim %%s unit %%s",dim(G),reduce(1,G)==0); quit;'%(mode,ach))
open('s2m_%s_%s.sing'%(mode,ach),'w').write('\n'.join(L)+'\n')
