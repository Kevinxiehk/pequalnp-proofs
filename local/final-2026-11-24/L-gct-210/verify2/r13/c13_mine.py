# verify2 r13: independent generator for stage3 35(C) cases (c1), (c3) of (alpha1) |supp W| = 2 (system on K_f = {Y(s) + mu Z : s in f^perp}).
# (c1): n_2 = v, gam_2 = sig, n_3 special (= chi_1 WLOG), v free isotropic (w(tau) | chi_3); (c3): v special (= chi_1), n_2 = n_3 = n free isotropic,
# gam_2 = gam_3 = gam.  y_0 = s/2 + al0 v, y_1 = s/2 + (sig - al0) v, y_k = s/2 + gam_k n_k, y_4 = -s - sig v - gam_2 n_2 - gam_3 n_3.
# f^perp in Gr(2,V) charts (first three coordinates); sig, gam linear on f^perp (values on the chart basis); u det(sig, gam) = 1.
# usage: CASE (c1|c3) CHART (0|1|2) FREE (w|c3) TDEG
import sys, itertools, sympy as sp
I=sp.I
chi=[[I**(k*r) for r in range(4)] for k in range(4)]
case,ch,fr,TDEG=sys.argv[1],int(sys.argv[2]),sys.argv[3],int(sys.argv[4])
q=lambda e: str(sp.expand(e)).replace('**','^')
spec=[q(x) for x in chi[1]]
free=['(%s)+2*tau*(%s)-2*tau^2*(%s)'%(q(chi[1][r]),q(chi[2][r]),q(chi[3][r])) for r in range(4)] if fr=='w' else [q(x) for x in chi[3]]
basisV={0:(['1','0','pa'],['0','1','pb']),1:(['1','pa','0'],['0','pb','1']),2:(['pa','1','0'],['pb','0','1'])}[ch]
full4=lambda v3: v3+['(-(%s)-(%s)-(%s))'%tuple(v3)]
sa,sb=full4(basisV[0]),full4(basisV[1])
S=['(x1*(%s)+x2*(%s))'%(sa[r],sb[r]) for r in range(4)]
sig='(x1*sa+x2*sb)'; gam='(x1*ga+x2*gb)'
if case=='c1': v=free; n2=free; n3=spec; g2=sig; g3=gam
else: v=spec; n2=free; n3=free; g2=gam; g3=gam
vars_=['pa','pb','sa','sb','ga','gb','u']+(['tau'] if fr=='w' else [])
L=['ring R=(0,I),(%s,t,x1,x2,al0),dp; minpoly=I^2+1;'%','.join(vars_),'matrix Y[4][5];']
for r in range(4):
    L.append('Y[%d,1]=(%s)/2+al0*(%s);'%(r+1,S[r],v[r]))
    L.append('Y[%d,2]=(%s)/2+(%s-al0)*(%s);'%(r+1,S[r],sig,v[r]))
    L.append('Y[%d,3]=(%s)/2+%s*(%s);'%(r+1,S[r],g2,n2[r]))
    L.append('Y[%d,4]=(%s)/2+%s*(%s);'%(r+1,S[r],g3,n3[r]))
    L.append('Y[%d,5]=-(%s)-%s*(%s)-%s*(%s)-%s*(%s);'%(r+1,S[r],sig,v[r],g2,n2[r],g3,n3[r]))
P4=list(itertools.permutations(range(4)))
for jd in range(5):
    cols=[c for c in range(5) if c!=jd]
    L.append('poly C%d=%s;'%(jd,'+'.join('*'.join('(1+t*Y[%d,%d])'%(r+1,cols[p[r]]+1) for r in range(4)) for p in P4)))
L.append('ideal D=C1-C0,C2-C0,C3-C0,C4+4*C0-120; ideal E; int k; int j; matrix M; poly g;')
wt=','.join(['0']*len(vars_)+['1','0','0','0'])
L.append('for(k=1;k<=4;k++){ g=jet(D[k],%d,intvec(%s)); M=coef(g,t*x1*x2*al0); for(j=1;j<=ncols(M);j++){E=E,M[2,j];} }'%(TDEG,wt))
L.append('E=E,u*(sa*gb-sb*ga)-1;')
L.append('ring R2=(0,I),(%s),dp; minpoly=I^2+1; ideal E=imap(R,E); E=simplify(E,2); option(redSB); ideal G=std(E);'%','.join(vars_))
L.append('printf("C13MINE %s chart %d %s tdeg %d: dim %%s unit %%s",dim(G),reduce(1,G)==0); quit;'%(case,ch,fr,TDEG))
open('c13m_%s_%d_%s_%d.sing'%(case,ch,fr,TDEG),'w').write('\n'.join(L)+'\n')
