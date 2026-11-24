# verify2 r12: independent generator for stage3 34(F) ((alpha1), |supp W| = 3).  W = v (1, l1, -1-l1, 0, 0)^T, v = chi_1; e = chi_2/2 (unit, perp v);
# A_j = v (x) psi_j + eps_j rho e (x) f (j <= 2, psi_0 = 0 by the Z-gauge), A_3 = n (x) phi + eps_3 rho e3 (x) f, n = w(tau), e3 = chi_2/2 - tau chi_3
# (or n = chi_3, e3 = chi_2/2); y_j = (s + A_j s)/2 + mu z_j, y_4 = -s - (1/2) sum_{j<=3} A_j s; q rho l1 (1+l1) = 1; f chart f_c = 1.
# Every element Y_s + mu Z must have defect in C m0.  s = (s0,s1,s2,-s0-s1-s2).  usage: SIGNS(4 chars +/-) FCHART NCHART(w|c3) TDEG
import sys, itertools, sympy as sp
I=sp.I
chi=[[I**(k*r) for r in range(4)] for k in range(4)]
sg=[1 if c=='+' else -1 for c in sys.argv[1]]; fc=int(sys.argv[2]); nch=sys.argv[3]; TDEG=int(sys.argv[4])
q=lambda e: str(sp.expand(e)).replace('**','^')
v=chi[1]; e2=chi[2]   # 2e = chi_2 (halves applied to whole poly terms to avoid Singular int division)
if nch=='w':
    n=['(%s)+2*tau*(%s)-2*tau^2*(%s)'%(q(chi[1][r]),q(chi[2][r]),q(chi[3][r])) for r in range(4)]
    e3=['((%s)-2*tau*(%s))'%(q(chi[2][r]),q(chi[3][r])) for r in range(4)]   # = 2 e3
else:
    n=[q(chi[3][r]) for r in range(4)]; e3=[q(e2[r]) for r in range(4)]   # = 2 e3
V4=lambda nm:['%s0'%nm,'%s1'%nm,'%s2'%nm,'(-%s0-%s1-%s2)'%(nm,nm,nm)]
S=['s0','s1','s2','(-s0-s1-s2)']
f3=['1' if i==fc else 'f%d'%i for i in range(3)]; f=f3+['(-(%s)-(%s)-(%s))'%tuple(f3)]
psi={0:['0']*4,1:V4('pa'),2:V4('pb')}; phi=V4('ph')
dot=lambda a,b:'('+'+'.join('(%s)*(%s)'%(x,y) for x,y in zip(a,b))+')'
fs=dot(f,S); lv=['1','l1','(-1-l1)']
vars_=['pa0','pa1','pa2','pb0','pb1','pb2','ph0','ph1','ph2']+['f%d'%i for i in range(3) if i!=fc]+['rho','l1','qq']+(['tau'] if nch=='w' else [])
L=['ring R=(0,I),(%s,t,s0,s1,s2,mu),dp; minpoly=I^2+1;'%','.join(vars_),'matrix Y[4][5]; poly fs=%s;'%fs]
for j in range(3): L.append('poly c%d=%s;'%(j,dot(psi[j],S)))
L.append('poly c3=%s;'%dot(phi,S))
for r in range(4):
    Ajs=[]
    for j in range(3):
        a='c%d*(%s)+(%d)*rho*fs*(%s)/2'%(j,q(v[r]),sg[j],q(e2[r])); Ajs.append(a)
        L.append('Y[%d,%d]=((%s)+%s)/2+mu*(%s)*(%s);'%(r+1,j+1,S[r],a,lv[j],q(v[r])))
    a3='c3*(%s)+(%d)*rho*fs*(%s)/2'%(n[r],sg[3],e3[r]); Ajs.append(a3)
    L.append('Y[%d,4]=((%s)+%s)/2;'%(r+1,S[r],a3))
    L.append('Y[%d,5]=-(%s)-(%s)/2;'%(r+1,S[r],'+'.join('(%s)'%x for x in Ajs)))
P4=list(itertools.permutations(range(4)))
for jd in range(5):
    cols=[c for c in range(5) if c!=jd]
    L.append('poly C%d=%s;'%(jd,'+'.join('*'.join('(1+t*Y[%d,%d])'%(r+1,cols[p[r]]+1) for r in range(4)) for p in P4)))
L.append('ideal D=C1-C0,C2-C0,C3-C0,C4+4*C0-120; ideal E; int k; int j; matrix M; poly g;')
wt=','.join(['0']*len(vars_)+['1','0','0','0','0'])
L.append('for(k=1;k<=4;k++){ g=jet(D[k],%d,intvec(%s)); M=coef(g,t*s0*s1*s2*mu); for(j=1;j<=ncols(M);j++){E=E,M[2,j];} }'%(TDEG,wt))
L.append('E=E,qq*rho*l1*(1+l1)-1;')
L.append('ring R2=(0,I),(%s),dp; minpoly=I^2+1; ideal E=imap(R,E); E=simplify(E,2); option(redSB); ideal G=std(E);'%','.join(vars_))
L.append('printf("A1S3MINE %s f%d %s tdeg %d: dim %%s unit %%s",dim(G),reduce(1,G)==0); quit;'%(sys.argv[1],fc,nch,TDEG))
open('a1s3m_%s_%d_%s_%d.sing'%(sys.argv[1],fc,nch,TDEG),'w').write('\n'.join(L)+'\n')
