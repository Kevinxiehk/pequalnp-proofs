# verify2 r11: independent generator for stage3 33(G) (alpha0, |supp W| = 4). K = {Y_s + mu Z : s in V}, Z = [W|0],
# y_j = (s + <phi_j,s> z_j)/2 (j <= 3), y_4 = -s - (1/2) sum_j <phi_j,s> z_j, phi_0 = 0 (gauge), phi_k in V (k = 1,2,3).
# Condition: every element of K has its line defect in C m0, m0 = (1,1,1,1,-4).  s = (s0,s1,s2,-s0-s1-s2) (different param from stage3).
# usage: alpha0_mine.py SUBSET TDEG   (TDEG = max t-degree kept: 4 = full system; smaller = calibration relaxation)
import sys, itertools, sympy as sp
I=sp.I
base=[1,I,-1,-I]; lines=[]
for p in itertools.permutations(range(4)):
    v=sp.Matrix([base[k] for k in p])
    if not any(sp.Matrix.hstack(v,w).rank(simplify=True)<2 for w in lines): lines.append(v)
S=tuple(int(c) for c in sys.argv[1]); TDEG=int(sys.argv[2])
V=sp.Matrix.hstack(*[lines[c] for c in S]); lam=V.nullspace()[0]
W=V*sp.diag(*lam)
def q(e): return str(sp.expand(e)).replace('**','^')
P4=list(itertools.permutations(range(4)))
L=['ring R=(0,I),(f10,f11,f12,f20,f21,f22,f30,f31,f32,t,s0,s1,s2,mu),dp; minpoly=I^2+1;',
   'poly S0=s0; poly S1=s1; poly S2=s2; poly S3=-s0-s1-s2;']
phi={0:['0','0','0','0']}
for k in (1,2,3): phi[k]=['f%d0'%k,'f%d1'%k,'f%d2'%k,'(-f%d0-f%d1-f%d2)'%(k,k,k)]
Sv=['S0','S1','S2','S3']
for j in range(4): L.append('poly c%d=%s;'%(j,'+'.join('(%s)*%s'%(phi[j][r],Sv[r]) for r in range(4))))
L.append('matrix Y[4][5];')
for r in range(4):
    for j in range(4): L.append('Y[%d,%d]=(%s+c%d*(%s))/2+mu*(%s);'%(r+1,j+1,Sv[r],j,q(W[r,j]),q(W[r,j])))
    L.append('Y[%d,5]=-%s-(%s)/2;'%(r+1,Sv[r],'+'.join('c%d*(%s)'%(j,q(W[r,j])) for j in range(4))))
for jd in range(5):
    cols=[c for c in range(5) if c!=jd]
    L.append('poly C%d=%s;'%(jd,'+'.join('*'.join('(1+t*Y[%d,%d])'%(r+1,cols[p[r]]+1) for r in range(4)) for p in P4)))
L.append('ideal D=C1-C0,C2-C0,C3-C0,C4+4*C0-120; ideal E; int k; int j; matrix M; poly g;')
L.append('for(k=1;k<=4;k++){ g=jet(D[k],%d,intvec(0,0,0,0,0,0,0,0,0,1,0,0,0,0)); M=coef(g,t*s0*s1*s2*mu); for(j=1;j<=ncols(M);j++){E=E,M[2,j];} }'%TDEG)
L.append('ring R2=(0,I),(f10,f11,f12,f20,f21,f22,f30,f31,f32),dp; minpoly=I^2+1; ideal E=imap(R,E); E=simplify(E,2); option(redSB); ideal G=std(E);')
L.append('printf("ALPHA0-mine subset %s tdeg %d: %%s equations, dim %%s, unit %%s",size(E),dim(G),reduce(1,G)==0); quit;'%(sys.argv[1],TDEG))
open('a0mine_%s_%d.sing'%(sys.argv[1],TDEG),'w').write('\n'.join(L)+'\n')
