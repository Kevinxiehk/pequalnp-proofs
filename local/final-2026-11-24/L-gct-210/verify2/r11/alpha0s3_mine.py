# verify2 r11: independent generator for stage3 33(H) (alpha0, |supp W| = 3): W = v (1, l1, -1-l1) on columns 0,1,2 (z_3 = z_4 = 0), v special;
# column 3 off-support: y_3 = (s + <phi_3,s> n_3)/2, n_3 special; y_j = (s + <phi_j,s> z_j)/2 + mu z_j (j <= 2), phi_0 = 0 (gauge over supp only);
# y_4 = -s - (1/2) sum_{j<=3} <phi_j,s> N_j.  Rabinowitsch q l1 (1+l1) = 1.  s = (s0,s1,s2,-s0-s1-s2).  usage: IV IN TDEG
import sys, itertools, sympy as sp
I=sp.I
base=[1,I,-1,-I]; lines=[]
for p in itertools.permutations(range(4)):
    v=sp.Matrix([base[k] for k in p])
    if not any(sp.Matrix.hstack(v,w).rank(simplify=True)<2 for w in lines): lines.append(v)
iv,inn,TDEG=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3])
q=lambda e: str(sp.expand(e)).replace('**','^')
v=lines[iv]; n3=lines[inn]
L=['ring R=(0,I),(f10,f11,f12,f20,f21,f22,f30,f31,f32,l1,qq,t,s0,s1,s2,mu),dp; minpoly=I^2+1;','poly S0=s0; poly S1=s1; poly S2=s2; poly S3=-s0-s1-s2;']
phi={0:['0']*4}
for k in (1,2,3): phi[k]=['f%d0'%k,'f%d1'%k,'f%d2'%k,'(-f%d0-f%d1-f%d2)'%(k,k,k)]
Sv=['S0','S1','S2','S3']; lv=['1','l1','(-1-l1)']
for j in range(4): L.append('poly c%d=%s;'%(j,'+'.join('(%s)*%s'%(phi[j][r],Sv[r]) for r in range(4))))
L.append('matrix Y[4][5];')
for r in range(4):
    for j in range(3): L.append('Y[%d,%d]=(%s+c%d*(%s)*(%s))/2+mu*(%s)*(%s);'%(r+1,j+1,Sv[r],j,lv[j],q(v[r]),lv[j],q(v[r])))
    L.append('Y[%d,4]=(%s+c3*(%s))/2;'%(r+1,Sv[r],q(n3[r])))
    L.append('Y[%d,5]=-%s-(%s+c3*(%s))/2;'%(r+1,Sv[r],'+'.join('c%d*(%s)*(%s)'%(j,lv[j],q(v[r])) for j in range(3)),q(n3[r])))
P4=list(itertools.permutations(range(4)))
for jd in range(5):
    cols=[c for c in range(5) if c!=jd]
    L.append('poly C%d=%s;'%(jd,'+'.join('*'.join('(1+t*Y[%d,%d])'%(r+1,cols[p[r]]+1) for r in range(4)) for p in P4)))
L.append('ideal D=C1-C0,C2-C0,C3-C0,C4+4*C0-120; ideal E; int k; int j; matrix M; poly g;')
L.append('for(k=1;k<=4;k++){ g=jet(D[k],%d,intvec(0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0)); M=coef(g,t*s0*s1*s2*mu); for(j=1;j<=ncols(M);j++){E=E,M[2,j];} }'%TDEG)
L.append('E=E,qq*l1*(1+l1)-1;')
L.append('ring R2=(0,I),(f10,f11,f12,f20,f21,f22,f30,f31,f32,l1,qq),dp; minpoly=I^2+1; ideal E=imap(R,E); E=simplify(E,2); option(redSB); ideal G=std(E);')
L.append('printf("S3MINE v%d n%d tdeg %d: dim %%s unit %%s",dim(G),reduce(1,G)==0); quit;'%(iv,inn,TDEG))
open('a0s3mine_%d_%d_%d.sing'%(iv,inn,TDEG),'w').write('\n'.join(L)+'\n')
