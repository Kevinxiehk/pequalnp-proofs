# Principal (5,1), kernel types (3) and (2,1), ANY m (rows, round 7).  Normal form (R7.4): m_a = 0, m_b = 1 (columns a,b,c,d,e = 0..4),
# N = {a m^T : a in A_N}, A_N a 2-plane in C^4 (rank-one row-centred part).
#   type 3 : K = F_a = {x e_a^T : x in V}
#   type 21: K = {(x_b cross w) e_a^T + s0 x_b e_b^T} (Walsh cross product; x_b non-isotropic, X_a = x_b^perp)
# Equations: all identity-variable coefficients of C_j(Y) - 24 - m_j (C_1(Y) - 24), j = 0,2,3,4.  A_N = row space of [a1; a2] in the
# chart where the 2x2 minor on coordinates (k,l) is the identity.  type 21 also: chart x_b[q] = 1, saturation by <x_b,x_b>.
# usage: python3 x51r.py P TYPE KL [Q] OUT     (KL = two digits 0..3, k<l; Q = 1..3 for type 21)
import sys
CAL=sys.argv[-1]=='cal'
if CAL: sys.argv=sys.argv[:-1]
P=sys.argv[1]; T=sys.argv[2]; KL=sys.argv[3]
if T=='21': Q=int(sys.argv[4]); out=sys.argv[5]
else: Q=None; out=sys.argv[4]
k,l=int(KL[0]),int(KL[1])
idv='s1,s2,s3,s0,ph,et'
unk=['a1%d'%i for i in range(4)]+['a2%d'%i for i in range(4)]+['mc','md']+(['xb1','xb2','xb3'] if T=='21' else [])
L=['ring R=%s,(%s,%s),dp; option(redSB);'%(P,idv,','.join(unk))]
L.append('matrix H[4][3]=1,1,1,1,-1,-1,-1,1,-1,-1,-1,1;')
L.append('list mm=0,1,mc,md,-1-mc-md;')
L.append('matrix A1[4][1]=a10,a11,a12,a13; matrix A2[4][1]=a20,a21,a22,a23;')
if T=='3':
    L.append('matrix W[3][1]=s1,s2,s3; matrix ka=H*W; matrix kb[4][1];')
else:
    L.append('matrix xb[3][1]=xb1,xb2,xb3; matrix w[3][1]=s1,s2,s3;')
    L.append('matrix cr[3][1]=xb[2,1]*w[3,1]-xb[3,1]*w[2,1],xb[3,1]*w[1,1]-xb[1,1]*w[3,1],xb[1,1]*w[2,1]-xb[2,1]*w[1,1];')
    L.append('matrix ka=H*cr; matrix kb=s0*(H*xb);')
L.append('matrix Y[4][5]; int i; int j; int kk; int c;')
L.append('for(i=1;i<=4;i++){ poly ai=ph*A1[i,1]+et*A2[i,1]; for(j=1;j<=5;j++){ Y[i,j]=ai*mm[j]; } Y[i,1]=Y[i,1]+ka[i,1]; Y[i,2]=Y[i,2]+kb[i,1]; kill ai; }')
L.append('proc perm4(matrix M){ poly s=0; int p1,p2,p3,p4;')
L.append(' for(p1=1;p1<=4;p1++){for(p2=1;p2<=4;p2++){ if(p2!=p1){ for(p3=1;p3<=4;p3++){ if((p3!=p1)&&(p3!=p2)){ p4=10-p1-p2-p3;')
L.append('   s=s+M[1,p1]*M[2,p2]*M[3,p3]*M[4,p4]; }}}}}')
L.append(' return(s);}')
L.append('list CC;')
L.append('for(j=1;j<=5;j++){ matrix M[4][4]; c=0; for(kk=1;kk<=5;kk++){ if(kk!=j){ c++; for(i=1;i<=4;i++){ M[i,c]=1+Y[i,kk]; } } } CC[j]=perm4(M)-24; kill M; }')
L.append('ideal E;')
L.append('for(j=1;j<=5;j++){ if(j!=2){ poly F=CC[j]-mm[j]*CC[2]; matrix TT=coef(F,s1*s2*s3*s0*ph*et); for(kk=1;kk<=ncols(TT);kk++){ E=E,TT[2,kk]; } kill F; kill TT; } }')
L.append('ring R2=%s,(%s),dp; option(redSB); LIB "elim.lib"; ideal E=imap(R,E);'%(P,','.join(unk)))
ch=['a1%d-1'%k,'a1%d'%l,'a2%d'%k,'a2%d-1'%l] if not CAL else ['a1%d-1'%k]+['a2%d'%i for i in range(4)]
if T=='21': ch.append('xb%d-1'%Q)
L.append('ideal I=E,%s; I=std(simplify(I,2+4+8));'%','.join(ch))
L.append('printf("X51R%s type %s chart %s%s p=%s: dim %%s unit %%s size %%s",dim(I),(reduce(1,I)==0),size(I));'%(' CAL' if CAL else '',T,KL,'' if Q is None else ' q%d'%Q,P))
if T=='21':
    L.append('I=sat(I,ideal(xb1^2+xb2^2+xb3^2)); I=std(I); printf("   after sat by <xb,xb>: dim %s unit %s",dim(I),(reduce(1,I)==0));')
L.append('if(size(I)<30){print(I);}')
L.append('quit;')
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
