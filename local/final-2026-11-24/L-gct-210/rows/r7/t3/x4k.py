# X4-K generator (rows, round 7): 3-dim strongly level K = {h(s) = (A_0 s | ... | A_4 s)}, s in V (Walsh coordinates), sum A_j = 1,
# with exactly NC active columns (NC = 3, 4, 5; the others identically 0).  Equations: all s-coefficients of C_j(h(s)) - 24, j = 0..4
# (C_j = perm(J + h(s) without column j), actual 4x5 matrices h = H * Walsh).  Saturation by each active column ideal (A_j = 0).
# usage: python3 x4k.py P NC OUT       NC=3 is the calibration (non-unit: types (1,1,1), (2,2,1)); NC=4, 5: claim "unit".
import sys
P=sys.argv[1]; NC=int(sys.argv[2]); out=sys.argv[3]
free=NC-1
names=['a%d%d%d'%(j,r,c) for j in range(free) for r in range(3) for c in range(3)]
L=['ring R=%s,(%s,s1,s2,s3),dp; option(redSB); LIB "elim.lib";'%(P,','.join(names))]
L.append('matrix H[4][3]=1,1,1,1,-1,-1,-1,1,-1,-1,-1,1; matrix Id[3][3]=1,0,0,0,1,0,0,0,1; matrix S[3][1]=s1,s2,s3;')
L.append('list A;')
for j in range(free):
    L.append('matrix A%d[3][3]=%s; A[%d]=A%d;'%(j,','.join('a%d%d%d'%(j,r,c) for r in range(3) for c in range(3)),j+1,j))
L.append('matrix Al=Id;'+''.join(' Al=Al-A%d;'%j for j in range(free))+' A[%d]=Al;'%NC)
L.append('matrix Y[4][5]; int i; int j; int k; int c;')
L.append('for(j=1;j<=%d;j++){ matrix M=A[j]; matrix col=H*(M*S); for(i=1;i<=4;i++){ Y[i,j]=col[i,1]; } kill M; kill col; }'%NC)
L.append('proc perm4(matrix M){ poly s=0; int p1,p2,p3,p4;')
L.append(' for(p1=1;p1<=4;p1++){for(p2=1;p2<=4;p2++){ if(p2!=p1){ for(p3=1;p3<=4;p3++){ if((p3!=p1)&&(p3!=p2)){ p4=10-p1-p2-p3;')
L.append('   s=s+M[1,p1]*M[2,p2]*M[3,p3]*M[4,p4]; }}}}}')
L.append(' return(s);}')
L.append('ideal E;')
L.append('for(j=1;j<=5;j++){ matrix M[4][4]; c=0; for(k=1;k<=5;k++){ if(k!=j){ c++; for(i=1;i<=4;i++){ M[i,c]=1+Y[i,k]; } } } poly F=perm4(M)-24; matrix T=coef(F,s1*s2*s3); for(k=1;k<=ncols(T);k++){ E=E,T[2,k]; } kill M; kill F; kill T; }')
L.append('ring R2=%s,(%s),dp; option(redSB); LIB "elim.lib"; ideal E=imap(R,E); list A=imap(R,A);'%(P,','.join(names)))
L.append('ideal I=std(simplify(E,2+4+8)); printf("X4K NC=%d p=%s: %%s gens, dim %%s",size(I),dim(I));'%(NC,P))
L.append('for(j=1;j<=%d;j++){ matrix M=A[j]; ideal Jc=M[1,1],M[1,2],M[1,3],M[2,1],M[2,2],M[2,3],M[3,1],M[3,2],M[3,3]; I=sat(I,Jc); I=std(I); printf("  after sat by column %%s: dim %%s unit %%s",j,dim(I),(reduce(1,I)==0)); kill M; kill Jc; }'%NC)
L.append('printf("RESULT X4K NC=%d p=%s: unit %%s",(reduce(1,I)==0)); quit;'%(NC,P))
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
