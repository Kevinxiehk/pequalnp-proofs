# X4K-sign (rows, round 8): 3-dim strongly level K on exactly NC active columns (Walsh coords, A_0..A_{NC-1}, sum = 1), split by the
# SIGN PATTERN eps_j = det(B_j), B_j = 1 - 2A_j.  Columns with eps_j = -1 can never vanish (A_j = 0 => B_j = 1 => det +1), so only the
# eps = +1 columns are saturated.  DEG = 3: degree-2 and degree-3 conditions only (a RELAXATION: unit => unit with the quartic too);
# DEG = 4: all conditions.   usage: python3 x4ks.py P NC SIGNS DEG OUT     (SIGNS e.g. '----', '+---'; sorted '+' first WLOG)
import sys
P=sys.argv[1]; NC=int(sys.argv[2]); SG=sys.argv[3]; DEG=int(sys.argv[4]); out=sys.argv[5]; assert len(SG)==NC
TR=len(sys.argv)>6 and sys.argv[6]=='tr'   # add the derived LINEAR trace equations tr A_j = kappa_j (R8.8; NC = 4, rank-4 frame patterns only)
free=NC-1
names=['a%d%d%d'%(j,r,c) for j in range(free) for r in range(3) for c in range(3)]
L=['ring R=%s,(%s,s1,s2,s3),dp; option(redSB);'%(P,','.join(names))]
L.append('matrix H[4][3]=1,1,1,1,-1,-1,-1,1,-1,-1,-1,1; matrix Id[3][3]=1,0,0,0,1,0,0,0,1; matrix S[3][1]=s1,s2,s3; list A;')
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
L.append('for(j=1;j<=5;j++){ matrix M[4][4]; c=0; for(k=1;k<=5;k++){ if(k!=j){ c++; for(i=1;i<=4;i++){ M[i,c]=1+Y[i,k]; } } } poly F=perm4(M)-24; matrix T=coef(F,s1*s2*s3); for(k=1;k<=ncols(T);k++){ if(deg(T[1,k])<=%d){ E=E,T[2,k]; } } kill M; kill F; kill T; }'%DEG)
for j in range(NC):
    L.append('matrix Bm%d=Id-2*A[%d]; E=E,det(Bm%d)-(%d);'%(j,j+1,j,1 if SG[j]=='+' else -1))
if TR:
    assert NC==4
    s_=sum(1 if x=='+' else -1 for x in SG); cc=(s_-2)/2; assert cc not in (0,-4)
    from fractions import Fraction as Fr
    for j in range(NC):
        e=1 if SG[j]=='+' else -1; t2=Fr(4)+Fr(cc).limit_denominator(); t2=(4+Fr(cc).limit_denominator())*(1-Fr(cc).limit_denominator()*e/2)
        trB=e*(t2-1); kap=(3-trB)/2
        L.append('E=E,trace(A[%d])-(%s);'%(j+1,str(kap)))
L.append('ring R2=%s,(%s),dp; option(redSB); LIB "elim.lib"; ideal E=imap(R,E); list A=imap(R,A);'%(P,','.join(names)))
L.append('ideal I=std(simplify(E,2+4+8)); printf("X4KS NC=%d signs %s deg<=%d p=%s: dim %%s unit %%s size %%s",dim(I),(reduce(1,I)==0),size(I));'%(NC,SG,DEG,P))
for j in range(NC):
    if SG[j]=='+':
        L.append('matrix M%d=A[%d]; ideal Jc%d=M%d[1,1],M%d[1,2],M%d[1,3],M%d[2,1],M%d[2,2],M%d[2,3],M%d[3,1],M%d[3,2],M%d[3,3]; I=std(sat(I,Jc%d)); printf("  sat column %d: dim %%s unit %%s",dim(I),(reduce(1,I)==0));'%((j,j+1)+(j,)*10+(j,j)))
L.append('printf("RESULT X4KS NC=%d signs %s deg<=%d p=%s: unit %%s",(reduce(1,I)==0)); quit;'%(NC,SG,DEG,P))
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
