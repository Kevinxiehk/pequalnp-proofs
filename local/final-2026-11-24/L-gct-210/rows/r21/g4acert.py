# EXACT certificate for G4-A case (a) (R21.9'''): plane x1 = 0, u = (0,1,e), w = sg*q3*(0,1,-e) (e = +-i, sg = +-1, q3^2 = 3).
# Points: s in {1, -1, rr, rr'} with rr, rr' the roots of i v3 z^2 + 2 v2 z + i v3 (v = 2u - w); rr' = -2 v2/(i v3) - rr.
# be, al by Cramer, scaled by D = det[c(s2), c(s3), c(s4)] (Rabinowitsch rz*D - 1 forces distinct points).  Conditions: all (t, ka)
# coefficients of perm(J + t Y_ka \ col j) - 24 (j = 1..5), Y_ka = e1 + ka n (scaled).  UNIT <=> no strongly level plane here.
import sys
e,sg,out=sys.argv[1],int(sys.argv[2]),sys.argv[3]
L=['ring R=0,(t,ka,rr,rz,q3,ii),dp; option(redSB);',
 'matrix H[4][3]=1,1,1,1,-1,-1,-1,1,-1,-1,-1,1; int i; int j; int k; int c;',
 'proc cc(poly s){ matrix v[3][1]=s^2-1,ii*(s^2+1),2*s; return(v); }',
 'poly e=%s; int sg=%d;'%(e,sg),
 'matrix u[3][1]=0,1,e; matrix w[3][1]=0,sg*q3,-sg*q3*e; matrix v=2*u-w;',
 'ideal REL=ii^2+1,q3^2-3,ii*v[3,1]*rr^2+2*v[2,1]*rr+ii*v[3,1];',
 'poly rq=-ii*v[3,1]*rr-2*v[2,1];',   # (i v3) * rr' = -2 v2 - i v3 rr  -> use scaled point via homogeneous c
 # rr' = rq/(i v3): homogeneous conic point c(S,T) = (S^2-T^2, i(S^2+T^2), 2ST) with S = rq, T = i v3
 'proc ch(poly S, poly T){ matrix v[3][1]=S^2-T^2,ii*(S^2+T^2),2*S*T; return(v); }',
 'matrix C1=cc(1); matrix C2=cc(-1); matrix C3=cc(rr); matrix C4=ch(rq,ii*v[3,1]);',
 'proc det3(matrix a, matrix b, matrix d){ return(a[1,1]*(b[2,1]*d[3,1]-b[3,1]*d[2,1])-a[2,1]*(b[1,1]*d[3,1]-b[3,1]*d[1,1])+a[3,1]*(b[1,1]*d[2,1]-b[2,1]*d[1,1])); }',
 'poly D=det3(C2,C3,C4); matrix mC1=-C1; matrix z=3*u-w;',
 # be_1 = D, be_2..4 = Cramer numerators for sum be_k C_k = 0 ; al_1 = 0, al_2..4 for sum al_k C_k = z (all scaled by D)
 'poly b1=D; poly b2=det3(mC1,C3,C4); poly b3=det3(C2,mC1,C4); poly b4=det3(C2,C3,mC1);',
 'poly a2=det3(z,C3,C4); poly a3=det3(C2,z,C4); poly a4=det3(C2,C3,z);',
 'matrix CHK1=b1*C1+b2*C2+b3*C3+b4*C4; matrix CHK2=a2*C2+a3*C3+a4*C4-D*z;',
 'ideal CH=reduce(ideal(CHK1[1,1],CHK1[2,1],CHK1[3,1],CHK2[1,1],CHK2[2,1],CHK2[3,1]),std(REL)); printf("linear relations hold: %s",size(CH)==0);',
 'list Cs=C1,C2,C3,C4; list bs=b1,b2,b3,b4; list as=0,a2,a3,a4;',
 'matrix Y[4][5]; matrix col[3][1]; matrix c4[4][1];',
 'for(k=1;k<=4;k++){ col=(D*u-as[k]*Cs[k])/2-ka*bs[k]*Cs[k]/2; c4=H*col; for(i=1;i<=4;i++){ Y[i,k]=c4[i,1]; } }',
 'col=D*(u-w)/2; c4=H*col; for(i=1;i<=4;i++){ Y[i,5]=c4[i,1]; }',
 'proc perm4(matrix M){ poly s=0; int a1,a2,a3,a4; for(a1=1;a1<=4;a1++){for(a2=1;a2<=4;a2++){ if(a2!=a1){ for(a3=1;a3<=4;a3++){ if((a3!=a1)&&(a3!=a2)){ a4=10-a1-a2-a3; s=s+M[1,a1]*M[2,a2]*M[3,a3]*M[4,a4]; }}}}} return(s);}',
 'ideal E=REL,rz*D-1;',
 'for(j=1;j<=5;j++){ matrix M[4][4]; c=0; for(k=1;k<=5;k++){ if(k!=j){ c++; for(i=1;i<=4;i++){ M[i,c]=1+t*Y[i,k]; } } } poly F=perm4(M)-24; matrix T=coef(F,t*ka); for(k=1;k<=ncols(T);k++){ if(T[1,k]!=1){ E=E,T[2,k]; } } kill F; kill T; kill M; }',
 'ring R2=0,(rr,rz,q3,ii),dp; option(redSB); ideal E=imap(R,E); ideal I=std(E);',
 'printf("G4-A case (a) cert e=%s sg=%d: dim %%s unit %%s",dim(I),reduce(1,I)==0);'%(e,sg),
 'quit;']
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
