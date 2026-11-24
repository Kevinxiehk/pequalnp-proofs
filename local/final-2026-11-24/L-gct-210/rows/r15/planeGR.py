# Case G (support 4) plane test, REDUCED (rows, round 15): the four points s1..s4 satisfy e2 = 0, e4 = -1 (R14.7); parametrize s3 by
# s3^2 - S s3 + Pp = 0, s4 = S - s3 with Pp = -1/(s1 s2), S = -(s1 s2 + Pp)/(s1 + s2)  (denominators via r1 = 1/(s1 s2 (s1+s2)));
# n_k = c(s_k)/D_k (Vandermonde weights, D_k = prod_{j != k}(s_k - s_j); 1/D_k via r2 = 1/prod_{i<j}(s_i - s_j)); a_1 = 0; sum a_k n_k = 2u.
# usage: python3 -I planeGR.py P OUT
import sys
P,out=sys.argv[1],sys.argv[2]
unk=['s0','s1','s2','s3','a2','a3','a4','ii','r1','r2']
L=['ring R=%s,(y1,y3,%s),dp; option(redSB);'%(P,','.join(unk))]
L.append('matrix H[4][3]=1,1,1,1,-1,-1,-1,1,-1,-1,-1,1; int i; int j; int k; int c;')
L.append('proc cc(poly s){ matrix v[3][1]=s^2-1,ii*(s^2+1),2*s; return(v); }')
L.append('poly Pp=-r1*(s1+s2); poly S=-(s1*s2+Pp)*r1*s1*s2; poly s4=S-s3;')   # Pp = -1/(s1 s2) = -r1 (s1+s2);  S = -(s1 s2 + Pp)/(s1+s2) = -(s1 s2 + Pp) r1 s1 s2
L.append('list sl=s1,s2,s3,s4; matrix u=cc(s0);')
L.append('poly d12=s1-s2; poly d13=s1-s3; poly d14=s1-s4; poly d23=s2-s3; poly d24=s2-s4; poly d34=s3-s4;')
# 1/D_1 = 1/(d12 d13 d14) = r2 * d23 d24 d34 ; 1/D_2 = 1/((-d12) d23 d24) = -r2 d13 d14 d34 ; 1/D_3 = 1/((-d13)(-d23) d34) = r2 d12 d14 d24 ; 1/D_4 = 1/((-d14)(-d24)(-d34)) = -r2 d12 d13 d23
L.append('list iD=r2*d23*d24*d34, -r2*d13*d14*d34, r2*d12*d14*d24, -r2*d12*d13*d23;')
L.append('list nn; for(k=1;k<=4;k++){ nn[k]=iD[k]*cc(sl[k]); } list aa=0,a2,a3,a4;')
L.append('ideal E=ii^2+1, r1*s1*s2*(s1+s2)-1, r2*d12*d13*d14*d23*d24*d34-1, s3^2-S*s3+Pp;')
L.append('matrix SA=aa[1]*nn[1]+aa[2]*nn[2]+aa[3]*nn[3]+aa[4]*nn[4]-2*u; for(i=1;i<=3;i++){ E=E,SA[i,1]; }')
L.append('matrix Y[4][5]; matrix colW[3][1]; matrix nk;')
L.append('for(k=1;k<=4;k++){ nk=nn[k]; colW=y1*(u-aa[k]*nk)/2-y3*nk/2; matrix cC=H*colW; for(i=1;i<=4;i++){ Y[i,k]=cC[i,1]; } kill cC; } for(i=1;i<=4;i++){ Y[i,5]=0; }')
L.append('proc perm4(matrix M){ poly s=0; int a1,a2_,a3_,a4_; for(a1=1;a1<=4;a1++){for(a2_=1;a2_<=4;a2_++){ if(a2_!=a1){ for(a3_=1;a3_<=4;a3_++){ if((a3_!=a1)&&(a3_!=a2_)){ a4_=10-a1-a2_-a3_; s=s+M[1,a1]*M[2,a2_]*M[3,a3_]*M[4,a4_]; }}}}} return(s);}')
L.append('for(j=1;j<=5;j++){ matrix M[4][4]; c=0; for(k=1;k<=5;k++){ if(k!=j){ c++; for(i=1;i<=4;i++){ M[i,c]=1+Y[i,k]; } } } poly F=perm4(M)-24; matrix T=coef(F,y1*y3); for(k=1;k<=ncols(T);k++){ if(deg(T[1,k])>=2){E=E,T[2,k];} } kill F; kill T; kill M; }')
L.append('ring R2=%s,(%s),dp; option(redSB); ideal E=imap(R,E); ideal I=std(E); printf("PLANE-GR p=%s: dim %%s unit %%s",dim(I),(reduce(1,I)==0));'%(P,','.join(unk),P))
L.append('quit;')
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
