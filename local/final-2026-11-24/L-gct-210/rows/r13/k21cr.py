# Support-4 (2,1) kernels, Lemma-RS normal form with the linear sums SOLVED by Cramer (rows, round 13).
# Columns 1..4 support, column 5 zero.  Gauges be_1 = 1, al_1 = 0, mu_1 = 0.  With F = [c(s2) c(s3) c(s4)], D = det F (Rabinowitsch rD):
#   (al_2,al_3,al_4) = F^{-1} (2u),   (be_2,be_3,be_4) = F^{-1} (-c(s1)),   (mu_2,mu_3,mu_4) = F^{-1} (2w - sum_k ep_k c'(s_k)/2)  [ep_1 = 1].
# Unknowns: s0..s4, ep2..ep4, ii, rD.  Conditions: y-coefficients of P_3, P_4 of all deletions; then saturation "column k nonzero".
# usage: python3 -I k21cr.py P OUT [MOB]   (MOB = a,b,c,d: Moebius reparametrisation c(a s + b : c s + d), chart at infinity)
import sys
P,out=sys.argv[1],sys.argv[2]
mob=[int(x) for x in sys.argv[3].split(',')] if len(sys.argv)>3 else [1,0,0,1]
a,b,c_,d=mob; det=a*d-b*c_
unk=['s0','s1','s2','s3','s4','ep1','ep2','ep3','ep4','ii','rD']
L=['ring R=%s,(y1,y2,y3,%s),dp; option(redSB); LIB "elim.lib";'%(P,','.join(unk))]
L.append('matrix H[4][3]=1,1,1,1,-1,-1,-1,1,-1,-1,-1,1; int i; int j; int k; int c;')
# homogeneous conic param through the Moebius map: c(S:T) = (S^2-T^2, ii(S^2+T^2), 2ST), S = a s + b, T = c s + d; derivative/2/det is a unit vector
L.append('proc cc(poly s){ poly S=%d*s+%d; poly T=%d*s+%d; matrix v[3][1]=S^2-T^2,ii*(S^2+T^2),2*S*T; return(v); }'%(a,b,c_,d))
L.append('proc cd(poly s){ poly S=%d*s+%d; poly T=%d*s+%d; matrix v[3][1]=(%d*S-%d*T),ii*(%d*S+%d*T),(%d*T+%d*S); v=v/%d; return(v); }'%(a,b,c_,d,a,c_,a,c_,a,c_,det))
L.append('matrix u=cc(s0); matrix w=cd(s0);')
L.append('matrix F[3][3]; matrix f2=cc(s2); matrix f3=cc(s3); matrix f4=cc(s4); for(i=1;i<=3;i++){ F[i,1]=f2[i,1]; F[i,2]=f3[i,1]; F[i,3]=f4[i,1]; } poly D=det(F);')
L.append('matrix Fa[3][3]; Fa[1,1]=F[2,2]*F[3,3]-F[2,3]*F[3,2]; Fa[1,2]=-(F[1,2]*F[3,3]-F[1,3]*F[3,2]); Fa[1,3]=F[1,2]*F[2,3]-F[1,3]*F[2,2]; Fa[2,1]=-(F[2,1]*F[3,3]-F[2,3]*F[3,1]); Fa[2,2]=F[1,1]*F[3,3]-F[1,3]*F[3,1]; Fa[2,3]=-(F[1,1]*F[2,3]-F[1,3]*F[2,1]); Fa[3,1]=F[2,1]*F[3,2]-F[2,2]*F[3,1]; Fa[3,2]=-(F[1,1]*F[3,2]-F[1,2]*F[3,1]); Fa[3,3]=F[1,1]*F[2,2]-F[1,2]*F[2,1];')
L.append('matrix f1=cc(s1); matrix m1=ep1*cd(s1); matrix ra=2*u; matrix rb=-f1; matrix rm=2*w-m1-ep2*cd(s2)-ep3*cd(s3)-ep4*cd(s4);')
L.append('matrix AL=rD*Fa*ra; matrix BE=rD*Fa*rb; matrix MU=rD*Fa*rm;')
L.append('matrix m2=ep2*cd(s2)+MU[1,1]*f2; matrix m3=ep3*cd(s3)+MU[2,1]*f3; matrix m4=ep4*cd(s4)+MU[3,1]*f4; matrix f5=u; matrix m5=w;')
L.append('list al=0,AL[1,1],AL[2,1],AL[3,1],1; list be=1,BE[1,1],BE[2,1],BE[3,1],0; list ff=f1,f2,f3,f4,f5; list mm=m1,m2,m3,m4,m5;')
L.append('ideal E=ii^2+1,ep1^2-1,ep2^2-1,ep3^2-1,ep4^2-1,rD*D-1;')
L.append('matrix Y[4][5]; matrix colW[3][1]; matrix fk; matrix mk;')
L.append('for(k=1;k<=5;k++){ fk=ff[k]; mk=mm[k]; colW=y1*(u-al[k]*fk)/2+y2*(w-mk)/2-y3*be[k]*fk/2; matrix colC=H*colW; for(i=1;i<=4;i++){ Y[i,k]=colC[i,1]; } kill colC; }')
L.append('proc perm4(matrix M){ poly s=0; int a1,a2,a3,a4; for(a1=1;a1<=4;a1++){for(a2=1;a2<=4;a2++){ if(a2!=a1){ for(a3=1;a3<=4;a3++){ if((a3!=a1)&&(a3!=a2)){ a4=10-a1-a2-a3; s=s+M[1,a1]*M[2,a2]*M[3,a3]*M[4,a4]; }}}}} return(s);}')
L.append('ideal CHK; for(j=1;j<=5;j++){ matrix M[4][4]; c=0; for(k=1;k<=5;k++){ if(k!=j){ c++; for(i=1;i<=4;i++){ M[i,c]=1+Y[i,k]; } } } poly G=perm4(M)-24; matrix T=coef(G,y1*y2*y3); for(k=1;k<=ncols(T);k++){ if(deg(T[1,k])>=3){E=E,T[2,k];} else {CHK=CHK,T[2,k];} } kill G; kill T; kill M; }')
L.append('list CN; for(k=1;k<=4;k++){ fk=ff[k]; mk=mm[k]; matrix dA=al[k]*fk-u; matrix dM=mk-w; CN[k]=ideal(dA[1,1],dA[2,1],dA[3,1],dM[1,1],dM[2,1],dM[3,1],be[k]); kill dA; kill dM; }')
L.append('ring R2=%s,(%s),dp; option(redSB); LIB "elim.lib"; ideal E=imap(R,E); ideal CHK=imap(R,CHK); list CN=imap(R,CN);'%(P,','.join(unk)))
L.append('ideal I=std(E); printf("K21CR mob %s p=%s: dim %%s unit %%s",dim(I),(reduce(1,I)==0)); printf("  degree<=2 parts reduce to 0: %%s",size(reduce(CHK,I))==0);'%(sys.argv[3] if len(sys.argv)>3 else 'id',P))
L.append('for(k=1;k<=4;k++){ if(reduce(1,I)!=0){ I=std(sat(I,CN[k])); printf("  after saturation by column %s nonzero: dim %s unit %s",k,dim(I),(reduce(1,I)==0)); } }')
L.append('quit;')
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
