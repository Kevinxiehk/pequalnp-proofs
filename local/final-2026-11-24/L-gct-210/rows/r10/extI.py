# all 3-dim strongly level spaces containing the type-I plane N_I = chi (x) Lambda_M, chi = (1,i,-1,-i), M = {0,1,2}:
# N_I = {chi (a e0 + b e1 - (a+b) e2)^T}; unknown Y modulo N_I (gauge Y[0][0] = Y[0][1] = 0), ii^2 = -1.
import sys
P=sys.argv[1]; out=sys.argv[2]
ys=['y%d%d'%(i,j) for i in range(4) for j in range(5) if not (i==0 and j in (0,1))]
L=['ring R=%s,(pa,pb,yy,%s,ii),dp; option(redSB); LIB "elim.lib";'%(P,','.join(ys))]
L.append('matrix Yv[4][5]; int i; int j; int k; int c;')
for i in range(4):
    for j in range(5):
        if not (i==0 and j in (0,1)): L.append('Yv[%d,%d]=y%d%d;'%(i+1,j+1,i,j))
L.append('list chi=1,ii,-1,-ii;')
L.append('matrix Y[4][5]; for(i=1;i<=4;i++){ Y[i,1]=pa*chi[i]; Y[i,2]=pb*chi[i]; Y[i,3]=-(pa+pb)*chi[i]; for(j=1;j<=5;j++){Y[i,j]=Y[i,j]+yy*Yv[i,j];} }')
L.append('proc perm4(matrix M){ poly s=0; int p1,p2,p3,p4; for(p1=1;p1<=4;p1++){for(p2=1;p2<=4;p2++){ if(p2!=p1){ for(p3=1;p3<=4;p3++){ if((p3!=p1)&&(p3!=p2)){ p4=10-p1-p2-p3; s=s+M[1,p1]*M[2,p2]*M[3,p3]*M[4,p4]; }}}}} return(s);}')
L.append('ideal E; for(j=1;j<=5;j++){ matrix M[4][4]; c=0; for(k=1;k<=5;k++){ if(k!=j){ c++; for(i=1;i<=4;i++){ M[i,c]=1+Y[i,k]; } } } poly F=perm4(M)-24; matrix T=coef(F,pa*pb*yy); for(k=1;k<=ncols(T);k++){E=E,T[2,k];} kill M; kill F; kill T; }')
L.append('ring R2=%s,(%s,ii),dp; option(redSB); LIB "elim.lib"; ideal E=imap(R,E); ideal I=std(E+ideal(ii^2+1));'%(P,','.join(ys)))
L.append('printf("EXT-I p=%s: dim %%s unit %%s",dim(I),(reduce(1,I)==0)); list pr=minAssGTZ(I); printf("  %%s minimal associated primes",size(pr)); for(k=1;k<=size(pr);k++){ printf("  prime %%s: dim %%s",k,dim(std(pr[k]))); print(pr[k]); } quit;'%P)
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
