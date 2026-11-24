# ++-- orbit test: base configuration B_j = eps_j Rot(s_j, v_j) (R8.10), unknown R in O(3,C); triple products t(R A_a tau, ...) == 0.
# INV = 1: the inverse configuration v_j -> -v_j.   usage: python3 orb_ppmm.py OUT P INV
import sys
out,P,INV=sys.argv[1],sys.argv[2],int(sys.argv[3]); sg=-1 if INV else 1
L=['ring R=%s,(r2,r3,ii,x11,x12,x13,x21,x22,x23,x31,x32,x33,s1,s2,s3),dp; option(redSB);'%P]
L.append('matrix X[3][3]=x11,x12,x13,x21,x22,x23,x31,x32,x33; matrix Id[3][3]=1,0,0,0,1,0,0,0,1; matrix T[3][1]=s1,s2,s3; list A;')
L.append('poly a=r2/4; poly b=r2*r3/4; poly sp=3*r2/4; poly sm=-r2*r3/4;')
vs=['-ii/2,0,a','ii/2,0,a','0,1/2,-b','0,-1/2,-b']; ss=['sp','sp','sm','sm']; es=[1,1,-1,-1]
for j in range(4):
    L.append('matrix v%d[3][1]=%s; v%d=%d*v%d; matrix c%d[3][3]=0,-v%d[3,1],v%d[2,1],v%d[3,1],0,-v%d[1,1],-v%d[2,1],v%d[1,1],0;'%(j,vs[j],j,sg,j,j,j,j,j,j,j,j))
    L.append('matrix B%d[3][3]; B%d=(%s^2-(transpose(v%d)*v%d)[1,1])*Id; B%d=B%d+2*v%d*transpose(v%d); B%d=B%d+2*%s*c%d; B%d=%d*B%d; A[%d]=(Id-B%d)/2;'%(j,j,ss[j],j,j,j,j,j,j,j,j,ss[j],j,j,es[j],j,j+1,j))
L.append('ideal E=r2^2-2,r3^2-3,ii^2+1; matrix O=transpose(X)*X-Id; int i; int k; for(i=1;i<=3;i++){for(k=i;k<=3;k++){E=E,O[i,k];}}')
L.append('matrix SS=B0+B1+B2+B3-2*Id; poly chk=0; for(i=1;i<=3;i++){for(k=1;k<=3;k++){chk=chk+SS[i,k]^2;}}')
L.append('proc t3(matrix x, matrix y, matrix z){ return(x[1,1]*y[2,1]*z[3,1]+x[1,1]*y[3,1]*z[2,1]+x[2,1]*y[1,1]*z[3,1]+x[2,1]*y[3,1]*z[1,1]+x[3,1]*y[1,1]*z[2,1]+x[3,1]*y[2,1]*z[1,1]); }')
L.append('list V; for(i=1;i<=4;i++){ matrix Mi=A[i]; V[i]=X*(Mi*T); kill Mi; }')
L.append('int p; int q; int u; for(p=1;p<=4;p++){for(q=p+1;q<=4;q++){for(u=q+1;u<=4;u++){ poly F=t3(V[p],V[q],V[u]); matrix C=coef(F,s1*s2*s3); for(k=1;k<=ncols(C);k++){E=E,C[2,k];} kill F; kill C; }}}')
L.append('ring R2=%s,(r2,r3,ii,x11,x12,x13,x21,x22,x23,x31,x32,x33),dp; option(redSB); ideal E=imap(R,E); poly chk=imap(R,chk);'%P)
L.append('ideal Z=std(ideal(r2^2-2,r3^2-3,ii^2+1)); printf("check sum B = 2I in the number field: %s",reduce(chk,Z)==0);')
L.append('ideal G=std(E); printf("ORB ++-- inv=%d p=%s: dim %%s unit %%s size %%s",dim(G),(reduce(1,G)==0),size(G)); quit;'%(INV,P))
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
