# A-coordinates, NC active columns, sign pattern SG: orthogonality of B_j = 1 - 2A_j (degree 2), det B_j = eps_j, and ONLY the summed cubic
# P_3(h(s)) = 2 sum_i e_3(row_i) == 0 (R10.1).  Saturation only by the A_j of eps = +1 columns.   usage: python3 aksum.py P SG OUT
import sys
P=sys.argv[1]; SG=sys.argv[2]; out=sys.argv[3]; NC=len(SG); free=NC-1
names=['a%d%d%d'%(j,r,c) for j in range(free) for r in range(3) for c in range(3)]
L=['ring R=%s,(%s,s1,s2,s3),dp; option(redSB);'%(P,','.join(names)),
   'matrix H[4][3]=1,1,1,1,-1,-1,-1,1,-1,-1,-1,1; matrix Id[3][3]=1,0,0,0,1,0,0,0,1; matrix S[3][1]=s1,s2,s3; list A; ideal E;']
for j in range(free):
    L.append('matrix A%d[3][3]=%s; A[%d]=A%d;'%(j,','.join('a%d%d%d'%(j,r,c) for r in range(3) for c in range(3)),j+1,j))
L.append('matrix Al=Id;'+''.join(' Al=Al-A%d;'%j for j in range(free))+' A[%d]=Al;'%NC)
L.append('int i; int j; int k; int l; int q;')
L.append('for(j=1;j<=%d;j++){ matrix M=A[j]; matrix B=Id-2*M; matrix O=transpose(B)*B-Id; for(i=1;i<=3;i++){for(k=i;k<=3;k++){E=E,O[i,k];}} kill M; kill B; kill O; }'%NC)
for j in range(NC):
    L.append('matrix Bd%d=Id-2*A[%d]; E=E,det(Bd%d)-(%d);'%(j,j+1,j,1 if SG[j]=='+' else -1))
L.append('matrix Y[4][%d]; for(j=1;j<=%d;j++){ matrix M=A[j]; matrix col=H*(M*S); for(i=1;i<=4;i++){Y[i,j]=col[i,1];} kill M; kill col; }'%(NC,NC))
L.append('poly P3=0; for(i=1;i<=4;i++){ for(j=1;j<=%d;j++){for(k=j+1;k<=%d;k++){for(l=k+1;l<=%d;l++){ P3=P3+Y[i,j]*Y[i,k]*Y[i,l]; }}} }'%(NC,NC,NC))
L.append('matrix C=coef(P3,s1*s2*s3); for(q=1;q<=ncols(C);q++){E=E,C[2,q];}')
L.append('ring R2=%s,(%s),dp; option(redSB); LIB "elim.lib"; ideal E=imap(R,E); list A=imap(R,A); ideal G=std(E); printf("AKSUM %s p=%s: dim %%s unit %%s",dim(G),(reduce(1,G)==0));'%(P,','.join(names),SG,P))
for j in range(NC):
    if SG[j]=='+':
        L.append('matrix Mj%d=A[%d]; ideal Jc%d=Mj%d[1,1],Mj%d[1,2],Mj%d[1,3],Mj%d[2,1],Mj%d[2,2],Mj%d[2,3],Mj%d[3,1],Mj%d[3,2],Mj%d[3,3]; G=std(sat(G,Jc%d)); printf("  sat col %d: dim %%s unit %%s",dim(G),(reduce(1,G)==0));'%((j,j+1)+(j,)*10+(j,j)))
L.append('printf("RESULT AKSUM %s p=%s: unit %%s",(reduce(1,G)==0)); quit;'%(SG,P))
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
