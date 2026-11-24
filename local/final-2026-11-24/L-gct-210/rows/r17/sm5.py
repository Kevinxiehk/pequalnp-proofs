# (SM_n) exact test: a single strongly level 4x5 matrix Y (column-centred columns y_1..y_n in V, the others 0) with ISOTROPIC row sum
# f = c(s0) (scale fixed; identity chart suffices: f is one isotropic point and S_4 moves a vertex at infinity to a finite one) and all n
# columns nonzero.  Conditions: |y_k|^2 = <f,y_k> (degree 2), P_3 and P_4 of every deletion.  usage: python3 -I sm5.py P NC OUT
import sys
P,NC,out=sys.argv[1],int(sys.argv[2]),sys.argv[3]
vs=['y%d%d'%(k,c) for k in range(1,NC+1) for c in (1,2,3)]
unk=['s0']+vs+['ii']
L=['ring R=%s,(%s),dp; option(redSB); LIB "elim.lib";'%(P,','.join(unk))]
L.append('matrix H[4][3]=1,1,1,1,-1,-1,-1,1,-1,-1,-1,1; int i; int j; int k; int c;')
L.append('matrix f[3][1]=s0^2-1,ii*(s0^2+1),2*s0;')
for k in range(1,NC+1): L.append('matrix y%d[3][1]=y%d1,y%d2,y%d3;'%(k,k,k,k))
L.append('proc dt(matrix a, matrix b){ return(a[1,1]*b[1,1]+a[2,1]*b[2,1]+a[3,1]*b[3,1]); }')
L.append('ideal E=ii^2+1; matrix S=%s-f; for(i=1;i<=3;i++){ E=E,S[i,1]; }'%('+'.join('y%d'%k for k in range(1,NC+1))))
for k in range(1,NC+1): L.append('E=E,dt(y%d,y%d)-dt(f,y%d);'%(k,k,k))
L.append('matrix Y[4][5]; matrix cC;')
for k in range(1,6):
    if k<=NC: L.append('cC=H*y%d; for(i=1;i<=4;i++){ Y[i,%d]=cC[i,1]; }'%(k,k))
    else: L.append('for(i=1;i<=4;i++){ Y[i,%d]=0; }'%k)
L.append('proc perm4(matrix M){ poly s=0; int a1,a2,a3,a4; for(a1=1;a1<=4;a1++){for(a2=1;a2<=4;a2++){ if(a2!=a1){ for(a3=1;a3<=4;a3++){ if((a3!=a1)&&(a3!=a2)){ a4=10-a1-a2-a3; s=s+M[1,a1]*M[2,a2]*M[3,a3]*M[4,a4]; }}}}} return(s);}')
L.append('proc t3(matrix a, matrix b, matrix c){ poly q=0; int r; for(r=1;r<=4;r++){ q=q+a[r,1]*b[r,1]*c[r,1]; } return(q); }')
L.append('list col; for(j=1;j<=5;j++){ matrix cj[4][1]; for(i=1;i<=4;i++){ cj[i,1]=Y[i,j]; } col[j]=cj; kill cj; }')
L.append('int d1,d2,d3; for(k=1;k<=5;k++){ poly F3=0; for(d1=1;d1<=5;d1++){ for(d2=d1+1;d2<=5;d2++){ for(d3=d2+1;d3<=5;d3++){ if((d1!=k)&&(d2!=k)&&(d3!=k)){ F3=F3+t3(col[d1],col[d2],col[d3]); } } } } E=E,F3; kill F3; matrix M4[4][4]; c=0; for(j=1;j<=5;j++){ if(j!=k){ c++; for(i=1;i<=4;i++){ M4[i,c]=Y[i,j]; } } } E=E,perm4(M4); kill M4; }')
L.append('list CN;')
for k in range(1,NC+1): L.append('CN[%d]=ideal(y%d1,y%d2,y%d3);'%(k,k,k,k))
L.append('ideal I=std(E); printf("SM%s p=%s: dim %%s unit %%s",dim(I),(reduce(1,I)==0)); for(k=1;k<=%d;k++){ if(reduce(1,I)!=0){ I=std(sat(I,CN[k])); printf("  after column %%s nonzero: dim %%s unit %%s",k,dim(I),(reduce(1,I)==0)); } }'%(NC,P,NC))
L.append('quit;')
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
