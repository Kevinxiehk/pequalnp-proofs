# (SM_n), conic form (rows, round 17): f = c(sg), g_k = la_k c(ta_k) (isotropic, la_k = 0 allowed), sum g_k = (n-2) f, columns y_k = (f - g_k)/2
# (degree 2 automatic).  Conditions: P_3, P_4 of every deletion (columns n+1..5 zero).  Columns nonzero: saturation by (f - g_k) components.
# Affine conic chart (mod-p evidence); usage: python3 -I smc.py P NC OUT
import sys
P,NC,out=sys.argv[1],int(sys.argv[2]),sys.argv[3]
unk=['sg']+['ta%d'%k for k in range(1,NC+1)]+['la%d'%k for k in range(1,NC+1)]+['ii']
L=['ring R=%s,(%s),dp; option(redSB); LIB "elim.lib";'%(P,','.join(unk))]
L.append('matrix H[4][3]=1,1,1,1,-1,-1,-1,1,-1,-1,-1,1; int i; int j; int k; int c;')
L.append('proc cc(poly s){ matrix v[3][1]=s^2-1,ii*(s^2+1),2*s; return(v); }')
L.append('matrix f=cc(sg);')
for k in range(1,NC+1): L.append('matrix g%d=la%d*cc(ta%d);'%(k,k,k))
L.append('ideal E=ii^2+1; matrix S=%s-%d*f; for(i=1;i<=3;i++){ E=E,S[i,1]; }'%('+'.join('g%d'%k for k in range(1,NC+1)),NC-2))
L.append('matrix Y[4][5]; matrix cC;')
for k in range(1,6):
    if k<=NC: L.append('cC=H*(f-g%d)/2; for(i=1;i<=4;i++){ Y[i,%d]=cC[i,1]; }'%(k,k))
    else: L.append('for(i=1;i<=4;i++){ Y[i,%d]=0; }'%k)
L.append('proc perm4(matrix M){ poly s=0; int a1,a2,a3,a4; for(a1=1;a1<=4;a1++){for(a2=1;a2<=4;a2++){ if(a2!=a1){ for(a3=1;a3<=4;a3++){ if((a3!=a1)&&(a3!=a2)){ a4=10-a1-a2-a3; s=s+M[1,a1]*M[2,a2]*M[3,a3]*M[4,a4]; }}}}} return(s);}')
L.append('proc t3(matrix a, matrix b, matrix c){ poly q=0; int r; for(r=1;r<=4;r++){ q=q+a[r,1]*b[r,1]*c[r,1]; } return(q); }')
L.append('list col; for(j=1;j<=5;j++){ matrix cj[4][1]; for(i=1;i<=4;i++){ cj[i,1]=Y[i,j]; } col[j]=cj; kill cj; }')
L.append('int d1,d2,d3; for(k=1;k<=5;k++){ poly F3=0; for(d1=1;d1<=5;d1++){ for(d2=d1+1;d2<=5;d2++){ for(d3=d2+1;d3<=5;d3++){ if((d1!=k)&&(d2!=k)&&(d3!=k)){ F3=F3+t3(col[d1],col[d2],col[d3]); } } } } E=E,F3; kill F3; matrix M4[4][4]; c=0; for(j=1;j<=5;j++){ if(j!=k){ c++; for(i=1;i<=4;i++){ M4[i,c]=Y[i,j]; } } } E=E,perm4(M4); kill M4; }')
L.append('list CN;')
for k in range(1,NC+1): L.append('matrix dz%d=f-g%d; CN[%d]=ideal(dz%d[1,1],dz%d[2,1],dz%d[3,1]);'%(k,k,k,k,k,k))
L.append('ideal I=std(E); printf("SMC%s p=%s: dim %%s unit %%s",dim(I),(reduce(1,I)==0)); for(k=1;k<=%d;k++){ if(reduce(1,I)!=0){ I=std(sat(I,CN[k])); printf("  after column %%s nonzero: dim %%s unit %%s",k,dim(I),(reduce(1,I)==0)); } }'%(NC,P,NC))
L.append('quit;')
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
