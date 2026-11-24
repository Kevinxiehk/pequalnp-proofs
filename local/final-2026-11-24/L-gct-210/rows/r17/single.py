# single strongly level matrices Y_f on 4 columns with isotropic row sum f and isotropic "images" g_j: columns (f - g_j)/2, sum g_j = 2f
# (the row-sum-f element of a principal plane / kernel); conditions: P_3, P_4 of every deletion; saturation: columns nonzero.
import sys
P,out=sys.argv[1],sys.argv[2]
pts=['f']+['g%d'%j for j in (1,2,3,4)]
vs=[]
for q in pts: vs+=['s_'+q,'t_'+q]
unk=vs+['ii']
L=['ring R=%s,(%s),dp; option(redSB); LIB "elim.lib";'%(P,','.join(unk))]
L.append('matrix H[4][3]=1,1,1,1,-1,-1,-1,1,-1,-1,-1,1; int i; int j; int k; int c;')
L.append('proc cc(poly s, poly t){ matrix v[3][1]=s^2-t^2,ii*(s^2+t^2),2*s*t; return(v); }')
for q in pts: L.append('matrix %s=cc(s_%s,t_%s);'%(q,q,q))
L.append('ideal E=ii^2+1; matrix S1=g1+g2+g3+g4-2*f; for(i=1;i<=3;i++){ E=E,S1[i,1]; }')
L.append('matrix Y[4][5]; matrix cC;')
for j in (1,2,3,4): L.append('cC=H*(f-g%d)/2; for(i=1;i<=4;i++){ Y[i,%d]=cC[i,1]; }'%(j,j))
L.append('for(i=1;i<=4;i++){ Y[i,5]=0; }')
L.append('proc perm4(matrix M){ poly s=0; int a1,a2,a3,a4; for(a1=1;a1<=4;a1++){for(a2=1;a2<=4;a2++){ if(a2!=a1){ for(a3=1;a3<=4;a3++){ if((a3!=a1)&&(a3!=a2)){ a4=10-a1-a2-a3; s=s+M[1,a1]*M[2,a2]*M[3,a3]*M[4,a4]; }}}}} return(s);}')
L.append('proc t3(matrix a, matrix b, matrix c){ poly q=0; int r; for(r=1;r<=4;r++){ q=q+a[r,1]*b[r,1]*c[r,1]; } return(q); }')
L.append('list col; for(j=1;j<=4;j++){ matrix cj[4][1]; for(i=1;i<=4;i++){ cj[i,1]=Y[i,j]; } col[j]=cj; kill cj; }')
L.append('E=E,t3(col[1],col[2],col[3]),t3(col[1],col[2],col[4]),t3(col[1],col[3],col[4]),t3(col[2],col[3],col[4]);')
L.append('matrix M4[4][4]; for(j=1;j<=4;j++){ for(i=1;i<=4;i++){ M4[i,j]=Y[i,j]; } } E=E,perm4(M4);')
L.append('list CN; for(j=1;j<=4;j++){ matrix dz=col[j]; CN[j]=ideal(dz[1,1],dz[2,1],dz[3,1],dz[4,1]); kill dz; }')
L.append('ideal I=std(E); printf("SINGLE p=%s: dim %%s",dim(I)); for(k=1;k<=4;k++){ I=std(sat(I,CN[k])); printf("  after column %%s nonzero: dim %%s unit %%s",k,dim(I),(reduce(1,I)==0)); }'%P)
L.append('I=std(sat(I,ideal(s_f,t_f))); printf("  f != 0: dim %s unit %s",dim(I),(reduce(1,I)==0));')
L.append('quit;')
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
