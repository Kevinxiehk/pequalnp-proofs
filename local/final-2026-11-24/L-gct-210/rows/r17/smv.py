# (SM5) all-vertex configurations: f and the five g-directions are the 6 octahedral vertices (u = vertex 0 WLOG), g_k = la_k * vertex;
# sum g_k = 3 f; columns (f - g_k)/2; P_3, P_4 of every deletion; columns nonzero.  usage: python3 -I smv.py P OUT
import sys, itertools
P,out=sys.argv[1],sys.argv[2]
V=['-1,ii,0','0,2*ii,2','0,2*ii,-2','-2,0,2*ii','-2,0,-2*ii','1,ii,0']
L=['ring R=%s,(la1,la2,la3,la4,la5,ii),dp; option(redSB); LIB "elim.lib";'%P,'matrix H[4][3]=1,1,1,1,-1,-1,-1,1,-1,-1,-1,1; int i; int j; int k; int c; int bad=0; int tot=0;']
L.append('proc perm4(matrix M){ poly s=0; int a1,a2,a3,a4; for(a1=1;a1<=4;a1++){for(a2=1;a2<=4;a2++){ if(a2!=a1){ for(a3=1;a3<=4;a3++){ if((a3!=a1)&&(a3!=a2)){ a4=10-a1-a2-a3; s=s+M[1,a1]*M[2,a2]*M[3,a3]*M[4,a4]; }}}}} return(s);}')
L.append('proc t3(matrix a, matrix b, matrix c){ poly q=0; int r; for(r=1;r<=4;r++){ q=q+a[r,1]*b[r,1]*c[r,1]; } return(q); }')
L.append('matrix f[3][1]=%s;'%V[0])
for perm in itertools.permutations(range(1,6)):
    L.append('matrix v1[3][1]=%s; matrix v2[3][1]=%s; matrix v3[3][1]=%s; matrix v4[3][1]=%s; matrix v5[3][1]=%s;'%tuple(V[p] for p in perm))
    L.append('list gg=la1*v1,la2*v2,la3*v3,la4*v4,la5*v5; ideal E=ii^2+1; matrix S=la1*v1+la2*v2+la3*v3+la4*v4+la5*v5-3*f; for(i=1;i<=3;i++){ E=E,S[i,1]; }')
    L.append('list col; for(k=1;k<=5;k++){ matrix gk=gg[k]; col[k]=H*(f-gk)/2; kill gk; }')
    L.append('int d1,d2,d3; for(k=1;k<=5;k++){ poly F3=0; for(d1=1;d1<=5;d1++){ for(d2=d1+1;d2<=5;d2++){ for(d3=d2+1;d3<=5;d3++){ if((d1!=k)&&(d2!=k)&&(d3!=k)){ F3=F3+t3(col[d1],col[d2],col[d3]); } } } } E=E,F3; kill F3; matrix M4[4][4]; c=0; for(j=1;j<=5;j++){ if(j!=k){ c++; matrix cj=col[j]; for(i=1;i<=4;i++){ M4[i,c]=cj[i,1]; } kill cj; } } E=E,perm4(M4); kill M4; }')
    L.append('ideal I=std(E); tot++; for(k=1;k<=5;k++){ if(reduce(1,I)!=0){ matrix cz=col[k]; I=std(sat(I,ideal(cz[1,1],cz[2,1],cz[3,1],cz[4,1]))); kill cz; } } if(reduce(1,I)!=0){ bad++; printf("NONUNIT"); }')
    L.append('kill v1,v2,v3,v4,v5,gg,E,S,col,I,d1,d2,d3;')
L.append('printf("SMV5 p=%s: %%s assignments, %%s non-unit",tot,bad); quit;'%P)
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
