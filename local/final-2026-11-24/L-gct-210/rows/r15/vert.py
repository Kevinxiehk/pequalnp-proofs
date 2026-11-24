# ALL-VERTEX configurations (support 5, cases G4 and R5) for the plane test: the 6 isotropic points are exactly the 6 octahedral vertices.
# WLOG (octahedral group transitive on vertices) u = vertex 0; loop over the 5! assignments of the other vertices.  Explicit vectors, no chart.
# G4: n-directions f1..f4 = 4 vertices (distinct), column 5 zero n with e1-part (u - al5 f5)/2, f5 = the last vertex, plane column 5 nonzero.
# R5: n-directions f1..f5 = the 5 other vertices.   usage: python3 -I vert.py P CASE OUT
import sys, itertools
P,CASE,out=sys.argv[1],sys.argv[2],sys.argv[3]
V=['-1,ii,0','0,2*ii,2','0,2*ii,-2','-2,0,2*ii','-2,0,-2*ii','1,ii,0']   # c(0), c(1), c(-1), c(i), c(-i), c(inf)
unk=['be2','be3','be4','be5','a2','a3','a4','a5','al5','ii']
L=['ring R=%s,(y1,y3,%s),dp; option(redSB); LIB "elim.lib";'%(P,','.join(unk)),'matrix H[4][3]=1,1,1,1,-1,-1,-1,1,-1,-1,-1,1; int i; int j; int k; int c; int bad=0; int tot=0;']
L.append('proc perm4(matrix M){ poly s=0; int a1,a2,a3,a4; for(a1=1;a1<=4;a1++){for(a2=1;a2<=4;a2++){ if(a2!=a1){ for(a3=1;a3<=4;a3++){ if((a3!=a1)&&(a3!=a2)){ a4=10-a1-a2-a3; s=s+M[1,a1]*M[2,a2]*M[3,a3]*M[4,a4]; }}}}} return(s);}')
L.append('matrix u[3][1]=%s;'%V[0])
for perm in itertools.permutations(range(1,6)):
    vs=[V[p] for p in perm]
    L.append('matrix f1[3][1]=%s; matrix f2[3][1]=%s; matrix f3[3][1]=%s; matrix f4[3][1]=%s; matrix f5[3][1]=%s;'%tuple(vs))
    if CASE=='G4':
        L.append('matrix n1=f1; matrix n2=be2*f2; matrix n3=be3*f3; matrix n4=be4*f4; matrix n5[3][1]; matrix g5=al5*f5;')
        L.append('ideal E=ii^2+1; matrix S1=n1+n2+n3+n4; matrix S2=a2*n2+a3*n3+a4*n4+g5-3*u; for(i=1;i<=3;i++){ E=E,S1[i,1],S2[i,1]; }')
        cols=['y1*(u)/2-y3*n1/2','y1*(u-a2*n2)/2-y3*n2/2','y1*(u-a3*n3)/2-y3*n3/2','y1*(u-a4*n4)/2-y3*n4/2','y1*(u-g5)/2']
    else:
        L.append('matrix n1=f1; matrix n2=be2*f2; matrix n3=be3*f3; matrix n4=be4*f4; matrix n5=be5*f5;')
        L.append('ideal E=ii^2+1; matrix S1=n1+n2+n3+n4+n5; matrix S2=a2*n2+a3*n3+a4*n4+a5*n5-3*u; for(i=1;i<=3;i++){ E=E,S1[i,1],S2[i,1]; }')
        cols=['y1*(u)/2-y3*n1/2','y1*(u-a2*n2)/2-y3*n2/2','y1*(u-a3*n3)/2-y3*n3/2','y1*(u-a4*n4)/2-y3*n4/2','y1*(u-a5*n5)/2-y3*n5/2']
    L.append('matrix Y[4][5]; matrix cw[3][1]; matrix cC;')
    for k,cexp in enumerate(cols):
        L.append('cw=%s; cC=H*cw; for(i=1;i<=4;i++){ Y[i,%d]=cC[i,1]; }'%(cexp,k+1))
    L.append('for(j=1;j<=5;j++){ matrix M[4][4]; c=0; for(k=1;k<=5;k++){ if(k!=j){ c++; for(i=1;i<=4;i++){ M[i,c]=1+Y[i,k]; } } } poly F=perm4(M)-24; matrix T=coef(F,y1*y3); for(k=1;k<=ncols(T);k++){ if(deg(T[1,k])>=2){E=E,T[2,k];} } kill F; kill T; kill M; }')
    if CASE=='G4': L.append('E=E+ideal(0); ideal I=std(E); if(reduce(1,I)!=0){ matrix dz=g5-u; I=std(sat(I,ideal(dz[1,1],dz[2,1],dz[3,1]))); kill dz; } tot++; if(reduce(1,I)!=0){ I=std(sat(I,ideal(be2*be3*be4))); } if(reduce(1,I)!=0){ bad++; printf("NONUNIT assignment %s",string(I)); }')
    else: L.append('ideal I=std(E); tot++; if(reduce(1,I)!=0){ I=std(sat(I,ideal(be2*be3*be4*be5))); } if(reduce(1,I)!=0){ bad++; printf("NONUNIT assignment"); }')
    L.append('kill n1,n2,n3,n4,n5,f1,f2,f3,f4,f5,Y,cw,cC,S1,S2,E,I;'+(' kill g5;' if CASE=='G4' else ''))
L.append('printf("VERT %s p=%s: %%s assignments, %%s non-unit",tot,bad); quit;'%(CASE,P))
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
