# Principal plane test on 4 columns in ISOTROPIC coordinates (rows, round 17): P = span(f, fb), f, fb isotropic, <f,fb> != 0;
# B_j|P maps f -> g_j, fb -> gb_j (isotropic, <g_j,gb_j> = <f,fb>); sum g_j = 2 f, sum gb_j = 2 fb.  All isotropic vectors as
# c(s:t) = (s^2 - t^2, ii (s^2 + t^2), 2 s t) with free homogeneous (s,t) (scale absorbed; no charts).  Columns y_j = (a(f-g_j) + b(fb-gb_j))/2.
# usage: python3 -I pplane2.py P OUT
import sys
P,out=sys.argv[1],sys.argv[2]
pts=['f','fb']+['g%d'%j for j in (1,2,3,4)]+['gb%d'%j for j in (1,2,3,4)]
vs=[]
for q in pts: vs+=['s_'+q,'t_'+q]
unk=vs+['ii','rz']
L=['ring R=%s,(ya,yb,%s),dp; option(redSB); LIB "elim.lib";'%(P,','.join(unk))]
L.append('matrix H[4][3]=1,1,1,1,-1,-1,-1,1,-1,-1,-1,1; int i; int j; int k; int c;')
L.append('proc cc(poly s, poly t){ matrix v[3][1]=s^2-t^2,ii*(s^2+t^2),2*s*t; return(v); }')
L.append('proc dt(matrix a, matrix b){ return(a[1,1]*b[1,1]+a[2,1]*b[2,1]+a[3,1]*b[3,1]); }')
for q in pts: L.append('matrix %s=cc(s_%s,t_%s);'%(q,q,q))
L.append('poly ff=dt(f,fb); ideal E=ii^2+1,rz*ff-1;')
for j in (1,2,3,4): L.append('E=E,dt(g%d,gb%d)-ff;'%(j,j))
L.append('matrix S1=g1+g2+g3+g4-2*f; matrix S2=gb1+gb2+gb3+gb4-2*fb; for(i=1;i<=3;i++){ E=E,S1[i,1],S2[i,1]; }')
L.append('matrix Y[4][5]; matrix cw[3][1]; matrix cC;')
for j in (1,2,3,4):
    L.append('cw=ya*(f-g%d)/2+yb*(fb-gb%d)/2; cC=H*cw; for(i=1;i<=4;i++){ Y[i,%d]=cC[i,1]; }'%(j,j,j))
L.append('for(i=1;i<=4;i++){ Y[i,5]=0; }')
L.append('proc perm4(matrix M){ poly s=0; int a1,a2,a3,a4; for(a1=1;a1<=4;a1++){for(a2=1;a2<=4;a2++){ if(a2!=a1){ for(a3=1;a3<=4;a3++){ if((a3!=a1)&&(a3!=a2)){ a4=10-a1-a2-a3; s=s+M[1,a1]*M[2,a2]*M[3,a3]*M[4,a4]; }}}}} return(s);}')
L.append('ideal CHK; for(j=1;j<=5;j++){ matrix M[4][4]; c=0; for(k=1;k<=5;k++){ if(k!=j){ c++; for(i=1;i<=4;i++){ M[i,c]=1+Y[i,k]; } } } poly F=perm4(M)-24; matrix T=coef(F,ya*yb); for(k=1;k<=ncols(T);k++){ if(deg(T[1,k])>=3){E=E,T[2,k];} else {CHK=CHK,T[2,k];} } kill F; kill T; kill M; }')
L.append('list CN;')
for j in (1,2,3,4):
    L.append('matrix d%d1=f-g%d; matrix d%d2=fb-gb%d; CN[%d]=ideal(d%d1[1,1],d%d1[2,1],d%d1[3,1],d%d2[1,1],d%d2[2,1],d%d2[3,1]);'%(j,j,j,j,j,j,j,j,j,j,j))
L.append('ring R2=%s,(%s),dp; option(redSB); LIB "elim.lib"; ideal E=imap(R,E); ideal CHK=imap(R,CHK); list CN=imap(R,CN);'%(P,','.join(unk)))
L.append('ideal I=std(E); printf("PPLANE2 p=%s: dim %%s unit %%s",dim(I),(reduce(1,I)==0)); printf("  degree-2 parts reduce to 0: %%s",size(reduce(CHK,I))==0);'%P)
L.append('for(k=1;k<=4;k++){ if(reduce(1,I)!=0){ I=std(sat(I,CN[k])); printf("  after saturation by plane column %s nonzero: dim %s unit %s",k,dim(I),(reduce(1,I)==0)); } }')
L.append('quit;')
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
