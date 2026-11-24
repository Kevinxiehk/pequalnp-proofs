# (4,1) spaces L' = K_II (+) C Z with ker c = K_II = {mu zeta (e0-e1)^T + mu' zetabar (e2-e3)^T + y w e4^T}, zeta = (1,om,om^2,0),
# zetabar = (1,om^2,om,0), w = (1,1,1,-3), om^2+om+1 = 0.  Unknowns: Z (gauge Z[0][0] = Z[0][2] = Z[0][4] = 0), m (m_0 = 1 chart; covers
# all m by the symmetries 0<->1, 2<->3, (01)<->(23) with om <-> om^2), om.  Conditions: c(Z) = m and all coefficients of c_j - m_j c_0.
import sys
P=sys.argv[1]; out=sys.argv[2]
zs=['z%d%d'%(i,j) for i in range(4) for j in range(5) if not (i==0 and j in (0,2,4))]
unk=zs+['m1','m2','m3','m4','om']
L=['ring R=%s,(mu,mup,y,t,%s),dp; option(redSB); LIB "elim.lib";'%(P,','.join(unk))]
L.append('matrix Z[4][5]; int i; int j; int k; int c;')
for i in range(4):
    for j in range(5):
        if not (i==0 and j in (0,2,4)): L.append('Z[%d,%d]=z%d%d;'%(i+1,j+1,i,j))
L.append('list ze=1,om,om^2,0; list zb=1,om^2,om,0; list w=1,1,1,-3; list mm=1,m1,m2,m3,m4;')
L.append('matrix Y[4][5]; for(i=1;i<=4;i++){ Y[i,1]=mu*ze[i]; Y[i,2]=-mu*ze[i]; Y[i,3]=mup*zb[i]; Y[i,4]=-mup*zb[i]; Y[i,5]=y*w[i]; for(j=1;j<=5;j++){Y[i,j]=Y[i,j]+t*Z[i,j];} }')
L.append('proc perm4(matrix M){ poly s=0; int p1,p2,p3,p4; for(p1=1;p1<=4;p1++){for(p2=1;p2<=4;p2++){ if(p2!=p1){ for(p3=1;p3<=4;p3++){ if((p3!=p1)&&(p3!=p2)){ p4=10-p1-p2-p3; s=s+M[1,p1]*M[2,p2]*M[3,p3]*M[4,p4]; }}}}} return(s);}')
L.append('list CC; for(j=1;j<=5;j++){ matrix M[4][4]; c=0; for(k=1;k<=5;k++){ if(k!=j){ c++; for(i=1;i<=4;i++){ M[i,c]=1+Y[i,k]; } } } CC[j]=perm4(M)-24; kill M; }')
L.append('ideal E; for(j=1;j<=5;j++){ poly cs=0; for(i=1;i<=4;i++){cs=cs+Z[i,j];} E=E,cs; }')
L.append('for(j=2;j<=5;j++){ poly F=CC[j]-mm[j]*CC[1]; matrix T=coef(F,mu*mup*y*t); for(k=1;k<=ncols(T);k++){E=E,T[2,k];} kill F; kill T; }')
L.append('ring R2=%s,(%s),dp; option(redSB); LIB "elim.lib"; ideal E=imap(R,E); ideal I=std(E+ideal(om^2+om+1,1+m1+m2+m3+m4));'%(P,','.join(unk)))
L.append('I=std(sat(I,ideal(%s))); printf("CHI2-CC (column-centred, Z != 0) p=%s: dim %%s unit %%s",dim(I),(reduce(1,I)==0));'%(','.join(zs),P)); L.append(' if(reduce(1,I)!=0){ ideal Em=eliminate(I,%s); print(Em); ideal S=std(sat(I,ideal(m1*m2*m3*m4))); printf("  after saturation by m1 m2 m3 m4 (no zero entry): unit %%s",(reduce(1,S)==0)); }'%('*'.join(zs)))
L.append('quit;')
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
