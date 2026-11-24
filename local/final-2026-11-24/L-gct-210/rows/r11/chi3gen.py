# (4,1) spaces over the special kernels K_u = u^perp e_a^T (+) C u e_b^T (a = 0, b = 1), u isotropic (Walsh, u = (al^2-1, ii(al^2+1), 2al)),
# u^perp = span(u, w), w = (u2, -u1, 0) (Walsh; chart: w not in C u).  Unknowns: Z (gauge Z[0][0] = Z[1][0] = Z[0][1] = 0, chart det != 0),
# m (chart m_0 = 1 covers m_a != 0; chart m_1 = 1 covers m_a = 0 != m_b), al, ii.  Conditions: c(Z) = m and all coefficients of c_j - m_j c_K0.
import sys
P,K0,out=sys.argv[1],int(sys.argv[2]),sys.argv[3]
zs=['z%d%d'%(i,j) for i in range(4) for j in range(5) if (i,j) not in ((0,0),(1,0),(0,1))]
mv=['m%d'%k for k in range(5) if k!=K0]
unk=['al','ii','rr']+zs+mv
L=['ring R=%s,(sa,sb,sc,t,%s),dp; option(redSB); LIB "elim.lib";'%(P,','.join(unk))]
L.append('matrix H[4][3]=1,1,1,1,-1,-1,-1,1,-1,-1,-1,1; matrix uW[3][1]=al^2-1,ii*(al^2+1),2*al; matrix wW[3][1]=uW[2,1],-uW[1,1],0;')
L.append('matrix u=H*uW; matrix w=H*wW; matrix Z[4][5]; int i; int j; int k; int c;')
for i in range(4):
    for j in range(5):
        if (i,j) not in ((0,0),(1,0),(0,1)): L.append('Z[%d,%d]=z%d%d;'%(i+1,j+1,i,j))
L.append('list mm=%s;'%','.join('1' if k==K0 else 'm%d'%k for k in range(5)))
L.append('matrix Y[4][5]; for(i=1;i<=4;i++){ Y[i,1]=sa*u[i,1]+sb*w[i,1]; Y[i,2]=sc*u[i,1]; for(j=1;j<=5;j++){Y[i,j]=Y[i,j]+t*Z[i,j];} }')
L.append('matrix MK[3][3]=u[1,1],u[2,1],0, w[1,1],w[2,1],0, 0,0,u[1,1]; poly dk=det(MK);')
L.append('proc perm4(matrix M){ poly s=0; int a1,a2,a3,a4; for(a1=1;a1<=4;a1++){for(a2=1;a2<=4;a2++){ if(a2!=a1){ for(a3=1;a3<=4;a3++){ if((a3!=a1)&&(a3!=a2)){ a4=10-a1-a2-a3; s=s+M[1,a1]*M[2,a2]*M[3,a3]*M[4,a4]; }}}}} return(s);}')
L.append('list CC; for(j=1;j<=5;j++){ matrix M[4][4]; c=0; for(k=1;k<=5;k++){ if(k!=j){ c++; for(i=1;i<=4;i++){ M[i,c]=1+Y[i,k]; } } } CC[j]=perm4(M)-24; kill M; }')
L.append('ideal E; for(j=1;j<=5;j++){ poly cs=0; for(i=1;i<=4;i++){cs=cs+Z[i,j];} E=E,cs-mm[j]; kill cs; }')
L.append('for(j=1;j<=5;j++){ if(j!=%d){ poly F=CC[j]-mm[j]*CC[%d]; matrix T=coef(F,sa*sb*sc*t); for(k=1;k<=ncols(T);k++){E=E,T[2,k];} kill F; kill T; } }'%(K0+1,K0+1))
L.append('E=E,ii^2+1,1+%s,rr*dk-1;'%('+'.join(mv)))
L.append('ring R2=%s,(%s),dp; option(redSB); LIB "elim.lib"; ideal E=imap(R,E); ideal I=std(E);'%(P,','.join(unk)))
L.append('printf("CHI3 m%d p=%s: dim %%s unit %%s",dim(I),(reduce(1,I)==0)); if(reduce(1,I)!=0){ ideal S=std(sat(I,ideal(%s))); printf("   after saturation by the other m_j: dim %%s unit %%s",dim(S),(reduce(1,S)==0)); ideal Em=eliminate(I,%s); print(Em); }'%(K0,P,'*'.join(mv),'*'.join(zs)))
L.append('quit;')
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
