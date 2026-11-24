# Column-centred (4,1) extensions with m_a = m_b = 0 over the GENERIC two-column (2,1) kernels (rows, round 12; target 3 / hand-off (H)).
# K = span{u(e_a+e_b), (p+e)e_a + (p-e)e_b, d(e_a-e_b)} (Walsh data as in c21g/c21s: u, d on the conic (al, ga), u.p = 0, p.p = 1, d.e = 0,
# e.e = 1, gauges p.q1 = 0, e.q2 = 0 with Rabinowitsch charts).  Reduction R12.1 (valid where Pi = V): z_t = m_t zeta (t = c,d,e), zeta in V.
# m = (0, 0, 1, m3, -1-m3) (chart m_c = 1; S_3 on {c,d,e} covers all m with m_a = m_b = 0, |supp m| >= 2).
# Z mod K: Walsh coordinates of z_a, z_b with za1 = za2 = zb1 = 0 (chart: det of K at those coordinates != 0, Rabinowitsch).
# Output: dim / unit after saturation by the Z-unknowns (Z = 0 mod K is the trivial solution).   usage: python3 -I c21cc0.py P OUT
import sys
P,out=sys.argv[1],sys.argv[2]
q1=(2,3,5); q2=(3,-7,2)
zv=['za3','zb2','zb3','x1','x2','x3']
unk=['al','ga','p1','p2','p3','e1','e2','e3','ii','r1','r2','r3']+zv+['m3']
L=['ring R=%s,(sa,sb,sc,t,%s),dp; option(redSB); LIB "elim.lib";'%(P,','.join(unk))]
L.append('matrix H[4][3]=1,1,1,1,-1,-1,-1,1,-1,-1,-1,1;')
L.append('matrix uW[3][1]=al^2-1,ii*(al^2+1),2*al; matrix dW[3][1]=ga^2-1,ii*(ga^2+1),2*ga; matrix pW[3][1]=p1,p2,p3; matrix eW[3][1]=e1,e2,e3;')
L.append('matrix zaW[3][1]=0,0,za3; matrix zbW[3][1]=0,zb2,zb3; matrix xW[3][1]=x1,x2,x3;')
L.append('matrix u=H*uW; matrix d=H*dW; matrix pp=H*pW; matrix ee=H*eW; matrix za=H*zaW; matrix zb=H*zbW; matrix ze=H*xW;')
L.append('list mm=0,0,1,m3,-1-m3; int i; int j; int k; int c;')
L.append('matrix Y[4][5]; for(i=1;i<=4;i++){ Y[i,1]=sa*u[i,1]+sb*(pp[i,1]+ee[i,1])+sc*d[i,1]+t*za[i,1]; Y[i,2]=sa*u[i,1]+sb*(pp[i,1]-ee[i,1])-sc*d[i,1]+t*zb[i,1]; for(j=3;j<=5;j++){ Y[i,j]=t*mm[j]*ze[i,1]; } }')
# gauge determinant: K's Walsh coordinates (za1, za2, zb1) for the three generators
L.append('matrix MK[3][3]=uW[1,1],uW[2,1],uW[1,1], pW[1,1]+eW[1,1],pW[2,1]+eW[2,1],pW[1,1]-eW[1,1], dW[1,1],dW[2,1],-dW[1,1]; poly dk=det(MK);')
L.append('proc perm4(matrix M){ poly s=0; int a1,a2,a3,a4; for(a1=1;a1<=4;a1++){for(a2=1;a2<=4;a2++){ if(a2!=a1){ for(a3=1;a3<=4;a3++){ if((a3!=a1)&&(a3!=a2)){ a4=10-a1-a2-a3; s=s+M[1,a1]*M[2,a2]*M[3,a3]*M[4,a4]; }}}}} return(s);}')
L.append('list CC; for(j=1;j<=5;j++){ matrix M[4][4]; c=0; for(k=1;k<=5;k++){ if(k!=j){ c++; for(i=1;i<=4;i++){ M[i,c]=1+Y[i,k]; } } } CC[j]=perm4(M)-24; kill M; }')
L.append('ideal E; for(j=1;j<=5;j++){ if(j!=3){ poly F=CC[j]-mm[j]*CC[3]; matrix T=coef(F,sa*sb*sc*t); for(k=1;k<=ncols(T);k++){E=E,T[2,k];} kill F; kill T; } }')
L.append('E=E,ii^2+1,(transpose(uW)*pW)[1,1],(transpose(pW)*pW)[1,1]-1,(transpose(dW)*eW)[1,1],(transpose(eW)*eW)[1,1]-1;')
L.append('E=E,%d*p1+%d*p2+%d*p3,%d*e1+%d*e2+%d*e3;'%(q1+q2))
L.append('E=E,r1*dk-1,r2*(%d*uW[1,1]+%d*uW[2,1]+%d*uW[3,1])-1,r3*(%d*dW[1,1]+%d*dW[2,1]+%d*dW[3,1])-1;'%(q1+q2))
L.append('ring R2=%s,(%s),dp; option(redSB); LIB "elim.lib"; ideal E=imap(R,E); ideal I=std(E);'%(P,','.join(unk)))
L.append('printf("C21CC0 before Z-saturation p=%s: dim %%s unit %%s",dim(I),(reduce(1,I)==0));'%P)
L.append('if(reduce(1,I)!=0){ ideal S=std(sat(I,ideal(%s))); printf("C21CC0 m_a = m_b = 0, column-centred, Z != 0 mod K, p=%s: dim %%s unit %%s",dim(S),(reduce(1,S)==0)); }'%(','.join(zv),P))
L.append('quit;')
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
