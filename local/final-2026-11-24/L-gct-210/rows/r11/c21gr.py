# (4,1) spaces over the TWO-COLUMN (2,1) kernels, GAUGE-FIXED (rows, round 11).
# K = span{U = u(e0+e1)^T, W = (p+e)e0^T + (p-e)e1^T, D = d(e0-e1)^T}; Walsh coordinates; u = (al^2-1, ii(al^2+1), 2al), d likewise (ga);
# u.p = 0, p.p = 1, d.e = 0, e.e = 1; gauges p.q1 = 0, e.q2 = 0 (chart u.q1 != 0, d.q2 != 0: Rabinowitsch);
# Z modulo K: Z[0][0] = Z[1][0] = Z[0][1] = 0 (chart det M_K != 0: Rabinowitsch); m chart m_K0 = 1; c(Z) = m.
# Output: dim; saturation by prod of the other m_j (unit <=> a zero entry of m, i.e. a neutral column).   usage: python3 c21g.py P K0 OUT
import sys
P,K0,out=sys.argv[1],int(sys.argv[2]),sys.argv[3]
q1=(2,3,5); q2=(3,-7,2)
zs=['z%d%d'%(i,j) for i in range(4) for j in range(5) if (i,j) not in ((0,0),(1,0),(0,1))]
mv=['m%d'%k for k in range(5) if k!=K0]
unk=['al','ga','p1','p2','p3','e1','e2','e3','ii','r1','r2','r3']+zs+mv
L=['ring R=%s,(sa,sb,sc,t,%s),dp; option(redSB); LIB "elim.lib";'%(P,','.join(unk))]
L.append('matrix H[4][3]=1,1,1,1,-1,-1,-1,1,-1,-1,-1,1;')
L.append('matrix uW[3][1]=al^2-1,ii*(al^2+1),2*al; matrix dW[3][1]=ga^2-1,ii*(ga^2+1),2*ga; matrix pW[3][1]=p1,p2,p3; matrix eW[3][1]=e1,e2,e3;')
L.append('matrix u=H*uW; matrix d=H*dW; matrix pp=H*pW; matrix ee=H*eW;')
L.append('matrix Z[4][5]; int i; int j; int k; int c;')
for i in range(4):
    for j in range(5):
        if (i,j) not in ((0,0),(1,0),(0,1)): L.append('Z[%d,%d]=z%d%d;'%(i+1,j+1,i,j))
L.append('list mm=%s;'%','.join('1' if k==K0 else 'm%d'%k for k in range(5)))
L.append('matrix Y[4][5]; for(i=1;i<=4;i++){ Y[i,1]=sa*u[i,1]+sb*(pp[i,1]+ee[i,1])+sc*d[i,1]; Y[i,2]=sa*u[i,1]+sb*(pp[i,1]-ee[i,1])-sc*d[i,1]; for(j=1;j<=5;j++){Y[i,j]=Y[i,j]+t*Z[i,j];} }')
L.append('matrix MK[3][3]=u[1,1],u[2,1],u[1,1], pp[1,1]+ee[1,1],pp[2,1]+ee[2,1],pp[1,1]-ee[1,1], d[1,1],d[2,1],-d[1,1]; poly dk=det(MK);')
L.append('proc perm4(matrix M){ poly s=0; int a1,a2,a3,a4; for(a1=1;a1<=4;a1++){for(a2=1;a2<=4;a2++){ if(a2!=a1){ for(a3=1;a3<=4;a3++){ if((a3!=a1)&&(a3!=a2)){ a4=10-a1-a2-a3; s=s+M[1,a1]*M[2,a2]*M[3,a3]*M[4,a4]; }}}}} return(s);}')
L.append('list CC; for(j=1;j<=5;j++){ matrix M[4][4]; c=0; for(k=1;k<=5;k++){ if(k!=j){ c++; for(i=1;i<=4;i++){ M[i,c]=1+Y[i,k]; } } } CC[j]=perm4(M)-24; kill M; }')
L.append('ideal E; for(j=1;j<=5;j++){ poly cs=0; for(i=1;i<=4;i++){cs=cs+Z[i,j];} E=E,cs-mm[j]; }')
L.append('for(j=1;j<=5;j++){ if(j!=%d){ poly F=CC[j]-mm[j]*CC[%d]; matrix T=coef(F,sa*sb*sc*t); for(k=1;k<=ncols(T);k++){E=E,T[2,k];} kill F; kill T; } }'%(K0+1,K0+1))
L.append('E=E,ii^2+1,1+%s;'%('+'.join(mv)))
# hand reduction (R11.1): for m not two-column, <d0, D_Z> = 0 and <d0, s_Z - P_Z> = 0 (C^4 coordinates; P_Z = z_0 + z_1, D_Z = z_0 - z_1)
L.append('poly del=0; poly bet=0; for(i=1;i<=4;i++){ poly sZ=0; for(j=1;j<=5;j++){sZ=sZ+Z[i,j];} del=del+d[i,1]*(Z[i,1]-Z[i,2]); bet=bet+d[i,1]*(sZ-Z[i,1]-Z[i,2]); kill sZ; } E=E,del,bet;')
L.append('E=E,(transpose(uW)*pW)[1,1],(transpose(pW)*pW)[1,1]-1,(transpose(dW)*eW)[1,1],(transpose(eW)*eW)[1,1]-1;')
L.append('E=E,%d*p1+%d*p2+%d*p3,%d*e1+%d*e2+%d*e3;'%(q1+q2))
L.append('E=E,r1*dk-1,r2*(%d*uW[1,1]+%d*uW[2,1]+%d*uW[3,1])-1,r3*(%d*dW[1,1]+%d*dW[2,1]+%d*dW[3,1])-1;'%(q1+q2))
L.append('ring R2=%s,(%s),dp; option(redSB); LIB "elim.lib"; ideal E=imap(R,E); ideal I=std(E);'%(P,','.join(unk)))
L.append('printf("C21G-R m%d p=%s: dim %%s unit %%s",dim(I),(reduce(1,I)==0)); if(reduce(1,I)!=0){ ideal S=std(sat(I,ideal(%s))); printf("   after saturation by the other m_j: dim %%s unit %%s",dim(S),(reduce(1,S)==0)); }'%(K0,P,'*'.join(mv)))
L.append('quit;')
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
