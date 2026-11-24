# Family B, column-centred (4,1) extensions with REDUCED Z (rows, round 13).  K = span{d e_a, d e_b, x e_c}, d = H dW (conic, ga or infinity),
# x = H xW, xW = dW x sg(dW,dW).  Reductions [rigorous, R13.1]:
#  chart A (m_a = 1): z_k orthogonal to d for all k, so modulo K:  Z = (aa x, ab x, ac d, ad x + bd d, ae x + be d).
#  chart C (m_a = m_b = 0, m_c = 1): z_k orthogonal to x (k != c), z_a = z_b = 0 mod K; z_c modulo x via the gauge rA.z_c = 0 (Rabinowitsch
#           on rA.x; second gauge rB), z_d, z_e in x^perp.
# usage: python3 -I bred.py P CHART(A|C) GAUGE(0|1) INF(0|1) OUT [num=<i>]
import sys
P,CH,GC,INF,out=sys.argv[1],sys.argv[2],int(sys.argv[3]),int(sys.argv[4]),sys.argv[5]
NUM=[a[4:] for a in sys.argv if a.startswith('num=')]
r=[(2,3,5),(3,-7,2)][GC]
par=([] if INF else ['ga'])+['ii','rd']
if CH=='A':
    zv=['aa','ab','ac','ad','bd','ae','be']; mv=['m1','m2','m3','m4']; mm='1,m1,m2,m3,m4'; extra=[]
elif CH=='D':
    zv=['ac','ad','ae','mu']; mv=['m3']; mm='0,0,1,m3,-1-m3'; extra=[]
else:
    zv=['c1','c2','c3','d1','d2','d3','e1','e2','e3','rg']; mv=['m3']; mm='0,0,1,m3,-1-m3'; extra=[]
unk=par+zv+mv
L=['ring R=%s,(s1,s2_,s3,t,%s),dp; option(redSB); LIB "elim.lib";'%(P,','.join(unk))]
L.append('matrix H[4][3]=1,1,1,1,-1,-1,-1,1,-1,-1,-1,1; matrix dW[3][1]=%s;'%('1,ii,0' if INF else 'ga^2-1,ii*(ga^2+1),2*ga'))
L.append('matrix sW[3][1]=2*dW[2,1]*dW[3,1],2*dW[1,1]*dW[3,1],2*dW[1,1]*dW[2,1]; matrix xW[3][1]=dW[2,1]*sW[3,1]-dW[3,1]*sW[2,1],dW[3,1]*sW[1,1]-dW[1,1]*sW[3,1],dW[1,1]*sW[2,1]-dW[2,1]*sW[1,1];')
L.append('matrix dM=H*dW; matrix xM=H*xW; int i; int j; int k; int c; list mm=%s; matrix Z[4][5];'%mm)
if CH=='A':
    L.append('for(i=1;i<=4;i++){ Z[i,1]=aa*xM[i,1]; Z[i,2]=ab*xM[i,1]; Z[i,3]=ac*dM[i,1]; Z[i,4]=ad*xM[i,1]+bd*dM[i,1]; Z[i,5]=ae*xM[i,1]+be*dM[i,1]; }')
elif CH=='D':
    L.append('matrix sM=H*sW; for(i=1;i<=4;i++){ Z[i,1]=0; Z[i,2]=0; Z[i,3]=ac*dM[i,1]+mu*sM[i,1]; Z[i,4]=ad*dM[i,1]+mu*m3*sM[i,1]; Z[i,5]=ae*dM[i,1]+mu*(-1-m3)*sM[i,1]; }')
else:
    L.append('matrix cW[3][1]=c1,c2,c3; matrix dZ[3][1]=d1,d2,d3; matrix eZ[3][1]=e1,e2,e3; matrix cM=H*cW; matrix dZM=H*dZ; matrix eZM=H*eZ;')
    L.append('for(i=1;i<=4;i++){ Z[i,1]=0; Z[i,2]=0; Z[i,3]=cM[i,1]; Z[i,4]=dZM[i,1]; Z[i,5]=eZM[i,1]; }')
L.append('matrix Y[4][5]; for(i=1;i<=4;i++){ for(j=1;j<=5;j++){ Y[i,j]=t*Z[i,j]; } Y[i,1]=Y[i,1]+s1*dM[i,1]; Y[i,2]=Y[i,2]+s2_*dM[i,1]; Y[i,3]=Y[i,3]+s3*xM[i,1]; }')
L.append('proc perm4(matrix M){ poly s=0; int a1,a2,a3,a4; for(a1=1;a1<=4;a1++){for(a2=1;a2<=4;a2++){ if(a2!=a1){ for(a3=1;a3<=4;a3++){ if((a3!=a1)&&(a3!=a2)){ a4=10-a1-a2-a3; s=s+M[1,a1]*M[2,a2]*M[3,a3]*M[4,a4]; }}}}} return(s);}')
L.append('list CC; for(j=1;j<=5;j++){ matrix M[4][4]; c=0; for(k=1;k<=5;k++){ if(k!=j){ c++; for(i=1;i<=4;i++){ M[i,c]=1+Y[i,k]; } } } CC[j]=perm4(M)-24; kill M; }')
K0=1 if CH=='A' else 3
L.append('ideal E=%s;'%('ii-(%s)'%NUM[0] if NUM else 'ii^2+1'))
L.append('E=E,rd*dW[1,1]*dW[2,1]*dW[3,1]-1;')   # d1 d2 d3 != 0: x not parallel to d (else K = d (x) C^3, the (1,2) stratum)
if CH=='A': L.append('E=E,1+m1+m2+m3+m4;')
L.append('for(j=1;j<=5;j++){ if(j!=%d){ poly F=CC[j]-mm[j]*CC[%d]; matrix T=coef(F,s1*s2_*s3*t); for(k=1;k<=ncols(T);k++){E=E,T[2,k];} kill F; kill T; } }'%(K0,K0))
if CH=='C':
    L.append('E=E,(transpose(xW)*dZ)[1,1],(transpose(xW)*eZ)[1,1],%d*c1+%d*c2+%d*c3,rg*(%d*xW[1,1]+%d*xW[2,1]+%d*xW[3,1])-1;'%(r+r))
L.append('ring R2=%s,(%s),dp; option(redSB); LIB "elim.lib"; ideal E=imap(R,E); ideal I=std(E);'%(P,','.join(unk)))
zsat=[v for v in zv if v!='rg']
L.append('printf("BRED chart %s gauge %d inf %d p=%s: dim %%s unit %%s",dim(I),(reduce(1,I)==0)); I=std(sat(I,ideal(%s))); printf("  after Z != 0 saturation: dim %%s unit %%s",dim(I),(reduce(1,I)==0));'%(CH,GC,INF,P,','.join(zsat)))
L.append('quit;')
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
