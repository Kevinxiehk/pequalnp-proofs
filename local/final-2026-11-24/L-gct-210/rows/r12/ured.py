# The special line d = u: K_u = span{u e_a, p e_a, u e_b} (u^perp (x) e_a + C u (x) e_b), column-centred (4,1) extensions, REDUCED Z [R13.2].
# Walsh: u = (al^2-1, ii(al^2+1), 2 al), p = (al, ii al, 1) (= u'/2, orthogonal to u, never parallel to u), w = (1, ii, 0) (<w,u> = -2 != 0);
# at infinity: u = (1, ii, 0), p = (0,0,1), w = (1,-ii,0).
#  chart B (m_a = 0, m_b = 1):           Z = (0, eta p, ac u + pc p, ad u + pd p, ae u + pe p)
#  chart C (m_a = m_b = 0, m_c = 1):     Z = (0, 0, m_t zeta + al_t u)_t,  zeta = zp p + zw w
# usage: python3 -I ured.py P CHART(B|C) INF(0|1) OUT
import sys
P,CH,INF,out=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
par=([] if INF else ['al'])+['ii']
if CH=='B': zv=['eta','ac','pc','ad','pd','ae','pe']; mv=['m2','m3','m4']; mm='0,1,m2,m3,m4'; K0=2
else: zv=['zp','zw','ac','ad','ae']; mv=['m3']; mm='0,0,1,m3,-1-m3'; K0=3
unk=par+zv+mv
L=['ring R=%s,(s1,s2_,s3,t,%s),dp; option(redSB); LIB "elim.lib";'%(P,','.join(unk))]
L.append('matrix H[4][3]=1,1,1,1,-1,-1,-1,1,-1,-1,-1,1;')
if INF: L.append('matrix uW[3][1]=1,ii,0; matrix pW[3][1]=0,0,1; matrix wW[3][1]=1,-ii,0;')
else: L.append('matrix uW[3][1]=al^2-1,ii*(al^2+1),2*al; matrix pW[3][1]=al,ii*al,1; matrix wW[3][1]=1,ii,0;')
L.append('matrix uM=H*uW; matrix pM=H*pW; matrix wM=H*wW; int i; int j; int k; int c; list mm=%s; matrix Z[4][5];'%mm)
if CH=='B':
    L.append('for(i=1;i<=4;i++){ Z[i,1]=0; Z[i,2]=eta*pM[i,1]; Z[i,3]=ac*uM[i,1]+pc*pM[i,1]; Z[i,4]=ad*uM[i,1]+pd*pM[i,1]; Z[i,5]=ae*uM[i,1]+pe*pM[i,1]; }')
else:
    L.append('for(i=1;i<=4;i++){ poly ze=zp*pM[i,1]+zw*wM[i,1]; Z[i,1]=0; Z[i,2]=0; Z[i,3]=ze+ac*uM[i,1]; Z[i,4]=m3*ze+ad*uM[i,1]; Z[i,5]=(-1-m3)*ze+ae*uM[i,1]; kill ze; }')
L.append('matrix Y[4][5]; for(i=1;i<=4;i++){ for(j=1;j<=5;j++){ Y[i,j]=t*Z[i,j]; } Y[i,1]=Y[i,1]+s1*uM[i,1]+s2_*pM[i,1]; Y[i,2]=Y[i,2]+s3*uM[i,1]; }')
L.append('proc perm4(matrix M){ poly s=0; int a1,a2,a3,a4; for(a1=1;a1<=4;a1++){for(a2=1;a2<=4;a2++){ if(a2!=a1){ for(a3=1;a3<=4;a3++){ if((a3!=a1)&&(a3!=a2)){ a4=10-a1-a2-a3; s=s+M[1,a1]*M[2,a2]*M[3,a3]*M[4,a4]; }}}}} return(s);}')
L.append('list CC; for(j=1;j<=5;j++){ matrix M[4][4]; c=0; for(k=1;k<=5;k++){ if(k!=j){ c++; for(i=1;i<=4;i++){ M[i,c]=1+Y[i,k]; } } } CC[j]=perm4(M)-24; kill M; }')
L.append('ideal E=ii^2+1;')
if CH=='B': L.append('E=E,1+m2+m3+m4;')
L.append('for(j=1;j<=5;j++){ if(j!=%d){ poly F=CC[j]-mm[j]*CC[%d]; matrix T=coef(F,s1*s2_*s3*t); for(k=1;k<=ncols(T);k++){E=E,T[2,k];} kill F; kill T; } }'%(K0,K0))
# self-check: K_u strongly level
L.append('matrix Y0=subst(Y,t,0); poly chk=0; for(j=1;j<=5;j++){ matrix M[4][4]; c=0; for(k=1;k<=5;k++){ if(k!=j){ c++; for(i=1;i<=4;i++){ M[i,c]=1+Y0[i,k]; } } } chk=chk+(perm4(M)-24)^2; kill M; }')
L.append('ring R2=%s,(%s),dp; option(redSB); LIB "elim.lib"; ideal E=imap(R,E); ideal I=std(E); poly chk=imap(R,chk); chk=reduce(chk,std(ideal(ii^2+1)));'%(P,','.join(unk)))
L.append('printf("K_u strongly level check (0 = ok): %s",chk);')
L.append('printf("URED chart %s inf %d p=%s: dim %%s unit %%s",dim(I),(reduce(1,I)==0)); I=std(sat(I,ideal(%s))); printf("  after Z != 0 saturation: dim %%s unit %%s",dim(I),(reduce(1,I)==0));'%(CH,INF,P,','.join(zv)))
if CH=='C': L.append('if(reduce(1,I)!=0){ ideal S=std(sat(I,m3*(1+m3))); printf("  after saturation by m3*(1+m3) (m not two-column): dim %s unit %s",dim(S),(reduce(1,S)==0)); }')
L.append('quit;')
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
