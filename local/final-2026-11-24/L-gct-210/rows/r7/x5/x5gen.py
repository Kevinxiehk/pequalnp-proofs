# X5 generator (rows, round 7): principal (5,1) space with kernel type (2,2,1), normal form of COMPUTE-rows X5 (verified by verify2).
# usage: python3 x5gen.py P CHART OUT [CAL]
#   CHART in {11,10,01,00}: first digit: n chart (1: a2=1; 0: a1=1,a2=0), second: n' chart (b2=1 / b1=1,b2=0).
#   CAL = 'cal': calibration variant: N replaced by the LINE {Z(ph, r*ph)} (unknown r)  -> a (4,1)-type system.
# Columns a,b,c,d,e = 0,1,2,3,4; m = (1, mb, 0, md, -1-mb-md); K = span{v e_2^T, n((1-lam)e_0+(1+lam)e_1)^T, n'((1-mu)e_0+(1+mu)e_1)^T},
# lam*mu = 1, n, n' isotropic (Walsh conic parametrisation), v = n x n' (Walsh cross product);
# Z(ph,et) = A m^T + t n (e_0 - e_1)^T, A = (kc ph/4) 1 + ph v + et n, t = (lam-1) et, kc^2 = (4/3)<v,v>, lam(1-mb) = 1+mb.
# Equations: all (s1,s2,s3,ph,et)-coefficients of C_j(Y) - 24 - m_j (C_0(Y) - 24), j = 1..4, Y = s1 K1 + s2 K2 + s3 K3 + Z(ph,et).
import sys
P=sys.argv[1]; chart=sys.argv[2]; out=sys.argv[3]; cal=len(sys.argv)>4
idv='s1,s2,s3,ph,et'
unk='a1,a2,b1,b2,lam,mu,mb,md,kc,ii'+(',rr' if cal else '')
S=[]
S.append('ring R=%s,(%s,%s),dp;'%(P,idv,unk))
S.append('option(redSB);')
S.append('matrix H[4][3]=1,1,1,1,-1,-1,-1,1,-1,-1,-1,1;')
S.append('matrix nW[3][1]=a1^2-a2^2,ii*(a1^2+a2^2),2*a1*a2;')
S.append('matrix pW[3][1]=b1^2-b2^2,ii*(b1^2+b2^2),2*b1*b2;')
S.append('matrix vW[3][1]=nW[2,1]*pW[3,1]-nW[3,1]*pW[2,1],nW[3,1]*pW[1,1]-nW[1,1]*pW[3,1],nW[1,1]*pW[2,1]-nW[2,1]*pW[1,1];')
S.append('matrix n4=H*nW; matrix p4=H*pW; matrix v4=H*vW;')
S.append('poly vv=4*(vW[1,1]^2+vW[2,1]^2+vW[3,1]^2);')
S.append('list mm=1,mb,0,md,-1-mb-md;')
S.append('poly ETA=%s;'%('rr*ph' if cal else 'et'))
S.append('poly tt=(lam-1)*ETA;')
S.append('matrix Y[4][5]; int i; int j;')
S.append('for(i=1;i<=4;i++){ poly Ai=kc*ph/4+ph*v4[i,1]+ETA*n4[i,1];')
S.append('  for(j=1;j<=5;j++){ Y[i,j]=Ai*mm[j]; }')
S.append('  Y[i,3]=Y[i,3]+s1*v4[i,1];')
S.append('  Y[i,1]=Y[i,1]+s2*(1-lam)*n4[i,1]+s3*(1-mu)*p4[i,1]+tt*n4[i,1];')
S.append('  Y[i,2]=Y[i,2]+s2*(1+lam)*n4[i,1]+s3*(1+mu)*p4[i,1]-tt*n4[i,1];')
S.append('  kill Ai; }')
S.append('proc perm4(matrix M){ poly s=0; int p1,p2,p3,p4;')
S.append(' for(p1=1;p1<=4;p1++){for(p2=1;p2<=4;p2++){ if(p2!=p1){ for(p3=1;p3<=4;p3++){ if((p3!=p1)&&(p3!=p2)){ p4=10-p1-p2-p3;')
S.append('   s=s+M[1,p1]*M[2,p2]*M[3,p3]*M[4,p4]; }}}}}')
S.append(' return(s);}')
S.append('list CC; int k; int c;')
S.append('for(j=1;j<=5;j++){ matrix M[4][4]; c=0; for(k=1;k<=5;k++){ if(k!=j){ c++; for(i=1;i<=4;i++){ M[i,c]=1+Y[i,k]; } } } CC[j]=perm4(M)-24; kill M; }')
S.append('ideal E;')
S.append('for(j=2;j<=5;j++){ poly F=CC[j]-mm[j]*CC[1]; matrix T=coef(F,s1*s2*s3*ph*et); for(k=1;k<=ncols(T);k++){ E=E,T[2,k]; } kill F; kill T; }')
ch={'1':('a2=1','a2-1'),'0':('a1=1,a2=0','a1-1,a2')}
S.append('ring R2=%s,(%s),dp; option(redSB);'%(P,unk))
S.append('ideal E=imap(R,E); poly vv=imap(R,vv);')
extra=['lam*mu-1','lam*(1-mb)-(1+mb)','kc^2-4/3*vv','ii^2+1']
extra.append(ch[chart[0]][1].replace('a','a')); extra.append(ch[chart[1]][1].replace('a','b'))
S.append('ideal I=E,%s;'%(','.join(extra)))
S.append('I=simplify(I,2+4+8);')
S.append('printf("X5 chart %s %s: %%s generators",size(I));'%(chart,'CAL' if cal else ''))
S.append('int t0=timer; ideal G=std(I);')
S.append('printf("X5 chart %s %s p=%s: dim %%s, unit %%s, size %%s",dim(G),(reduce(1,G)==0),size(G));'%(chart,'CAL' if cal else '',P))
S.append('if(size(G)<40){print(G);}')
S.append('LIB "elim.lib"; poly nn=imap(R,nW)[1,1]*imap(R,pW)[1,1]+imap(R,nW)[2,1]*imap(R,pW)[2,1]+imap(R,nW)[3,1]*imap(R,pW)[3,1];')
S.append('ideal G2=sat(G,ideal(nn)); G2=std(G2);')
S.append('printf("X5 chart %s %s p=%s: after saturation by <n,n2>: dim %%s, unit %%s",dim(G2),(reduce(1,G2)==0));'%(chart,'CAL' if cal else '',P))
S.append('if(size(G2)<40){print(G2);}')
S.append('quit;')
open(out,'w').write('\n'.join(S)+'\n')
print('written',out)
