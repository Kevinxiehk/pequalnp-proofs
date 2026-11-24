# CASE G plane test (support 4), variants of rows/r15/plane.py (PAT=G):
#  REAL: no Q(i).  Substitute y_2 -> i y_2 (D = diag(1,i,1)): the isotropic conic becomes c(s) = (s^2-1, s^2+1, 2s) (rational), and every
#        condition is (power of i) x (rational polynomial): x_2 -> -x_2 maps H to -(row permutation of H), so P_2, P_4 are even and P_3 odd in
#        the x_2-coordinates.  Checked per generator: g = g0 + ii*g1 with g0 = 0 or g1 = 0 (else PARITY FAIL); the nonzero part is kept.
#  LAG:  eliminate be_k, a_k: for distinct s_1..s_4, sum be_k c(s_k) = 0 forces be_k = la / w_k (w_k = prod_{j != k}(s_k - s_j)) and
#        sum al_k c(s_k) = 2 c(s0) forces al_k = 2 L_k(s0) + mu be_k (cubic Lagrange basis).  Gauge mu = 0, la = 1; scale e1, n by
#        W = prod_{a<b}(s_a - s_b):  n-column k = -(W/w_k) c(s_k)/2,  e1-column k = (W c(s0) - 2 (W/w_k) prod_{j != k}(s0 - s_j) c(s_k))/2.
#  FAM:  add the case-G point-family equations e_2(s) = 0, e_4(s) = -1 (R14.7, identity chart).
# usage: python3 -I planeG.py P OUT [REAL] [LAG] [FAM]
import sys
P,out=sys.argv[1],sys.argv[2]; opt=set(sys.argv[3:]); REAL='REAL' in opt; LAG='LAG' in opt
ks=[1,2,3,4]
unk=['s0','s1','s2','s3','s4']+([] if LAG else ['be2','be3','be4','a2','a3','a4'])+['rz']
L=['ring R=%s,(y1,y3,%s,ii),dp; option(redSB); LIB "elim.lib";'%(P,','.join(unk))]
L.append('matrix H[4][3]=1,1,1,1,-1,-1,-1,1,-1,-1,-1,1; matrix D[3][3]=1,0,0,0,%s,0,0,0,1; int i; int j; int k; int c;'%('ii' if REAL else '1'))
L.append('proc cc(poly s){ matrix v[3][1]=s^2-1,%s(s^2+1),2*s; return(v); }'%('' if REAL else 'ii*'))
L.append('matrix u=cc(s0);')
pairs=[(a,b) for a in ks for b in ks if a<b]
W='*'.join('(s%d-s%d)'%p for p in pairs)
if LAG:
    for k in ks:
        Wk='%d*%s'%((-1)**(k-1),'*'.join('(s%d-s%d)'%p for p in pairs if k not in p))
        Lk='*'.join('(s0-s%d)'%j for j in ks if j!=k)
        L.append('matrix n%d=(%s)*cc(s%d); matrix e%d=(%s)*u-2*(%s)*(%s)*cc(s%d);'%(k,Wk,k,k,W,Wk,Lk,k))
    L.append('matrix S1=%s; matrix S2=%s-2*(%s)*u;'%('+'.join('n%d'%k for k in ks),'+'.join('(%s)*u-e%d'%(W,k) for k in ks),W))
    L.append('ideal CHK=reduce(ideal(S1[1,1],S1[2,1],S1[3,1],S2[1,1],S2[2,1],S2[3,1]),std(ideal(ii^2+1))); printf("Lagrange identities hold: %s",size(CHK)==0);')
    L.append('ideal E=rz*%s-1;'%W)
else:
    for k in ks: L.append('matrix n%d=%s*cc(s%d); poly a%d_=%s; matrix e%d=u-a%d_*n%d;'%(k,'1' if k==1 else 'be%d'%k,k,k,'0' if k==1 else 'a%d'%k,k,k,k))
    L.append('ideal E; matrix S1=%s; matrix S2=%s-2*u; for(i=1;i<=3;i++){ E=E,S1[i,1],S2[i,1]; }'%('+'.join('n%d'%k for k in ks),'+'.join('a%d_*n%d'%(k,k) for k in ks)))
    L.append('E=E,rz*be2*be3*be4*%s-1;'%W)
if 'FAM' in opt: L.append('E=E,s1*s2+s1*s3+s2*s3+s1*s4+s2*s4+s3*s4,s1*s2*s3*s4+1;')
L.append('matrix Y[4][5]; matrix colW[3][1];')
for k in ks: L.append('colW=y1*e%d/2-y3*n%d/2; matrix cC%d=H*D*colW; for(i=1;i<=4;i++){ Y[i,%d]=cC%d[i,1]; }'%(k,k,k,k,k))
L.append('for(i=1;i<=4;i++){ Y[i,5]=0; }')
L.append('proc perm4(matrix M){ poly s=0; int a1,a2,a3,a4; for(a1=1;a1<=4;a1++){for(a2=1;a2<=4;a2++){ if(a2!=a1){ for(a3=1;a3<=4;a3++){ if((a3!=a1)&&(a3!=a2)){ a4=10-a1-a2-a3; s=s+M[1,a1]*M[2,a2]*M[3,a3]*M[4,a4]; }}}}} return(s);}')
L.append('ideal SI=std(ideal(ii^2+1)); ideal C0; ideal C1; int bad=0; poly g; poly g0; poly g1;')
L.append('for(j=1;j<=5;j++){ matrix M[4][4]; c=0; for(k=1;k<=5;k++){ if(k!=j){ c++; for(i=1;i<=4;i++){ M[i,c]=1+Y[i,k]; } } } poly F=perm4(M)-24; matrix T=coef(F,y1*y3); for(k=1;k<=ncols(T);k++){ if(deg(T[1,k])>=2){ g=reduce(T[2,k],SI); g0=subst(g,ii,0); g1=subst(diff(g,ii),ii,0); if(%s){ if((g0!=0) and (g1!=0)){ bad++; } poly gg; if(g0!=0){gg=g0;} else {gg=g1;} C0=C0,gg; if(deg(subst(T[1,k],y3,1))<=1){ C1=C1,gg; } } else { C0=C0,g; if(deg(subst(T[1,k],y3,1))<=1){ C1=C1,g; } } } } kill F; kill T; kill M; }'%('1' if REAL else '0'))
L.append('printf("parity failures: %s",bad);')
L.append('ring R2=%s,(%s),dp; option(redSB); ideal E0=imap(R,C0); ideal E1=imap(R,E); ideal EC1=imap(R,C1); ideal E=E0;'%(P,','.join(unk)) if REAL else
         'ring R2=%s,(%s,ii),dp; option(redSB); ideal E0=imap(R,C0); ideal E1=imap(R,E); ideal E=E0,E1,ii^2+1;'%(P,','.join(unk)))
if REAL: L.append('E=E,E1;')
if 'STAGED' in opt: L.append('ideal IP=std(EC1+E1); printf("stage 1 (y1-degree <= 1): dim %s unit %s",dim(IP),reduce(1,IP)==0); E=E+IP;')
L.append('ideal I=std(E); printf("PLANE-G %s p=%s: dim %%s unit %%s",dim(I),(reduce(1,I)==0));'%(' '.join(sorted(opt)),P))
L.append('quit;')
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
