# (PL) K version, four active columns, sign pattern SG (of ++++, ++--, ----): B_j = eps_j Rot(q_j), q_j = (s_j, v_j) complex quaternion,
# s_j^2 + v_j.v_j = 1, Rot(q) x = (s^2 - v.v) x + 2 (v.x) v + 2 s (v x x)  (covers all of O(3,C) with eps).  Lemma TR fixes s_j^2 = tr(g_j)^2/4.
# Equations: sum_j B_j = 2 I, and the four triple products t(A_a s, A_b s, A_c s) == 0 (t = polarised x1x2x3, Walsh coordinates),
# A_j = (I - B_j)/2.  Independent of the tetrahedral base configuration used in orbgen.py.   usage: python3 quat4.py SG OUT [P]
import sys
from fractions import Fraction as Fr
SG=sys.argv[1]; out=sys.argv[2]; P=sys.argv[3] if len(sys.argv)>3 else '0'
s_=sum(1 if x=='+' else -1 for x in SG); c=Fr(s_-2,2)
qs=[]; L=[]
names=[]
for j in range(4): names+=['s%d'%j,'a%d'%j,'b%d'%j,'d%d'%j]
L.append('ring R=%s,(%s,x1,x2,x3),dp; option(redSB);'%(P,','.join(names)))
L.append('matrix Id[3][3]=1,0,0,0,1,0,0,0,1; matrix X[3][1]=x1,x2,x3; list A; ideal E;')
for j in range(4):
    e=1 if SG[j]=='+' else -1; t2=(4+c)*(1-c*e/2); s2=t2/4
    L.append('matrix v%d[3][1]=a%d,b%d,d%d; poly vv%d=a%d^2+b%d^2+d%d^2;'%((j,)*8))
    L.append('matrix cx%d[3][3]=0,-d%d,b%d,d%d,0,-a%d,-b%d,a%d,0;'%((j,)*7))
    L.append('matrix B%d[3][3]; B%d=(s%d^2-vv%d)*Id; B%d=B%d+2*v%d*transpose(v%d); B%d=B%d+2*s%d*cx%d; B%d=%d*B%d;'%((j,)*12+(j,e,j)))
    L.append('E=E,s%d^2+vv%d-1,s%d^2-(%s); A[%d]=(Id-B%d)/2;'%(j,j,j,str(s2),j+1,j))
L.append('matrix S=B0+B1+B2+B3-2*Id; int i; int k; for(i=1;i<=3;i++){for(k=1;k<=3;k++){E=E,S[i,k];}}')
L.append('proc t3(matrix x, matrix y, matrix z){ return(x[1,1]*y[2,1]*z[3,1]+x[1,1]*y[3,1]*z[2,1]+x[2,1]*y[1,1]*z[3,1]+x[2,1]*y[3,1]*z[1,1]+x[3,1]*y[1,1]*z[2,1]+x[3,1]*y[2,1]*z[1,1]); }')
L.append('list V; for(i=1;i<=4;i++){ matrix Mi=A[i]; V[i]=Mi*X; kill Mi; }')
L.append('int a; int b; int cc; for(a=1;a<=4;a++){for(b=a+1;b<=4;b++){for(cc=b+1;cc<=4;cc++){ poly F=t3(V[a],V[b],V[cc]); matrix C=coef(F,x1*x2*x3); for(k=1;k<=ncols(C);k++){E=E,C[2,k];} kill F; kill C; }}}')
L.append('ring R2=%s,(%s),dp; option(redSB); ideal E=imap(R,E); ideal G=std(E);'%(P,','.join(names)))
L.append('printf("QUAT %s p=%s: dim %%s unit %%s size %%s",dim(G),(reduce(1,G)==0),size(G)); quit;'%(SG,P))
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
