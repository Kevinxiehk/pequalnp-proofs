# (PL) K version on FIVE active columns, sign pattern SG (5 chars), quaternion parametrisation B_j = eps_j Rot(s_j, v_j).
# Degree 2 (equivalent to sum B_j = 3): s_j^2 + v_j.v_j = 1, sum eps_j v_j v_j^T = (c/2) I, sum eps_j s_j v_j = 0, c = (sum eps - 3)/2.
# Degree 3: for each j, F_j = sum_{k<l, k,l != j} t(A_j x, A_k x, A_l x) == 0  (t = polarised x1x2x3, Walsh coordinates).
# A_j = |v|^2 I - v v^T - s [v]_x (eps = +1; vanishes iff v = 0) ;  A_j = s^2 I + v v^T + s [v]_x (eps = -1; never 0).
# Saturation only by the ideals (v_j) of the eps = +1 columns.   usage: python3 quat5.py SG OUT [P]
import sys
SG=sys.argv[1]; out=sys.argv[2]; P=sys.argv[3] if len(sys.argv)>3 else '0'
s_=sum(1 if x=='+' else -1 for x in SG); c2='(%d)/4'%(s_-3)   # c/2 = (s-3)/4
names=[]
for j in range(5): names+=['s%d'%j,'a%d'%j,'b%d'%j,'d%d'%j]
L=['ring R=%s,(%s,x1,x2,x3),dp; option(redSB);'%(P,','.join(names)),'matrix Id[3][3]=1,0,0,0,1,0,0,0,1; matrix X[3][1]=x1,x2,x3; list A; ideal E;']
L.append('matrix VV[3][3]; matrix SV[3][1];')
for j in range(5):
    e=1 if SG[j]=='+' else -1
    L.append('matrix v%d[3][1]=a%d,b%d,d%d; poly n%d=a%d^2+b%d^2+d%d^2; matrix c%d[3][3]=0,-d%d,b%d,d%d,0,-a%d,-b%d,a%d,0;'%((j,)*15))
    L.append('E=E,s%d^2+n%d-1; VV=VV+(%d)*v%d*transpose(v%d); SV=SV+(%d)*s%d*v%d;'%(j,j,e,j,j,e,j,j))
    if e==1: L.append('matrix A%d[3][3]; A%d=n%d*Id; A%d=A%d-v%d*transpose(v%d); A%d=A%d-s%d*c%d; A[%d]=A%d;'%((j,)*11+(j+1,j)))
    else:    L.append('matrix A%d[3][3]; A%d=s%d^2*Id; A%d=A%d+v%d*transpose(v%d); A%d=A%d+s%d*c%d; A[%d]=A%d;'%((j,)*11+(j+1,j)))
L.append('int i; int k; poly cc=%d; cc=cc/4; matrix Wm=VV-cc*Id; for(i=1;i<=3;i++){for(k=i;k<=3;k++){E=E,Wm[i,k];}} for(i=1;i<=3;i++){E=E,SV[i,1];}'%(s_-3))
L.append('proc t3(matrix x, matrix y, matrix z){ return(x[1,1]*y[2,1]*z[3,1]+x[1,1]*y[3,1]*z[2,1]+x[2,1]*y[1,1]*z[3,1]+x[2,1]*y[3,1]*z[1,1]+x[3,1]*y[1,1]*z[2,1]+x[3,1]*y[2,1]*z[1,1]); }')
L.append('list Y; for(i=1;i<=5;i++){ matrix Mi=A[i]; Y[i]=Mi*X; kill Mi; }')
L.append('int j; int l; int q; for(j=1;j<=5;j++){ poly F=0; for(k=1;k<=5;k++){ for(l=k+1;l<=5;l++){ if((k!=j)&&(l!=j)){ F=F+t3(Y[j],Y[k],Y[l]); } } } matrix C=coef(F,x1*x2*x3); for(q=1;q<=ncols(C);q++){E=E,C[2,q];} kill F; kill C; }')
L.append('ring R2=%s,(%s),dp; option(redSB); LIB "elim.lib"; ideal E=imap(R,E); ideal G=std(E); printf("QUAT5 %s p=%s: dim %%s unit %%s",dim(G),(reduce(1,G)==0));'%(P,','.join(names),SG,P))
for j in range(5):
    if SG[j]=='+': L.append('G=std(sat(G,ideal(a%d,b%d,d%d))); printf("  sat v%d: dim %%s unit %%s",dim(G),(reduce(1,G)==0));'%(j,j,j,j))
L.append('printf("RESULT QUAT5 %s p=%s: unit %%s",(reduce(1,G)==0)); quit;'%(SG,P))
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
