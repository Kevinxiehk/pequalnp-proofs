# (PL) K version, NC active columns, sign pattern SG: quaternion degree-2 data + ONLY the SUMMED cubic sum_j c(B_j x) = (NC-2) c(x)
# (c = x1 x2 x3 in Walsh coordinates; the sum over j of the cubic conditions F_j).  A relaxation of the full system (unit => unit).
# Saturation only by v_j for eps = +1 columns.   usage: python3 sumq.py SG OUT [P]
import sys
SG=sys.argv[1]; out=sys.argv[2]; P=sys.argv[3] if len(sys.argv)>3 else '0'; NC=len(SG)
s_=sum(1 if x=='+' else -1 for x in SG)
names=[]
for j in range(NC): names+=['s%d'%j,'a%d'%j,'b%d'%j,'d%d'%j]
L=['ring R=%s,(%s,x1,x2,x3),dp; option(redSB);'%(P,','.join(names)),'matrix Id[3][3]=1,0,0,0,1,0,0,0,1; matrix X[3][1]=x1,x2,x3; ideal E; matrix VV[3][3]; matrix SV[3][1]; poly CS=0;']
L.append('proc cub(matrix y){ return(y[1,1]*y[2,1]*y[3,1]); }')
for j in range(NC):
    e=1 if SG[j]=='+' else -1
    L.append('matrix v%d[3][1]=a%d,b%d,d%d; poly n%d=a%d^2+b%d^2+d%d^2; matrix c%d[3][3]=0,-d%d,b%d,d%d,0,-a%d,-b%d,a%d,0;'%((j,)*15))
    L.append('E=E,s%d^2+n%d-1; VV=VV+(%d)*v%d*transpose(v%d); SV=SV+(%d)*s%d*v%d;'%(j,j,e,j,j,e,j,j))
    L.append('matrix B%d[3][3]; B%d=(s%d^2-n%d)*Id; B%d=B%d+2*v%d*transpose(v%d); B%d=B%d+2*s%d*c%d; B%d=(%d)*B%d; CS=CS+cub(B%d*X);'%((j,)*12+(j,e,j,j)))
L.append('int i; int k; poly cc=%d; cc=cc/4; matrix Wm=VV-cc*Id; for(i=1;i<=3;i++){for(k=i;k<=3;k++){E=E,Wm[i,k];}} for(i=1;i<=3;i++){E=E,SV[i,1];}'%(s_-(NC-2)))
L.append('CS=CS-(%d)*cub(X); matrix C=coef(CS,x1*x2*x3); for(k=1;k<=ncols(C);k++){E=E,C[2,k];}'%(NC-2))
L.append('ring R2=%s,(%s),dp; option(redSB); LIB "elim.lib"; ideal E=imap(R,E); ideal G=std(E); printf("SUMQ %s p=%s: dim %%s unit %%s",dim(G),(reduce(1,G)==0));'%(P,','.join(names),SG,P))
for j in range(NC):
    if SG[j]=='+': L.append('G=std(sat(G,ideal(a%d,b%d,d%d))); printf("  sat v%d: dim %%s unit %%s",dim(G),(reduce(1,G)==0));'%(j,j,j,j))
L.append('printf("RESULT SUMQ %s p=%s: unit %%s",(reduce(1,G)==0)); quit;'%(SG,P))
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
