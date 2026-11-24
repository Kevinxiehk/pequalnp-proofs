# PRINCIPAL PLANE TEST (rows, round 17; (PL) reflection columns).  If column k of a principal 5-column kernel is a REFLECTION
# (B_k = -Ad(q_k), s_k = 0), then Pi := ker A_k = R^{-1}(P), P = mirror plane (nondegenerate, |v_k| = 1), is a strongly level PLANE on the
# other four columns with injective row-sum map onto P.  Normal form (Lemma RS for planes): basis e1, e2 of Pi with R e_i = p_i orthonormal,
# column j: A_j e_i = (p_i - b_ji)/2 with (b_j1, b_j2) orthonormal (B_j restricted to P), sum_j b_ji = 2 p_i (four columns).
# Conditions: P_3, P_4 (and P_2 as a check) of every deletion; saturation: every plane column nonzero.  usage: python3 -I pplane.py P OUT
import sys
P,out=sys.argv[1],sys.argv[2]
vs=['p%d%d'%(i,c) for i in (1,2) for c in (1,2,3)]+['b%d%d%d'%(j,i,c) for j in (1,2,3,4) for i in (1,2) for c in (1,2,3)]
L=['ring R=%s,(y1,y2,%s),dp; option(redSB); LIB "elim.lib";'%(P,','.join(vs))]
L.append('matrix H[4][3]=1,1,1,1,-1,-1,-1,1,-1,-1,-1,1; int i; int j; int k; int c;')
L.append('matrix p1[3][1]=p11,p12,p13; matrix p2[3][1]=p21,p22,p23;')
for j in (1,2,3,4):
    L.append('matrix b%d1[3][1]=b%d11,b%d12,b%d13; matrix b%d2[3][1]=b%d21,b%d22,b%d23;'%((j,)*8))
L.append('proc dt(matrix a, matrix b){ return(a[1,1]*b[1,1]+a[2,1]*b[2,1]+a[3,1]*b[3,1]); }')
L.append('ideal E=dt(p1,p1)-1,dt(p2,p2)-1,dt(p1,p2);')
for j in (1,2,3,4):
    L.append('E=E,dt(b%d1,b%d1)-1,dt(b%d2,b%d2)-1,dt(b%d1,b%d2);'%((j,)*6))
L.append('matrix S1=b11+b21+b31+b41-2*p1; matrix S2=b12+b22+b32+b42-2*p2; for(i=1;i<=3;i++){ E=E,S1[i,1],S2[i,1]; }')
L.append('matrix Y[4][5]; matrix cw[3][1]; matrix cC;')
for j in (1,2,3,4):
    L.append('cw=y1*(p1-b%d1)/2+y2*(p2-b%d2)/2; cC=H*cw; for(i=1;i<=4;i++){ Y[i,%d]=cC[i,1]; }'%(j,j,j))
L.append('for(i=1;i<=4;i++){ Y[i,5]=0; }')
L.append('proc perm4(matrix M){ poly s=0; int a1,a2,a3,a4; for(a1=1;a1<=4;a1++){for(a2=1;a2<=4;a2++){ if(a2!=a1){ for(a3=1;a3<=4;a3++){ if((a3!=a1)&&(a3!=a2)){ a4=10-a1-a2-a3; s=s+M[1,a1]*M[2,a2]*M[3,a3]*M[4,a4]; }}}}} return(s);}')
L.append('ideal CHK; for(j=1;j<=5;j++){ matrix M[4][4]; c=0; for(k=1;k<=5;k++){ if(k!=j){ c++; for(i=1;i<=4;i++){ M[i,c]=1+Y[i,k]; } } } poly F=perm4(M)-24; matrix T=coef(F,y1*y2); for(k=1;k<=ncols(T);k++){ if(deg(T[1,k])>=3){E=E,T[2,k];} else {CHK=CHK,T[2,k];} } kill F; kill T; kill M; }')
L.append('list CN; for(j=1;j<=4;j++){ CN[j]=0; }')
for j in (1,2,3,4):
    L.append('matrix d%d1=p1-b%d1; matrix d%d2=p2-b%d2; CN[%d]=ideal(d%d1[1,1],d%d1[2,1],d%d1[3,1],d%d2[1,1],d%d2[2,1],d%d2[3,1]);'%(j,j,j,j,j,j,j,j,j,j,j))
L.append('ring R2=%s,(%s),dp; option(redSB); LIB "elim.lib"; ideal E=imap(R,E); ideal CHK=imap(R,CHK); list CN=imap(R,CN);'%(P,','.join(vs)))
L.append('ideal I=std(E); printf("PPLANE p=%s: dim %%s unit %%s",dim(I),(reduce(1,I)==0)); printf("  degree-2 parts reduce to 0: %%s",size(reduce(CHK,I))==0);'%P)
L.append('for(k=1;k<=4;k++){ if(reduce(1,I)!=0){ I=std(sat(I,CN[k])); printf("  after saturation by plane column %s nonzero: dim %s unit %s",k,dim(I),(reduce(1,I)==0)); } }')
L.append('quit;')
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
