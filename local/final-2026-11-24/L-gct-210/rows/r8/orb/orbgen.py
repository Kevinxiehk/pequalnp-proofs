# (PL) K version, four active columns, sign patterns ++++ / ----: the degree-2 data are ONE O(3,C)-orbit of the tetrahedral
# configuration B_j^0 (axes = rows H_j of the Walsh matrix).  Unknown R in O(3,C); condition: t(R A_a^0 tau, R A_b^0 tau, R A_c^0 tau) == 0
# for all four triples (t = polarised x1 x2 x3, Walsh coordinates; A^0 = (1 - B^0)/2).  usage: python3 orbgen.py PAT OUT [P] [quartic]
import sys
pat=sys.argv[1]; out=sys.argv[2]; P=sys.argv[3] if len(sys.argv)>3 else '0'; Q4=len(sys.argv)>4
H=[[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]]
L=['ring R=%s,(r,x11,x12,x13,x21,x22,x23,x31,x32,x33,s1,s2,s3),dp; option(redSB);'%P]
L.append('matrix X[3][3]=x11,x12,x13,x21,x22,x23,x31,x32,x33; matrix Id[3][3]=1,0,0,0,1,0,0,0,1; matrix T[3][1]=s1,s2,s3;')
L.append('list A; matrix h[3][1]; matrix cx[3][3]; matrix B[3][3];')
for j in range(4):
    a,b,c=H[j]
    L.append('h=%d,%d,%d; cx=0,%d,%d,%d,0,%d,%d,%d,0;'%(a,b,c,-c,b,c,-a,-b,a))
    if pat=='++++':   # B = (1/4) I + (1/4) h h^T + (r/4) [h]_x , r^2 = 5
        L.append('B=Id/4+h*transpose(h)/4+r*cx/4;')
    else:             # ----: B = (5/4) I - (3/4) h h^T - (r/4) [h]_x , r^2 = -3   (r = i sqrt 3)
        L.append('B=5*Id/4-3*h*transpose(h)/4-r*cx/4;')
    L.append('A[%d]=(Id-B)/2;'%(j+1))
L.append('ideal E=r^2-(%s);'%('5' if pat=='++++' else '-3'))
L.append('matrix O=transpose(X)*X-Id; int i; int k; for(i=1;i<=3;i++){for(k=i;k<=3;k++){E=E,O[i,k];}}')
L.append('proc t3(matrix x, matrix y, matrix z){ return(x[1,1]*y[2,1]*z[3,1]+x[1,1]*y[3,1]*z[2,1]+x[2,1]*y[1,1]*z[3,1]+x[2,1]*y[3,1]*z[1,1]+x[3,1]*y[1,1]*z[2,1]+x[3,1]*y[2,1]*z[1,1]); }')
L.append('list V; for(i=1;i<=4;i++){ matrix Mi=A[i]; V[i]=X*(Mi*T); kill Mi; }')
L.append('int a; int b; int c;')
L.append('for(a=1;a<=4;a++){for(b=a+1;b<=4;b++){for(c=b+1;c<=4;c++){ poly F=t3(V[a],V[b],V[c]); matrix C=coef(F,s1*s2*s3); for(k=1;k<=ncols(C);k++){E=E,C[2,k];} kill F; kill C; }}}')
if Q4:  # the 4x4 permanent of the active block (columns = H * v_j) must vanish identically
    L.append('matrix Hm[4][3]=1,1,1,1,-1,-1,-1,1,-1,-1,-1,1; matrix q[4][4]; for(i=1;i<=4;i++){ matrix vv=Hm*V[i]; for(k=1;k<=4;k++){q[k,i]=vv[k,1];} kill vv; }')
    L.append('poly pq=0; int p1; int p2; int p3; int p4; for(p1=1;p1<=4;p1++){for(p2=1;p2<=4;p2++){if(p2!=p1){for(p3=1;p3<=4;p3++){if((p3!=p1)&&(p3!=p2)){p4=10-p1-p2-p3; pq=pq+q[1,p1]*q[2,p2]*q[3,p3]*q[4,p4];}}}}}')
    L.append('matrix C4=coef(pq,s1*s2*s3); for(k=1;k<=ncols(C4);k++){E=E,C4[2,k];}')
L.append('matrix SS=-2*Id; for(i=1;i<=4;i++){ matrix Mi=A[i]; SS=SS+Id-2*Mi; kill Mi; } poly chk=0; for(i=1;i<=3;i++){for(k=1;k<=3;k++){chk=chk+SS[i,k]^2;}}')
L.append('ring R2=%s,(r,x11,x12,x13,x21,x22,x23,x31,x32,x33),dp; option(redSB); ideal E=imap(R,E); poly chk=imap(R,chk); ideal Z=std(ideal(E[1])); printf("check sum B = 2I exactly: %%s",reduce(chk,Z)==0); ideal G=std(E);'%P)
L.append('printf("ORB %s p=%s %s: dim %%s unit %%s size %%s",dim(G),(reduce(1,G)==0),size(G));'%(pat,P,'with quartic' if Q4 else 'deg<=3'))
L.append('if(size(G)<20){print(G);} quit;')
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
