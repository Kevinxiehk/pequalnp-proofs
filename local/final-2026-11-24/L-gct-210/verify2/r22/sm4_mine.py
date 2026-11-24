# verify2 r22: INDEPENDENT generator for rows' (SM4) in the conic form (R18.1 IS0/IS4): Y 4x5 column-centred, column 5 zero, columns 1..4 nonzero,
# row sum f = c(s) isotropic (fixed scale), y_k = (f - g_k)/2 with g_k = l_k c(t_k) isotropic (degree 2 built in), sum_{k<=4} g_k = 2 f (5-column layout,
# g_5 = f). Strongly level: sigma_3 and sigma_4 (= permanent) of every 4x4 deletion vanish (sigma_1, sigma_2 automatic). Saturation: each column != 0.
# usage: python3 -I sm4_mine.py P OUT   (P = 0: over Q(i) with ii^2+1; else prime with i a constant)
import sys
P=int(sys.argv[1]); out=sys.argv[2]
iv={2147483629:'629208553'}.get(P)
hdr='ring R=%d,(s,l1,l2,l3,l4,t1,t2,t3,t4%s),dp; option(redSB); LIB "elim.lib";'%(P,',ii' if P==0 else '')
L=[hdr]
L.append('poly I_=%s;'%('ii' if P==0 else iv))
L.append('matrix H[4][3]=1,1,1,1,-1,-1,-1,1,-1,-1,-1,1;')
L.append('proc cc(poly x){ matrix v[3][1]=x^2-1,I_*(x^2+1),2*x; return(v); }')
L.append('matrix f=cc(s);')
for k in range(1,5): L.append('matrix g%d=l%d*cc(t%d); matrix y%d=H*((f-g%d)/2);'%(k,k,k,k,k))
L.append('matrix S=g1+g2+g3+g4-2*f; ideal E=S[1,1],S[2,1],S[3,1];'+(' E=E,ii^2+1;' if P==0 else ''))
L.append('matrix Y[4][5]; int r; int k; int j; for(r=1;r<=4;r++){ Y[r,1]=y1[r,1]; Y[r,2]=y2[r,1]; Y[r,3]=y3[r,1]; Y[r,4]=y4[r,1]; Y[r,5]=0; }')
L.append('proc perm4(matrix M){ poly q=0; int a1,a2,a3,a4; for(a1=1;a1<=4;a1++){for(a2=1;a2<=4;a2++){ if(a2!=a1){ for(a3=1;a3<=4;a3++){ if((a3!=a1)&&(a3!=a2)){ a4=10-a1-a2-a3; q=q+M[1,a1]*M[2,a2]*M[3,a3]*M[4,a4]; } } } } } return(q); }')
L.append('proc sig3(matrix M){ poly q=0; int r1,r2,r3,c1,c2,c3; for(r1=1;r1<=4;r1++){for(r2=r1+1;r2<=4;r2++){for(r3=r2+1;r3<=4;r3++){ for(c1=1;c1<=4;c1++){for(c2=1;c2<=4;c2++){ if(c2!=c1){ for(c3=1;c3<=4;c3++){ if((c3!=c1)&&(c3!=c2)){ q=q+M[r1,c1]*M[r2,c2]*M[r3,c3]; } } } } } } } } return(q); }')
L.append('for(j=1;j<=5;j++){ matrix M[4][4]; int c=0; for(k=1;k<=5;k++){ if(k!=j){ c++; for(r=1;r<=4;r++){ M[r,c]=Y[r,k]; } } } E=E,sig3(M),perm4(M); kill M; kill c; }')
L.append('int t0=timer; ideal G=std(E); printf("SM4 (own) p=%d: before saturation dim %%s unit %%s",dim(G),reduce(1,G)==0);'%P)
for k in range(1,5):
    L.append('if(reduce(1,G)!=0){ G=std(sat(G,ideal(y%d[1,1],y%d[2,1],y%d[3,1],y%d[4,1]))); printf("  after column %d nonzero: dim %%s unit %%s",dim(G),reduce(1,G)==0); }'%(k,k,k,k,k))
L.append('printf("  time %s s",timer-t0); quit;')
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
