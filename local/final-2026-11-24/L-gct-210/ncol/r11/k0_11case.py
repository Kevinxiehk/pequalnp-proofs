# (1,1) restricted classification by the hand case split of R11.14 (exact over Q):
#  CASE B (G == 0, F != 0, D != 0): b = e_i + beta e_j, a with a_0 = 1 (all a_k != 0 since F is zero-free), rank(D,F) <= 1,
#         shape (equal rows), Rabinowitsch 1 - z prod_k D_k.
#  CASE C (F, G != 0, so all a_k, b_k != 0): a_0 = b_0 = 1, rank(D,F,G) <= 1, shape, Rabinowitsch 1 - z prod_k F_k * G_0.
# usage: python3 -I k0_11case.py SH CASE(B|C) [i j] CH OUT.sing
import sys
SH=sys.argv[1]; CASE=sys.argv[2]
if CASE=='B': i,j=int(sys.argv[3]),int(sys.argv[4]); CH,out=sys.argv[5],sys.argv[6]
else: CH,out=sys.argv[3],sys.argv[4]
a=['1']+['a%d'%k for k in range(1,5)]
if CASE=='B': b=['1' if k==i else ('be' if k==j else '0') for k in range(5)]; par=a[1:]+['be','z']
else: b=['1']+['b%d'%k for k in range(1,5)]; par=a[1:]+b[1:]+['z']
eqrows=[(0,1),(2,3)] if SH=='b22' else [(0,1),(1,2)]
L=['LIB "primdec.lib";',
'proc e2(list v){ poly s=0; int i; int j; for(i=1;i<=size(v);i++){for(j=i+1;j<=size(v);j++){s=s+v[i]*v[j];}} return(s);}',
'proc e3(list v){ poly s=0; int i; int j; int k; for(i=1;i<=size(v);i++){for(j=i+1;j<=size(v);j++){for(k=j+1;k<=size(v);k++){s=s+v[i]*v[j]*v[k];}}} return(s);}',
'proc dropk(list v, int k){ list w; int i; for(i=1;i<=size(v);i++){ if(i!=k){ w=insert(w,v[i],size(w)); } } return(w); }',
'ring R = %s, (%s), dp; option(redSB);'%(CH,','.join(par)),
'list A = %s; list B = %s;'%(','.join(a),','.join(b)),
'poly SA = 0; poly SB = 0; poly ab = 0; int k; for(k=1;k<=5;k++){ SA = SA + A[k]; SB = SB + B[k]; ab = ab + A[k]*B[k]; }',
'matrix W[5][3]; for(k=1;k<=5;k++){ W[k,1] = SA*B[k]+SB*A[k]-2*A[k]*B[k]; W[k,2] = A[k]*e2(dropk(A,k)); W[k,3] = B[k]*e2(dropk(B,k)); }',
'ideal I0 = e3(A), e3(B), ab - SA*SB, minor(W,2); int t;']
for r1,r2 in eqrows: L.append('for(t=1;t<=3;t++){ I0 = I0, W[%d,t] - W[%d,t]; }'%(r1+1,r2+1))
if CASE=='B': L.append('I0 = I0, 1 - z*W[1,1]*W[2,1]*W[3,1]*W[4,1]*W[5,1];')
else: L.append('I0 = I0, 1 - z*W[1,2]*W[2,2]*W[3,2]*W[4,2]*W[5,2]*W[1,3];')
L+=['int t0 = timer; ideal G = std(I0); "STD", "unit", ((size(G)==1) && (deg(G[1])==0)), "dim", dim(G), "vdim", vdim(G), "SECONDS", timer - t0;',
'if(!((size(G)==1) && (deg(G[1])==0))){ list pr = minAssGTZ(G); "NCOMP", size(pr); int q;',
'  for(q=1;q<=size(pr);q++){ ideal P = std(pr[q]); "COMP", q, "dim", dim(P), "vdim", vdim(P); P; kill P; } }',
'quit;']
open(out,'w').write('\n'.join(L)+'\n')
