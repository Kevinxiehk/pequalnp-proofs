# (1,1) restricted classification, closed form (no m/Q/z): S = span((u,0),(0,p)), u_I = 1, p_J = 1; e3(u) = e3(p) = 0, sum u p = U P,
# rank <= 1 of the 5x3 matrix W (rows k: D_k, F_k, G_k) and the shape as equal rows (b22: row0 = row1, row2 = row3; a3: rows 0,1,2 equal).
# Minimal primes over Q; per component: rows vanishing identically (zeros of m), e = 0?, dim.  Zero-free members = components with no
# identically-zero row (their points are zero-free off a proper closed subset; a 0-dim component is a point / Galois orbit).
# usage: python3 -I k0_11s.py SH I J CH OUT.sing
import sys
SH,I,J,CH,out=sys.argv[1],int(sys.argv[2]),int(sys.argv[3]),sys.argv[4],sys.argv[5]
u=['1' if k==I else 'u%d'%k for k in range(5)]; p=['1' if k==J else 'p%d'%k for k in range(5)]
par=[x for x in u+p if x!='1']
eqrows=[(0,1),(2,3)] if SH=='b22' else [(0,1),(1,2)]
L=['LIB "primdec.lib";',
'proc e2(list v){ poly s=0; int i; int j; for(i=1;i<=size(v);i++){for(j=i+1;j<=size(v);j++){s=s+v[i]*v[j];}} return(s);}',
'proc e3(list v){ poly s=0; int i; int j; int k; for(i=1;i<=size(v);i++){for(j=i+1;j<=size(v);j++){for(k=j+1;k<=size(v);k++){s=s+v[i]*v[j]*v[k];}}} return(s);}',
'proc dropk(list v, int k){ list w; int i; for(i=1;i<=size(v);i++){ if(i!=k){ w=insert(w,v[i],size(w)); } } return(w); }',
'ring R = %s, (%s), dp;'%(CH,','.join(par)),
'list A = %s; list B = %s;'%(','.join(u),','.join(p)),
'poly SA = 0; poly SB = 0; poly ab = 0; int k; for(k=1;k<=5;k++){ SA = SA + A[k]; SB = SB + B[k]; ab = ab + A[k]*B[k]; }',
'matrix W[5][3]; for(k=1;k<=5;k++){ W[k,1] = SA*B[k]+SB*A[k]-2*A[k]*B[k]; W[k,2] = A[k]*e2(dropk(A,k)); W[k,3] = B[k]*e2(dropk(B,k)); }',
'ideal I0 = e3(A), e3(B), ab - SA*SB, minor(W,2); int t;']
for r1,r2 in eqrows: L.append('for(t=1;t<=3;t++){ I0 = I0, W[%d,t] - W[%d,t]; }'%(r1+1,r2+1))
L+=['int t0 = timer; list pr = minAssGTZ(I0); "NCOMP", size(pr), "SECONDS", timer - t0;',
'int q; int z; int r;',
'for(q=1;q<=size(pr);q++){ ideal P = std(pr[q]); string zs = ""; int allz = 1;',
'  for(z=1;z<=5;z++){ int cz = 1; for(r=1;r<=3;r++){ if(reduce(W[z,r],P)!=0){ cz = 0; allz = 0; } } if(cz==1){ zs = zs + string(z-1) + " "; } kill cz; }',
'  "COMP", q, "dim", dim(P), "vdim", vdim(P), " zero rows:", zs, " e=0:", allz; if(size(zs)==0){ "  ZEROFREE", P; } kill P; kill zs; kill allz; }',
'quit;']
open(out,'w').write('\n'.join(L)+'\n')
