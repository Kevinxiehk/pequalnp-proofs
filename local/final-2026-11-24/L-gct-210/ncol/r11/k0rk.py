# K0 without m/Q variables: S = {(a(x,y), b(x,y))}, conditions P2 == 0, P3 == 0 (coefficients in x,y) and rank <= 1 of the 5x7 matrix
# whose row k = coefficients of (d2_k, d3_k), d2_k = A b_k + B a_k - 2 a_k b_k, d3_k = a_k e2(a\k) + b_k e2(b\k) (sign immaterial).
# Then minimal primes; per component: rows vanishing identically (= zeros of m), and whether all rows vanish (e = 0).
# SUB 21: a = x u + y v, b = x p; chart v0 = 1, u0 = 0 (S5 + GL2), p_PJ = 1 (PJ in {0,1}: S4 fixing 0).
# usage: python3 -I k0rk.py SUB PJ CH OUT.sing [method: GTZ|SY]
import sys
SUB,PJ,CH,out=sys.argv[1],int(sys.argv[2]),sys.argv[3],sys.argv[4]; METH=sys.argv[5] if len(sys.argv)>5 else 'GTZ'
if SUB=='21':
    u=['0']+['u%d'%i for i in range(1,5)]; v=['1']+['v%d'%i for i in range(1,5)]; p=['p%d'%i if i!=PJ else '1' for i in range(5)]
    par=['u%d'%i for i in range(1,5)]+['v%d'%i for i in range(1,5)]+['p%d'%i for i in range(5) if i!=PJ]
    A=['x*(%s)+y*(%s)'%(u[i],v[i]) for i in range(5)]; B=['x*(%s)'%p[i] for i in range(5)]
L=['LIB "primdec.lib";',
'proc e2(list v){ poly s=0; int i; int j; for(i=1;i<=size(v);i++){for(j=i+1;j<=size(v);j++){s=s+v[i]*v[j];}} return(s);}',
'proc e3(list v){ poly s=0; int i; int j; int k; for(i=1;i<=size(v);i++){for(j=i+1;j<=size(v);j++){for(k=j+1;k<=size(v);k++){s=s+v[i]*v[j]*v[k];}}} return(s);}',
'proc dropk(list v, int k){ list w; int i; for(i=1;i<=size(v);i++){ if(i!=k){ w=insert(w,v[i],size(w)); } } return(w); }',
'proc cf(poly f, poly m){ matrix C = coef(f, x*y); int t; for(t=1;t<=ncols(C);t++){ if(C[1,t]==m){ return(C[2,t]); } } return(poly(0)); }',
'ring R = %s, (%s,x,y), dp;'%(CH,','.join(par)),
'list A = %s; list B = %s;'%(','.join(A),','.join(B)),
'poly SA = 0; poly SB = 0; poly ab = 0; int k; for(k=1;k<=5;k++){ SA = SA + A[k]; SB = SB + B[k]; ab = ab + A[k]*B[k]; }',
'poly P2 = ab - SA*SB; poly P3 = e3(A) + e3(B);',
'list m2 = x^2, x*y, y^2; list m3 = x^3, x^2*y, x*y^2, y^3; ideal I0; int t;',
'for(t=1;t<=3;t++){ I0 = I0, cf(P2, m2[t]); } for(t=1;t<=4;t++){ I0 = I0, cf(P3, m3[t]); }',
'matrix W[5][7];',
'for(k=1;k<=5;k++){ poly d2 = SA*B[k] + SB*A[k] - 2*A[k]*B[k]; poly d3 = A[k]*e2(dropk(A,k)) + B[k]*e2(dropk(B,k));',
'  for(t=1;t<=3;t++){ W[k,t] = cf(d2, m2[t]); } for(t=1;t<=4;t++){ W[k,3+t] = cf(d3, m3[t]); } kill d2; kill d3; }',
'I0 = I0 + minor(W,2);',
'ring S = %s, (%s), dp; ideal I = imap(R, I0); matrix Ws = imap(R, W);'%(CH,','.join(par)),
'int t0 = timer; list pr = %s; "NCOMP", size(pr), "SECONDS", timer - t0;'%('minAssGTZ(I)' if METH=='GTZ' else 'minAssChar(I)'),
'int q; int z; int r;',
'for(q=1;q<=size(pr);q++){ ideal P = std(pr[q]); string zs = ""; int allz = 1;',
'  for(z=1;z<=5;z++){ int cz = 1; for(r=1;r<=7;r++){ if(reduce(Ws[z,r],P)!=0){ cz = 0; allz = 0; } } if(cz==1){ zs = zs + string(z-1) + " "; } kill cz; }',
'  "COMP", q, "dim", dim(P), " zeros of m:", zs, " e=0:", allz; if(size(zs) < 4 && allz == 0){ "  CANDIDATE", P; } kill P; kill zs; kill allz; }',
'quit;']
open(out,'w').write('\n'.join(L)+'\n')
