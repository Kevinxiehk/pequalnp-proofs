# Singular script: build the 12 defect generators in chart (pa,pb), a random 4x4 combination M, D = det(M); write the pair ideal + D in msolve format.
import sys, random, itertools
P=int(sys.argv[1]); pa=[int(c) for c in sys.argv[2]]; pb=[int(c) for c in sys.argv[3]]; seed=int(sys.argv[4]); out=sys.argv[5]
random.seed(seed)
def plane(piv,off):
    non=[c for c in range(5) if c not in piv]; u=[['0']*5,['0']*5]
    for r in range(2):
        u[r][piv[r]]='1'
        for k,c in enumerate(non): u[r][c]='t(%d)'%(off+r*3+k)
    return u
ua=plane(pa,1); vb=plane(pb,7)      # Singular vars t(1..12)
L=['ring R = %d, (t(1..12),x,y), dp;'%P]
for name,U in (('a',ua),('b',vb)):
    for r in range(2):
        L.append('matrix %s%d[1][5] = %s;'%(name,r,','.join(U[r])))
L.append('''proc e2(matrix v){ poly s=0; int i; int j; for(i=1;i<=5;i++){for(j=i+1;j<=5;j++){s=s+v[1,i]*v[1,j];}} return(s);}
proc e3(matrix v){ poly s=0; int i; int j; int k; for(i=1;i<=5;i++){for(j=i+1;j<=5;j++){for(k=j+1;k<=5;k++){s=s+v[1,i]*v[1,j]*v[1,k];}}} return(s);}
proc sm(matrix v){ poly s=0; int i; for(i=1;i<=5;i++){s=s+v[1,i];} return(s);}
proc d2(matrix a, matrix b){ matrix r[1][5]; int j; poly A=sm(a); poly B=sm(b); for(j=1;j<=5;j++){r[1,j]=A*b[1,j]+B*a[1,j]-2*a[1,j]*b[1,j];} return(r);}
proc d3(matrix a){ matrix r[1][5]; int j; poly A=sm(a); poly E=e2(a); for(j=1;j<=5;j++){r[1,j]=-a[1,j]*(E-A*a[1,j]+a[1,j]^2);} return(r);}
matrix wa[1][5] = x*a0+y*a1; matrix wb[1][5] = x*b0+y*b1;
list G = d2(a0,b0), d2(a0,b1), d2(a1,b0), d2(a1,b1);
matrix D3a[1][5] = d3(wa); matrix D3b[1][5] = d3(wb);
int j; int e; matrix c[1][5];
for(e=0;e<=3;e++){ for(j=1;j<=5;j++){ c[1,j] = jet(subst(diff(diff(diff(D3a[1,j],x),x),x),x,0),0); } }
''')
# cubic coefficients via coeffs in x,y: use explicit extraction
L.append('''proc cubcoef(matrix D, int ex){ matrix r[1][5]; int j; for(j=1;j<=5;j++){ matrix K = coeffs(D[1,j],x); poly cf = 0; if (nrows(K) > ex) { cf = K[ex+1,1]; } r[1,j] = subst(cf,y,1); } return(r);}
int k; for(k=0;k<=3;k++){ G = insert(G, cubcoef(D3a,k), size(G)); G = insert(G, cubcoef(D3b,k), size(G)); }''')
R=[[random.randrange(1,1000) for _ in range(12)] for _ in range(4)]
L.append('matrix M[4][4];')
for r in range(4):
    for j in range(4):
        L.append('M[%d,%d] = %s;'%(r+1,j+1,'+'.join('%d*G[%d][1,%d]'%(R[r][g],g+1,j+1) for g in range(12))))
L.append('poly Dt = det(M);')
L.append('ideal I = coeffs(e3(wa),x)[1..4,1], coeffs(e3(wb),x)[1..4,1];')   # placeholder, replaced below
open(out,'w').write('\n'.join(L)+'\n')
