# (L6G) GENERAL-Z version of (L6): c^(0)(Z) = s ARBITRARY (5 coordinates) instead of al*1.
# (L6) PROJECTIVE system: L6 = K' (+) e_0 U_0 (+) C Z, K' = span(n1 (e_1-e_2)^T, n2 e_3^T, n2 e_4^T), t = e_1 - e_2, U_0 = C cap t^perp
# (3 charts in Gr(2, {u in V5: u_1 = u_2})), Z in P(V_Z / K'), V_Z = {Y : c(Y) in C t, c^(0)(Y) in C 1}: coordinates
# (lam, al, a0, a1, a3, a4, b0, b1, b2): row 0 = lam t - al 1, rows 1..3 column l = (al/3) n0 + a_l n1 + b_l n2  (a2 = b3 = b4 = 0 mod K').
# Chart: coordinate ZC = 1 (9 charts).  Equations: coefficients of R(Y).1 and R(Y).w' in (k1,k2,k3,r1,r2,zz).  Closed + projective.
# usage: python3 -I r211L6.py P UCHART ZC OUT.ms
import sys
P=int(sys.argv[1]); uc=int(sys.argv[2]); ZC=int(sys.argv[3]); out=sys.argv[4]
g=next(a for a in range(2,100) if pow(a,(P-1)//2,P)!=1 and pow(a,(P-1)//3,P)!=1); w=pow(g,(P-1)//3,P); i3=pow(3,P-2,P)
zn=['lam','s0','s1','s2','s3','s4','za0','za1','za3','za4','zb0','zb1','zb2']
zx={n:(n if k!=ZC else '1') for k,n in enumerate(zn)}
unk=['c1','c2']+[n for k,n in enumerate(zn) if k!=ZC]
L=['ring R = %d, (%s,k1,k2,k3,r1,r2,zz), dp;'%(P,','.join(unk)),'short = 0;','poly w = %d; poly i3 = %d;'%(w,i3)]
b=[[1,0,0,0,-1],[0,1,1,0,-2],[0,0,0,1,-1]]
oth=[i for i in range(3) if i!=uc]
def vec(i,c): return ['(%d)+(%s)*(%d)'%(b[i][j],c,b[uc][j]) for j in range(5)]
L.append('matrix u1[1][5] = %s;'%(','.join(vec(oth[0],'c1'))))
L.append('matrix u2[1][5] = %s;'%(','.join(vec(oth[1],'c2'))))
L.append('matrix tt[1][5] = 0,1,-1,0,0;'); L.append('matrix one[1][5] = 1,1,1,1,1;')
L.append('''matrix MM[4][5]; int j; for(j=1;j<=5;j++){ MM[1,j]=one[1,j]; MM[2,j]=tt[1,j]; MM[3,j]=u1[1,j]; MM[4,j]=u2[1,j]; }
matrix wp[1][5]; int c; int cc; int rr;
for(j=1;j<=5;j++){ matrix S4[4][4]; for(rr=1;rr<=4;rr++){ cc=0; for(c=1;c<=5;c++){ if(c!=j){ cc++; S4[rr,cc]=MM[rr,c]; } } } wp[1,j]=(-1)^j*det(S4); kill S4; }''')
n1=['0','1','w','w^2']; n2=['0','1','w^2','w']; n0=['0','1','1','1']
def ent(r,l):
    t=[]
    if l in (1,2) and r>0: t.append('k1*(%s)*(%d)'%(n1[r],1 if l==1 else -1))
    if l==3 and r>0: t.append('k2*(%s)'%n2[r])
    if l==4 and r>0: t.append('k3*(%s)'%n2[r])
    if r==0: t.append('r1*u1[1,%d] + r2*u2[1,%d]'%(l+1,l+1))
    if r==0: t.append('zz*((%s)*tt[1,%d]-(%s))'%(zx['lam'],l+1,zx['s%d'%l]))
    else:
        s='i3*(%s)*(%s)'%(zx['s%d'%l],n0[r])
        if l in (0,1,3,4): s+=' + (%s)*(%s)'%(zx['za%d'%l],n1[r])
        if l in (0,1,2): s+=' + (%s)*(%s)'%(zx['zb%d'%l],n2[r])
        t.append('zz*(%s)'%s)
    return ' + '.join(t)
L.append('matrix Y[4][5];')
for r in range(4):
    for l in range(5): L.append('Y[%d,%d] = %s;'%(r+1,l+1,ent(r,l)))
L.append('''proc perm4(matrix A){ poly s = 0; int a; int b; int c; int d;
  for(a=1;a<=4;a++){ for(b=1;b<=4;b++){ if(b!=a){ for(c=1;c<=4;c++){ if(c!=a && c!=b){ d = 10-a-b-c;
    s = s + A[1,a]*A[2,b]*A[3,c]*A[4,d]; }}}}}
  return(s); }
proc delcol(matrix A, int k){ matrix B[4][4]; int r; int c; int cc; for(r=1;r<=4;r++){ cc=0; for(c=1;c<=5;c++){ if(c!=k){ cc++; B[r,cc]=1+A[r,c]; }}} return(B); }
poly S1 = 0; poly SW = 0; int k; poly Rk;
for(k=1;k<=5;k++){ Rk = perm4(delcol(Y,k))-24; S1 = S1 + Rk; SW = SW + Rk*wp[1,k]; }
ideal E;''')
for cnd in ('S1','SW'):
    L.append('matrix C = coef(%s, k1*k2*k3*r1*r2*zz); int ii; for(ii=1;ii<=ncols(C);ii++){ if(C[2,ii]!=0){ E = E, C[2,ii]; } } kill C; kill ii;'%cnd)
L.append('E = simplify(E, 2+4+8); "NEQ", size(E);')
L.append('link lo = ":w %s"; open(lo); write(lo, "%s"); write(lo, "%d");'%(out,','.join(unk),P))
L.append('int q; for(q=1;q<=size(E);q++){ if(q<size(E)){ write(lo, string(E[q])+","); } else { write(lo, string(E[q])); } } close(lo);')
L.append('"WROTE"; quit;')
open(out.replace('.ms','.sing'),'w').write('\n'.join(L)+'\n')
