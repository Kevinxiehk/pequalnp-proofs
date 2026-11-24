# R2.11 CONDITIONAL system (assumes the K' classification R7.2): L' = K' (+) e_0 U_0 (+) C Y_g (+) C Z inside 4x5, rows 0..3.
# K' = span(n1 (e_1 - e_2)^T, n2 e_3^T, n2 e_4^T), n1 = (0,1,w,w^2), n2 = (0,1,w^2,w), n0 = (0,1,1,1); t = e_1 - e_2.
# U_0 = C cap t^perp (2-dim, inside {u in V5 : u_1 = u_2} = span(b1, b2, b3)), C = U_0 + C t, w' = generator of C^perp cap 1^perp.
# Y_g: c(Y_g) = 0, row 0 = -(al0 1 + d), rows 1..3 column l = ((al0 + d_l)/3) n0 + a_l n1 + b_l n2 (normalised mod K': a2 = b3 = b4 = 0).
# Z: c(Z) = t, row 0 = t - alZ 1, rows 1..3 column l = (alZ/3) n0 + A_l n1 + B_l n2 (A2 = B3 = B4 = 0).  d in V5, chart d_D = 1.
# Equations: coefficients of R(Y).1 and R(Y).w' in (k1,k2,k3,r1,r2,gg,zz).  AFFINE in al0, alZ, a, b, A, B: char-p evidence only.
# usage: python3 -I r211gen.py P UCHART(0|1|2) D OUT.ms
import sys
P=int(sys.argv[1]); uc=int(sys.argv[2]); D=int(sys.argv[3]); out=sys.argv[4]; mode=sys.argv[5] if len(sys.argv)>5 else 'full'   # full | noZ | noYZ
g=next(a for a in range(2,100) if pow(a,(P-1)//2,P)!=1 and pow(a,(P-1)//3,P)!=1); w=pow(g,(P-1)//3,P); i3=pow(3,P-2,P)
dv=['d%d'%j for j in range(5) if j!=D]
ya=['ya%d'%l for l in (0,1,3,4)]; yb=['yb%d'%l for l in (0,1,2)]
za=['za%d'%l for l in (0,1,3,4)]; zb=['zb%d'%l for l in (0,1,2)]
unk=['c1','c2']+(dv[:3]+['al0']+ya+yb if mode not in ('noYZ','noY') else [])+(['alZ']+za+zb if mode in ('full','noY') else [])
L=['ring R = %d, (%s,k1,k2,k3,r1,r2,gg,zz), dp;'%(P,','.join(unk+(['d1','d2','d3','d4','d0','al0']+ya+yb if mode in ('noYZ','noY') else [])+(['alZ']+za+zb if mode in ('noZ','noYZ') else []))),'short = 0;','poly w = %d; poly i3 = %d;'%(w,i3)]
# d vector: chart d_D = 1, sum zero
free=[j for j in range(5) if j!=D]
dexpr={D:'1'}
for k,j in enumerate(free[:3]): dexpr[j]='d%d'%j
last=free[3]; dexpr[last]='(-1-%s)'%('-'.join(dexpr[j] for j in free[:3]))
L.append('matrix dd[1][5] = %s;'%(','.join(dexpr[j] for j in range(5))))
# U_0 basis: b1 = e0-e4, b2 = e1+e2-2e4, b3 = e3-e4; chart uc: the two basis vectors are b_i + c b_k (k = uc)
b=[[1,0,0,0,-1],[0,1,1,0,-2],[0,0,0,1,-1]]
oth=[i for i in range(3) if i!=uc]
def vec(i,c): return ['(%d)+(%s)*(%d)'%(b[i][j],c,b[uc][j]) for j in range(5)]
L.append('matrix u1[1][5] = %s;'%(','.join(vec(oth[0],'c1'))))
L.append('matrix u2[1][5] = %s;'%(','.join(vec(oth[1],'c2'))))
L.append('matrix tt[1][5] = 0,1,-1,0,0;')
L.append('matrix one[1][5] = 1,1,1,1,1;')
# w' = generalized cross product of rows one, tt, u1, u2
L.append('''matrix MM[4][5]; int j; for(j=1;j<=5;j++){ MM[1,j]=one[1,j]; MM[2,j]=tt[1,j]; MM[3,j]=u1[1,j]; MM[4,j]=u2[1,j]; }
matrix wp[1][5]; intvec cols; int c; int cc;
for(j=1;j<=5;j++){ matrix S4[4][4]; for(int r=1;r<=4;r++){ cc=0; for(c=1;c<=5;c++){ if(c!=j){ cc++; S4[r,cc]=MM[r,c]; } } } wp[1,j]=(-1)^j*det(S4); kill S4; }''')
n1=['0','1','w','w^2']; n2=['0','1','w^2','w']; n0=['0','1','1','1']
def ent(r,l):
    t=[]
    # K'
    if l in (1,2) and r>0: t.append('k1*(%s)*(%d)'%(n1[r],1 if l==1 else -1))
    if l==3 and r>0: t.append('k2*(%s)'%n2[r])
    if l==4 and r>0: t.append('k3*(%s)'%n2[r])
    # e_0 U_0
    if r==0: t.append('r1*u1[1,%d] + r2*u2[1,%d]'%(l+1,l+1))
    # Y_g
    if r==0: t.append('gg*(-al0-dd[1,%d])'%(l+1))
    else:
        s='i3*(al0+dd[1,%d])*(%s)'%(l+1,n0[r])
        if l in (0,1,3,4): s+=' + ya%d*(%s)'%(l,n1[r])
        if l in (0,1,2): s+=' + yb%d*(%s)'%(l,n2[r])
        t.append('gg*(%s)'%s)
    # Z
    if r==0: t.append('zz*(tt[1,%d]-alZ)'%(l+1))
    else:
        s='i3*alZ*(%s)'%n0[r]
        if l in (0,1,3,4): s+=' + za%d*(%s)'%(l,n1[r])
        if l in (0,1,2): s+=' + zb%d*(%s)'%(l,n2[r])
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
if mode in ('noZ','noYZ'): L.append('S1 = subst(S1, zz, 0); SW = subst(SW, zz, 0);')
if mode in ('noYZ','noY'): L.append('S1 = subst(S1, gg, 0); SW = subst(SW, gg, 0);')
for cnd in ('S1','SW'):
    L.append('matrix C = coef(%s, k1*k2*k3*r1*r2*gg*zz); int ii; for(ii=1;ii<=ncols(C);ii++){ if(C[2,ii]!=0){ E = E, C[2,ii]; } } kill C; kill ii;'%cnd)
L.append('E = simplify(E, 2+4+8); "NEQ", size(E);')
L.append('link lo = ":w %s"; open(lo); write(lo, "%s"); write(lo, "%d");'%(out,','.join(unk),P))
L.append('int q; for(q=1;q<=size(E);q++){ if(q<size(E)){ write(lo, string(E[q])+","); } else { write(lo, string(E[q])); } } close(lo);')
L.append('"WROTE"; quit;')
open(out.replace('.ms','.sing'),'w').write('\n'.join(L)+'\n')
