# TWO-ZERO split isotropic (5,1) case: m = (1, w, w^2, 0, 0) (any isotropic m with |supp| = 3 is this up to S5 and scaling, or its image
# under the column swap (1 2)), row 0 carries C m (e_0 m^T in L').  Gamma(C m) = span(1, e_3, e_4), so (F1) gives
# row 0 of Y = kappa m - (alpha 1 + delta e_3 + delta' e_4).  L' = C e_0 m^T (+) L'', L'' = ker c in Gr(4, U2), U2 (13-dim) coordinates
# (alpha, delta, delta', a_0..a_4, b_0..b_4): row 0 = -(alpha 1 + delta e_3 + delta' e_4), rows 1..3 of column j = -y0_j/3 (1,1,1) + a_j nu1 + b_j nu2.
# Conditions (identities in u_1..u_nv, kappa): R_3 == R_4 == 0 and m_l R_k - m_k R_l == 0 (k < l <= 2).
# usage: python3 -I r32z.py P S(comma-separated pivots, 4 of 0..12) OUT.ms
import sys
P=int(sys.argv[1]); S=[int(c) for c in sys.argv[2].split(',')]; out=sys.argv[3]; nv=len(S)
g=next(a for a in range(2,100) if pow(a,(P-1)//2,P)!=1 and pow(a,(P-1)//3,P)!=1); w=pow(g,(P-1)//3,P); inv3=pow(3,P-2,P)
m=[1,w,w*w%P,0,0]
free=[c for c in range(13) if c not in S]
gv=['g%d_%d'%(s,c) for s in range(nv) for c in free]
def coord(s,c):
    if c in S: return '1' if S.index(c)==s else '0'
    return 'g%d_%d'%(s,c)
us=['u%d'%(s+1) for s in range(nv)]
L=['ring R = %d, (%s,%s,kk), dp;'%(P,','.join(gv),','.join(us)),'short = 0;','poly w = %d; poly i3 = %d;'%(w,inv3),'matrix Y[4][5];']
nu1=['1','w','w^2']; nu2=['1','w^2','w']
for j in range(5):
    y0=' + '.join('u%d*(-(%s)%s)'%(s+1,coord(s,0),(' - (%s)'%coord(s,1) if j==3 else (' - (%s)'%coord(s,2) if j==4 else ''))) for s in range(nv))
    L.append('poly y0_%d = %s;'%(j,y0))
    L.append('Y[1,%d] = kk*%d + y0_%d;'%(j+1,m[j],j))
    for r in range(3):
        L.append('Y[%d,%d] = -i3*y0_%d + %s;'%(r+2,j+1,j,' + '.join('u%d*((%s)*(%s)+(%s)*(%s))'%(s+1,coord(s,3+j),nu1[r],coord(s,8+j),nu2[r]) for s in range(nv))))
L.append('''proc perm4(matrix A){ poly s = 0; int a; int b; int c; int d;
  for(a=1;a<=4;a++){ for(b=1;b<=4;b++){ if(b!=a){ for(c=1;c<=4;c++){ if(c!=a && c!=b){ d = 10-a-b-c;
    s = s + A[1,a]*A[2,b]*A[3,c]*A[4,d]; }}}}}
  return(s); }
proc delcol(matrix A, int k){ matrix B[4][4]; int r; int c; int cc; for(r=1;r<=4;r++){ cc=0; for(c=1;c<=5;c++){ if(c!=k){ cc++; B[r,cc]=1+A[r,c]; }}} return(B); }
list Rk; int k; for(k=1;k<=5;k++){ Rk = insert(Rk, perm4(delcol(Y,k))-24, size(Rk)); }
ideal E;''')
conds=['Rk[4]','Rk[5]']+['(%d)*Rk[%d]-(%d)*Rk[%d]'%(m[l],k+1,m[k],l+1) for k in range(3) for l in range(k+1,3)]
UPROD='*'.join(us)+'*kk'
for cnd in conds:
    L.append('matrix C = coef(%s, %s); int ii; for(ii=1;ii<=ncols(C);ii++){ if(C[2,ii]!=0){ E = E, C[2,ii]; } } kill C; kill ii;'%(cnd,UPROD))
L.append('E = simplify(E, 2+4+8); "NEQ", size(E);')
L.append('link lo = ":w %s"; open(lo); write(lo, "%s"); write(lo, "%d");'%(out,','.join(gv),P))
L.append('int q; for(q=1;q<=size(E);q++){ if(q<size(E)){ write(lo, string(E[q])+","); } else { write(lo, string(E[q])); } } close(lo);')
L.append('"WROTE"; quit;')
open(out.replace('.ms','.sing'),'w').write('\n'.join(L)+'\n')
