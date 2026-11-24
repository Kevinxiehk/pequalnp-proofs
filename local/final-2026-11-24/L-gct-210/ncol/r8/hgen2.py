# H-CONJECTURE system (last piece of case (C), type a3): K = ker c (4-dim) inside V_0' = {row 0 = -s, s in U_0^perp, c(Y) = 0},
# U_0 = V_012, U_0^perp = span(1, e_3, e_4) (coordinates sg0, sg3, sg4 = 0,1,2), a_0..a_4 = 3..7, b_0..b_4 = 8..12;
# C = V_012 (+) C t'', t'' = p f1 + q f2, f1 = (1,1,1,0,-3), f2 = (0,0,0,1,-1), chart TC (p = 1 or q = 1).
# Conditions: K (+) e_0 U_0 level with defect in C: coefficients of R(Y).1 and R(Y).w' in (k1..k4, r1, r2), w' = cross product of 1, e0-e1,
# e1-e2, t''.  usage: python3 -I hgen.py P S(4 pivots, comma) TC OUT.ms
import sys
TY=sys.argv[1]; P=int(sys.argv[2]); S=[int(c) for c in sys.argv[3].split(',')]; TC=int(sys.argv[4]); out=sys.argv[5]; nv=len(S)
g=next(a for a in range(2,100) if pow(a,(P-1)//2,P)!=1 and pow(a,(P-1)//3,P)!=1); w=pow(g,(P-1)//3,P); i3=pow(3,P-2,P)
free=[c for c in range(13) if c not in S]
gv=['g%d_%d'%(s,c) for s in range(nv) for c in free]; unk=gv+(['tp'] if TC in (0,1) else [])
def coord(s,c):
    if c in S: return '1' if S.index(c)==s else '0'
    return 'g%d_%d'%(s,c)
ks=['k%d'%(s+1) for s in range(nv)]
L=['ring R = %d, (%s,%s,r1,r2), dp;'%(P,','.join(unk),','.join(ks)),'short = 0;','poly w = %d; poly i3 = %d;'%(w,i3)]
pq=('1','tp') if TC==0 else (('tp','1') if TC==1 else ('0','1'))
if TY=='a3':
    F1,F2=[1,1,1,0,-3],[0,0,0,1,-1]; U1,U2='1,-1,0,0,0','0,1,-1,0,0'
    Dv=[['1']*5,['0','0','0','1','0'],['0','0','0','0','1']]
elif TY=='b22':
    F1,F2=[1,1,0,0,-2],[0,0,1,1,-2]; U1,U2='1,-1,0,0,0','0,0,1,-1,0'
    Dv=[['1']*5,['1','1','0','0','0'],['0','0','0','0','1']]
else:   # b23: C fixed; t'' = any complement of U_0 in C: take e2+e3-2e4-type vector orthogonal-free: t'' = (0,0,1,1,-2) (in V_234, not in U_0 generically)
    F1,F2=None,None; U1='1,-1,0,0,0'
    U2=('0,0,1,tp,-1-tp' if TC==0 else '0,0,0,1,-1')
    Dv=[['1']*5,['1','1','0','0','0'],(['0','0','-tp','1','0'] if TC==0 else ['0','0','1','0','0'])]
if TY in ('a3','b22'):
    L.append('matrix tt[1][5] = %s;'%(','.join('(%s)*(%d)+(%s)*(%d)'%(pq[0],f1,pq[1],f2) for f1,f2 in zip(F1,F2))))
else:
    L.append('matrix tt[1][5] = %s;'%('(0),(0),(1),(1),(-2)' if TC==0 else '(0),(0),(2),(-1),(-1)'))
L.append('matrix one[1][5] = 1,1,1,1,1; matrix u1[1][5] = %s; matrix u2[1][5] = %s;'%(U1,U2))
L.append('''matrix MM[4][5]; int j; for(j=1;j<=5;j++){ MM[1,j]=one[1,j]; MM[2,j]=u1[1,j]; MM[3,j]=u2[1,j]; MM[4,j]=tt[1,j]; }
matrix wp[1][5]; int c; int cc; int rr;
for(j=1;j<=5;j++){ matrix S4[4][4]; for(rr=1;rr<=4;rr++){ cc=0; for(c=1;c<=5;c++){ if(c!=j){ cc++; S4[rr,cc]=MM[rr,c]; } } } wp[1,j]=(-1)^j*det(S4); kill S4; }''')
if TY=='b23': L.append('wp[1,1]=3; wp[1,2]=3; wp[1,3]=-2; wp[1,4]=-2; wp[1,5]=-2;')   # C = V_01 + V_234 fixed
n1=['0','1','w','w^2']; n2=['0','1','w^2','w']; n0=['0','1','1','1']
def sval(s,l):   # s_l = sum_k coord(s,k) * Dv[k][l]
    return '+'.join('(%s)*(%s)'%(coord(s,k),Dv[k][l]) for k in range(3))
L.append('matrix Y[4][5];')
for r in range(4):
    for l in range(5):
        terms=[]
        for s in range(nv):
            if r==0: terms.append('k%d*(-(%s))'%(s+1,sval(s,l)))
            else: terms.append('k%d*(i3*(%s)*(%s) + (%s)*(%s) + (%s)*(%s))'%(s+1,sval(s,l),n0[r],coord(s,3+l),n1[r],coord(s,8+l),n2[r]))
        if r==0: terms.append('r1*u1[1,%d] + r2*u2[1,%d]'%(l+1,l+1))
        L.append('Y[%d,%d] = %s;'%(r+1,l+1,' + '.join(terms)))
L.append('''proc perm4(matrix A){ poly s = 0; int a; int b; int c; int d;
  for(a=1;a<=4;a++){ for(b=1;b<=4;b++){ if(b!=a){ for(c=1;c<=4;c++){ if(c!=a && c!=b){ d = 10-a-b-c;
    s = s + A[1,a]*A[2,b]*A[3,c]*A[4,d]; }}}}}
  return(s); }
proc delcol(matrix A, int k){ matrix B[4][4]; int r; int c; int cc; for(r=1;r<=4;r++){ cc=0; for(c=1;c<=5;c++){ if(c!=k){ cc++; B[r,cc]=1+A[r,c]; }}} return(B); }
poly S1 = 0; poly SW = 0; int k; poly Rk;
for(k=1;k<=5;k++){ Rk = perm4(delcol(Y,k))-24; S1 = S1 + Rk; SW = SW + Rk*wp[1,k]; }
ideal E;''')
UP='*'.join(ks)+'*r1*r2'
for cnd in ('S1','SW'):
    L.append('matrix C = coef(%s, %s); int ii; for(ii=1;ii<=ncols(C);ii++){ if(C[2,ii]!=0){ E = E, C[2,ii]; } } kill C; kill ii;'%(cnd,UP))
L.append('E = simplify(E, 2+4+8); "NEQ", size(E);')
L.append('link lo = ":w %s"; open(lo); write(lo, "%s"); write(lo, "%d");'%(out,','.join(unk),P))
L.append('int q; for(q=1;q<=size(E);q++){ if(q<size(E)){ write(lo, string(E[q])+","); } else { write(lo, string(E[q])); } } close(lo);')
L.append('"WROTE"; quit;')
open(out.replace('.ms','.sing'),'w').write('\n'.join(L)+'\n')
