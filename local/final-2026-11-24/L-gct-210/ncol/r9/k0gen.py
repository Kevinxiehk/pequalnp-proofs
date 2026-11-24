# K_0-FIXED system (type a3, last piece): K_0 = span((e_a - e_b, 0), (0, e_c - e_d)) in isotropic coordinates (Lemma SL_3 pair),
# Y in P(V_0'/K_0): coordinates sg0, sg3, sg4 (s = sg0 1 + sg3 e3 + sg4 e4), a_0..a_4, b_0..b_4, minus one a (index ia) and one b (index ib)
# killed by K_0; U_0 = V_012; C = V_012 + C(f1 + tp f2) [TC 0] or + C f2 [TC 2].  Conditions: K_0 (+) C Y (+) e_0 U_0 level with defect in C.
# usage: python3 -I k0gen.py P a b c d TC ZC OUT.ms     (ZC: index of the Y-coordinate set to 1, in the list printed as 'coords')
import sys
P=int(sys.argv[1]); A,Bq,Cc,Dd=[int(x) for x in sys.argv[2:6]]; TC=int(sys.argv[6]); ZC=int(sys.argv[7]); out=sys.argv[8]
g=next(x for x in range(2,100) if pow(x,(P-1)//2,P)!=1 and pow(x,(P-1)//3,P)!=1); w=pow(g,(P-1)//3,P); i3=pow(3,P-2,P)
coords=['sg0','sg3','sg4']+['a%d'%j for j in range(5) if j!=Bq]+['b%d'%j for j in range(5) if j!=Dd]   # a_b and b_d eliminated via K_0
yx={c:(c if k!=ZC else '1') for k,c in enumerate(coords)}
def ya(j): return yx.get('a%d'%j,'0')
def yb(j): return yx.get('b%d'%j,'0')
unk=[c for k,c in enumerate(coords) if k!=ZC]+(['tp'] if TC==0 else [])
L=['ring R = %d, (%s,k1,k2,yy,r1,r2), dp;'%(P,','.join(unk)),'short = 0;','poly w = %d; poly i3 = %d;'%(w,i3)]
pq=('1','tp') if TC==0 else ('0','1')
L.append('matrix tt[1][5] = %s;'%(','.join('(%s)*(%d)+(%s)*(%d)'%(pq[0],f1,pq[1],f2) for f1,f2 in zip([1,1,1,0,-3],[0,0,0,1,-1]))))
L.append('matrix one[1][5] = 1,1,1,1,1; matrix u1[1][5] = 1,-1,0,0,0; matrix u2[1][5] = 0,1,-1,0,0;')
L.append('''matrix MM[4][5]; int j; for(j=1;j<=5;j++){ MM[1,j]=one[1,j]; MM[2,j]=u1[1,j]; MM[3,j]=u2[1,j]; MM[4,j]=tt[1,j]; }
matrix wp[1][5]; int c; int cc; int rr;
for(j=1;j<=5;j++){ matrix S4[4][4]; for(rr=1;rr<=4;rr++){ cc=0; for(c=1;c<=5;c++){ if(c!=j){ cc++; S4[rr,cc]=MM[rr,c]; } } } wp[1,j]=(-1)^j*det(S4); kill S4; }''')
n1=['0','1','w','w^2']; n2=['0','1','w^2','w']; n0=['0','1','1','1']
def sval(l): return '(%s)'%yx['sg0']+('+(%s)'%yx['sg3'] if l==3 else '')+('+(%s)'%yx['sg4'] if l==4 else '')
L.append('matrix Y[4][5];')
for r in range(4):
    for l in range(5):
        t=[]
        ka=(1 if l==A else (-1 if l==Bq else 0)); kb=(1 if l==Cc else (-1 if l==Dd else 0))
        if r>0 and ka: t.append('k1*(%d)*(%s)'%(ka,n1[r]))
        if r>0 and kb: t.append('k2*(%d)*(%s)'%(kb,n2[r]))
        if r==0: t.append('yy*(-(%s))'%sval(l)); t.append('r1*u1[1,%d] + r2*u2[1,%d]'%(l+1,l+1))
        else: t.append('yy*(i3*(%s)*(%s) + (%s)*(%s) + (%s)*(%s))'%(sval(l),n0[r],ya(l),n1[r],yb(l),n2[r]))
        L.append('Y[%d,%d] = %s;'%(r+1,l+1,' + '.join(t)))
L.append('''proc perm4(matrix A){ poly s = 0; int a; int b; int c; int d;
  for(a=1;a<=4;a++){ for(b=1;b<=4;b++){ if(b!=a){ for(c=1;c<=4;c++){ if(c!=a && c!=b){ d = 10-a-b-c;
    s = s + A[1,a]*A[2,b]*A[3,c]*A[4,d]; }}}}}
  return(s); }
proc delcol(matrix A, int k){ matrix B[4][4]; int r; int c; int cc; for(r=1;r<=4;r++){ cc=0; for(c=1;c<=5;c++){ if(c!=k){ cc++; B[r,cc]=1+A[r,c]; }}} return(B); }
poly S1 = 0; poly SW = 0; int k; poly Rk;
for(k=1;k<=5;k++){ Rk = perm4(delcol(Y,k))-24; S1 = S1 + Rk; SW = SW + Rk*wp[1,k]; }
ideal E;''')
for cnd in ('S1','SW'):
    L.append('matrix C = coef(%s, k1*k2*yy*r1*r2); int ii; for(ii=1;ii<=ncols(C);ii++){ if(C[2,ii]!=0){ E = E, C[2,ii]; } } kill C; kill ii;'%cnd)
L.append('E = simplify(E, 2+4+8); "NEQ", size(E);')
L.append('link lo = ":w %s"; open(lo); write(lo, "%s"); write(lo, "%d");'%(out,','.join(unk),P))
L.append('int q; for(q=1;q<=size(E);q++){ if(q<size(E)){ write(lo, string(E[q])+","); } else { write(lo, string(E[q])); } } close(lo);')
L.append('"WROTE"; quit;')
open(out.replace('.ms','.sing'),'w').write('\n'.join(L)+'\n')
print('coords',coords)
