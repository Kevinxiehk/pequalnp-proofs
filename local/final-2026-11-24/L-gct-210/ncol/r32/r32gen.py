# R3.2 closure system (round 6).  L' = C e_0 m'^T (+) L'',  L'' = ker c in Gr(4, U),  U = (V3)^4 (+) V4 (rows 1..3 column-centred on
# columns 0..3; column 4 in V4 = sum-zero C^4, rows 0..3).  CC34 => L'' contains a single-column element (0|y'), y' in V4.
# Chart: y' = f1 + y2 f2 + y3 f3 (f_r = e_r - e_0; S3 on rows 1..3 brings any y' to y_1 != 0), L'' = C(0|y') (+) span(v1,v2,v3),
# v_s in the 10-dim space (a_0..a_3, b_0..b_3, w2, w3) = (V3)^4 (+) span(f2,f3), Pluecker chart S (3 pivots) of Gr(3,10).
# Columns j<=3, rows 1..3: a_j nu1 + b_j nu2, nu1 = (1,w,w^2), nu2 = (1,w^2,w).  Column 4: w2 f2 + w3 f3.  m' = (M0..M3), sum M = 0,
# sum M^2 = 0, chart M_J = 1.  Conditions, as identities in (u0..u3, kk): R_4(Y) == 0 and M_l R_k(Y) - M_k R_l(Y) == 0 (k<l<=3), where
# Y = u0 (0|y') + sum u_s v_s + kk e_0 m'^T and R_k(Y) = perm_4((J+Y) minus column k) - 24.
# usage: python3 -I r32gen.py P S(e.g. 016) J OUT.ms [r4only]   -> writes OUT.sing (Singular) which writes OUT.ms (msolve)
import sys, itertools
P=int(sys.argv[1]); S=[int(c) for c in sys.argv[2].split(',')] if ',' in sys.argv[2] else [int(c) for c in sys.argv[2]]
J=int(sys.argv[3]); out=sys.argv[4]; r4only='r4only' in sys.argv[5:]
nv=len(S)   # number of v vectors = number of pivots (3 for the real system; 2, 1 for calibration)
g=next(a for a in range(2,100) if pow(a,(P-1)//2,P)!=1 and pow(a,(P-1)//3,P)!=1); w=pow(g,(P-1)//3,P)
free=[c for c in range(10) if c not in S]
gv=['g%d_%d'%(s,c) for s in range(nv) for c in free]
Mv=['M%d'%j for j in range(4) if j!=J]
unk=gv+['y2','y3']+Mv
def coord(s,c):
    if c in S: return '1' if S.index(c)==s else '0'
    return 'g%d_%d'%(s,c)
L=['ring R = %d, (%s,u0,%s,kk), dp;'%(P,','.join(unk),','.join('u%d'%(s+1) for s in range(nv))),'short = 0;','poly w = %d;'%w]
L.append('poly M%d = 1;'%J) if False else None
L=[l for l in L if l]
# m' as polys
Mexpr={j:('M%d'%j if j!=J else '1') for j in range(4)}
L.append('matrix Y[4][5];')
nu1=['1','w','w^2']; nu2=['1','w^2','w']
for j in range(4):
    L.append('Y[1,%d] = kk*(%s);'%(j+1,Mexpr[j]))
    for r in range(3):
        terms=['u%d*(%s)*((%s)*(%s)+(%s)*(%s))'%(s+1,'1',coord(s,j),nu1[r],coord(s,4+j),nu2[r]) for s in range(nv)]
        L.append('Y[%d,%d] = %s;'%(r+2,j+1,' + '.join(terms)))
# column 4: rows 0..3 entries z_0..z_3; y' = f1 + y2 f2 + y3 f3 ; v_s column 4 = w2 f2 + w3 f3 (coords 8, 9)
z={0:'-u0*(1+y2+y3)',1:'u0',2:'u0*y2',3:'u0*y3'}
for s in range(nv):
    W2=coord(s,8); W3=coord(s,9)
    z[0]+=' - u%d*((%s)+(%s))'%(s+1,W2,W3); z[2]+=' + u%d*(%s)'%(s+1,W2); z[3]+=' + u%d*(%s)'%(s+1,W3)
for r in range(4): L.append('Y[%d,5] = %s;'%(r+1,z[r]))
L.append('''proc perm4(matrix A){ poly s = 0; int a; int b; int c; int d;
  for(a=1;a<=4;a++){ for(b=1;b<=4;b++){ if(b!=a){ for(c=1;c<=4;c++){ if(c!=a && c!=b){ d = 10-a-b-c;
    s = s + A[1,a]*A[2,b]*A[3,c]*A[4,d]; }}}}}
  return(s); }
proc delcol(matrix A, int k){ matrix B[4][4]; int r; int c; int cc; for(r=1;r<=4;r++){ cc=0; for(c=1;c<=5;c++){ if(c!=k){ cc++; B[r,cc]=1+A[r,c]; }}} return(B); }
list Rk; int k; for(k=1;k<=5;k++){ Rk = insert(Rk, perm4(delcol(Y,k))-24, size(Rk)); }''')
L.append('ideal E;')
conds=['Rk[5]'] if r4only else ['Rk[5]']+['(%s)*Rk[%d]-(%s)*Rk[%d]'%(Mexpr[l],k+1,Mexpr[k],l+1) for k in range(4) for l in range(k+1,4)]
for cnd in conds:
    UPROD='u0*'+'*'.join('u%d'%(s+1) for s in range(nv))+'*kk'
    L.append('matrix C = coef(%s, %s); int ii; for(ii=1;ii<=ncols(C);ii++){ if(C[2,ii]!=0){ E = E, C[2,ii]; } } kill C; kill ii;'%(cnd,UPROD))
L.append('E = E, %s;'%('+'.join(Mexpr[j] for j in range(4))))
L.append('E = E, %s;'%('+'.join('(%s)^2'%Mexpr[j] for j in range(4))))
L.append('E = simplify(E, 2+4+8);')   # remove zeros, duplicates (scalar multiples)
L.append('"NEQ", size(E);')
L.append('link lo = ":w %s"; open(lo); write(lo, "%s"); write(lo, "%d");'%(out,','.join(unk),P))
L.append('int q; for(q=1;q<=size(E);q++){ if(q<size(E)){ write(lo, string(E[q])+","); } else { write(lo, string(E[q])); } } close(lo);')
L.append('"WROTE"; quit;')
open(out.replace('.ms','.sing'),'w').write('\n'.join(L)+'\n')
