# K' census, exact: column-centred 3x5 level spaces S of dim nv (default 3) with defect inside C m (m in V5, projective; m = 0 allowed
# in the sense that e = 0 lies in every line).  Isotropic coordinates (a_0..a_4 = 0..4, b_0..b_4 = 5..9).  Exact identities (R2.5):
# P_2 = 3(sum a b - A B), P_3 = 6(e_3(a) + e_3(b)); deletion k: d2_k = 3(sum_{j!=k} a_j b_j - A^(k) B^(k)), d3_k = 6(e_3(a^(k)) + e_3(b^(k))).
# Equations (identities in u_1..u_nv): P_2, P_3, M_l d2_k - M_k d2_l, M_l d3_k - M_k d3_l (k<l), sum M = 0, chart M_J = 1.
# usage: python3 -I k3gen.py P S(pivots, comma) J OUT.ms
import sys
P=int(sys.argv[1]); S=[int(c) for c in sys.argv[2].split(',')]; J=int(sys.argv[3]); out=sys.argv[4]; nv=len(S)
free=[c for c in range(10) if c not in S]
gv=['g%d_%d'%(s,c) for s in range(nv) for c in free]; Mv=[]; unk=gv
us=['u%d'%(s+1) for s in range(nv)]
def coord(s,c):
    if c in S: return '1' if S.index(c)==s else '0'
    return 'g%d_%d'%(s,c)
Mx={j:'0' for j in range(5)}
L=['ring R = %d, (%s,%s), dp;'%(P,','.join(unk),','.join(us)),'short = 0;']
for j in range(5):
    L.append('poly a%d = %s;'%(j,' + '.join('u%d*(%s)'%(s+1,coord(s,j)) for s in range(nv))))
    L.append('poly b%d = %s;'%(j,' + '.join('u%d*(%s)'%(s+1,coord(s,5+j)) for s in range(nv))))
L.append('''proc e3(list v){ poly s=0; int i; int j; int k; int n=size(v); for(i=1;i<=n;i++){for(j=i+1;j<=n;j++){for(k=j+1;k<=n;k++){s=s+v[i]*v[j]*v[k];}}} return(s);}
proc sm(list v){ poly s=0; int i; for(i=1;i<=size(v);i++){s=s+v[i];} return(s);}
proc dot(list v, list w){ poly s=0; int i; for(i=1;i<=size(v);i++){s=s+v[i]*w[i];} return(s);}
list A = a0,a1,a2,a3,a4; list B = b0,b1,b2,b3,b4;
poly P2 = 3*(dot(A,B) - sm(A)*sm(B)); poly P3 = 6*(e3(A)+e3(B));
list D2; list D3; int k; list Ak; list Bk; int j;
for(k=1;k<=5;k++){ Ak = list(); Bk = list(); for(j=1;j<=5;j++){ if(j!=k){ Ak = insert(Ak, A[j], size(Ak)); Bk = insert(Bk, B[j], size(Bk)); } }
  D2 = insert(D2, 3*(dot(Ak,Bk) - sm(Ak)*sm(Bk)), size(D2)); D3 = insert(D3, 6*(e3(Ak)+e3(Bk)), size(D3)); }
ideal E;''')
Ml=[Mx[j] for j in range(5)]
L.append('list MM = %s;'%(','.join('poly(%s)'%x for x in Ml)))
UPROD='*'.join(us)
red='red' in sys.argv[5:]
if red:   # same ideal: with M_J = 1 the pair conditions follow from d_k = M_k d_J
    conds=['P2','P3']+['D2[%d]-MM[%d]*D2[%d]'%(k+1,k+1,J+1) for k in range(5) if k!=J]+['D3[%d]-MM[%d]*D3[%d]'%(k+1,k+1,J+1) for k in range(5) if k!=J]
else:
    conds=['P2','P3']+['D2[%d]'%(k+1) for k in range(5)]+['D3[%d]'%(k+1) for k in range(5)]
for c in conds:
    L.append('matrix C = coef(%s, %s); int ii; for(ii=1;ii<=ncols(C);ii++){ if(C[2,ii]!=0){ E = E, C[2,ii]; } } kill C; kill ii;'%(c,UPROD))

L.append('E = simplify(E, 2+4+8); "NEQ", size(E);')
L.append('link lo = ":w %s"; open(lo); write(lo, "%s"); write(lo, "%d");'%(out,','.join(unk),P))
L.append('int q; for(q=1;q<=size(E);q++){ if(q<size(E)){ write(lo, string(E[q])+","); } else { write(lo, string(E[q])); } } close(lo);')
L.append('"WROTE"; quit;')
open(out.replace('.ms','.sing'),'w').write('\n'.join(L)+'\n')
