# Round 20: sub-case dim Delta <= 1 of the H-plane (strata (II)/(III)): h_i = h + t_i d (t_2 = 0, t_0 = 1, t_1 = t; distinct t's: u (t (1-t)) = 1).
# Defect <= 2: U' = span(d, uq) 2-dim (uq = second basis vector, chart: uq_A = 1, uq_B = 0 with d_B = 1, d_A = 0 normalised -- see charts) contains all
# deletion vectors of H. MODE 'H': H-part only (level of H + c, D_2, D_3 of H in U'). Membership via 3x3 minors of [d, uq, v] (rows {B, A, k}).
# Charts: d_B = 1 (d != 0; B in 0..4), uq_B = 0, uq_A = 1 (A != B): span(d, uq) has (B,A)-minor 1.
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r16'); from pr3lib import level, deletion
B,A,P=int(sys.argv[1]),int(sys.argv[2]),sys.argv[3]
h=['h%d'%j for j in range(5)]; d=['d%d'%j for j in range(5)]; d[B]='1'
uq=['q%d'%j for j in range(5)]; uq[B]='0'; uq[A]='1'
ts=['1','t','0']
H=[['(%s+(%s)*%s)'%(h[j],ts[i],d[j]) for j in range(5)] for i in range(3)]
co=['a','b','(-a-b)']
rows=[['(%s)*%s'%(co[i],H[i][j]) for j in range(5)] for i in range(3)]
lev=level(rows); c,D2,D3=deletion(rows)
vs=h+[x for x in d if x not in ('0','1')]+[x for x in uq if x not in ('0','1')]+['t','u']
o=['ring R0=0,(%s,a,b),dp;'%','.join(vs),'ideal L=%s;'%','.join(lev),'ideal C; int kk; int ll; matrix M; poly g;',
   'for(kk=1;kk<=ncols(L);kk++){ M=coef(L[kk],a*b); for(ll=1;ll<=ncols(M);ll++){ C=C,M[2,ll]; } }']
others=[k for k in range(5) if k not in (A,B)]
for nm,vec in (('c',c),('D2',D2),('D3',D3)):
    for j in range(5): o.append('poly %s_%d=%s;'%(nm,j,vec[j]))
    for k in others:
        o.append('g=det(matrix(ideal(%s,%s,%s_%d, %s,%s,%s_%d, %s,%s,%s_%d),3,3)); M=coef(g,a*b); for(ll=1;ll<=ncols(M);ll++){ C=C,M[2,ll]; }'%(
            d[B],uq[B],nm,B, d[A],uq[A],nm,A, d[k],uq[k],nm,k))
o.append('C=C,u*t*(1-t)-1;')
o.append('ring R=%s,(%s),dp; ideal C=imap(R0,C); C=simplify(C,2); ideal G=std(C); "DLT1 H-part B=%d A=%d: dim",dim(G),"unit",(G[1]==1);'%(P,','.join(vs),B,A))
o.append('quit;')
f='/home/kevxhk/work/L-gct-210/stage3/r20/dlt1_%d%d_%s.sing'%(B,A,'q' if P=='0' else 'p'); open(f,'w').write('\n'.join(o)+'\n'); print(f)
