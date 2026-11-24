# Round 20: dim Delta = 1, distinct t's, s = 1 branch: h_i = e_4 + g_i d (d_4 = 0, sum d = 0, <d,d> = 0), U' = span(d, d o d); x* normalised by
# c(x*) = ka (d o d) (subtract an H-element): ka = 0 (zero column sums) or ka = 1 (scale). Equations: all (a,b,e)-coefficients of sigma_1..3 of
# x = (a h_0, b h_1, (-a-b) h_2) + e x*, and U'-membership of c, D_2, D_3 (3x3 minors of [d, d o d, v] on rows {A,B,k}, chart u2 * minor_{AB} = 1).
# x*-chart: KA = 0: r_{I,J} = 1; KA = 1: none needed (scale fixed by ka = 1).
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r16'); from pr3lib import level, deletion
KA,A,B,P=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]),sys.argv[4]; XI=sys.argv[5] if len(sys.argv)>5 else ''
d=['d0','d1','d2','(-d0-d1-d2)','0']; dd=['(%s)^2'%x for x in d]
g=['g0','g1','g2']
H=[['(%s+%s*%s)'%('1' if j==4 else '0',g[i],d[j]) for j in range(5)] for i in range(3)]
r0=['r0_%d'%j for j in range(5)]; r1=['r1_%d'%j for j in range(5)]
if KA==0 and XI: I,J=int(XI[0]),int(XI[1]); (r0 if I==0 else r1)[J]='1'
r2=['(-(%s)-(%s)%s)'%(r0[j],r1[j],('+ka*%s'%dd[j]) if KA==1 else '') for j in range(5)]   # column sums of x* = -ka (d o d)  [c(x) = -(sum of rows)]
r2=['(-(%s)-(%s)-%s)'%(r0[j],r1[j],dd[j]) if KA==1 else '(-(%s)-(%s))'%(r0[j],r1[j]) for j in range(5)]
R=[r0,r1,r2]; co=['a','b','(-a-b)']
rows=[['(%s)*%s+e*%s'%(co[i],H[i][j],R[i][j]) for j in range(5)] for i in range(3)]
lev=level(rows); c,D2,D3=deletion(rows)
vs=['d0','d1','d2','g0','g1','g2']+[x for x in r0+r1 if x!='1']+['u','u2']
o=['ring R0=0,(%s,a,b,e),dp;'%','.join(vs),'ideal L=%s;'%','.join(lev),'ideal C; int kk; int ll; matrix M; poly gg;',
   'for(kk=1;kk<=ncols(L);kk++){ M=coef(L[kk],a*b*e); for(ll=1;ll<=ncols(M);ll++){ C=C,M[2,ll]; } }']
others=[k for k in range(5) if k not in (A,B)]
for nm,vec in (('c',c),('D2',D2),('D3',D3)):
    for j in range(5): o.append('poly %s_%d=%s;'%(nm,j,vec[j]))
    for k in others:
        o.append('gg=det(matrix(ideal(%s,%s,%s_%d, %s,%s,%s_%d, %s,%s,%s_%d),3,3)); M=coef(gg,a*b*e); for(ll=1;ll<=ncols(M);ll++){ C=C,M[2,ll]; }'%(
            d[A],dd[A],nm,A, d[B],dd[B],nm,B, d[k],dd[k],nm,k))
o.append('C=C,u*(g0-g1)*(g0-g2)*(g1-g2)-1,u2*((%s)*(%s)-(%s)*(%s))-1;'%(d[A],dd[B],d[B],dd[A]))
o.append('ring R=%s,(%s),dp; ideal C=imap(R0,C); C=simplify(C,2); ideal G=std(C); "DLT1B ka=%d chart %d%d x*%s: dim",dim(G),"unit",(G[1]==1);'%(P,','.join(vs),KA,A,B,XI))
o.append('quit;')
f='/home/kevxhk/work/L-gct-210/stage3/r20/dlt1b_%d_%d%d%s_%s.sing'%(KA,A,B,XI,'q' if P=='0' else 'p'); open(f,'w').write('\n'.join(o)+'\n'); print(f)
