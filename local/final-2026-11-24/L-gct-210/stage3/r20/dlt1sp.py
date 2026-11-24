# Round 20: dim Delta = 1 SPECIAL LOCUS: h_0 = e_4, h_1 = e_4 + g1 d, h_2 = e_4 + g2 d (d_4 = 0, sum d = 0, <d,d> = 0, g1 != g2, g1 g2 != 0), U' = span(d, d o d).
# x* = (r_0, r_1, r_2) with column sums -ka (d o d): KA = 0 (chart r_{I,J} = 1) or KA = 1 (scale fixed). Claim: KA = 1 empty, and for KA = 0 the
# charts with J in {0,1,2,3} are empty (x* supported in column 4 = a column element).
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r16'); from pr3lib import level, deletion
KA,XI,P=int(sys.argv[1]),sys.argv[2],sys.argv[3]; A,B=0,1
d=['d0','d1','d2','(-d0-d1-d2)','0']; dd=['(%s)^2'%x for x in d]
g=['0','g1','g2']
H=[['(%s+%s*%s)'%('1' if j==4 else '0',g[i],d[j]) for j in range(5)] for i in range(3)]
r0=['r0_%d'%j for j in range(5)]; r1=['r1_%d'%j for j in range(5)]
if KA==0: I,J=int(XI[0]),int(XI[1]); (r0 if I==0 else r1)[J]='1'
r2=['(-(%s)-(%s)-%s)'%(r0[j],r1[j],dd[j]) if KA==1 else '(-(%s)-(%s))'%(r0[j],r1[j]) for j in range(5)]
R=[r0,r1,r2]; co=['a','b','(-a-b)']
rows=[['(%s)*%s+e*%s'%(co[i],H[i][j],R[i][j]) for j in range(5)] for i in range(3)]
lev=level(rows); c,D2,D3=deletion(rows)
vs=['d0','d1','d2','g1','g2']+[x for x in r0+r1 if x!='1']+['u','u2']+(['u3'] if (KA==1 and XI!='x') else [])
o=['ring R0=0,(%s,a,b,e),dp;'%','.join(vs),'ideal L=%s;'%','.join(lev),'ideal C=%s; int kk; int ll; matrix M; poly gg;'%('+'.join('(%s)^2'%x for x in d[:4])),
   'for(kk=1;kk<=ncols(L);kk++){ M=coef(L[kk],a*b*e); for(ll=1;ll<=ncols(M);ll++){ C=C,M[2,ll]; } }']
for nm,vec in (('c',c),('D2',D2),('D3',D3)):
    for j in range(5): o.append('poly %s_%d=%s;'%(nm,j,vec[j]))
    for k in (2,3,4):
        o.append('gg=det(matrix(ideal(%s,%s,%s_%d, %s,%s,%s_%d, %s,%s,%s_%d),3,3)); M=coef(gg,a*b*e); for(ll=1;ll<=ncols(M);ll++){ C=C,M[2,ll]; }'%(
            d[A],dd[A],nm,A, d[B],dd[B],nm,B, d[k],dd[k],nm,k))
o.append(('C=C,u3*r%s_%s-1;'%(XI[0],XI[1])) if (KA==1 and XI!='x') else '')
if KA==1:
    p3='+'.join('(%s)^3'%x for x in d[:4])
    o.append('C=C,%s,%s,%s,(%s)-(%s),(%s)+(%s),%s;'%('+'.join(r0[:4]),'+'.join(r1[:4]),'+'.join(r2[:4]),'+'.join('(%s)*(%s)'%(r0[j],d[j]) for j in range(4)),p3,'+'.join('(%s)*(%s)'%(r1[j],d[j]) for j in range(4)),p3,'+'.join('(%s)*(%s)^2'%(r0[j],d[j]) for j in range(4))))
o.append('C=C,u*g1*g2*(g1-g2)-1,u2*((%s)*(%s)-(%s)*(%s))-1;'%(d[A],dd[B],d[B],dd[A]))
o.append('ring R=%s,(%s),dp; ideal C=imap(R0,C); C=simplify(C,2); ideal G=std(C); "DLT1SP ka=%d x*chart %s: dim",dim(G),"unit",(G[1]==1);'%(P,','.join(vs),KA,XI))
o.append('quit;')
f='/home/kevxhk/work/L-gct-210/stage3/r20/dlt1sp_%d_%s_%s.sing'%(KA,XI,'q' if P=='0' else 'p'); open(f,'w').write('\n'.join(o)+'\n'); print(f)
