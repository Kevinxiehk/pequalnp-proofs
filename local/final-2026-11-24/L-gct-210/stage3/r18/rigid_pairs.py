# Round 18: rigid member of z = (1,1,1,1,0): m = (1, i, -1, -i, 0) on rows 0,1,2, w = (1,1,1,1,-4) on row 3, row 4 none. For a pair (r,k) of
# rows in S = {0,1,2,3}, the third element xi of X_{rk} on the rows {l, n, 4} (l, n = S - {r,k}); gauge: xi_l mod (single-row vector of l),
# xi_n mod (vector of n) normalised at a coordinate where that vector is nonzero; chart XC = 1. Exact over Q(i). Prints dim/unit per chart.
import sys, itertools; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r16'); from pr3lib import sig
r,k,XC=int(sys.argv[1]),int(sys.argv[2]),sys.argv[3]
m=['1','I','-1','-I','0']; w=['1','1','1','1','-4']; vec={0:m,1:m,2:m,3:w}
l,n=[i for i in range(4) if i not in (r,k)]
xl=['xl%d'%j for j in range(5)]; xn=['xn%d'%j for j in range(5)]; v=['v%d'%j for j in range(5)]
xl[0]='0'; xn[0]='0'          # gauge: both single-row vectors have entry 1 at column 0
for L in (xl,xn,v):
    if XC in L: L[L.index(XC)]='1'
rows=[]
for i in range(5):
    if i in (r,k): rows.append(['c%d*(%s)'%(i,vec[i][j]) for j in range(5)])
    elif i==l: rows.append(['al*(%s)+c%d*(%s)'%(xl[j],i,vec[i][j]) for j in range(5)])
    elif i==n: rows.append(['al*(%s)+c%d*(%s)'%(xn[j],i,vec[i][j]) for j in range(5)])
    else: rows.append(['al*(%s)'%v[j] for j in range(5)])
lev=[sig(rows,t,range(5)) for t in range(1,6)]
vs=[x for x in xl+xn+v if x not in ('0','1')]
o=['ring R0=(0,I),(%s,al,c0,c1,c2,c3),dp; minpoly=I^2+1;'%','.join(vs),'ideal L=%s;'%','.join(lev),'ideal C; int kk; int ll; matrix M;',
   'for(kk=1;kk<=ncols(L);kk++){ M=coef(L[kk],al*c0*c1*c2*c3); for(ll=1;ll<=ncols(M);ll++){ C=C,M[2,ll]; } }',
   'ring R=(0,I),(%s),dp; minpoly=I^2+1; ideal C=imap(R0,C); C=simplify(C,2); ideal G=std(C);'%','.join(vs),
   '"PAIR (%d,%d) xi=%s: dim",dim(G),"unit",(G[1]==1);'%(r,k,XC),'if(dim(G)>=0){print(G);}','quit;']
f='/home/kevxhk/work/L-gct-210/stage3/r18/rp_%d%d_%s.sing'%(r,k,XC); open(f,'w').write('\n'.join(o)+'\n'); print(f)
