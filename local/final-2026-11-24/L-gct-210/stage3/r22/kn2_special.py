# Round 22: a special k_N = 2 member: rows 0,1: m = (1, w^2, w, 0, 0) (w^2 + w + 1 = 0), row 2: (0,0,0,1,-1), row 3: (2,2,2,-3,-3); row 4 none.
# Exact pair test over Q(w) for pair (r,k): third element xi of X_{rk} on rows {l, n, 4}; gauge xi_l[g_l] = 0, xi_n[g_n] = 0; chart XC = 1.
import sys, itertools; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r16'); from pr3lib import sig
r,k,XC=int(sys.argv[1]),int(sys.argv[2]),sys.argv[3]
W={0:['1','w^2','w','0','0'],1:['1','w^2','w','0','0'],2:['0','0','0','1','-1'],3:['2','2','2','-3','-3']}
gauge={0:0,1:0,2:3,3:0}
l,n=[i for i in range(4) if i not in (r,k)]
xl=['xl%d'%j for j in range(5)]; xn=['xn%d'%j for j in range(5)]; v=['v%d'%j for j in range(5)]
xl[gauge[l]]='0'; xn[gauge[n]]='0'
for L in (xl,xn,v):
    if XC in L: L[L.index(XC)]='1'
rows=[]
for i in range(5):
    if i in (r,k): rows.append(['c%d*(%s)'%(i,W[i][j]) for j in range(5)])
    elif i==l: rows.append(['al*(%s)+c%d*(%s)'%(xl[j],i,W[i][j]) for j in range(5)])
    elif i==n: rows.append(['al*(%s)+c%d*(%s)'%(xn[j],i,W[i][j]) for j in range(5)])
    else: rows.append(['al*(%s)'%v[j] for j in range(5)])
lev=[sig(rows,t,range(5)) for t in range(1,6)]
vs=[x for x in xl+xn+v if x not in ('0','1')]
o=['ring R0=(0,w),(%s,al,c0,c1,c2,c3),dp; minpoly=w^2+w+1;'%','.join(vs),'ideal L=%s;'%','.join(lev),'ideal C; int kk; int ll; matrix M;',
   'for(kk=1;kk<=ncols(L);kk++){ M=coef(L[kk],al*c0*c1*c2*c3); for(ll=1;ll<=ncols(M);ll++){ C=C,M[2,ll]; } }',
   'ring R=(0,w),(%s),dp; minpoly=w^2+w+1; ideal C=imap(R0,C); C=simplify(C,2); ideal G=std(C);'%','.join(vs),
   '"kn2 pair (%d,%d) xi=%s: dim",dim(G),"unit",(G[1]==1); if(G[1]!=1){print(G);}'%(r,k,XC),'quit;']
f='/home/kevxhk/work/L-gct-210/stage3/r22/kn2_%d%d_%s.sing'%(r,k,XC); open(f,'w').write('\n'.join(o)+'\n'); print(f)
