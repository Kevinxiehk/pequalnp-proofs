# Round 18: generic "outside-row" pair test for z = (1,1,1,1,0) configurations. Rows 0..3 carry single-row vectors W[i] (polynomial vectors in
# configuration variables with constraints CONS = all single-row level conditions E(...) of the configuration), row 4 none. For a pair (r,k)
# the third element xi of X_{rk} lives on rows {l, n, 4}; gauge: xi_l -> xi_l + mu W[l], normalised by xi_l[g_l] = 0 where W[l][g_l] = 1 (chart);
# chart XC = 1 for one remaining xi-coordinate. Equations: all sigma_t coefficients (al, c0..c3) of al xi + sum c_i e_i W[i]. UNIT => no xi.
import sys, itertools; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r16'); from pr3lib import sig
def build(W, cons, cvars, r, k, gauge, XC, P, tag, field='0'):
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
    vs=cvars+[x for x in xl+xn+v if x not in ('0','1')]
    ring='ring R0=%s,(%s,al,c0,c1,c2,c3),dp;'%(field,','.join(vs))
    if field!='0': ring+=' minpoly=I^2+1;'
    o=[ring,'ideal L=%s;'%','.join(lev),'ideal C=%s; int kk; int ll; matrix M;'%(','.join(cons) if cons else '0'),
       'for(kk=1;kk<=ncols(L);kk++){ M=coef(L[kk],al*c0*c1*c2*c3); for(ll=1;ll<=ncols(M);ll++){ C=C,M[2,ll]; } }',
       ('ring R=%s,(%s),dp;'%(P if field=='0' else field,','.join(vs)))+(' minpoly=I^2+1;' if field!='0' else '')+' ideal C=imap(R0,C); C=simplify(C,2); ideal G=std(C);',
       '"%s pair (%d,%d) xi=%s: dim",dim(G),"unit",(G[1]==1);'%(tag,r,k,XC),'quit;']
    f='/home/kevxhk/work/L-gct-210/stage3/r18/pt_%s_%d%d_%s.sing'%(tag,r,k,XC); open(f,'w').write('\n'.join(o)+'\n'); return f
