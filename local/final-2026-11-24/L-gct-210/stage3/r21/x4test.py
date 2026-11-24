# Round 21: dim Delta = 1 special locus, ka = 1. U' = span(d, d o d) vanishes at column 4, so every deletion vector has 4th entry 0: sigma_t(x minus
# column 4) = 0 (t = 1,2,3), i.e. X^(4) = {x restricted to columns 0..3} is a LEVEL 3x4 space. It contains e_1 (x) d', e_2 (x) d' (from H) and
# y = x*^(4) = (r_0', r_1', r_2') with r_0' + r_1' + r_2' = -(d' o d') (ka = 1). Test: is span(e_1 d', e_2 d', y) level possible? (exact, small)
# d' = (d0, d1, d2, -d0-d1-d2), <d',d'> = 0, chart d_A = 1 (scale of d is free: g_i d = (la g_i)(d/la)).
import sys, itertools; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r16'); from pr3lib import sig
A,P=int(sys.argv[1]),sys.argv[2]
d=['d0','d1','d2','d3']; d[A]='1'   # all four coordinates as variables, chart d_A = 1, linear constraint sum d = 0 added below
r0=['r0_%d'%j for j in range(4)]; r1=['r1_%d'%j for j in range(4)]
r2=['(-(%s)-(%s)-(%s)^2)'%(r0[j],r1[j],d[j]) for j in range(4)]
rows=[['al*(%s)'%r0[j] for j in range(4)],['al*(%s)+c1*(%s)'%(r1[j],d[j]) for j in range(4)],['al*(%s)+c2*(%s)'%(r2[j],d[j]) for j in range(4)]]
lev=[sig(rows,t,range(4)) for t in (1,2,3)]
dv=[x for x in ['d0','d1','d2','d3'] if x in d]
cons=['+'.join('(%s)^2'%x for x in d),'+'.join(d)]
vs=dv+r0+r1
o=['ring R0=0,(%s,al,c1,c2),dp;'%','.join(vs),'ideal L=%s;'%','.join(lev),'ideal C=%s; int kk; int ll; matrix M;'%','.join(cons),
   'for(kk=1;kk<=ncols(L);kk++){ M=coef(L[kk],al*c1*c2); for(ll=1;ll<=ncols(M);ll++){ C=C,M[2,ll]; } }',
   'ring R=%s,(%s),dp; ideal C=imap(R0,C); C=simplify(C,2); ideal G=std(C); "X4TEST chart d_%d = 1: dim",dim(G),"unit",(G[1]==1);'%(P,','.join(vs),A),'quit;']
f='/home/kevxhk/work/L-gct-210/stage3/r21/x4_%d_%s.sing'%(A,'q' if P=='0' else 'p'); open(f,'w').write('\n'.join(o)+'\n'); print(f)
