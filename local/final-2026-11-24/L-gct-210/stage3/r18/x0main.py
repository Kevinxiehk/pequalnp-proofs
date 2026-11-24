# Round 18: X0 core, MAIN CASE dim c(P_a) = dim c'(P_c) = 2. Delta_a = span(f_0, f_1) (chart: (0,1)-minor nonzero: f_0 = (1,0,p2,p3,*),
# f_1 = (0,1,q2,q3,*)); Delta_c = Delta_a^perp cap 1^perp with basis g_0, g_1 (computed as polynomial vectors: solve <g, f_k> = 0, sum g = 0 on a
# chart g_k[2+k] = 1 ... via explicit cross-product formulas below); Y_ab = {(L f, f - L f)}, Y_cd = {(M g, g - M g)}, L, M linear (2 x 5 each).
# Equations: level of X0 = Y_ab + Y_cd (all coefficients). Hinge-free first (expect: unit or degenerate).
import sys, itertools; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r16'); from pr3lib import sig
P=sys.argv[1]; GCH=sys.argv[2] if len(sys.argv)>2 else '34'
f0=['1','0','p2','p3','(-1-p2-p3)']; f1=['0','1','q2','q3','(-1-q2-q3)']
# Delta_c: g with sum g = 0, <g,f0> = 0, <g,f1> = 0: 3 linear equations in 5 unknowns -> 2-dim; chart: g_0 has (g[GCH[0]], g[GCH[1]]) = (1,0), g_1 = (0,1)
# solved symbolically inside Singular (linear solve) -> we instead introduce g-coordinates as unknowns with the linear equations as constraints.
a,b=int(GCH[0]),int(GCH[1])
g0=['g0%d'%j for j in range(5)]; g1=['g1%d'%j for j in range(5)]; g0[a]='1'; g0[b]='0'; g1[a]='0'; g1[b]='1'
L0=['L0%d'%j for j in range(5)]; L1=['L1%d'%j for j in range(5)]; M0=['M0%d'%j for j in range(5)]; M1=['M1%d'%j for j in range(5)]
rows=[['al*(%s)+be*(%s)'%(L0[j],L1[j]) for j in range(5)],['al*((%s)-(%s))+be*((%s)-(%s))'%(f0[j],L0[j],f1[j],L1[j]) for j in range(5)],
      ['ga*(%s)+de*(%s)'%(M0[j],M1[j]) for j in range(5)],['ga*((%s)-(%s))+de*((%s)-(%s))'%(g0[j],M0[j],g1[j],M1[j]) for j in range(5)]]
lev=[sig(rows,t,range(5)) for t in range(1,5)]
ip=lambda x,y: '+'.join('(%s)*(%s)'%(x[j],y[j]) for j in range(5))
lin=[ '+'.join(g) for g in (g0,g1)]+[ip(g0,f0),ip(g0,f1),ip(g1,f0),ip(g1,f1)]
vs=['p2','p3','q2','q3']+[x for x in g0+g1 if x not in ('0','1')]+L0+L1+M0+M1
o=['ring R0=0,(%s,al,be,ga,de),dp;'%','.join(vs),'ideal L=%s;'%','.join(lev),'ideal C=%s; int kk; int ll; matrix Mm;'%','.join(lin),
   'for(kk=1;kk<=ncols(L);kk++){ Mm=coef(L[kk],al*be*ga*de); for(ll=1;ll<=ncols(Mm);ll++){ C=C,Mm[2,ll]; } }',
   'ring R=%s,(%s),dp; option(redSB); ideal C=imap(R0,C); C=simplify(C,2);'%(P,','.join(vs)),
   '"eqs",ncols(C),"vars",nvars(R); int t0=timer; ideal G=%s(C); "X0MAIN g-chart %s: dim",dim(std(G)),"unit",(G[1]==1),"time",timer-t0;'%('slimgb' if P=='0' else 'std',GCH),"quit;"]
f='/home/kevxhk/work/L-gct-210/stage3/r18/x0main_%s_%s.sing'%(GCH,'q' if P=='0' else 'p'); open(f,'w').write('\n'.join(o)+'\n'); print(f)
