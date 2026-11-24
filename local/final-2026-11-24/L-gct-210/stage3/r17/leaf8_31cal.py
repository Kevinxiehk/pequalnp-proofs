# Round 17: EXACT test, z = (1,1,1,1,0), configuration "rows 0,1,2 carry m (e_1 = e_2 = e_3 = 0), row 3 carries w (w orthogonal to 1, m, m^2, m^3),
# row 4 none" (= k_N = 1 and the (3,1) distribution). Regime: lam_{03} = dim X_{03} >= 3, X_{03} contains e_1 m, e_2 m. A third element
# xi = (v row 4; a row 1; b row 2) (rows 0, 3 zero), gauge a_0 = b_0 = 0 (m_0 = 1), chart xi-coordinate = 1, w-chart w_J = 1.
# Equations: all coefficients (in al, c0..c3) of sigma_1..sigma_5 of al xi + c0 e_0 m + c1 e_1 m + c2 e_2 m + c3 e_3 w, plus e_1(m) = e_2(m) = e_3(m) = 0,
# <w, m^t> = 0 (t = 0..3).  UNIT => no third element => lam_{03} <= 2 < 3: configuration impossible in the regime.
import sys, itertools; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r16'); from pr3lib import sig
J,XC,P=int(sys.argv[1]),sys.argv[2],sys.argv[3]; CAL=len(sys.argv)>4
m=['1','m1','m2','m3','m4']; w=['w%d'%j for j in range(5)]; w[J]='1'
v=['v%d'%j for j in range(5)]; a=['0']+['a%d'%j for j in range(1,5)]; b=['0']+['b%d'%j for j in range(1,5)]
for L in (v,a,b):
    if XC in L: L[L.index(XC)]='1'
Z=['0']*5
rows=[['c0*(%s)'%m[j] for j in range(5)],['al*(%s)+c1*(%s)'%(a[j],m[j]) for j in range(5)],['al*(%s)+c2*(%s)'%(b[j],m[j]) for j in range(5)],
      ['c3*(%s)'%w[j] for j in range(5)],['al*(%s)'%v[j] for j in range(5)]]
lev=[sig(rows,t,range(5)) for t in range(1,6)]
def e(k,x): return '+'.join('*'.join(x[i] for i in S) for S in itertools.combinations(range(5),k))
pw=lambda x,t: ['(%s)^%d'%(y,t) if t>0 else '1' for y in x]
extra=[e(1,m),e(2,m),e(3,m)]+['+'.join('(%s)*(%s)'%(w[j],pw(m,t)[j]) for j in range(5)) for t in range(4)]
vs=['m1','m2','m3','m4']+[x for x in w if x!='1']+[x for x in v+a+b if x not in ('0','1')]
o=['ring R0=0,(%s,al,c0,c1,c2,c3),dp;'%','.join(vs),'ideal L=%s;'%','.join(lev),'ideal C=%s; int k; int l; matrix M;'%','.join(extra),
   'for(k=1;k<=ncols(L);k++){ M=coef(jet(L[k],1,intvec(%s)),al*c0*c1*c2*c3); for(l=1;l<=ncols(M);l++){ C=C,M[2,l]; } }'%(','.join(['0']*len(vs)+['1','0','0','0','0'])),
   'ring R=%s,(%s),dp; ideal C=imap(R0,C); C=simplify(C,2); ideal G=std(C);'%(P,','.join(vs)),
   '"CAL(al-linear only) LEAF8-31 w%d xi=%s: dim",dim(G),"unit",(G[1]==1);'%(J,XC),'quit;']
f='/home/kevxhk/work/L-gct-210/stage3/r17/l831cal_%d_%s_%s.sing'%(J,XC,'q' if P=='0' else 'p'); open(f,'w').write('\n'.join(o)+'\n'); print(f)
