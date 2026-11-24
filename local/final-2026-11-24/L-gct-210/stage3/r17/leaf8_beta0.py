# Round 17: the rank-drop configuration of "three m + w": m = (1, i, -1, -i, 0) (e_5(m) = 0), w = (1,1,1,1,-4). Exact over Q(i):
# third element xi = (v row 4; a row 1; b row 2) of X_{03} (rows 0, 3 zero); gauge a_0 = b_0 = 0; chart xi-coordinate XC = 1.
import sys, itertools; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r16'); from pr3lib import sig
XC=sys.argv[1]
m=['1','I','-1','-I','0']; w=['1','1','1','1','-4']
v=['v%d'%j for j in range(5)]; a=['0']+['a%d'%j for j in range(1,5)]; b=['0']+['b%d'%j for j in range(1,5)]
for L in (v,a,b):
    if XC in L: L[L.index(XC)]='1'
rows=[['c0*(%s)'%m[j] for j in range(5)],['al*(%s)+c1*(%s)'%(a[j],m[j]) for j in range(5)],['al*(%s)+c2*(%s)'%(b[j],m[j]) for j in range(5)],
      ['c3*(%s)'%w[j] for j in range(5)],['al*(%s)'%v[j] for j in range(5)]]
lev=[sig(rows,t,range(5)) for t in range(1,6)]
vs=[x for x in v+a+b if x not in ('0','1')]
o=['ring R0=(0,I),(%s,al,c0,c1,c2,c3),dp; minpoly=I^2+1;'%','.join(vs),'ideal L=%s;'%','.join(lev),'ideal C; int k; int l; matrix M;',
   'for(k=1;k<=ncols(L);k++){ M=coef(L[k],al*c0*c1*c2*c3); for(l=1;l<=ncols(M);l++){ C=C,M[2,l]; } }',
   'ring R=(0,I),(%s),dp; minpoly=I^2+1; ideal C=imap(R0,C); C=simplify(C,2); ideal G=std(C);'%','.join(vs),
   '"BETA0 xi=%s: dim",dim(G),"unit",(G[1]==1);'%XC,'quit;']
f='/home/kevxhk/work/L-gct-210/stage3/r17/lb0_%s.sing'%XC; open(f,'w').write('\n'.join(o)+'\n'); print(f)
