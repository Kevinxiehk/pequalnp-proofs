# Round 18: configuration (2,1,1) of z = (1,1,1,1,0): rows 0,1 carry m, row 2 m', row 3 m'' (all in a totally isotropic plane T).
# All single-row level conditions = sum over row subsets R of the full permanent-sums; charts m_0 = 1, m'_A = 1, m''_B = 1; distinctness by
# Rabinowitsch on the minors (m ^ m')_{0A}, (m ^ m'')_{0B}, (m' ^ m'')_{AB}-type (one chart).  Report dim / vdim.
import sys, itertools; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r16'); from pr3lib import sig
A,B,P=int(sys.argv[1]),int(sys.argv[2]),sys.argv[3]
m=['1','m1','m2','m3','m4']; n=['n%d'%j for j in range(5)]; n[A]='1'; o_=['o%d'%j for j in range(5)]; o_[B]='1'
W=[m,m,n,o_]
rows=[['c%d*(%s)'%(i,W[i][j]) for j in range(5)] for i in range(4)]
lev=[sig(rows,t,range(5)) for t in range(1,5)]
vs=['m1','m2','m3','m4']+[x for x in n if x!='1']+[x for x in o_ if x!='1']+['u']
mn=lambda x,y,i,j: '((%s)*(%s)-(%s)*(%s))'%(x[i],y[j],x[j],y[i])
o=['ring R0=0,(%s,c0,c1,c2,c3),dp;'%','.join(vs),'ideal L=%s;'%','.join(lev),'ideal C; int kk; int ll; matrix M;',
   'for(kk=1;kk<=ncols(L);kk++){ M=coef(L[kk],c0*c1*c2*c3); for(ll=1;ll<=ncols(M);ll++){ C=C,M[2,ll]; } }',
   'C=C,u*%s*%s*%s-1;'%(mn(m,n,0,A if A!=0 else 1),mn(m,o_,0,B if B!=0 else 1),mn(n,o_,A,B)),
   'ring R=%s,(%s),dp; ideal C=imap(R0,C); C=simplify(C,2); ideal G=std(C); "CFG211 A=%d B=%d: dim",dim(G),"vdim",vdim(G);'%(P,','.join(vs),A,B),'quit;']
f='/home/kevxhk/work/L-gct-210/stage3/r18/cfg211_%d%d_%s.sing'%(A,B,'q' if P=='0' else 'p'); open(f,'w').write('\n'.join(o)+'\n'); print(f)
