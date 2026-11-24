# Round 16: z = (2,1,1,1,0), last configuration: Z_1 = span(n, z') with n = rad(Z_1); rows 2, 3 carry n; row 4 carries w (w not parallel to n).
# Level of the single-row subspace {row1 = al z' + c1 n, row2 = c2 n, row3 = c3 n, row4 = c4 w}: all coefficients (in al, c1..c4) of sigma_1..sigma_4.
# Charts: n_0 = 1 (S_5 + scaling); z' -> z' + la n gauge: z'_0 = 0, scaling of z': z'_j = 1 for some j in 1..4 (WLOG j = 1 by S_4);
# w: w_k = 1, k in 0..4 (5 charts), then w not parallel to n by Rabinowitsch on the minor (n_0 w_j - n_j w_0) for j = 1..4 (u_j).
import itertools, sys
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r16'); from pr3lib import sig
P=sys.argv[1]; k=int(sys.argv[2]); j=int(sys.argv[3])
n=['1','n1','n2','n3','n4']; z=['0','1','z2','z3','z4']; w=['w%d'%i for i in range(5)]; w[k]='1'
rows=[['(al*(%s)+c1*(%s))'%(z[c],n[c]) for c in range(5)],['c2*(%s)'%n[c] for c in range(5)],['c3*(%s)'%n[c] for c in range(5)],['c4*(%s)'%w[c] for c in range(5)]]
lev=[sig(rows,t,range(5)) for t in range(1,5)]
vs=['n1','n2','n3','n4','z2','z3','z4']+[x for x in w if x!='1']+['u']
o=['ring R0=%s,(%s,al,c1,c2,c3,c4),dp;'%(P,','.join(vs)),'ideal L=%s;'%','.join(lev),
   'ideal C; int a; int b; matrix M;','for(a=1;a<=ncols(L);a++){ M=coef(L[a],al*c1*c2*c3*c4); for(b=1;b<=ncols(M);b++){ C=C,M[2,b]; } }',
   'C=C,u*((%s)*(%s)-(%s)*(%s))-1;'%(n[0],w[j],n[j],w[0]),
   'ring R=%s,(%s),dp; ideal C=imap(R0,C); C=simplify(C,2); ideal G=std(C);'%(P,','.join(vs)),
   '"srow2111 w-chart %d minor %d: dim",dim(G),"unit",(G[1]==1);'%(k,j),'quit;']
f='/home/kevxhk/work/L-gct-210/stage3/r16/srow2111_%d_%d_%s.sing'%(k,j,'p' if P!='0' else 'q'); open(f,'w').write('\n'.join(o)+'\n'); print(f)
