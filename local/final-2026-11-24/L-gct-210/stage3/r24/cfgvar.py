# Round 24: exact configuration variety of a (1,1,1,1,0) configuration: rows 0..3 single-row vectors; all single-row level conditions
# (coefficients of c-monomials of sigma_t of sum c_i e_i (x) w_i). CFG kn2: w0 = w1 = m, w2 = n2, w3 = n3 (non-isotropic hinges).
# Charts: m0 = 1 (S_5), n2[J2] = 1, n3[J3] = 1. Output: dim and minimal associated primes (minAssGTZ).
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r16'); from pr3lib import sig
CFG,J2,J3=sys.argv[1],int(sys.argv[2]),int(sys.argv[3])
m=['1']+['m%d'%j for j in range(1,5)]
n2=['n2%d'%j for j in range(5)]; n3=['n3%d'%j for j in range(5)]
n2[J2]='1'; n3[J3]='1'
if CFG=='kn2': W=[m,m,n2,n3]
elif CFG=='22': W=[m,m,n2,n2]
rows=[['c%d*(%s)'%(i,W[i][j]) for j in range(5)] for i in range(4)]+[['0']*5]
lev=[sig(rows,t,range(5)) for t in range(1,5)]
vs=[x for x in m[1:]+n2+(n3 if CFG=='kn2' else []) if x!='1']
hin=[]
if CFG=='kn2': hin=['u2*(%s)-1'%'+'.join('(%s)^2'%x for x in n2),'u3*(%s)-1'%'+'.join('(%s)^2'%x for x in n3)]
o=['ring R0=0,(%s,u2,u3,c0,c1,c2,c3),dp;'%','.join(vs),'ideal L=%s;'%','.join(lev),'ideal C; int kk; int ll; matrix M;',
   'for(kk=1;kk<=ncols(L);kk++){ M=coef(L[kk],c0*c1*c2*c3); for(ll=1;ll<=ncols(M);ll++){ C=C,M[2,ll]; } }',
   ''.join('C=C,%s;'%h for h in hin),
   'ring R=0,(%s,u2,u3),dp; ideal C=imap(R0,C); C=simplify(C,2); ideal G=std(C); "cfg %s chart %d %d: dim",dim(G);'%(','.join(vs),CFG,J2,J3),
   'LIB "primdec.lib"; if(dim(G)>=0){ list P=minAssGTZ(G); int pp; for(pp=1;pp<=size(P);pp++){ "component",pp,"dim",dim(std(P[pp])); print(P[pp]); } }','quit;']
f='/home/kevxhk/work/L-gct-210/stage3/r24/cfg_%s_%d%d.sing'%(CFG,J2,J3); open(f,'w').write('\n'.join(o)+'\n'); print(f)
