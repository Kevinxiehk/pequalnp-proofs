# 3-column strongly level 3-spaces K = {(A_a s | A_b s | A_c s | 0 | 0)}, A_a+A_b+A_c = 1 (Walsh coordinates, dot = standard):
# B_j = 1-2A_j orthogonal (degree 2) and t(A_a s, A_b s, A_c s) = 0 identically (degree 3; t = polarised x1 x2 x3).
# Question: is every solution of some column of rank <= 1?  Saturate by the 2x2-minor ideals of A_a, A_b, A_c.
import sys
P=sys.argv[1]; out=sys.argv[2]
A=[['a%d%d'%(i,j) for j in range(3)] for i in range(3)]
B=[['b%d%d'%(i,j) for j in range(3)] for i in range(3)]
vars_=[x for r in A for x in r]+[x for r in B for x in r]
L=['ring R=%s,(%s,s1,s2,s3),dp; option(redSB); LIB "elim.lib";'%(P,','.join(vars_))]
L.append('matrix Aa[3][3]=%s; matrix Ab[3][3]=%s; matrix Id[3][3]=1,0,0,0,1,0,0,0,1;'%(','.join(x for r in A for x in r),','.join(x for r in B for x in r)))
L.append('matrix Ac=Id-Aa-Ab; matrix S[3][1]=s1,s2,s3;')
L.append('ideal E; int i; int j;')
L.append('list Ms=Aa,Ab,Ac;')
L.append('for(int k=1;k<=3;k++){ matrix M=Ms[k]; matrix Q=transpose(M)*M-(M+transpose(M))/2; for(i=1;i<=3;i++){for(j=i;j<=3;j++){E=E,Q[i,j];}} kill M; kill Q; }')
L.append('matrix x=Aa*S; matrix y=Ab*S; matrix z=Ac*S;')
L.append('poly T=x[1,1]*y[2,1]*z[3,1]+x[1,1]*y[3,1]*z[2,1]+x[2,1]*y[1,1]*z[3,1]+x[2,1]*y[3,1]*z[1,1]+x[3,1]*y[1,1]*z[2,1]+x[3,1]*y[2,1]*z[1,1];')
L.append('matrix TT=coef(T,s1*s2*s3); for(i=1;i<=ncols(TT);i++){E=E,TT[2,i];}')
L.append('ring R2=%s,(%s),dp; option(redSB); ideal E=imap(R,E); matrix Aa=imap(R,Aa); matrix Ab=imap(R,Ab); matrix Ac=imap(R,Ac);'%(P,','.join(vars_)))
L.append('ideal I=std(simplify(E,2)); printf("T3 p=%s: %%s gens, dim %%s",size(I),dim(I));'%P)
L.append('I=sat(I,minor(Aa,2)); I=std(I); printf("  after sat by rank(Aa)<=1: dim %%s unit %%s",dim(I),(reduce(1,I)==0));')
L.append('I=sat(I,minor(Ab,2)); I=std(I); printf("  after sat by rank(Ab)<=1: dim %%s unit %%s",dim(I),(reduce(1,I)==0));')
L.append('I=sat(I,minor(Ac,2)); I=std(I); printf("  after sat by rank(Ac)<=1: dim %%s unit %%s",dim(I),(reduce(1,I)==0));')
L.append('printf("RESULT T3 p=%s: every 3-column kernel has a column of rank <= 1: %%s",(reduce(1,I)==0)); quit;'%P)
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
