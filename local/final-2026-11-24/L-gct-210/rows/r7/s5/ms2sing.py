# convert an msolve input file to a Singular script computing std, dim, vdim (dp order)
import sys
src,out,tag=sys.argv[1],sys.argv[2],sys.argv[3]
L=open(src).read().split('\n'); vars_=L[0].strip(); p=L[1].strip(); pols=' '.join(L[2:]).strip().rstrip(',')
open(out,'w').write('ring r=%s,(%s),dp; option(redSB);\nideal I=%s;\nint t=timer; ideal G=std(I);\nprintf("%s: dim %%s vdim %%s unit %%s size %%s",dim(G),vdim(G),(reduce(1,G)==0),size(G));\nquit;\n'%(p,vars_,pols,tag))
