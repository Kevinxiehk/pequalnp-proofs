# msolve reduced grevlex GB (.out) + its input (.ms) -> Singular script printing dim and vdim (GB loaded as SB, no recomputation)
import sys, re
ms,out,sing=sys.argv[1:4]
L=open(ms).read().split('\n'); v=L[0].strip(); p=L[1].strip()
gb=open(out).read().split('#---')[-1].strip().lstrip('[').rstrip(':').rstrip(']').replace('\n','')
open(sing,'w').write('ring R = %s, (%s), dp;\nideal G = %s;\nattrib(G,"isSB",1);\n"DIM", dim(G); if (dim(G)==0) { "VDIM", vdim(G); }\nquit;\n'%(p,v,gb))
