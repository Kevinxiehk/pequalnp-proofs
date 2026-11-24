# finiteness of the admissible set over the parameters (hh, tp): GB in a block order (Y-variables) > (hh, tp); every Y-variable must
# occur as a pure power among the leading monomials => the coordinate ring is finite over C[hh, tp] => ALL fibres finite.
import sys
ms=sys.argv[1]; out=sys.argv[2]
L=open(ms).read().split('\n'); v=L[0].strip().split(','); p=L[1].strip(); body=''.join(L[2:]).strip().rstrip(',')
par=[x for x in v if x in ('hh','tp')]; yv=[x for x in v if x not in par]
s='ring R = %s, (%s,%s), (dp(%d),dp(%d));\nideal I = %s;\nideal G = std(I);\n'%(p,','.join(yv),','.join(par),len(yv),len(par),body)
s+='int ok = 1; int i; int j; int found;\nfor(i=1;i<=%d;i++){ found=0; for(j=1;j<=size(G);j++){ poly lm = leadmonom(G[j]); if (lm / var(i) * var(i) == lm) { if (deg(lm) == deg(lm, intvec(%s))) { found=1; } } kill lm; } if(found==0){ ok=0; } }\n'%(len(yv),','.join(['1' if k==i else '0' for k in range(1)] ) if False else ','.join('0' for _ in range(len(yv)+len(par))))
open(out,'w').write(s)
