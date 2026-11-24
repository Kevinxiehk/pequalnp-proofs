# Round 20: exact level check of a one-parameter-free space over Q(w): every level polynomial of the 6 basis matrices reduces to 0 mod w^2+w+1.
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
import sympy as sp
from famtool import *
fam=sys.argv[1]; src=open('/home/kevxhk/work/L-gct-210/reg2/gb/gen_rank.py').read(); sys.argv=['x',fam,'16','1','1']
exec(src[:src.index('F=Family(params,bfn,d)')])
F=Family(params,bfn,d); W=sp.Symbol('w'); iw=F.names.index('w')
bad=0
for q in F.level:
    p=sum(sp.Integer(v)*W**k[iw] for k,v in q.items() if not any(k[i] for i in range(len(k)) if i!=iw))
    if any(any(k[i] for i in range(len(k)) if i!=iw) for k in q): print('unexpected variables'); bad+=1; continue
    if sp.rem(sp.expand(p),W**2+W+1,W)!=0: bad+=1
print(fam,': %d level polynomials, %d nonzero mod w^2+w+1'%(len(F.level),bad))
