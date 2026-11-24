# verify2 r7: substitution test of stage3's FC generator with the exact solution M_0 (mod p, omega realised mod p).
import sys
p=2147483629
sys.argv=['fc_gen.py',str(p),'IDENT23']
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/gb'); import gbl as G, fc_gen as F
g=2
while pow(g,(p-1)//3,p)==1: g+=1
w=pow(g,(p-1)//3,p); assert (w*w+w+1)%p==0
inv=lambda x: pow(x%p,p-2,p)
qa=[1,w*w%p,0,w]; qb=[(-x)%p for x in qa]; qc=[1,w,0,w*w%p]; qd=[(-x)%p for x in qc]
wv=[1,1,(-3)%p,1]; pp=[0,0,0,0]          # w scaled by -1 so that w[0]=1; p'=0
pt=qa[:3]+qb[:3]+qc[:3]+qd[:3]+wv[:3]+pp[:3]+[0]*7+[inv(qb[0]),inv(qd[0])]
def ev(f): return sum(c*pow(1,0)*eval_mon(k) for k,c in f.items())%p
def eval_mon(k):
    r=1
    for i,e in enumerate(k):
        if e: r=r*pow(pt[i],e,p)%p
    return r
F.MODE='LEVEL'; eqL,_,nlev=F.system(0,0,0,0,0)
F.MODE='IDENT23'; eqI,_,_=F.system(0,0,0,0,0)
lev=[ev(f) for f in eqL]; ide=[ev(f) for f in eqI]
print('LEVEL system: %d polys, nonzero values at M_0: %d'%(len(eqL),sum(1 for v in lev if v)))
print('IDENT23 system: %d polys, nonzero values at M_0: %d (must be > 0: M_0 violates (iii))'%(len(eqI),sum(1 for v in ide if v)))
# random point must violate LEVEL
import random; random.seed(5); pt=[random.randrange(p) for _ in range(27)]
print('random point: nonzero LEVEL values %d of %d'%(sum(1 for f in eqL if ev(f)),len(eqL)))
