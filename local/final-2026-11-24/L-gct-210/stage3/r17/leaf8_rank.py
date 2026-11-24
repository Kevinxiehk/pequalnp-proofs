# Round 17: rank conditions for the hand argument of the configuration "rows 0,1,2: m (e_1=e_2=e_3=0), row 3: w orthogonal to 1, m, m^2, m^3":
#   R1: rank(m, m^2, m^3, w m^2, w m^3) = 4,   R2: rank(m, m^2, w m, w m^2) = 3.
# Exact: the loci where R1 or R2 FAIL (all 4x4 resp. 3x3 minors vanish), with m_0 = 1 (S_5, scale), w-chart w_J = 1. UNIT => R1, R2 hold always.
import sys, itertools
J,which,P=int(sys.argv[1]),sys.argv[2],sys.argv[3]
m=['1','m1','m2','m3','m4']; w=['w%d'%j for j in range(5)]; w[J]='1'
def e(k,x): return '+'.join('*'.join(x[i] for i in S) for S in itertools.combinations(range(5),k))
pw=lambda x,t: ['((%s)^%d)'%(y,t) if t>0 else '1' for y in x]
eqs=[e(1,m),e(2,m),e(3,m)]+['+'.join('(%s)*%s'%(w[j],pw(m,t)[j]) for j in range(5)) for t in range(4)]
if which=='R1': cols=[pw(m,1),pw(m,2),pw(m,3),['(%s)*%s'%(w[j],pw(m,2)[j]) for j in range(5)],['(%s)*%s'%(w[j],pw(m,3)[j]) for j in range(5)]]; r=4
else: cols=[pw(m,1),pw(m,2),['(%s)*%s'%(w[j],pw(m,1)[j]) for j in range(5)],['(%s)*%s'%(w[j],pw(m,2)[j]) for j in range(5)]]; r=3
vs=['m1','m2','m3','m4']+[x for x in w if x!='1']
o=['ring R=%s,(%s),dp;'%(P,','.join(vs)),'matrix A[5][%d];'%len(cols)]
for c,col in enumerate(cols):
    for j in range(5): o.append('A[%d,%d]=%s;'%(j+1,c+1,col[j]))
o+=['ideal C=%s;'%','.join(eqs),'C=C,minor(A,%d);'%r,'ideal G=std(C);','"RANK %s w%d: dim",dim(G),"unit",(G[1]==1);'%(which,J),'quit;']
f='/home/kevxhk/work/L-gct-210/stage3/r17/lrank_%s_%d_%s.sing'%(which,J,'q' if P=='0' else 'p'); open(f,'w').write('\n'.join(o)+'\n'); print(f)
