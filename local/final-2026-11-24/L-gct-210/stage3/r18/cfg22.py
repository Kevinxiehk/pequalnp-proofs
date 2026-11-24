# z = (1,1,1,1,0), configuration (2,2): rows 0,1 carry m, rows 2,3 carry m' (T = span(m,m') totally isotropic, k_N = 0).
# Charts: m_0 = 1 (S_5, scale), m'_1 = 1 or m'_0 = 1 (scale; S_4 on columns 1..4). Constraints: all E_{a,b}(m,m') (a,b <= 2) = 0.
import sys, itertools; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r18'); from pairtest import build
ch,r,k,XC,P=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]),sys.argv[4],sys.argv[5]
m=['1','m1','m2','m3','m4']; n=['n0','n1','n2','n3','n4']; n[ch]='1'
def E(a,b):
    t=[]
    for A in itertools.combinations(range(5),a):
        rest=[j for j in range(5) if j not in A]
        for B in itertools.combinations(rest,b): t.append('*'.join([m[j] for j in A]+[n[j] for j in B]) or '1')
    return '+'.join(t)
cons=[E(a,b) for a in range(3) for b in range(3) if (a,b)!=(0,0)]
cv=['m1','m2','m3','m4']+[x for x in n if x!='1']
W={0:m,1:m,2:n,3:n}; gauge={0:0,1:0,2:ch,3:ch}
print(build(W,cons,cv,r,k,gauge,XC,P,'c22_%d'%ch))
