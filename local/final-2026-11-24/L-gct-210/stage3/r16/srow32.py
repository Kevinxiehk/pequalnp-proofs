# Round 16: z = (1,1,1,1,1), the last configuration (3,2): single-row vectors m in three rows, m' in two rows (T = span(m, m') totally
# isotropic). Level of the single-row subspace {sum_{i in S} c_i e_i m + sum_{i in S'} c'_i e_i m'} <=> E_{a,b}(m, m') = 0 for 0<=a<=3, 0<=b<=2,
# (a,b) != (0,0), where E_{a,b}(x,y) = sum over disjoint column sets A, B (|A| = a, |B| = b) of prod_A x prod_B y.
# Charts: m_0 = 1 (S_5, scaling of m); m'_0 = 1 or m'_1 = 1 (stabiliser S_4 of column 0, scaling of m').  Expect UNIT.
import itertools, sys
P=sys.argv[1]; ch=int(sys.argv[2]); amax=int(sys.argv[3]) if len(sys.argv)>3 else 3; bmax=int(sys.argv[4]) if len(sys.argv)>4 else 2
m=['1','m1','m2','m3','m4']; n=['n0','n1','n2','n3','n4']; n[ch]='1'
def E(a,b):
    t=[]
    for A in itertools.combinations(range(5),a):
        rest=[j for j in range(5) if j not in A]
        for B in itertools.combinations(rest,b):
            t.append('*'.join([m[j] for j in A]+[n[j] for j in B]) or '1')
    return '+'.join(t)
eqs=[E(a,b) for a in range(amax+1) for b in range(bmax+1) if (a,b)!=(0,0)]
vs=['m1','m2','m3','m4']+[x for x in n if x!='1']
s='ring R=%s,(%s),dp;\nideal I=%s;\nideal G=std(I);\n"srow32 chart %d (a<=%d,b<=%d): dim",dim(G),"unit",(G[1]==1);\nquit;\n'%(P,','.join(vs),',\n'.join(eqs),ch,amax,bmax)
f='/home/kevxhk/work/L-gct-210/stage3/r16/srow32_%d_%d%d_%s.sing'%(ch,amax,bmax,'p' if P!='0' else 'q'); open(f,'w').write(s); print(f)
