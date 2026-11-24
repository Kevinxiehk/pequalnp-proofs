# orbits of 4-subsets of the 13 two-zero coordinates (0 alpha, 1 delta, 2 delta', 3..7 a_0..a_4, 8..12 b_0..b_4) under
# rows 2<->3 (a_j <-> b_j), columns 3<->4 (delta <-> delta', a_3<->a_4, b_3<->b_4), cyclic columns (0 1 2)
import itertools
def gens():
    def rows(c): return c+5 if 3<=c<=7 else (c-5 if c>=8 else c)
    def c34(c): return {1:2,2:1,6:7,7:6,11:12,12:11}.get(c,c)
    def cyc(c):
        if 3<=c<=5: return 3+((c-3)+1)%3
        if 8<=c<=10: return 8+((c-8)+1)%3
        return c
    return [rows,c34,cyc]
G=gens()
def orbit(S):
    seen={S}; todo=[S]
    while todo:
        T=todo.pop()
        for f in G:
            U=tuple(sorted(f(c) for c in T))
            if U not in seen: seen.add(U); todo.append(U)
    return seen
done=set(); reps=[]
for S in itertools.combinations(range(13),4):
    if S in done: continue
    o=orbit(S); done|=o; reps.append((S,len(o)))
print(len(reps),'orbits, total',sum(n for _,n in reps))
open('repsz.txt','w').write('\n'.join(','.join(map(str,S))+' %d'%n for S,n in reps)+'\n')
