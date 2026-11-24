# orbits of 4-subsets of 11 coords (a 0..3, b 4..7, z1 8, z2 9, z3 10) under S4 (columns) x S3 (rows 1..3: (2 3) = a<->b, z2<->z3; 3-cycle z1->z2->z3, a, b scaled)
import itertools
def col(sig):
    return lambda c: sig[c] if c<4 else (4+sig[c-4] if c<8 else c)
def r23(c): return c+4 if c<4 else (c-4 if c<8 else {8:8,9:10,10:9}[c])
def r3(c): return c if c<8 else {8:9,9:10,10:8}[c]
G=[col((1,0,2,3)),col((1,2,3,0)),r23,r3]
def orbit(S):
    seen={S}; todo=[S]
    while todo:
        T=todo.pop()
        for f in G:
            U=tuple(sorted(f(c) for c in T))
            if U not in seen: seen.add(U); todo.append(U)
    return seen
done=set(); reps=[]
for S in itertools.combinations(range(11),4):
    if S in done: continue
    o=orbit(S); done|=o; reps.append((S,len(o)))
print(len(reps),'orbits, total',sum(n for _,n in reps))
open('reps411.txt','w').write('\n'.join(','.join(map(str,S))+' %d'%n for S,n in reps)+'\n')
