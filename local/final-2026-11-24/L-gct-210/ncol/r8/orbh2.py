# orbit reps of 4-subsets of the 13 H-coordinates for types b22 / b23 (env TYPE); coordinates: 0..2 s, 3..7 a_0..a_4, 8..12 b_0..b_4
import itertools, os
TY=os.environ.get('TYPE','b22')
def swap(i,j):
    def f(c):
        if c<3: return c
        base=3 if c<8 else 8; k=c-base
        k=j if k==i else (i if k==j else k); return base+k
    return f
def ab(c): return c+5 if 3<=c<=7 else (c-5 if c>=8 else c)
gens=[swap(0,1),ab]+([swap(2,3)] if TY=='b22' else [])
def orbit(S):
    seen={tuple(sorted(S))}; todo=list(seen)
    while todo:
        T=todo.pop()
        for f in gens:
            U=tuple(sorted(f(c) for c in T))
            if U not in seen: seen.add(U); todo.append(U)
    return seen
done=set()
if __name__=='__main__':
    reps=[]
    for S in itertools.combinations(range(13),4):
        if S in done: continue
        o=orbit(S); done|=o; reps.append((S,len(o)))
    print(TY,len(reps),'orbits total',sum(n for _,n in reps))
    open('repsh_%s.txt'%TY,'w').write('\n'.join(','.join(map(str,S))+' %d'%n for S,n in reps)+'\n')
