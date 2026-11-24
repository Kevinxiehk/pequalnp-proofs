# orbits of 4-subsets of the 13 H-coordinates (0 sg0, 1 sg3, 2 sg4, 3..7 a_0..a_4, 8..12 b_0..b_4) under S3 (cols 0,1,2) x S2 (cols 3,4) x Z2 (a<->b)
import itertools
def col(perm3,sw):
    def f(c):
        if c==0: return 0
        if c in (1,2): return (3-c) if sw else c
        base=3 if c<8 else 8; j=c-base
        if j<3: j=perm3[j]
        else: j=(7-j) if sw else j
        return base+j
    return f
def ab(c): return c+5 if 3<=c<=7 else (c-5 if c>=8 else c)
G=[col(p,sw) for p in itertools.permutations(range(3)) for sw in (0,1)]
def orbit(S):
    out=set()
    for f in G:
        T=tuple(sorted(f(c) for c in S)); out.add(T); out.add(tuple(sorted(ab(c) for c in T)))
    return out
done=set()
if __name__=='__main__':
    reps=[]
    for S in itertools.combinations(range(13),4):
        if S in done: continue
        o=orbit(S); done|=o; reps.append((S,len(o)))
    print(len(reps),'orbits total',sum(n for _,n in reps))
    open('repsh.txt','w').write('\n'.join(','.join(map(str,S))+' %d'%n for S,n in reps)+'\n')
