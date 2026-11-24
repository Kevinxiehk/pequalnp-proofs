# orbit representatives of 3-subsets of the 10 coordinates (a_0..a_3 = 0..3, b_0..b_3 = 4..7, w2 = 8, w3 = 9) under
# S4 (columns: j -> s(j) on a and b) x Z2 (rows 2<->3: a_j <-> b_j and w2 <-> w3)
import itertools, sys
d=int(sys.argv[1]) if len(sys.argv)>1 else 3
def act(sig,flip,c):
    if c<4: c2=sig[c]; return c2+4 if flip else c2
    if c<8: c2=sig[c-4]; return c2 if flip else c2+4
    return {8:9,9:8}[c] if flip else c
seen=set(); reps=[]
for S in itertools.combinations(range(10),d):
    if S in seen: continue
    orb={tuple(sorted(act(sig,fl,c) for c in S)) for sig in itertools.permutations(range(4)) for fl in (0,1)}
    seen|=orb; reps.append((S,len(orb)))
print(len(reps),'orbits; sizes sum',sum(o for _,o in reps))
for S,o in reps: print(''.join(str(c) for c in S),o)
