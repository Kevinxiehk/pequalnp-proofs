import itertools
G=[(a,b) for a in range(1,5) for b in range(1,5)]
idx={g:i for i,g in enumerate(G)}
def neg(g): return ((-g[0])%5,(-g[1])%5)
def add(g,h): return ((g[0]+h[0])%5,(g[1]+h[1])%5)
best={}
for k in [2,3,4]:  # forbid zero sums of length 2..k (with repetition) -> P2..Pk vanish? (power sums only)
    pass
# condition: E subset Gamma, no zero sum of j elements of E (with repetition) for j in J
def ok(E, J):
    for j in J:
        for c in itertools.combinations_with_replacement(E, j):
            s=(0,0)
            for g in c: s=add(s,g)
            if s==(0,0): return False
    return True
for J in [(2,),(2,3),(2,3,4),(2,3,4,5)]:
    m=0; ex=None
    for r in range(1,9):
        found=False
        for E in itertools.combinations(G,r):
            if ok(E,J): found=True; ex=E; break
        if found: m=r; bex=ex
        else: break
    print('forbid zero sums of lengths',J,': max |E| =',m,' e.g.',bex)
