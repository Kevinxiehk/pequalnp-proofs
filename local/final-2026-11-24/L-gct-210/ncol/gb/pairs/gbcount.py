# number of standard monomials (= degree of a 0-dim ideal, with multiplicity) from a msolve grevlex GB file
import sys, re
def leads(fn):
    txt=open(fn).read().split('#---')[-1].strip().lstrip('[').rstrip(':').rstrip(']')
    L=[]
    for p in txt.split(',\n'):
        p=p.strip()
        if not p: continue
        lt=p.split('+')[0]
        e=[0]*12
        for v,k in re.findall(r't(\d+)\^(\d+)',lt): e[int(v)]+=int(k)
        L.append(tuple(e))
    return L
def count(L,n=12,cap=200000):
    # count monomials not divisible by any leading monomial (BFS over exponent vectors)
    from collections import deque
    seen=set([tuple([0]*n)]); q=deque(seen); c=0
    def divisible(m): return any(all(m[i]>=l[i] for i in range(n)) for l in L)
    while q:
        m=q.popleft()
        if divisible(m): continue
        c+=1
        if c>cap: return None
        for i in range(n):
            m2=list(m); m2[i]+=1; m2=tuple(m2)
            if m2 not in seen: seen.add(m2); q.append(m2)
    return c
for fn in sys.argv[1:]:
    L=leads(fn); print(fn,'standard monomials:',count(L))
