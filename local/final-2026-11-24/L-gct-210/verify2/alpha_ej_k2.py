# verify2: MIN-C (alpha), v_0 = e_j, sub-case k <= 2 (all five vectors pi_i in C^4 are "loops" e_m or "edges" with 2 nonzero entries).
# CLAIM: all ten triple products zero + NZ (supports cover the 4 columns) + NT (no three equal loops) is impossible.
# Exact combinatorial filter: a coefficient (triple, 3-set S) that is a single monomial cannot vanish. For the surviving support patterns
# print the remaining equations (sums of monomials in the edge ratios) for inspection / exact solution.
import itertools
cols=range(4); perms4=list(itertools.permutations(cols))
types=[1<<j for j in cols]+[(1<<j)|(1<<l) for j,l in itertools.combinations(cols,2)]
def pm(mask,p): return sum(1<<p[j] for j in cols if mask>>j&1)
pats=set()
for t in itertools.combinations_with_replacement(types,5):
    pats.add(min(tuple(sorted(pm(m,p) for m in t)) for p in perms4))
pats=sorted(pats)
triples=list(itertools.combinations(range(5),3)); S3=list(itertools.combinations(cols,3)); P3=list(itertools.permutations(range(3)))
def name(m): return ''.join(str(j) for j in cols if m>>j&1)
stat={'patterns up to column perms':len(pats),'NZ fails':0,'NT fails':0,'killed by a single-monomial coefficient':0,'survive the monomial filter':0}
surv=[]
for pat in pats:
    u=0
    for m in pat: u|=m
    if u!=15: stat['NZ fails']+=1; continue
    if any(pat.count(1<<j)>=3 for j in cols): stat['NT fails']+=1; continue
    eqs=[]
    for tr in triples:
        for S in S3:
            ms=[tuple((tr[i],S[p[i]]) for i in range(3)) for p in P3 if all(pat[tr[i]]>>S[p[i]]&1 for i in range(3))]
            if ms: eqs.append((tr,S,ms))
    if any(len(e[2])==1 for e in eqs): stat['killed by a single-monomial coefficient']+=1; continue
    stat['survive the monomial filter']+=1; surv.append((pat,eqs))
for k,v in stat.items(): print('%-45s %d'%(k,v))
# Exact treatment of survivors: write edge i as (1 at its smaller column, r_i at its larger column), loops as 1. Each equation is a sum of
# monomials in the r_i. Collect the distinct equations as frozensets of exponent tuples.
for pat,eqs in surv:
    edges=[i for i in range(5) if bin(pat[i]).count('1')==2]
    E=set()
    for tr,S,ms in eqs:
        poly=[]
        for mono in ms:
            ex=[0]*5
            for (i,j) in mono:
                if i in edges and j==max(c for c in cols if pat[i]>>c&1): ex[i]=1
            poly.append(tuple(ex))
        E.add(tuple(sorted(poly)))
    print('pattern',[name(m) for m in pat],' distinct equations (exponent vectors of r_0..r_4, summed):')
    for poly in sorted(E): print('     ',' + '.join('*'.join('r%d'%i for i in range(5) if ex[i]) or '1' for ex in poly),'= 0')
