# verify2: MIN-E (b-alpha), v_0 = e_j: five nonzero vectors pi_1..pi_5 in C^3 with ALL ten 3x3 permanents of triples = 0, supports covering
# the 3 columns, no three proportional to the same unit vector (NT).  Claim: impossible.  Exact monomial filter over support patterns.
import itertools
cols=range(3); perms=list(itertools.permutations(cols))
def pm(mask,p): return sum(1<<p[j] for j in cols if mask>>j&1)
pats=set()
for t in itertools.combinations_with_replacement(range(1,8),5):
    pats.add(min(tuple(sorted(pm(m,p) for m in t)) for p in perms))
pats=sorted(pats); triples=list(itertools.combinations(range(5),3))
def name(m): return ''.join(str(j) for j in cols if m>>j&1)
stat={'patterns up to column perms':len(pats),'cover fails':0,'NT fails':0,'killed by a single-monomial permanent':0,'survive':0}; surv=[]
for pat in pats:
    u=0
    for m in pat: u|=m
    if u!=7: stat['cover fails']+=1; continue
    if any(pat.count(1<<j)>=3 for j in cols): stat['NT fails']+=1; continue
    cnt=[sum(1 for p in perms if all(pat[tr[i]]>>p[i]&1 for i in range(3))) for tr in triples]
    if 1 in cnt: stat['killed by a single-monomial permanent']+=1; continue
    stat['survive']+=1; surv.append(pat)
for k,v in stat.items(): print('%-42s %d'%(k,v))
for p in surv: print('  survivor:',[name(m) for m in p])
