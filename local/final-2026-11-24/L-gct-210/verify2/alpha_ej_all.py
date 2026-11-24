# verify2: MIN-C (alpha), v_0 = e_j, ALL support patterns (five nonzero vectors in C^4): exact monomial filter, then count survivors.
import itertools, sys, pickle
cols=range(4); perms4=list(itertools.permutations(cols))
def pm(mask,p): return sum(1<<p[j] for j in cols if mask>>j&1)
pats=set()
for t in itertools.combinations_with_replacement(range(1,16),5):
    pats.add(min(tuple(sorted(pm(m,p) for m in t)) for p in perms4))
pats=sorted(pats)
triples=list(itertools.combinations(range(5),3)); S3=list(itertools.combinations(cols,3)); P3=list(itertools.permutations(range(3)))
def name(m): return ''.join(str(j) for j in cols if m>>j&1)
stat={'patterns up to column perms':len(pats),'NZ fails':0,'NT fails':0,'killed by a single-monomial coefficient':0,'survive':0}
surv=[]; bymax={}
for pat in pats:
    u=0
    for m in pat: u|=m
    if u!=15: stat['NZ fails']+=1; continue
    if any(pat.count(1<<j)>=3 for j in cols): stat['NT fails']+=1; continue
    bad=False
    for tr in triples:
        for S in S3:
            c=sum(1 for p in P3 if all(pat[tr[i]]>>S[p[i]]&1 for i in range(3)))
            if c==1: bad=True; break
        if bad: break
    if bad: stat['killed by a single-monomial coefficient']+=1; continue
    stat['survive']+=1; surv.append(pat); k=max(bin(m).count('1') for m in pat); bymax[k]=bymax.get(k,0)+1
for k,v in stat.items(): print('%-45s %d'%(k,v))
print('survivors by max support size k:',bymax)
pickle.dump(surv,open('/home/kevxhk/work/L-gct-210/verify2/alpha_surv.pkl','wb'))
for p in surv[:40]: print('  ',[name(m) for m in p])
