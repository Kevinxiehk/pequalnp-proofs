# verify2 round 4: stage3's Lemma 5V (five nonzero vectors in C^4, all ten triple products zero in (A_N)_3  =>  three of them are
# multiples of one unit vector, or all five lie in a coordinate 2-plane).  Exact support-pattern filter; survivors are listed.
import itertools
cols=range(4); perms4=list(itertools.permutations(cols))
def pm(mask,p): return sum(1<<p[j] for j in cols if mask>>j&1)
pats=set()
for t in itertools.combinations_with_replacement(range(1,16),5):
    pats.add(min(tuple(sorted(pm(m,p) for m in t)) for p in perms4))
pats=sorted(pats)
triples=list(itertools.combinations(range(5),3)); S3=list(itertools.combinations(cols,3)); P3=list(itertools.permutations(range(3)))
def name(m): return ''.join(str(j) for j in cols if m>>j&1)
stat={'patterns up to column permutations':len(pats),'conclusion holds: all in two columns':0,'conclusion holds: three equal unit supports':0,
      'killed: some coefficient has exactly one monomial':0,'survive the monomial filter':0}
surv=[]
for pat in pats:
    u=0
    for m in pat: u|=m
    if bin(u).count('1')<=2: stat['conclusion holds: all in two columns']+=1; continue
    if any(pat.count(1<<j)>=3 for j in cols): stat['conclusion holds: three equal unit supports']+=1; continue
    bad=False
    for tr in triples:
        for S in S3:
            c=sum(1 for p in P3 if all(pat[tr[i]]>>S[p[i]]&1 for i in range(3)))
            if c==1: bad=True; break
        if bad: break
    if bad: stat['killed: some coefficient has exactly one monomial']+=1; continue
    stat['survive the monomial filter']+=1; surv.append(pat)
for k,v in stat.items(): print('%-55s %d'%(k,v))
for p in surv: print('  ',[name(m) for m in p])
import pickle; pickle.dump(surv,open('/home/kevxhk/work/L-gct-210/verify2/lemma5v_surv.pkl','wb'))
