# Round 16: run inctype.py over ALL e = 5 types (pattern x genuine pair position x genuine type), canonical representatives.
import itertools, subprocess, sys, os
pats=set()
for a in itertools.product(range(4),repeat=4):
    for b in itertools.product(range(4),repeat=5):
        if sum(a)+sum(b)==5: pats.add((tuple(sorted(a,reverse=True)),tuple(sorted(b,reverse=True))))
jobs=[]
for (a,b) in sorted(pats):
    seen=set()
    for r,j in itertools.combinations(range(4),2):
        key=('row',tuple(sorted((a[r],a[j]))))
        if key in seen: continue
        seen.add(key)
        for g in ('R1','N'): jobs.append((a,b,'row',r,j,g))
    for c,dd in itertools.combinations(range(5),2):
        key=('col',tuple(sorted((b[c],b[dd]))))
        if key in seen: continue
        seen.add(key)
        for g in ('C1','N'): jobs.append((a,b,'col',c,dd,g))
print('types:',len(jobs),flush=True)
tmo=sys.argv[1] if len(sys.argv)>1 else '20'
for (a,b,k,p,q,g) in jobs:
    r=subprocess.run(['python3','-I','/home/kevxhk/work/L-gct-210/reg2/e5/stage2q.py',''.join(map(str,a)),''.join(map(str,b)),k,str(p),str(q),g],capture_output=True,text=True,timeout=3600)
    print(r.stdout.strip() if r.stdout.strip() else 'ERR '+r.stderr[-200:],flush=True)
