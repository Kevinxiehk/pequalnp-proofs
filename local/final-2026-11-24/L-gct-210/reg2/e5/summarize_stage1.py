import re, collections, sys
cnt=collections.Counter(); types=collections.Counter(); surv_types=0; tot_classes=0
for line in open(sys.argv[1]):
    if not line.startswith('TYPE'): continue
    if 'KILLED-P2' in line and 'classes' not in line: types['killed P2']+=1; continue
    m=re.search(r': (\d+) classes -> (.*)$',line)
    if not m: types['other']+=1; continue
    tot_classes+=int(m.group(1)); alive=False
    for part in m.group(2).split('; '):
        k,n=part.rsplit(' x',1); n=int(n); key=re.sub(r'\(\d+ comps,','(',k); cnt[key]+=n
        if k.startswith('LINES(') or k.startswith('TIMEOUT'): alive=True
    types['with surviving classes' if alive else 'all classes killed by stage 1']+=1
print('types:',dict(types)); print('classes total',tot_classes); [print('  %-30s %d'%(k,v)) for k,v in cnt.most_common()]
