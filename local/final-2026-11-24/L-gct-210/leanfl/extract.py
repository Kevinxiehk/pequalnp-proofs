import sys,re
# usage: extract.py partfile name1 name2 ... ; prints the named top-level blocks in file order
f=sys.argv[1]; names=set(sys.argv[2:])
lines=open(f).read().split('\n')
blocks=[];cur=None
for l in lines:
    m=re.match(r'^(theorem|def|lemma) (\S+)',l)
    if m or l.startswith('set_option'):
        if cur is not None and cur[0] is not None: blocks.append(cur)
        if l.startswith('set_option'):
            cur=[None,[l]]; pend=True; continue
        if cur is not None and cur[0] is None: cur=[m.group(2),cur[1]+[l]]
        else: cur=[m.group(2),[l]]
    elif cur is not None: cur[1].append(l)
if cur is not None and cur[0] is not None: blocks.append(cur)
found=set()
for n,b in blocks:
    if n in names:
        found.add(n); print('\n'.join(b).rstrip()+'\n')
missing=names-found
if missing: sys.stderr.write('MISSING '+' '.join(sorted(missing))+'\n'); sys.exit(1)
