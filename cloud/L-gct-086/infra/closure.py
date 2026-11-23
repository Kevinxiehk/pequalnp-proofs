import sys,os,re
root='/home/claude/pequalnp-proofs/lean'
def deps(mod,seen):
    if mod in seen or not mod.startswith('PEqualNP'): return
    p=os.path.join(root,*mod.split('.'))+'.lean'
    if not os.path.exists(p): return
    seen[mod]=p
    for line in open(p,encoding='utf-8'):
        m=re.match(r'^import\s+(\S+)',line)
        if m: deps(m.group(1),seen)
for mod in sys.argv[1:]:
    seen={}; deps(mod,seen)
    tot=0; parts=[]
    for k,p in seen.items():
        if k in ('PEqualNP.Defs',) or k.startswith('PEqualNP.Defs.'): continue
        n=sum(1 for _ in open(p,encoding='utf-8')); b=os.path.getsize(p); tot+=b; parts.append((k.replace('PEqualNP.',''),n))
    print(mod.replace('PEqualNP.',''),'closure bytes(excl Defs)=',tot,'files=',len(parts),'::',' '.join(f'{a}:{b}' for a,b in parts))
