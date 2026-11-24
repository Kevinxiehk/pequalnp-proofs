import sys,re
# usage: closure.py DIR "prefix parts" "target parts" out ; pre.part is copied whole, then the needed blocks of the prefix
# parts (in order), then the target parts whole, then test.tail
D,pref,targ,out=sys.argv[1],sys.argv[2].split(),sys.argv[3].split(),sys.argv[4]
def blocks(text):
    res=[];cur=None;pend=[]
    for l in text.split('\n'):
        m=re.match(r'^(theorem|def|lemma|abbrev) (\S+)',l)
        if l.startswith('set_option'):
            pend.append(l); continue
        if m:
            if cur: res.append(cur)
            cur=[m.group(2),pend+[l]]; pend=[]
        elif cur is not None: cur[1].append(l)
        else: pend.append(l)
    if cur: res.append(cur)
    return res
tok=re.compile(r"[A-Za-z_][A-Za-z0-9_'₀-₉]*")
allb=[]
for p in pref:
    for n,b in blocks(open(f'{D}/{p}.part').read()): allb.append((p,n,'\n'.join(b)))
defined={n for _,n,_ in allb}
need=set()
tgt_text=''.join(open(f'{D}/{p}.part').read() for p in targ)
work=[t for t in tok.findall(tgt_text) if t in defined]
bodies={n:b for _,n,b in allb}
while work:
    t=work.pop()
    if t in need: continue
    need.add(t)
    work.extend(x for x in tok.findall(bodies[t]) if x in defined and x not in need)
with open(out,'w') as f:
    f.write(open(f'{D}/pre.part').read())
    for p,n,b in allb:
        if p!='pre' and n in need: f.write(b.rstrip()+'\n\n')
    for p in targ: f.write(open(f'{D}/{p}.part').read())
    f.write(open(f'{D}/test.tail').read())
print(len(need),'blocks needed')
