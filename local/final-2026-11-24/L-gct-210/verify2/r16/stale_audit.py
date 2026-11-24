# verify2 r16: after-the-fact audit for E-STALE-OUTPUT. For every msolve input X.ms (or X) with an output among
# X.gb, X.ms.gb, X.out, X.ms.out, stem.gb, stem.out: genuine iff mtime(out) >= mtime(in). Output older than input = the last
# msolve call on this input wrote nothing -> any verdict read then was STALE (or a FAILED that a careful driver caught).
import os, sys, collections
root=sys.argv[1]; rep=collections.defaultdict(lambda: [0,0,0,[]])
def verdict(f):
    try: s=open(f,errors='replace').read()
    except Exception: return '?'
    body=''.join(l for l in s.splitlines() if not l.startswith('#')).replace(' ','')
    return 'UNIT' if body.strip().rstrip(':') in ('[1]','[1]:') else ('EMPTY' if not body.strip() else 'NON')
for d,_,fs in os.walk(root):
    S=set(fs)
    for f in fs:
        if not f.endswith('.ms'): continue
        stem=f[:-3]; inp=os.path.join(d,f)
        outs=[o for o in (f+'.gb',f+'.out',stem+'.gb',stem+'.out',stem+'.res') if o in S]
        r=rep[d]
        if not outs: continue
        for o in outs:
            op=os.path.join(d,o)
            if os.path.getmtime(op)+1e-6>=os.path.getmtime(inp): r[0]+=1
            else: r[1]+=1; r[3].append((o,verdict(op)))
for d in sorted(rep):
    g,s,_,L=rep[d]
    if g+s==0: continue
    print('%-70s genuine %5d  OLDER-THAN-INPUT %4d'%(d.replace('/home/kevxhk/work/L-gct-210/',''),g,s))
    for o,v in L[:6]: print('      stale-suspect',o,v)
