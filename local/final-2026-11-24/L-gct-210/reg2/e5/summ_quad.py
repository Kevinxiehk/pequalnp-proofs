# Round 18: summarise r18_e5_quad.log (stage2q sweep): counts of classes by verdict; for survivors: genuine type, line counts on the pair,
# free column (b_c = 3 -> stage3 LEMMA PFC), 3-dim row part (a_i = 3).
import re, sys, collections
f=sys.argv[1] if len(sys.argv)>1 else '/home/kevxhk/work/L-gct-210/reg2/evidence/logs/r18_e5_quad.log'
tot=collections.Counter(); surv=[]
for line in open(f):
    if not line.startswith('TYPE'): continue
    m0=re.match(r'TYPE (\d+)\|(\d+) (row|col)\((\d),(\d)\) (\w+):(.*)$',line.strip())
    a,b,k,p,q,g,rest=m0.groups(); A=[int(c) for c in a]; B=[int(c) for c in b]; p=int(p); q=int(q)
    if 'classes' not in rest: tot[rest.strip()]+=1; continue
    for part in rest.split('->')[1].split('; '):
        key,n=part.strip().rsplit(' x',1); n=int(n)
        if key.startswith('kernel dims'):
            ks=eval(key[len('kernel dims '):])
            gen=any(isinstance(t,tuple) and t[0]=='Q' and t[2]!='gen0' for t in ks)
            other=[t for t in ks if not (isinstance(t,tuple) and t[0] in ('Q','Q0','Qs0'))]
            if gen or other: surv.append((a,b,k,p,q,g,n,ks)); tot['SURVIVE(gen or ?)']+=n
            else: tot['QUAD-KILL(per comp)']+=n
        else: tot[key]+=n
print('class counts:',dict(tot))
c=collections.Counter()
for (a,b,k,p,q,g,n,ks) in surv:
    A=[int(x) for x in a]; B=[int(x) for x in b]
    pair=(A[p],A[q]) if k=='row' else (B[p],B[q])
    pfc=3 in B
    c[(g,k,tuple(sorted(pair)),'PFC' if pfc else ('a3' if 3 in A else '-'))]+=n
for key,v in sorted(c.items()): print(key,v)
print('survivor types:')
for s in surv: print(' ',s[:7],[t for t in s[7]][:3])
