import sys,re,collections
# usage: prof.py LOG : aggregates Lean profiler lines "<what> took <t>(ms|s)"
agg=collections.Counter(); cnt=collections.Counter(); big=[]
pos=None
for l in open(sys.argv[1],errors='replace'):
    m=re.search(r'check\.lean:(\d+):\d+',l)
    if m: pos=int(m.group(1))
    m=re.search(r'(.+?) took ([\d.]+)(ms|s)\b',l)
    if m:
        what=m.group(1).strip(); t=float(m.group(2))*(0.001 if m.group(3)=='ms' else 1)
        what=re.sub(r'.*info: ','',what)
        key=re.sub(r'\s+of\s+.*','',what) if what.startswith('typeclass') else what
        agg[key]+=t; cnt[key]+=1
        big.append((t,what[:90],pos))
for k,v in agg.most_common(25): print(f'{v:9.1f}s  {cnt[k]:5d}  {k[:100]}')
print('--- largest single entries')
for t,w,p in sorted(big,reverse=True)[:25]: print(f'{t:8.1f}s line {p}: {w}')
print('--- cumulative section (if any)')
on=False
for l in open(sys.argv[1],errors='replace'):
    if 'cumulative profiling times' in l: on=True; print(l.rstrip()); continue
    if on:
        if l.startswith('\t') or l.startswith('  '): print(l.rstrip())
        else: on=False
