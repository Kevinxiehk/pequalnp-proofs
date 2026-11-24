import sys,re
# usage: locate2.py LEANFILE LOGFILE : prints enclosing declaration name and relative line for each error
src=open(sys.argv[1]).read().split('\n')
decl=[None]*(len(src)+2); cur=('?',0)
for i,l in enumerate(src,1):
    m=re.match(r'^(theorem|def|abbrev) (\S+)',l)
    if m: cur=(m.group(2),i)
    decl[i]=cur
seen=0
for l in open(sys.argv[2]):
    m=re.search(r'check\.lean:(\d+):(\d+): error: (.*)',l)
    if m:
        ln=int(m.group(1)); n,s=decl[ln]
        print(f'{n} (+{ln-s}) [line {ln}]: {m.group(3)[:150]}')
