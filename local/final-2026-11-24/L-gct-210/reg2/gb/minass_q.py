# minimal associated primes (over Q) of the elimination ideals in /tmp/dr211q/*_om_*.qout ; groups identical answers
import glob, subprocess, sys
res={}
for fn in sorted(glob.glob(sys.argv[1])):
    s=open(fn).read().split('FACTORS')[0].strip().rstrip(',')
    if not s: res.setdefault('EMPTY OUTPUT',[]).append(fn); continue
    names='b1,b2,b3,c1,c2,c3' if '/g_' in fn else 'b1,b2,b3'
    sc='LIB "primdec.lib";\nring R=0,(%s),dp;\nideal J=%s;\nif(J[1]==1){print("UNIT");}else{list L=minAssGTZ(J);int i; for(i=1;i<=size(L);i++){print("COMP");print(L[i]);}}\nquit;\n'%(names,s)
    open('/tmp/mq.sing','w').write(sc); r=subprocess.run(['/usr/bin/Singular','-q'],stdin=open('/tmp/mq.sing'),capture_output=True,text=True,timeout=300)
    key=' | '.join(' '.join(c.split()) for c in r.stdout.split('COMP')[1:]) or r.stdout.strip()[:200]
    res.setdefault(key,[]).append(fn.split('/')[-1])
for k,v in res.items(): print(len(v),'files:',' '.join(x.replace('.qout','') for x in v)); print('    ',k)
