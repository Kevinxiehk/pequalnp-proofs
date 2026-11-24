# Dump the (FO-r) incidence ideal of an r9_direct.py script with Singular, then eliminate the t's with msolve (-e) [NOTES R11-5].
# usage: r11_elim_msolve.py SCRIPT.sing CHAR   (CHAR = prime or 0)
import sys, os, subprocess, re
f,ch=sys.argv[1],sys.argv[2]; b=os.path.basename(f)[:-5]; d='/tmp/st2_el2_'+b; os.makedirs(d,exist_ok=True)
src=open(f).read().split('\n'); out=[]
for l in src:
    if l.startswith('int t=timer; ideal G=std(I);'):
        out.append('string vs=varstr(basering); write(":w %s/ideal.txt", vs); write(":a %s/ideal.txt", I); quit;'%(d,d)); break
    out.append(l)
open(d+'/dump.sing','w').write('\n'.join(out)+'\n')
subprocess.run('ulimit -v 2000000; timeout 300 Singular -q %s/dump.sing < /dev/null > %s/dump.log 2>&1'%(d,d),shell=True)
txt=open(d+'/ideal.txt').read().strip().split('\n'); vs=txt[0].split(',')
polys=[p.strip() for p in ' '.join(txt[1:]).split(',') if p.strip() and p.strip()!='0']
body=' '.join(polys); vs=[v for v in vs if re.search(r'\b%s\b'%re.escape(v),body)]
tv=[v for v in vs if v.startswith('t')]; pv=[v for v in vs if not v.startswith('t')]
open(d+'/in.ms','w').write(','.join(tv+pv)+'\n'+ch+'\n'+',\n'.join(polys)+'\n')
subprocess.run('ulimit -v 2000000; timeout 900 msolve -e %d -g 2 -t 1 -f %s/in.ms -o %s/out.txt > %s/log.txt 2>&1'%(len(tv),d,d,d),shell=True)
res=[l for l in open(d+'/out.txt').read().splitlines() if not l.startswith('#')] if os.path.exists(d+'/out.txt') else ['NO OUTPUT']
gb=' '.join(res).replace('[','').replace(']:','')
elim=[g.strip() for g in gb.split(',') if g.strip() and not re.search(r'\bt\d',g)]
print('ELIM %s char %s (params %s): %s'%(b,ch,pv,elim[:12]),flush=True)
