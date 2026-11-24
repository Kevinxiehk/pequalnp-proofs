# Round 18: ONE resumable batch driver for the exact e = 5 stage 2 (big slot).  Items = the 194 types that still have classes after stage 1
# (from the stage-1 log).  For each type twostage.py runs the FULL stage 2 on every surviving class (per-class Singular timeout TMO), with
# RETRY_TIMEOUTS=1 so the 74 stage-1 timeouts are retried with the long timeout.  One verdict line per type is appended to OUT; types already
# in OUT are skipped (resumable).   usage: batch_e5.py STAGE1_LOG OUT TMO
import sys, re, os, subprocess
log,outf,tmo=sys.argv[1],sys.argv[2],int(sys.argv[3])
# round 19: optional 4th argument = an earlier batch output; then only the types whose verdict there contains NONEMPTY / TIMEOUT / ERR are
# rerun, with the exact RANK-ONE SPLIT (RANK1SPLIT=1: per component 'NR1-...' = non-rank-one part, 'R1P-...' = rank-one part).
prev=sys.argv[4] if len(sys.argv)>4 else None
items=[]
for line in open(log):
    if not line.startswith('TYPE') or 'classes' not in line: continue
    if 'LINES(' not in line and 'TIMEOUT-1' not in line: continue
    m0=re.match(r'TYPE (\d+)\|(\d+) (row|col)\((\d),(\d)\) (\w+):',line.strip()); items.append(m0.groups())
done=set()
if os.path.exists(outf):
    for l in open(outf):
        if l.startswith('TYPE '): done.add(l.split(':')[0])
env=dict(os.environ); env['RETRY_TIMEOUTS']='1'
if prev:
    env['RANK1SPLIT']='1'; keep=set()
    for l in open(prev):
        if l.startswith('TYPE ') and any(w in l for w in ('NONEMPTY','TIMEOUT','ERR')): keep.add(l.split(':')[0])
    items=[it for it in items if ('TYPE %s|%s %s(%s,%s) %s'%it) in keep]
for (a,b,k,p,q,g) in items:
    tag='TYPE %s|%s %s(%s,%s) %s'%(a,b,k,p,q,g)
    if tag in done: continue
    try:
        r=subprocess.run(['python3','-I','/home/kevxhk/work/L-gct-210/reg2/e5/twostage.py',a,b,k,p,q,g,str(tmo)],capture_output=True,text=True,timeout=tmo*60,env=env)
        v=(r.stdout.strip().split('\n')[-1] if r.stdout.strip() else tag+': ERR '+r.stderr[-200:])
    except subprocess.TimeoutExpired: v=tag+': TYPE-TIMEOUT'
    open(outf,'a').write(v+'\n')
open(outf,'a').write('BATCH DONE\n')
