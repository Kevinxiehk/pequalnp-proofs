# Round 9: per-chart exact runs (Singular std over Q, one process per chart, timeout per chart). Skips charts already recorded.
# usage: python3 -I exact9c.py CASE MODE RAB ND TIMEOUT [ALG]   ALG = std (default) | modstd
import sys, subprocess, time, os
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r9'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/gb')
import gen9
BIG=(1<<127)-1
case,mode,rab,nd,TO=sys.argv[1],sys.argv[2],int(sys.argv[3]),int(sys.argv[4]),int(sys.argv[5]); alg=sys.argv[6] if len(sys.argv)>6 else 'std'; strat=int(sys.argv[7]) if len(sys.argv)>7 else 0
def sgn(v): return v if v<=BIG//2 else v-BIG
def tostr(f,names):
    ts=[]
    for k,v in sorted(f.items(),reverse=True):
        c=sgn(v); assert abs(c)<10**9
        m='*'.join('%s^%d'%(names[i],e) for i,e in enumerate(k) if e)
        ts.append('(%d)%s'%(c,'*'+m if m else ''))
    return '+'.join(ts)
rec='/home/kevxhk/work/L-gct-210/stage3/r9/exact_%s_%s_r%d_n%d.txt'%(case,mode,rab,nd)
done={}
if os.path.exists(rec):
    for l in open(rec):
        t=l.split(); done[t[0]]=t[1]
for l in open('/home/kevxhk/work/L-gct-210/stage3/r9/gb/ex_%s_%s_r%d_n%d_0.sing.out'%(case,mode,rab,nd)) if os.path.exists('/home/kevxhk/work/L-gct-210/stage3/r9/gb/ex_%s_%s_r%d_n%d_0.sing.out'%(case,mode,rab,nd)) else []:
    if l.startswith('CHART') and l.split()[2]=='UNIT' and l.split()[1] not in done:
        done[l.split()[1]]='UNIT'; open(rec,'a').write('%s UNIT std(batch)\n'%l.split()[1])
t0=time.time()
for ch in gen9.charts(case,nd):
    tag=''.join(map(str,ch))
    if done.get(tag)=='UNIT': continue
    if strat and done.get(tag)!='TIMEOUT': continue      # strat pass: only the charts that timed out
    names,eqs,use,nlev=gen9.build(case,ch,BIG,mode,rab,nd,strat)
    body=['ring r=0,(%s),dp;'%(','.join(names[i] for i in use)),'ideal I='+',\n'.join(tostr(e,names) for e in eqs)+';']
    if alg=='modstd': body+=['LIB "modstd.lib";','ideal Gb=modStd(I);']
    else: body+=['ideal Gb=std(I);']
    body+=['if (size(Gb)==1 and Gb[1]==1) {"RES UNIT";} else {"RES NONUNIT",size(Gb),dim(Gb);}','quit;']
    fn='/home/kevxhk/work/L-gct-210/stage3/r9/gb/exc_%s_%s_%s.sing'%(case,mode,tag); open(fn,'w').write('\n'.join(body)+'\n')
    t1=time.time()
    try:
        out=subprocess.run(['/usr/bin/Singular','-q',fn],capture_output=True,text=True,timeout=TO).stdout
        r=[l for l in out.splitlines() if l.startswith('RES')]; r=r[0].split()[1] if r else 'ERROR'
    except subprocess.TimeoutExpired: r='TIMEOUT'
    open(rec,'a').write('%s %s %s%s %.1fs\n'%(tag,r,alg,'-strat' if strat else '',time.time()-t1)); done[tag]=r
    print(tag,r,'%.1f s'%(time.time()-t1),flush=True)
vals=[done.get(''.join(map(str,ch)),'?') for ch in gen9.charts(case,nd)]
print('EXACT %s %s rab %d nd %d: charts %d UNIT %d NONUNIT %d TIMEOUT %d other %d (%.0f s)'%(case,mode,rab,nd,len(vals),vals.count('UNIT'),vals.count('NONUNIT'),vals.count('TIMEOUT'),len(vals)-vals.count('UNIT')-vals.count('NONUNIT')-vals.count('TIMEOUT'),time.time()-t0),flush=True)
