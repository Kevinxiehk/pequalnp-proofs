# verify2 r8: (1) substitution control of stage3/r9/gen9.py with the exact core M_0 (free column = C1G with u_a = 0), mod p;
#             (2) exact reproduction (Singular std over Q) of the five eliminations of (M5'), scripts written to verify2/r8 only.
# usage: python3 -I f4b_repro.py subst | python3 -I f4b_repro.py exact CASE MODE RAB ND [TIMEOUT]
import sys, subprocess, time, os
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r9'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/gb')
import gen9, gbl as G
OUT='/home/kevxhk/work/L-gct-210/verify2/r8'
if sys.argv[1]=='subst':
    p=2147483629
    g=2
    while pow(g,(p-1)//3,p)==1: g+=1
    w=pow(g,(p-1)//3,p); w2=w*w%p
    ch=(0,1,1,1,1)      # iw=0, ia=1, ic=1, ib=1, id=1
    for mode in ('LEVEL','FULL'):
        names,eqs,use,nlev=gen9.build('C1G',ch,p,mode,0,1)
        val={}
        # u_a = 0; w = -(0,-1,-1,3,-1) = (0,1,1,-3,1): free coords w1 (index1), w2 (index2) (w0 is the chart = 1); p' = 0
        n=[0,1,w2,0,w]; npr=[0,1,w,0,w2]
        assign={'u0':0,'u1':0,'u2':0,'w1':1,'w2':(-3)%p,'pp1':0,'pp2':0}
        ga={i:n[i] for i in range(5)}; gb={i:(-n[i])%p for i in range(5)}; gc={i:npr[i] for i in range(5)}; gd={i:(-npr[i])%p for i in range(5)}
        for i in range(1,5):
            if i!=1: assign['ga%d'%i]=ga[i]; assign['gc%d'%i]=gc[i]
        for i in range(5): assign['gb%d'%i]=gb[i]; assign['gd%d'%i]=gd[i]
        assign['tnb']=pow(gb[1],p-2,p); assign['tnd']=pow(gd[1],p-2,p)
        pt=[assign.get(nm,0) for nm in names]
        missing=[nm for nm in names[7:] if nm not in assign]
        def ev(f):
            s=0
            for k,c in f.items():
                t=c
                for i,e in enumerate(k):
                    if e: t=t*pow(pt[i],e,p)%p
                s+=t
            return s%p
        nz=sum(1 for f in eqs if ev(f))
        print('C1G chart %s mode %s: %d polys (level %d), nonzero at M_0: %d   (missing assignments: %s)'%(ch,mode,len(eqs),nlev,nz,missing),flush=True)
    sys.exit()
case,mode,rab,nd=sys.argv[2],sys.argv[3],int(sys.argv[4]),int(sys.argv[5]); TO=int(sys.argv[6]) if len(sys.argv)>6 else 120
BIG=(1<<127)-1
def sgn(v): return v if v<=BIG//2 else v-BIG
def tostr(f,names):
    ts=[]
    for k,v in sorted(f.items(),reverse=True):
        c=sgn(v); assert abs(c)<10**9
        m='*'.join('%s^%d'%(names[i],e) for i,e in enumerate(k) if e)
        ts.append('(%d)%s'%(c,'*'+m if m else ''))
    return '+'.join(ts)
res={}; t0=time.time()
for ch in gen9.charts(case,nd):
    tag=''.join(map(str,ch)); r='?'
    for strat in (0,1):
        names,eqs,use,nlev=gen9.build(case,ch,BIG,mode,rab,nd,strat)
        body=['ring r=0,(%s),dp;'%(','.join(names[i] for i in use)),'ideal I='+',\n'.join(tostr(e,names) for e in eqs)+';','ideal Gb=std(I);',
              'if (size(Gb)==1 and Gb[1]==1) {"RES UNIT";} else {"RES NONUNIT",size(Gb),dim(Gb);}','quit;']
        fn='%s/sing/%s_%s_%s_s%d.sing'%(OUT,case,mode,tag,strat); os.makedirs(OUT+'/sing',exist_ok=True); open(fn,'w').write('\n'.join(body)+'\n')
        try:
            out=subprocess.run(['/usr/bin/Singular','-q',fn],capture_output=True,text=True,timeout=TO).stdout
            rr=[l for l in out.splitlines() if l.startswith('RES')]; r=rr[0].split()[1] if rr else 'ERROR'
        except subprocess.TimeoutExpired: r='TIMEOUT'
        if r!='TIMEOUT': break
    res[tag]=r+('(strat)' if strat else '')
    if not r.startswith('UNIT'): print(tag,res[tag],flush=True)
v=list(res.values())
print('EXACT %s %s rab %d nd %d: charts %d, UNIT %d (of which stratified %d), other %d, %.0f s'%(case,mode,rab,nd,len(v),sum(1 for x in v if x.startswith('UNIT')),sum(1 for x in v if x=='UNIT(strat)'),sum(1 for x in v if not x.startswith('UNIT')),time.time()-t0),flush=True)
