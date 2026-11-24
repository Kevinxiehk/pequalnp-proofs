# Round 8: EXACT (characteristic 0) version of fc_gen.py: the same systems with integer coefficients, Singular std over Q, all 81 charts.
# usage: python3 -I fc_exact.py MODE     (MODE as in fc_gen.py)
import sys, itertools, subprocess, time
MODE=sys.argv[1]; BIG=(1<<127)-1
sys.argv=['fc_gen.py',str(BIG),MODE]
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/gb'); import gbl as G, fc_gen as F
def sgn(v): return v if v<=BIG//2 else v-BIG
def tostr(f):
    ts=[]
    for k,v in sorted(f.items(),reverse=True):
        c=sgn(v); assert abs(c)<10**9, 'coefficient not small: modular wrap?'
        m='*'.join('%s^%d'%(F.names[i],e) for i,e in enumerate(k) if e)
        ts.append('(%d)%s'%(c,'*'+m if m else ''))
    return '+'.join(ts)
t0=time.time(); charts=list(itertools.product([0],range(3),range(3),range(3),range(3))); lines=[]
for n,ch in enumerate(charts):
    eqs,use,nlev=F.system(*ch); eqs=[e for e in eqs if e]
    lines.append('ring r%d=0,(%s),dp;'%(n,','.join(F.names[i] for i in use)))
    lines.append('ideal I='+',\n'.join(tostr(e) for e in eqs)+';')
    lines.append('ideal Gb=std(I);')
    lines.append('if (size(Gb)==1 and Gb[1]==1) {"CHART %s UNIT";} else {"CHART %s NONUNIT size",size(Gb),"dim",dim(Gb),"vdim",vdim(Gb);}'%(''.join(map(str,ch)),''.join(map(str,ch))))
lines.append('quit;')
open('fc_exact_%s.sing'%MODE,'w').write('\n'.join(lines)+'\n')
print('script written, %.1f s'%(time.time()-t0),flush=True)
out=subprocess.run(['/usr/bin/Singular','-q'],stdin=open('fc_exact_%s.sing'%MODE),capture_output=True,text=True,timeout=100).stdout
open('fc_exact_%s.out'%MODE,'w').write(out)
ls=[l for l in out.splitlines() if l.startswith('CHART')]
print('MODE',MODE,'charts answered',len(ls),' UNIT',sum(1 for l in ls if l.endswith('UNIT') and 'NONUNIT' not in l),' NONUNIT',sum(1 for l in ls if 'NONUNIT' in l),' total %.1f s'%(time.time()-t0))
for l in ls[:4]: print(l)
print([l for l in out.splitlines() if not l.startswith('CHART')][:5])
