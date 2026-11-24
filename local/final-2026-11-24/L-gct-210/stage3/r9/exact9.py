# Round 9: EXACT (char 0) version of gen9.py: same systems with integer coefficients (recovered through the modulus 2^127-1,
# |coeff| < 10^9 asserted), Singular std over Q, one chart per ring; results printed per chart as they come.
# usage: python3 -I exact9.py CASE MODE RAB ND [CHUNK_INDEX NCHUNKS]
import sys, subprocess, time
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r9'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/gb')
import gen9
BIG=(1<<127)-1
case,mode,rab,nd=sys.argv[1],sys.argv[2],int(sys.argv[3]),int(sys.argv[4])
ci,nc=(int(sys.argv[5]),int(sys.argv[6])) if len(sys.argv)>6 else (0,1)
def sgn(v): return v if v<=BIG//2 else v-BIG
def tostr(f,names):
    ts=[]
    for k,v in sorted(f.items(),reverse=True):
        c=sgn(v); assert abs(c)<10**9
        m='*'.join('%s^%d'%(names[i],e) for i,e in enumerate(k) if e)
        ts.append('(%d)%s'%(c,'*'+m if m else ''))
    return '+'.join(ts)
chs=gen9.charts(case,nd)[ci::nc]; lines=[]
for n,ch in enumerate(chs):
    names,eqs,use,nlev=gen9.build(case,ch,BIG,mode,rab,nd)
    tag=''.join(map(str,ch))
    lines.append('ring r%d=0,(%s),dp;'%(n,','.join(names[i] for i in use)))
    lines.append('ideal I='+',\n'.join(tostr(e,names) for e in eqs)+';')
    lines.append('ideal Gb=std(I);')
    lines.append('if (size(Gb)==1 and Gb[1]==1) {"CHART %s UNIT";} else {"CHART %s NONUNIT size",size(Gb),"dim",dim(Gb);}'%(tag,tag))
    lines.append('kill r%d;'%n)
lines.append('quit;')
fn='/home/kevxhk/work/L-gct-210/stage3/r9/gb/ex_%s_%s_r%d_n%d_%d.sing'%(case,mode,rab,nd,ci)
open(fn,'w').write('\n'.join(lines)+'\n')
t0=time.time()
out=open(fn+'.out','w')
subprocess.run(['/usr/bin/Singular','-q',fn],stdout=out,stderr=subprocess.STDOUT,timeout=1700)
out.close(); txt=open(fn+'.out').read(); ls=[l for l in txt.splitlines() if l.startswith('CHART')]
nu=sum(1 for l in ls if l.endswith('UNIT') and 'NONUNIT' not in l)
print('EXACT case',case,'mode',mode,'rab',rab,'nd',nd,'chunk %d/%d'%(ci,nc),': charts',len(chs),'answered',len(ls),'UNIT',nu,'NONUNIT',len(ls)-nu,'time %.1f s'%(time.time()-t0),flush=True)
for l in ls:
    if 'NONUNIT' in l: print(l)
