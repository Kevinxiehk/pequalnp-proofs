# staged driver for eqtA: partitions (nS,nF); KA = 0 x*-charts (I,J) with refinement (a unit chart (I',J') gives r_{I'J'} = 0 on all KA = 0 solutions);
# KA = 1 single system (with the KA = 0 refinement NOT used: different family).  Usage: python3 -I staged_eqtA.py P TO VMEM
import sys, subprocess
P,TO,VM=sys.argv[1],int(sys.argv[2]),int(sys.argv[3])
base='/home/kevxhk/work/L-gct-210/stage3/r22'
parts=[tuple(int(c) for c in p.split(',')) for p in sys.argv[4].split(';')]
log=open(base+'/staged_eqtA_%s.log'%P,'a')
def run(f):
    try:
        r=subprocess.run(['bash','-c','ulimit -v %d; Singular -q %s'%(VM,f)],capture_output=True,text=True,timeout=TO).stdout
        return 'UNIT' if 'unit 1' in r else ('NONUNIT' if 'unit 0' in r else 'ERR')
    except subprocess.TimeoutExpired: return 'TIMEOUT'
for nS,nF in parts:
    unit=set()
    for ps in range(3):
        prog=False
        for I in (0,1):
            for J in range(5):
                if (I,J) in unit: continue
                f=subprocess.run(['python3','-I',base+'/eqtA.py',str(nS),str(nF),'0','%d%d'%(I,J),P],capture_output=True,text=True).stdout.strip()
                extra=['r%d_%d'%u for u in unit if u!=(I,J)]
                if extra:
                    s=open(f).read(); s=s.replace('ring R=%s,'%P,'ideal EXTRA_R0=%s;\nC=C,EXTRA_R0;\nring R=%s,'%(','.join(extra),P),1); open(f,'w').write(s)
                v=run(f); log.write('nS=%d nF=%d ka=0 chart %d%d pass %d extra %d: %s\n'%(nS,nF,I,J,ps,len(extra),v)); log.flush()
                if v=='UNIT': unit.add((I,J)); prog=True
        if len(unit)==10 or not prog: break
    f=subprocess.run(['python3','-I',base+'/eqtA.py',str(nS),str(nF),'1','x',P],capture_output=True,text=True).stdout.strip()
    v=run(f); log.write('nS=%d nF=%d ka=1: %s\n'%(nS,nF,v)); log.write('nS=%d nF=%d SUMMARY ka=0 unit charts %d/10\n'%(nS,nF,len(unit))); log.flush()
