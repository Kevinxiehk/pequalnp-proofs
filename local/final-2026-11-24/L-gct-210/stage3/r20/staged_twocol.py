# Round 20: STAGED TWOCOL driver (exact over Q by default). Charts S = (I,J,I2,J2): r_{I,J} = 1, u3 r_{I2,J2} = 1 (J2 != J), unified stratum-(II)/(III)
# system of r16/st2_bigQ.py ('twocol'). Refinement: a UNIT chart T = (I',J',I2',J2') shows r_{I'J'} r_{I2'J2'} = 0 on every solution; so on chart S
# (r_{IJ} != 0, r_{I2J2} != 0) we may add r_X = 0 whenever {X,(I,J)} or {X,(I2,J2)} is the entry pair of a chart in a unit orbit (closed conditions).
# Symmetry: rows 0 <-> 1 (I -> 1-I), columns 0 <-> 1 (with f_0 <-> f_1), S_3 on columns 2,3,4.  Orbits of entry PAIRS are tracked.
# Usage: python3 -I staged_twocol.py SCHARTS(s1,s0) P(0|prime) TIMEOUT_S VMEM_KB PASSES
import sys, subprocess, itertools
schs=sys.argv[1].split(','); P=sys.argv[2]; TO=int(sys.argv[3]); VM=int(sys.argv[4]); PASSES=int(sys.argv[5])
base='/home/kevxhk/work/L-gct-210/stage3/r16'; out='/home/kevxhk/work/L-gct-210/stage3/r20'
entries=[(i,j) for i in (0,1) for j in range(5)]
def maps():
    for rs in (0,1):
        for cs in (0,1):
            for pm in itertools.permutations((2,3,4)):
                m={0:0,1:1,2:pm[0],3:pm[1],4:pm[2]}
                if cs: m[0],m[1]=1,0
                yield (lambda e,rs=rs,m=m: ((1-e[0]) if rs else e[0], m[e[1]]))
def pair_orbit(p):
    return {frozenset((g(p[0]),g(p[1]))) for g in maps()}
reps=[tuple(int(x) for x in l.split()) for l in open(base+'/twocol_reps.txt') if l.strip()]
alg='slimgb' if P=='0' else 'std'
for sch in schs:
    unitpairs=set(); log=open(out+'/staged_twocol_%s_%s.log'%(sch,P),'a')
    for ps in range(PASSES):
        prog=False
        for (I,J,I2,J2) in reps:
            pr=frozenset(((I,J),(I2,J2)))
            if pr in unitpairs: continue
            f=subprocess.run(['python3','-I',base+'/st2_bigQ.py','twocol',sch,str(I),str(J),alg,P,str(I2),str(J2)],capture_output=True,text=True).stdout.strip()
            extra=[]
            for X in entries:
                if X in ((I,J),(I2,J2)): continue
                if frozenset(((I,J),X)) in unitpairs or frozenset(((I2,J2),X)) in unitpairs:
                    if not (X[0]==I and X[1]==J): extra.append('r%d_%d'%X)
            s=open(f).read()
            # r_{I,J} is the chart coordinate '1'; refinement zeros are plain variables r{i}_{j}
            extra=[e for e in extra if e in s]
            if extra: s=s.replace('ring R=%s,'%P,'ideal EXTRA_R0=%s;\nC=C,EXTRA_R0;\nring R=%s,'%(','.join(extra),P),1)
            g=out+'/st_%s_%s_%d%d_%d%d_p%d.sing'%(sch,P,I,J,I2,J2,ps); open(g,'w').write(s)
            try:
                r=subprocess.run(['bash','-c','ulimit -v %d; Singular -q %s'%(VM,g)],capture_output=True,text=True,timeout=TO).stdout
                v='UNIT' if 'unit 1' in r else ('NONUNIT' if 'unit 0' in r else 'ERROR/MEM')
            except subprocess.TimeoutExpired: v='TIMEOUT'
            log.write('%s pass %d chart %d%d_%d%d extra %d: %s\n'%(sch,ps,I,J,I2,J2,len(extra),v)); log.flush()
            if v=='UNIT': unitpairs|=pair_orbit(((I,J),(I2,J2))); prog=True
        log.write('%s after pass %d: %d unit pair-orbits\n'%(sch,ps,len(unitpairs))); log.flush()
        if not prog: break
