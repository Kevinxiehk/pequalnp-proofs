# Round 20: STAGED CHART REFINEMENT for the colel sigma = 0 stratum-(II)-proper charts (x* = (1,rho,-1-rho) (x) e_2, charts u3 rho(1+rho) h_0[c0]
# h_1[c1] h_2[c2] = 1, c_i in {0,1,3,4}). If chart (a',b,c) is verified UNIT then every solution has h_0[a'] h_1[b] h_2[c] rho(1+rho) = 0, so on chart
# (a,b,c) (where h_1[b] h_2[c] rho(1+rho) != 0) we may add h_0[a'] = 0; similarly for the other two slots. Closed conditions -> sound by induction.
# Symmetries used to expand the unit set: rows 0 <-> 1 ((a,b,c) -> (b,a,c)), columns 0 <-> 1 and columns 3 <-> 4 on all three slots.
# Usage: python3 -I staged_colel.py SCH TO VMEM PASSES
import sys, subprocess, itertools, os
sch,TO,VM,PASSES=sys.argv[1],int(sys.argv[2]),int(sys.argv[3]),int(sys.argv[4])
base='/home/kevxhk/work/L-gct-210/stage3/r16'; out='/home/kevxhk/work/L-gct-210/stage3/r20'
C=[0,1,3,4]; charts=[(a,b,c) for a in C for b in C for c in C]
def colmaps():
    for s01 in (0,1):
        for s34 in (0,1):
            m={0:0,1:1,3:3,4:4}
            if s01: m[0],m[1]=1,0
            if s34: m[3],m[4]=4,3
            yield m
def orbit(ch):
    a,b,c=ch; o=set()
    for m in colmaps():
        o.add((m[a],m[b],m[c])); o.add((m[b],m[a],m[c]))
    return o
unit=set(); log=open(out+'/staged_colel_%s.log'%sch,'a')
for ps in range(PASSES):
    progress=False
    for ch in charts:
        if ch in unit: continue
        a,b,c=ch
        f=subprocess.run(['python3','-I',base+'/st2_bigQ.py','colel',sch,'0','2','slimgb','0',str(a),str(b),str(c)],capture_output=True,text=True).stdout.strip()
        H=['h0','h1','h2']; extra=[]
        # explicit h-vectors as in st2_bigQ.py (Delta-chart): h0 = k + l0 f0 + m0 f1, h1 = k + l1 f0 + m1 f1, h2 = k
        f0=['1','0','p2','p3','(-1-p2-p3)']; f1=['0','1','q2','q3','(-1-q2-q3)']
        hv=[['(k%d+l0*%s+m0*%s)'%(j,f0[j],f1[j]) for j in range(5)],['(k%d+l1*%s+m1*%s)'%(j,f0[j],f1[j]) for j in range(5)],['k%d'%j for j in range(5)]]
        for x in C:
            if x!=a and (x,b,c) in unit: extra.append(hv[0][x])
            if x!=b and (a,x,c) in unit: extra.append(hv[1][x])
            if x!=c and (a,b,x) in unit: extra.append(hv[2][x])
        s=open(f).read()
        if extra: s=s.replace('ring R=0,','ideal EXTRA_R0=%s;\nC=C,EXTRA_R0;\nring R=0,'%','.join(extra),1)
        g=out+'/sc_%s_%d%d%d_p%d.sing'%(sch,a,b,c,ps); open(g,'w').write(s)
        try:
            r=subprocess.run(['bash','-c','ulimit -v %d; Singular -q %s'%(VM,g)],capture_output=True,text=True,timeout=TO).stdout
            v='UNIT' if 'unit 1' in r else ('NONUNIT' if 'unit 0' in r else 'ERROR')
        except subprocess.TimeoutExpired: v='TIMEOUT'
        log.write('pass %d chart %d%d%d extra %d: %s\n'%(ps,a,b,c,len(extra),v)); log.flush()
        if v=='UNIT': unit|=orbit(ch); progress=True
        if v=='NONUNIT': print('NONUNIT chart',ch,flush=True)
    log.write('after pass %d: unit %d of 64\n'%(ps,len(unit))); log.flush()
    if len(unit)==64 or not progress: break
print('FINAL unit',len(unit),'of 64; missing',sorted(set(charts)-unit))
