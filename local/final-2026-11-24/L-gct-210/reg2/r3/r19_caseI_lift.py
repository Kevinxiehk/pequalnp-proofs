# Round 19: lift the 3-dim LINEAR components of V_B (case (I), n = (1,2,3,-6,0)) found mod 32003 to Q (rational reconstruction) and check
# over Q (Singular, exact) that each lies in V_B: reduce(I, std(L)) == 0 for every generator of I.
import re, subprocess, sys
from fractions import Fraction
p=32003
log=open('/home/kevxhk/work/L-gct-210/reg2/evidence/logs/r19_caseI_modp_linear.log').read()
blocks=[b.split('COMP')[0] for b in log.split('LINEAR COMPONENT:')[1:]]
def ratrec(a):
    a%=p; r0,r1,s0,s1=p,a,0,1
    while r1*r1*2>p: q=r0//r1; r0,r1=r1,r0-q*r1; s0,s1=s1,s0-q*s1
    return Fraction(r1,s1)
def lift(poly):
    poly=poly.strip().rstrip(',')
    out=''
    for sign,coef,var in re.findall(r'([+-]?)(\d*)\*?([a-z]\w*)',poly):
        c=int(coef) if coef else 1; c=-c if sign=='-' else c; f=ratrec(c)
        out+='+(%s)*%s'%(f,var)
    return out[1:] if out.startswith('+') else out
src=open('/home/kevxhk/work/L-gct-210/reg2/r3/r3_cone_I_1.sing').read()
head=src.split('I=std(I);')[0]
for bi,b in enumerate(blocks):
    lines=[l for l in b.strip().split('\n') if l.strip()]
    L=[lift(l) for l in lines]
    body=head+'ideal Lq=%s;\nLq=std(Lq);\nprint("dim L = "+string(dim(Lq)));\nideal N=reduce(I,Lq);\nprint("nonzero remainders: "+string(size(N)));\nquit;\n'%(','.join(L))
    open('/tmp/r19_caseI_lift_%d.sing'%bi,'w').write(body)
    r=subprocess.run(['/usr/bin/Singular','-q'],stdin=open('/tmp/r19_caseI_lift_%d.sing'%bi),capture_output=True,text=True,timeout=300)
    o='\n'.join(l for l in r.stdout.split('\n') if not l.startswith('// **'))
    print('component %d: L = %s'%(bi+1,', '.join(x.replace('+(1)*','+') for x in L)))
    print('   ',o.strip().replace('\n','  '))
