# evaluate .ms polynomial systems mod p at the exact point of R3.5 in chart 01_01_01 (W_a = W_b = span(e_0, chi'), G = D2^perp, D2 = span(chi', chi'^2))
import sys, re
P=2147483629
I=next(c for a in range(2,10**6) for c in [pow(a,(P-1)//4,P)] if c*c%P==P-1)
inv=lambda x: pow(x%P,P-2,P)
q4=inv(4); q2=inv(2)
pt=[0,0,0, I,P-1,(P-I)%P, 0,0,0, I,P-1,(P-I)%P, (-(1-I)*q4)%P, (-q2)%P, I, P-1]
def ev(poly):
    s=0
    for term in poly.split('+'):
        parts=term.split('*'); c=int(parts[0]); v=c
        for f in parts[1:]:
            m=re.match(r't(\d+)(\^(\d+))?$',f); e=int(m.group(3)) if m.group(3) else 1
            v=v*pow(pt[int(m.group(1))],e,P)%P
        s=(s+v)%P
    return s
for fn in sys.argv[1:]:
    L=open(fn).read().split('\n'); polys=''.join(L[2:]).strip().rstrip(',').split(',')
    vals=[ev(p.strip()) for p in polys if p.strip()]
    print(fn, len(vals),'equations; nonzero at the point:', sum(1 for v in vals if v))
