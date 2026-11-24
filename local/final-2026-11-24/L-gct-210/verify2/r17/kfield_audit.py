# verify2 r17: audit tool for leanfl's K-field port (FLk/TC5 over a field K with i^2 = -1 and numeral hypotheses).
# usage: python3 -I kfield_audit.py FILE.lean [FINAL_THEOREM_NAME]
# Reports: (1) remaining C-specific constructs; (2) every numeral N occurring in a hypothesis "(N : K) != 0" / "NeZero" / list "[..]" of
# nonzero numerals, with its factorisation and whether P1 divides it; (3) all integer literals in the file and any literal divisible by P1;
# (4) the binders of the final theorem (must quantify over K with [Field K] and the numeral hypotheses, nothing else unproved);
# (5) sorry / axiom / admit occurrences.
import re, sys
from sympy import factorint
P1=2147483629
f=sys.argv[1]; fin=sys.argv[2] if len(sys.argv)>2 else None
s=open(f).read(); sc=re.sub(r'--[^\n]*','',s); sc=re.sub(r'/-.*?-/','',sc,flags=re.S)
print('== file',f,len(s.splitlines()),'lines')
for k in ('ℂ','Complex.','Real','‖','abs ','CharZero','IsAlgClosed','nlinarith','positivity'):
    n=sc.count(k)
    if n: print('  construct %-12s %d'%(k,n))
for k in ('sorry','admit','axiom '):
    print('  %-6s %d'%(k,len(re.findall(r'\b'+k.strip()+r'\b',sc))))
hyp=set()
for m in re.finditer(r'\((\d+)\s*:\s*\w+\)\s*≠\s*0',sc): hyp.add(int(m.group(1)))
for m in re.finditer(r'NeZero\s*\(\s*\(?(\d+)',sc): hyp.add(int(m.group(1)))
for m in re.finditer(r'CharP\s+\w+\s+(\d+)',sc): print('  CharP mention with',m.group(1))
print('  numerals in "(N : K) != 0"-type hypotheses:',sorted(hyp))
for N in sorted(hyp): print('    N =',N,factorint(N),' P1 | N:',N%P1==0)
lits=set(int(x) for x in re.findall(r'(?<![\w.])(\d+)(?![\w.])',sc))
bad=[N for N in lits if N and N%P1==0]
pr=set()
for N in lits:
    if N>1 and N<10**12: pr|=set(factorint(N))
print('  integer literals: %d distinct, max %d; primes dividing some literal: %s; literals divisible by P1: %s'%(len(lits),max(lits) if lits else 0,sorted(pr)[:40],bad))
if fin:
    m=re.search(r'theorem\s+'+re.escape(fin)+r'(.*?):=',s,flags=re.S)
    print('== final theorem binders:\n',(m.group(1)[:2500] if m else 'NOT FOUND'))
