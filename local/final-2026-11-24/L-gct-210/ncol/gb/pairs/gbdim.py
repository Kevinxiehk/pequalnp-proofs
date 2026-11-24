# Krull dimension of the ideal from a msolve GB file (grevlex, leading term = first term of each element)
import sys, re, itertools
def lead_vars(fn):
    txt=open(fn).read().split('#---')[-1]
    txt=txt.strip().lstrip('[').rstrip(':').rstrip(']')
    polys=txt.split(',\n')
    L=[]
    for p in polys:
        p=p.strip()
        if not p: continue
        first=re.split(r'(?<!\^)[+-]',p.replace('-','+-'),maxsplit=1)[0] if False else None
        terms=[t for t in re.split(r'\+(?![^()]*\))',p.replace('-','+-')) if t.strip()]
        lt=terms[0]
        vs=set(int(m) for m in re.findall(r't(\d+)',lt))
        L.append(vs)
    return L
for fn in sys.argv[1:]:
    L=lead_vars(fn); n=12; best=0
    for k in range(n,-1,-1):
        found=False
        for U in itertools.combinations(range(n),k):
            Us=set(U)
            if all(not vs<=Us for vs in L): found=True; break
        if found: best=k; break
    print(fn, 'elements',len(L),' dimension',best)
