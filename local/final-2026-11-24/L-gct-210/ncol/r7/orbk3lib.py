import itertools
def act(sig,fl,c):
    j=c%5; ab=c//5; j2=sig[j]; ab2=(1-ab) if fl else ab; return ab2*5+j2
G=[(sig,fl) for sig in itertools.permutations(range(5)) for fl in (0,1)]
def orbit(S): return {tuple(sorted(act(sig,fl,c) for c in S)) for sig,fl in G}
done=set()
