# orbits of 3-subsets of the 10 isotropic coordinates (a_0..a_4 = 0..4, b_0..b_4 = 5..9) under S5 (columns) x Z2 (a <-> b)
import itertools
def act(sig,fl,c):
    j=c%5; ab=c//5; j2=sig[j]; ab2=(1-ab) if fl else ab; return ab2*5+j2
G=[(sig,fl) for sig in itertools.permutations(range(5)) for fl in (0,1)]
def orbit(S): return {tuple(sorted(act(sig,fl,c) for c in S)) for sig,fl in G}
if __name__=='__main__':
    done=set(); reps=[]
    for S in itertools.combinations(range(10),3):
        if S in done: continue
        o=orbit(S); done|=o; reps.append((S,len(o)))
    print(len(reps),'orbits total',sum(n for _,n in reps))
    open('repsk3.txt','w').write('\n'.join(','.join(map(str,S))+' %d'%n for S,n in reps)+'\n')
