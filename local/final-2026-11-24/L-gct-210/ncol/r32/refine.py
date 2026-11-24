# Refine a failed orbit chart S of Gr(nv,N): every solution lying in a chart T whose orbit is already verified UNIT is excluded, so on
# chart S we may add p_T = 0 for all such T (closed conditions; RED-p stays valid: Z_p-bar is empty iff every chart piece is).
# single exchange T = S - S[s] + c: p_T = +- g_{s,c};  double exchange: p_T = 2x2 minor.
# usage: python3 -I refine.py IN.ms OUT.ms S(comma) N UNIT_REPS_FILE ORBIT_MODULE(orbz|orbits)
import sys, itertools, importlib.util
inp,out,Sstr,N,unitf,orbmod=sys.argv[1:7]; N=int(N); S=[int(c) for c in Sstr.split(',')]; nv=len(S)
spec=importlib.util.spec_from_file_location('om',orbmod); om=importlib.util.module_from_spec(spec)
src=open(orbmod).read().split('done=set()')[0]   # reuse generator definitions only
exec(src,om.__dict__)
unit_reps=[tuple(int(c) for c in l.split()[0].split(',')) for l in open(unitf) if l.strip()]
unit=set()
for R in unit_reps: unit|=om.orbit(tuple(sorted(R)))
myorb=om.orbit(tuple(sorted(S)))
free=[c for c in range(N) if c not in S]
def g(s,c): return 'g%d_%d'%(s,c)
extra=[]
for s in range(nv):
    for c in free:
        T=tuple(sorted([x for x in S if x!=S[s]]+[c]))
        if T in unit and T not in myorb: extra.append(g(s,c))
for s1,s2 in itertools.combinations(range(nv),2):
    for c1,c2 in itertools.permutations(free,2):
        if c1>c2: continue
        T=tuple(sorted([x for x in S if x not in (S[s1],S[s2])]+[c1,c2]))
        if T in unit and T not in myorb:
            extra.append('%s*%s-%s*%s'%(g(s1,c1),g(s2,c2),g(s1,c2),g(s2,c1)))
L=open(inp).read().rstrip('\n').rstrip(',').split('\n')
body='\n'.join(L)+(',\n'+',\n'.join(extra) if extra else '')
open(out,'w').write(body+'\n')
print('%s: added %d single-exchange zeros and %d minors'%(out,sum(1 for e in extra if '*' not in e),sum(1 for e in extra if '*' in e)))
