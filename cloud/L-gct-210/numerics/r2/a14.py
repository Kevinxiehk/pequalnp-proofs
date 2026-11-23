import sys; sys.path.insert(0,"/home/claude/work/L-gct-210/numerics/r2")
from spaces import *
rng=np.random.default_rng(5)
for nm,B in [('ex3',ex3()),('fam(0.6+1.4i)',fam(0.3+0.7j)),('lim0',lim0())]:
    L=orth(B); out=[]
    for tr in range(3):
        C=rng.normal(size=(6,7))+1j*rng.normal(size=(6,7)); S=orth(np.einsum('ij,jab->iab',C,L))
        dS,ES,sS=ext_space(S); out.append(f'dimE(S)={dS} gap {sS[24-dS]:.1e}/{sS[25-dS]:.1e} E(S) level? {fresh_check(ES):.1e}')
    print(nm,'generic hyperplanes:',' | '.join(out),flush=True)
# two family blocks in disjoint column pairs
F=ex1()[2:]
for s1,s2 in [(0.7+0.2j,1.3-0.5j),(1j*np.sqrt(3)/2,1j*np.sqrt(3)/2),(0.0001,0.5)]:
    V1=fam(s1,0,3)[:2]; V2=fam(s2,1,2)[:2]
    print(f'F+V(s1;0,3)+V(s2;1,2) dim9 fresh {fresh_check(np.concatenate([F,V1,V2])):.1e}; F+V1+V2[0] dim8 fresh {fresh_check(np.concatenate([F,V1,V2[:1]])):.1e}',flush=True)
