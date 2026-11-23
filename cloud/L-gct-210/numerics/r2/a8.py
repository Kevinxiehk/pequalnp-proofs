import sys; sys.path.insert(0,"/home/claude/work/L-gct-210/numerics/r2")
from spaces import *
B=ex3(); L=orth(B); dE,E,_=ext_space(L); print('ex3 E level? %.2e'%fresh_check(E))
for i in range(7):
    S=orth(np.delete(B,i,axis=0)); dS,ES,sS=ext_space(S)
    print(f' ex3 drop {i}: inv {invariants(S)} dimE(S)={dS} gap {sS[24-dS]:.1e}/{sS[25-dS]:.1e}',flush=True)
