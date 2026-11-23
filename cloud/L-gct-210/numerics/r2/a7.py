import sys; sys.path.insert(0,"/home/claude/work/L-gct-210/numerics/r2")
from spaces import *
sp={'L080':L080(),'ex1':ex1(),'ex2':ex2(),'ex3':ex3()}
for nm,B in sp.items():
    inv,dE,gap,gr=inv_full(B)
    print(f'{nm}: fresh {fresh_check(B):.1e} (r,d,ra,rb)=({inv["r"]},{inv["d"]},{inv["ra"]},{inv["rb"]}) genrank {gr} dimE {dE} gap {gap[0]:.1e}/{gap[1]:.1e}',flush=True)
names=list(sp)
for a in range(4):
    for b in range(a+1,4):
        print(f'  equiv-angle (perms,transpose,conj) {names[a]} vs {names[b]}: {equiv_angle_c(sp[names[a]],sp[names[b]]):.2e}',flush=True)
