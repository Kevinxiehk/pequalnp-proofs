import sys; sys.path.insert(0,"/home/claude/work/L-gct-210/numerics/r2")
from spaces import *
for c in [0.3+0.7j, 2.0, -1.3+0.2j, 1j*np.sqrt(3)/2, 1e-3]:
    B=fam(c); inv,dE,gap,gr=inv_full(B); E=ext_space(B)[1]
    print(f'c={c:.3f}: fresh {fresh_check(B):.1e} (r,d,ra,rb)=({inv["r"]},{inv["d"]},{inv["ra"]},{inv["rb"]}) rk{gr} dimE {dE} gap {gap[0]:.1e}/{gap[1]:.1e} E level? {fresh_check(E):.1e}')
print('cp free test (c=1, cp=1):', '%.1e'%fresh_check(fam(1.0,cp=1.0)))
B=lim0(); inv,dE,gap,gr=inv_full(B); E=ext_space(B)[1]
print(f'limit c->0: fresh {fresh_check(B):.1e} {inv} rk{gr} dimE {dE} gap {gap[0]:.1e}/{gap[1]:.1e} E level? {fresh_check(E):.1e}')
print('equiv fam(0.3+0.7j) vs fam(2.0): %.2e'%equiv_angle_c(fam(0.3+0.7j),fam(2.0)))
