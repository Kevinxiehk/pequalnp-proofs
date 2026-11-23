import sys; sys.path.insert(0,"/home/claude/work/L-gct-210/numerics/r2")
from spaces import *
from fractions import Fraction
sp={'ex1':ex1(),'ex2':ex2(),'rc45p1':np.load('/home/claude/work/L-gct-210/split/rc45p1.npy'),
    'd1_ext1':np.load('/home/claude/work/L-gct-210/split/d1_ext1.npy'),'L080':L080()}
imgs=L080_images()
print('distinct L080 images:',len(imgs), 'check all level:',max(fresh_check(I,trials=5) for I in imgs[:6]))
for nm,B in sp.items():
    inv,dE,gap,gr=inv_full(B)
    angs=[angle(B,I) for I in imgs]
    print(f'{nm}: dim {len(orth(B))} fresh {fresh_check(B):.1e} {inv} genrank {gr} dimE {dE} sv gap {gap[0]:.1e}/{gap[1]:.1e} min sin-angle to L080 images {min(angs):.2e}',flush=True)
print('angle ex1 vs rc45p1 %.1e, ex2 vs d1_ext1 %.1e, ex1 vs d1_ext1 %.1e'%(angle(sp['ex1'],sp['rc45p1']),angle(sp['ex2'],sp['d1_ext1']),angle(sp['ex1'],sp['d1_ext1'])))
