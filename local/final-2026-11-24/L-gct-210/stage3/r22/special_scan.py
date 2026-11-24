# Round 22: numerical scan for SPECIAL members (outside-row kernel > 4 for EVERY pair) of the (1,1,1,1,0) configurations k_N = 2, (2,2), (2,1,1), k_N = 4.
# Strategy: sample many random members (LM on the single-row level conditions), compute the smallest 'extra' singular value per pair
# (kernel dim 4 generic: sigma_{11} of the 16 x 15 matrix), then minimise max over pairs of sigma_{11}/sigma_1 along the family by LM (adding it as a target).
import numpy as np, itertools, sys
ARGV=sys.argv[:]; sys.argv=['x','7']
exec(open('/home/kevxhk/work/L-gct-210/stage3/r18/cfg_kernels.py').read().split("for nm,(param,nv,extra) in cfgs.items():")[0])
sys.argv=ARGV
def pair_mats(W):
    out=[]
    for r,k in itertools.combinations(range(4),2):
        l,n=[i for i in range(4) if i not in (r,k)]; A=[]
        for t in range(5):
            for T in itertools.combinations(range(4),t):
                Dv=delv(np.array([W[i] for i in T]).reshape(len(T),5))
                A.append(np.concatenate([Dv,Dv*(l not in T),Dv*(n not in T)]))
        out.append(np.array(A))
    return out
def jump_measure(W):
    vals=[]
    for A in pair_mats(W):
        s=np.linalg.svd(A,compute_uv=False); vals.append(s[10]/s[0])   # 11th singular value (rank 11 generic -> kernel 4)
    return np.array(vals)
nm=sys.argv[1]; param,nv,extra=cfgs[nm]
nvar=nv+len(extra(np.zeros(nv+4,complex)))
found=[]
for trial in range(int(sys.argv[2])):
    x=solve(param,nvar,extra)
    if x is None: continue
    W=np.array(param(x)); jm=jump_measure(W)
    print(nm,'member',trial,'jump measures per pair',np.round(jm,5),flush=True)
