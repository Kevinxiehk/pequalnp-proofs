import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/numerics')
from core import *
from ext_in_E import ext_search
rng=np.random.default_rng(11)
W=orth(weight_w5())
circ=np.zeros((5,5),complex); f=[1,1j,-1j,-1]
for i in range(4):
    for j in range(4): circ[i,j]=f[(j-i)%4]
print('circ line DC level fresh %.1e'%fresh_check(circ[None]))
# test L080 + circ (not a block gluing)
print('L080+circ fresh %.1e'%fresh_check(np.concatenate([L080(),circ[None]])))
seeds={'circ':circ[None],'W5_1':np.einsum('j,jab->ab',rng.normal(size=3)+1j*rng.normal(size=3),W)[None],
       'W5_2':orth(np.einsum('ij,jab->iab',rng.normal(size=(2,3))+1j*rng.normal(size=(2,3)),W))}
for name,K in seeds.items():
    K=orth(K); dE=ext_space(K)[0]
    for D in [5,7]:
        dE,na,res,(fc,B)=ext_search(K,D-len(K),starts=2,seed=D,tlimit=float(sys.argv[1]))
        msg=f'{name} (d0={len(K)}, dimE={dE}) -> D={D}: fresh '+' '.join('%.0e'%r for r in res)
        if fc<1e-10:
            inv=invariants(B); msg+=f' FOUND (r,d)=({inv["r"]},{inv["d"]}) ra,rb={inv["ra"]},{inv["rb"]} extdim={ext_space(B)[0]}'
            np.save(f'rd_{name}_D{D}.npy',B)
        print(msg,flush=True)
