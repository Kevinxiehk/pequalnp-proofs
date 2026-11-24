# verify2 r7: the decisive [DC3] cell (3,2,(0,),0,'ab','ab') of verifyfl/exact/gen_n1s.py, split by vartheta(Z_0) = 0 (A) / != 0 (B).
# A and B together cover the cell over F_p-bar (B: Rabinowitsch u*<z,z> = 1 with the Theta-normalisation of the complement elements).
# usage: python3 -I dc3_split.py A|B|PLAIN [piv]
import sys, os, time
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/verifyfl/exact')
import exactlib as X, gen_n1s as G
p=2147483629; split=sys.argv[1]; piv=int(sys.argv[2]) if len(sys.argv)>2 else 0
case=(3,2,(piv,),0,'ab','ab')
names,polys=G.build(p,'m12m3',case,split=None if split=='PLAIN' else split)
fn='/home/kevxhk/work/L-gct-210/verify2/r7/dc3split_piv%d_%s.ms'%(piv,split)
X.write_msolve(fn,names,p,polys)
print('case',case,'split',split,'nvars',len(names),'npolys',len(polys),flush=True)
t0=time.time(); v,nb,dt=X.run_msolve(fn,timeout=1500); print('verdict',v,'basis',nb,'time %.1f s'%dt,flush=True)
