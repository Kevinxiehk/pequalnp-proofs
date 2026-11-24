# verify2 r7: split B' of the decisive [DC3] cell: the PLAIN cell system of gen_n1s.py plus u*<z_0,z_0> = 1 (vartheta(Z_0) != 0),
# pivot normalisation kept.  Split A (plain + <z_0,z_0> = 0) and B' cover the plain cell over F_p-bar.
import sys, os, time
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/verifyfl/exact')
import exactlib as X, gen_n1s as G
p=2147483629; piv=int(sys.argv[1]) if len(sys.argv)>1 else 0
CAP={}
orig=X.equations
def cap(B,W,pp,keyed=False):
    CAP['B']=B; return orig(B,W,pp)
X.equations=cap
case=(3,2,(piv,),0,'ab','ab')
names,polys=G.build(p,'m12m3',case)
B0=CAP['B'][0]                       # Z_0 = the N_P element (echelon row), first in B
nrm={}
for a in range(4): nrm=X.padd(nrm,X.pmul(B0[a][0],B0[a][0],p),p)
u=len(names); names=names+['u']
polys=polys+[X.padd(X.pmul({(u,):1},nrm,p),X.pconst(-1,p),p)]
fn='/home/kevxhk/work/L-gct-210/verify2/r7/dc3splitBp_piv%d.ms'%piv
X.write_msolve(fn,names,p,polys)
print('case',case,"split B' nvars",len(names),'npolys',len(polys),flush=True)
v,nb,dt=X.run_msolve(fn,timeout=1500); print('verdict',v,'basis',nb,'time %.1f s'%dt,flush=True)
