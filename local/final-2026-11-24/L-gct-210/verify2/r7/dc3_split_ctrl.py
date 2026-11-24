# verify2 r7: controls for the split A/B mode of gen_n1s.py.
# (1) NON-unit control: k = 2, rho = 1, N_P = C chi_1 (e_0 - e_1)^T (pivot 0), complement with column 3 on the line C chi_1 ('ab' chart: a = i, b = -1),
#     column 4 inactive (al = 0 allowed, v4 chart 'z1'): contains the strongly level type I plane chi_1 (x) Lam_{0,1,3}; split A must be NON-unit.
#     We also substitute that plane into the split-A system (exact mod p) to check the equations vanish there.
# (2) UNIT consistency: piv1 cell (unsplit UNIT in 42 s) under split A and split B.
import sys, time
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/verifyfl/exact')
import exactlib as X, gen_n1s as G
p=2147483629
for case,split in [((2,1,(0,),0,'ab','z1'),'A'),((3,2,(1,),0,'ab','ab'),'A'),((3,2,(1,),0,'ab','ab'),'B')]:
    names,polys=G.build(p,'m12m3',case,split=split)
    fn='/home/kevxhk/work/L-gct-210/verify2/r7/ctrl_%s_%s.ms'%(G.casename(case),split)
    X.write_msolve(fn,names,p,polys)
    v,nb,dt=X.run_msolve(fn,timeout=600)
    print('case',case,'split',split,'nvars',len(names),'npolys',len(polys),'->',v,nb,'%.1fs'%dt,flush=True)
