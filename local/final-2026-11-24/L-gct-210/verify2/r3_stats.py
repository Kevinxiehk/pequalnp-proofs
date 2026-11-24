# verify2: statistics of the cubics c_S in the 132 exception configurations: dim K_S, number of linear factors, Gaussian-rationality.
import sys, itertools, importlib.util, numpy as np
from fractions import Fraction as Fr
spec=importlib.util.spec_from_file_location('r3s','/home/kevxhk/work/L-gct-210/stage2/r3_survey.py'); r3=importlib.util.module_from_spec(spec); spec.loader.exec_module(r3)
nullspace,rank,perm,typeII=r3.nullspace,r3.rank,r3.perm,r3.typeII
rng=np.random.default_rng(3)
def rnd(k): return rng.normal(size=k)+1j*rng.normal(size=k)
hist={}; irr=0; tot=0; cof={}
for comp in ((1,1,3),(1,3,1),(3,1,1),(1,2,2),(2,1,2),(2,2,1)):
    s12=(tuple([0]*comp[0]+[1]*comp[1]+[2]*comp[2]),1)
    for cells in itertools.product(range(3),repeat=5):
        if len(set(cells))<3: continue
        for eps in (1,-1):
            s13=(cells,eps)
            w2,A1,A2,y12=typeII(*s12); w3,B1,B3,y13=typeII(*s13); one=np.ones(5)
            if not (np.abs(A1-B1).max()<1e-9 or np.abs(A1+B1-1).max()<1e-9): continue
            def F(rows):
                v=np.zeros((3,5),complex)
                for i,vec in rows: v[i]=vec
                return v.reshape(-1)
            A0=np.array([F([(0,one),(1,-one)]),F([(0,one),(2,-one)]),F([(0,A1+y12*one),(1,A2)]),F([(0,B1+y13*one),(2,B3)])])
            u=np.array([one,1/w2,1/w3])
            for S in itertools.combinations(range(5),3):
                cols=[i*5+j for i in range(3) for j in S]
                Pt=nullspace(A0[:,cols]); ell=np.array([1,1,1,0,0,0,0,0,0])@Pt
                if np.abs(ell).max()<1e-9: hist[('ell=0 on Pi~_S',)]=hist.get(('ell=0 on Pi~_S',),0)+1; continue
                E=Pt@nullspace(ell[None,:]); d=E.shape[1]
                def cfun(v,E=E,S=S): return perm(((E@v).reshape(3,3))*u[:,list(S)])
                facs=r3.linfactors(cfun,d)
                if facs is None: hist[(d,'c=0')]=hist.get((d,'c=0'),0)+1; continue
                # multiplicity check: does c equal k * product of found factors (with repetition)?
                key=(d,len(facs)); hist[key]=hist.get(key,0)+1; tot+=len(facs)
                if len(facs)==1:
                    lam=facs[0]; pts=[rnd(d) for _ in range(40)]
                    # cofactor quadric q = c / lam : fit and compute rank
                    mons=[(a,b) for a in range(d) for b in range(a,d)]
                    M=np.array([[p[a]*p[b] for (a,b) in mons] for p in pts]); y=np.array([cfun(p)/(lam@p) for p in pts])
                    co=np.linalg.lstsq(M,y,rcond=None)[0]; Q=np.zeros((d,d),complex)
                    for (a,b),c in zip(mons,co): Q[a,b]+=c/2; Q[b,a]+=c/2
                    s=np.linalg.svd(Q,compute_uv=False); rk=int(np.sum(s>1e-7*s[0])); cof[(d,rk)]=cof.get((d,rk),0)+1
for k,v in sorted(hist.items(),key=str): print(k,v)
print('total factors',tot,' cofactor quadric (dim K_S, rank) when exactly one linear factor:',cof)
