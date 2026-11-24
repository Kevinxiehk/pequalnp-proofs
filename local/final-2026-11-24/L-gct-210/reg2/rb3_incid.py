# Round 11, target 1: which incidences (n = generator of W^perp cap 1^perp, zeta non-constant) allow a RANK-3 B with b skew and SK2(zeta)?
import numpy as np, itertools
rg=np.random.default_rng(11)
F=np.array([[1 if c==i else (-1 if c==4 else 0) for c in range(5)] for i in range(4)],float)
def bspace(n,zeta):
    Wb=np.linalg.svd(np.array([np.ones(5),n]))[2][2:].conj()
    assert np.abs(Wb@n).max()<1e-8
    rows=[]
    for i in range(3):
        for l in range(i,3):
            for z in (np.ones(5),zeta):
                row=np.zeros((3,4),complex)
                for k in range(4):
                    row[l,k]+=np.sum(Wb[i]*z*F[k]); row[i,k]+=np.sum(Wb[l]*z*F[k])
                rows.append(row.ravel())
    A=np.array(rows); u,s,vh=np.linalg.svd(A); r=int((s>1e-9*s[0]).sum()); N=vh[r:].conj()
    if len(N)==0: return 0,0
    rk=max(np.linalg.matrix_rank(((rg.normal(size=len(N))+1j*rg.normal(size=len(N)))@N).reshape(3,4),tol=1e-8) for _ in range(3))
    return len(N),rk
def rnd(): return rg.normal()+1j*rg.normal()
types={'(4,1)':[0,0,0,0,1],'(3,2)':[0,0,0,1,1],'(3,1,1)':[0,0,0,1,2],'(2,2,1)':[0,0,1,1,2],'(2,1,1,1)':[0,0,1,2,3],'distinct':[0,1,2,3,4]}
for tn,lab in types.items():
    zeta_lab=np.array(lab)
    found=set()
    # n: sum-zero with zeros on a subset Z0 of coordinates; values random otherwise; also isotropic variants
    for zs in range(0,4):
        for Z0 in itertools.combinations(range(5),zs):
            for trial in range(2):
                n=np.array([0 if c in Z0 else rnd() for c in range(5)],complex)
                free=[c for c in range(5) if c not in Z0]
                if len(free)<2: continue
                n[free[-1]]=-n[free[:-1]].sum()
                vals=rg.normal(size=5)+1j*rg.normal(size=5); zeta=np.array([vals[x] for x in zeta_lab])
                d,rk=bspace(n,zeta)
                if rk==3: found.add('n zero on %s (zeta level sets %s)'%(Z0,[tuple(np.where(zeta_lab==v)[0]) for v in sorted(set(lab))]))
    print(tn,':',sorted(found) if found else 'no rank-3 with these incidences')
