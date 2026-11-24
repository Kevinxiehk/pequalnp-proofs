import itertools, random
from fractions import Fraction
# (INJ) test: L_e = 5-dim subspace of P_a + P_b + P_c + P_d = (C^2)^4 with all four projections onto, dim(L_e cap three rows) = 3.
# Is the restriction {4-linear forms} -> {quartics on L_e} injective (16 coordinate products linearly independent on L_e)?
# Types by prescribed single-row parts Z_i inside P_i (z_i = 0, 1, 2), rest generic.  Exact rational arithmetic.
def rank(rows):
    rows=[r[:] for r in rows]; rk=0
    for c in range(len(rows[0])):
        piv=next((i for i in range(rk,len(rows)) if rows[i][c]!=0),None)
        if piv is None: continue
        rows[rk],rows[piv]=rows[piv],rows[rk]
        for i in range(len(rows)):
            if i!=rk and rows[i][c]!=0:
                f=rows[i][c]/rows[rk][c]; rows[i]=[x-f*y for x,y in zip(rows[i],rows[rk])]
        rk+=1
    return rk
rnd=random.Random(7); g=lambda: Fraction(rnd.randint(-6,6))
def make(z):
    basis=[]
    for i,zi in enumerate(z):
        for k in range(zi):
            v=[Fraction(0)]*8; v[2*i+k]=Fraction(1); basis.append(v)       # e_i (x) (k-th basis vector of P_i)
    while len(basis)<5: basis.append([g() for _ in range(8)])
    return basis[:5]
def dims(B):
    out=[rank(B)]
    out.append([rank([[b[2*i],b[2*i+1]] for b in B]) for i in range(4)])                  # projections
    out.append([5-rank([[b[2*i],b[2*i+1]] for b in B]+[]) for i in range(4)])
    out.append([5-rank([[b[2*i+k] for i in range(4) if i!=m for k in range(2)] for b in B]+[]) if False else None for m in range(4)])
    return out
def kern_dim(B,rows):   # dim of {xi in L : rows in 'rows' vanish}
    M=[[b[2*i+k] for i in rows for k in range(2)] for b in B]; return 5-rank(M)
def inj_rank(B,npts=80):
    pts=[[Fraction(rnd.randint(-9,9)) for _ in range(5)] for _ in range(npts)]
    rows=[]
    for eps in itertools.product(range(2),repeat=4):
        row=[]
        for t in pts:
            xi=[sum(t[k]*B[k][c] for k in range(5)) for c in range(8)]
            row.append(xi[eps[0]]*xi[2+eps[1]]*xi[4+eps[2]]*xi[6+eps[3]])
        rows.append(row)
    return rank(rows)
seen=set()
for z in itertools.product(range(3),repeat=4):
    zs=tuple(sorted(z,reverse=True))
    if zs in seen or sum(zs)>5: continue
    seen.add(zs)
    B=make(zs)
    if rank(B)<5: print(zs,'degenerate'); continue
    lam=[kern_dim(B,[i]) for i in range(4)]            # dim L cap {row i = 0}  (should be 3)
    single=[kern_dim(B,[k for k in range(4) if k!=i]) for i in range(4)]
    print('z =',zs,' dim(L cap {row i=0}) =',lam,' single-row parts =',single,' rank of the 16 products =',inj_rank(B))
