# verify2: does stage2/t10_typeII_exact.py use a correct I_3^perp?  Check rank of the 5 functionals N on C^15 for all all-Type-II configs.
import itertools, sys
src=open('/home/claude/work/L-gct-210/stage2/t10_typeII_exact.py').read()
head=src.split("canon=[]")[0]
exec(head)
def Nmat(s12,s13,s23):
    w2,A1,A2,y12=typeII(*s12); w3,B1,B3,y13=typeII(*s13); w23,C2,C3,y23=typeII(*s23)
    def F(rows):
        v=[Z]*15
        for i,vec in rows:
            for j in range(5): v[5*i+j]=vec[j] if isinstance(vec[j],G) else G(vec[j])
        return v
    one=[1]*5
    return [F([(0,one),(1,[-1]*5)]),F([(0,one),(2,[-1]*5)]),F([(0,[G(A1[j])+y12 for j in range(5)]),(1,A2)]),
       F([(0,[G(B1[j])+y13 for j in range(5)]),(2,B3)]),F([(1,[G(C2[j])+y23 for j in range(5)]),(2,C3)])]
canon=[]
for comp in ((1,1,3),(1,3,1),(3,1,1),(1,2,2),(2,1,2),(2,2,1)):
    canon.append((tuple([0]*comp[0]+[1]*comp[1]+[2]*comp[2]),1))
structs=[(cells,eps) for cells in itertools.product(range(3),repeat=5) if len(set(cells))==3 for eps in (1,-1)]
tot=0; ranks={}; bad=[]; wcheck=0
for s12 in canon:
    e2=expo(*s12)
    for s13 in structs:
        e3=expo(*s13); r=[(e3[j]-e2[j])%4 for j in range(5)]
        for s23 in opts23(r):
            tot+=1
            N=Nmat(s12,s13,s23)
            ns,rk=nullspace(N,15)
            ranks[rk]=ranks.get(rk,0)+1
            if rk<5: bad.append((s12,s13,s23))
            # consistency of the (2,3) structure with the ratio w3/w2: w23 must be proportional to w3/w2
            w2=typeII(*s12)[0]; w3=typeII(*s13)[0]; w23=typeII(*s23)[0]
            q=[(w3[j]/w2[j])/w23[j] for j in range(5)]
            if any(not (q[j]-q[0]).iszero() for j in range(5)): wcheck+=1
print('configs',tot,'rank histogram of N on C^15',ranks,'ratio-inconsistent (2,3) structures:',wcheck)
for b in bad[:10]: print('  rank<5:',b)
