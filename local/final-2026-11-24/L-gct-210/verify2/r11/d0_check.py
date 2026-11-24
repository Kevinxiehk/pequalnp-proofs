# Is the column-constant element (rows (3,-1,-1,-1,0)) x 1^T (reg2's 4 d_0) in T_1(M) for the BB / BLOCK / DBLOCK members?  Also the
# analogous d_r for each row r, and tau_r.  D_t perm(J+m) checked at 60 random rational points of M (degree <= 4 in 6 variables: 210 monomials;
# a nonzero value is a disproof, 60 zeros only evidence -- then confirmed by the exact T' membership below).
import random
exec(open('/home/kevxhk/work/L-gct-210/verify2/r11/reg2_r56.py').read().split("# BB:")[0])
def dperm(A,T):
    return sum(T[i][j]*perm([[A[a][b] for b in range(5) if b!=j] for a in range(5) if a!=i]) for i in range(5) for j in range(5) if T[i][j]!=0)
def full(B,c):
    M=[[F(1)]*5 for _ in range(5)]
    for i in range(4):
        for l in range(5): M[i][l]+=sum(c[q]*B[q][i][l] for q in range(len(B)))
    return M
def dr(r):
    v=[F(-1)]*4+[F(0)]; v[r]=F(3); return [[v[i]]*5 for i in range(5)]
exec(open('/home/kevxhk/work/L-gct-210/verify2/r11/reg2_r56.py').read().split("# BB:")[1].split("\n",1)[1].replace("run(","(lambda *a: None)("))
fams={'BB':[outer_row(0,[1,-1,0,0,0]),outer_row(0,[1,0,-1,0,0]),outer_row(1,[-1,-1,-1,4,-1]),outer_row(1,[-1,-1,-1,-1,4]),outer_col(x,3),outer_col(xp,4)],
      'BLOCK(2,3)':block(2,3),'DBLOCK(2,3)':dblock(2,3)}
random.seed(3)
for nm,B in fams.items():
    pts=[full(B,[F(random.randint(-9,9)) for _ in B]) for _ in range(60)]
    res=[]
    for r in range(4):
        res.append('d_%d:%s'%(r,all(dperm(A,dr(r))==0 for A in pts)))
    print(nm,' '.join(res),flush=True)
