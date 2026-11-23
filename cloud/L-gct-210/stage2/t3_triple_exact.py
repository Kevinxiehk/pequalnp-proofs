# EXACT (rational) combinatorial test, tau-coordinates: tau_i(j) = kappa^i_j z_ij.
# Triple of rows 1,2,3 with a=1, pairwise Type I (sign vectors d1=1,d2,d3), X_123 = 0.
# For S (3 columns): functionals on C^{3xS}: f_i = row sums, g_{ii'} = sum_{j in C^{ii'} cap S} (tau_i - tau_i').
# If the six are independent (rho_S=6): ell != 0 on Pi_S for EVERY kappa, Pi_S cap ker ell = common kernel (3-dim),
# and ZBF needs perm_3(z) = k ell^3 on Pi_S, hence perm(d o tau) == 0 on that kernel (cubic in 3 parameters: test on a 4^3 grid).
import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/stage2')
from exactla import *
pats=[e for e in itertools.product([1,-1],repeat=5) if e[0]==1 and abs(sum(e))<5]
tot=0; killed=0; surv=[]; noS=0
grid=list(itertools.product(range(4),repeat=3))
for d2 in pats:
    for d3 in pats:
        if d2==d3: continue
        d=[(1,)*5,d2,d3]; tot+=1
        C={(0,1):[j for j in range(5) if d2[j]==1],(0,2):[j for j in range(5) if d3[j]==1],(1,2):[j for j in range(5) if d2[j]==d3[j]]}
        found=None; nS6=0
        for S in itertools.combinations(range(5),3):
            rows=[]
            for i in range(3):
                v=[0]*9
                for k in range(3): v[3*i+k]=1
                rows.append(v)
            for (i,ip),Cs in C.items():
                v=[0]*9
                for k,j in enumerate(S):
                    if j in Cs: v[3*i+k]=1; v[3*ip+k]=-1
                rows.append(v)
            ns,rk=nullspace(rows,9)
            if rk<6: continue
            nS6+=1
            nz=False
            for (x,y,z) in grid:
                tau=[x*ns[0][q]+y*ns[1][q]+z*ns[2][q] for q in range(9)]
                T=[[d[i][S[k]]*tau[3*i+k] for k in range(3)] for i in range(3)]
                if perm(T)!=0: nz=True; break
            if nz: found=S; break
        if found: killed+=1
        else:
            surv.append((d2,d3,nS6)); noS+= (nS6==0)
print('sign configurations (d2,d3):',tot,' killed (some S with rho_S=6 and perm^d != 0 on the kernel):',killed)
print('surviving:',len(surv),' of which with no S of rank 6:',noS); [print('  ',s) for s in surv[:60]]
