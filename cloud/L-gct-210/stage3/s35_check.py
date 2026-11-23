# Exact check of the computation in Lemma S3-5: u = a*y + b*e_e w^T + c*x_3 on the rows (k,l,e), columns 0..4, T = {0,1};
# y = (e_k - e_l) e_0^T, w = (1,-1,0,0,0), x_3 = ((h/2)(e_0+e_1); (h/2)(e_0+e_1); p).  P_1, P_2, P_3 = sums of k x k subpermanents.
import itertools, random
from fractions import Fraction as Fr
def Pk(M,k):
    tot=0
    for rows in itertools.combinations(range(len(M)),k):
        for cols in itertools.combinations(range(5),k):
            for perm in itertools.permutations(cols):
                pr=Fr(1)
                for i,cc in zip(rows,perm): pr*=M[i][cc]
                tot+=pr
    return tot
rnd=random.Random(2); ok=True
for trial in range(200):
    h=Fr(rnd.randint(-5,5)); a,b,c=[Fr(rnd.randint(-4,4)) for _ in range(3)]
    p=[Fr(rnd.randint(-5,5)) for _ in range(5)]
    p[4]=-2*h-sum(p[:4])                                   # P_1 of x_3: s(p) = -2h
    yk=[Fr(1),0,0,0,0]; yl=[Fr(-1),0,0,0,0]; w=[Fr(1),Fr(-1),0,0,0]; xk=[h/2,h/2,0,0,0]
    M=[[a*yk[j]+c*xk[j] for j in range(5)],[a*yl[j]+c*xk[j] for j in range(5)],[b*w[j]+c*p[j] for j in range(5)]]
    sp=sum(p[2:])                                          # s'(p)
    P2f=c*c*(h*h/2-4*h*h-h*(p[0]+p[1])); P3f=c**3*sp*h*h/2
    ok&=(Pk(M,1)==0) and (Pk(M,2)==P2f) and (Pk(M,3)==P3f)
print('Lemma S3-5 formulas  P_1 = 0,  P_2 = c^2 (h^2/2 - 4h^2 - h(p_j+p_l\')),  P_3 = c^3 s\'(p) h^2/2  hold on 200 random rational points:',ok)
print('consequence: P_2 = 0 gives p_j + p_l\' = -(7/2) h, hence s\'(p) = s(p) - (p_j+p_l\') = (3/2) h and P_3 = (3/4) h^3 c^3')
