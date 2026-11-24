# verify2: exact checks of the eliminations in the two strata of Lemma N2-GEN flagged by the author.
from fractions import Fraction as Fr
import itertools, random
# |S| = 4, (1,1,1,1):  be_a = tau^2 - A h, be_b = tau^2 - B h, be = tau^2 - A B, c = tau^3 - A B h.
#   (2) be_a be - c (tau - A) == A tau (tau - B)(tau - h);   (3) be_b be - c (tau - B) == B tau (tau - A)(tau - h).
# Grid {0..5}^4 is unisolvent for polynomials of degree <= 5 in each variable, so agreement on it is a proof of the identities.
bad=0
for tau,h,A,B in itertools.product(range(6),repeat=4):
    bea=tau*tau-A*h; beb=tau*tau-B*h; be=tau*tau-A*B; c=tau**3-A*B*h
    if bea*be-c*(tau-A)!=A*tau*(tau-B)*(tau-h): bad+=1
    if beb*be-c*(tau-B)!=B*tau*(tau-A)*(tau-h): bad+=1
print('|S|=4 (1,1,1,1): identities (2),(3) on the 6^4 grid: mismatches',bad)
# ends: tau = 0 -> (1) 4c = be (tau - h) becomes -4ABh = ABh;  tau = h -> c = 0;  tau = A = B -> be_a be = 0 but be be_a be_b = 4 c^2 != 0.
# Lagrange facts used (k distinct points, om_m = 1/F'(z_m)): sum om z^r = 0 (r <= k-2), = 1 (r = k-1): exact check on random rational points
random.seed(2); badL=0
for k in (4,5):
    for _ in range(50):
        z=random.sample([Fr(a,b) for a in range(-9,10) for b in (1,2,3)],k)
        if len(set(z))<k: continue
        om=[Fr(1)/Fr(__import__('math').prod([z[m]-z[j] for j in range(k) if j!=m])) for m in range(k)]
        for r in range(k):
            s=sum(om[m]*z[m]**r for m in range(k))
            if s!=(1 if r==k-1 else 0): badL+=1
print('Lagrange moment facts (k = 4, 5; 100 random rational point sets): mismatches',badL)
# (2,1,1,1): with XY = XZ = YZ = -2 the cubic class sum needs (1 + XY + XZ + YZ)/4 = 1/4:
print('(2,1,1,1): (1 + XY + XZ + YZ)/4 with XY = XZ = YZ = -2 equals',Fr(1-6,4),' but must equal 1/(om pqr)^2 =',Fr(1,4))
# the product identity behind it: [(1+X)(1+Y)(1+Z) + (1-X)(1-Y)(1-Z)]/8 == (1 + XY + XZ + YZ)/4, and [(1+X)(1+Z)+(1-X)(1-Z)]/4 == (1+XZ)/2
bad2=0
for X,Y,Zv in itertools.product(range(-3,4),repeat=3):
    if Fr((1+X)*(1+Y)*(1+Zv)+(1-X)*(1-Y)*(1-Zv),8)!=Fr(1+X*Y+X*Zv+Y*Zv,4): bad2+=1
    if Fr((1+X)*(1+Zv)+(1-X)*(1-Zv),4)!=Fr(1+X*Zv,2): bad2+=1
print('(2,1,1,1): class-sum product identities on a 7^3 grid: mismatches',bad2)
