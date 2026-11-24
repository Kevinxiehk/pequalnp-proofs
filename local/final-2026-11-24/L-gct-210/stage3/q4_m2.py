import itertools, random
from fractions import Fraction
# Is the restriction map (multilinear forms on P_a x P_b x P_c x P_d) -> (quartics on L_e) injective for the normal form of L_e
# when m_ab = 2 (Y_ab = graph of phi), lines x^{ac}, x^{ad}, x^{cd}?  L_e = { xi_a = v + al p_ac + be p_ad, xi_b = phi v,
# xi_c = al p_ca + ga p_cd, xi_d = be p_da + ga p_dc }.  Coordinates: xi_i in C^2 w.r.t. the indicated bases.
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
def test(param,nvar,npts=90,seed=1):
    rnd=random.Random(seed); pts=[[Fraction(rnd.randint(-9,9)) for _ in range(nvar)] for _ in range(npts)]
    rows=[]
    for eps in itertools.product(range(2),repeat=4):
        row=[]
        for t in pts:
            a,b,c,d=param(t); row.append(a[eps[0]]*b[eps[1]]*c[eps[2]]*d[eps[3]])
        rows.append(row)
    return rank(rows)
# generic case: p_ac, p_ad independent in P_a; p_ca, p_cd independent in P_c; p_da, p_dc independent in P_d
gen=lambda t:((t[0]+t[2],t[1]+t[3]),(t[0],t[1]),(t[2],t[4]),(t[3],t[4]))
print('m_ab = 2, no triangle: rank of the 16 products on L_e =',test(gen,5))
# triangle acd: p_ac || p_ad, p_ca || p_cd, p_da || p_dc; then x^{cd} = x^{ac} - x^{ad}; L_e = Y_ab + C x^{ac} + C x^{ad} + C zeta,
# zeta a further element with rows (w_a, 0, s_c, s_d) (general position): xi_a = v + (al+be) p + de w, xi_c = al q + de s_c, xi_d = be r + de s_d
tri=lambda t:((t[0]+t[2]+t[3],t[1]+t[4]),(t[0],t[1]),(t[2],t[4]),(t[3],t[4]))
print('m_ab = 2, triangle acd (one normal form): rank =',test(tri,5))
# minimal case, non-collapsed, for comparison: L_e spanned by x^{ab},x^{ac},x^{ad},x^{bc},x^{bd} with generic marked vectors
import random as R
R.seed(3); g=lambda: Fraction(R.randint(-5,5))
pv={(i,k):(g(),g()) for i in range(4) for k in range(4) if i!=k}
def mn(t):
    xs=[(0,1),(0,2),(0,3),(1,2),(1,3)]; rows=[[Fraction(0),Fraction(0)] for _ in range(4)]
    for co,(i,k) in zip(t,xs):
        for (r,s) in ((i,k),(k,i)):
            rows[r][0]+=co*pv[(r,s)][0]; rows[r][1]+=co*pv[(r,s)][1]
    return tuple(tuple(r) for r in rows)
print('minimal case, 5 generic lines spanning L_e: rank =',test(mn,5))
# triangle acd with the extra element zeta having row a parallel to p (after reparametrisation w = 0)
tri0=lambda t:((t[0]+t[2]+t[3],t[1]),(t[0],t[1]),(t[2],t[4]),(t[3],t[4]))
print('m_ab = 2, triangle acd, zeta_a in C p: rank =',test(tri0,5))
# two disjoint pairs with m = 2 inside the 4-set: L_e = Y_ab + Y_cd + C zeta, zeta = (w,0,s,0), bases with w = e1, s = e1
two=lambda t:((t[0]+t[4],t[1]),(t[0],t[1]),(t[2]+t[4],t[3]),(t[2],t[3]))
print('m_ab = m_cd = 2: rank =',test(two,5))
