"""3-row DC level spaces u(x)W1 + conj(u)(x)W2, W_i = span of Z_n characters S_i (u = cube roots on 3 rows).
Level iff S1+S2 has no 0, and no 3-multiset of S1 (resp. S2) sums to 0 mod n. Max |S1|+|S2| (L157: <= n-1)."""
import itertools
def ok3(S,n): return all((a+b+c)%n for a,b,c in itertools.combinations_with_replacement(S,3))
for n in range(3,14):
    nz=list(range(1,n)); best=(0,None)
    for mask in range(3**(n-1)):
        S1=[];S2=[];m=mask
        for k in nz:
            r=m%3; m//=3
            if r==1: S1.append(k)
            elif r==2: S2.append(k)
        if len(S1)+len(S2)<=best[0]: continue
        if any((a+b)%n==0 for a in S1 for b in S2): continue
        if ok3(S1,n) and ok3(S2,n): best=(len(S1)+len(S2),(S1,S2))
    print('n',n,'max dim',best[0],'(n-1 =',n-1,')',best[1])
