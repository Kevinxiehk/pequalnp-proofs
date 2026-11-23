import itertools
val={0:1,1:1j,2:-1j,3:-1}
n=4
t=[[val[(j-i)%4] for j in range(n)] for i in range(n)]
def perm(A):
    n=len(A); s=0
    for p in itertools.permutations(range(n)):
        pr=1
        for i in range(n): pr*=A[i][p[i]]
        s+=pr
    return s
for c in [0.3,1.7,-2+1j]:
    print('perm(J+ct)=',perm([[1+c*t[i][j] for j in range(n)] for i in range(n)]))
print('rows',[sum(r) for r in t],'cols',[sum(t[i][j] for i in range(n)) for j in range(n)])
for k in range(2,6): print('p',k,sum(t[i][j]**k for i in range(n) for j in range(n)))
