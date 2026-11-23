import itertools, math
def perm(A):
    n=len(A); s=0
    for p in itertools.permutations(range(n)):
        pr=1
        for i in range(n): pr*=A[i][p[i]]
        s+=pr
    return s
val={0:1,1:1j,2:-1j,3:-1}
for n in (5,6):
    t=[[0]*n for _ in range(n)]
    for i in range(4):
        for j in range(4): t[i][j]=val[(j-i)%4]
    errs=[abs(perm([[1+c*t[i][j] for j in range(n)] for i in range(n)])-math.factorial(n)) for c in (0.7,-1.3+2j,3j)]
    print(n,'max err',max(errs),'DC',max(abs(sum(r)) for r in t),max(abs(sum(t[i][j] for i in range(n))) for j in range(n)),
          'p_k k=2..5',[sum(t[i][j]**k for i in range(n) for j in range(n)) for k in range(2,6)])
