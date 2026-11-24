import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-086/smallcases')
import level
class Zw:
    # a + b*w, w^2 = -1 - w
    __slots__=('a','b')
    def __init__(s,a=0,b=0): s.a=a; s.b=b
    def _c(o): return o if isinstance(o,Zw) else Zw(o,0)
    def __add__(s,o): o=Zw._c(o); return Zw(s.a+o.a,s.b+o.b)
    __radd__=__add__
    def __neg__(s): return Zw(-s.a,-s.b)
    def __sub__(s,o): return s+(-Zw._c(o))
    def __rsub__(s,o): return Zw._c(o)-s
    def __mul__(s,o):
        o=Zw._c(o); # (a+bw)(c+dw)=ac+(ad+bc)w+bd w^2 = (ac-bd)+(ad+bc-bd)w
        return Zw(s.a*o.a-s.b*o.b, s.a*o.b+s.b*o.a-s.b*o.b)
    __rmul__=__mul__
    def __eq__(s,o): o=Zw._c(o); return s.a==o.a and s.b==o.b
    def __ne__(s,o): return not s.__eq__(o)
    def __repr__(s): return f'({s.a}+{s.b}w)'
W=[Zw(1),Zw(0,1),Zw(-1,-1)]  # 1, w, w^2
def zero(): return [[Zw(0) for _ in range(5)] for _ in range(5)]
B=[]
M=zero()
for i in range(3): M[i][0]=W[i]; M[i][1]=-W[i]
B.append(M)
M=zero()
for i in range(3): M[i][2]=W[(2*i)%3]; M[i][3]=-W[(2*i)%3]
B.append(M)
for j in range(4):
    M=zero(); M[3][j]=Zw(1); M[3][4]=Zw(-1); B.append(M)
M=zero()
for i in range(3): M[i][4]=Zw(1)
M[4][4]=Zw(-3); B.append(M)
print(level.check_exact(B,5))
