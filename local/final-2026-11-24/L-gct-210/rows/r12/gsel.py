# choose a valid gauge for kgen spec S+/S- at a numeric special point mod p (rows, round 13)
import sys
P=int(sys.argv[1]); s3=int(sys.argv[2])%P; ii=int(sys.argv[3])%P; eps=int(sys.argv[4]); cj=int(sys.argv[5]); es=1 if sys.argv[6]=='+' else -1
inv=lambda a: pow(a%P,P-2,P)
H=[[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]]
ga=eps*(1+s3)*((1-ii) if cj else (1+ii))*inv(2)%P; al=(-2+s3)*ga%P
uW=[(al*al-1)%P,ii*(al*al+1)%P,2*al%P]; dW=[(ga*ga-1)%P,ii*(ga*ga+1)%P,2*ga%P]
rA=[2,3,5]; rB=[3,-7,2]
cr=lambda a,b:[(a[1]*b[2]-a[2]*b[1])%P,(a[2]*b[0]-a[0]*b[2])%P,(a[0]*b[1]-a[1]*b[0])%P]
dt=lambda a,b:sum(x*y for x,y in zip(a,b))%P
pW=[x*inv(ii*dt(uW,rA))%P for x in cr(uW,rA)]; eW=[es*x*inv(ii*dt(dW,rB))%P for x in cr(dW,rB)]
M=lambda w:[sum(H[i][k]*w[k] for k in range(3))%P for i in range(4)]
u,d,p,e=M(uW),M(dW),M(pW),M(eW)
K=[[(u[i],u[i]) for i in range(4)],[((p[i]+e[i])%P,(p[i]-e[i])%P) for i in range(4)],[(d[i],(-d[i])%P) for i in range(4)]]
G=[[(0,0),(1,0),(0,1)],[(2,0),(3,0),(2,1)],[(0,0),(2,0),(1,1)],[(1,0),(3,0),(3,1)]]
def det3(m): return (m[0][0]*(m[1][1]*m[2][2]-m[1][2]*m[2][1])-m[0][1]*(m[1][0]*m[2][2]-m[1][2]*m[2][0])+m[0][2]*(m[1][0]*m[2][1]-m[1][1]*m[2][0]))%P
for gc,g in enumerate(G):
    m=[[K[r][i][j] for (i,j) in g] for r in range(3)]
    if det3(m)!=0: print(gc); break
else: print(-1)
