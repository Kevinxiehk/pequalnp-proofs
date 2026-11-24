import sys, time; sys.path.insert(0,'/home/kevxhk/work/L-gct-086/smallcases')
import level
A=[2,-1,-1]; b=[0,1,-1]; p,q=0,3
def basis(c):
    B=[]
    M=[[0]*5 for _ in range(5)]
    for i in range(3): M[i][p]=A[i]; M[i][q]=2*c*b[i]
    B.append(M)
    M=[[0]*5 for _ in range(5)]
    for i in range(3): M[i][p]=-3*b[i]; M[i][q]=2*c*A[i]
    B.append(M)
    for j in range(4):
        M=[[0]*5 for _ in range(5)]; M[3][j]=1; M[3][4]=-1; B.append(M)
    M=[[0]*5 for _ in range(5)]
    for i in range(3): M[i][4]=1
    M[4][4]=-3; B.append(M)
    return B
for c in [int(x) for x in sys.argv[1:]]:
    t0=time.time(); print('c =',c,level.check_exact(basis(c),5),f'{time.time()-t0:.0f}s',flush=True)
