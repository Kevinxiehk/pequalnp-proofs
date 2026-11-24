# case (a) of C3: L' = {(a chi^T | x) : a in C^S, x in 1^perp}, chi = (1,i,-1,-i): level? defect dim?
import sys, numpy as np
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/handoff')
import oracle
chi=np.array([1,1j,-1,-1j])
B=[]
for i in range(3):
    Y=np.zeros((4,5),complex); Y[i,:4]=chi; B.append(Y)
for k in range(3):
    x=np.zeros(4,complex); x[k]=1; x[3]=-1
    Y=np.zeros((4,5),complex); Y[:,4]=x; B.append(Y)
B=np.array(B)
np.save('caseA_chi.npy',B)
print(oracle.analyse_4x5(B))
