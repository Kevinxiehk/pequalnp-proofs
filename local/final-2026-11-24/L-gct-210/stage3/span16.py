import numpy as np, itertools
# In P_a(x)P_b(x)P_c(x)P_d (each P_i = C^2): W_ab = p_ab(x)p_ba(x)P_c(x)P_d etc. for the six pairs. Dimension of the sum
# when the three marked vectors in each P_i are pairwise independent (normal form e1, e2, e1+e2), and for coincidences.
e1=np.array([1.,0]); e2=np.array([0,1.]); I2=np.eye(2)
def span_dim(marks):
    # marks[i][k] = marked vector in P_i towards partner k (i,k in 0..3, k != i)
    vecs=[]
    for i,k in itertools.combinations(range(4),2):
        for f1 in I2:
            for f2 in I2:
                fac=[None]*4; fac[i]=marks[i][k]; fac[k]=marks[k][i]
                rest=[x for x in range(4) if x not in (i,k)]; fac[rest[0]]=f1; fac[rest[1]]=f2
                t=fac[0]
                for f in fac[1:]: t=np.tensordot(t,f,0)
                vecs.append(t.reshape(-1))
    return np.linalg.matrix_rank(np.array(vecs),tol=1e-9)
rng=np.random.default_rng(0)
gen=[{k:rng.normal(size=2) for k in range(4) if k!=i} for i in range(4)]
print('generic marked vectors: dim span =',span_dim(gen),'of 16')
# one coincidence: in P_0 the vectors towards 1 and 2 are proportional
m=[dict(d) for d in gen]; m[0][2]=2.5*m[0][1]; print('p_01 || p_02:',span_dim(m))
# triangle 0,1,2: p_01||p_02, p_10||p_12, p_20||p_21
m=[dict(d) for d in gen]; m[0][2]=m[0][1]; m[1][2]=m[1][0]; m[2][1]=m[2][0]; print('triangle on rows 0,1,2:',span_dim(m))
# all three marked vectors proportional in P_0
m=[dict(d) for d in gen]; m[0][2]=m[0][1]; m[0][3]=m[0][1]; print('all three proportional in P_0:',span_dim(m))
m=[dict(d) for d in gen]; 
for i in range(4):
    ks=[k for k in range(4) if k!=i]; m[i][ks[1]]=m[i][ks[0]]; m[i][ks[2]]=m[i][ks[0]]
print('all proportional in every P_i:',span_dim(m))
