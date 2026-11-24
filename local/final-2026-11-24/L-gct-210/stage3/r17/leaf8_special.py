import numpy as np, itertools
exec(open('/home/kevxhk/work/L-gct-210/stage3/r17/leaf8_31.py').read().split('rg=np.random')[0])
def kd(m):
    V=np.array([m**t for t in range(4)]); w=np.linalg.svd(V)[2][-1].conj()
    rows_sr=[m,m,m,w]; out=[]
    for r,k in itertools.combinations(range(4),2):
        l,n=[i for i in range(4) if i not in (r,k)]; A=[]
        for t in range(5):
            for T in itertools.combinations(range(4),t):
                Dv=delv(np.array([rows_sr[i] for i in T]).reshape(len(T),5))
                A.append(np.concatenate([Dv,Dv*(l not in T),Dv*(n not in T)]))
        sv=np.linalg.svd(np.array(A),compute_uv=False); out.append(15-int((sv>1e-9*sv[0]).sum()))
    R1=np.linalg.matrix_rank(np.array([m,m**2,m**3,w*m**2,w*m**3]),1e-9); R2=np.linalg.matrix_rank(np.array([m,m**2,w*m,w*m**2]),1e-9)
    return out,R1,R2
for nm,co in (('alpha=0 (Fourier m)',[1,0,0,0,0,-1]),('beta=0 (zero entry)',[1,0,0,0,-1,0]),('generic',[1,0,0,0,0.7+0.2j,-1.3])):
    m=np.roots(co); print(nm,'kernel dims per pair, R1 rank, R2 rank:',kd(m))
# scan for R2/R1 drop along j = alpha^5/beta^4: beta = 1, alpha on a grid; report minimal 3rd/4th singular values
best=[]
for al in np.linspace(-3,3,121):
    for im in np.linspace(-3,3,121):
        m=np.roots([1,0,0,0,al+1j*im,1.0]); V=np.array([m**t for t in range(4)]); w=np.linalg.svd(V)[2][-1].conj()
        s2=np.linalg.svd(np.array([m,m**2,w*m,w*m**2]),compute_uv=False); s1=np.linalg.svd(np.array([m,m**2,m**3,w*m**2,w*m**3]),compute_uv=False)
        best.append((s2[2]/s2[0],s1[3]/s1[0],al,im))
best.sort(); print('smallest R2 ratios:',[tuple(np.round(b,3)) for b in best[:3]])
best.sort(key=lambda b:b[1]); print('smallest R1 ratios:',[tuple(np.round(b,3)) for b in best[:3]])
