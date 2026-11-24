import numpy as np, sys
exec(open('deg2_4.py').read().split("cnt={}")[0].replace("seed,nst=int(sys.argv[1]),int(sys.argv[2]); pat=sys.argv[3] if len(sys.argv)>3 else None","seed,nst,pat=1,0,'+---'"))
rng=np.random.default_rng(7); found=0
for st in range(40):
    x=rng.normal(size=27)+1j*rng.normal(size=27); lam=1e-3; f=res(x); nf=np.linalg.norm(f)
    for it in range(400):
        if nf<1e-14: break
        J=np.zeros((len(f),27),complex)
        for k in range(27):
            e=np.zeros(27,complex); e[k]=1e-7; J[:,k]=(res(x+e)-f)/1e-7
        dx=np.linalg.lstsq(J.conj().T@J+lam*np.eye(27),-J.conj().T@f,rcond=None)[0]; f2=res(x+dx)
        if np.linalg.norm(f2)<nf: x=x+dx; f=f2; nf=np.linalg.norm(f2); lam=max(lam/3,1e-14)
        else: lam*=4
    if nf>1e-11: continue
    B=[x[9*k:9*k+9].reshape(3,3) for k in range(3)]; B.append(2*I-sum(B))
    for j,M in enumerate(B):
        A=(I-M)/2
        print('col %d det %.3f tr B %.4f  sv(A) %s  |B-B^T| %.1e  eig B %s'%(j,np.real(np.linalg.det(M)),np.real(np.trace(M)),np.array2string(np.linalg.svd(A,compute_uv=False),precision=3),np.linalg.norm(M-M.T),np.round(np.linalg.eigvals(M),4)))
    print('---'); found+=1
    if found>=2: break
