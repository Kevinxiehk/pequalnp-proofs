import sys, numpy as np, itertools
np.set_printoptions(precision=3,suppress=True,linewidth=220)
def rank(M,tol=1e-6):
    s=np.linalg.svd(np.atleast_2d(M),compute_uv=False); return int((s>tol*max(1,s[0])).sum())
S=np.load(sys.argv[1]); shown=0
for x in S:
    z=x[:45]+1j*x[45:]; A=z[:40].reshape(4,2,5); w=z[40:45]
    if int((np.abs(w)>1e-5).sum())!=int(sys.argv[2]): continue
    shown+=1
    if shown>int(sys.argv[3]): break
    print('== w =',np.round(w,3),' ratio of the two nonzero entries:',np.round((lambda v:v[1]/v[0])(w[np.abs(w)>1e-5]),3) if (np.abs(w)>1e-5).sum()==2 else '')
    for i in range(4):
        P=A[i]; cn=np.linalg.norm(P,axis=0)
        # reduced row echelon-like description: project out w if w in P
        inw=rank(np.vstack([P,w[None]]))==2
        print('   P_%s: column norms'%'abcd'[i],np.round(cn,3),' contains w:',inw,' unit vectors in P:',[j for j in range(5) if rank(np.vstack([P,np.eye(5)[j][None]]))==2],
              ' coordinate-plane?',int((cn>1e-5).sum())==2)
    print('   equal pairs:',[('abcd'[i],'abcd'[k]) for i in range(4) for k in range(i) if rank(np.vstack([A[i],A[k]]))==2],
          ' pairs meeting:',[('abcd'[i]+'abcd'[k]) for i in range(4) for k in range(i) if rank(np.vstack([A[i],A[k]]))==3],
          ' dim of sum of all planes + w:',rank(np.vstack([A.reshape(8,5),w[None]])))
