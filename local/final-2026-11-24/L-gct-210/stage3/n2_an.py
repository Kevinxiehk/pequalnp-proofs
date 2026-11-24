import sys, glob, itertools
import numpy as np
np.set_printoptions(precision=3,suppress=True,linewidth=200)
def rank(A,tol=1e-7):
    s=np.linalg.svd(np.atleast_2d(A),compute_uv=False); return int((s>tol*max(1,s[0])).sum())
TR=list(itertools.product(range(2),repeat=3)); K3=list(itertools.combinations(range(5),3))
for fn in sorted(glob.glob(sys.argv[1]))[:int(sys.argv[2])]:
    x=np.load(fn); z=x[:37]+1j*x[37:74]
    Ac,Ad,Ae,rho,w=z[:10].reshape(5,2),z[10:20].reshape(5,2),z[20:30].reshape(5,2),z[30:35],z[35:37]
    print('==',fn)
    print(' |rho_j|',np.abs(rho),' |w|',np.abs(w))
    for nm,A in (('c',Ac),('d',Ad),('e',Ae)): print('  P_'+nm,'row norms per column',np.round(np.linalg.norm(A,axis=1),3))
    print('  dim P_c+P_d, P_c+P_e, P_d+P_e, sum of all:',rank(np.hstack([Ac,Ad])),rank(np.hstack([Ac,Ae])),rank(np.hstack([Ad,Ae])),rank(np.hstack([Ac,Ad,Ae])),
          ' dim span(P_c+P_d+P_e, rho):',rank(np.hstack([Ac,Ad,Ae,rho[:,None]])))
    Wm=[]
    for (ec,ed,ee) in TR:
        y=[Ac[:,ec],Ad[:,ed],Ae[:,ee]]
        Wm.append([sum(np.prod([y[i][K[p[i]]] for i in range(3)]) for p in itertools.permutations(range(3))) for K in K3])
    Wm=np.array(Wm); u,s,vh=np.linalg.svd(Wm); dW=int((s>1e-7*s[0]).sum())
    Bs=[]
    for k in range(dW):
        B=np.zeros((5,5),complex)
        for n,K in enumerate(K3):
            j,l=[c for c in range(5) if c not in K]; B[j,l]=B[l,j]=vh[k,n]
        Bs.append(B)
    ker=5-rank(np.vstack(Bs))
    print('  dim W',dW,' ranks of B_w:',[rank(B) for B in Bs],' dim of common kernel of the B_w:',ker)
    # sigma, Gram data
    print('  sigma (c,d,e):',Ac.sum(0),Ad.sum(0),Ae.sum(0))
    # elements of X_ab-type space in L_a; single-row check not needed.  P_i cap P_k:
    def inter(A,B): return 4-rank(np.hstack([A,B]))
    print('  dim P_c cap P_d, P_c cap P_e, P_d cap P_e:',inter(Ac,Ad),inter(Ac,Ae),inter(Ad,Ae))
    j=int(np.argmax(np.abs(rho))); ej=np.eye(5)[j]
    vs=[]
    for nm,A in (('c',Ac),('d',Ad),('e',Ae)):
        v,res,_,_=np.linalg.lstsq(A,ej.astype(complex),rcond=None); vs.append(v)
        print('   e_j in P_'+nm+': residual %.1e'%np.linalg.norm(A@v-ej),' preimage v =',v)
    def par(u,v): return abs(u[0]*v[1]-u[1]*v[0])/(np.linalg.norm(u)*np.linalg.norm(v))
    print('   non-parallelism (0 = parallel): v_c vs v_d %.1e, v_c vs v_e %.1e, v_c vs w %.1e'%(par(vs[0],vs[1]),par(vs[0],vs[2]),par(vs[0],w)),' ratios v_d/v_c, v_e/v_c, w/v_c:',vs[1][0]/vs[0][0],vs[2][0]/vs[0][0],w[0]/vs[0][0],' rho_j =',rho[j])
