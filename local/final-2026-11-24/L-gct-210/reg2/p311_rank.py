# rank of q_Y >= 3 on T_1 for the whole family (3,1|1,1) case A (NOTES-reg2 9.8), WITHOUT computing T_1:
#   S := span(M, d_0, tau) lies in T_1(M) (M: trivially; d_0 in E_0 by Lemma DL, row 0 deletable; tau = J - 5 e_4 1^T always), so
#   rank(q_Y | T_1) >= rank(q_Y | S).  The Gram matrix of q_Y on S is polynomial in (p, w); we show that the 3x3 minors (for two Y) together with
#   w^2 + w + 1 generate the unit ideal over Q (Singular), i.e. rank q >= 3 for EVERY member.  Chart x = (0,1,p,-1-p) ('1') or x = (0,0,1,-1) ('0').
#   Also: exact certificate for the special member of case B (m = (1,w,w^2,0,0), c = 4, x = (0,2,-1,-1), c' = 0, x' = (0,0,1,-1)).
import sys, itertools, subprocess; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2')
import sympy as sp
from dr211_special import perm, bigY, fo_matrix, hessian, ys
p,w=sp.symbols('p w')
def famA(chart,wv):
    m=[1,wv,-1-wv,0,0]
    xs=[1,p] if chart=='1' else [0,1]
    x=[0,xs[0],xs[1],-xs[0]-xs[1]]; xp=[0,x[2]-x[3],x[3]-x[1],x[1]-x[2]]
    return m,3,x,4,xp
def basis(m,c,x,cp,xp):
    Z=lambda: sp.zeros(4,5); B=[]
    for k in (1,2,3):
        b=Z(); b[0,0]=m[k]; b[0,k]=-1; b[0,4]=1-m[k]; B.append(b)
    b=Z()
    for j in range(5): b[1,j]=m[j]
    B.append(b)
    b=Z()
    for i in range(4): b[i,c]=x[i]
    B.append(b)
    b=Z()
    for i in range(4): b[i,cp]=xp[i]
    B.append(b)
    return B
def emb(X4):
    E=sp.zeros(5,5); E[:4,:]=X4; return E
mode=sys.argv[1] if __name__=="__main__" else ""
if mode in ('A1','A0'):
    B=basis(*famA(mode[1],w))
    d0=sp.ones(4,5)*sp.Rational(-1,4); d0[0,:]=sp.ones(1,5)*sp.Rational(3,4)
    tau=sp.ones(5,5); tau[4,:]=sp.ones(1,5)*(-4)
    S=[emb(b) for b in B]+[emb(d0),tau]
    vec=lambda E: sp.Matrix(25,1,lambda k,_: E[k//5,k%5])
    Sm=sp.Matrix.hstack(*[vec(E) for E in S]).T          # 8 x 25
    minors=[]
    for yv in [(1,2,-1,3,1,-2),(2,-1,1,1,-3,1)]:
        H=hessian(B,yv); G=(Sm*H*Sm.T).applyfunc(lambda e: sp.rem(sp.expand(e),w**2+w+1,w))
        for I in itertools.combinations(range(8),3):
            for J in itertools.combinations(range(8),3):
                if J<I: continue
                d=sp.expand(G.extract(list(I),list(J)).det(method='berkowitz'))
                if d!=0: minors.append(d)
        print('Y=%s: %d nonzero 3x3 minors'%(str(yv),len(minors)),flush=True)
    vs='p,w' if mode=='A1' else 'w'
    gens=[str(sp.expand(d)).replace('**','^') for d in minors[:400]]+['w^2+w+1']
    open('/tmp/p311rank.sing','w').write('ring R=0,(%s),dp;\noption(redSB);\nideal I=%s;\nideal G=std(I);\nprint(G);\nquit;\n'%(vs,',\n'.join(gens)))
    r=subprocess.run(['/usr/bin/Singular','-q'],stdin=open('/tmp/p311rank.sing'),capture_output=True,text=True,timeout=900)
    print('ideal of 3x3 minors of q on span(M,d_0,tau) + (w^2+w+1):',' '.join(r.stdout.split())[:200])
elif mode=='Bpt':
    wv=sp.Rational(-1,2)+sp.sqrt(-3)/2
    B=basis([1,wv,sp.expand(wv**2),0,0],4,[0,2,-1,-1],0,[0,0,1,-1])
    A5=sp.ones(5,5)+bigY(B); print('level identity:',sp.expand(perm(A5)-120)==0,flush=True)
    A=fo_matrix(B); K=sp.QQ.algebraic_field(sp.sqrt(-3))
    dm=sp.polys.matrices.DomainMatrix.from_Matrix(A).convert_to(K); rk=dm.rank(); N=dm.nullspace().to_Matrix()
    best=0
    for yv in [(1,2,-1,3,1,-2),(2,-1,1,1,-3,1)]:
        H=hessian(B,yv); Q=(N*H*N.T).applyfunc(sp.expand)
        best=max(best,sp.polys.matrices.DomainMatrix.from_Matrix(Q).convert_to(K).rank())
    print('dim T_1 =',25-rk,' rank q =',best,' => dim L <=',N.shape[0]-(best+1)//2)
