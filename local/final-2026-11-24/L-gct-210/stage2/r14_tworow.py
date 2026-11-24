# Exact test of the TWO-ROW case of target 2 [NOTES R14-3]: P = {(A, mu(A) m - A)} on rows a,b (row c zero), A in a 2-dim space Acal of C^5.
# Level of X = P + e_i (x) Z  <=>  (E1) <A,B> = -sigma_A^2  and  (E2) -A o A + sigma_A A + mu(A) m o A  in span(1,m)  (quadratic in A), polarised.
# Chart: Acal = rowspace [[1,0,x1,x2,x3],[0,1,y1,y2,y3]] after a column permutation (all 10 charts by S_5 on columns), m = (m0,m1,m2,m3,1),
# m0 = -(1+m1+m2+m3) (chart m_4 = 1; the remaining charts m_k = 1 are covered by the column permutations ... see notes), msolve mod p.
import sys, itertools, subprocess, os, re, sympy as sp
p=int(sys.argv[1]) if len(sys.argv)>1 else 2147483629
x=sp.symbols('x1:4'); y=sp.symbols('y1:4'); mu1,mu2=sp.symbols('mu1 mu2'); m1,m2,m3=sp.symbols('m1 m2 m3')
al=sp.symbols('al11 al22 al12'); be=sp.symbols('be11 be22 be12')
def run(chart_cols, mpos):
    # A1, A2 with identity in columns chart_cols
    rest=[c for c in range(5) if c not in chart_cols]
    A1=[0]*5; A2=[0]*5; A1[chart_cols[0]]=1; A2[chart_cols[1]]=1
    for i,c in enumerate(rest): A1[c]=x[i]; A2[c]=y[i]
    mm=[None]*5; others=[k for k in range(5) if k!=mpos]
    mm[mpos]=sp.Integer(1); free=[m1,m2,m3]
    for i,k in enumerate(others[:3]): mm[k]=free[i]
    mm[others[3]]=-(1+m1+m2+m3)
    A=[A1,A2]; mu=[mu1,mu2]; B=[[mu[s]*mm[j]-A[s][j] for j in range(5)] for s in range(2)]
    sg=[sum(A[s]) for s in range(2)]
    eqs=[]
    for (s,t),k in zip([(0,0),(1,1),(0,1)],range(3)):
        eqs.append(sp.expand(sum(A[s][j]*B[t][j]+A[t][j]*B[s][j] for j in range(5))+2*sg[s]*sg[t]))
        W=[-2*A[s][j]*A[t][j]+sg[s]*A[t][j]+sg[t]*A[s][j]+mu[s]*mm[j]*A[t][j]+mu[t]*mm[j]*A[s][j] for j in range(5)]
        for j in range(5): eqs.append(sp.expand(W[j]-al[k]-be[k]*mm[j]))
    vs=list(x)+list(y)+[mu1,mu2,m1,m2,m3]+list(al)+list(be)
    def msstr(e):
        P=sp.Poly(e,*vs); terms=[]
        for mon,c in P.terms():
            c=int(c)%p
            if c==0: continue
            mono='*'.join('%s^%d'%(v,k) if k>1 else str(v) for v,k in zip(vs,mon) if k>0)
            terms.append(str(c)+('*'+mono if mono else ''))
        return '+'.join(terms) if terms else '0'
    fn='/tmp/st2_tworow.ms'; out='/tmp/st2_tworow.out'
    if os.path.exists(out): os.remove(out)
    open(fn,'w').write(','.join(map(str,vs))+'\n'+str(p)+'\n'+',\n'.join(msstr(e) for e in eqs if e!=0)+'\n')
    subprocess.run('ulimit -v 2000000; msolve -g 2 -t 1 -f %s -o %s > /dev/null 2>&1'%(fn,out),shell=True)
    res=open(out).read() if os.path.exists(out) else ''
    body=''.join(l for l in res.splitlines() if not l.startswith('#'))
    st='UNIT' if re.sub(r'\s','',body)=='[1]:' else ('FAILED' if body.strip()=='' else 'NONUNIT: '+body[:300])
    print('Acal chart',chart_cols,'m chart m_%d = 1:'%mpos,st,flush=True)
for cc in itertools.combinations(range(5),2):
    for mpos in range(5):
        run(cc,mpos)
