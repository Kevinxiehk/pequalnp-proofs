# General symmetry cut [NOTES-stage2 R16-5/R17]. Projective n = (a1,a2,a3,a4) (Z-normal, column-0 entry 0, chart a4 = 1 <-> n4 != 0).
# Given an INVARIANT ambient linear subspace AMB, a list of survivor PIECES (each: list of homogeneous linear forms, or a point), and a group G of
# coordinate permutations preserving AMB and the family, a survivor n with sigma(n) in the chart for every sigma (i.e. n_j != 0 for all j moved to
# position 4 by G) lies in INTERSECTION_{sigma in G} sigma^{-1}(union of pieces). Output: the components (exact, over Q), each tagged with whether it
# satisfies the chart condition (no zero coordinate among the positions G moves to 4).
import sys, itertools, sympy as sp
a=sp.symbols('a1:5')
def ptlin(p): return [a[i]*p[j]-a[j]*p[i] for i in range(4) for j in range(i+1,4)]
def run(name, amb, pieces, group, chartpos):
    res={}
    def act(eqs,s): return [e.xreplace({a[i]:a[s[i]] for i in range(4)}) for e in eqs]
    seen=set()
    def dfs(k,eqs,tag):
        M=sp.Matrix([[sp.Poly(e,*a).coeff_monomial(v) for v in a] for e in eqs]) if eqs else sp.zeros(0,4)
        r=M.rank() if eqs else 0
        if r==4: return
        if eqs:
            Rr=M.rref()[0]; eqs=[sum(Rr[i,j]*a[j] for j in range(4)) for i in range(r)]
            st=(k,str(Rr[:r,:].tolist()))
            if st in seen: return
            seen.add(st)
        if k==len(group):
            ns=M.nullspace() if eqs else [sp.eye(4).col(i) for i in range(4)]
            B=sp.Matrix.hstack(*ns).T.rref()[0]; key=str(B.tolist())
            res.setdefault(key,(3-r,B,tag)); return
        for pn,pe in pieces.items(): dfs(k+1,eqs+act(pe,group[k]),tag+(pn,))
    dfs(0,list(amb),())
    print('==== cut:',name,'| ambient',amb,'| group size',len(group),flush=True)
    for key,(d,B,tag) in sorted(res.items(),key=lambda x:(x[1][0],x[0])):
        # chart condition: a generic point of the component has nonzero coordinates at chartpos
        gen=sum((sp.Symbol('t%d'%i)*B.row(i) for i in range(B.rows)),sp.zeros(1,4))
        ok=all(sp.expand(gen[j])!=0 for j in chartpos)
        print('  dim %d %s span %s'%(d,'IN-REGION ' if ok else 'boundary  ',B.tolist()),flush=True)
S3=[ (0,)+tuple(p) for p in itertools.permutations([1,2,3])]
S4=list(itertools.permutations(range(4)))
H=[a[0]+2*a[1]+2*a[2]-6*a[3]]; A=[a[0]]; D=[a[0]+a[1]+a[2]-4*a[3]]; J=[a[0]+a[1]+a[2]+a[3]]
P01={'P%d'%i:ptlin(p) for i,p in enumerate([(1,0,0,1),(1,0,1,1),(1,1,0,1),(1,1,1,1)])}
if __name__=='__main__':
    which=sys.argv[1] if len(sys.argv)>1 else 'all'
    if which in ('nu0','all'):   # nu = 0 slice: pieces of the nu = 0 family (H, A, D, J0 = jump plane, 0/1 points)
        run('nu=0 slice',[],dict(H=H,A=A,D=D,J0=J,**P01),S3,[1,2,3])
    if which in ('J0','all'):    # inside J0 = {nu=0, a1+a2+a3+a4 = 0}: jump-type survivors a2+a3 = 7 a4, exceptional a1 = 0 (Deg added when known)
        run('J0',J,dict(S=[a[1]+a[2]-7*a[3]],A=A),S3,[1,2,3])
    if which in ('JA','all'):    # inside J_A = {a1 = 0, a2+a3+a4 = 0}: jump-type survivors a3 = 7 a4 (tree), exceptional from its setup (none linear)
        run('J_A',[a[0],a[1]+a[2]+a[3]],dict(S=[a[2]-7*a[3]]),S3,[1,2,3])
    if which in ('jump','all'):  # cross-type jump plane {sum a = 0} with S_4: survivors a1 = -8 a4, a1 = 0
        run('jump plane (S_4)',J,dict(S=[a[0]+8*a[3]],A=A),S4,[0,1,2,3])
