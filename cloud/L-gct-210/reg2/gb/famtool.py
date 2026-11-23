# Generic exact tool for a parametrised family of 4x5 spaces M(p) = span(B_1(p),..,B_d(p)):
#   level equations  (coefficients in y of F(J' + sum y_k B_k) - 120),
#   FO equations     (coefficients in y of D_t perm(J + (Y;0)), t = (X ; rho) unknown),
#   then unit-ideal tests in charts with msolve (prime) or Singular (0 = exact over Q).
import sys, itertools, time; sys.path.insert(0,'/home/claude/work/L-gct-210/reg2/gb')
from polylib import *
P5=list(itertools.permutations(range(5)))
class Family:
    def __init__(self,params,basis_fn,d):
        """params: list of names; basis_fn(R, V) -> list of d matrices (4x5) of polys in the ring R (which also has y, x, r)"""
        self.params=list(params); self.d=d
        self.ys=['y%d'%i for i in range(1,d+1)]
        self.xv=['x%d%d'%(i,j) for i in range(4) for j in range(5)]; self.rv=['r%d'%j for j in range(5)]
        self.R=Ring(self.ys+self.params+self.xv+self.rv); R=self.R; V=R.var; one=R.const(1)
        B=basis_fn(R,V); assert len(B)==d
        A=[[one for _ in range(5)] for _ in range(5)]
        for k in range(d):
            yk=V(self.ys[k])
            for i in range(4):
                for j in range(5):
                    if B[k][i][j]: A[i][j]=add(A[i][j],mul(yk,B[k][i][j]))
        self.A=A
        # level polynomial = perm of A (row 4 = ones) expanded along row 4: sum_j cof_{4j}
        cof={}
        for i in range(5):
            for j in range(5):
                cof[(i,j)]=perm4([[A[a][b] for b in range(5) if b!=j] for a in range(5) if a!=i])
        lev=R.const(-120)
        for j in range(5): lev=add(lev,cof[(4,j)])
        FO={}
        for i in range(5):
            for j in range(5):
                tv=V('x%d%d'%(i,j)) if i<4 else V('r%d'%j); FO=add(FO,mul(cof[(i,j)],tv))
        ny=d; self.names=R.names[ny:]; strip=lambda q:{k[ny:]:v for k,v in q.items()}
        self.level=[strip(q) for q in coeffs_wrt(lev,R,self.ys).values()]; self.level=[q for q in self.level if q]
        self.fo=[strip(q) for q in coeffs_wrt(FO,R,self.ys).values()]
        self.R2=Ring(self.names)
    def W(self,n): return self.R2.var(n)
    def c(self,v): return self.R2.const(v)
    def eq(self,name,val): return add(self.W(name),self.c(-val))
    def run(self,extra,p,tag,fo=True,timeout=110):
        polys=self.level+(self.fo if fo else [])+extra
        if p==0: return run_singular(polys,self.names,tag,timeout=timeout)
        return run_msolve(polys,self.names,p,tag,timeout=timeout)
