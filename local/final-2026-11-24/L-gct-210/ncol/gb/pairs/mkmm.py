# export multiplication matrices of the 12 variables on the standard-monomial basis of A = F_p[t]/(G) and NF(det M), sparse, for numpy.
# usage: python3 -I mkmm.py q_CHART.sing mm_CHART.sing OUTPREFIX
import sys
src,out,pre=sys.argv[1:4]
L=open(src).read().split('\n')
cut=[i for i,l in enumerate(L) if l.startswith('"DET_IS_ZERO_IN_QUOTIENT"')][0]
L=L[:cut]+['''ideal B = kbase(G); int n = size(B); int r; int k; int v; poly f; poly m; intvec ev;
link lb = ":w %s.basis"; for(r=1;r<=n;r++){ ev = leadexp(B[r]); write(lb, string(ev)); } close(lb);
link ld = ":w %s.det"; for(k=1;k<=size(Dt);k++){ m = Dt[k]; ev = leadexp(m); write(ld, string(leadcoef(m)) + " " + string(ev)); } close(ld);
link lm = ":w %s.mm"; open(lm);
for(v=1;v<=12;v++){ for(r=1;r<=n;r++){ f = reduce(var(v)*B[r],G); for(k=1;k<=size(f);k++){ m = f[k]; ev = leadexp(m); write(lm, string(v)+" "+string(r)+" "+string(leadcoef(m))+" "+string(ev)); } } }
close(lm);
"EXPORTED", n;
quit;'''%(pre,pre,pre)]
open(out,'w').write('\n'.join(L)+'\n')
