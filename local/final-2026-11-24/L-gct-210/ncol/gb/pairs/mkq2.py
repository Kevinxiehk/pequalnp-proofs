# alternative: length of A/(det) = dim A - rank(multiplication by det), A = F_p[t]/(G).  Writes the multiplication matrix to a file for numpy.
import sys
src=sys.argv[1]; out=sys.argv[2]; mat=sys.argv[3]
L=open(src).read().split('\n')
cut=[i for i,l in enumerate(L) if l.startswith('ideal H = std')][0]
L=L[:cut]+['ideal B = kbase(G); int n = size(B); int r; int c;',
 'link lk = ":w %s";'%mat,
 'for(r=1;r<=n;r++){ poly f = reduce(Dt*B[r],G); matrix cf = coeffs(f,B); string s=""; for(c=1;c<=n;c++){ s = s + string(cf[c,1]) + " "; } write(lk,s); kill f; kill cf; kill s; }',
 'close(lk);','"WROTE", n;','quit;']
open(out,'w').write('\n'.join(L)+'\n')
