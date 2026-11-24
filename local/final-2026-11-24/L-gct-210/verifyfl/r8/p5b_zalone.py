import sys; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact')
"""m = (1,1,1,1,-4), split A: Z doubly centred (12 coordinates), vartheta(Z) = 0 (<z_0,z_0> = 0, hence all <z_j,z_j> = 0 by (C2')), and the
defect of the line C Z (coefficients of x^2, x^3, x^4 of R_i(xZ)).  HOMOGENEOUS in Z: affine dimension 0 <=> Z = 0 only.  Writes Singular."""
import exactlib as X
p = int(sys.argv[1]); mspec = sys.argv[2]; out = sys.argv[3]
cs = X.Consts(p); m, W = X.parse_m(mspec, cs); V = X.Vars()
co = [V.new('c%d' % d) for d in range(12)]; Z = X.dc_matrix(co, p)
polys, nx = X.equations([Z], W, p)
q = {}
for a in range(4): q = X.padd(q, X.pmul(Z[a][0], Z[a][0], p), p)
polys.append(q)
with open(out, 'w') as f:
    f.write('ring r = %d, (%s), dp; option(redSB); ideal I = %s; ideal J = std(I); print(dim(J)); print(size(J)); quit;\n' % (p, ','.join(V.names), ','.join(X.fmt_poly(e, V.names) for e in polys)))
print(len(polys), 'equations')
