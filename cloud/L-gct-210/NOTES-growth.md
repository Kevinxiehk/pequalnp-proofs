# NOTES-growth (role: growth; 13:15-14:15)
## RESULT (14:12) -- no proof; growth is the right target but has NO cheap proof. Settled:
 (G1) [exact, checked 1e-15] PRODUCT FORMULA. u-coords u = g - (3/2)(al_i+be_j) (R,C = row/col sums of u):
      Q(u,v) = <u,v> - (5/9)(R.R'+C.C') [= polar 2P_2],  T(u,v,w) = sum uvw - (1/9)(sum RR'R''+sum CC'C'') [P_3 = (2/3)T(u,u,u)]
      u∘v = G^{-1}(h - mean h),  h = u*v - (1/9)(R_iR'_i + C_jC'_j),  G = id on DC, -16/9 on row/col parts.
      Equivalently u∘v = pi_E(iota u . iota v) in C^35 = C^25 x C^5 x C^5 (iota u = (u, R/5, C/5), trace weights 1 / -125/9),
      E = iota(U) (24-dim), E^perp (11-dim) = {(c + (25/9)(p_i+q_j), p, q)}.  NB on DC the product LEAVES DC (row/col parts).
 (G2) [exact] NON-ASSOCIATIVITY IS RANK <= 11: Q(x∘y, z∘w) = S4(x,y,z,w) - <eps(x,y), eps(z,w)>, S4 = tr_w(xyzw) fully
      symmetric quartic, eps(x,y) = E^perp-component of iota x . iota y, determined by the 11 bilinear forms <x,y>,
      rowcov_i(x,y) = sum_j (x_ij - xbar_i)(y_ij - ybar_i), colcov_j(x,y).  (checked numerically, growth/epsid.py)
      For P2P3 L: S4|Sym^2 L = G_beta + G_eps with rank G_beta <= 24-2l, rank G_eps <= 11.
 (G3) [exact, trivial] FORCED ZERO DIVISORS: if dim L = 9 and P2=P3=0 then beta: L x L -> L^perp/L (dim 6) has, for EVERY
      x in L, kernel K_x = {y in L: x∘y in L} of dim >= 3; the set {x: x∘x in L} is a cone of dim >= 3 in L.  (no contradiction found)
 (G4) [exact] C^35 Kneser route (B = 1 + iota L, B^2 perp L, L perp E^perp): gives only h + j >= 5 (h = dim Stab B^2,
      j = dim B^2 cap E^perp); generic 7-dim P2P3 spaces have B^2 ⊇ E^perp (j = 11). DEAD (it forgets E).
 (G5) [numerical] dim(L + L∘L): random iso l: min(l + l(l+1)/2, 24). P2P3 examples: generic 7-dim (lowd LM) 17 = 24-l (L + L∘L = L^perp),
      L080 16, p23supp 16, ex1/ex2/rc45p1 14 = 2l, weight6 (6) 14, k4gen (4) 10, rank1weight (3) 7.  So ALL P2P3 examples have
      dim(L+L∘L) >= 2l; "growth >= 2l-2" for P2P3 spaces would give l <= 8 (needs >= 16 at l = 9).
 (G6) [exact, exhaustive] Abelian gradings <sigma> x <tau> (all 28 cycle-type pairs, full 24-dim U, unions of eigenspaces):
      max P2P3 weight space = 7 (matches the believed max; no 8 or 9); min dim(L+L∘L) over 9-dim Q-isotropic graded L = 18 = 2l.
 (G7) [numerical] small-growth Q-isotropic 9-spaces exist only near the extremal examples: rad(ex2 + ex2∘ex2) is a 9-dim
      Q-isotropic space containing ex2 with dim(L+L∘L) = 17 (T != 0).  Best 9-dim iso growth seen: 17 (need <= 15 to break the pure
      growth target).  ∘-closures: every example generates all of U except the 3-row K (k4gen), which generates a proper 19-dim
      subalgebra (Q nondegenerate on it, max iso 9) -- the only proper subalgebra seen; it cannot host growth <= 15 at l = 9.
 (G8) NEGATIVE (numerics): LM searches for low growth (growth/lmfl.py: L,F with Q(L,F)=T(L,L,F)=0; growth/mingrowth.py:
      variable projection) fail their calibrations (cannot find 7-dim P2P3 / growth-14 / even growth-17 from 1e-2 perturbations),
      so they give no evidence either way. Do not trust them.
 Best next step: the pure growth statement "Q-isotropic 9-dim L => dim(L+L∘L) >= 16" is consistent with all data (min seen 17)
 but a proof needs a Kneser theorem for (U,∘); (G2) says ∘ is associative up to an 11-dim correction (row/col covariances),
 so a Kneser-with-stabiliser argument in C^35 must be run on pi_E(B^2), not B^2 -- try "dim pi_E(XY) >= dim X + dim Y - dim Stab - 11"
 type bounds only after splitting off block stabilisers (the extremal examples all have row/column block structure).
 Files: growth/core.py (Q, T, ∘), known.py, c35.py, wgrade.py, wgrowth.py, closure.py, rad.py, epsid.py, lmfl.py, mingrowth.py.
Target: no 9-dim L in the 24-dim sum-zero space with P_2 = P_3 = 0, via growth of L + L∘L (x∘y = Q^{-1}T_3(x,y,.)).
STATUS 13:18: started; reading notes, writing growth/core.py (u-coordinates, Q, T, ∘).
STATUS 13:41: core.py done: u-coords (u = g - 1.5(al_i+be_j)), Q(u,v) = <u,v> - (5/9)(R.R'+C.C'), T = sum uvw - (1/9)(sum RR'R''+sum CC'C'');
 EXACT PRODUCT: u∘v = G^{-1}(h - mean h), h = u*v - (1/9)(R_iR'_i + C_jC'_j), G = 1 on DC, -16/9 on row/col parts
 (verified Q(u∘v,w) = T(u,v,w) to 1e-15). dim(L+L∘L) data: random iso l: min(l + l(l+1)/2, 24);
 P2P3 7-dim: generic LM solutions 17 (= 24 - l, L∘L + L = L^perp exactly), p23supp 16, L080 16, ex1/ex2/rc45p1 14 (= 2l),
 weight6 (DC p2p3) 14, k4gen 10, rank1weight 7.  Graded (2-dim cyclic gradings <sigma> x <tau>, all cycle types):
 max P2P3 weight-space dim in full U = 7 (no 8!), and min dim(L+L∘L) over graded 9-dim Q-isotropic unions of
 eigenspaces = 18 (= 2l).  C^35 Kneser route (B = 1 + iota L): useless, B^2 ⊇ E^perp for generic examples (j = 11).
STATUS 14:13: finished; final report sent.
