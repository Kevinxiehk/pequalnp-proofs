# NOTES-literature (started 11:19)

Context found in project: L-gct-077 reduction = level spaces at J for perm_n -> zero-subspaces of perm_(n+1)
at Sigma (corner -n), via L-gct-069/035 (the "Kumar-Volk style" fact: if f = det_N(affine), every zero y of f
lies on an affine subspace of codim <= N inside {f=0}; kernel vector argument). So literature to check:
"affine subspaces in the zero set of the permanent through a point".

## Findings so far (11:30)
- No paper found (yet) that studies perm(J+t)=n! level spaces or affine subspaces of V(perm) through the
  Mignon-Ressayre point. Mignon-Ressayre 2004 point = corner 1-m, others 1 = project's Sigma_(n+1).
- Over R the analogue is easy (P_2 pos. def. on doubly centred) and Yabe 2015 (arXiv 1504.00151) gets
  dc_R(perm_d) >= (d-1)^2+1 over the reals. So any C-proof must use complex isotropy.
- Chan-Ilten 2015 (Fano schemes of det & perm, arXiv 1312.2577): linear spaces in V(perm_n) through 0:
  max proj. dim n(n-1)-1, for large k Fano scheme = union of compression-space components. (Through 0, not J.)
- 2026 preprints: OpenAI (24 Sep 2026) "A cubic lower bound for border determinantal complexity of the
  permanent" claims dc-bar_C(perm_n)=Omega(n^3) (restrict perm to smooth hypersurface of deg ~n/3 in ~n^2/100
  vars + kernel-equation multihomogeneous Bezout count). Sheshadri arXiv 2610.40484 extends to char p.
  If correct, the L-gct-077 "unlock" (m^2-O(m)) is superseded asymptotically, but this does NOT answer the
  level-space question (reduction is one-way).
- Yabe 2015 Thm 1.7: dc_R(perm_d) >= (d-1)^2+1 over R, via Hessian at Sigma_d (corner 1-d): signature
  n_- = (d-1)^2+1, n_+ = 2d-2 (real isotropic dims <= 2d-2). Yabe Thm 1.5 uses HIGHER Taylor parts:
  dc(p) >= 4^{-(k-1)} b-rank(p_{x0}^{(2k)}) - 2(k-1)D^{k-1}  (loses 4^k, useless for growing k).
- LMR 2013 (arXiv 1004.4802): dc-bar(P) >= (dim dual(Z(P))+1)/2; perm dual nondegenerate -> m^2/2 is the ceiling
  of the dual-variety/Hessian method. No discussion of linear spaces / level sets.
- Ghasemi-Gross-Kopparty ECCC 2025/206 (arXiv 2512.03221): "permanull" S<=F^n (all n x n matrices with
  columns in S have perm 0) => S in a coordinate hyperplane (char 0). Key perm-only fact: perm(v,...,v)=n! prod v_i.
  (Product-type statement, analogous to team's L-gct-090.)
- CHECKED numerically (literature/hess.py, d=3..6): Hessian of perm_d at Sigma_d (corner 1-d) has full rank d^2,
  signature n+ = 2d-2, n- = (d-1)^2+1 (matches Yabe). So REAL level spaces are O(n) trivially; over C Taylor
  order 2 caps at ~d^2/2 (complex isotropic). Order >= 3 info is needed (as the project says).
- Ilten-Teitler 2015 (arXiv 1503.00822): Fano-scheme (linear subspaces in V(perm)) method for product rank;
  border product rank of perm_n > n. Same "complexity => big linear subspaces in V(f)" principle as L-gct-035.
- Sheshadri arXiv 2611.06658 "dc(perm_4)=15": uses kernel linear spaces K in Sing(perm) at a zero + Hessian;
  no level-set results.
- NOT FOUND anywhere: perm(J+t)=n! level spaces; max dim of affine spaces in V(perm_m) through Sigma_m;
  any O(n) bound or superlinear construction. The question appears to be genuinely open / unstudied.
