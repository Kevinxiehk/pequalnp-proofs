# NOTES-numerics (role: numerics)
## RESULT (numerics, 12:52) -- no 8- or 9-dim candidate; map is thin. Details below.
CERTIFIED (residual/fresh-point check on ORTHONORMALISED span < 1e-13, clear singular gaps):
 C1. L080 (dim 7): (r,d)=(7,0), (ra,rb)=(4,3), generic rank 2, dim E(L080)=8 (gap 2.0 vs 2e-14).
 C2. For a GENERIC 6-dim subspace S of L080, E(S) is already 8-dim and E(S) is not level (|P_k|~1.2 at unit
     points). So no 8-dim level space contains L080, nor even a generic hyperplane of L080.
 C3. W5 (DC weight space, dim 3, exact by L_gct_119): dim E(W5)=12 (gap 0.18 vs 2e-14).
 C4. A 4-dim level space containing W5 with (r,d)=(1,3), (ra,rb)=(1,0) (polished fresh 5e-15):
     numerics/S4_r1d3.npy. Its E-dim is ambiguous (sv 9e-6,2e-7,9e-9: no gap) -> maximality NOT certified.
 C5. The old L-gct-086 claim "W5 extends to a 7-dim level space" is UNSUPPORTED: saved
     smallcases/ext_w5_4.npy has fresh error 0.26 after orthonormalisation (artifact of degenerate drift).
WEAK (failures to find; method sanity: recovers L080 from a generic 4-dim subspace inside E (dim 11) in 1
start, but NOT from a generic 3-dim subspace (E dim 15, 2 starts)):
 W1. Level space of dim 5 containing W5: not found (4 starts inside E(W5) + 5 in full complement).
 W2. DC level space of dim 4 containing W5: not found (4 starts inside E(W5) ∩ DC, dim 8).
 W3. 8-dim level containing a generic 5-dim (E dim 9) or 4-dim (E dim 11) subspace of L080: not found
     (2 starts each, stalls 0.08-0.2).
 W4. 5- and 7-dim level spaces containing a DC line (4x4 circulant line of L_gct_193 padded, or a line
     of W5) or a 2-dim subspace of W5: not found (2 starts each; E dims 12-22: very weak).
 W5'. No 7-dim level space inequivalent to L080 found: every "new" 7-dim hit (6 of them, seeded from
     5/6-dim subspaces of L080) was L080 within principal angle 1e-8 (see PITFALL).
(r,d) seen: dims 5..7 only (dim,0) [subspaces of L080]; d>0 only at small dims: (0,d) d<=3, (1,3).
PITFALL: L080 is non-reduced: first-order deformation space in G(7,25) has dim 43, so residual 1e-15 is
 compatible with 1e-8 displacements. Compare spaces by principal angles. Also: do not normalise gradient
 rows one by one when computing E(L) (amplifies noise of tiny P_4,P_5 gradients); use raw rows at unit points.
STATUS 12:25: tools in numerics/core.py (invariants r,d; ext space E(L); LM with re-charting + fresh check
on ORTHONORMALISED span). WARNING: the old L-gct-086 claim "n=5 DC weight space W5 (dim 3) extends to a
7-dim level space" looks like an artifact: the saved file smallcases/ext_w5_4.npy has fresh-point error
0.26 after orthonormalisation; LM 'successes' there were degenerate drift (new vectors collapsing into W5,
basis singular values down to 0.08). With new vectors forced into the complement of W5, W5+2 fails
(stalls at res 5e-2, 5 starts). Weak evidence so far, being checked inside E(W5).
STATUS 12:40:
- CERTIFIED (exact-structure + numeric, fresh 1e-15): E(L080) = first-order extension space has dim 8, and
  for a GENERIC 6-dim subspace S of L080, E(S) is already 8-dim and E(S) itself is NOT level (fresh |P_k| ~1.2).
  Hence no 8-dim level space contains L080 or even a generic 6-dim subspace of L080 (any level L' ⊇ S lies
  in E(S)).
- PITFALL (important for anyone using residuals): L080 is a highly degenerate (non-reduced) point: first-order
  deformation space of L080 in G(7,25) has dim 43 (tangent computed with 800+ sample points). LM "finds"
  7-dim spaces with residual 4e-15 that differ from L080 by angles ~1e-8 (they look new: different ra/rb,
  span(B,L080)=8 at tol 1e-8) -- they are L080 with sqrt(eps) slop. Residual < 1e-10 does NOT pin down a
  space better than ~1e-7 near L080; compare spaces by principal angles, not by rank tests at 1e-8.
- W5 (DC weight space, dim 3, exact by L_gct_119 symmetry): E(W5) dim 12; W5 + 1 direction gives a 4-dim level
  space with (r,d)=(1,3) (fresh 1.1e-13). W5 + 2 (inside E(W5)): not found (4 starts, stalls ~1e-2). W5 + 1 DC
  direction (dc dim 4 containing W5): not found (4 starts). Weak evidence that W5 sits only in <=4-dim level spaces.
- 8-dim containing a generic 5-dim (resp. 4-dim) subspace of L080: not found (2 starts each, stall 0.1-0.2). Weak.
STATUS 12:52: final. Budget ended. See RESULT at top.

## ROUND 2 (12:28-, task: certify split's 7-dim spaces, E(L), search 8 inside E)  -- files numerics/r2/
STATUS 12:41:
- ex1 (5,2) and ex2 (6,1) from NOTES-split: exact bases rebuilt (r2/spaces.py), fresh 3e-15. dim E = 8 for BOTH
  (clean gaps 0.72/3e-14 and 0.91/3e-14) -- NOT "E = itself" as NOTES-split says (the split value came from the
  LM-approximate rc45p1/d1_ext1, which are ex1/ex2 within angle 2e-7: non-reduced slop again, its E shows a
  spurious 1e-6 singular value). The extra E-direction is rank one u 1^T (row 3 = 1, other rows -1/4), as for
  L080; E(L) is NOT level (|P_2| 0.76, |P_3| 0.28, |P_4| 0.03 on L+v) => ex1, ex2 not extendable (certified).
- NEW exact 7-dim level space ex3 (checked over Z[w], all P_k exactly 0, r2/ex3exact.py):
    rows 0..2: cols (2,3) = (w^{2i}, -w^{2i})  and  cols (2,3) = (w^i, w^i)   [2 dims; first is DC]
    row 3: any sum-zero row (4 dims);  column 4 multiple of (1,1,1,0,-3)^T (1 dim).
  (r,d,ra,rb) = (6,1,2,4) like ex2 but generic rank 4 (ex2: 3). Found as a 7-dim level space through the
  hyperplane "ex1 minus B1" (inside E(S), dim 10).
- Pairwise INEQUIVALENT (min over 120x120 row/col perms x transpose x complex conjugation of sin(max principal
  angle)): L080/ex1/ex2/ex3 all >= 0.87. Invariants: L080 (7,0,4,3) rk2; ex1 (5,2,1,4) rk4; ex2 (6,1,2,4) rk3;
  ex3 (6,1,2,4) rk4. All have dim E = 8 and E not level.
- generic 6-dim S in ex1/ex2: E(S) = 8, not level -> no 8-dim through a generic hyperplane of them (certified).
- special hyperplanes (drop one natural basis vector): E(S) = 8,9,10,12. 8-dim searches inside E(S) (fixed S,
  2 new vectors): ex1 drop B1 / drop col4 (E=10, Gr(2,4)): 6 starts each, all stall ~0.1;
  ex2 drop col0 / drop col4 (E=12, Gr(2,6)): 5 starts each, stall 0.06-0.1. Weak-to-moderate (small Grassmannians).
STATUS 12:51:
- NEW EXACT 1-PARAMETER FAMILY of 7-dim level spaces (certified for ALL s in C): with A=(2,-1,-1), b=(0,1,-1)
  on rows 0..2,
    v1 = A in col p + s*b in col q,   v2 = -3b in col p + s*A in col q      (p != q in {0..3}),
    + row 3 any sum-zero row (4) + column 4 multiple of (1,1,1,0,-3)^T (1).
  Exact integer check (r2/famexact.py, unisolvent, P_1..P_5) at s = 2c for c = 0,1,2,3,4,5,-1,-2: all zero; every
  evaluation is a polynomial of degree <= 5 in s, so P_k == 0 on the span for every complex s.
  s = i*sqrt3 gives ex3 (DC part appears: (6,1,2,4)); generic s: (r,d,ra,rb) = (7,0,3,4), generic rank 4;
  s = 0: column p rows 0..2 sum-zero (rank 3). Members are pairwise inequivalent in general (equiv-angle 0.56
  between s=0.6+1.4i and s=4). => the variety of 7-dim level spaces has a positive-dimensional component;
  "inequivalent to L080" is cheap. Random LM in the 3x4 block with the row3+col4 skeleton fixed: 5/8 starts give
  7-dim level spaces, all in this family (or its s=0 end).
- dim E = 8 at every tested member (s generic, s=0, ex3), clean gaps; E not level (|P_k| ~ 0.7-1.1) => no member
  extends to 8 (certified per member tested).
- Structured-hyperplane scan (S = L ∩ {t_ab=0}, {row/col sum=0}, drop-basis-vector): max dim E(S) = 12
  (L080 ∩ {t_40=0}; ex2/ex3/family drop col4-vector), 10 (ex1 many; ex3 drop1). 8-dim searches inside E(S)
  (S fixed, Gr(2,4) or Gr(2,6)): L080∩{t40=0}, ex3 drop6, family drop0, ex3 drop1: 4 starts each, all stall
  0.06-0.1. Skeleton F = row3+col4 (dim 5, E(F)=16): 8-dim F+3 searched in 3x4 block (8 starts) and in E(F)
  (6 starts): all stall ~0.1, whereas F+2 (7-dim) succeeds in 5/8 starts. Moderate evidence: no 8-dim here.
STATUS 13:01 (round 2 final):
- generic hyperplanes S of ex3, family member, s=0 member: E(S) = 8 and not level (3 each) => certified no 8-dim
  through a generic hyperplane of any of them.
- First-order deformation dims (Zariski tangent in G(7,25)): L080 43, ex1 9, ex2 21, ex3 20, fam generic 20,
  s=0 member 27 -- all far above the visible family dimension: these points are non-reduced or on larger
  components; expect residual-slop ~1e-7 on any LM hit near them.
- ANOTHER LARGE FAMILY (numerical, 8/8 random starts, fresh 3e-15): row 3 (sum-zero, 4 dims) + a 3-dim subspace of
  the 4x2 block rows {0,1,2,4} x cols {2,4}. (r,d,ra,rb)=(7,0,3,4), generic rank 4, dim E = 8 (gaps ~1 vs 3e-14),
  E not level. Same skeleton +4 vectors in that block (8-dim): 8/8 starts stall at 0.2-0.3. Strong-ish evidence.
- Global 8-dim LM over all of Gr(8, sum-zero 24) seeded at E(L) (+5% / 30% noise) for L080, ex1, ex2 and a family
  member: all stall at fresh 2-4e-2 (sample residual ~0.8); a 160 s run from the family member drifts away from L
  (min overlap sv 0.77) without converging. No 8-dim candidate anywhere.
SUMMARY round 2: every 7-dim level space we have (L080, ex1, ex2, ex3, the exact 1-parameter family, the 4x2-block
family) has dim E(L) = 8 exactly, with the extra direction a pure row/column-mean rank-one matrix, and E(L) not
level. So none extends to 8. 7-dim spaces come in positive-dimensional families (the problem is not rigid), but
all 8-dim searches (special hyperplanes with E(S) up to 12, skeletons, global seeded) fail.
