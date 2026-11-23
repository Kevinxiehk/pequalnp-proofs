# NOTES-infra (map of checked material for L-gct-086)

Conventions: LS(n) = max dim of an n x n level space; LS(p,q) = max dim of a space of p x q
matrices on which all injective sums M_k (k = 1..min(p,q)) vanish (rectangular level space).
DC = doubly centred (all row and column sums 0). "UB" upper bound, "LB" construction, "ID" identity.
All files under /home/claude/pequalnp-proofs/lean/PEqualNP/. All are checked (no sorry) unless said.

## KEY STRUCTURAL FACT (use this): gluing on disjoint blocks (L_gct_110)
Outside/L_gct_110.lean `PEqualNP.Outside.L_gct_110`: if L1 is level and supported in rows A x cols B,
L2 level and supported in rows A^c x cols B^c, then L1 ⊔ L2 is level.  (ID/LB tool)
Consequence: LS(n) >= sum_i LS(a_i, b_i) whenever sum a_i = n = sum b_i (a block of a x b inside
n x n is level iff its rectangular M_k all vanish, by Minc L084). So L-gct-086 is essentially
equivalent to "LS(p,q) <= C (p+q)" for rectangular blocks; any superlinear counterexample can be
looked for as a single rectangular block, and any proof must control rectangular blocks.

## Constructions (lower bounds)
- Gct/L080 `L080` (helper Helpers/LevelLow `level_space_lower`): LB, dim = 2n-3 for n>=2. The space:
  t supported on last row and last column; last row off the corner = (x_1..x_{n-2}, -sum x)
  (free x, n-2 params), last column off corner = y (n-1 params), corner = -sum y.  Proof via
  bordered expansion (Helpers/BorderedPerm `eval_permPoly_bordered`).
- Outside/L_gct_189: LB, explicit 5x5 level space of dim 7 (= 2n-3, nothing better found at n=5).
- Outside/L_gct_197: LB, 4x4 row-centred level space, dim 5 (= 2n-3).
- Outside/L_gct_180: LB, 4x5 row-centred rectangular level space dim 6.
- Outside/L_gct_198: LB, 4x6 row-centred rectangular level space dim 7 (rows: one free sum-zero
  row, others built from cube roots of unity on column pairs).
- Outside/L_gct_208: LB, 4x6 rectangular level space (sum over Fin 4 ↪ Fin 6 of prod(1+t) = 360) dim 7.
- Outside/L_gct_108: LB, 2 x q (q>=2) space with M_1 = M_2 = 0 of dim q-1 (tight with L101).
- Outside/L_gct_119: LB tool, ID-type: if t(σi, τj) = z t(i,j) with z^k ≠ 1 for k=1..n then
  perm(J+t) = n!.  So every eigenspace {t : t∘(σ×τ) = z t} is a level space. (infra remark, not
  checked: its dimension is sum over cycle pairs with ord(z) | lcm of gcd(c_p,d_q) <= n^2/ord(z) < n,
  so symmetry eigenspaces alone never beat n.)
- Outside/L_gct_193: LB, one explicit 4x4 level line c*(circulant with 1, i, -i, -1).
- Gct/L081, L085 (Helpers/BadZero): at the zero [[-1,e1^T],[e1,I]] (NOT at J) the permanent vanishes
  on a space of dim k(k+1)/2 (quadratic). Shows quadratic behaviour at other zeros.
- Gct/L087 (Helpers/Sigma4Space): 7-dim space through J-with-corner-(-3) (a zero of perm_4).

## Upper bounds
- Gct/L092 `L092`: reduction to DC. If every DC level space has dim <= G then every level space has
  dim <= G + 2n. Proof: phi = (row sums, col sums), L ⊓ ker phi is DC level, rank-nullity, and
  dim phi(L) <= 2n is used crudely (loses up to 2n; the image actually lies in the 2n-1 dim
  space {sum rows = sum cols}, and is further constrained by M_1, M_2 — not exploited).
- Gct/L094 `L094` (Helpers/LevelThree `level_three_le`): LS(3) <= 3 (= 2n-3, tight). Fourier coords
  for cyclic shifts (w^2+w+1=0), perm(J+t) = 6 + 3 c6(x), isotropy for the quadratic part (four
  hyperbolic pairs), charts, 16 explicit unit-ideal certificates (kern_0000..kern_1111).
- Outside/L_gct_109: UB, 3x3 DC level spaces have dim <= 1 (2x2 minors argument, `core`).
- Outside/L_gct_216: UB, 4x4 DC level spaces have dim <= 3 (Walsh/Fourier coords, `walsh`, `bound`;
  1307 lines; uses `colFalse`, `walshMoments`).
- Outside/L_gct_217: UB, 4x4 row-centred level spaces dim <= 5 (tight with L_gct_197).
- Gct/Helpers/LS4/* : pieces for L-gct-091 "LS(4) <= 5" (gluing obstructions: OddPart, TwoTwo,
  GlueRow, GlueTwo, Symmetry, WcIdentity). No Gct/L091 file for this gap exists (Library/L091 is
  unrelated), so LS(4) <= 5 itself seems NOT checked; only DC (L_gct_216) and row-centred (217).
- Gct/L055 (Helpers/BlockIsotropic): LS(3) <= 4 (superseded by L094).
- Gct/L083 `L083`: UB, dim L + dim W(L) <= n^2, W(L) = span of gradients of perm at J+t, t in L
  (first-order extension; L ⊥ W(L)).
- Gct/L090 `L090` (Conjecture C, product type): subspaces S_1..S_n of C^n all of whose nonempty
  column product sums vanish: sum dim S_j <= n-1. Via Helpers/ProdSigmaChain `chain` (Kneser
  chain; span of subset products has dim >= 1 + sum dim).
- Gct/L079: product-type spaces through Sigma_m in the hypersurface: sum dim <= 2m-2.
- Outside/L_gct_111: UB, row-product type (row i from its own V_i, all combos level): sum dim V_i <= n-1.
- Outside/L_gct_123: UB, column-product type: sum dim S_j <= n-1.
- Outside/L_gct_114: UB, t = r + c (rows r_i in V_i, columns c_j in S_j, all combinations level):
  sum dim V_i + sum dim S_j <= 2n-2. (This is "the product-type bound"; the 2n-3 construction is
  essentially of this shape.)
- Gct/L098 (Lemma I, Helpers/InvisibleBlock `lemmaI`): P x m space with every column-set injective
  sum vanishing: dim <= P-1.  (Moebius: injective sums -> diagonal sums, then chain.)
- Gct/L102 (Helpers/SProduct): p+1 row subspaces with all level sums vanishing + Y: total <= p+q-2.
- Gct/L101 (Helpers/STwoRow): 2 x q with M_1 = M_2 = 0: dim <= q-1. So LS(2,q) = q-1.
- Gct/L156 `L156`: 3 x q rectangular level spaces dim <= q+1; from L157 (row-centred 3 x q: dim <= q-1,
  Rado L171 + ThreeRowRado). So LS(3,q) <= q+1.
- Gct/L170, L175 (ColumnCore): V containing J with functional lam, lam(J)=1, sum_j prod_i x(i,j) =
  q lam(x)^p on V  =>  dim V <= q.  (p rows, any p.)
- Gct/L158 (Helpers/RealLevel): OVER THE REALS, p x q with M_1 = M_2 = 0: dim <= p+q-2. So the real
  version of L-gct-086 is trivial (M_2 on DC = sum of squares); a proof must be genuinely complex.
- Gct/L100 (Conjecture S at p=1), Outside/L_gct_212 (2x2 instance of S2 Target, total <= 2),
  Outside/L_gct_213 (2x3 instance, <= 3). The general S2 Target (Helpers/S2Reduction `Target`,
  `reduction : StmtS2 -> Target`) and S2Elem `MainClaim` are NOT checked in general;
  Outside/L_gct_153 proves MainClaim's isotropic form (dim R <= dim T(R)) — check its exact hyps.
- Outside/L_gct_142: UB, W ⊆ C^n on which all even elementary symmetric e_{2j} vanish: dim <= 1.
- Outside/L_gct_120: UB (line): t with every row equal to c*w is level only if c = 0 or w = 0.
- Outside/L_gct_121: UB (line): rank-one level line u v^T forces |supp u| ≠ |supp v|.
- Outside/L_gct_202: 4 x q, first row constant c, all level sums vanish => c = 0.
- Gct/L163 (T3, Helpers/T3Assembly, T3LemmaP): A+B totally isotropic, C ⊥ A, B, A*B, sum a^4 = 0 on A
  => dim A + dim B + dim C <= m (Kneser L-gct-065 based).
- Outside/L_gct_152: symmetric nondegenerate B, B v v ≠ 0, A isotropic ⊥ v => 2 dim A + 1 <= dim V.
- Outside/L_gct_151: circuit lemma (minimal-support vector with nonzero sum spans its support).
- Gct/L169 (corner lemma, perm_4 vanishing on dim>=7 space), Gct/L150 (gap lemma for polynomials).

## Identities (Taylor / subpermanent expansions)
- Gct/L084 `L084` (Helpers/MincExpansion `minc_expansion`): perm(J+t) = sum_k (n-k)! M_k(t), M_k = sum of
  k x k subpermanents.  THE Taylor expansion at J. Level <=> M_k|L = 0 for all k (by scaling).
- Gct/L088 (Helpers/RankOne `injForm`): k! M_k(t) = sum_{i,j : Fin k ↪ Fin n} prod_a t(i a, j a).
  RankOne also has `MkPol` (full polarization, `MkPol_diag`) and `MkPol_rankOne` (factorizes as
  Inj u * Inj w on rank-one arguments).
- Gct/L089 `L089`: M_k(x y^T) = k! e_k(x) e_k(y).
- Outside/L_gct_118: perm(J + μ u v^T) = sum_k μ^k k! (n-k)! e_k(u) e_k(v).
- Gct/L099 (Helpers/SupportCriterion): perm(J + sum_i c_i u_i w_i^T) = sum_α (n-|α|)! α! a_α b_α c^α
  (Binet-Cauchy for permanents, a, b coefficients of prod_j (1 + sum_i u_i(j) X_i) etc.).
- Outside/L_gct_105: DC p x q: sum_{i≠k, j≠l} t_ij t_kl = sum t_ij^2  (so 2 M_2 = sum t^2 on DC).
- Outside/L_gct_106: DC: ordered 3-injective sum = 4 sum t_ij^3  (6 M_3 = 4 p_3 on DC).
- Outside/L_gct_134: DC: 24 M_4 = 36 sum t^4 - 18(sum_i (row sq sum)^2 + sum_j (col sq sum)^2)
  + 6 sum_{i,i',j,j'} t_ij t_ij' t_i'j t_i'j' + 3 (sum t^2)^2.
- Gct/L159 (RealLevel `ident`): general off-row off-column pair sum = (total)^2 - sum row^2 - sum col^2 + sum t^2.
- Outside/L_gct_107: rank-one bilinear version of the pair sum.
- Helpers/SigmaSums: second and third distinct sums of DC matrices (used for L-gct-062).
- Helpers/LS4/WcIdentity: on 4x4 column-centred t: perm(J+t) - 24 = -2 sum_i e2(row i) + 2 sum_i e3(row i) + perm t.
- Helpers/LS4/OddPart, TwoTwo: odd-part / four-sign polarization identities for perm_4(J ± A ± R).
- Outside/L_gct_112: perm_4 Laplace expansion in 2x2 blocks. Outside/L_gct_126: 24xyz polarization.
- Helpers/GReduction (L-gct-077): perm_{n+1}(Sigma + c t) = -c d/dc perm_n(J + c s).
- Helpers/Extension/Gradient: perm(a+e_q) - perm(a) = D a e_q (permanent affine in each variable).
- Helpers/TaylorOnSpace, OrderConditions: generic "vanishing on y+L => all differentials vanish on L".

## Downstream
- Gct/L077: level-space bound G => border det complexity of perm_{n+1} >= (n+1)^2 + 1 - G - 2(n+1).
- Gct/L069/L071/L075/L070: border subspace reduction and the 2m^2 bound.

## Power-sum / Kneser machinery (checked) and what it gives here  [infra, 11:23]
- Gct/L065 Kneser for codes over C (Mirandola-Zemor): dim S + dim T <= dim(S*T) + dim Stab(S*T),
  S*T = coordinatewise (Hadamard) product span in C^n.
- Gct/L061 (= L066 applied to L065), sharp Fermat: W ⊆ C^M with p_2 = p_3 = 0 on W => 3 dim W <= M.
- Gct/L067 iterated Fermat: p_j = 0 on W for 2 <= j <= k  =>  k dim W <= M.
- Gct/L063: n >= 19, W ⊆ C^{n x n} with p_2 = p_3 = 0 => 2 dim W + 6n + 4 <= n^2.
- Gct/L062: zero-subspaces at Sigma_m reduce to p_2,p_3-killing spaces (+4n).
READY ASSEMBLY (all pieces checked, not stated as one theorem): DC level K => M_2 = 0 and M_3 = 0,
  L_gct_105 gives sum t^2 = 0, L_gct_106 gives sum t^3 = 0 on K; L061 with M = n^2 gives
  dim K <= n^2/3; L092 gives LS(n) <= n^2/3 + 2n.  Quadratic only.
WARNING (verified numerically, infra/circ.py): the iterated-Fermat route "DC level => p_j = 0 for
  j <= k(n) -> L067 gives dim <= n^2/k" FAILS already at j = 4: the checked 4x4 DC level line of
  Outside/L_gct_193 (t_ij = f((j-i) mod 4), f = (1, i, -i, -1)) has p_2 = p_3 = p_5 = 0 but
  p_4 = sum t^4 = 16 ≠ 0. So M_4 = 0 does NOT force p_4 = 0 (consistent with L_gct_134's extra terms).
  Any Taylor-order-growing argument has to use M_k, not entrywise power sums.

## FORMALIZATION CONSTRAINTS + READY KIT  [infra, 11:29]  (important for anyone writing Lean)
- The gap's file may import ONLY Mathlib and PEqualNP.Defs (gap.json "imports"). NONE of the checked
  lemmas above (L092, L084, L061, L065, L110, ...) can be imported: they must be copied into the file.
  leancheck's format report also requires: no comments at all (no -- or /-), no '#' (so no `#s`
  card notation, no #print), no double quotes, no words sorry/axiom/instance/structure/attribute/
  macro/notation/syntax/elab/initialize/inductive anywhere. <= 512 KiB. One theorem
  PEqualNP.Outside.L_gct_086 with the verbatim statement.
- Accepted Outside files are already format-clean self-contained copies; reuse them:
  L_gct_123 (private Kneser + Kneser chain `prod_sigma_bound`, row-matrix permanent formulas),
  L_gct_114 (Rado `rado_aux`, ColumnCore, InvisibleBlock adaptations), L_gct_110 (gluing + poly
  coefficient extraction), L_gct_216 (4x4 Walsh coords), L_gct_134/105/106 (DC identities).
- Import-closure sizes (stripped of comments they have no '#'/quotes, except SupportCriterion: 3 '#'):
  L092 2 KB (self-contained); Minc L084 15 KB; injForm L088 8 KB; Kneser L065 30 KB; Fermat L061 49 KB;
  iterated Fermat L067 63 KB; L090 chain 63 KB; L098 80 KB; L094 (3x3) 107 KB. All fit easily.
- infra/strip.py FILE... : prints comment-stripped, import-free Lean (use to inline helpers).
- infra/Kit.lean  COMPILES with leancheck (exit 0, axioms propext/choice/Quot.sound, format all 0):
  inlined MethodCeiling + MincExpansion + RankOne, plus NEW lemmas in namespace PEqualNP.Gct.Kit086:
    Mk_smul        : Mk n k (s • t) = s^k * Mk n k t
    level_Mk_zero  : level L -> ∀ t ∈ L, ∀ k, 1 <= k -> k <= n -> Mk n k t = 0
    level_of_Mk_zero : (∀ k in [1,n], Mk n k t = 0) -> perm(J+t) = n!
    level_inj_zero : level L -> ∀ t ∈ L, k in [1,n]: Σ_{i j : Fin k ↪ Fin n} Π_a t(i a, j a) = 0
    reduce_dc      : the statement of L092 (DC bound G => all level spaces <= G + 2n)
  So a proof only has to supply: "DC space K with all injective sums vanishing => dim K <= C n - 2n",
  then `reduce_dc` finishes. Start any Lean attempt by copying Kit.lean.

## Ruled out (infra, 11:32, numerically verified, infra/glue.py)
- "DC level => entrywise power sums p_k vanish for k < n (then iterated Fermat L067 with k=n-1 gives
  dim <= n^2/(n-1))": FALSE for every n >= 4. Glue (L_gct_110) the 4x4 circulant DC level line of
  L_gct_193 into the top-left block of an n x n zero matrix: still DC and level (perm(J+ct) = n!
  checked for n = 5, 6), but p_4 = 16. So iterated Fermat can only ever be used with k = 3
  (=> the checked-assembly bound LS(n) <= n^2/3 + 2n). Any growing-order argument must be robust
  under block-diagonal gluing, i.e. must work with M_k / connected sums c_k, not p_k.

## Repository notes on this route (item 2)
- The checkout has NO notes directory: files cited in Lean headers (notes/gct-086-core/t3/notes.md,
  notes/gct-086-S-p2-statement.txt, notes/gct-086-S-p2-elementary.md, reduction.md,
  Gct/FermatProof.md, Gct/Gadget025/dim.md, rung-notes.md) are absent. Only Lean headers survive.
- Routes visible from those headers (status):
  * "Conjecture S" / S2 (hub row L-gct-143): induction adding one row X and one column Y to a 2-row
    core L (Helpers/S2Reduction `Target`: dim L + dim X + dim Y <= q). Checked: p=1 case (L100),
    2x2 and 2x3 instances (L_gct_212/213), MainClaim dim R <= dim T(R) (L_gct_153), reduction
    StmtS2 -> Target; valuation-theoretic steps T1-T6 / R3-R5 only partially (S2Val, S2ValExists,
    S2Height). General S2 NOT checked. This is a row/column-splitting style induction (brief: dead).
  * T3 (gct-086-core/t3): L163 checked (Kneser-based: A+B isotropic, C ⊥ A,B,AB, p_4|A = 0 =>
    dim A+B+C <= m). Its role in an overall argument is not recorded in the repo.
  * Three-row / column-core route: L156, L157, L170, L175 checked (Rado L171 + induction on
    columns) -> LS(3,q) <= q+1. Fixed number of rows only.
  * LS(4) <= 5 (L-gct-091): helpers LS4/* only; assembled pieces L_gct_216 (DC <= 3) and
    L_gct_217 (row-centred <= 5). The full n=4 statement is NOT a checked theorem.
  * Helpers/ThreeRow.lean and ColumnCore.lean still say "conjecture" in their headers (stale: L157,
    L175 are checked).
- Failed / capped approaches I can document beyond the brief's dead list:
  * entrywise power sums + iterated Fermat: capped at order 3 (see "Ruled out" above);
    best checked-assembly bound LS(n) <= n^2/3 + 2n.
  * symmetry eigenspaces (L_gct_119): always < n.
  * real-number arguments (L158, Yabe): trivial over R, do not transfer.
  * first/second-order arguments: L083 (gradient span), L055/isotropy ((n-1)^2/2) — bounded order.

## PLUG-INS: which checked lemmas fit the other agents' best ideas  [infra, 11:33]
proof (cumulants c_k / Gaussian E_k / power-sum heuristic):
- Your unproved "Lemma A" (N forms spanning C^d with p_1..p_m = 0 => N >= m d (+1)) IS CHECKED:
  Gct/L067 (iterated Fermat, via Kneser L065): p_j|W = 0 for 2<=j<=k => k dim W <= M. Format-clean
  inline closure 63 KB. Sharp k=3 case L061. So only the graph terms of c_k are missing.
- Your P_2, P_3, P_4 formulas on DC are checked: Outside/L_gct_105 (k=2), L_gct_106 (k=3),
  L_gct_134 (k=4, injective-sum form; 24 M_4 = 36p_4 - 18(Σr^2+Σc^2) + 6 tr((tt^T)^2) + 3p_2^2).
- Your rank-one DC space u ⊗ W: levelness = Gct/L089 (M_k(xy^T) = k! e_k(x) e_k(y)) or
  Outside/L_gct_118 (perm(J+μuv^T) expansion); Outside/L_gct_121 explains the support condition.
- Your block multiplicativity of G_t = Outside/L_gct_110 (checked gluing).
- Your direction B (gradient) = Gct/L083 (checked).
- Bridge for formalizing anything stated with P_k: infra/Kit.lean `level_Mk_zero`,
  `level_inj_zero`, `level_of_Mk_zero`, `reduce_dc` (compiles).
construct (moment algebra A = C[x]/(x_i^2), shared-row gluing):
- per-block "all squarefree row moments vanish => <= c_b - 1": Gct/L098 (Lemma I, injective sums
  over column sets) and Gct/L090 / Helpers/ProdSigmaChain `chain` (diagonal products); Gct/L102
  (p+1 row subspaces with level sums + Y: <= p+q-2). Moebius injective->diagonal sums:
  Helpers/InvisibleBlock `diag_of_inj`.
- disjoint-block gluing: Outside/L_gct_110. Your shared-row gluing lemma is NOT checked (new).
- rectangular data points: L101/L_gct_108 (LS(2,q) = q-1), L156 (LS(3,q) <= q+1),
  L_gct_180 (4x5 row-centred: 6), L_gct_198/208 (4x6: 7), all consistent with LS(p,q) = p+q-3.
smallcases: L094 (n=3 <= 3), L_gct_109 (3x3 DC <= 1), L_gct_216 (4x4 DC <= 3), L_gct_217 (4x4
  row-centred <= 5), L_gct_197 (4x4 row-centred = 5), L_gct_189 (5x5 level space dim 7). n=4 full
  bound LS(4) <= 5 is open in the project (only LS4/* helpers).
  Note: of the .npy files in smallcases/, n4_d6_full_s1, n4_d3_dc_s3 and n5_d4_dc_s5 are NOT level
  (|perm(J+t)-n!| ~ 1e3 at random points, infra/chk.py); n4_d5_full_s0 is level (err 2e-7).

## KitFermat (infra, 11:32): inlined Kneser + iterated Fermat COMPILES (28 s, exit 0, format 0)
- infra/KitFermat.lean = stripped Kneser/SubalgFinite, ETransform, Assembly, FermatFromKneser,
  FermatIterated + L065 renamed PEqualNP.Gct.Kit086.kneser + L067 renamed
  PEqualNP.Gct.Kit086.fermat_iter (p_j|W = 0 for 2<=j<=k => k dim W <= M). Concatenate with
  Kit.lean (drop the duplicate import lines and the two test theorems) for any attempt that needs
  Kneser/Fermat. Plumbing note: Outside/L_gct_134 (k=4 DC identity) is already in the
  `Fin k ↪ Fin n` form produced by `level_inj_zero`; L_gct_105/106 (k=2,3) are in the
  "if i = k ∨ j = l then 0 else ..." curried form, so a small conversion lemma would be needed.

## Addendum for proof's "most promising next step" (D_m(n) <= n^2/m + O(n))  [infra, 11:34]
- Milestone "pure power-sum lemma" = CHECKED: Gct/L067 (k dim W <= M when p_2..p_k vanish on W).
  The +1 / p_1 refinement is not needed.
- m = 2 (isotropy) and m = 3 are CHECKED pieces: D_3(n) <= n^2/3 follows from L_gct_105 + L_gct_106
  (DC: 2M_2 = p_2, 6M_3 = 4p_3) + L061 (sharp Fermat). m = 4 is the first open step.
- For m = 4 the project already has a Kneser-type tool mixing isotropy with a 4th power sum:
  Gct/L163 (T3, from notes/gct-086-core, i.e. made for THIS gap): A+B totally isotropic,
  C ⊥ A, B and A∘B (Hadamard), sum a_i^4 = 0 on A  =>  dim A + dim B + dim C <= m. Plus
  Helpers/T3LemmaP (`iso_half`, `lemmaP`: isotropic subspace of a unital subalgebra H has dim
  <= dim H/2, strictly less if p_4 also vanishes). These are the natural ingredients for absorbing
  the graph terms of c_4 (sum r_i^2, sum c_j^2, tr((tt^T)^2)) — none of that absorption is checked.
- Caveat for the O(n) slack: it must be uniform in m (C_m bounded), and it must survive gluing
  (L_gct_110), since glued 4x4 circulant blocks have p_4 ≠ 0 in every n >= 4.
