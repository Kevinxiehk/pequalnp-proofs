# Team brief: gap L-gct-086 (open research problem, 45-minute team attempt)

You are one of five agents attacking ONE open problem from the public pequalnp-proofs project
(each gap is a Lean 4 statement that counts only when a proof checker accepts it). Full record:
/home/claude/work/L-gct-086/gap.json (read it).

## The question
For n x n complex matrices t, call a linear subspace L a *level space* if
perm(J + t) = n! for every t in L (J = all-ones matrix). Equivalently all the homogeneous
parts P_k(t) = sum over k x k partial permutations of the product of entries ("sums of k x k
subpermanents"), k = 1..n, vanish identically on L (scale t by a parameter).
Statement to prove: there is a constant C with dim L <= C * n for all n and all level spaces L.
The project says it MAY BE FALSE (then a family of level spaces of superlinear dimension refutes it).

Known and checked in the project (Lean files under /home/claude/pequalnp-proofs/lean/PEqualNP/,
READ-ONLY): a level space of dimension 2n - 3 exists (L-gct-080); the problem reduces to doubly
centred spaces, losing 2n (Gct/L092.lean); the 3 x 3 case (L-gct-094); product-type parts are
bounded (L-gct-090); many related lemmas in Outside/L_gct_1*.lean and Gct/L0*.lean (grep permPoly).
Easy facts: P_1 = 24-style sum of all entries; on doubly centred matrices P_2 is (up to a
constant) the sum of squares of entries, so a doubly centred level space has dim <= (n-1)^2 / 2.
Dead ends (do not retry): every form of "a level space splits into a row part and a column part"
(exact counterexamples); arguments of bounded Taylor order; anything that also works for the
determinant (the determinant analogue allows quadratic dimension), so a proof must use something
the permanent has and the determinant lacks; the project says a proof must use Taylor orders
growing with n.

## Hard limits
- Team deadline: stop and send your final report by 35 minutes after you start. The coordinator
  ends the attempt at 45 minutes.
- No heavy computation: no brute-force enumeration, Groebner bases on big systems, long SAT/solver
  runs, or anything taking more than ~2 minutes of CPU per run (2 CPU cores are shared by 5 agents).
  If a route clearly needs heavy computation, say so and stop that route.
- Do not touch /home/claude/pequalnp-proofs (read only), do not use git, do not contact
  pequalnp.com. Python: python3 -I (numpy/sympy available or pip install --break-system-packages).
- Lean (only if you are told to write Lean): compile only with
  /home/claude/tools/leancheck FILE /home/claude/work/L-gct-086/gap.json (about 50 s per run).

## Sharing
Work in /home/claude/work/L-gct-086/<your-role>/. Append short, concrete findings to
/home/claude/work/L-gct-086/NOTES-<your-role>.md as you go, and read the other NOTES-*.md files
every so often. If you find a counterexample family or a complete proof idea, write it at the top
of your notes file in a section headed RESULT.

## Final report (short)
What you established (with evidence), what you ruled out, and the single most promising next step.
