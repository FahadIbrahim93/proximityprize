# Open-math hypotheses for the remaining #301/#302/#304(/#232) kernels — 2026-06-10

Literature swept: BCIKS20 (J.ACM'23), ABF26 open-problems (eprint 2026/680), CS25
"On RS Proximity Gaps Conjectures" (eprint 2025/2046 — up-to-capacity conjectures DISPROVED,
replaced by the entropic bound `H_q(δ) < 1−ρ`), ECCC 2025/169 (zero-loss/O(n)-exceptions
proximity gaps up to Johnson + Ω(n^1.99) lower bounds AT Johnson), the folded-RS subspace-design
proximity gaps (arXiv 2601.10047, June 2026), Fenzi–Sanso attacks (2025/2197), the syndrome-lens
preprint (2025/1712 — overclaimed per our CapacityVacuity kernels), Conway–Jones (Acta Arith. 30,
1976) / Lam–Leung (2000) / Lenstra's survey on vanishing sums of roots of unity (no formalization
exists anywhere — checked), and the in-tree state (this repo's DISPROOF_LOG O104–O123, the
GS-surface lane, `SectionGlobalLift`, the SZ/ThresholdKSF budget machinery).

The genuinely open kernels these target:
(i) the §5 Johnson-branch `StrictCoeffPolysResidual` and §6.2 `BoundaryCardResidual`
(the non-vacuous BCIKS20 list-decoding CA — gates #304→#302/#301 large-field);
(ii) `hRsep` (trivariate GS-interpolant separability) and fiber-section coherence
(the two residuals of `SectionGlobalLift`);
(iii) the #232 walls: Lam–Leung minimal sums, the both-dead-cosets stall (O122), δ*.

Per-hypothesis discipline: constraints → new direction → why nobody has done it → larp-check
(have they actually?) → what is novel → the hypothesis → proof plan.

## Known-grounded hypotheses

### K1 — Fiber-section coherence is free (interpolation rigidity of surface branches)
- **Constraints**: `SectionGlobalLift.section_dvd_global_of_fibers` needs the fiber sections
  `v_y` to be readings of ONE global `w` (`v_y = w.eval (C y)`); the documented gap.
- **New direction**: don't ASSUME coherence — derive it. The `v_y` are roots of the SAME
  surface `R(y, ·, ·)`; a root-choice function that agrees with a degree-`< k` polynomial at
  `k+1` centres off the discriminant locus IS that polynomial's branch everywhere off the locus
  (resultant separation of branches).
- **Why not done**: the two layers (per-place sections, global factor) were built in different
  waves; nobody asked whether coherence is implied rather than assumed.
- **Larp-check**: branch-separation off the discriminant is classical (algebraic-function
  theory); the LEAN bridge from `DiscriminantBadSet` to a coherence lemma does not exist.
- **Novel**: the formal lemma; the math is standard.
- **Hypothesis**: if `(T − C v_y) ∣ evalX (C y) R` for all `y ∈ S`, `disc ≠ 0` on `S`, and the
  Lagrange interpolant `w` of `{(y, v_y)}` on any `natDegree`-bounded subset has
  `natDegreeY w < k`, then `v_y = w.eval (C y)` for ALL `y ∈ S` (coherence), hence `hdvdR`
  fires via the landed lifting.
- **Proof plan**: per-centre uniqueness of the section among roots ≡ the discriminant
  nonvanishing already in `DiscriminantBadSet`; then two coherent families agreeing at
  > deg-many centres coincide (the landed `section_dvd_global_of_fibers` counting reused).

### K2 — ECCC 2025/169's O(n)-exceptions structure discharges §5 at Johnson with ε = O(n)/q
- **Constraints**: our keystone consumes `StrictCoeffPolysResidual (ε := errorBound)` with
  errorBound = deg²/((2m)⁷q) in the interior; the §5 extraction is THE wall.
- **New direction**: 2025/169 proves zero proximity loss with O(n) exceptional values up to
  Johnson — a DIFFERENT (better-error, worse-radius-sharpness) tradeoff than BCIKS20 §5.
  Restated: the bad-set of lines is O(n), so `ε = O(n)/q` suffices — and our keystone chain is
  already parametric in ε.
- **Why not done**: the paper postdates the in-tree §5 formalization; nobody re-targeted the
  residual to the new bad-set bound.
- **Larp-check**: real paper (ECCC 2025/169); its positive technique must be read in full
  before formalizing (only abstract verified).
- **Novel**: first formalization of the 2025/169 positive result; the re-targeting lemma.
- **Hypothesis**: `StrictCoeffPolysResidual (k) (deg) (domain) (δ)` holds for δ < Johnson with
  ε replaced by `C·n/q` for an explicit constant C, via the 2025/169 exceptional-set bound.
- **Proof plan**: agent reads the paper's §(positive results), extracts the combinatorial core
  (likely a Berlekamp–Welch-style counting over the line pencil), formalizes the bad-set
  cardinality, plugs into `curveCommonAgreementResidual_of_card_le`'s parametric shape.

### K3 — CA ⟹ list-decodability (CS25 Prop) sharpens the leaderboard Y-side
- **Constraints**: the leaderboard's attack side wants the largest provable winning set.
- **New direction**: CS25 proves correlated agreement with small error implies list
  decodability; contrapositive: list-decoding LOWER bounds (known beyond Johnson for some RS)
  force CA error lower bounds — a new mechanical Y-side source.
- **Why not done**: the implication is new (Nov 2025) and its formalization touches both our
  CA defs and `ListDecodability.lean` — cross-file work nobody owned.
- **Larp-check**: implication stated in 2025/2046 (verified via abstract + search snippets).
- **Novel**: the formal implication + its leaderboard wiring.
- **Hypothesis**: `δ_ε_correlatedAgreementCurves (ε) → listDecodable C δ L(ε)` formalizes with
  explicit L(ε), and instantiating known non-list-decodable parameter points yields
  `soundnessError ≥ 2^{-Y'}` with Y' < current Y at some regime.
- **Proof plan**: formalize the probabilistic argument (a random combination of a too-big list
  violates CA); wire to `Leaderboard.lean`.

### K4 — `hRsep` eliminated by the radical (squarefree-part) substitution
- **Constraints**: `Section5GlobalAssembler` takes `hRsep : R.Separable`; known-open for the
  GS interpolant; but every USE is branch-separation (no double root at the section).
- **New direction**: replace `R` by its radical `R*` throughout the bundle: `(Y′−C w) ∣ R ⟹
  (Y′−C w) ∣ R*` (linear factors divide the radical), degrees only shrink (budgets survive),
  and `R*` IS separable in char 0 / char > deg (Mathlib `RingTheory/Polynomial/Radical`).
- **Why nobody did it**: the bundle hypotheses were transcribed from the paper, which assumes
  squarefreeness as part of "the GS step" silently.
- **Larp-check**: radical machinery exists in Mathlib (verified file list); the char caveat is
  genuine — must be carried as `char F = 0 ∨ CharP.char F > natDegree R` (fine: prize fields
  are large-char).
- **Novel**: the substitution theorem `ofProducersOn_global_radical` deleting `hRsep`.
- **Hypothesis**: the global assembler holds with `hRsep` REPLACED by a characteristic bound,
  via the radical substitution.
- **Proof plan**: `radical_separable` (char hypothesis) + `dvd_radical_of_dvd` for the linear
  factor + degree monotonicity through the budget lemmas.

### K5 — Lam–Leung from Mann's induction (closing O116's kernel; first formalization anywhere)
- **Constraints**: O116 reduced Lam–Leung to: minimal vanishing sums at squarefree n (≥ 3
  primes) have weight in ℕp₁+…+ℕp_k. Conway–Jones/Mann is the standard source; NO
  formalization exists (checked: Mathlib, AFP-equivalents, literature).
- **New direction**: Mann's proof is elementary: a minimal relation lives in ℚ(ζ_n); reduce
  mod the largest prime p | n via the degree-(p−1) minimal polynomial of ζ_p over ℚ(ζ_{n/p});
  minimality forces the relation to be a union of full ζ_p-fibers — weight gains a factor p.
- **Why not done**: pre-O116 the statement wasn't isolated as the single missing kernel; the
  cyclotomic-tower machinery in Mathlib only recently matured (FLT-regular work).
- **Larp-check**: Mathlib has `IsCyclotomicExtension` towers, `Polynomial.cyclotomic`, the
  degree formulas; the fiber-collapse argument is not there.
- **Novel**: first machine-checked Mann/Conway–Jones structure theorem; closes the #232
  two-prime → general-k arc (O104+O110+O116 then give full Lam–Leung).
- **Hypothesis**: minimal vanishing ℕ-weights over μ_n (n squarefree) lie in ℕp₁+…+ℕp_k —
  formalizable from Mathlib's cyclotomic machinery in one arc.
- **Proof plan**: induction on the number of primes; the ζ_p-fiber decomposition via the
  ℚ(ζ_{n/p})-linear independence of `1, ζ_p, …, ζ_p^{p−2}`.

## Advanced hypotheses (new math)

### A1 — Folding transfer: folded-RS proximity gaps re-enter the plain-RS chain
- **Constraints**: 2025/169's Ω(n^1.99) lower bound blocks plain-RS Johnson-radius gaps with
  small exceptional sets; but STIR/WHIR/FRI only ever USE folded oracles downstream.
- **New direction**: arXiv 2601.10047 (June 2026) gets OPTIMAL proximity gaps for folded RS
  via subspace designs. The protocols fold anyway — so re-route the per-round soundness through
  folded-CA + a transfer lemma, never demanding plain-RS gaps beyond Johnson.
- **Why not done**: the folded result is weeks old; no soundness chain (formal or paper) has
  been re-based onto it.
- **Larp-check**: the paper is real but I have only a small-model summary — an agent MUST read
  the PDF (saved locally at tool-results/webfetch-…mqbr63.pdf) and verify the exact statement
  before anything else. The transfer lemma may lose exactly what the lower bound says it must.
- **Novel**: the transfer lemma `foldedCA(r) ⟹ plainCA(r′)` with explicit loss, and the
  protocol re-basing. Calibrated expectation: the WIN is in error/exception size at fixed
  radius (≤ Johnson), not radius beyond Johnson (which 2025/169 forbids cheaply).
- **Hypothesis**: per-round STIR/WHIR soundness holds with the folded-RS subspace-design error
  bound — strictly better constants than `errorBound` in the smooth regime — via a linear-map
  CA-transfer lemma through the fold.
- **Proof plan**: read paper → state foldedCA in our `Code` language → transfer through
  `Fri/EvenAndOdd`-style fold algebra → swap into `PerRoundCA`.

### A2 — The syndrome lens, salvaged on its validity domain
- **Constraints**: 2025/1712 claimed capacity via a syndrome-space basis change; our
  `CapacityVacuity` kernels show the general claim fails (parity/3-div/6-div obstructions).
- **New direction**: characterize the EXACT validity domain: words whose syndrome weight
  distribution avoids the vacuity kernels ("syndrome-balanced"); prove CA up to the entropic
  bound (the corrected CS25 target!) on that subclass; protocol-level self-reduction
  (shift/rejection) into the subclass.
- **Why not done**: the community discarded 1712 wholesale; our kernels are the only precise
  failure analysis, and only we can cut along them.
- **Larp-check**: 1712 exists and is flawed (our own refutation); the salvage does not exist.
- **Novel**: the validity-domain characterization and the conditional capacity statement.
- **Hypothesis**: there is a syndrome-balance predicate B(u) with (a) CA up to `H_q(δ)<1−ρ`
  for stacks satisfying B, and (b) a 1-round self-reduction making any protocol word satisfy B
  with ≤ 1/q error.
- **Proof plan**: extract B from the CapacityVacuity counterexample family (they are the
  coset-structured words of O111!); attempt (a) on the two-prime structured subfamily first.

### A3 — The windowed coset law as the §6 boundary counter on smooth domains
- **Constraints**: `BoundaryCardResidual` (§6.2) needs cardinality control of boundary bad
  sets over the evaluation domain; FRI/STIR domains are SMOOTH — exactly cosets of 2-power
  roots of unity; our O111 windowed law classifies vanishing weighted power-sum patterns over
  μ_n COMPLETELY (union of μ_d-coset indicator combinations, d > t).
- **New direction**: re-express the §6.2 boundary bad-set conditions as power-sum windows over
  the smooth domain; apply O111 to get STRUCTURE (alive-coset unions) and the O123 budget
  mechanism for cardinality — a counting theorem replacing the paper's analytic §6.2 argument
  on smooth domains.
- **Why not done**: the #232 lane and the #304 lane evolved独立ly (different waves); O111/O123
  are days old and ours alone.
- **Larp-check**: the precise §6.2 bad-set shape must be confirmed power-sum-expressible
  (agent task 0); if it isn't, the hypothesis dies honestly.
- **Novel**: cross-lane unification — prize-side spectral rigidity counting a SNARK-side
  residual. Exactly the "interpolate parts of the code" win the user asked for.
- **Hypothesis**: over smooth domains, `BoundaryCardResidual` reduces to a windowed-coset count
  bounded by the O123 alive-trace injection — discharging §6.2 for all FRI/STIR/WHIR
  instantiations (which are smooth) without the general-field argument.
- **CORRECTED 2026-06-10 (larp-check fired on our own tree)**: `BoundaryCardResidual` is
  ALREADY REFUTED in-tree (`not_boundaryCardResidual` + two counterexample families,
  axiom-clean; the def survives only as a documented-false assumption surface). The boundary
  is not open — it is false; the strict chain avoids it. A3 must be retargeted at the §5
  strict-interior object (`StrictCanonicalCoeffPolysResidual` / the `RS_goodCoeffsCurve`
  counting) — whether THAT bad set is power-sum-expressible over smooth domains is the
  corrected open question.
- **CORRECTED 2026-10-22**: that retarget is dead as stated too.
  `StrictCanonicalCoeffPolysResidual` is now refuted in-tree, axiom-clean
  (`ProximityGap.StrictCanonicalCoeffPolysRefutation.not_strictCanonicalCoeffPolysResidual`
  in `BCIKS20/Curves/CanonicalCoeffExtractionRefutation.lean`): its uniqueness clause is false,
  since a constant curve makes the good-coefficient set the whole field and one word can sit at
  the same radius from two distinct codewords. The same witness refutes the broad
  `StrictCoeffPolysResidual` and its large-good-set sector `StrictCoeffPolysLargeResidual`
  (`not_strictCoeffPolysResidual`, `not_strictCoeffPolysLargeResidual`): an adversarial decoder
  is decoded everywhere while its `coeff 1` layer is a two-point indicator, which no degree
  `< k + 1` polynomial interpolates. The same witness also kills the exceptional-set repair
  `StrictCoeffPolysExcResidual b` at every budget `2b + 2 < |F|`
  (`not_strictCoeffPolysExcResidual_of_two_mul_add_two_lt_card`, plus the concrete `b = 1`
  instance `not_strictCoeffPolysExcResidual_one`): a block decoder's `coeff 1` is the indicator
  of a `(b + 1)`-point parameter block, which cannot be matched off fewer than half the field's
  worth of exceptions. So "allow `O(n)` exceptional parameters" is NOT an adequate repair; the
  §5 strict-interior target must be re-stated (existence-only extraction, a fixed canonical
  decoder, or uniqueness below the unique-decoding radius), not taken as given. The geometric
  root of the chain falls too: `CurveCommonAgreementResidual` is refuted at the same witness by
  `not_curveCommonAgreementResidual`, since it implies the broad form via
  `strictCoeffPolysResidual_of_commonAgreement`. Census: `docs/wiki/residual-census.md`.
- **Proof plan**: shape-confirmation; then the window dictionary (`O111` is at modulus n with
  arbitrary Z-weights — the boundary weights are the coefficient extractions); then O123.

### A4 — The gap-divisor factorization theorem (O122 engine (b)) via Newton + Kronecker
- **Constraints**: the both-dead-cosets stall blocks the per-element induction; engine (b)
  restates the law as: a monic divisor of `X^n − 1` over ℚ whose elementary symmetric
  functions e₁…e_t vanish is a product of binomials `X^d − γ`, d | n, d > t.
- **New direction**: Newton's identities convert the window (p₁…p_t = 0) to e₁…e_t = 0; the
  root-of-unity constraint (all roots in μ_n) is the rigidity source — Kronecker-type: the
  polynomial is determined by its high coefficients among μ_n-divisors, and binomials are the
  only gap-t-compatible factor shapes (probe-verified 349/349, O122).
- **Why not done**: this exact statement appears in NO literature found (searches: "gap
  divisor X^n-1 binomial factorization", Newton window cyclotomic) — it sits between
  trigonometric diophantine equations and coding theory; our probes are the only evidence.
- **Larp-check**: genuine novelty risk is INVERSE here — it may be FALSE in a corner (probes
  passed; ℚ vs F_q matters; the agent must also probe characteristic-p).
- **Novel**: the theorem itself — new elementary number theory if true.
- **Hypothesis**: (ℚ form) any monic `g ∣ X^n − 1` with `e_i(g) = 0` for `1 ≤ i ≤ t` factors
  as `∏ (X^{d_j} − γ_j)` with `d_j ∣ n`, `d_j > t`, `γ_j ∈ μ_{n/d_j}`.
- **RESOLVED 2026-06-10 (probe + counterexample; DISPROOF_LOG O124)**: general n FALSE
  (Conway–Jones (5:6) minimal sum at n = 30); prime powers TRUE in all probes with the proof
  skeleton mapped (tower basis + cross-fiber recombination); two primes = K5's kernel exactly.
  Corrected target: the prime-power multiset window law (the A3-relevant case).
- **Proof plan**: induction on deg g: the smallest j with e_j ≠ 0 must be a multiple of some
  d > t by the μ_n constraint (sub-hypothesis: the minimal support gap of a μ_n-product is a
  divisor); peel the corresponding binomial via the O116 minimal-sum machinery.

### A5 — A generic RBR budget calculus for PIT-block chains (unification metatheorem)
- **Constraints**: WHIR and STIR sub-unit budgets are being proven per-protocol; each needs
  the same三 steps (threshold KSF, flip→salvage reduction, SZ count).
- **New direction**: a typeclass `PITBlock` (a block whose verifier decision is a polynomial
  identity test of challenge-degree ≤ d) with a METATHEOREM: any seqCompose/append chain of
  PIT-blocks has RBR knowledge soundness at budget `fun c => d_c/|F|` — turning the
  bounded-flip shell + SZ core + the append RBR keystone into a budget CALCULATOR.
- **Why not done**: paper proofs are per-protocol by culture; no formal library has an RBR
  budget calculus (checked: no analogue in our tree or in the cited formalizations).
- **Larp-check**: the components all exist in-tree NOW (this session); only the abstraction
  is missing — low risk, high DRY value.
- **Novel**: formalization-architecture novelty; collapses the remaining #301(c)/#302
  sub-unit work into instances.
- **Hypothesis**: the metatheorem `pitChain_rbrKnowledgeSoundness` holds and WHIR's checked
  verifier + STIR's 3-slot block are instances.
- **Proof plan**: define the class around `rbrKnowledgeSoundness_of_flipBound`'s hFlip shape;
  prove the chain composition by the unconditional append RBR keystone; instantiate.

## Unification observations (independent of the hypotheses)
1. `stirOStmtRel`/`stirVOStmtRel`/`whirRelation` are one relation family (statement-indexed
   proximity); a single polymorphic def would DRY three files.
2. The threshold-KSF discharge pattern has now been applied verbatim to WHIR and STIR —
   evidence for A5's metatheorem.
3. `Section5GlobalAssembler` + `SectionGlobalLift` + `GSSurfaceData` are three doors to one
   room; after K1/K4 they should merge into a single `GSDecoderOutput` interface.
4. Smoothness is load-bearing in BOTH lanes (#232 windows need μ_n; FRI domains are μ_{2^k}) —
   A3 is the bridge; if it works, `BoundaryCardResidual` and the O123 budget are the SAME LEMMA.
