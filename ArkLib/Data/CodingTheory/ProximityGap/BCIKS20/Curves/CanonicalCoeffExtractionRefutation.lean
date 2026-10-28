/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves.CoeffExtractionResidual
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.StrictCoeffLargeReduction
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.StrictCoeffPolysExceptional
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Counterexamples to the strict-Johnson coefficient-extraction residuals

The BCIKS20 §5/§6 strict Johnson-branch extraction is formalized by five named residual surfaces:

* `CurveCommonAgreementResidual` (geometric form, the §5 root): the decoded family admits `k + 1`
  sample parameters whose decodings share a `≥ deg`-size agreement set with every good decoding;
* `StrictCoeffPolysResidual` (broad form): for every curve `u`, every parameter family `P` that is
  decoded on the good-coefficient set `S = RS_goodCoeffsCurve u δ` has coefficient polynomials
  `B j` of degree `< k + 1` interpolating `z ↦ (P z).coeff j` on `S`;
* `StrictCoeffPolysLargeResidual` (the large-good-set sector, equivalent to the broad form by
  `strictCoeffPolysResidual_iff_large`);
* `StrictCanonicalCoeffPolysResidual` (canonical form): one decoded family `P₀` carries such
  witnesses, and **every** other family decoded on `S` agrees with `P₀` on `S`;
* `StrictCoeffPolysExcResidual b` (the exceptional-set repair of the broad form): the same demand
  as `StrictCoeffPolysResidual`, relaxed to hold only at good parameters outside an exceptional
  set `E` with `E.card ≤ b`.

All five are false as stated, and one witness refutes them simultaneously — the geometric form
because it implies the broad form (`strictCoeffPolysResidual_of_commonAgreement`). The
exceptional-set
repair survives only once its budget reaches half the field: it is refuted at every `b` with
`2b + 2 < |F|`, which is the whole regime in which the repaired §6 consumer chain
(`correlatedAgreement_affine_curves_of_strict_coeff_polys_exc`, at proximity error
`errorBound + b/|F|`) is meant to run.

## The witness

* Coordinate set `ι = Fin 7`, evaluation domain the first seven elements of an enumeration of
  `GF(2⁶⁴)` (so `|F| = 2⁶⁴` and `|ι| = 7`);
* Reed–Solomon degree `deg = 2`, curve dimension `k = 1`, radius `δ = 3/7`;
* `linPoly = X - C (domain7 0)`, a monic linear polynomial, and `wLin` its codeword;
* `eWord` keeps `wLin` on the coordinates `{1, 2, 3}` and is zero elsewhere, so `eWord` is at
  relative distance exactly `3/7` from **both** codewords `wLin` and `0` (weight six, split
  evenly);
* `curveStack` is the constant curve `u 0 = eWord`, `u 1 = 0`, so every line word equals
  `eWord` and the good-coefficient set is all of `F`.

The probability hypothesis is satisfied because the field is huge: the rate is `2/7`, so in the
strict Johnson strip the BCIKS20 error bound is `errorBound δ 2 domain7 < 1`, and `|S|/|F| = 1`.

## Why the canonical form fails

The two constant families `P z = linPoly` and `P z = 0` are both decoded on all of `S` (degree
`< 2`, distance `3/7 ≤ δ`), while they differ at every `z`. Uniqueness would force
`linPoly = 0`, contradicting `linPoly.natDegree = 1`. The uniqueness clause — not the existence
of coefficient witnesses — is the false content.

## Why the broad form fails

The broad form quantifies over *every* decoded family, so we may choose an adversarial decoder.
Let `stepFamily z = linPoly` for `z ∈ {domain7 1, domain7 2}` and `stepFamily z = 0` otherwise.
Every member is decoded on all of `S`, but `(stepFamily z).coeff 1` is `1` exactly on the
two-point set `{domain7 1, domain7 2}` and `0` at `domain7 3` and `domain7 4`. A polynomial of
degree `< k + 1 = 2` cannot take the value `1` at `domain7 1` and `0` at the two distinct points
`domain7 3`, `domain7 4`, so no coefficient witness `B 1` exists. Since `|S| = 2⁶⁴ > k + 1`, the
same family refutes `StrictCoeffPolysLargeResidual`.

## Why the exceptional-set repair fails

`StrictCoeffPolysExcResidual b` keeps the adversarial decoder in play but lets the coefficient
identity fail on an exceptional set `E` of size `≤ b`. The `coeff 1` of the adversarial decoder is
now an *indicator function* instead of a two-point one: pick a parameter block `S` of size `b + 1`
and set `P z = linPoly` on `S`, `P z = 0` off `S`. Any witness `B 1` of degree `< 2` that matches
this indicator off `E` is impossible once `2b + 2 < |F|`: a nonzero polynomial of degree `≤ 1`
takes the value `0` at no more than one point, so the `|F| - (b + 1)` off-block parameters outside
`E` would all have to be that single point, while the very same estimate also forces
`|F| - (b + 1) - b ≤ 1`. In other words the repair needs a budget of at least half the field,
which is far outside the regime where the exceptional-set §6 consumer chain is meaningful.

## Scope

This refutes the five residual *statements* (and hence any unconditional use of them); it does not
refute the BCIKS20 list-decoding theorem, the production `δ*` conjecture, or the existence half of
the extraction. In particular it refutes the exceptional-set repair at every budget `2b + 2 < |F|`;
budgets at or above half the field are left untouched (no claim of satisfiability is made there).
A repaired statement must fix the decoded family canonically (a genuine canonical decoder) rather
than quantifying over all of them, or must restrict to a regime where decoding is unique, for
example below the unique-decoding radius. Axiom-clean:
`[propext, Classical.choice, Quot.sound]`.
-/

namespace ProximityGap

noncomputable section

open NNReal Finset Function ProbabilityTheory Code Polynomial
open scoped BigOperators LinearCode ProbabilityTheory ENNReal

namespace StrictCanonicalCoeffPolysRefutation

/-- The concrete field `GF(2⁶⁴)`, with `2⁶⁴` elements. -/
abbrev GF64 : Type := GaloisField 2 64

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : Fintype GF64 := Fintype.ofFinite _
local instance : DecidableEq GF64 := fun a b => Classical.propDecidable (a = b)

theorem card_GF64 : Fintype.card GF64 = 2 ^ 64 := by
  rw [Fintype.card_eq_nat_card, GaloisField.card (p := 2) (n := 64) (by norm_num)]

/-- A seven-point evaluation domain: the first seven elements of an enumeration of `GF(2⁶⁴)`. -/
def domain7 : Fin 7 ↪ GF64 :=
  ⟨fun i => (Fintype.equivFin GF64).symm ⟨(i : ℕ), by
      rw [card_GF64]; exact lt_trans i.isLt (by norm_num)⟩,
   fun i j h => Fin.ext (by
      simpa using congrArg Fin.val ((Fintype.equivFin GF64).symm.injective h))⟩

/-- A monic linear polynomial vanishing at the first domain point. -/
def linPoly : GF64[X] := (Polynomial.X : GF64[X]) - Polynomial.C (domain7 0)

lemma linPoly_natDegree : linPoly.natDegree = 1 := by
  rw [linPoly, natDegree_X_sub_C]

/-- The evaluation word of `linPoly`: a codeword that is zero at exactly one coordinate. -/
def wLin : Fin 7 → GF64 := fun i => linPoly.eval (domain7 i)

lemma wLin_mem : wLin ∈ ReedSolomon.code domain7 2 := by
  refine ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval linPoly ?_ ?_
  · rw [linPoly_natDegree]; norm_num
  · intro i; rfl

lemma wLin_eq_zero_iff (i : Fin 7) : wLin i = 0 ↔ i = 0 := by
  rw [wLin, linPoly, eval_sub, eval_X, eval_C, sub_eq_zero]
  exact domain7.injective.eq_iff

lemma wLin_ne_zero_iff (i : Fin 7) : wLin i ≠ 0 ↔ i ≠ 0 := by
  simp [wLin_eq_zero_iff]

lemma zero_eq_wLin_iff (i : Fin 7) : (0 : GF64) = wLin i ↔ i = 0 :=
  (eq_comm (a := (0 : GF64)) (b := wLin i)).trans (wLin_eq_zero_iff i)

/-- The test word: three of the six nonzero coordinates of `wLin`, zero on the rest. -/
def eWord : Fin 7 → GF64 := fun i => if i = 1 ∨ i = 2 ∨ i = 3 then wLin i else 0

lemma disagreement_e_zero :
    disagreementCols eWord (0 : Fin 7 → GF64) = ({1, 2, 3} : Finset (Fin 7)) := by
  ext i
  simp only [mem_disagreementCols, Pi.zero_apply, eWord]
  fin_cases i <;> simp [wLin_eq_zero_iff]

lemma disagreement_e_wLin :
    disagreementCols eWord wLin = ({4, 5, 6} : Finset (Fin 7)) := by
  ext i
  simp only [mem_disagreementCols, eWord]
  fin_cases i <;> simp [zero_eq_wLin_iff]

lemma hamming_e_zero : hammingDist eWord (0 : Fin 7 → GF64) = 3 := by
  rw [hammingDist_eq_disagreementCols_card, disagreement_e_zero]
  decide

lemma hamming_e_wLin : hammingDist eWord wLin = 3 := by
  rw [hammingDist_eq_disagreementCols_card, disagreement_e_wLin]
  decide

lemma relDist_e_zero : δᵣ(eWord, (0 : Fin 7 → GF64)) = (3 / 7 : ℚ≥0) := by
  rw [relHammingDist, hamming_e_zero, Fintype.card_fin]
  norm_num

lemma relDist_e_wLin : δᵣ(eWord, wLin) = (3 / 7 : ℚ≥0) := by
  rw [relHammingDist, hamming_e_wLin, Fintype.card_fin]
  norm_num

/-- The rational `3/7` has the same value under the two nonnegative coercions in play. -/
lemma coe_three_sevenths_nn : ((3 / 7 : ℚ≥0) : ℝ≥0) = (3 / 7 : ℝ≥0) := by
  apply NNReal.coe_injective
  push_cast
  norm_num

lemma coe_three_sevenths_ennreal :
    ((3 / 7 : ℚ≥0) : ENNReal) = ((3 / 7 : ℝ≥0) : ENNReal) := by
  rw [ENNReal.coe_NNRat_coe_NNReal, coe_three_sevenths_nn]

lemma relDistFromCode_e :
    δᵣ(eWord, ReedSolomon.code domain7 2) ≤ ((3 / 7 : ℝ≥0) : ENNReal) := by
  calc δᵣ(eWord, ReedSolomon.code domain7 2) ≤ δᵣ(eWord, wLin) :=
        relDistFromCode_le_relDist_to_mem eWord wLin wLin_mem
    _ = ((3 / 7 : ℚ≥0) : ENNReal) := by rw [relDist_e_wLin]
    _ = ((3 / 7 : ℝ≥0) : ENNReal) := coe_three_sevenths_ennreal

/-- The constant curve through `eWord`. -/
def curveStack : WordStack GF64 (Fin 2) (Fin 7) := fun t => if t = 0 then eWord else 0

lemma line_curveStack (z : GF64) :
    (∑ t : Fin 2, (z ^ (t : ℕ)) • curveStack t) = eWord := by
  simp [curveStack]

lemma mem_goodCoeffsCurve (z : GF64) :
    z ∈ RS_goodCoeffsCurve (k := 1) (deg := 2) (domain := domain7) curveStack (3 / 7) := by
  simp only [RS_goodCoeffsCurve, mem_filter, mem_univ, true_and]
  change δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • curveStack t, ReedSolomon.code domain7 2) ≤
    (3 / 7 : ℝ≥0)
  rw [line_curveStack]
  exact relDistFromCode_e

lemma goodCoeffsCurve_eq_univ :
    RS_goodCoeffsCurve (k := 1) (deg := 2) (domain := domain7) curveStack (3 / 7) = univ :=
  eq_univ_of_forall mem_goodCoeffsCurve

/-! ## The error bound is strictly below one -/

theorem rate_eq : (LinearCode.rate (ReedSolomon.code domain7 2) : ℝ≥0) = 2 / 7 := by
  rw [ReedSolomon.rateOfLinearCode_eq_div' (F := GF64) (α := domain7) (n := 2) (by decide)]
  rw [Fintype.card_fin]
  push_cast
  norm_num

theorem sqrt_two_sevenths_ge : (53 / 100 : ℝ) ≤ Real.sqrt (2 / 7) := by
  rw [Real.le_sqrt (by norm_num) (by norm_num)]
  norm_num

theorem sqrt_two_sevenths_le : Real.sqrt (2 / 7) ≤ (54 / 100 : ℝ) := by
  rw [Real.sqrt_le_left (by norm_num)]
  norm_num

theorem sqrt_two_sevenths_le_one : (2 / 7 : ℝ≥0).sqrt ≤ 1 :=
  calc (2 / 7 : ℝ≥0).sqrt ≤ (1 : ℝ≥0).sqrt :=
        (NNReal.sqrt_le_sqrt).2 (by rw [← NNReal.coe_le_coe]; norm_num)
    _ = 1 := NNReal.sqrt_one

theorem sqrtRate_le_one : ReedSolomon.sqrtRate 2 domain7 ≤ 1 := by
  rw [ReedSolomon.sqrtRate, rate_eq]
  exact sqrt_two_sevenths_le_one

theorem johnson_side_lt :
    (1 - (LinearCode.rate (ReedSolomon.code domain7 2) : ℝ≥0)) / 2 < (3 / 7 : ℝ≥0) := by
  have h27 : (2 / 7 : ℝ≥0) ≤ 1 := by
    rw [← NNReal.coe_le_coe]
    norm_num
  rw [rate_eq, ← NNReal.coe_lt_coe]
  simp only [NNReal.coe_div, NNReal.coe_sub h27, NNReal.coe_ofNat]
  norm_num

theorem sqrtRate_lt : (3 / 7 : ℝ≥0) < 1 - ReedSolomon.sqrtRate 2 domain7 := by
  rw [ReedSolomon.sqrtRate, rate_eq, ← NNReal.coe_lt_coe]
  rw [NNReal.coe_sub sqrt_two_sevenths_le_one]
  simp only [Real.coe_sqrt, NNReal.coe_one, NNReal.coe_div, NNReal.coe_ofNat]
  linarith [sqrt_two_sevenths_le]

/-- In the strict Johnson interior the BCIKS20 error bound is strictly smaller than one, so the
probability hypothesis `Pr > k · errorBound` is satisfiable with `Pr = 1`. -/
theorem errorBound_lt_one : errorBound (3 / 7 : ℝ≥0) 2 domain7 < 1 := by
  classical
  set r : ℝ≥0 := (LinearCode.rate (ReedSolomon.code domain7 2) : ℝ≥0) with hr
  have hUD : ¬ (3 / 7 : ℝ≥0) ≤ (1 - r) / 2 := by
    rw [hr]
    exact not_le.mpr johnson_side_lt
  have hδ' : (3 / 7 : ℝ≥0) < 1 - r.sqrt := by
    rw [hr]
    exact sqrtRate_lt
  have hmem2 : (1 - r) / 2 < (3 / 7 : ℝ≥0) ∧ (3 / 7 : ℝ≥0) < 1 - r.sqrt :=
    ⟨lt_of_not_ge hUD, hδ'⟩
  simp only [errorBound, ← hr, Set.mem_Icc, zero_le, hUD, and_false,
    ↓reduceIte, Set.mem_Ioo, hmem2, and_self, coe_pow, NNReal.coe_natCast,
    coe_min, NNReal.coe_div, Real.coe_sqrt, NNReal.coe_ofNat]
  change (↑2 ^ 2 : ℝ) /
      ((2 * min (↑(1 - r.sqrt - (3 / 7 : ℝ≥0)) : ℝ) (Real.sqrt (r : ℝ) / 20)) ^ 7 *
        (Fintype.card GF64 : ℝ)) < 1
  set m : ℝ := min (↑(1 - r.sqrt - (3 / 7 : ℝ≥0)) : ℝ) (Real.sqrt (r : ℝ) / 20) with hm
  have hcoer : ((1 - r.sqrt - (3 / 7 : ℝ≥0) : ℝ≥0) : ℝ) = 1 - Real.sqrt (r : ℝ) - 3 / 7 := by
    have hsr : r.sqrt ≤ 1 := by
      rw [hr]; exact sqrtRate_le_one
    have hd : (3 / 7 : ℝ≥0) ≤ 1 - r.sqrt := by
      rw [le_tsub_iff_right hsr, ← NNReal.coe_le_coe]
      push_cast
      have h27 : ((r : ℝ≥0) : ℝ) = 2 / 7 := by
        rw [hr, rate_eq]
        push_cast
        norm_num
      rw [h27]
      linarith [sqrt_two_sevenths_le]
    rw [NNReal.coe_sub hd, NNReal.coe_sub hsr, Real.coe_sqrt]
    have h27 : ((r : ℝ≥0) : ℝ) = 2 / 7 := by
      rw [hr, rate_eq]
      push_cast
      norm_num
    rw [h27]
    norm_num
  have hs_le : Real.sqrt (r : ℝ) ≤ (54 / 100 : ℝ) := by
    have h27 : ((r : ℝ≥0) : ℝ) = 2 / 7 := by
      rw [hr, rate_eq]
      push_cast
      norm_num
    rw [h27]
    exact sqrt_two_sevenths_le
  have hs_ge : (53 / 100 : ℝ) ≤ Real.sqrt (r : ℝ) := by
    have h27 : ((r : ℝ≥0) : ℝ) = 2 / 7 := by
      rw [hr, rate_eq]
      push_cast
      norm_num
    rw [h27]
    exact sqrt_two_sevenths_ge
  have harg1 : (53 / 2000 : ℝ) ≤ (↑(1 - r.sqrt - (3 / 7 : ℝ≥0)) : ℝ) := by
    rw [hcoer]
    linarith
  have harg2 : (53 / 2000 : ℝ) ≤ Real.sqrt (r : ℝ) / 20 := by linarith
  have hm_ge : (53 / 2000 : ℝ) ≤ m := by
    rw [hm]
    exact le_min harg1 harg2
  have h2m_ge : (53 / 1000 : ℝ) ≤ 2 * m := by linarith
  have hpow_ge : (53 / 1000 : ℝ) ^ 7 ≤ (2 * m) ^ 7 :=
    pow_le_pow_left₀ (by norm_num) h2m_ge 7
  have hq : (Fintype.card GF64 : ℝ) = 2 ^ 64 := by
    rw [card_GF64]
    norm_num
  have hden_ge : (53 / 1000 : ℝ) ^ 7 * 2 ^ 64 ≤ (2 * m) ^ 7 * (Fintype.card GF64 : ℝ) := by
    rw [hq]
    exact mul_le_mul hpow_ge le_rfl (by positivity) (by positivity)
  have hden_pos : 0 < (2 * m) ^ 7 * (Fintype.card GF64 : ℝ) :=
    lt_of_lt_of_le (by norm_num) hden_ge
  rw [div_lt_one hden_pos]
  have h4 : (4 : ℝ) < (53 / 1000 : ℝ) ^ 7 * 2 ^ 64 := by norm_num
  linarith

/-! ## The probability hypothesis -/

/-- The good-coefficient set is the whole field, so a random line is close to the code with
probability `1`, which dominates `k · errorBound`. -/
theorem prob_gt_k_errorBound :
    Pr_{let z ← $ᵖ GF64}[
      δᵣ(∑ t : Fin (1 + 1), (z ^ (t : ℕ)) • curveStack t,
        ReedSolomon.code domain7 2) ≤ (3 / 7 : ℝ≥0)] >
      (((1 : ℕ) : ENNReal) * (errorBound (3 / 7 : ℝ≥0) 2 domain7 : ENNReal)) := by
  rw [prob_close_curve_eq_card_goodCoeffsCurve_div_card (k := 1) (deg := 2)
    (domain := domain7) (δ := (3 / 7 : ℝ≥0)) curveStack]
  rw [goodCoeffsCurve_eq_univ, Finset.card_univ]
  simp only [Nat.cast_one, one_mul]
  rw [ENNReal.div_self (by simp) (by simp), ← ENNReal.coe_one]
  change ((errorBound (3 / 7 : ℝ≥0) 2 domain7 : ℝ≥0) : ENNReal) <
    ((1 : ℝ≥0) : ENNReal)
  rw [ENNReal.coe_lt_coe]
  exact errorBound_lt_one

/-! ## The canonical refutation -/

/-- **The canonical strict coefficient-polynomial residual is false as stated.** The constant
curve through `eWord` has good-coefficient set all of `F`, and the two constant decoded families
`linPoly` and `0` violate the uniqueness clause at every parameter. -/
theorem not_strictCanonicalCoeffPolysResidual :
    ¬ StrictCanonicalCoeffPolysResidual (k := 1) (deg := 2) (domain := domain7)
      (δ := (3 / 7 : ℝ≥0)) := by
  classical
  intro h
  obtain ⟨P₀, _hCoeff, huniq⟩ :=
    h (by norm_num) curveStack prob_gt_k_errorBound johnson_side_lt sqrtRate_lt
  have hPc : ∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := 2) (domain := domain7) curveStack
      (3 / 7 : ℝ≥0),
      ((fun _ : GF64 => linPoly) z).natDegree < 2 ∧
        δᵣ(∑ t : Fin (1 + 1), (z ^ (t : ℕ)) • curveStack t,
          ((fun _ : GF64 => linPoly) z).eval ∘ domain7) ≤ (3 / 7 : ℝ≥0) := by
    intro z _
    constructor
    · change linPoly.natDegree < 2
      rw [linPoly_natDegree]
      norm_num
    · change δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • curveStack t, linPoly.eval ∘ domain7) ≤
        (3 / 7 : ℝ≥0)
      rw [line_curveStack, show (linPoly.eval ∘ domain7) = wLin from rfl, relDist_e_wLin,
        coe_three_sevenths_nn]
  have hP0 : ∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := 2) (domain := domain7) curveStack
      (3 / 7 : ℝ≥0),
      ((fun _ : GF64 => (0 : GF64[X])) z).natDegree < 2 ∧
        δᵣ(∑ t : Fin (1 + 1), (z ^ (t : ℕ)) • curveStack t,
          ((fun _ : GF64 => (0 : GF64[X])) z).eval ∘ domain7) ≤ (3 / 7 : ℝ≥0) := by
    intro z _
    constructor
    · change (0 : GF64[X]).natDegree < 2
      rw [natDegree_zero]
      norm_num
    · change δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • curveStack t,
        ((fun _ : GF64 => (0 : GF64[X])) z).eval ∘ domain7) ≤ (3 / 7 : ℝ≥0)
      rw [line_curveStack]
      have hz : ((fun _ : GF64 => (0 : GF64[X])) z).eval ∘ domain7 = (0 : Fin 7 → GF64) := by
        funext i
        simp
      rw [hz, relDist_e_zero, coe_three_sevenths_nn]
  have h1 : linPoly = P₀ 0 := by
    simpa using huniq (fun _ : GF64 => linPoly) hPc 0 (mem_goodCoeffsCurve 0)
  have h0 : (0 : GF64[X]) = P₀ 0 := by
    simpa using huniq (fun _ : GF64 => (0 : GF64[X])) hP0 0 (mem_goodCoeffsCurve 0)
  have hc : linPoly = 0 := by rw [h1, ← h0]
  have hdeg : linPoly.natDegree = 0 := by rw [hc, natDegree_zero]
  rw [linPoly_natDegree] at hdeg
  norm_num at hdeg

/-! ## The broad refutation

The broad residual quantifies over *every* decoded family, so the constant families above are not
needed: an adversarial decoder whose coefficients cannot possibly be interpolated refutes it. -/

/-- Two evaluation points at which the adversarial decoder selects `linPoly`. -/
def stepSet : Finset GF64 := {domain7 1, domain7 2}

/-- The adversarial decoder attached to a parameter block `S`: `linPoly` on `S`, the zero
polynomial elsewhere. Every member is decoded at every parameter, while
`(blockFamily S z).coeff 1` is the indicator function of `S`. -/
def blockFamily (S : Finset GF64) : GF64 → GF64[X] := fun z => if z ∈ S then linPoly else 0

/-- The two-point adversarial decoder: `linPoly` on `stepSet`, the zero polynomial elsewhere. -/
def stepFamily : GF64 → GF64[X] := blockFamily stepSet

lemma mem_stepSet_one : domain7 1 ∈ stepSet := by
  simp [stepSet]

lemma notMem_stepSet_three : domain7 3 ∉ stepSet := by
  simp only [stepSet, mem_insert, mem_singleton, not_or]
  exact ⟨fun h => absurd (domain7.injective h) (by decide),
    fun h => absurd (domain7.injective h) (by decide)⟩

lemma notMem_stepSet_four : domain7 4 ∉ stepSet := by
  simp only [stepSet, mem_insert, mem_singleton, not_or]
  exact ⟨fun h => absurd (domain7.injective h) (by decide),
    fun h => absurd (domain7.injective h) (by decide)⟩

lemma blockFamily_coeff_one_of_mem {S : Finset GF64} {z : GF64} (hz : z ∈ S) :
    (blockFamily S z).coeff 1 = 1 := by
  rw [show blockFamily S z = linPoly from by simp [blockFamily, hz]]
  simp [linPoly]

lemma blockFamily_coeff_one_of_notMem {S : Finset GF64} {z : GF64} (hz : z ∉ S) :
    (blockFamily S z).coeff 1 = 0 := by
  rw [show blockFamily S z = (0 : GF64[X]) from by simp [blockFamily, hz]]
  simp

lemma stepFamily_coeff_one_of_mem {z : GF64} (hz : z ∈ stepSet) :
    (stepFamily z).coeff 1 = 1 :=
  blockFamily_coeff_one_of_mem hz

lemma stepFamily_coeff_one_of_notMem {z : GF64} (hz : z ∉ stepSet) :
    (stepFamily z).coeff 1 = 0 :=
  blockFamily_coeff_one_of_notMem hz

/-- Every member of the adversarial family is decoded on the good-coefficient set. -/
lemma blockFamily_decoded (S : Finset GF64) (z : GF64) :
    (blockFamily S z).natDegree < 2 ∧
      δᵣ(∑ t : Fin (1 + 1), (z ^ (t : ℕ)) • curveStack t,
        (blockFamily S z).eval ∘ domain7) ≤ (3 / 7 : ℝ≥0) := by
  by_cases hz : z ∈ S
  · rw [show blockFamily S z = linPoly from by simp [blockFamily, hz]]
    exact ⟨by rw [linPoly_natDegree]; norm_num, by
      rw [line_curveStack, show (linPoly.eval ∘ domain7) = wLin from rfl, relDist_e_wLin,
        coe_three_sevenths_nn]⟩
  · rw [show blockFamily S z = (0 : GF64[X]) from by simp [blockFamily, hz]]
    constructor
    · rw [natDegree_zero]
      norm_num
    · rw [line_curveStack]
      have hz0 : ((0 : GF64[X]).eval ∘ domain7) = (0 : Fin 7 → GF64) := by
        funext i
        simp
      rw [hz0, relDist_e_zero, coe_three_sevenths_nn]

lemma stepFamily_decoded (z : GF64) :
    (stepFamily z).natDegree < 2 ∧
      δᵣ(∑ t : Fin (1 + 1), (z ^ (t : ℕ)) • curveStack t,
        (stepFamily z).eval ∘ domain7) ≤ (3 / 7 : ℝ≥0) :=
  blockFamily_decoded stepSet z

/-- **The broad strict coefficient-polynomial residual is false as stated.** The adversarial
decoder is decoded at every parameter, but `(stepFamily z).coeff 1` is the indicator of a
two-point set, which no polynomial of degree `< k + 1 = 2` can interpolate on `S = univ`. -/
theorem not_strictCoeffPolysResidual :
    ¬ StrictCoeffPolysResidual (k := 1) (deg := 2) (domain := domain7)
      (δ := (3 / 7 : ℝ≥0)) := by
  classical
  intro h
  obtain ⟨B, hBdeg, hBeval⟩ :=
    h (by norm_num) curveStack prob_gt_k_errorBound johnson_side_lt sqrtRate_lt
      stepFamily (fun z _ => stepFamily_decoded z)
  have h1 : (B 1).eval (domain7 1) = 1 := by
    have h' := hBeval (domain7 1) (mem_goodCoeffsCurve (domain7 1)) 1 (by norm_num)
    rw [stepFamily_coeff_one_of_mem mem_stepSet_one] at h'
    exact h'.symm
  have h3 : (B 1).eval (domain7 3) = 0 := by
    have h' := hBeval (domain7 3) (mem_goodCoeffsCurve (domain7 3)) 1 (by norm_num)
    rw [stepFamily_coeff_one_of_notMem notMem_stepSet_three] at h'
    exact h'.symm
  have h4 : (B 1).eval (domain7 4) = 0 := by
    have h' := hBeval (domain7 4) (mem_goodCoeffsCurve (domain7 4)) 1 (by norm_num)
    rw [stepFamily_coeff_one_of_notMem notMem_stepSet_four] at h'
    exact h'.symm
  have hcard : ({domain7 3, domain7 4} : Finset GF64).card = 2 :=
    Finset.card_pair (fun hEq => absurd (domain7.injective hEq) (by decide))
  have hB1 : B 1 = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (B 1)
      {domain7 3, domain7 4} ?_ ?_
    · intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact h3
      · rw [mem_singleton.mp hx]
        exact h4
    · rw [hcard]
      simpa using hBdeg 1 (by norm_num)
  rw [hB1, Polynomial.eval_zero] at h1
  exact one_ne_zero h1.symm

/-- **The large-sector strict coefficient-polynomial residual is false as stated.** By
`strictCoeffPolysResidual_iff_large` the adversarial curve — whose good-coefficient set has
`|S| = 2⁶⁴ > k + 1 = 2` — refutes the sector that carries the content of the residual. -/
theorem not_strictCoeffPolysLargeResidual :
    ¬ StrictCoeffPolysLargeResidual (k := 1) (deg := 2) (domain := domain7)
      (δ := (3 / 7 : ℝ≥0)) :=
  fun hLarge =>
    not_strictCoeffPolysResidual
      (strictCoeffPolysResidual_of_large (k := 1) (deg := 2) (domain := domain7)
        (δ := (3 / 7 : ℝ≥0)) hLarge)

/-! ## The geometric refutation

`CurveCommonAgreementResidual` is the transparent geometric form of the §5 extraction: the
decoded family must admit `k + 1` sample parameters whose decodings share a `≥ deg`-size common
agreement set with `P z` at every good `z`. Since
`strictCoeffPolysResidual_of_commonAgreement` derives the algebraic broad form from it, the same
witness refutes the geometric statement. -/

/-- **The geometric §5 common-agreement residual is false as stated.** It implies the broad
coefficient-polynomial form (`strictCoeffPolysResidual_of_commonAgreement`), which the adversarial
curve refutes at these parameters. -/
theorem not_curveCommonAgreementResidual :
    ¬ CurveCommonAgreementResidual (k := 1) (deg := 2) (domain := domain7)
      (δ := (3 / 7 : ℝ≥0)) :=
  fun h =>
    not_strictCoeffPolysResidual
      (strictCoeffPolysResidual_of_commonAgreement (k := 1) (deg := 2)
        (domain := domain7) (δ := (3 / 7 : ℝ≥0)) h)

/-! ## The exceptional-set refutation

`StrictCoeffPolysExcResidual b` relaxes the broad form by allowing the coefficient identity to
fail on an exceptional parameter set of size `≤ b`. The relaxation does not rescue the statement
in the regime where it is used: a block decoder of block size `b + 1` has an indicator function
as its `coeff 1`, and a degree `≤ 1` polynomial cannot match a `0/1` function off `b` exceptions
unless the field has at most `2b + 2` elements. -/

/-- **The exceptional-set strict coefficient-polynomial residual is false below half the field.**
For every budget `b` with `2b + 2 < |F|`, the block decoder on a `(b + 1)`-point parameter set is
decoded on the whole good-coefficient set but admits no witness `B 1` matching the indicator
function of the block off any exceptional set of size `≤ b`. -/
theorem not_strictCoeffPolysExcResidual_of_two_mul_add_two_lt_card {b : ℕ}
    (hb : 2 * b + 2 < Fintype.card GF64) :
    ¬ StrictCoeffPolysExcResidual (k := 1) (deg := 2) (domain := domain7)
      (δ := (3 / 7 : ℝ≥0)) b := by
  classical
  intro h
  obtain ⟨S, _hSsub, hScard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset GF64)) (n := b + 1) (by
      rw [Finset.card_univ]
      omega)
  obtain ⟨B, E, hEcard, hBdeg, hBid⟩ :=
    h (by norm_num) curveStack prob_gt_k_errorBound johnson_side_lt sqrtRate_lt
      (blockFamily S) (fun z _ => blockFamily_decoded S z)
  have hB1deg : (B 1).natDegree < 2 := hBdeg 1 (by norm_num)
  rcases eq_or_ne (B 1) 0 with hB0 | hBne
  · -- A vanishing witness forces the parameter block into the exceptional set.
    have hsub : S ⊆ E := by
      intro z hz
      by_contra hzE
      have h' := hBid z (mem_goodCoeffsCurve z) hzE 1 (by norm_num)
      rw [blockFamily_coeff_one_of_mem hz, hB0, Polynomial.eval_zero] at h'
      exact one_ne_zero h'
    have := Finset.card_le_card hsub
    omega
  · -- Otherwise the vanishing set of `B 1` has at most one point, yet it must contain every
    -- off-block parameter outside `E`.
    have hZle : (Finset.univ.filter (fun z => (B 1).eval z = 0)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb'
      by_contra hab
      have ha' : (B 1).eval a = 0 := (Finset.mem_filter.mp ha).2
      have hb'' : (B 1).eval b = 0 := (Finset.mem_filter.mp hb').2
      have hcard : ({a, b} : Finset GF64).card = 2 := Finset.card_pair hab
      have hzero : B 1 = 0 := by
        refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (B 1) {a, b} ?_ ?_
        · intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact ha'
          · rw [Finset.mem_singleton.mp hx]
            exact hb''
        · rw [hcard]
          exact hB1deg
      exact hBne hzero
    have hsub : (Finset.univ \ S) \ E ⊆
        Finset.univ.filter (fun z => (B 1).eval z = 0) := by
      intro z hz
      have hzS : z ∉ S := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2
      have hzE : z ∉ E := (Finset.mem_sdiff.mp hz).2
      have h' := hBid z (mem_goodCoeffsCurve z) hzE 1 (by norm_num)
      rw [blockFamily_coeff_one_of_notMem hzS] at h'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, h'.symm⟩
    have hcard₁ : ((Finset.univ \ S) \ E).card ≤ 1 :=
      le_trans (Finset.card_le_card hsub) hZle
    have hcard₂ : (Finset.univ \ S).card - E.card ≤ ((Finset.univ \ S) \ E).card :=
      Finset.le_card_sdiff E (Finset.univ \ S)
    have hUS : (Finset.univ \ S).card = Fintype.card GF64 - S.card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
    omega

/-- In particular the exceptional-set residual fails at budget `1`: a two-point block already
defeats every exceptional set of size `≤ 1`. -/
theorem not_strictCoeffPolysExcResidual_one :
    ¬ StrictCoeffPolysExcResidual (k := 1) (deg := 2) (domain := domain7)
      (δ := (3 / 7 : ℝ≥0)) 1 := by
  refine not_strictCoeffPolysExcResidual_of_two_mul_add_two_lt_card ?_
  rw [card_GF64]
  norm_num

end StrictCanonicalCoeffPolysRefutation

end

end ProximityGap

/-! ## Axiom audit -/

open ProximityGap.StrictCanonicalCoeffPolysRefutation

#print axioms not_strictCanonicalCoeffPolysResidual
#print axioms not_strictCoeffPolysResidual
#print axioms not_strictCoeffPolysLargeResidual
#print axioms not_curveCommonAgreementResidual
#print axioms not_strictCoeffPolysExcResidual_of_two_mul_add_two_lt_card
#print axioms not_strictCoeffPolysExcResidual_one
#print axioms errorBound_lt_one
