/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Counterexample to `StrictCanonicalCoeffPolysResidual`

`StrictCanonicalCoeffPolysResidual` is the canonical-family form of the BCIKS20 §5/§6
strict Johnson-branch coefficient extraction. Besides supplying one decoded family `P₀` with
coefficient-polynomial witnesses, it asks that **every** family `P` that is decoded on the
good-coefficient set `S = RS_goodCoeffsCurve u δ` agree with `P₀` on `S`.

That uniqueness clause is false as stated: decoding inside a `δ`-ball need not be unique, and
`S` is allowed to contain parameters where two distinct decoded families are simultaneously
close to the curve word. This file gives a kernel-checked counterexample.

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

The two constant families `P z = linPoly` and `P z = 0` are therefore both decoded on all of
`S` (degree `< 2`, distance `3/7 ≤ δ`), while they differ at every `z`. Uniqueness would force
`linPoly = 0`, contradicting `linPoly.natDegree = 1`.

The probability hypothesis is satisfied because the field is huge: the rate is `2/7`, so in the
strict Johnson strip the BCIKS20 error bound is `errorBound δ 2 domain7 < 1`, and `|S|/|F| = 1`.

## Scope

This refutes `StrictCanonicalCoeffPolysResidual` (and hence any unconditional use of it) as a
mathematical statement; it does not refute the BCIKS20 list-decoding theorem, the production
`δ*` conjecture, or the existence half of the residual. A repaired statement must either make
the choice of `P₀` part of the data (a genuine canonical decoder) or restrict `P` by a
uniqueness hypothesis, for example by working below the unique-decoding radius. Axiom-clean:
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

/-! ## The refutation -/

/-- **The canonical strict coefficient-polynomial residual is false as stated.** The constant
curve through `eWord` has good-coefficient set all of `F`, and the two constant decoded families
`linPoly` and `0` violate the uniqueness clause at every parameter. -/
theorem not_strictCanonicalCoeffPolysResidual :
    ¬ StrictCanonicalCoeffPolysResidual (k := 1) (deg := 2) (domain := domain7)
      (δ := (3 / 7 : ℝ≥0)) := by
  classical
  have hprob :
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
  intro h
  obtain ⟨P₀, _hCoeff, huniq⟩ := h (by norm_num) curveStack hprob johnson_side_lt sqrtRate_lt
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

end StrictCanonicalCoeffPolysRefutation

end

end ProximityGap

/-! ## Axiom audit -/

#print axioms ProximityGap.StrictCanonicalCoeffPolysRefutation.not_strictCanonicalCoeffPolysResidual
#print axioms ProximityGap.StrictCanonicalCoeffPolysRefutation.errorBound_lt_one
