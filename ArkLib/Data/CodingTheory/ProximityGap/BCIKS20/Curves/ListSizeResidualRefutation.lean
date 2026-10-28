/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves.ListSizeResidual
import Mathlib.Algebra.Field.ZMod

/-!
# Counterexample to the unconditional RS curve list-size residual

`ProximityGap.RSCurveListSizeResidual` is documented as the single remaining
research input for the strict-Johnson Reed–Solomon proximity gap.  Its statement, however,
carries none of the strict-Johnson hypotheses of the sibling coefficient-polynomial residuals:
there is no regime hypothesis `δ < 1 - √ρ`, no probability hypothesis
`Pr > k·errorBound`, and no canonical-choice restriction on the per-parameter codeword map
`cw`.  This file kernel-checks a counterexample at the closed Johnson boundary.

* coordinate domain `ι = Fin 4`;
* field `F = ZMod 7`;
* Reed–Solomon degree `deg = 1`, so codewords are constant functions on the four points;
* curve dimension parameter `k = 1`;
* `δ = 1 - √(1/4) = 1/2` and `e = 2`; then `(1-δ)·4 = 2 = 4 - e`, so the size hypothesis
  `(1-δ)·|ι| ≤ |ι| - e` of `RS_jointAgreement_of_curveListSizeResidual` holds with equality;
* stack `u 0 = 0`, `u 1 = (1, 1, 0, 0)`, so the curve word at parameter `z` is `(z, z, 0, 0)`;
* `cw z = constant z`.

Every parameter `z ∈ F` is good (the good set is all of `F`), every `cw z` lies in the code
and agrees with the curve word on two coordinates, yet the image of `cw` on the good set has
seven elements.  The conclusion of the residual would therefore require `7·(1·4) < 7`.

Hence the residual is false as stated, and the unconditional definition cannot be the
strict-Johnson input: a surviving form has to restrict `δ` to the strict sub-Johnson band
`δ < 1 - √ρ`, keep the probability hypothesis that makes the good set nonempty, and pin down
the codeword choice, exactly as the coefficient-polynomial residuals do.

## Verification
`./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves/ListSizeResidualRefutation.lean`

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (list-decoding extraction), §6.2 (closed Johnson boundary at `1 - √ρ`).
-/

namespace ProximityGap

namespace RSCurveListSizeRefutation

open Code NNReal
open scoped BigOperators NNReal ENNReal

private instance : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

abbrev I : Type := Fin 4
abbrev F : Type := ZMod 7

/-- Four distinct evaluation points in `ZMod 7`. -/
def domain : I ↪ F where
  toFun i := (i : ℕ)
  inj' := by
    intro a b h
    apply Fin.ext
    have h' : (((a : ℕ) : ZMod 7) = ((b : ℕ) : ZMod 7)) := h
    have hmod := (ZMod.natCast_eq_natCast_iff' (a : ℕ) (b : ℕ) 7).mp h'
    have ha7 : (a : ℕ) < 7 := by omega
    have hb7 : (b : ℕ) < 7 := by omega
    rwa [Nat.mod_eq_of_lt ha7, Nat.mod_eq_of_lt hb7] at hmod

/-- Curve stack `u 0 = 0`, `u 1 = (1, 1, 0, 0)`: the word at `z` is `(z, z, 0, 0)`. -/
def uFlat : WordStack F (Fin (1 + 1)) I :=
  ![![0, 0, 0, 0], ![1, 1, 0, 0]]

/-- Per-parameter codeword choice: the constant word with value `z`. -/
def cw (z : F) : I → F := ReedSolomon.constantCode z I

theorem word_flat_zero (z : F) :
    (∑ t : Fin (1 + 1), (z ^ (t : ℕ)) • uFlat t) (0 : I) = z := by
  simp [uFlat, Fin.sum_univ_two]

theorem word_flat_one (z : F) :
    (∑ t : Fin (1 + 1), (z ^ (t : ℕ)) • uFlat t) (1 : I) = z := by
  simp [uFlat, Fin.sum_univ_two]

/-- A word agreeing with a constant on two distinct coordinates is within relative distance
`1/2` of it. -/
theorem relDist_half_of_agree {w : I → F} {c : F} {i j : I} (hij : i ≠ j)
    (hi : w i = c) (hj : w j = c) :
    δᵣ(w, ReedSolomon.constantCode c I) ≤ (1 : ℝ≥0) / 2 := by
  rw [Code.relCloseToWord_iff_exists_agreementCols]
  refine ⟨{i, j}, ?_, ?_⟩
  · rw [Finset.card_pair hij]
    norm_num [I]
  · intro k
    constructor
    · intro hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · simpa [ReedSolomon.constantCode] using hi
      · simpa [ReedSolomon.constantCode] using hj
    · intro hne hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact hne (by simpa [ReedSolomon.constantCode] using hi)
      · exact hne (by simpa [ReedSolomon.constantCode] using hj)

/-- Every parameter is good: the curve word `(z, z, 0, 0)` agrees with the constant word `z`
on coordinates `0` and `1`, hence has relative distance at most `1/2 = 1 - √ρ`. -/
theorem flat_good (z : F) :
    z ∈ RS_goodCoeffsCurve (k := 1) (deg := 1) (domain := domain) uFlat
      ((1 : ℝ≥0) / 2) := by
  simp only [RS_goodCoeffsCurve, Finset.mem_filter, Finset.mem_univ, true_and]
  refine le_trans
    (Code.relDistFromCode_le_relDist_to_mem
      _ (ReedSolomon.constantCode z I) (by simp)) ?_
  have hpair := relDist_half_of_agree (w := ∑ t : Fin (1 + 1), (z ^ (t : ℕ)) • uFlat t)
    (c := z) (i := 0) (j := 1) (by decide) (word_flat_zero z) (word_flat_one z)
  exact_mod_cast hpair

/-- The chosen codeword agrees with the curve word on at least `|ι| - 2 = 2` coordinates. -/
theorem flat_agreement (z : F) :
    Fintype.card I - 2 ≤
      (Finset.univ.filter (fun i =>
        ∑ t : Fin (1 + 1), z ^ (t : ℕ) * uFlat t i = cw z i)).card := by
  have hsub : ({0, 1} : Finset I) ⊆
      Finset.univ.filter (fun i =>
        ∑ t : Fin (1 + 1), z ^ (t : ℕ) * uFlat t i = cw z i) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · simp [cw, ReedSolomon.constantCode, uFlat]
    · simp [cw, ReedSolomon.constantCode, uFlat]
  calc Fintype.card I - 2 = 2 := by decide
    _ = ({0, 1} : Finset I).card := by decide
    _ ≤ _ := Finset.card_le_card hsub

theorem cw_mem (z : F) :
    cw z ∈ (ReedSolomon.code domain 1 : Set (I → F)) := by
  simpa [cw] using (ReedSolomon.constantCode_mem_code (α := domain) (n := 1) (x := z))

theorem cw_injective : Function.Injective cw := by
  intro z1 z2 h
  have h0 := congrFun h (0 : I)
  simpa [cw, ReedSolomon.constantCode] using h0

theorem cw_image_card : (Finset.univ.image cw).card = 7 := by
  rw [Finset.card_image_of_injective _ cw_injective]
  simp [F]

/-- The unconditional RS curve list-size residual is false at the closed Johnson boundary
`δ = 1 - √ρ`: the good set is all of `ZMod 7`, every chosen codeword is within distance `δ`,
and the seven distinct constant codewords violate `L · k · |ι| < |G|`. -/
theorem not_rsCurveListSizeResidual :
    ¬ RSCurveListSizeResidual (k := 1) (deg := 1) (domain := domain)
      (δ := (1 : ℝ≥0) / 2) 2 := by
  intro h
  have hconcl := h uFlat cw (fun z _ => cw_mem z) (fun z _ => flat_agreement z)
  have hG :
      RS_goodCoeffsCurve (k := 1) (deg := 1) (domain := domain) uFlat
        ((1 : ℝ≥0) / 2) = Finset.univ := by
    ext z
    simpa [one_div] using flat_good z
  rw [hG, cw_image_card] at hconcl
  norm_num [I] at hconcl

end RSCurveListSizeRefutation

end ProximityGap

/-! ## Axiom audit -/
#print axioms ProximityGap.RSCurveListSizeRefutation.relDist_half_of_agree
#print axioms ProximityGap.RSCurveListSizeRefutation.word_flat_zero
#print axioms ProximityGap.RSCurveListSizeRefutation.flat_good
#print axioms ProximityGap.RSCurveListSizeRefutation.flat_agreement
#print axioms ProximityGap.RSCurveListSizeRefutation.cw_mem
#print axioms ProximityGap.RSCurveListSizeRefutation.cw_image_card
#print axioms ProximityGap.RSCurveListSizeRefutation.not_rsCurveListSizeResidual
