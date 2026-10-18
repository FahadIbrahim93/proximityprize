/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ListDecoding.CZ25GeomCapacity

/-!
# The general T3.4 / coordinate-fiber-cap hypotheses need `η ≤ 1`

The C3.5 reduction chain (`frs_list_decoding_capacity_cz25_of_T34_T218`, the
`frs_list_decoding_capacity_cz25_of_residuals` / `_of_coordFiberCap_*` endpoints in
`ListDecoding/Bounds/SubspaceDesign.lean`, `CZ25CapacityReduction.lean` and
`CZ25GeomCapacity.lean`) takes ABF26 T3.4 [CZ25 B.5] (`hT34`) and the coordinate-fiber cap
(`hCap`) as hypotheses quantified over *every* τ-subspace-design code and every slack
`η' > 0`. Both evaluate the profile at `⌊1/η'⌋`.

`IsSubspaceDesign s τ C` constrains `τ r` only through subspaces of rank `≤ r`; at `r = 0`
the only such subspace is `⊥`, so `τ 0` is unconstrained. For `η' > 1` the floor is `0`, so
the radius `1 - τ 0 - η'` and the bound `(1 - τ 0)/η'` can be moved freely. With `τ 0 = -2`,
`η' = 2` the radius is `1` (every word is close) while the bound is `3/2`, and the full space
`(ZMod 2)^1` has two codewords. So the unrestricted hypotheses can never be supplied and every
theorem taking them was vacuous. The consumers only use `η ≤ 1` (`1/η` is a positive natural
number there), so the hypotheses are now stated for `0 < η' ≤ 1`.

This file keeps the failure of the old unrestricted shapes as an axiom-clean regression.
-/

open CodingTheory ListDecodable

namespace ProximityGap.CZ25T34TauZeroRegime

/-- A valid design profile for the full space: `τ 0 = -2` (unconstrained) and `τ r = 1` for
`r ≥ 1` (always valid, since `A ⊓ ker ≤ A`). -/
noncomputable def τZeroNeg : ℕ → ℝ := fun r => if r = 0 then -2 else 1

/-- The full space `(ZMod 2)^1` (one coordinate, fold `s = 1`). -/
abbrev fullCode : Submodule (ZMod 2) (Fin 1 → Fin 1 → ZMod 2) := ⊤

theorem isSubspaceDesign_τZeroNeg : IsSubspaceDesign 1 τZeroNeg fullCode := by
  intro r A _ hr
  rcases Nat.eq_zero_or_pos r with rfl | hpos
  · have hA : A = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hr)
    subst hA
    simp [τZeroNeg]
  · have hτ : τZeroNeg r = 1 := by simp [τZeroNeg, Nat.pos_iff_ne_zero.mp hpos]
    rw [hτ, mul_one]
    simp only [Finset.univ_unique, Finset.sum_singleton, Fintype.card_unique, Nat.cast_one,
      div_one]
    exact_mod_cast Submodule.finrank_mono inf_le_left

/-- At radius `1` both codewords of the full space `(ZMod 2)^1` are close to `0`. -/
theorem two_le_lambda_fullCode_one :
    (2 : ℕ∞) ≤ Lambda ((fullCode : Set (Fin 1 → Fin 1 → ZMod 2))) 1 := by
  have hall :
      closeCodewordsRel ((fullCode : Set (Fin 1 → Fin 1 → ZMod 2))) 0 1 = Set.univ := by
    ext c
    simp only [closeCodewordsRel, relHammingBall, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    refine ⟨Submodule.mem_top, ?_⟩
    have h1 : ((Code.relHammingDist (0 : Fin 1 → Fin 1 → ZMod 2) c : ℚ≥0) : ℝ) ≤ 1 := by
      exact_mod_cast Code.relHammingDist_le_one
    convert h1
  have hcard : (Set.univ : Set (Fin 1 → Fin 1 → ZMod 2)).ncard = 2 := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card]; rfl
  refine le_trans ?_ (le_iSup _ (0 : Fin 1 → Fin 1 → ZMod 2))
  rw [hall, hcard]; rfl

/-- **The old unrestricted `hT34` shape is false.** -/
theorem forall_T34_unguarded_false :
    ¬ (∀ (τ : ℕ → ℝ) (C : Submodule (ZMod 2) (Fin 1 → Fin 1 → ZMod 2)),
        IsSubspaceDesign 1 τ C → ∀ η' : ℝ, 0 < η' →
        (Lambda ((C : Set (Fin 1 → Fin 1 → ZMod 2)))
            (1 - τ (Nat.floor (1 / η')) - η') : ENNReal) ≤
          ENNReal.ofReal ((1 - τ (Nat.floor (1 / η'))) / η')) := by
  intro h
  have h2 := h τZeroNeg fullCode isSubspaceDesign_τZeroNeg 2 (by norm_num)
  have hfl : Nat.floor ((1 : ℝ) / 2) = 0 := by
    rw [Nat.floor_eq_zero]; norm_num
  have hτ0 : τZeroNeg 0 = -2 := by simp [τZeroNeg]
  rw [hfl, hτ0] at h2
  norm_num at h2
  have hle : ((2 : ℕ∞) : ENNReal) ≤ ENNReal.ofReal (3 / 2) :=
    le_trans (by exact_mod_cast two_le_lambda_fullCode_one) h2
  have h32 : ENNReal.ofReal (3 / 2) < 2 := by
    rw [show (2 : ENNReal) = ENNReal.ofReal 2 by simp]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
  exact absurd (lt_of_le_of_lt (by simpa using hle) h32) (lt_irrefl _)

/-- **The old unrestricted `hCap` shape is false** (it implies the old `hT34` shape through the
in-tree bridge `subspaceDesign_list_decoding_cz25_of_coordFiberCap`). -/
theorem forall_coordFiberCap_unguarded_false :
    ¬ (∀ (τ : ℕ → ℝ) (C : Submodule (ZMod 2) (Fin 1 → Fin 1 → ZMod 2))
        (h : IsSubspaceDesign 1 τ C) (η' : ℝ) (hη' : 0 < η'),
        CZ25CoordFiberCap 1 τ C h η' hη') := by
  intro hCap
  exact forall_T34_unguarded_false fun τ C h η' hη' =>
    subspaceDesign_list_decoding_cz25_of_coordFiberCap 1 τ C h η' hη' (hCap τ C h η' hη')

end ProximityGap.CZ25T34TauZeroRegime

#print axioms ProximityGap.CZ25T34TauZeroRegime.forall_T34_unguarded_false
#print axioms ProximityGap.CZ25T34TauZeroRegime.forall_coordFiberCap_unguarded_false
