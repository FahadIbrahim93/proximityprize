/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikhail Izhutkin (mashingaan, @mashingaan)
-/
import Mathlib

set_option autoImplicit false
namespace ProximityGap.IncidenceTripleMass

/-- The integer-degree triple incidence mass uses this division-free cube bound. -/
theorem cube_sum_le_card_sq_mul_sum_cube
    {I : Type} [Fintype I] [Nonempty I]
    (d : I → ℝ) (hd : ∀ i, 0 ≤ d i) :
    (∑ i, d i) ^ 3 ≤ (Fintype.card I : ℝ) ^ 2 * ∑ i, (d i) ^ 3 := by
  classical
  let N : ℝ := Fintype.card I
  let S : ℝ := ∑ i, d i
  let mean : ℝ := S / N
  have hN : 0 < N := by
    change 0 < (Fintype.card I : ℝ)
    exact_mod_cast (show 0 < Fintype.card I from Fintype.card_pos)
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => hd i)
  have hm : 0 ≤ mean := div_nonneg hS0 hN.le
  have hS : S = mean * N := by
    dsimp [mean]
    rw [div_mul_cancel₀ _ (ne_of_gt hN)]
  have hterm : ∀ i, 3 * mean ^ 2 * d i - 2 * mean ^ 3 ≤ (d i) ^ 3 := by
    intro i
    have hp := mul_nonneg (sq_nonneg (d i - mean))
      (add_nonneg (hd i) (mul_nonneg (by norm_num) hm))
    nlinarith
  have hmean : N * mean ^ 3 ≤ ∑ i, (d i) ^ 3 := by
    calc
      N * mean ^ 3 = ∑ i, (3 * mean ^ 2 * d i - 2 * mean ^ 3) := by
        simp only [Finset.sum_sub_distrib, ← Finset.mul_sum,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        change N * mean ^ 3 = 3 * mean ^ 2 * S - 2 * (N * mean ^ 3)
        rw [hS]
        ring
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hterm i)
  have hmul := mul_le_mul_of_nonneg_left hmean (sq_nonneg N)
  change S ^ 3 ≤ N ^ 2 * ∑ i, (d i) ^ 3
  calc
    S ^ 3 = N ^ 2 * (N * mean ^ 3) := by
      rw [hS]
      ring
    _ ≤ _ := hmul

end ProximityGap.IncidenceTripleMass
#print axioms ProximityGap.IncidenceTripleMass.cube_sum_le_card_sq_mul_sum_cube
