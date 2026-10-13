/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikhail Izhutkin (mashingaan, @mashingaan)
-/
import scratch.IncidenceTripleMass
import scratch.IncidenceAffineLines

set_option autoImplicit false

namespace ProximityGap.IncidenceCanonicalTriples

open ProximityGap.IncidenceTripleMass ProximityGap.IncidenceAffineLines

/-- Triple-incidence mass excludes an over-budget family of canonical bad witnesses.
The support predicate is the unfolded minimum-distance bound for the code. -/
theorem no_bad_witness_family_of_triple_budget
    {F I X A : Type} [Field F] [Fintype I] [DecidableEq I]
    [Fintype X] [Nonempty X] [DecidableEq X] [AddCommGroup A] [Module F A]
    (gamma : I → F) (w : I → (X → A)) (hinj : Function.Injective gamma)
    (C : Submodule F (X → A)) (d t s : ℕ) (hs : 2 ≤ s)
    (htn : t ≤ Fintype.card X)
    (hC : ∀ z ∈ C, (∃ B : Finset X, B.card ≤ d ∧ ∀ x ∉ B, z x = 0) → z = 0)
    (T : I → Finset X) (u0 u1 : X → A)
    (hwC : ∀ i, w i ∈ C)
    (hcompl : ∀ i, (T i)ᶜ.card ≤ t)
    (hwag : ∀ i, ∀ x ∈ T i, w i x = u0 x + gamma i • u1 x)
    (hno : ∀ i, ¬ ∃ f0 ∈ C, ∃ f1 ∈ C,
      ∀ x ∈ T i, f0 x = u0 x ∧ f1 x = u1 x)
    (hbig : s * Fintype.card X ^ 2 * (d + 1) * Fintype.card I ^ 3 +
        s * (Fintype.card I * (Fintype.card X - t)) ^ 3 >
      s * Fintype.card X ^ 3 * Fintype.card I ^ 3 +
        Fintype.card X ^ 2 * (d + 1) *
          (s * Fintype.card I * (t + 1) ^ 2 + 3 * Fintype.card I ^ 3 +
            s ^ 2 * Fintype.card I ^ 2 + 3 * s * Fintype.card I ^ 2)) : False := by
  classical
  have hpad : ∀ i, ∃ E : Finset X, (T i)ᶜ ⊆ E ∧ E.card = t := by
    intro i
    obtain ⟨E,hTE,_,hcard⟩ := Finset.exists_subsuperset_card_eq
      (Finset.subset_univ ((T i)ᶜ)) (hcompl i) (by simpa using htn)
    exact ⟨E,hTE,hcard⟩
  choose E hTE hEcard using hpad
  have hlow := bad_witness_triple_mass_lower gamma w hinj Finset.univ C d t s hs
    hC T u0 u1 (fun i _ => hwC i) (fun i _ => hcompl i)
    (fun i _ => hwag i) (fun i _ => hno i)
  simp only [Finset.card_univ] at hlow
  have hmono : (∑ a, ∑ b, ∑ c, (((T a)ᶜ ∪ (T b)ᶜ) ∪ (T c)ᶜ).card) ≤
      ∑ a, ∑ b, ∑ c, (E a ∪ E b ∪ E c).card := by
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro b _
    apply Finset.sum_le_sum
    intro c _
    exact Finset.card_le_card
      (Finset.union_subset_union (Finset.union_subset_union (hTE a) (hTE b)) (hTE c))
  have hmonoS := Nat.mul_le_mul_left s hmono
  have hlowN := Nat.mul_le_mul_left (Fintype.card X ^ 2) hlow
  have hmonoN := Nat.mul_le_mul_left (Fintype.card X ^ 2) hmonoS
  have hupp := triple_union_mass_bound E t hEcard
  have huppS := Nat.mul_le_mul_left s hupp
  nlinarith [hlowN,hmonoN,huppS,hbig]

end ProximityGap.IncidenceCanonicalTriples

#print axioms ProximityGap.IncidenceCanonicalTriples.no_bad_witness_family_of_triple_budget
