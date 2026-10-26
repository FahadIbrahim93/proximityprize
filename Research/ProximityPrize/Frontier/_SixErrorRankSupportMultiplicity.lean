/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under both MIT and Apache-2.0 licenses as described in LICENSE.
Authors: Mikhail Izhutkin (mashingaan, @mashingaan)
-/
import Mathlib.Tactic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Coordinate support forced by low rank

If every `r` members of an `n`-vector family are linearly independent while
the full span has dimension at most `r`, each active coordinate must occur in
at least `n - r + 1` vectors. Summing this multiplicity yields a support-mass
lower bound. At `n = 6` and `r = 4`, this is the rank-four obstruction used in
six-error circuit analysis. It is a necessary condition, not an independence
result.
-/

set_option autoImplicit false
attribute [local instance] Classical.propDecidable

namespace ProximityGap.SixErrorRankSupportMultiplicity

/-- If every `r` vectors are independent and the whole family has rank at
most `r`, an active coordinate occurs in at least `n - r + 1` vectors. -/
theorem rank_coordinate_multiplicity
    {F Coord : Type} [Field F] [Fintype Coord] {n r : ℕ}
    (hrn : r ≤ n) (e : Fin n → (Coord → F))
    (hLI : ∀ b : Fin r → Fin n, Function.Injective b →
      LinearIndependent F (fun j => e (b j)))
    (hrank : Module.finrank F (Submodule.span F (Set.range e)) ≤ r)
    (x : Coord) (hactive : ∃ j, e j x ≠ 0)
    (N : Finset (Fin n)) (hNmem : ∀ j, j ∈ N ↔ e j x ≠ 0) :
    n - r + 1 ≤ N.card := by
  classical
  by_contra hn
  let Z := {j : Fin n // e j x = 0}
  have hN : Fintype.card {j : Fin n // ¬ e j x = 0} ≤ n - r := by
    rw [Fintype.card_of_subtype (p := fun j : Fin n => ¬ e j x = 0) N hNmem]
    omega
  have hcomp := Fintype.card_subtype_compl (fun j : Fin n => e j x = 0)
  have hZle := Fintype.card_subtype_le (fun j : Fin n => e j x = 0)
  have hZcard : r ≤ Fintype.card Z := by
    simp only [Fintype.card_fin] at hcomp hZle
    dsimp [Z]
    omega
  let bz : Fin r → Z := fun j =>
    (Fintype.equivFin Z).symm (Fin.castLE hZcard j)
  let b : Fin r → Fin n := fun j => (bz j).val
  have hb : Function.Injective b := by
    intro i j hij
    have hs : bz i = bz j := Subtype.ext hij
    have hf : Fin.castLE hZcard i = Fin.castLE hZcard j :=
      (Fintype.equivFin Z).symm.injective hs
    apply Fin.ext
    exact congrArg (fun k : Fin (Fintype.card Z) => k.val) hf
  have hLIb := hLI b hb
  have hspan : Submodule.span F (Set.range (fun j => e (b j))) ≤
      Submodule.span F (Set.range e) := by
    apply Submodule.span_mono
    rintro z ⟨j, rfl⟩
    exact ⟨b j, rfl⟩
  have heq := Submodule.eq_of_le_of_finrank_le hspan (by
    rw [finrank_span_eq_card hLIb]
    simpa using hrank)
  let ev : (Coord → F) →ₗ[F] F :=
    LinearMap.proj (R := F) (φ := fun _ : Coord => F) x
  have hvan : Submodule.span F (Set.range (fun j => e (b j))) ≤
      LinearMap.ker ev := by
    apply Submodule.span_le.mpr
    rintro z ⟨j, rfl⟩
    exact (bz j).property
  obtain ⟨k, hk⟩ := hactive
  apply hk
  have hm : e k ∈ Submodule.span F (Set.range (fun j => e (b j))) := by
    rw [heq]
    exact Submodule.subset_span ⟨k, rfl⟩
  exact hvan hm

/-- The coordinate multiplicity forces `n - r + 1` incidences per active
coordinate, even when supplied supports include coordinates where a vector
vanishes. -/
theorem rank_support_mass
    {F Coord : Type} [Field F] [Fintype Coord] [DecidableEq Coord]
    {n r : ℕ} (hrn : r ≤ n) (e : Fin n → (Coord → F)) (Q : Fin n → Finset Coord)
    (hsupport : ∀ j, ∀ x ∉ Q j, e j x = 0)
    (hLI : ∀ b : Fin r → Fin n, Function.Injective b →
      LinearIndependent F (fun j => e (b j)))
    (hrank : Module.finrank F (Submodule.span F (Set.range e)) ≤ r) :
    (n - r + 1) * (Finset.univ.filter (fun x => ∃ j, e j x ≠ 0)).card ≤
      ∑ j, (Q j).card := by
  classical
  let S := Finset.univ.filter (fun x => ∃ j, e j x ≠ 0)
  have hpoint : ∀ x : Coord, (if x ∈ S then n - r + 1 else 0) ≤
      ∑ j : Fin n, if x ∈ Q j then 1 else 0 := by
    intro x
    by_cases hx : x ∈ S
    · have hmul := rank_coordinate_multiplicity hrn e hLI hrank x
        ((Finset.mem_filter.mp hx).2)
        (Finset.univ.filter (fun j => e j x ≠ 0)) (fun j => by simp)
      have hcount : (Finset.univ.filter (fun j : Fin n => e j x ≠ 0)).card ≤
          ∑ j : Fin n, if x ∈ Q j then 1 else 0 := by
        rw [Finset.card_filter]
        apply Finset.sum_le_sum
        intro j _
        by_cases he : e j x = 0
        · simp [he]
        · have hxQ : x ∈ Q j := by
            by_contra h
            exact he (hsupport j x h)
          simp [he, hxQ]
      simpa only [if_pos hx] using hmul.trans hcount
    · simp only [if_neg hx]
      exact Nat.zero_le _
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hpoint x)
  rw [Finset.sum_comm] at hs
  simpa [S, Finset.sum_ite, mul_comm] using hs

end ProximityGap.SixErrorRankSupportMultiplicity

#print axioms ProximityGap.SixErrorRankSupportMultiplicity.rank_coordinate_multiplicity
#print axioms ProximityGap.SixErrorRankSupportMultiplicity.rank_support_mass
