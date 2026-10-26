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

/-- A rank-`r` family of `r + 1` vectors whose every deletion is independent has a dependence
with every coefficient nonzero. This is the circuit relation needed to pass from rank information
to full-support error relations. -/
theorem full_support_relation_of_rank
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {r : ℕ} (e : Fin (r + 1) → V)
    (hLI : ∀ i : Fin (r + 1),
      LinearIndependent F (fun j : Fin r => e (i.succAbove j)))
    (hrank : Module.finrank F (Submodule.span F (Set.range e)) ≤ r) :
    ∃ c : Fin (r + 1) → F,
      (∑ i, c i • e i = 0) ∧ ∀ i, c i ≠ 0 := by
  classical
  have hnot : ¬ LinearIndependent F e := by
    intro hlin
    have hspan := hrank
    rw [finrank_span_eq_card hlin] at hspan
    simp only [Fintype.card_fin] at hspan
    omega
  obtain ⟨c, hsum, hc⟩ := Fintype.not_linearIndependent_iff.mp hnot
  refine ⟨c, hsum, ?_⟩
  intro i
  by_contra hci_ne
  have hci : c i = 0 := by simpa using hci_ne
  let b : Fin r → Fin (r + 1) := i.succAbove
  have hb : Function.Injective b := Fin.succAbove_right_injective
  have hImage : Finset.univ.image b = Finset.univ.erase i := by
    apply Finset.eq_of_subset_of_card_le
    · intro j hj
      rcases Finset.mem_image.mp hj with ⟨k, _hk, rfl⟩
      exact Finset.mem_erase.mpr ⟨Fin.succAbove_ne i k, Finset.mem_univ _⟩
    · rw [Finset.card_image_of_injective _ hb]
      simp
  have hsumErase :
      (∑ j ∈ Finset.univ.erase i, c j • e j) = 0 := by
    have hsplit := Finset.sum_erase_add Finset.univ (fun j => c j • e j)
      (Finset.mem_univ i)
    rw [hsum] at hsplit
    simpa [hci] using hsplit
  have hsumImage :
      (∑ j ∈ Finset.univ.image b, c j • e j) =
        ∑ j : Fin r, c (b j) • e (b j) := by
    rw [Finset.sum_image (fun j _ k _ hjk => hb hjk)]
  have hsumB : (∑ j : Fin r, c (b j) • e (b j)) = 0 := by
    rw [← hsumImage, hImage]
    exact hsumErase
  have hcoeff : ∀ j : Fin r, c (b j) = 0 := by
    have hz := Fintype.linearIndependent_iff.mp (hLI i) (fun j => c (b j)) hsumB
    intro j
    simpa using hz j
  have hcAll : ∀ j : Fin (r + 1), c j = 0 := by
    intro j
    by_cases hji : j = i
    · simpa [hji] using hci
    · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hji
      rw [← hk]
      exact hcoeff k
  rcases hc with ⟨j, hj⟩
  exact hj (hcAll j)

/-- If every member of a finite vector family participates in some linear dependence, and the
field has more elements than the family has members, then one dependence has full support.
This is the finite-field hyperplane-avoidance step that converts coordinatewise activity into a
single relation usable by affine-head collapse arguments. -/
theorem full_support_relation_of_active_coordinates
    {F V I : Type*} [Field F] [Fintype F] [Fintype I]
    [AddCommGroup V] [Module F V]
    (e : I → V) (hcard : Fintype.card I < Fintype.card F)
    (hactive : ∀ i, ∃ c : I → F, (∑ j, c j • e j = 0) ∧ c i ≠ 0) :
    ∃ c : I → F, (∑ j, c j • e j = 0) ∧ ∀ i, c i ≠ 0 := by
  classical
  have hstep : ∀ s : Finset I, ∃ c : I → F,
      (∑ j, c j • e j = 0) ∧ ∀ i ∈ s, c i ≠ 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        exact ⟨0, by simp, by simp⟩
    | @insert i s hi ih =>
        obtain ⟨v, hv, hvS⟩ := ih
        obtain ⟨w, hw, hwi⟩ := hactive i
        let bad := (insert i s).image (fun j =>
          if w j = 0 then 0 else -v j / w j)
        have hbad : bad.card < Fintype.card F := by
          calc
            bad.card ≤ (insert i s).card := Finset.card_image_le
            _ ≤ Fintype.card I := Finset.card_le_univ _
            _ < Fintype.card F := hcard
        have hbadCompl : 0 < badᶜ.card := by
          rw [Finset.card_compl]
          omega
        obtain ⟨a, ha⟩ := Finset.card_pos.mp hbadCompl
        have haBad : a ∉ bad := by simpa using ha
        have hnew : ∀ j ∈ insert i s, v j + a * w j ≠ 0 := by
          intro j hj hzero
          have hvj : v j ≠ 0 ∨ j = i := by
            rcases Finset.mem_insert.mp hj with hji | hjs
            · exact Or.inr hji
            · exact Or.inl (hvS j hjs)
          by_cases hwj : w j = 0
          · rcases hvj with hvj | hji
            · exact hvj (by simpa [hwj] using hzero)
            · subst j
              exact hwi hwj
          · have haEq : a = -v j / w j := by
              have hmul : a * w j = -v j := by linear_combination hzero
              calc
                a = (a * w j) / w j := by field_simp [hwj]
                _ = -v j / w j := by rw [hmul]
            apply haBad
            apply Finset.mem_image.mpr
            exact ⟨j, hj, by simp [hwj, haEq]⟩
        have hrel : (∑ j, (v j + a * w j) • e j) = 0 := by
          have hmul : (∑ j, (a * w j) • e j) = a • (∑ j, w j • e j) := by
            calc
              (∑ j, (a * w j) • e j) = ∑ j, a • (w j • e j) := by
                apply Finset.sum_congr rfl
                intro j hj
                rw [mul_smul]
              _ = a • (∑ j, w j • e j) := by rw [Finset.smul_sum]
          calc
            (∑ j, (v j + a * w j) • e j) =
                (∑ j, v j • e j) + a • (∑ j, w j • e j) := by
                  rw [Finset.sum_add_distrib, add_smul, hmul]
            _ = 0 := by rw [hv, hw]; simp
        refine ⟨fun j => v j + a * w j, hrel, ?_⟩
        intro j hj
        exact hnew j hj
  obtain ⟨c, hc, hall⟩ := hstep Finset.univ
  exact ⟨c, hc, fun i => hall i (Finset.mem_univ i)⟩

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
#print axioms ProximityGap.SixErrorRankSupportMultiplicity.full_support_relation_of_rank
#print axioms ProximityGap.SixErrorRankSupportMultiplicity.full_support_relation_of_active_coordinates
