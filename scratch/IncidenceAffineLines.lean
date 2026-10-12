/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikhail Izhutkin (mashingaan, @mashingaan)
-/
import Mathlib

set_option autoImplicit false
attribute [local instance] Classical.propDecidable
namespace ProximityGap.IncidenceAffineLines
variable {F V I : Type} [Field F] [AddCommGroup V] [Module F V]

def OnLine (gamma : I → F) (w : I → V) (U D : V) (i : I) : Prop :=
  w i = U + gamma i • D

def CollinearTriple (gamma : I → F) (w : I → V) (i j k : I) : Prop :=
  ∃ U D : V, OnLine gamma w U D i ∧ OnLine gamma w U D j ∧ OnLine gamma w U D k

theorem params_eq_of_two {a b : F} (hab : a ≠ b) {U D U' D' : V}
    (ha : U + a • D = U' + a • D')
    (hb : U + b • D = U' + b • D') : U = U' ∧ D = D' := by
  have hz : (a - b) • (D - D') = 0 := by
    calc
      _ = (U + a • D - (U' + a • D')) -
          (U + b • D - (U' + b • D')) := by module
      _ = 0 := by
        rw [ha, hb]
        abel
  have hD : D = D' := by
    rcases smul_eq_zero.mp hz with h | h
    · exact False.elim ((sub_ne_zero.mpr hab) h)
    · exact sub_eq_zero.mp h
  rw [hD] at ha
  exact ⟨add_right_cancel ha, hD⟩

theorem distinct_lines_intersect_at_most_one
    (gamma : I → F) (w : I → V) (hinj : Function.Injective gamma)
    {U D U' D' : V} (hne : (U,D) ≠ (U',D')) {a b : I}
    (ha : OnLine gamma w U D a) (ha' : OnLine gamma w U' D' a)
    (hb : OnLine gamma w U D b) (hb' : OnLine gamma w U' D' b) : a = b := by
  by_contra hab
  have hgamma : gamma a ≠ gamma b := fun h => hab (hinj h)
  obtain ⟨hU,hD⟩ := params_eq_of_two hgamma (ha.symm.trans ha') (hb.symm.trans hb')
  exact hne (Prod.ext hU hD)

theorem collinear_triple_forces_onLine
    (gamma : I → F) (w : I → V) (hinj : Function.Injective gamma)
    {U D : V} {a b c : I} (hab : a ≠ b)
    (ha : OnLine gamma w U D a) (hb : OnLine gamma w U D b)
    (hcol : CollinearTriple gamma w a b c) : OnLine gamma w U D c := by
  obtain ⟨U',D',ha',hb',hc'⟩ := hcol
  have hgamma : gamma a ≠ gamma b := fun h => hab (hinj h)
  obtain ⟨hU,hD⟩ := params_eq_of_two hgamma (ha.symm.trans ha') (hb.symm.trans hb')
  simpa only [hU,hD] using hc'

theorem mixed_completion_unique
    (gamma : I → F) (w : I → V) (hinj : Function.Injective gamma)
    {U D : V} {a a' b c : I} (hbc : b ≠ c)
    (hbnot : ¬ OnLine gamma w U D b)
    (ha : OnLine gamma w U D a) (ha' : OnLine gamma w U D a')
    (hcol : CollinearTriple gamma w a b c)
    (hcol' : CollinearTriple gamma w a' b c) : a = a' := by
  obtain ⟨U1,D1,ha1,hb1,hc1⟩ := hcol
  obtain ⟨U2,D2,ha2,hb2,hc2⟩ := hcol'
  have ha'1 : OnLine gamma w U1 D1 a' :=
    collinear_triple_forces_onLine gamma w hinj hbc hb1 hc1
      ⟨U2,D2,hb2,hc2,ha2⟩
  by_contra haa'
  have hgamma : gamma a ≠ gamma a' := fun h => haa' (hinj h)
  obtain ⟨hU,hD⟩ := params_eq_of_two hgamma
    (ha.symm.trans ha1) (ha'.symm.trans ha'1)
  apply hbnot
  simpa only [hU,hD] using hb1

theorem mixed_triples_card_le_sq
    [DecidableEq I]
    (gamma : I → F) (w : I → V) (hinj : Function.Injective gamma)
    (B R : Finset I) (U D : V)
    (hB : ∀ a ∈ B, OnLine gamma w U D a)
    (hR : ∀ b ∈ R, ¬ OnLine gamma w U D b) :
    ((B.product (R.product R)).filter (fun z =>
      z.2.1 ≠ z.2.2 ∧ CollinearTriple gamma w z.1 z.2.1 z.2.2)).card ≤ R.card ^ 2 := by
  classical
  let M := (B.product (R.product R)).filter (fun z =>
      z.2.1 ≠ z.2.2 ∧ CollinearTriple gamma w z.1 z.2.1 z.2.2)
  change M.card ≤ R.card ^ 2
  calc
    M.card ≤ (R.product R).card := by
      apply Finset.card_le_card_of_injOn (fun z : I × (I × I) => z.2)
      · intro z hz
        exact (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).2
      · intro x hx y hy hxy
        obtain ⟨hxprod,hxc⟩ := Finset.mem_filter.mp hx
        obtain ⟨hyprod,hyc⟩ := Finset.mem_filter.mp hy
        have hxB := (Finset.mem_product.mp hxprod).1
        have hyB := (Finset.mem_product.mp hyprod).1
        have hxR := (Finset.mem_product.mp
          (Finset.mem_product.mp hxprod).2).1
        change x.2 = y.2 at hxy
        have hycol := hyc.2
        rw [← hxy] at hycol
        have haeq := mixed_completion_unique gamma w hinj hxc.1
          (hR _ hxR) (hB _ hxB) (hB _ hyB) hxc.2 hycol
        exact Prod.ext haeq hxy
    _ = R.card ^ 2 := by
      rw [Finset.product_eq_sprod, Finset.card_product, pow_two]

theorem params_mem_code_of_two
    (gamma : I → F) (w : I → V) (hinj : Function.Injective gamma)
    (C : Submodule F V) {U D : V} {a b : I} (hab : a ≠ b)
    (ha : OnLine gamma w U D a) (hb : OnLine gamma w U D b)
    (hwa : w a ∈ C) (hwb : w b ∈ C) : U ∈ C ∧ D ∈ C := by
  have hgamma : gamma a - gamma b ≠ 0 :=
    sub_ne_zero.mpr (fun h => hab (hinj h))
  have hdiff : w a - w b = (gamma a - gamma b) • D := by
    rw [ha,hb,sub_smul]
    abel
  have hD : D = (gamma a - gamma b)⁻¹ • (w a - w b) := by
    rw [hdiff,smul_smul,inv_mul_cancel₀ hgamma,one_smul]
  have hDC : D ∈ C := by
    rw [hD]
    exact C.smul_mem _ (C.sub_mem hwa hwb)
  have hU : U = w a - gamma a • D := by
    rw [ha]
    abel
  refine ⟨?_,hDC⟩
  rw [hU]
  exact C.sub_mem hwa (C.smul_mem _ hDC)

theorem triple_line_partition
    (gamma : I → F) (w : I → V) (hinj : Function.Injective gamma)
    (U D : V) {a b c : I} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcol : CollinearTriple gamma w a b c) :
    (OnLine gamma w U D a ∧ OnLine gamma w U D b ∧ OnLine gamma w U D c) ∨
    (¬ OnLine gamma w U D a ∧ ¬ OnLine gamma w U D b ∧ ¬ OnLine gamma w U D c) ∨
    (OnLine gamma w U D a ∧ ¬ OnLine gamma w U D b ∧ ¬ OnLine gamma w U D c) ∨
    (¬ OnLine gamma w U D a ∧ OnLine gamma w U D b ∧ ¬ OnLine gamma w U D c) ∨
    (¬ OnLine gamma w U D a ∧ ¬ OnLine gamma w U D b ∧ OnLine gamma w U D c) := by
  have hAB : OnLine gamma w U D a → OnLine gamma w U D b → OnLine gamma w U D c :=
    fun ha hb => collinear_triple_forces_onLine gamma w hinj hab ha hb hcol
  obtain ⟨U',D',ha',hb',hc'⟩ := hcol
  have hAC : OnLine gamma w U D a → OnLine gamma w U D c → OnLine gamma w U D b :=
    fun ha hc => collinear_triple_forces_onLine gamma w hinj hac ha hc ⟨U',D',ha',hc',hb'⟩
  have hBC : OnLine gamma w U D b → OnLine gamma w U D c → OnLine gamma w U D a :=
    fun hb hc => collinear_triple_forces_onLine gamma w hinj hbc hb hc ⟨U',D',hb',hc',ha'⟩
  by_cases ha : OnLine gamma w U D a
  all_goals by_cases hb : OnLine gamma w U D b
  all_goals by_cases hc : OnLine gamma w U D c
  all_goals aesop

theorem block_step_arithmetic (r ell s : ℕ) (hs : s ≤ ell) :
    3 * s * r ^ 2 + 3 * r ^ 3 + s ^ 2 * r ^ 2 ≤
      3 * (r + ell) ^ 3 + s ^ 2 * (r + ell) ^ 2 := by
  have hcube : r ^ 3 + s * r ^ 2 ≤ (r + ell) ^ 3 := by
    have hmul := Nat.mul_le_mul_right (r ^ 2) hs
    nlinarith [Nat.zero_le (ell ^ 3), Nat.zero_le (ell * r ^ 2),
      Nat.zero_le (ell ^ 2 * r)]
  have hsquare : r ^ 2 ≤ (r + ell) ^ 2 := by
    nlinarith [Nat.zero_le (ell ^ 2), Nat.zero_le (r * ell)]
  have hc3 := Nat.mul_le_mul_left 3 hcube
  have hs2 := Nat.mul_le_mul_left (s ^ 2) hsquare
  nlinarith

noncomputable def collinearTriples [DecidableEq I] (gamma : I -> F) (w : I -> V) (S : Finset I) : Finset (I × (I × I)) :=
  (S.product (S.product S)).filter (fun z =>
    z.1 ≠ z.2.1 ∧ z.1 ≠ z.2.2 ∧ z.2.1 ≠ z.2.2 ∧
      CollinearTriple gamma w z.1 z.2.1 z.2.2)

noncomputable def mixedTriples [DecidableEq I] (gamma : I -> F) (w : I -> V) (B R : Finset I) : Finset (I × (I × I)) :=
  (B.product (R.product R)).filter (fun z =>
    z.2.1 ≠ z.2.2 ∧ CollinearTriple gamma w z.1 z.2.1 z.2.2)

def swapAB (z : I × (I × I)) : I × (I × I) := (z.2.1,z.1,z.2.2)
def swapAC (z : I × (I × I)) : I × (I × I) := (z.2.2,z.2.1,z.1)

theorem collinearTriples_card_le_cube [DecidableEq I]
    (gamma : I -> F) (w : I -> V) (S : Finset I) :
    (collinearTriples gamma w S).card ≤ S.card ^ 3 := by
  calc
    _ ≤ (S.product (S.product S)).card := Finset.card_filter_le _ _
    _ = _ := by
      simp only [Finset.product_eq_sprod, Finset.card_product]
      ring

theorem collinearTriples_block_step [DecidableEq I]
    (gamma : I -> F) (w : I -> V) (hinj : Function.Injective gamma)
    (S : Finset I) (U D : V) :
    let B := S.filter (OnLine gamma w U D)
    let R := S \ B
    (collinearTriples gamma w S).card ≤
      B.card ^ 3 + 3 * R.card ^ 2 + (collinearTriples gamma w R).card := by
  classical
  let B := S.filter (OnLine gamma w U D)
  let R := S \ B
  let M := mixedTriples gamma w B R
  change (collinearTriples gamma w S).card ≤
      B.card ^ 3 + 3 * R.card ^ 2 + (collinearTriples gamma w R).card
  have hmemB : ∀ a ∈ S, OnLine gamma w U D a ↔ a ∈ B := by
    intro a ha
    simp [B,ha]
  have hmemR : ∀ a ∈ S, ¬ OnLine gamma w U D a ↔ a ∈ R := by
    intro a ha
    simp [R,B,ha]
  have hB : ∀ a ∈ B, OnLine gamma w U D a := by
    intro a ha
    exact (Finset.mem_filter.mp ha).2
  have hR : ∀ a ∈ R, ¬ OnLine gamma w U D a := by
    intro a ha hline
    obtain ⟨haS,haB⟩ := Finset.mem_sdiff.mp ha
    exact haB (Finset.mem_filter.mpr ⟨haS,hline⟩)
  have hcover : collinearTriples gamma w S ⊆
      collinearTriples gamma w B ∪ (collinearTriples gamma w R ∪
        (M ∪ (M.image swapAB ∪ M.image swapAC))) := by
    rintro ⟨a,b,c⟩ hz
    obtain ⟨hp,hab,hac,hbc,hcol⟩ := Finset.mem_filter.mp hz
    have haS := (Finset.mem_product.mp hp).1
    have hbS := (Finset.mem_product.mp (Finset.mem_product.mp hp).2).1
    have hcS := (Finset.mem_product.mp (Finset.mem_product.mp hp).2).2
    simp only [Finset.mem_union]
    rcases triple_line_partition gamma w hinj U D hab hac hbc hcol with
      ⟨ha,hb,hc⟩ | ⟨ha,hb,hc⟩ | ⟨ha,hb,hc⟩ | ⟨ha,hb,hc⟩ | ⟨ha,hb,hc⟩
    · left
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨(hmemB a haS).mp ha,Finset.mem_product.mpr
          ⟨(hmemB b hbS).mp hb,(hmemB c hcS).mp hc⟩⟩,hab,hac,hbc,hcol⟩
    · right
      left
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨(hmemR a haS).mp ha,Finset.mem_product.mpr
          ⟨(hmemR b hbS).mp hb,(hmemR c hcS).mp hc⟩⟩,hab,hac,hbc,hcol⟩
    · right
      right
      left
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨(hmemB a haS).mp ha,Finset.mem_product.mpr
          ⟨(hmemR b hbS).mp hb,(hmemR c hcS).mp hc⟩⟩,hbc,hcol⟩
    · right
      right
      right
      left
      apply Finset.mem_image.mpr
      refine ⟨(b,a,c),?_,rfl⟩
      obtain ⟨U',D',h1,h2,h3⟩ := hcol
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨(hmemB b hbS).mp hb,Finset.mem_product.mpr
          ⟨(hmemR a haS).mp ha,(hmemR c hcS).mp hc⟩⟩,hac,⟨U',D',h2,h1,h3⟩⟩
    · right
      right
      right
      right
      apply Finset.mem_image.mpr
      refine ⟨(c,b,a),?_,rfl⟩
      obtain ⟨U',D',h1,h2,h3⟩ := hcol
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨(hmemB c hcS).mp hc,Finset.mem_product.mpr
          ⟨(hmemR b hbS).mp hb,(hmemR a haS).mp ha⟩⟩,hab.symm,⟨U',D',h3,h2,h1⟩⟩
  have h0 := Finset.card_le_card hcover
  have h1 := Finset.card_union_le (collinearTriples gamma w B)
    (collinearTriples gamma w R ∪ (M ∪ (M.image swapAB ∪ M.image swapAC)))
  have h2 := Finset.card_union_le (collinearTriples gamma w R)
    (M ∪ (M.image swapAB ∪ M.image swapAC))
  have h3 := Finset.card_union_le M (M.image swapAB ∪ M.image swapAC)
  have h4 := Finset.card_union_le (M.image swapAB) (M.image swapAC)
  have hi1 : (M.image swapAB).card ≤ M.card := Finset.card_image_le
  have hi2 : (M.image swapAC).card ≤ M.card := Finset.card_image_le
  have hm : M.card ≤ R.card ^ 2 := mixed_triples_card_le_sq gamma w hinj B R U D hB hR
  have hb := collinearTriples_card_le_cube gamma w B
  omega

end ProximityGap.IncidenceAffineLines
#print axioms ProximityGap.IncidenceAffineLines.params_eq_of_two
#print axioms ProximityGap.IncidenceAffineLines.distinct_lines_intersect_at_most_one
#print axioms ProximityGap.IncidenceAffineLines.collinear_triple_forces_onLine

#print axioms ProximityGap.IncidenceAffineLines.mixed_completion_unique
#print axioms ProximityGap.IncidenceAffineLines.mixed_triples_card_le_sq

#print axioms ProximityGap.IncidenceAffineLines.params_mem_code_of_two

#print axioms ProximityGap.IncidenceAffineLines.triple_line_partition

#print axioms ProximityGap.IncidenceAffineLines.block_step_arithmetic

#print axioms ProximityGap.IncidenceAffineLines.collinearTriples_card_le_cube

#print axioms ProximityGap.IncidenceAffineLines.collinearTriples_block_step
