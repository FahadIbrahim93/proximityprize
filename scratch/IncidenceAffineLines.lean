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

end ProximityGap.IncidenceAffineLines
#print axioms ProximityGap.IncidenceAffineLines.params_eq_of_two
#print axioms ProximityGap.IncidenceAffineLines.distinct_lines_intersect_at_most_one
#print axioms ProximityGap.IncidenceAffineLines.collinear_triple_forces_onLine

#print axioms ProximityGap.IncidenceAffineLines.mixed_completion_unique
#print axioms ProximityGap.IncidenceAffineLines.mixed_triples_card_le_sq
