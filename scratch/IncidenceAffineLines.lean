/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikhail Izhutkin (mashingaan, @mashingaan)
-/
import Mathlib

set_option autoImplicit false
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

end ProximityGap.IncidenceAffineLines
#print axioms ProximityGap.IncidenceAffineLines.params_eq_of_two
#print axioms ProximityGap.IncidenceAffineLines.distinct_lines_intersect_at_most_one
#print axioms ProximityGap.IncidenceAffineLines.collinear_triple_forces_onLine
