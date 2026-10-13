/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikhail Izhutkin (mashingaan, @mashingaan)
-/
import Research.ProximityPrize.Frontier._SYZ3OverBudgetStackWitness

set_option autoImplicit false
set_option maxRecDepth 4096

namespace ProximityGap.IncidenceFullScaleCores

open Finset Polynomial ProximityGap.Ownership
open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.KKH26

private instance : Fact P.Prime := ⟨prime_P⟩
private instance : NeZero (2 ^ 30 : ℕ) := ⟨by norm_num⟩

abbrev n : ℕ := 1073741824
abbrev k : ℕ := 536870912
abbrev commonSize : ℕ := 536870910
abbrev groupSize : ℕ := 178956971
abbrev Coord := Fin n

/-- Coordinate embedding of the common root set. -/
def commonEmb : Fin commonSize ↪ Coord where
  toFun a := ⟨a.val, by have ha := a.isLt
                       omega⟩
  inj' := by
    intro a b h
    apply Fin.ext
    exact congrArg Fin.val h

/-- Three disjoint coordinate groups, leaving one unused coordinate. -/
def groupEmb (j : Fin 3) : Fin groupSize ↪ Coord where
  toFun a := ⟨commonSize + j.val * groupSize + a.val, by
    have ha := a.isLt
    have hj := j.isLt
    omega⟩
  inj' := by
    intro a b h
    apply Fin.ext
    have hh := congrArg Fin.val h
    dsimp at hh
    omega

def common : Finset Coord := Finset.univ.map commonEmb
def group (j : Fin 3) : Finset Coord := Finset.univ.map (groupEmb j)
def core (j : Fin 3) : Finset Coord := common ∪ group j

theorem mem_common (i : Coord) : i ∈ common ↔ i.val < commonSize := by
  constructor
  · intro hi
    obtain ⟨a,_,ha⟩ := Finset.mem_map.mp hi
    have he := congrArg Fin.val ha
    have hb := a.isLt
    dsimp [commonEmb] at he
    omega
  · intro hi
    exact Finset.mem_map.mpr ⟨⟨i.val,hi⟩,Finset.mem_univ _,Fin.ext rfl⟩

theorem mem_group (j : Fin 3) (i : Coord) : i ∈ group j ↔
    commonSize + j.val * groupSize ≤ i.val ∧
      i.val < commonSize + (j.val + 1) * groupSize := by
  constructor
  · intro hi
    obtain ⟨a,_,ha⟩ := Finset.mem_map.mp hi
    have he := congrArg Fin.val ha
    have hb := a.isLt
    dsimp [groupEmb] at he
    omega
  · rintro ⟨hlo,hhi⟩
    refine Finset.mem_map.mpr ⟨⟨i.val - (commonSize + j.val * groupSize),by omega⟩,
      Finset.mem_univ _,?_⟩
    apply Fin.ext
    dsimp [groupEmb]
    omega

theorem core_card (j : Fin 3) : (core j).card = 715827881 := by
  have hd : Disjoint common (group j) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hc := (mem_common i).mp hi
    have hg := (mem_group j i).mp hj
    omega
  rw [core,Finset.card_union_of_disjoint hd]
  simp only [common,group,Finset.card_map,Finset.card_univ,Fintype.card_fin]
  norm_num

/-- Heights of the three groups and the one unused coordinate. -/
def height (i : Coord) : ℕ :=
  if i.val < commonSize then 3 else
    if i.val < commonSize + 3 * groupSize then (i.val - commonSize) / groupSize else 3

theorem height_le (i : Coord) : height i ≤ 3 := by
  unfold height
  split_ifs
  all_goals omega

theorem height_eq_iff (j : Fin 3) (i : Coord) : height i = j.val ↔ i ∈ group j := by
  rw [mem_group]
  have hj := j.isLt
  unfold height
  split_ifs
  all_goals omega

/-- Locator of the common coordinates, without enumerating the production domain. -/
noncomputable def locator : Polynomial (ZMod P) :=
  ∏ a : Fin commonSize, (Polynomial.X - Polynomial.C (g ^ a.val))

noncomputable def z (i : Coord) : ZMod P := locator.eval (g ^ i.val)

theorem locator_natDegree_le : locator.natDegree ≤ commonSize := by
  unfold locator
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc
    _ ≤ ∑ _a : Fin commonSize, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro a _
      exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
    _ = commonSize := by simp

theorem z_eq_zero_iff (i : Coord) : z i = 0 ↔ i ∈ common := by
  rw [z,locator,Polynomial.eval_prod,Finset.prod_eq_zero_iff]
  simp only [Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,sub_eq_zero]
  constructor
  · rintro ⟨a,_,ha⟩
    have he : i = commonEmb a :=
      (smoothDom g n orderOf_g).injective ha
    rw [he,mem_common]
    exact a.isLt
  · intro hi
    have hc := (mem_common i).mp hi
    exact ⟨⟨i.val,hc⟩,Finset.mem_univ _,rfl⟩

noncomputable def prodCode : Submodule (ZMod P) (Coord → ZMod P) :=
  rsCode (smoothDom g n orderOf_g) k

noncomputable def xz (i : Coord) : ZMod P := z i * g ^ i.val
noncomputable def u1 (i : Coord) : ZMod P := (height i : ZMod P) * z i
noncomputable def u0 (i : Coord) : ZMod P := (height i : ZMod P) ^ 2 * xz i
noncomputable def v1 (j : Fin 3) : Coord → ZMod P := (j.val : ZMod P) • z
noncomputable def v0 (j : Fin 3) : Coord → ZMod P := (j.val : ZMod P) ^ 2 • xz

theorem z_mem : z ∈ prodCode := by
  refine ⟨locator,?_,rfl⟩
  exact lt_of_le_of_lt Polynomial.degree_le_natDegree
    (by exact_mod_cast (locator_natDegree_le.trans_lt (by norm_num : commonSize < k)))

theorem xz_mem : xz ∈ prodCode := by
  refine ⟨locator * Polynomial.X,?_,?_⟩
  · apply lt_of_le_of_lt (Polynomial.degree_mul_le _ _)
    have hz : locator.degree ≤ (commonSize : ℕ) :=
      Polynomial.degree_le_natDegree.trans (by exact_mod_cast locator_natDegree_le)
    have hx : (Polynomial.X : Polynomial (ZMod P)).degree ≤ (1 : ℕ) :=
      Polynomial.degree_X_le
    exact (add_le_add hz hx).trans_lt (by norm_num)
  · funext i
    simp only [Polynomial.eval_mul,Polynomial.eval_X]
    rfl

theorem v1_mem (j : Fin 3) : v1 j ∈ prodCode := prodCode.smul_mem _ z_mem
theorem v0_mem (j : Fin 3) : v0 j ∈ prodCode := prodCode.smul_mem _ xz_mem

theorem agree_v1 (j : Fin 3) : ∀ i ∈ core j, v1 j i = u1 i := by
  intro i hi
  rcases Finset.mem_union.mp hi with hc | hg
  · have hz := (z_eq_zero_iff i).mpr hc
    simp [v1,u1,hz]
  · have hh := (height_eq_iff j i).mpr hg
    simp [v1,u1,hh]

theorem agree_v0 (j : Fin 3) : ∀ i ∈ core j, v0 j i = u0 i := by
  intro i hi
  rcases Finset.mem_union.mp hi with hc | hg
  · have hz := (z_eq_zero_iff i).mpr hc
    simp [v0,u0,xz,hz]
  · have hh := (height_eq_iff j i).mpr hg
    simp [v0,u0,hh]

end ProximityGap.IncidenceFullScaleCores

#print axioms ProximityGap.IncidenceFullScaleCores.core_card
#print axioms ProximityGap.IncidenceFullScaleCores.z_eq_zero_iff
#print axioms ProximityGap.IncidenceFullScaleCores.z_mem
#print axioms ProximityGap.IncidenceFullScaleCores.xz_mem
#print axioms ProximityGap.IncidenceFullScaleCores.agree_v1
#print axioms ProximityGap.IncidenceFullScaleCores.agree_v0
