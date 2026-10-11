/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Research.ProximityPrize.Frontier.PackingFloorTwoPowLower

/-!
# Sponsor no-go for the agreement-set packing bridge

The multiplicity-aware packing route supplies the distinct-scalar cap

`C(n, k + 1) / C(a, k + 1)`

under its general-position hypothesis.  At the rate-half predecessor used by the
production `31/64` gate, the unconditional falling-factorial lower bound from
`PackingFloorTwoPowLower` already puts this cap strictly above the sponsor budget
`n`.  Thus this route cannot discharge the production `WorstCaseIncidenceBounded`
obligation, even before its general-position hypothesis is checked.

This is a numerical obstruction to that bridge only.  It does not refute the
production conjecture or the separate BCHKS incidence statement.
-/

namespace ArkLib.ProximityGap.Frontier.BchksPackingSponsorNoGo

open ProximityGap.Ownership

def sponsorN : ℕ := 2 ^ 30

def sponsorK : ℕ := 2 ^ 29 - 1

def sponsorA : ℕ := 31 * 2 ^ 24

theorem sponsor_band_half : 2 * sponsorA ≤ sponsorN := by
  norm_num [sponsorN, sponsorA]

theorem sponsor_tuple_fits : sponsorK + 1 ≤ sponsorA := by
  norm_num [sponsorK, sponsorA]

theorem sponsor_packing_floor_gt_budget :
    sponsorN < packingDeflationFloor sponsorN sponsorK sponsorA := by
  have hfloor : 2 ^ (sponsorK + 1) ≤
      packingDeflationFloor sponsorN sponsorK sponsorA :=
    packingFloor_ge_two_pow sponsor_band_half sponsor_tuple_fits
  have hpow : sponsorN < 2 ^ (sponsorK + 1) := by
    apply Nat.pow_lt_pow_right (by norm_num : 1 < (2 : ℕ))
    norm_num [sponsorN, sponsorK]
  exact lt_of_lt_of_le hpow hfloor

theorem sponsor_packing_cannot_prove_budget :
    ¬ packingDeflationFloor sponsorN sponsorK sponsorA ≤ sponsorN := by
  exact Nat.not_le.mpr sponsor_packing_floor_gt_budget

end ArkLib.ProximityGap.Frontier.BchksPackingSponsorNoGo

#print axioms ArkLib.ProximityGap.Frontier.BchksPackingSponsorNoGo.sponsor_packing_floor_gt_budget
#print axioms ArkLib.ProximityGap.Frontier.BchksPackingSponsorNoGo.sponsor_packing_cannot_prove_budget
