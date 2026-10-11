/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Research.ProximityPrize.Frontier.PackingFloorTwoPowLower

/-!
# Sponsor parameter mismatch for the agreement-set packing bridge

The multiplicity-aware packing route supplies the distinct-scalar cap

`C(n, k + 1) / C(a, k + 1)`

only when the band contains a `(k+1)`-tuple, which is the positive-denominator
hypothesis `k + 1 ≤ a`.  At the exact rate-half predecessor used by the production
`31/64` gate, `A = 31 · 2^24` is strictly smaller than `k + 1 = 2^29`.  Therefore
the deployed floor has denominator zero and evaluates to `0` in `Nat` division.
The packing theorem is unavailable at these sponsor parameters, so it cannot
discharge `WorstCaseIncidenceBounded` through this interface.

This is an exact parameter mismatch for that bridge only.  It does not refute the
production conjecture or the separate BCHKS incidence statement.
-/

namespace ArkLib.ProximityGap.Frontier.BchksPackingSponsorNoGo

open ProximityGap.Ownership

def sponsorN : ℕ := 2 ^ 30

def sponsorK : ℕ := 2 ^ 29 - 1

def sponsorA : ℕ := 31 * 2 ^ 24

theorem sponsor_band_half : 2 * sponsorA ≤ sponsorN := by
  norm_num [sponsorN, sponsorA]

theorem sponsor_tuple_does_not_fit : ¬ sponsorK + 1 ≤ sponsorA := by
  norm_num [sponsorK, sponsorA]

theorem sponsor_packing_denominator_zero :
    sponsorA.choose (sponsorK + 1) = 0 := by
  apply Nat.choose_eq_zero_of_lt
  norm_num [sponsorK, sponsorA]

theorem sponsor_packing_floor_degenerates :
    packingDeflationFloor sponsorN sponsorK sponsorA = 0 := by
  unfold packingDeflationFloor
  rw [sponsor_packing_denominator_zero]
  simp

theorem sponsor_packing_bridge_hypothesis_fails :
    ¬ sponsorK + 1 ≤ sponsorA := by
  exact sponsor_tuple_does_not_fit

end ArkLib.ProximityGap.Frontier.BchksPackingSponsorNoGo

#print axioms ArkLib.ProximityGap.Frontier.BchksPackingSponsorNoGo.sponsor_packing_floor_degenerates
#print axioms ArkLib.ProximityGap.Frontier.BchksPackingSponsorNoGo.sponsor_packing_bridge_hypothesis_fails
