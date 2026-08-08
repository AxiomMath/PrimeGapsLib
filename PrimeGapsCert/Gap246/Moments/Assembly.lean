/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Moments.Checks
public import PrimeGapsCert.Gap246.Moments.CoeffCheck
public import PrimeGapsCert.Gap246.Moments.LevelConcreteSound

import Mathlib.Tactic.IntervalCases

/-! # Assembly of the complete packed moment certificate -/

@[expose] public section

namespace PrimeGaps.Gap246

/-- Every row of the checked nilpotent base table is sound. -/
theorem certBase : ∀ t < 272, ∀ s ≤ t,
    cert246Data.nilLevelAt cert246Data.nilLevelShifts cert246Data.nilLevelPmasks
        cert246Data.nilLevelWidths cert246Data.nilLevelMasks cert246Data.nilLevelTrees
        0 (cert246Data.triIdx s t) =
      if cert246Data.sigField cert246Data.sigEnc s = 0 ∧
          cert246Data.sigField cert246Data.sigEnc t = 0 then 1 else 0 := by
  gather_cert246_level_base

/-- Every checked identity-free transition level is sound. -/
theorem certSteps : ConcreteLevelSteps := by
  intro level hpositive hbound
  interval_cases level <;> gather_cert246_level_step

/-- Every checked final row carries the reconstruction read off the coefficient table. -/
theorem certResultAndBoundRaw : ∀ t < 272, ∀ s ≤ t,
      cert246Data.treeAt 7 127 512 (2 ^ 512 - 1) cert246Data.pairT
        (cert246Data.triIdx s t) =
      (cert246Data.nilMomentPairPredLevels 256 cert246Data.coeffT 24 cert246Data.sigEnc
        cert246Data.nilLevelShifts cert246Data.nilLevelPmasks
        cert246Data.nilLevelWidths cert246Data.nilLevelMasks
        cert246Data.nilLevelTrees s t).1 ∧
    (cert246Data.nilMomentPairPredLevels 256 cert246Data.coeffT 24 cert246Data.sigEnc
      cert246Data.nilLevelShifts cert246Data.nilLevelPmasks
      cert246Data.nilLevelWidths cert246Data.nilLevelMasks
      cert246Data.nilLevelTrees s t).2 < 2 ^ 256 := by
  gather_cert246_level_result_bound

/-- Every checked final row has both the reconstructed pair and predecessor bound. -/
theorem certResultAndBound : ∀ t < 272, ∀ s ≤ t,
      cert246Data.treeAt 7 127 512 (2 ^ 512 - 1) cert246Data.pairT
        (cert246Data.triIdx s t) =
      cert246Data.nilMomentPairLevels 256 50 24 cert246Data.sigEnc
        cert246Data.nilLevelShifts cert246Data.nilLevelPmasks
        cert246Data.nilLevelWidths cert246Data.nilLevelMasks
        cert246Data.nilLevelTrees s t ∧
    cert246Data.nilMomentValueLevels 49 24 cert246Data.sigEnc
      cert246Data.nilLevelShifts cert246Data.nilLevelPmasks
      cert246Data.nilLevelWidths cert246Data.nilLevelMasks
      cert246Data.nilLevelTrees s t < 2 ^ 256 := by
  intro t ht s hst
  obtain ⟨hpair, hbound⟩ := certResultAndBoundRaw t ht s hst
  rw [nilMomentPairPredLevels_fst cert246Data.coeff_ok] at hpair
  rw [nilMomentPairPredLevels_snd cert246Data.coeff_ok] at hbound
  exact ⟨hpair, hbound⟩

/-- Every row of the checked final packed-pair table is sound. -/
theorem certResult : ∀ t < 272, ∀ s ≤ t,
      cert246Data.treeAt 7 127 512 (2 ^ 512 - 1) cert246Data.pairT
        (cert246Data.triIdx s t) =
      cert246Data.nilMomentPairLevels 256 50 24 cert246Data.sigEnc
        cert246Data.nilLevelShifts cert246Data.nilLevelPmasks
        cert246Data.nilLevelWidths cert246Data.nilLevelMasks
        cert246Data.nilLevelTrees s t :=
  fun t ht s hst ↦ (certResultAndBound t ht s hst).1

/-- Every final packed pair contains the dimension-fifty and dimension-forty-nine
factorial moments. -/
theorem certMomentPairs : ∀ t < 272, ∀ s ≤ t,
    cert246Data.treeAt 7 127 512 (2 ^ 512 - 1) cert246Data.pairT
        (cert246Data.triIdx s t) =
      facMomentNat 49 (PrimeGaps.Gap246.sigOf cert246Data.sigEnc s)
          (PrimeGaps.Gap246.sigOf cert246Data.sigEnc t) +
        (facMomentNat 50 (PrimeGaps.Gap246.sigOf cert246Data.sigEnc s)
          (PrimeGaps.Gap246.sigOf cert246Data.sigEnc t)).shiftLeft 256 :=
  concreteMomentLevelPairsSound certBase certSteps certResult

end PrimeGaps.Gap246
