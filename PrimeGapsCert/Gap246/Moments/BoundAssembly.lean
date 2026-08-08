/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Certificate.MomentSound
public import PrimeGapsCert.Gap246.Moments.Assembly

/-! # Assembly of the predecessor-moment radix bound -/

@[expose] public section

namespace PrimeGaps.Gap246

/-- Every reconstructed dimension-forty-nine moment fits its 256-bit lane. -/
theorem certMomentPredRawBound : ∀ t < 272, ∀ s ≤ t,
    cert246Data.nilMomentValueLevels 49 24 cert246Data.sigEnc
      cert246Data.nilLevelShifts cert246Data.nilLevelPmasks
      cert246Data.nilLevelWidths cert246Data.nilLevelMasks
      cert246Data.nilLevelTrees s t < 2 ^ 256 :=
  fun t ht s hst ↦ (certResultAndBound t ht s hst).2

/-- The checked raw bound is the corresponding mathematical factorial-moment bound. -/
theorem certMomentPredTriBound : ∀ t < 272, ∀ s ≤ t,
    facMomentNat 49 (sigOf cert246Data.sigEnc s) (sigOf cert246Data.sigEnc t) <
      2 ^ 256 :=
  concreteMomentPredLevelBoundSound certBase certSteps certMomentPredRawBound

/-- The predecessor bound holds for every ordered signature pair. -/
theorem certMomentPredNat_lt (pair : Fin (272 * 272)) :
    facMomentNat 49 (sigOf cert246Data.sigEnc pair.divNat)
        (sigOf cert246Data.sigEnc pair.modNat) < 2 ^ 256 := by
  by_cases horder : pair.divNat ≤ pair.modNat
  · exact certMomentPredTriBound pair.modNat pair.modNat.isLt pair.divNat horder
  · have h := certMomentPredTriBound pair.divNat pair.divNat.isLt pair.modNat
      (le_of_not_ge horder)
    rwa [facMomentNat_comm] at h

/-- The direct predecessor evaluator is smaller than the packed moment radix. -/
theorem certMomentPred_lt (pair : Fin (preEpsWitnessInt.S * preEpsWitnessInt.S)) :
    facMomentDirect 49
        (preEpsWitnessInt.sig pair.divNat) (preEpsWitnessInt.sig pair.modNat) <
      preEpsWitnessInt.momentRadix := by
  change Fin (272 * 272) at pair
  change facMomentDirect 49 (certSig pair.divNat) (certSig pair.modNat) < 2 ^ 256
  rw [facMomentDirect_eq 49 (certSig pair.divNat) (certSig pair.modNat)
    (certSig_zeroFree pair.divNat pair.divNat.isLt)
    (certSig_zeroFree pair.modNat pair.modNat.isLt)]
  simpa only [certSig_coe] using certMomentPredNat_lt pair

end PrimeGaps.Gap246
