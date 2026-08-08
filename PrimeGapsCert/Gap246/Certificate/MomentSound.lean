/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Certificate.Defs
public import PrimeGapsCert.Gap246.Moments.TableSound

/-! # Bridge from the triangular moment result to the lightweight certificate interface -/

@[expose] public section

namespace PrimeGaps.Gap246

/-- A sound triangular result table gives the two mathematical moments for every ordered
signature pair. -/
theorem certPairValue_sound
    (hpairs : ∀ t < 272, ∀ s ≤ t,
      cert246Data.treeAt 7 127 512 (2 ^ 512 - 1) cert246Data.pairT
          (cert246Data.triIdx s t) =
        facMomentNat 49 (sigOf cert246Data.sigEnc s) (sigOf cert246Data.sigEnc t) +
          (facMomentNat 50 (sigOf cert246Data.sigEnc s)
            (sigOf cert246Data.sigEnc t)).shiftLeft 256)
    (pair : Fin (272 * 272)) :
    certPairValue pair =
      facMomentNat 49 (sigOf cert246Data.sigEnc pair.divNat)
          (sigOf cert246Data.sigEnc pair.modNat) +
        (facMomentNat 50 (sigOf cert246Data.sigEnc pair.divNat)
          (sigOf cert246Data.sigEnc pair.modNat)).shiftLeft 256 := by
  by_cases horder : pair.divNat ≤ pair.modNat
  · simpa only [certPairValue] using hpairs pair.modNat pair.modNat.isLt pair.divNat horder
  · have h := hpairs pair.divNat pair.divNat.isLt pair.modNat (le_of_not_ge horder)
    rw [triIdx_comm, facMomentNat_comm 49, facMomentNat_comm 50] at h
    simpa only [certPairValue] using h

/-- Sound reconstructed pair values agree with the direct packed-pair specification. -/
theorem prePairValue_eq_direct
    (hpairs : ∀ t < 272, ∀ s ≤ t,
      cert246Data.treeAt 7 127 512 (2 ^ 512 - 1) cert246Data.pairT
          (cert246Data.triIdx s t) =
        facMomentNat 49 (sigOf cert246Data.sigEnc s) (sigOf cert246Data.sigEnc t) +
          (facMomentNat 50 (sigOf cert246Data.sigEnc s)
            (sigOf cert246Data.sigEnc t)).shiftLeft 256) :
    ∀ pair, preEpsWitnessInt.pairValue pair = preEpsWitnessInt.directPairValue pair := by
  change ∀ pair : Fin (272 * 272), certPairValue pair =
    let moments := facMomentDirectPair 50 49 (certSig pair.divNat) (certSig pair.modNat)
    2 ^ 256 * moments.1 + moments.2
  intro pair
  rw [certPairValue_sound hpairs,
    facMomentDirectPair_eq 50 49 (certSig pair.divNat) (certSig pair.modNat)
      (certSig_zeroFree pair.divNat pair.divNat.isLt)
      (certSig_zeroFree pair.modNat pair.modNat.isLt)]
  simp only [certSig_coe]
  rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq]
  ring

/-- The packed moment lookup is symmetric before any mathematical soundness assumptions. -/
theorem prePairValue_comm (left right : Fin 272) :
    preEpsWitnessInt.pairValue (signaturePairIndex left right) =
      preEpsWitnessInt.pairValue (signaturePairIndex right left) := by
  simp only [preEpsWitnessInt, certPairValue, signaturePairIndex_divNat,
    signaturePairIndex_modNat, triIdx_comm]

/-- The high packed moment lane is symmetric by its triangular storage. -/
theorem preMomentTop_comm (left right : Fin 272) :
    preEpsWitnessInt.momentTop left right = preEpsWitnessInt.momentTop right left := by
  simp only [PreEpsCertificateExplicitDagInt.momentTop, prePairValue_comm]

/-- The low packed moment lane is symmetric by its triangular storage. -/
theorem preMomentPred_comm (left right : Fin 272) :
    preEpsWitnessInt.momentPred left right = preEpsWitnessInt.momentPred right left := by
  simp only [PreEpsCertificateExplicitDagInt.momentPred, prePairValue_comm]

end PrimeGaps.Gap246
