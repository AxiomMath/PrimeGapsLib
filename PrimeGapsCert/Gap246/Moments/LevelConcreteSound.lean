/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Data.Sound
public import PrimeGapsCert.Gap246.Moments.LevelDefs
public import PrimeGapsCert.Gap246.Moments.LevelGather
public import PrimeGapsCert.Gap246.Moments.PairDefs

/-! # Concrete soundness of the independently packed packed moment levels -/

@[expose] public section

namespace PrimeGaps.Gap246

/-- Every concrete decoded signature is zero-free. -/
theorem levelCertZeroFree : ∀ row < 272, (0 : ℕ) ∉ sigOf cert246Data.sigEnc row :=
  fun row hrow ↦ zero_notMem_decodeSig fun position hposition ↦
    (certRows row hrow).nib_pos position hposition

/-- A concrete pair of signatures contains at most twenty-four parts. -/
theorem levelCertPairCount (s t : ℕ) (hs : s < 272) (ht : t < 272) :
    (sigOf cert246Data.sigEnc s).card + (sigOf cert246Data.sigEnc t).card ≤ 24 := by
  rw [sigOf_card, sigOf_card]
  have hsCount := (certRows s hs).count_le
  have htCount := (certRows t ht).count_le
  omega

/-- The concrete support-masked transition equations. -/
abbrev ConcreteLevelSteps : Prop :=
  ∀ level, 0 < level → level ≤ 24 → ∀ t < 272, ∀ s ≤ t,
    let active := cert246Data.nilActive level
      (cert246Data.sigCount (cert246Data.sigField cert246Data.sigEnc s) +
        cert246Data.sigCount (cert246Data.sigField cert246Data.sigEnc t))
    Bool.rec (motive := fun _ ↦ ℕ) 0
      (cert246Data.nilLevelAt cert246Data.nilLevelShifts
        cert246Data.nilLevelPmasks cert246Data.nilLevelWidths cert246Data.nilLevelMasks
        cert246Data.nilLevelTrees level (cert246Data.triIdx s t)) active =
      Bool.rec (motive := fun _ ↦ ℕ) 0
        (cert246Data.nilLevelEntry cert246Data.sigEnc cert246Data.eraseEnc
        cert246Data.factT level cert246Data.nilLevelShifts cert246Data.nilLevelPmasks
        cert246Data.nilLevelWidths cert246Data.nilLevelMasks cert246Data.nilLevelTrees s t)
        active

/-- The concrete support-masked nilpotent ladder. -/
abbrev ConcreteLevelLadder : Prop :=
  ∀ level ≤ 24, ∀ t < 272, ∀ s ≤ t,
    Bool.rec (motive := fun _ ↦ ℕ) 0
      (cert246Data.nilLevelAt cert246Data.nilLevelShifts
        cert246Data.nilLevelPmasks cert246Data.nilLevelWidths cert246Data.nilLevelMasks
        cert246Data.nilLevelTrees level (cert246Data.triIdx s t))
      (cert246Data.nilActive level
        (cert246Data.sigCount (cert246Data.sigField cert246Data.sigEnc s) +
          cert246Data.sigCount (cert246Data.sigField cert246Data.sigEnc t))) =
      nilMoment level (sigOf cert246Data.sigEnc s) (sigOf cert246Data.sigEnc t)

/-- Checked independent levels identify the complete concrete nilpotent ladder. -/
theorem concreteNilLevelLadderSound
    (hbase : ∀ t < 272, ∀ s ≤ t,
      cert246Data.nilLevelAt cert246Data.nilLevelShifts cert246Data.nilLevelPmasks
          cert246Data.nilLevelWidths cert246Data.nilLevelMasks cert246Data.nilLevelTrees
          0 (cert246Data.triIdx s t) =
        if cert246Data.sigField cert246Data.sigEnc s = 0 ∧
            cert246Data.sigField cert246Data.sigEnc t = 0 then 1 else 0)
    (hstep : ConcreteLevelSteps) : ConcreteLevelLadder :=
  nilLevelLadder_sound (S := 272) (maxNib := 12) (partBound := 12)
    (sigEnc := cert246Data.sigEnc) (eraseEnc := cert246Data.eraseEnc)
    (factT := cert246Data.factT) (lastLevel := 24)
    (shifts := cert246Data.nilLevelShifts) (pmasks := cert246Data.nilLevelPmasks)
    (widths := cert246Data.nilLevelWidths) (masks := cert246Data.nilLevelMasks)
    (trees := cert246Data.nilLevelTrees) (by norm_num) certRows certEncoding certParts
    (fun n hn ↦ certFactorials n (by omega)) hbase hstep

/-- The gathered split-level checks imply both factorial moments in every final pair. -/
theorem concreteMomentLevelPairsSound
    (hbase : ∀ t < 272, ∀ s ≤ t,
      cert246Data.nilLevelAt cert246Data.nilLevelShifts cert246Data.nilLevelPmasks
          cert246Data.nilLevelWidths cert246Data.nilLevelMasks cert246Data.nilLevelTrees
          0 (cert246Data.triIdx s t) =
        if cert246Data.sigField cert246Data.sigEnc s = 0 ∧
            cert246Data.sigField cert246Data.sigEnc t = 0 then 1 else 0)
    (hstep : ConcreteLevelSteps)
    (hresult : ∀ t < 272, ∀ s ≤ t,
      cert246Data.treeAt 7 127 512 (2 ^ 512 - 1) cert246Data.pairT
          (cert246Data.triIdx s t) =
        cert246Data.nilMomentPairLevels 256 50 24 cert246Data.sigEnc
          cert246Data.nilLevelShifts cert246Data.nilLevelPmasks
          cert246Data.nilLevelWidths cert246Data.nilLevelMasks
          cert246Data.nilLevelTrees s t) :
    ∀ t < 272, ∀ s ≤ t,
      cert246Data.treeAt 7 127 512 (2 ^ 512 - 1) cert246Data.pairT
          (cert246Data.triIdx s t) =
        facMomentNat 49 (sigOf cert246Data.sigEnc s) (sigOf cert246Data.sigEnc t) +
          (facMomentNat 50 (sigOf cert246Data.sigEnc s)
            (sigOf cert246Data.sigEnc t)).shiftLeft 256 := by
  have hladder := concreteNilLevelLadderSound hbase hstep
  intro t ht s hst
  have hpair := levelCertPairCount s t (by omega) ht
  rw [hresult t ht s hst]
  exact nilMomentPairLevels_sound (by simp only [sigOf_card]) hpair (by omega)
    (fun level hlevel ↦ hladder level (hlevel.trans hpair) t ht s hst)
    (levelCertZeroFree s (by omega)) (levelCertZeroFree t ht)

/-- A checked split-level predecessor bound implies the mathematical moment bound. -/
theorem concreteMomentPredLevelBoundSound
    (hbase : ∀ t < 272, ∀ s ≤ t,
      cert246Data.nilLevelAt cert246Data.nilLevelShifts cert246Data.nilLevelPmasks
          cert246Data.nilLevelWidths cert246Data.nilLevelMasks cert246Data.nilLevelTrees
          0 (cert246Data.triIdx s t) =
        if cert246Data.sigField cert246Data.sigEnc s = 0 ∧
            cert246Data.sigField cert246Data.sigEnc t = 0 then 1 else 0)
    (hstep : ConcreteLevelSteps)
    (hbound : ∀ t < 272, ∀ s ≤ t,
      cert246Data.nilMomentValueLevels 49 24 cert246Data.sigEnc
        cert246Data.nilLevelShifts cert246Data.nilLevelPmasks
        cert246Data.nilLevelWidths cert246Data.nilLevelMasks
        cert246Data.nilLevelTrees s t < 2 ^ 256) :
    ∀ t < 272, ∀ s ≤ t,
      facMomentNat 49 (sigOf cert246Data.sigEnc s) (sigOf cert246Data.sigEnc t) <
        2 ^ 256 := by
  have hladder := concreteNilLevelLadderSound hbase hstep
  intro t ht s hst
  have hpair := levelCertPairCount s t (by omega) ht
  calc
    facMomentNat 49 (sigOf cert246Data.sigEnc s) (sigOf cert246Data.sigEnc t) =
        cert246Data.nilMomentValueLevels 49 24 cert246Data.sigEnc
          cert246Data.nilLevelShifts cert246Data.nilLevelPmasks
          cert246Data.nilLevelWidths cert246Data.nilLevelMasks
          cert246Data.nilLevelTrees s t :=
      (nilMomentValueLevels_sound (by simp only [sigOf_card]) hpair (by omega)
        (fun level hlevel ↦ hladder level (hlevel.trans hpair) t ht s hst)
        (levelCertZeroFree s (by omega)) (levelCertZeroFree t ht)).symm
    _ < 2 ^ 256 := hbound t ht s hst

end PrimeGaps.Gap246
