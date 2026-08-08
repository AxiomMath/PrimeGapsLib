/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Kernel.RHS
public import PrimeGapsCert.Gap246.Sparse.SignedSound


/-! # Soundness of sparse RHS index checks -/

@[expose] public section

namespace PrimeGaps.Gap246

/-- A successful ranged packed-key check bounds every RHS entry in that range. -/
theorem rhsKeysRangeCheck_sound
    {groupCount signatureCount keyEnc lower upper : ℕ}
    (hcheck : cert246Data.rhsKeysRangeCheck groupCount signatureCount keyEnc lower upper = true) :
    ∀ entry, lower ≤ entry → entry < upper →
      let field := cert246Data.keyField keyEnc entry
      cert246Data.keyGroup field < groupCount ∧
        cert246Data.keyTarget field < signatureCount := by
  intro entry hlower hupper
  unfold cert246Data.rhsKeysRangeCheck at hcheck
  have h := boolRec_sound
    (fun entry ↦
      let field := cert246Data.keyField keyEnc entry
      Bool.and' (Nat.blt (cert246Data.keyGroup field) groupCount)
        (Nat.blt (cert246Data.keyTarget field) signatureCount))
    (upper - lower) lower hcheck entry (by omega) (by omega)
  simpa only [Bool.and'_eq_and, Bool.and_eq_true, Nat.blt_eq] using h

/-- A successful ranged signature check bounds every decoded RHS feature signature in that
range. -/
theorem rhsFeatureSignatureRangeCheck_sound
    {signatureCount featureEnc lower upper : ℕ}
    (hcheck : cert246Data.rhsFeatureSignatureRangeCheck signatureCount featureEnc lower upper =
      true) :
    ∀ feature, lower ≤ feature → feature < upper →
      cert246Data.rhsFeatureSignature
        (cert246Data.rhsFeatureField featureEnc feature) < signatureCount := by
  intro feature hlower hupper
  unfold cert246Data.rhsFeatureSignatureRangeCheck at hcheck
  have h := boolRec_sound
    (fun feature ↦ Nat.blt
      (cert246Data.rhsFeatureSignature (cert246Data.rhsFeatureField featureEnc feature))
      signatureCount)
    (upper - lower) lower hcheck feature (by omega) (by omega)
  exact Nat.blt_eq.mp h

/-- A successful ranged sparse-location check decodes every RHS group row in that range. -/
theorem rhsLocationIndexRangeCheck_sound
    {signatureCount entryCount locationCs locationPmask keyEnc lower upper : ℕ}
    {locationTree : Lean.RArray ℕ}
    (hcheck : cert246Data.rhsLocationIndexRangeCheck signatureCount entryCount
      locationCs locationPmask keyEnc locationTree lower upper = true) :
    ∀ group, lower ≤ group → group < upper → ∀ target < signatureCount,
      let location := cert246Data.treeAt locationCs locationPmask 16 65535 locationTree
        (group * signatureCount + target)
      location = 0 ∨
        (0 < location ∧ location ≤ entryCount ∧
          cert246Data.keyGroup
              (cert246Data.keyField keyEnc (location - 1)) = group ∧
            cert246Data.keyTarget
              (cert246Data.keyField keyEnc (location - 1)) = target) := by
  intro group hlower hupper target htarget
  unfold cert246Data.rhsLocationIndexRangeCheck at hcheck
  have hgroupCheck := boolRec_sound
    (fun group ↦
      Nat.rec (motive := fun _ ↦ ℕ → Bool)
        (fun _ ↦ true)
        (fun _ targetHypothesis target ↦
          let location := cert246Data.treeAt locationCs locationPmask 16 65535 locationTree
            (group * signatureCount + target)
          let key := cert246Data.keyField keyEnc (location - 1)
          let valid := Bool.rec
            (Bool.and' (Nat.ble location entryCount)
              (Bool.and' (Nat.beq (cert246Data.keyGroup key) group)
                (Nat.beq (cert246Data.keyTarget key) target)))
            true (Nat.beq location 0)
          Bool.rec false (targetHypothesis target.succ) valid)
        signatureCount 0)
    (upper - lower) lower hcheck group (by omega) (by omega)
  have hentry := boolRec_sound
    (fun target ↦
      let location := cert246Data.treeAt locationCs locationPmask 16 65535 locationTree
        (group * signatureCount + target)
      let key := cert246Data.keyField keyEnc (location - 1)
      Bool.rec
        (Bool.and' (Nat.ble location entryCount)
          (Bool.and' (Nat.beq (cert246Data.keyGroup key) group)
            (Nat.beq (cert246Data.keyTarget key) target)))
        true (Nat.beq location 0))
    signatureCount 0 hgroupCheck target (by omega) (by omega)
  let location := cert246Data.treeAt locationCs locationPmask 16 65535 locationTree
    (group * signatureCount + target)
  by_cases hzero : location = 0
  · exact Or.inl hzero
  · have hfalse : Nat.beq location 0 = false :=
      Bool.eq_false_of_not_eq_true fun h ↦ hzero (Nat.beq_eq.mp h)
    change Bool.rec
      (Bool.and' (Nat.ble location entryCount)
        (Bool.and' (Nat.beq (cert246Data.keyGroup
            (cert246Data.keyField keyEnc (location - 1))) group)
          (Nat.beq (cert246Data.keyTarget
            (cert246Data.keyField keyEnc (location - 1))) target)))
      true (Nat.beq location 0) = true at hentry
    rw [hfalse] at hentry
    exact Or.inr ⟨Nat.pos_of_ne_zero hzero, by
      simpa only [Bool.and'_eq_and, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] using hentry⟩

end PrimeGaps.Gap246
