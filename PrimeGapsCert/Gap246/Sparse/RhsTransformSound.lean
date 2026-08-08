/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Kernel.RHS
public import PrimeGapsCert.Gap246.Sparse.SignedSound


/-! # Soundness of sparse RHS transform sums -/

@[expose] public section

namespace PrimeGaps.Gap246

open Finset

/-- Integer weight represented by one packed RHS feature. -/
noncomputable def rhsFeatureWeight
    (weightCs weightPmask weightWidth weightMask : ℕ)
    (weightTree : Lean.RArray ℕ) (feature : ℕ) : ℤ :=
  signedValue (cert246Data.treeAt weightCs weightPmask weightWidth weightMask
    weightTree feature)

/-- Mathematical integer sum represented by one raw sparse RHS transform. -/
noncomputable def rhsTransformSpec
    (featureEnc groupEnc weightCs weightPmask weightWidth weightMask pairCs pairPmask pairWidth
      pairMask outMask : ℕ) (weightTree pairTree : Lean.RArray ℕ)
    (group target : ℕ) : ℤ :=
  let groupField := cert246Data.groupField groupEnc group
  ∑ offset ∈ Finset.range (cert246Data.groupSize groupField),
    let position := cert246Data.groupStart groupField + offset
    let featureField := cert246Data.rhsFeatureField featureEnc position
    rhsFeatureWeight weightCs weightPmask weightWidth weightMask weightTree position *
      cert246Data.rhsMomentPred pairCs pairPmask pairWidth pairMask outMask pairTree target
        (cert246Data.rhsFeatureSignature featureField)

/-- The raw two-lane RHS transform denotes its integer finite sum. -/
theorem rhsTransformValue_sound
    (featureEnc groupEnc weightCs weightPmask weightWidth weightMask pairCs pairPmask pairWidth
      pairMask outMask : ℕ) (weightTree pairTree : Lean.RArray ℕ)
    (group target : ℕ) :
    signedValue (cert246Data.rhsTransformValue featureEnc groupEnc weightCs weightPmask
      weightWidth weightMask pairCs pairPmask pairWidth pairMask outMask weightTree pairTree
      group target) = rhsTransformSpec featureEnc groupEnc weightCs weightPmask weightWidth
        weightMask pairCs pairPmask pairWidth pairMask outMask weightTree pairTree group
        target := by
  unfold cert246Data.rhsTransformValue rhsTransformSpec
  let groupField := cert246Data.groupField groupEnc group
  let weight : ℕ → ℕ := fun cursor ↦
    cert246Data.treeAt weightCs weightPmask weightWidth weightMask weightTree cursor
  let moment : ℕ → ℕ := fun cursor ↦
    let featureField := cert246Data.rhsFeatureField featureEnc cursor
    cert246Data.rhsMomentPred pairCs pairPmask pairWidth pairMask outMask pairTree target
      (cert246Data.rhsFeatureSignature featureField)
  simp only [Nat.add_eq, Nat.mul_eq]
  rw [signedRec_sound (fun cursor ↦ Nat.beq (cert246Data.signedSign (weight cursor)) 0)
    (fun cursor ↦ cert246Data.signedMagnitude (weight cursor) * moment cursor)]
  simp only [Int.ofNat_zero, sub_self, zero_add]
  apply Finset.sum_congr rfl
  intro offset _
  unfold weight moment rhsFeatureWeight
  simp only [Nat.beq_eq]
  exact signedScaleTerm _ _

/-- A successful raw RHS transform-range check yields every stored equality in that range. -/
theorem rhsTransformCheck_sound
    {transformCs transformPmask transformWidth transformMask featureEnc groupEnc keyEnc weightCs
      weightPmask weightWidth weightMask pairCs pairPmask pairWidth pairMask outMask lower
      upper : ℕ}
    {transformTree weightTree pairTree : Lean.RArray ℕ}
    (hcheck : cert246Data.rhsTransformCheck transformCs transformPmask transformWidth
      transformMask featureEnc groupEnc keyEnc weightCs weightPmask weightWidth weightMask pairCs
      pairPmask pairWidth pairMask outMask transformTree weightTree pairTree lower upper = true) :
    ∀ entry, lower ≤ entry → entry < upper →
      cert246Data.treeAt transformCs transformPmask transformWidth transformMask transformTree
          entry =
        let key := cert246Data.keyField keyEnc entry
        cert246Data.rhsTransformValue featureEnc groupEnc weightCs weightPmask weightWidth
          weightMask pairCs pairPmask pairWidth pairMask outMask weightTree pairTree
          (cert246Data.keyGroup key) (cert246Data.keyTarget key) := by
  intro entry hlower hupper
  unfold cert246Data.rhsTransformCheck at hcheck
  have h := boolRec_sound
    (fun entry ↦
      let key := cert246Data.keyField keyEnc entry
      Nat.beq
        (cert246Data.treeAt transformCs transformPmask transformWidth transformMask
          transformTree entry)
        (cert246Data.rhsTransformValue featureEnc groupEnc weightCs weightPmask weightWidth
          weightMask pairCs pairPmask pairWidth pairMask outMask weightTree pairTree
          (cert246Data.keyGroup key) (cert246Data.keyTarget key)))
    (upper - lower) lower hcheck entry hlower (by omega)
  simpa only [Nat.beq_eq] using h

end PrimeGaps.Gap246
