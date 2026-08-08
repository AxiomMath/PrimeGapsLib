/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Certificate.Fast
public import PrimeGapsCert.Gap246.Kernel.RHSFormula
public import PrimeGapsCert.Gap246.Sparse.AccessorBridge
public import PrimeGapsCert.Gap246.Sparse.SignedSound


/-! # Soundness of sparse RHS feature and support checks -/

@[expose] public section

namespace PrimeGaps.Gap246

/-- A successful raw feature-key check exposes its four component facts. -/
theorem rhsFeatureKeyAt_sound
    {featureCount degreeBound sourceCs sourcePmask eraseCs erasePmask labelEnc featureEnc label
      exponent : ℕ} {sourceTree eraseTree : Lean.RArray ℕ}
    (hcheck : cert246Data.rhsFeatureKeyAt featureCount degreeBound sourceCs sourcePmask
      eraseCs erasePmask labelEnc featureEnc sourceTree eraseTree label exponent = true) :
    let labelField := cert246Data.labelField labelEnc label
    let sourceSignature := cert246Data.labelSignature labelField
    let location := cert246Data.treeAt sourceCs sourcePmask 16 65535 sourceTree
      (label * (degreeBound + 1) + exponent)
    let erasedSignature := cert246Data.treeAt eraseCs erasePmask 16 65535 eraseTree
      (sourceSignature * (degreeBound + 1) + exponent)
    let featureField := cert246Data.rhsFeatureField featureEnc location
    location < featureCount ∧ cert246Data.rhsFeatureSignature featureField = erasedSignature ∧
      cert246Data.rhsFeatureResidual featureField = cert246Data.labelDegree labelField - exponent ∧
      cert246Data.rhsFeatureRadial featureField =
        cert246Data.labelA labelField + exponent + 1 := by
  unfold cert246Data.rhsFeatureKeyAt at hcheck
  dsimp only
  simpa only [Bool.and'_eq_and, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.add_eq,
    Nat.mul_eq, Nat.sub_eq] using hcheck

/-- A successful label check covers its identity transition and every signature position. -/
theorem rhsFeatureKeyLabelCheck_sound
    {featureCount degreeBound sourceCs sourcePmask eraseCs erasePmask sigEnc labelEnc featureEnc
      label : ℕ} {sourceTree eraseTree : Lean.RArray ℕ}
    (hcheck : cert246Data.rhsFeatureKeyLabelCheck featureCount degreeBound sourceCs sourcePmask
      eraseCs erasePmask sigEnc labelEnc featureEnc sourceTree eraseTree label = true) :
    cert246Data.rhsFeatureKeyAt featureCount degreeBound sourceCs sourcePmask eraseCs erasePmask
        labelEnc featureEnc sourceTree eraseTree label 0 = true ∧
      ∀ position < cert246Data.sigCount (cert246Data.sigField sigEnc
          (cert246Data.labelSignature (cert246Data.labelField labelEnc label))),
        cert246Data.rhsFeatureKeyAt featureCount degreeBound sourceCs sourcePmask eraseCs
          erasePmask labelEnc featureEnc sourceTree eraseTree label
            (2 * cert246Data.sigNib
              (cert246Data.sigField sigEnc
                (cert246Data.labelSignature (cert246Data.labelField labelEnc label))) position) =
                  true := by
  unfold cert246Data.rhsFeatureKeyLabelCheck at hcheck
  obtain ⟨hidentity, hpositions⟩ := Bool.and_eq_true_iff.mp hcheck
  refine ⟨hidentity, fun position hposition ↦ ?_⟩
  exact boolRec_sound _ _ _ hpositions position (by omega) (by omega)

/-- A successful range check supplies every label-and-erasure feature-key check in the range. -/
theorem rhsFeatureKeysCheck_sound
    {featureCount degreeBound sourceCs sourcePmask eraseCs erasePmask sigEnc labelEnc featureEnc
      lower upper : ℕ} {sourceTree eraseTree : Lean.RArray ℕ}
    (hcheck : cert246Data.rhsFeatureKeysCheck featureCount degreeBound sourceCs sourcePmask
      eraseCs erasePmask sigEnc labelEnc featureEnc lower upper sourceTree eraseTree = true) :
    ∀ label, lower ≤ label → label < upper →
      cert246Data.rhsFeatureKeyLabelCheck featureCount degreeBound sourceCs sourcePmask eraseCs
        erasePmask sigEnc labelEnc featureEnc sourceTree eraseTree label = true := by
  intro label hlower hupper
  unfold cert246Data.rhsFeatureKeysCheck at hcheck
  exact boolRec_sound _ (upper - lower) lower hcheck label hlower (by omega)

/-- A successful pair-support check makes every smaller-side RHS transform location positive. -/
theorem rhsSupportPairCheck_sound
    {signatureCount featureEnc groupEnc locationCs locationPmask left right : ℕ}
    {locationTree : Lean.RArray ℕ}
    (hcheck : cert246Data.rhsSupportPairCheck signatureCount featureEnc groupEnc
      locationCs locationPmask locationTree left right = true) :
    let leftField := cert246Data.groupField groupEnc left
    let rightField := cert246Data.groupField groupEnc right
    let useLeft := Nat.ble (cert246Data.groupSize leftField)
      (cert246Data.groupSize rightField)
    let sourceField : ℕ := Bool.rec rightField leftField useLeft
    let transformGroup : ℕ := Bool.rec left right useLeft
    ∀ offset < cert246Data.groupSize sourceField,
      let featureField := cert246Data.rhsFeatureField featureEnc
        (cert246Data.groupStart sourceField + offset)
      let target := cert246Data.rhsFeatureSignature featureField
      0 < cert246Data.treeAt locationCs locationPmask 16 65535 locationTree
        (transformGroup * signatureCount + target) := by
  dsimp only
  intro offset hoffset
  let leftField := cert246Data.groupField groupEnc left
  let rightField := cert246Data.groupField groupEnc right
  let useLeft := Nat.ble (cert246Data.groupSize leftField)
    (cert246Data.groupSize rightField)
  let sourceField : ℕ := Bool.rec rightField leftField useLeft
  let transformGroup : ℕ := Bool.rec left right useLeft
  have hoffset' : offset < cert246Data.groupSize sourceField := by
    simpa only [leftField, rightField, useLeft, sourceField] using hoffset
  have hscan :
      Nat.rec (motive := fun _ ↦ ℕ → Bool)
          (fun _ ↦ true)
          (fun _ inductionHypothesis cursor ↦
            let featureField := cert246Data.rhsFeatureField featureEnc cursor
            let target := cert246Data.rhsFeatureSignature featureField
            Bool.rec false (inductionHypothesis cursor.succ)
              (Nat.blt 0 (cert246Data.treeAt locationCs locationPmask 16 65535 locationTree
                (transformGroup * signatureCount + target))))
          (cert246Data.groupSize sourceField)
          (cert246Data.groupStart sourceField) = true := by
    simpa only [cert246Data.rhsSupportPairCheck, leftField, rightField, useLeft,
      sourceField, transformGroup, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] using hcheck
  have h := boolRec_sound
    (fun cursor ↦
      let featureField := cert246Data.rhsFeatureField featureEnc cursor
      let target := cert246Data.rhsFeatureSignature featureField
      Nat.blt 0 (cert246Data.treeAt locationCs locationPmask 16 65535 locationTree
        (transformGroup * signatureCount + target)))
    (cert246Data.groupSize sourceField)
    (cert246Data.groupStart sourceField) hscan
    (cert246Data.groupStart sourceField + offset) (by omega) (by omega)
  simpa only [Nat.blt_eq, leftField, rightField, useLeft, sourceField, transformGroup] using h

/-- A successful row-support check covers every contraction query in that upper RHS row. -/
theorem rhsSupportRowCheck_sound
    {groupCount signatureCount featureEnc groupEnc locationCs locationPmask : ℕ}
    {locationTree : Lean.RArray ℕ} {left : ℕ}
    (hcheck : cert246Data.rhsSupportRowCheck groupCount signatureCount featureEnc groupEnc
      locationCs locationPmask locationTree left = true) :
    ∀ right, left ≤ right → right < groupCount →
      let leftField := cert246Data.groupField groupEnc left
      let rightField := cert246Data.groupField groupEnc right
      let useLeft := Nat.ble (cert246Data.groupSize leftField)
        (cert246Data.groupSize rightField)
      let sourceField : ℕ := Bool.rec rightField leftField useLeft
      let transformGroup : ℕ := Bool.rec left right useLeft
      ∀ offset < cert246Data.groupSize sourceField,
        let featureField := cert246Data.rhsFeatureField featureEnc
          (cert246Data.groupStart sourceField + offset)
        let target := cert246Data.rhsFeatureSignature featureField
        0 < cert246Data.treeAt locationCs locationPmask 16 65535 locationTree
          (transformGroup * signatureCount + target) := by
  intro right hright hrightBound
  unfold cert246Data.rhsSupportRowCheck at hcheck
  have hpair := boolRec_sound
    (fun right ↦ cert246Data.rhsSupportPairCheck signatureCount featureEnc groupEnc
      locationCs locationPmask locationTree left right)
    (groupCount - left) left hcheck right hright (by omega)
  exact rhsSupportPairCheck_sound hpair

/-- A successful radial range check supplies every checked local recurrence entry. -/
theorem rhsRadialCheck_sound
    {dimension epsilonDenominator radialDimension radialCs radialPmask radialWidth radialMask
      lower upper : ℕ} {radialTree : Lean.RArray ℕ}
    (hcheck : cert246Data.rhsRadialCheck dimension epsilonDenominator radialDimension radialCs
      radialPmask radialWidth radialMask lower upper radialTree = true) :
    ∀ index, lower ≤ index → index < upper →
      cert246Data.rhsRadialEntryCheck dimension epsilonDenominator radialDimension radialCs
        radialPmask radialWidth radialMask index radialTree = true := by
  intro index hlower hupper
  unfold cert246Data.rhsRadialCheck at hcheck
  exact boolRec_sound _ (upper - lower) lower hcheck index hlower (by omega)

/-- A valid successful radial entry is its boundary formula or its local recurrence. -/
theorem rhsRadialEntryCheck_sound
    {dimension epsilonDenominator radialDimension radialCs radialPmask radialWidth radialMask
      index : ℕ} {radialTree : Lean.RArray ℕ}
    (hcheck : cert246Data.rhsRadialEntryCheck dimension epsilonDenominator radialDimension
      radialCs radialPmask radialWidth radialMask index radialTree = true)
    (hlower : dimension - 1 ≤ index / radialDimension)
    (hupper : index / radialDimension + index % radialDimension ≤ 2 * dimension + 1) :
    let q := index / radialDimension
    let e := index % radialDimension
    let value := cert246Data.treeAt radialCs radialPmask radialWidth radialMask radialTree index
    if e = 0 then value = cert246Data.rhsRadialBoundary dimension epsilonDenominator q
    else epsilonDenominator * value + epsilonDenominator * q *
        cert246Data.treeAt radialCs radialPmask radialWidth radialMask radialTree
          ((q + 1) * radialDimension + (e - 1)) =
      (epsilonDenominator + 1) *
        cert246Data.treeAt radialCs radialPmask radialWidth radialMask radialTree
          (q * radialDimension + (e - 1)) := by
  dsimp only
  unfold cert246Data.rhsRadialEntryCheck at hcheck
  dsimp only at hcheck
  have hregion : Bool.and' (Nat.ble (Nat.sub dimension 1) (index / radialDimension))
      (Nat.ble (Nat.add (index / radialDimension) (index % radialDimension))
        (Nat.add (Nat.mul 2 dimension) 1)) = true := by
    simp only [Bool.and'_eq_and, Bool.and_eq_true, Nat.ble_eq, Nat.add_eq, Nat.mul_eq,
      Nat.sub_eq, hlower, hupper, and_self]
  rw [hregion] at hcheck
  by_cases he : index % radialDimension = 0
  · rw [show Nat.beq (index % radialDimension) 0 = true from Nat.beq_eq.mpr he] at hcheck
    simpa only [he, if_true, Nat.beq_eq] using hcheck
  · rw [show Nat.beq (index % radialDimension) 0 = false from
      Bool.eq_false_of_not_eq_true fun h ↦ he (Nat.beq_eq.mp h)] at hcheck
    simpa only [he, if_false, Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] using hcheck

/-- The first-order radial boundary is the degree-zero generic radial formula. -/
@[simp] theorem rhsRadialBoundary_eq_formula (dimension epsilonDenominator q : ℕ) :
    cert246Data.rhsRadialBoundary dimension epsilonDenominator q =
      cert246Data.rhsRadialFormula dimension epsilonDenominator q 0 := by
  simp [cert246Data.rhsRadialBoundary, cert246Data.rhsRadialFormula,
    descFactorialFold_eq_descFactorial]

/-- The generic first-order radial formula is the generic cleared radial factor. -/
theorem rhsRadialFormula_eq (dimension epsilonDenominator q e : ℕ) :
    cert246Data.rhsRadialFormula dimension epsilonDenominator q e =
      radialExplicitInt dimension epsilonDenominator q e := rfl

end PrimeGaps.Gap246
