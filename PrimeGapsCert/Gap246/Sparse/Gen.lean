/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Emit.Gen

/-! # Untrusted generator for the packed sparse quadratic forms -/

@[expose] public section

open scoped Nat

namespace cert246Data.SparseGen

open cert246Data.Gen

/-- A signed natural represented by separate nonnegative accumulators. -/
structure SignedNat where
  positive : ℕ
  negative : ℕ
deriving Repr, Inhabited
attribute [nolint docBlame] SignedNat.positive SignedNat.negative

/-- Canonicalize a signed accumulator so at most one lane is nonzero. -/
def SignedNat.normalize (value : SignedNat) : SignedNat :=
  if value.negative ≤ value.positive then
    { positive := value.positive - value.negative, negative := 0 }
  else { positive := 0, negative := value.negative - value.positive }

/-- Add one signed magnitude to an accumulator. -/
def SignedNat.addMagnitude (value : SignedNat) (negative : Bool) (magnitude : ℕ) : SignedNat :=
  if negative then { value with negative := value.negative + magnitude }
  else { value with positive := value.positive + magnitude }

/-- Multiply a signed value by a signed magnitude and add it to an accumulator. -/
def SignedNat.addProduct (accumulator value : SignedNat) (negative : Bool)
    (magnitude : ℕ) : SignedNat :=
  let positiveMagnitude := magnitude * value.positive
  let negativeMagnitude := magnitude * value.negative
  if negative then
    { positive := accumulator.positive + negativeMagnitude
      negative := accumulator.negative + positiveMagnitude }
  else
    { positive := accumulator.positive + positiveMagnitude
      negative := accumulator.negative + negativeMagnitude }

/-- Scale both signed lanes by a nonnegative factor. -/
def SignedNat.scale (value : SignedNat) (factor : ℕ) : SignedNat :=
  { positive := factor * value.positive, negative := factor * value.negative }

/-- Encode a normalized signed value as a sign bit followed by its magnitude. -/
def SignedNat.encode (value : SignedNat) : ℕ :=
  let value := value.normalize
  if value.negative = 0 then value.positive <<< 1 else (value.negative <<< 1) + 1

/-- Pack a table of 64-bit group descriptors from each group's start, size and two degrees. -/
def packGroupTable (groups : Array (ℕ × ℕ × ℕ × ℕ)) : ℕ :=
  packTable 64 (groups.map fun (start, size, lowDegree, highDegree) ↦
    start + (size <<< 11) + (lowDegree <<< 22) + (highDegree <<< 28))

/-- Pack a table of 32-bit descriptors carrying a group in the low byte and one further field. -/
def packPairTable (entries : Array (ℕ × ℕ)) : ℕ :=
  packTable 32 (entries.map fun (group, field) ↦ group + (field <<< 8))

/-- One consecutive LHS degree group parsed from the committed partition. -/
structure LhsGroup where
  start : ℕ
  size : ℕ
  distinguishedDegree : ℕ
  signatureDegree : ℕ
  members : Array ℕ
deriving Repr, Inhabited
attribute [nolint docBlame] LhsGroup.start LhsGroup.size LhsGroup.distinguishedDegree
  LhsGroup.signatureDegree LhsGroup.members

/-- Dimensions and fixed-width lanes of the sparse LHS certificate. -/
structure LhsDims where
  dimension : ℕ
  epsilonDenominator : ℕ
  degreeBound : ℕ
  signatureCount : ℕ
  labelCount : ℕ
  groupCount : ℕ
  transformCount : ℕ
  scalarDimension : ℕ
  transformWidth : ℕ
  rowWidth : ℕ
  scalarWidth : ℕ
deriving Repr, Inhabited
attribute [nolint docBlame] LhsDims.dimension LhsDims.epsilonDenominator LhsDims.degreeBound
  LhsDims.signatureCount LhsDims.labelCount LhsDims.groupCount LhsDims.transformCount
  LhsDims.scalarDimension LhsDims.transformWidth LhsDims.rowWidth LhsDims.scalarWidth

/-- Serialize the LHS dimensions consumed by theorem-only modules. -/
def LhsDims.serialize (dims : LhsDims) : String :=
  String.intercalate " "
    ([dims.dimension, dims.epsilonDenominator, dims.degreeBound, dims.signatureCount,
      dims.labelCount, dims.groupCount, dims.transformCount, dims.scalarDimension,
      dims.transformWidth, dims.rowWidth, dims.scalarWidth].map toString)

/-- Packed tables proposed to the first-order sparse-LHS kernel. -/
structure LhsTables where
  dims : LhsDims
  groupEnc : ℕ
  memberEnc : ℕ
  inverseEnc : ℕ
  keyEnc : ℕ
  locationLeaves : Array ℕ
  transformLeaves : Array ℕ
  rowLeaves : Array ℕ
  scalarLeaves : Array ℕ
attribute [nolint docBlame] LhsTables.dims LhsTables.groupEnc LhsTables.memberEnc
  LhsTables.inverseEnc LhsTables.keyEnc LhsTables.locationLeaves LhsTables.transformLeaves
  LhsTables.rowLeaves LhsTables.scalarLeaves

/-- One aggregated RHS marginal feature. -/
structure RhsFeature where
  signature : ℕ
  residualDegree : ℕ
  radialDegree : ℕ
  weight : SignedNat
deriving Repr, Inhabited
attribute [nolint docBlame] RhsFeature.signature RhsFeature.residualDegree
  RhsFeature.radialDegree RhsFeature.weight

/-- One consecutive RHS group with fixed residual and radial degrees. -/
structure RhsGroup where
  start : ℕ
  size : ℕ
  residualDegree : ℕ
  radialDegree : ℕ
deriving Repr, Inhabited
attribute [nolint docBlame] RhsGroup.start RhsGroup.size RhsGroup.residualDegree
  RhsGroup.radialDegree

/-- Dimensions and fixed-width lanes of the sparse RHS certificate. -/
structure RhsDims where
  dimension : ℕ
  epsilonDenominator : ℕ
  degreeBound : ℕ
  signatureCount : ℕ
  featureCount : ℕ
  groupCount : ℕ
  transformCount : ℕ
  radialDimension : ℕ
  weightWidth : ℕ
  transformWidth : ℕ
  rowWidth : ℕ
  radialWidth : ℕ
deriving Repr, Inhabited
attribute [nolint docBlame] RhsDims.dimension RhsDims.epsilonDenominator RhsDims.degreeBound
  RhsDims.signatureCount RhsDims.featureCount RhsDims.groupCount RhsDims.transformCount
  RhsDims.radialDimension RhsDims.weightWidth RhsDims.transformWidth RhsDims.rowWidth
  RhsDims.radialWidth

/-- Serialize the RHS dimensions consumed by theorem-only modules. -/
def RhsDims.serialize (dims : RhsDims) : String :=
  String.intercalate " "
    ([dims.dimension, dims.epsilonDenominator, dims.degreeBound, dims.signatureCount,
      dims.featureCount, dims.groupCount, dims.transformCount, dims.radialDimension,
      dims.weightWidth, dims.transformWidth, dims.rowWidth, dims.radialWidth].map toString)

/-- Packed tables proposed to the first-order sparse-RHS kernel. -/
structure RhsTables where
  dims : RhsDims
  featureEnc : ℕ
  groupEnc : ℕ
  inverseEnc : ℕ
  keyEnc : ℕ
  sourceLocationLeaves : Array ℕ
  weightLeaves : Array ℕ
  locationLeaves : Array ℕ
  transformLeaves : Array ℕ
  rowLeaves : Array ℕ
  radialLeaves : Array ℕ
attribute [nolint docBlame] RhsTables.dims RhsTables.featureEnc RhsTables.groupEnc
  RhsTables.inverseEnc RhsTables.keyEnc RhsTables.sourceLocationLeaves RhsTables.weightLeaves
  RhsTables.locationLeaves RhsTables.transformLeaves RhsTables.rowLeaves RhsTables.radialLeaves

/-- Independently checkable partial lanes for the global RHS feature-weight identity. -/
structure RhsWeightCheckpoints where
  laneWidth : ℕ
  sourceBlockSize : ℕ
  expectedBlockSize : ℕ
  sourceBound : Array ℕ
  sourcePositive : Array ℕ
  sourceNegative : Array ℕ
  expectedBound : Array ℕ
  expectedPositive : Array ℕ
  expectedNegative : Array ℕ
attribute [nolint docBlame] RhsWeightCheckpoints.laneWidth RhsWeightCheckpoints.sourceBlockSize
  RhsWeightCheckpoints.expectedBlockSize RhsWeightCheckpoints.sourceBound
  RhsWeightCheckpoints.sourcePositive RhsWeightCheckpoints.sourceNegative
  RhsWeightCheckpoints.expectedBound RhsWeightCheckpoints.expectedPositive
  RhsWeightCheckpoints.expectedNegative

/-- Descending factorial computed natively by the untrusted generator. -/
def descendingFactorial (n count : ℕ) : ℕ := Id.run do
  let mut result := 1
  let mut current := n
  for _ in [0:count] do
    result := result * current
    current := current - 1
  return result

/-- Enlarged-simplex scalar used by the LHS, with all parameters explicit. -/
def lhsScalar (dimension epsilonDenominator degreeBound d aSum : ℕ) : ℕ :=
  (epsilonDenominator + 1) ^ (dimension + d) *
    epsilonDenominator ^ (dimension + 1 - d) * aSum ! *
    descendingFactorial (2 * dimension + 1) (dimension + 1 - d) *
    (degreeBound + 1) ! ^ 2

/-- Radial scalar used by the RHS, with all parameters explicit. -/
def rhsRadial (dimension epsilonDenominator q e : ℕ) : ℕ := Id.run do
  let mut inner := 0
  for m in [0:e+1] do
    inner := inner + e.choose m * 2 ^ (e - m) * (epsilonDenominator - 1) ^ m *
      m ! * descendingFactorial (2 * dimension + 1)
        (2 * dimension + 1 - (m + q))
  return epsilonDenominator ^ (2 * dimension + 1 - (q + e)) *
    (epsilonDenominator - 1) ^ q * inner

/-- Signed sum defining one group-by-signature moment transform entry. -/
def lhsTransform (input : SharedInput) (top : Array ℕ) (group : LhsGroup)
    (target : ℕ) : SignedNat := Id.run do
  let mut result := { positive := 0, negative := 0 : SignedNat }
  for offset in [0:group.members.size] do
    let label := input.labels[group.members[offset]!]!
    let moment := top[tri target label.signature]!
    result := result.addMagnitude label.negative (label.magnitude * moment)
  return result.normalize

/-- Generate all sparse LHS transform entries and contracted group rows. -/
def generateLhs (sharedDims : SharedDims) (input : SharedInput)
    (groups : Array LhsGroup) (keys : Array (ℕ × ℕ))
    (transformValues rows : Array SignedNat) : LhsTables := Id.run do
  let groupCount := groups.size
  let transformCount := keys.size
  let signatureCount := input.signatures.size
  let labelCount := input.labels.size
  let mut locations := Array.replicate (groupCount * signatureCount) 0
  for entry in [0:transformCount] do
    let (group, target) := keys[entry]!
    locations := locations.set! (group * signatureCount + target) (entry + 1)
  let scalarDimension := 2 * sharedDims.degreeBound + 1
  let scalarValues := Id.run do
    let mut values := #[]
    for d in [0:scalarDimension] do
      for aSum in [0:scalarDimension] do
        values := values.push
          (if d ≤ sharedDims.dimension ∧ aSum ≤ d then
            lhsScalar sharedDims.dimension sharedDims.epsilonDenominator
              sharedDims.degreeBound d aSum
          else 0)
    return values
  let transformEncoded := transformValues.map SignedNat.encode
  let rowEncoded := rows.map SignedNat.encode
  let transformWidth := roundWidth (widthFor transformEncoded)
  let rowWidth := roundWidth (widthFor rowEncoded)
  let scalarWidth := roundWidth (widthFor scalarValues)
  let members := groups.foldl (fun result group ↦ result ++ group.members) #[]
  let inverseFields := Id.run do
    let mut values := Array.replicate labelCount (0, 0)
    for group in [0:groupCount] do
      for offset in [0:groups[group]!.members.size] do
        let member := groups[group]!.members[offset]!
        values := values.set! member (group, offset)
    return values
  let groupFields := groups.map fun group ↦
    (group.start, group.size, group.distinguishedDegree, group.signatureDegree)
  return {
    dims := {
      dimension := sharedDims.dimension
      epsilonDenominator := sharedDims.epsilonDenominator
      degreeBound := sharedDims.degreeBound
      signatureCount, labelCount, groupCount, transformCount, scalarDimension
      transformWidth, rowWidth, scalarWidth
    }
    groupEnc := packGroupTable groupFields
    memberEnc := packTable 16 members
    inverseEnc := packPairTable inverseFields
    keyEnc := packPairTable keys
    locationLeaves := packLeaves 16 locations.size fun index ↦ locations[index]!
    transformLeaves := packLeaves transformWidth transformCount fun index ↦
      transformEncoded[index]!
    rowLeaves := packLeaves rowWidth groupCount fun index ↦ rowEncoded[index]!
    scalarLeaves := packLeaves scalarWidth scalarValues.size fun index ↦ scalarValues[index]!
  }

/-- Signed sum defining one RHS group-by-signature predecessor-moment transform entry. -/
def rhsTransform (predecessor : Array ℕ) (features : Array RhsFeature) (group : RhsGroup)
    (target : ℕ) : SignedNat := Id.run do
  let mut result := { positive := 0, negative := 0 : SignedNat }
  for offset in [0:group.size] do
    let feature := features[group.start + offset]!
    let moment := predecessor[tri target feature.signature]!
    result := {
      positive := result.positive + feature.weight.positive * moment
      negative := result.negative + feature.weight.negative * moment
    }
  return result.normalize

/-- Locate every bounded label/exponent pair in the proposed RHS feature table. -/
def rhsSourceLocations (sharedDims : SharedDims) (input : SharedInput)
    (features : Array RhsFeature) : Array ℕ := Id.run do
  let signatureCount := input.signatures.size
  let featureCount := features.size
  let encodings := input.signatures.map encodeSig
  let sums := input.signatures.map (·.foldl (· + ·) 0)
  let mut signatureMap : Std.HashMap ℕ ℕ := {}
  for signature in [0:encodings.size] do
    signatureMap := signatureMap.insert encodings[signature]! signature
  let featureKey (signature residual radial : ℕ) : String :=
    s!"{signature}:{residual}:{radial}"
  let mut featureMap : Std.HashMap String ℕ := {}
  for featureIndex in [0:features.size] do
    let feature := features[featureIndex]!
    featureMap := featureMap.insert
      (featureKey feature.signature feature.residualDegree feature.radialDegree) featureIndex
  let mut locations := #[]
  for labelIndex in [0:input.labels.size] do
    let label := input.labels[labelIndex]!
    let signature := input.signatures[label.signature]!
    for exponent in [0:sharedDims.degreeBound + 1] do
      let targetSignature := (signatureMap.get?
        (encodeSig (eraseOne signature exponent))).getD signatureCount
      let featureIndex := (featureMap.get? (featureKey targetSignature
        (sums[label.signature]! - exponent) (label.a + exponent + 1))).getD featureCount
      locations := locations.push
        (if exponent = 0 ∨ exponent ∈ signature then featureIndex else 0)
  return locations

/-- Generate bounded partial sums for a low-memory proof of the RHS weight identity. -/
def generateRhsWeightCheckpoints (sharedDims : SharedDims) (input : SharedInput)
    (features : Array RhsFeature) (sourceBlockSize expectedBlockSize : ℕ) :
    RhsWeightCheckpoints := Id.run do
  let sourceLocations := rhsSourceLocations sharedDims input features
  let mut radius := 0
  for labelIndex in [0:input.labels.size] do
    let label := input.labels[labelIndex]!
    let signature := input.signatures[label.signature]!
    for exponent in [0:sharedDims.degreeBound + 1] do
      if exponent = 0 ∨ exponent ∈ signature then
        radius := radius + label.magnitude * exponent ! * label.a ! *
          descendingFactorial (sharedDims.degreeBound + 1)
            (sharedDims.degreeBound - (label.a + exponent))
  let expectedBound := features.foldl
    (fun bound feature ↦ bound.max (feature.weight.positive + feature.weight.negative)) 0
  let laneWidth := roundWidth (widthFor #[radius + expectedBound])
  let sourceBlockCount := input.labels.size / sourceBlockSize + 1
  let mut sourceBound := #[]
  let mut sourcePositive := #[]
  let mut sourceNegative := #[]
  for block in [0:sourceBlockCount] do
    let lower := block * sourceBlockSize
    let upper := min input.labels.size (lower + sourceBlockSize)
    let mut lanesBound := 0
    let mut lanesPositive := 0
    let mut lanesNegative := 0
    for labelIndex in [lower:upper] do
      let label := input.labels[labelIndex]!
      let signature := input.signatures[label.signature]!
      for exponent in [0:sharedDims.degreeBound + 1] do
        if exponent = 0 ∨ exponent ∈ signature then
          let magnitude := label.magnitude * exponent ! * label.a ! *
            descendingFactorial (sharedDims.degreeBound + 1)
              (sharedDims.degreeBound - (label.a + exponent))
          let location := sourceLocations[labelIndex * (sharedDims.degreeBound + 1) + exponent]!
          let shifted := magnitude <<< (laneWidth * location)
          lanesBound := lanesBound + magnitude
          if label.negative then lanesNegative := lanesNegative + shifted
          else lanesPositive := lanesPositive + shifted
    sourceBound := sourceBound.push lanesBound
    sourcePositive := sourcePositive.push lanesPositive
    sourceNegative := sourceNegative.push lanesNegative
  let expectedBlockCount := features.size / expectedBlockSize + 1
  let mut expectedBounds := #[]
  let mut expectedPositive := #[]
  let mut expectedNegative := #[]
  for block in [0:expectedBlockCount] do
    let lower := block * expectedBlockSize
    let upper := min features.size (lower + expectedBlockSize)
    let mut lanesBound := 0
    let mut lanesPositive := 0
    let mut lanesNegative := 0
    for featureIndex in [lower:upper] do
      let weight := features[featureIndex]!
      lanesBound := lanesBound.max (weight.weight.positive + weight.weight.negative)
      lanesPositive := lanesPositive + (weight.weight.positive <<< (laneWidth * featureIndex))
      lanesNegative := lanesNegative + (weight.weight.negative <<< (laneWidth * featureIndex))
    expectedBounds := expectedBounds.push lanesBound
    expectedPositive := expectedPositive.push lanesPositive
    expectedNegative := expectedNegative.push lanesNegative
  return {
    laneWidth, sourceBlockSize, expectedBlockSize, sourceBound,
    sourcePositive, sourceNegative, expectedBound := expectedBounds,
    expectedPositive, expectedNegative
  }

/-- Generate all sparse RHS transform entries and contracted group rows. -/
def generateRhs (sharedDims : SharedDims) (input : SharedInput)
    (features : Array RhsFeature) (groups : Array RhsGroup)
    (keys : Array (ℕ × ℕ)) (transformValues rows : Array SignedNat) : RhsTables := Id.run do
  let featureCount := features.size
  let groupCount := groups.size
  let transformCount := keys.size
  let signatureCount := input.signatures.size
  let sourceLocations := rhsSourceLocations sharedDims input features
  let mut locations := Array.replicate (groupCount * signatureCount) 0
  for entry in [0:transformCount] do
    let (group, target) := keys[entry]!
    locations := locations.set! (group * signatureCount + target) (entry + 1)
  let radialDimension := 2 * sharedDims.dimension + 2
  let radialValues := Id.run do
    let mut values := #[]
    for q in [0:radialDimension] do
      for e in [0:radialDimension] do
        values := values.push
          (if sharedDims.dimension - 1 ≤ q ∧ q + e ≤ 2 * sharedDims.dimension + 1 then
            rhsRadial sharedDims.dimension sharedDims.epsilonDenominator q e
          else 0)
    return values
  let weightsEncoded := features.map fun feature ↦ feature.weight.encode
  let transformEncoded := transformValues.map SignedNat.encode
  let rowEncoded := rows.map SignedNat.encode
  let weightWidth := roundWidth (widthFor weightsEncoded)
  let transformWidth := roundWidth (widthFor transformEncoded)
  let rowWidth := roundWidth (widthFor rowEncoded)
  let radialWidth := roundWidth (widthFor radialValues)
  let featureFields := features.map fun feature ↦
    feature.signature + (feature.residualDegree <<< 9) + (feature.radialDegree <<< 15)
  let inverseFields := Id.run do
    let mut values := Array.replicate featureCount (0, 0)
    for group in [0:groupCount] do
      for offset in [0:groups[group]!.size] do
        values := values.set! (groups[group]!.start + offset) (group, offset)
    return values
  let groupFields := groups.map fun group ↦
    (group.start, group.size, group.residualDegree, group.radialDegree)
  return {
    dims := {
      dimension := sharedDims.dimension
      epsilonDenominator := sharedDims.epsilonDenominator
      degreeBound := sharedDims.degreeBound
      signatureCount, featureCount, groupCount, transformCount, radialDimension
      weightWidth, transformWidth, rowWidth, radialWidth
    }
    featureEnc := packTable 32 featureFields
    groupEnc := packGroupTable groupFields
    inverseEnc := packPairTable inverseFields
    keyEnc := packPairTable keys
    sourceLocationLeaves := packLeaves 16 sourceLocations.size fun index ↦
      sourceLocations[index]!
    weightLeaves := packLeaves weightWidth featureCount fun index ↦ weightsEncoded[index]!
    locationLeaves := packLeaves 16 locations.size fun index ↦ locations[index]!
    transformLeaves := packLeaves transformWidth transformCount fun index ↦
      transformEncoded[index]!
    rowLeaves := packLeaves rowWidth groupCount fun index ↦ rowEncoded[index]!
    radialLeaves := packLeaves radialWidth radialValues.size fun index ↦ radialValues[index]!
  }

end cert246Data.SparseGen
