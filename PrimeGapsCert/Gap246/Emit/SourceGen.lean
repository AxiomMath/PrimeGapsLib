/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Sparse.Gen

/-! # Single-source generator for the 246 certificate

This module derives every numerical input used by the packed certificate from the original
labelled coefficient file.  The computations are untrusted: the resulting declarations are
subsequently checked by the small kernels in `PrimeGapsCert.Gap246.Kernel`.
-/

@[expose] public section

open scoped Nat

namespace cert246Data.SourceGen

open cert246Data.Gen cert246Data.SparseGen

/-- The sole external data file for the 246 certificate. -/
def certificateFile : System.FilePath :=
  ".." / "k50e25d25n1295.json"

/-- Fixed parameters encoded in the certificate filename. -/
def dimension : ℕ := 50

/-- Denominator of the epsilon parameter encoded in the certificate filename. -/
def epsilonDenominator : ℕ := 25

/-- One entry in the original labelled polynomial. -/
structure RawLabel where
  a : ℕ
  signature : Array ℕ
  coefficient : ℤ
deriving Repr
attribute [nolint docBlame] RawLabel.a RawLabel.signature RawLabel.coefficient

/-- Data shared by the moment, LHS, and RHS generators. -/
structure Base where
  dims : SharedDims
  input : SharedInput
  top : Array ℕ
  predecessor : Array ℕ
attribute [nolint docBlame] Base.dims Base.input Base.top Base.predecessor

/-- Sparse LHS inputs derived from the original labelled polynomial. -/
structure LhsSource where
  groups : Array LhsGroup
  keys : Array (ℕ × ℕ)
  transforms : Array SignedNat
  rows : Array SignedNat
attribute [nolint docBlame] LhsSource.groups LhsSource.keys LhsSource.transforms LhsSource.rows

/-- Sparse RHS inputs derived from the original labelled polynomial. -/
structure RhsSource where
  features : Array RhsFeature
  groups : Array RhsGroup
  keys : Array (ℕ × ℕ)
  transforms : Array SignedNat
  rows : Array SignedNat
attribute [nolint docBlame] RhsSource.features RhsSource.groups RhsSource.keys
  RhsSource.transforms RhsSource.rows

/-- Parse and canonically sort the signatures in the original certificate. -/
def parseRaw (json : Lean.Json) : Except String (Array RawLabel) := do
  let source ← json.getArr?
  source.mapM fun entry ↦ do
    let fields ← entry.getArr?
    let signatureSource ← fields[1]!.getArr?
    let signature ← signatureSource.mapM fun part ↦
      return (← part.getInt?).toNat
    return {
      a := (← fields[0]!.getInt?).toNat
      signature := signature.qsort (fun left right ↦ left < right)
      coefficient := ← fields[2]!.getInt?
    }

/-- Read the original certificate. -/
def readRaw (source : System.FilePath) : IO (Array RawLabel) := do
  let certificatePath := (source.parent.getD ".") / certificateFile
  unless ← certificatePath.pathExists do
    throw <| IO.userError s!"cert246Data: no certificate at {certificatePath}"
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile certificatePath))
  IO.ofExcept (parseRaw json)

/-- Extract the first-occurrence-ordered erase-closed signature family and labelled terms. -/
def sharedInput (raw : Array RawLabel) : Except String SharedInput := do
  let mut signatures := #[]
  let mut encodings := #[]
  for label in raw do
    let encoding := encodeSig label.signature
    unless encodings.contains encoding do
      signatures := signatures.push label.signature
      encodings := encodings.push encoding
  for signature in signatures do
    for exponent in distinctParts signature do
      unless encodings.contains (encodeSig (eraseOne signature exponent)) do
        throw s!"signature family is not closed under erasure: {signature}"
  let mut labels := #[]
  for label in raw do
    let signature := sigIndex encodings (encodeSig label.signature)
    if signature = signatures.size then
      throw "internal signature lookup failure"
    labels := labels.push {
      a := label.a
      signature
      negative := label.coefficient < 0
      magnitude := label.coefficient.natAbs
    }
  return { dimension, signatures, labels }

/-- Add two signed accumulators without prematurely normalizing either lane. -/
def addSigned (left right : SignedNat) : SignedNat :=
  { positive := left.positive + right.positive, negative := left.negative + right.negative }

/-- Generate the lexicographically ordered LHS degree groups. -/
def lhsGroups (base : Base) : Array LhsGroup := Id.run do
  let degreeBound := base.dims.degreeBound
  let sums := base.input.signatures.map (fun signature ↦ signature.foldl (· + ·) 0)
  let mut groups := #[]
  let mut start := 0
  for a in [0:degreeBound + 1] do
    for signatureDegree in [0:degreeBound + 1] do
      let mut members := #[]
      for index in [0:base.input.labels.size] do
        let label := base.input.labels[index]!
        if label.a = a && sums[label.signature]! = signatureDegree then
          members := members.push index
      if !members.isEmpty then
        groups := groups.push {
          start
          size := members.size
          distinguishedDegree := a
          signatureDegree
          members
        }
        start := start + members.size
  return groups

/-- Support keys needed by the sparse LHS contractions. -/
def lhsKeys (base : Base) (groups : Array LhsGroup) : Array (ℕ × ℕ) := Id.run do
  let signatureCount := base.input.signatures.size
  let mut targets := Array.replicate (groups.size * signatureCount) false
  for left in [0:groups.size] do
    for right in [left:groups.size] do
      let destination := if groups[left]!.size ≤ groups[right]!.size then right else left
      let source := if groups[left]!.size ≤ groups[right]!.size then left else right
      for member in groups[source]!.members do
        let signature := base.input.labels[member]!.signature
        targets := targets.set! (destination * signatureCount + signature) true
  let mut keys := #[]
  for group in [0:groups.size] do
    for signature in [0:signatureCount] do
      if targets[group * signatureCount + signature]! then
        keys := keys.push (group, signature)
  return keys

/-- Locate each sparse transform key in a dense temporary index. -/
def transformLocations (groupCount signatureCount : ℕ) (keys : Array (ℕ × ℕ)) :
    Array ℕ := Id.run do
  let mut locations := Array.replicate (groupCount * signatureCount) 0
  for index in [0:keys.size] do
    let (group, signature) := keys[index]!
    locations := locations.set! (group * signatureCount + signature) (index + 1)
  return locations

/-- Derive every sparse LHS source array. -/
def generateLhsSource (base : Base) : LhsSource := Id.run do
  let groups := lhsGroups base
  let degreeBound := base.dims.degreeBound
  let keys := lhsKeys base groups
  let transforms := keys.map fun (group, target) ↦
    lhsTransform base.input base.top groups[group]! target
  let signatureCount := base.input.signatures.size
  let locations := transformLocations groups.size signatureCount keys
  let mut rows := Array.replicate groups.size { positive := 0, negative := 0 : SignedNat }
  for left in [0:groups.size] do
    for right in [left:groups.size] do
      let sourceIndex := if groups[left]!.size ≤ groups[right]!.size then left else right
      let destinationIndex := if groups[left]!.size ≤ groups[right]!.size then right else left
      let mut contraction := { positive := 0, negative := 0 : SignedNat }
      for member in groups[sourceIndex]!.members do
        let label := base.input.labels[member]!
        let location := locations[destinationIndex * signatureCount + label.signature]!
        let value := transforms[location - 1]!
        contraction := contraction.addProduct value label.negative label.magnitude
      let normalized := contraction.normalize
      let distinguishedDegree := groups[left]!.distinguishedDegree +
        groups[right]!.distinguishedDegree
      let totalDegree := distinguishedDegree + groups[left]!.signatureDegree +
        groups[right]!.signatureDegree
      let multiplicity := if left = right then 1 else 2
      let factor := multiplicity * lhsScalar dimension epsilonDenominator
        degreeBound totalDegree distinguishedDegree
      rows := rows.set! left (addSigned rows[left]! (normalized.scale factor))
  return { groups, keys, transforms, rows := rows.map SignedNat.normalize }

/-- Cleared marginal coefficient attached to one source label and erased exponent. -/
def marginalFactor (degreeBound a exponent : ℕ) : ℕ :=
  exponent ! * a ! *
    descendingFactorial (degreeBound + 1) (degreeBound - (a + exponent))

/-- Derive and sort the aggregated RHS features. -/
def rhsFeatures (base : Base) : Array RhsFeature := Id.run do
  let signatureCount := base.input.signatures.size
  let radialCount := base.dims.degreeBound + 2
  let encodings := base.input.signatures.map encodeSig
  let sums := base.input.signatures.map (fun signature ↦ signature.foldl (· + ·) 0)
  let mut weights := Array.replicate
    ((base.dims.degreeBound + 1) * radialCount * signatureCount)
    { positive := 0, negative := 0 : SignedNat }
  for labelIndex in [0:base.input.labels.size] do
    let label := base.input.labels[labelIndex]!
    let signature := base.input.signatures[label.signature]!
    let exponents := #[0] ++ distinctParts signature
    for exponent in exponents do
      let target := sigIndex encodings (encodeSig (eraseOne signature exponent))
      let residual := sums[label.signature]! - exponent
      let radial := label.a + exponent + 1
      let index := (residual * radialCount + radial) * signatureCount + target
      let magnitude := label.magnitude * marginalFactor base.dims.degreeBound
        label.a exponent
      weights := weights.set! index (weights[index]!.addMagnitude label.negative magnitude)
  let mut features := #[]
  for residual in [0:base.dims.degreeBound + 1] do
    for radial in [0:radialCount] do
      for signature in [0:signatureCount] do
        let weight := weights[(residual * radialCount + radial) * signatureCount + signature]!
          |>.normalize
        if weight.positive ≠ 0 || weight.negative ≠ 0 then
          features := features.push {
            signature
            residualDegree := residual
            radialDegree := radial
            weight
          }
  return features

/-- Consecutive RHS groups with fixed residual and radial degrees. -/
def rhsGroups (features : Array RhsFeature) : Array RhsGroup := Id.run do
  let mut groups := #[]
  for index in [0:features.size] do
    let feature := features[index]!
    match groups.back? with
    | some group =>
        if group.residualDegree = feature.residualDegree &&
            group.radialDegree = feature.radialDegree then
          groups := groups.set! (groups.size - 1) { group with size := group.size + 1 }
        else
          groups := groups.push {
            start := index
            size := 1
            residualDegree := feature.residualDegree
            radialDegree := feature.radialDegree
          }
    | none =>
        groups := groups.push {
          start := index
          size := 1
          residualDegree := feature.residualDegree
          radialDegree := feature.radialDegree
        }
  return groups

/-- Support keys needed by the sparse RHS contractions. -/
def rhsKeys (signatureCount : ℕ) (features : Array RhsFeature)
    (groups : Array RhsGroup) : Array (ℕ × ℕ) := Id.run do
  let mut targets := Array.replicate (groups.size * signatureCount) false
  for left in [0:groups.size] do
    for right in [left:groups.size] do
      let destination := if groups[left]!.size ≤ groups[right]!.size then right else left
      let source := if groups[left]!.size ≤ groups[right]!.size then left else right
      for offset in [0:groups[source]!.size] do
        let signature := features[groups[source]!.start + offset]!.signature
        targets := targets.set! (destination * signatureCount + signature) true
  let mut keys := #[]
  for group in [0:groups.size] do
    for signature in [0:signatureCount] do
      if targets[group * signatureCount + signature]! then
        keys := keys.push (group, signature)
  return keys

/-- Multiply two normalized signed values and add the product to an accumulator. -/
def addSignedProduct (accumulator left right : SignedNat) : SignedNat :=
  if left.negative = 0 then accumulator.addProduct right false left.positive
  else accumulator.addProduct right true left.negative

/-- Radial degrees of one unordered RHS group pair. -/
def rhsRadialKey (groups : Array RhsGroup) (left right : ℕ) : ℕ × ℕ :=
  (dimension - 1 + groups[left]!.residualDegree + groups[right]!.residualDegree,
    groups[left]!.radialDegree + groups[right]!.radialDegree)

/-- The radial scalar of every degree pair reached by the RHS contraction, one entry per pair. -/
def rhsRadialTable (groups : Array RhsGroup) : Std.HashMap (ℕ × ℕ) ℕ := Id.run do
  let mut table := {}
  for left in [0:groups.size] do
    for right in [left:groups.size] do
      let key := rhsRadialKey groups left right
      unless table.contains key do
        table := table.insert key (rhsRadial dimension epsilonDenominator key.1 key.2)
  return table

/-- Derive every sparse RHS source array. -/
def generateRhsSource (base : Base) : RhsSource := Id.run do
  let features := rhsFeatures base
  let groups := rhsGroups features
  let signatureCount := base.input.signatures.size
  let keys := rhsKeys signatureCount features groups
  let transforms := keys.map fun (group, target) ↦
    rhsTransform base.predecessor features groups[group]! target
  let locations := transformLocations groups.size signatureCount keys
  let radials := rhsRadialTable groups
  let mut rows := Array.replicate groups.size { positive := 0, negative := 0 : SignedNat }
  for left in [0:groups.size] do
    for right in [left:groups.size] do
      let sourceIndex := if groups[left]!.size ≤ groups[right]!.size then left else right
      let destinationIndex := if groups[left]!.size ≤ groups[right]!.size then right else left
      let mut contraction := { positive := 0, negative := 0 : SignedNat }
      for offset in [0:groups[sourceIndex]!.size] do
        let feature := features[groups[sourceIndex]!.start + offset]!
        let location := locations[destinationIndex * signatureCount + feature.signature]!
        contraction := addSignedProduct contraction feature.weight transforms[location - 1]!
      let normalized := contraction.normalize
      let multiplicity := if left = right then 1 else 2
      let factor := multiplicity * radials[rhsRadialKey groups left right]!
      rows := rows.set! left (addSigned rows[left]! (normalized.scale factor))
  return { features, groups, keys, transforms, rows := rows.map SignedNat.normalize }

/-- Generate all packed sparse LHS tables from the sole external certificate. -/
def generateLhsTables (base : Base) : LhsTables :=
  let source := generateLhsSource base
  generateLhs base.dims base.input source.groups
    source.keys source.transforms source.rows

end cert246Data.SourceGen
