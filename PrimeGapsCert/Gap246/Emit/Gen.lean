/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Nat.Choose.Basic

/-! # Untrusted generator for the packed factorial-moment certificate

The generator computes powers of the identity-free erase transition and packs them into
fixed-width leaves.  Every generated value is subsequently checked by the kernel.
-/

@[expose] public section

namespace cert246Data.Gen

/-- Generator input: requested dimension and the erase-closed signature family. -/
structure Input where
  dimension : ℕ
  signatures : Array (Array ℕ)
deriving Repr
attribute [nolint docBlame] Input.dimension Input.signatures

/-- One labelled basis coefficient needed by both sparse quadratic-form kernels. -/
structure Label where
  a : ℕ
  signature : ℕ
  negative : Bool
  magnitude : ℕ
deriving Repr, Inhabited
attribute [nolint docBlame] Label.a Label.signature Label.negative Label.magnitude

/-- Generator input shared by the moment and sparse quadratic-form certificates. -/
structure SharedInput where
  dimension : ℕ
  signatures : Array (Array ℕ)
  labels : Array Label
deriving Repr
attribute [nolint docBlame] SharedInput.dimension SharedInput.signatures SharedInput.labels

/-- Dimensions of the dependency-isolated shared certificate data. -/
structure SharedDims where
  dimension : ℕ
  epsilonDenominator : ℕ
  signatureCount : ℕ
  labelCount : ℕ
  maxCount : ℕ
  degreeBound : ℕ
  factorialCount : ℕ
  coefficientWidth : ℕ
deriving Repr, Inhabited
attribute [nolint docBlame] SharedDims.dimension SharedDims.epsilonDenominator
  SharedDims.signatureCount SharedDims.labelCount SharedDims.maxCount SharedDims.degreeBound
  SharedDims.factorialCount SharedDims.coefficientWidth

/-- Space-separated dimension cache for the shared certificate data. -/
def SharedDims.serialize (dims : SharedDims) : String :=
  String.intercalate " "
    ([dims.dimension, dims.epsilonDenominator, dims.signatureCount, dims.labelCount, dims.maxCount,
      dims.degreeBound, dims.factorialCount, dims.coefficientWidth].map toString)

/-- Dimensions and field widths needed by the raw theorem emitter. -/
structure Dims where
  dimension : ℕ
  signatureCount : ℕ
  maxCount : ℕ
  maxLevel : ℕ
  factorialCount : ℕ
  nilWidth : ℕ
  outputWidth : ℕ
  pairWidth : ℕ
deriving Repr, Inhabited
attribute [nolint docBlame] Dims.dimension Dims.signatureCount Dims.maxCount Dims.maxLevel
  Dims.factorialCount Dims.nilWidth Dims.outputWidth Dims.pairWidth

/-- Space-separated dimension cache used by theorem-only modules. -/
def Dims.serialize (dims : Dims) : String :=
  String.intercalate " "
    ([dims.dimension, dims.signatureCount, dims.maxCount, dims.maxLevel,
      dims.factorialCount, dims.nilWidth, dims.outputWidth, dims.pairWidth].map toString)

/-- Packed data proposed to the kernel. -/
structure Tables where
  dims : Dims
  sigEnc : ℕ
  eraseEnc : ℕ
  factT : ℕ
  nilLeaves : Array ℕ
  levelWidths : Array ℕ
  levelLeaves : Array (Array ℕ)
  pairLeaves : Array ℕ
  top : Array ℕ
  predecessor : Array ℕ
attribute [nolint docBlame] Tables.dims Tables.sigEnc Tables.eraseEnc Tables.factT Tables.nilLeaves
  Tables.levelWidths Tables.levelLeaves Tables.pairLeaves Tables.top Tables.predecessor

/-- Packed inputs shared by moments, LHS, and RHS, without any evaluator output. -/
structure SharedTables where
  dims : SharedDims
  sigEnc : ℕ
  eraseEnc : ℕ
  eraseTargetLeaves : Array ℕ
  labelEnc : ℕ
  coefficientLeaves : Array ℕ
  factT : ℕ
attribute [nolint docBlame] SharedTables.dims SharedTables.sigEnc SharedTables.eraseEnc
  SharedTables.eraseTargetLeaves SharedTables.labelEnc SharedTables.coefficientLeaves
  SharedTables.factT

/-- Field width of the packed factorial table. -/
def factorialWidth : ℕ := 256

/-- Field width of every packed index table. -/
def indexWidth : ℕ := 16

/-- Pack fixed-width fields into one natural. -/
partial def packTable (width : ℕ) (values : Array ℕ) : ℕ :=
  go 0 values.size
where
  /-- Pack `[lo,hi)`. -/
  go (lo hi : ℕ) : ℕ :=
    if hi ≤ lo then 0
    else if hi = lo + 1 then values[lo]!
    else
      let mid := (lo + hi) / 2
      go lo mid + (go mid hi <<< (width * (mid - lo)))

/-- Least positive field width for an array. -/
def widthFor (values : Array ℕ) : ℕ :=
  values.foldl (fun width value ↦ width.max value.log2.succ) 1

/-- Round a positive bit width up to a 64-bit boundary. -/
def roundWidth (width : ℕ) : ℕ := 64 * ((width + 63) / 64)

/-- Chunk shift targeting leaves of at most 16 Kbit. -/
def chunkShift (width : ℕ) : ℕ := Id.run do
  let mut shift := 0
  while (1 <<< (shift + 1)) * width ≤ 16384 ∧ shift < 14 do
    shift := shift + 1
  return shift

/-- Chunk shift of one 4x-regrouped packed tree: four 16-Kbit cache leaves per stored leaf. -/
def levelChunkShift (width : ℕ) : ℕ := chunkShift width + 2

/-- Pack cached leaves four to a stored leaf at `levelChunkShift width`. -/
def regroupLevelLeaves (width : ℕ) (leaves : Array ℕ) : Array ℕ := Id.run do
  let per := 1 <<< chunkShift width
  let mut out := #[]
  let mut start := 0
  while start < leaves.size do
    let mut acc := 0
    for j in [0:4] do
      if start + j < leaves.size then
        acc := acc + (leaves[start + j]! <<< (j * (width * per)))
    out := out.push acc
    start := start + 4
  return out

/-- Pack `entries` values supplied by index into independent leaves. -/
def packLeaves (width entries : ℕ) (value : ℕ → ℕ) : Array ℕ := Id.run do
  let per := 1 <<< chunkShift width
  let count := ((entries + per - 1) / per).max 1
  let mut leaves := #[]
  for leaf in [0:count] do
    let start := leaf * per
    let stop := min entries (start + per)
    let fields := (Array.range (stop - start)).map fun i ↦ value (start + i)
    leaves := leaves.push (packTable width fields)
  return leaves

/-- Signature encoding: count in the low nibble, followed by halved parts. -/
def encodeSig (signature : Array ℕ) : ℕ :=
  signature.size + (signature.foldr (fun part acc ↦ (acc <<< 4) + part / 2) 0 <<< 4)

/-- Index of an encoding in the erase-closed signature list. -/
def sigIndex (encodings : Array ℕ) (encoding : ℕ) : ℕ :=
  (encodings.findIdx? (· = encoding)).getD encodings.size

/-- Distinct parts of a sorted signature. -/
def distinctParts (signature : Array ℕ) : Array ℕ :=
  signature.foldl (fun out part ↦ if out.back? = some part then out else out.push part) #[]

/-- Remove the first occurrence of `part`. -/
def eraseOne (signature : Array ℕ) (part : ℕ) : Array ℕ :=
  match signature.findIdx? (· = part) with
  | some index => signature.eraseIdx! index
  | none => signature

/-- Four padded genuine erase descriptors followed by the identity descriptor. -/
def eraseSlots (signatures : Array (Array ℕ)) (encodings : Array ℕ) (s : ℕ) : Array ℕ :=
  Id.run do
    let mut out := #[]
    for part in distinctParts signatures[s]! do
      let target := sigIndex encodings (encodeSig (eraseOne signatures[s]! part))
      out := out.push (1 + ((part / 2) <<< 1) + (target <<< 5))
    while out.size < 4 do
      out := out.push 0
    return out.push (1 + (s <<< 5))

/-- Factorials `0!` through `(count-1)!`. -/
def factorials (count : ℕ) : Array ℕ := Id.run do
  let mut out := #[1]
  for i in [1:count] do
    out := out.push (out.back! * i)
  return out

/-- Generate only the dependency-isolated signature, label, coefficient, and factorial data. -/
def generateShared (epsilonDenominator : ℕ) (input : SharedInput) : SharedTables := Id.run do
  let signatures := input.signatures
  let signatureCount := signatures.size
  let labelCount := input.labels.size
  let encodings := signatures.map encodeSig
  let slots := (Array.range signatureCount).map (eraseSlots signatures encodings)
  let sums := signatures.map (·.foldl (· + ·) 0)
  let degreeBound := input.labels.foldl
    (fun bound label ↦ bound.max (label.a + sums[label.signature]!)) 0
  let eraseTargets := Id.run do
    let mut targets := #[]
    for signature in [0:signatureCount] do
      for exponent in [0:degreeBound + 1] do
        targets := targets.push (sigIndex encodings
          (encodeSig (eraseOne signatures[signature]! exponent)))
    return targets
  let labelFields := input.labels.map fun label ↦
    label.a + (label.signature <<< 5) + (sums[label.signature]! <<< 14) +
      ((if label.negative then 1 else 0) <<< 19)
  let magnitudes := input.labels.map (·.magnitude)
  let coefficientWidth := roundWidth (widthFor magnitudes)
  let maxCount := signatures.foldl (fun count signature ↦ count.max signature.size) 0
  let maxPart := signatures.foldl (fun part signature ↦ part.max (signature.back?.getD 0)) 0
  let factorialCount := 2 * maxPart + 1
  return {
    dims := {
      dimension := input.dimension
      epsilonDenominator
      signatureCount, labelCount, maxCount, degreeBound, factorialCount, coefficientWidth
    }
    sigEnc := packTable 64 encodings
    eraseEnc := packTable indexWidth slots.flatten
    eraseTargetLeaves := packLeaves indexWidth eraseTargets.size fun index ↦
      eraseTargets[index]!
    labelEnc := packTable 32 labelFields
    coefficientLeaves := packLeaves coefficientWidth labelCount fun index ↦ magnitudes[index]!
    factT := packTable factorialWidth (factorials factorialCount)
  }

/-- Triangular unordered-pair index. -/
def tri (s t : ℕ) : ℕ :=
  if s ≤ t then t * (t + 1) / 2 + s else s * (s + 1) / 2 + t

/-- Nilpotent base: one only for the two empty signatures. -/
def nilBase (signatureCount : ℕ) (encodings : Array ℕ) : Array ℕ := Id.run do
  let mut out := #[]
  for t in [0:signatureCount] do
    for s in [0:t+1] do
      out := out.push (if encodings[s]! = 0 ∧ encodings[t]! = 0 then 1 else 0)
  return out

/-- One native identity-free transition. -/
def nilStep (signatureCount level : ℕ) (signatures slots : Array (Array ℕ))
    (facts previous : Array ℕ) : Array ℕ := Id.run do
  let mut out := #[]
  for t in [0:signatureCount] do
    for s in [0:t+1] do
      let count := signatures[s]!.size + signatures[t]!.size
      if level ≤ count ∧ count ≤ 2 * level then
        let mut acc := 0
        for j₁ in [0:4] do
          let field₁ := slots[s]![j₁]!
          if field₁ % 2 = 1 then
            for j₂ in [0:5] do
              let field₂ := slots[t]![j₂]!
              if field₂ % 2 = 1 then
                let p₁ := (field₁ >>> 1) % 16
                let p₂ := (field₂ >>> 1) % 16
                let target₁ := (field₁ >>> 5) % 512
                let target₂ := (field₂ >>> 5) % 512
                acc := acc + facts[2 * (p₁ + p₂)]! * previous[tri target₁ target₂]!
        for j₂ in [0:4] do
          let field₂ := slots[t]![j₂]!
          if field₂ % 2 = 1 then
            let p₂ := (field₂ >>> 1) % 16
            let target₂ := (field₂ >>> 5) % 512
            acc := acc + facts[2 * p₂]! * previous[tri s target₂]!
        out := out.push acc
      else
        out := out.push 0
  return out

/-- Binomial coefficients `dimension.choose level` for every level of the ladder. -/
def binomials (dimension maxLevel : ℕ) : Array ℕ :=
  (Array.range (maxLevel + 1)).map dimension.choose

/-- Reconstruct one ordinary moment from nilpotent powers and the level binomials. -/
def reconstruct (binomials : Array ℕ) (maxLevel : ℕ) (levels : Array (Array ℕ))
    (signatures : Array (Array ℕ)) (s t : ℕ) : ℕ := Id.run do
  let count := signatures[s]!.size + signatures[t]!.size
  let entry := tri s t
  let mut out := 0
  for level in [0:min count maxLevel + 1] do
    if count ≤ 2 * level then
      out := out + binomials[level]! * levels[level]![entry]!
  return out

/-- Generate all proposed tables. -/
def generate (input : Input) : Tables := Id.run do
  let dimension := input.dimension
  let signatures := input.signatures
  let signatureCount := signatures.size
  let encodings := signatures.map encodeSig
  let slots := (Array.range signatureCount).map (eraseSlots signatures encodings)
  let maxCount := signatures.foldl (fun count signature ↦ count.max signature.size) 0
  let maxLevel := 2 * maxCount
  let maxPart := signatures.foldl (fun part signature ↦ part.max (signature.back?.getD 0)) 0
  let factorialCount := 2 * maxPart + 1
  let facts := factorials factorialCount
  let triCount := signatureCount * (signatureCount + 1) / 2
  let mut levels := #[nilBase signatureCount encodings]
  for level in [1:maxLevel+1] do
    levels := levels.push (nilStep signatureCount level signatures slots facts levels.back!)
  let topBinomials := binomials dimension maxLevel
  let predecessorBinomials := binomials (dimension - 1) maxLevel
  let top := Id.run do
    let mut out := #[]
    for t in [0:signatureCount] do
      for s in [0:t+1] do
        out := out.push (reconstruct topBinomials maxLevel levels signatures s t)
    return out
  let predecessor := Id.run do
    let mut out := #[]
    for t in [0:signatureCount] do
      for s in [0:t+1] do
        out := out.push (reconstruct predecessorBinomials maxLevel levels signatures s t)
    return out
  let outputWidth := roundWidth (max (widthFor top) (widthFor predecessor))
  let pairWidth := 2 * outputWidth
  let nilWidth := roundWidth (levels.foldl (fun width level ↦ width.max (widthFor level)) 1)
  let nilEntries := (maxLevel + 1) * triCount
  let nilLeaves := packLeaves nilWidth nilEntries fun index ↦
    levels[index / triCount]![index % triCount]!
  let levelWidths := levels.map fun level ↦ roundWidth (widthFor level)
  let levelLeaves := levels.mapIdx fun index level ↦
    packLeaves levelWidths[index]! triCount fun entry ↦ level[entry]!
  let pairLeaves := packLeaves pairWidth triCount fun index ↦
    predecessor[index]! + (top[index]! <<< outputWidth)
  return {
    dims := {
      dimension, signatureCount, maxCount, maxLevel, factorialCount
      nilWidth, outputWidth, pairWidth
    }
    sigEnc := packTable 64 encodings
    eraseEnc := packTable 16 slots.flatten
    factT := packTable 256 facts
    nilLeaves, levelWidths, levelLeaves, pairLeaves, top, predecessor
  }

end cert246Data.Gen
