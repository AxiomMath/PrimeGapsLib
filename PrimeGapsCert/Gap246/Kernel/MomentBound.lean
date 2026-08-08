/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Nat.Choose.Basic
public import PrimeGapsCert.Gap246.Kernel.Moments

/-! # First-order predecessor-moment bounds

This module is deliberately separate from the shared moment kernel.  Only the final
certificate imports it, so changing the bound check does not invalidate the ladder,
LHS, or RHS numerical modules.
-/

@[expose] public section

namespace cert246Data

/-- The two requested moments reconstructed from independently packed nilpotent levels. -/
noncomputable def nilMomentPairLevels (outWidth dimension maxLevel sigEnc : ℕ)
    (shifts pmasks widths masks : Lean.RArray ℕ)
    (trees : Lean.RArray (Lean.RArray ℕ)) (s t : ℕ) : ℕ :=
  let count := Nat.add (sigCount (sigField sigEnc s)) (sigCount (sigField sigEnc t))
  let levels := Nat.succ (Nat.min count maxLevel)
  Nat.rec (motive := fun _ ↦ ℕ → ℕ → ℕ)
    (fun _ accumulator ↦ accumulator)
    (fun _ inductionHypothesis level accumulator ↦
      inductionHypothesis (Nat.succ level)
        (Bool.rec accumulator
          (Nat.add accumulator (Nat.mul
            (nilLevelAt shifts pmasks widths masks trees level (triIdx s t))
            (Nat.add (Nat.choose (Nat.sub dimension 1) level)
              (Nat.shiftLeft (Nat.choose dimension level) outWidth))))
          (Nat.ble count (Nat.mul 2 level))))
    levels 0 0

/-- The two requested moments packed into `outW`-bit lanes, reconstructed from the
nilpotent powers by the binomial theorem. -/
noncomputable def nilMomentPair (tri cs pmask w mask outW dimension maxLevel sigEnc : ℕ)
    (tree : Lean.RArray ℕ) (s t : ℕ) : ℕ :=
  let count := Nat.add (sigCount (sigField sigEnc s)) (sigCount (sigField sigEnc t))
  let levels := Nat.succ (Nat.min count maxLevel)
  Nat.rec (motive := fun _ ↦ ℕ → ℕ → ℕ)
    (fun _ acc ↦ acc)
    (fun _ ih level acc ↦
      ih (Nat.succ level)
        (Bool.rec acc
          (let value := treeAt cs pmask w mask tree
              (Nat.add (Nat.mul level tri) (triIdx s t))
            let coefficient := Nat.add (Nat.choose (Nat.sub dimension 1) level)
              (Nat.shiftLeft (Nat.choose dimension level) outW)
            Nat.add acc (Nat.mul value coefficient))
          (Nat.ble count (Nat.mul 2 level))))
    levels 0 0

/-- Check a row range of the packed final dimension and predecessor-dimension table. -/
noncomputable def nilResultCheck (tri cs pmask w mask outW pairCs pairPm pairW pairMask
    dimension maxLevel sigEnc : ℕ) (tree resultTree : Lean.RArray ℕ)
    (tLo tHi idx0 : ℕ) : Bool :=
  Nat.rec (motive := fun _ ↦ ℕ → ℕ → ℕ → Bool)
    (fun _ _ _ ↦ true)
    (fun _ ihT t idx cur ↦
      Nat.rec (motive := fun _ ↦ ℕ → ℕ → ℕ → Bool)
        (fun _ idx' cur' ↦ ihT (Nat.succ t) idx' cur')
        (fun _ ihS s idx' cur' ↦
          Bool.rec false
            (ihS (Nat.succ s) (Nat.succ idx')
              (Bool.rec
                (Nat.shiftRight cur' pairW)
                (resultTree.get (Nat.shiftRight (Nat.succ idx') pairCs))
                (Nat.beq (Nat.land idx' pairPm) pairPm)))
            (Nat.beq (Nat.land cur' pairMask)
              (nilMomentPair tri cs pmask w mask outW dimension maxLevel sigEnc tree s t)))
        (Nat.succ t) 0 idx cur)
    (Nat.sub tHi tLo) tLo idx0
    (Nat.shiftRight (resultTree.get (Nat.shiftRight idx0 pairCs))
      (Nat.mul pairW (Nat.land idx0 pairPm)))

/-- One requested moment reconstructed from independently packed nilpotent levels. -/
noncomputable def nilMomentValueLevels (dimension maxLevel sigEnc : ℕ)
    (shifts pmasks widths masks : Lean.RArray ℕ)
    (trees : Lean.RArray (Lean.RArray ℕ)) (s t : ℕ) : ℕ :=
  let count := Nat.add (sigCount (sigField sigEnc s)) (sigCount (sigField sigEnc t))
  let levels := Nat.succ (Nat.min count maxLevel)
  Nat.rec (motive := fun _ ↦ ℕ → ℕ → ℕ)
    (fun _ accumulator ↦ accumulator)
    (fun _ inductionHypothesis level accumulator ↦
      inductionHypothesis (Nat.succ level)
        (Bool.rec accumulator
          (Nat.add accumulator (Nat.mul
            (nilLevelAt shifts pmasks widths masks trees level (triIdx s t))
            (Nat.choose dimension level)))
          (Nat.ble count (Nat.mul 2 level))))
    levels 0 0

/-- The binomial coefficient `Nat.choose dimension level`, folded from the multiplicative
recurrence with `Nat.rec` over `Nat.mul`, `Nat.sub` and `Nat.div`.  The bridge to
`Nat.choose` is `binomial_eq_choose`. -/
noncomputable def binomial (dimension level : ℕ) : ℕ :=
  Nat.rec (motive := fun _ ↦ ℕ) 1
    (fun cursor value ↦ Nat.div (Nat.mul value (Nat.sub dimension cursor)) (Nat.succ cursor))
    level

/-- Check the packed coefficient table `coeffT`: for every level up to `maxLevel`, the
128-bit field of that level holds `binomial (dimension - 1) level` in its low 64 bits and
`binomial dimension level` in its high 64 bits. -/
noncomputable def coeffCheck (dimension maxLevel coeffT : ℕ) : Bool :=
  Nat.rec (motive := fun _ ↦ ℕ → Bool)
    (fun _ ↦ true)
    (fun _ inductionHypothesis level ↦
      let field := Nat.land (Nat.shiftRight coeffT (Nat.shiftLeft level 7))
        340282366920938463463374607431768211455
      Bool.rec false (inductionHypothesis (Nat.succ level))
        ((Nat.beq (Nat.land field 18446744073709551615)
            (binomial (Nat.sub dimension 1) level))
          && (Nat.beq (Nat.shiftRight field 64) (binomial dimension level))))
    (Nat.succ maxLevel) 0

/-- Reconstruct the packed pair and predecessor component from independently packed levels,
reading each level's two binomial coefficients from the packed table `coeffT`. -/
noncomputable def nilMomentPairPredLevels
    (outWidth coeffT maxLevel sigEnc : ℕ)
    (shifts pmasks widths masks : Lean.RArray ℕ)
    (trees : Lean.RArray (Lean.RArray ℕ)) (s t : ℕ) : ℕ × ℕ :=
  let count := Nat.add (sigCount (sigField sigEnc s)) (sigCount (sigField sigEnc t))
  let levels := Nat.succ (Bool.rec maxLevel count (Nat.ble count maxLevel))
  Nat.rec (motive := fun _ ↦ ℕ → ℕ × ℕ → ℕ × ℕ)
    (fun _ state ↦ state)
    (fun _ inductionHypothesis level state ↦
      let value := nilLevelAt shifts pmasks widths masks trees level (triIdx s t)
      let field := Nat.land (Nat.shiftRight coeffT (Nat.shiftLeft level 7))
        340282366920938463463374607431768211455
      let predecessorCoefficient := Nat.land field 18446744073709551615
      let packedCoefficient := Nat.add predecessorCoefficient
        (Nat.shiftLeft (Nat.shiftRight field 64) outWidth)
      inductionHypothesis (Nat.succ level)
        (Bool.rec state
          (Nat.add state.1 (Nat.mul value packedCoefficient),
            Nat.add state.2 (Nat.mul value predecessorCoefficient))
          (Nat.ble count (Nat.mul 2 level))))
    levels 0 (0, 0)

/-- Check final rows and the predecessor bound from independently packed levels. -/
noncomputable def nilResultBoundLevelsCheck
    (outWidth pairCs pairPmask pairWidth pairMask coeffT maxLevel sigEnc : ℕ)
    (shifts pmasks widths masks : Lean.RArray ℕ)
    (trees : Lean.RArray (Lean.RArray ℕ)) (resultTree : Lean.RArray ℕ)
    (tLo tHi idx0 : ℕ) : Bool :=
  Nat.rec (motive := fun _ ↦ ℕ → ℕ → ℕ → Bool)
    (fun _ _ _ ↦ true)
    (fun _ inductionHypothesis t idx current ↦
      Nat.rec (motive := fun _ ↦ ℕ → ℕ → ℕ → Bool)
        (fun _ index' current' ↦ inductionHypothesis (Nat.succ t) index' current')
        (fun _ rowHypothesis s index' current' ↦
          let reconstructed := nilMomentPairPredLevels outWidth coeffT maxLevel sigEnc
            shifts pmasks widths masks trees s t
          let checked := Bool.and' (Nat.beq (Nat.land current' pairMask) reconstructed.1)
            (Nat.blt reconstructed.2 (Nat.shiftLeft 1 outWidth))
          Bool.rec false
            (rowHypothesis (Nat.succ s) (Nat.succ index')
              (Bool.rec
                (Nat.shiftRight current' pairWidth)
                (resultTree.get (Nat.shiftRight (Nat.succ index') pairCs))
                (Nat.beq (Nat.land index' pairPmask) pairPmask)))
            checked)
        (Nat.succ t) 0 idx current)
    (Nat.sub tHi tLo) tLo idx0
    (Nat.shiftRight (resultTree.get (Nat.shiftRight idx0 pairCs))
      (Nat.mul pairWidth (Nat.land idx0 pairPmask)))

end cert246Data

end
