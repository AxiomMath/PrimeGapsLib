/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Kernel.Core

local notation "ℕ" => Nat

/-! # First-order kernel for the packed factorial-moment certificate

The usual moment transition is `I + N`, where `N` contains every erase-slot pair except
the two identity slots.  Iterating `N` from the empty-signature base is nilpotent: its
level can be nonzero only when it is between half the total part count and the total part
count.  The numerical checks below expose only `Nat`, `Bool`, and packed-tree operations
to the kernel.
-/

@[expose] public section

namespace cert246Data

/-- Check a packed signature-by-exponent erase-target table. -/
noncomputable def eraseTargetCheck
    (signatureCount degreeBound eraseCs erasePmask sigEnc : ℕ)
    (eraseTargetTree : Lean.RArray ℕ) : Bool :=
  Nat.rec (motive := fun _ ↦ ℕ → Bool)
    (fun _ ↦ true)
    (fun _ inductionHypothesis row ↦
      let enc := sigField sigEnc row
      let entries := Nat.rec (motive := fun _ ↦ ℕ → Bool)
        (fun _ ↦ Nat.beq
          (treeAt eraseCs erasePmask 16 65535 eraseTargetTree
            (Nat.mul row (Nat.add degreeBound 1))) row)
        (fun _ positionHypothesis position ↦
          let target := treeAt eraseCs erasePmask 16 65535 eraseTargetTree
            (Nat.add (Nat.mul row (Nat.add degreeBound 1))
              (Nat.mul 2 (sigNib enc position)))
          Bool.rec false (positionHypothesis position.succ)
            (Bool.and' (Nat.blt target signatureCount)
              (Nat.beq (sigField sigEnc target) (eraseAt enc position))))
        (sigCount enc) 0
      Bool.rec false (inductionHypothesis row.succ) entries)
    signatureCount 0

/-- Factorial `n!` from a table of 256-bit fields. -/
noncomputable def factAt (factT n : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight factT (Nat.shiftLeft n 8))
    115792089237316195423570985008687907853269984665640564039457584007913129639935

/-- Whether nilpotent level `level` can be nonzero at total part count `count`. -/
noncomputable def nilActive (level count : ℕ) : Bool :=
  Bool.and' (Nat.ble level count) (Nat.ble count (Nat.mul 2 level))

/-- One application of the identity-free transition `N` through an arbitrary
predecessor lookup.

Slots `0..3` are genuine erasures and slot `4` is the identity.  Each genuine left slot
is paired with all five right slots, and the identity left slot with the four genuine
right slots. -/
noncomputable def nilEntryWith (eraseEnc factT : ℕ) (lookup : ℕ → ℕ → ℕ)
    (s t : ℕ) : ℕ :=
  let pair : ℕ → ℕ → ℕ → ℕ := fun field₁ j₂ acc₂ ↦
    let field₂ := slotField eraseEnc t j₂
    Bool.rec acc₂
      (Nat.add acc₂
        (Nat.mul
          (factAt factT (Nat.shiftLeft (Nat.add (slotPart2 field₁) (slotPart2 field₂)) 1))
          (lookup (slotTarget field₁) (slotTarget field₂))))
      (slotUsed field₂)
  let genuine : ℕ → ℕ → ℕ := fun j₁ acc₁ ↦
    let field₁ := slotField eraseEnc s j₁
    Bool.rec acc₁
      (pair field₁ 4 (pair field₁ 3 (pair field₁ 2 (pair field₁ 1 (pair field₁ 0 acc₁)))))
      (slotUsed field₁)
  let identity : ℕ → ℕ → ℕ := fun j₂ acc₂ ↦
    let field₂ := slotField eraseEnc t j₂
    Bool.rec acc₂
      (Nat.add acc₂
        (Nat.mul
          (factAt factT (Nat.shiftLeft (slotPart2 field₂) 1))
          (lookup s (slotTarget field₂))))
      (slotUsed field₂)
  identity 3 (identity 2 (identity 1 (identity 0
    (genuine 3 (genuine 2 (genuine 1 (genuine 0 0)))))))

/-- One application of the identity-free transition to a flat packed ladder. -/
noncomputable def nilEntry (tri cs pmask w mask eraseEnc factT level : ℕ)
    (tree : Lean.RArray ℕ) (s t : ℕ) : ℕ :=
  nilEntryWith eraseEnc factT
    (fun first second ↦ treeAt cs pmask w mask tree
      (Nat.add (Nat.mul (Nat.sub level 1) tri) (triIdx first second))) s t

/-- Check a row range of nilpotent level zero. -/
noncomputable def nilBaseCheck (cs pmask w mask sigEnc : ℕ) (tree : Lean.RArray ℕ)
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
                (Nat.shiftRight cur' w)
                (tree.get (Nat.shiftRight (Nat.succ idx') cs))
                (Nat.beq (Nat.land idx' pmask) pmask)))
            (Nat.beq (Nat.land cur' mask)
              (Bool.rec 0 1
                (Bool.and' (Nat.beq (sigField sigEnc s) 0)
                  (Nat.beq (sigField sigEnc t) 0)))))
        (Nat.succ t) 0 idx cur)
    (Nat.sub tHi tLo) tLo idx0
    (Nat.shiftRight (tree.get (Nat.shiftRight idx0 cs))
      (Nat.mul w (Nat.land idx0 pmask)))

/-- Check a row range of one identity-free transition level.  Inactive entries are
required to be zero, so every stored field remains certified. -/
noncomputable def nilStepCheck (tri cs pmask w mask sigEnc eraseEnc factT level : ℕ)
    (tree : Lean.RArray ℕ) (tLo tHi idx0 : ℕ) : Bool :=
  let out0 := Nat.add (Nat.mul level tri) idx0
  Nat.rec (motive := fun _ ↦ ℕ → ℕ → ℕ → Bool)
    (fun _ _ _ ↦ true)
    (fun _ ihT t idx cur ↦
      let countT := sigCount (sigField sigEnc t)
      Nat.rec (motive := fun _ ↦ ℕ → ℕ → ℕ → Bool)
        (fun _ idx' cur' ↦ ihT (Nat.succ t) idx' cur')
        (fun _ ihS s idx' cur' ↦
          let count := Nat.add (sigCount (sigField sigEnc s)) countT
          let expected := Bool.rec 0
            (nilEntry tri cs pmask w mask eraseEnc factT level tree s t)
            (nilActive level count)
          Bool.rec false
            (ihS (Nat.succ s) (Nat.succ idx')
              (Bool.rec
                (Nat.shiftRight cur' w)
                (tree.get (Nat.shiftRight (Nat.succ idx') cs))
                (Nat.beq (Nat.land idx' pmask) pmask)))
            (Nat.beq (Nat.land cur' mask) expected))
        (Nat.succ t) 0 idx cur)
    (Nat.sub tHi tLo) tLo out0
    (Nat.shiftRight (tree.get (Nat.shiftRight out0 cs))
      (Nat.mul w (Nat.land out0 pmask)))

/-- One entry in an independently packed nilpotent level. -/
noncomputable def nilLevelAt
    (shifts pmasks widths masks : Lean.RArray ℕ)
    (trees : Lean.RArray (Lean.RArray ℕ)) (level index : ℕ) : ℕ :=
  treeAt (shifts.get level) (pmasks.get level) (widths.get level) (masks.get level)
    (trees.get level) index

/-- A predecessor lookup in an independently packed ladder, masked by the generic
support bound for that predecessor level. -/
noncomputable def nilLevelPreviousAt (sigEnc previous : ℕ)
    (shifts pmasks widths masks : Lean.RArray ℕ)
    (trees : Lean.RArray (Lean.RArray ℕ)) (first second : ℕ) : ℕ :=
  Bool.rec 0
    (nilLevelAt shifts pmasks widths masks trees previous (triIdx first second))
    (nilActive previous
      (Nat.add (sigCount (sigField sigEnc first)) (sigCount (sigField sigEnc second))))

/-- One support-masked identity-free transition between independently packed levels. -/
noncomputable def nilLevelEntry (sigEnc eraseEnc factT level : ℕ)
    (shifts pmasks widths masks : Lean.RArray ℕ)
    (trees : Lean.RArray (Lean.RArray ℕ)) (s t : ℕ) : ℕ :=
  nilEntryWith eraseEnc factT
    (nilLevelPreviousAt sigEnc (Nat.sub level 1) shifts pmasks widths masks trees) s t

/-- A predecessor lookup that references only the immediately preceding packed tree. -/
noncomputable def nilTreePreviousAt (sigEnc previous previousShift previousPmask
    previousWidth previousMask : ℕ) (previousTree : Lean.RArray ℕ)
    (first second : ℕ) : ℕ :=
  Bool.rec 0
    (treeAt previousShift previousPmask previousWidth previousMask previousTree
      (triIdx first second))
    (nilActive previous
      (Nat.add (sigCount (sigField sigEnc first)) (sigCount (sigField sigEnc second))))

/-- One identity-free transition referencing only the immediately preceding packed tree. -/
noncomputable def nilTreeEntry (sigEnc eraseEnc factT level previousShift previousPmask
    previousWidth previousMask : ℕ) (previousTree : Lean.RArray ℕ) (s t : ℕ) : ℕ :=
  nilEntryWith eraseEnc factT
    (nilTreePreviousAt sigEnc (Nat.sub level 1) previousShift previousPmask previousWidth
      previousMask previousTree) s t

/-- Check level zero in an independently packed nilpotent ladder. -/
noncomputable def nilBaseLevelsCheck (sigEnc : ℕ)
    (shifts pmasks widths masks : Lean.RArray ℕ)
    (trees : Lean.RArray (Lean.RArray ℕ)) (tLo tHi idx0 : ℕ) : Bool :=
  nilBaseCheck (shifts.get 0) (pmasks.get 0) (widths.get 0) (masks.get 0) sigEnc
    (trees.get 0) tLo tHi idx0

/-- Check one transition using only its current and immediately preceding packed trees. -/
noncomputable def nilStepTreesCheck
    (currentShift currentPmask currentWidth currentMask previousShift previousPmask
      previousWidth previousMask sigEnc eraseEnc factT level : ℕ)
    (currentTree previousTree : Lean.RArray ℕ) (tLo tHi idx0 : ℕ) : Bool :=
  Nat.rec (motive := fun _ ↦ ℕ → ℕ → Bool)
    (fun _ _ ↦ true)
    (fun _ inductionHypothesis t idx ↦
      let countT := sigCount (sigField sigEnc t)
      Nat.rec (motive := fun _ ↦ ℕ → ℕ → Bool)
        (fun _ idx' ↦ inductionHypothesis (Nat.succ t) idx')
        (fun _ rowHypothesis s idx' ↦
          let count := Nat.add (sigCount (sigField sigEnc s)) countT
          Bool.rec
            (rowHypothesis (Nat.succ s) (Nat.succ idx'))
            (Bool.rec false (rowHypothesis (Nat.succ s) (Nat.succ idx'))
              (Nat.beq
                (treeAt currentShift currentPmask currentWidth currentMask currentTree idx')
                (nilTreeEntry sigEnc eraseEnc factT level previousShift previousPmask
                  previousWidth previousMask previousTree s t)))
            (nilActive level count))
        (Nat.succ t) 0 idx)
    (Nat.sub tHi tLo) tLo idx0

end cert246Data

end
