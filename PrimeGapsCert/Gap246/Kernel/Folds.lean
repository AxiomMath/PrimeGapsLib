/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Nat.Notation
public import PrimeGapsCert.Gap246.Kernel.Core

/-! # Kernel fold functions for the certificate computation

The functions the kernel reduces to check the certificate tables. Every term here is built
from `Nat.rec`, `Bool.rec`, `Lean.RArray.rec` and the primitive `Nat` operations; loops are
`Nat.rec` with a function-typed motive whose extra arguments carry the accumulators. Large
tables are `Lean.RArray ℕ` trees of packed leaves read through `treeAt`; boolean state
short-circuits through `Bool.rec`. The check theorems are proved by `Lean.reflBoolTrue`.

The term shapes here are fixed by measurement. The packed-field accessors live in
`PrimeGapsCert.Gap246.Kernel.Core` and are produced by `PrimeGapsCert.Gap246.Emit.Gen`;
edit both together.
-/

@[expose] public section

namespace cert246Kernel

open cert246Data (eagerAt triIdx sigField sigCount sigNib eraseAt slotField slotUsed slotPart2
  slotTarget labelField labelA labelSignature labelDegree labelSign)

/-- Field `i` of a packed-leaf tree: `t` is a `Lean.RArray ℕ` of leaves, each holding
`2^cs` fields of `w` bits (`pmask = 2^cs - 1`, `mask = 2^w - 1`); the field lives in
leaf `i >>> cs` at bit offset `w * (i &&& pmask)`. -/
noncomputable def treeAt (cs pmask w mask : ℕ) (t : Lean.RArray ℕ) (i : ℕ) : ℕ :=
  Nat.land
    (Nat.shiftRight (eagerAt t.get (Nat.shiftRight i cs)) (Nat.mul w (Nat.land i pmask)))
    mask

/-- Factorial `n!` from the factorial table `factT` (256-bit fields, `fmask = 2 ^ 256 - 1`). -/
noncomputable def factAt (fmask factT n : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight factT (Nat.shiftLeft n (nat_lit 8))) fmask

/-- Check the factorial table holds `0!, …, (count - 1)!` in 256-bit fields, peeling one
field per step, with nothing above the last field. -/
noncomputable def factCheck (fmask count factT : ℕ) : Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → Bool)
    (fun _ _ cur => Nat.beq cur (nat_lit 0))
    (fun _ ih i f cur =>
      Bool.rec (motive := fun _ => Bool) false
        (ih (Nat.succ i) (Nat.mul f (Nat.succ i)) (Nat.shiftRight cur (nat_lit 256)))
        (Nat.beq (Nat.land cur fmask) f))
    count (nat_lit 0) (nat_lit 1) factT

/-- One level-`k + 1` moment entry for the signature pair `(s, t)` from the level-`k` tree
`tIn`: the slot recurrence `∑ over used erase slots (j₁, j₂) of
(x₁ + x₂)! * tIn[erase j₁ s, erase j₂ t]`, where the identity slot contributes erased part
`0` and target the signature itself. -/
noncomputable def stepEntry (csI pmI wI maskI fmask eraseEnc factT : ℕ) (tIn : Lean.RArray ℕ)
    (s t : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ)
    (fun _ acc => acc)
    (fun _ ih₁ j₁ acc₁ =>
      ih₁ (Nat.succ j₁)
        ((fun f₁ =>
          Bool.rec (motive := fun _ => ℕ) acc₁
            ((fun p₁ g₁ =>
              Nat.rec (motive := fun _ => ℕ → ℕ → ℕ)
                (fun _ acc => acc)
                (fun _ ih₂ j₂ acc₂ =>
                  ih₂ (Nat.succ j₂)
                    ((fun f₂ =>
                      Bool.rec (motive := fun _ => ℕ) acc₂
                        (Nat.add acc₂
                          (Nat.mul
                            (factAt fmask factT
                              (Nat.shiftLeft (Nat.add p₁ (slotPart2 f₂)) (nat_lit 1)))
                            (treeAt csI pmI wI maskI tIn (triIdx g₁ (slotTarget f₂)))))
                        (slotUsed f₂))
                      (slotField eraseEnc t j₂)))
                (nat_lit 5) (nat_lit 0) acc₁)
              (slotPart2 f₁) (slotTarget f₁))
            (slotUsed f₁))
          (slotField eraseEnc s j₁)))
    (nat_lit 5) (nat_lit 0) (nat_lit 0)

/-- The outer erase-slot walk of one level-`k + 1` moment entry: `inner` runs at each used
slot of `s` among `0–3`, the walk stops at the first unused slot (the used ones are a
prefix), and the outer identity slot's body `innerId` closes the entry. Row `t`'s slots
enter through `inner` and `innerId` (`PrimeGaps.stepEntryH_walk`). -/
noncomputable def stepEntryH (eraseEnc : ℕ) (inner : ℕ → ℕ → ℕ → ℕ)
    (innerId : ℕ → ℕ → ℕ) (s : ℕ) : ℕ :=
  (fun (outer : ℕ → (ℕ → ℕ) → ℕ → ℕ) =>
    innerId s
      (outer (nat_lit 0)
        (outer (nat_lit 1) (outer (nat_lit 2) (outer (nat_lit 3) (fun a => a))))
        (nat_lit 0)))
    (fun j₁ cont acc₁ =>
      (fun f₁ =>
        Bool.rec (motive := fun _ => ℕ) acc₁
          ((fun p₁ g₁ => cont (inner p₁ g₁ acc₁)) (slotPart2 f₁) (slotTarget f₁))
          (slotUsed f₁))
        (slotField eraseEnc s j₁))

/-- Check row `t` of one level transition and hand the row's end state to `cont`: each
entry `(s, t)` (`s ≤ t`) is rebuilt by the slot recurrence over row `t`'s used slots (a
prefix of slots `0–3`, plus the identity slot with erased part `0` and target `t`) and
compared with the output cursor's field; the input cursor's own field supplies the
identity pair. -/
noncomputable def stepRow (csO pmO wO maskO csI pmI wI maskI fmask eraseEnc factT : ℕ)
    (tIn tOut : Lean.RArray ℕ) (cont : ℕ → ℕ → ℕ → ℕ → Bool)
    (t idx cur curI : ℕ) :
    Bool :=
  (fun f₀ f₁ f₂ f₃ =>
    (fun y₀ r₀ w₀ y₁ r₁ w₁ y₂ r₂ w₂ y₃ r₃ w₃ wt =>
      (fun (rowGo : (ℕ → ℕ) → Bool) =>
        Bool.rec (motive := fun _ => Bool)
          (rowGo (stepEntryH eraseEnc
            (fun p₁ g₁ acc₂ =>
              (fun fS tg =>
                Nat.add acc₂
                  (Nat.mul (Nat.land fS fmask)
                    (treeAt csI pmI wI maskI tIn
                      (Bool.rec (motive := fun _ => ℕ) (Nat.add wt g₁) (Nat.add tg t)
                        (Nat.blt t g₁)))))
                (Nat.shiftRight factT (Nat.shiftLeft p₁ (nat_lit 9)))
                (Nat.div (Nat.mul g₁ (Nat.succ g₁)) (nat_lit 2)))
            (fun _ acc₂ => acc₂)))
          (Bool.rec (motive := fun _ => Bool)
            (rowGo (stepEntryH eraseEnc
              (fun p₁ g₁ acc₂ =>
                (fun fS tg =>
                  Nat.add
                    (Nat.add acc₂
                      (Nat.mul (Nat.land (Nat.shiftRight fS y₀) fmask)
                        (treeAt csI pmI wI maskI tIn
                          (Bool.rec (motive := fun _ => ℕ) (Nat.add w₀ g₁)
                            (Nat.add tg r₀) (Nat.blt r₀ g₁)))))
                    (Nat.mul (Nat.land fS fmask)
                      (treeAt csI pmI wI maskI tIn
                        (Bool.rec (motive := fun _ => ℕ) (Nat.add wt g₁) (Nat.add tg t)
                          (Nat.blt t g₁)))))
                  (Nat.shiftRight factT (Nat.shiftLeft p₁ (nat_lit 9)))
                  (Nat.div (Nat.mul g₁ (Nat.succ g₁)) (nat_lit 2)))
              (fun s' acc₂ =>
                (fun tg' =>
                  Nat.add acc₂
                    (Nat.mul (Nat.land (Nat.shiftRight factT y₀) fmask)
                      (treeAt csI pmI wI maskI tIn
                        (Bool.rec (motive := fun _ => ℕ) (Nat.add w₀ s')
                          (Nat.add tg' r₀) (Nat.blt r₀ s')))))
                  (Nat.div (Nat.mul s' (Nat.succ s')) (nat_lit 2)))))
            (Bool.rec (motive := fun _ => Bool)
              (rowGo (stepEntryH eraseEnc
                (fun p₁ g₁ acc₂ =>
                  (fun fS tg =>
                    Nat.add
                      (Nat.add
                        (Nat.add acc₂
                          (Nat.mul (Nat.land (Nat.shiftRight fS y₀) fmask)
                            (treeAt csI pmI wI maskI tIn
                              (Bool.rec (motive := fun _ => ℕ) (Nat.add w₀ g₁)
                                (Nat.add tg r₀) (Nat.blt r₀ g₁)))))
                        (Nat.mul (Nat.land (Nat.shiftRight fS y₁) fmask)
                          (treeAt csI pmI wI maskI tIn
                            (Bool.rec (motive := fun _ => ℕ) (Nat.add w₁ g₁)
                              (Nat.add tg r₁) (Nat.blt r₁ g₁)))))
                      (Nat.mul (Nat.land fS fmask)
                        (treeAt csI pmI wI maskI tIn
                          (Bool.rec (motive := fun _ => ℕ) (Nat.add wt g₁)
                            (Nat.add tg t) (Nat.blt t g₁)))))
                    (Nat.shiftRight factT (Nat.shiftLeft p₁ (nat_lit 9)))
                    (Nat.div (Nat.mul g₁ (Nat.succ g₁)) (nat_lit 2)))
                (fun s' acc₂ =>
                  (fun tg' =>
                    Nat.add
                      (Nat.add acc₂
                        (Nat.mul (Nat.land (Nat.shiftRight factT y₀) fmask)
                          (treeAt csI pmI wI maskI tIn
                            (Bool.rec (motive := fun _ => ℕ) (Nat.add w₀ s')
                              (Nat.add tg' r₀) (Nat.blt r₀ s')))))
                      (Nat.mul (Nat.land (Nat.shiftRight factT y₁) fmask)
                        (treeAt csI pmI wI maskI tIn
                          (Bool.rec (motive := fun _ => ℕ) (Nat.add w₁ s')
                            (Nat.add tg' r₁) (Nat.blt r₁ s')))))
                    (Nat.div (Nat.mul s' (Nat.succ s')) (nat_lit 2)))))
              (Bool.rec (motive := fun _ => Bool)
                (rowGo (stepEntryH eraseEnc
                  (fun p₁ g₁ acc₂ =>
                    (fun fS tg =>
                      Nat.add
                        (Nat.add
                          (Nat.add
                            (Nat.add acc₂
                              (Nat.mul (Nat.land (Nat.shiftRight fS y₀) fmask)
                                (treeAt csI pmI wI maskI tIn
                                  (Bool.rec (motive := fun _ => ℕ) (Nat.add w₀ g₁)
                                    (Nat.add tg r₀) (Nat.blt r₀ g₁)))))
                            (Nat.mul (Nat.land (Nat.shiftRight fS y₁) fmask)
                              (treeAt csI pmI wI maskI tIn
                                (Bool.rec (motive := fun _ => ℕ) (Nat.add w₁ g₁)
                                  (Nat.add tg r₁) (Nat.blt r₁ g₁)))))
                          (Nat.mul (Nat.land (Nat.shiftRight fS y₂) fmask)
                            (treeAt csI pmI wI maskI tIn
                              (Bool.rec (motive := fun _ => ℕ) (Nat.add w₂ g₁)
                                (Nat.add tg r₂) (Nat.blt r₂ g₁)))))
                        (Nat.mul (Nat.land fS fmask)
                          (treeAt csI pmI wI maskI tIn
                            (Bool.rec (motive := fun _ => ℕ) (Nat.add wt g₁)
                              (Nat.add tg t) (Nat.blt t g₁)))))
                      (Nat.shiftRight factT (Nat.shiftLeft p₁ (nat_lit 9)))
                      (Nat.div (Nat.mul g₁ (Nat.succ g₁)) (nat_lit 2)))
                  (fun s' acc₂ =>
                    (fun tg' =>
                      Nat.add
                        (Nat.add
                          (Nat.add acc₂
                            (Nat.mul (Nat.land (Nat.shiftRight factT y₀) fmask)
                              (treeAt csI pmI wI maskI tIn
                                (Bool.rec (motive := fun _ => ℕ) (Nat.add w₀ s')
                                  (Nat.add tg' r₀) (Nat.blt r₀ s')))))
                          (Nat.mul (Nat.land (Nat.shiftRight factT y₁) fmask)
                            (treeAt csI pmI wI maskI tIn
                              (Bool.rec (motive := fun _ => ℕ) (Nat.add w₁ s')
                                (Nat.add tg' r₁) (Nat.blt r₁ s')))))
                        (Nat.mul (Nat.land (Nat.shiftRight factT y₂) fmask)
                          (treeAt csI pmI wI maskI tIn
                            (Bool.rec (motive := fun _ => ℕ) (Nat.add w₂ s')
                              (Nat.add tg' r₂) (Nat.blt r₂ s')))))
                      (Nat.div (Nat.mul s' (Nat.succ s')) (nat_lit 2)))))
                (rowGo (stepEntryH eraseEnc
                  (fun p₁ g₁ acc₂ =>
                    (fun fS tg =>
                      Nat.add
                        (Nat.add
                          (Nat.add
                            (Nat.add
                              (Nat.add acc₂
                                (Nat.mul (Nat.land (Nat.shiftRight fS y₀) fmask)
                                  (treeAt csI pmI wI maskI tIn
                                    (Bool.rec (motive := fun _ => ℕ) (Nat.add w₀ g₁)
                                      (Nat.add tg r₀) (Nat.blt r₀ g₁)))))
                              (Nat.mul (Nat.land (Nat.shiftRight fS y₁) fmask)
                                (treeAt csI pmI wI maskI tIn
                                  (Bool.rec (motive := fun _ => ℕ) (Nat.add w₁ g₁)
                                    (Nat.add tg r₁) (Nat.blt r₁ g₁)))))
                            (Nat.mul (Nat.land (Nat.shiftRight fS y₂) fmask)
                              (treeAt csI pmI wI maskI tIn
                                (Bool.rec (motive := fun _ => ℕ) (Nat.add w₂ g₁)
                                  (Nat.add tg r₂) (Nat.blt r₂ g₁)))))
                          (Nat.mul (Nat.land (Nat.shiftRight fS y₃) fmask)
                            (treeAt csI pmI wI maskI tIn
                              (Bool.rec (motive := fun _ => ℕ) (Nat.add w₃ g₁)
                                (Nat.add tg r₃) (Nat.blt r₃ g₁)))))
                        (Nat.mul (Nat.land fS fmask)
                          (treeAt csI pmI wI maskI tIn
                            (Bool.rec (motive := fun _ => ℕ) (Nat.add wt g₁)
                              (Nat.add tg t) (Nat.blt t g₁)))))
                      (Nat.shiftRight factT (Nat.shiftLeft p₁ (nat_lit 9)))
                      (Nat.div (Nat.mul g₁ (Nat.succ g₁)) (nat_lit 2)))
                  (fun s' acc₂ =>
                    (fun tg' =>
                      Nat.add
                        (Nat.add
                          (Nat.add
                            (Nat.add acc₂
                              (Nat.mul (Nat.land (Nat.shiftRight factT y₀) fmask)
                                (treeAt csI pmI wI maskI tIn
                                  (Bool.rec (motive := fun _ => ℕ) (Nat.add w₀ s')
                                    (Nat.add tg' r₀) (Nat.blt r₀ s')))))
                            (Nat.mul (Nat.land (Nat.shiftRight factT y₁) fmask)
                              (treeAt csI pmI wI maskI tIn
                                (Bool.rec (motive := fun _ => ℕ) (Nat.add w₁ s')
                                  (Nat.add tg' r₁) (Nat.blt r₁ s')))))
                          (Nat.mul (Nat.land (Nat.shiftRight factT y₂) fmask)
                            (treeAt csI pmI wI maskI tIn
                              (Bool.rec (motive := fun _ => ℕ) (Nat.add w₂ s')
                                (Nat.add tg' r₂) (Nat.blt r₂ s')))))
                        (Nat.mul (Nat.land (Nat.shiftRight factT y₃) fmask)
                          (treeAt csI pmI wI maskI tIn
                            (Bool.rec (motive := fun _ => ℕ) (Nat.add w₃ s')
                              (Nat.add tg' r₃) (Nat.blt r₃ s')))))
                      (Nat.div (Nat.mul s' (Nat.succ s')) (nat_lit 2)))))
                (slotUsed f₃))
              (slotUsed f₂))
            (slotUsed f₁))
          (slotUsed f₀))
        (fun entry =>
          Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → Bool)
            (fun _ idx' cur' curI' => cont (Nat.succ t) idx' cur' curI')
            (fun _ ihS s idx' cur' curI' =>
              Bool.rec (motive := fun _ => Bool) false
                (ihS (Nat.succ s) (Nat.succ idx')
                  (Bool.rec (motive := fun _ => ℕ)
                    (Nat.shiftRight cur' wO)
                    (Lean.RArray.get tOut (Nat.shiftRight (Nat.succ idx') csO))
                    (Nat.beq (Nat.land idx' pmO) pmO))
                  (Bool.rec (motive := fun _ => ℕ)
                    (Nat.shiftRight curI' wI)
                    (Lean.RArray.get tIn (Nat.shiftRight (Nat.succ idx') csI))
                    (Nat.beq (Nat.land idx' pmI) pmI)))
                (Nat.beq (Nat.land cur' maskO)
                  (Nat.add (entry s) (Nat.land curI' maskI))))
            (Nat.succ t) (nat_lit 0) idx cur curI))
      (Nat.shiftLeft (slotPart2 f₀) (nat_lit 9)) (slotTarget f₀)
      (Nat.div (Nat.mul (slotTarget f₀) (Nat.succ (slotTarget f₀))) (nat_lit 2))
      (Nat.shiftLeft (slotPart2 f₁) (nat_lit 9)) (slotTarget f₁)
      (Nat.div (Nat.mul (slotTarget f₁) (Nat.succ (slotTarget f₁))) (nat_lit 2))
      (Nat.shiftLeft (slotPart2 f₂) (nat_lit 9)) (slotTarget f₂)
      (Nat.div (Nat.mul (slotTarget f₂) (Nat.succ (slotTarget f₂))) (nat_lit 2))
      (Nat.shiftLeft (slotPart2 f₃) (nat_lit 9)) (slotTarget f₃)
      (Nat.div (Nat.mul (slotTarget f₃) (Nat.succ (slotTarget f₃))) (nat_lit 2))
      (Nat.div (Nat.mul t (Nat.succ t)) (nat_lit 2)))
    (slotField eraseEnc t (nat_lit 0)) (slotField eraseEnc t (nat_lit 1))
    (slotField eraseEnc t (nat_lit 2)) (slotField eraseEnc t (nat_lit 3))

/-- Check rows `tLo ≤ t < tHi` of one moment-ladder level transition
(`idx0 = tLo*(tLo+1)/2`): rebuild every entry `(s, t)` (`s ≤ t`) from the level-`k` tree
`tIn` by the slot recurrence and compare it with the level-`k + 1` tree `tOut` at the
running triangular index. The two leading guards require `pmO + 1 = 2^csO` and
`pmI + 1 = 2^csI`. -/
noncomputable def stepCheck (csO pmO wO maskO csI pmI wI maskI fmask
    eraseEnc factT : ℕ) (tIn tOut : Lean.RArray ℕ) (tLo tHi idx0 : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) false
    (Bool.rec (motive := fun _ => Bool) false
      (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → Bool)
        (fun _ _ _ _ => true)
        (fun _ ihT t idx cur curI =>
          stepRow csO pmO wO maskO csI pmI wI maskI fmask eraseEnc factT tIn tOut
            ihT t idx cur curI)
        (Nat.sub tHi tLo) tLo idx0
        (Nat.shiftRight (Lean.RArray.get tOut (Nat.shiftRight idx0 csO))
          (Nat.mul wO (Nat.land idx0 pmO)))
        (Nat.shiftRight (Lean.RArray.get tIn (Nat.shiftRight idx0 csI))
          (Nat.mul wI (Nat.land idx0 pmI))))
      (Nat.beq (Nat.succ pmI) (Nat.shiftLeft (nat_lit 1) csI)))
    (Nat.beq (Nat.succ pmO) (Nat.shiftLeft (nat_lit 1) csO))

/-- Validate the signature, erase and label tables against each other, short-circuiting on
any failure. Signatures: at most `maxNib` nonzero halved parts, sorted ascending, trailing
nibbles zero. Erase slots: the used slots 0–3 list the signature's distinct parts ascending
(at most four), each targeting an in-range signature encoding with one copy of that part
removed; slot 4 is the identity slot. Labels: signature index below `S`, part sum `u`
matching the signature, `a + u ≤ aBound`. -/
noncomputable def dataCheck (S n maxNib aBound sigEnc eraseEnc labelEnc : ℕ) : Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool)
    (fun _ uT =>
      Nat.rec (motive := fun _ => ℕ → Bool)
        (fun _ => true)
        (fun _ ihL i =>
          (fun fL =>
            Bool.rec (motive := fun _ => Bool) false
              (ihL (Nat.succ i))
              (Bool.and'
                (Bool.and' (Nat.blt (labelSignature fL) S)
                  (Nat.beq (labelDegree fL)
                    (Nat.land
                      (Nat.shiftRight uT (Nat.shiftLeft (labelSignature fL) (nat_lit 4)))
                      (nat_lit 65535))))
                (Nat.ble (Nat.add (labelA fL) (labelDegree fL)) aBound)))
            (labelField labelEnc i))
        n (nat_lit 0))
    (fun _ ihS s uT =>
      (fun enc =>
        (fun m =>
          Bool.rec (motive := fun _ => Bool) false
            (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → Bool)
              (fun _ _ jSlot usum =>
                Nat.rec (motive := fun _ => ℕ → Bool)
                  (fun _ =>
                    Bool.rec (motive := fun _ => Bool) false
                      (ihS (Nat.succ s)
                        (Nat.add uT
                          (Nat.shiftLeft (Nat.shiftLeft usum (nat_lit 1))
                            (Nat.shiftLeft s (nat_lit 4)))))
                      (Bool.and' (Nat.ble jSlot (nat_lit 4))
                        (Nat.beq (slotField eraseEnc s (nat_lit 4))
                          (Nat.succ (Nat.shiftLeft s (nat_lit 5))))))
                  (fun _ ihJ j =>
                    Bool.rec (motive := fun _ => Bool) false
                      (ihJ (Nat.succ j))
                      (Nat.beq (slotField eraseEnc s j) (nat_lit 0)))
                  (Nat.sub (nat_lit 4) jSlot) jSlot)
              (fun _ ihT t prev jSlot usum =>
                (fun nib =>
                  Bool.rec (motive := fun _ => Bool)
                    (Bool.rec (motive := fun _ => Bool) false
                      (ihT (Nat.succ t) prev jSlot usum)
                      (Nat.beq nib (nat_lit 0)))
                    (Bool.rec (motive := fun _ => Bool) false
                      (Bool.rec (motive := fun _ => Bool)
                        (ihT (Nat.succ t) nib jSlot (Nat.add usum nib))
                        ((fun fS =>
                          Bool.rec (motive := fun _ => Bool) false
                            (ihT (Nat.succ t) nib (Nat.succ jSlot) (Nat.add usum nib))
                            (Bool.and'
                              (Bool.and' (slotUsed fS) (Nat.beq (slotPart2 fS) nib))
                              (Bool.and' (Nat.blt (slotTarget fS) S)
                                (Nat.beq (sigField sigEnc (slotTarget fS))
                                  (eraseAt enc t)))))
                          (slotField eraseEnc s jSlot))
                        (Bool.or' (Nat.beq t (nat_lit 0))
                          (Bool.not' (Nat.beq nib prev))))
                      (Bool.and' (Nat.blt (nat_lit 0) nib) (Nat.ble prev nib)))
                    (Nat.blt t m))
                  (sigNib enc t))
              maxNib (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0))
            (Nat.ble m maxNib))
          (sigCount enc))
        (sigField sigEnc s))
    S (nat_lit 0) (nat_lit 0)

end cert246Kernel
