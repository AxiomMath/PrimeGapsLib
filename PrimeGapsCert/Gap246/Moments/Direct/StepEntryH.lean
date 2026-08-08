/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import PrimeGapsCert.Gap246.Kernel.Folds
public import PrimeGapsCert.Gap246.Sums

import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Monoid.NatCast
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

/-! # The hoisted ladder step entry

The value one row of `cert246Kernel.stepCheck` compares against the output tree, as a double sum
over the erase slots. `rowVal` names that value: the outer erase slots `0–3` of the column
against all five slots of the row, plus the outer identity slot against the row's slots
`0–3`. `stepEntryH_walk` identifies the outer walk of `cert246Kernel.stepEntryH` with the
sum over the column's used slots.

The two facts the row bodies rest on are `SlotId` (slot `4` is the identity slot) and
`SlotPrefix` (the used flags of slots `0–3` are a prefix); `cert246Kernel.dataCheck` establishes
both.
-/

@[expose] public section

namespace PrimeGaps.Gap246

open cert246Kernel
open cert246Data (slotField slotUsed slotPart2 slotTarget triIdx)

section stepEntryH

/-! ### The erase-slot facts the row bodies rest on -/

/-- The identity erase slot of signature `g`: slot `4` is used, carries halved erased part
`0` and targets `g` itself. -/
structure SlotId (eraseEnc g : ℕ) : Prop where
  used : slotUsed (slotField eraseEnc g 4) = true
  part2 : slotPart2 (slotField eraseEnc g 4) = 0
  tgt : slotTarget (slotField eraseEnc g 4) = g

/-- The used flags of the erase slots `0–3` of signature `g` form a prefix. -/
def SlotPrefix (eraseEnc g : ℕ) : Prop :=
  ∀ i j, i ≤ j → j < 4 → slotUsed (slotField eraseEnc g j) = true →
    slotUsed (slotField eraseEnc g i) = true

/-- Past an unused erase slot every later slot of `0–3` is unused. -/
theorem SlotPrefix.unused {eraseEnc g : ℕ} (h : SlotPrefix eraseEnc g) {i j : ℕ}
    (hij : i ≤ j) (hj : j < 4) (hi : slotUsed (slotField eraseEnc g i) = false) :
    slotUsed (slotField eraseEnc g j) = false := by grind [SlotPrefix]

/-! ### The value of one row entry -/

/-- The gated slot sum of row `t` against an outer slot with halved erased part `p` and
target `g`. -/
noncomputable def innerSum (csI pmI wI maskI fmask eraseEnc factT : ℕ)
    (tIn : Lean.RArray ℕ) (t p g : ℕ) : ℕ :=
  ∑ j ∈ Finset.range 5,
    if slotUsed (slotField eraseEnc t j) = true then
      factAt fmask factT (Nat.shiftLeft (p + slotPart2 (slotField eraseEnc t j)) 1) *
        treeAt csI pmI wI maskI tIn (triIdx g (slotTarget (slotField eraseEnc t j)))
    else 0

/-- The part of the ladder entry at `(s, t)` the row body computes: the outer erase slots
`0–3` of `s` against all five slots of row `t`, and the outer identity slot against the
row's slots `0–3`. -/
noncomputable def rowVal (csI pmI wI maskI fmask eraseEnc factT : ℕ)
    (tIn : Lean.RArray ℕ) (t s : ℕ) : ℕ :=
  (∑ j ∈ Finset.range 4,
    if slotUsed (slotField eraseEnc s j) = true then
      innerSum csI pmI wI maskI fmask eraseEnc factT tIn t
        (slotPart2 (slotField eraseEnc s j)) (slotTarget (slotField eraseEnc s j))
    else 0) +
    ∑ j ∈ Finset.range 4,
      if slotUsed (slotField eraseEnc t j) = true then
        factAt fmask factT (Nat.shiftLeft (slotPart2 (slotField eraseEnc t j)) 1) *
          treeAt csI pmI wI maskI tIn (triIdx s (slotTarget (slotField eraseEnc t j)))
      else 0

/-- The identity slot of row `t` contributes the level-`k` entry at the outer slot's target
and `t`. -/
theorem innerSum_eq {csI pmI wI maskI fmask eraseEnc factT : ℕ} {tIn : Lean.RArray ℕ}
    {t : ℕ} (hidT : SlotId eraseEnc t) (p g : ℕ) :
    innerSum csI pmI wI maskI fmask eraseEnc factT tIn t p g =
      (∑ j ∈ Finset.range 4,
        if slotUsed (slotField eraseEnc t j) = true then
          factAt fmask factT (Nat.shiftLeft (p + slotPart2 (slotField eraseEnc t j)) 1) *
            treeAt csI pmI wI maskI tIn (triIdx g (slotTarget (slotField eraseEnc t j)))
        else 0) +
      factAt fmask factT (Nat.shiftLeft p 1) * treeAt csI pmI wI maskI tIn (triIdx g t) := by
  simp [innerSum, Finset.sum_range_succ, hidT.used, hidT.part2, hidT.tgt]

/-! ### The outer erase-slot walk -/

/-- The outer walk of `cert246Kernel.stepEntryH` accumulates its per-slot value over the used
erase slots `0–3` of `s` and hands the total to the identity body. -/
theorem stepEntryH_walk {eraseEnc s : ℕ} {inner : ℕ → ℕ → ℕ → ℕ}
    {innerId : ℕ → ℕ → ℕ}
    {V : ℕ → ℕ → ℕ} (hinner : ∀ p g acc, inner p g acc = acc + V p g)
    (hpre : SlotPrefix eraseEnc s) :
    stepEntryH eraseEnc inner innerId s =
      innerId s
        (∑ j ∈ Finset.range 4,
          if slotUsed (slotField eraseEnc s j) = true then
            V (slotPart2 (slotField eraseEnc s j)) (slotTarget (slotField eraseEnc s j))
          else 0) := by
  rcases h0 : slotUsed (slotField eraseEnc s 0) with _ | _
  · simp [stepEntryH, Finset.sum_range_succ, fun j (hj : j < 4) => hpre.unused j.zero_le hj h0]
  · rcases h1 : slotUsed (slotField eraseEnc s 1) with _ | _
    · simp [stepEntryH, Finset.sum_range_succ, h0, hinner,
        fun j (h : 1 ≤ j) (hj : j < 4) => hpre.unused h hj h1]
    · rcases h2 : slotUsed (slotField eraseEnc s 2) with _ | _
      · simp [stepEntryH, Finset.sum_range_succ, h0, h1, h2, hinner,
          hpre.unused (i := 2) (j := 3) (by omega) (by omega) h2]
      · rcases h3 : slotUsed (slotField eraseEnc s 3) with _ | _ <;>
          simp [stepEntryH, Finset.sum_range_succ, h0, h1, h2, h3, hinner]

/-! ### The unhoisted slot recurrence -/

private theorem sumScan_sound (f : ℕ → ℕ → ℕ) (v : ℕ → ℕ)
    (hf : ∀ j a, f j a = a + v j) :
    ∀ count j accumulator,
      Nat.rec (motive := fun _ ↦ ℕ → ℕ → ℕ)
        (fun _ a ↦ a)
        (fun _ ih j' a ↦ ih (Nat.succ j') (f j' a))
        count j accumulator = accumulator + ∑ i ∈ Finset.range count, v (j + i)
  | 0, j, accumulator => by simp
  | count + 1, j, accumulator => by
    dsimp only
    rw [sumScan_sound f v hf count (Nat.succ j) (f j accumulator), hf j accumulator,
      sum_range_head v j count]
    simp only [Nat.succ_eq_add_one]
    omega

private theorem gateScan_sound (used : ℕ → Bool) (value : ℕ → ℕ)
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ j a, f j a = Bool.rec a (Nat.add a (value j)) (used j)) (n a : ℕ) :
    Nat.rec (motive := fun _ ↦ ℕ → ℕ → ℕ)
      (fun _ accumulator ↦ accumulator)
      (fun _ ih j' accumulator ↦ ih (Nat.succ j') (f j' accumulator))
      n 0 a = a + ∑ i ∈ Finset.range n, if used i = true then value i else 0 :=
  (sumScan_sound f (fun i ↦ if used i = true then value i else 0)
    (fun j accumulator ↦ by
      rcases hu : used j with _ | _ <;> simp [hf, hu]) n 0 a).trans (by simp)

/-- The direct slot walk is the double sum over the five erase descriptors of each signature. -/
theorem stepEntry_eq (csI pmI wI maskI fmask eraseEnc factT : ℕ)
    (tIn : Lean.RArray ℕ) (s t : ℕ) :
    stepEntry csI pmI wI maskI fmask eraseEnc factT tIn s t =
      ∑ j₁ ∈ Finset.range 5,
        (if slotUsed (slotField eraseEnc s j₁) = true then
          ∑ j₂ ∈ Finset.range 5,
            (if slotUsed (slotField eraseEnc t j₂) = true then
              factAt fmask factT
                (Nat.shiftLeft
                  (slotPart2 (slotField eraseEnc s j₁) +
                    slotPart2 (slotField eraseEnc t j₂)) 1) *
                treeAt csI pmI wI maskI tIn
                  (triIdx (slotTarget (slotField eraseEnc s j₁))
                    (slotTarget (slotField eraseEnc t j₂)))
            else 0)
        else 0) := by
  have inner : ∀ n p₁ g₁ a : ℕ,
      (Nat.rec (motive := fun _ ↦ ℕ → ℕ → ℕ)
        (fun _ accumulator ↦ accumulator)
        (fun _ ih₂ j₂ accumulator ↦
          ih₂ (Nat.succ j₂)
            ((fun f₂ ↦
              Bool.rec accumulator
                (Nat.add accumulator
                  (Nat.mul
                    (factAt fmask factT
                      (Nat.shiftLeft (Nat.add p₁ (slotPart2 f₂)) 1))
                    (treeAt csI pmI wI maskI tIn (triIdx g₁ (slotTarget f₂)))))
                (slotUsed f₂))
              (slotField eraseEnc t j₂)))
        n 0 a : ℕ) =
      a + ∑ j₂ ∈ Finset.range n,
        (if slotUsed (slotField eraseEnc t j₂) = true then
          factAt fmask factT
            (Nat.shiftLeft (p₁ + slotPart2 (slotField eraseEnc t j₂)) 1) *
            treeAt csI pmI wI maskI tIn (triIdx g₁ (slotTarget (slotField eraseEnc t j₂)))
        else 0) := fun n p₁ g₁ a ↦ gateScan_sound _ _ _ (fun _ _ ↦ rfl) n a
  unfold stepEntry
  generalize hn : (nat_lit 5 : ℕ) = n
  refine (gateScan_sound (fun j₁ ↦ slotUsed (slotField eraseEnc s j₁))
    (fun j₁ ↦
      ∑ j₂ ∈ Finset.range n,
        (if slotUsed (slotField eraseEnc t j₂) = true then
          factAt fmask factT
            (Nat.shiftLeft
              (slotPart2 (slotField eraseEnc s j₁) +
                slotPart2 (slotField eraseEnc t j₂)) 1) *
            treeAt csI pmI wI maskI tIn
              (triIdx (slotTarget (slotField eraseEnc s j₁))
                (slotTarget (slotField eraseEnc t j₂)))
        else 0)) _ ?_ n 0).trans ?_
  · intro j accumulator
    rcases hu : slotUsed (slotField eraseEnc s j) with _ | _
    · simp [hu]
    · simp only [hu]
      exact inner n _ _ accumulator
  · subst hn
    simp

end stepEntryH

end PrimeGaps.Gap246

end
