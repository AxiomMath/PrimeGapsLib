/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module


/-! # Dependency-free packed accessors for the packed certificate

This module is the complete shared environment of the hot numerical kernels. It keeps
their reduction language to natural-number bit operations, booleans, and `Lean.RArray`,
without importing Mathlib or either of the other certificate implementations.
-/

@[expose] public section

namespace cert246Data

/-- Apply `k` to `n` with `n` reduced to constructor form first, at any result sort;
`eagerAt k n = k n`. -/
noncomputable def eagerAt.{u} {α : Sort u} (k : Nat → α) (n : Nat) : α :=
  Nat.rec (motive := fun _ => α) (k (nat_lit 0)) (fun i _ => k (Nat.succ i)) n

/-- `eagerAt` applies its function. -/
theorem eagerAt_eq.{u} {α : Sort u} (k : Nat → α) (n : Nat) : eagerAt k n = k n := by
  cases n <;> rfl

/-- Field `i` of a packed-leaf tree with `2^cs` fields of width `w` per leaf. -/
noncomputable def treeAt (cs pmask w mask : Nat) (tree : Lean.RArray Nat) (i : Nat) : Nat :=
  Nat.land
    (Nat.shiftRight (eagerAt tree.get (Nat.shiftRight i cs)) (Nat.mul w (Nat.land i pmask)))
    mask

/-- Index of the unordered pair `(s,t)` in a triangular table. -/
noncomputable def triIdx (s t : Nat) : Nat :=
  Bool.rec
    (Nat.add (Nat.div (Nat.mul t (Nat.succ t)) 2) s)
    (Nat.add (Nat.div (Nat.mul s (Nat.succ s)) 2) t)
    (Nat.ble (Nat.succ t) s)

/-- Signature `i`: part count in the low nibble, followed by halved parts. -/
noncomputable def sigField (sigEnc i : Nat) : Nat :=
  Nat.land (Nat.shiftRight sigEnc (Nat.shiftLeft i 6)) 18446744073709551615

/-- Number of parts in an encoded signature. -/
noncomputable def sigCount (enc : Nat) : Nat := Nat.land enc 15

/-- Halved part at position `position` in an encoded signature. -/
noncomputable def sigNib (enc position : Nat) : Nat :=
  Nat.land (Nat.shiftRight enc (Nat.shiftLeft (Nat.succ position) 2)) 15

/-- Remove the part at `position` from an encoded signature. -/
noncomputable def eraseAt (enc position : Nat) : Nat :=
  Nat.add
    (Nat.sub
      (Nat.land enc (Nat.sub (Nat.shiftLeft 1 (Nat.shiftLeft (Nat.succ position) 2)) 1))
      1)
    (Nat.shiftLeft (Nat.shiftRight enc (Nat.shiftLeft (Nat.add position 2) 2))
      (Nat.shiftLeft (Nat.succ position) 2))

/-- Erase-slot descriptor `j` of signature `s`. -/
noncomputable def slotField (eraseEnc s j : Nat) : Nat :=
  Nat.land (Nat.shiftRight eraseEnc (Nat.shiftLeft (Nat.add (Nat.mul 5 s) j) 4)) 65535

/-- Whether an erase-slot descriptor is used. -/
noncomputable def slotUsed (field : Nat) : Bool := Nat.beq (Nat.land field 1) 1

/-- Halved erased part in a slot descriptor. -/
noncomputable def slotPart2 (field : Nat) : Nat := Nat.land (Nat.shiftRight field 1) 15

/-- Erased-signature target in a slot descriptor. -/
noncomputable def slotTarget (field : Nat) : Nat := Nat.land (Nat.shiftRight field 5) 511

/-- Label descriptor `i`, packed into one 32-bit field. -/
noncomputable def labelField (labelEnc i : Nat) : Nat :=
  Nat.land (Nat.shiftRight labelEnc (Nat.shiftLeft i 5)) 4294967295

/-- Slack exponent of a packed label descriptor. -/
noncomputable def labelA (field : Nat) : Nat := Nat.land field 31

/-- Signature index of a packed label descriptor. -/
noncomputable def labelSignature (field : Nat) : Nat :=
  Nat.land (Nat.shiftRight field 5) 511

/-- Signature part sum of a packed label descriptor. -/
noncomputable def labelDegree (field : Nat) : Nat :=
  Nat.land (Nat.shiftRight field 14) 31

/-- Coefficient sign bit of a packed label descriptor. -/
noncomputable def labelSign (field : Nat) : Nat :=
  Nat.land (Nat.shiftRight field 19) 1

/-- Group descriptor `group`, packed into one 64-bit field. -/
noncomputable def groupField (groupEnc group : Nat) : Nat :=
  Nat.land (Nat.shiftRight groupEnc (Nat.shiftLeft group 6)) 18446744073709551615

/-- Start of a group in the array it indexes. -/
noncomputable def groupStart (field : Nat) : Nat := Nat.land field 2047

/-- Number of members of a group. -/
noncomputable def groupSize (field : Nat) : Nat :=
  Nat.land (Nat.shiftRight field 11) 2047

/-- First common degree of a group, at bit 22. -/
noncomputable def groupLowDegree (field : Nat) : Nat :=
  Nat.land (Nat.shiftRight field 22) 63

/-- Second common degree of a group, at bit 28. -/
noncomputable def groupHighDegree (field : Nat) : Nat :=
  Nat.land (Nat.shiftRight field 28) 63

/-- Inverse group-and-offset descriptor `i`, packed into one 32-bit field. -/
noncomputable def inverseField (inverseEnc i : Nat) : Nat :=
  Nat.land (Nat.shiftRight inverseEnc (Nat.shiftLeft i 5)) 4294967295

/-- Group component of an inverse descriptor. -/
noncomputable def inverseGroup (field : Nat) : Nat := Nat.land field 255

/-- Offset component of an inverse descriptor. -/
noncomputable def inverseOffset (field : Nat) : Nat :=
  Nat.land (Nat.shiftRight field 8) 2047

/-- Sparse-transform key `entry`, packed into one 32-bit field. -/
noncomputable def keyField (keyEnc entry : Nat) : Nat :=
  Nat.land (Nat.shiftRight keyEnc (Nat.shiftLeft entry 5)) 4294967295

/-- Group component of a sparse-transform key. -/
noncomputable def keyGroup (field : Nat) : Nat := Nat.land field 255

/-- Target signature of a sparse-transform key. -/
noncomputable def keyTarget (field : Nat) : Nat :=
  Nat.land (Nat.shiftRight field 8) 511

/-- Factorial as a dependency-free first-order fold. -/
noncomputable def factorialFold (n : Nat) : Nat :=
  Nat.rec (motive := fun _ ↦ Nat) 1 (fun cursor value ↦ Nat.mul (Nat.succ cursor) value) n

/-- Descending factorial as a dependency-free first-order fold. -/
noncomputable def descFactorialFold (n k : Nat) : Nat :=
  Nat.rec (motive := fun _ ↦ Nat) 1 (fun cursor value ↦ Nat.mul (Nat.sub n cursor) value) k

end cert246Data
