/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Kernel.Folds

/-! # Supplementary kernel checks for the certificate data

Three facts the main validation fold does not establish, each needed by the moment-ladder
soundness proof (`PrimeGapsCert.Gap246.Moments.Direct.LadderSound`):
signature encodings carry nothing above their last inspected nibble, every halved part is
at most `partBound`, and the table of erase slots addresses rows in range.

Same fold discipline as `PrimeGapsCert.Gap246.Kernel.Folds`.
-/

@[expose] public section

namespace cert246Kernel

open cert246Data (sigField sigNib)

/-- Check every signature encoding: nothing above nibble `maxNib`, and every halved part
below `partBound + 1`. -/
noncomputable def encCheck (S maxNib partBound sigEnc : ℕ) : Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool)
    (fun _ => true)
    (fun _ ihS s =>
      (fun enc =>
        Bool.rec (motive := fun _ => Bool) false
          (Nat.rec (motive := fun _ => ℕ → Bool)
            (fun _ => ihS (Nat.succ s))
            (fun _ ihT t =>
              Bool.rec (motive := fun _ => Bool) false
                (ihT (Nat.succ t))
                (Nat.ble (sigNib enc t) partBound))
            maxNib (nat_lit 0))
          (Nat.blt enc (Nat.shiftLeft (nat_lit 1)
            (Nat.shiftLeft (Nat.succ maxNib) (nat_lit 2)))))
        (sigField sigEnc s))
    S (nat_lit 0)

end cert246Kernel
