/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Certificate.Fast

/-! # Mathematical specification of the direct factorial-moment DAG -/

@[expose] public section

namespace cert246Kernel

/-- Decode a packed signature field into its multiset of positive even exponents. -/
def decodeSig (enc : ℕ) : Multiset ℕ :=
  ↑((List.range (enc % 16)).map fun j ↦ 2 * ((enc >>> (4 * (j + 1))) % 16))

end cert246Kernel
