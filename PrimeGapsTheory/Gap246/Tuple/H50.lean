/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.NumberTheory.Admissible

/-!
# The admissible 50-tuple of diameter 246

`H50` is Engelsma's narrowest admissible 50-tuple (diameter 246), the tuple
Polymath8b uses for `H₁ ≤ 246`.

Both the diameter (`= 246`) and admissibility are re-verified in-kernel by
`decide` on the explicit `Finset` literal — the literal is not trusted, the
kernel checks it — exactly as the 600 development does for its 105-tuple
`H105` (`PrimeGapsTheory.NumberTheory.Admissible`), including the raised `maxRecDepth`
needed to evaluate the 50-deep `insert` chain.
-/

@[expose] public section

open scoped Finset

namespace Gaps246

open Finset

/-- Engelsma's narrowest admissible 50-tuple, normalized to `min = 0`, `max = 246`
(diameter 246); the tuple behind Polymath8b's `H₁ ≤ 246`. -/
def H50 : Finset ℕ :=
  {0, 4, 6, 16, 30, 34, 36, 46, 48, 58, 60, 64, 70, 78, 84, 88, 90, 94, 100, 106,
   108, 114, 118, 126, 130, 136, 144, 148, 150, 156, 160, 168, 174, 178, 184, 190,
   196, 198, 204, 210, 214, 216, 220, 226, 228, 234, 238, 240, 244, 246}

/-- `H50` has 50 elements. -/
theorem card_H50 : #H50 = 50 := by
  set_option maxRecDepth 4000 in decide

/-- The diameter of `H50` is 246. -/
theorem diameter_H50 : H50.diameter = 246 := by
  set_option maxRecDepth 4000 in decide

/-- `H50` is admissible: for every prime `p` it omits a residue class mod `p`
(only `p ≤ 50` need checking — for `p > 50` a 50-element set cannot fill `p`
classes). -/
theorem admissible_H50 : H50.Admissible := by
  set_option maxRecDepth 4000 in decide

end Gaps246
