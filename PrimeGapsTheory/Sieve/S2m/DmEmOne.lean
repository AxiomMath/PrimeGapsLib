/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Nat.Prime.Defs

import PrimeGapsTheory.Tactic.PaperTag

/-!
# A compositeness criterion

A divisibility criterion that rules out primality.

## Main results

* `lem_S2m_dm_em_one`: A number with a proper divisor at least two is not prime.
-/

@[expose] public section

namespace PrimeGaps

/-- Compositeness from a non-trivial divisor: if `2 ≤ m < x` and `m ∣ x` then `x` is not prime. -/
@[pg_tag "bg246" "lem_S2m_dm_em_one"]
theorem lem_S2m_dm_em_one (x m : ℕ) (hm : 2 ≤ m) (hx : m < x) (hdvd : m ∣ x) :
    ¬ x.Prime := fun hp ↦ by
  rcases hp.eq_one_or_self_of_dvd m hdvd with h | h <;> omega

end PrimeGaps
