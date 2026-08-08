/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.S1.SijCoprimeToW

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Off-diagonal dichotomy

Splits the restricted first-moment sum according to whether all off-diagonal entries are one.

## Main results

* `lem_S1_sij_dichotomy`: Gives the off-diagonal one-or-nontrivial decomposition.
-/

@[expose] public section

namespace PrimeGaps

open GPYSieveS1 in
/-- For a contributing summand (`PrimeGaps.lToY` nonzero on both `boldA u s` and `boldB u s`)
and distinct indices `i ≠ j`, the shared-factor quantity `s i j` is either `1`, or every prime
dividing it is strictly greater than the cutoff `⌊D₀ N⌋₊`.
-/
@[pg_tag "bg246" "lem_S1_sij_dichotomy"]
theorem lem_S1_sij_dichotomy {k : ℕ} (N : ℕ) (R : ℝ) (W : ℕ)
    (hW : W = primorial ⌊PrimeGaps.D₀ N⌋₊) (lam : (Fin k → ℕ) →₀ ℝ)
    (hlam : lam.HasPermissibleSupport ⌊R⌋₊ W)
    (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ)
    (hnz : PrimeGaps.lToY lam (boldA u s) ≠ 0 ∧ PrimeGaps.lToY lam (boldB u s) ≠ 0)
    (i j : Fin k) (hij : i ≠ j) :
    s i j = 1 ∨ (∀ q, q.Prime → q ∣ s i j → ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < q) := by
  have hcop := lem_S1_sij_coprime_to_W R W lam hlam u s hnz i j hij
  refine Or.inr fun q hq hqd ↦ ?_
  have hqW : ¬ q ∣ W := hq.coprime_iff_not_dvd.mp (hcop.coprime_dvd_left hqd)
  rw [hW, hq.dvd_primorial_iff] at hqW
  omega

end PrimeGaps
