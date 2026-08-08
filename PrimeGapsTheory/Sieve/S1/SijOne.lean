/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.Common.SijOne
public import PrimeGapsTheory.Sieve.S1.Decoupling
public import PrimeGapsTheory.Sieve.S1.Expansion

import PrimeGapsTheory.Tactic.PaperTag

/-!
# The diagonal off-diagonal tuple

Evaluates the first-moment sum when every off-diagonal entry equals one.

## Main results

* `lem_S1_sij_one`: Identifies the all-one off-diagonal contribution.
-/

@[expose] public section

open scoped ArithmeticFunction.Moebius

namespace PrimeGaps

open GPYSieveS1 PrimeGaps.LemS1RestrictSij in
/-- The `s ≡ 1` contribution to the `S₁` weighted sum, simplified: on each contributing tuple `u`
the moebius-square weight `∏_i μ(u_i)²/φ(u_i)` folds into the squared GPY weight, giving
`PrimeGaps.lToY lam u ^ 2 / ∏_i φ(u_i)`. No squarefree hypothesis is needed, since
`PrimeGaps.lToY lam u = 0` on non-squarefree `u`.
-/
@[pg_tag "bg246" "lem_S1_sij_one"]
theorem lem_S1_sij_one {k : ℕ} (N : ℕ) (W : ℕ) (lam : (Fin k → ℕ) →₀ ℝ) :
    (N / (W : ℝ)) * (∑' u : Fin k → ℕ, if (∀ i, 1 ≤ u i) ∧ RestrictedCoprime u (fun _ _ ↦ 1) then
            (∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ)) *
            PrimeGaps.lToY lam u * PrimeGaps.lToY lam u
          else 0)
      =
    (N / (W : ℝ)) * (∑' u : Fin k → ℕ, if (∀ i, 1 ≤ u i) ∧ RestrictedCoprime u (fun _ _ ↦ 1) then
            PrimeGaps.lToY lam u ^ 2 / (∏ i, (Nat.totient (u i) : ℝ))
          else 0) :=
  mul_tsum_mobiusSq_weight_mul_self _ (fun n ↦ (Nat.totient n : ℝ)) (lToY lam) _ fun _ ↦
    or_iff_not_imp_right.mpr squarefree_of_lToY_ne_zero

end PrimeGaps
