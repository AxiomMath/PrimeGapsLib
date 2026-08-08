/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.Common.Decoupling
import PrimeGapsTheory.Tactic.PaperTag

/-!
# Möbius decoupling for the first moment

Defines the decoupled first-moment sum and derives its evaluation from the common tuple-domain
Möbius identity.

## Main definitions

* `SigmaFull`: The unrestricted decoupled sum.

## Main results

* `lem_S1_mobius_coprime`: Expresses the first-moment sum in decoupled form.
-/

@[expose] public section

open scoped ArithmeticFunction.Moebius

open scoped BigOperators

namespace PrimeGaps
namespace LemS1RestrictSij

/-- The summand / weight of a configuration. -/
noncomputable def T {k : ℕ} (lam : (Fin k → ℕ) → ℝ)
    (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ) (d e : Fin k → ℕ) : ℝ :=
  (∏ i, (Nat.totient (u i) : ℝ)) *
  (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
      ((μ (s p.1 p.2) : ℤ) : ℝ)) *
  (lam d * lam e / (((∏ i, d i) : ℕ) * ((∏ i, e i) : ℕ)))

/-- `Σ_full = ∑_{(u,s,d,e)} T`, summing `T` over all configurations. -/
noncomputable def SigmaFull {k : ℕ} (D : Finset (Fin k → ℕ)) (lam : (Fin k → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ D, ∑ u ∈ uDomain d e, ∑ s ∈ sDomain d e, T lam u s d e

/-- The decoupled `u` -sum produced by `lem_S1_decouple_lcm` — namely
`∑_{d,e} (∑_u ∏_i φ(u_i)) · 1[(d_i,e_j)=1 ∀ i≠j] · λ(d)λ(e)/∏_i(d_i e_j)` — is expanded, via the
per-pair Möbius identity `∑_{s ∣ (d_i,e_j)} μ(s) = 1[(d_i,e_j)=1]`, into the full Möbius-decoupled
sum `Σ_full`: the cross-coprimality indicator is replaced by an extra sum over off-diagonal divisor
tuples `s = (s_{ij})` weighted by `∏_{i≠j} μ(s_{ij})`.
-/
@[pg_tag "bg246" "lem_S1_mobius_coprime"]
theorem lem_S1_mobius_coprime {k : ℕ} (D : Finset (Fin k → ℕ)) (lam : (Fin k → ℕ) → ℝ) :
    (∑ d ∈ D, ∑ e ∈ D, (∑ u ∈ Fintype.piFinset (fun i ↦ (Nat.gcd (d i) (e i)).divisors),
            (∏ i, (Nat.totient (u i) : ℝ))) * (if (∀ i j, i ≠ j → Nat.Coprime (d i) (e j))
            then lam d * lam e / (∏ i, ((d i : ℝ) * e i)) else 0)) = SigmaFull D lam := by
  unfold SigmaFull
  refine Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun e _ ↦ ?_
  simp only [uDomain]
  have hK : ∀ u : Fin k → ℕ, (∑ s ∈ sDomain d e, T lam u s d e) = (∏ i, (Nat.totient (u i) : ℝ)) *
        (lam d * lam e / (((∏ i, d i) : ℕ) * ((∏ i, e i) : ℕ))) *
        (if (∀ i j, i ≠ j → Nat.Coprime (d i) (e j)) then (1 : ℝ) else 0) := by
    intro u
    unfold T
    rw [← Finset.sum_mul, ← Finset.mul_sum, msum d e]
    ring
  rw [Finset.sum_congr rfl fun u _ ↦ hK u, ← Finset.sum_mul, ← Finset.sum_mul]
  have hden : (∏ i, ((d i : ℝ) * e i)) = (((∏ i, d i) : ℕ) * ((∏ i, e i) : ℕ) : ℝ) := by
    push_cast
    rw [Finset.prod_mul_distrib]
  by_cases hP : ∀ i j, i ≠ j → Nat.Coprime (d i) (e j)
  · rw [if_pos hP, if_pos hP, mul_one, hden]
  · rw [if_neg hP, if_neg hP, mul_zero, mul_zero]

end LemS1RestrictSij

end PrimeGaps
