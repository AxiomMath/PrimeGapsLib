/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.ArithmeticFunction.LYTransform.Specialized
public import PrimeGapsTheory.Gap246.Sieve.SupportSplit

/-!
# The ε-enlarged sieve weight and its permissible support

This file defines the enlarged sieve weight `λ_ε` of the ε-enlarged variational
problem built over the Maynard-600 development.  It is the
`R → R^{1+ε}` analogue of `PrimeGaps.l₀` (`l₀_apply`): the divisor bound in the
antidiagonal support is relaxed from `R` to `R^{1+ε}`, while the argument of `F`
still normalises by `log R` (with the *original* `R = sieveTruncation N δ θ`), so
that a tuple with `∏ rᵢ ≤ R^{1+ε}` lands in the enlarged simplex `𝒯_ε`.

* `lambdaEps` — the enlarged weight, the `l₀_apply` formula over promoted
  `Finset.permissibleSupport` at the enlarged radius.
* `lem_lambda_perm` — `lambdaEps` has `epsPermissible` support (mirrors the 600
  `hasPermissibleSupport_l₀`).
-/

@[expose] public section

open scoped ArithmeticFunction.Moebius

open Finset

namespace Gaps246

variable {k N : ℕ} {δ θ ε : ℝ} {d : Fin k → ℕ}

/-- **`def_lambda_from_F` (ε-enlarged).** The enlarged sieve weight `λ_ε`, defined by
the `l₀_apply` formula over the promoted permissible support at the enlarged radius. Note the
argument of `F` normalises by `log R` with the *original* `R = sieveTruncation N δ θ`
(not `R^{1+ε}`), so `∑ᵢ log rᵢ / log R ≤ 1 + ε` puts the point inside `𝒯_ε`. -/
noncomputable def lambdaEps (k N : ℕ) (δ θ ε : ℝ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (d : Fin k → ℕ) : ℝ :=
  (∏ i, (μ (d i) : ℝ) * (d i)) * ∑ r ∈ Finset.permissibleSupport k
      ⌊(PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε)⌋₊ (PrimeGaps.sieveModulus N)
      with (∀ i, d i ∣ r i),
      (1 / (∏ i, (Nat.totient (r i) : ℝ))) *
        F (WithLp.toLp 2 (fun i ↦ Real.log (r i) / Real.log (PrimeGaps.sieveTruncation N δ θ)))

/-- **`lem_lambda_0_permissible_support` (ε-enlarged).** The enlarged weight `λ_ε`
has `epsPermissible` support: `λ_ε d = 0` unless every `dᵢ ≥ 1`, the product
`∏ dᵢ ≤ R^{1+ε}`, is coprime to `W N`, and is squarefree.  Mirrors the 600
`PrimeGaps.hasPermissibleSupport_l₀`. -/
theorem lem_lambda_perm (k N : ℕ) (δ θ ε : ℝ) (F : EuclideanSpace ℝ (Fin k) → ℝ) :
    epsPermissible k N δ θ ε (lambdaEps k N δ θ ε F) := by
  intro d hd
  unfold lambdaEps
  by_cases hpos : ∀ i, 1 ≤ d i
  · -- Every `dᵢ ≥ 1`, so one of the product/coprime/squarefree conditions fails;
    -- then no `r` in the enlarged support has `dᵢ ∣ rᵢ`, so the filtered sum is `0`.
    apply mul_eq_zero_of_right
    rw [Finset.sum_filter]
    refine Finset.sum_eq_zero fun r hr ↦ ?_
    rw [if_neg]
    intro hdvd
    rw [Finset.mem_permissibleSupport_iff] at hr
    obtain ⟨hprod, hcop, hsq⟩ := hr
    have hdr : ∏ i, d i ∣ ∏ i, r i := Finset.prod_dvd_prod_of_dvd _ _ fun i _ ↦ hdvd i
    refine hd ⟨hpos, ?_, Nat.Coprime.coprime_dvd_left hdr hcop, hsq.squarefree_of_dvd hdr⟩
    calc (∏ i, d i : ℝ) ≤ (∏ i, r i : ℝ) := by
          exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hsq.ne_zero) hdr
      _ ≤ ⌊(PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε)⌋₊ := by exact_mod_cast hprod
      _ ≤ _ := Nat.floor_le (Real.rpow_nonneg (by positivity) _)
  · -- Some `dᵢ = 0`, so the `∏ μ(dᵢ)·dᵢ` factor vanishes.
    apply mul_eq_zero_of_left
    push Not at hpos
    obtain ⟨i, hi⟩ := hpos
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [show d i = 0 from by omega]
    simp

end Gaps246
