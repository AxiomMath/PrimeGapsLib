/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.NumberTheory.LevelOfDistribution

import PrimeGapsTheory.Tactic.PaperTag

/-! # The Bombieri-Vinogradov theorem

The Bombieri-Vinogradov theorem, packaged as a proposition that is carried as a hypothesis
throughout the development, together with its standard reformulations.

## Main definitions

* `BombieriVinogradov`: the assertion that `ℕ` has level of distribution `θ` for all `θ < 1 / 2`.

## Main results

* `hasLevelOfDistribution_Prime`: the primes have level of distribution `θ` for all `θ < 1 / 2`.
* `bombieriVinogradov_explicit`: the estimate with an explicit constant.
* `bombieriVinogradov_bigO`: the estimate in big-`O` form.
-/

@[expose] public section

open Nat Real Finset Filter Asymptotics

/-- The **Bombieri-Vinogradov Theorem**, as a proposition.

`ℕ` has level of distribution `θ` for all `θ < 1 / 2`.

This will be a hypothesis throughout.
-/
def BombieriVinogradov : Prop :=
  ∀ θ < (1 / 2 : ℝ), ∀ A ≥ (1 : ℝ), ∃ c > (0 : ℝ), ∀ x ≥ (3 : ℝ),
    ∑ q ∈ Icc (1 : ℕ) ⌊x ^ θ⌋₊, ⨆ a : (ZMod q)ˣ, |(π(x; q, a) - π(x) / φ q : ℝ)| ≤ c * x / x.log ^ A

theorem BombieriVinogradov.hasLevelOfDistribution (hBV : BombieriVinogradov)
    {θ : ℝ} (hθ : θ < 1 / 2) : HasLevelOfDistribution Set.univ θ 1 := by
  simpa [HasLevelOfDistribution] using hBV _ hθ

/-- The **Bombieri-Vinogradov Theorem**.

The set of all primes has level of distribution `θ` for all `θ < 1 / 2`.
-/
@[pg_tag "bg246" "thm_BV"]
theorem hasLevelOfDistribution_Prime (hBV : BombieriVinogradov) {θ : ℝ} (hθ : θ < 1 / 2) :
    HasLevelOfDistribution Nat.Prime θ 1 := by
  rw [← Set.univ_inter Nat.Prime, hasLevelOfDistribution_inter_Prime]
  exact hBV.hasLevelOfDistribution hθ

/-- The **Bombieri-Vinogradov Theorem** (Explicit Formulation).

For all real numbers `θ < 1 / 2` and `A ≥ 1`, there is some constant `C > 0` (which depends on `A`)
such that for all `X ≥ 3`, the following inequality holds:
`∑_{q ≤ X^θ} max_{(q, a) = 1} |π(X; q, a) - π(X) / φ(q)| ≤ C A X / log(X)^A`.
-/
theorem bombieriVinogradov_explicit (hBV : BombieriVinogradov)
    {θ : ℝ} (hθ : θ < 1 / 2) {A : ℝ} (hA : 1 ≤ A) :
    ∃ C > (0 : ℝ), ∀ X ≥ (3 : ℝ), ∑ q ∈ Finset.Icc (1 : ℕ) ⌊X ^ θ⌋₊,
        ⨆ a : (ZMod q)ˣ, |(π(X; q, a) : ℝ) - (π(X) : ℝ) / q.totient| ≤
      C * X / (log X) ^ A := by
  simpa [BombieriVinogradov, hasLevelOfDistribution_def, Real.primeCountingWithin_univ,
    Real.primeCountingZModWithin_univ] using hBV θ hθ A hA

/-- The **Bombieri-Vinogradov Theorem** (Asymptotic Formulation).

This is a slightly weaker version of the Bombieri-Vinogradov Theorem, in that it does not strictly
require X ≥ 3, just that X be tending to infinity.
-/
theorem bombieriVinogradov_bigO (hBV : BombieriVinogradov)
    {θ : ℝ} (hθ : θ < 1 / 2) {A : ℝ} (hA : 1 ≤ A) :
    (fun X : ℝ ↦ ∑ q ∈ Finset.Icc (1 : ℕ) ⌊X ^ θ⌋₊,
      ⨆ a : (ZMod q)ˣ, |(π(X; q, a) : ℝ) - (π(X) : ℝ) / q.totient|) =O[atTop]
    (fun X : ℝ ↦ X / X.log ^ A) := by
  obtain ⟨C, hC_pos, hC⟩ := bombieriVinogradov_explicit hBV hθ hA
  rw [isBigO_atTop_iff_eventually_exists, eventually_atTop]
  refine ⟨3, fun b hb ↦ ⟨C, fun X hX ↦ ?_⟩⟩
  specialize hC X (by linarith)
  calc ‖∑ q ∈ Finset.Icc 1 ⌊X ^ θ⌋₊, ⨆ a : (ZMod q)ˣ, |(π(X; q, a) : ℝ) - π(X) / q.totient|‖
    _ = |(∑ q ∈ Finset.Icc 1 ⌊X ^ θ⌋₊,
            ⨆ a : (ZMod q)ˣ, |(π(X; q, a) : ℝ) - π(X) / q.totient| : ℝ)| := norm_eq_abs _
    _ = ∑ q ∈ Finset.Icc 1 ⌊X ^ θ⌋₊, ⨆ a : (ZMod q)ˣ, |(π(X; q, a) : ℝ) - π(X) / q.totient| :=
      abs_of_nonneg <| Finset.sum_nonneg fun _ _ ↦ iSup_nonneg fun _ ↦ abs_nonneg _
    _ ≤ C * X / (log X) ^ A := hC
    _ ≤ ‖C * X / (log X) ^ A‖ := le_norm_self _
    _ = C * ‖X / (log X) ^ A‖ := by
      rw [mul_div_assoc, norm_mul, norm_of_nonneg hC_pos.le]
