/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module


public import PrimeGapsTheory.NumberTheory.PrimeCountingSubset

import PrimeGapsTheory.Tactic.PaperTag

/-! # Level of distribution

The level of distribution of a set of natural numbers: a measure of how far one can push
equidistribution of the set over residue classes on average over the modulus.

## Main definitions

* `Nat.HasLevelOfDistribution`: the set `S` has level of distribution `θ` relative to `Ξ`.

## Implementation notes

The level of distribution is usually defined for a set of primes. Since it makes no difference
whether one considers the set of primes or its intersection with a set `S`, we define it for an
arbitrary `S` instead; `hasLevelOfDistribution_inter_Prime` records that the two agree.
-/

@[expose] public section

open Real

namespace Nat

/-- A set `S` of natural numbers has level of distribution `θ : ℝ` with respect to `Ξ : ℕ` if for
all `A > 1`, there is some constant `c > 0` such that for all `x ≥ 3`,
$$\sum_{\substack{q \leq x^{\theta} \\ (q, Ξ) = 1}} \max_{(q, a) = 1}
\left\lvert \pi_S(x; q, a) - \frac{\pi_S(X)}{\varphi(q)} \right\rvert ≤ C A \frac{X}{\log(X)}$$. -/
@[pg_tag "bg246" "def_level_of_distribution"]
def HasLevelOfDistribution (S : Set ℕ) (θ : ℝ) (Ξ : ℕ) : Prop :=
  ∀ A ≥ (1 : ℝ), ∃ c > (0 : ℝ), ∀ x ≥ (3 : ℝ),
    ∑ q ∈ Finset.Icc (1 : ℕ) ⌊x ^ θ⌋₊ with Nat.gcd q Ξ = 1,
      ⨆ a : (ZMod q)ˣ, |(π[S](x; q, a) : ℝ) - (π[S](x) : ℝ) / q.totient| ≤ c * x / (Real.log x) ^ A

lemma hasLevelOfDistribution_def (S : Set ℕ) (θ : ℝ) (Ξ : ℕ) : HasLevelOfDistribution S θ Ξ ↔
    ∀ A ≥ (1 : ℝ), ∃ c > (0 : ℝ), ∀ x ≥ (3 : ℝ),
      ∑ q ∈ Finset.Icc (1 : ℕ) ⌊x ^ θ⌋₊ with Nat.gcd q Ξ = 1,
        ⨆ a : (ZMod q)ˣ, |(π[S](x; q, a) : ℝ) - (π[S](x) : ℝ) / q.totient| ≤
        c * x / (Real.log x) ^ A := Iff.rfl

lemma hasLevelOfDistribution_inter_Prime {S : Set ℕ} {θ : ℝ} {Ξ : ℕ} :
    HasLevelOfDistribution (S ∩ Prime) θ Ξ ↔ HasLevelOfDistribution S θ Ξ := by
  rw [show (S ∩ Prime : Set ℕ) = S ∩ {p | p.Prime} from rfl]
  simp only [hasLevelOfDistribution_def, Real.primeCountingZModWithin_inter_setOf_prime,
    Real.primeCountingWithin_inter_setOf_prime]

lemma hasLevelOfDistribution_zero {S : Set ℕ} {Ξ : ℕ} : HasLevelOfDistribution S 0 Ξ := by
  simp only [hasLevelOfDistribution_def, Real.rpow_zero, floor_one, Finset.Icc_self]
  intro _ _
  refine ⟨1, by positivity, fun x _ ↦ ?_⟩
  calc _
      = ∑ q ∈ {1}, ⨆ a : (ZMod q)ˣ, |(π[S](x; q, a) : ℝ) - π[S](x) / (φ q)| := by
        congr
        simp
    _ = ⨆ a : (ZMod 1)ˣ, |(π[S](x; 1, a) : ℝ) - π[S](x) / (φ 1)| := Finset.sum_singleton _ _
    _ = 0 := by simp
    _ ≤ _ := div_nonneg (by positivity) (by positivity [log_nonneg (x := x) <| by linarith])

lemma hasLevelOfDistribution_of_le {S : Set ℕ} {ϑ : ℝ} {Ξ : ℕ}
    (hlevel : HasLevelOfDistribution S ϑ Ξ) {θ : ℝ} (hθ : θ ≤ ϑ) :
    HasLevelOfDistribution S θ Ξ := by
  rw [hasLevelOfDistribution_def]
  intro A hA
  obtain ⟨c, hc₁, hc₂⟩ := hlevel A hA
  refine ⟨c, hc₁, fun x hx ↦ ?_⟩
  have h_le_pow_vartheta : x ^ θ ≤ x ^ ϑ :=
    (Real.strictMono_rpow_of_base_gt_one (b := x) (by linarith)).monotone hθ
  calc _
      ≤ ∑ q ∈ Finset.Icc 1 ⌊x ^ ϑ⌋₊ with q.gcd Ξ = 1,
            ⨆ a : (ZMod q)ˣ, |(π[S](x; q, a) : ℝ) - π[S](x) / (φ q)| := by
        gcongr
        intro i hi₁ hi₂
        simp only [Finset.mem_filter, Finset.mem_Icc, not_and, and_imp] at hi₁ hi₂
        apply iSup_nonneg
        grind
    _ ≤ _ := hc₂ x hx

lemma hasLevelOfDistribution_of_nonpos {S : Set ℕ} {θ : ℝ} (hθ : θ ≤ 0) {Ξ : ℕ} :
    HasLevelOfDistribution S θ Ξ :=
  hasLevelOfDistribution_of_le hasLevelOfDistribution_zero hθ

end Nat
