/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.Primorial
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import PrimeGapsTheory.Tactic.PaperTag

/-! # The singular series

The singular series `𝔖 γ = ∏_p (1 - 1/p) / (1 - γ p / p)` attached to a local-density function
`γ`, and its evaluation for the indicator density `γ_W` of coprimality to a primorial.

## Main definitions

* `PrimeGaps.singularSeries`: the singular series `𝔖 γ`, with scoped notation `𝔖`.
* `PrimeGaps.gammaW`: the totally multiplicative density `γ_W n = 𝟙[(n, W) = 1]`.

## Main results

* `PrimeGaps.singularSeries_gammaW`: `𝔖 (γ_W) = φ(W) / W` for `W` a primorial.

## Implementation notes

`singularSeries` only reads `γ` at primes, so the value of `gammaW` at composites is irrelevant;
the totally multiplicative extension is chosen for convenience.
-/

@[expose] public section

namespace PrimeGaps

/-- The singular series associated to the local-density function `γ`. -/
@[pg_tag "bg246" "not_singular_series"]
noncomputable def singularSeries (γ : ℕ → ℝ) : ℝ :=
  ∏' p : ℕ, if p.Prime then ((1 - 1 / p) / (1 - γ p / p) : ℝ) else 1

/-- The notation `𝔖` denotes `singularSeries`. -/
@[pg_tag "bg246" "not_singular_series"]
scoped notation "𝔖" => singularSeries

@[pg_tag "bg246" "not_singular_series"]
lemma singularSeries_primorial {γ : ℕ → ℝ} {N : ℕ} (hN₀ : ∀ p : ℕ, p.Prime → p ≤ N → γ p = 0)
    (hN₁ : ∀ p : ℕ, p.Prime → N < p → γ p = 1) :
    𝔖 γ = (primorial N).totient / primorial N := by
  rw [singularSeries, ← Rat.cast_natCast, Nat.totient_eq_mul_prod_factors, Rat.cast_mul,
    Rat.cast_natCast, mul_div_cancel_left₀ _ (by simp [primorial_ne_zero]), Rat.cast_prod,
    tprod_eq_prod (s := N.primesLE) fun p hp ↦ ?_, primeFactors_primorial]
  · refine Finset.prod_congr rfl fun p hp ↦ ?_
    rw [Nat.mem_primesLE] at hp
    simp [hp, hN₀]
  · rw [Nat.mem_primesLE] at hp
    split_ifs with h
    · rw [hN₁ _ h (by grind), div_self]
      refine sub_ne_zero_of_ne <| ne_of_gt <| (div_lt_comm₀ ?_ ?_).mpr ?_
      · simp [h.pos]
      · positivity
      · simp [h.one_lt]
    · rfl

/-- **Maynard §4 `def_gamma_W`.** The totally multiplicative function `γ_W(n) = 𝟙[(n, W) = 1]`
associated to a positive integer `W`; at a prime `p` it is `𝟙[p ∤ W]`. -/
@[pg_tag "bg246" "def_gamma_W"]
noncomputable def gammaW (W : ℕ) (n : ℕ) : ℝ := if n.Coprime W then 1 else 0

/-- **Maynard §4 `lem_singular_series_gamma_W`.** For `W = primorial N`,
`𝔖(γ_W) = φ(W) / W`. -/
@[pg_tag "bg246" "lem_singular_series_gamma_W"]
lemma singularSeries_gammaW (N : ℕ) :
    𝔖 (gammaW (primorial N)) = (primorial N).totient / primorial N := by
  refine singularSeries_primorial (γ := gammaW (primorial N)) (N := N) ?_ ?_
  · intro p hp hpN
    simp [gammaW, Nat.Coprime, Nat.gcd_eq_left ((hp.dvd_primorial_iff (n := N)).mpr hpN), hp.ne_one]
  · intro p hp hpN
    have hndvd : ¬ p ∣ primorial N := by
      rw [hp.dvd_primorial_iff (n := N)]
      exact Nat.not_le.mpr hpN
    simp [gammaW, (hp.coprime_iff_not_dvd).mpr hndvd]

end PrimeGaps
