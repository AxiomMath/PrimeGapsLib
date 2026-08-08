/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Arithmetic.ConvergentSums
public import PrimeGapsTheory.Arithmetic.SingularSeries

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Prime density bounds

Primewise density bounds for the `W`-tricked Maynard sieve datum.

## Main definitions

* `SatisfiesH3`: The third density hypothesis for a family of sieve data.

## Main results

* `maynardSieveDatum_γ_prime_div_le_half`: The prime density ratio is at most one half.
* `gammaPrime_satisfiesH3`: The `W`-tricked prime density satisfies the third density hypothesis.
-/

@[expose] public section

open Filter Topology
open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.detotient

namespace PrimeGaps

/-- Per-prime two-sided bound for Maynard's `γ_g`.  Assuming `2 ∣ W N` (the
`N → ∞` regime), for every prime `p` we have `0 ≤ γ_g(p)/p ≤ 1 - A₁ = 1/2`.

Here `γ_g = (maynardSieveDatum N hN hD).γ`.  The lower bound is the `γ_nonneg`
axiom of the sieve datum; the upper bound is the `γ_density` axiom
(`γ(p)/p ≤ 1 - A₁ = 1/2`). -/
@[pg_tag "bg246" "slem_gg_growth"]
theorem maynardSieveDatum_γ_prime_div_le_half
    (N : ℕ) (hN : 0 < N) (hD : 2 ≤ PrimeGaps.D₀ N) (p : ℕ) (hp : p.Prime) :
    0 ≤ (maynardSieveDatum N hN hD).γ p / p ∧
      (maynardSieveDatum N hN hD).γ p / p ≤ 1 - (1 / 2 : ℝ) := by
  refine ⟨div_nonneg ((maynardSieveDatum N hN hD).γ_nonneg p) (Nat.cast_nonneg _), ?_⟩
  simpa using (maynardSieveDatum N hN hD).γ_density p hp

/-- Hypothesis `(H3)`: the per-prime sieve density bound with exceptional modulus `V` and
constant `A_3`. For every prime `p`: `0 <= gamma p`, and `gamma p / p` is bounded by `0` when
`p | V` and by `1 - 1/A_3` otherwise. -/
def SatisfiesH3 (γ : ℕ → ℝ) (V : ℕ) (A₃ : ℝ) : Prop :=
  ∀ p : ℕ, p.Prime → 0 ≤ γ p ∧ γ p / p ≤ (if p ∣ V then 0 else 1 - 1 / A₃)

/-- If `2 ∣ W`, the local density `gamma_g(W, ·)` satisfies hypothesis `(H3)` with exceptional
modulus `W` and constant `A₃ = 2`. -/
@[pg_tag "bg246" "slem_gg_H3"]
theorem gammaPrime_satisfiesH3 (W : ℕ) (h2dvd : 2 ∣ W) :
    SatisfiesH3 (PrimeGaps.S2mSingularSeries.gammaPrime W) W 2 := by
  intro p hp
  simp only [PrimeGaps.S2mSingularSeries.gammaPrime]
  by_cases hpW : p ∣ W
  · simp [hpW]
  · simp only [hpW, if_false]
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      rcases hp.eq_two_or_odd with h2 | hodd
      · exact absurd (h2 ▸ h2dvd) hpW
      · omega
    have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    have hden_pos : (0 : ℝ) < (p : ℝ) ^ 3 - (p : ℝ) ^ 2 - 2 * (p : ℝ) + 1 := by nlinarith
    refine ⟨div_nonneg (by positivity) (by linarith), ?_⟩
    rw [div_div, div_le_iff₀ (by positivity)]
    nlinarith [hden_pos, sq_nonneg ((p : ℝ) - 1), hpR]

open scoped PrimeGaps.sieveModulus

/-- If `r` is squarefree and `gcd(r, W N) = 1`, then
`S.gStar(r) = mu(r)^2 / g(r)`, where `S := maynardSieveDatum N hN hD` bundles Maynard's `γ_g`
and modulus `W N` into
a `SieveDatum` under the standing hypothesis `2 ∣ W N`.

Both sides equal `1/g(r)` since `mu(r)^2 = 1` and `g(r) ≥ 1` for
squarefree `r` coprime to `W N`. -/
@[pg_tag "bg246" "slem_gg_identification"]
theorem maynardSieveDatum_gStar_squarefree_coprime (N : ℕ) (hN : 0 < N) (hD : 2 ≤ PrimeGaps.D₀ N)
    (r : ℕ) (hr : Squarefree r) (hcop : Nat.Coprime r (W N)) :
    (maynardSieveDatum N hN hD).gStar r = ((μ r : ℤ) : ℝ) ^ 2 / (g r : ℝ) := by
  have hW : 2 ∣ W N := Nat.prime_two.dvd_W_iff_le_D₀.mpr (by exact_mod_cast hD)
  set S := maynardSieveDatum N hN hD with hSdef
  rw [S.gStar_squarefree_eq_prod r hr]
  have hfac : ∀ p ∈ r.primeFactors, S.gStar p = 1 / ((p : ℝ) - 2) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpW : ¬ p ∣ W N := fun hdvd ↦ hpp.one_lt.ne'
      (Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) hdvd))
    have hγv : S.γ p = (p : ℝ) / ((p : ℝ) - 1) := by
      rw [hSdef, maynardSieveDatum_γ_prime N hN hD p hpp, if_neg hpW]
    have hp3n : (3 : ℕ) ≤ p := by
      have := hpp.two_le
      rcases hpp.eq_two_or_odd with h | h
      · exact absurd (h ▸ hW) hpW
      · omega
    have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3n
    have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have hpne : (p : ℝ) ≠ 0 := by linarith
    rw [S.gStar_prime p hpp, hγv, show (p : ℝ) - (p : ℝ) / ((p : ℝ) - 1) =
        (p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1) by field_simp; ring,
      div_div_div_cancel_right₀ h1, div_mul_eq_div_div, div_self hpne]
  have hprod : (∏ p ∈ r.primeFactors, (1 / ((p : ℝ) - 2))) = 1 / (g r : ℝ) := by
    rw [Finset.prod_div_distrib, Finset.prod_const_one,
      ArithmeticFunction.detotient_squarefree_eq_prod hr]
    push_cast
    refine congrArg (fun x : ℝ ↦ 1 / x) (Finset.prod_congr rfl fun p hp ↦ ?_)
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).two_le]
    norm_num
  rw [Finset.prod_congr rfl hfac, hprod, show ((μ r : ℤ) : ℝ) ^ 2 = 1 from
    mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hr, one_div]

/-- If `r` is squarefree and `gcd(r, W N) ≠ 1`, then `S.gStar(r) = 0`, where
`S := maynardSieveDatum N hN hD`.  A common prime `p ∣ gcd(r,
  W N)` divides `S.V = W N`,
so `S.gStar p = 0` by `SieveDatum.gStar_prime_zero`, and the squarefree product
vanishes at that factor. -/
@[pg_tag "bg246" "slem_gg_identification"]
theorem maynardSieveDatum_gStar_not_coprime (N : ℕ) (hN : 0 < N) (hD : 2 ≤ PrimeGaps.D₀ N)
    (r : ℕ) (hr : Squarefree r) (hcop : ¬ Nat.Coprime r (W N)) :
    (maynardSieveDatum N hN hD).gStar r = 0 := by
  set S := maynardSieveDatum N hN hD with hSdef
  rw [S.gStar_squarefree_eq_prod r hr]
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (hcop : Nat.gcd r (W N) ≠ 1)
  refine Finset.prod_eq_zero
    (Nat.mem_primeFactors.mpr ⟨hp, hpd.trans (Nat.gcd_dvd_left r (W N)), hr.ne_zero⟩) ?_
  exact S.gStar_prime_zero p hp (by rw [hSdef]; exact hpd.trans (Nat.gcd_dvd_right r (W N)))

end PrimeGaps

end
