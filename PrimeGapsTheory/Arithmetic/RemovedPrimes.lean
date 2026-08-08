/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.NNRat.Floor
public import PrimeGapsTheory.Arithmetic.LogDivSq
public import PrimeGapsTheory.Arithmetic.Mertens.TauK
public import PrimeGapsTheory.Foundations.SieveDatum

import PrimeGapsTheory.Tactic.PaperTag

/-!
# The removed-primes bound

Bounds for logarithmic sums over prime divisors removed by a squarefree modulus.

## Main definitions

* `ellV`: The logarithmic prime-divisor sum of a modulus.
* `intervalPrimeSum`: The weighted prime sum associated with a density function.

## Main results

* `ellV_le_two_L_add_const`: A uniform upper bound for `ellV`.
-/

@[expose] public section

open scoped BigOperators

namespace PrimeGaps

/-- The quantity $\ell_m = \sum_{p \mid m} \frac{\log p}{p-1}$, where the sum ranges over the
(distinct) prime divisors of `m`. For squarefree `m` these are exactly the primes appearing in its
factorization. -/
@[pg_tag "bg246" "def_ell_m"]
noncomputable def ellV (m : ℕ) : ℝ := ∑ p ∈ m.primeFactors, Real.log p / (p - 1)

/-- `ellV m` is nonnegative: every prime divisor `p` of `m` satisfies `p ≥ 2`, so both
`log p` and `p - 1` are nonnegative. -/
lemma ellV_nonneg (m : ℕ) : 0 ≤ ellV m :=
  Finset.sum_nonneg fun p hp ↦ div_nonneg (Real.log_natCast_nonneg p) <| by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    linarith

/-- The absolute error constant `S = ∑ log n / n²`. -/
noncomputable def Serr : ℝ := ∑' n : ℕ, Real.log n / (n : ℝ) ^ 2

/-- `Serr` is nonnegative, being a sum of nonnegative terms. -/
lemma Serr_nonneg : 0 ≤ Serr :=
  tsum_nonneg fun n ↦ div_nonneg (Real.log_natCast_nonneg n) (by positivity)

/-- A finite partial sum of `log n / n²` over any finset of naturals is `≤ Serr`. -/
lemma sum_log_div_sq_le (s : Finset ℕ) : ∑ n ∈ s, Real.log n / (n : ℝ) ^ 2 ≤ Serr :=
  Summable.sum_le_tsum s
    (fun n _ ↦ div_nonneg (Real.log_natCast_nonneg n) (by positivity)) Real.summable_log_div_sq

/-- A constant in the upper bound for `∑_{p ≤ N} log p / p`. -/
noncomputable def Cmert : ℝ := Classical.choose WeightedDivisorSum.sum_log_div_prime_le

/-- For `N ≥ 2`, `∑_{p ≤ N} log p / p ≤ log N + Cmert`. -/
lemma mertens_upper (N : ℕ) (hN : 2 ≤ N) :
    ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, Real.log p / (p : ℝ) ≤ Real.log N + Cmert := by
  have hthis := Classical.choose_spec WeightedDivisorSum.sum_log_div_prime_le (N : ℝ)
    (by exact_mod_cast hN)
  rw [Nat.floor_natCast] at hthis
  have heq : (N + 1).primesBelow = (Finset.Icc 2 N).filter Nat.Prime := by
    rw [Nat.primesBelow_eq_filter_Ico_zero]
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc, Nat.lt_succ_iff]
    exact ⟨fun ⟨⟨_, hlt⟩, hp⟩ ↦ ⟨⟨hp.two_le, hlt⟩, hp⟩,
      fun ⟨⟨_, hle⟩, hp⟩ ↦ ⟨⟨Nat.zero_le _, hle⟩, hp⟩⟩
  rwa [heq] at hthis

/-- The sum `∑_{p ∣ V} log p / (p(p - 1))` is at most `2 · Serr`. -/
lemma tail_bound (V : ℕ) :
    ∑ p ∈ V.primeFactors, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 2 * Serr :=
  calc ∑ p ∈ V.primeFactors, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ ∑ p ∈ V.primeFactors, 2 * (Real.log p / (p : ℝ) ^ 2) := by
        refine Finset.sum_le_sum fun p hp ↦ ?_
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        rw [show (2 : ℝ) * (Real.log p / (p : ℝ) ^ 2) = Real.log p / ((p : ℝ) ^ 2 / 2) by ring]
        exact div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) (by nlinarith) (by nlinarith)
    _ = 2 * ∑ p ∈ V.primeFactors, Real.log p / (p : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 2 * Serr := by linarith [sum_log_div_sq_le V.primeFactors]

/-- With `V ≥ 2` squarefree, `γ(p)=0` for `p|V`, `|γ(p)-1| ≤ A₃/p` for `p∤V`, and the two-sided
Mertens hypothesis (lower bound `-L`), the main term satisfies `M = ∑_{p|V} log p/p ≤ log 2 + Cmert
+ L + A₃·Serr`. -/
lemma main_term_bound (A₂ A₃ L : ℝ) (γ : ℕ → ℝ) (V : ℕ) (hA₃ : 0 < A₃) (hV2 : 2 ≤ V)
    (hmertens : ∀ w z : ℝ, 2 ≤ w → w ≤ z → -L ≤ intervalPrimeSum γ w z - Real.log (z / w) ∧
      intervalPrimeSum γ w z - Real.log (z / w) ≤ A₂)
    (hγV : ∀ p, Nat.Prime p → p ∣ V → γ p = 0)
    (hγcoprime : ∀ p, Nat.Prime p → ¬ p ∣ V → |γ p - 1| ≤ A₃ / p) :
    ∑ p ∈ V.primeFactors, Real.log p / (p : ℝ) ≤ Real.log 2 + Cmert + L + A₃ * Serr := by
  have hV0 : V ≠ 0 := by omega
  set P : Finset ℕ := (Finset.Icc 2 V).filter Nat.Prime with hP
  set PnotV : Finset ℕ := {p ∈ P | ¬ p ∣ V} with hPnotV
  have hpf_eq : V.primeFactors = {p ∈ P | p ∣ V} := by
    ext p
    simp only [Nat.mem_primeFactors, hP, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨fun ⟨hp, hdvd, _⟩ ↦ ⟨⟨⟨hp.two_le, Nat.le_of_dvd (by omega) hdvd⟩, hp⟩, hdvd⟩,
      fun ⟨⟨_, hp⟩, hdvd⟩ ↦ ⟨hp, hdvd, hV0⟩⟩
  have hsplit_P : ∑ p ∈ P, Real.log p / (p : ℝ) = (∑ p ∈ V.primeFactors, Real.log p / (p : ℝ)) +
        ∑ p ∈ PnotV, Real.log p / (p : ℝ) := by
    rw [hpf_eq, hPnotV]
    exact (Finset.sum_filter_add_sum_filter_not P (fun p ↦ p ∣ V) _).symm
  have hupper : ∑ p ∈ P, Real.log p / (p : ℝ) ≤ Real.log V + Cmert := mertens_upper V hV2
  have hmS_eq : intervalPrimeSum γ 2 V = ∑ p ∈ PnotV, γ p * Real.log p / (p : ℝ) := by
    unfold intervalPrimeSum
    rw [Nat.floor_natCast]
    have hidx : {p ∈ (Finset.range (V + 1)) | Nat.Prime p ∧ (2 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) ≤ (V : ℝ)} =
      P := by
      rw [hP]
      ext p
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, Nat.lt_succ_iff]
      exact ⟨fun ⟨hpV, hprime, hp2, _⟩ ↦ ⟨⟨by exact_mod_cast hp2, hpV⟩, hprime⟩,
        fun ⟨⟨hp2, hpV⟩, hprime⟩ ↦ ⟨hpV, hprime, by exact_mod_cast hp2, by exact_mod_cast hpV⟩⟩
    have hzero : ∑ p ∈ {p ∈ P | ¬(¬ p ∣ V)}, γ p * Real.log p / (p : ℝ) = 0 := by
      refine Finset.sum_eq_zero fun p hp ↦ ?_
      simp only [Finset.mem_filter, not_not, hP, Finset.mem_Icc] at hp
      simp [hγV p hp.1.2 hp.2]
    rw [hidx, hPnotV, ← Finset.sum_filter_add_sum_filter_not P (fun p ↦ ¬ p ∣ V), hzero, add_zero]
  have hmlow : Real.log V - Real.log 2 - L ≤ intervalPrimeSum γ 2 V := by
    have hVr : (2 : ℝ) ≤ (V : ℝ) := by exact_mod_cast hV2
    have hh := (hmertens 2 (V : ℝ) (le_refl 2) hVr).1
    rw [Real.log_div (by positivity) (by norm_num)] at hh
    linarith
  have herr : ∑ p ∈ PnotV, γ p * Real.log p / (p : ℝ) ≤
      (∑ p ∈ PnotV, Real.log p / (p : ℝ)) + A₃ * ∑ p ∈ PnotV, Real.log p / (p : ℝ) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun p hp ↦ ?_
    simp only [hPnotV, hP, Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨_, hpp⟩, hndvd⟩ := hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hγub : γ p ≤ 1 + A₃ / p := by linarith [(abs_le.mp (hγcoprime p hpp hndvd)).2]
    refine (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hγub
      (Real.log_natCast_nonneg p)) (by linarith)).trans_eq ?_
    field_simp
  rw [hmS_eq] at hmlow
  linarith [hsplit_P, hupper, herr, hmlow,
    mul_le_mul_of_nonneg_left (sum_log_div_sq_le PnotV) hA₃.le]

/-- `ellV V = M + T`: for each prime `p ≥ 2`, `log p/(p-1) = log p/p + log p/(p(p-1))`. -/
lemma ellV_split (V : ℕ) : ellV V = (∑ p ∈ V.primeFactors, Real.log p / (p : ℝ)) +
      (∑ p ∈ V.primeFactors, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
  unfold ellV
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- There is a constant depending only on `A₃` such that, for every density function `γ` and
squarefree modulus `V` satisfying the sifting-dimension bound (1), the Mertens-type two-sided bound
(2), and the squarefree-modulus conditions (3), the quantity `ℓ_V` is bounded above by
`2L + C(A₃)`.

The hypothesis `∀ p prime, 0 ≤ γ p` records that `γ` takes values in `ℝ_{≥0}` on primes. -/
@[pg_tag "bg246" "slem_removed_primes"]
theorem ellV_le_two_L_add_const : ∃ C : ℝ → ℝ,
      ∀ (A₁ A₂ A₃ L : ℝ) (γ : ℕ → ℝ) (V : ℕ), 0 < A₁ → 0 < A₂ → 0 < A₃ → 0 < L →
        (∀ p, Nat.Prime p → 0 ≤ γ p) →
        (∀ p, Nat.Prime p → 0 ≤ γ p / p ∧ γ p / p ≤ 1 - A₁) →
        (∀ w z : ℝ, 2 ≤ w → w ≤ z → -L ≤ intervalPrimeSum γ w z - Real.log (z / w) ∧
          intervalPrimeSum γ w z - Real.log (z / w) ≤ A₂) →
        Squarefree V →
        (∀ p, Nat.Prime p → p ∣ V → γ p = 0) →
        (∀ p, Nat.Prime p → ¬ p ∣ V → |γ p - 1| ≤ A₃ / p) →
        ellV V ≤ 2 * L + C A₃ := by
  refine ⟨fun a ↦ Real.log 2 + |Cmert| + a * Serr + 2 * Serr, ?_⟩
  intro A₁ A₂ A₃ L γ V hA₁ hA₂ hA₃ hL hγnn hsift hmertens hVsf hγV hγcoprime
  have hV1 : 1 ≤ V := Nat.one_le_iff_ne_zero.mpr hVsf.ne_zero
  rcases eq_or_lt_of_le hV1 with hVeq | hVgt
  · subst hVeq
    rw [show ellV 1 = 0 by simp [ellV]]
    nlinarith [hL, mul_nonneg hA₃.le Serr_nonneg, abs_nonneg Cmert,
      Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  · rw [ellV_split V]
    nlinarith [main_term_bound A₂ A₃ L γ V hA₃ hVgt hmertens hγV hγcoprime, tail_bound V, hL,
      le_abs_self Cmert]

end PrimeGaps
