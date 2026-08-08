/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Batteries.Data.Nat.Gcd
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Data.Finset.Functor
public import PrimeGapsTheory.Analysis.SingularSeries
public import PrimeGapsTheory.Arithmetic.BDefect
public import PrimeGapsTheory.Arithmetic.ConvergentSums
public import PrimeGapsTheory.Arithmetic.Mertens.CoprimeDensity

/-!
# The convolution form of `H`

`partialSumALt` and the convolution form of the `H` sum, with the `bTilde`
multiplicativity API.

## Main results

* `slem_H_convolution_form`
-/

@[expose] public section

open scoped Finset

open scoped ArithmeticFunction.Moebius

namespace PrimeGaps

/-- The partial sum `∑ hfun f` over positive `f < x` coprime to `m`.  This is the form of
`PrimeGaps.MaynardOffDiagonal.sumA` used throughout the `H`-asymptotic argument; the two agree
up to `O(1/√x)` (`PrimeGaps.boundary_sqrt`). -/
noncomputable def partialSumALt (m : ℕ) (x : ℝ) : ℝ :=
  ∑ f ∈ (Finset.range ⌈x⌉₊).filter (fun f : ℕ ↦ 0 < f ∧ (f : ℝ) < x ∧ f.Coprime m), hfun f

/-- The squarefree positive `d < z` coprime to `V` and divisible by `e`. -/
noncomputable def Dfin (S : SieveDatum) (z : ℝ) (e : ℕ) : Finset ℕ :=
  (Finset.range ⌈z⌉₊).filter
    (fun d : ℕ ↦ e ∣ d ∧ 0 < d ∧ (d : ℝ) < z ∧ Squarefree d ∧ d.Coprime S.V)

/-- The `H`-index set (matches `H_eq_sum_coprime`), further restricted to squarefree `d`.
Since `h d = 0` off squarefree, this restriction is harmless. -/
noncomputable def Rfin (S : SieveDatum) (z : ℝ) : Finset ℕ :=
  (Finset.range ⌈z⌉₊).filter (fun d : ℕ ↦ 0 < d ∧ (d : ℝ) < z ∧ d.Coprime S.V)

/-- For `x ≤ 1` no positive natural `f` satisfies `(f : ℝ) < x`, so the strict partial sum is
empty and hence `0`. -/
theorem partialSumALt_eq_zero_of_le_one (m : ℕ) (x : ℝ) (hx : x ≤ 1) : partialSumALt m x = 0 := by
  refine Finset.sum_eq_zero fun f hf ↦ ?_
  obtain ⟨-, hf0, hflt, -⟩ := Finset.mem_filter.mp hf
  exact absurd (hx.trans (by exact_mod_cast hf0 : (1 : ℝ) ≤ (f : ℝ))) (not_le.2 hflt)

/-- Past the truncation point the summand vanishes: `⌈z⌉₊ ≤ e` forces `z / e ≤ 1` (the quotient
being `0` when `e = 0`), so `partialSumALt m (z / e) = 0`. -/
theorem partialSumALt_div_eq_zero_of_ceil_le (m e : ℕ) (z : ℝ) (he : ⌈z⌉₊ ≤ e) :
    partialSumALt m (z / e) = 0 := by
  refine partialSumALt_eq_zero_of_le_one m _ ?_
  rcases Nat.eq_zero_or_pos e with rfl | hepos
  · simp
  · rw [div_le_one (by exact_mod_cast hepos : (0 : ℝ) < (e : ℝ))]
    exact (Nat.le_ceil z).trans (by exact_mod_cast he)

/-- **Dilation by `e`.**  For `e ≠ 0` squarefree and coprime to `S.V`, the map `f ↦ e * f`
carries the index set of `partialSumALt (S.V * e) (z / e)` bijectively onto `Dfin S z e`, so
`partialSumALt (S.V * e) (z / e) = ∑ d ∈ Dfin S z e, hfun (d / e)`. -/
private theorem partialSumALt_eq_sum_Dfin (S : SieveDatum) (z : ℝ) (e : ℕ) (he_ne : e ≠ 0)
    (he_sf : Squarefree e) (he_cop : e.Coprime S.V) :
    partialSumALt (S.V * e) (z / e) = ∑ d ∈ Dfin S z e, hfun (d / e) := by
  have epos : 0 < e := Nat.pos_of_ne_zero he_ne
  have eposR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast epos
  have hsupp : ∀ f ∈ (Finset.range ⌈z / e⌉₊).filter
      (fun f : ℕ ↦ 0 < f ∧ (f : ℝ) < z / e ∧ f.Coprime (S.V * e)), hfun f ≠ 0 → Squarefree f :=
    fun f _ hne ↦ by
      by_contra hsf
      exact hne (by simp [hfun, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf])
  unfold partialSumALt
  rw [← Finset.sum_filter_of_ne hsupp, Finset.filter_filter]
  refine Finset.sum_nbij' (i := fun f ↦ e * f) (j := fun d ↦ d / e) (fun f hf ↦ ?_)
    (fun d hd ↦ ?_) (fun f _ ↦ Nat.mul_div_cancel_left f epos) (fun d hd ↦ ?_)
    (fun f _ ↦ by rw [Nat.mul_div_cancel_left f epos])
  · rw [Finset.mem_filter] at hf
    obtain ⟨-, ⟨hf0, hflt, hfcop⟩, hfsf⟩ := hf
    have hzlt : ((e * f : ℕ) : ℝ) < z := by
      rw [lt_div_iff₀ eposR] at hflt
      push_cast
      linarith
    unfold Dfin
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_ceil.mpr hzlt, dvd_mul_right e f, Nat.mul_pos epos hf0, hzlt,
      Nat.squarefree_mul_iff.mpr ⟨(hfcop.coprime_dvd_right (dvd_mul_left e S.V)).symm, he_sf, hfsf⟩,
      Nat.Coprime.mul_left he_cop (hfcop.coprime_dvd_right (dvd_mul_right S.V e))⟩
  · unfold Dfin at hd
    rw [Finset.mem_filter] at hd
    obtain ⟨-, ⟨q, rfl⟩, hd0, hdz, hdsf, hdcop⟩ := hd
    obtain ⟨hqe, -, hqsf⟩ := Nat.squarefree_mul_iff.mp hdsf
    have hqlt : (q : ℝ) < z / e := by
      rw [lt_div_iff₀ eposR]
      push_cast at hdz
      linarith
    rw [Nat.mul_div_cancel_left q epos, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_ceil.mpr hqlt, ⟨Nat.pos_of_ne_zero (by rintro rfl; simp at hd0), hqlt,
      Nat.Coprime.mul_right (hdcop.coprime_dvd_left (dvd_mul_left q e)) hqe.symm⟩, hqsf⟩
  · unfold Dfin at hd
    exact Nat.mul_div_cancel' (Finset.mem_filter.mp hd).2.1

/-- (a1+a2) Per-`e` identity: the term equals a sum over divisor-multiples of `e`.
Handles `bDefect e = 0` (both sides 0) and the bijection `f ↦ e·f` for `e` squarefree cop V. -/
theorem convForm_term (S : SieveDatum) (z : ℝ) (e : ℕ) :
    S.bDefect e * partialSumALt (S.V * e) (z / e) =
      ∑ d ∈ Dfin S z e, S.bDefect e * hfun (d / e) := by
  by_cases hb : S.bDefect e = 0
  · simp [hb]
  · rw [← Finset.mul_sum, partialSumALt_eq_sum_Dfin S z e
      (fun h ↦ hb (by rw [h]; exact S.bDefect_eq_zero_of_not_squarefree 0 (by simp)))
      (not_not.1 fun h ↦ hb (S.bDefect_eq_zero_of_not_squarefree e h))
      (not_not.1 fun h ↦ hb (S.bDefect_eq_zero_of_not_coprime e h))]

/-- (a3) Support finiteness: the term vanishes for `e ≥ ⌈z⌉₊` (and `e = 0`), so the
`tsum` reduces to a finite sum over `range ⌈z⌉₊`. -/
theorem convForm_tsum_eq_sum (S : SieveDatum) (z : ℝ) :
    (∑' e : ℕ, S.bDefect e * partialSumALt (S.V * e) (z / e)) =
      ∑ e ∈ Finset.range ⌈z⌉₊, S.bDefect e * partialSumALt (S.V * e) (z / e) := by
  refine tsum_eq_sum fun e he ↦ ?_
  rw [partialSumALt_div_eq_zero_of_ceil_le _ e z (by simpa using he), mul_zero]

/-- **Divisor-sum collapse.**  Summing the indicator kernel over `e ∣ d` collapses the inner
divisor sum through `S.h_eq_sum_bDefect_mul_a`, leaving `∑ d, S.h d` over the squarefree
`d < z` coprime to `S.V`. -/
private theorem sum_sum_ite_bDefect_eq_sum_h (S : SieveDatum) (z : ℝ) :
    (∑ d ∈ Finset.range ⌈z⌉₊, ∑ e ∈ Finset.range ⌈z⌉₊,
      (if (e ∣ d ∧ 0 < d ∧ (d : ℝ) < z ∧ Squarefree d ∧ d.Coprime S.V)
        then S.bDefect e * hfun (d / e) else 0)) =
      ∑ d ∈ (Finset.range ⌈z⌉₊).filter
        (fun d : ℕ ↦ 0 < d ∧ (d : ℝ) < z ∧ d.Coprime S.V ∧ Squarefree d), S.h d := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [Finset.mem_range] at hd
  by_cases hR : 0 < d ∧ (d : ℝ) < z ∧ d.Coprime S.V ∧ Squarefree d
  · obtain ⟨hd0, hdz, hdcop, hdsf⟩ := hR
    rw [if_pos ⟨hd0, hdz, hdcop, hdsf⟩, ← Finset.sum_filter,
      S.h_eq_sum_bDefect_mul_a d hd0 hdsf hdcop]
    refine Finset.sum_congr (Finset.ext fun e ↦ ?_) fun _ _ ↦ rfl
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors]
    exact ⟨fun h ↦ ⟨h.2.1, hd0.ne'⟩, fun h ↦
      ⟨lt_of_le_of_lt (Nat.le_of_dvd hd0 h.1) hd, h.1, hd0, hdz, hdsf, hdcop⟩⟩
  · rw [if_neg hR]
    exact Finset.sum_eq_zero fun e _ ↦ if_neg fun h ↦ hR ⟨h.2.1, h.2.2.1, h.2.2.2.2, h.2.2.2.1⟩

/-- (a4) Fubini / hyperbola double-count: swap the `(e,d)` order and collapse the inner
divisor sum to `h d` via `h_eq_sum_bDefect_mul_a`, then drop the squarefree restriction. -/
theorem convForm_fubini (S : SieveDatum) (z : ℝ) :
    (∑ e ∈ Finset.range ⌈z⌉₊, ∑ d ∈ Dfin S z e, S.bDefect e * hfun (d / e)) =
      ∑ d ∈ Rfin S z, S.h d := by
  simp only [Dfin, Finset.sum_filter]
  rw [Finset.sum_comm, sum_sum_ite_bDefect_eq_sum_h S z]
  refine Finset.sum_subset (fun d hd ↦ ?_) fun d hd hdnot ↦ ?_
  · obtain ⟨hr, hd0, hdz, hdcop, -⟩ := Finset.mem_filter.mp hd
    unfold Rfin
    exact Finset.mem_filter.mpr ⟨hr, hd0, hdz, hdcop⟩
  · unfold Rfin at hd
    obtain ⟨hdrange, hd0, hdz, hdcop⟩ := Finset.mem_filter.mp hd
    change (μ d : ℝ) ^ 2 * S.gStar d = 0
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree fun hsf ↦
      hdnot (Finset.mem_filter.mpr ⟨hdrange, hd0, hdz, hdcop, hsf⟩)]
    simp

/-- `H z` equals the sum over `Rfin` (i.e. `H_eq_sum_coprime` in our `Rfin` notation). -/
theorem H_eq_sum_Rfin (S : SieveDatum) (z : ℝ) : S.H z = ∑ d ∈ Rfin S z, S.h d := by
  rw [S.H_eq_sum_coprime z]; rfl

/-- Convolution formula: `S.H z = ∑' e, S.bDefect e * partialSumALt (S.V * e) (z / e)`. -/
theorem slem_H_convolution_form (S : SieveDatum) (z : ℝ) :
    S.H z = ∑' e : ℕ, S.bDefect e * partialSumALt (S.V * e) (z / e) := by
  rw [convForm_tsum_eq_sum S z, H_eq_sum_Rfin S z, ← convForm_fubini S z]
  exact (Finset.sum_congr rfl (fun e _ ↦ convForm_term S z e)).symm

/-- `bTilde 0 = 0`. -/
theorem bTilde_zero (S : SieveDatum) : S.bTilde 0 = 0 := by
  simp [SieveDatum.bTilde, SieveDatum.bDefect]

/-- `bTilde 1 = 1`. -/
theorem bTilde_one (S : SieveDatum) : S.bTilde 1 = 1 := by
  simp [SieveDatum.bTilde, SieveDatum.bDefect]

/-- `bTilde` vanishes off the squarefree numbers coprime to `V`. -/
theorem bTilde_eq_zero_of_not_squarefree (S : SieveDatum) (n : ℕ)
    (h : ¬ Squarefree n) : S.bTilde n = 0 := by
  simp [SieveDatum.bTilde, S.bDefect_eq_zero_of_not_squarefree n h]

/-- `bTilde` vanishes at `p ^ k` for a prime `p` and `2 ≤ k`, such a power not being squarefree. -/
theorem bTilde_prime_pow_eq_zero (S : SieveDatum) {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) :
    S.bTilde (p ^ k) = 0 := by
  refine bTilde_eq_zero_of_not_squarefree S _ ?_
  rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]
  rintro ⟨-, hk1⟩
  omega

/-- `bTilde` is multiplicative on coprime arguments. -/
theorem bTilde_mul (S : SieveDatum) {m n : ℕ} (hmn : m.Coprime n) :
    S.bTilde (m * n) = S.bTilde m * S.bTilde n := by
  simp only [SieveDatum.bTilde, S.bDefect_mul m n hmn, Nat.totient_mul hmn]
  push_cast; ring

/-- Per-prime Euler factor of `bTilde`: for a prime `p ∤ V`,
`1 + b̃(p) = (1-1/p)/(1-γp/p)`, the singular-series local factor. -/
theorem bTilde_prime_add_one (S : SieveDatum) {p : ℕ} (hp : p.Prime) (hpV : ¬ p ∣ S.V) :
    1 + S.bTilde p = (1 - 1 / (p : ℝ)) / (1 - S.γ p / p) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hpγ : (0 : ℝ) < (p : ℝ) - S.γ p := by linarith [S.γ_lt p hp]
  have hne1 : (1 : ℝ) - S.γ p / p ≠ 0 := (sub_pos.mpr ((div_lt_one hp0).mpr (S.γ_lt p hp))).ne'
  rw [show S.bTilde p = S.bDefect p * (p.totient : ℝ) / p from rfl,
    S.bDefect_prime p hp hpV, Nat.totient_prime hp, Nat.cast_pred hp.pos]
  field_simp
  ring

/-- At a prime `p | V`, `b̃(p) = 0` (since `p` is not coprime to `V`). -/
theorem bTilde_prime_dvd_V (S : SieveDatum) {p : ℕ} (hp : p.Prime) (hpV : p ∣ S.V) :
    S.bTilde p = 0 := by
  simp [SieveDatum.bTilde,
    S.bDefect_eq_zero_of_not_coprime p fun hc ↦ hp.coprime_iff_not_dvd.mp hc hpV]

/-- Every Euler factor of the singular series is positive.  At `p ∣ S.V` the factor is `1`;
otherwise it is `(1 - 1/p) / (1 - γ p / p)`, positive since `0 ≤ γ p < p ≤ p`. -/
theorem one_add_bTilde_prime_pos (S : SieveDatum) (p : Nat.Primes) : 0 < 1 + S.bTilde (p : ℕ) := by
  have hp : (p : ℕ).Prime := p.2
  by_cases hpV : (p : ℕ) ∣ S.V
  · rw [bTilde_prime_dvd_V S hp hpV]; norm_num
  · rw [bTilde_prime_add_one S hp hpV]
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    exact div_pos (by rw [sub_pos, div_lt_one hp0]; linarith)
      (by rw [sub_pos, div_lt_one hp0]; exact S.γ_lt (p : ℕ) hp)

/-- The local Euler factor `∑'_k b̃(p^k) = 1 + b̃(p)` (higher prime powers are not
squarefree, so `bTilde` vanishes there). -/
theorem bTilde_localFactor (S : SieveDatum) {p : ℕ} (hp : p.Prime) :
    ∑' k : ℕ, S.bTilde (p ^ k) = 1 + S.bTilde p := by
  rw [tsum_eq_sum (s := {0, 1})]
  · rw [Finset.sum_insert (by simp), Finset.sum_singleton]
    simp only [pow_zero, pow_one, bTilde_one]
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    exact bTilde_prime_pow_eq_zero S hp (by omega)

/-- The logarithmically weighted `bTilde` term is dominated by the `bDefect`-weighted `τ·√`
term: `|S.bTilde e| * (1 + log e) ≤ 3 * (|S.bDefect e| * (e.divisors.card) * √e)`. -/
theorem abs_bTilde_mul_log_le (S : SieveDatum) (e : ℕ) :
    |S.bTilde e| * (1 + Real.log e) ≤
      3 * (|S.bDefect e| * (#e.divisors : ℝ) * √e) := by
  rcases Nat.eq_zero_or_pos e with rfl | hepos
  · simp [bTilde_zero S]
  · have heR : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast hepos
    have heRpos : (0 : ℝ) < (e : ℝ) := by linarith
    have h1 : |S.bTilde e| ≤ |S.bDefect e| := by
      rw [show S.bTilde e = S.bDefect e * (e.totient : ℝ) / (e : ℝ) from rfl, mul_div_assoc,
        abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (e.totient : ℝ) / (e : ℝ))]
      refine (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)).trans_eq (mul_one _)
      rw [div_le_one heRpos]
      exact_mod_cast Nat.totient_le e
    have h2 : (1 : ℝ) + Real.log e ≤ 3 * √e := by
      have hge1 : (1 : ℝ) ≤ √e := by simpa using Real.sqrt_le_sqrt heR
      have hlog := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr heRpos)
      rw [Real.log_sqrt heRpos.le] at hlog
      linarith
    have h3 : (1 : ℝ) ≤ (#e.divisors : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hepos.ne'⟩
    calc |S.bTilde e| * (1 + Real.log e) ≤ |S.bDefect e| * (3 * √e) :=
          mul_le_mul h1 h2 (by linarith [Real.log_nonneg heR]) (abs_nonneg _)
      _ = 3 * (|S.bDefect e| * √e) := by ring
      _ ≤ 3 * (|S.bDefect e| * (#e.divisors : ℝ) * √e) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (le_mul_of_one_le_right (abs_nonneg _) h3) (Real.sqrt_nonneg _)) (by norm_num)

end PrimeGaps
