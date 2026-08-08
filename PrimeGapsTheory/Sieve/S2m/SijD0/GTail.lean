/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Arithmetic.DivisorTails
public import PrimeGapsTheory.Sieve.Common.SijD0.FirstMoment
public import PrimeGapsTheory.Sieve.S2m.Substitution

/-!
# The guarded g-tail

Summability and the master bound for the tail of the g-weighted prime sum.

## Main results

* `PrimeGaps.guarded_g_tail_le_div`: the guarded tail `∑ |μ(s)|/g(s)²` is `O(1/D)`.
* `chebyshev_pi_diff_mul_log_le`: `(π(2N) - π(N)) * log N ≤ θ(2N)`.
-/

@[expose] public section

open scoped Finset
open scoped ArithmeticFunction.Moebius

open scoped ArithmeticFunction.detotient

namespace PrimeGaps

open Classical in
/-- Summability of `∑_{q prime, q > D} 1/(q-2)²`, by comparison with `4/q²`. -/
theorem gtail_prime_summand_summable (D : ℕ) : Summable (fun q : ℕ ↦
      if Nat.Prime q ∧ D < q then (1 : ℝ) / ((q : ℝ) - 2) ^ 2 else 0) := by
  have hmaj : Summable (fun q : ℕ ↦ 4 / (q : ℝ) ^ 2 + if q = 3 then (1 : ℝ) else 0) := by
    refine Summable.add ?_ (hasSum_ite_eq 3 (1 : ℝ)).summable
    simpa only [mul_one_div] using (Real.summable_one_div_nat_pow.mpr (by norm_num)).mul_left 4
  refine Summable.of_nonneg_of_le (fun q ↦ by split <;> positivity) (fun q ↦ ?_) hmaj
  by_cases hcond : Nat.Prime q ∧ D < q
  · rw [if_pos hcond]
    have hq2 : 2 ≤ q := hcond.1.two_le
    rcases Nat.lt_or_ge q 4 with hlt | hge
    · interval_cases q <;> norm_num
    · have hqR : (4 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hge
      have hqm2 : (0 : ℝ) < (q : ℝ) - 2 := by linarith
      rw [if_neg (by omega : q ≠ 3), add_zero, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
  · rw [if_neg hcond]
    split <;> positivity

open Classical in
/-- `∑_{q prime, q > D} 1/(q-2)² ≤ 2A/D` for `D ≥ 100`, with `A > 0` absolute. -/
theorem gtail_prime_tail_le : ∃ A : ℝ, 0 < A ∧ ∀ D : ℕ, 100 ≤ D →
      (∑' q : ℕ, if Nat.Prime q ∧ D < q then (1 : ℝ) / ((q : ℝ) - 2) ^ 2 else 0) ≤
        2 * A / (D : ℝ) := by
  obtain ⟨A, hA, hAtail⟩ := tail_sum_one_over_sq
  refine ⟨A, hA, fun D hD ↦ Real.tsum_le_of_sum_le (fun q ↦ by split <;> positivity) (fun u ↦ ?_)⟩
  rw [← Finset.sum_filter]
  have hmemS : ∀ q ∈ u.filter (fun q ↦ Nat.Prime q ∧ D < q), Nat.Prime q ∧ D < q :=
    fun q hq ↦ (Finset.mem_filter.mp hq).2
  have hpt : ∀ q ∈ u.filter (fun q ↦ Nat.Prime q ∧ D < q),
      (1 : ℝ) / ((q : ℝ) - 2) ^ 2 ≤ 2 * ((1 : ℝ) / (q : ℝ) ^ 2) := by
    intro q hq
    have hqR : (101 : ℝ) ≤ (q : ℝ) := by
      have := (hmemS q hq).2; exact_mod_cast (by omega : 101 ≤ q)
    have hqm2 : (0 : ℝ) < (q : ℝ) - 2 := by linarith
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc ∑ q ∈ u.filter (fun q ↦ Nat.Prime q ∧ D < q), (1 : ℝ) / ((q : ℝ) - 2) ^ 2
      ≤ ∑ q ∈ u.filter (fun q ↦ Nat.Prime q ∧ D < q), 2 * ((1 : ℝ) / (q : ℝ) ^ 2) :=
        Finset.sum_le_sum hpt
    _ = 2 * ∑ q ∈ u.filter (fun q ↦ Nat.Prime q ∧ D < q), (1 : ℝ) / (q : ℝ) ^ 2 :=
        (Finset.mul_sum ..).symm
    _ ≤ 2 * (A / (D : ℝ)) :=
        mul_le_mul_of_nonneg_left (hAtail D (by omega) _ fun p hp ↦ (hmemS p hp).2) (by norm_num)
    _ = 2 * A / (D : ℝ) := by ring

open Classical in
/-- The splitting map `s ↦ (s.minFac, s / s.minFac)` is injective on the guarded tail set. -/
theorem gtail_e_inj (D : ℕ) :
    ∀ s₁ : ℕ, (D < s₁ ∧ Squarefree s₁ ∧ (∀ q, Nat.Prime q → q ∣ s₁ → D < q)) →
    ∀ s₂ : ℕ, (D < s₂ ∧ Squarefree s₂ ∧ (∀ q, Nat.Prime q → q ∣ s₂ → D < q)) →
    (s₁.minFac, s₁ / s₁.minFac) = (s₂.minFac, s₂ / s₂.minFac) → s₁ = s₂ := by
  rintro s₁ - s₂ - heq
  obtain ⟨hq, hm⟩ := (Prod.mk.injEq ..).mp heq
  rw [← Nat.mul_div_cancel' (Nat.minFac_dvd s₁), ← Nat.mul_div_cancel' (Nat.minFac_dvd s₂), hm, hq]

open Classical in
/-- Summability of the guarded tail summand `|μ(s)|/g(s)²`, dominated pointwise by `term`. -/
theorem gtail_Fsum_summable (D : ℕ) : Summable (fun s : ℕ ↦
      if D < s ∧ Squarefree s ∧ (∀ q, Nat.Prime q → q ∣ s → D < q) then
        |(μ s : ℝ)| / (g s : ℝ) ^ 2
      else 0) := by
  refine convergent_sum_g.of_nonneg_of_le (fun s ↦ by split <;> positivity) fun s ↦ ?_
  by_cases hcond : D < s ∧ Squarefree s ∧ (∀ q, Nat.Prime q → q ∣ s → D < q)
  · rw [if_pos hcond, term_eq_squarefree, if_pos ⟨by omega, hcond.2.1⟩]
  · simpa only [if_neg hcond] using term_nonneg s

open Classical in
/-- Peeling the least prime factor `q = s.minFac` off a guarded `s`:
`|μ(s)|/g(s)² = 1/(q-2)² · term (s/q)`. -/
theorem gtail_claimA (D : ℕ) (hD : 100 ≤ D) :
    ∀ s : ℕ, (D < s ∧ Squarefree s ∧ (∀ q, Nat.Prime q → q ∣ s → D < q)) →
      |(μ s : ℝ)| / (g s : ℝ) ^ 2 =
      (if Nat.Prime s.minFac ∧ D < s.minFac then (1 : ℝ) / ((s.minFac : ℝ) - 2) ^ 2 else 0) *
          term (s / s.minFac) := by
  intro s ⟨hDs, hsf, hguard⟩
  have hsne : s ≠ 1 := by omega
  set q := s.minFac
  have hqp : Nat.Prime q := Nat.minFac_prime hsne
  have hqdvd : q ∣ s := Nat.minFac_dvd s
  set mm := s / q
  have hqm : q * mm = s := Nat.mul_div_cancel' hqdvd
  have hcop : q.Coprime mm := hqp.coprime_iff_not_dvd.mpr fun ⟨c, hc⟩ ↦
    hqp.one_lt.ne' (Nat.isUnit_iff.mp (hsf q ⟨c, by rw [← hqm, hc]; ring⟩))
  have hmsf : Squarefree mm := hsf.squarefree_of_dvd ⟨q, by rw [← hqm]; ring⟩
  have hmumul : (μ s : ℝ) =
      (μ q : ℝ) * (μ mm : ℝ) := by
    rw [← hqm, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop]
    push_cast; ring
  have hgmul : (g s : ℝ) = (g q : ℝ) * (g mm : ℝ) := by
    rw [← hqm, ArithmeticFunction.isMultiplicative_detotient.map_mul_of_coprime hcop]
    push_cast; ring
  have hgq : (g q : ℝ) = (q : ℝ) - 2 := by
    rw [ArithmeticFunction.detotient_prime hqp, Nat.cast_sub hqp.two_le]
    norm_num
  have hmuq : |(μ q : ℝ)| = 1 := by
    rw [← Real.sqrt_sq_eq_abs, show ((μ q : ℝ)) ^ 2 = 1 from
      mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hqp.squarefree, Real.sqrt_one]
  rw [if_pos ⟨hqp, hguard q hqp hqdvd⟩, term_eq_squarefree,
    if_pos ⟨Nat.one_le_iff_ne_zero.mpr hmsf.ne_zero, hmsf⟩, hmumul, hgmul, hgq, abs_mul, hmuq,
    one_mul, mul_pow]
  simp only [div_eq_mul_inv, mul_inv]
  ring

open Classical in
/-- The guarded tail sum is at most `(∑_{q prime, q > D} 1/(q-2)²) * (∑' m, term m)`. -/
theorem gtail_master (D : ℕ) (hD : 100 ≤ D) : (∑' s : ℕ,
        if D < s ∧ Squarefree s ∧ (∀ q, Nat.Prime q → q ∣ s → D < q) then
          |(μ s : ℝ)| / (g s : ℝ) ^ 2
        else 0) ≤ (∑' q : ℕ, if Nat.Prime q ∧ D < q then (1 : ℝ) / ((q : ℝ) - 2) ^ 2 else 0) *
          (∑' m : ℕ, term m) := by
  set P : ℕ → Prop := fun s ↦ D < s ∧ Squarefree s ∧ (∀ q, Nat.Prime q → q ∣ s → D < q)
  set Fsum : ℕ → ℝ := fun s ↦ if P s then |(μ s : ℝ)| / (g s : ℝ) ^ 2
    else 0
  set Pq : ℕ → ℝ := fun q ↦ if Nat.Prime q ∧ D < q then (1 : ℝ) / ((q : ℝ) - 2) ^ 2 else 0 with hPq
  set Gpair : ℕ × ℕ → ℝ := fun p ↦ Pq p.1 * term p.2 with hGpair
  have hPq_nonneg : ∀ q, 0 ≤ Pq q := fun q ↦ by simp only [hPq]; split <;> positivity
  have hGpair_summable : Summable Gpair :=
    (gtail_prime_summand_summable D).mul_of_nonneg convergent_sum_g hPq_nonneg term_nonneg
  have hRHS : (∑' q : ℕ, Pq q) * (∑' m : ℕ, term m) = ∑' p : ℕ × ℕ, Gpair p := by
    rw [hGpair_summable.tsum_prod' fun q ↦ convergent_sum_g.mul_left (Pq q)]
    simp_rw [hGpair, tsum_mul_left, tsum_mul_right]
  change (∑' s : ℕ, Fsum s) ≤ (∑' q : ℕ, Pq q) * (∑' m : ℕ, term m)
  have hsub_eq : (∑' s : ℕ, Fsum s) = ∑' t : {s // P s}, Fsum (t : ℕ) :=
    (tsum_subtype_eq_of_support_subset fun s hs ↦ by by_contra hnp; exact hs (if_neg hnp)).symm
  rw [hRHS, hsub_eq]
  refine Summable.tsum_le_tsum_of_inj (fun t ↦ ((t : ℕ).minFac, (t : ℕ) / (t : ℕ).minFac))
    (fun t₁ t₂ heq ↦ Subtype.ext (gtail_e_inj D t₁ t₁.2 t₂ t₂.2 heq))
    (fun c _ ↦ mul_nonneg (hPq_nonneg _) (term_nonneg _))
    (fun t ↦ le_of_eq ((if_pos t.2).trans (gtail_claimA D hD t t.2)))
    ((gtail_Fsum_summable D).subtype _) hGpair_summable

open Classical in
/-- `∑_{s > D squarefree, all prime factors > D} |μ(s)|/g(s)² ≤ K/D` for `D ≥ 100`, with `K > 0`
absolute. -/
theorem guarded_g_tail_le_div : ∃ K : ℝ, 0 < K ∧ ∀ D : ℕ, 100 ≤ D →
      (∑' s : ℕ, if D < s ∧ Squarefree s ∧ (∀ q, Nat.Prime q → q ∣ s → D < q) then
          |(μ s : ℝ)| / (g s : ℝ) ^ 2
        else 0) ≤ K / (D : ℝ) := by
  obtain ⟨A, hA, hAtail⟩ := gtail_prime_tail_le
  set C : ℝ := ∑' m : ℕ, term m
  have hCnn : 0 ≤ C := tsum_nonneg term_nonneg
  refine ⟨2 * A * C + 1, by positivity, fun D hD ↦ (gtail_master D hD).trans
    ((mul_le_mul_of_nonneg_right (hAtail D hD) hCnn).trans ?_)⟩
  rw [div_mul_eq_mul_div]
  gcongr
  linarith

end PrimeGaps

/-- `(π(2N) - π(N)) * Real.log N ≤ Chebyshev.theta (2N)`, each prime in `(N, 2N]` having
`log p ≥ log N`. -/
theorem chebyshev_pi_diff_mul_log_le (N : ℕ) (hN : 1 ≤ N) :
    (((2 * N).primeCounting : ℝ) - (N.primeCounting : ℝ)) * Real.log (N : ℝ) ≤
      Chebyshev.theta (2 * N : ℕ) := by
  have hsub : N.primesLE ⊆ (2 * N).primesLE := fun p hp ↦ by
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨hp.1.trans (by omega), hp.2⟩
  rw [Chebyshev.theta_eq_sum_primesLE_log, ← Finset.sum_sdiff hsub]
  have hsmall_nonneg : (0 : ℝ) ≤ ∑ p ∈ N.primesLE, Real.log (p : ℝ) :=
    Finset.sum_nonneg fun p hp ↦
      Real.log_nonneg (by exact_mod_cast one_le_two.trans (Nat.two_le_of_mem_primesLE hp))
  have hgap : (((2 * N).primeCounting : ℝ) - (N.primeCounting : ℝ)) * Real.log (N : ℝ) ≤
      ∑ p ∈ (2 * N).primesLE \ N.primesLE, Real.log (p : ℝ) := by
    have hcard : #((2 * N).primesLE \ N.primesLE) = Nat.primeCountingIoc N (2 * N) :=
      congrArg Finset.card (Nat.primesLE_sdiff_eq_filter_Ioc N (2 * N))
    have hcardR : (#((2 * N).primesLE \ N.primesLE) : ℝ) =
        ((2 * N).primeCounting : ℝ) - (N.primeCounting : ℝ) := by
      rw [hcard, Nat.cast_primeCountingIoc (by omega)]
    rw [← hcardR, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun p hp ↦ Real.log_le_log (Nat.cast_pos.mpr hN) ?_
    obtain ⟨hpmem, hpnot⟩ := Finset.mem_sdiff.mp hp
    rw [Nat.mem_primesLE] at hpmem
    exact_mod_cast not_lt.mp fun hlt ↦ hpnot (Nat.mem_primesLE.mpr ⟨hlt.le, hpmem.2⟩)
  linarith
