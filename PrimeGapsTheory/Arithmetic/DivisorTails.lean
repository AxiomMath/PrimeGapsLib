/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Arithmetic.TdDecomposition

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Divisor-sum tail bounds

Rankin-type and Mertens-type estimates for truncated divisor sums.

## Main definitions

* `tailSum`: The outer divisor-tail sum.

## Main results

* `rankin_trick_inequality`: Rankin’s inequality for finite sums.
* `tailSum_ll`: A logarithmic bound for the divisor-tail sum.
-/

@[expose] public section

open ArithmeticFunction

open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta BigOperators ENNReal Finset NNReal

/-- The Rankin trick inequality: for non-negative `a`, `Z ≥ 1` and `κ ≥ 0`,
the finite sum `∑_{1 ≤ n ≤ Z} a(n)` is bounded by `Z^κ ∑_{n ≥ 1} a(n)/n^κ`,
the inequality being understood in `[0, +∞]`. -/
@[pg_tag "bg246" "lem_rankin_trick"]
theorem rankin_trick_inequality (a : ℕ → ℝ≥0) (Z : ℝ) (κ : ℝ) (hZ : 1 ≤ Z) (hκ : 0 ≤ κ) :
    ((∑ n ∈ Finset.Icc 1 ⌊Z⌋₊, a n : ℝ≥0) : ℝ≥0∞) ≤ (ENNReal.ofReal (Z ^ κ)) *
          ∑' n : ℕ, (a (n + 1) : ℝ≥0∞) / (ENNReal.ofReal ((n + 1 : ℝ) ^ κ)) := by
  set N := ⌊Z⌋₊
  set C : ℝ≥0∞ := ENNReal.ofReal (Z ^ κ)
  set f : ℕ → ℝ≥0∞ := fun n ↦ (a (n + 1) : ℝ≥0∞) / (ENNReal.ofReal ((n + 1 : ℝ) ^ κ)) with hf
  have hreindex : ((∑ n ∈ Finset.Icc 1 N, a n : ℝ≥0) : ℝ≥0∞) =
      ∑ m ∈ Finset.range N, (a (m + 1) : ℝ≥0∞) := by
    rw [ENNReal.ofNNReal_finsetSum, ← Finset.Ico_succ_right_eq_Icc, Order.succ_eq_add_one,
      Finset.sum_Ico_eq_sum_range]
    simp [Nat.add_comm]
  have hterm : ∀ m ∈ Finset.range N, (a (m + 1) : ℝ≥0∞) ≤ C * f m := by
    intro m hm
    simp only [Finset.mem_range] at hm
    have hbpos : (0 : ℝ) < (m + 1 : ℝ) := by positivity
    have hmZ : (m + 1 : ℝ) ≤ Z :=
      le_trans (by exact_mod_cast hm) (Nat.floor_le (by linarith))
    have hcne : ENNReal.ofReal ((m + 1 : ℝ) ^ κ) ≠ 0 := by
      simpa using Real.rpow_pos_of_pos hbpos κ
    calc (a (m + 1) : ℝ≥0∞)
        = ENNReal.ofReal ((m + 1 : ℝ) ^ κ) * f m := by
          rw [hf, mul_comm, ENNReal.div_mul_cancel hcne ENNReal.ofReal_ne_top]
      _ ≤ C * f m := by gcongr; exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hbpos.le hmZ hκ)
  rw [hreindex]
  calc (∑ m ∈ Finset.range N, (a (m + 1) : ℝ≥0∞))
      ≤ ∑ m ∈ Finset.range N, C * f m := Finset.sum_le_sum hterm
    _ = C * ∑ m ∈ Finset.range N, f m := (Finset.mul_sum _ _ _).symm
    _ ≤ C * ∑' m, f m := by gcongr; exact ENNReal.sum_le_tsum _

namespace PrimeGaps

/-- **Truncated divisor sum bound** (`lem_truncated_divisor_sum`).

For a fixed positive integer `k`, there is a constant `C(k) > 0` (uniform in `D`) such that
for every positive integer `D` and every real `Z ≥ 2`,
$$
  \sum_{\substack{r' \le Z \\ (r', D) = 1}}
    \frac{\mu(r')^2 \, \tau_k(r')}{\phi(r')} \le C(k)\,(\log Z)^k.
$$
The sum is taken over `r'` with `1 ≤ r' ≤ Z` (i.e. `r' ∈ Finset.Icc 1 ⌊Z⌋₊`) coprime to `D`. -/
@[pg_tag "bg246" "lem_truncated_divisor_sum"]
theorem lem_truncated_divisor_sum (k : ℕ) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : ℕ), 0 < D → ∀ (Z : ℝ), 2 ≤ Z →
      (∑ r' ∈ {r' ∈ Finset.Icc 1 ⌊Z⌋₊ | Nat.gcd r' D = 1},
          ((μ r' : ℝ) ^ 2 * (((ζ ^ k) r' : ℕ) : ℝ)) / (Nat.totient r' : ℝ)) ≤
        C * (Real.log Z) ^ k := by
  obtain ⟨C, hC, hbound⟩ := WeightedDivisorSum.weightedSum_le k hk
  refine ⟨C, hC, fun D _ Z hZ ↦ le_trans ?_ (hbound Z hZ)⟩
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun r' _ _ ↦ by positivity

/-- The `d`-th summand of the outer tail sum, viewed as a function of all
positive integers `d`.  It is
`μ(d)^2 / (d φ(d)) · T_d` restricted to `d > R^{1/2}`, `d` squarefree and
`gcd(d, W) = 1`, and `0` otherwise.  Only finitely many terms are nonzero
(the factor `T_d` vanishes once `d > R`), so the total sum below is well
defined. -/
noncomputable def outerSummand (R : ℝ) (W d : ℕ) : ℝ :=
  if √R < (d : ℝ) ∧ Squarefree d ∧ Nat.Coprime d W then
    ((μ d : ℝ) ^ 2) / ((d : ℝ) * (Nat.totient d : ℝ)) * PrimeGaps.T R W d
  else 0

/-- The full outer tail sum
`∑_{d > R^{1/2}, d squarefree, (d,W)=1} μ(d)^2 / (d φ(d)) · T_d`,
expressed as an (effectively finite) infinite sum over all positive integers
`d`. -/
noncomputable def tailSum (R : ℝ) (W : ℕ) : ℝ := ∑' d : ℕ, outerSummand R W d

/-- `T R W d ≤ C₁ * Real.log R` for some `C₁ > 0`, uniformly in `W` and `d`, for all `R ≥ 2`. -/
theorem innerSum_mertens_bound : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ R : ℝ, 2 ≤ R →
      ∀ W d : ℕ, PrimeGaps.T R W d ≤ C₁ * Real.log R := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := WeightedDivisorSum.weightedSum_le 1 le_rfl
  refine ⟨C₁, hC₁pos, ?_⟩
  intro R hR W d
  have hRnn : (0 : ℝ) ≤ R := by linarith
  have hsubset : {v ∈ Finset.Icc 1 ⌊R / (d : ℝ)⌋₊ | Nat.Coprime v (d * W)}
      ⊆ Finset.Icc 1 ⌊R⌋₊ := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_Icc] at hv
    obtain ⟨⟨hv1, hv2⟩, _⟩ := hv
    rw [Finset.mem_Icc]
    refine ⟨hv1, hv2.trans (Nat.floor_le_floor ?_)⟩
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · simp [hd0, hRnn]
    · exact div_le_self hRnn (by exact_mod_cast hdpos)
  have hstep1 : PrimeGaps.T R W d ≤ ∑ v ∈ Finset.Icc 1 ⌊R⌋₊, ((μ v : ℝ)) ^ 2 / (v : ℝ) := by
    simp only [PrimeGaps.T]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset fun v _ _ ↦ by positivity
  have hstep2 : ∑ v ∈ Finset.Icc 1 ⌊R⌋₊, ((μ v : ℝ)) ^ 2 / (v : ℝ) ≤
      WeightedDivisorSum.weightedSum 1 R := by
    unfold WeightedDivisorSum.weightedSum
    refine Finset.sum_le_sum fun v hv ↦ ?_
    rw [Finset.mem_Icc] at hv
    have hvne : v ≠ 0 := by omega
    rw [pow_one, ArithmeticFunction.zeta_apply_ne hvne, Nat.cast_one, mul_one]
    exact div_le_div_of_nonneg_left (by positivity)
      (by exact_mod_cast Nat.totient_pos.mpr (by omega)) (by exact_mod_cast Nat.totient_le v)
  have hstep3 := hC₁ R hR
  rw [pow_one] at hstep3
  linarith

/-- The divisor-counting function `(ζ ^ 2) d` is the number of divisors of `d`. -/
private lemma zeta_sq_apply (d : ℕ) : (ζ ^ 2) d = #d.divisors := by
  rw [sq, ← ArithmeticFunction.sigma_zero_apply, ← ArithmeticFunction.zeta_mul_pow_eq_sigma,
    ArithmeticFunction.pow_zero_eq_zeta]

/-- `outerSummand R W d ≤ (C₁ * Real.log R) * (ζ ^ 2) d / d ^ 2`, given `T R W d ≤ C₁ * log R`. -/
theorem outerSummand_support_bound (R : ℝ) (W : ℕ) (C₁ : ℝ) (hC₁ : 0 < C₁)
    (hInner : ∀ d : ℕ, PrimeGaps.T R W d ≤ C₁ * Real.log R)
    (hlogpos : 0 ≤ Real.log R) :
    ∀ d : ℕ, outerSummand R W d ≤ (C₁ * Real.log R) *
          ((ζ ^ 2) d : ℝ) / (d : ℝ) ^ 2 := by
  have hInnerNonneg : ∀ d : ℕ, 0 ≤ PrimeGaps.T R W d := fun _ ↦
    Finset.sum_nonneg fun _ _ ↦ by positivity
  have htau : ∀ d : ℕ, 0 < d → d ≤ (ζ ^ 2) d * Nat.totient d := by
    intro d hd
    rw [zeta_sq_apply]
    calc d = ∑ i ∈ d.divisors, Nat.totient i := (Nat.sum_totient d).symm
      _ ≤ ∑ _i ∈ d.divisors, Nat.totient d :=
            Finset.sum_le_sum fun i hi ↦ Nat.le_of_dvd (Nat.totient_pos.mpr hd)
              (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hi))
      _ = #d.divisors * Nat.totient d := by rw [Finset.sum_const, smul_eq_mul]
  intro d
  by_cases h : √R < (d : ℝ) ∧ Squarefree d ∧ Nat.Coprime d W
  · have hdpos : 0 < d := by exact_mod_cast lt_of_le_of_lt (Real.sqrt_nonneg R) h.1
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
    have hφpos : (0 : ℝ) < (Nat.totient d : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hdpos
    have hmoeb : ((μ d : ℝ)) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree h.2.1
    unfold outerSummand
    rw [if_pos h, hmoeb]
    set tau : ℝ := ((ζ ^ 2) d : ℝ) with htaudef
    have hbound : (d : ℝ) ≤ tau * (Nat.totient d : ℝ) := by
      rw [htaudef]; exact_mod_cast htau d hdpos
    have hkey : 1 / ((d : ℝ) * (Nat.totient d : ℝ)) ≤ tau / (d : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hbound hdR.le]
    calc 1 / ((d : ℝ) * (Nat.totient d : ℝ)) * PrimeGaps.T R W d
        ≤ (tau / (d : ℝ) ^ 2) * PrimeGaps.T R W d :=
          mul_le_mul_of_nonneg_right hkey (hInnerNonneg d)
      _ ≤ (tau / (d : ℝ) ^ 2) * (C₁ * Real.log R) :=
          mul_le_mul_of_nonneg_left (hInner d) (by positivity)
      _ = C₁ * Real.log R * tau / (d : ℝ) ^ 2 := by ring
  · unfold outerSummand
    rw [if_neg h]
    positivity

/-- Summability of `d ↦ (ζ ^ 2) d / d ^ 2`, the divisor Dirichlet series at `s = 2`. -/
theorem divisorSeries_summable :
    Summable (fun d : ℕ ↦ ((ζ ^ 2) d : ℝ) / (d : ℝ) ^ 2) := by
  have hz : LSeriesSummable (fun x ↦ ((ζ x : ℕ) : ℂ)) (2 : ℂ) := by
    rw [ArithmeticFunction.LSeriesSummable_zeta_iff]; norm_num
  have hz' : LSeriesSummable
      (fun n ↦ ((↑ζ : ArithmeticFunction ℂ) n)) (2 : ℂ) := by
    convert hz using 2 with n
    rw [ArithmeticFunction.natCoe_apply]
  have hmul := ArithmeticFunction.LSeriesSummable_mul hz' hz'
  have hprod : ((↑ζ : ArithmeticFunction ℂ) * (↑ζ : ArithmeticFunction ℂ)) =
      (↑(ζ ^ 2) : ArithmeticFunction ℂ) := by
    rw [sq, ArithmeticFunction.natCoe_mul]
  rw [hprod, LSeriesSummable] at hmul
  have hmul2 : Summable (fun n ↦ (((if n = 0 then (0 : ℝ)
      else ((ζ ^ 2) n : ℝ) / (n : ℝ) ^ 2) : ℝ) : ℂ)) := by
    refine hmul.congr fun n ↦ ?_
    rw [LSeries.term_def]
    by_cases hn : n = 0
    · simp [hn]
    · rw [if_neg hn, if_neg hn, ArithmeticFunction.natCoe_apply,
        show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
      push_cast; ring
  rw [Complex.summable_ofReal] at hmul2
  refine hmul2.congr fun n ↦ ?_
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn]

/-- Zeroing out an arbitrary set of terms of the divisor Dirichlet series at `s = 2`
leaves a summable series. -/
private lemma summable_divisorSeries_ite {P : ℕ → Prop} (inst : DecidablePred P) :
    Summable fun d : ℕ ↦
      if P d then ((ζ ^ 2) d : ℝ) / (d : ℝ) ^ 2 else 0 := by
  refine Summable.of_nonneg_of_le (fun d ↦ ?_) (fun d ↦ ?_) divisorSeries_summable
  · split <;> positivity
  · split
    · exact le_rfl
    · positivity

/-- Both entries of a pair in `d.divisorsAntidiagonal` are positive. -/
private lemma one_le_of_mem_divisorsAntidiagonal {d : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ d.divisorsAntidiagonal) : 1 ≤ q.1 ∧ 1 ≤ q.2 :=
  ⟨Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hq),
    Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hq)⟩

/-- Hyperbola reindexing `d = (a+1)(e+1)` in `ℝ≥0∞`:
`∑_{d > x} (ζ ^ 2) d / d ^ 2 = ∑_{a,e : x < (a+1)(e+1)} 1 / ((a+1)(e+1)) ^ 2`. -/
theorem dtb_bridge (x : ℝ) : (∑' d : ℕ, ENNReal.ofReal
        (if x < (d : ℝ) then ((ζ ^ 2) d : ℝ) / (d : ℝ) ^ 2 else 0)) =
      ∑' a : ℕ, ∑' e : ℕ, ENNReal.ofReal (if x < (((a + 1 : ℕ) : ℝ) * ((e + 1 : ℕ) : ℝ))
           then 1 / (((a + 1 : ℕ) : ℝ) * ((e + 1 : ℕ) : ℝ)) ^ 2 else 0) := by
  set F : ℕ × ℕ → ℝ≥0∞ := fun p ↦ ENNReal.ofReal
    (if x < (((p.1 + 1 : ℕ) : ℝ) * ((p.2 + 1 : ℕ) : ℝ))
     then 1 / (((p.1 + 1 : ℕ) : ℝ) * ((p.2 + 1 : ℕ) : ℝ)) ^ 2 else 0) with hFdef
  set g : ℕ × ℕ → ℕ := fun p ↦ (p.1 + 1) * (p.2 + 1) with hgdef
  have hRHS : (∑' a : ℕ, ∑' e : ℕ, ENNReal.ofReal (if x < (((a + 1 : ℕ) : ℝ) * ((e + 1 : ℕ) : ℝ))
           then 1 / (((a + 1 : ℕ) : ℝ) * ((e + 1 : ℕ) : ℝ)) ^ 2 else 0)) = ∑' p : ℕ × ℕ, F p := by
    rw [← ENNReal.tsum_prod]
  rw [hRHS, ← ENNReal.tsum_fiberwise F g]
  refine tsum_congr fun d ↦ ?_
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · have hempty : g ⁻¹' {0} = (∅ : Set (ℕ × ℕ)) := by
      ext p
      simp only [Set.mem_preimage, Set.mem_singleton_iff, hgdef, Set.mem_empty_iff_false, iff_false]
      exact Nat.mul_ne_zero (Nat.succ_ne_zero _) (Nat.succ_ne_zero _)
    rw [hempty, tsum_empty]
    simp
  · set S : Finset (ℕ × ℕ) := d.divisorsAntidiagonal.image (fun q ↦ (q.1 - 1, q.2 - 1)) with hSdef
    have hset : g ⁻¹' {d} = ↑S := by
      ext p
      simp only [Set.mem_preimage, Set.mem_singleton_iff, hgdef, hSdef, Finset.coe_image,
        Set.mem_image, Finset.mem_coe, Nat.mem_divisorsAntidiagonal]
      refine ⟨fun hp ↦ ⟨(p.1 + 1, p.2 + 1), ⟨hp, by omega⟩, by simp⟩, ?_⟩
      rintro ⟨q, hq, rfl⟩
      obtain ⟨h1, h2⟩ := one_le_of_mem_divisorsAntidiagonal (Nat.mem_divisorsAntidiagonal.mpr hq)
      simp only
      rw [Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
      exact hq.1
    rw [hset, Finset.tsum_subtype' S F]
    have hinj : Set.InjOn (fun q : ℕ × ℕ ↦ (q.1 - 1, q.2 - 1))
        (d.divisorsAntidiagonal : Set (ℕ × ℕ)) := by
      intro a ha b hb hab
      obtain ⟨ha1, ha2⟩ := one_le_of_mem_divisorsAntidiagonal (Finset.mem_coe.mp ha)
      obtain ⟨hb1, hb2⟩ := one_le_of_mem_divisorsAntidiagonal (Finset.mem_coe.mp hb)
      simp only [Prod.mk.injEq] at hab
      obtain ⟨e1, e2⟩ := hab
      ext <;> omega
    rw [hSdef, Finset.sum_image hinj]
    have hterm : ∀ q ∈ d.divisorsAntidiagonal,
        F (q.1 - 1, q.2 - 1) = ENNReal.ofReal (if x < (d : ℝ) then 1 / (d : ℝ) ^ 2 else 0) := by
      intro q hq
      obtain ⟨h1, h2⟩ := one_le_of_mem_divisorsAntidiagonal hq
      rw [Nat.mem_divisorsAntidiagonal] at hq
      simp only [hFdef]
      rw [show q.1 - 1 + 1 = q.1 from by omega, show q.2 - 1 + 1 = q.2 from by omega,
        show ((q.1 : ℝ)) * ((q.2 : ℝ)) = (d : ℝ) from by rw [← Nat.cast_mul, hq.1]]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const,
      show #d.divisorsAntidiagonal = (ζ ^ 2) d from by
        rw [zeta_sq_apply, ← Nat.map_div_right_divisors, Finset.card_map],
      nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    split
    · rw [mul_one_div]
    · rw [mul_zero]

/-- `∑_{b : y < b + 1} 1 / (b+1) ^ 2 ≤ 2 / y` for `y > 0`. -/
theorem dtb_tail_sq (y : ℝ) (hy : 0 < y) :
    (∑' b : ℕ, (if y < ((b + 1 : ℕ) : ℝ) then 1 / ((b + 1 : ℕ) : ℝ) ^ 2 else 0)) ≤ 2 / y := by
  set k : ℕ := ⌊y⌋₊
  refine Real.tsum_le_of_sum_range_le (fun n ↦ by split <;> positivity) fun n ↦ ?_
  simp only [one_div]
  rw [← Finset.sum_filter]
  set F := {b ∈ Finset.range n | y < ((b + 1 : ℕ) : ℝ)} with hF
  have hinj : Set.InjOn (fun b : ℕ ↦ b + 1) (F : Set ℕ) := fun a _ b _ hab ↦ by simpa using hab
  have hsub : F.image (fun b : ℕ ↦ b + 1) ⊆ Finset.Ioo k (n + 1) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨b, hb, rfl⟩ := hi
    rw [hF, Finset.mem_filter, Finset.mem_range] at hb
    rw [Finset.mem_Ioo]
    exact ⟨by exact_mod_cast lt_of_le_of_lt (Nat.floor_le hy.le) hb.2, by omega⟩
  calc ∑ b ∈ F, (((b + 1 : ℕ) : ℝ) ^ 2)⁻¹
      = ∑ i ∈ F.image (fun b : ℕ ↦ b + 1), ((i : ℝ) ^ 2)⁻¹ :=
        (Finset.sum_image (f := fun i : ℕ ↦ ((i : ℝ) ^ 2)⁻¹) hinj).symm
    _ ≤ ∑ i ∈ Finset.Ioo k (n + 1), ((i : ℝ) ^ 2)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ ↦ by positivity
    _ ≤ 2 / ((k : ℝ) + 1) := sum_Ioo_inv_sq_le k (n + 1)
    _ ≤ 2 / y := by
        refine div_le_div_of_nonneg_left (by norm_num) hy ?_
        linarith [Nat.lt_floor_add_one y]

/-- `∑' b, 1 / (b+1) ^ 2 ≤ 2`. -/
theorem dtb_full_sq : (∑' b : ℕ, 1 / ((b + 1 : ℕ) : ℝ) ^ 2) ≤ 2 := by
  refine Real.tsum_le_of_sum_range_le (fun n ↦ by positivity) fun n ↦ ?_
  have hinj : Set.InjOn (fun b : ℕ ↦ b + 1) (Finset.range n : Set ℕ) :=
    fun a _ b _ hab ↦ by simpa using hab
  have hsub : (Finset.range n).image (fun b : ℕ ↦ b + 1) ⊆ Finset.Ioo 0 (n + 1) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨b, hb, rfl⟩ := hi
    rw [Finset.mem_range] at hb
    rw [Finset.mem_Ioo]
    omega
  calc ∑ i ∈ Finset.range n, 1 / ((i + 1 : ℕ) : ℝ) ^ 2
      = ∑ i ∈ (Finset.range n).image (fun b : ℕ ↦ b + 1), ((i : ℝ) ^ 2)⁻¹ := by
        rw [Finset.sum_image hinj]; simp [one_div]
    _ ≤ ∑ i ∈ Finset.Ioo 0 (n + 1), ((i : ℝ) ^ 2)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ ↦ by positivity
    _ ≤ 2 / ((0 : ℕ) + 1) := sum_Ioo_inv_sq_le 0 (n + 1)
    _ = 2 := by norm_num

/-- `∑_{a : a + 1 ≤ x} 1 / (a+1) ≤ Real.log x + 1` for `x ≥ 1`. -/
theorem dtb_harmonic (x : ℝ) (hx : 1 ≤ x) :
    (∑' a : ℕ, (if ((a + 1 : ℕ) : ℝ) ≤ x then 1 / ((a + 1 : ℕ) : ℝ) else 0)) ≤ Real.log x + 1 := by
  have hzero : ∀ a ∉ Finset.range ⌊x⌋₊,
      (if ((a + 1 : ℕ) : ℝ) ≤ x then 1 / ((a + 1 : ℕ) : ℝ) else 0) = 0 := by
    intro a ha
    rw [Finset.mem_range, not_lt] at ha
    refine if_neg fun hle ↦ ?_
    have : a + 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hle)
    omega
  have htrue : ∀ a ∈ Finset.range ⌊x⌋₊,
      (if ((a + 1 : ℕ) : ℝ) ≤ x then 1 / ((a + 1 : ℕ) : ℝ) else 0) = 1 / ((a + 1 : ℕ) : ℝ) := by
    intro a ha
    rw [Finset.mem_range] at ha
    exact if_pos <| le_trans (by exact_mod_cast Nat.succ_le_of_lt ha) (Nat.floor_le (by linarith))
  have hharm : ∑ a ∈ Finset.range ⌊x⌋₊, 1 / ((a + 1 : ℕ) : ℝ) = (harmonic ⌊x⌋₊ : ℝ) := by
    simp [harmonic, one_div]
  rw [tsum_eq_sum hzero, Finset.sum_congr rfl htrue, hharm]
  linarith [harmonic_floor_le_one_add_log x hx]

/-- The series `∑ 1 / (e+1) ^ 2` is summable. -/
private lemma summable_one_div_natSucc_sq : Summable (fun e : ℕ ↦ 1 / ((e + 1 : ℕ) : ℝ) ^ 2) := by
  refine ((summable_nat_add_iff 1).mpr
    ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num))).congr fun n ↦ ?_
  push_cast
  ring

/-- The inner tail of the divisor series: for `A > 0` and `x > 0`,
`∑'_e [x < A·(e+1)] / (A·(e+1))²` is at most `2/(A·x)` when `A ≤ x`, and at most `2/A²`
otherwise. -/
private lemma tsum_ofReal_scaled_tail_sq_le {A x : ℝ} (hA : 0 < A) (hx : 0 < x) :
    (∑' e : ℕ, ENNReal.ofReal (if x < (A * ((e + 1 : ℕ) : ℝ))
        then 1 / (A * ((e + 1 : ℕ) : ℝ)) ^ 2 else 0)) ≤
      ENNReal.ofReal (if A ≤ x then 2 / (A * x) else 2 / A ^ 2) := by
  have hstep : ∀ e : ℕ, ENNReal.ofReal (if x < (A * ((e + 1 : ℕ) : ℝ))
         then 1 / (A * ((e + 1 : ℕ) : ℝ)) ^ 2 else 0) =
      ENNReal.ofReal (1 / A ^ 2) * ENNReal.ofReal
        (if x / A < ((e + 1 : ℕ) : ℝ) then 1 / ((e + 1 : ℕ) : ℝ) ^ 2 else 0) := by
    intro e
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hcond : (x < A * ((e + 1 : ℕ) : ℝ)) ↔ (x / A < ((e + 1 : ℕ) : ℝ)) := by
      rw [div_lt_iff₀ hA, mul_comm]
    by_cases hc : x / A < ((e + 1 : ℕ) : ℝ)
    · rw [if_pos (hcond.mpr hc), if_pos hc, mul_pow]
      field_simp
    · rw [if_neg (fun h ↦ hc (hcond.mp h)), if_neg hc, mul_zero]
  rw [tsum_congr hstep, ENNReal.tsum_mul_left]
  set g : ℕ → ℝ := fun i ↦
    if x / A < ((i + 1 : ℕ) : ℝ) then 1 / ((i + 1 : ℕ) : ℝ) ^ 2 else 0 with hgdef
  have hg_nn : ∀ i, 0 ≤ g i := by intro i; rw [hgdef]; dsimp only; split <;> positivity
  have hg_le : ∀ i, g i ≤ 1 / ((i + 1 : ℕ) : ℝ) ^ 2 := by
    intro i; rw [hgdef]; dsimp only; split
    · exact le_rfl
    · positivity
  have hg_summable : Summable g := Summable.of_nonneg_of_le hg_nn hg_le summable_one_div_natSucc_sq
  have hgeq : (∑' i : ℕ, ENNReal.ofReal
        (if x / A < ((i + 1 : ℕ) : ℝ) then 1 / ((i + 1 : ℕ) : ℝ) ^ 2 else 0)) =
      ENNReal.ofReal (∑' i, g i) := (ENNReal.ofReal_tsum_of_nonneg hg_nn hg_summable).symm
  rw [hgeq, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  by_cases hAx : A ≤ x
  · rw [if_pos hAx]
    have hinner_le : (∑' i, g i) ≤ 2 / (x / A) := by
      rw [hgdef]; exact dtb_tail_sq (x / A) (by positivity)
    rw [show (2 : ℝ) / (x / A) = 2 * A / x by field_simp] at hinner_le
    calc 1 / A ^ 2 * (∑' i, g i) ≤ 1 / A ^ 2 * (2 * A / x) :=
          mul_le_mul_of_nonneg_left hinner_le (by positivity)
      _ = 2 / (A * x) := by field_simp
  · rw [if_neg hAx]
    have hinner_le : (∑' i, g i) ≤ 2 :=
      le_trans (Summable.tsum_le_tsum hg_le hg_summable summable_one_div_natSucc_sq) dtb_full_sq
    calc 1 / A ^ 2 * (∑' i, g i) ≤ 1 / A ^ 2 * 2 :=
          mul_le_mul_of_nonneg_left hinner_le (by positivity)
      _ = 2 / A ^ 2 := by ring

/-- `∑_{d > x} (ζ ^ 2) d / d ^ 2 ≤ 8 * (Real.log x + 1) / x` for `x ≥ 1`. -/
theorem divisor_tail_bound (x : ℝ) (hx : 1 ≤ x) :
    (∑' d : ℕ, (if x < (d : ℝ) then ((ζ ^ 2) d : ℝ) / (d : ℝ) ^ 2 else 0)) ≤
      8 * (Real.log x + 1) / x := by
  have hx0 : 0 < x := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hf_summable : Summable (fun d : ℕ ↦
      if x < (d : ℝ) then ((ζ ^ 2) d : ℝ) / (d : ℝ) ^ 2 else 0) :=
    summable_divisorSeries_ite _
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity),
    ENNReal.ofReal_tsum_of_nonneg (fun d ↦ by split <;> positivity) hf_summable, dtb_bridge x]
  have hinner : ∀ a : ℕ, (∑' e : ℕ, ENNReal.ofReal (if x < (((a + 1 : ℕ) : ℝ) * ((e + 1 : ℕ) : ℝ))
         then 1 / (((a + 1 : ℕ) : ℝ) * ((e + 1 : ℕ) : ℝ)) ^ 2 else 0)) ≤
      ENNReal.ofReal (if ((a + 1 : ℕ) : ℝ) ≤ x then 2 / (((a + 1 : ℕ) : ℝ) * x)
                        else 2 / ((a + 1 : ℕ) : ℝ) ^ 2) := fun a ↦
    tsum_ofReal_scaled_tail_sq_le (by exact_mod_cast Nat.succ_pos a) hx0
  refine le_trans (ENNReal.tsum_le_tsum hinner) ?_
  set P1 : ℕ → ℝ := fun a ↦
    if ((a + 1 : ℕ) : ℝ) ≤ x then 2 / (((a + 1 : ℕ) : ℝ) * x) else 0 with hP1def
  set P2 : ℕ → ℝ := fun a ↦
    if x < ((a + 1 : ℕ) : ℝ) then 2 / ((a + 1 : ℕ) : ℝ) ^ 2 else 0 with hP2def
  have hsplit : ∀ a : ℕ, ENNReal.ofReal (if ((a + 1 : ℕ) : ℝ) ≤ x then 2 / (((a + 1 : ℕ) : ℝ) * x)
        else 2 / ((a + 1 : ℕ) : ℝ) ^ 2) = ENNReal.ofReal (P1 a) + ENNReal.ofReal (P2 a) := by
    intro a
    rw [hP1def, hP2def]; dsimp only
    by_cases h : ((a + 1 : ℕ) : ℝ) ≤ x
    · rw [if_pos h, if_pos h, if_neg (by linarith), ENNReal.ofReal_zero, add_zero]
    · rw [if_neg h, if_neg h, if_pos (by push Not at h; linarith), ENNReal.ofReal_zero, zero_add]
  rw [tsum_congr hsplit]
  have hP1_nn : ∀ a, 0 ≤ P1 a := by intro a; rw [hP1def]; dsimp only; split <;> positivity
  have hP2_nn : ∀ a, 0 ≤ P2 a := by intro a; rw [hP2def]; dsimp only; split <;> positivity
  have hP2_summable : Summable P2 := by
    apply Summable.of_nonneg_of_le hP2_nn (fun a ↦ ?_) (summable_one_div_natSucc_sq.mul_left 2)
    rw [hP2def]; dsimp only; split
    · rw [mul_one_div]
    · positivity
  have hP1_summable : Summable P1 := by
    have hfin : Summable (fun a : ℕ ↦
        (2 / x) * (if ((a + 1 : ℕ) : ℝ) ≤ x then 1 / ((a + 1 : ℕ) : ℝ) else 0)) := by
      refine Summable.mul_left _ (summable_of_ne_finset_zero (s := Finset.range ⌊x⌋₊) fun a ha ↦ ?_)
      rw [Finset.mem_range, not_lt] at ha
      refine if_neg fun hle ↦ ?_
      have : a + 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hle)
      omega
    apply Summable.of_nonneg_of_le hP1_nn (fun a ↦ ?_) hfin
    rw [hP1def]; dsimp only; split
    · rw [mul_one_div]
      exact le_of_eq (by field_simp)
    · positivity
  rw [ENNReal.tsum_add, ← ENNReal.ofReal_tsum_of_nonneg hP1_nn hP1_summable,
      ← ENNReal.ofReal_tsum_of_nonneg hP2_nn hP2_summable]
  have hP1bound : (∑' n, P1 n) ≤ (2 / x) * (Real.log x + 1) := by
    have hfactor : ∀ n : ℕ,
        P1 n = (2 / x) * (if ((n + 1 : ℕ) : ℝ) ≤ x then 1 / ((n + 1 : ℕ) : ℝ) else 0) := by
      intro n; rw [hP1def]; dsimp only; split
      · rw [mul_one_div]; field_simp
      · rw [mul_zero]
    rw [tsum_congr hfactor, tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (dtb_harmonic x hx) (by positivity)
  have hP2bound : (∑' n, P2 n) ≤ 4 / x := by
    have hfactor : ∀ n : ℕ,
        P2 n = 2 * (if x < ((n + 1 : ℕ) : ℝ) then 1 / ((n + 1 : ℕ) : ℝ) ^ 2 else 0) := by
      intro n; rw [hP2def]; dsimp only; split
      · rw [mul_one_div]
      · rw [mul_zero]
    rw [tsum_congr hfactor, tsum_mul_left]
    calc 2 * (∑' n, if x < ((n + 1 : ℕ) : ℝ) then 1 / ((n + 1 : ℕ) : ℝ) ^ 2 else 0)
        ≤ 2 * (2 / x) := mul_le_mul_of_nonneg_left (dtb_tail_sq x hx0) (by norm_num)
      _ = 4 / x := by ring
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal <| le_trans (add_le_add hP1bound hP2bound) ?_
  rw [show (2 / x) * (Real.log x + 1) + 4 / x = (2 * (Real.log x + 1) + 4) / x by field_simp,
    show (8 : ℝ) * (Real.log x + 1) / x = (8 * (Real.log x + 1)) / x by ring,
    div_le_div_iff_of_pos_right hx0]
  linarith

/-- `∑_{d > √R, d squarefree, (d,W) = 1} (ζ ^ 2) d / d ^ 2 ≤ C₂ * Real.log R ^ 2 / √R` for some
`C₂ > 0` and all `R ≥ 2`. -/
theorem rankin_divisor_tail : ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ R : ℝ, 2 ≤ R → ∀ W : ℕ,
      (∑' d : ℕ, (if √R < (d : ℝ) ∧ Squarefree d ∧ Nat.Coprime d W
          then ((ζ ^ 2) d : ℝ) / (d : ℝ) ^ 2 else 0)) ≤ C₂ * (Real.log R) ^ 2 / √R := by
  refine ⟨24, by norm_num, ?_⟩
  intro R hR W
  have hR1 : (1 : ℝ) ≤ R := by linarith
  have hsqrt1 : (1 : ℝ) ≤ √R := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_le_sqrt hR1
  have hsqrtpos : 0 < √R := by linarith
  have hterm_le : ∀ d : ℕ, (if √R < (d : ℝ) ∧ Squarefree d ∧ Nat.Coprime d W
          then ((ζ ^ 2) d : ℝ) / (d : ℝ) ^ 2 else 0) ≤
        (if √R < (d : ℝ) then ((ζ ^ 2) d : ℝ) / (d : ℝ) ^ 2 else 0) := by
    intro d
    by_cases h : √R < (d : ℝ) ∧ Squarefree d ∧ Nat.Coprime d W
    · rw [if_pos h, if_pos h.1]
    · rw [if_neg h]
      split <;> positivity
  have hlogsqrt : Real.log (√R) = Real.log R / 2 := by
    rw [Real.sqrt_eq_rpow, Real.log_rpow (by linarith)]; ring
  have hlogR2 : Real.log 2 ≤ Real.log R := Real.log_le_log (by norm_num) hR
  have hlog2 : (0.6931471803 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogRpos : 0 < Real.log R := lt_of_lt_of_le (by linarith) hlogR2
  refine le_trans (Summable.tsum_le_tsum hterm_le (summable_divisorSeries_ite _)
    (summable_divisorSeries_ite _)) <| le_trans (divisor_tail_bound (√R) hsqrt1) ?_
  rw [div_le_div_iff_of_pos_right hsqrtpos, hlogsqrt]
  nlinarith [sq_nonneg (Real.log R), hlogRpos, hlogR2, hlog2]

open scoped PrimeGaps.sieveTruncation in
/-- **Rankin's trick tail bound.**  For fixed `θ ∈ (0,1)` and `δ` with
`0 < δ < θ/2`, there is a constant `C > 0` such that for all sufficiently
large `N`,
`|tailSum R (W₀ N)| ≤ C · (log R)^3 / R^{1/2}` for an arbitrary modulus family `W₀`.
Equivalently, `tailSum R (W₀ N) ≪ (log R)^3 / R^{1/2}`
as `N → ∞`. -/
@[pg_tag "bg246" "slem_mertens_W_tail_d"]
theorem tailSum_ll (W₀ : ℕ → ℕ) (θ : ℝ) (δ : ℝ) (hδθ : δ < θ / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in Filter.atTop,
      |tailSum R (W₀ N)| ≤ C * (Real.log R) ^ 3 / √R := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := innerSum_mertens_bound
  obtain ⟨C₂, hC₂pos, hC₂⟩ := rankin_divisor_tail
  refine ⟨C₁ * C₂, by positivity, ?_⟩
  filter_upwards [R_eventually_ge θ δ hδθ 2] with N hR
  have hlogpos : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
  have hInnerNonneg : ∀ d : ℕ, 0 ≤ PrimeGaps.T R (W₀ N) d := fun _ ↦
    Finset.sum_nonneg fun _ _ ↦ by positivity
  have hnn : ∀ d : ℕ, 0 ≤ outerSummand R (W₀ N) d := by
    intro d
    unfold outerSummand
    split
    · exact mul_nonneg (by positivity) (hInnerNonneg d)
    · exact le_rfl
  set S : ℕ → ℝ := fun d ↦ if √R < (d : ℝ) ∧ Squarefree d ∧ Nat.Coprime d (W₀ N)
      then ((ζ ^ 2) d : ℝ) / (d : ℝ) ^ 2 else 0 with hSdef
  have hSupport := outerSummand_support_bound R (W₀ N) C₁ hC₁pos (hC₁ R hR (W₀ N)) hlogpos
  have hterm : ∀ d, outerSummand R (W₀ N) d ≤ (C₁ * Real.log R) * S d := by
    intro d
    rw [hSdef]; dsimp only
    by_cases h : √R < (d : ℝ) ∧ Squarefree d ∧ Nat.Coprime d (W₀ N)
    · rw [if_pos h]
      calc outerSummand R (W₀ N) d
          ≤ (C₁ * Real.log R) * ((ζ ^ 2) d : ℝ) / (d : ℝ) ^ 2 := hSupport d
        _ = (C₁ * Real.log R) * (((ζ ^ 2) d : ℝ) / (d : ℝ) ^ 2) := by ring
    · rw [if_neg h, mul_zero]
      unfold outerSummand
      rw [if_neg h]
  have hRHSsummable : Summable (fun d ↦ (C₁ * Real.log R) * S d) :=
    (hSdef ▸ summable_divisorSeries_ite (P := fun d ↦ √R < (d : ℝ) ∧ Squarefree d ∧
      Nat.Coprime d (W₀ N)) _).mul_left _
  rw [show tailSum R (W₀ N) = ∑' d, outerSummand R (W₀ N) d from rfl,
    abs_of_nonneg (tsum_nonneg hnn)]
  calc ∑' d, outerSummand R (W₀ N) d ≤ ∑' d, (C₁ * Real.log R) * S d :=
      Summable.tsum_le_tsum hterm (Summable.of_nonneg_of_le hnn hterm hRHSsummable) hRHSsummable
    _ = (C₁ * Real.log R) * ∑' d, S d := tsum_mul_left
    _ ≤ (C₁ * Real.log R) * (C₂ * (Real.log R) ^ 2 / √R) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hSdef]
          exact hC₂ R hR (W₀ N)
    _ = (C₁ * C₂) * (Real.log R) ^ 3 / √R := by ring

end PrimeGaps
