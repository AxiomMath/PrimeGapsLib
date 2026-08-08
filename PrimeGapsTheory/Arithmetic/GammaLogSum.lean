/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.NumberTheory.SumPrimeReciprocals
public import PrimeGapsTheory.NumberTheory.PrimeSumEstimates
public import PrimeGapsTheory.Foundations.SieveDatum
import PrimeGapsTheory.Tactic.PaperTag

/-!
# Weighted prime logarithmic sums

Bounds for weighted prime logarithmic sums associated with `W`-tricked density functions.

## Main definitions

* `primeLogSum`: The plain logarithmic prime sum.
* `IsWTrickedFamily`: The predicate for a `W`-tricked family of densities.

## Main results

* `two_sided_estimate`: A two-sided estimate for the weighted prime logarithmic sum.
* `lower_bound_L`: A lower bound for the logarithmic sum.
-/

@[expose] public section

namespace Real

/-- `log p ≤ 2 * √p` for `p ≥ 1`. -/
theorem log_le_two_sqrt (p : ℝ) (hp : 0 < p) : Real.log p ≤ 2 * √p := by
  rw [Real.sqrt_eq_rpow]
  linarith [Real.log_le_rpow_div hp.le one_half_pos]

end Real

namespace PrimeGaps

/-- Every term `2 log p / p²` of the prime-square log series is nonnegative. -/
private lemma two_log_div_sq_nonneg (q : Nat.Primes) :
    0 ≤ 2 * Real.log ((q : ℕ) : ℝ) / ((q : ℕ) : ℝ) ^ 2 := by
  positivity

/-- The prime-square log series `∑_p 2 log p / p²` is summable (over `Nat.Primes`). -/
theorem summable_two_log_div_sq :
    Summable (fun p : Nat.Primes ↦ 2 * Real.log (p : ℝ) / (p : ℝ) ^ 2) := by
  have hb4 : Summable (fun p : Nat.Primes ↦ 4 * (p : ℝ) ^ (-(3 / 2) : ℝ)) :=
    (Nat.Primes.summable_rpow.mpr (by norm_num)).mul_left 4
  refine Summable.of_nonneg_of_le two_log_div_sq_nonneg ?_ hb4
  intro p
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  rw [show ((p : ℝ)) ^ (-(3 / 2) : ℝ) = √(p : ℝ) / (p : ℝ) ^ 2 by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (p : ℝ) 2, ← Real.rpow_sub hppos]; norm_num,
    ← mul_div_assoc, div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < (p : ℝ) ^ 2)]
  linarith [Real.log_le_two_sqrt (p : ℝ) hppos]

/-- The prime-square log series `∑'_p 2 log p / p²` has nonnegative sum. -/
private lemma tsum_two_log_div_sq_nonneg :
    0 ≤ ∑' p : Nat.Primes, 2 * Real.log (p : ℝ) / (p : ℝ) ^ 2 :=
  tsum_nonneg two_log_div_sq_nonneg

/-- A finite sum of `2 log p / p²` taken over a finset of naturals that are all prime is
bounded by the full prime series `∑'_p 2 log p / p²`. -/
private lemma sum_two_log_div_sq_le_tsum {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) :
    ∑ p ∈ S, 2 * Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤
      ∑' p : Nat.Primes, 2 * Real.log (p : ℝ) / (p : ℝ) ^ 2 := by
  set e : {x // x ∈ S} → Nat.Primes := fun q ↦ ⟨q.1, hS q.1 q.2⟩
  set G : Finset Nat.Primes := S.attach.image e with hG
  have hcast : ∑ p ∈ S, 2 * Real.log (p : ℝ) / (p : ℝ) ^ 2 =
      ∑ q ∈ G, 2 * Real.log ((q : ℕ) : ℝ) / ((q : ℕ) : ℝ) ^ 2 := by
    rw [hG, Finset.sum_image]
    · rw [← Finset.sum_attach S fun p ↦ 2 * Real.log (p : ℝ) / (p : ℝ) ^ 2]
    · exact fun x _ y _ hxy ↦ Subtype.ext (congrArg (fun p : Nat.Primes ↦ (p : ℕ)) hxy)
  rw [hcast]
  exact summable_two_log_div_sq.sum_le_tsum G fun q _ ↦ two_log_div_sq_nonneg q

/-- The geometric tail of the prime-power log series: for `p ≥ 2` and any cutoff `K`,
`∑_{2 ≤ k ≤ K} log p / p ^ k ≤ 2 log p / p ^ 2`. -/
private lemma sum_Icc_two_log_div_pow_le (K : ℕ) {p : ℕ} (hp : 2 ≤ p) :
    ∑ k ∈ Finset.Icc 2 K, Real.log p / (p : ℝ) ^ k ≤ 2 * Real.log p / (p : ℝ) ^ 2 := by
  have hpR2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hlogp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hrw : ∑ k ∈ Finset.Icc 2 K, Real.log p / (p : ℝ) ^ k =
      Real.log p * ∑ k ∈ Finset.Icc 2 K, ((1 : ℝ) / (p : ℝ)) ^ k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [div_pow, one_pow]; field_simp
  rw [hrw]
  set x := (1 : ℝ) / (p : ℝ) with hx
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hx1 : x < 1 := by rw [hx, div_lt_one hppos]; linarith
  have hxhalf : x ≤ 1 / 2 := by
    rw [hx, one_div_le_one_div hppos (by norm_num : (0 : ℝ) < 2)]; linarith
  have hbound : ∑ k ∈ Finset.Icc 2 K, x ^ k ≤ 2 * x ^ 2 := by
    rw [show Finset.Icc 2 K = Finset.Ico 2 (K + 1) by
      ext m; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
    refine (geom_sum_Ico_le_of_lt_one hx0 hx1).trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg x]
  calc Real.log p * ∑ k ∈ Finset.Icc 2 K, x ^ k ≤ Real.log p * (2 * x ^ 2) :=
        mul_le_mul_of_nonneg_left hbound hlogp
    _ = 2 * Real.log p / (p : ℝ) ^ 2 := by rw [hx]; field_simp

/-- A sum of `(log p)/p` over a finset of primes contained in a singleton is at most `1`,
since each term satisfies `(log p)/p ≤ 1`. -/
private lemma sum_log_div_le_one {T : Finset ℕ} {m : ℕ} (hprime : ∀ p ∈ T, Nat.Prime p)
    (hT : T ⊆ {m}) : ∑ p ∈ T, Real.log p / p ≤ 1 := by
  have hcard : T.card ≤ 1 := by simpa using Finset.card_le_card hT
  calc ∑ p ∈ T, Real.log p / p ≤ ∑ _p ∈ T, (1 : ℝ) :=
        Finset.sum_le_sum fun p hp ↦ by
          have hppos : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
          rw [div_le_one hppos]
          linarith [Real.log_le_sub_one_of_pos hppos]
    _ = T.card := by simp
    _ ≤ 1 := by exact_mod_cast hcard

/-- Every member of `Finset.range (⌊x⌋₊ + 1)` is bounded by `x`, for `0 < x`. -/
private lemma cast_le_of_mem_range_floor {x : ℝ} (hx : 0 < x) {p : ℕ}
    (hp : p ∈ Finset.range (⌊x⌋₊ + 1)) : (p : ℝ) ≤ x := by
  rw [Finset.mem_range, Nat.lt_succ_iff] at hp
  calc (p : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hp
    _ ≤ x := Nat.floor_le hx.le

/-- Per-prime form of the `W`-tricked reduction error.  Let `p ≥ 2`, let `g` be a weight
which vanishes whenever `kill` holds and satisfies `|g − 1| ≤ c/p` otherwise, and let `a`
be a threshold below which `kill` always holds.  Then the weighted term `g·(log p)/p`
differs from the plain term `[a ≤ p]·(log p)/p` by at most `c·(2 log p/p²)` together with
the boundary term `[a ≤ p ∧ kill]·(log p)/p`. -/
private lemma abs_weight_mul_log_div_sub_indicator_le {p : ℕ} (hp : 2 ≤ p) {g c a : ℝ}
    (hc : 0 ≤ c) {kill : Prop} [Decidable kill] (hzero : kill → g = 0)
    (hnear : ¬ kill → |g - 1| ≤ c / (p : ℝ)) (hbelow : ¬ ((a : ℝ) ≤ (p : ℝ)) → kill) :
    |g * Real.log p / p - (if (a : ℝ) ≤ (p : ℝ) then Real.log p / p else 0)| ≤
      c * (2 * Real.log p / (p : ℝ) ^ 2) +
        (if ((a : ℝ) ≤ (p : ℝ) ∧ kill) then Real.log p / p else 0) := by
  have hpR2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hlogp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hcterm : 0 ≤ c * (2 * Real.log p / (p : ℝ) ^ 2) := mul_nonneg hc (by positivity)
  have hlogdiv_nn : (0 : ℝ) ≤ Real.log p / (p : ℝ) := by positivity
  by_cases hap : (a : ℝ) ≤ (p : ℝ)
  · rw [if_pos hap]
    by_cases hk : kill
    · rw [hzero hk, if_pos ⟨hap, hk⟩, zero_mul, zero_div, zero_sub, abs_neg,
        abs_of_nonneg hlogdiv_nn]
      linarith
    · rw [if_neg (fun h ↦ hk h.2), add_zero,
        show g * Real.log p / p - Real.log p / p = (g - 1) * (Real.log p / p) by ring,
        abs_mul, abs_of_nonneg hlogdiv_nn]
      have hval : (c / (p : ℝ)) * (Real.log p / p) ≤ c * (2 * Real.log p / (p : ℝ) ^ 2) := by
        rw [div_mul_div_comm, show (p : ℝ) * (p : ℝ) = (p : ℝ) ^ 2 by ring, mul_div_assoc,
          show c * (2 * Real.log p / (p : ℝ) ^ 2) = c * (2 * (Real.log p / (p : ℝ) ^ 2)) by ring]
        refine mul_le_mul_of_nonneg_left ?_ hc
        nlinarith [div_nonneg hlogp (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ 2)]
      linarith [mul_le_mul_of_nonneg_right (hnear hk) hlogdiv_nn]
  · rw [if_neg hap, sub_zero, hzero (hbelow hap), zero_mul, zero_div, abs_zero]
    have hbdy_nn : (0 : ℝ) ≤ (if ((a : ℝ) ≤ (p : ℝ) ∧ kill) then Real.log p / p else 0) := by
      split <;> positivity
    linarith

open scoped PrimeGaps.sieveModulus in
/-- **CRUX / reduction lemma (H1)+(H2).** For a W-tricked density family, the weighted
interval sum `∑_{w ≤ p ≤ z} γ N p (log p)/p` differs from the *plain* prime log-sum over
the same interval, restricted to the survivors `p > D₀ N`, by an `O(1)` error.

Concretely: set `a := max w (D₀ N)`. By (H1), every prime `p ≤ D₀ N` (equivalently
`p ∣ W N`) has `γ N p = 0`,
  so those terms vanish and the sum runs over primes in `(a, z]`
(i.e. `p > D₀ N` and `p ≥ w`, hence `p > a` up to the endpoint). On those survivors (H2)
gives `γ N p = 1 + O(1/p)`, so `γ N p (log p)/p = (log p)/p + η_p` with
`|η_p| ≤ c (log p)/p²`; summing and using `∑_p (log p)/p² < ∞`
(`Nat.Primes.summable_rpow` with exponent `< −1` bounds `∑ (log p)/p²`) bounds the total
error by a constant `c·S` with `S := ∑_p (log p)/p²`, uniform in `N, w, z`. -/
theorem wtricked_reduction (γ : ℝ → ℕ → ℝ) (hkill : ∀ N : ℕ, ∀ p, Nat.Prime p → p ∣ W N → γ N p = 0)
    (hunit : ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 0 < N → 2 ≤ PrimeGaps.D₀ N →
      ∀ p, Nat.Prime p → ¬ (p ∣ W N) → |γ N p - 1| ≤ c / (p : ℝ)) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ N : ℕ, 0 < N → 2 ≤ PrimeGaps.D₀ N → ∀ w z : ℝ, 2 ≤ w → w ≤ z →
      |intervalPrimeSum (γ N) w z -
          intervalPrimeSum (fun _ ↦ 1) (max w (PrimeGaps.D₀ N)) z| ≤ E := by
  obtain ⟨c, hc0, hcbound⟩ := hunit
  set B := ∑' p : Nat.Primes, 2 * Real.log (p : ℝ) / (p : ℝ) ^ 2 with hB
  have hBnn : 0 ≤ B := by rw [hB]; exact tsum_two_log_div_sq_nonneg
  refine ⟨c * B + 1, by positivity, ?_⟩
  intro N hN hD w z hw hwz
  have hWiff : ∀ p : ℕ, Nat.Prime p → (p ∣ W N ↔ (p : ℝ) ≤ PrimeGaps.D₀ N) := by
    intro p hp
    rw [Nat.Prime.dvd_primorial_iff hp, Nat.le_floor_iff' hp.ne_zero, PrimeGaps.D₀]
  set a := max w (PrimeGaps.D₀ N) with ha
  have hwa : w ≤ a := le_max_left _ _
  have hDa : PrimeGaps.D₀ N ≤ a := le_max_right _ _
  set F := {p ∈ Finset.range (⌊z⌋₊ + 1) | Nat.Prime p ∧ (w : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) ≤ z} with hF
  have hplain_eq : intervalPrimeSum (fun _ ↦ 1) a z =
      ∑ p ∈ F.filter (fun p : ℕ ↦ (a : ℝ) ≤ (p : ℝ)), Real.log p / p := by
    rw [intervalPrimeSum, hF, Finset.filter_filter]
    refine Finset.sum_congr (Finset.filter_congr fun p _ ↦ ?_) fun p _ ↦ by ring
    exact ⟨fun h ↦ ⟨⟨h.1, hwa.trans h.2.1, h.2.2⟩, h.2.1⟩, fun h ↦ ⟨h.1.1, h.2, h.1.2.2⟩⟩
  have hgsum_eq : intervalPrimeSum (γ N) w z = ∑ p ∈ F, γ N p * Real.log p / p := by
    rw [intervalPrimeSum, hF]
  have hplain_ind : ∑ p ∈ F.filter (fun p : ℕ ↦ (a : ℝ) ≤ (p : ℝ)), Real.log p / p =
      ∑ p ∈ F, (if (a : ℝ) ≤ (p : ℝ) then Real.log p / p else 0) := Finset.sum_filter _ _
  rw [hgsum_eq, hplain_eq, hplain_ind, ← Finset.sum_sub_distrib]
  set term : ℕ → ℝ := fun p ↦
    γ N p * Real.log p / p - (if (a : ℝ) ≤ (p : ℝ) then Real.log p / p else 0) with hterm
  set bdy : ℕ → ℝ := fun p ↦ if ((a : ℝ) ≤ (p : ℝ) ∧ p ∣ W N) then Real.log p / p else 0 with hbdy
  have hterm_bound : ∀ p ∈ F, |term p| ≤ c * (2 * Real.log p / (p : ℝ) ^ 2) + bdy p := by
    intro p hpF
    simp only [hF, Finset.mem_filter, Finset.mem_range] at hpF
    obtain ⟨_, hprime, hwp, -⟩ := hpF
    have hbelow : ¬ ((a : ℝ) ≤ (p : ℝ)) → p ∣ W N := fun hap ↦ by
      rw [ha, not_le, lt_max_iff] at hap
      exact (hWiff p hprime).mpr (hap.resolve_left (by linarith)).le
    simp only [hterm, hbdy]
    exact abs_weight_mul_log_div_sub_indicator_le hprime.two_le hc0.le
      (fun h ↦ hkill N p hprime h) (fun h ↦ hcbound N hN hD p hprime h) hbelow
  have hstep1 : |∑ p ∈ F, term p| ≤ ∑ p ∈ F, (c * (2 * Real.log p / (p : ℝ) ^ 2) + bdy p) :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm_bound)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hstep1
  have hFprime : ∀ p ∈ F, Nat.Prime p := by
    intro p hpF; simp only [hF, Finset.mem_filter] at hpF; exact hpF.2.1
  have hsum1_le : ∑ p ∈ F, 2 * Real.log p / (p : ℝ) ^ 2 ≤ B := by
    rw [hB]; exact sum_two_log_div_sq_le_tsum hFprime
  have hbdy_le : ∑ p ∈ F, bdy p ≤ 1 := by
    have hbdy_filter : ∑ p ∈ F, bdy p =
        ∑ p ∈ F.filter (fun p : ℕ ↦ (a : ℝ) ≤ (p : ℝ) ∧ p ∣ W N), Real.log p / p := by
      simp only [hbdy]
      exact (Finset.sum_filter _ _).symm
    rw [hbdy_filter]
    refine sum_log_div_le_one (m := ⌊PrimeGaps.D₀ N⌋₊)
      (fun p hp ↦ hFprime p (Finset.mem_filter.mp hp).1) fun p hp ↦ ?_
    simp only [hF, Finset.mem_filter] at hp
    obtain ⟨⟨_, hprime, _, _⟩, hap, hdvd⟩ := hp
    have heq : (p : ℝ) = PrimeGaps.D₀ N := le_antisymm ((hWiff p hprime).mp hdvd) (hDa.trans hap)
    have : ⌊PrimeGaps.D₀ N⌋₊ = p := by rw [← heq]; exact Nat.floor_natCast p
    simp [this]
  calc |∑ p ∈ F, term p| ≤ c * (∑ p ∈ F, 2 * Real.log p / (p : ℝ) ^ 2) + ∑ p ∈ F, bdy p := hstep1
    _ ≤ c * B + 1 := add_le_add (mul_le_mul_of_nonneg_left hsum1_le hc0.le) hbdy_le

/-- The plain prime log-sum over `[0, x]`: `∑_{p ≤ x, p prime} (log p)/p`. -/
noncomputable def primeLogSum (x : ℝ) : ℝ :=
  ∑ p ∈ {p ∈ Finset.range (⌊x⌋₊ + 1) | Nat.Prime p}, Real.log p / p

open ArithmeticFunction

/-- The `k`-th root cutoff never exceeds its argument: `⌊N ^ (1/k)⌋₊ ≤ N` for `1 ≤ k`. -/
private lemma floor_rpow_inv_le (N : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    ⌊(N : ℝ) ^ ((1 : ℝ) / k)⌋₊ ≤ N := by
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · rw [Nat.cast_zero, Real.zero_rpow (div_ne_zero one_ne_zero
      (Nat.cast_ne_zero.mpr (by omega)))]
    simp
  · refine Nat.floor_le_of_le ?_
    calc (N : ℝ) ^ ((1 : ℝ) / k) ≤ (N : ℝ) ^ (1 : ℝ) := by
          refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hNpos) ?_
          rw [div_le_one (by exact_mod_cast (by omega : 0 < k))]
          exact_mod_cast hk
      _ = (N : ℝ) := Real.rpow_one _

/-- **Prime-power tail bound (Step D).** `T_N = P_N + (proper prime powers)`, and the tail
is uniformly bounded: `0 ≤ T_N − P_N ≤ B` for a constant `B` independent of `N`. -/
theorem abs_T_sub_primeLogSum : ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
      |(∑ d ∈ Finset.Ioc 0 N, Λ d / d) - primeLogSum (N : ℝ)| ≤ B := by
  set B := ∑' p : Nat.Primes, 2 * Real.log (p : ℝ) / (p : ℝ) ^ 2 with hB
  have hBnn : 0 ≤ B := by rw [hB]; exact tsum_two_log_div_sq_nonneg
  refine ⟨B, hBnn, ?_⟩
  intro N
  set f : ℕ → ℝ := fun n ↦ Λ n / n with hf
  have hT_eq : (∑ d ∈ Finset.Ioc 0 N, Λ d / d) = ∑ n ∈ Finset.Ioc 0 N, f n := rfl
  have hrestrict : ∑ n ∈ Finset.Ioc 0 N, f n =
      ∑ n ∈ {n ∈ Finset.Ioc 0 N | IsPrimePow n}, f n := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    by_cases hpp : IsPrimePow n
    · simp [hpp]
    · simp [hf, hpp, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]
  have hreindex := Chebyshev.sum_PrimePow_eq_sum_sum f (x := (N : ℝ)) (by positivity)
  rw [Nat.floor_natCast N] at hreindex
  set K := ⌊Real.log (N : ℝ) / Real.log 2⌋₊ with hK
  have hTdouble : (∑ d ∈ Finset.Ioc 0 N, Λ d / d) = ∑ k ∈ Finset.Icc 1 K,
          ∑ p ∈ {p ∈ Finset.Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / k)⌋₊ | Nat.Prime p},
          f (p ^ k) := by
    rw [hT_eq, hrestrict, hreindex]
  have hfpk : ∀ k : ℕ, 1 ≤ k → ∀ p : ℕ, Nat.Prime p → f (p ^ k) = Real.log p / (p : ℝ) ^ k := by
    intro k hk p hp
    simp only [hf, ArithmeticFunction.vonMangoldt_apply_pow (by omega : k ≠ 0),
      ArithmeticFunction.vonMangoldt_apply_prime hp]
    push_cast
    rfl
  set g : ℕ → ℝ := fun k ↦
    ∑ p ∈ {p ∈ Finset.Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / k)⌋₊ | Nat.Prime p}, f (p ^ k)
    with hg
  have hTdouble' : (∑ d ∈ Finset.Ioc 0 N, Λ d / d) = ∑ k ∈ Finset.Icc 1 K, g k := hTdouble
  have hgnn : ∀ k, 1 ≤ k → 0 ≤ g k := by
    intro k hk
    rw [hg]
    refine Finset.sum_nonneg fun p hp ↦ ?_
    rw [hfpk k hk p (Finset.mem_filter.mp hp).2]
    positivity
  have hg1 : g 1 = primeLogSum (N : ℝ) := by
    rw [hg, primeLogSum, Nat.floor_natCast]
    simp only [Nat.cast_one, div_one, Real.rpow_one, Nat.floor_natCast]
    refine Finset.sum_congr (Finset.ext fun p ↦ ?_) fun p hp ↦ ?_
    · simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range, Nat.lt_succ_iff]
      exact ⟨fun h ↦ ⟨h.1.2, h.2⟩, fun h ↦ ⟨⟨h.2.pos, h.1⟩, h.2⟩⟩
    · rw [hfpk 1 le_rfl p (Finset.mem_filter.mp hp).2]
      simp
  by_cases hKpos : 1 ≤ K
  · have hdiff : (∑ d ∈ Finset.Ioc 0 N, Λ d / d) - primeLogSum (N : ℝ) =
        ∑ k ∈ Finset.Icc 2 K, g k := by
      rw [hTdouble', show Finset.Icc 1 K = insert 1 (Finset.Icc 2 K) by
        ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
        Finset.sum_insert (by simp), hg1]
      ring
    have htail_nn : 0 ≤ ∑ k ∈ Finset.Icc 2 K, g k :=
      Finset.sum_nonneg fun k hk ↦ hgnn k (le_trans (by norm_num) (Finset.mem_Icc.mp hk).1)
    set Sprimes := {p ∈ Finset.Ioc 0 N | Nat.Prime p} with hSprimes
    have hgle : ∀ k ∈ Finset.Icc 2 K, g k ≤ ∑ p ∈ Sprimes, Real.log p / (p : ℝ) ^ k := by
      intro k hk
      have hk1 : 1 ≤ k := le_trans (by norm_num) (Finset.mem_Icc.mp hk).1
      calc g k = ∑ p ∈ {p ∈ Finset.Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / k)⌋₊ | Nat.Prime p},
              Real.log p / (p : ℝ) ^ k :=
            Finset.sum_congr rfl fun p hp ↦ hfpk k hk1 p (Finset.mem_filter.mp hp).2
        _ ≤ ∑ p ∈ Sprimes, Real.log p / (p : ℝ) ^ k := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp ↦ ?_) fun p _ _ ↦ by positivity
            simp only [hSprimes, Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
            exact ⟨⟨hp.1.1, hp.1.2.trans (floor_rpow_inv_le N hk1)⟩, hp.2⟩
    rw [abs_of_nonneg (by rw [hdiff]; exact htail_nn), hdiff]
    calc ∑ k ∈ Finset.Icc 2 K, g k
        ≤ ∑ k ∈ Finset.Icc 2 K, ∑ p ∈ Sprimes, Real.log p / (p : ℝ) ^ k :=
          Finset.sum_le_sum hgle
      _ = ∑ p ∈ Sprimes, ∑ k ∈ Finset.Icc 2 K, Real.log p / (p : ℝ) ^ k := Finset.sum_comm
      _ ≤ ∑ p ∈ Sprimes, 2 * Real.log p / (p : ℝ) ^ 2 :=
          Finset.sum_le_sum fun p hp ↦ sum_Icc_two_log_div_pow_le K
            (by simp only [hSprimes, Finset.mem_filter] at hp; exact hp.2.two_le)
      _ ≤ B := by
          rw [hB]
          exact sum_two_log_div_sq_le_tsum fun p hp ↦ by
            simp only [hSprimes, Finset.mem_filter] at hp; exact hp.2
  · push Not at hKpos
    have hK0 : K = 0 := by omega
    have hTzero : (∑ d ∈ Finset.Ioc 0 N, Λ d / d) = 0 := by rw [hTdouble', hK0]; simp
    have hNlt2 : N < 2 := by
      by_contra! hge
      have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hratio : 1 ≤ Real.log (N : ℝ) / Real.log 2 := by
        rw [le_div_iff₀ hlog2pos]
        linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2)
          (by exact_mod_cast hge : (2 : ℝ) ≤ (N : ℝ))]
      have : 1 ≤ K := by rw [hK]; exact Nat.le_floor (by exact_mod_cast hratio)
      omega
    have hPzero : primeLogSum (N : ℝ) = 0 := by
      rw [← hg1, hg]
      simp only [Nat.cast_one, div_one, Real.rpow_one, Nat.floor_natCast]
      refine Finset.sum_eq_zero fun p hp ↦ ?_
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
      exact absurd (hp.2.two_le.trans hp.1.2) (by omega)
    rw [hTzero, hPzero, sub_zero, abs_zero]
    exact hBnn

/-- The interval prime log-sum equals the difference of pointwise sums: for `2 ≤ a ≤ z`,
`intervalPrimeSum (fun _ => 1) a z = primeLogSum z − ∑_{p < a}(log p)/p`.
Elementary Finset manipulation splitting the `[a, z]` filter as `(≤ z) minus (< a)`. -/
theorem intervalPrimeSum_eq_sub (a z : ℝ) (ha : 2 ≤ a) (haz : a ≤ z) :
    intervalPrimeSum (fun _ ↦ 1) a z = primeLogSum z -
      ∑ p ∈ {p ∈ Finset.range (⌊a⌋₊ + 1) | Nat.Prime p ∧ (p : ℝ) < a}, Real.log p / p := by
  have hzpos : (0 : ℝ) < z := by linarith
  have hIV : intervalPrimeSum (fun _ ↦ 1) a z =
      ∑ p ∈ {p ∈ Finset.range (⌊z⌋₊ + 1) | Nat.Prime p ∧ (a : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) ≤ z},
        Real.log p / p := by
    rw [intervalPrimeSum]; exact Finset.sum_congr rfl fun p _ ↦ by ring
  have hPLS : primeLogSum z =
      ∑ p ∈ {p ∈ Finset.range (⌊z⌋₊ + 1) | Nat.Prime p ∧ (p : ℝ) ≤ z}, Real.log p / p := by
    rw [primeLogSum]
    exact Finset.sum_congr (Finset.filter_congr fun p hp ↦
      ⟨fun h ↦ ⟨h, cast_le_of_mem_range_floor hzpos hp⟩, And.left⟩) fun _ _ ↦ rfl
  rw [hIV, hPLS]
  set S := {p ∈ Finset.range (⌊z⌋₊ + 1) | Nat.Prime p ∧ (p : ℝ) ≤ z} with hS
  have hsplit : (∑ p ∈ S, Real.log p / p) =
        (∑ p ∈ S.filter (fun p : ℕ ↦ (a : ℝ) ≤ (p : ℝ)), Real.log p / p) +
        (∑ p ∈ S.filter (fun p : ℕ ↦ ¬ ((a : ℝ) ≤ (p : ℝ))), Real.log p / p) :=
    (Finset.sum_filter_add_sum_filter_not S _ _).symm
  have hpart1 : (∑ p ∈ S.filter (fun p : ℕ ↦ (a : ℝ) ≤ (p : ℝ)), Real.log p / p) =
        ∑ p ∈ {p ∈ Finset.range (⌊z⌋₊ + 1) | Nat.Prime p ∧ (a : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) ≤ z},
          Real.log p / p := by
    refine Finset.sum_congr ?_ fun _ _ ↦ rfl
    rw [hS, Finset.filter_filter]
    exact Finset.filter_congr fun p _ ↦ by tauto
  have hpart2 : (∑ p ∈ S.filter (fun p : ℕ ↦ ¬ ((a : ℝ) ≤ (p : ℝ))), Real.log p / p) =
        ∑ p ∈ {p ∈ Finset.range (⌊a⌋₊ + 1) | Nat.Prime p ∧ (p : ℝ) < a}, Real.log p / p := by
    refine Finset.sum_congr (Finset.ext fun p ↦ ?_) fun _ _ ↦ rfl
    simp only [hS, Finset.mem_filter, Finset.mem_range, not_le]
    constructor
    · rintro ⟨⟨_, hprime, _⟩, hpa⟩
      exact ⟨by have := Nat.le_floor hpa.le; omega, hprime, hpa⟩
    · rintro ⟨_, hprime, hpa⟩
      have hpaz : (p : ℝ) < z := hpa.trans_le haz
      exact ⟨⟨by have := Nat.le_floor hpaz.le; omega, hprime, hpaz.le⟩, hpa⟩
  rw [hsplit, hpart1, hpart2]; ring

/-- `primeLogSum x = primeLogSum ⌊x⌋₊`: the prime log-sum only depends on the
natural floor of its nonnegative real endpoint. -/
theorem primeLogSum_eq_floor (x : ℝ) : primeLogSum x = primeLogSum (⌊x⌋₊ : ℝ) := by
  rw [primeLogSum, primeLogSum, Nat.floor_natCast]

/-- **Pointwise Mertens' second theorem.** `∑_{p ≤ x}(log p)/p = log x + O(1)`: there is a
constant `M₀ ≥ 0` with `|primeLogSum x − log x| ≤ M₀` for all `x ≥ 2`.

Assembled from the integer von-Mangoldt Mertens `abs_sum_vonMangoldt_div_sub_log`
(`|T_N − log N| ≤ log 4 + 5`), the prime-power tail bound `abs_T_sub_primeLogSum`
(`|T_N − P_N| ≤ B`), the identity `primeLogSum x = primeLogSum ⌊x⌋₊`, and the bound
`|log ⌊x⌋₊ − log x| ≤ log (3/2)` (since `⌊x⌋₊ ≤ x < ⌊x⌋₊ + 1 ≤ (3/2)⌊x⌋₊` for `x ≥ 2`).
Take `M₀ := B + (log 4 + 5) + log (3/2)`. -/
theorem mertens_pointwise :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ x : ℝ, 2 ≤ x → |primeLogSum x - Real.log x| ≤ M₀ := by
  obtain ⟨B, hB0, hB⟩ := abs_T_sub_primeLogSum
  refine ⟨B + (Real.log 4 + 5) + Real.log (3 / 2), ?_, ?_⟩
  · have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hlog32 : 0 ≤ Real.log (3 / 2) := Real.log_nonneg (by norm_num)
    linarith
  · intro x hx
    have hxpos : (0 : ℝ) < x := by linarith
    set N := ⌊x⌋₊ with hN
    have hN2 : 2 ≤ N := by rw [hN]; exact Nat.le_floor (by exact_mod_cast hx)
    have hNRpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hstep1 : |primeLogSum (N : ℝ) - Real.log N| ≤ B + (Real.log 4 + 5) := by
      have hBN := hB N
      rw [abs_sub_comm] at hBN
      calc |primeLogSum (N : ℝ) - Real.log N|
          ≤ |primeLogSum (N : ℝ) - (∑ d ∈ Finset.Ioc 0 N, Λ d / d)| +
              |(∑ d ∈ Finset.Ioc 0 N, Λ d / d) - Real.log N| := abs_sub_le _ _ _
        _ ≤ B + (Real.log 4 + 5) := by
              linarith [abs_sum_vonMangoldt_div_sub_log (by omega : 1 ≤ N)]
    have hstep2 : |Real.log N - Real.log x| ≤ Real.log (3 / 2) := by
      have hNlex : (N : ℝ) ≤ x := by rw [hN]; exact Nat.floor_le hxpos.le
      have hxle : x ≤ 3 / 2 * (N : ℝ) := by
        have hNR2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
        have hxltN1 : x < (N : ℝ) + 1 := by rw [hN]; exact Nat.lt_floor_add_one x
        linarith
      have hlogxle : Real.log x ≤ Real.log (3 / 2) + Real.log N := by
        rw [← Real.log_mul (by norm_num) hNRpos.ne']
        exact Real.log_le_log hxpos hxle
      rw [abs_le]
      constructor <;>
        linarith [Real.log_le_log hNRpos hNlex, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3 / 2)]
    rw [primeLogSum_eq_floor x, ← hN]
    calc |primeLogSum (N : ℝ) - Real.log x|
        ≤ |primeLogSum (N : ℝ) - Real.log N| + |Real.log N - Real.log x| := abs_sub_le _ _ _
      _ ≤ B + (Real.log 4 + 5) + Real.log (3 / 2) := by linarith

/-- The tail `∑_{p < a}(log p)/p` for primes below `a` is `log a + O(1)`. Concretely there
is `M₁` with `|(∑_{p < a}(log p)/p) − log a| ≤ M₁` for `a ≥ 2`. Follows from
`mertens_pointwise` by dropping the single boundary term `(log a)/a` if `a` is prime
(`(log p)/p ≤ 1` for all `p`). -/
theorem primeLogSumLt_bound : ∃ M₁ : ℝ, 0 ≤ M₁ ∧ ∀ a : ℝ, 2 ≤ a →
      |(∑ p ∈ {p ∈ Finset.range (⌊a⌋₊ + 1) | Nat.Prime p ∧ (p : ℝ) < a}, Real.log p / p) -
        Real.log a| ≤ M₁ := by
  obtain ⟨M₀, hM₀0, hM₀⟩ := mertens_pointwise
  refine ⟨M₀ + 1, by linarith, ?_⟩
  intro a ha
  have hapos : (0 : ℝ) < a := by linarith
  set F := {p ∈ Finset.range (⌊a⌋₊ + 1) | Nat.Prime p} with hF
  set ltSum := ∑ p ∈ {p ∈ Finset.range (⌊a⌋₊ + 1) | Nat.Prime p ∧ (p : ℝ) < a},
    Real.log p / p with hltSum
  set eqSum := ∑ p ∈ F.filter (fun p : ℕ ↦ ¬ ((p : ℝ) < a)), Real.log p / p with heqSum
  have hsplit : primeLogSum a = ltSum + eqSum := by
    rw [primeLogSum, hltSum, heqSum, ← hF]
    rw [← Finset.sum_filter_add_sum_filter_not F (fun p : ℕ ↦ (p : ℝ) < a)]
    congr 1
    rw [hF, Finset.filter_filter]
  have heqSum_nonneg : 0 ≤ eqSum := by
    rw [heqSum]
    exact Finset.sum_nonneg fun p _ ↦ by positivity
  have heqSum_le : eqSum ≤ 1 := by
    rw [heqSum]
    refine sum_log_div_le_one (m := ⌊a⌋₊) (fun p hp ↦ ?_) fun p hp ↦ ?_
    · simp only [hF, Finset.mem_filter] at hp
      exact hp.1.2
    · simp only [hF, Finset.mem_filter, Finset.mem_range, not_lt] at hp
      obtain ⟨⟨hpr, _⟩, hple⟩ := hp
      have heq : (p : ℝ) = a :=
        le_antisymm (cast_le_of_mem_range_floor hapos (Finset.mem_range.mpr hpr)) hple
      have : ⌊a⌋₊ = p := by rw [← heq]; exact Nat.floor_natCast p
      simp [this]
  have hltEq : ltSum = primeLogSum a - eqSum := by rw [hsplit]; ring
  have hM := abs_le.mp (hM₀ a ha)
  rw [hltEq, abs_le]
  constructor <;> linarith [hM.1, hM.2]

/-- The Mertens deviation of the constant weight `1` is uniformly bounded on intervals:
`|∑_{a ≤ p ≤ z} log p / p - log (z / a)| ≤ M` for all `2 ≤ a ≤ z`. -/
theorem mertens_interval : ∃ M : ℝ, 0 ≤ M ∧ ∀ a z : ℝ, 2 ≤ a → a ≤ z →
      |intervalPrimeSum (fun _ ↦ 1) a z - Real.log (z / a)| ≤ M := by
  obtain ⟨M₀, hM₀0, hM₀⟩ := mertens_pointwise
  obtain ⟨M₁, hM₁0, hM₁⟩ := primeLogSumLt_bound
  refine ⟨M₀ + M₁, by positivity, ?_⟩
  intro a z ha haz
  have hz : 2 ≤ z := le_trans ha haz
  have hzpos : (0 : ℝ) < z := by linarith
  have hapos : (0 : ℝ) < a := by linarith
  have hsplit := intervalPrimeSum_eq_sub a z ha haz
  have hlogza : Real.log (z / a) = Real.log z - Real.log a :=
    Real.log_div (ne_of_gt hzpos) (ne_of_gt hapos)
  have h1 := abs_le.mp (hM₀ z hz)
  have h2 := abs_le.mp (hM₁ a ha)
  rw [hsplit, hlogza, abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **Elementary log bound.** For `2 ≤ w` and `2 ≤ D₀ N`,
`0 ≤ log (max w (D₀ N) / w) ≤ log (D₀ N)`.

Lower bound: `max w (D₀N) ≥ w > 0` so the ratio is `≥ 1` and its log is `≥ 0`.
Upper bound: `max w (D₀N) ≤ w · D₀N` when `w ≥ 1` (since both `w ≤ w·D₀N` as `D₀N ≥ 1`,
and `D₀N ≤ w·D₀N` as `w ≥ 1`), so `max/w ≤ D₀N` and `log(max/w) ≤ log D₀N`. -/
theorem log_max_div_le (w N : ℝ) (hw : 2 ≤ w) (hN : 2 ≤ PrimeGaps.D₀ N) :
    0 ≤ Real.log (max w (PrimeGaps.D₀ N) / w) ∧
      Real.log (max w (PrimeGaps.D₀ N) / w) ≤ Real.log (PrimeGaps.D₀ N) := by
  have hwpos : 0 < w := by linarith
  have haw : w ≤ max w (PrimeGaps.D₀ N) := le_max_left _ _
  refine ⟨Real.log_nonneg ((one_le_div hwpos).mpr haw),
    Real.log_le_log (div_pos (hwpos.trans_le haw) hwpos) ?_⟩
  rw [div_le_iff₀ hwpos]
  exact max_le (by nlinarith) (by nlinarith)

open scoped PrimeGaps.sieveModulus in
/-- For a density family `γ` killed at the primes dividing `W N` and satisfying
`|γ_N(p) - 1| ≤ c / p` elsewhere, the Mertens deviation obeys
`-(log (D₀ N) + C₀) ≤ Δ (γ N) w z ≤ C₀` for all `2 ≤ w ≤ z`. -/
theorem core_estimate (γ : ℝ → ℕ → ℝ) (hkill : ∀ N : ℕ, ∀ p, Nat.Prime p → p ∣ W N → γ N p = 0)
    (hunit : ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 0 < N → 2 ≤ PrimeGaps.D₀ N →
      ∀ p, Nat.Prime p → ¬ (p ∣ W N) → |γ N p - 1| ≤ c / (p : ℝ)) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ N : ℕ, 0 < N → 2 ≤ PrimeGaps.D₀ N → ∀ w z : ℝ, 2 ≤ w → w ≤ z →
      -(Real.log (PrimeGaps.D₀ N) + C₀) ≤ Δ (γ N) w z ∧ Δ (γ N) w z ≤ C₀ := by
  obtain ⟨E, hE0, hE⟩ := wtricked_reduction γ hkill hunit
  obtain ⟨M, hM0, hM⟩ := mertens_interval
  refine ⟨E + M + 1, by positivity, ?_⟩
  intro N hN hD w z hw hwz
  set a := max w (PrimeGaps.D₀ N) with ha
  have hwpos : (0 : ℝ) < w := by linarith
  have hzpos : (0 : ℝ) < z := by linarith
  have haw : w ≤ a := le_max_left _ _
  have hapos : (0 : ℝ) < a := hwpos.trans_le haw
  set G := intervalPrimeSum (γ N) w z with hG
  set P := intervalPrimeSum (fun _ ↦ 1) a z with hP
  have hEbound : |G - P| ≤ E := hE N hN hD w z hw hwz
  have hEabs := abs_le.mp hEbound
  obtain ⟨hlaw0, hlawD⟩ := log_max_div_le w N hw hD
  have hlogzw : Real.log (z / w) = Real.log z - Real.log w :=
    Real.log_div hzpos.ne' hwpos.ne'
  have hΔ : Δ (γ N) w z = G - Real.log (z / w) := rfl
  rw [Real.log_div hapos.ne' hwpos.ne'] at hlaw0 hlawD
  rw [hΔ, hlogzw]
  by_cases hcase : a ≤ z
  · have hMabs := abs_le.mp (hM a z (hw.trans haw) hcase)
    rw [Real.log_div hzpos.ne' hapos.ne'] at hMabs
    constructor <;> linarith [hEabs.1, hEabs.2, hMabs.1, hMabs.2]
  · push Not at hcase
    have hPzero : P = 0 := by
      rw [hP, intervalPrimeSum]
      refine Finset.sum_eq_zero fun p hp ↦ ?_
      simp only [Finset.mem_filter] at hp
      obtain ⟨_, _, hap, hpz⟩ := hp
      exact absurd (hap.trans hpz) (by linarith)
    have hzD : z ≤ PrimeGaps.D₀ N := by
      rw [ha, lt_max_iff] at hcase
      exact (hcase.resolve_left (by linarith)).le
    have hlogzD : Real.log z ≤ Real.log (PrimeGaps.D₀ N) := Real.log_le_log hzpos hzD
    have hlogw0 : 0 ≤ Real.log w := Real.log_nonneg (by linarith)
    have hlogwz : Real.log w ≤ Real.log z := Real.log_le_log hwpos hwz
    rw [hPzero, sub_zero] at hEabs
    constructor <;> linarith [hEabs.1, hEabs.2]

open scoped PrimeGaps.sieveModulus in
/-- **Definition 7 (the W-tricked sieve density family `gamma_g`).**
`gamma : ℝ → ℕ → ℝ` is the family of W-tricked densities attached to the fixed admissible
tuple `H`: for each level `N`, `gamma N` is an instance of the abstract density `gamma`
(Definition 6), and in addition satisfies the two characterizing properties:

* **(H1) Killing of small primes.** For every level `N` and every prime `p` dividing
  `W N` (equivalently `p <= D_0 N`), `gamma N p = 0`.
* **(H2) Unit density on surviving primes.** There is a single constant `c > 0`, depending
  only on `H` (through `k`) and *uniform in `N`*, such that for every sufficiently large
  level `N` (`0 < N` and `2 ≤ D_0 N`) and every prime `p` not dividing `W N`
  (equivalently `p > D_0 N`), `|gamma N p - 1| <= c / p`.

The uniform constant `c` is packaged existentially, quantified over `N` inside, so it is
independent of `N`. -/
structure IsWTrickedFamily (H : Finset ℕ) (γ : ℝ → ℕ → ℝ) : Prop where
  /-- For each level `N`, `γ N` is an abstract multiplicative density (Definition 6). -/
  density : ∀ N : ℕ, IsGammaDensity (γ N)
  /-- (H1) Small primes (`p ∣ W N`, i.e. `p ≤ D_0 N`) are killed
  at every level `N`. -/
  kill : ∀ N : ℕ, ∀ p, Nat.Prime p → p ∣ W N → γ N p = 0
  /-- (H2) unit density `gamma_g(p) = 1 + O(1/p)` on surviving primes, with a single
  constant `c = c(k, H)` uniform in `N`. -/
  unit : ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 0 < N → 2 ≤ PrimeGaps.D₀ N →
    ∀ p, Nat.Prime p → ¬ (p ∣ W N) → |γ N p - 1| ≤ c / (p : ℝ)

open scoped PrimeGaps.sieveModulus in
/-- **Statement 1 (two-sided sieve estimate).**
Fix an admissible tuple `H` with `k = |H| >= 2` and the W-tricked density family `gamma_g`.
There is a constant `C > 0` — the `O(1)`, depending only on `H` and the family, quantified
before `N`, `w`, `z` — such that for every large level `N` (`0 < N`, `2 ≤ D_0 N`) and every
real pair `2 <= w <= z`,
`|sum_{w <= p <= z} gamma_g(p)(log p)/p - log(z/w)| <= log (D_0 N) + C`. -/
@[pg_tag "bg246" "slem_gg_log_sum"]
theorem two_sided_estimate (H : Finset ℕ) (γ : ℝ → ℕ → ℝ) (hγ : IsWTrickedFamily H γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → 2 ≤ PrimeGaps.D₀ N → ∀ w z : ℝ, 2 ≤ w → w ≤ z →
        |Δ (γ N) w z| ≤ Real.log (PrimeGaps.D₀ N) + C := by
  obtain ⟨C₀, hC0, hcore⟩ := core_estimate γ hγ.kill hγ.unit
  refine ⟨C₀, hC0, ?_⟩
  intro N hN hD w z hw hwz
  obtain ⟨hlo, hhi⟩ := hcore N hN hD w z hw hwz
  have hlogD : 0 ≤ Real.log (PrimeGaps.D₀ N) := Real.log_nonneg (le_trans (by norm_num) hD)
  rw [abs_le]
  constructor <;> linarith

open scoped PrimeGaps.sieveModulus in
/-- **Statement 2 (sharp one-sided upper bound, `A_2 = O(1)`).**
There is a constant `A₂ > 0`, depending only on `H` (and the family), not on `N`, `w`, `z`
— it is quantified before `N` — such that for every large level `N` and every real pair
`2 <= w <= z`, `sum_{w <= p <= z} gamma_g(p)(log p)/p - log(z/w) <= A₂`. -/
theorem upper_bound_A₂ (H : Finset ℕ) (γ : ℝ → ℕ → ℝ) (hγ : IsWTrickedFamily H γ) :
    ∃ A₂ : ℝ, 0 < A₂ ∧ ∀ N : ℕ, 0 < N → 2 ≤ PrimeGaps.D₀ N → ∀ w z : ℝ, 2 ≤ w → w ≤ z →
        Δ (γ N) w z ≤ A₂ := by
  obtain ⟨C₀, hC0, hcore⟩ := core_estimate γ hγ.kill hγ.unit
  exact ⟨C₀, hC0, fun N hN hD w z hw hwz ↦ (hcore N hN hD w z hw hwz).2⟩

open scoped PrimeGaps.sieveModulus in
/-- **Statement 3 (one-sided lower bound, `L << log D_0`).**
There is a constant `C > 0`, depending only on `H` (and the family) and quantified before
`N` (so `C` is independent of `N`, `w`, `z`), such that for every large level `N` there is
a lower-deviation parameter `L` with `0 <= L <= C * log (D_0 N)` (i.e. `L << log D_0`) and,
for every real pair `2 <= w <= z`,
`sum_{w <= p <= z} gamma_g(p)(log p)/p - log(z/w) >= -L`. -/
theorem lower_bound_L (H : Finset ℕ) (γ : ℝ → ℕ → ℝ) (hγ : IsWTrickedFamily H γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → 2 ≤ PrimeGaps.D₀ N →
      ∃ L : ℝ, 0 ≤ L ∧ L ≤ C * Real.log (PrimeGaps.D₀ N) ∧
        ∀ w z : ℝ, 2 ≤ w → w ≤ z → -L ≤ Δ (γ N) w z := by
  obtain ⟨C₀, hC0, hcore⟩ := core_estimate γ hγ.kill hγ.unit
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 + C₀ / Real.log 2, by positivity, ?_⟩
  intro N hN hD
  have hlogD2 : Real.log 2 ≤ Real.log (PrimeGaps.D₀ N) := Real.log_le_log (by norm_num) hD
  refine ⟨Real.log (PrimeGaps.D₀ N) + C₀, by linarith, ?_,
    fun w z hw hwz ↦ (hcore N hN hD w z hw hwz).1⟩
  have key : C₀ ≤ C₀ / Real.log 2 * Real.log (PrimeGaps.D₀ N) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    nlinarith
  calc Real.log (PrimeGaps.D₀ N) + C₀
      ≤ Real.log (PrimeGaps.D₀ N) + C₀ / Real.log 2 * Real.log (PrimeGaps.D₀ N) := by linarith
    _ = (1 + C₀ / Real.log 2) * Real.log (PrimeGaps.D₀ N) := by ring

end PrimeGaps
