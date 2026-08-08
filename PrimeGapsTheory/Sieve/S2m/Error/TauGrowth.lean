/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.S2m.Error.Basic

/-!
# Growth of the divisor function

Polynomial-versus-geometric comparisons giving the epsilon-power bound for the
k-fold divisor function.

## Main results

* `MaynardS2Error.tau_le_rpow`: `τ r m ≤ C * m ^ ε` for every `ε > 0`.
* `MaynardS2Error.tau_sq_summable`: summability of `τ r (m + 1) ^ 2 / (m + 1) ^ κ` for `κ > 1`.
* `MaynardS2Error.tau_sq_sum_bound`: the truncated sum of `τ (3 * k) q ^ 2` is `O(N / log N ^ A')`.
-/

@[expose] public section

open scoped Finset

namespace MaynardS2Error

open ArithmeticFunction zeta

/-- The window discrepancy `E*(q) = windowError N q - 1`, i.e. the `sSup` part of the window error
(without the leading `+1` ). -/
noncomputable def windowDisc (N : ℝ) (q : ℕ) : ℝ := windowError N q - 1

/-- `0 ≤ windowDisc N q`. -/
lemma windowDisc_nonneg (N : ℝ) (q : ℕ) : 0 ≤ windowDisc N q :=
  sub_nonneg.mpr (Nat.one_le_primeCountingIocError ⌊N⌋₊ ⌊2 * N⌋₊ q)

/-- For `s > 1` there is `M > 0` with `n ^ r ≤ M * s ^ n` for all `n`. -/
lemma poly_le_geom (r : ℕ) (s : ℝ) (hs : 1 < s) :
    ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ, (n : ℝ) ^ r ≤ M * s ^ n := by
  obtain ⟨M, hM⟩ :=
    (isLittleO_pow_const_const_pow_of_one_lt r hs).tendsto_div_nhds_zero.bddAbove_range
  refine ⟨max M 1, one_pos.trans_le (le_max_right _ _), fun n ↦ ?_⟩
  rw [← div_le_iff₀ (pow_pos (one_pos.trans hs) n)]
  exact (hM (Set.mem_range_self n)).trans (le_max_left _ _)

/-- For `ε > 0` there is `M ≥ 1` with `(a + 1) ^ r ≤ M * 2 ^ (a * ε)` for all `a`. -/
lemma poly_le_geom_eps (r : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ a : ℕ, ((a : ℝ) + 1) ^ r ≤ M * (2 : ℝ) ^ ((a : ℝ) * ε) := by
  have hs : (1 : ℝ) < (2 : ℝ) ^ ε :=
    (Real.one_lt_rpow_iff_of_pos (by norm_num)).mpr (Or.inl ⟨by norm_num, hε⟩)
  obtain ⟨M, -, hM⟩ := poly_le_geom r ((2 : ℝ) ^ ε) hs
  refine ⟨max (M * (2 : ℝ) ^ ε) 1, le_max_right _ _, fun a ↦ ?_⟩
  have h1 := hM (a + 1)
  push_cast at h1
  rw [pow_succ, ← Real.rpow_natCast ((2 : ℝ) ^ ε) a, ← Real.rpow_mul (by norm_num), mul_comm ε,
    mul_comm ((2 : ℝ) ^ ((a : ℝ) * ε)), ← mul_assoc] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

/-- For `ε > 0` there is a threshold `T` beyond which `2 ^ r ≤ p ^ ε`. -/
lemma zeta_threshold (r : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℕ, ∀ p : ℕ, T ≤ p → (2 : ℝ) ^ r ≤ (p : ℝ) ^ ε := by
  obtain ⟨B, hB⟩ := Filter.tendsto_atTop_atTop.mp (tendsto_rpow_atTop hε) ((2 : ℝ) ^ r)
  exact ⟨⌈B⌉₊, fun p hp ↦ hB p ((Nat.le_ceil B).trans (by exact_mod_cast hp))⟩

/-- Anything bounded by both `(a + 1) ^ r` and `(2 ^ r) ^ a` satisfies
`v ≤ (if p < T then M else 1) * (p ^ a) ^ ε`: the small primes use the polynomial bound, the large
ones the geometric bound. -/
lemma per_prime_bound (r : ℕ) (ε : ℝ) (hε : 0 < ε)
    (M : ℝ) (hM1 : 1 ≤ M) (hMbd : ∀ a : ℕ, ((a : ℝ) + 1) ^ r ≤ M * (2 : ℝ) ^ ((a : ℝ) * ε))
    (T : ℕ) (hT : ∀ p : ℕ, T ≤ p → (2 : ℝ) ^ r ≤ (p : ℝ) ^ ε)
    (p a : ℕ) (hp : p.Prime)
    (v : ℝ)
    (hv1 : v ≤ ((a : ℝ) + 1) ^ r) (hv2 : v ≤ ((2 : ℝ) ^ r) ^ a) :
    v ≤ (if p < T then M else 1) * ((p : ℝ) ^ a) ^ ε := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  by_cases hlt : p < T
  · rw [if_pos hlt]
    refine (hv1.trans (hMbd a)).trans ?_
    rw [Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (pow_le_pow_left₀ (by norm_num) hp2 a) hε.le)
      (zero_le_one.trans hM1)
  · have hpid : ((p : ℝ) ^ ε) ^ a = ((p : ℝ) ^ a) ^ ε := by
      rw [← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ (p : ℝ)), mul_comm,
        Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ (p : ℝ))]
    rw [if_neg hlt, one_mul, ← hpid]
    exact hv2.trans (pow_le_pow_left₀ (by positivity) (hT p (not_lt.mp hlt)) a)

/-- For every `ε > 0` there is `C > 0` with `τ r m ≤ C * m ^ ε` for all `m ≥ 1`. -/
lemma tau_le_rpow (r : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → (τ r m : ℝ) ≤ C * (m : ℝ) ^ ε := by
  obtain ⟨M, hM1, hMbd⟩ := poly_le_geom_eps r ε hε
  obtain ⟨T, hT⟩ := zeta_threshold r ε hε
  set N := #((Finset.range T).filter Nat.Prime) with hNdef
  refine ⟨M ^ N, by positivity, fun m hm ↦ ?_⟩
  have hm0 : m ≠ 0 := by omega
  set S := m.factorization.support with hSdef
  have hp : ∀ p ∈ S, p.Prime := fun p hpS ↦
    Nat.prime_of_mem_primeFactors (by rwa [hSdef, Nat.support_factorization] at hpS)
  have hprodm : (∏ p ∈ S, ((p : ℝ) ^ m.factorization p) ^ ε) = (m : ℝ) ^ ε := by
    rw [Real.finsetProd_rpow S _ (fun i _ ↦ by positivity) ε]
    congr 1
    exact_mod_cast Nat.prod_factorization_pow_eq_self hm0
  have hconst : (∏ p ∈ S, (if p < T then M else 1)) ≤ M ^ N := by
    simp only [Finset.prod_ite, Finset.prod_const, one_pow, mul_one]
    refine pow_le_pow_right₀ hM1 ((Finset.card_le_card fun p hq ↦ ?_).trans hNdef.ge)
    rw [Finset.mem_filter] at hq ⊢
    exact ⟨Finset.mem_range.mpr hq.2, hp p hq.1⟩
  rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization τ r
    (ArithmeticFunction.isMultiplicative_zeta.pow (k := r)) hm0, Nat.cast_finsuppProd]
  calc (∏ p ∈ S, (τ r (p ^ m.factorization p) : ℝ))
      ≤ ∏ p ∈ S, (if p < T then M else 1) * ((p : ℝ) ^ m.factorization p) ^ ε :=
        Finset.prod_le_prod (fun i _ ↦ by positivity) fun p hpS ↦
          per_prime_bound r ε hε M hM1 hMbd T hT p (m.factorization p) (hp p hpS) _
            (by exact_mod_cast zeta_pow_ppow_le r p (m.factorization p) (hp p hpS))
            (by exact_mod_cast zeta_pow_ppow_le' r p (m.factorization p) (hp p hpS))
    _ = (∏ p ∈ S, (if p < T then M else 1)) * ∏ p ∈ S, ((p : ℝ) ^ m.factorization p) ^ ε :=
        Finset.prod_mul_distrib
    _ ≤ M ^ N * (m : ℝ) ^ ε := by
        rw [hprodm]; exact mul_le_mul_of_nonneg_right hconst (by positivity)

/-- Summability of `m ↦ τ r (m+1) ^ 2 / (m+1) ^ κ` for `κ > 1`. -/
lemma tau_sq_summable (r : ℕ) (κ : ℝ) (hκ : 1 < κ) :
    Summable (fun m : ℕ ↦ (τ r (m + 1) : ℝ) ^ 2 / ((m : ℝ) + 1) ^ κ) := by
  set ε : ℝ := (κ - 1) / 4 with hεdef
  obtain ⟨C, -, hC⟩ := tau_le_rpow r ε (by rw [hεdef]; linarith)
  set p : ℝ := κ - 2 * ε with hpdef
  have hshift : Summable (fun m : ℕ ↦ 1 / (((m : ℝ) + 1)) ^ p) := by
    simpa using (summable_nat_add_iff (f := fun n : ℕ ↦ 1 / (n : ℝ) ^ p) 1).mpr
      (Real.summable_one_div_nat_rpow.mpr (by rw [hpdef, hεdef]; linarith))
  refine Summable.of_nonneg_of_le (fun m ↦ by positivity) (fun m ↦ ?_) (hshift.mul_left (C ^ 2))
  have hbpos : (0 : ℝ) < ((m : ℝ) + 1) := by positivity
  have hb := hC (m + 1) (by omega)
  push_cast at hb
  have hsq : (τ r (m + 1) : ℝ) ^ 2 ≤ C ^ 2 * ((m : ℝ) + 1) ^ (2 * ε) := by
    rw [two_mul, Real.rpow_add hbpos, show C ^ 2 * (((m : ℝ) + 1) ^ ε * ((m : ℝ) + 1) ^ ε) =
      (C * ((m : ℝ) + 1) ^ ε) ^ 2 from by ring]
    exact pow_le_pow_left₀ (by positivity) hb 2
  calc (τ r (m + 1) : ℝ) ^ 2 / ((m : ℝ) + 1) ^ κ
      ≤ (C ^ 2 * ((m : ℝ) + 1) ^ (2 * ε)) / ((m : ℝ) + 1) ^ κ := by gcongr
    _ = C ^ 2 * (1 / (((m : ℝ) + 1)) ^ p) := by
        rw [hpdef, Real.rpow_sub hbpos]
        field_simp

/-- `∑_{1 ≤ q ≤ N ^ θ} τ (3 * k) q ^ 2 ≤ Ct * N / Real.log N ^ A'` for all large `N`. -/
lemma tau_sq_sum_bound {k : ℕ} (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (A' : ℝ) :
    ∃ (Ct N₀ : ℝ), 0 < Ct ∧ ∀ (N : ℝ), N₀ ≤ N →
      (∑ q ∈ {q ∈ (Finset.range (⌊N ^ θ⌋₊ + 1)) | 1 ≤ q},
        (τ (3 * k) q : ℝ) ^ 2) ≤ Ct * N / (Real.log N) ^ A' := by
  set r : ℕ := 3 * k
  set κ : ℝ := (1 + 1 / θ) / 2 with hκdef
  have hκ1 : 1 < κ := by rw [hκdef]; linarith [(one_lt_div hθ0).mpr hθ1]
  have hθκ : θ * κ < 1 := by
    rw [hκdef, ← mul_div_assoc, mul_add, mul_one, mul_one_div, div_self hθ0.ne']
    linarith
  set f : ℕ → ℝ := fun m ↦ (τ r (m + 1) : ℝ) ^ 2 / ((m : ℝ) + 1) ^ κ with hf
  have hfsummable : Summable f := tau_sq_summable r κ hκ1
  set S : ℝ := ∑' m, f m with hSdef
  have hSnonneg : 0 ≤ S := by rw [hSdef]; exact tsum_nonneg fun m ↦ by rw [hf]; positivity
  set s : ℝ := 1 - θ * κ with hsdef
  have hs0 : 0 < s := by rw [hsdef]; linarith
  have hlobound : ∀ᶠ N : ℝ in Filter.atTop, Real.log N ^ A' ≤ N ^ s := by
    filter_upwards [(isLittleO_log_rpow_rpow_atTop A' hs0).def (by norm_num : (0 : ℝ) < 1),
      Filter.eventually_gt_atTop (1 : ℝ)] with N hN hN1
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, one_mul,
      abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hN1.le) A'),
      abs_of_nonneg (Real.rpow_nonneg (one_pos.trans hN1).le s)] at hN
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hlobound
  refine ⟨S + 1, max N₁ 2, by positivity, fun N hN ↦ ?_⟩
  have hN2 : (2 : ℝ) ≤ N := (le_max_right N₁ 2).trans hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hNs : (0 : ℝ) < N ^ s := Real.rpow_pos_of_pos hN0 s
  have hlogA' : (0 : ℝ) < (Real.log N) ^ A' :=
    Real.rpow_pos_of_pos (Real.log_pos (by linarith)) A'
  have hZpos : (0 : ℝ) < N ^ θ := Real.rpow_pos_of_pos hN0 θ
  set Q := {q ∈ (Finset.range (⌊N ^ θ⌋₊ + 1)) | 1 ≤ q} with hQdef
  have hreindex : (∑ q ∈ Q, ((τ r q : ℝ) ^ 2 / (q : ℝ) ^ κ)) =
      ∑ m ∈ Finset.range ⌊N ^ θ⌋₊, f m := by
    rw [hQdef, show {q ∈ (Finset.range (⌊N ^ θ⌋₊ + 1)) | 1 ≤ q} =
        Finset.Ico 1 (⌊N ^ θ⌋₊ + 1) from by
          ext q; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega,
      Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, hf]
    exact Finset.sum_congr rfl fun m _ ↦ by rw [add_comm 1 m]; push_cast; ring
  have hstep1 : (∑ q ∈ Q, (τ r q : ℝ) ^ 2) ≤ (N ^ θ) ^ κ * S := by
    have hterm : ∀ q ∈ Q, (τ r q : ℝ) ^ 2 ≤ (N ^ θ) ^ κ * ((τ r q : ℝ) ^ 2 / (q : ℝ) ^ κ) := by
      intro q hq
      rw [hQdef, Finset.mem_filter, Finset.mem_range] at hq
      have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.2
      calc (τ r q : ℝ) ^ 2 = ((τ r q : ℝ) ^ 2 / (q : ℝ) ^ κ) * (q : ℝ) ^ κ :=
            (div_mul_cancel₀ _ (Real.rpow_pos_of_pos hqpos κ).ne').symm
        _ ≤ ((τ r q : ℝ) ^ 2 / (q : ℝ) ^ κ) * (N ^ θ) ^ κ :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hqpos.le
              ((Nat.cast_le.mpr (Nat.lt_succ_iff.mp hq.1)).trans (Nat.floor_le hZpos.le))
              (one_pos.trans hκ1).le) (by positivity)
        _ = (N ^ θ) ^ κ * ((τ r q : ℝ) ^ 2 / (q : ℝ) ^ κ) := mul_comm _ _
    calc (∑ q ∈ Q, (τ r q : ℝ) ^ 2)
        ≤ ∑ q ∈ Q, (N ^ θ) ^ κ * ((τ r q : ℝ) ^ 2 / (q : ℝ) ^ κ) := Finset.sum_le_sum hterm
      _ = (N ^ θ) ^ κ * ∑ q ∈ Q, ((τ r q : ℝ) ^ 2 / (q : ℝ) ^ κ) := by rw [Finset.mul_sum]
      _ ≤ (N ^ θ) ^ κ * S := by
          rw [hreindex]
          exact mul_le_mul_of_nonneg_left
            (hfsummable.sum_le_tsum _ fun i _ ↦ by rw [hf]; positivity)
            (Real.rpow_nonneg hZpos.le κ)
  have hZκN : (N ^ θ) ^ κ = N / N ^ s := by
    rw [← Real.rpow_mul hN0.le, eq_div_iff hNs.ne', ← Real.rpow_add hN0,
      show θ * κ + s = 1 from by rw [hsdef]; ring, Real.rpow_one]
  calc (∑ q ∈ Q, (τ r q : ℝ) ^ 2) ≤ (N ^ θ) ^ κ * S := hstep1
    _ = S * N / N ^ s := by rw [hZκN]; ring
    _ ≤ (S + 1) * N / (Real.log N) ^ A' := by
        rw [div_le_div_iff₀ hNs hlogA']
        nlinarith [hN₁ N ((le_max_left _ _).trans hN), hNs, hlogA', hSnonneg, hN0,
          mul_nonneg hSnonneg hN0.le]

end MaynardS2Error
