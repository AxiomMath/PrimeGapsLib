/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.S2m.Error.TauFourSums

import PrimeGapsTheory.Tactic.PaperTag

/-!
# The S2m error bound

Assembles the modulus sums into the total error contribution bound.

## Main results

* `MaynardS2Error.weighted_modulus_sum_bound`: the modulus sum weighted by `windowError`.
* `MaynardS2Error.exists_totalErrorContribution_le`: the total error contribution is
  `O(y_max ^ 2 * N / log N ^ A)`.
-/

@[expose] public section

open Real

namespace MaynardS2Error

open ArithmeticFunction zeta

/-- `∑_{1 ≤ q ≤ N ^ θ} τ (3 * k) q ^ 4 / φ q ≤ Ct4 * Real.log N ^ B4` for all large `N`. -/
lemma tau4_over_totient_sum_bound {k : ℕ} (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃ (Ct4 B4 N₀ : ℝ), 0 < Ct4 ∧ ∀ (N : ℝ), N₀ ≤ N →
      (∑ q ∈ {q ∈ (Finset.range (⌊N ^ θ⌋₊ + 1)) | 1 ≤ q},
        (τ (3 * k) q : ℝ) ^ 4 / (Nat.totient q : ℝ)) ≤ Ct4 * (Real.log N) ^ B4 := by
  have hIcc : ∀ n : ℕ, {q ∈ (Finset.range (n + 1)) | 1 ≤ q} = Finset.Icc 1 n := fun n ↦ by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]; omega
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    refine ⟨1, 0, 0, one_pos, fun N _ ↦ ?_⟩
    have hval : ∀ q : ℕ, (τ (3 * 0) q : ℝ) ^ 4 / (Nat.totient q : ℝ) = if q = 1 then 1 else 0 :=
      fun q ↦ by by_cases hq1 : q = 1 <;> simp [hq1]
    simp only [hIcc, hval, Finset.sum_ite_eq', Real.rpow_zero, one_mul]
    split <;> norm_num
  · obtain ⟨C, B, hCpos, hbound⟩ := tau4_totient_full_sum_le (3 * k) (by omega)
    refine ⟨C * θ ^ B, B, max 2 (rexp (Real.log 2 / θ)), by positivity, fun N hN ↦ ?_⟩
    have hN2 : (2 : ℝ) ≤ N := (le_max_left _ _).trans hN
    have hb := hbound (N ^ θ) (PrimeGaps.two_le_rpow_of_exp_log_two_div_le hθ0
      ((le_max_right _ _).trans hN))
    rw [Real.log_rpow (by linarith), Real.mul_rpow hθ0.le (Real.log_nonneg (by linarith))] at hb
    rw [hIcc]
    exact hb.trans_eq (by ring)

/-- Under a level of distribution `θ`,
`∑_{1 ≤ q ≤ N ^ θ} τ (3 * k) q ^ 2 * windowError N q ≤ C₄ * N / Real.log N ^ A'` for large `N`. -/
lemma weighted_modulus_sum_bound {k : ℕ} (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hLoD : Nat.HasLevelOfDistribution Set.univ θ 1) (A' : ℝ) (hA' : 1 ≤ A') :
    ∃ (C₄ N₄ : ℝ), 0 < C₄ ∧ ∀ (N : ℝ), N₄ ≤ N →
      (∑ q ∈ {q ∈ (Finset.range (⌊N ^ θ⌋₊ + 1)) | 1 ≤ q},
        (τ (3 * k) q : ℝ) ^ 2 * windowError N q) ≤ C₄ * N / (Real.log N) ^ A' := by
  classical
  obtain ⟨Ct, N01, hCt, h1part⟩ := tau_sq_sum_bound (k := k) θ hθ0 hθ1 A'
  obtain ⟨Cp, hCp, hpoint⟩ := windowDisc_pointwise_bound
  obtain ⟨Ct4, B4raw, N04, hCt4, htau4raw⟩ := tau4_over_totient_sum_bound (k := k) θ hθ0 hθ1
  set B4 := max B4raw 0
  have hB4nn : (0 : ℝ) ≤ B4 := le_max_right _ _
  obtain ⟨Cd, N03, hCd, hEsum⟩ :=
    windowDisc_sum_le_hLoD θ hθ0 hLoD (2 * A' + B4) (by linarith [hB4nn])
  refine ⟨Ct + √(Cp * Ct4 * Cd), max (max (max N01 N04) N03) (rexp 1),
    by positivity, ?_⟩
  intro N hN
  have hN01 : N01 ≤ N :=
    (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hN
  have hN04 : N04 ≤ N :=
    (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hN
  have hN03 : N03 ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hNe : rexp 1 ≤ N := (le_max_right _ _).trans hN
  have hN1 : (1 : ℝ) ≤ N := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hNe
  have hN0 : (0 : ℝ) < N := one_pos.trans_le hN1
  have hL1 : (1 : ℝ) ≤ Real.log N := (Real.le_log_iff_exp_le hN0).2 hNe
  have hLpos : (0 : ℝ) < Real.log N := one_pos.trans_le hL1
  set L := Real.log N with hLdef
  set S := {q ∈ (Finset.range (⌊N ^ θ⌋₊ + 1)) | 1 ≤ q} with hSdef
  have hqle : ∀ q ∈ S, (q : ℝ) ≤ N := by
    intro q hq
    rw [hSdef, Finset.mem_filter, Finset.mem_range] at hq
    have h1 : (q : ℝ) ≤ (⌊N ^ θ⌋₊ : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp hq.1
    have h2 : (⌊N ^ θ⌋₊ : ℝ) ≤ N ^ θ := Nat.floor_le (Real.rpow_nonneg hN0.le θ)
    have h3 : N ^ θ ≤ N := by simpa using Real.rpow_le_rpow_of_exponent_le hN1 hθ1.le
    linarith
  have hq1 : ∀ q ∈ S, 1 ≤ q := fun q hq ↦ (Finset.mem_filter.mp hq).2
  have hEnn : ∀ q, 0 ≤ windowDisc N q := windowDisc_nonneg N
  have hsplit : (∑ q ∈ S, (τ (3 * k) q : ℝ) ^ 2 * windowError N q) =
      (∑ q ∈ S, (τ (3 * k) q : ℝ) ^ 2) +
        (∑ q ∈ S, (τ (3 * k) q : ℝ) ^ 2 * windowDisc N q) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ ↦ by simp only [windowDisc]; ring
  rw [hsplit]
  have hp1 : (∑ q ∈ S, (τ (3 * k) q : ℝ) ^ 2) ≤ Ct * N / L ^ A' := h1part N hN01
  set sq : ℕ → ℝ := fun q ↦ √(windowDisc N q)
  have hsq2 : ∀ q, sq q ^ 2 = windowDisc N q := fun q ↦ Real.sq_sqrt (hEnn q)
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq S (fun q ↦ (τ (3 * k) q : ℝ) ^ 2 * sq q) (fun q ↦ sq q)
  have hCSlhs : (∑ q ∈ S, (τ (3 * k) q : ℝ) ^ 2 * sq q * sq q) =
      ∑ q ∈ S, (τ (3 * k) q : ℝ) ^ 2 * windowDisc N q :=
    Finset.sum_congr rfl fun q _ ↦ by rw [mul_assoc, ← pow_two, hsq2 q]
  have hCSf2 : (∑ q ∈ S, ((τ (3 * k) q : ℝ) ^ 2 * sq q) ^ 2) =
      ∑ q ∈ S, (τ (3 * k) q : ℝ) ^ 4 * windowDisc N q :=
    Finset.sum_congr rfl fun q _ ↦ by rw [mul_pow, hsq2 q]; ring
  have hCSg2 : (∑ q ∈ S, sq q ^ 2) = ∑ q ∈ S, windowDisc N q :=
    Finset.sum_congr rfl fun q _ ↦ hsq2 q
  rw [hCSlhs, hCSf2, hCSg2] at hCS
  have htau4part : (∑ q ∈ S, (τ (3 * k) q : ℝ) ^ 4 * windowDisc N q) ≤ Cp * N * (Ct4 * L ^ B4) := by
    have hstep : (∑ q ∈ S, (τ (3 * k) q : ℝ) ^ 4 * windowDisc N q) ≤
        Cp * N * (∑ q ∈ S, (τ (3 * k) q : ℝ) ^ 4 / (Nat.totient q : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun q hq ↦ ?_
      rw [show Cp * N * ((τ (3 * k) q : ℝ) ^ 4 / (Nat.totient q : ℝ)) =
        (τ (3 * k) q : ℝ) ^ 4 * (Cp * N / (Nat.totient q : ℝ)) from by ring]
      exact mul_le_mul_of_nonneg_left (hpoint N hN1 q (hq1 q hq) (hqle q hq)) (by positivity)
    refine hstep.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact (htau4raw N hN04).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _)) hCt4.le)
  have hEpart : (∑ q ∈ S, windowDisc N q) ≤ Cd * N / L ^ (2 * A' + B4) := hEsum N hN03
  set D := ∑ q ∈ S, (τ (3 * k) q : ℝ) ^ 2 * windowDisc N q
  have hRHS : D ^ 2 ≤ (Cp * Ct4 * Cd) * N ^ 2 / L ^ (2 * A') := by
    refine (hCS.trans (mul_le_mul htau4part hEpart
      (Finset.sum_nonneg fun q _ ↦ hEnn q) (by positivity))).trans_eq ?_
    rw [Real.rpow_add hLpos]
    field_simp
  have hDbound : D ≤ √(Cp * Ct4 * Cd) * N / L ^ A' := by
    have hL2 : (L ^ A') ^ 2 = L ^ (2 * A') := by
      rw [← Real.rpow_natCast (L ^ A') 2, ← Real.rpow_mul hLpos.le]
      congr 1; push_cast; ring
    have hsqle : D ^ 2 ≤ (√(Cp * Ct4 * Cd) * N / L ^ A') ^ 2 := by
      rwa [div_pow, mul_pow, Real.sq_sqrt (by positivity), hL2]
    exact (abs_le_of_sq_le_sq' hsqle (by positivity)).2
  calc (∑ q ∈ S, (τ (3 * k) q : ℝ) ^ 2) + D
      ≤ Ct * N / L ^ A' + √(Cp * Ct4 * Cd) * N / L ^ A' := add_le_add hp1 hDbound
    _ = (Ct + √(Cp * Ct4 * Cd)) * N / L ^ A' := by ring

/-- Fix an admissible set `H ⊂ ℤ` with `|H| = k ≥ 2`, a fixed exponent `A > 0`, and fixed real
parameters `θ, δ` with `0 < δ < θ/2` and `θ < 1/2`. Under the Bombieri-Vinogradov
level-of-distribution hypothesis for `θ`, the total contribution of the `O(E(N,q))` error terms
in the CRT expansion of `S_2^{(m)}` is `O(y_max² N / (log N)^A)` as `N → ∞`, with an implied
constant `C` (and threshold `N₀` ) depending on all the fixed data `A, k, H, θ, δ` but not on
`N`. -/
@[pg_tag "bg246" "lem_S2m_error"]
theorem exists_totalErrorContribution_le (k : ℕ) (hk : 2 ≤ k) (A : ℝ) (hA : 0 < A)
    (θ δ : ℝ) (hδ0 : 0 < δ) (hδθ : δ < θ / 2) (hθ : θ < 1 / 2)
    (hLoD : Nat.HasLevelOfDistribution Set.univ θ 1) :
    ∃ (C N₀ : ℝ), 0 < C ∧ ∀ (N : ℝ), N₀ ≤ N →
        ∀ (w : SieveWeights k N θ δ), totalErrorContribution w ≤
            C * (Finsupp.maxRealAbs (PrimeGaps.lToY w.lam)) ^ 2 * N / (Real.log N) ^ A := by
  have hθ0 : 0 < θ := by linarith
  have hθ1 : θ < 1 := by linarith
  obtain ⟨C₁, N₁, hC₁, hlam⟩ := lambdaMax_bound k hk θ δ hδ0 hδθ hθ1
  obtain ⟨C₃, N₃, hC₃, hcollapse⟩ :=
    collapse_to_modulus_sum (k := k) (by omega) θ δ hδ0 C₁ N₁ hlam
  obtain ⟨C₄, N₄, hC₄, hLoDsum⟩ := weighted_modulus_sum_bound (k := k) θ hθ0 hθ1 hLoD (A + 2 * k)
      (by linarith [show (2 : ℝ) ≤ (k : ℝ) from mod_cast hk])
  refine ⟨C₃ * C₁ ^ 2 * C₄, max (max (max N₁ N₃) N₄) (rexp 1), by positivity, ?_⟩
  intro N hN w
  have hN₃ : N₃ ≤ N :=
    (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hN
  have hN₄ : N₄ ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hNe : rexp 1 ≤ N := (le_max_right _ _).trans hN
  have hLpos : (0 : ℝ) < Real.log N :=
    one_pos.trans_le ((Real.le_log_iff_exp_le ((Real.exp_pos 1).trans_le hNe)).2 hNe)
  set L := Real.log N with hLdef
  set y := Finsupp.maxRealAbs (PrimeGaps.lToY w.lam) with hydef
  set Sq := (∑ q ∈ {q ∈ (Finset.range (⌊N ^ θ⌋₊ + 1)) | 1 ≤ q},
      (τ (3 * k) q : ℝ) ^ 2 * windowError N q) with hSqdef
  have h1 := hcollapse N hN₃ w
  have h2 := hLoDsum N hN₄
  rw [← hLdef, ← hydef, ← hSqdef] at h1
  rw [← hLdef, ← hSqdef] at h2
  have hchain : totalErrorContribution w ≤
      C₃ * (C₁ * y * L ^ k) ^ 2 * (C₄ * N / L ^ (A + 2 * (k : ℝ))) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  have hpow2 : ((L ^ k) ^ 2 : ℝ) = L ^ (2 * (k : ℝ)) := by
    rw [← pow_mul, ← Real.rpow_natCast L (k * 2)]
    congr 1; push_cast; ring
  have hRHS : C₃ * (C₁ * y * L ^ k) ^ 2 * (C₄ * N / L ^ (A + 2 * (k : ℝ))) =
      C₃ * C₁ ^ 2 * C₄ * y ^ 2 * N / L ^ A := by
    rw [show (C₁ * y * L ^ k) ^ 2 = C₁ ^ 2 * y ^ 2 * (L ^ k) ^ 2 from by ring, hpow2,
      Real.rpow_add hLpos A (2 * (k : ℝ))]
    field_simp
  rwa [hRHS] at hchain

end MaynardS2Error
