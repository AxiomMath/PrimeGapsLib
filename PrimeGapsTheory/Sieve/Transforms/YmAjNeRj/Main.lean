/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.Transforms.YmAjNeRj.Harmonic

import PrimeGapsTheory.Tactic.PaperTag

/-!
# The off-diagonal bound

Assembles the kernel and harmonic bounds into `offDiagonal_bound`.

## Main results

* `offDiagonal_bound`
-/

@[expose] public section

open Real

open scoped ArithmeticFunction.Moebius

open scoped ArithmeticFunction.detotient

namespace PrimeGaps

open scoped ArithmeticFunction BigOperators

namespace MaynardOffDiagonal

open ArithmeticFunction (moebius)

noncomputable section


/-- Every prime `p ≤ ⌊D₀ N⌋₊` divides `primorial ⌊D₀ N⌋₊`. -/
theorem prime_dvd_primorial_D0 (N : ℝ) (p : ℕ) (hp : Nat.Prime p) (hple : p ≤ ⌊D₀ N⌋₊) :
    p ∣ primorial ⌊D₀ N⌋₊ := hp.dvd_primorial_iff.mpr hple

/-- `sumB W R ≤ ∑' s, μ(s)² / φ(s)²`, uniformly in `W` and `R`. -/
theorem sumB_le_tsum (W : ℕ) (R : ℝ) :
    sumB W R ≤ ∑' s, ((μ s : ℝ)) ^ 2 / (s.totient : ℝ) ^ 2 := by
  have heq : ∀ n ∈ Sset W R, (1 / (Nat.totient n : ℝ) ^ 2) =
      ((μ n : ℝ)) ^ 2 / (n.totient : ℝ) ^ 2 := by
    intro n hn
    simp only [Sset, Finset.mem_filter] at hn
    have hcast : ((μ n : ℝ)) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hn.2.1
    rw [hcast, one_div]
  rw [sumB, Finset.sum_congr rfl heq]
  exact Summable.sum_le_tsum _ (fun i _ ↦ by positivity) lem_convergent_sum_phi

/-- Given the tail estimate `∑_{n ∈ S} 1/n² ≤ A / D` for finite sets `S` of integers exceeding
`D ≥ 2`, `sumT W R ≤ (8 * A / D₀ N) * sumB W R` at `W = primorial ⌊D₀ N⌋₊`; the gain comes from
the least prime factor of each `n ≠ 1` in the support exceeding `D₀ N`. -/
theorem sumT_le_main (N : ℝ) (R : ℝ) (hD2 : 2 ≤ D₀ N) (A : ℝ) (hApos : 0 < A)
    (htail : ∀ (D0n : ℕ), 2 ≤ D0n → ∀ (S : Finset ℕ), (∀ p ∈ S, D0n < p) →
        ∑ p ∈ S, 1 / (p : ℝ) ^ 2 ≤ A / D0n) :
    sumT (primorial ⌊D₀ N⌋₊) R ≤ (8 * A / D₀ N) * sumB (primorial ⌊D₀ N⌋₊) R := by
  set W := primorial ⌊D₀ N⌋₊
  set Tset := {n ∈ (Sset W R) | n ≠ 1} with hTset
  set M := Sset W R with hM
  set Q := {q ∈ (Finset.Icc 1 ⌊R⌋₊) | Nat.Prime q ∧ ⌊D₀ N⌋₊ < q} with hQ
  set Φ : ℕ → ℕ × ℕ := fun n ↦ (n.minFac, n / n.minFac) with hΦ
  set F : ℕ × ℕ → ℝ := fun p ↦ (1 / ((p.1 : ℝ) - 1) ^ 2) * (1 / (Nat.totient p.2 : ℝ) ^ 2) with hF
  have hfact : ∀ n ∈ Tset, Nat.Prime n.minFac ∧ n.minFac ∣ n ∧
      Nat.Coprime n.minFac (n / n.minFac) ∧ Φ n ∈ Q ×ˢ M ∧
      n.minFac * (n / n.minFac) = n := by
    intro n hn
    rw [hTset, Finset.mem_filter, hM, Sset, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨⟨h1, hR⟩, hsq, hgcd⟩, hn1⟩ := hn
    have hp : Nat.Prime n.minFac := Nat.minFac_prime hn1
    have hdvd : n.minFac ∣ n := Nat.minFac_dvd n
    have hn0 : 0 < n := by omega
    have hmul : n.minFac * (n / n.minFac) = n := Nat.mul_div_cancel' hdvd
    have hcop : Nat.Coprime n.minFac (n / n.minFac) :=
      (Nat.Prime.coprime_iff_not_dvd hp).2 fun hc ↦ hp.one_lt.ne'
        (Nat.isUnit_iff.1 (hsq _ ((Nat.mul_dvd_mul_left n.minFac hc).trans hmul.dvd)))
    refine ⟨hp, hdvd, hcop, ?_, hmul⟩
    rw [Finset.mem_product]
    constructor
    · rw [hQ, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨hp.pos, le_trans (Nat.le_of_dvd hn0 hdvd) hR⟩, hp, ?_⟩
      by_contra hle
      push Not at hle
      exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one
        (hgcd ▸ Nat.dvd_gcd hdvd (prime_dvd_primorial_D0 N n.minFac hp hle)))
    · rw [hM, Sset, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨Nat.div_pos (Nat.minFac_le hn0) hp.pos,
          le_trans (Nat.le_of_dvd hn0 (Nat.div_dvd_of_dvd hdvd)) hR⟩,
        hsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hdvd),
        Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hdvd) hgcd⟩
  have hstepA : sumT W R = ∑ n ∈ Tset, F (Φ n) := by
    rw [sumT, ← hTset]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    obtain ⟨hp, -, hcop, -, hmul⟩ := hfact n hn
    have htot : (Nat.totient n : ℝ) = ((n.minFac : ℝ) - 1) * (Nat.totient (n / n.minFac) : ℝ) := by
      conv_lhs => rw [← hmul, Nat.totient_mul hcop, Nat.totient_prime hp]
      push_cast [Nat.cast_sub hp.one_lt.le]
      ring
    have hmf0 : 0 < (n.minFac : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (n.minFac : ℝ) := by exact_mod_cast hp.two_le
      linarith
    simp only [hF, hΦ, htot]
    field_simp
  have hInj : Set.InjOn Φ Tset := fun a ha b hb hab ↦ by
    rw [hΦ] at hab
    simp only [Prod.mk.injEq] at hab
    rw [← (hfact a ha).2.2.2.2, ← (hfact b hb).2.2.2.2, hab.2, hab.1]
  have hsub : Finset.image Φ Tset ⊆ Q ×ˢ M := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨n, hn, rfl⟩ := hp
    exact (hfact n hn).2.2.2.1
  have hFnn : ∀ p, 0 ≤ F p := by intro p; rw [hF]; positivity
  have hBnn : 0 ≤ sumB W R := Finset.sum_nonneg fun m _ ↦ by positivity
  have hQprime : ∀ q ∈ Q, Nat.Prime q ∧ ⌊D₀ N⌋₊ < q := by
    intro q hq; rw [hQ, Finset.mem_filter] at hq; exact hq.2
  have htailQ : ∑ q ∈ Q, (1 : ℝ) / ((q : ℝ) - 1) ^ 2 ≤ 8 * A / D₀ N := by
    set Dn := ⌊D₀ N⌋₊ with hDn
    have hDn2 : 2 ≤ Dn := by rw [hDn]; exact Nat.le_floor (by exact_mod_cast hD2)
    have hDn2R : (2 : ℝ) ≤ (Dn : ℝ) := by exact_mod_cast hDn2
    have hD0pos : (0 : ℝ) < D₀ N := by linarith
    have hDnR : D₀ N ≤ 2 * (Dn : ℝ) := by
      have hfl : D₀ N - 1 < (Dn : ℝ) := by rw [hDn]; exact Nat.sub_one_lt_floor (D₀ N)
      linarith
    have hstep1 : ∑ q ∈ Q, (1 : ℝ) / ((q : ℝ) - 1) ^ 2 ≤ 4 * ∑ q ∈ Q, 1 / (q : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun q hq ↦ ?_
      have hq2R : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (hQprime q hq).1.two_le
      have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hq2R, hq1]
    have htA := htail Dn hDn2 Q (fun p hp ↦ (hQprime p hp).2)
    have key : (4 : ℝ) * (A / (Dn : ℝ)) ≤ 8 * A / D₀ N := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by linarith) hD0pos]
      linarith [mul_nonneg hApos.le (by linarith : (0 : ℝ) ≤ 2 * (Dn : ℝ) - D₀ N)]
    linarith
  calc sumT W R = ∑ n ∈ Tset, F (Φ n) := hstepA
    _ = ∑ p ∈ Finset.image Φ Tset, F p := (Finset.sum_image hInj).symm
    _ ≤ ∑ p ∈ Q ×ˢ M, F p := Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ ↦ hFnn i
    _ = (∑ q ∈ Q, 1 / ((q : ℝ) - 1) ^ 2) * sumB W R := by
        rw [sumB, ← hM, Finset.sum_product, Finset.sum_mul_sum]
    _ ≤ (8 * A / D₀ N) * sumB W R := mul_le_mul_of_nonneg_right htailQ hBnn

/-- A single absolute constant `C_B` with `sumB W R ≤ C_B` for all `W, R`, and
`sumT (primorial ⌊D₀ N⌋₊) R ≤ 2 * C_B / D₀ N` whenever `2 ≤ D₀ N`. -/
theorem sumB_sumT_le : ∃ C_B : ℝ, 0 < C_B ∧ (∀ (W : ℕ) (R : ℝ), sumB W R ≤ C_B) ∧
      (∀ (N : ℝ) (R : ℝ), 2 ≤ D₀ N → sumT (primorial ⌊D₀ N⌋₊) R ≤ 2 * C_B / D₀ N) := by
  set C_B' := ∑' s, ((μ s : ℝ)) ^ 2 / (s.totient : ℝ) ^ 2 with hC_B'
  have hC_B'pos : 0 < C_B' := by
    rw [hC_B']
    exact lt_of_lt_of_le (by simp)
      (Summable.le_tsum lem_convergent_sum_phi 1 fun i _ ↦ by positivity)
  obtain ⟨A, hApos, htail⟩ := PrimeGaps.tail_sum_one_over_sq
  refine ⟨max C_B' (4 * A * C_B'), lt_of_lt_of_le hC_B'pos (le_max_left _ _),
    fun W R ↦ le_trans (sumB_le_tsum W R) (le_max_left _ _), ?_⟩
  intro N R hD2
  have hD0pos : (0 : ℝ) < D₀ N := by linarith
  have h1 : sumT (primorial ⌊D₀ N⌋₊) R ≤ (8 * A / D₀ N) * C_B' :=
    le_trans (sumT_le_main N R hD2 A hApos htail)
      (mul_le_mul_of_nonneg_left (sumB_le_tsum _ R) (by positivity))
  refine le_trans h1 ?_
  rw [show (8 * A / D₀ N) * C_B' = 2 * (4 * A * C_B') / D₀ N by ring]
  gcongr
  exact le_max_right _ _

/-- For `2 ≤ k` and all large `N`, `offDiagKernel W R m r ≤ C₀ · φ(W) · log R / (W · D₀ N)` at
`W = primorial ⌊D₀ N⌋₊` and `R = N ^ (θ / 2 - δ)`, with `C₀ = C₀(k)`. -/
theorem offDiagKernel_le_of_two_le {k : ℕ} (hk : 2 ≤ k) : ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ θ δ : ℝ, θ ∈ Set.Ioo (0 : ℝ) 1 → δ ∈ Set.Ioo (0 : ℝ) (θ / 2) →
      ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ m : Fin k, ∀ r : Fin k → ℕ, (∀ i, 0 < r i) → r m = 1 →
        offDiagKernel (primorial ⌊D₀ N⌋₊) (N ^ (θ / 2 - δ)) m r ≤
          C₀ * (Nat.totient (primorial ⌊D₀ N⌋₊) : ℝ) * Real.log (N ^ (θ / 2 - δ)) /
              ((primorial ⌊D₀ N⌋₊ : ℝ) * D₀ N) := by
  obtain ⟨c₁, hc₁pos, hA⟩ := sumA_le
  obtain ⟨C_B, hCBpos, hB, hT⟩ := sumB_sumT_le
  have hk1 : (0 : ℝ) < (k - 1 : ℝ) := by
    have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  refine ⟨(k - 1 : ℝ) * c₁ * 2 * C_B ^ (k - 1), by positivity, ?_⟩
  intro θ δ hθ hδ
  obtain ⟨N₀A, hN₀A3, hAreg⟩ := hA θ δ hθ hδ
  refine ⟨max (max 3 (rexp (rexp (rexp 2)))) N₀A,
          le_trans (le_max_left _ _) (le_max_left _ _), ?_⟩
  intro N hN m r hr hrm
  have hNbig : rexp (rexp (rexp 2)) ≤ N :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hDpos : 0 < D₀ N := lt_of_lt_of_le (by norm_num) (two_le_D0_of_large hNbig)
  have hN1 : (1 : ℝ) ≤ N := le_trans (Real.one_le_exp (by positivity)) hNbig
  have hlogR : 0 ≤ Real.log (N ^ (θ / 2 - δ)) :=
    Real.log_nonneg (Real.one_le_rpow hN1 (by linarith [hδ.2]))
  set W : ℕ := primorial ⌊D₀ N⌋₊
  set R : ℝ := N ^ (θ / 2 - δ)
  have hAnn : 0 ≤ sumA W R := Finset.sum_nonneg fun n _ ↦ by positivity
  have hBnn : 0 ≤ sumB W R := Finset.sum_nonneg fun n _ ↦ by positivity
  have hTnn : 0 ≤ sumT W R := Finset.sum_nonneg fun n _ ↦ by positivity
  have hAbd : sumA W R ≤ c₁ * (Nat.totient W : ℝ) / (W : ℝ) * Real.log R :=
    hAreg N (le_trans (le_max_right _ _) hN)
  have hTbd : sumT W R ≤ 2 * C_B / D₀ N := hT N R (two_le_D0_of_large hNbig)
  have hred : offDiagKernel W R m r ≤ (k - 1 : ℝ) * sumA W R * sumT W R * sumB W R ^ (k - 2) :=
    offDiagKernel_le_reduction hk W R m r hr hrm
  have hAub_nn : 0 ≤ c₁ * (Nat.totient W : ℝ) / (W : ℝ) * Real.log R := le_trans hAnn hAbd
  have hTub_nn : 0 ≤ 2 * C_B / D₀ N := le_trans hTnn hTbd
  have hCBnn : 0 ≤ C_B := le_of_lt hCBpos
  have hBbd : sumB W R ≤ C_B := hB W R
  have hchain : (k - 1 : ℝ) * sumA W R * sumT W R * sumB W R ^ (k - 2) ≤
      (k - 1 : ℝ) * (c₁ * (Nat.totient W : ℝ) / (W : ℝ) * Real.log R) *
          (2 * C_B / D₀ N) * C_B ^ (k - 2) := by gcongr
  have hfinal : (k - 1 : ℝ) * (c₁ * (Nat.totient W : ℝ) / (W : ℝ) * Real.log R) *
          (2 * C_B / D₀ N) * C_B ^ (k - 2) =
      ((k - 1 : ℝ) * c₁ * 2 * C_B ^ (k - 1)) * (Nat.totient W : ℝ) *
          Real.log R / ((W : ℝ) * D₀ N) := by
    have hWpos : (W : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (primorial_pos _).ne'
    have hDne : D₀ N ≠ 0 := ne_of_gt hDpos
    rw [show k - 1 = (k - 2) + 1 by omega, pow_succ]
    field_simp
  exact hred.trans (hchain.trans_eq hfinal)

/-- `offDiagKernel_le_of_two_le` with the hypothesis `2 ≤ k` removed, the case `k ≤ 1` being
vacuous. -/
theorem offDiagKernel_le {k : ℕ} : ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ θ δ : ℝ, θ ∈ Set.Ioo (0 : ℝ) 1 → δ ∈ Set.Ioo (0 : ℝ) (θ / 2) →
      ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ m : Fin k, ∀ r : Fin k → ℕ, (∀ i, 0 < r i) → r m = 1 →
        offDiagKernel (primorial ⌊D₀ N⌋₊) (N ^ (θ / 2 - δ)) m r ≤
          C₀ * (Nat.totient (primorial ⌊D₀ N⌋₊) : ℝ) * Real.log (N ^ (θ / 2 - δ)) /
              ((primorial ⌊D₀ N⌋₊ : ℝ) * D₀ N) := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · have hk1 : k ≤ 1 := by omega
    refine ⟨1, one_pos, ?_⟩
    intro θ δ hθ hδ
    refine ⟨max 3 (rexp (rexp (rexp 2))), le_max_left _ _, ?_⟩
    intro N hN m r _ _
    have hNbig : rexp (rexp (rexp 2)) ≤ N := le_trans (le_max_right _ _) hN
    have hN1 : (1 : ℝ) ≤ N := le_trans (Real.one_le_exp (by positivity)) hNbig
    rw [offDiagKernel_eq_zero_of_le_one hk1]
    exact kernel_rhs_nonneg zero_le_one (lt_of_lt_of_le (by norm_num) (two_le_D0_of_large hNbig))
      (Real.log_nonneg (Real.one_le_rpow hN1 (by linarith [hδ.2])))
  · exact offDiagKernel_le_of_two_le hk

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- The off-diagonal terms `a_j ≠ r_j` of `y^{(m)}_r` contribute at most
`C · ‖y‖ · φ(W) · log R / (W · D₀ N)`, for all large `N` and every `y` with permissible
support. -/
@[pg_tag "bg246" "lem_ym_aj_ne_rj"]
theorem offDiagonal_bound
    {k : ℕ} :
    ∃ C : ℝ, 0 < C ∧ ∀ θ δ : ℝ, θ ∈ Set.Ioo (0 : ℝ) 1 → δ ∈ Set.Ioo (0 : ℝ) (θ / 2) →
      ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ y : (Fin k → ℕ) →₀ ℝ, y.HasPermissibleSupport ⌊R⌋₊ (W N) →
      ∀ m : Fin k, ∀ r : Fin k → ℕ, (∀ i, 0 < r i) → r m = 1 →
        |∑ᶠ (a : Fin k → ℕ) (_ : OffDiag m r a), Tsummand y m r a| ≤
          C * y.maxRealAbs * (Nat.totient (W N) : ℝ) * Real.log R / ((W N : ℝ) *
                D₀ N) := by
  obtain ⟨C₀, hC₀pos, hker⟩ := offDiagKernel_le (k := k)
  refine ⟨C₀, hC₀pos, ?_⟩
  intro θ δ hθ hδ
  obtain ⟨N₀, hN₀, hbound⟩ := hker θ δ hθ hδ
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN y hy m r hr hrm
  refine (offDiag_abs_le_maxRealAbs_kernel (W N) R y hy m r).trans ?_
  refine (mul_le_mul_of_nonneg_left (hbound N hN m r hr hrm)
    Finsupp.maxRealAbs_nonneg).trans_eq ?_
  ring

end

end MaynardOffDiagonal

end PrimeGaps
