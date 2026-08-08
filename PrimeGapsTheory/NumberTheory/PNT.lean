/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeNumberTheoremAnd.MediumPNT


/-!
# Prime Number Theorem

The bulk of the prime number theorem is Alex Kontorovich's library `PrimeNumberTheoremAnd`; here we
convert its statement about `Chebyshev.psi` into the estimate
`π(N) = N / log N + O(N / (log N) ^ 2)`.
-/

@[expose] public section

open Nat Real Filter Asymptotics
open scoped Chebyshev

namespace PNT

/-- `π(N) = N/log N + O(N/(log N)^2) as N → ∞`. -/
theorem primeCounting :
    ∃ (C : ℝ) (N₀ : ℕ), ∀ N ≥ N₀, |primeCounting N - N / Real.log N| ≤ C * N / Real.log N ^ 2 := by
  obtain ⟨c, hc, hmedium⟩ := MediumPNT
  have ht : Tendsto (fun x : ℝ ↦ log x ^ ((1 : ℝ) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp tendsto_log_atTop
  have hdecay' : (fun x : ℝ ↦ rexp (-c * log x ^ ((1 : ℝ) / 10))) =O[atTop]
      (fun x ↦ 1 / log x) := by
    apply ((isLittleO_exp_neg_mul_rpow_atTop hc (-10)).isBigO.comp_tendsto ht).congr'
    · aesop
    · filter_upwards [eventually_gt_atTop 1] with x hx
      dsimp
      rw [Real.rpow_neg (Real.rpow_pos_of_pos (log_pos hx) _).le,
        ← Real.rpow_mul (log_nonneg hx.le)]
      norm_num
  have hpsi : (Chebyshev.psi - id) =O[atTop] (fun x : ℝ ↦ x / log x) :=
    hmedium.trans <| by
      simpa only [one_div, div_eq_mul_inv, one_mul] using
        (isBigO_refl (fun x : ℝ ↦ x) atTop).mul hdecay'
  have hdiff : (fun x : ℝ ↦ Chebyshev.psi x - Chebyshev.theta x) =O[atTop] (fun x ↦ x / log x) := by
    rw [isBigO_iff']
    refine ⟨2, by positivity, ?_⟩
    have hsmall :=
      (isLittleO_log_rpow_rpow_atTop 2 (by positivity : (0 : ℝ) < 1 / 2)).bound one_pos
    filter_upwards [eventually_ge_atTop 2, hsmall] with x hx hs
    have hsqrt : log x ^ 2 ≤ √x := by
      rw [sqrt_eq_rpow]
      simpa [norm_eq_abs, abs_of_nonneg (log_nonneg (show (1 : ℝ) ≤ x by linarith)),
        abs_of_nonneg (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ x) _)] using hs
    rw [norm_eq_abs, norm_eq_abs]
    calc |Chebyshev.psi x - Chebyshev.theta x|
        ≤ 2 * √x * log x :=
          Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith)
      _ ≤ 2 * (x / log x) := by
        rw [show 2 * √x * log x = 2 * (√x * log x) by ring,
          mul_le_mul_iff_of_pos_left (by positivity : (0 : ℝ) < 2)]
        refine (le_div_iff₀ (log_pos (by linarith))).2 ?_
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x by positivity),
          Real.log_pos (show (1 : ℝ) < x by linarith)]
      _ = 2 * |x / log x| := by
        rw [abs_of_pos (div_pos (by positivity) (log_pos (by linarith)))]
  have htheta : (fun x : ℝ ↦ Chebyshev.theta x - x) =O[atTop] (fun x ↦ x / log x) :=
    (hpsi.sub hdiff).congr' (by aesop) .rfl
  have htheta_div := htheta.mul (isBigO_refl (fun x : ℝ ↦ 1 / log x) atTop)
  have htheta_div' : (fun x : ℝ ↦ Chebyshev.theta x / log x - x / log x) =O[atTop]
        (fun x ↦ x / log x ^ 2) := by
    grind
  have hfinal : (fun x : ℝ ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ) - x / log x) =O[atTop]
        (fun x ↦ x / log x ^ 2) :=
    (Chebyshev.primeCounting_sub_theta_div_log_isBigO.add htheta_div').congr' (by aesop) .rfl
  have hnat := hfinal.comp_tendsto tendsto_natCast_atTop_atTop
  rw [isBigO_iff] at hnat
  obtain ⟨C, hC⟩ := hnat
  rw [eventually_atTop] at hC
  obtain ⟨N₀, hN₀⟩ := hC
  refine ⟨C, N₀, fun N hN ↦ ?_⟩
  have h := hN₀ N hN
  simp only [Function.comp_apply, Nat.floor_natCast, norm_eq_abs] at h
  rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg N) (sq_nonneg (log (N : ℝ))))] at h
  grind

end PNT
