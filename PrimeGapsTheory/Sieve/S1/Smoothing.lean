/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.S1.ApplyPartialSum
public import PrimeGapsTheory.Sieve.S1.DropUij
public import PrimeGapsTheory.Sieve.S1.SubstituteSmoothY

import PrimeGapsTheory.Tactic.PaperTag

/-!
# The smooth first-moment asymptotic

Combines the transformed-sum estimates into the smooth asymptotic for the first moment.

## Main results

* `lem_S1_smooth`: Gives the smooth first-moment asymptotic.
-/

@[expose] public section

open Real

namespace PrimeGaps

open Filter in
/-- For any `c > 0`, eventually `D₀ N · log (D₀ N) ≤ c · log N`. Since `D₀ N = log log log N`, the
left side is `o(log N)`.
-/
private theorem eventually_D0_mul_logD0_le {c : ℝ} (hc : 0 < c) : ∀ᶠ N : ℝ in atTop,
      PrimeGaps.D₀ N * Real.log (PrimeGaps.D₀ N) ≤ c * Real.log N := by
  have hLO2 : ∀ᶠ z : ℝ in atTop, (Real.log z) ^ 2 ≤ c * z :=
    Real.eventually_log_pow_le_const_mul 2 hc
  have he4 : ∀ᶠ N : ℝ in atTop, (Real.log (Real.log N)) ^ 2 ≤ c * Real.log N :=
    Real.tendsto_log_atTop.eventually hLO2
  have hp1 : ∀ᶠ N : ℝ in atTop, (2 : ℝ) ≤ PrimeGaps.D₀ N :=
    (eventually_ge_atTop (rexp (rexp (rexp 2)))).mono
      (fun N hN ↦ PrimeGaps.MaynardOffDiagonal.two_le_D0_of_large hN)
  have hp2 : ∀ᶠ N : ℝ in atTop, PrimeGaps.D₀ N ≤ Real.log (Real.log N) := by
    have hv : ∀ᶠ N : ℝ in atTop, (1 : ℝ) ≤ Real.log (Real.log N) :=
      Real.tendsto_log_atTop.eventually (Real.tendsto_log_atTop.eventually_ge_atTop 1)
    filter_upwards [hv] with N hN
    have hpos : (0 : ℝ) < Real.log (Real.log N) := lt_of_lt_of_le one_pos hN
    have hh := Real.log_le_sub_one_of_pos hpos
    simp only [PrimeGaps.D₀]
    linarith
  filter_upwards [hp1, hp2, he4] with N hN1 hN2 hN4
  have hD0pos : (0 : ℝ) < PrimeGaps.D₀ N := by linarith
  have hlogD0 : Real.log (PrimeGaps.D₀ N) ≤ PrimeGaps.D₀ N := by
    have := Real.log_le_sub_one_of_pos hD0pos; linarith
  calc PrimeGaps.D₀ N * Real.log (PrimeGaps.D₀ N) ≤ PrimeGaps.D₀ N * PrimeGaps.D₀ N :=
        mul_le_mul_of_nonneg_left hlogD0 hD0pos.le
    _ = (PrimeGaps.D₀ N) ^ 2 := by ring
    _ ≤ (Real.log (Real.log N)) ^ 2 := pow_le_pow_left₀ hD0pos.le hN2 2
    _ ≤ c * Real.log N := hN4

/-- From `|S − a·x| ≤ e₁`, `|x − y| ≤ e₂`, `|y − z| ≤ e₃` and `0 ≤ a`, deduce
`|S − a·z| ≤ e₁ + a·e₂ + a·e₃`.
-/
private lemma s1_smooth_triangle {S a x y z e1 e2 e3 : ℝ} (ha : 0 ≤ a)
    (H1 : |S - a * x| ≤ e1) (H2 : |x - y| ≤ e2) (H3 : |y - z| ≤ e3) :
    |S - a * z| ≤ e1 + a * e2 + a * e3 := by
  have hrw : S - a * z = (S - a * x) + a * (x - y) + a * (y - z) := by ring
  have h2' : |a * (x - y)| ≤ a * e2 := by
    rw [abs_mul, abs_of_nonneg ha]; exact mul_le_mul_of_nonneg_left H2 ha
  have h3' : |a * (y - z)| ≤ a * e3 := by
    rw [abs_mul, abs_of_nonneg ha]; exact mul_le_mul_of_nonneg_left H3 ha
  rw [hrw]
  calc |(S - a * x) + a * (x - y) + a * (y - z)|
      ≤ |(S - a * x) + a * (x - y)| + |a * (y - z)| := abs_add_le _ _
    _ ≤ (|S - a * x| + |a * (x - y)|) + |a * (y - z)| := by
        gcongr; exact abs_add_le _ _
    _ ≤ e1 + a * e2 + a * e3 := by linarith [add_le_add (add_le_add H1 h2') h3']

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
open MeasureTheory GPYSieveS1 MaynardSmoothY Filter in
/-- (Maynard, Lemma 6.2). For a smooth weight `F` supported on the simplex `𝓡 k`, the first moment
`S₁` equals its main term `φW^k · N · (log R)^k / W^{k+1} · ∫ F²` up to an error of order
`Fmax² · φW^k · N · (log R)^k / (W^{k+1} · D₀)`.
-/
@[pg_tag "bg246" "lem_S1_smooth"]
theorem lem_S1_smooth {k : ℕ} (hk : 2 ≤ k) (h : Fin k → ℕ) (hadm : IsAdmissible h)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupp : Function.support F ⊆ 𝓡 k) :
    ∀ θ δ : ℝ, θ ∈ Set.Ioo (0 : ℝ) 1 → δ ∈ Set.Ioo (0 : ℝ) (θ / 2) →
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
    ∀ v0 : ℕ, V0Valid h (W N) v0 →
      |S1 h (l₀ (R) (W N) (fun x ↦ F (WithLp.toLp 2 x))) N (W N) v0 -
          ((W N).totient : ℝ) ^ k * (N : ℝ) * Real.log (R) ^ k /
              (W N : ℝ) ^ (k + 1) * (∫ x in 𝓡 k, (F x) ^ 2)| ≤
        (C) * (MaynardSmoothY.Fmax F) ^ 2 * ((W N).totient : ℝ) ^ k * (N : ℝ) * Real.log (R) ^ k /
            ((W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ)) := by
  classical
  intro θ δ hθ hδ
  have hcpos : (0 : ℝ) < θ / 2 - δ := sub_pos.mpr hδ.2
  obtain ⟨C1, hC1, N1, hSub⟩ := lem_S1_substitute_smooth_y hk h hadm F hF hFsupp θ δ hθ hδ
  obtain ⟨C2, hC2, N2, hDrop⟩ := drop_uij_coupling_bound δ θ hθ hδ
  obtain ⟨C3, hC3, N3, hApp⟩ := S1_aggregate δ θ hθ hδ
  obtain ⟨Mabs, hMabs⟩ := Filter.eventually_atTop.mp (eventually_D0_mul_logD0_le hcpos)
  refine ⟨C1 + C2 + C3, by linarith, ?_⟩
  refine ⟨max (max N1 N2) (max N3 (max Mabs (rexp (rexp (rexp 2))))), ?_⟩
  intro N hN v0 hv0
  obtain ⟨hA, hB⟩ := max_le_iff.mp hN
  obtain ⟨hN1, hN2⟩ := max_le_iff.mp hA
  obtain ⟨hN3, hCD⟩ := max_le_iff.mp hB
  obtain ⟨hNabs, hNe⟩ := max_le_iff.mp hCD
  have hgt1 : (1 : ℝ) < rexp (rexp (rexp 2)) :=
    Real.one_lt_exp_iff.mpr (by positivity)
  have hN1R : (1 : ℝ) < (N : ℝ) := lt_of_lt_of_le hgt1 hNe
  have hNposR : (0 : ℝ) < (N : ℝ) := lt_trans one_pos hN1R
  have hD2 : (2 : ℝ) ≤ PrimeGaps.D₀ (N : ℝ) := PrimeGaps.MaynardOffDiagonal.two_le_D0_of_large hNe
  have hD0pos : (0 : ℝ) < PrimeGaps.D₀ (N : ℝ) := by linarith
  have hlogRval : Real.log (R) = (θ / 2 - δ) * Real.log (N : ℝ) := Real.log_rpow hNposR _
  have hlogR_pos : (0 : ℝ) < Real.log (R) := by
    rw [hlogRval]; exact mul_pos hcpos (Real.log_pos hN1R)
  have hℓnn : (0 : ℝ) ≤ Real.log (R) := hlogR_pos.le
  have hAbsMain : PrimeGaps.D₀ (N : ℝ) * Real.log (PrimeGaps.D₀ (N : ℝ)) ≤ Real.log (R) := by
    rw [hlogRval]; exact hMabs (N : ℝ) hNabs
  have habs : Real.log (PrimeGaps.D₀ (N : ℝ)) ≤ Real.log (R) / PrimeGaps.D₀ (N : ℝ) := by
    rw [le_div_iff₀ hD0pos, mul_comm]; exact hAbsMain
  have hk1 : k - 1 + 1 = k := by omega
  have hkpow : Real.log (R) ^ k = Real.log (R) * Real.log (R) ^ (k - 1) := by
    conv_lhs => rw [← hk1, pow_succ]
    ring
  have H1 := hSub N hN1 v0 hv0
  have H3 := hApp N hN3 F hF hFsupp
  have ha : (0 : ℝ) ≤ (N : ℝ) / (W N : ℝ) := by positivity
  have hcomb := s1_smooth_triangle ha H1 (by
    convert hDrop N hN2 F hF hFsupp using 1
    congr 2
    · apply tsum_congr
      intro u
      by_cases hu : DropUij.raGuard (W N) u
      · rw [if_pos hu, if_pos (by simpa only [DropUij.raGuard] using hu)]
        rfl
      · rw [if_neg hu, if_neg]
        simpa only [DropUij.raGuard] using hu
    · apply tsum_congr
      intro u
      by_cases hu : DropUij.facGuard (W N) u
      · rw [if_pos hu, if_pos (by simpa only [DropUij.facGuard] using hu)]
        rfl
      · rw [if_neg hu, if_neg]
        simpa only [DropUij.facGuard] using hu) H3
  have hmain : ((W N).totient : ℝ) ^ k * (N : ℝ) * Real.log (R) ^ k /
          (W N : ℝ) ^ (k + 1) * (∫ x in 𝓡 k, (F x) ^ 2) = (N : ℝ) / (W N : ℝ) *
            (((W N).totient : ℝ) ^ k * Real.log (R) ^ k /
                (W N : ℝ) ^ k * (∫ x in 𝓡 k, (F x) ^ 2)) := by
    rw [pow_succ]; ring
  rw [hmain]
  refine le_trans hcomb ?_
  have hK : (0 : ℝ) ≤ MaynardSmoothY.Fmax F ^ 2 * ((W N).totient : ℝ) ^ k *
      (N : ℝ) * Real.log (R) ^ (k - 1) /
      (W N : ℝ) ^ (k + 1) :=
    div_nonneg (mul_nonneg (by positivity) (pow_nonneg hℓnn _)) (by positivity)
  set K : ℝ := MaynardSmoothY.Fmax F ^ 2 * ((W N).totient : ℝ) ^ k *
      (N : ℝ) * Real.log (R) ^ (k - 1) /
      (W N : ℝ) ^ (k + 1) with hKdef
  have hLHS : (C1 * MaynardSmoothY.Fmax F ^ 2 * ((W N).totient : ℝ) ^ k *
    (N : ℝ) * Real.log (R) ^ k / ((W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ))) + (N : ℝ) /
              (W N : ℝ) *
            (C2 * MaynardSmoothY.Fmax F ^ 2 * ((W N).totient : ℝ) ^ k * Real.log (R) ^ k /
                ((W N : ℝ) ^ k * PrimeGaps.D₀ (N : ℝ))) + (N : ℝ) / (W N : ℝ) *
            (C3 * MaynardSmoothY.Fmax F ^ 2 * ((W N).totient : ℝ) ^ k *
                Real.log (PrimeGaps.D₀ (N : ℝ)) *
                Real.log (R) ^ (k - 1) / (W N : ℝ) ^ k) =
        C1 * (K * (Real.log (R) / PrimeGaps.D₀ (N : ℝ))) +
          C2 * (K * (Real.log (R) / PrimeGaps.D₀ (N : ℝ))) +
          C3 * (K * Real.log (PrimeGaps.D₀ (N : ℝ))) := by
    rw [hKdef, hkpow]; ring
  have hRHS : (C1 + C2 + C3) * MaynardSmoothY.Fmax F ^ 2 * ((W N).totient : ℝ) ^ k *
          (N : ℝ) * Real.log (R) ^ k /
          ((W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ)) =
        C1 * (K * (Real.log (R) / PrimeGaps.D₀ (N : ℝ))) +
          C2 * (K * (Real.log (R) / PrimeGaps.D₀ (N : ℝ))) +
          C3 * (K * (Real.log (R) / PrimeGaps.D₀ (N : ℝ))) := by
    rw [hKdef, hkpow]; ring
  rw [hLHS, hRHS]
  have hmono : C3 * (K * Real.log (PrimeGaps.D₀ (N : ℝ))) ≤
        C3 * (K * (Real.log (R) / PrimeGaps.D₀ (N : ℝ))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left habs hK) hC3.le
  linarith [hmono]

end PrimeGaps
