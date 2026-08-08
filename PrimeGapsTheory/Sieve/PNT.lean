/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.NumberTheory.DyadicPNT
public import PrimeGapsTheory.Sieve.S2m.ExpandDrop
public import PrimeGapsTheory.Sieve.S2m.SijD0

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Prime-number-theorem error for the second moment

Bounds the effect of replacing the dyadic prime count by its prime-number-theorem main term.

## Main results

* `lem_S2m_PNT`: Absorbs the prime-counting error into the second-moment error term.
-/

@[expose] public section

open scoped ArithmeticFunction.detotient

open Real Filter Asymptotics PrimeGaps GPYSieveS1 ArithmeticFunction
open PrimeGaps.LemS1RestrictSij

namespace PrimeGaps

/-- For any real `a b S`, the "same-`S`" difference `a·S − b·S` factors, so
`|a·S − b·S| = |a − b| · |S|`.
-/
private theorem lem_S2m_PNT_factor (a b S : ℝ) : |a * S - b * S| = |a - b| * |S| := by
  rw [← sub_mul, abs_mul]

/-- Each summand of the diagonal sum is dominated by the squared supremum of `|y_m|` against the
matching `bSum` weight: `y_m(u)² / ∏ᵢ g(uᵢ) ≤ (⨆ r, |y_m r|)² · bSum W R m u`, the summand being
`0` off the restricted range.
-/
private theorem ym_sq_div_prod_g_le_ciSup_sq_mul_bSum {k : ℕ} (m : Fin k) (R : ℝ) (W : ℕ)
    (lam : (Fin k → ℕ) →₀ ℝ)
    (hsupp : lam.HasPermissibleSupport ⌊R⌋₊ W) (u : Fin k → ℕ) :
    (if (∀ i, 1 ≤ u i) ∧ RestrictedCoprime u (fun _ _ ↦ 1)
        then PrimeGaps.ym m lam u ^ 2 / ∏ i, (g (u i) : ℝ) else 0) ≤
      (⨆ r, |PrimeGaps.ym m lam r|) ^ 2 * PrimeGaps.bSum W R m u := by
  have hbdd := PrimeGaps.ym_abs_bddAbove m lam R W hsupp
  have hb : 0 ≤ (⨆ r, |PrimeGaps.ym m lam r|) ^ 2 * PrimeGaps.bSum W R m u :=
    mul_nonneg (sq_nonneg _) (PrimeGaps.bSum_nonneg _ _ _ _)
  by_cases hnz : PrimeGaps.ym m lam u = 0
  · simp only [hnz]
    split <;> simpa using hb
  · have hpin : u m = 1 := PrimeGaps.ym_pin_eq_one m lam R W hsupp u hnz
    have hle : ∀ i, u i ≤ ⌊R⌋₊ := PrimeGaps.ym_coord_le_floor m lam R W hsupp u hnz
    have hcop : ∀ i, (u i).Coprime W := fun i ↦ PrimeGaps.ym_coord_coprimeW W m lam R hsupp u hnz i
    have hsf : ∀ i, Squarefree (u i) := fun i ↦
      PrimeGaps.ym_coord_squarefree m lam R W hsupp u hnz i
    have hbSum : PrimeGaps.bSum W R m u = ∏ i ∈ Finset.univ.erase m, (1 / (g (u i) : ℝ)) := by
      unfold PrimeGaps.bSum
      rw [if_pos hpin]
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      rw [PrimeGaps.cSum, if_pos ⟨hsf i, hcop i, hle i⟩]
    have hym2 : PrimeGaps.ym m lam u ^ 2 ≤ (⨆ r, |PrimeGaps.ym m lam r|) ^ 2 := by
      rw [← sq_abs (PrimeGaps.ym m lam u)]
      exact pow_le_pow_left₀ (abs_nonneg _) (le_ciSup hbdd u) 2
    have hprod : (∏ i, (g (u i) : ℝ)) = ∏ i ∈ Finset.univ.erase m, (g (u i) : ℝ) := by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ m), hpin]
      simp [detotient_one]
    have hgnn : ∀ i, (0 : ℝ) ≤ (g (u i) : ℝ) := fun i ↦ by positivity
    have hprod_erase_nn : (0 : ℝ) ≤ ∏ i ∈ Finset.univ.erase m, (g (u i) : ℝ) :=
      Finset.prod_nonneg (fun i _ ↦ hgnn i)
    have hbSum' : PrimeGaps.bSum W R m u = 1 / (∏ i ∈ Finset.univ.erase m, (g (u i) : ℝ)) := by
      rw [hbSum]
      simp [one_div, Finset.prod_inv_distrib]
    split
    · rw [hprod, hbSum', div_eq_mul_one_div]
      apply mul_le_mul_of_nonneg_right hym2
      rw [one_div]
      exact inv_nonneg.mpr hprod_erase_nn
    · exact hb

/-- The diagonal sum `Σ` is bounded, in absolute value, by
`y_max² · C_tuple · (φW · log R / W)^(k−1)`, where `C_tuple ≥ 0` is the constant from
`lem_S2m_tuple_g_mass_cutoff` and the side conditions on `R` hold.
-/
private theorem lem_S2m_PNT_sigma_bound {k : ℕ} (m : Fin k) (R : ℝ) (W : ℕ) (lam : (Fin k → ℕ) →₀ ℝ)
    (hsupp : lam.HasPermissibleSupport ⌊R⌋₊ W)
    (Cg : ℝ)
    (hgSum : PrimeGaps.gSum W R ≤ Cg * (W.totient : ℝ) / (W : ℝ) * Real.log R)
    (hWpos : 0 < W) :
    |∑' u : Fin k → ℕ, if (∀ i, 1 ≤ u i) ∧ RestrictedCoprime u (fun _ _ ↦ 1)
        then PrimeGaps.ym m lam u ^ 2 / ∏ i, (g (u i) : ℝ) else 0| ≤
      (⨆ r, |PrimeGaps.ym m lam r|) ^ 2 * (Cg ^ (k - 1)) *
          ((W.totient : ℝ) * Real.log R / W) ^ (k - 1) := by
  set Y := (⨆ r, |PrimeGaps.ym m lam r|) ^ 2 with hY
  have hptwise : ∀ u : Fin k → ℕ, (if (∀ i, 1 ≤ u i) ∧ RestrictedCoprime u (fun _ _ ↦ 1)
        then PrimeGaps.ym m lam u ^ 2 / ∏ i, (g (u i) : ℝ) else 0) ≤ Y *
          PrimeGaps.bSum W R m u := fun u ↦ by
    rw [hY]
    exact ym_sq_div_prod_g_le_ciSup_sq_mul_bSum m R W lam hsupp u
  have hsummaj : Summable (fun u : Fin k → ℕ ↦ Y * PrimeGaps.bSum W R m u) :=
    (PrimeGaps.bSum_summable W R m).mul_left Y
  have hlhsnn : ∀ u : Fin k → ℕ, 0 ≤ (if (∀ i, 1 ≤ u i) ∧ RestrictedCoprime u (fun _ _ ↦ 1)
        then PrimeGaps.ym m lam u ^ 2 / ∏ i, (g (u i) : ℝ) else 0) := fun u ↦ by
    split
    · exact div_nonneg (sq_nonneg _) (Finset.prod_nonneg fun i _ ↦ by positivity)
    · exact le_rfl
  have hsummlhs : Summable (fun u : Fin k → ℕ ↦
      if (∀ i, 1 ≤ u i) ∧ RestrictedCoprime u (fun _ _ ↦ 1)
        then PrimeGaps.ym m lam u ^ 2 / ∏ i, (g (u i) : ℝ) else 0) :=
    Summable.of_nonneg_of_le hlhsnn hptwise hsummaj
  rw [abs_of_nonneg (tsum_nonneg hlhsnn)]
  have hchain : (∑' u : Fin k → ℕ, if (∀ i, 1 ≤ u i) ∧ RestrictedCoprime u (fun _ _ ↦ 1)
        then PrimeGaps.ym m lam u ^ 2 / ∏ i, (g (u i) : ℝ) else 0) ≤
      Y * (PrimeGaps.gSum W R) ^ (k - 1) :=
    calc (∑' u : Fin k → ℕ, if (∀ i, 1 ≤ u i) ∧ RestrictedCoprime u (fun _ _ ↦ 1)
        then PrimeGaps.ym m lam u ^ 2 / ∏ i, (g (u i) : ℝ) else 0) ≤
        ∑' u : Fin k → ℕ, Y * PrimeGaps.bSum W R m u :=
          Summable.tsum_le_tsum hptwise hsummlhs hsummaj
      _ = Y * ∑' u : Fin k → ℕ, PrimeGaps.bSum W R m u := by rw [tsum_mul_left]
      _ = Y * (PrimeGaps.gSum W R) ^ (k - 1) := by rw [PrimeGaps.tsum_bSum_eq]
  refine hchain.trans ?_
  have hYnn : 0 ≤ Y := sq_nonneg _
  have hpow : (PrimeGaps.gSum W R) ^ (k - 1) ≤
      (Cg * (W.totient : ℝ) / (W : ℝ) * Real.log R) ^ (k - 1) :=
    pow_le_pow_left₀ (PrimeGaps.gSum_nonneg W R) hgSum _
  have hWposR : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hWpos
  have hrw : (Cg * (W.totient : ℝ) / (W : ℝ) * Real.log R) ^ (k - 1) =
      Cg ^ (k - 1) * ((W.totient : ℝ) * Real.log R / W) ^ (k - 1) := by
    rw [← mul_pow]
    congr 1
    field_simp
  calc Y * (PrimeGaps.gSum W R) ^ (k - 1)
      ≤ Y * (Cg * (W.totient : ℝ) / (W : ℝ) * Real.log R) ^ (k - 1) :=
        mul_le_mul_of_nonneg_left hpow hYnn
    _ = Y * Cg ^ (k - 1) * ((W.totient : ℝ) * Real.log R / W) ^ (k - 1) := by
      rw [hrw]
      ring

/-- The product of the `|X − N/L|` and `|Σ|` bounds is absorbed into the target right-hand side for
a suitable choice of constant and threshold.
-/
private theorem lem_S2m_PNT_growth {k : ℕ} (m : Fin k) (N : ℕ) (R : ℝ) (W : ℕ)
    (lam : (Fin k → ℕ) →₀ ℝ) (K Ctuple : ℝ) (hK0 : 0 ≤ K) (hCt0 : 0 ≤ Ctuple)
    (hk : 2 ≤ k)
    (hlogR : Real.log R ≤ Real.log N)
    (hlogRpos : 0 ≤ Real.log R)
    (hD0 : PrimeGaps.D₀ (N : ℝ) ≤ Real.log N)
    (hD0pos : 0 < PrimeGaps.D₀ (N : ℝ))
    (hLpos : 0 < Real.log N)
    (hWpos : 0 < W) (hφpos : 0 < W.totient) :
    (K * N / (Real.log N) ^ 2 / (W.totient : ℝ)) * ((⨆ r, |PrimeGaps.ym m lam r|) ^ 2 * Ctuple *
        ((W.totient : ℝ) * Real.log R / W) ^ (k - 1)) ≤
      (K * Ctuple) * (⨆ r, |PrimeGaps.ym m lam r|) ^ 2 * (W.totient : ℝ) ^ (k - 2) * (N : ℝ) *
        (Real.log N) ^ (k - 2) / ((W : ℝ) ^ (k - 1) * PrimeGaps.D₀ (N : ℝ)) := by
  have hφposR : (0 : ℝ) < (W.totient : ℝ) := by exact_mod_cast hφpos
  have hWposR : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hWpos
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hY0 : (0 : ℝ) ≤ (⨆ r, |PrimeGaps.ym m lam r|) ^ 2 := sq_nonneg _
  set φW : ℝ := (W.totient : ℝ) with hφW
  set Wr : ℝ := (W : ℝ) with hWr
  set L : ℝ := Real.log N with hL
  set logR : ℝ := Real.log R with hlogRdef
  set D0 : ℝ := PrimeGaps.D₀ (N : ℝ) with hD0def
  set Y : ℝ := (⨆ r, |PrimeGaps.ym m lam r|) ^ 2 with hYdef
  set Nr : ℝ := (N : ℝ) with hNr
  have hk1 : k - 1 = (k - 2) + 1 := by omega
  have hkey : logR ^ (k - 1) / L ^ 2 ≤ L ^ (k - 2) / D0 := by
    have h3 : logR ^ (k - 1) ≤ L ^ (k - 2) * L := by
      rw [← pow_succ, ← hk1]
      exact pow_le_pow_left₀ hlogRpos hlogR _
    calc logR ^ (k - 1) / L ^ 2 ≤ (L ^ (k - 2) * L) / L ^ 2 :=
          div_le_div_of_nonneg_right h3 (by positivity)
      _ = L ^ (k - 2) / L := by
          rw [pow_two]
          field_simp
      _ ≤ L ^ (k - 2) / D0 := div_le_div_of_nonneg_left (by positivity) hD0pos hD0
  set A : ℝ := K * Ctuple * Y * φW ^ (k - 2) * Nr with hA
  have hAnn : 0 ≤ A := by
    rw [hA]
    positivity
  have hφk : φW ^ (k - 1) = φW ^ (k - 2) * φW := by rw [hk1, pow_succ]
  have heqL : (K * Nr / L ^ 2 / φW) * (Y * Ctuple * (φW * logR / Wr) ^ (k - 1)) =
      A / Wr ^ (k - 1) * (logR ^ (k - 1) / L ^ 2) := by
    rw [div_pow, mul_pow, hφk, hA]
    field_simp
  have heqR : (K * Ctuple) * Y * φW ^ (k - 2) * Nr * L ^ (k - 2) / (Wr ^ (k - 1) * D0) =
      A / Wr ^ (k - 1) * (L ^ (k - 2) / D0) := by
    rw [hA]
    field_simp
  rw [heqL, heqR]
  exact mul_le_mul_of_nonneg_left hkey (by positivity)

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- For all large `N` the sieve truncation `R` and the level `D₀ N` sit correctly against `log N`:
`0 ≤ log R ≤ log N`, `0 < D₀ N ≤ log N`, and `0 < log N`.
-/
private theorem eventually_logR_and_D0_le_logN (θ δ : ℝ)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2)) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → Real.log (R) ≤ Real.log N ∧ 0 ≤ Real.log (R) ∧
      PrimeGaps.D₀ (N : ℝ) ≤ Real.log N ∧
      0 < PrimeGaps.D₀ (N : ℝ) ∧
      0 < Real.log N := by
  have hexpo : 0 < θ / 2 - δ := by linarith [hδ.2]
  have hexpo1 : θ / 2 - δ ≤ 1 := by linarith [hθ.2, hδ.1]
  obtain ⟨n3, hn3⟩ := Filter.eventually_atTop.mp
    (tendsto_natCast_atTop_atTop.eventually eventually_D0_le_log)
  obtain ⟨n4, hn4⟩ := Filter.eventually_atTop.mp
    (tendsto_natCast_atTop_atTop.eventually eventually_D0_pos)
  refine ⟨max (↑n3) (max (↑n4) 2), fun N hN ↦ ?_⟩
  simp only [max_le_iff] at hN
  obtain ⟨hN3, hN4, hN2b⟩ := hN
  have hN2nat : 2 ≤ N := by exact_mod_cast hN2b
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlogNpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2nat)
  have hlogR : Real.log (R) = (θ / 2 - δ) * Real.log N :=
    Real.log_rpow hNpos (θ / 2 - δ)
  refine ⟨?_, ?_, hn3 N (by exact_mod_cast hN3), hn4 N (by exact_mod_cast hN4), hlogNpos⟩
  · rw [hlogR]
    nlinarith [hlogNpos.le]
  · rw [hlogR]
    positivity

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- `lem_S2m_PNT`: absorbing the `X_N` secondary error. -/
@[pg_tag "bg246" "lem_S2m_PNT"]
theorem lem_S2m_PNT {k : ℕ} (m : Fin k) (θ δ : ℝ) (hk : 2 ≤ k) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2)) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ lam : (Fin k → ℕ) →₀ ℝ,
        lam.HasPermissibleSupport ⌊R⌋₊ (W N) →
        |((Nat.primeCountingIoc N (2 * N) : ℝ) / ((W N).totient : ℝ)) *
          (∑' u : Fin k → ℕ, if (∀ i, 1 ≤ u i) ∧ RestrictedCoprime u (fun _ _ ↦ 1)
              then PrimeGaps.ym m lam u ^ 2 / ∏ i, (g (u i) : ℝ)
              else 0) - ((N : ℝ) / (((W N).totient : ℝ) * Real.log N)) *
            (∑' u : Fin k → ℕ, if (∀ i, 1 ≤ u i) ∧ RestrictedCoprime u (fun _ _ ↦ 1)
              then PrimeGaps.ym m lam u ^ 2 / ∏ i, (g (u i) : ℝ)
              else 0)| ≤
        C * (⨆ r, |PrimeGaps.ym m lam r|) ^ 2 * ((W N).totient : ℝ) ^ (k - 2) *
          (N : ℝ) * (Real.log N) ^ (k - 2) / (((W N : ℝ)) ^ (k - 1) *
              PrimeGaps.D₀ (N : ℝ)) := by
  obtain ⟨K₀, M, hPNT⟩ := PNT.primeCountingIoc_self_two_mul
  let K := |K₀|
  have hK0 : 0 ≤ K := abs_nonneg K₀
  have hH1' : ∀ N : ℕ, M ≤ N →
      |(Nat.primeCountingIoc N (2 * N) : ℝ) - N / Real.log N| ≤
        K * N / (Real.log N) ^ 2 := by
    intro N hN
    refine (hPNT N hN).trans ?_
    dsimp [K]
    calc K₀ * N / Real.log N ^ 2
        = K₀ * ((N : ℝ) / Real.log N ^ 2) := by ring
      _ ≤ |K₀| * ((N : ℝ) / Real.log N ^ 2) :=
          mul_le_mul_of_nonneg_right (le_abs_self K₀) (by positivity)
      _ = |K₀| * N / Real.log N ^ 2 := by ring
  obtain ⟨Cg, hCg0, N₀g, hgs⟩ := PrimeGaps.gSum_le θ δ hδ.2
  set Ctuple : ℝ := Cg ^ (k - 1) with hCtuple_def
  have hCt0 : 0 ≤ Ctuple := by
    rw [hCtuple_def]
    positivity
  refine ⟨K * Ctuple + 1, by positivity, ?_⟩
  obtain ⟨N₀, hN₀⟩ := eventually_logR_and_D0_le_logN θ δ hθ hδ
  refine ⟨max (max N₀ N₀g) (↑M), fun N hN lam hsupp ↦ ?_⟩
  simp only [max_le_iff] at hN
  obtain ⟨⟨hN₀N, hNg⟩, hMR⟩ := hN
  have hMN : M ≤ N := by exact_mod_cast hMR
  obtain ⟨hlogR, hlogRpos, hD0, hD0pos, hLpos⟩ := hN₀ N hN₀N
  have hWpos : 0 < W N := PrimeGaps.W_pos
  have hφpos : 0 < (W N).totient := Nat.totient_pos.mpr hWpos
  set S : ℝ := (∑' u : Fin k → ℕ, if (∀ i, 1 ≤ u i) ∧ RestrictedCoprime u (fun _ _ ↦ 1)
        then PrimeGaps.ym m lam u ^ 2 / ∏ i, (g (u i) : ℝ) else 0) with hS
  set X : ℝ := (Nat.primeCountingIoc N (2 * N) : ℝ) with hX
  set φW : ℝ := ((W N).totient : ℝ) with hφW
  set L : ℝ := Real.log N with hL
  have hS1 : |(X / φW) * S - ((N : ℝ) / (φW * L)) * S| =
      |X / φW - (N : ℝ) / (φW * L)| * |S| := lem_S2m_PNT_factor _ _ _
  rw [hS1]
  have hφposR : (0 : ℝ) < φW := by rw [hφW]; exact_mod_cast hφpos
  have hφne : φW ≠ 0 := ne_of_gt hφposR
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hfac : X / φW - (N : ℝ) / (φW * L) = (X - (N : ℝ) / L) / φW := by
    field_simp
  rw [hfac]
  have hS2 : |X - (N : ℝ) / L| ≤ K * (N : ℝ) / L ^ 2 := hH1' N hMN
  have hS3 : |S| ≤ (⨆ r, |PrimeGaps.ym m lam r|) ^ 2 * Ctuple *
        (φW * Real.log (R) / (W N)) ^ (k - 1) := by
    rw [hS, hφW, hCtuple_def]
    exact lem_S2m_PNT_sigma_bound m R (W N) lam hsupp Cg (hgs N hNg) hWpos
  have hcomb : |(X - (N : ℝ) / L) / φW| * |S| ≤ (K * (N : ℝ) / L ^ 2 / φW) *
          ((⨆ r, |PrimeGaps.ym m lam r|) ^ 2 * Ctuple *
            (φW * Real.log (R) / (W N)) ^ (k - 1)) := by
    rw [abs_div, abs_of_pos hφposR]
    have hbnd : |X - (N : ℝ) / L| / φW ≤ K * (N : ℝ) / L ^ 2 / φW := by gcongr
    have hnumnn : (0 : ℝ) ≤ K * (N : ℝ) / L ^ 2 / φW :=
      div_nonneg (div_nonneg (mul_nonneg hK0 (Nat.cast_nonneg N)) (sq_nonneg _)) hφposR.le
    calc |X - (N : ℝ) / L| / φW * |S| ≤ (K * (N : ℝ) / L ^ 2 / φW) * |S| :=
          mul_le_mul_of_nonneg_right hbnd (abs_nonneg _)
      _ ≤ (K * (N : ℝ) / L ^ 2 / φW) * ((⨆ r, |PrimeGaps.ym m lam r|) ^ 2 * Ctuple *
              (φW * Real.log (R) / (W N)) ^ (k - 1)) :=
          mul_le_mul_of_nonneg_left hS3 hnumnn
  refine hcomb.trans ((lem_S2m_PNT_growth m N (R) (W N) lam K Ctuple hK0 hCt0 hk
    hlogR hlogRpos hD0 hD0pos hLpos hWpos hφpos).trans ?_)
  have hWposR : (0 : ℝ) < (W N : ℝ) := by exact_mod_cast hWpos
  have hdenpos : (0 : ℝ) < (W N : ℝ) ^ (k - 1) * PrimeGaps.D₀ (N : ℝ) := by positivity
  calc K * Ctuple * (⨆ r, |PrimeGaps.ym m lam r|) ^ 2 * ((W N).totient : ℝ) ^ (k - 2) * (N : ℝ) *
        Real.log N ^ (k - 2) / ((W N : ℝ) ^ (k - 1) * PrimeGaps.D₀ (N : ℝ)) =
      K * Ctuple * (⨆ r, |PrimeGaps.ym m lam r|) ^ 2 * φW ^ (k - 2) * (N : ℝ) * L ^ (k - 2) /
        ((W N : ℝ) ^ (k - 1) * PrimeGaps.D₀ (N : ℝ)) := by rw [hφW, hL]
    _ ≤ (K * Ctuple + 1) * (⨆ r, |PrimeGaps.ym m lam r|) ^ 2 * φW ^ (k - 2) * (N : ℝ) *
        L ^ (k - 2) / ((W N : ℝ) ^ (k - 1) * PrimeGaps.D₀ (N : ℝ)) := by
        gcongr
        linarith

end PrimeGaps
