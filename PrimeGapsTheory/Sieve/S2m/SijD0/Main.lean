/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.S2m.SijD0.PairMasterG

import PrimeGapsTheory.Tactic.PaperTag

/-!
# The S2m sij bound at D0

Assembles the tail and pair bounds into `lem_S2m_sij_D0`.

## Main results

* `lem_S2m_sij_D0`
-/

@[expose] public section

open Real

open scoped ArithmeticFunction.Moebius

open scoped ArithmeticFunction.detotient

/-- The threshold `exp (exp (exp 100)) + 1` used throughout this section lies above `exp 1`. -/
private lemma exp_one_lt_of_exp_exp_exp_hundred_lt {x : ℝ}
    (hx : rexp (rexp (rexp 100)) + 1 ≤ x) : rexp 1 < x :=
  (Real.exp_le_exp.mpr (Real.one_le_exp_iff.mpr (Real.exp_pos 100).le)).trans_lt (by linarith)

open GPYSieveS1 PrimeGaps in
open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- The unrestricted squarefree sum `∑_{s ≥ 1 squarefree} |μ(s)| / g(s)²` is finite: by
`PrimeGaps.term_eq_squarefree` it is literally the convergent series `∑' s, PrimeGaps.term s`. -/
private lemma exists_tsum_squarefree_abs_moebius_div_g_sq_le :
    ∃ C : ℝ, 0 < C ∧ (∑' s : ℕ, if 1 ≤ s ∧ Squarefree s
        then |(μ s : ℝ)| / (g s : ℝ) ^ 2 else 0) ≤ C := by
  classical
  have hnn : (0 : ℝ) ≤ ∑' s, PrimeGaps.term s := tsum_nonneg PrimeGaps.term_nonneg
  refine ⟨(∑' s, PrimeGaps.term s) + 1, by linarith, ?_⟩
  rw [tsum_congr (fun s ↦ (PrimeGaps.term_eq_squarefree s).symm)]
  linarith

open Classical GPYSieveS1 PrimeGaps in
open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- Once `N` is large the squarefree sum `∑_{s > ⌊D₀ N⌋₊} |μ(s)| / g(s)²` restricted to `s` all
of whose prime factors exceed `⌊D₀ N⌋₊` is `O(1 / D₀ N)`. This upgrades
`guarded_g_tail_le_div`, which is stated in terms of `⌊D₀ N⌋₊`, using `D₀ N ≤ 2 ⌊D₀ N⌋₊`. -/
private lemma exists_tsum_guarded_abs_moebius_div_g_sq_le_div_D₀ :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      (∑' s : ℕ, if ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < s ∧ Squarefree s ∧
            (∀ q, Nat.Prime q → q ∣ s → ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < q)
          then |(μ s : ℝ)| / (g s : ℝ) ^ 2 else 0) ≤
        C / PrimeGaps.D₀ (N : ℝ) := by
  classical
  obtain ⟨K, hK, hcore⟩ := guarded_g_tail_le_div
  refine ⟨2 * K, by positivity, rexp (rexp (rexp 100)) + 1, fun N hN ↦ ?_⟩
  have hD0gt : (100 : ℝ) < PrimeGaps.D₀ (N : ℝ) := PrimeGaps.lt_D₀_of_le hN
  have hfloor : 100 ≤ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hfloorR_pos : (0 : ℝ) < (⌊PrimeGaps.D₀ (N : ℝ)⌋₊ : ℝ) := Nat.cast_pos.mpr (by omega)
  have hD0_le_two_floor : PrimeGaps.D₀ (N : ℝ) ≤ 2 * (⌊PrimeGaps.D₀ (N : ℝ)⌋₊ : ℝ) := by
    linarith only [Nat.sub_one_lt_floor (PrimeGaps.D₀ (N : ℝ)), hD0gt]
  refine le_trans (hcore _ hfloor) ?_
  rw [div_le_div_iff₀ hfloorR_pos (by linarith : (0 : ℝ) < PrimeGaps.D₀ (N : ℝ))]
  linarith only [mul_le_mul_of_nonneg_left hD0_le_two_floor hK.le]

open GPYSieveS1 PrimeGaps in
open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- Chebyshev's upper bound gives `π(N, 2N] = O(N / log N)`, hence
`π(N, 2N] / φ(W N) ≤ C N / (φ(W N) log N)` for all large `N`. -/
private lemma exists_primeCountingIoc_div_totient_W_le :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      (Nat.primeCountingIoc N (2 * N) : ℝ) / (Nat.totient (W N) : ℝ) ≤ C * (N : ℝ) /
        ((Nat.totient (W N) : ℝ) * Real.log (N : ℝ)) := by
  refine ⟨2 * Real.log 4, by positivity, rexp (rexp (rexp 100)) + 1, fun N hN ↦ ?_⟩
  have hN_gt1 : (1 : ℝ) < (N : ℝ) :=
    (Real.one_lt_exp_iff.mpr one_pos).trans (exp_one_lt_of_exp_exp_exp_hundred_lt hN)
  have hNge1 : 1 ≤ N := by exact_mod_cast hN_gt1.le
  have hlogNpos : (0 : ℝ) < Real.log (N : ℝ) := Real.log_pos hN_gt1
  have hφWpos : (0 : ℝ) < (Nat.totient (W N) : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr PrimeGaps.W_pos
  have h1 : (Nat.primeCountingIoc N (2 * N) : ℝ) * Real.log (N : ℝ) ≤ 2 * Real.log 4 * (N : ℝ) := by
    rw [PrimeGaps.primeCountingIoc_eq_primeCounting_diff N]
    calc (((2 * N).primeCounting : ℝ) - (N.primeCounting : ℝ)) * Real.log (N : ℝ)
        ≤ Chebyshev.theta ((2 * N : ℕ) : ℝ) := chebyshev_pi_diff_mul_log_le N hNge1
      _ ≤ Real.log 4 * ((2 * N : ℕ) : ℝ) := Chebyshev.theta_le_log4_mul_x (by positivity)
      _ = 2 * Real.log 4 * (N : ℝ) := by push_cast; ring
  rw [div_le_div_iff₀ hφWpos (by positivity)]
  exact le_of_eq_of_le (by ring) (mul_le_mul_of_nonneg_right h1 hφWpos.le)

-- Bounds the sum of large-prime coupling contributions.
namespace PrimeGaps

open GPYSieveS1 PrimeGaps.LemS1RestrictSij in
open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- The second-moment contribution from off-diagonal terms with `s i j > ⌊D₀ N⌋₊` is
`O((⨆ r, |ym m lam r|)² φ(W N)^(k-2) N (log R)^(k-1) / (W N^(k-1) D₀ N log N))`. -/
@[pg_tag "bg246" "lem_S2m_sij_D0"]
theorem lem_S2m_sij_D0 {k : ℕ} (m : Fin k) :
    ∀ θ δ : ℝ, θ ∈ Set.Ioo (0 : ℝ) 1 → δ ∈ Set.Ioo (0 : ℝ) (θ / 2) →
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
    ∀ lam : (Fin k → ℕ) →₀ ℝ, lam.HasPermissibleSupport ⌊R⌋₊ (W N) →
    ∀ i j : Fin k, i ≠ j → ((Nat.primeCountingIoc N (2 * N) : ℝ) /
      (Nat.totient (W N) : ℝ)) * (∑' u : Fin k → ℕ, ∑' s : Fin k → Fin k → ℕ,
            |(if ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
                  RestrictedCoprime u s ∧ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < s i j) then
                (∏ i, (μ (u i) : ℝ) ^ 2 / (g (u i) : ℝ)) *
                (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
                    (μ (s p.1 p.2) : ℝ) / (g (s p.1 p.2) : ℝ) ^ 2) *
                PrimeGaps.ym m lam (PrimeGaps.boldA u s) * PrimeGaps.ym m lam (PrimeGaps.boldB u s)
              else 0)|) ≤
        C * (⨆ r, |PrimeGaps.ym m lam r|) ^ 2 * (Nat.totient (W N) : ℝ) ^ (k - 2) *
            N * (Real.log R) ^ (k - 1) /
            ((W N : ℝ) ^ (k - 1) * PrimeGaps.D₀ (N : ℝ) * Real.log N) := by
  intro θ δ hθ hδ
  classical
  set Ufin_g : ℕ → ℝ := fun N ↦ ∑ u ∈ Finset.Icc 1 ⌊R⌋₊ with Nat.Coprime u (W N),
        (μ u : ℝ) ^ 2 / (g u : ℝ) with hUfin_g
  set S0fin_g : ℝ := ∑' s : ℕ, if 1 ≤ s ∧ Squarefree s
        then |(μ s : ℝ)| / (g s : ℝ) ^ 2
        else 0 with hS0fin_g
  set Sijfin_g : ℕ → ℝ := fun N ↦ ∑' s : ℕ, if ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < s ∧ Squarefree s ∧
                    (∀ q, Nat.Prime q → q ∣ s → ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < q)
        then |(μ s : ℝ)| / (g s : ℝ) ^ 2
        else 0 with hSijfin_g
  obtain ⟨C₁, hC₁, N₁, hmertens⟩ := mertens_factor_g δ θ hθ hδ
  obtain ⟨C₂, hC₂, hs0⟩ := exists_tsum_squarefree_abs_moebius_div_g_sq_le
  obtain ⟨C₃, hC₃, N₃, hsij⟩ := exists_tsum_guarded_abs_moebius_div_g_sq_le_div_D₀
  obtain ⟨C₄, hC₄, N₄, hpnt⟩ := exists_primeCountingIoc_div_totient_W_le
  obtain ⟨Nlog, hNlog⟩ := Filter.eventually_atTop.mp (PrimeGaps.R_eventually_ge θ δ hδ.2 2)
  refine ⟨C₁ ^ (k - 1) * C₂ ^ (k ^ 2 - k - 1) * C₃ * C₄, by positivity,
      max (max (max (max N₁ N₃) N₄) (rexp (rexp (rexp 100)) + 1)) (Nlog : ℝ),
      fun N hN lam hlam i j hij ↦ ?_⟩
  simp only [max_le_iff] at hN
  obtain ⟨⟨⟨⟨hN₁, hN₃⟩, hN₄⟩, hNbig⟩, hNlogN⟩ := hN
  have hRge2 : (2 : ℝ) ≤ R := hNlog N (by exact_mod_cast hNlogN)
  have hpm := PrimeGaps.pairMasterG_final R (W N) ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ m lam hlam
    (fun p hp hpD ↦ hp.dvd_W_iff_le_D₀.mpr ((Nat.le_floor_iff' hp.ne_zero).mp hpD)) i j hij
  set ym : ℝ := ⨆ r, |PrimeGaps.ym m lam r|
  set φW : ℝ := (Nat.totient (W N) : ℝ) with hφW
  set Wr : ℝ := (W N : ℝ) with hWr
  set D0 : ℝ := PrimeGaps.D₀ (N : ℝ) with hD0
  set lR : ℝ := Real.log R with hlR
  set lN : ℝ := Real.log (N : ℝ) with hlN
  have hWpos : (0 : ℝ) < Wr := by
    rw [hWr]; exact_mod_cast PrimeGaps.W_pos
  have hφWge1 : (1 : ℝ) ≤ φW := by
    rw [hφW]; exact_mod_cast Nat.totient_pos.mpr PrimeGaps.W_pos
  have hφWpos : (0 : ℝ) < φW := one_pos.trans_le hφWge1
  have hlNpos : (0 : ℝ) < lN := by
    rw [hlN]
    exact Real.log_pos ((Real.one_lt_exp_iff.mpr one_pos).trans
      (exp_one_lt_of_exp_exp_exp_hundred_lt hNbig))
  have hD0gt : (100 : ℝ) < D0 := by rw [hD0]; exact PrimeGaps.lt_D₀_of_le hNbig
  have hlR_nonneg : (0 : ℝ) ≤ lR := by
    rw [hlR]; exact Real.log_nonneg (by linarith only [hRge2])
  have hmert : Ufin_g N ≤ C₁ * (φW / Wr) * lR := hmertens N hN₁
  have hsijN : Sijfin_g N ≤ C₃ / D0 := hsij N hN₃
  have hpntN : (Nat.primeCountingIoc N (2 * N) : ℝ) / φW ≤ C₄ * (N : ℝ) / (φW * lN) := hpnt N hN₄
  have hP_nonneg : (0 : ℝ) ≤ (Nat.primeCountingIoc N (2 * N) : ℝ) / φW :=
    div_nonneg (Nat.cast_nonneg _) hφWpos.le
  have hUfin_nonneg : 0 ≤ Ufin_g N := by
    rw [hUfin_g]
    exact Finset.sum_nonneg fun u _ ↦ div_nonneg (sq_nonneg _) (by positivity)
  have hS0_nonneg : 0 ≤ S0fin_g := by
    rw [hS0fin_g]; exact tsum_nonneg fun s ↦ by split <;> positivity
  have hSij_nonneg : 0 ≤ Sijfin_g N := by
    rw [hSijfin_g]; exact tsum_nonneg fun s ↦ by split <;> positivity
  have hMstar : ym ^ 2 * Ufin_g N ^ (k - 1) * S0fin_g ^ (k ^ 2 - k - 1) * Sijfin_g N ≤
      ym ^ 2 * (C₁ * (φW / Wr) * lR) ^ (k - 1) * C₂ ^ (k ^ 2 - k - 1) * (C₃ / D0) := by
    have h1 : ym ^ 2 * Ufin_g N ^ (k - 1) ≤ ym ^ 2 * (C₁ * (φW / Wr) * lR) ^ (k - 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hUfin_nonneg hmert _) (by positivity)
    exact mul_le_mul (mul_le_mul h1 (pow_le_pow_left₀ hS0_nonneg hs0 _)
      (pow_nonneg hS0_nonneg _) (by positivity)) hsijN hSij_nonneg (by positivity)
  have hMstar_nonneg : (0 : ℝ) ≤ ym ^ 2 * (C₁ * (φW / Wr) * lR) ^ (k - 1) *
      C₂ ^ (k ^ 2 - k - 1) * (C₃ / D0) := by positivity
  refine le_trans (mul_le_mul_of_nonneg_left (hpm.trans hMstar) hP_nonneg) ?_
  refine le_trans (mul_le_mul_of_nonneg_right hpntN hMstar_nonneg) ?_
  have hexpand : (C₁ * (φW / Wr) * lR) ^ (k - 1) =
      C₁ ^ (k - 1) * φW ^ (k - 1) * lR ^ (k - 1) / Wr ^ (k - 1) := by
    rw [mul_pow, mul_pow, div_pow]
    field_simp
  rw [hexpand]
  have hexp : φW ^ (k - 1) ≤ φW ^ (k - 2) * φW := by
    rcases Nat.lt_or_ge k 2 with hk | hk
    · rw [show k - 1 = 0 by omega, show k - 2 = 0 by omega]; simpa using hφWge1
    · rw [show k - 1 = k - 2 + 1 by omega, pow_succ]
  have hden_pos : (0 : ℝ) < φW * lN := by positivity
  have hRden_pos : (0 : ℝ) < Wr ^ (k - 1) * D0 * lN := by positivity
  rw [div_mul_eq_mul_div, div_le_div_iff₀ hden_pos hRden_pos]
  have hKnn : (0 : ℝ) ≤ C₁ ^ (k - 1) * C₂ ^ (k ^ 2 - k - 1) * C₃ * C₄ * ym ^ 2 *
      lR ^ (k - 1) * (N : ℝ) := by positivity
  set K : ℝ := C₁ ^ (k - 1) * C₂ ^ (k ^ 2 - k - 1) * C₃ * C₄ * ym ^ 2 *
      lR ^ (k - 1) * (N : ℝ) with hKdef
  have hLHS_eq : C₄ * (N : ℝ) *
          (ym ^ 2 * (C₁ ^ (k - 1) * φW ^ (k - 1) * lR ^ (k - 1) / Wr ^ (k - 1)) *
            C₂ ^ (k ^ 2 - k - 1) * (C₃ / D0)) * (Wr ^ (k - 1) * D0 * lN) =
        K * φW ^ (k - 1) * lN := by
    rw [hKdef]; field_simp
  have hRHS_eq : C₁ ^ (k - 1) * C₂ ^ (k ^ 2 - k - 1) * C₃ * C₄ * ym ^ 2 * φW ^ (k - 2) * (N : ℝ) *
          lR ^ (k - 1) * (φW * lN) = K * (φW ^ (k - 2) * φW) * lN := by
    rw [hKdef]; ring
  rw [hLHS_eq, hRHS_eq]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hKnn) hlNpos.le

end PrimeGaps
