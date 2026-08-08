/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.NumberTheory.Compatibility
public import PrimeGapsTheory.Auxiliary.Floor
public import PrimeGapsTheory.Endgame.MainProp
public import PrimeGapsTheory.Endgame.ManyPrimes
public import PrimeGapsTheory.Variational.MkApprox

import PrimeGapsTheory.Tactic.PaperTag

/-!
# The bounded-gaps endgame

The final deduction of a bounded prime-gap theorem from the sieve and variational estimates.

## Main results

* `lem_main_conclusion`: Infinitely many translates of an admissible tuple contain the prescribed
  number of primes.
* `lem_liminf_statement`: A bound for the lower limit of consecutive prime gaps.
* `thm_main`: Infinitely many consecutive prime gaps are at most 600.
-/

@[expose] public section
open MeasureTheory Filter Finset
open scoped PrimeGaps BigOperators

namespace PrimeGaps

/-- If infinitely many `n` have at least `r` primes among the `n + h i`, then arbitrarily large
windows of length `(Finset.image h Finset.univ).diameter` contain at least `r` primes. -/
theorem frequently_containsAtLeast_of_infinite {k : ℕ} (hk : 1 ≤ k) (h : Fin k → ℕ)
    (hinj : Function.Injective h) (r : ℕ)
    (hInf : {n : ℕ | r ≤ #{i : Fin k | (n + h i).Prime}}.Infinite) :
    ∃ᶠ n' in atTop, ContainsAtLeastPrimes n' (Finset.image h Finset.univ).diameter r := by
  haveI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  set H := Finset.image h Finset.univ with hHdef
  have hHne : H.Nonempty := Finset.univ_nonempty.image h
  set mn := H.min' hHne with hmndef
  set mx := H.max' hHne with hmxdef
  have hmnmx : mn ≤ mx := Finset.min'_le_max' H hHne
  have hdiam : H.diameter = mx - mn := diameter_eq_max_sub_min hHne
  rw [Filter.frequently_atTop]
  intro M
  obtain ⟨n, hnmem, hnM⟩ := hInf.exists_gt M
  have hrle : r ≤ #{i : Fin k | (n + h i).Prime} := hnmem
  refine ⟨n + mn, by omega, le_trans hrle ?_⟩
  apply Finset.card_le_card_of_injOn (fun i ↦ n + h i)
  · intro i hi
    rw [Finset.mem_coe, Finset.mem_filter] at hi
    have hiH : h i ∈ H := Finset.mem_image_of_mem h (Finset.mem_univ i)
    have h1 : mn ≤ h i := Finset.min'_le H (h i) hiH
    have h2 : h i ≤ mx := Finset.le_max' H (h i) hiH
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, ?_⟩, hi.2⟩
    rw [hdiam]; omega
  · intro i _ j _ hij
    have hij' : n + h i = n + h j := hij
    exact hinj (by omega)

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- Assuming `BombieriVinogradov` and `θ < 1 / 2`, an admissible tuple `h` has infinitely many
translates containing at least `r θ k = ⌈θ * M k / 2⌉₊` primes among the `n + h i`. -/
@[pg_tag "bg246" "lem_main_conclusion", pg_tag "bg246" "prop_explicit"]
theorem lem_main_conclusion {k : ℕ} (hk : 2 ≤ k) (h : Fin k → ℕ) (hadm : GPYSieveS1.IsAdmissible h)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ : θ < 1 / 2)
    (hBV : BombieriVinogradov) :
    {n : ℕ | PrimeGaps.r θ k ≤ #{i : Fin k | (n + h i).Prime}}.Infinite := by
  classical
  change {n : ℕ | ⌈θ * PrimeGaps.M k / 2⌉₊ ≤ #{i : Fin k | (n + h i).Prime}}.Infinite
  have hLD : Nat.HasLevelOfDistribution Set.univ θ 1 := hBV.hasLevelOfDistribution hθ
  have hadmF : Finset.Admissible (Finset.image h Finset.univ) := hadm.2
  have hMpos : 0 < PrimeGaps.M k := M_pos_of_ne_zero (by omega)
  have hxpos : 0 < θ * PrimeGaps.M k / 2 := div_pos (mul_pos hθ0 hMpos) (by norm_num)
  have hrk_pos : 0 < ⌈θ * PrimeGaps.M k / 2⌉₊ := Nat.ceil_pos.mpr hxpos
  have hrk_lo : (⌈θ * PrimeGaps.M k / 2⌉₊ : ℝ) - 1 < θ * PrimeGaps.M k / 2 := by
    linarith [Nat.ceil_lt_add_one hxpos.le]
  have hrk_hi : θ * PrimeGaps.M k / 2 ≤ (⌈θ * PrimeGaps.M k / 2⌉₊ : ℝ) := Nat.le_ceil _
  obtain ⟨ε₀, hε₀pos, hfloor⟩ :=
    lem_floor_rho (θ * PrimeGaps.M k / 2) ⌈θ * PrimeGaps.M k / 2⌉₊ hrk_pos hrk_lo hrk_hi
  set ε : ℝ := min ε₀ (θ * PrimeGaps.M k / 2) / 2 with hεdef
  have hminpos : 0 < min ε₀ (θ * PrimeGaps.M k / 2) := lt_min hε₀pos hxpos
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hεltε₀ : ε < ε₀ := by
    rw [hεdef]; linarith [min_le_left ε₀ (θ * PrimeGaps.M k / 2)]
  have hεltx : ε < θ * PrimeGaps.M k / 2 := by
    rw [hεdef]; linarith [min_le_right ε₀ (θ * PrimeGaps.M k / 2)]
  set ρ : ℝ := θ * PrimeGaps.M k / 2 - ε with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; linarith
  obtain ⟨F, hCD, htsupp, hmem, hIpos, δ, hδpos, hwit_choose⟩ :=
    maynard_smooth_witness_ineq k hk θ ⟨hθ0, by linarith⟩ ε hεpos ρ hρdef
  have hsupp : Function.support F ⊆ 𝓡 k := (subset_tsupport F).trans htsupp
  have hsumJ_nonneg : 0 ≤ ∑ m, PrimeGaps.J m (hmem.toLp F) :=
    Finset.sum_nonneg (fun m _ ↦ by rw [J_eq_normSq]; positivity)
  have hδθ : δ < θ / 2 := by
    nlinarith [mul_pos hρpos hIpos, hsumJ_nonneg, hwit_choose]
  obtain ⟨N₀, HS⟩ := PrimeGaps.MainProp.lem_S_positive hk h hadm F hCD hsupp θ δ hθ0 hθ hδpos hδθ
      ρ hρpos hLD hwit_choose
  choose v₀ hvalid using hadmF.exists_zmod_gcd_eq_one
  have hposSupported : ∀ᶠ N in atTop, ∃ l : (Fin k → ℕ) →₀ ℝ, l.HasPermissibleSupport ⌊R⌋₊
          (W N) ∧
        0 < PrimeGaps.S₂ h l N (v₀ N) - ρ * PrimeGaps.S₁ h l N (v₀ N) := by
    rw [Filter.eventually_atTop]
    refine ⟨⌈N₀⌉₊, fun N hN ↦ ?_⟩
    have hN₀le : N₀ ≤ (N : ℝ) := le_trans (Nat.le_ceil N₀) (by exact_mod_cast hN)
    exact ⟨PrimeGaps.l₀ (R) (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp)),
      PrimeGaps.hasPermissibleSupport_l₀,
      HS N hN₀le (v₀ N) (hvalid N)⟩
  have hpos : ∀ᶠ N in atTop, ∃ l : (Fin k → ℕ) →₀ ℝ,
        0 < PrimeGaps.S₂ h l N (v₀ N) - ρ * PrimeGaps.S₁ h l N (v₀ N) :=
    hposSupported.mono fun _ ⟨l, _, hl⟩ ↦ ⟨l, hl⟩
  have hInfInt := PrimeGaps.maynardTao_endgame h ρ v₀ hpos
  have hnf : ⌊ρ + 1⌋₊ = ⌈θ * PrimeGaps.M k / 2⌉₊ := hfloor ε hεpos hεltε₀
  have hle1 : (⌈θ * PrimeGaps.M k / 2⌉₊ : ℝ) ≤ ρ + 1 := by
    rw [← hnf]; exact Nat.floor_le (by linarith)
  have hlt1 : ρ + 1 < (⌈θ * PrimeGaps.M k / 2⌉₊ : ℝ) + 1 := by
    have := Nat.lt_floor_add_one (ρ + 1); rw [hnf] at this; exact_mod_cast this
  have hif : ⌊ρ + 1⌋ = (⌈θ * PrimeGaps.M k / 2⌉₊ : ℤ) := by
    rw [Int.floor_eq_iff]
    refine ⟨by push_cast; linarith, by push_cast; linarith⟩
  have hset : {n : ℕ | ⌈θ * PrimeGaps.M k / 2⌉₊ ≤ #{i : Fin k | (n + h i).Prime}} =
      {n : ℕ | ⌊ρ + 1⌋ ≤ (#{i : Fin k | (n + h i).Prime} : ℤ)} := by
    ext n
    simp only [Set.mem_ofPred_eq, hif, Nat.cast_le]
  rw [hset]; exact hInfInt

/-- **`lem_liminf_statement`**.

For an admissible tuple `h` and `θ < 1/2`, there are infinitely many `m` with
`p_{m + r_k − 1} − p_m ≤ diam 𝓗`, with primes indexed by `Nat.nth Nat.Prime`
(matching `lem_many_primes_implies_small_gaps`).

From `lem_main_conclusion`, the primes among `n + h i` lie in `[n + min 𝓗, n + max 𝓗]`
(an interval of length `diam 𝓗`) and are distinct, giving arbitrarily large windows with `r_k`
primes; `lem_many_primes_implies_small_gaps` then yields the bound. -/
@[pg_tag "bg246" "lem_liminf_statement"]
theorem lem_liminf_statement {k : ℕ} (hk : 2 ≤ k) (h : Fin k → ℕ) (hadm : GPYSieveS1.IsAdmissible h)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ : θ < 1 / 2)
    (hBV : BombieriVinogradov) :
    ∃ᶠ m in Filter.atTop, Nat.nth Nat.Prime (m + (PrimeGaps.r θ k - 1)) - Nat.nth Nat.Prime m ≤
        (Finset.image h Finset.univ).diameter := by
  have hinj : Function.Injective h := hadm.1.injective
  have hInf := lem_main_conclusion hk h hadm θ hθ0 hθ hBV
  have hMpos : 0 < PrimeGaps.M k := M_pos_of_ne_zero (by omega)
  have hxpos : 0 < θ * PrimeGaps.M k / 2 := div_pos (mul_pos hθ0 hMpos) (by norm_num)
  have hrk1 : 1 ≤ PrimeGaps.r θ k := Nat.ceil_pos.mpr hxpos
  have hfreq := frequently_containsAtLeast_of_infinite (by omega) h hinj (PrimeGaps.r θ k) hInf
  exact frequently_prime_gap_le_of_frequently_interval (PrimeGaps.r θ k)
    (Finset.image h Finset.univ).diameter hrk1 hfreq

/-- Assuming `BombieriVinogradov`, infinitely many consecutive prime gaps are at most `600`:
`p_{m+1} - p_m ≤ 600` for frequently many `m`, via the admissible `105`-tuple `H105`. -/
@[pg_tag "bg246" "thm_main_600"]
theorem thm_main (hBV : BombieriVinogradov) :
    ∃ᶠ m in Filter.atTop, Nat.nth Nat.Prime (m + 1) - Nat.nth Nat.Prime m ≤ 600 := by
  set h : Fin 105 → ℕ := ⇑(PrimeGaps.H105.orderEmbOfFin PrimeGaps.card_H105) with hh
  have himg : Finset.image h Finset.univ = PrimeGaps.H105 :=
    PrimeGaps.H105.image_orderEmbOfFin_univ PrimeGaps.card_H105
  have hmono : StrictMono h := (PrimeGaps.H105.orderEmbOfFin PrimeGaps.card_H105).strictMono
  have hinj : Function.Injective h := hmono.injective
  have hadm : GPYSieveS1.IsAdmissible h :=
    ⟨hmono, by rw [himg]; exact PrimeGaps.admissible_H105⟩
  have hMpos : 0 < PrimeGaps.M 105 := lt_trans (by norm_num) four_lt_M_verified
  have hMne : PrimeGaps.M 105 ≠ 0 := hMpos.ne'
  set θ : ℝ := 1 / 4 + 1 / PrimeGaps.M 105 with hθdef
  have hθ0 : 0 < θ := by rw [hθdef]; positivity
  have hθ : θ < 1 / 2 := by
    rw [hθdef]
    have hlt : 1 / PrimeGaps.M 105 < 1 / 4 :=
      one_div_lt_one_div_of_lt (by norm_num) four_lt_M_verified
    linarith
  have hx1 : (1 : ℝ) < θ * PrimeGaps.M 105 / 2 := by
    have hexp : θ * PrimeGaps.M 105 / 2 = PrimeGaps.M 105 / 8 + 1 / 2 := by
      rw [hθdef]; field_simp; ring
    rw [hexp]; linarith [four_lt_M_verified]
  have hrk2 : 1 < PrimeGaps.r θ 105 := Nat.lt_ceil.mpr (by exact_mod_cast hx1)
  have hInf := lem_main_conclusion (k := 105) (by norm_num) h hadm θ hθ0 hθ hBV
  have hfreq :=
    frequently_containsAtLeast_of_infinite (by norm_num) h hinj (PrimeGaps.r θ 105) hInf
  have hdiam600 : (Finset.image h Finset.univ).diameter = 600 := by
    rw [himg]; exact PrimeGaps.diameter_H105
  rw [hdiam600] at hfreq
  have hfreq2 : ∃ᶠ n' in atTop, ContainsAtLeastPrimes n' 600 2 :=
    hfreq.mono (fun n' hcp ↦ le_trans (by omega : 2 ≤ PrimeGaps.r θ 105) hcp)
  have hfreqgap := frequently_prime_gap_le_of_frequently_interval 2 600 (by norm_num) hfreq2
  simpa using hfreqgap

end PrimeGaps

open Nat

/-- `BombieriVinogradov` implies arbitrarily large `n` with `p_{n+1} ≤ p_n + 600`. -/
theorem bombieriVinogradov_implies_nth_prime_gap_le_600 :
    BombieriVinogradov → ∀ n₀ : ℕ, ∃ n ≥ n₀, (n + 1).nth Nat.Prime ≤ n.nth Nat.Prime + 600 := by
  rintro hBV n₀
  have := PrimeGaps.thm_main hBV
  rw [frequently_atTop] at this
  obtain ⟨n, hn₀, hn⟩ := this n₀
  grind

/-- `BombieriVinogradov` implies that beyond any `n₀` there are primes `p < q ≤ p + 600`. -/
theorem bombieriVinogradov_implies_prime_gap_le_600 :
    BombieriVinogradov → ∀ n₀ : ℕ, ∃ p q : ℕ, n₀ ≤ p ∧ p < q ∧ p.Prime ∧ q.Prime ∧ q ≤ p + 600 := by
  rintro hBV n₀
  have := bombieriVinogradov_implies_nth_prime_gap_le_600 hBV
  obtain ⟨n, hn₀, hn⟩ := this n₀
  refine ⟨n.nth Nat.Prime, (n + 1).nth Nat.Prime, ?_, ?_, prime_nth_prime _, prime_nth_prime _, hn⟩
  · grw [← add_two_le_nth_prime, ← hn₀]
    grind
  · exact nth_strictMono infinite_setOfPred_prime <| by grind
