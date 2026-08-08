/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Gap246.Sieve.Certificate.Hypothesis
public import PrimeGapsTheory.Gap246.Endgame.Mollify
public import PrimeGapsTheory.Gap246.Endgame.ThetaBV
public import PrimeGapsTheory.Gap246.Endgame.Witness
public import PrimeGapsTheory.Gap246.Tuple.H50

import PrimeGapsTheory.Tactic.PaperTag


/-!
# The bound H₁ ≤ 246

The enlarged sieve witness gives DHL[50, 2] for the admissible tuple `H50`, hence
infinitely many consecutive prime gaps of size at most 246.

## Main results

* `thm_dhl`: Infinitely many translates of an admissible 50-tuple contain two primes.
* `thm_main`: Infinitely many consecutive prime gaps are at most 246.
-/

@[expose] public section

open PrimeGaps
open MeasureTheory Filter Finset
open scoped PrimeGaps BigOperators

namespace Gaps246

/-- Every admissible 50-tuple has infinitely many translates containing at least two primes. -/
@[pg_tag "bg246" "thm_dhl"]
theorem thm_dhl (hBV : BombieriVinogradov) (hCert : PrimeGaps.ExistsEpsCert 50)
    (h : Fin 50 → ℕ) (hmono : StrictMono h)
    (hadm : Finset.Admissible (Finset.image h Finset.univ)) :
    {n : ℕ | 2 ≤ #{i : Fin 50 | (n + h i).Prime}}.Infinite := by
  obtain @⟨ε, hε0, hε1, ct⟩ := hCert
  have hεR : (0 : ℝ) ≤ (ε : ℝ) := by exact_mod_cast hε0
  have hε1R : (ε : ℝ) ≤ 1 := by exact_mod_cast hε1
  have hadmG : GPYSieveS1.IsAdmissible h := ⟨hmono, hadm⟩
  let Q := PrimeGaps.gaps246CertificateRayleigh hε0 hε1 ct
  have hQ : 4 < Q := PrimeGaps.gaps246CertificateRayleigh_gt_four hε0 hε1 ct
  obtain ⟨θ, hθhalf, hθthr, hθε, hLDθ⟩ := lem_theta_bv hBV (ε : ℝ) Q hεR hε1R hQ
  have hθ0 : 0 < θ := one_div_pos.mp
    (lt_trans (by linarith : (0 : ℝ) < 1 + (ε : ℝ)) hθε)
  have hθIoo : θ ∈ Set.Ioo (0 : ℝ) 1 := ⟨hθ0, by linarith⟩
  obtain ⟨F, hF, hFsupp, δ, hδ, _, hwit⟩ := lem_mollify hε0 hε1 ct θ hθthr hθε
  exact Gaps246.prop_witness (by norm_num) h hadmG (ε : ℝ) hεR hε1R F hF hFsupp
    θ δ hθIoo hθhalf hLDθ hδ hθε (ρ := 1) le_rfl (by simpa using hwit)

/-- **`thm_main`** (Polymath8b record): infinitely many `n` with `p_{n+1} − p_n ≤ 246`.

The certificate hypothesis supplies the enlarged-simplex witness, and Bombieri--Vinogradov
supplies the required distribution level. The conclusion improves the bound `600` to `246`. -/
@[pg_tag "bg246" "thm_main"]
theorem thm_main (hBV : BombieriVinogradov) (hCert : PrimeGaps.ExistsEpsCert 50) :
    ∃ᶠ m in Filter.atTop, Nat.nth Nat.Prime (m + 1) - Nat.nth Nat.Prime m ≤ 246 := by
  set h : Fin 50 → ℕ := ⇑(H50.orderEmbOfFin card_H50) with hh
  have himg : Finset.image h Finset.univ = H50 := H50.image_orderEmbOfFin_univ card_H50
  have hmono : StrictMono h := (H50.orderEmbOfFin card_H50).strictMono
  have hinj : Function.Injective h := hmono.injective
  have hadm : Finset.Admissible (Finset.image h Finset.univ) := by rw [himg]; exact admissible_H50
  have hInf : {n : ℕ | 2 ≤ #{i : Fin 50 | (n + h i).Prime}}.Infinite :=
    thm_dhl hBV hCert h hmono hadm
  have hfreq : ∃ᶠ n' in Filter.atTop,
      ContainsAtLeastPrimes n' (Finset.image h Finset.univ).diameter 2 := by
    haveI : Nonempty (Fin 50) := ⟨⟨0, by norm_num⟩⟩
    set H := Finset.image h Finset.univ with hHdef
    have hHne : H.Nonempty := Finset.univ_nonempty.image h
    set mn := H.min' hHne with hmndef
    set mx := H.max' hHne with hmxdef
    have hmnmx : mn ≤ mx := Finset.min'_le_max' H hHne
    have hdiam : H.diameter = mx - mn := Finset.diameter_eq_max_sub_min hHne
    rw [Filter.frequently_atTop]
    intro M
    obtain ⟨n, hnmem, hnM⟩ := hInf.exists_gt M
    have hrle : 2 ≤ #{i : Fin 50 | (n + h i).Prime} := hnmem
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
  have hdiam246 : (Finset.image h Finset.univ).diameter = 246 := by
    rw [himg]; exact diameter_H50
  rw [hdiam246] at hfreq
  have hfinal := frequently_prime_gap_le_of_frequently_interval 2 246 (by norm_num) hfreq
  simpa using hfinal

end Gaps246

open Nat

theorem bombieriVinogradov_and_existsEpsCert50_imply_nth_prime_gap_le_246 :
    BombieriVinogradov → PrimeGaps.ExistsEpsCert 50 →
    ∀ n₀ : ℕ, ∃ n ≥ n₀, (n + 1).nth Nat.Prime ≤ n.nth Nat.Prime + 246 := by
  rintro hBV hCert n₀
  have := Gaps246.thm_main hBV hCert
  rw [frequently_atTop] at this
  obtain ⟨n, hn₀, hn⟩ := this n₀
  grind

theorem bombieriVinogradov_and_existsEpsCert50_imply_prime_gap_le_246 :
    BombieriVinogradov → PrimeGaps.ExistsEpsCert 50 →
    ∀ n₀ : ℕ, ∃ p q : ℕ, n₀ ≤ p ∧ p < q ∧ p.Prime ∧ q.Prime ∧ q ≤ p + 246 := by
  rintro hBV hCert n₀
  have := bombieriVinogradov_and_existsEpsCert50_imply_nth_prime_gap_le_246 hBV hCert
  obtain ⟨n, hn₀, hn⟩ := this n₀
  refine ⟨n.nth Nat.Prime, (n + 1).nth Nat.Prime, ?_, ?_, prime_nth_prime _, prime_nth_prime _, hn⟩
  · grw [← add_two_le_nth_prime, ← hn₀]
    grind
  · exact nth_strictMono infinite_setOfPred_prime <| by grind
