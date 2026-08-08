/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.S2m.SijD0.GTail

/-!
# The Mertens factor for g

The multiplicative function `moebiusSqDivGMaynard` and the Mertens-type factor it
produces.

## Main results

* `convolution_A`
* `mertens_core`
* `mertens_factor_g`
-/

@[expose] public section

open scoped ArithmeticFunction.Moebius

open scoped ArithmeticFunction.detotient

section MertensFactorGPort
open ArithmeticFunction

namespace PrimeGaps

/-- The arithmetic function `d ↦ μ(d)² / g d`. -/
noncomputable def moebiusSqDivGMaynard : ArithmeticFunction ℝ :=
  ⟨fun d ↦ if d = 0 then 0 else (μ d : ℝ) ^ 2 / (g d : ℝ), by simp⟩

/-- Value on a nonzero argument: `moebiusSqDivGMaynard d = μ(d)² / g d`. -/
lemma moebiusSqDivGMaynard_apply (d : ℕ) (hd : d ≠ 0) :
    moebiusSqDivGMaynard d = (μ d : ℝ) ^ 2 / (g d : ℝ) := by
  simp [moebiusSqDivGMaynard, hd]

/-- `moebiusSqDivGMaynard` is multiplicative, `μ` and `g` both being so. -/
lemma moebiusSqDivGMaynard_mult : moebiusSqDivGMaynard.IsMultiplicative := by
  refine ⟨by simp [moebiusSqDivGMaynard], ?_⟩
  intro m n hmn
  rcases eq_or_ne m 0 with rfl | hm
  · simp only [Nat.coprime_zero_left] at hmn; subst hmn; simp [moebiusSqDivGMaynard]
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [Nat.coprime_zero_right] at hmn; subst hmn; simp [moebiusSqDivGMaynard]
  rw [moebiusSqDivGMaynard_apply _ (Nat.mul_ne_zero hm hn), moebiusSqDivGMaynard_apply _ hm,
    moebiusSqDivGMaynard_apply _ hn,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn,
    ArithmeticFunction.isMultiplicative_detotient.map_mul_of_coprime hmn]
  push_cast
  ring

/-- For `u` squarefree and odd, `∑ d ∈ u.divisors, μ(d)²/g d = φ u / g u`. -/
lemma convolution_A (u : ℕ) (hu : Squarefree u) (hodd : Odd u) :
    ∑ d ∈ u.divisors, (μ d : ℝ) ^ 2 / (g d : ℝ) =
      (Nat.totient u : ℝ) / (g u : ℝ) := by
  have hsum : ∀ d ∈ u.divisors, (μ d : ℝ) ^ 2 / (g d : ℝ) = moebiusSqDivGMaynard d :=
    fun d hd ↦ (moebiusSqDivGMaynard_apply d (Nat.pos_of_mem_divisors hd).ne').symm
  rw [Finset.sum_congr rfl hsum,
    ← moebiusSqDivGMaynard_mult.prodPrimeFactors_one_add_of_squarefree hu]
  have hfac : ∀ p ∈ u.primeFactors,
      (1 : ℝ) + moebiusSqDivGMaynard p = ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) < (p : ℝ) := by
      have := Nat.odd_iff.mp (hodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))
      have := hpp.two_le
      exact_mod_cast (by omega : 2 < p)
    rw [moebiusSqDivGMaynard_apply p hpp.ne_zero, ArithmeticFunction.moebius_apply_prime hpp,
      detotient_prime hpp, Nat.cast_sub hpp.two_le]
    have hne : (p : ℝ) - 2 ≠ 0 := by linarith
    push_cast
    field_simp
    ring
  rw [Finset.prod_congr rfl hfac, Finset.prod_div_distrib,
    ← PrimeGaps.totient_eq_prod_sub_one u (Nat.pos_of_ne_zero hu.ne_zero) hu,
    ← ArithmeticFunction.coe_detotient_squarefree_eq_prod (R := ℝ) hu]
end PrimeGaps

namespace Nat

/-- For `d ∣ u` with `u` squarefree, `φ u = φ d * φ (u / d)`. -/
lemma tot_split (d u : ℕ) (hdu : d ∣ u) (hu : Squarefree u) (hd1 : 1 ≤ d) :
    (Nat.totient u : ℝ) = Nat.totient d * Nat.totient (u / d) := by
  obtain ⟨m, rfl⟩ := hdu
  rw [Nat.mul_div_cancel_left _ (by omega : 0 < d),
    Nat.totient_mul (Nat.coprime_of_squarefree_mul hu)]
  exact Nat.cast_mul _ _

end Nat

namespace PrimeGaps

/-- Writing `u = d * m`, the inner sum `∑_{u ≤ R, d ∣ u, (u,W)=1} μ(u)²/φ(u)` is at most
`(1/φ d) * MaynardOffDiagonal.sumA (d * W) R`. -/
lemma inner_totient_sum_le_sumA (d W : ℕ) (R : ℝ) (hd1 : 1 ≤ d) :
    ∑ u ∈ {u ∈ (Finset.Icc 1 ⌊R⌋₊) | d ∣ u ∧ u.Coprime W}, (μ u : ℝ) ^ 2 / (Nat.totient u : ℝ) ≤
      (1 / (Nat.totient d : ℝ)) * MaynardOffDiagonal.sumA (d * W) R := by
  set M := ⌊R⌋₊
  have hφd : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < d)
  set T := {u ∈ (Finset.Icc 1 M) | d ∣ u ∧ u.Coprime W} with hT
  set T' := T.filter (fun u ↦ Squarefree u) with hT'
  have hstep1 : ∑ u ∈ T, (μ u : ℝ) ^ 2 / (Nat.totient u : ℝ) =
      ∑ u ∈ T', (μ u : ℝ) ^ 2 / (Nat.totient u : ℝ) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) fun u huT huT' ↦ ?_).symm
    simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree
      fun h ↦ huT' (Finset.mem_filter.mpr ⟨huT, h⟩)]
  have hval : ∀ u ∈ T', (μ u : ℝ) ^ 2 / (Nat.totient u : ℝ) =
      (1 / (Nat.totient d : ℝ)) * (1 / (Nat.totient (u / d) : ℝ)) := by
    intro u hu
    rw [hT', Finset.mem_filter, hT, Finset.mem_filter] at hu
    obtain ⟨⟨-, hdu, -⟩, hsf⟩ := hu
    have hmu : (μ u : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
    rw [hmu, Nat.tot_split d u hdu hsf hd1, one_div_mul_one_div]
  have hinj : Set.InjOn (fun u ↦ u / d) (T' : Set ℕ) := by
    intro a ha b hb hab
    simp only [hT', Finset.coe_filter, Set.mem_ofPred_eq, hT, Finset.mem_filter] at ha hb
    obtain ⟨⟨-, ⟨a', rfl⟩, -⟩, -⟩ := ha
    obtain ⟨⟨-, ⟨b', rfl⟩, -⟩, -⟩ := hb
    simp only [Nat.mul_div_cancel_left _ (by omega : 0 < d)] at hab
    rw [hab]
  have himg : ∑ u ∈ T', (1 / (Nat.totient (u / d) : ℝ)) =
      ∑ m ∈ T'.image (fun u ↦ u / d), (1 / (Nat.totient m : ℝ)) :=
    (Finset.sum_image (f := fun m ↦ 1 / (Nat.totient m : ℝ))
      fun a ha b hb ↦ hinj (by simpa using ha) (by simpa using hb)).symm
  rw [hstep1, Finset.sum_congr rfl hval, ← Finset.mul_sum, himg]
  have hsub : T'.image (fun u ↦ u / d) ⊆ MaynardOffDiagonal.Sset (d * W) R := by
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨u, huT', rfl⟩ := hm
    rw [hT', Finset.mem_filter, hT, Finset.mem_filter, Finset.mem_Icc] at huT'
    obtain ⟨⟨⟨hu1, huM⟩, ⟨m', rfl⟩, hcop⟩, hsf⟩ := huT'
    rw [Nat.mul_div_cancel_left _ (by omega : 0 < d)]
    simp only [MaynardOffDiagonal.Sset, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.pos_of_ne_zero (by rintro rfl; simp at hu1),
        (Nat.le_mul_of_pos_left m' (by omega)).trans huM⟩, hsf.of_mul_right,
      (Nat.coprime_of_squarefree_mul hsf).symm.mul_right
        (hcop.coprime_dvd_left (dvd_mul_left m' d))⟩
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  simpa only [MaynardOffDiagonal.sumA] using
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ ↦ by positivity

/-- For `d` squarefree and odd, `μ(d)²/(g d * φ d) ≤ term d`, since `g d ≤ φ d`. -/
lemma outerE_pointwise (d : ℕ) (hd : Squarefree d) (hodd : Odd d) :
    (μ d : ℝ) ^ 2 / ((g d : ℝ) * (Nat.totient d : ℝ)) ≤
      PrimeGaps.term d := by
  simp only [PrimeGaps.term, if_pos hodd]
  have hg : (0 : ℝ) < g d := by exact_mod_cast detotient_pos_of_odd hodd
  have hgφ : (g d : ℝ) ≤ (Nat.totient d : ℝ) := by
    rw [ArithmeticFunction.coe_detotient_squarefree_eq_prod (R := ℝ) hd,
      PrimeGaps.totient_eq_prod_sub_one d (Nat.pos_of_ne_zero hd.ne_zero) hd]
    refine Finset.prod_le_prod (fun p hp ↦ ?_) (fun p hp ↦ ?_) <;>
      · have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        linarith
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)

/-- For odd `u`, `μ(u)²/g u = ∑ d ∈ u.divisors, (μ(d)²/g d) * (μ(u)²/φ u)`. -/
lemma ufin_pointwise (u : ℕ) (hodd : Odd u) :
    (μ u : ℝ) ^ 2 / (g u : ℝ) = ∑ d ∈ u.divisors,
          (μ d : ℝ) ^ 2 / (g d : ℝ) *
            ((μ u : ℝ) ^ 2 / (Nat.totient u : ℝ)) := by
  by_cases hu : Squarefree u
  · have hmu : (μ u : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hu
    have hg : (0 : ℝ) < g u := by exact_mod_cast detotient_pos_of_odd hodd
    have hφ : (0 : ℝ) < Nat.totient u := by
      exact_mod_cast Nat.totient_pos.mpr hu.ne_zero.bot_lt
    rw [← Finset.sum_mul, convolution_A u hu hodd, hmu]
    field_simp
  · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hu]
end PrimeGaps

namespace Nat

/-- Exchange of summation between `∑_{u ≤ M, (u,W)=1} ∑_{d ∣ u}` and `∑_{d ≤ M} ∑_{u ≤ M, d ∣ u,
(u,W)=1}`. -/
lemma swap_coprime (M W : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ u ∈ {u ∈ (Finset.Icc 1 M) | u.Coprime W}, ∑ d ∈ u.divisors, f u d =
    ∑ d ∈ Finset.Icc 1 M,
        ∑ u ∈ {u ∈ (Finset.Icc 1 M) | d ∣ u ∧ u.Coprime W}, f u d := by
  refine Finset.sum_comm' fun u d ↦ ?_
  simp only [Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨⟨hu1, huM⟩, hcop⟩, hdu, -⟩
    exact ⟨⟨⟨hu1, huM⟩, hdu, hcop⟩, Nat.pos_of_dvd_of_pos hdu (by omega),
      (Nat.le_of_dvd (by omega) hdu).trans huM⟩
  · rintro ⟨⟨⟨hu1, huM⟩, hdu, hcop⟩, -⟩
    exact ⟨⟨⟨hu1, huM⟩, hcop⟩, hdu, by omega⟩

end Nat

namespace PrimeGaps

/-- For even `W`, `∑_{d ≤ M, (d,W)=1} μ(d)²/(g d * φ d) ≤ ∑' s, term s`. -/
lemma outerE_finite_le (M W : ℕ) (hWeven : 2 ∣ W) :
    ∑ d ∈ {d ∈ (Finset.Icc 1 M) | d.Coprime W},
        (μ d : ℝ) ^ 2 / ((g d : ℝ) * (Nat.totient d : ℝ)) ≤
      ∑' s, PrimeGaps.term s := by
  have hle : ∀ d ∈ {d ∈ (Finset.Icc 1 M) | d.Coprime W},
      (μ d : ℝ) ^ 2 / ((g d : ℝ) * (Nat.totient d : ℝ)) ≤
        PrimeGaps.term d := by
    intro d hd
    obtain ⟨-, hcop⟩ := Finset.mem_filter.mp hd
    have hodd : Odd d := Nat.odd_iff.mpr <| by
      by_contra h
      simpa using Nat.eq_one_of_dvd_coprimes hcop (by omega : 2 ∣ d) hWeven
    by_cases hsf : Squarefree d
    · exact outerE_pointwise d hsf hodd
    · simpa [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf] using
        PrimeGaps.term_nonneg d
  exact (Finset.sum_le_sum hle).trans
    (PrimeGaps.convergent_sum_g.sum_le_tsum _ fun s _ ↦ PrimeGaps.term_nonneg s)
end PrimeGaps

namespace Nat

/-- For coprime `d` and `W`, `φ (d * W) / (d * W) ≤ φ W / W`. -/
lemma totient_ratio_mul_le (d W : ℕ) (hd : 1 ≤ d) (hW : 1 ≤ W) (hcop : Nat.Coprime d W) :
    (Nat.totient (d * W) : ℝ) / (d * W : ℝ) ≤ (Nat.totient W : ℝ) / (W : ℝ) := by
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hφd_le : (Nat.totient d : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.totient_le d
  have hφW_nonneg : (0 : ℝ) ≤ Nat.totient W := by positivity
  rw [Nat.totient_mul hcop, div_le_div_iff₀ (by positivity) hWpos]
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hφd_le (mul_nonneg hφW_nonneg hWpos.le)]

end Nat

namespace PrimeGaps

/-- The `d`-th term of the Mertens double sum is at most
`μ(d)² / (g d · φ(d)) · (c₁ · (φ(W)/W) · log R + c₁)`, and vanishes unless `d` is coprime to `W`.
The inner sum over multiples of `d` coprime to `W` is at most `sumA (d * W) R / φ(d)`, the
hypothesis `hsumA` bounds `sumA (d * W) R`, and `φ(dW)/(dW) ≤ φ(W)/W` removes the `d`. -/
private lemma mertens_divisor_term_le (W : ℕ) (R : ℝ) (hW1 : 1 ≤ W) (hWeven : 2 ∣ W)
    (hR2 : 2 ≤ R) (hWpf : ∀ p ∈ W.primeFactors, (p : ℝ) ≤ R)
    (c₁ : ℝ) (hc₁pos : 0 < c₁)
    (hsumA : ∀ (W' : ℕ) (cutoff : ℝ), 1 ≤ W' → 2 ≤ cutoff →
      (∀ p ∈ W'.primeFactors, (p : ℝ) ≤ cutoff) → MaynardOffDiagonal.sumA W' cutoff ≤
          c₁ * ↑W'.totient / ↑W' * Real.log cutoff + c₁)
    (d : ℕ) (hd : d ∈ Finset.Icc 1 ⌊R⌋₊) :
    (μ d : ℝ) ^ 2 / (g d : ℝ) *
        ∑ u ∈ {u ∈ (Finset.Icc 1 ⌊R⌋₊) | d ∣ u ∧ u.Coprime W},
            (μ u : ℝ) ^ 2 / (Nat.totient u : ℝ) ≤
      (if d.Coprime W then
        (μ d : ℝ) ^ 2 / ((g d : ℝ) * (Nat.totient d : ℝ)) *
          (c₁ * (Nat.totient W / (W : ℝ)) * Real.log R + c₁)
      else 0) := by
  obtain ⟨hd1, hdM⟩ := Finset.mem_Icc.mp hd
  by_cases hdcop : d.Coprime W
  · rw [if_pos hdcop]
    by_cases hdsf : Squarefree d
    · have hmu : (μ d : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hdsf
      have hodd : Odd d := Nat.odd_iff.mpr <| by
        by_contra h
        simpa using Nat.eq_one_of_dvd_coprimes hdcop (by omega : 2 ∣ d) hWeven
      have hφdpos : (0 : ℝ) < Nat.totient d := by
        exact_mod_cast Nat.totient_pos.mpr hdsf.ne_zero.bot_lt
      have hlogR : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
      have hpfDW : ∀ p ∈ (d * W).primeFactors, (p : ℝ) ≤ R := by
        intro p hp
        rw [Nat.primeFactors_mul (by omega) (by omega), Finset.mem_union] at hp
        rcases hp with hpd | hpW
        · calc (p : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.le_of_mem_primeFactors hpd
            _ ≤ (⌊R⌋₊ : ℝ) := by exact_mod_cast hdM
            _ ≤ R := Nat.floor_le (by linarith)
        · exact hWpf p hpW
      have hsA' : MaynardOffDiagonal.sumA (d * W) R ≤
          c₁ * (Nat.totient W / (W : ℝ)) * Real.log R + c₁ := by
        refine (hsumA (d * W) R (Nat.one_le_iff_ne_zero.mpr (by positivity)) hR2 hpfDW).trans ?_
        rw [show c₁ * ↑(d * W).totient / ↑(d * W) =
          c₁ * ((Nat.totient (d * W) : ℝ) / ((d : ℝ) * (W : ℝ))) by push_cast; ring]
        gcongr c₁ * ?_ * Real.log R + c₁
        exact Nat.totient_ratio_mul_le d W hd1 hW1 hdcop
      rw [hmu, show (1 : ℝ) / ((g d : ℝ) * (Nat.totient d : ℝ)) =
        1 / (g d : ℝ) * (1 / (Nat.totient d : ℝ)) from (one_div_mul_one_div _ _).symm, mul_assoc]
      exact mul_le_mul_of_nonneg_left ((inner_totient_sum_le_sumA d W R hd1).trans
        (mul_le_mul_of_nonneg_left hsA' (by positivity))) (by positivity)
    · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hdsf]
  · rw [if_neg hdcop, Finset.filter_eq_empty_iff.mpr fun u _ ⟨hdu, hucop⟩ ↦
      hdcop (hucop.coprime_dvd_left hdu), Finset.sum_empty, mul_zero]

/-- Mertens-type bound for the `g`-weighted sum: given a linear bound `hsumA` on
`MaynardOffDiagonal.sumA`, `∑_{u ≤ ⌊R⌋₊, (u,W)=1} μ(u)²/g u ≤ (∑' s, term s) *
(c₁ * (φ W / W) * log R + c₁)`. -/
lemma mertens_core (W : ℕ) (R : ℝ) (hW1 : 1 ≤ W) (hWeven : 2 ∣ W)
    (hR2 : 2 ≤ R) (hWpf : ∀ p ∈ W.primeFactors, (p : ℝ) ≤ R)
    (c₁ : ℝ) (hc₁pos : 0 < c₁)
    (hsumA : ∀ (W' : ℕ) (cutoff : ℝ), 1 ≤ W' → 2 ≤ cutoff →
      (∀ p ∈ W'.primeFactors, (p : ℝ) ≤ cutoff) → MaynardOffDiagonal.sumA W' cutoff ≤
          c₁ * ↑W'.totient / ↑W' * Real.log cutoff + c₁) :
      (∑ u ∈ {u ∈ (Finset.Icc 1 ⌊R⌋₊) | u.Coprime W},
          (μ u : ℝ) ^ 2 / (g u : ℝ)) ≤ (∑' s, PrimeGaps.term s) *
            (c₁ * (Nat.totient W / (W : ℝ)) * Real.log R + c₁) := by
  set M := ⌊R⌋₊
  have hstep1 : ∑ u ∈ {u ∈ (Finset.Icc 1 M) | u.Coprime W}, (μ u : ℝ) ^ 2 / (g u : ℝ) =
      ∑ u ∈ {u ∈ (Finset.Icc 1 M) | u.Coprime W}, ∑ d ∈ u.divisors,
            (μ d : ℝ) ^ 2 / (g d : ℝ) *
              ((μ u : ℝ) ^ 2 / (Nat.totient u : ℝ)) := by
    refine Finset.sum_congr rfl fun u hu ↦ ufin_pointwise u (Nat.odd_iff.mpr <| by
      obtain ⟨-, hcop⟩ := Finset.mem_filter.mp hu
      by_contra h
      simpa using Nat.eq_one_of_dvd_coprimes hcop (by omega : 2 ∣ u) hWeven)
  rw [hstep1, Nat.swap_coprime M W]
  simp only [← Finset.mul_sum]
  refine (Finset.sum_le_sum fun d hd ↦
    mertens_divisor_term_le W R hW1 hWeven hR2 hWpf c₁ hc₁pos hsumA d hd).trans ?_
  rw [← Finset.sum_filter, ← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right (outerE_finite_le M W hWeven) ?_
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
  have hc₁nn : 0 ≤ c₁ := hc₁pos.le
  positivity

/-- `1 ≤ ∑' s, term s`, from the single term `term 1 = 1`. -/
lemma E_ge_one : (1 : ℝ) ≤ ∑' s, PrimeGaps.term s := by
  have h1 := PrimeGaps.convergent_sum_g.sum_le_tsum {1} fun i _ ↦ PrimeGaps.term_nonneg i
  rwa [Finset.sum_singleton, PrimeGaps.term_one] at h1

/-- `1 ≤ MaynardOffDiagonal.sumA W R` for `R ≥ 2`, from the single index `n = 1`. -/
lemma sumA_ge_one (W : ℕ) (R : ℝ) (hR2 : 2 ≤ R) : (1 : ℝ) ≤ MaynardOffDiagonal.sumA W R := by
  have h1mem : (1 : ℕ) ∈ MaynardOffDiagonal.Sset W R := by
    change (1 : ℕ) ∈ {n ∈ Finset.Icc 1 ⌊R⌋₊ | Squarefree n ∧ n.gcd W = 1}
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_rfl, Nat.le_floor (by exact_mod_cast one_le_two.trans hR2)⟩,
      squarefree_one, by simp⟩
  simpa [MaynardOffDiagonal.sumA] using Finset.single_le_sum
    (f := fun n ↦ 1 / (Nat.totient n : ℝ)) (fun n _ ↦ by positivity) h1mem

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- Eventually in `N`, `∑_{u ≤ ⌊R⌋₊, (u, W N)=1} μ(u)²/g u ≤ C₁ * (φ (W N) / W N) * log R`, the
`g`-analogue of `mertens_factor`. -/
lemma mertens_factor_g (δ θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2)) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ N₁ : ℝ, ∀ N : ℕ, N₁ ≤ (N : ℝ) →
      (∑ u ∈ {u ∈ (Finset.Icc 1 ⌊R⌋₊) | u.Coprime (W N)}, (μ u : ℝ) ^ 2 / (g u : ℝ)) ≤
        C₁ * ((Nat.totient (W N) : ℝ) / (W N : ℝ)) * Real.log R := by
  obtain ⟨-, hθ1⟩ := hθ
  obtain ⟨hδ0, hδθ2⟩ := hδ
  have hexp : 0 < θ / 2 - δ := by linarith
  obtain ⟨C₁m, hC₁m, N₁m, hmf⟩ := mertens_factor δ θ ⟨hδ0, hδθ2, hθ1⟩
  obtain ⟨Na, hNa⟩ := Filter.eventually_atTop.mp (PrimeGaps.R_eventually_ge θ δ hδθ2 2)
  obtain ⟨N₂, -, hN₂⟩ := exists_N0_for_D0_ge_2
  obtain ⟨N₃, -, hN₃⟩ := MaynardOffDiagonal.primorial_D0_primeFactors_le_Rval θ δ hexp
  obtain ⟨c₁, hc₁pos, hsumA_le⟩ := MaynardOffDiagonal.sumA_le_floor
  set Ebig := ∑' s, PrimeGaps.term s with hEdef
  have hEnn : 0 ≤ Ebig := tsum_nonneg PrimeGaps.term_nonneg
  refine ⟨(Ebig + 1) * c₁ * (1 + C₁m), by positivity, ?_⟩
  refine ⟨max (max (Na : ℝ) (N₂ : ℝ)) (max (N₃ : ℝ) N₁m), ?_⟩
  intro N hN
  have hNa' : (Na : ℝ) ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hN₂' : (N₂ : ℝ) ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hN₃' : (N₃ : ℝ) ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hN₁m' : N₁m ≤ (N : ℝ) := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  have hR2 : (2 : ℝ) ≤ R := hNa N (by exact_mod_cast hNa')
  have hW1 : 1 ≤ W N := PrimeGaps.W_pos
  have hWeven : 2 ∣ W N := by
    rw [PrimeGaps.W_eq_primorial_D₀]
    exact MaynardOffDiagonal.prime_dvd_primorial_D0 (N : ℝ) 2 Nat.prime_two
      (hN₂ N (by exact_mod_cast hN₂'))
  have hWpf : ∀ p ∈ (W N).primeFactors, (p : ℝ) ≤ R := by
    intro p hp
    rw [PrimeGaps.W_eq_primorial_D₀] at hp
    simpa [PrimeGaps.sieveTruncation] using hN₃ (N : ℝ) hN₃' p hp
  have hc := mertens_core (W N) R hW1 hWeven hR2 hWpf c₁ hc₁pos hsumA_le
  set φWr : ℝ := (Nat.totient (W N) : ℝ) / (W N : ℝ) with hφWr
  set lR : ℝ := Real.log R
  have hφWnn : 0 ≤ φWr := by rw [hφWr]; positivity
  have hlRnn : 0 ≤ lR := Real.log_nonneg (by linarith)
  have hc₁nn : 0 ≤ c₁ := hc₁pos.le
  have habs : (1 : ℝ) ≤ C₁m * φWr * lR := (sumA_ge_one (W N) R hR2).trans (hmf N hN₁m')
  have hkey : c₁ ≤ c₁ * C₁m * (φWr * lR) := by
    nlinarith [mul_nonneg hc₁nn (sub_nonneg.mpr habs)]
  rw [← hEdef] at hc
  refine hc.trans ?_
  nlinarith [mul_nonneg hEnn (sub_nonneg.mpr hkey), mul_nonneg hc₁nn (mul_nonneg hφWnn hlRnn)]

end PrimeGaps
end MertensFactorGPort
