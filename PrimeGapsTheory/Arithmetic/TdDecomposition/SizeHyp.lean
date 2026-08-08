/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Arithmetic.TdDecomposition.Decomp

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Size hypotheses for the inner sum

Divisor and omega bounds giving the size hypothesis for the inner `w` sum.

## Main results

* `slem_T_d_inner_w_sum`
-/

@[expose] public section

open Real

open scoped Finset

open ArithmeticFunction

namespace PrimeGaps

/-- `n * τ(n) / φ(n) ≤ 4 ^ ω(n)` for squarefree `n ≥ 1`. -/
theorem sqfree_prod_tau_over_phi_le (n : ℕ) (hn : Squarefree n) (h1 : 1 ≤ n) :
    (n : ℝ) * (#n.divisors : ℝ) / (n.totient : ℝ) ≤ 4 ^ #n.primeFactors := by
  have h0 : n ≠ 0 := by omega
  have htau : #n.divisors = 2 ^ #n.primeFactors := by
    rw [Nat.card_divisors h0]
    refine Finset.prod_eq_pow_card fun p hp ↦ ?_
    have := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd h0
      (Nat.dvd_of_mem_primeFactors hp)
    have := hn.natFactorization_le_one p
    omega
  rw [htau]
  push_cast
  rw [squarefree_eq_prod_primes n hn, totient_eq_prod_sub_one n (by omega) hn,
    ← Finset.prod_const (2 : ℝ), ← Finset.prod_const (4 : ℝ), ← Finset.prod_mul_distrib,
    ← Finset.prod_div_distrib]
  refine Finset.prod_le_prod (fun p hp ↦ ?_) fun p hp ↦ ?_ <;>
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  · exact div_nonneg (by positivity) (by linarith)
  · rw [div_le_iff₀ (by linarith)]; nlinarith

/-- For `B ≥ 2` and `n ≥ 1`, the number of prime factors of `n` is at most
`π(B) + log n / log B`. -/
theorem omega_le_pi_add_log_div (B n : ℕ) (hB : 2 ≤ B) (hn : 1 ≤ n) :
    (#n.primeFactors : ℝ) ≤ (#((Finset.Icc 2 B).filter Nat.Prime) : ℝ) +
          Real.log n / Real.log B := by
  have hlogB_pos : 0 < Real.log B := Real.log_pos (by exact_mod_cast (by omega : 1 < B))
  set S := n.primeFactors.filter (fun p ↦ p ≤ B) with hS
  set T := n.primeFactors.filter (fun p ↦ ¬ p ≤ B) with hT
  have hScard : #S ≤ #((Finset.Icc 2 B).filter Nat.Prime) := by
    refine Finset.card_le_card fun p hp ↦ ?_
    obtain ⟨hpmem, hple⟩ := Finset.mem_filter.1 (hS ▸ hp)
    have hprime := Nat.prime_of_mem_primeFactors hpmem
    exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hprime.two_le, hple⟩, hprime⟩
  have hBpow_le : B ^ #T ≤ n :=
    calc B ^ #T = ∏ _ ∈ T, B := (Finset.prod_const B).symm
      _ ≤ ∏ p ∈ T, p := Finset.prod_le_prod' fun p hp ↦ by
            have := Finset.mem_filter.1 (hT ▸ hp); omega
      _ ≤ n := Nat.le_of_dvd (by omega)
            ((Finset.prod_dvd_prod_of_subset _ _ _ (hT ▸ Finset.filter_subset _ _)).trans
              (Nat.prod_primeFactors_dvd n))
  have hTdiv : (#T : ℝ) ≤ Real.log n / Real.log B := by
    rw [le_div_iff₀ hlogB_pos, ← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hBpow_le)
  have hsplit : (#n.primeFactors : ℝ) = #S + #T := by
    rw [hS, hT, ← Nat.cast_add, Finset.card_filter_add_card_filter_not]
  linarith [hsplit, (Nat.cast_le (α := ℝ)).2 hScard]

open Filter in
/-- **Sub-lemma (W').** Uniform in `n`: for a suitable prime bound `B`, for every
`n ≥ 1`, `4^{ω(n)} ≤ 4^{π(B)} · n^{log 4 / log B}`, with `log 4 / log B` made as
small as we like by choosing `B` large. Consequence of `omega_le_pi_add_log_div`
by exponentiating (`4^x = exp(x·log4)`, `n^y = exp(y·log n)`). -/
theorem four_pow_omega_le_const_mul_rpow (B n : ℕ) (hB : 2 ≤ B) (hn : 1 ≤ n) :
    (4 : ℝ) ^ #n.primeFactors ≤ (4 : ℝ) ^ #((Finset.Icc 2 B).filter Nat.Prime) *
          (n : ℝ) ^ (Real.log 4 / Real.log B) := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.rpow_natCast (4 : ℝ) #n.primeFactors,
    ← Real.rpow_natCast (4 : ℝ) #((Finset.Icc 2 B).filter Nat.Prime)]
  simp only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4), Real.rpow_def_of_pos hn_pos,
    ← Real.exp_add, Real.exp_le_exp]
  calc Real.log 4 * (#n.primeFactors : ℝ)
      ≤ Real.log 4 * ((#((Finset.Icc 2 B).filter Nat.Prime) : ℝ) + Real.log n / Real.log B) :=
        mul_le_mul_of_nonneg_left (omega_le_pi_add_log_div B n hB hn)
          (Real.log_nonneg (by norm_num))
    _ = _ := by ring

open Filter in
/-- For every `α > 0` and every constant `K > 0`, the product
`K · (N^α)^{1/16} · (log log N)^{1/4}` is eventually at most `(N^α)^{1/4}`: the extra
`(N^α)^{3/16}` beats any fixed power of `log log N`. -/
private lemma eventually_const_mul_rpow_mul_loglog_rpow_le {α K : ℝ} (hα : 0 < α) (hK : 0 < K) :
    ∀ᶠ N : ℕ in atTop, K * ((N : ℝ) ^ α) ^ ((1 : ℝ) / 16) *
        ((Real.log (Real.log N)) ^ ((1 : ℝ) / 4)) ≤ ((N : ℝ) ^ α) ^ ((1 : ℝ) / 4) := by
  have hbound : ∀ᶠ x : ℝ in atTop, K * (Real.log x) ^ ((1 : ℝ) / 4) ≤ x ^ ((3 : ℝ) * α / 16) := by
    filter_upwards [(isLittleO_log_rpow_rpow_atTop ((1 : ℝ) / 4)
        (by positivity : 0 < (3 : ℝ) * α / 16)).def (by positivity : (0 : ℝ) < 1 / K),
      eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1) _),
      Real.norm_of_nonneg (Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos hx1) _).le] at hx
    calc K * (Real.log x) ^ ((1 : ℝ) / 4) ≤ K * ((1 / K) * x ^ ((3 : ℝ) * α / 16)) :=
          mul_le_mul_of_nonneg_left hx hK.le
      _ = x ^ ((3 : ℝ) * α / 16) := by field_simp
  have hll_le : ∀ᶠ N : ℕ in atTop, Real.log (Real.log (N : ℝ)) ≤ Real.log (N : ℝ) := by
    filter_upwards [(tendsto_natCast_atTop_atTop («R» := ℝ)).eventually_gt_atTop 1] with N hN
    linarith [Real.log_le_sub_one_of_pos (Real.log_pos hN)]
  have hll_nonneg : ∀ᶠ N : ℕ in atTop, (0 : ℝ) ≤ Real.log (Real.log (N : ℝ)) :=
    (Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop 0
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hbound, hll_le, hll_nonneg,
    (tendsto_natCast_atTop_atTop («R» := ℝ)).eventually_gt_atTop 1] with N hb hle hnn hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_trans one_pos hN1
  rw [← Real.rpow_mul hNpos.le, ← Real.rpow_mul hNpos.le]
  calc K * (N : ℝ) ^ (α * (1 / 16)) * (Real.log (Real.log (N : ℝ))) ^ ((1 : ℝ) / 4)
      = ((N : ℝ) ^ (α * (1 / 16))) * (K * (Real.log (Real.log (N : ℝ))) ^ ((1 : ℝ) / 4)) := by ring
    _ ≤ ((N : ℝ) ^ (α * (1 / 16))) * ((N : ℝ) ^ ((3 : ℝ) * α / 16)) :=
        mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hnn hle (by norm_num)) hK.le).trans hb)
          (Real.rpow_pos_of_pos hNpos _).le
    _ = (N : ℝ) ^ (α * (1 / 4)) := by rw [← Real.rpow_add hNpos]; ring_nf

open Filter in
open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- **Crux size lemma (S4).** For `N` large, whenever `d` is squarefree and
coprime to `W N`, `d ≤ R^{1/2}`, `1 ≤ e`, `e ≤ R^{1/8}`, and `e` is coprime to
`d·W N`, the Mertens size hypothesis holds:
`R/(d e²) ≥ 𝒲·τ(𝒲)/φ(𝒲)` with `𝒲 = d·W N`, the paper truncation `R`. -/
theorem slem_T_d_inner_size_hyp (δ θ : ℝ) (hδθ : 0 < δ ∧ δ < θ / 2 ∧ θ < 1) :
    ∀ᶠ N in atTop, ∀ d e : ℕ, Squarefree d → Nat.Coprime d (W N) → (d : ℝ) ≤ R ^ (1 / 2 : ℝ) →
      1 ≤ e → (e : ℝ) ≤ R ^ (1 / 8 : ℝ) →
      Nat.Coprime e (d * W N) → let 𝒲 := d * W N
        (𝒲 : ℝ) * (#𝒲.divisors : ℝ) / (𝒲.totient : ℝ) ≤ R / (d * e ^ 2) := by
  have hδθ2 := hδθ.2.1
  set B : ℕ := 65536 with hB_def
  have hB2 : 2 ≤ B := by norm_num [hB_def]
  have hc : Real.log 4 / Real.log B = 1 / 8 := by
    have h4 : Real.log 4 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    rw [show ((B : ℕ) : ℝ) = (4 : ℝ) ^ (8 : ℕ) by rw [hB_def]; norm_num, Real.log_pow]
    push_cast
    field_simp
  set K : ℝ := (4 : ℝ) ^ #((Finset.Icc 2 B).filter Nat.Prime) with hK_def
  have hK_pos : 0 < K := by rw [hK_def]; positivity
  have hengine : ∀ᶠ N : ℕ in atTop, K * (R ^ ((1 : ℝ) / 16)) *
        ((Real.log (Real.log N)) ^ ((1 : ℝ) / 4)) ≤ R ^ ((1 : ℝ) / 4) :=
    eventually_const_mul_rpow_mul_loglog_rpow_le (by linarith) hK_pos
  have hLLev : ∀ᶠ N : ℕ in atTop, (0 : ℝ) ≤ Real.log (Real.log (N : ℝ)) :=
    (Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop 0
  filter_upwards [hengine, PrimeGaps.lem_W_size,
      R_eventually_ge θ δ hδθ2 256, hLLev] with N hEng hWsize hR256 hLL
  intro d e hd hcop_d hd_le he1 he_le hcop_e 𝒲
  have hR_pos : (0 : ℝ) < R := lt_of_lt_of_le (by norm_num) hR256
  have h𝒲_sqfree : Squarefree 𝒲 := Nat.squarefree_mul_iff.2 ⟨hcop_d, hd, PrimeGaps.W_squarefree⟩
  have h𝒲_pos : 1 ≤ 𝒲 := Nat.one_le_iff_ne_zero.2
    (Nat.mul_ne_zero hd.ne_zero (Nat.one_le_iff_ne_zero.1 PrimeGaps.W_pos))
  have h𝒲R : (0 : ℝ) < (𝒲 : ℝ) := by exact_mod_cast h𝒲_pos
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd.ne_zero
  have he_pos : (0 : ℝ) < e := by exact_mod_cast he1
  have hB' : (4 : ℝ) ^ #𝒲.primeFactors ≤ K * (𝒲 : ℝ) ^ (Real.log 4 / Real.log B) :=
    four_pow_omega_le_const_mul_rpow B 𝒲 hB2 h𝒲_pos
  rw [hc] at hB'
  have h𝒲_le : (𝒲 : ℝ) ≤ (R ^ ((1 : ℝ) / 2)) * (Real.log (Real.log N)) ^ 2 := by
    simp only [𝒲, Nat.cast_mul]
    calc (d : ℝ) * (W N : ℝ) ≤ (R ^ ((1 : ℝ) / 2)) * (W N : ℝ) :=
          mul_le_mul_of_nonneg_right hd_le (Nat.cast_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hWsize (Real.rpow_pos_of_pos hR_pos _).le
  have hRHS : R ^ ((1 : ℝ) / 4) ≤ R / (d * e ^ 2) := by
    have hde2 : (d : ℝ) * e ^ 2 ≤ R ^ ((3 : ℝ) / 4) :=
      calc (d : ℝ) * e ^ 2 ≤ (R ^ ((1 : ℝ) / 2)) * (R ^ ((1 : ℝ) / 8)) ^ 2 :=
            mul_le_mul hd_le (pow_le_pow_left₀ he_pos.le he_le 2) (sq_nonneg _)
              (Real.rpow_pos_of_pos hR_pos _).le
        _ = R ^ ((3 : ℝ) / 4) := by
            rw [← Real.rpow_natCast (R ^ ((1 : ℝ) / 8)) 2, ← Real.rpow_mul hR_pos.le,
                ← Real.rpow_add hR_pos]
            norm_num
    rw [le_div_iff₀ (mul_pos hd_pos (pow_pos he_pos 2))]
    calc R ^ ((1 : ℝ) / 4) * ((d : ℝ) * e ^ 2) ≤ R ^ ((1 : ℝ) / 4) * R ^ ((3 : ℝ) / 4) :=
          mul_le_mul_of_nonneg_left hde2 (Real.rpow_pos_of_pos hR_pos _).le
      _ = R := by rw [← Real.rpow_add hR_pos]; norm_num
  calc (𝒲 : ℝ) * (#𝒲.divisors : ℝ) / (𝒲.totient : ℝ) ≤ 4 ^ #𝒲.primeFactors :=
        sqfree_prod_tau_over_phi_le 𝒲 h𝒲_sqfree h𝒲_pos
    _ ≤ K * (𝒲 : ℝ) ^ ((1 : ℝ) / 8) := hB'
    _ ≤ K * ((R ^ ((1 : ℝ) / 2)) * (Real.log (Real.log N)) ^ 2) ^ ((1 : ℝ) / 8) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h𝒲R.le h𝒲_le (by norm_num)) hK_pos.le
    _ = K * (R ^ ((1 : ℝ) / 16)) * (Real.log (Real.log N)) ^ ((1 : ℝ) / 4) := by
        rw [Real.mul_rpow (Real.rpow_pos_of_pos hR_pos _).le (sq_nonneg _),
          ← Real.rpow_natCast (Real.log (Real.log N)) 2,
          ← Real.rpow_mul hR_pos.le, ← Real.rpow_mul hLL]
        norm_num [mul_assoc]
    _ ≤ R ^ ((1 : ℝ) / 4) := hEng
    _ ≤ R / (d * e ^ 2) := hRHS

open Filter in
open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- Mertens for the inner sum: `∑_{w ≤ R/(d e ^ 2), (w, 𝒲) = 1} 1 / w` equals
`(φ(𝒲) / 𝒲) * (log R - log d - 2 log e)` up to `C * (φ(𝒲) / 𝒲) * (1 + log (log (exp 1 * 𝒲)))`,
where `𝒲 = d * W N`. -/
@[pg_tag "bg246" "slem_T_d_inner_w_sum"]
theorem slem_T_d_inner_w_sum (δ θ : ℝ) (hδθ : 0 < δ ∧ δ < θ / 2 ∧ θ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N in atTop, ∀ d e : ℕ, Squarefree d → Nat.Coprime d (W N) →
      (d : ℝ) ≤ R ^ (1 / 2 : ℝ) →
      1 ≤ e → (e : ℝ) ≤ R ^ (1 / 8 : ℝ) →
      Nat.Coprime e (d * W N) → let 𝒲 := d * W N
        |(∑ w ∈ {w ∈ Finset.Icc 1 ⌊R / (d * e ^ 2)⌋₊ | Nat.Coprime w 𝒲},
              (1 : ℝ) / w) - (𝒲.totient : ℝ) / 𝒲 * (Real.log R - Real.log d - 2 * Real.log e)| ≤
          C * ((𝒲.totient : ℝ) / 𝒲) * (1 + Real.log (Real.log (rexp 1 * 𝒲))) := by
  obtain ⟨C, hC, hmert⟩ := mertens_reciprocal_general
  refine ⟨C, hC, ?_⟩
  filter_upwards [slem_T_d_inner_size_hyp δ θ hδθ,
      R_eventually_ge θ δ hδθ.2.1 256] with N hsize hR256
  intro d e hd hcop_d hd_le he1 he_le hcop_e 𝒲
  have hsize' := hsize d e hd hcop_d hd_le he1 he_le hcop_e
  simp only at hsize'
  have h𝒲_sqfree : Squarefree 𝒲 := Nat.squarefree_mul_iff.2 ⟨hcop_d, hd, PrimeGaps.W_squarefree⟩
  have h𝒲_pos : 1 ≤ 𝒲 := Nat.one_le_iff_ne_zero.2
    (Nat.mul_ne_zero hd.ne_zero (Nat.one_le_iff_ne_zero.1 PrimeGaps.W_pos))
  have hR_pos : (0 : ℝ) < R := lt_of_lt_of_le (by norm_num) hR256
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd.ne_zero
  have he_pos : (0 : ℝ) < e := by exact_mod_cast he1
  have hlog : Real.log (R / (d * e ^ 2)) = Real.log R - Real.log d - 2 * Real.log e := by
    rw [Real.log_div hR_pos.ne' (by positivity),
      Real.log_mul hd_pos.ne' (by positivity), Real.log_pow]
    push_cast
    ring
  rw [← hlog]
  exact hmert 𝒲 h𝒲_sqfree h𝒲_pos (R / (d * e ^ 2)) hsize'

end PrimeGaps
