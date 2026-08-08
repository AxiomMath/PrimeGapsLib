/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Arithmetic.ConstantsAB
public import PrimeGapsTheory.Arithmetic.Mertens.ReciprocalW
public import PrimeGapsTheory.Arithmetic.MobiusLcm
public import PrimeGapsTheory.Arithmetic.Totient.Basic

import PrimeGapsTheory.Tactic.PaperTag

/-!
# The Td decomposition

The Mobius decomposition of `T` and the tail bound for its double sum.

## Main results

* `T_decomposition`
-/

@[expose] public section

open scoped ArithmeticFunction.Moebius

open ArithmeticFunction

namespace PrimeGaps

/-- The sum `T d = ∑_{v ≤ R/d, gcd(v, d*W) = 1} μ(v)^2 / v`, where `v` ranges over
positive integers with `v ≤ R/d` and `gcd(v, d*W) = 1`. -/
noncomputable def T (R : ℝ) (W d : ℕ) : ℝ :=
  ∑ v ∈ {v ∈ Finset.Icc 1 ⌊R / d⌋₊ | Nat.Coprime v (d * W)}, ((μ v : ℝ) ^ 2) / v

end PrimeGaps

namespace Nat

/-- `(e ^ 2 * w).Coprime n ↔ e.Coprime n ∧ w.Coprime n`. -/
lemma coprime_sq_mul_iff (e w n : ℕ) :
    Nat.Coprime (e ^ 2 * w) n ↔ Nat.Coprime e n ∧ Nat.Coprime w n := by
  rw [Nat.coprime_mul_iff_left, Nat.coprime_pow_left_iff (by norm_num : 0 < 2)]

end Nat

namespace PrimeGaps

/-- The range `e ^ 2 * w ≤ ⌊R / d⌋₊` splits as `e ≤ ⌊√(R / d)⌋₊` and `w ≤ ⌊R / (d * e ^ 2)⌋₊`. -/
lemma floor_range_equiv (R : ℝ) (hR : 1 ≤ R) (d e w : ℕ) (hd : 0 < d) (he : 1 ≤ e) (hw : 1 ≤ w) :
    e ^ 2 * w ≤ ⌊R / d⌋₊ ↔
      e ≤ ⌊√(R / d)⌋₊ ∧ w ≤ ⌊R / (d * (e : ℝ) ^ 2)⌋₊ := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  set x : ℝ := R / d with hx
  have hx0 : 0 ≤ x := div_nonneg (by linarith) hd0.le
  have he0 : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hesq : (0 : ℝ) < (e : ℝ) ^ 2 := by positivity
  have hw0 : (1 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  have hdiv : R / ((d : ℝ) * (e : ℝ) ^ 2) = x / (e : ℝ) ^ 2 := by rw [hx]; field_simp
  rw [hdiv, Nat.le_floor_iff hx0, Nat.le_floor_iff (Real.sqrt_nonneg x),
    Nat.le_floor_iff (div_nonneg hx0 hesq.le), Real.le_sqrt he0.le hx0, le_div_iff₀ hesq]
  push_cast
  exact ⟨fun h ↦ ⟨by nlinarith, by linarith⟩, fun h ↦ by linarith [h.2]⟩

/-- **Reindexing by `v = e ^ 2 * w`.**  The sum of `μ(e) / v` over the pairs `(v, e)` with
`v ≤ R/d`, `v` coprime to `d * W` and `e ^ 2 ∣ v` equals the sum of `(μ(e) / e ^ 2) * (1 / w)`
over the pairs `(e, w)` with `e ≤ √(R/d)`, `w ≤ R/(d e ^ 2)` and both coprime to `d * W`.

The bijection is `(v, e) ↦ (e, v / e ^ 2)` with inverse `(e, w) ↦ (e ^ 2 * w, e)`; the range
condition splits by `floor_range_equiv` and the coprimality by `Nat.coprime_sq_mul_iff`. -/
lemma sum_sigma_sqDvd_eq_sum_sigma_split (R : ℝ) (hR : 1 ≤ R) (W d : ℕ) (hd : 0 < d) :
    (∑ p ∈ {v ∈ Finset.Icc 1 ⌊R / d⌋₊ | Nat.Coprime v (d * W)}.sigma
          (fun v ↦ {e ∈ Finset.Icc 1 v | e ^ 2 ∣ v}),
        (μ p.2 : ℝ) / (p.1 : ℝ)) =
      ∑ q ∈ {e ∈ Finset.Icc 1 ⌊√(R / d)⌋₊ | Nat.Coprime e (d * W)}.sigma
          (fun e ↦ {w ∈ Finset.Icc 1 ⌊R / (d * (e : ℝ) ^ 2)⌋₊ | Nat.Coprime w (d * W)}),
        ((μ q.1 : ℝ) / (q.1 : ℝ) ^ 2) * (1 / (q.2 : ℝ)) := by
  refine Finset.sum_bij' (i := fun p _ ↦ (⟨p.2, p.1 / p.2 ^ 2⟩ : Σ _ : ℕ, ℕ))
    (j := fun q _ ↦ (⟨q.1 ^ 2 * q.2, q.1⟩ : Σ _ : ℕ, ℕ))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨v, e⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    obtain ⟨⟨⟨hv1, hvR⟩, hvcop⟩, ⟨he1, -⟩, hsq⟩ := hp
    have hwe : e ^ 2 * (v / e ^ 2) = v := Nat.mul_div_cancel' hsq
    have hw1 : 1 ≤ v / e ^ 2 :=
      (Nat.one_le_div_iff (Nat.pow_pos he1)).mpr (Nat.le_of_dvd (by omega) hsq)
    have hrange := floor_range_equiv R hR d e (v / e ^ 2) hd he1 hw1
    rw [hwe] at hrange
    obtain ⟨heS, hwS⟩ := hrange.mp hvR
    have hcop := (Nat.coprime_sq_mul_iff e (v / e ^ 2) (d * W)).mp (by rwa [hwe])
    exact ⟨⟨⟨he1, heS⟩, hcop.1⟩, ⟨hw1, hwS⟩, hcop.2⟩
  · rintro ⟨e, w⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at hq ⊢
    obtain ⟨⟨⟨he1, heS⟩, hecop⟩, ⟨hw1, hwS⟩, hwcop⟩ := hq
    exact ⟨⟨⟨Nat.one_le_iff_ne_zero.mpr (by positivity),
        (floor_range_equiv R hR d e w hd he1 hw1).mpr ⟨heS, hwS⟩⟩,
      (Nat.coprime_sq_mul_iff e w (d * W)).mpr ⟨hecop, hwcop⟩⟩, ⟨he1, by nlinarith⟩, w, by ring⟩
  · rintro ⟨v, e⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter] at hp
    simp only [Nat.mul_div_cancel' hp.2.2]
  · rintro ⟨e, w⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at hq
    simp only [Nat.mul_div_cancel_left w (Nat.pow_pos hq.1.1.1 : 0 < e ^ 2)]
  · rintro ⟨v, e⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hv1, -⟩, -⟩, ⟨he1, -⟩, hsq⟩ := hp
    have hene : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hvne : (v : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hcast : ((v / e ^ 2 : ℕ) : ℝ) = (v : ℝ) / (e : ℝ) ^ 2 := by
      rw [eq_div_iff (pow_ne_zero 2 hene)]; exact_mod_cast Nat.div_mul_cancel hsq
    simp only [hcast]
    field_simp

/-- Writing `v = e ^ 2 * w` via `μ(v) ^ 2 = ∑_{e ^ 2 ∣ v} μ(e)` decomposes `T R W d` as
`∑_{e ≤ √(R/d), (e, dW) = 1} (μ(e) / e ^ 2) * ∑_{w ≤ R/(d e ^ 2), (w, dW) = 1} 1 / w`. -/
@[pg_tag "bg246" "slem_T_d_mobius"]
theorem T_decomposition (R : ℝ) (hR : 1 ≤ R) (W d : ℕ) (hd : 0 < d) :
    T R W d = ∑ e ∈ {e ∈ Finset.Icc 1 ⌊√(R / d)⌋₊ | Nat.Coprime e (d * W)},
          ((μ e : ℝ) / (e : ℝ) ^ 2) *
            ∑ w ∈ {w ∈ Finset.Icc 1 ⌊R / (d * (e : ℝ) ^ 2)⌋₊ | Nat.Coprime w (d * W)},
              (1 / (w : ℝ)) := by
  set Vset := {v ∈ Finset.Icc 1 ⌊R / d⌋₊ | Nat.Coprime v (d * W)}
  set Eset := {e ∈ Finset.Icc 1 ⌊√(R / d)⌋₊ | Nat.Coprime e (d * W)}
  set Dset : ℕ → Finset ℕ := fun v ↦ {e ∈ Finset.Icc 1 v | e ^ 2 ∣ v} with hDset
  set Wset : ℕ → Finset ℕ :=
    fun e ↦ {w ∈ Finset.Icc 1 ⌊R / (d * (e : ℝ) ^ 2)⌋₊ | Nat.Coprime w (d * W)}
  have stepA : T R W d = ∑ v ∈ Vset, ∑ e ∈ Dset v, (μ e : ℝ) / (v : ℝ) := by
    rw [T]
    refine Finset.sum_congr rfl fun v hv ↦ ?_
    rw [Finset.mem_filter, Finset.mem_Icc] at hv
    have hvpos : 0 < v := hv.1.1
    have hset : Dset v = v.divisors.filter (fun e ↦ e ^ 2 ∣ v) := by
      ext e
      simp only [hDset, Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
      exact ⟨fun ⟨_, hsq⟩ ↦ ⟨⟨(dvd_pow_self e two_ne_zero).trans hsq, hvpos.ne'⟩, hsq⟩,
        fun ⟨⟨he, _⟩, hsq⟩ ↦ ⟨⟨Nat.pos_of_dvd_of_pos he hvpos, Nat.le_of_dvd hvpos he⟩, hsq⟩⟩
    rw [show ((μ v : ℝ)) ^ 2 = ∑ e ∈ Dset v, (μ e : ℝ) by
        rw [hset]; exact_mod_cast moebius_sq_eq_sum_moebius_of_sq_dvd v hvpos,
      Finset.sum_div]
  have stepC : (∑ p ∈ Vset.sigma Dset, (μ p.2 : ℝ) / (p.1 : ℝ)) = ∑ q ∈ Eset.sigma Wset,
            ((μ q.1 : ℝ) / (q.1 : ℝ) ^ 2) * (1 / (q.2 : ℝ)) :=
    sum_sigma_sqDvd_eq_sum_sigma_split R hR W d hd
  have stepD : (∑ q ∈ Eset.sigma Wset, ((μ q.1 : ℝ) / (q.1 : ℝ) ^ 2) * (1 / (q.2 : ℝ))) =
        ∑ e ∈ Eset, ((μ e : ℝ) / (e : ℝ) ^ 2) * ∑ w ∈ Wset e, (1 / (w : ℝ)) := by
    simp only [Finset.mul_sum, Finset.sum_sigma']
  rw [stepA, Finset.sum_sigma', stepC, stepD]

open Finset

/-- The Möbius weight `μ(e)·c/e²` has absolute value at most `c/e²` when `0 ≤ c`. -/
lemma abs_moebius_mul_div_sq_le (e : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    |(μ e : ℝ) * c / (e : ℝ) ^ 2| ≤ c / (e : ℝ) ^ 2 := by
  have hμ : |(μ e : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  rw [abs_div, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (e : ℝ) ^ 2), abs_of_nonneg hc]
  exact div_le_div_of_nonneg_right (mul_le_of_le_one_left hc hμ) (by positivity)

/-- The Möbius weight `μ(e)/e²` has absolute value at most `1/e²`. -/
lemma abs_moebius_div_sq_le (e : ℕ) : |(μ e : ℝ) / (e : ℝ) ^ 2| ≤ 1 / (e : ℝ) ^ 2 := by
  simpa using abs_moebius_mul_div_sq_le e zero_le_one

/-- The partial sums of `∑ 1/e²` starting at `e = 1` never exceed `2`. -/
private lemma sum_Icc_one_inv_sq_le_two (m : ℕ) : ∑ e ∈ Finset.Icc 1 m, 1 / (e : ℝ) ^ 2 ≤ 2 := by
  rcases Nat.lt_or_ge m 1 with hm | hm
  · rw [Finset.Icc_eq_empty (by omega)]; norm_num
  · have hsub := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 1) (n := m) (by norm_num) (by omega)
    rw [show Finset.Icc 1 m = insert 1 (Finset.Ioc 1 m) by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]; omega,
      Finset.sum_insert (by simp), show (1 : ℝ) / ((1 : ℕ) : ℝ) ^ 2 = 1 by norm_num]
    simp only [one_div] at hsub ⊢
    norm_num at hsub
    linarith [inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) m)]

/-- A Möbius-weighted sum whose factors are uniformly bounded by `K` on a set of indices
lying in `Finset.Icc 1 m` is bounded by `2 * K`. -/
lemma abs_sum_moebius_div_sq_mul_le {m : ℕ} {E : Finset ℕ} (hE : E ⊆ Finset.Icc 1 m)
    {F : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K) (hF : ∀ e ∈ E, |F e| ≤ K) :
    |∑ e ∈ E, (μ e : ℝ) / (e : ℝ) ^ 2 * F e| ≤ 2 * K :=
  calc |∑ e ∈ E, (μ e : ℝ) / (e : ℝ) ^ 2 * F e|
      ≤ ∑ e ∈ E, |(μ e : ℝ) / (e : ℝ) ^ 2 * F e| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ E, 1 / (e : ℝ) ^ 2 * K := by
        refine Finset.sum_le_sum fun e he ↦ ?_
        rw [abs_mul]
        exact mul_le_mul (abs_moebius_div_sq_le e) (hF e he) (abs_nonneg _) (by positivity)
    _ = (∑ e ∈ E, 1 / (e : ℝ) ^ 2) * K := by rw [← Finset.sum_mul]
    _ ≤ 2 * K := mul_le_mul_of_nonneg_right
        ((Finset.sum_le_sum_of_subset_of_nonneg hE fun e _ _ ↦ by positivity).trans
          (sum_Icc_one_inv_sq_le_two m)) hK

/-- For `0 ≤ y ≤ z`, cutting `Finset.Icc 1 ⌊z⌋₊` down by the size constraint `(e : ℝ) ≤ y`
leaves exactly `Finset.Icc 1 ⌊y⌋₊`, so the two filtered index sets agree. -/
lemma filter_Icc_floor_and_natCast_le_eq {y z : ℝ} (hy : 0 ≤ y) (hyz : y ≤ z)
    (p : ℕ → Prop) [DecidablePred p] :
    {e ∈ Finset.Icc 1 ⌊z⌋₊ | p e ∧ (e : ℝ) ≤ y} = (Finset.Icc 1 ⌊y⌋₊).filter p := by
  ext e
  simp only [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨fun ⟨⟨he1, _⟩, hp, hey⟩ ↦ ⟨⟨he1, Nat.le_floor hey⟩, hp⟩, fun ⟨⟨he1, hey⟩, hp⟩ ↦ ?_⟩
  have hey' : (e : ℝ) ≤ y := (Nat.le_floor_iff hy).mp hey
  exact ⟨⟨he1, Nat.le_floor (hey'.trans hyz)⟩, hp, hey'⟩

/-- The inner sum
`∑_{w ≤ R/(d e²), (w, dW) = 1} 1/w`. -/
noncomputable def innerSum (R : ℝ) (W d e : ℕ) : ℝ :=
  ∑ w ∈ (Finset.Icc 1 ⌊R / ((d : ℝ) * (e : ℝ) ^ 2)⌋₊).filter
      (fun w : ℕ ↦ (w : ℝ) ≤ R / ((d : ℝ) * (e : ℝ) ^ 2) ∧ Nat.Coprime w (d * W)),
    (1 : ℝ) / w

/-- The full double sum
`∑_{R^{1/8} < e ≤ √(R/d), (e, dW)=1} (μ(e)/e²) · ∑_{w ≤ R/(d e²), (w, dW)=1} 1/w`. -/
noncomputable def doubleSum (R : ℝ) (W d : ℕ) : ℝ :=
  ∑ e ∈ (Finset.Icc 1 ⌊√(R / d)⌋₊).filter
      (fun e : ℕ ↦ R ^ (1 / 8 : ℝ) < (e : ℝ) ∧ (e : ℝ) ≤ √(R / d) ∧ Nat.Coprime e (d * W)),
    ((μ e : ℝ) / (e : ℝ) ^ 2) * innerSum R W d e

/-- The inner sum is nonnegative. -/
lemma innerSum_nonneg (R : ℝ) (W d e : ℕ) : 0 ≤ innerSum R W d e :=
  Finset.sum_nonneg fun w _ ↦ by positivity

/-- The inner sum is bounded by `1 + log R`. -/
lemma innerSum_le (R : ℝ) (W d e : ℕ) (hR : 1 ≤ R) (hd : 1 ≤ d) (he : 1 ≤ e) :
    innerSum R W d e ≤ 1 + Real.log R := by
  set M : ℝ := R / ((d : ℝ) * (e : ℝ) ^ 2) with hM
  have hde : (1 : ℝ) ≤ (d : ℝ) * (e : ℝ) ^ 2 := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show d * e ^ 2 ≠ 0 by positivity)
  have hMR : M ≤ R := div_le_self (by linarith) hde
  have hstep : innerSum R W d e ≤ (harmonic ⌊M⌋₊ : ℝ) := by
    unfold innerSum
    rw [harmonic_eq_sum_Icc]
    push_cast
    simp only [one_div, ← hM]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun w _ _ ↦ by positivity
  refine hstep.trans ?_
  by_cases hM1 : 1 ≤ M
  · have := harmonic_floor_le_one_add_log M hM1
    linarith [Real.log_le_log (by linarith : (0 : ℝ) < M) hMR]
  · push Not at hM1
    rw [Nat.floor_eq_zero.mpr hM1]
    simp only [harmonic_zero, Rat.cast_zero]
    linarith [Real.log_nonneg hR]

/-- Core real-analytic bound on the double sum, valid for any `W` and any
`d ≥ 1`, once `R` is large enough. -/
lemma doubleSum_core (R : ℝ) (W d : ℕ) (hR : (256 : ℝ) ≤ R) (hd : 1 ≤ d) :
    |doubleSum R W d| ≤ 4 * Real.log R / R ^ (1 / 8 : ℝ) := by
  set K : ℝ := R ^ (1 / 8 : ℝ) with hK
  set L : ℕ := ⌊√(R / d)⌋₊ with hLdef
  set m : ℕ := ⌊K⌋₊ with hmdef
  have h256 : (256 : ℝ) ^ (1 / 8 : ℝ) = 2 := by
    rw [show (256 : ℝ) = (2 : ℝ) ^ (8 : ℕ) by norm_num, ← Real.rpow_natCast 2 8,
      ← Real.rpow_mul (by norm_num)]
    norm_num
  have hK2 : (2 : ℝ) ≤ K := by
    rw [hK, ← h256]; exact Real.rpow_le_rpow (by norm_num) hR (by norm_num)
  have hKpos : (0 : ℝ) < K := by linarith
  have hmK : (m : ℝ) ≤ K := Nat.floor_le hKpos.le
  have hKm : K ≤ (m : ℝ) + 1 := (Nat.lt_floor_add_one K).le
  have hm1 : 1 ≤ m := Nat.one_le_cast.mp (by linarith : (1 : ℝ) ≤ (m : ℝ))
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hlogR : (1 : ℝ) ≤ Real.log R := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  set S : Finset ℕ := (Finset.Icc 1 L).filter
      (fun e : ℕ ↦ R ^ (1 / 8 : ℝ) < (e : ℝ) ∧ (e : ℝ) ≤ √(R / d) ∧
        Nat.Coprime e (d * W)) with hSdef
  have htri : |doubleSum R W d| ≤ (∑ e ∈ S, (1 / (e : ℝ) ^ 2)) * (1 + Real.log R) := by
    unfold doubleSum
    rw [← hSdef, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e he ↦ ?_)
    simp only [hSdef, Finset.mem_filter, Finset.mem_Icc] at he
    rw [abs_mul, abs_of_nonneg (innerSum_nonneg R W d e)]
    exact mul_le_mul (abs_moebius_div_sq_le e) (innerSum_le R W d e (by linarith) hd he.1.1)
      (innerSum_nonneg R W d e) (by positivity)
  have hSsub : S ⊆ Finset.Ioc m L := fun e he ↦ by
    simp only [hSdef, Finset.mem_filter, Finset.mem_Icc] at he
    exact Finset.mem_Ioc.mpr ⟨by exact_mod_cast hmK.trans_lt he.2.1, he.1.2⟩
  have hIoc : ∑ e ∈ Finset.Ioc m L, (1 / (e : ℝ) ^ 2) ≤ (m : ℝ)⁻¹ := by
    simp only [one_div]
    by_cases hmL : m ≤ L
    · linarith [sum_Ioc_inv_sq_le_sub (α := ℝ) (k := m) (n := L) (by omega) hmL,
        inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) L)]
    · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]; positivity
  have hsumfinal : ∑ e ∈ S, (1 / (e : ℝ) ^ 2) ≤ (m : ℝ)⁻¹ :=
    (Finset.sum_le_sum_of_subset_of_nonneg hSsub fun e _ _ ↦ by positivity).trans hIoc
  have hminv : (m : ℝ)⁻¹ ≤ 2 / K := by
    rw [inv_eq_one_div, div_le_div_iff₀ hmpos hKpos]; linarith
  calc |doubleSum R W d| ≤ (∑ e ∈ S, (1 / (e : ℝ) ^ 2)) * (1 + Real.log R) := htri
    _ ≤ (m : ℝ)⁻¹ * (2 * Real.log R) :=
        mul_le_mul hsumfinal (by linarith) (by linarith) (by positivity)
    _ ≤ (2 / K) * (2 * Real.log R) := mul_le_mul_of_nonneg_right hminv (by linarith)
    _ = 4 * Real.log R / K := by ring

/-- `c ≤ R` for all large `N` at any bound `c`, since `R = N ^ (θ / 2 - δ) → ∞`. -/
lemma R_eventually_ge (θ δ : ℝ) (hδθ : δ < θ / 2) (c : ℝ) :
    ∀ᶠ N : ℕ in Filter.atTop, c ≤ PrimeGaps.sieveTruncation N δ θ := by
  have htend : Filter.Tendsto (fun N : ℕ ↦ PrimeGaps.sieveTruncation N δ θ)
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  exact htend.eventually_ge_atTop c

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- **Theorem.**  With `R = N^(θ/2 - δ)` (`R`) and the paper modulus `W N`, there is an
absolute constant `C > 0` such that, for every fixed level-of-distribution exponent
`θ ∈ (0,1)` and every fixed `δ` with `0 < δ < θ/2`, for all sufficiently large `N`, and for
every squarefree integer `d` with `(d, W) = 1` and `d ≤ R^(1/2)`, the double sum is bounded in
absolute value by `C · (log R) / R^(1/8)`.  The constant `C` is independent of
`N` and of the ranging parameter `d`. -/
@[pg_tag "bg246" "slem_T_d_tail_e"]
theorem doubleSum_ll_log_div_rpow : ∃ C : ℝ, 0 < C ∧
      ∀ θ δ : ℝ, 0 < θ → θ < 1 → 0 < δ → δ < θ / 2 → ∀ᶠ N : ℕ in Filter.atTop,
          ∀ d : ℕ, Squarefree d → Nat.Coprime d (W N) → (d : ℝ) ≤ R ^ (1 / 2 : ℝ) →
              |doubleSum R (W N) d| ≤ C * (Real.log R) / R ^ (1 / 8 : ℝ) := by
  refine ⟨4, by norm_num, fun θ δ _ _ _ hδθ ↦ ?_⟩
  filter_upwards [R_eventually_ge θ δ hδθ 256] with N hN256 d hsf _ _
  exact doubleSum_core R (W N) d hN256 (Nat.one_le_iff_ne_zero.mpr hsf.ne_zero)

end PrimeGaps
