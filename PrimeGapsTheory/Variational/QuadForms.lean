/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.Certificate.Explicit
public import PrimeGapsTheory.Variational.Integration.Simplex

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Polynomial quadratic forms

Evaluates the one-dimensional integrals and quadratic forms associated with polynomial test
functions on a simplex.

## Main definitions

* `polyP`: The polynomial test function determined by a finite monomial basis.
* `F_P_quad`: The simplex-supported polynomial test function.

## Main results

* `lem_inner_integral_1D`: Evaluates the inner one-dimensional integral.
* `lem_squared_inner_integral`: Evaluates the square of the inner integral.
* `lem_quad_forms`: Expresses the marginal integral as a quadratic form.
-/

@[expose] public section

open EuclideanSpace

open scoped Nat

namespace PrimeGaps

section

open MeasureTheory

/-- The binomial expansion of `(t^2 + P2')^c`. -/
lemma pow_sq_add_eq_sum (c : ℕ) (t P2' : ℝ) : (t ^ 2 + P2') ^ c = ∑ c' ∈ Finset.range (c + 1),
          (c.choose c' : ℝ) * P2' ^ c' * t ^ (2 * (c - c')) := by
  rw [add_comm (t ^ 2) P2', add_pow]
  refine Finset.sum_congr rfl (fun c' _ ↦ ?_)
  rw [← pow_mul, mul_comm 2 (c - c')]
  ring

/-- The integral of the binomial expansion of `(t1 ^ 2 + P2') ^ c` equals the corresponding
finite sum of integrals. -/
lemma integral_eq_sum (b c : ℕ) (P1' P2' : ℝ) : ∫ t1 in (0 : ℝ)..(1 - P1'),
        (1 - P1' - t1) ^ b * (t1 ^ 2 + P2') ^ c ∂volume = ∑ c' ∈ Finset.range (c + 1),
          (c.choose c' : ℝ) * P2' ^ c' * ∫ t1 in (0 : ℝ)..(1 - P1'),
                (1 - P1' - t1) ^ b * t1 ^ (2 * (c - c')) ∂volume := by
  have hpoint : ∀ t1 : ℝ, (1 - P1' - t1) ^ b * (t1 ^ 2 + P2') ^ c = ∑ c' ∈ Finset.range (c + 1),
            (c.choose c' : ℝ) * P2' ^ c' *
              ((1 - P1' - t1) ^ b * t1 ^ (2 * (c - c'))) := by
    intro t1
    rw [pow_sq_add_eq_sum c t1 P2', Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c' _ ↦ ?_)
    ring
  simp_rw [hpoint]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl (fun c' _ ↦ ?_)
    exact intervalIntegral.integral_const_mul _ _
  · intros c' _
    refine Continuous.intervalIntegrable ?_ _ _
    fun_prop

/-- For natural numbers `b, c, c'` with `c' ≤ c`, `b + 2 * (c - c') + 1 = b + 2 * c - 2 * c' + 1`.
-/
lemma exp_eq (b c c' : ℕ) (hc' : c' ≤ c) : b + 2 * (c - c') + 1 = b + 2 * c - 2 * c' + 1 := by omega

/-- For natural numbers `c, c'` with `c' ≤ c`, `2 * (c - c') = 2 * c - 2 * c'`. -/
lemma two_mul_sub (c c' : ℕ) (hc' : c' ≤ c) : 2 * (c - c') = 2 * c - 2 * c' := by omega

/-- The integral of `(1 - P1' - t) ^ b * (t ^ 2 + P2') ^ c` equals its finite beta-integral
expansion. -/
@[pg_tag "bg246" "lem_inner_integral_1D"]
theorem lem_inner_integral_1D (b c : ℕ) (P1' P2' : ℝ) : ∫ t1 in (0 : ℝ)..(1 - P1'),
        (1 - P1' - t1) ^ b * (t1 ^ 2 + P2') ^ c ∂volume = ∑ c' ∈ Finset.range (c + 1),
          (c.choose c' : ℝ) * P2' ^ c' * (1 - P1') ^ (b + 2 * c - 2 * c' + 1) *
            ((b ! * (2 * c - 2 * c')! : ℝ) /
              ((b + 2 * c - 2 * c' + 1)! : ℝ)) := by
  rw [integral_eq_sum b c P1' P2']
  refine Finset.sum_congr rfl (fun c' hc'mem ↦ ?_)
  have hc' : c' ≤ c := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc'mem)
  rw [integral_complement_pow_mul_pow b (2 * (c - c')) (1 - P1'),
      exp_eq b c c' hc', two_mul_sub c c' hc']
  ring

end

section
open scoped BigOperators PrimeGaps

local notation "ES(" 𝕜:65 ", " k:65 ")" => EuclideanSpace 𝕜 (Fin k)

variable {ι : Type*}

/-- The polynomial `P(x_1, …, x_k) = ∑_{i ∈ I} a_i (1 - P_1)^{b_i} P_2^{c_i}`, where
`P_1 = ∑_j x_j` and `P_2 = ∑_j x_j^2`.
-/
noncomputable def polyP {k : ℕ} (I : Finset ι) (a : ι → ℝ) (b c : ι → ℕ) (t : ES(ℝ, k)) : ℝ :=
  ∑ i ∈ I, a i * (1 - (∑ j, t j)) ^ (b i) * (∑ j, (t j) ^ 2) ^ (c i)

/-- The truncated integrand `F_P_idx = 1_{𝓡 k} · polyP`. -/
@[nolint defsWithUnderscore]
noncomputable def F_P_idx {k : ℕ} (I : Finset ι) (a : ι → ℝ) (b c : ι → ℕ) (t : ES(ℝ, k)) : ℝ :=
  (𝓡 k).indicator (polyP I a b c) t

/-- The truncated power sum `P_1' = ∑_{i=2}^k x_i`. -/
noncomputable def P1' {n : ℕ} (s : ES(ℝ, n)) : ℝ := ∑ i, s i

/-- Truncated power sum `P_2' = ∑_{i=2}^k x_i^2`. -/
noncomputable def P2' {n : ℕ} (s : ES(ℝ, n)) : ℝ := ∑ i, (s i) ^ 2

/-- The integral of `F_P_idx` over its first coordinate in `[0, 1]`. -/
noncomputable def innerIntegral {n : ℕ} (I : Finset ι) (a : ι → ℝ) (b c : ι → ℕ)
    (s : ES(ℝ, n)) : ℝ :=
  ∫ t1 in (0 : ℝ)..1, F_P_idx I a b c (consLp t1 s)

/-- The indicator integral over `[0,1]` equals the integral over `[0, 1 - P1' s]`. -/
theorem reduce_to_L {n : ℕ} (I : Finset ι) (a : ι → ℝ) (b c : ι → ℕ)
    (s : ES(ℝ, n)) (hs : ∀ i, 0 ≤ s i) (hP : P1' s ≤ 1) :
    (∫ t1 in (0 : ℝ)..1, F_P_idx I a b c (consLp t1 s)) =
      ∫ t1 in (0 : ℝ)..(1 - P1' s), polyP I a b c (consLp t1 s) := by
  have hsum0 : (0 : ℝ) ≤ ∑ i, s i := Finset.sum_nonneg (fun i _ ↦ hs i)
  have hPun : (∑ i, s i) ≤ 1 := hP
  have hL0 : 0 ≤ 1 - P1' s := by simp only [P1']; linarith
  have hmem : (1 - P1' s) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨hL0, ?_⟩
    simp only [P1']; linarith
  have hequiv : ∀ t1 : ℝ, t1 ∈ Set.Icc (0 : ℝ) 1 → (consLp t1 s ∈ 𝓡 (n + 1) ↔ t1 ≤ 1 - P1' s) := by
    intro t1 ht1
    change ((∀ i, 0 ≤ (consLp t1 s) i) ∧ ∑ i, (consLp t1 s) i ≤ 1) ↔ _
    rw [forall_consLp_nonneg, sum_consLp]
    constructor
    · rintro ⟨⟨_, _⟩, hsum⟩
      simp only [P1']; linarith
    · intro hcase
      refine ⟨⟨ht1.1, hs⟩, ?_⟩
      simp only [P1'] at hcase; linarith
  rw [show (∫ t1 in (0 : ℝ)..1, F_P_idx I a b c (consLp t1 s)) =
      ∫ t1 in (0 : ℝ)..1, {x : ℝ | x ≤ 1 - P1' s}.indicator
          (fun t1 ↦ polyP I a b c (consLp t1 s)) t1 from ?_]
  · exact intervalIntegral.integral_indicator hmem
  · apply intervalIntegral.integral_congr
    intro t1 ht1
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht1
    change (𝓡 (n + 1)).indicator (polyP I a b c) (consLp t1 s) =
       {x : ℝ | x ≤ 1 - P1' s}.indicator (fun t1 ↦ polyP I a b c (consLp t1 s)) t1
    by_cases hcase : t1 ≤ 1 - P1' s
    · rw [Set.indicator_of_mem ((hequiv t1 ht1).mpr hcase),
          Set.indicator_of_mem (show t1 ∈ {x : ℝ | x ≤ 1 - P1' s} from hcase)]
    · rw [Set.indicator_of_notMem (fun h ↦ hcase ((hequiv t1 ht1).mp h)),
          Set.indicator_of_notMem (show t1 ∉ {x : ℝ | x ≤ 1 - P1' s} from hcase)]

/-- The integral of `(L - t) ^ B * (t ^ 2 + Q) ^ C` equals its finite beta-integral expansion. -/
theorem term_integral (B C : ℕ) (L Q : ℝ) :
    (∫ t1 in (0 : ℝ)..L, (L - t1) ^ B * (t1 ^ 2 + Q) ^ C) = ∑ c' ∈ Finset.range (C + 1),
          (Nat.choose C c' : ℝ) * Q ^ c' *
          L ^ (B + 2 * C - 2 * c' + 1) *
          ((B ! : ℝ) * (2 * C - 2 * c')! /
            (B + 2 * C - 2 * c' + 1)!) := by
  have hexp : ∀ t1 : ℝ, (L - t1) ^ B * (t1 ^ 2 + Q) ^ C = ∑ c' ∈ Finset.range (C + 1),
          ((Nat.choose C c' : ℝ) * Q ^ c') * ((L - t1) ^ B * t1 ^ (2 * C - 2 * c')) := by
    intro t1
    rw [add_comm (t1 ^ 2) Q, add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c' _
    rw [← pow_mul, show 2 * (C - c') = 2 * C - 2 * c' from by omega]
    ring
  rw [show (∫ t1 in (0 : ℝ)..L, (L - t1) ^ B * (t1 ^ 2 + Q) ^ C) =
      ∫ t1 in (0 : ℝ)..L, ∑ c' ∈ Finset.range (C + 1),
          ((Nat.choose C c' : ℝ) * Q ^ c') * ((L - t1) ^ B * t1 ^ (2 * C - 2 * c')) from by
        apply intervalIntegral.integral_congr; intro t1 _; exact hexp t1]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro c' hc'
    rw [intervalIntegral.integral_const_mul,
      PrimeGaps.integral_complement_pow_mul_pow_all B (2 * C - 2 * c') L,
      show B + (2 * C - 2 * c') + 1 = B + 2 * C - 2 * c' + 1 from by
        have := Finset.mem_range.mp hc'; omega]
    ring
  · intro c' _
    apply Continuous.intervalIntegrable
    fun_prop

/-- If every `s i` is nonnegative and `P1' s ≤ 1`, then `innerIntegral` equals its explicit finite
sum. -/
theorem lem_inner_integral_1D_inline {n : ℕ} (I : Finset ι) (a : ι → ℝ) (b c : ι → ℕ)
    (s : ES(ℝ, n)) (hs : ∀ i, 0 ≤ s i) (hP : P1' s ≤ 1) :
    innerIntegral I a b c s = ∑ i ∈ I, a i *
        ∑ c' ∈ Finset.range (c i + 1), (Nat.choose (c i) c' : ℝ) * (P2' s) ^ c' *
          (1 - P1' s) ^ (b i + 2 * c i - 2 * c' + 1) *
          ((b i)! * (2 * c i - 2 * c')! /
            (b i + 2 * c i - 2 * c' + 1)!) := by
  unfold innerIntegral
  rw [reduce_to_L I a b c s hs hP]
  have hpoly : ∀ t1 : ℝ, polyP I a b c (consLp t1 s) =
      ∑ i ∈ I, a i * ((1 - P1' s) - t1) ^ (b i) * (t1 ^ 2 + P2' s) ^ (c i) := by
    intro t1
    unfold polyP
    apply Finset.sum_congr rfl
    intro i _
    rw [sum_consLp]
    have h2 : (∑ j, ((consLp t1 s) j) ^ 2) = t1 ^ 2 + P2' s := by
      rw [Fin.sum_univ_succ, consLp_zero]
      simp only [P2', consLp_succ]
    rw [h2]
    simp only [P1']
    ring
  rw [show (∫ t1 in (0 : ℝ)..(1 - P1' s), polyP I a b c (consLp t1 s)) = ∫ t1 in (0 : ℝ)..(1 -
    P1' s),
          ∑ i ∈ I, a i * ((1 - P1' s) - t1) ^ (b i) * (t1 ^ 2 + P2' s) ^ (c i) from by
        apply intervalIntegral.integral_congr; intro t1 _; exact hpoly t1]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [show (∫ t1 in (0 : ℝ)..(1 - P1' s), a i * ((1 - P1' s) - t1) ^ (b i) * (t1 ^ 2 + P2' s) ^
      (c i)) = a i * ∫ t1 in (0 : ℝ)..(1 - P1' s), ((1 - P1' s) - t1) ^ (b i) * (t1 ^ 2 + P2' s) ^
          (c i) from by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr; intro t1 _; ring]
    rw [term_integral (b i) (c i) (1 - P1' s) (P2' s)]
  · intro i _
    apply Continuous.intervalIntegrable
    fun_prop

/-- If every `s i` is nonnegative and `P1' s ≤ 1`, then the square of `innerIntegral` equals its
explicit double sum. -/
@[pg_tag "bg246" "lem_squared_inner_integral"]
theorem lem_squared_inner_integral {n : ℕ} (I : Finset ι) (a : ι → ℝ) (b c : ι → ℕ)
    (s : ES(ℝ, n)) (hs : ∀ i, 0 ≤ s i) (hP : P1' s ≤ 1) :
    (innerIntegral I a b c s) ^ 2 = ∑ i ∈ I, ∑ j ∈ I, a i * a j *
        ∑ c1' ∈ Finset.range (c i + 1), ∑ c2' ∈ Finset.range (c j + 1),
          (Nat.choose (c i) c1' : ℝ) * (Nat.choose (c j) c2') *
          (P2' s) ^ (c1' + c2') *
          (1 - P1' s) ^ (b i + b j + 2 * c i + 2 * c j - 2 * c1' - 2 * c2' + 2) *
          ((b i)! * (b j)! *
            (2 * c i - 2 * c1')! * (2 * c j - 2 * c2')! /
            ((b i + 2 * c i - 2 * c1' + 1)! *
             (b j + 2 * c j - 2 * c2' + 1)!)) := by
  set F : ι → ℕ → ℝ := fun i c' ↦ (Nat.choose (c i) c' : ℝ) * (P2' s) ^ c' *
      (1 - P1' s) ^ (b i + 2 * c i - 2 * c' + 1) *
      ((b i)! * (2 * c i - 2 * c')! /
        (b i + 2 * c i - 2 * c' + 1)!) with hF
  have h1 : innerIntegral I a b c s = ∑ i ∈ I, a i * ∑ c' ∈ Finset.range (c i + 1), F i c' :=
    lem_inner_integral_1D_inline I a b c s hs hP
  rw [h1, sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl (fun j _ ↦ ?_))
  rw [show (a i * ∑ c' ∈ Finset.range (c i + 1), F i c') *
        (a j * ∑ c' ∈ Finset.range (c j + 1), F j c') =
      a i * a j * ((∑ c' ∈ Finset.range (c i + 1), F i c') *
         (∑ c' ∈ Finset.range (c j + 1), F j c')) from by ring]
  congr 1
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun c1' hc1 ↦ Finset.sum_congr rfl (fun c2' hc2 ↦ ?_))
  have hc1' : c1' ≤ c i := by
    have := Finset.mem_range.mp hc1; omega
  have hc2' : c2' ≤ c j := by
    have := Finset.mem_range.mp hc2; omega
  simp only [hF]
  have hexp : (b i + 2 * c i - 2 * c1' + 1) + (b j + 2 * c j - 2 * c2' + 1) =
      b i + b j + 2 * c i + 2 * c j - 2 * c1' - 2 * c2' + 2 := by omega
  rw [← hexp, pow_add (1 - P1' s) (b i + 2 * c i - 2 * c1' + 1) (b j + 2 * c j - 2 * c2' + 1),
      pow_add (P2' s) c1' c2']
  ring

end

section

open scoped PrimeGaps

local notation "ES(" 𝕜:65 ", " k:65 ")" => EuclideanSpace 𝕜 (Fin k)

/-- The simplex-supported polynomial whose monomials are
`a i * (1 - ∑ j, x j) ^ (b i) * (∑ j, (x j) ^ 2) ^ (c i)`. -/
@[nolint defsWithUnderscore]
noncomputable def F_P_quad (d k : ℕ) (a : Fin d → ℝ) (b c : Fin d → ℕ) :
    EuclideanSpace ℝ (Fin k) → ℝ :=
  F_P_idx (k := k) (Finset.univ) a b c

/-- Integrating the coordinate `m` out of `F_P_quad` gives the same square-integral over the
simplex as integrating out the first coordinate: `F_P_idx` is symmetric in its coordinates,
so `insertLp m s t` may be replaced by `consLp s t`, and on the simplex the resulting inner
integral is `innerIntegral`. -/
private lemma integral_sq_marginal_insertLp_eq (d n : ℕ) (a : Fin d → ℝ) (b c : Fin d → ℕ)
    (m : Fin (n + 1)) :
    (∫ t in 𝓡 n, (∫ s in Set.Icc (0 : ℝ) (1 - ∑ i, t i),
          F_P_quad d (n + 1) a b c (insertLp m s t)) ^ 2) =
      ∫ t in 𝓡 n, (innerIntegral (Finset.univ) a b c t) ^ 2 := by
  have hmeas : MeasurableSet (𝓡 n) :=
    (EuclideanSpace.isClosed_scaledStdSimplex (k := n) (s := 1)).measurableSet
  unfold F_P_quad
  apply MeasureTheory.setIntegral_congr_fun hmeas
  intro t ht
  have htR : (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ 1 := ht
  obtain ⟨hnn, hsum⟩ := htR
  have hle : (0 : ℝ) ≤ 1 - ∑ i, t i := by linarith
  simp only []
  congr 1
  have hsym : ∀ s : ℝ, F_P_idx (Finset.univ) a b c (insertLp m s t) =
        F_P_idx (Finset.univ) a b c (consLp s t) := by
    intro s
    have hpoly : polyP (Finset.univ) a b c (insertLp m s t) =
        polyP (Finset.univ) a b c (consLp s t) := by
      unfold polyP
      have h1 : (∑ j, (insertLp m s t) j) = (∑ j, (consLp s t) j) := by
        rw [sum_insertLp, sum_consLp]
      have h2 : (∑ j, ((insertLp m s t) j) ^ 2) = (∑ j, ((consLp s t) j) ^ 2) := by
        rw [sq_sum_insertLp, Fin.sum_univ_succ, consLp_zero]
        simp only [consLp_succ]
      rw [h1, h2]
    unfold F_P_idx
    unfold Set.indicator
    rw [hpoly]
    by_cases h : insertLp m s t ∈ 𝓡 (n + 1)
    · rw [if_pos h, if_pos ((insertLp_mem_R_iff_consLp_mem_R m s t).mp h)]
    · rw [if_neg h, if_neg (fun hc ↦ h ((insertLp_mem_R_iff_consLp_mem_R m s t).mpr hc))]
  have hLHS : (∫ s in Set.Icc (0 : ℝ) (1 - ∑ i, t i),
        F_P_idx (Finset.univ) a b c (insertLp m s t)) = ∫ s in Set.Icc (0 : ℝ) (1 - ∑ i, t i),
        F_P_idx (Finset.univ) a b c (consLp s t) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    intro s _; exact hsym s
  rw [hLHS]
  change _ = ∫ t1 in (0 : ℝ)..1, F_P_idx (Finset.univ) a b c (consLp t1 t)
  rw [reduce_to_L Finset.univ a b c t hnn hsum]
  change (∫ s in Set.Icc (0 : ℝ) (1 - ∑ i, t i),
        F_P_idx (Finset.univ) a b c (consLp s t)) = ∫ t1 in (0 : ℝ)..(1 - ∑ i, t i),
        polyP Finset.univ a b c (consLp t1 t)
  rw [intervalIntegral.integral_of_le hle, MeasureTheory.integral_Icc_eq_integral_Ioc]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  have hmem : consLp s t ∈ 𝓡 (n + 1) := by
    refine ⟨?_, ?_⟩
    · rw [forall_consLp_nonneg]; exact ⟨le_of_lt hs.1, hnn⟩
    · rw [sum_consLp]; linarith [hs.2]
  change F_P_idx (Finset.univ) a b c (consLp s t) = polyP Finset.univ a b c (consLp s t)
  unfold F_P_idx
  rw [Set.indicator_of_mem hmem]

/-- The basic simplex moment: `∫_{𝓡 n} (1 − P1' t)^A · P2' t^q` equals
`A! / (n + 1 + A + 2q − 1)! · maynardG q 2 n`. -/
private lemma integral_one_sub_P1_pow_mul_P2_pow (n A q : ℕ) :
    (∫ t in 𝓡 n, (1 - P1' t) ^ A * P2' t ^ q) =
      (A ! : ℝ) / ((n + 1 + A + 2 * q - 1)! : ℝ) * (maynardG q 2 n : ℝ) := by
  rcases n with _ | nn
  · have hR0 : (𝓡 (0 : ℕ)) = (Set.univ : Set (ES(ℝ, 0))) := by
      ext t
      simp only [EuclideanSpace.scaledStdSimplex, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact ⟨fun i ↦ Fin.elim0 i, by simp⟩
    rw [hR0]
    have hint : ∀ t : ES(ℝ, 0), (1 - P1' t) ^ A * P2' t ^ q = (1 - (0 : ℝ)) ^ A * (0 : ℝ) ^ q := by
      intro t
      simp [P1', P2']
    rw [MeasureTheory.setIntegral_congr_fun MeasurableSet.univ (fun t _ ↦ hint t)]
    rw [MeasureTheory.setIntegral_const, volumeReal_univ_euclideanSpace_zero, one_smul]
    rcases q with _ | q'
    · have h01 : (0 + 1 + A + 2 * 0 - 1) = A := by omega
      rw [h01, maynardG_zero_fst, sub_zero, one_pow, pow_zero, mul_one]
      have hne : (A ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero A)
      field_simp
      norm_num
    · rw [zero_pow (Nat.succ_ne_zero q'), mul_zero]
      have hG : maynardG (q' + 1) 2 0 = 0 := by
        simp [maynardG]
      norm_num [hG]
  · have h := lem_integration_prime (nn + 2) (by omega) A q
    have he1 : nn + 2 - 1 = nn + 1 := by omega
    rw [he1] at h
    have he2 : nn + 2 + A + 2 * q - 1 = nn + 1 + 1 + A + 2 * q - 1 := by omega
    rw [he2] at h
    convert h using 2 with t
    unfold P1' P2'
    rfl

/-- The marginal integral of `F_P_quad` equals its explicit quadratic form in the coefficients. -/
@[pg_tag "bg246" "lem_quad_forms"]
theorem lem_quad_forms (d n : ℕ) (a : Fin d → ℝ) (b c : Fin d → ℕ) (m : Fin (n + 1)) :
    (∫ t in 𝓡 n, (∫ s in Set.Icc (0 : ℝ) (1 - ∑ i, t i),
          F_P_quad d (n + 1) a b c (insertLp m s t)) ^ 2) =
      ∑ i : Fin d, ∑ j : Fin d, a i * a j *
          ∑ c1' ∈ Finset.range (c i + 1), ∑ c2' ∈ Finset.range (c j + 1),
            ((c i).choose c1' : ℝ) * ((c j).choose c2' : ℝ) *
              ((PrimeGaps.gamma (b i) (b j) (c i) (c j) c1' c2' : ℚ) : ℝ) *
              (maynardG (c1' + c2') 2 n : ℝ) /
              (((n + 1) + b i + b j + 2 * c i + 2 * c j + 1)! : ℝ) := by
  have hmeas : MeasurableSet (𝓡 n) :=
    (EuclideanSpace.isClosed_scaledStdSimplex (k := n) (s := 1)).measurableSet
  have hcompact : IsCompact (𝓡 n) := EuclideanSpace.isCompact_scaledStdSimplex (k := n) (s := 1)
  have hInt : ∀ f : ES(ℝ, n) → ℝ, Continuous f →
      MeasureTheory.Integrable f (MeasureTheory.volume.restrict (𝓡 n)) :=
    fun f hf ↦ ContinuousOn.integrableOn_compact' hcompact hmeas hf.continuousOn
  have hcP1 : Continuous (P1' (n := n)) := by
    unfold P1'
    exact continuous_finsetSum _ (fun i _ ↦ PiLp.continuous_apply 2 _ i)
  have hcP2 : Continuous (P2' (n := n)) := by
    unfold P2'
    exact continuous_finsetSum _ (fun i _ ↦ (PiLp.continuous_apply 2 _ i).pow 2)
  have per_term : ∀ (i j : Fin d) (c1' c2' : ℕ), c1' ≤ c i → c2' ≤ c j → (∫ t in 𝓡 n,
        ((c i).choose c1' : ℝ) * ((c j).choose c2') * P2' t ^ (c1' + c2') *
          (1 - P1' t) ^ (b i + b j + 2 * c i + 2 * c j - 2 * c1' - 2 * c2' + 2) *
          ((b i)! * (b j)! * (2 * c i - 2 * c1')! *
            (2 * c j - 2 * c2')! /
            ((b i + 2 * c i - 2 * c1' + 1)! * (b j + 2 * c j - 2 * c2' + 1)!))) =
        ((c i).choose c1' : ℝ) * ((c j).choose c2' : ℝ) *
              ((PrimeGaps.gamma (b i) (b j) (c i) (c j) c1' c2' : ℚ) : ℝ) *
              (maynardG (c1' + c2') 2 n : ℝ) /
              (((n + 1) + b i + b j + 2 * c i + 2 * c j + 1)! : ℝ) := by
    intro i j c1' c2' hc1 hc2
    set A := b i + b j + 2 * c i + 2 * c j - 2 * c1' - 2 * c2' + 2 with hA
    set Q := c1' + c2' with hQ
    set κ : ℝ := ((c i).choose c1' : ℝ) * ((c j).choose c2') *
        ((b i)! * (b j)! * (2 * c i - 2 * c1')! *
          (2 * c j - 2 * c2')! /
          ((b i + 2 * c i - 2 * c1' + 1)! *
            (b j + 2 * c j - 2 * c2' + 1)!)) with hκ
    rw [MeasureTheory.setIntegral_congr_fun hmeas (g := fun t ↦
        κ * ((1 - P1' t) ^ A * P2' t ^ Q)) ?_]
    · rw [MeasureTheory.integral_const_mul]
      rw [integral_one_sub_P1_pow_mul_P2_pow n A Q]
      have hden : n + 1 + A + 2 * Q - 1 = (n + 1) + b i + b j + 2 * c i + 2 * c j + 1 := by
        simp only [hA, hQ]; omega
      rw [hden, hκ]
      unfold PrimeGaps.gamma
      push_cast
      ring
    · intro t _
      simp only [hκ]
      ring
  rw [integral_sq_marginal_insertLp_eq d n a b c m]
  rw [MeasureTheory.setIntegral_congr_fun hmeas (g := fun t ↦
      ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, a i * a j *
        ∑ c1' ∈ Finset.range (c i + 1), ∑ c2' ∈ Finset.range (c j + 1),
          ((c i).choose c1' : ℝ) * ((c j).choose c2') * P2' t ^ (c1' + c2') *
            (1 - P1' t) ^ (b i + b j + 2 * c i + 2 * c j - 2 * c1' - 2 * c2' + 2) *
            ((b i)! * (b j)! * (2 * c i - 2 * c1')! *
              (2 * c j - 2 * c2')! /
              ((b i + 2 * c i - 2 * c1' + 1)! *
                (b j + 2 * c j - 2 * c2' + 1)!))) ?_]
  · rw [MeasureTheory.integral_finsetSum _ (fun i _ ↦ hInt _ (by fun_prop))]
    apply Finset.sum_congr rfl
    intro i _
    rw [MeasureTheory.integral_finsetSum _ (fun j _ ↦ hInt _ (by fun_prop))]
    apply Finset.sum_congr rfl
    intro j _
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.integral_finsetSum _ (fun c1' _ ↦ hInt _ (by fun_prop))]
    apply Finset.sum_congr rfl
    intro c1' hc1'
    rw [MeasureTheory.integral_finsetSum _ (fun c2' _ ↦ hInt _ (by fun_prop))]
    apply Finset.sum_congr rfl
    intro c2' hc2'
    rw [Finset.mem_range, Nat.lt_succ_iff] at hc1' hc2'
    exact per_term i j c1' c2' hc1' hc2'
  · intro t ht
    have htR : (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ 1 := ht
    obtain ⟨hnn, hsum⟩ := htR
    have h1 : P1' t ≤ 1 := by
      change ∑ i, t i ≤ 1; exact hsum
    exact lem_squared_inner_integral Finset.univ a b c t hnn h1

end

end PrimeGaps

end
