/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import PrimeGapsTheory.Analysis.Simplex

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Positive-definite Gram matrices

Positive-definiteness results for Gram matrices of square-integrable functions and their
marginals on simplices.

## Main definitions

* `PrimeGaps.marginal`: A one-coordinate marginal on a simplex.
* `PrimeGaps.Jfunctional`: The bilinear integral of two marginals.
* `PrimeGaps.A2`: The Gram matrix obtained by summing the marginal bilinear forms.

## Main results

* `lem_A1_posdef`: A scaled Gram matrix of linearly independent functions is positive definite.
* `PrimeGaps.main_A2_posDef`: The marginal quadratic form is positive on nonzero coefficients.
* `PrimeGaps.main_A2_PosDef_matrix`: The marginal Gram matrix is positive definite.
-/

@[expose] public section

open scoped Matrix

open MeasureTheory Matrix

namespace MainTheoremHelpers

/-- The product `ft i x * ft j x` is integrable when each `(ft k)^2` is integrable. -/
private lemma prod_integrable {α : Type*} [MeasurableSpace α] {μ : Measure α} {d : ℕ}
    {ft : Fin d → α → ℝ} (hft_meas : ∀ i, Measurable (ft i))
    (hft_sq_int : ∀ i, Integrable (fun x ↦ (ft i x) ^ 2) μ) (i j : Fin d) :
    Integrable (fun x ↦ ft i x * ft j x) μ := by
  refine (((hft_sq_int i).add (hft_sq_int j)).div_const 2).mono'
    ((hft_meas i).mul (hft_meas j)).aestronglyMeasurable
    (.of_forall fun x ↦ ?_)
  simp only [Pi.add_apply, Real.norm_eq_abs, abs_le]
  exact ⟨by nlinarith [sq_nonneg (ft i x + ft j x)],
    by nlinarith [sq_nonneg (ft i x - ft j x)]⟩

/-- Expansion of a squared sum as a double sum of products. -/
private lemma sum_mul_sq_expand {d : ℕ} (x g : Fin d → ℝ) :
    (∑ i, x i * g i) ^ 2 = ∑ i, ∑ j, x i * x j * (g i * g j) := by
  rw [sq, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

/-- The linear combination `∑ i, x i * ft i` has integrable square. -/
private lemma sum_sq_integrable {α : Type*} [MeasurableSpace α] {μ : Measure α} {d : ℕ}
    {ft : Fin d → α → ℝ} (hft_meas : ∀ i, Measurable (ft i))
    (hft_sq_int : ∀ i, Integrable (fun x ↦ (ft i x) ^ 2) μ) (x : Fin d → ℝ) :
    Integrable (fun y ↦ (∑ i, x i * ft i y) ^ 2) μ := by
  simp_rw [fun y ↦ sum_mul_sq_expand x (fun i ↦ ft i y)]
  exact integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
    (prod_integrable hft_meas hft_sq_int i j).const_mul (x i * x j)

/-- The quadratic form equals `k * ∫ (∑ i, x i * ft i y)^2 ∂μ`. -/
private lemma quadForm_eq_integral {α : Type*} [MeasurableSpace α] {μ : Measure α} {d : ℕ}
    {ft : Fin d → α → ℝ} (hft_meas : ∀ i, Measurable (ft i))
    (hft_sq_int : ∀ i, Integrable (fun x ↦ (ft i x) ^ 2) μ) (k : ℕ) (x : Fin d → ℝ) :
    (∑ i, ∑ j, x i * ((k : ℝ) * ∫ y, ft i y * ft j y ∂μ) * x j) =
      (k : ℝ) * ∫ y, (∑ i, x i * ft i y) ^ 2 ∂μ := by
  simp_rw [fun y ↦ sum_mul_sq_expand x (fun i ↦ ft i y)]
  have hint : ∀ i j : Fin d, Integrable (fun y ↦ x i * x j * (ft i y * ft j y)) μ :=
    fun i j ↦ (prod_integrable hft_meas hft_sq_int i j).const_mul (x i * x j)
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j]
  simp_rw [integral_finsetSum _ fun j _ ↦ hint _ j, integral_const_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

/-- The integral `∫ y, (∑ i, x i * ft i y)^2 ∂μ` is strictly positive for `x ≠ 0`. -/
private lemma integral_sum_sq_pos {α : Type*} [MeasurableSpace α] {μ : Measure α} {d : ℕ}
    {ft : Fin d → α → ℝ} (hft_meas : ∀ i, Measurable (ft i))
    (hft_sq_int : ∀ i, Integrable (fun x ↦ (ft i x) ^ 2) μ)
    (hft_lin_indep : ∀ a : Fin d → ℝ, (∀ᵐ x ∂μ, (∑ i, a i * ft i x) = 0) → a = 0)
    {x : Fin d → ℝ} (hx : x ≠ 0) :
    0 < ∫ y, (∑ i, x i * ft i y) ^ 2 ∂μ := by
  have h_nonneg : ∀ y, 0 ≤ (∑ i, x i * ft i y) ^ 2 := fun y ↦ sq_nonneg _
  refine lt_of_le_of_ne (integral_nonneg h_nonneg) fun heq ↦ hx <| hft_lin_indep x ?_
  have h_ae_sq : (fun y ↦ (∑ i, x i * ft i y) ^ 2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg h_nonneg (sum_sq_integrable hft_meas hft_sq_int x)).mp heq.symm
  filter_upwards [h_ae_sq] with y hy using sq_eq_zero_iff.mp (by simpa using hy)

end MainTheoremHelpers

open MainTheoremHelpers

namespace MeasureTheory

/-- Gram matrix of linearly-independent L² functions scaled by k is positive definite. -/
@[pg_tag "bg246" "lem_A1_posdef"]
theorem lem_A1_posdef {d : ℕ} {α : Type*} [MeasurableSpace α] (μ : Measure α) (k : ℕ) (hk : 0 < k)
    (ft : Fin d → α → ℝ) (hft_meas : ∀ i, Measurable (ft i))
    (hft_sq_int : ∀ i, Integrable (fun x ↦ (ft i x) ^ 2) μ)
    (hft_lin_indep : ∀ a : Fin d → ℝ, (∀ᵐ x ∂μ, (∑ i, a i * ft i x) = 0) → a = 0) :
    let A : Matrix (Fin d) (Fin d) ℝ := fun i j ↦ (k : ℝ) * ∫ x, ft i x * ft j x ∂μ
    A.PosDef := by
  intro A
  refine ⟨?_, fun x hx ↦ ?_⟩
  · ext i j
    simp only [A]
    exact congr_arg _ (integral_congr_ae (by filter_upwards with x using by ring))
  · have hx' : (fun i ↦ x i) ≠ 0 :=
      fun heq ↦ hx (by ext i; simpa using congr_fun heq i)
    rw [show x.sum (fun i xi ↦ x.sum fun j xj ↦ star xi * A i j * xj) =
        ∑ i, ∑ j, x i * A i j * x j by
      rw [Finsupp.sum_fintype _ _ (by intro; simp)]
      exact Finset.sum_congr rfl fun i _ ↦ by
        rw [Finsupp.sum_fintype _ _ (by intro; ring)]
        simp]
    rw [quadForm_eq_integral hft_meas hft_sq_int k]
    exact mul_pos (by exact_mod_cast hk) (integral_sum_sq_pos hft_meas hft_sq_int hft_lin_indep hx')

end MeasureTheory

open scoped PrimeGaps

open Finset

namespace PrimeGaps

/-- The `m`-th marginal `T_m F : 𝓡_{k} → ℝ` (the outer variables live in
`EuclideanSpace ℝ (Fin k)`).  It integrates out the variable inserted at position `m` over its
admissible range `[0, 1 - ∑ i, t i]`, where `t` ranges over the outer simplex `𝓡 k`.

Here the ambient dimension is `k + 1`, so `m : Fin (k + 1)` and the resulting function is on
`EuclideanSpace ℝ (Fin k)`. The inserted variable is placed at position `m` via
`Fin.insertNth`, after transporting `t` from `EuclideanSpace ℝ (Fin k)` to `Fin k → ℝ`. -/
noncomputable def marginal {k : ℕ} (m : Fin (k + 1))
    (F : (Fin (k + 1) → ℝ) → ℝ) (t : EuclideanSpace ℝ (Fin k)) : ℝ :=
  ∫ s in Set.Icc (0 : ℝ) (1 - ∑ i, t i), F (m.insertNth s t.ofLp)

/-- The bilinear functional
`J_k^{(m)}(F, G) = ∫_{𝓡_k} (T_m F)(T_m G)`,
the integral of the product of the `m`-th marginals over the outer simplex `𝓡 k` (in the
`EuclideanSpace ℝ (Fin k)` variables). -/
noncomputable def Jfunctional {k : ℕ} (m : Fin (k + 1)) (F G : (Fin (k + 1) → ℝ) → ℝ) : ℝ :=
  ∫ t in 𝓡 k, marginal m F t * marginal m G t

/-- The trial function `F = ∑ n, c n • P n` built from the basis `P` and coefficients `c`. -/
noncomputable def trial {k d : ℕ} (P : Fin d → (Fin (k + 1) → ℝ) → ℝ)
    (c : Fin d → ℝ) : (Fin (k + 1) → ℝ) → ℝ :=
  fun t ↦ ∑ n, c n * P n t

/-- The Gram matrix `A_2`, with entries `(A_2)_{i,j} = ∑_{m} J_k^{(m)}(P_i, P_j)`. -/
noncomputable def A2 {k d : ℕ} (P : Fin d → (Fin (k + 1) → ℝ) → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j ↦ ∑ m : Fin (k + 1), Jfunctional m (P i) (P j)

/-- The quadratic form `c ↦ ∑_{m} J_k^{(m)}(F, F)` with `F = ∑_n c_n P_n`; this is the value
`c^{\mathsf T} A_2 c`. -/
noncomputable def quadForm {k d : ℕ} (P : Fin d → (Fin (k + 1) → ℝ) → ℝ) (c : Fin d → ℝ) : ℝ :=
  ∑ m : Fin (k + 1), Jfunctional m (trial P c) (trial P c)

/-- Under square-integrability and marginal linearity,
`J_k^{(m)}(F, F) = ∑_{i,j} c_i c_j J_k^{(m)}(P_i, P_j)` for `F = ∑_n c_n P_n`. -/
theorem Jfunctional_trial_expand {k d : ℕ} (P : Fin d → (Fin (k + 1) → ℝ) → ℝ)
    (hmem : ∀ (m : Fin (k + 1)) (n : Fin d), MemLp (marginal m (P n)) 2 (volume.restrict (𝓡 k)))
    (hlin : ∀ (m : Fin (k + 1)) (c : Fin d → ℝ), marginal m (trial P c)
        =ᶠ[ae (volume.restrict (𝓡 k))]
        (fun t ↦ ∑ n, c n * marginal m (P n) t))
    (m : Fin (k + 1)) (c : Fin d → ℝ) :
    Jfunctional m (trial P c) (trial P c) = ∑ i, ∑ j, c i * c j * Jfunctional m (P i) (P j) := by
  set μ := volume.restrict (𝓡 k) with hμ
  have hstep1 : Jfunctional m (trial P c) (trial P c) =
      ∫ t, (∑ i, c i * marginal m (P i) t) * (∑ j, c j * marginal m (P j) t) ∂μ := by
    rw [Jfunctional]
    apply integral_congr_ae
    filter_upwards [hlin m c] with t ht
    rw [ht]
  rw [hstep1]
  simp_rw [Finset.sum_mul_sum]
  have hint : ∀ i j, Integrable
      (fun t ↦ (c i * marginal m (P i) t) * (c j * marginal m (P j) t)) μ := by
    intro i j
    have h1 : MemLp (fun t ↦ c i * marginal m (P i) t) 2 μ := (hmem m i).const_mul (c i)
    have h2 : MemLp (fun t ↦ c j * marginal m (P j) t) 2 μ := (hmem m j).const_mul (c j)
    exact h1.integrable_mul h2
  rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hint i j))]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [integral_finsetSum _ (fun j _ ↦ hint i j)]
  refine Finset.sum_congr rfl (fun j _ ↦ ?_)
  rw [Jfunctional, show (fun t ↦ (c i * marginal m (P i) t) * (c j * marginal m (P j) t)) =
        (fun t ↦ (c i * c j) * (marginal m (P i) t * marginal m (P j) t)) from
        funext fun t ↦ by ring, integral_const_mul]

/-- If the marginals of `P` are square-integrable and linear in trial functions, and the
first marginals are linearly independent in `L²`, then `quadForm P c` is positive for every
nonzero `c`. -/
theorem main_A2_posDef {k d : ℕ} (P : Fin d → (Fin (k + 1) → ℝ) → ℝ)
    (hmem : ∀ (m : Fin (k + 1)) (n : Fin d), MemLp (marginal m (P n)) 2 (volume.restrict (𝓡 k)))
    (hlin : ∀ (m : Fin (k + 1)) (c : Fin d → ℝ), marginal m (trial P c)
        =ᶠ[ae (volume.restrict (𝓡 k))]
        (fun t ↦ ∑ n, c n * marginal m (P n) t))
    (hindep : ∀ c : Fin d → ℝ, (fun t ↦ ∑ n, c n * marginal 0 (P n) t)
          =ᶠ[ae (volume.restrict (𝓡 k))] 0 → c = 0) :
    ∀ c : Fin d → ℝ, c ≠ 0 → 0 < quadForm P c := by
  intro c hc
  set μ := volume.restrict (𝓡 k) with hμ
  set g : EuclideanSpace ℝ (Fin k) → ℝ := fun t ↦ ∑ n, c n * marginal 0 (P n) t with hg
  have hgL2 : MemLp g 2 μ := by
    have hrw : g = ∑ n, fun t ↦ c n * marginal 0 (P n) t := by
      rw [hg]; ext t; rw [Finset.sum_apply]
    rw [hrw]
    exact memLp_finsetSum' _ fun n _ ↦ (hmem 0 n).const_mul (c n)
  have hgg_int : Integrable (fun t ↦ g t * g t) μ := hgL2.integrable_mul hgL2
  have hterm_nonneg : ∀ m : Fin (k + 1), 0 ≤ Jfunctional m (trial P c) (trial P c) :=
    fun m ↦ integral_nonneg fun t ↦ mul_self_nonneg _
  have hterm0 : Jfunctional 0 (trial P c) (trial P c) = ∫ t, g t * g t ∂μ := by
    rw [Jfunctional]
    apply integral_congr_ae
    filter_upwards [hlin 0 c] with t ht
    rw [ht]
  have hterm0_pos : 0 < Jfunctional 0 (trial P c) (trial P c) := by
    rw [hterm0]
    refine (integral_nonneg fun t ↦ mul_self_nonneg (g t)).lt_of_ne fun h ↦ hc (hindep c ?_)
    have hzero : (fun t ↦ g t * g t) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun t ↦ mul_self_nonneg (g t)) hgg_int).mp h.symm
    filter_upwards [hzero] with t ht
    simpa [mul_self_eq_zero] using ht
  rw [quadForm]
  refine lt_of_lt_of_le hterm0_pos ?_
  exact Finset.single_le_sum (fun m _ ↦ hterm_nonneg m) (Finset.mem_univ 0)

/-- `A2` is a symmetric matrix (Gram matrix of a symmetric bilinear form). -/
theorem A2_isSymm {k d : ℕ} (P : Fin d → (Fin (k + 1) → ℝ) → ℝ) : (A2 (k := k) P).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, A2, Jfunctional]
  exact Finset.sum_congr rfl fun m _ ↦
    integral_congr_ae (.of_forall fun t ↦ by ring)

/-- The matrix quadratic form of `A2 P` at `c` equals `quadForm P c`. -/
theorem A2_quadForm_eq {k d : ℕ} (P : Fin d → (Fin (k + 1) → ℝ) → ℝ)
    (hmem : ∀ (m : Fin (k + 1)) (n : Fin d), MemLp (marginal m (P n)) 2 (volume.restrict (𝓡 k)))
    (hlin : ∀ (m : Fin (k + 1)) (c : Fin d → ℝ), marginal m (trial P c)
        =ᶠ[ae (volume.restrict (𝓡 k))]
        (fun t ↦ ∑ n, c n * marginal m (P n) t))
    (c : Fin d → ℝ) :
    (Matrix.toBilin' (A2 P)) c c = quadForm P c := by
  set μ := volume.restrict (𝓡 k) with hμ
  rw [Matrix.toBilin'_apply']
  have hLHS : c ⬝ᵥ (A2 P) *ᵥ c = ∑ i, ∑ j, c i * c j * A2 P i j := by
    simp only [dotProduct, Matrix.mulVec]
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ ↦ ?_)
    ring
  rw [hLHS, quadForm]
  have hexp : ∀ m : Fin (k + 1), Jfunctional m (trial P c) (trial P c) =
      ∑ i, ∑ j, c i * c j * Jfunctional m (P i) (P j) :=
    fun m ↦ Jfunctional_trial_expand P hmem hlin m c
  simp_rw [hexp]
  have hLHS2 : ∑ i, ∑ j, c i * c j * A2 P i j =
      ∑ i, ∑ j, c i * c j * (∑ m : Fin (k + 1), Jfunctional m (P i) (P j)) := rfl
  have hRHS2 : ∑ m : Fin (k + 1), ∑ i, ∑ j, c i * c j * Jfunctional m (P i) (P j) =
      ∑ i, ∑ j, c i * c j * (∑ m : Fin (k + 1), Jfunctional m (P i) (P j)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ ↦ ?_)
    rw [Finset.mul_sum]
  rw [hLHS2, hRHS2]

/-- If the marginals of `P` satisfy the stated integrability, linearity, and independence
hypotheses, then `A2 P` is positive definite. -/
@[pg_tag "bg246" "lem_A2_posdef"]
theorem main_A2_PosDef_matrix {k d : ℕ} (P : Fin d → (Fin (k + 1) → ℝ) → ℝ)
    (hmem : ∀ (m : Fin (k + 1)) (n : Fin d), MemLp (marginal m (P n)) 2 (volume.restrict (𝓡 k)))
    (hlin : ∀ (m : Fin (k + 1)) (c : Fin d → ℝ), marginal m (trial P c)
        =ᶠ[ae (volume.restrict (𝓡 k))]
        (fun t ↦ ∑ n, c n * marginal m (P n) t))
    (hindep : ∀ c : Fin d → ℝ, (fun t ↦ ∑ n, c n * marginal 0 (P n) t)
          =ᶠ[ae (volume.restrict (𝓡 k))] 0 → c = 0) :
    (A2 P).PosDef := by
  constructor
  · change (A2 P).IsHermitian
    rw [Matrix.IsHermitian]
    have hH : (A2 P)ᴴ = (A2 P)ᵀ := by
      ext i j; simp [Matrix.conjTranspose, Matrix.transpose]
    rw [hH]
    exact A2_isSymm P
  · intro x hx
    set c : Fin d → ℝ := fun i ↦ x i with hc
    have hcne : c ≠ 0 := fun h ↦ hx <| by ext i; simpa [hc] using congr_fun h i
    have hpos : 0 < quadForm P c := main_A2_posDef P hmem hlin hindep c hcne
    have heq : (Matrix.toBilin' (A2 P)) c c = quadForm P c := A2_quadForm_eq P hmem hlin c
    rw [Matrix.toBilin'_apply'] at heq
    have hsum : (x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * A2 P i j * xj) =
        c ⬝ᵥ (A2 P) *ᵥ c := by
      rw [dotProduct, Finsupp.sum_fintype]
      · refine Finset.sum_congr rfl (fun i _ ↦ ?_)
        rw [Matrix.mulVec, dotProduct, Finset.mul_sum, Finsupp.sum_fintype]
        · refine Finset.sum_congr rfl (fun j _ ↦ ?_)
          simp only [star_trivial, hc]
          ring
        · intro j; simp
      · intro i
        rw [Finsupp.sum_fintype]
        · simp
        · intro j; simp
    rwa [hsum, heq]

end PrimeGaps
