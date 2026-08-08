/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.Matrix.Order

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Generalised Rayleigh quotient

For real positive-definite matrices `A₁` and `A₂`, the maximum of
`(aᵀ A₂ a) / (aᵀ A₁ a)` over nonzero `a` is the largest generalised eigenvalue of the pair,
equivalently the largest element of `spectrum ℝ (A₁⁻¹ * A₂)`.

## Main results

* `lem_rayleigh`: The generalised Rayleigh quotient attains the largest generalised eigenvalue.

The general matrix facts the proof rests on are stated in the `Matrix` namespace:

* `Matrix.PosDef.exists_eq_mul_transpose`: A real positive-definite matrix factors as `L * Lᵀ`
  with `L` invertible.
* `Matrix.IsHermitian.dotProduct_mulVec_eq_sum_eigenvalues_mul_sq`: The spectral decomposition
  of a real Hermitian quadratic form.
* `Matrix.IsHermitian.dotProduct_mulVec_le_of_eigenvalues_le`: The Rayleigh upper bound for a
  real Hermitian quadratic form.
* `Matrix.mem_spectrum_iff_exists_mulVec_eq_smul`: Membership in the spectrum is the existence
  of a nonzero eigenvector.
-/

@[expose] public section

open scoped Matrix

open Matrix
open scoped InnerProductSpace MatrixOrder

namespace Matrix

/-- Every real positive-definite matrix `A` factors as `L * Lᵀ` with `L` invertible. -/
lemma PosDef.exists_eq_mul_transpose {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosDef) :
    ∃ L : Matrix (Fin d) (Fin d) ℝ, IsUnit L.det ∧ A = L * Lᵀ := by
  classical
  obtain ⟨B, hB, hBA⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
    hA.isStrictlyPositive
  refine ⟨Bᵀ, ?_, ?_⟩
  · rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det B).mp hB
  · rw [Matrix.transpose_transpose, hBA, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]

/-- The quadratic form of `L * Lᵀ` at `a` is the squared length of `Lᵀ a`. -/
lemma dotProduct_mul_transpose_mulVec {d : ℕ} (L : Matrix (Fin d) (Fin d) ℝ) (a : Fin d → ℝ) :
    a ⬝ᵥ (L * Lᵀ) *ᵥ a = (Lᵀ *ᵥ a) ⬝ᵥ (Lᵀ *ᵥ a) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

/-- Conjugating the quadratic form of `A₂` by `(L⁻¹)ᵀ` yields the quadratic form of
`L⁻¹ * A₂ * (L⁻¹)ᵀ`. -/
private lemma dotProduct_mulVec_conj_subst {d : ℕ}
    (A₂ L : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) :
    ((L⁻¹)ᵀ *ᵥ b) ⬝ᵥ A₂.mulVec ((L⁻¹)ᵀ *ᵥ b) = b ⬝ᵥ (L⁻¹ * A₂ * (L⁻¹)ᵀ) *ᵥ b := by
  have adj : ∀ (M : Matrix (Fin d) (Fin d) ℝ) (x y : Fin d → ℝ),
      M.mulVec x ⬝ᵥ y = x ⬝ᵥ Mᵀ *ᵥ y := fun M x y ↦ by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rw [adj, Matrix.transpose_transpose, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/-- If `L` is invertible then `Lᵀ` sends nonzero vectors to nonzero vectors. -/
private lemma transpose_mulVec_ne_zero {d : ℕ} (L : Matrix (Fin d) (Fin d) ℝ)
    (hL : IsUnit L.det) (v : Fin d → ℝ) (hv : v ≠ 0) :
    Lᵀ *ᵥ v ≠ 0 := by
  have hLT : IsUnit Lᵀ := (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.det_transpose L ▸ hL)
  exact fun h ↦ hv (((Matrix.mulVec_injective_of_isUnit hLT).eq_iff' (Matrix.mulVec_zero _)).mp h)

/-- If `L` is invertible then `(L⁻¹)ᵀ` sends nonzero vectors to nonzero vectors. -/
private lemma invTranspose_mulVec_ne_zero {d : ℕ} (L : Matrix (Fin d) (Fin d) ℝ)
    (hL : IsUnit L.det) (v : Fin d → ℝ) (hv : v ≠ 0) :
    (L⁻¹)ᵀ *ᵥ v ≠ 0 := by
  refine transpose_mulVec_ne_zero L⁻¹ ?_ v hv
  rw [Matrix.det_nonsing_inv]
  exact hL.ringInverse

/-- `(L⁻¹)ᵀ.mulVec (Lᵀ.mulVec a) = a` when `L` is invertible. -/
private lemma invTranspose_mulVec_transpose_mulVec {d : ℕ} (L : Matrix (Fin d) (Fin d) ℝ)
    (hL : IsUnit L.det) (a : Fin d → ℝ) :
    (L⁻¹)ᵀ *ᵥ (Lᵀ *ᵥ a) = a := by
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hL,
      Matrix.transpose_one, Matrix.one_mulVec]

/-- Each vector of `hB.eigenvectorBasis` is nonzero, being a unit vector. -/
private lemma eigenvectorBasis_ne_zero {d : ℕ} {B : Matrix (Fin d) (Fin d) ℝ}
    (hB : B.IsHermitian) (i : Fin d) :
    (fun j ↦ (hB.eigenvectorBasis i : EuclideanSpace ℝ (Fin d)) j) ≠ 0 := fun h ↦
  hB.eigenvectorBasis.orthonormal.ne_zero i (by ext j; simpa using congrFun h j)

/-- For `b : Fin d → ℝ`, `b ⬝ᵥ b` equals the squared norm of the lift to
`EuclideanSpace ℝ (Fin d)`. -/
private lemma dotProduct_eq_norm_sq_euclideanSpace {d : ℕ} (b : Fin d → ℝ) :
    b ⬝ᵥ b = ‖(WithLp.toLp 2 b : EuclideanSpace ℝ (Fin d))‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ ↦ sq_nonneg _))]
  simp [dotProduct, sq, Real.norm_eq_abs]

/-- The real inner product on `EuclideanSpace ℝ (Fin d)` agrees with the
`dotProduct` of the underlying functions. -/
private lemma inner_euclidean_eq_dotProduct {d : ℕ} (u v : EuclideanSpace ℝ (Fin d)) :
    ⟪u, v⟫_ℝ = (fun j ↦ (u : EuclideanSpace ℝ (Fin d)) j) ⬝ᵥ
      (fun j ↦ (v : EuclideanSpace ℝ (Fin d)) j) := by
  rw [PiLp.inner_apply]
  unfold dotProduct
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  change v.ofLp i * u.ofLp i = u.ofLp i * v.ofLp i
  exact mul_comm _ _

/-- Parseval identity for an orthonormal basis of `EuclideanSpace ℝ (Fin d)`,
expressed in `dotProduct` form. -/
private lemma euclidean_dotProduct_sum_orthonormal {d : ℕ}
    (basis : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (b : Fin d → ℝ) :
    b ⬝ᵥ b = ∑ i, (b ⬝ᵥ (fun j ↦ (basis i : EuclideanSpace ℝ (Fin d)) j)) ^ 2 := by
  set b' : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 b with hb'
  rw [dotProduct_eq_norm_sq_euclideanSpace b, ← hb', ← OrthonormalBasis.sum_sq_inner_left basis b']
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  congr 1
  rw [inner_euclidean_eq_dotProduct]

/-- Parseval in the eigenbasis of a Hermitian `B`: `b ⬝ᵥ b = ∑ i, (b ⬝ᵥ eigenvectorBasis i) ^ 2`. -/
private lemma norm_sq_eq_sum_eigenbasis_coeffs {d : ℕ} {B : Matrix (Fin d) (Fin d) ℝ}
    (hB : B.IsHermitian) (b : Fin d → ℝ) :
    b ⬝ᵥ b = ∑ i : Fin d,
      (b ⬝ᵥ (fun j ↦ (hB.eigenvectorBasis i : EuclideanSpace ℝ (Fin d)) j)) ^ 2 :=
  euclidean_dotProduct_sum_orthonormal hB.eigenvectorBasis b

/-- Expansion of a vector in the orthonormal eigenbasis (function form). -/
private lemma b_eq_sum_eigenbasis {d : ℕ} {B : Matrix (Fin d) (Fin d) ℝ}
    (hB : B.IsHermitian) (b : Fin d → ℝ) :
    b = ∑ i : Fin d, (b ⬝ᵥ (fun j ↦ (hB.eigenvectorBasis i : EuclideanSpace ℝ (Fin d)) j)) •
        (fun j ↦ (hB.eigenvectorBasis i : EuclideanSpace ℝ (Fin d)) j) := by
  set basis := hB.eigenvectorBasis
  set b' : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 b
  have hcoef : ∀ i : Fin d, (basis.repr b').ofLp i =
      b ⬝ᵥ (fun j ↦ (basis i : EuclideanSpace ℝ (Fin d)) j) := fun i ↦ by
    rw [OrthonormalBasis.repr_apply_apply, EuclideanSpace.inner_eq_star_dotProduct]
    change (b ⬝ᵥ star (fun j ↦ (basis i : EuclideanSpace ℝ (Fin d)) j)) = b ⬝ᵥ _
    rfl
  have h2 : ((∑ i, (basis.repr b').ofLp i • basis i : EuclideanSpace ℝ (Fin d))).ofLp =
      b'.ofLp := congrArg _ (basis.sum_repr b')
  have hsum : ((∑ i, (basis.repr b').ofLp i • basis i : EuclideanSpace ℝ (Fin d))).ofLp =
      ∑ i, ((basis.repr b').ofLp i • basis i : EuclideanSpace ℝ (Fin d)).ofLp :=
    map_sum (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)) _ _
  rw [hsum] at h2
  simp_rw [← hcoef]
  exact h2.symm

/-- Spectral decomposition of a real Hermitian quadratic form: `b ⬝ᵥ B *ᵥ b` is the
eigenvalue-weighted sum of the squared eigenbasis coefficients of `b`. -/
lemma IsHermitian.dotProduct_mulVec_eq_sum_eigenvalues_mul_sq {d : ℕ}
    {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.IsHermitian) (b : Fin d → ℝ) :
    b ⬝ᵥ B.mulVec b = ∑ i : Fin d, hB.eigenvalues i *
        (b ⬝ᵥ (fun j ↦ (hB.eigenvectorBasis i : EuclideanSpace ℝ (Fin d)) j)) ^ 2 := by
  set v : Fin d → (Fin d → ℝ) := fun i j ↦ (hB.eigenvectorBasis i : EuclideanSpace ℝ (Fin d)) j
  have hBb : B.mulVec b = ∑ i, ((b ⬝ᵥ v i) * hB.eigenvalues i) • v i := by
    conv_lhs => rw [b_eq_sum_eigenbasis hB b]
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    rw [Matrix.mulVec_smul, hB.mulVec_eigenvectorBasis i, smul_smul]
  rw [hBb, dotProduct_sum]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [dotProduct_smul, smul_eq_mul]
  ring

/-- Rayleigh upper bound: if `i₀` maximises the eigenvalues of a real Hermitian `B` then
`b ⬝ᵥ B *ᵥ b ≤ hB.eigenvalues i₀ * (b ⬝ᵥ b)` for every `b`. -/
lemma IsHermitian.dotProduct_mulVec_le_of_eigenvalues_le {d : ℕ}
    {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.IsHermitian) (i₀ : Fin d)
    (hmax : ∀ i : Fin d, hB.eigenvalues i ≤ hB.eigenvalues i₀)
    (b : Fin d → ℝ) :
    b ⬝ᵥ B.mulVec b ≤ hB.eigenvalues i₀ * (b ⬝ᵥ b) := by
  rw [hB.dotProduct_mulVec_eq_sum_eigenvalues_mul_sq b,
      norm_sq_eq_sum_eigenbasis_coeffs hB b, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  have h_sq := sq_nonneg (b ⬝ᵥ (fun j ↦ (hB.eigenvectorBasis i : EuclideanSpace ℝ (Fin d)) j))
  nlinarith [hmax i]

/-- A real positive-definite matrix has a largest eigenvalue, attained by a nonzero
eigenvector, which bounds its quadratic form. -/
private lemma posDef_max_eig_quadForm {d : ℕ} [NeZero d]
    {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.PosDef) :
    ∃ μ : ℝ, ∃ b₀ : Fin d → ℝ,
      b₀ ≠ 0 ∧ B.mulVec b₀ = μ • b₀ ∧ (∀ b : Fin d → ℝ, b ⬝ᵥ B.mulVec b ≤ μ * (b ⬝ᵥ b)) ∧
      (∀ ν : ℝ, (∃ b : Fin d → ℝ, b ≠ 0 ∧ B.mulVec b = ν • b) → ν ≤ μ) := by
  have hB_herm : B.IsHermitian := hB.isHermitian
  obtain ⟨i₀, -, hmax'⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin d))
    hB_herm.eigenvalues Finset.univ_nonempty
  have hmax : ∀ i : Fin d, hB_herm.eigenvalues i ≤ hB_herm.eigenvalues i₀ :=
    fun i ↦ hmax' i (Finset.mem_univ i)
  refine ⟨hB_herm.eigenvalues i₀,
    (fun j ↦ (hB_herm.eigenvectorBasis i₀ : EuclideanSpace ℝ (Fin d)) j),
    eigenvectorBasis_ne_zero hB_herm i₀,
    hB_herm.mulVec_eigenvectorBasis i₀,
    fun b ↦ hB_herm.dotProduct_mulVec_le_of_eigenvalues_le i₀ hmax b, ?_⟩
  rintro ν ⟨a, ha_ne, ha_eig⟩
  have h1 : a ⬝ᵥ B.mulVec a = ν * (a ⬝ᵥ a) := by
    rw [ha_eig, dotProduct_smul, smul_eq_mul]
  have h3 := hB_herm.dotProduct_mulVec_le_of_eigenvalues_le i₀ hmax a
  rw [h1] at h3
  exact le_of_mul_le_mul_right h3 (by simpa using Matrix.dotProduct_star_self_pos_iff.mpr ha_ne)

/-- The identity `(ν • 1 - M).mulVec a = 0 ↔ M.mulVec a = ν • a`. -/
lemma smul_one_sub_mulVec_eq_zero_iff {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (a : Fin d → ℝ) :
    (ν • (1 : Matrix (Fin d) (Fin d) ℝ) - M) *ᵥ a = 0 ↔
      M.mulVec a = ν • a := by
  rw [Matrix.sub_mulVec, sub_eq_zero, eq_comm]
  have h : (ν • (1 : Matrix (Fin d) (Fin d) ℝ)) *ᵥ a = ν • a := by
    ext i
    simp [Matrix.mulVec, dotProduct, smul_eq_mul, Matrix.one_apply]
  rw [h]

/-- `ν ∈ spectrum ℝ M` iff there is a nonzero `a` with `M.mulVec a = ν • a`. -/
lemma mem_spectrum_iff_exists_mulVec_eq_smul {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) :
    ν ∈ spectrum ℝ M ↔ ∃ a : Fin d → ℝ, a ≠ 0 ∧ M.mulVec a = ν • a := by
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one,
      show (¬ IsUnit (ν • (1 : Matrix (Fin d) (Fin d) ℝ) - M) ↔
          ∃ a : Fin d → ℝ, a ≠ 0 ∧ (ν • 1 - M) *ᵥ a = 0) from by
        rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ne_eq, not_not]
        exact Matrix.exists_mulVec_eq_zero_iff.symm]
  exact exists_congr fun a ↦ and_congr_right fun _ ↦ smul_one_sub_mulVec_eq_zero_iff M ν a

/-- Quadratic-form translation: `a ⬝ᵥ A₂.mulVec a` equals the quadratic form of
`L⁻¹ * A₂ * (L⁻¹)ᵀ` at `Lᵀ a`. -/
private lemma quadForm_A2_eq_quadForm_B {d : ℕ}
    (A₂ L : Matrix (Fin d) (Fin d) ℝ) (hLu : IsUnit L.det) (a : Fin d → ℝ) :
    a ⬝ᵥ A₂.mulVec a = (Lᵀ *ᵥ a) ⬝ᵥ (L⁻¹ * A₂ * (L⁻¹)ᵀ) *ᵥ (Lᵀ *ᵥ a) := by
  have key := dotProduct_mulVec_conj_subst A₂ L (Lᵀ *ᵥ a)
  rwa [invTranspose_mulVec_transpose_mulVec L hLu a] at key

/-- `Lᵀ.mulVec ((L⁻¹)ᵀ.mulVec b) = b` when `L` is invertible. -/
private lemma transpose_mulVec_invTranspose_mulVec {d : ℕ} (L : Matrix (Fin d) (Fin d) ℝ)
    (hL : IsUnit L.det) (b : Fin d → ℝ) :
    Lᵀ *ᵥ ((L⁻¹)ᵀ *ᵥ b) = b := by
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hL,
      Matrix.transpose_one, Matrix.one_mulVec]

/-- If `B b₀ = μ • b₀` where
`B = L⁻¹ * A₂ * (L⁻¹)ᵀ`, then with `a₀ := (L⁻¹)ᵀ b₀`,
`A₂.mulVec a₀ = μ • (L * Lᵀ).mulVec a₀`. -/
private lemma eig_B_to_genEig {d : ℕ} (A₂ L : Matrix (Fin d) (Fin d) ℝ) (hLu : IsUnit L.det)
    (μ : ℝ) (b₀ : Fin d → ℝ)
    (hB_eig : (L⁻¹ * A₂ * (L⁻¹)ᵀ) *ᵥ b₀ = μ • b₀) :
    A₂.mulVec ((L⁻¹)ᵀ *ᵥ b₀) = μ • (L * Lᵀ) *ᵥ ((L⁻¹)ᵀ *ᵥ b₀) := by
  have hb : Lᵀ *ᵥ ((L⁻¹)ᵀ *ᵥ b₀) = b₀ := transpose_mulVec_invTranspose_mulVec L hLu b₀
  have h2 : (L * Lᵀ) *ᵥ ((L⁻¹)ᵀ *ᵥ b₀) = L.mulVec b₀ := by
    rw [← Matrix.mulVec_mulVec, hb]
  rw [h2]
  have key : A₂.mulVec ((L⁻¹)ᵀ *ᵥ b₀) = L.mulVec ((L⁻¹ * A₂ * (L⁻¹)ᵀ) *ᵥ b₀) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← mul_assoc, ← mul_assoc,
        Matrix.mul_nonsing_inv _ hLu, Matrix.one_mul]
  rw [key, hB_eig, Matrix.mulVec_smul]

/-- A generalised eigenvector of `(L * Lᵀ, A₂)` gives an eigenvector of
`L⁻¹ * A₂ * (L⁻¹)ᵀ`. -/
private lemma genEig_to_eig_B {d : ℕ} (A₂ L : Matrix (Fin d) (Fin d) ℝ) (hLu : IsUnit L.det)
    (μ : ℝ) (a : Fin d → ℝ)
    (hgen : A₂.mulVec a = μ • (L * Lᵀ) *ᵥ a) :
    (L⁻¹ * A₂ * (L⁻¹)ᵀ) *ᵥ (Lᵀ *ᵥ a) = μ • (Lᵀ *ᵥ a) := by
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      invTranspose_mulVec_transpose_mulVec L hLu a, hgen, Matrix.mulVec_smul]
  congr 1
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hLu, Matrix.one_mul]

/-- `(A₁⁻¹ * A₂).mulVec a = μ • a ↔ A₂.mulVec a = μ • A₁.mulVec a`, for invertible `A₁`. -/
lemma nonsing_inv_mul_mulVec_eq_smul_iff {d : ℕ}
    (A₁ A₂ : Matrix (Fin d) (Fin d) ℝ) (hA₁_inv : IsUnit A₁.det)
    (μ : ℝ) (a : Fin d → ℝ) :
    (A₁⁻¹ * A₂) *ᵥ a = μ • a ↔ A₂.mulVec a = μ • A₁.mulVec a := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h1 : A₁.mulVec ((A₁⁻¹ * A₂) *ᵥ a) = A₁.mulVec (μ • a) := by rw [h]
    rwa [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA₁_inv,
        Matrix.one_mul, Matrix.mulVec_smul] at h1
  · rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul,
        Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA₁_inv, Matrix.one_mulVec]

end Matrix

namespace PrimeGaps

/-- Generalised Rayleigh-quotient maximum equals the largest generalised
eigenvalue of the pair `(A₁, A₂)`. -/
@[pg_tag "bg246" "lem_rayleigh"]
theorem lem_rayleigh {d : ℕ} [NeZero d] (A₁ A₂ : Matrix (Fin d) (Fin d) ℝ)
    (h₁ : A₁.PosDef) (h₂ : A₂.PosDef) :
    ∃ lam : ℝ, (∀ a : Fin d → ℝ, a ≠ 0 →
          a ⬝ᵥ A₂.mulVec a ≤ lam * (a ⬝ᵥ A₁.mulVec a)) ∧ (∃ a₀ : Fin d → ℝ, a₀ ≠ 0 ∧
            a₀ ⬝ᵥ A₂.mulVec a₀ = lam * (a₀ ⬝ᵥ A₁.mulVec a₀)) ∧ lam = sSup {q : ℝ |
            ∃ a : Fin d → ℝ, a ≠ 0 ∧ q = (a ⬝ᵥ A₂.mulVec a) / (a ⬝ᵥ A₁.mulVec a)} ∧
      (∃ a : Fin d → ℝ, a ≠ 0 ∧ A₂.mulVec a = lam • A₁.mulVec a) ∧ (∀ μ : ℝ,
            (∃ a : Fin d → ℝ, a ≠ 0 ∧ A₂.mulVec a = μ • A₁.mulVec a) → μ ≤ lam) ∧
      lam ∈ spectrum ℝ (A₁⁻¹ * A₂) ∧ (∀ μ : ℝ, μ ∈ spectrum ℝ (A₁⁻¹ * A₂) → μ ≤ lam) := by
  obtain ⟨L, hLu, hA₁⟩ := h₁.exists_eq_mul_transpose
  set B : Matrix (Fin d) (Fin d) ℝ := L⁻¹ * A₂ * (L⁻¹)ᵀ
  have hLinv : IsUnit L⁻¹ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_nonsing_inv]
    exact hLu.ringInverse
  have hBPD : B.PosDef := by
    have h := h₂.mul_mul_conjTranspose_same (B := L⁻¹) (Matrix.vecMul_injective_of_isUnit hLinv)
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  obtain ⟨μ, b₀, hb₀_ne, hb₀_eig, h_bound, h_max⟩ := Matrix.posDef_max_eig_quadForm hBPD
  have hA₁_inv : IsUnit A₁.det := by
    rw [hA₁, det_mul, det_transpose]
    exact hLu.mul hLu
  set a₀ : Fin d → ℝ := (L⁻¹)ᵀ *ᵥ b₀
  have ha₀_ne : a₀ ≠ 0 := Matrix.invTranspose_mulVec_ne_zero L hLu b₀ hb₀_ne
  have h_genEig_a₀ : A₂.mulVec a₀ = μ • A₁.mulVec a₀ := by
    rw [hA₁]
    exact Matrix.eig_B_to_genEig A₂ L hLu μ b₀ hb₀_eig
  have h_largest : ∀ ν : ℝ, (∃ a : Fin d → ℝ, a ≠ 0 ∧ A₂.mulVec a = ν • A₁.mulVec a) →
      ν ≤ μ := fun ν ⟨a, ha, hgen⟩ ↦ by
    have hgen' : A₂.mulVec a = ν • (L * Lᵀ) *ᵥ a := hA₁ ▸ hgen
    exact h_max ν ⟨Lᵀ *ᵥ a, Matrix.transpose_mulVec_ne_zero L hLu a ha,
      Matrix.genEig_to_eig_B A₂ L hLu ν a hgen'⟩
  have h_ineq : ∀ a : Fin d → ℝ, a ≠ 0 → a ⬝ᵥ A₂.mulVec a ≤ μ * (a ⬝ᵥ A₁.mulVec a) := fun a _ ↦ by
    rw [Matrix.quadForm_A2_eq_quadForm_B A₂ L hLu a, show a ⬝ᵥ A₁.mulVec a =
      (Lᵀ *ᵥ a) ⬝ᵥ (Lᵀ *ᵥ a) by rw [hA₁, Matrix.dotProduct_mul_transpose_mulVec]]
    exact h_bound (Lᵀ *ᵥ a)
  have h_eq_a₀ : a₀ ⬝ᵥ A₂.mulVec a₀ = μ * (a₀ ⬝ᵥ A₁.mulVec a₀) := by
    have h1 : a₀ ⬝ᵥ A₂.mulVec a₀ = b₀ ⬝ᵥ B.mulVec b₀ := by
      simpa [a₀, B] using Matrix.dotProduct_mulVec_conj_subst A₂ L b₀
    have h2 : b₀ ⬝ᵥ B.mulVec b₀ = μ * (b₀ ⬝ᵥ b₀) := by
      rw [hb₀_eig, dotProduct_smul, smul_eq_mul]
    have h3 : a₀ ⬝ᵥ A₁.mulVec a₀ = b₀ ⬝ᵥ b₀ := by
      rw [hA₁, Matrix.dotProduct_mul_transpose_mulVec,
        Matrix.transpose_mulVec_invTranspose_mulVec L hLu b₀]
    rw [h1, h2, h3]
  refine ⟨μ, h_ineq, ⟨a₀, ha₀_ne, h_eq_a₀⟩, ?_, ⟨a₀, ha₀_ne, h_genEig_a₀⟩, h_largest, ?_, ?_⟩
  · set S : Set ℝ := {q : ℝ | ∃ a : Fin d → ℝ, a ≠ 0 ∧ q = (a ⬝ᵥ A₂.mulVec a) / (a ⬝ᵥ A₁.mulVec a)}
    have h_pos_a₀ : 0 < a₀ ⬝ᵥ A₁.mulVec a₀ := h₁.dotProduct_mulVec_pos ha₀_ne
    have h_mem : μ ∈ S := ⟨a₀, ha₀_ne, by field_simp; linarith [h_eq_a₀]⟩
    have h_ub : ∀ q ∈ S, q ≤ μ := by
      rintro q ⟨a, ha, rfl⟩
      exact (div_le_iff₀ (h₁.dotProduct_mulVec_pos ha)).mpr (h_ineq a ha)
    exact (IsLUB.csSup_eq ⟨h_ub, fun _ hy ↦ hy h_mem⟩ ⟨μ, h_mem⟩).symm
  · rw [Matrix.mem_spectrum_iff_exists_mulVec_eq_smul]
    exact ⟨a₀, ha₀_ne,
      (Matrix.nonsing_inv_mul_mulVec_eq_smul_iff A₁ A₂ hA₁_inv μ a₀).mpr h_genEig_a₀⟩
  · intro ν hν
    rw [Matrix.mem_spectrum_iff_exists_mulVec_eq_smul] at hν
    obtain ⟨a, ha, h_eq⟩ := hν
    exact h_largest ν ⟨a, ha, (Matrix.nonsing_inv_mul_mulVec_eq_smul_iff A₁ A₂ hA₁_inv ν a).mp h_eq⟩

end PrimeGaps
