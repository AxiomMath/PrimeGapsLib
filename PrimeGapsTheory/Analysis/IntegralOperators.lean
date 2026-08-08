/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import PrimeGapsTheory.Analysis.Simplex
public import PrimeGapsTheory.Analysis.Tonelli.LpEuclidean

import PrimeGapsTheory.Tactic.PaperTag

/-!
# The variational constants `M_k` and `M_{k, ε}`

This file builds the continuous bilinear and quadratic forms obtained by integrating an `L²`
function on a simplex along one coordinate and pairing the resulting marginals, and defines the
variational constants `M_k` and `M_{k, ε}` as suprema of their normalized sums.

## Main definitions

* `EuclideanSpace.tonelliBilinCLM`: the bilinear form `(f, g) ↦ ⟪∫ f dxₘ, ∫ g dxₘ⟫` on `L²(S)`.
* `PrimeGaps.J` and `PrimeGaps.JEps`: the quadratic marginals on the standard simplex `𝓡 k` and
  on the enlarged simplex `𝓡(k, 1 + ε)`.
* `PrimeGaps.M` and `PrimeGaps.MEps`: the associated variational constants.
* `PrimeGaps.r`: the lower bound `r_k = ⌈θ * M_k / 2⌉` on the number of primes targeted.

## Implementation notes

`def_M_k` takes its supremum over `L²(𝓡 k)` directly; `PrimeGaps.M` below realizes it.
-/

@[expose] public section

add_to_pg "maynard" "lem_Ik_L2_continuous" continuous_norm

open ENNReal MeasureTheory Measure EuclideanSpace Finset

local notation "ES(" 𝕜:65 ", " k:65 ")" => EuclideanSpace 𝕜 (Fin k)

-- belongs to mathlib
theorem MeasureTheory.norm_LpToLpRestrictCLM_le
    {X F : Type*} [MeasurableSpace X] {𝕜 : Type} [NormedRing 𝕜] [NormedAddCommGroup F] [Module 𝕜 F]
    [IsBoundedSMul 𝕜 F] {μ : Measure X} {p : ℝ≥0∞} [Fact (1 ≤ p)] {s : Set X} {f : Lp F p μ} :
    ‖LpToLpRestrictCLM X F 𝕜 μ p s f‖ ≤ ‖f‖ := norm_Lp_toLp_restrict_le _ _

/-- The continuous bilinear form `(f, g) ↦ ⟪∫ f dxₘ, ∫ g dxₘ⟫` on `L²(S)`, obtained by
integrating along variable `m` and pairing via the inner product. -/
noncomputable def EuclideanSpace.tonelliBilinCLM {k : ℕ} (m : Fin k) {S : Set ES(ℝ, k)}
    (hMS : MeasurableSet S) (hS : EssFiniteSnd (finIsolateEquivProd ℝ m '' S) volume volume) :
    Lp ℝ 2 (volume.restrict S) →L[ℝ] Lp ℝ 2 (volume.restrict S) →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (Lp.integralVarCLM m hMS hS) (Lp.integralVarCLM m hMS hS)

namespace PrimeGaps

open scoped Pointwise

/-- The continuous bilinear form obtained by pairing the `m`-coordinate marginals on
`𝓡(k - 1, 1 - ε)` of two functions on `𝓡(k, 1 + ε)`. -/
@[pg_tag "bg246" "def_j_eps"]
noncomputable def JEpsBilinCLM {k : ℕ} (ε : ℝ) (m : Fin k) :
    Lp ℝ 2 (volume.restrict (𝓡(k, 1 + ε))) →L[ℝ] Lp ℝ 2 (volume.restrict (𝓡(k, 1 + ε))) →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp
    ((LpToLpRestrictCLM _ _ _ _ _ 𝓡(k - 1, 1 - ε)).comp (Lp.integralVarCLM m
      isClosed_scaledStdSimplex.measurableSet (.of_isCompact isCompact_scaledStdSimplex)))
    ((LpToLpRestrictCLM _ _ _ _ _ 𝓡(k - 1, 1 - ε)).comp (Lp.integralVarCLM m
      isClosed_scaledStdSimplex.measurableSet (.of_isCompact isCompact_scaledStdSimplex)))

/-- The quadratic form associated to `JEpsBilinCLM ε m`. -/
@[pg_tag "bg246" "def_j_eps"]
noncomputable def JEps {k : ℕ} (ε : ℝ) (m : Fin k) :
    QuadraticForm ℝ (Lp ℝ 2 (volume.restrict (𝓡(k, 1 + ε)))) :=
  (JEpsBilinCLM ε m).toBilinForm.toQuadraticMap

theorem JEps_coe {k : ℕ} {ε : ℝ} (m : Fin k) : ⇑(JEps ε m) = (fun f ↦ JEpsBilinCLM ε m f f) := rfl

theorem JEps_apply {k : ℕ} {ε : ℝ} (m : Fin k) (f : Lp ℝ 2 (volume.restrict (𝓡(k, 1 + ε)))) :
    JEps ε m f = JEpsBilinCLM ε m f f := rfl

@[pg_tag "bg246" "lem_Jk_m_L2_continuous", fun_prop]
theorem continuous_JEps {k : ℕ} {ε : ℝ} (m : Fin k) : Continuous (JEps ε m) := by
  rw [JEps_coe]
  fun_prop

/-- The continuous bilinear form obtained by pairing the `m`-coordinate marginals of two
functions on the standard simplex. -/
@[pg_tag "bg246" "def_J_k"]
noncomputable def JBilinCLM {k : ℕ} (m : Fin k) :
    Lp ℝ 2 (volume.restrict (𝓡 k)) →L[ℝ] Lp ℝ 2 (volume.restrict (𝓡 k)) →L[ℝ] ℝ :=
  tonelliBilinCLM m isClosed_scaledStdSimplex.measurableSet <|
    .of_isCompact isCompact_scaledStdSimplex

/-- The quadratic form associated to `JBilinCLM m`. -/
@[pg_tag "bg246" "def_J_k"]
noncomputable def J {k : ℕ} (m : Fin k) : QuadraticForm ℝ (Lp ℝ 2 (volume.restrict (𝓡 k))) :=
  (JBilinCLM m).toBilinForm.toQuadraticMap

theorem J_coe {k : ℕ} (m : Fin k) : ⇑(J m) = (fun f ↦ JBilinCLM m f f) := rfl

theorem J_apply {k : ℕ} (m : Fin k) (f : Lp ℝ 2 (volume.restrict (𝓡 k))) :
    J m f = JBilinCLM m f f := rfl

@[pg_tag "bg246" "lem_Jk_m_L2_continuous", fun_prop]
theorem continuous_J {k : ℕ} (m : Fin k) : Continuous (J m) := by
  rw [J_coe]
  fun_prop

/-- The supremum of the sum of the quadratic marginals `J m f`, normalized by `‖f‖ ^ 2`. -/
@[pg_tag "bg246" "def_M_k"]
noncomputable def M (k : ℕ) : ℝ := ⨆ f, (∑ m : Fin k, J m f) / ‖f‖ ^ 2

/-- The enlarged-simplex variational constant `M_{k,ε}`: the supremum of the sum of the
quadratic marginals restricted to `𝓡(k - 1, 1 - ε)`, divided by the squared `L²` norm on
the enlarged simplex `𝓡(k, 1 + ε)`. -/
noncomputable def MEps (k : ℕ) (ε : ℝ) : ℝ := ⨆ f, (∑ m : Fin k, JEps ε m f) / ‖f‖ ^ 2

/-- The lower bound `r_k := ⌈θ M_k / 2⌉`: the number of primes targeted among `n + h_i`,
given a level of distribution `θ` and the functional `M_k` of `Definition def_M_k`. -/
@[pg_tag "bg246" "def_r_k"]
noncomputable def r (θ : ℝ) (k : ℕ) : ℕ := ⌈θ * M k / 2⌉₊

theorem JEps_nonneg {k : ℕ} {ε : ℝ} {m : Fin k} {f : Lp ℝ 2 (volume.restrict (𝓡(k, 1 + ε)))} :
    0 ≤ JEps ε m f := by simp [JEps_apply, JEpsBilinCLM]

theorem JEps_le {k : ℕ} {ε : ℝ} {m : Fin k} {f : Lp ℝ 2 (volume.restrict (𝓡(k, 1 + ε)))} :
    JEps ε m f ≤ 2 * max 0 (1 + ε) * ‖f‖ ^ 2 := by
  simp only [JEps_apply, JEpsBilinCLM, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.comp_apply, coe_innerSL_apply, inner_self_eq_norm_sq_to_K,
    RCLike.ofReal_real_eq_id, id_eq]
  grw [norm_LpToLpRestrictCLM_le, Lp.norm_integralVarCLM_le 2, ← ENNReal.toReal_rpow,
    essSupSnd_le_of_subset_closedBall scaledStdSimplex_subset_closedBall]
  · rw [mul_pow]
    simp [← Real.rpow_mul_natCast, toReal_ofReal', max_comm]
  · exact (mul_lt_top ofNat_lt_top ofReal_lt_top).ne

theorem J_nonneg {k : ℕ} {m : Fin k} {f : Lp ℝ 2 (volume.restrict (𝓡 k))} :
    0 ≤ J m f := by simp [J_apply, JBilinCLM, tonelliBilinCLM]

theorem J_le {k : ℕ} {m : Fin k} {f : Lp ℝ 2 (volume.restrict (𝓡 k))} : J m f ≤ 2 * ‖f‖ ^ 2 := by
  simp only [J_apply, JBilinCLM, tonelliBilinCLM, ContinuousLinearMap.bilinearComp_apply,
    coe_innerSL_apply, inner_self_eq_norm_sq_to_K, RCLike.ofReal_real_eq_id, id_eq]
  grw [Lp.norm_integralVarCLM_le 2,
    essSupSnd_le_of_subset_closedBall scaledStdSimplex_subset_closedBall]
  · rw [mul_pow, ← toReal_rpow, ← Real.rpow_mul_natCast (by positivity)]
    simp
  · simp

theorem M_bounded_two_mul {k : ℕ} {f : Lp ℝ 2 (volume.restrict (𝓡 k))} :
    (∑ m : Fin k, J m f) / ‖f‖ ^ 2 ≤ 2 * k := by
  grw [J_le]
  by_cases! hf : ‖f‖ = 0
  · simp [hf]
  simp [← mul_assoc, hf, mul_comm]

theorem M_bounded {k : ℕ} : BddAbove (Set.range fun f ↦ (∑ m : Fin k, J m f) / ‖f‖ ^ 2) :=
  ⟨2 * k, Set.forall_mem_range.2 fun _ ↦ M_bounded_two_mul⟩

theorem M_ge {k : ℕ} {f : Lp ℝ 2 (volume.restrict (𝓡 k))} : (∑ m, J m f) / ‖f‖ ^ 2 ≤ M k :=
  le_ciSup M_bounded f

theorem M_nonneg {k : ℕ} : 0 ≤ M k := by simpa using M_ge (f := 0)

/-- The real asymptotic is `M k = log k + O(1)` as `k → ∞`. -/
theorem M_le_two_mul {k : ℕ} : M k ≤ 2 * k := ciSup_le fun _ ↦ M_bounded_two_mul

theorem MEps_bounded_explicit {k : ℕ} {ε : ℝ} {f : Lp ℝ 2 (volume.restrict (𝓡(k, 1 + ε)))} :
    (∑ m : Fin k, JEps ε m f) / ‖f‖ ^ 2 ≤ 2 * max 0 (1 + ε) * k := by
  grw [JEps_le]
  by_cases! hf : ‖f‖ = 0
  · simpa [hf] using by positivity
  simp [← mul_assoc, hf, mul_comm]

theorem MEps_bounded {k : ℕ} {ε : ℝ} :
    BddAbove (Set.range fun f ↦ (∑ m : Fin k, JEps ε m f) / ‖f‖ ^ 2) :=
  ⟨2 * max 0 (1 + ε) * k, Set.forall_mem_range.2 fun _ ↦ MEps_bounded_explicit⟩

theorem MEps_ge {k : ℕ} {ε : ℝ} {f : Lp ℝ 2 (volume.restrict (𝓡(k, 1 + ε)))} :
    (∑ m : Fin k, JEps ε m f) / ‖f‖ ^ 2 ≤ MEps k ε :=
  le_ciSup MEps_bounded f

theorem MEps_nonneg {k : ℕ} {ε : ℝ} : 0 ≤ MEps k ε := by simpa using MEps_ge (f := 0)

theorem MEps_le {k : ℕ} {ε : ℝ} : MEps k ε ≤ 2 * max 0 (1 + ε) * k :=
  ciSup_le fun _ ↦ MEps_bounded_explicit

end PrimeGaps
