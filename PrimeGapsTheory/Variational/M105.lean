/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap600.Witness
public import PrimeGapsTheory.Variational.MkVerified
public import PrimeGapsTheory.Variational.PolynomialF
public import PrimeGapsTheory.Variational.QuadForms

import PrimeGapsTheory.Tactic.PaperTag

/-!
# The variational bound `M₁₀₅ > 4`

Evaluates the degree-eleven polynomial certificate and proves that its Rayleigh quotient exceeds
four.

## Main definitions

* `Asum`: The value of the certificate's `A`-quadratic form.
* `Bterm`: The value of the certificate's `B`-quadratic form.
* `f₀`: The certificate polynomial as an element of `L²(𝓡 105)`.

## Main results

* `Jk_sum`: The sum of the 105 marginal integrals equals `105 * Bterm`.
* `four_lt_M_verified`: The variational constant `M 105` is greater than four.
-/

@[expose] public section

open scoped Nat

open MeasureTheory EuclideanSpace
open scoped PrimeGaps RealInnerProductSpace

namespace PrimeGaps

namespace PropM105

/-- The explicit rational certificate of `M₁₀₅ > 4`. -/
noncomputable def cert105 : CertificateExplicit 105 := gap600CertInt.toExplicit

/-- The certificate's coefficients, as reals. -/
noncomputable def aR (i : Fin cert105.N) : ℝ := (cert105.a i : ℝ)

/-- The `I`-form of a rational certificate, cast to `ℝ`, in the shape produced by
`lem_Ik_quadratic_I`. -/
theorem cast_sum_IExplicit (k d : ℕ) (a : Fin d → ℚ) (b c : Fin d → ℕ) :
    ((∑ i, ∑ j, a i * a j * IExplicit k (b i + b j) (c i + c j) : ℚ) : ℝ) =
      ∑ i, ∑ j, (a i : ℝ) * (a j : ℝ) * ((b i + b j)! : ℝ) *
          (maynardG (c i + c j) 2 k : ℝ) /
          ((k + b i + b j + 2 * c i + 2 * c j)! : ℝ) := by
  push_cast [IExplicit]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [show k + (b i + b j) + 2 * (c i + c j) = k + b i + b j + 2 * c i + 2 * c j from by ring]
  ring

/-- The `J`-form of a rational certificate, cast to `ℝ`, in the shape produced by
`lem_quad_forms`. -/
theorem cast_sum_JExplicit (n d : ℕ) (a : Fin d → ℚ) (b c : Fin d → ℕ) :
    ((∑ i, ∑ j, a i * a j * JExplicit (n + 1) (b i) (b j) (c i) (c j) : ℚ) : ℝ) =
      ∑ i, ∑ j, (a i : ℝ) * (a j : ℝ) *
          ∑ c1' ∈ Finset.range (c i + 1), ∑ c2' ∈ Finset.range (c j + 1),
            ((c i).choose c1' : ℝ) * ((c j).choose c2' : ℝ) *
              ((PrimeGaps.gamma (b i) (b j) (c i) (c j) c1' c2' : ℚ) : ℝ) *
              (maynardG (c1' + c2') 2 n : ℝ) /
              ((n + 1 + b i + b j + 2 * c i + 2 * c j + 1)! : ℝ) := by
  push_cast [JExplicit, Nat.add_sub_cancel, Finset.sum_div]
  rfl

/-- The `A`-quadratic form of the certificate at `k = 105`. -/
noncomputable def Asum : ℝ :=
  ((∑ i, ∑ j, cert105.a i * cert105.a j *
    IExplicit 105 (cert105.b i + cert105.b j) (cert105.c i + cert105.c j) : ℚ) : ℝ)

/-- The `B`-quadratic form of the certificate at `k = 105`. -/
noncomputable def Bterm : ℝ :=
  ((∑ i, ∑ j, cert105.a i * cert105.a j *
    JExplicit 105 (cert105.b i) (cert105.b j) (cert105.c i) (cert105.c j) : ℚ) : ℝ)

/-- The certificate values satisfy `4 · Asum < 105 · Bterm`. -/
theorem rayleigh_ineq : 4 * Asum < 105 * Bterm := by
  rw [Asum, Bterm]
  exact_mod_cast cert105.cert

/-- The sum of the 105 marginal integrals of `F_P_quad` equals `105 · Bterm`. -/
theorem Jk_sum : (∑ m : Fin 105, ∫ t in 𝓡 104, (∫ s in Set.Icc (0 : ℝ) (1 - ∑ i, t i),
              F_P_quad cert105.N 105 aR cert105.b cert105.c (insertLp m s t)) ^ 2) =
      105 * Bterm := by
  have hm : ∀ m : Fin 105, (∫ t in 𝓡 104, (∫ s in Set.Icc (0 : ℝ) (1 - ∑ i, t i),
              F_P_quad cert105.N 105 aR cert105.b cert105.c (insertLp m s t)) ^ 2) = Bterm := by
    intro m
    rw [lem_quad_forms cert105.N 104 aR cert105.b cert105.c m, Bterm,
      cast_sum_JExplicit 104 cert105.N cert105.a cert105.b cert105.c]
    simp only [aR]
  rw [Finset.sum_congr rfl fun m _ ↦ hm m, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  norm_num

end PropM105

open PropM105

/-- The certificate polynomial as an element of `L²(𝓡 105)`. -/
noncomputable def f₀ : Lp ℝ 2 (volume.restrict (𝓡 105)) :=
  (polyP_memLp 105 cert105.N aR cert105.b cert105.c).toLp _

/-- The squared norm of `f₀` is `Asum`. -/
theorem I_f₀ : ‖f₀‖ ^ 2 = Asum := by
  rw [f₀, lem_Ik_quadratic_I 105 cert105.N aR cert105.b cert105.c, Asum,
    cast_sum_IExplicit 105 cert105.N cert105.a cert105.b cert105.c]
  simp only [aR]

/-- On the L² simplex `𝓡 104` and admissible slice `Icc 0 (1 - ∑ t)`, the polynomial `polyP univ`
agrees pointwise with its extension-by-zero `F_P_quad cert105.N 105 …`.
-/
theorem polyP_eq_F_P_quad_on_slice (m : Fin 105) (t : EuclideanSpace ℝ (Fin 104))
    (ht : t ∈ 𝓡 104) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) (1 - ∑ i, t i)) :
    polyP Finset.univ aR cert105.b cert105.c (insertLp m s t) =
      F_P_quad cert105.N 105 aR cert105.b cert105.c (insertLp m s t) := by
  have htR : (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ 1 := ht
  obtain ⟨hnn, hsum⟩ := htR
  obtain ⟨hs0, hs1⟩ := hs
  have hmem : insertLp m s t ∈ 𝓡 105 := by
    refine ⟨?_, ?_⟩
    · rw [forall_insertLp_nonneg]; exact ⟨hs0, hnn⟩
    · rw [sum_insertLp]; linarith
  change _ = F_P_idx Finset.univ aR cert105.b cert105.c (insertLp m s t)
  rw [F_P_idx, Set.indicator_of_mem hmem]

/-- `∑ m, J m f₀ = 105 · Bterm`. -/
theorem J_f₀_sum : ∑ m : Fin 105, PrimeGaps.J m f₀ = 105 * Bterm := by
  have hmem : MemLp (polyP (ι := Fin cert105.N) (k := 105) Finset.univ aR cert105.b cert105.c) 2
      (volume.restrict (𝓡 105)) := polyP_memLp 105 cert105.N aR cert105.b cert105.c
  have hf₀_eq : hmem.toLp _ = f₀ := rfl
  have hperm : ∀ m : Fin 105, PrimeGaps.J m f₀ = ∫ t in 𝓡 104,
          (∫ s in Set.Icc (0 : ℝ) (1 - ∑ i, t i),
              F_P_quad cert105.N 105 aR cert105.b cert105.c (insertLp m s t)) ^ 2 := by
    intro m
    have hL2 := J_toLp_eq_iterated 104 m
      (polyP (ι := Fin cert105.N) (k := 105) Finset.univ aR cert105.b cert105.c) hmem
    rw [hf₀_eq] at hL2
    rw [hL2]
    apply MeasureTheory.setIntegral_congr_fun
      isClosed_scaledStdSimplex.measurableSet
    intro x hx
    beta_reduce
    congr 1
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    exact fun s hs ↦ polyP_eq_F_P_quad_on_slice m x hx s hs
  rw [Finset.sum_congr rfl (fun m _ ↦ hperm m), Jk_sum]

/-- The marginal integration operator as a continuous linear map. -/
noncomputable def Vclm (k : ℕ) (m : Fin k) :
    Lp ℝ 2 (volume.restrict (𝓡 k)) →L[ℝ] Lp ℝ 2 (volume (α := EuclideanSpace ℝ (Fin (k - 1)))) :=
  Lp.integralVarCLM m isClosed_scaledStdSimplex.measurableSet
    (.of_isCompact isCompact_scaledStdSimplex)

/-- `J m f = ‖Vclm k m f‖ ^ 2`: the `m`-th marginal functional is the squared norm of `Vclm`. -/
theorem J_eq_normSq (k : ℕ) (m : Fin k) (f : Lp ℝ 2 (volume.restrict (𝓡 k))) :
    PrimeGaps.J m f = ‖Vclm k m f‖ ^ 2 := by
  rw [PrimeGaps.J_apply, PrimeGaps.JBilinCLM, EuclideanSpace.tonelliBilinCLM]
  simp only [ContinuousLinearMap.bilinearComp_apply, coe_innerSL_apply]
  rw [real_inner_self_eq_norm_sq]
  rfl

/-- Each marginal is bounded by the operator norm of `Vclm`. -/
theorem J_le_opNorm (k : ℕ) (m : Fin k) (f : Lp ℝ 2 (volume.restrict (𝓡 k))) :
    PrimeGaps.J m f ≤ ‖Vclm k m‖ ^ 2 * ‖f‖ ^ 2 := by
  rw [J_eq_normSq, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) ((Vclm k m).le_opNorm f) 2

namespace PropM105

/-- The certificate value `Asum` is positive: it is the squared norm of `f₀`, and it cannot vanish,
since `f₀ = 0` would force `105 · Bterm = ∑ m, J m f₀ = 0`, contradicting `4 · Asum < 105 · Bterm`.
-/
theorem Asum_pos : 0 < Asum := by
  have h0 : (0 : ℝ) ≤ Asum := by rw [← I_f₀]; positivity
  rcases h0.lt_or_eq with h | h
  · exact h
  · exfalso
    have hf : f₀ = 0 := by
      have h2 : ‖f₀‖ ^ 2 = 0 := by rw [I_f₀, ← h]
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp h2)
    have hJ : ∑ m : Fin 105, PrimeGaps.J m f₀ = 0 := by
      refine Finset.sum_eq_zero fun m _ ↦ ?_
      rw [hf, J_eq_normSq]
      simp
    rw [J_f₀_sum] at hJ
    linarith [rayleigh_ineq]

end PropM105

/-- The variational constant `M 105` is greater than four. -/
@[pg_tag "bg246" "prop_M105"]
theorem four_lt_M_verified : (4 : ℝ) < PrimeGaps.M 105 := by
  have hle : (∑ m, PrimeGaps.J m f₀) / ‖f₀‖ ^ 2 ≤ PrimeGaps.M 105 := PrimeGaps.M_ge
  rw [I_f₀, J_f₀_sum] at hle
  have h4 : (4 : ℝ) < 105 * Bterm / Asum := by
    rw [lt_div_iff₀ Asum_pos]; linarith [rayleigh_ineq]
  linarith

end PrimeGaps
