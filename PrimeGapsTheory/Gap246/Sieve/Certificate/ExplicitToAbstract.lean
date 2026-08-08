/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Gap246.Sieve.Certificate.Abstract
public import PrimeGapsTheory.Gap246.Sieve.Certificate.Explicit
public import PrimeGapsTheory.Gap246.Variational.Marginal

/-! # From explicit to abstract epsilon-enlarged certificates

This file realizes an explicit rational certificate by its monomial-symmetric polynomial on the
enlarged simplex and evaluates the resulting analytic quadratic forms.
-/

@[expose] public section

open scoped Nat

open Finset MeasureTheory EuclideanSpace
open scoped PrimeGaps BigOperators

namespace PrimeGaps

/-- The monomial belonging to an exponent vector. -/
noncomputable def exponentMonomial {k : ℕ} (A : Fin k → ℕ) (x : EuclideanSpace ℝ (Fin k)) : ℝ :=
  ∏ i, x i ^ A i

/-- The monomial-symmetric polynomial with exponent signature `α`. -/
noncomputable def monomialSymmetric (k : ℕ) (α : Multiset ℕ) (x : EuclideanSpace ℝ (Fin k)) : ℝ :=
  ∑ A ∈ α.embeddings k, exponentMonomial A x

/-- The polynomial basis element represented by `(a, α)` in an explicit certificate. -/
noncomputable def epsBasis (k : ℕ) (ε : ℝ) (a : ℕ) (α : Multiset ℕ)
    (x : EuclideanSpace ℝ (Fin k)) : ℝ :=
  (1 + ε - ∑ i, x i) ^ a * monomialSymmetric k α x

/-- The polynomial represented by an explicit certificate. -/
noncomputable def EpsCertificateExplicit.polynomial {k : ℕ} {ε : ℚ}
    (ct : EpsCertificateExplicit k ε) (x : EuclideanSpace ℝ (Fin k)) : ℝ :=
  ∑ i, (ct.coeff i : ℝ) * epsBasis k (ε : ℝ) (ct.a i) (ct.α i) x

theorem sum_eq_of_mem_embeddings {k : ℕ} {α : Multiset ℕ} {A : Fin k → ℕ}
    (hA : A ∈ α.embeddings k) : ∑ i, A i = α.sum := by
  rw [Multiset.mem_embeddings_iff] at hA
  have hsum := congrArg Multiset.sum hA
  have sum_filter_ne_zero (m : Multiset ℕ) : (m.filter (· ≠ 0)).sum = m.sum := by
    induction m using Multiset.induction_on with
    | empty => simp
    | @cons a m ih => by_cases ha : a = 0 <;> simp [ha, ih]
  rw [sum_filter_ne_zero, sum_filter_ne_zero] at hsum
  simpa [List.sum_ofFn] using hsum

theorem continuous_exponentMonomial {k : ℕ} (A : Fin k → ℕ) : Continuous (exponentMonomial A) := by
  unfold exponentMonomial
  fun_prop

theorem continuous_monomialSymmetric (k : ℕ) (α : Multiset ℕ) :
    Continuous (monomialSymmetric k α) := by
  unfold monomialSymmetric
  exact continuous_finsetSum _ fun A _ ↦ continuous_exponentMonomial A

theorem continuous_epsBasis (k : ℕ) (ε : ℝ) (a : ℕ) (α : Multiset ℕ) :
    Continuous (epsBasis k ε a α) := by
  unfold epsBasis
  exact (show Continuous (fun x : EuclideanSpace ℝ (Fin k) ↦
    (1 + ε - ∑ i, x i) ^ a) by fun_prop).mul (continuous_monomialSymmetric k α)

theorem EpsCertificateExplicit.continuous_polynomial {k : ℕ} {ε : ℚ}
    (ct : EpsCertificateExplicit k ε) : Continuous ct.polynomial := by
  unfold polynomial
  exact continuous_finsetSum _ fun i _ ↦
    continuous_const.mul (continuous_epsBasis k (ε : ℝ) (ct.a i) (ct.α i))

/-- The polynomial represented by an explicit certificate belongs to the required `L²` space. -/
theorem EpsCertificateExplicit.polynomial_memLp {k : ℕ} {ε : ℚ} (ct : EpsCertificateExplicit k ε) :
    MemLp ct.polynomial 2 (volume.restrict 𝓡(k, 1 + (ε : ℝ))) := by
  haveI : IsFiniteMeasure (volume.restrict 𝓡(k, 1 + (ε : ℝ))) :=
    ⟨by rw [Measure.restrict_apply_univ]
        exact (isCompact_scaledStdSimplex (k := k) (s := 1 + (ε : ℝ))).measure_lt_top⟩
  obtain ⟨C, hC⟩ :=
    (isCompact_scaledStdSimplex (k := k) (s := 1 + (ε : ℝ))).exists_bound_of_continuousOn
      ct.continuous_polynomial.continuousOn
  refine MemLp.of_bound ct.continuous_polynomial.aestronglyMeasurable C ?_
  rw [ae_restrict_iff' (isClosed_scaledStdSimplex (k := k) (s := 1 + (ε : ℝ))).measurableSet]
  exact Filter.Eventually.of_forall hC

theorem epsBasis_pair_integral {k : ℕ} {ε : ℚ} (hε : 0 ≤ 1 + ε)
    (a₁ : ℕ) (α₁ : Multiset ℕ) (a₂ : ℕ) (α₂ : Multiset ℕ) :
    (∫ x in 𝓡(k, 1 + (ε : ℝ)), epsBasis k (ε : ℝ) a₁ α₁ x * epsBasis k (ε : ℝ) a₂ α₂ x) =
      (IEpsExplicit k ε a₁ α₁ a₂ α₂ : ℚ) := by
  classical
  unfold epsBasis monomialSymmetric exponentMonomial IEpsExplicit facMoment
  push_cast
  rw [show (fun x : EuclideanSpace ℝ (Fin k) ↦
      ((1 + (ε : ℝ) - ∑ i, x i) ^ a₁ * ∑ A ∈ α₁.embeddings k, ∏ i, x i ^ A i) *
        ((1 + (ε : ℝ) - ∑ i, x i) ^ a₂ * ∑ B ∈ α₂.embeddings k, ∏ i, x i ^ B i)) =
      fun x ↦ ∑ A ∈ α₁.embeddings k, ∑ B ∈ α₂.embeddings k,
        ((1 + (ε : ℝ) - ∑ i, x i) ^ a₁ * ∏ i, x i ^ A i) *
          ((1 + (ε : ℝ) - ∑ i, x i) ^ a₂ * ∏ i, x i ^ B i) by
    funext x
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]]
  rw [integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A hA
    rw [integral_finsetSum]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B hB
      rw [show (fun x : EuclideanSpace ℝ (Fin k) ↦
          ((1 + (ε : ℝ) - ∑ i, x i) ^ a₁ * ∏ i, x i ^ A i) *
            ((1 + (ε : ℝ) - ∑ i, x i) ^ a₂ * ∏ i, x i ^ B i)) =
          fun x ↦ (1 + (ε : ℝ) - ∑ i, x i) ^ (a₁ + a₂) *
            ∏ i, x i ^ (A i + B i) by
        funext x
        simp_rw [pow_add, Finset.prod_mul_distrib]
        ring]
      change (∫ x in 𝓡(k, 1 + (ε : ℝ)),
        (1 + (ε : ℝ) - ∑ i, x i) ^ (a₁ + a₂) * ∏ i, x i ^ (A i + B i)) = _
      rw [dirichlet_scaled k (a₁ + a₂) (fun i ↦ A i + B i) (1 + (ε : ℝ))]
      · rw [sum_add_distrib, sum_eq_of_mem_embeddings hA, sum_eq_of_mem_embeddings hB]
        push_cast
        ring
      · exact_mod_cast hε
    · intro B hB
      exact (by fun_prop : Continuous (fun x : EuclideanSpace ℝ (Fin k) ↦
        ((1 + (ε : ℝ) - ∑ i, x i) ^ a₁ * ∏ i, x i ^ A i) * ((1 + (ε : ℝ) - ∑ i, x i) ^ a₂ *
            ∏ i, x i ^ B i))).continuousOn.integrableOn_compact
            (isCompact_scaledStdSimplex (k := k) (s := 1 + (ε : ℝ)))
  · intro A hA
    apply integrable_finsetSum
    intro B hB
    exact (by fun_prop : Continuous (fun x : EuclideanSpace ℝ (Fin k) ↦
      ((1 + (ε : ℝ) - ∑ i, x i) ^ a₁ * ∏ i, x i ^ A i) * ((1 + (ε : ℝ) - ∑ i, x i) ^ a₂ *
          ∏ i, x i ^ B i))).continuousOn.integrableOn_compact
            (isCompact_scaledStdSimplex (k := k) (s := 1 + (ε : ℝ)))

/-- The analytic witness represented by an explicit certificate. -/
noncomputable def EpsCertificateExplicit.toLp {k : ℕ} {ε : ℚ} (ct : EpsCertificateExplicit k ε) :
    Lp ℝ 2 (volume.restrict 𝓡(k, 1 + (ε : ℝ))) :=
  ct.polynomial_memLp.toLp ct.polynomial

theorem EpsCertificateExplicit.norm_sq_toLp {k : ℕ} {ε : ℚ} (ct : EpsCertificateExplicit k ε) :
    ‖ct.toLp‖ ^ 2 = ∫ x in 𝓡(k, 1 + (ε : ℝ)), ct.polynomial x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ct.polynomial_memLp.coeFn_toLp] with x hx
  rw [show (ct.toLp : EuclideanSpace ℝ (Fin k) → ℝ) x = ct.polynomial x from hx]
  simp [sq]

/-- Evaluation of the denominator of the analytic witness by the explicit rational Gram form. -/
theorem EpsCertificateExplicit.norm_sq_eq_explicit {k : ℕ} {ε : ℚ}
    (ct : EpsCertificateExplicit k ε) (hε : 0 ≤ 1 + ε) :
    ‖ct.toLp‖ ^ 2 = ((∑ i, ∑ j, ct.coeff i * ct.coeff j *
      IEpsExplicit k ε (ct.a i) (ct.α i) (ct.a j) (ct.α j) : ℚ) : ℝ) := by
  classical
  rw [ct.norm_sq_toLp]
  unfold polynomial
  rw [PrimeGaps.setIntegral_sq_sum (isCompact_scaledStdSimplex (k := k) (s := 1 + (ε : ℝ)))
    (fun i ↦ (ct.coeff i : ℝ)) (fun i ↦ epsBasis k (ε : ℝ) (ct.a i) (ct.α i))
    (fun i ↦ continuous_epsBasis k (ε : ℝ) (ct.a i) (ct.α i))]
  push_cast
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [epsBasis_pair_integral hε (ct.a i) (ct.α i) (ct.a j) (ct.α j)]

/-- Evaluation of a shifted monomial on the shrunken simplex. -/
theorem shiftedMonomial_integral (K e : ℕ) (ε : ℚ) (hε1 : ε ≤ 1) (C : Fin K → ℕ) :
    (∫ x in 𝓡(K, 1 - (ε : ℝ)), (1 + (ε : ℝ) - ∑ i, x i) ^ e * ∏ i, x i ^ C i) =
      (radialExplicit (K + ∑ i, C i) ε e : ℚ) * ∏ i, (C i)! := by
  classical
  unfold radialExplicit
  push_cast
  rw [show (fun x : EuclideanSpace ℝ (Fin K) ↦ (1 + (ε : ℝ) - ∑ i, x i) ^ e * ∏ i, x i ^ C i) =
      fun x ↦ ∑ m ∈ Finset.range (e + 1), ((e.choose m : ℝ) * (2 * (ε : ℝ)) ^ (e - m)) *
          (((1 - (ε : ℝ)) - ∑ i, x i) ^ m * ∏ i, x i ^ C i) by
    funext x
    rw [show 1 + (ε : ℝ) - ∑ i, x i =
      ((1 - (ε : ℝ)) - ∑ i, x i) + 2 * (ε : ℝ) by ring, add_pow]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    ring]
  rw [integral_finsetSum]
  · rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    rw [integral_const_mul]
    change _ * (∫ x in 𝓡(K, 1 - (ε : ℝ)),
      ((1 - (ε : ℝ)) - ∑ i, x i) ^ m * ∏ i, x i ^ C i) = _
    rw [dirichlet_scaled K m C (1 - (ε : ℝ))]
    · push_cast
      ring_nf
    · exact_mod_cast sub_nonneg.mpr hε1
  · intro m _
    exact (continuous_const.mul (by fun_prop : Continuous (fun x : EuclideanSpace ℝ (Fin K) ↦
        ((1 - (ε : ℝ)) - ∑ i, x i) ^ m * ∏ i, x i ^ C i))).continuousOn.integrableOn_compact
          (isCompact_scaledStdSimplex (k := K) (s := 1 - (ε : ℝ)))

/-- The certificate polynomial, extended by zero away from its enlarged simplex. -/
noncomputable def EpsCertificateExplicit.supportedPolynomial {k : ℕ} {ε : ℚ}
    (ct : EpsCertificateExplicit k ε) : EuclideanSpace ℝ (Fin k) → ℝ :=
  𝓡(k, 1 + (ε : ℝ)).indicator ct.polynomial

theorem EpsCertificateExplicit.supportedPolynomial_memLp {k : ℕ} {ε : ℚ}
    (ct : EpsCertificateExplicit k ε) :
    MemLp ct.supportedPolynomial 2 (volume.restrict 𝓡(k, 1 + (ε : ℝ))) :=
  ct.polynomial_memLp.indicator
    (isClosed_scaledStdSimplex (k := k) (s := 1 + (ε : ℝ))).measurableSet

theorem EpsCertificateExplicit.supported_toLp_eq {k : ℕ} {ε : ℚ} (ct : EpsCertificateExplicit k ε) :
    ct.supportedPolynomial_memLp.toLp ct.supportedPolynomial = ct.toLp := by
  apply MemLp.toLp_congr
  filter_upwards [ae_restrict_mem
    (isClosed_scaledStdSimplex (k := k) (s := 1 + (ε : ℝ))).measurableSet] with x hx
  exact Set.indicator_of_mem hx ct.polynomial

/-- The available length in the isolated coordinate above an outer point. -/
noncomputable def epsOuterFace {n : ℕ} (ε : ℝ) (t : EuclideanSpace ℝ (Fin n)) : ℝ :=
  1 + ε - ∑ i, t i

/-- The monomial in the coordinates remaining after coordinate `m` is isolated. -/
noncomputable def residualMonomial {n : ℕ} (m : Fin (n + 1)) (A : Fin (n + 1) → ℕ)
    (t : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∏ i, t i ^ A (m.succAbove i)

@[fun_prop]
theorem continuous_epsOuterFace {n : ℕ} (ε : ℝ) : Continuous (epsOuterFace (n := n) ε) := by
  unfold epsOuterFace
  fun_prop

@[fun_prop]
theorem continuous_residualMonomial {n : ℕ} (m : Fin (n + 1)) (A : Fin (n + 1) → ℕ) :
    Continuous (residualMonomial m A) := by
  unfold residualMonomial
  fun_prop

theorem sum_sliceInsert {n : ℕ} (m : Fin (n + 1)) (s : ℝ) (t : EuclideanSpace ℝ (Fin n)) :
    ∑ i, (WithLp.toLp 2 (Gaps246.sliceInsert (n + 1) m s t) :
      EuclideanSpace ℝ (Fin (n + 1))) i = s + ∑ i, t i := by
  rw [show Gaps246.sliceInsert (n + 1) m s t.ofLp =
    m.insertNth s (fun i ↦ t i) from Gaps246.sliceInsert_eq_insertNth m s t]
  exact Fin.sum_insertNth m s (fun i ↦ t i)

theorem exponentMonomial_sliceInsert {n : ℕ} (m : Fin (n + 1)) (A : Fin (n + 1) → ℕ)
    (s : ℝ) (t : EuclideanSpace ℝ (Fin n)) :
    exponentMonomial A (WithLp.toLp 2 (Gaps246.sliceInsert (n + 1) m s t)) =
      s ^ A m * residualMonomial m A t := by
  unfold exponentMonomial residualMonomial
  rw [show Gaps246.sliceInsert (n + 1) m s t.ofLp =
    m.insertNth s (fun i ↦ t i) from Gaps246.sliceInsert_eq_insertNth m s t]
  rw [Fin.prod_univ_succAbove _ m]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

theorem epsOuterFace_nonneg {n : ℕ} {ε : ℚ} (hε : 0 ≤ ε)
    {t : EuclideanSpace ℝ (Fin n)} (ht : t ∈ 𝓡(n, 1 - (ε : ℝ))) :
    0 ≤ epsOuterFace (ε : ℝ) t := by
  unfold epsOuterFace
  have hεR : (0 : ℝ) ≤ (ε : ℝ) := by exact_mod_cast hε
  calc 0
      ≤ 2 * (ε : ℝ) := mul_nonneg (by norm_num) hεR
    _ = (1 + (ε : ℝ)) - (1 - (ε : ℝ)) := by ring
    _ ≤ (1 + (ε : ℝ)) - ∑ i, t i := sub_le_sub_left ht.2 _

theorem sliceInsert_mem_scaledStdSimplex {n : ℕ} {ε : ℚ}
    (m : Fin (n + 1)) {s : ℝ} {t : EuclideanSpace ℝ (Fin n)}
    (ht : t ∈ 𝓡(n, 1 - (ε : ℝ))) (hs0 : 0 ≤ s)
    (hs : s ≤ epsOuterFace (ε : ℝ) t) :
    (WithLp.toLp 2 (Gaps246.sliceInsert (n + 1) m s t) :
      EuclideanSpace ℝ (Fin (n + 1))) ∈ 𝓡(n + 1, 1 + (ε : ℝ)) := by
  rw [mem_scaledStdSimplex_iff]
  constructor
  · intro i
    rw [show Gaps246.sliceInsert (n + 1) m s t.ofLp =
      m.insertNth s (fun i ↦ t i) from Gaps246.sliceInsert_eq_insertNth m s t]
    refine Fin.succAboveCases m ?_ (fun j ↦ ?_) i
    · simpa using hs0
    · simp [ht.1 j]
  · rw [sum_sliceInsert m]
    unfold epsOuterFace at hs
    exact (le_sub_iff_add_le).mp hs

theorem sliceInsert_notMem_scaledStdSimplex {n : ℕ} {ε : ℚ}
    (m : Fin (n + 1)) {s : ℝ} {t : EuclideanSpace ℝ (Fin n)}
    (hs : epsOuterFace (ε : ℝ) t < s) :
    (WithLp.toLp 2 (Gaps246.sliceInsert (n + 1) m s t) :
      EuclideanSpace ℝ (Fin (n + 1))) ∉ 𝓡(n + 1, 1 + (ε : ℝ)) := by
  intro hmem
  have hsum := hmem.2
  rw [sum_sliceInsert m] at hsum
  unfold epsOuterFace at hs
  exact (not_lt_of_ge hsum) ((sub_lt_iff_lt_add).mp hs)

/-- The coordinate marginal of one monomial-symmetric basis polynomial. -/
noncomputable def epsBasisMarginal {n : ℕ} (m : Fin (n + 1)) (ε : ℝ)
    (a : ℕ) (α : Multiset ℕ) (t : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ A ∈ α.embeddings (n + 1), ((a ! * (A m)! : ℝ) / (a + A m + 1)!) *
      epsOuterFace ε t ^ (a + A m + 1) * residualMonomial m A t

@[fun_prop]
theorem continuous_epsBasisMarginal {n : ℕ} (m : Fin (n + 1)) (ε : ℝ)
    (a : ℕ) (α : Multiset ℕ) : Continuous (epsBasisMarginal m ε a α) := by
  unfold epsBasisMarginal
  exact continuous_finsetSum _ fun A _ ↦ by fun_prop

theorem epsBasis_sliceInsert {n : ℕ} (m : Fin (n + 1)) (ε : ℝ)
    (a : ℕ) (α : Multiset ℕ) (s : ℝ) (t : EuclideanSpace ℝ (Fin n)) :
    epsBasis (n + 1) ε a α (WithLp.toLp 2 (Gaps246.sliceInsert (n + 1) m s t)) =
      ∑ A ∈ α.embeddings (n + 1), (epsOuterFace ε t - s) ^ a *
          (s ^ A m * residualMonomial m A t) := by
  classical
  unfold epsBasis monomialSymmetric
  rw [sum_sliceInsert m, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  rw [exponentMonomial_sliceInsert]
  unfold epsOuterFace
  ring_nf

theorem epsBasis_intervalMarginal {n : ℕ} (m : Fin (n + 1)) (ε : ℝ)
    (a : ℕ) (α : Multiset ℕ) (t : EuclideanSpace ℝ (Fin n)) :
    (∫ s in (0 : ℝ)..epsOuterFace ε t, epsBasis (n + 1) ε a α
        (WithLp.toLp 2 (Gaps246.sliceInsert (n + 1) m s t))) =
      epsBasisMarginal m ε a α t := by
  classical
  rw [intervalIntegral.integral_congr fun s _ ↦ epsBasis_sliceInsert m ε a α s t]
  rw [intervalIntegral.integral_finsetSum]
  · unfold epsBasisMarginal
    apply Finset.sum_congr rfl
    intro A _
    rw [show (fun s : ℝ ↦ (epsOuterFace ε t - s) ^ a * (s ^ A m * residualMonomial m A t)) =
        fun s ↦ residualMonomial m A t *
          ((epsOuterFace ε t - s) ^ a * s ^ A m) by
      funext s
      ring]
    rw [intervalIntegral.integral_const_mul, PrimeGaps.integral_complement_pow_mul_pow_all]
    ring
  · intro A _
    exact (by fun_prop : Continuous (fun s : ℝ ↦ (epsOuterFace ε t - s) ^ a *
        (s ^ A m * residualMonomial m A t))).intervalIntegrable _ _

theorem epsBasis_supportedMarginal {n : ℕ} {ε : ℚ} (hε : 0 ≤ ε)
    (m : Fin (n + 1)) (a : ℕ) (α : Multiset ℕ)
    {t : EuclideanSpace ℝ (Fin n)} (ht : t ∈ 𝓡(n, 1 - (ε : ℝ))) :
    (∫ s in Set.Ici (0 : ℝ), 𝓡(n + 1, 1 + (ε : ℝ)).indicator (epsBasis (n + 1) (ε : ℝ) a α)
        (WithLp.toLp 2 (Gaps246.sliceInsert (n + 1) m s t))) =
      epsBasisMarginal m (ε : ℝ) a α t := by
  let c := epsOuterFace (ε : ℝ) t
  let f : ℝ → ℝ := fun s ↦ 𝓡(n + 1, 1 + (ε : ℝ)).indicator (epsBasis (n + 1) (ε : ℝ) a α)
      (WithLp.toLp 2 (Gaps246.sliceInsert (n + 1) m s t))
  have hc : 0 ≤ c := epsOuterFace_nonneg hε ht
  have hsupport : (∫ s in Set.Ioi (0 : ℝ), f s) = ∫ s in Set.Ioc (0 : ℝ) c, f s := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    · exact Set.Ioc_subset_Ioi_self
    · intro s hs
      have hcs : c < s := not_le.mp fun h ↦ hs.2 ⟨hs.1, h⟩
      unfold f
      rw [Set.indicator_of_notMem (sliceInsert_notMem_scaledStdSimplex m hcs)]
  rw [integral_Ici_eq_integral_Ioi, hsupport, ← intervalIntegral.integral_of_le hc]
  have hon : (∫ s in (0 : ℝ)..c, f s) = ∫ s in (0 : ℝ)..c, epsBasis (n + 1) (ε : ℝ) a α
        (WithLp.toLp 2 (Gaps246.sliceInsert (n + 1) m s t)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) c := by simpa [Set.uIcc_of_le hc] using hs
    unfold f
    rw [Set.indicator_of_mem (sliceInsert_mem_scaledStdSimplex m ht hs'.1 hs'.2)]
  rw [hon, epsBasis_intervalMarginal]

/-- A one-coordinate marginal Gram entry before grouping exponent vectors by the exponent in the
isolated coordinate. -/
def JEpsDirect (n : ℕ) (ε : ℚ) (m : Fin (n + 1))
    (a₁ : ℕ) (α₁ : Multiset ℕ) (a₂ : ℕ) (α₂ : Multiset ℕ) : ℚ :=
  ∑ A ∈ α₁.embeddings (n + 1), ∑ B ∈ α₂.embeddings (n + 1),
    ((A m)! * a₁ ! / (a₁ + A m + 1)!) *
      ((B m)! * a₂ ! / (a₂ + B m + 1)!) *
      radialExplicit (n + ((α₁.sum - A m) + (α₂.sum - B m))) ε ((a₁ + A m + 1) + (a₂ + B m + 1)) *
      ∏ i : Fin n, (A (m.succAbove i) + B (m.succAbove i))!

theorem sum_residual_eq {n : ℕ} {α : Multiset ℕ} {m : Fin (n + 1)}
    {A : Fin (n + 1) → ℕ} (hA : A ∈ α.embeddings (n + 1)) :
    ∑ i : Fin n, A (m.succAbove i) = α.sum - A m := by
  have hsum := sum_eq_of_mem_embeddings hA
  rw [Fin.sum_univ_succAbove _ m] at hsum
  omega

theorem exponentMultiset_split {n : ℕ} (m : Fin (n + 1)) (A : Fin (n + 1) → ℕ) :
    (List.ofFn A : Multiset ℕ) =
      A m ::ₘ (List.ofFn (fun i : Fin n ↦ A (m.succAbove i)) : Multiset ℕ) := by
  induction n with
  | zero =>
    have hm : m = 0 := Fin.eq_zero m
    subst m
    simp
  | succ n ih =>
    refine Fin.cases ?_ (fun m ↦ ?_) m
    · simp [List.ofFn_succ]
    · rw [List.ofFn_succ]
      change ({A 0} : Multiset ℕ) + (List.ofFn (fun i ↦ A i.succ) : Multiset ℕ) = _
      rw [ih m (fun i ↦ A i.succ), List.ofFn_succ]
      simp only [Fin.succ_succAbove_zero, Fin.succ_succAbove_succ]
      exact Quotient.sound (List.Perm.swap _ _ _)

theorem filter_erase_zero (α : Multiset ℕ) : (α.erase 0).filter (· ≠ 0) = α.filter (· ≠ 0) := by
  induction α using Multiset.induction_on with
  | empty => simp
  | @cons a α ih => by_cases ha : a = 0 <;> simp [ha, ih]

theorem filter_erase_ne_zero (α : Multiset ℕ) {r : ℕ} (hr : r ≠ 0) :
    (α.filter (· ≠ 0)).erase r = (α.erase r).filter (· ≠ 0) := by
  induction α using Multiset.induction_on with
  | empty => simp
  | @cons a α ih =>
    by_cases har : a = r
    · subst a
      simp [hr]
    · by_cases ha : a = 0
      · subst a
        simp [har, ih]
      · simp [har, ha, ih]

theorem mem_embeddings_iff_coord_residual {n : ℕ} {α : Multiset ℕ}
    (m : Fin (n + 1)) (A : Fin (n + 1) → ℕ) :
    A ∈ α.embeddings (n + 1) ↔ A m ∈ insert 0 α.toFinset ∧
      (fun i : Fin n ↦ A (m.succAbove i)) ∈ (α.erase (A m)).embeddings n := by
  classical
  rw [Multiset.mem_embeddings_iff, Multiset.mem_embeddings_iff, exponentMultiset_split m A]
  by_cases hr : A m = 0
  · simp [hr, filter_erase_zero]
  · constructor
    · intro h
      have hrmem : A m ∈ α := by
        have : A m ∈ (A m ::ₘ (List.ofFn (fun i : Fin n ↦ A (m.succAbove i)) : Multiset ℕ)).filter
              (· ≠ 0) := by
          simp [hr]
        rw [h] at this
        exact Multiset.mem_of_mem_filter this
      refine ⟨by simp [hr, hrmem], ?_⟩
      have := congrArg (Multiset.erase · (A m)) h
      rw [filter_erase_ne_zero α hr] at this
      simpa [hr] using this
    · rintro ⟨_, h⟩
      have hrmem : A m ∈ α := by simpa [hr] using ‹A m ∈ insert 0 α.toFinset›
      have hα : A m ::ₘ α.erase (A m) = α := Multiset.cons_erase hrmem
      rw [← hα]
      simpa [hr] using congrArg (A m ::ₘ ·) h

/-- Group a sum over exponent embeddings by the exponent in one distinguished coordinate. -/
theorem sum_embeddings_eq_sum_coord {R : Type*} [AddCommMonoid R]
    {n : ℕ} (α : Multiset ℕ) (m : Fin (n + 1))
    (f : ℕ → (Fin n → ℕ) → R) :
    ∑ A ∈ α.embeddings (n + 1), f (A m) (fun i ↦ A (m.succAbove i)) =
      ∑ r ∈ insert 0 α.toFinset, ∑ C ∈ (α.erase r).embeddings n, f r C := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (t := insert 0 α.toFinset)
    (fun A hA ↦ (mem_embeddings_iff_coord_residual m A).mp hA |>.1)
    (fun A ↦ f (A m) (fun i ↦ A (m.succAbove i)))]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_bij (fun A _ ↦ fun i ↦ A (m.succAbove i))
  · intro A hA
    obtain ⟨hA', hcoord⟩ := Finset.mem_filter.mp hA
    rw [← hcoord]
    exact (mem_embeddings_iff_coord_residual m A).mp hA' |>.2
  · intro A₁ hA₁ A₂ hA₂ heq
    have hcoord₁ := (Finset.mem_filter.mp hA₁).2
    have hcoord₂ := (Finset.mem_filter.mp hA₂).2
    funext i
    refine Fin.succAboveCases m ?_ (fun j ↦ ?_) i
    · exact hcoord₁.trans hcoord₂.symm
    · exact congr_fun heq j
  · intro C hC
    let A : Fin (n + 1) → ℕ := m.insertNth r C
    have hA : A ∈ α.embeddings (n + 1) := (mem_embeddings_iff_coord_residual m A).mpr <| by
      simpa [A] using And.intro hr hC
    refine ⟨A, Finset.mem_filter.mpr ⟨hA, by simp [A]⟩, ?_⟩
    funext i
    simp [A]
  · intro A hA
    rw [(Finset.mem_filter.mp hA).2]

theorem epsBasisMarginal_pair_integral {n : ℕ} {ε : ℚ} (hε1 : ε ≤ 1)
    (m : Fin (n + 1)) (a₁ : ℕ) (α₁ : Multiset ℕ) (a₂ : ℕ) (α₂ : Multiset ℕ) :
    (∫ t in 𝓡(n, 1 - (ε : ℝ)),
      epsBasisMarginal m (ε : ℝ) a₁ α₁ t * epsBasisMarginal m (ε : ℝ) a₂ α₂ t) =
      (JEpsDirect n ε m a₁ α₁ a₂ α₂ : ℚ) := by
  classical
  unfold epsBasisMarginal JEpsDirect
  push_cast
  rw [show (fun t : EuclideanSpace ℝ (Fin n) ↦ (∑ A ∈ α₁.embeddings (n + 1),
        ((a₁ ! : ℝ) * (A m)! / (a₁ + A m + 1)!) *
          epsOuterFace (ε : ℝ) t ^ (a₁ + A m + 1) * residualMonomial m A t) *
      (∑ B ∈ α₂.embeddings (n + 1),
        ((a₂ ! : ℝ) * (B m)! / (a₂ + B m + 1)!) *
          epsOuterFace (ε : ℝ) t ^ (a₂ + B m + 1) * residualMonomial m B t)) =
      fun t ↦ ∑ A ∈ α₁.embeddings (n + 1), ∑ B ∈ α₂.embeddings (n + 1),
        (((a₁ ! : ℝ) * (A m)! / (a₁ + A m + 1)!) *
          epsOuterFace (ε : ℝ) t ^ (a₁ + A m + 1) * residualMonomial m A t) *
        (((a₂ ! : ℝ) * (B m)! / (a₂ + B m + 1)!) *
          epsOuterFace (ε : ℝ) t ^ (a₂ + B m + 1) * residualMonomial m B t) by
    funext t
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro A hA
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro B hB
      let C : Fin n → ℕ := fun i ↦ A (m.succAbove i) + B (m.succAbove i)
      rw [show (fun t : EuclideanSpace ℝ (Fin n) ↦
          (((a₁ ! : ℝ) * (A m)! / (a₁ + A m + 1)!) *
            epsOuterFace (ε : ℝ) t ^ (a₁ + A m + 1) * residualMonomial m A t) *
          (((a₂ ! : ℝ) * (B m)! / (a₂ + B m + 1)!) *
            epsOuterFace (ε : ℝ) t ^ (a₂ + B m + 1) * residualMonomial m B t)) =
          fun t ↦ (((a₁ ! : ℝ) * (A m)! / (a₁ + A m + 1)!) *
            ((a₂ ! : ℝ) * (B m)! / (a₂ + B m + 1)!)) *
            ((1 + (ε : ℝ) - ∑ i, t i) ^
              ((a₁ + A m + 1) + (a₂ + B m + 1)) * ∏ i, t i ^ C i) by
        funext t
        unfold epsOuterFace residualMonomial C
        simp_rw [pow_add, Finset.prod_mul_distrib]
        ring]
      rw [integral_const_mul,
        shiftedMonomial_integral n ((a₁ + A m + 1) + (a₂ + B m + 1)) ε hε1 C]
      rw [show ∑ i, C i = (α₁.sum - A m) + (α₂.sum - B m) by
        unfold C
        rw [sum_add_distrib, sum_residual_eq hA, sum_residual_eq hB]]
      push_cast
      ring
    · intro B _
      exact (by fun_prop : Continuous (fun t : EuclideanSpace ℝ (Fin n) ↦
        (((a₁ ! : ℝ) * (A m)! / (a₁ + A m + 1)!) *
          epsOuterFace (ε : ℝ) t ^ (a₁ + A m + 1) * residualMonomial m A t) *
        (((a₂ ! : ℝ) * (B m)! / (a₂ + B m + 1)!) *
          epsOuterFace (ε : ℝ) t ^ (a₂ + B m + 1) *
            residualMonomial m B t))).continuousOn.integrableOn_compact
            (isCompact_scaledStdSimplex (k := n) (s := 1 - (ε : ℝ)))
  · intro A _
    apply integrable_finsetSum
    intro B _
    exact (by fun_prop : Continuous (fun t : EuclideanSpace ℝ (Fin n) ↦
      (((a₁ ! : ℝ) * (A m)! / (a₁ + A m + 1)!) *
        epsOuterFace (ε : ℝ) t ^ (a₁ + A m + 1) * residualMonomial m A t) *
      (((a₂ ! : ℝ) * (B m)! / (a₂ + B m + 1)!) *
        epsOuterFace (ε : ℝ) t ^ (a₂ + B m + 1) *
          residualMonomial m B t))).continuousOn.integrableOn_compact
          (isCompact_scaledStdSimplex (k := n) (s := 1 - (ε : ℝ)))

/-- A single grouped summand of `JEpsExplicit`: the contribution of the pinned exponents
`r₁, r₂` together with the remaining exponent vectors `C₁, C₂`, consisting of the two radial
Beta factors, the radial integral `radialExplicit`, and the factorial moment `∏ (C₁ i + C₂ i)!`. -/
def JEpsGroupedTerm (n : ℕ) (ε : ℚ) (a₁ : ℕ) (α₁ : Multiset ℕ)
    (a₂ : ℕ) (α₂ : Multiset ℕ) (r₁ : ℕ) (C₁ : Fin n → ℕ) (r₂ : ℕ)
    (C₂ : Fin n → ℕ) : ℚ :=
  (r₁ ! * a₁ ! / (a₁ + r₁ + 1)!) *
    (r₂ ! * a₂ ! / (a₂ + r₂ + 1)!) *
    radialExplicit (n + ((α₁.sum - r₁) + (α₂.sum - r₂))) ε ((a₁ + r₁ + 1) + (a₂ + r₂ + 1)) *
    ∏ i, (C₁ i + C₂ i)!

theorem JEpsDirect_eq_explicit {n : ℕ} (ε : ℚ) (m : Fin (n + 1))
    (a₁ : ℕ) (α₁ : Multiset ℕ) (a₂ : ℕ) (α₂ : Multiset ℕ) :
    JEpsDirect n ε m a₁ α₁ a₂ α₂ = JEpsExplicit (n + 1) ε a₁ α₁ a₂ α₂ := by
  classical
  unfold JEpsDirect JEpsExplicit facMoment
  change (∑ A ∈ α₁.embeddings (n + 1), ∑ B ∈ α₂.embeddings (n + 1),
    JEpsGroupedTerm n ε a₁ α₁ a₂ α₂ (A m) (fun i ↦ A (m.succAbove i))
      (B m) (fun i ↦ B (m.succAbove i))) = _
  rw [sum_embeddings_eq_sum_coord α₁ m (fun r₁ C₁ ↦ ∑ B ∈ α₂.embeddings (n + 1),
      JEpsGroupedTerm n ε a₁ α₁ a₂ α₂ r₁ C₁ (B m) (fun i ↦ B (m.succAbove i)))]
  apply Finset.sum_congr rfl
  intro r₁ _
  have hgroup (C₁ : Fin n → ℕ) : (∑ B ∈ α₂.embeddings (n + 1),
        JEpsGroupedTerm n ε a₁ α₁ a₂ α₂ r₁ C₁ (B m) (fun i ↦ B (m.succAbove i))) =
      ∑ r₂ ∈ insert 0 α₂.toFinset, ∑ C₂ ∈ (α₂.erase r₂).embeddings n,
        JEpsGroupedTerm n ε a₁ α₁ a₂ α₂ r₁ C₁ r₂ C₂ :=
    sum_embeddings_eq_sum_coord α₂ m _
  simp_rw [hgroup]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r₂ _
  unfold JEpsGroupedTerm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro C₁ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro C₂ _
  push_cast
  ring_nf
  rfl

theorem epsBasis_supported_integrableOn_Ici {n : ℕ} {ε : ℚ} (hε : 0 ≤ ε)
    (m : Fin (n + 1)) (a : ℕ) (α : Multiset ℕ)
    {t : EuclideanSpace ℝ (Fin n)} (ht : t ∈ 𝓡(n, 1 - (ε : ℝ))) :
    IntegrableOn (fun s : ℝ ↦ 𝓡(n + 1, 1 + (ε : ℝ)).indicator (epsBasis (n + 1) (ε : ℝ) a α)
        (WithLp.toLp 2 (Gaps246.sliceInsert (n + 1) m s t))) (Set.Ici 0) := by
  let c := epsOuterFace (ε : ℝ) t
  let f : ℝ → ℝ := fun s ↦ 𝓡(n + 1, 1 + (ε : ℝ)).indicator (epsBasis (n + 1) (ε : ℝ) a α)
      (WithLp.toLp 2 (Gaps246.sliceInsert (n + 1) m s t))
  let g : ℝ → ℝ := fun s ↦ epsBasis (n + 1) (ε : ℝ) a α
    (WithLp.toLp 2 (Gaps246.sliceInsert (n + 1) m s t))
  have hc : 0 ≤ c := epsOuterFace_nonneg hε ht
  have hg : Continuous g := by
    unfold g
    apply (continuous_epsBasis (n + 1) (ε : ℝ) a α).comp
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro j
    unfold Gaps246.sliceInsert
    split_ifs <;> fun_prop
  have hgInt : IntegrableOn g (Set.Icc 0 c) := hg.continuousOn.integrableOn_compact isCompact_Icc
  have hfInt : IntegrableOn f (Set.Icc 0 c) := by
    refine hgInt.congr_fun ?_ measurableSet_Icc
    intro s hs
    unfold f g
    rw [Set.indicator_of_mem (sliceInsert_mem_scaledStdSimplex m ht hs.1 hs.2)]
  apply hfInt.of_forall_sdiff_eq_zero measurableSet_Ici
  intro s hs
  have hcs : c < s := not_le.mp fun h ↦ hs.2 ⟨hs.1, h⟩
  unfold f
  rw [Set.indicator_of_notMem (sliceInsert_notMem_scaledStdSimplex m hcs)]

theorem EpsCertificateExplicit.supportedPolynomial_eq_sum {n : ℕ} {ε : ℚ}
    (ct : EpsCertificateExplicit (n + 1) ε) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ct.supportedPolynomial x = ∑ i, (ct.coeff i : ℝ) * 𝓡(n + 1, 1 + (ε : ℝ)).indicator
        (epsBasis (n + 1) (ε : ℝ) (ct.a i) (ct.α i)) x := by
  classical
  by_cases hx : x ∈ 𝓡(n + 1, 1 + (ε : ℝ))
  · simp [supportedPolynomial, polynomial, hx]
  · simp [supportedPolynomial, Set.indicator_of_notMem hx]

/-- The concrete coordinate marginal of a certificate polynomial. -/
noncomputable def EpsCertificateExplicit.marginalPolynomial {n : ℕ} {ε : ℚ}
    (ct : EpsCertificateExplicit (n + 1) ε) (m : Fin (n + 1))
    (t : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, (ct.coeff i : ℝ) * epsBasisMarginal m (ε : ℝ) (ct.a i) (ct.α i) t

theorem EpsCertificateExplicit.inner_supportedPolynomial {n : ℕ} {ε : ℚ}
    (ct : EpsCertificateExplicit (n + 1) ε) (hε : 0 ≤ ε) (m : Fin (n + 1))
    {t : EuclideanSpace ℝ (Fin n)} (ht : t ∈ 𝓡(n, 1 - (ε : ℝ))) :
    (∫ s in Set.Ici (0 : ℝ), ct.supportedPolynomial
        (WithLp.toLp 2 (Gaps246.sliceInsert (n + 1) m s t))) =
      ct.marginalPolynomial m t := by
  classical
  simp_rw [ct.supportedPolynomial_eq_sum]
  rw [integral_finsetSum]
  · unfold marginalPolynomial
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul, epsBasis_supportedMarginal hε m (ct.a i) (ct.α i) ht]
  · intro i _
    exact (epsBasis_supported_integrableOn_Ici hε m (ct.a i) (ct.α i) ht).const_mul _

theorem EpsCertificateExplicit.marginalPolynomial_pair_integral {n : ℕ} {ε : ℚ}
    (ct : EpsCertificateExplicit (n + 1) ε) (hε1 : ε ≤ 1) (m : Fin (n + 1)) :
    (∫ t in 𝓡(n, 1 - (ε : ℝ)), ct.marginalPolynomial m t ^ 2) =
      ((∑ i, ∑ j, ct.coeff i * ct.coeff j *
        JEpsExplicit (n + 1) ε (ct.a i) (ct.α i) (ct.a j) (ct.α j) : ℚ) : ℝ) := by
  classical
  unfold marginalPolynomial
  rw [PrimeGaps.setIntegral_sq_sum (isCompact_scaledStdSimplex (k := n) (s := 1 - (ε : ℝ)))
    (fun i ↦ (ct.coeff i : ℝ)) (fun i ↦ epsBasisMarginal m (ε : ℝ) (ct.a i) (ct.α i))
    (fun i ↦ by fun_prop)]
  push_cast
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [epsBasisMarginal_pair_integral hε1 m (ct.a i) (ct.α i) (ct.a j) (ct.α j),
    JEpsDirect_eq_explicit]

theorem EpsCertificateExplicit.jEps_eq_explicit {n : ℕ} {ε : ℚ}
    (ct : EpsCertificateExplicit (n + 1) ε) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (m : Fin (n + 1)) :
    Gaps246.jEps (n + 1) (ε : ℝ) m ct.supportedPolynomial = ((∑ i, ∑ j, ct.coeff i * ct.coeff j *
        JEpsExplicit (n + 1) ε (ct.a i) (ct.α i) (ct.a j) (ct.α j) : ℚ) : ℝ) := by
  unfold Gaps246.jEps
  rw [show Gaps246.shrunkenSlice (n + 1) (ε : ℝ) = 𝓡(n, 1 - (ε : ℝ)) by rfl]
  change (∫ t : EuclideanSpace ℝ (Fin n) in 𝓡(n, 1 - (ε : ℝ)),
    (∫ s in Set.Ici (0 : ℝ), ct.supportedPolynomial
      (WithLp.toLp 2 (Gaps246.sliceInsert (n + 1) m s t))) ^ 2) = _
  rw [setIntegral_congr_fun
    (isClosed_scaledStdSimplex (k := n) (s := 1 - (ε : ℝ))).measurableSet
    (fun t ht ↦ by rw [ct.inner_supportedPolynomial hε m ht])]
  exact ct.marginalPolynomial_pair_integral hε1 m

theorem EpsCertificateExplicit.JEps_toLp_eq_explicit {n : ℕ} {ε : ℚ}
    (ct : EpsCertificateExplicit (n + 1) ε) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (m : Fin (n + 1)) :
    JEps (ε : ℝ) m ct.toLp = ((∑ i, ∑ j, ct.coeff i * ct.coeff j *
        JEpsExplicit (n + 1) ε (ct.a i) (ct.α i) (ct.a j) (ct.α j) : ℚ) : ℝ) := by
  rw [← ct.supported_toLp_eq]
  change Gaps246.enlargedJQF (ε : ℝ) m
      (ct.supportedPolynomial_memLp.toLp ct.supportedPolynomial) = _
  rw [Gaps246.enlargedJQF_toLp_eq_jEps (ε : ℝ) m ct.supportedPolynomial
    ct.supportedPolynomial_memLp (fun x hx ↦ Set.indicator_of_notMem hx ct.polynomial)]
  exact ct.jEps_eq_explicit hε hε1 m

theorem EpsCertificateExplicit.sum_JEps_toLp_eq_explicit {n : ℕ} {ε : ℚ}
    (ct : EpsCertificateExplicit (n + 1) ε) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ∑ m, JEps (ε : ℝ) m ct.toLp = (((n + 1) * ∑ i, ∑ j, ct.coeff i * ct.coeff j *
        JEpsExplicit (n + 1) ε (ct.a i) (ct.α i) (ct.a j) (ct.α j) : ℚ) : ℝ) := by
  rw [Finset.sum_congr rfl fun m _ ↦ ct.JEps_toLp_eq_explicit hε hε1 m,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- Convert an explicit rational certificate into the analytic `L²` certificate represented by
its monomial-symmetric polynomial. -/
noncomputable def EpsCertificateExplicit.toAbstract {k : ℕ} {ε : ℚ}
    (ct : EpsCertificateExplicit k ε) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    EpsCertificate k (ε : ℝ) := by
  cases k with
  | zero =>
      exfalso
      -- The `I`-form is the squared norm of `ct.toLp`, hence nonnegative, while `cert` at `k = 0`
      -- makes it negative.
      have hi : (0 : ℚ) ≤ ∑ i, ∑ j, ct.coeff i * ct.coeff j *
          IEpsExplicit 0 ε (ct.a i) (ct.α i) (ct.a j) (ct.α j) := by
        have hnorm : (0 : ℝ) ≤ ((∑ i, ∑ j, ct.coeff i * ct.coeff j *
            IEpsExplicit 0 ε (ct.a i) (ct.α i) (ct.a j) (ct.α j) : ℚ) : ℝ) := by
          rw [← ct.norm_sq_eq_explicit (by linarith)]
          positivity
        exact_mod_cast hnorm
      have hc := ct.cert
      simp only [Nat.cast_zero, zero_mul] at hc
      linarith
  | succ n =>
      refine ⟨ct.toLp, ?_⟩
      rw [ct.norm_sq_eq_explicit (by positivity), ct.sum_JEps_toLp_eq_explicit hε hε1]
      exact_mod_cast ct.cert

end PrimeGaps
