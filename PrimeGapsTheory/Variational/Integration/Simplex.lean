/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Analysis.Simplex
public import PrimeGapsTheory.Analysis.Tonelli.EuclideanLemmas
public import PrimeGapsTheory.Variational.Integration.Beta
public import PrimeGapsTheory.Variational.PartitionCounts

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Dirichlet integral over the standard simplex

The Lebesgue integral of `(1 - x₁ - ⋯ - x_k)^a · ∏ᵢ xᵢ^{aᵢ}` over the standard simplex
`𝓡 k ⊆ EuclideanSpace ℝ (Fin k)` is evaluated in terms of factorials.

## Main results

* `dirichlet_integral`: The factorial formula for the Dirichlet integral on `𝓡 k`.
* `lem_integration_formula`: The integral of `(1 - ∑ tᵢ)^a · (∑ tᵢ²)^b`.
* `lem_integration_prime`: The corresponding integral in dimension `k - 1`.
-/

@[expose] public section

open Real

open scoped Nat

section

open MeasureTheory Finset EuclideanSpace
open scoped PrimeGaps

local notation "ES(" 𝕜:65 ", " k:65 ")" => EuclideanSpace 𝕜 (Fin k)

namespace EuclideanSpace

/-- For a negative bound the scaled simplex is empty. -/
theorem scaledStdSimplex_empty_of_neg (n : ℕ) (r : ℝ) (hr : r < 0) :
    𝓡(n, r) = ∅ := by
  ext t
  simp only [EuclideanSpace.scaledStdSimplex, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
    iff_false, not_and]
  intro hpos
  have : (0 : ℝ) ≤ ∑ i, t i := Finset.sum_nonneg (fun i _ ↦ hpos i)
  linarith

/-- The `0`-dimensional Euclidean space is a single point of unit volume.  This is the base case
of every induction on the dimension of a simplex integral, where `∫ over 𝓡 0` collapses to
evaluation at the unique point. -/
theorem volumeReal_univ_euclideanSpace_zero : volume.real (Set.univ : Set (ES(ℝ, 0))) = 1 := by
  have hp : MeasurePreserving (WithLp.ofLp : ES(ℝ, 0) → (Fin 0 → ℝ))
      (volume : Measure (ES(ℝ, 0))) (volume : Measure (Fin 0 → ℝ)) :=
    PiLp.volume_preserving_ofLp _
  have h1 : volume (Set.univ : Set (ES(ℝ, 0))) =
      volume ((WithLp.ofLp : ES(ℝ, 0) → (Fin 0 → ℝ)) ⁻¹' Set.univ) := by
    simp
  rw [measureReal_def, h1, hp.measure_preimage MeasurableSet.univ.nullMeasurableSet,
    volume_pi]
  simp

/-- The L² vector obtained by prepending `x` to the coordinates of `t`. -/
def consLp {n : ℕ} (x : ℝ) (t : ES(ℝ, n)) : ES(ℝ, n + 1) := WithLp.toLp 2 (Fin.cons x t.ofLp)

/-- The zeroth coordinate of `consLp x t` is `x`. -/
@[simp] lemma consLp_zero {n : ℕ} (x : ℝ) (t : ES(ℝ, n)) : (consLp x t) 0 = x := by
  simp [consLp]

/-- The later coordinates of `consLp x t` are those of `t`. -/
@[simp] lemma consLp_succ {n : ℕ} (x : ℝ) (t : ES(ℝ, n)) (j : Fin n) :
    (consLp x t) j.succ = t j := by
  simp [consLp]

/-- `∑ i, (consLp x t) i = x + ∑ j, t j`. -/
lemma sum_consLp {n : ℕ} (x : ℝ) (t : ES(ℝ, n)) : ∑ i, (consLp x t) i = x + ∑ j, t j := by
  simp [Fin.sum_univ_succ]

/-- `∏ i, (consLp x t) i ^ e i = x ^ e 0 * ∏ j, t j ^ e j.succ`. -/
lemma prod_consLp {n : ℕ} (x : ℝ) (t : ES(ℝ, n)) (e : Fin (n + 1) → ℕ) :
    ∏ i, (consLp x t) i ^ (e i) = x ^ (e 0) * ∏ j, (t j) ^ (e j.succ) := by
  simp [Fin.prod_univ_succ]

/-- `consLp x t` is coordinatewise nonnegative iff `0 ≤ x` and `t` is. -/
lemma forall_consLp_nonneg {n : ℕ} {x : ℝ} {t : ES(ℝ, n)} :
    (∀ i, 0 ≤ (consLp x t) i) ↔ 0 ≤ x ∧ ∀ j, 0 ≤ t j := by
  rw [Fin.forall_fin_succ, consLp_zero]
  refine ⟨fun ⟨h0, hsucc⟩ ↦ ⟨h0, fun j ↦ ?_⟩, fun ⟨h0, hsucc⟩ ↦ ⟨h0, fun j ↦ ?_⟩⟩
  · rw [← consLp_succ x t j]; exact hsucc j
  · rw [consLp_succ]; exact hsucc j

/-- The L² vector obtained by inserting `s` into `t` at position `m`. -/
def insertLp {n : ℕ} (m : Fin (n + 1)) (s : ℝ) (t : ES(ℝ, n)) : ES(ℝ, n + 1) :=
  WithLp.toLp 2 (m.insertNth s t.ofLp)

/-- The `m`-th coordinate of `insertLp m s t` is `s`. -/
@[simp] lemma insertLp_apply_same {n : ℕ} (m : Fin (n + 1)) (s : ℝ) (t : ES(ℝ, n)) :
    (insertLp m s t) m = s := by
  simp [insertLp, Fin.insertNth_apply_same]

/-- The coordinates of `insertLp m s t` away from `m` are those of `t`. -/
@[simp] lemma insertLp_apply_succAbove {n : ℕ} (m : Fin (n + 1)) (s : ℝ) (t : ES(ℝ, n))
    (j : Fin n) : (insertLp m s t) (m.succAbove j) = t j := by
  simp [insertLp, Fin.insertNth_apply_succAbove]

/-- `∑ i, (insertLp m s t) i = s + ∑ j, t j`. -/
lemma sum_insertLp {n : ℕ} (m : Fin (n + 1)) (s : ℝ) (t : ES(ℝ, n)) :
    ∑ i, (insertLp m s t) i = s + ∑ j, t j := by
  rw [Fin.sum_univ_succAbove _ m, insertLp_apply_same]
  congr 1
  exact Finset.sum_congr rfl (fun j _ ↦ insertLp_apply_succAbove m s t j)

/-- `∑ i, (insertLp m s t) i ^ 2 = s ^ 2 + ∑ j, (t j) ^ 2`. -/
lemma sq_sum_insertLp {n : ℕ} (m : Fin (n + 1)) (s : ℝ) (t : ES(ℝ, n)) :
    ∑ i, (insertLp m s t) i ^ 2 = s ^ 2 + ∑ j, (t j) ^ 2 := by
  rw [Fin.sum_univ_succAbove _ m, insertLp_apply_same]
  congr 1
  exact Finset.sum_congr rfl (fun j _ ↦ by rw [insertLp_apply_succAbove])

/-- `insertLp m s t` is coordinatewise nonnegative iff `0 ≤ s` and `t` is. -/
lemma forall_insertLp_nonneg {n : ℕ} {m : Fin (n + 1)} {s : ℝ} {t : ES(ℝ, n)} :
    (∀ i, 0 ≤ (insertLp m s t) i) ↔ 0 ≤ s ∧ ∀ j, 0 ≤ t j := by
  refine ⟨fun h ↦ ⟨?_, fun j ↦ ?_⟩, fun ⟨hs, ht⟩ i ↦ ?_⟩
  · have := h m; rwa [insertLp_apply_same] at this
  · have := h (m.succAbove j); rwa [insertLp_apply_succAbove] at this
  · refine Fin.succAboveCases m ?_ ?_ i
    · rw [insertLp_apply_same]; exact hs
    · intro j; rw [insertLp_apply_succAbove]; exact ht j

/-- `Fin.insertNth m s` and `Fin.cons s` give the same L² element when combined with the
`(𝓡 (n+1))`-membership predicate: both correspond to the same set of nonneg constraints and
sum constraint. -/
lemma insertLp_mem_R_iff_consLp_mem_R {n : ℕ} (m : Fin (n + 1)) (s : ℝ) (t : ES(ℝ, n)) :
    insertLp m s t ∈ 𝓡 (n + 1) ↔ consLp s t ∈ 𝓡 (n + 1) := by
  change ((∀ i, 0 ≤ (insertLp m s t) i) ∧ ∑ i, (insertLp m s t) i ≤ 1) ↔
    ((∀ i, 0 ≤ (consLp s t) i) ∧ ∑ i, (consLp s t) i ≤ 1)
  rw [forall_insertLp_nonneg, forall_consLp_nonneg, sum_insertLp, sum_consLp]

/-- The section of the `(n+1)`-dimensional integrand at a fixed nonnegative first
coordinate `x` reduces to the scaled-simplex integral in the remaining `n`
coordinates, with the `x^(e 0)` factor pulled out. -/
theorem dirichlet_peel_section (n a : ℕ) (e : Fin (n + 1) → ℕ) (s x : ℝ) (hx : 0 ≤ x) :
    (∫ t' : ES(ℝ, n), 𝓡(n + 1, s).indicator
          (fun t ↦ (s - ∑ i, t i) ^ a * ∏ i, (t i) ^ (e i)) (consLp x t')) =
      x ^ (e 0) * ∫ t' in 𝓡(n, s - x),
          ((s - x) - ∑ j, t' j) ^ a * ∏ j, (t' j) ^ (e j.succ) := by
  have hfun : (fun t' : ES(ℝ, n) ↦ 𝓡(n + 1, s).indicator
          (fun t ↦ (s - ∑ i, t i) ^ a * ∏ i, (t i) ^ (e i)) (consLp x t')) =
      𝓡(n, s - x).indicator (fun t' ↦ x ^ (e 0) *
            (((s - x) - ∑ j, t' j) ^ a * ∏ j, (t' j) ^ (e j.succ))) := by
    funext t'
    by_cases hmem : t' ∈ 𝓡(n, s - x)
    · have hmem' : consLp x t' ∈ 𝓡(n + 1, s) := by
        obtain ⟨h1, h2⟩ := hmem
        refine ⟨?_, ?_⟩
        · rw [forall_consLp_nonneg]; exact ⟨hx, h1⟩
        · rw [sum_consLp]; linarith
      rw [Set.indicator_of_mem hmem', Set.indicator_of_mem hmem, sum_consLp, prod_consLp]
      ring
    · have hmem' : consLp x t' ∉ 𝓡(n + 1, s) := by
        intro hcon
        apply hmem
        obtain ⟨h1, h2⟩ := hcon
        rw [forall_consLp_nonneg] at h1
        rw [sum_consLp] at h2
        exact ⟨h1.2, by linarith⟩
      rw [Set.indicator_of_notMem hmem', Set.indicator_of_notMem hmem]
  rw [hfun, integral_indicator
    EuclideanSpace.isClosed_scaledStdSimplex.measurableSet]
  rw [integral_const_mul]

/-- The section integral vanishes when the first coordinate is negative. -/
theorem dirichlet_peel_section_neg (n a : ℕ) (e : Fin (n + 1) → ℕ) (s x : ℝ) (hx : x < 0) :
    (∫ t' : ES(ℝ, n), 𝓡(n + 1, s).indicator
          (fun t ↦ (s - ∑ i, t i) ^ a * ∏ i, (t i) ^ (e i)) (consLp x t')) = 0 := by
  have hfun : (fun t' : ES(ℝ, n) ↦ 𝓡(n + 1, s).indicator
          (fun t ↦ (s - ∑ i, t i) ^ a * ∏ i, (t i) ^ (e i)) (consLp x t')) = 0 := by
    funext t'
    apply Set.indicator_of_notMem
    intro ⟨hpos, _⟩
    have := hpos 0
    rw [consLp_zero] at this
    linarith
  rw [hfun]; simp

end EuclideanSpace

namespace Real

/-- For `s ≥ 0`,
`∫_0^s (s - t)^a · t^e dt = s^(a+e+1) · a!·e! / (a+e+1)!`. -/
theorem betaIntegralNat (a e : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    (∫ t in Set.Ioo (0 : ℝ) s, (s - t) ^ a * t ^ e) =
      s ^ (a + e + 1) * (a ! * e ! : ℝ) / (a + e + 1)! := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hs,
    PrimeGaps.integral_complement_pow_mul_pow a e s]
  ring

end Real

namespace EuclideanSpace

/-- First component of `finIsolateEquivProd ℝ 0` at coordinate `j : Fin n` is the
`j.succ`-th coordinate of the input. -/
lemma finIsolateEquivProd_zero_fst_apply {n : ℕ} (v : ES(ℝ, n + 1)) (j : Fin n) :
    ((EuclideanSpace.finIsolateEquivProd ℝ (0 : Fin (n + 1))) v).1 j = v j.succ := by
  change v.ofLp ⟨if (j : ℕ) < 0 then j else (j : ℕ) + 1, by grind⟩ = v.ofLp j.succ
  have : (⟨if (j : ℕ) < 0 then j else (j : ℕ) + 1, by grind⟩ : Fin (n + 1)) = j.succ := by
    apply Fin.ext; simp
  rw [this]

/-- Second component of `finIsolateEquivProd ℝ 0` at (the unique) coord `0 : Fin 1` is the
`0`-th coordinate of the input. -/
lemma finIsolateEquivProd_zero_snd_apply {n : ℕ} (v : ES(ℝ, n + 1)) :
    ((EuclideanSpace.finIsolateEquivProd ℝ (0 : Fin (n + 1))) v).2 0 = v 0 := rfl

/-- Forward computation of `finIsolateEquivProd ℝ 0` on `consLp x rest`. -/
lemma finIsolateEquivProd_zero_consLp {n : ℕ} (x : ℝ) (rest : ES(ℝ, n)) :
    (EuclideanSpace.finIsolateEquivProd ℝ (0 : Fin (n + 1))) (consLp x rest) =
      (rest, WithLp.toLp 2 (fun _ : Fin 1 ↦ x)) := by
  refine Prod.ext (PiLp.ext fun j ↦ ?_) (PiLp.ext fun i ↦ ?_)
  · rw [finIsolateEquivProd_zero_fst_apply, consLp_succ]
  · rw [Subsingleton.elim i 0, finIsolateEquivProd_zero_snd_apply, consLp_zero]

/-- Any element of `ES(ℝ, 1)` is the L² promotion of its constant value at `0`. -/
lemma es_one_ext (first : ES(ℝ, 1)) : first = WithLp.toLp 2 (fun _ : Fin 1 ↦ first 0) :=
  PiLp.ext fun i ↦ by rw [Subsingleton.elim i 0]

/-- Inversion identity: `(finIsolateEquivProd ℝ 0).symm (rest, first) = consLp (first 0) rest`. -/
lemma finIsolateEquivProd_zero_symm_apply {n : ℕ} (rest : ES(ℝ, n)) (first : ES(ℝ, 1)) :
    (EuclideanSpace.finIsolateEquivProd ℝ (0 : Fin (n + 1))).symm (rest, first) =
      consLp (first 0) rest := by
  apply (EuclideanSpace.finIsolateEquivProd ℝ (0 : Fin (n + 1))).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, finIsolateEquivProd_zero_consLp, ← es_one_ext first]

/-- The measurable equivalence from `ES(ℝ, 1)` to `ℝ` given by its unique coordinate. -/
noncomputable def esOneEquiv : ES(ℝ, 1) ≃ᵐ ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans (MeasurableEquiv.funUnique (Fin 1) ℝ)

/-- `esOneEquiv y = y 0`. -/
@[simp] lemma esOneEquiv_apply (y : ES(ℝ, 1)) : esOneEquiv y = y 0 := rfl

/-- The equivalence `esOneEquiv` preserves volume. -/
lemma measurePreserving_esOneEquiv : MeasurePreserving esOneEquiv volume volume :=
  (volume_preserving_funUnique (Fin 1) ℝ).comp (PiLp.volume_preserving_ofLp _)

/-- The integral over the `(n+1)`-dimensional scaled simplex as an iterated integral
over its first coordinate and the remaining `n` coordinates. -/
theorem dirichlet_peel (n : ℕ) (a : ℕ) (e : Fin (n + 1) → ℕ) (s : ℝ) :
    (∫ t in 𝓡(n + 1, s), (s - ∑ i, t i) ^ a * ∏ i, (t i) ^ (e i)) =
      ∫ x in Set.Ioo (0 : ℝ) s, (x ^ (e 0)) *
        (∫ t' in 𝓡(n, s - x), ((s - x) - ∑ j, t' j) ^ a *
          ∏ j, (t' j) ^ (e j.succ)) := by
  classical
  set F : ES(ℝ, n + 1) → ℝ := fun t ↦ (s - ∑ i, t i) ^ a * ∏ i, (t i) ^ (e i) with hF
  set eqv : ES(ℝ, n + 1) ≃ᵐ ES(ℝ, n) × ES(ℝ, 1) :=
    (EuclideanSpace.finIsolateEquivProd ℝ (0 : Fin (n + 1))).toHomeomorph.toMeasurableEquiv
  have hmp_symm :
      MeasurePreserving eqv.symm (volume.prod volume) (volume : Measure (ES(ℝ, n + 1))) :=
    measurePreserving_symm_finIsolateEquivProd (0 : Fin (n + 1))
  rw [← integral_indicator EuclideanSpace.isClosed_scaledStdSimplex.measurableSet]
  rw [← MeasurePreserving.integral_comp' hmp_symm]
  have hInt : Integrable (𝓡(n + 1, s).indicator F)
      (volume : Measure (ES(ℝ, n + 1))) := by
    apply IntegrableOn.integrable_indicator _
      EuclideanSpace.isClosed_scaledStdSimplex.measurableSet
    apply ContinuousOn.integrableOn_compact EuclideanSpace.isCompact_scaledStdSimplex
    rw [hF]
    exact Continuous.continuousOn (by fun_prop)
  have hIntComp : Integrable (fun z : ES(ℝ, n) × ES(ℝ, 1) ↦
      𝓡(n + 1, s).indicator F (eqv.symm z)) (volume.prod volume) :=
    (hmp_symm.integrable_comp hInt.aestronglyMeasurable).mpr hInt
  rw [integral_prod _ hIntComp]
  have hcons : ∀ (rest : ES(ℝ, n)) (first : ES(ℝ, 1)),
      eqv.symm (rest, first) = consLp (first 0) rest := fun rest first ↦
    finIsolateEquivProd_zero_symm_apply rest first
  simp_rw [hcons]
  have hInt' : Integrable (fun z : ES(ℝ, n) × ES(ℝ, 1) ↦
        𝓡(n + 1, s).indicator F (consLp (z.2 0) z.1))
      (volume.prod volume) := by
    convert hIntComp using 1
    funext z
    exact congrArg _ (hcons z.1 z.2).symm
  have hstep : (∫ (rest : ES(ℝ, n)), ∫ (first : ES(ℝ, 1)),
                  𝓡(n + 1, s).indicator F (consLp (first 0) rest)) =
             (∫ (first : ES(ℝ, 1)), ∫ (rest : ES(ℝ, n)),
                  𝓡(n + 1, s).indicator F
                    (consLp (first 0) rest)) := by
    rw [← integral_prod _ hInt', ← integral_prod_symm _ hInt']
  rw [hstep]
  simp_rw [show ∀ (first : ES(ℝ, 1)), first 0 = esOneEquiv first from fun _ ↦ rfl]
  rw [measurePreserving_esOneEquiv.integral_comp' (fun x ↦ ∫ (rest : ES(ℝ, n)),
    𝓡(n + 1, s).indicator F (consLp x rest))]
  rw [← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  have hN : volume ({0, s} : Set ℝ) = 0 :=
    Set.Countable.measure_zero (Set.countable_insert.mpr (Set.countable_singleton s)) _
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ ({0, s} : Set ℝ) := by
    rw [ae_iff]
    convert hN using 2
    ext x; push Not; rfl
  filter_upwards [hae] with x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
  obtain ⟨hx0, hxs⟩ := hx
  by_cases hxpos : 0 ≤ x
  · have hxpos' : 0 < x := lt_of_le_of_ne hxpos (Ne.symm hx0)
    rw [hF, dirichlet_peel_section n a e s x hxpos]
    by_cases hxlt : x < s
    · rw [Set.indicator_of_mem (Set.mem_Ioo.mpr ⟨hxpos', hxlt⟩)]
    · push Not at hxlt
      have hxgt : s < x := lt_of_le_of_ne hxlt (Ne.symm hxs)
      rw [Set.indicator_of_notMem (by simp only [Set.mem_Ioo, not_and, not_lt]; intro _; linarith)]
      rw [scaledStdSimplex_empty_of_neg n (s - x) (by linarith)]
      simp
  · push Not at hxpos
    rw [hF, dirichlet_peel_section_neg n a e s x hxpos]
    rw [Set.indicator_of_notMem (by simp only [Set.mem_Ioo, not_and, not_lt]; intro h; linarith)]

/-- For `s ≥ 0`, `∫_{EuclideanSpace.scaledStdSimplex k s} (s - ∑ x_i)^a · ∏ x_i^{e_i} dx =
s^(k+a+∑e_i) · a!·∏e_i! / (k+a+∑e_i)!`. -/
theorem dirichlet_scaled (k : ℕ) (a : ℕ) (e : Fin k → ℕ) (s : ℝ) (hs : 0 ≤ s) :
    (∫ t in 𝓡(k, s), (s - ∑ i, t i) ^ a * ∏ i, (t i) ^ (e i)) =
      s ^ (k + a + ∑ i, e i) * (a ! * ∏ i, (e i)! : ℝ) /
        (k + a + ∑ i, e i)! := by
  induction k generalizing a s with
  | zero =>
    have hregion : 𝓡(0, s) = (Set.univ : Set (ES(ℝ, 0))) := by
      ext t
      simp [EuclideanSpace.scaledStdSimplex, hs]
    rw [hregion]
    simp only [Fin.sum_univ_zero, Fin.prod_univ_zero, sub_zero, mul_one, Nat.add_zero,
      Nat.zero_add, Nat.cast_one]
    rw [setIntegral_univ, integral_const, volumeReal_univ_euclideanSpace_zero, one_smul]
    have hfac : (a ! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos a).ne'
    rw [mul_div_assoc, div_self hfac, mul_one]
  | succ n ih =>
    set e' : Fin n → ℕ := fun j ↦ e j.succ with he'
    set Se : ℕ := ∑ j, e' j with hSe
    rw [dirichlet_peel n a e s]
    have hcongr : (∫ x in Set.Ioo (0 : ℝ) s, (x ^ (e 0)) *
        (∫ t' in 𝓡(n, s - x), ((s - x) - ∑ j, t' j) ^ a *
          ∏ j, (t' j) ^ (e j.succ))) = ∫ x in Set.Ioo (0 : ℝ) s,
          (a ! * ∏ j, (e' j)! : ℝ) / (n + a + Se)! *
          ((s - x) ^ (n + a + Se) * x ^ (e 0)) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      simp only [Set.mem_Ioo] at hx
      have hsx : (0 : ℝ) ≤ s - x := by linarith [hx.2]
      have hinner : (∫ t' in 𝓡(n, s - x), ((s - x) - ∑ j, t' j) ^ a *
          ∏ j, (t' j) ^ (e j.succ)) =
          (s - x) ^ (n + a + Se) * (a ! * ∏ j, (e' j)! : ℝ) /
            (n + a + Se)! := by
        rw [hSe]
        exact ih a e' (s - x) hsx
      simp only
      rw [hinner]
      ring
    rw [hcongr, integral_const_mul, betaIntegralNat (n + a + Se) (e 0) s hs]
    have hsum : ∑ i, e i = e 0 + Se := by
      rw [hSe, he', Fin.sum_univ_succ]
    have hprod : ∏ i, (e i)! = (e 0)! * ∏ j, (e' j)! := by
      rw [he', Fin.prod_univ_succ]
    have hexp : (n + a + Se) + (e 0) + 1 = n + 1 + a + (e 0 + Se) := by ring
    rw [hsum, hprod, hexp]
    have hfac : ((n + a + Se)! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have hfac2 : ((n + 1 + a + (e 0 + Se))! : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.factorial_pos _).ne'
    push_cast
    field_simp

/-- The integral of `(1 - ∑ x_i)^a · ∏ x_i^{e i}` over
`𝓡 k ⊆ EuclideanSpace ℝ (Fin k)` equals
`a! · ∏ (e i)! / (k + a + ∑ e i)!`. -/
@[pg_tag "bg246" "lem_monomial_integration"]
theorem dirichlet_integral (k : ℕ) (a : ℕ) (e : Fin k → ℕ) :
    (∫ x in 𝓡 k, (1 - ∑ i, x i) ^ a * ∏ i, (x i) ^ (e i)) =
      (a ! * ∏ i, (e i)! : ℝ) / (k + a + ∑ i, e i)! := by
  simpa using dirichlet_scaled k a e 1 (by norm_num)

end EuclideanSpace

end

open scoped BigOperators PrimeGaps
open Finset MeasureTheory EuclideanSpace

local notation "ES(" 𝕜:65 ", " k:65 ")" => EuclideanSpace 𝕜 (Fin k)

section

namespace PrimeGaps

/-- The factorial formula for the images under `Rk_integral` of
`(1 - ∑ tᵢ)^a · (∑ tᵢ²)^b`. -/
def IsFactorialMoment {k : ℕ} (Rk_integral : (ES(ℝ, k) → ℝ) → ℝ) (G : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ (a' b' : ℕ), Rk_integral (fun t ↦ (1 - ∑ i, t i) ^ a' * (∑ i, (t i) ^ 2) ^ b') =
      (a' ! : ℝ) * (G b' 2 k : ℝ) / ((k + a' + 2 * b')! : ℝ)

end PrimeGaps

namespace IntegrationFormula

open PrimeGaps

/-- Block weight `(2 b)! / b!`. -/
def blockWeight (bi : ℕ) : ℕ := (2 * bi)! / bi !

/-- Natural division distributes over a product of exact quotients:
`∏ i ∈ s, f i / g i = (∏ i ∈ s, f i) / ∏ i ∈ s, g i` when `g i ∣ f i` on `s`. -/
lemma prod_div {α} (s : Finset α) (f g : α → ℕ) (h : ∀ i ∈ s, g i ∣ f i) :
    ∏ i ∈ s, f i / g i = (∏ i ∈ s, f i) / (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha,
        ih (fun i hi ↦ h i (Finset.mem_insert_of_mem hi)),
        Nat.div_mul_div_comm (h a (Finset.mem_insert_self a s))
          (Finset.prod_dvd_prod_of_dvd g f (fun i hi ↦ h i (Finset.mem_insert_of_mem hi)))]

/-- `(B / Q) * R = B * (R / Q)` in `ℕ`, given `Q ∣ B` and `Q ∣ R`. -/
lemma per_div (Q R B : ℕ) (hQb : Q ∣ B) (hQR : Q ∣ R) : (B / Q) * R = B * (R / Q) := by
  rw [Nat.mul_comm (B / Q) R, ← Nat.mul_div_assoc _ hQb, Nat.mul_comm R B, Nat.mul_div_assoc _ hQR]

/-- `maynardG b 2 k` as a factorial-weighted sum over `piAntidiag`. -/
lemma Gbj_bfact (k b : ℕ) : maynardG b 2 k =
      b ! * ∑ v ∈ (univ : Finset (Fin k)).piAntidiag b, ∏ i, blockWeight (v i) := by
  unfold maynardG blockWeight
  rw [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple]

/-- The multinomial form of `maynardG`:
`∑_{v ∈ piAntidiag b} (b! / ∏ᵢ (vᵢ)!) * ∏ᵢ (2 vᵢ)! = maynardG b 2 k`. -/
lemma key_nat (k b : ℕ) : (∑ v ∈ (univ : Finset (Fin k)).piAntidiag b,
        (b ! / ∏ i, (v i)!) * ∏ i, (2 * v i)!) = maynardG b 2 k := by
  rw [Gbj_bfact k b, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  have hsum : ∑ i, v i = b := by have := (mem_piAntidiag.mp hv).1; simpa using this
  have hQb : (∏ i, (v i)!) ∣ b ! := by
    have := Nat.prod_factorial_dvd_factorial_sum (univ : Finset (Fin k)) v
    simpa [hsum] using this
  have hQR : (∏ i, (v i)!) ∣ ∏ i, (2 * v i)! :=
    Finset.prod_dvd_prod_of_dvd _ _ (fun i _ ↦ Nat.factorial_dvd_factorial (by omega))
  have hW : ∏ i, blockWeight (v i) = (∏ i, (2 * v i)!) / (∏ i, (v i)!) := by
    simp only [blockWeight]
    exact prod_div _ (fun i ↦ (2 * v i)!) (fun i ↦ (v i)!)
      (fun i _ ↦ Nat.factorial_dvd_factorial (by omega))
  rw [hW]
  exact per_div _ _ _ hQb hQR

/-- On the L² simplex `𝓡 k`, the polynomial
`(1 - ∑ tᵢ)^a · (∑ tᵢ²)^b` integrates to `a! · G_{b,2}(k) / (k + a + 2b)!`. -/
theorem lem_integration_formula_real (k : ℕ) (a b : ℕ) :
    (∫ t in 𝓡 k, (1 - ∑ i, t i) ^ a * (∑ i, (t i) ^ 2) ^ b) =
      (a ! : ℝ) * (maynardG b 2 k : ℝ) / ((k + a + 2 * b)! : ℝ) := by
  have hcpt : IsCompact (𝓡 k) := EuclideanSpace.isCompact_scaledStdSimplex
  have hexp : ∀ t : ES(ℝ, k),
      (1 - ∑ i, t i) ^ a * (∑ i, (t i) ^ 2) ^ b = ∑ v ∈ (univ : Finset (Fin k)).piAntidiag b,
            (((b ! / ∏ i, (v i)! : ℕ) : ℝ) *
              ((1 - ∑ i, t i) ^ a * ∏ i, (t i) ^ (2 * v i))) := by
    intro t
    rw [PrimeGaps.lem_multinomial_Pj k (fun i ↦ t i) 2 b, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun v _ ↦ by ring)
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun v _ ↦
        ContinuousOn.integrableOn_compact hcpt (by fun_prop))]
  have hstep : ∀ v ∈ (univ : Finset (Fin k)).piAntidiag b, (∫ t in 𝓡 k,
          ((b ! / ∏ i, (v i)! : ℕ) : ℝ) *
            ((1 - ∑ i, t i) ^ a * ∏ i, (t i) ^ (2 * v i))) =
      ((b ! / ∏ i, (v i)! : ℕ) : ℝ) *
          ((a ! : ℝ) * (∏ i, ((2 * v i)! : ℝ)) /
            ((k + a + 2 * b)! : ℝ)) := by
    intro v hv
    have hsum : ∑ i, v i = b := by simpa using (mem_piAntidiag.mp hv).1
    rw [integral_const_mul, dirichlet_integral k a (fun i ↦ 2 * v i)]
    have he : (k + a + ∑ i, 2 * v i) = k + a + 2 * b := by rw [← Finset.mul_sum, hsum]
    rw [he, Nat.cast_prod]
  rw [Finset.sum_congr rfl hstep]
  have hcast : (∑ v ∈ (univ : Finset (Fin k)).piAntidiag b,
      ((b ! / ∏ i, (v i)! : ℕ) : ℝ) * ∏ i, ((2 * v i)! : ℝ)) =
      ((maynardG b 2 k : ℕ) : ℝ) := by
    rw [← key_nat k b]; push_cast; rfl
  rw [← hcast, Finset.mul_sum, Finset.sum_div]
  exact Finset.sum_congr rfl (fun v _ ↦ by ring)

end IntegrationFormula

namespace PrimeGaps

/-- The factorial formula `IsFactorialMoment` for integration over the L² simplex `𝓡 k`. -/
@[pg_tag "bg246" "lem_integration_formula"]
theorem lem_integration_formula (k : ℕ) : IsFactorialMoment (fun f ↦ ∫ t in 𝓡 k, f t) maynardG :=
  fun a b ↦ IntegrationFormula.lem_integration_formula_real k a b

end PrimeGaps

end

section

namespace PrimeGaps

/-- For `k ≥ 2` and nonnegative integers
`a, c`, `∫_{𝓡_{k-1}} (1 − ∑ tᵢ)^a · (∑ tᵢ²)^c dt = a! / (k+a+2c−1)! · G_{c,2}(k − 1)`,
where the integral is over `𝓡_{k-1} ⊆ EuclideanSpace ℝ (Fin (k-1))`. -/
@[pg_tag "bg246" "lem_integration_prime"]
theorem lem_integration_prime (k : ℕ) (hk : 2 ≤ k) (a c : ℕ) :
    (∫ t in 𝓡 (k - 1), (1 - ∑ i, t i) ^ a * (∑ i, (t i) ^ 2) ^ c) =
      (a ! : ℝ) / ((k + a + 2 * c - 1)! : ℝ) * (maynardG c 2 (k - 1) : ℝ) := by
  rw [IntegrationFormula.lem_integration_formula_real (k - 1) a c,
    show (k - 1) + a + 2 * c = k + a + 2 * c - 1 by omega]
  ring

/-- The integral of the square of a finite combination of continuous functions over a compact set
is the double sum of the pairwise integrals. -/
theorem setIntegral_sq_sum {k : ℕ} {ι : Type*} [Fintype ι]
    {s : Set (EuclideanSpace ℝ (Fin k))} (hs : IsCompact s) (c : ι → ℝ)
    (f : ι → EuclideanSpace ℝ (Fin k) → ℝ) (hf : ∀ i, Continuous (f i)) :
    (∫ x in s, (∑ i, c i * f i x) ^ 2) =
      ∑ i, ∑ j, c i * c j * ∫ x in s, f i x * f j x := by
  have hint : ∀ i j, MeasureTheory.IntegrableOn
      (fun x ↦ (c i * f i x) * (c j * f j x)) s := fun i j ↦
    ((continuous_const.mul (hf i)).mul
      (continuous_const.mul (hf j))).continuousOn.integrableOn_compact hs
  rw [show (fun x : EuclideanSpace ℝ (Fin k) ↦ (∑ i, c i * f i x) ^ 2) =
      fun x ↦ ∑ i, ∑ j, (c i * f i x) * (c j * f j x) by
    funext x
    rw [sq, Finset.sum_mul_sum]]
  rw [MeasureTheory.integral_finsetSum _
    (fun i _ ↦ MeasureTheory.integrable_finsetSum _ fun j _ ↦ hint i j)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [MeasureTheory.integral_finsetSum _ (fun j _ ↦ hint i j)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [show (fun x : EuclideanSpace ℝ (Fin k) ↦ (c i * f i x) * (c j * f j x)) =
      fun x ↦ (c i * c j) * (f i x * f j x) by
    funext x
    ring]
  rw [MeasureTheory.integral_const_mul]

end PrimeGaps

end
