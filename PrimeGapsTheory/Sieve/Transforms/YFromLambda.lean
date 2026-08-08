/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.ArithmeticFunction.LYTransform.Specialized
public import PrimeGapsTheory.Foundations.SieveDatum
public import PrimeGapsTheory.Sieve.Transforms.YmSubstitute
public import PrimeGapsTheory.Variational.SmoothApprox

import PrimeGapsTheory.ForMathlib.NumberTheory.ArithmeticFunction.Moebius
import PrimeGapsTheory.Tactic.PaperTag

/-!
# Evaluation of transformed sieve weights

Evaluates the transform of the smooth Maynard sieve weights.

## Main results

* `lem_y_from_lambda_0`: Identifies the transform of the smooth sieve weights.
* `y_from_lambda`: Evaluates the transform under the simplex-support hypotheses.
-/

@[expose] public section

open scoped ArithmeticFunction.Moebius ENNReal

namespace PrimeGaps

/-- Each coordinate of a tuple with squarefree product is itself squarefree. -/
theorem coord_squarefree {k : ℕ} (e : Fin k → ℕ) (hsq : Squarefree (∏ i, e i))
    (i : Fin k) : Squarefree (e i) :=
  hsq.squarefree_of_dvd (Finset.dvd_prod_of_mem e (Finset.mem_univ i))

/-- Applying the `y` -from-`λ` transform `lToY` to the `F` -derived `λ` -weight `l₀` recovers the
`F` -derived `y` -weight `y₀`; this holds precisely because `y₀` is supported on squarefree
tuples. -/
@[pg_tag "bg246" "lem_y_from_lambda_0"]
theorem lem_y_from_lambda_0 {k W : ℕ} {R : ℝ} (F : EuclideanSpace ℝ (Fin k) → ℝ) :
    PrimeGaps.lToY (PrimeGaps.l₀ R W F) = PrimeGaps.y₀ R W F := by
  ext r
  rw [PrimeGaps.l₀, PrimeGaps.lToY_yToL]
  split
  · rfl
  · rename_i h
    symm
    by_contra hr
    have hmem : r ∈ (PrimeGaps.y₀ R W F).support := Finsupp.mem_support_iff.mpr hr
    have hperm := PrimeGaps.hasPermissibleSupport_y₀ (k := k) (R := R) (W := W) (F := F) hmem
    rw [Finset.mem_permissibleSupport_iff] at hperm
    have hsq : Squarefree (∏ i, r i) := hperm.2.2
    exact h (coord_squarefree r hsq)

open scoped PrimeGaps

end PrimeGaps

open scoped PrimeGaps

/-- A continuous `F` supported in `𝓡 k` vanishes at the origin, since `0` lies in the closure of
`(𝓡 k)ᶜ` once `1 ≤ k`. -/
lemma F_zero_of_support_simplex {k : ℕ} (hk : 1 ≤ k) {F : EuclideanSpace ℝ (Fin k) → ℝ}
    (hF_cont : Continuous F) (hF_supp : Function.support F ⊆ 𝓡 k) :
    F 0 = 0 := by
  have hzero_in : (0 : EuclideanSpace ℝ (Fin k)) ∈ closure ((𝓡 k)ᶜ) := by
    obtain ⟨i0⟩ : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    set g : ℝ → EuclideanSpace ℝ (Fin k) :=
      fun t ↦ WithLp.toLp 2 (Function.update (fun _ ↦ (0 : ℝ)) i0 t) with hg
    have hgcont : Continuous g := by
      refine (PiLp.continuous_toLp (p := (2 : ℝ≥0∞)) (β := fun _ : Fin k ↦ ℝ)).comp ?_
      refine continuous_pi (fun i ↦ ?_)
      by_cases hi : i = i0
      · subst hi
        simp only [Function.update_self]
        exact continuous_id
      · simp only [Function.update_of_ne hi]
        exact continuous_const
    have himg : g '' (Set.Iio 0) ⊆ (𝓡 k)ᶜ := by
      rintro _ ⟨t, ht, rfl⟩
      simp only [Set.mem_compl_iff]
      intro hmem
      obtain ⟨hall, _⟩ := EuclideanSpace.mem_scaledStdSimplex_iff.mp hmem
      have hnn : (0 : ℝ) ≤ (g t) i0 := hall i0
      simp only [hg, PiLp.toLp_apply, Function.update_self] at hnn
      exact (not_le.mpr ht) hnn
    have h0mem : (0 : ℝ) ∈ closure (Set.Iio (0 : ℝ)) := by
      rw [closure_Iio]; exact Set.self_mem_Iic
    have : g 0 ∈ closure (g '' Set.Iio 0) :=
      image_closure_subset_closure_image hgcont ⟨0, h0mem, rfl⟩
    have hg0 : g 0 = (0 : EuclideanSpace ℝ (Fin k)) := by
      ext i
      by_cases hi : i = i0 <;> simp [hg, hi]
    rw [hg0] at this
    exact closure_mono himg this
  have hEq : Set.EqOn F (fun _ ↦ (0 : ℝ)) ((𝓡 k)ᶜ) := by
    intro x hx
    simp only [Set.mem_compl_iff] at hx
    by_contra hFx
    exact hx (hF_supp (by simpa [Function.mem_support] using hFx))
  simpa using (Set.EqOn.closure hEq hF_cont continuous_const) hzero_in

namespace PrimeGaps

/-- Simplex support forces the truncation `∏ᵢ rᵢ ≤ R`: if `F` is continuous, supported in `𝓡 k`,
and nonzero at `(log rᵢ / log R)ᵢ`, then the product of the coordinates is at most `R`. -/
lemma prod_le_R_of_F_ne_zero {k : ℕ} {R : ℝ} (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hk : 1 ≤ k) (hR : 0 < R)
    (hF_cont : Continuous F) (hF_supp : Function.support F ⊆ 𝓡 k)
    (r : Fin k → ℕ) (hsq : Squarefree (∏ i, r i))
    (hFr : F (WithLp.toLp 2 (fun i ↦ Real.log (r i) / Real.log R)) ≠ 0) :
    (↑(∏ i, r i) : ℝ) ≤ R := by
  have hr1 : ∀ i, 1 ≤ r i := fun i ↦ Nat.one_le_iff_ne_zero.mpr fun h0 ↦
      hsq.ne_zero (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  have hx_mem : (WithLp.toLp 2
      (fun i ↦ Real.log (r i) / Real.log R) : EuclideanSpace ℝ (Fin k)) ∈ 𝓡 k :=
    hF_supp (Function.mem_support.mpr hFr)
  obtain ⟨hnn, hsum⟩ := EuclideanSpace.mem_scaledStdSimplex_iff.mp hx_mem
  have hnn' : ∀ i, 0 ≤ Real.log (r i) / Real.log R :=
    fun i ↦ by simpa [PiLp.toLp_apply] using hnn i
  have hsum' : ∑ i, Real.log (r i) / Real.log R ≤ 1 := by
    simpa [PiLp.toLp_apply] using hsum
  by_cases hlogR : 0 < Real.log R
  · have hlogsum : ∑ i, Real.log (r i) ≤ Real.log R := by
      rwa [← Finset.sum_div, div_le_one hlogR] at hsum'
    have hne : ∀ i ∈ Finset.univ, (r i : ℝ) ≠ 0 := fun i _ ↦ by have := hr1 i; positivity
    have hprodlog : Real.log (∏ i, (r i : ℝ)) ≤ Real.log R := by
      rwa [Real.log_prod hne]
    have h1 : (0 : ℝ) < ∏ i, (r i : ℝ) := Finset.prod_pos fun i _ ↦ by have := hr1 i; positivity
    rw [Nat.cast_prod]
    have := Real.exp_le_exp.mpr hprodlog
    rwa [Real.exp_log h1, Real.exp_log hR] at this
  · exfalso
    apply hFr
    have hx0 : (WithLp.toLp 2 (fun i ↦ Real.log (r i) / Real.log R) :
          EuclideanSpace ℝ (Fin k)) = 0 := by
      ext i
      simp only [PiLp.zero_apply]
      change (WithLp.toLp 2 (fun j ↦ Real.log (r j) / Real.log R) : EuclideanSpace ℝ (Fin k)) i = 0
      rw [PiLp.toLp_apply]
      have h1 : 0 ≤ Real.log (r i) := Real.log_nonneg (by exact_mod_cast hr1 i)
      have hle0 : Real.log (r i) / Real.log R ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos h1 (not_lt.mp hlogR)
      exact le_antisymm hle0 (hnn' i)
    rw [hx0]
    exact F_zero_of_support_simplex hk hF_cont hF_supp

open Finset in
/-- Pointwise evaluation of the Maynard--Tao change of variables. For `F` continuous and supported
in the simplex `𝓡 k`, the transform `lToY` of the sieve weight `l₀ R W (F ∘ WithLp.toLp 2)` takes
the value `F (log r₁ / log R, …, log r_k / log R)` at every tuple `r` whose product is squarefree
and coprime to `W`, and `0` at every other tuple. -/
theorem lToY_l₀_apply {k W : ℕ} {R : ℝ} (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hk : 1 ≤ k) (hR : 0 < R) (hF_cont : Continuous F)
    (hF_supp : Function.support F ⊆ 𝓡 k) (r : Fin k → ℕ) :
    lToY (l₀ R W (fun x ↦ F (WithLp.toLp 2 x))) r =
      if Squarefree (∏ i, r i) ∧ (∏ i, r i).Coprime W then
        F (WithLp.toLp 2 (fun i ↦ Real.log (r i) / Real.log R))
      else 0 := by
  classical
  have hYsupp : ∀ s : Fin k → ℕ, (if Squarefree (∏ i, s i) ∧ (∏ i, s i).Coprime W then
        F (WithLp.toLp 2 (fun i ↦ Real.log (s i) / Real.log R))
        else 0) ≠ 0 →
      s ∈ permissibleSupport k ⌊R⌋₊ W := by
    intro s hs
    by_cases hc : Squarefree (∏ i, s i) ∧ (∏ i, s i).Coprime W
    · rw [if_pos hc] at hs
      rw [mem_permissibleSupport_iff]
      exact ⟨Nat.le_floor (prod_le_R_of_F_ne_zero F hk hR hF_cont hF_supp s hc.1 hs), hc.2, hc.1⟩
    · rw [if_neg hc] at hs; exact absurd rfl hs
  obtain ⟨Y, hY_perm, hYval⟩ : ∃ Y : (Fin k → ℕ) →₀ ℝ, Y.HasPermissibleSupport ⌊R⌋₊ W ∧
        ∀ s, Y s = if Squarefree (∏ i, s i) ∧ (∏ i, s i).Coprime W then
          F (WithLp.toLp 2 (fun i ↦ Real.log (s i) / Real.log R))
          else 0 :=
    ⟨Finsupp.onFinset (permissibleSupport k ⌊R⌋₊ W) _ hYsupp,
      Finsupp.support_onFinset_subset, fun _ ↦ Finsupp.onFinset_apply⟩
  have key : yToL Y = l₀ R W (fun x ↦ F (WithLp.toLp 2 x)) := by
    refine Finsupp.ext fun d ↦ ?_
    rw [yToL_apply hY_perm, l₀_apply]
    congr 1
    rw [Finsupp.sum_of_support_subset Y hY_perm _ (fun s _ ↦ by simp), Finset.sum_filter]
    refine Finset.sum_congr rfl fun s hs ↦ ?_
    have hs' := mem_permissibleSupport_iff.mp hs
    have hYs : Y s = F (WithLp.toLp 2 (fun i ↦ Real.log (s i) / Real.log R)) := by
      rw [hYval s, if_pos ⟨hs'.2.2, hs'.2.1⟩]
    by_cases hds : ∀ i, d i ∣ s i
    · rw [if_pos hds, if_pos hds, hYs]
      ring
    · rw [if_neg hds, if_neg hds]
  rw [← key, lToY_yToL]
  by_cases hsf : ∀ i, Squarefree (r i)
  · rw [if_pos hsf]; exact hYval r
  · rw [if_neg hsf]
    exact (if_neg fun h ↦ hsf (coord_squarefree r h.1)).symm

open Finset in
/-- Recovery direction of the Maynard--Tao change of variables. Fix an integer `k ≥ 2` and a
truncation parameter `R > 0`. For `F: EuclideanSpace ℝ (Fin k) → ℝ` smooth and supported on the
change of variables `y` applied to the sieve weight
`l₀ = PrimeGaps.l₀ R W (F ∘ WithLp.toLp 2)` returns the values of `F` sampled at the
lattice points `WithLp.toLp 2 (log r_1 / log R,..., log r_k / log R)` on the squarefree
tuples coprime to `W`, and `0` elsewhere. -/
@[pg_tag "bg246" "lem_smooth_y"]
theorem y_from_lambda
    {k W : ℕ} {R : ℝ} (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hk : 2 ≤ k) (hR : 0 < R)
    (hF_smooth : ContDiff ℝ (⊤ : ℕ∞) F)
    (hF_supp : Function.support F ⊆ 𝓡 k)
    (r : Fin k → ℕ) :
    lToY (l₀ R W (fun x ↦ F (WithLp.toLp 2 x))) r =
      if Squarefree (∏ i, r i) ∧ (∏ i, r i).Coprime W then
        F (WithLp.toLp 2 (fun i ↦ Real.log (r i) / Real.log R))
      else 0 :=
  lToY_l₀_apply F (by omega) hR hF_smooth.continuous hF_supp r

end PrimeGaps

namespace PrimeGaps


/-- `∑_{d ∣ e, r ∣ d} μ(d) = if e = r then μ(r) else 0`, for squarefree `e` and `r ∣ e`. -/
theorem moebius_chain_sum {r e : ℕ} (he : Squarefree e) (hre : r ∣ e) :
    (∑ d ∈ e.divisors.filter (fun d ↦ r ∣ d), μ d) = if e = r then μ r else 0 := by
  have he0 : e ≠ 0 := he.ne_zero
  have hr0 : r ≠ 0 := fun h ↦ by simp only [h, zero_dvd_iff] at hre; exact he0 (by simpa using hre)
  obtain ⟨m, rfl⟩ := hre
  have hcop : r.Coprime m := Nat.coprime_of_squarefree_mul he
  have hm0 : m ≠ 0 := by rintro rfl; simp at hr0 ⊢; omega
  have key : {d ∈ (r * m).divisors | r ∣ d} = m.divisors.image (fun c ↦ r * c) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]
    constructor
    · rintro ⟨⟨hd, _⟩, c, rfl⟩
      exact ⟨c, ⟨(mul_dvd_mul_iff_left hr0).mp hd, hm0⟩, rfl⟩
    · rintro ⟨c, ⟨hc, _⟩, rfl⟩
      exact ⟨⟨mul_dvd_mul_left r hc, by positivity⟩, Dvd.intro c rfl⟩
  rw [key, Finset.sum_image (by
    intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hr0) hab)]
  have : ∀ c ∈ m.divisors, μ (r * c) = μ r * μ c := by
    intro c hc
    exact ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (hcop.coprime_dvd_right (Nat.mem_divisors.mp hc).1)
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum,
    ArithmeticFunction.sum_divisors_moebius (d := m)]
  have hiff : (r * m = r) ↔ (m = 1) := by
    constructor
    · intro h
      have : r * m = r * 1 := by rwa [mul_one]
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hr0) this
    · intro h; rw [h, mul_one]
  simp only [hiff]
  split_ifs <;> ring

/-- `moebius_chain_sum` over the range `[0, B]`:
`∑_{x ≤ B, r ∣ x ∣ e} μ(x) = if e = r then μ(r) else 0`. -/
theorem coord_sum (B : ℕ) (r e : ℕ) (hre : r ∣ e) (he : Squarefree e) (hB : e ≤ B) :
    (∑ x ∈ Finset.range (B + 1), (if r ∣ x ∧ x ∣ e then (μ x : ℝ) else 0)) =
      if e = r then (μ r : ℝ) else 0 := by
  have he0 : e ≠ 0 := he.ne_zero
  rw [← Finset.sum_filter]
  have hset : {x ∈ Finset.range (B + 1) | r ∣ x ∧ x ∣ e} =
      e.divisors.filter (fun d ↦ r ∣ d) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors]
    constructor
    · rintro ⟨_, hrx, hxe⟩
      exact ⟨⟨hxe, he0⟩, hrx⟩
    · rintro ⟨⟨hxe, _⟩, hrx⟩
      refine ⟨?_, hrx, hxe⟩
      have : x ≤ e := Nat.le_of_dvd (Nat.pos_of_ne_zero he0) hxe
      omega
  rw [hset, ← Int.cast_sum, moebius_chain_sum he hre]
  split_ifs <;> simp

/-- Tuple form of `coord_sum`: `∑_{d, rᵢ ∣ dᵢ ∣ eᵢ} ∏ᵢ μ(dᵢ) = if e = r then ∏ᵢ μ(rᵢ) else 0`. -/
theorem dsum_moebius_collapse {k : ℕ} (B : ℕ) (r e : Fin k → ℕ)
    (hre : ∀ i, r i ∣ e i) (hsq : Squarefree (∏ i, e i))
    (hB : ∀ i, e i ≤ B) :
    (∑ d ∈ Fintype.piFinset (fun _ : Fin k ↦ Finset.range (B + 1)),
        (if (∀ i, r i ∣ d i) ∧ (∀ i, d i ∣ e i) then (∏ i, (μ (d i) : ℝ)) else 0)) =
      if e = r then (∏ i, (μ (r i) : ℝ)) else 0 := by
  have hrw : ∀ d : Fin k → ℕ, (if (∀ i, r i ∣ d i) ∧ (∀ i, d i ∣ e i) then
        (∏ i, (μ (d i) : ℝ)) else 0) =
      ∏ i, (if r i ∣ d i ∧ d i ∣ e i then (μ (d i) : ℝ) else 0) := by
    intro d
    by_cases hcond : (∀ i, r i ∣ d i) ∧ (∀ i, d i ∣ e i)
    · rw [if_pos hcond]
      exact Finset.prod_congr rfl (fun i _ ↦ (if_pos ⟨hcond.1 i, hcond.2 i⟩).symm)
    · rw [if_neg hcond]
      symm
      by_cases hA : ∀ i, r i ∣ d i
      · have hB' : ¬ ∀ i, d i ∣ e i := fun h ↦ hcond ⟨hA, h⟩
        push Not at hB'
        obtain ⟨i0, hi0⟩ := hB'
        exact Finset.prod_eq_zero (Finset.mem_univ i0) (if_neg (fun h ↦ hi0 h.2))
      · push Not at hA
        obtain ⟨i0, hi0⟩ := hA
        exact Finset.prod_eq_zero (Finset.mem_univ i0) (if_neg (fun h ↦ hi0 h.1))
  rw [Finset.sum_congr rfl (fun d _ ↦ hrw d)]
  rw [Finset.sum_prod_piFinset (Finset.range (B + 1))
      (fun i x ↦ if r i ∣ x ∧ x ∣ e i then (μ x : ℝ) else 0)]
  have hcoord : ∀ i, (∑ x ∈ Finset.range (B + 1),
      (if r i ∣ x ∧ x ∣ e i then (μ x : ℝ) else 0)) =
      if e i = r i then (μ (r i) : ℝ) else 0 := by
    intro i
    exact coord_sum B (r i) (e i) (hre i) (coord_squarefree e hsq i) (hB i)
  rw [Finset.prod_congr rfl (fun i _ ↦ hcoord i)]
  by_cases hER : e = r
  · rw [if_pos hER]
    exact Finset.prod_congr rfl (fun i _ ↦ by rw [if_pos (by rw [hER])])
  · rw [if_neg hER]
    have hex : ∃ i, e i ≠ r i := by
      by_contra h
      push Not at h
      exact hER (funext h)
    obtain ⟨i0, hi0⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ i0) (if_neg hi0)
end PrimeGaps

namespace PrimeGaps

/-- Maynard `λ ↔ y` inversion (`lem_lambda_from_y`). For a smooth cutoff `F` supported on the
simplex `R_k` (it vanishes unless every coordinate lies in `[0,1]` and the coordinates sum to
at most `1` ), with `λ = l₀ R W F` (Definition 1) and `y = y λ` (Definition 2), the
change-of-variable weight `y r` equals `μ(∏ r_i)^2 · 𝟙[(∏ r_i, W) = 1] · F(log r_i / log R)`;
i.e. it recovers `F` at the sampled point `(log r_i / log R)_i` exactly when `∏ r_i` is
squarefree and coprime to `W`, and vanishes otherwise. Hypotheses: * `hFsmooth` records the
smoothness (`C^∞`) regularity of `F` assumed in the problem. * `hFsupp` records that `F` is
supported on the simplex `R_k ⊆ [0,1]^k`. * `hR: 1 < R` records that in the
intended large-`N` regime the truncation level `R > 1`, so `log R > 0` (in particular
`log R ≠ 0`, making the sampling points `log r_i / log R` well-behaved). -/
@[pg_tag "bg246" "rmk_smooth_y"]
theorem rmk_smooth_y
    {k : ℕ}
    (R : ℝ) (W : ℕ) (hR : 1 < R)
    (F : (Fin k → ℝ) → ℝ)
    (hFsupp : ∀ x : Fin k → ℝ, ¬ ((∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ ∑ i, x i ≤ 1) → F x = 0)
    (r : Fin k → ℕ) (hr : ∀ i, 1 ≤ r i) :
    lToY (l₀ R W (fun x ↦ F (WithLp.ofLp x))) r = (μ (∏ i, r i) ^ 2 : ℝ) *
      (if (∏ i, r i).Coprime W then (1 : ℝ) else 0) *
        F (fun i ↦ Real.log (r i) / Real.log R) := by
  classical
  set Rt := R with hRdef
  have hlogR : 0 < Real.log Rt := Real.log_pos hR
  have hR0 : 0 < Rt := lt_trans one_pos hR
  set B := ⌊Rt⌋₊ with hBdef
  set PS := Finset.permissibleSupport k ⌊R⌋₊ W with hPSdef
  set Box : Finset (Fin k → ℕ) := Fintype.piFinset (fun _ ↦ Finset.range (B + 1)) with hBox
  set S : (Fin k → ℕ) → ℝ :=
    fun e ↦ 1 / (∏ i, (e i).totient) * F (fun i ↦ Real.log (e i) / Real.log Rt) with hSdef
  have hmemBox : ∀ e : Fin k → ℕ, e ∈ Box ↔ ∀ i, e i ≤ B := fun e ↦ by
    simp only [hBox, Fintype.mem_piFinset, Finset.mem_range]
    exact forall_congr' fun i ↦ Nat.lt_succ_iff
  have hPSBox : ∀ d, d ∈ PS → d ∈ Box := by
    intro d hd
    rw [hmemBox]
    rw [hPSdef, Finset.mem_permissibleSupport_iff] at hd
    obtain ⟨hprodR, _, hsq⟩ := hd
    intro i
    have hle : d i ≤ ∏ j, d j := Nat.le_of_dvd (Nat.pos_of_ne_zero hsq.ne_zero)
      (Finset.dvd_prod_of_mem d (Finset.mem_univ i))
    have hB : (∏ j, d j) ≤ B := by rw [hBdef, hRdef]; exact hprodR
    omega
  rw [lToY_apply hasPermissibleSupport_l₀]
  rw [Finsupp.sum_of_support_subset (l₀ R W (fun x ↦ F (WithLp.ofLp x))) hasPermissibleSupport_l₀
        (fun d ld ↦ if ∀ i, r i ∣ d i then ld / ∏ i, d i else 0)
        (fun d _ ↦ by simp)]
  have hpref : ∀ d : Fin k → ℕ, (∀ i, 1 ≤ d i) →
      (↑(∏ i, μ (d i) * (d i : ℤ)) : ℝ) / (↑(∏ i, d i) : ℝ) = ∏ i, (μ (d i) : ℝ) := by
    intro d hd
    have hne : (↑(∏ i, d i) : ℝ) ≠ 0 := by
      have : (0 : ℝ) < ∏ i, d i := by
        rw [Nat.cast_prod]
        apply Finset.prod_pos
        intro i _
        exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (hd i)
      exact ne_of_gt this
    rw [div_eq_iff hne]
    push_cast
    rw [← Finset.prod_mul_distrib]
  have hexpand : ∀ d ∈ PS,
      (if ∀ i, r i ∣ d i then (l₀ R W (fun x ↦ F (WithLp.ofLp x)) d) / ∏ i, d i else 0) =
      (if ∀ i, r i ∣ d i then
          (∏ i, (μ (d i) : ℝ)) * (∑ e ∈ PS with ∀ i, d i ∣ e i, S e) else 0) := by
    intro d hd
    have hne0 : ∀ i, 1 ≤ d i := by
      rw [hPSdef, Finset.mem_permissibleSupport_iff] at hd
      intro i
      have := hd.2.2.ne_zero
      have hdi : d i ≠ 0 := fun h ↦ this (Finset.prod_eq_zero (Finset.mem_univ i) h)
      omega
    split_ifs with hc
    · rw [l₀_apply, mul_div_right_comm, hpref d hne0]
    · rfl
  rw [Finset.sum_congr rfl hexpand]
  have hd2e : ∀ d ∈ PS, (if ∀ i, r i ∣ d i then
        (∏ i, (μ (d i) : ℝ)) * (∑ e ∈ PS with ∀ i, d i ∣ e i, S e) else 0) =
      ∑ e ∈ PS, (if (∀ i, r i ∣ d i) ∧ (∀ i, d i ∣ e i) then
          (∏ i, (μ (d i) : ℝ)) * S e else 0) := by
    intro d _
    rw [Finset.sum_filter]
    split_ifs with hc
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      by_cases hde : ∀ i, d i ∣ e i
      · rw [if_pos hde, if_pos ⟨hc, hde⟩]
      · rw [if_neg hde, if_neg (fun h ↦ hde h.2), mul_zero]
    · symm
      apply Finset.sum_eq_zero
      intro e _
      rw [if_neg (fun h ↦ hc h.1)]
  rw [Finset.sum_congr rfl hd2e, Finset.sum_comm]
  have hinner_e : ∀ e ∈ PS, (∑ d ∈ PS, (if (∀ i, r i ∣ d i) ∧ (∀ i, d i ∣ e i) then
        (∏ i, (μ (d i) : ℝ)) * S e else 0)) =
      S e * (if e = r then (∏ i, (μ (r i) : ℝ)) else 0) := by
    intro e he
    have hfac : (∑ d ∈ PS, (if (∀ i, r i ∣ d i) ∧ (∀ i, d i ∣ e i) then
          (∏ i, (μ (d i) : ℝ)) * S e else 0)) =
        S e * (∑ d ∈ PS, (if (∀ i, r i ∣ d i) ∧ (∀ i, d i ∣ e i) then
          (∏ i, (μ (d i) : ℝ)) else 0)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      split_ifs with h
      · ring
      · rw [mul_zero]
    rw [hfac]
    congr 1
    have hconv : (∑ d ∈ PS, (if (∀ i, r i ∣ d i) ∧ (∀ i, d i ∣ e i) then
          (∏ i, (μ (d i) : ℝ)) else 0)) =
        ∑ d ∈ Box, (if (∀ i, r i ∣ d i) ∧ (∀ i, d i ∣ e i) then
          (∏ i, (μ (d i) : ℝ)) else 0) := by
      apply Finset.sum_subset (fun d hd ↦ hPSBox d hd)
      intro d _ hdPS
      rw [if_neg]
      rintro ⟨_, hde⟩
      exact hdPS (Finset.mem_permissibleSupport_of_dvd he hde)
    rw [hconv]
    by_cases hre : ∀ i, r i ∣ e i
    · have hsq : Squarefree (∏ i, e i) := by
        rw [hPSdef, Finset.mem_permissibleSupport_iff] at he; exact he.2.2
      have hB' : ∀ i, e i ≤ B := (hmemBox e).mp (hPSBox e he)
      exact PrimeGaps.dsum_moebius_collapse B r e hre hsq hB'
    · rw [if_neg (by rintro rfl; exact hre (fun i ↦ dvd_refl _))]
      apply Finset.sum_eq_zero
      intro d _
      rw [if_neg]
      rintro ⟨hrd, hde⟩
      exact hre (fun i ↦ (hrd i).trans (hde i))
  rw [Finset.sum_congr rfl hinner_e]
  by_cases hrPS : r ∈ PS
  · rw [Finset.sum_eq_single_of_mem r hrPS (fun e _ her ↦ by rw [if_neg her, mul_zero]), if_pos rfl]
    have hmem := hrPS
    rw [hPSdef, Finset.mem_permissibleSupport_iff] at hmem
    obtain ⟨_, hcop, hsqr⟩ := hmem
    rw [if_pos hcop]
    have hMsq : (∏ i, (μ (r i) : ℝ)) ^ 2 = 1 := by
      rw [← Finset.prod_pow, Finset.prod_eq_one]
      intro i _
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
        (PrimeGaps.coord_squarefree r hsqr i)
    have hMUsq : (μ (∏ i, r i) : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsqr
    have hphi_ne : (↑(∏ i, (r i).totient) : ℝ) ≠ 0 := by
      rw [Nat.cast_prod]
      apply ne_of_gt
      apply Finset.prod_pos
      intro i _
      exact_mod_cast Nat.totient_pos.mpr (by have := hr i; omega)
    rw [hMUsq]
    simp only [hSdef]
    set M : ℝ := ∏ i, (μ (r i) : ℝ) with hM
    set P : ℝ := (↑(∏ i, (r i).totient) : ℝ) with hP
    set Fv : ℝ := F (fun i ↦ Real.log (r i) / Real.log Rt) with hFv
    have hCsplit :
        (↑(∏ i, μ (r i) * ((r i).totient : ℤ)) : ℝ) = M * P := by
      rw [hM, hP, Nat.cast_prod, ← Finset.prod_mul_distrib]
      push_cast
      rfl
    rw [hCsplit]
    have hrw : M * P * (1 / P * Fv * M) = M ^ 2 * (P * (1 / P)) * Fv := by ring
    rw [hrw, mul_one_div_cancel hphi_ne, mul_one, hMsq, one_mul, one_mul, one_mul]
  · rw [Finset.sum_eq_zero (fun e he ↦ by
          rw [if_neg (by rintro rfl; exact hrPS he), mul_zero]), mul_zero]
    symm
    by_cases hcop : (∏ i, r i).Coprime W
    · rw [if_pos hcop]
      by_cases hsqr : Squarefree (∏ i, r i)
      · have hFr0 : F (fun i ↦ Real.log (r i) / Real.log Rt) = 0 := by
          apply hFsupp
          rintro ⟨_, hsum⟩
          apply hrPS
          rw [hPSdef, Finset.mem_permissibleSupport_iff]
          refine ⟨?_, hcop, hsqr⟩
          have hlogsum : ∑ i, Real.log (r i) ≤ Real.log Rt := by
            rwa [← Finset.sum_div, div_le_one hlogR] at hsum
          have hne : ∀ i ∈ Finset.univ, (r i : ℝ) ≠ 0 := by
            intro i _; have := hr i; positivity
          have hprodlog : Real.log (∏ i, (r i : ℝ)) ≤ Real.log Rt := by
            rwa [Real.log_prod hne]
          have h1 : (0 : ℝ) < ∏ i, (r i : ℝ) := by
            apply Finset.prod_pos; intro i _; have := hr i; positivity
          have := Real.exp_le_exp.mpr hprodlog
          rw [Real.exp_log h1, Real.exp_log hR0] at this
          rw [← hRdef]
          apply Nat.le_floor
          rw [Nat.cast_prod]
          exact this
        rw [hFr0, mul_zero]
      · have : (μ (∏ i, r i) : ℝ) ^ 2 = 0 := by
          rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsqr]; simp
        rw [this, zero_mul, zero_mul]
    · rw [if_neg hcop, mul_zero, zero_mul]

end PrimeGaps
