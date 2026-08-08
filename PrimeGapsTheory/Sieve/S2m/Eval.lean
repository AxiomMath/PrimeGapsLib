/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.Common.S2mEvalAssembly

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Evaluation of the decoupled second-moment sum

Evaluates the decoupled sum in terms of the Maynard marginal quadratic form.

## Main results

* `lem_S2m_eval`: Approximates the decoupled sum by its integral main term with a quantitative
  error.
* `cross_error`: Bounds the cost of replacing the discrete weights by the marginal integral.
* `sieveE_split_bound`: Splits the sieve error into a singular-series and a partial-summation
  contribution.
-/

@[expose] public section

open Real

open scoped ArithmeticFunction.Moebius
open scoped Finset

open scoped ArithmeticFunction.detotient

namespace PrimeGaps

open MeasureTheory EuclideanSpace

open scoped PrimeGaps.sieveTruncation in
/-- For every `M`, eventually `M * (D₀ N * log (D₀ N)) ≤ log R`. -/
theorem D0_logD0_scaled (δ θ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2)) (M : ℝ) :
    ∃ x₀ : ℝ, ∀ N : ℕ, x₀ ≤ (N : ℝ) → M * (PrimeGaps.D₀ (N : ℝ) * Real.log (PrimeGaps.D₀ (N : ℝ))) ≤
        Real.log R := by
  set κ : ℝ := θ / 2 - δ with hκ
  have hκpos : 0 < κ := sub_pos.mpr hδ.2
  set M' : ℝ := max M 1
  have hM'pos : 0 < M' := one_pos.trans_le (le_max_right _ _)
  have hcore : ∀ᶠ x : ℝ in Filter.atTop, M' * (Real.log x) ^ 2 ≤ κ * x := by
    filter_upwards [Real.eventually_log_pow_le_const_mul 2
      (show (0 : ℝ) < κ / M' by positivity)] with x hle
    exact (mul_le_mul_of_nonneg_left hle hM'pos.le).trans_eq (by field_simp)
  obtain ⟨x1, hx1⟩ := Filter.eventually_atTop.mp <|
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually hcore
  refine ⟨max (x1 : ℝ) (rexp (rexp (rexp 2))), fun N hN ↦ ?_⟩
  have hNe : rexp (rexp (rexp 2)) ≤ (N : ℝ) := (le_max_right _ _).trans hN
  have hNpos : (0 : ℝ) < (N : ℝ) := (Real.exp_pos _).trans_le hNe
  set D₀ : ℝ := PrimeGaps.D₀ (N : ℝ)
  set LL : ℝ := Real.log (Real.log (N : ℝ))
  have hlogN_ge : rexp (rexp 2) ≤ Real.log (N : ℝ) := (Real.le_log_iff_exp_le hNpos).mpr hNe
  have hLL_ge : rexp 2 ≤ LL :=
    (Real.le_log_iff_exp_le ((Real.exp_pos _).trans_le hlogN_ge)).mpr hlogN_ge
  have hLLpos : (0 : ℝ) < LL := (Real.exp_pos 2).trans_le hLL_ge
  have hD₀_ge2 : (2 : ℝ) ≤ D₀ := MaynardOffDiagonal.two_le_D0_of_large hNe
  have hD₀pos : (0 : ℝ) < D₀ := two_pos.trans_le hD₀_ge2
  have hlogD₀nn : 0 ≤ Real.log D₀ := Real.log_nonneg (one_le_two.trans hD₀_ge2)
  have hD₀_le_LL : D₀ ≤ LL := Real.log_le_self hLLpos.le
  have hlogD₀_le : Real.log D₀ ≤ LL := (Real.log_le_self hD₀pos.le).trans hD₀_le_LL
  calc M * (D₀ * Real.log D₀)
      ≤ M' * (D₀ * Real.log D₀) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hD₀pos.le hlogD₀nn)
    _ ≤ M' * (LL * LL) := by gcongr
    _ = M' * LL ^ 2 := by ring
    _ ≤ κ * Real.log (N : ℝ) := hx1 N (by exact_mod_cast (le_max_left _ _).trans hN)
    _ = Real.log R := by rw [PrimeGaps.sieveTruncation, ← hκ, Real.log_rpow hNpos]

/-- `D₀ N = log log log N` tends to infinity: for every `c`, eventually `c ≤ D₀ N`. -/
theorem le_D0_of_large (c : ℝ) : ∃ x₀ : ℝ, ∀ N : ℕ, x₀ ≤ (N : ℝ) → c ≤ PrimeGaps.D₀ (N : ℝ) := by
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp <| (Real.tendsto_log_atTop.comp <|
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop c
  exact ⟨x₀, fun N hN ↦ hx₀ N hN⟩

open scoped PrimeGaps.sieveModulus in
private lemma W_ratio_pos (N : ℕ) : 0 < ((W N).totient : ℝ) / (W N : ℝ) :=
  div_pos (mod_cast Nat.totient_pos.mpr (PrimeGaps.W_pos (N := N)))
    (mod_cast PrimeGaps.W_pos (N := N))

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- `∑_{r < R, r squarefree, (r, W) = 1} 1/g r ≤ 2 · (φ(W)/W) · log R` for large `N`. -/
theorem Sg_tsum_le (δ θ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2)) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N → ∀ (_ : 0 < N) (_ : 2 ≤ PrimeGaps.D₀ (N : ℝ)),
      (∑' r : ℕ, if (r.Coprime (W N) ∧ Squarefree r ∧ (r : ℝ) < R) then
          (1 : ℝ) / (g r : ℝ) else 0) ≤ 2 * (((W N).totient : ℝ) / (W N : ℝ)) *
            Real.log R := by
  obtain ⟨Cg, hCg0, Ng, hg⟩ := lem_S2m_g_coord δ θ hδ
  obtain ⟨x2, h2R⟩ := two_le_R δ θ hδ
  obtain ⟨xs, hscaled⟩ := D0_logD0_scaled δ θ hδ (2 * Cg)
  obtain ⟨xD, hxDge⟩ := le_D0_of_large (2 * Cg)
  refine ⟨max Ng (max x2 (max xs xD)), fun N hN₀ hN hD ↦ ?_⟩
  simp only [max_le_iff] at hN₀
  obtain ⟨hNg, hx2, hxs, hxD⟩ := hN₀
  have hlogRpos : 0 < Real.log R := Real.log_pos (one_lt_two.trans_le (h2R N hx2))
  have hratiopos : 0 < ((W N).totient : ℝ) / (W N : ℝ) := W_ratio_pos N
  have hD₀pos : (0 : ℝ) < PrimeGaps.D₀ (N : ℝ) := two_pos.trans_le hD
  have hlogD₀nn : 0 ≤ Real.log (PrimeGaps.D₀ (N : ℝ)) := Real.log_nonneg (one_le_two.trans hD)
  have hbridge : (∑' r : ℕ, if (r.Coprime (W N) ∧ Squarefree r ∧ (r : ℝ) < R) then
      (1 : ℝ) / (g r : ℝ) else 0) = ∑ r ∈ (Finset.range ⌈R⌉₊).filter
        (fun r : ℕ ↦ 0 < r ∧ (r : ℝ) < R ∧ Nat.Coprime r (W N)),
      (μ r : ℝ) ^ 2 / (g r : ℝ) := by
    refine (tsum_eq_sum fun r hr ↦ if_neg fun hc ↦ hr ?_).trans
      (Finset.sum_congr rfl fun r hr ↦ ?_)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_ceil.mpr hc.2.2),
        Nat.pos_of_ne_zero fun h ↦ not_squarefree_zero (h ▸ hc.2.1), hc.2.2, hc.1⟩
    · rw [Finset.mem_filter] at hr
      by_cases hsfr : Squarefree r
      · have hmu : (μ r : ℝ) ^ 2 = 1 :=
          mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsfr
        rw [if_pos ⟨hr.2.2.2, hsfr, hr.2.2.1⟩, hmu]
      · rw [if_neg fun h ↦ hsfr h.2.1]
        simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsfr]
  have hGmax1 : Gmax (fun _ : ℝ ↦ (1 : ℝ)) ≤ 1 := ciSup_le fun t ↦ by simp
  have hg' := hg N hNg hN hD (fun _ : ℝ ↦ (1 : ℝ)) contDiff_const
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero, abs_one,
    ← hbridge] at hg'
  have hCgD₀ : Cg * (Real.log R / PrimeGaps.D₀ (N : ℝ)) ≤ Real.log R / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ hD₀pos two_pos]
    linarith [mul_le_mul_of_nonneg_right (hxDge N hxD) hlogRpos.le]
  have hCglogD₀ : Cg * Real.log (PrimeGaps.D₀ (N : ℝ)) ≤ Real.log R / 2 := by
    linarith [hscaled N hxs, mul_le_mul_of_nonneg_left
      (le_mul_of_one_le_left hlogD₀nn (one_le_two.trans hD)) hCg0.le]
  linarith [(abs_le.mp hg').2,
    mul_le_mul_of_nonneg_left hGmax1 (mul_nonneg (mul_nonneg hCg0.le hratiopos.le) hlogD₀nn),
    mul_le_mul_of_nonneg_left hCgD₀ hratiopos.le,
    mul_le_mul_of_nonneg_left hCglogD₀ hratiopos.le]

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- The `n`-fold box sum `∑_σ ∏_j 1/g (σ j) ≤ (2 · (φ(W)/W) · log R) ^ n`, by `Sg_tsum_le`. -/
theorem boxmass_le {n : ℕ} (δ θ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2)) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N → ∀ (_ : 0 < N) (_ : 2 ≤ PrimeGaps.D₀ (N : ℝ)),
      (∑' σ : Fin n → ℕ, if (∀ j, (σ j).Coprime (W N) ∧ Squarefree (σ j) ∧ (σ j : ℝ) < R) then
          ∏ j, (1 : ℝ) / (g (σ j) : ℝ) else 0) ≤
        (2 * (((W N).totient : ℝ) / (W N : ℝ)) *
              Real.log R) ^ n := by
  obtain ⟨N₀, hSg⟩ := Sg_tsum_le δ θ hδ
  refine ⟨N₀, fun N hN₀ hN hD ↦ ?_⟩
  have hprodeq : ∀ σ : Fin n → ℕ,
      (if (∀ j, (σ j).Coprime (W N) ∧ Squarefree (σ j) ∧ (σ j : ℝ) < R) then
          ∏ j, (1 : ℝ) / (g (σ j) : ℝ) else 0) =
        ∏ j, if (σ j).Coprime (W N) ∧ Squarefree (σ j) ∧ (σ j : ℝ) < R then
          (1 : ℝ) / (g (σ j) : ℝ) else 0 := fun σ ↦ by simp [Fintype.prod_ite_zero]
  rw [tsum_congr hprodeq, SijD0.tsum_prod_of_box ⌈R⌉₊
    (fun _ r ↦ if r.Coprime (W N) ∧ Squarefree r ∧ (r : ℝ) < R then (1 : ℝ) / (g r : ℝ) else 0)
    fun _ r hr ↦ (Nat.lt_ceil.mpr (ite_ne_right_iff.mp hr).1.2.2).le]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    pow_le_pow_left₀ (tsum_nonneg fun r ↦ by positivity) (hSg N hN₀ hN hD) n

private lemma abs_sq_sub_mul_sq_le {a b c e f : ℝ} (hc : 0 ≤ c) (he : 0 ≤ e)
    (h₁ : |a - c * b| ≤ e) (h₂ : |b| ≤ f) :
    |a ^ 2 - c ^ 2 * b ^ 2| ≤ e * (2 * c * f + e) := by
  have h₃ : |a + c * b| ≤ 2 * c * f + e :=
    calc |a + c * b| = |a - c * b + 2 * (c * b)| := by ring_nf
      _ ≤ |a - c * b| + |2 * (c * b)| := abs_add_le _ _
      _ = |a - c * b| + 2 * (c * |b|) := by rw [abs_mul, abs_mul, abs_two, abs_of_nonneg hc]
      _ ≤ e + 2 * (c * f) := by gcongr
      _ = 2 * c * f + e := by ring
  calc |a ^ 2 - c ^ 2 * b ^ 2| = |(a - c * b) * (a + c * b)| := by ring_nf
    _ = |a - c * b| * |a + c * b| := abs_mul _ _
    _ ≤ e * (2 * c * f + e) := mul_le_mul h₁ h₃ (abs_nonneg _) he

private lemma abs_tsum_mul_sq_sub_le_boxmass {ι : Type*} {P : ι → Prop} [DecidablePred P]
    {w y t : ι → ℝ} {c E : ℝ} (s : Finset ι) (hw : ∀ i, 0 ≤ w i)
    (hy : ∀ i ∉ s, y i = 0) (ht : ∀ i ∉ s, t i = 0)
    (hpt : ∀ i, |y i ^ 2 - c ^ 2 * t i ^ 2| ≤ E) :
    |(∑' i, if P i then w i * y i ^ 2 else 0) - c ^ 2 * (∑' i, if P i then w i * t i ^ 2 else 0)| ≤
      E * ∑ i ∈ s, if P i then w i else 0 := by
  have h₁ : (∑' i, if P i then w i * y i ^ 2 else 0) =
      ∑ i ∈ s, if P i then w i * y i ^ 2 else 0 := tsum_eq_sum fun i hi ↦ by simp [hy i hi]
  have h₂ : (∑' i, if P i then w i * t i ^ 2 else 0) =
      ∑ i ∈ s, if P i then w i * t i ^ 2 else 0 := tsum_eq_sum fun i hi ↦ by simp [ht i hi]
  rw [h₁, h₂, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  split_ifs with h
  · rw [mul_left_comm, ← mul_sub, abs_mul, abs_of_nonneg (hw i)]
    exact (mul_le_mul_of_nonneg_left (hpt i) (hw i)).trans_eq (mul_comm _ _)
  · simp

private lemma Ydisc_Tm_vanish_of_notMem_box {n : ℕ} {z : ℝ} (W : ℕ) (m : Fin (n + 1))
    (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hsupp : Function.support F ⊆ 𝓡 (n + 1)) (hz : 1 < z) {σ : Fin n → ℕ}
    (hσ : σ ∉ Fintype.piFinset fun _ : Fin n ↦ Finset.range ⌈z⌉₊) :
    Ydisc z W F m (Fin.insertNth m 1 σ) = 0 ∧ Tm m F (sigmaPt z σ) = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, ⌈z⌉₊ ≤ σ j := by
    simpa [Fintype.mem_piFinset, not_lt] using hσ
  refine ⟨Ydisc_vanish_coord z W m F hF hsupp hz σ hj,
    Tm_vanish_coord m F hF hsupp (sigmaPt z σ) (j := j) ?_⟩
  rw [sigmaPt]
  change (1 : ℝ) ≤ Real.log (σ j) / Real.log z
  rw [le_div_iff₀ (Real.log_pos hz), one_mul]
  exact Real.log_le_log (zero_lt_one.trans hz) ((Nat.le_ceil z).trans (mod_cast hj))

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- Cost of replacing the discrete `Ydisc` by `(φ(W)/W · log R) · Tm m F` in the box sum, bounded
by `C · (φ(W)/W)^(n+2) · (log R)^(n+1) · log (D₀ N) · (Fmax F)²`. -/
theorem cross_error {n : ℕ} (δ θ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N → ∀ (_ : 0 < N) (_ : 2 ≤ PrimeGaps.D₀ (N : ℝ)),
      ∀ (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ), ContDiff ℝ (⊤ : ℕ∞) F →
        Function.support F ⊆ 𝓡 (n + 1) → ∀ (m : Fin (n + 1)),
      |(∑' σ : Fin n → ℕ, if (∀ j, (σ j).Coprime (W N) ∧ Squarefree (σ j)) then
            (∏ j, (1 : ℝ) / (g (σ j) : ℝ)) * (Ydisc R (W N) F m
                (Fin.insertNth m 1 σ)) ^ 2 else 0) -
          (((W N).totient : ℝ) / (W N : ℝ) * Real.log R) ^ 2 *
            (∑' σ : Fin n → ℕ, if (∀ j, (σ j).Coprime (W N) ∧ Squarefree (σ j)) then
                (∏ j, (1 : ℝ) / (g (σ j) : ℝ)) * (Tm m F (sigmaPt R σ)) ^ 2 else 0)| ≤
        C * (((W N).totient : ℝ) / (W N : ℝ)) ^ (n + 2) * (Real.log R) ^ (n + 1) *
            Real.log (PrimeGaps.D₀ (N : ℝ)) * (MaynardSmoothY.Fmax F) ^ 2 := by
  classical
  obtain ⟨Cyd, hCyd0, Nyd, hyd⟩ := Ydisc_approx (n := n) δ θ hδ
  obtain ⟨Nbox, hbox⟩ := boxmass_le (n := n) δ θ hδ
  obtain ⟨x2, h2R⟩ := two_le_R δ θ hδ
  obtain ⟨xLD, hLDscaled⟩ := D0_logD0_scaled δ θ hδ 1
  refine ⟨2 ^ n * (2 * Cyd + Cyd ^ 2), by positivity,
      max Nyd (max Nbox (max x2 xLD)), fun N hN₀ hN hD F hF hsupp m ↦ ?_⟩
  simp only [max_le_iff] at hN₀
  obtain ⟨hNyd, hNbox, hx2, hxLD⟩ := hN₀
  have hyd' := hyd N hNyd hN hD F hF hsupp m
  have hboxN := hbox N hNbox hN hD
  have hTm := Tm_abs_le_Fmax m F hF hsupp
  have hR1 : (1 : ℝ) < R := one_lt_two.trans_le (h2R N hx2)
  have hlogRpos : 0 < Real.log R := Real.log_pos hR1
  have hratiopos : 0 < ((W N).totient : ℝ) / (W N : ℝ) := W_ratio_pos N
  have hFmnn : 0 ≤ MaynardSmoothY.Fmax F := MaynardSmoothY.Fmax_nonneg F hF
  have hLDnn : 0 ≤ Real.log (PrimeGaps.D₀ (N : ℝ)) := Real.log_nonneg (one_le_two.trans hD)
  have hLDle : Real.log (PrimeGaps.D₀ (N : ℝ)) ≤ Real.log R := by
    linarith only [hLDscaled N hxLD, le_mul_of_one_le_left hLDnn (one_le_two.trans hD)]
  set ratio : ℝ := ((W N).totient : ℝ) / (W N : ℝ)
  set Fm : ℝ := MaynardSmoothY.Fmax F
  set LD : ℝ := Real.log (PrimeGaps.D₀ (N : ℝ))
  have hcnn : 0 ≤ ratio * Real.log R := mul_nonneg hratiopos.le hlogRpos.le
  have hErrnn : 0 ≤ Cyd * ratio * LD * Fm := by positivity
  have hEnn := mul_nonneg hErrnn
    (add_nonneg (mul_nonneg (mul_nonneg zero_le_two hcnn) hFmnn) hErrnn)
  have hEbound : Cyd * ratio * LD * Fm * (2 * (ratio * Real.log R) * Fm +
      Cyd * ratio * LD * Fm) ≤ (2 * Cyd + Cyd ^ 2) * ratio ^ 2 * Real.log R * LD * Fm ^ 2 := by
    linarith [mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg ratio) hLDnn) (sq_nonneg Fm))
      (mul_nonneg (sq_nonneg Cyd) (sub_nonneg.mpr hLDle))]
  set Fbox : Finset (Fin n → ℕ) :=
    Fintype.piFinset (fun _ : Fin n ↦ Finset.range ⌈R⌉₊) with hFboxdef
  have hboxle : (∑ σ ∈ Fbox, if (∀ j, (σ j).Coprime (W N) ∧ Squarefree (σ j)) then
      ∏ j, (1 : ℝ) / (g (σ j) : ℝ) else 0) ≤ (2 * ratio * Real.log R) ^ n := by
    have hmem : ∀ σ : Fin n → ℕ, σ ∈ Fbox ↔ ∀ j, (σ j : ℝ) < R := by
      simp [hFboxdef, Fintype.mem_piFinset, Nat.lt_ceil]
    exact le_of_eq_of_le
      ((tsum_eq_sum fun σ hσ ↦ if_neg fun h ↦ hσ ((hmem σ).mpr fun j ↦ (h j).2.2)).trans
        (Finset.sum_congr rfl fun σ hσ ↦ if_congr ⟨fun h j ↦ ⟨(h j).1, (h j).2.1⟩,
          fun h j ↦ ⟨(h j).1, (h j).2, (hmem σ).mp hσ j⟩⟩ rfl rfl)).symm hboxN
  have hvanish := fun σ (hσ : σ ∉ Fbox) ↦ Ydisc_Tm_vanish_of_notMem_box (W N) m F hF hsupp hR1 hσ
  refine (abs_tsum_mul_sq_sub_le_boxmass Fbox
      (fun σ ↦ Finset.prod_nonneg fun j _ ↦ by positivity)
      (fun σ hσ ↦ (hvanish σ hσ).1) (fun σ hσ ↦ (hvanish σ hσ).2)
      fun σ ↦ abs_sq_sub_mul_sq_le hcnn hErrnn (hyd' σ) (hTm _)).trans ?_
  exact ((mul_le_mul_of_nonneg_left hboxle hEnn).trans (mul_le_mul_of_nonneg_right hEbound
    (pow_nonneg (mul_nonneg (mul_nonneg zero_le_two hratiopos.le) hlogRpos.le) n))).trans_eq
    (by ring)

private theorem hasDerivAt_integral_insertLp_shift {n : ℕ} (m : Fin (n + 1))
    (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hsupp : Function.support F ⊆ 𝓡 (n + 1)) (t : EuclideanSpace ℝ (Fin n))
    (eJ : EuclideanSpace ℝ (Fin (n + 1))) (heJnorm : ‖eJ‖ = 1) (Cf : ℝ)
    (hCf : ∀ x, ‖fderiv ℝ F x‖ ≤ Cf)
    (hvan : ∀ (h s : ℝ), s ∉ Set.Icc (0 : ℝ) 1 → fderiv ℝ F (insertLp m s t + h • eJ) = 0) :
    HasDerivAt (fun h : ℝ ↦ ∫ s : ℝ, F (insertLp m s t + h • eJ))
      (∫ s : ℝ, fderiv ℝ F (insertLp m s t + (0 : ℝ) • eJ) eJ) (0 : ℝ) := by
  have hcont_y : Continuous (fun s : ℝ ↦ insertLp m s t) := by
    have h1 : Continuous (fun s : ℝ ↦ insertLp m 0 t + s • EuclideanSpace.single m (1 : ℝ)) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa only [← insertLp_affine] using h1
  set G : ℝ → ℝ → ℝ := fun h s ↦ F (insertLp m s t + h • eJ) with hG
  set G' : ℝ → ℝ → ℝ := fun h s ↦ fderiv ℝ F (insertLp m s t + h • eJ) eJ with hG'
  have hdom : ∀ h s : ℝ, ‖G' h s‖ ≤ Set.indicator (Set.Icc (0 : ℝ) 1) (fun _ ↦ Cf) s := by
    intro h s
    by_cases hs : s ∈ Set.Icc (0 : ℝ) 1
    · rw [Set.indicator_of_mem hs]
      simpa [hG', heJnorm] using
        (fderiv ℝ F (insertLp m s t + h • eJ)).le_of_opNorm_le (hCf _) eJ
    · simp [hG', Set.indicator_of_notMem hs, hvan h s hs]
  have hdiff : ∀ s h : ℝ, HasDerivAt (fun h ↦ G h s) (G' h s) h := by
    intro s h
    have hlin : HasDerivAt (fun h : ℝ ↦ insertLp m s t + h • eJ) eJ h := by
      simpa using ((hasDerivAt_id h).smul_const eJ).const_add (insertLp m s t)
    exact (hF.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt h hlin
  have hcontG : ∀ h : ℝ, Continuous (G h) := fun h ↦
    hF.continuous.comp (hcont_y.add continuous_const)
  have hcs_G0 : HasCompactSupport (G 0) := by
    refine .of_support_subset_isCompact (isCompact_Icc (a := (0 : ℝ)) (b := 1)) fun s hs ↦ ?_
    have hmem : insertLp m s t ∈ 𝓡 (n + 1) := hsupp (by simpa [hG] using hs)
    simpa using coord_mem_Icc_of_mem_R hmem m
  have hcontG'0 : Continuous (G' 0) :=
    (ContinuousLinearMap.apply ℝ ℝ eJ).continuous.comp
      ((hF.continuous_fderiv (by simp)).comp (hcont_y.add continuous_const))
  have hbint : Integrable (Set.indicator (Set.Icc (0 : ℝ) 1) (fun _ ↦ Cf)) volume :=
    (continuousOn_const.integrableOn_compact isCompact_Icc).integrable_indicator
      measurableSet_Icc
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := G) (F' := G') (bound := Set.indicator (Set.Icc (0 : ℝ) 1) (fun _ ↦ Cf))
    (Metric.ball_mem_nhds (0 : ℝ) one_pos)
    (Filter.Eventually.of_forall fun h ↦ (hcontG h).aestronglyMeasurable)
    ((hcontG 0).integrable_of_hasCompactSupport hcs_G0) hcontG'0.aestronglyMeasurable
    (Filter.Eventually.of_forall fun s h _ ↦ hdom h s) hbint
    (Filter.Eventually.of_forall fun s h _ ↦ hdiff s h)).2

private theorem abs_fderiv_single_le_Fmax {k : ℕ} {F : EuclideanSpace ℝ (Fin k) → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) {x : EuclideanSpace ℝ (Fin k)}
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) (i : Fin k) :
    |fderiv ℝ F x (EuclideanSpace.single i 1)| ≤ MaynardSmoothY.Fmax F :=
  ((Finset.single_le_sum (f := fun j ↦ |fderiv ℝ F x (EuclideanSpace.single j 1)|)
      (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ i)).trans
    (le_add_of_nonneg_left (abs_nonneg _))).trans
    (le_csSup (MaynardSmoothY.abs_F_bddAbove F hF) ⟨x, hx, rfl⟩)

/-- The directional derivatives of the marginal `Tm m F` on the unit box are bounded by
`Fmax F`. -/
theorem Tm_dir_deriv_le {n : ℕ} (m : Fin (n + 1)) (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hsupp : Function.support F ⊆ 𝓡 (n + 1))
    (t : EuclideanSpace ℝ (Fin n)) (ht : ∀ j, t j ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) :
    |fderiv ℝ (Tm m F) t (EuclideanSpace.single i 1)| ≤ MaynardSmoothY.Fmax F := by
  set eJ : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single (m.succAbove i) (1 : ℝ) with heJ
  obtain ⟨Cf, hCf⟩ := (hF.continuous_fderiv (by simp)).bounded_above_of_compact_support
    ((HasCompactSupport.of_support_subset_isCompact isCompact_scaledStdSimplex hsupp).fderiv
      (𝕜 := ℝ))
  have hins : ∀ s h : ℝ,
      insertLp m s (t + h • EuclideanSpace.single i (1 : ℝ)) = insertLp m s t + h • eJ := by
    intro s h
    ext k
    refine Fin.succAboveCases m (by simp [heJ]) (fun j ↦ ?_) k
    rcases eq_or_ne j i with rfl | hij
    · simp [heJ]
    · simp [heJ, hij]
  have hvan : ∀ (h s : ℝ), s ∉ Set.Icc (0 : ℝ) 1 → fderiv ℝ F (insertLp m s t + h • eJ) = 0 := by
    intro h s hs
    refine fderiv_of_notMem_tsupport ℝ fun hmem ↦ hs ?_
    simpa [heJ] using coord_mem_Icc_of_mem_R
      (closure_minimal hsupp EuclideanSpace.isClosed_scaledStdSimplex hmem) m
  have hderiv := hasDerivAt_integral_insertLp_shift m F hF hsupp t eJ
    (by simp [heJ, PiLp.norm_single]) Cf hCf hvan
  simp only [zero_smul, add_zero, ← hins] at hderiv
  have hline : HasDerivAt (fun h : ℝ ↦ t + h • EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single i 1) (0 : ℝ) := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single i (1 : ℝ))).const_add t
  have hchain : HasDerivAt (fun h ↦ Tm m F (t + h • EuclideanSpace.single i (1 : ℝ)))
      (fderiv ℝ (Tm m F) t (EuclideanSpace.single i 1)) (0 : ℝ) :=
    ((Tm_contDiff m F hF hsupp).differentiable (by simp)).differentiableAt.hasFDerivAt
      |>.comp_hasDerivAt_of_eq 0 hline (by simp)
  rw [hchain.unique hderiv, ← Real.norm_eq_abs]
  have hbnd : ∀ s : ℝ, ‖fderiv ℝ F (insertLp m s t) eJ‖ ≤
      Set.indicator (Set.Icc (0 : ℝ) 1) (fun _ ↦ MaynardSmoothY.Fmax F) s := by
    intro s
    by_cases hs : s ∈ Set.Icc (0 : ℝ) 1
    · rw [Set.indicator_of_mem hs, Real.norm_eq_abs, heJ]
      exact abs_fderiv_single_le_Fmax hF
        (fun k ↦ Fin.succAboveCases m (by simpa using hs) (fun j ↦ by simpa using ht j) k)
        (m.succAbove i)
    · have h0 : fderiv ℝ F (insertLp m s t) = 0 := by simpa using hvan 0 s hs
      simp [Set.indicator_of_notMem hs, h0]
  refine (norm_integral_le_of_norm_le ((continuousOn_const.integrableOn_compact
      isCompact_Icc).integrable_indicator measurableSet_Icc)
      (Filter.Eventually.of_forall hbnd)).trans_eq ?_
  rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le zero_le_one]
  simp

/-- `Fmax (Tm m F) ≤ (n + 1) * Fmax F`. -/
theorem Fmax_Tm_le {n : ℕ} (m : Fin (n + 1)) (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hsupp : Function.support F ⊆ 𝓡 (n + 1)) :
    MaynardSmoothY.Fmax (Tm m F) ≤ ((n : ℝ) + 1) * MaynardSmoothY.Fmax F := by
  rw [MaynardSmoothY.Fmax]
  refine Real.sSup_le ?_ (mul_nonneg n.cast_add_one_pos.le (MaynardSmoothY.Fmax_nonneg F hF))
  rintro v ⟨τ, hτ, rfl⟩
  have h2 : ∑ j, |fderiv ℝ (Tm m F) τ (EuclideanSpace.single j 1)| ≤
      (n : ℝ) * MaynardSmoothY.Fmax F := by
    simpa using Finset.sum_le_card_nsmul .univ _ _ fun j _ ↦ Tm_dir_deriv_le m F hF hsupp τ hτ j
  linarith [Tm_abs_le_Fmax m F hF hsupp τ]

/-- `0 ≤ ∫_{𝓡 k} F² ≤ (Fmax F)²`, since `𝓡 k` sits inside the unit cube of volume `1`. -/
theorem S2m_intFsq_le {k : ℕ} (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hsupp : Function.support F ⊆ 𝓡 k) :
    0 ≤ (∫ x in 𝓡 k, (F x) ^ 2) ∧ (∫ x in 𝓡 k, (F x) ^ 2) ≤ (MaynardSmoothY.Fmax F) ^ 2 := by
  set cube : Set (Fin k → ℝ) := Set.pi Set.univ (fun _ : Fin k ↦ Set.Icc (0 : ℝ) 1) with hcube
  have hcubeq : (∫ x in 𝓡 k, (F x) ^ 2) =
      ∫ x in cube, (F (WithLp.toLp 2 x)) ^ 2 := S1_integral_cube F hsupp
  have hcube' : cube = Set.Icc (fun _ : Fin k ↦ (0 : ℝ)) (fun _ : Fin k ↦ (1 : ℝ)) := by
    rw [hcube, Set.pi_univ_Icc]
  refine ⟨?_, ?_⟩
  · rw [hcubeq]
    exact setIntegral_nonneg (.univ_pi fun _ ↦ measurableSet_Icc) fun x _ ↦ by positivity
  · rw [hcubeq]
    have hfin : volume cube < ⊤ := by
      rw [hcube', Real.volume_Icc_pi]
      exact ENNReal.prod_lt_top fun i _ ↦ ENNReal.ofReal_lt_top
    have hbound : ∀ x ∈ cube, ‖(F (WithLp.toLp 2 x)) ^ 2‖ ≤ (MaynardSmoothY.Fmax F) ^ 2 := by
      intro x hx
      rw [hcube, Set.mem_pi] at hx
      have habs := abs_le.mp (MaynardSmoothY.abs_F_le_Fmax F hF fun i ↦ hx i (Set.mem_univ i))
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact sq_le_sq' habs.1 habs.2
    have hkey := norm_setIntegral_le_of_norm_le_const hfin hbound
    have hvol : volume.real cube = 1 := by
      rw [measureReal_def, hcube', Real.volume_Icc_pi_toReal fun _ ↦ zero_le_one]
      simp
    rw [hvol, mul_one] at hkey
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hkey)

private theorem abs_pow_mul_sub_pow_mul_le (k : ℕ) (𝔰 q ℓ I Fm Cs K D : ℝ)
    (hCs : 0 ≤ Cs) (hK1 : 1 ≤ K) (h𝔰nn : 0 ≤ 𝔰) (hqnn : 0 ≤ q) (hℓnn : 0 ≤ ℓ)
    (hDpos : 0 < D) (hSing : |𝔰 - q| ≤ Cs * q * (1 / D)) (h𝔰leKq : 𝔰 ≤ K * q)
    (hInn : 0 ≤ I) (hIle : I ≤ Fm) :
    |(𝔰 * ℓ) ^ k * I - (q * ℓ) ^ k * I| ≤
      Cs * (k : ℝ) * K ^ (k - 1) * (Fm * q ^ k * ℓ ^ (k - 1) * (ℓ / D)) := by
  obtain _ | k := k
  · simp
  have hFm : (0 : ℝ) ≤ Fm := hInn.trans hIle
  have hmax : max |𝔰| |q| ≤ K * q :=
    max_le ((abs_of_nonneg h𝔰nn).trans_le h𝔰leKq)
      ((abs_of_nonneg hqnn).trans_le (le_mul_of_one_le_left hqnn hK1))
  calc |(𝔰 * ℓ) ^ (k + 1) * I - (q * ℓ) ^ (k + 1) * I|
      = |𝔰 ^ (k + 1) - q ^ (k + 1)| * (ℓ ^ (k + 1) * I) := by
        rw [← abs_of_nonneg (mul_nonneg (pow_nonneg hℓnn _) hInn), ← abs_mul]
        ring_nf
    _ ≤ |𝔰 - q| * (k + 1 : ℕ) * max |𝔰| |q| ^ k * (ℓ ^ (k + 1) * Fm) := by
        gcongr
        simpa using abs_pow_sub_pow_le 𝔰 q (k + 1)
    _ ≤ Cs * q * (1 / D) * (k + 1 : ℕ) * (K * q) ^ k * (ℓ ^ (k + 1) * Fm) := by gcongr
    _ = Cs * (k + 1 : ℕ) * K ^ k * (Fm * q ^ (k + 1) * ℓ ^ k * (ℓ / D)) := by ring

private theorem boxTerm_le_mul_aux {a₁ a₂ K c₁ c₃ CLD 𝔰 q ℓ LD τ P z L : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hK : 0 ≤ K) (hc₁ : 0 ≤ c₁) (hc₃ : 0 ≤ c₃)
    (hq : 0 ≤ q) (hℓ : 0 ≤ ℓ) (hτ : 0 ≤ τ) (hP : 0 ≤ P) (hz : 0 ≤ z)
    (h𝔰K : 𝔰 ≤ K * q) (hPc : P ≤ c₁ * LD) (hzL : τ * (z * L) ≤ c₃ * q * LD)
    (hLD : LD ≤ CLD * ℓ) (hℓL : ℓ ≤ L) :
    2 * 𝔰 * ℓ + a₁ * 𝔰 * P + a₂ * τ * (z * (L + ℓ)) ≤
      (2 * K + a₁ * K * c₁ * CLD + 2 * (a₂ * c₃ * CLD)) * q * ℓ := by
  have h1 : 2 * 𝔰 * ℓ ≤ 2 * K * q * ℓ := by
    linarith only [mul_le_mul_of_nonneg_right h𝔰K hℓ]
  have h2 : a₁ * 𝔰 * P ≤ a₁ * K * c₁ * CLD * q * ℓ :=
    calc a₁ * 𝔰 * P ≤ a₁ * (K * q) * (c₁ * (CLD * ℓ)) := by
          gcongr
          exact hPc.trans (by gcongr)
      _ = a₁ * K * c₁ * CLD * q * ℓ := by ring
  have h3 : a₂ * τ * (z * (L + ℓ)) ≤ 2 * (a₂ * c₃ * CLD) * q * ℓ :=
    calc a₂ * τ * (z * (L + ℓ)) ≤ a₂ * τ * (z * (L + L)) := by gcongr
      _ = a₂ * (2 * (τ * (z * L))) := by ring
      _ ≤ a₂ * (2 * (c₃ * q * LD)) := by gcongr a₂ * (2 * ?_)
      _ ≤ a₂ * (2 * (c₃ * q * (CLD * ℓ))) := by gcongr
      _ = 2 * (a₂ * c₃ * CLD) * q * ℓ := by ring
  linarith

private theorem perturbTerm_le_mul_aux {b₁ b₂ K c₁ c₂ c₃ 𝔰 q LD τ P Fm X Y : ℝ}
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hK : 0 ≤ K)
    (hq : 0 ≤ q) (hP : 0 ≤ P) (hFm : 0 ≤ Fm)
    (h𝔰K : 𝔰 ≤ K * q) (hPc : P ≤ c₁ * LD) (hX : τ * X ≤ c₃ * q * LD)
    (hY : τ * Y ≤ c₂ * q * LD) :
    2 * (3 * Fm) * (2 * b₁ * 𝔰 * P + b₂ * τ * (X + Y)) ≤
      6 * (2 * b₁ * K * c₁ + b₂ * (c₂ + c₃)) * Fm * q * LD := by
  have h1 : 2 * b₁ * 𝔰 * P ≤ 2 * b₁ * K * c₁ * q * LD :=
    calc 2 * b₁ * 𝔰 * P ≤ 2 * b₁ * (K * q) * (c₁ * LD) := by gcongr
      _ = 2 * b₁ * K * c₁ * q * LD := by ring
  have h2 : b₂ * τ * (X + Y) ≤ b₂ * (c₂ + c₃) * q * LD :=
    calc b₂ * τ * (X + Y) = b₂ * (τ * X + τ * Y) := by ring
      _ ≤ b₂ * (c₃ * q * LD + c₂ * q * LD) := by gcongr b₂ * (?_ + ?_)
      _ = b₂ * (c₂ + c₃) * q * LD := by ring
  calc 2 * (3 * Fm) * (2 * b₁ * 𝔰 * P + b₂ * τ * (X + Y))
      ≤ 2 * (3 * Fm) * (2 * b₁ * K * c₁ * q * LD + b₂ * (c₂ + c₃) * q * LD) := by gcongr
    _ = 6 * (2 * b₁ * K * c₁ + b₂ * (c₂ + c₃)) * Fm * q * LD := by ring

private theorem mul_pow_mul_le_aux {k : ℕ} (hk : 0 < k) {Bc PE Cb Cp Fm q ℓ LD : ℝ}
    (hBc : 0 ≤ Bc) (hPE : 0 ≤ PE) (hCb : 0 ≤ Cb) (hq : 0 ≤ q) (hℓ : 0 ≤ ℓ)
    (hFm : 0 ≤ Fm) (hLD : 0 ≤ LD) (hCp : 0 ≤ Cp)
    (h1 : Bc ≤ Cb * q * ℓ) (h2 : PE ≤ Cp * Fm * q * LD) :
    (k : ℝ) * Bc ^ (k - 1) * PE ≤
      (k : ℝ) * max 1 Cb ^ k * Cp * (Fm * q ^ k * ℓ ^ (k - 1) * LD) := by
  have hpow : Cb ^ (k - 1) ≤ max 1 Cb ^ k :=
    (pow_le_pow_left₀ hCb (le_max_right 1 Cb) _).trans
      (pow_le_pow_right₀ (le_max_left 1 Cb) (Nat.sub_le k 1))
  calc (k : ℝ) * Bc ^ (k - 1) * PE
      ≤ (k : ℝ) * (Cb * q * ℓ) ^ (k - 1) * (Cp * Fm * q * LD) := by gcongr
    _ = (k : ℝ) * Cb ^ (k - 1) * Cp * (Fm * (q ^ (k - 1) * q) * ℓ ^ (k - 1) * LD) := by
        rw [mul_pow, mul_pow]; ring
    _ = (k : ℝ) * Cb ^ (k - 1) * Cp * (Fm * q ^ k * ℓ ^ (k - 1) * LD) := by
        rw [pow_sub_one_mul hk.ne' q]
    _ ≤ (k : ℝ) * max 1 Cb ^ k * Cp * (Fm * q ^ k * ℓ ^ (k - 1) * LD) := by gcongr

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- `sieveE` differs from its main term `(φ(W)/W · log R)^k · ∫_{𝓡 k} F²` by a singular-series
error and a partial-summation error, each of relative size `1/D₀ N` resp. `log (D₀ N) / log R`. -/
theorem sieveE_split_bound {k : ℕ} : ∃ Csing : ℝ, 0 ≤ Csing ∧ ∀ (δ θ : ℝ),
      θ ∈ Set.Ioo (0 : ℝ) 1 → δ ∈ Set.Ioo (0 : ℝ) (θ / 2) →
      ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (hNpos : 0 < N) (hD : 2 ≤ PrimeGaps.D₀ (N : ℝ))
        (F : EuclideanSpace ℝ (Fin k) → ℝ), ContDiff ℝ (⊤ : ℕ∞) F →
        Function.support F ⊆ 𝓡 k →
        |sieveE (maynardSieveDatum N hNpos hD) R F k - (((W N).totient : ℝ) / (W N : ℝ) *
                Real.log R) ^ k * (∫ x in 𝓡 k, (F x) ^ 2)| ≤
          Csing * ((MaynardSmoothY.Fmax F) ^ 2 * ((W N).totient : ℝ) ^ k *
                (Real.log R) ^ (k - 1) *
                (Real.log R / PrimeGaps.D₀ (N : ℝ)) /
                (W N : ℝ) ^ k) +
            C₁ * ((MaynardSmoothY.Fmax F) ^ 2 * ((W N).totient : ℝ) ^ k * (Real.log R) ^ (k - 1) *
                Real.log (PrimeGaps.D₀ (N : ℝ)) / (W N : ℝ) ^ k) := by
  obtain ⟨Cs, hCs, xs, hSing⟩ := singularSeries_maynard_asymptotic
  obtain ⟨Cs₁, Cs₂, Ch₁, Ch₂, hCs₁, hCs₂, hCh₁, hCh₂, habs⟩ := sieveDatum_kfold_partial_sum
  obtain ⟨c₁, hc₁, N₁, hH1⟩ := S1_OB_H1
  have hCs₁' : 0 < Cs₁ (1 / 2) 2 := hCs₁ _ _
  have hCs₂' : 0 < Cs₂ (1 / 2) 2 := hCs₂ _ _
  have hCh₁' : 0 < Ch₁ (1 / 2) 2 := hCh₁ _ _
  have hCh₂' : 0 < Ch₂ (1 / 2) 2 := hCh₂ _ _
  set K : ℝ := 1 + Cs / 2 with hKdef
  have hK1 : (1 : ℝ) ≤ K := by rw [hKdef]; linarith
  have hKpos : 0 < K := one_pos.trans_le hK1
  set Csing : ℝ := Cs * (k : ℝ) * K ^ (k - 1) with hCsingdef
  have hCsingnn : 0 ≤ Csing := by rw [hCsingdef]; positivity
  refine ⟨Csing, hCsingnn, fun δ θ hθ hδ ↦ ?_⟩
  obtain ⟨c₂, hc₂, N₂, hH2⟩ := S1_OB_H2 δ θ hθ hδ
  obtain ⟨c₃, hc₃, N₃, hH3⟩ := S1_OB_H3 δ θ hθ hδ
  obtain ⟨x2, h2R⟩ := two_le_R δ θ hδ
  obtain ⟨hδ0, hδθ⟩ := hδ
  have hcθ : (0 : ℝ) < θ / 2 - δ := by linarith
  set CLD : ℝ := 1 / (θ / 2 - δ) with hCLDdef
  set Cbox : ℝ := 2 * K + Ch₁ (1 / 2) 2 * K * c₁ * CLD + 2 * (Ch₂ (1 / 2) 2 * c₃ *
    CLD) with hCboxdef
  have hCboxpos : 0 < Cbox := by rw [hCboxdef]; positivity
  set Cp : ℝ := 6 * (2 * Cs₁ (1 / 2) 2 * K * c₁ + Cs₂ (1 / 2) 2 * (c₂ + c₃)) with hCpdef
  have hCppos : 0 < Cp := by rw [hCpdef]; positivity
  set C₁ : ℝ := (k : ℝ) * (max 1 Cbox) ^ k * Cp with hC₁def
  have hC₁nn : 0 ≤ C₁ := by rw [hC₁def]; positivity
  refine ⟨C₁, hC₁nn,
    max (max N₁ N₂) (max N₃ (max xs (max x2 (rexp (rexp (rexp 2)) + 1)))),
    fun N hN hNpos hD F hF hsupp ↦ ?_⟩
  simp only [max_le_iff] at hN
  obtain ⟨⟨hN1, hN2⟩, hN3, hxs, hx2, hNexp⟩ := hN
  have hNe : rexp (rexp (rexp 2)) ≤ (N : ℝ) := by linarith
  have hNposR : (0 : ℝ) < (N : ℝ) := (Real.exp_pos _).trans_le hNe
  have hW1R : (1 : ℝ) ≤ (W N : ℝ) := mod_cast PrimeGaps.W_pos (N := N)
  have hR2 : (2 : ℝ) ≤ R := h2R N hx2
  have hℓpos : 0 < Real.log R := Real.log_pos (by linarith)
  have hqnn : (0 : ℝ) ≤ ((W N).totient : ℝ) / (W N : ℝ) := by positivity
  have hFmnn : (0 : ℝ) ≤ (MaynardSmoothY.Fmax F) ^ 2 := sq_nonneg _
  have hτnn : (0 : ℝ) ≤ (#(W N).divisors : ℝ) := Nat.cast_nonneg _
  have hD0pos : (0 : ℝ) < PrimeGaps.D₀ (N : ℝ) := by linarith
  have hLDpos : 0 < Real.log (PrimeGaps.D₀ (N : ℝ)) := Real.log_pos (by linarith)
  have h𝔰pos : 0 < PrimeGaps.singularSeries (maynardSieveDatum N hNpos hD).γ :=
    PrimeGaps.singularSeries_pos _
  have hpls1 : (0 : ℝ) ≤ 1 + ellV (W N) := add_nonneg zero_le_one (ellV_nonneg (W N))
  have hzpow : (0 : ℝ) ≤ R ^ (-(1 : ℝ) / 8) := by positivity
  have hlogWnn : 0 ≤ Real.log (2 * (W N : ℝ)) := Real.log_nonneg (by linarith)
  have hlogRle : Real.log R ≤ Real.log (2 * (W N : ℝ) * R) :=
    Real.log_le_log (by linarith) (le_mul_of_one_le_left (by linarith) (by linarith))
  have hlogRnn : (0 : ℝ) ≤ Real.log (2 * (W N : ℝ) * R) := hℓpos.le.trans hlogRle
  have hDleN : PrimeGaps.D₀ (N : ℝ) ≤ (N : ℝ) :=
    PrimeGaps.D₀_le_self ((Real.exp_le_exp.mpr (Real.one_le_exp (Real.exp_nonneg _))).trans hNe)
  have hlogDleN : Real.log (PrimeGaps.D₀ (N : ℝ)) ≤ Real.log (N : ℝ) := Real.log_le_log hD0pos hDleN
  have hRlog : Real.log R = (θ / 2 - δ) * Real.log (N : ℝ) := Real.log_rpow hNposR _
  obtain ⟨hINTnn, hINTle⟩ := S2m_intFsq_le F hF hsupp
  have hSing' := hSing N hxs hNpos hD
  have hb1 := hH1 N hN1
  have hb2 := hH2 N hN2
  have hb3 := hH3 N hN3
  have hE0 := sieveE_zero (maynardSieveDatum N hNpos hD) R F hsupp
  have hb := habs (maynardSieveDatum N hNpos hD) F hF hsupp R hR2
  rw [maynardSieveDatum_A₁ N hNpos hD, maynardSieveDatum_A₃ N hNpos hD,
    maynardSieveDatum_V N hNpos hD] at hb
  set S : SieveDatum := maynardSieveDatum N hNpos hD
  set 𝔰 : ℝ := PrimeGaps.singularSeries S.γ
  set q : ℝ := ((W N).totient : ℝ) / (W N : ℝ) with hqdef
  set ℓ : ℝ := Real.log R
  set LD : ℝ := Real.log (PrimeGaps.D₀ (N : ℝ))
  set Fm : ℝ := (MaynardSmoothY.Fmax F) ^ 2
  set τ : ℝ := (#(W N).divisors : ℝ)
  set D0 : ℝ := PrimeGaps.D₀ (N : ℝ)
  set INT : ℝ := ∫ x in 𝓡 k, (F x) ^ 2
  have hTGBnn : (0 : ℝ) ≤ Fm * ((W N).totient : ℝ) ^ k * ℓ ^ (k - 1) * LD / (W N : ℝ) ^ k := by
    positivity
  set TGA : ℝ := Fm * ((W N).totient : ℝ) ^ k * ℓ ^ (k - 1) * (ℓ / D0) / (W N : ℝ) ^ k with hTGAdef
  set TGB : ℝ := Fm * ((W N).totient : ℝ) ^ k * ℓ ^ (k - 1) * LD / (W N : ℝ) ^ k with hTGBdef
  have h𝔰leKq : 𝔰 ≤ K * q := by
    have h2 : Cs * q * (1 / D0) ≤ Cs * q * (1 / 2) := by gcongr
    rw [hKdef]
    linarith [(abs_le.mp hSing').2]
  have hLDℓ : LD ≤ CLD * ℓ :=
    hlogDleN.trans_eq (by rw [hCLDdef, hRlog, one_div, inv_mul_cancel_left₀ hcθ.ne'])
  have hBoundA : |sieveE S R F 0 - (q * ℓ) ^ k * INT| ≤ Csing * TGA := by
    rw [hE0, hCsingdef, hTGAdef]
    refine (abs_pow_mul_sub_pow_mul_le k 𝔰 q ℓ INT Fm Cs K D0 hCs.le hK1 h𝔰pos.le hqnn
      hℓpos.le hD0pos hSing' h𝔰leKq hINTnn hINTle).trans_eq ?_
    rw [hqdef, div_pow]
    ring
  have hBoundB : |sieveE S R F k - sieveE S R F 0| ≤ C₁ * TGB := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      simp only [Nat.cast_zero, zero_mul] at hb
      exact hb.trans (mul_nonneg hC₁nn hTGBnn)
    · set Bc : ℝ := 2 * 𝔰 * ℓ + Ch₁ (1 / 2) 2 * 𝔰 * (1 + ellV (W N)) + Ch₂ (1 / 2) 2 * τ *
        (R ^ (-(1 : ℝ) / 8) * (Real.log (2 * (W N : ℝ) * R) + ℓ)) with hBcdef
      set PE : ℝ := 2 * (3 * Fm) * (2 * Cs₁ (1 / 2) 2 * 𝔰 * (1 + ellV (W N)) +
        Cs₂ (1 / 2) 2 * τ * (R ^ (-(1 : ℝ) / 8) * Real.log (2 * (W N : ℝ) * R) +
          (8 * Real.log (2 * (W N : ℝ)) + 64) / ℓ)) with hPEdef
      have hBcnn : 0 ≤ Bc := by rw [hBcdef]; positivity
      have hPEnn : 0 ≤ PE := by rw [hPEdef]; positivity
      have hBcle : Bc ≤ Cbox * q * ℓ := by
        rw [hBcdef, hCboxdef]
        exact boxTerm_le_mul_aux hCh₁'.le hCh₂'.le hKpos.le hc₁.le hc₃.le hqnn hℓpos.le hτnn
          hpls1 hzpow h𝔰leKq hb1 hb3 hLDℓ hlogRle
      have hPEle : PE ≤ Cp * Fm * q * LD := by
        rw [hPEdef, hCpdef]
        exact perturbTerm_le_mul_aux hCs₁'.le hCs₂'.le hKpos.le hqnn hpls1 hFmnn h𝔰leKq hb1
          hb3 (by rwa [← mul_div_assoc])
      calc |sieveE S R F k - sieveE S R F 0| ≤ (k : ℝ) * Bc ^ (k - 1) * PE := hb
        _ ≤ (k : ℝ) * max 1 Cbox ^ k * Cp * (Fm * q ^ k * ℓ ^ (k - 1) * LD) :=
            mul_pow_mul_le_aux hkpos hBcnn hPEnn hCboxpos.le hqnn hℓpos.le hFmnn hLDpos.le
              hCppos.le hBcle hPEle
        _ = C₁ * TGB := by rw [hC₁def, hTGBdef, hqdef, div_pow]; ring
  calc |sieveE S R F k - (q * ℓ) ^ k * INT|
      ≤ |sieveE S R F k - sieveE S R F 0| + |sieveE S R F 0 - (q * ℓ) ^ k * INT| :=
        abs_sub_le _ _ _
    _ ≤ C₁ * TGB + Csing * TGA := add_le_add hBoundB hBoundA
    _ = Csing * TGA + C₁ * TGB := add_comm _ _

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- The decoupled sum evaluates to `φ(W)^(k+1) (log R)^(k+1) / W^(k+1) · J m F`, with error
`O((Fmax F)² · φ(W)^(k+1) (log R)^(k+1) / (W^(k+1) · D₀ N))` uniformly in `F` and `m`. -/
@[pg_tag "bg246" "lem_S2m_eval"]
theorem lem_S2m_eval {k : ℕ} (hk : 2 ≤ k) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (H : Finset ℕ), H.Admissible → #H = k →
      ∀ (θ δ : ℝ), θ ∈ Set.Ioo (0 : ℝ) 1 → 0 < δ → δ < θ / 2 →
      ∀ (F : EuclideanSpace ℝ (Fin k) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
        (hsupp : Function.support F ⊆ 𝓡 k),
      ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N → ∀ (m : Fin k),
          |decoupledSum R (W N) F m - ((W N).totient : ℝ) ^ (k + 1) * (Real.log R) ^ (k + 1) /
                (W N : ℝ) ^ (k + 1) * PrimeGaps.J m ((hF.continuous.memLp_of_hasCompactSupport
                      (HasCompactSupport.of_support_subset_isCompact
                        isCompact_scaledStdSimplex hsupp)).toLp F)| ≤
          C * (MaynardSmoothY.Fmax F) ^ 2 * ((W N).totient : ℝ) ^ (k + 1) *
              (Real.log R) ^ (k + 1) /
              ((W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ)) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  obtain ⟨Csing, hCsing0, hsplit⟩ := sieveE_split_bound (k := n + 1)
  refine ⟨Csing * ((n : ℝ) + 2) ^ 2 + 2, by positivity, ?_⟩
  intro H _ _ θ δ hθ hδ0 hδθ F hF hsupp
  have hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2) := ⟨hδ0, hδθ⟩
  obtain ⟨Ccross, hCcross0, Ncross, hcross⟩ := cross_error (n := n + 1) δ θ hδ
  obtain ⟨C₁, hC₁0, Nsplit, hsplitN⟩ := hsplit δ θ hθ hδ
  obtain ⟨xg1, hg1⟩ := D0_logD0_scaled δ θ hδ Ccross
  obtain ⟨xg2, hg2⟩ := D0_logD0_scaled δ θ hδ (C₁ * ((n : ℝ) + 2) ^ 2)
  obtain ⟨x2, h2R⟩ := two_le_R δ θ hδ
  refine ⟨max (max Ncross Nsplit) (max xg1 (max xg2 (max x2
      (rexp (rexp (rexp 2)) + 1)))), fun N hN₀ m ↦ ?_⟩
  simp only [max_le_iff] at hN₀
  obtain ⟨⟨hNcross, hNsplit⟩, hxg1, hxg2, hx2, hNexp⟩ := hN₀
  have hNe : rexp (rexp (rexp 2)) ≤ (N : ℝ) := by linarith
  have hNpos : 0 < N := mod_cast (Real.exp_pos _).trans_le hNe
  have hD : 2 ≤ PrimeGaps.D₀ (N : ℝ) := MaynardOffDiagonal.two_le_D0_of_large hNe
  have hR2 : (2 : ℝ) ≤ R := h2R N hx2
  rw [decoupledSum_reindex R (W N) (one_lt_two.trans_le hR2) F hsupp m]
  have hmemF : MemLp F 2 (volume.restrict (𝓡 (n + 2))) :=
    hF.continuous.memLp_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_scaledStdSimplex hsupp)
  have hcrossN := hcross N hNcross hNpos hD F hF hsupp m
  rw [M_eq_sieveE (n := n + 1) N R hNpos hD F hsupp m] at hcrossN
  have hsplitTm := hsplitN N hNsplit hNpos hD (Tm m F) (Tm_contDiff m F hF hsupp)
    (Tm_support m F hsupp)
  rw [Tm_sq_integral_eq_J m F hsupp hmemF] at hsplitTm
  simp only [Nat.add_sub_cancel] at hsplitTm
  have hℓpos : 0 < Real.log R := Real.log_pos (by linarith only [hR2])
  have hD0pos : 0 < PrimeGaps.D₀ (N : ℝ) := by linarith only [hD]
  have hLDnn : 0 ≤ Real.log (PrimeGaps.D₀ (N : ℝ)) := Real.log_nonneg (by linarith only [hD])
  have hFmnn : 0 ≤ MaynardSmoothY.Fmax F := MaynardSmoothY.Fmax_nonneg F hF
  have hFmTsq : MaynardSmoothY.Fmax (Tm m F) ^ 2 ≤
      ((n : ℝ) + 2) ^ 2 * MaynardSmoothY.Fmax F ^ 2 := by
    have h := Fmax_Tm_le m F hF hsupp
    push_cast at h
    rw [← mul_pow]
    exact pow_le_pow_left₀ (MaynardSmoothY.Fmax_nonneg _ (Tm_contDiff m F hF hsupp))
      (by linarith) 2
  have hg1' := hg1 N hxg1
  have hg2' := hg2 N hxg2
  set q : ℝ := ((W N).totient : ℝ) / (W N : ℝ) with hqdef
  set ℓ : ℝ := Real.log R
  set D0 : ℝ := PrimeGaps.D₀ (N : ℝ)
  set LD : ℝ := Real.log D0
  set Fm : ℝ := MaynardSmoothY.Fmax F
  set FmT : ℝ := MaynardSmoothY.Fmax (Tm m F)
  set S : SieveDatum := maynardSieveDatum N hNpos hD
  set J : ℝ := PrimeGaps.J m (hmemF.toLp F)
  set base : ℝ := Fm ^ 2 * q ^ (n + 3) * ℓ ^ (n + 3) / D0 with hbasedef
  have hT1 : Ccross * q ^ (n + 1 + 2) * ℓ ^ (n + 1 + 1) * LD * Fm ^ 2 ≤ base :=
    calc Ccross * q ^ (n + 1 + 2) * ℓ ^ (n + 1 + 1) * LD * Fm ^ 2
        = Fm ^ 2 * q ^ (n + 3) * ℓ ^ (n + 2) * (Ccross * LD) := by ring
      _ ≤ Fm ^ 2 * q ^ (n + 3) * ℓ ^ (n + 2) * (ℓ / D0) := by
          gcongr
          rw [le_div_iff₀ hD0pos]
          linarith only [hg1']
      _ = base := by rw [hbasedef]; ring
  have hT2 : (q * ℓ) ^ 2 * (Csing * (FmT ^ 2 * q ^ (n + 1) * ℓ ^ n * (ℓ / D0))) ≤
      Csing * ((n : ℝ) + 2) ^ 2 * base :=
    calc (q * ℓ) ^ 2 * (Csing * (FmT ^ 2 * q ^ (n + 1) * ℓ ^ n * (ℓ / D0)))
        = Csing * (q ^ (n + 3) * ℓ ^ (n + 2) * (ℓ / D0)) * FmT ^ 2 := by ring
      _ ≤ Csing * (q ^ (n + 3) * ℓ ^ (n + 2) * (ℓ / D0)) * (((n : ℝ) + 2) ^ 2 * Fm ^ 2) :=
          mul_le_mul_of_nonneg_left hFmTsq (by positivity)
      _ = Csing * ((n : ℝ) + 2) ^ 2 * base := by rw [hbasedef]; ring
  have hT3 : (q * ℓ) ^ 2 * (C₁ * (FmT ^ 2 * q ^ (n + 1) * ℓ ^ n * LD)) ≤ base :=
    calc (q * ℓ) ^ 2 * (C₁ * (FmT ^ 2 * q ^ (n + 1) * ℓ ^ n * LD))
        = C₁ * (q ^ (n + 3) * ℓ ^ (n + 2) * LD) * FmT ^ 2 := by ring
      _ ≤ C₁ * (q ^ (n + 3) * ℓ ^ (n + 2) * LD) * (((n : ℝ) + 2) ^ 2 * Fm ^ 2) :=
          mul_le_mul_of_nonneg_left hFmTsq (by positivity)
      _ = Fm ^ 2 * q ^ (n + 3) * ℓ ^ (n + 2) * (C₁ * ((n : ℝ) + 2) ^ 2 * LD) := by ring
      _ ≤ Fm ^ 2 * q ^ (n + 3) * ℓ ^ (n + 2) * (ℓ / D0) := by
          gcongr
          rw [le_div_iff₀ hD0pos]
          linarith only [hg2']
      _ = base := by rw [hbasedef]; ring
  have hsecond : |(q * ℓ) ^ 2 * sieveE S R (Tm m F) (n + 1) -
      ((W N).totient : ℝ) ^ (n + 2 + 1) * ℓ ^ (n + 2 + 1) / (W N : ℝ) ^ (n + 2 + 1) * J| ≤
        Csing * ((n : ℝ) + 2) ^ 2 * base + base := by
    rw [show ((W N).totient : ℝ) ^ (n + 2 + 1) * ℓ ^ (n + 2 + 1) / (W N : ℝ) ^ (n + 2 + 1) * J =
          (q * ℓ) ^ (n + 3) * J by rw [hqdef]; ring,
      show (q * ℓ) ^ 2 * sieveE S R (Tm m F) (n + 1) - (q * ℓ) ^ (n + 3) * J =
          (q * ℓ) ^ 2 * (sieveE S R (Tm m F) (n + 1) - (q * ℓ) ^ (n + 1) * J) by ring,
      abs_mul, abs_of_nonneg (sq_nonneg (q * ℓ))]
    calc (q * ℓ) ^ 2 * |sieveE S R (Tm m F) (n + 1) - (q * ℓ) ^ (n + 1) * J|
        ≤ (q * ℓ) ^ 2 * (Csing * (FmT ^ 2 * q ^ (n + 1) * ℓ ^ n * (ℓ / D0)) +
            C₁ * (FmT ^ 2 * q ^ (n + 1) * ℓ ^ n * LD)) := by
          refine mul_le_mul_of_nonneg_left (hsplitTm.trans_eq ?_) (sq_nonneg _)
          rw [hqdef, div_pow]
          ring
      _ ≤ Csing * ((n : ℝ) + 2) ^ 2 * base + base := by
          rw [mul_add]
          exact add_le_add hT2 hT3
  refine ((abs_sub_le _ ((q * ℓ) ^ 2 * sieveE S R (Tm m F) (n + 1)) _).trans
    (add_le_add (hcrossN.trans hT1) hsecond)).trans_eq ?_
  rw [hbasedef, hqdef, div_pow]
  field_simp
  ring
end PrimeGaps
