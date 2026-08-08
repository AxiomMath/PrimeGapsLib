/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.S2m.ExpandDrop.Drop

/-!
# Bounds for `gSum`

Estimates for `gSum` and its comparison with `sumA`.

## Main results

* `PrimeGaps.W_le_R_eventually`
* `PrimeGaps.gSum_le`
* `PrimeGaps.sumA_le_gSum`
-/

@[expose] public section

open Real

open scoped ArithmeticFunction.Moebius

open scoped ArithmeticFunction.detotient
open PrimeGaps

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- `(W N : ℝ) ≤ R` for all large `N`, when `δ < θ / 2`. -/
theorem PrimeGaps.W_le_R_eventually (θ δ : ℝ) (hδθ : δ < θ / 2) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N → (W N : ℝ) ≤ R := by
  set c : ℝ := θ / 2 - δ with hc_def
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  set ε : ℝ := c / Real.log 4 with hε_def
  have hε : 0 < ε := by simp only [hε_def]; positivity
  have hlittle : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ≤ ε * x := by
    filter_upwards [Real.isLittleO_log_id_atTop.def hε, Filter.eventually_ge_atTop (1 : ℝ)]
      with x hx hx1
    rwa [Real.norm_of_nonneg (Real.log_nonneg hx1), id,
      Real.norm_of_nonneg (zero_le_one.trans hx1)] at hx
  have hlittle2 : ∀ᶠ x : ℝ in Filter.atTop, Real.log (Real.log x) ≤ ε * Real.log x :=
    Real.tendsto_log_atTop.eventually hlittle
  have hkeyR : ∀ᶠ x : ℝ in Filter.atTop,
      Real.log (Real.log (Real.log x)) * Real.log 4 ≤ c * Real.log x := by
    have hxbig : ∀ᶠ x : ℝ in Filter.atTop, rexp (rexp 1) ≤ x := Filter.eventually_ge_atTop _
    filter_upwards [hlittle2, hxbig] with x h2 hxb
    have hlogx_ge : rexp 1 ≤ Real.log x := by
      have := Real.log_le_log (by positivity) hxb
      rwa [Real.log_exp] at this
    have hloglogx_ge1 : (1 : ℝ) ≤ Real.log (Real.log x) := by
      have := Real.log_le_log (by positivity) hlogx_ge
      rwa [Real.log_exp] at this
    have hstep : Real.log (Real.log (Real.log x)) ≤ Real.log (Real.log x) := by
      have := Real.log_le_sub_one_of_pos (one_pos.trans_le hloglogx_ge1)
      linarith
    refine (mul_le_mul_of_nonneg_right (hstep.trans h2) hlog4.le).trans_eq ?_
    simp only [hε_def]
    field_simp
  rw [Filter.eventually_atTop] at hkeyR
  obtain ⟨x₀, hx₀⟩ := hkeyR
  refine ⟨max (max x₀ (rexp (rexp (rexp 2)))) 2, fun N hN ↦ ?_⟩
  have hNx₀ : x₀ ≤ (N : ℝ) := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hNexp : rexp (rexp (rexp 2)) ≤ (N : ℝ) :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := (le_max_right _ _).trans hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hD0 : (2 : ℝ) ≤ PrimeGaps.D₀ (N : ℝ) := MaynardOffDiagonal.two_le_D0_of_large hNexp
  have hstepA : (W N : ℝ) ≤ (4 : ℝ) ^ (⌊PrimeGaps.D₀ (N : ℝ)⌋₊) := by
    have hnat : W N ≤ 4 ^ (⌊PrimeGaps.D₀ (N : ℝ)⌋₊) := by
      rw [PrimeGaps.W_eq_primorial_D₀]
      exact primorial_le_four_pow _
    exact_mod_cast hnat
  have hstepB : (4 : ℝ) ^ (⌊PrimeGaps.D₀ (N : ℝ)⌋₊) ≤ (4 : ℝ) ^ (PrimeGaps.D₀ (N : ℝ)) := by
    rw [← Real.rpow_natCast (4 : ℝ) (⌊PrimeGaps.D₀ (N : ℝ)⌋₊)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le (by linarith))
  have hstepC : (4 : ℝ) ^ (PrimeGaps.D₀ (N : ℝ)) ≤ (N : ℝ) ^ c := by
    rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.rpow_pos_of_pos hNpos _), Real.log_rpow (by norm_num), Real.log_rpow hNpos,
      PrimeGaps.D₀]
    exact hx₀ (N : ℝ) hNx₀
  rw [show R = (N : ℝ) ^ c from by rw [PrimeGaps.sieveTruncation, hc_def]]
  exact hstepA.trans (hstepB.trans hstepC)

/-- `gSum W z ≤ (∑_{0 < r < z, (r, W) = 1} μ r ^ 2 / g r) + 1`, the `+ 1` absorbing the boundary
term at `r = ⌊z⌋`. -/
theorem PrimeGaps.gSum_le_range_add_one (W : ℕ) (z : ℝ) (hz : 0 < z) :
    PrimeGaps.gSum W z ≤ (∑ r ∈ (Finset.range ⌈z⌉₊).filter
            (fun r : ℕ ↦ 0 < r ∧ (r : ℝ) < z ∧ Nat.Coprime r W),
            (μ r : ℝ) ^ 2 / (g r : ℝ)) + 1 := by
  have hmu2 : ∀ n : ℕ, (μ n : ℝ) ^ 2 = if Squarefree n then 1 else 0 :=
    fun n ↦ by rw [← Int.cast_pow, ArithmeticFunction.moebius_sq]; split_ifs <;> norm_num
  have hbdd_term : ∀ m : ℕ, (μ m : ℝ) ^ 2 / (g m : ℝ) ≤ 1 := fun m ↦ by
    rcases Nat.eq_zero_or_pos (g m) with hg | hg
    · simp [hg]
    · refine div_le_one_of_le₀ ?_ (by positivity)
      rw [hmu2]
      split_ifs
      · exact_mod_cast hg
      · positivity
  have hgSum_eq : PrimeGaps.gSum W z = ∑ n ∈ {n ∈ (Finset.Icc 1 ⌊z⌋₊) | Nat.Coprime n W},
            (μ n : ℝ) ^ 2 / (g n : ℝ) := by
    rw [PrimeGaps.gSum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [hmu2]
    by_cases hcop : Nat.Coprime n W
    · by_cases hsf : Squarefree n
      · rw [if_pos ⟨hsf, hcop⟩, if_pos hcop, if_pos hsf]
      · rw [if_neg fun h ↦ hsf h.1, if_pos hcop, if_neg hsf, zero_div]
    · rw [if_neg fun h ↦ hcop h.2, if_neg hcop]
  have hBA : (Finset.range ⌈z⌉₊).filter (fun r : ℕ ↦ 0 < r ∧ (r : ℝ) < z ∧ Nat.Coprime r W)
        ⊆ {n ∈ (Finset.Icc 1 ⌊z⌋₊) | Nat.Coprime n W} := fun r hr ↦ by
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hr ⊢
    exact ⟨⟨hr.2.1, Nat.le_floor hr.2.2.1.le⟩, hr.2.2.2⟩
  have hAB_sub : {n ∈ (Finset.Icc 1 ⌊z⌋₊) | Nat.Coprime n W}
        \ ((Finset.range ⌈z⌉₊).filter (fun r : ℕ ↦ 0 < r ∧ (r : ℝ) < z ∧ Nat.Coprime r W))
        ⊆ {⌊z⌋₊} := fun n hn ↦ by
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range,
      Finset.mem_singleton] at hn ⊢
    obtain ⟨⟨⟨hn1, hnfl⟩, hncop⟩, hnB⟩ := hn
    by_contra hne
    have hnlt : n < ⌊z⌋₊ := hnfl.lt_of_ne hne
    exact hnB ⟨hnlt.trans_le (Nat.floor_le_ceil z), hn1,
      (Nat.cast_lt.mpr hnlt).trans_le (Nat.floor_le hz.le), hncop⟩
  rw [hgSum_eq, ← Finset.sum_sdiff hBA]
  have hbd := (Finset.sum_le_sum_of_subset_of_nonneg (f := fun n : ℕ ↦
    (μ n : ℝ) ^ 2 / (g n : ℝ)) hAB_sub fun i _ _ ↦ by positivity).trans
    ((Finset.sum_singleton _ ⌊z⌋₊).le.trans (hbdd_term _))
  linarith

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- `gSum (W N) R ≤ Cg * φ (W N) / W N * log R` for some `Cg ≥ 0` and all large `N`, when
`δ < θ / 2`. -/
theorem PrimeGaps.gSum_le (θ δ : ℝ) (hδθ : δ < θ / 2) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
      PrimeGaps.gSum (W N) R ≤ Cg * ((W N).totient : ℝ) / (W N : ℝ) * Real.log R := by
  have hcpos : (0 : ℝ) < θ / 2 - δ := by linarith
  have hδ' : (θ / 2 - δ) ∈ Set.Ioo (0 : ℝ) ((2 * θ - 4 * δ) / 2) := ⟨hcpos, by linarith⟩
  have hReq : ∀ M : ℕ, (M : ℝ) ^ ((2 * θ - 4 * δ) / 2 - (θ / 2 - δ)) =
        (M : ℝ) ^ (θ / 2 - δ) := fun M ↦ congrArg (fun x : ℝ ↦ (M : ℝ) ^ x) (by ring)
  obtain ⟨Cc, hCcpos, N₀g, hgc⟩ := lem_S2m_g_coord (θ / 2 - δ) (2 * θ - 4 * δ) hδ'
  obtain ⟨N₂, -, hF2⟩ :=
    MaynardOffDiagonal.phi_logRval_ge_one_of_large (2 * θ - 4 * δ) (θ / 2 - δ) hδ'
  have hGmax : Gmax (fun _ : ℝ ↦ (1 : ℝ)) = 1 := by
    have : Nonempty ↥(Set.Icc (0 : ℝ) 1) := ⟨⟨0, by norm_num⟩⟩
    simp [Gmax]
  obtain ⟨x2, h2R⟩ := two_le_R (θ / 2 - δ) (2 * θ - 4 * δ) hδ'
  obtain ⟨xd, hxd⟩ := Filter.eventually_atTop.mp eventually_D0_le_log
  have hlittle : ∀ᶠ y : ℝ in Filter.atTop, Real.log y ≤ (θ / 2 - δ) * y := by
    filter_upwards [Real.isLittleO_log_id_atTop.def hcpos, Filter.eventually_ge_atTop (1 : ℝ)]
      with y hy hy1
    rwa [Real.norm_of_nonneg (Real.log_nonneg hy1), id,
      Real.norm_of_nonneg (zero_le_one.trans hy1)] at hy
  obtain ⟨xl, hxl⟩ := Filter.eventually_atTop.mp (Real.tendsto_log_atTop.eventually hlittle)
  have hint1 : (∫ _ in (0 : ℝ)..1, (1 : ℝ)) = 1 := by simp
  refine ⟨2 + 2 * Cc, by positivity,
    max (max N₀g N₂) (max (max x2 xd) (max xl (rexp (rexp (rexp 2))))), fun N hN ↦ ?_⟩
  simp only [max_le_iff] at hN
  obtain ⟨⟨hN0g, hN2⟩, ⟨hNx2, hNxd⟩, hNxl, hNe⟩ := hN
  have hNposR : (0 : ℝ) < (N : ℝ) := (Real.exp_pos _).trans_le hNe
  have hNpos : 0 < N := by exact_mod_cast hNposR
  have hD : 2 ≤ PrimeGaps.D₀ (N : ℝ) := MaynardOffDiagonal.two_le_D0_of_large hNe
  have hD₀pos : (0 : ℝ) < PrimeGaps.D₀ (N : ℝ) := by linarith
  have hR2 : 2 ≤ R := by
    simpa only [PrimeGaps.sieveTruncation, hReq N] using h2R N hNx2
  have hlogR_pos : 0 < Real.log R := Real.log_pos (by linarith)
  have hρ : 0 ≤ ((W N).totient : ℝ) / (W N : ℝ) := by positivity
  have hF2' : (1 : ℝ) ≤ ((W N).totient : ℝ) / (W N : ℝ) * Real.log R := by
    have h := hF2 (N : ℝ) hN2
    rwa [show (2 * θ - 4 * δ) / 2 - (θ / 2 - δ) = θ / 2 - δ from by ring,
      ← PrimeGaps.W_eq_primorial_D₀] at h
  have hF1 : Real.log (PrimeGaps.D₀ (N : ℝ)) ≤ Real.log R := by
    rw [Real.log_rpow hNposR]
    exact (Real.log_le_log hD₀pos (hxd (N : ℝ) hNxd)).trans (hxl (N : ℝ) hNxl)
  have hgc0 := hgc N hN0g hNpos hD (fun _ : ℝ ↦ (1 : ℝ)) contDiff_const
  simp only [PrimeGaps.sieveTruncation, hReq N, mul_one, hGmax, hint1, abs_one] at hgc0
  have hgcbound : (∑ r ∈ (Finset.range ⌈R⌉₊).filter
          (fun r : ℕ ↦ 0 < r ∧ (r : ℝ) < R ∧ Nat.Coprime r (W N)),
          (μ r : ℝ) ^ 2 / (g r : ℝ)) ≤
        ((W N).totient : ℝ) / (W N : ℝ) * Real.log R + Cc * (((W N).totient : ℝ) / (W N : ℝ)) *
              (Real.log R / PrimeGaps.D₀ (N : ℝ) + Real.log (PrimeGaps.D₀ (N : ℝ))) := by
    linarith [(abs_le.mp hgc0).2]
  have hbdry := PrimeGaps.gSum_le_range_add_one (W N) R (by linarith)
  have hLD : ((W N).totient : ℝ) / (W N : ℝ) * (Real.log R / PrimeGaps.D₀ (N : ℝ)) ≤
      ((W N).totient : ℝ) / (W N : ℝ) * Real.log R := by
    refine mul_le_mul_of_nonneg_left ?_ hρ
    rw [div_le_iff₀ hD₀pos]
    exact le_mul_of_one_le_right hlogR_pos.le (by linarith only [hD])
  have hLlogD : ((W N).totient : ℝ) / (W N : ℝ) * Real.log (PrimeGaps.D₀ (N : ℝ)) ≤
      ((W N).totient : ℝ) / (W N : ℝ) * Real.log R :=
    mul_le_mul_of_nonneg_left hF1 hρ
  rw [mul_div_assoc]
  linarith only [hbdry, hgcbound, hF2', mul_le_mul_of_nonneg_left hLD hCcpos.le,
    mul_le_mul_of_nonneg_left hLlogD hCcpos.le]

/-- `sumA W X ≤ gSum W X` for even `W`, since `g p = p - 2 ≤ p - 1 = φ p` at the odd primes. -/
theorem PrimeGaps.sumA_le_gSum (W : ℕ) (X : ℝ) (hW : 2 ∣ W) :
    PrimeGaps.MaynardOffDiagonal.sumA W X ≤ PrimeGaps.gSum W X := by
  rw [PrimeGaps.sumA_eq_ite_sum, PrimeGaps.gSum]
  refine Finset.sum_le_sum fun n hn ↦ ?_
  by_cases hguard : Squarefree n ∧ n.Coprime W
  · rw [if_pos hguard, if_pos hguard]
    obtain ⟨hsqf, hcop⟩ := hguard
    have hp3 : ∀ p ∈ n.primeFactors, (3 : ℝ) ≤ (p : ℝ) := fun p hp ↦ by
      obtain ⟨hpp, hpdvd, -⟩ := Nat.mem_primeFactors.mp hp
      have hp2 := hpp.two_le
      have hpne2 : p ≠ 2 := by
        rintro rfl
        simpa using Nat.eq_one_of_dvd_coprimes hcop hpdvd hW
      exact_mod_cast show 3 ≤ p by omega
    have hgprodR := ArithmeticFunction.coe_detotient_squarefree_eq_prod (R := ℝ) hsqf
    refine one_div_le_one_div_of_le ?_ ?_
    · rw [hgprodR]
      exact Finset.prod_pos fun p hp ↦ by linarith [hp3 p hp]
    · rw [hgprodR, PrimeGaps.totient_eq_prod_sub_one n (Finset.mem_Icc.mp hn).1 hsqf]
      exact Finset.prod_le_prod (fun p hp ↦ by linarith [hp3 p hp])
        fun p hp ↦ by linarith [hp3 p hp]
  · rw [if_neg hguard, if_neg hguard]
