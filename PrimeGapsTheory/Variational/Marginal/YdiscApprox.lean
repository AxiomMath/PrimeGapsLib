/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.S1.ApplyPartialSum
public import PrimeGapsTheory.Variational.Marginal.DecoupledSeparate
public import PrimeGapsTheory.Variational.Marginal.Infra

/-!
# Approximation of the inner sum `Ydisc`

Evaluates the one-dimensional inner sum `Ydisc` uniformly in its free coordinates.

## Main definitions

*  `sigmaPt`: The logarithmically normalized free-coordinate point.
*  `Gsigma`: The one-dimensional profile obtained by freezing the free coordinates.

## Main results

*  `Ydisc_approx`: Approximates `Ydisc` by the marginal profile with a uniform error bound.
-/

@[expose] public section

open scoped ArithmeticFunction.Moebius
open scoped Finset
open scoped Topology


namespace PrimeGaps

open MeasureTheory EuclideanSpace

variable {n : ℕ}

/-- Evaluation point of the free coordinates `σ`. -/
noncomputable def sigmaPt (z : ℝ) (σ : Fin n → ℕ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j ↦ Real.log (σ j) / Real.log z)

/-- The one-dimensional profile: `F` with the free coordinates frozen at `σ̃` and the isolated
coordinate `m` carrying the running scalar `s`. -/
noncomputable def Gsigma (m : Fin (n + 1)) (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (z : ℝ)
    (σ : Fin n → ℕ) : ℝ → ℝ :=
  fun s ↦ F (insertLp m s (sigmaPt z σ))

/-- The `Ydisc` summand's point (`update (insertNth m 1 σ) m u`) coincides with
`insertLp m (log u / log z) σ̃`, so the `F` -value is `Gσ (log u / log z)`. -/
theorem F_update_eq_Gsigma (m : Fin (n + 1)) (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (z : ℝ)
    (σ : Fin n → ℕ) (u : ℕ) :
    F (WithLp.toLp 2 (fun i ↦
        Real.log ((Function.update (Fin.insertNth m (1 : ℕ) σ : Fin (n + 1) → ℕ) m u) i : ℝ) /
          Real.log z)) = Gsigma m F z σ (Real.log u / Real.log z) := by
  have hfun : (fun i ↦
      Real.log ((Function.update (Fin.insertNth m (1 : ℕ) σ : Fin (n + 1) → ℕ) m u) i : ℝ) /
        Real.log z) =
      m.insertNth (Real.log u / Real.log z) (fun j ↦ Real.log (σ j) / Real.log z) := by
    funext i
    refine Fin.succAboveCases m ?_ ?_ i
    · rw [Function.update_self, Fin.insertNth_apply_same]
    · intro j
      rw [Function.update_of_ne (Fin.succAbove_ne m j),
          Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
  unfold Gsigma insertLp sigmaPt
  rw [WithLp.ofLp_toLp]
  exact congrArg F (congrArg (WithLp.toLp 2) hfun)

/-- `s ↦ insertLp m s t` is smooth (it is affine in `s` ). -/
theorem contDiff_insertLp_fixed (m : Fin (n + 1)) (t : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ ↦ insertLp m s t) := by
  have h := contDiff_insertLp_neg (n := n) m
  have hcomp : (fun s : ℝ ↦ insertLp m s t) =
      (fun p : EuclideanSpace ℝ (Fin n) × ℝ ↦ insertLp m (-p.2) p.1)
        ∘ (fun s : ℝ ↦ (t, -s)) := by
    funext s; simp
  rw [hcomp]
  exact h.comp (contDiff_const.prodMk contDiff_neg)

/-- `Gσ` is smooth (hence `ContDiff ℝ 1` ). -/
theorem Gsigma_contDiff (m : Fin (n + 1)) (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (z : ℝ) (σ : Fin n → ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (Gsigma m F z σ) :=
  hF.comp (contDiff_insertLp_fixed m (sigmaPt z σ))

/-- `Gσ` is uniformly bounded by `Fmax F`. -/
theorem Gsigma_abs_le_Fmax (m : Fin (n + 1)) (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hsupp : Function.support F ⊆ 𝓡 (n + 1)) (z : ℝ)
    (σ : Fin n → ℕ) (s : ℝ) :
    |Gsigma m F z σ s| ≤ MaynardSmoothY.Fmax F :=
  S1_abs_F_le_Fmax_global F hF hsupp _

/-- Coordinate `m` of `insertLp m s t` is `s`. -/
theorem insertLp_ofLp_same (m : Fin (n + 1)) (s : ℝ) (t : EuclideanSpace ℝ (Fin n)) :
    (insertLp m s t).ofLp m = s := by
  unfold insertLp
  rw [WithLp.ofLp_toLp, Fin.insertNth_apply_same]

/-- `Gσ` vanishes outside `Ioc 0 1`. -/
theorem Gsigma_vanish (m : Fin (n + 1)) (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hsupp : Function.support F ⊆ 𝓡 (n + 1)) (z : ℝ)
    (σ : Fin n → ℕ) {s : ℝ} (hs : s ∉ Set.Ioc (0 : ℝ) 1) :
    Gsigma m F z σ s = 0 := by
  unfold Gsigma
  by_cases hmem : insertLp m s (sigmaPt z σ) ∈ 𝓡 (n + 1)
  · have hmem' := hmem
    rw [EuclideanSpace.mem_scaledStdSimplex_iff] at hmem
    obtain ⟨hnn, hsum⟩ := hmem
    have hcm : (insertLp m s (sigmaPt z σ)).ofLp m = s := insertLp_ofLp_same m s (sigmaPt z σ)
    have h0 : 0 ≤ s := hcm ▸ hnn m
    have h1 : s ≤ 1 := by
      have hle := Finset.single_le_sum
        (f := fun i ↦ (insertLp m s (sigmaPt z σ)).ofLp i) (fun i _ ↦ hnn i) (Finset.mem_univ m)
      rw [hcm] at hle; linarith
    have hs0 : s = 0 := by
      rcases eq_or_lt_of_le h0 with h | h
      exacts [h.symm, absurd ⟨h, h1⟩ hs]
    exact S1_boundary_vanish F hF hsupp hmem' (Or.inl ⟨m, by rw [hcm, hs0]⟩)
  · by_contra hne
    exact hmem (hsupp (Function.mem_support.mpr hne))

/-- `Gσ` vanishes for `s ≥ 1`. -/
theorem Gsigma_vanish_ge_one (m : Fin (n + 1)) (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hsupp : Function.support F ⊆ 𝓡 (n + 1)) (z : ℝ)
    (σ : Fin n → ℕ) {s : ℝ} (hs : 1 ≤ s) :
    Gsigma m F z σ s = 0 := by
  unfold Gsigma
  by_cases hmem : insertLp m s (sigmaPt z σ) ∈ 𝓡 (n + 1)
  · have hmem' := hmem
    rw [EuclideanSpace.mem_scaledStdSimplex_iff] at hmem
    obtain ⟨hnn, hsum⟩ := hmem
    have hcm : (insertLp m s (sigmaPt z σ)).ofLp m = s := insertLp_ofLp_same m s (sigmaPt z σ)
    have hge : s ≤ ∑ i, (insertLp m s (sigmaPt z σ)).ofLp i := by
      have hle := Finset.single_le_sum
        (f := fun i ↦ (insertLp m s (sigmaPt z σ)).ofLp i) (fun i _ ↦ hnn i) (Finset.mem_univ m)
      rwa [hcm] at hle
    have hsum1 : ∑ i, (insertLp m s (sigmaPt z σ)).ofLp i = 1 := le_antisymm hsum (by linarith)
    exact S1_boundary_vanish F hF hsupp hmem' (Or.inr hsum1)
  · by_contra hne
    exact hmem (hsupp (Function.mem_support.mpr hne))

/-- `s ↦ insertLp m s t` is affine with slope `EuclideanSpace.single m 1`. -/
theorem insertLp_affine (m : Fin (n + 1)) (s : ℝ) (t : EuclideanSpace ℝ (Fin n)) :
    insertLp m s t = insertLp m 0 t + s • EuclideanSpace.single m (1 : ℝ) := by
  ext i
  refine Fin.succAboveCases m ?_ ?_ i
  · simp [insertLp_apply_same]
  · intro j
    simp [insertLp_apply_succAbove, (Fin.succAbove_ne m j)]

/-- Derivative of `Gσ`: the `m` -directional derivative of `F` at `insertLp m s σ̃`. -/
theorem Gsigma_hasDerivAt (m : Fin (n + 1)) (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (z : ℝ) (σ : Fin n → ℕ) (s : ℝ) :
    HasDerivAt (Gsigma m F z σ)
      (fderiv ℝ F (insertLp m s (sigmaPt z σ)) (EuclideanSpace.single m (1 : ℝ))) s := by
  have hlin : HasDerivAt (fun s : ℝ ↦ insertLp m s (sigmaPt z σ))
      (EuclideanSpace.single m (1 : ℝ)) s := by
    have h1 : HasDerivAt (fun s : ℝ ↦ s • EuclideanSpace.single m (1 : ℝ))
        (EuclideanSpace.single m (1 : ℝ)) s := by
      simpa using (hasDerivAt_id s).smul_const (EuclideanSpace.single m (1 : ℝ))
    have h2 := h1.const_add (insertLp m 0 (sigmaPt z σ))
    have haff : (fun s : ℝ ↦ insertLp m s (sigmaPt z σ)) =
        fun s : ℝ ↦ insertLp m 0 (sigmaPt z σ) + s • EuclideanSpace.single m (1 : ℝ) := by
      funext s; exact insertLp_affine m s (sigmaPt z σ)
    rw [haff]; exact h2
  have hFd : HasFDerivAt F (fderiv ℝ F (insertLp m s (sigmaPt z σ))) (insertLp m s (sigmaPt z σ)) :=
    (hF.differentiable (by simp)).differentiableAt.hasFDerivAt
  exact hFd.comp_hasDerivAt s hlin

/-- `Gmax Gσ ≤ Fmax F`. -/
theorem Gmax_Gsigma_le (m : Fin (n + 1)) (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hsupp : Function.support F ⊆ 𝓡 (n + 1)) (z : ℝ)
    (σ : Fin n → ℕ) :
    Gmax (Gsigma m F z σ) ≤ MaynardSmoothY.Fmax F := by
  have hFnn : 0 ≤ MaynardSmoothY.Fmax F := MaynardSmoothY.Fmax_nonneg F hF
  have hbdd := MaynardSmoothY.abs_F_bddAbove F hF
  have hpt : ∀ s : ℝ, |Gsigma m F z σ s| + |deriv (Gsigma m F z σ) s| ≤ MaynardSmoothY.Fmax F := by
    intro s
    set pt : EuclideanSpace ℝ (Fin (n + 1)) := insertLp m s (sigmaPt z σ) with hpt
    have hderiv : deriv (Gsigma m F z σ) s = fderiv ℝ F pt (EuclideanSpace.single m (1 : ℝ)) :=
      (Gsigma_hasDerivAt m F hF z σ s).deriv
    by_cases hin : ∀ i, pt i ∈ Set.Icc (0 : ℝ) 1
    · have hmem : |F pt| + ∑ i : Fin (n + 1), |fderiv ℝ F pt (EuclideanSpace.single i 1)| ∈
          ((fun w : EuclideanSpace ℝ (Fin (n + 1)) ↦
            |F w| + ∑ i, |fderiv ℝ F w (EuclideanSpace.single i 1)|) ''
            {w : EuclideanSpace ℝ (Fin (n + 1)) | ∀ i, w i ∈ Set.Icc (0 : ℝ) 1}) :=
          ⟨pt, hin, rfl⟩
      have hle : |F pt| + ∑ i, |fderiv ℝ F pt (EuclideanSpace.single i 1)| ≤
          MaynardSmoothY.Fmax F := le_csSup hbdd hmem
      have hsingle : |fderiv ℝ F pt (EuclideanSpace.single m (1 : ℝ))| ≤
          ∑ i, |fderiv ℝ F pt (EuclideanSpace.single i 1)| :=
        Finset.single_le_sum (f := fun i ↦ |fderiv ℝ F pt (EuclideanSpace.single i 1)|)
          (fun i _ ↦ abs_nonneg _) (Finset.mem_univ m)
      have hGeq : Gsigma m F z σ s = F pt := rfl
      rw [hderiv, hGeq]; linarith
    · have hptR : pt ∉ 𝓡 (n + 1) := by
        intro hR
        obtain ⟨hnn, hsum⟩ := EuclideanSpace.mem_scaledStdSimplex_iff.mp hR
        exact hin (fun i ↦ ⟨hnn i, le_trans (Finset.single_le_sum
          (f := fun j ↦ pt j) (fun j _ ↦ hnn j) (Finset.mem_univ i)) hsum⟩)
      have hFev : F =ᶠ[𝓝 pt] 0 := by
        refine Filter.eventuallyEq_of_mem
          ((isClosed_scaledStdSimplex.isOpen_compl).mem_nhds hptR) ?_
        intro w hw
        by_contra hne
        exact hw (hsupp (Function.mem_support.mpr hne))
      have hF0 : F pt = 0 := by simpa using hFev.eq_of_nhds
      have hfd0 : fderiv ℝ F pt = 0 := by
        rw [hFev.fderiv_eq]; simp
      have hGeq : Gsigma m F z σ s = F pt := rfl
      rw [hderiv, hGeq, hF0, hfd0]; simp [hFnn]
  refine ciSup_le ?_
  exact fun t ↦ hpt t.1

/-- The interval integral of `Gσ` is the marginal `Tm` at the frozen point `σ̃`. -/
theorem Gsigma_integral_eq_Tm (m : Fin (n + 1)) (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hsupp : Function.support F ⊆ 𝓡 (n + 1)) (z : ℝ)
    (σ : Fin n → ℕ) :
    ∫ x in (0 : ℝ)..1, Gsigma m F z σ x = Tm m F (sigmaPt z σ) := by
  have hTm : Tm m F (sigmaPt z σ) = ∫ s, Gsigma m F z σ s := rfl
  rw [hTm, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
  exact fun s hs ↦ Gsigma_vanish m F hF hsupp z σ hs

/-- At the reindexed argument, `Ydisc` equals the filtered sum with weight
`S.h u = μ²/φ · [coprime]` and profile `Gσ`. -/
theorem Ydisc_eq_filtered (R : ℝ) (W : ℕ) (m : Fin (n + 1))
    (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hsupp : Function.support F ⊆ 𝓡 (n + 1))
    (hR : 1 < R) (σ : Fin n → ℕ) (S : SieveDatum)
    (hSh : ∀ u : ℕ, S.h u = if (u.Coprime W ∧ Squarefree u) then (1 / (u.totient : ℝ)) else 0) :
    Ydisc R W F m (Fin.insertNth m 1 σ) = ∑ d ∈ (Finset.range ⌈R⌉₊).filter
            (fun d : ℕ ↦ 0 < d ∧ (d : ℝ) < R),
          S.h d * Gsigma m F R σ (Real.log d / Real.log R) := by
  set z := R with hz
  have hz0 : (0 : ℝ) < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos hR
  have hsummand : ∀ u : ℕ, (if (u.Coprime W ∧ Squarefree u) then (1 / (u.totient : ℝ)) *
          F (WithLp.toLp 2 (fun i ↦
              Real.log ((Function.update (Fin.insertNth m (1 : ℕ) σ : Fin (n + 1) → ℕ) m u) i : ℝ) /
              Real.log z)) else 0) = S.h u * Gsigma m F z σ (Real.log u / Real.log z) := by
    intro u
    rw [F_update_eq_Gsigma m F z σ u, hSh u]
    split <;> ring
  have hYd : Ydisc R W F m (Fin.insertNth m 1 σ) =
      ∑' u : ℕ, S.h u * Gsigma m F z σ (Real.log u / Real.log z) := by
    unfold Ydisc
    exact tsum_congr hsummand
  rw [hYd]
  apply tsum_eq_sum
  intro u hu
  rcases Nat.eq_zero_or_pos u with hu0 | hupos
  · subst hu0
    rw [hSh 0, if_neg (by rintro ⟨_, hsf⟩; exact not_squarefree_zero hsf), zero_mul]
  · have huz : z ≤ (u : ℝ) := by
      by_contra hlt
      push Not at hlt
      exact hu (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
        (by exact_mod_cast lt_of_lt_of_le hlt (Nat.le_ceil z)), hupos, hlt⟩)
    have hs1 : 1 ≤ Real.log u / Real.log z := by
      rw [le_div_iff₀ hlogz, one_mul]
      exact Real.log_le_log hz0 huz
    rw [Gsigma_vanish_ge_one m F hF hsupp z σ hs1, mul_zero]

-- For the γ_W datum, `Ydisc` at the reindexed argument equals `(φW/W)·log R·Tm σ̃`
-- up to `O((φW/W)·log D₀·Fmax)`, uniformly in `σ`.
open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- `Ydisc R (W N) F m (Fin.insertNth m 1 σ)` agrees with
`(φ(W N) / W N) * log R * Tm m F (sigmaPt R σ)` up to
`C * (φ(W N) / W N) * log (D₀ N) * Fmax F`, uniformly in the free coordinates `σ`. -/
theorem Ydisc_approx {n : ℕ} (δ θ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N → ∀ (_ : 0 < N) (_ : 2 ≤ PrimeGaps.D₀ (N : ℝ)),
      ∀ (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ), ContDiff ℝ (⊤ : ℕ∞) F →
        Function.support F ⊆ 𝓡 (n + 1) → ∀ (m : Fin (n + 1)) (σ : Fin n → ℕ),
        |Ydisc (R) (W N) F m (Fin.insertNth m 1 σ) - ((W N).totient : ℝ) /
          (W N : ℝ) * Real.log (R) * Tm m F (sigmaPt (R) σ)| ≤
        C * (((W N).totient : ℝ) / (W N : ℝ)) *
            Real.log (PrimeGaps.D₀ (N : ℝ)) * MaynardSmoothY.Fmax F := by
  classical
  obtain ⟨B₁, B₂, B₃, hB₁, hB₂, hB₃, hSharp⟩ := sharp_partial_sum
  obtain ⟨cP, hcP, xP, hPrime⟩ := ellV_W_le_const_log_D0
  obtain ⟨cB, hcB, xB, hRbdry⟩ := residual_boundary_le_const δ θ hδ
  obtain ⟨cI, hcI, xI, hRint⟩ := residual_integral_le_const δ θ hδ
  obtain ⟨x2, h2R⟩ := two_le_R δ θ hδ
  set B₁' : ℝ := B₁ (1 / 2) 0 with hB₁'def
  set B₂' : ℝ := B₂ (1 / 2) 0 with hB₂'def
  set B₃' : ℝ := B₃ (1 / 2) 0 with hB₃'def
  have hB₁'nn : 0 ≤ B₁' := hB₁ _ _
  have hB₂'nn : 0 ≤ B₂' := hB₂ _ _
  have hB₃'nn : 0 ≤ B₃' := hB₃ _ _
  set C : ℝ := B₁' * (1 / Real.log 2 + cP) + B₂' * cB + B₃' * cI with hCdef
  refine ⟨C, by positivity, max (max xP xB) (max xI x2), ?_⟩
  intro N hN₀ hN hD F hF hsupp m σ
  have hxP : xP ≤ (N : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN₀
  have hxB : xB ≤ (N : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN₀
  have hxI : xI ≤ (N : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN₀
  have hx2 : x2 ≤ (N : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN₀
  obtain ⟨S, hSγ, hSV, hSA₁, hSA₃⟩ := S1_WSieveDatum (W N) PrimeGaps.W_pos PrimeGaps.W_squarefree
  obtain ⟨h𝔖eq, hSh2, hSh3⟩ :=
    S1_datum_facts (W N) ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ (PrimeGaps.W_eq_primorial_D₀)
      S hSγ hSV
  set Wt : ℕ := W N with hWdef
  set Rt : ℝ := R with hRdef
  set ratio : ℝ := (Wt.totient : ℝ) / (Wt : ℝ) with hratiodef
  set D₀ : ℝ := PrimeGaps.D₀ (N : ℝ) with hD₀def
  set Fm : ℝ := MaynardSmoothY.Fmax F with hFmdef
  set G : ℝ → ℝ := Gsigma m F Rt σ with hGdef
  have hR2 : 2 ≤ Rt := h2R N hx2
  have hR1 : 1 < Rt := by linarith
  have hlogR_nn : 0 ≤ Real.log Rt := Real.log_nonneg (by linarith)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogD₀_ge : Real.log 2 ≤ Real.log D₀ :=
    Real.log_le_log (by norm_num) (by rw [hD₀def]; exact_mod_cast hD)
  have hlogD₀_nn : 0 ≤ Real.log D₀ := le_trans hlog2_pos.le hlogD₀_ge
  have h2D : (2 : ℝ) ≤ D₀ := by rw [hD₀def]; exact hD
  have hD₀pos : 0 < D₀ := by linarith
  have hratio_nn : 0 ≤ ratio := by rw [hratiodef]; positivity
  have hFm_nn : 0 ≤ Fm := MaynardSmoothY.Fmax_nonneg F hF
  have hg : Gmax G ≤ Fm := by rw [hGdef, hFmdef]; exact Gmax_Gsigma_le m F hF hsupp Rt σ
  have hgnn : 0 ≤ Gmax G := by
    rw [hGdef]; unfold Gmax; exact Real.iSup_nonneg (fun t ↦ by positivity)
  have hSh : ∀ u : ℕ, S.h u = if (u.Coprime Wt ∧ Squarefree u) then (1 /
        (u.totient : ℝ)) else 0 := by
    intro u
    rw [hWdef]
    by_cases hcs : u.Coprime (W N) ∧ Squarefree u
    · rw [if_pos hcs, hSh2 u hcs.2 hcs.1]
      have hμ : (μ u : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hcs.2
      rw [hμ]
    · rw [if_neg hcs, hSh3 u (fun h ↦ hcs ⟨h.2, h.1⟩)]
  rw [Ydisc_eq_filtered Rt Wt m F hF hsupp hR1 σ S hSh]
  have hsharp := hSharp S G ((Gsigma_contDiff m F hF Rt σ).of_le (by exact_mod_cast le_top)) Rt hR2
  have hInt : ∫ x in (0 : ℝ)..1, G x = Tm m F (sigmaPt Rt σ) := by
    rw [hGdef]; exact Gsigma_integral_eq_Tm m F hF hsupp Rt σ
  rw [h𝔖eq, hInt, hSV, hSA₁, hSA₃, ← hB₁'def, ← hB₂'def, ← hB₃'def] at hsharp
  refine le_trans hsharp ?_
  have hPrime' : ellV Wt ≤ cP * Real.log D₀ := by
    rw [hWdef, hD₀def]; exact hPrime N hxP hN hD
  have hterm1 : B₁' * ratio * (1 + ellV Wt) * Gmax G ≤
      B₁' * (1 / Real.log 2 + cP) * (ratio * Real.log D₀ * Fm) := by
    have h2 : 1 + ellV Wt ≤ Real.log D₀ * (1 / Real.log 2 + cP) := by
      have hone : (1 : ℝ) ≤ Real.log D₀ / Real.log 2 := (one_le_div hlog2_pos).mpr hlogD₀_ge
      have heq : Real.log D₀ * (1 / Real.log 2 + cP) =
          Real.log D₀ / Real.log 2 + cP * Real.log D₀ := by ring
      rw [heq]; linarith [hPrime']
    have hinv2 : (0 : ℝ) ≤ 1 / Real.log 2 := div_nonneg zero_le_one hlog2_pos.le
    have hcoef1_nn : (0 : ℝ) ≤ 1 / Real.log 2 + cP := add_nonneg hinv2 hcP
    have hc1 : 0 ≤ B₁' * ratio := mul_nonneg hB₁'nn hratio_nn
    calc B₁' * ratio * (1 + ellV Wt) * Gmax G
        ≤ B₁' * ratio * (Real.log D₀ * (1 / Real.log 2 + cP)) * Fm := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left h2 hc1) hg hgnn
          exact mul_nonneg hc1 (mul_nonneg hlogD₀_nn hcoef1_nn)
      _ = B₁' * (1 / Real.log 2 + cP) * (ratio * Real.log D₀ * Fm) := by ring
  have hRbdry' : (#Wt.divisors : ℝ) * Rt ^ ((-1 : ℝ) / 8) * Real.log (2 * (Wt : ℝ) * Rt) ≤
      cB * ratio * Real.log D₀ := by
    have hVR := hRbdry N hxB hN hD
    rw [maynardSieveDatum_V N hN hD] at hVR
    rw [← hWdef, ← hRdef, ← hratiodef, ← hD₀def] at hVR
    exact hVR
  have hterm2 : B₂' * (#Wt.divisors : ℝ) * Rt ^ ((-1 : ℝ) / 8) * Real.log (2 * (Wt : ℝ) * Rt) *
    Gmax G ≤ B₂' * cB * (ratio * Real.log D₀ * Fm) :=
    calc B₂' * (#Wt.divisors : ℝ) * Rt ^ ((-1 : ℝ) / 8) * Real.log (2 * (Wt : ℝ) * Rt) * Gmax G
        ≤ B₂' * (cB * ratio * Real.log D₀) * Fm := by
          apply mul_le_mul _ hg hgnn
            (mul_nonneg hB₂'nn (mul_nonneg (mul_nonneg hcB hratio_nn) hlogD₀_nn))
          calc B₂' * (#Wt.divisors : ℝ) * Rt ^ ((-1 : ℝ) / 8) * Real.log (2 * (Wt : ℝ) * Rt)
              = B₂' * ((#Wt.divisors : ℝ) * Rt ^ ((-1 : ℝ) / 8) * Real.log (2 * (Wt : ℝ) *
                Rt)) :=
                by ring
            _ ≤ B₂' * (cB * ratio * Real.log D₀) := mul_le_mul_of_nonneg_left hRbdry' hB₂'nn
      _ = B₂' * cB * (ratio * Real.log D₀ * Fm) := by ring
  have hRint' : (#Wt.divisors : ℝ) * Real.log (2 * (Wt : ℝ)) / Real.log Rt ≤
      cI * ratio * Real.log D₀ := by
    have hVR := hRint N hxI hN hD
    rw [maynardSieveDatum_V N hN hD] at hVR
    rw [← hWdef, ← hRdef, ← hratiodef, ← hD₀def] at hVR
    exact hVR
  have hterm3 : B₃' * (#Wt.divisors : ℝ) * Real.log (2 * (Wt : ℝ)) / Real.log Rt * Gmax G ≤
      B₃' * cI * (ratio * Real.log D₀ * Fm) :=
    calc B₃' * (#Wt.divisors : ℝ) * Real.log (2 * (Wt : ℝ)) / Real.log Rt * Gmax G
        ≤ B₃' * (cI * ratio * Real.log D₀) * Fm := by
          apply mul_le_mul _ hg hgnn
            (mul_nonneg hB₃'nn (mul_nonneg (mul_nonneg hcI hratio_nn) hlogD₀_nn))
          calc B₃' * (#Wt.divisors : ℝ) * Real.log (2 * (Wt : ℝ)) / Real.log Rt
              = B₃' * ((#Wt.divisors : ℝ) * Real.log (2 * (Wt : ℝ)) / Real.log Rt) := by ring
            _ ≤ B₃' * (cI * ratio * Real.log D₀) := mul_le_mul_of_nonneg_left hRint' hB₃'nn
      _ = B₃' * cI * (ratio * Real.log D₀ * Fm) := by ring
  rw [hCdef]
  calc B₁' * ratio * (1 + ellV Wt) * Gmax G +
        B₂' * (#Wt.divisors : ℝ) * Rt ^ ((-1 : ℝ) / 8) * Real.log (2 * (Wt : ℝ) * Rt) * Gmax G +
        B₃' * (#Wt.divisors : ℝ) * Real.log (2 * (Wt : ℝ)) / Real.log Rt * Gmax G ≤
      B₁' * (1 / Real.log 2 + cP) * (ratio * Real.log D₀ * Fm) +
        B₂' * cB * (ratio * Real.log D₀ * Fm) + B₃' * cI * (ratio * Real.log D₀ * Fm) :=
        add_le_add (add_le_add hterm1 hterm2) hterm3
    _ = (B₁' * (1 / Real.log 2 + cP) + B₂' * cB + B₃' * cI) * (ratio * Real.log D₀ * Fm) := by ring
    _ = (B₁' * (1 / Real.log 2 + cP) + B₂' * cB + B₃' * cI) * ratio * Real.log D₀ * Fm := by ring

end PrimeGaps
