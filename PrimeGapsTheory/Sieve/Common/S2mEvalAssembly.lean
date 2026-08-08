/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Variational.Marginal.PinCoordReindex
public import PrimeGapsTheory.Variational.Marginal.YdiscApprox

/-!
# Second-moment evaluation identities

Collects reindexing, vanishing, and comparison identities for the second-moment evaluation.

## Main results

* `decoupledSum_reindex`: Reindexes the pinned decoupled sum over its free coordinates.
* `M_eq_sieveE`: Identifies the second-moment summand with the sieve-datum summand.
* `sieveE_Tm_zero`: Shows the summand vanishes when a coordinate is outside the simplex.
-/

@[expose] public section

open scoped ArithmeticFunction.Moebius


open scoped ArithmeticFunction.detotient


namespace PrimeGaps

open MeasureTheory

variable {n : ℕ}

/-- The common scale of the first and second sieve moments. -/
noncomputable def mainScale (k N : ℕ) (R : ℝ) (W : ℕ) : ℝ :=
  (W.totient : ℝ) ^ k * (N : ℝ) * Real.log R ^ k / (W : ℝ) ^ (k + 1)

/-- The standard `D₀⁻¹` second-moment error scale for a norm bound `M`. -/
noncomputable def secondMomentErrorScale (k N : ℕ) (R : ℝ) (W : ℕ) (M : ℝ) : ℝ :=
  M ^ 2 * (W.totient : ℝ) ^ k * (N : ℝ) * Real.log R ^ k / ((W : ℝ) ^ (k + 1) * D₀ (N : ℝ))

/-- The normalized second-moment main term attached to an `L²` profile. -/
noncomputable def profileSecondMomentMainTerm {k : ℕ} (N : ℕ) (R : ℝ) (W : ℕ)
    (m : Fin k) (P : Lp ℝ 2 (volume.restrict (𝓡 k))) : ℝ :=
  (W.totient : ℝ) ^ k * (N : ℝ) * Real.log R ^ (k + 1) / ((W : ℝ) ^ (k + 1) * Real.log N) * J m P

/-- The combined `D₀⁻¹` error scale for a base norm and a profile norm. -/
noncomputable def profileSecondMomentErrorScale {k : ℕ} (N : ℕ) (R : ℝ) (W : ℕ)
    (M : ℝ) (P : EuclideanSpace ℝ (Fin k) → ℝ) : ℝ :=
  (M ^ 2 + MaynardSmoothY.Fmax P ^ 2) * (W.totient : ℝ) ^ k * (N : ℝ) *
      Real.log R ^ k / ((W : ℝ) ^ (k + 1) * D₀ (N : ℝ))

/-- A single-norm second-moment error is bounded by the corresponding combined profile error. -/
theorem secondMomentErrorScale_le_profileSecondMomentErrorScale {k N W : ℕ}
    {R M : ℝ} (P : EuclideanSpace ℝ (Fin k) → ℝ)
    (hlogR : 0 ≤ Real.log R) (hD₀ : 0 ≤ D₀ (N : ℝ)) :
    secondMomentErrorScale k N R W M ≤ profileSecondMomentErrorScale N R W M P := by
  unfold secondMomentErrorScale profileSecondMomentErrorScale
  have hs : M ^ 2 ≤ M ^ 2 + MaynardSmoothY.Fmax P ^ 2 := by
    nlinarith [sq_nonneg (MaynardSmoothY.Fmax P)]
  gcongr

/-- The diagonal-removal component of the transformed-weight error. -/
noncomputable def weightedDiagonalErrorScale {k : ℕ} (C : ℝ) (N W : ℕ) (U : ℝ) : ℝ :=
  C * U ^ 2 * (W.totient : ℝ) ^ (k - 2) * (N : ℝ) * Real.log N ^ (k - 2) /
      ((W : ℝ) ^ (k - 1) * D₀ (N : ℝ))

/-- The combined diagonal-removal and finite-support transformed-weight error scale. -/
noncomputable def fromYmErrorScale {k : ℕ} (A C : ℝ) (N W : ℕ) (U Y : ℝ) : ℝ :=
  weightedDiagonalErrorScale (k := k) C N W U + C * Y ^ 2 * (N : ℝ) / Real.log N ^ A

/-- Error scale for approximating an inverse diagonal form at radius `R` and modulus `W`. -/
noncomputable def inverseDiagonalApproxErrorScale (k : ℕ) (C R : ℝ) (W : ℕ) (M D : ℝ) : ℝ :=
  C * M ^ 2 * (W.totient : ℝ) ^ (k + 1) * Real.log R ^ (k + 1) / ((W : ℝ) ^ (k + 1) * D)

/-- The error scale is nonnegative once `0 ≤ C`, `0 ≤ log R` and `0 ≤ D`. -/
theorem inverseDiagonalApproxErrorScale_nonneg (k : ℕ) (C R : ℝ)
    (W : ℕ) (M D : ℝ) (hC : 0 ≤ C) (hlog : 0 ≤ Real.log R) (hD : 0 ≤ D) :
    0 ≤ inverseDiagonalApproxErrorScale k C R W M D := by
  unfold inverseDiagonalApproxErrorScale
  positivity

/-- `decoupledSum` (via `decoupledSum_eq_sq_sum`) equals the `n` -fold sum over the free
coordinates `σ: Fin n → ℕ`, with the pinned coordinate `m` removed.
-/
theorem decoupledSum_reindex (R : ℝ) (W : ℕ) (hR : 1 < R)
    (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (hsupp : Function.support F ⊆ 𝓡 (n + 1))
    (m : Fin (n + 1)) :
    decoupledSum R W F m = ∑' σ : Fin n → ℕ, if (∀ j, (σ j).Coprime W ∧ Squarefree (σ j)) then
            (∏ j, (1 : ℝ) / (g (σ j) : ℝ)) * (Ydisc R W F m (Fin.insertNth m 1 σ)) ^ 2
          else 0 := by
  classical
  rw [decoupledSum_eq_sq_sum R W hR F hsupp m]
  have hsplit : ∀ ρ : Fin (n + 1) → ℕ,
      (if (ρ m = 1 ∧ ∀ i, i ≠ m → (ρ i).Coprime W ∧ Squarefree (ρ i)) then
          (∏ i ∈ Finset.univ.erase m, (1 : ℝ) / (g (ρ i) : ℝ)) * (Ydisc R W F m ρ) ^ 2
        else 0) = if ρ m = 1 then
          (if (∀ i, i ≠ m → (ρ i).Coprime W ∧ Squarefree (ρ i)) then
            (∏ i ∈ Finset.univ.erase m, (1 : ℝ) / (g (ρ i) : ℝ)) * (Ydisc R W F m ρ) ^ 2
          else 0)
        else 0 := by
    intro ρ
    by_cases h1 : ρ m = 1
    · by_cases h2 : ∀ i, i ≠ m → (ρ i).Coprime W ∧ Squarefree (ρ i)
      · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2]
      · rw [if_neg (fun h ↦ h2 h.2), if_pos h1, if_neg h2]
    · rw [if_neg (fun h ↦ h1 h.1), if_neg h1]
  rw [tsum_congr hsplit, tsum_pin_coord_one m (fun ρ ↦
      if (∀ i, i ≠ m → (ρ i).Coprime W ∧ Squarefree (ρ i)) then
        (∏ i ∈ Finset.univ.erase m, (1 : ℝ) / (g (ρ i) : ℝ)) * (Ydisc R W F m ρ) ^ 2
      else 0)]
  apply tsum_congr
  intro σ
  set ρ : Fin (n + 1) → ℕ := Fin.insertNth m 1 σ with hρdef
  have hsucc : ∀ j : Fin n, ρ (m.succAbove j) = σ j := by
    intro j; rw [hρdef, Fin.insertNth_apply_succAbove]
  have hguard : (∀ i, i ≠ m → (ρ i).Coprime W ∧ Squarefree (ρ i)) ↔
      (∀ j, (σ j).Coprime W ∧ Squarefree (σ j)) := by
    constructor
    · intro h j
      have := h (m.succAbove j) (Fin.succAbove_ne m j)
      rwa [hsucc] at this
    · intro h i hi
      obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
      rw [hsucc]; exact h j
  have hweight : (∏ i ∈ Finset.univ.erase m,
        (1 : ℝ) / (g (ρ i) : ℝ)) = ∏ j, (1 : ℝ) / (g (σ j) : ℝ) := by
    rw [prod_erase_eq_prod_succAbove m (fun i ↦ (1 : ℝ) / (g (ρ i) : ℝ))]
    apply Finset.prod_congr rfl
    intro j _; rw [hsucc]
  by_cases h : ∀ j, (σ j).Coprime W ∧ Squarefree (σ j)
  · rw [if_pos (hguard.mpr h), if_pos h, hweight]
  · rw [if_neg (fun hh ↦ h (hguard.mp hh)), if_neg h]

open scoped PrimeGaps.sieveModulus in
/-- Pointwise value of the `maynardSieveDatum` weight: `S.h d = μ(d)²/g(d)` for `d` coprime to
`W N`, else `0`.
-/
theorem S2m_h_eq (N : ℕ) (hN : 0 < N) (hD : 2 ≤ PrimeGaps.D₀ (N : ℝ)) (d : ℕ) :
    (maynardSieveDatum N hN hD).h d = if Nat.Coprime d (W N) then
          (μ d : ℝ) ^ 2 / (g d : ℝ)
        else 0 := by
  change (μ d : ℝ) ^ 2 * (maynardSieveDatum N hN hD).gStar d = _
  by_cases hcop : Nat.Coprime d (W N)
  · rw [if_pos hcop]
    by_cases hsf : Squarefree d
    · rw [maynardSieveDatum_gStar_squarefree_coprime N hN hD d hsf hcop,
        show (μ d : ℝ) ^ 2 = 1 by
          exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf]
      ring
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]; push_cast; ring
  · rw [if_neg hcop]
    by_cases hsf : Squarefree d
    · rw [maynardSieveDatum_gStar_not_coprime N hN hD d hsf hcop]; ring
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]; push_cast; ring

open scoped PrimeGaps.sieveModulus in
/-- `S.h d = 1/φ?` — the `μ²/g` weight simplifies to `1/g` on the `coprime ∧ squarefree` set, and
is `0` off it.
-/
theorem S2m_h_eq' (N : ℕ) (hN : 0 < N) (hD : 2 ≤ PrimeGaps.D₀ (N : ℝ)) (d : ℕ) :
    (maynardSieveDatum N hN hD).h d = if (d.Coprime (W N) ∧ Squarefree d) then
          (1 : ℝ) / (g d : ℝ) else 0 := by
  rw [S2m_h_eq N hN hD d]
  by_cases hcs : d.Coprime (W N) ∧ Squarefree d
  · rw [if_pos hcs.1, if_pos hcs,
      show (μ d : ℝ) ^ 2 = 1 by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hcs.2]
  · rw [if_neg hcs]
    by_cases hcop : d.Coprime (W N)
    · rw [if_pos hcop]
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree fun h ↦ hcs ⟨hcop, h⟩]
      push_cast; ring
    · rw [if_neg hcop]

open scoped PrimeGaps.sieveModulus in
/-- The reindexed main sum (weight `∏ 1/g`, profile `Tm²`) equals the density-agnostic `sieveE` at
the Maynard (γ_g) datum.
-/
theorem M_eq_sieveE (N : ℕ) (R : ℝ) (hN : 0 < N) (hD : 2 ≤ PrimeGaps.D₀ (N : ℝ))
    (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hsupp : Function.support F ⊆ 𝓡 (n + 1)) (m : Fin (n + 1)) :
    (∑' σ : Fin n → ℕ, if (∀ j, (σ j).Coprime (W N) ∧ Squarefree (σ j)) then
          (∏ j, (1 : ℝ) / (g (σ j) : ℝ)) * (Tm m F (sigmaPt R σ)) ^ 2
        else 0) =
      sieveE (maynardSieveDatum N hN hD) R (Tm m F) n := by
  classical
  rw [sieveE_full (maynardSieveDatum N hN hD) R (Tm m F) (Tm_support m F hsupp)]
  apply tsum_congr
  intro σ
  set S := maynardSieveDatum N hN hD with hSdef
  set z := R with hzdef
  have hTmpt : Tm m F (WithLp.toLp 2 (fun i ↦ Real.log (σ i) / Real.log z)) =
      Tm m F (sigmaPt z σ) := rfl
  rw [hTmpt]
  by_cases hgood : ∀ j, (σ j).Coprime (W N) ∧ Squarefree (σ j)
  · have h1 : ∀ i, 1 ≤ σ i :=
      fun i ↦ Nat.pos_of_ne_zero (fun h ↦ not_squarefree_zero (h ▸ (hgood i).2))
    rw [if_pos h1, if_pos hgood]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    rw [hSdef, S2m_h_eq' N hN hD (σ j), if_pos (hgood j)]
  · rw [if_neg hgood]
    by_cases h1 : ∀ i, 1 ≤ σ i
    · rw [if_pos h1]
      have hzero : (∏ i, S.h (σ i)) = 0 := by
        push Not at hgood
        obtain ⟨j, hj⟩ := hgood
        apply Finset.prod_eq_zero (Finset.mem_univ j)
        rw [hSdef, S2m_h_eq' N hN hD (σ j), if_neg (fun h ↦ hj h.1 h.2)]
      rw [hzero, zero_mul]
    · rw [if_neg h1]

/-- `F (EuclideanSpace.insertLp m s t) = 0` when a free coordinate `t j ≥ 1` (off the simplex,
or on the `∑ = 1` boundary face).
-/
theorem F_insertLp_zero_of_coord_ge_one (m : Fin (n + 1))
    (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hsupp : Function.support F ⊆ 𝓡 (n + 1)) (t : EuclideanSpace ℝ (Fin n)) {j : Fin n}
    (hj : 1 ≤ t j) (s : ℝ) :
    F (EuclideanSpace.insertLp m s t) = 0 := by
  by_cases hmem : EuclideanSpace.insertLp m s t ∈ 𝓡 (n + 1)
  · have hmem' := hmem
    rw [EuclideanSpace.mem_scaledStdSimplex_iff] at hmem
    obtain ⟨hnn, hsum⟩ := hmem
    have hcoord : (EuclideanSpace.insertLp m s t).ofLp (m.succAbove j) = t j := by
      unfold EuclideanSpace.insertLp; rw [WithLp.ofLp_toLp, Fin.insertNth_apply_succAbove]
    have hge : t j ≤ ∑ i, (EuclideanSpace.insertLp m s t).ofLp i := by
      have hle := Finset.single_le_sum
        (f := fun i ↦ (EuclideanSpace.insertLp m s t).ofLp i) (fun i _ ↦ hnn i)
        (Finset.mem_univ (m.succAbove j))
      rwa [hcoord] at hle
    have hsum1 : ∑ i, (EuclideanSpace.insertLp m s t).ofLp i = 1 := le_antisymm hsum (by linarith)
    exact S1_boundary_vanish F hF hsupp hmem' (Or.inr hsum1)
  · by_contra hne
    exact hmem (hsupp (Function.mem_support.mpr hne))

/-- `Tm m F t = 0` when a free coordinate `t j ≥ 1`. -/
theorem Tm_vanish_coord (m : Fin (n + 1)) (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hsupp : Function.support F ⊆ 𝓡 (n + 1))
    (t : EuclideanSpace ℝ (Fin n)) {j : Fin n} (hj : 1 ≤ t j) :
    Tm m F t = 0 := by
  unfold Tm
  rw [MeasureTheory.integral_eq_zero_of_ae]
  exact Filter.Eventually.of_forall (fun s ↦ F_insertLp_zero_of_coord_ge_one m F hF hsupp t hj s)

/-- `Ydisc` at `insertNth m 1 σ` vanishes when a free coordinate `σj ≥ ⌈R⌉` (so `σ̃ j ≥ 1`). -/
theorem Ydisc_vanish_coord (R : ℝ) (W : ℕ) (m : Fin (n + 1))
    (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hsupp : Function.support F ⊆ 𝓡 (n + 1)) (hR : 1 < R)
    (σ : Fin n → ℕ) {j : Fin n} (hj : ⌈R⌉₊ ≤ σ j) :
    Ydisc R W F m (Fin.insertNth m 1 σ) = 0 := by
  set z := R with hzdef
  have hz0 : (0 : ℝ) < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos hR
  have htj : 1 ≤ (sigmaPt z σ) j := by
    rw [sigmaPt]
    have hσj : (z : ℝ) ≤ (σ j : ℝ) :=
      le_trans (Nat.le_ceil z) (by exact_mod_cast hj)
    change 1 ≤ Real.log (σ j) / Real.log z
    rw [le_div_iff₀ hlogz, one_mul]
    exact Real.log_le_log hz0 hσj
  have key : ∀ u : ℕ, (if (u.Coprime W ∧ Squarefree u) then
        (1 / (u.totient : ℝ)) * F (WithLp.toLp 2 (fun i ↦ Real.log
              ((Function.update (Fin.insertNth m (1 : ℕ) σ : Fin (n + 1) → ℕ) m u) i : ℝ) /
              Real.log z)) else 0) = 0 := by
    intro u
    by_cases hu : u.Coprime W ∧ Squarefree u
    · rw [if_pos hu, F_update_eq_Gsigma m F z σ u]
      have hzero : Gsigma m F z σ (Real.log u / Real.log z) = 0 := by
        unfold Gsigma
        exact F_insertLp_zero_of_coord_ge_one m F hF hsupp (sigmaPt z σ) htj _
      rw [hzero, mul_zero]
    · rw [if_neg hu]
  unfold Ydisc
  rw [tsum_congr key, tsum_zero]

/-- `sieveE (γ_g) z (Tm m F) 0 = (𝔖 · log z)^n · J_k^{(m)}(F)`. -/
theorem sieveE_Tm_zero (N : ℕ) (R : ℝ) (hN : 0 < N) (hD : 2 ≤ PrimeGaps.D₀ (N : ℝ))
    (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (hsupp : Function.support F ⊆ 𝓡 (n + 1))
    (m : Fin (n + 1))
    (hmem : MemLp F 2 (volume.restrict (𝓡 (n + 1)))) :
    sieveE (maynardSieveDatum N hN hD) R (Tm m F) 0 =
      (PrimeGaps.singularSeries (maynardSieveDatum N hN hD).γ *
            Real.log R) ^ n * PrimeGaps.J m (hmem.toLp _) := by
  rw [sieveE_zero (maynardSieveDatum N hN hD) R (Tm m F)
    (Tm_support m F hsupp), Tm_sq_integral_eq_J m F hsupp hmem]

end PrimeGaps
