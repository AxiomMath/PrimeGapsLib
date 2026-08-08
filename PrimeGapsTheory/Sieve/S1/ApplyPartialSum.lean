/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Arithmetic.GammaLogSum
public import PrimeGapsTheory.Arithmetic.Mertens.W
public import PrimeGapsTheory.Arithmetic.TdDecomposition
public import PrimeGapsTheory.Sieve.Common.SieveDatumEval
public import PrimeGapsTheory.Sieve.S1.CRT

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Partial summation for the first moment

Evaluates the transformed first-moment sum by iterated partial summation.

## Main definitions

* `S1E`: The mixed sum/integral interpolating between the main integral term and the target
  discrete sum.

## Main results

* `S1_aggregate`: Approximates the transformed sum by its simplex integral.
-/

@[expose] public section

open Real

open scoped ArithmeticFunction.Moebius
open scoped Finset
open scoped Topology

open scoped ArithmeticFunction.detotient

namespace PrimeGaps

section S1Aggregate
open MeasureTheory

variable {k : ℕ}

/-- There exist `L A₂: ℝ` with `0 ≤ L`, `0 < A₂`, and for all `2 ≤ w ≤ z`,
`-L ≤ Δ (gammaW W) w z ≤ A₂`.
-/
theorem S1_gammaW_mertens (W : ℕ) (hWpos : 0 < W) : ∃ L A₂ : ℝ, 0 ≤ L ∧ 0 < A₂ ∧
      ∀ a b : ℝ, 2 ≤ a → a ≤ b → -L ≤ Δ (PrimeGaps.gammaW W) a b ∧
        Δ (PrimeGaps.gammaW W) a b ≤ A₂ := by
  classical
  obtain ⟨M, hM0, hM⟩ := mertens_interval
  set B_W : ℝ := ∑ p ∈ W.primeFactors, Real.log ↑p / ↑p with hBW
  have hBW_nonneg : 0 ≤ B_W := Finset.sum_nonneg fun p _ ↦ by positivity
  refine ⟨M + B_W, M + 1, by linarith, by linarith, ?_⟩
  intro a b ha hab
  set S : Finset ℕ := {p ∈ Finset.range (⌊b⌋₊ + 1) | Nat.Prime p ∧ a ≤ ↑p ∧ ↑p ≤ b} with hS
  set removed : ℝ := ∑ p ∈ S, (if p ∣ W then (1 : ℝ) else 0) * Real.log ↑p / ↑p with hrem
  have hident : Δ (fun _ ↦ (1 : ℝ)) a b - Δ (PrimeGaps.gammaW W) a b = removed := by
    have hExpand : (∑ p ∈ S, (fun _ ↦ (1 : ℝ)) p * Real.log ↑p / ↑p) -
            (∑ p ∈ S, PrimeGaps.gammaW W p * Real.log ↑p / ↑p) =
          ∑ p ∈ S, (if p ∣ W then (1 : ℝ) else 0) * Real.log ↑p / ↑p := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      simp only [hS, Finset.mem_filter] at hp
      by_cases hdvd : p ∣ W <;> simp [PrimeGaps.gammaW, hp.2.1.coprime_iff_not_dvd, hdvd]
    have hIPS1 : intervalPrimeSum (fun _ ↦ (1 : ℝ)) a b =
        ∑ p ∈ S, (fun _ ↦ (1 : ℝ)) p * Real.log ↑p / ↑p := by
      rw [hS]; rfl
    have hIPSg : intervalPrimeSum (PrimeGaps.gammaW W) a b =
        ∑ p ∈ S, PrimeGaps.gammaW W p * Real.log ↑p / ↑p := by
      rw [hS]; rfl
    change (intervalPrimeSum (fun _ ↦ (1 : ℝ)) a b - Real.log (b / a)) -
          (intervalPrimeSum (PrimeGaps.gammaW W) a b - Real.log (b / a)) = removed
    rw [hIPS1, hIPSg, hrem]
    linarith [hExpand]
  have hrem_nonneg : 0 ≤ removed := by
    rw [hrem]
    refine Finset.sum_nonneg fun p _ ↦ ?_
    by_cases hdvd : p ∣ W <;> simp only [hdvd, if_true, if_false] <;> positivity
  have hrem_le : removed ≤ B_W := by
    rw [hrem, hBW]
    have hsub : (S.filter (fun p ↦ p ∣ W)) ⊆ W.primeFactors := by
      intro p hp
      simp only [Finset.mem_filter, hS] at hp
      exact Nat.mem_primeFactors.mpr ⟨hp.1.2.1, hp.2, hWpos.ne'⟩
    have hfilter_eq : ∑ p ∈ S.filter (fun p ↦ p ∣ W), Real.log ↑p / ↑p =
        ∑ p ∈ S, (if p ∣ W then (1 : ℝ) else 0) * Real.log ↑p / ↑p := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      by_cases hdvd : p ∣ W <;> simp [hdvd]
    calc ∑ p ∈ S, (if p ∣ W then (1 : ℝ) else 0) * Real.log ↑p / ↑p
        = ∑ p ∈ S.filter (fun p ↦ p ∣ W), Real.log ↑p / ↑p := hfilter_eq.symm
      _ ≤ ∑ p ∈ W.primeFactors, Real.log ↑p / ↑p :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ ↦ by positivity
  have hM'' : |Δ (fun _ ↦ (1 : ℝ)) a b| ≤ M := hM a b ha hab
  obtain ⟨hM1, hM2⟩ := abs_le.mp hM''
  constructor <;> linarith [hrem_le, hrem_nonneg]

/-- The `W` -tricked density `gammaW W` assembles into a `SieveDatum` with `V = W`, `A₁ = 1 / 2`
and `A₃ = 0`. -/
theorem S1_WSieveDatum (W : ℕ) (hWpos : 0 < W) (hWsqf : Squarefree W) : ∃ S : SieveDatum,
      S.γ = PrimeGaps.gammaW W ∧ S.V = W ∧
        S.A₁ = (1 / 2 : ℝ) ∧ S.A₃ = (0 : ℝ) := by
  obtain ⟨L, A₂, hL, hA₂, hmertens⟩ := S1_gammaW_mertens W hWpos
  refine ⟨SieveDatum.mk (PrimeGaps.gammaW W) (1 / 2) W 0
    ?γ_nonneg ?γ_one ?γ_mul ?γ_lt ?A₁_pos ?A₁_lt_one ?γ_density
    ?V_pos ?V_squarefree ?A₃_nonneg ?γ_zero_of_dvd ?γ_approx
    A₂ L ?A₂_pos ?L_nonneg ?mertens_bound, rfl, rfl, rfl, rfl⟩
  case γ_nonneg =>
    intro n; simp only [PrimeGaps.gammaW]; split <;> norm_num
  case γ_one =>
    simp [PrimeGaps.gammaW]
  case γ_mul =>
    intro m n hmn
    simp only [PrimeGaps.gammaW, Nat.coprime_mul_iff_left]
    split_ifs <;> simp_all
  case γ_lt =>
    intro p hp
    have h2 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    simp only [PrimeGaps.gammaW]
    split <;> linarith
  case A₁_pos => norm_num
  case A₁_lt_one => norm_num
  case γ_density =>
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    simp only [PrimeGaps.gammaW]
    split
    · rw [div_le_iff₀ (by linarith)]; linarith
    · norm_num
  case V_pos => exact hWpos
  case V_squarefree => exact hWsqf
  case A₃_nonneg => norm_num
  case γ_zero_of_dvd =>
    intro p hp hpdvd
    simp [PrimeGaps.gammaW, hp.coprime_iff_not_dvd, hpdvd]
  case γ_approx =>
    intro p hp hpndvd
    simp [PrimeGaps.gammaW, hp.coprime_iff_not_dvd, hpndvd]
  case A₂_pos => exact hA₂
  case L_nonneg => exact hL
  case mertens_bound => exact hmertens

/-- For a `SieveDatum` `S` with `S.γ = gammaW W`, `S.V = W` and `W = n#`, its singular series is
`𝔖 S.γ = φ(W)/W`, its weight is `S.h u = μ(u)² / φ(u)` for squarefree `u` coprime to `W`, and
`S.h u = 0` otherwise. -/
theorem S1_datum_facts (W n : ℕ) (hW : W = primorial n) (S : SieveDatum)
    (hγ : S.γ = PrimeGaps.gammaW W) (hV : S.V = W) :
    𝔖 S.γ = (W.totient : ℝ) / (W : ℝ) ∧
    (∀ u : ℕ, Squarefree u → Nat.Coprime u W →
        S.h u = (μ u : ℝ) ^ 2 / (Nat.totient u : ℝ)) ∧
    (∀ u : ℕ, ¬ (Squarefree u ∧ Nat.Coprime u W) →
        S.h u = 0) := by
  have hgammaW_one : ∀ p : ℕ, Nat.Coprime p W → S.γ p = 1 :=
    fun p hp ↦ by simp [hγ, PrimeGaps.gammaW, hp]
  have hgStar_one : ∀ p : ℕ, p.Prime → Nat.Coprime p W → S.gStar p = 1 / ((p : ℝ) - 1) :=
    fun p hp hcop ↦ by rw [S.gStar_prime p hp, hgammaW_one p hcop]
  refine ⟨?_, ?_, ?_⟩
  · rw [hγ, hW]
    exact PrimeGaps.singularSeries_gammaW n
  · intro u hsqf hcop
    rw [S.h_squarefree_eq_prod u hsqf]
    have hfac : ∀ p ∈ u.primeFactors, S.gStar p = 1 / ((p : ℝ) - 1) := fun p hp ↦
      hgStar_one p (Nat.prime_of_mem_primeFactors hp)
        (hcop.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp))
    rw [Finset.prod_congr rfl hfac]
    have hφ : (Nat.totient u : ℝ) = ∏ p ∈ u.primeFactors, ((p : ℝ) - 1) := by
      have h1 : Nat.totient u = ∏ p ∈ u.primeFactors, (p - 1) := by
        have := Nat.totient_eq_div_primeFactors_mul u
        rw [Nat.prod_primeFactors_of_squarefree hsqf] at this
        rw [this, Nat.div_self hsqf.ne_zero.bot_lt, one_mul]
      rw [h1]; push_cast
      refine Finset.prod_congr rfl fun p hp ↦ ?_
      push_cast [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le]; ring
    have hμ : (μ u : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsqf
    rw [hμ, hφ, Finset.prod_div_distrib, Finset.prod_const_one]
  · intro u hu
    by_cases hsqf : Squarefree u
    · have hWpos : 0 < W := by rw [hW]; exact primorial_pos n
      have hgcd : 1 < u.gcd W := by
        have h0 : u.gcd W ≠ 0 := fun h ↦ by
          have := Nat.eq_zero_of_gcd_eq_zero_right h; omega
        have h1 : u.gcd W ≠ 1 := fun h ↦ hu ⟨hsqf, h⟩
        omega
      exact S.h_eq_zero_of_gcd_gt_one u (by rw [hV]; exact hgcd)
    · change (μ u : ℝ) ^ 2 * S.gStar u = 0
      simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsqf]

/-- For `F` supported on `𝓡 k`, `∫_{𝓡 k} F² = ∫_{[0,1]^k} F²`. This is
`PrimeGaps.sieve_integral_cube` read at the sieve dimension. -/
theorem S1_integral_cube (F : EuclideanSpace ℝ (Fin k) → ℝ) (hsupp : Function.support F ⊆ 𝓡 k) :
    (∫ x in 𝓡 k, (F x) ^ 2) = ∫ x in Set.pi Set.univ (fun _ : Fin k ↦ Set.Icc (0 : ℝ) 1),
          (F (WithLp.toLp 2 x)) ^ 2 :=
  PrimeGaps.sieve_integral_cube F hsupp

/-- For `0 ≤ m ≤ k`, `S1E R W F m` is the mixed sum/integral obtained after peeling `m`
coordinates into discrete sums and leaving `k − m` as an integral: the outer `tsum` over
`u : Fin m → ℕ` of the weight `∏ μ(uᵢ)²/φ(uᵢ)` times `(φ(W)/W · log R)^{k-m}` times the
truncated-simplex integral of `F²` over the remaining coordinates. `E_0` is the main integral term
and `E_k` is the target discrete sum. -/
noncomputable def S1E (R : ℝ) (W : ℕ) (F : EuclideanSpace ℝ (Fin k) → ℝ) (m : ℕ) : ℝ :=
  ∑' u : Fin m → ℕ, (if (∀ i, 1 ≤ u i) ∧ (∀ i, Nat.Coprime (u i) W) then
        (∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ))
      else 0) * (((W.totient : ℝ) / (W : ℝ) * Real.log R) ^ (k - m) *
    (∫ x in Set.pi Set.univ (fun _ : Fin k ↦ Set.Icc (0 : ℝ) 1), Set.indicator
            {y : Fin k → ℝ |
              ∑ i : Fin k, (if h : (i : ℕ) < m then
                      Real.log (u ⟨i, h⟩) / Real.log (R)
                    else y i) ≤ 1}
            (fun y ↦ (F (WithLp.toLp 2 (fun i ↦ if h : (i : ℕ) < m then
                    Real.log (u ⟨i, h⟩) / Real.log (R)
                  else y i))) ^ 2) x))

/-- `E_0` is the main integral term `(φ(W)/W · log R)^k · ∫_{𝓡 k} F²` (via `S1_integral_cube`). -/
theorem S1E_zero (R : ℝ) (W : ℕ) (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hsupp : Function.support F ⊆ 𝓡 k) :
    S1E R W F 0 = (W.totient : ℝ) ^ k * (Real.log R) ^ k /
          (W : ℝ) ^ k * (∫ x in 𝓡 k, (F x) ^ 2) := by
  classical
  unfold S1E
  rw [tsum_eq_single (default : Fin 0 → ℕ) (fun b hb ↦ absurd (Subsingleton.elim b default) hb)]
  have hcond : (∀ i, 1 ≤ (default : Fin 0 → ℕ) i) ∧
      (∀ i, Nat.Coprime ((default : Fin 0 → ℕ) i) W) :=
    ⟨fun i ↦ i.elim0, fun i ↦ i.elim0⟩
  rw [if_pos hcond, Finset.prod_eq_one fun i _ ↦ i.elim0, Nat.sub_zero]
  set cube : Set (Fin k → ℝ) := Set.pi Set.univ (fun _ : Fin k ↦ Set.Icc (0 : ℝ) 1) with hcube
  have hcubemeas : MeasurableSet cube := MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc
  have hsubst_id : ∀ y : Fin k → ℝ, (fun i : Fin k ↦ if h : (i : ℕ) < 0 then
          Real.log ((default : Fin 0 → ℕ) ⟨i, h⟩) / Real.log (R)
        else y i) = y := fun y ↦ funext fun i ↦ dif_neg (Nat.not_lt_zero _)
  have hinner : (∫ x in cube, Set.indicator
            {y : Fin k → ℝ |
              ∑ i : Fin k, (if h : (i : ℕ) < 0 then
                      Real.log ((default : Fin 0 → ℕ) ⟨i, h⟩) / Real.log (R)
                    else y i) ≤ 1}
            (fun y ↦ (F (WithLp.toLp 2 (fun i ↦ if h : (i : ℕ) < 0 then
                    Real.log ((default : Fin 0 → ℕ) ⟨i, h⟩) / Real.log (R)
                  else y i))) ^ 2) x) = ∫ x in cube, (F (WithLp.toLp 2 x)) ^ 2 := by
    apply MeasureTheory.setIntegral_congr_fun hcubemeas
    intro y hy
    by_cases hys : y ∈ {y : Fin k → ℝ |
              ∑ i : Fin k, (if h : (i : ℕ) < 0 then
                      Real.log ((default : Fin 0 → ℕ) ⟨i, h⟩) / Real.log (R)
                    else y i) ≤ 1}
    · rw [Set.indicator_of_mem hys]
      simp only
      rw [hsubst_id y]
    · rw [Set.indicator_of_notMem hys]
      simp only [Set.mem_ofPred_eq, not_le] at hys
      have hsum_gt : (1 : ℝ) < ∑ i, y i := by
        simpa only [dif_neg (Nat.not_lt_zero _)] using hys
      have hnotmem : WithLp.toLp 2 y ∉ 𝓡 k := by
        rw [EuclideanSpace.mem_scaledStdSimplex_iff]
        rintro ⟨_, hle⟩
        have : ∑ i, y i ≤ 1 := hle
        linarith
      have hFz : F (WithLp.toLp 2 y) = 0 := by by_contra hne; exact hnotmem (hsupp hne)
      change (0 : ℝ) = (F (WithLp.toLp 2 y)) ^ 2
      rw [hFz]; ring
  rw [hinner, ← S1_integral_cube F hsupp, mul_pow, div_pow]
  ring

/-- The concrete `∏ μ²/φ` weight equals the abstract `∏ S.h` weight. For the `W`-coprime datum
`S`, the coprime-squarefree `μ²/φ` outer weight coincides with the density-agnostic weight `∏ S.h`
(via `S1_datum_facts`). Used to route the concrete `S1E`-based lemmas through their
`sieveE`-based counterparts. -/
theorem S1_weight_eq (W : ℕ) (S : SieveDatum) (hh_pos : ∀ u : ℕ, Squarefree u → Nat.Coprime u W →
      S.h u = (μ u : ℝ) ^ 2 / (Nat.totient u : ℝ))
    (hh_zero : ∀ u : ℕ, ¬ (Squarefree u ∧ Nat.Coprime u W) → S.h u = 0)
    {m : ℕ} (u : Fin m → ℕ) :
    (if (∀ i, 1 ≤ u i) ∧ (∀ i, Nat.Coprime (u i) W) then
        (∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ))
      else 0) = (if (∀ i, 1 ≤ u i) then (∏ i, S.h (u i)) else 0) := by
  classical
  by_cases h1 : ∀ i, 1 ≤ u i
  · by_cases hcop : ∀ i, Nat.Coprime (u i) W
    · rw [if_pos ⟨h1, hcop⟩, if_pos h1]
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      by_cases hsq : Squarefree (u i)
      · rw [hh_pos (u i) hsq (hcop i)]
      · have hmu : (μ (u i) : ℝ) = 0 := by
          simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
        rw [hmu, hh_zero (u i) fun h ↦ hsq h.1]; ring
    · rw [if_neg fun h ↦ hcop h.2, if_pos h1]
      obtain ⟨j, hj⟩ := not_forall.mp hcop
      exact (Finset.prod_eq_zero (Finset.mem_univ j) (hh_zero (u j) fun h ↦ hj h.2)).symm
  · rw [if_neg fun h ↦ h1 h.1, if_neg h1]

/-- `S1E = sieveE` at the `W`-coprime datum. The concrete mixed sum/integral `S1E` equals the
density-agnostic `sieveE` instantiated at the `W`-coprime `SieveDatum` `S` and truncation `z = R`
(via `S1_datum_facts`: `φ(W)/W = 𝔖 S.γ` and the weight identity `S1_weight_eq`). -/
theorem S1E_eq_sieveE (R : ℝ) (W : ℕ) (S : SieveDatum) (hSS : 𝔖 S.γ = (W.totient : ℝ) / (W : ℝ))
    (hh_pos : ∀ u : ℕ, Squarefree u → Nat.Coprime u W →
      S.h u = (μ u : ℝ) ^ 2 / (Nat.totient u : ℝ))
    (hh_zero : ∀ u : ℕ, ¬ (Squarefree u ∧ Nat.Coprime u W) → S.h u = 0)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (m : ℕ) :
    S1E R W F m = sieveE S R F m := by
  classical
  unfold S1E sieveE
  refine tsum_congr fun u ↦ ?_
  rw [S1_weight_eq W S hh_pos hh_zero u, hSS]
  ring

/-- `E_k` is the target discrete sum (via `S1_datum_facts`: the empty remaining integral collapses
to the point evaluation `F(log u / log R)²`).
-/
theorem S1E_full (R : ℝ) (W : ℕ) (S : SieveDatum) (hSS : 𝔖 S.γ = (W.totient : ℝ) / (W : ℝ))
    (hh_pos : ∀ u : ℕ, Squarefree u → Nat.Coprime u W →
      S.h u = (μ u : ℝ) ^ 2 / (Nat.totient u : ℝ))
    (hh_zero : ∀ u : ℕ, ¬ (Squarefree u ∧ Nat.Coprime u W) → S.h u = 0)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hsupp : Function.support F ⊆ 𝓡 k) :
    S1E R W F k = ∑' u : Fin k → ℕ, if (∀ i, 1 ≤ u i) ∧ (∀ i, Nat.Coprime (u i) W) then
            (∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ)) *
              (F (WithLp.toLp 2 (fun i ↦ Real.log (u i) / Real.log R))) ^ 2
          else 0 := by
  classical
  rw [S1E_eq_sieveE R W S hSS hh_pos hh_zero F k, sieveE_full S R F hsupp]
  refine tsum_congr fun u ↦ ?_
  by_cases h1 : ∀ i, 1 ≤ u i
  · by_cases hcop : ∀ i, Nat.Coprime (u i) W
    · rw [if_pos h1, if_pos ⟨h1, hcop⟩]
      congr 1
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      by_cases hsq : Squarefree (u i)
      · exact hh_pos (u i) hsq (hcop i)
      · have hmu : (μ (u i) : ℝ) = 0 := by
          simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
        rw [hmu, hh_zero (u i) fun h ↦ hsq h.1]; ring
    · rw [if_pos h1, if_neg fun h ↦ hcop h.2]
      obtain ⟨j, hj⟩ := not_forall.mp hcop
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (hh_zero (u j) fun h ↦ hj h.2), zero_mul]
  · rw [if_neg h1, if_neg fun h ↦ h1 h.1]

private theorem one_le_log_D₀ {N : ℕ} (hN : rexp (rexp (rexp 3)) + 1 ≤ (N : ℝ)) :
    (1 : ℝ) ≤ Real.log (PrimeGaps.D₀ (N : ℝ)) :=
  ((Real.le_log_iff_exp_le (by norm_num)).mpr Real.exp_one_lt_three.le).trans
    (Real.log_le_log (by norm_num) (PrimeGaps.lt_D₀_of_le hN).le)

open scoped PrimeGaps.sieveModulus in
/-- Eventually `1 + ellV (W N) ≤ c₁ · log (D₀ N)`. Here `ellV (W N) = ∑_{p ∣ WN} log p/(p−1) ≪
log log (WN)` (`mertens_weighted_prime_bound`), and `log (WN) = θ(D₀ N) ≍ D₀ N`, so
`log log (WN) = log D₀ N + O(1)`. -/
theorem S1_OB_H1 : ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      1 + ellV (W N) ≤ c₁ * Real.log (PrimeGaps.D₀ (N : ℝ)) := by
  classical
  obtain ⟨C_B, hCB, hmert⟩ := mertens_weighted_prime_bound
  refine ⟨1 + 3 * C_B, by positivity, rexp (rexp (rexp 3)) + 1, ?_⟩
  intro N hN
  have hdef : ellV (W N) = ∑ p ∈ (W N).primeFactors, Real.log (p : ℝ) / ((p : ℝ) - 1) := rfl
  have hWpos : 0 < W N := PrimeGaps.W_pos (N := N)
  have hM := hmert (W N) PrimeGaps.W_squarefree hWpos
  rw [← hdef] at hM
  have hD3 : 3 ≤ PrimeGaps.D₀ (N : ℝ) := (PrimeGaps.lt_D₀_of_le hN).le
  have hD0nn : 0 ≤ PrimeGaps.D₀ (N : ℝ) := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log (PrimeGaps.D₀ (N : ℝ)) := one_le_log_D₀ hN
  set L := Real.log (PrimeGaps.D₀ (N : ℝ)) with hLdef
  have hlogmul : Real.log (rexp 1 * (W N : ℝ)) =
      1 + Chebyshev.theta (PrimeGaps.D₀ (N : ℝ)) := by
    rw [Real.log_mul (Real.exp_pos 1).ne' (Nat.cast_ne_zero.mpr hWpos.ne'), Real.log_exp,
      PrimeGaps.real_log_W_eq_theta_D₀ (N := N)]
  have hθnn : 0 ≤ Chebyshev.theta (PrimeGaps.D₀ (N : ℝ)) := Chebyshev.theta_nonneg _
  have hlog4le2 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; linarith [Real.log_two_lt_d9]
  have hθle : Chebyshev.theta (PrimeGaps.D₀ (N : ℝ)) ≤ 2 * PrimeGaps.D₀ (N : ℝ) := by
    nlinarith [Chebyshev.theta_le_log4_mul_x hD0nn, hD0nn, hlog4le2]
  have hbnd : 1 + Chebyshev.theta (PrimeGaps.D₀ (N : ℝ)) ≤ (PrimeGaps.D₀ (N : ℝ)) ^ 2 := by
    nlinarith [hθle, hD3]
  have h1θpos : 0 < 1 + Chebyshev.theta (PrimeGaps.D₀ (N : ℝ)) := by linarith
  have hloglog : Real.log (Real.log (rexp 1 * (W N : ℝ))) ≤ 2 * L := by
    rw [hlogmul]
    calc Real.log (1 + Chebyshev.theta (PrimeGaps.D₀ (N : ℝ)))
        ≤ Real.log ((PrimeGaps.D₀ (N : ℝ)) ^ 2) := Real.log_le_log h1θpos hbnd
      _ = 2 * L := by rw [Real.log_pow]; push_cast; rw [hLdef]
  have hstep1 : 1 + ellV (W N) ≤ 1 + C_B * (1 + 2 * L) := by
    have hmono : C_B * (1 + Real.log (Real.log (rexp 1 * (W N : ℝ)))) ≤ C_B * (1 + 2 * L) :=
      mul_le_mul_of_nonneg_left (by linarith) hCB.le
    linarith
  calc 1 + ellV (W N) ≤ 1 + C_B * (1 + 2 * L) := hstep1
    _ ≤ (1 + 3 * C_B) * L := by nlinarith [hCB, hL1, mul_nonneg hCB.le (sub_nonneg.mpr hL1)]

private theorem eventually_log_pow_four_mul_le (c : ℝ) (hc : 0 < c) : ∀ᶠ (L : ℝ) in Filter.atTop,
      (Real.log L) ^ 4 * (8 * Real.log (2 * (Real.log L) ^ 2) + 64) ≤ c * L := by
  have hpow5 : ∀ᶠ (L : ℝ) in Filter.atTop, (Real.log L) ^ 5 / L ≤ c / 176 := by
    filter_upwards [Real.eventually_log_pow_le_const_mul 5 (by positivity : (0 : ℝ) < c / 176),
      Filter.eventually_gt_atTop (0 : ℝ)] with L hL hLpos
    rw [div_le_iff₀ hLpos]; linarith
  filter_upwards [hpow5, Filter.eventually_ge_atTop (rexp 1),
    Filter.eventually_ge_atTop (144 / c), Filter.eventually_gt_atTop (0 : ℝ)]
    with L hp5 hLe hLe2 hLp
  have hlogL_pos : 0 < Real.log L := Real.log_pos (by linarith [Real.add_one_le_exp (1 : ℝ)])
  have hlogL_nonneg : 0 ≤ Real.log L := hlogL_pos.le
  have hloglog_le : Real.log (Real.log L) ≤ Real.log L :=
    Real.log_le_log hlogL_pos (by linarith [Real.log_le_sub_one_of_pos hLp])
  have hmiddle : 8 * Real.log (2 * (Real.log L) ^ 2) + 64 =
      8 * Real.log 2 + 16 * Real.log (Real.log L) + 64 := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
  have hlog2_le : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hmid_le : 8 * Real.log (2 * (Real.log L) ^ 2) + 64 ≤ 16 * Real.log L + 72 := by
    rw [hmiddle]; linarith
  have hpow4_nonneg : 0 ≤ (Real.log L) ^ 4 := by positivity
  have hstep1 : (Real.log L) ^ 4 * (8 * Real.log (2 * (Real.log L) ^ 2) + 64) ≤
      (Real.log L) ^ 4 * (16 * Real.log L + 72) :=
    mul_le_mul_of_nonneg_left hmid_le hpow4_nonneg
  have hx4 : (Real.log L) ^ 4 ≤ (Real.log L) ^ 5 + 1 := by
    rcases le_or_gt (Real.log L) 1 with hle | hgt
    · have h1 : (Real.log L) ^ 4 ≤ 1 := pow_le_one₀ hlogL_nonneg hle
      linarith [pow_nonneg hlogL_nonneg 5]
    · nlinarith [hpow4_nonneg, hgt, pow_succ (Real.log L) 4]
  have hstep2 : (Real.log L) ^ 4 * (16 * Real.log L + 72) ≤ 88 * (Real.log L) ^ 5 + 72 := by
    nlinarith [hx4, hpow4_nonneg, hlogL_nonneg, pow_succ (Real.log L) 4]
  have hpow5_le : (Real.log L) ^ 5 ≤ c / 176 * L := (div_le_iff₀ hLp).mp hp5
  have h88 : 88 * (Real.log L) ^ 5 ≤ c * L / 2 := by linarith
  have h72 : (72 : ℝ) ≤ c * L / 2 := by linarith [(div_le_iff₀ hc).mp hLe2]
  calc (Real.log L) ^ 4 * (8 * Real.log (2 * (Real.log L) ^ 2) + 64)
      ≤ (Real.log L) ^ 4 * (16 * Real.log L + 72) := hstep1
    _ ≤ 88 * (Real.log L) ^ 5 + 72 := hstep2
    _ ≤ c * L / 2 + c * L / 2 := add_le_add h88 h72
    _ = c * L := by ring

open scoped PrimeGaps.sieveModulus in
/-- Eventually `1 / (log log N)^2 ≤ (φ(W N) / W N) · log (D₀ N)`. Uses `φ(W) / W ≥ 1 / W`,
`lem_W_size` (`W ≤ (log log N)^2`), and `log (D₀ N) ≥ 1` eventually (`D₀ N → ∞`). -/
theorem S1_OB_H2_rhs : ∀ᶠ (N : ℕ) in Filter.atTop,
      1 / (Real.log (Real.log N)) ^ 2 ≤ (((W N).totient : ℝ) / (W N : ℝ)) *
            Real.log (PrimeGaps.D₀ (N : ℝ)) := by
  filter_upwards [PrimeGaps.lem_W_size,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ))),
      tendsto_natCast_atTop_atTop.eventually
        (Filter.eventually_ge_atTop (rexp (rexp (rexp 3)) + 1))]
    with N hWsize hloglog_ge1 hNge
  have hWpos : 0 < W N := PrimeGaps.W_pos (N := N)
  have hWposR : (0 : ℝ) < (W N : ℝ) := by exact_mod_cast hWpos
  have hloglog_ge1' : (1 : ℝ) ≤ Real.log (Real.log (N : ℝ)) := by
    simpa only [Function.comp] using hloglog_ge1
  have hloglog_pos : (0 : ℝ) < Real.log (Real.log (N : ℝ)) := by linarith
  have hphi1R : (1 : ℝ) ≤ ((W N).totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hWpos
  have hphiposR : (0 : ℝ) < ((W N).totient : ℝ) := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log (PrimeGaps.D₀ (N : ℝ)) := one_le_log_D₀ hNge
  have hstep1 : 1 / (Real.log (Real.log (N : ℝ))) ^ 2 ≤ 1 / (W N : ℝ) :=
    one_div_le_one_div_of_le hWposR hWsize
  refine hstep1.trans ?_
  rw [div_mul_eq_mul_div, one_div, le_div_iff₀ hWposR, inv_mul_cancel₀ hWposR.ne']
  nlinarith [hphi1R, hL1, hphiposR]

private theorem card_divisors_le_of_natCast_le {V : ℕ} {b : ℝ} (h : (V : ℝ) ≤ b) :
    (#V.divisors : ℝ) ≤ b :=
  le_trans (by exact_mod_cast Nat.card_divisors_le_self V) h

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- With `c := θ/2 - δ`, eventually `τ(W N)·(8 log(2 W N)+64)/log R ≤
(log log N)^2·(8 log(2 (log log N)^2)+64)/(c · log N)`. Uses `τ(W) ≤ W`
(`Nat.card_divisors_le_self`), `lem_W_size` (`W ≤ (log log N)^2`), monotonicity of
`x ↦ 8 log(2x)+64`, and `log R = c · log N`. -/
theorem S1_OB_H2_lhs (δ θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2)) :
    ∀ᶠ (N : ℕ) in Filter.atTop, (#(W N).divisors : ℝ) * (8 * Real.log (2 * (W N : ℝ)) + 64) /
          Real.log (R) ≤ (Real.log (Real.log N)) ^ 2 *
            (8 * Real.log (2 * (Real.log (Real.log N)) ^ 2) + 64) / ((θ / 2 - δ) * Real.log N) := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  obtain ⟨hδ0, hδθ⟩ := hδ
  have hc : (0 : ℝ) < θ / 2 - δ := by linarith
  filter_upwards [PrimeGaps.lem_W_size,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (Filter.eventually_gt_atTop (0 : ℝ))]
    with N hWsize hlogN_pos
  set B : ℝ := Real.log (Real.log (N : ℝ))
  have hWpos : 0 < W N := PrimeGaps.W_pos (N := N)
  have hWposR : (0 : ℝ) < (W N : ℝ) := by exact_mod_cast hWpos
  have hlogN_pos' : (0 : ℝ) < Real.log (N : ℝ) := by
    simpa only [Function.comp] using hlogN_pos
  have hRlog : Real.log (R) = (θ / 2 - δ) * Real.log (N : ℝ) :=
    Real.log_rpow (Nat.cast_pos.mpr (Nat.pos_of_ne_zero fun h ↦ by simp [h] at hlogN_pos')) _
  rw [hRlog]
  set D : ℝ := (θ / 2 - δ) * Real.log (N : ℝ)
  have hDpos : 0 < D := mul_pos hc hlogN_pos
  rw [div_le_div_iff_of_pos_right hDpos]
  have htau : (#(W N).divisors : ℝ) ≤ B ^ 2 := card_divisors_le_of_natCast_le hWsize
  have h2Wpos : (0 : ℝ) < 2 * (W N : ℝ) := by positivity
  have hlog_le : Real.log (2 * (W N : ℝ)) ≤ Real.log (2 * B ^ 2) :=
    Real.log_le_log h2Wpos (by linarith [hWsize])
  have hmidW_nonneg : 0 ≤ 8 * Real.log (2 * (W N : ℝ)) + 64 := by
    have hW1R : (1 : ℝ) ≤ (W N : ℝ) := by exact_mod_cast hWpos
    linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * (W N : ℝ))]
  calc (#(W N).divisors : ℝ) * (8 * Real.log (2 * (W N : ℝ)) + 64)
      ≤ B ^ 2 * (8 * Real.log (2 * (W N : ℝ)) + 64) := mul_le_mul_of_nonneg_right htau hmidW_nonneg
    _ ≤ B ^ 2 * (8 * Real.log (2 * B ^ 2) + 64) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- Pure algebra: from the asymptotic `(loglogN)^4·Q ≤ c·logN` (with `Q ≥ 64 > 0`, `c > 0`,
`loglogN > 0`, `logN > 0`), `(loglogN)^2·Q/(c·logN) ≤ 1/(loglogN)²`. -/
theorem S1_OB_H2_ratio (δ θ : ℝ) (hc : (0 : ℝ) < θ / 2 - δ) : ∀ᶠ (N : ℕ) in Filter.atTop,
      (Real.log (Real.log N)) ^ 2 * (8 * Real.log (2 * (Real.log (Real.log N)) ^ 2) + 64) /
          ((θ / 2 - δ) * Real.log N) ≤ 1 / (Real.log (Real.log N)) ^ 2 := by
  set c : ℝ := θ / 2 - δ with hcdef
  have hR : ∀ᶠ (L : ℝ) in Filter.atTop,
      (Real.log L) ^ 4 * (8 * Real.log (2 * (Real.log L) ^ 2) + 64) ≤ c * L ∧
        (0 : ℝ) < Real.log (Real.log L) ∧ (0 : ℝ) < Real.log L ∧ (0 : ℝ) < L := by
    filter_upwards [eventually_log_pow_four_mul_le c hc,
        Filter.eventually_ge_atTop (rexp (rexp 1)),
        Filter.eventually_gt_atTop (0 : ℝ)] with L hkey hLee hLp
    have hlogL_gt1 : 1 < Real.log L := by
      linarith [(Real.le_log_iff_exp_le hLp).mpr hLee, Real.add_one_le_exp (1 : ℝ)]
    exact ⟨hkey, Real.log_pos hlogL_gt1, by linarith, hLp⟩
  have hlog : Filter.Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually hR] with N hN
  obtain ⟨hasymp, _, hloglogN_pos, hlogN_pos⟩ := hN
  have hcB : 0 < c * Real.log (N : ℝ) := mul_pos hc hlogN_pos
  have hA2 : 0 < (Real.log (Real.log (N : ℝ))) ^ 2 := pow_pos hloglogN_pos 2
  rw [div_le_div_iff₀ hcB hA2]
  nlinarith [hasymp, hA2, hcB]

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- Eventually `τ(W N) · (8 log (2 * W N) + 64) / log R ≤ c₂ · (φW / W) · log (D₀ N)`. Here
`D₀ N ≍ log log log N` is tiny and `W N = primorial ⌊D₀⌋`, so `τ(W N)` and `log (W N) = θ(D₀)`
are `≪` any positive power of `log R ≈ θ log N`. -/
theorem S1_OB_H2 (δ θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2)) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      (#(W N).divisors : ℝ) * (8 * Real.log (2 * (W N : ℝ)) + 64) / Real.log (R) ≤
        c₂ * (((W N).totient : ℝ) / (W N : ℝ)) *
            Real.log (PrimeGaps.D₀ (N : ℝ)) := by
  refine ⟨1, one_pos, ?_⟩
  have hc : (0 : ℝ) < θ / 2 - δ := by linarith [hδ.1, hδ.2]
  have hcomb : ∀ᶠ (N : ℕ) in Filter.atTop, (#(W N).divisors : ℝ) * (8 * Real.log (2 *
        (W N : ℝ)) + 64) / Real.log (R) ≤
        1 * (((W N).totient : ℝ) / (W N : ℝ)) *
            Real.log (PrimeGaps.D₀ (N : ℝ)) := by
    filter_upwards [S1_OB_H2_lhs δ θ hθ hδ, S1_OB_H2_ratio δ θ hc, S1_OB_H2_rhs]
      with N hL hA hR
    calc _ ≤ _ := hL
      _ ≤ 1 / (Real.log (Real.log N)) ^ 2 := hA
      _ ≤ _ := hR
      _ = 1 * (((W N).totient : ℝ) / (W N : ℝ)) *
            Real.log (PrimeGaps.D₀ (N : ℝ)) := by ring
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hcomb
  exact ⟨(M : ℝ), fun N hN ↦ hM N (by exact_mod_cast hN)⟩

/-- With `a:= (θ/2-δ)/8 > 0`, eventually `3 · (log N)^5 / N^a ≤ 1`. -/
theorem S1_OB_H3_asymp (a : ℝ) (ha : 0 < a) :
    ∀ᶠ (N : ℕ) in Filter.atTop, 3 * (Real.log (N : ℝ)) ^ 5 / (N : ℝ) ^ a ≤ 1 := by
  have htend : Filter.Tendsto (fun x : ℝ ↦ 3 * (Real.log x) ^ 5 / x ^ a) Filter.atTop (𝓝 0) := by
    have h3 := (PrimeGaps.tendsto_pow_log_div_rpow 5 a ha).const_mul (3 : ℝ)
    simp only [mul_zero] at h3
    apply h3.congr'
    filter_upwards with x
    rw [mul_div_assoc]
  exact tendsto_natCast_atTop_atTop.eventually
    (htend.eventually_le_const (by norm_num : (0 : ℝ) < 1))

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
private theorem tau_W_rpow_log_le_inv_loglog_sq (δ θ : ℝ)
    (hθ1 : θ < 1) (hδ0 : 0 < δ) (hδθ : δ < θ / 2) :
    ∀ᶠ (N : ℕ) in Filter.atTop,
      (#(W N).divisors : ℝ) * ((R) ^ (-(1 : ℝ) / 8) * Real.log (2 * (W N : ℝ) * R)) ≤
        1 / (Real.log (Real.log N)) ^ 2 := by
  have hc : (0 : ℝ) < θ / 2 - δ := by linarith
  set a : ℝ := (θ / 2 - δ) / 8 with hadef
  have ha : 0 < a := by rw [hadef]; positivity
  filter_upwards [PrimeGaps.lem_W_size, S1_OB_H3_asymp a ha,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ))),
      tendsto_natCast_atTop_atTop.eventually (Filter.eventually_ge_atTop (2 : ℝ)),
      tendsto_natCast_atTop_atTop.eventually
        (((Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 (by norm_num)).eventually_le_const
          (by norm_num : (0 : ℝ) < 1)))]
    with N hWsize hAsymp hloglog_ge1 hNge2 hlogsqN
  have hWpos : 0 < W N := PrimeGaps.W_pos (N := N)
  have hWposR : (0 : ℝ) < (W N : ℝ) := by exact_mod_cast hWpos
  have hW1R : (1 : ℝ) ≤ (W N : ℝ) := by exact_mod_cast hWpos
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  set B : ℝ := Real.log (Real.log (N : ℝ)) with hBdef
  have hB1 : (1 : ℝ) ≤ B := by simpa only [Function.comp] using hloglog_ge1
  have hBpos : 0 < B := by linarith
  have hRval : R = (N : ℝ) ^ (θ / 2 - δ) := rfl
  have hRpos : (0 : ℝ) < R := by rw [hRval]; exact Real.rpow_pos_of_pos hNpos _
  have hRpow : (R) ^ (-(1 : ℝ) / 8) = (N : ℝ) ^ (-a) := by
    rw [hRval, ← Real.rpow_mul hNpos.le]
    congr 1
    rw [hadef]; ring
  have htau : (#(W N).divisors : ℝ) ≤ B ^ 2 := card_divisors_le_of_natCast_le hWsize
  have hReN : R ≤ (N : ℝ) := by
    rw [hRval]
    calc (N : ℝ) ^ (θ / 2 - δ) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = (N : ℝ) := Real.rpow_one _
  have hBlogN : B ≤ Real.log (N : ℝ) := by
    rw [hBdef]
    exact Real.log_le_log hlogN_pos (by linarith [Real.log_le_sub_one_of_pos hNpos])
  have hWeN : (W N : ℝ) ≤ (N : ℝ) :=
    calc (W N : ℝ) ≤ B ^ 2 := hWsize
      _ ≤ Real.log (N : ℝ) ^ 2 := pow_le_pow_left₀ hBpos.le hBlogN 2
      _ ≤ (N : ℝ) := by
          simp only [one_mul, add_zero] at hlogsqN
          rwa [div_le_one hNpos] at hlogsqN
  have hbox_le : 2 * (W N : ℝ) * R ≤ (N : ℝ) ^ 3 := by
    have h2WN : 2 * (W N : ℝ) ≤ (N : ℝ) * (N : ℝ) := by
      linarith only [hWeN,
        mul_nonneg hNpos.le (by linarith only [hNge2] : (0 : ℝ) ≤ (N : ℝ) - 2)]
    calc 2 * (W N : ℝ) * R ≤ (N : ℝ) * (N : ℝ) * (N : ℝ) :=
          mul_le_mul h2WN hReN hRpos.le (mul_nonneg hNpos.le hNpos.le)
      _ = (N : ℝ) ^ 3 := by ring
  have hbox_pos : (0 : ℝ) < 2 * (W N : ℝ) * R := by positivity
  have hlogbox : Real.log (2 * (W N : ℝ) * R) ≤ 3 * Real.log (N : ℝ) :=
    calc Real.log (2 * (W N : ℝ) * R) ≤ Real.log ((N : ℝ) ^ 3) := Real.log_le_log hbox_pos hbox_le
      _ = 3 * Real.log (N : ℝ) := by rw [Real.log_pow]; push_cast; ring
  have hRge1 : (1 : ℝ) ≤ R := by
    rw [hRval]
    calc (1 : ℝ) = (N : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
      _ ≤ (N : ℝ) ^ (θ / 2 - δ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hlogbox_nonneg : (0 : ℝ) ≤ Real.log (2 * (W N : ℝ) * R) :=
    Real.log_nonneg (by nlinarith [hW1R, hRge1])
  have hNa_pos : (0 : ℝ) < (N : ℝ) ^ (-a) := Real.rpow_pos_of_pos hNpos _
  have hLHS_le : (#(W N).divisors : ℝ) * ((R) ^ (-(1 : ℝ) / 8) * Real.log (2 * (W N : ℝ) * R)) ≤
      B ^ 2 * ((N : ℝ) ^ (-a) * (3 * Real.log (N : ℝ))) := by
    rw [hRpow]
    refine mul_le_mul htau ?_ (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_left hlogbox hNa_pos.le
  have hB2pos : (0 : ℝ) < B ^ 2 := by positivity
  have hB4log : B ^ 4 * Real.log (N : ℝ) ≤ (Real.log (N : ℝ)) ^ 5 := by
    have hB4 : B ^ 4 ≤ (Real.log (N : ℝ)) ^ 4 := pow_le_pow_left₀ hBpos.le hBlogN 4
    calc B ^ 4 * Real.log (N : ℝ) ≤ (Real.log (N : ℝ)) ^ 4 * Real.log (N : ℝ) :=
          mul_le_mul_of_nonneg_right hB4 hlogN_pos.le
      _ = (Real.log (N : ℝ)) ^ 5 := by ring
  have hfinal : B ^ 2 * ((N : ℝ) ^ (-a) * (3 * Real.log (N : ℝ))) ≤ 1 / B ^ 2 := by
    have hNa_pos' : (0 : ℝ) < (N : ℝ) ^ a := Real.rpow_pos_of_pos hNpos _
    rw [le_div_iff₀ hB2pos, Real.rpow_neg hNpos.le, ← one_div,
      show B ^ 2 * (1 / (N : ℝ) ^ a * (3 * Real.log (N : ℝ))) * B ^ 2 =
        3 * (B ^ 4 * Real.log (N : ℝ)) / (N : ℝ) ^ a by ring, div_le_one hNa_pos']
    rw [div_le_iff₀ hNa_pos'] at hAsymp
    linarith [hB4log]
  calc (#(W N).divisors : ℝ) * ((R) ^ (-(1 : ℝ) / 8) * Real.log (2 * (W N : ℝ) * R))
      ≤ B ^ 2 * ((N : ℝ) ^ (-a) * (3 * Real.log (N : ℝ))) := hLHS_le
    _ ≤ 1 / B ^ 2 := hfinal
    _ = 1 / (Real.log (Real.log N)) ^ 2 := by rw [hBdef]

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- Eventually `τ(W N) · R ^ (-1 / 8) · log (2 · W N · R) ≤ c₃ · (φW / W) · log (D₀ N)`. Here
`R ^ (-1 / 8) = N ^ (-θ / 8)` decays polynomially, dwarfing the subpolynomial
`τ(W N)·log (2 W N R)`. -/
theorem S1_OB_H3 (δ θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2)) :
    ∃ c₃ : ℝ, 0 < c₃ ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → (#(W N).divisors : ℝ) * ((R) ^
        (-(1 : ℝ) / 8) * Real.log (2 * (W N : ℝ) * R)) ≤
        c₃ * (((W N).totient : ℝ) / (W N : ℝ)) *
            Real.log (PrimeGaps.D₀ (N : ℝ)) := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  obtain ⟨hδ0, hδθ⟩ := hδ
  refine ⟨1, one_pos, ?_⟩
  have hcomb : ∀ᶠ (N : ℕ) in Filter.atTop, (#(W N).divisors : ℝ) * ((R) ^
        (-(1 : ℝ) / 8) * Real.log (2 * (W N : ℝ) * R)) ≤
        1 * (((W N).totient : ℝ) / (W N : ℝ)) *
            Real.log (PrimeGaps.D₀ (N : ℝ)) := by
    filter_upwards [tau_W_rpow_log_le_inv_loglog_sq δ θ hθ1 hδ0 hδθ, S1_OB_H2_rhs]
      with N hsmall hRHS
    calc (#(W N).divisors : ℝ) * ((R) ^ (-(1 : ℝ) / 8) * Real.log (2 * (W N : ℝ) * R))
        ≤ 1 / (Real.log (Real.log N)) ^ 2 := hsmall
      _ ≤ (((W N).totient : ℝ) / (W N : ℝ)) * Real.log (PrimeGaps.D₀ (N : ℝ)) := hRHS
      _ = 1 * (((W N).totient : ℝ) / (W N : ℝ)) *
            Real.log (PrimeGaps.D₀ (N : ℝ)) := by ring
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hcomb
  exact ⟨(M : ℝ), fun N hN ↦ hM N (by exact_mod_cast hN)⟩

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- This is the main inductive result: applying `lem_partial_sum` to each coordinate sum, with `G`
the partial integral of `F²` over the already-summed coordinates, replaces the discrete sum by its
main term `(φ(W)/W)^k (log R)^k / W^{...} · ∫_{𝓡 k}F²` up to an aggregate error
`C · Fmax² · φ(W)^k · log D₀ · (log R)^{k-1} / W^k`.
-/
@[pg_tag "bg246" "lem_S1_apply_partial_sum"]
theorem S1_aggregate (δ θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2)) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : EuclideanSpace ℝ (Fin k) → ℝ), ContDiff ℝ (⊤ : ℕ∞) F → Function.support F ⊆ 𝓡 k →
        |(∑' u : Fin k → ℕ, if (∀ i, 1 ≤ u i) ∧ (∀ i, Nat.Coprime (u i) (W N)) then
              (∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ)) *
                (F (WithLp.toLp 2 (fun i ↦ Real.log (u i) / Real.log (R)))) ^ 2
            else 0) - ((W N).totient : ℝ) ^ k * (Real.log (R)) ^ k /
              (W N : ℝ) ^ k * (∫ x in 𝓡 k, (F x) ^ 2)| ≤
        C * (MaynardSmoothY.Fmax F) ^ 2 * ((W N).totient : ℝ) ^ k *
            Real.log (PrimeGaps.D₀ (N : ℝ)) * (Real.log (R)) ^ (k - 1) /
            (W N : ℝ) ^ k := by
  classical
  obtain ⟨Cs₁, Cs₂, Ch₁, Ch₂, hCs₁, hCs₂, hCh₁, hCh₂, habs⟩ := sieveDatum_kfold_partial_sum
  obtain ⟨c₁, hc₁, N₁, hH1⟩ := S1_OB_H1
  obtain ⟨c₂, hc₂, N₂, hH2⟩ := S1_OB_H2 δ θ hθ hδ
  obtain ⟨c₃, hc₃, N₃, hH3⟩ := S1_OB_H3 δ θ hθ hδ
  obtain ⟨hδ0, hδθ⟩ := hδ
  have hcθ : (0 : ℝ) < θ / 2 - δ := by linarith
  obtain ⟨N₄, hN₄⟩ := Filter.eventually_atTop.mp (R_eventually_ge θ δ hδθ 2)
  have hCs₁' : 0 < Cs₁ (1 / 2) 0 := hCs₁ _ _
  have hCs₂' : 0 < Cs₂ (1 / 2) 0 := hCs₂ _ _
  have hCh₁' : 0 < Ch₁ (1 / 2) 0 := hCh₁ _ _
  have hCh₂' : 0 < Ch₂ (1 / 2) 0 := hCh₂ _ _
  set Cp : ℝ := 6 * (2 * Cs₁ (1 / 2) 0 * c₁ + Cs₂ (1 / 2) 0 * (c₂ + c₃)) with hCpdef
  have hCppos : 0 < Cp := by rw [hCpdef]; positivity
  set CLD : ℝ := 1 / (θ / 2 - δ) with hCLDdef
  have hCLDpos : 0 < CLD := by rw [hCLDdef]; positivity
  set Cbox : ℝ := 2 + Ch₁ (1 / 2) 0 * c₁ * CLD + 2 * (Ch₂ (1 / 2) 0 * c₃ * CLD) with hCboxdef
  have hCboxpos : 0 < Cbox := by rw [hCboxdef]; positivity
  refine ⟨(k : ℝ) * (max 1 Cbox) ^ k * Cp + 1, by positivity, ?_⟩
  refine ⟨max (max N₁ N₂) (max N₃ (max (N₄ : ℝ) (rexp (rexp (rexp 1)) + 1))), ?_⟩
  intro N hN F hF hsupp
  have hN1 : N₁ ≤ (N : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ (N : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : N₃ ≤ (N : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN4 : (N₄ : ℝ) ≤ (N : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_right _ _) hN)
  have hNexp : rexp (rexp (rexp 1)) + 1 ≤ (N : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_trans (le_max_right _ _) hN)
  have hN4' : N₄ ≤ N := by exact_mod_cast hN4
  have hR2 : (2 : ℝ) ≤ R := hN₄ N hN4'
  have hNe : rexp 1 < (N : ℝ) := by
    linarith [Real.exp_le_exp.mpr (Real.one_le_exp (Real.exp_pos 1).le)]
  have hNpos : 0 < N := by exact_mod_cast (Real.exp_pos 1).trans hNe
  have hD1 : 1 < PrimeGaps.D₀ (N : ℝ) := by
    by_contra! hlt
    linarith [(PrimeGaps.D₀_le_self_iff (M := 1) hNe).mp hlt]
  let w := W N
  let n := ⌊PrimeGaps.D₀ (N : ℝ)⌋₊
  have hw : w = primorial n := PrimeGaps.W_eq_primorial_D₀
  obtain ⟨S, hγ, hV, hA₁, hA₃⟩ := S1_WSieveDatum w PrimeGaps.W_pos PrimeGaps.W_squarefree
  obtain ⟨hSS, hh_pos, hh_zero⟩ := S1_datum_facts w n hw S hγ hV
  rw [← S1E_full R w S hSS hh_pos hh_zero F hsupp, ← S1E_zero R w F hsupp,
      S1E_eq_sieveE R w S hSS hh_pos hh_zero F k,
      S1E_eq_sieveE R w S hSS hh_pos hh_zero F 0]
  refine le_trans (habs S F hF hsupp (R) hR2) ?_
  rw [hA₁, hA₃, hV, hSS]
  set q : ℝ := ((W N).totient : ℝ) / (W N : ℝ) with hqdef
  set ℓ : ℝ := Real.log (R) with hℓdef
  set LD : ℝ := Real.log (PrimeGaps.D₀ (N : ℝ)) with hLDdef
  set Fm : ℝ := (MaynardSmoothY.Fmax F) ^ 2 with hFmdef
  set τ : ℝ := (#(W N).divisors : ℝ) with hτdef
  have hWpos : 0 < W N := PrimeGaps.W_pos
  have hWposR : (0 : ℝ) < (W N : ℝ) := by exact_mod_cast hWpos
  have hqnn : 0 ≤ q := by rw [hqdef]; positivity
  have hℓpos : 0 < ℓ := by rw [hℓdef]; exact Real.log_pos (by linarith)
  have hℓnn : 0 ≤ ℓ := hℓpos.le
  have hFmnn : 0 ≤ Fm := by rw [hFmdef]; positivity
  have hτnn : 0 ≤ τ := by rw [hτdef]; positivity
  have hLDpos : 0 < LD := by rw [hLDdef]; exact Real.log_pos hD1
  have hLDnn : 0 ≤ LD := hLDpos.le
  have hRlog : ℓ = (θ / 2 - δ) * Real.log (N : ℝ) := by
    rw [hℓdef]
    exact Real.log_rpow (by exact_mod_cast hNpos) (θ / 2 - δ)
  have hLDle : LD ≤ CLD * ℓ := by
    have hlogDleN : LD ≤ Real.log (N : ℝ) := by
      rw [hLDdef]; exact Real.log_le_log (by linarith) (PrimeGaps.D₀_le_self hNe.le)
    rw [hCLDdef, hRlog, one_div, inv_mul_eq_div, le_div_iff₀ hcθ,
      mul_comm (θ / 2 - δ) (Real.log (N : ℝ))]
    exact mul_le_mul_of_nonneg_right hlogDleN hcθ.le
  have hb1 : 1 + ellV (W N) ≤ c₁ * LD := by rw [hLDdef]; exact hH1 N hN1
  have hb2 : τ * (8 * Real.log (2 * (W N : ℝ)) + 64) / ℓ ≤ c₂ * q * LD := by
    rw [hτdef, hℓdef, hqdef, hLDdef]; exact hH2 N hN2
  have hb3 : τ * (R ^ (-(1 : ℝ) / 8) * Real.log (2 * (W N : ℝ) * R)) ≤ c₃ * q * LD := by
    rw [hτdef, hqdef, hLDdef]; exact hH3 N hN3
  have hzpow_nn : 0 ≤ R ^ (-(1 : ℝ) / 8) := (Real.rpow_pos_of_pos (by linarith) _).le
  have hW1R : (1 : ℝ) ≤ (W N : ℝ) := by exact_mod_cast hWpos
  have hznn : (0 : ℝ) ≤ R := by linarith only [hR2]
  have hlogRle : ℓ ≤ Real.log (2 * (W N : ℝ) * R) := by
    rw [hℓdef]; apply Real.log_le_log (by linarith only [hR2])
    linarith only [mul_nonneg hznn (by linarith only [hW1R] : (0 : ℝ) ≤ 2 * (W N : ℝ) - 1)]
  have hlogRnn : 0 ≤ Real.log (2 * (W N : ℝ) * R) := hℓnn.trans hlogRle
  have hplsnn : 0 ≤ ellV (W N) := PrimeGaps.ellV_nonneg (W N)
  set Bc' : ℝ := 2 * q * ℓ + Ch₁ (1 / 2) 0 * q * (1 + ellV (W N)) +
      Ch₂ (1 / 2) 0 * τ * (R ^ (-(1 : ℝ) / 8) * (Real.log (2 * (W N : ℝ) * R) + ℓ)) with hBc'def
  set Pe' : ℝ := 2 * (3 * Fm) * (2 * Cs₁ (1 / 2) 0 * q * (1 + ellV (W N)) +
          Cs₂ (1 / 2) 0 * τ * (R ^ (-(1 : ℝ) / 8) * Real.log (2 * (W N : ℝ) * R) +
              (8 * Real.log (2 * (W N : ℝ)) + 64) / ℓ)) with hPe'def
  have hBc_le : Bc' ≤ Cbox * q * ℓ := by
    have e1 : Ch₁ (1 / 2) 0 * q * (1 + ellV (W N)) ≤ Ch₁ (1 / 2) 0 * c₁ * CLD * (q * ℓ) := by
      have s1 : Ch₁ (1 / 2) 0 * q * (1 + ellV (W N)) ≤ Ch₁ (1 / 2) 0 * q * (c₁ * LD) :=
        mul_le_mul_of_nonneg_left hb1 (by positivity)
      have s2 : Ch₁ (1 / 2) 0 * q * (c₁ * LD) ≤ Ch₁ (1 / 2) 0 * c₁ * CLD * (q * ℓ) := by
        have hqL : q * LD ≤ q * (CLD * ℓ) := mul_le_mul_of_nonneg_left hLDle hqnn
        have hc : 0 ≤ Ch₁ (1 / 2) 0 * c₁ := mul_nonneg hCh₁'.le hc₁.le
        calc Ch₁ (1 / 2) 0 * q * (c₁ * LD) = (Ch₁ (1 / 2) 0 * c₁) * (q * LD) := by ring
          _ ≤ (Ch₁ (1 / 2) 0 * c₁) * (q * (CLD * ℓ)) := mul_le_mul_of_nonneg_left hqL hc
          _ = Ch₁ (1 / 2) 0 * c₁ * CLD * (q * ℓ) := by ring
      linarith
    have e2 : Ch₂ (1 / 2) 0 * τ * (R ^ (-(1 : ℝ) / 8) * (Real.log (2 * (W N : ℝ) * R) + ℓ)) ≤
        2 * (Ch₂ (1 / 2) 0 * c₃ * CLD) * (q * ℓ) := by
      have hsum_le : R ^ (-(1 : ℝ) / 8) * (Real.log (2 * (W N : ℝ) * R) + ℓ) ≤
          2 * (R ^ (-(1 : ℝ) / 8) * Real.log (2 * (W N : ℝ) * R)) := by
        linarith only [mul_nonneg hzpow_nn (sub_nonneg.mpr hlogRle)]
      have hstep : Ch₂ (1 / 2) 0 * τ * (R ^ (-(1 : ℝ) / 8) * (Real.log (2 * (W N : ℝ) * R) + ℓ)) ≤
          Ch₂ (1 / 2) 0 * (2 * (c₃ * q * LD)) := by
        have h1 : τ * (R ^ (-(1 : ℝ) / 8) * (Real.log (2 * (W N : ℝ) * R) + ℓ)) ≤
            2 * (c₃ * q * LD) :=
          calc τ * (R ^ (-(1 : ℝ) / 8) * (Real.log (2 * (W N : ℝ) * R) + ℓ))
              ≤ τ * (2 * (R ^ (-(1 : ℝ) / 8) * Real.log (2 * (W N : ℝ) * R))) :=
                mul_le_mul_of_nonneg_left hsum_le hτnn
            _ = 2 * (τ * (R ^ (-(1 : ℝ) / 8) * Real.log (2 * (W N : ℝ) * R))) := by ring
            _ ≤ 2 * (c₃ * q * LD) := by linarith [hb3]
        calc Ch₂ (1 / 2) 0 * τ * (R ^ (-(1 : ℝ) / 8) * (Real.log (2 * (W N : ℝ) * R) + ℓ))
            = Ch₂ (1 / 2) 0 * (τ * (R ^ (-(1 : ℝ) / 8) *
                (Real.log (2 * (W N : ℝ) * R) + ℓ))) := by ring
          _ ≤ Ch₂ (1 / 2) 0 * (2 * (c₃ * q * LD)) := mul_le_mul_of_nonneg_left h1 hCh₂'.le
      have hLDCLD : q * LD ≤ q * (CLD * ℓ) := mul_le_mul_of_nonneg_left hLDle hqnn
      have hfin : Ch₂ (1 / 2) 0 * (2 * (c₃ * q * LD)) ≤
          2 * (Ch₂ (1 / 2) 0 * c₃ * CLD) * (q * ℓ) := by
        have hc : 0 ≤ 2 * (Ch₂ (1 / 2) 0 * c₃) := by positivity
        calc Ch₂ (1 / 2) 0 * (2 * (c₃ * q * LD)) = (2 * (Ch₂ (1 / 2) 0 * c₃)) * (q * LD) := by ring
          _ ≤ (2 * (Ch₂ (1 / 2) 0 * c₃)) * (q * (CLD * ℓ)) := mul_le_mul_of_nonneg_left hLDCLD hc
          _ = 2 * (Ch₂ (1 / 2) 0 * c₃ * CLD) * (q * ℓ) := by ring
      linarith [hstep, hfin]
    rw [hBc'def, hCboxdef]
    linarith only [e1, e2]
  have hPe_le : Pe' ≤ Cp * Fm * q * LD := by
    have hinner : 2 * Cs₁ (1 / 2) 0 * q * (1 + ellV (W N)) +
          Cs₂ (1 / 2) 0 * τ * (R ^ (-(1 : ℝ) / 8) * Real.log (2 * (W N : ℝ) * R) +
              (8 * Real.log (2 * (W N : ℝ)) + 64) / ℓ) ≤
        (2 * Cs₁ (1 / 2) 0 * c₁ + Cs₂ (1 / 2) 0 * (c₂ + c₃)) * q * LD := by
      have hb2' : τ * ((8 * Real.log (2 * (W N : ℝ)) + 64) / ℓ) ≤ c₂ * q * LD := by
        rw [← mul_div_assoc]; exact hb2
      have hsum : τ * (R ^ (-(1 : ℝ) / 8) * Real.log (2 * (W N : ℝ) * R) +
              (8 * Real.log (2 * (W N : ℝ)) + 64) / ℓ) ≤ c₃ * q * LD + c₂ * q * LD := by
        have hexp : τ * (R ^ (-(1 : ℝ) / 8) * Real.log (2 * (W N : ℝ) * R) +
                (8 * Real.log (2 * (W N : ℝ)) + 64) / ℓ) =
            τ * (R ^ (-(1 : ℝ) / 8) * Real.log (2 * (W N : ℝ) * R)) +
              τ * ((8 * Real.log (2 * (W N : ℝ)) + 64) / ℓ) := by ring
        rw [hexp]; linarith [hb3, hb2']
      have ht1 : 2 * Cs₁ (1 / 2) 0 * q * (1 + ellV (W N)) ≤
          2 * Cs₁ (1 / 2) 0 * (q * (c₁ * LD)) :=
        calc 2 * Cs₁ (1 / 2) 0 * q * (1 + ellV (W N))
            = 2 * Cs₁ (1 / 2) 0 * (q * (1 + ellV (W N))) := by ring
          _ ≤ 2 * Cs₁ (1 / 2) 0 * (q * (c₁ * LD)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb1 hqnn)
                (by linarith only [hCs₁'.le])
      have ht2 : Cs₂ (1 / 2) 0 * τ * (R ^ (-(1 : ℝ) / 8) * Real.log (2 * (W N : ℝ) * R) +
              (8 * Real.log (2 * (W N : ℝ)) + 64) / ℓ) ≤
          Cs₂ (1 / 2) 0 * (c₃ * q * LD + c₂ * q * LD) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hsum hCs₂'.le
      linarith only [ht1, ht2]
    rw [hPe'def, hCpdef]
    refine le_trans (mul_le_mul_of_nonneg_left hinner (by linarith only [hFmnn]))
      (le_of_eq ?_)
    ring
  have hBc'nn : 0 ≤ Bc' := by
    rw [hBc'def]
    have t2nn : 0 ≤ Ch₁ (1 / 2) 0 * q * (1 + ellV (W N)) :=
      mul_nonneg (mul_nonneg hCh₁'.le hqnn) (by linarith only [hplsnn])
    have t3nn : 0 ≤ Ch₂ (1 / 2) 0 * τ * (R ^ (-(1 : ℝ) / 8) *
        (Real.log (2 * (W N : ℝ) * R) + ℓ)) := by
      have hin : 0 ≤ R ^ (-(1 : ℝ) / 8) * (Real.log (2 * (W N : ℝ) * R) + ℓ) :=
        mul_nonneg hzpow_nn (by linarith only [hℓnn, hlogRle])
      exact mul_nonneg (mul_nonneg hCh₂'.le hτnn) hin
    have t1nn : 0 ≤ 2 * q * ℓ :=
      mul_nonneg (mul_nonneg (by norm_num) hqnn) hℓnn
    linarith only [t1nn, t2nn, t3nn]
  have hPe'nn : 0 ≤ Pe' := by
    rw [hPe'def]
    have hi1 : 0 ≤ 1 + ellV (W N) := by linarith only [hplsnn]
    have hi2 : 0 ≤ R ^ (-(1 : ℝ) / 8) * Real.log (2 * (W N : ℝ) * R) := mul_nonneg hzpow_nn hlogRnn
    have hi3 : 0 ≤ (8 * Real.log (2 * (W N : ℝ)) + 64) / ℓ := by
      refine div_nonneg ?_ hℓnn
      linarith only [Real.log_nonneg (by linarith only [hW1R] : (1 : ℝ) ≤ 2 * (W N : ℝ))]
    have hinner : 0 ≤ 2 * Cs₁ (1 / 2) 0 * q * (1 + ellV (W N)) +
        Cs₂ (1 / 2) 0 * τ * (R ^ (-(1 : ℝ) / 8) * Real.log (2 * (W N : ℝ) * R) +
            (8 * Real.log (2 * (W N : ℝ)) + 64) / ℓ) := by
      have hsum : 0 ≤ R ^ (-(1 : ℝ) / 8) * Real.log (2 * (W N : ℝ) * R) +
          (8 * Real.log (2 * (W N : ℝ)) + 64) / ℓ := by linarith only [hi2, hi3]
      exact add_nonneg
        (mul_nonneg (mul_nonneg (by linarith only [hCs₁'.le]) hqnn) hi1)
        (mul_nonneg (mul_nonneg hCs₂'.le hτnn) hsum)
    exact mul_nonneg (by linarith only [hFmnn]) hinner
  have hCboxqℓnn : 0 ≤ Cbox * q * ℓ := mul_nonneg (mul_nonneg hCboxpos.le hqnn) hℓnn
  have hstepB : Bc' ^ (k - 1) ≤ (Cbox * q * ℓ) ^ (k - 1) := pow_le_pow_left₀ hBc'nn hBc_le _
  have hmul : (k : ℝ) * Bc' ^ (k - 1) * Pe' ≤
      (k : ℝ) * (Cbox * q * ℓ) ^ (k - 1) * (Cp * Fm * q * LD) := by
    apply mul_le_mul _ hPe_le hPe'nn (mul_nonneg (Nat.cast_nonneg k) (pow_nonneg hCboxqℓnn _))
    exact mul_le_mul_of_nonneg_left hstepB (Nat.cast_nonneg k)
  refine le_trans hmul ?_
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    simp only [Nat.cast_zero, zero_mul]
    positivity
  · have hqk : q ^ (k - 1) * q = q ^ k := pow_sub_one_mul hkpos.ne' q
    have hCbox_pow : (Cbox * q * ℓ) ^ (k - 1) = Cbox ^ (k - 1) * q ^ (k - 1) * ℓ ^ (k - 1) := by
      rw [mul_pow, mul_pow]
    have hcoef : (k : ℝ) * Cbox ^ (k - 1) * Cp ≤ (k : ℝ) * (max 1 Cbox) ^ k * Cp := by
      have h3 : Cbox ^ (k - 1) ≤ (max 1 Cbox) ^ k :=
        (pow_le_pow_left₀ hCboxpos.le (le_max_right _ _) _).trans
          (pow_le_pow_right₀ (le_max_left _ _) (by omega))
      calc (k : ℝ) * Cbox ^ (k - 1) * Cp = ((k : ℝ) * Cp) * Cbox ^ (k - 1) := by ring
        _ ≤ ((k : ℝ) * Cp) * (max 1 Cbox) ^ k :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = (k : ℝ) * (max 1 Cbox) ^ k * Cp := by ring
    have hqfact : ((W N).totient : ℝ) ^ k / (W N : ℝ) ^ k = q ^ k := by rw [hqdef, div_pow]
    have hFqLDnn : 0 ≤ Fm * q ^ k * ℓ ^ (k - 1) * LD := by positivity
    calc (k : ℝ) * (Cbox * q * ℓ) ^ (k - 1) * (Cp * Fm * q * LD)
        = ((k : ℝ) * Cbox ^ (k - 1) * Cp) * (Fm * (q ^ (k - 1) * q) * ℓ ^ (k - 1) * LD) := by
          rw [hCbox_pow]; ring
      _ = ((k : ℝ) * Cbox ^ (k - 1) * Cp) * (Fm * q ^ k * ℓ ^ (k - 1) * LD) := by rw [hqk]
      _ ≤ ((k : ℝ) * (max 1 Cbox) ^ k * Cp) * (Fm * q ^ k * ℓ ^ (k - 1) * LD) :=
          mul_le_mul_of_nonneg_right hcoef hFqLDnn
      _ ≤ ((k : ℝ) * (max 1 Cbox) ^ k * Cp + 1) * (Fm * q ^ k * ℓ ^ (k - 1) * LD) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hFqLDnn
      _ = ((k : ℝ) * (max 1 Cbox) ^ k * Cp + 1) * Fm * ((W N).totient : ℝ) ^ k * LD * ℓ ^ (k - 1) /
              (W N : ℝ) ^ k := by
          rw [← hqfact]; ring

end S1Aggregate

end PrimeGaps
