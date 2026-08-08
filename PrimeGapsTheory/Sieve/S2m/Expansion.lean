/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.PNT
public import PrimeGapsTheory.Sieve.S1.ExpansionBinomial
public import PrimeGapsTheory.Sieve.S2m.SijOne

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Expansion of the second-moment sieve sum

Rewrites the second-moment sieve sum using transformed weights.

## Main results

* `lem_S2m_expansion`: Expands the second-moment sieve count as a weighted double sum.
* `ymWeightedSum_to_diagonal`: Removes the off-diagonal `s` contribution from `ymWeightedSum`.
* `lem_S2m_from_ym`: Expresses the restricted sum in terms of the transformed weights.
-/

@[expose] public section

open scoped Finset
open scoped ArithmeticFunction.Moebius

open scoped ArithmeticFunction.detotient

namespace PrimeGaps
open PrimeGaps.SumOverDivisors

/-- Expanding the square: the prime-weighted sum of `(∑_{d ∈ D, d ∣ n + h} λ d) ^ 2` over
`n ∈ Ioc N (2 * N)` in the residue class `v₀ mod W` equals `∑ d, ∑ e, λ d * λ e` times the weighted
count of such `n` with `lcm (d i) (e i) ∣ n + h i` for every `i`. -/
@[pg_tag "bg246" "lem_S2m_expansion"]
theorem lem_S2m_expansion (N W v_0 : ℕ) (k : ℕ) (h : Fin k → ℕ) (m : Fin k) (D : Finset (Fin k → ℕ))
    (lam : (Fin k → ℕ) →₀ ℝ) :
    (∑ n ∈ Finset.Ioc N (2 * N), if n % W = v_0 % W then
          PrimeGaps.primeIndicator (n + h m) *
          (∑ d ∈ D.filter (fun d ↦ ∀ i, d i ∣ n + h i), lam d) ^ 2
        else 0) =
    ∑ d ∈ D, ∑ e ∈ D, lam d * lam e *
      (∑ n ∈ Finset.Ioc N (2 * N), if n % W = v_0 % W ∧ ∀ i, Nat.lcm (d i) (e i) ∣ n + h i then
            PrimeGaps.primeIndicator (n + h m)
          else 0) :=
  lem_expansion_general N W v_0 k h (fun n ↦ PrimeGaps.primeIndicator (n + h m)) D lam
end PrimeGaps

open ArithmeticFunction GPYSieveS1 PrimeGaps.LemS1RestrictSij

namespace PrimeGaps

/-- The boxes `Ubox k R`, `Sbox k R` capture every guarded `(u, s)` whose two `ym` factors are both
nonzero. -/
lemma from_ym_box_support {k : ℕ} (m : Fin k) (l : (Fin k → ℕ) →₀ ℝ) (R : ℝ) (W : ℕ)
    (hlam : l.HasPermissibleSupport ⌊R⌋₊ W) :
    ∀ u s, ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
          RestrictedCoprime u s) → PrimeGaps.ym m l (boldA u s) ≠ 0 →
            PrimeGaps.ym m l (boldB u s) ≠ 0 →
          u ∈ Ubox k R ∧ s ∈ Sbox k R := by
  intro u s hguard hA _
  obtain ⟨hu1, hsii, hsij1, _⟩ := hguard
  exact mem_Ubox_Sbox_of_boldA_le R u s hu1 hsii hsij1
    fun i ↦ PrimeGaps.ym_coord_le_floor m l R W hlam (boldA u s) hA i

/-- `ymWeightedSum m l = S2mYm m l (Ubox k R) (Sbox k R)` for `l` of permissible support. -/
lemma ymWeightedSum_eq_box {k : ℕ} (m : Fin k) (l : (Fin k → ℕ) →₀ ℝ) (R : ℝ) (W : ℕ)
    (hlam : l.HasPermissibleSupport ⌊R⌋₊ W) :
    ymWeightedSum m l = S2mYm m l (Ubox k R) (Sbox k R) :=
  S2mYm_eq_ymWeightedSum m l _ _ (from_ym_box_support m l R W hlam)

/-- The `ymWeightedSum` summand (as in `S2mYm` ). -/
noncomputable def Fsum {k : ℕ} (m : Fin k) (l : (Fin k → ℕ) →₀ ℝ)
    (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ) : ℝ :=
  if (∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧ RestrictedCoprime u s then
      (∏ i, (μ (u i) : ℝ) ^ 2 / (g (u i) : ℝ)) *
      (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
          (μ (s p.1 p.2) : ℝ) / (g (s p.1 p.2) : ℝ) ^ 2) *
      PrimeGaps.ym m l (boldA u s) * PrimeGaps.ym m l (boldB u s)
    else 0

/-- The `sij_D0` fixed-pair summand at pair `p`. -/
noncomputable def Gsum {k : ℕ} (m : Fin k) (l : (Fin k → ℕ) →₀ ℝ) (N : ℕ)
    (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ) (p : Fin k × Fin k) : ℝ :=
  |(if (∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
        RestrictedCoprime u s ∧ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < s p.1 p.2 then
      (∏ i, (μ (u i) : ℝ) ^ 2 / (g (u i) : ℝ)) *
      (∏ q ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
          (μ (s q.1 q.2) : ℝ) / (g (s q.1 q.2) : ℝ) ^ 2) *
      PrimeGaps.ym m l (boldA u s) * PrimeGaps.ym m l (boldB u s)
    else 0)|

/-- `Gsum` is nonnegative, being an absolute value. -/
lemma Gsum_nonneg {k : ℕ} (m : Fin k) (l : (Fin k → ℕ) →₀ ℝ) (N : ℕ)
    (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ) (p : Fin k × Fin k) :
    0 ≤ Gsum m l N u s p := abs_nonneg _

/-- Off the diagonal `s = 1`, `|Fsum m l u s| ≤ ∑ p ∈ univ.offDiag, Gsum m l N u s p`: some entry of
`s` must exceed `⌊D₀ N⌋₊`, since every prime up to `⌊D₀ N⌋₊` divides `W`. -/
lemma from_ym_covering {k : ℕ} (m : Fin k) (l : (Fin k → ℕ) →₀ ℝ) (N : ℕ) (R : ℝ)
    (W : ℕ) (hsmall : ∀ p, p.Prime → p ≤ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ → p ∣ W)
    (hlam : l.HasPermissibleSupport ⌊R⌋₊ W)
    (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ) (hs1 : s ≠ fun _ _ ↦ 1) :
    |Fsum m l u s| ≤ ∑ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)), Gsum m l N u s p := by
  classical
  unfold Fsum
  by_cases hg : (∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
        RestrictedCoprime u s
  · rw [if_pos hg]
    obtain ⟨hu1, hsii, hsij1, hRA⟩ := hg
    by_cases hB : PrimeGaps.ym m l (boldB u s) = 0
    · rw [hB, mul_zero, abs_zero]
      exact Finset.sum_nonneg (fun p _ ↦ Gsum_nonneg m l N u s p)
    · obtain ⟨a, ha⟩ := Function.ne_iff.mp hs1
      obtain ⟨b, hb⟩ := Function.ne_iff.mp ha
      have hab : a ≠ b := by rintro rfl; exact hb (hsii a)
      have hs2 : 2 ≤ s a b := by have := hsij1 a b hab; omega
      obtain ⟨q, hqp, hqd⟩ := (s a b).exists_prime_and_dvd (by omega)
      have hsgt : ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < s a b :=
        (pairMasterG_sij_prime_guard R W ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ hsmall m l hlam u s a b hab hB
          q hqp hqd).trans_le (Nat.le_of_dvd (by omega) hqd)
      have hmem : (a, b) ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)) :=
        Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hab⟩
      refine le_of_eq_of_le ?_ (Finset.single_le_sum (f := fun p ↦ Gsum m l N u s p)
        (fun p _ ↦ Gsum_nonneg m l N u s p) hmem)
      unfold Gsum
      rw [if_pos ⟨hu1, hsii, hsij1, hRA, hsgt⟩]
  · rw [if_neg hg, abs_zero]
    exact Finset.sum_nonneg (fun p _ ↦ Gsum_nonneg m l N u s p)

/-- At the all-ones `s` both `boldA` and `boldB` collapse to `u`, so `Fsum` reduces to
`(∏ i, μ(uᵢ)² / g(uᵢ)) * ym m l u * ym m l u` under the guard. -/
lemma Fsum_diag {k : ℕ} (m : Fin k) (l : (Fin k → ℕ) →₀ ℝ) (u : Fin k → ℕ) :
    Fsum m l u (fun _ _ ↦ 1) = (if (∀ i, 1 ≤ u i) ∧ RestrictedCoprime u (fun _ _ ↦ 1) then
          (∏ i, (μ (u i) : ℝ) ^ 2 / (g (u i) : ℝ)) * PrimeGaps.ym m l u * PrimeGaps.ym m l u
        else 0) := by
  unfold Fsum
  have hbA : boldA u (fun _ _ ↦ 1) = u := by funext j; unfold boldA; simp
  have hbB : boldB u (fun _ _ ↦ 1) = u := by funext j; unfold boldB; simp
  have hprod1 : (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
      (μ ((fun _ _ ↦ 1 : Fin k → Fin k → ℕ) p.1 p.2) : ℝ) /
        (g ((fun _ _ ↦ 1 : Fin k → Fin k → ℕ) p.1 p.2) : ℝ) ^ 2) = 1 :=
    Finset.prod_eq_one fun p _ ↦ by simp [detotient_one]
  rw [hbA, hbB, hprod1]
  by_cases hg : (∀ i, 1 ≤ u i) ∧ RestrictedCoprime u (fun _ _ ↦ 1)
  · rw [if_pos ⟨hg.1, fun _ ↦ rfl, fun _ _ _ ↦ le_rfl, hg.2⟩, if_pos hg]; ring
  · rw [if_neg (fun hcon ↦ hg ⟨hcon.1, hcon.2.2.2⟩), if_neg hg]

/-- `Fsum m l u s ≠ 0` forces `u ∈ Ubox k R` and `s ∈ Sbox k R`. -/
lemma Fsum_mem {k : ℕ} (m : Fin k) (l : (Fin k → ℕ) →₀ ℝ) (R : ℝ) (W : ℕ)
    (hlam : l.HasPermissibleSupport ⌊R⌋₊ W)
    (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ)
    (h0 : Fsum m l u s ≠ 0) :
    u ∈ Ubox k R ∧ s ∈ Sbox k R := by
  rw [Fsum] at h0
  by_cases hg : (∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
        RestrictedCoprime u s
  · rw [if_pos hg] at h0
    have hA : PrimeGaps.ym m l (boldA u s) ≠ 0 := fun hz ↦ h0 (by rw [hz]; ring)
    have hB : PrimeGaps.ym m l (boldB u s) ≠ 0 := fun hz ↦ h0 (by rw [hz]; ring)
    exact from_ym_box_support m l R W hlam u s hg hA hB
  · rw [if_neg hg] at h0; exact absurd rfl h0

/-- `Gsum m l N u s p ≠ 0` forces `u ∈ Ubox k R` and `s ∈ Sbox k R`. -/
lemma Gsum_mem {k : ℕ} (m : Fin k) (l : (Fin k → ℕ) →₀ ℝ) (N : ℕ) (R : ℝ) (W : ℕ)
    (hlam : l.HasPermissibleSupport ⌊R⌋₊ W)
    (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ)
    (p : Fin k × Fin k) (h0 : Gsum m l N u s p ≠ 0) :
    u ∈ Ubox k R ∧ s ∈ Sbox k R := by
  rw [Gsum, abs_ne_zero] at h0
  by_cases hg : (∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
        RestrictedCoprime u s ∧ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < s p.1 p.2
  · rw [if_pos hg] at h0
    have hA : PrimeGaps.ym m l (boldA u s) ≠ 0 := fun hz ↦ h0 (by rw [hz]; ring)
    have hB : PrimeGaps.ym m l (boldB u s) ≠ 0 := fun hz ↦ h0 (by rw [hz]; ring)
    exact from_ym_box_support m l R W hlam u s ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1⟩ hA hB
  · rw [if_neg hg] at h0; exact absurd rfl h0

/-- The double `tsum` of `Gsum` collapses to the finite sum over `Ubox k R × Sbox k R`. -/
lemma Gsum_tsum_eq {k : ℕ} (m : Fin k) (l : (Fin k → ℕ) →₀ ℝ)
    (N : ℕ) (R : ℝ) (W : ℕ) (hlam : l.HasPermissibleSupport ⌊R⌋₊ W)
    (p : Fin k × Fin k) :
    (∑' (u : Fin k → ℕ), ∑' (s : Fin k → Fin k → ℕ), Gsum m l N u s p) =
      ∑ u ∈ Ubox k R, ∑ s ∈ Sbox k R, Gsum m l N u s p :=
  tsum_tsum_eq_sum_sum (fun u s ↦ Gsum m l N u s p) _ _
    fun u s hc ↦ Gsum_mem m l N R W hlam u s p hc

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- The `s_{ij}` off-diagonal removal from `lem_S2m_from_ym`, isolated
from both the prime-distribution substitution and the PNT conversion.
This is the reusable arithmetic bridge needed when the CRT/BV step is
proved with a sharper outer-support argument. -/
theorem ymWeightedSum_to_diagonal {k : ℕ} (m : Fin k) (hk : 2 ≤ k)
    (θ δ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2)) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ l : (Fin k → ℕ) →₀ ℝ, l.HasPermissibleSupport ⌊R⌋₊ (W N) →
        |(Nat.primeCountingIoc N (2 * N) : ℝ) / (Nat.totient (W N) : ℝ) * ymWeightedSum m l -
          (Nat.primeCountingIoc N (2 * N) : ℝ) / (Nat.totient (W N) : ℝ) * (∑' u : Fin k → ℕ,
                  if (∀ i, 1 ≤ u i) ∧ RestrictedCoprime u (fun _ _ ↦ 1)
                  then PrimeGaps.ym m l u ^ 2 / ∏ i, (g (u i) : ℝ)
                  else 0)| ≤ C * (⨆ r, |PrimeGaps.ym m l r|) ^ 2 *
              (Nat.totient (W N) : ℝ) ^ (k - 2) *
              (N : ℝ) * (Real.log N) ^ (k - 2) / ((W N : ℝ) ^ (k - 1) * D₀ (N : ℝ)) := by
  obtain ⟨Cd0, hCd0, Nd0, hd0⟩ := lem_S2m_sij_D0 m θ δ hθ hδ
  let cardOD := #(Finset.univ.offDiag : Finset (Fin k × Fin k))
  obtain ⟨nD0, hnD0⟩ := Filter.eventually_atTop.mp eventually_D0_pos.natCast_atTop
  refine ⟨(cardOD : ℝ) * Cd0 + 1,
    by linarith only [mul_nonneg (Nat.cast_nonneg cardOD) hCd0.le], ?_⟩
  refine ⟨max Nd0 (max (nD0 : ℝ) 2), ?_⟩
  intro N hN l hlam
  simp only [max_le_iff] at hN
  obtain ⟨hNd0N, hnD0N, hN2R⟩ := hN
  have hN2 : 2 ≤ N := by exact_mod_cast hN2R
  have hNposR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogNpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
  have hexpo : 0 < θ / 2 - δ := sub_pos.mpr hδ.2
  have hRdef : R = (N : ℝ) ^ (θ / 2 - δ) := rfl
  have hlogR : Real.log R = (θ / 2 - δ) * Real.log N := by
    rw [hRdef, Real.log_rpow hNposR]
  have hlogRle : Real.log R ≤ Real.log N := by
    rw [hlogR]
    linarith only [mul_nonneg (by linarith only [hθ.2, hδ.1] : (0 : ℝ) ≤ 1 - (θ / 2 -
      δ)) hlogNpos.le]
  have hlogRpos : 0 ≤ Real.log R := by
    rw [hlogR]
    positivity
  have hRge1 : (1 : ℝ) ≤ R := by
    rw [hRdef, ← Real.one_rpow (θ / 2 - δ)]
    exact Real.rpow_le_rpow (by norm_num)
      (by exact_mod_cast (by omega : 1 ≤ N)) hexpo.le
  have hM1 : 1 ≤ ⌊R⌋₊ :=
    Nat.le_floor (by exact_mod_cast hRge1 : ((1 : ℕ) : ℝ) ≤ _)
  have hφpos : (0 : ℝ) < (Nat.totient (W N) : ℝ) := PrimeGaps.totient_W_pos
  have hD0pos : 0 < D₀ (N : ℝ) := hnD0 N (by exact_mod_cast hnD0N)
  have hone := lem_S2m_sij_one N (W N) m l
  have hYbox : ymWeightedSum m l = ∑ u ∈ Ubox k R, ∑ s ∈ Sbox k R, Fsum m l u s := by
    rw [ymWeightedSum_eq_box m l R (W N) hlam]
    rfl
  have h1mem : (fun _ _ ↦ (1 : ℕ)) ∈ Sbox k R := by
    simp only [Sbox, Fintype.mem_piFinset, Finset.mem_Iic]
    exact fun _ _ ↦ hM1
  let Ysum := ymWeightedSum m l
  let Sig : ℝ := ∑' u : Fin k → ℕ, if (∀ i, 1 ≤ u i) ∧ RestrictedCoprime u (fun _ _ ↦ 1)
    then PrimeGaps.ym m l u ^ 2 / ∏ i, (g (u i) : ℝ) else 0
  have hS1box : (∑' u : Fin k → ℕ, if (∀ i, 1 ≤ u i) ∧ RestrictedCoprime u (fun _ _ ↦ 1)
        then (∏ i, (μ (u i) : ℝ) ^ 2 / (g (u i) : ℝ)) *
              PrimeGaps.ym m l u * PrimeGaps.ym m l u else 0) = ∑ u ∈ Ubox k R,
          Fsum m l u (fun _ _ ↦ 1) :=
    (tsum_congr fun u ↦ (Fsum_diag m l u).symm).trans <|
      tsum_eq_sum fun u hu ↦ by by_contra hc; exact hu (Fsum_mem m l R (W N) hlam u _ hc).1
  rw [hS1box] at hone
  have hpref_nn : (0 : ℝ) ≤ (Nat.primeCountingIoc N (2 * N) : ℝ) / (Nat.totient (W N) : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hφpos.le
  have hYsub : Ysum - ∑ u ∈ Ubox k R, Fsum m l u (fun _ _ ↦ 1) = ∑ u ∈ Ubox k R,
          ∑ s ∈ (Sbox k R).erase (fun _ _ ↦ 1),
            Fsum m l u s := by
    dsimp [Ysum]
    rw [hYbox, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [← Finset.add_sum_erase _ (Fsum m l u) h1mem]
    ring
  have hsmall : ∀ p, p.Prime → p ≤ ⌊D₀ (N : ℝ)⌋₊ → p ∣ W N := fun p hp hpD ↦
    hp.dvd_W_iff_le_D₀.mpr ((Nat.le_floor_iff' hp.ne_zero).mp hpD)
  have hcov : |Ysum - ∑ u ∈ Ubox k R, Fsum m l u (fun _ _ ↦ 1)| ≤
      ∑ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)), ∑ u ∈ Ubox k R,
            ∑ s ∈ Sbox k R, Gsum m l N u s p := by
    rw [hYsub]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun u _ ↦ (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun s hs ↦ from_ym_covering m l N R (W N) hsmall hlam u s
            (Finset.mem_erase.mp hs).1)).trans ?_
    have hstep : (∑ u ∈ Ubox k R, ∑ s ∈ (Sbox k R).erase (fun _ _ ↦ 1),
            ∑ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
              Gsum m l N u s p) ≤ ∑ u ∈ Ubox k R,
            ∑ s ∈ Sbox k R,
              ∑ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)), Gsum m l N u s p :=
      Finset.sum_le_sum (fun u _ ↦ Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun s _ _ ↦ Finset.sum_nonneg (fun p _ ↦ Gsum_nonneg m l N u s p)))
    exact hstep.trans
      (le_of_eq ((Finset.sum_congr rfl fun u _ ↦ Finset.sum_comm).trans Finset.sum_comm))
  have hlogbound : Real.log R ^ (k - 1) / Real.log N ≤ Real.log N ^ (k - 2) := by
    rw [div_le_iff₀ hlogNpos, show k - 1 = (k - 2) + 1 from by omega, pow_succ]
    exact mul_le_mul (pow_le_pow_left₀ hlogRpos hlogRle _) hlogRle hlogRpos
      (pow_nonneg (hlogRpos.trans hlogRle) _)
  let E : ℝ := (⨆ r, |PrimeGaps.ym m l r|) ^ 2 * (Nat.totient (W N) : ℝ) ^ (k - 2) *
      (N : ℝ) * Real.log N ^ (k - 2) / ((W N : ℝ) ^ (k - 1) * D₀ (N : ℝ))
  have hEnn : 0 ≤ E := by dsimp [E]; positivity
  have hpair : ∀ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
      (Nat.primeCountingIoc N (2 * N) : ℝ) / (Nat.totient (W N) : ℝ) * (∑ u ∈ Ubox k R,
            ∑ s ∈ Sbox k R, Gsum m l N u s p) ≤ Cd0 * E := by
    intro p hp
    have hp' : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
    have hbase := hd0 N hNd0N l hlam p.1 p.2 hp'
    rw [← Gsum_tsum_eq m l N R (W N) hlam p]
    refine hbase.trans ?_
    have hAB : 0 ≤ Cd0 * (⨆ r, |PrimeGaps.ym m l r|) ^ 2 *
        (Nat.totient (W N) : ℝ) ^ (k - 2) * (N : ℝ) /
        ((W N : ℝ) ^ (k - 1) * D₀ (N : ℝ)) := by
      have := hCd0.le
      positivity
    dsimp [E]
    calc
      Cd0 * (⨆ r, |PrimeGaps.ym m l r|) ^ 2 * (Nat.totient (W N) : ℝ) ^ (k - 2) * (N : ℝ) *
            Real.log R ^ (k - 1) /
            ((W N : ℝ) ^ (k - 1) * D₀ (N : ℝ) * Real.log N) =
          (Cd0 * (⨆ r, |PrimeGaps.ym m l r|) ^ 2 * (Nat.totient (W N) : ℝ) ^ (k - 2) * (N : ℝ) /
                ((W N : ℝ) ^ (k - 1) * D₀ (N : ℝ))) *
            (Real.log R ^ (k - 1) /
                Real.log N) := by field_simp
      _ ≤ (Cd0 * (⨆ r, |PrimeGaps.ym m l r|) ^ 2 * (Nat.totient (W N) : ℝ) ^ (k - 2) * (N : ℝ) /
              ((W N : ℝ) ^ (k - 1) * D₀ (N : ℝ))) * Real.log N ^ (k - 2) :=
        mul_le_mul_of_nonneg_left hlogbound hAB
      _ = Cd0 * ((⨆ r, |PrimeGaps.ym m l r|) ^ 2 * (Nat.totient (W N) : ℝ) ^ (k - 2) * (N : ℝ) *
              Real.log N ^ (k - 2) / ((W N : ℝ) ^ (k - 1) * D₀ (N : ℝ))) := by field_simp
  have hsumpair : (Nat.primeCountingIoc N (2 * N) : ℝ) / (Nat.totient (W N) : ℝ) *
        ∑ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)), (∑ u ∈ Ubox k R, ∑ s ∈ Sbox k R,
                Gsum m l N u s p) ≤ (cardOD : ℝ) * (Cd0 * E) := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum hpair).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  have hstepII :
      |(Nat.primeCountingIoc N (2 * N) : ℝ) / (Nat.totient (W N) : ℝ) * Ysum -
        (Nat.primeCountingIoc N (2 * N) : ℝ) / (Nat.totient (W N) : ℝ) * Sig| ≤
      (cardOD : ℝ) * (Cd0 * E) := by
    have heq : (Nat.primeCountingIoc N (2 * N) : ℝ) / (Nat.totient (W N) : ℝ) * Ysum -
          (Nat.primeCountingIoc N (2 * N) : ℝ) / (Nat.totient (W N) : ℝ) * Sig =
        (Nat.primeCountingIoc N (2 * N) : ℝ) / (Nat.totient (W N) : ℝ) * (Ysum - ∑ u ∈ Ubox k R,
                Fsum m l u (fun _ _ ↦ 1)) := by
      rw [← hone]
      ring
    rw [heq, abs_mul, abs_of_nonneg hpref_nn]
    exact (mul_le_mul_of_nonneg_left hcov hpref_nn).trans hsumpair
  refine hstepII.trans (le_of_eq_of_le
    (by ring : (cardOD : ℝ) * (Cd0 * E) = (cardOD : ℝ) * Cd0 * E) ?_)
  refine (mul_le_mul_of_nonneg_right (by linarith :
    (cardOD : ℝ) * Cd0 ≤ (cardOD : ℝ) * Cd0 + 1) hEnn).trans (le_of_eq ?_)
  dsimp only [E]
  ring

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- `S₂m` is approximated by the diagonal transformed-weight sum
`(N / (φ(W N) * log N)) * ∑' u, ym m L u ^ 2 / ∏ i, g (u i)`, with an off-diagonal coupling error
and a level-of-distribution error. -/
@[pg_tag "bg246" "lem_S2m_from_ym"]
theorem lem_S2m_from_ym {k : ℕ} (m : Fin k) (hk : 2 ≤ k)
    (h : Fin k → ℕ) (hinj : Function.Injective h)
    (θ δ : ℝ) (hθ0 : 0 < θ) (hθ : θ < 1 / 2) (hδ : 0 < δ) (hδθ : δ < θ / 2)
    (hLD : Nat.HasLevelOfDistribution Set.univ θ 1)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ w₀ : ZMod (W N),
        (∀ i, ((w₀.val : ℤ) + h i).gcd (W N) = 1) →
      ∀ L : (Fin k → ℕ) →₀ ℝ, (∀ d, L d ≠ 0 → d ∈ Finset.permissibleSupport k ⌊(N : ℝ) ^ (θ / 2 -
        δ)⌋₊ (primorial ⌊PrimeGaps.D₀ (N : ℝ)⌋₊)) →
        L.HasPermissibleSupport ⌊R⌋₊ (W N) →
        |PrimeGaps.S₂m h (⇑L) N w₀ m - ((N : ℝ) / ((Nat.totient (W N) : ℝ) *
          Real.log N)) * (∑' u : Fin k → ℕ, if (∀ i, 1 ≤ u i) ∧ RestrictedCoprime u (fun _ _ ↦ 1)
                    then PrimeGaps.ym m L u ^ 2 / ∏ i, (g (u i) : ℝ)
                    else 0)| ≤
          C * (⨆ r, |PrimeGaps.ym m L r|) ^ 2 * (Nat.totient (W N) : ℝ) ^ (k - 2) *
              (N : ℝ) * (Real.log N) ^ (k - 2) /
              ((W N : ℝ) ^ (k - 1) * PrimeGaps.D₀ (N : ℝ)) +
            C * (Finsupp.maxRealAbs (PrimeGaps.lToY L)) ^ 2 * (N : ℝ) / (Real.log N) ^ A := by
  obtain ⟨Csub, Nsub, hCsub, hNsub, hsub⟩ :=
    lem_S2m_substitute_ym hk h m hinj θ δ hδ hδθ hθ hLD A hA
  obtain ⟨Cpnt, hCpnt, Npnt, hpnt⟩ :=
    lem_S2m_PNT m θ δ hk ⟨hθ0, by linarith⟩ ⟨hδ, hδθ⟩
  obtain ⟨Cdiag, hCdiag, Ndiag, hdiag⟩ :=
    ymWeightedSum_to_diagonal m hk θ δ ⟨hθ0, by linarith⟩ ⟨hδ, hδθ⟩
  obtain ⟨nD0, hnD0⟩ := Filter.eventually_atTop.mp eventually_D0_pos.natCast_atTop
  refine ⟨Cdiag + Cpnt + Csub, by linarith only [hCdiag, hCpnt, hCsub], ?_⟩
  refine ⟨max (max Nsub Npnt) (max Ndiag (max (nD0 : ℝ) 2)), ?_⟩
  intro N hN w₀ hw₀ L hsupp hlam
  let l : (Fin k → ℕ) →₀ ℝ := L
  simp only [max_le_iff] at hN
  obtain ⟨⟨hNsubN, hNpntN⟩, hNdiagN, hnD0N, hN2R⟩ := hN
  have hN2 : 2 ≤ N := by exact_mod_cast hN2R
  have hlogNpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
  have hD0pos : 0 < PrimeGaps.D₀ (N : ℝ) := hnD0 N (by exact_mod_cast hnD0N)
  have hsupp' : L.HasPermissibleSupport ⌊(N : ℝ) ^ (θ / 2 - δ)⌋₊ (primorial ⌊D₀ (N : ℝ)⌋₊) :=
    Finsupp.HasPermissibleSupport.of_forall fun d hd ↦
      Finset.mem_permissibleSupport_iff.mp (hsupp d hd)
  have hI := hsub N hNsubN w₀ hw₀ L hsupp'
  have hIII := hpnt N hNpntN l hlam
  have hstepII := hdiag N hNdiagN l hlam
  set Ysum := ymWeightedSum m l
  set Sig : ℝ := (∑' u : Fin k → ℕ, if (∀ i, 1 ≤ u i) ∧ RestrictedCoprime u (fun _ _ ↦ 1)
      then PrimeGaps.ym m l u ^ 2 / ∏ i, (g (u i) : ℝ) else 0)
  have hT1nn : (0 : ℝ) ≤ (⨆ r, |PrimeGaps.ym m l r|) ^ 2 * (Nat.totient (W N) : ℝ) ^ (k - 2) *
      (N : ℝ) * (Real.log N) ^ (k - 2) / ((W N : ℝ) ^ (k - 1) *
        PrimeGaps.D₀ (N : ℝ)) := div_nonneg (by positivity) (by positivity)
  set pref := (Nat.primeCountingIoc N (2 * N) : ℝ) / (Nat.totient (W N) : ℝ)
  have htri : |PrimeGaps.S₂m h l N w₀ m -
        ((N : ℝ) / ((Nat.totient (W N) : ℝ) * Real.log N)) * Sig| ≤
      |PrimeGaps.S₂m h l N w₀ m - pref * Ysum| + |pref * Ysum - pref * Sig| +
        |pref * Sig - ((N : ℝ) / ((Nat.totient (W N) : ℝ) * Real.log N)) *
          Sig| := by
    have t1 := abs_sub_le (PrimeGaps.S₂m h l N w₀ m) (pref * Ysum)
      (((N : ℝ) / ((Nat.totient (W N) : ℝ) * Real.log N)) * Sig)
    have t2 := abs_sub_le (pref * Ysum) (pref * Sig)
      (((N : ℝ) / ((Nat.totient (W N) : ℝ) * Real.log N)) * Sig)
    linarith
  have he2nn : (0 : ℝ) ≤ (Finsupp.maxRealAbs (PrimeGaps.lToY L)) ^ 2 * (N : ℝ) /
      (Real.log N) ^ A := div_nonneg (by positivity) (by positivity)
  have h1 : Csub ≤ Cdiag + Cpnt + Csub := by linarith only [hCdiag.le, hCpnt.le]
  have h2 : Cdiag + Cpnt ≤ Cdiag + Cpnt + Csub := by linarith only [hCsub.le]
  have hI' : |PrimeGaps.S₂m h l N w₀ m - pref * Ysum| ≤
      Csub * ((Finsupp.maxRealAbs (PrimeGaps.lToY L)) ^ 2 * (N : ℝ) / (Real.log N) ^ A) :=
    le_of_le_of_eq hI (by ring)
  have hstepII' : |pref * Ysum - pref * Sig| ≤ Cdiag * ((⨆ r, |PrimeGaps.ym m l r|) ^
    2 * (Nat.totient (W N) : ℝ) ^ (k - 2) * (N : ℝ) * (Real.log N) ^ (k - 2) /
          ((W N : ℝ) ^ (k - 1) * PrimeGaps.D₀ (N : ℝ))) :=
    le_of_le_of_eq hstepII (by ring)
  have hIII' : |pref * Sig - ((N : ℝ) / ((Nat.totient (W N) : ℝ) *
    Real.log N)) * Sig| ≤ Cpnt * ((⨆ r, |PrimeGaps.ym m l r|) ^ 2 *
          (Nat.totient (W N) : ℝ) ^ (k - 2) * (N : ℝ) * (Real.log N) ^ (k - 2) /
          ((W N : ℝ) ^ (k - 1) * PrimeGaps.D₀ (N : ℝ))) :=
    le_of_le_of_eq hIII (by ring)
  refine htri.trans ((add_le_add (add_le_add hI' hstepII') hIII').trans ?_)
  refine le_trans ?_ (le_of_eq (by ring : (Cdiag + Cpnt + Csub) *
        ((⨆ r, |PrimeGaps.ym m l r|) ^ 2 * (Nat.totient (W N) : ℝ) ^ (k - 2) * (N : ℝ) *
          (Real.log N) ^ (k - 2) / ((W N : ℝ) ^ (k - 1) * PrimeGaps.D₀ (N : ℝ))) +
      (Cdiag + Cpnt + Csub) *
        ((Finsupp.maxRealAbs (PrimeGaps.lToY L)) ^ 2 * (N : ℝ) / (Real.log N) ^ A) =
      (Cdiag + Cpnt + Csub) * (⨆ r, |PrimeGaps.ym m l r|) ^ 2 *
          (Nat.totient (W N) : ℝ) ^ (k - 2) * (N : ℝ) * (Real.log N) ^ (k - 2) /
          ((W N : ℝ) ^ (k - 1) * PrimeGaps.D₀ (N : ℝ)) +
        (Cdiag + Cpnt + Csub) *
          (Finsupp.maxRealAbs (PrimeGaps.lToY L)) ^ 2 * (N : ℝ) / (Real.log N) ^ A))
  linarith only [mul_le_mul_of_nonneg_right h1 he2nn,
    mul_le_mul_of_nonneg_right h2 hT1nn, hT1nn, he2nn]

end PrimeGaps
