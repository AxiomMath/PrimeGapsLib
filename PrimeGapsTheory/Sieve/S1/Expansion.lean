/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.NumberTheory.Admissible
public import PrimeGapsTheory.Sieve.Common.Expansion
public import PrimeGapsTheory.Sieve.S1.CRT

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Expansion of the first moment

Expands the first sieve moment, evaluates its main term, and bounds the remainder.

## Main definitions

* `IsAdmissible`: Admissibility of a shift tuple.
* `innerDivSum`: The inner divisor sum defining the sieve weight.
* `wVal`: The sieve value at an integer.
* `V0Valid`: Validity of a residue class modulo `W`.
* `S1`: The first sieve moment.
* `primedSum`: The double sum forming the first-moment main term.
* `pairCount`: The number of sieved integers divisible by a given pair of moduli.

## Main results

* `main_S1_asymptotic`: Approximates the first moment by the primed sum.
-/

@[expose] public section

open Real

open scoped BigOperators Finset
open PrimeGaps (D₀)

namespace GPYSieveS1

/-- An admissible tuple, encoded as a strictly monotone map `h: Fin k → ℤ` (so
`h 0 < h 1 <... < h (k-1)`), satisfying that for every prime `q`, the number of residue classes
modulo `q` occupied by the `h i` is `< q`.
-/
def IsAdmissible {k : ℕ} (h : Fin k → ℕ) : Prop :=
  StrictMono h ∧ Finset.Admissible (Finset.image h Finset.univ)

/-- The inner divisor sum `∑_{d_i | n + h_i} λ(d)` over all `k` -tuples `d` of positive integers
with `(d_i: ℤ) ∣ (n + h_i)` for each `i`.
-/
noncomputable def innerDivSum {k : ℕ} (h : Fin k → ℕ) (lam : (Fin k → ℕ) → ℝ) (n : ℤ) : ℝ :=
  ∑' d : Fin k → ℕ, (if (∀ i, 1 ≤ d i) ∧ (∀ i, (d i : ℤ) ∣ (n + h i)) then lam d else 0)

/-- The sieve value `w_n:= (∑_{d_i | n + h_i} λ(d))^2`. -/
noncomputable def wVal {k : ℕ} (h : Fin k → ℕ) (lam : (Fin k → ℕ) → ℝ) (n : ℤ) : ℝ :=
  (innerDivSum h lam n) ^ 2

/-- Validity of the residue class `v_0`: `v_0 < W` and `gcd(v_0 + h_i, W) = 1` for all `i`
(coprimality taken over `ℤ`).
-/
def V0Valid {k : ℕ} (h : Fin k → ℕ) (W : ℕ) (v0 : ℕ) : Prop :=
  v0 < W ∧ ∀ i, IsCoprime ((v0 : ℤ) + h i) (W : ℤ)

/-- The sum `S_1:= ∑_{N < n ≤ 2N, n ≡ v_0 (mod W)} w_n`, with `N: ℝ` and the integer index `n: ℤ`
ranging over `⌊N⌋ < n ≤ ⌊2N⌋` (equivalently, `N < n ≤ 2N`).
-/
noncomputable def S1 {k : ℕ} (h : Fin k → ℕ) (lam : (Fin k → ℕ) → ℝ) (N : ℝ) (W v0 : ℕ) : ℝ :=
  ∑ n ∈ {n ∈ (Finset.Ioc ⌊N⌋ ⌊2 * N⌋) | n % (W : ℤ) = (v0 : ℤ) % (W : ℤ)}, wVal h lam n

open Classical in
/-- The restricted (primed) double sum `∑'_{d,e} λ(d)λ(e)/∏[d_i,e_i]`, over pairs of positive `k`
-tuples `(d,e)` for which `W, [d_1,e_1],..., [d_k,e_k]` are pairwise coprime.
-/
noncomputable def primedSum {k : ℕ} (W : ℕ) (lam : (Fin k → ℕ) →₀ ℝ) : ℝ :=
  ∑' de : (Fin k → ℕ) × (Fin k → ℕ),
    (if ((∀ i, 1 ≤ de.1 i) ∧ (∀ i, 1 ≤ de.2 i) ∧ PrimeGaps.PairwiseCoprimeModuli W (fun i ↦
      Nat.lcm (de.1 i) (de.2 i))) then
        lam de.1 * lam de.2 / (∏ i, (Nat.lcm (de.1 i) (de.2 i) : ℝ))
      else 0)

/-- The integer counting function:
`Count(d,e) = #{ n ∈ (⌊N⌋, ⌊2N⌋]: n ≡ v0 (mod W) ∧ ∀ i, [d_i,e_i] | n+h_i }`.
-/
noncomputable def pairCount {k : ℕ} (h : Fin k → ℕ) (N : ℝ) (W v0 : ℕ) (d e : Fin k → ℕ) : ℕ :=
  #{n ∈ (Finset.Ioc ⌊N⌋ ⌊2 * N⌋) | n % (W : ℤ) = (v0 : ℤ) % (W : ℤ) ∧
        ∀ i, ((Nat.lcm (d i) (e i) : ℕ) : ℤ) ∣ (n + h i)}

/-- Square-expansion and sum-swap: there is a finite support set `D` for `λ` such that `S1` equals
the finite double sum of `λ(d)λ(e)·Count(d,e)`.
-/
theorem lem_S1_expand_swap {k : ℕ} (h : Fin k → ℕ) (lam : (Fin k → ℕ) →₀ ℝ) (N : ℝ) (W v0 : ℕ)
    (R : ℝ) (hsupp : lam.HasPermissibleSupport ⌊R⌋₊ W) :
    ∃ D : Finset (Fin k → ℕ), (∀ d, lam d ≠ 0 → d ∈ D) ∧ S1 h lam N W v0 = ∑ d ∈ D, ∑ e ∈ D,
          lam d * lam e * (pairCount h N W v0 d e : ℝ) := by
  classical
  set D : Finset (Fin k → ℕ) := Fintype.piFinset (fun _ : Fin k ↦ Finset.Icc 1 ⌊R⌋₊) with hDdef
  have hDpos : ∀ d ∈ D, ∀ i, 1 ≤ d i := fun d hd i ↦ by
    rw [hDdef, Fintype.mem_piFinset] at hd
    exact (Finset.mem_Icc.mp (hd i)).1
  have hD : ∀ d, lam d ≠ 0 → d ∈ D := fun d hne ↦ by
    have hdmem := hsupp (Finsupp.mem_support_iff.mpr hne)
    have h1 : ∀ j, 1 ≤ d j := fun j ↦ Nat.one_le_iff_ne_zero.mpr
      (Finset.squarefree_of_mem_permissibleSupport hdmem j).ne_zero
    rw [hDdef, Fintype.mem_piFinset]
    exact fun i ↦ Finset.mem_Icc.mpr ⟨h1 i,
      (Finset.single_le_prod' (f := d) (fun j _ ↦ h1 j) (Finset.mem_univ i)).trans
        (Finset.mem_permissibleSupport_iff.mp hdmem).1⟩
  refine ⟨D, hD, ?_⟩
  have hQ : ∀ (n : ℤ) (d e : Fin k → ℕ),
      ((∀ i, (d i : ℤ) ∣ (n + h i)) ∧ (∀ i, (e i : ℤ) ∣ (n + h i))) ↔
        (∀ i, ((Nat.lcm (d i) (e i) : ℕ) : ℤ) ∣ (n + h i)) := fun n d e ↦ by
    have hcast : ∀ i, ((Nat.lcm (d i) (e i) : ℕ) : ℤ) = ↑(((d i : ℤ)).lcm ((e i : ℤ))) :=
      fun i ↦ by simp [Int.lcm]
    exact ⟨fun hde i ↦ (hcast i) ▸ Int.coe_lcm_dvd (hde.1 i) (hde.2 i), fun hde ↦
      ⟨fun i ↦ (Int.natCast_dvd_natCast.mpr (Nat.dvd_lcm_left (d i) (e i))).trans (hde i),
        fun i ↦ (Int.natCast_dvd_natCast.mpr (Nat.dvd_lcm_right (d i) (e i))).trans (hde i)⟩⟩
  have hinner : ∀ n : ℤ, innerDivSum h lam n =
      ∑ d ∈ D.filter (fun d ↦ ∀ i, (d i : ℤ) ∣ (n + h i)), lam d := fun n ↦ by
    rw [innerDivSum, tsum_eq_sum (s := D) ?_, Finset.sum_filter]
    · refine Finset.sum_congr rfl fun d hd ↦ ?_
      by_cases hdvd : ∀ i, (d i : ℤ) ∣ (n + h i)
      · rw [if_pos ⟨hDpos d hd, hdvd⟩, if_pos hdvd]
      · rw [if_neg fun hh ↦ hdvd hh.2, if_neg hdvd]
    · exact fun d hd ↦ by simp [not_not.mp (mt (hD d) hd)]
  have key := PrimeGaps.Expansion.sum_ite_mul_sq (Finset.Ioc ⌊N⌋ ⌊2 * N⌋)
    (fun n : ℤ ↦ n % (W : ℤ) = (v0 : ℤ) % (W : ℤ)) (fun _ ↦ (1 : ℝ))
    (fun (n : ℤ) (d : Fin k → ℕ) ↦ ∀ i, (d i : ℤ) ∣ (n + h i)) hQ D lam
  simp only [one_mul] at key
  rw [S1, Finset.sum_filter]
  simp only [wVal, hinner, key]
  refine Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun e _ ↦ ?_
  congr 1
  rw [Finset.sum_boole]
  rfl

open Classical in
/-- Main-term identification: summing the leading CRT term `N/Q` over the support pairs, only
pairwise-coprime pairs survive and reproduce `(N/W)·primedSum W lam`.
-/
theorem lem_main_term {k : ℕ} (lam : (Fin k → ℕ) →₀ ℝ) (N : ℝ) (W : ℕ)
    (D : Finset (Fin k → ℕ)) (hD : ∀ d, lam d ≠ 0 → d ∈ D) :
    ∑ d ∈ D, ∑ e ∈ D, (if (∀ i, 0 < d i) ∧ (∀ i, 0 < e i) ∧
      PrimeGaps.PairwiseCoprimeModuli W (fun i ↦ Nat.lcm (d i) (e i)) then
            lam d * lam e * (N / (PrimeGaps.qMod W d e : ℝ)) else 0) =
      (N / (W : ℝ)) * primedSum W lam := by
  classical
  have hps : primedSum W lam = ∑ de ∈ D ×ˢ D,
        (if ((∀ i, 1 ≤ de.1 i) ∧ (∀ i, 1 ≤ de.2 i) ∧ PrimeGaps.PairwiseCoprimeModuli W (fun i ↦
          Nat.lcm (de.1 i) (de.2 i))) then
            lam de.1 * lam de.2 / (∏ i, (Nat.lcm (de.1 i) (de.2 i) : ℝ))
          else 0) := by
    rw [primedSum]
    refine tsum_eq_sum fun de hde ↦ ?_
    rw [Finset.mem_product] at hde
    push Not at hde
    have hz : lam de.1 * lam de.2 = 0 := by
      by_cases h1 : de.1 ∈ D
      · exact mul_eq_zero_of_right _ (not_not.mp (mt (hD _) (hde h1)))
      · exact mul_eq_zero_of_left (not_not.mp (mt (hD _) h1)) _
    simp [hz]
  rw [hps, Finset.mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun e _ ↦ ?_
  have hguard : ((∀ i, 0 < d i) ∧ (∀ i, 0 < e i) ∧
      PrimeGaps.PairwiseCoprimeModuli W fun i ↦ Nat.lcm (d i) (e i)) ↔
        ((∀ i, 1 ≤ d i) ∧ (∀ i, 1 ≤ e i) ∧
          PrimeGaps.PairwiseCoprimeModuli W fun i ↦ Nat.lcm (d i) (e i)) := Iff.rfl
  by_cases hc : (∀ i, 0 < d i) ∧ (∀ i, 0 < e i) ∧ PrimeGaps.PairwiseCoprimeModuli W (fun i ↦
    Nat.lcm (d i) (e i))
  · rw [if_pos hc, if_pos (hguard.mp hc)]
    simp only [PrimeGaps.qMod]
    push_cast
    field_simp
  · rw [if_neg hc, if_neg fun hh ↦ hc (hguard.mpr hh)]
    ring

/-- A threshold `N₀` beyond which `3 ≤ N` and every shift gap satisfies `|h i - h j| ≤ D₀ N`. -/
theorem exists_thresh {k : ℕ} (h : Fin k → ℕ) : ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      3 ≤ N ∧ ∀ i j : Fin k, i ≠ j → |(h i : ℝ) - (h j : ℝ)| ≤ D₀ N := by
  obtain ⟨N₀, hN₀3, hN₀⟩ := PrimeGaps.exists_shift_gap_threshold h
  refine ⟨N₀, fun N hN ↦ ⟨hN₀3.trans hN, fun i j hij ↦ ?_⟩⟩
  rw [Nat.abs_sub_cast_eq_dist (h i) (h j)]
  linarith [hN₀ N hN i j hij]

open PrimeGaps in
open scoped PrimeGaps.sieveModulus in
open Classical in
/-- For a positive pair `(d,e)` whose coordinate products are coprime to `W`, and for `N` above the
threshold (`3 ≤ N` and `|h i − h j| ≤ D_0`), the rounding error `|pairCount − mp|` is `≤ 1`. On
pairwise-coprime pairs this is `PrimeGaps.lem_coprime_branch`; on the remaining pairs
`pairCount = 0` via `lem_noncoprime_branch` (the large prime factors come from
`primeFactor_large`).
-/
theorem lem_per_pair {k : ℕ} (h : Fin k → ℕ) (hHinj : Function.Injective h) (N : ℕ)
    (hthr : ∀ i j : Fin k, i ≠ j → |(h i : ℝ) - (h j : ℝ)| ≤ D₀ N)
    (v0 : ℕ) (d e : Fin k → ℕ) (hd : ∀ i, 0 < d i) (he : ∀ i, 0 < e i)
    (hdcop : Nat.Coprime (∏ i, d i) (W N))
    (hecop : Nat.Coprime (∏ i, e i) (W N)) :
    |(pairCount h N (W N) v0 d e : ℝ) -
        (if (∀ i, 0 < d i) ∧ (∀ i, 0 < e i) ∧ PrimeGaps.PairwiseCoprimeModuli (W N) (fun i ↦
          Nat.lcm (d i) (e i)) then
              N / (PrimeGaps.qMod (W N) d e : ℝ) else 0)| ≤ 1 := by
  have hpc : pairCount h N (W N) v0 d e = PrimeGaps.Scount h N (W N) v0 d e := by
    unfold pairCount PrimeGaps.Scount
    have h2N : ⌊2 * (N : ℝ)⌋ = (2 * N : ℤ) := by
      rw [show (2 : ℝ) * N = ((2 * N : ℕ) : ℝ) from (Nat.cast_mul 2 N).symm, Int.floor_natCast]
      exact Nat.cast_mul 2 N
    rw [Int.floor_natCast, h2N]
    rfl
  have hqm : (PrimeGaps.qMod (W N) d e : ℝ) = ((PrimeGaps.qMod (W N) d e : ℕ) : ℝ) := rfl
  by_cases hcond : (∀ i, 0 < d i) ∧ (∀ i, 0 < e i) ∧ PrimeGaps.PairwiseCoprimeModuli (W N) (fun i ↦
    Nat.lcm (d i) (e i))
  · rw [if_pos hcond, hpc, hqm]
    exact PrimeGaps.lem_coprime_branch h N (W N) v0 d e PrimeGaps.W_pos hd he hcond.2.2
  · rw [if_neg hcond]
    have hbig : ∀ (i : Fin k) (p : ℕ), Nat.Prime p →
        p ∣ Nat.lcm (d i) (e i) → Real.log (Real.log (Real.log N)) < (p : ℝ) := by
      intro i p hp hpl
      rcases hp.dvd_mul.mp (hpl.trans (Nat.lcm_dvd_mul _ _)) with hpd | hpe
      · exact PrimeGaps.primeFactor_large N (∏ j, d j) p hdcop hp
          (hpd.trans (Finset.dvd_prod_of_mem d (Finset.mem_univ i)))
      · exact PrimeGaps.primeFactor_large N (∏ j, e j) p hecop hp
          (hpe.trans (Finset.dvd_prod_of_mem e (Finset.mem_univ i)))
    have hzero : PrimeGaps.Scount h N (W N) v0 d e = 0 :=
      PrimeGaps.lem_noncoprime_branch h hHinj N (W N) v0 d e PrimeGaps.W_eq_primorial_D₀
        hbig hthr fun hp ↦ hcond ⟨hd, he, hp⟩
    rw [hpc, hzero]
    simp

open PrimeGaps in
open scoped PrimeGaps.sieveModulus in
open Classical in
/-- Using the per-pair bound (`lem_per_pair`), the aggregate rounding error is bounded by
`(∑_{d∈D}|λ(d)|)²`. Support-positivity (`hpos`) and support-coprimality (`hcop`) supply the
hypotheses of `lem_per_pair` on nonzero terms; zero terms vanish.
-/
theorem lem_agg_reduce {k : ℕ} (h : Fin k → ℕ) (hHinj : Function.Injective h) (N : ℕ)
    (hthr : ∀ i j : Fin k, i ≠ j → |(h i : ℝ) - (h j : ℝ)| ≤ D₀ N) (lam : (Fin k → ℕ) →₀ ℝ)
    (v0 : ℕ) (D : Finset (Fin k → ℕ)) (hpos : ∀ d, lam d ≠ 0 → ∀ i, 0 < d i)
    (hcop : ∀ d, lam d ≠ 0 → Nat.Coprime (∏ i, d i) (W N)) :
    |∑ d ∈ D, ∑ e ∈ D, lam d * lam e * ((pairCount h N (W N) v0 d e : ℝ) -
            (if (∀ i, 0 < d i) ∧ (∀ i, 0 < e i) ∧ PrimeGaps.PairwiseCoprimeModuli (W N) (fun i ↦
              Nat.lcm (d i) (e i)) then
                N / (PrimeGaps.qMod (W N) d e : ℝ) else 0))| ≤ (∑ d ∈ D, |lam d|) ^ 2 := by
  classical
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hstep : ∀ d ∈ D, |∑ e ∈ D, lam d * lam e * ((pairCount h N (W N) v0 d e : ℝ) -
          (if (∀ i, 0 < d i) ∧ (∀ i, 0 < e i) ∧ PrimeGaps.PairwiseCoprimeModuli (W N) (fun i ↦
            Nat.lcm (d i) (e i)) then
              N / (PrimeGaps.qMod (W N) d e : ℝ) else 0))| ≤ |lam d| * ∑ e ∈ D, |lam e| :=
    fun d _ ↦ by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun e _ ↦ ?_
    rw [abs_mul, abs_mul]
    by_cases hld : lam d = 0
    · simp [hld]
    by_cases hle : lam e = 0
    · simp [hle]
    simpa using mul_le_mul_of_nonneg_left
      (lem_per_pair h hHinj N hthr v0 d e (hpos d hld) (hpos e hle) (hcop d hld) (hcop e hle))
      (mul_nonneg (abs_nonneg (lam d)) (abs_nonneg (lam e)))
  calc ∑ d ∈ D, |∑ e ∈ D, lam d * lam e * ((pairCount h N (W N) v0 d e : ℝ) -
            (if (∀ i, 0 < d i) ∧ (∀ i, 0 < e i) ∧ PrimeGaps.PairwiseCoprimeModuli (W N) (fun i ↦
              Nat.lcm (d i) (e i)) then
                N / (PrimeGaps.qMod (W N) d e : ℝ) else 0))| ≤
      ∑ d ∈ D, |lam d| * ∑ e ∈ D, |lam e| := Finset.sum_le_sum hstep
    _ = (∑ d ∈ D, |lam d|) ^ 2 := by rw [← Finset.sum_mul]; ring

/-- Under the `δ/2` scaling trick, each `|λ(d)|` is bounded by
`C₁ · y_max · (log (sieveLevel N θ (δ/2)))^k`. -/
theorem l1_perd {k : ℕ} (_hk : 2 ≤ k) (θ δ : ℝ) (hδ0 : 0 < δ) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ N : ℝ, 1 < N → 2 ≤ N ^ (θ / 2 - δ / 2) →
      ∀ lam : (Fin k → ℕ) →₀ ℝ, lam.HasPermissibleSupport ⌊N ^ (θ / 2 - δ)⌋₊ (primorial ⌊D₀ N⌋₊) →
        (∀ d, lam d ≠ 0 → ∀ i, 1 ≤ d i) →
        ∀ d : Fin k → ℕ, |lam d| ≤
          C₁ * Finsupp.maxRealAbs (PrimeGaps.lToY lam) * Real.log (N ^ (θ / 2 - δ / 2)) ^ k := by
  refine ⟨rexp (1 + 3 * k), Real.exp_pos _, ?_⟩
  intro N hN1 hSL2 lam hsupp _ d
  have hRlt : N ^ (θ / 2 - δ) < N ^ (θ / 2 - δ / 2) :=
    (Real.rpow_lt_rpow_left_iff hN1).mpr (by linarith)
  have hsupp' : lam.HasPermissibleSupport ⌊N ^ (θ / 2 - δ / 2)⌋₊ (primorial ⌊PrimeGaps.D₀ N⌋₊) := by
    refine Finsupp.HasPermissibleSupport.of_forall fun d hne ↦ ?_
    have hdmem := hsupp (Finsupp.mem_support_iff.mpr hne)
    obtain ⟨hprodNat, hcop, hsq⟩ := Finset.mem_permissibleSupport_iff.mp hdmem
    refine ⟨Nat.le_floor ?_, hcop, hsq⟩
    calc ((∏ i, d i : ℕ) : ℝ) = (∏ i, (d i : ℝ)) := by push_cast; ring
      _ ≤ N ^ (θ / 2 - δ) := le_trans (by exact_mod_cast hprodNat)
          (Nat.floor_le (Real.rpow_nonneg (by positivity) _))
      _ ≤ N ^ (θ / 2 - δ / 2) := hRlt.le
  have hRfloor : 2 ≤ ⌊N ^ (θ / 2 - δ / 2)⌋₊ := Nat.le_floor hSL2
  have hbound := PrimeGaps.max_yToL_le_const_mul_max_y_mul_log_pow hsupp'.lToY hRfloor
  have hlogFloor : Real.log (⌊N ^ (θ / 2 - δ / 2)⌋₊ : ℝ) ≤ Real.log (N ^ (θ / 2 - δ / 2)) :=
    Real.log_le_log (by positivity)
      (Nat.floor_le (Real.rpow_nonneg (le_trans (by norm_num) hN1.le) _))
  have hlogFloor0 : 0 ≤ Real.log (⌊N ^ (θ / 2 - δ / 2)⌋₊ : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (le_trans (by omega : 1 ≤ 2) hRfloor))
  have hlamRecover : lam d = PrimeGaps.yToL (PrimeGaps.lToY lam) d := by
    rw [PrimeGaps.yToL_lToY]
    split_ifs with hd
    · rfl
    · exact not_not.mp fun hne ↦ hd (hsupp.squarefree_of_ne_zero hne)
  rw [hlamRecover]
  calc |PrimeGaps.yToL (PrimeGaps.lToY lam) d| ≤
        Finsupp.maxRealAbs (PrimeGaps.yToL (PrimeGaps.lToY lam)) := Finsupp.le_maxRealAbs
    _ ≤ rexp (1 + 3 * k) * Finsupp.maxRealAbs (PrimeGaps.lToY lam) *
        Real.log ⌊N ^ (θ / 2 - δ / 2)⌋₊ ^ k := hbound
    _ ≤ rexp (1 + 3 * k) * Finsupp.maxRealAbs (PrimeGaps.lToY lam) *
        Real.log (N ^ (θ / 2 - δ / 2)) ^ k := by
      gcongr
      exact mul_nonneg (Real.exp_pos _).le Finsupp.maxRealAbs_nonneg

open Classical in
/-- The nonzero support of `λ`, restricted to `D`, sits inside promoted permissible support at
the exactly equivalent strict real cutoff `R + 1`. -/
theorem l1_supp_sub {k : ℕ} (N θ δ : ℝ) (lam : (Fin k → ℕ) →₀ ℝ)
    (hsupp : lam.HasPermissibleSupport ⌊N ^ (θ / 2 - δ)⌋₊ (primorial ⌊D₀ N⌋₊))
    (D : Finset (Fin k → ℕ)) :
    (D.filter (fun d ↦ lam d ≠ 0)) ⊆ Finset.permissibleSupport k (⌈N ^ (θ / 2 - δ) + 1⌉₊ - 1)
        (primorial ⌊D₀ N⌋₊) := by
  intro d hd
  obtain ⟨-, hne⟩ := Finset.mem_filter.mp hd
  have hdmem := hsupp (Finsupp.mem_support_iff.mpr hne)
  obtain ⟨hprodNat, hcop, hsq⟩ := Finset.mem_permissibleSupport_iff.mp hdmem
  have hp : ∀ i, 1 ≤ d i := fun i ↦
    Nat.one_le_iff_ne_zero.mpr (Finset.squarefree_of_mem_permissibleSupport hdmem i).ne_zero
  have hprod : (∏ i, d i : ℝ) ≤ N ^ (θ / 2 - δ) :=
    le_trans (by exact_mod_cast hprodNat) (Nat.floor_le (Nat.pos_of_floor_pos
      (lt_of_lt_of_le (Finset.prod_pos fun i _ ↦ hp i) hprodNat)).le)
  refine Finset.mem_permissibleSupport_iff.mpr ⟨?_, hcop, hsq⟩
  have hltR : ((∏ i, d i : ℕ) : ℝ) < N ^ (θ / 2 - δ) + 1 := by rw [Nat.cast_prod]; linarith
  have hltCeil : (∏ i, d i) < ⌈N ^ (θ / 2 - δ) + 1⌉₊ := by
    exact_mod_cast hltR.trans_le (Nat.le_ceil _)
  omega

/-- For `N` above a threshold, the ℓ¹ norm of the weights over any support-containing `D` is
bounded by `C · y_max · R · (log R)^{2k}`.
-/
theorem lem_l1_bound {k : ℕ} (hk : 2 ≤ k) (θ δ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2)) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → ∀ lam : (Fin k → ℕ) →₀ ℝ,
        lam.HasPermissibleSupport ⌊N ^ (θ / 2 - δ)⌋₊ (primorial ⌊D₀ N⌋₊) →
      ∀ D : Finset (Fin k → ℕ), (∀ d, lam d ≠ 0 → d ∈ D) → ∑ d ∈ D, |lam d| ≤
          C * Finsupp.maxRealAbs (PrimeGaps.lToY lam) * N ^ (θ / 2 - δ) *
            Real.log (N ^ (θ / 2 - δ)) ^ (2 * k) := by
  classical
  obtain ⟨_, hθ1⟩ := hθ
  obtain ⟨hδ0, _⟩ := hδ
  obtain ⟨C₁, hC₁, hperd⟩ := l1_perd hk θ δ hδ0
  obtain ⟨C₂, hC₂, hcount0⟩ := PrimeGaps.lem_support_count (k := k)
  rw [Filter.eventually_atTop] at hcount0
  obtain ⟨M, hcount⟩ := hcount0
  have hexp : 0 < θ / 2 - δ := by linarith
  have hexp2 : 0 < θ / 2 - δ / 2 := by linarith
  have hcgt : θ / 2 - δ < θ / 2 - δ / 2 := by linarith
  set cc : ℝ := (θ / 2 - δ / 2) / (θ / 2 - δ) with hcc
  have hcc1 : 1 < cc := by rw [hcc, lt_div_iff₀ hexp]; linarith
  have hccpos : 0 < cc := by linarith
  refine ⟨C₁ * C₂ * 2 * (1 + Real.log 2) ^ k * cc ^ k, by positivity, ?_⟩
  have hRtt : Filter.Tendsto (fun N : ℝ ↦ N ^ (θ / 2 - δ)) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop hexp
  have hStt : Filter.Tendsto (fun N : ℝ ↦ N ^ (θ / 2 - δ / 2)) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop hexp2
  have hev1 : ∀ᶠ N in Filter.atTop, rexp 1 ≤ N ^ (θ / 2 - δ) :=
    hRtt.eventually_ge_atTop (rexp 1)
  have hev2 : ∀ᶠ N in Filter.atTop, M ≤ N ^ (θ / 2 - δ) + 1 := by
    filter_upwards [hRtt.eventually_ge_atTop M] with N hN; linarith
  have hev3 : ∀ᶠ N in Filter.atTop, (2 : ℝ) ≤ N ^ (θ / 2 - δ / 2) := hStt.eventually_ge_atTop 2
  have hev4 : ∀ᶠ N in Filter.atTop, (1 : ℝ) < N := Filter.eventually_gt_atTop 1
  rw [Filter.eventually_atTop] at hev1 hev2 hev3 hev4
  obtain ⟨N1, h1⟩ := hev1
  obtain ⟨N2, h2⟩ := hev2
  obtain ⟨N3, h3⟩ := hev3
  obtain ⟨N4, h4⟩ := hev4
  refine ⟨max (max N1 N2) (max N3 N4), ?_⟩
  intro N hN lam hsupp D _
  have hRe : rexp 1 ≤ N ^ (θ / 2 - δ) :=
    h1 N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)
  have hRM : M ≤ N ^ (θ / 2 - δ) + 1 :=
    h2 N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
  have hS2 : (2 : ℝ) ≤ N ^ (θ / 2 - δ / 2) :=
    h3 N (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN)
  have hN1 : (1 : ℝ) < N := h4 N (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN)
  have hlampos : ∀ d, lam d ≠ 0 → ∀ i, 1 ≤ d i :=
    fun d hne i ↦ Nat.one_le_iff_ne_zero.mpr (hsupp.ne_zero_of_ne_zero hne i)
  have hlogR1 : 1 ≤ Real.log (N ^ (θ / 2 - δ)) := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hRe
  have hlogRpos : 0 < Real.log (N ^ (θ / 2 - δ)) := one_pos.trans_le hlogR1
  have hRpos : 0 < N ^ (θ / 2 - δ) := (Real.exp_pos 1).trans_le hRe
  have hNpos : (0 : ℝ) < N := one_pos.trans hN1
  have hccmul : cc * (θ / 2 - δ) = θ / 2 - δ / 2 := by
    rw [hcc]; exact div_mul_cancel₀ _ hexp.ne'
  have hlogSL : Real.log (N ^ (θ / 2 - δ / 2)) = cc * Real.log (N ^ (θ / 2 - δ)) := by
    rw [Real.log_rpow hNpos, Real.log_rpow hNpos, ← hccmul]; ring
  have hsumfilt : ∑ d ∈ D, |lam d| = ∑ d ∈ D.filter (fun d ↦ lam d ≠ 0), |lam d| := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    split_ifs with hz
    · rfl
    · simp [not_not.mp hz]
  rw [hsumfilt]
  set S := D.filter (fun d ↦ lam d ≠ 0) with hSdef
  have hperdN := hperd N hN1 hS2 lam hsupp hlampos
  have hyM : 0 ≤ Finsupp.maxRealAbs (PrimeGaps.lToY lam) := Finsupp.maxRealAbs_nonneg
  have hlogSLnn : 0 ≤ Real.log (N ^ (θ / 2 - δ / 2)) := by
    rw [hlogSL]; positivity
  have hMbd : 0 ≤
      C₁ * Finsupp.maxRealAbs (PrimeGaps.lToY lam) * Real.log (N ^ (θ / 2 - δ / 2)) ^ k := by
    positivity
  have hsumcard : ∑ d ∈ S, |lam d| ≤
      #S • (C₁ * Finsupp.maxRealAbs (PrimeGaps.lToY lam) *
        Real.log (N ^ (θ / 2 - δ / 2)) ^ k) :=
    Finset.sum_le_card_nsmul _ _ _ fun d _ ↦ hperdN d
  rw [nsmul_eq_mul] at hsumcard
  have hcardle : (#S : ℝ) ≤ (#(Finset.permissibleSupport k
      (⌈N ^ (θ / 2 - δ) + 1⌉₊ - 1) (primorial ⌊D₀ N⌋₊)) : ℝ) := by
    exact_mod_cast Finset.card_le_card (l1_supp_sub N θ δ lam hsupp D)
  have hScard : (#S : ℝ) ≤ C₂ * (N ^ (θ / 2 - δ) + 1) * Real.log (N ^ (θ / 2 - δ) + 1) ^ k :=
    hcardle.trans (hcount (N ^ (θ / 2 - δ) + 1) hRM (primorial ⌊D₀ N⌋₊))
  have hR1le : N ^ (θ / 2 - δ) + 1 ≤ 2 * N ^ (θ / 2 - δ) := by
    have : (1 : ℝ) ≤ N ^ (θ / 2 - δ) := (Real.one_le_exp (by norm_num)).trans hRe
    linarith
  have hlogR1le : Real.log (N ^ (θ / 2 - δ) + 1) ≤ (1 + Real.log 2) * Real.log (N ^ (θ / 2 - δ)) :=
    calc Real.log (N ^ (θ / 2 - δ) + 1) ≤ Real.log (2 * N ^ (θ / 2 - δ)) :=
          Real.log_le_log (by linarith) hR1le
      _ = Real.log 2 + Real.log (N ^ (θ / 2 - δ)) := by
          rw [Real.log_mul (by norm_num) (ne_of_gt hRpos)]
      _ ≤ (1 + Real.log 2) * Real.log (N ^ (θ / 2 - δ)) := by
          have : Real.log 2 ≤ Real.log 2 * Real.log (N ^ (θ / 2 - δ)) := by
            nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2), hlogR1]
          nlinarith
  have hlog2nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc ∑ d ∈ S, |lam d| ≤ (#S : ℝ) *
          (C₁ * Finsupp.maxRealAbs (PrimeGaps.lToY lam) * Real.log (N ^ (θ / 2 - δ / 2)) ^ k) :=
        hsumcard
    _ ≤ (C₂ * (N ^ (θ / 2 - δ) + 1) * Real.log (N ^ (θ / 2 - δ) + 1) ^ k) *
          (C₁ * Finsupp.maxRealAbs (PrimeGaps.lToY lam) * Real.log (N ^ (θ / 2 - δ / 2)) ^ k) :=
        mul_le_mul_of_nonneg_right hScard hMbd
    _ ≤ (C₂ * (2 * N ^ (θ / 2 - δ)) * ((1 + Real.log 2) * Real.log (N ^ (θ / 2 - δ))) ^ k) *
          (C₁ * Finsupp.maxRealAbs (PrimeGaps.lToY lam) *
            (cc * Real.log (N ^ (θ / 2 - δ))) ^ k) := by
        rw [hlogSL]
        apply mul_le_mul
        · apply mul_le_mul
          · apply mul_le_mul_of_nonneg_left hR1le (le_of_lt hC₂)
          · apply pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlogR1le
          · exact pow_nonneg (Real.log_nonneg (by linarith)) k
          · positivity
        · exact le_refl _
        · positivity
        · positivity
    _ = C₁ * C₂ * 2 * (1 + Real.log 2) ^ k * cc ^ k * Finsupp.maxRealAbs (PrimeGaps.lToY lam) *
          N ^ (θ / 2 - δ) * Real.log (N ^ (θ / 2 - δ)) ^ (2 * k) := by
        rw [mul_pow, mul_pow, show 2 * k = k + k from two_mul k, pow_add]; ring

open PrimeGaps in
open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
open Classical in
/-- Error aggregation: the aggregate rounding error over all support pairs is dominated by the
target error term.
-/
theorem lem_error_bound {k : ℕ} (hk : 2 ≤ k) (h : Fin k → ℕ) (hadm : IsAdmissible h) :
    ∀ θ δ : ℝ, θ ∈ Set.Ioo (0 : ℝ) 1 → δ ∈ Set.Ioo (0 : ℝ) (θ / 2) → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ,
      ∀ N : ℕ, N₀ ≤ N →
      ∀ lam : (Fin k → ℕ) →₀ ℝ, lam.HasPermissibleSupport ⌊R⌋₊ (W N) →
      ∀ v0 : ℕ, V0Valid h (W N) v0 →
      ∀ D : Finset (Fin k → ℕ), (∀ d, lam d ≠ 0 → d ∈ D) →
        |∑ d ∈ D, ∑ e ∈ D, lam d * lam e *
              ((pairCount h N (W N) v0 d e : ℝ) - (if (∀ i, 0 < d i) ∧ (∀ i, 0 <
                e i) ∧ PrimeGaps.PairwiseCoprimeModuli (W N) (fun i ↦ Nat.lcm (d i) (e i)) then
                    N / (PrimeGaps.qMod (W N) d e : ℝ) else 0))| ≤
          C * (Finsupp.maxRealAbs (PrimeGaps.lToY lam)) ^ 2 * (Nat.totient (W N) : ℝ) ^ k * N *
            (Real.log R) ^ k /
              ((W N : ℝ) ^ (k + 1) * D₀ N) := by
  intro θ δ hθ hδ
  obtain ⟨hθ0, hθ1⟩ := hθ
  obtain ⟨hδ0, hδ2⟩ := hδ
  have hHinj : Function.Injective h := hadm.1.injective
  obtain ⟨Cneg, hCneg, hnegbd⟩ := PrimeGaps.crt_error_negligible k
  obtain ⟨Nneg, hNneg⟩ :=
    Filter.eventually_atTop.mp (hnegbd θ δ 1 hθ0 hθ1 hδ0 hδ2 (by norm_num))
  obtain ⟨Cl1, hCl1, Nl1, hl1⟩ := lem_l1_bound hk θ δ ⟨hθ0, hθ1⟩ ⟨hδ0, hδ2⟩
  obtain ⟨Nthr, hthr⟩ := exists_thresh h
  refine ⟨Cl1 ^ 2 * Cneg, by positivity, max (max (Nneg : ℝ) Nl1) (max Nthr 3), ?_⟩
  intro N hN lam hsupp v0 hv0 D hD
  have hNneg' : Nneg ≤ N := by
    exact_mod_cast le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNl1' : Nl1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNthr' : Nthr ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  obtain ⟨-, hthrN⟩ := hthr N hNthr'
  have hpos : ∀ d, lam d ≠ 0 → ∀ i, 0 < d i :=
    fun d hne i ↦ Nat.one_le_iff_ne_zero.mpr (hsupp.ne_zero_of_ne_zero hne i)
  have hcop : ∀ d, lam d ≠ 0 → Nat.Coprime (∏ i, d i) (W N) :=
    fun d hne ↦ hsupp.coprime_prod_W_of_ne_zero hne
  have hA := lem_agg_reduce h hHinj N hthrN lam v0 D hpos hcop
  have hB := hl1 N hNl1' lam hsupp D hD
  have hSumnn : 0 ≤ ∑ d ∈ D, |lam d| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hB2 : (∑ d ∈ D, |lam d|) ^ 2 ≤ Cl1 ^ 2 * Finsupp.maxRealAbs (PrimeGaps.lToY lam) ^ 2 *
      (N ^ (θ / 2 - δ)) ^ 2 * Real.log (N ^ (θ / 2 - δ)) ^ (4 * k) :=
    calc (∑ d ∈ D, |lam d|) ^ 2
        ≤ (Cl1 * Finsupp.maxRealAbs (PrimeGaps.lToY lam) * N ^ (θ / 2 - δ) *
            Real.log (N ^ (θ / 2 - δ)) ^ (2 * k)) ^ 2 := pow_le_pow_left₀ hSumnn hB 2
      _ = Cl1 ^ 2 * Finsupp.maxRealAbs (PrimeGaps.lToY lam) ^ 2 * (N ^ (θ / 2 - δ)) ^ 2 *
            Real.log (N ^ (θ / 2 - δ)) ^ (4 * k) := by
          rw [show 4 * k = 2 * (2 * k) from by ring, pow_mul,
            ← pow_mul (Real.log (N ^ (θ / 2 - δ)))]
          ring
  have hC1 := hNneg N hNneg'
  simp only [one_pow, one_mul] at hC1
  have hC2 : Finsupp.maxRealAbs (PrimeGaps.lToY lam) ^ 2 * ((N ^ (θ / 2 - δ)) ^ 2 *
      Real.log (N ^ (θ / 2 - δ)) ^ (4 * k)) ≤
      Finsupp.maxRealAbs (PrimeGaps.lToY lam) ^ 2 * (Cneg * ((Nat.totient (W N) : ℝ) ^ k *
        N * Real.log (N ^ (θ / 2 - δ)) ^ k / ((W N : ℝ) ^ (k + 1) * D₀ N))) :=
    mul_le_mul_of_nonneg_left hC1 (sq_nonneg _)
  calc |∑ d ∈ D, ∑ e ∈ D, lam d * lam e * ((pairCount h N (W N) v0 d e : ℝ) -
              (if (∀ i, 0 < d i) ∧ (∀ i, 0 < e i) ∧ PrimeGaps.PairwiseCoprimeModuli (W N) (fun i ↦
                Nat.lcm (d i) (e i)) then
                  N / (PrimeGaps.qMod (W N) d e : ℝ) else 0))| ≤ (∑ d ∈ D, |lam d|) ^ 2 := hA
    _ ≤ Cl1 ^ 2 * Finsupp.maxRealAbs (PrimeGaps.lToY lam) ^ 2 * (N ^ (θ / 2 - δ)) ^ 2 *
          Real.log (N ^ (θ / 2 - δ)) ^ (4 * k) := hB2
    _ = Cl1 ^ 2 * (Finsupp.maxRealAbs (PrimeGaps.lToY lam) ^ 2 *
          ((N ^ (θ / 2 - δ)) ^ 2 * Real.log (N ^ (θ / 2 - δ)) ^ (4 * k))) := by ring
    _ ≤ Cl1 ^ 2 * (Finsupp.maxRealAbs (PrimeGaps.lToY lam) ^ 2 * (Cneg *
          ((Nat.totient (W N) : ℝ) ^ k * N *
            Real.log (N ^ (θ / 2 - δ)) ^ k / ((W N : ℝ) ^ (k + 1) * D₀ N)))) :=
        mul_le_mul_of_nonneg_left hC2 (sq_nonneg _)
    _ = Cl1 ^ 2 * Cneg * Finsupp.maxRealAbs (PrimeGaps.lToY lam) ^ 2 *
          (Nat.totient (W N) : ℝ) ^ k * N * Real.log (N ^ (θ / 2 - δ)) ^ k /
            ((W N : ℝ) ^ (k + 1) * D₀ N) := by ring

open PrimeGaps in
open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
open Classical in
/-- Fix `k ≥ 2` and an admissible tuple `h: Fin k → ℤ`. Following the `O_k` /`≪` convention, the
level of distribution `θ ∈ (0,1)` and the sieve parameter `δ ∈ (0, θ/2)` are fixed *first*. Then
there exist a constant `C > 0` and a threshold `N₀` (both depending only on `k`, `h`, `θ`, `δ` —and
in particular *not* on `N`), such that for every `N ≥ N₀`, every sieve weight `λ` supported as
required, and every valid residue class `v_0`, the sieve sum `S_1` satisfies
-/
@[pg_tag "bg246" "lem_S1_after_CRT"]
theorem main_S1_asymptotic
    {k : ℕ} (hk : 2 ≤ k) (h : Fin k → ℕ) (hadm : IsAdmissible h) :
    ∀ θ δ : ℝ, θ ∈ Set.Ioo (0 : ℝ) 1 → δ ∈ Set.Ioo (0 : ℝ) (θ / 2) → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ,
      ∀ N : ℕ, N₀ ≤ N →
      ∀ lam : (Fin k → ℕ) →₀ ℝ, lam.HasPermissibleSupport ⌊R⌋₊ (W N) →
      ∀ v0 : ℕ, V0Valid h (W N) v0 →
        |S1 h lam N (W N) v0 - (N / (W N : ℝ)) * primedSum (W N) lam| ≤
          C * (Finsupp.maxRealAbs (PrimeGaps.lToY lam)) ^ 2 * (Nat.totient (W N) : ℝ) ^ k * N *
            (Real.log (R)) ^ k /
              ((W N : ℝ) ^ (k + 1) * D₀ N) := by
  intro θ δ hθ hδ
  obtain ⟨C, hC, N₀, hbound⟩ := lem_error_bound hk h hadm θ δ hθ hδ
  refine ⟨C, hC, max N₀ 3, ?_⟩
  intro N hN lam hsupp v0 hv0
  have hN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  obtain ⟨D, hD, hS1⟩ := lem_S1_expand_swap h lam N (W N) v0 (N ^ (θ / 2 - δ)) hsupp
  set mp : (Fin k → ℕ) → (Fin k → ℕ) → ℝ := fun d e ↦
    (if (∀ i, 0 < d i) ∧ (∀ i, 0 < e i) ∧ PrimeGaps.PairwiseCoprimeModuli (W N) (fun i ↦
      Nat.lcm (d i) (e i)) then
        N / (PrimeGaps.qMod (W N) d e : ℝ) else 0) with hmp
  have hsplit : S1 h lam N (W N) v0 - (N / (W N : ℝ)) * primedSum (W N) lam =
        ∑ d ∈ D, ∑ e ∈ D, lam d * lam e *
              ((pairCount h N (W N) v0 d e : ℝ) - mp d e) := by
    rw [hS1]
    have hmain : ∑ d ∈ D, ∑ e ∈ D, lam d * lam e * mp d e =
        (N / (W N : ℝ)) * primedSum (W N) lam := by
      rw [← lem_main_term lam N (W N) D hD, hmp]
      simp only [mul_ite, mul_zero]
    rw [← hmain, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun e _ ↦ by ring
  rw [hsplit]
  exact hbound N hN₀ lam hsupp v0 hv0 D hD

end GPYSieveS1
