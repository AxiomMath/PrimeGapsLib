/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Nat.Dist
public import PrimeGapsTheory.Foundations.SieveDatum

/-!
# Chinese remainder theorem identities

Proves finite Chinese-remainder equivalences and bounds prime factors of sieve moduli.

## Main results

* `Int.crt_equiv`: Combines congruences for a finite pairwise-coprime family.
* `PrimeGaps.primeFactor_large`: Every prime factor of a modulus coprime to the primorial
  exceeds the sieve level `D₀ N`.
* `PrimeGaps.exists_shift_gap_threshold`: Bounds all fixed pairwise shift gaps by a common
  threshold.
-/

@[expose] public section

open scoped PrimeGaps

open Finset

namespace Int

/-- If `a ≡ r [ZMOD M]` and `r` is coprime to `M`, then `a` is coprime to `M`. -/
theorem coprime_of_modEq {a r M : ℤ} (hmod : a ≡ r [ZMOD M]) (hcop : IsCoprime r M) :
    IsCoprime a M := by
  obtain ⟨s, hs⟩ := Int.modEq_iff_dvd.1 hmod
  rw [show a = r + M * (-s) by linarith]
  exact hcop.add_mul_left_left (-s)

/-- For coprime `a, b` and any residues `r1, r2`, there is `x` with `x ≡ r1 [ZMOD a]` and
`x ≡ r2 [ZMOD b]`.
-/
theorem crt2 (a b : ℤ) (hab : IsCoprime a b) (r1 r2 : ℤ) :
    ∃ x : ℤ, x ≡ r1 [ZMOD a] ∧ x ≡ r2 [ZMOD b] := by
  obtain ⟨u, v, huv⟩ := hab
  refine ⟨r1 * (v * b) + r2 * (u * a), Int.modEq_iff_dvd.2 ⟨r1 * u - r2 * u, ?_⟩,
    Int.modEq_iff_dvd.2 ⟨r2 * v - r1 * v, ?_⟩⟩
  · linear_combination (-r1) * huv
  · linear_combination (-r2) * huv

/-- For coprime `a, b`, a congruence mod `a*b` is equivalent to the pair of congruences mod `a` and
mod `b`.
-/
theorem crt2_equiv (a b : ℤ) (hab : IsCoprime a b) (x : ℤ) (p : ℤ) :
    (p ≡ x [ZMOD a] ∧ p ≡ x [ZMOD b]) ↔ p ≡ x [ZMOD a * b] := by
  rw [Int.modEq_iff_dvd, Int.modEq_iff_dvd, Int.modEq_iff_dvd]
  exact ⟨fun h ↦ hab.mul_dvd h.1 h.2,
    fun h ↦ ⟨(dvd_mul_right a b).trans h, (dvd_mul_left b a).trans h⟩⟩

/-- For a family of pairwise-coprime moduli `M i` over `i ∈ s` and any residues `R i`, there is `x`
such that satisfying all the congruences `p ≡ R i [ZMOD M i]` is equivalent to the single
congruence `p ≡ x [ZMOD ∏ i ∈ s, M i]`.
-/
theorem crt_equiv {ι : Type*} (s : Finset ι) (M R : ι → ℤ)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (M i) (M j)) :
    ∃ x : ℤ, ∀ p, (∀ i ∈ s, p ≡ R i [ZMOD M i]) ↔ p ≡ x [ZMOD ∏ i ∈ s, M i] := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨0, fun p ↦ by simp [Int.ModEq]⟩
  | @insert a s ha ih =>
    obtain ⟨x, hx⟩ := ih fun i hi j hj hij ↦
      hcop i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij
    have hcopP : IsCoprime (M a) (∏ i ∈ s, M i) := IsCoprime.prod_right fun i hi ↦
      hcop a (mem_insert_self a s) i (mem_insert_of_mem hi) (by rintro rfl; exact ha hi)
    obtain ⟨y, hy1, hy2⟩ := crt2 (M a) (∏ i ∈ s, M i) hcopP (R a) x
    refine ⟨y, fun p ↦ ?_⟩
    rw [Finset.prod_insert ha, ← crt2_equiv (M a) (∏ i ∈ s, M i) hcopP y p]
    refine ⟨fun hp ↦ ⟨(hp a (mem_insert_self a s)).trans hy1.symm,
      ((hx p).mp fun i hi ↦ hp i (mem_insert_of_mem hi)).trans hy2.symm⟩, ?_⟩
    rintro ⟨hpa, hps⟩ i hi
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · exact hpa.trans hy1
    · exact (hx p).mpr (hps.trans hy2) i hi'

end Int

namespace Nat

/-- The real absolute difference of two casts of naturals equals the cast of their `Nat.dist`. -/
theorem abs_sub_cast_eq_dist (a b : ℕ) : |(a : ℝ) - (b : ℝ)| = ((a.dist b : ℕ) : ℝ) := by
  rcases le_total a b with hle | hle
  · rw [Nat.dist_eq_sub_of_le hle, abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hle))]
    push_cast [Nat.cast_sub hle]
    ring
  · rw [Nat.dist_eq_sub_of_le_right hle, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hle))]
    push_cast [Nat.cast_sub hle]
    ring

end Nat

namespace PrimeGaps

/-- If a natural `m` is coprime to `W = primorial ⌊D₀ N⌋₊` and a prime `p` divides `m`, then `p`
exceeds `D₀ N = log log log N` (every prime `≤ ⌊D₀ N⌋₊` already divides the primorial).
-/
theorem primeFactor_large (N : ℝ) (m p : ℕ) (hcop : Nat.Coprime m (primorial ⌊D₀ N⌋₊))
    (hp : p.Prime) (hpm : p ∣ m) : D₀ N < (p : ℝ) := by
  have hpW : ¬ p ∣ primorial ⌊D₀ N⌋₊ := fun hpW ↦
    hp.one_lt.ne' ((Nat.Coprime.coprime_dvd_left hpm hcop).eq_one_of_dvd hpW)
  by_contra! hle
  refine hpW ?_
  unfold primorial
  refine Finset.dvd_prod_of_mem _ ?_
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le (Nat.le_floor hle), hp⟩

/-- Every prime dividing `Nat.lcm (d i) (e i)` exceeds `D₀ N`, provided `∏ i, d i` and `∏ i, e i`
are coprime to `primorial ⌊D₀ N⌋₊`. -/
theorem lcm_prime_factor_large {k : ℕ} (N : ℝ) (d e : Fin k → ℕ)
    (hcd : (∏ i, d i).Coprime (primorial ⌊D₀ N⌋₊))
    (hce : (∏ i, e i).Coprime (primorial ⌊D₀ N⌋₊))
    (i : Fin k) (p : ℕ) (hp : p.Prime) (hpi : p ∣ Nat.lcm (d i) (e i)) :
    D₀ N < (p : ℝ) := by
  rcases hp.dvd_mul.mp (hpi.trans (Nat.lcm_dvd_mul (d i) (e i))) with hpd | hpe
  · exact primeFactor_large N (∏ i, d i) p hcd hp
      (hpd.trans (Finset.dvd_prod_of_mem d (Finset.mem_univ i)))
  · exact primeFactor_large N (∏ i, e i) p hce hp
      (hpe.trans (Finset.dvd_prod_of_mem e (Finset.mem_univ i)))

/-- `D₀ N = log log log N` tends to `+∞` as `N → ∞`. -/
theorem D0_tendsto_atTop : Filter.Tendsto D₀ Filter.atTop Filter.atTop := by
  unfold D₀
  exact Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)

/-- For a fixed shift tuple `h: Fin k → ℕ`, there is a real threshold `N₀ ≥ 3` past which `D₀ N`
strictly dominates every pairwise gap: `(hᵢ.dist hⱼ) + 1 ≤ D₀ N` for all `i ≠ j` and all real
`N ≥ N₀`.
-/
theorem exists_shift_gap_threshold {k : ℕ} (h : Fin k → ℕ) :
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ i j : Fin k, i ≠ j → ((h i).dist (h j) : ℝ) + 1 ≤ D₀ N := by
  set T : ℝ := (∑ p : Fin k × Fin k, ((h p.1).dist (h p.2) : ℝ)) + 1 with hT
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (D0_tendsto_atTop.eventually_ge_atTop T)
  refine ⟨max M 3, le_max_right _ _, fun N hN i j hij ↦ ?_⟩
  have hbig : T ≤ D₀ N := hM N (le_trans (le_max_left _ _) hN)
  have hle : ((h i).dist (h j) : ℝ) ≤ ∑ p : Fin k × Fin k, ((h p.1).dist (h p.2) : ℝ) :=
    Finset.single_le_sum (f := fun p : Fin k × Fin k ↦ ((h p.1).dist (h p.2) : ℝ))
      (fun p _ ↦ by positivity) (Finset.mem_univ (i, j))
  rw [hT] at hbig
  linarith

end PrimeGaps

end
