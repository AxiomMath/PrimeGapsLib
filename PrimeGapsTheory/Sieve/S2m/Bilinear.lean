/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.Convex.Measure
public import PrimeGapsTheory.Sieve.S2m.Smooth

/-!
# Bilinear second-moment sums

This module develops the two-weight form of the second-moment CRT expansion.

## Main definitions

* `bilinearPrimeSum`: The prime-weighted product of two divisor sums.
* `restrictedCrossSum`: The corresponding restricted CRT main term.
* `twoWeightError`: The aggregate two-weight Bombieri–Vinogradov error.

## Main results

* `bilinearPrimeSum_crt_bound`: The bilinear CRT error estimate.
* `restrictedCrossSum_eq_ym_polarization_finsupp`: Polarization after substitution.
-/

@[expose] public section

open Real
open scoped ArithmeticFunction.detotient

namespace PrimeGaps

/-- The aggregate Bombieri–Vinogradov error of a bilinear form with weights `λ, λ'`:
`∑_{d,e} |λ_d| |λ'_e| · E(X, q(d,e))`, where `q(d,e)` is built from `modulus` and
`E = windowError`. -/
noncomputable def twoWeightError (k : ℕ) (X : ℝ) (modulus : ℕ) (m : Fin k)
    (lam lam' : (Fin k → ℕ) → ℝ) : ℝ :=
  ∑' d : Fin k → ℕ, ∑' e : Fin k → ℕ, (if d m = 1 ∧ e m = 1 ∧ lam d * lam' e ≠ 0 then
        |lam d| * |lam' e| * MaynardS2Error.windowError X (PrimeGaps.qMod modulus d e)
      else 0)

/-- The polarization of a quadratic form: `(Q (x + y) - Q x - Q y) / 2`. -/
noncomputable def quadraticPolarization {V : Type*} [Add V] (Q : V → ℝ) (x y : V) : ℝ :=
  (Q (x + y) - Q x - Q y) / 2

/-- The prime-weighted bilinear divisor sum for two arbitrary weights. -/
noncomputable def bilinearPrimeSum {k : ℕ} (h : Fin k → ℕ) (N : ℕ) (m : Fin k)
    (lam₁ lam₂ : (Fin k → ℕ) → ℝ) (w₀ : ZMod (PrimeGaps.sieveModulus N)) : ℝ :=
  quadraticPolarization (fun lam ↦ PrimeGaps.S₂m h lam N w₀ m) lam₁ lam₂

/-- `0 ≤ S₂m h lam N w₀ m`, the second moment being a sum of nonnegative terms. -/
theorem S₂m_nonneg {k : ℕ} (h : Fin k → ℕ) (lam : (Fin k → ℕ) → ℝ)
    (N : ℕ) (w₀ : ZMod (PrimeGaps.sieveModulus N)) (m : Fin k) :
    0 ≤ PrimeGaps.S₂m h lam N w₀ m :=
  Finset.sum_nonneg fun n _ ↦ mul_nonneg (by positivity) PrimeGaps.w_nonneg

/-- If `lam = lam₁ + lam₂`, its second moment is bounded below by the `lam₁` square
and twice the `lam₁`, `lam₂` mixed term. -/
theorem bilinear_split_lower {k : ℕ} (h : Fin k → ℕ) (N : ℕ) (m : Fin k)
    (lam lam₁ lam₂ : (Fin k → ℕ) → ℝ)
    (hsplit : ∀ d, lam₁ d + lam₂ d = lam d)
    (w₀ : ZMod (PrimeGaps.sieveModulus N)) :
    PrimeGaps.S₂m h lam₁ N w₀ m + 2 * bilinearPrimeSum h N m lam₁ lam₂ w₀ ≤
      PrimeGaps.S₂m h lam N w₀ m := by
  simp only [bilinearPrimeSum, quadraticPolarization, ← (funext hsplit : lam₁ + lam₂ = lam)]
  linarith [S₂m_nonneg h lam₂ N w₀ m]

/-- Exact expansion of the bilinear prime sum into the CRT kernel. -/
theorem bilinearPrimeSum_eq_crux {k : ℕ} (h : Fin k → ℕ) (N : ℕ) (m : Fin k)
    (lam₁ lam₂ : (Fin k → ℕ) → ℝ) (w₀ : ZMod (PrimeGaps.sieveModulus N))
    (L₁ L₂ : (Fin k → ℕ) →₀ ℝ)
    (hL₁ : ⇑L₁ = lam₁) (hL₂ : ⇑L₂ = lam₂) :
    bilinearPrimeSum h N m lam₁ lam₂ w₀ = ∑ d ∈ L₁.support, ∑ e ∈ L₂.support,
          lam₁ d * lam₂ e * PrimeGaps.sieveCount (fun i ↦ (h i : ℤ)) m
                (PrimeGaps.sieveModulus N) (w₀.val : ℤ) d e N := by
  let D := L₁.support ∪ L₂.support
  have hL₁D : L₁.support ⊆ D := Finset.subset_union_left
  have hL₂D : L₂.support ⊆ D := Finset.subset_union_right
  have hadd := S2m_expand_to_crux_S_on h m N w₀ (lam₁ + lam₂) (L₁ + L₂)
    (by simp [hL₁, hL₂]) D Finsupp.support_add
  have h₁ := S2m_expand_to_crux_S_on h m N w₀ lam₁ L₁ hL₁ D hL₁D
  have h₂ := S2m_expand_to_crux_S_on h m N w₀ lam₂ L₂ hL₂ D hL₂D
  have hswap : (∑ d ∈ D, ∑ e ∈ D, lam₂ d * lam₁ e *
        PrimeGaps.sieveCount (fun i ↦ (h i : ℤ)) m (PrimeGaps.sieveModulus N) (w₀.val : ℤ) d e N) =
      ∑ d ∈ D, ∑ e ∈ D, lam₁ d * lam₂ e *
        PrimeGaps.sieveCount (fun i ↦ (h i : ℤ)) m (PrimeGaps.sieveModulus N)
          (w₀.val : ℤ) d e N := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun e _ ↦ by
      rw [PrimeGaps.sieveCount_comm, mul_comm (lam₂ e)]
  have hrestrict : (∑ d ∈ D, ∑ e ∈ D, lam₁ d * lam₂ e *
        PrimeGaps.sieveCount (fun i ↦ (h i : ℤ)) m (PrimeGaps.sieveModulus N) (w₀.val : ℤ) d e N) =
      ∑ d ∈ L₁.support, ∑ e ∈ L₂.support, lam₁ d * lam₂ e *
        PrimeGaps.sieveCount (fun i ↦ (h i : ℤ)) m (PrimeGaps.sieveModulus N)
          (w₀.val : ℤ) d e N := by
    refine (Finset.sum_subset hL₁D fun d _ hd ↦ Finset.sum_eq_zero fun e _ ↦ ?_).symm.trans
      (Finset.sum_congr rfl fun d _ ↦ (Finset.sum_subset hL₂D fun e _ he ↦ ?_).symm)
    · simp [← hL₁, Finsupp.notMem_support_iff.mp hd]
    · simp [← hL₂, Finsupp.notMem_support_iff.mp he]
  simp only [bilinearPrimeSum, quadraticPolarization]
  rw [hadd, h₁, h₂]
  simp_rw [Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib, add_mul,
    Finset.sum_add_distrib]
  linear_combination hswap / 2 + hrestrict

/-- The bilinear restricted CRT summand for two weights. -/
noncomputable def restrictedCrossSummand {k : ℕ} (h : Fin k → ℕ) (m : Fin k) (modulus : ℕ)
    (lam₁ lam₂ : (Fin k → ℕ) → ℝ) (p : (Fin k → ℕ) × (Fin k → ℕ)) : ℝ :=
  lam₁ p.1 * lam₂ p.2 * restrictedKernel h m modulus p

/-- The restricted bilinear CRT main form. -/
noncomputable def restrictedCrossSum {k : ℕ} (h : Fin k → ℕ) (m : Fin k) (modulus : ℕ)
    (lam₁ lam₂ : (Fin k → ℕ) → ℝ) : ℝ :=
  ∑' p : (Fin k → ℕ) × (Fin k → ℕ), restrictedCrossSummand h m modulus lam₁ lam₂ p

/-- Swapping the two weights leaves the restricted bilinear main form unchanged. -/
theorem restrictedCrossSum_comm {k : ℕ} (h : Fin k → ℕ) (m : Fin k) (modulus : ℕ)
    (lam₁ lam₂ : (Fin k → ℕ) → ℝ) :
    restrictedCrossSum h m modulus lam₁ lam₂ = restrictedCrossSum h m modulus lam₂ lam₁ :=
  ((Equiv.prodComm _ _).tsum_eq _).symm.trans <| tsum_congr fun ⟨d, e⟩ ↦ by
    grind [restrictedCrossSummand, restrictedKernel_comm]

/-- Pointwise polarization of the quadratic restricted CRT summand. -/
theorem restrictedSummand_add {k : ℕ} (h : Fin k → ℕ) (m : Fin k) (modulus : ℕ)
    (lam₁ lam₂ : (Fin k → ℕ) → ℝ) (p : (Fin k → ℕ) × (Fin k → ℕ)) :
    restrictedSummand h m modulus (fun d ↦ lam₁ d + lam₂ d) p =
      restrictedSummand h m modulus lam₁ p + restrictedSummand h m modulus lam₂ p +
        restrictedCrossSummand h m modulus lam₁ lam₂ p +
        restrictedCrossSummand h m modulus lam₂ lam₁ p := by
  grind [restrictedCrossSummand, restrictedKernel, restrictedSummand]

/-- Finite support makes the quadratic restricted CRT form summable. -/
theorem summable_restrictedSummand {k : ℕ} (h : Fin k → ℕ) (m : Fin k) (modulus : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (L : (Fin k → ℕ) →₀ ℝ) (hL : ⇑L = lam) :
    Summable (restrictedSummand h m modulus lam) := by
  subst hL
  refine summable_of_ne_finset_zero (s := L.support ×ˢ L.support) fun p hp ↦ ?_
  grind [restrictedSummand]

/-- Separate finite supports make the bilinear restricted CRT form summable. -/
theorem summable_restrictedCrossSummand {k : ℕ} (h : Fin k → ℕ) (m : Fin k) (modulus : ℕ)
    (lam₁ lam₂ : (Fin k → ℕ) → ℝ) (L₁ L₂ : (Fin k → ℕ) →₀ ℝ)
    (hL₁ : ⇑L₁ = lam₁) (hL₂ : ⇑L₂ = lam₂) :
    Summable (restrictedCrossSummand h m modulus lam₁ lam₂) := by
  subst hL₁ hL₂
  refine summable_of_ne_finset_zero (s := L₁.support ×ˢ L₂.support) fun p hp ↦ ?_
  grind [restrictedCrossSummand]

/-- Polarization identity for the full restricted CRT forms. -/
theorem restrictedCrossSum_polarization {k : ℕ} (h : Fin k → ℕ) (m : Fin k) (modulus : ℕ)
    (lam₁ lam₂ : (Fin k → ℕ) → ℝ) (L₁ L₂ : (Fin k → ℕ) →₀ ℝ)
    (hL₁ : ⇑L₁ = lam₁) (hL₂ : ⇑L₂ = lam₂) :
    2 * restrictedCrossSum h m modulus lam₁ lam₂ =
      (∑' p, restrictedSummand h m modulus (fun d ↦ lam₁ d + lam₂ d) p) -
        (∑' p, restrictedSummand h m modulus lam₁ p) -
          ∑' p, restrictedSummand h m modulus lam₂ p := by
  have hs₁ := summable_restrictedSummand h m modulus lam₁ L₁ hL₁
  have hs₂ := summable_restrictedSummand h m modulus lam₂ L₂ hL₂
  have hsc₁₂ := summable_restrictedCrossSummand h m modulus lam₁ lam₂ L₁ L₂ hL₁ hL₂
  have hsc₂₁ := summable_restrictedCrossSummand h m modulus lam₂ lam₁ L₂ L₁ hL₂ hL₁
  have hpoint : (∑' p, restrictedSummand h m modulus (fun d ↦ lam₁ d + lam₂ d) p) = _ :=
    tsum_congr (restrictedSummand_add h m modulus lam₁ lam₂)
  rw [((hs₁.add hs₂).add hsc₁₂).tsum_add hsc₂₁, (hs₁.add hs₂).tsum_add hsc₁₂,
    hs₁.tsum_add hs₂] at hpoint
  have hcomm := restrictedCrossSum_comm h m modulus lam₁ lam₂
  unfold restrictedCrossSum at hcomm ⊢
  linear_combination hcomm - hpoint

/-- Polarized finite-support identity for the restricted main term. -/
theorem restrictedCrossSum_eq_ym_polarization_finsupp {k : ℕ}
    (h : Fin k → ℕ) (m : Fin k) (hinj : Function.Injective h)
    (Θ Δ : ℝ) (N : ℕ)
    (lam₁ lam₂ : (Fin k → ℕ) → ℝ) (L₁ L₂ : (Fin k → ℕ) →₀ ℝ)
    (hL₁ : ⇑L₁ = lam₁) (hL₂ : ⇑L₂ = lam₂)
    (hsupp₁ : L₁.HasPermissibleSupport
      ⌊(N : ℝ) ^ (Θ / 2 - Δ)⌋₊ (PrimeGaps.sieveModulus N))
    (hsupp₂ : L₂.HasPermissibleSupport
      ⌊(N : ℝ) ^ (Θ / 2 - Δ)⌋₊ (PrimeGaps.sieveModulus N))
    (hD0 : ∀ i j : Fin k, i ≠ j → (h i).dist (h j) < ⌊PrimeGaps.D₀ (N : ℝ)⌋₊)
    (hN2 : 2 ≤ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊) :
    2 * restrictedCrossSum h m (PrimeGaps.sieveModulus N) lam₁ lam₂ =
      ymWeightedSum m (L₁ + L₂) - ymWeightedSum m L₁ - ymWeightedSum m L₂ := by
  have hLadd : ⇑(L₁ + L₂) = fun d ↦ lam₁ d + lam₂ d := funext fun d ↦ by simp [hL₁, hL₂]
  have hsuppAdd : (L₁ + L₂).HasPermissibleSupport
      ⌊(N : ℝ) ^ (Θ / 2 - Δ)⌋₊ (PrimeGaps.sieveModulus N) :=
    Finsupp.support_add.trans (Finset.union_subset hsupp₁ hsupp₂)
  rw [← restrictedSummand_tsum_eq_ymWeightedSum h m hinj Θ Δ N (L₁ + L₂) hsuppAdd hD0 hN2,
    ← restrictedSummand_tsum_eq_ymWeightedSum h m hinj Θ Δ N L₁ hsupp₁ hD0 hN2,
    ← restrictedSummand_tsum_eq_ymWeightedSum h m hinj Θ Δ N L₂ hsupp₂ hD0 hN2]
  simpa [hLadd, hL₁, hL₂] using restrictedCrossSum_polarization h m (PrimeGaps.sieveModulus N)
    lam₁ lam₂ L₁ L₂ hL₁ hL₂

/-- The eligible prime-counting term has the normalization of the restricted bilinear form. -/
theorem restrictedPrimeTerm_mul_eq {k : ℕ} (h : Fin k → ℕ) (m : Fin k) (N modulus : ℕ)
    (lam₁ lam₂ : (Fin k → ℕ) → ℝ) (d e : Fin k → ℕ)
    (hmodulus : 0 < modulus) (hdpos : ∀ i, 1 ≤ d i) (hepos : ∀ i, 1 ≤ e i) :
    lam₁ d * lam₂ e * restrictedPrimeTerm h m N modulus d e =
      (Nat.primeCountingIoc N (2 * N) : ℝ) / modulus.totient *
          restrictedCrossSummand h m modulus lam₁ lam₂ (d, e) := by
  unfold restrictedPrimeTerm restrictedCrossSummand restrictedKernel restrictedSummand
    PrimeGaps.qMod
  dsimp only
  split_ifs with helig
  · have hφW : (modulus.totient : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hmodulus).ne'
    have hφprod : (∏ i, (((d i).lcm (e i)).totient : ℝ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ ↦ Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr
        (Nat.pos_of_ne_zero (Nat.lcm_ne_zero (Nat.one_le_iff_ne_zero.mp (hdpos i))
          (Nat.one_le_iff_ne_zero.mp (hepos i))))).ne'
    rw [totient_W_mul_lcm_prod modulus d e helig.2.2.1 helig.2.2.2.1]
    push_cast
    field_simp
  · ring

/-- Weighted per-pair CRT estimate when `l` supports both coefficient functions. -/
theorem weighted_crux_sub_restricted_le {k : ℕ}
    (h : Fin k → ℕ) (m : Fin k) (hinj : Function.Injective h)
    (θ δ : ℝ) (N : ℕ) (w₀ : ZMod (PrimeGaps.sieveModulus N))
    (hw₀ : ∀ i, ((w₀.val : ℤ) + (h i : ℤ)).gcd (PrimeGaps.sieveModulus N) = 1)
    (l : (Fin k → ℕ) → ℝ)
    (hsupp : ∀ d, l d ≠ 0 → d ∈ Finset.permissibleSupport k
      ⌊(N : ℝ) ^ (θ / 2 - δ)⌋₊ (PrimeGaps.sieveModulus N))
    (hD0_large : ∀ i j : Fin k, i ≠ j → (h i).dist (h j) < ⌊PrimeGaps.D₀ (N : ℝ)⌋₊)
    (hcoord_lcm_lt_prime : ∀ dd ee, l dd ≠ 0 → l ee ≠ 0 → ∀ i, (dd i).lcm (ee i) < N + h m)
    (Ccrt : ℝ) (hCcrt : 0 < Ccrt)
    (hCRT : ∀ (W : ℕ) (v₀ : ℤ) (d e : Fin k → ℕ) (q : ℕ) (Narg : ℕ), 1 ≤ W →
      (∀ i, 1 ≤ d i) → (∀ i, 1 ≤ e i) →
      d m = 1 → e m = 1 →
      (∀ i, W.Coprime ((d i).lcm (e i))) →
      (∀ i j, i ≠ j → ((d i).lcm (e i)).Coprime ((d j).lcm (e j))) →
      q = W * ∏ i, (d i).lcm (e i) →
      (∀ i, (v₀ + (h i : ℤ)).gcd (W : ℤ) = 1) →
      (∀ i, i ≠ m → ((h m : ℤ) - (h i : ℤ)).gcd ((d i).lcm (e i) : ℤ) = 1) →
      |PrimeGaps.sieveCount (fun i ↦ (h i : ℤ)) m W v₀ d e Narg -
          (Nat.primeCountingIoc Narg (2 * Narg) : ℝ) / q.totient| ≤
        Ccrt * Nat.primeCountingIocError Narg (2 * Narg) q)
    (lam₁ lam₂ : (Fin k → ℕ) → ℝ) (d e : Fin k → ℕ)
    (hd : l d ≠ 0) (he : l e ≠ 0) :
    |lam₁ d * lam₂ e * PrimeGaps.sieveCount (fun i ↦ (h i : ℤ)) m
              (PrimeGaps.sieveModulus N) (w₀.val : ℤ) d e N -
        (Nat.primeCountingIoc N (2 * N) : ℝ) / (PrimeGaps.sieveModulus N).totient *
            restrictedCrossSummand h m (PrimeGaps.sieveModulus N) lam₁ lam₂ (d, e)| ≤
        Ccrt * (if d m = 1 ∧ e m = 1 then
            |lam₁ d| * |lam₂ e| * MaynardS2Error.windowError (N : ℝ)
                  (PrimeGaps.qMod (PrimeGaps.sieveModulus N) d e)
          else 0) := by
  by_cases hm : d m = 1 ∧ e m = 1
  · have hbase := crux_sub_restrictedPrimeTerm_le h m hinj θ δ N w₀ hw₀ l hsupp
      hD0_large hcoord_lcm_lt_prime Ccrt hCcrt hCRT d e hd he
    have hdpos : ∀ i, 1 ≤ d i := fun i ↦ Nat.one_le_iff_ne_zero.mpr
      ((Finset.mem_permissibleSupport_iff'.mp (hsupp d hd)).1 i)
    have hepos : ∀ i, 1 ≤ e i := fun i ↦ Nat.one_le_iff_ne_zero.mpr
      ((Finset.mem_permissibleSupport_iff'.mp (hsupp e he)).1 i)
    rw [if_pos hm, ← restrictedPrimeTerm_mul_eq h m N (PrimeGaps.sieveModulus N) lam₁ lam₂ d e
      PrimeGaps.W_pos hdpos hepos, ← mul_sub, abs_mul, abs_mul]
    exact (mul_le_mul_of_nonneg_left hbase (by positivity)).trans_eq (by ring)
  · have hrs : restrictedCrossSummand h m (PrimeGaps.sieveModulus N) lam₁ lam₂ (d, e) = 0 := by
      grind [restrictedCrossSummand, restrictedKernel, restrictedSummand]
    rw [if_neg hm, crux_S_vanish_of_not_restricted h m hinj θ δ N w₀ hw₀ l hsupp hD0_large
      hcoord_lcm_lt_prime d e hd he (fun H ↦ hm ⟨H.1, H.2.1⟩), hrs]
    simp

/-- A finite-support presentation of the restricted bilinear main form. -/
theorem restrictedCrossSum_eq_support_sum {k : ℕ} (h : Fin k → ℕ) (m : Fin k) (modulus : ℕ)
    (lam₁ lam₂ : (Fin k → ℕ) → ℝ) (L₁ L₂ : (Fin k → ℕ) →₀ ℝ)
    (hL₁ : ⇑L₁ = lam₁) (hL₂ : ⇑L₂ = lam₂) :
    restrictedCrossSum h m modulus lam₁ lam₂ = ∑ d ∈ L₁.support, ∑ e ∈ L₂.support,
          restrictedCrossSummand h m modulus lam₁ lam₂ (d, e) := by
  subst hL₁ hL₂
  rw [restrictedCrossSum, tsum_eq_sum (s := L₁.support ×ˢ L₂.support), Finset.sum_product]
  grind [restrictedCrossSummand]

/-- On the actual supports, `twoWeightError` is the expected finite double
sum with no remaining gate. -/
theorem twoWeightError_eq_support_sum {k : ℕ} (m : Fin k) (X : ℝ) (modulus : ℕ)
    (lam₁ lam₂ : (Fin k → ℕ) → ℝ) (L₁ L₂ : (Fin k → ℕ) →₀ ℝ)
    (hL₁ : ⇑L₁ = lam₁) (hL₂ : ⇑L₂ = lam₂) :
    twoWeightError k X modulus m lam₁ lam₂ =
      ∑ d ∈ L₁.support, ∑ e ∈ L₂.support, if d m = 1 ∧ e m = 1 then
            |lam₁ d| * |lam₂ e| * MaynardS2Error.windowError X (PrimeGaps.qMod modulus d e)
          else 0 := by
  subst hL₁ hL₂
  rw [twoWeightError, tsum_eq_sum (s := L₁.support) fun d hd ↦ by
    simp [Finsupp.notMem_support_iff.mp hd]]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [tsum_eq_sum (s := L₂.support) fun e he ↦ by simp [Finsupp.notMem_support_iff.mp he]]
  exact Finset.sum_congr rfl fun e he ↦ by
    simp [Finsupp.mem_support_iff.mp hd, Finsupp.mem_support_iff.mp he]

/-- An aggregate bilinear CRT estimate. -/
theorem bilinear_crt_sum_bound {k : ℕ} (h : Fin k → ℕ) (m : Fin k) (hinj : Function.Injective h)
    (θ δ : ℝ) (N : ℕ) (w₀ : ZMod (PrimeGaps.sieveModulus N))
    (hw₀ : ∀ i, ((w₀.val : ℤ) + (h i : ℤ)).gcd (PrimeGaps.sieveModulus N) = 1)
    (l : (Fin k → ℕ) → ℝ)
    (hsupp : ∀ d, l d ≠ 0 → d ∈ Finset.permissibleSupport k
      ⌊(N : ℝ) ^ (θ / 2 - δ)⌋₊ (PrimeGaps.sieveModulus N))
    (hD0_large : ∀ i j : Fin k, i ≠ j → (h i).dist (h j) < ⌊PrimeGaps.D₀ (N : ℝ)⌋₊)
    (hcoord_lcm_lt_prime : ∀ dd ee, l dd ≠ 0 → l ee ≠ 0 → ∀ i, (dd i).lcm (ee i) < N + h m)
    (Ccrt : ℝ) (hCcrt : 0 < Ccrt)
    (hCRT : ∀ (W : ℕ) (v₀ : ℤ) (d e : Fin k → ℕ) (q : ℕ) (Narg : ℕ), 1 ≤ W →
      (∀ i, 1 ≤ d i) → (∀ i, 1 ≤ e i) →
      d m = 1 → e m = 1 →
      (∀ i, W.Coprime ((d i).lcm (e i))) →
      (∀ i j, i ≠ j → ((d i).lcm (e i)).Coprime ((d j).lcm (e j))) →
      q = W * ∏ i, (d i).lcm (e i) →
      (∀ i, (v₀ + (h i : ℤ)).gcd (W : ℤ) = 1) →
      (∀ i, i ≠ m → ((h m : ℤ) - (h i : ℤ)).gcd ((d i).lcm (e i) : ℤ) = 1) →
      |PrimeGaps.sieveCount (fun i ↦ (h i : ℤ)) m W v₀ d e Narg -
          (Nat.primeCountingIoc Narg (2 * Narg) : ℝ) / q.totient| ≤
        Ccrt * Nat.primeCountingIocError Narg (2 * Narg) q)
    (lam₁ lam₂ : (Fin k → ℕ) → ℝ) (L₁ L₂ : (Fin k → ℕ) →₀ ℝ)
    (hL₁ : ⇑L₁ = lam₁) (hL₂ : ⇑L₂ = lam₂)
    (hdom₁ : ∀ d, lam₁ d ≠ 0 → l d ≠ 0)
    (hdom₂ : ∀ e, lam₂ e ≠ 0 → l e ≠ 0) :
    |(∑ d ∈ L₁.support, ∑ e ∈ L₂.support,
      lam₁ d * lam₂ e * PrimeGaps.sieveCount (fun i ↦ (h i : ℤ)) m
            (PrimeGaps.sieveModulus N) (w₀.val : ℤ) d e N) -
      (Nat.primeCountingIoc N (2 * N) : ℝ) / (PrimeGaps.sieveModulus N).totient *
          restrictedCrossSum h m (PrimeGaps.sieveModulus N) lam₁ lam₂| ≤
        Ccrt *
          twoWeightError k (N : ℝ) (PrimeGaps.sieveModulus N) m lam₁ lam₂ := by
  subst hL₁ hL₂
  rw [restrictedCrossSum_eq_support_sum h m (PrimeGaps.sieveModulus N) _ _ L₁ L₂ rfl rfl,
    twoWeightError_eq_support_sum m (N : ℝ) (PrimeGaps.sieveModulus N) _ _ L₁ L₂ rfl rfl]
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans <| Finset.sum_le_sum fun d hd ↦
    (Finset.abs_sum_le_sum_abs _ _).trans <| Finset.sum_le_sum fun e he ↦
      weighted_crux_sub_restricted_le h m hinj θ δ N w₀ hw₀ l hsupp hD0_large
        hcoord_lcm_lt_prime Ccrt hCcrt hCRT _ _ d e
        (hdom₁ d (Finsupp.mem_support_iff.mp hd)) (hdom₂ e (Finsupp.mem_support_iff.mp he))

/-- The aggregate CRT bound for an arbitrary pair of finitely-supported weights. -/
theorem bilinearPrimeSum_crt_bound {k : ℕ} (h : Fin k → ℕ) (m : Fin k) (hinj : Function.Injective h)
    (θs δs : ℝ) (N : ℕ)
    (lam₁ lam₂ : (Fin k → ℕ) → ℝ) (w₀ : ZMod (PrimeGaps.sieveModulus N))
    (hw₀ : ∀ i, ((w₀.val : ℤ) + (h i : ℤ)).gcd (PrimeGaps.sieveModulus N) = 1)
    (l : (Fin k → ℕ) → ℝ)
    (hsupp : ∀ d, l d ≠ 0 → d ∈ Finset.permissibleSupport k
      ⌊(N : ℝ) ^ (θs / 2 - δs)⌋₊ (PrimeGaps.sieveModulus N))
    (hD0_large : ∀ i j : Fin k, i ≠ j → (h i).dist (h j) < ⌊PrimeGaps.D₀ (N : ℝ)⌋₊)
    (hcoord_lcm_lt_prime : ∀ dd ee, l dd ≠ 0 → l ee ≠ 0 → ∀ i, (dd i).lcm (ee i) < N + h m)
    (Ccrt : ℝ) (hCcrt : 0 < Ccrt)
    (hCRT : ∀ (W : ℕ) (v₀ : ℤ) (d e : Fin k → ℕ) (q : ℕ) (Narg : ℕ), 1 ≤ W →
      (∀ i, 1 ≤ d i) → (∀ i, 1 ≤ e i) →
      d m = 1 → e m = 1 →
      (∀ i, W.Coprime ((d i).lcm (e i))) →
      (∀ i j, i ≠ j → ((d i).lcm (e i)).Coprime ((d j).lcm (e j))) →
      q = W * ∏ i, (d i).lcm (e i) →
      (∀ i, (v₀ + (h i : ℤ)).gcd (W : ℤ) = 1) →
      (∀ i, i ≠ m → ((h m : ℤ) - (h i : ℤ)).gcd ((d i).lcm (e i) : ℤ) = 1) →
      |PrimeGaps.sieveCount (fun i ↦ (h i : ℤ)) m W v₀ d e Narg -
          (Nat.primeCountingIoc Narg (2 * Narg) : ℝ) / q.totient| ≤
        Ccrt * Nat.primeCountingIocError Narg (2 * Narg) q)
    (L₁ L₂ : (Fin k → ℕ) →₀ ℝ)
    (hL₁ : ⇑L₁ = lam₁) (hL₂ : ⇑L₂ = lam₂)
    (hdom₁ : ∀ d, lam₁ d ≠ 0 → l d ≠ 0)
    (hdom₂ : ∀ e, lam₂ e ≠ 0 → l e ≠ 0) :
    |bilinearPrimeSum h N m lam₁ lam₂ w₀ -
      (Nat.primeCountingIoc N (2 * N) : ℝ) / (PrimeGaps.sieveModulus N).totient *
          restrictedCrossSum h m (PrimeGaps.sieveModulus N) lam₁ lam₂| ≤
        Ccrt * twoWeightError k (N : ℝ) (PrimeGaps.sieveModulus N) m lam₁ lam₂ :=
  bilinearPrimeSum_eq_crux h N m lam₁ lam₂ w₀ L₁ L₂ hL₁ hL₂ ▸
    bilinear_crt_sum_bound h m hinj θs δs N w₀ hw₀ l hsupp hD0_large hcoord_lcm_lt_prime Ccrt
      hCcrt hCRT lam₁ lam₂ L₁ L₂ hL₁ hL₂ hdom₁ hdom₂

/-- One term of the diagonal `ym` quadratic form:
`(ym m L r) ^ 2 / ∏ i ∈ univ.erase m, detotient (r i)` on the admissible `r`,
and `0` elsewhere. -/
noncomputable def ymDiagonalTerm {k : ℕ} (m : Fin k) (modulus : ℕ)
    (L : (Fin k → ℕ) →₀ ℝ) (r : Fin k → ℕ) : ℝ :=
  if r m = 1 ∧ (∀ i, i ≠ m → 1 ≤ r i ∧ (r i).Coprime modulus)
  then (PrimeGaps.ym m L r) ^ 2 / (∏ i ∈ Finset.univ.erase m,
        (g (r i) : ℝ))
  else 0

/-- The diagonal `ym` quadratic form `∑' r, ymDiagonalTerm m modulus L r`. -/
noncomputable def ymDiagonalForm {k : ℕ} (m : Fin k) (modulus : ℕ) (L : (Fin k → ℕ) →₀ ℝ) : ℝ :=
  ∑' r : Fin k → ℕ, ymDiagonalTerm m modulus L r

/-- The transformed diagonal sum equals `ymDiagonalForm`. -/
theorem fromYm_diagonal_eq_ymDiagonalForm {k : ℕ} (m : Fin k) (R : ℝ) (W : ℕ) (L : (Fin k → ℕ) →₀ ℝ)
    (hL : L.HasPermissibleSupport ⌊R⌋₊ W) :
    (∑' u : Fin k → ℕ, if (∀ i, 1 ≤ u i) ∧ PrimeGaps.LemS1RestrictSij.RestrictedCoprime
            u (fun _ _ ↦ 1)
      then PrimeGaps.ym m L u ^ 2 / ∏ i, (g (u i) : ℝ)
      else 0) = ymDiagonalForm m W L := PrimeGaps.S2mSmooth.gapB m R W L hL

/-- One term of the diagonal `yInverseSum` quadratic form:
`(yInverseSum L m r) ^ 2 / ∏ i ∈ univ.erase m, detotient (r i)` on the admissible `r`,
and `0` elsewhere. -/
noncomputable def inverseDiagonalTerm {k : ℕ} (m : Fin k) (modulus : ℕ)
    (L : (Fin k → ℕ) →₀ ℝ) (r : Fin k → ℕ) : ℝ :=
  if r m = 1 ∧ (∀ i, i ≠ m → 1 ≤ r i ∧ (r i).Coprime modulus)
  then (yInverseSum L m r) ^ 2 / (∏ i ∈ Finset.univ.erase m,
        (g (r i) : ℝ))
  else 0

/-- The diagonal `yInverseSum` quadratic form `∑' r, inverseDiagonalTerm m modulus L r`. -/
noncomputable def inverseDiagonalForm {k : ℕ} (m : Fin k) (modulus : ℕ)
    (L : (Fin k → ℕ) →₀ ℝ) : ℝ :=
  ∑' r : Fin k → ℕ, inverseDiagonalTerm m modulus L r

/-- `inverseDiagonalTerm m modulus L` is summable whenever the divisor weight `L` has
permissible support: it vanishes outside a finite box. -/
theorem summable_inverseDiagonalTerm {k : ℕ} (R : ℝ) (modulus : ℕ)
    (m : Fin k) (L : (Fin k → ℕ) →₀ ℝ)
    (hL : L.HasPermissibleSupport ⌊R⌋₊ modulus) :
    Summable (inverseDiagonalTerm m modulus L) := by
  refine summable_of_ne_finset_zero
    (s := Fintype.piFinset fun _ : Fin k ↦ Finset.range (⌈R⌉₊ + 2)) fun r hr ↦ ?_
  obtain ⟨i, hi⟩ : ∃ i, ⌈R⌉₊ + 2 ≤ r i := by simpa using hr
  simp only [inverseDiagonalTerm]
  split_ifs with hg
  · have him : i ≠ m := by grind
    have hR : R < (r i : ℝ) := (Nat.le_ceil R).trans_lt (Nat.cast_lt.mpr (by omega))
    simp [yInverseSum_eq_zero_of_coord_ge hL him hR]
  · rfl

/-- Splitting a divisor weight by an outer-product cutoff splits its inverse diagonal form. -/
theorem inverseDiagonalForm_retainedL_add_discardedL {k : ℕ} (R B : ℝ)
    (m : Fin k) (W : ℕ) (L : (Fin k → ℕ) →₀ ℝ)
    (hL : L.HasPermissibleSupport ⌊R⌋₊ W) :
    inverseDiagonalForm m W L = inverseDiagonalForm m W (retainedL B m L) +
      inverseDiagonalForm m W (discardedL B m L) := by
  unfold inverseDiagonalForm
  rw [← Summable.tsum_add
    (summable_inverseDiagonalTerm R W m _ (retainedL_hasPermissibleSupport B m L hL))
    (summable_inverseDiagonalTerm R W m _ (discardedL_hasPermissibleSupport B m L hL))]
  refine tsum_congr fun r ↦ ?_
  grind [inverseDiagonalTerm, yInverseSum_retainedL, yInverseSum_discardedL]

/-- `(∏ i, d i : ℝ) ≤ R` for `d` in the permissible support at truncation `⌊R⌋₊`. -/
lemma cast_prod_le_of_mem_permissibleSupport {k W : ℕ} {R : ℝ}
    {d : Fin k → ℕ} (hd : d ∈ Finset.permissibleSupport k ⌊R⌋₊ W) :
    ((∏ i, d i : ℕ) : ℝ) ≤ R := by
  obtain ⟨-, hle, -, hsq⟩ := Finset.mem_permissibleSupport_iff'.mp hd
  exact (Nat.le_floor_iff' hsq.ne_zero).mp hle

/-- A polarization error bound for three diagonal approximations. -/
theorem abs_two_cross_le_of_weighted_diagonal_approximations (B X p a Y₀ Y₁ Y₂ D₀ D₁ D₂ I₀ I₁ I₂
      eb e₀ e₁ e₂ q₀ q₁ q₂ : ℝ)
    (ha : 0 ≤ a)
    (hB : |B - p * X| ≤ eb)
    (hpol : 2 * X = Y₀ - Y₁ - Y₂)
    (h₀ : |p * Y₀ - a * D₀| ≤ e₀)
    (h₁ : |p * Y₁ - a * D₁| ≤ e₁)
    (h₂ : |p * Y₂ - a * D₂| ≤ e₂)
    (hq₀ : |D₀ - I₀| ≤ q₀)
    (hq₁ : |D₁ - I₁| ≤ q₁)
    (hq₂ : |D₂ - I₂| ≤ q₂)
    (hinv : I₀ = I₁ + I₂) :
    |2 * B| ≤ 2 * eb + e₀ + e₁ + e₂ + a * (q₀ + q₁ + q₂) := by
  have tri : ∀ {x₀ x₁ x₂ c₀ c₁ c₂ : ℝ}, |x₀| ≤ c₀ → |x₁| ≤ c₁ → |x₂| ≤ c₂ →
      |x₀ - x₁ - x₂| ≤ c₀ + c₁ + c₂ := fun {x₀ x₁ _ _ _ _} h0 h1 h2 ↦
    ((abs_sub (x₀ - x₁) _).trans (add_le_add (abs_sub x₀ x₁) le_rfl)).trans
      (add_le_add (add_le_add h0 h1) h2)
  have hd : |p * (Y₀ - Y₁ - Y₂) - a * (D₀ - D₁ - D₂)| ≤ e₀ + e₁ + e₂ := by
    rw [show p * (Y₀ - Y₁ - Y₂) - a * (D₀ - D₁ - D₂) =
      p * Y₀ - a * D₀ - (p * Y₁ - a * D₁) - (p * Y₂ - a * D₂) by ring]
    exact tri h₀ h₁ h₂
  have hq : |D₀ - D₁ - D₂| ≤ q₀ + q₁ + q₂ := by
    rw [show D₀ - D₁ - D₂ = D₀ - I₀ - (D₁ - I₁) - (D₂ - I₂) by linear_combination hinv]
    exact tri hq₀ hq₁ hq₂
  have haq : |a * (D₀ - D₁ - D₂)| ≤ a * (q₀ + q₁ + q₂) := by
    rw [abs_mul, abs_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left hq ha
  have hb2 : |2 * (B - p * X)| ≤ 2 * eb := by
    rw [abs_mul, abs_two]
    linarith
  calc |2 * B|
      = |2 * (B - p * X) + (p * (Y₀ - Y₁ - Y₂) - a * (D₀ - D₁ - D₂)) + a * (D₀ - D₁ - D₂)| := by
        congr 1
        linear_combination p * hpol
    _ ≤ |2 * (B - p * X)| + |p * (Y₀ - Y₁ - Y₂) - a * (D₀ - D₁ - D₂)| + |a * (D₀ - D₁ - D₂)| :=
      abs_add_three _ _ _
    _ ≤ 2 * eb + e₀ + e₁ + e₂ + a * (q₀ + q₁ + q₂) := by linarith

/-- If `S = Fm²·φW^k·N·(log R)^k/(W^{k+1}·D₀)` and `log R = c·L`, then
`Ca·Fm²·N/L^{k+3} ≤ (Ca·K_W/c^k)·S` under the stated positivity and growth bounds. -/
theorem rsq_absorbA {k : ℕ} (Ca Fm φW Wr Nr L logR D0 c K_W S : ℝ)
    (hCa : 0 < Ca) (hφW : 1 ≤ φW) (hWr : 1 ≤ Wr)
    (hL : 1 ≤ L) (hD0 : 0 < D0) (hc : 0 < c) (hKW : 0 < K_W) (hNr : 0 ≤ Nr)
    (hlogR : logR = c * L)
    (hWa : Wr ^ (k + 1) * D0 ≤ K_W * L ^ (2 * k + 3))
    (hSform : S = Fm ^ 2 * φW ^ k * Nr * logR ^ k / (Wr ^ (k + 1) * D0)) :
    Ca * Fm ^ 2 * Nr / L ^ ((k : ℝ) + 3) ≤ (Ca * K_W / c ^ k) * S := by
  rw [hSform, hlogR, show L ^ ((k : ℝ) + 3) = L ^ (k + 3) by norm_cast]
  calc Ca * Fm ^ 2 * Nr / L ^ (k + 3)
      ≤ Ca * Fm ^ 2 * Nr * φW ^ k / L ^ (k + 3) := by
        gcongr ?_ / _
        exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hφW)
    _ = Ca * K_W / c ^ k * (Fm ^ 2 * φW ^ k * Nr * (c * L) ^ k / (K_W * L ^ (2 * k + 3))) := by
        field_simp
        ring
    _ ≤ Ca * K_W / c ^ k * (Fm ^ 2 * φW ^ k * Nr * (c * L) ^ k / (Wr ^ (k + 1) * D0)) := by gcongr

/-- On the diagonal the bilinear form is the quadratic one:
`restrictedCrossSum h m modulus lam lam = ∑' p, restrictedSummand h m modulus lam p`. -/
theorem restrictedCrossSum_self {k : ℕ} (h : Fin k → ℕ) (modulus : ℕ)
    (m : Fin k) (lam : (Fin k → ℕ) → ℝ) :
    restrictedCrossSum h m modulus lam lam =
      ∑' p, restrictedSummand h m modulus lam p := by
  grind [restrictedCrossSum, restrictedCrossSummand, restrictedKernel, restrictedSummand]

end PrimeGaps

namespace MeasureTheory

/-- A level set of the coordinate sum in a nonempty Euclidean space is Lebesgue-null. -/
theorem volume_setOf_sum_eq {ι : Type*} [Fintype ι] [Nonempty ι] (c : ℝ) :
    volume {x : EuclideanSpace ℝ ι | ∑ i, x i = c} = 0 := by
  let L : EuclideanSpace ℝ ι →L[ℝ] ℝ := ∑ i, EuclideanSpace.proj i
  have hL_apply : ∀ x : EuclideanSpace ℝ ι, L x = ∑ i, x i := fun x ↦ by simp [L]
  have hsurj : Function.Surjective L := fun y ↦
    ⟨WithLp.toLp 2 fun _ ↦ y / Fintype.card ι, by
      simp [hL_apply, Finset.card_univ,
        mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero : (Fintype.card ι : ℝ) ≠ 0)]⟩
  have hset : {x : EuclideanSpace ℝ ι | ∑ i, x i = c} = L ⁻¹' ({c} : Set ℝ) := by
    ext x
    simp [hL_apply]
  rw [hset, ← frontier_Iic, ← L.frontier_preimage hsurj]
  exact ((convex_Iic c).linear_preimage L.toLinearMap).addHaar_frontier volume

end MeasureTheory

namespace PrimeGaps

/-- `∑ i ∈ univ.erase m, insertLp m s t i = ∑ j, t j`: inserting `s` at `m` adds no other mass. -/
theorem sum_erase_insertLp {n : ℕ} (m : Fin (n + 1)) (s : ℝ) (t : EuclideanSpace ℝ (Fin n)) :
    ∑ i ∈ Finset.univ.erase m, (EuclideanSpace.insertLp m s t) i = ∑ j, t j := by
  simp [Finset.sum_erase_eq_sub, EuclideanSpace.sum_insertLp]

/-- `a • insertLp m s t = insertLp m (a * s) (a • t)`. -/
theorem smul_insertLp {n : ℕ} (a s : ℝ) (m : Fin (n + 1)) (t : EuclideanSpace ℝ (Fin n)) :
    a • EuclideanSpace.insertLp m s t = EuclideanSpace.insertLp m (a * s) (a • t) := by
  ext i
  exact m.succAboveCases (by simp) (fun _ ↦ by simp) i

/-- Eventually `0 < D₀`, `1 ≤ (φ(W)/W)·log R`, and `D₀ ≤ (φ(W)/W)·log R`. -/
theorem ym_phiW_logR_large (δ θ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2)) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → 0 < PrimeGaps.D₀ (N : ℝ) ∧
      1 ≤ ((PrimeGaps.sieveModulus N).totient : ℝ) / (PrimeGaps.sieveModulus N : ℝ) *
          Real.log (PrimeGaps.sieveTruncation N δ θ) ∧
      PrimeGaps.D₀ (N : ℝ) ≤ ((PrimeGaps.sieveModulus N).totient : ℝ) /
        (PrimeGaps.sieveModulus N : ℝ) *
          Real.log (PrimeGaps.sieveTruncation N δ θ) := by
  set κ : ℝ := θ / 2 - δ
  have hκpos : 0 < κ := sub_pos.mpr hδ.2
  have hcompN : ∀ᶠ N : ℕ in Filter.atTop,
      (Real.log (Real.log (N : ℝ))) ^ 3 ≤ κ * Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Real.eventually_log_pow_le_const_mul 3 hκpos)
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.mp hcompN
  obtain ⟨n₂, hn₂⟩ := Filter.eventually_atTop.mp PrimeGaps.lem_W_size
  refine ⟨max (max (n₁ : ℝ) (n₂ : ℝ)) (rexp (rexp (rexp 2))), fun N hN ↦ ?_⟩
  simp only [max_le_iff] at hN
  obtain ⟨⟨hNn₁, hNn₂⟩, hNe⟩ := hN
  have hNpos : (0 : ℝ) < (N : ℝ) := (Real.exp_pos _).trans_le hNe
  set LL : ℝ := Real.log (Real.log (N : ℝ))
  have hlogN_ge : Real.exp (Real.exp 2) ≤ Real.log (N : ℝ) := by
    simpa using Real.log_le_log (Real.exp_pos _) hNe
  have hLLge : Real.exp 2 ≤ LL := by
    simpa using Real.log_le_log (Real.exp_pos _) hlogN_ge
  have hLLpos : 0 < LL := (Real.exp_pos _).trans_le hLLge
  have hLL1 : (1 : ℝ) ≤ LL := (Real.one_le_exp (by norm_num)).trans hLLge
  have hD₀eq : PrimeGaps.D₀ (N : ℝ) = Real.log LL := rfl
  have hD₀ge2 : (2 : ℝ) ≤ PrimeGaps.D₀ (N : ℝ) := by
    rw [hD₀eq, ← Real.log_exp 2]
    exact Real.log_le_log (Real.exp_pos _) hLLge
  have hD₀pos : 0 < PrimeGaps.D₀ (N : ℝ) := zero_lt_two.trans_le hD₀ge2
  have hD₀leLL : PrimeGaps.D₀ (N : ℝ) ≤ LL := hD₀eq.trans_le (Real.log_le_self hLLpos.le)
  have hWle : (PrimeGaps.sieveModulus N : ℝ) ≤ LL ^ 2 := hn₂ N (by exact_mod_cast hNn₂)
  have hcube : LL ^ 3 ≤ κ * Real.log (N : ℝ) := hn₁ N (by exact_mod_cast hNn₁)
  have hlogR : Real.log (PrimeGaps.sieveTruncation N δ θ) = κ * Real.log (N : ℝ) :=
    Real.log_rpow hNpos κ
  have hWpos : (0 : ℝ) < (PrimeGaps.sieveModulus N : ℝ) := by exact_mod_cast PrimeGaps.W_pos
  have hφ1 : (1 : ℝ) ≤ ((PrimeGaps.sieveModulus N).totient : ℝ) := PrimeGaps.one_le_totient_W
  have hlogRnn : 0 ≤ Real.log (PrimeGaps.sieveTruncation N δ θ) := by
    rw [hlogR]
    positivity
  have hstep1 : Real.log (PrimeGaps.sieveTruncation N δ θ) / (PrimeGaps.sieveModulus N : ℝ) ≤
      ((PrimeGaps.sieveModulus N).totient : ℝ) / (PrimeGaps.sieveModulus N : ℝ) *
        Real.log (PrimeGaps.sieveTruncation N δ θ) := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (le_mul_of_one_le_left hlogRnn hφ1) hWpos.le
  have hstep2 : LL ≤ Real.log (PrimeGaps.sieveTruncation N δ θ) /
      (PrimeGaps.sieveModulus N : ℝ) := by
    rw [le_div_iff₀ hWpos, hlogR]
    calc LL * (PrimeGaps.sieveModulus N : ℝ) ≤ LL * LL ^ 2 :=
          mul_le_mul_of_nonneg_left hWle hLLpos.le
      _ = LL ^ 3 := by ring
      _ ≤ κ * Real.log (N : ℝ) := hcube
  have hLLx : LL ≤ ((PrimeGaps.sieveModulus N).totient : ℝ) / (PrimeGaps.sieveModulus N : ℝ) *
      Real.log (PrimeGaps.sieveTruncation N δ θ) := hstep2.trans hstep1
  exact ⟨hD₀pos, hLL1.trans hLLx, hD₀leLL.trans hLLx⟩

/-- For large `N`, `1 ≤ W N` and `W^{k+1}·D₀ ≪ (log N)^{2k+3}`. -/
theorem rsq_Wasymp {k : ℕ} : ∃ K_W : ℝ, 0 < K_W ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      (1 : ℝ) ≤ (PrimeGaps.sieveModulus N : ℝ) ∧
      ((PrimeGaps.sieveModulus N : ℝ)) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ) ≤
        K_W * (Real.log N) ^ (2 * k + 3) := by
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 PrimeGaps.lem_W_size
  refine ⟨1, one_pos, max (n₀ : ℝ) (rexp (rexp (rexp 4))), fun N hN ↦ ?_⟩
  have hNexp : rexp (rexp (rexp 4)) ≤ (N : ℝ) := (le_max_right _ _).trans hN
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos _).trans_le hNexp
  set L : ℝ := Real.log (N : ℝ)
  have hLlb : rexp (rexp 4) ≤ L := (Real.le_log_iff_exp_le hNpos).2 hNexp
  have hLpos : 0 < L := (Real.exp_pos _).trans_le hLlb
  set u : ℝ := Real.log L
  have hulb : rexp 4 ≤ u := (Real.le_log_iff_exp_le hLpos).2 hLlb
  have hupos : 0 < u := (Real.exp_pos _).trans_le hulb
  have hD0pos : 0 < PrimeGaps.D₀ (N : ℝ) :=
    zero_lt_four.trans_le ((Real.le_log_iff_exp_le hupos).2 hulb)
  have hW1 : (1 : ℝ) ≤ (PrimeGaps.sieveModulus N : ℝ) := Nat.one_le_cast.mpr PrimeGaps.W_pos
  refine ⟨hW1, ?_⟩
  have hWu : (PrimeGaps.sieveModulus N : ℝ) ≤ u ^ 2 :=
    hn₀ N (Nat.cast_le.mp ((le_max_left _ _).trans hN))
  rw [one_mul]
  calc (PrimeGaps.sieveModulus N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ)
      ≤ (u ^ 2) ^ (k + 1) * u :=
        mul_le_mul (pow_le_pow_left₀ (zero_le_one.trans hW1) hWu _)
          (Real.log_le_self hupos.le) hD0pos.le (pow_nonneg (sq_nonneg u) _)
    _ = u ^ (2 * k + 3) := by ring
    _ ≤ L ^ (2 * k + 3) := pow_le_pow_left₀ hupos.le (Real.log_le_self hLpos.le) _

/-- Exact normalization of each inverse-form approximation error. -/
theorem cross_inverse_error_eq {k : ℕ} (C q c Fm φW Wr Nr L logR logRp D0 : ℝ)
    (hφW : φW ≠ 0) (hWr : Wr ≠ 0) (hL : L ≠ 0) (hD0 : D0 ≠ 0)
    (hlogRp : logRp = q * logR) (hlogR : logR = c * L) :
    Nr / (φW * L) * (C * Fm ^ 2 * φW ^ (k + 1) * logRp ^ (k + 1) /
          (Wr ^ (k + 1) * D0)) = C * q ^ (k + 1) * c *
          (Fm ^ 2 * φW ^ k * Nr * logR ^ k /
            (Wr ^ (k + 1) * D0)) := by
  rw [hlogRp, mul_pow, pow_succ φW, pow_succ logR, hlogR]
  field_simp

/-- A normalization identity for the principal `S₂m → ym` error. -/
theorem cross_fromYm_principal_eq {k : ℕ} (hk : 2 ≤ k) (C Cy q c Fm φW Wr Nr L logR logRp D0 : ℝ)
    (cne : c ≠ 0) (Wrne : Wr ≠ 0) (D0ne : D0 ≠ 0)
    (hlogRp : logRp = q * logR) (hlogR : logR = c * L) :
    C * (Cy * Fm * φW * logRp / Wr) ^ 2 * φW ^ (k - 2) * Nr * L ^ (k - 2) / (Wr ^ (k - 1) * D0) =
      (C * Cy ^ 2 * q ^ 2 / c ^ (k - 2)) * (Fm ^ 2 * φW ^ k * Nr * logR ^ k /
            (Wr ^ (k + 1) * D0)) := by
  have hkW : Wr ^ (k + 1) = Wr ^ (k - 1) * Wr ^ 2 :=
    (pow_sub_mul_pow Wr (Nat.le_succ_of_le hk)).symm
  rw [hlogRp, hlogR, ← pow_sub_mul_pow φW hk, hkW, mul_pow c L k,
    ← pow_sub_mul_pow L hk, ← pow_sub_mul_pow c hk]
  field_simp

/-- An abstract bound absorbing the finite-support tail into `S`. -/
theorem cross_fromYm_tail_absorb {k : ℕ} (hk : 2 ≤ k) (C Y Fm φW Wr Nr L logR D0 c K_W S : ℝ)
    (hC : 0 < C) (hY0 : 0 ≤ Y) (hY : Y ≤ Fm)
    (hφW : 1 ≤ φW) (hWr : 1 ≤ Wr)
    (hL : 1 ≤ L) (hD0 : 0 < D0) (hc : 0 < c)
    (hKW : 0 < K_W) (hNr : 0 ≤ Nr)
    (hlogR : logR = c * L)
    (hWa : Wr ^ (k + 1) * D0 ≤ K_W * L ^ (2 * k + 3))
    (hSform : S = Fm ^ 2 * φW ^ k * Nr * logR ^ k / (Wr ^ (k + 1) * D0)) :
    C * Y ^ 2 * Nr / L ^ (9 * (k : ℝ) + 3) ≤ (C * K_W / c ^ k) * S := by
  refine (rsq_absorbA C Fm φW Wr Nr L logR D0 c K_W S
    hC hφW hWr hL hD0 hc hKW hNr hlogR hWa hSform).trans' ?_
  gcongr
  exact le_mul_of_one_le_left (zero_le_two.trans (by exact_mod_cast hk : (2 : ℝ) ≤ k))
    (by norm_num : (1 : ℝ) ≤ 9)

/-- Combined normalization of a principal error and a finite-support tail. -/
theorem cross_fromYm_error_absorb {k : ℕ} (hk : 2 ≤ k)
    (C Cy U Y q c Fm φW Wr Nr L logR logRp D0 K_W S : ℝ)
    (hC : 0 < C) (hCy : 0 ≤ Cy)
    (hU0 : 0 ≤ U) (hU : U ≤ Cy * Fm * φW * logRp / Wr)
    (hY0 : 0 ≤ Y) (hY : Y ≤ Fm)
    (hFm : 0 ≤ Fm)
    (hφW : 1 ≤ φW) (hWr : 1 ≤ Wr)
    (hL : 1 ≤ L) (hlogRp0 : 0 ≤ logRp)
    (hD0 : 0 < D0) (hc : 0 < c)
    (hKW : 0 < K_W) (hNr : 0 ≤ Nr)
    (hlogRp : logRp = q * logR) (hlogR : logR = c * L)
    (hWa : Wr ^ (k + 1) * D0 ≤ K_W * L ^ (2 * k + 3))
    (hSform : S = Fm ^ 2 * φW ^ k * Nr * logR ^ k / (Wr ^ (k + 1) * D0)) :
    C * U ^ 2 * φW ^ (k - 2) * Nr * L ^ (k - 2) /
          (Wr ^ (k - 1) * D0) + C * Y ^ 2 * Nr / L ^ (9 * (k : ℝ) + 3) ≤
      (C * Cy ^ 2 * q ^ 2 / c ^ (k - 2) + C * K_W / c ^ k) * S := by
  have hWrpos : 0 < Wr := zero_lt_one.trans_le hWr
  rw [add_mul]
  refine add_le_add ?_ (cross_fromYm_tail_absorb hk C Y Fm φW Wr Nr L logR D0 c K_W S
    hC hY0 hY hφW hWr hL hD0 hc hKW hNr hlogR hWa hSform)
  rw [hSform, ← cross_fromYm_principal_eq hk C Cy q c Fm φW Wr Nr L logR logRp D0
    hc.ne' hWrpos.ne' hD0.ne' hlogRp hlogR]
  gcongr C * ?_ * φW ^ (k - 2) * Nr * L ^ (k - 2) / (Wr ^ (k - 1) * D0)
  exact sq_le_sq' ((neg_nonpos.2 (by positivity)).trans hU0) hU

/-- The one-weight transformed-sum error: the `D₀`-saving diagonal term plus the
`N / log N ^ A` Bombieri–Vinogradov term. -/
noncomputable def fromYmError {k : ℕ} (m : Fin k) (A C : ℝ) (N W : ℕ) (L : (Fin k → ℕ) →₀ ℝ) : ℝ :=
  C * (⨆ r, |PrimeGaps.ym m L r|) ^ 2 * (W.totient : ℝ) ^ (k - 2) * (N : ℝ) * Real.log N ^ (k - 2) /
      ((W : ℝ) ^ (k - 1) * PrimeGaps.D₀ (N : ℝ)) +
    C * (Finsupp.maxRealAbs (PrimeGaps.lToY L)) ^ 2 * (N : ℝ) / Real.log N ^ A

/-- `0 ≤ fromYmError m A C N W L` for `0 ≤ C`, `0 < log N` and `0 < D₀ N`. -/
theorem fromYmError_nonneg {k N W : ℕ} (m : Fin k) (A C : ℝ) (L : (Fin k → ℕ) →₀ ℝ) (hC : 0 ≤ C)
    (hlog : 0 < Real.log N) (hD0 : 0 < PrimeGaps.D₀ (N : ℝ)) :
    0 ≤ fromYmError m A C N W L := by
  unfold fromYmError
  positivity

/-- The `D₀`-saving diagonal term of `fromYmError`, without the Bombieri–Vinogradov summand. -/
noncomputable def weightedDiagonalErrorEarly {k : ℕ} (m : Fin k)
    (C : ℝ) (N W : ℕ) (L : (Fin k → ℕ) →₀ ℝ) : ℝ :=
  C * (⨆ r, |PrimeGaps.ym m L r|) ^ 2 * (W.totient : ℝ) ^ (k - 2) * (N : ℝ) * Real.log N ^ (k - 2) /
      ((W : ℝ) ^ (k - 1) * PrimeGaps.D₀ (N : ℝ))

/-- The three-weight error package for the orthogonal polarization argument. -/
noncomputable def correctedCrossNativeError {k : ℕ} (m : Fin k)
    (A C C₀ C₁ C₂ : ℝ) (N W : ℕ) (R M D : ℝ)
    (L₀ L₁ L₂ : (Fin k → ℕ) →₀ ℝ) : ℝ :=
  fromYmError m A C N W L₀ + fromYmError m A C N W L₁ + fromYmError m A C N W L₂ +
    (N : ℝ) / ((W.totient : ℝ) * Real.log N) *
      (PrimeGaps.inverseDiagonalApproxErrorScale k C₀ R W M D +
        PrimeGaps.inverseDiagonalApproxErrorScale k C₁ R W M D +
        PrimeGaps.inverseDiagonalApproxErrorScale k C₂ R W M D)

/-- A mixed comparison error with an explicit smooth norm and three divisor weights. -/
noncomputable def weakCrossNativeError {k : ℕ} (m : Fin k)
    (A Cb Cd C₀ C₁ C₂ : ℝ) (N W : ℕ) (R M D : ℝ)
    (L₀ L₁ L₂ : (Fin k → ℕ) →₀ ℝ) : ℝ :=
  2 * (Cb * M ^ 2 * (N : ℝ) / Real.log N ^ A) +
    weightedDiagonalErrorEarly m Cd N W L₀ + weightedDiagonalErrorEarly m Cd N W L₁ +
    weightedDiagonalErrorEarly m Cd N W L₂ + (N : ℝ) / ((W.totient : ℝ) * Real.log N) *
      (PrimeGaps.inverseDiagonalApproxErrorScale k C₀ R W M D +
        PrimeGaps.inverseDiagonalApproxErrorScale k C₁ R W M D +
        PrimeGaps.inverseDiagonalApproxErrorScale k C₂ R W M D)

/-- A one-weight transformed-sum error with an explicit smooth norm. -/
noncomputable def weakFromYmError {k : ℕ} (m : Fin k) (A C : ℝ)
    (N W : ℕ) (M : ℝ) (L : (Fin k → ℕ) →₀ ℝ) : ℝ :=
  PrimeGaps.fromYmErrorScale (k := k) A C N W (⨆ r, |PrimeGaps.ym m L r|) M

/-- The prime-weighted sum is approximated by `N / (φ W * log N) * ymDiagonalForm m W L`, up to
`weightedDiagonalErrorEarly`, for all large `N`. -/
theorem ymWeightedSum_to_ymDiagonal_early {k : ℕ} (m : Fin k) (hk : 2 ≤ k)
    (Θ Δ : ℝ) (hΘ : Θ ∈ Set.Ioo (0 : ℝ) 1)
    (hΔ : Δ ∈ Set.Ioo (0 : ℝ) (Θ / 2)) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ L : (Fin k → ℕ) →₀ ℝ,
        L.HasPermissibleSupport ⌊PrimeGaps.sieveTruncation N Δ Θ⌋₊ (PrimeGaps.sieveModulus N) →
      |(Nat.primeCountingIoc N (2 * N) : ℝ) /
            (PrimeGaps.sieveModulus N).totient * ymWeightedSum m L - (N : ℝ) /
            (((PrimeGaps.sieveModulus N).totient : ℝ) * Real.log N) *
              ymDiagonalForm m (PrimeGaps.sieveModulus N) L| ≤
        weightedDiagonalErrorEarly m C N (PrimeGaps.sieveModulus N) L := by
  obtain ⟨Cd, hCd, Nd, hd⟩ := ymWeightedSum_to_diagonal m hk Θ Δ hΘ hΔ
  obtain ⟨Cp, hCp, Np, hp⟩ := lem_S2m_PNT m Θ Δ hk hΘ hΔ
  refine ⟨Cd + Cp + 1, by linarith, max Nd Np, ?_⟩
  intro N hN L hL
  let pref : ℝ := (Nat.primeCountingIoc N (2 * N) : ℝ) / (PrimeGaps.sieveModulus N).totient
  let mainPref : ℝ := (N : ℝ) / (((PrimeGaps.sieveModulus N).totient : ℝ) * Real.log N)
  let Sig : ℝ := ∑' u : Fin k → ℕ, if (∀ i, 1 ≤ u i) ∧ PrimeGaps.LemS1RestrictSij.RestrictedCoprime
            u (fun _ _ ↦ 1)
      then PrimeGaps.ym m L u ^ 2 / ∏ i, (g (u i) : ℝ)
      else 0
  let E : ℝ := (⨆ r, |PrimeGaps.ym m L r|) ^ 2 *
      ((PrimeGaps.sieveModulus N).totient : ℝ) ^ (k - 2) *
      (N : ℝ) * Real.log N ^ (k - 2) / ((PrimeGaps.sieveModulus N : ℝ) ^ (k - 1) *
          PrimeGaps.D₀ (N : ℝ))
  have hdN : |pref * ymWeightedSum m L - pref * Sig| ≤ Cd * E := by
    simpa [pref, Sig, E, mul_assoc, mul_div_assoc] using hd N ((le_max_left _ _).trans hN) L hL
  have hpN : |pref * Sig - mainPref * Sig| ≤ Cp * E := by
    simpa [pref, mainPref, Sig, E, mul_assoc, mul_div_assoc] using
      hp N ((le_max_right _ _).trans hN) L hL
  have hE : 0 ≤ E := nonneg_of_mul_nonneg_right ((abs_nonneg _).trans hpN) hCp
  rw [← fromYm_diagonal_eq_ymDiagonalForm m (PrimeGaps.sieveTruncation N Δ Θ)
    (PrimeGaps.sieveModulus N) L hL]
  calc |pref * ymWeightedSum m L - mainPref * Sig|
      ≤ |pref * ymWeightedSum m L - pref * Sig| +
          |pref * Sig - mainPref * Sig| := abs_sub_le _ _ _
    _ ≤ Cd * E + Cp * E := add_le_add hdN hpN
    _ ≤ (Cd + Cp + 1) * E := by linarith
    _ = weightedDiagonalErrorEarly m (Cd + Cp + 1) N (PrimeGaps.sieveModulus N) L := by
      dsimp [weightedDiagonalErrorEarly, E]
      ring

end PrimeGaps
