/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.PermissibleSupport.FunctionW
public import PrimeGapsTheory.Sieve.SieveTruncation
public import PrimeGapsTheory.Arithmetic.Mertens.TauK
public import PrimeGapsTheory.Arithmetic.Totient.Basic

/-!
# Restricted reciprocal sums

Bounds totient-weighted reciprocal sums over squarefree integers subject to divisibility,
coprimality, and product-cutoff conditions.

## Main definitions

* `innerReciprocalSum`: The totient-weighted reciprocal sum over tuples with prescribed
  divisors, squarefree product below a cutoff, and product coprime to `W`.
* `restrictedTauSum`: The coprime-restricted squarefree `τ_k/φ` sum over an initial segment.

## Main results

* `innerReciprocalSum_core`: A uniform logarithmic bound for the inner reciprocal sum.
* `euler_prod_le`: A logarithmic bound for the associated truncated Euler product.
-/

@[expose] public section

open scoped Finset

open scoped BigOperators ArithmeticFunction.Moebius
open Filter ArithmeticFunction zeta

open scoped ArithmeticFunction.zeta

namespace RestrictedReciprocalSum

/-- `∑_r (∏ᵢ φ(rᵢ))⁻¹` over the tuples `r` with `dᵢ ∣ rᵢ` for all `i` and `∏ᵢ rᵢ` at most `R`,
squarefree, and coprime to `W`. -/
noncomputable def innerReciprocalSum {k : ℕ} (R : ℝ) (W : ℕ) (d : Fin k → ℕ) : ℝ :=
  ∑' r : Fin k → ℕ, (if (∀ i, d i ∣ r i) ∧
        ((∏ i, r i : ℝ) ≤ R ∧ Squarefree (∏ i, r i) ∧ Nat.Coprime (∏ i, r i) W)
      then (∏ i, (Nat.totient (r i) : ℝ))⁻¹ else 0)

/-- The coprime-restricted squarefree `τ_k/φ` sum over `[1, N]`:
`∑_{1 ≤ m ≤ N, m squarefree, gcd(m,D)=1} τ_k(m)/φ(m)`. -/
noncomputable def restrictedTauSum (k N D : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N,
    (if Squarefree m ∧ Nat.Coprime m D then (τ k m : ℝ) / (m.totient : ℝ) else 0)

private lemma restrictedTauSum_nonneg (k N D : ℕ) : 0 ≤ restrictedTauSum k N D := by
  refine Finset.sum_nonneg fun m _ ↦ ?_
  split
  · positivity
  · exact le_rfl

/-- A family of tuples `r` with `dᵢ ∣ rᵢ` and `∏ᵢ rᵢ = D * m`, where `D = ∏ᵢ dᵢ`, has at most
`τ k m` members. -/
theorem fiber_card_le {k : ℕ} (d : Fin k → ℕ) (D m : ℕ) (hD : D = ∏ i, d i) (hDne : D ≠ 0)
    (hm : m ≠ 0) (Sfin : Finset (Fin k → ℕ))
    (hS : ∀ r ∈ Sfin, (∀ i, d i ∣ r i) ∧ ∏ i, r i = D * m) :
    #Sfin ≤ τ k m := by
  rw [ArithmeticFunction.tau_apply_eq_card_finMulAntidiag]
  apply Finset.card_le_card_of_injOn fun r i ↦ r i / d i
  · intro r hr
    obtain ⟨hdvd, hprod⟩ := hS r hr
    have hh : ∏ i, r i = D * ∏ i, (r i / d i) := by
      rw [hD, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ ↦ (Nat.mul_div_cancel' (hdvd i)).symm
    rw [hprod] at hh
    simp only [Finset.mem_coe, Nat.mem_finMulAntidiag]
    exact ⟨Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hDne) hh.symm, hm⟩
  · intro r hr r' hr' heq
    obtain ⟨hdvd, _⟩ := hS r hr
    obtain ⟨hdvd', _⟩ := hS r' hr'
    funext i
    have hi : r i / d i = r' i / d i := congrFun heq i
    rw [← Nat.mul_div_cancel' (hdvd i), ← Nat.mul_div_cancel' (hdvd' i), hi]

/-- `∏ᵢ φ(rᵢ) = φ(∏ᵢ rᵢ)` when `∏ᵢ rᵢ` is squarefree, since the `rᵢ` are then pairwise coprime. -/
theorem prod_totient_eq {k : ℕ} (r : Fin k → ℕ) (hsqf : Squarefree (∏ i, r i)) :
    ∏ i, (r i).totient = (∏ i, r i).totient := by
  have hpair : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).Pairwise
      (Function.onFun Nat.Coprime r) := by
    intro i _ j _ hij
    have hdvd : r i * r j ∣ ∏ i, r i := by
      have hh := Finset.prod_dvd_prod_of_subset ({i, j} : Finset (Fin k)) Finset.univ r
        (Finset.subset_univ _)
      rwa [Finset.prod_pair hij] at hh
    exact (Nat.squarefree_mul_iff.mp (hsqf.squarefree_of_dvd hdvd)).1
  have hh := ArithmeticFunction.isMultiplicative_totient.map_prod r Finset.univ hpair
  simp only [ArithmeticFunction.totient_apply] at hh
  exact hh.symm

/-- `innerReciprocalSum R W d ≤ restrictedTauSum k ⌊R⌋₊ D / φ(D)`, where `D = ∏ᵢ dᵢ`. -/
theorem inner_le_restricted_div (k : ℕ) (R : ℝ) (W : ℕ) (d : Fin k → ℕ) :
    innerReciprocalSum R W d ≤
      restrictedTauSum k ⌊R⌋₊ (∏ i, d i) / ((∏ i, d i).totient : ℝ) := by
  set N := ⌊R⌋₊ with hN
  set D := ∏ i, d i with hD
  set g : (Fin k → ℕ) → ℝ := fun r ↦ (if (∀ i, d i ∣ r i) ∧
        ((∏ i, r i : ℝ) ≤ R ∧ Squarefree (∏ i, r i) ∧ Nat.Coprime (∏ i, r i) W)
      then (∏ i, (Nat.totient (r i) : ℝ))⁻¹ else 0) with hg
  set B : Finset (Fin k → ℕ) := Fintype.piFinset (fun _ ↦ Finset.Icc 1 N) with hB
  have hsupp : ∀ r, g r ≠ 0 → r ∈ B := by
    intro r hr0
    have hcond : (∀ i, d i ∣ r i) ∧
        ((∏ i, r i : ℝ) ≤ R ∧ Squarefree (∏ i, r i) ∧ Nat.Coprime (∏ i, r i) W) := by
      by_contra hc; exact hr0 (by rw [hg]; simp [hc])
    obtain ⟨_, hlt, hsqf, _⟩ := hcond
    have hri_pos : ∀ i, 1 ≤ r i := fun i ↦ Nat.one_le_iff_ne_zero.mpr fun h ↦
      hsqf.ne_zero (Finset.prod_eq_zero (Finset.mem_univ i) h)
    have hle : ∀ i, r i ≤ ∏ i, r i := fun i ↦
      Finset.single_le_prod' (fun j _ ↦ hri_pos j) (Finset.mem_univ i)
    rw [hB, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    exact ⟨hri_pos i, Nat.le_floor (le_trans (by exact_mod_cast hle i) hlt)⟩
  have htsum : innerReciprocalSum R W d = ∑ r ∈ B, g r := by
    rw [innerReciprocalSum, tsum_eq_sum (s := B)]
    exact fun b hb ↦ not_not.mp fun hne ↦ hb (hsupp b hne)
  rw [htsum]
  classical
  set S : Finset (Fin k → ℕ) := {r ∈ B | g r ≠ 0} with hSdef
  have hBS : ∑ r ∈ B, g r = ∑ r ∈ S, g r := (Finset.sum_filter_ne_zero B).symm
  rw [hBS]
  set φD : ℝ := (D.totient : ℝ) with hφD
  have hScontrib : ∀ r ∈ S, (∀ i, d i ∣ r i) ∧ (∏ i, r i : ℝ) ≤ R ∧
      Squarefree (∏ i, r i) ∧ Nat.Coprime (∏ i, r i) W := by
    intro r hr
    rw [hSdef, Finset.mem_filter] at hr
    by_contra hc
    exact hr.2 (by rw [hg]; simp [hc])
  have hDdvd : ∀ r ∈ S, D ∣ ∏ i, r i := by
    intro r hr
    rw [hD]
    exact Finset.prod_dvd_prod_of_dvd _ _ fun i _ ↦ (hScontrib r hr).1 i
  rcases Nat.eq_zero_or_pos D with hD0 | hDpos
  · have hSempty : S = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      exact fun r hr ↦ (hScontrib r hr).2.2.1.ne_zero
        (Nat.eq_zero_of_zero_dvd (hD0 ▸ hDdvd r hr))
    rw [hSempty, Finset.sum_empty]
    exact div_nonneg (restrictedTauSum_nonneg k N D) (by rw [hφD]; positivity)
  · have hDne : D ≠ 0 := by omega
    set ν : (Fin k → ℕ) → ℕ := fun r ↦ (∏ i, r i) / D with hν
    have hrfacts : ∀ r ∈ S, ∏ i, r i = D * ν r ∧ ν r ≠ 0 ∧ Squarefree (ν r) ∧
        Nat.Coprime (ν r) D ∧ ν r ∈ Finset.Icc 1 N ∧
        g r = (φD * ((ν r).totient : ℝ))⁻¹ := by
      intro r hr
      obtain ⟨hdvd, hlt, hsqf, hcop⟩ := hScontrib r hr
      have hune : ∏ i, r i ≠ 0 := hsqf.ne_zero
      have hprodeq : ∏ i, r i = D * ν r := by
        rw [hν]; exact (Nat.mul_div_cancel' (hDdvd r hr)).symm
      have hνne : ν r ≠ 0 := fun h0 ↦ hune (by rw [hprodeq, h0, mul_zero])
      have hsplit : Nat.Coprime D (ν r) ∧ Squarefree D ∧ Squarefree (ν r) :=
        Nat.squarefree_mul_iff.mp (hprodeq ▸ hsqf)
      have hνmem : ν r ∈ Finset.Icc 1 N := by
        rw [Finset.mem_Icc]
        refine ⟨Nat.one_le_iff_ne_zero.mpr hνne, le_trans (Nat.le_of_dvd
          (Nat.pos_of_ne_zero hune) ⟨D, by rw [hprodeq]; ring⟩) ?_⟩
        rw [hN]
        exact Nat.le_floor (by simpa [Nat.cast_prod] using hlt)
      have hgr : g r = (φD * ((ν r).totient : ℝ))⁻¹ := by
        rw [hg]; dsimp only
        rw [if_pos ⟨hdvd, hlt, hsqf, hcop⟩, ← Nat.cast_prod, prod_totient_eq r hsqf, hprodeq,
          Nat.totient_mul hsplit.1, hφD]
        push_cast; ring_nf
      exact ⟨hprodeq, hνne, hsplit.2.2, hsplit.1.symm, hνmem, hgr⟩
    have hφDpos : (0 : ℝ) < φD := by
      rw [hφD]; exact_mod_cast Nat.totient_pos.mpr hDpos
    have hmaps : ∀ r ∈ S, ν r ∈ Finset.Icc 1 N := fun r hr ↦ (hrfacts r hr).2.2.2.2.1
    rw [← Finset.sum_fiberwise_of_maps_to hmaps g, restrictedTauSum, Finset.sum_div]
    refine Finset.sum_le_sum fun m hm ↦ ?_
    set Fm : Finset (Fin k → ℕ) := {r ∈ S | ν r = m} with hFm
    rcases Finset.eq_empty_or_nonempty Fm with hFe | ⟨r₀, hr₀⟩
    · rw [hFe, Finset.sum_empty]
      refine div_nonneg ?_ hφDpos.le
      split
      · positivity
      · exact le_rfl
    · rw [hFm, Finset.mem_filter] at hr₀
      have hfacts₀ := hrfacts r₀ hr₀.1
      have hmne : m ≠ 0 := by rw [Finset.mem_Icc] at hm; omega
      rw [if_pos ⟨hr₀.2 ▸ hfacts₀.2.2.1, hr₀.2 ▸ hfacts₀.2.2.2.1⟩]
      have hfibval : ∀ r ∈ Fm, g r = (φD * (m.totient : ℝ))⁻¹ := by
        intro r hr
        rw [hFm, Finset.mem_filter] at hr
        rw [(hrfacts r hr.1).2.2.2.2.2, hr.2]
      rw [Finset.sum_congr rfl hfibval, Finset.sum_const, nsmul_eq_mul]
      have hcardle : (#Fm : ℝ) ≤ (τ k m : ℝ) := by
        have hnat : #Fm ≤ τ k m := by
          refine fiber_card_le d D m hD hDne hmne Fm fun r hr ↦ ?_
          rw [hFm, Finset.mem_filter] at hr
          exact ⟨(hScontrib r hr.1).1, by rw [(hrfacts r hr.1).1, hr.2]⟩
        exact_mod_cast hnat
      calc (#Fm : ℝ) * (φD * (m.totient : ℝ))⁻¹ ≤ (τ k m : ℝ) * (φD * (m.totient : ℝ))⁻¹ :=
            mul_le_mul_of_nonneg_right hcardle (by positivity)
        _ = (τ k m : ℝ) / (m.totient : ℝ) / φD := by rw [mul_inv]; ring

/-- `D * innerReciprocalSum R W d ≤ (D / φ(D)) * restrictedTauSum k ⌊R⌋₊ D`, where `D = ∏ᵢ dᵢ`. -/
theorem inner_le_Dphi_restricted (k : ℕ) (R : ℝ) (W : ℕ) (d : Fin k → ℕ) :
    (∏ i, (d i : ℝ)) * innerReciprocalSum R W d ≤ ((∏ i, (d i : ℝ)) / ((∏ i, d i).totient : ℝ)) *
        restrictedTauSum k ⌊R⌋₊ (∏ i, d i) := by
  rw [← Nat.cast_prod, div_mul_eq_mul_div, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (inner_le_restricted_div k R W d) (by positivity)

/-- `τ k m / φ(m) = ∏ p ∈ m.primeFactors, k / (p - 1)` for squarefree `m`. -/
theorem tau_div_totient_squarefree (k : ℕ) (m : ℕ) (hm : Squarefree m) :
    ((τ k m : ℕ) : ℝ) / (m.totient : ℝ) =
      ∏ p ∈ m.primeFactors, (k : ℝ) / ((p : ℝ) - 1) := by
  have htau : ((ζ ^ k)) m = ∏ p ∈ m.primeFactors, k := by
    rw [← ArithmeticFunction.isMultiplicative_tau.prod_primeFactors hm]
    exact Finset.prod_congr rfl fun p hp ↦
      ArithmeticFunction.tau_prime (Nat.prime_of_mem_primeFactors hp)
  rw [htau, PrimeGaps.totient_eq_prod_sub_one m (Nat.pos_of_ne_zero hm.ne_zero) hm]
  push_cast
  rw [← Finset.prod_div_distrib]

/-- `restrictedTauSum k N D ≤ ∏_{p < N + 1 prime, p ∤ D} (1 + k/(p-1))`, by expanding the product
over subsets of primes. -/
theorem restricted_tau_sum_le_prod (k N D : ℕ) : restrictedTauSum k N D ≤
      ∏ p ∈ (N + 1).primesBelow with ¬ (p ∣ D), (1 + (k : ℝ) / ((p : ℝ) - 1)) := by
  set P := {p ∈ (N + 1).primesBelow | ¬ p ∣ D} with hP
  set f : ℕ → ℝ := fun p ↦ (k : ℝ) / ((p : ℝ) - 1) with hf
  have hPge2 : ∀ p ∈ P, 2 ≤ p := by
    intro p hp
    rw [hP, Finset.mem_filter, Nat.mem_primesBelow] at hp
    exact hp.1.2.two_le
  have hfnn : ∀ p ∈ P, 0 ≤ f p := fun p hp ↦ div_nonneg (by positivity) (by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hPge2 p hp
    linarith)
  have hprodSnn : ∀ S ∈ P.powerset, 0 ≤ ∏ p ∈ S, f p := fun S hS ↦
    Finset.prod_nonneg fun p hp ↦ hfnn p (Finset.mem_powerset.mp hS hp)
  set A := {m ∈ Finset.Icc 1 N | Squarefree m ∧ Nat.Coprime m D} with hA
  have hLHS : restrictedTauSum k N D = ∑ m ∈ A, (τ k m : ℝ) / (m.totient : ℝ) := by
    rw [restrictedTauSum, hA, Finset.sum_filter]
  have hterm : ∀ m ∈ A, (τ k m : ℝ) / (m.totient : ℝ) = ∏ p ∈ m.primeFactors, f p := by
    intro m hm
    rw [hA, Finset.mem_filter] at hm
    exact tau_div_totient_squarefree k m hm.2.1
  have hΦinj : ∀ a ∈ A, ∀ b ∈ A, Nat.primeFactors a = Nat.primeFactors b → a = b := by
    intro a ha b hb hab
    rw [hA, Finset.mem_filter] at ha hb
    have := congrArg (fun s : Finset ℕ ↦ ∏ p ∈ s, p) hab
    rwa [Nat.prod_primeFactors_of_squarefree ha.2.1,
      Nat.prod_primeFactors_of_squarefree hb.2.1] at this
  have hΦmem : ∀ m ∈ A, m.primeFactors ∈ P.powerset := by
    intro m hm
    rw [hA, Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm1, hmN⟩, _, hcop⟩ := hm
    rw [Finset.mem_powerset]
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    obtain ⟨hpp, hpm, _⟩ := hp
    rw [hP, Finset.mem_filter, Nat.mem_primesBelow]
    refine ⟨⟨?_, hpp⟩, fun hpD ↦ hpp.one_lt.ne'
      (Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd hpm hpD))⟩
    have hple : p ≤ m := Nat.le_of_dvd (by omega) hpm
    omega
  calc restrictedTauSum k N D = ∑ m ∈ A, ∏ p ∈ m.primeFactors, f p := by
          rw [hLHS]; exact Finset.sum_congr rfl hterm
    _ = ∑ S ∈ A.image (fun m ↦ m.primeFactors), ∏ p ∈ S, f p := by
          rw [Finset.sum_image hΦinj]
    _ ≤ ∑ S ∈ P.powerset, ∏ p ∈ S, f p := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun S hS _ ↦ hprodSnn S hS
          intro S hS
          rw [Finset.mem_image] at hS
          obtain ⟨m, hmA, rfl⟩ := hS
          exact hΦmem m hmA
    _ = ∏ p ∈ P, (1 + f p) := (Finset.prod_one_add P).symm

/-- `D / φ(D) ≤ ∏_{p < N + 1 prime, p ∣ D} (1 + k/(p-1))`, when every prime factor of `D` is at
most `N`. -/
theorem Dphi_le_prod_dvd (k N D : ℕ) (hk : 1 ≤ k) (hD : 1 ≤ D)
    (hDprimes : ∀ p ∈ D.primeFactors, p ≤ N) :
    (D : ℝ) / (D.totient : ℝ) ≤
      ∏ p ∈ (N + 1).primesBelow with (p ∣ D), (1 + (k : ℝ) / ((p : ℝ) - 1)) := by
  have hD0 : D ≠ 0 := by omega
  have hfilter : {p ∈ (N + 1).primesBelow | p ∣ D} = D.primeFactors := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesBelow, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨_, hp⟩, hpd⟩
      exact ⟨hp, hpd, hD0⟩
    · rintro ⟨hp, hpd, _⟩
      exact ⟨⟨by have := hDprimes p (Nat.mem_primeFactors.mpr ⟨hp, hpd, hD0⟩); omega, hp⟩, hpd⟩
  rw [hfilter]
  have hp2 : ∀ p ∈ D.primeFactors, 2 ≤ p := fun p hp ↦ (Nat.prime_of_mem_primeFactors hp).two_le
  have htot : (D.totient : ℝ) = (D : ℝ) * ∏ p ∈ D.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have := congrArg (fun x : ℚ ↦ (x : ℝ)) (Nat.totient_eq_mul_prod_factors D)
    push_cast at this
    convert this using 2
  have hfac_pos : ∀ p ∈ D.primeFactors, (0 : ℝ) < 1 - (p : ℝ)⁻¹ := by
    intro p hp
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2 p hp
    have hpinv : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_iff_one_le_mul₀ (by linarith)]
      linarith
    linarith
  have hprodpos : (0 : ℝ) < ∏ p ∈ D.primeFactors, (1 - (p : ℝ)⁻¹) := Finset.prod_pos hfac_pos
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  rw [show (D : ℝ) / (D.totient : ℝ) = ∏ p ∈ D.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ by
    rw [htot, Finset.prod_inv_distrib, eq_comm, inv_eq_one_div,
      div_eq_div_iff (by positivity) (by positivity)]
    ring]
  refine Finset.prod_le_prod (fun p hp ↦ (inv_pos.mpr (hfac_pos p hp)).le) fun p hp ↦ ?_
  have hp2' : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2 p hp
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  rw [show (1 - (p : ℝ)⁻¹)⁻¹ = 1 + 1 / ((p : ℝ) - 1) by field_simp; ring]
  gcongr

/-- `innerReciprocalSum R W d = 0` as soon as `∏ᵢ dᵢ` has a prime factor exceeding `⌊R⌋₊`. -/
theorem inner_eq_zero_of_prime_gt (k : ℕ) (R : ℝ) (W : ℕ) (d : Fin k → ℕ)
    (hbad : ¬ ∀ p ∈ (∏ i, d i).primeFactors, p ≤ ⌊R⌋₊) :
    innerReciprocalSum R W d = 0 := by
  unfold innerReciprocalSum
  have hzero : ∀ r : Fin k → ℕ, (if (∀ i, d i ∣ r i) ∧
          ((∏ i, r i : ℝ) ≤ R ∧ Squarefree (∏ i, r i) ∧ Nat.Coprime (∏ i, r i) W)
        then (∏ i, (Nat.totient (r i) : ℝ))⁻¹ else 0) = 0 := by
    intro r
    rw [if_neg]
    rintro ⟨hdvd, hlt, hsqf, _⟩
    refine hbad fun p hp ↦ ?_
    have hple : p ≤ ∏ i, r i := Nat.le_of_dvd (Nat.pos_of_ne_zero hsqf.ne_zero)
      ((Nat.dvd_of_mem_primeFactors hp).trans
        (Finset.prod_dvd_prod_of_dvd _ _ fun i _ ↦ hdvd i))
    have huR : ∏ i, r i ≤ ⌊R⌋₊ := Nat.le_floor (by simpa [Nat.cast_prod] using hlt)
    omega
  exact (tsum_congr hzero).trans tsum_zero

/-- `(∏ᵢ dᵢ) * innerReciprocalSum R W d ≤ ∏_{p < ⌊R⌋₊ + 1 prime} (1 + k/(p-1))`, uniformly
in `d`. -/
theorem inner_le_euler_prod (k : ℕ) (hk : 1 ≤ k) (R : ℝ) (W : ℕ) (d : Fin k → ℕ) :
    (∏ i, (d i : ℝ)) * innerReciprocalSum R W d ≤
      ∏ p ∈ (⌊R⌋₊ + 1).primesBelow, (1 + (k : ℝ) / ((p : ℝ) - 1)) := by
  set N := ⌊R⌋₊ with hN
  set D := ∏ i, d i with hD
  have hfac_ge_one : ∀ p ∈ (N + 1).primesBelow, (1 : ℝ) ≤ 1 + (k : ℝ) / ((p : ℝ) - 1) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
    have : (0 : ℝ) ≤ (k : ℝ) / ((p : ℝ) - 1) := div_nonneg (by positivity) (by linarith)
    linarith
  have hRHS_nonneg : (0 : ℝ) ≤ ∏ p ∈ (N + 1).primesBelow, (1 + (k : ℝ) / ((p : ℝ) - 1)) :=
    Finset.prod_nonneg fun p hp ↦ le_trans zero_le_one (hfac_ge_one p hp)
  by_cases hbad : ∀ p ∈ D.primeFactors, p ≤ N
  · by_cases hD0 : D = 0
    · rw [show (∏ i, (d i : ℝ)) = 0 by rw [← Nat.cast_prod]; simp [← hD, hD0], zero_mul]
      exact hRHS_nonneg
    · have hA1 : (∏ i, (d i : ℝ)) * innerReciprocalSum R W d ≤
          ((∏ i, (d i : ℝ)) / (D.totient : ℝ)) * restrictedTauSum k N D := by
        simpa [← hN, ← hD] using inner_le_Dphi_restricted k R W d
      have hA3 : (D : ℝ) / (D.totient : ℝ) ≤
          ∏ p ∈ (N + 1).primesBelow with (p ∣ D), (1 + (k : ℝ) / ((p : ℝ) - 1)) :=
        Dphi_le_prod_dvd k N D hk (Nat.one_le_iff_ne_zero.mpr hD0) hbad
      have hP1nn : (0 : ℝ) ≤
          ∏ p ∈ (N + 1).primesBelow with (p ∣ D), (1 + (k : ℝ) / ((p : ℝ) - 1)) :=
        Finset.prod_nonneg fun p hp ↦ le_trans zero_le_one
          (hfac_ge_one p (Finset.mem_of_mem_filter p hp))
      calc (∏ i, (d i : ℝ)) * innerReciprocalSum R W d
          ≤ ((∏ i, (d i : ℝ)) / (D.totient : ℝ)) * restrictedTauSum k N D := hA1
        _ = ((D : ℝ) / (D.totient : ℝ)) * restrictedTauSum k N D := by rw [hD, Nat.cast_prod]
        _ ≤ (∏ p ∈ (N + 1).primesBelow with (p ∣ D), (1 + (k : ℝ) / ((p : ℝ) - 1))) *
              (∏ p ∈ (N + 1).primesBelow with ¬ (p ∣ D), (1 + (k : ℝ) / ((p : ℝ) - 1))) :=
              mul_le_mul hA3 (restricted_tau_sum_le_prod k N D)
                (restrictedTauSum_nonneg k N D) hP1nn
        _ = ∏ p ∈ (N + 1).primesBelow, (1 + (k : ℝ) / ((p : ℝ) - 1)) :=
              Finset.prod_filter_mul_prod_filter_not _ _ _
  · rw [inner_eq_zero_of_prime_gt k R W d hbad, mul_zero]
    exact hRHS_nonneg

/-- A constant `C = C(k)` with `∏_{p < ⌊R⌋₊ + 1 prime} (1 + k/(p-1)) ≤ C * (log R)^k` for
all `R ≥ 2`. -/
theorem euler_prod_le (k : ℕ) (hk : 1 ≤ k) : ∃ C : ℝ, 0 < C ∧
      ∀ (R : ℝ), 2 ≤ R → ∏ p ∈ (⌊R⌋₊ + 1).primesBelow, (1 + (k : ℝ) / ((p : ℝ) - 1)) ≤
          C * (Real.log R) ^ k := by
  obtain ⟨D, hDpos, hD⟩ := WeightedDivisorSum.exp_sum_inv_pred_prime_le k hk
  exact ⟨D, hDpos, fun R hR ↦ le_trans (WeightedDivisorSum.prod_one_add_le_exp_sum k
    ((⌊R⌋₊ + 1).primesBelow) fun p hp ↦ (Nat.prime_of_mem_primesBelow hp).two_le) (hD R hR)⟩

/-- A constant `C = C(k)` with `(∏ᵢ dᵢ) * innerReciprocalSum R W d ≤ C * (log R)^k` for all
`R ≥ 2`, uniformly in `W` and `d`. -/
theorem innerReciprocalSum_core (k : ℕ) (hk : 1 ≤ k) : ∃ C : ℝ, 0 < C ∧
      ∀ (R : ℝ) (W : ℕ) (d : Fin k → ℕ), 2 ≤ R →
        (∏ i, (d i : ℝ)) * innerReciprocalSum R W d ≤ C * (Real.log R) ^ k := by
  obtain ⟨C, hCpos, hC⟩ := euler_prod_le k hk
  exact ⟨C, hCpos, fun R W d hR ↦ (inner_le_euler_prod k hk R W d).trans (hC R hR)⟩

open PrimeGaps in
open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- `innerReciprocalSum_core` at the sieve parameters: `(∏ᵢ dᵢ) * innerReciprocalSum R (W N) d ≤
C * (log R)^k` for all `d`, eventually in `N`. -/
theorem mertens_core (k : ℕ) (hk : 2 ≤ k) : ∃ C : ℝ, 0 < C ∧
      ∀ θ δ : ℝ, 0 < θ → θ < 1 → 0 < δ → δ < θ / 2 → ∀ᶠ N : ℕ in atTop,
          ∀ d : Fin k → ℕ, (∏ i, (d i : ℝ)) *
                innerReciprocalSum R (W N) d ≤ C * (Real.log R) ^ k := by
  obtain ⟨C, hCpos, hC⟩ := innerReciprocalSum_core k (le_trans (by norm_num) hk)
  refine ⟨C, hCpos, fun θ δ hθ0 hθ1 hδ0 hδθ ↦ ?_⟩
  have hev : ∀ᶠ N : ℕ in atTop, 2 ≤ R := by
    have htend : Filter.Tendsto (fun N : ℕ ↦ R) atTop atTop :=
      (tendsto_rpow_atTop (show 0 < θ / 2 - δ by linarith)).comp tendsto_natCast_atTop_atTop
    exact htend.eventually_ge_atTop 2
  filter_upwards [hev] with N hN
  exact fun d ↦ hC R (W N) d hN

end RestrictedReciprocalSum
