/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Arithmetic.Mertens.W
public import PrimeGapsTheory.Arithmetic.TdDecomposition
public import PrimeGapsTheory.Sieve.S1.Expansion
public import PrimeGapsTheory.Sieve.S1.RestrictSij
public import PrimeGapsTheory.Sieve.Transforms.YmSubstituteSmooth

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Dropping off-diagonal coprimality

Bounds the change in the first-moment sum after removing off-diagonal coprimality.

## Main definitions

* `DropUij.raTerm`, `DropUij.facTerm`: The summands of the RA-guarded and factored sums.
* `DropUij.raGuard`, `DropUij.facGuard`: The guards restricting those two sums.
* `DropUij.box`: The finite box `[1, ⌊R⌋]^k` supporting every guarded summand.

## Main results

* `drop_uij_coupling_bound`: Bounds the difference between the restricted and factored sums.
-/

@[expose] public section

open scoped ArithmeticFunction.Moebius Finset Real

open GPYSieveS1 PrimeGaps.LemS1RestrictSij PrimeGaps

namespace DropUij

variable {k : ℕ}

/-- The summand of the RA-guarded sum (before the guard): `F(log u/log R)² / ∏ φ(uᵢ)`. -/
noncomputable def raTerm (R : ℝ) (F : EuclideanSpace ℝ (Fin k) → ℝ) (u : Fin k → ℕ) : ℝ :=
  (F (WithLp.toLp 2 (fun i ↦ Real.log (u i) / Real.log R))) ^ 2 / (∏ i, (Nat.totient (u i) : ℝ))

/-- The summand of the factored sum (before the guard): `(∏ μ(uᵢ)²/φ(uᵢ)) · F(log u/log R)²`. -/
noncomputable def facTerm (R : ℝ) (F : EuclideanSpace ℝ (Fin k) → ℝ) (u : Fin k → ℕ) : ℝ :=
  (∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ)) *
    (F (WithLp.toLp 2 (fun i ↦ Real.log (u i) / Real.log R))) ^ 2

/-- The RA guard as it appears in `S_RA`. -/
def raGuard (W : ℕ) (u : Fin k → ℕ) : Prop :=
  (∀ i, 1 ≤ u i) ∧ RestrictedCoprime u (fun _ _ ↦ 1) ∧ Squarefree (∏ i, u i) ∧ (∏ i, u i).Coprime W

/-- The factored guard as it appears in `S_fac`. -/
def facGuard (W : ℕ) (u : Fin k → ℕ) : Prop := (∀ i, 1 ≤ u i) ∧ (∀ i, Nat.Coprime (u i) W)

end DropUij

namespace PrimeGaps

/-- With the all-ones spacing matrix, `RestrictedCoprime u (fun _ _ => 1)` holds for every tuple
`u`: the predicate reduces to pairwise coprimality together with side conditions of the form
`gcd 1 _ = 1`, all of which are trivial.
-/
theorem restrictedCoprime_one {k : ℕ} (u : Fin k → ℕ) : RestrictedCoprime u (fun _ _ ↦ 1) := by
  simp [RestrictedCoprime]

end PrimeGaps

namespace Nat

/-- `Squarefree (∏ i, u i)` over a finite index type is equivalent to every factor `u i` being
squarefree together with pairwise coprimality of the factors.
-/
theorem squarefree_prod_fin_iff {k : ℕ} (u : Fin k → ℕ) : Squarefree (∏ i, u i) ↔
      (∀ i, Squarefree (u i)) ∧ (∀ i j, i ≠ j → (u i).Coprime (u j)) := by
  constructor
  · refine fun h ↦ ⟨fun i ↦ PrimeGaps.coord_squarefree u h i,
      fun i j hij ↦ Nat.coprime_of_squarefree_mul (h.squarefree_of_dvd ?_)⟩
    calc u i * u j = ∏ x ∈ ({i, j} : Finset (Fin k)), u x := (Finset.prod_pair hij).symm
      _ ∣ ∏ x, u x := Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)
  · rintro ⟨hsq, hcop⟩
    refine Finset.squarefree_prod_of_pairwise_isCoprime (fun i _ j _ hij ↦ ?_) fun i _ ↦ hsq i
    simpa only [Function.onFun] using Nat.coprime_iff_isRelPrime.mp (hcop i j hij)

end Nat

namespace PrimeGaps

open DropUij in
/-- On the RA support the two summands coincide: `raTerm δ θ N F u = facTerm δ θ N F u`. There each
`u i` is squarefree and coprime to `W`, so `μ(u i)² = 1` and the Möbius factors of `facTerm`
collapse, leaving `F(…)² / ∏ φ(u i) = raTerm`.
-/
theorem raTerm_eq_facTerm_on_raGuard {k : ℕ} (R : ℝ) (W : ℕ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) {u : Fin k → ℕ} (hu : DropUij.raGuard W u) :
    DropUij.raTerm R F u = DropUij.facTerm R F u := by
  obtain ⟨-, -, hsq, -⟩ := hu
  have hmu : ∀ i, (μ (u i) : ℝ) ^ 2 = 1 := fun i ↦ by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
      (((Nat.squarefree_prod_fin_iff u).mp hsq).1 i)
  simp only [DropUij.raTerm, DropUij.facTerm, hmu, Finset.prod_div_distrib, Finset.prod_const_one]
  ring

end PrimeGaps

namespace DropUij

/-- `facTerm` is always nonnegative. -/
theorem facTerm_nonneg {k : ℕ} (R : ℝ) (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (u : Fin k → ℕ) : 0 ≤ facTerm R F u := by
  unfold facTerm
  positivity

/-- `raGuard N u` implies `facGuard N u` together with pairwise coprimality. -/
theorem facGuard_of_raGuard {k : ℕ} (W : ℕ) {u : Fin k → ℕ} (h : raGuard W u) :
    facGuard W u ∧ (∀ i j, i ≠ j → (u i).Coprime (u j)) := by
  obtain ⟨h1, -, hsq, hcop⟩ := h
  exact ⟨⟨h1, Nat.coprime_fintype_prod_left_iff.mp hcop⟩,
    ((Nat.squarefree_prod_fin_iff u).mp hsq).2⟩

open Classical in
/-- The guarded RA summand equals the summand guarded by `facGuard ∧ pairwise-coprime`, pointwise
(using that `facTerm` vanishes on non-squarefree tuples).
-/
theorem raIndicator_eq_facIndicator {k : ℕ} (R : ℝ) (W : ℕ) (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (u : Fin k → ℕ) :
    (if raGuard W u then raTerm R F u else 0) =
      (if facGuard W u ∧ (∀ i j, i ≠ j → (u i).Coprime (u j)) then facTerm R F u else 0) := by
  by_cases hra : raGuard W u
  · rw [if_pos hra, if_pos (facGuard_of_raGuard W hra)]
    exact raTerm_eq_facTerm_on_raGuard R W F hra
  · rw [if_neg hra]
    by_cases hfc : facGuard W u ∧ (∀ i j, i ≠ j → (u i).Coprime (u j))
    · rw [if_pos hfc]
      obtain ⟨⟨h1, hcopeach⟩, hpair⟩ := hfc
      have hnotall : ¬ ∀ i, Squarefree (u i) := fun hall ↦ hra ⟨h1, restrictedCoprime_one u,
        (Nat.squarefree_prod_fin_iff u).mpr ⟨hall, hpair⟩,
        Nat.coprime_fintype_prod_left_iff.mpr hcopeach⟩
      push Not at hnotall
      obtain ⟨i, hi⟩ := hnotall
      rw [facTerm, Finset.prod_eq_zero (Finset.mem_univ i)
        (by simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hi]), zero_mul]
    · rw [if_neg hfc]

/-- The finite "box" of tuples whose coordinates lie in `[1, ⌊R⌋]`. Outside this box every guarded
summand vanishes (once `R > 1`).
-/
noncomputable def box {k : ℕ} (R : ℝ) : Finset (Fin k → ℕ) :=
  Fintype.piFinset (fun _ ↦ Finset.Icc 1 ⌊R⌋₊)

/-- If `1 < R`, `facGuard N u` holds, and `F (toLp (log u/log R)) ≠ 0`, then `u` lies in the box
`[1,⌊R⌋]^k`.
-/
theorem mem_box_of_facTerm_ne {k : ℕ} (R : ℝ) (W : ℕ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (hR : 1 < R)
    (hsupp : Function.support F ⊆ 𝓡 k)
    {u : Fin k → ℕ} (hg : facGuard W u)
    (hne : facTerm R F u ≠ 0) : u ∈ box R := by
  have hFne : F (WithLp.toLp 2 fun i ↦ Real.log (u i) / Real.log R) ≠ 0 := fun h0 ↦ hne <| by
    rw [facTerm, h0]
    ring
  rw [box, Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  refine ⟨hg.1 i, Nat.le_floor ?_⟩
  refine (Real.log_le_log_iff (Nat.cast_pos.mpr (hg.1 i)) (one_pos.trans hR)).mp ?_
  exact (div_le_one (Real.log_pos hR)).mp (coord_mem_Icc_of_mem_R (hsupp hFne) i).2

end DropUij

namespace PrimeGaps

/-- `PrimeGaps.MaynardOffDiagonal.sumA` is nonnegative. -/
theorem sumA_nonneg (R : ℝ) (W : ℕ) : 0 ≤ PrimeGaps.MaynardOffDiagonal.sumA W R :=
  Finset.sum_nonneg fun m _ ↦ by positivity

/-- Reindexing bound: the subsum of the Mertens mass restricted to multiples of a prime `p` is at
most `1/(p-1)` times the full mass.
-/
theorem sumA_dvd_le (R : ℝ) (W p : ℕ) (hp : p.Prime) :
    ∑ m ∈ {m ∈ (Finset.Icc 1 ⌊R⌋₊) | m.Coprime W ∧ p ∣ m},
        (μ m : ℝ) ^ 2 / (Nat.totient m : ℝ) ≤
      (1 / ((p : ℝ) - 1)) * PrimeGaps.MaynardOffDiagonal.sumA W R := by
  classical
  set g : ℕ → ℝ := fun m ↦ (μ m : ℝ) ^ 2 / (Nat.totient m : ℝ) with hg
  set L : Finset ℕ := {m ∈ Finset.Icc 1 ⌊R⌋₊ | m.Coprime W ∧ p ∣ m} with hL
  set S : Finset ℕ := {m ∈ Finset.Icc 1 ⌊R⌋₊ | m.Coprime W} with hS
  have hg_nonneg : ∀ m, 0 ≤ g m := fun m ↦ by rw [hg]; positivity
  have hp1pos : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    linarith
  have hpinv_nonneg : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) := by positivity
  have hstep : ∀ m ∈ L, g m ≤ (1 / ((p : ℝ) - 1)) * g (m / p) := by
    intro m hm
    rw [hL, Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm1, _⟩, _, hpdvd⟩ := hm
    by_cases hsf : Squarefree m
    · set a := m / p with ha
      have hma : m = p * a := (Nat.mul_div_cancel' hpdvd).symm
      have hpna : ¬ p ∣ a := by
        rintro ⟨b, hb⟩
        exact absurd (Nat.isUnit_iff.mp (hsf p (by rw [hma, hb]; exact ⟨b, by ring⟩))) hp.ne_one
      have hsfa : Squarefree a := hsf.squarefree_of_dvd ⟨p, by rw [hma]; ring⟩
      have hmum : (μ m : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
      have hmua : (μ a : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsfa
      have htot : Nat.totient m = (p - 1) * Nat.totient a := by
        rw [hma, Nat.totient_mul ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpna),
          Nat.totient_prime hp]
      have hapos : 0 < a := by
        rcases Nat.eq_zero_or_pos a with h0 | h
        · rw [h0, mul_zero] at hma; omega
        · exact h
      have hpe : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub hp.one_lt.le]; simp
      have hp1ne : ((p : ℝ) - 1) ≠ 0 := ne_of_gt hp1pos
      have htane : ((Nat.totient a : ℝ)) ≠ 0 := by
        have : (0 : ℝ) < (Nat.totient a : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hapos
        exact ne_of_gt this
      simp only [hg]
      rw [hmum, hmua, htot, Nat.cast_mul, hpe]
      apply le_of_eq
      field_simp
    · have hgm0 : g m = 0 := by
        rw [hg]
        simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
      rw [hgm0]
      exact mul_nonneg hpinv_nonneg (hg_nonneg _)
  have hinj : ∀ m₁ ∈ L, ∀ m₂ ∈ L, m₁ / p = m₂ / p → m₁ = m₂ := by
    intro m₁ hm₁ m₂ hm₂ heq
    rw [hL, Finset.mem_filter] at hm₁ hm₂
    calc m₁ = p * (m₁ / p) := (Nat.mul_div_cancel' hm₁.2.2).symm
      _ = p * (m₂ / p) := by rw [heq]
      _ = m₂ := Nat.mul_div_cancel' hm₂.2.2
  have himg : L.image (fun m ↦ m / p) ⊆ S := by
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨m, hmL, hma⟩ := ha
    rw [hL, Finset.mem_filter, Finset.mem_Icc] at hmL
    obtain ⟨⟨hm1, hmR⟩, hcop, hpdvd⟩ := hmL
    rw [hS, Finset.mem_filter, Finset.mem_Icc]
    subst hma
    exact ⟨⟨Nat.one_le_div_iff hp.pos |>.mpr (Nat.le_of_dvd hm1 hpdvd),
      le_trans (Nat.div_le_self m p) hmR⟩,
      Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hpdvd) hcop⟩
  have hmass : PrimeGaps.MaynardOffDiagonal.sumA W R = ∑ a ∈ S, g a := by
    rw [sumA_eq_mobiusTotientSum]
  calc ∑ m ∈ L, g m ≤ ∑ m ∈ L, (1 / ((p : ℝ) - 1)) * g (m / p) := Finset.sum_le_sum hstep
    _ = (1 / ((p : ℝ) - 1)) * ∑ a ∈ L.image (fun m ↦ m / p), g a := by
        rw [Finset.sum_image hinj, Finset.mul_sum]
    _ ≤ (1 / ((p : ℝ) - 1)) * ∑ a ∈ S, g a := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg himg fun i _ _ ↦ hg_nonneg i) hpinv_nonneg
    _ = (1 / ((p : ℝ) - 1)) * PrimeGaps.MaynardOffDiagonal.sumA W R := by rw [hmass]

/-- For `N` large, `4 ≤ D₀ N`. -/
theorem four_le_D0_of_large {N : ℝ} (hN : rexp (rexp (rexp 4)) ≤ N) :
    4 ≤ PrimeGaps.D₀ N := by
  change 4 ≤ Real.log (Real.log (Real.log N))
  have h1 : rexp (rexp 4) ≤ Real.log N := by
    rw [← Real.log_exp (rexp (rexp 4))]
    exact Real.log_le_log (Real.exp_pos _) hN
  have h2 : rexp 4 ≤ Real.log (Real.log N) := by
    rw [← Real.log_exp (rexp 4)]
    exact Real.log_le_log (Real.exp_pos _) h1
  rw [← Real.log_exp 4]
  exact Real.log_le_log (Real.exp_pos _) h2

open DropUij in
/-- Pointwise `Fmax` bound on `facTerm`: on a tuple satisfying `facGuard`, the factored summand is
at most the Möbius/totient product times `Fmax F ^ 2`.
-/
theorem facTerm_le_prod_g_Fmax {k : ℕ} (R : ℝ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hsupp : Function.support F ⊆ 𝓡 k)
    {u : Fin k → ℕ} :
    DropUij.facTerm R F u ≤
      (∏ l, (μ (u l) : ℝ) ^ 2 / (Nat.totient (u l) : ℝ)) *
        MaynardSmoothY.Fmax F ^ 2 := by
  unfold DropUij.facTerm
  set x := WithLp.toLp 2 fun i ↦ Real.log (u i) / Real.log R with hx
  refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun l _ ↦ by positivity)
  by_cases hFne : F x = 0
  · rw [hFne]
    simpa using sq_nonneg (MaynardSmoothY.Fmax F)
  · have habs : |F x| ≤ MaynardSmoothY.Fmax F := MaynardSmoothY.abs_F_le_Fmax F hF
      (coord_mem_Icc_of_mem_R (hsupp (by simpa [hx] using hFne)))
    calc F x ^ 2 = |F x| ^ 2 := (sq_abs _).symm
      _ ≤ MaynardSmoothY.Fmax F ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2

/-- A prime dividing a coordinate coprime to `W = primorial ⌊D₀⌋₊` must exceed `⌊D₀⌋₊`. -/
theorem prime_gt_floor_D0_of_dvd {N : ℕ} (W : ℕ)
    (hW : W = primorial ⌊PrimeGaps.D₀ (N : ℝ)⌋₊) {p n : ℕ} (hp : p.Prime)
    (hpn : p ∣ n) (hcop : n.Coprime W) :
    ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < p :=
  (Nat.floor_lt' hp.pos.ne').mpr (PrimeGaps.primeFactor_large (N : ℝ) n p (hW ▸ hcop) hp hpn)

open DropUij Classical in
/-- Factorization of the per-prime coupling sum over the box: for a fixed prime `p`, the box-sum
of `∏ g(u l)` over tuples coprime to `W` with `p ∣ u i` and `p ∣ u j` is at most
`PrimeGaps.MaynardOffDiagonal.sumA^k / (p-1)²`. -/
theorem couplingPrime_factor {k : ℕ} (R : ℝ) (W p : ℕ) (hp : p.Prime) (i j : Fin k) (hij : i ≠ j) :
    (∑ u ∈ DropUij.box R, (if (∀ l, (u l).Coprime W) ∧ p ∣ u i ∧ p ∣ u j
          then ∏ l, (μ (u l) : ℝ) ^ 2 / (Nat.totient (u l) : ℝ)
          else 0)) ≤ (PrimeGaps.MaynardOffDiagonal.sumA W R) ^ k / ((p : ℝ) - 1) ^ 2 := by
  classical
  set Rf := ⌊R⌋₊
  set g : ℕ → ℝ := fun m ↦ (μ m : ℝ) ^ 2 / (Nat.totient m : ℝ) with hgdef
  set S := {m ∈ Finset.Icc 1 Rf | m.Coprime W} with hS
  set Sp := {m ∈ Finset.Icc 1 Rf | m.Coprime W ∧ p ∣ m} with hSp
  set M := ∑ m ∈ S, g m with hM
  have hMmass : M = PrimeGaps.MaynardOffDiagonal.sumA W R := by
    rw [hM, hS, sumA_eq_mobiusTotientSum]
  have hp1pos : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    linarith
  have hdvd : (∑ m ∈ Sp, g m) ≤ (1 / ((p : ℝ) - 1)) * M := by
    rw [hMmass, hSp, hgdef]
    exact sumA_dvd_le R W p hp
  have hg_nonneg : ∀ m, 0 ≤ g m := fun m ↦ by rw [hgdef]; positivity
  set f : Fin k → ℕ → ℝ := fun l m ↦ if l = i ∨ l = j then (if m.Coprime W ∧ p ∣ m then g m else 0)
    else (if m.Coprime W then g m else 0) with hf
  have hf_nonneg : ∀ l m, 0 ≤ f l m := by
    intro l m
    rw [hf]
    simp only
    split <;> [split; split] <;> first | exact hg_nonneg m | exact le_refl 0
  have hcoordbnd : ∀ l : Fin k,
      (∑ m ∈ Finset.Icc 1 Rf, f l m) ≤ M * (if l = i ∨ l = j then (1 / ((p : ℝ) - 1)) else 1) := by
    intro l
    by_cases hl : l = i ∨ l = j
    · have hfl : ∀ m, f l m = (if m.Coprime W ∧ p ∣ m then g m else 0) := by
        intro m
        rw [hf]
        simp only
        rw [if_pos hl]
      have hEq : (∑ m ∈ Finset.Icc 1 Rf, (if m.Coprime W ∧ p ∣ m then g m else 0)) =
          ∑ m ∈ Sp, g m := by rw [hSp, Finset.sum_filter]
      rw [if_pos hl, Finset.sum_congr rfl (fun m _ ↦ hfl m), hEq, mul_comm M]
      exact hdvd
    · have hfl : ∀ m, f l m = (if m.Coprime W then g m else 0) := by
        intro m
        rw [hf]
        simp only
        rw [if_neg hl]
      have hEq : (∑ m ∈ Finset.Icc 1 Rf, (if m.Coprime W then g m else 0)) =
          ∑ m ∈ S, g m := by rw [hS, Finset.sum_filter]
      rw [if_neg hl, Finset.sum_congr rfl (fun m _ ↦ hfl m), hEq, hM, mul_one]
  have hcoord_nonneg : ∀ l : Fin k, 0 ≤ ∑ m ∈ Finset.Icc 1 Rf, f l m :=
    fun l ↦ Finset.sum_nonneg (fun m _ ↦ hf_nonneg l m)
  rw [← hMmass]
  calc (∑ u ∈ DropUij.box R,
          (if (∀ l, (u l).Coprime W) ∧ p ∣ u i ∧ p ∣ u j then ∏ l, g (u l) else 0)) ≤
      ∑ u ∈ DropUij.box R, ∏ l, f l (u l) := by
        refine Finset.sum_le_sum fun u _ ↦ ?_
        by_cases hcond : (∀ l, (u l).Coprime W) ∧ p ∣ u i ∧ p ∣ u j
        · rw [if_pos hcond]
          obtain ⟨hcop, hpi, hpj⟩ := hcond
          refine le_of_eq (Finset.prod_congr rfl fun l _ ↦ ?_)
          rw [hf]
          simp only
          by_cases hl : l = i ∨ l = j
          · rw [if_pos hl]
            rcases hl with rfl | rfl
            · rw [if_pos ⟨hcop l, hpi⟩]
            · rw [if_pos ⟨hcop l, hpj⟩]
          · rw [if_neg hl, if_pos (hcop l)]
        · rw [if_neg hcond]
          exact Finset.prod_nonneg (fun l _ ↦ hf_nonneg l (u l))
    _ = ∏ l : Fin k, ∑ m ∈ Finset.Icc 1 Rf, f l m := by
        rw [DropUij.box, Finset.prod_univ_sum]
    _ ≤ ∏ l : Fin k, M * (if l = i ∨ l = j then (1 / ((p : ℝ) - 1)) else 1) :=
        Finset.prod_le_prod (fun l _ ↦ hcoord_nonneg l) fun l _ ↦ hcoordbnd l
    _ = M ^ k * ∏ l : Fin k, (if l = i ∨ l = j then (1 / ((p : ℝ) - 1)) else 1) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = M ^ k * (1 / ((p : ℝ) - 1)) ^ 2 := by
        congr 1
        rw [Finset.prod_congr rfl fun l _ ↦ show (if l = i ∨ l = j then 1 / ((p : ℝ) - 1)
            else (1 : ℝ)) = if l ∈ ({i, j} : Finset (Fin k)) then 1 / ((p : ℝ) - 1) else 1 by
          congr 1
          simp, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const, Finset.card_pair hij]
    _ = M ^ k / ((p : ℝ) - 1) ^ 2 := by rw [div_pow, one_pow]; ring

open DropUij Classical in
/-- The non-coprime part of the box sum is dominated by the sum, over the primes `p ≤ ⌊R⌋₊`
exceeding `⌊D₀ N⌋₊`, of the part where `p` divides both `u i` and `u j`.  A tuple satisfying
`facGuard W` whose coordinates `u i, u j` share a factor shares a prime factor `p`, and `p` is
coprime to `W = primorial ⌊D₀ N⌋₊`, hence exceeds `⌊D₀ N⌋₊`; so that tuple is already counted by
the single term `p` of the inner sum. -/
private theorem sum_notCoprime_le_sum_over_primes_dvd {k : ℕ} (R : ℝ) (W N : ℕ)
    (hW : W = primorial ⌊PrimeGaps.D₀ (N : ℝ)⌋₊) (i j : Fin k) :
    (∑ u ∈ DropUij.box R, (if DropUij.facGuard W u ∧ ¬ (u i).Coprime (u j)
          then ∏ l, (μ (u l) : ℝ) ^ 2 / (Nat.totient (u l) : ℝ)
          else 0)) ≤ ∑ u ∈ DropUij.box R,
        ∑ p ∈ {q ∈ (Finset.Icc 1 ⌊R⌋₊) | q.Prime ∧ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < q},
          (if (∀ l, (u l).Coprime W) ∧ p ∣ u i ∧ p ∣ u j
            then ∏ l, (μ (u l) : ℝ) ^ 2 / (Nat.totient (u l) : ℝ)
            else 0) := by
  classical
  set Rf := ⌊R⌋₊
  set D0f := ⌊PrimeGaps.D₀ (N : ℝ)⌋₊
  set P : Finset ℕ := {q ∈ Finset.Icc 1 Rf | q.Prime ∧ D0f < q} with hP
  have hprod_nonneg : ∀ u : Fin k → ℕ,
      0 ≤ ∏ l, (μ (u l) : ℝ) ^ 2 / (Nat.totient (u l) : ℝ) :=
    fun u ↦ Finset.prod_nonneg fun l _ ↦ by positivity
  refine Finset.sum_le_sum fun u hubox ↦ ?_
  by_cases hc : DropUij.facGuard W u ∧ ¬ (u i).Coprime (u j)
  · rw [if_pos hc]
    obtain ⟨hguard, hncop⟩ := hc
    obtain ⟨p, hpp, hpi, hpj⟩ : ∃ p, p.Prime ∧ p ∣ u i ∧ p ∣ u j := by
      obtain ⟨p, hpp, hpd⟩ := Nat.exists_prime_and_dvd (hncop : Nat.gcd (u i) (u j) ≠ 1)
      exact ⟨p, hpp, hpd.trans (Nat.gcd_dvd_left _ _), hpd.trans (Nat.gcd_dvd_right _ _)⟩
    have hpmemP : p ∈ P := by
      rw [DropUij.box, Fintype.mem_piFinset] at hubox
      rw [hP, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hpp.one_lt.le, le_trans (Nat.le_of_dvd (hguard.1 i) hpi)
        (Finset.mem_Icc.mp (hubox i)).2⟩, hpp, prime_gt_floor_D0_of_dvd W hW hpp hpi (hguard.2 i)⟩
    refine le_trans (le_of_eq (if_pos ⟨hguard.2, hpi, hpj⟩).symm)
      (Finset.single_le_sum (f := fun q ↦ if (∀ l, (u l).Coprime W) ∧ q ∣ u i ∧ q ∣ u j
        then ∏ l, (μ (u l) : ℝ) ^ 2 / (Nat.totient (u l) : ℝ)
        else 0) (fun q _ ↦ ?_) hpmemP)
    split
    · exact hprod_nonneg u
    · exact le_rfl
  · rw [if_neg hc]
    refine Finset.sum_nonneg fun q _ ↦ ?_
    split
    · exact hprod_nonneg u
    · exact le_rfl

open DropUij Classical in
/-- Per-pair coupling bound: for a fixed pair `i ≠ j`, the coupling sum (over the box, tuples
coprime-to-`W` but with `u i, u j` sharing a prime) is at most
`Fmax² · PrimeGaps.MaynardOffDiagonal.sumA^k / (⌊D₀⌋₊ - 1)`. -/
theorem couplingPair_le {k : ℕ} (R : ℝ) (W N : ℕ) (hW : W = primorial ⌊PrimeGaps.D₀ (N : ℝ)⌋₊)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hsupp : Function.support F ⊆ 𝓡 k)
    (hND : 2 ≤ PrimeGaps.D₀ (N : ℝ))
    (i j : Fin k) (hij : i ≠ j) :
    ∑ u ∈ DropUij.box R, (if DropUij.facGuard W u ∧ ¬ (u i).Coprime (u j)
          then DropUij.facTerm R F u else 0) ≤ MaynardSmoothY.Fmax F ^ 2 *
        (PrimeGaps.MaynardOffDiagonal.sumA W R) ^ k /
          ((⌊PrimeGaps.D₀ (N : ℝ)⌋₊ : ℝ) - 1) := by
  classical
  set Rf := ⌊R⌋₊
  set D0f := ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ with hD0f
  set g : ℕ → ℝ := fun m ↦ (μ m : ℝ) ^ 2 / (Nat.totient m : ℝ) with hgdef
  set M := PrimeGaps.MaynardOffDiagonal.sumA W R with hM
  set P : Finset ℕ := {q ∈ Finset.Icc 1 Rf | q.Prime ∧ D0f < q} with hP
  have hMnn : 0 ≤ M := sumA_nonneg R W
  have hD0f2 : 2 ≤ D0f := by
    rw [hD0f]
    exact Nat.le_floor (by exact_mod_cast hND)
  have hStepA : (∑ u ∈ DropUij.box R, (if DropUij.facGuard W u ∧ ¬ (u i).Coprime (u j)
            then DropUij.facTerm R F u else 0)) ≤ MaynardSmoothY.Fmax F ^ 2 *
            (∑ u ∈ DropUij.box R, (if DropUij.facGuard W u ∧ ¬ (u i).Coprime (u j)
                then ∏ l, g (u l) else 0)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun u _ ↦ ?_
    by_cases hc : DropUij.facGuard W u ∧ ¬ (u i).Coprime (u j)
    · rw [if_pos hc, if_pos hc]
      simp only [hgdef]
      rw [mul_comm (MaynardSmoothY.Fmax F ^ 2)]
      exact facTerm_le_prod_g_Fmax (u := u) R F hF hsupp
    · rw [if_neg hc, if_neg hc, mul_zero]
  have hStepB : (∑ u ∈ DropUij.box R, (if DropUij.facGuard W u ∧ ¬ (u i).Coprime (u j)
            then ∏ l, g (u l) else 0)) ≤ ∑ u ∈ DropUij.box R,
            ∑ p ∈ P, (if (∀ l, (u l).Coprime W) ∧ p ∣ u i ∧ p ∣ u j
                then ∏ l, g (u l) else 0) :=
    sum_notCoprime_le_sum_over_primes_dvd R W N hW i j
  have hStepC : (∑ u ∈ DropUij.box R, ∑ p ∈ P, (if (∀ l, (u l).Coprime W) ∧ p ∣ u i ∧ p ∣ u j
              then ∏ l, g (u l) else 0)) = ∑ p ∈ P,
            ∑ u ∈ DropUij.box R, (if (∀ l, (u l).Coprime W) ∧ p ∣ u i ∧ p ∣ u j
                then ∏ l, g (u l) else 0) := Finset.sum_comm
  have hStepD : ∀ p ∈ P, (∑ u ∈ DropUij.box R, (if (∀ l, (u l).Coprime W) ∧ p ∣ u i ∧ p ∣ u j
            then ∏ l, g (u l) else 0)) ≤ M ^ k / ((p : ℝ) - 1) ^ 2 := by
    intro p hp
    rw [hgdef, hM]
    exact couplingPrime_factor R W p (Finset.mem_filter.mp hp).2.1 i j hij
  have hStepE : (∑ p ∈ P, M ^ k / ((p : ℝ) - 1) ^ 2) ≤ M ^ k / ((D0f : ℝ) - 1) := by
    have hMknn : 0 ≤ M ^ k := by positivity
    have htail : (∑ p ∈ P, 1 / ((p : ℝ) - 1) ^ 2) ≤ 1 / ((D0f : ℝ) - 1) :=
      prime_tail_inv_sq_le P D0f hD0f2 fun p hp ↦ (Finset.mem_filter.mp hp).2.2
    calc (∑ p ∈ P, M ^ k / ((p : ℝ) - 1) ^ 2) = M ^ k * ∑ p ∈ P, 1 / ((p : ℝ) - 1) ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun p _ ↦ by ring
      _ ≤ M ^ k * (1 / ((D0f : ℝ) - 1)) := mul_le_mul_of_nonneg_left htail hMknn
      _ = M ^ k / ((D0f : ℝ) - 1) := mul_one_div _ _
  calc (∑ u ∈ DropUij.box R, (if DropUij.facGuard W u ∧ ¬ (u i).Coprime (u j)
            then DropUij.facTerm R F u else 0)) ≤ MaynardSmoothY.Fmax F ^ 2 *
          (∑ u ∈ DropUij.box R, (if DropUij.facGuard W u ∧ ¬ (u i).Coprime (u j)
              then ∏ l, g (u l) else 0)) := hStepA
    _ ≤ MaynardSmoothY.Fmax F ^ 2 * (∑ p ∈ P, ∑ u ∈ DropUij.box R,
            (if (∀ l, (u l).Coprime W) ∧ p ∣ u i ∧ p ∣ u j
              then ∏ l, g (u l) else 0)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← hStepC]
        exact hStepB
    _ ≤ MaynardSmoothY.Fmax F ^ 2 * (∑ p ∈ P, M ^ k / ((p : ℝ) - 1) ^ 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hStepD) (by positivity)
    _ ≤ MaynardSmoothY.Fmax F ^ 2 * (M ^ k / ((D0f : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left hStepE (by positivity)
    _ = MaynardSmoothY.Fmax F ^ 2 * M ^ k / ((D0f : ℝ) - 1) := by ring

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
open DropUij Classical in
/-- **The RA/factored discrepancy is exactly the coupling mass.**  Both sums are supported on the
finite box `DropUij.box R`, and the RA guard is the factored guard together with pairwise
coprimality; so their difference is the sum of `facTerm` over the tuples that violate pairwise
coprimality, and that sum is nonnegative. -/
private theorem abs_ra_sub_fac_eq_coupling_sum {k : ℕ} (θ δ : ℝ) (N : ℕ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (hsupp : Function.support F ⊆ 𝓡 k) (hR : 1 < R) :
    |(∑' u : Fin k → ℕ, if DropUij.raGuard (W N) u then DropUij.raTerm (R) F u else 0) -
      (∑' u : Fin k → ℕ, if DropUij.facGuard (W N) u then DropUij.facTerm (R) F u else 0)| =
    ∑ u ∈ DropUij.box (R), (if DropUij.facGuard (W N) u ∧
        ¬ (∀ i j, i ≠ j → (u i).Coprime (u j)) then DropUij.facTerm (R) F u else 0) := by
  classical
  have hRA : (∑' u : Fin k → ℕ, if DropUij.raGuard (W N) u then DropUij.raTerm (R) F u else 0) =
        ∑ u ∈ DropUij.box (R), (if DropUij.facGuard (W N) u ∧ (∀ i j, i ≠ j → (u i).Coprime (u j))
              then DropUij.facTerm (R) F u else 0) := by
    rw [tsum_congr (fun u ↦ DropUij.raIndicator_eq_facIndicator R (W N) F u)]
    refine tsum_eq_sum' fun u hu ↦ ?_
    simp only [Function.mem_support, ne_eq] at hu
    by_cases hg : DropUij.facGuard (W N) u ∧ (∀ i j, i ≠ j → (u i).Coprime (u j))
    · rw [if_pos hg] at hu
      exact DropUij.mem_box_of_facTerm_ne R (W N) F hR hsupp hg.1 hu
    · exact absurd (if_neg hg) hu
  have hfac : (∑' u : Fin k → ℕ,
    if DropUij.facGuard (W N) u then DropUij.facTerm (R) F u else 0) = ∑ u ∈ DropUij.box (R),
            (if DropUij.facGuard (W N) u then DropUij.facTerm (R) F u else 0) := by
    refine tsum_eq_sum' fun u hu ↦ ?_
    simp only [Function.mem_support, ne_eq] at hu
    by_cases hg : DropUij.facGuard (W N) u
    · rw [if_pos hg] at hu
      exact DropUij.mem_box_of_facTerm_ne R (W N) F hR hsupp hg hu
    · exact absurd (if_neg hg) hu
  rw [hRA, hfac, ← Finset.sum_sub_distrib]
  have hterm : ∀ u : Fin k → ℕ, (if DropUij.facGuard (W N) u ∧ (∀ i j, i ≠ j → (u i).Coprime (u j))
          then DropUij.facTerm (R) F u else 0) -
        (if DropUij.facGuard (W N) u then DropUij.facTerm (R) F u else 0) = -
      (if DropUij.facGuard (W N) u ∧ ¬ (∀ i j, i ≠ j → (u i).Coprime (u j))
            then DropUij.facTerm (R) F u else 0) := by
    intro u
    by_cases hfg : DropUij.facGuard (W N) u
    · by_cases hpw : (∀ i j, i ≠ j → (u i).Coprime (u j))
      · rw [if_pos ⟨hfg, hpw⟩, if_pos hfg, if_neg (fun h ↦ h.2 hpw), neg_zero, sub_self]
      · rw [if_neg (fun h ↦ hpw h.2), if_pos hfg, if_pos ⟨hfg, hpw⟩, zero_sub]
    · rw [if_neg (fun h ↦ hfg h.1), if_neg hfg, if_neg (fun h ↦ hfg h.1), neg_zero, sub_self]
  rw [Finset.sum_congr rfl (fun u _ ↦ hterm u), Finset.sum_neg_distrib, abs_neg]
  refine abs_of_nonneg (Finset.sum_nonneg fun u _ ↦ ?_)
  split
  · exact DropUij.facTerm_nonneg R F u
  · exact le_rfl

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
open DropUij Classical in
/-- The analytic crux: the coupling (pairwise-coprimality-violating) part of the factored sum,
which equals `|S_RA - S_fac|`, is `O(1/D₀)` times the factored Mertens mass. Concretely, for a
uniform constant `C > 0` and threshold `N₀`,
`|S_RA - S_fac| ≤ C · (Fmax F)² · φ(W)^k · (log R)^k / (W^k · D₀)` for all `N ≥ N₀`.
-/
@[pg_tag "bg246" "lem_S1_drop_uij"]
theorem drop_uij_coupling_bound {k : ℕ} (δ θ : ℝ)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2)) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : EuclideanSpace ℝ (Fin k) → ℝ), ContDiff ℝ (⊤ : ℕ∞) F → Function.support F ⊆ 𝓡 k →
        |(∑' u : Fin k → ℕ,
            if DropUij.raGuard (W N) u then DropUij.raTerm (R) F u else 0) - (∑' u : Fin k → ℕ,
            if DropUij.facGuard (W N) u then DropUij.facTerm (R) F u else 0)| ≤
        C * (MaynardSmoothY.Fmax F) ^ 2 * ((W N).totient : ℝ) ^ k * (Real.log (R)) ^ k /
            ((W N : ℝ) ^ k * PrimeGaps.D₀ (N : ℝ)) := by
  classical
  obtain ⟨c₁, hc₁, hmass⟩ := PrimeGaps.MaynardOffDiagonal.sumA_le
  obtain ⟨Nm, -, hNmass⟩ := hmass θ δ hθ hδ
  obtain ⟨aR, haR⟩ := Filter.eventually_atTop.mp (R_eventually_ge θ δ hδ.2 2)
  obtain ⟨aD, haD⟩ := Filter.eventually_atTop.mp
    (Filter.eventually_atTop.2 ⟨⌈rexp (rexp (rexp 4))⌉₊, fun n hn ↦
      four_le_D0_of_large (le_trans (Nat.le_ceil _) (by exact_mod_cast hn))⟩ :
      ∀ᶠ n : ℕ in Filter.atTop, 4 ≤ PrimeGaps.D₀ (n : ℝ))
  have hkk : (0 : ℝ) ≤ (k : ℝ) * ((k : ℝ) - 1) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk1
    · simp [hk0]
    · have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
      nlinarith
  refine ⟨2 * ((k : ℝ) * ((k : ℝ) - 1)) * c₁ ^ k + 1, by positivity,
    max (max (aR : ℝ) (aD : ℝ)) Nm, fun N hN F hF hsupp ↦ ?_⟩
  have hNa : aR ≤ N := by
    have : (aR : ℝ) ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
    exact_mod_cast this
  have hND4 : 4 ≤ PrimeGaps.D₀ (N : ℝ) := by
    have : (aD : ℝ) ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
    exact haD N (by exact_mod_cast this)
  have hND : 2 ≤ PrimeGaps.D₀ (N : ℝ) := by linarith
  have hNmassN : PrimeGaps.MaynardOffDiagonal.sumA (W N) R ≤
      c₁ * ((W N).totient : ℝ) / (W N : ℝ) * Real.log R := by
    have hmN := hNmass (N : ℝ) (le_trans (le_max_right _ _) hN)
    rw [PrimeGaps.W_eq_primorial_D₀, show R = (N : ℝ) ^ (θ / 2 - δ) from rfl]
    convert hmN using 2
  have hR : 1 < R := lt_of_lt_of_le one_lt_two (haR N hNa)
  rw [abs_ra_sub_fac_eq_coupling_sum θ δ N F hsupp hR]
  set M := PrimeGaps.MaynardOffDiagonal.sumA (W N) R with hM
  set Fm := MaynardSmoothY.Fmax F with hFm
  have hMnn : 0 ≤ M := sumA_nonneg R (W N)
  have hFmnn : 0 ≤ Fm := MaynardSmoothY.Fmax_nonneg F hF
  have hUnion : (∑ u ∈ DropUij.box R,
          (if DropUij.facGuard (W N) u ∧ ¬ (∀ i j, i ≠ j → (u i).Coprime (u j))
            then DropUij.facTerm R F u else 0)) ≤ ∑ p ∈ (Finset.univ : Finset (Fin k)).offDiag,
            ∑ u ∈ DropUij.box R, (if DropUij.facGuard (W N) u ∧ ¬ (u p.1).Coprime (u p.2)
                then DropUij.facTerm R F u else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun u _ ↦ ?_
    by_cases hg : DropUij.facGuard (W N) u ∧ ¬ (∀ i j, i ≠ j → (u i).Coprime (u j))
    · rw [if_pos hg]
      obtain ⟨i, j, hij, hnc⟩ : ∃ i j : Fin k, i ≠ j ∧ ¬ (u i).Coprime (u j) := by
        have h2 := hg.2
        push Not at h2
        exact h2
      calc DropUij.facTerm R F u
          = (if DropUij.facGuard (W N) u ∧ ¬ (u (i, j).1).Coprime (u (i, j).2)
              then DropUij.facTerm R F u else 0) := (if_pos ⟨hg.1, hnc⟩).symm
        _ ≤ ∑ p ∈ (Finset.univ : Finset (Fin k)).offDiag,
              (if DropUij.facGuard (W N) u ∧ ¬ (u p.1).Coprime (u p.2)
                then DropUij.facTerm R F u else 0) := by
              refine Finset.single_le_sum (f := fun p ↦
                if DropUij.facGuard (W N) u ∧ ¬ (u p.1).Coprime (u p.2)
                  then DropUij.facTerm R F u else 0) (fun p _ ↦ ?_)
                (show (i, j) ∈ (Finset.univ : Finset (Fin k)).offDiag from
                  Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hij⟩)
              split
              · exact DropUij.facTerm_nonneg R F u
              · exact le_rfl
    · rw [if_neg hg]
      refine Finset.sum_nonneg fun p _ ↦ ?_
      split
      · exact DropUij.facTerm_nonneg R F u
      · exact le_rfl
  have hPair : ∀ p ∈ (Finset.univ : Finset (Fin k)).offDiag, (∑ u ∈ DropUij.box R,
        (if DropUij.facGuard (W N) u ∧ ¬ (u p.1).Coprime (u p.2)
          then DropUij.facTerm R F u else 0)) ≤
        Fm ^ 2 * M ^ k / ((⌊PrimeGaps.D₀ (N : ℝ)⌋₊ : ℝ) - 1) := fun p hp ↦
    couplingPair_le R (W N) N PrimeGaps.W_eq_primorial_D₀ F hF hsupp hND p.1 p.2
      (Finset.mem_offDiag.mp hp).2.2
  have hCard : (#(Finset.univ : Finset (Fin k)).offDiag : ℝ) ≤ (k : ℝ) * ((k : ℝ) - 1) := by
    rw [Finset.offDiag_card]
    simp only [Finset.card_univ, Fintype.card_fin]
    rcases Nat.eq_zero_or_pos k with hk0 | hk1
    · simp [hk0]
    · rw [Nat.cast_sub (Nat.le_mul_of_pos_left k hk1)]
      push_cast
      nlinarith [sq_nonneg ((k : ℝ))]
  have hfloor4 : (4 : ℕ) ≤ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ := Nat.le_floor (by exact_mod_cast hND4)
  have hfloorm1pos : (0 : ℝ) < (⌊PrimeGaps.D₀ (N : ℝ)⌋₊ : ℝ) - 1 := by
    have : (4 : ℝ) ≤ (⌊PrimeGaps.D₀ (N : ℝ)⌋₊ : ℝ) := by exact_mod_cast hfloor4
    linarith
  have hBoundNN : 0 ≤ Fm ^ 2 * M ^ k / ((⌊PrimeGaps.D₀ (N : ℝ)⌋₊ : ℝ) - 1) :=
    div_nonneg (by positivity) (by linarith)
  have hStep3 : (∑ p ∈ (Finset.univ : Finset (Fin k)).offDiag,
          ∑ u ∈ DropUij.box R, (if DropUij.facGuard (W N) u ∧ ¬ (u p.1).Coprime (u p.2)
              then DropUij.facTerm R F u else 0)) ≤
        ((k : ℝ) * ((k : ℝ) - 1)) * (Fm ^ 2 * M ^ k / ((⌊PrimeGaps.D₀ (N : ℝ)⌋₊ : ℝ) - 1)) :=
    calc _ ≤ ∑ _ ∈ (Finset.univ : Finset (Fin k)).offDiag,
                (Fm ^ 2 * M ^ k / ((⌊PrimeGaps.D₀ (N : ℝ)⌋₊ : ℝ) - 1)) :=
              Finset.sum_le_sum hPair
      _ = (#(Finset.univ : Finset (Fin k)).offDiag : ℝ) *
            (Fm ^ 2 * M ^ k / ((⌊PrimeGaps.D₀ (N : ℝ)⌋₊ : ℝ) - 1)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((k : ℝ) * ((k : ℝ) - 1)) * (Fm ^ 2 * M ^ k / ((⌊PrimeGaps.D₀ (N : ℝ)⌋₊ : ℝ) - 1)) :=
              mul_le_mul_of_nonneg_right hCard hBoundNN
  refine le_trans (le_trans hUnion hStep3) ?_
  have hWpos : (0 : ℝ) < (W N : ℝ) := by exact_mod_cast PrimeGaps.W_pos (N := N)
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR.le
  have hD0pos : (0 : ℝ) < PrimeGaps.D₀ (N : ℝ) := by linarith
  have hD0m1pos : (0 : ℝ) < PrimeGaps.D₀ (N : ℝ) - 1 := by linarith
  have hfloorlt : PrimeGaps.D₀ (N : ℝ) - 1 < (⌊PrimeGaps.D₀ (N : ℝ)⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (PrimeGaps.D₀ (N : ℝ))
    linarith
  have hMk : M ^ k ≤ c₁ ^ k * ((W N).totient : ℝ) ^ k * Real.log R ^ k / (W N : ℝ) ^ k :=
    calc M ^ k ≤ (c₁ * ((W N).totient : ℝ) / (W N : ℝ) * Real.log R) ^ k :=
          pow_le_pow_left₀ hMnn hNmassN k
      _ = c₁ ^ k * ((W N).totient : ℝ) ^ k * Real.log R ^ k / (W N : ℝ) ^ k := by
          rw [mul_pow, div_pow, mul_pow]
          ring
  have hFm2nn : 0 ≤ Fm ^ 2 := by positivity
  have hMkNN : 0 ≤ M ^ k := by positivity
  rw [div_eq_mul_inv (Fm ^ 2 * M ^ k)]
  set D0 := PrimeGaps.D₀ (N : ℝ) with hD0
  set φW := ((W N).totient : ℝ) with hφW
  set WN := (W N : ℝ) with hWN
  set LR := Real.log R with hLR
  have hφWnn : 0 ≤ φW := by positivity
  have hLRnn : 0 ≤ LR := hlogR
  have hinvle : ((⌊PrimeGaps.D₀ (N : ℝ)⌋₊ : ℝ) - 1)⁻¹ ≤ 2 / D0 := by
    rw [← one_div, div_le_div_iff₀ hfloorm1pos hD0pos]
    nlinarith [hND4, hfloorlt]
  have hMknn' : 0 ≤ c₁ ^ k * φW ^ k * LR ^ k / WN ^ k := by positivity
  calc (k : ℝ) * ((k : ℝ) - 1) * (Fm ^ 2 * M ^ k * ((⌊PrimeGaps.D₀ (N : ℝ)⌋₊ : ℝ) - 1)⁻¹)
      ≤ (k : ℝ) * ((k : ℝ) - 1) * (Fm ^ 2 * (c₁ ^ k * φW ^ k * LR ^ k / WN ^ k) * (2 / D0)) :=
        mul_le_mul_of_nonneg_left (le_trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMk hFm2nn)
            (inv_nonneg.mpr hfloorm1pos.le))
          (mul_le_mul_of_nonneg_left hinvle (by positivity))) hkk
    _ = 2 * ((k : ℝ) * ((k : ℝ) - 1)) * c₁ ^ k * (Fm ^ 2 * φW ^ k * LR ^ k) / (WN ^ k * D0) := by
        field_simp
    _ ≤ (2 * ((k : ℝ) * ((k : ℝ) - 1)) * c₁ ^ k + 1) * Fm ^ 2 * φW ^ k * LR ^ k /
          (WN ^ k * D0) := by
        refine div_le_div_of_nonneg_right ?_ (by positivity : (0 : ℝ) ≤ WN ^ k * D0)
        have hslack : 0 ≤ Fm ^ 2 * φW ^ k * LR ^ k := by positivity
        nlinarith [hslack]

end PrimeGaps
