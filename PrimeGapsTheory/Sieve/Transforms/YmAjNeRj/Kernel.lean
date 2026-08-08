/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Discrete.MaxRealAbs
public import PrimeGapsTheory.Arithmetic.Mertens.CoprimeHarmonic
public import PrimeGapsTheory.Auxiliary.UnionBound
public import PrimeGapsTheory.Sieve.Transforms.YmRearrange

/-!
# The off-diagonal kernel

The off-diagonal summand, its kernel majorant, and the reduction of the kernel sum.

## Main results

* `offDiagKernel_le_reduction`
-/

@[expose] public section

open Real

open scoped Finset
open scoped ArithmeticFunction.Moebius

open scoped ArithmeticFunction.detotient

namespace PrimeGaps

open scoped ArithmeticFunction BigOperators

namespace MaynardOffDiagonal

open ArithmeticFunction (moebius)

noncomputable section

/-- The summand `T(a)` for fixed `m` and `r` with `r_m = 1`:
`T(a) = (∏ᵢ μ(rᵢ) g(rᵢ)) · (y_a / ∏ᵢ φ(aᵢ)) · ∏_{i ≠ m} μ(aᵢ) rᵢ / φ(aᵢ)`. The prefactor
`∏ᵢ μ(rᵢ) g(rᵢ)` depends only on `r`, not on `a`. -/
def Tsummand {k : ℕ} (y : (Fin k → ℕ) →₀ ℝ) (m : Fin k) (r a : Fin k → ℕ) : ℝ :=
  (∏ i, ((μ (r i) : ℝ) * (g (r i) : ℝ))) * (y a / (∏ i, (Nat.totient (a i) : ℝ))) *
    (∏ i ∈ Finset.univ.erase m, ((μ (a i) : ℝ) * (r i : ℝ)) / (Nat.totient (a i) : ℝ))

/-- The diagonal index set `D = {a: rᵢ ∣ aᵢ ∀ i, and aᵢ = rᵢ for all i ≠ m}`. Only the coordinate
`a_m` is free (subject to `r_m ∣ a_m`; since `r_m = 1` this is no constraint). -/
def Diag {k : ℕ} (m : Fin k) (r a : Fin k → ℕ) : Prop := (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i

/-- The off-diagonal index set `O = {a: rᵢ ∣ aᵢ ∀ i, and ∃ j ≠ m, a_j ≠ r_j}`. -/
def OffDiag {k : ℕ} (m : Fin k) (r a : Fin k → ℕ) : Prop :=
  (∀ i, r i ∣ a i) ∧ ∃ j, j ≠ m ∧ a j ≠ r j

/-- The diagonal and off-diagonal index sets are disjoint: no tuple `a` lies in both. -/
theorem diag_offDiag_disjoint {k : ℕ} (m : Fin k) (r a : Fin k → ℕ) :
    ¬ (Diag m r a ∧ OffDiag m r a) := by
  rintro ⟨⟨_, hd⟩, ⟨_, j, hj, hne⟩⟩
  exact hne (hd j hj)

/-- The constraint `∀ i, r i ∣ a i` splits as `Diag m r a ∨ OffDiag m r a`. -/
theorem diag_union_offDiag {k : ℕ} (m : Fin k) (r a : Fin k → ℕ) :
    (∀ i, r i ∣ a i) ↔ (Diag m r a ∨ OffDiag m r a) := by
  refine ⟨fun hdvd ↦ ?_, ?_⟩
  · by_cases h : ∀ i, i ≠ m → a i = r i
    · exact Or.inl ⟨hdvd, h⟩
    · push Not at h
      exact Or.inr ⟨hdvd, h⟩
  · rintro (⟨hdvd, _⟩ | ⟨hdvd, _⟩) <;> exact hdvd

/-- The `y` -free majorant `|∏ᵢ μ(rᵢ) g(rᵢ)| · ∑_{a ∈ O, a permissible} (1 / ∏ᵢ φ(aᵢ)) ·
∏_{i ≠ m} rᵢ / φ(aᵢ)` of the off-diagonal sum. -/
def offDiagKernel {k : ℕ} (W : ℕ) (R : ℝ) (m : Fin k) (r : Fin k → ℕ) : ℝ :=
  |∏ i, ((μ (r i) : ℝ) * (g (r i) : ℝ))| *
    ∑ᶠ (a : Fin k → ℕ) (_ : OffDiag m r a ∧ a ∈ Finset.permissibleSupport k ⌊R⌋₊ W),
      (1 / (∏ i, (Nat.totient (a i) : ℝ))) *
        ∏ i ∈ Finset.univ.erase m, (r i : ℝ) / (Nat.totient (a i) : ℝ)

/-- Pointwise majorant for the off-diagonal summand: at a permissible `a`, the summand `T(a)` is
bounded by `y.maxRealAbs` times the corresponding term of `offDiagKernel`, because `|y a| ≤
y.maxRealAbs` and each Möbius factor has absolute value at most one. -/
theorem abs_Tsummand_le_maxRealAbs_mul_kernelTerm {k : ℕ} (W : ℕ) (R : ℝ)
    (y : (Fin k → ℕ) →₀ ℝ) (m : Fin k) (r a : Fin k → ℕ)
    (ha : a ∈ Finset.permissibleSupport k ⌊R⌋₊ W) :
    |Tsummand y m r a| ≤ y.maxRealAbs * (|∏ i, ((μ (r i) : ℝ) * (g (r i) : ℝ))| *
        ((1 / (∏ i, (Nat.totient (a i) : ℝ))) *
          ∏ i ∈ Finset.univ.erase m, (r i : ℝ) / (Nat.totient (a i) : ℝ))) := by
  have hymax0 : (0 : ℝ) ≤ y.maxRealAbs := Finsupp.maxRealAbs_nonneg
  have hya : |y a| ≤ y.maxRealAbs := Finsupp.le_maxRealAbs
  have hapos : ∀ i, (0 : ℝ) < (Nat.totient (a i) : ℝ) := fun i ↦ by
    exact_mod_cast Nat.totient_pos.mpr
      (Nat.pos_of_ne_zero ((Finset.mem_permissibleSupport_iff'.mp ha).1 i))
  have hphi : (0 : ℝ) < ∏ i, (Nat.totient (a i) : ℝ) := Finset.prod_pos fun i _ ↦ hapos i
  have hQ : |∏ i ∈ Finset.univ.erase m,
      ((μ (a i) : ℝ) * (r i : ℝ)) / (Nat.totient (a i) : ℝ)| ≤
      ∏ i ∈ Finset.univ.erase m, (r i : ℝ) / (Nat.totient (a i) : ℝ) := by
    rw [Finset.abs_prod]
    refine Finset.prod_le_prod (fun i _ ↦ abs_nonneg _) fun i _ ↦ ?_
    rw [abs_div, abs_mul, Nat.abs_cast, abs_of_pos (hapos i)]
    gcongr
    refine mul_le_of_le_one_left (by positivity) ?_
    rw [← Int.cast_abs]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  rw [show y.maxRealAbs * (|∏ i, ((μ (r i) : ℝ) * (g (r i) : ℝ))| *
      ((1 / (∏ i, (Nat.totient (a i) : ℝ))) *
        ∏ i ∈ Finset.univ.erase m, (r i : ℝ) / (Nat.totient (a i) : ℝ))) =
      |∏ i, ((μ (r i) : ℝ) * (g (r i) : ℝ))| *
        (y.maxRealAbs / (∏ i, (Nat.totient (a i) : ℝ))) *
        ∏ i ∈ Finset.univ.erase m, (r i : ℝ) / (Nat.totient (a i) : ℝ) by ring]
  unfold Tsummand
  rw [abs_mul, abs_mul, abs_div, abs_of_pos hphi]
  gcongr

/-- For `y` with permissible support, `|∑_{a ∈ O} Tsummand y m r a| ≤
y.maxRealAbs * offDiagKernel W R m r`. -/
theorem offDiag_abs_le_maxRealAbs_kernel {k : ℕ} (W : ℕ) (R : ℝ) (y : (Fin k → ℕ) →₀ ℝ)
    (hy : y.HasPermissibleSupport ⌊R⌋₊ W)
    (m : Fin k) (r : Fin k → ℕ) :
    |∑ᶠ (a : Fin k → ℕ) (_ : OffDiag m r a), Tsummand y m r a| ≤
      y.maxRealAbs * offDiagKernel W R m r := by
  have hSfin : {a : Fin k → ℕ | OffDiag m r a ∧ a ∈ Finset.permissibleSupport k ⌊R⌋₊ W}.Finite :=
    (Finset.permissibleSupport k ⌊R⌋₊ W).finite_toSet.subset fun _ ha ↦ ha.2
  set t := hSfin.toFinset
  have hmemt : ∀ x, x ∈ t ↔ (OffDiag m r x ∧ x ∈ Finset.permissibleSupport k ⌊R⌋₊ W) := fun x ↦
    hSfin.mem_toFinset
  have hLHS : (∑ᶠ (a : Fin k → ℕ) (_ : OffDiag m r a), Tsummand y m r a) =
      ∑ a ∈ t, Tsummand y m r a := by
    apply finsum_cond_eq_sum_of_cond_iff
    intro a hTne
    have hyne : y a ≠ 0 := fun hy0 ↦ hTne (by
      unfold Tsummand; rw [hy0, zero_div, mul_zero, zero_mul])
    rw [hmemt]
    exact ⟨fun hod ↦ ⟨hod, hy (Finsupp.mem_support_iff.mpr hyne)⟩, And.left⟩
  have hKER : (∑ᶠ (a : Fin k → ℕ) (_ : OffDiag m r a ∧ a ∈ Finset.permissibleSupport k ⌊R⌋₊ W),
      (1 / (∏ i, (Nat.totient (a i) : ℝ))) *
        ∏ i ∈ Finset.univ.erase m, (r i : ℝ) / (Nat.totient (a i) : ℝ)) =
      ∑ a ∈ t, (1 / (∏ i, (Nat.totient (a i) : ℝ))) *
        ∏ i ∈ Finset.univ.erase m, (r i : ℝ) / (Nat.totient (a i) : ℝ) := by
    apply finsum_cond_eq_sum_of_cond_iff
    intro a _
    rw [hmemt]
  rw [hLHS]
  unfold offDiagKernel
  rw [hKER, Finset.mul_sum, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a ha ↦ ?_)
  exact abs_Tsummand_le_maxRealAbs_mul_kernelTerm W R y m r a ((hmemt a).1 ha).2

/-- For `k ≤ 1` there is no index `j ≠ m`, so `offDiagKernel W R m r = 0`. -/
theorem offDiagKernel_eq_zero_of_le_one {k : ℕ} (hk : k ≤ 1) (W : ℕ) (R : ℝ)
    (m : Fin k) (r : Fin k → ℕ) : offDiagKernel W R m r = 0 := by
  unfold offDiagKernel
  convert mul_zero _
  apply finsum_mem_eq_zero_of_forall_eq_zero
  rintro a ⟨⟨_, j, hj, _⟩, _⟩
  exact absurd (Fin.ext (by omega : (j : ℕ) = (m : ℕ))) hj

/-- `2 ≤ D₀ N = log log log N` once `exp (exp (exp 2)) ≤ N`. -/
theorem two_le_D0_of_large {N : ℝ} (hN : rexp (rexp (rexp 2)) ≤ N) : 2 ≤ D₀ N := by
  unfold D₀
  have key : ∀ x y : ℝ, rexp x ≤ y → x ≤ Real.log y := fun x _ h ↦ by
    rw [← Real.log_exp x]; exact Real.log_le_log (Real.exp_pos _) h
  exact key 2 _ (key _ _ (key _ _ hN))

/-- Nonnegativity of the kernel bound `C₀ · φ(W) · log R / (W · D₀ N)`. -/
theorem kernel_rhs_nonneg {C₀ : ℝ} (hC₀ : 0 ≤ C₀) {θ δ N : ℝ}
    (hD : 0 < D₀ N) (hR : 0 ≤ Real.log (N ^ (θ / 2 - δ))) :
    0 ≤ C₀ * (Nat.totient (primorial ⌊D₀ N⌋₊) : ℝ) * Real.log (N ^ (θ / 2 - δ)) /
          ((primorial ⌊D₀ N⌋₊ : ℝ) * D₀ N) := by
  positivity

/-- `g n * n ≤ φ n ^ 2` for squarefree `n`, from `(p - 2) * p ≤ (p - 1) ^ 2` at each prime. -/
theorem gMaynard_cast_mul_self_le_totient_sq {n : ℕ} (hn : Squarefree n) :
    (g n : ℝ) * (n : ℝ) ≤ (Nat.totient n : ℝ) ^ 2 := by
  rw [ArithmeticFunction.coe_detotient_squarefree_eq_prod (R := ℝ) hn,
      squarefree_eq_prod_primes n hn,
      totient_eq_prod_sub_one n (Nat.pos_of_ne_zero hn.ne_zero) hn,
      ← Finset.prod_mul_distrib, sq, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun p hp ↦ ?_) (fun p hp ↦ ?_) <;>
    · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      nlinarith

/-- `|∏ᵢ μ(rᵢ) g(rᵢ)| · (1 / ∏ᵢ φ(rᵢ)) · ∏_{i ≠ m} rᵢ / φ(rᵢ) ≤ 1` for positive `r` with
`r m = 1`. -/
theorem offdiag_prefactor_le_one {k : ℕ} (m : Fin k) (r : Fin k → ℕ)
    (hr : ∀ i, 0 < r i) (hrm : r m = 1) :
    |∏ i, ((μ (r i) : ℝ) * (g (r i) : ℝ))| * (1 / ∏ i, (Nat.totient (r i) : ℝ)) *
        ∏ i ∈ Finset.univ.erase m, (r i : ℝ) / (Nat.totient (r i) : ℝ) ≤ 1 := by
  classical
  by_cases hsq : ∀ i, Squarefree (r i)
  · have hφpos : ∀ i, (0 : ℝ) < (Nat.totient (r i) : ℝ) := fun i ↦ by
      exact_mod_cast Nat.totient_pos.mpr (hr i)
    have habs : |∏ i, ((μ (r i) : ℝ) * (g (r i) : ℝ))| ≤ ∏ i, (g (r i) : ℝ) := by
      rw [Finset.abs_prod]
      refine Finset.prod_le_prod (fun i _ ↦ abs_nonneg _) fun i _ ↦ ?_
      rw [abs_mul, Nat.abs_cast]
      refine mul_le_of_le_one_left (by positivity) ?_
      rw [← Int.cast_abs]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right habs (by positivity))
      (by positivity)).trans ?_
    rw [one_div, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib,
        ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ m)]
    have hgm : g (r m) = 1 := by
      rw [hrm]; exact ArithmeticFunction.isMultiplicative_detotient.map_one
    have hφm : Nat.totient (r m) = 1 := by rw [hrm]; simp
    rw [hgm, hφm]
    push_cast
    rw [mul_assoc, ← Finset.prod_mul_distrib]
    ring_nf
    refine Finset.prod_le_one (fun i _ ↦ by positivity) fun i _ ↦ ?_
    have hφ : (0 : ℝ) < (Nat.totient (r i) : ℝ) := hφpos i
    rw [inv_pow, mul_assoc, mul_comm ((Nat.totient (r i) : ℝ) ^ 2)⁻¹ _, ← mul_assoc,
      ← div_eq_mul_inv, div_le_one (by positivity)]
    exact gMaynard_cast_mul_self_le_totient_sq (hsq i)
  · obtain ⟨i₀, hi₀⟩ := not_forall.mp hsq
    have hz : ∏ i, ((μ (r i) : ℝ) * (g (r i) : ℝ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i₀) (by
        rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hi₀]; simp)
    rw [hz]; simp

/-- **Termwise reduction of the off-diagonal kernel.**  If the divisor tuple `a` factors as
`a i = r i * b i` with `φ(a i) = φ(r i) φ(b i)`, then the `offDiagKernel` summand at `a` is at most
the pure `b`-weight `1 / φ(b m) * ∏_{i ≠ m} 1 / φ(b i) ^ 2`: the `r` -part is exactly the prefactor
bounded by `offdiag_prefactor_le_one`. -/
private theorem offDiagKernel_term_le {k : ℕ} (m : Fin k) (r b a : Fin k → ℕ)
    (hr : ∀ i, 0 < r i) (hrm : r m = 1) (hbpos : ∀ i, 0 < b i)
    (hphi : ∀ i, Nat.totient (a i) = Nat.totient (r i) * Nat.totient (b i)) :
    |∏ i, ((μ (r i) : ℝ) * (g (r i) : ℝ))| * ((1 / (∏ i, (Nat.totient (a i) : ℝ))) *
          ∏ i ∈ Finset.univ.erase m, (r i : ℝ) / (Nat.totient (a i) : ℝ)) ≤
      (1 / (Nat.totient (b m) : ℝ)) *
        ∏ i ∈ Finset.univ.erase m, (1 / (Nat.totient (b i) : ℝ) ^ 2) := by
  classical
  set Pr := |∏ i, ((μ (r i) : ℝ) * (g (r i) : ℝ))|
  have hphirw : ∀ i, (Nat.totient (a i) : ℝ) =
      (Nat.totient (r i) : ℝ) * (Nat.totient (b i) : ℝ) := fun i ↦ by exact_mod_cast hphi i
  have hbposR : ∀ i, (0 : ℝ) < (Nat.totient (b i) : ℝ) := fun i ↦ by
    exact_mod_cast Nat.totient_pos.mpr (hbpos i)
  set prefac := Pr * (1 / ∏ i, (Nat.totient (r i) : ℝ)) *
      ∏ i ∈ Finset.univ.erase m, (r i : ℝ) / (Nat.totient (r i) : ℝ) with hprefac
  set bfac := (1 / ∏ i, (Nat.totient (b i) : ℝ)) *
      ∏ i ∈ Finset.univ.erase m, (1 / (Nat.totient (b i) : ℝ)) with hbfac
  have hbfac_nn : 0 ≤ bfac := by rw [hbfac]; positivity
  have hLHSeq : Pr * ((1 / (∏ i, (Nat.totient (a i) : ℝ))) *
        ∏ i ∈ Finset.univ.erase m, (r i : ℝ) / (Nat.totient (a i) : ℝ)) = prefac * bfac := by
    have h1 : (∏ i, (Nat.totient (a i) : ℝ)) =
        (∏ i, (Nat.totient (r i) : ℝ)) * (∏ i, (Nat.totient (b i) : ℝ)) := by
      rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl fun i _ ↦ hphirw i
    have h2 : (∏ i ∈ Finset.univ.erase m, (r i : ℝ) / (Nat.totient (a i) : ℝ)) =
        (∏ i ∈ Finset.univ.erase m, (r i : ℝ) / (Nat.totient (r i) : ℝ)) *
          (∏ i ∈ Finset.univ.erase m, (1 / (Nat.totient (b i) : ℝ))) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      rw [hphirw i]; field_simp
    rw [hprefac, hbfac, h1, h2]
    field_simp
  have hbfac_eq : bfac = (1 / (Nat.totient (b m) : ℝ)) *
      ∏ i ∈ Finset.univ.erase m, (1 / (Nat.totient (b i) : ℝ) ^ 2) := by
    have e1 : (1 / ∏ i, (Nat.totient (b i) : ℝ)) = (1 / (Nat.totient (b m) : ℝ)) *
        ∏ i ∈ Finset.univ.erase m, (1 / (Nat.totient (b i) : ℝ)) := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ m)]
      simp [one_div, mul_comm]
    rw [hbfac, e1, mul_assoc, ← Finset.prod_mul_distrib]
    exact congrArg _ (Finset.prod_congr rfl fun i _ ↦ by rw [sq]; field_simp)
  rw [hLHSeq, ← hbfac_eq]
  exact mul_le_of_le_one_left hbfac_nn (offdiag_prefactor_le_one m r hr hrm)

/-- Reduction to the one-dimensional weights: for `2 ≤ k` and positive `r` with `r m = 1`,
`offDiagKernel W R m r ≤ (k - 1) * sumA W R * sumT W R * sumB W R ^ (k - 2)`. -/
theorem offDiagKernel_le_reduction {k : ℕ} (hk : 2 ≤ k) (W : ℕ) (R : ℝ)
    (m : Fin k) (r : Fin k → ℕ) (hr : ∀ i, 0 < r i) (hrm : r m = 1) :
    offDiagKernel W R m r ≤ (k - 1 : ℝ) * sumA W R * sumT W R * sumB W R ^ (k - 2) := by
  classical
  set Pr := |∏ i, ((μ (r i) : ℝ) * (g (r i) : ℝ))|
  have hSfin : {a : Fin k → ℕ | OffDiag m r a ∧ a ∈ Finset.permissibleSupport k ⌊R⌋₊ W}.Finite :=
    (Finset.permissibleSupport k ⌊R⌋₊ W).finite_toSet.subset fun _ ha ↦ ha.2
  set t := hSfin.toFinset
  have hmemt : ∀ x, x ∈ t ↔ (OffDiag m r x ∧ x ∈ Finset.permissibleSupport k ⌊R⌋₊ W) := fun x ↦
    hSfin.mem_toFinset
  have hKER : (∑ᶠ (a : Fin k → ℕ) (_ : OffDiag m r a ∧ a ∈ Finset.permissibleSupport k ⌊R⌋₊ W),
      (1 / (∏ i, (Nat.totient (a i) : ℝ))) *
        ∏ i ∈ Finset.univ.erase m, (r i : ℝ) / (Nat.totient (a i) : ℝ)) =
      ∑ a ∈ t, (1 / (∏ i, (Nat.totient (a i) : ℝ))) *
        ∏ i ∈ Finset.univ.erase m, (r i : ℝ) / (Nat.totient (a i) : ℝ) := by
    apply finsum_cond_eq_sum_of_cond_iff
    intro a _
    rw [hmemt]
  unfold offDiagKernel
  rw [hKER, Finset.mul_sum]
  have hdvd_t : ∀ a ∈ t, ∀ i, r i ∣ a i := fun a ha i ↦ ((hmemt a).1 ha).1.1 i
  have hapos_t : ∀ a ∈ t, ∀ i, 0 < a i := fun a ha i ↦
    Nat.pos_of_ne_zero ((Finset.mem_permissibleSupport_iff'.mp ((hmemt a).1 ha).2).1 i)
  set bfun : (Fin k → ℕ) → (Fin k → ℕ) := fun a i ↦ a i / r i with hbfun
  have hbmul : ∀ a ∈ t, ∀ i, a i = r i * bfun a i := fun a ha i ↦ by
    simp only [hbfun]; rw [Nat.mul_div_cancel' (hdvd_t a ha i)]
  have hbpos_t : ∀ a ∈ t, ∀ i, 0 < bfun a i := fun a ha i ↦ by
    simp only [hbfun]
    exact Nat.div_pos (Nat.le_of_dvd (hapos_t a ha i) (hdvd_t a ha i)) (hr i)
  have hcop : ∀ a ∈ t, ∀ i, Nat.Coprime (r i) (bfun a i) := fun a ha i ↦
    (Nat.squarefree_mul_iff.mp (by
      rw [← hbmul a ha i]
      exact (Finset.mem_permissibleSupport_iff.mp ((hmemt a).1 ha).2).2.2.squarefree_of_dvd
        (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))).1
  have hphi : ∀ a ∈ t, ∀ i,
      Nat.totient (a i) = Nat.totient (r i) * Nat.totient (bfun a i) := fun a ha i ↦ by
    conv_lhs => rw [hbmul a ha i]
    exact Nat.totient_mul (hcop a ha i)
  have term_bound : ∀ a ∈ t, Pr * ((1 / (∏ i, (Nat.totient (a i) : ℝ))) *
          ∏ i ∈ Finset.univ.erase m, (r i : ℝ) / (Nat.totient (a i) : ℝ)) ≤
        (1 / (Nat.totient (bfun a m) : ℝ)) *
            ∏ i ∈ Finset.univ.erase m, (1 / (Nat.totient (bfun a i) : ℝ) ^ 2) := fun a ha ↦
    offDiagKernel_term_le m r (bfun a) a hr hrm (hbpos_t a ha) (hphi a ha)
  set gfun : (Fin k → ℕ) → ℝ := fun d ↦ (1 / (Nat.totient (d m) : ℝ)) *
      ∏ i ∈ Finset.univ.erase m, (1 / (Nat.totient (d i) : ℝ) ^ 2) with hgfun
  have hgfun_nn : ∀ d, 0 ≤ gfun d := fun d ↦ by simp only [hgfun]; positivity
  have step1 : (∑ a ∈ t, Pr * ((1 / (∏ i, (Nat.totient (a i) : ℝ))) *
        ∏ i ∈ Finset.univ.erase m, (r i : ℝ) / (Nat.totient (a i) : ℝ))) ≤
      ∑ a ∈ t, gfun (bfun a) :=
    Finset.sum_le_sum fun a ha ↦ by simp only [hgfun]; exact term_bound a ha
  have hInj : Set.InjOn bfun (t : Set (Fin k → ℕ)) := fun a ha b hb hab ↦ funext fun i ↦ by
    rw [hbmul a (Finset.mem_coe.mp ha) i, hbmul b (Finset.mem_coe.mp hb) i, congrFun hab i]
  have step2 : (∑ a ∈ t, gfun (bfun a)) = ∑ d ∈ Finset.image bfun t, gfun d :=
    (Finset.sum_image (fun x hx y hy ↦ hInj (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy))).symm
  set S := Sset W R with hS
  set S' := S.filter (fun n ↦ n ≠ 1) with hS'
  set V : Fin k → Finset (Fin k → ℕ) :=
    fun j ↦ Fintype.piFinset (fun i ↦ if i = j then S' else S) with hV
  have himg_sub : Finset.image bfun t ⊆ (Finset.univ.erase m).biUnion V := by
    intro d hd
    obtain ⟨a, hat, rfl⟩ := Finset.mem_image.mp hd
    have ha := (hmemt a).1 hat
    obtain ⟨-, j, hjm, hjne⟩ := ha.1
    obtain ⟨hlt, hcop, hsq⟩ := Finset.mem_permissibleSupport_iff.mp ha.2
    have hcoordS : ∀ i, bfun a i ∈ S := fun i ↦ by
      have hbdvd_tp : bfun a i ∣ ∏ i, a i :=
        dvd_trans ⟨r i, by rw [hbmul a hat i]; ring⟩ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
      rw [hS, Sset, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hbpos_t a hat i, (Nat.le_of_dvd
          (Finset.prod_pos fun i _ ↦ hapos_t a hat i) hbdvd_tp).trans hlt⟩,
        hsq.squarefree_of_dvd hbdvd_tp, Nat.Coprime.coprime_dvd_left hbdvd_tp hcop⟩
    refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_erase.mpr ⟨hjm, Finset.mem_univ j⟩, ?_⟩
    rw [hV]
    refine Fintype.mem_piFinset.mpr fun i ↦ ?_
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, hS', Finset.mem_filter]
      exact ⟨hcoordS i, fun hbj1 ↦ hjne (by rw [hbmul a hat i, hbj1, mul_one])⟩
    · rw [if_neg hij]; exact hcoordS i
  set Fcoord : Fin k → ℕ → ℝ :=
    fun i n ↦ if i = m then (1 / (Nat.totient n : ℝ)) else (1 / (Nat.totient n : ℝ) ^ 2)
    with hFcoord
  have hgfun_prod : ∀ d, gfun d = ∏ i, Fcoord i (d i) := fun d ↦ by
    rw [hgfun, ← Finset.mul_prod_erase Finset.univ (fun i ↦ Fcoord i (d i)) (Finset.mem_univ m),
      hFcoord]
    simp only [↓reduceIte]
    congr 1
    exact Finset.prod_congr rfl fun i hi ↦ by rw [if_neg (Finset.mem_erase.mp hi).1]
  have hfact_j : ∀ j ∈ Finset.univ.erase m, (∑ d ∈ V j, gfun d) =
      sumA W R * sumT W R * sumB W R ^ (k - 2) := by
    intro j hj
    obtain ⟨hjm, -⟩ := Finset.mem_erase.mp hj
    simp only [hgfun_prod, hV]
    rw [← Finset.prod_univ_sum (fun i ↦ if i = j then S' else S) fun i n ↦ Fcoord i n]
    set c : Fin k → ℝ := fun i ↦ ∑ n ∈ (if i = j then S' else S), Fcoord i n with hc
    have hcm : c m = sumA W R := by
      rw [hc]; simp only [if_neg (Ne.symm hjm), hFcoord, ↓reduceIte]; rw [sumA, hS]
    have hcj : c j = sumT W R := by
      rw [hc]; simp only [↓reduceIte, hFcoord, if_neg hjm]; rw [sumT, hS', hS]
    have hcother : ∀ i ∈ (Finset.univ.erase m).erase j, c i = sumB W R := by
      intro i hi
      rw [Finset.mem_erase, Finset.mem_erase] at hi
      obtain ⟨hij, him, -⟩ := hi
      rw [hc]; simp only [if_neg hij, hFcoord, if_neg him]; rw [sumB, hS]
    have hsplit : (∏ i, c i) = c m * (c j * ∏ i ∈ (Finset.univ.erase m).erase j, c i) := by
      rw [← Finset.mul_prod_erase Finset.univ c (Finset.mem_univ m), ← Finset.mul_prod_erase
        (Finset.univ.erase m) c (Finset.mem_erase.mpr ⟨hjm, Finset.mem_univ j⟩)]
    have hcard : #((Finset.univ.erase m).erase j) = k - 2 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hjm, Finset.mem_univ j⟩),
          Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ, Fintype.card_fin]
      omega
    rw [hsplit, hcm, hcj, Finset.prod_congr rfl hcother, Finset.prod_const, hcard]
    ring
  have step3 : (∑ d ∈ Finset.image bfun t, gfun d) ≤ ∑ j ∈ Finset.univ.erase m, ∑ d ∈ V j, gfun d :=
    (Finset.sum_le_sum_of_subset_of_nonneg himg_sub fun i _ _ ↦ hgfun_nn i).trans
      (Finset.sum_biUnion_le _ V gfun fun y ↦ hgfun_nn y)
  have hconst : (∑ j ∈ Finset.univ.erase m, ∑ d ∈ V j, gfun d) =
      (k - 1 : ℝ) * sumA W R * sumT W R * sumB W R ^ (k - 2) := by
    rw [Finset.sum_congr rfl hfact_j, Finset.sum_const,
        Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ k)]
    push_cast
    ring
  exact step1.trans (step2.trans_le (step3.trans_eq hconst))

end

end MaynardOffDiagonal

end PrimeGaps
