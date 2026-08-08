/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Nat.Totient
public import PrimeGapsTheory.ForMathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Common decoupling domains

Defines the tuple domains and restricted-coprimality condition shared by the first- and
second-moment sieve arguments, together with the common Möbius sum over the off-diagonal domain.
-/

@[expose] public section

open scoped ArithmeticFunction.Moebius

open scoped BigOperators

namespace PrimeGaps
namespace LemS1RestrictSij

/-- The weight `lam: (Fin k → ℕ) → ℝ` has positive, pairwise-coprime support if, whenever
`lam t ≠ 0`, every coordinate `t i` is positive and any two distinct coordinates are coprime.

This is weaker than `Finsupp.HasPermissibleSupport`: it does not assert a product bound,
squarefreeness, or coprimality with the sieve modulus.
-/
def HasPositivePairwiseCoprimeSupport {k : ℕ} (lam : (Fin k → ℕ) → ℝ) : Prop :=
  ∀ t : Fin k → ℕ, lam t ≠ 0 → (∀ i, 0 < t i) ∧ (∀ i j, i ≠ j → Nat.gcd (t i) (t j) = 1)

/-- The per-entry finite domain for the off-diagonal variable `s i j`. On the diagonal (`i = j`) it
is the singleton `{1}`; off the diagonal it is the positive divisors of `gcd (d i) (e j)`. -/
def sEntryDomain {k : ℕ} (d e : Fin k → ℕ) (i j : Fin k) : Finset ℕ :=
  if i = j then {1} else (Nat.gcd (d i) (e j)).divisors

/-- `u: Fin k → ℕ` ranges over tuples with `u i ∈ divisors (gcd (d i) (e i))`. -/
def uDomain {k : ℕ} (d e : Fin k → ℕ) : Finset (Fin k → ℕ) :=
  Fintype.piFinset (fun i ↦ (Nat.gcd (d i) (e i)).divisors)

/-- `s: Fin k → Fin k → ℕ` ranges over tuples with `s i j ∈ sEntryDomain d e i j`. -/
def sDomain {k : ℕ} (d e : Fin k → ℕ) : Finset (Fin k → Fin k → ℕ) :=
  Fintype.piFinset (fun i ↦ Fintype.piFinset (fun j ↦ sEntryDomain d e i j))

/-- A configuration `(u, s)` is restricted-coprime if every off-diagonal `s i j` is coprime to
the two adjacent `u` entries and to the other entries in its row and column. -/
def RestrictedCoprime {k : ℕ} (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ) : Prop :=
  ∀ i j : Fin k, i ≠ j → Nat.gcd (s i j) (u i) = 1 ∧ Nat.gcd (s i j) (u j) = 1 ∧
    (∀ a : Fin k, a ≠ j → a ≠ i → Nat.gcd (s i j) (s i a) = 1) ∧
    (∀ b : Fin k, b ≠ i → b ≠ j → Nat.gcd (s i j) (s b j) = 1)

/-- The restriction predicate is decidable, so it can be used in a `Finset.filter`. -/
instance {k : ℕ} (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ) : Decidable (RestrictedCoprime u s) := by
  unfold RestrictedCoprime
  infer_instance

/-- Summing the off-diagonal Möbius product over `sDomain` gives the cross-coprimality
indicator. -/
theorem msum {k : ℕ} (d e : Fin k → ℕ) : (∑ s ∈ sDomain d e,
        ∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
          ((μ (s p.1 p.2) : ℤ) : ℝ)) =
    if (∀ i j, i ≠ j → Nat.Coprime (d i) (e j)) then 1 else 0 := by
  have hbody : ∀ s : Fin k → Fin k → ℕ, (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
          ((μ (s p.1 p.2) : ℤ) : ℝ)) =
      ∏ i, ∏ j, (if i ≠ j then ((μ (s i j) : ℤ) : ℝ) else 1) := by
    intro s
    have hoff : (Finset.univ.offDiag : Finset (Fin k × Fin k)) =
        Finset.univ.filter (fun p ↦ p.1 ≠ p.2) := by
      ext p
      simp [Finset.mem_offDiag]
    rw [hoff, Finset.prod_filter, Fintype.prod_prod_type]
  simp_rw [hbody]
  have hinner : ∀ i : Fin k, (∑ g ∈ Fintype.piFinset (fun j ↦ sEntryDomain d e i j),
          ∏ j, (if i ≠ j then ((μ (g j) : ℤ) : ℝ) else 1)) =
      ∏ j, (if i ≠ j then (if Nat.Coprime (d i) (e j) then (1 : ℝ) else 0) else 1) := by
    intro i
    rw [← Finset.prod_univ_sum (fun j ↦ sEntryDomain d e i j)
          (fun j x ↦ if i ≠ j then ((μ x : ℤ) : ℝ) else 1)]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    by_cases hij : i = j
    · subst hij
      simp [sEntryDomain]
    · simp only [if_pos hij, sEntryDomain, if_neg hij]
      exact ArithmeticFunction.sum_divisors_coe_moebius (α := ℝ)
  simp only [sDomain]
  rw [← Finset.prod_univ_sum (fun i ↦ Fintype.piFinset (fun j ↦ sEntryDomain d e i j))
        (fun i g ↦ ∏ j, (if i ≠ j then ((μ (g j) : ℤ) : ℝ) else 1))]
  simp_rw [hinner]
  have hfac : ∀ i j : Fin k,
      (if i ≠ j then (if Nat.Coprime (d i) (e j) then (1 : ℝ) else 0) else 1) =
      (if (i ≠ j → Nat.Coprime (d i) (e j)) then (1 : ℝ) else 0) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [if_pos hij]
      by_cases hc : Nat.Coprime (d i) (e j)
      · rw [if_pos hc, if_pos (fun _ ↦ hc)]
      · rw [if_neg hc, if_neg (fun h ↦ hc (h hij))]
  simp_rw [hfac]
  by_cases h : ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)
  · rw [if_pos h]
    exact Finset.prod_eq_one fun i _ ↦ Finset.prod_eq_one fun j _ ↦ if_pos (h i j)
  · rw [if_neg h]
    simp only [not_forall] at h
    obtain ⟨i, j, hij, hnc⟩ := h
    refine Finset.prod_eq_zero (Finset.mem_univ i) (Finset.prod_eq_zero (Finset.mem_univ j) ?_)
    rw [if_neg (fun hcon ↦ hnc (hcon hij))]

end LemS1RestrictSij
end PrimeGaps
