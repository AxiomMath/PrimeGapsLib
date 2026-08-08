/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.S1.Decoupling

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Restricting off-diagonal variables

Restricts the first-moment decoupled sum to the required off-diagonal coprimality conditions.

## Main definitions

* `SigmaRestr`: The restricted decoupled first-moment sum.

## Main results

* `lem_S1_restrict_sij`: Identifies the full and restricted decoupled sums.
-/

@[expose] public section

namespace PrimeGaps
namespace LemS1RestrictSij

open scoped BigOperators
open ArithmeticFunction

/-- The restricted sum `Σ_restr`: the same sum as `Σ_full` but with the configurations restricted
to the `RestrictedCoprime` ones.
-/
@[pg_tag "bg246" "not_starsum"]
noncomputable def SigmaRestr {k : ℕ} (D : Finset (Fin k → ℕ)) (lam : (Fin k → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ D, ∑ u ∈ uDomain d e,
    ∑ s ∈ {s ∈ (sDomain d e) | RestrictedCoprime u s}, T lam u s d e

/-- `RestrictedCoprime u s` from divisibility plus pairwise coprimality of the divisor tuples.
If each `u i` divides both `d i` and `e i`, each off-diagonal `s i j` divides `d i` and `e j`, and
the coordinates of `d` and of `e` are separately pairwise coprime, then all four coprimalities
defining `RestrictedCoprime u s` hold. Every way of landing in the `(u, s)` domains factors through
this lemma; only the source of the divisibilities differs. -/
theorem restrictedCoprime_of_dvd {k : ℕ} {d e u : Fin k → ℕ} {s : Fin k → Fin k → ℕ}
    (hudvd : ∀ i, u i ∣ d i ∧ u i ∣ e i)
    (hsdvd : ∀ i j, i ≠ j → s i j ∣ d i ∧ s i j ∣ e j)
    (hdcop : ∀ i j, i ≠ j → (d i).Coprime (d j))
    (hecop : ∀ i j, i ≠ j → (e i).Coprime (e j)) :
    RestrictedCoprime u s := by
  intro i j hij
  exact ⟨((hecop j i hij.symm).coprime_dvd_right (hudvd i).2).coprime_dvd_left (hsdvd i j hij).2,
    ((hdcop i j hij).coprime_dvd_right (hudvd j).1).coprime_dvd_left (hsdvd i j hij).1,
    fun a haj hai ↦ ((hecop j a haj.symm).coprime_dvd_right
      (hsdvd i a hai.symm).2).coprime_dvd_left (hsdvd i j hij).2,
    fun b hbi hbj ↦ ((hdcop i b hbi.symm).coprime_dvd_right
      (hsdvd b j hbj).1).coprime_dvd_left (hsdvd i j hij).1⟩

/-- Pointwise coprimalities of the `s i j`. Fix a configuration `(u, s)` with induced divisor
tuples `d, e` (so `u ∈ uDomain d e` and `s ∈ sDomain d e`, giving `u i ∣ d i, e i` and
`s i j ∣ d i, e j`) contributing a nonzero summand — `T lam u s d e ≠ 0`, forcing
`lam d * lam e ≠ 0`. Then, using the squarefree pairwise-coprime support of `lam`, the four
coprimalities defining `RestrictedCoprime` hold.
-/
@[pg_tag "bg246" "lem_S1_sij_coprimality"]
theorem lem_S1_sij_coprimality {k : ℕ} (lam : (Fin k → ℕ) → ℝ)
    (hlam : HasPositivePairwiseCoprimeSupport lam)
    (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ) (d e : Fin k → ℕ)
    (hu : u ∈ uDomain d e) (hs : s ∈ sDomain d e)
    (hTne : T lam u s d e ≠ 0) :
    RestrictedCoprime u s := by
  have hlamprod : lam d * lam e ≠ 0 := fun h0 ↦ hTne (by unfold T; rw [h0]; ring)
  obtain ⟨-, hdcop⟩ := hlam d (left_ne_zero_of_mul hlamprod)
  obtain ⟨-, hecop⟩ := hlam e (right_ne_zero_of_mul hlamprod)
  have hu_mem : ∀ i, u i ∈ (Nat.gcd (d i) (e i)).divisors := fun i ↦ by
    simpa [uDomain] using (Fintype.mem_piFinset).mp hu i
  have hs_mem : ∀ i j, s i j ∈ sEntryDomain d e i j :=
    fun i j ↦ (Fintype.mem_piFinset).mp ((Fintype.mem_piFinset).mp hs i) j
  have hudvd : ∀ i, u i ∣ d i ∧ u i ∣ e i :=
    fun i ↦ Nat.dvd_gcd_iff.mp ((Nat.mem_divisors).mp (hu_mem i)).1
  have hsdvd : ∀ i j, i ≠ j → s i j ∣ d i ∧ s i j ∣ e j := by
    intro i j hij
    have hmem := hs_mem i j
    rw [sEntryDomain, if_neg hij] at hmem
    exact Nat.dvd_gcd_iff.mp ((Nat.mem_divisors).mp hmem).1
  exact restrictedCoprime_of_dvd hudvd hsdvd hdcop hecop

/-- For any fixed finite set `D` of divisor tuples and any weight `lam` with positive,
pairwise-coprime support,
restricting the off-diagonal Moebius variables `s i j` to be coprime to `u i`, `u j`, `s i a` (for
`a ≠ j`) and `s b j` (for `b ≠ i`) does not change the value of the sum: `Σ_restr = Σ_full`.
-/
@[pg_tag "bg246" "lem_S1_restrict_sij"]
theorem lem_S1_restrict_sij {k : ℕ} (D : Finset (Fin k → ℕ)) (lam : (Fin k → ℕ) → ℝ)
    (hlam : HasPositivePairwiseCoprimeSupport lam) :
    SigmaRestr D lam = SigmaFull D lam := by
  unfold SigmaRestr SigmaFull
  refine Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun e _ ↦
    Finset.sum_congr rfl fun u hu ↦ Finset.sum_filter_of_ne fun s hs hTne ↦
      lem_S1_sij_coprimality lam hlam u s d e hu hs hTne

end LemS1RestrictSij

end PrimeGaps
