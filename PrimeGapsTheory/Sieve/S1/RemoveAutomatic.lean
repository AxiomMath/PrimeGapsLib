/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Real.Basic
import PrimeGapsTheory.Tactic.PaperTag

/-!
# Automatic coprimality conditions

Removes coprimality conditions implied by the remaining first-moment constraints.

## Main results

* `lem_S1_remove_automatic`: Rewrites the first-moment sum without automatic conditions.
-/

@[expose] public section

namespace PrimeGaps

/-- On the support of `lam` (positive entries, squarefree product coprime to `W`), the extra
constraints of the full-restriction guard beyond cross-coprimality — the intra-coprimalities and
the `W` -coprimalities — are automatic, so the fully-guarded sum equals the one guarded by
`∀ i ≠ j, Nat.Coprime (d i) (e j)` alone. Squarefreeness of `∏ i, t i` forces the
intra-coprimalities; divisor-inheritance forces the `W` -coprimalities.
-/
@[pg_tag "bg246" "lem_S1_remove_automatic"]
theorem lem_S1_remove_automatic {k : ℕ} (W : ℕ) (D : Finset (Fin k → ℕ))
    (lam : (Fin k → ℕ) → ℝ) (f : (Fin k → ℕ) → (Fin k → ℕ) → ℝ)
    (hsupp : ∀ t, lam t ≠ 0 → (∀ i, 0 < t i) ∧ Squarefree (∏ i, t i) ∧ Nat.Coprime (∏ i, t i) W) :
    (∑ d ∈ D, ∑ e ∈ D,
        if ((∀ i j, i ≠ j → Nat.Coprime (d i) (e j)) ∧ (∀ i j, i ≠ j → Nat.Coprime (d i) (d j)) ∧
            (∀ i j, i ≠ j → Nat.Coprime (e i) (e j)) ∧ (∀ i, Nat.Coprime (d i) W) ∧
            (∀ i, Nat.Coprime (e i) W))
        then lam d * lam e * f d e else 0)
      =
    ∑ d ∈ D, ∑ e ∈ D, if (∀ i j, i ≠ j → Nat.Coprime (d i) (e j))
        then lam d * lam e * f d e else 0 := by
  have intra : ∀ (t : Fin k → ℕ), Squarefree (∏ i, t i) →
      ∀ i j, i ≠ j → Nat.Coprime (t i) (t j) := fun t hsq i j hij ↦
    Nat.coprime_of_squarefree_mul <| hsq.squarefree_of_dvd <| by
      rw [← Finset.prod_pair hij]
      exact Finset.prod_dvd_prod_of_subset _ _ _ (by simp)
  have wcop : ∀ (t : Fin k → ℕ), Nat.Coprime (∏ i, t i) W →
      ∀ i, Nat.Coprime (t i) W := fun t hcop i ↦
    Nat.Coprime.of_dvd_left (Finset.dvd_prod_of_mem t (Finset.mem_univ i)) hcop
  refine Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun e _ ↦ ?_
  by_cases hd : lam d = 0
  · simp [hd]
  · by_cases he : lam e = 0
    · simp [he]
    · obtain ⟨_, hdsq, hdW⟩ := hsupp d hd
      obtain ⟨_, hesq, heW⟩ := hsupp e he
      by_cases hcross : ∀ i j, i ≠ j → Nat.Coprime (d i) (e j)
      · rw [if_pos ⟨hcross, intra d hdsq, intra e hesq, wcop d hdW, wcop e heW⟩, if_pos hcross]
      · rw [if_neg (fun h ↦ hcross h.1), if_neg hcross]

end PrimeGaps
