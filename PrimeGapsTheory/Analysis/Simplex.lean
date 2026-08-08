/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import PrimeGapsTheory.Tactic.PaperTag

/-! # Scaled standard simplex

The scaled standard simplex `𝓡(k, s)` of nonnegative vectors in `EuclideanSpace ℝ (Fin k)` whose
coordinates sum to at most `s`, together with its closedness and compactness.

## Main definitions

* `EuclideanSpace.scaledStdSimplex`: the simplex, with scoped notation `𝓡(k, s)` and `𝓡 k`.
-/

@[expose] public section

open EuclideanSpace Finset Metric

local notation "ES(" 𝕜:65 ", " k:65 ")" => EuclideanSpace 𝕜 (Fin k)

namespace EuclideanSpace

/-- The set of nonnegative vectors whose coordinate sum is at most `s`. -/
@[pg_tag "bg246" "def_shr"]
def scaledStdSimplex (k : ℕ) (s : ℝ) : Set ES(ℝ, k) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ s}

/-- The notation `𝓡(k, s)` denotes the scaled standard simplex `scaledStdSimplex k s`. -/
@[pg_tag "bg246" "def_shr"]
scoped[PrimeGaps] notation "𝓡(" k ", " s ")" => scaledStdSimplex k s

/-- The notation `𝓡 k` denotes the standard simplex `scaledStdSimplex k 1`. -/
@[pg_tag "bg246" "def_simplex"]
scoped[PrimeGaps] notation "𝓡" k:max => scaledStdSimplex k 1

open scoped PrimeGaps

@[pg_tag "bg246" "def_simplex", pg_tag "bg246" "def_shr", simp]
theorem mem_scaledStdSimplex_iff {k : ℕ} {s : ℝ} {x : ES(ℝ, k)} :
    x ∈ 𝓡(k, s) ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ s := Set.mem_ofPred

theorem scaledStdSimplex_subset_closedBall {k : ℕ} {s : ℝ} :
    𝓡(k, s) ⊆ closedBall 0 s := fun x hx ↦ by
  simp_rw [mem_closedBall_zero_iff, norm_eq, Real.norm_eq_abs, abs_of_nonneg (hx.1 _)]
  grw [sum_sq_le_sq_sum_of_nonneg fun i _ ↦ hx.1 i]
  simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (sum_nonneg fun i _ ↦ hx.1 i)] using hx.2

theorem isClosed_scaledStdSimplex {k : ℕ} {s : ℝ} : IsClosed (𝓡(k, s)) := by
  rw [scaledStdSimplex, Set.ofPred_and, Set.ofPred_forall]
  refine .inter (isClosed_iInter fun _ ↦ isClosed_le ?_ ?_) <| isClosed_le ?_ ?_ <;> fun_prop

theorem isCompact_scaledStdSimplex {k : ℕ} {s : ℝ} : IsCompact (𝓡(k, s)) :=
  isCompact_of_isClosed_isBounded isClosed_scaledStdSimplex <|
    isBounded_closedBall.subset scaledStdSimplex_subset_closedBall

end EuclideanSpace
