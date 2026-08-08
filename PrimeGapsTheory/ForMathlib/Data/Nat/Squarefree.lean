/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Nat.Squarefree


/-! # Squarefree numbers -/

@[expose] public section

open Finset

namespace Nat

theorem squarefree_prod_iff {ι : Type*} {s : Finset ι} {f : ι → ℕ} :
    Squarefree (∏ i ∈ s, f i) ↔ (∀ i ∈ s, Squarefree (f i)) ∧
      Set.Pairwise s (Function.onFun Coprime f) := by
  refine ⟨fun h ↦ ⟨fun i hi ↦ h.squarefree_of_dvd <| dvd_prod_of_mem _ hi, fun i hi j hj hij ↦ ?_⟩,
    fun h ↦ squarefree_prod_of_pairwise_isCoprime ?_ h.1⟩
  · refine coprime_of_squarefree_mul <| h.squarefree_of_dvd ?_
    classical rw [← mul_prod_erase _ _ hi]
    exact mul_dvd_mul_left _ <| dvd_prod_of_mem _ <| by grind
  · convert h.2
    ext
    rw [coprime_iff_isRelPrime]

end Nat
