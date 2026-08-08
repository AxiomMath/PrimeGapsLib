/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.NumberTheory.Admissible

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Admissible finite sets

Characterizes admissibility by the number of residue classes occupied modulo each prime.

## Main results

* `lem_admissible_cardinality_char`: A finite set is admissible exactly when it occupies fewer
  than all residue classes modulo every prime.
-/

@[expose] public section

open scoped Finset

open Finset

namespace PrimeGaps

/-- A finite set `H ⊆ ℕ` is admissible iff `#{h mod p: h ∈ H} < p` for *every* prime `p`. -/
@[pg_tag "bg246" "lem_admissible_cardinality_char"]
theorem lem_admissible_cardinality_char (H : Finset ℕ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → #(H.image ((↑) : ℕ → ZMod p)) < p := by
  rw [admissible_iff_forall_prime_exists_ZMod_nequiv]
  refine forall_congr' fun p ↦ imp_congr_right fun hp ↦ ?_
  haveI : Fact p.Prime := ⟨hp⟩
  constructor
  · rintro ⟨a, ha⟩
    have hnotmem : a ∉ H.image ((↑) : ℕ → ZMod p) := by simpa [mem_image] using ha
    have hlt := card_lt_card ⟨subset_univ _, fun hsub ↦ hnotmem (hsub (mem_univ a))⟩
    rwa [card_univ, ZMod.card] at hlt
  · intro hcard
    have hlt : #(H.image ((↑) : ℕ → ZMod p)) < #(univ : Finset (ZMod p)) := by
      rwa [card_univ, ZMod.card]
    obtain ⟨a, -, ha⟩ := exists_mem_notMem_of_card_lt_card hlt
    exact ⟨a, fun h hh he ↦ ha (mem_image.mpr ⟨h, hh, he⟩)⟩

end PrimeGaps
