/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Finset.Prod
import PrimeGapsTheory.Tactic.PaperTag

/-!
# Monomial basis indices

The finite set of pairs indexing the monomials
`{(1 − P₁)ᵇ · P₂ᶜ | b, c ∈ ℕ, b + 2c ≤ d}`.

## Main definitions

* `basisB`: The basis indexing set of pairs `(b, c)` with `b + 2c ≤ d`.

## Main results

* `lem_size_B11`: The identity `|basisB 11| = 42`.
-/

@[expose] public section

open scoped Finset


namespace PrimeGaps

/-- The basis indexing set of pairs `(b, c) ∈ ℕ²` with `b + 2c ≤ d`.
Cardinality is `∑_{c=0}^{⌊d/2⌋} (d − 2c + 1)`. -/
@[pg_tag "bg246" "def_basis_Bd"]
def basisB (d : ℕ) : Finset (ℕ × ℕ) :=
  {p ∈ (Finset.range (d + 1) ×ˢ Finset.range (d + 1)) | p.1 + 2 * p.2 ≤ d}

/-- `|basisB 11| = 42`. -/
@[pg_tag "bg246" "lem_size_B11"]
theorem lem_size_B11 : #(basisB 11) = 42 := by
  decide

end PrimeGaps
