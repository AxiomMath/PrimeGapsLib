/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.LHS.Checks
public import PrimeGapsCert.Gap246.LHS.ConcreteSound.Rows
public import PrimeGapsCert.Meta.Batched

/-! # Completion of the packed sparse LHS rows -/

@[expose] public section

namespace PrimeGaps.Gap246

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 3000 in
/-- Every stored LHS row equals its mathematical upper-triangular degree row. -/
theorem certLhsRows_complete : ∀ row : Fin 138, certLhsStoredRow row = certLhsRow row := by
  have hrows : ∀ row : Fin 138, CertLhsRowCorrect row :=
    combine_batched_theorems% CertLhsRowCorrect 138
  intro row
  exact certLhsRowCheck_correct row (hrows row)

end PrimeGaps.Gap246
