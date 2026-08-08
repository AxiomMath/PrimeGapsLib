/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.RHS.Assembly.RadialChecks
public import PrimeGapsCert.Gap246.RHS.ConcreteSound.Rows

/-! # Completion of the packed sparse RHS rows -/

@[expose] public section

namespace PrimeGaps.Gap246

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 3000 in
/-- Every stored RHS row equals its mathematical upper-triangular degree row. -/
theorem certRhsRows_complete : ∀ row : Fin 172, certRhsStoredRow row = certRhsRow row := by
  have hrows : ∀ row : Fin 172, CertRhsRowCorrect row :=
    combine_batched_theorems% CertRhsRowCorrect 172
  intro row
  exact certRhsRowCheck_correct certRhsRadialChecks_complete row (hrows row)

end PrimeGaps.Gap246
