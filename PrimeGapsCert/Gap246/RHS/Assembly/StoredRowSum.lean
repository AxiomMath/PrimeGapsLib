/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.RHS.Assembly.RowSum
public import PrimeGapsCert.Gap246.RHS.Assembly.RowsComplete

/-! # Sum of the stored packed sparse RHS rows -/

@[expose] public section

namespace PrimeGaps.Gap246

/-- The stored RHS row totals sum to the complete aggregated feature quadratic form. -/
theorem certRhsStoredRowSum :
    (∑ row : Fin 172, certRhsStoredRow row) =
      preEpsWitnessInt.rhsFeatureSum certFactorTables certRhsFeature := by
  simpa only [certRhsRows_complete] using certRhsRowSum

end PrimeGaps.Gap246
