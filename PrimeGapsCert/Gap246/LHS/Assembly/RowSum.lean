/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.LHS.Assembly.Transform
public import PrimeGapsCert.Gap246.LHS.ConcreteSound.Rows

/-! # Sum of the complete packed sparse LHS rows -/

@[expose] public section

namespace PrimeGaps.Gap246

/-- The checked LHS rows cover the complete symmetric LHS quadratic form. -/
theorem certLhsRowSum :
    (∑ row : Fin 138, certLhsRow row) =
      preEpsWitnessInt.lhsPairWithTablesSumSymmetric certFactorTables := by
  simpa only [certLhsRow] using
    preEpsWitnessInt.sum_lhsDegreeSymmetricRow certFactorTables certLhsPartition
      certLhsPartition_valid certLhsTransform certLhsTransform_complete preMomentTop_comm

end PrimeGaps.Gap246
