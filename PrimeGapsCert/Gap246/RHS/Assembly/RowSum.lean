/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.RHS.Assembly.Transform
public import PrimeGapsCert.Gap246.RHS.ConcreteSound.Rows
import PrimeGapsCert.Gap246.Certificate.MomentSound

/-! # Sum of the complete packed sparse RHS rows -/

@[expose] public section

namespace PrimeGaps.Gap246

/-- The checked RHS rows cover the complete aggregated marginal-feature quadratic form. -/
theorem certRhsRowSum :
    (∑ row : Fin 172, certRhsRow row) =
      preEpsWitnessInt.rhsFeatureSum certFactorTables certRhsFeature := by
  simpa only [certRhsRow] using
    preEpsWitnessInt.sum_rhsDegreeGroupSymmetricRowTransformed certFactorTables
      certRhsFeature certRhsPartition certRhsPartition_valid certRhsTransform
      certRhsTransform_complete preMomentPred_comm

end PrimeGaps.Gap246
