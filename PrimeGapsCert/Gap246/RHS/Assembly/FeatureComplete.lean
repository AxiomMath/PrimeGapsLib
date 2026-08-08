/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.RHS.Assembly.KeyChecks
public import PrimeGapsCert.Gap246.RHS.FeatureSound

/-! # Completion of the packed sparse RHS features -/

@[expose] public section

namespace PrimeGaps.Gap246

/-- The packed feature keys and the canonical weight encoding certify every RHS feature. -/
theorem certRhsFeatures_complete :
    RhsMarginalFeature.Correct preEpsWitnessInt certFactorTables certRhsFeature :=
  certRhsFeatures_of_keyChecks certRhsFeatureKeyChecks_complete

end PrimeGaps.Gap246
