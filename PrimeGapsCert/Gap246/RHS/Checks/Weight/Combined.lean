module

public import PrimeGapsCert.Gap246.RHS.Checks.Weight.Balance
public import PrimeGapsCert.Gap246.RHS.Checks.Weight.Expected01
public import PrimeGapsCert.Gap246.RHS.Checks.Weight.Expected02
public import PrimeGapsCert.Gap246.RHS.Checks.Weight.Expected03
public import PrimeGapsCert.Gap246.RHS.Checks.Weight.Expected04
public import PrimeGapsCert.Gap246.RHS.Checks.Weight.Source01
public import PrimeGapsCert.Gap246.RHS.Checks.Weight.Source02
public import PrimeGapsCert.Gap246.RHS.Checks.Weight.Source03
public import PrimeGapsCert.Gap246.RHS.Checks.Weight.Source04
public import PrimeGapsCert.Gap246.RHS.Checks.Weight.Source05
public import PrimeGapsCert.Gap246.RHS.Checks.Weight.Source06

import PrimeGapsCert.Meta.Batched

/-! # Combined low-memory RHS weight checks -/

set_option maxRecDepth 100000
set_option exponentiation.threshold 1000

@[expose] public section

namespace PrimeGaps.Gap246

/-- Every source-label checkpoint block passes its direct numerical comparison. -/
theorem certRhsSourceWeightBlockChecks :
    ∀ block : Fin 41, CertRhsSourceWeightBlockCorrect block :=
  combine_batched_theorems% CertRhsSourceWeightBlockCorrect 41

/-- Every stored-feature checkpoint block passes its direct numerical comparison. -/
theorem certRhsExpectedWeightBlockChecks :
    ∀ block : Fin 24, CertRhsExpectedWeightBlockCorrect block :=
  combine_batched_theorems% CertRhsExpectedWeightBlockCorrect 24

/-- The merged source and expected checkpoints satisfy the carry-free identity. -/
theorem certRhsWeightCheckpointBalance : CertRhsWeightCheckpointBalanceCorrect :=
  cert246Data.rhs_weight_checkpoint_balance_ok

end PrimeGaps.Gap246
