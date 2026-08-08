module

public import PrimeGapsCert.Gap246.RHS.Data.ExpectedWeightCheckpoints
public import PrimeGapsCert.Gap246.RHS.Data.SourceWeightCheckpoints
public import PrimeGapsCert.Gap246.RHS.Defs

/-! # Low-memory block propositions for the packed RHS weight certificate -/

@[expose] public section

namespace PrimeGaps.Gap246

/-- The raw comparison for one bounded source-label weight block. -/
@[reducible] def CertRhsSourceWeightBlockCorrect (block : Nat) : Prop :=
  cert246Data.rhsSourceWeightCheckpointBlockCheck 1295 25 10 1023 9 511 128
    (2 ^ 128 - 1) cert246Data.rhsWeightLaneWidth cert246Data.sigEnc
    cert246Data.labelEnc cert246Data.rhsSourceWeightBlockSize block
    cert246Data.rhsSourceLocationT cert246Data.coeffMag
    cert246Data.rhsSourceWeightBoundCheckpoint
    cert246Data.rhsSourceWeightPositiveCheckpoint
    cert246Data.rhsSourceWeightNegativeCheckpoint = true

/-- The raw comparison for one bounded stored-feature weight block. -/
@[reducible] def CertRhsExpectedWeightBlockCorrect (block : Nat) : Prop :=
  cert246Data.rhsExpectedWeightCheckpointBlockCheck 1504 8 255 256 (2 ^ 256 - 1)
    cert246Data.rhsWeightLaneWidth cert246Data.rhsExpectedWeightBlockSize block
    cert246Data.rhsWeightT cert246Data.rhsExpectedWeightBoundCheckpoint
    cert246Data.rhsExpectedWeightPositiveCheckpoint
    cert246Data.rhsExpectedWeightNegativeCheckpoint = true

/-- The raw carry-free balance check after all independently verified blocks are merged. -/
@[reducible] def CertRhsWeightCheckpointBalanceCorrect : Prop :=
  cert246Data.rhsWeightCheckpointBalanceCheck cert246Data.rhsWeightLaneWidth
    (1295 / cert246Data.rhsSourceWeightBlockSize)
    (1504 / cert246Data.rhsExpectedWeightBlockSize)
    cert246Data.rhsSourceWeightBoundCheckpoint
    cert246Data.rhsSourceWeightPositiveCheckpoint
    cert246Data.rhsSourceWeightNegativeCheckpoint
    cert246Data.rhsExpectedWeightBoundCheckpoint
    cert246Data.rhsExpectedWeightPositiveCheckpoint
    cert246Data.rhsExpectedWeightNegativeCheckpoint = true

end PrimeGaps.Gap246
