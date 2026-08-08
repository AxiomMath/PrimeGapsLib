/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Moments.PairDefs
public import PrimeGapsCert.Gap246.RHS.Data

/-! # Packed data for the packed sparse RHS certificate -/

@[expose] public section

namespace PrimeGaps.Gap246

/-- The raw packed-key check for one 256-entry RHS block. -/
@[reducible] def CertRhsKeysBlockCorrect (block : Nat) : Prop :=
  cert246Data.rhsKeysRangeCheck 172 272 cert246Data.rhsKeyEnc
    (block * 256) (min 6057 ((block + 1) * 256)) = true

/-- The raw location-index check for one eight-group RHS block. -/
@[reducible] def CertRhsLocationBlockCorrect (block : Nat) : Prop :=
  cert246Data.rhsLocationIndexRangeCheck 272 6057 12 4095 cert246Data.rhsKeyEnc
    cert246Data.rhsLocationT (block * 8) (min 172 ((block + 1) * 8)) = true

/-- The raw signature-bound check for one 256-feature RHS block. -/
@[reducible] def CertRhsFeatureSignatureBlockCorrect (block : Nat) : Prop :=
  cert246Data.rhsFeatureSignatureRangeCheck 272 cert246Data.rhsFeatureEnc
    (block * 256) (min 1504 ((block + 1) * 256)) = true

/-- The raw check for one 32-entry block of the stored sparse RHS transform. -/
@[reducible] def CertRhsTransformBlockCorrect (block : Nat) : Prop :=
  cert246Data.rhsTransformCheck 7 127 384 (2 ^ 384 - 1)
    cert246Data.rhsFeatureEnc cert246Data.rhsGroupEnc cert246Data.rhsKeyEnc
    8 255 256 (2 ^ 256 - 1) 7 127 512 (2 ^ 512 - 1) (2 ^ 256 - 1)
    cert246Data.rhsTransformT cert246Data.rhsWeightT cert246Data.pairT
    (block * 32) (min 6057 ((block + 1) * 32)) = true

/-- The raw complete check for one stored sparse RHS row and all of its queried support. -/
@[reducible] def CertRhsRowCorrect (row : Nat) : Prop :=
  cert246Data.rhsRowCheck 50 172 272 102 cert246Data.rhsFeatureEnc
    cert246Data.rhsGroupEnc 12 4095 7 127 384 (2 ^ 384 - 1)
    5 31 1088 (2 ^ 1088 - 1) 8 255 256 (2 ^ 256 - 1)
    6 63 832 (2 ^ 832 - 1) cert246Data.rhsLocationT
    cert246Data.rhsTransformT cert246Data.rhsRowT cert246Data.rhsWeightT
    cert246Data.rhsRadialT row (row + 1) = true

/-- The raw check for one 32-label block of marginal-feature keys. -/
@[reducible] def CertRhsFeatureKeyBlockCorrect (block : Nat) : Prop :=
  cert246Data.rhsFeatureKeysCheck 1504 25 10 1023 10 1023
    cert246Data.sigEnc cert246Data.labelEnc cert246Data.rhsFeatureEnc
    (block * 32) (min 1295 ((block + 1) * 32)) cert246Data.rhsSourceLocationT
    cert246Data.eraseTargetT = true

/-- The raw check for one 128-entry block of the flattened RHS radial recurrence table. -/
@[reducible] def CertRhsRadialBlockCorrect (block : Nat) : Prop :=
  cert246Data.rhsRadialCheck 50 25 102 6 63 832 (2 ^ 832 - 1)
    (4998 + block * 128) (min 10404 (4998 + (block + 1) * 128))
    cert246Data.rhsRadialT = true

end PrimeGaps.Gap246
