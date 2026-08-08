/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.LHS.Data
public import PrimeGapsCert.Gap246.Moments.PairDefs

/-! # Packed data for the packed sparse LHS certificate -/

@[expose] public section

namespace PrimeGaps.Gap246

/-- The raw packed-key check for one 256-entry LHS block. -/
@[reducible] def CertLhsKeysBlockCorrect (block : Nat) : Prop :=
  cert246Data.lhsKeysRangeCheck 138 272 cert246Data.lhsKeyEnc
    (block * 256) (min 5533 ((block + 1) * 256)) = true

/-- The raw location-index check for one eight-group LHS block. -/
@[reducible] def CertLhsLocationBlockCorrect (block : Nat) : Prop :=
  cert246Data.lhsLocationIndexRangeCheck 272 5533 12 4095 cert246Data.lhsKeyEnc
    cert246Data.lhsLocationT (block * 8) (min 138 ((block + 1) * 8)) = true

/-- The raw check for one 32-entry block of the stored sparse LHS transform. -/
@[reducible] def CertLhsTransformBlockCorrect (block : Nat) : Prop :=
  cert246Data.lhsTransformCheck 7 127 320 (2 ^ 320 - 1)
    cert246Data.lhsMemberEnc cert246Data.labelEnc cert246Data.lhsGroupEnc
    cert246Data.lhsKeyEnc 9 511 128 (2 ^ 128 - 1) 7 127 512 (2 ^ 512 - 1) 256
    cert246Data.lhsTransformT cert246Data.coeffMag cert246Data.pairT
    (block * 32) (min 5533 ((block + 1) * 32)) = true

/-- The raw complete check for one stored sparse LHS row and all of its queried support. -/
@[reducible] def CertLhsRowCorrect (row : Nat) : Prop :=
  cert246Data.lhsRowCheck 138 272 51 cert246Data.lhsMemberEnc
    cert246Data.labelEnc cert246Data.lhsGroupEnc 12 4095 7 127 320
    (2 ^ 320 - 1) 5 31 1088 (2 ^ 1088 - 1) 9 511 128 (2 ^ 128 - 1)
    6 63 1024 cert246Data.lhsScalarMask cert246Data.lhsLocationT
    cert246Data.lhsTransformT cert246Data.lhsRowT cert246Data.coeffMag
    cert246Data.lhsScalarT row (row + 1) = true

end PrimeGaps.Gap246
