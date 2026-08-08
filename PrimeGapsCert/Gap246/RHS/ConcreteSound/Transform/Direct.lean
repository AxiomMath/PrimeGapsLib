/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.RHS.ConcreteSound.Transform.Basic


/-! # Direct RHS transform soundness -/

@[expose] public section

namespace PrimeGaps.Gap246

open Finset

/-- Concrete direct RHS transform with no dependent certificate fields in its type. -/
noncomputable def certRhsDirectTransform (group : Fin 172) (target : Fin 272) : ℤ :=
  ∑ offset : Fin (certRhsPartition.group group).size,
    (certRhsFeature (certRhsPartition.member certRhsPartition_bound group offset)).weight *
      ((certPairValue (signaturePairIndex target
        (certRhsFeature
          (certRhsPartition.member certRhsPartition_bound group offset)).signature) %
            2 ^ 256 : ℕ) : ℤ)

/-- The mathematical specification of a raw transform is the direct sparse-transform sum. -/
theorem certRhsTransformSpec_eq (group : Fin 172) (target : Fin 272) :
    rhsTransformSpec cert246Data.rhsFeatureEnc cert246Data.rhsGroupEnc 8 255 256
        (2 ^ 256 - 1) 7 127 512 (2 ^ 512 - 1) (2 ^ 256 - 1)
        cert246Data.rhsWeightT cert246Data.pairT group target =
      certRhsDirectTransform group target := by
  unfold rhsTransformSpec certRhsDirectTransform
  change (∑ offset ∈ Finset.range (certRhsPartition.group group).size,
      rhsFeatureWeight 8 255 256 (2 ^ 256 - 1) cert246Data.rhsWeightT
          ((certRhsPartition.group group).start + offset) *
        cert246Data.rhsMomentPred 7 127 512 (2 ^ 512 - 1) (2 ^ 256 - 1)
          cert246Data.pairT target
            (cert246Data.rhsFeatureSignature
              (cert246Data.rhsFeatureField cert246Data.rhsFeatureEnc
                ((certRhsPartition.group group).start + offset))) = _)
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro offset _
  rw [certRhsFeatureWeight group offset]
  have hsignature : cert246Data.rhsFeatureSignature
      (cert246Data.rhsFeatureField cert246Data.rhsFeatureEnc
        ((certRhsPartition.group group).start + offset)) =
      (certRhsFeature
        (certRhsPartition.member certRhsPartition_bound group offset)).signature.val := by
    rw [certRhsMember]
    unfold certRhsFeature
    dsimp only
    rw [Nat.mod_eq_of_lt (certRhsFeatureSignature_bound _
      (lt_of_lt_of_le (Nat.add_lt_add_left offset.isLt _)
        (certRhsPartition_bound group)))]
  rw [hsignature]
  rw [certRhsMomentPred]

end PrimeGaps.Gap246
