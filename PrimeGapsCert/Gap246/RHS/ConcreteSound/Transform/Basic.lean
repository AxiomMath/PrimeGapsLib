/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.RHS.HighLevel
public import PrimeGapsCert.Gap246.Sparse.RhsTransformSound

import PrimeGapsCert.Gap246.RHS.Checks.Index
import PrimeGapsCert.Meta.Batched

/-! # Concrete soundness bridge for the packed sparse RHS kernel -/

set_option maxRecDepth 100000

@[expose] public section

namespace PrimeGaps.Gap246

open Finset

/-- Every packed RHS feature signature is an in-range signature index. -/
theorem certRhsFeatureSignature_bound : ∀ feature < 1504,
    cert246Data.rhsFeatureSignature
      (cert246Data.rhsFeatureField cert246Data.rhsFeatureEnc feature) < 272 := by
  have hblocks : ∀ block : Fin 6, CertRhsFeatureSignatureBlockCorrect block :=
    combine_batched_theorems% CertRhsFeatureSignatureBlockCorrect 6
  intro feature hfeature
  let block : Fin 6 := ⟨feature / 256, by omega⟩
  apply rhsFeatureSignatureRangeCheck_sound (hblocks block) feature
  · dsimp only [block]
    exact Nat.div_mul_le_self feature 256
  · dsimp only [block]
    omega

/-- The mathematical feature signature removes the redundant checked modulus. -/
theorem certRhsFeatureSignature_raw (feature : Fin 1504) :
    (certRhsFeature feature).signature.val = cert246Data.rhsFeatureSignature
      (cert246Data.rhsFeatureField cert246Data.rhsFeatureEnc feature) := by
  unfold certRhsFeature
  dsimp only
  rw [Nat.mod_eq_of_lt (certRhsFeatureSignature_bound feature feature.isLt)]

/-- The packed feature at a valid group offset is the corresponding mathematical member. -/
theorem certRhsMember (group : Fin 172) (offset : Fin (certRhsPartition.group group).size) :
    certRhsPartition.member certRhsPartition_bound group offset =
      ⟨(certRhsPartition.group group).start + offset,
        lt_of_lt_of_le (Nat.add_lt_add_left offset.isLt _)
          (certRhsPartition_bound group)⟩ := by
  apply Fin.ext
  rfl

/-- The raw weight at a group offset is the corresponding mathematical feature weight. -/
theorem certRhsFeatureWeight (group : Fin 172)
    (offset : Fin (certRhsPartition.group group).size) :
    rhsFeatureWeight 8 255 256 (2 ^ 256 - 1) cert246Data.rhsWeightT
        ((certRhsPartition.group group).start + offset) =
      (certRhsFeature (certRhsPartition.member certRhsPartition_bound group offset)).weight := by
  rw [certRhsMember]
  rfl

/-- The raw low-lane lookup is the mathematical predecessor moment lookup. -/
theorem certRhsMomentPred (target signature : Fin 272) :
    cert246Data.rhsMomentPred 7 127 512 (2 ^ 512 - 1) (2 ^ 256 - 1)
        cert246Data.pairT target signature =
      certPairValue (signaturePairIndex target signature) % 2 ^ 256 := by
  simp only [cert246Data.rhsMomentPred, certPairValue, signaturePairIndex_divNat,
    signaturePairIndex_modNat]
  exact Nat.and_two_pow_sub_one_eq_mod _ 256

end PrimeGaps.Gap246
