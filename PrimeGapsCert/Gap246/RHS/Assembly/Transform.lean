/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.RHS.Checks
public import PrimeGapsCert.Gap246.RHS.ConcreteSound.Transform
public import PrimeGapsCert.Meta.Batched


/-! # Assembly of the complete packed sparse RHS transform -/

@[expose] public section

namespace PrimeGaps.Gap246

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 3000 in
/-- Every stored sparse-transform entry passes its direct numerical check. -/
theorem certRhsTransformChecks_complete : CertRhsTransformChecks := by
  have hblocks : ∀ block : Fin 190, CertRhsTransformBlockCorrect block :=
    combine_batched_theorems% CertRhsTransformBlockCorrect 190
  intro entry hentry
  let block : Fin 190 := ⟨entry / 32, by
    apply Nat.div_lt_of_lt_mul
    exact lt_of_lt_of_le hentry (by norm_num)⟩
  have hraw := hblocks block
  unfold CertRhsTransformBlockCorrect at hraw
  apply rhsTransformCheck_sound hraw entry
  · dsimp only [block]
    exact Nat.div_mul_le_self entry 32
  · have hmod := Nat.mod_lt entry (by norm_num : 0 < 32)
    have hdecompose := Nat.mod_add_div' entry 32
    have hstop : entry < (entry / 32 + 1) * 32 := by omega
    dsimp only [block]
    exact lt_min hentry hstop

/-- Every lookup in the complete checked sparse RHS transform is mathematically exact. -/
theorem certRhsTransform_complete : ∀ group target,
    RhsDegreeTransformCorrectAt preEpsWitnessInt certRhsFeature certRhsPartition
      certRhsPartition_valid certRhsTransform group target :=
  certRhsTransform_correct certRhsTransformChecks_complete

end PrimeGaps.Gap246
