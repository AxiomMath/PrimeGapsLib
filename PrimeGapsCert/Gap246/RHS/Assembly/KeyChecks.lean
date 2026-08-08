/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.RHS.Checks
public import PrimeGapsCert.Gap246.RHS.WeightBridge
public import PrimeGapsCert.Meta.Batched


/-! # Assembly of the complete packed sparse RHS feature-key checks -/

@[expose] public section

namespace PrimeGaps.Gap246

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 3000 in
/-- Every source-label erasure lookup passes its complete packed feature-key check. -/
theorem certRhsFeatureKeyChecks_complete : CertRhsFeatureKeyChecks := by
  have hblocks : ∀ block : Fin 41, CertRhsFeatureKeyBlockCorrect block :=
    combine_batched_theorems% CertRhsFeatureKeyBlockCorrect 41
  intro label hlabel
  let block : Fin 41 := ⟨label / 32, by
    apply Nat.div_lt_of_lt_mul
    exact lt_of_lt_of_le hlabel (by norm_num)⟩
  have hraw := hblocks block
  unfold CertRhsFeatureKeyBlockCorrect at hraw
  apply rhsFeatureKeysCheck_sound hraw label
  · dsimp only [block]
    exact Nat.div_mul_le_self label 32
  · have hmod := Nat.mod_lt label (by norm_num : 0 < 32)
    have hdecompose := Nat.mod_add_div' label 32
    have hstop : label < (label / 32 + 1) * 32 := by omega
    dsimp only [block]
    exact lt_min hlabel hstop

end PrimeGaps.Gap246
