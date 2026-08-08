/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.RHS.Checks
public import PrimeGapsCert.Gap246.RHS.ConcreteSound.Contraction
public import PrimeGapsCert.Meta.Batched


/-! # Assembly of the complete packed sparse RHS radial checks -/

@[expose] public section

namespace PrimeGaps.Gap246

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 3000 in
private theorem certRhsRadialEntries_complete : ∀ index,
    4998 ≤ index → index < 10404 →
      cert246Data.rhsRadialEntryCheck 50 25 102 6 63 832 (2 ^ 832 - 1)
        index cert246Data.rhsRadialT = true := by
  have hblocks : ∀ block : Fin 43, CertRhsRadialBlockCorrect block :=
    combine_batched_theorems% CertRhsRadialBlockCorrect 43
  intro index hlower hupper
  let block : Fin 43 := ⟨(index - 4998) / 128, by
    apply Nat.div_lt_of_lt_mul
    omega⟩
  have hraw := hblocks block
  unfold CertRhsRadialBlockCorrect at hraw
  apply rhsRadialCheck_sound hraw index
  · have hdiv := Nat.div_mul_le_self (index - 4998) 128
    dsimp only [block]
    omega
  · have hmod := Nat.mod_lt (index - 4998) (by norm_num : 0 < 128)
    have hdecompose := Nat.mod_add_div' (index - 4998) 128
    dsimp only [block]
    apply lt_min hupper
    omega

set_option exponentiation.threshold 1000 in
/-- Every needed packed radial entry equals the direct cleared radial-factor formula. -/
theorem certRhsRadialChecks_complete : CertRhsRadialChecks := by
  intro q e hlower hupper
  induction e generalizing q with
  | zero =>
      have hentry := certRhsRadialEntries_complete (q * 102) (by omega) (by omega)
      have hsound := rhsRadialEntryCheck_sound hentry (by omega) (by omega)
      simpa using hsound
  | succ e inductionHypothesis =>
      have he : e + 1 < 102 := by omega
      have hdiv : (q * 102 + (e + 1)) / 102 = q := by omega
      have hmod : (q * 102 + (e + 1)) % 102 = e + 1 := by omega
      have hentry := certRhsRadialEntries_complete (q * 102 + (e + 1))
        (by omega) (by omega)
      have hrec := rhsRadialEntryCheck_sound hentry (by omega) (by omega)
      simp only [hdiv, hmod, if_neg (by omega : e + 1 ≠ 0), Nat.add_sub_cancel] at hrec
      rw [inductionHypothesis q hlower (by omega)] at hrec
      rw [inductionHypothesis (q + 1) (by omega) (by omega)] at hrec
      have hformula :
          25 * cert246Data.rhsRadialFormula 50 25 q (e + 1) +
              25 * q * cert246Data.rhsRadialFormula 50 25 (q + 1) e =
            26 * cert246Data.rhsRadialFormula 50 25 q e := by
        simpa only [rhsRadialFormula_eq] using
          radialExplicitInt_recurrence 50 25 q e (by norm_num) (by omega)
      have hmul := Nat.add_right_cancel (hrec.trans hformula.symm)
      exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 25) hmul

end PrimeGaps.Gap246
