/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Data.Sound
public import PrimeGapsCert.Gap246.Moments.PairDefs

/-! # Lightweight certificate interface over the packed packed data -/

@[expose] public section

namespace PrimeGaps.Gap246

/-- Packed descriptor of one labelled basis coefficient. -/
noncomputable def certLabelField (label : Fin 1295) : ℕ :=
  cert246Data.labelField cert246Data.labelEnc label

/-- Slack exponent of one labelled basis coefficient. -/
noncomputable def certLabelA (label : Fin 1295) : ℕ :=
  cert246Data.labelA (certLabelField label)

/-- Signature label of one basis coefficient, with its checked range proof. -/
noncomputable def certLabelSignature (label : Fin 1295) : Fin 272 :=
  ⟨cert246Data.labelSignature (certLabelField label), (certLabels label label.isLt).1⟩

/-- Signed integral basis coefficient, its magnitude read from the fixed-width packed tree. -/
noncomputable def certLabelCoefficient (label : Fin 1295) : ℤ :=
  if cert246Data.labelSign (certLabelField label) = 1 then
    -(cert246Data.treeAt 9 511 128 (2 ^ 128 - 1) cert246Data.coeffMag label : ℤ)
  else cert246Data.treeAt 9 511 128 (2 ^ 128 - 1) cert246Data.coeffMag label

/-- One ordered signature-pair value read symmetrically from the triangular packed tree. -/
noncomputable def certPairValue (pair : Fin (272 * 272)) : ℕ :=
  cert246Data.treeAt 7 127 512 (2 ^ 512 - 1) cert246Data.pairT
    (cert246Data.triIdx pair.divNat pair.modNat)

/-- Direct factor tables used only by the mathematical soundness layer. -/
noncomputable def certFactorTables : EpsPairFactorTables 50 25 25 :=
  directEpsPairFactorTables 50 25 25

/-- The complete lightweight pre-certificate backed by packed first-order data. -/
noncomputable def preEpsWitnessInt : PreEpsCertificateExplicitDagInt 50 25 25 where
  S := 272
  S_pos := by norm_num
  sig row := certSig row
  zeroFree row := certSig_zeroFree row row.isLt
  exponent_lt row x hx := certSig_exponent_lt row row.isLt x hx
  erase := certErase
  erase_sig row x hx := certErase_sig row x hx
  momentRadix := 2 ^ 256
  momentRadix_pos := by positivity
  pairValue := certPairValue
  epsilon_pos := by norm_num
  degree_pos := by norm_num
  degree_pair_bound := by norm_num
  N := 1295
  a := certLabelA
  sigIndex := certLabelSignature
  coeff := certLabelCoefficient
  degree label := by
    obtain ⟨-, hsum, hbound⟩ := certLabels label label.isLt
    change cert246Data.labelA (cert246Data.labelField cert246Data.labelEnc label) +
      (certSig (cert246Data.labelSignature
        (cert246Data.labelField cert246Data.labelEnc label))).sum ≤ 25
    rw [certSig_sum, ← hsum]
    exact hbound

/-- The direct factor-table bundle is globally correct by construction. -/
theorem certFactorTables_correct : certFactorTables.Correct :=
  directEpsPairFactorTables_correct 50 25 25

end PrimeGaps.Gap246
