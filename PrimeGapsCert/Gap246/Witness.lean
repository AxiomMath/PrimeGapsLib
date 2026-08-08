/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.LHS.Assembly
public import PrimeGapsCert.Gap246.Moments.BoundAssembly
public import PrimeGapsCert.Gap246.RHS.Assembly
public import PrimeGapsTheory.Gap246.Sieve.Certificate.Hypothesis

/-! # Complete packed certificate for `M_{50,1/25} > 4` -/

@[expose] public section

namespace PrimeGaps.Gap246

/-- The stored LHS rows equal the original enlarged-simplex quadratic form. -/
theorem certLhsStoredRowSum_eq :
    (∑ row : Fin 138, certLhsStoredRow row) =
      ∑ i, ∑ j, preEpsWitnessInt.lhsPairTerm i j := by
  rw [certLhsStoredRowSum]
  exact preEpsWitnessInt.lhsPairWithTablesSumSymmetric_eq certFactorTables
    certFactorTables_correct preMomentTop_comm

/-- The stored RHS rows equal the original marginal quadratic form. -/
theorem certRhsStoredRowSum_eq :
    (∑ row : Fin 172, certRhsStoredRow row) =
      ∑ i, ∑ j, preEpsWitnessInt.rhsPairTerm i j := by
  rw [certRhsStoredRowSum,
    preEpsWitnessInt.rhsFeatureSum_eq certFactorTables certRhsFeature
      certRhsFeatures_complete certFactorTables_correct]

/-- The final inequality between the two checked families of stored row totals. -/
theorem certStoredInequality :
    4 * ∑ row : Fin 138, certLhsStoredRow row <
      50 * ∑ row : Fin 172, certRhsStoredRow row := by
  decide +kernel

/-- The complete cleared-denominator witnessing inequality. -/
theorem certInequality :
    4 * ∑ i, ∑ j, preEpsWitnessInt.lhsPairTerm i j <
      50 * ∑ i, ∑ j, preEpsWitnessInt.rhsPairTerm i j := by
  rw [← certLhsStoredRowSum_eq, ← certRhsStoredRowSum_eq]
  exact certStoredInequality

/-- The precomputed integer data with its moment table and final inequality certified. -/
noncomputable def epsWitnessInt : EpsCertificateExplicitPrecomputedInt 50 25 25 where
  pre := preEpsWitnessInt
  pairValue_eq := prePairValue_eq_direct certMomentPairs
  momentPred_lt := certMomentPred_lt
  cert := certInequality

/-- A packed certificate for `M_{50,1/25} > 4`. -/
noncomputable def epsWitness : EpsCertificateExplicit 50 (1 / 25) :=
  epsWitnessInt.toExplicit

end PrimeGaps.Gap246

namespace PrimeGaps

/-- The precomputed integer data for the `M_{50,1/25} > 4` certificate. -/
noncomputable def epsWitnessInt : EpsCertificateExplicitPrecomputedInt 50 25 25 :=
  Gap246.epsWitnessInt

/-- A certificate for `M_{50,1/25} > 4`. -/
noncomputable def epsWitness : EpsCertificateExplicit 50 (1 / 25) :=
  Gap246.epsWitness

theorem existsEpsCert50 : ExistsEpsCert 50 := .mk' epsWitness

end PrimeGaps
