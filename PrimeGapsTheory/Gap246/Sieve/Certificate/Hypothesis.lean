/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Gap246.Sieve.Certificate.Explicit

/-! # Hypothesis that an explicit certificate for `M_{k,ε} > 4` exists -/

@[expose] public section

namespace PrimeGaps

/-- The hypothesis that an explicit certificate for `M_{k,ε} > 4` exists. -/
inductive ExistsEpsCert (k : ℕ) : Prop where
  | mk : {ε : ℚ} → 0 ≤ ε → ε ≤ 1 → EpsCertificateExplicit k ε → ExistsEpsCert k

theorem ExistsEpsCert.mk' {k : ℕ} {ε : ℚ} (ct : EpsCertificateExplicit k ε)
    (hε₀ : 0 ≤ ε := by decide +kernel) (hε₁ : ε ≤ 1 := by decide +kernel) : ExistsEpsCert k :=
  .mk hε₀ hε₁ ct

end PrimeGaps
