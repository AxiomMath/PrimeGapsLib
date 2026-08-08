/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Witness
public import PrimeGapsTheory.Gap246.Endgame.Main

/-! # Prime Gaps Bounded by 246

This file combines the theory developed in `PrimeGapsTheory.Gap246.Endgame.Main`
with the certificate in `PrimeGapsCert.Gap246.Witness` to prove the main result, that the
Bombieri-Vinogradov theorem implies that prime gaps are bounded by 246 infinitely often.

-/

@[expose] public section

theorem bombieriVinogradov_implies_frequently_prime_gap_le_246 (hBV : BombieriVinogradov) :
    ∃ᶠ m in Filter.atTop, Nat.nth Nat.Prime (m + 1) - Nat.nth Nat.Prime m ≤ 246 :=
  Gaps246.thm_main hBV PrimeGaps.existsEpsCert50

theorem bombieriVinogradov_implies_prime_gap_le_246 :
    BombieriVinogradov → ∀ n₀ : ℕ, ∃ p q : ℕ, n₀ ≤ p ∧ p < q ∧ p.Prime ∧ q.Prime ∧ q ≤ p + 246 :=
  (bombieriVinogradov_and_existsEpsCert50_imply_prime_gap_le_246 · PrimeGaps.existsEpsCert50)

theorem bombieriVinogradov_implies_nth_prime_gap_le_246 :
    BombieriVinogradov → ∀ n₀ : ℕ, ∃ n ≥ n₀, (n + 1).nth Nat.Prime ≤ n.nth Nat.Prime + 246 :=
  (bombieriVinogradov_and_existsEpsCert50_imply_nth_prime_gap_le_246 · PrimeGaps.existsEpsCert50)
