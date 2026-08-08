/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.PrimeCounting

/-! # The statement file

This file is built by humans to act as the standard to check the main theorems against, using
the comparator.

-/

@[expose] public section

open Nat Real Finset

section BombieriVinogradov

noncomputable def Real.primeCountingZMod (x : ℝ) (q : ℕ) (a : ZMod q) : ℕ :=
  {p : ℕ | p.Prime ∧ (p : ZMod q) = a ∧ p ≤ x}.ncard

-- from PNT+
noncomputable def pi (x : ℝ) : ℝ :=
  ⌊x⌋₊.primeCounting

local notation "π(" x "; " q ", " a ")" => Real.primeCountingZMod x q a
local notation "π(" x ")" => pi x

-- Corresponds to (1.3) in James Maynard's paper *Small gaps between primes*.
def BombieriVinogradov : Prop := ∀ θ < (1 / 2 : ℝ), ∀ A ≥ (1 : ℝ), ∃ c > (0 : ℝ), ∀ x ≥ (3 : ℝ),
    ∑ q ∈ Icc (1 : ℕ) ⌊x ^ θ⌋₊, ⨆ a : (ZMod q)ˣ, |(π(x; q, a) - π(x) / φ q : ℝ)| ≤ c * x / x.log ^ A

end BombieriVinogradov

section Challenges

theorem bombieriVinogradov_implies_prime_gap_le_246 :
    BombieriVinogradov → ∀ n₀ : ℕ, ∃ p q : ℕ, n₀ ≤ p ∧ p < q ∧ p.Prime ∧ q.Prime ∧ q ≤ p + 246 :=
  sorry

theorem bombieriVinogradov_implies_nth_prime_gap_le_246 :
    BombieriVinogradov → ∀ n₀ : ℕ, ∃ n ≥ n₀, (n + 1).nth Nat.Prime ≤ n.nth Nat.Prime + 246 :=
  sorry

end Challenges
