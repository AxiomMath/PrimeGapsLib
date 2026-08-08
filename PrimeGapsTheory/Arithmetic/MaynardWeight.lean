/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Arithmetic weights for the Maynard sieve

Shared arithmetic definitions used by the Mertens estimates and both sieve moments.

## Main definitions

* `hfun`: The arithmetic function `μ²/φ`.
* `Sset`: The squarefree, `W`-coprime integers below `R`.
* `sumA`, `sumB`, `sumT`: The free-coordinate and off-diagonal weights over `Sset`.
* `momentSum`: The convergent multiplier `∑ μ(d)²/(φ(d)·d)`.

## Main results

* `hfun_isMultiplicative`: `μ²/φ` is multiplicative.
-/

@[expose] public section

open scoped BigOperators

open scoped ArithmeticFunction.Moebius

namespace PrimeGaps

/-- The arithmetic function `a ↦ μ(a)² / φ(a)` over `ℝ`. -/
noncomputable def hfun : ArithmeticFunction ℝ where
  toFun a := (μ a : ℝ) ^ 2 / (Nat.totient a : ℝ)
  map_zero' := by simp

/-- Evaluation of `hfun`: `hfun a = μ(a)² / φ(a)`. -/
theorem hfun_apply (a : ℕ) :
    hfun a = (μ a : ℝ) ^ 2 / (Nat.totient a : ℝ) := rfl

/-- `hfun = μ²/φ` is multiplicative. -/
theorem hfun_isMultiplicative : hfun.IsMultiplicative := by
  refine ⟨by simp [hfun_apply], fun {m n} hmn ↦ ?_⟩
  simp only [hfun_apply]
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn, Nat.totient_mul hmn]
  push_cast
  ring

end PrimeGaps

namespace PrimeGaps.MaynardOffDiagonal

/-- The squarefree, `W`-coprime integers below `R`, as a concrete `Finset ℕ`. -/
noncomputable def Sset (W : ℕ) (R : ℝ) : Finset ℕ :=
  {n ∈ (Finset.Icc 1 ⌊R⌋₊) | Squarefree n ∧ Nat.gcd n W = 1}

/-- `A = ∑_{n ∈ S} 1/φ(n)` — the free-coordinate weight. -/
@[pg_tag "bg246" "def_A_m_x"]
noncomputable def sumA (W : ℕ) (R : ℝ) : ℝ := ∑ n ∈ Sset W R, 1 / (Nat.totient n : ℝ)

/-- `B = ∑_{n ∈ S} 1/φ(n)²` — the unconstrained off-diagonal weight. -/
noncomputable def sumB (W : ℕ) (R : ℝ) : ℝ := ∑ n ∈ Sset W R, 1 / (Nat.totient n : ℝ) ^ 2

/-- `T = ∑_{n ∈ S, n ≠ 1} 1/φ(n)²` — the off-diagonal weight forced `≠ 1`. -/
noncomputable def sumT (W : ℕ) (R : ℝ) : ℝ :=
  ∑ n ∈ {n ∈ (Sset W R) | n ≠ 1}, 1 / (Nat.totient n : ℝ) ^ 2

/-- The convergent multiplier `∑_{d ≤ N, d squarefree, gcd(d,W)=1} μ(d)²/(φ(d)·d)`. -/
noncomputable def momentSum (W N : ℕ) : ℝ :=
  ∑ d ∈ {d ∈ (Finset.Icc 1 N) | Squarefree d ∧ Nat.gcd d W = 1},
    (μ d : ℝ) ^ 2 / (Nat.totient d : ℝ) * (1 / (d : ℝ))

end PrimeGaps.MaynardOffDiagonal
