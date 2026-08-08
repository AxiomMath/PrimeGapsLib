/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.ArithmeticFunction.Zeta


/-! # Real powers as an arithmetic function -/

@[expose] public section

open Real

namespace ArithmeticFunction

open zeta

/-- The arithmetic function indexed by `σ : ℝ` that sends `n : ℕ` to `n ^ σ`. -/
noncomputable def rpow (σ : ℝ) : ArithmeticFunction ℝ where
  toFun n := if σ = 0 ∧ n = 0 then 0 else n ^ σ
  map_zero' := by simp +contextual

@[simp] theorem rpow_apply {σ : ℝ} {n : ℕ} (h : σ ≠ 0 ∨ n ≠ 0) : rpow σ n = n ^ σ := by
  simp only [rpow, coe_mk]
  grind

@[simp] theorem rpow_zero : rpow 0 = ζ := ext fun n ↦ by aesop

@[aesop safe apply]
theorem isMultiplicative_rpow {σ : ℝ} : IsMultiplicative (rpow σ) := by
  obtain rfl | hσ := eq_or_ne σ 0
  · simpa using isMultiplicative_zeta.natCast
  simp [IsMultiplicative, hσ, mul_rpow]

end ArithmeticFunction
