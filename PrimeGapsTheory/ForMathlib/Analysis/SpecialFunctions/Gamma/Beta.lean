/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import PrimeGapsTheory.Tactic.PaperTag

/-! # Beta function -/

@[expose] public section

namespace Real

/-- The real Beta function. Notation is `Β(a, b)`, where note that `Β` is Greek capital beta,
input as `\GB`. -/
@[pg_tag "bg246" "not_beta"]
noncomputable def betaIntegral (a b : ℝ) : ℝ := ∫ t in 0..1, t ^ (a - 1) * (1 - t) ^ (b - 1)

@[inherit_doc] scoped[Real.beta] notation "Β(" a:max ", " b:max ")" => betaIntegral a b

open beta

@[simp] theorem ofReal_betaIntegral {a b : ℝ} : (Β(a, b) : ℂ) = (a : ℂ).betaIntegral b := by
  rw [betaIntegral, Complex.betaIntegral, ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr_uIoo fun x hx ↦ ?_
  rw [Set.uIoo_of_lt one_pos] at hx
  simp [Complex.ofReal_cpow, show 0 ≤ x by grind, show 0 ≤ 1 - x by grind]

theorem betaIntegral_eq_Gamma_mul_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Β(a, b) = a.Gamma * b.Gamma / (a + b).Gamma := Complex.ofReal_injective <| by
  simp [Complex.betaIntegral_eq_Gamma_mul_div, ha, hb, ← Complex.Gamma_ofReal]

end Real

namespace Nat

@[pg_tag "bg246" "lem_beta_integral"]
theorem betaIntegral_eq_factorial_mul_div (a b : ℕ) :
    ∫ t in 0..1, t ^ a * (1 - t) ^ b = a ! * b ! / (a + b + 1)! := by
  convert Real.betaIntegral_eq_Gamma_mul_div (a := a + 1) (b := b + 1) (by positivity)
    (by positivity) <;>
  simp [Real.betaIntegral, ← Real.Gamma_nat_eq_factorial]
  grind

end Nat
add_to_pg "maynard" "not_Gamma" Real.Gamma
add_to_pg "maynard" "lem_Gamma_factorial" Real.Gamma_nat_eq_factorial
