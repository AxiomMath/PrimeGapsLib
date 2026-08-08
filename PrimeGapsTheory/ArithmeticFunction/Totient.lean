/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import PrimeGapsTheory.Tactic.PaperTag

/-! # The Euler totient function as an arithmetic function -/

@[expose] public section

namespace ArithmeticFunction

/-- Euler's totient function as an arithmetic function. -/
@[pg_tag "bg246" "def_totient"]
def totient : ArithmeticFunction ℕ where
  toFun := Nat.totient
  map_zero' := by simp

@[inherit_doc] scoped[ArithmeticFunction.totient] notation "φ" => ArithmeticFunction.totient

open totient zeta

@[simp] theorem totient_apply {n : ℕ} : φ n = n.totient := rfl

@[aesop safe apply]
theorem isMultiplicative_totient : (φ).IsMultiplicative := by
  simpa [IsMultiplicative] using @Nat.totient_mul

@[simp] theorem totient_mul_zeta : φ * ζ = .id := ext fun n ↦ by
  obtain rfl | hn := eq_or_ne n 0
  · rfl
  simp +contextual [show ∀ x ∈ n.divisorsAntidiagonal, x.2 ≠ 0 by aesop,
    Nat.sum_divisorsAntidiagonal (fun d _ ↦ d.totient), Nat.sum_totient]

@[simp] theorem zeta_mul_totient : ζ * φ = .id := by grind [totient_mul_zeta]

end ArithmeticFunction
