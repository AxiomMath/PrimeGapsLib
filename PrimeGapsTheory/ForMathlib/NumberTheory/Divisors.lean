/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.Divisors


/-! # Divisors as Finset -/

@[expose] public section

open Finset

namespace Nat

/-- The finset of divisors between `d₀` and `d`, i.e. `{r : d₀ ∣ r ∧ r ∣ d}`, except if `d = 0` in
which case we return `∅`. -/
def divisorsBetween (d₀ d : ℕ) : Finset ℕ := if d₀ ∣ d then (d / d₀).divisors.image (d₀ * ·) else ∅

@[simp] theorem mem_divisorsBetween_iff {d₀ d r : ℕ} :
    r ∈ divisorsBetween d₀ d ↔ d ≠ 0 ∧ d₀ ∣ r ∧ r ∣ d := by
  simp_rw [divisorsBetween, mem_ite, mem_image, mem_divisors, notMem_empty, imp_false,
    not_not, Nat.div_ne_zero_iff]
  refine ⟨fun h ↦ by aesop, fun ⟨h₁, h₂, h₃⟩ ↦ ?_⟩
  have h₄ := h₂.trans h₃
  exact ⟨fun _ ↦ ⟨r / d₀, ⟨div_dvd_div h₂ h₃, ne_zero_of_dvd_ne_zero h₁ h₄,
    le_of_dvd (by grind) h₄⟩, Nat.mul_div_cancel' h₂⟩, h₄⟩

end Nat
