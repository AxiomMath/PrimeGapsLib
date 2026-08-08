/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Reindexing at a pinned coordinate

Reindexes sums and products after fixing one coordinate to one.

## Main definitions

*  `pinOneEquiv`: The equivalence between free tuples and tuples whose distinguished coordinate is
  one.

## Main results

*  `tsum_pin_coord_one`: Reindexes a sum guarded by a distinguished coordinate equal to one.
*  `prod_erase_eq_prod_succAbove`: Reindexes a product over all coordinates except the
  distinguished coordinate.
-/

@[expose] public section


namespace PrimeGaps

/-- `σ ↦ Fin.insertNth m 1 σ` is a bijection from `Fin n → ℕ` onto
`{ρ: Fin (n + 1) → ℕ // ρ m = 1}`. -/
def pinOneEquiv {n : ℕ} (m : Fin (n + 1)) : (Fin n → ℕ) ≃ {ρ : Fin (n + 1) → ℕ // ρ m = 1} where
  toFun σ := ⟨Fin.insertNth m 1 σ, by simp⟩
  invFun ρ := Fin.removeNth m ρ.1
  left_inv σ := by simp [Fin.removeNth_insertNth]
  right_inv ρ := Subtype.ext (ρ.2 ▸ Fin.insertNth_self_removeNth m ρ.1)

/-- For any `h: (Fin (n+1) → ℕ) → M`,
`∑' ρ, (if ρ m = 1 then h ρ else 0) = ∑' σ: Fin n → ℕ, h (Fin.insertNth m 1 σ)`. -/
theorem tsum_pin_coord_one {n : ℕ} {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    (m : Fin (n + 1)) (h : (Fin (n + 1) → ℕ) → M) :
    (∑' ρ : Fin (n + 1) → ℕ, if ρ m = 1 then h ρ else 0) =
      ∑' σ : Fin n → ℕ, h (Fin.insertNth m 1 σ) := by
  classical
  have hind : (fun ρ : Fin (n + 1) → ℕ ↦ if ρ m = 1 then h ρ else 0) =
      Set.indicator {ρ : Fin (n + 1) → ℕ | ρ m = 1} h := by
    funext ρ; simp [Set.indicator_apply]
  rw [hind, ← tsum_subtype]
  exact (Equiv.tsum_eq (pinOneEquiv m) (fun x ↦ h x.1)).symm

/-- A product over `Finset.univ.erase m` equals the product over all `Fin n` composed with
`m.succAbove`. -/
theorem prod_erase_eq_prod_succAbove {n : ℕ} {M : Type*} [CommMonoid M] (m : Fin (n + 1))
    (f : Fin (n + 1) → M) :
    ∏ i ∈ Finset.univ.erase m, f i = ∏ j : Fin n, f (m.succAbove j) := by
  rw [← Finset.compl_singleton, ← Fin.image_succAbove_univ,
    Finset.prod_image fun a _ b _ h ↦ Fin.succAbove_right_injective h]

end PrimeGaps
