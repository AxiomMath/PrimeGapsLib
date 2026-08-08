/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions


/-! # Finsupps supported on a set -/

@[expose] public section

universe u

open scoped Cardinal

namespace Finsupp

instance {α : Type*} (M R : Type*) [Semiring R] [AddCommMonoid M] [Module R M] [Module.Free R M]
    (s : Set α) : Module.Free R (supported M R s) :=
  .of_equiv (supportedEquivFinsupp s).symm

theorem supported_ext {α M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {s : Set α}
    {f g : supported M R s} (ih : ∀ i ∈ s, f.1 i = g.1 i) : f = g := Subtype.ext <| ext fun i ↦
  by_cases (p := i ∈ s) (ih i) <| by
    simp_all [(mem_supported' _ _).mp f.2, (mem_supported' _ _).mp g.2]

theorem rank_supported' {α : Type u} (M : Type u) (R : Type*) [Semiring R] [StrongRankCondition R]
    [AddCommMonoid M] [Module R M] [Module.Free R M] (s : Set α) :
    Module.rank R (supported M R s) = #s * Module.rank R M :=
  LinearEquiv.rank_eq (supportedEquivFinsupp s) |>.trans <| rank_finsupp' ..

theorem rank_supported {α : Type*} (M R : Type*) [Semiring R] [StrongRankCondition R]
    [AddCommMonoid M] [Module R M] [Module.Free R M] (s : Set α) :
    Module.rank R (supported M R s) = (#s).lift * (Module.rank R M).lift :=
  LinearEquiv.rank_eq (supportedEquivFinsupp s) |>.trans <| rank_finsupp ..

theorem rank_supported_self' {α : Type u} (R : Type u) [Semiring R] [StrongRankCondition R]
    (s : Set α) : Module.rank R (supported R R s) = #s := by
  rw [rank_supported', Module.rank_self, mul_one]

theorem rank_supported_self {α : Type*} (R : Type*) [Semiring R] [StrongRankCondition R]
    (s : Set α) : Module.rank R (supported R R s) = (#s).lift := by
  rw [rank_supported, Module.rank_self, Cardinal.lift_one, mul_one]

theorem rank_supported_self_finset {α : Type*} (R : Type*) [Semiring R]
    [StrongRankCondition R] (s : Finset α) :
    Module.rank R (supported R R (s : Set α)) = s.card := by
  simp [rank_supported_self]

instance {α : Type*} (R : Type*) [Semiring R] [StrongRankCondition R] (s : Finset α) :
    Module.Finite R (supported R R (s : Set α)) := by
  simp [← Module.rank_lt_aleph0_iff, rank_supported_self_finset]

@[simp] theorem finrank_supported_self_finset {α : Type*} (R : Type*) [Semiring R]
    [StrongRankCondition R] (s : Finset α) :
    Module.finrank R (supported R R (s : Set α)) = s.card := by
  simp [Module.finrank, rank_supported_self_finset]

end Finsupp
