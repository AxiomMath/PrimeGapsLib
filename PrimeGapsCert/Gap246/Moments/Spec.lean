/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Group.Hom.End
public import PrimeGapsCert.Gap246.Certificate.Fast

/-! # Mathematical specification of the nilpotent moment ladder -/

@[expose] public section

open scoped Nat

namespace PrimeGaps.Gap246

open Finset

/-- A factorial-moment table indexed by two signatures. -/
abbrev MomentState := Multiset ℕ → Multiset ℕ → ℕ

/-- The identity-free part of the coordinate-splitting transition. -/
def nilStep (state : MomentState) (α β : Multiset ℕ) : ℕ :=
  (∑ y ∈ β.toFinset, y ! * state α (β.erase y)) +
    ∑ x ∈ α.toFinset, (x ! * state (α.erase x) β +
      ∑ y ∈ β.toFinset, (x + y)! * state (α.erase x) (β.erase y))

/-- The identity-free transition as an additive endomorphism. -/
def nilOperator : AddMonoid.End MomentState where
  toFun := nilStep
  map_zero' := by
    funext α β
    simp [nilStep]
  map_add' left right := by
    funext α β
    simp only [Pi.add_apply, nilStep, mul_add, Finset.sum_add_distrib]
    ac_rfl

/-- Level-zero table. -/
def nilBase : MomentState := fun α β ↦ if α = 0 ∧ β = 0 then 1 else 0

/-- The `r`th power of the identity-free transition applied to level zero. -/
def nilMoment (r : ℕ) : MomentState := (nilOperator ^ r) nilBase

/-- The ordinary moment reconstructed by the binomial theorem. -/
def binomialMoment (dimension : ℕ) : MomentState := fun α β ↦
  ∑ r ∈ Finset.range (dimension + 1), dimension.choose r * nilMoment r α β

/-- The full recurrence is the identity plus its identity-free part. -/
theorem fullStep_eq_add_nilStep (state : MomentState) {α β : Multiset ℕ}
    (hα : 0 ∉ α) (hβ : 0 ∉ β) :
    (∑ x ∈ insert 0 α.toFinset, ∑ y ∈ insert 0 β.toFinset,
      (x + y)! * state (α.erase x) (β.erase y)) =
        state α β + nilStep state α β := by
  have hαfin : 0 ∉ α.toFinset := by simpa
  have hβfin : 0 ∉ β.toFinset := by simpa
  simp only [Finset.sum_insert hαfin, Finset.sum_insert hβfin, nilStep,
    Multiset.erase_of_notMem hα, Multiset.erase_of_notMem hβ, Nat.zero_add,
    Nat.add_zero, Nat.factorial_zero, one_mul]
  ac_rfl

/-- The mathematical factorial moment is the binomial reconstruction of nilpotent powers. -/
theorem facMomentNat_eq_binomialMoment {α β : Multiset ℕ} (hα : 0 ∉ α) (hβ : 0 ∉ β) :
    ∀ dimension, facMomentNat dimension α β = binomialMoment dimension α β := by
  intro dimension
  have hiterate : ∀ n (left right : Multiset ℕ), 0 ∉ left → 0 ∉ right →
      facMomentNat n left right = ((nilOperator + 1) ^ n) nilBase left right := by
    intro n
    induction n with
    | zero =>
        intro left right hleft hright
        simpa [nilBase] using facMomentNat_zero left right hleft hright
    | succ n inductionHypothesis =>
        intro left right hleft hright
        rw [facMomentNat_succ hleft hright]
        calc
          (∑ x ∈ insert 0 left.toFinset, ∑ y ∈ insert 0 right.toFinset,
              (x + y)! * facMomentNat n (left.erase x) (right.erase y)) =
              ∑ x ∈ insert 0 left.toFinset, ∑ y ∈ insert 0 right.toFinset,
                (x + y)! * ((nilOperator + 1) ^ n) nilBase
                  (left.erase x) (right.erase y) := by
            refine sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ ?_
            rw [inductionHypothesis (left.erase x) (right.erase y)
              (fun h ↦ hleft (Multiset.mem_of_mem_erase h))
              (fun h ↦ hright (Multiset.mem_of_mem_erase h))]
          _ = ((nilOperator + 1) ^ n) nilBase left right +
              nilStep (((nilOperator + 1) ^ n) nilBase) left right :=
            fullStep_eq_add_nilStep _ hleft hright
          _ = (nilOperator + 1) (((nilOperator + 1) ^ n) nilBase) left right :=
            Nat.add_comm _ _
          _ = ((nilOperator + 1) ^ (n + 1)) nilBase left right := by
            rw [pow_succ']
            rfl
  rw [hiterate dimension α β hα hβ]
  have hbinomial := congrArg (fun operator : AddMonoid.End MomentState ↦
    operator nilBase α β) ((Commute.one_right nilOperator).add_pow dimension)
  have sum_apply (indices : Finset ℕ) (operator : ℕ → AddMonoid.End MomentState) :
      (∑ r ∈ indices, operator r) nilBase α β = ∑ r ∈ indices, operator r nilBase α β := by
    induction indices using Finset.induction_on with
    | empty => rfl
    | @insert r indices hr inductionHypothesis =>
        rw [sum_insert hr, sum_insert hr]
        calc
          (operator r + ∑ i ∈ indices, operator i) nilBase α β =
              operator r nilBase α β + (∑ i ∈ indices, operator i) nilBase α β :=
            congrArg (fun state : MomentState ↦ state α β)
              (AddMonoidHom.add_apply (operator r) (∑ i ∈ indices, operator i) nilBase)
          _ = operator r nilBase α β + ∑ i ∈ indices, operator i nilBase α β := by
            rw [inductionHypothesis]
  calc
    ((nilOperator + 1) ^ dimension) nilBase α β =
        (∑ r ∈ range (dimension + 1),
          nilOperator ^ r * ↑(dimension.choose r)) nilBase α β := by
      simpa only [one_pow, mul_one] using hbinomial
    _ = binomialMoment dimension α β := by
      rw [binomialMoment, sum_apply]
      refine sum_congr rfl fun r _ ↦ ?_
      rw [congrFun
          (AddMonoid.End.coe_mul MomentState (nilOperator ^ r) (↑(dimension.choose r))) nilBase,
        Function.comp_apply, AddMonoid.End.natCast_apply, map_nsmul]
      rfl

end PrimeGaps.Gap246
