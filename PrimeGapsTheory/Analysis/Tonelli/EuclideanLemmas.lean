/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace


/-! # Measure-preserving maps between Euclidean spaces

Equivalences of Euclidean spaces that isolate or split off coordinates, and the fact that they
preserve Lebesgue measure. These are the change-of-variables maps used to apply Tonelli's theorem
in Euclidean coordinates.
-/

@[expose] public section

open Fin MeasureTheory EuclideanSpace

local notation "ES(" 𝕜:65 ", " k:65 ")" => EuclideanSpace 𝕜 (Fin k)

namespace Fin

/-- Isolate a chosen `k : Fin n`. -/
def finIsolateEquivSum {n : ℕ} (k : Fin n) : Fin n ≃ Fin (n - 1) ⊕ Fin 1 where
  toFun i := if h : i = k then .inr 0 else .inl ⟨if i < k then i else i - 1, by grind⟩
  invFun i := i.elim (fun j : Fin (n - 1) ↦ ⟨if (j : ℕ) < k then j else j + 1, by grind⟩) ![k]
  left_inv i := by
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, isValue]
    split_ifs <;> simp <;> grind
  right_inv i := by
    cases i
    · simp [Fin.ext_iff]
      grind
    · simp [Subsingleton.elim (α := Fin 1) _ 0]

end Fin

namespace EuclideanSpace

/-- Isolate a chosen `k : Fin n`. -/
noncomputable def finIsolateEquivProd (𝕜 : Type*) [RCLike 𝕜] {n : ℕ} (k : Fin n) :
    ES(𝕜, n) ≃L[𝕜] ES(𝕜, n - 1) × ES(𝕜, 1) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 (finIsolateEquivSum k)).toContinuousLinearEquiv.trans
    sumEquivProd

theorem measurePreserving_sumEquivProd {ι κ : Type*} [Fintype ι] [Fintype κ] :
    MeasurePreserving (sumEquivProd (𝕜 := ℝ) (ι := ι) (κ := κ)) volume volume :=
  have h₁ : MeasurePreserving
      (WithLp.prodContinuousLinearEquiv 2 ℝ (WithLp 2 (ι → ℝ)) (WithLp 2 (κ → ℝ)))
      volume volume :=
    WithLp.volume_preserving_ofLp (WithLp 2 (ι → ℝ)) (WithLp 2 (κ → ℝ))
  have h₂ : MeasurePreserving (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : ι ⊕ κ ↦ ℝ)) volume volume :=
    LinearIsometryEquiv.measurePreserving _
  h₁.comp h₂

theorem measurePreserving_finAddEquivProd {n m : ℕ} :
    MeasurePreserving (finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)) volume volume :=
  measurePreserving_sumEquivProd.comp (LinearIsometryEquiv.measurePreserving _)

theorem measurePreserving_finIsolateEquivProd {n : ℕ} (k : Fin n) :
    MeasurePreserving (finIsolateEquivProd ℝ k) volume volume :=
  measurePreserving_sumEquivProd.comp
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finIsolateEquivSum k)).measurePreserving

theorem measurePreserving_symm_finIsolateEquivProd {n : ℕ} (k : Fin n) :
    MeasurePreserving (finIsolateEquivProd ℝ k).symm volume volume :=
  (measurePreserving_finIsolateEquivProd k).symm
    (finIsolateEquivProd ℝ k).toHomeomorph.toMeasurableEquiv

end EuclideanSpace
