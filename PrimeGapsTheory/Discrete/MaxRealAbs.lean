/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import PrimeGapsTheory.ForMathlib.Data.Finsupp.Basic

import PrimeGapsTheory.Tactic.PaperTag

/-!
# The largest absolute value of a finite family of reals

We define `Finset.maxRealAbs s`, the maximum of `|x|` over `x ∈ s`, and its `Finsupp` analogue
`Finsupp.maxRealAbs f`, the maximum of `|f x|`. Both are `0` on the empty family, and
`Finsupp.iSup_abs_eq_maxRealAbs` identifies the latter with `⨆ x, |f x|`.
-/

@[expose] public section

open Real

namespace Finset

/-- The max of `{|x| : x ∈ s}` for `s : Finset ℝ`. -/
def maxRealAbs (s : Finset ℝ) : ℝ := (s.sup fun r ↦ ‖r‖₊).toReal

variable {s : Finset ℝ} {x : ℝ}

@[simp] theorem maxRealAbs_empty : maxRealAbs ∅ = 0 := by norm_cast

@[simp] theorem le_maxRealAbs (hx : x ∈ s) : |x| ≤ s.maxRealAbs := by
  rw [← norm_eq_abs, ← coe_nnnorm]
  exact NNReal.coe_le_coe.mpr <| s.le_sup hx

@[simp] theorem maxRealAbs_nonneg : 0 ≤ s.maxRealAbs := NNReal.zero_le_coe

@[simp] theorem maxRealAbs_le_iff (hx : 0 ≤ x) : s.maxRealAbs ≤ x ↔ ∀ y ∈ s, |y| ≤ x := by
  lift x to NNReal using hx
  simp_rw [maxRealAbs, NNReal.coe_le_coe, Finset.sup_le_iff, ← NNReal.coe_le_coe,
    coe_nnnorm, Real.norm_eq_abs]

@[simp] theorem maxRealAbs_le_iff' (hs : s.Nonempty) : s.maxRealAbs ≤ x ↔ ∀ y ∈ s, |y| ≤ x := by
  obtain hx | hx := lt_or_ge x 0
  · obtain ⟨y, hys⟩ := hs
    exact iff_of_false (by linarith [s.maxRealAbs_nonneg]) fun H ↦ hx.not_ge <|
      (abs_nonneg y).trans <| H y hys
  exact maxRealAbs_le_iff hx

end Finset

namespace Finsupp

/-- The max of `|f(x)|` for a `Finsupp` `f`. -/
@[pg_tag "bg246" "def_y_max", pg_tag "bg246" "def_ym_max"]
def maxRealAbs {α : Type*} (f : α →₀ ℝ) : ℝ := (f.support.sup fun x ↦ ‖f x‖₊).toReal

variable {α : Type*} {f : α →₀ ℝ} {x : α}

@[simp] theorem maxRealAbs_zero : maxRealAbs (0 : α →₀ ℝ) = 0 := by norm_cast

@[simp] theorem maxRealAbs_frange_eq_maxRealAbs : f.frange.maxRealAbs = f.maxRealAbs :=
  congrArg NNReal.toReal <| Finset.sup_image _ _ _

@[pg_tag "bg246" "def_y_max", pg_tag "bg246" "def_ym_max", simp]
theorem le_maxRealAbs : |f x| ≤ f.maxRealAbs := by
  rw [← maxRealAbs_frange_eq_maxRealAbs]
  by_cases hfx : f x = 0
  · simp [hfx, -maxRealAbs_frange_eq_maxRealAbs]
  exact Finset.le_maxRealAbs <| by simpa

@[simp] theorem maxRealAbs_nonneg : 0 ≤ f.maxRealAbs := NNReal.zero_le_coe

@[simp] theorem maxRealAbs_le_iff' {M : ℝ} (hf : f ≠ 0) : f.maxRealAbs ≤ M ↔ ∀ x, |f x| ≤ M := by
  rw [← maxRealAbs_frange_eq_maxRealAbs, Finset.maxRealAbs_le_iff' (by simpa)]
  simp only [mem_frange, Set.mem_range, and_imp, forall_exists_index]
  grind

@[pg_tag "bg246" "def_y_max", pg_tag "bg246" "def_ym_max", simp]
theorem maxRealAbs_le_iff {M : ℝ} [Nonempty α] : f.maxRealAbs ≤ M ↔ ∀ x, |f x| ≤ M :=
  by_cases (by simp +contextual) maxRealAbs_le_iff'

/-- The `Finsupp` max-abs equals the supremum of `|f x|` over the whole index type. -/
theorem iSup_abs_eq_maxRealAbs [Nonempty α] : ⨆ x, |f x| = f.maxRealAbs := by
  have hbdd : BddAbove (Set.range fun x ↦ |f x|) :=
    ⟨f.maxRealAbs, Set.forall_mem_range.2 fun _ ↦ le_maxRealAbs⟩
  refine le_antisymm (ciSup_le fun x ↦ le_maxRealAbs) ?_
  rw [maxRealAbs_le_iff]
  exact fun x ↦ le_ciSup hbdd x

end Finsupp
