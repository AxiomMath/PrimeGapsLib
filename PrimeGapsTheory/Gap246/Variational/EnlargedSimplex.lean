/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Analysis.Simplex

/-!
# The ε-enlarged and ε-shrunken simplices

This file introduces the geometric objects of the ε-enlarged-simplex variational
problem built over the Maynard-600 development.  Everything is stated
parametric in `(k, ε)`; setting `ε = 0` recovers the 600 objects, which is both
the specification and a consistency check (`enlargedSimplex_zero`,
`shrunkenSlice_zero`).

* `enlargedSimplex k ε` — the enlarged region `𝒯_ε` (`def_enl`).
* `shrunkenSlice k ε` — the shrunken `(k-1)`-slice `𝒮_ε` (`def_shr`).
-/

@[expose] public section

open EuclideanSpace
open scoped PrimeGaps

namespace Gaps246

/-- **`def_enl`.** The ε-enlarged simplex `𝒯_ε ⊆ ES(ℝ, k)`: the corner region with
the total-mass bound relaxed from `1` to `1 + ε`.  At `ε = 0` this is `𝓡 k`. -/
def enlargedSimplex (k : ℕ) (ε : ℝ) : Set (EuclideanSpace ℝ (Fin k)) := 𝓡(k, 1 + ε)

/-- **`def_shr`.** The ε-shrunken `(k-1)`-slice `𝒮_ε ⊆ ES(ℝ, k-1)`: the corner region
with the total-mass bound tightened from `1` to `1 - ε`.  At `ε = 0` this is `𝓡 (k-1)`. -/
def shrunkenSlice (k : ℕ) (ε : ℝ) : Set (EuclideanSpace ℝ (Fin (k - 1))) := 𝓡(k - 1, 1 - ε)

/-- **Recovery.** At `ε = 0` the enlarged simplex is `𝓡 k`. -/
theorem enlargedSimplex_zero (k : ℕ) : enlargedSimplex k 0 = 𝓡 k := by
  ext x
  simp [enlargedSimplex, EuclideanSpace.scaledStdSimplex]

/-- **Recovery.** At `ε = 0` the shrunken slice is `𝓡 (k-1)`. -/
theorem shrunkenSlice_zero (k : ℕ) : shrunkenSlice k 0 = 𝓡 (k - 1) := by
  ext x
  simp [shrunkenSlice, EuclideanSpace.scaledStdSimplex]

open scoped Pointwise

/-- For a positive scale, the corner region of that total mass is the homothetic image of the
standard simplex. -/
theorem smul_stdSimplex (n : ℕ) {c : ℝ} (hc : 0 < c) : c • 𝓡 n = 𝓡(n, c) := by
  ext y
  simp only [Set.mem_smul_set, EuclideanSpace.scaledStdSimplex, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, ⟨hx0, hx1⟩, rfl⟩
    refine ⟨fun i ↦ ?_, ?_⟩
    · rw [PiLp.smul_apply, smul_eq_mul]
      exact mul_nonneg hc.le (hx0 i)
    · have hsum : ∑ i, (c • x) i = c * ∑ i, x i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [PiLp.smul_apply, smul_eq_mul]
      rw [hsum]
      calc c * ∑ i, x i ≤ c * 1 := mul_le_mul_of_nonneg_left hx1 hc.le
        _ = c := mul_one _
  · rintro ⟨hy0, hy1⟩
    refine ⟨c⁻¹ • y, ⟨fun i ↦ ?_, ?_⟩, ?_⟩
    · rw [PiLp.smul_apply, smul_eq_mul]
      exact mul_nonneg (inv_pos.mpr hc).le (hy0 i)
    · have hsum : ∑ i, (c⁻¹ • y) i = c⁻¹ * ∑ i, y i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [PiLp.smul_apply, smul_eq_mul]
      rw [hsum]
      have hbound := mul_le_mul_of_nonneg_left hy1 (inv_pos.mpr hc).le
      rwa [inv_mul_cancel₀ (ne_of_gt hc)] at hbound
    · rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hc), one_smul]

/-- A positive shrunken simplex is the scalar image of the standard simplex. -/
theorem shrunkenSlice_eq_smul (k : ℕ) (ε : ℝ) (hε1 : 0 < 1 - ε) :
    (1 - ε) • 𝓡 (k - 1) = shrunkenSlice k ε :=
  smul_stdSimplex (k - 1) hε1

/-- A shrunken simplex with positive scale is compact. -/
theorem isCompact_shrunkenSlice (k : ℕ) (ε : ℝ) (hε1 : 0 < 1 - ε) :
    IsCompact (shrunkenSlice k ε) := by
  rw [← shrunkenSlice_eq_smul k ε hε1]
  exact isCompact_scaledStdSimplex.smul (1 - ε)

/-- The enlarged simplex is the homothetic image `(1+ε) • 𝓡 k`. -/
theorem enlargedSimplex_eq_smul (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    (1 + ε) • 𝓡 k = enlargedSimplex k ε :=
  smul_stdSimplex k (by linarith)

/-- The enlarged simplex is compact. -/
theorem isCompact_enlargedSimplex (k : ℕ) (ε : ℝ) : IsCompact (enlargedSimplex k ε) :=
  isCompact_scaledStdSimplex

/-- The enlarged simplex is closed. -/
theorem isClosed_enlargedSimplex (k : ℕ) (ε : ℝ) : IsClosed (enlargedSimplex k ε) :=
  isClosed_scaledStdSimplex

end Gaps246
