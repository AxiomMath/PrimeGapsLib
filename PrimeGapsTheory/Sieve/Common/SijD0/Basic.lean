/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Product factorizations for off-diagonal sums

Proves product and matrix-block factorizations for sums indexed by finite tuples.

## Main results

* `tsum_prod_of_summable`: Factors a summable tuple product into coordinate sums.
* `pinned_block_factor`: Factors a tuple-indexed sum whose slots outside a given `Finset` are
  pinned to the `n = 1` indicator.
* `matrix_block_factor`: Factors a matrix-indexed sum with a distinguished off-diagonal pair.
-/

@[expose] public section

open scoped Finset


namespace SijD0

open scoped ENNReal

/-- A pointwise product majorant bounds a doubly-indexed `tsum` by the product of the two block
`tsum` s. This is the final step of the off-diagonal master bound in either moment: a summand
guarded by `D₀ < s i j` is dominated coordinatewise by `Y · Pu u · Ps s`, and the double sum is
then bounded by `Y` times the `u` -block sum times the `s` -block sum. -/
theorem tsum_tsum_le_of_prod_majorant {α β : Type*} (F : α → β → ℝ) (Y : ℝ)
    (Pu : α → ℝ) (Ps : β → ℝ) (hFnn : ∀ u s, 0 ≤ F u s)
    (hle : ∀ u s, F u s ≤ Y * Pu u * Ps s)
    (hsu : Summable Pu) (hss : Summable Ps) :
    (∑' u, ∑' s, F u s) ≤ Y * (∑' u, Pu u) * ∑' s, Ps s := by
  have hinnerSummable : ∀ u, Summable (F u) := fun u ↦
    Summable.of_nonneg_of_le (hFnn u) (hle u) (hss.mul_left (Y * Pu u))
  have hinner : ∀ u, (∑' s, F u s) ≤ Y * Pu u * ∑' s, Ps s := fun u ↦
    (Summable.tsum_le_tsum (hle u) (hinnerSummable u) (hss.mul_left _)).trans_eq tsum_mul_left
  have hmaj : Summable fun u ↦ Y * Pu u * ∑' s, Ps s := (hsu.mul_left Y).mul_right _
  have houter : Summable fun u ↦ ∑' s, F u s :=
    Summable.of_nonneg_of_le (fun u ↦ tsum_nonneg (hFnn u)) hinner hmaj
  refine (Summable.tsum_le_tsum hinner houter hmaj).trans_eq ?_
  rw [tsum_mul_right, tsum_mul_left]

/-- For an arbitrary `Fintype` index and nonnegative-extended-real coordinate weights, the `tsum`
over the pi-type of the coordinatewise product equals the product of coordinatewise `tsum` s.
-/
theorem ennreal_box {ι : Type*} [Fintype ι] (G : ι → ℕ → ℝ≥0∞) :
    (∑' f : ι → ℕ, ∏ i, G i (f i)) = ∏ i, ∑' n, G i n := by
  classical
  revert G
  refine Fintype.induction_empty_option
    (P := fun α _ ↦ ∀ (G : α → ℕ → ℝ≥0∞), (∑' f : α → ℕ, ∏ i, G i (f i)) = ∏ i, ∑' n, G i n)
    ?_ ?_ ?_ ι
  · intro α β _ e ih G
    haveI : Fintype α := Fintype.ofEquiv β e.symm
    rw [← (e.arrowCongr (Equiv.refl ℕ)).tsum_eq (fun f ↦ ∏ i, G i (f i))]
    have hfun : ∀ g : α → ℕ,
        (∏ i, G i ((e.arrowCongr (Equiv.refl ℕ)) g i)) = ∏ a, G (e a) (g a) := by
      intro g
      rw [← Equiv.prod_comp e (fun i ↦ G i ((e.arrowCongr (Equiv.refl ℕ)) g i))]
      exact Finset.prod_congr rfl (by simp [Equiv.arrowCongr])
    simp_rw [hfun]
    have hih := ih (fun a ↦ G (e a))
    rw [← Equiv.prod_comp e (fun i ↦ ∑' n, G i n)]
    rw [Subsingleton.elim (Fintype.ofEquiv β e.symm) this] at hih
    exact hih
  · intro G
    rw [Finset.univ_eq_empty, Finset.prod_empty, tsum_eq_single (fun _ ↦ 0)]
    · rw [Finset.prod_empty]
    · intro f hf
      exact absurd (Subsingleton.elim f (fun _ ↦ 0)) hf
  · intro α _ ih G
    rw [← (Equiv.piOptionEquivProd (β := fun _ : Option α ↦ ℕ)).symm.tsum_eq]
    have hfun : ∀ p : ℕ × (α → ℕ),
        (∏ i, G i ((Equiv.piOptionEquivProd (β := fun _ : Option α ↦ ℕ)).symm p i)) =
          G none p.1 * ∏ a, G (some a) (p.2 a) := by
      intro p
      rw [Fintype.prod_option]
      rfl
    simp_rw [hfun]
    rw [ENNReal.tsum_prod']
    have : (∑' (a : ℕ) (b : α → ℕ), G none a * ∏ x, G (some x) (b x)) =
        ∑' (a : ℕ), G none a * (∑' b : α → ℕ, ∏ x, G (some x) (b x)) :=
      tsum_congr fun n ↦ ENNReal.tsum_mul_left
    rw [this, ih (fun a ↦ G (some a)), ENNReal.tsum_mul_right, Fintype.prod_option]

/-- Real-valued box factorizer for nonnegative summable coordinate weights:
`∑' f, ∏ i, g i (f i) = ∏ i, ∑' n, g i n`. No bounded-support assumption is needed, only
per-coordinate summability.
-/
theorem tsum_prod_of_summable {ι : Type*} [Fintype ι] (g : ι → ℕ → ℝ)
    (hnn : ∀ i n, 0 ≤ g i n) (hsum : ∀ i, Summable (g i)) :
    (∑' f : ι → ℕ, ∏ i, g i (f i)) = ∏ i, ∑' n, g i n := by
  classical
  set G : ι → ℕ → ℝ≥0∞ := fun i n ↦ ENNReal.ofReal (g i n) with hG
  have hcoord : ∀ i, (∑' n, G i n) = ENNReal.ofReal (∑' n, g i n) := fun i ↦
    (ENNReal.ofReal_tsum_of_nonneg (hnn i) (hsum i)).symm
  have hprodfin : ∀ f : ι → ℕ, (∏ i, G i (f i)) = ENNReal.ofReal (∏ i, g i (f i)) := fun f ↦ by
    rw [hG, ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ hnn i (f i))]
  have hprod_ne_top : ∀ f : ι → ℕ, (∏ i, G i (f i)) ≠ ⊤ := fun f ↦ by
    rw [hprodfin f]; exact ENNReal.ofReal_ne_top
  have key : (∑' f : ι → ℕ, ∏ i, G i (f i)).toReal = (∏ i, ∑' n, G i n).toReal := by
    rw [ennreal_box G]
  rw [ENNReal.tsum_toReal_eq hprod_ne_top] at key
  have hLHSterm : ∀ f : ι → ℕ, (∏ i, G i (f i)).toReal = ∏ i, g i (f i) := fun f ↦ by
    rw [hprodfin f, ENNReal.toReal_ofReal (Finset.prod_nonneg (fun i _ ↦ hnn i (f i)))]
  simp_rw [hLHSterm] at key
  rw [ENNReal.toReal_prod] at key
  have hRHSterm : ∀ i, (∑' n, G i n).toReal = ∑' n, g i n := fun i ↦ by
    rw [hcoord i, ENNReal.toReal_ofReal (tsum_nonneg (hnn i))]
  simp_rw [hRHSterm] at key
  exact key

/-- Summability of a box product from per-coordinate nonneg summability. -/
theorem summable_prod_of_summable {ι : Type*} [Fintype ι] (g : ι → ℕ → ℝ)
    (hnn : ∀ i n, 0 ≤ g i n) (hsum : ∀ i, Summable (g i)) :
    Summable (fun f : ι → ℕ ↦ ∏ i, g i (f i)) := by
  classical
  set G : ι → ℕ → ℝ≥0∞ := fun i n ↦ ENNReal.ofReal (g i n) with hG
  have hcoord : ∀ i, (∑' n, G i n) = ENNReal.ofReal (∑' n, g i n) := fun i ↦
    (ENNReal.ofReal_tsum_of_nonneg (hnn i) (hsum i)).symm
  have hRHS_ne_top : (∏ i, ∑' n, G i n) ≠ ⊤ := by
    apply ENNReal.prod_ne_top
    intro i _; rw [hcoord i]; exact ENNReal.ofReal_ne_top
  have hLHS_ne_top : (∑' f : ι → ℕ, ∏ i, G i (f i)) ≠ ⊤ := by
    rw [ennreal_box G]; exact hRHS_ne_top
  have hprodfin : ∀ f : ι → ℕ, (∏ i, G i (f i)) = ENNReal.ofReal (∏ i, g i (f i)) := fun f ↦ by
    rw [hG, ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ hnn i (f i))]
  have hsummableNN : Summable (ENNReal.toNNReal ∘ (fun f : ι → ℕ ↦ ∏ i, G i (f i))) :=
    ENNReal.summable_toNNReal_of_tsum_ne_top hLHS_ne_top
  have heq : (fun f : ι → ℕ ↦ ∏ i, g i (f i)) =
      (fun f : ι → ℕ ↦ ((ENNReal.toNNReal ((fun f : ι → ℕ ↦ ∏ i, G i (f i)) f)) : ℝ)) := by
    funext f
    change ∏ i, g i (f i) = ((ENNReal.toNNReal (∏ i, G i (f i))) : ℝ)
    rw [show ((ENNReal.toNNReal (∏ i, G i (f i))) : ℝ) = (∏ i, G i (f i)).toReal from rfl,
      hprodfin f, ENNReal.toReal_ofReal (Finset.prod_nonneg (fun i _ ↦ hnn i (f i)))]
  rw [heq]
  exact (NNReal.summable_coe.mpr hsummableNN)

/-- If each per-coordinate function `g i` has support inside the box `[0, M]`, then the tsum over
the pi-type of the coordinatewise product equals the product of the coordinatewise tsums. (No
nonnegativity needed.)
-/
theorem tsum_prod_of_box {ι : Type*} [Fintype ι] (M : ℕ) (g : ι → ℕ → ℝ)
    (hsupp : ∀ i n, g i n ≠ 0 → n ≤ M) :
    ∑' f : ι → ℕ, ∏ i, g i (f i) = ∏ i, ∑' n : ℕ, g i n := by
  classical
  have hbox : ∑' f : ι → ℕ, ∏ i, g i (f i) =
      ∑ f ∈ Fintype.piFinset (fun _ : ι ↦ Finset.Iic M), ∏ i, g i (f i) := by
    apply tsum_eq_sum
    intro f hf
    rw [Fintype.mem_piFinset] at hf
    push Not at hf
    obtain ⟨i₀, hi₀⟩ := hf
    rw [Finset.mem_Iic] at hi₀
    apply Finset.prod_eq_zero (Finset.mem_univ i₀)
    by_contra hne
    exact hi₀ (hsupp i₀ (f i₀) hne)
  rw [hbox, Finset.sum_prod_piFinset (Finset.Iic M) g]
  apply Finset.prod_congr rfl
  intro i _
  symm
  apply tsum_eq_sum
  intro n hn
  rw [Finset.mem_Iic] at hn
  by_contra hne
  exact hn (hsupp i n hne)

/-- A real weight on `ℕ` whose support lies in `[0, M]` is summable. -/
theorem summable_of_support_le {M : ℕ} {w : ℕ → ℝ} (hw : ∀ n, w n ≠ 0 → n ≤ M) : Summable w :=
  summable_of_hasFiniteSupport <| Set.Finite.subset (Finset.Iic M).finite_toSet fun n hn ↦ by
    simpa using hw n (Function.mem_support.mp hn)

/-- A box weight carrying a weight `w` supported in `[0, M]` on the slots of `S` and the `n = 1`
indicator on the slots outside `S` has all its coordinate supports inside `[0, max M 1]`. -/
theorem pinned_support {ι : Type*} {M : ℕ} {S : Finset ι} {G : ι → ℕ → ℝ} {w : ℕ → ℝ}
    (hw : ∀ n, w n ≠ 0 → n ≤ M) (hGon : ∀ a ∈ S, ∀ n, G a n = w n)
    (hGpin : ∀ a ∉ S, ∀ n, G a n = if n = 1 then (1 : ℝ) else 0)
    (a : ι) (n : ℕ) (hn : G a n ≠ 0) : n ≤ max M 1 := by
  by_cases ha : a ∈ S
  · rw [hGon a ha n] at hn; exact (hw n hn).trans (le_max_left _ _)
  · rw [hGpin a ha n] at hn
    by_cases hn1 : n = 1
    · exact hn1.le.trans (le_max_right M 1)
    · exact absurd (if_neg hn1) hn

/-- A box weight carrying the one-dimensional weight `w` on the slots of `S` and the `n = 1`
indicator on the remaining, pinned slots has `tsum` over `u : ι → ℕ` of the coordinatewise product
equal to `(∑' w) ^ S.card`, each pinned slot contributing `1`. The first moment instantiates this at
`S = univ`, the second — whose weight is pinned at its distinguished coordinate `m` — at
`S = univ.erase m`, so the exponents are `card ι` and `card ι - 1`. -/
theorem pinned_block_factor {ι : Type*} [Fintype ι] {M : ℕ} (S : Finset ι) (G : ι → ℕ → ℝ)
    (w : ℕ → ℝ) (hw : ∀ n, w n ≠ 0 → n ≤ M) (hGon : ∀ a ∈ S, ∀ n, G a n = w n)
    (hGpin : ∀ a ∉ S, ∀ n, G a n = if n = 1 then (1 : ℝ) else 0) :
    (∑' u : ι → ℕ, ∏ a, G a (u a)) = (∑' n : ℕ, w n) ^ #S := by
  classical
  rw [tsum_prod_of_box (max M 1) G (pinned_support hw hGon hGpin),
    ← Finset.prod_sdiff (Finset.subset_univ S)]
  have hpin : (∏ a ∈ Finset.univ \ S, ∑' n : ℕ, G a n) = 1 :=
    Finset.prod_eq_one fun a ha ↦ (tsum_congr (hGpin a (Finset.mem_sdiff.mp ha).2)).trans
      (tsum_ite_eq 1 fun _ ↦ (1 : ℝ))
  have hon : (∏ a ∈ S, ∑' n : ℕ, G a n) = (∑' n : ℕ, w n) ^ #S := by
    rw [Finset.prod_congr rfl fun a ha ↦ tsum_congr (hGon a ha), Finset.prod_const]
  rw [hpin, hon, one_mul]

variable {k : ℕ}

/-- The ordered pair `(i,j)` with `i ≠ j` lies in the off-diagonal. -/
theorem mem_offDiag_pair (i j : Fin k) (hij : i ≠ j) :
    (i, j) ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)) := by
  rw [Finset.mem_offDiag]; exact ⟨Finset.mem_univ _, Finset.mem_univ _, hij⟩

/-- Removing the distinguished pair `(i,j)` from the `k(k-1)` -element off-diagonal leaves `k²-k-1`
elements.
-/
theorem offDiag_erase_card (i j : Fin k) (hij : i ≠ j) :
    #((Finset.univ.offDiag : Finset (Fin k × Fin k)).erase (i, j)) = k ^ 2 - k - 1 := by
  rw [Finset.card_erase_of_mem (mem_offDiag_pair i j hij), Finset.offDiag_card,
      Finset.card_univ, Fintype.card_fin, pow_two]

/-- Let `G: (Fin k × Fin k) → ℕ → ℝ` be a nonnegative, per-coordinate summable box weight whose
distinguished off-diagonal slot `(i,j)` carries the one-dimensional weight `wij`, whose remaining
off-diagonal slots carry `ws0`, and whose diagonal slots are pinned to the `n = 1` indicator. Then
the double `tsum` over the matrix `s: Fin k → Fin k → ℕ` of the box product factors as
`(∑' wij) · (∑' ws0) ^ (k²−k−1)`.
-/
theorem matrix_block_factor (i j : Fin k) (hij : i ≠ j) (G : (Fin k × Fin k) → ℕ → ℝ)
    (hnn : ∀ p n, 0 ≤ G p n) (hsum : ∀ p, Summable (G p))
    (wij ws0 : ℕ → ℝ)
    (hGij : ∀ n, G (i, j) n = wij n)
    (hGoff : ∀ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)).erase (i, j), ∀ n, G p n = ws0 n)
    (hGdiag : ∀ p ∉ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
      ∀ n, G p n = if n = 1 then (1 : ℝ) else 0) :
    (∑' s : Fin k → Fin k → ℕ, ∏ p : Fin k × Fin k, G p (s p.1 p.2)) =
      (∑' n : ℕ, wij n) * (∑' n : ℕ, ws0 n) ^ (k ^ 2 - k - 1) := by
  classical
  have hreindex : (∑' s : Fin k → Fin k → ℕ, ∏ p : Fin k × Fin k, G p (s p.1 p.2)) =
      (∑' t : Fin k × Fin k → ℕ, ∏ p : Fin k × Fin k, G p (t p)) := by
    rw [← (Equiv.curry (Fin k) (Fin k) ℕ).symm.tsum_eq (fun t ↦ ∏ p : Fin k × Fin k, G p (t p))]
    apply tsum_congr; intro s; apply Finset.prod_congr rfl; intro p _; rfl
  rw [hreindex, tsum_prod_of_summable G hnn hsum]
  rw [show (Finset.univ : Finset (Fin k × Fin k)) =
        Finset.univ.offDiag ∪ (Finset.univ \ Finset.univ.offDiag) by
      rw [Finset.union_sdiff_of_subset (Finset.subset_univ _)]]
  rw [Finset.prod_union (Finset.disjoint_sdiff)]
  have hcompl : (∏ p ∈ Finset.univ \ Finset.univ.offDiag, (∑' n : ℕ, G p n)) = 1 := by
    apply Finset.prod_eq_one
    intro p hp
    rw [Finset.mem_sdiff] at hp
    exact (tsum_congr (hGdiag p hp.2)).trans (tsum_ite_eq 1 fun _ ↦ (1 : ℝ))
  rw [hcompl, mul_one, ← Finset.prod_erase_mul _ _ (mem_offDiag_pair i j hij)]
  have herase : (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)).erase (i, j),
        (∑' n : ℕ, G p n)) = (∑' n : ℕ, ws0 n) ^ (k ^ 2 - k - 1) := by
    rw [Finset.prod_congr rfl (fun p hp ↦ tsum_congr (fun n ↦ hGoff p hp n)),
      Finset.prod_const, offDiag_erase_card i j hij]
  rw [herase, tsum_congr hGij, mul_comm]

end SijD0

end
