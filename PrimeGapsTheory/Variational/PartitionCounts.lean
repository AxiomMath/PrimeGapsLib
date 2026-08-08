/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import PrimeGapsTheory.Sieve.MaynardG
import PrimeGapsTheory.Tactic.PaperTag

/-!
# Support stratification of `piAntidiag` sums

Sums over tuples with a fixed total can be regrouped according to the size of their positive
support.

## Main definitions

* `posSum`: The weighted sum over positive tuples with a fixed total.

## Main results

* `lem_partition_count`: The factorial-weighted support-stratification identity.
* `lem_partition_count_piantidiag_support`: The general weighted support-stratification identity.
* `lem_multinomial_Pj`: The multinomial expansion of `(∑ i, t i ^ j) ^ b`.
-/

@[expose] public section

open scoped Finset
open scoped Nat


open Finset

namespace PrimeGaps

/-- A tuple with positive total has at least one positive entry. -/
private lemma one_le_hammingNorm_of_sum_pos {k : ℕ} (b_vec : Fin k → ℕ)
    (h : 1 ≤ ∑ i, b_vec i) : 1 ≤ hammingNorm b_vec :=
  hammingNorm_pos_iff.mpr fun h0 ↦ by simp [h0] at h

/-- For `b_vec ∈ piAntidiag univ b` with `b ≥ 1`, the Hamming norm lies in `[1, b]`. -/
private lemma hammingNorm_mem_Icc (k b : ℕ) (hb : 1 ≤ b) (b_vec : Fin k → ℕ)
    (h : b_vec ∈ ((Finset.univ : Finset (Fin k)).piAntidiag b)) :
    hammingNorm b_vec ∈ Finset.Icc 1 b := by
  rw [Finset.mem_piAntidiag] at h
  obtain ⟨hsum, _⟩ := h
  rw [Finset.mem_Icc]
  exact ⟨one_le_hammingNorm_of_sum_pos b_vec (hsum ▸ hb),
    hsum ▸ MaynardGOpt.hammingNorm_le_sum b_vec⟩

/-- Extends `c : Fin r → ℕ` by zero outside `S`. -/
private noncomputable def fwdF {k r : ℕ} (S : Finset (Fin k)) (hS : #S = r)
    (c : Fin r → ℕ) : Fin k → ℕ :=
  fun i ↦ if h : i ∈ S then c (Finset.equivFinOfCardEq hS ⟨i, h⟩) else 0

/-- Restricts `b_vec : Fin k → ℕ` to `S` through the equivalence induced by `hS`. -/
private noncomputable def bwdF {k r : ℕ} (S : Finset (Fin k)) (hS : #S = r)
    (b_vec : Fin k → ℕ) : Fin r → ℕ :=
  fun j ↦ b_vec ((Finset.equivFinOfCardEq hS).symm j : Fin k)

/-- `fwdF S hS c` vanishes off `S`. -/
private lemma fwdF_eq_zero_of_not_mem {k r : ℕ} (S : Finset (Fin k)) (hS : #S = r)
    (c : Fin r → ℕ) (i : Fin k) (h : i ∉ S) : fwdF S hS c i = 0 :=
  dif_neg h

/-- On `S`, `fwdF S hS c` reads off the corresponding entry of `c`. -/
private lemma fwdF_eq_of_mem {k r : ℕ} (S : Finset (Fin k)) (hS : #S = r)
    (c : Fin r → ℕ) (i : Fin k) (h : i ∈ S) :
    fwdF S hS c i = c (Finset.equivFinOfCardEq hS ⟨i, h⟩) :=
  dif_pos h

/-- The sum of `bwdF S hS b_vec` over `Fin r` equals the sum of `b_vec` over `Fin k`,
    given that the support of `b_vec` equals `S`. -/
private lemma bwdF_sum_eq {k r : ℕ} (S : Finset (Fin k)) (hS : #S = r) (b_vec : Fin k → ℕ)
    (hsupp : {i ∈ (Finset.univ : Finset (Fin k)) | 0 < b_vec i} = S) :
    ∑ j, bwdF S hS b_vec j = ∑ i, b_vec i := by
  rw [show ∑ j, bwdF S hS b_vec j = ∑ i ∈ S, b_vec i from
        (MaynardGOpt.sum_eq_sum_equivFin hS b_vec).symm,
      show ∑ i, b_vec i = ∑ i ∈ S, b_vec i by
        rw [← hsupp]
        exact (Finset.sum_filter_of_ne fun i _ hne ↦ Nat.pos_of_ne_zero hne).symm]

/-- If the support of `b_vec` is exactly `S`, then `bwdF S hS b_vec` is strictly positive. -/
private lemma bwdF_pos {k r : ℕ} (S : Finset (Fin k)) (hS : #S = r) (b_vec : Fin k → ℕ)
    (hsupp : {i ∈ (Finset.univ : Finset (Fin k)) | 0 < b_vec i} = S) :
    ∀ j, 0 < bwdF S hS b_vec j := fun j ↦ by
  let e : Fin r ≃ S := (Finset.equivFinOfCardEq hS).symm
  have hmem : (e j : Fin k) ∈ {i ∈ (Finset.univ : Finset (Fin k)) | 0 < b_vec i} := by
    rw [hsupp]
    exact (e j).property
  exact (Finset.mem_filter.mp hmem).2

/-- `bwdF` is a left inverse of `fwdF`. -/
private lemma bwdF_fwdF {k r : ℕ} (S : Finset (Fin k)) (hS : #S = r) (c : Fin r → ℕ) :
    bwdF S hS (fwdF S hS c) = c := by
  funext j
  simp [bwdF, fwdF]

/-- On tuples whose support is exactly `S`, `fwdF` is a left inverse of `bwdF`. -/
private lemma fwdF_bwdF {k r : ℕ} (S : Finset (Fin k)) (hS : #S = r) (b_vec : Fin k → ℕ)
    (hsupp : {i ∈ (Finset.univ : Finset (Fin k)) | 0 < b_vec i} = S) :
    fwdF S hS (bwdF S hS b_vec) = b_vec := by
  funext i
  unfold fwdF bwdF
  by_cases h : i ∈ S
  · simp [h]
  · simp only [h, dite_false]
    have hi : i ∉ {i ∈ (Finset.univ : Finset (Fin k)) | 0 < b_vec i} := hsupp ▸ h
    simp [Finset.mem_filter] at hi
    omega

/-- Extension by zero preserves the total: `∑ i, fwdF S hS c i = ∑ j, c j`. -/
private lemma fwdF_sum_eq {k r : ℕ} (S : Finset (Fin k)) (hS : #S = r) (c : Fin r → ℕ) :
    ∑ i, fwdF S hS c i = ∑ j, c j := by
  rw [show (∑ i, fwdF S hS c i) = ∑ i ∈ S, fwdF S hS c i from
        (Finset.sum_subset (Finset.subset_univ S) fun i _ hi ↦
          fwdF_eq_zero_of_not_mem S hS c i hi).symm,
      ← Finset.sum_attach S (fun i ↦ fwdF S hS c i)]
  symm
  apply Fintype.sum_equiv (Finset.equivFinOfCardEq hS).symm c
    (fun s : {x // x ∈ S} ↦ fwdF S hS c s.val)
  intro jj
  simp [fwdF]

/-- If `c` is strictly positive, the support of `fwdF S hS c` equals `S`. -/
private lemma fwdF_support {k r : ℕ} (S : Finset (Fin k)) (hS : #S = r)
    (c : Fin r → ℕ) (hc : ∀ j, 0 < c j) :
    {i ∈ (Finset.univ : Finset (Fin k)) | 0 < fwdF S hS c i} = S := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold fwdF
  refine ⟨fun h ↦ by by_contra hi; rw [dif_neg hi] at h; exact absurd h (lt_irrefl 0),
    fun hi ↦ by rw [dif_pos hi]; exact hc _⟩

/-- The sum over vectors `b_vec : Fin k → ℕ` in `piAntidiag`
    with exactly `r` nonzero entries equals `k.choose r` times the sum over strictly
    positive vectors `c : Fin r → ℕ` with `∑ c = b`.

    This is `MaynardGOpt.sum_fiber_eq_choose_mul` transported along
    `Finset.piAntidiag_univ_fin_eq_antidiagonalTuple` and the shift
    `MaynardGFast.antidiagonalTuple_shift`, together with the degenerate case `b < r`
    in which both sides vanish. -/
private lemma sum_fiber_eq_choose_mul (k b j r : ℕ) :
    (∑ b_vec ∈ ((Finset.univ : Finset (Fin k)).piAntidiag b) with hammingNorm b_vec = r,
        ∏ i, ((j * b_vec i)! / (b_vec i)! : ℕ))
    =
    k.choose r * ∑ c ∈ ((Finset.univ : Finset (Fin r)).piAntidiag b) with (∀ i, 0 < c i),
      ∏ i, ((j * c i)! / (c i)! : ℕ) := by
  rw [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.piAntidiag_univ_fin_eq_antidiagonalTuple]
  rcases le_or_gt r b with hrb | hbr
  · rw [MaynardGOpt.sum_fiber_eq_choose_mul j hrb,
      MaynardGFast.antidiagonalTuple_shift r (b - r) (fun i ↦ (j * i)! / i !),
      Nat.sub_add_cancel hrb]
  · have hL : ∀ d ∈ {d ∈ (Finset.Nat.antidiagonalTuple k b) | hammingNorm d = r},
        ∏ i, ((j * d i)! / (d i)! : ℕ) = 0 := by
      intro d hd
      rw [Finset.mem_filter, Nat.mem_antidiagonalTuple] at hd
      obtain ⟨hsum, hcard⟩ := hd
      have hle := MaynardGOpt.hammingNorm_le_sum d
      exact absurd hcard (by omega)
    have hR : ∀ c ∈ {c ∈ (Finset.Nat.antidiagonalTuple r b) | ∀ i, 0 < c i},
        ∏ i, ((j * c i)! / (c i)! : ℕ) = 0 := by
      intro c hc
      rw [Finset.mem_filter, Nat.mem_antidiagonalTuple] at hc
      obtain ⟨hsum, hpos⟩ := hc
      have hge : r ≤ ∑ i, c i :=
        calc r = ∑ _ : Fin r, 1 := by simp
          _ ≤ ∑ i, c i := Finset.sum_le_sum fun i _ ↦ hpos i
      exact absurd hsum (by omega)
    rw [Finset.sum_eq_zero hL, Finset.sum_eq_zero hR, Nat.mul_zero]

/-- Partition-count identity: group compositions by support size. -/
@[pg_tag "bg246" "lem_partition_count"]
theorem lem_partition_count (k b j : ℕ) (hb : 1 ≤ b) :
    (∑ b_vec ∈ ((Finset.univ : Finset (Fin k)).piAntidiag b),
        ∏ i, ((j * b_vec i)! / (b_vec i)! : ℕ))
    =
    ∑ r ∈ Finset.Icc 1 b, k.choose r * ∑ b_vec ∈ ((Finset.univ : Finset (Fin r)).piAntidiag b),
        if (∀ i, 0 < b_vec i) then
          ∏ i, ((j * b_vec i)! / (b_vec i)! : ℕ)
        else 0 := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := ((Finset.univ : Finset (Fin k)).piAntidiag b))
      (t := Finset.Icc 1 b)
      (g := hammingNorm)
      (fun b_vec h ↦ hammingNorm_mem_Icc k b hb b_vec h)
      (f := fun b_vec ↦ ∏ i, ((j * b_vec i)! / (b_vec i)! : ℕ))]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [sum_fiber_eq_choose_mul k b j r, Finset.sum_filter]


open scoped BigOperators


/-- The sum of `∏ φ(c i)` over strictly-positive `r`-tuples summing to `b`. -/
noncomputable def posSum (r b : ℕ) (φ : ℕ → ℝ) : ℝ :=
  ∑ c_vec ∈ {c ∈ ((univ : Finset (Fin r)).piAntidiag b) | ∀ i, 0 < c i},
    ∏ i : Fin r, φ (c_vec i)

/-- The `if`-gated form of `posSum`. -/
lemma sum_if_pos_eq_posSum (r b : ℕ) (φ : ℕ → ℝ) :
    (∑ c_vec ∈ ((univ : Finset (Fin r)).piAntidiag b),
        if (∀ i, 0 < c_vec i) then ∏ i : Fin r, φ (c_vec i) else 0) = posSum r b φ := by
  rw [← Finset.sum_filter]
  rfl

/-- Partition a `piAntidiag` sum into the fibres of the positive-support map `c ↦ {i | 0 < c i}`. -/
lemma lhs_partition_by_support (k b : ℕ) (φ : ℕ → ℝ) :
    (∑ c_vec ∈ ((univ : Finset (Fin k)).piAntidiag b), ∏ i : Fin k, φ (c_vec i)) =
    ∑ S ∈ (univ : Finset (Fin k)).powerset, ∑ c_vec ∈ ((univ : Finset (Fin k)).piAntidiag b).filter
          (fun c ↦ univ.filter (fun i ↦ 0 < c i) = S),
        ∏ i : Fin k, φ (c_vec i) := by
  classical
  rw [Finset.sum_fiberwise_of_maps_to]
  intros; simp

/-- For each subset `S ⊆ Fin k` of size `r := |S|`, the contribution from the
support-stratum equals `posSum r b φ`. -/
lemma stratum_eq_posSum (k b : ℕ) (φ : ℕ → ℝ) (hφ0 : φ 0 = 1) (S : Finset (Fin k)) :
    (∑ c_vec ∈ ((univ : Finset (Fin k)).piAntidiag b).filter
        (fun c ↦ univ.filter (fun i ↦ 0 < c i) = S),
      ∏ i : Fin k, φ (c_vec i)) = posSum #S b φ := by
  unfold posSum
  refine Finset.sum_nbij' (bwdF S rfl) (fwdF S rfl) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    simp only [mem_filter, mem_piAntidiag] at hc ⊢
    obtain ⟨⟨hsum, _⟩, hsupp⟩ := hc
    refine ⟨⟨?_, fun _ _ ↦ mem_univ _⟩, bwdF_pos S rfl c hsupp⟩
    rw [bwdF_sum_eq S rfl c hsupp, hsum]
  · intro c' hc'
    simp only [mem_filter, mem_piAntidiag] at hc' ⊢
    obtain ⟨⟨hsum, _⟩, hpos⟩ := hc'
    refine ⟨⟨?_, fun _ _ ↦ mem_univ _⟩, fwdF_support S rfl c' hpos⟩
    rw [fwdF_sum_eq S rfl c', hsum]
  · intro c hc
    exact fwdF_bwdF S rfl c (mem_filter.mp hc).2
  · intro c' _
    exact bwdF_fwdF S rfl c'
  · intro c hc
    have hsupp := (mem_filter.mp hc).2
    calc ∏ i : Fin k, φ (c i)
        = ∏ i ∈ S, φ (c i) := by
          refine (Finset.prod_subset (subset_univ S) fun i _ hi ↦ ?_).symm
          have hzero : c i = 0 := by
            by_contra hne
            exact hi (hsupp ▸ mem_filter.mpr ⟨mem_univ _, Nat.pos_of_ne_zero hne⟩)
          rw [hzero, hφ0]
      _ = ∏ j : Fin #S, φ (bwdF S rfl c j) :=
        MaynardGOpt.prod_eq_prod_equivFin rfl fun i ↦ φ (c i)

/-- Summing `f S.card` over subsets of `Fin k` equals `∑ r, (k.choose r) * f r`. -/
lemma sum_powerset_by_card (k : ℕ) (f : ℕ → ℝ) :
    (∑ S ∈ (univ : Finset (Fin k)).powerset, f #S) =
    ∑ r ∈ Finset.range (k + 1), (k.choose r : ℝ) * f r := by
  rw [Finset.sum_powerset_apply_card]
  simp [card_univ, nsmul_eq_mul]

/-- When `b ≥ 1`, no `0`-tuple sums to `b`, so `posSum 0 b φ = 0`. -/
lemma posSum_zero (b : ℕ) (hb : 1 ≤ b) (φ : ℕ → ℝ) : posSum 0 b φ = 0 := by
  simp [posSum, show b ≠ 0 from by omega]

/-- When `b < r`, no positive `r`-tuple can sum to `b`, so the sum is `0`. -/
lemma posSum_eq_zero_of_lt (r b : ℕ) (hbr : b < r) (φ : ℕ → ℝ) : posSum r b φ = 0 := by
  refine Finset.sum_eq_zero fun c hc ↦ ?_
  simp only [mem_filter, mem_piAntidiag] at hc
  obtain ⟨⟨hsum, _⟩, hpos⟩ := hc
  have hge : ∑ i : Fin r, c i ≥ ∑ i : Fin r, 1 := Finset.sum_le_sum fun i _ ↦ hpos i
  simp [hsum] at hge
  omega

/-- The outer sum can be taken either over `range (k+1)` or over `Icc 1 b`. -/
lemma sum_range_eq_sum_Icc (k b : ℕ) (hb : 1 ≤ b) (φ : ℕ → ℝ) :
    (∑ r ∈ Finset.range (k + 1), (k.choose r : ℝ) * posSum r b φ) =
    ∑ r ∈ Finset.Icc 1 b, (k.choose r : ℝ) * posSum r b φ := by
  trans ∑ r ∈ Finset.Icc 0 (max k b), (k.choose r : ℝ) * posSum r b φ
  · refine Finset.sum_subset
      (fun r hr ↦ by rw [Finset.mem_range] at hr; rw [mem_Icc]; omega)
      (fun r _ hr' ↦ by
        rw [Finset.mem_range] at hr'
        rw [Nat.choose_eq_zero_of_lt (by omega : k < r), Nat.cast_zero, zero_mul])
  · refine (Finset.sum_subset
      (fun r hr ↦ by rw [mem_Icc] at hr ⊢; omega)
      (fun r _ hr' ↦ by
        rw [mem_Icc] at hr'
        by_cases hr0 : r = 0
        · rw [hr0, posSum_zero b hb, mul_zero]
        · rw [posSum_eq_zero_of_lt r b (by omega) φ, mul_zero])).symm

/-- Support-stratification of `piAntidiag` sums: a sum over k-tuples with fixed total
`b ≥ 1` can be regrouped by positive-support size. -/
theorem lem_partition_count_piantidiag_support (k b : ℕ) (hk : 1 ≤ k) (hb : 1 ≤ b)
    (φ : ℕ → ℝ) (hφ0 : φ 0 = 1) :
    (∑ c_vec ∈ ((Finset.univ : Finset (Fin k)).piAntidiag b), ∏ i : Fin k, φ (c_vec i)) =
    ∑ r ∈ Finset.Icc 1 b, k.choose r * (∑ c_vec ∈ ((Finset.univ : Finset (Fin r)).piAntidiag b),
        if (∀ i, 0 < c_vec i) then ∏ i : Fin r, φ (c_vec i) else 0) := by
  let _ := hk
  rw [lhs_partition_by_support k b φ,
    Finset.sum_congr rfl (fun S _ ↦ stratum_eq_posSum k b φ hφ0 S),
    sum_powerset_by_card k (fun r ↦ posSum r b φ),
    sum_range_eq_sum_Icc k b hb φ]
  exact Finset.sum_congr rfl fun r _ ↦ by rw [← sum_if_pos_eq_posSum r b φ]

/-- Multinomial expansion of `(∑ tᵢ^j)^b`. -/
@[pg_tag "bg246" "lem_multinomial_Pj"]
theorem lem_multinomial_Pj {R : Type*} [CommSemiring R] (k : ℕ) (t : Fin k → R) (j b : ℕ) :
    (∑ i, (t i) ^ j) ^ b = ∑ b_vec ∈ ((Finset.univ : Finset (Fin k)).piAntidiag b),
        (b ! / (∏ i, (b_vec i)!) : ℕ) *
        ∏ i, (t i) ^ (j * b_vec i) := by
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  refine Finset.sum_congr rfl fun b_vec hb_vec ↦ ?_
  rw [show Nat.multinomial Finset.univ b_vec = b ! / ∏ i, (b_vec i)! from
    (Finset.mem_piAntidiag.mp hb_vec).1 ▸ rfl]
  exact congrArg _ <| Finset.prod_congr rfl fun i _ ↦ (pow_mul _ _ _).symm

end PrimeGaps
