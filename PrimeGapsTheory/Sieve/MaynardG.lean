/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.InformationTheory.Hamming

import PrimeGapsTheory.Tactic.PaperTag

/-!
# The function `G_{b,j}(x)`

We define `maynardG b j x` as `b! ∑[d1+...+dx=b], ∏[i], (j*di)!/di!`.

The first optimization, which Maynard did, was to eliminate the zero entries. A reduced vector with
`r` non-zero entries appears `x.choose r` times. This takes `x` out of the complexity. This then
allows us to write it as `b! ∑[r, d1+...+dr=b, di>0], x.choose r * ∏[i], (j*di)!/di!`.

The second optimization is to make `di` ascending. The multiplicity of each partition is then
calculated from its runs of the same entry. It is now
`b! ∑[r, d1+...+dr=b, 0<d1, di ascending], x.choose r * d.countPerms * ∏[i], (j*di)!/di!`
These partitions are actually modeled as `Multiset ℕ`.

## Main definitions

* `PrimeGaps.maynardG`: Maynard's polynomial `G_{b, j}(x)`, with notation `G[b, j]`.
* `PrimeGaps.maynardGFast`: the second optimization, summing over the partitions of `b`.
* `Nat.partitionMultisetGE`: the partitions of `n` into parts at least `r`, as a `List`.
* `Nat.partitionMultiset`: the partitions of `n`, as a `Finset (Multiset ℕ)`.
* `List.countPerms` and `Multiset.countPermsTR`: computable permutation counts.

## Main results

* `PrimeGaps.maynardG_eq_sum_range_choose`: the first optimization, summing over the support size.
* `PrimeGaps.maynardG_eq_maynardGFast`: `maynardG` agrees with `maynardGFast`.
-/

@[expose] public section

open Finset Nat
open scoped Finset Polynomial

namespace List

/-- The number of permutations of a given list. -/
def countPerms {α : Type*} [DecidableEq α] (l : List α) : ℕ := match l with
  | [] => 1
  | a :: t =>
    have : (t.attach.filter (.not <| a = ·.1)).length ≤ t.length := by grind
    (t.length + 1).choose (t.count a + 1) * (t.filter (a ≠ ·)).countPerms
termination_by length l

/-- `List.countPerms` agrees with `Multiset.countPerms` on the underlying multiset. -/
theorem countPerms_eq_multiset_countPerms {α : Type*} [DecidableEq α] {l : List α} :
    l.countPerms = Multiset.countPerms (.ofList l) := by
  induction hl : l.length using Nat.strong_induction_on generalizing l with | h n ih =>
  obtain _ | ⟨x, t⟩ := l
  · simp [countPerms]
  · rw [countPerms, Multiset.countPerms_filter_ne x, ih _ (by grind) rfl]
    simp

end List

namespace Multiset

/-- The number of permutations of a given multiset, as a computable analogue of `countPerms`. -/
def countPermsTR {α : Type*} [DecidableEq α] (m : Multiset α) : ℕ :=
  Quot.recOn m List.countPerms fun a b h ↦ by
    grind [List.countPerms_eq_multiset_countPerms, show ofList a = ofList b from Quot.sound h]

/-- `Multiset.countPerms` agrees with its computable analogue `countPermsTR`. -/
theorem countPerms_eq_countPermsTR : @countPerms = @countPermsTR := funext₃ fun _ _ m ↦
  Quot.induction_on m fun _ ↦ List.countPerms_eq_multiset_countPerms.symm

end Multiset

namespace Nat

/-- The list of partitions of `n` into parts of size at least `r`, represented as multisets
summing to `n`. -/
def partitionMultisetGE (n r : ℕ) : List (Multiset ℕ) :=
  if hn : n = 0 then [{}]
  else if hnr : n < r ∨ r = 0 then []
  else (List.range' r (n - r + 1)).attach.flatMap fun x ↦
    have : n - Subtype.val x < n := by grind
    (partitionMultisetGE (n - x.val) x).map (x ::ₘ ·)

/-- A multiset lies in `partitionMultisetGE n r` iff its parts are at least `r` and sum to `n`. -/
theorem mem_partitionMultisetGE {n r : ℕ} (hr : 1 ≤ r) {v : Multiset ℕ} :
    v ∈ partitionMultisetGE n r ↔ (∀ a ∈ v, r ≤ a) ∧ v.sum = n := by
  induction n using Nat.strong_induction_on generalizing r v with | h n ih =>
  rw [partitionMultisetGE]
  split_ifs with hn hnr
  · exact List.mem_singleton.trans ⟨fun h ↦ by simp [h, hn], fun ⟨h1, h2⟩ ↦
      Multiset.eq_zero_of_forall_notMem fun a ha ↦ by grind [Multiset.le_sum_of_mem ha]⟩
  · refine iff_of_false (by simp) fun ⟨h1, h2⟩ ↦ ?_
    obtain ⟨a, ha⟩ : ∃ a, a ∈ v := Multiset.exists_mem_of_ne_zero (by grind)
    grind [Multiset.le_sum_of_mem ha]
  · simp only [List.mem_flatMap, List.mem_attach, List.mem_map, true_and]
    constructor
    · rintro ⟨a, w, hw, rfl⟩
      grind [a.property, List.mem_range', Multiset.sum_cons]
    · rintro ⟨h1, h2⟩
      obtain ⟨x, hxv, hxle⟩ := Multiset.exists_min_image (id : ℕ → ℕ) (s := v) (by grind)
      exact ⟨⟨x, by grind [List.mem_range', Multiset.le_sum_of_mem hxv]⟩, v.erase x,
        (ih (n - x) (by grind) (hr.trans (h1 x hxv))).mpr
          ⟨fun a ha ↦ hxle a (Multiset.mem_of_mem_erase ha), by grind [Multiset.sum_erase hxv]⟩,
        Multiset.cons_erase hxv⟩

/-- The list `partitionMultisetGE n r` has no duplicate entries. -/
theorem nodup_partitionMultisetGE {n r : ℕ} : (partitionMultisetGE n r).Nodup := by
  induction n using Nat.strong_induction_on generalizing r with
  | h n ih =>
    rw [partitionMultisetGE]
    split_ifs with hn hnr
    · simp
    · simp
    · exact List.nodup_flatMap.2 ⟨fun a _ ↦ (ih (n - a) (by grind)).map fun _ _ ↦
        (Multiset.cons_inj_right _).mp, (List.nodup_range').attach.pairwise_of_forall_ne
          fun a _ b _ hne w hwa hwb ↦ by grind [mem_partitionMultisetGE, Multiset.mem_cons_self]⟩

/-- The finite set of partitions of `n`, represented as multisets of positive integers summing to
`n`. It agrees with Mathlib's `Finset.univ : Finset n.Partition` under `Nat.Partition.parts`, but
is computed by direct recursion rather than by enumerating all compositions of `n`. -/
def partitionMultiset (n : ℕ) : Finset (Multiset ℕ) where
  val := partitionMultisetGE n 1
  nodup := nodup_partitionMultisetGE

/-- A multiset is a partition of `n` iff it sums to `n` and has no zero parts. -/
@[simp] theorem mem_partitionMultiset {n : ℕ} {v : Multiset ℕ} :
    v ∈ partitionMultiset n ↔ v.sum = n ∧ 0 ∉ v := by
  grind [partitionMultiset, Multiset.mem_coe, mem_partitionMultisetGE]

end Nat

namespace PrimeGaps

/-- Maynard's polynomial `G_{b, j}(x)`. -/
@[pg_tag "bg246" "def_Gbj"]
def maynardG (b j x : ℕ) : ℕ := b ! * ∑ d ∈ antidiagonalTuple x b, ∏ i, (j * d i)! / (d i)!

end PrimeGaps

/-- The notation `G[b, j]` denotes Maynard's polynomial `maynardG b j`. -/
@[pg_tag "bg246" "def_Gbj" "Maynard's polynomial `G_{b, j}(x)`."]
scoped[PrimeGaps] notation "G[" b ", " j "]" => maynardG b j

namespace PrimeGaps

/-- Second optimization of `maynardG`. See `maynardG_eq_maynardGFast` for the equivalence. -/
def maynardGFast (b j x : ℕ) : ℕ :=
  b ! * ∑ r ∈ partitionMultiset b, x.choose r.card * r.countPermsTR *
    (r.map fun i ↦ (j * i)! / i !).prod

end PrimeGaps

open PrimeGaps

namespace MaynardGOpt

/-- The Hamming norm of a natural-valued function is at most the sum of its values. -/
lemma hammingNorm_le_sum {ι : Type*} [Fintype ι] (d : ι → ℕ) : hammingNorm d ≤ ∑ i, d i :=
  (Finset.card_filter _ _).trans_le (Finset.sum_le_sum fun i _ ↦ by grind)

private lemma hammingNorm_mem_range {x b : ℕ} {d : Fin x → ℕ} (h : d ∈ antidiagonalTuple x b) :
    hammingNorm d ∈ range (b + 1) :=
  mem_range_succ_iff.mpr (Nat.mem_antidiagonalTuple.mp h ▸ hammingNorm_le_sum d)

private noncomputable def fwd {x r : ℕ} (S : Finset (Fin x)) (hS : #S = r)
    (c : Fin r → ℕ) : Fin x → ℕ :=
  fun i ↦ if h : i ∈ S then c (Finset.equivFinOfCardEq hS ⟨i, h⟩) + 1 else 0

private noncomputable def bwd {x r : ℕ} (S : Finset (Fin x)) (hS : #S = r)
    (d : Fin x → ℕ) : Fin r → ℕ :=
  fun m ↦ d ((Finset.equivFinOfCardEq hS).symm m : Fin x) - 1

private lemma fwd_eq_zero_of_notMem {x r : ℕ} {S : Finset (Fin x)} (hS : #S = r)
    (c : Fin r → ℕ) {i : Fin x} (h : i ∉ S) : fwd S hS c i = 0 :=
  dif_neg h

private lemma fwd_eq_of_mem {x r : ℕ} {S : Finset (Fin x)} (hS : #S = r)
    (c : Fin r → ℕ) {i : Fin x} (h : i ∈ S) :
    fwd S hS c i = c (Finset.equivFinOfCardEq hS ⟨i, h⟩) + 1 :=
  dif_pos h

private lemma fwd_apply_symm {x r : ℕ} {S : Finset (Fin x)} (hS : #S = r)
    (c : Fin r → ℕ) (m : Fin r) :
    fwd S hS c ((Finset.equivFinOfCardEq hS).symm m : Fin x) = c m + 1 := by simp [fwd]

private lemma fwd_ne_zero {x r : ℕ} {S : Finset (Fin x)} (hS : #S = r)
    (c : Fin r → ℕ) {i : Fin x} (h : i ∈ S) : fwd S hS c i ≠ 0 :=
  (fwd_eq_of_mem hS c h).trans_ne (Nat.succ_ne_zero _)

private lemma fwd_support {x r : ℕ} {S : Finset (Fin x)} (hS : #S = r) (c : Fin r → ℕ) :
    univ.filter (fun i ↦ fwd S hS c i ≠ 0) = S := by grind [fwd]

/-- Reindexing a product over `S` through the bijection
`Finset.equivFinOfCardEq hS : S ≃ Fin r`. -/
@[to_additive /-- Reindexing a sum over `S` through the bijection
`Finset.equivFinOfCardEq hS : S ≃ Fin r`. -/]
lemma prod_eq_prod_equivFin {M : Type*} [CommMonoid M] {x r : ℕ} {S : Finset (Fin x)}
    (hS : #S = r) (g : Fin x → M) :
    ∏ i ∈ S, g i = ∏ m : Fin r, g ((Finset.equivFinOfCardEq hS).symm m : Fin x) :=
  (((Finset.equivFinOfCardEq hS).symm.prod_comp fun i ↦ g i).trans (S.prod_coe_sort g)).symm

private lemma fwd_sum_eq {x r : ℕ} {S : Finset (Fin x)} (hS : #S = r) (c : Fin r → ℕ) :
    ∑ i, fwd S hS c i = r + ∑ m, c m := by
  simp [← Finset.sum_subset (Finset.subset_univ S) fun i _ hi ↦ fwd_eq_zero_of_notMem hS c hi,
    sum_eq_sum_equivFin hS, fwd_apply_symm, Finset.sum_add_distrib, add_comm]

private lemma weight_fwd_eq {x r : ℕ} {S : Finset (Fin x)} (hS : #S = r) (j : ℕ)
    (c : Fin r → ℕ) :
    ∏ i, (j * fwd S hS c i)! / (fwd S hS c i)! = ∏ i, (j * (c i + 1))! / (c i + 1)! := by
  rw [← Finset.prod_subset (Finset.subset_univ S)
    fun i _ hi ↦ by simp [fwd_eq_zero_of_notMem hS c hi]]
  simp [prod_eq_prod_equivFin hS, fwd_apply_symm]

private lemma bwd_fwd {x r : ℕ} {S : Finset (Fin x)} (hS : #S = r) (c : Fin r → ℕ) :
    bwd S hS (fwd S hS c) = c := by grind [bwd, fwd_apply_symm]

private lemma fwd_bwd {x r : ℕ} {S : Finset (Fin x)} (hS : #S = r) (d : Fin x → ℕ)
    (hsupp : univ.filter (fun i ↦ d i ≠ 0) = S) : fwd S hS (bwd S hS d) = d := by
  grind [fwd, bwd]

private lemma bwd_sum_eq {x r : ℕ} {S : Finset (Fin x)} (hS : #S = r) (d : Fin x → ℕ)
    (hsupp : univ.filter (fun i ↦ d i ≠ 0) = S) :
    ∑ m, bwd S hS d m + r = ∑ i, d i := by
  grind [fwd_sum_eq, fwd_bwd]

private lemma sum_fiber_support_eq {x r b : ℕ} (hrb : r ≤ b) {S : Finset (Fin x)}
    (hS : #S = r) (j : ℕ) :
    ∑ d ∈ (antidiagonalTuple x b).filter (fun d ↦ univ.filter (fun i ↦ d i ≠ 0) = S),
        ∏ i, (j * d i)! / (d i)! =
      ∑ c ∈ antidiagonalTuple r (b - r), ∏ i, (j * (c i + 1))! / (c i + 1)! :=
  (sum_nbij' (fwd S hS) (bwd S hS) (fun c hc ↦ by grind [mem_antidiagonalTuple, fwd_sum_eq, fwd])
    (fun d hd ↦ by grind [mem_antidiagonalTuple, bwd_sum_eq]) (fun c _ ↦ bwd_fwd hS c)
    (fun d hd ↦ fwd_bwd hS d (mem_filter.1 hd).2) fun c _ ↦ (weight_fwd_eq hS j c).symm).symm

/-- Grouping `antidiagonalTuple x b` by support size `r` gives `x.choose r` copies of the
shifted sum over `antidiagonalTuple r (b - r)`. -/
lemma sum_fiber_eq_choose_mul {x b r : ℕ} (j : ℕ) (hrb : r ≤ b) :
    ∑ d ∈ {d ∈ antidiagonalTuple x b | hammingNorm d = r}, ∏ i, (j * d i)! / (d i)! =
      x.choose r * ∑ c ∈ antidiagonalTuple r (b - r), ∏ i, (j * (c i + 1))! / (c i + 1)! := by
  have hmaps d (hd : d ∈ {d ∈ antidiagonalTuple x b | hammingNorm d = r}) :
      univ.filter (d · ≠ 0) ∈ powersetCard r univ := mem_powersetCard_univ.2 (mem_filter.1 hd).2
  rw [← sum_fiberwise_of_maps_to hmaps (f := fun d ↦ ∏ i, (j * d i)! / (d i)!)]
  refine (sum_eq_card_nsmul fun S hS ↦ ?_).trans <| by rw [card_powersetCard, card_fin, smul_eq_mul]
  rw [← sum_fiber_support_eq hrb (mem_powersetCard_univ.1 hS) j]
  exact sum_congr ((filter_comm ..).trans <| filter_true_of_mem fun d hd ↦
    (congrArg Finset.card (mem_filter.1 hd).2).trans (mem_powersetCard_univ.1 hS)) fun _ _ ↦ rfl

end MaynardGOpt

namespace PrimeGaps

/-- Maynard's first optimization: grouping the tuples of `antidiagonalTuple x b` by the size `r` of
their support eliminates the zero entries, each reduced tuple being counted `x.choose r` times. -/
theorem maynardG_eq_sum_range_choose (b j x : ℕ) : G[b, j] x =
    b ! * ∑ r ∈ range (b + 1), x.choose r *
      ∑ c ∈ antidiagonalTuple r (b - r), ∏ i, (j * (c i + 1))! / (c i + 1)! := by
  rw [maynardG, ← Finset.sum_fiberwise_of_maps_to (fun d hd ↦ MaynardGOpt.hammingNorm_mem_range hd)
      (f := fun d ↦ ∏ i, (j * d i)! / (d i)!)]
  exact congrArg _ <| sum_congr rfl fun r hr ↦
    MaynardGOpt.sum_fiber_eq_choose_mul j (mem_range_succ_iff.mp hr)

end PrimeGaps

namespace MaynardGFast

open Polynomial

private noncomputable def generatingMonomial (φ : ℕ → ℕ) (i : ℕ) : ℕ[X] := monomial i (φ i)

private lemma prod_generatingMonomial {r : ℕ} (φ : ℕ → ℕ) (p : Fin r → ℕ) :
    ∏ i, generatingMonomial φ (p i) = monomial (∑ i, p i) (∏ i, φ (p i)) := by
  simp [generatingMonomial, ← C_mul_X_pow_eq_monomial, prod_mul_distrib, prod_pow_eq_pow_sum]

private lemma prod_map_generatingMonomial (φ : ℕ → ℕ) (v : Multiset ℕ) :
    (v.map (generatingMonomial φ)).prod = monomial v.sum ((v.map φ).prod) := by
  induction v using Multiset.induction <;> simp [generatingMonomial, monomial_mul_monomial, *]

private lemma coeff_prod_generatingMonomial {r n : ℕ} (φ : ℕ → ℕ) (p : Fin r → ℕ) :
    (∏ i, generatingMonomial φ (p i)).coeff n = if ∑ i, p i = n then ∏ i, φ (p i) else 0 := by
  simp [prod_generatingMonomial, coeff_monomial]

private lemma coeff_prod_map_generatingMonomial {n : ℕ} (φ : ℕ → ℕ) (v : Multiset ℕ) :
    (v.map (generatingMonomial φ)).prod.coeff n = if v.sum = n then (v.map φ).prod else 0 := by
  simp [prod_map_generatingMonomial, coeff_monomial]

private lemma coeff_countPerms_mul_prod_map_generatingMonomial {r n : ℕ} (φ : ℕ → ℕ)
    (k : Sym ℕ r) :
    ((k.1.countPerms : ℕ[X]) * (k.1.map (generatingMonomial φ)).prod).coeff n =
      if k.1.sum = n then k.1.countPerms * (k.1.map φ).prod else 0 := by
  rw [Polynomial.coeff_natCast_mul, coeff_prod_map_generatingMonomial]
  simp only [mul_ite, mul_zero, Nat.cast_id]

private lemma piFinset_Icc_filter_sum_eq {r n : ℕ} :
    {p ∈ Fintype.piFinset (fun _ : Fin r ↦ Finset.Icc 1 n) | ∑ i, p i = n} =
      {d ∈ antidiagonalTuple r n | ∀ i, 0 < d i} := by
  ext d
  have := fun i : Fin r ↦ Finset.single_le_sum (f := d) (fun j _ ↦ Nat.zero_le _) (mem_univ i)
  grind [Nat.mem_antidiagonalTuple]

private lemma sum_positive_eq_partitionSum (φ : ℕ → ℕ) (r n : ℕ) :
    ∑ d ∈ {d ∈ antidiagonalTuple r n | ∀ i, 0 < d i}, ∏ i, φ (d i) =
      ∑ v ∈ {v ∈ partitionMultiset n | v.card = r},
          v.countPermsTR * (v.map φ).prod := by
  rw [← Multiset.countPerms_eq_countPermsTR, ← piFinset_Icc_filter_sum_eq, Finset.sum_filter,
    ← Finset.sum_congr rfl (fun p _ ↦ coeff_prod_generatingMonomial φ p),
    ← Polynomial.finsetSum_coeff, ← Finset.sum_pow', Finset.sum_pow, Polynomial.finsetSum_coeff,
    Finset.sum_congr rfl fun k _ ↦ coeff_countPerms_mul_prod_map_generatingMonomial φ k,
    ← Finset.sum_filter]
  refine Finset.sum_bij' (fun k _ ↦ k.1) (fun v hv ↦ Sym.mk v (Finset.mem_filter.mp hv).2)
    (fun k hk ↦ ?_) (fun v hv ↦ ?_) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) fun _ _ ↦ rfl
  · simp only [Finset.mem_filter, Finset.mem_sym_iff, mem_partitionMultiset] at hk ⊢
    exact ⟨⟨hk.2, fun h0 ↦ absurd (hk.1 0 h0) (by simp)⟩, k.2⟩
  · simp only [Finset.mem_filter, Finset.mem_sym_iff, mem_partitionMultiset] at hv ⊢
    exact ⟨fun a ha ↦ Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero fun h ↦ hv.1.2 (h ▸ ha),
      (Multiset.le_sum_of_mem ha).trans_eq hv.1.1⟩, hv.1.1⟩

/-- Shifting a nonnegative tuple `c : Fin r → ℕ` summing to `n` up by `1` in each coordinate gives
a positive tuple summing to `n + r`. -/
lemma antidiagonalTuple_shift (r n : ℕ) (φ : ℕ → ℕ) :
    ∑ c ∈ antidiagonalTuple r n, ∏ i, φ (c i + 1) =
      ∑ d ∈ {d ∈ antidiagonalTuple r (n + r) | ∀ i, 0 < d i}, ∏ i, φ (d i) := by
  refine Finset.sum_nbij' (fun c i ↦ c i + 1) (fun d i ↦ d i - 1) (fun c hc ↦ ?_) (fun d hd ↦ ?_)
    ?_ ?_ ?_
  · rw [Nat.mem_antidiagonalTuple] at hc
    simp [Nat.mem_antidiagonalTuple, Finset.sum_add_distrib, hc]
  · rw [Nat.mem_antidiagonalTuple, Finset.sum_tsub_distrib univ fun i _ ↦ (mem_filter.mp hd).2 i]
    simp_all [Nat.mem_antidiagonalTuple]
  all_goals grind

end MaynardGFast

namespace PrimeGaps

/-- Maynard's polynomial `maynardG` agrees with its optimized form `maynardGFast`. -/
theorem maynardG_eq_maynardGFast : maynardG = maynardGFast := funext₃ fun b j x ↦ by
  have hmaps : ∀ v ∈ partitionMultiset b, Multiset.card v ∈ range (b + 1) := fun v hv ↦
    have ⟨hsum, hzero⟩ := mem_partitionMultiset.mp hv
    mem_range_succ_iff.mpr <| hsum ▸ show v.card ≤ v.sum by
      simpa using Multiset.card_nsmul_le_sum fun x hx ↦
        Nat.one_le_iff_ne_zero.mpr fun h ↦ hzero (h ▸ hx)
  rw [maynardG_eq_sum_range_choose, maynardGFast, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine congrArg _ (Finset.sum_congr rfl fun r hr ↦ ?_)
  rw [MaynardGFast.antidiagonalTuple_shift r (b - r) (fun i ↦ (j * i)! / i !),
    Nat.sub_add_cancel (mem_range_succ_iff.mp hr),
    MaynardGFast.sum_positive_eq_partitionSum (fun i ↦ (j * i)! / i !) r b, Finset.mul_sum]
  exact Finset.sum_congr rfl fun v hv ↦ by rw [(Finset.mem_filter.mp hv).2, mul_assoc]

/-- Maynard's polynomial `G_{0, j}` is identically `1`. -/
@[simp] theorem maynardG_zero_fst (j x : ℕ) : G[0, j] x = 1 := by
  simp [maynardG, Nat.antidiagonalTuple_zero_right]

end PrimeGaps
