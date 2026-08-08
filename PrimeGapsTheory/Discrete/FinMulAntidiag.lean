/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.Algebra.Order.Antidiag.Nat


/-!
# Tuples of fixed length that multiply to a fixed natural number

We record the basic API of `Nat.finMulAntidiag` in the degenerate lengths `0` and `1`, describe its
image and its fibres under evaluation at a coordinate, and identify it on prime powers with
`Nat.antidiagonalTuple`. We also define `Nat.finMulAntidiagLE`, the tuples whose product is at
most a given bound, which is the index set of the Maynard–Tao sieve.
-/

@[expose] public section

open Finset Nat

-- move
@[simp] theorem Fin.insertNthEquiv_apply'
    {n : ℕ} {α : Fin (n + 1) → Type*} {p : Fin (n + 1)}
    {q : α p × ((i : _) → α (p.succAbove i))} : p.insertNthEquiv α q = p.insertNth q.1 q.2 := rfl

namespace Nat

@[simp] theorem finMulAntidiag_zero_fst {n : ℕ} :
    (0).finMulAntidiag n = if n = 1 then {![]} else ∅ := by
  obtain rfl | hn := eq_or_ne n 1 <;>
  simp [Finset.ext_iff, *, eq_comm, Unique.eq_default ![]]

@[simp] theorem finMulAntidiag_one_fst {n : ℕ} :
    (1).finMulAntidiag n = if n = 0 then ∅ else {![n]} := by
  obtain rfl | hn := eq_or_ne n 0 <;>
  simp [Finset.ext_iff, *, eq_comm, funext_iff]

theorem image_finMulAntidiag_apply {r n : ℕ} {i : Fin r} (hr : r ≠ 1) :
    (r.finMulAntidiag n).image (· i) = n.divisors := ext fun d ↦ by
  simp_rw [mem_image, mem_finMulAntidiag, mem_divisors]
  have _ : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr <| by grind [i.pos]
  obtain ⟨j, hj⟩ := exists_ne i
  refine ⟨?_, fun ⟨hdn, hn⟩ ↦ ?_⟩
  · rintro ⟨d, ⟨rfl, hn⟩, rfl⟩
    simp [dvd_prod_of_mem, hn]
  · refine ⟨Function.update (Function.update 1 j (n / d)) i d, ⟨?_, hn⟩, by simp⟩
    rw [prod_update_of_mem (by simp), prod_update_of_mem (by grind)]
    simp [Nat.mul_div_cancel' hdn]

theorem finMulAntidiag_filter_apply_eq {r n a : ℕ} {i : Fin (r + 1)} :
    {d ∈ (r + 1).finMulAntidiag n | d i = a} =
    if a ∣ n then (r.finMulAntidiag (n / a)).map
      ⟨i.insertNth a, Fin.insertNth_right_injective _⟩ else ∅ := ext fun d ↦ by
  obtain ⟨⟨b, d⟩, rfl⟩ := (Fin.insertNthEquiv (fun _ ↦ ℕ) i).surjective d
  simp_rw [mem_filter, mem_ite, mem_map, Function.Embedding.coeFn_mk,
    mem_finMulAntidiag, notMem_empty, imp_false, not_not,
    show ∀ p q, (p → q) ∧ p ↔ p ∧ q by grind, Fin.insertNthEquiv_apply',
    Fin.insertNth_apply_same, Fin.prod_insertNth, Fin.insertNth_inj]
  constructor
  · rintro ⟨⟨rfl, hn⟩, rfl⟩
    grind [dvd_mul_right, mul_ne_zero_iff, Nat.mul_div_cancel_left]
  · rintro ⟨han, e, ⟨he, hna⟩, rfl, rfl⟩
    rw [he, Nat.mul_div_cancel' han]
    grind [Nat.div_ne_zero_iff.mp hna]

theorem finMulAntidiag_prime_pow {r p a : ℕ} (hp : p.Prime) : r.finMulAntidiag (p ^ a) =
    (antidiagonalTuple r a).map ⟨fun d i ↦ p ^ d i, by
      intro d₁ d₂ h
      exact funext fun i ↦ (Nat.pow_right_injective hp.two_le).eq_iff.mp (congr($h i))⟩ :=
  ext fun d ↦ by
  simp_rw [mem_finMulAntidiag, mem_map, Function.Embedding.coeFn_mk,
    mem_antidiagonalTuple, eq_true (pow_ne_zero a hp.ne_zero), and_true]
  refine ⟨fun h ↦ ?_, ?_⟩
  · have h₁ (i) : ∃ b ≤ a, d i = p ^ b := (dvd_prime_pow hp).mp <| h ▸ dvd_prod_of_mem _ (by simp)
    choose e _ he using h₁
    refine ⟨e, (Nat.pow_right_injective hp.two_le).eq_iff.mp ?_, by grind⟩
    simp_rw [← prod_pow_eq_pow_sum, ← he, h]
  · rintro ⟨e, he, rfl⟩
    simp_rw [prod_pow_eq_pow_sum, he]

theorem antidiagonalTuple_eq_map_finsuppAntidiag {r n : ℕ} :
    antidiagonalTuple r n = (finsuppAntidiag (univ : Finset (Fin r)) n).map
      (Finsupp.equivFunOnFinite (α := Fin r) (M := ℕ)) := by
  simp [Finset.ext_iff, mem_antidiagonalTuple]

/-- The `Finset` of tuples `ι → ℕ` with product between `1` and `R`. -/
def finMulAntidiagLE (ι : Type*) [Fintype ι] [DecidableEq ι] (R : ℕ) : Finset (ι → ℕ) :=
  {r ∈ Fintype.piFinset fun _ : ι ↦ Icc 1 R | ∏ i, r i ≤ R}

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : ℕ} {r : ι → ℕ}

@[simp] theorem mem_finMulAntidiagLE_iff :
    r ∈ finMulAntidiagLE ι R ↔ ∏ i, r i ≤ R ∧ ∀ i, r i ≠ 0 := by
  simp only [finMulAntidiagLE, mem_filter, Fintype.mem_piFinset, mem_Icc, one_le_iff_ne_zero]
  refine ⟨by grind, fun H ↦ ⟨fun i ↦ ⟨H.2 i, ?_⟩, H.1⟩⟩
  refine (le_of_dvd ?_ (dvd_prod_of_mem _ (mem_univ i))).trans H.1
  simp [prod_eq_zero_iff, pos_iff_ne_zero, H.2]

end Nat
