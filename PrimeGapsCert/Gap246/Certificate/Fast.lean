/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Multiset.Interval
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Tactic.DeriveFintype
public import PrimeGapsTheory.Gap246.Sieve.Certificate.Explicit

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity.Finset

/-! # Fast epsilon-enlarged certificates

The definitions in `Explicit.lean` are convenient mathematical specifications, but
`Multiset.embeddings` must not be evaluated for large certificates.  This file first
proves the coordinate-splitting recurrence used by the compressed evaluator, and then provides
the cleared-denominator certificate checked by `Witness.lean`.
-/

@[expose] public section

open scoped Finset Nat

open Finset

namespace Multiset

variable {k : ℕ}

/-- Permuting coordinates preserves membership in the embedding finset. -/
theorem comp_perm_mem_embeddings_iff (m : Multiset ℕ) (a : Fin k → ℕ)
    (σ : Equiv.Perm (Fin k)) :
    (a ∘ σ) ∈ m.embeddings k ↔ a ∈ m.embeddings k := by
  rw [mem_embeddings_iff, mem_embeddings_iff]
  have hp := Equiv.Perm.ofFn_comp_perm σ a
  have heq : (List.ofFn (a ∘ σ) : Multiset ℕ) = (List.ofFn a : Multiset ℕ) := Quot.sound hp
  rw [heq]

/-- Splitting off the zeroth coordinate of an embedding removes its value from the signature.
The hypothesis is the normal form used by the certificate signatures. -/
theorem cons_mem_embeddings_iff {m : Multiset ℕ} (hm : 0 ∉ m) (r : ℕ)
    (A : Fin k → ℕ) :
    Fin.cons r A ∈ m.embeddings (k + 1) ↔
      r ∈ insert 0 m.toFinset ∧ A ∈ (m.erase r).embeddings k := by
  rw [mem_embeddings_iff, mem_embeddings_iff, List.ofFn_cons]
  change (r ::ₘ (List.ofFn A : Multiset ℕ)).filter (· ≠ 0) = m.filter (· ≠ 0) ↔ _
  have hmfilter : m.filter (· ≠ 0) = m := Multiset.filter_eq_self.mpr fun x hx ↦ by
    exact ne_of_mem_of_not_mem hx hm
  by_cases hr : r = 0
  · subst r
    simp [hm, hmfilter]
  · rw [hmfilter]
    have herasefilter : (m.erase r).filter (· ≠ 0) = m.erase r :=
      Multiset.filter_eq_self.mpr fun x hx ↦
        ne_of_mem_of_not_mem (Multiset.mem_of_mem_erase hx) hm
    simp only [hr, mem_insert, mem_toFinset, false_or, herasefilter]
    have hfilter : (r ::ₘ (List.ofFn A : Multiset ℕ)).filter (· ≠ 0) =
        r ::ₘ (List.ofFn A : Multiset ℕ).filter (· ≠ 0) :=
      filter_cons_of_pos (p := fun x : ℕ ↦ x ≠ 0) _ hr
    constructor
    · intro h
      rw [hfilter] at h
      have hrm : r ∈ m := h ▸ by simp
      refine ⟨hrm, ?_⟩
      have hc := congrArg (Multiset.erase · r) h
      simpa [erase_cons_head] using hc
    · rintro ⟨hrm, h⟩
      rw [hfilter, h, cons_erase hrm]

end Multiset

namespace PrimeGaps

variable {k : ℕ}

/-- The integral factorial moment. -/
def facMomentNat (k : ℕ) (α β : Multiset ℕ) : ℕ :=
  ∑ A ∈ α.embeddings k, ∑ B ∈ β.embeddings k, ∏ i : Fin k, (A i + B i)!

/-- The part of a factorial moment in which coordinate `i` of the first embedding is `x`. -/
def coordContribution (k x : ℕ) (α β : Multiset ℕ) (i : Fin k) : ℕ :=
  ∑ A ∈ α.embeddings k, ∑ B ∈ β.embeddings k,
    if A i = x then ∏ j : Fin k, (A j + B j)! else 0

/-- Every coordinate makes the same contribution to a symmetric factorial moment. -/
theorem coordContribution_eq_zero (x : ℕ) (α β : Multiset ℕ) (i : Fin (k + 1)) :
    coordContribution (k + 1) x α β i = coordContribution (k + 1) x α β 0 := by
  let σ : Equiv.Perm (Fin (k + 1)) := Equiv.swap 0 i
  have hσ0 : σ 0 = i := by simp [σ]
  rw [coordContribution, coordContribution]
  apply sum_bij (fun A _ ↦ A ∘ σ)
  · intro A hA
    exact (Multiset.comp_perm_mem_embeddings_iff α A σ).2 hA
  · intro A₁ hA₁ A₂ hA₂ h
    funext j
    have := congrFun h (σ.symm j)
    simpa using this
  · intro A hA
    refine ⟨A ∘ σ, (Multiset.comp_perm_mem_embeddings_iff α A σ).2 hA, ?_⟩
    funext j
    simp [σ]
  · intro A hA
    apply sum_bij (fun B _ ↦ B ∘ σ)
    · intro B hB
      exact (Multiset.comp_perm_mem_embeddings_iff β B σ).2 hB
    · intro B₁ hB₁ B₂ hB₂ h
      funext j
      have := congrFun h (σ.symm j)
      simpa using this
    · intro B hB
      refine ⟨B ∘ σ, (Multiset.comp_perm_mem_embeddings_iff β B σ).2 hB, ?_⟩
      funext j
      simp [σ]
    · intro B hB
      simp only [Function.comp_apply, hσ0]
      split
      · exact (Equiv.prod_comp (σ : Fin (k + 1) ≃ Fin (k + 1))
          (fun j ↦ (A j + B j)!)).symm
      · rfl

/-- In an embedding, the multiplicity of a nonzero exponent is the number of coordinates carrying
that exponent. -/
theorem count_eq_card_coord {α : Multiset ℕ} (hα : 0 ∉ α)
    {A : Fin k → ℕ} (hA : A ∈ α.embeddings k) {x : ℕ} (hx : x ≠ 0) :
    α.count x = #(univ.filter fun i ↦ A i = x) := by
  rw [Multiset.mem_embeddings_iff] at hA
  have hfα : α.filter (· ≠ 0) = α :=
    Multiset.filter_eq_self.mpr fun y hy ↦ ne_of_mem_of_not_mem hy hα
  rw [hfα] at hA
  have hc := congrArg (Multiset.count x) hA
  rw [Multiset.count_filter_of_pos (p := fun y : ℕ ↦ y ≠ 0) (a := x) hx] at hc
  rw [← hc, Multiset.count_eq_card_filter_eq]
  change (List.filter (fun b ↦ decide (x = b)) (List.ofFn A)).length =
    (List.filter (fun i ↦ decide (A i = x)) (List.finRange k)).length
  rw [List.ofFn_eq_map, List.filter_map]
  simp [Function.comp_def, eq_comm]

/-- Multiplying by the exponent multiplicity marks one coordinate carrying that exponent. -/
theorem count_mul_facMomentNat {α β : Multiset ℕ} (hα : 0 ∉ α) {x : ℕ} (hx : x ≠ 0) :
    α.count x * facMomentNat (k + 1) α β =
      ∑ i : Fin (k + 1), coordContribution (k + 1) x α β i := by
  rw [facMomentNat, mul_sum]
  simp only [coordContribution]
  rw [sum_comm]
  refine sum_congr rfl fun A hA ↦ ?_
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun B hB ↦ ?_
  rw [count_eq_card_coord hα hA hx]
  let W := ∏ i : Fin (k + 1), (A i + B i)!
  change #(univ.filter fun i ↦ A i = x) * W = ∑ i, if A i = x then W else 0
  calc
    #(univ.filter fun i ↦ A i = x) * W =
        ∑ _ ∈ univ.filter (fun i ↦ A i = x), W := by
      symm
      exact Finset.sum_const_nat fun _ _ ↦ rfl
    _ = ∑ i, if A i = x then W else 0 :=
      Finset.sum_filter (fun i ↦ A i = x) (fun _ ↦ W)

/-- Summing the marked contribution over the coordinates multiplies the zeroth-coordinate
contribution by the number of variables. -/
theorem sum_coordContribution (x : ℕ) (α β : Multiset ℕ) :
    (∑ i : Fin (k + 1), coordContribution (k + 1) x α β i) =
      (k + 1) * coordContribution (k + 1) x α β 0 := by
  simp_rw [coordContribution_eq_zero]
  simp

/-- A sum over embeddings splits into the possible value of its zeroth coordinate. -/
theorem sum_embeddings_succ {m : Multiset ℕ} (hm : 0 ∉ m) (f : (Fin (k + 1) → ℕ) → ℕ) :
    ∑ A ∈ m.embeddings (k + 1), f A =
      ∑ r ∈ insert 0 m.toFinset, ∑ A ∈ (m.erase r).embeddings k, f (Fin.cons r A) := by
  let E := m.embeddings (k + 1)
  let R := insert 0 m.toFinset
  have hmaps : ∀ A ∈ E, A 0 ∈ R := by
    intro A hA
    exact ((Multiset.cons_mem_embeddings_iff hm (A 0) (fun i ↦ A i.succ)).mp <|
      Fin.cons_self_tail A ▸ hA).1
  have hfilt : E.filter (fun A ↦ A 0 ∈ R) = E := filter_eq_self.mpr hmaps
  change (∑ A ∈ E, f A) = ∑ r ∈ R, ∑ A ∈ (m.erase r).embeddings k, f (Fin.cons r A)
  rw [← hfilt, ← Finset.sum_fiberwise_eq_sum_filter E R (fun A ↦ A 0) f]
  dsimp only [R, E]
  refine sum_congr rfl fun r hr ↦ ?_
  apply sum_bij (fun A _ ↦ fun i ↦ A i.succ)
  · intro A hA
    rw [Finset.mem_filter] at hA
    have heq : Fin.cons r (fun i ↦ A i.succ) = A := by
      rw [← hA.2]
      exact Fin.cons_self_tail A
    exact (Multiset.cons_mem_embeddings_iff hm r (fun i ↦ A i.succ)).mp (heq ▸ hA.1) |>.2
  · intro A₁ hA₁ A₂ hA₂ heq
    rw [Finset.mem_filter] at hA₁ hA₂
    funext i
    refine Fin.cases ?_ (congrFun heq) i
    exact hA₁.2.trans hA₂.2.symm
  · intro A hA
    refine ⟨Fin.cons r A, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨(Multiset.cons_mem_embeddings_iff hm r A).mpr ⟨hr, hA⟩, Fin.cons_zero _ _⟩
  · intro A hA
    rw [Finset.mem_filter] at hA
    rw [← hA.2]
    exact congrArg f (Fin.cons_self_tail A).symm

/-- The zeroth-coordinate contribution is a sum over the distinct exponent placed in the second
embedding at that coordinate. -/
theorem coordContribution_zero {α β : Multiset ℕ} (hα : 0 ∉ α) (hβ : 0 ∉ β)
    {x : ℕ} (hxα : x ∈ α) :
    coordContribution (k + 1) x α β 0 =
      ∑ s ∈ insert 0 β.toFinset, (x + s)! * facMomentNat k (α.erase x) (β.erase s) := by
  rw [coordContribution, sum_embeddings_succ hα, sum_eq_single x]
  · simp only [Fin.cons_zero, if_pos, facMomentNat]
    simp_rw [sum_embeddings_succ hβ]
    rw [sum_comm]
    refine sum_congr rfl fun s hs ↦ ?_
    rw [mul_sum]
    refine sum_congr rfl fun A hA ↦ ?_
    rw [mul_sum]
    refine sum_congr rfl fun B hB ↦ ?_
    rw [Fin.prod_univ_succ]
    rfl
  · intro r hr hrx
    simp [hrx]
  · simp [hxα]

/-- Marking one occurrence of `x` gives a recurrence with no zero-coordinate branch.  This is the
recurrence used by the compressed evaluator. -/
theorem facMomentNat_marked {α β : Multiset ℕ} (hα : 0 ∉ α) (hβ : 0 ∉ β)
    {x : ℕ} (hxα : x ∈ α) :
    α.count x * facMomentNat (k + 1) α β =
      (k + 1) * ∑ s ∈ insert 0 β.toFinset,
        (x + s)! * facMomentNat k (α.erase x) (β.erase s) := by
  have hx : x ≠ 0 := ne_of_mem_of_not_mem hxα hα
  rw [count_mul_facMomentNat hα hx, sum_coordContribution,
    coordContribution_zero hα hβ hxα]

/-- The integral factorial moment is symmetric in its two signatures. -/
theorem facMomentNat_comm (k : ℕ) (α β : Multiset ℕ) :
    facMomentNat k α β = facMomentNat k β α := by
  rw [facMomentNat, facMomentNat, sum_comm]
  refine sum_congr rfl fun B hB ↦ ?_
  refine sum_congr rfl fun A hA ↦ ?_
  apply Fintype.prod_congr
  intro i
  rw [add_comm]

/-- A compressed table of factorial moments.  Its recurrence mentions only erasures of signatures,
so the witness can check the table without enumerating functions `Fin k → ℕ`. -/
structure FacMomentTable : Type where
  /-- Largest sieve dimension represented by the table. -/
  K : ℕ
  /-- Number of normalized signatures in the table. -/
  S : ℕ
  /-- The signatures, including the empty signature and all erasures needed below. -/
  sig : Fin S → Multiset ℕ
  /-- Table signatures contain no zero exponents. -/
  zeroFree (i : Fin S) : 0 ∉ sig i
  /-- A distinguished exponent of every nonempty signature. -/
  pivot : Fin S → ℕ
  /-- The distinguished exponent belongs to a nonempty signature. -/
  pivot_mem (i : Fin S) (hi : sig i ≠ 0) : pivot i ∈ sig i
  /-- Index of a signature after erasing an exponent (zero means no erasure). -/
  erase : Fin S → ℕ → Fin S
  /-- The erasure indices are correct. -/
  erase_sig (i : Fin S) (x : ℕ) (hx : x ∈ insert 0 (sig i).toFinset) :
    sig (erase i x) = (sig i).erase x
  /-- The compressed factorial moments. -/
  val : ℕ → Fin S → Fin S → ℕ
  /-- Initial values in dimension zero. -/
  val_zero (i j : Fin S) :
    val 0 i j = if sig i = 0 ∧ sig j = 0 then 1 else 0
  /-- The value for two empty signatures is one in every positive dimension. -/
  val_empty (k : Fin K) (i j : Fin S) (hi : sig i = 0) (hj : sig j = 0) :
    val (k + 1) i j = 1
  /-- Marked recurrence when the first signature is nonempty. -/
  val_left (k : Fin K) (i j : Fin S) (hi : sig i ≠ 0) :
    (sig i).count (pivot i) * val (k + 1) i j =
      (k + 1) * ∑ s ∈ insert 0 (sig j).toFinset,
        (pivot i + s)! * val k (erase i (pivot i)) (erase j s)
  /-- Marked recurrence when only the second signature is nonempty. -/
  val_right (k : Fin K) (i j : Fin S) (hi : sig i = 0) (hj : sig j ≠ 0) :
    (sig j).count (pivot j) * val (k + 1) i j =
      (k + 1) * (pivot j)! * val k i (erase j (pivot j))

/-- A balanced tree of independently packed blocks.  Looking up one value only divides the
small natural number stored in its leaf, rather than a numeral containing the entire table. -/
inductive PackedNatTree : Type where
  | leaf (code width mask : ℕ)
  | node (leftSize : ℕ) (left right : PackedNatTree)

/-- Extract an entry from a balanced tree of packed blocks. -/
def PackedNatTree.get : PackedNatTree → ℕ → ℕ
  | .leaf code width mask, i => (code >>> (width * i)) &&& mask
  | .node leftSize left right, i =>
      if i < leftSize then left.get i else right.get (i - leftSize)

theorem facMomentNat_zero (α β : Multiset ℕ) (hα : 0 ∉ α) (hβ : 0 ∉ β) :
    facMomentNat 0 α β = if α = 0 ∧ β = 0 then 1 else 0 := by
  have hfα : α.filter (· ≠ 0) = α :=
    Multiset.filter_eq_self.mpr fun x hx ↦ ne_of_mem_of_not_mem hx hα
  have hfβ : β.filter (· ≠ 0) = β :=
    Multiset.filter_eq_self.mpr fun x hx ↦ ne_of_mem_of_not_mem hx hβ
  by_cases ha : α = 0
  · subst α
    by_cases hb : β = 0
    · subst β
      simp [facMomentNat, Multiset.embeddings]
    · have hb' : 0 ≠ β := fun h ↦ hb h.symm
      simp [facMomentNat, Multiset.embeddings, hfβ, hb, hb']
  · have ha' : 0 ≠ α := fun h ↦ ha h.symm
    by_cases hb : β = 0
    · subst β
      simp [facMomentNat, Multiset.embeddings, hfα, ha, ha']
    · have hb' : 0 ≠ β := fun h ↦ hb h.symm
      simp [facMomentNat, Multiset.embeddings, hfα, hfβ, ha, hb, ha', hb']

/-- The integral factorial moment obeys the coordinate-splitting recurrence. -/
theorem facMomentNat_succ {α β : Multiset ℕ} (hα : 0 ∉ α) (hβ : 0 ∉ β) :
    facMomentNat (k + 1) α β = ∑ r ∈ insert 0 α.toFinset, ∑ s ∈ insert 0 β.toFinset,
      (r + s)! * facMomentNat k (α.erase r) (β.erase s) := by
  rw [facMomentNat, sum_embeddings_succ hα]
  refine sum_congr rfl fun r hr ↦ ?_
  simp_rw [sum_embeddings_succ hβ]
  simp only [facMomentNat]
  rw [sum_comm]
  refine sum_congr rfl fun s hs ↦ ?_
  rw [mul_sum]
  refine sum_congr rfl fun A hA ↦ ?_
  rw [mul_sum]
  refine sum_congr rfl fun B hB ↦ ?_
  rw [Fin.prod_univ_succ]
  rfl

/-- The factorial moment of two empty signatures is one. -/
@[simp] theorem facMomentNat_empty (k : ℕ) : facMomentNat k 0 0 = 1 := by
  induction k with
  | zero => rw [facMomentNat_zero] <;> simp
  | succ k ih => rw [facMomentNat_succ] <;> simp [ih]

/-- Every entry of a compressed table is the factorial moment specified in `Explicit.lean`. -/
theorem FacMomentTable.val_eq (T : FacMomentTable) (k : ℕ) (i j : Fin T.S) :
    k ≤ T.K → T.val k i j = facMomentNat k (T.sig i) (T.sig j) := by
  intro hkK
  induction hcard : (T.sig i).card + (T.sig j).card using Nat.strong_induction_on generalizing k i j
  rename_i n ih
  cases k with
  | zero => rw [T.val_zero, facMomentNat_zero _ _ (T.zeroFree i) (T.zeroFree j)]
  | succ k =>
      have hk : k < T.K := by omega
      by_cases hi : T.sig i = 0
      · by_cases hj : T.sig j = 0
        · rw [T.val_empty ⟨k, hk⟩ i j hi hj]
          simp [hi, hj]
        · have hxj := T.pivot_mem j hj
          have hcount : 0 < (T.sig j).count (T.pivot j) := Multiset.count_pos.mpr hxj
          apply Nat.eq_of_mul_eq_mul_left hcount
          rw [T.val_right ⟨k, hk⟩ i j hi hj]
          have herasej := T.erase_sig j (T.pivot j) (by simp [hxj])
          have hlt : (T.sig i).card + (T.sig (T.erase j (T.pivot j))).card < n := by
            rw [herasej, hi]
            rw [hi] at hcard
            have := Multiset.card_erase_lt_of_mem hxj
            omega
          rw [ih _ hlt k i (T.erase j (T.pivot j)) (by omega) rfl, herasej]
          rw [facMomentNat_comm (k + 1) (T.sig i) (T.sig j),
            facMomentNat_marked (T.zeroFree j) (T.zeroFree i) hxj]
          rw [facMomentNat_comm k (T.sig i) ((T.sig j).erase (T.pivot j))]
          simp [hi, mul_assoc]
      · have hxi := T.pivot_mem i hi
        have hcount : 0 < (T.sig i).count (T.pivot i) := Multiset.count_pos.mpr hxi
        apply Nat.eq_of_mul_eq_mul_left hcount
        rw [T.val_left ⟨k, hk⟩ i j hi, facMomentNat_marked (T.zeroFree i) (T.zeroFree j) hxi]
        apply congrArg ((k + 1) * ·)
        refine sum_congr rfl fun s hs ↦ ?_
        apply congrArg ((T.pivot i + s)! * ·)
        have herasei := T.erase_sig i (T.pivot i) (by simp [hxi])
        have herasej := T.erase_sig j s hs
        have hlt : (T.sig (T.erase i (T.pivot i))).card +
            (T.sig (T.erase j s)).card < n := by
          rw [herasei, herasej]
          calc
            ((T.sig i).erase (T.pivot i)).card + ((T.sig j).erase s).card <
                (T.sig i).card + (T.sig j).card :=
              Nat.add_lt_add_of_lt_of_le (Multiset.card_erase_lt_of_mem hxi)
                Multiset.card_erase_le
            _ = n := hcard
        rw [ih _ hlt k (T.erase i (T.pivot i)) (T.erase j s) (by omega) rfl,
          herasei, herasej]

/-- A sparse DAG containing only factorial-moment states reachable from the dimensions used by
the certificate.  Every edge removes at least one positive exponent, so the local recurrence
checks determine all node values without a rectangular `51 × S × S` table. -/
structure FacMomentDag (K degreeBound : ℕ) : Type where
  /-- Number of normalized signatures. -/
  S : ℕ
  /-- Number of reachable recurrence nodes. -/
  N : ℕ
  /-- Normalized signatures. -/
  sig : Fin S → Multiset ℕ
  /-- Signatures contain no zero exponents. -/
  zeroFree (i : Fin S) : 0 ∉ sig i
  /-- Every exponent fits in the finite transition alphabet. -/
  exponent_lt (i : Fin S) (x : ℕ) (hx : x ∈ sig i) : x < degreeBound
  /-- Distinguished exponent of a nonempty signature. -/
  pivot : Fin S → ℕ
  /-- The distinguished exponent belongs to a nonempty signature. -/
  pivot_mem (i : Fin S) (hi : sig i ≠ 0) : pivot i ∈ sig i
  /-- Signature erasure lookup used by the final marginal pairing. -/
  erase : Fin S → ℕ → Fin S
  /-- Signature erasure lookup is correct. -/
  erase_sig (i : Fin S) (x : ℕ) (hx : x ∈ insert 0 (sig i).toFinset) :
    sig (erase i x) = (sig i).erase x
  /-- Sieve dimension of a recurrence node. -/
  dim : Fin N → ℕ
  /-- First signature of a recurrence node. -/
  fst : Fin N → Fin S
  /-- Second signature of a recurrence node. -/
  snd : Fin N → Fin S
  /-- Explicit value stored at a recurrence node. -/
  val : Fin N → ℕ
  /-- Child node selected by the exponent erased from the second signature. -/
  child : Fin N → ℕ → Fin N
  /-- Every stored node has positive dimension. -/
  dim_pos (n : Fin N) : 0 < dim n
  /-- Empty signatures have value one. -/
  val_empty (n : Fin N) (hi : sig (fst n) = 0) (hj : sig (snd n) = 0) : val n = 1
  /-- A left-recurrence child has dimension one smaller. -/
  child_dim_left (n : Fin N) (s : Fin degreeBound) (hi : sig (fst n) ≠ 0)
      (hs : s.val ∈ insert 0 (sig (snd n)).toFinset) :
    dim (child n s) = dim n - 1
  /-- A left-recurrence child erases the pivot from the first signature. -/
  child_fst_left (n : Fin N) (s : Fin degreeBound) (hi : sig (fst n) ≠ 0)
      (hs : s.val ∈ insert 0 (sig (snd n)).toFinset) :
    sig (fst (child n s)) = (sig (fst n)).erase (pivot (fst n))
  /-- A left-recurrence child erases the selected exponent from the second signature. -/
  child_snd_left (n : Fin N) (s : Fin degreeBound) (hi : sig (fst n) ≠ 0)
      (hs : s.val ∈ insert 0 (sig (snd n)).toFinset) :
    sig (snd (child n s)) = (sig (snd n)).erase s
  /-- Stored values satisfy the marked recurrence when the first signature is nonempty. -/
  val_left (n : Fin N) (hi : sig (fst n) ≠ 0) :
    (sig (fst n)).count (pivot (fst n)) * val n =
      dim n * ∑ s ∈ insert 0 (sig (snd n)).toFinset,
        (pivot (fst n) + s)! * val (child n s)
  /-- A right-recurrence child has dimension one smaller. -/
  child_dim_right (n : Fin N) (hi : sig (fst n) = 0) (hj : sig (snd n) ≠ 0) :
    dim (child n (pivot (snd n))) = dim n - 1
  /-- A right-recurrence child retains the empty first signature. -/
  child_fst_right (n : Fin N) (hi : sig (fst n) = 0) (hj : sig (snd n) ≠ 0) :
    sig (fst (child n (pivot (snd n)))) = sig (fst n)
  /-- A right-recurrence child erases the pivot from the second signature. -/
  child_snd_right (n : Fin N) (hi : sig (fst n) = 0) (hj : sig (snd n) ≠ 0) :
    sig (snd (child n (pivot (snd n)))) = (sig (snd n)).erase (pivot (snd n))
  /-- Stored values satisfy the marked recurrence when only the second signature is nonempty. -/
  val_right (n : Fin N) (hi : sig (fst n) = 0) (hj : sig (snd n) ≠ 0) :
    (sig (snd n)).count (pivot (snd n)) * val n =
      dim n * (pivot (snd n))! * val (child n (pivot (snd n)))
  /-- Root node for a signature pair in dimension `K`. -/
  rootTop : Fin S → Fin S → Fin N
  /-- Root node for a signature pair in dimension `K - 1`. -/
  rootPred : Fin S → Fin S → Fin N
  rootTop_dim (i j : Fin S) : dim (rootTop i j) = K
  rootTop_fst (i j : Fin S) : fst (rootTop i j) = i
  rootTop_snd (i j : Fin S) : snd (rootTop i j) = j
  rootPred_dim (i j : Fin S) : dim (rootPred i j) = K - 1
  rootPred_fst (i j : Fin S) : fst (rootPred i j) = i
  rootPred_snd (i j : Fin S) : snd (rootPred i j) = j

/-- Every checked sparse-DAG node equals the specification factorial moment. -/
theorem FacMomentDag.val_eq {K degreeBound : ℕ} (T : FacMomentDag K degreeBound)
    (n : Fin T.N) :
    T.val n = facMomentNat (T.dim n) (T.sig (T.fst n)) (T.sig (T.snd n)) := by
  induction hcard : (T.sig (T.fst n)).card + (T.sig (T.snd n)).card using
    Nat.strong_induction_on generalizing n
  rename_i card ih
  by_cases hi : T.sig (T.fst n) = 0
  · by_cases hj : T.sig (T.snd n) = 0
    · rw [T.val_empty n hi hj]
      simp [hi, hj]
    · have hxj := T.pivot_mem (T.snd n) hj
      have hcount : 0 < (T.sig (T.snd n)).count (T.pivot (T.snd n)) :=
        Multiset.count_pos.mpr hxj
      apply Nat.eq_of_mul_eq_mul_left hcount
      rw [T.val_right n hi hj]
      let c := T.child n (T.pivot (T.snd n))
      have hcDim := T.child_dim_right n hi hj
      have hcFst := T.child_fst_right n hi hj
      have hcSnd := T.child_snd_right n hi hj
      have hlt : (T.sig (T.fst c)).card + (T.sig (T.snd c)).card < card := by
        change (T.sig (T.fst (T.child n (T.pivot (T.snd n))))).card +
          (T.sig (T.snd (T.child n (T.pivot (T.snd n))))).card < card
        calc
          _ = ((T.sig (T.snd n)).erase (T.pivot (T.snd n))).card := by
            rw [hcFst, hcSnd, hi]
            simp
          _ <
              (T.sig (T.snd n)).card := Multiset.card_erase_lt_of_mem hxj
          _ = card := by simpa [hi] using hcard
      rw [ih _ hlt c rfl, hcDim, hcFst, hcSnd]
      rw [facMomentNat_comm (T.dim n) (T.sig (T.fst n)) (T.sig (T.snd n))]
      have hdimPos := T.dim_pos n
      have hdim : T.dim n - 1 + 1 = T.dim n := by omega
      rw [← hdim, facMomentNat_marked (T.zeroFree (T.snd n)) (T.zeroFree (T.fst n)) hxj, hdim]
      rw [facMomentNat_comm (T.dim n - 1) (T.sig (T.fst n))
        ((T.sig (T.snd n)).erase (T.pivot (T.snd n)))]
      simp [hi, mul_assoc]
  · have hxi := T.pivot_mem (T.fst n) hi
    have hcount : 0 < (T.sig (T.fst n)).count (T.pivot (T.fst n)) :=
      Multiset.count_pos.mpr hxi
    apply Nat.eq_of_mul_eq_mul_left hcount
    rw [T.val_left n hi]
    have hdimPos := T.dim_pos n
    have hdim : T.dim n - 1 + 1 = T.dim n := by omega
    rw [← hdim, facMomentNat_marked (T.zeroFree (T.fst n)) (T.zeroFree (T.snd n)) hxi, hdim]
    apply congrArg (T.dim n * ·)
    refine sum_congr rfl fun s hs ↦ ?_
    apply congrArg ((T.pivot (T.fst n) + s)! * ·)
    have hpivotlt := T.exponent_lt (T.fst n) (T.pivot (T.fst n)) hxi
    have hslt : s < degreeBound := by
      rcases mem_insert.mp hs with rfl | hs
      · omega
      · exact T.exponent_lt (T.snd n) s (Multiset.mem_toFinset.mp hs)
    let c := T.child n s
    have hcDim := T.child_dim_left n ⟨s, hslt⟩ hi hs
    have hcFst := T.child_fst_left n ⟨s, hslt⟩ hi hs
    have hcSnd := T.child_snd_left n ⟨s, hslt⟩ hi hs
    have hlt : (T.sig (T.fst c)).card + (T.sig (T.snd c)).card < card := by
      change (T.sig (T.fst (T.child n s))).card +
        (T.sig (T.snd (T.child n s))).card < card
      calc
        _ = ((T.sig (T.fst n)).erase (T.pivot (T.fst n))).card +
            ((T.sig (T.snd n)).erase s).card := by rw [hcFst, hcSnd]
        _ < (T.sig (T.fst n)).card + (T.sig (T.snd n)).card :=
          Nat.add_lt_add_of_lt_of_le (Multiset.card_erase_lt_of_mem hxi)
            Multiset.card_erase_le
        _ = card := hcard
    rw [ih _ hlt c rfl, hcDim, hcFst, hcSnd]

/-- Dimension-`K` lookup supplied by a sparse factorial-moment DAG. -/
def FacMomentDag.valTop {K degreeBound : ℕ} (T : FacMomentDag K degreeBound)
    (i j : Fin T.S) : ℕ :=
  T.val (T.rootTop i j)

/-- Dimension-`K - 1` lookup supplied by a sparse factorial-moment DAG. -/
def FacMomentDag.valPred {K degreeBound : ℕ} (T : FacMomentDag K degreeBound)
    (i j : Fin T.S) : ℕ :=
  T.val (T.rootPred i j)

theorem FacMomentDag.valTop_eq {K degreeBound : ℕ} (T : FacMomentDag K degreeBound)
    (i j : Fin T.S) :
    T.valTop i j = facMomentNat K (T.sig i) (T.sig j) := by
  rw [FacMomentDag.valTop, T.val_eq, T.rootTop_dim, T.rootTop_fst, T.rootTop_snd]

theorem FacMomentDag.valPred_eq {K degreeBound : ℕ} (T : FacMomentDag K degreeBound)
    (i j : Fin T.S) :
    T.valPred i j = facMomentNat (K - 1) (T.sig i) (T.sig j) := by
  rw [FacMomentDag.valPred, T.val_eq, T.rootPred_dim, T.rootPred_fst, T.rootPred_snd]

/-- Casting the integral moment gives the rational moment used by `Explicit.lean`. -/
theorem facMomentNat_cast (k : ℕ) (α β : Multiset ℕ) :
    (facMomentNat k α β : ℚ) = facMoment k α β := by
  rw [facMomentNat, facMoment]
  calc
    (↑(∑ A ∈ α.embeddings k, ∑ B ∈ β.embeddings k,
      ∏ i : Fin k, (A i + B i)!) : ℚ) =
        ∑ A ∈ α.embeddings k, (↑(∑ B ∈ β.embeddings k,
          ∏ i : Fin k, (A i + B i)!) : ℚ) := by
      simp
    _ = ∑ A ∈ α.embeddings k, ∑ B ∈ β.embeddings k,
        ∏ i : Fin k, (↑(A i + B i)! : ℚ) := by
      refine sum_congr rfl fun A hA ↦ ?_
      have hcast : (↑(∑ B ∈ β.embeddings k, ∏ i : Fin k, (A i + B i)!) : ℚ) =
          ∑ B ∈ β.embeddings k, (↑(∏ i : Fin k, (A i + B i)!) : ℚ) := by
        simp
      rw [hcast]
      refine sum_congr rfl fun B hB ↦ ?_
      simp

/-- Common denominator for a pairing certificate with independent epsilon denominator and degree
bound. -/
def epsDenom (K epsilonDenominator degreeBound : ℕ) : ℕ :=
  epsilonDenominator ^ (2 * K + 1) * (2 * K + 1)! * (degreeBound + 1)! ^ 2

/-- Cleared-denominator enlarged-simplex pairing, using the specification factorial moment. -/
def IEpsExplicitNat (K epsilonDenominator degreeBound : ℕ) (a₁ : ℕ)
    (α₁ : Multiset ℕ) (a₂ : ℕ) (α₂ : Multiset ℕ) : ℕ :=
  let d := (a₁ + a₂) + (α₁.sum + α₂.sum)
  (epsilonDenominator + 1) ^ (K + d) * epsilonDenominator ^ (K + 1 - d) *
    (a₁ + a₂)! * facMomentNat K α₁ α₂ *
    (2 * K + 1).descFactorial (K + 1 - d) * (degreeBound + 1)! ^ 2

/-- The integral enlarged-simplex pairing casts to `epsDenom` times the rational pairing. -/
theorem IEpsExplicitNat_cast (K epsilonDenominator degreeBound a₁ : ℕ)
    (α₁ : Multiset ℕ) (a₂ : ℕ) (α₂ : Multiset ℕ) (hε : 0 < epsilonDenominator)
    (hd : (a₁ + a₂) + (α₁.sum + α₂.sum) ≤ K) :
    (IEpsExplicitNat K epsilonDenominator degreeBound a₁ α₁ a₂ α₂ : ℚ) =
      epsDenom K epsilonDenominator degreeBound *
        IEpsExplicit K (1 / epsilonDenominator) a₁ α₁ a₂ α₂ := by
  let d := (a₁ + a₂) + (α₁.sum + α₂.sum)
  have hd' : d ≤ K := hd
  have hlen : K + 1 - d ≤ 2 * K + 1 := by omega
  have hsub : 2 * K + 1 - (K + 1 - d) = K + d := by omega
  have hfac := Nat.factorial_mul_descFactorial hlen
  rw [hsub] at hfac
  have hfacQ : ((K + d)! : ℚ) *
      ((2 * K + 1).descFactorial (K + 1 - d) : ℚ) = ((2 * K + 1)! : ℚ) := by
    exact_mod_cast hfac
  have hpow : (epsilonDenominator : ℚ) ^ (2 * K + 1) =
      epsilonDenominator ^ (K + d) * epsilonDenominator ^ (K + 1 - d) := by
    rw [← pow_add]
    congr 1
    omega
  dsimp [d] at hfacQ hpow
  rw [IEpsExplicitNat, epsDenom, IEpsExplicit]
  rw [show (1 : ℚ) + 1 / epsilonDenominator =
    (epsilonDenominator + 1) / epsilonDenominator by
      field_simp]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  rw [facMomentNat_cast, div_pow, hpow, ← hfacQ]
  field_simp [ne_of_gt hε]
  ring_nf

/-- Cleared-denominator radial factor. -/
def radialExplicitInt (K epsilonDenominator q e : ℕ) : ℕ :=
  epsilonDenominator ^ (2 * K + 1 - (q + e)) * (epsilonDenominator - 1) ^ q *
    ∑ m ∈ range (e + 1), e.choose m * 2 ^ (e - m) *
      (epsilonDenominator - 1) ^ m * m ! *
      (2 * K + 1).descFactorial (2 * K + 1 - (m + q))

/-- The integral radial factor casts to its rational value times its common denominator. -/
theorem radialExplicitInt_cast (K epsilonDenominator q e : ℕ)
    (hε : 0 < epsilonDenominator) (hqe : q + e ≤ 2 * K + 1) :
    (radialExplicitInt K epsilonDenominator q e : ℚ) =
      epsilonDenominator ^ (2 * K + 1) * (2 * K + 1)! *
        radialExplicit q (1 / epsilonDenominator) e := by
  rw [radialExplicitInt, radialExplicit]
  rw [show (1 : ℚ) - 1 / epsilonDenominator =
    ((epsilonDenominator - 1 : ℕ) : ℚ) / epsilonDenominator by
      rw [Nat.cast_sub (by omega : 1 ≤ epsilonDenominator)]
      norm_num
      field_simp]
  simp only [Nat.cast_mul, Nat.cast_pow]
  have hcast : (↑(∑ m ∈ range (e + 1),
      e.choose m * 2 ^ (e - m) * (epsilonDenominator - 1) ^ m * m ! *
        (2 * K + 1).descFactorial (2 * K + 1 - (m + q))) : ℚ) =
      ∑ m ∈ range (e + 1), (↑(e.choose m * 2 ^ (e - m) *
        (epsilonDenominator - 1) ^ m * m ! *
        (2 * K + 1).descFactorial (2 * K + 1 - (m + q))) : ℚ) := by
    simp
  rw [hcast, mul_sum]
  conv_rhs => rw [← mul_assoc, mul_sum]
  refine sum_congr rfl fun m hm ↦ ?_
  have hme : m ≤ e := by simp at hm; omega
  have hmq : m + q ≤ 2 * K + 1 := by omega
  have hfac := Nat.factorial_mul_descFactorial
    (show 2 * K + 1 - (m + q) ≤ 2 * K + 1 by omega)
  rw [show 2 * K + 1 - (2 * K + 1 - (m + q)) = m + q by omega] at hfac
  have hfacQ : ((m + q)! : ℚ) *
      ((2 * K + 1).descFactorial (2 * K + 1 - (m + q)) : ℚ) =
      ((2 * K + 1)! : ℚ) := by exact_mod_cast hfac
  have hpow : (epsilonDenominator : ℚ) ^ (2 * K + 1) =
      epsilonDenominator ^ (q + e) * epsilonDenominator ^ (2 * K + 1 - (q + e)) := by
    rw [← pow_add]
    congr 1
    omega
  have hpowE : (epsilonDenominator : ℚ) ^ e =
      epsilonDenominator ^ m * epsilonDenominator ^ (e - m) := by
    rw [← pow_add]
    congr 1
    omega
  have hpowQE : (epsilonDenominator : ℚ) ^ (q + e) =
      epsilonDenominator ^ q * epsilonDenominator ^ e := pow_add _ q e
  rw [div_pow, div_pow, hpow, ← hfacQ]
  simp only [Nat.cast_mul, Nat.cast_pow]
  rw [show (2 : ℚ) * (1 / epsilonDenominator) = 2 / epsilonDenominator by ring]
  rw [div_pow, hpowQE, hpowE]
  field_simp [ne_of_gt hε]
  ring

/-- One marginal factorial quotient with its degree-dependent denominator cleared. -/
def marginalFactorInt (degreeBound a r : ℕ) : ℕ :=
  r ! * a ! * (degreeBound + 1).descFactorial (degreeBound - (a + r))

theorem marginalFactorInt_cast (degreeBound a r : ℕ) (har : a + r ≤ degreeBound) :
    (marginalFactorInt degreeBound a r : ℚ) =
      (degreeBound + 1)! * (r ! * a ! / (a + r + 1)! : ℚ) := by
  have hlen : degreeBound - (a + r) ≤ degreeBound + 1 := by omega
  have hsub : degreeBound + 1 - (degreeBound - (a + r)) = a + r + 1 := by omega
  have hfac := Nat.factorial_mul_descFactorial hlen
  rw [hsub] at hfac
  have hfacQ : ((a + r + 1)! : ℚ) *
      ((degreeBound + 1).descFactorial (degreeBound - (a + r)) : ℚ) =
      ((degreeBound + 1)! : ℚ) := by exact_mod_cast hfac
  rw [marginalFactorInt]
  simp only [Nat.cast_mul]
  rw [← hfacQ]
  field_simp

/-- Cleared-denominator marginal pairing, using the specification factorial moment. -/
def JEpsExplicitNat (K epsilonDenominator degreeBound : ℕ) (a₁ : ℕ)
    (α₁ : Multiset ℕ) (a₂ : ℕ) (α₂ : Multiset ℕ) : ℕ :=
  ∑ r₁ ∈ insert 0 α₁.toFinset, ∑ r₂ ∈ insert 0 α₂.toFinset,
    marginalFactorInt degreeBound a₁ r₁ * marginalFactorInt degreeBound a₂ r₂ *
      radialExplicitInt K epsilonDenominator (K - 1 + ((α₁.sum - r₁) + (α₂.sum - r₂)))
        ((a₁ + r₁ + 1) + (a₂ + r₂ + 1)) *
      facMomentNat (K - 1) (α₁.erase r₁) (α₂.erase r₂)

/-- The integral marginal pairing casts to `epsDenom` times the rational pairing. -/
theorem JEpsExplicitNat_cast (K epsilonDenominator degreeBound : ℕ) (a₁ : ℕ)
    (α₁ : Multiset ℕ) (a₂ : ℕ) (α₂ : Multiset ℕ)
    (hα₁ : 0 ∉ α₁) (hα₂ : 0 ∉ α₂) (hε : 0 < epsilonDenominator)
    (hdegreePos : 0 < degreeBound)
    (hdegree : 2 * degreeBound ≤ K)
    (hd₁ : a₁ + α₁.sum ≤ degreeBound) (hd₂ : a₂ + α₂.sum ≤ degreeBound) :
    (JEpsExplicitNat K epsilonDenominator degreeBound a₁ α₁ a₂ α₂ : ℚ) =
      epsDenom K epsilonDenominator degreeBound *
        JEpsExplicit K (1 / epsilonDenominator) a₁ α₁ a₂ α₂ := by
  rw [JEpsExplicitNat, JEpsExplicit, epsDenom]
  have hcastOuter : (↑(∑ r₁ ∈ insert 0 α₁.toFinset, ∑ r₂ ∈ insert 0 α₂.toFinset,
      marginalFactorInt degreeBound a₁ r₁ * marginalFactorInt degreeBound a₂ r₂ *
        radialExplicitInt K epsilonDenominator (K - 1 + ((α₁.sum - r₁) + (α₂.sum - r₂)))
          ((a₁ + r₁ + 1) + (a₂ + r₂ + 1)) *
        facMomentNat (K - 1) (α₁.erase r₁) (α₂.erase r₂) : ℕ) : ℚ) =
      ∑ r₁ ∈ insert 0 α₁.toFinset, (↑(∑ r₂ ∈ insert 0 α₂.toFinset,
        marginalFactorInt degreeBound a₁ r₁ * marginalFactorInt degreeBound a₂ r₂ *
          radialExplicitInt K epsilonDenominator (K - 1 + ((α₁.sum - r₁) + (α₂.sum - r₂)))
            ((a₁ + r₁ + 1) + (a₂ + r₂ + 1)) *
          facMomentNat (K - 1) (α₁.erase r₁) (α₂.erase r₂) : ℕ) : ℚ) := by
    simp
  rw [hcastOuter]
  conv_rhs => rw [mul_sum]
  refine sum_congr rfl fun r₁ hr₁ ↦ ?_
  have hcastInner : (↑(∑ r₂ ∈ insert 0 α₂.toFinset,
      marginalFactorInt degreeBound a₁ r₁ * marginalFactorInt degreeBound a₂ r₂ *
        radialExplicitInt K epsilonDenominator (K - 1 + ((α₁.sum - r₁) + (α₂.sum - r₂)))
          ((a₁ + r₁ + 1) + (a₂ + r₂ + 1)) *
        facMomentNat (K - 1) (α₁.erase r₁) (α₂.erase r₂) : ℕ) : ℚ) =
      ∑ r₂ ∈ insert 0 α₂.toFinset, (↑(marginalFactorInt degreeBound a₁ r₁ *
        marginalFactorInt degreeBound a₂ r₂ *
        radialExplicitInt K epsilonDenominator (K - 1 + ((α₁.sum - r₁) + (α₂.sum - r₂)))
          ((a₁ + r₁ + 1) + (a₂ + r₂ + 1)) *
        facMomentNat (K - 1) (α₁.erase r₁) (α₂.erase r₂) : ℕ) : ℚ) := by
    simp
  rw [hcastInner, mul_sum]
  refine sum_congr rfl fun r₂ hr₂ ↦ ?_
  have hr₁le : r₁ ≤ α₁.sum := by
    rcases mem_insert.mp hr₁ with rfl | hr₁
    · simp
    · exact Multiset.le_sum_of_mem (Multiset.mem_toFinset.mp hr₁)
  have hr₂le : r₂ ≤ α₂.sum := by
    rcases mem_insert.mp hr₂ with rfl | hr₂
    · simp
    · exact Multiset.le_sum_of_mem (Multiset.mem_toFinset.mp hr₂)
  have hsum₁ : r₁ + (α₁.erase r₁).sum = α₁.sum := by
    rcases mem_insert.mp hr₁ with rfl | hr₁
    · simp [Multiset.erase_of_notMem hα₁]
    · exact Multiset.sum_erase (Multiset.mem_toFinset.mp hr₁)
  have hsum₂ : r₂ + (α₂.erase r₂).sum = α₂.sum := by
    rcases mem_insert.mp hr₂ with rfl | hr₂
    · simp [Multiset.erase_of_notMem hα₂]
    · exact Multiset.sum_erase (Multiset.mem_toFinset.mp hr₂)
  have hpair : (a₁ + α₁.sum) + (a₂ + α₂.sum) ≤ K := by omega
  have hradial :
      ((α₁.sum - r₁) + (α₂.sum - r₂)) +
          ((a₁ + r₁ + 1) + (a₂ + r₂ + 1)) =
        (a₁ + α₁.sum) + (a₂ + α₂.sum) + 2 := by omega
  have hqe : K - 1 + ((α₁.sum - r₁) + (α₂.sum - r₂)) +
      ((a₁ + r₁ + 1) + (a₂ + r₂ + 1)) ≤ 2 * K + 1 := by omega
  simp only [Nat.cast_mul]
  rw [marginalFactorInt_cast degreeBound _ _ (by omega),
    marginalFactorInt_cast degreeBound _ _ (by omega),
    radialExplicitInt_cast K epsilonDenominator _ _ hε hqe, facMomentNat_cast]
  simp only [Nat.cast_pow]
  ring_nf

/-- Enlarged-simplex pairing evaluated through a compressed factorial-moment table. -/
def IEpsTableInt (K epsilonDenominator degreeBound : ℕ) (T : FacMomentTable)
    (a₁ : ℕ) (i₁ : Fin T.S) (a₂ : ℕ) (i₂ : Fin T.S) : ℕ :=
  let d := (a₁ + a₂) + ((T.sig i₁).sum + (T.sig i₂).sum)
  (epsilonDenominator + 1) ^ (K + d) * epsilonDenominator ^ (K + 1 - d) *
    (a₁ + a₂)! * T.val K i₁ i₂ *
    (2 * K + 1).descFactorial (K + 1 - d) * (degreeBound + 1)! ^ 2

theorem IEpsTableInt_cast (K epsilonDenominator degreeBound : ℕ)
    (T : FacMomentTable) (hK : K ≤ T.K) (hε : 0 < epsilonDenominator)
    (a₁ : ℕ) (i₁ : Fin T.S) (a₂ : ℕ) (i₂ : Fin T.S)
    (hd : (a₁ + a₂) + ((T.sig i₁).sum + (T.sig i₂).sum) ≤ K) :
    (IEpsTableInt K epsilonDenominator degreeBound T a₁ i₁ a₂ i₂ : ℚ) =
      epsDenom K epsilonDenominator degreeBound *
        IEpsExplicit K (1 / epsilonDenominator) a₁ (T.sig i₁) a₂ (T.sig i₂) := by
  rw [IEpsTableInt, T.val_eq K i₁ i₂ hK]
  exact IEpsExplicitNat_cast K epsilonDenominator degreeBound _ _ _ _ hε hd

/-- Marginal pairing evaluated through a compressed factorial-moment table. -/
def JEpsTableInt (K epsilonDenominator degreeBound : ℕ) (T : FacMomentTable)
    (a₁ : ℕ) (i₁ : Fin T.S) (a₂ : ℕ) (i₂ : Fin T.S) : ℕ :=
  ∑ r₁ ∈ insert 0 (T.sig i₁).toFinset, ∑ r₂ ∈ insert 0 (T.sig i₂).toFinset,
    marginalFactorInt degreeBound a₁ r₁ * marginalFactorInt degreeBound a₂ r₂ *
      radialExplicitInt K epsilonDenominator
        (K - 1 + (((T.sig i₁).sum - r₁) + ((T.sig i₂).sum - r₂)))
        ((a₁ + r₁ + 1) + (a₂ + r₂ + 1)) *
      T.val (K - 1) (T.erase i₁ r₁) (T.erase i₂ r₂)

theorem JEpsTableInt_cast (K epsilonDenominator degreeBound : ℕ)
    (T : FacMomentTable) (hK : K ≤ T.K) (hε : 0 < epsilonDenominator)
    (hdegreePos : 0 < degreeBound)
    (hdegree : 2 * degreeBound ≤ K)
    (a₁ : ℕ) (i₁ : Fin T.S) (a₂ : ℕ) (i₂ : Fin T.S)
    (hd₁ : a₁ + (T.sig i₁).sum ≤ degreeBound) (hd₂ : a₂ + (T.sig i₂).sum ≤ degreeBound) :
    (JEpsTableInt K epsilonDenominator degreeBound T a₁ i₁ a₂ i₂ : ℚ) =
      epsDenom K epsilonDenominator degreeBound *
        JEpsExplicit K (1 / epsilonDenominator) a₁ (T.sig i₁) a₂ (T.sig i₂) := by
  have hEq : JEpsTableInt K epsilonDenominator degreeBound T a₁ i₁ a₂ i₂ =
      JEpsExplicitNat K epsilonDenominator degreeBound a₁ (T.sig i₁) a₂ (T.sig i₂) := by
    rw [JEpsTableInt, JEpsExplicitNat]
    refine sum_congr rfl fun r₁ hr₁ ↦ ?_
    refine sum_congr rfl fun r₂ hr₂ ↦ ?_
    rw [T.val_eq (K - 1) (T.erase i₁ r₁) (T.erase i₂ r₂) (by omega),
      T.erase_sig i₁ r₁ hr₁, T.erase_sig i₂ r₂ hr₂]
  rw [hEq]
  exact JEpsExplicitNat_cast K epsilonDenominator degreeBound _ _ _ _
    (T.zeroFree i₁) (T.zeroFree i₂) hε hdegreePos hdegree hd₁ hd₂

/-- Enlarged-simplex pairing evaluated through a sparse factorial-moment DAG. -/
def IEpsDagInt (K epsilonDenominator degreeBound : ℕ)
    (T : FacMomentDag K degreeBound) (a₁ : ℕ) (i₁ : Fin T.S) (a₂ : ℕ)
    (i₂ : Fin T.S) : ℕ :=
  let d := (a₁ + a₂) + ((T.sig i₁).sum + (T.sig i₂).sum)
  (epsilonDenominator + 1) ^ (K + d) * epsilonDenominator ^ (K + 1 - d) *
    (a₁ + a₂)! * T.valTop i₁ i₂ *
    (2 * K + 1).descFactorial (K + 1 - d) * (degreeBound + 1)! ^ 2

theorem IEpsDagInt_cast (K epsilonDenominator degreeBound : ℕ)
    (T : FacMomentDag K degreeBound) (hε : 0 < epsilonDenominator)
    (a₁ : ℕ) (i₁ : Fin T.S) (a₂ : ℕ) (i₂ : Fin T.S)
    (hd : (a₁ + a₂) + ((T.sig i₁).sum + (T.sig i₂).sum) ≤ K) :
    (IEpsDagInt K epsilonDenominator degreeBound T a₁ i₁ a₂ i₂ : ℚ) =
      epsDenom K epsilonDenominator degreeBound *
        IEpsExplicit K (1 / epsilonDenominator) a₁ (T.sig i₁) a₂ (T.sig i₂) := by
  rw [IEpsDagInt, T.valTop_eq]
  exact IEpsExplicitNat_cast K epsilonDenominator degreeBound _ _ _ _ hε hd

/-- Marginal pairing evaluated through a sparse factorial-moment DAG. -/
def JEpsDagInt (K epsilonDenominator degreeBound : ℕ)
    (T : FacMomentDag K degreeBound) (a₁ : ℕ) (i₁ : Fin T.S) (a₂ : ℕ)
    (i₂ : Fin T.S) : ℕ :=
  ∑ r₁ ∈ insert 0 (T.sig i₁).toFinset, ∑ r₂ ∈ insert 0 (T.sig i₂).toFinset,
    marginalFactorInt degreeBound a₁ r₁ * marginalFactorInt degreeBound a₂ r₂ *
      radialExplicitInt K epsilonDenominator
        (K - 1 + (((T.sig i₁).sum - r₁) + ((T.sig i₂).sum - r₂)))
        ((a₁ + r₁ + 1) + (a₂ + r₂ + 1)) *
      T.valPred (T.erase i₁ r₁) (T.erase i₂ r₂)

theorem JEpsDagInt_cast (K epsilonDenominator degreeBound : ℕ)
    (T : FacMomentDag K degreeBound) (hε : 0 < epsilonDenominator)
    (hdegreePos : 0 < degreeBound) (hdegree : 2 * degreeBound ≤ K)
    (a₁ : ℕ) (i₁ : Fin T.S) (a₂ : ℕ) (i₂ : Fin T.S)
    (hd₁ : a₁ + (T.sig i₁).sum ≤ degreeBound)
    (hd₂ : a₂ + (T.sig i₂).sum ≤ degreeBound) :
    (JEpsDagInt K epsilonDenominator degreeBound T a₁ i₁ a₂ i₂ : ℚ) =
      epsDenom K epsilonDenominator degreeBound *
        JEpsExplicit K (1 / epsilonDenominator) a₁ (T.sig i₁) a₂ (T.sig i₂) := by
  have hEq : JEpsDagInt K epsilonDenominator degreeBound T a₁ i₁ a₂ i₂ =
      JEpsExplicitNat K epsilonDenominator degreeBound a₁ (T.sig i₁) a₂ (T.sig i₂) := by
    rw [JEpsDagInt, JEpsExplicitNat]
    refine sum_congr rfl fun r₁ hr₁ ↦ ?_
    refine sum_congr rfl fun r₂ hr₂ ↦ ?_
    rw [T.valPred_eq, T.erase_sig i₁ r₁ hr₁, T.erase_sig i₂ r₂ hr₂]
  rw [hEq]
  exact JEpsExplicitNat_cast K epsilonDenominator degreeBound _ _ _ _
    (T.zeroFree i₁) (T.zeroFree i₂) hε hdegreePos hdegree hd₁ hd₂

/-- The multiplicity classes of a signature. -/
def signatureGroups (α : List ℕ) : List (ℕ × ℕ) :=
  α.eraseDups.map fun x ↦ (x, α.count x)

/-- The product of the factorial weights of the unmatched entries of a signature. -/
def signatureFactorialWeight (α : Multiset ℕ) : ℕ :=
  ∏ x ∈ α.toFinset, x ! ^ α.count x

/-- The factorial weight contributed when the entries of `γ` overlap a block of entries equal
to `x`, while the remaining entries of the block are unmatched. -/
def overlapFactorialWeight (x m : ℕ) (γ : Multiset ℕ) : ℕ :=
  x ! ^ (m - γ.card) * ∏ y ∈ γ.toFinset, (x + y)! ^ γ.count y

/-- Direct overlap-profile evaluation of a factorial moment. Each pair `(x, m)` is one
multiplicity class in the first signature. For that class, `γ` records the submultiset of the
second signature placed on the same coordinates. -/
def facMomentOverlapCore : ℕ → List (ℕ × ℕ) → Multiset ℕ → ℕ
  | k, [], β =>
      k.choose β.card * Nat.multinomial β.toFinset β.count * signatureFactorialWeight β
  | k, (x, m) :: groups, β =>
      k.choose m * ∑ γ ∈ Finset.Iic β,
        if γ.card ≤ m then
          m.choose γ.card * Nat.multinomial γ.toFinset γ.count *
            overlapFactorialWeight x m γ * facMomentOverlapCore (k - m) groups (β - γ)
        else 0

/-- The multiset represented by aligned value and multiplicity vectors. -/
def countsSignature : List ℕ → List ℕ → Multiset ℕ
  | y :: ys, n :: ns => Multiset.replicate n y + countsSignature ys ns
  | _, _ => 0

/-- All pointwise-bounded count vectors for a fixed multiplicity vector. -/
def countProfiles : List ℕ → List (List ℕ)
  | [] => [[]]
  | n :: ns => (List.range (n + 1)).flatMap fun i =>
      (countProfiles ns).map (i :: ·)

/-- The multinomial coefficient of a count vector, evaluated by successive binomial choices. -/
def countMultinomial : List ℕ → ℕ
  | [] => 1
  | n :: ns => (n + ns.sum).choose n * countMultinomial ns

/-- A count vector's factorial contribution against a block of equal exponents. -/
def countOverlapWeight (x slots : ℕ) (values counts : List ℕ) : ℕ :=
  x ! ^ (slots - counts.sum) *
    (List.zipWith (fun y n ↦ (x + y)! ^ n) values counts).prod

/-- A remaining signature's factorial contribution after all left blocks are assigned. -/
def countSignatureWeight (values counts : List ℕ) : ℕ :=
  (List.zipWith (fun y n ↦ y ! ^ n) values counts).prod

/-- Subtract one aligned count vector from another. -/
def subtractCounts (counts used : List ℕ) : List ℕ :=
  List.zipWith (fun n i ↦ n - i) counts used

private theorem mem_countProfiles (used counts : List ℕ) :
    used ∈ countProfiles counts ↔ List.Forall₂ (· ≤ ·) used counts := by
  induction counts generalizing used with
  | nil => simp [countProfiles]
  | cons n ns ih =>
      constructor
      · simp only [countProfiles, List.mem_flatMap, List.mem_range, List.mem_map]
        rintro ⟨i, hi, tail, htail, rfl⟩
        exact .cons (by omega) (ih tail |>.mp htail)
      · intro h
        cases h with
        | cons hi htail =>
            simp only [countProfiles, List.mem_flatMap, List.mem_range, List.mem_map]
            exact ⟨_, by omega, _, ih _ |>.mpr htail, rfl⟩

private theorem countProfiles_nodup (counts : List ℕ) : (countProfiles counts).Nodup := by
  induction counts with
  | nil => simp [countProfiles]
  | cons n ns ih =>
      rw [countProfiles]
      apply List.nodup_flatMap.2
      refine ⟨?_, ?_⟩
      · intro i hi
        exact ih.map (by simp_all)
      rw [List.pairwise_iff_get]
      intro a b hab
      apply List.disjoint_left.2
      intro z hza hzb
      simp only [List.mem_map] at hza hzb
      obtain ⟨ta, _, rfl⟩ := hza
      obtain ⟨tb, _, htb⟩ := hzb
      have := congrArg List.head? htb
      simp only [List.head?_cons, Option.some.injEq] at this
      exact (Fin.ne_of_lt hab) (List.nodup_range.get_inj_iff.mp this.symm)

private theorem mem_countsSignature {values counts : List ℕ} {y : ℕ}
    (hy : y ∈ countsSignature values counts) : y ∈ values := by
  induction values generalizing counts with
  | nil => simp [countsSignature] at hy
  | cons x xs ih =>
      cases counts with
      | nil => simp [countsSignature] at hy
      | cons n ns =>
          rw [countsSignature, Multiset.mem_add] at hy
          rcases hy with hy | hy
          · simp only [Multiset.mem_replicate] at hy
            exact List.mem_cons.mpr (.inl hy.2)
          · exact List.mem_cons.mpr (.inr (ih hy))

private theorem card_countsSignature (values counts : List ℕ)
    (hlen : values.length = counts.length) :
    (countsSignature values counts).card = counts.sum := by
  induction values generalizing counts with
  | nil =>
      cases counts <;> simp_all [countsSignature]
  | cons x xs ih =>
      cases counts with
      | nil => simp at hlen
      | cons n ns =>
          simp only [countsSignature, Multiset.card_add, Multiset.card_replicate,
            List.sum_cons]
          rw [ih ns (by simpa using hlen)]

private theorem countsSignature_counts_cons (x n : ℕ) (tail : Multiset ℕ)
    {values counts : List ℕ} (hx : x ∉ values)
    (h : List.Forall₂ (fun y m ↦ tail.count y = m) values counts) :
    List.Forall₂ (fun y m ↦ (Multiset.replicate n x + tail).count y = m)
      values counts := by
  induction h with
  | nil => exact .nil
  | @cons y m values counts hym htail ih =>
      rw [List.mem_cons, not_or] at hx
      apply List.Forall₂.cons
      · rw [Multiset.count_add, Multiset.count_replicate, if_neg hx.1, zero_add, hym]
      · exact ih hx.2

private theorem countsSignature_counts (values counts : List ℕ) (hvalues : values.Nodup)
    (hlen : values.length = counts.length) :
    List.Forall₂ (fun y n ↦ (countsSignature values counts).count y = n) values counts := by
  induction values generalizing counts with
  | nil =>
      cases counts <;> simp_all
  | cons x xs ih =>
      cases counts with
      | nil => simp at hlen
      | cons n ns =>
          rw [List.nodup_cons] at hvalues
          have htail := ih ns hvalues.2 (by simpa using hlen)
          apply List.Forall₂.cons
          · rw [countsSignature, Multiset.count_add, Multiset.count_replicate,
              if_pos rfl, Multiset.count_eq_zero.mpr
                (fun hx ↦ hvalues.1 (mem_countsSignature hx)), add_zero]
          · exact countsSignature_counts_cons x n (countsSignature xs ns) hvalues.1 htail

private theorem countsSignature_mono {used counts : List ℕ}
    (h : List.Forall₂ (· ≤ ·) used counts) (values : List ℕ)
    (hlen : values.length = counts.length) :
    countsSignature values used ≤ countsSignature values counts := by
  induction h generalizing values with
  | nil =>
      cases values <;> simp_all [countsSignature]
  | @cons u n used counts hun htail ih =>
      cases values with
      | nil => simp at hlen
      | cons y ys =>
          simp only [countsSignature]
          exact add_le_add ((Multiset.replicate_le_replicate y).2 hun)
            (ih ys (by simpa using hlen))

private theorem count_countsSignature_countsOf (values : List ℕ) (m : Multiset ℕ)
    (hvalues : values.Nodup) (y : ℕ) :
    (countsSignature values (values.map m.count)).count y =
      if y ∈ values then m.count y else 0 := by
  induction values with
  | nil => simp [countsSignature]
  | cons x xs ih =>
      rw [List.nodup_cons] at hvalues
      simp only [List.map_cons, countsSignature, Multiset.count_add,
        Multiset.count_replicate, List.mem_cons]
      by_cases hxy : x = y
      · subst x
        simp [hvalues.1, ih hvalues.2]
      · by_cases hy : y ∈ xs <;> simp [hxy, Ne.symm hxy, hy, ih hvalues.2]

private theorem countsSignature_countsOf_eq (values : List ℕ) (m : Multiset ℕ)
    (hvalues : values.Nodup) (hsupport : ∀ y ∈ m, y ∈ values) :
    countsSignature values (values.map m.count) = m := by
  ext y
  rw [count_countsSignature_countsOf values m hvalues y]
  by_cases hy : y ∈ values
  · rw [if_pos hy]
  · rw [if_neg hy, Multiset.count_eq_zero.mpr]
    exact fun hym ↦ hy (hsupport y hym)

private theorem countsRelation_unique (m : Multiset ℕ) {values used counts : List ℕ}
    (hused : List.Forall₂ (fun y n ↦ m.count y = n) values used)
    (hcounts : List.Forall₂ (fun y n ↦ m.count y = n) values counts) : used = counts := by
  induction hused generalizing counts with
  | nil => exact (List.forall₂_nil_left_iff.mp hcounts).symm
  | @cons y u values used hyu htail ih =>
      rw [List.forall₂_cons_left_iff] at hcounts
      obtain ⟨n, counts, hyn, hcounts, rfl⟩ := hcounts
      rw [hyu] at hyn
      subst n
      exact congrArg (u :: ·) (ih hcounts)

private theorem countsSignature_injective_on (values used counts : List ℕ)
    (hvalues : values.Nodup) (hu : values.length = used.length)
    (hc : values.length = counts.length)
    (heq : countsSignature values used = countsSignature values counts) : used = counts := by
  have hused := countsSignature_counts values used hvalues hu
  have hcounts := countsSignature_counts values counts hvalues hc
  rw [heq] at hused
  exact countsRelation_unique (countsSignature values counts) hused hcounts

private theorem map_eq_of_forall₂ {f : ℕ → ℕ} {values counts : List ℕ}
    (h : List.Forall₂ (fun y n ↦ f y = n) values counts) : values.map f = counts := by
  induction h with
  | nil => rfl
  | cons hhead htail ih => simp only [List.map_cons, hhead, ih]

private theorem map_count_countsSignature_eq (values counts : List ℕ)
    (hvalues : values.Nodup) (hlen : values.length = counts.length) :
    values.map (countsSignature values counts).count = counts := by
  have h := countsSignature_counts values counts hvalues hlen
  exact map_eq_of_forall₂ h

private theorem countsOf_forall₂_le {values counts : List ℕ} {m base : Multiset ℕ}
    (hm : m ≤ base)
    (hbase : List.Forall₂ (fun y n ↦ base.count y = n) values counts) :
    List.Forall₂ (· ≤ ·) (values.map m.count) counts := by
  induction hbase with
  | nil => exact .nil
  | @cons y n values counts hyn htail ih =>
      exact .cons (by rw [← hyn]; exact Multiset.le_iff_count.mp hm y) ih

private theorem sum_countProfiles (values counts : List ℕ) (hvalues : values.Nodup)
    (hlen : values.length = counts.length) (f : List ℕ → ℕ) :
    ((countProfiles counts).map f).sum =
      ∑ m ∈ Finset.Iic (countsSignature values counts), f (values.map m.count) := by
  rw [← List.sum_toFinset f (countProfiles_nodup counts)]
  apply Finset.sum_bij (fun used _ ↦ countsSignature values used)
  · intro used hused
    rw [List.mem_toFinset, mem_countProfiles] at hused
    rw [Finset.mem_Iic]
    exact countsSignature_mono hused values hlen
  · intro used₁ hused₁ used₂ hused₂ heq
    rw [List.mem_toFinset, mem_countProfiles] at hused₁ hused₂
    exact countsSignature_injective_on values used₁ used₂ hvalues
      (by rw [hused₁.length_eq, hlen]) (by rw [hused₂.length_eq, hlen]) heq
  · intro m hm
    rw [Finset.mem_Iic] at hm
    have hbase := countsSignature_counts values counts hvalues hlen
    let used := values.map m.count
    have hused : List.Forall₂ (· ≤ ·) used counts :=
      countsOf_forall₂_le hm hbase
    have hsupport : ∀ y ∈ m, y ∈ values := by
      intro y hym
      have hybase := Multiset.subset_of_le hm hym
      exact mem_countsSignature hybase
    exact ⟨used, List.mem_toFinset.mpr (mem_countProfiles used counts |>.mpr hused),
      countsSignature_countsOf_eq values m hvalues hsupport⟩
  · intro used hused
    rw [List.mem_toFinset, mem_countProfiles] at hused
    rw [map_count_countsSignature_eq values used hvalues
      (by rw [hused.length_eq, hlen])]

private theorem countMultinomial_eq_countPerms (values counts : List ℕ)
    (hvalues : values.Nodup) (hlen : values.length = counts.length) :
    countMultinomial counts = (countsSignature values counts).countPerms := by
  induction values generalizing counts with
  | nil =>
      cases counts <;> simp_all [countMultinomial, countsSignature]
  | cons x xs ih =>
      cases counts with
      | nil => simp at hlen
      | cons n ns =>
          rw [List.nodup_cons] at hvalues
          rw [countMultinomial, Multiset.countPerms_filter_ne x]
          have htail : x ∉ countsSignature xs ns :=
            fun hx ↦ hvalues.1 (mem_countsSignature hx)
          simp only [countsSignature, Multiset.card_add, Multiset.card_replicate,
            Multiset.count_add, Multiset.count_replicate]
          rw [if_true, Multiset.count_eq_zero.mpr htail, add_zero]
          rw [show (Multiset.replicate n x + countsSignature xs ns).filter (x ≠ ·) =
              countsSignature xs ns by
            rw [Multiset.filter_add, Multiset.filter_eq_nil.mpr, zero_add,
              Multiset.filter_eq_self.mpr]
            · intro y hy
              exact fun hxy ↦ htail (hxy.symm ▸ hy)
            · intro y hy
              simpa using (Multiset.eq_of_mem_replicate hy).symm]
          rw [card_countsSignature xs ns (by simpa using hlen)]
          rw [ih ns hvalues.2 (by simpa using hlen)]

private theorem countMultinomial_eq (values counts : List ℕ) (hvalues : values.Nodup)
    (hlen : values.length = counts.length) :
    countMultinomial counts = Nat.multinomial (countsSignature values counts).toFinset
      (countsSignature values counts).count := by
  rw [countMultinomial_eq_countPerms values counts hvalues hlen,
    Multiset.countPerms, Finsupp.multinomial_eq, Multiset.toFinsupp_support]
  congr 1

private theorem map_count_sub_eq_subtractCounts (values counts used : List ℕ)
    (base chosen : Multiset ℕ)
    (hbase : List.Forall₂ (fun y n ↦ base.count y = n) values counts)
    (hchosen : List.Forall₂ (fun y n ↦ chosen.count y = n) values used) :
    values.map (base - chosen).count = subtractCounts counts used := by
  induction hbase generalizing used with
  | nil =>
      rw [List.forall₂_nil_left_iff] at hchosen
      subst used
      rfl
  | @cons y n values counts hyn htail ih =>
      rw [List.forall₂_cons_left_iff] at hchosen
      obtain ⟨i, used, hyi, hchosen, rfl⟩ := hchosen
      simpa only [List.map, subtractCounts, List.zipWith, Multiset.count_sub, hyn, hyi]
        using congrArg (fun tail ↦ (n - i) :: tail) (ih used hchosen)

private theorem countsSignature_subtract (values counts used : List ℕ)
    (hvalues : values.Nodup) (hcounts : values.length = counts.length)
    (hused : values.length = used.length) :
    countsSignature values (subtractCounts counts used) =
      countsSignature values counts - countsSignature values used := by
  let base := countsSignature values counts
  let chosen := countsSignature values used
  have hbase := countsSignature_counts values counts hvalues hcounts
  have hchosen := countsSignature_counts values used hvalues hused
  have hsupport : ∀ y ∈ base - chosen, y ∈ values := by
    intro y hy
    exact mem_countsSignature (Multiset.mem_of_le (Multiset.sub_le_self base chosen) hy)
  have hcanonical := countsSignature_countsOf_eq values (base - chosen) hvalues hsupport
  rw [map_count_sub_eq_subtractCounts values counts used base chosen hbase hchosen] at hcanonical
  exact hcanonical

private theorem length_subtractCounts (counts used : List ℕ)
    (hlen : counts.length = used.length) :
    (subtractCounts counts used).length = counts.length := by
  simp [subtractCounts, List.length_zipWith, hlen]

/-- Factorial-moment overlap evaluation using only aligned natural-number count vectors. -/
def facMomentCountCore : ℕ → List (ℕ × ℕ) → List ℕ → List ℕ → ℕ
  | k, [], values, counts =>
      k.choose counts.sum * countMultinomial counts * countSignatureWeight values counts
  | k, (x, slots) :: groups, values, counts =>
      k.choose slots * ((countProfiles counts).map fun used =>
        if used.sum ≤ slots then
          slots.choose used.sum * countMultinomial used *
            countOverlapWeight x slots values used *
              facMomentCountCore (k - slots) groups values (subtractCounts counts used)
        else 0).sum

/-- Evaluate two dimensions through one traversal of aligned natural-number count vectors. -/
def facMomentCountPairCore :
    ℕ → ℕ → List (ℕ × ℕ) → List ℕ → List ℕ → ℕ × ℕ
  | k, l, [], values, counts =>
      let common := countMultinomial counts * countSignatureWeight values counts
      (k.choose counts.sum * common, l.choose counts.sum * common)
  | k, l, (x, slots) :: groups, values, counts =>
      let total := ((countProfiles counts).map fun used =>
        if used.sum ≤ slots then
          let weight := slots.choose used.sum * countMultinomial used *
            countOverlapWeight x slots values used
          let child := facMomentCountPairCore (k - slots) (l - slots) groups values
            (subtractCounts counts used)
          (weight * child.1, weight * child.2)
        else (0, 0)).sum
      (k.choose slots * total.1, l.choose slots * total.2)

private theorem listSumProd_fst (xs : List (ℕ × ℕ)) : xs.sum.1 = (xs.map Prod.fst).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.sum_cons, List.map_cons, Prod.fst_add, ih]

private theorem listSumProd_snd (xs : List (ℕ × ℕ)) : xs.sum.2 = (xs.map Prod.snd).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.sum_cons, List.map_cons, Prod.snd_add, ih]

private theorem facMomentCountPairCore_fst (k l : ℕ) (groups : List (ℕ × ℕ))
    (values counts : List ℕ) :
    (facMomentCountPairCore k l groups values counts).1 =
      facMomentCountCore k groups values counts := by
  induction groups generalizing k l counts with
  | nil => simp [facMomentCountPairCore, facMomentCountCore, mul_assoc]
  | cons group groups ih =>
      obtain ⟨x, slots⟩ := group
      simp only [facMomentCountPairCore, facMomentCountCore]
      apply congrArg (k.choose slots * ·)
      rw [listSumProd_fst, List.map_map]
      apply congrArg List.sum
      refine List.map_congr_left fun used hused ↦ ?_
      simp only [Function.comp_apply]
      split_ifs
      · rw [ih]
      · rfl

private theorem facMomentCountPairCore_snd (k l : ℕ) (groups : List (ℕ × ℕ))
    (values counts : List ℕ) :
    (facMomentCountPairCore k l groups values counts).2 =
      facMomentCountCore l groups values counts := by
  induction groups generalizing k l counts with
  | nil => simp [facMomentCountPairCore, facMomentCountCore, mul_assoc]
  | cons group groups ih =>
      obtain ⟨x, slots⟩ := group
      simp only [facMomentCountPairCore, facMomentCountCore]
      apply congrArg (l.choose slots * ·)
      rw [listSumProd_snd, List.map_map]
      apply congrArg List.sum
      refine List.map_congr_left fun used hused ↦ ?_
      simp only [Function.comp_apply]
      split_ifs
      · rw [ih]
      · rfl

private def denominator (s : Finset ℕ) (m : Multiset ℕ) : ℕ :=
  ∏ x ∈ s, (m.count x)!

private theorem denominator_erase (m : Multiset ℕ) {a : ℕ} (ha : a ∈ m) :
    denominator m.toFinset m = m.count a * denominator m.toFinset (m.erase a) := by
  rw [denominator, denominator]
  conv_lhs => rw [← Finset.mul_prod_erase _ _ (Multiset.mem_toFinset.mpr ha)]
  conv_rhs => rw [← Finset.mul_prod_erase _ _ (Multiset.mem_toFinset.mpr ha)]
  rw [Multiset.count_erase_self]
  have hp : (∏ x ∈ m.toFinset.erase a, (m.count x)!) =
      ∏ x ∈ m.toFinset.erase a, ((m.erase a).count x)! := by
    refine Finset.prod_congr rfl fun x hx ↦ ?_
    rw [Finset.mem_erase] at hx
    rw [Multiset.count_erase_of_ne hx.1]
  rw [hp]
  have hc : m.count a = m.count a - 1 + 1 :=
    (Nat.sub_add_cancel (Multiset.count_pos.mpr ha)).symm
  conv_lhs => rw [hc, Nat.factorial_succ]
  rw [← hc, Nat.mul_assoc]

private theorem denominator_mul_countPerms (m : Multiset ℕ) :
    denominator m.toFinset m * m.countPerms = m.card ! := by
  rw [Multiset.countPerms, Finsupp.multinomial_eq, Multiset.toFinsupp_support]
  change denominator m.toFinset m * Nat.multinomial m.toFinset m.count = _
  rw [denominator, Nat.multinomial_spec]
  simp

private theorem denominator_mul_countPerms_erase (m : Multiset ℕ) {a : ℕ} (ha : a ∈ m) :
    denominator m.toFinset (m.erase a) * (m.erase a).countPerms =
      (m.card - 1) ! := by
  have hsupp : (m.erase a).toFinsupp.support ⊆ m.toFinset := by
    intro x hx
    simp only [Finsupp.mem_support_iff, Multiset.toFinsupp_apply, ne_eq] at hx
    exact Multiset.mem_toFinset.mpr <| Multiset.mem_of_mem_erase <|
      Multiset.count_pos.mp (Nat.pos_of_ne_zero hx)
  rw [Multiset.countPerms, Finsupp.multinomial_eq_of_support_subset hsupp]
  change denominator m.toFinset (m.erase a) *
    Nat.multinomial m.toFinset (m.erase a).count = _
  rw [denominator, Nat.multinomial_spec]
  have hsub : (m.erase a).toFinset ⊆ m.toFinset := by
    intro x hx
    exact Multiset.mem_toFinset.mpr <| Multiset.mem_of_mem_erase <|
      Multiset.mem_toFinset.mp hx
  have hsum : (∑ i ∈ m.toFinset, (m.erase a).count i) =
      ∑ i ∈ (m.erase a).toFinset, (m.erase a).count i := by
    symm
    refine Finset.sum_subset hsub fun x _ hx ↦ ?_
    rw [Multiset.count_eq_zero.mpr]
    exact fun h ↦ hx (Multiset.mem_toFinset.mpr h)
  rw [hsum]
  simp [Multiset.card_erase_of_mem ha, Nat.pred_eq_sub_one]

private theorem sum_countPerms_erase (m : Multiset ℕ) (hm : m ≠ 0) :
    (∑ a ∈ m.toFinset, (m.erase a).countPerms) = m.countPerms := by
  have hden : 0 < denominator m.toFinset m :=
    Finset.prod_pos fun _ _ ↦ Nat.factorial_pos _
  apply Nat.eq_of_mul_eq_mul_left hden
  rw [mul_sum, denominator_mul_countPerms]
  calc
    ∑ a ∈ m.toFinset, denominator m.toFinset m * (m.erase a).countPerms =
        ∑ a ∈ m.toFinset, m.count a * (m.card - 1) ! := by
      refine Finset.sum_congr rfl fun a ha ↦ ?_
      have ham : a ∈ m := Multiset.mem_toFinset.mp ha
      rw [denominator_erase m ham, Nat.mul_assoc,
        denominator_mul_countPerms_erase m ham]
    _ = m.card * (m.card - 1) ! := by
      rw [← Finset.sum_mul]
      simp
    _ = m.card ! := by
      have hcard : 0 < m.card := Multiset.card_pos.mpr hm
      exact Nat.mul_factorial_pred (Nat.ne_of_gt hcard)

private theorem count_mul_countPerms_erase (m : Multiset ℕ) {a : ℕ} (ha : a ∈ m) :
    m.count a * m.countPerms = m.card * (m.erase a).countPerms := by
  have hden : 0 < denominator m.toFinset (m.erase a) :=
    Finset.prod_pos fun _ _ ↦ Nat.factorial_pos _
  apply Nat.eq_of_mul_eq_mul_left hden
  calc
    denominator m.toFinset (m.erase a) * (m.count a * m.countPerms) =
        denominator m.toFinset m * m.countPerms := by
      rw [denominator_erase m ha]
      ring_nf
    _ = m.card ! := denominator_mul_countPerms m
    _ = m.card * (m.card - 1) ! :=
      (Nat.mul_factorial_pred (Nat.ne_of_gt (Multiset.card_pos.mpr fun h ↦ by
        subst m; simp at ha))).symm
    _ = m.card * (denominator m.toFinset (m.erase a) * (m.erase a).countPerms) := by
      rw [denominator_mul_countPerms_erase m ha]
    _ = denominator m.toFinset (m.erase a) *
        (m.card * (m.erase a).countPerms) := by
      ring_nf

private def placements (slots : ℕ) (m : Multiset ℕ) : ℕ :=
  slots.choose m.card * Nat.multinomial m.toFinset m.count

private theorem placements_eq_zero {slots : ℕ} {m : Multiset ℕ} (h : slots < m.card) :
    placements slots m = 0 := by simp [placements, Nat.choose_eq_zero_of_lt h]

private theorem placements_pascal (slots : ℕ) (m : Multiset ℕ) :
    placements (slots + 1) m = placements slots m +
      ∑ a ∈ m.toFinset, placements slots (m.erase a) := by
  by_cases hm : m = 0
  · subst m
    simp [placements]
  have hcard : 0 < m.card := Multiset.card_pos.mpr hm
  have hsucc : m.card - 1 + 1 = m.card := Nat.sub_add_cancel hcard
  rw [placements, placements]
  have hsum : (∑ a ∈ m.toFinset, placements slots (m.erase a)) =
      slots.choose (m.card - 1) * ∑ a ∈ m.toFinset, (m.erase a).countPerms := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    rw [placements, Multiset.card_erase_of_mem (Multiset.mem_toFinset.mp ha),
      Nat.pred_eq_sub_one]
    rw [Multiset.countPerms, Finsupp.multinomial_eq, Multiset.toFinsupp_support]
    congr 2
  rw [hsum, show Nat.multinomial m.toFinset m.count = m.countPerms by
    rw [Multiset.countPerms, Finsupp.multinomial_eq, Multiset.toFinsupp_support]
    rfl]
  rw [sum_countPerms_erase m hm, ← Nat.add_mul]
  have hchoose := Nat.choose_succ_succ' slots (m.card - 1)
  rw [hsucc, Nat.add_comm] at hchoose
  have hchoose' : (slots + 1).choose m.card =
      slots.choose m.card + slots.choose (m.card - 1) := by
    simpa [Nat.add_comm] using hchoose
  exact congrArg (fun n ↦ n * m.countPerms) hchoose'

private theorem sum_Iic_erase (m : Multiset ℕ) {a : ℕ} (ha : a ∈ m)
    (f : Multiset ℕ → ℕ) :
    (∑ d ∈ (Finset.Iic m).filter (a ∈ ·), f (d.erase a)) =
      ∑ e ∈ Finset.Iic (m.erase a), f e := by
  symm
  apply Finset.sum_bij (fun e _ ↦ a ::ₘ e)
  · intro e he
    rw [Finset.mem_Iic] at he
    rw [Finset.mem_filter, Finset.mem_Iic]
    refine ⟨?_, by simp⟩
    rwa [← Multiset.cons_erase ha, Multiset.cons_le_cons_iff]
  · intro e₁ he₁ e₂ he₂ h
    exact (Multiset.cons_inj_right a).mp h
  · intro d hd
    rw [Finset.mem_filter, Finset.mem_Iic] at hd
    refine ⟨d.erase a, Finset.mem_Iic.mpr (Multiset.erase_le_erase a hd.1), ?_⟩
    rw [Multiset.cons_erase hd.2]
  · intro e he
    rw [Multiset.erase_cons_head]

private theorem sum_Iic_erase_swap (m : Multiset ℕ)
    (f : ℕ → Multiset ℕ → ℕ) :
    (∑ d ∈ Finset.Iic m, ∑ a ∈ d.toFinset, f a (d.erase a)) =
      ∑ a ∈ m.toFinset, ∑ e ∈ Finset.Iic (m.erase a), f a e := by
  have hinner : ∀ d ∈ Finset.Iic m,
      (∑ a ∈ d.toFinset, f a (d.erase a)) =
        ∑ a ∈ m.toFinset, if a ∈ d then f a (d.erase a) else 0 := by
    intro d hd
    rw [Finset.mem_Iic] at hd
    calc
      (∑ a ∈ d.toFinset, f a (d.erase a)) =
          ∑ a ∈ d.toFinset, if a ∈ d then f a (d.erase a) else 0 := by
        refine Finset.sum_congr rfl fun a ha ↦ ?_
        rw [if_pos (Multiset.mem_toFinset.mp ha)]
      _ = ∑ a ∈ m.toFinset, if a ∈ d then f a (d.erase a) else 0 := by
        apply Finset.sum_subset
        · intro a ha
          exact Multiset.mem_toFinset.mpr <| Multiset.subset_of_le hd <|
            Multiset.mem_toFinset.mp ha
        · intro a _ ha
          have had : a ∉ d := fun h ↦ ha (Multiset.mem_toFinset.mpr h)
          rw [if_neg had]
  have hexpand : (∑ d ∈ Finset.Iic m, ∑ a ∈ d.toFinset, f a (d.erase a)) =
      ∑ d ∈ Finset.Iic m, ∑ a ∈ m.toFinset,
        if a ∈ d then f a (d.erase a) else 0 := by
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    exact hinner d hd
  rw [hexpand, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  rw [← Finset.sum_filter]
  exact sum_Iic_erase m (Multiset.mem_toFinset.mp ha) (f a)

private theorem overlapFactorialWeight_eq (x slots : ℕ) (m : Multiset ℕ) :
    overlapFactorialWeight x slots m =
      x ! ^ (slots - m.card) * (m.map fun y ↦ (x + y)!).prod := by
  rw [overlapFactorialWeight, Finset.prod_multiset_map_count]

private theorem signatureFactorialWeight_eq (m : Multiset ℕ) :
    signatureFactorialWeight m = (m.map Nat.factorial).prod := by
  rw [signatureFactorialWeight, Finset.prod_multiset_map_count]

private theorem countSignatureWeight_eq (values counts : List ℕ)
    (hlen : values.length = counts.length) :
    countSignatureWeight values counts =
      signatureFactorialWeight (countsSignature values counts) := by
  rw [signatureFactorialWeight_eq]
  induction values generalizing counts with
  | nil =>
      cases counts <;> simp_all [countSignatureWeight, countsSignature]
  | cons x xs ih =>
      cases counts with
      | nil => simp at hlen
      | cons n ns =>
          simp only [countSignatureWeight, List.zipWith, List.prod_cons, countsSignature,
            Multiset.map_add, Multiset.prod_add, Multiset.map_replicate,
            Multiset.prod_replicate]
          congr 1
          exact ih ns (by simpa using hlen)

private theorem countOverlapWeight_eq (x slots : ℕ) (values counts : List ℕ)
    (hlen : values.length = counts.length) :
    countOverlapWeight x slots values counts =
      overlapFactorialWeight x slots (countsSignature values counts) := by
  rw [overlapFactorialWeight_eq, card_countsSignature values counts hlen]
  simp only [countOverlapWeight]
  congr 1
  induction values generalizing counts with
  | nil =>
      cases counts <;> simp_all [countsSignature]
  | cons y ys ih =>
      cases counts with
      | nil => simp at hlen
      | cons n ns =>
          simp only [List.zipWith, List.prod_cons, countsSignature, Multiset.map_add,
            Multiset.prod_add, Multiset.map_replicate, Multiset.prod_replicate]
          congr 1
          exact ih ns (by simpa using hlen)

private theorem facMomentCountCore_eq_overlapCore (k : ℕ) (groups : List (ℕ × ℕ))
    (values counts : List ℕ) (hvalues : values.Nodup)
    (hlen : values.length = counts.length) :
    facMomentCountCore k groups values counts =
      facMomentOverlapCore k groups (countsSignature values counts) := by
  induction groups generalizing k counts with
  | nil =>
      simp only [facMomentCountCore, facMomentOverlapCore]
      rw [card_countsSignature values counts hlen,
        countMultinomial_eq values counts hvalues hlen,
        countSignatureWeight_eq values counts hlen]
  | cons group groups ih =>
      obtain ⟨x, slots⟩ := group
      simp only [facMomentCountCore, facMomentOverlapCore]
      apply congrArg (k.choose slots * ·)
      rw [sum_countProfiles values counts hvalues hlen]
      refine Finset.sum_congr rfl fun chosen hchosenMem ↦ ?_
      rw [Finset.mem_Iic] at hchosenMem
      let used := values.map chosen.count
      have husedLen : values.length = used.length := by simp [used]
      have hsupport : ∀ y ∈ chosen, y ∈ values := by
        intro y hy
        exact mem_countsSignature (Multiset.subset_of_le hchosenMem hy)
      have husedSig : countsSignature values used = chosen :=
        countsSignature_countsOf_eq values chosen hvalues hsupport
      have husedSum : used.sum = chosen.card := by
        rw [← card_countsSignature values used husedLen, husedSig]
      have husedSumExplicit : (values.map chosen.count).sum = chosen.card := by
        simpa [used] using husedSum
      have hsubtractLen : values.length = (subtractCounts counts used).length := by
        rw [length_subtractCounts counts used (by omega)]
        exact hlen
      by_cases hcard : chosen.card ≤ slots
      · rw [if_pos (husedSum.trans_le hcard), if_pos hcard,
          countMultinomial_eq values used hvalues husedLen, husedSig,
          countOverlapWeight_eq x slots values used husedLen,
          ih (k - slots) (subtractCounts counts used) hsubtractLen,
          countsSignature_subtract values counts used hvalues hlen husedLen]
        simp only [husedSumExplicit, husedSig]
      · rw [if_neg (fun h ↦ hcard (husedSum ▸ h)), if_neg hcard]

private theorem signatureFactorialWeight_erase (m : Multiset ℕ) {a : ℕ} (ha : a ∈ m) :
    signatureFactorialWeight m = a ! * signatureFactorialWeight (m.erase a) := by
  rw [signatureFactorialWeight_eq, signatureFactorialWeight_eq]
  conv_lhs => rw [← Multiset.cons_erase ha, Multiset.map_cons, Multiset.prod_cons]

private theorem facMomentNat_empty_left (k : ℕ) (β : Multiset ℕ) (hβ : 0 ∉ β) :
    facMomentNat k 0 β = k.choose β.card * Nat.multinomial β.toFinset β.count *
      signatureFactorialWeight β := by
  induction β using Multiset.induction_on generalizing k with
  | empty => simp [signatureFactorialWeight]
  | @cons a β ih =>
      have ha0 : a ≠ 0 := by
        intro h
        subst a
        exact hβ (Multiset.mem_cons_self 0 β)
      have hβ' : 0 ∉ β := fun h ↦ hβ (Multiset.mem_cons_of_mem h)
      cases k with
      | zero =>
          rw [facMomentNat_zero]
          · simp
          · simp
          · exact hβ
      | succ k =>
          rw [facMomentNat_comm]
          apply Nat.eq_of_mul_eq_mul_left (Multiset.count_pos.mpr (Multiset.mem_cons_self a β))
          rw [facMomentNat_marked hβ (by simp) (Multiset.mem_cons_self a β)]
          simp only [Multiset.toFinset_zero, insert_empty_eq, Finset.sum_singleton, add_zero,
            Multiset.erase_zero]
          rw [Multiset.erase_cons_head, facMomentNat_comm k β 0, ih k hβ']
          have hperm : Nat.multinomial (a ::ₘ β).toFinset (a ::ₘ β).count =
              (a ::ₘ β).countPerms := by
            rw [Multiset.countPerms, Finsupp.multinomial_eq, Multiset.toFinsupp_support]
            rfl
          have hpermβ : Nat.multinomial β.toFinset β.count = β.countPerms := by
            rw [Multiset.countPerms, Finsupp.multinomial_eq, Multiset.toFinsupp_support]
            rfl
          rw [hperm, hpermβ,
            signatureFactorialWeight_erase (a ::ₘ β) (Multiset.mem_cons_self a β),
            Multiset.erase_cons_head, Multiset.card_cons]
          have hcountPerm :=
            count_mul_countPerms_erase (a ::ₘ β) (Multiset.mem_cons_self a β)
          rw [Multiset.erase_cons_head, Multiset.card_cons] at hcountPerm
          have hchoose := Nat.add_one_mul_choose_eq k β.card
          calc
            (k + 1) * (a ! * (k.choose β.card * β.countPerms *
                signatureFactorialWeight β)) =
              ((k + 1) * k.choose β.card) *
                (a ! * β.countPerms * signatureFactorialWeight β) := by ring_nf
            _ = ((k + 1).choose (β.card + 1) * (β.card + 1)) *
                (a ! * β.countPerms * signatureFactorialWeight β) := by rw [hchoose]
            _ = (k + 1).choose (β.card + 1) * ((β.card + 1) * β.countPerms) *
                (a ! * signatureFactorialWeight β) := by ring_nf
            _ = (k + 1).choose (β.card + 1) *
                ((a ::ₘ β).count a * (a ::ₘ β).countPerms) *
                  (a ! * signatureFactorialWeight β) := by rw [← hcountPerm]
            _ = (a ::ₘ β).count a *
                ((k + 1).choose (β.card + 1) * (a ::ₘ β).countPerms *
                  (a ! * signatureFactorialWeight β)) := by ring_nf

private theorem overlapFactorialWeight_unmatched (x slots : ℕ) (m : Multiset ℕ)
    (hm : m.card ≤ slots) :
    x ! * overlapFactorialWeight x slots m = overlapFactorialWeight x (slots + 1) m := by
  rw [overlapFactorialWeight_eq, overlapFactorialWeight_eq]
  rw [show slots + 1 - m.card = slots - m.card + 1 by omega, pow_succ']
  ac_rfl

private theorem overlapFactorialWeight_matched (x slots : ℕ) (m : Multiset ℕ)
    {a : ℕ} (ha : a ∈ m) (hm : m.card ≤ slots + 1) :
    (x + a)! * overlapFactorialWeight x slots (m.erase a) =
      overlapFactorialWeight x (slots + 1) m := by
  rw [overlapFactorialWeight_eq, overlapFactorialWeight_eq,
    Multiset.card_erase_of_mem ha, Nat.pred_eq_sub_one]
  have hcard : 0 < m.card := Multiset.card_pos.mpr fun h ↦ by subst m; simp at ha
  rw [show slots - (m.card - 1) = slots + 1 - m.card by omega]
  have hprod : (m.map fun y ↦ (x + y)!).prod =
      (x + a)! * ((m.erase a).map fun y ↦ (x + y)!).prod := by
    conv_lhs => rw [← Multiset.cons_erase ha, Multiset.map_cons, Multiset.prod_cons]
  rw [hprod]
  ac_rfl

private def overlapSum (x slots : ℕ) (m : Multiset ℕ) (f : Multiset ℕ → ℕ) : ℕ :=
  ∑ d ∈ Finset.Iic m, if d.card ≤ slots then
    placements slots d * overlapFactorialWeight x slots d * f (m - d) else 0

private theorem overlapSum_unmatched (x slots : ℕ) (m : Multiset ℕ)
    (f : Multiset ℕ → ℕ) :
    x ! * overlapSum x slots m f =
      ∑ d ∈ Finset.Iic m, if d.card ≤ slots then
        placements slots d * overlapFactorialWeight x (slots + 1) d * f (m - d) else 0 := by
  rw [overlapSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  split_ifs with hcard
  · rw [← overlapFactorialWeight_unmatched x slots d hcard]
    ring_nf
  · simp

private theorem overlapSum_matched (x slots : ℕ) (m : Multiset ℕ)
    (f : Multiset ℕ → ℕ) :
    (∑ a ∈ m.toFinset, (x + a)! * overlapSum x slots (m.erase a) f) =
      ∑ d ∈ Finset.Iic m, if d.card ≤ slots + 1 then
        (∑ a ∈ d.toFinset, placements slots (d.erase a)) *
          overlapFactorialWeight x (slots + 1) d * f (m - d) else 0 := by
  simp only [overlapSum]
  simp_rw [Finset.mul_sum]
  rw [← sum_Iic_erase_swap m (fun a e ↦
    (x + a)! * if e.card ≤ slots then
      placements slots e * overlapFactorialWeight x slots e * f (m.erase a - e) else 0)]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [Finset.mem_Iic] at hd
  by_cases hcard : d.card ≤ slots + 1
  · rw [if_pos hcard]
    conv_rhs => rw [Nat.mul_assoc, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    have had : a ∈ d := Multiset.mem_toFinset.mp ha
    have hcardErase : (d.erase a).card ≤ slots := by
      have hpos : 0 < d.card := Multiset.card_pos.mpr fun h ↦ by subst d; simp at had
      rw [Multiset.card_erase_of_mem had, Nat.pred_eq_sub_one]
      omega
    rw [if_pos hcardErase, ← Multiset.sub_cons, Multiset.cons_erase had]
    have hw := overlapFactorialWeight_matched x slots d had hcard
    calc
      (x + a)! * (placements slots (d.erase a) *
          overlapFactorialWeight x slots (d.erase a) * f (m - d)) =
        placements slots (d.erase a) *
          ((x + a)! * overlapFactorialWeight x slots (d.erase a)) * f (m - d) := by ring_nf
      _ = placements slots (d.erase a) *
          (overlapFactorialWeight x (slots + 1) d * f (m - d)) := by rw [hw]; ring_nf
  · rw [if_neg hcard]
    refine Finset.sum_eq_zero fun a ha ↦ ?_
    have had : a ∈ d := Multiset.mem_toFinset.mp ha
    have hcardErase : ¬(d.erase a).card ≤ slots := by
      have hpos : 0 < d.card := Multiset.card_pos.mpr fun h ↦ by subst d; simp at had
      rw [Multiset.card_erase_of_mem had, Nat.pred_eq_sub_one]
      omega
    rw [if_neg hcardErase, mul_zero]

private theorem overlapSum_eq_sum (x slots : ℕ) (m : Multiset ℕ)
    (f : Multiset ℕ → ℕ) :
    overlapSum x slots m f = ∑ d ∈ Finset.Iic m,
      placements slots d * overlapFactorialWeight x slots d * f (m - d) := by
  rw [overlapSum]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  by_cases hcard : d.card ≤ slots
  · rw [if_pos hcard]
  · simp [hcard, placements_eq_zero (Nat.lt_of_not_ge hcard)]

private theorem overlapSum_unmatched_all (x slots : ℕ) (m : Multiset ℕ)
    (f : Multiset ℕ → ℕ) :
    x ! * overlapSum x slots m f = ∑ d ∈ Finset.Iic m,
      placements slots d * overlapFactorialWeight x (slots + 1) d * f (m - d) := by
  rw [overlapSum_unmatched]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  by_cases hcard : d.card ≤ slots
  · rw [if_pos hcard]
  · simp [hcard, placements_eq_zero (Nat.lt_of_not_ge hcard)]

private theorem overlapSum_matched_all (x slots : ℕ) (m : Multiset ℕ)
    (f : Multiset ℕ → ℕ) :
    (∑ a ∈ m.toFinset, (x + a)! * overlapSum x slots (m.erase a) f) =
      ∑ d ∈ Finset.Iic m,
        (∑ a ∈ d.toFinset, placements slots (d.erase a)) *
          overlapFactorialWeight x (slots + 1) d * f (m - d) := by
  rw [overlapSum_matched]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  by_cases hcard : d.card ≤ slots + 1
  · rw [if_pos hcard]
  · rw [if_neg hcard]
    have hsum : (∑ a ∈ d.toFinset, placements slots (d.erase a)) = 0 := by
      refine Finset.sum_eq_zero fun a ha ↦ ?_
      have had : a ∈ d := Multiset.mem_toFinset.mp ha
      apply placements_eq_zero
      rw [Multiset.card_erase_of_mem had, Nat.pred_eq_sub_one]
      have hpos : 0 < d.card := Multiset.card_pos.mpr fun h ↦ by subst d; simp at had
      omega
    simp [hsum]

private theorem overlapSum_pascal (x slots : ℕ) (m : Multiset ℕ)
    (f : Multiset ℕ → ℕ) :
    overlapSum x (slots + 1) m f = x ! * overlapSum x slots m f +
      ∑ a ∈ m.toFinset, (x + a)! * overlapSum x slots (m.erase a) f := by
  rw [overlapSum_eq_sum, overlapSum_unmatched_all, overlapSum_matched_all,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [placements_pascal]
  ring_nf

private theorem overlapSum_zero (x : ℕ) (m : Multiset ℕ) (f : Multiset ℕ → ℕ) :
    overlapSum x 0 m f = f m := by
  rw [overlapSum, Finset.sum_eq_single 0]
  · simp [placements, overlapFactorialWeight]
  · intro d hd hd0
    rw [Finset.mem_Iic] at hd
    have hcard : ¬d.card ≤ 0 := by
      intro h
      have : d = 0 := Multiset.card_eq_zero.mp (Nat.eq_zero_of_le_zero h)
      exact hd0 this
    rw [if_neg hcard]
  · simp

private theorem facMomentNat_block (k x slots : ℕ) (α β : Multiset ℕ)
    (hx : x ≠ 0) (hxα : x ∉ α) (hα : 0 ∉ α) (hβ : 0 ∉ β) :
    facMomentNat k (Multiset.replicate slots x + α) β =
      k.choose slots * overlapSum x slots β
        (fun δ ↦ facMomentNat (k - slots) α δ) := by
  induction slots generalizing k β with
  | zero => simp [overlapSum_zero]
  | succ slots ih =>
      cases k with
      | zero =>
          rw [facMomentNat_zero]
          · simp
          · intro h
            rw [Multiset.mem_add] at h
            rcases h with h | h
            · exact hx (Multiset.eq_of_mem_replicate h).symm
            · exact hα h
          · exact hβ
      | succ k =>
          have hsig : 0 ∉ Multiset.replicate (slots + 1) x + α := by
            intro h
            rw [Multiset.mem_add] at h
            rcases h with h | h
            · exact hx (Multiset.eq_of_mem_replicate h).symm
            · exact hα h
          have hxmem : x ∈ Multiset.replicate (slots + 1) x + α := by simp
          have hcount : (Multiset.replicate (slots + 1) x + α).count x = slots + 1 := by
            simp [hxα]
          have herase : (Multiset.replicate (slots + 1) x + α).erase x =
              Multiset.replicate slots x + α := by
            rw [Multiset.replicate_succ, Multiset.erase_add_left_pos]
            · rw [Multiset.erase_cons_head]
            · simp
          apply Nat.eq_of_mul_eq_mul_left (Nat.succ_pos slots)
          have hleft : (slots + 1) *
              facMomentNat (k + 1) (Multiset.replicate (slots + 1) x + α) β =
                (k + 1) * ∑ s ∈ insert 0 β.toFinset,
                  (x + s)! * facMomentNat k
                    (Multiset.replicate slots x + α) (β.erase s) :=
            calc
              (slots + 1) * facMomentNat (k + 1)
                  (Multiset.replicate (slots + 1) x + α) β =
                (Multiset.replicate (slots + 1) x + α).count x *
                  facMomentNat (k + 1) (Multiset.replicate (slots + 1) x + α) β := by
                    rw [hcount]
              _ = (k + 1) * ∑ s ∈ insert 0 β.toFinset,
                  (x + s)! * facMomentNat k
                    ((Multiset.replicate (slots + 1) x + α).erase x) (β.erase s) :=
                facMomentNat_marked (k := k) (α := Multiset.replicate (slots + 1) x + α)
                  (β := β) (x := x) hsig hβ hxmem
              _ = _ := by rw [herase]
          rw [hleft]
          · have hi (s : ℕ) : facMomentNat k (Multiset.replicate slots x + α) (β.erase s) =
                k.choose slots * overlapSum x slots (β.erase s)
                  (fun δ ↦ facMomentNat (k - slots) α δ) :=
              ih k (β.erase s) fun h ↦ hβ (Multiset.mem_of_mem_erase h)
            simp_rw [hi]
            rw [overlapSum_pascal, Finset.sum_insert]
            · simp only [Multiset.erase_of_notMem hβ]
              have hdim : k + 1 - (slots + 1) = k - slots := Nat.add_sub_add_right k 1 slots
              simp only [hdim]
              have hfactor :
                  (x + 0)! * (k.choose slots * overlapSum x slots β
                      (fun δ ↦ facMomentNat (k - slots) α δ)) +
                    ∑ a ∈ β.toFinset, (x + a)! *
                      (k.choose slots * overlapSum x slots (β.erase a)
                        (fun δ ↦ facMomentNat (k - slots) α δ)) =
                    k.choose slots *
                      (x ! * overlapSum x slots β
                          (fun δ ↦ facMomentNat (k - slots) α δ) +
                        ∑ a ∈ β.toFinset, (x + a)! * overlapSum x slots (β.erase a)
                          (fun δ ↦ facMomentNat (k - slots) α δ)) := by
                rw [Nat.mul_add, Finset.mul_sum]
                apply congrArg₂ (fun a b : ℕ ↦ a + b)
                · ring_nf
                · apply Finset.sum_congr rfl
                  intro a _
                  ring_nf
              rw [hfactor]
              let Q := x ! * overlapSum x slots β
                    (fun δ ↦ facMomentNat (k - slots) α δ) +
                  ∑ a ∈ β.toFinset, (x + a)! * overlapSum x slots (β.erase a)
                    (fun δ ↦ facMomentNat (k - slots) α δ)
              change (k + 1) * (k.choose slots * Q) =
                (slots + 1) * ((k + 1).choose (slots + 1) * Q)
              calc
                (k + 1) * (k.choose slots * Q) =
                    ((k + 1) * k.choose slots) * Q := by rw [Nat.mul_assoc]
                _ = ((k + 1).choose (slots + 1) * (slots + 1)) * Q := by
                  rw [Nat.add_one_mul_choose_eq]
                _ = (slots + 1) * ((k + 1).choose (slots + 1) * Q) := by ac_rfl
            · exact fun h ↦ hβ (Multiset.mem_toFinset.mp h)

private def groupedSignature : List (ℕ × ℕ) → Multiset ℕ
  | [] => 0
  | (x, m) :: groups => Multiset.replicate m x + groupedSignature groups

private theorem countsSignature_groupedSignature (groups : List (ℕ × ℕ)) :
    countsSignature (groups.map Prod.fst) (groups.map Prod.snd) = groupedSignature groups := by
  induction groups with
  | nil => rfl
  | cons group groups ih =>
      obtain ⟨x, slots⟩ := group
      simp only [List.map_cons, countsSignature, groupedSignature, ih]

private theorem mem_keys_of_mem_groupedSignature {groups : List (ℕ × ℕ)} {x : ℕ}
    (hx : x ∈ groupedSignature groups) : x ∈ groups.map Prod.fst := by
  induction groups with
  | nil => simp [groupedSignature] at hx
  | cons group groups ih =>
      obtain ⟨y, m⟩ := group
      rw [groupedSignature, Multiset.mem_add] at hx
      simp only [List.map_cons, List.mem_cons]
      rcases hx with hx | hx
      · exact Or.inl (Multiset.eq_of_mem_replicate hx)
      · exact Or.inr (ih hx)

private theorem zero_not_mem_groupedSignature {groups : List (ℕ × ℕ)}
    (hzero : ∀ group ∈ groups, group.1 ≠ 0) : 0 ∉ groupedSignature groups := by
  intro h
  have hkey := mem_keys_of_mem_groupedSignature h
  simp only [List.mem_map] at hkey
  obtain ⟨group, hgroup, hgroup0⟩ := hkey
  exact hzero group hgroup hgroup0

private theorem facMomentOverlapCore_eq (k : ℕ) (groups : List (ℕ × ℕ))
    (β : Multiset ℕ) (hkeys : (groups.map Prod.fst).Nodup)
    (hzero : ∀ group ∈ groups, group.1 ≠ 0) (hβ : 0 ∉ β) :
    facMomentOverlapCore k groups β = facMomentNat k (groupedSignature groups) β := by
  induction groups generalizing k β with
  | nil =>
      rw [facMomentOverlapCore, groupedSignature]
      exact (facMomentNat_empty_left k β hβ).symm
  | cons group groups ih =>
      obtain ⟨x, m⟩ := group
      have hkeys' : (groups.map Prod.fst).Nodup := (List.nodup_cons.mp hkeys).2
      have hxkeys : x ∉ groups.map Prod.fst := (List.nodup_cons.mp hkeys).1
      have hzero' : ∀ group ∈ groups, group.1 ≠ 0 := by
        intro group hgroup
        exact hzero group (List.mem_cons_of_mem _ hgroup)
      have hx : x ≠ 0 := hzero (x, m) (by simp)
      have hxgroups : x ∉ groupedSignature groups := fun h ↦
        hxkeys (mem_keys_of_mem_groupedSignature h)
      have hgroupsZero : 0 ∉ groupedSignature groups :=
        zero_not_mem_groupedSignature hzero'
      rw [facMomentOverlapCore, groupedSignature]
      change k.choose m * overlapSum x m β
          (fun δ ↦ facMomentOverlapCore (k - m) groups δ) = _
      rw [facMomentNat_block k x m (groupedSignature groups) β hx hxgroups hgroupsZero hβ]
      apply congrArg (k.choose m * ·)
      rw [overlapSum, overlapSum]
      apply Finset.sum_congr rfl
      intro γ hγ
      split_ifs
      · apply congrArg
        apply ih (k - m) (β - γ) hkeys' hzero'
        intro h
        exact hβ (Multiset.mem_of_le (Multiset.sub_le_self β γ) h)
      · rfl

private theorem count_groupedSignature_map (α xs : List ℕ) (x : ℕ) :
    (groupedSignature (xs.map fun y ↦ (y, α.count y))).count x =
      (xs.map fun y ↦ if x = y then α.count y else 0).sum := by
  induction xs with
  | nil => simp [groupedSignature]
  | cons y ys ih =>
      change (Multiset.replicate (α.count y) y +
          groupedSignature (ys.map fun z ↦ (z, α.count z))).count x = _
      rw [Multiset.count_add, Multiset.count_replicate, ih]
      by_cases hxy : x = y
      · subst y
        simp
      · simp [hxy, Ne.symm hxy]

private theorem nodup_eraseDups : ∀ α : List ℕ, α.eraseDups.Nodup
  | [] => by simp
  | x :: xs => by
      rw [List.eraseDups_cons, List.nodup_cons]
      exact ⟨by simp, nodup_eraseDups (xs.filter fun y ↦ !y == x)⟩
termination_by α => α.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

private theorem indicator_sum_eq (α xs : List ℕ) (x : ℕ) (hxs : xs.Nodup) :
    (xs.map fun y ↦ if x = y then α.count y else 0).sum =
      if x ∈ xs then α.count x else 0 := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
      rw [List.nodup_cons] at hxs
      by_cases hxy : x = y
      · subst y
        rw [List.map_cons, List.sum_cons, if_pos rfl, ih hxs.2, if_neg hxs.1]
        simp
      · rw [List.map_cons, List.sum_cons, if_neg hxy, ih hxs.2]
        simp [hxy]

private theorem groupedSignature_signatureGroups (α : List ℕ) :
    groupedSignature (signatureGroups α) = (α : Multiset ℕ) := by
  ext x
  rw [signatureGroups, count_groupedSignature_map]
  rw [indicator_sum_eq α α.eraseDups x (nodup_eraseDups α)]
  simp only [List.mem_eraseDups]
  by_cases hx : x ∈ α
  · rw [if_pos hx]
    exact (Multiset.coe_count x α).symm
  · rw [if_neg hx]
    exact (Multiset.count_eq_zero.mpr (by simpa using hx)).symm

/-- Insert one multiplicity class into a list ordered by increasing multiplicity. -/
def insertSignatureGroup (group : ℕ × ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [group]
  | head :: groups =>
      if group.2 ≤ head.2 then group :: head :: groups
      else head :: insertSignatureGroup group groups

/-- Order multiplicity classes from the smallest branching factor to the largest. -/
def orderSignatureGroups : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | group :: groups => insertSignatureGroup group (orderSignatureGroups groups)

private theorem insertSignatureGroup_perm (group : ℕ × ℕ)
    (groups : List (ℕ × ℕ)) :
    List.Perm (insertSignatureGroup group groups) (group :: groups) := by
  induction groups with
  | nil => rfl
  | cons head groups ih =>
      rw [insertSignatureGroup]
      split_ifs with h
      · rfl
      · exact (ih.cons head).trans (List.Perm.swap head group groups).symm

private theorem orderSignatureGroups_perm (groups : List (ℕ × ℕ)) :
    List.Perm (orderSignatureGroups groups) groups := by
  induction groups with
  | nil => rfl
  | cons group groups ih =>
      rw [orderSignatureGroups]
      exact (insertSignatureGroup_perm group _).trans (ih.cons group)

private theorem groupedSignature_eq_of_perm {left right : List (ℕ × ℕ)}
    (h : List.Perm left right) : groupedSignature left = groupedSignature right := by
  induction h with
  | nil => rfl
  | cons group h ih =>
      obtain ⟨x, slots⟩ := group
      simp only [groupedSignature, ih]
  | swap first second groups =>
      obtain ⟨x, slots⟩ := first
      obtain ⟨y, places⟩ := second
      simp only [groupedSignature]
      ac_rfl
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem groupedSignature_orderSignatureGroups (groups : List (ℕ × ℕ)) :
    groupedSignature (orderSignatureGroups groups) = groupedSignature groups :=
  groupedSignature_eq_of_perm (orderSignatureGroups_perm groups)

private theorem orderSignatureGroups_keys_nodup (groups : List (ℕ × ℕ))
    (hgroups : (groups.map Prod.fst).Nodup) :
    ((orderSignatureGroups groups).map Prod.fst).Nodup :=
  ((orderSignatureGroups_perm groups).map Prod.fst).nodup_iff.mpr hgroups

private theorem orderSignatureGroups_zeroFree {groups : List (ℕ × ℕ)}
    (hgroups : ∀ group ∈ groups, group.1 ≠ 0) :
    ∀ group ∈ orderSignatureGroups groups, group.1 ≠ 0 := by
  intro group hgroup
  exact hgroups group ((orderSignatureGroups_perm groups).mem_iff.mp hgroup)

private theorem countsSignature_signatureGroups (α : List ℕ) :
    countsSignature ((signatureGroups α).map Prod.fst)
      ((signatureGroups α).map Prod.snd) = (α : Multiset ℕ) := by
  rw [countsSignature_groupedSignature, groupedSignature_signatureGroups]

private theorem signatureGroups_keys_nodup (α : List ℕ) :
    ((signatureGroups α).map Prod.fst).Nodup := by
  rw [signatureGroups, List.map_map]
  simpa [Function.comp_def] using nodup_eraseDups α

private theorem facMomentCountCore_signatureGroups_eq (k : ℕ)
    (groups : List (ℕ × ℕ)) (α : List ℕ) :
    facMomentCountCore k groups ((signatureGroups α).map Prod.fst)
      ((signatureGroups α).map Prod.snd) = facMomentOverlapCore k groups α := by
  rw [facMomentCountCore_eq_overlapCore k groups
    ((signatureGroups α).map Prod.fst) ((signatureGroups α).map Prod.snd)
    (signatureGroups_keys_nodup α) (by simp), countsSignature_signatureGroups]

private theorem signatureGroups_zeroFree {α : List ℕ} (hα : 0 ∉ α) :
    ∀ group ∈ signatureGroups α, group.1 ≠ 0 := by
  intro group hgroup
  rw [signatureGroups] at hgroup
  simp only [List.mem_map] at hgroup
  obtain ⟨x, hx, rfl⟩ := hgroup
  exact fun hx0 ↦ hα (hx0 ▸ List.mem_eraseDups.mp hx)

/-- A cheap estimate of the number of overlap profiles visited in one orientation. -/
def overlapOrientationCost (groups : List (ℕ × ℕ)) (other : List (ℕ × ℕ)) : ℕ :=
  groups.length * (other.map fun group ↦ group.2 + 1).prod

/-- Direct overlap-profile evaluator, oriented using the multiplicity profile of both inputs. -/
def facMomentDirect (k : ℕ) (α β : List ℕ) : ℕ :=
  let αGroups := signatureGroups α
  let βGroups := signatureGroups β
  if overlapOrientationCost αGroups βGroups ≤ overlapOrientationCost βGroups αGroups then
    facMomentCountCore k (orderSignatureGroups αGroups)
      (βGroups.map Prod.fst) (βGroups.map Prod.snd)
  else facMomentCountCore k (orderSignatureGroups βGroups)
    (αGroups.map Prod.fst) (αGroups.map Prod.snd)

/-- Evaluate two dimensions together, using the cheaper multiplicity-profile orientation. -/
def facMomentDirectPair (k l : ℕ) (α β : List ℕ) : ℕ × ℕ :=
  let αGroups := signatureGroups α
  let βGroups := signatureGroups β
  if overlapOrientationCost αGroups βGroups ≤ overlapOrientationCost βGroups αGroups then
    facMomentCountPairCore k l (orderSignatureGroups αGroups)
      (βGroups.map Prod.fst) (βGroups.map Prod.snd)
  else facMomentCountPairCore k l (orderSignatureGroups βGroups)
    (αGroups.map Prod.fst) (αGroups.map Prod.snd)

/-- The overlap-profile evaluator agrees with the factorial moment defined by summing over
embeddings. -/
theorem facMomentDirect_eq (k : ℕ) (α β : List ℕ) (hα : 0 ∉ α) (hβ : 0 ∉ β) :
    facMomentDirect k α β = facMomentNat k α β := by
  rw [facMomentDirect]
  split_ifs
  · rw [facMomentCountCore_signatureGroups_eq,
      facMomentOverlapCore_eq k (orderSignatureGroups (signatureGroups α))
        (β : Multiset ℕ)
        (orderSignatureGroups_keys_nodup _ (signatureGroups_keys_nodup α))
        (orderSignatureGroups_zeroFree (signatureGroups_zeroFree hα))
        (by simpa using hβ),
      groupedSignature_orderSignatureGroups, groupedSignature_signatureGroups]
  · rw [facMomentCountCore_signatureGroups_eq,
      facMomentOverlapCore_eq k (orderSignatureGroups (signatureGroups β))
        (α : Multiset ℕ)
        (orderSignatureGroups_keys_nodup _ (signatureGroups_keys_nodup β))
        (orderSignatureGroups_zeroFree (signatureGroups_zeroFree hβ))
        (by simpa using hα),
      groupedSignature_orderSignatureGroups, groupedSignature_signatureGroups, facMomentNat_comm]

/-- The shared, adaptively oriented traversal computes both requested factorial moments. -/
theorem facMomentDirectPair_eq (k l : ℕ) (α β : List ℕ)
    (hα : 0 ∉ α) (hβ : 0 ∉ β) :
    facMomentDirectPair k l α β = (facMomentNat k α β, facMomentNat l α β) := by
  rw [facMomentDirectPair]
  split_ifs
  · apply Prod.ext
    · rw [facMomentCountPairCore_fst, facMomentCountCore_signatureGroups_eq,
        facMomentOverlapCore_eq k (orderSignatureGroups (signatureGroups α))
          (β : Multiset ℕ)
          (orderSignatureGroups_keys_nodup _ (signatureGroups_keys_nodup α))
          (orderSignatureGroups_zeroFree (signatureGroups_zeroFree hα))
          (by simpa using hβ),
        groupedSignature_orderSignatureGroups, groupedSignature_signatureGroups]
    · rw [facMomentCountPairCore_snd, facMomentCountCore_signatureGroups_eq,
        facMomentOverlapCore_eq l (orderSignatureGroups (signatureGroups α))
          (β : Multiset ℕ)
          (orderSignatureGroups_keys_nodup _ (signatureGroups_keys_nodup α))
          (orderSignatureGroups_zeroFree (signatureGroups_zeroFree hα))
          (by simpa using hβ),
        groupedSignature_orderSignatureGroups, groupedSignature_signatureGroups]
  · apply Prod.ext
    · rw [facMomentCountPairCore_fst, facMomentCountCore_signatureGroups_eq,
        facMomentOverlapCore_eq k (orderSignatureGroups (signatureGroups β))
          (α : Multiset ℕ)
          (orderSignatureGroups_keys_nodup _ (signatureGroups_keys_nodup β))
          (orderSignatureGroups_zeroFree (signatureGroups_zeroFree hβ))
          (by simpa using hα),
        groupedSignature_orderSignatureGroups, groupedSignature_signatureGroups, facMomentNat_comm]
    · rw [facMomentCountPairCore_snd, facMomentCountCore_signatureGroups_eq,
        facMomentOverlapCore_eq l (orderSignatureGroups (signatureGroups β))
          (α : Multiset ℕ)
          (orderSignatureGroups_keys_nodup _ (signatureGroups_keys_nodup β))
          (orderSignatureGroups_zeroFree (signatureGroups_zeroFree hβ))
          (by simpa using hα),
        groupedSignature_orderSignatureGroups, groupedSignature_signatureGroups, facMomentNat_comm]

/-- The first projection of the shared traversal is the first direct moment. -/
theorem facMomentDirectPair_fst (k l : ℕ) (α β : List ℕ)
    (hα : 0 ∉ α) (hβ : 0 ∉ β) :
    (facMomentDirectPair k l α β).1 = facMomentDirect k α β := by
  rw [facMomentDirectPair_eq k l α β hα hβ, facMomentDirect_eq k α β hα hβ]

/-- The second projection of the shared traversal is the second direct moment. -/
theorem facMomentDirectPair_snd (k l : ℕ) (α β : List ℕ)
    (hα : 0 ∉ α) (hβ : 0 ∉ β) :
    (facMomentDirectPair k l α β).2 = facMomentDirect l α β := by
  rw [facMomentDirectPair_eq k l α β hα hβ, facMomentDirect_eq l α β hα hβ]

/-- The data of a denominator-cleared certificate backed by externally stored labelled
signatures and factorial moments, without the final witnessing inequality. -/
structure PreEpsCertificateExplicitDagInt
    (K epsilonDenominator degreeBound : ℕ) : Type where
  /-- Number of externally stored exponent signatures. -/
  S : ℕ
  /-- There is at least one stored signature. -/
  S_pos : 0 < S
  /-- Externally stored canonical exponent signatures. -/
  sig : Fin S → List ℕ
  /-- Signatures contain no zero exponents. -/
  zeroFree (i : Fin S) : 0 ∉ sig i
  /-- Every exponent fits in the finite transition alphabet. -/
  exponent_lt (i : Fin S) (x : ℕ) (hx : x ∈ sig i) : x < degreeBound
  /-- Label of a signature after erasing an exponent; zero means no erasure. -/
  erase : Fin S → ℕ → Fin S
  /-- Erasure labels refer to the corresponding stored signatures. -/
  erase_sig (i : Fin S) (x : ℕ) (hx : x ∈ insert 0 (sig i).toFinset) :
    sig (erase i x) = (sig i).erase x
  /-- Radix separating the dimensions `K - 1` and `K` in each stored pair value. -/
  momentRadix : ℕ
  /-- The moment radix is positive. -/
  momentRadix_pos : 0 < momentRadix
  /-- Packed factorial moments for all ordered pairs of signature labels. -/
  pairValue : Fin (S * S) → ℕ
  /-- The epsilon denominator is positive. -/
  epsilon_pos : 0 < epsilonDenominator
  /-- The basis degree bound is positive. -/
  degree_pos : 0 < degreeBound
  /-- Two basis degrees fit within the sieve dimension. -/
  degree_pair_bound : 2 * degreeBound ≤ K
  /-- Number of basis elements. -/
  N : ℕ
  /-- Slack exponents. -/
  a : Fin N → ℕ
  /-- Labels of the exponent signatures. -/
  sigIndex : Fin N → Fin S
  /-- Integral coefficients. -/
  coeff : Fin N → ℤ
  /-- Every basis element has total degree at most `degreeBound`. -/
  degree (i : Fin N) : a i + (sig (sigIndex i)).sum ≤ degreeBound

/-- Row-major label of an ordered signature pair. -/
def signaturePairIndex {S : ℕ} (i j : Fin S) : Fin (S * S) :=
  ⟨i.val * S + j.val,
    calc
      i.val * S + j.val < i.val * S + S := Nat.add_lt_add_left j.isLt _
      _ = (i.val + 1) * S := (Nat.succ_mul i.val S).symm
      _ ≤ S * S := Nat.mul_le_mul_right S (Nat.succ_le_iff.mpr i.isLt)⟩

/-- Transpose a row-major signature-pair index. -/
def signaturePairSwap {S : ℕ} (p : Fin (S * S)) : Fin (S * S) :=
  signaturePairIndex p.modNat p.divNat

/-- Taking the row of a row-major signature-pair index recovers its first index. -/
@[simp]
theorem signaturePairIndex_divNat {S : ℕ} (i j : Fin S) :
    (signaturePairIndex i j).divNat = i := by
  apply Fin.ext
  simp only [Fin.divNat, signaturePairIndex, Fin.val_mk]
  rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ (Fin.size_positive j),
    Nat.div_eq_of_lt j.isLt, zero_add]

/-- Taking the column of a row-major signature-pair index recovers its second index. -/
@[simp]
theorem signaturePairIndex_modNat {S : ℕ} (i j : Fin S) :
    (signaturePairIndex i j).modNat = j := by
  apply Fin.ext
  simp only [Fin.modNat, signaturePairIndex, Fin.val_mk]
  rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.isLt]

/-- Transposing a row-major signature pair exchanges its row with its column. -/
@[simp]
theorem signaturePairSwap_divNat {S : ℕ} (p : Fin (S * S)) :
    (signaturePairSwap p).divNat = p.modNat := by
  rw [signaturePairSwap, signaturePairIndex_divNat]

/-- Transposing a row-major signature pair exchanges its column with its row. -/
@[simp]
theorem signaturePairSwap_modNat {S : ℕ} (p : Fin (S * S)) :
    (signaturePairSwap p).modNat = p.divNat := by
  rw [signaturePairSwap, signaturePairIndex_modNat]

/-- Stored factorial moment in dimension `K`. -/
def PreEpsCertificateExplicitDagInt.momentTop {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (i j : Fin ct.S) : ℕ :=
  ct.pairValue (signaturePairIndex i j) / ct.momentRadix

/-- Stored factorial moment in dimension `K - 1`. -/
def PreEpsCertificateExplicitDagInt.momentPred {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (i j : Fin ct.S) : ℕ :=
  ct.pairValue (signaturePairIndex i j) % ct.momentRadix

/-- The directly computed packed value for an ordered pair of stored signature labels. -/
def PreEpsCertificateExplicitDagInt.directPairValue
    {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (p : Fin (ct.S * ct.S)) : ℕ :=
  let moments := facMomentDirectPair K (K - 1) (ct.sig p.divNat) (ct.sig p.modNat)
  ct.momentRadix * moments.1 + moments.2

/-- Correct packed pair values recover the directly computed dimension-`K` moment. -/
theorem PreEpsCertificateExplicitDagInt.momentTop_eq
    {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (hpack : ∀ p, ct.pairValue p = ct.directPairValue p)
    (hpred : ∀ p : Fin (ct.S * ct.S),
      facMomentDirect (K - 1) (ct.sig p.divNat) (ct.sig p.modNat) < ct.momentRadix)
    (i j : Fin ct.S) :
    ct.momentTop i j = facMomentDirect K (ct.sig i) (ct.sig j) := by
  have hp := hpred (signaturePairIndex i j)
  simp only [signaturePairIndex_divNat, signaturePairIndex_modNat] at hp
  rw [PreEpsCertificateExplicitDagInt.momentTop, hpack,
    PreEpsCertificateExplicitDagInt.directPairValue]
  simp only [signaturePairIndex_divNat, signaturePairIndex_modNat]
  rw [facMomentDirectPair_fst K (K - 1) (ct.sig i) (ct.sig j)
    (ct.zeroFree i) (ct.zeroFree j),
    facMomentDirectPair_snd K (K - 1) (ct.sig i) (ct.sig j)
      (ct.zeroFree i) (ct.zeroFree j)]
  rw [Nat.mul_add_div ct.momentRadix_pos, Nat.div_eq_of_lt hp, add_zero]

/-- Correct packed pair values recover the directly computed dimension-`K - 1` moment. -/
theorem PreEpsCertificateExplicitDagInt.momentPred_eq
    {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (hpack : ∀ p, ct.pairValue p = ct.directPairValue p)
    (hpred : ∀ p : Fin (ct.S * ct.S),
      facMomentDirect (K - 1) (ct.sig p.divNat) (ct.sig p.modNat) < ct.momentRadix)
    (i j : Fin ct.S) :
    ct.momentPred i j = facMomentDirect (K - 1) (ct.sig i) (ct.sig j) := by
  have hp := hpred (signaturePairIndex i j)
  simp only [signaturePairIndex_divNat, signaturePairIndex_modNat] at hp
  rw [PreEpsCertificateExplicitDagInt.momentPred, hpack,
    PreEpsCertificateExplicitDagInt.directPairValue]
  simp only [signaturePairIndex_divNat, signaturePairIndex_modNat]
  rw [facMomentDirectPair_fst K (K - 1) (ct.sig i) (ct.sig j)
    (ct.zeroFree i) (ct.zeroFree j),
    facMomentDirectPair_snd K (K - 1) (ct.sig i) (ct.sig j)
      (ct.zeroFree i) (ct.zeroFree j)]
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hp]

/-- Enlarged-simplex pairing evaluated through externally stored labelled moments. -/
def PreEpsCertificateExplicitDagInt.iPair {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (a₁ : ℕ) (i₁ : Fin ct.S) (a₂ : ℕ) (i₂ : Fin ct.S) : ℕ :=
  let d := (a₁ + a₂) + ((ct.sig i₁).sum + (ct.sig i₂).sum)
  (epsilonDenominator + 1) ^ (K + d) * epsilonDenominator ^ (K + 1 - d) *
    (a₁ + a₂)! * ct.momentTop i₁ i₂ *
    (2 * K + 1).descFactorial (K + 1 - d) * (degreeBound + 1)! ^ 2

/-- Marginal pairing evaluated through externally stored labelled moments. -/
def PreEpsCertificateExplicitDagInt.jPair {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (a₁ : ℕ) (i₁ : Fin ct.S) (a₂ : ℕ) (i₂ : Fin ct.S) : ℕ :=
  ∑ r₁ ∈ insert 0 (ct.sig i₁).toFinset, ∑ r₂ ∈ insert 0 (ct.sig i₂).toFinset,
    marginalFactorInt degreeBound a₁ r₁ * marginalFactorInt degreeBound a₂ r₂ *
      radialExplicitInt K epsilonDenominator
        (K - 1 + (((ct.sig i₁).sum - r₁) + ((ct.sig i₂).sum - r₂)))
        ((a₁ + r₁ + 1) + (a₂ + r₂ + 1)) *
      ct.momentPred (ct.erase i₁ r₁) (ct.erase i₂ r₂)

/-- The non-moment scalar in an enlarged-simplex pairing, indexed only by its total degree and
the sum of its two distinguished exponents. -/
def iPairScalarValue (K epsilonDenominator degreeBound d aSum : ℕ) : ℕ :=
  (epsilonDenominator + 1) ^ (K + d) * epsilonDenominator ^ (K + 1 - d) *
    aSum ! * (2 * K + 1).descFactorial (K + 1 - d) *
      (degreeBound + 1)! ^ 2

private def radialFactorKernel (N x q e : ℕ) : ℕ :=
  ∑ m ∈ range (e + 1), e.choose m * 2 ^ (e - m) * x ^ m * m ! *
    N.descFactorial (N - (m + q))

private theorem descFactorial_diagonal (N m q : ℕ) (h : m + q < N) :
    (m + q + 1) * N.descFactorial (N - (m + q + 1)) =
      N.descFactorial (N - (m + q)) := by
  rw [show N - (m + q) = N - (m + q + 1) + 1 by omega, Nat.descFactorial_succ]
  rw [show N - (N - (m + q + 1)) = m + q + 1 by omega]

private theorem radialFactorKernel_recurrence (N x q e : ℕ) (h : q + e < N) :
    radialFactorKernel N x q (e + 1) + x * q * radialFactorKernel N x (q + 1) e =
      (x + 2) * radialFactorKernel N x q e := by
  simp only [radialFactorKernel]
  rw [sum_range_succ']
  simp_rw [Nat.choose_succ_succ]
  simp only [add_mul]
  rw [sum_add_distrib]
  have hfirst :
      (∑ m ∈ range (e + 1), e.choose m * 2 ^ (e + 1 - (m + 1)) * x ^ (m + 1) *
        (m + 1)! * N.descFactorial (N - (m + 1 + q))) =
        x * ∑ m ∈ range (e + 1), e.choose m * 2 ^ (e - m) * x ^ m *
          (m + 1)! * N.descFactorial (N - (m + 1 + q)) := by
    rw [mul_sum]
    refine sum_congr rfl fun m hm ↦ ?_
    rw [show e + 1 - (m + 1) = e - m by omega, pow_succ]
    ring
  rw [hfirst]
  have hsecond :
      (∑ m ∈ range (e + 1), e.choose (m + 1) * 2 ^ (e + 1 - (m + 1)) *
          x ^ (m + 1) * (m + 1)! * N.descFactorial (N - (m + 1 + q))) +
        (e + 1).choose 0 * 2 ^ (e + 1 - 0) * x ^ 0 * 0! *
          N.descFactorial (N - (0 + q)) =
        2 * ∑ m ∈ range (e + 1), e.choose m * 2 ^ (e - m) * x ^ m * m ! *
          N.descFactorial (N - (m + q)) :=
    calc
      _ = (∑ m ∈ range e, e.choose (m + 1) * 2 ^ (e + 1 - (m + 1)) *
            x ^ (m + 1) * (m + 1)! * N.descFactorial (N - (m + 1 + q))) +
          (e + 1).choose 0 * 2 ^ (e + 1 - 0) * x ^ 0 * 0! *
            N.descFactorial (N - (0 + q)) := by
        rw [sum_range_succ]
        simp
      _ = 2 * ((∑ m ∈ range e, e.choose (m + 1) * 2 ^ (e - (m + 1)) *
            x ^ (m + 1) * (m + 1)! * N.descFactorial (N - (m + 1 + q))) +
          e.choose 0 * 2 ^ (e - 0) * x ^ 0 * 0! *
            N.descFactorial (N - (0 + q))) := by
        rw [mul_add, mul_sum]
        congr 1
        · apply sum_congr rfl
          intro m hm
          simp only [mem_range] at hm
          rw [show e + 1 - (m + 1) = e - m by omega]
          rw [show e - m = (e - (m + 1)) + 1 by omega, pow_succ]
          ring
        · simp [pow_succ]
          ac_rfl
      _ = _ := by rw [sum_range_succ']
  let A := x * ∑ m ∈ range (e + 1), e.choose m * 2 ^ (e - m) * x ^ m *
    (m + 1)! * N.descFactorial (N - (m + 1 + q))
  let B := ∑ m ∈ range (e + 1), e.choose (m + 1) * 2 ^ (e + 1 - (m + 1)) *
    x ^ (m + 1) * (m + 1)! * N.descFactorial (N - (m + 1 + q))
  let C := (e + 1).choose 0 * 2 ^ (e + 1 - 0) * x ^ 0 * 0! *
    N.descFactorial (N - (0 + q))
  let D := x * q * ∑ m ∈ range (e + 1), e.choose m * 2 ^ (e - m) * x ^ m * m ! *
    N.descFactorial (N - (m + (q + 1)))
  let E := x * ∑ m ∈ range (e + 1), e.choose m * 2 ^ (e - m) * x ^ m * m ! *
    N.descFactorial (N - (m + q))
  let F := 2 * ∑ m ∈ range (e + 1), e.choose m * 2 ^ (e - m) * x ^ m * m ! *
    N.descFactorial (N - (m + q))
  change B + C = F at hsecond
  change A + B + C + D = E + F
  calc
    A + B + C + D = A + (B + C) + D := by omega
    _ = A + F + D := by rw [hsecond]
    _ = E + F := by
      have hAD : A + D = E := by
        dsimp only [A, D, E]
        rw [mul_assoc x q, ← mul_add, mul_sum, ← sum_add_distrib]
        congr 1
        refine sum_congr rfl fun m hm ↦ ?_
        simp only [mem_range] at hm
        rw [Nat.factorial_succ, show m + (q + 1) = m + 1 + q by omega]
        calc
          _ = e.choose m * 2 ^ (e - m) * x ^ m * m ! *
              ((m + q + 1) * N.descFactorial (N - (m + q + 1))) := by ring_nf
          _ = _ := by rw [descFactorial_diagonal N m q (by omega)]
      calc
        A + F + D = (A + D) + F := by ac_rfl
        _ = E + F := by rw [hAD]

private theorem radialExplicitInt_eq_kernel (K epsilonDenominator q e : ℕ) :
    radialExplicitInt K epsilonDenominator q e =
      epsilonDenominator ^ (2 * K + 1 - (q + e)) * (epsilonDenominator - 1) ^ q *
        radialFactorKernel (2 * K + 1) (epsilonDenominator - 1) q e := rfl

theorem radialExplicitInt_recurrence (K epsilonDenominator q e : ℕ)
    (hε : 0 < epsilonDenominator) (h : q + e < 2 * K + 1) :
    epsilonDenominator * radialExplicitInt K epsilonDenominator q (e + 1) +
        epsilonDenominator * q * radialExplicitInt K epsilonDenominator (q + 1) e =
      (epsilonDenominator + 1) * radialExplicitInt K epsilonDenominator q e := by
  rw [radialExplicitInt_eq_kernel, radialExplicitInt_eq_kernel,
    radialExplicitInt_eq_kernel]
  have hexp : 2 * K + 1 - (q + e) = 2 * K + 1 - (q + (e + 1)) + 1 := by omega
  have hexp' : 2 * K + 1 - (q + 1 + e) = 2 * K + 1 - (q + (e + 1)) := by omega
  rw [hexp, hexp', pow_succ]
  have hrec := radialFactorKernel_recurrence
    (2 * K + 1) (epsilonDenominator - 1) q e h
  rw [show epsilonDenominator - 1 + 2 = epsilonDenominator + 1 by omega] at hrec
  have hrec' :
      radialFactorKernel (2 * K + 1) (epsilonDenominator - 1) q (e + 1) +
          (epsilonDenominator - 1) * q *
            radialFactorKernel (2 * K + 1) (epsilonDenominator - 1) (q + 1) e =
        (epsilonDenominator + 1) *
          radialFactorKernel (2 * K + 1) (epsilonDenominator - 1) q e := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hrec
  let c := epsilonDenominator *
    epsilonDenominator ^ (2 * K + 1 - (q + (e + 1))) *
      (epsilonDenominator - 1) ^ q
  calc
    _ = c * (radialFactorKernel (2 * K + 1) (epsilonDenominator - 1) q (e + 1) +
        (epsilonDenominator - 1) * q *
          radialFactorKernel (2 * K + 1) (epsilonDenominator - 1) (q + 1) e) := by
      dsimp only [c]
      ring
    _ = c * ((epsilonDenominator + 1) *
        radialFactorKernel (2 * K + 1) (epsilonDenominator - 1) q e) := by
      rw [hrec']
    _ = _ := by
      dsimp only [c]
      ring

/-- Parameter-generic lookup tables for the three repeated arithmetic factors in the two
quadratic forms.  The concrete certificate may store these functions however it chooses. -/
structure EpsPairFactorTables (K epsilonDenominator degreeBound : ℕ) where
  /-- Enlarged-simplex scalar indexed by total degree and distinguished-exponent sum. -/
  iScalar : ℕ → ℕ → ℕ
  /-- Marginal factor indexed by a distinguished exponent and an erased exponent. -/
  marginal : ℕ → ℕ → ℕ
  /-- Radial factor indexed by its two exponents. -/
  radial : ℕ → ℕ → ℕ

/-- A factor table agrees with the generic arithmetic formulas. -/
def EpsPairFactorTables.Correct {K epsilonDenominator degreeBound : ℕ}
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound) : Prop :=
  (∀ d aSum,
      tables.iScalar d aSum =
        iPairScalarValue K epsilonDenominator degreeBound d aSum) ∧
    (∀ a r, tables.marginal a r = marginalFactorInt degreeBound a r) ∧
    ∀ q e, tables.radial q e = radialExplicitInt K epsilonDenominator q e

/-- The factor tables obtained directly from the formulas are correct for every parameter
choice. -/
def directEpsPairFactorTables (K epsilonDenominator degreeBound : ℕ) :
    EpsPairFactorTables K epsilonDenominator degreeBound where
  iScalar := iPairScalarValue K epsilonDenominator degreeBound
  marginal := marginalFactorInt degreeBound
  radial := radialExplicitInt K epsilonDenominator

/-- Directly evaluated factor tables satisfy their correctness predicate. -/
theorem directEpsPairFactorTables_correct (K epsilonDenominator degreeBound : ℕ) :
    (directEpsPairFactorTables K epsilonDenominator degreeBound).Correct :=
  ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

/-- Finite square caches for all factor arguments that can occur under the certificate degree
bounds.  Every cache dimension is derived from `K` or `degreeBound`. -/
structure EpsPairFactorCache (K epsilonDenominator degreeBound : ℕ) where
  /-- Cached enlarged-simplex scalars on `[0, 2 * degreeBound]²`. -/
  iScalar : Fin ((2 * degreeBound + 1) * (2 * degreeBound + 1)) → ℕ
  /-- Cached marginal factors on `[0, degreeBound]²`. -/
  marginal : Fin ((degreeBound + 1) * (degreeBound + 1)) → ℕ
  /-- Cached radial factors on `[0, 2 * K + 1]²`. -/
  radial : Fin ((2 * K + 2) * (2 * K + 2)) → ℕ

/-- A bounded scalar-cache lookup, returning zero outside its square storage. -/
def EpsPairFactorCache.iScalarGet {K epsilonDenominator degreeBound : ℕ}
    (cache : EpsPairFactorCache K epsilonDenominator degreeBound) (d a : ℕ) : ℕ :=
  if hd : d < 2 * degreeBound + 1 then
    if ha : a < 2 * degreeBound + 1 then
      cache.iScalar (signaturePairIndex ⟨d, hd⟩ ⟨a, ha⟩)
    else 0
  else 0

/-- A bounded marginal-cache lookup, returning zero outside its square storage. -/
def EpsPairFactorCache.marginalGet {K epsilonDenominator degreeBound : ℕ}
    (cache : EpsPairFactorCache K epsilonDenominator degreeBound) (a r : ℕ) : ℕ :=
  if ha : a < degreeBound + 1 then
    if hr : r < degreeBound + 1 then
      cache.marginal (signaturePairIndex ⟨a, ha⟩ ⟨r, hr⟩)
    else 0
  else 0

/-- A bounded radial-cache lookup, returning zero outside its square storage. -/
def EpsPairFactorCache.radialGet {K epsilonDenominator degreeBound : ℕ}
    (cache : EpsPairFactorCache K epsilonDenominator degreeBound) (q e : ℕ) : ℕ :=
  if hq : q < 2 * K + 2 then
    if he : e < 2 * K + 2 then
      cache.radial (signaturePairIndex ⟨q, hq⟩ ⟨e, he⟩)
    else 0
  else 0

/-- Every cache entry in the three regions used by the contractions agrees with its formula. -/
def EpsPairFactorCache.Correct {K epsilonDenominator degreeBound : ℕ}
    (cache : EpsPairFactorCache K epsilonDenominator degreeBound) : Prop :=
  (∀ d a, d < 2 * degreeBound + 1 → a < 2 * degreeBound + 1 → d ≤ K → a ≤ d →
      cache.iScalarGet d a = iPairScalarValue K epsilonDenominator degreeBound d a) ∧
    (∀ a r, a < degreeBound + 1 → r < degreeBound + 1 → a + r ≤ degreeBound →
      cache.marginalGet a r = marginalFactorInt degreeBound a r) ∧
    ∀ q e, q < 2 * K + 2 → e < 2 * K + 2 → K - 1 ≤ q → q + e ≤ 2 * K + 1 →
      cache.radialGet q e = radialExplicitInt K epsilonDenominator q e

/-- The local scalar-cache recurrence represented by one square entry. -/
@[reducible] def EpsPairFactorCache.IScalarRecurrenceAt
    {K epsilonDenominator degreeBound : ℕ}
    (cache : EpsPairFactorCache K epsilonDenominator degreeBound)
    (p : Fin ((2 * degreeBound + 1) * (2 * degreeBound + 1))) : Prop :=
  let d := p.divNat.val
  let a := p.modNat.val
  if d ≤ K ∧ a ≤ d then
    if a = 0 then
      if d = 0 then
        cache.iScalar p = iPairScalarValue K epsilonDenominator degreeBound 0 0
      else
        epsilonDenominator * (K + (d - 1) + 1) * cache.iScalar p =
          (epsilonDenominator + 1) * cache.iScalarGet (d - 1) 0
    else cache.iScalar p = a * cache.iScalarGet d (a - 1)
  else True

/-- The local marginal-cache recurrence represented by one square entry. -/
@[reducible] def EpsPairFactorCache.MarginalRecurrenceAt
    {K epsilonDenominator degreeBound : ℕ}
    (cache : EpsPairFactorCache K epsilonDenominator degreeBound)
    (p : Fin ((degreeBound + 1) * (degreeBound + 1))) : Prop :=
  let a := p.divNat.val
  let r := p.modNat.val
  if a + r ≤ degreeBound then
    if r = 0 then
      if a = 0 then cache.marginal p = marginalFactorInt degreeBound 0 0
      else cache.marginal p * (a - 1 + r + 2) = cache.marginalGet (a - 1) r * a
    else cache.marginal p * (a + (r - 1) + 2) = cache.marginalGet a (r - 1) * r
  else True

/-- The local radial-cache recurrence represented by one square entry. -/
@[reducible] def EpsPairFactorCache.RadialRecurrenceAt
    {K epsilonDenominator degreeBound : ℕ}
    (cache : EpsPairFactorCache K epsilonDenominator degreeBound)
    (p : Fin ((2 * K + 2) * (2 * K + 2))) : Prop :=
  let q := p.divNat.val
  let e := p.modNat.val
  if K - 1 ≤ q ∧ q + e ≤ 2 * K + 1 then
    if e = 0 then
      cache.radial p = radialExplicitInt K epsilonDenominator q 0
    else
      epsilonDenominator * cache.radial p +
          epsilonDenominator * q * cache.radialGet (q + 1) (e - 1) =
        (epsilonDenominator + 1) * cache.radialGet q (e - 1)
  else True

/-- Evaluate a labelled enlarged-simplex pairing through a supplied scalar table. -/
def PreEpsCertificateExplicitDagInt.iPairCached
    {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (scalar : ℕ → ℕ → ℕ)
    (a₁ : ℕ) (i₁ : Fin ct.S) (a₂ : ℕ) (i₂ : Fin ct.S) : ℕ :=
  let d := (a₁ + a₂) + ((ct.sig i₁).sum + (ct.sig i₂).sum)
  scalar d (a₁ + a₂) * ct.momentTop i₁ i₂

/-- A correct supplied scalar table makes the cached enlarged-simplex pairing exact. -/
theorem PreEpsCertificateExplicitDagInt.iPairCached_eq
    {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (scalar : ℕ → ℕ → ℕ)
    (hscalar : ∀ d aSum,
      scalar d aSum = iPairScalarValue K epsilonDenominator degreeBound d aSum)
    (a₁ : ℕ) (i₁ : Fin ct.S) (a₂ : ℕ) (i₂ : Fin ct.S) :
    ct.iPairCached scalar a₁ i₁ a₂ i₂ = ct.iPair a₁ i₁ a₂ i₂ := by
  simp only [PreEpsCertificateExplicitDagInt.iPairCached, hscalar,
    iPairScalarValue, PreEpsCertificateExplicitDagInt.iPair]
  ac_rfl

/-- Evaluate a labelled marginal pairing through supplied marginal and radial tables. -/
def PreEpsCertificateExplicitDagInt.jPairCached
    {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (marginal : ℕ → ℕ → ℕ) (radial : ℕ → ℕ → ℕ)
    (a₁ : ℕ) (i₁ : Fin ct.S) (a₂ : ℕ) (i₂ : Fin ct.S) : ℕ :=
  ∑ r₁ ∈ insert 0 (ct.sig i₁).toFinset, ∑ r₂ ∈ insert 0 (ct.sig i₂).toFinset,
    marginal a₁ r₁ * marginal a₂ r₂ *
      radial (K - 1 + (((ct.sig i₁).sum - r₁) + ((ct.sig i₂).sum - r₂)))
        ((a₁ + r₁ + 1) + (a₂ + r₂ + 1)) *
      ct.momentPred (ct.erase i₁ r₁) (ct.erase i₂ r₂)

/-- Correct supplied factor tables make the cached marginal pairing exact. -/
theorem PreEpsCertificateExplicitDagInt.jPairCached_eq
    {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (marginal : ℕ → ℕ → ℕ) (radial : ℕ → ℕ → ℕ)
    (hmarginal : ∀ a r, marginal a r = marginalFactorInt degreeBound a r)
    (hradial : ∀ q e, radial q e = radialExplicitInt K epsilonDenominator q e)
    (a₁ : ℕ) (i₁ : Fin ct.S) (a₂ : ℕ) (i₂ : Fin ct.S) :
    ct.jPairCached marginal radial a₁ i₁ a₂ i₂ = ct.jPair a₁ i₁ a₂ i₂ := by
  simp only [PreEpsCertificateExplicitDagInt.jPairCached,
    PreEpsCertificateExplicitDagInt.jPair, hmarginal, hradial]

/-- Evaluate an enlarged-simplex pairing using a single generic factor-table bundle. -/
def PreEpsCertificateExplicitDagInt.iPairWithTables
    {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (a₁ : ℕ) (i₁ : Fin ct.S) (a₂ : ℕ) (i₂ : Fin ct.S) : ℕ :=
  ct.iPairCached tables.iScalar a₁ i₁ a₂ i₂

/-- Evaluate a marginal pairing using a single generic factor-table bundle. -/
def PreEpsCertificateExplicitDagInt.jPairWithTables
    {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (a₁ : ℕ) (i₁ : Fin ct.S) (a₂ : ℕ) (i₂ : Fin ct.S) : ℕ :=
  ct.jPairCached tables.marginal tables.radial a₁ i₁ a₂ i₂

/-- Correct factor tables make the bundled enlarged-simplex evaluator exact. -/
theorem PreEpsCertificateExplicitDagInt.iPairWithTables_eq
    {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (htables : tables.Correct)
    (a₁ : ℕ) (i₁ : Fin ct.S) (a₂ : ℕ) (i₂ : Fin ct.S) :
    ct.iPairWithTables tables a₁ i₁ a₂ i₂ = ct.iPair a₁ i₁ a₂ i₂ :=
  ct.iPairCached_eq tables.iScalar htables.1 a₁ i₁ a₂ i₂

/-- Correct factor tables make the bundled marginal evaluator exact. -/
theorem PreEpsCertificateExplicitDagInt.jPairWithTables_eq
    {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (htables : tables.Correct)
    (a₁ : ℕ) (i₁ : Fin ct.S) (a₂ : ℕ) (i₂ : Fin ct.S) :
    ct.jPairWithTables tables a₁ i₁ a₂ i₂ = ct.jPair a₁ i₁ a₂ i₂ :=
  ct.jPairCached_eq tables.marginal tables.radial htables.2.1 htables.2.2
    a₁ i₁ a₂ i₂

/-- The labelled enlarged-simplex pairing agrees with the specification pairing when the packed
moment table has been certified. -/
theorem PreEpsCertificateExplicitDagInt.iPair_eq
    {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (hpack : ∀ p, ct.pairValue p = ct.directPairValue p)
    (hpred : ∀ p : Fin (ct.S * ct.S),
      facMomentDirect (K - 1) (ct.sig p.divNat) (ct.sig p.modNat) < ct.momentRadix)
    (a₁ : ℕ) (i₁ : Fin ct.S) (a₂ : ℕ) (i₂ : Fin ct.S) :
    ct.iPair a₁ i₁ a₂ i₂ = IEpsExplicitNat K epsilonDenominator degreeBound
      a₁ (ct.sig i₁ : Multiset ℕ) a₂ (ct.sig i₂ : Multiset ℕ) := by
  rw [PreEpsCertificateExplicitDagInt.iPair, IEpsExplicitNat,
    ct.momentTop_eq hpack hpred,
    facMomentDirect_eq _ _ _ (ct.zeroFree i₁) (ct.zeroFree i₂)]
  simp

/-- The labelled marginal pairing agrees with the specification pairing when the packed moment
table has been certified. -/
theorem PreEpsCertificateExplicitDagInt.jPair_eq
    {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (hpack : ∀ p, ct.pairValue p = ct.directPairValue p)
    (hpred : ∀ p : Fin (ct.S * ct.S),
      facMomentDirect (K - 1) (ct.sig p.divNat) (ct.sig p.modNat) < ct.momentRadix)
    (a₁ : ℕ) (i₁ : Fin ct.S) (a₂ : ℕ) (i₂ : Fin ct.S) :
    ct.jPair a₁ i₁ a₂ i₂ = JEpsExplicitNat K epsilonDenominator degreeBound
      a₁ (ct.sig i₁ : Multiset ℕ) a₂ (ct.sig i₂ : Multiset ℕ) := by
  rw [PreEpsCertificateExplicitDagInt.jPair, JEpsExplicitNat]
  refine sum_congr rfl fun r₁ hr₁ ↦ ?_
  refine sum_congr rfl fun r₂ hr₂ ↦ ?_
  rw [ct.momentPred_eq hpack hpred,
    facMomentDirect_eq _ _ _ (ct.zeroFree (ct.erase i₁ r₁)) (ct.zeroFree (ct.erase i₂ r₂))]
  rw [ct.erase_sig i₁ r₁ (by simpa using hr₁), ct.erase_sig i₂ r₂ (by simpa using hr₂)]
  simp

/-- One entry of the enlarged-simplex quadratic form. -/
def PreEpsCertificateExplicitDagInt.lhsPairTerm {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (i j : Fin ct.N) : ℤ :=
  ct.coeff i * ct.coeff j *
    ct.iPair (ct.a i) (ct.sigIndex i) (ct.a j) (ct.sigIndex j)

/-- One entry of the marginal quadratic form. -/
def PreEpsCertificateExplicitDagInt.rhsPairTerm {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (i j : Fin ct.N) : ℤ :=
  ct.coeff i * ct.coeff j *
    ct.jPair (ct.a i) (ct.sigIndex i) (ct.a j) (ct.sigIndex j)

/-- One aggregated enlarged-simplex feature.  Its weight combines all ordered basis pairs with
the same two signature labels and the same distinguished-exponent sum. -/
structure LhsPairFeature (S : ℕ) where
  /-- First signature label. -/
  first : Fin S
  /-- Second signature label. -/
  second : Fin S
  /-- Sum of the two distinguished exponents. -/
  aSum : ℕ
  /-- Sum of the corresponding products of basis coefficients. -/
  weight : ℤ

/-- Apply a test function to every ordered pair of basis elements. -/
def PreEpsCertificateExplicitDagInt.lhsBasisPairLinear
    {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (g : Fin ct.S → Fin ct.S → ℕ → ℤ) : ℤ :=
  ∑ i, ∑ j, ct.coeff i * ct.coeff j *
    g (ct.sigIndex i) (ct.sigIndex j) (ct.a i + ct.a j)

/-- A sparse LHS feature family represents the coefficient convolution of the original basis. -/
def LhsPairFeature.Correct
    {K epsilonDenominator degreeBound F : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (feature : Fin F → LhsPairFeature ct.S) : Prop :=
  ∀ g : Fin ct.S → Fin ct.S → ℕ → ℤ,
    (∑ u, (feature u).weight * g (feature u).first (feature u).second
      (feature u).aSum) =
      ct.lhsBasisPairLinear g

/-- Evaluate only the diagonal and strict upper triangle of a symmetric finite square. -/
def symmetricFinSquare {n : ℕ} (f : Fin n → Fin n → ℤ) : ℤ :=
  ∑ i, ∑ j, if i < j then 2 * f i j else if i = j then f i j else 0

/-- The upper-triangle evaluator equals the full square sum for a symmetric kernel. -/
theorem symmetricFinSquare_eq {n : ℕ} (f : Fin n → Fin n → ℤ)
    (hsymm : ∀ i j, f i j = f j i) :
    symmetricFinSquare f = ∑ i, ∑ j, f i j := by
  let upper := ∑ i, ∑ j, if i < j then f i j else 0
  let diagonal := ∑ i, ∑ j, if i = j then f i j else 0
  let lower := ∑ i, ∑ j, if j < i then f i j else 0
  have hlower : lower = upper := by
    simp only [lower, upper]
    rw [sum_comm]
    refine sum_congr rfl fun i hi ↦ ?_
    refine sum_congr rfl fun j hj ↦ ?_
    by_cases hij : i < j
    · simp only [hij, if_true]
      exact hsymm j i
    · simp only [hij, if_false]
  have hsplit : (∑ i, ∑ j, f i j) = upper + diagonal + lower := by
    simp only [upper, diagonal, lower]
    simp_rw [← Finset.sum_add_distrib]
    refine sum_congr rfl fun i hi ↦ ?_
    refine sum_congr rfl fun j hj ↦ ?_
    rcases lt_trichotomy i j with hij | hij | hij
    · have hne : i ≠ j := _root_.ne_of_lt hij
      have hnji : ¬j < i := not_lt_of_ge (le_of_lt hij)
      simp [hij, hne, hnji]
    · subst j
      simp
    · simp [hij, ne_of_gt hij, not_lt_of_ge (le_of_lt hij)]
  rw [hsplit, hlower, symmetricFinSquare]
  simp only [upper, diagonal]
  simp_rw [← Finset.sum_add_distrib]
  refine sum_congr rfl fun i hi ↦ ?_
  refine sum_congr rfl fun j hj ↦ ?_
  by_cases hij : i < j
  · have hne : i ≠ j := _root_.ne_of_lt hij
    simp [hij, hne]
    ring
  · by_cases heq : i = j
    · simp [heq]
    · simp [hij, heq]

/-- One enlarged-simplex pair evaluated through the finite scalar cache. -/
def PreEpsCertificateExplicitDagInt.lhsPairWithTablesTerm
    {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (i j : Fin ct.N) : ℤ :=
  ct.coeff i * ct.coeff j *
    ct.iPairWithTables tables (ct.a i) (ct.sigIndex i) (ct.a j) (ct.sigIndex j)

/-- Symmetric upper-triangle evaluation of the cached enlarged-simplex quadratic form. -/
def PreEpsCertificateExplicitDagInt.lhsPairWithTablesSumSymmetric
    {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound) : ℤ :=
  symmetricFinSquare (ct.lhsPairWithTablesTerm tables)

/-- Correct scalar and moment tables make the cached symmetric evaluator equal the original
enlarged-simplex quadratic form. -/
theorem PreEpsCertificateExplicitDagInt.lhsPairWithTablesSumSymmetric_eq
    {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (htables : tables.Correct) (hmoment : ∀ i j, ct.momentTop i j = ct.momentTop j i) :
    ct.lhsPairWithTablesSumSymmetric tables = ∑ i, ∑ j, ct.lhsPairTerm i j := by
  rw [PreEpsCertificateExplicitDagInt.lhsPairWithTablesSumSymmetric]
  calc
    symmetricFinSquare (ct.lhsPairWithTablesTerm tables) =
        ∑ i, ∑ j, ct.lhsPairWithTablesTerm tables i j := by
      apply symmetricFinSquare_eq
      intro i j
      have hscalar : tables.iScalar
          (ct.a i + ct.a j + ((ct.sig (ct.sigIndex i)).sum + (ct.sig (ct.sigIndex j)).sum))
          (ct.a i + ct.a j) = tables.iScalar
          (ct.a j + ct.a i + ((ct.sig (ct.sigIndex j)).sum + (ct.sig (ct.sigIndex i)).sum))
          (ct.a j + ct.a i) := by
        congr 1 <;> omega
      simp only [PreEpsCertificateExplicitDagInt.lhsPairWithTablesTerm,
        PreEpsCertificateExplicitDagInt.iPairWithTables,
        PreEpsCertificateExplicitDagInt.iPairCached, hmoment, hscalar]
      ring
    _ = ∑ i, ∑ j, ct.lhsPairTerm i j := by
      refine sum_congr rfl fun i hi ↦ ?_
      refine sum_congr rfl fun j hj ↦ ?_
      rw [PreEpsCertificateExplicitDagInt.lhsPairWithTablesTerm,
        PreEpsCertificateExplicitDagInt.lhsPairTerm,
        ct.iPairWithTables_eq tables htables]

/-- A basis element's signature and distinguished exponent, with the exponent bounded by the
certificate's degree parameter. -/
def PreEpsCertificateExplicitDagInt.lhsCoefficientKey
    {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound) (i : Fin ct.N) :
    Fin ct.S × Fin (degreeBound + 1) :=
  (ct.sigIndex i, ⟨ct.a i, by
    have := ct.degree i
    omega⟩)

/-- One independently checkable compact-coefficient entry. -/
@[reducible] def LhsCoefficientCacheCorrectAt
    {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (cache : Fin ct.S → Fin (degreeBound + 1) → ℤ)
    (key : Fin ct.S × Fin (degreeBound + 1)) : Prop :=
  cache key.1 key.2 = ∑ i, if ct.lhsCoefficientKey i = key then ct.coeff i else 0

/-- Fast bounded Cauchy coefficient for a fixed sum of distinguished exponents. -/
def lhsCoefficientConvolution {S degreeBound : ℕ}
    (cache : Fin S → Fin (degreeBound + 1) → ℤ)
    (first second : Fin S) (aSum : Fin (2 * degreeBound + 1)) : ℤ :=
  ∑ a : Fin (degreeBound + 1),
    if h : a.val ≤ aSum.val ∧ aSum.val - a.val < degreeBound + 1 then
      cache first a * cache second ⟨aSum.val - a.val, h.2⟩
    else 0

/-- Canonical unordered coefficient of one signature pair and exponent sum. -/
def lhsDenseFeatureWeight {S degreeBound : ℕ}
    (cache : Fin S → Fin (degreeBound + 1) → ℤ)
    (first second : Fin S) (aSum : Fin (2 * degreeBound + 1)) : ℤ :=
  if first < second then 2 * lhsCoefficientConvolution cache first second aSum
  else if first = second then lhsCoefficientConvolution cache first second aSum else 0

/-- One canonical sparse LHS key; its weight is derived from the compact coefficient cache. -/
structure LhsPairFeatureKey (S degreeBound : ℕ) where
  /-- First signature label. -/
  first : Fin S
  /-- Second signature label. -/
  second : Fin S
  /-- Sum of the two distinguished exponents. -/
  aSum : Fin (2 * degreeBound + 1)
deriving DecidableEq, Fintype

/-- Dense key space used only to certify that the sparse LHS family omits exactly the zero
coefficients. -/
abbrev LhsDenseFeatureKey (S degreeBound : ℕ) :=
  Fin S × (Fin S × Fin (2 * degreeBound + 1))

/-- Read a sparse key as an element of the dense key space. -/
def LhsPairFeatureKey.toDense {S degreeBound : ℕ}
    (key : LhsPairFeatureKey S degreeBound) : LhsDenseFeatureKey S degreeBound :=
  (key.first, key.second, key.aSum)

/-- Weight of a dense LHS key. -/
def lhsDenseFeatureKeyWeight {S degreeBound : ℕ}
    (cache : Fin S → Fin (degreeBound + 1) → ℤ)
    (key : LhsDenseFeatureKey S degreeBound) : ℤ :=
  lhsDenseFeatureWeight cache key.1 key.2.1 key.2.2

/-- One dense-key direction of sparse-support correctness. -/
@[reducible] def LhsPairFeatureKey.ForwardCorrectAt {S degreeBound F : ℕ}
    (cache : Fin S → Fin (degreeBound + 1) → ℤ)
    (feature : Fin F → LhsPairFeatureKey S degreeBound)
    (locate : LhsDenseFeatureKey S degreeBound → Fin F)
    (key : LhsDenseFeatureKey S degreeBound) : Prop :=
  lhsDenseFeatureKeyWeight cache key ≠ 0 → (feature (locate key)).toDense = key

/-- One sparse-feature direction of sparse-support correctness. -/
@[reducible] def LhsPairFeatureKey.BackCorrectAt {S degreeBound F : ℕ}
    (cache : Fin S → Fin (degreeBound + 1) → ℤ)
    (feature : Fin F → LhsPairFeatureKey S degreeBound)
    (locate : LhsDenseFeatureKey S degreeBound → Fin F) (u : Fin F) : Prop :=
  lhsDenseFeatureKeyWeight cache (feature u).toDense ≠ 0 ∧
    locate (feature u).toDense = u

/-- One class of basis entries having the same distinguished and signature degrees. -/
structure LhsDegreeGroup where
  /-- Position of the first member in the flattened group permutation. -/
  start : ℕ
  /-- Number of basis entries in the class. -/
  size : ℕ
  /-- Common distinguished exponent. -/
  distinguishedDegree : ℕ
  /-- Common sum of the signature exponents. -/
  signatureDegree : ℕ

/-- A permutation of the basis entries partitioned by their two degree coordinates. -/
structure LhsDegreePartition (N G : ℕ) where
  /-- Metadata for each degree class. -/
  group : Fin G → LhsDegreeGroup
  /-- Basis entry stored at each position of the flattened group permutation. -/
  memberIndex : Fin N → Fin N
  /-- Degree class containing each basis entry. -/
  locateGroup : Fin N → Fin G
  /-- Offset of each basis entry within its degree class. -/
  locateOffset : Fin N → ℕ

/-- Position in the flattened group permutation represented by one group offset. -/
def LhsDegreePartition.flatMember {N G : ℕ} (partition : LhsDegreePartition N G)
    (hbound : ∀ group, (partition.group group).start + (partition.group group).size ≤ N)
    (group : Fin G) (offset : Fin (partition.group group).size) : Fin N :=
  ⟨(partition.group group).start + offset.val, by
    exact lt_of_lt_of_le (Nat.add_lt_add_left offset.isLt _) (hbound group)⟩

/-- Basis entry represented by one valid offset inside a degree class. -/
def LhsDegreePartition.member {N G : ℕ} (partition : LhsDegreePartition N G)
    (hbound : ∀ group, (partition.group group).start + (partition.group group).size ≤ N)
    (group : Fin G) (offset : Fin (partition.group group).size) : Fin N :=
  partition.memberIndex (partition.flatMember hbound group offset)

/-- A degree partition is a permutation of the basis and records the correct degree keys. -/
structure LhsDegreePartition.Valid
    {K epsilonDenominator degreeBound G : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (partition : LhsDegreePartition ct.N G) : Prop where
  /-- Every group lies inside the flattened permutation. -/
  bound : ∀ group, (partition.group group).start + (partition.group group).size ≤ ct.N
  /-- Every inverse offset lies inside its group. -/
  locateOffset_lt : ∀ i,
    partition.locateOffset i < (partition.group (partition.locateGroup i)).size
  /-- Looking up the located group member recovers the original basis entry. -/
  right_inv : ∀ i, partition.member bound (partition.locateGroup i)
    ⟨partition.locateOffset i, locateOffset_lt i⟩ = i
  /-- Locating a stored group member recovers its group and offset. -/
  left_inv : ∀ group (offset : Fin (partition.group group).size),
    partition.locateGroup (partition.member bound group offset) = group ∧
      partition.locateOffset (partition.member bound group offset) = offset.val
  /-- Every member has the two degrees recorded by its group. -/
  key : ∀ group (offset : Fin (partition.group group).size),
    ct.a (partition.member bound group offset) =
        (partition.group group).distinguishedDegree ∧
      (ct.sig (ct.sigIndex (partition.member bound group offset))).sum =
        (partition.group group).signatureDegree

/-- A valid LHS degree partition identifies dependent group offsets with the original basis. -/
noncomputable def LhsDegreePartition.equiv
    {K epsilonDenominator degreeBound G : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (partition : LhsDegreePartition ct.N G) (hvalid : partition.Valid ct) :
    (Σ group, Fin (partition.group group).size) ≃ Fin ct.N :=
  Equiv.ofBijective
    (fun entry ↦ partition.member hvalid.bound entry.1 entry.2)
    ⟨by
      intro left right heq
      have hgroup : left.1 = right.1 :=
        calc
          left.1 = partition.locateGroup
              (partition.member hvalid.bound left.1 left.2) :=
            (hvalid.left_inv left.1 left.2).1.symm
          _ = partition.locateGroup
              (partition.member hvalid.bound right.1 right.2) := congrArg _ heq
          _ = right.1 := (hvalid.left_inv right.1 right.2).1
      rcases left with ⟨leftGroup, leftOffset⟩
      rcases right with ⟨rightGroup, rightOffset⟩
      simp only at hgroup
      subst rightGroup
      have hoffset : leftOffset.val = rightOffset.val :=
        calc
          leftOffset.val = partition.locateOffset
              (partition.member hvalid.bound leftGroup leftOffset) :=
            (hvalid.left_inv leftGroup leftOffset).2.symm
          _ = partition.locateOffset
              (partition.member hvalid.bound leftGroup rightOffset) := congrArg _ heq
          _ = rightOffset.val := (hvalid.left_inv leftGroup rightOffset).2
      exact Sigma.ext rfl (heq_of_eq (Fin.ext hoffset)), by
      intro i
      let offset : Fin (partition.group (partition.locateGroup i)).size :=
        ⟨partition.locateOffset i, hvalid.locateOffset_lt i⟩
      exact ⟨⟨partition.locateGroup i, offset⟩, hvalid.right_inv i⟩⟩

/-- Reindexing a sum through a valid LHS degree partition preserves its value. -/
theorem LhsDegreePartition.sum_equiv
    {K epsilonDenominator degreeBound G : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (partition : LhsDegreePartition ct.N G) (hvalid : partition.Valid ct)
    (f : Fin ct.N → ℤ) :
    (∑ group, ∑ offset : Fin (partition.group group).size,
      f (partition.member hvalid.bound group offset)) = ∑ i, f i :=
  calc
    (∑ group, ∑ offset : Fin (partition.group group).size,
        f (partition.member hvalid.bound group offset)) =
        ∑ entry : Σ group, Fin (partition.group group).size,
          f (partition.member hvalid.bound entry.1 entry.2) :=
      (Fintype.sum_sigma' fun group offset ↦
        f (partition.member hvalid.bound group offset)).symm
    _ = ∑ i, f i := by
      apply Fintype.sum_equiv (partition.equiv ct hvalid)
      intro entry
      rfl

/-- Row-major index of a degree class and a signature. -/
def lhsDegreeSignatureIndex {G S : ℕ} (group : Fin G) (signature : Fin S) : Fin (G * S) :=
  ⟨group.val * S + signature.val,
    calc
      group.val * S + signature.val < group.val * S + S :=
        Nat.add_lt_add_left signature.isLt _
      _ = (group.val + 1) * S := (Nat.succ_mul group.val S).symm
      _ ≤ G * S := Nat.mul_le_mul_right S (Nat.succ_le_iff.mpr group.isLt)⟩

/-- Decoding a row-major degree/signature index recovers its degree class. -/
@[simp]
theorem lhsDegreeSignatureIndex_divNat {G S : ℕ} (group : Fin G) (signature : Fin S) :
    (lhsDegreeSignatureIndex group signature).divNat = group := by
  apply Fin.ext
  simp only [Fin.divNat, lhsDegreeSignatureIndex, Fin.val_mk]
  rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ (Fin.size_positive signature),
    Nat.div_eq_of_lt signature.isLt, zero_add]

/-- Decoding a row-major degree/signature index recovers its signature. -/
@[simp]
theorem lhsDegreeSignatureIndex_modNat {G S : ℕ} (group : Fin G) (signature : Fin S) :
    (lhsDegreeSignatureIndex group signature).modNat = signature := by
  apply Fin.ext
  simp only [Fin.modNat, lhsDegreeSignatureIndex, Fin.val_mk]
  rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt signature.isLt]

/-- Direct moment transform of one degree class, evaluated at one target signature. -/
def PreEpsCertificateExplicitDagInt.lhsDegreeTransformDirect
    {K epsilonDenominator degreeBound G : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (partition : LhsDegreePartition ct.N G) (hvalid : partition.Valid ct)
    (group : Fin G) (target : Fin ct.S) : ℤ :=
  ∑ offset : Fin (partition.group group).size,
    ct.coeff (partition.member hvalid.bound group offset) *
      ct.momentTop target (ct.sigIndex (partition.member hvalid.bound group offset))

/-- One stored entry of the class-by-signature moment transform is correct. -/
@[reducible] def LhsDegreeTransformCorrectAt
    {K epsilonDenominator degreeBound G : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (partition : LhsDegreePartition ct.N G) (hvalid : partition.Valid ct)
    (transform : Fin G → Fin ct.S → ℤ) (group : Fin G) (target : Fin ct.S) : Prop :=
  transform group target = ct.lhsDegreeTransformDirect partition hvalid group target

/-- Sparse indexing data for the class/signature transform.  Location zero denotes an entry that
is deliberately computed directly; positive locations are one-based stored-value indices. -/
structure LhsSparseTransformIndex (G S T : ℕ) where
  /-- One-based stored location of a class/signature pair, or zero for direct evaluation. -/
  location : Fin G → Fin S → Fin (T + 1)
  /-- Degree class represented by each stored value. -/
  entryGroup : Fin T → Fin G
  /-- Target signature represented by each stored value. -/
  entryTarget : Fin T → Fin S

/-- Convert a nonzero one-based sparse location to its zero-based stored-value index. -/
def LhsSparseTransformIndex.entryOf {G S T : ℕ} (index : LhsSparseTransformIndex G S T)
    (group : Fin G) (target : Fin S) (h : (index.location group target).val ≠ 0) : Fin T :=
  ⟨(index.location group target).val - 1, by
    have := (index.location group target).isLt
    omega⟩

/-- Every positive sparse location points back to the class/signature pair that requested it. -/
structure LhsSparseTransformIndex.Valid {G S T : ℕ}
    (index : LhsSparseTransformIndex G S T) : Prop where
  /-- Decoding a nonzero location recovers its class and target signature. -/
  right_inv : ∀ group target,
    if h : (index.location group target).val = 0 then True else
      index.entryGroup (index.entryOf group target h) = group ∧
        index.entryTarget (index.entryOf group target h) = target

/-- Read a sparse stored transform entry, falling back to the direct formula off its support. -/
def PreEpsCertificateExplicitDagInt.lhsSparseTransformGet
    {K epsilonDenominator degreeBound G T : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (partition : LhsDegreePartition ct.N G) (hvalid : partition.Valid ct)
    (value : Fin T → ℤ) (index : LhsSparseTransformIndex G ct.S T)
    (group : Fin G) (target : Fin ct.S) : ℤ :=
  if h : (index.location group target).val = 0 then
    ct.lhsDegreeTransformDirect partition hvalid group target
  else value (index.entryOf group target h)

/-- One stored sparse-transform value agrees with the direct class moment sum. -/
@[reducible] def LhsSparseTransformValueCorrectAt
    {K epsilonDenominator degreeBound G T : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (partition : LhsDegreePartition ct.N G) (hvalid : partition.Valid ct)
    (value : Fin T → ℤ) (index : LhsSparseTransformIndex G ct.S T) (entry : Fin T) : Prop :=
  value entry = ct.lhsDegreeTransformDirect partition hvalid
    (index.entryGroup entry) (index.entryTarget entry)

/-- One bounded block of stored sparse-transform values is correct. -/
@[reducible] def LhsSparseTransformValueBlockCorrect
    {K epsilonDenominator degreeBound G T blockSize : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (partition : LhsDegreePartition ct.N G) (hvalid : partition.Valid ct)
    (value : Fin T → ℤ) (index : LhsSparseTransformIndex G ct.S T) (block : ℕ) : Prop :=
  ∀ offset : Fin blockSize,
    let entry := block * blockSize + offset.val
    if h : entry < T then
      LhsSparseTransformValueCorrectAt ct partition hvalid value index ⟨entry, h⟩
    else True

/-- A valid sparse index and correct stored values make every transform lookup exact. -/
theorem PreEpsCertificateExplicitDagInt.lhsSparseTransformGet_correct
    {K epsilonDenominator degreeBound G T : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (partition : LhsDegreePartition ct.N G) (hvalid : partition.Valid ct)
    (value : Fin T → ℤ) (index : LhsSparseTransformIndex G ct.S T)
    (hindex : index.Valid)
    (hvalue : ∀ entry, LhsSparseTransformValueCorrectAt ct partition hvalid value index entry) :
    ∀ group target, LhsDegreeTransformCorrectAt ct partition hvalid
      (ct.lhsSparseTransformGet partition hvalid value index) group target := by
  intro group target
  rw [LhsDegreeTransformCorrectAt, PreEpsCertificateExplicitDagInt.lhsSparseTransformGet]
  split_ifs with hlocation
  · rfl
  · rw [hvalue]
    have hkey := hindex.right_inv group target
    rw [dif_neg hlocation] at hkey
    rw [hkey.1, hkey.2]

/-- Contract two degree classes using the smaller sparse support and a reusable moment
transform. -/
def PreEpsCertificateExplicitDagInt.lhsDegreeContraction
    {K epsilonDenominator degreeBound G : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (partition : LhsDegreePartition ct.N G) (hvalid : partition.Valid ct)
    (transform : Fin G → Fin ct.S → ℤ) (left right : Fin G) : ℤ :=
  if (partition.group left).size ≤ (partition.group right).size then
    ∑ offset : Fin (partition.group left).size,
      ct.coeff (partition.member hvalid.bound left offset) *
        transform right (ct.sigIndex (partition.member hvalid.bound left offset))
  else
    ∑ offset : Fin (partition.group right).size,
      ct.coeff (partition.member hvalid.bound right offset) *
        transform left (ct.sigIndex (partition.member hvalid.bound right offset))

/-- Pair two LHS degree classes, taking their common scalar factor outside the contraction. -/
def PreEpsCertificateExplicitDagInt.lhsDegreePair
    {K epsilonDenominator degreeBound G : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (partition : LhsDegreePartition ct.N G) (hvalid : partition.Valid ct)
    (transform : Fin G → Fin ct.S → ℤ) (left right : Fin G) : ℤ :=
  tables.iScalar
      ((partition.group left).distinguishedDegree +
          (partition.group right).distinguishedDegree +
        ((partition.group left).signatureDegree +
          (partition.group right).signatureDegree))
      ((partition.group left).distinguishedDegree +
        (partition.group right).distinguishedDegree) *
    ct.lhsDegreeContraction partition hvalid transform left right

/-- One upper-triangular row of the LHS contraction by degree classes. -/
def PreEpsCertificateExplicitDagInt.lhsDegreeSymmetricRow
    {K epsilonDenominator degreeBound G : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (partition : LhsDegreePartition ct.N G) (hvalid : partition.Valid ct)
    (transform : Fin G → Fin ct.S → ℤ) (left : Fin G) : ℤ :=
  ∑ right, if left < right then
      2 * ct.lhsDegreePair tables partition hvalid transform left right
    else if left = right then
      ct.lhsDegreePair tables partition hvalid transform left right
    else 0

/-- A correct transform expands the sparse class contraction into its full member square. -/
theorem PreEpsCertificateExplicitDagInt.lhsDegreeContraction_eq
    {K epsilonDenominator degreeBound G : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (partition : LhsDegreePartition ct.N G) (hvalid : partition.Valid ct)
    (transform : Fin G → Fin ct.S → ℤ)
    (htransform : ∀ group target,
      LhsDegreeTransformCorrectAt ct partition hvalid transform group target)
    (hmoment : ∀ i j, ct.momentTop i j = ct.momentTop j i) (left right : Fin G) :
    ct.lhsDegreeContraction partition hvalid transform left right =
      ∑ i : Fin (partition.group left).size,
        ∑ j : Fin (partition.group right).size,
          ct.coeff (partition.member hvalid.bound left i) *
            ct.coeff (partition.member hvalid.bound right j) *
              ct.momentTop (ct.sigIndex (partition.member hvalid.bound left i))
                (ct.sigIndex (partition.member hvalid.bound right j)) := by
  rw [PreEpsCertificateExplicitDagInt.lhsDegreeContraction]
  by_cases hsize : (partition.group left).size ≤ (partition.group right).size
  · rw [if_pos hsize]
    refine sum_congr rfl fun i hi ↦ ?_
    rw [htransform right, PreEpsCertificateExplicitDagInt.lhsDegreeTransformDirect,
      Finset.mul_sum]
    refine sum_congr rfl fun j hj ↦ ?_
    ring
  · rw [if_neg hsize]
    simp_rw [htransform left, PreEpsCertificateExplicitDagInt.lhsDegreeTransformDirect,
      Finset.mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun i hi ↦ ?_
    refine sum_congr rfl fun j hj ↦ ?_
    rw [hmoment]
    ring

/-- The cached LHS basis-pair term is symmetric when the stored moments are symmetric. -/
theorem PreEpsCertificateExplicitDagInt.lhsPairWithTablesTerm_comm
    {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (hmoment : ∀ i j, ct.momentTop i j = ct.momentTop j i) (i j : Fin ct.N) :
    ct.lhsPairWithTablesTerm tables i j = ct.lhsPairWithTablesTerm tables j i := by
  have hscalar : tables.iScalar
      (ct.a i + ct.a j + ((ct.sig (ct.sigIndex i)).sum + (ct.sig (ct.sigIndex j)).sum))
      (ct.a i + ct.a j) = tables.iScalar
      (ct.a j + ct.a i + ((ct.sig (ct.sigIndex j)).sum + (ct.sig (ct.sigIndex i)).sum))
      (ct.a j + ct.a i) := by
    congr 1 <;> omega
  simp only [PreEpsCertificateExplicitDagInt.lhsPairWithTablesTerm,
    PreEpsCertificateExplicitDagInt.iPairWithTables,
    PreEpsCertificateExplicitDagInt.iPairCached, hscalar, hmoment]
  ring

/-- A degree-class pairing is the corresponding rectangular sum of cached basis-pair terms. -/
theorem PreEpsCertificateExplicitDagInt.lhsDegreePair_eq
    {K epsilonDenominator degreeBound G : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (partition : LhsDegreePartition ct.N G) (hvalid : partition.Valid ct)
    (transform : Fin G → Fin ct.S → ℤ)
    (htransform : ∀ group target,
      LhsDegreeTransformCorrectAt ct partition hvalid transform group target)
    (hmoment : ∀ i j, ct.momentTop i j = ct.momentTop j i) (left right : Fin G) :
    ct.lhsDegreePair tables partition hvalid transform left right =
      ∑ i : Fin (partition.group left).size,
        ∑ j : Fin (partition.group right).size,
          ct.lhsPairWithTablesTerm tables
            (partition.member hvalid.bound left i)
            (partition.member hvalid.bound right j) := by
  rw [PreEpsCertificateExplicitDagInt.lhsDegreePair,
    ct.lhsDegreeContraction_eq partition hvalid transform htransform hmoment]
  rw [Finset.mul_sum]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mul_sum]
  refine sum_congr rfl fun j hj ↦ ?_
  have hleft := hvalid.key left i
  have hright := hvalid.key right j
  simp only [PreEpsCertificateExplicitDagInt.lhsPairWithTablesTerm,
    PreEpsCertificateExplicitDagInt.iPairWithTables,
    PreEpsCertificateExplicitDagInt.iPairCached, hleft.1, hleft.2, hright.1, hright.2]
  push_cast
  ring

/-- Degree-class pairing is symmetric. -/
theorem PreEpsCertificateExplicitDagInt.lhsDegreePair_comm
    {K epsilonDenominator degreeBound G : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (partition : LhsDegreePartition ct.N G) (hvalid : partition.Valid ct)
    (transform : Fin G → Fin ct.S → ℤ)
    (htransform : ∀ group target,
      LhsDegreeTransformCorrectAt ct partition hvalid transform group target)
    (hmoment : ∀ i j, ct.momentTop i j = ct.momentTop j i) (left right : Fin G) :
    ct.lhsDegreePair tables partition hvalid transform left right =
      ct.lhsDegreePair tables partition hvalid transform right left := by
  rw [ct.lhsDegreePair_eq tables partition hvalid transform htransform hmoment,
    ct.lhsDegreePair_eq tables partition hvalid transform htransform hmoment, sum_comm]
  refine sum_congr rfl fun i hi ↦ ?_
  refine sum_congr rfl fun j hj ↦ ?_
  exact ct.lhsPairWithTablesTerm_comm tables hmoment _ _

/-- Summing the degree-class rows reproduces the cached symmetric LHS evaluator. -/
theorem PreEpsCertificateExplicitDagInt.sum_lhsDegreeSymmetricRow
    {K epsilonDenominator degreeBound G : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (partition : LhsDegreePartition ct.N G) (hvalid : partition.Valid ct)
    (transform : Fin G → Fin ct.S → ℤ)
    (htransform : ∀ group target,
      LhsDegreeTransformCorrectAt ct partition hvalid transform group target)
    (hmoment : ∀ i j, ct.momentTop i j = ct.momentTop j i) :
    (∑ group, ct.lhsDegreeSymmetricRow tables partition hvalid transform group) =
      ct.lhsPairWithTablesSumSymmetric tables := by
  simp only [PreEpsCertificateExplicitDagInt.lhsDegreeSymmetricRow]
  change symmetricFinSquare
      (ct.lhsDegreePair tables partition hvalid transform) = _
  rw [symmetricFinSquare_eq _
    (ct.lhsDegreePair_comm tables partition hvalid transform htransform hmoment)]
  calc
    (∑ left, ∑ right, ct.lhsDegreePair tables partition hvalid transform left right) =
        ∑ left, ∑ right,
          ∑ i : Fin (partition.group left).size,
            ∑ j : Fin (partition.group right).size,
              ct.lhsPairWithTablesTerm tables
                (partition.member hvalid.bound left i)
                (partition.member hvalid.bound right j) := by
      refine sum_congr rfl fun left hleft ↦ ?_
      refine sum_congr rfl fun right hright ↦ ?_
      exact ct.lhsDegreePair_eq tables partition hvalid transform htransform hmoment left right
    _ = ∑ left, ∑ i : Fin (partition.group left).size,
        ∑ right, ∑ j : Fin (partition.group right).size,
          ct.lhsPairWithTablesTerm tables
            (partition.member hvalid.bound left i)
            (partition.member hvalid.bound right j) := by
      refine sum_congr rfl fun left hleft ↦ ?_
      rw [sum_comm]
    _ = ∑ left, ∑ i : Fin (partition.group left).size,
        ∑ j : Fin ct.N, ct.lhsPairWithTablesTerm tables
          (partition.member hvalid.bound left i) j := by
      refine sum_congr rfl fun left hleft ↦ ?_
      refine sum_congr rfl fun i hi ↦ ?_
      exact partition.sum_equiv ct hvalid
        (ct.lhsPairWithTablesTerm tables (partition.member hvalid.bound left i))
    _ = ∑ i : Fin ct.N, ∑ j : Fin ct.N, ct.lhsPairWithTablesTerm tables i j :=
      partition.sum_equiv ct hvalid
        (fun i ↦ ∑ j, ct.lhsPairWithTablesTerm tables i j)
    _ = ct.lhsPairWithTablesSumSymmetric tables :=
      (symmetricFinSquare_eq (ct.lhsPairWithTablesTerm tables)
        (ct.lhsPairWithTablesTerm_comm tables hmoment)).symm

/-- One aggregated one-sided marginal feature.  Its weight combines every basis/erasure
transition with the same erased signature and the same two scalar exponents. -/
structure RhsMarginalFeature (S : ℕ) where
  /-- Signature label after erasing the selected exponent. -/
  signature : Fin S
  /-- Original signature sum minus the erased exponent. -/
  residualDegree : ℕ
  /-- Distinguished exponent plus erased exponent plus one. -/
  radialDegree : ℕ
  /-- Sum of coefficient times marginal factor over all represented transitions. -/
  weight : ℤ

/-- One consecutive group of marginal features having the same two degree coordinates. -/
structure RhsDegreeGroup where
  /-- Index of the first feature in the group. -/
  start : ℕ
  /-- Number of features in the group. -/
  size : ℕ
  /-- Common residual degree. -/
  residualDegree : ℕ
  /-- Common radial degree. -/
  radialDegree : ℕ

/-- A consecutive partition of marginal features by their two degree coordinates. -/
structure RhsDegreePartition (F G : ℕ) where
  /-- The consecutive feature groups. -/
  group : Fin G → RhsDegreeGroup
  /-- Group containing each feature. -/
  locateGroup : Fin F → Fin G
  /-- Offset of each feature inside its group. -/
  locateOffset : Fin F → ℕ

/-- Flat feature index represented by an offset inside a consecutive degree group. -/
def RhsDegreePartition.memberIndex {F G : ℕ} (partition : RhsDegreePartition F G)
    (group : Fin G) (offset : ℕ) : ℕ :=
  (partition.group group).start + offset

/-- Read a feature at a valid offset inside a consecutive degree group. -/
def RhsDegreePartition.member {F G : ℕ} (partition : RhsDegreePartition F G)
    (hbound : ∀ group, (partition.group group).start + (partition.group group).size ≤ F)
    (group : Fin G) (offset : Fin (partition.group group).size) : Fin F :=
  ⟨partition.memberIndex group offset.val, by
    rw [RhsDegreePartition.memberIndex]
    exact lt_of_lt_of_le (Nat.add_lt_add_left offset.isLt _) (hbound group)⟩

/-- A degree partition enumerates every feature exactly once and records the correct degree key. -/
structure RhsDegreePartition.Valid {S F G : ℕ} (partition : RhsDegreePartition F G)
    (feature : Fin F → RhsMarginalFeature S) : Prop where
  /-- Every group lies inside the feature array. -/
  bound : ∀ group, (partition.group group).start + (partition.group group).size ≤ F
  /-- Every inverse offset lies inside its group. -/
  locateOffset_lt : ∀ u,
    partition.locateOffset u < (partition.group (partition.locateGroup u)).size
  /-- Locating a feature and then reading that group offset recovers its index. -/
  right_inv : ∀ u, partition.memberIndex (partition.locateGroup u)
    (partition.locateOffset u) = u.val
  /-- Reading a group offset and then locating it recovers the group and offset. -/
  left_inv : ∀ group (offset : Fin (partition.group group).size),
    partition.locateGroup (partition.member bound group offset) = group ∧
      partition.locateOffset (partition.member bound group offset) = offset.val
  /-- Every feature in a group has the group's two degree coordinates. -/
  key : ∀ group (offset : Fin (partition.group group).size),
    (feature (partition.member bound group offset)).residualDegree =
        (partition.group group).residualDegree ∧
      (feature (partition.member bound group offset)).radialDegree =
        (partition.group group).radialDegree

/-- A valid degree partition identifies its dependent family of group offsets with all features. -/
noncomputable def RhsDegreePartition.equiv {S F G : ℕ} (partition : RhsDegreePartition F G)
    (feature : Fin F → RhsMarginalFeature S) (hvalid : partition.Valid feature) :
    (Σ group, Fin (partition.group group).size) ≃ Fin F :=
  Equiv.ofBijective
    (fun entry ↦ partition.member hvalid.bound entry.1 entry.2)
    ⟨by
      intro left right heq
      have hgroup : left.1 = right.1 :=
        calc
          left.1 = partition.locateGroup
              (partition.member hvalid.bound left.1 left.2) :=
            (hvalid.left_inv left.1 left.2).1.symm
          _ = partition.locateGroup
              (partition.member hvalid.bound right.1 right.2) := congrArg _ heq
          _ = right.1 := (hvalid.left_inv right.1 right.2).1
      rcases left with ⟨leftGroup, leftOffset⟩
      rcases right with ⟨rightGroup, rightOffset⟩
      simp only at hgroup
      subst rightGroup
      have hoffset : leftOffset.val = rightOffset.val :=
        calc
          leftOffset.val = partition.locateOffset
              (partition.member hvalid.bound leftGroup leftOffset) :=
            (hvalid.left_inv leftGroup leftOffset).2.symm
          _ = partition.locateOffset
              (partition.member hvalid.bound leftGroup rightOffset) := congrArg _ heq
          _ = rightOffset.val := (hvalid.left_inv leftGroup rightOffset).2
      exact Sigma.ext rfl (heq_of_eq (Fin.ext hoffset)), by
      intro u
      let offset : Fin (partition.group (partition.locateGroup u)).size :=
        ⟨partition.locateOffset u, hvalid.locateOffset_lt u⟩
      refine ⟨⟨partition.locateGroup u, offset⟩, ?_⟩
      apply Fin.ext
      exact hvalid.right_inv u⟩

/-- Reindexing a sum by a valid consecutive degree partition preserves its value. -/
theorem RhsDegreePartition.sum_equiv {S F G : ℕ} (partition : RhsDegreePartition F G)
    (feature : Fin F → RhsMarginalFeature S) (hvalid : partition.Valid feature)
    (f : Fin F → ℤ) :
    (∑ group, ∑ offset : Fin (partition.group group).size,
      f (partition.member hvalid.bound group offset)) = ∑ u, f u :=
  calc
    (∑ group, ∑ offset : Fin (partition.group group).size,
        f (partition.member hvalid.bound group offset)) =
        ∑ entry : Σ group, Fin (partition.group group).size,
          f (partition.member hvalid.bound entry.1 entry.2) :=
      (Fintype.sum_sigma' fun group offset ↦
        f (partition.member hvalid.bound group offset)).symm
    _ = ∑ u, f u := by
      apply Fintype.sum_equiv (partition.equiv feature hvalid)
      intro entry
      rfl

/-- Summing weights over fibers of a finite map and then over its targets is the same as summing
each source weight at its target, for a source ranging over an explicit finite set. -/
theorem sum_fiber_mul_finset {A B : Type} [Fintype B] [DecidableEq B]
    (source : Finset A) (locate : A → B) (weight : A → ℤ) (g : B → ℤ) :
    (∑ b, (∑ a ∈ source, if locate a = b then weight a else 0) * g b) =
      ∑ a ∈ source, weight a * g (locate a) := by
  simp_rw [Finset.sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun a ha ↦ ?_
  simp [eq_comm]

/-- A one-sided basis/erasure transition before equal feature keys are aggregated. -/
abbrev PreEpsCertificateExplicitDagInt.RhsTransition
    {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound) :=
  Σ i : Fin ct.N, {r // r ∈ insert 0 (ct.sig (ct.sigIndex i)).toFinset}

/-- Regard the erased exponent of a transition as an element of the parameter-derived finite
alphabet. -/
def PreEpsCertificateExplicitDagInt.rhsTransitionExponent
    {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (transition : ct.RhsTransition) : Fin (degreeBound + 1) :=
  ⟨transition.2.val, by
    rcases Finset.mem_insert.mp transition.2.property with hzero | hmem
    · omega
    · exact Nat.lt_succ_of_lt (ct.exponent_lt (ct.sigIndex transition.1) transition.2.val
        (Multiset.mem_toFinset.mp hmem))⟩

/-- Lift a rectangular basis/exponent lookup to the dependent transition type. -/
def PreEpsCertificateExplicitDagInt.rhsLocateTransition
    {K epsilonDenominator degreeBound F : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (locate : Fin ct.N → Fin (degreeBound + 1) → Fin F)
    (transition : ct.RhsTransition) : Fin F :=
  locate transition.1 (ct.rhsTransitionExponent transition)

/-- Computable list of all one-sided basis/erasure transitions. -/
def PreEpsCertificateExplicitDagInt.rhsTransitionList
    {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound) :
    List ct.RhsTransition :=
  ((List.finRange ct.N).sigma fun i ↦ (0 :: ct.sig (ct.sigIndex i)).dedup.attach).map
    fun transition ↦ ⟨transition.1, transition.2.val, by
      have hmem := List.mem_dedup.mp transition.2.property
      rcases List.mem_cons.mp hmem with hzero | hsignature
      · simp [hzero]
      · exact Finset.mem_insert.mpr (Or.inr (by simpa using hsignature))⟩

/-- Finset of all one-sided basis/erasure transitions. -/
def PreEpsCertificateExplicitDagInt.rhsTransitions
    {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound) :
    Finset ct.RhsTransition :=
  Finset.univ.sigma fun i ↦ (insert 0 (ct.sig (ct.sigIndex i)).toFinset).attach

/-- Coefficient and marginal-factor weight of one RHS transition. -/
def PreEpsCertificateExplicitDagInt.rhsTransitionWeight
    {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (transition : ct.RhsTransition) : ℤ :=
  ct.coeff transition.1 * tables.marginal (ct.a transition.1) transition.2.val

/-- Accumulate a finite list of weighted objects into an array of fibers in one pass. -/
def accumulateFiberWeights {A : Type} (F : ℕ) (source : List A)
    (locate : A → Fin F) (weight : A → ℤ) : Array ℤ :=
  source.foldl (fun values item ↦
    values.modify (locate item).val (· + weight item)) (Array.replicate F 0)

/-- Accumulate all RHS transition weights into their sparse feature fibers in one pass. -/
def PreEpsCertificateExplicitDagInt.rhsTransitionWeightArray
    {K epsilonDenominator degreeBound F : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (locate : ct.RhsTransition → Fin F) : Array ℤ :=
  accumulateFiberWeights F ct.rhsTransitionList locate (ct.rhsTransitionWeight tables)

/-- Signature and scalar exponents of one RHS transition. -/
def PreEpsCertificateExplicitDagInt.rhsTransitionKey
    {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (transition : ct.RhsTransition) : Fin ct.S × ℕ × ℕ :=
  (ct.erase (ct.sigIndex transition.1) transition.2.val,
    (ct.sig (ct.sigIndex transition.1)).sum - transition.2.val,
    ct.a transition.1 + transition.2.val + 1)

/-- A location map assigns every source transition to the sparse feature representing its key. -/
def RhsMarginalFeature.LocationCorrect
    {K epsilonDenominator degreeBound F : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (feature : Fin F → RhsMarginalFeature ct.S)
    (locate : ct.RhsTransition → Fin F) : Prop :=
  (∀ transition ∈ ct.rhsTransitions,
      (feature (locate transition)).signature = (ct.rhsTransitionKey transition).1 ∧
      (feature (locate transition)).residualDegree = (ct.rhsTransitionKey transition).2.1 ∧
      (feature (locate transition)).radialDegree = (ct.rhsTransitionKey transition).2.2) ∧
    ∀ u, (feature u).weight =
      ∑ transition ∈ ct.rhsTransitions, if locate transition = u then
        ct.rhsTransitionWeight tables transition else 0

/-- Key correctness for all erasures of one basis element. -/
@[reducible] def RhsMarginalFeature.KeyCorrectAt
    {K epsilonDenominator degreeBound F : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (feature : Fin F → RhsMarginalFeature ct.S)
    (locate : Fin ct.N → Fin (degreeBound + 1) → Fin F) (i : Fin ct.N) : Prop :=
  ∀ r : Fin (degreeBound + 1),
    if hr : r.val ∈ insert 0 (ct.sig (ct.sigIndex i)).toFinset then
      let transition : ct.RhsTransition := ⟨i, r.val, hr⟩
      (feature (ct.rhsLocateTransition locate transition)).signature =
          (ct.rhsTransitionKey transition).1 ∧
        (feature (ct.rhsLocateTransition locate transition)).residualDegree =
          (ct.rhsTransitionKey transition).2.1 ∧
        (feature (ct.rhsLocateTransition locate transition)).radialDegree =
          (ct.rhsTransitionKey transition).2.2
    else True

/-- Fiber-weight correctness for one stored RHS feature. -/
@[reducible] def RhsMarginalFeature.WeightCorrectAt
    {K epsilonDenominator degreeBound F : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (feature : Fin F → RhsMarginalFeature ct.S)
    (locate : Fin ct.N → Fin (degreeBound + 1) → Fin F) (u : Fin F) : Prop :=
  (feature u).weight = ∑ transition ∈ ct.rhsTransitions,
    if ct.rhsLocateTransition locate transition = u then
      ct.rhsTransitionWeight tables transition else 0

/-- One array equality certifies every RHS feature weight after a single transition pass. -/
@[reducible] def RhsMarginalFeature.WeightArrayCorrect
    {K epsilonDenominator degreeBound F : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (feature : Fin F → RhsMarginalFeature ct.S)
    (locate : Fin ct.N → Fin (degreeBound + 1) → Fin F) : Prop :=
  Array.ofFn (fun u ↦ (feature u).weight) =
    ct.rhsTransitionWeightArray tables (ct.rhsLocateTransition locate)

/-- Per-basis key checks and per-feature fiber checks assemble into the extensional RHS feature
correctness predicate. -/
theorem RhsMarginalFeature.locationCorrect_of_checks
    {K epsilonDenominator degreeBound F : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (feature : Fin F → RhsMarginalFeature ct.S)
    (locate : Fin ct.N → Fin (degreeBound + 1) → Fin F)
    (hkey : ∀ i, RhsMarginalFeature.KeyCorrectAt ct feature locate i)
    (hweight : ∀ u, RhsMarginalFeature.WeightCorrectAt ct tables feature locate u) :
    RhsMarginalFeature.LocationCorrect ct tables feature (ct.rhsLocateTransition locate) := by
  constructor
  · intro transition htransition
    have h := hkey transition.1 (ct.rhsTransitionExponent transition)
    have hr : (ct.rhsTransitionExponent transition).val ∈
        insert 0 (ct.sig (ct.sigIndex transition.1)).toFinset := by
      change transition.2.val ∈ insert 0 (ct.sig (ct.sigIndex transition.1)).toFinset
      exact transition.2.property
    rw [dif_pos hr] at h
    simpa only [PreEpsCertificateExplicitDagInt.rhsTransitionExponent] using h
  · exact hweight

/-- Apply a test function to every one-sided basis/erasure transition. -/
def PreEpsCertificateExplicitDagInt.rhsTransitionLinear
    {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (g : Fin ct.S → ℕ → ℕ → ℤ) : ℤ :=
  ∑ i, ct.coeff i * ∑ r ∈ insert 0 (ct.sig (ct.sigIndex i)).toFinset,
    tables.marginal (ct.a i) r *
      g (ct.erase (ct.sigIndex i) r) ((ct.sig (ct.sigIndex i)).sum - r)
        (ct.a i + r + 1)

/-- A sparse RHS feature family represents all one-sided basis/erasure transitions. -/
def RhsMarginalFeature.Correct
    {K epsilonDenominator degreeBound F : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (feature : Fin F → RhsMarginalFeature ct.S) : Prop :=
  ∀ g : Fin ct.S → ℕ → ℕ → ℤ,
    (∑ u, (feature u).weight * g (feature u).signature
      (feature u).residualDegree (feature u).radialDegree) =
      ct.rhsTransitionLinear tables g

/-- Correct feature locations and fiber weights certify the sparse RHS linearization. -/
theorem RhsMarginalFeature.correct_of_locationCorrect
    {K epsilonDenominator degreeBound F : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (feature : Fin F → RhsMarginalFeature ct.S)
    (locate : ct.RhsTransition → Fin F)
    (hlocate : RhsMarginalFeature.LocationCorrect ct tables feature locate) :
    RhsMarginalFeature.Correct ct tables feature := by
  intro g
  simp_rw [hlocate.2]
  rw [sum_fiber_mul_finset]
  calc
    (∑ transition ∈ ct.rhsTransitions, ct.rhsTransitionWeight tables transition *
        g (feature (locate transition)).signature
          (feature (locate transition)).residualDegree
          (feature (locate transition)).radialDegree) =
        ∑ transition ∈ ct.rhsTransitions, ct.rhsTransitionWeight tables transition *
          g (ct.rhsTransitionKey transition).1 (ct.rhsTransitionKey transition).2.1
            (ct.rhsTransitionKey transition).2.2 := by
      refine Finset.sum_congr rfl fun transition htransition ↦ ?_
      rw [(hlocate.1 transition htransition).1,
        (hlocate.1 transition htransition).2.1,
        (hlocate.1 transition htransition).2.2]
    _ = ct.rhsTransitionLinear tables g := by
      rw [PreEpsCertificateExplicitDagInt.rhsTransitionLinear]
      simp only [PreEpsCertificateExplicitDagInt.rhsTransitionWeight,
        PreEpsCertificateExplicitDagInt.rhsTransitionKey,
        PreEpsCertificateExplicitDagInt.rhsTransitions, Finset.sum_sigma]
      simp only [Finset.mul_sum]
      refine sum_congr rfl fun i hi ↦ ?_
      simpa only [add_assoc, add_comm, add_left_comm, mul_assoc] using
        (Finset.sum_attach (insert 0 (ct.sig (ct.sigIndex i)).toFinset) fun r ↦
          ct.coeff i * tables.marginal (ct.a i) r *
            g (ct.erase (ct.sigIndex i) r) ((ct.sig (ct.sigIndex i)).sum - r)
              (1 + ct.a i + r))

/-- Bilinear kernel between two aggregated marginal features. -/
def PreEpsCertificateExplicitDagInt.rhsFeatureKernel
    {K epsilonDenominator degreeBound : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (left right : RhsMarginalFeature ct.S) : ℤ :=
  tables.radial (K - 1 + (left.residualDegree + right.residualDegree))
      (left.radialDegree + right.radialDegree) *
    ct.momentPred left.signature right.signature

/-- Direct predecessor-moment transform of one fixed-degree marginal-feature group. -/
def PreEpsCertificateExplicitDagInt.rhsDegreeTransformDirect
    {K epsilonDenominator degreeBound F G : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (feature : Fin F → RhsMarginalFeature ct.S) (partition : RhsDegreePartition F G)
    (hvalid : partition.Valid feature) (group : Fin G) (target : Fin ct.S) : ℤ :=
  ∑ offset : Fin (partition.group group).size,
    let item := feature (partition.member hvalid.bound group offset)
    item.weight * ct.momentPred target item.signature

/-- One stored entry of the marginal-feature predecessor-moment transform is correct. -/
@[reducible] def RhsDegreeTransformCorrectAt
    {K epsilonDenominator degreeBound F G : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (feature : Fin F → RhsMarginalFeature ct.S) (partition : RhsDegreePartition F G)
    (hvalid : partition.Valid feature) (transform : Fin G → Fin ct.S → ℤ)
    (group : Fin G) (target : Fin ct.S) : Prop :=
  transform group target = ct.rhsDegreeTransformDirect feature partition hvalid group target

/-- Read a sparse stored RHS transform entry, falling back to its direct formula off support. -/
def PreEpsCertificateExplicitDagInt.rhsSparseTransformGet
    {K epsilonDenominator degreeBound F G T : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (feature : Fin F → RhsMarginalFeature ct.S) (partition : RhsDegreePartition F G)
    (hvalid : partition.Valid feature) (value : Fin T → ℤ)
    (index : LhsSparseTransformIndex G ct.S T) (group : Fin G) (target : Fin ct.S) : ℤ :=
  if h : (index.location group target).val = 0 then
    ct.rhsDegreeTransformDirect feature partition hvalid group target
  else value (index.entryOf group target h)

/-- One stored sparse RHS transform value agrees with its direct group sum. -/
@[reducible] def RhsSparseTransformValueCorrectAt
    {K epsilonDenominator degreeBound F G T : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (feature : Fin F → RhsMarginalFeature ct.S) (partition : RhsDegreePartition F G)
    (hvalid : partition.Valid feature) (value : Fin T → ℤ)
    (index : LhsSparseTransformIndex G ct.S T) (entry : Fin T) : Prop :=
  value entry = ct.rhsDegreeTransformDirect feature partition hvalid
    (index.entryGroup entry) (index.entryTarget entry)

/-- One bounded block of stored sparse RHS transform values is correct. -/
@[reducible] def RhsSparseTransformValueBlockCorrect
    {K epsilonDenominator degreeBound F G T blockSize : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (feature : Fin F → RhsMarginalFeature ct.S) (partition : RhsDegreePartition F G)
    (hvalid : partition.Valid feature) (value : Fin T → ℤ)
    (index : LhsSparseTransformIndex G ct.S T) (block : ℕ) : Prop :=
  ∀ offset : Fin blockSize,
    let entry := block * blockSize + offset.val
    if h : entry < T then
      RhsSparseTransformValueCorrectAt ct feature partition hvalid value index ⟨entry, h⟩
    else True

/-- A valid sparse index and correct stored values make every RHS transform lookup exact. -/
theorem PreEpsCertificateExplicitDagInt.rhsSparseTransformGet_correct
    {K epsilonDenominator degreeBound F G T : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (feature : Fin F → RhsMarginalFeature ct.S) (partition : RhsDegreePartition F G)
    (hvalid : partition.Valid feature) (value : Fin T → ℤ)
    (index : LhsSparseTransformIndex G ct.S T) (hindex : index.Valid)
    (hvalue : ∀ entry,
      RhsSparseTransformValueCorrectAt ct feature partition hvalid value index entry) :
    ∀ group target, RhsDegreeTransformCorrectAt ct feature partition hvalid
      (ct.rhsSparseTransformGet feature partition hvalid value index) group target := by
  intro group target
  rw [RhsDegreeTransformCorrectAt, PreEpsCertificateExplicitDagInt.rhsSparseTransformGet]
  split_ifs with hlocation
  · rfl
  · rw [hvalue]
    have hkey := hindex.right_inv group target
    rw [dif_neg hlocation] at hkey
    rw [hkey.1, hkey.2]

/-- Contract two fixed-degree RHS groups through the smaller signature support. -/
def PreEpsCertificateExplicitDagInt.rhsDegreeContraction
    {K epsilonDenominator degreeBound F G : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (feature : Fin F → RhsMarginalFeature ct.S) (partition : RhsDegreePartition F G)
    (hvalid : partition.Valid feature) (transform : Fin G → Fin ct.S → ℤ)
    (left right : Fin G) : ℤ :=
  if (partition.group left).size ≤ (partition.group right).size then
    ∑ offset : Fin (partition.group left).size,
      let item := feature (partition.member hvalid.bound left offset)
      item.weight * transform right item.signature
  else
    ∑ offset : Fin (partition.group right).size,
      let item := feature (partition.member hvalid.bound right offset)
      item.weight * transform left item.signature

/-- A correct RHS transform expands its sparse contraction into the full member square. -/
theorem PreEpsCertificateExplicitDagInt.rhsDegreeContraction_eq
    {K epsilonDenominator degreeBound F G : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (feature : Fin F → RhsMarginalFeature ct.S) (partition : RhsDegreePartition F G)
    (hvalid : partition.Valid feature) (transform : Fin G → Fin ct.S → ℤ)
    (htransform : ∀ group target,
      RhsDegreeTransformCorrectAt ct feature partition hvalid transform group target)
    (hmoment : ∀ i j, ct.momentPred i j = ct.momentPred j i) (left right : Fin G) :
    ct.rhsDegreeContraction feature partition hvalid transform left right =
      ∑ i : Fin (partition.group left).size,
        ∑ j : Fin (partition.group right).size,
          let leftFeature := feature (partition.member hvalid.bound left i)
          let rightFeature := feature (partition.member hvalid.bound right j)
          leftFeature.weight * rightFeature.weight *
            ct.momentPred leftFeature.signature rightFeature.signature := by
  rw [PreEpsCertificateExplicitDagInt.rhsDegreeContraction]
  by_cases hsize : (partition.group left).size ≤ (partition.group right).size
  · rw [if_pos hsize]
    refine sum_congr rfl fun i hi ↦ ?_
    dsimp only
    rw [htransform right, PreEpsCertificateExplicitDagInt.rhsDegreeTransformDirect,
      Finset.mul_sum]
    refine sum_congr rfl fun j hj ↦ ?_
    ring
  · rw [if_neg hsize]
    simp_rw [htransform left, PreEpsCertificateExplicitDagInt.rhsDegreeTransformDirect,
      Finset.mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun i hi ↦ ?_
    refine sum_congr rfl fun j hj ↦ ?_
    rw [hmoment]
    ring

/-- Moment-weight contraction between two groups having fixed degree coordinates. -/
def PreEpsCertificateExplicitDagInt.rhsDegreeGroupKernel
    {K epsilonDenominator degreeBound F G : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (feature : Fin F → RhsMarginalFeature ct.S) (partition : RhsDegreePartition F G)
    (hvalid : partition.Valid feature) (left right : Fin G) : ℤ :=
  ∑ i : Fin (partition.group left).size,
    ∑ j : Fin (partition.group right).size,
      let leftFeature := feature (partition.member hvalid.bound left i)
      let rightFeature := feature (partition.member hvalid.bound right j)
      leftFeature.weight * rightFeature.weight *
        ct.momentPred leftFeature.signature rightFeature.signature

/-- One pair of fixed-degree RHS groups, with the common radial factor taken outside. -/
def PreEpsCertificateExplicitDagInt.rhsDegreeGroupPair
    {K epsilonDenominator degreeBound F G : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (feature : Fin F → RhsMarginalFeature ct.S) (partition : RhsDegreePartition F G)
    (hvalid : partition.Valid feature) (left right : Fin G) : ℤ :=
  tables.radial
      (K - 1 + ((partition.group left).residualDegree +
        (partition.group right).residualDegree))
      ((partition.group left).radialDegree + (partition.group right).radialDegree) *
    ct.rhsDegreeGroupKernel feature partition hvalid left right

/-- One upper-triangular row of the RHS contraction by fixed degree coordinates. -/
def PreEpsCertificateExplicitDagInt.rhsDegreeGroupSymmetricRow
    {K epsilonDenominator degreeBound F G : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (feature : Fin F → RhsMarginalFeature ct.S) (partition : RhsDegreePartition F G)
    (hvalid : partition.Valid feature) (left : Fin G) : ℤ :=
  ∑ right, if left < right then 2 *
      ct.rhsDegreeGroupPair tables feature partition hvalid left right
    else if left = right then
      ct.rhsDegreeGroupPair tables feature partition hvalid left right
    else 0

/-- Pair two fixed-degree RHS groups through a reusable predecessor-moment transform. -/
def PreEpsCertificateExplicitDagInt.rhsDegreeGroupPairTransformed
    {K epsilonDenominator degreeBound F G : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (feature : Fin F → RhsMarginalFeature ct.S) (partition : RhsDegreePartition F G)
    (hvalid : partition.Valid feature) (transform : Fin G → Fin ct.S → ℤ)
    (left right : Fin G) : ℤ :=
  tables.radial
      (K - 1 + ((partition.group left).residualDegree +
        (partition.group right).residualDegree))
      ((partition.group left).radialDegree + (partition.group right).radialDegree) *
    ct.rhsDegreeContraction feature partition hvalid transform left right

/-- One upper-triangular RHS row evaluated through the reusable moment transform. -/
def PreEpsCertificateExplicitDagInt.rhsDegreeGroupSymmetricRowTransformed
    {K epsilonDenominator degreeBound F G : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (feature : Fin F → RhsMarginalFeature ct.S) (partition : RhsDegreePartition F G)
    (hvalid : partition.Valid feature) (transform : Fin G → Fin ct.S → ℤ)
    (left : Fin G) : ℤ :=
  ∑ right, if left < right then 2 *
      ct.rhsDegreeGroupPairTransformed tables feature partition hvalid transform left right
    else if left = right then
      ct.rhsDegreeGroupPairTransformed tables feature partition hvalid transform left right
    else 0

/-- A correct transform makes the transformed group pairing equal the direct group kernel. -/
theorem PreEpsCertificateExplicitDagInt.rhsDegreeGroupPairTransformed_eq
    {K epsilonDenominator degreeBound F G : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (feature : Fin F → RhsMarginalFeature ct.S) (partition : RhsDegreePartition F G)
    (hvalid : partition.Valid feature) (transform : Fin G → Fin ct.S → ℤ)
    (htransform : ∀ group target,
      RhsDegreeTransformCorrectAt ct feature partition hvalid transform group target)
    (hmoment : ∀ i j, ct.momentPred i j = ct.momentPred j i) (left right : Fin G) :
    ct.rhsDegreeGroupPairTransformed tables feature partition hvalid transform left right =
      ct.rhsDegreeGroupPair tables feature partition hvalid left right := by
  rw [PreEpsCertificateExplicitDagInt.rhsDegreeGroupPairTransformed,
    PreEpsCertificateExplicitDagInt.rhsDegreeGroupPair,
    ct.rhsDegreeContraction_eq feature partition hvalid transform htransform hmoment,
    PreEpsCertificateExplicitDagInt.rhsDegreeGroupKernel]

/-- The fixed-degree RHS group pairing is symmetric when the moment table is symmetric. -/
theorem PreEpsCertificateExplicitDagInt.rhsDegreeGroupPair_comm
    {K epsilonDenominator degreeBound F G : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (feature : Fin F → RhsMarginalFeature ct.S) (partition : RhsDegreePartition F G)
    (hvalid : partition.Valid feature)
    (hmoment : ∀ i j, ct.momentPred i j = ct.momentPred j i) (left right : Fin G) :
    ct.rhsDegreeGroupPair tables feature partition hvalid left right =
      ct.rhsDegreeGroupPair tables feature partition hvalid right left := by
  rw [PreEpsCertificateExplicitDagInt.rhsDegreeGroupPair,
    PreEpsCertificateExplicitDagInt.rhsDegreeGroupPair]
  have hradial : tables.radial
      (K - 1 + ((partition.group left).residualDegree +
        (partition.group right).residualDegree))
      ((partition.group left).radialDegree + (partition.group right).radialDegree) =
      tables.radial
        (K - 1 + ((partition.group right).residualDegree +
          (partition.group left).residualDegree))
        ((partition.group right).radialDegree + (partition.group left).radialDegree) := by
    congr 1 <;> omega
  rw [hradial]
  apply congrArg
  rw [PreEpsCertificateExplicitDagInt.rhsDegreeGroupKernel,
    PreEpsCertificateExplicitDagInt.rhsDegreeGroupKernel, sum_comm]
  refine sum_congr rfl fun i hi ↦ ?_
  refine sum_congr rfl fun j hj ↦ ?_
  dsimp only
  rw [hmoment]
  ring

/-- Full-overlap RHS evaluator: aggregate all equal one-sided marginal features before taking
their quadratic form. -/
def PreEpsCertificateExplicitDagInt.rhsFeatureSum
    {K epsilonDenominator degreeBound F : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (feature : Fin F → RhsMarginalFeature ct.S) : ℤ :=
  ∑ u, (feature u).weight * ∑ v, (feature v).weight *
    ct.rhsFeatureKernel tables (feature u) (feature v)

/-- Summing the fixed-degree RHS rows reproduces the fully aggregated feature evaluator. -/
theorem PreEpsCertificateExplicitDagInt.sum_rhsDegreeGroupSymmetricRow
    {K epsilonDenominator degreeBound F G : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (feature : Fin F → RhsMarginalFeature ct.S) (partition : RhsDegreePartition F G)
    (hvalid : partition.Valid feature)
    (hmoment : ∀ i j, ct.momentPred i j = ct.momentPred j i) :
    (∑ group, ct.rhsDegreeGroupSymmetricRow tables feature partition hvalid group) =
      ct.rhsFeatureSum tables feature := by
  simp only [PreEpsCertificateExplicitDagInt.rhsDegreeGroupSymmetricRow]
  change symmetricFinSquare
      (ct.rhsDegreeGroupPair tables feature partition hvalid) = _
  rw [symmetricFinSquare_eq _
    (ct.rhsDegreeGroupPair_comm tables feature partition hvalid hmoment)]
  let term (left right : Fin F) : ℤ :=
    (feature left).weight * (feature right).weight *
      ct.rhsFeatureKernel tables (feature left) (feature right)
  calc
    (∑ left, ∑ right, ct.rhsDegreeGroupPair tables feature partition hvalid left right) =
        ∑ left, ∑ i : Fin (partition.group left).size,
          ∑ right, ∑ j : Fin (partition.group right).size,
            term (partition.member hvalid.bound left i)
              (partition.member hvalid.bound right j) := by
      refine sum_congr rfl fun left hleft ↦ ?_
      simp only [PreEpsCertificateExplicitDagInt.rhsDegreeGroupPair,
        PreEpsCertificateExplicitDagInt.rhsDegreeGroupKernel, Finset.mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun i hi ↦ ?_
      refine sum_congr rfl fun right hright ↦ ?_
      refine sum_congr rfl fun j hj ↦ ?_
      have hleftKey := hvalid.key left i
      have hrightKey := hvalid.key right j
      rw [← hleftKey.1, ← hleftKey.2, ← hrightKey.1, ← hrightKey.2]
      simp only [term, PreEpsCertificateExplicitDagInt.rhsFeatureKernel]
      ring
    _ = ∑ left, ∑ i : Fin (partition.group left).size,
        ∑ right : Fin F, term (partition.member hvalid.bound left i) right := by
      refine sum_congr rfl fun left hleft ↦ ?_
      refine sum_congr rfl fun i hi ↦ ?_
      exact partition.sum_equiv feature hvalid
        (term (partition.member hvalid.bound left i))
    _ = ∑ left : Fin F, ∑ right : Fin F, term left right :=
      partition.sum_equiv feature hvalid (fun left ↦ ∑ right, term left right)
    _ = ct.rhsFeatureSum tables feature := by
      simp only [term, PreEpsCertificateExplicitDagInt.rhsFeatureSum, Finset.mul_sum,
        mul_assoc]

/-- Summing transformed fixed-degree RHS rows reproduces the fully aggregated evaluator. -/
theorem PreEpsCertificateExplicitDagInt.sum_rhsDegreeGroupSymmetricRowTransformed
    {K epsilonDenominator degreeBound F G : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (feature : Fin F → RhsMarginalFeature ct.S) (partition : RhsDegreePartition F G)
    (hvalid : partition.Valid feature) (transform : Fin G → Fin ct.S → ℤ)
    (htransform : ∀ group target,
      RhsDegreeTransformCorrectAt ct feature partition hvalid transform group target)
    (hmoment : ∀ i j, ct.momentPred i j = ct.momentPred j i) :
    (∑ group, ct.rhsDegreeGroupSymmetricRowTransformed tables feature partition hvalid
      transform group) = ct.rhsFeatureSum tables feature :=
  calc
    (∑ group, ct.rhsDegreeGroupSymmetricRowTransformed tables feature partition hvalid
        transform group) =
        ∑ group, ct.rhsDegreeGroupSymmetricRow tables feature partition hvalid group := by
      refine sum_congr rfl fun left hleft ↦ ?_
      simp only [PreEpsCertificateExplicitDagInt.rhsDegreeGroupSymmetricRowTransformed,
        PreEpsCertificateExplicitDagInt.rhsDegreeGroupSymmetricRow]
      refine sum_congr rfl fun right hright ↦ ?_
      split_ifs
      · rw [ct.rhsDegreeGroupPairTransformed_eq tables feature partition hvalid
          transform htransform hmoment]
      · rw [ct.rhsDegreeGroupPairTransformed_eq tables feature partition hvalid
          transform htransform hmoment]
      · rfl
    _ = ct.rhsFeatureSum tables feature :=
      ct.sum_rhsDegreeGroupSymmetricRow tables feature partition hvalid hmoment

/-- Correct marginal features transform the fully aggregated RHS evaluator back into the
unaggregated cached transition sum. -/
theorem PreEpsCertificateExplicitDagInt.rhsFeatureSum_eq_cached
    {K epsilonDenominator degreeBound F : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (feature : Fin F → RhsMarginalFeature ct.S)
    (hfeature : RhsMarginalFeature.Correct ct tables feature) :
    ct.rhsFeatureSum tables feature =
      ∑ i, ct.coeff i * ∑ j, ct.coeff j *
        ct.jPairWithTables tables (ct.a i) (ct.sigIndex i) (ct.a j) (ct.sigIndex j) := by
  let kernel : Fin ct.S → ℕ → ℕ → Fin ct.S → ℕ → ℕ → ℤ :=
    fun s₁ A₁ B₁ s₂ A₂ B₂ ↦
      tables.radial (K - 1 + (A₁ + A₂)) (B₁ + B₂) * ct.momentPred s₁ s₂
  calc
    ct.rhsFeatureSum tables feature =
        ∑ u, (feature u).weight * ∑ v, (feature v).weight *
          kernel (feature u).signature (feature u).residualDegree
            (feature u).radialDegree (feature v).signature
            (feature v).residualDegree (feature v).radialDegree := by
      rfl
    _ = ∑ u, (feature u).weight *
        ct.rhsTransitionLinear tables
          (kernel (feature u).signature (feature u).residualDegree
            (feature u).radialDegree) := by
      refine sum_congr rfl fun u hu ↦ ?_
      rw [hfeature (kernel (feature u).signature (feature u).residualDegree
        (feature u).radialDegree)]
    _ = ct.rhsTransitionLinear tables (fun s₁ A₁ B₁ ↦
        ct.rhsTransitionLinear tables (kernel s₁ A₁ B₁)) :=
      hfeature (fun s₁ A₁ B₁ ↦ ct.rhsTransitionLinear tables (kernel s₁ A₁ B₁))
    _ = ∑ i, ct.coeff i * ∑ j, ct.coeff j *
        ct.jPairWithTables tables (ct.a i) (ct.sigIndex i)
          (ct.a j) (ct.sigIndex j) := by
      simp only [PreEpsCertificateExplicitDagInt.rhsTransitionLinear,
        PreEpsCertificateExplicitDagInt.jPairWithTables,
        PreEpsCertificateExplicitDagInt.jPairCached, kernel]
      refine sum_congr rfl fun i hi ↦ ?_
      apply congrArg (ct.coeff i * ·)
      simp_rw [Finset.mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun j hj ↦ ?_
      push_cast
      rw [Finset.mul_sum]
      refine sum_congr rfl fun r₁ hr₁ ↦ ?_
      rw [Finset.mul_sum]
      refine sum_congr rfl fun r₂ hr₂ ↦ ?_
      ring

/-- Correct marginal features and factor tables reproduce the original RHS quadratic form. -/
theorem PreEpsCertificateExplicitDagInt.rhsFeatureSum_eq
    {K epsilonDenominator degreeBound F : ℕ}
    (ct : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound)
    (tables : EpsPairFactorTables K epsilonDenominator degreeBound)
    (feature : Fin F → RhsMarginalFeature ct.S)
    (hfeature : RhsMarginalFeature.Correct ct tables feature) (htables : tables.Correct) :
    ct.rhsFeatureSum tables feature = ∑ i, ∑ j, ct.rhsPairTerm i j := by
  rw [ct.rhsFeatureSum_eq_cached tables feature hfeature]
  refine sum_congr rfl fun i hi ↦ ?_
  simp only [PreEpsCertificateExplicitDagInt.rhsPairTerm]
  rw [Finset.mul_sum]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [ct.jPairWithTables_eq tables htables]
  ac_rfl

/-- A denominator-cleared certificate backed by externally stored labelled signatures and a
separately certified packed factorial-moment table. -/
structure EpsCertificateExplicitPrecomputedInt
    (K epsilonDenominator degreeBound : ℕ) : Type where
  /-- The externally stored certificate data, before its computational facts are proved. -/
  pre : PreEpsCertificateExplicitDagInt K epsilonDenominator degreeBound
  /-- Every packed moment-table entry agrees with the direct recurrence. -/
  pairValue_eq (p : Fin (pre.S * pre.S)) : pre.pairValue p = pre.directPairValue p
  /-- The lower packed component is smaller than the radix and hence is recovered by remainder. -/
  momentPred_lt (p : Fin (pre.S * pre.S)) :
    facMomentDirect (K - 1) (pre.sig p.divNat) (pre.sig p.modNat) < pre.momentRadix
  /-- Cleared-denominator witnessing inequality. -/
  cert : 4 * ∑ i, ∑ j, pre.lhsPairTerm i j <
    K * ∑ i, ∑ j, pre.rhsPairTerm i j

/-- Read a certified precomputed integer certificate as the explicit rational certificate. -/
def EpsCertificateExplicitPrecomputedInt.toExplicit
    {K epsilonDenominator degreeBound : ℕ}
    (ct : EpsCertificateExplicitPrecomputedInt K epsilonDenominator degreeBound) :
    EpsCertificateExplicit K (1 / epsilonDenominator) where
  N := ct.pre.N
  a := ct.pre.a
  α := fun i ↦ (ct.pre.sig (ct.pre.sigIndex i) : Multiset ℕ)
  coeff := fun i ↦ ct.pre.coeff i
  cert := by
    have hD : (0 : ℚ) < epsDenom K epsilonDenominator degreeBound := by
      rw [epsDenom]
      simp only [Nat.cast_mul, Nat.cast_pow]
      have hεQ : (0 : ℚ) < epsilonDenominator := by exact_mod_cast ct.pre.epsilon_pos
      exact mul_pos (mul_pos (pow_pos hεQ _) (by positivity)) (by positivity)
    have hI (i j : Fin ct.pre.N) :
        (ct.pre.iPair (ct.pre.a i) (ct.pre.sigIndex i)
          (ct.pre.a j) (ct.pre.sigIndex j) : ℚ) =
          epsDenom K epsilonDenominator degreeBound *
            IEpsExplicit K (1 / epsilonDenominator) (ct.pre.a i)
              (ct.pre.sig (ct.pre.sigIndex i) : Multiset ℕ) (ct.pre.a j)
              (ct.pre.sig (ct.pre.sigIndex j) : Multiset ℕ) := by
      rw [ct.pre.iPair_eq ct.pairValue_eq ct.momentPred_lt]
      exact IEpsExplicitNat_cast K epsilonDenominator degreeBound _ _ _ _
        ct.pre.epsilon_pos (by
          have hi := ct.pre.degree i
          have hj := ct.pre.degree j
          have hpair := ct.pre.degree_pair_bound
          simpa using (show (ct.pre.a i + ct.pre.a j) +
              ((ct.pre.sig (ct.pre.sigIndex i)).sum +
                (ct.pre.sig (ct.pre.sigIndex j)).sum) ≤ K by omega))
    have hJ (i j : Fin ct.pre.N) :
        (ct.pre.jPair (ct.pre.a i) (ct.pre.sigIndex i)
          (ct.pre.a j) (ct.pre.sigIndex j) : ℚ) =
          epsDenom K epsilonDenominator degreeBound *
            JEpsExplicit K (1 / epsilonDenominator) (ct.pre.a i)
              (ct.pre.sig (ct.pre.sigIndex i) : Multiset ℕ) (ct.pre.a j)
              (ct.pre.sig (ct.pre.sigIndex j) : Multiset ℕ) := by
      rw [ct.pre.jPair_eq ct.pairValue_eq ct.momentPred_lt]
      exact JEpsExplicitNat_cast K epsilonDenominator degreeBound _ _ _ _
        (by simpa using ct.pre.zeroFree (ct.pre.sigIndex i))
        (by simpa using ct.pre.zeroFree (ct.pre.sigIndex j))
        ct.pre.epsilon_pos ct.pre.degree_pos ct.pre.degree_pair_bound
        (by simpa using ct.pre.degree i) (by simpa using ct.pre.degree j)
    have hcert :
        (4 : ℚ) * ∑ i, ∑ j, (ct.pre.lhsPairTerm i j : ℚ) <
          (K : ℚ) * ∑ i, ∑ j, (ct.pre.rhsPairTerm i j : ℚ) := by
      exact_mod_cast ct.cert
    simp only [PreEpsCertificateExplicitDagInt.lhsPairTerm,
      PreEpsCertificateExplicitDagInt.rhsPairTerm, Int.cast_mul, Int.cast_natCast] at hcert
    simp_rw [hI, hJ] at hcert
    apply lt_of_mul_lt_mul_left _ hD.le
    simpa only [Nat.cast_ofNat, Int.cast_ofNat, Int.cast_mul, mul_sum, mul_assoc,
      mul_left_comm, mul_comm] using hcert

/-- A denominator-cleared certificate backed by a sparse factorial-moment DAG. -/
structure EpsCertificateExplicitDagInt
    (K epsilonDenominator degreeBound : ℕ) : Type where
  /-- Sparse factorial-moment DAG. -/
  dag : FacMomentDag K degreeBound
  /-- The epsilon denominator is positive. -/
  epsilon_pos : 0 < epsilonDenominator
  /-- The basis degree bound is positive. -/
  degree_pos : 0 < degreeBound
  /-- Two basis degrees fit within the sieve dimension. -/
  degree_pair_bound : 2 * degreeBound ≤ K
  /-- Number of basis elements. -/
  N : ℕ
  /-- Slack exponents. -/
  a : Fin N → ℕ
  /-- Indices of exponent signatures in the sparse DAG. -/
  sigIndex : Fin N → Fin dag.S
  /-- Integral coefficients. -/
  coeff : Fin N → ℤ
  /-- Every basis element has total degree at most `degreeBound`. -/
  degree (i : Fin N) : a i + (dag.sig (sigIndex i)).sum ≤ degreeBound
  /-- Cleared-denominator witnessing inequality. -/
  cert : 4 * ∑ i, coeff i * ∑ j, coeff j *
      IEpsDagInt K epsilonDenominator degreeBound dag
        (a i) (sigIndex i) (a j) (sigIndex j) <
    K * ∑ i, coeff i * ∑ j, coeff j *
      JEpsDagInt K epsilonDenominator degreeBound dag
        (a i) (sigIndex i) (a j) (sigIndex j)

/-- Read a sparse, cleared integer certificate as the explicit rational certificate. -/
def EpsCertificateExplicitDagInt.toExplicit {K epsilonDenominator degreeBound : ℕ}
    (ct : EpsCertificateExplicitDagInt K epsilonDenominator degreeBound) :
    EpsCertificateExplicit K (1 / epsilonDenominator) where
  N := ct.N
  a := ct.a
  α := fun i ↦ ct.dag.sig (ct.sigIndex i)
  coeff := fun i ↦ ct.coeff i
  cert := by
    have hD : (0 : ℚ) < epsDenom K epsilonDenominator degreeBound := by
      rw [epsDenom]
      simp only [Nat.cast_mul, Nat.cast_pow]
      have hεQ : (0 : ℚ) < epsilonDenominator := by exact_mod_cast ct.epsilon_pos
      exact mul_pos (mul_pos (pow_pos hεQ _) (by positivity)) (by positivity)
    have hI (i j : Fin ct.N) :
        (IEpsDagInt K epsilonDenominator degreeBound ct.dag
          (ct.a i) (ct.sigIndex i) (ct.a j) (ct.sigIndex j) : ℚ) =
          epsDenom K epsilonDenominator degreeBound *
            IEpsExplicit K (1 / epsilonDenominator) (ct.a i)
              (ct.dag.sig (ct.sigIndex i)) (ct.a j)
              (ct.dag.sig (ct.sigIndex j)) :=
      IEpsDagInt_cast K epsilonDenominator degreeBound ct.dag ct.epsilon_pos
        _ _ _ _ (by
          have hi := ct.degree i
          have hj := ct.degree j
          have hpair := ct.degree_pair_bound
          omega)
    have hJ (i j : Fin ct.N) :
        (JEpsDagInt K epsilonDenominator degreeBound ct.dag
          (ct.a i) (ct.sigIndex i) (ct.a j) (ct.sigIndex j) : ℚ) =
          epsDenom K epsilonDenominator degreeBound *
            JEpsExplicit K (1 / epsilonDenominator) (ct.a i)
              (ct.dag.sig (ct.sigIndex i)) (ct.a j)
              (ct.dag.sig (ct.sigIndex j)) :=
      JEpsDagInt_cast K epsilonDenominator degreeBound ct.dag ct.epsilon_pos
        ct.degree_pos ct.degree_pair_bound _ _ _ _ (ct.degree i) (ct.degree j)
    have hcert :
        (4 : ℚ) * ∑ i, (ct.coeff i : ℚ) * ∑ j, (ct.coeff j : ℚ) *
          (IEpsDagInt K epsilonDenominator degreeBound ct.dag
            (ct.a i) (ct.sigIndex i) (ct.a j) (ct.sigIndex j) : ℚ) <
        (K : ℚ) * ∑ i, (ct.coeff i : ℚ) * ∑ j, (ct.coeff j : ℚ) *
          (JEpsDagInt K epsilonDenominator degreeBound ct.dag
            (ct.a i) (ct.sigIndex i) (ct.a j) (ct.sigIndex j) : ℚ) := by
      exact_mod_cast ct.cert
    simp_rw [hI, hJ] at hcert
    apply lt_of_mul_lt_mul_left _ hD.le
    simpa only [Nat.cast_ofNat, Int.cast_ofNat, Int.cast_mul, mul_sum, mul_assoc,
      mul_left_comm, mul_comm] using hcert

/-- An integer, denominator-cleared certificate with independent parameters. -/
structure EpsCertificateExplicitInt (K epsilonDenominator degreeBound : ℕ) : Type where
  /-- Compressed factorial-moment table. -/
  table : FacMomentTable
  /-- The epsilon denominator is positive. -/
  epsilon_pos : 0 < epsilonDenominator
  /-- The basis degree bound is positive. -/
  degree_pos : 0 < degreeBound
  /-- Two basis degrees fit within the sieve dimension. -/
  degree_pair_bound : 2 * degreeBound ≤ K
  /-- The table covers the required dimensions. -/
  table_bound : K ≤ table.K
  /-- Number of basis elements. -/
  N : ℕ
  /-- Slack exponents. -/
  a : Fin N → ℕ
  /-- Indices of exponent signatures in the compressed table. -/
  sigIndex : Fin N → Fin table.S
  /-- Integral coefficients. -/
  coeff : Fin N → ℤ
  /-- Every basis element has total degree at most `degreeBound`. -/
  degree (i : Fin N) : a i + (table.sig (sigIndex i)).sum ≤ degreeBound
  /-- Cleared-denominator witnessing inequality. -/
  cert : 4 * ∑ i, coeff i * ∑ j, coeff j *
      IEpsTableInt K epsilonDenominator degreeBound table (a i) (sigIndex i) (a j) (sigIndex j) <
    K * ∑ i, coeff i * ∑ j, coeff j *
      JEpsTableInt K epsilonDenominator degreeBound table (a i) (sigIndex i) (a j) (sigIndex j)

/-- Read a cleared integer certificate as the explicit rational certificate. -/
def EpsCertificateExplicitInt.toExplicit {K epsilonDenominator degreeBound : ℕ}
    (ct : EpsCertificateExplicitInt K epsilonDenominator degreeBound) :
    EpsCertificateExplicit K (1 / epsilonDenominator) where
  N := ct.N
  a := ct.a
  α := fun i ↦ ct.table.sig (ct.sigIndex i)
  coeff := fun i ↦ ct.coeff i
  cert := by
    have hD : (0 : ℚ) < epsDenom K epsilonDenominator degreeBound := by
      rw [epsDenom]
      simp only [Nat.cast_mul, Nat.cast_pow]
      have hεQ : (0 : ℚ) < epsilonDenominator := by exact_mod_cast ct.epsilon_pos
      exact mul_pos (mul_pos (pow_pos hεQ _) (by positivity)) (by positivity)
    have hI (i j : Fin ct.N) :
        (IEpsTableInt K epsilonDenominator degreeBound ct.table
          (ct.a i) (ct.sigIndex i) (ct.a j) (ct.sigIndex j) : ℚ) =
          epsDenom K epsilonDenominator degreeBound *
            IEpsExplicit K (1 / epsilonDenominator) (ct.a i)
            (ct.table.sig (ct.sigIndex i)) (ct.a j) (ct.table.sig (ct.sigIndex j)) :=
      IEpsTableInt_cast K epsilonDenominator degreeBound ct.table ct.table_bound
        ct.epsilon_pos _ _ _ _ (by
          have hi := ct.degree i
          have hj := ct.degree j
          have hpair := ct.degree_pair_bound
          omega)
    have hJ (i j : Fin ct.N) :
        (JEpsTableInt K epsilonDenominator degreeBound ct.table
          (ct.a i) (ct.sigIndex i) (ct.a j) (ct.sigIndex j) : ℚ) =
          epsDenom K epsilonDenominator degreeBound *
            JEpsExplicit K (1 / epsilonDenominator) (ct.a i)
            (ct.table.sig (ct.sigIndex i)) (ct.a j) (ct.table.sig (ct.sigIndex j)) :=
      JEpsTableInt_cast K epsilonDenominator degreeBound ct.table ct.table_bound
        ct.epsilon_pos ct.degree_pos ct.degree_pair_bound _ _ _ _ (ct.degree i) (ct.degree j)
    have hcert :
        (4 : ℚ) * ∑ i, (ct.coeff i : ℚ) * ∑ j, (ct.coeff j : ℚ) *
          (IEpsTableInt K epsilonDenominator degreeBound ct.table
            (ct.a i) (ct.sigIndex i) (ct.a j) (ct.sigIndex j) : ℚ) <
        (K : ℚ) * ∑ i, (ct.coeff i : ℚ) * ∑ j, (ct.coeff j : ℚ) *
          (JEpsTableInt K epsilonDenominator degreeBound ct.table
            (ct.a i) (ct.sigIndex i) (ct.a j) (ct.sigIndex j) : ℚ) := by
      exact_mod_cast ct.cert
    simp_rw [hI, hJ] at hcert
    apply lt_of_mul_lt_mul_left _ hD.le
    simpa only [Nat.cast_ofNat, Int.cast_ofNat, Int.cast_mul, mul_sum, mul_assoc,
      mul_left_comm, mul_comm] using hcert


end PrimeGaps
