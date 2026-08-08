/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Moments.Direct.Spec
public import PrimeGapsCert.Gap246.Moments.Direct.StepEntryH


/-! # Soundness of the certificate data-table check

Characterizes the kernel fold `cert246Kernel.dataCheck`. `dataCheck_sig_sound` extracts, for every
signature row below `S`, the nibble ordering facts and the erase-slot facts (`RowFacts`),
indexing the used slots by `distinctCount`, the number of distinct-value starts among the
nibble positions. `dataCheck_label_sound` extracts, for every label below `n`, the
signature-index bound, the slack bound, and the identification of the label's `u` field
with twice the nibble sum of its signature. -/

@[expose] public section

open Finset

namespace PrimeGaps.Gap246

section dataCheckSound

open cert246Kernel
open cert246Data (sigField sigCount sigNib eraseAt slotField slotUsed slotPart2 slotTarget
  labelField labelA labelSignature labelDegree labelSign)

/-! ### Boolean and bitwise destructuring helpers -/

private theorem bool_rec_true {f t c : Bool} (h : (Bool.rec f t c : Bool) = true) :
    (c = true ∧ t = true) ∨ (c = false ∧ f = true) := by cases c <;> simp_all

private theorem bool_rec_false_true {t c : Bool} (h : (Bool.rec false t c : Bool) = true) :
    c = true ∧ t = true := by cases c <;> simp_all

private theorem land_mask16 (x : ℕ) : Nat.land x 65535 = x % 2 ^ 16 :=
  Nat.and_two_pow_sub_one_eq_mod x 16

private theorem shiftRight_pow (x k : ℕ) : Nat.shiftRight x k = x / 2 ^ k :=
  Nat.shiftRight_eq_div_pow x k

/-- Extend a property known from cursor `t + 1` onwards to the cursor `t` itself. -/
private theorem forall_of_succ {Q : ℕ → Prop} {t fuel : ℕ} (h0 : Q t)
    (ih : ∀ p, t + 1 ≤ p → p < t + 1 + fuel → Q p) :
    ∀ p, t ≤ p → p < t + (fuel + 1) → Q p := by grind

/-! ### Spec-side counting of distinct nibble values -/

/-- The number of positions `q < p` at which the nibble sequence of `enc` starts a new
distinct value: position `0`, or a nibble differing from its predecessor. -/
noncomputable def distinctCount (enc : ℕ) : ℕ → ℕ
  | 0 => 0
  | p + 1 =>
    distinctCount enc p + if p = 0 ∨ sigNib enc p ≠ sigNib enc (p - 1) then 1 else 0

/-- Erase slot `j` of row `g` matches nibble position `p` of the signature field `enc`:
used, carrying halved part `sigNib enc p`, and targeting an in-range signature whose field
is `enc` with position `p` erased. -/
structure SlotMatch (S sigEnc eraseEnc g enc j p : ℕ) : Prop where
  used : slotUsed (slotField eraseEnc g j) = true
  part2 : slotPart2 (slotField eraseEnc g j) = sigNib enc p
  tgt_lt : slotTarget (slotField eraseEnc g j) < S
  tgt_field : sigField sigEnc (slotTarget (slotField eraseEnc g j)) = eraseAt enc p

/-- The facts `cert246Kernel.dataCheck` establishes for signature row `g` with field `enc` and
part count `m`: a bounded part count, positive ascending nibbles below `m` and zero nibbles
from `m` to `maxNib`, the identity slot at `4`, and the erase slot `distinctCount enc p`
matching each distinct-value start `p`, the slots above `distinctCount enc m` being zero. -/
structure RowFacts (S maxNib sigEnc eraseEnc g enc m : ℕ) : Prop where
  count_le : m ≤ maxNib
  nib_pos : ∀ p < m, 0 < sigNib enc p
  nib_mono : ∀ p < m, 0 < p → sigNib enc (p - 1) ≤ sigNib enc p
  nib_zero : ∀ p, m ≤ p → p < maxNib → sigNib enc p = 0
  slot_id : slotField eraseEnc g 4 = Nat.succ (Nat.shiftLeft g 5)
  distinct_le : distinctCount enc m ≤ 4
  slot_zero : ∀ j, distinctCount enc m ≤ j → j < 4 → slotField eraseEnc g j = 0
  slot_match : ∀ p < m, (p = 0 ∨ sigNib enc p ≠ sigNib enc (p - 1)) →
    SlotMatch S sigEnc eraseEnc g enc (distinctCount enc p) p

/-! ### The fold, with fuel and state generalized -/

/-- The label loop of `dataCheck`, with the fuel and cursor generalized. -/
private noncomputable def labelFold (S aBound labelEnc uT : ℕ) (fuel i : ℕ) : Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool)
    (fun _ => true)
    (fun _ ihL i =>
      (fun fL =>
        Bool.rec (motive := fun _ => Bool) false
          (ihL (Nat.succ i))
          (Bool.and'
            (Bool.and' (Nat.blt (labelSignature fL) S)
              (Nat.beq (labelDegree fL)
                (Nat.land
                  (Nat.shiftRight uT (Nat.shiftLeft (labelSignature fL) (nat_lit 4)))
                  (nat_lit 65535))))
            (Nat.ble (Nat.add (labelA fL) (labelDegree fL)) aBound)))
        (labelField labelEnc i))
    fuel i

/-- The trailing-slot scan of `dataCheck`, with the continuation abstracted. -/
private noncomputable def trailFold (eraseEnc g : ℕ) (c : Bool) (fuel j : ℕ) : Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool)
    (fun _ => c)
    (fun _ ihJ j =>
      Bool.rec (motive := fun _ => Bool) false
        (ihJ (Nat.succ j))
        (Nat.beq (slotField eraseEnc g j) (nat_lit 0)))
    fuel j

/-- The nibble walk of `dataCheck` for row `g`, with the base continuation abstracted. -/
private noncomputable def walkFold (S sigEnc eraseEnc g enc m : ℕ) (B : ℕ → ℕ → Bool)
    (fuel t prev jSlot usum : ℕ) : Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → Bool)
    (fun _ _ jSlot usum => B jSlot usum)
    (fun _ ihT t prev jSlot usum =>
      (fun nib =>
        Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool) false
            (ihT (Nat.succ t) prev jSlot usum)
            (Nat.beq nib (nat_lit 0)))
          (Bool.rec (motive := fun _ => Bool) false
            (Bool.rec (motive := fun _ => Bool)
              (ihT (Nat.succ t) nib jSlot (Nat.add usum nib))
              ((fun fS =>
                Bool.rec (motive := fun _ => Bool) false
                  (ihT (Nat.succ t) nib (Nat.succ jSlot) (Nat.add usum nib))
                  (Bool.and'
                    (Bool.and' (slotUsed fS) (Nat.beq (slotPart2 fS) nib))
                    (Bool.and' (Nat.blt (slotTarget fS) S)
                      (Nat.beq (sigField sigEnc (slotTarget fS))
                        (eraseAt enc t)))))
                (slotField eraseEnc g jSlot))
              (Bool.or' (Nat.beq t (nat_lit 0))
                (Bool.not' (Nat.beq nib prev))))
            (Bool.and' (Nat.blt (nat_lit 0) nib) (Nat.ble prev nib)))
          (Nat.blt t m))
        (sigNib enc t))
    fuel t prev jSlot usum

/-- The signature loop of `dataCheck`, with the fuel and state generalized. -/
private noncomputable def outerFold (S n maxNib aBound sigEnc eraseEnc labelEnc : ℕ)
    (fuel s uT : ℕ) : Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool)
    (fun _ uT => labelFold S aBound labelEnc uT n (nat_lit 0))
    (fun _ ihS s uT =>
      Bool.rec (motive := fun _ => Bool) false
        (walkFold S sigEnc eraseEnc s (sigField sigEnc s) (sigCount (sigField sigEnc s))
          (fun jSlot usum =>
            trailFold eraseEnc s
              (Bool.rec (motive := fun _ => Bool) false
                (ihS (Nat.succ s)
                  (Nat.add uT
                    (Nat.shiftLeft (Nat.shiftLeft usum (nat_lit 1))
                      (Nat.shiftLeft s (nat_lit 4)))))
                (Bool.and' (Nat.ble jSlot (nat_lit 4))
                  (Nat.beq (slotField eraseEnc s (nat_lit 4))
                    (Nat.succ (Nat.shiftLeft s (nat_lit 5))))))
              (Nat.sub (nat_lit 4) jSlot) jSlot)
          maxNib (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0))
        (Nat.ble (sigCount (sigField sigEnc s)) maxNib))
    fuel s uT

/-! ### Definitional unfolding equations -/

private theorem dataCheck_eq_outerFold (S n maxNib aBound sigEnc eraseEnc labelEnc : ℕ) :
    dataCheck S n maxNib aBound sigEnc eraseEnc labelEnc =
      outerFold S n maxNib aBound sigEnc eraseEnc labelEnc S 0 0 := rfl

private theorem labelFold_succ (S aBound labelEnc uT fuel i : ℕ) :
    labelFold S aBound labelEnc uT (fuel + 1) i =
      Bool.rec (motive := fun _ => Bool) false
        (labelFold S aBound labelEnc uT fuel (i + 1))
        (Bool.and'
          (Bool.and' (Nat.blt (labelSignature (labelField labelEnc i)) S)
            (Nat.beq (labelDegree (labelField labelEnc i))
              (Nat.land
                (Nat.shiftRight uT (Nat.shiftLeft (labelSignature (labelField labelEnc i)) 4))
                65535)))
          (Nat.ble (labelA (labelField labelEnc i) + labelDegree (labelField labelEnc i))
            aBound)) := rfl

private theorem trailFold_succ (eraseEnc g : ℕ) (c : Bool) (fuel j : ℕ) :
    trailFold eraseEnc g c (fuel + 1) j =
      Bool.rec (motive := fun _ => Bool) false
        (trailFold eraseEnc g c fuel (j + 1))
        (Nat.beq (slotField eraseEnc g j) 0) := rfl

private theorem walkFold_succ (S sigEnc eraseEnc g enc m : ℕ) (B : ℕ → ℕ → Bool)
    (fuel t prev jSlot usum : ℕ) :
    walkFold S sigEnc eraseEnc g enc m B (fuel + 1) t prev jSlot usum =
      Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false
          (walkFold S sigEnc eraseEnc g enc m B fuel (t + 1) prev jSlot usum)
          (Nat.beq (sigNib enc t) 0))
        (Bool.rec (motive := fun _ => Bool) false
          (Bool.rec (motive := fun _ => Bool)
            (walkFold S sigEnc eraseEnc g enc m B fuel (t + 1) (sigNib enc t) jSlot
              (usum + sigNib enc t))
            (Bool.rec (motive := fun _ => Bool) false
              (walkFold S sigEnc eraseEnc g enc m B fuel (t + 1) (sigNib enc t) (jSlot + 1)
                (usum + sigNib enc t))
              (Bool.and'
                (Bool.and' (slotUsed (slotField eraseEnc g jSlot))
                  (Nat.beq (slotPart2 (slotField eraseEnc g jSlot)) (sigNib enc t)))
                (Bool.and' (Nat.blt (slotTarget (slotField eraseEnc g jSlot)) S)
                  (Nat.beq (sigField sigEnc (slotTarget (slotField eraseEnc g jSlot)))
                    (eraseAt enc t)))))
            (Bool.or' (Nat.beq t 0) (Bool.not' (Nat.beq (sigNib enc t) prev))))
          (Bool.and' (Nat.blt 0 (sigNib enc t)) (Nat.ble prev (sigNib enc t))))
        (Nat.blt t m) := rfl

private theorem outerFold_succ (S n maxNib aBound sigEnc eraseEnc labelEnc fuel s uT : ℕ) :
    outerFold S n maxNib aBound sigEnc eraseEnc labelEnc (fuel + 1) s uT =
      Bool.rec (motive := fun _ => Bool) false
        (walkFold S sigEnc eraseEnc s (sigField sigEnc s) (sigCount (sigField sigEnc s))
          (fun jSlot usum =>
            trailFold eraseEnc s
              (Bool.rec (motive := fun _ => Bool) false
                (outerFold S n maxNib aBound sigEnc eraseEnc labelEnc fuel (s + 1)
                  (uT + Nat.shiftLeft (Nat.shiftLeft usum 1) (Nat.shiftLeft s 4)))
                (Bool.and' (Nat.ble jSlot 4)
                  (Nat.beq (slotField eraseEnc s 4) (Nat.succ (Nat.shiftLeft s 5)))))
              (4 - jSlot) jSlot)
          maxNib 0 0 0 0)
        (Nat.ble (sigCount (sigField sigEnc s)) maxNib) := rfl

/-! ### Soundness of the individual loops -/

private theorem labelFold_sound {S aBound labelEnc uT : ℕ} :
    ∀ fuel i, labelFold S aBound labelEnc uT fuel i = true →
      ∀ j, i ≤ j → j < i + fuel →
        labelSignature (labelField labelEnc j) < S ∧
        labelDegree (labelField labelEnc j) =
          Nat.land
            (Nat.shiftRight uT (Nat.shiftLeft (labelSignature (labelField labelEnc j)) 4))
            65535 ∧
        labelA (labelField labelEnc j) + labelDegree (labelField labelEnc j) ≤ aBound := by
  intro fuel
  induction fuel with
  | zero => exact fun i _ j _ hj => absurd hj (by omega)
  | succ fuel ih =>
    intro i h
    rw [labelFold_succ] at h
    obtain ⟨hchk, h⟩ := bool_rec_false_true h
    simp only [Bool.and'_eq_and, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at hchk
    exact forall_of_succ ⟨hchk.1.1, hchk.1.2, hchk.2⟩ (ih (i + 1) h)

private theorem trailFold_sound {eraseEnc g : ℕ} {c : Bool} :
    ∀ fuel j, trailFold eraseEnc g c fuel j = true →
      (∀ i, j ≤ i → i < j + fuel → slotField eraseEnc g i = 0) ∧ c = true := by
  intro fuel
  induction fuel with
  | zero => exact fun j h => ⟨fun i _ hi => absurd hi (by omega), h⟩
  | succ fuel ih =>
    intro j h
    rw [trailFold_succ] at h
    obtain ⟨hz, h⟩ := bool_rec_false_true h
    exact ⟨forall_of_succ (Nat.eq_of_beq_eq_true hz) (ih (j + 1) h).1, (ih (j + 1) h).2⟩

/-- The facts the nibble walk of row `g` establishes at position `p`: below the part count
`m` the nibble is positive and at least its predecessor, from `m` on it vanishes, and each
distinct-value start is matched by erase slot `distinctCount enc p`. -/
private def NibFacts (S sigEnc eraseEnc g enc m p : ℕ) : Prop :=
  (p < m → 0 < sigNib enc p ∧ (0 < p → sigNib enc (p - 1) ≤ sigNib enc p)) ∧
  (m ≤ p → sigNib enc p = 0) ∧
  (p < m → (p = 0 ∨ sigNib enc p ≠ sigNib enc (p - 1)) →
    SlotMatch S sigEnc eraseEnc g enc (distinctCount enc p) p)

private theorem walkFold_sound {S sigEnc eraseEnc g enc m : ℕ} {B : ℕ → ℕ → Bool} :
    ∀ fuel t prev jSlot usum,
      walkFold S sigEnc eraseEnc g enc m B fuel t prev jSlot usum = true →
      (0 < t → t ≤ m → prev = sigNib enc (t - 1)) →
      jSlot = distinctCount enc (min t m) →
      usum = ∑ q ∈ Finset.range (min t m), sigNib enc q →
      (∀ p, t ≤ p → p < t + fuel → NibFacts S sigEnc eraseEnc g enc m p) ∧
      B (distinctCount enc (min (t + fuel) m))
        (∑ q ∈ Finset.range (min (t + fuel) m), sigNib enc q) = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro t prev jSlot usum h _ hj hu
    have hB : B jSlot usum = true := h
    subst hj hu
    exact ⟨fun p _ hp => absurd hp (by omega), by simpa using hB⟩
  | succ fuel ih =>
    intro t prev jSlot usum h hprev hj hu
    rw [walkFold_succ] at h
    rcases bool_rec_true h with ⟨hblt, h⟩ | ⟨hblt, h⟩
    · -- in-range position: `t < m`
      have ht : t < m := by simpa using hblt
      have hmin1 : min (t + 1) m = t + 1 := by omega
      have hjt : jSlot = distinctCount enc t := by rw [hj, Nat.min_eq_left ht.le]
      subst hjt
      obtain ⟨hcond, h⟩ := bool_rec_false_true h
      obtain ⟨hpos, hble⟩ : 0 < sigNib enc t ∧ prev ≤ sigNib enc t := by simpa using hcond
      have key : walkFold S sigEnc eraseEnc g enc m B fuel (t + 1) (sigNib enc t)
            (distinctCount enc (t + 1)) (usum + sigNib enc t) = true ∧
          ((t = 0 ∨ sigNib enc t ≠ sigNib enc (t - 1)) →
            SlotMatch S sigEnc eraseEnc g enc (distinctCount enc t) t) := by
        rcases bool_rec_true h with ⟨hor, h⟩ | ⟨hor, h⟩
        · -- a new distinct value starts at `t`
          obtain ⟨hslot, h⟩ := bool_rec_false_true h
          simp only [Bool.and'_eq_and, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hslot
          have hnew : t = 0 ∨ sigNib enc t ≠ sigNib enc (t - 1) := by
            rcases Nat.eq_zero_or_pos t with ht0 | htpos
            · exact Or.inl ht0
            rw [← hprev htpos ht.le]
            exact Or.inr fun hcon => by simp [hcon, Nat.ne_of_gt htpos] at hor
          simp only [distinctCount, if_pos hnew]
          exact ⟨h, fun _ => ⟨hslot.1.1, hslot.1.2, hslot.2.1, hslot.2.2⟩⟩
        · -- the value at `t` repeats the previous nibble
          have ht0 : t ≠ 0 := fun h0 => by simp [h0] at hor
          have heq : sigNib enc t = sigNib enc (t - 1) := by
            rw [← hprev (Nat.pos_of_ne_zero ht0) ht.le]
            by_contra hne
            simp [hne] at hor
          have hnotnew : ¬(t = 0 ∨ sigNib enc t ≠ sigNib enc (t - 1)) := by simp [ht0, heq]
          simp only [distinctCount, if_neg hnotnew, Nat.add_zero]
          exact ⟨h, fun hn => absurd hn hnotnew⟩
      obtain ⟨ih1, ih2⟩ := ih (t + 1) (sigNib enc t) _ (usum + sigNib enc t) key.1
        (fun _ _ => by simp) (by rw [hmin1])
        (by rw [hmin1, Finset.sum_range_succ, hu, Nat.min_eq_left ht.le])
      exact ⟨forall_of_succ ⟨fun _ => ⟨hpos, fun ht0 => by rwa [← hprev ht0 ht.le]⟩,
        fun hpm => absurd hpm (by omega), fun _ hpnew => key.2 hpnew⟩ ih1,
        by rwa [Nat.add_right_comm] at ih2⟩
    · -- out-of-range position: `m ≤ t`
      have hge : m ≤ t := Nat.le_of_not_lt (by simp [← Nat.blt_eq, hblt])
      obtain ⟨hz, h⟩ := bool_rec_false_true h
      have hminEq : min (t + 1) m = min t m := by omega
      obtain ⟨ih1, ih2⟩ := ih (t + 1) prev jSlot usum h (fun _ h2 => absurd h2 (by omega))
        (by rw [hminEq]; exact hj) (by rw [hminEq]; exact hu)
      exact ⟨forall_of_succ ⟨fun hpm => absurd hpm (by omega),
        fun _ => Nat.eq_of_beq_eq_true hz, fun hpm _ => absurd hpm (by omega)⟩ ih1,
        by rwa [Nat.add_right_comm] at ih2⟩

/-! ### The signature loop and the accumulated `u` table -/

private theorem shiftLeft_arith (u s : ℕ) :
    Nat.shiftLeft (Nat.shiftLeft u 1) (Nat.shiftLeft s 4) = 2 * u * 2 ^ (16 * s) := by
  simp [Nat.shiftLeft_eq, Nat.mul_comm, pow_mul, Nat.mul_assoc]

private theorem outerFold_sound {S n maxNib aBound sigEnc eraseEnc labelEnc : ℕ} :
    ∀ fuel s uT,
      outerFold S n maxNib aBound sigEnc eraseEnc labelEnc fuel s uT = true →
      (∀ g, s ≤ g → g < s + fuel →
        RowFacts S maxNib sigEnc eraseEnc g (sigField sigEnc g)
          (sigCount (sigField sigEnc g))) ∧
      labelFold S aBound labelEnc
        (uT + ∑ j ∈ Finset.range fuel,
          (2 * ∑ q ∈ Finset.range (sigCount (sigField sigEnc (s + j))),
            sigNib (sigField sigEnc (s + j)) q) * 2 ^ (16 * (s + j))) n 0 = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro s uT h
    have h0 : labelFold S aBound labelEnc uT n 0 = true := h
    exact ⟨fun g _ hg => absurd hg (by omega), by simpa using h0⟩
  | succ fuel ih =>
    intro s uT h
    rw [outerFold_succ] at h
    obtain ⟨hble, h⟩ := bool_rec_false_true h
    have hcount : sigCount (sigField sigEnc s) ≤ maxNib := by simpa using hble
    obtain ⟨hnib, hbase⟩ := walkFold_sound maxNib 0 0 0 0 h
      (by omega) (by simp [distinctCount]) (by simp)
    simp only [Nat.zero_add, min_eq_right hcount] at hnib hbase
    obtain ⟨hzeros, hcont⟩ := trailFold_sound _ _ hbase
    obtain ⟨hgate, hrec⟩ := bool_rec_false_true hcont
    simp only [Bool.and'_eq_and, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at hgate
    obtain ⟨ihrows, ihlab⟩ := ih (s + 1) _ hrec
    have hrow : RowFacts S maxNib sigEnc eraseEnc s (sigField sigEnc s)
        (sigCount (sigField sigEnc s)) :=
      { count_le := hcount
        nib_pos := fun p hp => ((hnib p (Nat.zero_le p) (by omega)).1 hp).1
        nib_mono := fun p hp => ((hnib p (Nat.zero_le p) (by omega)).1 hp).2
        nib_zero := fun p hp1 hp2 => (hnib p (Nat.zero_le p) hp2).2.1 hp1
        slot_id := hgate.2
        distinct_le := hgate.1
        slot_zero := fun j hj1 hj2 => hzeros j hj1 (by omega)
        slot_match := fun p hp => (hnib p (Nat.zero_le p) (by omega)).2.2 hp }
    refine ⟨forall_of_succ hrow ihrows, ?_⟩
    convert ihlab using 2
    rw [Finset.sum_range_succ', shiftLeft_arith]
    simp only [Nat.add_zero, Nat.add_succ, Nat.succ_add]
    omega

/-! ### Extraction from the packed 16-bit table -/

/-- Packing fields below `2 ^ 16` into 16-bit lanes stays below `2 ^ (16 * K)`, and masking
lane `σ` out of the packed value recovers the field `c σ`. -/
private theorem sum_fields (c : ℕ → ℕ) :
    ∀ K, (∀ g, g < K → c g < 2 ^ 16) →
      (∑ g ∈ Finset.range K, c g * 2 ^ (16 * g)) < 2 ^ (16 * K) ∧
      ∀ σ, σ < K →
        Nat.land (Nat.shiftRight (∑ g ∈ Finset.range K, c g * 2 ^ (16 * g)) (16 * σ)) 65535 =
          c σ := by
  intro K
  induction K with
  | zero => exact fun _ => ⟨by simp, fun σ hσ => absurd hσ (Nat.not_lt_zero σ)⟩
  | succ K ihK =>
    intro hc
    obtain ⟨hbound, hex⟩ := ihK fun g hg => hc g (by omega)
    refine ⟨?_, fun σ hσ => ?_⟩
    · calc ∑ g ∈ Finset.range (K + 1), c g * 2 ^ (16 * g)
          < (c K + 1) * 2 ^ (16 * K) := by
            rw [Finset.sum_range_succ, Nat.add_mul, Nat.one_mul]
            omega
        _ ≤ 2 ^ 16 * 2 ^ (16 * K) := Nat.mul_le_mul_right _ (hc K (by omega))
        _ = 2 ^ (16 * (K + 1)) := by rw [← pow_add, Nat.mul_add, Nat.mul_one, Nat.add_comm]
    · rw [land_mask16, shiftRight_pow, Finset.sum_range_succ]
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hσ) with hlt | rfl
      · have hprev := hex σ hlt
        rw [land_mask16, shiftRight_pow] at hprev
        have hsplit : c K * 2 ^ (16 * K) =
            c K * 2 ^ (16 * (K - σ - 1)) * 2 ^ 16 * 2 ^ (16 * σ) := by
          rw [Nat.mul_assoc, Nat.mul_assoc, ← pow_add, ← pow_add,
            (by omega : 16 * (K - σ - 1) + (16 + 16 * σ) = 16 * K)]
        rw [hsplit, Nat.add_mul_div_right _ _ (Nat.two_pow_pos (16 * σ)),
          Nat.add_mul_mod_self_right]
        exact hprev
      · rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos (16 * σ)), Nat.div_eq_of_lt hbound,
          Nat.zero_add, Nat.mod_eq_of_lt (hc σ (by omega))]

/-! ### The two soundness theorems -/

/-- Soundness of phase A of `cert246Kernel.dataCheck`: every signature row below `S` satisfies
`RowFacts` for its field and part count. -/
theorem dataCheck_sig_sound {S n maxNib aBound sigEnc eraseEnc labelEnc : ℕ}
    (h : dataCheck S n maxNib aBound sigEnc eraseEnc labelEnc = true) :
    ∀ g < S, RowFacts S maxNib sigEnc eraseEnc g (sigField sigEnc g)
      (sigCount (sigField sigEnc g)) := by
  rw [dataCheck_eq_outerFold] at h
  exact fun g hg => (outerFold_sound S 0 0 h).1 g (Nat.zero_le g) (by omega)

/-- Soundness of phase B of `cert246Kernel.dataCheck`: every label below `n` has an in-range
signature index, a `u` field equal to twice the nibble sum of its signature, and slack
plus `u` at most `aBound`. -/
theorem dataCheck_label_sound {S n maxNib aBound sigEnc eraseEnc labelEnc : ℕ}
    (hmax : maxNib ≤ 12) (h : dataCheck S n maxNib aBound sigEnc eraseEnc labelEnc = true) :
    ∀ i < n,
      labelSignature (labelField labelEnc i) < S ∧
      labelDegree (labelField labelEnc i) =
        2 * ∑ p ∈ Finset.range
            (sigCount (sigField sigEnc (labelSignature (labelField labelEnc i)))),
          sigNib (sigField sigEnc (labelSignature (labelField labelEnc i))) p ∧
      labelA (labelField labelEnc i) + labelDegree (labelField labelEnc i) ≤ aBound := by
  intro i hi
  have hrows := dataCheck_sig_sound h
  rw [dataCheck_eq_outerFold] at h
  obtain ⟨_, hlab⟩ := outerFold_sound S 0 0 h
  simp only [Nat.zero_add] at hlab
  obtain ⟨hσ, hU, hA⟩ := labelFold_sound n 0 hlab i (Nat.zero_le i) (by omega)
  refine ⟨hσ, ?_, hA⟩
  have hsh : Nat.shiftLeft (labelSignature (labelField labelEnc i)) 4 =
      16 * labelSignature (labelField labelEnc i) := by simp [Nat.shiftLeft_eq, Nat.mul_comm]
  rw [hU, hsh]
  refine (sum_fields _ S fun g hg => ?_).2 _ hσ
  have hsum : (∑ q ∈ Finset.range (sigCount (sigField sigEnc g)),
      sigNib (sigField sigEnc g) q) ≤ sigCount (sigField sigEnc g) * 15 := by
    simpa using Finset.sum_le_card_nsmul (Finset.range (sigCount (sigField sigEnc g)))
      (fun q => sigNib (sigField sigEnc g) q) 15 fun q _ => Nat.and_le_right
  have hm := (hrows g hg).count_le
  omega

end dataCheckSound

end PrimeGaps.Gap246
