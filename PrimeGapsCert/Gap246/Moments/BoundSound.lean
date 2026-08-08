/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Moments.ResultSound

/-! # Soundness of predecessor-moment bound checks -/

@[expose] public section

namespace PrimeGaps.Gap246

private theorem gatedScan_sound (used : ℕ → Bool) (value : ℕ → ℕ) :
    ∀ count cursor accumulator,
      Nat.rec
        (fun _ accumulator' ↦ accumulator')
        (fun _ inductionHypothesis cursor' accumulator' ↦
          inductionHypothesis cursor'.succ
            (Bool.rec accumulator' (accumulator' + value cursor') (used cursor')))
        count cursor accumulator =
      accumulator + ∑ i ∈ Finset.range count,
        if used (cursor + i) = true then value (cursor + i) else 0
  | 0, _, _ => by simp
  | count + 1, cursor, accumulator => by
      dsimp only
      rw [gatedScan_sound used value count cursor.succ
        (Bool.rec accumulator (accumulator + value cursor) (used cursor)),
        sum_range_head (fun i ↦ if used i = true then value i else 0) cursor count]
      cases used cursor <;> simp
      omega

private theorem gatedScan_congr (used : ℕ → Bool) (value₁ value₂ : ℕ → ℕ) :
    ∀ count cursor accumulator, (∀ i < count, value₁ (cursor + i) = value₂ (cursor + i)) →
      Nat.rec (motive := fun _ ↦ ℕ → ℕ → ℕ)
        (fun _ accumulator' ↦ accumulator')
        (fun _ inductionHypothesis cursor' accumulator' ↦
          inductionHypothesis cursor'.succ
            (Bool.rec accumulator' (Nat.add accumulator' (value₁ cursor')) (used cursor')))
        count cursor accumulator =
      Nat.rec (motive := fun _ ↦ ℕ → ℕ → ℕ)
        (fun _ accumulator' ↦ accumulator')
        (fun _ inductionHypothesis cursor' accumulator' ↦
          inductionHypothesis cursor'.succ
            (Bool.rec accumulator' (Nat.add accumulator' (value₂ cursor')) (used cursor')))
        count cursor accumulator := by
  intro count
  induction count with
  | zero => intros; rfl
  | succ count inductionHypothesis =>
      intro cursor accumulator hvalues
      dsimp only
      rw [show value₁ cursor = value₂ cursor by simpa using hvalues 0 (Nat.succ_pos count)]
      refine inductionHypothesis cursor.succ _ fun i hi ↦ ?_
      have hshift := hvalues (i + 1) (by omega)
      rwa [(by omega : cursor + (i + 1) = cursor.succ + i)] at hshift

/-- The split-level single-dimension reconstruction is a finite gated sum. -/
theorem nilMomentValueLevels_eq_sum (dimension maxLevel sigEnc : ℕ)
    (shifts pmasks widths masks : Lean.RArray ℕ) (trees : Lean.RArray (Lean.RArray ℕ)) (s t : ℕ) :
    cert246Data.nilMomentValueLevels dimension maxLevel sigEnc
        shifts pmasks widths masks trees s t =
      let count := cert246Data.sigCount (cert246Data.sigField sigEnc s) +
        cert246Data.sigCount (cert246Data.sigField sigEnc t)
      ∑ level ∈ Finset.range (Nat.min count maxLevel + 1),
        if count ≤ 2 * level then
          cert246Data.nilLevelAt shifts pmasks widths masks trees level
              (cert246Data.triIdx s t) * dimension.choose level
        else 0 := by
  unfold cert246Data.nilMomentValueLevels
  let count := Nat.add
    (cert246Data.sigCount (cert246Data.sigField sigEnc s))
    (cert246Data.sigCount (cert246Data.sigField sigEnc t))
  let value : ℕ → ℕ := fun level ↦
    cert246Data.nilLevelAt shifts pmasks widths masks trees level
        (cert246Data.triIdx s t) * dimension.choose level
  let used : ℕ → Bool := fun level ↦ Nat.ble count (2 * level)
  calc
    Nat.rec
        (fun _ accumulator ↦ accumulator)
        (fun _ inductionHypothesis level accumulator ↦
          inductionHypothesis level.succ
            (Bool.rec accumulator (accumulator + value level) (used level)))
        (Nat.min count maxLevel + 1) 0 0 =
      ∑ level ∈ Finset.range (Nat.min count maxLevel + 1),
        if used level = true then value level else 0 := by
      simpa only [Nat.zero_add] using
        gatedScan_sound used value (Nat.min count maxLevel + 1) 0 0
    _ = ∑ level ∈ Finset.range (Nat.min count maxLevel + 1),
        if count ≤ 2 * level then value level else 0 :=
      Finset.sum_congr rfl fun level _ ↦ by simp only [used, Nat.ble_eq]
    _ = _ := rfl

/-- A sound independently packed ladder reconstructs one factorial moment. -/
theorem nilMomentValueLevels_sound
    {dimension maxLevel sigEnc : ℕ} {shifts pmasks widths masks : Lean.RArray ℕ}
    {trees : Lean.RArray (Lean.RArray ℕ)} {s t : ℕ}
    (hcount : cert246Data.sigCount (cert246Data.sigField sigEnc s) +
        cert246Data.sigCount (cert246Data.sigField sigEnc t) =
      (sigOf sigEnc s).card + (sigOf sigEnc t).card)
    (hmax : (sigOf sigEnc s).card + (sigOf sigEnc t).card ≤ maxLevel)
    (hdimension : (sigOf sigEnc s).card + (sigOf sigEnc t).card ≤ dimension)
    (hlookup : ∀ level ≤ (sigOf sigEnc s).card + (sigOf sigEnc t).card,
      Bool.rec (motive := fun _ ↦ Nat) 0
        (cert246Data.nilLevelAt shifts pmasks widths masks trees level
          (cert246Data.triIdx s t))
        (cert246Data.nilActive level
          (cert246Data.sigCount (cert246Data.sigField sigEnc s) +
            cert246Data.sigCount (cert246Data.sigField sigEnc t))) =
        nilMoment level (sigOf sigEnc s) (sigOf sigEnc t))
    (hzeroS : (0 : ℕ) ∉ sigOf sigEnc s) (hzeroT : (0 : ℕ) ∉ sigOf sigEnc t) :
    cert246Data.nilMomentValueLevels dimension maxLevel sigEnc
        shifts pmasks widths masks trees s t =
      facMomentNat dimension (sigOf sigEnc s) (sigOf sigEnc t) := by
  let count := (sigOf sigEnc s).card + (sigOf sigEnc t).card
  rw [nilMomentValueLevels_eq_sum, hcount]
  dsimp only
  rw [Nat.min_eq_min, Nat.min_eq_left hmax]
  have hterms :
      (∑ level ∈ Finset.range (count + 1),
        if count ≤ 2 * level then
          cert246Data.nilLevelAt shifts pmasks widths masks trees level
              (cert246Data.triIdx s t) * dimension.choose level
        else 0) =
      ∑ level ∈ Finset.range (count + 1),
        nilMoment level (sigOf sigEnc s) (sigOf sigEnc t) * dimension.choose level := by
    refine Finset.sum_congr rfl fun level hlevel ↦ ?_
    have hlevelCount : level ≤ count := Nat.lt_succ_iff.mp (Finset.mem_range.mp hlevel)
    split_ifs with hactive
    · have hsupport : cert246Data.nilActive level
          (cert246Data.sigCount (cert246Data.sigField sigEnc s) +
            cert246Data.sigCount (cert246Data.sigField sigEnc t)) = true := by
        unfold cert246Data.nilActive
        rw [Nat.ble_eq_true_of_le (by rw [hcount]; exact hlevelCount),
          Nat.ble_eq_true_of_le (by rw [hcount]; exact hactive)]
        rfl
      have hvalue := hlookup level hlevelCount
      rw [hsupport] at hvalue
      change cert246Data.nilLevelAt shifts pmasks widths masks trees level
          (cert246Data.triIdx s t) =
        nilMoment level (sigOf sigEnc s) (sigOf sigEnc t) at hvalue
      rw [hvalue]
    · rw [nilMoment_eq_zero_of_count_gt level (sigOf sigEnc s) (sigOf sigEnc t)
          (by simpa only [count] using Nat.lt_of_not_ge hactive), Nat.zero_mul]
  rw [hterms, facMomentNat_eq_binomialMoment hzeroS hzeroT dimension,
    binomialMoment_eq_sum_card dimension _ _ hdimension]
  exact Finset.sum_congr rfl fun level _ ↦ Nat.mul_comm _ _

private theorem levelScan_sound (check : ℕ → Bool) :
    ∀ fuel cursor,
      Nat.rec (motive := fun _ ↦ ℕ → Bool)
        (fun _ ↦ true)
        (fun _ inductionHypothesis level ↦
          Bool.rec false (inductionHypothesis (Nat.succ level)) (check level))
        fuel cursor = true →
      ∀ level, cursor ≤ level → level < cursor + fuel → check level = true := by
  intro fuel
  induction fuel with
  | zero => exact fun _ _ level _ hupper ↦ absurd hupper (by omega)
  | succ fuel inductionHypothesis =>
      intro cursor hscan level hlower hupper
      dsimp only at hscan
      rcases hcheck : check cursor with _ | _
      · simp [hcheck] at hscan
      · rcases Nat.eq_or_lt_of_le hlower with rfl | hlower'
        · exact hcheck
        · rw [hcheck] at hscan
          exact inductionHypothesis cursor.succ hscan level hlower' (by omega)

/-- The primitive reference builder of the coefficient check computes `Nat.choose`. -/
theorem binomial_eq_choose (dimension level : ℕ) :
    cert246Data.binomial dimension level = Nat.choose dimension level := by
  induction level with
  | zero => exact (Nat.choose_zero_right dimension).symm
  | succ level inductionHypothesis =>
      change cert246Data.binomial dimension level * (dimension - level) / (level + 1) = _
      rw [inductionHypothesis, ← Nat.choose_succ_right_eq,
        Nat.mul_div_cancel _ (Nat.succ_pos level)]

/-- Every level of a checked coefficient table holds both binomial coefficients. -/
theorem coeffCheck_sound {dimension maxLevel coeffT : ℕ}
    (h : cert246Data.coeffCheck dimension maxLevel coeffT = true) (level : ℕ)
    (hlevel : level ≤ maxLevel) :
    Nat.land (Nat.land (Nat.shiftRight coeffT (Nat.shiftLeft level 7))
          340282366920938463463374607431768211455) 18446744073709551615 =
        Nat.choose (Nat.sub dimension 1) level ∧
      Nat.shiftRight (Nat.land (Nat.shiftRight coeffT (Nat.shiftLeft level 7))
        340282366920938463463374607431768211455) 64 = Nat.choose dimension level := by
  simpa only [Bool.and_eq_true, Nat.beq_eq, binomial_eq_choose] using levelScan_sound
    (fun level ↦ Bool.and
      (Nat.beq (Nat.land (Nat.land (Nat.shiftRight coeffT (Nat.shiftLeft level 7))
        340282366920938463463374607431768211455) 18446744073709551615)
        (cert246Data.binomial (Nat.sub dimension 1) level))
      (Nat.beq (Nat.shiftRight (Nat.land (Nat.shiftRight coeffT (Nat.shiftLeft level 7))
        340282366920938463463374607431768211455) 64)
        (cert246Data.binomial dimension level)))
    (Nat.succ maxLevel) 0 h level (Nat.zero_le level) (by omega)

private theorem bleBranch_eq_min (count maxLevel : ℕ) :
    Bool.rec (motive := fun _ ↦ ℕ) maxLevel count (Nat.ble count maxLevel) =
      Nat.min count maxLevel := by
  rcases hble : Nat.ble count maxLevel with _ | _
  · have hgt : ¬count ≤ maxLevel := by
      simpa only [Bool.eq_false_iff, ne_eq, Nat.ble_eq] using hble
    rw [Nat.min_eq_min, min_eq_right (by omega : maxLevel ≤ count)]
  · rw [Nat.min_eq_min, min_eq_left (Nat.le_of_ble_eq_true hble)]

private theorem pairedRec_fst (used : ℕ → Bool) (first second : ℕ → ℕ) :
    ∀ count cursor firstAccumulator secondAccumulator,
      (Nat.rec (motive := fun _ ↦ ℕ → ℕ × ℕ → ℕ × ℕ)
        (fun _ state ↦ state)
        (fun _ inductionHypothesis cursor' state ↦
          inductionHypothesis cursor'.succ
            (Bool.rec state
              (Nat.add state.1 (first cursor'), Nat.add state.2 (second cursor'))
              (used cursor')))
        count cursor (firstAccumulator, secondAccumulator)).1 =
      Nat.rec (motive := fun _ ↦ ℕ → ℕ → ℕ)
        (fun _ accumulator ↦ accumulator)
        (fun _ inductionHypothesis cursor' accumulator ↦
          inductionHypothesis cursor'.succ
            (Bool.rec accumulator (Nat.add accumulator (first cursor')) (used cursor')))
        count cursor firstAccumulator := by
  intro count
  induction count with
  | zero => intros; rfl
  | succ count inductionHypothesis =>
      intro cursor firstAccumulator secondAccumulator
      dsimp only
      cases used cursor <;> exact inductionHypothesis _ _ _

private theorem pairedRec_snd (used : ℕ → Bool) (first second : ℕ → ℕ) :
    ∀ count cursor firstAccumulator secondAccumulator,
      (Nat.rec (motive := fun _ ↦ ℕ → ℕ × ℕ → ℕ × ℕ)
        (fun _ state ↦ state)
        (fun _ inductionHypothesis cursor' state ↦
          inductionHypothesis cursor'.succ
            (Bool.rec state
              (Nat.add state.1 (first cursor'), Nat.add state.2 (second cursor'))
              (used cursor')))
        count cursor (firstAccumulator, secondAccumulator)).2 =
      Nat.rec (motive := fun _ ↦ ℕ → ℕ → ℕ)
        (fun _ accumulator ↦ accumulator)
        (fun _ inductionHypothesis cursor' accumulator ↦
          inductionHypothesis cursor'.succ
            (Bool.rec accumulator (Nat.add accumulator (second cursor')) (used cursor')))
        count cursor secondAccumulator := by
  intro count
  induction count with
  | zero => intros; rfl
  | succ count inductionHypothesis =>
      intro cursor firstAccumulator secondAccumulator
      dsimp only
      cases used cursor <;> exact inductionHypothesis _ _ _

/-- The split-level fused reconstruction has the same packed component as its pair fold. -/
theorem nilMomentPairPredLevels_fst {outWidth dimension coeffT maxLevel sigEnc : ℕ}
    {shifts pmasks widths masks : Lean.RArray ℕ} {trees : Lean.RArray (Lean.RArray ℕ)} {s t : ℕ}
    (hcoeff : cert246Data.coeffCheck dimension maxLevel coeffT = true) :
    (cert246Data.nilMomentPairPredLevels outWidth coeffT maxLevel sigEnc
      shifts pmasks widths masks trees s t).1 =
      cert246Data.nilMomentPairLevels outWidth dimension maxLevel sigEnc
        shifts pmasks widths masks trees s t := by
  unfold cert246Data.nilMomentPairPredLevels cert246Data.nilMomentPairLevels
  let count := Nat.add
    (cert246Data.sigCount (cert246Data.sigField sigEnc s))
    (cert246Data.sigCount (cert246Data.sigField sigEnc t))
  let entry : ℕ → ℕ := fun level ↦
    cert246Data.nilLevelAt shifts pmasks widths masks trees level (cert246Data.triIdx s t)
  let low : ℕ → ℕ := fun level ↦
    Nat.land (Nat.land (Nat.shiftRight coeffT (Nat.shiftLeft level 7))
      340282366920938463463374607431768211455) 18446744073709551615
  let high : ℕ → ℕ := fun level ↦
    Nat.shiftRight (Nat.land (Nat.shiftRight coeffT (Nat.shiftLeft level 7))
      340282366920938463463374607431768211455) 64
  let tableFirst : ℕ → ℕ := fun level ↦
    Nat.mul (entry level) (Nat.add (low level) (Nat.shiftLeft (high level) outWidth))
  let chooseFirst : ℕ → ℕ := fun level ↦
    Nat.mul (entry level) (Nat.add (Nat.choose (Nat.sub dimension 1) level)
      (Nat.shiftLeft (Nat.choose dimension level) outWidth))
  let second : ℕ → ℕ := fun level ↦ Nat.mul (entry level) (low level)
  let used : ℕ → Bool := fun level ↦ Nat.ble count (Nat.mul 2 level)
  have hlevels : ∀ i < Nat.min count maxLevel + 1,
      tableFirst (0 + i) = chooseFirst (0 + i) := by
    intro i hi
    obtain ⟨hlow, hhigh⟩ := coeffCheck_sound hcoeff i
      (Nat.le_trans (Nat.le_of_lt_succ hi) (Nat.min_le_right count maxLevel))
    simp only [tableFirst, chooseFirst, low, high, Nat.zero_add, hlow, hhigh]
  simpa only [count, entry, low, high, tableFirst, chooseFirst, second, used,
      bleBranch_eq_min] using
    (pairedRec_fst used tableFirst second (Nat.min count maxLevel + 1) 0 0 0).trans
      (gatedScan_congr used tableFirst chooseFirst (Nat.min count maxLevel + 1) 0 0 hlevels)

/-- The split-level fused reconstruction's second component is its predecessor fold. -/
theorem nilMomentPairPredLevels_snd {outWidth dimension coeffT maxLevel sigEnc : ℕ}
    {shifts pmasks widths masks : Lean.RArray ℕ} {trees : Lean.RArray (Lean.RArray ℕ)} {s t : ℕ}
    (hcoeff : cert246Data.coeffCheck dimension maxLevel coeffT = true) :
    (cert246Data.nilMomentPairPredLevels outWidth coeffT maxLevel sigEnc
      shifts pmasks widths masks trees s t).2 =
      cert246Data.nilMomentValueLevels (Nat.sub dimension 1) maxLevel sigEnc
        shifts pmasks widths masks trees s t := by
  unfold cert246Data.nilMomentPairPredLevels cert246Data.nilMomentValueLevels
  let count := Nat.add
    (cert246Data.sigCount (cert246Data.sigField sigEnc s))
    (cert246Data.sigCount (cert246Data.sigField sigEnc t))
  let entry : ℕ → ℕ := fun level ↦
    cert246Data.nilLevelAt shifts pmasks widths masks trees level (cert246Data.triIdx s t)
  let low : ℕ → ℕ := fun level ↦
    Nat.land (Nat.land (Nat.shiftRight coeffT (Nat.shiftLeft level 7))
      340282366920938463463374607431768211455) 18446744073709551615
  let high : ℕ → ℕ := fun level ↦
    Nat.shiftRight (Nat.land (Nat.shiftRight coeffT (Nat.shiftLeft level 7))
      340282366920938463463374607431768211455) 64
  let first : ℕ → ℕ := fun level ↦
    Nat.mul (entry level) (Nat.add (low level) (Nat.shiftLeft (high level) outWidth))
  let tableSecond : ℕ → ℕ := fun level ↦ Nat.mul (entry level) (low level)
  let chooseSecond : ℕ → ℕ := fun level ↦
    Nat.mul (entry level) (Nat.choose (Nat.sub dimension 1) level)
  let used : ℕ → Bool := fun level ↦ Nat.ble count (Nat.mul 2 level)
  have hlevels : ∀ i < Nat.min count maxLevel + 1,
      tableSecond (0 + i) = chooseSecond (0 + i) := by
    intro i hi
    simp only [tableSecond, chooseSecond, low, Nat.zero_add, (coeffCheck_sound hcoeff i
      (Nat.le_trans (Nat.le_of_lt_succ hi) (Nat.min_le_right count maxLevel))).1]
  simpa only [count, entry, low, high, first, tableSecond, chooseSecond, used,
      bleBranch_eq_min] using
    (pairedRec_snd used first tableSecond (Nat.min count maxLevel + 1) 0 0 0).trans
      (gatedScan_congr used tableSecond chooseSecond (Nat.min count maxLevel + 1) 0 0 hlevels)

private theorem resultWindowCons {P : ℕ → ℕ → Prop} {C : ℕ → Prop}
    {s index count : ℕ} (head : P s index)
    (tail : ∀ j < count, P (s + 1 + j) (index + 1 + j))
    (continuation : C (index + 1 + count)) :
    (∀ j < count + 1, P (s + j) (index + j)) ∧ C (index + (count + 1)) := by
  refine ⟨fun j hj ↦ ?_, by rwa [(by omega : index + (count + 1) = index + 1 + count)]⟩
  rcases j with _ | j
  · simpa using head
  · simpa [(by omega : s + (j + 1) = s + 1 + j),
      (by omega : index + (j + 1) = index + 1 + j)] using tail j (by omega)

private theorem resultScan_sound (check : ℕ → ℕ → ℕ → Bool) (next : ℕ → ℕ → ℕ)
    (cursor : ℕ → ℕ) (hnext : ∀ index, next index (cursor index) = cursor (index + 1))
    (continuation : ℕ → ℕ → Bool) : ∀ count s index : ℕ,
      Nat.rec
        (fun _ index' current ↦ continuation index' current)
        (fun _ inductionHypothesis s' index' current ↦
          Bool.rec false
            (inductionHypothesis s'.succ index'.succ (next index' current))
            (check s' index' current))
        count s index (cursor index) = true →
      (∀ j < count, check (s + j) (index + j) (cursor (index + j)) = true) ∧
        continuation (index + count) (cursor (index + count)) = true
  | 0, _, _, h => ⟨fun j hj ↦ absurd hj (Nat.not_lt_zero j), h⟩
  | count + 1, s, index, h => by
      dsimp only at h
      rw [hnext index] at h
      rcases hcheck : check s index (cursor index) with _ | _
      · simp [hcheck] at h
      · rw [hcheck] at h
        obtain ⟨hall, hcontinuation⟩ :=
          resultScan_sound check next cursor hnext continuation count s.succ index.succ h
        exact resultWindowCons (P := fun a b ↦ check a b (cursor b) = true)
          (C := fun b ↦ continuation b (cursor b) = true) hcheck hall hcontinuation

private noncomputable def resultRow (cs pmask width : ℕ) (tree : Lean.RArray ℕ)
    (check : ℕ → ℕ → ℕ → Bool) (continuation : ℕ → ℕ → ℕ → Bool) (t index current : ℕ) : Bool :=
  Nat.rec
    (fun _ index' current' ↦ continuation t.succ index' current')
    (fun _ inductionHypothesis s index' current' ↦
      Bool.rec false
        (inductionHypothesis s.succ index'.succ
          (Bool.rec (current'.shiftRight width)
            (tree.get (index'.succ.shiftRight cs)) ((index'.land pmask).beq pmask)))
        (check s t current'))
    t.succ 0 index current

private noncomputable def resultRows (cs pmask width : ℕ) (tree : Lean.RArray ℕ)
    (check : ℕ → ℕ → ℕ → Bool) (count t index current : ℕ) : Bool :=
  Nat.rec
    (fun _ _ _ ↦ true)
    (fun _ inductionHypothesis t' index' current' ↦
      resultRow cs pmask width tree check inductionHypothesis t' index' current')
    count t index current

private theorem resultRow_sound {cs pmask width : ℕ} {tree : Lean.RArray ℕ}
    (hpmask : pmask + 1 = 2 ^ cs) (check : ℕ → ℕ → ℕ → Bool)
    (continuation : ℕ → ℕ → ℕ → Bool) (t index : ℕ)
    (h : resultRow cs pmask width tree check continuation t index
      (cursorAt cs pmask width tree index) = true) :
    (∀ s ≤ t, check s t (cursorAt cs pmask width tree (index + s)) = true) ∧
      continuation (t + 1) (index + (t + 1))
        (cursorAt cs pmask width tree (index + (t + 1))) = true := by
  unfold resultRow at h
  obtain ⟨hall, hcontinuation⟩ := resultScan_sound _ _
    (cursorAt cs pmask width tree) (cursorAt_next hpmask) _ t.succ 0 index h
  refine ⟨fun s hs ↦ ?_, hcontinuation⟩
  simpa only [Nat.zero_add] using hall s (Nat.lt_succ_of_le hs)

private theorem resultRowsBase_shift (index t j s : ℕ) :
    index + (t + 1) + rowsBase (t + 1) j + s = index + rowsBase t (j + 1) + s := by
  rw [rowsBase_succ]
  omega

private theorem resultRows_sound {cs pmask width : ℕ} {tree : Lean.RArray ℕ}
    (hpmask : pmask + 1 = 2 ^ cs) (check : ℕ → ℕ → ℕ → Bool) :
    ∀ count t index,
      resultRows cs pmask width tree check count t index
          (cursorAt cs pmask width tree index) = true →
        ∀ j < count, ∀ s ≤ t + j,
          check s (t + j) (cursorAt cs pmask width tree (index + rowsBase t j + s)) = true
  | 0, _, _, _ => fun j hj ↦ absurd hj (Nat.not_lt_zero j)
  | count + 1, t, index, h => by
      intro j hj s hs
      unfold resultRows at h
      obtain ⟨hentry, hrest⟩ := resultRow_sound hpmask check _ t index h
      rcases j with _ | j
      · simpa [rowsBase] using hentry s (by omega)
      · have result := resultRows_sound hpmask check count t.succ (index + t.succ) hrest
          j (Nat.lt_of_succ_lt_succ hj) s (by omega)
        rwa [resultRowsBase_shift, (by omega : t.succ + j = t + (j + 1))] at result

/-- A successful split-level result block certifies its pair and predecessor bound. -/
theorem nilResultBoundLevelsCheck_sound
    {outWidth pairCs pairPmask pairWidth pairMask coeffT maxLevel sigEnc : ℕ}
    {shifts pmasks widths masks : Lean.RArray ℕ} {trees : Lean.RArray (Lean.RArray ℕ)}
    {resultTree : Lean.RArray ℕ} {tLo tHi index : ℕ}
    (hpairPmask : pairPmask + 1 = 2 ^ pairCs) (hindex : index = rowsBase 0 tLo)
    (h : cert246Data.nilResultBoundLevelsCheck outWidth pairCs pairPmask pairWidth
      pairMask coeffT maxLevel sigEnc shifts pmasks widths masks trees resultTree
      tLo tHi index = true) :
    ∀ t, tLo ≤ t → t < tHi → ∀ s ≤ t,
      cert246Data.treeAt pairCs pairPmask pairWidth pairMask resultTree
          (cert246Data.triIdx s t) =
          (cert246Data.nilMomentPairPredLevels outWidth coeffT maxLevel sigEnc
            shifts pmasks widths masks trees s t).1 ∧
        (cert246Data.nilMomentPairPredLevels outWidth coeffT maxLevel sigEnc
            shifts pmasks widths masks trees s t).2 < 2 ^ outWidth := by
  let check : ℕ → ℕ → ℕ → Bool := fun s t current ↦
    let reconstructed := cert246Data.nilMomentPairPredLevels outWidth coeffT
      maxLevel sigEnc shifts pmasks widths masks trees s t
    Bool.and' (Nat.beq (Nat.land current pairMask) reconstructed.1)
      (Nat.blt reconstructed.2 (Nat.shiftLeft 1 outWidth))
  change resultRows pairCs pairPmask pairWidth resultTree check (tHi - tLo) tLo index
    (cursorAt pairCs pairPmask pairWidth resultTree index) = true at h
  intro t hlow hhigh s hst
  have hentry := resultRows_sound hpairPmask check (tHi - tLo) tLo index h
    (t - tLo) (by omega) s (by omega)
  have ht : tLo + (t - tLo) = t := by omega
  have htableIndex : index + rowsBase tLo (t - tLo) + s = cert246Data.triIdx s t := by
    rw [hindex, triIdx_eq hst, ← rowsBase_add, ht]
  rw [ht, htableIndex] at hentry
  simp only [check, Bool.and'_eq_and, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hentry
  rw [← treeAt_cursorAt] at hentry
  refine ⟨hentry.1, ?_⟩
  simpa only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.one_mul] using hentry.2

end PrimeGaps.Gap246
