/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Kernel.MomentBound
public import PrimeGapsCert.Gap246.Moments.NilEntrySound

/-! # Soundness of the packed triangular-table checks -/

@[expose] public section

namespace PrimeGaps.Gap246

/-- Entries preceding row `t + j` in a triangular walk beginning at row `t`. -/
def rowsBase (t j : ℕ) : ℕ := ∑ i ∈ Finset.range j, (t + i + 1)

/-- Splitting the first row off a triangular walk. -/
theorem rowsBase_succ (t j : ℕ) : rowsBase t (j + 1) = t + 1 + rowsBase (t + 1) j :=
  sum_range_head (· + 1) t j

/-- Triangular row bases add along a split of the row index. -/
theorem rowsBase_add (t j : ℕ) : rowsBase 0 (t + j) = rowsBase 0 t + rowsBase t j := by
  simp [rowsBase, Finset.sum_range_add]

/-- The number of entries preceding triangular row `j`. -/
theorem rowsBase_zero (j : ℕ) : rowsBase 0 j = j * (j + 1) / 2 := by
  have hsum : rowsBase 0 j = ∑ i ∈ Finset.range (j + 1), i := by
    simp [rowsBase, Finset.sum_range_succ']
  rw [hsum, Finset.sum_range_id, Nat.add_sub_cancel, Nat.mul_comm]

private theorem rowsBase_shift (idx t j s : ℕ) :
    idx + (t + 1) + rowsBase (t + 1) j + s = idx + rowsBase t (j + 1) + s := by
  rw [rowsBase_succ]
  omega

private theorem window_cons {P : ℕ → ℕ → Prop} {C : ℕ → Prop} {s idx count : ℕ}
    (head : P s idx) (tail : ∀ j < count, P (s + 1 + j) (idx + 1 + j))
    (continuation : C (idx + 1 + count)) :
    (∀ j < count + 1, P (s + j) (idx + j)) ∧ C (idx + (count + 1)) := by
  refine ⟨fun j hj ↦ ?_, by rwa [(by omega : idx + (count + 1) = idx + 1 + count)]⟩
  rcases j with _ | j
  · simpa using head
  · simpa [(by omega : s + (j + 1) = s + 1 + j),
      (by omega : idx + (j + 1) = idx + 1 + j)] using tail j (by omega)

private theorem scanCur1_sound (check : ℕ → ℕ → ℕ → Bool) (next : ℕ → ℕ → ℕ)
    (cursor : ℕ → ℕ) (hnext : ∀ i, next i (cursor i) = cursor (i + 1))
    (continuation : ℕ → ℕ → Bool) : ∀ count s idx : ℕ,
      Nat.rec
        (fun _ idx' current ↦ continuation idx' current)
        (fun _ inductionHypothesis s' idx' current ↦
          Bool.rec false
            (inductionHypothesis s'.succ idx'.succ (next idx' current))
            (check s' idx' current))
        count s idx (cursor idx) = true →
      (∀ j < count, check (s + j) (idx + j) (cursor (idx + j)) = true) ∧
        continuation (idx + count) (cursor (idx + count)) = true
  | 0, _, _, h => ⟨fun j hj ↦ absurd hj (Nat.not_lt_zero j), h⟩
  | count + 1, s, idx, h => by
      dsimp only at h
      rw [hnext idx] at h
      rcases hcheck : check s idx (cursor idx) with _ | _
      · simp [hcheck] at h
      · rw [hcheck] at h
        obtain ⟨hall, hcontinuation⟩ :=
          scanCur1_sound check next cursor hnext continuation count s.succ idx.succ h
        exact window_cons (P := fun a b ↦ check a b (cursor b) = true)
          (C := fun b ↦ continuation b (cursor b) = true) hcheck hall hcontinuation

private theorem rowsCur1_sound {row : (ℕ → ℕ → ℕ → Bool) → ℕ → ℕ → ℕ → Bool}
    {property : ℕ → ℕ → ℕ → Prop} {cursor : ℕ → ℕ}
    (hrow : ∀ (continuation : ℕ → ℕ → ℕ → Bool) (t idx : ℕ),
      row continuation t idx (cursor idx) = true →
      (∀ s ≤ t, property t s (idx + s)) ∧
        continuation (t + 1) (idx + (t + 1)) (cursor (idx + (t + 1))) = true) :
    ∀ count t idx : ℕ,
      Nat.rec
        (fun _ _ _ ↦ true)
        (fun _ inductionHypothesis t' idx' current ↦
          row inductionHypothesis t' idx' current)
        count t idx (cursor idx) = true →
      ∀ j < count, ∀ s ≤ t + j,
        property (t + j) s (idx + rowsBase t j + s)
  | 0, _, _, _ => fun j hj ↦ absurd hj (Nat.not_lt_zero j)
  | count + 1, t, idx, h => by
      intro j hj s hs
      obtain ⟨hentry, hrest⟩ := hrow _ t idx h
      rcases j with _ | j
      · simpa [rowsBase] using hentry s (by omega)
      · have result := rowsCur1_sound hrow count t.succ (idx + t.succ) hrest j
          (Nat.lt_of_succ_lt_succ hj) s (by omega)
        rwa [rowsBase_shift, (by omega : t + 1 + j = t + (j + 1))] at result

/-- The shifted packed leaf containing the field at table index `i`. -/
noncomputable def cursorAt (cs pmask width : ℕ) (tree : Lean.RArray ℕ) (i : ℕ) : ℕ :=
  (tree.get (i.shiftRight cs)).shiftRight (width * (i.land pmask))

/-- A packed table entry is the masked field of the cursor sitting at its index. -/
theorem treeAt_cursorAt (cs pmask width mask : ℕ) (tree : Lean.RArray ℕ) (i : ℕ) :
    cert246Data.treeAt cs pmask width mask tree i =
      (cursorAt cs pmask width tree i).land mask := by
  simp only [cert246Data.treeAt, cert246Data.eagerAt_eq]
  rfl

private theorem shiftRight_shiftRight (x a b : ℕ) :
    (x.shiftRight a).shiftRight b = x.shiftRight (a + b) :=
  (Nat.shiftRight_add x a b).symm

/-- Advancing a packed cursor either shifts within its leaf or loads the next leaf. -/
theorem cursorAt_next {cs pmask width : ℕ} {tree : Lean.RArray ℕ}
    (hpmask : pmask + 1 = 2 ^ cs) (i : ℕ) :
    (Bool.rec ((cursorAt cs pmask width tree i).shiftRight width) (tree.get (i.succ.shiftRight cs))
      ((i.land pmask).beq pmask) : ℕ) = cursorAt cs pmask width tree (i + 1) := by
  have hpositive : 0 < 2 ^ cs := Nat.two_pow_pos cs
  obtain rfl : pmask = 2 ^ cs - 1 := by omega
  have hland : ∀ x : ℕ, x.land (2 ^ cs - 1) = x % 2 ^ cs := (Nat.and_two_pow_sub_one_eq_mod · cs)
  have hshift : ∀ x : ℕ, x.shiftRight cs = x / 2 ^ cs := (Nat.shiftRight_eq_div_pow · cs)
  have hdecompose : 2 ^ cs * (i / 2 ^ cs) + i % 2 ^ cs = i := Nat.div_add_mod i (2 ^ cs)
  have hlt : i % 2 ^ cs < 2 ^ cs := Nat.mod_lt i hpositive
  unfold cursorAt
  rcases hboundary : (i.land (2 ^ cs - 1)).beq (2 ^ cs - 1) with _ | _
  · have hne : i % 2 ^ cs ≠ 2 ^ cs - 1 := hland i ▸ Nat.ne_of_beq_eq_false hboundary
    have hsmall : i % 2 ^ cs + 1 < 2 ^ cs := by omega
    have hsucc : i + 1 = 2 ^ cs * (i / 2 ^ cs) + (i % 2 ^ cs + 1) := by omega
    simp only [hshift, hland, hsucc, Nat.mul_add_mod, Nat.mul_add_div hpositive,
      Nat.mod_eq_of_lt hsmall, Nat.div_eq_of_lt hsmall, Nat.add_zero]
    exact shiftRight_shiftRight _ _ _
  · have heq : i % 2 ^ cs = 2 ^ cs - 1 := hland i ▸ Nat.eq_of_beq_eq_true hboundary
    have hsucc : i + 1 = 2 ^ cs * (i / 2 ^ cs + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
    have hmod : (i + 1) % 2 ^ cs = 0 := by rw [hsucc]; exact Nat.mul_mod_right _ _
    simp only [hland, hmod]
    rfl

private noncomputable def tableRow (cs pmask width mask : ℕ) (tree : Lean.RArray ℕ)
    (expected : ℕ → ℕ → ℕ) (continuation : ℕ → ℕ → ℕ → Bool)
    (t idx current : ℕ) : Bool :=
  Nat.rec
    (fun _ idx' current' ↦ continuation t.succ idx' current')
    (fun _ inductionHypothesis s idx' current' ↦
      Bool.rec false
        (inductionHypothesis s.succ idx'.succ
          (Bool.rec (current'.shiftRight width) (tree.get (idx'.succ.shiftRight cs))
            ((idx'.land pmask).beq pmask)))
        ((current'.land mask).beq (expected s t)))
    t.succ 0 idx current

private noncomputable def tableRows (cs pmask width mask : ℕ) (tree : Lean.RArray ℕ)
    (expected : ℕ → ℕ → ℕ) (count t idx current : ℕ) : Bool :=
  Nat.rec
    (fun _ _ _ ↦ true)
    (fun _ inductionHypothesis t' idx' current' ↦
      tableRow cs pmask width mask tree expected inductionHypothesis t' idx' current')
    count t idx current

private theorem tableRow_sound {cs pmask width mask : ℕ} {tree : Lean.RArray ℕ}
    (hpmask : pmask + 1 = 2 ^ cs) (expected : ℕ → ℕ → ℕ) (continuation : ℕ → ℕ → ℕ → Bool)
    (t idx : ℕ)
    (h : tableRow cs pmask width mask tree expected continuation t idx
      (cursorAt cs pmask width tree idx) = true) :
    (∀ s ≤ t, cert246Data.treeAt cs pmask width mask tree (idx + s) = expected s t) ∧
      continuation (t + 1) (idx + (t + 1))
        (cursorAt cs pmask width tree (idx + (t + 1))) = true := by
  unfold tableRow at h
  obtain ⟨hall, hcontinuation⟩ := scanCur1_sound _ _
    (cursorAt cs pmask width tree) (cursorAt_next hpmask) _ t.succ 0 idx h
  refine ⟨fun s hs ↦ ?_, hcontinuation⟩
  rw [treeAt_cursorAt]
  simpa only [Nat.zero_add] using Nat.eq_of_beq_eq_true (hall s (Nat.lt_succ_of_le hs))

private theorem tableRows_sound {cs pmask width mask : ℕ} {tree : Lean.RArray ℕ}
    (hpmask : pmask + 1 = 2 ^ cs) (expected : ℕ → ℕ → ℕ) (count t idx : ℕ)
    (h : tableRows cs pmask width mask tree expected count t idx
      (cursorAt cs pmask width tree idx) = true) :
    ∀ j < count, ∀ s ≤ t + j,
      cert246Data.treeAt cs pmask width mask tree (idx + rowsBase t j + s) =
        expected s (t + j) := by
  unfold tableRows at h
  exact rowsCur1_sound
    (row := tableRow cs pmask width mask tree expected)
    (property := fun t' s' i ↦
      cert246Data.treeAt cs pmask width mask tree i = expected s' t')
    (cursor := cursorAt cs pmask width tree)
    (fun continuation t' idx' hrow ↦
      tableRow_sound hpmask expected continuation t' idx' hrow)
    count t idx h

private noncomputable def guardedRows (active : ℕ → ℕ → Bool) (check : ℕ → ℕ → ℕ → Bool)
    (count t idx : ℕ) : Bool :=
  Nat.rec
    (fun _ _ ↦ true)
    (fun _ inductionHypothesis t' idx' ↦
      Nat.rec
        (fun _ nextIdx ↦ inductionHypothesis t'.succ nextIdx)
        (fun _ rowHypothesis s nextIdx ↦
          Bool.rec (rowHypothesis s.succ nextIdx.succ)
            (Bool.rec false (rowHypothesis s.succ nextIdx.succ) (check s t' nextIdx))
            (active s t'))
        t'.succ 0 idx')
    count t idx

private theorem guardedScan_sound (active : ℕ → Bool) (check : ℕ → ℕ → Bool)
    (continuation : ℕ → Bool) :
    ∀ count s idx,
      Nat.rec (motive := fun _ ↦ ℕ → ℕ → Bool)
        (fun _ idx' ↦ continuation idx')
        (fun _ inductionHypothesis s' idx' ↦
          Bool.rec (inductionHypothesis s'.succ idx'.succ)
            (Bool.rec false (inductionHypothesis s'.succ idx'.succ) (check s' idx'))
            (active s'))
        count s idx = true →
      (∀ j < count, active (s + j) = true → check (s + j) (idx + j) = true) ∧
        continuation (idx + count) = true
  | 0, _, _, h => ⟨fun j hj ↦ absurd hj (Nat.not_lt_zero j), h⟩
  | count + 1, s, idx, h => by
      dsimp only at h
      obtain ⟨hhead, hall, hcontinuation⟩ :
          (active s = true → check s idx = true) ∧
          (∀ j < count, active (s.succ + j) = true → check (s.succ + j) (idx.succ + j) = true) ∧
          continuation (idx.succ + count) = true := by
        rcases hactive : active s with _ | _
        · rw [hactive] at h
          exact ⟨by simp, guardedScan_sound active check continuation count s.succ idx.succ h⟩
        · rw [hactive] at h
          rcases Bool.eq_false_or_eq_true (check s idx) with hcheck | hcheck
          · rw [hcheck] at h
            exact ⟨fun _ ↦ hcheck,
              guardedScan_sound active check continuation count s.succ idx.succ h⟩
          · simp [hcheck] at h
      refine ⟨fun j hj hjactive ↦ ?_, by
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1 count] using hcontinuation⟩
      rcases j with _ | j
      · simpa using hhead (by simpa using hjactive)
      · simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1 j] using
          hall j (by omega) (by
            simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1 j] using hjactive)

private theorem guardedRow_sound (active : ℕ → ℕ → Bool) (check : ℕ → ℕ → ℕ → Bool)
    (continuation : ℕ → ℕ → Bool) (t idx : ℕ)
    (h : Nat.rec (motive := fun _ ↦ ℕ → ℕ → Bool)
      (fun _ nextIdx ↦ continuation t.succ nextIdx)
      (fun _ inductionHypothesis s nextIdx ↦
        Bool.rec (inductionHypothesis s.succ nextIdx.succ)
          (Bool.rec false (inductionHypothesis s.succ nextIdx.succ) (check s t nextIdx))
          (active s t))
      t.succ 0 idx = true) :
    (∀ s ≤ t, active s t = true → check s t (idx + s) = true) ∧
      continuation t.succ (idx + t.succ) = true := by
  obtain ⟨hall, hcontinuation⟩ :=
    guardedScan_sound (fun s ↦ active s t) (fun s i ↦ check s t i)
      (continuation t.succ) t.succ 0 idx h
  exact ⟨fun s hs ↦ by simpa using hall s (by omega), by simpa using hcontinuation⟩

private theorem guardedRows_sound (active : ℕ → ℕ → Bool) (check : ℕ → ℕ → ℕ → Bool) :
    ∀ count t idx, guardedRows active check count t idx = true →
      ∀ j < count, ∀ s ≤ t + j,
        active s (t + j) = true → check s (t + j) (idx + rowsBase t j + s) = true
  | 0, _, _, _ => fun j hj ↦ absurd hj (Nat.not_lt_zero j)
  | count + 1, t, idx, h => by
      unfold guardedRows at h
      dsimp only at h
      obtain ⟨hrow, hrest⟩ := guardedRow_sound active check
        (fun nextT nextIdx ↦ guardedRows active check count nextT nextIdx) t idx h
      intro j hj s hs hactive
      rcases j with _ | j
      · simpa [rowsBase] using hrow s hs hactive
      · have hactive' : active s (t.succ + j) = true := by
          simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1 j] using hactive
        have result := guardedRows_sound active check count t.succ (idx + t.succ) hrest
          j (by omega) s (by omega) hactive'
        rwa [rowsBase_shift, (by omega : t + 1 + j = t + (j + 1))] at result

/-- The unordered triangular index is symmetric. -/
theorem triIdx_comm (s t : ℕ) : cert246Data.triIdx s t = cert246Data.triIdx t s := by
  unfold cert246Data.triIdx
  rcases Nat.lt_trichotomy s t with h | rfl | h
  · have hst : Nat.ble (Nat.succ s) t = true := Nat.ble_eq.mpr h
    have hts : Nat.ble (Nat.succ t) s = false := by
      simpa only [Bool.eq_false_iff, ne_eq, Nat.ble_eq] using Nat.not_le.mpr (Nat.lt_succ_of_lt h)
    rw [hst, hts]
  · rfl
  · have hts : Nat.ble (Nat.succ t) s = true := Nat.ble_eq.mpr h
    have hst : Nat.ble (Nat.succ s) t = false := by
      simpa only [Bool.eq_false_iff, ne_eq, Nat.ble_eq] using Nat.not_le.mpr (Nat.lt_succ_of_lt h)
    rw [hst, hts]

/-- On or below the diagonal, `triIdx` is the ordinary triangular row offset. -/
theorem triIdx_eq {s t : ℕ} (h : s ≤ t) : cert246Data.triIdx s t = rowsBase 0 t + s := by
  unfold cert246Data.triIdx
  have hcompare : Nat.ble (Nat.succ t) s = false := by
    simpa only [Bool.eq_false_iff, ne_eq, Nat.ble_eq] using Nat.not_le.mpr (Nat.lt_succ_of_le h)
  rw [hcompare, rowsBase_zero]
  rfl

/-- A successful base block identifies all of its level-zero table entries. -/
theorem nilBaseCheck_sound {cs pmask width mask sigEnc : ℕ} {tree : Lean.RArray ℕ}
    {tLo tHi idx0 : ℕ} (hpmask : pmask + 1 = 2 ^ cs)
    (hidx : idx0 = rowsBase 0 tLo)
    (h : cert246Data.nilBaseCheck cs pmask width mask sigEnc tree tLo tHi idx0 = true) :
    ∀ t, tLo ≤ t → t < tHi → ∀ s ≤ t,
      cert246Data.treeAt cs pmask width mask tree (cert246Data.triIdx s t) =
        if cert246Data.sigField sigEnc s = 0 ∧
            cert246Data.sigField sigEnc t = 0 then 1 else 0 := by
  let expected : ℕ → ℕ → ℕ := fun s t ↦
    Bool.rec 0 1 (Bool.and'
      (Nat.beq (cert246Data.sigField sigEnc s) 0)
      (Nat.beq (cert246Data.sigField sigEnc t) 0))
  change tableRows cs pmask width mask tree expected (tHi - tLo) tLo idx0
    (cursorAt cs pmask width tree idx0) = true at h
  intro t hlow hhigh s hst
  have hentry := tableRows_sound hpmask expected (tHi - tLo) tLo idx0 h
    (t - tLo) (by omega) s (by omega)
  rw [(by omega : tLo + (t - tLo) = t), hidx] at hentry
  rw [triIdx_eq hst, (by omega : t = tLo + (t - tLo)), rowsBase_add,
    (by omega : tLo + (t - tLo) = t), hentry]
  unfold expected
  rcases hs : (cert246Data.sigField sigEnc s).beq 0 with _ | _ <;>
    rcases ht : (cert246Data.sigField sigEnc t).beq 0 with _ | _ <;>
      simp_all [Nat.eq_of_beq_eq_true, Nat.ne_of_beq_eq_false]

/-- A successful transition block identifies every checked entry with the first-order
identity-free recurrence, or with zero outside that level's support. -/
theorem nilStepCheck_sound {tri cs pmask width mask sigEnc eraseEnc factT level : ℕ}
    {tree : Lean.RArray ℕ} {tLo tHi idx0 : ℕ}
    (hpmask : pmask + 1 = 2 ^ cs) (hidx : idx0 = rowsBase 0 tLo)
    (h : cert246Data.nilStepCheck tri cs pmask width mask sigEnc eraseEnc factT level tree
      tLo tHi idx0 = true) :
    ∀ t, tLo ≤ t → t < tHi → ∀ s ≤ t,
      cert246Data.treeAt cs pmask width mask tree
          (level * tri + cert246Data.triIdx s t) =
        Bool.rec 0
          (cert246Data.nilEntry tri cs pmask width mask eraseEnc factT level tree s t)
          (cert246Data.nilActive level
            (cert246Data.sigCount (cert246Data.sigField sigEnc s) +
              cert246Data.sigCount (cert246Data.sigField sigEnc t))) := by
  let expected : ℕ → ℕ → ℕ := fun s t ↦
    Bool.rec 0
      (cert246Data.nilEntry tri cs pmask width mask eraseEnc factT level tree s t)
      (cert246Data.nilActive level
        (cert246Data.sigCount (cert246Data.sigField sigEnc s) +
          cert246Data.sigCount (cert246Data.sigField sigEnc t)))
  change tableRows cs pmask width mask tree expected (tHi - tLo) tLo
    (level * tri + idx0) (cursorAt cs pmask width tree (level * tri + idx0)) = true at h
  intro t hlow hhigh s hst
  have hentry := tableRows_sound hpmask expected (tHi - tLo) tLo (level * tri + idx0) h
    (t - tLo) (by omega) s (by omega)
  rw [(by omega : tLo + (t - tLo) = t), hidx] at hentry
  rw [triIdx_eq hst, (by omega : t = tLo + (t - tLo)), rowsBase_add,
    (by omega : tLo + (t - tLo) = t)]
  simpa only [Nat.add_assoc] using hentry

/-- A successful independently packed base block identifies all of its entries. -/
theorem nilBaseLevelsCheck_sound {sigEnc : ℕ}
    {shifts pmasks widths masks : Lean.RArray ℕ}
    {trees : Lean.RArray (Lean.RArray ℕ)} {tLo tHi idx0 : ℕ}
    (hgeometry : pmasks.get 0 + 1 = 2 ^ shifts.get 0)
    (hidx : idx0 = rowsBase 0 tLo)
    (h : cert246Data.nilBaseLevelsCheck sigEnc shifts pmasks widths masks trees
      tLo tHi idx0 = true) :
    ∀ t, tLo ≤ t → t < tHi → ∀ s ≤ t,
      cert246Data.nilLevelAt shifts pmasks widths masks trees 0
          (cert246Data.triIdx s t) =
        if cert246Data.sigField sigEnc s = 0 ∧
            cert246Data.sigField sigEnc t = 0 then 1 else 0 := by
  unfold cert246Data.nilBaseLevelsCheck at h
  unfold cert246Data.nilLevelAt
  exact nilBaseCheck_sound hgeometry hidx h

/-- A successful two-tree transition block identifies every entry in the generic support
of that level. -/
theorem nilStepTreesCheck_sound
    {currentShift currentPmask currentWidth currentMask previousShift previousPmask
      previousWidth previousMask sigEnc eraseEnc factT level : ℕ}
    {currentTree previousTree : Lean.RArray ℕ} {tLo tHi idx0 : ℕ}
    (hidx : idx0 = rowsBase 0 tLo)
    (h : cert246Data.nilStepTreesCheck currentShift currentPmask currentWidth currentMask
      previousShift previousPmask previousWidth previousMask sigEnc eraseEnc factT level
      currentTree previousTree tLo tHi idx0 = true) :
    ∀ t, tLo ≤ t → t < tHi → ∀ s ≤ t,
      Bool.rec (motive := fun _ ↦ Nat) 0
          (cert246Data.treeAt currentShift currentPmask currentWidth currentMask currentTree
            (cert246Data.triIdx s t))
          (cert246Data.nilActive level
            (cert246Data.sigCount (cert246Data.sigField sigEnc s) +
              cert246Data.sigCount (cert246Data.sigField sigEnc t))) =
        Bool.rec (motive := fun _ ↦ Nat) 0
          (cert246Data.nilTreeEntry sigEnc eraseEnc factT level previousShift previousPmask
            previousWidth previousMask previousTree s t)
          (cert246Data.nilActive level
            (cert246Data.sigCount (cert246Data.sigField sigEnc s) +
              cert246Data.sigCount (cert246Data.sigField sigEnc t))) := by
  let active : ℕ → ℕ → Bool := fun s t ↦ cert246Data.nilActive level
    (cert246Data.sigCount (cert246Data.sigField sigEnc s) +
      cert246Data.sigCount (cert246Data.sigField sigEnc t))
  let check : ℕ → ℕ → ℕ → Bool := fun s t index ↦ Nat.beq
    (cert246Data.treeAt currentShift currentPmask currentWidth currentMask currentTree index)
    (cert246Data.nilTreeEntry sigEnc eraseEnc factT level previousShift previousPmask
      previousWidth previousMask previousTree s t)
  unfold cert246Data.nilStepTreesCheck at h
  change guardedRows active check (tHi - tLo) tLo idx0 = true at h
  intro t hlow hhigh s hst
  change Bool.rec (motive := fun _ ↦ Nat) 0
      (cert246Data.treeAt currentShift currentPmask currentWidth currentMask currentTree
        (cert246Data.triIdx s t)) (active s t) =
    Bool.rec (motive := fun _ ↦ Nat) 0
      (cert246Data.nilTreeEntry sigEnc eraseEnc factT level previousShift previousPmask
        previousWidth previousMask previousTree s t) (active s t)
  rcases hactive : active s t with _ | _
  · rfl
  · have hactive' : active s (tLo + (t - tLo)) = true := by
      rwa [Nat.add_sub_of_le hlow]
    have hentry := guardedRows_sound active check (tHi - tLo) tLo idx0 h
      (t - tLo) (by omega) s (by omega) hactive'
    rw [(by omega : tLo + (t - tLo) = t), hidx] at hentry
    unfold check at hentry
    rw [show rowsBase 0 tLo + rowsBase tLo (t - tLo) + s = cert246Data.triIdx s t by
      rw [← rowsBase_add, Nat.add_sub_of_le hlow, triIdx_eq hst]] at hentry
    exact Nat.eq_of_beq_eq_true hentry

/-- A successful result block identifies each packed output pair with its reconstruction
from the nilpotent table. -/
theorem nilResultCheck_sound
    {tri cs pmask width mask outWidth pairCs pairPmask pairWidth pairMask dimension maxLevel
      sigEnc : ℕ} {tree resultTree : Lean.RArray ℕ} {tLo tHi idx0 : ℕ}
    (hpairPmask : pairPmask + 1 = 2 ^ pairCs) (hidx : idx0 = rowsBase 0 tLo)
    (h : cert246Data.nilResultCheck tri cs pmask width mask outWidth pairCs pairPmask
      pairWidth pairMask dimension maxLevel sigEnc tree resultTree tLo tHi idx0 = true) :
    ∀ t, tLo ≤ t → t < tHi → ∀ s ≤ t,
      cert246Data.treeAt pairCs pairPmask pairWidth pairMask resultTree
          (cert246Data.triIdx s t) =
        cert246Data.nilMomentPair tri cs pmask width mask outWidth dimension maxLevel
          sigEnc tree s t := by
  let expected : ℕ → ℕ → ℕ := fun s t ↦
    cert246Data.nilMomentPair tri cs pmask width mask outWidth dimension maxLevel
      sigEnc tree s t
  change tableRows pairCs pairPmask pairWidth pairMask resultTree expected
    (tHi - tLo) tLo idx0 (cursorAt pairCs pairPmask pairWidth resultTree idx0) = true at h
  intro t hlow hhigh s hst
  have hentry := tableRows_sound hpairPmask expected (tHi - tLo) tLo idx0 h
    (t - tLo) (by omega) s (by omega)
  rw [(by omega : tLo + (t - tLo) = t), hidx] at hentry
  rw [triIdx_eq hst, (by omega : t = tLo + (t - tLo)), rowsBase_add,
    (by omega : tLo + (t - tLo) = t)]
  exact hentry

end PrimeGaps.Gap246
