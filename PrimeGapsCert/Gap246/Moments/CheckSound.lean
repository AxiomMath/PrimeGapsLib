/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Kernel.Extra
public import PrimeGapsCert.Gap246.Kernel.Moments
public import PrimeGapsCert.Gap246.Moments.Direct.DecodeSound
public import PrimeGapsCert.Gap246.Moments.Spec


/-! # Soundness of the shared packed moment inputs -/

@[expose] public section

open scoped Nat

namespace PrimeGaps.Gap246

open cert246Kernel

/-! ## Factorial-table soundness -/

private theorem shiftRight_shiftRight (x a b : ℕ) :
    (x.shiftRight a).shiftRight b = x.shiftRight (a + b) :=
  (Nat.shiftRight_add x a b).symm

/-- A successful factorial-table check identifies every inspected field. -/
theorem factCheck_sound {mask count factT : ℕ}
    (h : cert246Kernel.factCheck mask count factT = true) :
    ∀ k < count, (factT.shiftRight (256 * k)).land mask = k ! := by
  suffices aux : ∀ fuel i current, current = factT.shiftRight (256 * i) →
      Nat.rec
        (fun _ _ value ↦ value.beq 0)
        (fun _ ih index factorial value ↦
          Bool.rec false
            (ih index.succ (factorial * index.succ) (value.shiftRight 256))
            ((value.land mask).beq factorial))
        fuel i (i !) current = true →
      ∀ k, i ≤ k → k < i + fuel →
        (factT.shiftRight (256 * k)).land mask = (k !) by
    intro k hk
    exact aux count 0 factT (by simp) h k (Nat.zero_le k) (by omega)
  intro fuel
  induction fuel with
  | zero => exact fun _ _ _ _ _ _ upper ↦ by omega
  | succ remaining inductionHypothesis =>
      intro i current hcurrent hfold k lower upper
      dsimp only at hfold
      rcases hfield : (current.land mask).beq (i !) with _ | _ <;>
        rw [hfield] at hfold
      · simp at hfold
      · rcases Nat.eq_or_lt_of_le lower with rfl | lower'
        · rw [← hcurrent]
          exact Nat.eq_of_beq_eq_true hfield
        · have hstep : i ! * i.succ = (i + 1)! := by
            simp [Nat.factorial_succ, Nat.mul_comm]
          refine inductionHypothesis (i + 1) (current.shiftRight 256) ?_
            (by rwa [hstep] at hfold) k lower' (by omega)
          rw [hcurrent, shiftRight_shiftRight,
            (by omega : 256 * i + 256 = 256 * (i + 1))]

/-! ## Signature-encoding soundness -/

/-- A short-circuiting scan used to expose the inner recursion of `encCheck`. -/
private noncomputable def nibScan
    (check : ℕ → Bool) (continuation : Bool) (fuel cursor : ℕ) : Bool :=
  Nat.rec
    (fun _ ↦ continuation)
    (fun _ inductionHypothesis cursor' ↦
      Bool.rec false (inductionHypothesis cursor'.succ) (check cursor'))
    fuel cursor

private theorem nibScan_sound {check : ℕ → Bool} {continuation : Bool} :
    ∀ fuel cursor, nibScan check continuation fuel cursor = true →
      (∀ j, cursor ≤ j → j < cursor + fuel → check j = true) ∧ continuation = true := by
  intro fuel
  induction fuel with
  | zero => exact fun cursor h ↦ ⟨fun j _ upper ↦ absurd upper (by omega), h⟩
  | succ fuel inductionHypothesis =>
      intro cursor h
      dsimp [nibScan] at h
      rcases hcheck : check cursor with _ | _
      · simp [hcheck] at h
      · rw [hcheck] at h
        obtain ⟨hall, hcontinuation⟩ := inductionHypothesis (cursor + 1) h
        refine ⟨fun j lower upper ↦ ?_, hcontinuation⟩
        rcases Nat.eq_or_lt_of_le lower with rfl | lower'
        · exact hcheck
        · exact hall j (by omega) (by omega)

/-- The row recursion definitionally equal to `cert246Kernel.encCheck`. -/
private noncomputable def encRows (maxNib partBound sigEnc : ℕ) : ℕ → ℕ → Bool
    := fun fuel row ↦
  Nat.rec
    (fun _ ↦ true)
    (fun _ inductionHypothesis row' ↦
      let enc := cert246Data.sigField sigEnc row'
      Bool.rec false
        (nibScan (fun t ↦ (cert246Data.sigNib enc t).ble partBound)
          (inductionHypothesis row'.succ) maxNib 0)
        (enc.blt (Nat.shiftLeft 1 (Nat.shiftLeft (maxNib + 1) 2))))
    fuel row

private theorem encCheck_eq_rows (S maxNib partBound sigEnc : ℕ) :
    cert246Kernel.encCheck S maxNib partBound sigEnc =
      encRows maxNib partBound sigEnc S 0 := rfl

private theorem encodingBound (maxNib : ℕ) :
    1 <<< ((maxNib + 1) <<< 2) = 2 ^ (4 * (maxNib + 1)) := by
  simp [Nat.shiftLeft_eq, Nat.mul_comm]

private theorem encRows_sound (maxNib partBound sigEnc : ℕ) :
    ∀ fuel row, encRows maxNib partBound sigEnc fuel row = true →
      ∀ g, row ≤ g → g < row + fuel →
        cert246Data.sigField sigEnc g < 2 ^ (4 * (maxNib + 1)) ∧
          ∀ t < maxNib,
            cert246Data.sigNib (cert246Data.sigField sigEnc g) t ≤ partBound := by
  intro fuel
  induction fuel with
  | zero => exact fun _ _ _ _ upper ↦ absurd upper (by omega)
  | succ fuel inductionHypothesis =>
      intro row h
      dsimp [encRows] at h
      rcases hbound : (cert246Data.sigField sigEnc row).blt
          (1 <<< ((maxNib + 1) <<< 2)) with _ | _ <;>
        rw [hbound] at h
      · simp at h
      · obtain ⟨hparts, hrest⟩ := nibScan_sound maxNib 0 h
        rw [encodingBound] at hbound
        have hinduction := inductionHypothesis (row + 1) hrest
        grind [Nat.le_of_ble_eq_true, Nat.blt_eq]

/-- A successful encoding check bounds every encoding and each inspected halved part. -/
theorem encCheck_sound {S maxNib partBound sigEnc : ℕ}
    (h : cert246Kernel.encCheck S maxNib partBound sigEnc = true) :
    ∀ g < S, cert246Data.sigField sigEnc g < 2 ^ (4 * (maxNib + 1)) ∧
      ∀ t < maxNib, cert246Data.sigNib (cert246Data.sigField sigEnc g) t ≤ partBound := by
  rw [encCheck_eq_rows] at h
  exact fun g hg ↦ encRows_sound maxNib partBound sigEnc S 0 h g (Nat.zero_le g) (by omega)

private theorem boolRecContinuation_sound (check : ℕ → Bool) (continuation : Bool) :
    ∀ count cursor,
      Nat.rec (motive := fun _ ↦ ℕ → Bool)
          (fun _ ↦ continuation)
          (fun _ inductionHypothesis index ↦
            Bool.rec false (inductionHypothesis index.succ) (check index))
          count cursor = true →
        (∀ index, cursor ≤ index → index < cursor + count → check index = true) ∧
          continuation = true := by
  intro count
  induction count with
  | zero =>
      intro cursor h
      exact ⟨fun index _ hupper ↦ absurd hupper (by omega), h⟩
  | succ count inductionHypothesis =>
      intro cursor hscan
      dsimp only at hscan
      rcases hcheck : check cursor with _ | _
      · simp [hcheck] at hscan
      · rw [hcheck] at hscan
        obtain ⟨hrest, hcontinuation⟩ := inductionHypothesis cursor.succ hscan
        refine ⟨fun index hlower hupper ↦ ?_, hcontinuation⟩
        rcases Nat.eq_or_lt_of_le hlower with rfl | hlower
        · exact hcheck
        · exact hrest index (by omega) (by omega)

/-- A successful packed erase-target check validates every represented erasure and identity. -/
theorem eraseTargetCheck_sound
    {signatureCount degreeBound eraseCs erasePmask sigEnc : ℕ}
    {eraseTargetTree : Lean.RArray ℕ}
    (hcheck : cert246Data.eraseTargetCheck signatureCount degreeBound eraseCs erasePmask
      sigEnc eraseTargetTree = true) :
    ∀ row < signatureCount,
      cert246Data.treeAt eraseCs erasePmask 16 65535 eraseTargetTree
          (row * (degreeBound + 1)) = row ∧
        ∀ position < cert246Data.sigCount (cert246Data.sigField sigEnc row),
          let enc := cert246Data.sigField sigEnc row
          let target := cert246Data.treeAt eraseCs erasePmask 16 65535 eraseTargetTree
            (row * (degreeBound + 1) + 2 * cert246Data.sigNib enc position)
          target < signatureCount ∧
            cert246Data.sigField sigEnc target = cert246Data.eraseAt enc position := by
  intro row hrow
  unfold cert246Data.eraseTargetCheck at hcheck
  have hrowCheck := (boolRecContinuation_sound
    (fun row ↦
      let enc := cert246Data.sigField sigEnc row
      Nat.rec (motive := fun _ ↦ ℕ → Bool)
        (fun _ ↦ Nat.beq
          (cert246Data.treeAt eraseCs erasePmask 16 65535 eraseTargetTree
            (row * (degreeBound + 1))) row)
        (fun _ positionHypothesis position ↦
          let target := cert246Data.treeAt eraseCs erasePmask 16 65535 eraseTargetTree
            (row * (degreeBound + 1) + 2 * cert246Data.sigNib enc position)
          Bool.rec false (positionHypothesis position.succ)
            (Bool.and' (Nat.blt target signatureCount)
              (Nat.beq (cert246Data.sigField sigEnc target)
                (cert246Data.eraseAt enc position))))
        (cert246Data.sigCount enc) 0)
    true signatureCount 0 hcheck).1 row (by omega) (by omega)
  dsimp only at hrowCheck
  let enc := cert246Data.sigField sigEnc row
  let check := fun position ↦
    let target := cert246Data.treeAt eraseCs erasePmask 16 65535 eraseTargetTree
      (row * (degreeBound + 1) + 2 * cert246Data.sigNib enc position)
    Bool.and' (Nat.blt target signatureCount)
      (Nat.beq (cert246Data.sigField sigEnc target) (cert246Data.eraseAt enc position))
  have hentries := boolRecContinuation_sound check
    (Nat.beq
      (cert246Data.treeAt eraseCs erasePmask 16 65535 eraseTargetTree
        (row * (degreeBound + 1))) row)
    (cert246Data.sigCount enc) 0 (by
      simpa only [enc, check] using hrowCheck)
  refine ⟨Nat.beq_eq.mp hentries.2, fun position hposition ↦ ?_⟩
  have hposition' : position < cert246Data.sigCount enc := by
    simpa only [enc] using hposition
  simpa only [check, enc, Bool.and'_eq_and, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] using
    hentries.1 position (by omega) (by omega)

end PrimeGaps.Gap246
