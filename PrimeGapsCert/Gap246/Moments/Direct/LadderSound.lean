/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Moments.ScanLemmas


/-! # Soundness of the moment ladder

`ladder_sound` identifies every entry of every checked ladder level with `PrimeGaps.facMomentNat`
of the two decoded signatures.
-/

@[expose] public section

namespace PrimeGaps.Gap246

section ladderSound

open cert246Kernel Nat
open cert246Data (sigField sigCount sigNib eraseAt slotField slotUsed slotPart2 slotTarget
  triIdx)

/-! ### Nibble arithmetic -/

private theorem land_fifteen' (x : ℕ) : Nat.land x 15 = x % 16 :=
  Nat.and_two_pow_sub_one_eq_mod x 4

private theorem sigCount_eq_mod' (enc : ℕ) : sigCount enc = enc % 16 := land_fifteen' enc

private theorem sigNib_eq_div (enc j : ℕ) : sigNib enc j = enc / 2 ^ (4 * (j + 1)) % 16 := by
  unfold sigNib
  rw [land_fifteen']
  simp [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mul_comm]

/-- A natural number below `2 ^ (4 * N)` with all `N` low nibbles zero is zero. -/
private theorem eq_zero_of_nibbles_zero :
    ∀ N x : ℕ, x < 2 ^ (4 * N) → (∀ j < N, x / 2 ^ (4 * j) % 16 = 0) → x = 0 := by
  intro N
  induction N with
  | zero => exact fun x hx _ => by simpa using hx
  | succ N ih =>
    intro x hx hnib
    have h16 : (2 : ℕ) ^ (4 * (N + 1)) = 16 * 2 ^ (4 * N) := by ring
    have h0 : x % 16 = 0 := by simpa using hnib 0 (by omega)
    have := ih (x / 16) (by omega) fun j hj => by
      rw [Nat.div_div_eq_div_mul, (by ring : (16 : ℕ) * 2 ^ (4 * j) = 2 ^ (4 * (j + 1)))]
      exact hnib (j + 1) (by omega)
    omega

/-- A checked signature encodes the empty multiset exactly when its field is zero. -/
private theorem decodeSig_eq_zero_iff {S maxNib sigEnc eraseEnc g enc m : ℕ}
    (hrow : RowFacts S maxNib sigEnc eraseEnc g enc m) (hm : m = sigCount enc)
    (hlt : enc < 2 ^ (4 * (maxNib + 1))) :
    decodeSig enc = 0 ↔ enc = 0 := by
  constructor
  · intro h
    rw [decodeSig_eq_map, Multiset.coe_eq_zero, List.map_eq_nil_iff, List.range_eq_nil] at h
    refine eq_zero_of_nibbles_zero (maxNib + 1) enc hlt fun j hj => ?_
    rcases j with _ | i
    · simpa [← sigCount_eq_mod'] using h
    · rw [← sigNib_eq_div]
      exact hrow.nib_zero i (by omega) (by omega)
  · rintro rfl
    simp [decodeSig_eq_map, sigCount_eq_mod']

/-! ### The ladder -/

private theorem triIdx_comm (a b : ℕ) : triIdx a b = triIdx b a := by
  unfold triIdx
  rcases hab : Nat.ble (Nat.succ a) b with _ | _ <;>
    rcases hba : Nat.ble (Nat.succ b) a with _ | _ <;>
    simp_all [Nat.ble_eq, Bool.eq_false_iff] <;> grind

/-- Soundness of the checked moment ladder: entry `(s, t)` of level `j` is the factorial
moment of order `j` of the two decoded signatures. -/
theorem ladder_sound {S n maxNib aBound sigEnc eraseEnc labelEnc fmask factT L : ℕ}
    {cs pm w mask : ℕ → ℕ} {trees : ℕ → Lean.RArray ℕ} (hS : S ≤ 512)
    (hdata : dataCheck S n maxNib aBound sigEnc eraseEnc labelEnc = true)
    (henc : ∀ g < S, sigField sigEnc g < 2 ^ (4 * (maxNib + 1)))
    (hpart : ∀ g < S, ∀ t < maxNib, sigNib (sigField sigEnc g) t ≤ 12)
    (hfact : ∀ k ≤ 48, factAt fmask factT k = k !)
    (hbase : ∀ t < S, ∀ s ≤ t,
      treeAt (cs 0) (pm 0) (w 0) (mask 0) (trees 0) (triIdx s t) =
        (if sigField sigEnc s = 0 ∧ sigField sigEnc t = 0 then 1 else 0))
    (hstep : ∀ j, 0 < j → j ≤ L → ∀ t < S, ∀ s ≤ t,
      treeAt (cs j) (pm j) (w j) (mask j) (trees j) (triIdx s t) =
        stepEntry (cs (j - 1)) (pm (j - 1)) (w (j - 1)) (mask (j - 1)) fmask eraseEnc factT
          (trees (j - 1)) s t) :
    ∀ j ≤ L, ∀ t < S, ∀ s ≤ t,
      treeAt (cs j) (pm j) (w j) (mask j) (trees j) (triIdx s t) =
        facMomentNat j (sigOf sigEnc s) (sigOf sigEnc t) := by
  have hrows := dataCheck_sig_sound hdata
  have hzero : ∀ g < S, (0 : ℕ) ∉ sigOf sigEnc g := fun g hg =>
    zero_notMem_decodeSig fun p hp => (hrows g hg).nib_pos p hp
  have hz : ∀ g, g < S → (sigField sigEnc g = 0 ↔ sigOf sigEnc g = 0) := fun g hg =>
    (decodeSig_eq_zero_iff (hrows g hg) rfl (henc g hg)).symm
  intro j
  induction j with
  | zero =>
    intro _ t ht s hs
    rw [hbase t ht s hs,
      PrimeGaps.facMomentNat_zero _ _ (hzero s (by omega)) (hzero t ht)]
    simp only [hz s (by omega), hz t ht]
  | succ k ih =>
    intro hk t ht s hs
    have hs' : s < S := by omega
    have hIH : ∀ a < S, ∀ b < S,
        treeAt (cs k) (pm k) (w k) (mask k) (trees k) (triIdx a b) =
          facMomentNat k (sigOf sigEnc a) (sigOf sigEnc b) := by
      intro a ha b hb
      rcases Nat.le_total a b with h | h
      · exact ih (by omega) b hb a h
      · rw [triIdx_comm, ih (by omega) a ha b h, facMomentNat_comm]
    rw [hstep (k + 1) (by omega) hk t ht s hs, Nat.add_sub_cancel, stepEntry_eq,
      PrimeGaps.facMomentNat_succ (hzero s hs') (hzero t ht)]
    refine row_sum_eq (hrows s hs') rfl rfl (by omega) hs'
      (fun p hp => hpart s hs' p (Nat.lt_of_lt_of_le hp (hrows s hs').count_le))
      (fun x => ∑ y ∈ insert 0 (sigOf sigEnc t).toFinset,
        (x + y)! * facMomentNat k ((sigOf sigEnc s).erase x) ((sigOf sigEnc t).erase y))
      (fun x2 τ₁ => ∑ j₂ ∈ Finset.range 5,
        if slotUsed (slotField eraseEnc t j₂) = true then
          factAt fmask factT (Nat.shiftLeft (x2 + slotPart2 (slotField eraseEnc t j₂)) 1) *
            treeAt (cs k) (pm k) (w k) (mask k) (trees k)
              (triIdx τ₁ (slotTarget (slotField eraseEnc t j₂)))
        else 0) ?_
    intro x2 τ₁ hx2 hτ₁ herase₁
    refine row_sum_eq (hrows t ht) rfl rfl (by omega) ht
      (fun p hp => hpart t ht p (Nat.lt_of_lt_of_le hp (hrows t ht).count_le))
      (fun y => (2 * x2 + y)! * facMomentNat k ((sigOf sigEnc s).erase (2 * x2))
        ((sigOf sigEnc t).erase y))
      (fun y2 τ₂ => factAt fmask factT (Nat.shiftLeft (x2 + y2) 1) *
        treeAt (cs k) (pm k) (w k) (mask k) (trees k) (triIdx τ₁ τ₂)) ?_
    intro y2 τ₂ hy2 hτ₂ herase₂
    rw [(by simp [Nat.shiftLeft_eq]; ring : Nat.shiftLeft (x2 + y2) 1 = 2 * x2 + 2 * y2),
      hfact (2 * x2 + 2 * y2) (by omega), hIH τ₁ hτ₁ τ₂ hτ₂, herase₁, herase₂]

end ladderSound

end PrimeGaps.Gap246
