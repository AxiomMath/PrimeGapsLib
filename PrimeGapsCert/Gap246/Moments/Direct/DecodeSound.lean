/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Moments.Direct.DataCheckSound


/-! # Soundness of signature decoding

Relates `cert246Kernel.decodeSig` to the nibble accessors `cert246Data.sigCount` and
`cert246Data.sigNib`, and describes the effect of `cert246Data.eraseAt` on the decoded multiset.
-/

@[expose] public section

namespace PrimeGaps.Gap246

section decodeSound

open cert246Kernel
open cert246Data (sigField sigCount sigNib eraseAt)

/-- The multiset of parts of signature `g` of the packed signature table `sigEnc`. -/
noncomputable def sigOf (sigEnc g : ℕ) : Multiset ℕ := decodeSig (sigField sigEnc g)

/-! ### Nibble arithmetic -/

/-- Nibble `i` of `x`. -/
private def nib (x i : ℕ) : ℕ := x / 2 ^ (4 * i) % 16

private theorem land_mask (x k : ℕ) : Nat.land x (Nat.sub (2 ^ k) 1) = x % 2 ^ k :=
  Nat.and_two_pow_sub_one_eq_mod x k

private theorem shiftRight_pow (x k : ℕ) : Nat.shiftRight x k = x / 2 ^ k :=
  Nat.shiftRight_eq_div_pow x k

private theorem shiftLeft_pow (x k : ℕ) : Nat.shiftLeft x k = x * 2 ^ k := Nat.shiftLeft_eq x k

private theorem land_fifteen (x : ℕ) : Nat.land x 15 = x % 16 := land_mask x 4

private theorem shl2 (n : ℕ) : Nat.shiftLeft n 2 = 4 * n := by
  simp [Nat.shiftLeft_eq, Nat.mul_comm]

private theorem sigCount_eq_mod (enc : ℕ) : sigCount enc = enc % 16 := land_fifteen enc

private theorem sigNib_eq_nib (enc j : ℕ) : sigNib enc j = nib enc (j + 1) := by
  unfold sigNib nib
  rw [land_fifteen, shl2, shiftRight_pow]

private theorem nib_zero (x : ℕ) : nib x 0 = x % 16 := by simp [nib]

/-- Nibbles below the split point of `L + H * 2 ^ (4 * n)` come from `L`. -/
private theorem nib_add_of_lt {L H n i : ℕ} (hi : i < n) :
    nib (L + H * 2 ^ (4 * n)) i = nib L i := by
  have hk : H * 2 ^ (4 * n) = 2 ^ (4 * i) * (16 * (H * 2 ^ (4 * (n - i) - 4))) := by
    rw [(by omega : 4 * n = 4 * i + (4 + (4 * (n - i) - 4))), pow_add, pow_add]
    ring_nf
  unfold nib
  rw [hk, Nat.add_mul_div_left _ _ (Nat.two_pow_pos (4 * i)), Nat.add_mul_mod_self_left]

/-- Nibbles at or above the split point of `L + H * 2 ^ (4 * n)` come from `H`. -/
private theorem nib_add_of_ge {L H n i : ℕ} (hL : L < 2 ^ (4 * n)) (hi : n ≤ i) :
    nib (L + H * 2 ^ (4 * n)) i = nib H (i - n) := by
  have hsplit : (2 : ℕ) ^ (4 * i) = 2 ^ (4 * n) * 2 ^ (4 * (i - n)) := by
    rw [← pow_add, (by omega : 4 * n + 4 * (i - n) = 4 * i)]
  unfold nib
  rw [hsplit, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (Nat.two_pow_pos (4 * n)),
    Nat.div_eq_of_lt hL, Nat.zero_add]

/-- For a positive low nibble, nibble `i > 0` of `x - 1` agrees with nibble `i` of `x`. -/
private theorem nib_sub_one {x i : ℕ} (hx : 0 < x % 16) (hi : 0 < i) :
    nib (x - 1) i = nib x i := by
  have h16 : (2 : ℕ) ^ (4 * i) = 16 * 2 ^ (4 * (i - 1)) := by
    rw [(by norm_num : (16 : ℕ) = 2 ^ 4), ← pow_add, (by omega : 4 + 4 * (i - 1) = 4 * i)]
  unfold nib
  rw [h16, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
    (by omega : (x - 1) / 16 = x / 16)]

private theorem nib_div (x k j : ℕ) : nib (x / 2 ^ (4 * k)) j = nib x (k + j) := by
  unfold nib
  rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.mul_add]

/-! ### The effect of `cert246Data.eraseAt` on the nibbles -/

private theorem eraseAt_eq (enc t : ℕ) :
    eraseAt enc t =
      enc % 2 ^ (4 * (t + 1)) - 1 + enc / 2 ^ (4 * (t + 2)) * 2 ^ (4 * (t + 1)) := by
  unfold eraseAt
  rw [shl2, shl2, shiftLeft_pow, Nat.one_mul, land_mask, shiftRight_pow, shiftLeft_pow]
  rfl

/-- Erasing nibble `t` decrements the count nibble, reproduces the nibbles below `t + 1`,
and pulls every higher nibble down one place. -/
private theorem nib_eraseAt {enc t : ℕ} (ht : t < sigCount enc) (i : ℕ) :
    nib (eraseAt enc t) i =
      if i = 0 then sigCount enc - 1 else if i < t + 1 then nib enc i else nib enc (i + 1) := by
  have hAmod : enc % 2 ^ (4 * (t + 1)) % 16 = enc % 16 := Nat.mod_mod_of_dvd enc
    (by rw [(by norm_num : (16 : ℕ) = 2 ^ 4)]; exact Nat.pow_dvd_pow 2 (by omega))
  have hcount : sigCount enc = enc % 16 := sigCount_eq_mod enc
  have hmod : enc % 2 ^ (4 * (t + 1)) < 2 ^ (4 * (t + 1)) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hApos : 0 < enc % 2 ^ (4 * (t + 1)) % 16 := by omega
  have hencsplit : enc =
      enc % 2 ^ (4 * (t + 1)) + enc / 2 ^ (4 * (t + 1)) * 2 ^ (4 * (t + 1)) :=
    (Nat.mod_add_div' enc _).symm
  rw [eraseAt_eq]
  split_ifs with h1 h2
  · rw [h1, nib_add_of_lt (by omega), nib_zero]
    omega
  · rw [nib_add_of_lt h2, nib_sub_one hApos (by omega)]
    conv_rhs => rw [hencsplit]
    rw [nib_add_of_lt h2]
  · rw [nib_add_of_ge (by omega) (by omega), nib_div]
    congr 1
    omega

private theorem sigCount_eraseAt {enc t : ℕ} (ht : t < sigCount enc) :
    sigCount (eraseAt enc t) = sigCount enc - 1 := by
  rw [sigCount_eq_mod (eraseAt enc t), ← nib_zero, nib_eraseAt ht, if_pos rfl]

private theorem sigNib_eraseAt {enc t : ℕ} (ht : t < sigCount enc) (q : ℕ) :
    sigNib (eraseAt enc t) q = if q < t then sigNib enc q else sigNib enc (q + 1) := by
  grind [sigNib_eq_nib, nib_eraseAt]

/-! ### The decoded multiset as a mapped list -/

/-- `cert246Kernel.decodeSig` maps twice the nibble over the part positions. -/
theorem decodeSig_eq_map (enc : ℕ) :
    decodeSig enc = ↑((List.range (sigCount enc)).map fun p => 2 * sigNib enc p) := by
  rw [sigCount_eq_mod]
  refine congrArg _ (List.map_congr_left fun j _ => ?_)
  rw [sigNib_eq_nib, nib, Nat.shiftRight_eq_div_pow]

/-- A signature with only positive nibbles decodes to a multiset of positive parts. -/
theorem zero_notMem_decodeSig {enc : ℕ} (h : ∀ p < sigCount enc, 0 < sigNib enc p) :
    (0 : ℕ) ∉ decodeSig enc := by
  simp only [decodeSig_eq_map, Multiset.mem_coe, List.mem_map, List.mem_range, not_exists]
  grind

/-! ### Erasing one position from a mapped range -/

/-- Erasing the value at position `t` from a range map is the range map that skips `t`. -/
private theorem coe_map_range_erase (f : ℕ → ℕ) :
    ∀ n t, t ≤ n →
      (↑((List.range (n + 1)).map f) : Multiset ℕ).erase (f t) =
        ↑((List.range n).map fun q => if q < t then f q else f (q + 1)) := by
  intro n
  induction n with
  | zero =>
    intro t ht
    obtain rfl : t = 0 := by omega
    simp
  | succ n ih =>
    intro t ht
    rw [List.range_succ, List.map_append, ← Multiset.coe_add]
    rcases Nat.lt_or_ge t (n + 1) with hlt | hge
    · rw [Multiset.erase_add_left_pos _
        (Multiset.mem_coe.mpr (List.mem_map_of_mem (List.mem_range.mpr hlt))),
        ih t (by omega), List.range_succ, List.map_append, ← Multiset.coe_add]
      simp [Nat.not_lt.2 (by omega : t ≤ n)]
    · obtain rfl : t = n + 1 := by omega
      rw [(by rw [add_comm]; rfl : (↑((List.range (n + 1)).map f) : Multiset ℕ) +
          ↑(List.map f [n + 1]) = f (n + 1) ::ₘ ↑((List.range (n + 1)).map f)),
        Multiset.erase_cons_head]
      exact congrArg _ (List.map_congr_left fun q hq => (if_pos (List.mem_range.mp hq)).symm)

/-- Erasing nibble `t` erases one copy of that part from the decoded multiset. -/
theorem decodeSig_eraseAt {enc t : ℕ} (ht : t < sigCount enc) :
    decodeSig (eraseAt enc t) = (decodeSig enc).erase (2 * sigNib enc t) := by
  obtain ⟨n, hn⟩ : ∃ n, sigCount enc = n + 1 := ⟨sigCount enc - 1, by omega⟩
  rw [decodeSig_eq_map, decodeSig_eq_map, sigCount_eraseAt ht, hn, Nat.add_sub_cancel,
    coe_map_range_erase (fun p => 2 * sigNib enc p) n t (by omega)]
  refine congrArg _ (List.map_congr_left fun q _ => ?_)
  rw [sigNib_eraseAt ht]
  split <;> rfl

/-! ### Distinct-value starts enumerate the support -/

/-- Every part position shares its nibble with a distinct-value start. -/
private theorem exists_start {enc : ℕ} :
    ∀ p < sigCount enc, ∃ q < sigCount enc,
      (q = 0 ∨ sigNib enc q ≠ sigNib enc (q - 1)) ∧ sigNib enc q = sigNib enc p := by
  intro p
  induction p with
  | zero => exact fun hp => ⟨0, hp, Or.inl rfl, rfl⟩
  | succ p ih =>
    intro hp
    by_cases hstart : p + 1 = 0 ∨ sigNib enc (p + 1) ≠ sigNib enc (p + 1 - 1)
    · exact ⟨p + 1, hp, hstart, rfl⟩
    · obtain ⟨q, hq, hqs, hqv⟩ := ih (by omega)
      grind

/-- The images of the distinct-value starts are exactly the distinct decoded parts. -/
theorem distinct_starts_enumerate (enc : ℕ) :
    {p ∈ Finset.range (sigCount enc) |
        p = 0 ∨ sigNib enc p ≠ sigNib enc (p - 1)}.image
      (fun p => 2 * sigNib enc p) = (decodeSig enc).toFinset := by
  ext v
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range, Multiset.mem_toFinset,
    decodeSig_eq_map, Multiset.mem_coe, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨p, ⟨hp, -⟩, rfl⟩
    exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨q, hq, hqs, hqv⟩ := exists_start p hp
    exact ⟨q, ⟨hq, hqs⟩, by rw [hqv]⟩

end decodeSound

end PrimeGaps.Gap246
