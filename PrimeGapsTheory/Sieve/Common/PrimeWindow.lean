/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.ZMod.Units
public import Mathlib.RingTheory.Int.Basic
public import PrimeGapsTheory.NumberTheory.PrimeCountingInterval

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Prime counts in a dyadic window

Relates integer-window prime-indicator sums to natural prime-counting functions.

## Main definitions

* `chiP`: The real-valued prime indicator on the integers.
* `window`: The integer interval from `N` to `2N`.

## Main results

* `windowSum_eq_primeCountingIoc`: Identifies the window sum with a prime count.
* `windowFilterSum_eq_zmodCount`: Identifies a residue-filtered window sum.
-/

@[expose] public section

open scoped Finset
open scoped BigOperators PrimeGaps

namespace PrimeGaps

/-- The prime indicator `χ_𝒫`, real-valued (so we can divide by `φ(q)`). -/
noncomputable def chiP (n : ℤ) : ℝ := if 0 < n ∧ Nat.Prime n.natAbs then 1 else 0

/-- The dyadic window `(N, 2N]`, as a `Finset ℤ`. -/
noncomputable def window (N : ℕ) : Finset ℤ := Finset.Ioc (N : ℤ) (2 * (N : ℤ))

/-- The prime indicator is nonnegative. -/
lemma chiP_nonneg (n : ℤ) : 0 ≤ chiP n := by unfold chiP; split <;> norm_num

/-- The prime indicator is bounded by `1`. -/
lemma chiP_le_one (n : ℤ) : chiP n ≤ 1 := by unfold chiP; split <;> norm_num

/-- On the window every `n` is positive, so `chiP n = if n.natAbs.Prime then 1 else 0`. -/
lemma chiP_of_mem_window {N : ℕ} {n : ℤ} (hn : n ∈ window N) :
    chiP n = if (n.natAbs).Prime then 1 else 0 := by
  have hpos : 0 < n := by
    simp only [window, Finset.mem_Ioc] at hn; omega
  unfold chiP
  simp [hpos]

/-- Arithmetic facts for the `Int.toNat` reindexing of the window. -/
private lemma window_toNat_facts {N : ℕ} {n : ℤ} (hn : n ∈ window N) :
    N < n.toNat ∧ n.toNat ≤ 2 * N ∧ (n.toNat : ℤ) = n ∧ n.toNat = n.natAbs := by
  simp only [window, Finset.mem_Ioc] at hn
  have hpos : (0 : ℤ) ≤ n := by omega
  have hval : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hpos
  have habs : (n.natAbs : ℤ) = n := Int.natAbs_of_nonneg hpos
  exact ⟨by omega, by omega, hval, by omega⟩

/-- `∑_{n ∈ (N, 2N]} χ_𝒫(n) = π(N, 2N]`. -/
theorem windowSum_eq_primeCountingIoc (N : ℕ) :
    (∑ n ∈ window N, chiP n) = (π(N, (2 * N)) : ℝ) := by
  rw [Finset.sum_congr rfl (fun n hn ↦ chiP_of_mem_window hn), Finset.sum_boole,
    Nat.primeCountingIoc, Nat.cast_inj]
  refine Finset.card_nbij' (fun n ↦ n.toNat) (fun m ↦ (m : ℤ)) ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_coe, Finset.mem_filter] at hn
    obtain ⟨hb1, hb2, _, hAbs⟩ := window_toNat_facts hn.1
    rw [Finset.mem_coe]
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hb1, hb2⟩, by simpa [hAbs] using hn.2⟩
  · intro m hm
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at hm
    rw [Finset.mem_coe]
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_Ioc.mpr ⟨by exact_mod_cast hm.1.1, by omega⟩ :
          (m : ℤ) ∈ window N), by simpa using hm.2⟩
  · intro n hn
    rw [Finset.mem_coe, Finset.mem_filter] at hn
    exact (window_toNat_facts hn.1).2.2.1
  · intro m _; simp

/-- `∑_{n ∈ (N, 2N], n ≡ a (q)} χ_𝒫(n)` counts the primes in `(N, 2N]` in the class `a : ZMod q`. -/
theorem windowFilterSum_eq_zmodCount (N q : ℕ) (a : ℤ) :
    (∑ n ∈ {n ∈ window N | n ≡ a [ZMOD (q : ℤ)]}, chiP n) =
      (ZMod.primeCountingIoc N (2 * N) (a : ZMod q) : ℝ) := by
  rw [Finset.sum_congr rfl (fun n hn ↦ chiP_of_mem_window (Finset.mem_of_mem_filter n hn)),
    Finset.sum_boole, ZMod.primeCountingIoc, Nat.cast_inj]
  refine Finset.card_nbij' (fun n ↦ n.toNat) (fun m ↦ (m : ℤ)) ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter] at hn
    obtain ⟨hb1, hb2, hval, hAbs⟩ := window_toNat_facts hn.1.1
    have hmod : n ≡ a [ZMOD (q : ℤ)] := hn.1.2
    rw [← ZMod.intCast_eq_intCast_iff] at hmod
    rw [Finset.mem_coe]
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hb1, hb2⟩,
      by simpa [hAbs] using hn.2, ?_⟩
    calc ((n.toNat : ℕ) : ZMod q) = ((n.toNat : ℤ) : ZMod q) := by push_cast; ring
      _ = ((n : ℤ) : ZMod q) := by rw [hval]
      _ = ((a : ℤ) : ZMod q) := hmod
  · intro m hm
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at hm
    have hcong : ((m : ℤ)) ≡ a [ZMOD (q : ℤ)] := by
      rw [← ZMod.intCast_eq_intCast_iff]
      calc (((m : ℤ)) : ZMod q) = ((m : ℕ) : ZMod q) := by push_cast; ring
        _ = ((a : ℤ) : ZMod q) := hm.2.2
    rw [Finset.mem_coe]
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
          ⟨by exact_mod_cast hm.1.1, by omega⟩, hcong⟩ :
        (m : ℤ) ∈ {n ∈ window N | n ≡ a [ZMOD (q : ℤ)]}),
       by simpa using hm.2.1⟩
  · intro n hn
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter] at hn
    exact (window_toNat_facts hn.1.1).2.2.1
  · intro m _; simp

/-- `(a: ZMod q)` is a unit when `a` is coprime to `q`. -/
lemma isUnit_intCast_of_gcd_eq_one {q : ℕ} {a : ℤ} (ha : Int.gcd a (q : ℤ) = 1) :
    IsUnit (a : ZMod q) :=
  (ZMod.coe_int_isUnit_iff_isCoprime a q).mpr
    (Int.isCoprime_iff_gcd_eq_one.mpr (by rw [Int.gcd_comm]; exact ha))


end PrimeGaps

@[expose] public section

open Finset

namespace PrimeGaps

/-- The number of primes in `(N, 2N]` equals `π(2N) − π(N)`. -/
@[pg_tag "bg246" "lem_XN_pi_diff"]
theorem primeCountingIoc_eq_primeCounting_diff (N : ℕ) : (π(N, (2 * N)) : ℝ) =
      (Nat.primeCounting (2 * N) : ℝ) - (Nat.primeCounting N : ℝ) :=
  Nat.cast_primeCountingIoc (by omega)

end PrimeGaps
