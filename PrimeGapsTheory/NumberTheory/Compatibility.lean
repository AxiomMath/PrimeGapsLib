/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Nat.ChineseRemainder
public import PrimeGapsTheory.NumberTheory.Admissible
public import PrimeGapsTheory.Sieve.PermissibleSupport.FunctionW
import PrimeGapsTheory.Tactic.PaperTag

/-! # Compatible residues for the `W`-trick

A residue `v₀` is compatible with a finite set `H` modulo `W` when `v₀ + h` is coprime to `W`
for every `h ∈ H`. For an admissible `H` such a residue always exists below `W N`, which is what
makes the `W`-trick available.

## Main definitions

* `Finset.CompatibleWith`: `H.CompatibleWith W v₀` says `v₀ + h` is coprime to `W` for `h ∈ H`.

## Main results

* `Finset.Admissible.exists_compatibleWith`: an admissible `H` admits a compatible `v₀ < W N`.

## Implementation notes

The arguments of `Finset.CompatibleWith` are ordered so that, for fixed `H` and `W`, the partial
application `H.CompatibleWith W` is a predicate on `ℕ`.
-/

@[expose] public section

open PrimeGaps

namespace Finset

/-- A natural number `v₀` is *compatible* with some finite set `H` of natural numbers with respect
to some natural number `W` if `v₀ + h` is coprime to `W` for all `h ∈ H`.

`H.CompatibleWith W v₀` should be read as "`v₀` is compatible with `H` with respect to `W`." -/
@[pg_tag "bg246" "def_W_trick"]
def CompatibleWith (H : Finset ℕ) (W : ℕ) (v₀ : ℕ) : Prop := ∀ h ∈ H, (v₀ + h).Coprime W

lemma compatibleWith_iff_forall_coprime (H : Finset ℕ) (W : ℕ) (v₀ : ℕ) :
    H.CompatibleWith W v₀ ↔ ∀ h ∈ H, (v₀ + h).Coprime W := .rfl

lemma compatibleWith_iff_forall_gcd_eq_one (H : Finset ℕ) (W : ℕ) (v₀ : ℕ) :
    CompatibleWith H W v₀ ↔ ∀ h ∈ H, (v₀ + h).gcd W = 1 := .rfl

end Finset

open Nat Finset

namespace Finset.Admissible

open scoped sieveModulus

@[pg_tag "bg246" "lem_exists_v0"]
lemma exists_compatibleWith {H : Finset ℕ} (h_admissible : Admissible H) (N : ℕ) :
    ∃ v₀ < W N, H.CompatibleWith (W N) v₀ := by
  let S := {p ∈ range (⌊D₀ N⌋₊ + 1) | p.Prime}
  choose! v hvmem hvnot using
    fun p (hp : p ∈ S) ↦ h_admissible.exists_lt_forall_not_modEq (mem_filter.mp hp).2
  let cr := Nat.chineseRemainderOfFinset (fun p ↦ p - v p) id S
    (fun _ hp ↦ (mem_filter.mp hp).2.ne_zero)
    (fun _ hp _ hq h ↦ (Nat.coprime_primes (mem_filter.mp hp).2 (mem_filter.mp hq).2).mpr h)
  refine ⟨(cr : ℕ) % W N, Nat.mod_lt _ W_pos, fun h hh ↦ ?_⟩
  rw [W_eq_prod_primes_le, Nat.coprime_prod_right_iff]
  intro p hp
  rw [Nat.coprime_comm, (mem_filter.mp hp).2.coprime_iff_not_dvd, ← Nat.modEq_zero_iff_dvd]
  intro hv₀
  refine hvnot p hp h (mem_coe.mp hh) (Nat.ModEq.add_left_cancel' (p - v p) ?_)
  calc p - v p + h
      ≡ (cr : ℕ) + h [MOD p] := (cr.property p hp).symm.add_right h
    _ ≡ (cr : ℕ) % W N + h [MOD p] := by
        refine ((Nat.mod_modEq (cr : ℕ) (W N)).of_dvd ?_).symm.add_right h
        rw [W_eq_prod_primes_le]
        exact Finset.dvd_prod_of_mem _ hp
    _ ≡ 0 [MOD p] := hv₀
    _ ≡ p - v p + v p [MOD p] := by
        simp [Nat.sub_add_cancel (hvmem p hp).le, Nat.ModEq]

/-- An admissible tuple has, in each modulus `W N`, a residue whose shift by every coordinate is
coprime to `W N`. -/
lemma exists_zmod_gcd_eq_one {k : ℕ} {h : Fin k → ℕ}
    (h_admissible : Admissible (Finset.image h Finset.univ)) (N : ℕ) :
    ∃ v : ZMod (W N), ∀ i, ((v.val : ℤ) + h i).gcd (W N) = 1 := by
  obtain ⟨v₀, hlt, hcompat⟩ := h_admissible.exists_compatibleWith N
  refine ⟨(v₀ : ZMod (W N)), fun i ↦ ?_⟩
  have hco : (v₀ + h i).Coprime (W N) :=
    hcompat (h i) (Finset.mem_image_of_mem h (Finset.mem_univ i))
  have hcast : ((v₀ : ℤ) + (h i : ℤ)) = ((v₀ + h i : ℕ) : ℤ) := by push_cast; ring
  rwa [ZMod.val_natCast_of_lt hlt, hcast, Int.gcd_natCast_natCast]

end Finset.Admissible
