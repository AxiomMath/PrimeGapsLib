/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module


public import PrimeNumberTheoremAnd.Defs

/-!
# The Prime Counting Function in Arithmetic Progressions

This file develops the API for counting primes in a fixed congruence class. Given a real bound
`x`, a modulus `q : ℕ`, and a residue `a : ZMod q`, we count primes `≤ x` that are congruent
to `a` mod `q`.

## Main definitions

* `Nat.PrimeZMod n q a` — predicate "`n` is prime and `n ≡ a (mod q)`".
* `Nat.primesBelowZMod n q a` — `Finset` of primes `< n` lying in the class `a` mod `q`.
* `Nat.primesLEZMod n q a` — `Finset` of primes `≤ n` lying in the class `a` mod `q`;
  definitionally `Nat.primesBelowZMod (n + 1) q a`.
* `Real.primeCountingZMod x q a` — the number of primes at most `x` in the residue class `a`.

## Notation

* `π(x; q, a)` denotes `primeCountingZMod x q a`.
* `π(x)` denotes `primeCounting x`.

Both notations are scoped to the `Real` namespace.

## Main results

* `Real.primeCountingZMod_eq_nat_card` — the counting function as the cardinality of a subtype.
* `Real.primeCountingZMod_eq_card_finset_range` — the corresponding finite-range formula.
* `Real.primeCountingZMod_one_eq_primeCounting` — modulus one recovers `pi`.
-/

@[expose] public section

open Nat Finset

section PrimeZMod

/-- A natural number `n` is prime with respect to `a` modulo `q` if `n` is a prime number and is
congruent to `a` modulo `q`. -/
@[pp_nodot]
public def Nat.PrimeZMod (n q : ℕ) (a : ZMod q) : Prop := n.Prime ∧ n = a

namespace Nat

instance instDecidablePredPrimeZMod (q : ℕ) (a : ZMod q) :
    DecidablePred (fun x ↦ PrimeZMod x q a) := fun _ ↦ instDecidableAnd

end Nat

end PrimeZMod

section PrimeSetsZMod

namespace Nat

variable {p k n q : ℕ} {a : ZMod q}

/-- `Nat.primesBelowZMod n q a` is the set of primes less than `n` that are congruent to `a`
modulo `q`, as a `Finset`. -/
public def primesBelowZMod (n q : ℕ) (a : ZMod q) : Finset ℕ :=
  {p ∈ Finset.range n | p.PrimeZMod q a}

/-- `Nat.primesLEZMod n q a` is the set of primes less than or equal to `n` that are congruent
to `a` modulo `q`, as a `Finset`. -/
public def primesLEZMod (n q : ℕ) (a : ZMod q) : Finset ℕ := Nat.primesBelowZMod (n + 1) q a

lemma primesBelowZMod_eq_filter_range :
    Nat.primesBelowZMod n q a = filter (·.PrimeZMod q a) (range n) := rfl

lemma primesLEZMod_eq_filter_range :
    Nat.primesLEZMod n q a = filter (·.PrimeZMod q a) (range (n + 1)) := rfl

@[simp]
lemma primesBelowZMod_zero : Nat.primesBelowZMod 0 q a = ∅ := rfl

@[simp]
lemma primesBelowZMod_one : Nat.primesBelowZMod 1 q a = ∅ := rfl

@[simp]
lemma primesBelowZMod_two : Nat.primesBelowZMod 2 q a = ∅ := rfl

@[simp]
lemma primesLEZMod_zero : Nat.primesLEZMod 0 q a = ∅ := primesBelowZMod_one

@[simp]
lemma primesLEZMod_one : Nat.primesLEZMod 1 q a = ∅ := primesBelowZMod_two

theorem primesBelowZMod_eq_primesLEZMod_sub_one (n : ℕ) :
    Nat.primesBelowZMod n q a = Nat.primesLEZMod (n - 1) q a := by
  cases n <;> simp [Nat.primesLEZMod]

lemma mem_primesBelowZMod : n ∈ Nat.primesBelowZMod k q a ↔ n < k ∧ n.PrimeZMod q a := by
  simp [Nat.primesBelowZMod]

lemma mem_primesLEZMod : p ∈ Nat.primesLEZMod n q a ↔ p ≤ n ∧ p.PrimeZMod q a := by
  simp [Nat.primesLEZMod, mem_primesBelowZMod]

lemma primeZMod_of_mem_primesBelowZMod (h : p ∈ Nat.primesBelowZMod n q a) :
    p.PrimeZMod q a := (mem_filter.mp h).2

lemma primeZMod_of_mem_primesLEZMod (hp : p ∈ Nat.primesLEZMod n q a) :
    p.PrimeZMod q a := primeZMod_of_mem_primesBelowZMod hp

lemma prime_of_mem_primesBelowZMod (h : p ∈ Nat.primesBelowZMod n q a) : p.Prime :=
  (primeZMod_of_mem_primesBelowZMod h).1

lemma prime_of_mem_primesLEZMod (hp : p ∈ Nat.primesLEZMod n q a) : p.Prime :=
  (primeZMod_of_mem_primesLEZMod hp).1

lemma lt_of_mem_primesBelowZMod (h : p ∈ Nat.primesBelowZMod n q a) : p < n :=
  mem_range.mp <| mem_of_mem_filter p h

lemma le_of_mem_primesLEZMod (hp : p ∈ Nat.primesLEZMod n q a) : p ≤ n := (mem_primesLEZMod.mp hp).1

lemma one_lt_of_mem_primesBelowZMod (hp : p ∈ Nat.primesBelowZMod n q a) : 1 < p :=
  (prime_of_mem_primesBelowZMod hp).one_lt

lemma one_lt_of_mem_primesLEZMod (hp : p ∈ Nat.primesLEZMod n q a) : 1 < p :=
  one_lt_of_mem_primesBelowZMod hp

lemma two_le_of_mem_primesBelowZMod (hp : p ∈ Nat.primesBelowZMod n q a) : 2 ≤ p :=
  (prime_of_mem_primesBelowZMod hp).two_le

lemma two_le_of_mem_primesLEZMod (hp : p ∈ Nat.primesLEZMod n q a) : 2 ≤ p :=
  two_le_of_mem_primesBelowZMod hp

/-- A filter over `range n` by a predicate holding only at `c` and above is a filter over
`Ico c n`. -/
lemma filter_range_eq_filter_Ico {P : ℕ → Prop} [DecidablePred P] {c : ℕ}
    (hc : ∀ p, P p → c ≤ p) : filter P (range n) = filter P (Ico c n) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  exact ⟨fun ⟨hb, hP⟩ ↦ ⟨⟨hc p hP, hb⟩, hP⟩, fun ⟨⟨_, hb⟩, hP⟩ ↦ ⟨hb, hP⟩⟩

/-- A filter over `range (n + 1)` by a predicate holding only at `c` and above is a filter over
`Icc c n`. -/
lemma filter_range_succ_eq_filter_Icc {P : ℕ → Prop} [DecidablePred P] {c : ℕ}
    (hc : ∀ p, P p → c ≤ p) : filter P (range (n + 1)) = filter P (Icc c n) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, Nat.lt_succ_iff]
  exact ⟨fun ⟨hb, hP⟩ ↦ ⟨⟨hc p hP, hb⟩, hP⟩, fun ⟨⟨_, hb⟩, hP⟩ ↦ ⟨hb, hP⟩⟩

lemma primesBelowZMod_eq_filter_Ico_zero :
    Nat.primesBelowZMod n q a = filter (·.PrimeZMod q a) (Ico 0 n) :=
  filter_range_eq_filter_Ico fun _ _ ↦ Nat.zero_le _

lemma primesLEZMod_eq_filter_Icc_zero :
    Nat.primesLEZMod n q a = filter (·.PrimeZMod q a) (Icc 0 n) :=
  filter_range_succ_eq_filter_Icc fun _ _ ↦ Nat.zero_le _

lemma primesBelowZMod_eq_filter_Ico_one :
    Nat.primesBelowZMod n q a = filter (·.PrimeZMod q a) (Ico 1 n) :=
  filter_range_eq_filter_Ico fun _ hP ↦ hP.1.one_le

lemma primesLEZMod_eq_filter_Icc_one :
    Nat.primesLEZMod n q a = filter (·.PrimeZMod q a) (Icc 1 n) :=
  filter_range_succ_eq_filter_Icc fun _ hP ↦ hP.1.one_le

lemma primesBelowZMod_eq_filter_Ico_two :
    Nat.primesBelowZMod n q a = filter (·.PrimeZMod q a) (Ico 2 n) :=
  filter_range_eq_filter_Ico fun _ hP ↦ hP.1.two_le

lemma primesLEZMod_eq_filter_Icc_two :
    Nat.primesLEZMod n q a = filter (·.PrimeZMod q a) (Icc 2 n) :=
  filter_range_succ_eq_filter_Icc fun _ hP ↦ hP.1.two_le

lemma primesBelowZMod_mono : Monotone (Nat.primesBelowZMod · q a) :=
  (monotone_filter_left _).comp range_mono

lemma primesLEZMod_mono : Monotone (Nat.primesLEZMod · q a) :=
  fun _ _ h ↦ primesBelowZMod_mono (Nat.succ_le_succ h)

lemma primesBelowZMod_succ : Nat.primesBelowZMod (n + 1) q a =
    if n.PrimeZMod q a then insert n (Nat.primesBelowZMod n q a)
    else Nat.primesBelowZMod n q a := by
  rw [Nat.primesBelowZMod, Nat.primesBelowZMod, Finset.range_add_one, Finset.filter_insert]

lemma primesLEZMod_succ : Nat.primesLEZMod (n + 1) q a =
    if (n + 1).PrimeZMod q a then insert (n + 1) (Nat.primesLEZMod n q a)
    else Nat.primesLEZMod n q a :=
  primesBelowZMod_succ

lemma notMem_primesBelowZMod (n : ℕ) : n ∉ Nat.primesBelowZMod n q a :=
  fun hn ↦ (lt_of_mem_primesBelowZMod hn).false

lemma notMem_primesLEZMod (n : ℕ) : n + 1 ∉ Nat.primesLEZMod n q a := notMem_primesBelowZMod (n + 1)

lemma primesLEZMod_eq_primesBelowZMod_insert_iff :
    n.primesLEZMod q a = insert n (n.primesBelowZMod q a) ↔ n.PrimeZMod q a := by
  grind [Nat.primesLEZMod, primesBelowZMod_succ, notMem_primesBelowZMod]

end Nat

end PrimeSetsZMod

section PrimeCountingZMod

namespace Real

/-- The number of primes at most `x` in the residue class `a` modulo `q`. -/
public noncomputable def primeCountingZMod (x : ℝ) (q : ℕ) (a : ZMod q) : ℕ :=
  {p : ℕ | p.Prime ∧ (p : ZMod q) = a ∧ p ≤ x}.ncard

/-- Write `π(x; q, a)` for `Real.primeCountingZMod x q a`. -/
scoped[Real] notation "π(" x "; " q ", " a ")" => Real.primeCountingZMod x q a

/-- Write `π(x)` for the prime-counting function `pi x`. -/
scoped[Real] notation "π(" x ")" => pi x

lemma primeCountingZMod_def (x : ℝ) (q : ℕ) (a : ZMod q) :
    π(x; q, a) = {p : ℕ | p.Prime ∧ (p : ZMod q) = a ∧ p ≤ x}.ncard := rfl

lemma primeCountingZMod_setFinite (x : ℝ) (q : ℕ) (a : ZMod q) :
    ({p : ℕ | p.Prime ∧ (p : ZMod q) = a ∧ p ≤ x} : Set ℕ).Finite :=
  (Set.finite_Iic ⌊x⌋₊).subset fun _ hp ↦ (Nat.le_floor_iff' hp.1.ne_zero).2 hp.2.2

lemma primeCountingZMod_eq_nat_card (x : ℝ) (q : ℕ) (a : ZMod q) :
    π(x; q, a) = Nat.card {p : ℕ // p.Prime ∧ (p : ZMod q) = a ∧ p ≤ x} := rfl

lemma primeCountingZMod_eq_card_finset_range (x : ℝ) (q : ℕ) (a : ZMod q) :
    π(x; q, a) = #{p ∈ Finset.range (⌊x⌋₊ + 1) | (p : ℕ).Prime ∧ (p : ZMod q) = a} := by
  rw [primeCountingZMod_def, ← Set.ncard_coe_finset]
  congr 1
  ext p
  grind [Nat.le_floor_iff', Nat.Prime.ne_zero]

@[simp]
lemma primeCountingZMod_one_eq_primeCounting {x : ℝ} {a : ZMod 1} : π(x; 1, a) = π(x) := by
  rw [primeCountingZMod_eq_card_finset_range]
  simp [_root_.pi, primeCounting, primeCounting', count_eq_card_filter_range,
    Subsingleton.elim (α := ZMod 1) _ 0]

end Real

end PrimeCountingZMod
