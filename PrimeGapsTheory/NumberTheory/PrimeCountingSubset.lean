/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module


public import PrimeGapsTheory.NumberTheory.PrimeCountingZMod

/-!
# The Prime Counting Function in Arithmetic Progressions, restricted to a Subset

This file extends `PrimeGapsTheory.NumberTheory.PrimeCountingZMod` by restricting prime counts
to a fixed subset `S : Set ℕ`.

The natural-number API consists of predicates and finite sets used to describe the counted primes.
The counting functions themselves take real bounds and are defined directly with `Set.ncard`, so
they apply to arbitrary subsets without a decidable-membership hypothesis.

## Main definitions

* `Nat.PrimeWithin n S` — predicate “`n` is prime and `n ∈ S`”.
* `Nat.PrimeZModWithin n q a S` — the same predicate with the congruence `n ≡ a (mod q)`.
* `Nat.primesBelowWithin`, `Nat.primesLEWithin` — finite sets of primes in `S`.
* `Nat.primesBelowZModWithin`, `Nat.primesLEZModWithin` — their congruence-restricted
  analogues.
* `Real.primeCountingWithin x S` — the number of primes at most `x` in `S`.
* `Real.primeCountingZModWithin x q a S` — the number also congruent to `a` modulo `q`.

The notations `π[S](x)` and `π[S](x; q, a)` are scoped to the `Real` namespace.

## Main results

* `Real.primeCountingWithin_eq_nat_card` and
  `Real.primeCountingZModWithin_eq_nat_card` express the counts as subtype cardinalities.
* `Real.primeCountingWithin_eq_card_finset_range` and
  `Real.primeCountingZModWithin_eq_card_finset_range` give finite-range formulas.
* The `…_univ`, `…_inter_setOf_prime`, and `…_setOf_prime` lemmas relate restricted
  counting to unrestricted counting.
* `Real.primeCountingZModWithin_one_eq_primeCountingWithin` removes the vacuous
  modulus-one condition.
-/

@[expose] public section

open Nat Finset

/-- A natural number `n` is prime *with respect to a subset* `S` if `n` is prime and
`n` lies in `S`. -/
@[pp_nodot]
public def Nat.PrimeWithin (n : ℕ) (S : Set ℕ) : Prop := n.Prime ∧ n ∈ S

/-- A natural number `n` is prime *with respect to* `S` *and to the residue class* `a`
*modulo* `q` if `n` is prime, congruent to `a` modulo `q`, and lies in `S`. -/
@[pp_nodot]
public def Nat.PrimeZModWithin (n q : ℕ) (a : ZMod q) (S : Set ℕ) : Prop := n.PrimeZMod q a ∧ n ∈ S

namespace Nat

instance instDecidablePredPrimeWithin (S : Set ℕ) [DecidablePred (· ∈ S)] :
    DecidablePred (fun x ↦ PrimeWithin x S) := fun _ ↦ instDecidableAnd

instance instDecidablePredPrimeZModWithin (q : ℕ) (a : ZMod q) (S : Set ℕ)
    [DecidablePred (· ∈ S)] : DecidablePred (fun x ↦ PrimeZModWithin x q a S) :=
  fun _ ↦ instDecidableAnd

lemma primeZModWithin_iff (n q : ℕ) (a : ZMod q) (S : Set ℕ) :
    n.PrimeZModWithin q a S ↔ n.Prime ∧ (n : ZMod q) = a ∧ n ∈ S := and_assoc

variable {p k n q : ℕ} {a : ZMod q} {S : Set ℕ}

/-- `Nat.primesBelowWithin n S` is the set of primes less than `n` that lie in `S`,
as a `Finset`. -/
public def primesBelowWithin (n : ℕ) (S : Set ℕ) [DecidablePred (· ∈ S)] : Finset ℕ :=
  {p ∈ Finset.range n | p.PrimeWithin S}

/-- `Nat.primesLEWithin n S` is the set of primes less than or equal to `n` that lie
in `S`, as a `Finset`. -/
public def primesLEWithin (n : ℕ) (S : Set ℕ) [DecidablePred (· ∈ S)] : Finset ℕ :=
  Nat.primesBelowWithin (n + 1) S

/-- `Nat.primesBelowZModWithin n q a S` is the set of primes less than `n` that lie
in `S` and are congruent to `a` modulo `q`, as a `Finset`. -/
public def primesBelowZModWithin (n q : ℕ) (a : ZMod q) (S : Set ℕ)
    [DecidablePred (· ∈ S)] : Finset ℕ :=
  {p ∈ Finset.range n | p.PrimeZModWithin q a S}

/-- `Nat.primesLEZModWithin n q a S` is the set of primes less than or equal to `n`
that lie in `S` and are congruent to `a` modulo `q`, as a `Finset`. -/
public def primesLEZModWithin (n q : ℕ) (a : ZMod q) (S : Set ℕ)
    [DecidablePred (· ∈ S)] : Finset ℕ :=
  Nat.primesBelowZModWithin (n + 1) q a S

variable [DecidablePred (· ∈ S)]

lemma primesBelowWithin_eq_filter_range :
    Nat.primesBelowWithin n S = filter (·.PrimeWithin S) (range n) := rfl

lemma primesLEWithin_eq_filter_range :
    Nat.primesLEWithin n S = filter (·.PrimeWithin S) (range (n + 1)) := rfl

lemma primesBelowZModWithin_eq_filter_range :
    Nat.primesBelowZModWithin n q a S = filter (·.PrimeZModWithin q a S) (range n) := rfl

lemma primesLEZModWithin_eq_filter_range :
    Nat.primesLEZModWithin n q a S = filter (·.PrimeZModWithin q a S) (range (n + 1)) := rfl

@[simp]
lemma primesBelowWithin_zero : Nat.primesBelowWithin 0 S = ∅ := rfl

@[simp]
lemma primesBelowWithin_one : Nat.primesBelowWithin 1 S = ∅ := rfl

@[simp]
lemma primesBelowWithin_two : Nat.primesBelowWithin 2 S = ∅ := rfl

@[simp]
lemma primesLEWithin_zero : Nat.primesLEWithin 0 S = ∅ := primesBelowWithin_one

@[simp]
lemma primesLEWithin_one : Nat.primesLEWithin 1 S = ∅ := primesBelowWithin_two

@[simp]
lemma primesBelowZModWithin_zero : Nat.primesBelowZModWithin 0 q a S = ∅ := rfl

@[simp]
lemma primesBelowZModWithin_one : Nat.primesBelowZModWithin 1 q a S = ∅ := rfl

@[simp]
lemma primesBelowZModWithin_two : Nat.primesBelowZModWithin 2 q a S = ∅ := rfl

@[simp]
lemma primesLEZModWithin_zero : Nat.primesLEZModWithin 0 q a S = ∅ := primesBelowZModWithin_one

@[simp]
lemma primesLEZModWithin_one : Nat.primesLEZModWithin 1 q a S = ∅ := primesBelowZModWithin_two

theorem primesBelowWithin_eq_primesLEWithin_sub_one (n : ℕ) :
    Nat.primesBelowWithin n S = Nat.primesLEWithin (n - 1) S := by
  cases n <;> simp [primesLEWithin]

theorem primesBelowZModWithin_eq_primesLEZModWithin_sub_one (n : ℕ) :
    Nat.primesBelowZModWithin n q a S = Nat.primesLEZModWithin (n - 1) q a S := by
  cases n <;> simp [primesLEZModWithin]

lemma mem_primesBelowWithin : n ∈ Nat.primesBelowWithin k S ↔ n < k ∧ n.PrimeWithin S := by
  simp [primesBelowWithin]

lemma mem_primesLEWithin : p ∈ Nat.primesLEWithin n S ↔ p ≤ n ∧ p.PrimeWithin S := by
  simp [primesLEWithin, mem_primesBelowWithin]

lemma mem_primesBelowZModWithin :
    n ∈ Nat.primesBelowZModWithin k q a S ↔ n < k ∧ n.PrimeZModWithin q a S := by
  simp [primesBelowZModWithin]

lemma mem_primesLEZModWithin :
    p ∈ Nat.primesLEZModWithin n q a S ↔ p ≤ n ∧ p.PrimeZModWithin q a S := by
  simp [primesLEZModWithin, mem_primesBelowZModWithin]

lemma primeWithin_of_mem_primesBelowWithin (h : p ∈ Nat.primesBelowWithin n S) :
    p.PrimeWithin S := (mem_filter.mp h).2

lemma primeWithin_of_mem_primesLEWithin (hp : p ∈ Nat.primesLEWithin n S) :
    p.PrimeWithin S := primeWithin_of_mem_primesBelowWithin hp

lemma prime_of_mem_primesBelowWithin (h : p ∈ Nat.primesBelowWithin n S) : p.Prime :=
  (primeWithin_of_mem_primesBelowWithin h).1

lemma prime_of_mem_primesLEWithin (hp : p ∈ Nat.primesLEWithin n S) : p.Prime :=
  (primeWithin_of_mem_primesLEWithin hp).1

lemma mem_within_of_mem_primesBelowWithin (h : p ∈ Nat.primesBelowWithin n S) : p ∈ S :=
  (primeWithin_of_mem_primesBelowWithin h).2

lemma mem_within_of_mem_primesLEWithin (hp : p ∈ Nat.primesLEWithin n S) : p ∈ S :=
  (primeWithin_of_mem_primesLEWithin hp).2

lemma primeZModWithin_of_mem_primesBelowZModWithin (h : p ∈ Nat.primesBelowZModWithin n q a S) :
    p.PrimeZModWithin q a S := (mem_filter.mp h).2

lemma primeZModWithin_of_mem_primesLEZModWithin (hp : p ∈ Nat.primesLEZModWithin n q a S) :
    p.PrimeZModWithin q a S := primeZModWithin_of_mem_primesBelowZModWithin hp

lemma primeZMod_of_mem_primesBelowZModWithin
    (h : p ∈ Nat.primesBelowZModWithin n q a S) : p.PrimeZMod q a :=
  (primeZModWithin_of_mem_primesBelowZModWithin h).1

lemma primeZMod_of_mem_primesLEZModWithin
    (hp : p ∈ Nat.primesLEZModWithin n q a S) : p.PrimeZMod q a :=
  (primeZModWithin_of_mem_primesLEZModWithin hp).1

lemma prime_of_mem_primesBelowZModWithin (h : p ∈ Nat.primesBelowZModWithin n q a S) : p.Prime :=
  (primeZMod_of_mem_primesBelowZModWithin h).1

lemma prime_of_mem_primesLEZModWithin (hp : p ∈ Nat.primesLEZModWithin n q a S) : p.Prime :=
  (primeZMod_of_mem_primesLEZModWithin hp).1

lemma mem_within_of_mem_primesBelowZModWithin (h : p ∈ Nat.primesBelowZModWithin n q a S) : p ∈ S :=
  (primeZModWithin_of_mem_primesBelowZModWithin h).2

lemma mem_within_of_mem_primesLEZModWithin (hp : p ∈ Nat.primesLEZModWithin n q a S) : p ∈ S :=
  (primeZModWithin_of_mem_primesLEZModWithin hp).2

lemma lt_of_mem_primesBelowWithin (h : p ∈ Nat.primesBelowWithin n S) : p < n :=
  mem_range.mp <| mem_of_mem_filter p h

lemma le_of_mem_primesLEWithin (hp : p ∈ Nat.primesLEWithin n S) : p ≤ n :=
  (mem_primesLEWithin.mp hp).1

lemma lt_of_mem_primesBelowZModWithin (h : p ∈ Nat.primesBelowZModWithin n q a S) : p < n :=
  mem_range.mp <| mem_of_mem_filter p h

lemma le_of_mem_primesLEZModWithin (hp : p ∈ Nat.primesLEZModWithin n q a S) : p ≤ n :=
  (mem_primesLEZModWithin.mp hp).1

lemma one_lt_of_mem_primesBelowWithin (hp : p ∈ Nat.primesBelowWithin n S) : 1 < p :=
  (prime_of_mem_primesBelowWithin hp).one_lt

lemma one_lt_of_mem_primesLEWithin (hp : p ∈ Nat.primesLEWithin n S) : 1 < p :=
  one_lt_of_mem_primesBelowWithin hp

lemma two_le_of_mem_primesBelowWithin (hp : p ∈ Nat.primesBelowWithin n S) : 2 ≤ p :=
  (prime_of_mem_primesBelowWithin hp).two_le

lemma two_le_of_mem_primesLEWithin (hp : p ∈ Nat.primesLEWithin n S) : 2 ≤ p :=
  two_le_of_mem_primesBelowWithin hp

lemma one_lt_of_mem_primesBelowZModWithin (hp : p ∈ Nat.primesBelowZModWithin n q a S) : 1 < p :=
  (prime_of_mem_primesBelowZModWithin hp).one_lt

lemma one_lt_of_mem_primesLEZModWithin (hp : p ∈ Nat.primesLEZModWithin n q a S) : 1 < p :=
  one_lt_of_mem_primesBelowZModWithin hp

lemma two_le_of_mem_primesBelowZModWithin (hp : p ∈ Nat.primesBelowZModWithin n q a S) : 2 ≤ p :=
  (prime_of_mem_primesBelowZModWithin hp).two_le

lemma two_le_of_mem_primesLEZModWithin (hp : p ∈ Nat.primesLEZModWithin n q a S) : 2 ≤ p :=
  two_le_of_mem_primesBelowZModWithin hp

lemma primesBelowWithin_eq_filter_Ico_zero :
    Nat.primesBelowWithin n S = filter (·.PrimeWithin S) (Ico 0 n) :=
  filter_range_eq_filter_Ico fun _ _ ↦ Nat.zero_le _

lemma primesLEWithin_eq_filter_Icc_zero :
    Nat.primesLEWithin n S = filter (·.PrimeWithin S) (Icc 0 n) :=
  filter_range_succ_eq_filter_Icc fun _ _ ↦ Nat.zero_le _

lemma primesBelowWithin_eq_filter_Ico_one :
    Nat.primesBelowWithin n S = filter (·.PrimeWithin S) (Ico 1 n) :=
  filter_range_eq_filter_Ico fun _ hP ↦ hP.1.one_le

lemma primesLEWithin_eq_filter_Icc_one :
    Nat.primesLEWithin n S = filter (·.PrimeWithin S) (Icc 1 n) :=
  filter_range_succ_eq_filter_Icc fun _ hP ↦ hP.1.one_le

lemma primesBelowWithin_eq_filter_Ico_two :
    Nat.primesBelowWithin n S = filter (·.PrimeWithin S) (Ico 2 n) :=
  filter_range_eq_filter_Ico fun _ hP ↦ hP.1.two_le

lemma primesLEWithin_eq_filter_Icc_two :
    Nat.primesLEWithin n S = filter (·.PrimeWithin S) (Icc 2 n) :=
  filter_range_succ_eq_filter_Icc fun _ hP ↦ hP.1.two_le

lemma primesBelowZModWithin_eq_filter_Ico_zero :
    Nat.primesBelowZModWithin n q a S = filter (·.PrimeZModWithin q a S) (Ico 0 n) :=
  filter_range_eq_filter_Ico fun _ _ ↦ Nat.zero_le _

lemma primesLEZModWithin_eq_filter_Icc_zero :
    Nat.primesLEZModWithin n q a S = filter (·.PrimeZModWithin q a S) (Icc 0 n) :=
  filter_range_succ_eq_filter_Icc fun _ _ ↦ Nat.zero_le _

lemma primesBelowZModWithin_eq_filter_Ico_one :
    Nat.primesBelowZModWithin n q a S = filter (·.PrimeZModWithin q a S) (Ico 1 n) :=
  filter_range_eq_filter_Ico fun _ hP ↦ hP.1.1.one_le

lemma primesLEZModWithin_eq_filter_Icc_one :
    Nat.primesLEZModWithin n q a S = filter (·.PrimeZModWithin q a S) (Icc 1 n) :=
  filter_range_succ_eq_filter_Icc fun _ hP ↦ hP.1.1.one_le

lemma primesBelowZModWithin_eq_filter_Ico_two :
    Nat.primesBelowZModWithin n q a S = filter (·.PrimeZModWithin q a S) (Ico 2 n) :=
  filter_range_eq_filter_Ico fun _ hP ↦ hP.1.1.two_le

lemma primesLEZModWithin_eq_filter_Icc_two :
    Nat.primesLEZModWithin n q a S = filter (·.PrimeZModWithin q a S) (Icc 2 n) :=
  filter_range_succ_eq_filter_Icc fun _ hP ↦ hP.1.1.two_le

lemma primesBelowWithin_mono : Monotone (Nat.primesBelowWithin · S) :=
  (monotone_filter_left _).comp range_mono

lemma primesLEWithin_mono : Monotone (Nat.primesLEWithin · S) :=
  fun _ _ h ↦ primesBelowWithin_mono (Nat.succ_le_succ h)

lemma primesBelowZModWithin_mono : Monotone (Nat.primesBelowZModWithin · q a S) :=
  (monotone_filter_left _).comp range_mono

lemma primesLEZModWithin_mono : Monotone (Nat.primesLEZModWithin · q a S) :=
  fun _ _ h ↦ primesBelowZModWithin_mono (Nat.succ_le_succ h)

lemma primesBelowWithin_succ : Nat.primesBelowWithin (n + 1) S =
    if n.PrimeWithin S then insert n (Nat.primesBelowWithin n S)
    else Nat.primesBelowWithin n S := by
  simp [primesBelowWithin_eq_filter_range, range_add_one, filter_insert]

lemma primesLEWithin_succ : Nat.primesLEWithin (n + 1) S =
    if (n + 1).PrimeWithin S then insert (n + 1) (Nat.primesLEWithin n S)
    else Nat.primesLEWithin n S :=
  primesBelowWithin_succ

lemma primesBelowZModWithin_succ : Nat.primesBelowZModWithin (n + 1) q a S =
    if n.PrimeZModWithin q a S then insert n (Nat.primesBelowZModWithin n q a S)
    else Nat.primesBelowZModWithin n q a S := by
  simp [primesBelowZModWithin_eq_filter_range, range_add_one, filter_insert]

lemma primesLEZModWithin_succ : Nat.primesLEZModWithin (n + 1) q a S =
    if (n + 1).PrimeZModWithin q a S then insert (n + 1) (Nat.primesLEZModWithin n q a S)
    else Nat.primesLEZModWithin n q a S :=
  primesBelowZModWithin_succ

lemma notMem_primesBelowWithin (n : ℕ) : n ∉ Nat.primesBelowWithin n S :=
  fun hn ↦ (lt_of_mem_primesBelowWithin hn).false

lemma notMem_primesLEWithin (n : ℕ) : n + 1 ∉ Nat.primesLEWithin n S :=
  notMem_primesBelowWithin (n + 1)

lemma notMem_primesBelowZModWithin (n : ℕ) : n ∉ Nat.primesBelowZModWithin n q a S :=
  fun hn ↦ (lt_of_mem_primesBelowZModWithin hn).false

lemma notMem_primesLEZModWithin (n : ℕ) : n + 1 ∉ Nat.primesLEZModWithin n q a S :=
  notMem_primesBelowZModWithin (n + 1)

lemma primesLEWithin_eq_primesBelowWithin_insert_iff :
    n.primesLEWithin S = insert n (n.primesBelowWithin S) ↔ n.PrimeWithin S := by
  grind [Nat.primesLEWithin, primesBelowWithin_succ, notMem_primesBelowWithin]

lemma primesLEZModWithin_eq_primesBelowZModWithin_insert_iff :
    n.primesLEZModWithin q a S = insert n (n.primesBelowZModWithin q a S) ↔
      n.PrimeZModWithin q a S := by
  grind [Nat.primesLEZModWithin, primesBelowZModWithin_succ, notMem_primesBelowZModWithin]

end Nat

namespace Real

section

variable (x : ℝ) (q : ℕ) (a : ZMod q) (S : Set ℕ)

/-- The number of primes at most `x` lying in `S`. -/
public noncomputable def primeCountingWithin : ℕ :=
  {p : ℕ | p.Prime ∧ p ∈ S ∧ p ≤ x}.ncard

/-- The number of primes at most `x` lying in `S` and in the residue class `a`
modulo `q`. -/
public noncomputable def primeCountingZModWithin : ℕ :=
  {p : ℕ | p.Prime ∧ (p : ZMod q) = a ∧ p ∈ S ∧ p ≤ x}.ncard

/-- Write `π[S](x; q, a)` for `Real.primeCountingZModWithin x q a S`. -/
scoped[Real] notation "π[" S "](" x "; " q ", " a ")" =>
  Real.primeCountingZModWithin x q a S

/-- Write `π[S](x)` for `Real.primeCountingWithin x S`. -/
scoped[Real] notation "π[" S "](" x ")" => Real.primeCountingWithin x S

lemma primeCountingWithin_def : π[S](x) = {p : ℕ | p.Prime ∧ p ∈ S ∧ p ≤ x}.ncard := rfl

lemma primeCountingZModWithin_def :
    π[S](x; q, a) =
      {p : ℕ | p.Prime ∧ (p : ZMod q) = a ∧ p ∈ S ∧ p ≤ x}.ncard := rfl

lemma primeCountingWithin_set_finite : ({p : ℕ | p.Prime ∧ p ∈ S ∧ p ≤ x} : Set ℕ).Finite :=
  (Set.finite_Iic ⌊x⌋₊).subset fun _ ⟨_, _, hpx⟩ ↦ Nat.le_floor hpx

lemma primeCountingZModWithin_set_finite :
    ({p : ℕ | p.Prime ∧ (p : ZMod q) = a ∧ p ∈ S ∧ p ≤ x} : Set ℕ).Finite :=
  (Set.finite_Iic ⌊x⌋₊).subset fun _ ⟨_, _, _, hpx⟩ ↦ Nat.le_floor hpx

lemma primeCountingWithin_eq_nat_card : π[S](x) = Nat.card {p : ℕ // p.Prime ∧ p ∈ S ∧ p ≤ x} := rfl

lemma primeCountingZModWithin_eq_nat_card :
    π[S](x; q, a) = Nat.card {p : ℕ // p.Prime ∧ (p : ZMod q) = a ∧ p ∈ S ∧ p ≤ x} := rfl

variable [DecidablePred (· ∈ S)]

lemma primeCountingWithin_eq_card_finset_range :
    π[S](x) = #{p ∈ Finset.range (⌊x⌋₊ + 1) | (p : ℕ).Prime ∧ p ∈ S} := by
  rw [primeCountingWithin_def, ← Set.ncard_coe_finset]
  congr 1
  ext p
  grind [Nat.le_floor_iff', Nat.Prime.ne_zero]

lemma primeCountingZModWithin_eq_card_finset_range :
    π[S](x; q, a) =
      #{p ∈ Finset.range (⌊x⌋₊ + 1) | ((p : ℕ).Prime ∧ (p : ZMod q) = a) ∧ p ∈ S} := by
  rw [primeCountingZModWithin_def, ← Set.ncard_coe_finset]
  congr 1
  ext p
  grind [Nat.le_floor_iff', Nat.Prime.ne_zero]

lemma primeCountingWithin_eq_card_primesLEWithin : π[S](x) = #(⌊x⌋₊.primesLEWithin S) := by
  rw [primesLEWithin_eq_filter_range]
  exact primeCountingWithin_eq_card_finset_range x S

lemma primeCountingZModWithin_eq_card_primesLEZModWithin :
    π[S](x; q, a) = #(⌊x⌋₊.primesLEZModWithin q a S) := by
  rw [primesLEZModWithin_eq_filter_range]
  exact primeCountingZModWithin_eq_card_finset_range x q a S

end

@[simp]
lemma primeCountingZModWithin_univ (x : ℝ) (q : ℕ) (a : ZMod q) :
    π[Set.univ](x; q, a) = π(x; q, a) := by
  simp [Real.primeCountingZModWithin, Real.primeCountingZMod]

@[simp]
lemma primeCountingZModWithin_one_eq_primeCountingWithin {x : ℝ} {a : ZMod 1} {S : Set ℕ} :
    π[S](x; 1, a) = π[S](x) := by
  simp [Real.primeCountingWithin, Real.primeCountingZModWithin, eq_iff_true_of_subsingleton]

@[simp]
lemma primeCountingWithin_univ (x : ℝ) : π[Set.univ](x) = π(x) := by
  rw [← primeCountingZModWithin_one_eq_primeCountingWithin
    (x := x) (a := (0 : ZMod 1)) (S := Set.univ),
    primeCountingZModWithin_univ, primeCountingZMod_one_eq_primeCounting]

@[simp]
lemma primeCountingWithin_inter_setOf_prime (x : ℝ) (S : Set ℕ) :
    π[S ∩ {p | p.Prime}](x) = π[S](x) := by
  grind [Real.primeCountingWithin]

@[simp]
lemma primeCountingZModWithin_inter_setOf_prime (x : ℝ) (q : ℕ) (a : ZMod q) (S : Set ℕ) :
    π[S ∩ {p | p.Prime}](x; q, a) = π[S](x; q, a) := by
  grind [Real.primeCountingZModWithin]

@[simp]
lemma primeCountingWithin_setOf_prime (x : ℝ) : π[{p | p.Prime}](x) = π(x) := by
  rw [← Set.univ_inter ({p | p.Prime} : Set ℕ), primeCountingWithin_inter_setOf_prime,
    primeCountingWithin_univ]

@[simp]
lemma primeCountingZModWithin_setOf_prime (x : ℝ) (q : ℕ) (a : ZMod q) :
    π[{p | p.Prime}](x; q, a) = π(x; q, a) := by
  rw [← Set.univ_inter ({p | p.Prime} : Set ℕ),
    primeCountingZModWithin_inter_setOf_prime, primeCountingZModWithin_univ]

end Real
