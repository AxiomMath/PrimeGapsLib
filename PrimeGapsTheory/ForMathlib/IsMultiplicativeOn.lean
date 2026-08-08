/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Finset.NatDivisors
public import Mathlib.NumberTheory.LSeries.Convolution
import PrimeGapsTheory.ForMathlib.Data.Nat.Squarefree

/-!
# Multiplicativity

Multiplicativity of an `ArithmeticFunction` relative to a subset of `ℕ`, together with total
multiplicativity and submultiplicativity.

## Main definitions

* `ArithmeticFunction.IsMultiplicativeOn`: multiplicativity for coprime pairs drawn from a subset
  of `ℕ`.
* `ArithmeticFunction.IsTotallyMultiplicative`: multiplicativity without a coprimality hypothesis.
* `ArithmeticFunction.IsSubmultiplicativeOn` and `ArithmeticFunction.IsSubmultiplicative`: the
  inequality `f (m * n) ≤ f m * f n`, on a subset of `ℕ` and everywhere.
* `Function.toTotallyMultiplicative`: the totally multiplicative function agreeing with a given
  `f : ℕ → R` on the primes.

## Implementation notes

Much of this could be stated for structures more general than `ArithmeticFunction`, at the cost of
interfacing with the existing results on `ArithmeticFunction.IsMultiplicative`.
-/

@[expose] public section

open Nat Set

namespace ArithmeticFunction

variable {R : Type*}

section IsMultiplicativeOn

/-- Multiplicative functions on a subset. -/
@[mk_iff]
structure IsMultiplicativeOn [MonoidWithZero R] (f : ArithmeticFunction R) (s : Set ℕ) : Prop where
  map_one : f 1 = 1
  map_mul_of_coprime : ∀ {m n : ℕ}, m ∈ s → n ∈ s → m.Coprime n → f (m * n) = f m * f n

@[simp]
lemma isMultiplicativeOn_univ [MonoidWithZero R] {f : ArithmeticFunction R} :
    f.IsMultiplicativeOn univ ↔ f.IsMultiplicative := by
  simp [isMultiplicativeOn_iff, IsMultiplicative]

end IsMultiplicativeOn

section IsTotallyMultiplicative

/-- Totally multiplicative functions. -/
@[mk_iff]
structure IsTotallyMultiplicative
    {R : Type*} [MonoidWithZero R] (f : ArithmeticFunction R) : Prop where
  map_one : f 1 = 1
  map_mul : ∀ {m n : ℕ}, f (m * n) = f m * f n

/-- A totally multiplicative function sends a list product to the product of its values:
`f (l.prod) = (l.map f).prod`. -/
lemma IsTotallyMultiplicative.map_list_prod [MonoidWithZero R] {f : ArithmeticFunction R}
    (hf : f.IsTotallyMultiplicative) (l : List ℕ) : f l.prod = (l.map f).prod := by
  induction l <;> simp [hf.map_one, hf.map_mul, *]

/-- A totally multiplicative function sends a finite product over a `Finset` to the product of its
values: `f (∏ i ∈ s, g i) = ∏ i ∈ s, f (g i)`. -/
lemma IsTotallyMultiplicative.map_prod [CommMonoidWithZero R] {f : ArithmeticFunction R}
    (hf : f.IsTotallyMultiplicative) {ι : Type*} (s : Finset ι) (g : ι → ℕ) :
    f (∏ i ∈ s, g i) = ∏ i ∈ s, f (g i) := by
  induction s using Finset.cons_induction <;> simp [hf.map_one, hf.map_mul, *]

lemma isTotallyMultiplicative_congr [MonoidWithZero R]
    {f : ArithmeticFunction R} (hf : f.IsTotallyMultiplicative)
    {g : ArithmeticFunction R} (hg : g.IsTotallyMultiplicative)
    (hp : ∀ p : ℕ, p.Prime → f p = g p) : f = g := by
  ext n
  obtain rfl | hn := eq_or_ne n 0
  · simp
  rw [← prod_primeFactorsList hn, hf.map_list_prod, hg.map_list_prod]
  congr 1
  aesop

end IsTotallyMultiplicative

section toMultiplicative

variable [MonoidWithZero R] {f : ArithmeticFunction R} {s : Set ℕ}

lemma IsTotallyMultiplicative.isMultiplicative (hf : f.IsTotallyMultiplicative) :
    f.IsMultiplicative :=
  ⟨hf.map_one, fun _ ↦ hf.map_mul⟩

end toMultiplicative

section onSquarefree

section monoid
variable [MonoidWithZero R] {f : ArithmeticFunction R}

theorem IsMultiplicative.map_mul_of_squarefree_mul (hf : f.IsMultiplicative) {m n : ℕ}
    (h : Squarefree (m * n)) : f (m * n) = f m * f n :=
  hf.map_mul_of_coprime (Nat.coprime_of_squarefree_mul h)

end monoid

section comm_monoid
variable [CommMonoidWithZero R] {f : ArithmeticFunction R}

theorem IsMultiplicative.map_prod_of_squarefree_prod
    {ι : Type*} {s : Finset ι} {r : ι → ℕ}
    (hf : f.IsMultiplicative) (hr : Squarefree (∏ i ∈ s, r i)) :
    f (∏ i ∈ s, r i) = ∏ i ∈ s, f (r i) :=
  hf.map_prod _ _ (squarefree_prod_iff.mp hr).2

end comm_monoid

end onSquarefree

section IsSubmultiplicative

/-- Submultiplicative functions on a subset: `f (m * n) ≤ f m * f n` whenever `m, n ∈ s`. -/
def IsSubmultiplicativeOn [Mul R] [Zero R] [Preorder R]
    (f : ArithmeticFunction R) (s : Set ℕ) : Prop :=
  ∀ m ∈ s, ∀ n ∈ s, f (m * n) ≤ f m * f n

/-- Submultiplicative functions: `f (m * n) ≤ f m * f n` for all `m, n`. -/
def IsSubmultiplicative [Mul R] [Zero R] [Preorder R] (f : ArithmeticFunction R) : Prop :=
  ∀ m n : ℕ, f (m * n) ≤ f m * f n

section Basic

@[simp]
lemma isSubmultiplicativeOn_univ [Mul R] [Zero R] [Preorder R]
    {f : ArithmeticFunction R} : f.IsSubmultiplicativeOn univ ↔ f.IsSubmultiplicative := by
  simp [IsSubmultiplicativeOn, IsSubmultiplicative]

lemma IsSubmultiplicative.isSubmultiplicativeOn
    [Mul R] [Zero R] [Preorder R] {f : ArithmeticFunction R}
    (hf : f.IsSubmultiplicative) (s : Set ℕ) : f.IsSubmultiplicativeOn s :=
  fun m _ n _ ↦ hf m n

/-- Submultiplicativity on a set restricts to any subset. -/
lemma IsSubmultiplicativeOn.mono [Mul R] [Zero R] [Preorder R]
    {f : ArithmeticFunction R} {s t : Set ℕ} (hf : f.IsSubmultiplicativeOn s) (hts : t ⊆ s) :
    f.IsSubmultiplicativeOn t :=
  fun m hm n hn ↦ hf m (hts hm) n (hts hn)

lemma IsTotallyMultiplicative.isSubmultiplicative [MonoidWithZero R] [Preorder R]
    {f : ArithmeticFunction R} (hf : f.IsTotallyMultiplicative) :
    f.IsSubmultiplicative :=
  fun _ _ ↦ hf.map_mul.le

open Finset in
/-- Dirichlet convolution preserves submultiplicativity. -/
lemma IsSubmultiplicative.mul [CommSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
    [IsOrderedMonoid R] {f g : ArithmeticFunction R}
    (hf : f.IsSubmultiplicative) (hg : g.IsSubmultiplicative) :
    (f * g).IsSubmultiplicative := by
  have conv : ∀ n : ℕ, (f * g) n = ∑ d ∈ n.divisors, f d * g (n / d) := fun n ↦ by
    rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b ↦ f a * g b)]
  intro M N
  rcases eq_or_ne M 0 with rfl | hM
  · simp
  rcases eq_or_ne N 0 with rfl | hN
  · positivity
  set S := M.divisors ×ˢ N.divisors with hS
  set π : ℕ × ℕ → ℕ := fun p ↦ p.1 * p.2 with hπ
  calc (f * g) (M * N)
      = ∑ d ∈ S.image π, f d * g (M * N / d) := by
        rw [conv, Nat.divisors_mul, Finset.mul_def]
    _ ≤ ∑ x ∈ S, f (π x) * g (M * N / π x) := by
        refine le_trans ?_ (le_of_eq (Finset.sum_fiberwise_of_maps_to
          (fun x hx ↦ mem_image_of_mem π hx) (fun x ↦ f (π x) * g (M * N / π x))))
        refine Finset.sum_le_sum fun j hj ↦ ?_
        obtain ⟨x₀, hx₀, rfl⟩ := mem_image.mp hj
        exact single_le_sum (f := fun i ↦ f (π i) * g (M * N / π i)) (fun _ _ ↦ _root_.zero_le)
          (mem_filter.mpr ⟨hx₀, rfl⟩)
    _ ≤ ∑ x ∈ S, (f x.1 * g (M / x.1)) * (f x.2 * g (N / x.2)) := by
        refine Finset.sum_le_sum fun x hx ↦ ?_
        obtain ⟨a, b⟩ := x
        simp only [hS, mem_product, Nat.mem_divisors] at hx
        calc f (π (a, b)) * g (M * N / π (a, b))
            = f (a * b) * g (M / a * (N / b)) := by
              rw [hπ, Nat.div_mul_div_comm hx.1.1 hx.2.1]
          _ ≤ (f a * f b) * (g (M / a) * g (N / b)) := mul_le_mul' (hf a b) (hg _ _)
          _ = (f a * g (M / a)) * (f b * g (N / b)) := by ring
    _ = (f * g) M * (f * g) N := by
        rw [conv M, conv N, sum_mul_sum, ← Finset.sum_product', hS]

theorem IsSubmultiplicative.pow [CommSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
    [IsOrderedMonoid R] {f : ArithmeticFunction R}
    (hf : f.IsSubmultiplicative) {k : ℕ} : IsSubmultiplicative (f ^ k) := by
  induction k with
  | zero =>
    intro a b
    simp only [pow_zero, one_apply, mul_eq_one, mul_ite, mul_one, mul_zero]
    grind
  | succ k hk => exact pow_succ f k ▸ hk.mul hf

end Basic

section Prod

variable [CommMonoidWithZero R] [Preorder R] [IsOrderedMonoid R] {f : ArithmeticFunction R}

/-- On a submonoid `s` of `ℕ`, a function submultiplicative on `s` with `f 1 ≤ 1` sends a list
product of elements of `s` to at most the product of its values: `f l.prod ≤ (l.map f).prod`.
The submultiplicative analogue of `IsTotallyMultiplicative.map_list_prod`. -/
lemma IsSubmultiplicativeOn.map_list_prod {s : Submonoid ℕ}
    (hf : f.IsSubmultiplicativeOn (s : Set ℕ)) (hf1 : f 1 ≤ 1) {l : List ℕ}
    (hl : ∀ a ∈ l, a ∈ s) : f l.prod ≤ (l.map f).prod := by
  induction l with
  | nil => simpa using hf1
  | cons a l ih =>
    have hl' : ∀ b ∈ l, b ∈ s := fun b hb ↦ hl b (List.mem_cons_of_mem a hb)
    rw [List.prod_cons, List.map_cons, List.prod_cons]
    exact (hf a (hl a List.mem_cons_self) _ (s.list_prod_mem hl')).trans
      (mul_le_mul_right (ih hl') _)

/-- On a submonoid `s` of `ℕ`, a function submultiplicative on `s` with `f 1 ≤ 1` sends a finite
product over a `Finset` of elements of `s` to at most the product of its values:
`f (∏ i ∈ t, g i) ≤ ∏ i ∈ t, f (g i)`. The submultiplicative analogue of
`IsTotallyMultiplicative.map_prod`. -/
lemma IsSubmultiplicativeOn.map_prod {s : Submonoid ℕ}
    (hf : f.IsSubmultiplicativeOn (s : Set ℕ)) (hf1 : f 1 ≤ 1) {ι : Type*} {t : Finset ι}
    {g : ι → ℕ} (hg : ∀ i ∈ t, g i ∈ s) : f (∏ i ∈ t, g i) ≤ ∏ i ∈ t, f (g i) := by
  induction t using Finset.cons_induction with
  | empty => simpa using hf1
  | cons a t ha ih =>
    have hg' : ∀ i ∈ t, g i ∈ s := fun i hi ↦ hg i (Finset.mem_cons_of_mem hi)
    rw [Finset.prod_cons, Finset.prod_cons]
    exact (hf _ (hg a (Finset.mem_cons_self _ _)) _ (s.prod_mem hg')).trans
      (mul_le_mul_right (ih hg') _)

lemma IsSubmultiplicative.map_list_prod (hf : f.IsSubmultiplicative) (hf1 : f 1 ≤ 1) (l : List ℕ) :
    f l.prod ≤ (l.map f).prod :=
  (hf.isSubmultiplicativeOn ((⊤ : Submonoid ℕ) : Set ℕ)).map_list_prod hf1
    (fun a _ ↦ Submonoid.mem_top a)

lemma IsSubmultiplicative.map_prod (hf : f.IsSubmultiplicative) (hf1 : f 1 ≤ 1) {ι : Type*}
    (t : Finset ι) (g : ι → ℕ) : f (∏ i ∈ t, g i) ≤ ∏ i ∈ t, f (g i) :=
  (hf.isSubmultiplicativeOn ((⊤ : Submonoid ℕ) : Set ℕ)).map_prod hf1
    (fun i _ ↦ Submonoid.mem_top (g i))

end Prod

end IsSubmultiplicative

end ArithmeticFunction

section toTotallyMultiplicative

open ArithmeticFunction

namespace Function

/-- Given some function `f : ℕ → R`, `f.toTotallyMultiplicative` gives the unique totally
multiplicative function such that `f.toTotallyMultiplicative p = f p` for all primes `p`. -/
def toTotallyMultiplicative {R : Type*} [CommMonoidWithZero R] (f : ℕ → R) : ArithmeticFunction R :=
  toArithmeticFunction <| fun n ↦ n.factorization.prod (fun p k ↦ (f p) ^ k)

variable {R : Type*} [CommMonoidWithZero R] (f : ℕ → R)

lemma toTotallyMultiplicative_apply {n : ℕ} : f.toTotallyMultiplicative n =
    if n = 0 then 0 else n.factorization.prod (fun p k ↦ (f p) ^ k) := rfl

lemma toTotallyMultiplicative_apply_prime {p : ℕ} (hp : p.Prime) :
    f.toTotallyMultiplicative p = f p := by
  simp [toTotallyMultiplicative_apply, hp.ne_zero, hp.factorization]

lemma toTotallyMultiplicative_map_one : f.toTotallyMultiplicative 1 = 1 := by
  simp [toTotallyMultiplicative_apply]

lemma toTotallyMultiplicative_map_mul {m n : ℕ} : f.toTotallyMultiplicative (m * n) =
    f.toTotallyMultiplicative m * f.toTotallyMultiplicative n := by
  rcases eq_or_ne m 0 with hm | hm
  · aesop
  rcases eq_or_ne n 0 with hn | hn
  · aesop
  rw [toTotallyMultiplicative_apply, toTotallyMultiplicative_apply, toTotallyMultiplicative_apply,
    if_neg (mul_ne_zero hm hn), if_neg hm, if_neg hn, Nat.factorization_mul hm hn,
    Finsupp.prod_add_index' (fun a ↦ pow_zero _) (fun a b₁ b₂ ↦ pow_add _ _ _)]

lemma toTotallyMultiplicative_isTotallyMultiplicative :
    f.toTotallyMultiplicative.IsTotallyMultiplicative :=
  ⟨toTotallyMultiplicative_map_one f, toTotallyMultiplicative_map_mul f⟩

lemma toTotallyMultiplicative_isMultiplicative : f.toTotallyMultiplicative.IsMultiplicative :=
  (toTotallyMultiplicative_isTotallyMultiplicative f).isMultiplicative

lemma toTotallyMultiplicative_unique {g : ArithmeticFunction R}
    (hg_tot_mul : g.IsTotallyMultiplicative) (hg_eq : ∀ p : ℕ, p.Prime → g p = f p) :
    g = f.toTotallyMultiplicative :=
  isTotallyMultiplicative_congr hg_tot_mul (toTotallyMultiplicative_isTotallyMultiplicative f)
    fun p hp ↦ (hg_eq p hp).trans (toTotallyMultiplicative_apply_prime f hp).symm

lemma toTotallyMultiplicative_unique' {g : ℕ → R}
    (hg_tot_mul : (toArithmeticFunction g).IsTotallyMultiplicative)
    (hg_eq : ∀ p : ℕ, p.Prime → f p = g p) :
    toArithmeticFunction g = f.toTotallyMultiplicative :=
  toTotallyMultiplicative_unique f hg_tot_mul fun p hp ↦ by
    simp [hg_eq p hp, toArithmeticFunction, hp.ne_zero]

lemma _root_.ArithmeticFunction.toTotallyMultiplicative_eq_self_iff_isTotallyMultiplicative
    (g : ArithmeticFunction R) : (⇑g).toTotallyMultiplicative = g ↔ g.IsTotallyMultiplicative :=
  ⟨fun h ↦ h ▸ toTotallyMultiplicative_isTotallyMultiplicative _,
    fun hg ↦ (toTotallyMultiplicative_unique _ hg fun _ _ ↦ rfl).symm⟩

lemma toTotallyMultiplicative_isSubmultiplicative [Preorder R] :
    f.toTotallyMultiplicative.IsSubmultiplicative :=
  (toTotallyMultiplicative_isTotallyMultiplicative f).isSubmultiplicative

end Function

end toTotallyMultiplicative
