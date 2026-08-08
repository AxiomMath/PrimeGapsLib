/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.Common.Decoupling
import PrimeGapsTheory.Tactic.PaperTag

/-!
# Substitution identities

Defines the two tuple reindexings and proves their multiplicative coefficient identity.

## Main definitions

* `boldA`: The row-indexed tuple formed from diagonal and off-diagonal factors.
* `boldB`: The column-indexed tuple formed from diagonal and off-diagonal factors.

## Main results

* `coeff_collapse_gen`: Collapses the multiplicative substitution coefficient.
-/

@[expose] public section

open scoped ArithmeticFunction.Moebius


open PrimeGaps.LemS1RestrictSij

namespace PrimeGaps

/-- Given `u: Fin k → ℕ` and `s: Fin k → Fin k → ℕ`, define `a_j:= u_j ∏_{i ≠ j} s_{j,i}` (product
over the second index, first index fixed to `j`).
-/
@[pg_tag "bg246" "def_bold_a"]
def boldA {k : ℕ} (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ) : Fin k → ℕ :=
  fun j ↦ u j * ∏ i ∈ Finset.univ.erase j, s j i

/-- With the same data, define `b_j:= u_j ∏_{i ≠ j} s_{i,j}` (product over the first index, second
index fixed to `j`). Note the transposition of the `s` -indices between `boldA` and `boldB`.
-/
@[pg_tag "bg246" "def_bold_b"]
def boldB {k : ℕ} (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ) : Fin k → ℕ :=
  fun j ↦ u j * ∏ i ∈ Finset.univ.erase j, s i j

/-- A doubly-indexed `tsum` collapses to a double `Finset` sum as soon as two finite boxes catch
the whole support. -/
theorem tsum_tsum_eq_sum_sum {α β M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    (F : α → β → M) (U : Finset α) (S : Finset β)
    (hmem : ∀ a b, F a b ≠ 0 → a ∈ U ∧ b ∈ S) :
    (∑' a, ∑' b, F a b) = ∑ a ∈ U, ∑ b ∈ S, F a b := by
  classical
  have hrow : ∀ a, (∑' b, F a b) = ∑ b ∈ S, F a b := fun a ↦
    tsum_eq_sum fun b hb ↦ by by_contra hc; exact hb (hmem a b hc).2
  rw [tsum_eq_sum (s := U) fun a ha ↦ ?_]
  · exact Finset.sum_congr rfl fun a _ ↦ hrow a
  · rw [hrow a]
    exact Finset.sum_eq_zero fun b _ ↦ by by_contra hc; exact ha (hmem a b hc).1

/-- `1 ≤ boldA u s i` when `u ≥ 1` and off-diagonal `s ≥ 1`. -/
lemma boldA_pos {k : ℕ} (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ)
    (hupos : ∀ i, 1 ≤ u i) (hspos : ∀ i j, i ≠ j → 1 ≤ s i j) (i : Fin k) :
    1 ≤ boldA u s i := by
  simpa [boldA] using Nat.mul_le_mul (hupos i)
    (Finset.one_le_prod' fun a ha ↦ hspos i a (Ne.symm (Finset.mem_erase.mp ha).1))

end PrimeGaps

namespace Finset

/-- Row/erase form of the off-diagonal product: `∏ i ∏_{j ≠ i} F i j = ∏_{offDiag} F p.1 p.2`. -/
theorem prod_prod_erase_eq_prod_offDiag {ι M : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid M]
    (F : ι → ι → M) : ∏ i, ∏ j ∈ Finset.univ.erase i, F i j =
    ∏ p ∈ (Finset.univ.offDiag : Finset (ι × ι)), F p.1 p.2 := by
  have hoff : (Finset.univ.offDiag : Finset (ι × ι)) = Finset.univ.biUnion (fun i ↦
          (Finset.univ.erase i).map (Function.Embedding.sectR i ι)) := by
    ext p
    simp only [Finset.mem_offDiag, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_map,
      Finset.mem_erase, Function.Embedding.sectR_apply, and_true]
    constructor
    · intro hne
      exact ⟨p.1, p.2, fun h ↦ hne h.symm, rfl⟩
    · rintro ⟨i, j, hj, rfl⟩
      exact fun h ↦ hj h.symm
  rw [hoff, Finset.prod_biUnion]
  · apply Finset.prod_congr rfl
    intro i _
    rw [Finset.prod_map]
    simp only [Function.Embedding.sectR_apply]
  · intro a _ b _ hab
    simp only [Finset.disjoint_left, Finset.mem_map, Finset.mem_erase,
      Function.Embedding.sectR_apply]
    rintro p ⟨j, -, rfl⟩ ⟨j', -, h⟩
    exact hab (by have := (Prod.mk.injEq _ _ _ _).mp h; exact this.1.symm)

/-- Swap invariance of an off-diagonal product: `∏_{offDiag} G p.2 p.1 = ∏_{offDiag} G p.1 p.2`.
-/
theorem prod_offDiag_swap {ι M : Type*} [Fintype ι] [CommMonoid M] (G : ι → ι → M) :
    ∏ p ∈ (Finset.univ.offDiag : Finset (ι × ι)), G p.2 p.1 =
    ∏ p ∈ (Finset.univ.offDiag : Finset (ι × ι)), G p.1 p.2 := by
  apply Finset.prod_nbij' (fun p ↦ (p.2, p.1)) (fun p ↦ (p.2, p.1))
  · intro p hp; simp only [Finset.mem_offDiag] at * ; exact ⟨hp.2.1, hp.1, fun h ↦ hp.2.2 h.symm⟩
  · intro p hp; simp only [Finset.mem_offDiag] at * ; exact ⟨hp.2.1, hp.1, fun h ↦ hp.2.2 h.symm⟩
  · intro p hp; simp
  · intro p hp; simp
  · intro p hp; rfl

end Finset

namespace Nat

/-- A function multiplicative on coprime pairs is multiplicative over a pairwise-coprime finite
product. -/
theorem map_prod_of_pairwise_coprime {M ι : Type*} [CommMonoid M] (f : ℕ → M) (hf1 : f 1 = 1)
    (hmul : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b)
    (S : Finset ι) (t : ι → ℕ)
    (hpair : (S : Set ι).Pairwise fun i j ↦ Nat.Coprime (t i) (t j)) :
    f (∏ i ∈ S, t i) = ∏ i ∈ S, f (t i) := by
  classical
  induction S using Finset.induction with
  | empty => simpa using hf1
  | @insert a T ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, hmul _ _ ?_, ih (hpair.mono (by simp))]
      refine Nat.Coprime.prod_right fun i hi ↦ ?_
      exact hpair (by simp) (by simp [hi]) (by rintro rfl; exact ha hi)

end Nat

namespace PrimeGaps

/-- A function `f` multiplicative on coprime pairs factors over `boldA`:
`f (boldA u s i) = f (u i) ∏_{j ≠ i} f (s i j)`, using coprimality from `RestrictedCoprime`.
Instantiated at `μ`, at `φ` and at `g`. -/
theorem map_boldA {M : Type*} [CommMonoid M] (f : ℕ → M) (hf1 : f 1 = 1)
    (hmul : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b)
    {k : ℕ} (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ)
    (hcop : RestrictedCoprime u s) (i : Fin k) :
    f (boldA u s i) = f (u i) * ∏ j ∈ Finset.univ.erase i, f (s i j) := by
  classical
  rw [boldA, hmul _ _ ?_, Nat.map_prod_of_pairwise_coprime f hf1 hmul _ _ ?_]
  · intro a ha b hb hab
    have hai : i ≠ a := fun h ↦ (Finset.mem_erase.mp (Finset.mem_coe.mp ha)).1 h.symm
    have hbi : i ≠ b := fun h ↦ (Finset.mem_erase.mp (Finset.mem_coe.mp hb)).1 h.symm
    exact (hcop i a hai).2.2.1 b (fun h ↦ hab h.symm) (fun h ↦ hbi h.symm)
  · refine Nat.Coprime.prod_right fun j hj ↦ ?_
    exact Nat.coprime_comm.mp (hcop i j (fun h ↦ (Finset.mem_erase.mp hj).1 h.symm)).1

/-- The transpose of `PrimeGaps.map_boldA`:
`f (boldB u s i) = f (u i) ∏_{j ≠ i} f (s j i)`. -/
theorem map_boldB {M : Type*} [CommMonoid M] (f : ℕ → M) (hf1 : f 1 = 1)
    (hmul : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b)
    {k : ℕ} (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ)
    (hcop : RestrictedCoprime u s) (i : Fin k) :
    f (boldB u s i) = f (u i) * ∏ j ∈ Finset.univ.erase i, f (s j i) := by
  classical
  rw [boldB, hmul _ _ ?_, Nat.map_prod_of_pairwise_coprime f hf1 hmul _ _ ?_]
  · intro a ha b hb hab
    have hai : a ≠ i := fun h ↦ (Finset.mem_erase.mp (Finset.mem_coe.mp ha)).1 h
    have hbi : b ≠ i := fun h ↦ (Finset.mem_erase.mp (Finset.mem_coe.mp hb)).1 h
    exact (hcop a i hai).2.2.2 b (fun h ↦ hab h.symm) hbi
  · refine Nat.Coprime.prod_right fun j hj ↦ ?_
    exact Nat.coprime_comm.mp (hcop j i (fun h ↦ (Finset.mem_erase.mp hj).1 h)).2.1

/-- `μ(boldA u s i) = μ(u i) ∏_{j ≠ i} μ(s i j)`, using coprimality from `RestrictedCoprime`.
-/
theorem moebius_boldA_factor {k : ℕ} (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ)
    (hcop : RestrictedCoprime u s) (i : Fin k) :
    μ (boldA u s i) = μ (u i) *
        ∏ j ∈ Finset.univ.erase i, μ (s i j) :=
  map_boldA _ ArithmeticFunction.moebius_apply_one
    (fun _ _ hab ↦ ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab) u s hcop i

/-- `μ(boldB u s i) = μ(u i) ∏_{j ≠ i} μ(s j i)`, using coprimality from `RestrictedCoprime`.
-/
theorem moebius_boldB_factor {k : ℕ} (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ)
    (hcop : RestrictedCoprime u s) (i : Fin k) :
    μ (boldB u s i) = μ (u i) *
        ∏ j ∈ Finset.univ.erase i, μ (s j i) :=
  map_boldB _ ArithmeticFunction.moebius_apply_one
    (fun _ _ hab ↦ ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab) u s hcop i

/-- For any density `w: ℕ → ℝ` supplied with its bold-A / bold-B multiplicative factorizations
(`wA`, `wB`) and nonvanishing on the `u` /`s` support, the μ/`w` coefficient collapses:
`(∏ μ(u)²/w(u)) (∏_{i≠j} μ(s)/w(s)²) (∏ μ(A)w(A)) (∏ μ(B)w(B)) = (∏ w(u)) (∏_{i≠j} μ(s))`.
Instantiated with `w = φ` for the first moment and `w = g` for the second.
-/
theorem coeff_collapse_gen {k : ℕ} (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ) (w : ℕ → ℝ)
    (hcop : RestrictedCoprime u s)
    (hsq_u : ∀ i, Squarefree (u i))
    (hsq_s : ∀ i j, i ≠ j → Squarefree (s i j))
    (hwu_ne : ∀ i, w (u i) ≠ 0)
    (hws_ne : ∀ i j, i ≠ j → w (s i j) ≠ 0)
    (wA : ∀ i, w (boldA u s i) = w (u i) * ∏ a ∈ Finset.univ.erase i, w (s i a))
    (wB : ∀ i, w (boldB u s i) = w (u i) * ∏ a ∈ Finset.univ.erase i, w (s a i)) :
    (∏ i, (μ (u i) : ℝ) ^ 2 / w (u i)) *
    (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
        (μ (s p.1 p.2) : ℝ) / w (s p.1 p.2) ^ 2) *
    (∏ i, (μ (boldA u s i) : ℝ) * w (boldA u s i)) *
    (∏ i, (μ (boldB u s i) : ℝ) * w (boldB u s i)) = (∏ i, w (u i)) *
        (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
            (μ (s p.1 p.2) : ℝ)) := by
  classical
  have mA : ∀ i, (μ (boldA u s i) : ℝ) =
      (μ (u i) : ℝ) *
        ∏ a ∈ Finset.univ.erase i, (μ (s i a) : ℝ) := by
    intro i; rw [moebius_boldA_factor u s hcop i]; push_cast; rfl
  have mB : ∀ i, (μ (boldB u s i) : ℝ) =
      (μ (u i) : ℝ) *
        ∏ a ∈ Finset.univ.erase i, (μ (s a i) : ℝ) := by
    intro i; rw [moebius_boldB_factor u s hcop i]; push_cast; rfl
  have rowMs : (∏ i, ∏ a ∈ Finset.univ.erase i, (μ (s i a) : ℝ)) =
      ∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
          (μ (s p.1 p.2) : ℝ) :=
    Finset.prod_prod_erase_eq_prod_offDiag (fun x y ↦ (μ (s x y) : ℝ))
  have rowPs : (∏ i, ∏ a ∈ Finset.univ.erase i, w (s i a)) =
      ∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)), w (s p.1 p.2) :=
    Finset.prod_prod_erase_eq_prod_offDiag (fun x y ↦ w (s x y))
  have colMs : (∏ i, ∏ a ∈ Finset.univ.erase i, (μ (s a i) : ℝ)) =
      ∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
          (μ (s p.1 p.2) : ℝ) :=
    (Finset.prod_prod_erase_eq_prod_offDiag
        (fun x y ↦ (μ (s y x) : ℝ))).trans
      (Finset.prod_offDiag_swap (fun x y ↦ (μ (s x y) : ℝ)))
  have colPs : (∏ i, ∏ a ∈ Finset.univ.erase i, w (s a i)) =
      ∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)), w (s p.1 p.2) :=
    (Finset.prod_prod_erase_eq_prod_offDiag (fun x y ↦ w (s y x))).trans
      (Finset.prod_offDiag_swap (fun x y ↦ w (s x y)))
  have hboldA : (∏ i, (μ (boldA u s i) : ℝ) * w (boldA u s i)) =
      ((∏ i, (μ (u i) : ℝ)) *
          (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
              (μ (s p.1 p.2) : ℝ))) * ((∏ i, w (u i)) *
          (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)), w (s p.1 p.2))) := by
    have hstep : (∏ i, (μ (boldA u s i) : ℝ) * w (boldA u s i)) =
        ∏ i, ((μ (u i) : ℝ) *
            ∏ a ∈ Finset.univ.erase i, (μ (s i a) : ℝ)) *
          (w (u i) * ∏ a ∈ Finset.univ.erase i, w (s i a)) := by
      refine Finset.prod_congr rfl ?_
      intro i _; rw [mA i, wA i]
    rw [hstep, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      rowMs, rowPs]
  have hboldB : (∏ i, (μ (boldB u s i) : ℝ) * w (boldB u s i)) =
      ((∏ i, (μ (u i) : ℝ)) *
          (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
              (μ (s p.1 p.2) : ℝ))) * ((∏ i, w (u i)) *
          (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)), w (s p.1 p.2))) := by
    have hstep : (∏ i, (μ (boldB u s i) : ℝ) * w (boldB u s i)) =
        ∏ i, ((μ (u i) : ℝ) *
            ∏ a ∈ Finset.univ.erase i, (μ (s a i) : ℝ)) *
          (w (u i) * ∏ a ∈ Finset.univ.erase i, w (s a i)) := by
      refine Finset.prod_congr rfl ?_
      intro i _; rw [mB i, wB i]
    rw [hstep, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      colMs, colPs]
  have hprod_musq : (∏ i, (μ (u i) : ℝ) ^ 2) = 1 :=
    Finset.prod_eq_one fun i _ ↦ by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree (hsq_u i)
  have hprod_mssq : (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
        (μ (s p.1 p.2) : ℝ) ^ 2) = 1 :=
    Finset.prod_eq_one fun p hp ↦ by
      simp only [Finset.mem_offDiag, Finset.mem_univ, true_and] at hp
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree (hsq_s p.1 p.2 hp)
  have hPu_ne : (∏ i, w (u i)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ ↦ hwu_ne i)
  have hPs_ne : (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)), w (s p.1 p.2)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp ↦ by
      simp only [Finset.mem_offDiag, Finset.mem_univ, true_and] at hp
      exact hws_ne p.1 p.2 hp
  rw [Finset.prod_div_distrib, Finset.prod_div_distrib, hboldA, hboldB]
  rw [show (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)), w (s p.1 p.2) ^ 2) =
      (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)), w (s p.1 p.2)) ^ 2 by
    rw [Finset.prod_pow]]
  have hMu2 : (∏ i, (μ (u i) : ℝ)) ^ 2 = 1 := by
    rw [← Finset.prod_pow]; exact hprod_musq
  have hMs2 : (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
        (μ (s p.1 p.2) : ℝ)) ^ 2 = 1 := by
    rw [← Finset.prod_pow]; exact hprod_mssq
  rw [hprod_musq]
  set Pu : ℝ := ∏ i, w (u i)
  set Ps : ℝ := ∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)), w (s p.1 p.2)
  set Mu : ℝ := ∏ i, (μ (u i) : ℝ)
  set Ms : ℝ := ∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
      (μ (s p.1 p.2) : ℝ)
  have hlhs : (1 : ℝ) / Pu * (Ms / Ps ^ 2) * (Mu * Ms * (Pu * Ps)) * (Mu * Ms * (Pu * Ps)) =
      Mu ^ 2 * Ms ^ 2 * (Ms * Pu) := by
    field_simp
  rw [hlhs, hMu2, hMs2]
  ring

end PrimeGaps
