/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.S2m.ExpandDrop

/-!
# Separation of the decoupled second-moment sum

This file factors `decoupledSum` into a weighted sum of squares of `Ydisc`.

## Main definitions

* `gDisc`: the one-coordinate summand in `Ydisc`.
* `Ydisc`: the discrete marginal sum.

## Main results

* `decoupledSum_eq_sq_sum`: the factorization of `decoupledSum` into weighted squares of
  `Ydisc`.
-/

@[expose] public section

open scoped ArithmeticFunction.detotient PrimeGaps

namespace PrimeGaps

/-- An iterated `tsum` over `ρ`, `u`, `u'` with finite support collapses to the single `tsum` over
the product `(Fin k → ℕ) × ℕ × ℕ`. -/
theorem triple_tsum_eq_prod_rho {k : ℕ} (h : (Fin k → ℕ) → ℕ → ℕ → ℝ)
    (hfin : (Function.support (fun q : (Fin k → ℕ) × ℕ × ℕ ↦ h q.1 q.2.1 q.2.2)).Finite) :
    (∑' (ρ : Fin k → ℕ), ∑' (u : ℕ), ∑' (u' : ℕ), h ρ u u') =
      ∑' q : (Fin k → ℕ) × ℕ × ℕ, h q.1 q.2.1 q.2.2 := by
  classical
  set flat : (Fin k → ℕ) × ℕ × ℕ → ℝ := fun q ↦ h q.1 q.2.1 q.2.2 with hflat
  have hflatsum : Summable flat := summable_of_hasFiniteSupport hfin
  have hflatsec1 : ∀ ρ : Fin k → ℕ, Summable (fun q : ℕ × ℕ ↦ flat (ρ, q)) := fun ρ ↦
    summable_of_hasFiniteSupport <|
      (hfin.preimage (Set.injOn_of_injective (f := fun q : ℕ × ℕ ↦ (ρ, q))
        (fun a b hab ↦ by simpa using hab))).subset (fun _ hq ↦ hq)
  have hflatsec2 : ∀ (ρ : Fin k → ℕ) (u : ℕ), Summable (fun u' : ℕ ↦ flat (ρ, (u, u'))) := fun ρ u ↦
    summable_of_hasFiniteSupport <|
      (hfin.preimage (Set.injOn_of_injective (f := fun u' : ℕ ↦ (ρ, (u, u')))
        (fun a b hab ↦ by simpa using hab))).subset (fun _ hu' ↦ hu')
  rw [Summable.tsum_prod' hflatsum hflatsec1]
  apply tsum_congr; intro ρ
  rw [Summable.tsum_prod' (hflatsec1 ρ) (hflatsec2 ρ)]

/-- The one-coordinate summand of `Ydisc`: `F (log (update ρ m u) / log R) / φ u` for `u` squarefree
and coprime to `W`, and `0` otherwise. -/
noncomputable def gDisc {k : ℕ} (R : ℝ) (W : ℕ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (m : Fin k) (ρ : Fin k → ℕ) (u : ℕ) : ℝ :=
  if (u.Coprime W ∧ Squarefree u) then
    (1 / (u.totient : ℝ)) * F (WithLp.toLp 2 (fun i ↦ Real.log ((Function.update ρ m u) i : ℝ) /
            Real.log R))
  else 0

/-- The discrete marginal sum `∑' u, gDisc R W F m ρ u` over the free coordinate. -/
noncomputable def Ydisc {k : ℕ} (R : ℝ) (W : ℕ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (m : Fin k) (ρ : Fin k → ℕ) : ℝ :=
  ∑' u : ℕ, if (u.Coprime W ∧ Squarefree u) then
    (1 / (u.totient : ℝ)) * F (WithLp.toLp 2 (fun i ↦ Real.log ((Function.update ρ m u) i : ℝ) /
            Real.log R))
    else 0

/-- Because the decoupled summand carries only the individual squarefree / `(·, W) = 1` guards (no
cross-coordinate couplings), the triple `tsum` factors over the free coordinate `ρ` as
`∑'_ρ (guard) · w_g(ρ) · Ydisc(ρ)²`, with `w_g(ρ) = ∏_{i ≠ m} 1/g(ρ i)`, provided
`1 < R`. -/
theorem decoupledSum_eq_sq_sum {k : ℕ} (R : ℝ) (W : ℕ) (hR : 1 < R)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (hsupp : Function.support F ⊆ 𝓡 k) (m : Fin k) :
    decoupledSum R W F m = ∑' ρ : Fin k → ℕ, if (ρ m = 1 ∧ ∀ i, i ≠ m → (ρ i).Coprime W ∧
            Squarefree (ρ i)) then
            (∏ i ∈ Finset.univ.erase m, (1 : ℝ) / (g (ρ i) : ℝ)) * (Ydisc R W F m ρ) ^ 2
          else 0 := by
  classical
  have hfin_main : (Function.support
      (fun p : ℕ × ℕ × (Fin k → ℕ) ↦ S2mDecTerm R W F m p.2.2 p.1 p.2.1)).Finite :=
    PrimeGaps.S2mDecTerm_flat_support_finite R W hR F hsupp m
  let e : (Fin k → ℕ) × ℕ × ℕ ≃ ℕ × ℕ × (Fin k → ℕ) :=
    { toFun := fun q ↦ (q.2.1, q.2.2, q.1)
      invFun := fun p ↦ (p.2.2, p.1, p.2.1)
      left_inv := fun q ↦ rfl
      right_inv := fun p ↦ rfl }
  have hfin_rho : (Function.support
      (fun q : (Fin k → ℕ) × ℕ × ℕ ↦ S2mDecTerm R W F m q.1 q.2.1 q.2.2)).Finite :=
    (hfin_main.preimage (Set.injOn_of_injective e.injective)).subset (fun _ hq ↦ hq)
  have key : (∑' u : ℕ, ∑' u' : ℕ, ∑' ρ : Fin k → ℕ, S2mDecTerm R W F m ρ u u') =
      ∑' ρ : Fin k → ℕ, ∑' u : ℕ, ∑' u' : ℕ, S2mDecTerm R W F m ρ u u' := by
    rw [PrimeGaps.triple_tsum_eq_prod (S2mDecTerm R W F m) hfin_main,
        triple_tsum_eq_prod_rho (S2mDecTerm R W F m) hfin_rho]
    exact (Equiv.tsum_eq e (fun p ↦ S2mDecTerm R W F m p.2.2 p.1 p.2.1)).symm
  rw [decoupledSum_eq_triple, key]
  refine tsum_congr fun ρ ↦ ?_
  set gg : ℕ → ℝ := gDisc R W F m ρ with hgg
  have hYeq : Ydisc R W F m ρ = ∑' u : ℕ, gg u := by rw [hgg]; rfl
  by_cases hg : ρ m = 1 ∧ ∀ i, i ≠ m → (ρ i).Coprime W ∧ Squarefree (ρ i)
  · rw [if_pos hg]
    have hpt : ∀ u u' : ℕ, S2mDecTerm R W F m ρ u u' =
        (∏ i ∈ Finset.univ.erase m, (1 : ℝ) / (g (ρ i) : ℝ)) * (gg u * gg u') := by
      intro u u'
      rw [hgg]
      unfold S2mDecTerm gDisc
      by_cases hu : u.Coprime W ∧ Squarefree u
      · by_cases hu' : u'.Coprime W ∧ Squarefree u'
        · rw [if_pos ⟨hg.1, hu.1, hu'.1, hu.2, hu'.2, hg.2⟩, if_pos hu, if_pos hu']
          ring
        · have hbad : ¬ (ρ m = 1 ∧ u.Coprime W ∧ u'.Coprime W ∧ Squarefree u ∧ Squarefree u' ∧
              (∀ i, i ≠ m → (ρ i).Coprime W ∧ Squarefree (ρ i))) :=
            fun hb ↦ hu' ⟨hb.2.2.1, hb.2.2.2.2.1⟩
          rw [if_neg hbad, if_pos hu, if_neg hu']
          ring
      · have hbad : ¬ (ρ m = 1 ∧ u.Coprime W ∧ u'.Coprime W ∧ Squarefree u ∧ Squarefree u' ∧
            (∀ i, i ≠ m → (ρ i).Coprime W ∧ Squarefree (ρ i))) :=
          fun hb ↦ hu ⟨hb.2.1, hb.2.2.2.1⟩
        rw [if_neg hbad, if_neg hu]
        ring
    calc (∑' u : ℕ, ∑' u' : ℕ, S2mDecTerm R W F m ρ u u') = ∑' u : ℕ, ∑' u' : ℕ,
            (∏ i ∈ Finset.univ.erase m, (1 : ℝ) / (g (ρ i) : ℝ)) *
              (gg u * gg u') := by simp_rw [hpt]
      _ = ∑' u : ℕ,
            (∏ i ∈ Finset.univ.erase m, (1 : ℝ) / (g (ρ i) : ℝ)) * gg u * (∑' u' : ℕ, gg u') := by
            refine tsum_congr fun u ↦ ?_
            rw [← tsum_mul_left]
            exact tsum_congr fun u' ↦ by ring
      _ = (∑' u : ℕ, (∏ i ∈ Finset.univ.erase m, (1 : ℝ) / (g (ρ i) : ℝ)) *
              gg u) * (∑' u' : ℕ, gg u') := by rw [tsum_mul_right]
      _ = (∏ i ∈ Finset.univ.erase m, (1 : ℝ) / (g (ρ i) : ℝ)) *
            (∑' u : ℕ, gg u) * (∑' u' : ℕ, gg u') := by rw [tsum_mul_left]
      _ = (∏ i ∈ Finset.univ.erase m, (1 : ℝ) / (g (ρ i) : ℝ)) *
            (Ydisc R W F m ρ) ^ 2 := by rw [hYeq]; ring
  · rw [if_neg hg]
    have hz : ∀ u u' : ℕ, S2mDecTerm R W F m ρ u u' = 0 := by
      intro u u'
      have hbad : ¬ (ρ m = 1 ∧ u.Coprime W ∧ u'.Coprime W ∧ Squarefree u ∧ Squarefree u' ∧
          (∀ i, i ≠ m → (ρ i).Coprime W ∧ Squarefree (ρ i))) := by
        rintro ⟨h1, _, _, _, _, h6⟩
        exact hg ⟨h1, h6⟩
      unfold S2mDecTerm
      rw [if_neg hbad]
    simp only [hz, tsum_zero]

end PrimeGaps

end
