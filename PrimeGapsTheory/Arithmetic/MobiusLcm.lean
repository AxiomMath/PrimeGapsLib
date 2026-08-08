/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Nat.Factorization.Root
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

import PrimeGapsTheory.Tactic.PaperTag

/-!
# The Möbius function and an LCM pairing

A Möbius divisor identity and a bijection between paired divisors with prescribed least common
multiple.

## Main definitions

* `inDomain`: The domain condition for the LCM pairing.
* `inCodomain`: The codomain condition for the LCM pairing.
* `Phi`: The forward map of the LCM pairing.
* `Psi`: The candidate inverse of the LCM pairing.

## Main results

* `moebius_sq_eq_sum_moebius_of_sq_dvd`: A divisor-sum formula for the square of the Möbius
  function.
-/

@[expose] public section

open ArithmeticFunction

open scoped ArithmeticFunction.Moebius

namespace ArithmeticFunction

/-- For every positive integer $v$, the square of the Moebius function equals the sum of $\mu(e)$
over all positive integers $e$ (equivalently, divisors $e$ of $v$) such that $e^2 \mid v$. Since
$v \ge 1$, the condition $e^2 \mid v$ implies $e \mid v$, so restricting the index set to
`v.divisors` does not change the sum. -/
@[pg_tag "bg246" "slem_mu2_sqfree_inv"]
theorem moebius_sq_eq_sum_moebius_of_sq_dvd (v : ℕ) (hv : 0 < v) :
    (μ v) ^ 2 =
      ∑ e ∈ v.divisors with e ^ 2 ∣ v, μ e := by
  set w := Nat.floorRoot 2 v with hw_def
  have hw0 : w ≠ 0 := by
    rw [hw_def, Nat.floorRoot_ne_zero]
    exact ⟨two_ne_zero, hv.ne'⟩
  have hset : {e ∈ v.divisors | e ^ 2 ∣ v} = w.divisors := by
    ext e
    simp only [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨fun ⟨_, he⟩ ↦ ?_, fun ⟨he, _⟩ ↦ ?_⟩
    · rw [hw_def, ← Nat.pow_dvd_iff_dvd_floorRoot]
      exact ⟨he, hw0⟩
    · have he2 : e ^ 2 ∣ v := (Nat.pow_dvd_iff_dvd_floorRoot).mpr (hw_def ▸ he)
      exact ⟨⟨(dvd_pow_self e (n := 2) two_ne_zero).trans he2, hv.ne'⟩, he2⟩
  have hsum : (∑ e ∈ w.divisors, μ e) = (1 : ArithmeticFunction ℤ) w := by
    rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta]
  rw [hset, hsum, ArithmeticFunction.one_apply, ArithmeticFunction.moebius_sq]
  have hiff : w = 1 ↔ Squarefree v := by
    refine ⟨fun hw1 x hx ↦ ?_, fun hsf ↦ ?_⟩
    · have hxw : x ∣ w := by
        rw [hw_def, ← Nat.pow_dvd_iff_dvd_floorRoot, sq]
        exact hx
      rw [hw1, Nat.dvd_one] at hxw
      exact hxw ▸ isUnit_one
    · exact Nat.isUnit_iff.mp (hsf w (sq w ▸ (hw_def ▸ Nat.floorRoot_pow_dvd : w ^ 2 ∣ v)))
  simp only [hiff]

end ArithmeticFunction

namespace PrimeGaps

/-- A pair `(d, e)` lies in `𝒟_m` iff `d` and `e` are squarefree positive integers whose lcm equals
`m`. -/
def inDomain (m d e : ℕ) : Prop := 0 < d ∧ 0 < e ∧ Squarefree d ∧ Squarefree e ∧ Nat.lcm d e = m

/-- A triple `(g, a, b)` lies in `𝒞_m` iff `g, a, b` are pairwise coprime positive integers with
product `m`. -/
def inCodomain (m g a b : ℕ) : Prop :=
  0 < g ∧ 0 < a ∧ 0 < b ∧ Nat.Coprime g a ∧ Nat.Coprime g b ∧ Nat.Coprime a b ∧ g * a * b = m

/-- The map `Φ_m` sends `(d, e)` to `(gcd d e, d / gcd d e, e / gcd d e)`. -/
def Phi (d e : ℕ) : ℕ × ℕ × ℕ := (Nat.gcd d e, d / Nat.gcd d e, e / Nat.gcd d e)

/-- The candidate inverse `Ψ_m` sends `(g, a, b)` to `(g * a, g * b)`. -/
def Psi (g a b : ℕ) : ℕ × ℕ := (g * a, g * b)

/-- Well-definedness of `Φ_m`: for every `(d, e) ∈ 𝒟_m`, the triple `Φ_m (d, e)` lies in `𝒞_m`. -/
theorem phi_maps_into_codomain (m d e : ℕ) (h : inDomain m d e) :
    inCodomain m (Phi d e).1 (Phi d e).2.1 (Phi d e).2.2 := by
  obtain ⟨hd, he, hsd, hse, hlcm⟩ := h
  simp only [Phi, inCodomain]
  set g := Nat.gcd d e with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left e hd
  have hgd : g ∣ d := Nat.gcd_dvd_left d e
  have hge : g ∣ e := Nat.gcd_dvd_right d e
  have hdeq : g * (d / g) = d := Nat.mul_div_cancel' hgd
  have heeq : g * (e / g) = e := Nat.mul_div_cancel' hge
  have hgapos : 0 < d / g := Nat.div_pos (Nat.le_of_dvd hd hgd) hgpos
  have hgbpos : 0 < e / g := Nat.div_pos (Nat.le_of_dvd he hge) hgpos
  refine ⟨hgpos, hgapos, hgbpos, Nat.coprime_of_squarefree_mul (hdeq.symm ▸ hsd),
    Nat.coprime_of_squarefree_mul (heeq.symm ▸ hse), Nat.coprime_div_gcd_div_gcd hgpos, ?_⟩
  refine (Nat.eq_of_mul_eq_mul_left hgpos ?_).symm
  rw [show g * m = d * e from hlcm ▸ Nat.gcd_mul_lcm d e]
  nth_rewrite 1 [← hdeq, ← heeq]
  ring

/-- Well-definedness of `Ψ_m`: for every `(g, a, b) ∈ 𝒞_m`, the pair
`Ψ_m (g, a, b) = (g * a, g * b)` lies in `𝒟_m`. -/
theorem psi_maps_into_domain (m g a b : ℕ) (hm : Squarefree m) (h : inCodomain m g a b) :
    inDomain m (Psi g a b).1 (Psi g a b).2 := by
  obtain ⟨hg, ha, hb, -, -, hab, hprod⟩ := h
  simp only [Psi, inDomain]
  refine ⟨Nat.mul_pos hg ha, Nat.mul_pos hg hb, hm.squarefree_of_dvd ⟨b, by rw [← hprod]⟩,
    hm.squarefree_of_dvd ⟨a, by rw [← hprod]; ring⟩, ?_⟩
  have hmul := Nat.gcd_mul_lcm (g * a) (g * b)
  rw [Nat.gcd_mul_left, hab, Nat.mul_one] at hmul
  refine Nat.eq_of_mul_eq_mul_left hg ?_
  rw [hmul, ← hprod]
  ring

/-- Left inverse: `Ψ_m ∘ Φ_m = id` on `𝒟_m`. -/
theorem psi_phi_id (m d e : ℕ) (h : inDomain m d e) :
    Psi (Phi d e).1 (Phi d e).2.1 (Phi d e).2.2 = (d, e) := by
  obtain ⟨hd, he, hsd, hse, hlcm⟩ := h
  simp only [Phi, Psi]
  rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left d e), Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)]

/-- Right inverse: `Φ_m ∘ Ψ_m = id` on `𝒞_m`. -/
@[pg_tag "bg246" "slem_pair_lcm_bijection"]
theorem phi_psi_id (m g a b : ℕ) (h : inCodomain m g a b) :
    Phi (Psi g a b).1 (Psi g a b).2 = (g, a, b) := by
  obtain ⟨hg, -, -, -, -, hab, -⟩ := h
  simp only [Phi, Psi]
  rw [show Nat.gcd (g * a) (g * b) = g by rw [Nat.gcd_mul_left, hab, Nat.mul_one],
    Nat.mul_div_cancel_left a hg, Nat.mul_div_cancel_left b hg]

end PrimeGaps
