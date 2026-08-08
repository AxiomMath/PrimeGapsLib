/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Batteries.Data.Nat.Gcd
public import PrimeGapsTheory.NumberTheory.PrimeCountingInterval
public import PrimeGapsTheory.Arithmetic.MobiusLcm
public import PrimeGapsTheory.Sieve.S1.CRT

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Factorization and multiplicity of the sieve modulus

Establishes squarefreeness, factor encodings, multiplicity bounds, and an error majorization
for the sieve modulus.

## Main results

* `PrimeGaps.qMod_squarefree`: The sieve modulus is squarefree on permissible support.
* `multiplicity_bound`: Bounds the number of support pairs with fixed modulus.
* `sieve_error_majorization`: Majorizes the sieve error sum by a divisor-weighted modulus sum.
-/

@[expose] public section

open scoped ArithmeticFunction.Moebius Finset

open ArithmeticFunction Finset in
open scoped ArithmeticFunction.zeta in
/-- For `n ≠ 0`, `τ_r n` counts the `r`-tuples of divisors of `n` with `∏ᵢ dᵢ = n`. -/
theorem ArithmeticFunction.tau_apply_eq_card_pi_divisors {r n : ℕ} (hn : n ≠ 0) :
    (τ r) n = #{d : Fin r → n.divisors | ∏ i, (d i : ℕ) = n} := by
  rw [ArithmeticFunction.tau_apply_eq_card_finMulAntidiag]
  refine (Finset.card_bij' (fun d _ i ↦ (d i : ℕ)) (fun e he i ↦ ⟨e i, Nat.mem_divisors.mpr
      ⟨(Nat.mem_finMulAntidiag.mp he).1 ▸ Finset.dvd_prod_of_mem e (Finset.mem_univ i), hn⟩⟩)
    ?_ ?_ ?_ ?_).symm
  · exact fun d hd ↦ Nat.mem_finMulAntidiag.mpr ⟨(Finset.mem_filter.mp hd).2, hn⟩
  · exact fun e he ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Nat.mem_finMulAntidiag.mp he).1⟩
  · exact fun d _ ↦ funext fun i ↦ Subtype.ext rfl
  · exact fun e _ ↦ rfl

namespace PrimeGaps

/-- A pair `(d, e)` of `k` -tuples is *in the support of `λ` * when both `λ d` and `λ e` are
nonzero and the cross-coprimality `(dᵢ, eⱼ) = 1` holds for all `i ≠ j`. -/
def PairInSupport {k : ℕ} (l : (Fin k → ℕ) →₀ ℝ) (d e : Fin k → ℕ) : Prop :=
  l d ≠ 0 ∧ l e ≠ 0 ∧ ∀ i j : Fin k, i ≠ j → (d i).Coprime (e j)

/-- Squarefreeness of the sieve modulus. If `λ` has permissible support
(`Function.HasPermissibleSupport`) and `(d, e)` is in the support of `λ` (`PairInSupport`),
then the modulus `q(d, e) = W · ∏ᵢ lcm (dᵢ, eᵢ)` is squarefree. -/
@[pg_tag "bg246" "slem_S2m_q_squarefree"]
theorem qMod_squarefree
    {k R : ℕ} (W : ℕ) (hWsq : Squarefree W)
    (l : (Fin k → ℕ) →₀ ℝ)
    (hperm : l.HasPermissibleSupport R W)
    (d e : Fin k → ℕ)
    (hpair : PairInSupport l d e) :
    Squarefree (PrimeGaps.qMod W d e) := by
  obtain ⟨hld, hle, hcross⟩ := hpair
  have hd_sq : Squarefree (∏ i, d i) := hperm.squarefree_prod_of_ne_zero hld
  have hd_cop : (∏ i, d i).Coprime W := hperm.coprime_prod_W_of_ne_zero hld
  have he_sq : Squarefree (∏ i, e i) := hperm.squarefree_prod_of_ne_zero hle
  have he_cop : (∏ i, e i).Coprime W := hperm.coprime_prod_W_of_ne_zero hle
  have hdi_sq : ∀ i, Squarefree (d i) := fun i ↦
    hd_sq.squarefree_of_dvd (Finset.dvd_prod_of_mem d (Finset.mem_univ i))
  have hei_sq : ∀ i, Squarefree (e i) := fun i ↦
    he_sq.squarefree_of_dvd (Finset.dvd_prod_of_mem e (Finset.mem_univ i))
  have hcop : ∀ f : Fin k → ℕ, Squarefree (∏ i, f i) →
      ∀ i j : Fin k, i ≠ j → (f i).Coprime (f j) := fun f hf i j hij ↦
    Nat.coprime_of_squarefree_mul <| hf.squarefree_of_dvd <| by
      rw [← Finset.prod_pair hij]
      exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)
  have hdd := hcop d hd_sq
  have hee := hcop e he_sq
  have hlcm_sq : ∀ i, Squarefree (Nat.lcm (d i) (e i)) := by
    intro i
    refine Nat.squarefree_of_factorization_le_one
      (Nat.lcm_ne_zero (hdi_sq i).ne_zero (hei_sq i).ne_zero) fun p ↦ ?_
    rw [Nat.factorization_lcm (hdi_sq i).ne_zero (hei_sq i).ne_zero]
    simp only [Finsupp.sup_apply, sup_le_iff]
    exact ⟨(hdi_sq i).natFactorization_le_one p, (hei_sq i).natFactorization_le_one p⟩
  have hlcm_cop : ∀ i j : Fin k, i ≠ j → (Nat.lcm (d i) (e i)).Coprime (Nat.lcm (d j) (e j)) := by
    intro i j hij
    have hcop_dj : (Nat.lcm (d i) (e i)).Coprime (d j) :=
      Nat.Coprime.coprime_dvd_left (Nat.lcm_dvd_mul (d i) (e i))
        ((hdd i j hij).mul_left (hcross j i hij.symm).symm)
    have hcop_ej : (Nat.lcm (d i) (e i)).Coprime (e j) :=
      Nat.Coprime.coprime_dvd_left (Nat.lcm_dvd_mul (d i) (e i))
        ((hcross i j hij).mul_left (hee i j hij))
    exact Nat.Coprime.coprime_dvd_right (Nat.lcm_dvd_mul (d j) (e j)) (hcop_dj.mul_right hcop_ej)
  have hprod_sq : Squarefree (∏ i, Nat.lcm (d i) (e i)) :=
    Finset.squarefree_prod_of_pairwise_isCoprime
      (fun i _ j _ hij ↦ Nat.coprime_iff_isRelPrime.mp (hlcm_cop i j hij)) fun i _ ↦ hlcm_sq i
  have hW_cop : W.Coprime (∏ i, Nat.lcm (d i) (e i)) := by
    refine Nat.Coprime.prod_right fun i _ ↦ ?_
    have hdi : W.Coprime (d i) :=
      (hd_cop.coprime_dvd_left (Finset.dvd_prod_of_mem d (Finset.mem_univ i))).symm
    have hei : W.Coprime (e i) :=
      (he_cop.coprime_dvd_left (Finset.dvd_prod_of_mem e (Finset.mem_univ i))).symm
    exact Nat.Coprime.coprime_dvd_right (Nat.lcm_dvd_mul (d i) (e i)) (hdi.mul_right hei)
  rw [PrimeGaps.qMod, Nat.squarefree_mul hW_cop]
  exact ⟨hWsq, hprod_sq⟩

open ArithmeticFunction
open scoped ArithmeticFunction.zeta

/-- The coordinatewise lift of `Phi`, sending a pair of vectors `(d, e)` to the `3k` -tuple
`(g_i, a_i, b_i)_i`, where `g_i = gcd (d i) (e i)`, `a_i = d i / g_i`, `b_i = e i / g_i`. The
target `ℕ^{3k}` is modelled as `Fin k → ℕ × ℕ × ℕ`. -/
def phiTuple {k : ℕ} (d e : Fin k → ℕ) : Fin k → ℕ × ℕ × ℕ := fun i ↦ Phi (d i) (e i)

/-- The product of all `3k` coordinates of a tuple in `Fin k → ℕ × ℕ × ℕ`. -/
def phiTupleProd {k : ℕ} (t : Fin k → ℕ × ℕ × ℕ) : ℕ := ∏ i, (t i).1 * (t i).2.1 * (t i).2.2

/-- The fibre `P_r = { (d, e): PrimeGaps.qMod W d e = r }`.

Positivity of the coordinates is encoded by `1 ≤ d i` and `1 ≤ e i`. -/
def PrFibre (W : ℕ) {k : ℕ} (r : ℕ) : Set ((Fin k → ℕ) × (Fin k → ℕ)) :=
  { p | (∀ i, 1 ≤ p.1 i) ∧ (∀ i, 1 ≤ p.2 i) ∧ PrimeGaps.qMod W p.1 p.2 = r }

/-- With `g = gcd (d, e)`, `a = d / g`, `b = e / g`: `d = g·a`, `e = g·b`, `gcd (a, b) = 1` and
`lcm (d, e) = g·a·b`. -/
theorem pair_lcm_decomp {d e : ℕ} (hd : 1 ≤ d) : d = Nat.gcd d e * (d / Nat.gcd d e) ∧
    e = Nat.gcd d e * (e / Nat.gcd d e) ∧
    Nat.Coprime (d / Nat.gcd d e) (e / Nat.gcd d e) ∧
    Nat.lcm d e = Nat.gcd d e * (d / Nat.gcd d e) * (e / Nat.gcd d e) := by
  have hg : 0 < Nat.gcd d e := Nat.gcd_pos_of_pos_left _ hd
  have h1 : d = Nat.gcd d e * (d / Nat.gcd d e) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left d e)).symm
  have h2 : e = Nat.gcd d e * (e / Nat.gcd d e) :=
    (Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)).symm
  refine ⟨h1, h2, Nat.coprime_div_gcd_div_gcd hg, Nat.eq_of_mul_eq_mul_left hg ?_⟩
  calc Nat.gcd d e * Nat.lcm d e = d * e := Nat.gcd_mul_lcm d e
    _ = (Nat.gcd d e * (d / Nat.gcd d e)) * (Nat.gcd d e * (e / Nat.gcd d e)) := by rw [← h1, ← h2]
    _ = Nat.gcd d e * (Nat.gcd d e * (d / Nat.gcd d e) * (e / Nat.gcd d e)) := by ring

/-- On `PrFibre W r`, `phiTupleProd (phiTuple d e) = r / W`. -/
theorem phiTupleProd_phiTuple {W : ℕ} (hW : 1 ≤ W) {k : ℕ} {r : ℕ}
    (d e : Fin k → ℕ) (hp : (d, e) ∈ PrFibre W r) :
    phiTupleProd (phiTuple d e) = r / W := by
  obtain ⟨hd1, _, hq⟩ := hp
  have hq' : W * ∏ i, Nat.lcm (d i) (e i) = r := hq
  rw [show phiTupleProd (phiTuple d e) = ∏ i, Nat.lcm (d i) (e i) from
      Finset.prod_congr rfl fun i _ ↦ ((pair_lcm_decomp (e := e i) (hd1 i)).2.2.2).symm,
    ← hq', Nat.mul_div_cancel_left _ hW]

/-- The map `phiTuple` is injective on `PrFibre W r`: if `(d, e), (d', e') ∈ PrFibre W r` and
`phiTuple d e = phiTuple d' e'`, then `d = d'` and `e = e'`. -/
@[pg_tag "bg246" "slem_S2m_q_factor_bijection"]
theorem phiTuple_injOn {W : ℕ} {k : ℕ} {r : ℕ} (d e d' e' : Fin k → ℕ) (hp : (d, e) ∈ PrFibre W r)
    (hp' : (d', e') ∈ PrFibre W r) (h : phiTuple d e = phiTuple d' e') :
    d = d' ∧ e = e' := by
  obtain ⟨hd1, _, _⟩ := hp
  obtain ⟨hd1', _, _⟩ := hp'
  constructor
  · funext i
    have hi := congrFun h i
    simp only [phiTuple, Phi, Prod.mk.injEq] at hi
    have e1 : d i = (d i).gcd (e i) * (d i / (d i).gcd (e i)) :=
      (pair_lcm_decomp (e := e i) (hd1 i)).1
    have e2 : d' i = (d' i).gcd (e' i) * (d' i / (d' i).gcd (e' i)) :=
      (pair_lcm_decomp (e := e' i) (hd1' i)).1
    rw [e1, e2, hi.2.1, hi.1]
  · funext i
    have hi := congrFun h i
    simp only [phiTuple, Phi, Prod.mk.injEq] at hi
    have e1 : e i = (d i).gcd (e i) * (e i / (d i).gcd (e i)) :=
      (pair_lcm_decomp (e := e i) (hd1 i)).2.1
    have e2 : e' i = (d' i).gcd (e' i) * (e' i / (d' i).gcd (e' i)) :=
      (pair_lcm_decomp (e := e' i) (hd1' i)).2.1
    rw [e1, e2, hi.2.2, hi.1]

/-- For `W ≥ 1` and `r` divisible by `W` with `r ≥ 1`, the fibre `PrFibre W r` is bounded in
size by `τ (3k) (r / W)`. -/
@[pg_tag "bg246" "slem_S2m_q_factor_bijection"]
theorem card_Pr_le {W : ℕ} (hW : 1 ≤ W) {k : ℕ} {r : ℕ} (hr : 1 ≤ r) (hWr : W ∣ r) :
    Nat.card (PrFibre W r (k := k)) ≤ (τ (3 * k)) (r / W) := by
  have hrW : 1 ≤ r / W := (Nat.one_le_div_iff (by omega)).mpr (Nat.le_of_dvd hr hWr)
  have hrWne : r / W ≠ 0 := by omega
  rw [tau_apply_eq_card_pi_divisors hrWne]
  set eqv : Fin 3 × Fin k ≃ Fin (3 * k) := finProdFinEquiv
  set coord : (Fin k → ℕ) → (Fin k → ℕ) → Fin 3 × Fin k → ℕ := fun d e p ↦
      if p.1 = 0 then (phiTuple d e p.2).1
      else if p.1 = 1 then (phiTuple d e p.2).2.1
      else (phiTuple d e p.2).2.2 with hcoord
  set mkc : (Fin k → ℕ) → (Fin k → ℕ) → (Fin (3 * k) → ℕ) :=
    fun d e j ↦ coord d e (eqv.symm j) with hmkc
  have hprod : ∀ (d e : Fin k → ℕ), ∏ j, mkc d e j = phiTupleProd (phiTuple d e) := by
    intro d e
    rw [hmkc, Equiv.prod_comp eqv.symm (coord d e), Fintype.prod_prod_type, Finset.prod_comm]
    unfold phiTupleProd
    refine Finset.prod_congr rfl fun b _ ↦ ?_
    rw [Fin.prod_univ_three, hcoord]
    simp
  have hrecover : ∀ (d e : Fin k → ℕ) (a : Fin 3) (b : Fin k),
      mkc d e (eqv (a, b)) = coord d e (a, b) := fun d e a b ↦ by
    rw [hmkc]
    simp only [Equiv.symm_apply_apply]
  have hprodval : ∀ p : PrFibre W r (k := k), ∏ i, mkc p.val.1 p.val.2 i = r / W := fun p ↦
    (hprod _ _).trans (phiTupleProd_phiTuple hW p.val.1 p.val.2 p.property)
  have hmem_div : ∀ p : PrFibre W r (k := k), ∀ j, mkc p.val.1 p.val.2 j ∈ (r / W).divisors := by
    intro p j
    rw [Nat.mem_divisors]
    exact ⟨hprodval p ▸ Finset.dvd_prod_of_mem (mkc p.val.1 p.val.2) (Finset.mem_univ j), hrWne⟩
  set liftedMkc : PrFibre W r (k := k) → (Fin (3 * k) → (r / W).divisors) :=
    fun p j ↦ ⟨mkc p.val.1 p.val.2 j, hmem_div p j⟩ with hliftedMkc
  have hlifted_prod : ∀ p : PrFibre W r (k := k), ∏ j, ((liftedMkc p j : ℕ)) = r / W := hprodval
  set T : Finset (Fin (3 * k) → (r / W).divisors) :=
    {d ∈ Finset.univ | ∏ i, (d i : ℕ) = r / W} with hT
  have hTmem : ∀ p : PrFibre W r (k := k), liftedMkc p ∈ T := fun p ↦ by
    rw [hT]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlifted_prod p⟩
  have hinjective : Function.Injective
      (fun p : PrFibre W r (k := k) ↦ (⟨liftedMkc p, hTmem p⟩ : T)) := by
    rintro p1 p2 heq
    apply Subtype.ext
    have hlift_eq : liftedMkc p1 = liftedMkc p2 := by
      simpa only [Subtype.mk.injEq] using heq
    have hmkeq : mkc p1.val.1 p1.val.2 = mkc p2.val.1 p2.val.2 := by
      funext j
      have := congrFun hlift_eq j
      simpa [hliftedMkc] using congrArg (fun (x : (r / W).divisors) ↦ (x : ℕ)) this
    have hphi : phiTuple p1.val.1 p1.val.2 = phiTuple p2.val.1 p2.val.2 := by
      funext b
      have h0 := congrFun hmkeq (eqv (0, b))
      have h1 := congrFun hmkeq (eqv (1, b))
      have h2 := congrFun hmkeq (eqv (2, b))
      rw [hrecover, hrecover, hcoord] at h0 h1 h2
      simp only at h0 h1 h2
      exact Prod.ext h0 (Prod.ext h1 h2)
    obtain ⟨inj1, inj2⟩ :=
      phiTuple_injOn p1.val.1 p1.val.2 p2.val.1 p2.val.2 p1.property p2.property hphi
    exact Prod.ext inj1 inj2
  calc Nat.card (PrFibre W r (k := k)) ≤ Nat.card T := Nat.card_le_card_of_injective _ hinjective
    _ = #T := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]

/-- Encoding of a pair `(d, e)` of `Fin k → ℕ` tuples into a `Fin (3*k) → ℕ` factorisation. Under
`finProdFinEquiv: Fin 3 × Fin k ≃ Fin (3 * k)`, slot `(0, i)` holds `gcd (d i) (e i)` (with the
extra `W` factor folded in at `i = 0`), slot `(1, i)` holds `d i / gcd (d i) (e i)`, and
slot `(2, i)` holds `e i / gcd (d i) (e i)`. The product of all `3k` slots equals
`W · ∏ i lcm (d i) (e i) = PrimeGaps.qMod W d e`. -/
noncomputable def encFactor {k : ℕ} (W : ℕ) (d e : Fin k → ℕ) : Fin (3 * k) → ℕ := fun j ↦
  let p := (finProdFinEquiv (m := 3) (n := k)).symm j
  let s := p.1
  let i := p.2
  if s = 0 then Nat.gcd (d i) (e i) * (if i.val = 0 then W else 1)
  else if s = 1 then d i / Nat.gcd (d i) (e i)
  else e i / Nat.gcd (d i) (e i)

/-- `∏ⱼ encFactor W d e j = r` for a support pair `(d, e)` with `qMod W d e = r`. -/
theorem encFactor_prod_eq
    {k R : ℕ} (hk : 0 < k) (W : ℕ) (l : (Fin k → ℕ) →₀ ℝ)
    (hl : l.HasPermissibleSupport R W)
    (d e : Fin k → ℕ) (hde : PairInSupport l d e) (r : ℕ)
    (hmod : PrimeGaps.qMod W d e = r) :
    ∏ j, encFactor W d e j = r := by
  obtain ⟨hld, _, _⟩ := hde
  have hd_sq : Squarefree (∏ i, d i) :=
    (Finset.mem_permissibleSupport_iff.mp (hl (Finsupp.mem_support_iff.mpr hld))).2.2
  have hdi_pos : ∀ i, 0 < d i := fun i ↦ Nat.pos_of_ne_zero (hd_sq.squarefree_of_dvd
      (Finset.dvd_prod_of_mem d (Finset.mem_univ i))).ne_zero
  rw [← Equiv.prod_comp (finProdFinEquiv (m := 3) (n := k)) (encFactor W d e),
    Fintype.prod_prod_type_right]
  have key : ∀ i : Fin k, (∏ s : Fin 3, encFactor W d e (finProdFinEquiv (s, i))) =
        Nat.lcm (d i) (e i) * (if i.val = 0 then W else 1) := by
    intro i
    rw [Fin.prod_univ_three]
    simp only [encFactor, Equiv.symm_apply_apply, Fin.isValue, if_true, reduceIte, Fin.reduceEq]
    have hglcm : Nat.gcd (d i) (e i) * (d i / Nat.gcd (d i) (e i)) *
        (e i / Nat.gcd (d i) (e i)) = Nat.lcm (d i) (e i) :=
      ((pair_lcm_decomp (e := e i) (hdi_pos i)).2.2.2).symm
    rw [← hglcm]; ring
  rw [Finset.prod_congr rfl (fun i _ ↦ key i), Finset.prod_mul_distrib]
  have hWprod : (∏ i : Fin k, (if i.val = 0 then W else 1)) = W := by
    rw [Finset.prod_eq_single (⟨0, hk⟩ : Fin k)]
    · simp
    · exact fun b _ hb ↦ by simp [show b.val ≠ 0 from fun hbv ↦ hb (Fin.ext hbv)]
    · exact fun hb ↦ absurd (Finset.mem_univ _) hb
  rw [hWprod, ← hmod, qMod]
  ring

/-- Every slot of `encFactor W d e` is at least `1`, for `(d, e)` in the support of `l`. -/
theorem encFactor_pos
    {k R : ℕ} (W : ℕ) (hW : 1 ≤ W) (l : (Fin k → ℕ) →₀ ℝ)
    (hl : l.HasPermissibleSupport R W)
    (d e : Fin k → ℕ) (hde : PairInSupport l d e) :
    ∀ j, 1 ≤ encFactor W d e j := by
  obtain ⟨hld, hle, _⟩ := hde
  have hd_sq : Squarefree (∏ i, d i) :=
    (Finset.mem_permissibleSupport_iff.mp (hl (Finsupp.mem_support_iff.mpr hld))).2.2
  have he_sq : Squarefree (∏ i, e i) :=
    (Finset.mem_permissibleSupport_iff.mp (hl (Finsupp.mem_support_iff.mpr hle))).2.2
  have hdi_pos : ∀ i, 0 < d i := fun i ↦ Nat.pos_of_ne_zero (hd_sq.squarefree_of_dvd
      (Finset.dvd_prod_of_mem d (Finset.mem_univ i))).ne_zero
  have hei_pos : ∀ i, 0 < e i := fun i ↦ Nat.pos_of_ne_zero (he_sq.squarefree_of_dvd
      (Finset.dvd_prod_of_mem e (Finset.mem_univ i))).ne_zero
  intro j
  set p := (finProdFinEquiv (m := 3) (n := k)).symm j
  set s := p.1
  set i := p.2
  have hval : encFactor W d e j = if s = 0 then Nat.gcd (d i) (e i) * (if i.val = 0 then W else 1)
      else if s = 1 then d i / Nat.gcd (d i) (e i)
      else e i / Nat.gcd (d i) (e i) := rfl
  rw [hval]
  have hg_pos : 0 < Nat.gcd (d i) (e i) := by
    have := hdi_pos i
    positivity
  split_ifs
  · exact Nat.mul_le_mul hg_pos hW
  · rw [Nat.mul_one]; exact hg_pos
  · exact Nat.div_pos (Nat.le_of_dvd (hdi_pos i) (Nat.gcd_dvd_left _ _)) hg_pos
  · exact Nat.div_pos (Nat.le_of_dvd (hei_pos i) (Nat.gcd_dvd_right _ _)) hg_pos

/-- `encFactor W` is injective on the support pairs `(d, e)` with `qMod W d e = r`. -/
theorem encFactor_injective
    {k R : ℕ} (W : ℕ) (hW : 0 < W) (l : (Fin k → ℕ) →₀ ℝ)
    (hl : l.HasPermissibleSupport R W) (r : ℕ) :
    Set.InjOn (fun p : (Fin k → ℕ) × (Fin k → ℕ) ↦ encFactor W p.1 p.2)
      {p | PairInSupport l p.1 p.2 ∧ PrimeGaps.qMod W p.1 p.2 = r} := by
  intro x hx y hy hxy
  simp only [Set.mem_ofPred_eq] at hx hy
  obtain ⟨d, e⟩ := x
  obtain ⟨d', e'⟩ := y
  simp only at hxy
  obtain ⟨hld, _, _⟩ := hx.1
  have hd_sq : Squarefree (∏ i, d i) :=
    (Finset.mem_permissibleSupport_iff.mp (hl (Finsupp.mem_support_iff.mpr hld))).2.2
  have hdi_pos : ∀ i, 0 < d i := fun i ↦ Nat.pos_of_ne_zero (hd_sq.squarefree_of_dvd
      (Finset.dvd_prod_of_mem d (Finset.mem_univ i))).ne_zero
  have hcoord : ∀ i : Fin k, d i = d' i ∧ e i = e' i := by
    intro i
    have hc : 0 < (if (i : Fin k).val = 0 then W else 1) := by
      split_ifs
      · exact hW
      · exact one_pos
    have h0 := congrFun hxy (finProdFinEquiv (m := 3) (n := k) ((0 : Fin 3), i))
    have h1 := congrFun hxy (finProdFinEquiv (m := 3) (n := k) ((1 : Fin 3), i))
    have h2 := congrFun hxy (finProdFinEquiv (m := 3) (n := k) ((2 : Fin 3), i))
    simp only [encFactor, Equiv.symm_apply_apply, Fin.isValue, if_true,
      reduceIte, Fin.reduceEq] at h0 h1 h2
    have hgeq : Nat.gcd (d i) (e i) = Nat.gcd (d' i) (e' i) := Nat.eq_of_mul_eq_mul_right hc h0
    refine ⟨?_, ?_⟩
    · rw [← Nat.mul_div_cancel' (Nat.gcd_dvd_left (d i) (e i)),
        ← Nat.mul_div_cancel' (Nat.gcd_dvd_left (d' i) (e' i)), h1, hgeq]
    · rw [← Nat.mul_div_cancel' (Nat.gcd_dvd_right (d i) (e i)),
        ← Nat.mul_div_cancel' (Nat.gcd_dvd_right (d' i) (e' i)), h2, hgeq]
  exact Prod.mk_inj.mpr ⟨funext fun i ↦ (hcoord i).1, funext fun i ↦ (hcoord i).2⟩

/-- For squarefree `r`, the support pairs `(d, e)` with `qMod W d e = r` number at most
`τ_(3k) r`. -/
@[pg_tag "bg246" "slem_S2m_q_factor_count"]
theorem multiplicity_bound
    {k R : ℕ} (hk : 0 < k) (W : ℕ) (hW : 0 < W) (l : (Fin k → ℕ) →₀ ℝ)
    (hl : l.HasPermissibleSupport R W)
    (r : ℕ) (hr : Squarefree r) :
    Nat.card {p : (Fin k → ℕ) × (Fin k → ℕ) //
        PairInSupport l p.1 p.2 ∧ PrimeGaps.qMod W p.1 p.2 = r} ≤
          (τ (3 * k)) r := by
  classical
  have hrne : r ≠ 0 := hr.ne_zero
  rw [tau_apply_eq_card_pi_divisors hrne]
  have hprodval : ∀ p : {p : (Fin k → ℕ) × (Fin k → ℕ) // PairInSupport l p.1 p.2 ∧
      PrimeGaps.qMod W p.1 p.2 = r}, ∏ i, encFactor W p.val.1 p.val.2 i = r := fun p ↦
    encFactor_prod_eq hk W l hl p.val.1 p.val.2 p.property.1 r p.property.2
  have hmem : ∀ (p : {p : (Fin k → ℕ) × (Fin k → ℕ) // PairInSupport l p.1 p.2 ∧
                        PrimeGaps.qMod W p.1 p.2 = r})
                 (j : Fin (3 * k)),
      encFactor W p.val.1 p.val.2 j ∈ r.divisors := by
    intro p j
    have hdvd := Finset.dvd_prod_of_mem (encFactor W p.val.1 p.val.2) (Finset.mem_univ j)
    rw [hprodval p] at hdvd
    exact Nat.mem_divisors.mpr ⟨hdvd, hrne⟩
  set liftedEnc : {p : (Fin k → ℕ) × (Fin k → ℕ) // PairInSupport l p.1 p.2 ∧
                      PrimeGaps.qMod W p.1 p.2 = r} →
                  (Fin (3 * k) → r.divisors) :=
    fun p j ↦ ⟨encFactor W p.val.1 p.val.2 j, hmem p j⟩ with hliftedEnc
  have hlifted_prod : ∀ p, ∏ j, ((liftedEnc p j : ℕ)) = r := hprodval
  set T : Finset (Fin (3 * k) → r.divisors) :=
    {d ∈ Finset.univ | ∏ i, (d i : ℕ) = r} with hT
  have hTmem : ∀ p, liftedEnc p ∈ T := fun p ↦ by
    rw [hT]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlifted_prod p⟩
  have hinjective : Function.Injective (fun p : {p : (Fin k → ℕ) × (Fin k → ℕ) //
                PairInSupport l p.1 p.2 ∧ PrimeGaps.qMod W p.1 p.2 = r} ↦
         (⟨liftedEnc p, hTmem p⟩ : T)) := by
    rintro p1 p2 heq
    apply Subtype.ext
    have hlift_eq : liftedEnc p1 = liftedEnc p2 := by
      simpa only [Subtype.mk.injEq] using heq
    have henceq : encFactor W p1.val.1 p1.val.2 = encFactor W p2.val.1 p2.val.2 := by
      funext j
      have := congrFun hlift_eq j
      simpa [hliftedEnc] using congrArg (fun (x : r.divisors) ↦ (x : ℕ)) this
    exact encFactor_injective W hW l hl r p1.property p2.property henceq
  exact (Nat.card_le_card_of_injective _ hinjective).trans_eq
    (by rw [Nat.card_eq_fintype_card, Fintype.card_coe])

/-- The function-support of a `Finsupp` weight is finite. -/
theorem support_finite {k : ℕ} (l : (Fin k → ℕ) →₀ ℝ) : (Function.support l).Finite := by
  rw [Finsupp.fun_support_eq]; exact l.support.finite_toSet

/-- The index set of the majorizing sum, the positive naturals `r` with `r ≤ R²·W`, is finite. -/
theorem rhs_finite (R : ℝ) (W : ℕ) : Finite {r : ℕ // 0 < r ∧ (↑r : ℝ) ≤ R ^ 2 * W} := by
  have hfin : {r : ℕ | 0 < r ∧ (↑r : ℝ) ≤ R ^ 2 * W}.Finite := by
    refine Set.Finite.subset (Set.finite_Iio (⌈R ^ 2 * W⌉₊ + 1)) fun r hr ↦ ?_
    simp only [Set.mem_ofPred_eq, Set.mem_Iio] at hr ⊢
    exact Nat.lt_succ_of_le (by exact_mod_cast hr.2.trans (Nat.le_ceil _))
  exact hfin.to_subtype

/-- The index set of the error sum, the pairs `(d, e)` in the support of `l`, is finite. -/
theorem lhs_finite {k : ℕ} (l : (Fin k → ℕ) →₀ ℝ) (hl : (Function.support l).Finite) :
    Finite {p : (Fin k → ℕ) × (Fin k → ℕ) // PairInSupport l p.1 p.2} := by
  have hfin : {p : (Fin k → ℕ) × (Fin k → ℕ) | PairInSupport l p.1 p.2}.Finite := by
    refine Set.Finite.subset (hl.prod hl) fun p hp ↦ ?_
    simp only [Set.mem_ofPred_eq] at hp
    exact ⟨hp.1, hp.2.1⟩
  exact hfin.to_subtype

/-- On permissible support, `0 < qMod W d e` and `qMod W d e ≤ R² · W`. -/
theorem qMod_size_bound {k : ℕ} (R : ℝ) (W : ℕ) (hRnonneg : 0 ≤ R) (hWsq : Squarefree W)
    (l : (Fin k → ℕ) →₀ ℝ)
    (hperm : l.HasPermissibleSupport ⌊R⌋₊ W)
    (d e : Fin k → ℕ) (hpair : PairInSupport l d e) :
    0 < PrimeGaps.qMod W d e ∧
      (↑(PrimeGaps.qMod W d e) : ℝ) ≤ R ^ 2 * W := by
  refine ⟨Nat.pos_of_ne_zero (qMod_squarefree W hWsq l hperm d e hpair).ne_zero, ?_⟩
  obtain ⟨hld, hle, _⟩ := hpair
  have hC1d : (↑(∏ i, d i) : ℝ) ≤ R :=
    le_trans (by exact_mod_cast hperm.prod_lt_R_of_ne_zero hld) (Nat.floor_le hRnonneg)
  have hC1e : (↑(∏ i, e i) : ℝ) ≤ R :=
    le_trans (by exact_mod_cast hperm.prod_lt_R_of_ne_zero hle) (Nat.floor_le hRnonneg)
  have hpd_pos : 0 < ∏ i, d i :=
    Nat.pos_of_ne_zero (hperm.squarefree_prod_of_ne_zero hld).ne_zero
  have hpe_pos : 0 < ∏ i, e i :=
    Nat.pos_of_ne_zero (hperm.squarefree_prod_of_ne_zero hle).ne_zero
  have hle_prod : (∏ i, (d i).lcm (e i)) ≤ (∏ i, d i) * (∏ i, e i) :=
    Nat.le_of_dvd (Nat.mul_pos hpd_pos hpe_pos) (by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_dvd_prod_of_dvd _ _ fun i _ ↦ Nat.lcm_dvd_mul (d i) (e i))
  have hqle : (↑(qMod W d e) : ℝ) ≤ W * ((∏ i, d i : ℕ) : ℝ) * ((∏ i, e i : ℕ) : ℝ) := by
    rw [show qMod W d e = W * ∏ i, (d i).lcm (e i) from rfl]
    push_cast
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mod_cast hle_prod) (by positivity)
  have hR_pos : (0 : ℝ) < R := lt_of_lt_of_le (by exact_mod_cast hpd_pos) hC1d
  have hprod_le : ((∏ i, d i : ℕ) : ℝ) * ((∏ i, e i : ℕ) : ℝ) ≤ R ^ 2 := by
    rw [sq]
    exact mul_le_mul hC1d hC1e (by positivity) hR_pos.le
  calc (↑(qMod W d e) : ℝ) ≤ W * (((∏ i, d i : ℕ) : ℝ) * ((∏ i, e i : ℕ) : ℝ)) := by
        rw [← mul_assoc]; exact hqle
    _ ≤ W * R ^ 2 := mul_le_mul_of_nonneg_left hprod_le (by positivity)
    _ = R ^ 2 * W := by ring

/-- Real-valued form of `μ(r)² = 1` for squarefree `r`. -/
theorem moebius_sq_eq_one_of_squarefree (r : ℕ) (hr : Squarefree r) : ((μ r : ℝ)) ^ 2 = 1 := by
  rw [← Int.cast_pow, ArithmeticFunction.moebius_sq_eq_one_of_squarefree hr, Int.cast_one]

/-- Majorization of the `S₂ₘ` sieve error sum. For `k ≥ 2` and a weight `l` with permissible
support, the error sum over support pairs is bounded by `l.maxRealAbs` squared times the diagonal
sum `∑ᵣ μ(r)² · τ (3k) r · E(N, r)` taken over `0 < r ≤ R² · W`, where
`E = primeCountingIocError N (2 * N)`. -/
@[pg_tag "bg246" "slem_S2m_triangle"]
theorem sieve_error_majorization {k : ℕ} (hk : 2 ≤ k) (N : ℕ) (R : ℝ) (W : ℕ)
    (hRnonneg : 0 ≤ R) (hWsq : Squarefree W)
    (l : (Fin k → ℕ) →₀ ℝ) (hperm : l.HasPermissibleSupport ⌊R⌋₊ W) :
    (∑' p : {p : (Fin k → ℕ) × (Fin k → ℕ) // PairInSupport l p.1 p.2},
        |l p.1.1 * l p.1.2| * Nat.primeCountingIocError N (2 * N)
          (PrimeGaps.qMod W p.1.1 p.1.2)) ≤
      l.maxRealAbs ^ 2 * (∑' r : {r : ℕ // 0 < r ∧ (↑r : ℝ) ≤ R ^ 2 * W},
          ((μ r) : ℝ) ^ 2 * ((ζ ^ (3 * k)) (r : ℕ) : ℝ) *
            Nat.primeCountingIocError N (2 * N) r) := by
  have hWpos : 0 < W := Nat.pos_of_ne_zero hWsq.ne_zero
  have hl : (Function.support l).Finite := support_finite l
  haveI : Finite {p : (Fin k → ℕ) × (Fin k → ℕ) // PairInSupport l p.1 p.2} := lhs_finite l hl
  haveI : Finite {r : ℕ // 0 < r ∧ (↑r : ℝ) ≤ R ^ 2 * W} := rhs_finite R W
  haveI : Fintype {p : (Fin k → ℕ) × (Fin k → ℕ) // PairInSupport l p.1 p.2} := Fintype.ofFinite _
  haveI : Fintype {r : ℕ // 0 < r ∧ (↑r : ℝ) ≤ R ^ 2 * W} := Fintype.ofFinite _
  rw [tsum_fintype, tsum_fintype]
  have hstep1 : ∑ b : {p : (Fin k → ℕ) × (Fin k → ℕ) // PairInSupport l p.1 p.2},
        |l b.1.1 * l b.1.2| * Nat.primeCountingIocError N (2 * N) (qMod W b.1.1 b.1.2) ≤
      ∑ b : {p : (Fin k → ℕ) × (Fin k → ℕ) // PairInSupport l p.1 p.2},
        l.maxRealAbs ^ 2 * Nat.primeCountingIocError N (2 * N) (qMod W b.1.1 b.1.2) := by
    refine Finset.sum_le_sum fun b _ ↦
      mul_le_mul_of_nonneg_right ?_ (Nat.primeCountingIocError_nonneg _ _ _)
    rw [abs_mul, sq]
    exact mul_le_mul Finsupp.le_maxRealAbs Finsupp.le_maxRealAbs (abs_nonneg _)
      Finsupp.maxRealAbs_nonneg
  refine hstep1.trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  classical
  set sP : Finset ((Fin k → ℕ) × (Fin k → ℕ)) :=
    {p ∈ (hl.toFinset ×ˢ hl.toFinset) | PairInSupport l p.1 p.2} with hsP
  have hsP_iff : ∀ x : (Fin k → ℕ) × (Fin k → ℕ), x ∈ sP ↔ PairInSupport l x.1 x.2 := by
    intro x
    simp only [hsP, Finset.mem_filter, Finset.mem_product, Set.Finite.mem_toFinset,
      Function.mem_support]
    exact ⟨And.right, fun h ↦ ⟨⟨h.1, h.2.1⟩, h⟩⟩
  set sR : Finset ℕ :=
    {r ∈ (Finset.range (⌈R ^ 2 * W⌉₊ + 1)) | 0 < r ∧ (↑r : ℝ) ≤ R ^ 2 * W} with hsR
  have hsR_iff : ∀ r : ℕ, r ∈ sR ↔ (0 < r ∧ (↑r : ℝ) ≤ R ^ 2 * W) := by
    intro r
    simp only [hsR, Finset.mem_filter, Finset.mem_range]
    exact ⟨And.right, fun h ↦
      ⟨Nat.lt_succ_of_le (by exact_mod_cast h.2.trans (Nat.le_ceil _)), h⟩⟩
  rw [← Finset.sum_subtype sP hsP_iff
      (fun p ↦ Nat.primeCountingIocError N (2 * N) (qMod W p.1 p.2)),
    ← Finset.sum_subtype sR hsR_iff (fun r ↦ ((μ r) : ℝ) ^ 2 * ((ζ ^ (3 * k)) r : ℝ) *
      Nat.primeCountingIocError N (2 * N) r)]
  set q : (Fin k → ℕ) × (Fin k → ℕ) → ℕ := fun p ↦ qMod W p.1 p.2 with hq
  rw [show (fun a : (Fin k → ℕ) × (Fin k → ℕ) ↦
        Nat.primeCountingIocError N (2 * N) (qMod W a.1 a.2)) =
        (fun a ↦ (fun r ↦ Nat.primeCountingIocError N (2 * N) r) (q a)) from rfl,
    Finset.sum_comp (fun r ↦ Nat.primeCountingIocError N (2 * N) r) q]
  have hsub : Finset.image q sP ⊆ sR := by
    intro r hr
    rw [Finset.mem_image] at hr
    obtain ⟨p, hp, rfl⟩ := hr
    exact (hsR_iff (q p)).mpr
      (qMod_size_bound R W hRnonneg hWsq l hperm p.1 p.2 ((hsP_iff p).mp hp))
  have hterm : ∀ b ∈ Finset.image q sP,
      (#{a ∈ sP | q a = b} : ℕ) • Nat.primeCountingIocError N (2 * N) b ≤
        ((μ b) : ℝ) ^ 2 * ((ζ ^ (3 * k)) b : ℝ) * Nat.primeCountingIocError N (2 * N) b := by
    intro b hb
    rw [Finset.mem_image] at hb
    obtain ⟨p, hp, hbp⟩ := hb
    have hsq : Squarefree b := by
      rw [← hbp]
      exact qMod_squarefree W hWsq l hperm p.1 p.2 ((hsP_iff p).mp hp)
    rw [moebius_sq_eq_one_of_squarefree b hsq, one_mul]
    have hcard : (#{a ∈ sP | q a = b} : ℕ) ≤ (ζ ^ (3 * k)) b := by
      set S : Set ((Fin k → ℕ) × (Fin k → ℕ)) :=
        {p | PairInSupport l p.1 p.2 ∧ qMod W p.1 p.2 = b} with hS
      have hSfin : S.Finite := by
        refine Set.Finite.subset (hl.prod hl) fun x hx ↦ ?_
        obtain ⟨hpair, _⟩ := hx
        exact ⟨hpair.1, hpair.2.1⟩
      have hfin_eq : {a ∈ sP | q a = b} = hSfin.toFinset := by
        ext x
        simp only [Finset.mem_filter, Set.Finite.mem_toFinset, hS, Set.mem_ofPred_eq, hsP_iff, hq]
      rw [hfin_eq, ← Nat.card_eq_card_finite_toFinset hSfin]
      exact multiplicity_bound (Nat.zero_lt_of_lt hk) W hWpos l hperm b hsq
    rw [nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (mod_cast hcard)
      (Nat.primeCountingIocError_nonneg N (2 * N) b)
  have hnn : ∀ b ∈ sR, (0 : ℝ) ≤ ((μ b) : ℝ) ^ 2 * ((ζ ^ (3 * k)) b : ℝ) *
        Nat.primeCountingIocError N (2 * N) b := fun b _ ↦
    mul_nonneg (by positivity) (Nat.primeCountingIocError_nonneg N (2 * N) b)
  exact (Finset.sum_le_sum hterm).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hsub fun b hb _ ↦ hnn b hb)

end PrimeGaps
