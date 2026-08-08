/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.Common.Substitution.FirstMoment
public import PrimeGapsTheory.Sieve.S2m.DecouplePhiLcm
public import PrimeGapsTheory.Sieve.S2m.MainCRT
public import PrimeGapsTheory.Sieve.S2m.Mobius

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Second-moment substitution of transformed weights

Reindexes the restricted second-moment sum and substitutes the transformed weights.

## Main results

* `lem_S2m_substitute_ym`: Identifies the restricted double sum with the transformed-weight sum
  for large parameters.
-/

@[expose] public section

open scoped ArithmeticFunction.Moebius

open scoped ArithmeticFunction.detotient

namespace PrimeGaps

/-- The `g` -normalized weighted sum of
`PrimeGaps.ym m lam (boldA u s) * PrimeGaps.ym m lam (boldB u s)`, with diagonal entries of `s`
equal to one. -/
noncomputable def ymWeightedSum {k : ℕ} (m : Fin k) (lam : (Fin k → ℕ) →₀ ℝ) : ℝ :=
  ∑' u : Fin k → ℕ, ∑' s : Fin k → Fin k → ℕ,
    (if ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
          PrimeGaps.LemS1RestrictSij.RestrictedCoprime u s) then
        (∏ i, (μ (u i) : ℝ) ^ 2 / (g (u i) : ℝ)) *
        (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
            (μ (s p.1 p.2) : ℝ) / (g (s p.1 p.2) : ℝ) ^ 2) *
        PrimeGaps.ym m lam (boldA u s) * PrimeGaps.ym m lam (boldB u s)
      else 0)

/-- The finite double sum of `restrictedSummand` over `D`. -/
noncomputable def S2mFull {k : ℕ} (h : Fin k → ℕ) (m : Fin k) (modulus : ℕ)
    (l : (Fin k → ℕ) →₀ ℝ) (D : Finset (Fin k → ℕ)) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ D, restrictedSummand h m modulus l (d, e)

/-- The `tsum` of `restrictedSummand` collapses to `S2mFull h m modulus l D` for some finite `D`
containing the support of `l`. -/
theorem restrictedSummand_tsum_eq_S2mFull {k : ℕ} (h : Fin k → ℕ) (m : Fin k)
    (modulus : ℕ) (l : (Fin k → ℕ) →₀ ℝ) :
    ∃ D : Finset (Fin k → ℕ), (∀ d, l d ≠ 0 → d ∈ D) ∧ (∑' (p : (Fin k → ℕ) × (Fin k → ℕ)),
        restrictedSummand h m modulus l p) = S2mFull h m modulus l D := by
  have hfin : {d : Fin k → ℕ | l d ≠ 0}.Finite := l.hasFiniteSupport
  refine ⟨hfin.toFinset, fun _ ↦ hfin.mem_toFinset.mpr, ?_⟩
  rw [S2mFull, ← Finset.sum_product']
  refine tsum_eq_sum fun p hp ↦ ?_
  rw [Finset.mem_product] at hp
  push Not at hp
  have hz : l p.1 = 0 ∨ l p.2 = 0 := by
    by_contra hc
    push Not at hc
    exact hp (hfin.mem_toFinset.mpr hc.1) (hfin.mem_toFinset.mpr hc.2)
  simp only [restrictedSummand]
  split
  · rcases hz with h0 | h0 <;> rw [h0] <;> ring
  · rfl

/-- The `(u, s)` -indexed, `φ` -normalized form of `S2mFull`, with `d m = e m = 1`. -/
noncomputable def S2mRestr {k : ℕ} (m : Fin k) (l : (Fin k → ℕ) →₀ ℝ)
    (D : Finset (Fin k → ℕ)) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ D, ∑ u ∈ PrimeGaps.LemS1RestrictSij.uDomain d e,
      ∑ s ∈ PrimeGaps.LemS1RestrictSij.sDomain d e, ((∏ i, (g (u i) : ℝ)) *
            ∏ p ∈ Finset.univ.offDiag, (μ (s p.1 p.2) : ℝ)) *
          (if d m = 1 ∧ e m = 1 then
            l d * l e / ∏ i, ((d i).totient : ℝ) * ((e i).totient : ℝ) else 0)

end PrimeGaps

namespace Nat

/-- A prime dividing `lcm (d i) (e i)` divides `∏ i, d i` or `∏ i, e i`. -/
theorem prime_dvd_prod_lcm {k : ℕ} {d e : Fin k → ℕ} {i : Fin k} {p : ℕ}
    (hp : Nat.Prime p) (hpd : p ∣ Nat.lcm (d i) (e i)) :
    p ∣ ∏ i, d i ∨ p ∣ ∏ i, e i :=
  (hp.dvd_mul.mp (hpd.trans (Nat.lcm_dvd_mul _ _))).imp
    (·.trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))
    (·.trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))

/-- Distinct coordinates `d i`, `d j` are coprime when the product `∏ t, d t` is squarefree. -/
theorem coprime_of_sf_prod {k : ℕ} (d : Fin k → ℕ) (i j : Fin k) (hij : i ≠ j)
    (hsf : Squarefree (∏ t, d t)) : (d i).Coprime (d j) := by
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Nat.squarefree_mul_iff] at hsf
  exact (Nat.Coprime.coprime_dvd_left
    (Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)) hsf.1).symm

end Nat

namespace PrimeGaps

/-- `gcd (h m - h i) (lcm (d i) (e i)) = 1` for `d`, `e` of permissible support and `i ≠ m`. -/
theorem hgap_gcd_lcm_eq_one_of_support {k : ℕ} (h : Fin k → ℕ) (hinj : Function.Injective h)
    (m i : Fin k) (hi : i ≠ m) (N : ℕ) (d e : Fin k → ℕ) (θ δ : ℝ)
    (hd : d ∈ Finset.permissibleSupport k ⌊(N : ℝ) ^ (θ / 2 -
      δ)⌋₊ (primorial ⌊PrimeGaps.D₀ (N : ℝ)⌋₊))
    (he : e ∈ Finset.permissibleSupport k ⌊(N : ℝ) ^ (θ / 2 -
      δ)⌋₊ (primorial ⌊PrimeGaps.D₀ (N : ℝ)⌋₊))
    (hD0 : ∀ a b : Fin k, a ≠ b → (h a).dist (h b) < ⌊PrimeGaps.D₀ (N : ℝ)⌋₊) :
    (((h m : ℤ) - (h i : ℤ)).gcd ((Nat.lcm (d i) (e i) : ℕ) : ℤ)) = 1 := by
  rw [Int.gcd, Int.natAbs_natCast,
    show ((h m : ℤ) - (h i : ℤ)).natAbs = (h m).dist (h i) by rw [Nat.dist]; omega,
    Nat.eq_one_iff_not_exists_prime_dvd]
  intro p hp hpg
  have hp2 : p ∣ Nat.lcm (d i) (e i) := hpg.trans (Nat.gcd_dvd_right _ _)
  have hpos : 0 < (h m).dist (h i) :=
    Nat.pos_of_ne_zero fun h0 ↦ hi (hinj (Nat.eq_of_dist_eq_zero h0)).symm
  have hp_prim : p ∣ primorial ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ := hp.dvd_primorial_iff.mpr
    ((Nat.le_of_dvd hpos (hpg.trans (Nat.gcd_dvd_left _ _))).trans_lt (hD0 m i hi.symm)).le
  have hcontra : ∀ t : Fin k → ℕ, (∏ i, t i).Coprime (primorial ⌊PrimeGaps.D₀ (N : ℝ)⌋₊) →
      p ∣ ∏ i, t i → False := fun t hct hpt ↦
    hp.not_dvd_one (hct ▸ Nat.dvd_gcd hpt hp_prim)
  exact (Nat.prime_dvd_prod_lcm hp hp2).elim
    (hcontra d (Finset.mem_permissibleSupport_iff.mp hd).2.1)
    (hcontra e (Finset.mem_permissibleSupport_iff.mp he).2.1)

open scoped PrimeGaps.sieveModulus in
/-- On the permissible support the full `lcm`-coprimality guard of the restricted summand is
equivalent to the decoupled `(∀ i ≠ j, (d i).Coprime (e j)) ∧ d m = 1 ∧ e m = 1`. -/
theorem restricted_guard_iff_decouple {k : ℕ} (h : Fin k → ℕ) (hinj : Function.Injective h)
    (m : Fin k) (N : ℕ) (θ δ : ℝ) (d e : Fin k → ℕ)
    (hd : d ∈ Finset.permissibleSupport k ⌊(N : ℝ) ^ (θ / 2 -
      δ)⌋₊ (primorial ⌊PrimeGaps.D₀ (N : ℝ)⌋₊))
    (he : e ∈ Finset.permissibleSupport k ⌊(N : ℝ) ^ (θ / 2 -
      δ)⌋₊ (primorial ⌊PrimeGaps.D₀ (N : ℝ)⌋₊))
    (hD0 : ∀ a b : Fin k, a ≠ b → (h a).dist (h b) < ⌊PrimeGaps.D₀ (N : ℝ)⌋₊) :
    (d m = 1 ∧ e m = 1 ∧ (∀ i, (W N).Coprime ((d i).lcm (e i))) ∧
        (∀ i j, i ≠ j → ((d i).lcm (e i)).Coprime ((d j).lcm (e j))) ∧
        (∀ i, i ≠ m → ((h m : ℤ) - (h i : ℤ)).gcd ((Nat.lcm (d i) (e i) : ℕ) : ℤ) = 1)) ↔
      ((∀ i j, i ≠ j → (d i).Coprime (e j)) ∧ d m = 1 ∧ e m = 1) := by
  have hcd := (Finset.mem_permissibleSupport_iff.mp hd).2.1
  have hce := (Finset.mem_permissibleSupport_iff.mp he).2.1
  have hsfd := (Finset.mem_permissibleSupport_iff.mp hd).2.2
  have hsfe := (Finset.mem_permissibleSupport_iff.mp he).2.2
  constructor
  · rintro ⟨hdm, hem, _, hpc, _⟩
    exact ⟨fun i j hij ↦ ((hpc i j hij).coprime_dvd_left (Nat.dvd_lcm_left _ _)).coprime_dvd_right
      (Nat.dvd_lcm_right _ _), hdm, hem⟩
  · rintro ⟨hdec, hdm, hem⟩
    refine ⟨hdm, hem, fun i ↦ ?_, fun i j hij ↦ ?_,
      fun i hi ↦ hgap_gcd_lcm_eq_one_of_support h hinj m i hi N d e θ δ hd he hD0⟩
    · change (primorial ⌊PrimeGaps.D₀ (N : ℝ)⌋₊).Coprime ((d i).lcm (e i))
      have hdi : (d i).Coprime (primorial ⌊PrimeGaps.D₀ (N : ℝ)⌋₊) :=
        Nat.Coprime.coprime_dvd_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) hcd
      have hei : (e i).Coprime (primorial ⌊PrimeGaps.D₀ (N : ℝ)⌋₊) :=
        Nat.Coprime.coprime_dvd_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) hce
      exact (Nat.Coprime.coprime_dvd_left (Nat.lcm_dvd_mul _ _) (hdi.mul_left hei)).symm
    · exact Nat.Coprime.coprime_dvd_left (Nat.lcm_dvd_mul (d i) (e i))
        (Nat.Coprime.coprime_dvd_right (Nat.lcm_dvd_mul (d j) (e j))
          (((Nat.coprime_of_sf_prod d i j hij hsfd).mul_right (hdec i j hij)).mul_left
            ((hdec j i hij.symm).symm.mul_right (Nat.coprime_of_sf_prod e i j hij hsfe))))

/-- Coordinatewise consequences of membership in `Finset.permissibleSupport`: every `d i` is
positive and squarefree, and distinct coordinates are coprime. -/
theorem permissibleSupport_coord_facts {k : ℕ} (N : ℕ) (θ δ : ℝ) (d : Fin k → ℕ)
    (hd : d ∈ Finset.permissibleSupport k ⌊(N : ℝ) ^ (θ / 2 -
      δ)⌋₊ (primorial ⌊PrimeGaps.D₀ (N : ℝ)⌋₊)) :
    (∀ i, 0 < d i) ∧ (∀ i, Squarefree (d i)) ∧ (∀ i j, i ≠ j → (d i).Coprime (d j)) := by
  have hsf := (Finset.mem_permissibleSupport_iff.mp hd).2.2
  exact ⟨fun i ↦ Nat.one_le_iff_ne_zero.mpr
      (Finset.squarefree_of_mem_permissibleSupport hd i).ne_zero,
    fun i ↦ PrimeGaps.coord_squarefree d hsf i,
    fun i j hij ↦ Nat.coprime_of_sf_prod d i j hij hsf⟩

/-- `S2mFull` at the sieve modulus equals its `(u, s)`-indexed `φ`-normalized form `S2mRestr`. -/
theorem S2mFull_eq_S2mRestr {k : ℕ} (h : Fin k → ℕ) (hinj : Function.Injective h) (m : Fin k)
    (θ δ : ℝ)
    (N : ℕ) (l : (Fin k → ℕ) →₀ ℝ)
    (hsupp : l.HasPermissibleSupport ⌊(N : ℝ) ^ (θ / 2 - δ)⌋₊ (primorial ⌊PrimeGaps.D₀ (N : ℝ)⌋₊))
    (hD0 : ∀ i j : Fin k, i ≠ j → (h i).dist (h j) < ⌊PrimeGaps.D₀ (N : ℝ)⌋₊)
    (D : Finset (Fin k → ℕ)) :
    S2mFull h m (PrimeGaps.sieveModulus N) l D = S2mRestr m l D := by
  have hcongr : S2mFull h m (PrimeGaps.sieveModulus N) l D = ∑ d ∈ D, ∑ e ∈ D,
        (if (∀ i j : Fin k, i ≠ j → (d i).Coprime (e j)) ∧ d m = 1 ∧ e m = 1 then
          l d * l e / ∏ i, (((d i).lcm (e i)).totient : ℝ) else 0 : ℝ) := by
    rw [S2mFull]
    refine Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun e _ ↦ ?_
    by_cases hle : l d = 0 ∨ l e = 0
    · simp only [restrictedSummand]
      rcases hle with h0 | h0 <;>
        simp only [h0, zero_mul, mul_zero, zero_div, ite_self]
    · push Not at hle
      obtain ⟨hld, hle'⟩ := hle
      simp only [restrictedSummand]
      rw [if_congr (restricted_guard_iff_decouple h hinj m N θ δ d e
        (hsupp (Finsupp.mem_support_iff.mpr hld))
        (hsupp (Finsupp.mem_support_iff.mpr hle')) hD0) rfl rfl]
  have hsupp' : ∀ t, l t ≠ 0 → (∀ i, 0 < t i) ∧ (∀ i, Squarefree (t i)) ∧
      ∀ i j : Fin k, i ≠ j → (t i).Coprime (t j) :=
    fun t ht ↦ permissibleSupport_coord_facts N θ δ t (hsupp (Finsupp.mem_support_iff.mpr ht))
  rw [hcongr, lem_S2m_decouple_phi_lcm m D l hsupp', S2mRestr]
  exact lem_S2m_mobius m D l

/-- The fully-inverted `(u, s)` -indexed form: the coefficient collapsed multiplicatively (`u_i ↦
μ(u_i)²/g(u_i)`, off-diagonal `s_{i,j} ↦ μ(s_{i,j})/g(s_{i,j})²` ) and the two `λ/∏φ` factors
replaced by `PrimeGaps.ym m l (boldA u s)` and `PrimeGaps.ym m l (boldB u s)`, restricted to
`RestrictedCoprime u s` with `u ≥ 1`, diagonal `s i i = 1`, off-diagonal `s ≥ 1`. -/
noncomputable def S2mYm {k : ℕ} (m : Fin k) (l : (Fin k → ℕ) →₀ ℝ)
    (U : Finset (Fin k → ℕ)) (S : Finset (Fin k → Fin k → ℕ)) : ℝ :=
  ∑ u ∈ U, ∑ s ∈ S, (if ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
          PrimeGaps.LemS1RestrictSij.RestrictedCoprime u s) then
        (∏ i, (μ (u i) : ℝ) ^ 2 / (g (u i) : ℝ)) *
        (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
            (μ (s p.1 p.2) : ℝ) / (g (s p.1 p.2) : ℝ) ^ 2) *
        PrimeGaps.ym m l (boldA u s) * PrimeGaps.ym m l (boldB u s)
      else 0)

/-- `ym m l r = (∏ i, μ(rᵢ) g(rᵢ)) * ∑ d ∈ D, [d m = 1 ∧ ∀ i, rᵢ ∣ dᵢ squarefree] l d / ∏ i, φ(dᵢ)`,
for any `D` containing the support of `l`. -/
theorem ym_eq_sum_D {k : ℕ} (m : Fin k) (l : (Fin k → ℕ) →₀ ℝ)
    (D : Finset (Fin k → ℕ)) (hD : ∀ d, l d ≠ 0 → d ∈ D) (r : Fin k → ℕ) :
    PrimeGaps.ym m l r = (∏ i, (μ (r i) : ℝ) * (g (r i) : ℝ)) *
        ∑ d ∈ D, (if d m = 1 ∧ ∀ i, r i ∣ d i ∧ Squarefree (d i)
          then l d / (∏ i, ((d i).totient : ℝ)) else 0) := by
  rw [PrimeGaps.ym_apply']
  push_cast
  congr 1
  change (∑ d ∈ l.support, if d m = 1 ∧ ∀ i, r i ∣ d i ∧ Squarefree (d i)
      then l d / (∏ i, ((d i).totient : ℝ)) else 0) = _
  refine Finset.sum_subset (fun d hd ↦ hD d (Finsupp.mem_support_iff.mp hd)) fun d _ hd ↦ ?_
  simp [Finsupp.notMem_support_iff.mp hd]

/-- The finite expansion of both `PrimeGaps.ym` factors over `D`. -/
noncomputable def S2mReindexed {k : ℕ} (m : Fin k) (l : (Fin k → ℕ) →₀ ℝ)
    (Rb : ℝ) (D : Finset (Fin k → ℕ)) : ℝ :=
  ∑ u ∈ Ubox k Rb, ∑ s ∈ Sbox k Rb,
    (if ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
          PrimeGaps.LemS1RestrictSij.RestrictedCoprime u s) then
        (∏ i, (μ (u i) : ℝ) ^ 2 / (g (u i) : ℝ)) *
        (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
            (μ (s p.1 p.2) : ℝ) / (g (s p.1 p.2) : ℝ) ^ 2) *
        ((∏ i, (μ (boldA u s i) : ℝ) * (g (boldA u s i) : ℝ)) *
            ∑ d ∈ D, (if d m = 1 ∧ ∀ i, boldA u s i ∣ d i ∧ Squarefree (d i)
                then l d / (∏ i, ((d i).totient : ℝ)) else 0)) *
        ((∏ i, (μ (boldB u s i) : ℝ) * (g (boldB u s i) : ℝ)) *
            ∑ e ∈ D, (if e m = 1 ∧ ∀ i, boldB u s i ∣ e i ∧ Squarefree (e i)
                then l e / (∏ i, ((e i).totient : ℝ)) else 0))
      else 0)

/-- Expanding both `PrimeGaps.ym` factors over `D` turns `S2mYm m l (Ubox k Rb) (Sbox k Rb)` into
`S2mReindexed m l Rb D`. -/
theorem S2mYm_eq_reindexed {k : ℕ} (m : Fin k) (l : (Fin k → ℕ) →₀ ℝ)
    (Rb : ℝ) (D : Finset (Fin k → ℕ)) (hD : ∀ d, l d ≠ 0 → d ∈ D) :
    S2mYm m l (Ubox k Rb) (Sbox k Rb) = S2mReindexed m l Rb D := by
  rw [S2mYm, S2mReindexed]
  refine Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
  split
  · rw [PrimeGaps.ym_eq_sum_D m l D hD (boldA u s), PrimeGaps.ym_eq_sum_D m l D hD (boldB u s)]
  · rfl

/-- A `(d, e, u, s)` -indexed summand whose `(u, s)` box guard is bundled with the two `d m = 1`
/divisibility/squarefree tail guards; the coefficient is the collapsed
`(∏ g(u_i)) · (∏_{offDiag} μ(s))` and the two `λ/∏φ` tails. -/
noncomputable def S2mMerged {k : ℕ} (m : Fin k) (l : (Fin k → ℕ) →₀ ℝ)
    (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ) (d e : Fin k → ℕ) : ℝ :=
  if (((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
        PrimeGaps.LemS1RestrictSij.RestrictedCoprime u s) ∧
      (d m = 1 ∧ ∀ i, boldA u s i ∣ d i ∧ Squarefree (d i)) ∧
      (e m = 1 ∧ ∀ i, boldB u s i ∣ e i ∧ Squarefree (e i))) then
    ((∏ i, (g (u i) : ℝ)) * ∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
          (μ (s p.1 p.2) : ℝ)) * (l d / (∏ i, ((d i).totient : ℝ))) *
      (l e / (∏ i, ((e i).totient : ℝ)))
  else 0

section CollapseHelpers
open Finset ArithmeticFunction

/-- `g` vanishes at a squarefree even number. -/
theorem g_eq_zero_of_two_dvd {n : ℕ} (hsq : Squarefree n) (h2 : 2 ∣ n) : g n = 0 := by
  exact (ArithmeticFunction.detotient_eq_zero_iff hsq).2 h2

/-- `g` does not vanish at an odd number. -/
theorem g_ne_zero_of_not_two_dvd {n : ℕ} (h2 : ¬ 2 ∣ n) : g n ≠ 0 := by
  exact (ArithmeticFunction.detotient_pos_of_odd
    (Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using h2))).ne'

/-- Nonvanishing of `g` passes to divisors of a squarefree number. -/
theorem g_ne_zero_of_dvd {a b : ℕ} (ha : g a ≠ 0) (hsa : Squarefree a) (hb : b ∣ a) : g b ≠ 0 := by
  intro hbz
  exact ha <| g_eq_zero_of_two_dvd hsa <|
    (not_not.mp fun h2 ↦ g_ne_zero_of_not_two_dvd h2 hbz).trans hb

/-- `g (boldA u s i) = g (u i) * ∏ j ∈ univ.erase i, g (s i j)` under `RestrictedCoprime u s`. -/
theorem gA_fac {k : ℕ} (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ)
    (hcop : PrimeGaps.LemS1RestrictSij.RestrictedCoprime u s) (i : Fin k) :
    g (boldA u s i) = g (u i) * ∏ j ∈ Finset.univ.erase i, g (s i j) :=
  PrimeGaps.map_boldA _ ArithmeticFunction.detotient_one
    (fun _ _ hab ↦ ArithmeticFunction.isMultiplicative_detotient.map_mul_of_coprime hab)
    u s hcop i

/-- `g (boldB u s i) = g (u i) * ∏ j ∈ univ.erase i, g (s j i)`, the transpose form of `gA_fac`. -/
theorem gB_fac {k : ℕ} (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ)
    (hcop : PrimeGaps.LemS1RestrictSij.RestrictedCoprime u s) (i : Fin k) :
    g (boldB u s i) = g (u i) * ∏ j ∈ Finset.univ.erase i, g (s j i) :=
  PrimeGaps.map_boldB _ ArithmeticFunction.detotient_one
    (fun _ _ hab ↦ ArithmeticFunction.isMultiplicative_detotient.map_mul_of_coprime hab)
    u s hcop i

/-- The coefficient collapse
`(∏ μ(uᵢ)²/g(uᵢ)) (∏_offDiag μ(s)/g(s)²) (∏ μ(𝐀) g(𝐀)) (∏ μ(𝐁) g(𝐁)) = (∏ g(uᵢ)) ∏_offDiag μ(s)`. -/
theorem S2mMerged_coeff_collapse {k : ℕ} (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ) (d : Fin k → ℕ)
    (hguard : (∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
        PrimeGaps.LemS1RestrictSij.RestrictedCoprime u s)
    (hA : ∀ i, boldA u s i ∣ d i ∧ Squarefree (d i))
    (hgu : ∀ i, g (u i) ≠ 0)
    (hgs : ∀ i j, i ≠ j → g (s i j) ≠ 0) :
    (∏ i, (μ (u i) : ℝ) ^ 2 / (g (u i) : ℝ)) *
      (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
          (μ (s p.1 p.2) : ℝ) / (g (s p.1 p.2) : ℝ) ^ 2) *
      (∏ i, (μ (boldA u s i) : ℝ) * (g (boldA u s i) : ℝ)) *
      (∏ i, (μ (boldB u s i) : ℝ) * (g (boldB u s i) : ℝ)) =
      (∏ i, (g (u i) : ℝ)) * ∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
            (μ (s p.1 p.2) : ℝ) := by
  obtain ⟨hu, hsii, hs, hcop⟩ := hguard
  have hsfu : ∀ i, Squarefree (u i) := fun i ↦
    (hA i).2.squarefree_of_dvd ((dvd_mul_right (u i) _).trans (hA i).1)
  have hsfs : ∀ i j, i ≠ j → Squarefree (s i j) := fun i j hij ↦
    (hA i).2.squarefree_of_dvd <|
      (Finset.dvd_prod_of_mem _
          (Finset.mem_erase.mpr ⟨fun h ↦ hij h.symm, Finset.mem_univ j⟩)).trans <|
        (dvd_mul_left _ (u i)).trans (hA i).1
  have wA : ∀ i, (g (boldA u s i) : ℝ) = (g (u i) : ℝ) *
      ∏ a ∈ Finset.univ.erase i, (g (s i a) : ℝ) := fun i ↦ by exact_mod_cast gA_fac u s hcop i
  have wB : ∀ i, (g (boldB u s i) : ℝ) = (g (u i) : ℝ) *
      ∏ a ∈ Finset.univ.erase i, (g (s a i) : ℝ) := fun i ↦ by exact_mod_cast gB_fac u s hcop i
  exact coeff_collapse_gen u s (fun n ↦ (g n : ℝ)) hcop hsfu hsfs
    (fun i ↦ by exact_mod_cast hgu i) (fun i j hij ↦ by exact_mod_cast hgs i j hij) wA wB
end CollapseHelpers

/-- `S2mReindexed` as the quadruple sum of `S2mMerged` over `Ubox k Rb`, `Sbox k Rb` and `D × D`. -/
theorem S2mReindexed_outer {k : ℕ} (m : Fin k) (l : (Fin k → ℕ) →₀ ℝ)
    (Rb : ℝ) (D : Finset (Fin k → ℕ))
    (hgpos : ∀ t : Fin k → ℕ, l t ≠ 0 → ∀ i, g (t i) ≠ 0) :
    S2mReindexed m l Rb D =
      ∑ u ∈ Ubox k Rb, ∑ s ∈ Sbox k Rb, ∑ d ∈ D, ∑ e ∈ D, S2mMerged m l u s d e := by
  rw [S2mReindexed]
  refine Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
  set cB : ℝ := (∏ i, (μ (u i) : ℝ) ^ 2 / (g (u i) : ℝ)) *
    (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
        (μ (s p.1 p.2) : ℝ) / (g (s p.1 p.2) : ℝ) ^ 2) with hcB
  set pA : ℝ := ∏ i, (μ (boldA u s i) : ℝ) * (g (boldA u s i) : ℝ) with hpA
  set pB : ℝ := ∏ i, (μ (boldB u s i) : ℝ) * (g (boldB u s i) : ℝ) with hpB
  have key : ∀ X Y : ℝ, cB * (pA * X) * (pB * Y) = cB * pA * pB * X * Y := fun X Y ↦ by ring
  simp only [key]
  rw [ite_mul_sum_mul_sum D _ (cB * pA * pB) _ _ _ _]
  refine Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun e _ ↦ ?_
  rw [S2mMerged]
  by_cases hall : ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
        PrimeGaps.LemS1RestrictSij.RestrictedCoprime u s) ∧
      (d m = 1 ∧ ∀ i, boldA u s i ∣ d i ∧ Squarefree (d i)) ∧
      (e m = 1 ∧ ∀ i, boldB u s i ∣ e i ∧ Squarefree (e i))
  · rw [if_pos hall, if_pos hall]
    obtain ⟨hguard, ⟨-, hAd⟩, -⟩ := hall
    by_cases hld : l d = 0
    · rw [hld]; ring
    have hgd : ∀ i, g (d i) ≠ 0 := hgpos d hld
    have hgu : ∀ i, g (u i) ≠ 0 := fun i ↦
      g_ne_zero_of_dvd (hgd i) (hAd i).2 ((dvd_mul_right (u i) _).trans (hAd i).1)
    have hgs : ∀ i j, i ≠ j → g (s i j) ≠ 0 := fun i j hij ↦
      g_ne_zero_of_dvd (hgd i) (hAd i).2 <|
        (Finset.dvd_prod_of_mem _
            (Finset.mem_erase.mpr ⟨fun h ↦ hij h.symm, Finset.mem_univ j⟩)).trans <|
          (dvd_mul_left _ (u i)).trans (hAd i).1
    have hcoeff := S2mMerged_coeff_collapse u s d hguard hAd hgu hgs
    rw [← hcB, ← hpA, ← hpB] at hcoeff
    rw [hcoeff]
  · rw [if_neg hall, if_neg hall]

/-- `u ∈ uDomain d e` iff `u i ∣ (d i).gcd (e i) ≠ 0` for every `i`. -/
theorem mem_uDomain_iff {k : ℕ} {d e u : Fin k → ℕ} : u ∈ PrimeGaps.LemS1RestrictSij.uDomain d e ↔
      ∀ i, u i ∣ (d i).gcd (e i) ∧ (d i).gcd (e i) ≠ 0 := by
  rw [PrimeGaps.LemS1RestrictSij.uDomain, Fintype.mem_piFinset]
  exact forall_congr' fun _ ↦ Nat.mem_divisors

/-- Membership in `sDomain d e` is entrywise membership in `sEntryDomain d e i j`. -/
theorem mem_sDomain_iff {k : ℕ} {d e : Fin k → ℕ} {s : Fin k → Fin k → ℕ} :
    s ∈ PrimeGaps.LemS1RestrictSij.sDomain d e ↔
      ∀ i j, s i j ∈ PrimeGaps.LemS1RestrictSij.sEntryDomain d e i j := by
  rw [PrimeGaps.LemS1RestrictSij.sDomain, Fintype.mem_piFinset]
  exact forall_congr' fun _ ↦ Fintype.mem_piFinset

/-- `RestrictedCoprime u s` holds for `u ∈ uDomain d e`, `s ∈ sDomain d e` when the coordinates of
`d` and of `e` are pairwise coprime. -/
theorem restrictedCoprime_of_domain {k : ℕ} {d e u : Fin k → ℕ} {s : Fin k → Fin k → ℕ}
    (hu : u ∈ PrimeGaps.LemS1RestrictSij.uDomain d e)
    (hs : s ∈ PrimeGaps.LemS1RestrictSij.sDomain d e)
    (hdcop : ∀ i j, i ≠ j → (d i).Coprime (d j))
    (hecop : ∀ i j, i ≠ j → (e i).Coprime (e j)) :
    PrimeGaps.LemS1RestrictSij.RestrictedCoprime u s := by
  rw [mem_uDomain_iff] at hu
  rw [mem_sDomain_iff] at hs
  have hudvd : ∀ i, u i ∣ d i ∧ u i ∣ e i := fun i ↦
    ⟨(hu i).1.trans (Nat.gcd_dvd_left _ _), (hu i).1.trans (Nat.gcd_dvd_right _ _)⟩
  have hsdvd : ∀ i j, i ≠ j → s i j ∣ d i ∧ s i j ∣ e j := fun i j hij ↦ by
    have hsij := hs i j
    rw [PrimeGaps.LemS1RestrictSij.sEntryDomain, if_neg hij] at hsij
    have := (Nat.mem_divisors.mp hsij).1
    exact ⟨this.trans (Nat.gcd_dvd_left _ _), this.trans (Nat.gcd_dvd_right _ _)⟩
  exact PrimeGaps.LemS1RestrictSij.restrictedCoprime_of_dvd hudvd hsdvd hdcop hecop

/-- The inner `(u, s)` sum of `S2mRestr` over `uDomain d e × sDomain d e` equals `∑ S2mMerged` over
the boxes at `Rb = N ^ (θ / 2 - δ)`, for `d`, `e` of permissible support. -/
theorem S2mRestr_inner {k : ℕ} (m : Fin k) (θ δ : ℝ) (N : ℕ) (l : (Fin k → ℕ) →₀ ℝ)
    (d e : Fin k → ℕ)
    (hd : d ∈ Finset.permissibleSupport k ⌊(N : ℝ) ^ (θ / 2 -
      δ)⌋₊ (primorial ⌊PrimeGaps.D₀ (N : ℝ)⌋₊))
    (he : e ∈ Finset.permissibleSupport k ⌊(N : ℝ) ^ (θ / 2 -
      δ)⌋₊ (primorial ⌊PrimeGaps.D₀ (N : ℝ)⌋₊)) :
    (∑ u ∈ PrimeGaps.LemS1RestrictSij.uDomain d e,
      ∑ s ∈ PrimeGaps.LemS1RestrictSij.sDomain d e, ((∏ i, (g (u i) : ℝ)) *
            ∏ p ∈ Finset.univ.offDiag, (μ (s p.1 p.2) : ℝ)) *
          (if d m = 1 ∧ e m = 1 then
            l d * l e / ∏ i, ((d i).totient : ℝ) * ((e i).totient : ℝ) else 0)) =
      ∑ u ∈ Ubox k ((N : ℝ) ^ (θ / 2 - δ)),
          ∑ s ∈ Sbox k ((N : ℝ) ^ (θ / 2 - δ)), S2mMerged m l u s d e := by
  set Rb : ℝ := (N : ℝ) ^ (θ / 2 - δ)
  obtain ⟨hdpos, hdsf, hdcop⟩ := permissibleSupport_coord_facts N θ δ d hd
  obtain ⟨_, hesf, hecop⟩ := permissibleSupport_coord_facts N θ δ e he
  have hd1 : ∀ i, 1 ≤ d i := hdpos
  have hdbnd := (Finset.mem_permissibleSupport_iff.mp hd).1
  have hdle : ((∏ i, d i : ℕ) : ℝ) ≤ Rb :=
    le_trans (by exact_mod_cast hdbnd) (Nat.floor_le (Real.rpow_nonneg (by positivity) _))
  have hUsub : PrimeGaps.LemS1RestrictSij.uDomain d e ⊆ Ubox k Rb := uDomain_sub Rb d e hd1 hdle
  have hSsub : PrimeGaps.LemS1RestrictSij.sDomain d e ⊆ Sbox k Rb := sDomain_sub Rb d e hd1 hdle
  have hinner : ∀ u : Fin k → ℕ, (∑ s ∈ PrimeGaps.LemS1RestrictSij.sDomain d e,
        ((∏ i, (g (u i) : ℝ)) *
            ∏ p ∈ Finset.univ.offDiag, (μ (s p.1 p.2) : ℝ)) *
          (if d m = 1 ∧ e m = 1 then
            l d * l e / ∏ i, ((d i).totient : ℝ) * ((e i).totient : ℝ) else 0)) = ∑ s ∈ Sbox k Rb,
          if s ∈ PrimeGaps.LemS1RestrictSij.sDomain d e then
            ((∏ i, (g (u i) : ℝ)) *
              ∏ p ∈ Finset.univ.offDiag, (μ (s p.1 p.2) : ℝ)) *
            (if d m = 1 ∧ e m = 1 then
              l d * l e / ∏ i, ((d i).totient : ℝ) * ((e i).totient : ℝ) else 0)
          else 0 := fun _ ↦ Finset.sum_eq_sum_ite_mem _ _ hSsub _
  rw [Finset.sum_congr rfl fun u _ ↦ hinner u, Finset.sum_eq_sum_ite_mem _ _ hUsub]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  by_cases huD : u ∈ PrimeGaps.LemS1RestrictSij.uDomain d e
  · rw [if_pos huD]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    by_cases hsD : s ∈ PrimeGaps.LemS1RestrictSij.sDomain d e
    · rw [if_pos hsD]
      obtain ⟨hguard, hAdvd, hBdvd⟩ := (mem_domain_iff_bold_dvd d e hd1 u s).mp
        ⟨huD, hsD, restrictedCoprime_of_domain huD hsD hdcop hecop⟩
      have hAd : ∀ i, boldA u s i ∣ d i ∧ Squarefree (d i) := fun i ↦ ⟨hAdvd i, hdsf i⟩
      have hBe : ∀ i, boldB u s i ∣ e i ∧ Squarefree (e i) := fun i ↦ ⟨hBdvd i, hesf i⟩
      rw [S2mMerged]
      by_cases hdem : d m = 1 ∧ e m = 1
      · rw [if_pos hdem, if_pos ⟨hguard, ⟨hdem.1, hAd⟩, hdem.2, hBe⟩, Finset.prod_mul_distrib]
        ring
      · rw [if_neg hdem]
        symm
        rw [if_neg (by rintro ⟨-, ⟨hdm, -⟩, hem, -⟩; exact hdem ⟨hdm, hem⟩)]
        ring
    · rw [if_neg hsD]
      symm
      rw [S2mMerged, if_neg]
      rintro ⟨hguard, ⟨-, hAd⟩, -, hBe⟩
      exact hsD ((mem_domain_iff_bold_dvd d e hd1 u s).mpr
        ⟨hguard, fun i ↦ (hAd i).1, fun i ↦ (hBe i).1⟩).2.1
  · rw [if_neg huD]
    symm
    refine Finset.sum_eq_zero fun s _ ↦ ?_
    rw [S2mMerged, if_neg]
    rintro ⟨hguard, ⟨-, hAd⟩, -, hBe⟩
    exact huD ((mem_domain_iff_bold_dvd d e hd1 u s).mpr
      ⟨hguard, fun i ↦ (hAd i).1, fun i ↦ (hBe i).1⟩).1

/-- `g (t i) ≠ 0` in every coordinate of a permissible `t`, once `2 ≤ ⌊D₀ N⌋₊` forces `∏ i, t i`
odd. -/
theorem gpos_of_permissibleSupport {k : ℕ} (N : ℕ) (θ δ : ℝ) (t : Fin k → ℕ)
    (ht : t ∈ Finset.permissibleSupport k ⌊(N : ℝ) ^ (θ / 2 -
      δ)⌋₊ (primorial ⌊PrimeGaps.D₀ (N : ℝ)⌋₊))
    (hN2 : 2 ≤ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊) :
    ∀ i, g (t i) ≠ 0 := by
  have hcop := (Finset.mem_permissibleSupport_iff.mp ht).2.1
  intro i
  refine g_ne_zero_of_not_two_dvd fun h2 ↦ Nat.prime_two.not_dvd_one (hcop ▸ Nat.dvd_gcd
    (h2.trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))
    (Nat.prime_two.dvd_primorial_iff.mpr hN2))

/-- `S2mRestr m l D = S2mReindexed m l (N ^ (θ / 2 - δ)) D` for `l` of permissible support. -/
theorem S2mRestr_eq_reindexed {k : ℕ} (m : Fin k) (θ δ : ℝ) (N : ℕ) (l : (Fin k → ℕ) →₀ ℝ)
    (hsupp : l.HasPermissibleSupport ⌊(N : ℝ) ^ (θ / 2 - δ)⌋₊ (primorial ⌊PrimeGaps.D₀ (N : ℝ)⌋₊))
    (hN2 : 2 ≤ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊)
    (D : Finset (Fin k → ℕ)) :
    S2mRestr m l D = S2mReindexed m l ((N : ℝ) ^ (θ / 2 - δ)) D := by
  have hgpos : ∀ t : Fin k → ℕ, l t ≠ 0 → ∀ i, g (t i) ≠ 0 :=
    fun t ht ↦ gpos_of_permissibleSupport N θ δ t (hsupp (Finsupp.mem_support_iff.mpr ht)) hN2
  rw [S2mReindexed_outer m l ((N : ℝ) ^ (θ / 2 - δ)) D hgpos, S2mRestr]
  have hreorder : (∑ u ∈ Ubox k ((N : ℝ) ^ (θ / 2 - δ)),
        ∑ s ∈ Sbox k ((N : ℝ) ^ (θ / 2 - δ)), ∑ d ∈ D, ∑ e ∈ D, S2mMerged m l u s d e) =
      ∑ d ∈ D, ∑ e ∈ D, ∑ u ∈ Ubox k ((N : ℝ) ^ (θ / 2 - δ)),
          ∑ s ∈ Sbox k ((N : ℝ) ^ (θ / 2 - δ)), S2mMerged m l u s d e := by
    rw [Finset.sum_comm_cycle]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [Finset.sum_comm_cycle]
  rw [hreorder]
  refine Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun e _ ↦ ?_
  by_cases hle : l d = 0 ∨ l e = 0
  · have hRHS : (∑ u ∈ Ubox k ((N : ℝ) ^ (θ / 2 - δ)),
        ∑ s ∈ Sbox k ((N : ℝ) ^ (θ / 2 - δ)), S2mMerged m l u s d e) = 0 := by
      refine Finset.sum_eq_zero fun u _ ↦ Finset.sum_eq_zero fun s _ ↦ ?_
      rw [S2mMerged]
      split
      · rcases hle with h0 | h0 <;> rw [h0] <;> ring
      · rfl
    have hLHS : (∑ u ∈ PrimeGaps.LemS1RestrictSij.uDomain d e,
        ∑ s ∈ PrimeGaps.LemS1RestrictSij.sDomain d e, ((∏ i, (g (u i) : ℝ)) *
              ∏ p ∈ Finset.univ.offDiag, (μ (s p.1 p.2) : ℝ)) *
            (if d m = 1 ∧ e m = 1 then
              l d * l e / ∏ i, ((d i).totient : ℝ) * ((e i).totient : ℝ) else 0)) = 0 := by
      refine Finset.sum_eq_zero fun u _ ↦ Finset.sum_eq_zero fun s _ ↦ ?_
      rcases hle with h0 | h0 <;> rw [h0] <;>
        simp only [zero_mul, mul_zero, zero_div, ite_self, mul_zero]
    rw [hLHS, hRHS]
  · push Not at hle
    obtain ⟨hld, hle'⟩ := hle
    exact S2mRestr_inner m θ δ N l d e (hsupp (Finsupp.mem_support_iff.mpr hld))
      (hsupp (Finsupp.mem_support_iff.mpr hle'))

/-- `ym m l r ≠ 0` forces `r i ≤ ⌊N ^ (θ / 2 - δ)⌋₊` in every coordinate, for `l` of permissible
support at that level. -/
theorem ym_arg_le_of_ne_zero {k : ℕ} (m : Fin k) (l : (Fin k → ℕ) →₀ ℝ) (θ δ : ℝ) (N : ℕ)
    (hsupp : l.HasPermissibleSupport ⌊(N : ℝ) ^ (θ / 2 - δ)⌋₊ (primorial ⌊PrimeGaps.D₀ (N : ℝ)⌋₊))
    (D : Finset (Fin k → ℕ)) (hD : ∀ d, l d ≠ 0 → d ∈ D)
    (r : Fin k → ℕ) (hr : PrimeGaps.ym m l r ≠ 0) (i : Fin k) :
    r i ≤ ⌊(N : ℝ) ^ (θ / 2 - δ)⌋₊ := by
  rw [PrimeGaps.ym_eq_sum_D m l D hD r] at hr
  have hsum : (∑ d ∈ D, (if d m = 1 ∧ ∀ i, r i ∣ d i ∧ Squarefree (d i)
          then l d / (∏ i, ((d i).totient : ℝ)) else 0)) ≠ 0 :=
    fun h0 ↦ hr (by rw [h0]; ring)
  obtain ⟨d, -, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  by_cases hg : d m = 1 ∧ ∀ i, r i ∣ d i ∧ Squarefree (d i)
  · have hldiv : l d / (∏ i, ((d i).totient : ℝ)) ≠ 0 := by simpa [hg] using hterm
    have hld : l d ≠ 0 := fun h0 ↦ hldiv (by rw [h0]; ring)
    have hss := hsupp (Finsupp.mem_support_iff.mpr hld)
    have hpos : ∀ j, 1 ≤ d j := fun j ↦ Nat.one_le_iff_ne_zero.mpr
      (Finset.squarefree_of_mem_permissibleSupport hss j).ne_zero
    exact (Nat.le_of_dvd (hpos i) (hg.2 i).1).trans
      ((Finset.single_le_prod' (fun j _ ↦ hpos j) (Finset.mem_univ i)).trans
        (Finset.mem_permissibleSupport_iff.mp hss).1)
  · simp [hg] at hterm

/-- The boxes at `Rb = N ^ (θ / 2 - δ)` capture every guarded `(u, s)` with both `ym` factors
nonzero. -/
theorem S2mReindexed_support {k : ℕ} (m : Fin k) (l : (Fin k → ℕ) →₀ ℝ) (θ δ : ℝ) (N : ℕ)
    (hsupp : l.HasPermissibleSupport ⌊(N : ℝ) ^ (θ / 2 - δ)⌋₊ (primorial ⌊PrimeGaps.D₀ (N : ℝ)⌋₊))
    (D : Finset (Fin k → ℕ)) (hD : ∀ d, l d ≠ 0 → d ∈ D) :
    ∀ u s, ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
        PrimeGaps.LemS1RestrictSij.RestrictedCoprime u s) →
        PrimeGaps.ym m l (boldA u s) ≠ 0 → PrimeGaps.ym m l (boldB u s) ≠ 0 →
        u ∈ Ubox k ((N : ℝ) ^ (θ / 2 - δ)) ∧ s ∈ Sbox k ((N : ℝ) ^ (θ / 2 - δ)) := by
  rintro u s ⟨hu1, hsii, hsij, -⟩ hA -
  exact mem_Ubox_Sbox_of_boldA_le _ u s hu1 hsii hsij
    (PrimeGaps.ym_arg_le_of_ne_zero m l θ δ N hsupp D hD (boldA u s) hA)

/-- `S2mRestr m l D = S2mYm m l U S` for finite `U`, `S` capturing every guarded `(u, s)` with both
`ym` factors nonzero. -/
theorem S2mRestr_eq_S2mYm {k : ℕ} (m : Fin k) (θ δ : ℝ) (N : ℕ) (l : (Fin k → ℕ) →₀ ℝ)
    (hsupp : l.HasPermissibleSupport ⌊(N : ℝ) ^ (θ / 2 - δ)⌋₊ (primorial ⌊PrimeGaps.D₀ (N : ℝ)⌋₊))
    (hN2 : 2 ≤ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊)
    (D : Finset (Fin k → ℕ)) (hD : ∀ d, l d ≠ 0 → d ∈ D) :
    ∃ (U : Finset (Fin k → ℕ)) (S : Finset (Fin k → Fin k → ℕ)), S2mRestr m l D = S2mYm m l U S ∧
      (∀ u s, ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
          PrimeGaps.LemS1RestrictSij.RestrictedCoprime u s) →
          PrimeGaps.ym m l (boldA u s) ≠ 0 → PrimeGaps.ym m l (boldB u s) ≠ 0 → u ∈ U ∧ s ∈ S) := by
  refine ⟨Ubox k ((N : ℝ) ^ (θ / 2 - δ)), Sbox k ((N : ℝ) ^ (θ / 2 - δ)), ?_, ?_⟩
  · rw [S2mRestr_eq_reindexed m θ δ N l hsupp hN2 D,
        ← S2mYm_eq_reindexed m l ((N : ℝ) ^ (θ / 2 - δ)) D hD]
  · exact S2mReindexed_support m l θ δ N hsupp D hD

/-- `ymWeightedSum m l = S2mYm m l U S` when `U`, `S` contain every `(u, s)` with a nonzero
summand. -/
theorem S2mYm_eq_ymWeightedSum {k : ℕ} (m : Fin k) (l : (Fin k → ℕ) →₀ ℝ)
    (U : Finset (Fin k → ℕ)) (S : Finset (Fin k → Fin k → ℕ))
    (hU : ∀ u s, ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
          PrimeGaps.LemS1RestrictSij.RestrictedCoprime u s) →
          PrimeGaps.ym m l (boldA u s) ≠ 0 → PrimeGaps.ym m l (boldB u s) ≠ 0 → u ∈ U ∧ s ∈ S) :
    ymWeightedSum m l = S2mYm m l U S := by
  set F : (Fin k → ℕ) → (Fin k → Fin k → ℕ) → ℝ := fun u s ↦
    (if ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
          PrimeGaps.LemS1RestrictSij.RestrictedCoprime u s) then
        (∏ i, (μ (u i) : ℝ) ^ 2 / (g (u i) : ℝ)) *
        (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
            (μ (s p.1 p.2) : ℝ) / (g (s p.1 p.2) : ℝ) ^ 2) *
        PrimeGaps.ym m l (boldA u s) * PrimeGaps.ym m l (boldB u s)
      else 0) with hF
  have hmem : ∀ u s, F u s ≠ 0 → u ∈ U ∧ s ∈ S := by
    intro u s hne
    simp only [hF] at hne
    split at hne
    · rename_i hguard
      exact hU u s hguard (fun h0 ↦ hne (by rw [h0]; ring)) fun h0 ↦ hne (by rw [h0]; ring)
    · exact absurd rfl hne
  change (∑' u : Fin k → ℕ, ∑' s : Fin k → Fin k → ℕ, F u s) = ∑ u ∈ U, ∑ s ∈ S, F u s
  exact tsum_tsum_eq_sum_sum F U S hmem

/-- The `tsum` of `restrictedSummand` over pairs `(d, e)` equals `ymWeightedSum m l`. -/
theorem restrictedSummand_tsum_eq_ymWeightedSum {k : ℕ} (h : Fin k → ℕ)
    (m : Fin k) (hinj : Function.Injective h) (θ δ : ℝ) (N : ℕ) (l : (Fin k → ℕ) →₀ ℝ)
    (hsupp : l.HasPermissibleSupport ⌊(N : ℝ) ^ (θ / 2 - δ)⌋₊ (primorial ⌊PrimeGaps.D₀ (N : ℝ)⌋₊))
    (hD0 : ∀ i j : Fin k, i ≠ j → (h i).dist (h j) < ⌊PrimeGaps.D₀ (N : ℝ)⌋₊)
    (hN2 : 2 ≤ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊) :
    (∑' (p : (Fin k → ℕ) × (Fin k → ℕ)),
      restrictedSummand h m (PrimeGaps.sieveModulus N) l p) = ymWeightedSum m l := by
  obtain ⟨D, hD, hstep1⟩ := restrictedSummand_tsum_eq_S2mFull h m (PrimeGaps.sieveModulus N) l
  rw [hstep1, S2mFull_eq_S2mRestr h hinj m θ δ N l hsupp hD0 D]
  obtain ⟨U, S, hstep3, hU⟩ := S2mRestr_eq_S2mYm m θ δ N l hsupp hN2 D hD
  rw [hstep3]
  exact (S2mYm_eq_ymWeightedSum m l U S hU).symm

/-- For all large `N`, `⌊D₀ N⌋₊` exceeds every gap `(h i).dist (h j)`, `i ≠ j`. -/
theorem exists_N0_for_D0_exceeds_h_gaps {k : ℕ} (h : Fin k → ℕ) :
    ∃ N₁ : ℝ, 0 < N₁ ∧ ∀ N : ℕ, N₁ ≤ (N : ℝ) →
      ∀ i j : Fin k, i ≠ j → (h i).dist (h j) < ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ := by
  set Hmax : ℕ := Finset.univ.sup fun p : Fin k × Fin k ↦ (h p.1).dist (h p.2)
  have hev : ∀ᶠ x : ℝ in Filter.atTop, (Hmax : ℝ) + 1 < PrimeGaps.D₀ x :=
    PrimeGaps.D0_tendsto_atTop.eventually_gt_atTop ((Hmax : ℝ) + 1)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨a, ha⟩ := hev
  refine ⟨max a 1, lt_max_of_lt_right one_pos, fun N hN i j _ ↦ ?_⟩
  have hDgt : (Hmax : ℝ) + 1 < PrimeGaps.D₀ (N : ℝ) :=
    ha (N : ℝ) (le_trans (le_max_left _ _) hN)
  have hgap_le : (h i).dist (h j) ≤ Hmax :=
    Finset.le_sup (f := fun p : Fin k × Fin k ↦ (h p.1).dist (h p.2)) (Finset.mem_univ (i, j))
  have hfloor : Hmax + 1 ≤ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ := Nat.le_floor (by push_cast; linarith)
  omega

/-- `2 ≤ ⌊D₀ N⌋₊` for all large `N`. -/
theorem exists_N0_for_D0_ge_2 :
    ∃ N₂ : ℝ, 0 < N₂ ∧ ∀ N : ℕ, N₂ ≤ (N : ℝ) → 2 ≤ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ := by
  have hev : ∀ᶠ x : ℝ in Filter.atTop, (2 : ℝ) < PrimeGaps.D₀ x :=
    PrimeGaps.D0_tendsto_atTop.eventually_gt_atTop (2 : ℝ)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨a, ha⟩ := hev
  refine ⟨max a 1, lt_max_of_lt_right one_pos, fun N hN ↦ Nat.le_floor ?_⟩
  have hDgt : (2 : ℝ) < PrimeGaps.D₀ (N : ℝ) := ha (N : ℝ) (le_trans (le_max_left _ _) hN)
  push_cast
  linarith

open scoped PrimeGaps.sieveModulus in
/-- Under the Bombieri--Vinogradov level-of-distribution hypothesis, the `S_2^{(m)}` sieve sum
agrees, up to a `N / (log N)^A` error, with the main term
`(X_N / \phi(W)) * ymWeightedSum m l`, where `X_N = Nat.primeCountingIoc N (2N)` and `W =
  W N`. -/
@[pg_tag "bg246" "lem_S2m_substitute_ym"]
theorem lem_S2m_substitute_ym {k : ℕ} (hk : 2 ≤ k) (h : Fin k → ℕ) (m : Fin k)
    (hinj : Function.Injective h) (θ δ : ℝ) (hδ : 0 < δ) (hδθ : δ < θ / 2) (hθ : θ < 1 / 2)
    (hBV : Nat.HasLevelOfDistribution Set.univ θ 1) :
    ∀ A : ℝ, 0 < A → ∃ C N₀ : ℝ, 0 < C ∧ 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ w₀ : ZMod (W N), (∀ i, ((w₀.val : ℤ) + h i).gcd (W N) = 1) →
      ∀ l : (Fin k → ℕ) →₀ ℝ, l.HasPermissibleSupport ⌊(N : ℝ) ^ (θ / 2 -
        δ)⌋₊ (primorial ⌊PrimeGaps.D₀ (N : ℝ)⌋₊) →
        |PrimeGaps.S₂m h (⇑l) N w₀ m -
            (↑(Nat.primeCountingIoc N (2 * N)) / (Nat.totient (W N) : ℝ)) * ymWeightedSum m l| ≤
          C * (Finsupp.maxRealAbs (PrimeGaps.lToY l)) ^ 2 * (N : ℝ) / (Real.log N) ^ A := by
  intro A hA
  obtain ⟨C, N₀, hC, hN₀, hbound⟩ := S₂m_CRT_main_term_BV_error hk h m hinj θ δ hδ hδθ hθ hBV A hA
  obtain ⟨N₁, hN₁, hN₁gap⟩ := exists_N0_for_D0_exceeds_h_gaps (h := h)
  obtain ⟨N₂, hN₂, hN₂ge⟩ := exists_N0_for_D0_ge_2
  refine ⟨C, max (max N₀ N₁) N₂, hC, lt_max_of_lt_left (lt_max_of_lt_left hN₀), ?_⟩
  intro N hN w₀ hw₀ l hsupp
  have hNle : N₀ ≤ (N : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hD0 : ∀ i j : Fin k, i ≠ j → (h i).dist (h j) < ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ :=
    hN₁gap N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
  have hN2 : 2 ≤ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ := hN₂ge N (le_trans (le_max_right _ _) hN)
  have hid : (∑' (p : (Fin k → ℕ) × (Fin k → ℕ)),
      restrictedSummand h m (PrimeGaps.sieveModulus N) l p) =
      ymWeightedSum m l :=
    restrictedSummand_tsum_eq_ymWeightedSum h m hinj θ δ N l hsupp hD0 hN2
  have := hbound N hNle w₀ hw₀ l hsupp
  rwa [hid] at this

end PrimeGaps
