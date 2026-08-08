/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.S2m.SijD0.MertensFactorG

/-!
# The pair master bound

The coordinate lemmas for `ym` and the pointwise pair-master majorant.

## Main results

* `PrimeGaps.pairMasterG_pointwise`: the pointwise majorant for the `(i,j)`-guarded summand.
* `PrimeGaps.pairMasterG_final`: the resulting bound for the guarded double tsum.
-/

@[expose] public section

open scoped Finset
open scoped ArithmeticFunction.Moebius

open scoped ArithmeticFunction.detotient

namespace PrimeGaps

open ArithmeticFunction GPYSieveS1 SijD0 PrimeGaps.LemS1RestrictSij

variable {k : ℕ}

/-- A nonzero `PrimeGaps.ym m lam r` is witnessed by a `d` in the support of `lam` that lies in the
box `[1, ⌊Rr⌋₊]^k`, is pinned at `d m = 1`, and has squarefree coordinates each divisible by the
matching coordinate of `r`. -/
lemma ym_ne_zero_witness (m : Fin k) (lam : (Fin k → ℕ) →₀ ℝ) (Rr : ℝ) (W : ℕ)
    (hlam : lam.HasPermissibleSupport ⌊Rr⌋₊ W) (r : Fin k → ℕ) (hr : PrimeGaps.ym m lam r ≠ 0) :
    ∃ d : Fin k → ℕ, lam d ≠ 0 ∧ (∀ i, d i ∈ Finset.Icc 1 ⌊Rr⌋₊) ∧ d m = 1 ∧
      ∀ i, r i ∣ d i ∧ Squarefree (d i) := by
  have hD : ∀ d : Fin k → ℕ, lam d ≠ 0 →
      d ∈ Fintype.piFinset (fun _ : Fin k ↦ Finset.Icc 1 ⌊Rr⌋₊) := by
    intro d hd
    have h1 : ∀ j, 1 ≤ d j := fun j ↦ Nat.one_le_iff_ne_zero.mpr (hlam.ne_zero_of_ne_zero hd j)
    exact Fintype.mem_piFinset.mpr fun i ↦ Finset.mem_Icc.mpr ⟨h1 i,
      (Finset.single_le_prod' (fun j _ ↦ h1 j) (Finset.mem_univ i)).trans
        (hlam.prod_lt_R_of_ne_zero hd)⟩
  rw [PrimeGaps.ym_eq_sum_D m lam _ hD r, mul_ne_zero_iff] at hr
  obtain ⟨d, hdD, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hr.2
  by_cases hc : d m = 1 ∧ ∀ (i : Fin k), r i ∣ d i ∧ Squarefree (d i)
  · exact ⟨d, fun h0 ↦ hterm (by rw [if_pos hc, h0, zero_div]),
      Fintype.mem_piFinset.mp hdD, hc.1, hc.2⟩
  · exact (hterm (if_neg hc)).elim

/-- `PrimeGaps.ym m lam r ≠ 0` pins the distinguished coordinate: `r m = 1`. -/
lemma ym_pin_eq_one (m : Fin k) (lam : (Fin k → ℕ) →₀ ℝ) (Rr : ℝ) (W : ℕ)
    (hlam : lam.HasPermissibleSupport ⌊Rr⌋₊ W) (r : Fin k → ℕ) (hr : PrimeGaps.ym m lam r ≠ 0) :
    r m = 1 := by
  obtain ⟨d, -, -, hdm, hdvd⟩ := PrimeGaps.ym_ne_zero_witness m lam Rr W hlam r hr
  exact Nat.eq_one_of_dvd_one (hdm ▸ (hdvd m).1)

/-- `PrimeGaps.ym m lam (boldA u s) ≠ 0` forces `u m = 1`, since `u m ∣ boldA u s m`. -/
lemma boldA_pin_um (m : Fin k) (lam : (Fin k → ℕ) →₀ ℝ) (Rr : ℝ) (W : ℕ)
    (hlam : lam.HasPermissibleSupport ⌊Rr⌋₊ W) (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ)
    (hnz : PrimeGaps.ym m lam (boldA u s) ≠ 0) : u m = 1 :=
  Nat.eq_one_of_dvd_one ⟨_, (PrimeGaps.ym_pin_eq_one m lam Rr W hlam (boldA u s) hnz).symm⟩

/-- `PrimeGaps.ym m lam r ≠ 0` forces each coordinate `r i` to be coprime to `W`. -/
lemma ym_coord_coprimeW (W : ℕ) (m : Fin k) (lam : (Fin k → ℕ) →₀ ℝ)
    (Rr : ℝ) (hlam : lam.HasPermissibleSupport ⌊Rr⌋₊ W) (r : Fin k → ℕ)
    (hr : PrimeGaps.ym m lam r ≠ 0) (i : Fin k) :
    Nat.Coprime (r i) W := by
  obtain ⟨d, hd, -, -, hdvd⟩ := PrimeGaps.ym_ne_zero_witness m lam Rr W hlam r hr
  exact ((hlam.coprime_prod_W_of_ne_zero hd).coprime_dvd_left
    (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))).coprime_dvd_left (hdvd i).1

/-- `PrimeGaps.ym m lam r ≠ 0` forces each coordinate `r i ≤ ⌊Rr⌋₊`. -/
lemma ym_coord_le_floor (m : Fin k) (lam : (Fin k → ℕ) →₀ ℝ) (Rr : ℝ) (W : ℕ)
    (hlam : lam.HasPermissibleSupport ⌊Rr⌋₊ W) (r : Fin k → ℕ)
    (hr : PrimeGaps.ym m lam r ≠ 0) (i : Fin k) :
    r i ≤ ⌊Rr⌋₊ := by
  obtain ⟨d, -, hdbox, -, hdvd⟩ := PrimeGaps.ym_ne_zero_witness m lam Rr W hlam r hr
  obtain ⟨hdi1, hdi2⟩ := Finset.mem_Icc.mp (hdbox i)
  exact (Nat.le_of_dvd hdi1 (hdvd i).1).trans hdi2

/-- `PrimeGaps.ym m lam r ≠ 0` forces each coordinate `r i` to be squarefree. -/
lemma ym_coord_squarefree (m : Fin k) (lam : (Fin k → ℕ) →₀ ℝ) (Rr : ℝ) (W : ℕ)
    (hlam : lam.HasPermissibleSupport ⌊Rr⌋₊ W) (r : Fin k → ℕ)
    (hr : PrimeGaps.ym m lam r ≠ 0) (i : Fin k) :
    Squarefree (r i) := by
  obtain ⟨d, -, -, -, hdvd⟩ := PrimeGaps.ym_ne_zero_witness m lam Rr W hlam r hr
  exact (hdvd i).2.squarefree_of_dvd (hdvd i).1

/-- `s i j ∣ boldB u s j` for `i ≠ j`, the factor `s i j` occurring in that product. -/
lemma sij_dvd_boldB (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ) (i j : Fin k) (hij : i ≠ j) :
    s i j ∣ boldB u s j :=
  (Finset.dvd_prod_of_mem (fun a ↦ s a j) (by simp [Finset.mem_erase, hij])).mul_left (u j)

/-- `u a ∣ boldA u s a`. -/
lemma ua_dvd_boldA (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ) (a : Fin k) :
    u a ∣ boldA u s a := dvd_rfl.mul_right _

/-- If every prime `≤ D` divides `W`, then `PrimeGaps.ym m lam (boldB u s) ≠ 0` forces every prime
factor of `s i j` to exceed `D`. -/
lemma pairMasterG_sij_prime_guard (R : ℝ) (W D : ℕ) (hsmall : ∀ p, p.Prime → p ≤ D → p ∣ W)
    (m : Fin k) (lam : (Fin k → ℕ) →₀ ℝ)
    (hlam : lam.HasPermissibleSupport ⌊R⌋₊ W)
    (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ) (i j : Fin k) (hij : i ≠ j)
    (hnz : PrimeGaps.ym m lam (boldB u s) ≠ 0)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ s i j) :
    D < q :=
  lt_of_not_ge fun hqD ↦ hq.coprime_iff_not_dvd.mp
    ((PrimeGaps.ym_coord_coprimeW W m lam R hlam (boldB u s) hnz j).coprime_dvd_left
      (hqd.trans (sij_dvd_boldB u s i j hij))) (hsmall q hq hqD)

/-- `PrimeGaps.ym m lam (boldA u s) ≠ 0` forces each `u a` to be coprime to `W`. -/
lemma pairMasterG_u_support (R : ℝ) (W : ℕ) (m : Fin k) (lam : (Fin k → ℕ) →₀ ℝ)
    (hlam : lam.HasPermissibleSupport ⌊R⌋₊ W)
    (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ) (a : Fin k)
    (hnz : PrimeGaps.ym m lam (boldA u s) ≠ 0) :
    Nat.Coprime (u a) W :=
  (PrimeGaps.ym_coord_coprimeW W m lam R hlam (boldA u s) hnz a).coprime_dvd_left
    (ua_dvd_boldA u s a)

/-- The range of `r ↦ |PrimeGaps.ym m lam r|` is bounded above, its support lying in the finite box
`[0, ⌊Rr⌋₊]^k`. -/
lemma ym_abs_bddAbove (m : Fin k) (lam : (Fin k → ℕ) →₀ ℝ) (Rr : ℝ) (W : ℕ)
    (hlam : lam.HasPermissibleSupport ⌊Rr⌋₊ W) :
    BddAbove (Set.range fun r : Fin k → ℕ ↦ |PrimeGaps.ym m lam r|) := by
  refine Set.Finite.bddAbove (Set.Finite.subset ((Set.Finite.image
    (fun r : Fin k → ℕ ↦ |PrimeGaps.ym m lam r|)
    (Finset.finite_toSet (Fintype.piFinset fun _ : Fin k ↦ Finset.Icc 0 ⌊Rr⌋₊))).insert 0) ?_)
  rintro _ ⟨r, rfl⟩
  by_cases hr : PrimeGaps.ym m lam r = 0
  · left; simp only [hr, abs_zero]
  · exact Or.inr ⟨r, Finset.mem_coe.mpr (Fintype.mem_piFinset.mpr fun i ↦ Finset.mem_Icc.mpr
      ⟨Nat.zero_le _, PrimeGaps.ym_coord_le_floor m lam Rr W hlam r hr i⟩), rfl⟩

/-- `|ym m lam (boldA u s) * ym m lam (boldB u s)| ≤ (⨆ r, |ym m lam r|) ^ 2`. -/
lemma pairMasterG_sup_bound (m : Fin k) (lam : (Fin k → ℕ) →₀ ℝ) (Rr : ℝ) (W : ℕ)
    (hlam : lam.HasPermissibleSupport ⌊Rr⌋₊ W) (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ) :
    |PrimeGaps.ym m lam (boldA u s) * PrimeGaps.ym m lam (boldB u s)| ≤
      (⨆ r, |PrimeGaps.ym m lam r|) ^ 2 := by
  have hbdd := PrimeGaps.ym_abs_bddAbove m lam Rr W hlam
  rw [abs_mul, sq]
  exact mul_le_mul (le_ciSup hbdd _) (le_ciSup hbdd _) (abs_nonneg _)
    (Real.iSup_nonneg fun _ ↦ abs_nonneg _)

/-- `(Finset.univ.erase m).card = k - 1` for `m : Fin k`. -/
lemma card_univ_erase_m (m : Fin k) : #(Finset.univ.erase m) = k - 1 := by simp

/-- `u`-coordinate weight: `μ(n)²/g n` for `n ∈ [1, ⌊R⌋₊]` coprime to `W`, else `0`. -/
noncomputable def Fu (R : ℝ) (W : ℕ) : ℕ → ℝ :=
  fun n ↦ if n ∈ Finset.Icc 1 ⌊R⌋₊ ∧ Nat.Coprime n W
  then (μ n : ℝ) ^ 2 / (g n : ℝ) else 0

open Classical in
/-- Distinguished-pair tail weight: `|μ(n)|/g(n)²` for `n > D` squarefree with all prime factors
exceeding `D`, else `0`. -/
noncomputable def Fij (D : ℕ) : ℕ → ℝ :=
  fun n ↦ if D < n ∧ Squarefree n ∧ (∀ q, Nat.Prime q → q ∣ n → D < q)
  then |(μ n : ℝ)| / (g n : ℝ) ^ 2 else 0

/-- `m`-pinned coordinate weight: on slot `m` it is the indicator `n = 1`, elsewhere `Fu`. -/
noncomputable def Gu (R : ℝ) (W : ℕ) (m : Fin k) : Fin k → ℕ → ℝ :=
  fun a n ↦ if a = m then (if n = 1 then (1 : ℝ) else 0) else Fu R W n

/-- Distinguished-pair-pinned matrix coordinate weight over `Fin k × Fin k`: on the distinguished
pair `(i,j)` it is `Fij`; on the remaining off-diagonal slots it is `term`; on the diagonal (and
any slot outside `offDiag`) it is the indicator `n = 1`. -/
noncomputable def Gs (D : ℕ) (i j : Fin k) : (Fin k × Fin k) → ℕ → ℝ :=
  PrimeGaps.matrixWeight i j (Fij D) PrimeGaps.term

/-- `0 ≤ Fu R W n`. -/
lemma Fu_nonneg (R : ℝ) (W : ℕ) (n : ℕ) : 0 ≤ Fu R W n := by
  unfold Fu; split <;> positivity

/-- `Fu R W` is supported on `[0, ⌊R⌋₊]`. -/
lemma Fu_support (R : ℝ) (W : ℕ) (n : ℕ) (hn : Fu R W n ≠ 0) : n ≤ ⌊R⌋₊ := by
  unfold Fu at hn
  split_ifs at hn with hc
  exacts [(Finset.mem_Icc.mp hc.1).2, absurd rfl hn]

/-- Off the pinned slot `m`, `Gu` is `Fu`. -/
lemma Gu_of_mem_erase (R : ℝ) (W : ℕ) (m a : Fin k) (ha : a ∈ Finset.univ.erase m) (n : ℕ) :
    Gu R W m a n = Fu R W n := if_neg (Finset.ne_of_mem_erase ha)

/-- On the pinned slot `m`, `Gu` is the `n = 1` indicator. -/
lemma Gu_of_notMem_erase (R : ℝ) (W : ℕ) (m a : Fin k) (ha : a ∉ Finset.univ.erase m) (n : ℕ) :
    Gu R W m a n = if n = 1 then (1 : ℝ) else 0 := if_pos (by simpa using ha)

/-- `0 ≤ Fij D n`. -/
lemma Fij_nonneg (D : ℕ) (n : ℕ) : 0 ≤ Fij D n := by unfold Fij; split <;> positivity

/-- `0 ≤ Gu R W m a n`. -/
lemma Gu_nonneg (R : ℝ) (W : ℕ) (m : Fin k) (a : Fin k) (n : ℕ) : 0 ≤ Gu R W m a n := by
  unfold Gu; split_ifs <;> simp [Fu_nonneg]

/-- `0 ≤ Gs D i j p n`. -/
lemma Gs_nonneg (D : ℕ) (i j : Fin k) (p : Fin k × Fin k) (n : ℕ) : 0 ≤ Gs D i j p n :=
  PrimeGaps.matrixWeight_nonneg i j (Fij_nonneg D) PrimeGaps.term_nonneg p n

/-- On a tuple `u` at which `ym m lam (boldA u s)` does not vanish, the `Gu`-product is exactly
the diagonal Möbius weight `∏ i, μ (u i) ^ 2 / g (u i)`: each coordinate `a ≠ m` lies in
`[1, ⌊R⌋₊]` and is coprime to `W`, so `Gu` unfolds to `Fu`, while the pinned coordinate
contributes `1`. -/
private lemma prod_Gu_eq_prod_moebius_sq_div_g (R : ℝ) (W : ℕ) (m : Fin k)
    (lam : (Fin k → ℕ) →₀ ℝ) (hlam : lam.HasPermissibleSupport ⌊R⌋₊ W)
    (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ) (h1u : ∀ i, 1 ≤ u i)
    (hsij1 : ∀ i j, i ≠ j → 1 ≤ s i j) (hbA0 : PrimeGaps.ym m lam (boldA u s) ≠ 0) :
    (∏ a : Fin k, Gu R W m a (u a)) =
      ∏ i, (μ (u i) : ℝ) ^ 2 / (g (u i) : ℝ) := by
  have hum : u m = 1 := boldA_pin_um m lam R W hlam u s hbA0
  refine Finset.prod_congr rfl fun a _ ↦ ?_
  unfold Gu
  by_cases ha : a = m
  · rw [if_pos ha, ha, hum, if_pos rfl]
    simp [ArithmeticFunction.detotient_one]
  · rw [if_neg ha]
    unfold Fu
    rw [if_pos]
    have hbApos : 0 < boldA u s a := Nat.mul_pos (h1u a) (Finset.prod_pos fun x hx ↦
      Nat.zero_lt_one.trans_le (hsij1 a x (Finset.mem_erase.mp hx).1.symm))
    exact ⟨Finset.mem_Icc.mpr ⟨h1u a, (Nat.le_of_dvd hbApos (ua_dvd_boldA u s a)).trans
      (PrimeGaps.ym_coord_le_floor m lam R W hlam (boldA u s) hbA0 a)⟩,
      pairMasterG_u_support R W m lam hlam u s a hbA0⟩

/-- On a matrix `s` at which `ym m lam (boldB u s)` does not vanish, the off-diagonal Möbius
product is dominated by the `Gs`-product: every off-diagonal entry is squarefree, and the
distinguished entry `s i j` additionally exceeds `D` and has all its prime factors above `D`,
which is exactly what `Fij D` demands. -/
private lemma abs_prod_moebius_div_g_sq_le_prod_Gs (R : ℝ) (W D : ℕ) (m : Fin k)
    (lam : (Fin k → ℕ) →₀ ℝ) (hlam : lam.HasPermissibleSupport ⌊R⌋₊ W)
    (hsmall : ∀ p, p.Prime → p ≤ D → p ∣ W) (i j : Fin k) (hij : i ≠ j)
    (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ) (hsii : ∀ i, s i i = 1)
    (hsij1 : ∀ i j, i ≠ j → 1 ≤ s i j) (hD0lt : D < s i j)
    (hbB0 : PrimeGaps.ym m lam (boldB u s) ≠ 0) :
    |∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
        (μ (s p.1 p.2) : ℝ) / (g (s p.1 p.2) : ℝ) ^ 2| ≤
      ∏ p : Fin k × Fin k, Gs D i j p (s p.1 p.2) := by
  have hsf : ∀ p : Fin k × Fin k, p.1 ≠ p.2 → Squarefree (s p.1 p.2) := fun p hp ↦
    (PrimeGaps.ym_coord_squarefree m lam R W hlam (boldB u s) hbB0 p.2).squarefree_of_dvd
      (sij_dvd_boldB u s p.1 p.2 hp)
  have hFij_eq : Fij D (s i j) = |(μ (s i j) : ℝ)| / (g (s i j) : ℝ) ^ 2 :=
    if_pos ⟨hD0lt, hsf (i, j) hij,
      pairMasterG_sij_prime_guard R W D hsmall m lam hlam u s i j hij hbB0⟩
  have hGs_split : (∏ p : Fin k × Fin k, Gs D i j p (s p.1 p.2)) =
      Fij D (s i j) * ∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)).erase (i,j),
        PrimeGaps.term (s p.1 p.2) :=
    PrimeGaps.prod_matrixWeight_of_diag i j hij (Fij D) PrimeGaps.term s hsii
  rw [Finset.abs_prod, hGs_split, ← Finset.prod_erase_mul _ _ (mem_offDiag_pair i j hij),
    mul_comm (Fij D (s i j))]
  refine mul_le_mul (Finset.prod_le_prod (fun p _ ↦ abs_nonneg _) fun p hp ↦ ?_)
    (le_of_eq (by rw [hFij_eq, abs_div, abs_sq])) (abs_nonneg _)
    (Finset.prod_nonneg fun p _ ↦ PrimeGaps.term_nonneg _)
  have hne : p.1 ≠ p.2 := (Finset.mem_offDiag.mp (Finset.mem_of_mem_erase hp)).2.2
  have hcond : 1 ≤ s p.1 p.2 ∧ Squarefree (s p.1 p.2) := ⟨hsij1 p.1 p.2 hne, hsf p hne⟩
  exact le_of_eq (by rw [PrimeGaps.term_eq_squarefree, if_pos hcond, abs_div, abs_sq])

/-- Pointwise majorant for the `(i,j)`-guarded summand: its absolute value is at most
`(⨆ r, |ym m lam r|) ^ 2 * (∏ a, Gu R W m a (u a)) * (∏ p, Gs D i j p (s p.1 p.2))`. -/
lemma pairMasterG_pointwise (R : ℝ) (W D : ℕ) (m : Fin k) (lam : (Fin k → ℕ) →₀ ℝ)
    (hlam : lam.HasPermissibleSupport ⌊R⌋₊ W)
    (hsmall : ∀ p, p.Prime → p ≤ D → p ∣ W)
    (i j : Fin k) (hij : i ≠ j) (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ) :
    |(if ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
      RestrictedCoprime u s ∧ D < s i j) then
        (∏ i, (μ (u i) : ℝ) ^ 2 / (g (u i) : ℝ)) *
        (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
            (μ (s p.1 p.2) : ℝ) / (g (s p.1 p.2) : ℝ) ^ 2) *
        PrimeGaps.ym m lam (boldA u s) * PrimeGaps.ym m lam (boldB u s)
      else 0)| ≤ (⨆ r, |PrimeGaps.ym m lam r|) ^ 2 * (∏ a : Fin k, Gu R W m a (u a)) *
          (∏ p : Fin k × Fin k, Gs D i j p (s p.1 p.2)) := by
  have hRHS_nonneg : 0 ≤ (⨆ r, |PrimeGaps.ym m lam r|) ^ 2 * (∏ a : Fin k, Gu R W m a (u a)) *
      (∏ p : Fin k × Fin k, Gs D i j p (s p.1 p.2)) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (Finset.prod_nonneg fun a _ ↦ Gu_nonneg R W m a (u a)))
      (Finset.prod_nonneg fun p _ ↦ Gs_nonneg D i j p (s p.1 p.2))
  by_cases hguard : (∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
        RestrictedCoprime u s ∧ D < s i j
  · rw [if_pos hguard]
    obtain ⟨h1u, hsii, hsij1, -, hD0lt⟩ := hguard
    by_cases hbA0 : PrimeGaps.ym m lam (boldA u s) = 0
    · rw [hbA0, mul_zero, zero_mul, abs_zero]; exact hRHS_nonneg
    by_cases hbB0 : PrimeGaps.ym m lam (boldB u s) = 0
    · rw [hbB0, mul_zero, abs_zero]; exact hRHS_nonneg
    have hA_nn : (0 : ℝ) ≤ ∏ i, (μ (u i) : ℝ) ^ 2 / (g (u i) : ℝ) := by
      positivity
    rw [mul_assoc, abs_mul, abs_mul,
      prod_Gu_eq_prod_moebius_sq_div_g R W m lam hlam u s h1u hsij1 hbA0, abs_of_nonneg hA_nn]
    calc _ ≤ (∏ i, (μ (u i) : ℝ) ^ 2 / (g (u i) : ℝ)) *
            (∏ p : Fin k × Fin k, Gs D i j p (s p.1 p.2)) * (⨆ r, |PrimeGaps.ym m lam r|) ^ 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (abs_prod_moebius_div_g_sq_le_prod_Gs R W D m lam
            hlam hsmall i j hij u s hsii hsij1 hD0lt hbB0) hA_nn)
            (pairMasterG_sup_bound m lam R W hlam u s) (abs_nonneg _)
            (mul_nonneg hA_nn (Finset.prod_nonneg fun p _ ↦ Gs_nonneg D i j p (s p.1 p.2)))
      _ = (⨆ r, |PrimeGaps.ym m lam r|) ^ 2 *
            (∏ i, (μ (u i) : ℝ) ^ 2 / (g (u i) : ℝ)) *
            (∏ p : Fin k × Fin k, Gs D i j p (s p.1 p.2)) := by ring
  · rw [if_neg hguard, abs_zero]; exact hRHS_nonneg

/-- `Gu R W m a` is summable, its support lying in `[0, max ⌊R⌋₊ 1]`. -/
lemma Gu_summable (R : ℝ) (W : ℕ) (m a : Fin k) : Summable (fun n ↦ Gu R W m a n) :=
  summable_of_support_le
    (pinned_support (Fu_support R W) (Gu_of_mem_erase R W m) (Gu_of_notMem_erase R W m) a)

/-- The `u`-box tsum factors as `(∑' n, Fu R W n) ^ (k - 1)`, the pinned slot `m` contributing `1`.
-/
lemma tsum_Fu_factor (R : ℝ) (W : ℕ) (m : Fin k) :
    (∑' u : Fin k → ℕ, ∏ a : Fin k, Gu R W m a (u a)) =
      (∑' n : ℕ, Fu R W n) ^ (k - 1) := by
  rw [pinned_block_factor (Finset.univ.erase m) (Gu R W m) (Fu R W) (Fu_support R W)
      (Gu_of_mem_erase R W m) (Gu_of_notMem_erase R W m), card_univ_erase_m]

/-- `Fij D` is summable, being the guarded tail summand of `gtail_Fsum_summable`. -/
lemma Fij_summable (D : ℕ) : Summable (Fij D) := gtail_Fsum_summable D

/-- `Gs D i j p` is summable in each of its three cases. -/
lemma Gs_summable (D : ℕ) (i j : Fin k) (p : Fin k × Fin k) : Summable (fun n ↦ Gs D i j p n) :=
  PrimeGaps.matrixWeight_summable i j (Fij_summable D) PrimeGaps.convergent_sum_g p

/-- The `s`-box tsum factors as `(∑' n, Fij D n) * (∑' n, term n) ^ (k ^ 2 - k - 1)`. -/
lemma tsum_term_Fij_factor (D : ℕ) (i j : Fin k) (hij : i ≠ j) :
    (∑' s : Fin k → Fin k → ℕ, ∏ p : Fin k × Fin k, Gs D i j p (s p.1 p.2)) =
      (∑' n : ℕ, Fij D n) * (∑' n : ℕ, PrimeGaps.term n) ^ (k ^ 2 - k - 1) :=
  PrimeGaps.tsum_prod_matrixWeight i j hij (Fij_nonneg D) PrimeGaps.term_nonneg
    (Fij_summable D) PrimeGaps.convergent_sum_g

/-- `∑' n, Fu R W n` is the finite sum `∑_{u ∈ [1, ⌊R⌋₊], (u,W)=1} μ(u)²/g u`. -/
lemma tsum_Fu_eq (R : ℝ) (W : ℕ) : (∑' n : ℕ, Fu R W n) = ∑ u ∈ Finset.Icc 1 ⌊R⌋₊ with
        Nat.Coprime u W,
        (μ u : ℝ) ^ 2 / (g u : ℝ) := by
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊R⌋₊)
      (fun b hb ↦ by unfold Fu; rw [if_neg]; exact fun hcond ↦ hb hcond.1), Finset.sum_filter]
  exact Finset.sum_congr rfl fun n hn ↦ by unfold Fu; simp only [hn, true_and]

/-- `∑' n, term n` in its squarefree-support presentation. -/
lemma tsum_term_eq_squarefree : (∑' n : ℕ, PrimeGaps.term n) = ∑' s : ℕ, if 1 ≤ s ∧ Squarefree s
          then |(μ s : ℝ)| / (g s : ℝ) ^ 2
          else 0 := tsum_congr PrimeGaps.term_eq_squarefree

open Classical in
/-- `∑' n, Fij D n` written out as the guarded tail sum. -/
lemma tsum_Fij_eq (D : ℕ) : (∑' n : ℕ, Fij D n) = ∑' s : ℕ, if D < s ∧ Squarefree s ∧
                    (∀ q, Nat.Prime q → q ∣ s → D < q)
          then |(μ s : ℝ)| / (g s : ℝ) ^ 2
          else 0 := rfl

open Classical in
/-- The `(i,j)`-guarded double tsum of absolute values is bounded by `(⨆ r, |ym m lam r|) ^ 2` times
the `(k-1)`-st power of the `u`-sum, the `(k²-k-1)`-st power of the off-diagonal sum, and the
guarded tail sum. -/
lemma pairMasterG_final (R : ℝ) (W D : ℕ) (m : Fin k) (lam : (Fin k → ℕ) →₀ ℝ)
    (hlam : lam.HasPermissibleSupport ⌊R⌋₊ W)
    (hsmall : ∀ p, p.Prime → p ≤ D → p ∣ W)
    (i j : Fin k) (hij : i ≠ j) :
    (∑' u : Fin k → ℕ, ∑' s : Fin k → Fin k → ℕ,
        |(if ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
              RestrictedCoprime u s ∧ D < s i j) then
            (∏ i, (μ (u i) : ℝ) ^ 2 / (g (u i) : ℝ)) *
            (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
                (μ (s p.1 p.2) : ℝ) / (g (s p.1 p.2) : ℝ) ^ 2) *
            PrimeGaps.ym m lam (boldA u s) * PrimeGaps.ym m lam (boldB u s)
          else 0)|) ≤ (⨆ r, |PrimeGaps.ym m lam r|) ^ 2 *
          (∑ u ∈ Finset.Icc 1 ⌊R⌋₊ with (Nat.Coprime u
            W), (μ u : ℝ) ^ 2 / (g u : ℝ)) ^ (k - 1) *
          (∑' s : ℕ, if 1 ≤ s ∧ Squarefree s
              then |(μ s : ℝ)| / (g s : ℝ) ^ 2
              else 0) ^ (k ^ 2 - k - 1) * (∑' s : ℕ, if D < s ∧ Squarefree s ∧
                    (∀ q, Nat.Prime q → q ∣ s → D < q)
              then |(μ s : ℝ)| / (g s : ℝ) ^ 2
              else 0) := by
  set Y : ℝ := (⨆ r, |PrimeGaps.ym m lam r|) ^ 2
  set Pu : (Fin k → ℕ) → ℝ := fun u ↦ ∏ a : Fin k, Gu R W m a (u a) with hPu
  set Ps : (Fin k → Fin k → ℕ) → ℝ := fun s ↦ ∏ p : Fin k × Fin k, Gs D i j p (s p.1 p.2) with hPs
  set F : (Fin k → ℕ) → (Fin k → Fin k → ℕ) → ℝ := fun u s ↦
      |(if ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
            RestrictedCoprime u s ∧ D < s i j) then
          (∏ i, (μ (u i) : ℝ) ^ 2 / (g (u i) : ℝ)) *
          (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
              (μ (s p.1 p.2) : ℝ) / (g (s p.1 p.2) : ℝ) ^ 2) *
          PrimeGaps.ym m lam (boldA u s) * PrimeGaps.ym m lam (boldB u s)
        else 0)|
  have hPs_summable : Summable Ps := by
    rw [show Ps = (fun t : Fin k × Fin k → ℕ ↦ ∏ p, Gs D i j p (t p))
        ∘ (Equiv.curry (Fin k) (Fin k) ℕ).symm from funext fun _ ↦ rfl]
    exact (Equiv.summable_iff _).mpr
      (summable_prod_of_summable (Gs D i j) (Gs_nonneg D i j) (Gs_summable D i j))
  have hPu_summable : Summable Pu :=
    summable_prod_of_summable (Gu R W m) (Gu_nonneg R W m) (Gu_summable R W m)
  calc (∑' u, ∑' s, F u s) ≤ Y * (∑' u, Pu u) * ∑' s, Ps s :=
        tsum_tsum_le_of_prod_majorant F Y Pu Ps (fun _ _ ↦ abs_nonneg _)
          (pairMasterG_pointwise R W D m lam hlam hsmall i j hij) hPu_summable hPs_summable
    _ = Y * (∑' n : ℕ, Fu R W n) ^ (k - 1) *
          ((∑' n : ℕ, Fij D n) * (∑' n : ℕ, PrimeGaps.term n) ^ (k ^ 2 - k - 1)) := by
        rw [hPu, hPs, tsum_Fu_factor R W m, tsum_term_Fij_factor D i j hij]
    _ = Y * (∑ u ∈ Finset.Icc 1 ⌊R⌋₊ with (Nat.Coprime u
            W), (μ u : ℝ) ^ 2 / (g u : ℝ)) ^ (k - 1) *
          (∑' s : ℕ, if 1 ≤ s ∧ Squarefree s
              then |(μ s : ℝ)| / (g s : ℝ) ^ 2
              else 0) ^ (k ^ 2 - k - 1) * (∑' s : ℕ, if D < s ∧ Squarefree s ∧
                    (∀ q, Nat.Prime q → q ∣ s → D < q)
              then |(μ s : ℝ)| / (g s : ℝ) ^ 2
              else 0) := by
        rw [tsum_Fu_eq R W, tsum_Fij_eq D, tsum_term_eq_squarefree]
        ring
end PrimeGaps
