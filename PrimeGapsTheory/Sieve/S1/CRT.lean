/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Computability.Reduce
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Data.Int.Star
public import Mathlib.NumberTheory.Harmonic.Bounds
public import PrimeGapsTheory.ArithmeticFunction.LYTransform.Estimate
public import PrimeGapsTheory.Arithmetic.RestrictedReciprocalSum
public import PrimeGapsTheory.Sieve.CRT

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Chinese-remainder evaluation for the first moment

Evaluates the first-moment congruence count `S(d, e)` by the Chinese remainder theorem, and
bounds the resulting aggregate remainder against the main term of the first moment.

## Main definitions

* `PrimeGaps.qMod`: The combined congruence modulus `W * ∏ i, Nat.lcm (d i) (e i)`.
* `PrimeGaps.PairwiseCoprimeModuli`: Pairwise coprimality of `W` together with the `Nat.lcm`
  moduli.
* `PrimeGaps.Scount`: The number of integers satisfying the first-moment congruences.
* `PrimeGaps.Rcut`: The sieve truncation level `N ^ (θ / 2 - δ)` as a function of a real `N`.
* `PrimeGaps.rho`: The local remainder term `ρ(d, e)`.
* `PrimeGaps.aggregateRemainder`, `PrimeGaps.aggregateAbsRemainder`: The weighted and absolute
  double sums of `PrimeGaps.rho` over the support of `λ`.

## Main results

* `PrimeGaps.lem_S1_CRT`: Evaluates the congruence count in the coprime and non-coprime cases.
* `PrimeGaps.divisor_count_le`, `PrimeGaps.lem_support_count`: Divisor-type bounds on the
  cardinality of the sieve index set.
* `PrimeGaps.gpy_aggregate_remainder_bound`: The chain of bounds on the aggregate remainder.
* `PrimeGaps.eventually_master`: The master reduction `R² (log R)^{3k} W^{k+1} D₀ ≤ N`.
* `PrimeGaps.crt_error_negligible`: Bounds the aggregate Chinese-remainder error.
-/

open Filter Int Nat Topology

@[expose] public section

open Real

open scoped Finset

namespace Int

/-- Count of integers in `Ico a b` in a fixed residue class mod `q` (`q > 0`) equals the length of
an explicit integer interval of `t` 's. -/
private lemma aux_count_modeq (a b q : ℤ) (hq : 0 < q) (r : ℤ) :
    #{n ∈ (Finset.Ico a b) | n ≡ r [ZMOD q]} =
      #(Finset.Ico (⌈((a - r : ℤ) : ℚ) / q⌉) (⌈((b - r : ℤ) : ℚ) / q⌉)) := by
  have h := Int.Ico_filter_modEq_card a b hq r
  rw [← Int.toNat_eq_max] at h
  rw [Int.card_Ico]
  push_cast at h ⊢
  exact_mod_cast h

/-- The count of a fixed residue class mod `q` (`q > 0`) inside `Ico a b` (`a ≤ b`) is within `1`
of the real number `(b - a)/q`. -/
private lemma aux_count_bound (a b q : ℤ) (hq : 0 < q) (r : ℤ) (hab : a ≤ b) :
    |(#{n ∈ (Finset.Ico a b) | n ≡ r [ZMOD q]} : ℝ) - ((b : ℝ) - a) / q| ≤ 1 := by
  rw [aux_count_modeq a b q hq r]
  set A := ((a : ℝ) - r) / q with hA
  set B := ((b : ℝ) - r) / q with hB
  have ecA : ⌈((a - r : ℤ) : ℚ) / q⌉ = ⌈A⌉ := by
    rw [← Rat.ceil_cast (α := ℝ) (((a - r : ℤ) : ℚ) / q)]; congr 1; rw [hA]; push_cast; ring
  have ecB : ⌈((b - r : ℤ) : ℚ) / q⌉ = ⌈B⌉ := by
    rw [← Rat.ceil_cast (α := ℝ) (((b - r : ℤ) : ℚ) / q)]; congr 1; rw [hB]; push_cast; ring
  have hAB : A ≤ B := by rw [hA, hB]; gcongr
  have hcd : ⌈A⌉ ≤ ⌈B⌉ := Int.ceil_le_ceil hAB
  have hcard : (#(Finset.Ico ⌈A⌉ ⌈B⌉) : ℝ) = (⌈B⌉ : ℝ) - ⌈A⌉ := by
    rw [Int.card_Ico]
    exact_mod_cast Int.toNat_of_nonneg (show (0 : ℤ) ≤ ⌈B⌉ - ⌈A⌉ by omega)
  have hBA : ((b : ℝ) - a) / q = B - A := by rw [hA, hB]; field_simp; ring
  rw [ecA, ecB, hcard, hBA, abs_le]
  have ha := Int.le_ceil A
  have hb := Int.le_ceil B
  have ha' := Int.ceil_lt_add_one A
  have hb' := Int.ceil_lt_add_one B
  constructor <;> linarith

end Int

namespace PrimeGaps

/-- The combined congruence modulus `qMod W d e = W * ∏ i, Nat.lcm (d i) (e i)`. -/
@[pg_tag "bg246" "def_q_lcm"]
def qMod {k : ℕ} (W : ℕ) (d e : Fin k → ℕ) : ℕ := W * ∏ i, Nat.lcm (d i) (e i)

/-- The `k + 1` moduli `W, [d₁, e₁], …, [dₖ, eₖ]` are *pairwise coprime*: any two distinct members
have gcd `1`. The `k + 1` members are encoded as the function `Fin (k + 1) → ℕ` sending `0` to `W`
and `i + 1` to `[dᵢ, eᵢ]`. -/
def PairwiseCoprimeModuli {k : ℕ} (W : ℕ) (m : Fin k → ℕ) : Prop :=
  Pairwise (Function.onFun Nat.Coprime (Fin.cons W m : Fin (k + 1) → ℕ))

/-- The number of `n ∈ (N, 2N]` with `n ≡ v₀ [ZMOD W]` and `[dᵢ, eᵢ] ∣ n + Hᵢ` for every `i`. -/
noncomputable def Scount {k : ℕ} (H : Fin k → ℕ) (N W v₀ : ℕ) (d e : Fin k → ℕ) : ℕ :=
  #{n ∈ (Finset.Ioc (N : ℤ) (2 * N : ℤ)) |
      (n : ℤ) ≡ (v₀ : ℤ) [ZMOD (W : ℤ)] ∧ ∀ i, ((Nat.lcm (d i) (e i) : ℤ)) ∣ (n + H i)}

/-- The combined modulus is positive when `0 < W` and `d i, e i > 0` for every `i`. -/
lemma lem_qMod_pos {k : ℕ} (W : ℕ) (d e : Fin k → ℕ)
    (hW : 0 < W) (hd : ∀ i, 0 < d i) (he : ∀ i, 0 < e i) : 0 < qMod W d e :=
  Nat.mul_pos hW <| Finset.prod_pos fun i _ ↦ Nat.lcm_pos (hd i) (he i)

/-- From `lambda d ≠ 0` and `lambda.HasPermissibleSupport R W` one reads off the support conditions
on `d` (and symmetrically on `e`). Only coprimality to `W` and squarefreeness of `∏ i, d i` are
needed downstream. -/
lemma lem_support_conds {k R W : ℕ} (lambda : (Fin k → ℕ) →₀ ℝ)
    (hsupp : lambda.HasPermissibleSupport R W)
    (d : Fin k → ℕ) (hd : lambda d ≠ 0) :
    (∏ i, d i).Coprime W ∧ Squarefree (∏ i, d i) :=
  ⟨hsupp.coprime_prod_W_of_ne_zero hd, hsupp.squarefree_prod_of_ne_zero hd⟩

/-- When the `k + 1` moduli `W, [d₁, e₁], …, [dₖ, eₖ]` are pairwise coprime, the count is within
`1` of `N / q`. -/
lemma lem_coprime_branch {k : ℕ} (H : Fin k → ℕ) (N W : ℕ) (v₀ : ℕ) (d e : Fin k → ℕ)
    (hW : 0 < W) (hd : ∀ i, 0 < d i) (he : ∀ i, 0 < e i)
    (hpc : PairwiseCoprimeModuli W (fun i ↦ Nat.lcm (d i) (e i))) :
    |(Scount H N W v₀ d e : ℝ) - N / (qMod W d e : ℝ)| ≤ 1 := by
  classical
  set fnat : Fin (k + 1) → ℕ := Fin.cons W (fun i ↦ Nat.lcm (d i) (e i)) with hfnat
  set M : Fin (k + 1) → ℤ := fun j ↦ ((fnat j : ℕ) : ℤ) with hM
  set Rres : Fin (k + 1) → ℤ := Fin.cons (v₀ : ℤ) (fun i ↦ - H i) with hRres
  have hcopZ : ∀ a b : Fin (k + 1), a ≠ b → IsCoprime (M a) (M b) := fun a b hab ↦ by
    rw [hM, Nat.isCoprime_iff_coprime]; exact hpc hab
  have hqprodNat : (∏ j, fnat j) = qMod W d e := by rw [hfnat, Fin.prod_cons]; rfl
  have hqprod : ((qMod W d e : ℕ) : ℤ) = ∏ j, M j := by rw [← hqprodNat, Nat.cast_prod]
  obtain ⟨r₀, hr₀iff⟩ := Int.crt_equiv (Finset.univ : Finset (Fin (k + 1))) M Rres
      (fun i _ j _ hij ↦ hcopZ i j hij)
  have hjiff : ∀ n : ℤ, (∀ j, n ≡ Rres j [ZMOD M j]) ↔ n ≡ r₀ [ZMOD (∏ j, M j)] := fun n ↦ by
    simpa [Finset.mem_univ] using hr₀iff n
  have hPjiff : ∀ n : ℤ, ((n : ℤ) ≡ (v₀ : ℤ) [ZMOD (W : ℤ)] ∧ ∀ i, ((Nat.lcm (d i) (e i) : ℤ)) ∣
        (n + H i)) ↔
      (∀ j, n ≡ Rres j [ZMOD M j]) := by
    intro n
    constructor
    · rintro ⟨h0, hi⟩ j
      refine Fin.cases ?_ ?_ j
      · simpa only [hRres, hM, hfnat, Fin.cons_zero] using h0
      · intro i
        simp only [hRres, hM, hfnat, Fin.cons_succ]
        rw [Int.modEq_iff_dvd, show -(H i : ℤ) - n = -(n + H i) by ring]
        exact dvd_neg.mpr (hi i)
    · refine fun h ↦ ⟨by simpa only [hRres, hM, hfnat, Fin.cons_zero] using h 0, fun i ↦ ?_⟩
      have hs := h i.succ
      simp only [hRres, hM, hfnat, Fin.cons_succ] at hs
      rw [Int.modEq_iff_dvd, show -(H i : ℤ) - n = -(n + H i) by ring, dvd_neg] at hs
      exact hs
  have hPiff : ∀ n : ℤ, ((n : ℤ) ≡ (v₀ : ℤ) [ZMOD (W : ℤ)] ∧ ∀ i, ((Nat.lcm (d i) (e i) : ℤ)) ∣
        (n + H i)) ↔
      n ≡ r₀ [ZMOD ((qMod W d e : ℕ) : ℤ)] := fun n ↦ by rw [hPjiff n, hjiff n, hqprod]
  set q : ℤ := ((qMod W d e : ℕ) : ℤ) with hqdef
  have hqpos : 0 < q := by rw [hqdef]; exact_mod_cast lem_qMod_pos W d e hW hd he
  set qr : ℝ := (qMod W d e : ℝ) with hqrdef
  have hqr_eq : (q : ℝ) = qr := by rw [hqdef, hqrdef]; push_cast; ring
  have hScount : Scount H N W v₀ d e =
      #{n ∈ (Finset.Ioc (N : ℤ) (2 * N : ℤ)) | n ≡ r₀ [ZMOD q]} := by
    unfold Scount
    exact congrArg _ (Finset.filter_congr fun n _ ↦ by simpa only [hqdef] using hPiff n)
  have hset : Finset.Ioc (N : ℤ) (2 * N : ℤ) = Finset.Ico (N + 1 : ℤ) (2 * N + 1 : ℤ) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hScount, hset]
  have hb := Int.aux_count_bound (N + 1 : ℤ) (2 * N + 1 : ℤ) q hqpos r₀ (by omega)
  have hlength : (((2 * N + 1 : ℤ) : ℝ) - ((N + 1 : ℤ) : ℝ)) / (q : ℝ) = (N : ℝ) / qr := by
    rw [hqr_eq]; push_cast; ring
  rwa [hlength] at hb

/-- Suppose the moduli are *not* pairwise coprime, every prime factor of every modulus exceeds
`D₀ N`, and `D₀ N ≥ max_{i ≠ j} |(H i : ℤ) - (H j : ℤ)|`. Then no `n` is counted, so
`Scount = 0`. -/
lemma lem_noncoprime_branch {k : ℕ} (H : Fin k → ℕ)
    (hHinj : Function.Injective H) (N W : ℕ) (v₀ : ℕ) (d e : Fin k → ℕ)
    (hW : W = primorial ⌊D₀ N⌋₊)
    (hbig : ∀ (i : Fin k) (p : ℕ), p.Prime → p ∣ Nat.lcm (d i) (e i) → (D₀ N) < (p : ℝ))
    (hthresh : ∀ i j : Fin k, i ≠ j → (|((H i : ℤ) - (H j : ℤ))| : ℝ) ≤ D₀ N)
    (hnpc : ¬ PairwiseCoprimeModuli W (fun i ↦ Nat.lcm (d i) (e i))) :
    Scount H N W v₀ d e = 0 := by
  rw [PairwiseCoprimeModuli, Pairwise] at hnpc
  push Not at hnpc
  obtain ⟨a, b, hab, hncop⟩ := hnpc
  set f : Fin (k + 1) → ℕ := Fin.cons W (fun i ↦ Nat.lcm (d i) (e i)) with hf
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hncop
  have hpa : p ∣ f a := hpg.trans (Nat.gcd_dvd_left _ _)
  have hpb : p ∣ f b := hpg.trans (Nat.gcd_dvd_right _ _)
  have hpW_le : p ∣ W → (p : ℝ) ≤ (⌊D₀ N⌋₊ : ℝ) := fun hpW ↦ by
    exact_mod_cast (hp.dvd_primorial_iff (n := ⌊D₀ N⌋₊)).mp (hW ▸ hpW)
  have hcross : ∀ i : Fin k, p ∣ W → p ∣ Nat.lcm (d i) (e i) → False := by
    intro i hpW hpi
    have h1 : D₀ N < (p : ℝ) := hbig i p hp hpi
    have h2 : (p : ℝ) ≤ (⌊D₀ N⌋₊ : ℝ) := hpW_le hpW
    rcases le_or_gt 0 (D₀ N) with hpos | hneg
    · linarith [Nat.floor_le hpos]
    · rw [Nat.floor_eq_zero.mpr (by linarith : D₀ N < 1), Nat.cast_zero] at h2
      have : (0 : ℝ) < p := by exact_mod_cast hp.pos
      linarith
  have hdiag : ∀ i j : Fin k, i ≠ j → p ∣ Nat.lcm (d i) (e i) → p ∣ Nat.lcm (d j) (e j) →
      Scount H N W v₀ d e = 0 := by
    intro i j hij hpi hpj
    unfold Scount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro n - ⟨-, hdvd⟩
    have hsub : (p : ℤ) ∣ ((H i : ℤ) - (H j : ℤ)) := by
      simpa using dvd_sub ((Int.natCast_dvd_natCast.mpr hpi).trans (hdvd i))
        ((Int.natCast_dvd_natCast.mpr hpj).trans (hdvd j))
    have hne : ((H i : ℤ) - (H j : ℤ)) ≠ 0 :=
      sub_ne_zero.mpr fun h ↦ hij (hHinj (by exact_mod_cast h))
    have hple : (p : ℝ) ≤ (|((H i : ℤ) - (H j : ℤ))| : ℝ) := by
      exact_mod_cast Int.le_of_dvd (abs_pos.mpr hne) ((dvd_abs _ _).mpr hsub)
    linarith [hbig i p hp hpi, hthresh i j hij]
  rcases Fin.eq_zero_or_eq_succ a with ha | ⟨i, ha⟩ <;>
      rcases Fin.eq_zero_or_eq_succ b with hb | ⟨j, hb⟩ <;>
    subst ha <;> subst hb <;> simp only [hf, Fin.cons_zero, Fin.cons_succ] at hpa hpb
  · exact absurd rfl hab
  · exact (hcross j hpa hpb).elim
  · exact (hcross i hpb hpa).elim
  · exact hdiag i j (fun h ↦ hab (by rw [h])) hpa hpb

/-- Encodes the dependence of the threshold `N₀` on the shift tuple `H` (allowed by the problem
statement). -/
lemma lem_threshold_exists {k : ℕ} (H : Fin k → ℕ) : ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ i j : Fin k, i ≠ j → (|((H i : ℤ) - (H j : ℤ))| : ℝ) ≤ D₀ N := by
  obtain ⟨N₀, hN₀3, hN₀⟩ := exists_shift_gap_threshold H
  refine ⟨N₀, hN₀3, fun N hN i j hij ↦ ?_⟩
  rw [show (|((H i : ℤ) - (H j : ℤ))| : ℝ) = ((H i).dist (H j) : ℝ) by
    push_cast; rw [Nat.abs_sub_cast_eq_dist (H i) (H j)]]
  linarith [hN₀ (N : ℝ) hN i j hij]

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- The full Chinese-Remainder-Theorem evaluation of the inner count `S(d, e)`. -/
@[pg_tag "bg246" "lem_S1_CRT"]
theorem lem_S1_CRT {k : ℕ} (H : Fin k → ℕ) (hHinj : Function.Injective H)
    (δ θ : ℝ) (lambda : (Fin k → ℕ) →₀ ℝ) :
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → lambda.HasPermissibleSupport ⌊R⌋₊ (W N) →
        ∀ v₀ : ℕ, v₀ < W N → (∀ i, IsCoprime ((v₀ : ℤ) + H i) (W N : ℤ)) →
        ∀ d e : Fin k → ℕ, (∀ i, 0 < d i) → (∀ i, 0 < e i) → lambda d ≠ 0 → lambda e ≠ 0 →
          (PairwiseCoprimeModuli (W N) (fun i ↦ Nat.lcm (d i) (e i)) →
              |(Scount H N (W N) v₀ d e : ℝ) - N / (qMod (W N) d e : ℝ)| ≤ 1) ∧
          (¬ PairwiseCoprimeModuli (W N) (fun i ↦ Nat.lcm (d i) (e i)) →
              Scount H N (W N) v₀ d e = 0) := by
  obtain ⟨N₀, hN₀3, hN₀⟩ := lem_threshold_exists H
  refine ⟨N₀, hN₀3, fun N hN hsupp v₀ _ _ d e hd he hld hle ↦
    ⟨fun hpc ↦ lem_coprime_branch H N (W N) v₀ d e W_pos hd he hpc, fun hnpc ↦ ?_⟩⟩
  obtain ⟨hcd, -⟩ := lem_support_conds lambda hsupp d hld
  obtain ⟨hce, -⟩ := lem_support_conds lambda hsupp e hle
  exact lem_noncoprime_branch H hHinj N (W N) v₀ d e W_eq_primorial_D₀
    (lcm_prime_factor_large (N : ℝ) d e hcd hce) (hN₀ N hN) hnpc

variable {k : ℕ}

/-- Real-parameter adapter for the promoted natural-parameter sieve truncation formula. -/
noncomputable def Rcut (θ δ N : ℝ) : ℝ := N ^ (θ / 2 - δ)

/-- The local remainder term `ρ(d, e)`. The count is over integers `n` with `⌊N⌋ < n ≤ ⌊2N⌋`
(equivalently, `N < n ≤ 2N`), `n ≡ v₀ (mod W)` and `[dᵢ, eᵢ] ∣ n + hᵢ` for all `i`; the main term
is `N / (W ∏ᵢ [dᵢ, eᵢ])` times the indicator that `W, [d₁, e₁], …, [dₖ, eₖ]` are pairwise
coprime. -/
noncomputable def rho (N : ℝ) (W v₀ : ℕ) (h : Fin k → ℤ) (d e : Fin k → ℕ) : ℝ :=
  open scoped Classical in
  let m : Fin k → ℕ := fun i ↦ Nat.lcm (d i) (e i)
  #((Finset.Ioc ⌊N⌋ ⌊2 * N⌋).filter
      (fun n : ℤ ↦ n % (W : ℤ) = (v₀ : ℤ) % (W : ℤ) ∧ ∀ i, (m i : ℤ) ∣ (n + h i))) -
    (N / (W * ∏ i, (m i : ℝ))) * (if PrimeGaps.PairwiseCoprimeModuli W m then 1 else 0)

/-- The aggregate weighted remainder `∑_d ∑_e λ_d λ_e ρ(d, e)`, taken over the finite support
`Ssupp` of `λ` (equal to the formal sum over `ℤ_{≥1}^k`). -/
noncomputable def aggregateRemainder (N : ℝ) (W v₀ : ℕ) (h : Fin k → ℤ)
    (lam : (Fin k → ℕ) → ℝ) (Ssupp : Finset (Fin k → ℕ)) : ℝ :=
  ∑ d ∈ Ssupp, ∑ e ∈ Ssupp, lam d * lam e * rho N W v₀ h d e

/-- The double sum of the absolute remainders `∑_d ∑_e |ρ(d,e)|` over `Ssupp`. -/
noncomputable def aggregateAbsRemainder (N : ℝ) (W v₀ : ℕ) (h : Fin k → ℤ)
    (Ssupp : Finset (Fin k → ℕ)) : ℝ :=
  ∑ d ∈ Ssupp, ∑ e ∈ Ssupp, |rho N W v₀ h d e|

/-- Core divisor-type count: the number of positive `k`-tuples `d` with all entries in `[1, B]` and
`∏ dᵢ ≤ B` is at most `B · H_B ^ k`, where `H_B = ∑_{a = 1}^B 1 / a`. -/
theorem divisor_count_le (k B : ℕ) :
    (#(Finset.filter (fun d : Fin k → ℕ ↦ (∀ i, 1 ≤ d i) ∧ (∏ i, d i) ≤ B)
        (Fintype.piFinset (fun _ : Fin k ↦ Finset.Icc 1 B))) : ℝ) ≤
      (B : ℝ) * (∑ a ∈ Finset.Icc 1 B, (a : ℝ)⁻¹) ^ k := by
  set box := Fintype.piFinset (fun _ : Fin k ↦ Finset.Icc 1 B) with hbox
  set S := Finset.filter (fun d : Fin k → ℕ ↦ (∀ i, 1 ≤ d i) ∧ (∏ i, d i) ≤ B) box with hS
  have hstep1 : ∑ d ∈ S, (1 : ℝ) ≤ ∑ d ∈ S, (B : ℝ) * ∏ i, ((d i : ℝ))⁻¹ := by
    refine Finset.sum_le_sum fun d hd ↦ ?_
    rw [hS, Finset.mem_filter] at hd
    obtain ⟨-, hpos, hprod⟩ := hd
    have hprodpos : (0 : ℝ) < ∏ i, (d i : ℝ) :=
      Finset.prod_pos fun i _ ↦ by exact_mod_cast hpos i
    rw [Finset.prod_inv_distrib, ← div_eq_mul_inv, one_le_div hprodpos]
    exact_mod_cast hprod
  have hstep2 : ∑ d ∈ S, (B : ℝ) * ∏ i, ((d i : ℝ))⁻¹ ≤
      ∑ d ∈ box, (B : ℝ) * ∏ i, ((d i : ℝ))⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg (hS ▸ Finset.filter_subset _ _)
      fun d _ _ ↦ by positivity
  have hstep3 : ∑ d ∈ box, (B : ℝ) * ∏ i, ((d i : ℝ))⁻¹ =
      (B : ℝ) * (∑ a ∈ Finset.Icc 1 B, (a : ℝ)⁻¹) ^ k := by
    rw [← Finset.mul_sum]
    congr 1
    rw [hbox, ← Finset.prod_univ_sum (fun _ : Fin k ↦ Finset.Icc 1 B) (fun _ a ↦ (a : ℝ)⁻¹),
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [show ((#S : ℝ)) = ∑ _d ∈ S, (1 : ℝ) by simp]
  exact hstep1.trans (hstep2.trans hstep3.le)

/-- Divisor-type estimate: the number of positive `k`-tuples `d ∈ ℤ_{≥1}^k` with `∏ᵢ dᵢ < R` (and
the further sieve conditions) is `≪_k R (log R) ^ k`; that is, the sieve index `Finset` has
cardinality bounded by a `k`-dependent constant times `R (log R) ^ k`, eventually as `R → ∞`.
Squaring this gives `#pairs ≪_k R² (log R) ^ (2k)`, the fact behind bound (2). -/
theorem lem_support_count (k : ℕ) : ∃ C > 0, ∀ᶠ R : ℝ in atTop, ∀ W : ℕ,
      (#(Finset.permissibleSupport k (⌈R⌉₊ - 1) W) : ℝ) ≤
        C * R * (Real.log R) ^ k := by
  refine ⟨2 ^ (k + 1), by positivity, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (rexp (1 + Real.log 2)),
    Filter.eventually_gt_atTop (0 : ℝ), Filter.eventually_ge_atTop (1 : ℝ)]
    with R hRexp hRpos hR1 W
  set B := ⌈R⌉₊ with hB
  have hsub : Finset.permissibleSupport k (⌈R⌉₊ - 1) W ⊆
      Finset.filter (fun d : Fin k → ℕ ↦ (∀ i, 1 ≤ d i) ∧ (∏ i, d i) ≤ B)
        (Fintype.piFinset (fun _ : Fin k ↦ Finset.Icc 1 B)) := by
    intro d hd
    rw [Finset.mem_permissibleSupport_iff] at hd
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    have hpos : ∀ i, 1 ≤ d i := fun i ↦ Nat.one_le_iff_ne_zero.mpr
      ((Finset.prod_ne_zero_iff.mp hd.2.2.ne_zero) i (Finset.mem_univ i))
    exact ⟨fun i ↦ Finset.mem_Icc.mpr ⟨hpos i,
      (Finset.single_le_prod' (fun j _ ↦ hpos j) (Finset.mem_univ i)).trans
        (hd.1.trans (Nat.sub_le _ _))⟩, hpos, hd.1.trans (Nat.sub_le _ _)⟩
  have hcardle : (#(Finset.permissibleSupport k (⌈R⌉₊ - 1) W) : ℝ) ≤
      (B : ℝ) * (∑ a ∈ Finset.Icc 1 B, (a : ℝ)⁻¹) ^ k :=
    le_trans (by exact_mod_cast Finset.card_le_card hsub) (divisor_count_le k B)
  have hHnonneg : (0 : ℝ) ≤ ∑ a ∈ Finset.Icc 1 B, (a : ℝ)⁻¹ :=
    Finset.sum_nonneg fun a _ ↦ by positivity
  have hHle : (∑ a ∈ Finset.Icc 1 B, (a : ℝ)⁻¹) ≤ 1 + Real.log B := by
    rw [show (∑ a ∈ Finset.Icc 1 B, (a : ℝ)⁻¹) = (harmonic B : ℝ) by
      rw [harmonic_eq_sum_Icc]; push_cast; rfl]
    exact_mod_cast harmonic_le_one_add_log B
  have hBle : (B : ℝ) ≤ 2 * R := by
    have : (B : ℝ) ≤ R + 1 := by rw [hB]; exact (Nat.ceil_lt_add_one hRpos.le).le
    linarith
  have hlogB_le : Real.log B ≤ Real.log 2 + Real.log R := by
    rw [← Real.log_mul (by norm_num) hRpos.ne']
    exact Real.log_le_log (by rw [hB]; exact_mod_cast Nat.ceil_pos.mpr hRpos) hBle
  have hHle2 : (∑ a ∈ Finset.Icc 1 B, (a : ℝ)⁻¹) ≤ 2 * Real.log R := by
    have hbnd : 1 + Real.log 2 ≤ Real.log R := by
      simpa using Real.log_le_log (Real.exp_pos _) hRexp
    linarith
  calc (#(Finset.permissibleSupport k (⌈R⌉₊ - 1) W) : ℝ)
      ≤ (B : ℝ) * (∑ a ∈ Finset.Icc 1 B, (a : ℝ)⁻¹) ^ k := hcardle
    _ ≤ (2 * R) * (2 * Real.log R) ^ k :=
        mul_le_mul hBle (pow_le_pow_left₀ hHnonneg hHle2 k) (by positivity) (by positivity)
    _ = 2 ^ (k + 1) * R * (Real.log R) ^ k := by rw [mul_pow]; ring

/-- Under the GPY/Maynard--Tao setup, and given the two cited external inputs (`hRho : |ρ| ≪ 1`
from `lem_S1_CRT` and `hLam : λ_max ≪_k y_max (log R) ^ k` from `lem_lambda_max_bound`), the
aggregate remainder over the support of `λ` obeys a three-step chain of bounds ending in
`C₃ y_max² R² (log R) ^ (4k)`. -/
@[pg_tag "bg246" "lem_S1_CRT_error_aggregate"]
theorem gpy_aggregate_remainder_bound (k : ℕ) (h : Fin k → ℤ) (θ δ : ℝ) (hδ : 0 < δ ∧ δ < θ / 2)
    (W v₀ : ℝ → ℕ) (lam : ℝ → (Fin k → ℕ) →₀ ℝ) (Ssupp : ℝ → Finset (Fin k → ℕ))
    (hSindex : ∀ N : ℝ, Ssupp N = Finset.permissibleSupport k (⌈Rcut θ δ N⌉₊ - 1) (W N))
    (Cρ : ℝ) (hCρ : 0 < Cρ)
    (hRho : ∀ᶠ N : ℝ in atTop, ∀ d ∈ Ssupp N, ∀ e ∈ Ssupp N,
      |rho N (W N) (v₀ N) h d e| ≤ Cρ)
    (Clam : ℝ) (hClam : 0 < Clam)
    (hLam : ∀ᶠ N : ℝ in atTop, (lam N).maxRealAbs ≤
        Clam * (PrimeGaps.lToY (lam N)).maxRealAbs * (Real.log (Rcut θ δ N)) ^ k) :
    ∃ C₂ > 0, ∃ C₃ > 0, ∀ᶠ N : ℝ in atTop,
      |aggregateRemainder N (W N) (v₀ N) h (lam N) (Ssupp N)| ≤ (lam N).maxRealAbs ^ 2 *
              aggregateAbsRemainder N (W N) (v₀ N) h (Ssupp N) ∧
      (lam N).maxRealAbs ^ 2 * aggregateAbsRemainder N (W N) (v₀ N) h (Ssupp N) ≤
          C₂ * (lam N).maxRealAbs ^ 2 * (Rcut θ δ N) ^ 2 * (Real.log (Rcut θ δ N)) ^ (2 * k) ∧
      C₂ * (lam N).maxRealAbs ^ 2 * (Rcut θ δ N) ^ 2 * (Real.log (Rcut θ δ N)) ^ (2 * k) ≤
          C₃ * ((PrimeGaps.lToY (lam N)).maxRealAbs) ^ 2 * (Rcut θ δ N) ^ 2 *
              (Real.log (Rcut θ δ N)) ^ (4 * k) := by
  obtain ⟨C, hCpos, hCcount⟩ := lem_support_count k
  refine ⟨Cρ * C ^ 2, by positivity, (Cρ * C ^ 2) * Clam ^ 2, by positivity, ?_⟩
  have hexp : 0 < θ / 2 - δ := by linarith [hδ.2]
  have htend : Filter.Tendsto (fun N : ℝ ↦ Rcut θ δ N) atTop atTop := by
    simpa [Rcut] using tendsto_rpow_atTop hexp
  have hcount' : ∀ᶠ N : ℝ in atTop, ∀ W : ℕ,
      (#(Finset.permissibleSupport k (⌈Rcut θ δ N⌉₊ - 1) W) : ℝ) ≤
        C * (Rcut θ δ N) * (Real.log (Rcut θ δ N)) ^ k := htend.eventually hCcount
  have hRpos : ∀ᶠ N : ℝ in atTop, 0 < Rcut θ δ N := htend.eventually_gt_atTop 0
  have hlog1 : ∀ᶠ N : ℝ in atTop, 1 ≤ Real.log (Rcut θ δ N) := by
    have : Filter.Tendsto (fun N : ℝ ↦ Real.log (Rcut θ δ N)) atTop atTop :=
      Real.tendsto_log_atTop.comp htend
    exact this.eventually_ge_atTop 1
  filter_upwards [hRho, hLam, hcount', hRpos, hlog1] with N hRhoN hLamN hcountN hRposN hlog1N
  set R := Rcut θ δ N
  set L := Real.log R
  set lm := (lam N).maxRealAbs
  set ym := (PrimeGaps.lToY (lam N)).maxRealAbs
  have hlm_nonneg : 0 ≤ lm := Finsupp.maxRealAbs_nonneg
  refine ⟨?_, ?_, ?_⟩
  · unfold aggregateRemainder aggregateAbsRemainder
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d _ ↦ ?_)
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e _ ↦ ?_)
    rw [abs_mul, abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    calc |lam N d| * |lam N e| ≤ lm * lm :=
          mul_le_mul Finsupp.le_maxRealAbs Finsupp.le_maxRealAbs (abs_nonneg _) hlm_nonneg
      _ = lm ^ 2 := by ring
  · have hcard : (#(Ssupp N) : ℝ) ≤ C * R * L ^ k := by
      rw [hSindex N]; exact hcountN (W N)
    have hStep : aggregateAbsRemainder N (W N) (v₀ N) h (Ssupp N) ≤
        Cρ * (#(Ssupp N) : ℝ) ^ 2 := by
      unfold aggregateAbsRemainder
      calc ∑ d ∈ Ssupp N, ∑ e ∈ Ssupp N, |rho N (W N) (v₀ N) h d e|
          ≤ ∑ d ∈ Ssupp N, ∑ e ∈ Ssupp N, Cρ :=
            Finset.sum_le_sum fun d hd ↦ Finset.sum_le_sum fun e he ↦ hRhoN d hd e he
        _ = Cρ * (#(Ssupp N) : ℝ) ^ 2 := by simp [Finset.sum_const, nsmul_eq_mul]; ring
    have hSq : (#(Ssupp N) : ℝ) ^ 2 ≤ C ^ 2 * R ^ 2 * L ^ (2 * k) :=
      calc (#(Ssupp N) : ℝ) ^ 2 ≤ (C * R * L ^ k) ^ 2 :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
        _ = C ^ 2 * R ^ 2 * L ^ (2 * k) := by rw [pow_mul]; ring
    calc lm ^ 2 * aggregateAbsRemainder N (W N) (v₀ N) h (Ssupp N)
        ≤ lm ^ 2 * (Cρ * (C ^ 2 * R ^ 2 * L ^ (2 * k))) :=
          mul_le_mul_of_nonneg_left (hStep.trans (mul_le_mul_of_nonneg_left hSq hCρ.le))
            (sq_nonneg _)
      _ = Cρ * C ^ 2 * lm ^ 2 * R ^ 2 * L ^ (2 * k) := by ring
  · have hlm_sq : lm ^ 2 ≤ Clam ^ 2 * ym ^ 2 * L ^ (2 * k) :=
      calc lm ^ 2 ≤ (Clam * ym * L ^ k) ^ 2 := pow_le_pow_left₀ hlm_nonneg hLamN 2
        _ = Clam ^ 2 * ym ^ 2 * L ^ (2 * k) := by rw [pow_mul]; ring
    calc Cρ * C ^ 2 * lm ^ 2 * R ^ 2 * L ^ (2 * k)
        = (Cρ * C ^ 2 * R ^ 2 * L ^ (2 * k)) * lm ^ 2 := by ring
      _ ≤ (Cρ * C ^ 2 * R ^ 2 * L ^ (2 * k)) * (Clam ^ 2 * ym ^ 2 * L ^ (2 * k)) :=
          mul_le_mul_of_nonneg_left hlm_sq (by positivity)
      _ = Cρ * C ^ 2 * Clam ^ 2 * ym ^ 2 * R ^ 2 * (L ^ (2 * k) * L ^ (2 * k)) := by ring
      _ = Cρ * C ^ 2 * Clam ^ 2 * ym ^ 2 * R ^ 2 * L ^ (4 * k) := by rw [← pow_add]; ring_nf

/-- "Logs beat powers": `(log x) ^ m / x ^ b → 0` as `x → ∞`, for any `b > 0`. -/
theorem tendsto_pow_log_div_rpow (m : ℕ) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun x : ℝ ↦ (Real.log x) ^ m / x ^ b) atTop (𝓝 0) := by
  have hbase : Tendsto (fun y : ℝ ↦ (Real.log y) ^ m / (1 * y + 0)) atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 m one_ne_zero
  simp only [one_mul, add_zero] at hbase
  have hcomp : Tendsto (fun x : ℝ ↦ (Real.log (x ^ b)) ^ m / (x ^ b)) atTop (𝓝 0) :=
    hbase.comp (tendsto_rpow_atTop hb)
  have key : Tendsto (fun x : ℝ ↦ b ^ m * ((Real.log x) ^ m / (x ^ b))) atTop (𝓝 0) :=
    hcomp.congr' <| by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [Real.log_rpow hx, mul_pow]
      ring
  have hinv : Tendsto (fun x : ℝ ↦ (b ^ m)⁻¹ * (b ^ m * ((Real.log x) ^ m / (x ^ b))))
      atTop (𝓝 0) := by simpa using key.const_mul ((b ^ m)⁻¹)
  exact hinv.congr fun x ↦ by field_simp

/-- Eventually `(log x) ^ m ≤ x ^ b` for `b > 0`. -/
theorem eventually_pow_log_le_rpow (m : ℕ) (b : ℝ) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, (Real.log x) ^ m ≤ x ^ b := by
  have h1 : ∀ᶠ x : ℝ in atTop, (Real.log x) ^ m / x ^ b < 1 := by
    simpa using (tendsto_pow_log_div_rpow m b hb).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [h1, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  rw [div_lt_one (Real.rpow_pos_of_pos hx0 b)] at hx
  exact hx.le

/-- Eventually `(log log N) ^ 2 ≤ log N`. -/
theorem eventually_loglog_sq_le_log :
    ∀ᶠ N : ℝ in atTop, (Real.log (Real.log N)) ^ 2 ≤ Real.log N := by
  have hbase : ∀ᶠ x : ℝ in atTop, (Real.log x) ^ 2 ≤ x := by
    filter_upwards [eventually_pow_log_le_rpow 2 1 (by norm_num)] with x hx
    simpa using hx
  exact Real.tendsto_log_atTop.eventually hbase

/-- Eventually `PrimeGaps.D₀ N ≤ log N` (using `log x ≤ x - 1` twice). -/
theorem eventually_D0_le_log : ∀ᶠ N : ℝ in atTop, PrimeGaps.D₀ N ≤ Real.log N := by
  have hv : ∀ᶠ N : ℝ in atTop, (1 : ℝ) ≤ Real.log (Real.log N) :=
    Real.tendsto_log_atTop.eventually (Real.tendsto_log_atTop.eventually_ge_atTop 1)
  filter_upwards [hv, Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with N hN hw
  have h1 : Real.log (Real.log (Real.log N)) ≤ Real.log (Real.log N) := by
    linarith [Real.log_le_sub_one_of_pos (lt_of_lt_of_le one_pos hN)]
  have h2 : Real.log (Real.log N) ≤ Real.log N := by
    linarith [Real.log_le_sub_one_of_pos (lt_of_lt_of_le one_pos hw)]
  exact h1.trans h2

/-- Strict positivity of `PrimeGaps.D₀ N` eventually: needs `log log N > 1`, whence
`PrimeGaps.D₀ N = log (log log N) > 0`. -/
theorem eventually_D0_pos : ∀ᶠ N : ℝ in atTop, (0 : ℝ) < PrimeGaps.D₀ N := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (Real.tendsto_log_atTop.eventually_gt_atTop 1)] with N hN
  simpa only [PrimeGaps.D₀] using Real.log_pos hN

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- Master reduction (the analytic heart): eventually
`R ^ 2 * (log R) ^ (3k) * W ^ (k + 1) * PrimeGaps.D₀ ≤ N`. -/
theorem eventually_master (k : ℕ) (θ δ : ℝ) (hθ1 : θ < 1) (hδ0 : 0 < δ) (hδ : δ < θ / 2) :
    ∀ᶠ N : ℕ in atTop, R ^ 2 * (Real.log R) ^ (3 * k) *
        (W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ N ≤ N := by
  set a : ℝ := θ - 2 * δ with ha
  have hc1 : θ / 2 - δ ≤ 1 := by linarith
  have hpoly := (eventually_pow_log_le_rpow (4 * k + 2) (1 - a) (by linarith)).natCast_atTop
  have hloglog : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ Real.log (Real.log N) :=
    (Real.tendsto_log_atTop.eventually
      (Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ))).natCast_atTop
  filter_upwards [hpoly, PrimeGaps.lem_W_size, eventually_loglog_sq_le_log.natCast_atTop,
    eventually_D0_le_log.natCast_atTop, (eventually_gt_atTop (1 : ℝ)).natCast_atTop,
    (Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)).natCast_atTop, hloglog]
    with N hpoly hW hloglogSq hD0 hN1 hlogN hloglog
  have hN0 : (0 : ℝ) < N := by linarith
  have hlogN0 : (0 : ℝ) ≤ Real.log N := by linarith
  have hR2 : ((N : ℝ) ^ (θ / 2 - δ)) ^ 2 = (N : ℝ) ^ a := by
    simp only [ha]
    rw [← Real.rpow_natCast ((N : ℝ) ^ (θ / 2 - δ)) 2, ← Real.rpow_mul (le_of_lt hN0)]
    congr 1
    push_cast; ring
  have hlogR : Real.log ((N : ℝ) ^ (θ / 2 - δ)) = (θ / 2 - δ) * Real.log N := Real.log_rpow hN0 _
  have hlogR_le : Real.log ((N : ℝ) ^ (θ / 2 - δ)) ≤ Real.log N := by
    rw [hlogR]
    nlinarith [hc1, hlogN0]
  have hD0nonneg : (0 : ℝ) ≤ PrimeGaps.D₀ N := Real.log_nonneg hloglog
  have hR2pos : (0 : ℝ) < (N : ℝ) ^ a := Real.rpow_pos_of_pos hN0 a
  have hlogR_nonneg : 0 ≤ Real.log ((N : ℝ) ^ (θ / 2 - δ)) := by rw [hlogR]; positivity
  have key : ((N : ℝ) ^ (θ / 2 - δ)) ^ 2 * (Real.log ((N : ℝ) ^ (θ / 2 - δ))) ^ (3 * k) *
        (W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ N ≤
      (N : ℝ) ^ a * (Real.log N) ^ (3 * k) * (Real.log N) ^ (k + 1) * (Real.log N) := by
    rw [hR2]
    gcongr
    exact hW.trans hloglogSq
  rw [show (N : ℝ) ^ a * (Real.log N) ^ (3 * k) * (Real.log N) ^ (k + 1) * (Real.log N) =
      (N : ℝ) ^ a * (Real.log N) ^ (4 * k + 2) by
    rw [show 4 * k + 2 = 3 * k + (k + 1) + 1 by ring, pow_succ, pow_add]; ring] at key
  refine key.trans ?_
  calc (N : ℝ) ^ a * (Real.log N) ^ (4 * k + 2) ≤ (N : ℝ) ^ a * (N : ℝ) ^ (1 - a) :=
        mul_le_mul_of_nonneg_left hpoly hR2pos.le
    _ = N := by rw [← Real.rpow_add hN0, show a + (1 - a) = (1 : ℝ) by ring, Real.rpow_one]

/-- Final arithmetic assembly: from the master reduction plus the positivity facts
`0 < PrimeGaps.D₀ N`, `0 < W`, `φ(W) ≥ 1` and `0 ≤ log R`, the per-`N` goal inequality holds with
`C = 1`. -/
theorem crt_assembly (k : ℕ) (θ δ ymax : ℝ) (N : ℝ) (W : ℕ) (hN0 : 0 ≤ N)
    (hmaster : (N ^ (θ / 2 - δ)) ^ 2 * (Real.log (N ^ (θ / 2 - δ))) ^ (3 * k) *
        (W : ℝ) ^ (k + 1) * PrimeGaps.D₀ N ≤ N)
    (hD0pos : (0 : ℝ) < PrimeGaps.D₀ N)
    (hWpos : (0 : ℝ) < (W : ℝ))
    (hphi : (1 : ℝ) ≤ (Nat.totient W : ℝ))
    (hlogR_nonneg : 0 ≤ Real.log (N ^ (θ / 2 - δ))) :
    ymax ^ 2 * (N ^ (θ / 2 - δ)) ^ 2 * (Real.log (N ^ (θ / 2 - δ))) ^ (4 * k) ≤
      1 * (ymax ^ 2 * (Nat.totient W : ℝ) ^ k * N * (Real.log (N ^ (θ / 2 - δ))) ^ k /
              ((W : ℝ) ^ (k + 1) * PrimeGaps.D₀ N)) := by
  rw [one_mul, le_div_iff₀ (by positivity : (0 : ℝ) < (W : ℝ) ^ (k + 1) * PrimeGaps.D₀ N),
    show (Real.log (N ^ (θ / 2 - δ))) ^ (4 * k) =
      (Real.log (N ^ (θ / 2 - δ))) ^ (3 * k) * (Real.log (N ^ (θ / 2 - δ))) ^ k by
    rw [← pow_add]; congr 1; ring]
  have hphik : (1 : ℝ) ≤ (Nat.totient W : ℝ) ^ k := one_le_pow₀ hphi
  have step1 := mul_le_mul_of_nonneg_left hmaster
    (by positivity : 0 ≤ ymax ^ 2 * (Real.log (N ^ (θ / 2 - δ))) ^ k)
  have step2 : ymax ^ 2 * (Real.log (N ^ (θ / 2 - δ))) ^ k * N ≤
      ymax ^ 2 * (Nat.totient W : ℝ) ^ k * N * (Real.log (N ^ (θ / 2 - δ))) ^ k := by
    nlinarith [mul_le_mul_of_nonneg_left hphik
      (by positivity : 0 ≤ ymax ^ 2 * N * (Real.log (N ^ (θ / 2 - δ))) ^ k)]
  nlinarith [step1, step2]

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- For every sufficiently large `N`,
`ymax² * R ^ 2 * (log R) ^ (4k) ≪_k ymax² * φ(W) ^ k * N * (log R) ^ k / (W ^ (k + 1) * D₀)`. -/
@[pg_tag "bg246" "lem_S1_CRT_error_negligible"]
theorem crt_error_negligible (k : ℕ) : ∃ C : ℝ, 0 < C ∧
      ∀ θ δ ymax : ℝ, 0 < θ → θ < 1 → 0 < δ → δ < θ / 2 → 0 ≤ ymax → ∀ᶠ N : ℕ in atTop,
          ymax ^ 2 * (R) ^ 2 * (Real.log (R)) ^ (4 * k) ≤
            C * (ymax ^ 2 * (Nat.totient (W N) : ℝ) ^ k * N * (Real.log (R)) ^ k /
                    ((W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ N)) := by
  refine ⟨1, one_pos, ?_⟩
  intro θ δ ymax hθ0 hθ1 hδ0 hδ hymax
  filter_upwards [eventually_master k θ δ hθ1 hδ0 hδ, eventually_D0_pos.natCast_atTop,
    (eventually_gt_atTop (1 : ℝ)).natCast_atTop] with N hmaster hD0pos hN1
  have hN0' : (0 : ℝ) < N := by linarith
  have hphi : (1 : ℝ) ≤ (Nat.totient (W N) : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr W_pos
  have hlogR_nonneg : 0 ≤ Real.log ((N : ℝ) ^ (θ / 2 - δ)) := by
    rw [Real.log_rpow hN0']
    have hlogNnn : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by linarith)
    have hcoef : (0 : ℝ) ≤ θ / 2 - δ := by linarith
    positivity
  exact crt_assembly k θ δ ymax N (W N) hN0'.le hmaster hD0pos
    (by exact_mod_cast W_pos) hphi hlogR_nonneg

end PrimeGaps
