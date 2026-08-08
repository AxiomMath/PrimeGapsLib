/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Int.Star
public import PrimeGapsTheory.Sieve.CRT
public import PrimeGapsTheory.Sieve.Common.PrimeWindow

import PrimeGapsTheory.Tactic.PaperTag

/-!
# CRT reduction of the second-moment sieve count

A Chinese remainder theorem reduction of the second-moment sieve count to a prime-counting main
term and error.

## Main definitions

* `PrimeGaps.sieveCount`: the second-moment sieve count.
* `PrimeGaps.piShift`: the count of primes in a shifted window lying in a fixed residue class.

## Main results

* `PrimeGaps.crt_construct`: the sieve congruence system collapses to a single congruence.
* `PrimeGaps.lem_S2m_CRT`: bounds the difference between the sieve count and its prime-counting
  main term.
-/

open Int Nat

@[expose] public section

namespace PrimeGaps

open Finset

/-- The sieve count
`sieveCount := ∑_{N < n ≤ 2N, n ≡ v0 (mod W), [d_i,e_i] | n + h_i ∀ i} χ_P(n + h_m)`. -/
noncomputable def sieveCount {k : ℕ} (h : Fin k → ℤ) (m : Fin k)
    (W : ℕ) (v0 : ℤ) (d e : Fin k → ℕ) (N : ℕ) : ℝ :=
  ∑ n ∈ {n ∈ window N |
      n ≡ v0 [ZMOD (W : ℤ)] ∧ ∀ i : Fin k, ((Nat.lcm (d i) (e i) : ℤ)) ∣ (n + h i)},
    chiP (n + h m)

/-- For `a₀` coprime to `q ≥ 1`, the count of primes in `(N, 2N]` congruent to `a₀ (mod q)` differs
from `π(N, 2N] / φ(q)` by at most `primeCountingIocError N (2N) q - 1`. -/
theorem iSup_bound (N q : ℕ) (hq : 1 ≤ q) (a₀ : ℤ) (ha₀ : Int.gcd a₀ (q : ℤ) = 1) :
    |(ZMod.primeCountingIoc N (2 * N) (a₀ : ZMod q) : ℝ) -
        (primeCountingIoc N (2 * N) : ℝ) / (Nat.totient q)| ≤
      primeCountingIocError N (2 * N) q - 1 := by
  haveI : NeZero q := ⟨by omega⟩
  obtain ⟨u, hu⟩ := isUnit_intCast_of_gcd_eq_one ha₀
  rw [← hu]
  exact abs_sub_div_le_primeCountingIocError_sub_one N (2 * N) q u

/-- For pairwise coprime admissible moduli, the sieve congruence system on `p` collapses by the
Chinese remainder theorem to a single `p ≡ a₀ [ZMOD q]` with `a₀` coprime to `q`. -/
theorem crt_construct {k : ℕ} (h : Fin k → ℤ) (m : Fin k) (W : ℕ) (v0 : ℤ) (d e : Fin k → ℕ) (q : ℕ)
    (hdm : d m = 1) (hem : e m = 1)
    (hcopW : ∀ i, Nat.Coprime W (Nat.lcm (d i) (e i)))
    (hcopL : ∀ i j, i ≠ j → Nat.Coprime (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j)))
    (hq : q = W * ∏ i, Nat.lcm (d i) (e i))
    (hv0 : ∀ i, Int.gcd (v0 + h i) (W : ℤ) = 1)
    (hsupp : ∀ i, i ≠ m → Int.gcd (h m - h i) ((Nat.lcm (d i) (e i) : ℤ)) = 1) :
    ∃ a₀ : ℤ, Int.gcd a₀ (q : ℤ) = 1 ∧ ∀ p : ℤ, (p ≡ v0 + h m [ZMOD (W : ℤ)] ∧
          ∀ i, ((Nat.lcm (d i) (e i) : ℤ)) ∣ (p - (h m - h i))) ↔ p ≡ a₀ [ZMOD (q : ℤ)] := by
  classical
  set L : Fin k → ℕ := fun i ↦ Nat.lcm (d i) (e i) with hL
  set P : ℕ := ∏ i, L i with hP
  have hMcop : ∀ i ∈ (univ : Finset (Fin k)), ∀ j ∈ (univ : Finset (Fin k)), i ≠ j →
      IsCoprime ((L i : ℤ)) ((L j : ℤ)) := by
    intro i _ j _ hij
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd, hL] using hcopL i j hij
  obtain ⟨x, hx⟩ := crt_equiv (univ : Finset (Fin k)) (fun i ↦ (L i : ℤ)) (fun i ↦ h m - h i) hMcop
  have hprodcast : (∏ i, (L i : ℤ)) = (P : ℤ) := by rw [hP]; push_cast; rfl
  have hWP : Nat.Coprime W P := by rw [hP]; exact Nat.Coprime.prod_right fun i _ ↦ hcopW i
  have hWPcop : IsCoprime ((W : ℤ)) ((P : ℤ)) := by
    rw [Int.isCoprime_iff_gcd_eq_one]; simpa [Int.gcd] using hWP
  obtain ⟨a₀, ha1, ha2⟩ := crt2 (W : ℤ) (P : ℤ) hWPcop (v0 + h m) x
  have ha₀L : ∀ i, a₀ ≡ (h m - h i) [ZMOD (L i : ℤ)] := fun i ↦
    (hx a₀).mpr (by rw [hprodcast]; exact ha2) i (mem_univ i)
  refine ⟨a₀, ?_, ?_⟩
  · have key : IsCoprime a₀ ((W : ℤ) * (P : ℤ)) := by
      rw [IsCoprime.mul_right_iff]
      refine ⟨coprime_of_modEq ha1 (Int.isCoprime_iff_gcd_eq_one.mpr (hv0 m)), ?_⟩
      rw [hP, Nat.cast_prod]
      refine IsCoprime.prod_right fun i _ ↦ coprime_of_modEq (ha₀L i) ?_
      by_cases hi : i = m
      · have hLm : L i = 1 := by rw [hi]; simp [hL, hdm, hem, Nat.lcm]
        rw [hLm]; exact isCoprime_one_right
      · rw [Int.isCoprime_iff_gcd_eq_one]; exact hsupp i hi
    rw [hq]; push_cast
    rwa [Int.isCoprime_iff_gcd_eq_one] at key
  · intro p
    constructor
    · rintro ⟨hpW, hpL⟩
      have e1 : p ≡ a₀ [ZMOD (W : ℤ)] := hpW.trans ha1.symm
      have hpLmod : ∀ i ∈ (univ : Finset (Fin k)), p ≡ (h m - h i) [ZMOD (L i : ℤ)] := by
        intro i _
        rw [Int.modEq_iff_dvd]
        have hd := hpL i
        rwa [← dvd_neg, neg_sub] at hd
      have hpP : p ≡ x [ZMOD (∏ i, (L i : ℤ))] := (hx p).mp hpLmod
      rw [hprodcast] at hpP
      have e2 : p ≡ a₀ [ZMOD (P : ℤ)] := hpP.trans ha2.symm
      rw [hq]; push_cast
      exact (crt2_equiv (W : ℤ) (P : ℤ) hWPcop a₀ p).mp ⟨e1, e2⟩
    · intro hpq
      rw [hq] at hpq; push_cast at hpq
      obtain ⟨e1, e2⟩ := (crt2_equiv (W : ℤ) (P : ℤ) hWPcop a₀ p).mpr hpq
      refine ⟨e1.trans ha1, fun i ↦ ?_⟩
      have e2' : p ≡ x [ZMOD (∏ i, (L i : ℤ))] := by rw [hprodcast]; exact e2.trans ha2
      have hh := (hx p).mpr e2' i (mem_univ i)
      rw [Int.modEq_iff_dvd] at hh
      rwa [← neg_sub, dvd_neg] at hh

/-- Count of primes in the shifted window `(N + s, 2N + s]` lying in the residue class `a (mod q)`.
With `s = h m`, this is the quantity that `sieveCount` equals after the change of variables
`p = n + h_m`. -/
noncomputable def piShift (N : ℕ) (q : ℕ) (a : ℤ) (s : ℤ) : ℝ :=
  ∑ p ∈ {p ∈ Finset.Ioc ((N : ℤ) + s) (2 * (N : ℤ) + s) | p ≡ a [ZMOD (q : ℤ)]}, chiP p

/-- The change of variables `p = n + h m` identifies `sieveCount h m W v0 d e N` with
`piShift N q a₀ (h m)`. -/
theorem sieveCount_eq_piShift {k : ℕ} (h : Fin k → ℤ) (m : Fin k)
    (W : ℕ) (v0 : ℤ) (d e : Fin k → ℕ) (q : ℕ) (N : ℕ) (a₀ : ℤ)
    (hmem : ∀ p : ℤ, (p ≡ v0 + h m [ZMOD (W : ℤ)] ∧
        ∀ i, ((Nat.lcm (d i) (e i) : ℤ)) ∣ (p - (h m - h i))) ↔ p ≡ a₀ [ZMOD (q : ℤ)]) :
    sieveCount h m W v0 d e N = piShift N q a₀ (h m) := by
  unfold sieveCount piShift window
  apply Finset.sum_nbij' (i := fun n ↦ n + h m) (j := fun p ↦ p - h m)
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
    obtain ⟨⟨hn1, hn2⟩, hpred⟩ := hn
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [← hmem]
    exact ⟨hpred.1.add_right (h m), fun i ↦ by
      have := hpred.2 i
      rwa [(by ring : n + h m - (h m - h i) = n + h i)]⟩
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
    obtain ⟨⟨hp1, hp2⟩, hpred⟩ := hp
    rw [← hmem] at hpred
    refine ⟨⟨by omega, by omega⟩, by simpa using hpred.1.sub_right (h m), fun i ↦ ?_⟩
    have := hpred.2 i
    rwa [(by ring : p - (h m - h i) = (p - h m) + h i)] at this
  · intro n _
    simp
  · intro p _
    simp
  · intro n _
    simp

/-- Shifting the window by `s` changes the count in a fixed class mod `q` by at most `2|s|`. -/
theorem piShift_sub_zmodCount_le (N q : ℕ) (a s : ℤ) :
    |piShift N q a s - (ZMod.primeCountingIoc N (2 * N) (a : ZMod q) : ℝ)| ≤ 2 * |s| := by
  rw [← windowFilterSum_eq_zmodCount N q a]
  set P : ℤ → Prop := fun n ↦ n ≡ a [ZMOD (q : ℤ)] with hP
  set A : Finset ℤ := Finset.Ioc ((N : ℤ) + s) (2 * (N : ℤ) + s) with hA
  set B : Finset ℤ := window N with hB
  have hpiS : piShift N q a s = ∑ p ∈ A.filter P, chiP p := rfl
  rw [hpiS]
  set A' : Finset ℤ := A.filter P with hA'
  set B' : Finset ℤ := B.filter P with hB'
  have hdecompA : ∑ p ∈ A', chiP p = ∑ p ∈ A' ∩ B', chiP p + ∑ p ∈ A' \ B', chiP p :=
    (Finset.sum_inter_add_sum_sdiff _ _ _).symm
  have hdecompB : ∑ n ∈ B', chiP n = ∑ n ∈ B' ∩ A', chiP n + ∑ n ∈ B' \ A', chiP n :=
    (Finset.sum_inter_add_sum_sdiff _ _ _).symm
  have hinter : ∑ p ∈ A' ∩ B', chiP p = ∑ n ∈ B' ∩ A', chiP n := by rw [Finset.inter_comm]
  have hsub : ∑ p ∈ A', chiP p - ∑ n ∈ B', chiP n =
      ∑ p ∈ A' \ B', chiP p - ∑ n ∈ B' \ A', chiP n := by
    rw [hdecompA, hdecompB, hinter]; ring
  rw [hsub]
  have h1 : 0 ≤ ∑ p ∈ A' \ B', chiP p := Finset.sum_nonneg fun n _ ↦ chiP_nonneg n
  have h2 : 0 ≤ ∑ n ∈ B' \ A', chiP n := Finset.sum_nonneg fun n _ ↦ chiP_nonneg n
  have htri : |∑ p ∈ A' \ B', chiP p - ∑ n ∈ B' \ A', chiP n| ≤
      ∑ p ∈ A' \ B', chiP p + ∑ n ∈ B' \ A', chiP n := by
    rw [abs_le]; constructor <;> linarith
  refine htri.trans ?_
  have hcard : ∑ p ∈ A' \ B', chiP p + ∑ n ∈ B' \ A', chiP n ≤
      (#(A \ B) : ℝ) + (#(B \ A) : ℝ) := by
    have hcardA : ∑ p ∈ A' \ B', chiP p ≤ (#(A \ B) : ℝ) :=
      calc ∑ p ∈ A' \ B', chiP p
          ≤ ∑ p ∈ A' \ B', (1 : ℝ) := Finset.sum_le_sum fun n _ ↦ chiP_le_one n
        _ = (#(A' \ B') : ℝ) := by simp
        _ ≤ (#(A \ B) : ℝ) := by
            refine Nat.cast_le.mpr (Finset.card_le_card fun x hx ↦ ?_)
            simp only [hA', hB', Finset.mem_sdiff, Finset.mem_filter] at hx
            simpa only [Finset.mem_sdiff] using ⟨hx.1.1, fun hxB ↦ hx.2 ⟨hxB, hx.1.2⟩⟩
    have hcardB : ∑ n ∈ B' \ A', chiP n ≤ (#(B \ A) : ℝ) :=
      calc ∑ n ∈ B' \ A', chiP n
          ≤ ∑ n ∈ B' \ A', (1 : ℝ) := Finset.sum_le_sum fun n _ ↦ chiP_le_one n
        _ = (#(B' \ A') : ℝ) := by simp
        _ ≤ (#(B \ A) : ℝ) := by
            refine Nat.cast_le.mpr (Finset.card_le_card fun x hx ↦ ?_)
            simp only [hA', hB', Finset.mem_sdiff, Finset.mem_filter] at hx
            simpa only [Finset.mem_sdiff] using ⟨hx.1.1, fun hxA ↦ hx.2 ⟨hxA, hx.1.2⟩⟩
    exact add_le_add hcardA hcardB
  refine hcard.trans ?_
  have key : #(A \ B) + #(B \ A) ≤ 2 * s.natAbs := by
    have hAB : A \ B ⊆ Finset.Ioc (2 * (N : ℤ)) (2 * (N : ℤ) + s) ∪
        Finset.Ioc ((N : ℤ) + s) (N : ℤ) := by
      intro x hx
      rw [hA, hB, window] at hx
      simp only [Finset.mem_sdiff, Finset.mem_Ioc] at hx
      simp only [Finset.mem_union, Finset.mem_Ioc]
      omega
    have hBA : B \ A ⊆ Finset.Ioc (2 * (N : ℤ) + s) (2 * (N : ℤ)) ∪
        Finset.Ioc (N : ℤ) ((N : ℤ) + s) := by
      intro x hx
      rw [hA, hB, window] at hx
      simp only [Finset.mem_sdiff, Finset.mem_Ioc] at hx
      simp only [Finset.mem_union, Finset.mem_Ioc]
      omega
    have cAB := (Finset.card_le_card hAB).trans (Finset.card_union_le _ _)
    have cBA := (Finset.card_le_card hBA).trans (Finset.card_union_le _ _)
    rw [Int.card_Ioc, Int.card_Ioc] at cAB
    rw [Int.card_Ioc, Int.card_Ioc] at cBA
    omega
  calc (#(A \ B) : ℝ) + (#(B \ A) : ℝ)
      = ((#(A \ B) + #(B \ A) : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((2 * s.natAbs : ℕ) : ℝ) := by exact_mod_cast key
    _ = 2 * |s| := by push_cast [Nat.cast_natAbs]; ring

/-- With the fixed admissible-tuple data `k ≥ 1`, shifts `h: Fin k → ℤ`, distinguished index `m`,
there is an absolute constant `C > 0` (depending only on `k`, `h`, `m` ) such that for every
choice of `W ≥ 1`, residue `v0`, Selberg-sieve indices `d, e` (`≥ 1`) and modulus
`q = W · ∏_i [d_i, e_i]` (`q: ℕ`), and every length parameter `N: ℕ`, under the hypotheses 1.
`d_m = e_m = 1`; 2. the `k+1` moduli `W, [d_1,e_1], …, [d_k,e_k]` are pairwise coprime; 3.
`q = W · ∏_i [d_i, e_i]`; 4. `gcd(v0 + h_i, W) = 1` for every `i`; 5.
`gcd(h_m - h_i, [d_i, e_i]) = 1` for every `i ≠ m`; we have
`| sieveCount - X_N / φ(q) | ≤ C · E(N, q)`, i.e. `sieveCount = X_N/φ(q) + O(E(N,q))` with the
implied constant absolute (independent of `N`, `q`, `W`, `d_i`, `e_i` ). -/
@[pg_tag "bg246" "lem_S2m_CRT"]
theorem lem_S2m_CRT {k : ℕ} (h : Fin k → ℤ) (m : Fin k) : ∃ C : ℝ, 0 < C ∧
      ∀ (W : ℕ) (v0 : ℤ) (d e : Fin k → ℕ) (q : ℕ) (N : ℕ), 1 ≤ W →
        (∀ i, 1 ≤ d i) → (∀ i, 1 ≤ e i) →
        d m = 1 → e m = 1 →
        (∀ i, Nat.Coprime W (Nat.lcm (d i) (e i))) →
        (∀ i j, i ≠ j → Nat.Coprime (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))) →
        q = W * ∏ i, Nat.lcm (d i) (e i) →
        (∀ i, Int.gcd (v0 + h i) (W : ℤ) = 1) →
        (∀ i, i ≠ m → Int.gcd (h m - h i) ((Nat.lcm (d i) (e i) : ℤ)) = 1) →
        |sieveCount h m W v0 d e N - (primeCountingIoc N (2 * N) : ℝ) / (Nat.totient q)| ≤
          C * primeCountingIocError N (2 * N) q := by
  refine ⟨1 + 2 * |h m|, by positivity, ?_⟩
  intro W v0 d e q N hW hd he hdm hem hcopW hcopL hq hv0 hsupp
  have hq1 : 1 ≤ q := by
    have hP : 1 ≤ ∏ i, Nat.lcm (d i) (e i) := Finset.one_le_prod' fun i _ ↦
      Nat.one_le_iff_ne_zero.mpr (Nat.lcm_ne_zero (Nat.one_le_iff_ne_zero.mp (hd i))
        (Nat.one_le_iff_ne_zero.mp (he i)))
    rw [hq]
    simpa using Nat.mul_le_mul hW hP
  obtain ⟨a₀, ha₀cop, hmem⟩ := crt_construct h m W v0 d e q hdm hem hcopW hcopL hq hv0 hsupp
  have hbnd : |piShift N q a₀ (h m) - (ZMod.primeCountingIoc N (2 * N) (a₀ : ZMod q) : ℝ)| ≤
      2 * |h m| :=
    piShift_sub_zmodCount_le N q a₀ (h m)
  have hmain : |(ZMod.primeCountingIoc N (2 * N) (a₀ : ZMod q) : ℝ) -
      (primeCountingIoc N (2 * N) : ℝ) / (Nat.totient q)| ≤ primeCountingIocError N (2 * N) q - 1 :=
    iSup_bound N q hq1 a₀ ha₀cop
  have hE1 : (1 : ℝ) ≤ primeCountingIocError N (2 * N) q := one_le_primeCountingIocError N (2 * N) q
  rw [sieveCount_eq_piShift h m W v0 d e q N a₀ hmem]
  calc |piShift N q a₀ (h m) - (primeCountingIoc N (2 * N) : ℝ) / (Nat.totient q)|
      ≤ |piShift N q a₀ (h m) - (ZMod.primeCountingIoc N (2 * N) (a₀ : ZMod q) : ℝ)| +
          |(ZMod.primeCountingIoc N (2 * N) (a₀ : ZMod q) : ℝ) -
              (primeCountingIoc N (2 * N) : ℝ) / (Nat.totient q)| := abs_sub_le _ _ _
    _ ≤ 2 * |h m| + (primeCountingIocError N (2 * N) q - 1) := add_le_add hbnd hmain
    _ ≤ (1 + 2 * |h m|) * primeCountingIocError N (2 * N) q := by
        have hnn : (0 : ℝ) ≤ 2 * |h m| := by positivity
        nlinarith [hnn, hE1, mul_nonneg hnn (zero_le_one.trans hE1)]

end PrimeGaps
