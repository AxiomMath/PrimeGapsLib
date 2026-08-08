/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.ZMod.Units
public import PrimeGapsTheory.NumberTheory.BombieriVinogradov
public import PrimeGapsTheory.NumberTheory.PrimeCountingInterval

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Bombieri–Vinogradov in a dyadic window

Expresses the Bombieri–Vinogradov estimate for prime counts in a dyadic window.

## Main definitions

* `moduliRange`: The finite range of moduli in the dyadic estimate.
* `bvError`: The cumulative Bombieri–Vinogradov discrepancy at a real cutoff.

## Main results

* `bvError_eq_cumulative`: Identifies `bvError` with the supremum over unit residues of the
  cumulative prime-counting discrepancy.
* `lem_BV_restated`: Bounds the sum of dyadic prime-counting errors.
-/

@[expose] public section

open scoped ArithmeticFunction.Moebius BigOperators Finset

namespace PrimeGaps

/-- The moduli of the restated Bombieri--Vinogradov sum: `1 ≤ q ≤ N` with `q < N ^ (1/2 - ε)`. -/
noncomputable def moduliRange (N : ℕ) (ε : ℝ) : Finset ℕ :=
  {q ∈ Finset.Icc 1 N | (q : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 2 - ε)}

/-- The promoted interval error at lower endpoint `0`, adapted to the cumulative real cutoff and
with its built-in additive `1` removed. -/
noncomputable def bvError (X : ℝ) (q : ℕ) : ℝ := Nat.primeCountingIocError 0 ⌊X⌋₊ q - 1

/-- The prime count through `n` in residue class `a`, as a finite cardinality. -/
private theorem primeCountingZMod_eq_card (n q : ℕ) (a : ZMod q) :
    Real.primeCountingZMod (n : ℝ) q a =
      #((Finset.range (n + 1)).filter (fun m : ℕ ↦ m.Prime ∧ (↑m : ZMod q) = a)) := by
  simpa using Real.primeCountingZMod_eq_card_finset_range (n : ℝ) q a

/-- Counting primes in `(0,n]` is the cumulative prime count through `n`. -/
private theorem primeCountingIoc_zero (n : ℕ) : Nat.primeCountingIoc 0 n = Nat.primeCounting n := by
  simp [Nat.primeCountingIoc_eq_sub]

/-- Counting primes in a residue class in `(0,n]` is the cumulative class count through `n`. -/
private theorem primeCountingIocZMod_zero (n q : ℕ) (a : ZMod q) :
    ZMod.primeCountingIoc 0 n a = Real.primeCountingZMod (n : ℝ) q a := by
  rw [primeCountingZMod_eq_card]
  unfold ZMod.primeCountingIoc
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]
  exact ⟨fun ⟨⟨_, hple⟩, hp, ha⟩ ↦ ⟨by omega, hp, ha⟩,
    fun ⟨hplt, hp, ha⟩ ↦ ⟨⟨hp.pos, by omega⟩, hp, ha⟩⟩

/-- The interval adapter `bvError` is exactly the cumulative supremum used by the level-of-
distribution hypothesis. -/
theorem bvError_eq_cumulative (X : ℝ) (q : ℕ) : bvError X q = ⨆ a : (ZMod q)ˣ,
    |(Real.primeCountingZMod X q (a : ZMod q) : ℝ) -
        (pi X : ℝ) / (Nat.totient q : ℝ)| := by
  simp only [bvError, Nat.primeCountingIocError, primeCountingIoc_zero, primeCountingIocZMod_zero]
  rw [_root_.pi]
  simp only [Real.primeCountingZMod_eq_card_finset_range, Nat.floor_natCast]
  ring

/-- `bvError` is a supremum of absolute values, hence nonnegative. -/
theorem bvError_nonneg (X : ℝ) (q : ℕ) : (0 : ℝ) ≤ bvError X q := by
  rw [bvError_eq_cumulative]
  exact le_ciSup_of_le (Set.Finite.bddAbove (Set.finite_range _)) 1 (abs_nonneg _)

/-- `1 ≤ log X` for `X ≥ 3`, since `e < 3`. -/
private theorem one_le_log_of_three_le {X : ℝ} (hX : 3 ≤ X) : 1 ≤ Real.log X := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [Real.exp_one_lt_d9]

/-- Each individual cumulative discrepancy is bounded by `bvError`. -/
theorem bvError_term_le (X : ℝ) (q : ℕ) (u : (ZMod q)ˣ) :
    |(Real.primeCountingZMod X q (u : ZMod q) : ℝ) -
        (pi X : ℝ) / (Nat.totient q : ℝ)| ≤ bvError X q := by
  rw [bvError_eq_cumulative]
  exact le_ciSup (Set.Finite.bddAbove (Set.finite_range (fun a : (ZMod q)ˣ ↦
    |(Real.primeCountingZMod X q (a : ZMod q) : ℝ) - (pi X : ℝ) / (Nat.totient q : ℝ)|))) u

/-- Splitting `[0, 2N]` at `N`: the counts of a predicate over `[0, N]` and over `(N, 2N]` add. -/
private theorem card_filter_range_split (N : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    #((Finset.range (2 * N + 1)).filter P) =
      #((Finset.range (N + 1)).filter P) + #((Finset.Ioc N (2 * N)).filter P) := by
  have hdisj : Disjoint ((Finset.range (N + 1)).filter P) ((Finset.Ioc N (2 * N)).filter P) := by
    simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    omega
  have hsets : Finset.range (2 * N + 1) = Finset.range (N + 1) ∪ Finset.Ioc N (2 * N) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ioc]
    omega
  rw [hsets, Finset.filter_union, Finset.card_union_of_disjoint hdisj]

/-- The promoted window arithmetic-progression count is the difference of cumulative counts. -/
private theorem primeCountingIocZMod_diff (N q : ℕ) (a : ZMod q) :
    ZMod.primeCountingIoc N (2 * N) a + Real.primeCountingZMod (N : ℝ) q a =
      Real.primeCountingZMod (2 * N : ℕ) q a := by
  rw [primeCountingZMod_eq_card, primeCountingZMod_eq_card]
  unfold ZMod.primeCountingIoc
  have hsplit := card_filter_range_split N (fun n : ℕ ↦ n.Prime ∧ (↑n : ZMod q) = ↑a)
  omega

/-- Reduce the real cutoff `2N` to the natural-number cutoff. -/
private theorem real_primeCounting_2N (N : ℕ) : pi (2 * (N : ℝ)) = Nat.primeCounting (2 * N) := by
  rw [_root_.pi, show (2 : ℝ) * N = ((2 * N : ℕ) : ℝ) by norm_num, Nat.floor_natCast]

/-- Reduce the real cutoff `N` to the natural-number cutoff. -/
private theorem real_primeCounting_N (N : ℕ) : pi (N : ℝ) = Nat.primeCounting N := by
  rw [_root_.pi, Nat.floor_natCast]

/-- Reduce the real cutoff `2N` to the natural-number cutoff (ZMod version). -/
private theorem real_primeCountingZMod_2N (N q : ℕ) (b : ZMod q) :
    Real.primeCountingZMod (2 * (N : ℝ)) q b =
      Real.primeCountingZMod (2 * N : ℕ) q b := by
  rw [show (2 : ℝ) * N = ((2 * N : ℕ) : ℝ) by norm_num]

/-- Pointwise window-discrepancy bound for a unit residue. -/
private theorem windowDiscrepancy_le (N q : ℕ) (u : (ZMod q)ˣ) :
    |(ZMod.primeCountingIoc N (2 * N) (u : ZMod q) : ℝ) -
        (1 / (Nat.totient q : ℝ)) * (Nat.primeCountingIoc N (2 * N) : ℝ)| ≤
      bvError (2 * N : ℝ) q + bvError (N : ℝ) q := by
  have hprogR : (ZMod.primeCountingIoc N (2 * N) (u : ZMod q) : ℝ) =
      (Real.primeCountingZMod (2 * N : ℕ) q (u : ZMod q) : ℝ) -
        (Real.primeCountingZMod (N : ℕ) q (u : ZMod q) : ℝ) := by
    have := congrArg (fun n : ℕ ↦ (n : ℝ)) (primeCountingIocZMod_diff N q (u : ZMod q))
    norm_num at this ⊢
    linarith
  have hwindowR : (Nat.primeCountingIoc N (2 * N) : ℝ) =
      (Nat.primeCounting (2 * N) : ℝ) - (Nat.primeCounting N : ℝ) :=
    Nat.cast_primeCountingIoc (by omega)
  set φ : ℝ := (Nat.totient q : ℝ)
  have key : (ZMod.primeCountingIoc N (2 * N) (u : ZMod q) : ℝ) -
      (1 / φ) * (Nat.primeCountingIoc N (2 * N) : ℝ) =
      ((Real.primeCountingZMod (2 * N : ℕ) q (u : ZMod q) : ℝ) -
        (Nat.primeCounting (2 * N) : ℝ) / φ) -
      ((Real.primeCountingZMod (N : ℕ) q (u : ZMod q) : ℝ) -
        (Nat.primeCounting N : ℝ) / φ) := by
    rw [hprogR, hwindowR]; ring
  rw [key]
  refine le_trans (abs_sub _ _) ?_
  apply add_le_add
  · have h2 := bvError_term_le (2 * (N : ℝ)) q u
    rwa [real_primeCountingZMod_2N N q _, real_primeCounting_2N N] at h2
  · have h1 := bvError_term_le (N : ℝ) q u
    rwa [real_primeCounting_N N] at h1

/-- Since `μ(q)² ≤ 1`, the promoted weighted interval error is bounded by `1` plus the two
cumulative Bombieri–Vinogradov error terms at the window endpoints `2N` and `N`. -/
private theorem primeCountingIocError_le_bvError_sum (N q : ℕ) (hq : 1 ≤ q) :
    ((μ q : ℤ) : ℝ) ^ 2 * Nat.primeCountingIocError N (2 * N) q ≤
      1 + bvError (2 * N : ℝ) q + bvError (N : ℝ) q := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have hbdd := Nat.primeCountingIocError_bddAbove N (2 * N) q
  set B : ℝ := bvError (2 * N : ℝ) q + bvError (N : ℝ) q with hB
  have hsup : (⨆ a : (ZMod q)ˣ,
      |(ZMod.primeCountingIoc N (2 * N) (a : ZMod q) : ℝ) -
        (Nat.primeCountingIoc N (2 * N) : ℝ) / (Nat.totient q : ℝ)|) ≤ B := by
    refine ciSup_le fun a ↦ ?_
    rw [hB, ← one_div_mul_eq_div]
    exact windowDiscrepancy_le N q a
  have hsup0 : (0 : ℝ) ≤ (⨆ a : (ZMod q)ˣ,
      |(ZMod.primeCountingIoc N (2 * N) (a : ZMod q) : ℝ) -
        (Nat.primeCountingIoc N (2 * N) : ℝ) / (Nat.totient q : ℝ)|) :=
    le_ciSup_of_le hbdd 1 (abs_nonneg _)
  have hE0 : (0 : ℝ) ≤ Nat.primeCountingIocError N (2 * N) q :=
    Nat.primeCountingIocError_nonneg N (2 * N) q
  have hEle : Nat.primeCountingIocError N (2 * N) q ≤ 1 + B := by
    rw [Nat.primeCountingIocError]
    linarith
  have hmu1 : ((μ q : ℤ) : ℝ) ^ 2 ≤ 1 := by
    rw [← Int.cast_pow, ArithmeticFunction.moebius_sq]
    split_ifs <;> norm_num
  rw [hB] at hEle
  nlinarith [mul_le_mul_of_nonneg_right hmu1 hE0]

/-- A direct repackaging of `bombieriVinogradov_explicit`: assuming `BombieriVinogradov`, for
`θ < 1/2` and `A' ≥ 1` there is a constant `C₀ > 0` with, for all real `X ≥ 3`,
`∑_{q ∈ Finset.Icc 1 ⌊X^θ⌋₊} bvError X q ≤ C₀ * X / (Real.log X)^A'`.
-/
private theorem bvError_sum_bound (hBV : BombieriVinogradov)
    (θ : ℝ) (hθ : θ < 1 / 2) (A' : ℝ) (hA' : 1 ≤ A') :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ X : ℝ, 3 ≤ X →
      (∑ q ∈ Finset.Icc 1 ⌊X ^ θ⌋₊, bvError X q) ≤ C₀ * X / (Real.log X) ^ A' := by
  obtain ⟨C₀, hC₀, h⟩ := bombieriVinogradov_explicit hBV hθ hA'
  exact ⟨C₀, hC₀, fun X hX ↦ by simpa only [bvError_eq_cumulative] using h X hX⟩

/-- With `θ := 1/2 - ε/2`, every modulus in `moduliRange N ε` lies in the
Bombieri--Vinogradov range at cutoff `N`, once `N ≥ 1`. -/
private theorem moduliRange_subset_bvRange (ε : ℝ) (hε : 0 < ε) : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      moduliRange N ε ⊆ Finset.Icc 1 ⌊(N : ℝ) ^ (1 / 2 - ε / 2)⌋₊ := by
  refine ⟨1, fun N hN q hq ↦ ?_⟩
  have hbase : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [moduliRange, Finset.mem_filter, Finset.mem_Icc] at hq
  obtain ⟨⟨hq1, _⟩, hqlt⟩ := hq
  rw [Finset.mem_Icc]
  exact ⟨hq1, by
    rw [Nat.le_floor_iff (by positivity)]
    exact hqlt.le.trans (Real.rpow_le_rpow_of_exponent_le hbase (by linarith))⟩

/-- There is a positive constant bounding the modulus-cardinality term and the two cumulative
Bombieri–Vinogradov terms by `N / (log N) ^ A`.
-/
private theorem bv_tail_and_log_compare (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) (C₀ : ℝ)
    (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      ((#(moduliRange N ε) : ℝ) + C₀ * (2 * N : ℝ) / (Real.log (2 * N : ℝ)) ^ A +
        C₀ * (N : ℝ) / (Real.log (N : ℝ)) ^ A) ≤ C * (N : ℝ) / (Real.log N) ^ A := by
  obtain ⟨K₀, hK₀⟩ := ((isLittleO_log_rpow_rpow_atTop A (by linarith :
    (0 : ℝ) < 1 / 2 + ε)).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop).bddAbove_range
  set K : ℝ := max K₀ 1
  have hKpos : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hKbound : ∀ N : ℕ, 2 ≤ N → Real.log (N : ℝ) ^ A ≤ K * (N : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
    intro N hN
    have hxpos : (0 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 2 + ε) :=
      Real.rpow_pos_of_pos (Nat.cast_pos.2 (by omega)) _
    have hle : Real.log (N : ℝ) ^ A / (N : ℝ) ^ ((1 : ℝ) / 2 + ε) ≤ K :=
      le_trans (hK₀ ⟨N, rfl⟩) (le_max_left _ _)
    rwa [div_le_iff₀ hxpos] at hle
  refine ⟨K + 2 * C₀ + 2 ^ A * C₀, ?_, ?_⟩
  · have h2A : (0 : ℝ) < 2 ^ A := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  intro N hN
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hlogNA : 0 < (Real.log (N : ℝ)) ^ A := Real.rpow_pos_of_pos hlogN _
  have hcardA : (#(moduliRange N ε) : ℝ) ≤ K * (N : ℝ) / (Real.log N) ^ A := by
    have hxpos : (0 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - ε) := (Real.rpow_pos_of_pos hNpos _).le
    have hcard : (#(moduliRange N ε) : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - ε) := by
      have hsub : moduliRange N ε ⊆ Finset.Icc 1 ⌊(N : ℝ) ^ ((1 : ℝ) / 2 - ε)⌋₊ := by
        intro q hq
        rw [moduliRange, Finset.mem_filter, Finset.mem_Icc] at hq
        obtain ⟨⟨hq1, _⟩, hqlt⟩ := hq
        rw [Finset.mem_Icc]
        exact ⟨hq1, by rw [Nat.le_floor_iff hxpos]; exact le_of_lt hqlt⟩
      have hcardNat := Finset.card_le_card hsub
      rw [Nat.card_Icc, Nat.add_sub_cancel] at hcardNat
      exact (Nat.cast_le.2 hcardNat).trans (Nat.floor_le hxpos)
    rw [le_div_iff₀ hlogNA]
    have hstep : (#(moduliRange N ε) : ℝ) * (Real.log (N : ℝ)) ^ A ≤
        (N : ℝ) ^ ((1 : ℝ) / 2 - ε) * (K * (N : ℝ) ^ ((1 : ℝ) / 2 + ε)) :=
      mul_le_mul hcard (hKbound N hN) hlogNA.le hxpos
    rwa [show (N : ℝ) ^ ((1 : ℝ) / 2 - ε) * (K * (N : ℝ) ^ ((1 : ℝ) / 2 + ε)) =
        K * ((N : ℝ) ^ ((1 : ℝ) / 2 - ε) * (N : ℝ) ^ ((1 : ℝ) / 2 + ε)) by ring,
      ← Real.rpow_add hNpos, show (1 : ℝ) / 2 - ε + (1 / 2 + ε) = 1 by ring,
      Real.rpow_one] at hstep
  have htermB : C₀ * (2 * N : ℝ) / (Real.log (2 * N : ℝ)) ^ A ≤
      2 * C₀ * (N : ℝ) / (Real.log N) ^ A := by
    have hlogA : (Real.log (N : ℝ)) ^ A ≤ (Real.log (2 * N : ℝ)) ^ A :=
      Real.rpow_le_rpow hlogN.le (Real.log_le_log (by linarith) (by linarith)) hA.le
    rw [div_le_div_iff₀ (lt_of_lt_of_le hlogNA hlogA) hlogNA,
      show C₀ * (2 * N : ℝ) * (Real.log (N : ℝ)) ^ A =
        2 * C₀ * (N : ℝ) * (Real.log (N : ℝ)) ^ A by ring]
    exact mul_le_mul_of_nonneg_left hlogA (by positivity)
  have htermC : C₀ * (N : ℝ) / (Real.log (N : ℝ)) ^ A ≤
      2 ^ A * C₀ * (N : ℝ) / (Real.log N) ^ A := by
    calc C₀ * (N : ℝ) / (Real.log (N : ℝ)) ^ A = 1 * (C₀ * (N : ℝ) / (Real.log N) ^ A) := by ring
      _ ≤ 2 ^ A * (C₀ * (N : ℝ) / (Real.log N) ^ A) :=
        mul_le_mul_of_nonneg_right (Real.one_le_rpow (by norm_num) hA.le) (by positivity)
      _ = 2 ^ A * C₀ * (N : ℝ) / (Real.log N) ^ A := by ring
  calc (#(moduliRange N ε) : ℝ) + C₀ * (2 * N : ℝ) / (Real.log (2 * N : ℝ)) ^ A +
        C₀ * (N : ℝ) / (Real.log (N : ℝ)) ^ A ≤
      K * (N : ℝ) / (Real.log N) ^ A + 2 * C₀ * (N : ℝ) / (Real.log N) ^ A +
        2 ^ A * C₀ * (N : ℝ) / (Real.log N) ^ A := add_le_add (add_le_add hcardA htermB) htermC
    _ = (K + 2 * C₀ + 2 ^ A * C₀) * (N : ℝ) / (Real.log N) ^ A := by field_simp

/-- The `bvError` sum over `moduliRange N ε` at cutoff `X` inherits the Bombieri--Vinogradov
bound: the range is contained in `Icc 1 ⌊X ^ θ⌋₊`, the summands are nonnegative, and lowering
the exponent from `A'` to `A` only increases the right-hand side because `log X ≥ 1`. -/
private theorem bvError_moduliRange_sum_le {N : ℕ} {ε θ A A' C₀ X : ℝ} (hAA' : A ≤ A')
    (hC₀ : 0 < C₀)
    (hb : ∀ Y : ℝ, 3 ≤ Y → (∑ q ∈ Finset.Icc 1 ⌊Y ^ θ⌋₊, bvError Y q) ≤ C₀ * Y / (Real.log Y) ^ A')
    (hX : 3 ≤ X) (hsub : moduliRange N ε ⊆ Finset.Icc 1 ⌊X ^ θ⌋₊) :
    (∑ q ∈ moduliRange N ε, bvError X q) ≤ C₀ * X / (Real.log X) ^ A := by
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hlogX : (1 : ℝ) ≤ Real.log X := one_le_log_of_three_le hX
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun q _ _ ↦ bvError_nonneg _ _).trans
    ((hb X hX).trans (div_le_div_of_nonneg_left (by positivity)
      (Real.rpow_pos_of_pos (by linarith) _)
      (Real.rpow_le_rpow_of_exponent_le hlogX hAA')))

/-- **The large-`N` half of `lem_BV_restated`.**  Each weighted interval error is at most
`1 + bvError (2N) q + bvError N q`; summing over `moduliRange N ε` and applying the
Bombieri--Vinogradov bound at both window endpoints gives `C N / (log N) ^ A`. -/
private theorem bv_dyadic_sum_le {N : ℕ} {ε θ A A' C₀ C : ℝ} (hAA' : A ≤ A') (hC₀ : 0 < C₀)
    (hθ0 : 0 ≤ θ)
    (hb : ∀ Y : ℝ, 3 ≤ Y → (∑ q ∈ Finset.Icc 1 ⌊Y ^ θ⌋₊, bvError Y q) ≤ C₀ * Y / (Real.log Y) ^ A')
    (hN4 : 4 ≤ N) (hsubN : moduliRange N ε ⊆ Finset.Icc 1 ⌊(N : ℝ) ^ θ⌋₊)
    (hcollN : (#(moduliRange N ε) : ℝ) + C₀ * (2 * N : ℝ) / (Real.log (2 * N : ℝ)) ^ A +
        C₀ * (N : ℝ) / (Real.log (N : ℝ)) ^ A ≤ C * (N : ℝ) / (Real.log N) ^ A) :
    (∑ q ∈ moduliRange N ε,
        ((μ q : ℤ) : ℝ) ^ 2 * Nat.primeCountingIocError N (2 * N) q) ≤
      C * (N : ℝ) / (Real.log N) ^ A := by
  have hN4R : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN4
  have hstepA : (∑ q ∈ moduliRange N ε,
      ((μ q : ℤ) : ℝ) ^ 2 * Nat.primeCountingIocError N (2 * N) q) ≤
      ∑ q ∈ moduliRange N ε, (1 + bvError (2 * N : ℝ) q + bvError (N : ℝ) q) :=
    Finset.sum_le_sum fun q hq ↦ by
      rw [moduliRange, Finset.mem_filter, Finset.mem_Icc] at hq
      exact primeCountingIocError_le_bvError_sum N q hq.1.1
  have hsplit : (∑ q ∈ moduliRange N ε,
      (1 + bvError (2 * N : ℝ) q + bvError (N : ℝ) q)) = (#(moduliRange N ε) : ℝ) +
        (∑ q ∈ moduliRange N ε, bvError (2 * N : ℝ) q) +
        (∑ q ∈ moduliRange N ε, bvError (N : ℝ) q) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hS1 : (∑ q ∈ moduliRange N ε, bvError (N : ℝ) q) ≤ C₀ * (N : ℝ) / (Real.log (N : ℝ)) ^ A :=
    bvError_moduliRange_sum_le hAA' hC₀ hb (by linarith) hsubN
  have hS2 : (∑ q ∈ moduliRange N ε, bvError (2 * N : ℝ) q) ≤
      C₀ * (2 * N : ℝ) / (Real.log (2 * N : ℝ)) ^ A :=
    bvError_moduliRange_sum_le hAA' hC₀ hb (by linarith) (hsubN.trans
      (Finset.Icc_subset_Icc_right
        (Nat.floor_le_floor (Real.rpow_le_rpow (by linarith) (by linarith) hθ0))))
  calc (∑ q ∈ moduliRange N ε,
        ((μ q : ℤ) : ℝ) ^ 2 * Nat.primeCountingIocError N (2 * N) q) ≤
      (#(moduliRange N ε) : ℝ) + (∑ q ∈ moduliRange N ε, bvError (2 * N : ℝ) q) +
        (∑ q ∈ moduliRange N ε, bvError (N : ℝ) q) := by rwa [← hsplit]
    _ ≤ (#(moduliRange N ε) : ℝ) + C₀ * (2 * N : ℝ) / (Real.log (2 * N : ℝ)) ^ A +
        C₀ * (N : ℝ) / (Real.log (N : ℝ)) ^ A := add_le_add (add_le_add le_rfl hS2) hS1
    _ ≤ C * (N : ℝ) / (Real.log N) ^ A := hcollN

/-- Assuming `BombieriVinogradov`, for every fixed real `A > 0` and every fixed real
`ε ∈ (0, 1/2)`, there is a constant `C_{A,ε} > 0` such that for all positive integers `N`,
`∑_{1 ≤ q < N^(1/2 - ε)} μ(q)^2 · E(N, q) ≤ C · N / (log N)^A`.
-/
@[pg_tag "bg246" "lem_BV_restated"]
theorem lem_BV_restated : BombieriVinogradov → ∀ A : ℝ, 0 < A → ∀ ε : ℝ, 0 < ε → ε < (1 : ℝ) / 2 →
      ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → (∑ q ∈ moduliRange N ε,
            ((μ q : ℤ) : ℝ) ^ 2 * Nat.primeCountingIocError N (2 * N) q) ≤
          C * (N : ℝ) / (Real.log N) ^ A := by
  intro hBV A hA ε hε hε2
  set θ : ℝ := 1 / 2 - ε / 2 with hθdef
  have hθ : θ < 1 / 2 := by rw [hθdef]; linarith
  set A' : ℝ := max A 1 with hA'def
  have hA' : 1 ≤ A' := le_max_right _ _
  have hAA' : A ≤ A' := le_max_left _ _
  obtain ⟨C₀, hC₀, hb⟩ := bvError_sum_bound hBV θ hθ A' hA'
  obtain ⟨N₁, hsub⟩ := moduliRange_subset_bvRange ε hε
  set N₂ : ℕ := max N₁ 4 with hN₂def
  obtain ⟨C, hC, hcoll⟩ := bv_tail_and_log_compare A ε hA hε C₀ hC₀
  set s : ℕ → ℝ := fun N ↦ (∑ q ∈ moduliRange N ε,
      ((μ q : ℤ) : ℝ) ^ 2 * Nat.primeCountingIocError N (2 * N) q)
    with hsdef
  have hmain : ∀ N : ℕ, N₂ ≤ N → s N ≤ C * (N : ℝ) / (Real.log N) ^ A := by
    intro N hN
    have hN4 : 4 ≤ N := le_trans (le_max_right N₁ 4) hN
    have hN2 : 2 ≤ N := by omega
    have hN1le : N₁ ≤ N := le_trans (le_max_left N₁ 4) hN
    exact bv_dyadic_sum_le hAA' hC₀ (by rw [hθdef]; linarith) hb hN4 (hsub N hN1le) (hcoll N hN2)
  have hrange_ne : (Finset.range N₂).Nonempty := by
    rw [Finset.nonempty_range_iff]; omega
  set g : ℕ → ℝ := fun n ↦ s n * (Real.log n) ^ A / n with hgdef
  set Cbig : ℝ := max C ((Finset.range N₂).sup' hrange_ne g) with hCbigdef
  have hCbig : C ≤ Cbig := le_max_left _ _
  refine ⟨Cbig, lt_of_lt_of_le hC hCbig, ?_⟩
  intro N hNpos
  change s N ≤ Cbig * (N : ℝ) / (Real.log N) ^ A
  rcases Nat.lt_or_ge N N₂ with hlt | hge
  · rcases Nat.lt_or_ge N 2 with hN1 | hN2
    · have hNe : N = 1 := by omega
      subst hNe
      have hempty : moduliRange 1 ε = ∅ := by
        rw [moduliRange]
        refine Finset.filter_false_of_mem fun q hq ↦ ?_
        rw [Finset.mem_Icc] at hq
        obtain rfl : q = 1 := by omega
        norm_num
      have hs1 : s 1 = 0 := by simp [hsdef, hempty]
      rw [hs1, Nat.cast_one, Real.log_one, Real.zero_rpow hA.ne']
      simp
    · have hgle : g N ≤ Cbig :=
        le_trans (Finset.le_sup' g (Finset.mem_range.2 hlt)) (le_max_right C _)
      have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
      have hlogNA : 0 < (Real.log (N : ℝ)) ^ A := Real.rpow_pos_of_pos hlogN _
      have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
      have hsN : s N = g N * (N : ℝ) / (Real.log N) ^ A := by
        rw [hgdef]
        field_simp
      rw [hsN]
      gcongr
  · have hN4 : 4 ≤ N := le_trans (le_max_right N₁ 4) hge
    have hlogNA : 0 < (Real.log (N : ℝ)) ^ A :=
      Real.rpow_pos_of_pos (Real.log_pos (by exact_mod_cast (by omega : 1 < N))) _
    exact (hmain N hge).trans (by gcongr)

end PrimeGaps
