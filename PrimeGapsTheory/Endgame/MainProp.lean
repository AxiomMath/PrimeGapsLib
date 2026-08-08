/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.S1.Smoothing
public import PrimeGapsTheory.Sieve.S2m.Smooth

import PrimeGapsTheory.Tactic.PaperTag

/-!
# The main sieve asymptotic and positivity estimate

Asymptotic formulas for the first and second sieve moments and positivity of their difference.
The first moment is transferred from the `GPYSieveS1` formulation via `S1_eq_gpy`, and the
second moment is assembled from the marginal estimates `lem_S2m_smooth`.

## Main results

* `prop_main_prop`: Simultaneous asymptotic estimates for the first and second sieve moments.
* `lem_S_asymptotic`: The asymptotic formula for the combined sieve sum.
* `lem_S_positive`: The combined sieve sum is eventually positive.
-/

@[expose] public section

open Real

open scoped Topology
open MeasureTheory Filter EuclideanSpace
open scoped PrimeGaps BigOperators

namespace PrimeGaps.MainProp

open scoped PrimeGaps.sieveModulus in
local instance instNeZeroW_bridge (N : ℕ) : NeZero (W N) := ⟨PrimeGaps.W_pos.ne'⟩

/-- `PrimeGaps.weight h l n = GPYSieveS1.wVal h l n` whenever `n + h i ≠ 0` for every `i`. -/
theorem weight_eq_wVal {k : ℕ} (h : Fin k → ℕ) (l : (Fin k → ℕ) → ℝ) (n : ℕ)
    (hn : ∀ i, n + h i ≠ 0) :
    PrimeGaps.weight h l n = GPYSieveS1.wVal h l (n : ℤ) := by
  classical
  unfold PrimeGaps.weight GPYSieveS1.wVal GPYSieveS1.innerDivSum
  have hcond : ∀ d : Fin k → ℕ, ((∀ i, 1 ≤ d i) ∧ (∀ i, (d i : ℤ) ∣ ((n : ℤ) + h i))) ↔
      d ∈ Fintype.piFinset fun i ↦ (n + h i).divisors := fun d ↦ by
    rw [Fintype.mem_piFinset]
    exact ⟨fun ⟨_, hdvd⟩ i ↦ Nat.mem_divisors.mpr ⟨by exact_mod_cast hdvd i, hn i⟩,
      fun hd ↦ ⟨fun i ↦ Nat.pos_of_mem_divisors (hd i),
        fun i ↦ by exact_mod_cast (Nat.mem_divisors.mp (hd i)).1⟩⟩
  congr 1
  rw [tsum_eq_sum (s := Fintype.piFinset fun i ↦ (n + h i).divisors)]
  · exact Finset.sum_congr rfl fun d hd ↦ by rw [if_pos ((hcond d).mpr hd)]
  · exact fun d hd ↦ by rw [if_neg fun hc ↦ hd ((hcond d).mp hc)]

/-- Residue correspondence between the GPY integer-mod filter and the `ZMod` condition. -/
theorem res_iff {W : ℕ} [NeZero W] (w₀ : ZMod W) (n : ℕ) :
    ((n : ℤ) % (W : ℤ) = (w₀.val : ℤ) % (W : ℤ)) ↔ ((n : ZMod W) = w₀) := by
  rw [← Int.natCast_mod, ← Int.natCast_mod, Nat.cast_inj]
  conv_rhs => rw [← ZMod.natCast_zmod_val w₀]
  rw [ZMod.natCast_eq_natCast_iff']

open scoped PrimeGaps.sieveModulus in
/-- `PrimeGaps.S₁ h l N w₀ = GPYSieveS1.S1 h l N (W N) w₀.val`. -/
theorem S1_eq_gpy {k : ℕ} (h : Fin k → ℕ) (l : (Fin k → ℕ) → ℝ) (N : ℕ) (w₀ : ZMod (W N)) :
    PrimeGaps.S₁ h l N w₀ = GPYSieveS1.S1 h l (N : ℝ) (W N) w₀.val := by
  classical
  set T : ℕ → ℝ := fun n ↦ if ((n : ℕ) : ZMod (W N)) = w₀
    then PrimeGaps.weight h l n else 0 with hT
  have hlhs : PrimeGaps.S₁ h l N w₀ = ∑ n ∈ Finset.Ioc N (2 * N), T n := by
    rw [PrimeGaps.S₁, Finset.sum_filter]
  have hfloor2 : ⌊(2 : ℝ) * (N : ℝ)⌋ = ((2 * N : ℕ) : ℤ) := by
    rw [show (2 : ℝ) * (N : ℝ) = ((2 * N : ℕ) : ℝ) by push_cast; ring, Int.floor_natCast]
  have hmapset : (Finset.Ioc (N : ℤ) ((2 * N : ℕ) : ℤ)) =
      (Finset.Ioc N (2 * N)).map ⟨(Nat.cast : ℕ → ℤ), Nat.cast_injective⟩ := by
    ext m
    simp only [Finset.mem_Ioc, Finset.mem_map, Function.Embedding.coeFn_mk]
    refine ⟨fun ⟨h1, h2⟩ ↦ ⟨m.toNat, by omega, by omega⟩, ?_⟩
    rintro ⟨a, ⟨ha1, ha2⟩, rfl⟩
    omega
  have hrhs : GPYSieveS1.S1 h l (N : ℝ) (W N) w₀.val = ∑ n ∈ Finset.Ioc N (2 * N), T n := by
    rw [GPYSieveS1.S1, Int.floor_natCast, hfloor2, Finset.sum_filter, hmapset, Finset.sum_map]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    simp only [Function.Embedding.coeFn_mk, hT]
    rw [Finset.mem_Ioc] at hn
    have hres := res_iff w₀ n
    have hne : ∀ i, n + h i ≠ 0 := fun i ↦ by omega
    by_cases hc : ((n : ℕ) : ZMod (W N)) = w₀
    · rw [if_pos (hres.mpr hc), if_pos hc, weight_eq_wVal h l n hne]
    · rw [if_neg (fun hh ↦ hc (hres.mp hh)), if_neg hc]
  rw [hlhs, hrhs]

/-- The canonical `L²(𝓡 k)` membership witness of a smooth compactly-supported `F`, chosen to
be *definitionally identical* to the one appearing inside `lem_S2m_smooth`'s `J`-term. -/
theorem canonMemLp {k : ℕ} (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hsupp : Function.support F ⊆ 𝓡 k) :
    MemLp F 2 (volume.restrict (𝓡 k)) :=
  hF.continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_scaledStdSimplex hsupp)

/-- The little-`o` normaliser `c / D₀ N → 0` (since `D₀ N → ∞`). -/
theorem tendsto_coeff_div_D0 (c : ℝ) :
    Filter.Tendsto (fun N : ℕ ↦ c / PrimeGaps.D₀ (N : ℝ)) Filter.atTop (𝓝 0) :=
  (tendsto_const_nhds (x := c)).div_atTop
    (PrimeGaps.D0_tendsto_atTop.comp tendsto_natCast_atTop_atTop)

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- Uniformly in `w₀`, `S₁ = mainScale * ‖F‖² + o(mainScale)` and
`S₂ = (φ (W N) ^ k * N * log R ^ (k+1) / (W N ^ (k+1) * log N)) * ∑ m, J m F + o(mainScale)`. -/
@[pg_tag "bg246" "prop_main_prop"]
theorem prop_main_prop {k : ℕ} (hk : 2 ≤ k) (h : Fin k → ℕ) (hadm : GPYSieveS1.IsAdmissible h)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hsupp : Function.support F ⊆ 𝓡 k)
    (θ δ : ℝ) (hθ0 : 0 < θ) (hθ : θ < 1 / 2) (hδ : 0 < δ) (hδθ : δ < θ / 2)
    (hLD : Nat.HasLevelOfDistribution Set.univ θ 1) :
    ∃ e₁ e₂ : ℕ → ℝ,
      Filter.Tendsto e₁ Filter.atTop (𝓝 0) ∧ Filter.Tendsto e₂ Filter.atTop (𝓝 0) ∧
      ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ w₀ : ZMod (W N),
          (∀ i, ((w₀.val : ℤ) + h i).gcd (W N) = 1) →
          |PrimeGaps.S₁ h (⇑(PrimeGaps.l₀ (R)
        (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp)))) N w₀ -
              PrimeGaps.mainScale k N R (W N) * ‖(canonMemLp F hF hsupp).toLp F‖ ^ 2| ≤ e₁ N *
                PrimeGaps.mainScale k N R (W N) ∧
          |PrimeGaps.S₂ h (⇑(PrimeGaps.l₀ (R)
        (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp)))) N w₀ - ((W N).totient : ℝ) ^ k * (N : ℝ) *
                    Real.log (R) ^ (k + 1) /
                    ((W N : ℝ) ^ (k + 1) * Real.log N) *
                  (∑ m, PrimeGaps.J m ((canonMemLp F hF hsupp).toLp F))| ≤
            e₂ N * PrimeGaps.mainScale k N R (W N) := by
  classical
  haveI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  obtain ⟨C1, hC1, N1, HS1⟩ :=
    lem_S1_smooth hk h hadm F hF hsupp θ δ ⟨hθ0, by linarith⟩ ⟨hδ, hδθ⟩
  have hS2m : ∀ m : Fin k, ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ w₀ : ZMod (W N), (∀ i, ((w₀.val : ℤ) + h i).gcd (W N) = 1) →
        |PrimeGaps.S₂m h (⇑(PrimeGaps.l₀ (R)
        (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp)))) N w₀ m - ((W N).totient : ℝ) ^ k * (N : ℝ) *
                Real.log (R) ^ (k + 1) /
                ((W N : ℝ) ^ (k + 1) * Real.log N) *
              PrimeGaps.J m ((hF.continuous.memLp_of_hasCompactSupport
                  (HasCompactSupport.of_support_subset_isCompact
                    isCompact_scaledStdSimplex hsupp)).toLp F)| ≤
          C * (MaynardSmoothY.Fmax F) ^ 2 * ((W N).totient : ℝ) ^ k * (N : ℝ) * Real.log (R) ^ k /
              ((W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ)) :=
    fun m ↦ lem_S2m_smooth m hk h hadm.1.injective F hF hsupp θ δ hθ0 hθ hδ hδθ hLD
  choose Cf hCf N0f Hf using hS2m
  set N2 : ℝ := Finset.univ.sup' Finset.univ_nonempty N0f
  refine ⟨fun N ↦ C1 * (MaynardSmoothY.Fmax F) ^ 2 / PrimeGaps.D₀ (N : ℝ),
    fun N ↦ (∑ m, Cf m) * (MaynardSmoothY.Fmax F) ^ 2 / PrimeGaps.D₀ (N : ℝ),
    tendsto_coeff_div_D0 _, tendsto_coeff_div_D0 _,
    max (max N1 N2) (rexp (rexp (rexp 2))), ?_⟩
  intro N hN w₀ hw₀
  obtain ⟨hNa, hNe⟩ := max_le_iff.mp hN
  obtain ⟨hN1, hN2'⟩ := max_le_iff.mp hNa
  have hV0 : GPYSieveS1.V0Valid h (W N) w₀.val :=
    ⟨ZMod.val_lt w₀, fun i ↦ Int.isCoprime_iff_gcd_eq_one.mpr (hw₀ i)⟩
  have hD2 : (2 : ℝ) ≤ PrimeGaps.D₀ (N : ℝ) := PrimeGaps.MaynardOffDiagonal.two_le_D0_of_large hNe
  have hD0pos : (0 : ℝ) < PrimeGaps.D₀ (N : ℝ) := by linarith
  have hD0ne : PrimeGaps.D₀ (N : ℝ) ≠ 0 := ne_of_gt hD0pos
  have hWpos : (0 : ℝ) < (W N : ℝ) := by exact_mod_cast PrimeGaps.W_pos
  have hWne : ((W N : ℝ)) ^ (k + 1) ≠ 0 := by positivity
  constructor
  · have h1 := HS1 N (by exact_mod_cast hN1) w₀.val hV0
    rw [show (PrimeGaps.l₀ (R) (W N) (fun x ↦
      F (WithLp.toLp 2 x))) = PrimeGaps.l₀ (R)
        (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp)) from rfl,
      ← PrimeGaps.I_toLp_eq k F (canonMemLp F hF hsupp)] at h1
    rw [S1_eq_gpy]
    exact le_trans h1 (le_of_eq (by simp only [PrimeGaps.mainScale]; field_simp))
  · set g : Lp ℝ 2 (volume.restrict (𝓡 k)) := (canonMemLp F hF hsupp).toLp F
    set P : ℝ := ((W N).totient : ℝ) ^ k * (N : ℝ) * Real.log (R) ^ (k + 1) /
        ((W N : ℝ) ^ (k + 1) * Real.log N)
    have hEq : PrimeGaps.S₂ h (⇑(PrimeGaps.l₀ (R)
        (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp)))) N w₀ - P * (∑ m, PrimeGaps.J m g) =
        ∑ m, (PrimeGaps.S₂m h (⇑(PrimeGaps.l₀ (R)
        (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp))))
              N w₀ m - P * PrimeGaps.J m g) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, PrimeGaps.sum_S₂m_eq_S₂]
    simp only [PrimeGaps.mainScale]
    rw [hEq]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum fun m _ ↦
      Hf m N (le_trans (Finset.le_sup' N0f (Finset.mem_univ m)) hN2') w₀ hw₀) (le_of_eq ?_))
    rw [← Finset.sum_div, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
    field_simp

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- `S₂ - ρ * S₁ = mainScale * ((θ/2 - δ) * ∑ m, J m F - ρ * ‖F‖²) + o(mainScale)`,
uniformly in `w₀`. -/
@[pg_tag "bg246" "lem_S_asymptotic"]
theorem lem_S_asymptotic {k : ℕ} (hk : 2 ≤ k) (h : Fin k → ℕ) (hadm : GPYSieveS1.IsAdmissible h)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hsupp : Function.support F ⊆ 𝓡 k)
    (θ δ : ℝ) (hθ0 : 0 < θ) (hθ : θ < 1 / 2) (hδ : 0 < δ) (hδθ : δ < θ / 2)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLD : Nat.HasLevelOfDistribution Set.univ θ 1) :
    ∃ e : ℕ → ℝ, Filter.Tendsto e Filter.atTop (𝓝 0) ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
        ∀ w₀ : ZMod (W N), (∀ i, ((w₀.val : ℤ) + h i).gcd (W N) = 1) →
          |(PrimeGaps.S₂ h (⇑(PrimeGaps.l₀ (R)
        (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp)))) N w₀ - ρ * PrimeGaps.S₁ h (⇑(PrimeGaps.l₀ (R)
        (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp))))
                    N w₀) - PrimeGaps.mainScale k N R (W N) *
                ((θ / 2 - δ) * (∑ m, PrimeGaps.J m ((canonMemLp F hF hsupp).toLp F)) -
                    ρ * ‖(canonMemLp F hF hsupp).toLp F‖ ^ 2)| ≤
          e N * PrimeGaps.mainScale k N R (W N) := by
  obtain ⟨e₁, e₂, he₁, he₂, N₀, Hp⟩ := prop_main_prop hk h hadm F hF hsupp θ δ hθ0 hθ hδ hδθ hLD
  refine ⟨fun N ↦ e₂ N + ρ * e₁ N, by simpa using he₂.add (he₁.const_mul ρ), max N₀ 2, ?_⟩
  intro N hN w₀ hw₀
  obtain ⟨hN0, hN2⟩ := max_le_iff.mp hN
  obtain ⟨H1, H2⟩ := Hp N hN0 w₀ hw₀
  set S1v : ℝ := PrimeGaps.S₁ h (⇑(PrimeGaps.l₀ (R) (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp)))) N w₀
  set S2w : ℝ := PrimeGaps.S₂ h (⇑(PrimeGaps.l₀ (R) (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp)))) N w₀
  set sc : ℝ := PrimeGaps.mainScale k N R (W N) with hscdef
  set II : ℝ := ‖(canonMemLp F hF hsupp).toLp F‖ ^ 2
  set JJ : ℝ := ∑ m, PrimeGaps.J m ((canonMemLp F hF hsupp).toLp F)
  set P : ℝ := ((W N).totient : ℝ) ^ k * (N : ℝ) * Real.log (R) ^ (k + 1) /
      ((W N : ℝ) ^ (k + 1) * Real.log N) with hPdef
  have hN1 : (1 : ℝ) < (N : ℝ) := by linarith
  have hNposR : (0 : ℝ) < (N : ℝ) := by linarith
  have hWpos : (0 : ℝ) < (W N : ℝ) := by exact_mod_cast PrimeGaps.W_pos
  have hlogNpos : (0 : ℝ) < Real.log N := Real.log_pos hN1
  have hlogR_eq : Real.log (R) = (θ / 2 - δ) * Real.log N := Real.log_rpow hNposR _
  have hPJ : P * JJ = sc * ((θ / 2 - δ) * JJ) := by
    rw [hPdef, hscdef, PrimeGaps.mainScale, hlogR_eq]
    field_simp
    ring
  have hrw : (S2w - ρ * S1v) - sc * ((θ / 2 - δ) * JJ - ρ * II) =
      (S2w - P * JJ) - ρ * (S1v - sc * II) := by
    rw [hPJ]; ring
  rw [hrw]
  have hb : |(S2w - P * JJ) - ρ * (S1v - sc * II)| ≤ |S2w - P * JJ| + ρ * |S1v - sc * II| := by
    rw [sub_eq_add_neg]
    refine (abs_add_le _ _).trans_eq ?_
    rw [abs_neg, abs_mul, abs_of_pos hρ]
  have hstep : |S2w - P * JJ| + ρ * |S1v - sc * II| ≤ e₂ N * sc + ρ * (e₁ N * sc) := by
    linarith [H2, mul_le_mul_of_nonneg_left H1 hρ.le]
  exact hb.trans (hstep.trans (le_of_eq (by ring)))

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- If `ρ * ‖F‖² < (θ/2 - δ) * ∑ m, J m F`, then `0 < S₂ - ρ * S₁` for all large `N` and every
valid `w₀`. -/
@[pg_tag "bg246" "lem_S_positive"]
theorem lem_S_positive {k : ℕ} (hk : 2 ≤ k) (h : Fin k → ℕ) (hadm : GPYSieveS1.IsAdmissible h)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hsupp : Function.support F ⊆ 𝓡 k)
    (θ δ : ℝ) (hθ0 : 0 < θ) (hθ : θ < 1 / 2) (hδ : 0 < δ) (hδθ : δ < θ / 2)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLD : Nat.HasLevelOfDistribution Set.univ θ 1)
    (hwit : ρ * ‖(canonMemLp F hF hsupp).toLp F‖ ^ 2 <
        (θ / 2 - δ) * (∑ m, PrimeGaps.J m ((canonMemLp F hF hsupp).toLp F))) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ w₀ : ZMod (W N), (∀ i, ((w₀.val : ℤ) + h i).gcd (W N) = 1) →
        0 < PrimeGaps.S₂ h (⇑(PrimeGaps.l₀ (R)
        (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp)))) N w₀ - ρ * PrimeGaps.S₁ h (⇑(PrimeGaps.l₀ (R)
        (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp)))) N
                w₀ := by
  obtain ⟨e, he, N₀, Ha⟩ := lem_S_asymptotic hk h hadm F hF hsupp θ δ hθ0 hθ hδ hδθ ρ hρ hLD
  set c : ℝ := (θ / 2 - δ) * (∑ m, PrimeGaps.J m ((canonMemLp F hF hsupp).toLp F)) -
      ρ * ‖(canonMemLp F hF hsupp).toLp F‖ ^ 2 with hcdef
  have hc : 0 < c := sub_pos.mpr hwit
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (he.eventually_lt_const hc)
  refine ⟨max (max N₀ (rexp (rexp (rexp 2)))) (M : ℝ), ?_⟩
  intro N hN w₀ hw₀
  obtain ⟨hNa, hNM⟩ := max_le_iff.mp hN
  obtain ⟨hN0, hNe⟩ := max_le_iff.mp hNa
  have heN : e N < c := hM N (by exact_mod_cast hNM)
  have hD2 : (2 : ℝ) ≤ PrimeGaps.D₀ (N : ℝ) := PrimeGaps.MaynardOffDiagonal.two_le_D0_of_large hNe
  have hgt1 : (1 : ℝ) < rexp (rexp (rexp 2)) :=
    Real.one_lt_exp_iff.mpr (Real.exp_pos _)
  have hN1 : (1 : ℝ) < (N : ℝ) := lt_of_lt_of_le hgt1 hNe
  have hNposR : (0 : ℝ) < (N : ℝ) := lt_trans one_pos hN1
  have hWpos : (0 : ℝ) < (W N : ℝ) := by exact_mod_cast PrimeGaps.W_pos
  have hφWpos : (0 : ℝ) < ((W N).totient : ℝ) := PrimeGaps.totient_W_pos
  have hlogR_eq : Real.log (R) = (θ / 2 - δ) * Real.log N := Real.log_rpow hNposR _
  have hlogRpos : (0 : ℝ) < Real.log (R) := by
    rw [hlogR_eq]
    exact mul_pos (by linarith) (Real.log_pos hN1)
  have hscpos : 0 < PrimeGaps.mainScale k N R (W N) := by
    rw [PrimeGaps.mainScale]
    positivity
  have Ha' := Ha N hN0 w₀ hw₀
  set S : ℝ := PrimeGaps.S₂ h (⇑(PrimeGaps.l₀ (R) (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp)))) N w₀ -
      ρ * PrimeGaps.S₁ h (⇑(PrimeGaps.l₀ (R) (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp)))) N
          w₀
  have hlow : PrimeGaps.mainScale k N R (W N) * c - e N * PrimeGaps.mainScale k N R (W N) ≤ S := by
    linarith [(abs_le.mp Ha').1]
  linarith [hlow, mul_pos hscpos (show (0 : ℝ) < c - e N by linarith)]

end PrimeGaps.MainProp
