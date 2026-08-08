/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.S1.SubstituteSmoothY
public import PrimeGapsTheory.Sieve.S2m.Eval
public import PrimeGapsTheory.Sieve.S2m.Expansion

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Smooth weights in the second-moment sieve

Specializes the transformed-weight bounds to the smooth Maynard sieve weights.

## Main results

* `PrimeGaps.S2mSmooth.ym_sup_le`: a uniform bound for `⨆ r, |ym m (l₀ R W F) r|`.
* `PrimeGaps.lem_S2m_smooth`: the asymptotic for the second moment `S₂^(m)` at the canonical
  smooth weight `l₀`.
-/

@[expose] public section

open Real

open scoped Finset
open scoped Nat

open scoped ArithmeticFunction.detotient

open PrimeGaps ArithmeticFunction Moebius detotient GPYSieveS1 MeasureTheory MaynardSmoothY
open PrimeGaps.LemS1RestrictSij

namespace PrimeGaps.S2mSmooth

/-- Rewrites the `ym`-sum onto the pinned guard `r m = 1`, dropping the `i = m` factor from
`∏ᵢ g (r i)`. -/
lemma gapB {k : ℕ} (m : Fin k) (R : ℝ) (W : ℕ) (L : (Fin k → ℕ) →₀ ℝ)
    (hlam : L.HasPermissibleSupport ⌊R⌋₊ W) :
    (∑' u : Fin k → ℕ, if (∀ i, 1 ≤ u i) ∧ RestrictedCoprime u (fun _ _ ↦ 1)
        then PrimeGaps.ym m L u ^ 2 / ∏ i, (g (u i) : ℝ) else 0) = (∑' r : Fin k → ℕ,
        if r m = 1 ∧ (∀ i, i ≠ m → 1 ≤ r i ∧ (r i).Coprime W) then
          (PrimeGaps.ym m L r) ^ 2 / (∏ i ∈ Finset.univ.erase m, (g (r i) : ℝ))
        else 0) := by
  refine tsum_congr fun u ↦ ?_
  by_cases h0 : PrimeGaps.ym m L u = 0
  · simp [h0]
  · have hpin : u m = 1 := PrimeGaps.ym_pin_eq_one m L R W hlam u h0
    have hone : ∀ i, 1 ≤ u i := fun i ↦
      (PrimeGaps.ym_coord_squarefree m L R W hlam u h0 i).ne_zero.bot_lt
    have hguardL : (∀ i, 1 ≤ u i) ∧ RestrictedCoprime u (fun _ _ ↦ 1) :=
      ⟨hone, PrimeGaps.restrictedCoprime_one u⟩
    have hguardR : u m = 1 ∧ (∀ i, i ≠ m → 1 ≤ u i ∧ (u i).Coprime W) :=
      ⟨hpin, fun i _ ↦ ⟨hone i, PrimeGaps.ym_coord_coprimeW W m L R hlam u h0 i⟩⟩
    rw [if_pos hguardL, if_pos hguardR]
    congr 1
    rw [← Finset.mul_prod_erase Finset.univ (fun i ↦ (g (u i) : ℝ)) (Finset.mem_univ m), hpin]
    simp [detotient_one]

/-- `{0, k!, 2·k!, …, (k−1)·k!}` is admissible of cardinality `k`. -/
lemma exists_admissible_card (k : ℕ) : ∃ H : Finset ℕ, H.Admissible ∧ #H = k := by
  have hinj : Function.Injective (fun i : ℕ ↦ i * k !) :=
    mul_left_injective₀ (Nat.factorial_ne_zero k)
  refine ⟨(Finset.range k).image (fun i ↦ i * k !), ?_, ?_⟩
  · rw [Finset.admissible_iff_le_card, Finset.card_image_of_injective _ hinj, Finset.card_range]
    intro p hp hpp
    refine ⟨1, hpp.one_lt, fun x hx ↦ ?_⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    have : (i * k !) % p = 0 :=
      Nat.mod_eq_zero_of_dvd ((Nat.dvd_factorial hpp.pos hp).mul_left i)
    omega
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_range]

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- `⨆_r |ym m L r| ≤ C · Fmax G · φ(W) · log R / W` for large `N`, uniformly over permissible `L`
with `(lToY L).maxRealAbs ≤ Fmax G`. -/
theorem ym_sup_le_of_maxRealAbs {k : ℕ} (m : Fin k) (G : EuclideanSpace ℝ (Fin k) → ℝ)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hGsupp : Function.support G ⊆ 𝓡 k)
    (θ δ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ L : (Fin k → ℕ) →₀ ℝ, L.HasPermissibleSupport ⌊R⌋₊ (W N) →
        (PrimeGaps.lToY L).maxRealAbs ≤ MaynardSmoothY.Fmax G →
        ⨆ r, |PrimeGaps.ym m L r| ≤
          C * MaynardSmoothY.Fmax G * ((W N).totient : ℝ) * Real.log R / (W N : ℝ) := by
  obtain ⟨C_A, hC_A0, hA⟩ := MaynardSmoothY.exists_abs_ym_sub_yInverseSum_le (k := k)
  obtain ⟨H, hHadm, hHcard⟩ := PrimeGaps.S2mSmooth.exists_admissible_card k
  obtain ⟨N₀_A, hAbody⟩ := hA H hHadm hHcard θ δ hθ hδ.1 hδ.2 G hG hGsupp
  obtain ⟨C_B, hC_B0, hB⟩ := yInverseSum_triangle_bound (k := k)
  have hexp : 0 < θ / 2 - δ := by linarith [hδ.2]
  obtain ⟨N₁, _, hpf⟩ := PrimeGaps.MaynardOffDiagonal.primorial_D0_primeFactors_le_Rval θ δ hexp
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp (R_eventually_ge θ δ hδ.2 (rexp 1))
  refine ⟨2 * C_B + C_A, by linarith, ?_⟩
  refine ⟨max (max N₀_A N₁) (max (N₂ : ℝ) (rexp (rexp (rexp 2)))), ?_⟩
  intro N hN L hL hyMax
  simp only [max_le_iff] at hN
  obtain ⟨⟨hNA, hNN₁⟩, hNN₂, hNe⟩ := hN
  have hNpos : 0 < N := by
    have : (1 : ℝ) ≤ rexp (rexp (rexp 2)) := Real.one_le_exp (by positivity)
    exact_mod_cast lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one this) hNe
  have hW1 : 1 ≤ W N := PrimeGaps.W_pos
  have hFmnn : 0 ≤ MaynardSmoothY.Fmax G := MaynardSmoothY.Fmax_nonneg G hG
  have hR1 : rexp 1 ≤ R := hN₂ N (by exact_mod_cast hNN₂)
  have hlogR1 : 1 ≤ Real.log R := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hR1
  have hlogRpos : 0 < Real.log R := one_pos.trans_le hlogR1
  have hD1 : (1 : ℝ) ≤ PrimeGaps.D₀ (N : ℝ) := by
    linarith only [PrimeGaps.MaynardOffDiagonal.two_le_D0_of_large hNe]
  have hR1' : (1 : ℝ) ≤ (N : ℝ) ^ (θ / 2 - δ) := by
    rw [← Real.one_rpow (θ / 2 - δ)]
    exact Real.rpow_le_rpow (by norm_num) (by exact_mod_cast (by omega : 1 ≤ N)) hexp.le
  set M₀ : ℝ := MaynardSmoothY.Fmax G * ((W N).totient : ℝ) * Real.log R / (W N : ℝ) with hM₀
  have hM₀nn : 0 ≤ M₀ := by rw [hM₀]; positivity
  have hper : ∀ r, |PrimeGaps.ym m L r| ≤ (2 * C_B + C_A) * M₀ := by
    intro r
    by_cases hcase : r m = 1 ∧ ∀ i, Squarefree (r i)
    · have hyinv := hB R (W N) L hL m r hW1 (fun p hp ↦ hpf (N : ℝ) hNN₁ p hp) hR1'
      have hdiff := hAbody N hNA L hL hyMax m r hcase.1 hcase.2
      have htri : |PrimeGaps.ym m L r| ≤ |yInverseSum L m r| +
          |PrimeGaps.ym m L r - yInverseSum L m r| := by
        simpa using abs_add_le (yInverseSum L m r) (PrimeGaps.ym m L r - yInverseSum L m r)
      have hlog2 : Real.log R + 1 ≤ 2 * Real.log R := by linarith
      have hyinvM : |yInverseSum L m r| ≤ 2 * C_B * M₀ := by
        refine hyinv.trans ?_
        rw [hM₀,
          show 2 * C_B * (MaynardSmoothY.Fmax G * ((W N).totient : ℝ) * Real.log R / (W N : ℝ)) =
            C_B * MaynardSmoothY.Fmax G * ((W N).totient : ℝ) *
                (2 * Real.log R) / (W N : ℝ) by ring]
        gcongr
      have herr : MaynardSmoothY.errorSize R (W N) G N ≤ M₀ := by
        rw [hM₀]
        change _ * Real.log R / (_ * PrimeGaps.D₀ N) ≤ _ * Real.log R / _
        rw [div_mul_eq_div_div]
        exact div_le_self (by positivity) hD1
      have hdiffM : |PrimeGaps.ym m L r - yInverseSum L m r| ≤ C_A * M₀ :=
        hdiff.trans (mul_le_mul_of_nonneg_left herr hC_A0)
      have hsum : (2 * C_B + C_A) * M₀ = 2 * C_B * M₀ + C_A * M₀ := by ring
      linarith only [htri, hyinvM, hdiffM, hsum]
    · have h0 : PrimeGaps.ym m L r = 0 := by
        by_contra hne
        exact hcase ⟨PrimeGaps.ym_pin_eq_one m L R (W N) hL r hne,
          fun i ↦ PrimeGaps.ym_coord_squarefree m L R (W N) hL r hne i⟩
      rw [h0, abs_zero]
      exact mul_nonneg (by linarith) hM₀nn
  refine (ciSup_le hper).trans_eq ?_
  rw [hM₀]
  ring

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- `ym_sup_le_of_maxRealAbs` for the canonical smooth weight `l₀ R W F`. -/
lemma ym_sup_le {k : ℕ} (m : Fin k) (hk : 2 ≤ k)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hsupp : Function.support F ⊆ 𝓡 k)
    (θ δ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hδ0 : 0 < δ) (hδθ : δ < θ / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ⨆ r, |PrimeGaps.ym m
        (PrimeGaps.l₀ (R) (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp))) r| ≤
        C * MaynardSmoothY.Fmax F * ((W N).totient : ℝ) *
            Real.log (R) / (W N : ℝ) := by
  obtain ⟨C, hC0, N₀, hbody⟩ := ym_sup_le_of_maxRealAbs m F hF hsupp θ δ hθ ⟨hδ0, hδθ⟩
  refine ⟨C, hC0, max N₀ 1, fun N hN ↦ ?_⟩
  have hNpos : 0 < N := by
    exact_mod_cast zero_lt_one.trans_le ((le_max_right _ _).trans hN)
  exact hbody N ((le_max_left _ _).trans hN) _ PrimeGaps.hasPermissibleSupport_l₀
    (MaynardSmoothY.maxRealAbs_lambda0_le_Fmax R (W N) F hk
      (Real.rpow_pos_of_pos (by exact_mod_cast hNpos) _) hF hsupp)

open scoped PrimeGaps.sieveModulus in
/-- Eventually `W(N)^(k+1) · D₀(N) ≤ (log N)^(2k+3)`. -/
lemma W_pow_D0_le (k : ℕ) : ∀ᶠ N : ℕ in Filter.atTop,
    (W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ) ≤ Real.log N ^ (2 * k + 3) := by
  filter_upwards [PrimeGaps.lem_W_size,
    Filter.eventually_ge_atTop ⌈rexp (rexp 1)⌉₊] with N hWsize hNe
  have hNe' : rexp (rexp 1) ≤ (N : ℝ) := by exact_mod_cast Nat.ceil_le.mp hNe
  have hlogN : rexp 1 ≤ Real.log N := by
    rw [← Real.log_exp (rexp 1)]; exact Real.log_le_log (Real.exp_pos _) hNe'
  have hlogNpos : 0 < Real.log N := (Real.exp_pos 1).trans_le hlogN
  have hll1 : 1 ≤ Real.log (Real.log N) := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hlogN
  have hllpos : 0 < Real.log (Real.log N) := one_pos.trans_le hll1
  have hD0nn : 0 ≤ PrimeGaps.D₀ (N : ℝ) := Real.log_nonneg hll1
  have hD0le : PrimeGaps.D₀ (N : ℝ) ≤ Real.log (Real.log N) := by
    simp only [PrimeGaps.D₀]
    linarith [Real.log_le_sub_one_of_pos hllpos]
  have hllle : Real.log (Real.log N) ≤ Real.log N := by
    linarith [Real.log_le_sub_one_of_pos hlogNpos]
  calc (W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ)
      ≤ (Real.log (Real.log N) ^ 2) ^ (k + 1) * Real.log (Real.log N) :=
        mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hWsize _) hD0le hD0nn (by positivity)
    _ = Real.log (Real.log N) ^ (2 * k + 3) := by
        rw [← pow_mul, show 2 * (k + 1) = 2 * k + 2 from by omega, ← pow_succ,
          show 2 * k + 2 + 1 = 2 * k + 3 from by omega]
    _ ≤ Real.log N ^ (2 * k + 3) := pow_le_pow_left₀ hllpos.le hllle _

end PrimeGaps.S2mSmooth

namespace PrimeGaps

/-- If `P * E = C * T * (x / y)` with `0 ≤ C`, `0 ≤ T` and `0 < y`, then `x ≤ y` gives
`P * E ≤ C * T`. -/
private lemma mul_le_of_eq_mul_mul_div {P E C T x y : ℝ} (h : P * E = C * T * (x / y))
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hy : 0 < y) (hxy : x ≤ y) : P * E ≤ C * T := by
  rw [h]
  exact mul_le_of_le_one_right (mul_nonneg hC hT) ((div_le_one hy).mpr hxy)

open MeasureTheory MaynardSmoothY in
open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- For the canonical smooth weight `l₀`, the second-moment
sum `S₂^(m)` is asymptotic to the main term
`φ(W)^k · N · (log R)^{k+1} / (W^{k+1} · log N) · J m F`, with an error of size
`O(Fmax F ^ 2 · φ(W)^k · N · (log R)^k / (W^{k+1} · D₀ N))`. -/
@[pg_tag "bg246" "lem_S2m_smooth"]
theorem lem_S2m_smooth {k : ℕ} (m : Fin k) (hk : 2 ≤ k)
    (h : Fin k → ℕ) (hinj : Function.Injective h)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hsupp : Function.support F ⊆ 𝓡 k)
    (θ δ : ℝ) (hθ0 : 0 < θ) (hθ : θ < 1 / 2) (hδ : 0 < δ) (hδθ : δ < θ / 2)
    (hLD : Nat.HasLevelOfDistribution Set.univ θ 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ w₀ : ZMod (W N),
        (∀ i, ((w₀.val : ℤ) + h i).gcd (W N) = 1) →
        |PrimeGaps.S₂m h (⇑(PrimeGaps.l₀ (R)
        (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp)))) N w₀ m - ((W N).totient : ℝ) ^ k * (N : ℝ) *
                Real.log (R) ^ (k + 1) /
                ((W N : ℝ) ^ (k + 1) * Real.log N) * PrimeGaps.J m
                  ((hF.continuous.memLp_of_hasCompactSupport
                      (HasCompactSupport.of_support_subset_isCompact
                        EuclideanSpace.isCompact_scaledStdSimplex hsupp)).toLp F)| ≤
          C * (MaynardSmoothY.Fmax F) ^ 2 * ((W N).totient : ℝ) ^ k * (N : ℝ) * Real.log (R) ^ k /
              ((W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ)) := by
  have hθIoo : θ ∈ Set.Ioo (0 : ℝ) 1 := ⟨hθ0, by linarith⟩
  have hexp : 0 < θ / 2 - δ := by linarith
  set Aexp : ℝ := ((2 * k + 3 : ℕ) : ℝ) with hAexp
  have hA0 : 0 < Aexp := by rw [hAexp]; positivity
  obtain ⟨H, hHadm, hHcard⟩ := S2mSmooth.exists_admissible_card k
  obtain ⟨C_fy, hC_fy0, N_fy, hfy⟩ := lem_S2m_from_ym m hk h hinj θ δ hθ0 hθ hδ hδθ hLD Aexp hA0
  obtain ⟨C_sm, hC_sm0, hsm⟩ := lem_S2m_second_moment hk
  obtain ⟨N_sm, hsmbody⟩ := hsm H hHadm hHcard θ δ hθIoo hδ hδθ F hF hsupp
  obtain ⟨C_ed, hC_ed0, hed⟩ := lem_S2m_expand_drop hk
  obtain ⟨N_ed, hedbody⟩ := hed H hHadm hHcard θ δ hθIoo hδ hδθ F hF hsupp
  obtain ⟨C_ev, hC_ev0, hev⟩ := lem_S2m_eval hk
  obtain ⟨N_ev, hevbody⟩ := hev H hHadm hHcard θ δ hθIoo hδ hδθ F hF hsupp
  obtain ⟨C_sup, hC_sup0, N_sup, hsup⟩ := S2mSmooth.ym_sup_le m hk F hF hsupp θ δ hθIoo hδ hδθ
  obtain ⟨N_w, hN_wbody⟩ := Filter.eventually_atTop.mp (S2mSmooth.W_pow_D0_le k)
  obtain ⟨N_R, hN_R⟩ := Filter.eventually_atTop.mp (R_eventually_ge θ δ hδθ (rexp 1))
  have hCfin0 : 0 < (C_sm + C_ed + C_ev) +
      C_fy * C_sup ^ 2 * (1 / (θ / 2 - δ)) ^ (k - 2) + C_fy := by
    have h1 : 0 ≤ C_fy * C_sup ^ 2 * (1 / (θ / 2 - δ)) ^ (k - 2) :=
      mul_nonneg (mul_nonneg hC_fy0.le (sq_nonneg _))
        (pow_nonneg (div_nonneg zero_le_one hexp.le) (k - 2))
    linarith [hC_fy0, hC_sm0, hC_ed0, hC_ev0]
  refine ⟨_, hCfin0, max (max (max N_fy N_sm) (max N_ed N_ev))
    (max N_sup (max (N_w : ℝ) (max (rexp (rexp (rexp 2))) (N_R : ℝ)))), ?_⟩
  intro N hN₀ w₀ hw₀
  simp only [max_le_iff] at hN₀
  obtain ⟨⟨⟨hNfy, hNsm⟩, hNed, hNev⟩, hNsup, hNw, hNe, hNR⟩ := hN₀
  have hNpos : 0 < N := by
    have h1 : (1 : ℝ) ≤ rexp (rexp (rexp 2)) := Real.one_le_exp (by positivity)
    exact_mod_cast (zero_lt_one.trans_le h1).trans_le hNe
  have hNposR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hWpos : (0 : ℝ) < (W N : ℝ) := by exact_mod_cast PrimeGaps.W_pos
  have hφWpos : (0 : ℝ) < ((W N).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr PrimeGaps.W_pos
  have hlogNpos : 0 < Real.log N := Real.log_pos (by
    have h1 : (1 : ℝ) < rexp (rexp (rexp 2)) := by
      linarith only [Real.add_one_le_exp (rexp (rexp 2)), Real.exp_pos (rexp 2)]
    exact_mod_cast h1.trans_le hNe)
  have hlogR_eq : Real.log (R) = (θ / 2 - δ) * Real.log N := Real.log_rpow hNposR _
  have hlogRpos : 0 < Real.log (R) := by
    rw [hlogR_eq]; positivity
  have hlogRle : Real.log (R) ≤ Real.log N := by
    rw [hlogR_eq]
    exact mul_le_of_le_one_left hlogNpos.le (by linarith only [hθ, hδ])
  have hD0pos : 0 < PrimeGaps.D₀ (N : ℝ) := by
    linarith only [PrimeGaps.MaynardOffDiagonal.two_le_D0_of_large hNe]
  have hfyN := hfy N hNfy w₀ hw₀ (PrimeGaps.l₀ (R) (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp)))
    (fun d hd ↦ PrimeGaps.hasPermissibleSupport_l₀ (Finsupp.mem_support_iff.mpr hd))
    PrimeGaps.hasPermissibleSupport_l₀
  rw [S2mSmooth.gapB m (R) (W N) (PrimeGaps.l₀ (R) (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp)))
    PrimeGaps.hasPermissibleSupport_l₀] at hfyN
  have hyMaxle : (PrimeGaps.lToY (PrimeGaps.l₀ (R)
        (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp)))).maxRealAbs ≤
      MaynardSmoothY.Fmax F :=
    MaynardSmoothY.maxRealAbs_lambda0_le_Fmax R (W N) F hk
      (Real.rpow_pos_of_pos (by exact_mod_cast hNpos) _) hF hsupp
  have hsmN := hsmbody N hNsm (PrimeGaps.l₀ (R) (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp)))
    PrimeGaps.hasPermissibleSupport_l₀ hyMaxle m
  have hedN := hedbody N hNed m
  have hevN := hevbody N hNev m
  have hsupN := hsup N hNsup
  have hWD0N := hN_wbody N (by exact_mod_cast hNw)
  set φW : ℝ := ((W N).totient : ℝ) with hφWdef
  set Wr : ℝ := (W N : ℝ) with hWdef
  set logR : ℝ := Real.log (R) with hlogRdef
  set logN : ℝ := Real.log N with hlogNdef
  set Fm : ℝ := MaynardSmoothY.Fmax F with hFmdef
  set J : ℝ := PrimeGaps.J m ((hF.continuous.memLp_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact
        EuclideanSpace.isCompact_scaledStdSimplex hsupp)).toLp F) with hJdef
  set P : ℝ := (N : ℝ) / (φW * logN) with hPdef
  set mJ : ℝ := φW ^ (k + 1) * logR ^ (k + 1) / Wr ^ (k + 1) * J with hmJdef
  set ymSum : ℝ := ∑' r : Fin k → ℕ, if r m = 1 ∧ (∀ i, i ≠ m → 1 ≤ r i ∧ (r i).Coprime (W N)) then
        (PrimeGaps.ym m (PrimeGaps.l₀ (R)
        (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp))) r) ^ 2 /
          (∏ i ∈ Finset.univ.erase m, (g (r i) : ℝ))
      else 0 with hymSumdef
  set yInvSum : ℝ := ∑' r : Fin k → ℕ,
      if r m = 1 ∧ (∀ i, i ≠ m → 1 ≤ r i ∧ (r i).Coprime (W N)) then
        (yInverseSum (PrimeGaps.l₀ (R)
        (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp))) m r) ^ 2 /
          (∏ i ∈ Finset.univ.erase m, (g (r i) : ℝ))
      else 0 with hyInvSumdef
  set dSum : ℝ := decoupledSum R (W N) F m with hdSumdef
  have hFmnn : 0 ≤ Fm := MaynardSmoothY.Fmax_nonneg F hF
  have hPnn : 0 ≤ P := by rw [hPdef]; positivity
  set TU : ℝ := Fm ^ 2 * φW ^ k * (N : ℝ) * logR ^ k / (Wr ^ (k + 1) * PrimeGaps.D₀ (N : ℝ))
    with hTUdef
  have hTUnn : 0 ≤ TU := by
    rw [hTUdef]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg Fm) (pow_nonneg hφWpos.le k)) hNposR.le)
        (pow_nonneg hlogRpos.le k))
      (mul_nonneg (pow_nonneg hWpos.le (k + 1)) hD0pos.le)
  have hmain_id : φW ^ k * (N : ℝ) * logR ^ (k + 1) / (Wr ^ (k + 1) * logN) * J = P * mJ := by
    rw [hPdef, hmJdef]
    field_simp [hφWpos.ne', hWpos.ne']
    ring
  rw [hmain_id]
  have hchain := (abs_sub_le ymSum dSum mJ).trans
      (add_le_add ((abs_sub_le ymSum yInvSum dSum).trans (add_le_add hsmN hedN)) hevN)
  have hbnd2 : |P * ymSum - P * mJ| = P * |ymSum - mJ| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hPnn]
  have hbnd2' := hbnd2.le.trans (mul_le_mul_of_nonneg_left hchain hPnn)
  have hcomb := (abs_sub_le (PrimeGaps.S₂m h (⇑(PrimeGaps.l₀ (R)
        (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp)))) N w₀ m) (P * ymSum) (P * mJ)).trans
    (add_le_add hfyN hbnd2')
  refine hcomb.trans ?_
  set ymax : ℝ := ⨆ r,
    |PrimeGaps.ym m (PrimeGaps.l₀ (R) (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp))) r|
    with hymaxdef
  set Esm : ℝ :=
    C_sm * Fm ^ 2 * φW ^ (k + 1) * logR ^ (k + 1) / (Wr ^ (k + 1) * PrimeGaps.D₀ (N : ℝ))
    with hEsmdef
  set Eed : ℝ :=
    C_ed * Fm ^ 2 * φW ^ (k + 1) * logR ^ (k + 1) / (Wr ^ (k + 1) * PrimeGaps.D₀ (N : ℝ))
    with hEeddef
  set Eev : ℝ :=
    C_ev * Fm ^ 2 * φW ^ (k + 1) * logR ^ (k + 1) / (Wr ^ (k + 1) * PrimeGaps.D₀ (N : ℝ))
    with hEevdef
  have hymaxnn : 0 ≤ ymax := by rw [hymaxdef]; exact Real.iSup_nonneg fun _ ↦ abs_nonneg _
  have hmrlnn : (0 : ℝ) ≤ Finsupp.maxRealAbs (PrimeGaps.lToY (PrimeGaps.l₀ (R)
        (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp)))) :=
    Finsupp.maxRealAbs_nonneg
  have hφW1 : (1 : ℝ) ≤ φW := by
    rw [hφWdef]; exact_mod_cast Nat.totient_pos.mpr PrimeGaps.W_pos
  have hlogR1 : 1 ≤ logR := by
    rw [hlogRdef, ← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (hN_R N (by exact_mod_cast hNR))
  have hlogN_eq : logR / (θ / 2 - δ) = logN := by
    rw [hlogR_eq]; exact mul_div_cancel_left₀ _ hexp.ne'
  have hφWk : φW ^ k = φW ^ (k - 2) * φW ^ 2 := by
    rw [← pow_add, Nat.sub_add_cancel (by omega : 2 ≤ k)]
  have hWk1 : Wr ^ (k + 1) = Wr ^ (k - 1) * Wr ^ 2 := by
    rw [← pow_add, show k - 1 + 2 = k + 1 from by omega]
  have hlogRk : logR ^ k = logR ^ (k - 2) * logR ^ 2 := by
    rw [← pow_add, Nat.sub_add_cancel (by omega : 2 ≤ k)]
  have hPEsm : P * Esm ≤ C_sm * TU :=
    mul_le_of_eq_mul_mul_div (by
      rw [hPdef, hEsmdef, hTUdef]
      field_simp [hφWpos.ne', hlogNpos.ne', hWpos.ne', hD0pos.ne']
      ring) hC_sm0 hTUnn hlogNpos hlogRle
  have hPEed : P * Eed ≤ C_ed * TU :=
    mul_le_of_eq_mul_mul_div (by
      rw [hPdef, hEeddef, hTUdef]
      field_simp [hφWpos.ne', hlogNpos.ne', hWpos.ne', hD0pos.ne']
      ring) hC_ed0 hTUnn hlogNpos hlogRle
  have hPEev : P * Eev ≤ C_ev * TU :=
    mul_le_of_eq_mul_mul_div (by
      rw [hPdef, hEevdef, hTUdef]
      field_simp [hφWpos.ne', hlogNpos.ne', hWpos.ne', hD0pos.ne']
      ring) hC_ev0 hTUnn hlogNpos hlogRle
  have herr1 : C_fy * ymax ^ 2 * φW ^ (k - 2) * (N : ℝ) * logN ^ (k - 2) /
        (Wr ^ (k - 1) * PrimeGaps.D₀ (N : ℝ)) ≤
      (C_fy * C_sup ^ 2 * (1 / (θ / 2 - δ)) ^ (k - 2)) * TU := by
    have hstep : C_fy * ymax ^ 2 * φW ^ (k - 2) * (N : ℝ) * logN ^ (k - 2) /
          (Wr ^ (k - 1) * PrimeGaps.D₀ (N : ℝ)) ≤
        C_fy * (C_sup * Fm * φW * logR / Wr) ^ 2 * φW ^ (k - 2) * (N : ℝ) * logN ^ (k - 2) /
          (Wr ^ (k - 1) * PrimeGaps.D₀ (N : ℝ)) := by gcongr
    refine hstep.trans_eq ?_
    rw [hTUdef, ← hlogN_eq, hφWk, hWk1, hlogRk]
    simp only [div_pow, one_pow]
    field_simp [hφWpos.ne', hWpos.ne', hexp.ne']
  have herr2 : C_fy * (Finsupp.maxRealAbs (PrimeGaps.lToY (PrimeGaps.l₀ (R)
        (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp))))) ^ 2 *
        (N : ℝ) / logN ^ Aexp ≤ C_fy * TU := by
    have hlogNApos : (0 : ℝ) < logN ^ Aexp := by
      rw [hAexp]; exact Real.rpow_pos_of_pos hlogNpos _
    have hAeq : logN ^ Aexp = logN ^ (2 * k + 3) := by rw [hAexp, Real.rpow_natCast]
    have hstep : C_fy * (Finsupp.maxRealAbs (PrimeGaps.lToY (PrimeGaps.l₀ (R)
        (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp))))) ^ 2 *
          (N : ℝ) / logN ^ Aexp ≤ C_fy * Fm ^ 2 * (N : ℝ) / logN ^ Aexp := by gcongr
    refine hstep.trans ?_
    have hkey : Wr ^ (k + 1) * PrimeGaps.D₀ (N : ℝ) ≤ φW ^ k * logR ^ k * logN ^ (2 * k + 3) :=
      hWD0N.trans (le_mul_of_one_le_left (pow_nonneg hlogNpos.le _)
        (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hφW1) (one_le_pow₀ hlogR1)))
    have hratio1 : (1 : ℝ) ≤ φW ^ k * logR ^ k * logN ^ (2 * k + 3) /
        (Wr ^ (k + 1) * PrimeGaps.D₀ (N : ℝ)) := (one_le_div (by positivity)).mpr hkey
    rw [hTUdef, div_le_iff₀ hlogNApos, hAeq]
    have hgoaleq : C_fy * (Fm ^ 2 * φW ^ k * (N : ℝ) * logR ^ k /
          (Wr ^ (k + 1) * PrimeGaps.D₀ (N : ℝ))) * logN ^ (2 * k + 3) = C_fy * Fm ^ 2 * (N : ℝ) *
          (φW ^ k * logR ^ k * logN ^ (2 * k + 3) / (Wr ^ (k + 1) * PrimeGaps.D₀ (N : ℝ))) := by
      field_simp
    rw [hgoaleq]
    exact le_mul_of_one_le_right (by positivity) hratio1
  have hdist : P * (Esm + Eed + Eev) = P * Esm + P * Eed + P * Eev := by ring
  rw [hdist]
  have hCexp : ((C_sm + C_ed + C_ev) + C_fy * C_sup ^ 2 * (1 / (θ / 2 - δ)) ^ (k - 2) + C_fy) *
        Fm ^ 2 * φW ^ k * (N : ℝ) * logR ^ k / (Wr ^ (k + 1) * PrimeGaps.D₀ (N : ℝ)) =
      C_sm * TU + C_ed * TU + C_ev * TU +
        (C_fy * C_sup ^ 2 * (1 / (θ / 2 - δ)) ^ (k - 2)) * TU + C_fy * TU := by
    rw [hTUdef]; ring
  rw [hCexp]
  linarith only [hPEsm, hPEed, hPEev, herr1, herr2]

end PrimeGaps
