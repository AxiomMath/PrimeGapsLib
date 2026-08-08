/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Discrete.FinMulAntidiag
public import PrimeGapsTheory.Sieve.PermissibleSupport.FunctionW
public import PrimeGapsTheory.Sieve.SieveTruncation
import PrimeGapsTheory.Tactic.PaperTag

/-!
# Permissible support for sieve weights

For the Maynard–Tao sieve we work with weight functions `l : (Fin k → ℕ) → ℝ` and need to control
their support. A tuple `d : Fin k → ℕ` is *permissible* when
1. the product `∏ i, d i` lies below the sieve truncation `R`,
2. the product `∏ i, d i` is coprime to `W`, and
3. the product `∏ i, d i` is squarefree.

## Main definitions

* `Finset.permissibleSupport`: the finset of permissible tuples.
* `Finsupp.HasPermissibleSupport`: the support of `l` consists of permissible tuples.
-/

@[expose] public section

open Nat Finset

variable {k : ℕ} (R W : ℕ) (d : Fin k → ℕ)

section Conditions

namespace Finset

variable (k) in
/-- The tuples whose product is at most `R`, coprime to `W`, and squarefree. -/
@[pg_tag "bg246" "def_adm_support"]
noncomputable def permissibleSupport : Finset (Fin k → ℕ) :=
  { d ∈ finMulAntidiagLE (Fin k) R | (∏ i, d i).Coprime W ∧ Squarefree (∏ i, d i) }

variable {R W d}

@[pg_tag "bg246" "def_adm_support"]
theorem mem_permissibleSupport_iff : d ∈ permissibleSupport k R W ↔
    ∏ i, d i ≤ R ∧ (∏ i, d i).Coprime W ∧ Squarefree (∏ i, d i) := by
  simp_rw [permissibleSupport, mem_filter, mem_finMulAntidiagLE_iff]
  refine and_congr_left fun ⟨h₂, h₃⟩ ↦ ?_
  grind [prod_ne_zero_iff.mp h₃.ne_zero]

theorem permissibleSupport_subset_finMulAntidiagLE :
    permissibleSupport k R W ⊆ finMulAntidiagLE (Fin k) R := filter_subset _ _

theorem permissibleSupport_subset_filter_finMulAntidiagLE_squarefree :
    permissibleSupport k R W ⊆ {d ∈ finMulAntidiagLE (Fin k) R | Squarefree (∏ i, d i)} := by
  grind [permissibleSupport]

theorem mem_permissibleSupport_iff' : d ∈ permissibleSupport k R W ↔
    (∀ i, d i ≠ 0) ∧ ∏ i, d i ≤ R ∧ (∏ i, d i).Coprime W ∧ Squarefree (∏ i, d i) := by
  simp_rw [mem_permissibleSupport_iff]
  refine .symm <| and_iff_right_of_imp fun ⟨h₁, h₂, h₃⟩ ↦ ?_
  grind [prod_ne_zero_iff.mp h₃.ne_zero]

theorem mem_permissibleSupport_of_dvd {r : Fin k → ℕ} (hr : r ∈ permissibleSupport k R W)
    (hdvd : ∀ i, d i ∣ r i) : d ∈ permissibleSupport k R W := by
  rw [mem_permissibleSupport_iff'] at hr
  rw [mem_permissibleSupport_iff]
  have hdr : ∏ i, d i ∣ ∏ i, r i := prod_dvd_prod_of_dvd _ _ (by grind)
  grw [le_of_dvd (prod_pos (by grind)) hdr]
  exact ⟨hr.2.1, hr.2.2.1.of_dvd_left hdr, hr.2.2.2.squarefree_of_dvd hdr⟩

theorem squarefree_of_mem_permissibleSupport {r : Fin k → ℕ} (hr : r ∈ permissibleSupport k R W)
    (i : Fin k) : Squarefree (r i) := by
  rw [mem_permissibleSupport_iff] at hr
  exact hr.2.2.squarefree_of_dvd <| dvd_prod_of_mem _ <| by simp

end Finset

end Conditions

section HasPermissibleSupport

variable (l : (Fin k → ℕ) →₀ ℝ)

/-- A weight `l` on tuples `d : Fin k → ℕ` has permissible support when its support is contained in
`Finset.permissibleSupport R W`. -/
@[pg_tag "bg246" "def_adm_support"]
def Finsupp.HasPermissibleSupport : Prop := l.support ⊆ permissibleSupport k R W

variable {R W} {l}

namespace Finsupp

/-- `l` has permissible support iff, pointwise, `l d ≠ 0` is equivalent to the three permissibility
conditions holding for `d`. -/
lemma hasPermissibleSupport_iff_forall : l.HasPermissibleSupport R W ↔ ∀ d, l d ≠ 0 →
      ∏ i, d i ≤ R ∧ (∏ i, d i).Coprime W ∧ Squarefree (∏ i, d i) := by
  simp [HasPermissibleSupport, mem_permissibleSupport_iff, Finset.subset_iff]

lemma HasPermissibleSupport.of_forall
    (h : ∀ d, l d ≠ 0 → ∏ i, d i ≤ R ∧ (∏ i, d i).Coprime W ∧ Squarefree (∏ i, d i)) :
    l.HasPermissibleSupport R W := hasPermissibleSupport_iff_forall.mpr h

namespace HasPermissibleSupport

/-- The support of `l` is contained in the permissible set. -/
lemma support_subset (hl : l.HasPermissibleSupport R W) : l.support ⊆ permissibleSupport k R W := hl

/-- `l d ≠ 0` implies that the product `∏ i, d i` is at or below the sieve truncation `R`. -/
lemma prod_lt_R_of_ne_zero (hl : l.HasPermissibleSupport R W) {d : Fin k → ℕ} (hd : l d ≠ 0) :
    ∏ i, d i ≤ R := (mem_permissibleSupport_iff.mp (hl <| by simpa)).1

/-- `l d ≠ 0` implies that the product `∏ i, d i` is coprime to `W`. -/
lemma coprime_prod_W_of_ne_zero (hl : l.HasPermissibleSupport R W) {d : Fin k → ℕ}
    (hd : l d ≠ 0) : Coprime (∏ i, d i) W := (mem_permissibleSupport_iff.mp (hl <| by simpa)).2.1

/-- `l d ≠ 0` implies that the product `∏ i, d i` is squarefree. -/
lemma squarefree_prod_of_ne_zero (hl : l.HasPermissibleSupport R W) {d : Fin k → ℕ}
    (hd : l d ≠ 0) : Squarefree (∏ i, d i) := (mem_permissibleSupport_iff.mp (hl <| by simpa)).2.2

/-- `l d ≠ 0` implies that each `d i` is squarefree. -/
lemma squarefree_of_ne_zero (hl : l.HasPermissibleSupport R W) {d : Fin k → ℕ}
    (hd : l d ≠ 0) (i : Fin k) : Squarefree (d i) :=
  squarefree_of_mem_permissibleSupport (hl <| by simpa) _

/-- `l d ≠ 0` implies that each `d i ≠ 0`. -/
lemma ne_zero_of_ne_zero (hl : l.HasPermissibleSupport R W) {d : Fin k → ℕ}
    (hd : l d ≠ 0) (i : Fin k) : d i ≠ 0 :=
  (hl.squarefree_of_ne_zero hd i).ne_zero

end Finsupp.HasPermissibleSupport
