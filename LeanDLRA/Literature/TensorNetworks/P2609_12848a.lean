import Mathlib
import LeanDLRA.Matrix.LowRankDistance

/-!
# Results of arXiv 2609.12848: Diversifying MPS time evolution using BUGs

This module formalizes the structural facts of Secs. II A–B of arXiv 2609.12848 (MPS bond
dimensions near the chain ends). A chain of `k + l` sites with local dimension `d` is a function
`ψ : (Fin (k + l) → Fin d) → ℝ`, and its bond dimension across the cut after the first `k` sites is
the rank of the unfolding `unfold ψ : Matrix (Fin k → Fin d) (Fin l → Fin d) ℝ`, which is the
canonical bond dimension of the state at that cut. The bond cap is called `M` as in the paper.

Proved:

* `rank_unfold_le_left`, `rank_unfold_le_right`, `rank_unfold_le_min`: the bond dimension at a cut
  is at most `d ^ k` and at most `d ^ l`, the product of the mode sizes on either side.
* `distLR_unfold_eq_zero_of_pow_le`: if `d ^ m ≤ M` then the unfolding has rank at most `M`, so
  truncating it to bond dimension `M` (distance `distLR M`) changes nothing. The log form
  `distLR_unfold_eq_zero_of_lt_log` states the paper's range `m < log M / log d` (with `2 ≤ d`,
  `0 < M`) and is the statement "for the first `m < log M / log d` sites no truncation occurs".
* `example_unfold_no_truncation`: the hypotheses are satisfiable (`d = 2`, `M = 8`, `m = 2`).

Not formalized: the augmentation and the BUG sweeps of Secs. II B–C (the MPS recursion, the QR of
`[K(t₀), K(t₀+dt)]`, the Galerkin core step and the SVD truncation). The `2M`/`4M` bond bounds of
those steps, the MPS integrator and the midpoint (second-order) analysis are not in LeanDLRA and
are left out. The statement "augmentation has no effect" near the ends is the algorithmic
consequence of the bound proved here and is not separately formalized.
-/

open Set Filter Topology Finset
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2609_12848

/-- The unfolding of a chain `ψ` of `k + l` sites across the cut after the first `k` sites: the
row index runs over the left sites, the column index over the right sites. -/
def unfold {d k l : ℕ} (ψ : (Fin (k + l) → Fin d) → ℝ) : Matrix (Fin k → Fin d) (Fin l → Fin d) ℝ :=
  Matrix.of fun a b => ψ (Fin.append a b)

/-- Bond dimension at the cut after the first `k` sites is at most `d ^ k`, the number of
left configurations (arXiv 2609.12848, Secs. II A–B). -/
theorem rank_unfold_le_left {d k l : ℕ} (ψ : (Fin (k + l) → Fin d) → ℝ) :
    (unfold ψ).rank ≤ d ^ k := by
  refine (Matrix.rank_le_card_height _).trans ?_
  simp

/-- Bond dimension at the cut after the first `k` sites is at most `d ^ l`, the number of right
configurations. -/
theorem rank_unfold_le_right {d k l : ℕ} (ψ : (Fin (k + l) → Fin d) → ℝ) :
    (unfold ψ).rank ≤ d ^ l := by
  refine (Matrix.rank_le_card_width _).trans ?_
  simp

/-- The bond dimension is at most the smaller of the two mode products. -/
theorem rank_unfold_le_min {d k l : ℕ} (ψ : (Fin (k + l) → Fin d) → ℝ) :
    (unfold ψ).rank ≤ min (d ^ k) (d ^ l) :=
  le_min (rank_unfold_le_left ψ) (rank_unfold_le_right ψ)

/-- Near the chain end, with bond cap `M` and `d ^ m ≤ M`, the bond dimension across the cut after
`m` sites is at most `M`, so the truncation to bond dimension `M` has zero error: no truncation
occurs (arXiv 2609.12848, Secs. II A–B). -/
theorem distLR_unfold_eq_zero_of_pow_le {d m l M : ℕ} (ψ : (Fin (m + l) → Fin d) → ℝ)
    (hdM : d ^ m ≤ M) : LeanDLRA.distLR M (unfold ψ) = 0 :=
  LeanDLRA.distLR_eq_zero_of_rank_le ((rank_unfold_le_left ψ).trans hdM)

/-- The paper's range: for `m < log M / log d` (with `2 ≤ d` and `0 < M`) the first `m` sites carry
bond dimension at most `d ^ m < M`, so no truncation occurs there. -/
theorem distLR_unfold_eq_zero_of_lt_log {d m l M : ℕ} (ψ : (Fin (m + l) → Fin d) → ℝ)
    (hd : 2 ≤ d) (hM : 0 < M) (hm : (m : ℝ) < Real.log M / Real.log d) :
    LeanDLRA.distLR M (unfold ψ) = 0 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hlogd : 0 < Real.log d := Real.log_pos (by exact_mod_cast (by omega : 1 < d))
  have h1 : (m : ℝ) * Real.log d < Real.log M := by
    rwa [lt_div_iff₀ hlogd] at hm
  have h2 : Real.log ((d : ℝ) ^ m) < Real.log M := by
    rw [Real.log_pow]; exact h1
  have hpos : (0 : ℝ) < (d : ℝ) ^ m := pow_pos hd' m
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have h3 : (d : ℝ) ^ m < M := (Real.log_lt_log_iff hpos hMpos).1 h2
  have h4 : d ^ m ≤ M := by exact_mod_cast h3.le
  exact distLR_unfold_eq_zero_of_pow_le ψ h4

/-- Non-vacuity: `d = 2`, `M = 8`, `m = 2` satisfies `m < log M / log d` (since
`log 8 / log 2 = 3`), so the no-truncation statement applies to the chain with `m = 2` left sites
and `l = 3` right sites. -/
example (ψ : (Fin (2 + 3) → Fin 2) → ℝ) : LeanDLRA.distLR 8 (unfold ψ) = 0 := by
  apply distLR_unfold_eq_zero_of_lt_log ψ (by norm_num) (by norm_num)
  have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  norm_num only [Nat.cast_ofNat]
  rw [h8, lt_div_iff₀ hlog2]
  linarith

end LeanDLRA.Literature.P2609_12848
