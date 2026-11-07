import Mathlib
import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Literature.Applications.P2610_06885a

/-!
# Results of arXiv 2610.06885: local low-rank truncation error (Lemma 1, core)

This module formalizes the linear-algebra core of Lemma 1 (low-rank local approximability of
Bellman targets, Section 3.1). For the stacked matrix `G = [A; C]` of Lemma 1 (eq. (13)), with
`A` having `r` rows (playing `S Vᵀ ∇f₀(x_j)`) and `C` having `r_r` rows (playing `C_r`), it proves:

* `local_truncation_error`, part 1 (Lemma 1 (i), for the truncated matrix): the rank-`r`
  truncation `G_r = G V_r V_rᵀ` of the stacked matrix `G = stackG A C` has rank `≤ r`.
  The stacked matrix has `r + r_r` rows, so `rank G ≤ r + r_r` (used in the proof).
* `norm_sub_truncation_eq_tail`: the Frobenius error of truncating `G` to rank `r` equals
  `(∑_{r ≤ i < r + r_r} σ_i(G)²)^{1/2}`, which is the Eckart–Young–Mirsky quantity `ε_EYM(r_r)`
  of eq. (12) for `G` of rank `≤ r + r_r`.
* `lipschitz_truncation_error` and `local_truncation_error`, part 2 (step (32)): for any
  `L`-Lipschitz map `F` on `ℝ^{r+r_r}` (Euclidean norm), `|F(G x) − F(G_r x)| ≤ L R_X ε_EYM(r_r)`
  for `‖x‖ ≤ R_X`. This is the constant `C_EYM = L R_X` of eq. (14) with `L` the Lipschitz
  constant of `F`.

The Lipschitz constant `L` of `F` is a parameter (`hF`); the paper bounds it in (30) by a block
gradient argument, which is not formalized. The statements are about a general finite-dimensional
real matrix `G` and a Lipschitz `F`, not about the Bellman operator.

Left out (not formalized): Steps 1–3 of the proof, namely the Bellman target decomposition
`y(x) = F(G(x_j) x) + ϵ_rem(x)` with the remainder bounds `C₁δ + C₂δ²` (eqs. (15)–(29)), which
needs the stochastic max-min game and Assumption 1; the universal approximation step (33), which
Mathlib does not provide, so the network `V̂_j` with `|F(ψ(x)) − V̂_j(x)| ≤ ε` and the
rank bound `rank W_j ≤ r + r_r` of the network weight are not constructed; and the covering
argument giving the finite set `{x_j}`. Hence the full statement (11) of Lemma 1 is not proved here.

Core definitions used: `LeanDLRA.EckartYoung.truncation`, `rank_truncation_le`,
`norm_sub_truncation`, `rank_eq_finrank_range`, `sq_norm_toEuclideanLin`, `sq_norm_row`, and the
Frobenius norm `LeanDLRA.Frobenius`. Local additions: `stackG` (the stacked matrix
`[A; C]` of eq. (13)) and the lemmas above; `norm_toEuclideanLin_le_frob` comes from the
sibling module `P2610_06885a`.
-/

open scoped RealInnerProductSpace LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2610_06885

open Finset Matrix LeanDLRA.EckartYoung

/-- **Tail error of the truncation** (eq. (12) of arXiv 2610.06885). If `G` has rank `≤ k` and
`k ≤ n`, then the Frobenius error of its rank-`r` truncation is
`‖G − G_r‖_F = (∑_{r ≤ i < k} σ_i(G)²)^{1/2}`. For `k = r + r_r` this is the quantity
`ε_EYM(r_r)` of the paper. -/
theorem norm_sub_truncation_eq_tail {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (G : Matrix m n ℝ) (r k : ℕ) (hk : G.rank ≤ k) (hkn : k ≤ Fintype.card n) :
    ‖G - truncation G r‖ = √(∑ i ∈ Ico r k, (toEuclideanLin G).singularValues i ^ 2) := by
  rw [norm_sub_truncation]
  congr 1
  refine (Finset.sum_subset (Finset.Ico_subset_Ico_right hkn) fun i hi hni => ?_).symm
  have hik : k ≤ i := by
    by_contra h
    exact hni (Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hi).1, not_le.mp h⟩)
  have h0 : (toEuclideanLin G).singularValues i = 0 := by
    rw [LinearMap.singularValues_eq_zero_iff_le_finrank_range, ← rank_eq_finrank_range]
    omega
  simp [h0]

/-- **Lipschitz truncation bound** (step (32) of the proof of Lemma 1). If `F` is `L`-Lipschitz
for the Euclidean norm, then `|F(G x) − F(G_r x)| ≤ L ‖G − G_r‖_F ‖x‖`. -/
theorem lipschitz_truncation_error {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (F : EuclideanSpace ℝ m → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ∀ z z' : EuclideanSpace ℝ m, |F z - F z'| ≤ L * ‖z - z'‖)
    (G : Matrix m n ℝ) (r : ℕ) (x : EuclideanSpace ℝ n) :
    |F (toEuclideanLin G x) - F (toEuclideanLin (truncation G r) x)| ≤
      L * ‖G - truncation G r‖ * ‖x‖ := by
  have hdiff : toEuclideanLin G x - toEuclideanLin (truncation G r) x =
      toEuclideanLin (G - truncation G r) x := by
    rw [map_sub, LinearMap.sub_apply]
  calc |F (toEuclideanLin G x) - F (toEuclideanLin (truncation G r) x)|
      ≤ L * ‖toEuclideanLin G x - toEuclideanLin (truncation G r) x‖ := hF _ _
    _ = L * ‖toEuclideanLin (G - truncation G r) x‖ := by rw [hdiff]
    _ ≤ L * (‖x‖ * ‖G - truncation G r‖) :=
        mul_le_mul_of_nonneg_left (norm_toEuclideanLin_le_frob _ x) hL
    _ = L * ‖G - truncation G r‖ * ‖x‖ := by ring

/-- The stacked matrix `G = [A; C]` of eq. (13) of arXiv 2610.06885: `A` has `r` rows
(`S Vᵀ ∇f₀(x_j)`), `C` has `r_r` rows (`C_r`). -/
def stackG {n r rr : ℕ} (A : Matrix (Fin r) (Fin n) ℝ) (C : Matrix (Fin rr) (Fin n) ℝ) :
    Matrix (Fin (r + rr)) (Fin n) ℝ :=
  Fin.append A C

/-- **Lemma 1 core** (arXiv 2610.06885, Lemma 1 (i) and step (32), with `C_EYM = L R_X`).
Let `G = [A; C] = stackG A C` be the stacked matrix of eq. (13), with `A` of `r` rows and `C`
of `r_r` rows. Then:
* `rank (G_r) ≤ r` for the rank-`r` truncation `G_r = G V_r V_rᵀ`;
* for every `L`-Lipschitz `F` on `ℝ^{r+r_r}` and every `x` with `‖x‖ ≤ R_X`,
  `|F(G x) − F(G_r x)| ≤ L R_X (∑_{r ≤ i < r+r_r} σ_i(G)²)^{1/2}`, which is
  `C_EYM · ε_EYM(r_r)` with `ε_EYM` the tail sum of eq. (12).
The dimension condition `r + r_r ≤ n` is the regime in which `G` has `r + r_r` singular values
of interest. The Lipschitz constant `L` is a parameter. -/
theorem local_truncation_error (n r rr : ℕ)
    (A : Matrix (Fin r) (Fin n) ℝ) (C : Matrix (Fin rr) (Fin n) ℝ)
    (hkn : r + rr ≤ n)
    (F : EuclideanSpace ℝ (Fin (r + rr)) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ∀ z z' : EuclideanSpace ℝ (Fin (r + rr)), |F z - F z'| ≤ L * ‖z - z'‖)
    (RX : ℝ) (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ RX) :
    (truncation (stackG A C) r).rank ≤ r ∧
      |F (toEuclideanLin (stackG A C) x) -
          F (toEuclideanLin (truncation (stackG A C) r) x)| ≤
        L * RX * √(∑ i ∈ Ico r (r + rr), (toEuclideanLin (stackG A C)).singularValues i ^ 2) := by
  have hrank : (stackG A C).rank ≤ r + rr := rank_le_height (stackG A C)
  have h1 := lipschitz_truncation_error F L hL hF (stackG A C) r x
  rw [norm_sub_truncation_eq_tail (stackG A C) r (r + rr) hrank (by simpa using hkn)] at h1
  have h2 : L * √(∑ i ∈ Ico r (r + rr), (toEuclideanLin (stackG A C)).singularValues i ^ 2)
      * ‖x‖ ≤ L * √(∑ i ∈ Ico r (r + rr), (toEuclideanLin (stackG A C)).singularValues i ^ 2)
      * RX :=
    mul_le_mul_of_nonneg_left hx (by positivity)
  exact ⟨rank_truncation_le (stackG A C) r, h1.trans (h2.trans (le_of_eq (by ring)))⟩

end LeanDLRA.Literature.P2610_06885
