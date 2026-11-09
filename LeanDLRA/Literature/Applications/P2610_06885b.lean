import Mathlib
import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Literature.Applications.P2610_06885a

/-!
# Results of arXiv 2610.06885: local low-rank approximability of Bellman targets (Lemma 1)

This module formalizes Lemma 1 of arXiv 2610.06885 (Section 3.1) up to the universal
approximation step. `G = [A; C] = stackG A C` is the augmented matrix (13) at a center `x_j`,
with `A` of `r` rows (`S Vᵀ ∇f₀(x_j)`) and `C` of `r_r` rows (`C_r`), and `G_r` its rank-`r`
truncation (`LeanDLRA.EckartYoung.truncation`).

* `norm_sub_truncation_eq_tail`: `‖G − G_r‖_F = (∑_{r ≤ i < r + r_r} σ_i(G)²)^{1/2}`, the
  Eckart–Young–Mirsky quantity `ε_EYM(r_r)` of (12), for `G` of rank `≤ r + r_r`.
* `lipschitz_truncation_error`, `local_truncation_error` (step (32)): `rank G_r ≤ r`, and
  `|F(G x) − F(G_r x)| ≤ L R_X ε_EYM(r_r)` for every `L`-Lipschitz `F` and `‖x‖ ≤ R_X`.
* `lipschitz_of_block` (eq. (30)): Lipschitz constants `L₁`, `L₂` in the dynamics and reward
  blocks of `z ∈ ℝ^{r + r_r}` combine to `√(L₁² + L₂²)`.
* `maxmin_decomposition`, `lipschitz_iSup_iInf` (eqs. (28)–(29)): a decomposition
  `Φ(x, i, j) ≈ Ψ(G x, i, j)` of the payoff of every strategy pair, with error `η`, passes to the
  Bellman target `y = max_i min_j Φ` with the reduced target `F = max_i min_j Ψ`, which keeps the
  Lipschitz constant. The paper's Steps 1–3 decompose the payoff of one strategy pair and never
  take the max-min ((15) writes the target as the payoff of a fixed pair, and the expectations
  in (24)–(25) are over that pair), so its additive `F_j` of (28) does not describe the max-min
  target; with `F_j` the max-min of the reduced payoffs the argument goes through with the
  paper's constants.
* `local_bellman_target_error` (Lemma 1 (ii) without (33)): for `x` in the ball,
  `|y(x) − F(G_r x)| ≤ C_EYM ε_EYM(r_r) + η` with `C_EYM = √(L_{r₀}² + (γ Lϕ ‖w_out‖)²) R_X` of
  (14), where `F ∘ G_r` depends on `x` only through the rank-`r` feature `G_r x`.

Conditional parts and narrowings. The per-pair remainder bound (27), `η = C₁δ + C₂δ²`, is a
hypothesis of `local_bellman_target_error` (`hdec`): its derivation from the Taylor bound (18)
and the Lipschitz bound (19) (Steps 1–3, eqs. (15)–(27)) is not formalized, and neither is the
Taylor bound itself. The strategy sets are arbitrary nonempty types and the payoffs are assumed
bounded for each state. The universal approximation step (33) is not in Mathlib, so the network
`V̂_j` of (10) and the term `ε` of (11) are not constructed; Lemma 1 (i) is proved for the
rank-`r` feature matrix `G_r` (the paper's `Ŵ_j = β Σ_r V_rᵀ` has the same row space).

Core definitions used: `LeanDLRA.EckartYoung.truncation`, `rank_truncation_le`,
`norm_sub_truncation`, `rank_eq_finrank_range` and the Frobenius norm `LeanDLRA.Frobenius`. Local
addition: `stackG` (the stacked matrix of (13)). From the sibling module `P2610_06885a`:
`norm_toEuclideanLin_le_frob` and the max-min bound `abs_iSup_iInf_sub_le` of Prop. 1 (this
module needs the version of `P2610_06885a` that contains it).
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

/-- **Lemma 1, truncation step** (arXiv 2610.06885, Lemma 1 (i) for `G_r` and step (32), with
`C_EYM = L R_X`).
Let `G = [A; C] = stackG A C` be the stacked matrix of eq. (13), with `A` of `r` rows and `C`
of `r_r` rows. Then:
* `rank (G_r) ≤ r` for the rank-`r` truncation `G_r = G V_r V_rᵀ`;
* for every `L`-Lipschitz `F` on `ℝ^{r+r_r}` and every `x` with `‖x‖ ≤ R_X`,
  `|F(G x) − F(G_r x)| ≤ L R_X (∑_{r ≤ i < r+r_r} σ_i(G)²)^{1/2}`, which is
  `C_EYM · ε_EYM(r_r)` with `ε_EYM` the tail sum of eq. (12).
The dimension condition `r + r_r ≤ n` is the regime in which `G` has `r + r_r` singular values
of interest. The Lipschitz constant `L` is a parameter; for the reduced Bellman target it is the
constant of (30) (`lipschitz_of_block`, used in `local_bellman_target_error`). -/
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

/-! ### Lemma 1, Steps 3–4: the decomposition passes through the max-min -/

/-- The max-min `z ↦ max_i min_j Ψ(z, i, j)` of payoffs that are `L`-Lipschitz in `z` (for every
strategy pair) is `L`-Lipschitz. This is how the Lipschitz bound (30) of arXiv 2610.06885
survives the max-min of the Bellman operator; it is `abs_iSup_iInf_sub_le` (Prop. 1). -/
theorem lipschitz_iSup_iInf {E I J : Type*} [SeminormedAddCommGroup E] [Nonempty I] [Nonempty J]
    (Ψ : E → I → J → ℝ) (hb : ∀ z, ∃ M, ∀ i j, |Ψ z i j| ≤ M) {L : ℝ}
    (hL : ∀ i j z z', |Ψ z i j - Ψ z' i j| ≤ L * ‖z - z'‖) (z z' : E) :
    |(⨆ i, ⨅ j, Ψ z i j) - ⨆ i, ⨅ j, Ψ z' i j| ≤ L * ‖z - z'‖ := by
  obtain ⟨M, hM⟩ := hb z
  obtain ⟨M', hM'⟩ := hb z'
  exact abs_iSup_iInf_sub_le (M := |M| + |M'|)
    (fun i j => (hM i j).trans ((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))))
    (fun i j => (hM' i j).trans ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))))
    (fun i j => hL i j z z')

/-- **Eq. (29) of arXiv 2610.06885, through the max-min.** Suppose that for every strategy pair
`(i, j)` the mixed-strategy Bellman payoff `Φ(x, i, j)` is within `η` of a reduced payoff
`Ψ(G x, i, j)` on a set `B` (the paper's (24)–(27), which its proof derives for one strategy pair
at a time, with `η = C₁δ + C₂δ²` on the ball `B(x_j, δ)`). Then the Bellman target
`y(x) = max_i min_j Φ(x, i, j)` satisfies `|y(x) − F(G x)| ≤ η` on `B` with the reduced target
`F(z) = max_i min_j Ψ(z, i, j)`. The paper's Step 3 decomposes the payoff of a single strategy
pair and does not take the max-min; this lemma supplies that step (the max-min is 1-Lipschitz,
`abs_iSup_iInf_sub_le`), so `F_j` of (28) is the max-min of the reduced payoffs. -/
theorem maxmin_decomposition {E Z I J : Type*} [Nonempty I] [Nonempty J] (Φ : E → I → J → ℝ)
    (Ψ : Z → I → J → ℝ) (G : E → Z) (hΦb : ∀ x, ∃ M, ∀ i j, |Φ x i j| ≤ M)
    (hΨb : ∀ z, ∃ M, ∀ i j, |Ψ z i j| ≤ M) {B : Set E} {η : ℝ}
    (hdec : ∀ x ∈ B, ∀ i j, |Φ x i j - Ψ (G x) i j| ≤ η) (x : E) (hx : x ∈ B) :
    |(⨆ i, ⨅ j, Φ x i j) - ⨆ i, ⨅ j, Ψ (G x) i j| ≤ η := by
  obtain ⟨M, hM⟩ := hΦb x
  obtain ⟨M', hM'⟩ := hΨb (G x)
  exact abs_iSup_iInf_sub_le (M := |M| + |M'|)
    (fun i j => (hM i j).trans ((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))))
    (fun i j => (hM' i j).trans ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))))
    (hdec x hx)

/-- **Eq. (30) of arXiv 2610.06885 (block Lipschitz constant).** Split `z ∈ ℝ^{r + r_r}` into the
first `r` coordinates `z₁` (the dynamics block `A_j x`) and the last `r_r` coordinates `z₂` (the
reward block `C_r x`). If `|F z − F z'| ≤ L₁ ‖z₁ − z₁'‖ + L₂ ‖z₂ − z₂'‖`, then `F` is
`√(L₁² + L₂²)`-Lipschitz for the Euclidean norm (Cauchy–Schwarz in `ℝ²`). -/
theorem lipschitz_of_block {r rr : ℕ} (F : EuclideanSpace ℝ (Fin (r + rr)) → ℝ) {L₁ L₂ : ℝ}
    (hF : ∀ z z' : EuclideanSpace ℝ (Fin (r + rr)), |F z - F z'| ≤
      L₁ * √(∑ k : Fin r, (z (Fin.castAdd rr k) - z' (Fin.castAdd rr k)) ^ 2) +
        L₂ * √(∑ k : Fin rr, (z (Fin.natAdd r k) - z' (Fin.natAdd r k)) ^ 2))
    (z z' : EuclideanSpace ℝ (Fin (r + rr))) :
    |F z - F z'| ≤ √(L₁ ^ 2 + L₂ ^ 2) * ‖z - z'‖ := by
  set a := √(∑ k : Fin r, (z (Fin.castAdd rr k) - z' (Fin.castAdd rr k)) ^ 2)
  set b := √(∑ k : Fin rr, (z (Fin.natAdd r k) - z' (Fin.natAdd r k)) ^ 2)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hnorm : ‖z - z'‖ = √(a ^ 2 + b ^ 2) := by
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), ← Fin.sum_univ_add
        (f := fun k => (z k - z' k) ^ 2), ← Real.sqrt_sq (norm_nonneg _),
      EuclideanSpace.real_norm_sq_eq]
    simp [PiLp.sub_apply]
  rw [hnorm, ← Real.sqrt_mul (by positivity)]
  refine (hF z z').trans (Real.le_sqrt_of_sq_le ?_)
  nlinarith [sq_nonneg (L₁ * b - L₂ * a)]

/-- **Lemma 1 (ii) of arXiv 2610.06885 without the universal-approximation step.** Let
`G = [A; C] = stackG A C` be the augmented matrix (13) at a center `x_j`, and `G_r` its rank-`r`
truncation. Let `Φ(x, i, j)` be the mixed-strategy Bellman payoff for the strategy pair `(i, j)`
and `Ψ(z, i, j)` a reduced payoff that is `L_dyn`-Lipschitz in the dynamics block and
`L_rew`-Lipschitz in the reward block of `z` (in the paper `L_dyn = γ Lϕ ‖w_out‖`,
`L_rew = L_{r₀}`), with `|Φ(x, i, j) − Ψ(G x, i, j)| ≤ η` on `B` for every pair (the per-pair
remainder bound (27), `η = C₁δ + C₂δ²`, which is a hypothesis here). Then for `x ∈ B` with
`‖x‖ ≤ R_X` the Bellman target `y(x) = max_i min_j Φ(x, i, j)` and the reduced target
`F(z) = max_i min_j Ψ(z, i, j)` evaluated at the rank-`r` feature `G_r x` satisfy
`|y(x) − F(G_r x)| ≤ C_EYM ε_EYM(r_r) + η`, with `C_EYM = √(L_rew² + L_dyn²) R_X` as in (14).
This is (11) with `ε = 0` and `V̂_j` replaced by `F ∘ G_r`; the network `V̂_j` of (10) needs the
universal approximation theorem (33), which is not formalized. -/
theorem local_bellman_target_error (n r rr : ℕ) (hkn : r + rr ≤ n)
    (A : Matrix (Fin r) (Fin n) ℝ) (C : Matrix (Fin rr) (Fin n) ℝ)
    {I J : Type*} [Nonempty I] [Nonempty J] (Φ : EuclideanSpace ℝ (Fin n) → I → J → ℝ)
    (Ψ : EuclideanSpace ℝ (Fin (r + rr)) → I → J → ℝ) (hΦb : ∀ x, ∃ M, ∀ i j, |Φ x i j| ≤ M)
    (hΨb : ∀ z, ∃ M, ∀ i j, |Ψ z i j| ≤ M) {Ldyn Lrew : ℝ}
    (hΨ : ∀ i j, ∀ z z' : EuclideanSpace ℝ (Fin (r + rr)), |Ψ z i j - Ψ z' i j| ≤
      Ldyn * √(∑ k : Fin r, (z (Fin.castAdd rr k) - z' (Fin.castAdd rr k)) ^ 2) +
        Lrew * √(∑ k : Fin rr, (z (Fin.natAdd r k) - z' (Fin.natAdd r k)) ^ 2))
    {B : Set (EuclideanSpace ℝ (Fin n))} {η : ℝ}
    (hdec : ∀ x ∈ B, ∀ i j, |Φ x i j - Ψ (toEuclideanLin (stackG A C) x) i j| ≤ η)
    {RX : ℝ} (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ B) (hxR : ‖x‖ ≤ RX) :
    (truncation (stackG A C) r).rank ≤ r ∧
      |(⨆ i, ⨅ j, Φ x i j) - ⨆ i, ⨅ j, Ψ (toEuclideanLin (truncation (stackG A C) r) x) i j| ≤
        √(Lrew ^ 2 + Ldyn ^ 2) * RX *
          √(∑ i ∈ Ico r (r + rr), (toEuclideanLin (stackG A C)).singularValues i ^ 2) + η := by
  have hFL : ∀ z z' : EuclideanSpace ℝ (Fin (r + rr)),
      |(⨆ i, ⨅ j, Ψ z i j) - ⨆ i, ⨅ j, Ψ z' i j| ≤ √(Lrew ^ 2 + Ldyn ^ 2) * ‖z - z'‖ := by
    intro z z'
    refine lipschitz_iSup_iInf Ψ hΨb (fun i j y y' => ?_) z z'
    rw [add_comm (Lrew ^ 2)]
    exact lipschitz_of_block (fun y => Ψ y i j) (hΨ i j) y y'
  have h1 := (local_truncation_error n r rr A C hkn (fun z => ⨆ i, ⨅ j, Ψ z i j)
    (√(Lrew ^ 2 + Ldyn ^ 2)) (Real.sqrt_nonneg _) hFL RX x hxR)
  have h2 := maxmin_decomposition Φ Ψ (toEuclideanLin (stackG A C)) hΦb hΨb hdec x hx
  refine ⟨h1.1, ?_⟩
  have t := abs_sub_le (⨆ i, ⨅ j, Φ x i j) (⨆ i, ⨅ j, Ψ (toEuclideanLin (stackG A C) x) i j)
    (⨆ i, ⨅ j, Ψ (toEuclideanLin (truncation (stackG A C) r) x) i j)
  have h1' := h1.2
  linarith

end LeanDLRA.Literature.P2610_06885
