import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.Matrix.ProjectorSplitting
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Projectors
import LeanDLRA.OpenProblems.Curated.Classicala
import LeanDLRA.Training.InexactGradient

/-!
# Results of arXiv 2009.03887: Low-rank training for emerging memory technology

Gural, Nadeau, Tikekar and Murmann accumulate the gradient of a layer in a low-rank factorization,
sample by sample: the rank-`q = r + 1` matrix `L Rᵀ` gets an SVD through its small core, and is
brought back to rank `r`, either by dropping `σ_q` (biased LRT) or by an unbiased random mixing of
the smallest singular values.  This module proves the SVD of the factored update (Eq. (1):
`isThinSVD_factored`, `exists_isThinSVD_factored`, and `factoredSVD_cost_le`); the regret bound
with the paper's own perturbation constraint, with projection, boundedness and Eq. (8) derived
(`theorem1_regret`, `theorem1_regret_of_eq15`, `eq8_strongConvexity`, `eq15_sufficient`,
`theorem1_satisfiable`); the error of biased LRT (`IsBiasedStep.error_eq`,
`IsBiasedStep.norm_error`, `biased_accumulation_le`, `biased_sq_eq_of_uncorrelated`,
`eq19_sufficient`, `exists_biased_run`); and, in full, that the estimator of Sec. 4.1.2 is
unbiased, of rank at most `r` and of minimum variance among all unbiased estimators of rank at
most `r` on any probability space, for `Σ` and for the gradient itself
(`estimator_minimum_variance`, `lifted_minimum_variance`, `estimator_variance_eq`,
`exists_isMixer`, `estimator_isCompetitor`).

**False claim.** App. A.2 prints the minimum variance as `s₁²/k + s₂`.  It is `s₁²/k - s₂`, which is
the formula of Benzing et al. (2019) and what the paper's own value `2 σ_r σ_q` for `k = 1` needs
(`estimator_variance_of_pred`).  See `appA2_min_variance_formula_false`.

**Differences from the paper.**  `InexactGradient.regret_le_sqrt` already had Theorem 1 under the
stronger Eq. (15) with Eq. (8), boundedness and nonexpansiveness as hypotheses; it is used here, and
the rest is added.  The bound `‖G̃_B - ∑ᵢ dz⁽ⁱ⁾ a⁽ⁱ⁾ᵀ‖_F ≤ ∑ᵢ σ_q⁽ⁱ⁾` is not printed in the paper,
which gives the per-sample error and adds variances; both forms are here, and "uncorrelated" in
Eqs. (17), (19) is read as Frobenius orthogonality of the per-sample errors, which makes the
paper's `≈` an equality.  The paper does not prove minimality, citing Benzing et al.; the proof
here is a kernel vector of a matrix of rank `≤ r` (`sq_le_norm_sub_diagonal`).  Costs in Eq. (1) are
bookkeeping from assumed primitive costs, as Lean has no machine model.  The paper's `x₀` is `0/0`
if `s₁ = 0` and its Householder formula is `0/0` if `x₀ = e₁`; both are handled
(`estimator_of_s₁_eq_zero`, `exists_householder`).  The paper's indices are `1`-based, those of
the estimator here `0`-based.

**Not formalized.**  The accumulation (18) for unbiased LRT: only its per-sample value is proved,
because the paper's step is an unspecified "uncorrelated" heuristic about a random process.
Eqs. (16), (20) and Apps. A.1, A.3 are outside this slice.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2009_03887

/-! ### Eq. (1): the SVD of a factored low-rank update -/

section ThinSVD

variable {m n : Type*} [Fintype m] [Fintype n] {q : ℕ}

/-- `A = U diag(σ) Vᵀ` is a thin singular value decomposition with `q` components: orthonormal
columns, and nonnegative singular values in decreasing order. -/
structure IsThinSVD (A : Matrix m n ℝ) (U : Matrix m (Fin q) ℝ) (σ : Fin q → ℝ)
    (V : Matrix n (Fin q) ℝ) : Prop where
  orthU : Uᵀ * U = 1
  orthV : Vᵀ * V = 1
  antitone : Antitone σ
  nonneg : ∀ i, 0 ≤ σ i
  eq : A = U * Matrix.diagonal σ * Vᵀ

/-- **Eq. (1) of arXiv 2009.03887.**  From thin QR factorizations `L = Q_L R_L`, `R = Q_R R_R` and
an SVD `R_L R_Rᵀ = U_C Σ V_Cᵀ` of the `q × q` core, `L Rᵀ = (Q_L U_C) Σ (Q_R V_C)ᵀ` is an SVD.
Difference from the paper: `R_L`, `R_R` need not be triangular, only `Q_Lᵀ Q_L = Q_Rᵀ Q_R = I` is
used.  The operation count is `factoredSVD_cost_le`. -/
theorem isThinSVD_factored {L QL : Matrix m (Fin q) ℝ} {R QR : Matrix n (Fin q) ℝ}
    {RL RR UC VC : Matrix (Fin q) (Fin q) ℝ} {σ : Fin q → ℝ} (hQL : QLᵀ * QL = 1)
    (hL : L = QL * RL) (hQR : QRᵀ * QR = 1) (hR : R = QR * RR)
    (hC : IsThinSVD (RL * RRᵀ) UC σ VC) :
    IsThinSVD (L * Rᵀ) (QL * UC) σ (QR * VC) where
  orthU := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc QLᵀ, hQL, Matrix.one_mul,
      hC.orthU]
  orthV := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc QRᵀ, hQR, Matrix.one_mul,
      hC.orthV]
  antitone := hC.antitone
  nonneg := hC.nonneg
  eq := by
    have e := hC.eq
    calc L * Rᵀ = QL * (RL * RRᵀ) * QRᵀ := by
          rw [hL, hR, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = QL * UC * Matrix.diagonal σ * (QR * VC)ᵀ := by
          rw [e, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]

/-- The core SVD of Eq. (1) of arXiv 2009.03887: every square matrix has an SVD with decreasing
singular values (reindexing `LeanDLRA.SVD.exists_full_svd`). -/
theorem exists_isThinSVD_square (A : Matrix (Fin q) (Fin q) ℝ) :
    ∃ (U : Matrix (Fin q) (Fin q) ℝ) (σ : Fin q → ℝ) (V : Matrix (Fin q) (Fin q) ℝ),
      IsThinSVD A U σ V := by
  obtain ⟨Y, Z, em, en, hY, hZ, hM⟩ := LeanDLRA.SVD.exists_full_svd A
  have hcard : Fintype.card (Fin q) = q := Fintype.card_fin q
  let g : Fin q ≃ Fin q := em.trans (finCongr hcard)
  let h : Fin q ≃ Fin q := en.trans (finCongr hcard)
  let s : ℕ → ℝ := fun i => (Matrix.toEuclideanLin A).singularValues i
  let σ : Fin q → ℝ := fun i => s i
  have hg : ∀ i, ((g i : Fin q) : ℕ) = em i := fun i => by simp [g]
  have hh : ∀ i, ((h i : Fin q) : ℕ) = en i := fun i => by simp [h]
  refine ⟨Y.submatrix id g.symm, σ, Z.submatrix id h.symm, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.transpose_submatrix, ← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, hY,
      Matrix.submatrix_one_equiv]
  · rw [Matrix.transpose_submatrix, ← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, hZ,
      Matrix.submatrix_one_equiv]
  · intro i j hij
    exact (Matrix.toEuclideanLin A).singularValues_antitone hij
  · intro i
    exact (Matrix.toEuclideanLin A).singularValues_nonneg i
  · have hS : (Matrix.of fun i j ↦ if ((em i : ℕ) = en j) then
        (Matrix.toEuclideanLin A).singularValues (en j) else 0) =
        (Matrix.diagonal σ).submatrix g h := by
      ext i j
      simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.diagonal_apply]
      by_cases hij : ((em i : ℕ) = en j)
      · have : g i = h j := Fin.ext (by rw [hg, hh, hij])
        simp only [hij, this, ↓reduceIte, σ, s, hh]
      · have : g i ≠ h j := fun e => hij (by rw [← hg, ← hh, e])
        simp only [hij, this, ↓reduceIte]
    rw [hM, hS, Matrix.transpose_submatrix]
    ext i j
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, id]
    symm
    rw [← Equiv.sum_comp h]
    simp only [Equiv.symm_apply_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    rw [← Equiv.sum_comp g]
    simp only [Equiv.symm_apply_apply]

/-- **Eq. (1) of arXiv 2009.03887, existence.**  For `q ≤ n_o, n_i`, thin QR factorizations and an
SVD of the core give a thin SVD of `L Rᵀ` for all `L ∈ ℝ^{n_o × q}`, `R ∈ ℝ^{n_i × q}`.  The paper
leaves `q ≤ n_o, n_i` implicit in `Q_L ∈ ℝ^{n_o × q}`, `Q_R ∈ ℝ^{n_i × q}` being orthonormal. -/
theorem exists_isThinSVD_factored (L : Matrix m (Fin q) ℝ) (R : Matrix n (Fin q) ℝ)
    (hm : q ≤ Fintype.card m) (hn : q ≤ Fintype.card n) :
    ∃ (U : Matrix m (Fin q) ℝ) (σ : Fin q → ℝ) (V : Matrix n (Fin q) ℝ),
      IsThinSVD (L * Rᵀ) U σ V := by
  obtain ⟨QL, RL, hQL, hL⟩ := MatrixKSL.exists_qr L hm
  obtain ⟨QR, RR, hQR, hR⟩ := MatrixKSL.exists_qr R hn
  obtain ⟨UC, σ, VC, hC⟩ := exists_isThinSVD_square (RL * RRᵀ)
  exact ⟨_, σ, _, isThinSVD_factored hQL hL hQR hR hC⟩

/-- **The operation count of Eq. (1)**, `O((n_i + n_o + q) q²)` (arXiv 2009.03887, Sec. 4.1.1).
Lean has no machine model, so this is the bookkeeping only: if a QR of an `n × q` matrix costs at
most `C n q²` and the core product and the core SVD cost at most `C q³` each, and the two
basis updates `Q_L U_C`, `Q_R V_C` cost at most `C n q²`, the total is at most
`2 C (n_i + n_o + q) q²`.  The primitive costs are hypotheses. -/
theorem factoredSVD_cost_le {C ni no : ℝ} {q' : ℝ} {qrL qrR core svd upL upR : ℝ}
    (hqrL : qrL ≤ C * no * q' ^ 2) (hqrR : qrR ≤ C * ni * q' ^ 2) (hcore : core ≤ C * q' ^ 3)
    (hsvd : svd ≤ C * q' ^ 3) (hupL : upL ≤ C * no * q' ^ 2) (hupR : upR ≤ C * ni * q' ^ 2) :
    qrL + qrR + core + svd + upL + upR ≤ 2 * C * (ni + no + q') * q' ^ 2 := by
  nlinarith

end ThinSVD

/-! ### Theorem 1 and Eqs. (8), (15): regret of LRT-based SGD -/

section Regret

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `P` is a metric projection onto `F`: `P u` is a nearest point of `F` to `u`. -/
def IsMetricProj (F : Set E) (P : E → E) : Prop :=
  ∀ u, P u ∈ F ∧ ∀ v ∈ F, ‖u - P u‖ ≤ ‖u - v‖

/-- The projection `P_F` of Theorem 1 of arXiv 2009.03887 exists: the metric projection onto a
nonempty closed convex subset of a Hilbert space. -/
theorem exists_isMetricProj [CompleteSpace E] {F : Set E} (hne : F.Nonempty) (hcl : IsClosed F)
    (hconv : Convex ℝ F) : ∃ P : E → E, IsMetricProj F P := by
  have h := exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hconv
  choose P hPF hP using h
  refine ⟨P, fun u => ⟨hPF u, fun v hv => ?_⟩⟩
  rw [hP u]
  have : Nonempty F := hne.to_subtype
  exact ciInf_le ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩ (⟨v, hv⟩ : F)

/-- The metric projection onto a convex set does not increase the distance to points of the set
(the step of the proof of Theorem 1 of arXiv 2009.03887 that uses the projection `P_F`). -/
theorem IsMetricProj.norm_sub_le {F : Set E} {P : E → E} (hP : IsMetricProj F P)
    (hconv : Convex ℝ F) {w : E} (hw : w ∈ F) (u : E) : ‖P u - w‖ ≤ ‖u - w‖ := by
  obtain ⟨hPF, hmin⟩ := hP u
  have hinf : ‖u - P u‖ = ⨅ v : F, ‖u - v‖ := by
    have : Nonempty F := ⟨⟨w, hw⟩⟩
    exact le_antisymm (le_ciInf fun v => hmin v v.2)
      (ciInf_le ⟨0, by rintro _ ⟨v, rfl⟩; exact norm_nonneg _⟩ (⟨P u, hPF⟩ : F))
  have hin := (norm_eq_iInf_iff_real_inner_le_zero hconv hPF).1 hinf w hw
  have e : u - w = (u - P u) + (P u - w) := by abel
  have hsq : ‖P u - w‖ ^ 2 ≤ ‖u - w‖ ^ 2 := by
    rw [e, norm_add_sq_real]
    have e2 : ⟪u - P u, P u - w⟫ = -⟪u - P u, w - P u⟫ := by
      rw [← inner_neg_right, neg_sub]
    nlinarith [sq_nonneg ‖u - P u‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

/-- **Eq. (8) of arXiv 2009.03887**: for a `c`-strongly convex `f` with gradient `g` at `w`,
`f(w) + g·(v - w) + (c/2) ‖v - w‖² ≤ f(v)`.  The paper obtains it from `c I ⪯ ∇²f`; here it is
derived from strong convexity on a convex set containing `v`, `w`, which that Hessian bound implies,
and differentiability at `w`. -/
theorem eq8_strongConvexity [CompleteSpace E] {s : Set E} {f : E → ℝ} {c : ℝ} {w v g : E}
    (hf : StrongConvexOn s c f) (hw : w ∈ s) (hv : v ∈ s) (hg : HasGradientAt f g w) :
    f w + ⟪g, v - w⟫ + c / 2 * ‖v - w‖ ^ 2 ≤ f v := by
  set d := v - w with hd
  have hline : HasDerivAt (fun t : ℝ => f (w + t • d)) ⟪g, d⟫ 0 := by
    have := (hasGradientAt_iff_hasFDerivAt.1 hg).hasLineDerivAt d
    simpa [HasLineDerivAt, InnerProductSpace.toDual_apply_apply] using this
  have hslope := hline.tendsto_slope_zero_right
  have hbound : Tendsto (fun t : ℝ => f v - f w - (1 - t) * (c / 2 * ‖d‖ ^ 2)) (𝓝[>] 0)
      (𝓝 (f v - f w - (1 - 0) * (c / 2 * ‖d‖ ^ 2))) :=
    (Continuous.tendsto (by fun_prop) 0).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, t⁻¹ • (f (w + (0 + t) • d) - f (w + (0 : ℝ) • d)) ≤
      f v - f w - (1 - t) * (c / 2 * ‖d‖ ^ 2) := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    have ht0 : 0 < t := ht.1
    have hc := hf.2 hw hv (show 0 ≤ 1 - t by linarith [ht.2]) ht0.le (by ring)
    have e : (1 - t) • w + t • v = w + t • d := by
      rw [hd, smul_sub, sub_smul, one_smul]; abel
    have e2 : ‖w - v‖ = ‖d‖ := by rw [hd, norm_sub_rev]
    rw [e, e2] at hc
    simp only [smul_eq_mul, zero_add, zero_smul, add_zero] at hc ⊢
    rw [inv_mul_le_iff₀ ht0]
    nlinarith
  have := le_of_tendsto_of_tendsto hslope hbound hev
  nlinarith

/-- **Eq. (15) of arXiv 2009.03887** (Cauchy–Schwarz): the perturbation constraint of Theorem 1
holds if `‖ε‖ ≤ (c/2) ‖w - w⋆‖`; `v` stands for `w - w⋆` and `g̃ = g + ε`. -/
theorem eq15_sufficient {g ε v : E} {c : ℝ} (h : ‖ε‖ ≤ c / 2 * ‖v‖) :
    ⟪g, v⟫ - c / 2 * ‖v‖ ^ 2 ≤ ⟪g + ε, v⟫ := by
  have hcs : -(‖ε‖ * ‖v‖) ≤ ⟪ε, v⟫ := by
    have := real_inner_le_norm (-ε) v
    rw [inner_neg_left, norm_neg] at this
    linarith
  rw [inner_add_left]
  nlinarith [mul_le_mul_of_nonneg_right h (norm_nonneg v)]

/-- `∑_{t=1}^{n+1} h t = ∑_{t<n+1} h (t+1)`. -/
private lemma sum_Icc_one_eq (h : ℕ → ℝ) (n : ℕ) :
    ∑ t ∈ Finset.Icc 1 (n + 1), h t = ∑ t ∈ range (n + 1), h (t + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, sum_range_succ _ (n + 1)]

/-- **Theorem 1 of arXiv 2009.03887** with the paper's own perturbation constraint.  LRT-based SGD
`w^{t+1} = P_F(w^t - η_t g̃^t)`, `g̃^t = g^t + ε^t`, `η_t = 1/√t`, `t = 1, 2, …`, on `c`-strongly
convex `f^t` over a convex set `F` of diameter at most `D`, with `‖g^t‖ ≤ G`, `‖ε^t‖ ≤ E`, and
`g^t·(w^t - w⋆) - (c/2)‖w^t - w⋆‖² ≤ g̃^t·(w^t - w⋆)`, has
`R(T) ≤ (D²/2) √T + (G + E)² (√T - 1/2)` for `T ≥ 1`.

The library's `InexactGradient.regret_le_sqrt` assumes the stronger Eq. (15), and also Eq. (8), the
boundedness of the iterates and the projection inequality; here these are derived.  Differences
from the paper: `w⋆` is any point of `F` (the paper takes the offline minimizer, which is such a
point); `w¹ ∈ F` is explicit (the paper uses it silently through `‖w¹ - w⋆‖ ≤ D`); strong convexity
on `F` replaces `c I ⪯ ∇²f^t ⪯ C I`, and `C` is not needed. -/
theorem theorem1_regret [CompleteSpace E] {F : Set E} {P : E → E} {f : ℕ → E → ℝ}
    {g ε w : ℕ → E} {wstar : E} {c D G Eb : ℝ} (hP : IsMetricProj F P)
    (hdiam : ∀ x ∈ F, ∀ y ∈ F, ‖x - y‖ ≤ D) (hf : ∀ t ≥ 1, StrongConvexOn F c (f t))
    (hg : ∀ t ≥ 1, HasGradientAt (f t) (g t) (w t)) (hG : ∀ t ≥ 1, ‖g t‖ ≤ G)
    (hE : ∀ t ≥ 1, ‖ε t‖ ≤ Eb) (hstar : wstar ∈ F) (hw1 : w 1 ∈ F)
    (hw : ∀ t ≥ 1, w (t + 1) = P (w t - (1 / √(t : ℝ)) • (g t + ε t)))
    (hpert : ∀ t ≥ 1, ⟪g t, w t - wstar⟫ - c / 2 * ‖w t - wstar‖ ^ 2 ≤
      ⟪g t + ε t, w t - wstar⟫) {T : ℕ} (hT : 1 ≤ T) :
    ∑ t ∈ Finset.Icc 1 T, f t (w t) - ∑ t ∈ Finset.Icc 1 T, f t wstar ≤
      D ^ 2 / 2 * √(T : ℝ) + (G + Eb) ^ 2 * (√(T : ℝ) - 1 / 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
  have hconv : Convex ℝ F := (hf 1 le_rfl).1
  have hmem : ∀ t, w (t + 1) ∈ F := by
    intro t
    induction t with
    | zero => simpa using hw1
    | succ t ih => rw [hw (t + 1) (by omega)]; exact (hP _).1
  have hscGt : ∀ t, f (t + 1) (w (t + 1)) - f (t + 1) wstar ≤
      ⟪g (t + 1) + ε (t + 1), w (t + 1) - wstar⟫ - 0 / 2 * ‖w (t + 1) - wstar‖ ^ 2 := by
    intro t
    have h8 := eq8_strongConvexity (hf (t + 1) (by omega)) (hmem t) hstar (hg (t + 1) (by omega))
    have hp := hpert (t + 1) (by omega)
    have e : wstar - w (t + 1) = -(w (t + 1) - wstar) := by abel
    rw [e, inner_neg_right, norm_neg] at h8
    linarith
  have h := InexactGradient.regret_le_sqrt (f := fun t => f (t + 1)) (w := fun t => w (t + 1))
    (gr := fun t => g (t + 1) + ε (t + 1)) (gt := fun t => g (t + 1) + ε (t + 1))
    (wstar := wstar) (proj := P) (c := 0) (D := D) (G := G) (Eb := Eb)
    (fun u => hP.norm_sub_le hconv hstar u)
    (fun t => by
      have := hw (t + 1) (by omega)
      simpa using this)
    (fun t => hdiam _ (hmem t) _ hstar) hscGt (fun t => by simp)
    (fun t => (norm_add_le _ _).trans
      (add_le_add (hG (t + 1) (by omega)) (hE (t + 1) (by omega)))) n
  rw [sum_sub_distrib] at h
  rw [sum_Icc_one_eq, sum_Icc_one_eq]
  push_cast
  exact h

/-- **Theorem 1 of arXiv 2009.03887 under its sufficient condition (15)**
`‖ε^t‖ ≤ (c/2) ‖w^t - w⋆‖`, with the hypotheses of `theorem1_regret` otherwise. -/
theorem theorem1_regret_of_eq15 [CompleteSpace E] {F : Set E} {P : E → E} {f : ℕ → E → ℝ}
    {g ε w : ℕ → E} {wstar : E} {c D G Eb : ℝ} (hP : IsMetricProj F P)
    (hdiam : ∀ x ∈ F, ∀ y ∈ F, ‖x - y‖ ≤ D) (hf : ∀ t ≥ 1, StrongConvexOn F c (f t))
    (hg : ∀ t ≥ 1, HasGradientAt (f t) (g t) (w t)) (hG : ∀ t ≥ 1, ‖g t‖ ≤ G)
    (hE : ∀ t ≥ 1, ‖ε t‖ ≤ Eb) (hstar : wstar ∈ F) (hw1 : w 1 ∈ F)
    (hw : ∀ t ≥ 1, w (t + 1) = P (w t - (1 / √(t : ℝ)) • (g t + ε t)))
    (h15 : ∀ t ≥ 1, ‖ε t‖ ≤ c / 2 * ‖w t - wstar‖) {T : ℕ} (hT : 1 ≤ T) :
    ∑ t ∈ Finset.Icc 1 T, f t (w t) - ∑ t ∈ Finset.Icc 1 T, f t wstar ≤
      D ^ 2 / 2 * √(T : ℝ) + (G + Eb) ^ 2 * (√(T : ℝ) - 1 / 2) :=
  theorem1_regret hP hdiam hf hg hG hE hstar hw1 hw (fun t ht => eq15_sufficient (h15 t ht)) hT

end Regret

/-! ### Appendix A.2: the error of biased LRT -/

section Biased

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ}

/-- The singular values with the smallest one, `σ_q`, replaced by `0` (`q = r + 1`). -/
def dropLast (σ : Fin (r + 1) → ℝ) : Fin (r + 1) → ℝ :=
  fun i => if i = Fin.last r then 0 else σ i

/-- One sample of biased LRT (arXiv 2009.03887, Sec. 4.1 and App. A.2): the rank-`q = r + 1`
matrix `G̃ + dz aᵀ` has a thin SVD, and `G̃'` keeps its `r` largest components. -/
structure IsBiasedStep (G : Matrix m n ℝ) (dz : m → ℝ) (a : n → ℝ)
    (U : Matrix m (Fin (r + 1)) ℝ) (σ : Fin (r + 1) → ℝ) (V : Matrix n (Fin (r + 1)) ℝ)
    (G' : Matrix m n ℝ) : Prop where
  svd : IsThinSVD (G + Matrix.vecMulVec dz a) U σ V
  drop : G' = U * Matrix.diagonal (dropLast σ) * Vᵀ

omit [Fintype m] [Fintype n] in
/-- The entries of `U diag(d) Vᵀ`. -/
lemma mul_diagonal_mul_apply {q : ℕ} (U : Matrix m (Fin q) ℝ) (d : Fin q → ℝ)
    (V : Matrix n (Fin q) ℝ) (i : m) (j : n) :
    (U * Matrix.diagonal d * Vᵀ) i j = ∑ l, U i l * d l * V j l := by
  rw [Matrix.mul_apply]
  exact Finset.sum_congr rfl fun l _ => by rw [Matrix.mul_diagonal, Matrix.transpose_apply]

omit [Fintype m] [Fintype n] in
/-- The update of biased LRT is a rank-`r` factorization `L̃' R̃'ᵀ`. -/
lemma mul_dropLast_mul_eq (U : Matrix m (Fin (r + 1)) ℝ) (σ : Fin (r + 1) → ℝ)
    (V : Matrix n (Fin (r + 1)) ℝ) :
    U * Matrix.diagonal (dropLast σ) * Vᵀ =
      (U.submatrix id Fin.castSucc) * (V.submatrix id Fin.castSucc *
        Matrix.diagonal (σ ∘ Fin.castSucc))ᵀ := by
  have e : (U.submatrix id Fin.castSucc) * (V.submatrix id Fin.castSucc *
      Matrix.diagonal (σ ∘ Fin.castSucc))ᵀ = (U.submatrix id Fin.castSucc) *
      Matrix.diagonal (σ ∘ Fin.castSucc) * (V.submatrix id Fin.castSucc)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
  rw [e]
  ext i j
  rw [mul_diagonal_mul_apply, mul_diagonal_mul_apply, Fin.sum_univ_castSucc]
  simp [dropLast, Fin.castSucc_ne_last]

/-- **App. A.2 of arXiv 2009.03887, the error of one sample**: dropping the smallest component
gives the error `σ_q Q_{L,q} Q_{R,q}ᵀ`, the last singular vectors being columns of `U`, `V`. -/
theorem IsBiasedStep.error_eq {G G' : Matrix m n ℝ} {dz : m → ℝ} {a : n → ℝ}
    {U : Matrix m (Fin (r + 1)) ℝ} {σ : Fin (r + 1) → ℝ} {V : Matrix n (Fin (r + 1)) ℝ}
    (h : IsBiasedStep G dz a U σ V G') :
    G + Matrix.vecMulVec dz a - G' =
      σ (Fin.last r) •
        Matrix.vecMulVec (fun i => U i (Fin.last r)) (fun j => V j (Fin.last r)) := by
  rw [h.svd.eq, h.drop]
  ext i j
  rw [Matrix.sub_apply, mul_diagonal_mul_apply, mul_diagonal_mul_apply, ← Finset.sum_sub_distrib,
    Fin.sum_univ_castSucc]
  simp only [dropLast, Fin.castSucc_ne_last, ite_false, sub_self, Finset.sum_const_zero, zero_add,
    ite_true, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  ring

/-- **App. A.2 of arXiv 2009.03887**: the error of one sample has Frobenius norm exactly `σ_q`.
No Eckart–Young is needed: the update is defined by dropping the component. -/
theorem IsBiasedStep.norm_error {G G' : Matrix m n ℝ} {dz : m → ℝ} {a : n → ℝ}
    {U : Matrix m (Fin (r + 1)) ℝ} {σ : Fin (r + 1) → ℝ} {V : Matrix n (Fin (r + 1)) ℝ}
    (h : IsBiasedStep G dz a U σ V G') :
    ‖G + Matrix.vecMulVec dz a - G'‖ = σ (Fin.last r) := by
  have hD : U * Matrix.diagonal σ * Vᵀ - U * Matrix.diagonal (dropLast σ) * Vᵀ =
      U * (Matrix.diagonal fun i => if i = Fin.last r then σ i else 0) * Vᵀ := by
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]
    congr 3
    ext i
    by_cases hi : i = Fin.last r <;> simp [dropLast, hi]
  rw [h.svd.eq, h.drop, hD, Frobenius.norm_mul_transpose_of_orthonormal h.svd.orthV,
    Frobenius.norm_mul_of_orthonormal h.svd.orthU, Frobenius.norm_def]
  have : ∑ i, ∑ j, (Matrix.diagonal fun i => if i = Fin.last r then σ i else 0 :
      Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) i j ^ 2 = σ (Fin.last r) ^ 2 := by
    simp [Matrix.diagonal_apply, ite_pow, Finset.sum_ite_eq]
  rw [this, Real.sqrt_sq (h.svd.nonneg _)]

/-- Biased LRT keeps the rank at most `r` (arXiv 2009.03887, Sec. 4.1). -/
theorem IsBiasedStep.rank_le {G G' : Matrix m n ℝ} {dz : m → ℝ} {a : n → ℝ}
    {U : Matrix m (Fin (r + 1)) ℝ} {σ : Fin (r + 1) → ℝ} {V : Matrix n (Fin (r + 1)) ℝ}
    (h : IsBiasedStep G dz a U σ V G') : G'.rank ≤ r := by
  rw [h.drop, mul_dropLast_mul_eq]
  exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans (by simp))

/-- One sample of biased LRT (arXiv 2009.03887, Sec. 4.1) exists from any rank-`r` factorization
`G̃ = L̃ R̃ᵀ`, by Eq. (1) on `L = [L̃, dz]`, `R = [R̃, a]`, and again gives such a factorization. -/
theorem exists_isBiasedStep {LT : Matrix m (Fin r) ℝ} {RT : Matrix n (Fin r) ℝ} (dz : m → ℝ)
    (a : n → ℝ) (hm : r + 1 ≤ Fintype.card m) (hn : r + 1 ≤ Fintype.card n) :
    ∃ (U : Matrix m (Fin (r + 1)) ℝ) (σ : Fin (r + 1) → ℝ) (V : Matrix n (Fin (r + 1)) ℝ)
      (LT' : Matrix m (Fin r) ℝ) (RT' : Matrix n (Fin r) ℝ),
      IsBiasedStep (LT * RTᵀ) dz a U σ V (LT' * RT'ᵀ) := by
  let L : Matrix m (Fin (r + 1)) ℝ := Matrix.of fun i => Fin.snoc (LT i) (dz i)
  let R : Matrix n (Fin (r + 1)) ℝ := Matrix.of fun i => Fin.snoc (RT i) (a i)
  have hLR : L * Rᵀ = LT * RTᵀ + Matrix.vecMulVec dz a := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.add_apply, Matrix.vecMulVec_apply]
    rw [Fin.sum_univ_castSucc]
    simp [L, R]
  obtain ⟨U, σ, V, hsvd⟩ := exists_isThinSVD_factored L R hm hn
  rw [hLR] at hsvd
  exact ⟨U, σ, V, _, _, hsvd, (mul_dropLast_mul_eq U σ V).symm⟩

/-- Biased LRT (arXiv 2009.03887, App. A.2) runs on every sequence of samples, for
`q = r + 1 ≤ n_o, n_i`, so the hypotheses of `biased_accumulation_le` are satisfiable. -/
theorem exists_biased_run (dz : ℕ → m → ℝ) (a : ℕ → n → ℝ) (hm : r + 1 ≤ Fintype.card m)
    (hn : r + 1 ≤ Fintype.card n) :
    ∃ (G : ℕ → Matrix m n ℝ) (U : ℕ → Matrix m (Fin (r + 1)) ℝ) (σ : ℕ → Fin (r + 1) → ℝ)
      (V : ℕ → Matrix n (Fin (r + 1)) ℝ), G 0 = 0 ∧
        ∀ i, IsBiasedStep (G i) (dz i) (a i) (U i) (σ i) (V i) (G (i + 1)) := by
  let S := Matrix m (Fin r) ℝ × Matrix n (Fin r) ℝ
  have step : ∀ (i : ℕ) (p : S), ∃ (U : Matrix m (Fin (r + 1)) ℝ) (σ : Fin (r + 1) → ℝ)
      (V : Matrix n (Fin (r + 1)) ℝ) (p' : S),
      IsBiasedStep (p.1 * p.2ᵀ) (dz i) (a i) U σ V (p'.1 * p'.2ᵀ) := by
    intro i p
    obtain ⟨U, σ, V, LT', RT', h⟩ := exists_isBiasedStep (LT := p.1) (RT := p.2) (dz i) (a i) hm hn
    exact ⟨U, σ, V, (LT', RT'), h⟩
  choose U σ V p' hp using step
  let seq : ℕ → S := fun i => Nat.rec ((0 : Matrix m (Fin r) ℝ), (0 : Matrix n (Fin r) ℝ))
    (fun i p => p' i p) i
  refine ⟨fun i => (seq i).1 * (seq i).2ᵀ, fun i => U i (seq i), fun i => σ i (seq i),
    fun i => V i (seq i), ?_, fun i => hp i (seq i)⟩
  simp [seq]

omit [Fintype m] [Fintype n] in
/-- The error of `i` samples is the sum of the per-sample errors. -/
lemma biased_error_eq_sum {G : ℕ → Matrix m n ℝ} (h0 : G 0 = 0) (dz : ℕ → m → ℝ) (a : ℕ → n → ℝ)
    (B : ℕ) :
    G B - ∑ i ∈ range B, Matrix.vecMulVec (dz i) (a i) =
      -∑ i ∈ range B, (G i + Matrix.vecMulVec (dz i) (a i) - G (i + 1)) := by
  induction B with
  | zero => simp [h0]
  | succ B ih =>
    rw [sum_range_succ, sum_range_succ, neg_add, ← ih]
    abel

/-- **App. A.2 of arXiv 2009.03887, triangle form.**  After `B` samples from `G̃₀ = 0`,
`‖G̃_B - ∑ᵢ dz⁽ⁱ⁾ a⁽ⁱ⁾ᵀ‖_F ≤ ∑ᵢ σ_q⁽ⁱ⁾`.  The paper does not print this bound; it gives the
per-sample error `IsBiasedStep.error_eq` and adds variances, see `biased_sq_eq_of_uncorrelated`.
This form needs no assumption on the samples. -/
theorem biased_accumulation_le {G : ℕ → Matrix m n ℝ} {dz : ℕ → m → ℝ} {a : ℕ → n → ℝ}
    {U : ℕ → Matrix m (Fin (r + 1)) ℝ} {σ : ℕ → Fin (r + 1) → ℝ}
    {V : ℕ → Matrix n (Fin (r + 1)) ℝ} {B : ℕ} (h0 : G 0 = 0)
    (hstep : ∀ i < B, IsBiasedStep (G i) (dz i) (a i) (U i) (σ i) (V i) (G (i + 1))) :
    ‖G B - ∑ i ∈ range B, Matrix.vecMulVec (dz i) (a i)‖ ≤ ∑ i ∈ range B, σ i (Fin.last r) := by
  rw [biased_error_eq_sum h0, norm_neg]
  refine (norm_sum_le _ _).trans (sum_le_sum fun i hi => ?_)
  exact (hstep i (mem_range.1 hi)).norm_error.le

/-- **Eq. (17) of arXiv 2009.03887 (biased LRT, "the variances add").**  If the per-sample errors
are uncorrelated, i.e. pairwise orthogonal for the Frobenius inner product,
`‖G̃_B - ∑ᵢ dz⁽ⁱ⁾ a⁽ⁱ⁾ᵀ‖_F² = ∑ᵢ (σ_q⁽ⁱ⁾)²`.  The paper writes this as
`σ_ε² ≈ (1/N) ∑ᵢ (σ_q⁽ⁱ⁾)²` with `‖ε‖² ≈ N σ_ε²`; under its uncorrelation assumption, read as
this orthogonality, it is an equality. -/
theorem biased_sq_eq_of_uncorrelated {G : ℕ → Matrix m n ℝ} {dz : ℕ → m → ℝ} {a : ℕ → n → ℝ}
    {U : ℕ → Matrix m (Fin (r + 1)) ℝ} {σ : ℕ → Fin (r + 1) → ℝ}
    {V : ℕ → Matrix n (Fin (r + 1)) ℝ} {B : ℕ} (h0 : G 0 = 0)
    (hstep : ∀ i < B, IsBiasedStep (G i) (dz i) (a i) (U i) (σ i) (V i) (G (i + 1)))
    (hunc : ∀ i < B, ∀ j < B, i ≠ j →
      ⟪G i + Matrix.vecMulVec (dz i) (a i) - G (i + 1),
        G j + Matrix.vecMulVec (dz j) (a j) - G (j + 1)⟫ = 0) :
    ‖G B - ∑ i ∈ range B, Matrix.vecMulVec (dz i) (a i)‖ ^ 2 =
      ∑ i ∈ range B, σ i (Fin.last r) ^ 2 := by
  rw [biased_error_eq_sum h0, norm_neg]
  have key : ∀ n ≤ B, ‖∑ i ∈ range n, (G i + Matrix.vecMulVec (dz i) (a i) - G (i + 1))‖ ^ 2 =
      ∑ i ∈ range n, σ i (Fin.last r) ^ 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hn
      rw [sum_range_succ, sum_range_succ, norm_add_sq_real, ih (by omega), sum_inner,
        Finset.sum_eq_zero (fun i hi => hunc i (by have := mem_range.1 hi; omega) n (by omega)
          (by have := mem_range.1 hi; omega)), (hstep n (by omega)).norm_error]
      ring
  exact key B le_rfl

/-- **Eq. (19) of arXiv 2009.03887.**  Under the uncorrelation assumption,
`∑ᵢ (σ_q⁽ⁱ⁾)² ≤ (c²/4) ‖w - w⋆‖²` implies the sufficient condition (15) for the perturbation
`ε = G̃_B - ∑ᵢ dz⁽ⁱ⁾ a⁽ⁱ⁾ᵀ`. -/
theorem eq19_sufficient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {G : ℕ → Matrix m n ℝ} {dz : ℕ → m → ℝ} {a : ℕ → n → ℝ}
    {U : ℕ → Matrix m (Fin (r + 1)) ℝ} {σ : ℕ → Fin (r + 1) → ℝ}
    {V : ℕ → Matrix n (Fin (r + 1)) ℝ} {B : ℕ} {c : ℝ} {v : E} (hc : 0 ≤ c) (h0 : G 0 = 0)
    (hstep : ∀ i < B, IsBiasedStep (G i) (dz i) (a i) (U i) (σ i) (V i) (G (i + 1)))
    (hunc : ∀ i < B, ∀ j < B, i ≠ j →
      ⟪G i + Matrix.vecMulVec (dz i) (a i) - G (i + 1),
        G j + Matrix.vecMulVec (dz j) (a j) - G (j + 1)⟫ = 0)
    (h19 : ∑ i ∈ range B, σ i (Fin.last r) ^ 2 ≤ c ^ 2 / 4 * ‖v‖ ^ 2) :
    ‖G B - ∑ i ∈ range B, Matrix.vecMulVec (dz i) (a i)‖ ≤ c / 2 * ‖v‖ := by
  have hsq := biased_sq_eq_of_uncorrelated h0 hstep hunc
  have h : ‖G B - ∑ i ∈ range B, Matrix.vecMulVec (dz i) (a i)‖ ^ 2 ≤ (c / 2 * ‖v‖) ^ 2 := by
    rw [hsq]; nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

end Biased

/-! ### Sec. 4.1.2: the optimal unbiased Kronecker-sum estimator -/

section Estimator

open MeasureTheory

variable {r : ℕ}

/-- The paper's `s₁ = ∑_{i=m}^q σ_i`.  All indices of this section are `0`-based: `q = r + 1`, the
paper's `σ_i` is `σ (i - 1)` and the paper's `m` is our `m + 1`. -/
noncomputable def s₁ (σ : Fin (r + 1) → ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => m ≤ (i : ℕ)), σ i

/-- The paper's `s₂ = ∑_{i=m}^q σ_i²` (App. A.2). -/
noncomputable def s₂ (σ : Fin (r + 1) → ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => m ≤ (i : ℕ)), σ i ^ 2

/-- The set of indices satisfying the paper's stopping rule `(q - i) σ_i ≤ ∑_{j=i}^q σ_j`; in
`0`-based indices `q - i` reads `r - i`. -/
def stopSet (σ : Fin (r + 1) → ℝ) : Set ℕ :=
  {i | ∃ h : i < r + 1, ((r - i : ℕ) : ℝ) * σ ⟨i, h⟩ ≤ s₁ σ i}

/-- The paper's `m = min {i : (q - i) σ_i ≤ ∑_{j=i}^q σ_j}`, `0`-based. -/
noncomputable def mixIndex (σ : Fin (r + 1) → ℝ) : ℕ := sInf (stopSet σ)

/-- What the estimator needs of the first mixed index `m`: `k = r - m ≥ 1` (the paper's
`k = q - m`) and `k σ_i ≤ s₁` for the mixed indices, so that `x₀` below is well defined. -/
structure IsValidMix (σ : Fin (r + 1) → ℝ) (m : ℕ) : Prop where
  lt : m < r
  le : ∀ i : Fin (r + 1), m ≤ (i : ℕ) → ((r - m : ℕ) : ℝ) * σ i ≤ s₁ σ m

/-- The unit vector `x₀ = (√(1 - σ_i k / s₁))_{i ≥ m}`, extended by `0` to the kept indices. -/
noncomputable def x₀ (σ : Fin (r + 1) → ℝ) (m : ℕ) (i : Fin (r + 1)) : ℝ :=
  if m ≤ (i : ℕ) then √(1 - σ i * ((r - m : ℕ) : ℝ) / s₁ σ m) else 0

/-- The indicator of the mixed indices: the identity of the `(k+1) × (k+1)` block. -/
def mixedInd (m : ℕ) (i : Fin (r + 1)) : ℝ := if m ≤ (i : ℕ) then 1 else 0

/-- The paper's `X ∈ ℝ^{(k+1) × k}`: orthonormal columns with `X Xᵀ = I - x₀ x₀ᵀ`.  Its `k + 1` rows
are embedded in `ℝ^{r+1}`, with zero kept rows, which is forced by the second identity. -/
structure IsMixer (σ : Fin (r + 1) → ℝ) (m : ℕ) (X : Matrix (Fin (r + 1)) (Fin (r - m)) ℝ) :
    Prop where
  orth : Xᵀ * X = 1
  proj : X * Xᵀ = Matrix.diagonal (mixedInd m) - Matrix.vecMulVec (x₀ σ m) (x₀ σ m)

/-- The sign of a Boolean. -/
def sgn : Bool → ℝ
  | true => 1
  | false => -1

/-- The random signs `s ∈ {-1, 1}^{k+1}` on the mixed rows, and `1` on the kept rows. -/
noncomputable def signVec (m : ℕ) (b : Fin (r - m + 1) → Bool) (i : Fin (r + 1)) : ℝ :=
  if h : m ≤ (i : ℕ) then sgn (b ⟨i - m, by omega⟩) else 1

/-- The block `diag(√σ₁, …, √σ_{m-1})` of `Σ̃_L`, with its zero rows. -/
noncomputable def keptFactor (σ : Fin (r + 1) → ℝ) (m : ℕ) : Matrix (Fin (r + 1)) (Fin m) ℝ :=
  Matrix.of fun i j => if (i : ℕ) = j then √(σ i) else 0

/-- The paper's `Z = √(s₁/k) X_s`, where `X_s` multiplies the columns of `X` entrywise by `s`. -/
noncomputable def zBlock (σ : Fin (r + 1) → ℝ) (m : ℕ) (X : Matrix (Fin (r + 1)) (Fin (r - m)) ℝ)
    (b : Fin (r - m + 1) → Bool) : Matrix (Fin (r + 1)) (Fin (r - m)) ℝ :=
  √(s₁ σ m / ((r - m : ℕ) : ℝ)) • (Matrix.diagonal (signVec m b) * X)

/-- The paper's `Σ̃_L = Σ̃_R = diag(√σ₁, …, √σ_{m-1}, Z)`, a `q × r` matrix. -/
noncomputable def factor (σ : Fin (r + 1) → ℝ) (m : ℕ) (X : Matrix (Fin (r + 1)) (Fin (r - m)) ℝ)
    (b : Fin (r - m + 1) → Bool) : Matrix (Fin (r + 1)) (Fin m ⊕ Fin (r - m)) ℝ :=
  Matrix.fromCols (keptFactor σ m) (zBlock σ m X b)

/-- The paper's estimator `Σ̃ = Σ̃_L Σ̃_Rᵀ`. -/
noncomputable def estimator (σ : Fin (r + 1) → ℝ) (m : ℕ)
    (X : Matrix (Fin (r + 1)) (Fin (r - m)) ℝ) (b : Fin (r - m + 1) → Bool) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
  factor σ m X b * (factor σ m X b)ᵀ

/-- The expectation over uniform random signs `s ∈ {-1, 1}^{k+1}`. -/
noncomputable def signMean {k : ℕ} (f : (Fin (k + 1) → Bool) → ℝ) : ℝ :=
  (1 / 2 ^ (k + 1) : ℝ) * ∑ b, f b

/-- `sgn² = 1`. -/
lemma sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by cases b <;> norm_num [sgn]

/-- `sgn` changes sign under negation. -/
lemma sgn_not (b : Bool) : sgn (!b) = -sgn b := by cases b <;> norm_num [sgn]

/-- `E[s_i s_j] = 0` for `i ≠ j`. -/
lemma sum_sgn_mul_sgn {ι : Type*} [Fintype ι] [DecidableEq ι] {i j : ι} (h : i ≠ j) :
    ∑ b : ι → Bool, sgn (b i) * sgn (b j) = 0 := by
  let e : (ι → Bool) → (ι → Bool) := fun b => Function.update b i (!b i)
  have he : Function.Involutive e := by
    intro b
    ext l
    by_cases hl : l = i
    · subst hl; simp [e]
    · simp [e, hl]
  have hsum := Equiv.sum_comp (Function.Involutive.toPerm e he)
    (fun b : ι → Bool => sgn (b i) * sgn (b j))
  have hneg : ∀ b : ι → Bool, sgn ((Function.Involutive.toPerm e he b) i) *
      sgn ((Function.Involutive.toPerm e he b) j) = -(sgn (b i) * sgn (b j)) := by
    intro b
    simp [e, Function.update_of_ne h.symm, sgn_not]
  simp only [hneg, Finset.sum_neg_distrib] at hsum
  linarith

/-- `s_i² = 1`. -/
lemma signVec_mul_self (m : ℕ) (b : Fin (r - m + 1) → Bool) (i : Fin (r + 1)) :
    signVec m b i * signVec m b i = 1 := by
  unfold signVec
  split_ifs
  · exact sgn_mul_self _
  · norm_num

/-- `E[s_i s_j] = δ_{ij}` on the mixed block: the identity behind unbiasedness. -/
lemma sum_signVec_mul {m : ℕ} {i j : Fin (r + 1)} (hi : m ≤ (i : ℕ)) (hj : m ≤ (j : ℕ))
    (hij : i ≠ j) : ∑ b, signVec m b i * signVec m b j = 0 := by
  have hne : (⟨i - m, by omega⟩ : Fin (r - m + 1)) ≠ ⟨j - m, by omega⟩ := by
    intro h
    apply hij
    have := congrArg Fin.val h
    simp only at this
    exact Fin.ext (by omega)
  simpa [signVec, hi, hj] using sum_sgn_mul_sgn hne

/-- The expectation of a constant. -/
lemma signMean_const {k : ℕ} (c : ℝ) : signMean (fun _ : Fin (k + 1) → Bool => c) = c := by
  simp [signMean, Finset.card_univ]

/-- The number of mixed indices is `k + 1`. -/
lemma card_mixed {m : ℕ} (hm : m ≤ r) :
    (Finset.univ.filter (fun i : Fin (r + 1) => m ≤ (i : ℕ))).card = r - m + 1 := by
  have e : Finset.univ.filter (fun i : Fin (r + 1) => m ≤ (i : ℕ)) =
      Finset.Ici ⟨m, by omega⟩ := by
    ext i
    simp [Fin.le_def]
  rw [e, Fin.card_Ici]
  simp only
  omega

/-- `Σ_kept`: the part of `Σ` kept exactly by the estimator. -/
lemma keptFactor_mul_transpose {σ : Fin (r + 1) → ℝ} {m : ℕ} (hσ0 : ∀ i, 0 ≤ σ i) :
    keptFactor σ m * (keptFactor σ m)ᵀ =
      Matrix.diagonal (fun i : Fin (r + 1) => if (i : ℕ) < m then σ i else 0) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, keptFactor, Matrix.of_apply,
    Matrix.diagonal_apply]
  by_cases hi : (i : ℕ) < m
  · rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin m)]
    · by_cases hij : i = j
      · subst hij
        simp [hi, Real.mul_self_sqrt (hσ0 i)]
      · have : (j : ℕ) ≠ i := fun h => hij (Fin.ext h.symm)
        simp [hij, this]
    · intro l _ hl
      have : (i : ℕ) ≠ l := fun h => hl (Fin.ext h.symm)
      simp [this]
    · simp
  · have : ∀ l : Fin m, (i : ℕ) ≠ l := fun l h => hi (h ▸ l.2)
    simp [this, hi]

/-- `Σ̃ = Σ_kept + (s₁/k) D_s (X Xᵀ) D_s`. -/
lemma estimator_eq {σ : Fin (r + 1) → ℝ} {m : ℕ} (hσ0 : ∀ i, 0 ≤ σ i)
    (hc : 0 ≤ s₁ σ m / ((r - m : ℕ) : ℝ)) (X : Matrix (Fin (r + 1)) (Fin (r - m)) ℝ)
    (b : Fin (r - m + 1) → Bool) :
    estimator σ m X b = Matrix.diagonal (fun i : Fin (r + 1) => if (i : ℕ) < m then σ i else 0) +
      (s₁ σ m / ((r - m : ℕ) : ℝ)) •
        (Matrix.diagonal (signVec m b) * (X * Xᵀ) * Matrix.diagonal (signVec m b)) := by
  rw [estimator, factor, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows,
    keptFactor_mul_transpose hσ0, zBlock, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Real.mul_self_sqrt hc, Matrix.transpose_mul, Matrix.diagonal_transpose]
  simp only [Matrix.mul_assoc]

/-- **The rank of the estimator** (arXiv 2009.03887, Sec. 4.1.2): `rank Σ̃ ≤ (m - 1) + k = r` in the
paper's indices, because `Σ̃_L` has `r` columns. -/
theorem rank_estimator_le {σ : Fin (r + 1) → ℝ} {m : ℕ} (hm : m ≤ r)
    (X : Matrix (Fin (r + 1)) (Fin (r - m)) ℝ) (b : Fin (r - m + 1) → Bool) :
    (estimator σ m X b).rank ≤ r := by
  refine (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans ?_)
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

section Valid

variable {σ : Fin (r + 1) → ℝ} {m : ℕ}

/-- `x₀` vanishes on the kept indices. -/
lemma x₀_eq_zero {i : Fin (r + 1)} (h : ¬ m ≤ (i : ℕ)) : x₀ σ m i = 0 := by
  simp [x₀, h]

/-- `k > 0`. -/
lemma IsValidMix.cast_pos (hm : IsValidMix σ m) : (0 : ℝ) < ((r - m : ℕ) : ℝ) := by
  have := hm.lt
  exact_mod_cast (by omega : 0 < r - m)

/-- `x₀ᵢ² = 1 - σ_i k / s₁` on the mixed indices. -/
lemma x₀_sq (hm : IsValidMix σ m) (hs : 0 < s₁ σ m) (i : Fin (r + 1)) :
    x₀ σ m i ^ 2 = if m ≤ (i : ℕ) then 1 - σ i * ((r - m : ℕ) : ℝ) / s₁ σ m else 0 := by
  by_cases h : m ≤ (i : ℕ)
  · have hnn : 0 ≤ 1 - σ i * ((r - m : ℕ) : ℝ) / s₁ σ m := by
      have h1 := hm.le i h
      have : σ i * ((r - m : ℕ) : ℝ) / s₁ σ m ≤ 1 := by
        rw [div_le_one hs]
        linarith
      linarith
    simp only [x₀, h, ↓reduceIte]
    exact Real.sq_sqrt hnn
  · simp [x₀, h]

/-- `‖x₀‖ = 1`, as arXiv 2009.03887, Sec. 4.1.2 states. -/
theorem sum_x₀_sq (hm : IsValidMix σ m) (hs : 0 < s₁ σ m) : ∑ i, x₀ σ m i ^ 2 = 1 := by
  have hk := hm.cast_pos
  simp_rw [x₀_sq hm hs]
  rw [← Finset.sum_filter, Finset.sum_sub_distrib, Finset.sum_const, card_mixed hm.lt.le,
    nsmul_eq_mul, mul_one, Nat.cast_succ, ← Finset.sum_div, ← Finset.sum_mul]
  change ((r - m : ℕ) : ℝ) + 1 - s₁ σ m * ((r - m : ℕ) : ℝ) / s₁ σ m = 1
  field_simp
  ring

/-- `∑ x₀ᵢ⁴` in terms of `k`, `s₁`, `s₂`. -/
lemma sum_x₀_four (hm : IsValidMix σ m) (hs : 0 < s₁ σ m) :
    ∑ i, (x₀ σ m i ^ 2) ^ 2 = 1 - ((r - m : ℕ) : ℝ) +
      (((r - m : ℕ) : ℝ) / s₁ σ m) ^ 2 * s₂ σ m := by
  have hk := hm.cast_pos
  set k : ℝ := ((r - m : ℕ) : ℝ) with hkdef
  have h : ∀ i : Fin (r + 1), (x₀ σ m i ^ 2) ^ 2 = if m ≤ (i : ℕ) then
      1 - 2 * (k / s₁ σ m) * σ i + (k / s₁ σ m) ^ 2 * σ i ^ 2 else 0 := by
    intro i
    rw [x₀_sq hm hs]
    split_ifs
    · field_simp
      ring
    · norm_num
  simp_rw [h]
  rw [← Finset.sum_filter, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    card_mixed hm.lt.le, nsmul_eq_mul, mul_one, Nat.cast_succ, ← Finset.mul_sum, ← Finset.mul_sum]
  change k + 1 - 2 * (k / s₁ σ m) * s₁ σ m + (k / s₁ σ m) ^ 2 * s₂ σ m = _
  field_simp
  ring

/-- The entries of `Σ̃ - Σ`: the diagonal is exact, whatever the signs, and the error sits off the
diagonal of the mixed block. -/
lemma estimator_sub_apply (hσ0 : ∀ i, 0 ≤ σ i) (hm : IsValidMix σ m) (hs : 0 < s₁ σ m)
    {X : Matrix (Fin (r + 1)) (Fin (r - m)) ℝ} (hX : IsMixer σ m X) (b : Fin (r - m + 1) → Bool)
    (i j : Fin (r + 1)) :
    (estimator σ m X b - Matrix.diagonal σ) i j = if i = j then 0 else
      -(s₁ σ m / ((r - m : ℕ) : ℝ)) * (signVec m b i * signVec m b j) *
        (x₀ σ m i * x₀ σ m j) := by
  have hk := hm.cast_pos
  set k : ℝ := ((r - m : ℕ) : ℝ) with hkdef
  have hc : 0 ≤ s₁ σ m / k := by positivity
  have hentry : estimator σ m X b i j =
      (if i = j then (if (i : ℕ) < m then σ i else 0) else 0) + s₁ σ m / k *
        (signVec m b i * ((if i = j then mixedInd m i else 0) - x₀ σ m i * x₀ σ m j) *
          signVec m b j) := by
    rw [estimator_eq hσ0 hc, hX.proj]
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.sub_apply, Matrix.vecMulVec_apply, Matrix.diagonal_apply, ← hkdef]
  rw [Matrix.sub_apply, hentry, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    have hss := signVec_mul_self m b i
    have e : ∀ a : ℝ, signVec m b i * a * signVec m b i = a := fun a => by
      calc signVec m b i * a * signVec m b i = (signVec m b i * signVec m b i) * a := by ring
        _ = a := by rw [hss, one_mul]
    simp only [↓reduceIte, e]
    by_cases h : m ≤ (i : ℕ)
    · have hx := x₀_sq hm hs i
      simp only [h, ↓reduceIte] at hx
      have hlt : ¬ (i : ℕ) < m := by omega
      have hxx : x₀ σ m i * x₀ σ m i = 1 - σ i * k / s₁ σ m := by rw [← hx]; ring
      simp only [hlt, ↓reduceIte, mixedInd, h, hxx]
      field_simp
      ring
    · have hlt : (i : ℕ) < m := by omega
      simp [hlt, h, mixedInd, x₀_eq_zero h]
  · simp only [hij, ↓reduceIte]
    ring

/-- **Unbiasedness of the estimator** (arXiv 2009.03887, Sec. 4.1.2, footnote 3):
`E[Σ̃] = Σ` over uniform signs, for every valid first mixed index. -/
theorem estimator_unbiased (hσ0 : ∀ i, 0 ≤ σ i) (hm : IsValidMix σ m) (hs : 0 < s₁ σ m)
    {X : Matrix (Fin (r + 1)) (Fin (r - m)) ℝ} (hX : IsMixer σ m X) (i j : Fin (r + 1)) :
    signMean (fun b => estimator σ m X b i j) = Matrix.diagonal σ i j := by
  have hentry : ∀ b, estimator σ m X b i j = Matrix.diagonal σ i j +
      (estimator σ m X b - Matrix.diagonal σ) i j := fun b => by
    rw [Matrix.sub_apply]; ring
  simp_rw [hentry, estimator_sub_apply hσ0 hm hs hX]
  by_cases hij : i = j
  · simp only [hij, ↓reduceIte, add_zero, signMean_const]
  · simp only [hij, ↓reduceIte]
    by_cases hx : m ≤ (i : ℕ) ∧ m ≤ (j : ℕ)
    · have h0 := sum_signVec_mul hx.1 hx.2 hij
      have e : ∑ b : Fin (r - m + 1) → Bool, (Matrix.diagonal σ i j +
          -(s₁ σ m / ((r - m : ℕ) : ℝ)) * (signVec m b i * signVec m b j) *
            (x₀ σ m i * x₀ σ m j)) = ∑ _b : Fin (r - m + 1) → Bool, Matrix.diagonal σ i j := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, h0]
        ring
      have e2 : signMean (fun b : Fin (r - m + 1) → Bool => Matrix.diagonal σ i j +
          -(s₁ σ m / ((r - m : ℕ) : ℝ)) * (signVec m b i * signVec m b j) *
            (x₀ σ m i * x₀ σ m j)) =
          signMean (fun _ : Fin (r - m + 1) → Bool => Matrix.diagonal σ i j) := by
        unfold signMean
        rw [e]
      rw [e2, signMean_const]
    · have e0 : x₀ σ m i * x₀ σ m j = 0 := by
        by_cases hi : m ≤ (i : ℕ)
        · have hj : ¬ m ≤ (j : ℕ) := fun hj => hx ⟨hi, hj⟩
          rw [x₀_eq_zero hj, mul_zero]
        · rw [x₀_eq_zero hi, zero_mul]
      simp only [e0, mul_zero, add_zero, signMean_const]

/-- `∑_{i ≠ j} a_i a_j = (∑ a_i)² - ∑ a_i²`. -/
private lemma sum_sum_ite_ne {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) :
    ∑ i, ∑ j, (if i = j then 0 else a i * a j) = (∑ i, a i) ^ 2 - ∑ i, a i ^ 2 := by
  have h : ∀ i, ∑ j, (if i = j then 0 else a i * a j) = a i * ∑ j, a j - a i ^ 2 := by
    intro i
    have h1 : ∑ j, a i * a j = ∑ j, ((if i = j then 0 else a i * a j) +
        if i = j then a i * a j else 0) :=
      Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq] at h1
    simp only [Finset.mem_univ, ↓reduceIte] at h1
    rw [Finset.mul_sum, h1]
    ring
  simp_rw [h]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

/-- **The error of the estimator of arXiv 2009.03887, Sec. 4.1.2, is deterministic**: for every
value of the signs, `‖Σ̃ - Σ‖_F² = s₁²/k - s₂`.  The paper only considers the expectation. -/
theorem norm_estimator_sub_sq (hσ0 : ∀ i, 0 ≤ σ i) (hm : IsValidMix σ m) (hs : 0 < s₁ σ m)
    {X : Matrix (Fin (r + 1)) (Fin (r - m)) ℝ} (hX : IsMixer σ m X) (b : Fin (r - m + 1) → Bool) :
    ‖estimator σ m X b - Matrix.diagonal σ‖ ^ 2 =
      s₁ σ m ^ 2 / ((r - m : ℕ) : ℝ) - s₂ σ m := by
  have hk := hm.cast_pos
  set k : ℝ := ((r - m : ℕ) : ℝ) with hkdef
  have h1 : ∀ i j, (estimator σ m X b - Matrix.diagonal σ) i j ^ 2 =
      (s₁ σ m / k) ^ 2 * (if i = j then 0 else x₀ σ m i ^ 2 * x₀ σ m j ^ 2) := by
    intro i j
    rw [estimator_sub_apply hσ0 hm hs hX]
    by_cases hij : i = j
    · simp [hij]
    · simp only [hij, ↓reduceIte]
      have hss : (signVec m b i * signVec m b j) ^ 2 = 1 := by
        calc (signVec m b i * signVec m b j) ^ 2 =
            (signVec m b i * signVec m b i) * (signVec m b j * signVec m b j) := by ring
          _ = 1 := by rw [signVec_mul_self, signVec_mul_self, one_mul]
      calc (-(s₁ σ m / k) * (signVec m b i * signVec m b j) * (x₀ σ m i * x₀ σ m j)) ^ 2
          = (s₁ σ m / k) ^ 2 * (signVec m b i * signVec m b j) ^ 2 *
              (x₀ σ m i ^ 2 * x₀ σ m j ^ 2) := by ring
        _ = _ := by rw [hss, mul_one]
  rw [Frobenius.norm_sq_eq_sum]
  simp_rw [h1, ← Finset.mul_sum]
  rw [sum_sum_ite_ne (fun i => x₀ σ m i ^ 2), sum_x₀_sq hm hs, sum_x₀_four hm hs]
  field_simp
  ring

/-- **The variance of the estimator**: `E‖Σ̃ - Σ‖_F² = s₁²/k - s₂`.  This is the formula of
Benzing et al. (2019).  App. A.2 of arXiv 2009.03887 prints `s₁²/k + s₂`, which is false, see
`appA2_min_variance_formula_false`. -/
theorem estimator_variance_eq (hσ0 : ∀ i, 0 ≤ σ i) (hm : IsValidMix σ m) (hs : 0 < s₁ σ m)
    {X : Matrix (Fin (r + 1)) (Fin (r - m)) ℝ} (hX : IsMixer σ m X) :
    signMean (fun b => ‖estimator σ m X b - Matrix.diagonal σ‖ ^ 2) =
      s₁ σ m ^ 2 / ((r - m : ℕ) : ℝ) - s₂ σ m := by
  simp_rw [norm_estimator_sub_sq hσ0 hm hs hX]
  exact signMean_const _

end Valid

/-- A matrix of rank at most `r` in `ℝ^{(r+1) × (r+1)}` is at Frobenius distance at least `l` from
a diagonal matrix with entries `≥ l ≥ 0`: it has a kernel vector, on which the diagonal matrix
is bounded below.  This is the lower-bound half of the minimum-variance theorem. -/
lemma sq_le_norm_sub_diagonal {A : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ} (hA : A.rank ≤ r)
    {y : Fin (r + 1) → ℝ} {l : ℝ} (hl : 0 ≤ l) (hy : ∀ i, l ≤ y i) :
    l ^ 2 ≤ ‖A - Matrix.diagonal y‖ ^ 2 := by
  have hdet : A.det = 0 := by
    by_contra h
    have hu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 h)
    have := Matrix.rank_of_isUnit A hu
    simp only [Fintype.card_fin] at this
    omega
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  set B := A - Matrix.diagonal y with hB
  have hBv : ∀ i, (B.mulVec v) i = -(y i * v i) := by
    intro i
    simp [hB, Matrix.sub_mulVec, hAv, Matrix.mulVec_diagonal]
  have hvpos : 0 < ∑ i, v i ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
    exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨i, Finset.mem_univ _, by
      simpa using sq_pos_of_ne_zero (by simpa using hi)⟩
  have h1 : l ^ 2 * ∑ i, v i ^ 2 ≤ ∑ i, (B.mulVec v) i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hBv, neg_sq, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hl (hy i) 2) (sq_nonneg _)
  have h2 : ∑ i, (B.mulVec v) i ^ 2 ≤ ‖B‖ ^ 2 * ∑ i, v i ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => B i j) v
  exact le_of_mul_le_mul_right (h1.trans h2) hvpos

/-- The form of `variance_lower_bound` (arXiv 2009.03887, Sec. 4.1.2) with a dominating integrand
`W`, used for `lifted_minimum_variance`. -/
theorem variance_lower_bound_of_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : Fin (r + 1) → ℝ} {m : ℕ} (hlt : m < r)
    (hs : 0 ≤ s₁ σ m) (hkept : ∀ i : Fin (r + 1), (i : ℕ) < m →
      s₁ σ m / ((r - m : ℕ) : ℝ) ≤ σ i)
    {A : Ω → Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ} (hint : ∀ i j, Integrable (fun ω => A ω i j) μ)
    (hmean : ∀ i j, ∫ ω, A ω i j ∂μ = Matrix.diagonal σ i j)
    (hrank : ∀ᵐ ω ∂μ, (A ω).rank ≤ r) {W : Ω → ℝ} (hW : Integrable W μ)
    (hle : ∀ᵐ ω ∂μ, ‖A ω - Matrix.diagonal σ‖ ^ 2 ≤ W ω) :
    s₁ σ m ^ 2 / ((r - m : ℕ) : ℝ) - s₂ σ m ≤ ∫ ω, W ω ∂μ := by
  have hk : (0 : ℝ) < ((r - m : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < r - m)
  set k : ℝ := ((r - m : ℕ) : ℝ) with hkdef
  set l : ℝ := s₁ σ m / k with hl
  have hl0 : 0 ≤ l := div_nonneg hs hk.le
  let y : Fin (r + 1) → ℝ := fun i => if (i : ℕ) < m then σ i else l
  let t : Fin (r + 1) → ℝ := fun i => y i - σ i
  have hy : ∀ i, l ≤ y i := by
    intro i
    by_cases hi : (i : ℕ) < m
    · simpa [y, hi] using hkept i hi
    · simp [y, hi]
  -- the pointwise inequality
  have hpoint : ∀ B : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ, B.rank ≤ r →
      l ^ 2 - 2 * ∑ i, y i * t i + ∑ i, t i ^ 2 + 2 * ∑ i, B i i * t i ≤
        ‖B - Matrix.diagonal σ‖ ^ 2 := by
    intro B hB
    have hle := sq_le_norm_sub_diagonal hB hl0 hy
    have e : B - Matrix.diagonal σ = (B - Matrix.diagonal y) + Matrix.diagonal t := by
      ext i j
      by_cases hij : i = j <;> simp [hij, t]
    have hinner : ⟪B - Matrix.diagonal y, Matrix.diagonal t⟫ =
        ∑ i, B i i * t i - ∑ i, y i * t i := by
      rw [Frobenius.inner_def, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single i]
      · simp [sub_mul]
      · intro j _ hj
        simp [hj.symm]
      · simp
    have hnorm : ‖(Matrix.diagonal t : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)‖ ^ 2 =
        ∑ i, t i ^ 2 := by
      rw [Frobenius.norm_sq_eq_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [hj.symm]
      · simp
    rw [e, norm_add_sq_real, hinner, hnorm]
    linarith
  -- integrate
  have hψint : Integrable (fun ω => l ^ 2 - 2 * ∑ i, y i * t i + ∑ i, t i ^ 2 +
      2 * ∑ i, A ω i i * t i) μ :=
    (integrable_const _).fun_add
      ((integrable_finsetSum _ fun i _ => (hint i i).mul_const _).const_mul _)
  have hint2 : ∫ ω, (l ^ 2 - 2 * ∑ i, y i * t i + ∑ i, t i ^ 2 + 2 * ∑ i, A ω i i * t i) ∂μ =
      l ^ 2 - 2 * ∑ i, y i * t i + ∑ i, t i ^ 2 + 2 * ∑ i, σ i * t i := by
    rw [integral_add (integrable_const _)
      ((integrable_finsetSum _ fun i _ => (hint i i).mul_const _).const_mul _),
      integral_const, integral_const_mul,
      integral_finsetSum _ fun i _ => (hint i i).mul_const _]
    simp only [probReal_univ, one_smul, integral_mul_const, hmean, Matrix.diagonal_apply_eq]
  have hmono := integral_mono_ae hψint hW (by
    filter_upwards [hrank, hle] with ω hω hω' using (hpoint _ hω).trans hω')
  rw [hint2] at hmono
  refine le_trans (le_of_eq ?_) hmono
  -- the value of the bound
  have h1 : ∑ i, t i ^ 2 = (k + 1) * l ^ 2 - 2 * l * s₁ σ m + s₂ σ m := by
    have h : ∀ i, t i ^ 2 = if m ≤ (i : ℕ) then l ^ 2 - 2 * l * σ i + σ i ^ 2 else 0 := by
      intro i
      by_cases hi : (i : ℕ) < m
      · have hni : ¬ m ≤ (i : ℕ) := by omega
        simp [t, y, hi, hni]
      · have hni : m ≤ (i : ℕ) := by omega
        simp only [t, y, hi, hni, ↓reduceIte]
        ring
    simp_rw [h]
    rw [← Finset.sum_filter, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      card_mixed hlt.le, nsmul_eq_mul, Nat.cast_succ, ← Finset.mul_sum]
    rfl
  have h2 : ∑ i, y i * t i - ∑ i, σ i * t i = ∑ i, t i ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [t]; ring
  have h3 : l * k = s₁ σ m := by rw [hl]; field_simp
  have e : l ^ 2 - 2 * ∑ i, y i * t i + ∑ i, t i ^ 2 + 2 * ∑ i, σ i * t i =
      l ^ 2 - ∑ i, t i ^ 2 := by linarith
  rw [e, h1, ← h3]
  field_simp
  ring

/-- **The lower bound of the minimum-variance theorem** (arXiv 2009.03887, Sec. 4.1.2, attributed
there to Benzing et al. 2019).  On any probability space, an unbiased estimator `A` of
`Σ = diag(σ)` with rank at most `r = q - 1` almost surely has `E‖A - Σ‖_F² ≥ s₁²/k - s₂`, as soon as
the kept singular values dominate `s₁/k`.  For an unbiased `A`, `E‖A - Σ‖_F²` is the sum of the
entrywise variances; a square-integrable error is assumed because the Bochner integral of a
non-integrable function is `0` in Lean, and an infinite variance is not a competitor anyway. -/
theorem variance_lower_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : Fin (r + 1) → ℝ} {m : ℕ} (hlt : m < r)
    (hs : 0 ≤ s₁ σ m) (hkept : ∀ i : Fin (r + 1), (i : ℕ) < m →
      s₁ σ m / ((r - m : ℕ) : ℝ) ≤ σ i)
    {A : Ω → Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ} (hint : ∀ i j, Integrable (fun ω => A ω i j) μ)
    (hmean : ∀ i j, ∫ ω, A ω i j ∂μ = Matrix.diagonal σ i j)
    (hrank : ∀ᵐ ω ∂μ, (A ω).rank ≤ r)
    (hL2 : Integrable (fun ω => ‖A ω - Matrix.diagonal σ‖ ^ 2) μ) :
    s₁ σ m ^ 2 / ((r - m : ℕ) : ℝ) - s₂ σ m ≤ ∫ ω, ‖A ω - Matrix.diagonal σ‖ ^ 2 ∂μ :=
  variance_lower_bound_of_le hlt hs hkept hint hmean hrank hL2 (ae_of_all _ fun _ => le_rfl)

/-! #### The paper's index `m` -/

/-- `s₁ ≥ 0`. -/
lemma s₁_nonneg {σ : Fin (r + 1) → ℝ} (hσ0 : ∀ i, 0 ≤ σ i) (m : ℕ) : 0 ≤ s₁ σ m :=
  Finset.sum_nonneg fun i _ => hσ0 i

/-- `∑_{j ≥ i} σ_j = σ_i + ∑_{j ≥ i + 1} σ_j`. -/
lemma s₁_eq_add (σ : Fin (r + 1) → ℝ) {i : ℕ} (h : i < r + 1) :
    s₁ σ i = σ ⟨i, h⟩ + s₁ σ (i + 1) := by
  have e : Finset.univ.filter (fun j : Fin (r + 1) => i ≤ (j : ℕ)) =
      insert ⟨i, h⟩ (Finset.univ.filter (fun j : Fin (r + 1) => i + 1 ≤ (j : ℕ))) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [s₁, e, Finset.sum_insert (by simp), s₁]

/-- The stopping rule holds at the last but one index, as `σ_q ≥ 0`. -/
lemma mem_stopSet_pred (hr : 1 ≤ r) {σ : Fin (r + 1) → ℝ} (hσ0 : ∀ i, 0 ≤ σ i) :
    r - 1 ∈ stopSet σ := by
  refine ⟨by omega, ?_⟩
  have e : r - (r - 1) = 1 := by omega
  rw [e, s₁_eq_add σ (show r - 1 < r + 1 by omega)]
  have := s₁_nonneg hσ0 (r - 1 + 1)
  simp only [Nat.cast_one, one_mul]
  linarith

/-- **The index `m` of arXiv 2009.03887, Sec. 4.1.2, is well defined and valid**: `k ≥ 1`, and
`k σ_i ≤ s₁` for the mixed indices, so that the square roots in `x₀` are real. -/
theorem isValidMix_mixIndex (hr : 1 ≤ r) {σ : Fin (r + 1) → ℝ} (hanti : Antitone σ)
    (hσ0 : ∀ i, 0 ≤ σ i) : IsValidMix σ (mixIndex σ) := by
  have hne : (stopSet σ).Nonempty := ⟨_, mem_stopSet_pred hr hσ0⟩
  obtain ⟨h, hle⟩ := Nat.sInf_mem hne
  have hlt : mixIndex σ ≤ r - 1 := Nat.sInf_le (mem_stopSet_pred hr hσ0)
  refine ⟨by omega, fun i hi => ?_⟩
  calc ((r - mixIndex σ : ℕ) : ℝ) * σ i
      ≤ ((r - mixIndex σ : ℕ) : ℝ) * σ ⟨mixIndex σ, h⟩ :=
        mul_le_mul_of_nonneg_left (hanti (Fin.le_def.2 hi)) (Nat.cast_nonneg _)
    _ ≤ s₁ σ (mixIndex σ) := hle

/-- By minimality of the index `m` of arXiv 2009.03887, Sec. 4.1.2, the kept singular values
dominate `s₁/k`. -/
theorem div_le_of_kept (hr : 1 ≤ r) {σ : Fin (r + 1) → ℝ} (hanti : Antitone σ)
    (hσ0 : ∀ i, 0 ≤ σ i) {i : Fin (r + 1)} (hi : (i : ℕ) < mixIndex σ) :
    s₁ σ (mixIndex σ) / ((r - mixIndex σ : ℕ) : ℝ) ≤ σ i := by
  have hv := isValidMix_mixIndex hr hanti hσ0
  have hk := hv.cast_pos
  set m := mixIndex σ with hm
  have hp : m - 1 < r + 1 := by have := hv.lt; omega
  have hnot : m - 1 ∉ stopSet σ := Nat.notMem_of_lt_sInf (by rw [← mixIndex, ← hm]; omega)
  have hnl : ¬ ((r - (m - 1) : ℕ) : ℝ) * σ ⟨m - 1, hp⟩ ≤ s₁ σ (m - 1) := fun h => hnot ⟨hp, h⟩
  rw [s₁_eq_add σ hp, show m - 1 + 1 = m by omega] at hnl
  have hcast : ((r - (m - 1) : ℕ) : ℝ) = ((r - m : ℕ) : ℝ) + 1 := by
    have := hv.lt
    rw [show r - (m - 1) = r - m + 1 by omega, Nat.cast_succ]
  rw [hcast] at hnl
  have hlt : s₁ σ m < ((r - m : ℕ) : ℝ) * σ ⟨m - 1, hp⟩ := by
    by_contra hcon
    exact hnl (by push Not at hcon; linarith)
  have hanti' : σ ⟨m - 1, hp⟩ ≤ σ i := hanti (Fin.le_def.2 (by simp only; omega))
  rw [div_le_iff₀ hk]
  nlinarith

/-! #### Existence of the mixer `X`: the Householder reflection of Sec. 4.2.3 -/

/-- The Householder reflection `I - 2 v vᵀ / ‖v‖²`, `v = x - e_p`, of arXiv 2009.03887, Sec. 4.2.3:
an orthogonal matrix with `p`-th column the unit vector `x`, equal to the identity on the columns
`j ≠ p` with `x_j = 0`.  For `x = e_p` it is the identity, where the paper's formula reads `0/0`. -/
lemma exists_householder {ι : Type*} [Fintype ι] [DecidableEq ι] {x : ι → ℝ}
    (hx : ∑ i, x i ^ 2 = 1) (p : ι) :
    ∃ H : Matrix ι ι ℝ, Hᵀ * H = 1 ∧ H * Hᵀ = 1 ∧ (∀ i, H i p = x i) ∧
      ∀ i j, j ≠ p → x j = 0 → H i j = if i = j then 1 else 0 := by
  let v : ι → ℝ := fun i => x i - if i = p then 1 else 0
  have hvv : ∑ i, v i ^ 2 = 2 * (1 - x p) := by
    have h : ∀ i, v i ^ 2 = x i ^ 2 - 2 * (if i = p then x i else 0) +
        (if i = p then 1 else 0) := by
      intro i
      by_cases hi : i = p
      · simp only [v, hi, ↓reduceIte]; ring
      · simp [v, hi]
    simp_rw [h]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
      Finset.sum_ite_eq', hx]
    simp only [Finset.mem_univ, ↓reduceIte]
    ring
  by_cases hxp : x p = 1
  · have hv : ∀ i, v i = 0 := by
      intro i
      have h0 : ∑ i, v i ^ 2 = 0 := by rw [hvv, hxp]; ring
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (v i))).1 h0 i
        (Finset.mem_univ i)
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    have hxe : ∀ i, x i = if i = p then 1 else 0 := fun i => by
      have := hv i
      simp only [v] at this
      linarith
    refine ⟨1, by simp, by simp, fun i => ?_, fun i j _ _ => Matrix.one_apply⟩
    rw [hxe i, Matrix.one_apply]
  · have hne : 1 - x p ≠ 0 := sub_ne_zero.2 (Ne.symm hxp)
    let t : ℝ := 1 / (1 - x p)
    let Q : Matrix ι ι ℝ := Matrix.vecMulVec v v
    have htmul : t * (1 - x p) = 1 := by simp only [t]; field_simp
    have hQT : Qᵀ = Q := by
      ext i j
      simp [Q, Matrix.vecMulVec_apply, mul_comm]
    have hQQ : Q * Q = (2 * (1 - x p)) • Q := by
      ext i j
      simp only [Q, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul]
      have h : ∀ l, v i * v l * (v l * v j) = v i * v j * v l ^ 2 := fun l => by ring
      simp_rw [h]
      rw [← Finset.mul_sum, hvv]
      ring
    let H : Matrix ι ι ℝ := 1 - t • Q
    have hHT : Hᵀ = H := by
      simp [H, Matrix.transpose_sub, Matrix.transpose_smul, hQT]
    have hHH : H * H = 1 := by
      have e0 : t * (t * (2 * (1 - x p))) = 2 * t := by
        have : t * (t * (2 * (1 - x p))) = 2 * t * (t * (1 - x p)) := by ring
        rw [this, htmul, mul_one]
      calc H * H = 1 - t • Q - t • Q + (t * t) • (Q * Q) := by
            simp only [H, sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
              smul_sub, smul_smul]
            abel
        _ = 1 - t • Q - t • Q + (2 * t) • Q := by rw [hQQ, smul_smul, mul_assoc, e0]
        _ = 1 := by
            rw [two_mul, add_smul]
            abel
    refine ⟨H, by rw [hHT, hHH], by rw [hHT, hHH], fun i => ?_, fun i j hj hxj => ?_⟩
    · have hvp : t * v p = -1 := by
        simp only [v, ↓reduceIte]
        have : t * (x p - 1) = -(t * (1 - x p)) := by ring
        rw [this, htmul]
      have e : H i p = (if i = p then 1 else 0) - v i * (t * v p) := by
        simp only [H, Q, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul,
          Matrix.one_apply]
        ring
      rw [e, hvp]
      simp only [v]
      ring
    · have hvj : v j = 0 := by simp [v, hj, hxj]
      simp [H, Q, Matrix.one_apply, Matrix.vecMulVec_apply, hvj]

/-- Splitting a sum over `Fin (r + 1)` at the pivot `m`. -/
private lemma sum_split {m : ℕ} (hm : m < r) (f : Fin (r + 1) → ℝ) :
    ∑ l, f l = ∑ l ∈ Finset.univ.filter (fun l : Fin (r + 1) => (l : ℕ) < m), f l +
      f ⟨m, by omega⟩ + ∑ j : Fin (r - m), f ⟨m + 1 + j, by omega⟩ := by
  let p : Fin (r + 1) := ⟨m, by omega⟩
  let a : Fin (r - m) → Fin (r + 1) := fun j => ⟨m + 1 + j, by omega⟩
  have ha : Function.Injective a := fun j j' h => by
    have := congrArg Fin.val h
    simp only [a] at this
    exact Fin.ext (by omega)
  have e : Finset.univ.filter (fun l : Fin (r + 1) => ¬ (l : ℕ) < m) =
      insert p (Finset.univ.image a) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_image]
    constructor
    · intro hl
      by_cases hlp : (l : ℕ) = m
      · exact Or.inl (Fin.ext hlp)
      · exact Or.inr ⟨⟨l - m - 1, by omega⟩, Fin.ext (by simp only [a]; omega)⟩
    · rintro (rfl | ⟨j, rfl⟩)
      · simp [p]
      · simp only [a]; omega
  have hp : p ∉ Finset.univ.image a := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro j h
    have := congrArg Fin.val h
    simp only [a, p] at this
    omega
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun l : Fin (r + 1) => (l : ℕ) < m), e,
    Finset.sum_insert hp, Finset.sum_image ha.injOn, add_assoc]

/-- **The mixer `X` exists** for a valid first mixed index with `s₁ > 0`.  It is built from the
Householder reflection of arXiv 2009.03887, Sec. 4.2.3, by deleting the column of `x₀`. -/
theorem exists_isMixer {σ : Fin (r + 1) → ℝ} {m : ℕ} (hm : IsValidMix σ m) (hs : 0 < s₁ σ m) :
    ∃ X, IsMixer σ m X := by
  have hlt := hm.lt
  let p : Fin (r + 1) := ⟨m, by omega⟩
  obtain ⟨H, hHH, hHH', hcol, hkept⟩ := exists_householder (sum_x₀_sq hm hs) p
  let a : Fin (r - m) → Fin (r + 1) := fun j => ⟨m + 1 + j, by omega⟩
  have ha : Function.Injective a := fun j j' h => by
    have := congrArg Fin.val h
    simp only [a] at this
    exact Fin.ext (by omega)
  refine ⟨H.submatrix id a, ?_, ?_⟩
  · rw [Matrix.transpose_submatrix, ← Matrix.submatrix_mul _ _ a id a Function.bijective_id, hHH,
      Matrix.submatrix_one _ ha]
  · ext i i'
    have hentry := congrFun (congrFun hHH' i) i'
    rw [Matrix.mul_apply, sum_split hlt] at hentry
    simp only [Matrix.transpose_apply] at hentry
    have hpiv : H i ⟨m, by omega⟩ * H i' ⟨m, by omega⟩ = x₀ σ m i * x₀ σ m i' := by
      rw [show (⟨m, by omega⟩ : Fin (r + 1)) = p from rfl, hcol, hcol]
    have hKept : ∑ l ∈ Finset.univ.filter (fun l : Fin (r + 1) => (l : ℕ) < m),
        H i l * H i' l = if i = i' ∧ (i : ℕ) < m then 1 else 0 := by
      have h : ∀ l ∈ Finset.univ.filter (fun l : Fin (r + 1) => (l : ℕ) < m),
          H i l * H i' l = (if i = l then 1 else 0) * (if i' = l then 1 else 0) := by
        intro l hl
        have hl' : (l : ℕ) < m := (Finset.mem_filter.1 hl).2
        have hlp : l ≠ p := fun h => by
          have := congrArg Fin.val h
          simp only [p] at this
          omega
        have hx : x₀ σ m l = 0 := x₀_eq_zero (by omega)
        rw [hkept i l hlp hx, hkept i' l hlp hx]
      rw [Finset.sum_congr rfl h]
      by_cases hi : (i : ℕ) < m
      · rw [Finset.sum_eq_single i]
        · by_cases hii : i = i'
          · subst hii
            simp [hi]
          · have : i' ≠ i := Ne.symm hii
            simp [hii, this]
        · intro l _ hl
          simp [Ne.symm hl]
        · intro h
          exact (h (Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩)).elim
      · have h0 : ∀ l ∈ Finset.univ.filter (fun l : Fin (r + 1) => (l : ℕ) < m),
            (if i = l then (1 : ℝ) else 0) * (if i' = l then 1 else 0) = 0 := by
          intro l hl
          have hl' : (l : ℕ) < m := (Finset.mem_filter.1 hl).2
          have : i ≠ l := fun e => hi (e ▸ hl')
          simp [this]
        rw [Finset.sum_eq_zero h0]
        simp [hi]
    rw [hpiv, hKept] at hentry
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id,
      Matrix.sub_apply, Matrix.vecMulVec_apply, Matrix.diagonal_apply]
    have e : ∑ j, H i (a j) * H i' (a j) = (1 : Matrix _ _ ℝ) i i' -
        (if i = i' ∧ (i : ℕ) < m then 1 else 0) - x₀ σ m i * x₀ σ m i' := by
      rw [← hentry]
      simp only [a]
      ring
    rw [e, Matrix.one_apply]
    by_cases hii : i = i'
    · subst hii
      by_cases hi : (i : ℕ) < m
      · have : ¬ m ≤ (i : ℕ) := by omega
        simp [hi, mixedInd, this]
      · have : m ≤ (i : ℕ) := by omega
        simp [hi, mixedInd, this]
    · simp [hii]

/-- **Sec. 4.1.2 of arXiv 2009.03887: the estimator is unbiased, of rank at most `r`, and of
minimum variance.**  Let `σ₁ ≥ ⋯ ≥ σ_q ≥ 0`, `q = r + 1`, `r ≥ 1`, let `m` be the paper's index, and
let `Σ̃ = Σ̃_L Σ̃_Rᵀ` be the estimator with uniform signs.  Then `rank Σ̃ ≤ r`, `E Σ̃ = Σ`, and for
every unbiased estimator `A` of rank at most `r` a.s., on any probability space,
`E‖Σ̃ - Σ‖_F² ≤ E‖A - Σ‖_F²`.

The paper attributes minimality to Benzing et al. (2019) without proof; it is proved here.
Variance means `E‖· - Σ‖_F²`, the sum of the entrywise variances (the paper does not define it).
The paper's `x₀` is `0/0` when `s₁ = 0`, so `s₁ > 0` is assumed; that case is
`estimator_of_s₁_eq_zero`.  For `r = 0` the paper's `k` is `0`, which `r ≥ 1` excludes.
Existence of `X` is `exists_isMixer`.  The lift to the gradient `L Rᵀ` is
`lifted_minimum_variance`. -/
theorem estimator_minimum_variance (hr : 1 ≤ r) {σ : Fin (r + 1) → ℝ} (hanti : Antitone σ)
    (hσ0 : ∀ i, 0 ≤ σ i) (hs : 0 < s₁ σ (mixIndex σ))
    {X : Matrix (Fin (r + 1)) (Fin (r - mixIndex σ)) ℝ} (hX : IsMixer σ (mixIndex σ) X)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A : Ω → Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ} (hint : ∀ i j, Integrable (fun ω => A ω i j) μ)
    (hmean : ∀ i j, ∫ ω, A ω i j ∂μ = Matrix.diagonal σ i j)
    (hrank : ∀ᵐ ω ∂μ, (A ω).rank ≤ r)
    (hL2 : Integrable (fun ω => ‖A ω - Matrix.diagonal σ‖ ^ 2) μ) :
    (∀ b, (estimator σ (mixIndex σ) X b).rank ≤ r) ∧
    (∀ i j, signMean (fun b => estimator σ (mixIndex σ) X b i j) = Matrix.diagonal σ i j) ∧
    signMean (fun b => ‖estimator σ (mixIndex σ) X b - Matrix.diagonal σ‖ ^ 2) ≤
      ∫ ω, ‖A ω - Matrix.diagonal σ‖ ^ 2 ∂μ := by
  have hv := isValidMix_mixIndex hr hanti hσ0
  refine ⟨fun b => rank_estimator_le hv.lt.le X b, estimator_unbiased hσ0 hv hs hX, ?_⟩
  rw [estimator_variance_eq hσ0 hv hs hX]
  exact variance_lower_bound hv.lt (s₁_nonneg hσ0 _) (fun i hi => div_le_of_kept hr hanti hσ0 hi)
    hint hmean hrank hL2

/-- The uniform law on the signs `s ∈ {-1, 1}^{k+1}`. -/
noncomputable def signLaw (k : ℕ) : Measure (Fin (k + 1) → Bool) :=
  ProbabilityTheory.uniformOn Set.univ

instance (k : ℕ) : IsProbabilityMeasure (signLaw k) := by
  unfold signLaw
  infer_instance

/-- `signMean` is the integral for the uniform law. -/
lemma integral_signLaw {k : ℕ} (f : (Fin (k + 1) → Bool) → ℝ) :
    ∫ b, f b ∂signLaw k = signMean f := by
  rw [integral_fintype .of_finite, signMean, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h : (signLaw k).real {b} = 1 / 2 ^ (k + 1) := by
    have hu : signLaw k {b} = ((2 : ENNReal) ^ (k + 1))⁻¹ := by
      unfold signLaw
      rw [ProbabilityTheory.uniformOn_univ, Measure.count_singleton]
      simp
    rw [measureReal_def, hu]
    simp [ENNReal.toReal_inv]
  rw [h, smul_eq_mul]

/-- **The estimator of arXiv 2009.03887, Sec. 4.1.2, belongs to the class of competitors** of
`estimator_minimum_variance`, for the uniform law on the signs, and attains
`variance_lower_bound`.  So the class is not empty, and `s₁²/k - s₂` is a minimum. -/
theorem estimator_isCompetitor {σ : Fin (r + 1) → ℝ} {m : ℕ} (hσ0 : ∀ i, 0 ≤ σ i)
    (hm : IsValidMix σ m) (hs : 0 < s₁ σ m) {X : Matrix (Fin (r + 1)) (Fin (r - m)) ℝ}
    (hX : IsMixer σ m X) :
    (∀ i j, Integrable (fun b => estimator σ m X b i j) (signLaw (r - m))) ∧
    (∀ i j, ∫ b, estimator σ m X b i j ∂signLaw (r - m) = Matrix.diagonal σ i j) ∧
    (∀ᵐ b ∂signLaw (r - m), (estimator σ m X b).rank ≤ r) ∧
    Integrable (fun b => ‖estimator σ m X b - Matrix.diagonal σ‖ ^ 2) (signLaw (r - m)) ∧
    ∫ b, ‖estimator σ m X b - Matrix.diagonal σ‖ ^ 2 ∂signLaw (r - m) =
      s₁ σ m ^ 2 / ((r - m : ℕ) : ℝ) - s₂ σ m := by
  refine ⟨fun i j => .of_finite, fun i j => ?_,
    ae_of_all _ fun b => rank_estimator_le hm.lt.le X b, .of_finite, ?_⟩
  · rw [integral_signLaw, estimator_unbiased hσ0 hm hs hX]
  · rw [integral_signLaw, estimator_variance_eq hσ0 hm hs hX]

/-- The degenerate case `s₁ = 0` of arXiv 2009.03887, Sec. 4.1.2, where the paper's `x₀` is
undefined: `Z = 0` for every `X`, and `Σ̃ = Σ` exactly. -/
theorem estimator_of_s₁_eq_zero {σ : Fin (r + 1) → ℝ} {m : ℕ} (hσ0 : ∀ i, 0 ≤ σ i)
    (hs : s₁ σ m = 0) (X : Matrix (Fin (r + 1)) (Fin (r - m)) ℝ) (b : Fin (r - m + 1) → Bool) :
    estimator σ m X b = Matrix.diagonal σ := by
  rw [estimator_eq hσ0 (by rw [hs, zero_div]), hs, zero_div, zero_smul, add_zero]
  congr 1
  ext i
  by_cases hi : (i : ℕ) < m
  · simp [hi]
  · have hmem : i ∈ Finset.univ.filter (fun i : Fin (r + 1) => m ≤ (i : ℕ)) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega⟩
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hσ0 i).1 hs i hmem
    simp [hi, this]

/-- The index `m = r` of App. A.2 of arXiv 2009.03887 (`0`-based `r - 1`, `k = 1`) is always
valid. -/
theorem isValidMix_pred (hr : 1 ≤ r) {σ : Fin (r + 1) → ℝ} (hanti : Antitone σ)
    (hσ0 : ∀ i, 0 ≤ σ i) : IsValidMix σ (r - 1) := by
  refine ⟨by omega, fun i hi => ?_⟩
  have e : r - (r - 1) = 1 := by omega
  obtain ⟨h, hle⟩ := mem_stopSet_pred hr hσ0
  rw [e] at hle ⊢
  exact (mul_le_mul_of_nonneg_left (hanti (Fin.le_def.2 hi)) (by positivity)).trans hle

/-- **App. A.2 of arXiv 2009.03887, the per-sample variance for `m = r`, `k = 1`.**
`s₁ = σ_r + σ_q`, `s₂ = σ_r² + σ_q²`, and `E‖Σ̃ - Σ‖_F² = 2 σ_r σ_q` exactly.  The paper's
`(2/N) σ_r σ_q` per element is this value; its accumulation (18) adds variances over the samples.
For a general `σ` the index `m = r` is an allowed choice, not the optimal `m`. -/
theorem estimator_variance_of_pred (hr : 1 ≤ r) {σ : Fin (r + 1) → ℝ} (hanti : Antitone σ)
    (hσ0 : ∀ i, 0 ≤ σ i) (hs : 0 < s₁ σ (r - 1)) {X : Matrix (Fin (r + 1)) (Fin (r - (r - 1))) ℝ}
    (hX : IsMixer σ (r - 1) X) :
    signMean (fun b => ‖estimator σ (r - 1) X b - Matrix.diagonal σ‖ ^ 2) =
      2 * σ ⟨r - 1, by omega⟩ * σ (Fin.last r) := by
  rw [estimator_variance_eq hσ0 (isValidMix_pred hr hanti hσ0) hs hX]
  have e : r - (r - 1) = 1 := by omega
  have e1 : r - 1 + 1 = r := by omega
  have hlast : (⟨r, by omega⟩ : Fin (r + 1)) = Fin.last r := rfl
  have hs₁ : s₁ σ (r - 1) = σ ⟨r - 1, by omega⟩ + σ (Fin.last r) := by
    rw [s₁_eq_add σ (show r - 1 < r + 1 by omega), e1, s₁_eq_add σ (show r < r + 1 by omega), hlast]
    have : s₁ σ (r + 1) = 0 := by
      refine Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hσ0 i) |>.2 fun i hi => ?_
      have := (Finset.mem_filter.1 hi).2
      omega
    rw [this, add_zero]
  have hs₂ : s₂ σ (r - 1) = σ ⟨r - 1, by omega⟩ ^ 2 + σ (Fin.last r) ^ 2 := by
    have hf : Finset.univ.filter (fun i : Fin (r + 1) => r - 1 ≤ (i : ℕ)) =
        {⟨r - 1, by omega⟩, Fin.last r} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Fin.ext_iff, Fin.val_last]
      omega
    rw [s₂, hf, Finset.sum_pair]
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_last] at this
    omega
  rw [hs₁, hs₂, e]
  simp only [Nat.cast_one, div_one]
  ring

/-- **A false claim of arXiv 2009.03887, App. A.2.**  The paper states that the minimum variance is
`s₁²/k + s₂`.  It is `s₁²/k - s₂` (`estimator_variance_eq`, `variance_lower_bound`), which is what
Benzing et al. (2019) prove and what the paper's own `k = 1` value `2 σ_r σ_q` requires.  For
`σ = (1, 1)`, `q = 2`, `r = 1`: the paper's index is `m = 0` (0-based), the printed formula gives
`6`, and an unbiased rank-one estimator has variance `2`. -/
theorem appA2_min_variance_formula_false :
    ∃ (σ : Fin 2 → ℝ) (X : Matrix (Fin 2) (Fin (1 - mixIndex σ)) ℝ), Antitone σ ∧ (∀ i, 0 ≤ σ i) ∧
      mixIndex σ = 0 ∧ IsMixer σ (mixIndex σ) X ∧ (∀ b, (estimator σ _ X b).rank ≤ 1) ∧
      (∀ i j, signMean (fun b => estimator σ _ X b i j) = Matrix.diagonal σ i j) ∧
      s₁ σ (mixIndex σ) ^ 2 / ((1 - mixIndex σ : ℕ) : ℝ) + s₂ σ (mixIndex σ) = 6 ∧
      signMean (fun b => ‖estimator σ _ X b - Matrix.diagonal σ‖ ^ 2) = 2 := by
  let σ : Fin 2 → ℝ := fun _ => 1
  have hanti : Antitone σ := fun _ _ _ => le_rfl
  have hσ0 : ∀ i, 0 ≤ σ i := fun _ => zero_le_one
  have hsum : s₁ σ 0 = 2 := by simp [s₁, σ]
  have hsum2 : s₂ σ 0 = 2 := by simp [s₂, σ]
  have hmix : mixIndex σ = 0 := by
    apply Nat.eq_zero_of_le_zero
    refine Nat.sInf_le ⟨by omega, ?_⟩
    rw [hsum]
    simp [σ]
  have hv := isValidMix_mixIndex (le_refl 1) hanti hσ0
  have hs : 0 < s₁ σ (mixIndex σ) := by rw [hmix, hsum]; norm_num
  obtain ⟨X, hX⟩ := exists_isMixer hv hs
  refine ⟨σ, X, hanti, hσ0, hmix, hX, fun b => rank_estimator_le hv.lt.le X b,
    estimator_unbiased hσ0 hv hs hX, ?_, ?_⟩
  · rw [hmix, hsum, hsum2]
    norm_num
  · rw [estimator_variance_eq hσ0 hv hs hX, hmix, hsum, hsum2]
    norm_num

/-! #### The lift from the core `Σ` to the gradient `L Rᵀ` -/

section Lift

variable {no ni : Type*} [Fintype no] [Fintype ni]

/-- The expectation of a finite sum. -/
lemma signMean_sum {k : ℕ} {ι : Type*} (s : Finset ι) (f : ι → (Fin (k + 1) → Bool) → ℝ) :
    signMean (fun b => ∑ l ∈ s, f l b) = ∑ l ∈ s, signMean (f l) := by
  unfold signMean
  rw [Finset.sum_comm, Finset.mul_sum]

/-- Constants factor out of the expectation. -/
lemma signMean_mul_const {k : ℕ} (f : (Fin (k + 1) → Bool) → ℝ) (c d : ℝ) :
    signMean (fun b => c * f b * d) = c * signMean f * d := by
  unfold signMean
  have : ∑ b, c * f b * d = c * (∑ b, f b) * d := by
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [this]
  ring

omit [Fintype no] [Fintype ni] in
/-- The entries of `U A Vᵀ`. -/
lemma mul_mul_transpose_apply {q q' : Type*} [Fintype q] [Fintype q'] (U : Matrix no q ℝ)
    (A : Matrix q q' ℝ) (V : Matrix ni q' ℝ) (i : no) (j : ni) :
    (U * A * Vᵀ) i j = ∑ l', ∑ l, U i l * A l l' * V j l' := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l' _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul, Matrix.transpose_apply]

omit [Fintype no] [Fintype ni] in
/-- **The estimator of the gradient** (arXiv 2009.03887, Sec. 4.1.2): if `M = U Σ Vᵀ` is the SVD of
`L Rᵀ` from Eq. (1), then `U Σ̃ Vᵀ`, of rank at most `r`, is unbiased for `M`. -/
theorem lifted_unbiased {σ : Fin (r + 1) → ℝ} {m : ℕ} (hσ0 : ∀ i, 0 ≤ σ i) (hm : IsValidMix σ m)
    (hs : 0 < s₁ σ m) {X : Matrix (Fin (r + 1)) (Fin (r - m)) ℝ} (hX : IsMixer σ m X)
    (U : Matrix no (Fin (r + 1)) ℝ) (V : Matrix ni (Fin (r + 1)) ℝ) (i : no) (j : ni) :
    signMean (fun b => (U * estimator σ m X b * Vᵀ) i j) =
      (U * Matrix.diagonal σ * Vᵀ) i j := by
  simp_rw [mul_mul_transpose_apply, signMean_sum]
  refine Finset.sum_congr rfl fun l' _ => Finset.sum_congr rfl fun l _ => ?_
  rw [signMean_mul_const, estimator_unbiased hσ0 hm hs hX]

/-- The variance of the lifted estimator of arXiv 2009.03887, Sec. 4.1.2, is that of `Σ̃`:
`E‖U Σ̃ Vᵀ - U Σ Vᵀ‖_F² = s₁²/k - s₂`. -/
theorem lifted_variance_eq {σ : Fin (r + 1) → ℝ} {m : ℕ} (hσ0 : ∀ i, 0 ≤ σ i) (hm : IsValidMix σ m)
    (hs : 0 < s₁ σ m) {X : Matrix (Fin (r + 1)) (Fin (r - m)) ℝ} (hX : IsMixer σ m X)
    {U : Matrix no (Fin (r + 1)) ℝ} {V : Matrix ni (Fin (r + 1)) ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) :
    signMean (fun b => ‖U * estimator σ m X b * Vᵀ - U * Matrix.diagonal σ * Vᵀ‖ ^ 2) =
      s₁ σ m ^ 2 / ((r - m : ℕ) : ℝ) - s₂ σ m := by
  have e : ∀ b, ‖U * estimator σ m X b * Vᵀ - U * Matrix.diagonal σ * Vᵀ‖ =
      ‖estimator σ m X b - Matrix.diagonal σ‖ := fun b => by
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, Frobenius.norm_mul_transpose_of_orthonormal hV,
      Frobenius.norm_mul_of_orthonormal hU]
  simp_rw [e]
  exact estimator_variance_eq hσ0 hm hs hX

/-- **The estimator of the gradient has minimum variance** (arXiv 2009.03887, Sec. 4.1.2).  Let
`M = U Σ Vᵀ` be a thin SVD with `q = r + 1` components, e.g. `M = L Rᵀ` from Eq. (1).  Among all
unbiased estimators `B` of `M` of rank at most `r` a.s., in the full space `ℝ^{n_o × n_i}`, on any
probability space, `U Σ̃ Vᵀ` has the smallest `E‖· - M‖_F²`.  The paper states optimality for `Σ̃`
only; the competitors here are not assumed to have the singular vectors of `M`. -/
theorem lifted_minimum_variance (hr : 1 ≤ r) {M : Matrix no ni ℝ}
    {U : Matrix no (Fin (r + 1)) ℝ} {σ : Fin (r + 1) → ℝ} {V : Matrix ni (Fin (r + 1)) ℝ}
    (hM : IsThinSVD M U σ V) (hs : 0 < s₁ σ (mixIndex σ))
    {X : Matrix (Fin (r + 1)) (Fin (r - mixIndex σ)) ℝ} (hX : IsMixer σ (mixIndex σ) X)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : Ω → Matrix no ni ℝ} (hint : ∀ i j, Integrable (fun ω => B ω i j) μ)
    (hmean : ∀ i j, ∫ ω, B ω i j ∂μ = M i j) (hrank : ∀ᵐ ω ∂μ, (B ω).rank ≤ r)
    (hL2 : Integrable (fun ω => ‖B ω - M‖ ^ 2) μ) :
    signMean (fun b => ‖U * estimator σ (mixIndex σ) X b * Vᵀ - M‖ ^ 2) ≤
      ∫ ω, ‖B ω - M‖ ^ 2 ∂μ := by
  have hanti := hM.antitone
  have hσ0 := hM.nonneg
  have hv := isValidMix_mixIndex hr hanti hσ0
  have hU := hM.orthU
  have hV := hM.orthV
  rw [hM.eq, lifted_variance_eq hσ0 hv hs hX hU hV, ← hM.eq]
  -- the core of `B`
  let A : Ω → Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ := fun ω => Uᵀ * B ω * V
  have hentry : ∀ (C : Matrix no ni ℝ) (i j : Fin (r + 1)),
      (Uᵀ * C * V) i j = ∑ l', ∑ l, U l i * C l l' * V l' j := by
    intro C i j
    have := mul_mul_transpose_apply Uᵀ C Vᵀ i j
    simpa using this
  have hcore : Uᵀ * M * V = Matrix.diagonal σ := by
    rw [hM.eq]
    calc Uᵀ * (U * Matrix.diagonal σ * Vᵀ) * V = (Uᵀ * U) * Matrix.diagonal σ * (Vᵀ * V) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal σ := by rw [hU, hV, Matrix.one_mul, Matrix.mul_one]
  have hAint : ∀ i j, Integrable (fun ω => A ω i j) μ := by
    intro i j
    simp only [A, hentry]
    exact integrable_finsetSum _ fun l' _ => integrable_finsetSum _ fun l _ =>
      ((hint l l').const_mul _).mul_const _
  have hAmean : ∀ i j, ∫ ω, A ω i j ∂μ = Matrix.diagonal σ i j := by
    intro i j
    simp only [A, hentry]
    rw [← hcore, hentry, integral_finsetSum _ fun l' _ => integrable_finsetSum _ fun l _ =>
      ((hint l l').const_mul _).mul_const _]
    refine Finset.sum_congr rfl fun l' _ => ?_
    rw [integral_finsetSum _ fun l _ => ((hint l l').const_mul _).mul_const _]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_mul_const, integral_const_mul, hmean]
  have hArank : ∀ᵐ ω ∂μ, (A ω).rank ≤ r := by
    filter_upwards [hrank] with ω hω
    exact ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans hω
  have hle : ∀ᵐ ω ∂μ, ‖A ω - Matrix.diagonal σ‖ ^ 2 ≤ ‖B ω - M‖ ^ 2 := by
    refine ae_of_all _ fun ω => ?_
    have e : A ω - Matrix.diagonal σ = Uᵀ * (B ω - M) * V := by
      rw [← hcore, Matrix.mul_sub, Matrix.sub_mul]
    rw [e]
    exact pow_le_pow_left₀ (norm_nonneg _)
      ((norm_mul_le_of_orthonormal hV _).trans (norm_transpose_mul_le hU _)) 2
  exact variance_lower_bound_of_le hv.lt (s₁_nonneg hσ0 _)
    (fun i hi => div_le_of_kept hr hanti hσ0 hi) hAint hAmean hArank hL2 hle

end Lift

end Estimator

/-! ### The hypotheses of Theorem 1 are satisfiable with a nonzero perturbation -/

section Example

/-- The clamp to `[-1, 1]`. -/
private noncomputable def clamp (u : ℝ) : ℝ := max (-1) (min 1 u)

private lemma isMetricProj_clamp : IsMetricProj (Set.Icc (-1 : ℝ) 1) clamp := by
  intro u
  refine ⟨⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩, fun v hv => ?_⟩
  simp only [Real.norm_eq_abs, clamp]
  rcases le_total u (-1) with h | h
  · rw [min_eq_right (by linarith), max_eq_left h, abs_of_nonpos (by linarith),
      abs_of_nonpos (by linarith [hv.1])]
    linarith [hv.1]
  · rcases le_total u 1 with h' | h'
    · rw [min_eq_right h', max_eq_right h, sub_self, abs_zero]
      exact abs_nonneg _
    · rw [min_eq_left h', max_eq_right (by norm_num), abs_of_nonneg (by linarith),
        abs_of_nonneg (by linarith [hv.2])]
      linarith [hv.2]

/-- The iterates of the example. -/
private noncomputable def exW : ℕ → ℝ
  | 0 => 1
  | t + 1 => clamp (exW t - (1 / √(t : ℝ)) • (exW t + -exW t / 2))

private lemma exW_mem (t : ℕ) : exW t ∈ Set.Icc (-1 : ℝ) 1 := by
  cases t with
  | zero => simp [exW]
  | succ t => exact (isMetricProj_clamp _).1

/-- **The hypotheses of Theorem 1 of arXiv 2009.03887 (`theorem1_regret_of_eq15`) are satisfiable**
with a nonzero perturbation at the boundary of (15): `f^t(w) = w²/2` on `F = [-1, 1]`, `c = 1`,
`w⋆ = 0`, `ε^t = -w^t/2`. -/
theorem theorem1_satisfiable :
    ∃ (F : Set ℝ) (P : ℝ → ℝ) (f : ℕ → ℝ → ℝ) (g ε w : ℕ → ℝ), IsMetricProj F P ∧
      (∀ x ∈ F, ∀ y ∈ F, ‖x - y‖ ≤ 2) ∧ (∀ t ≥ 1, StrongConvexOn F 1 (f t)) ∧
      (∀ t ≥ 1, HasGradientAt (f t) (g t) (w t)) ∧ (∀ t ≥ 1, ‖g t‖ ≤ 1) ∧
      (∀ t ≥ 1, ‖ε t‖ ≤ 1 / 2) ∧ (0 : ℝ) ∈ F ∧ w 1 ∈ F ∧
      (∀ t ≥ 1, w (t + 1) = P (w t - (1 / √(t : ℝ)) • (g t + ε t))) ∧
      (∀ t ≥ 1, ‖ε t‖ ≤ 1 / 2 * ‖w t - 0‖) ∧ ε 1 ≠ 0 := by
  refine ⟨Set.Icc (-1) 1, clamp, fun _ x => x ^ 2 / 2, exW, fun t => -exW t / 2, exW,
    isMetricProj_clamp, ?_, ?_, ?_, ?_, ?_, ?_, exW_mem 1, ?_, ?_, ?_⟩
  · intro x hx y hy
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  · intro t _
    rw [strongConvexOn_iff_convex]
    have e : (fun x : ℝ => x ^ 2 / 2 - 1 / (2 : ℝ) * ‖x‖ ^ 2) = fun _ => 0 := by
      ext x
      rw [Real.norm_eq_abs, sq_abs]
      ring
    rw [e]
    exact convexOn_const 0 (convex_Icc _ _)
  · intro t _
    have h : HasDerivAt (fun x : ℝ => x ^ 2 / 2) (exW t) (exW t) := by
      have := (hasDerivAt_pow 2 (exW t)).div_const 2
      simpa using this
    simpa using h.hasGradientAt
  · intro t _
    exact abs_le.2 (exW_mem t)
  · intro t _
    have := exW_mem t
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [this.1, this.2]
  · exact ⟨by norm_num, by norm_num⟩
  · intro t _
    rfl
  · intro t _
    dsimp only
    rw [sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, neg_div, abs_neg, abs_div]
    norm_num
    linarith
  · have h1 : exW 1 = 1 := by
      simp [exW, clamp]
    simp [h1]

end Example

end LeanDLRA.Literature.P2009_03887
