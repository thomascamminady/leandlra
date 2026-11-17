import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Matrix.Orthonormal

/-!
# Dynamical low-rank approximation at and beyond the loss of rank

Open problems OP-RA-46 (meaning and continuation of DLRA beyond the loss of rank) and OP-EX-20
(behaviour of DLR solutions at the maximal existence time) of `docs/survey/open-problems.json`.
Everything is on actual matrices: a rank-`r` **Dirac–Frenkel solution** of a
constant field `G` is a curve `Y(t) = U S Vᵀ` (orthonormal `U`, `V`, invertible `S`) with
`Ẏ = P(Y) G`, `P(Y)` the tangent projector of the rank-`r` manifold (`IsDFSolution`; the
projector is intrinsic by `tangentProj_eq_of_factor_eq`).

## What is proved

* **The limit exists (OP-EX-20 (a), finite-dimensional).**  A curve with `‖Ẏ‖ ≤ B` on `(a, b)`
  converges as `t ↑ b`, with `‖Y t - Y∞‖ ≤ B (b - t)` (`exists_tendsto_of_norm_deriv_le`); since
  `‖P(Y) G‖ ≤ ‖G‖`, every Dirac–Frenkel solution has a limit at the time of rank loss
  (`IsDFSolution.exists_tendsto`).
* **Self-similar solutions.**  The line `t ↦ (t - t₀) Z`, `Z = U S Vᵀ` of rank `r`, is a
  Dirac–Frenkel solution iff `Z = P(Z) G` (`isDFSolution_line_iff`), iff `(range U, range V)`
  is an invariant block of `G` and `Z = U Uᵀ G V Vᵀ` (`tangentProj_eq_iff_block`).  So a
  solution reaching `0` has one linear continuation per invariant rank-`r` block of `G`.  The
  equation has the scaling symmetry `Y ↦ c Y(·/c)` (`IsDFSolution.scale`).
* **Rank loss in finite time for a smooth (constant) problem.**  `G₀ = diag(-2, 3)`, rank one:
  `Y(t) = -2 t E₁₁` solves the Dirac–Frenkel equation from `Y(-1) = 2 E₁₁`, its singular value
  reaches `0` at `t = 0` (`incoming_isDFSolution`), although the exact solution
  `A(t) = diag(-2t, 3(t+1))` never loses rank.
* **The continuation is genuinely non-unique.**  Beyond `t = 0` there are
  (i) the two linear continuations `-2 t E₁₁` and `3 t E₂₂` (`second_line_isDFSolution`), and
  (ii) the explicit non-linear solution `Yhet` (`Yhet_isDFSolution`), with
  `ρ = (1 + t)^{1/3}`, `m = ρ² - 1`, `q = √m`, `Yhet = (3m/ρ) [[-1, -q], [q, m]]`, which tends to
  `0` as `t ↓ 0` **with the incoming velocity** `-2 E₁₁` (`Yhet_hasDerivWithinAt_zero`):
  the glued curve is differentiable at the rank drop (`Yglue_hasDerivAt_zero`,
  `Yglue_isDFSolution`) and differs from the linear continuation (`Yhet_ne_line`).  The scaling
  symmetry turns it into a continuum `Yfam c`, `c > 0`, of pairwise distinct
  (`Yfam_injective`) differentiable continuations with the same one-sided derivative
  (`YglueFam_hasDerivAt_zero`, `YglueFam_isDFSolution`).  So neither continuity nor
  differentiability at the drop selects a continuation; the answer to OP-EX-20 (c) is negative
  already for a constant field in `ℝ^{2×2}`.  In self-similar variables `Z = Y/t`, `τ = log t`,
  `Yhet` is the heteroclinic orbit of `Z' = P(Z) G₀ - Z` from the saddle `-2 E₁₁` to the sink
  `3 E₂₂`; `G₀` is chosen so that it is elementary (`b = -3a/2`).
* **What the BUG integrator selects.**  A BUG step (fixed-rank or augmented, matrix form
  `IsBUGStepMat`) started on an invariant block `(range U, range V)` of `G` stays on it: the
  new projectors equal the old ones and the Galerkin step is exactly `U (S + h Uᵀ G V) Vᵀ`,
  also for singular `S` (`IsBUGStepMat.invariant`, `bug_trajectory`).  For `G₀` every BUG
  trajectory from `(e₁, [2], e₁)` is `Yₖ = -2 (-1 + k h) E₁₁` for all `k` and all `h`
  (`bug_example`): the integrator reproduces the linear continuation with zero error through
  the rank drop, so its `h → 0` limit is that continuation, and it never sees the heteroclinic
  family or the other block.  For the fixed-rank BUG the step is well defined iff `K ≠ 0`
  (`IsBUGStepMat.capU_of_isUnit`).

## Not proved

That the incoming solution is the unique Dirac–Frenkel solution on `[-1, 0)` (standard: the
field is locally Lipschitz where `σ_r > 0`); that the limit at a maximal existence time has rank
`< r` (needs local existence); a classification of all continuations; the instability of the
selected branch under perturbations (numerically evident: a perturbation of size `10⁻⁸` sends the
BUG trajectory to the `3 t E₂₂` branch).
-/

open Set Filter Topology
open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius

namespace LeanDLRA.Novel.OpRA46

open LeanDLRA LeanDLRA.Frobenius

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

variable {m n : Type*} [Fintype m] [Fintype n]

/-- A **rank-`r` Dirac–Frenkel solution** of the constant field `G` on the set `s` of times: at
every `t ∈ s` the matrix `Y t` has a factorisation `U S Vᵀ` with orthonormal `U`, `V` and
invertible `S` (so `Y t` has rank exactly `r`), and `Y` is differentiable at `t` with
`Ẏ(t) = P(Y(t)) G`, where `P(Y) Z = U Uᵀ Z + Z V Vᵀ - U Uᵀ Z V Vᵀ` is the orthogonal projector
onto the tangent space of the rank-`r` manifold at `Y` (`tangentProj`).  By
`tangentProj_eq_of_factor_eq` the projector depends only on `Y t`, so the definition is
intrinsic. -/
def IsDFSolution (r : ℕ) (G : Matrix m n ℝ) (Y : ℝ → Matrix m n ℝ) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, ∃ (U : Matrix m (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ) (V : Matrix n (Fin r) ℝ),
    Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ IsUnit S.det ∧ Y t = U * S * Vᵀ ∧
    HasDerivAt Y (tangentProj U V G) t

/-! ### The tangent projector is intrinsic -/

section Intrinsic

variable {r : ℕ} {U U' : Matrix m (Fin r) ℝ} {S S' : Matrix (Fin r) (Fin r) ℝ}
  {V V' : Matrix n (Fin r) ℝ}

/-- If `U S Vᵀ = U' S' V'ᵀ` with orthonormal factors and invertible cores, then `U Uᵀ = U' U'ᵀ`. -/
theorem colProj_eq_of_factor_eq (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hS : IsUnit S.det)
    (hU' : U'ᵀ * U' = 1) (hV' : V'ᵀ * V' = 1) (hS' : IsUnit S'.det)
    (h : U * S * Vᵀ = U' * S' * V'ᵀ) : U * Uᵀ = U' * U'ᵀ := by
  -- `U' U'ᵀ` fixes `Y = U S Vᵀ`, and `U Uᵀ = Y (V S⁻¹ Uᵀ)`.
  have key : ∀ {U₁ : Matrix m (Fin r) ℝ} {S₁ : Matrix (Fin r) (Fin r) ℝ} {V₁ : Matrix n (Fin r) ℝ}
      {U₂ : Matrix m (Fin r) ℝ} {S₂ : Matrix (Fin r) (Fin r) ℝ} {V₂ : Matrix n (Fin r) ℝ},
      U₁ᵀ * U₁ = 1 → V₁ᵀ * V₁ = 1 → IsUnit S₁.det → U₂ᵀ * U₂ = 1 →
      U₁ * S₁ * V₁ᵀ = U₂ * S₂ * V₂ᵀ → U₂ * U₂ᵀ * U₁ = U₁ := by
    intro U₁ S₁ V₁ U₂ S₂ V₂ hU₁ hV₁ hS₁ hU₂ h
    have h1 : U₂ * U₂ᵀ * (U₁ * S₁ * V₁ᵀ) = U₁ * S₁ * V₁ᵀ := by
      rw [h, Curvature.colProj_mul_factor hU₂]
    have h3 := Curvature.factor_mul_ginv (U := U₁) (S := S₁) hV₁ hS₁
    have h2 : U₂ * U₂ᵀ * (U₁ * U₁ᵀ) = U₁ * U₁ᵀ := by
      calc U₂ * U₂ᵀ * (U₁ * U₁ᵀ) = U₂ * U₂ᵀ * (U₁ * S₁ * V₁ᵀ * (V₁ * S₁⁻¹ * U₁ᵀ)) := by rw [h3]
        _ = U₁ * S₁ * V₁ᵀ * (V₁ * S₁⁻¹ * U₁ᵀ) := by rw [← Matrix.mul_assoc, h1]
        _ = U₁ * U₁ᵀ := h3
    calc U₂ * U₂ᵀ * U₁ = U₂ * U₂ᵀ * (U₁ * U₁ᵀ) * U₁ := by
          simp only [Matrix.mul_assoc, hU₁, Matrix.mul_one]
      _ = U₁ := by rw [h2, Matrix.mul_assoc, hU₁, Matrix.mul_one]
  exact mul_transpose_eq_of_capture_of_capture (key hU hV hS hU' h) (key hU' hV' hS' hU h.symm)

/-- The row-space version of `colProj_eq_of_factor_eq`. -/
theorem rowProj_eq_of_factor_eq (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hS : IsUnit S.det)
    (hU' : U'ᵀ * U' = 1) (hV' : V'ᵀ * V' = 1) (hS' : IsUnit S'.det)
    (h : U * S * Vᵀ = U' * S' * V'ᵀ) : V * Vᵀ = V' * V'ᵀ := by
  have hT : V * Sᵀ * Uᵀ = V' * S'ᵀ * U'ᵀ := by
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  exact colProj_eq_of_factor_eq hV hU (by rwa [Matrix.det_transpose]) hV' hU'
    (by rwa [Matrix.det_transpose]) hT

/-- **The Dirac–Frenkel projector is intrinsic.**  Two factorisations of the same rank-`r`
matrix give the same tangent projector. -/
theorem tangentProj_eq_of_factor_eq (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hS : IsUnit S.det)
    (hU' : U'ᵀ * U' = 1) (hV' : V'ᵀ * V' = 1) (hS' : IsUnit S'.det)
    (h : U * S * Vᵀ = U' * S' * V'ᵀ) :
    (tangentProj U V : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) = tangentProj U' V' := by
  have hc := colProj_eq_of_factor_eq hU hV hS hU' hV' hS' h
  have hr := rowProj_eq_of_factor_eq hU hV hS hU' hV' hS' h
  ext Z
  simp only [tangentProj_apply]
  rw [Matrix.mul_assoc Z V, Matrix.mul_assoc Z V', Matrix.mul_assoc (U * Uᵀ * Z) V,
    Matrix.mul_assoc (U' * U'ᵀ * Z) V', hc, hr]

end Intrinsic

/-! ### Speed bound -/

/-- The Dirac–Frenkel velocity is bounded by the field: `‖P(Y) G‖ ≤ ‖G‖`. -/
theorem norm_tangentProj_le {r : ℕ} {U : Matrix m (Fin r) ℝ} {V : Matrix n (Fin r) ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (G : Matrix m n ℝ) : ‖tangentProj U V G‖ ≤ ‖G‖ :=
  (isOrthProj_tangentProj hU hV).norm_le G

/-! ### The limit at the time of rank loss -/

section Limit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Mean value inequality on `Ioo a b`. -/
private theorem norm_sub_le_of_deriv_le {Y Y' : ℝ → E} {a b B : ℝ}
    (hd : ∀ t ∈ Ioo a b, HasDerivAt Y (Y' t) t) (hB : ∀ t ∈ Ioo a b, ‖Y' t‖ ≤ B)
    {t t' : ℝ} (ht : t ∈ Ioo a b) (ht' : t' ∈ Ioo a b) (htt' : t ≤ t') :
    ‖Y t' - Y t‖ ≤ B * (t' - t) :=
  norm_image_sub_le_of_norm_deriv_le_segment' (f := Y) (f' := Y') (a := t) (b := t') (C := B)
    (fun x hx => (hd x ⟨ht.1.trans_le hx.1, hx.2.trans_lt ht'.2⟩).hasDerivWithinAt)
    (fun x hx => hB x ⟨ht.1.trans_le hx.1, hx.2.trans ht'.2⟩) t' ⟨htt', le_rfl⟩

/-- **A curve with bounded velocity has a limit at the end of its interval of existence.**  If
`Y` is differentiable on `(a, b)` with `‖Ẏ‖ ≤ B`, then `Y(t) → Ylim` as `t ↑ b`, with
`‖Y t - Ylim‖ ≤ B (b - t)`.  This is the finite-dimensional content of OP-EX-20 (a): for the
Dirac–Frenkel equation `‖Ẏ‖ = ‖P(Y) G‖ ≤ ‖G‖`, so the solution has a limit at the time of rank
loss (`IsDFSolution.exists_tendsto`). -/
theorem exists_tendsto_of_norm_deriv_le {Y Y' : ℝ → E} {a b B : ℝ} (hab : a < b)
    (hd : ∀ t ∈ Ioo a b, HasDerivAt Y (Y' t) t) (hB : ∀ t ∈ Ioo a b, ‖Y' t‖ ≤ B) :
    ∃ Ylim : E, Tendsto Y (𝓝[<] b) (𝓝 Ylim) ∧ ∀ t ∈ Ioo a b, ‖Y t - Ylim‖ ≤ B * (b - t) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB ((a + b) / 2) ⟨by linarith, by linarith⟩)
  set τ : ℕ → ℝ := fun k => b - (b - a) / ((k : ℝ) + 2) with hτ
  have hτmem : ∀ k, τ k ∈ Ioo a b := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have h1 : (b - a) / ((k : ℝ) + 2) < b - a := by
      rw [div_lt_iff₀ hk]; nlinarith
    have h2 : 0 < (b - a) / ((k : ℝ) + 2) := by positivity
    simp only [hτ]
    constructor <;> linarith
  have hτmono : Monotone τ := by
    intro i j hij
    have : (b - a) / ((j : ℝ) + 2) ≤ (b - a) / ((i : ℝ) + 2) :=
      div_le_div_of_nonneg_left (by linarith) (by positivity) (by exact_mod_cast (by omega))
    simp only [hτ]; linarith
  have hgap : Tendsto (fun N : ℕ => (b - a) / ((N : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hτlim : Tendsto τ atTop (𝓝 b) := by
    simpa using tendsto_const_nhds.sub hgap
  have hcauchy : CauchySeq (fun k => Y (τ k)) := by
    apply cauchySeq_of_le_tendsto_0 (s := fun k => Y (τ k))
      (fun N : ℕ => B * ((b - a) / ((N : ℝ) + 2)))
    · intro i j N hi hj
      wlog hij : i ≤ j generalizing i j
      · rw [dist_comm]; exact this j i hj hi (by omega)
      rw [dist_eq_norm, norm_sub_rev]
      calc ‖Y (τ j) - Y (τ i)‖ ≤ B * (τ j - τ i) :=
            norm_sub_le_of_deriv_le hd hB (hτmem i) (hτmem j) (hτmono hij)
        _ ≤ B * ((b - a) / ((N : ℝ) + 2)) := by
          apply mul_le_mul_of_nonneg_left _ hB0
          have h1 : τ j < b := (hτmem j).2
          have h2 : τ N ≤ τ i := hτmono hi
          simp only [hτ] at h1 h2 ⊢; linarith
    · simpa using hgap.const_mul B
  obtain ⟨Ylim, hYlim⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hbound : ∀ t ∈ Ioo a b, ‖Y t - Ylim‖ ≤ B * (b - t) := by
    intro t ht
    have hev : ∀ᶠ k in atTop, t ≤ τ k := hτlim.eventually_const_le ht.2
    have h1 : Tendsto (fun k => ‖Y t - Y (τ k)‖) atTop (𝓝 ‖Y t - Ylim‖) :=
      (tendsto_const_nhds.sub hYlim).norm
    have h2 : Tendsto (fun k => B * (τ k - t)) atTop (𝓝 (B * (b - t))) :=
      (hτlim.sub_const t).const_mul B
    exact le_of_tendsto_of_tendsto h1 h2 (hev.mono fun k hk => by
      change ‖Y t - Y (τ k)‖ ≤ B * (τ k - t)
      rw [norm_sub_rev]; exact norm_sub_le_of_deriv_le hd hB ht (hτmem k) hk)
  refine ⟨Ylim, ?_, hbound⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun t => B * (b - t)) (𝓝[<] b) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => B * (b - t)) (𝓝 b) (𝓝 (B * (b - b))) :=
      (tendsto_const_nhds.sub tendsto_id).const_mul B
    simpa using this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  have : ∀ᶠ t in 𝓝[<] b, t ∈ Ioo a b :=
    Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hab)) self_mem_nhdsWithin
  exact this.mono fun t ht => hbound t ht

end Limit

/-- **The Dirac–Frenkel solution has a limit at the time of rank loss.**  A rank-`r` DF
solution of the constant field `G` on `(a, b)` converges as `t ↑ b`, at rate
`‖Y t - Ylim‖ ≤ ‖G‖ (b - t)`, whatever happens to the singular values.  Finite-dimensional
analogue of the continuity question (a) of OP-EX-20 (arXiv 2002.02356, Thm 4.6 vs. Prop. 4.9),
and the first half of the deterministic programme of OP-RA-46. -/
theorem IsDFSolution.exists_tendsto {r : ℕ} {G : Matrix m n ℝ} {Y : ℝ → Matrix m n ℝ}
    {a b : ℝ} (hab : a < b) (hY : IsDFSolution r G Y (Ioo a b)) :
    ∃ Ylim : Matrix m n ℝ, Tendsto Y (𝓝[<] b) (𝓝 Ylim) ∧
      ∀ t ∈ Ioo a b, ‖Y t - Ylim‖ ≤ ‖G‖ * (b - t) := by
  refine exists_tendsto_of_norm_deriv_le (Y' := deriv Y) hab ?_ ?_
  · intro t ht
    obtain ⟨U, S, V, -, -, -, -, hd⟩ := hY t ht
    exact hd.differentiableAt.hasDerivAt
  · intro t ht
    obtain ⟨U, S, V, hU, hV, -, -, hd⟩ := hY t ht
    rw [hd.deriv]
    exact norm_tangentProj_le hU hV G

/-! ### Lines through zero: self-similar Dirac–Frenkel solutions -/

section Line

variable {r : ℕ} {G : Matrix m n ℝ} {U : Matrix m (Fin r) ℝ} {S : Matrix (Fin r) (Fin r) ℝ}
  {V : Matrix n (Fin r) ℝ}

/-- Abstract form of `tangentProj_eq_iff_block` for idempotent `P`, `Q` fixing `Z`. -/
private theorem proj_block_iff [DecidableEq m] [DecidableEq n] {P : Matrix m m ℝ}
    {Q : Matrix n n ℝ} {G Z : Matrix m n ℝ}
    (hP : P * P = P) (hQ : Q * Q = Q) (hPZ : P * Z = Z) (hZQ : Z * Q = Z) :
    P * G + G * Q - P * G * Q = Z ↔
      P * G * Q = Z ∧ (1 - P) * G * Q = 0 ∧ P * G * (1 - Q) = 0 := by
  have hP2 : ∀ X : Matrix m n ℝ, P * (P * X) = P * X := fun X => by rw [← Matrix.mul_assoc, hP]
  constructor
  · intro h
    have h1 : P * G * Q = Z := by
      have := congrArg (fun X => P * X * Q) h
      simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul,
        Matrix.mul_assoc, hP2, hQ] at this
      rw [← Matrix.mul_assoc, hZQ, hPZ] at this
      rw [← this]; simp only [Matrix.mul_assoc]; abel
    have hsum : (P * G - P * G * Q) + (G * Q - P * G * Q) = 0 := by
      have : (P * G - P * G * Q) + (G * Q - P * G * Q) =
          (P * G + G * Q - P * G * Q) - P * G * Q := by abel
      rw [this, h, h1, sub_self]
    have hA : P * G - P * G * Q = 0 := by
      have := congrArg (fun X => P * X) hsum
      simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_zero, Matrix.mul_assoc, hP2,
        sub_self, add_zero] at this
      simpa [Matrix.mul_assoc] using this
    have hB : G * Q - P * G * Q = 0 := by rwa [hA, zero_add] at hsum
    refine ⟨h1, ?_, ?_⟩
    · rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul]; exact hB
    · rw [Matrix.mul_sub, Matrix.mul_one]; exact hA
  · rintro ⟨h1, h2, h3⟩
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul] at h2
    rw [Matrix.mul_sub, Matrix.mul_one] at h3
    have e : P * G + G * Q - P * G * Q = (P * G - P * G * Q) + (G * Q - P * G * Q) + P * G * Q := by
      abel
    rw [e, h3, h2, zero_add, zero_add, h1]

/-- `Z = P(Z) G` for `Z = U S Vᵀ` iff `G` is block diagonal with respect to
`range U ⊕ (range U)^⊥` and `range V ⊕ (range V)^⊥` and `Z` is its `(U, V)` block. -/
theorem tangentProj_eq_iff_block [DecidableEq m] [DecidableEq n] (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) :
    tangentProj U V G = U * S * Vᵀ ↔
      U * Uᵀ * G * (V * Vᵀ) = U * S * Vᵀ ∧ (1 - U * Uᵀ) * G * (V * Vᵀ) = 0 ∧
        U * Uᵀ * G * (1 - V * Vᵀ) = 0 := by
  have hPU : U * Uᵀ * (U * Uᵀ) = U * Uᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul]
  have hPV : V * Vᵀ * (V * Vᵀ) = V * Vᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ, hV, Matrix.one_mul]
  rw [tangentProj_apply, Matrix.mul_assoc G V Vᵀ, Matrix.mul_assoc (U * Uᵀ * G) V Vᵀ]
  exact proj_block_iff hPU hPV (Curvature.colProj_mul_factor hU) (Curvature.factor_mul_rowProj hV)

/-- Factorisation of a nonzero multiple: `c • (U S Vᵀ) = U (c • S) Vᵀ` with `c • S` invertible. -/
private theorem smul_factor (hS : IsUnit S.det) {c : ℝ} (hc : c ≠ 0) :
    IsUnit (c • S).det ∧ c • (U * S * Vᵀ) = U * (c • S) * Vᵀ := by
  refine ⟨?_, by simp [Matrix.mul_smul, Matrix.smul_mul]⟩
  rw [Matrix.det_smul]
  exact ((isUnit_iff_ne_zero.2 hc).pow _).mul hS

/-- **Self-similar Dirac–Frenkel solutions.**  The line `t ↦ (t - t₀) Z` through zero, with
`Z = U S Vᵀ` of rank `r`, is a rank-`r` Dirac–Frenkel solution of the constant field `G` on
`ℝ \ {t₀}` if and only if `Z = P(Z) G`, i.e. (by `tangentProj_eq_iff_block`) iff `G` maps
`range V` into `range U` and `range U` into `range V` (an invariant block of `G`) and `Z` is the
corresponding block `U Uᵀ G V Vᵀ`.  Consequence: a Dirac–Frenkel solution that reaches zero at
`t₀` has as many linear continuations as `G` has invariant rank-`r` blocks, which is more than
one as soon as `rank G > r` (and a continuum when singular values of `G` coincide). -/
theorem isDFSolution_line_iff (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hS : IsUnit S.det)
    (t₀ : ℝ) :
    IsDFSolution r G (fun t => (t - t₀) • (U * S * Vᵀ)) {t | t ≠ t₀} ↔
      tangentProj U V G = U * S * Vᵀ := by
  constructor
  · intro h
    obtain ⟨U', S', V', hU', hV', hS', hY, hd⟩ := h (t₀ + 1) (by simp)
    have hlin : HasDerivAt (fun t => (t - t₀) • (U * S * Vᵀ)) ((1 : ℝ) • (U * S * Vᵀ)) (t₀ + 1) :=
      ((hasDerivAt_id _).sub_const t₀).smul_const _
    have hfac : U * S * Vᵀ = U' * S' * V'ᵀ := by simpa using hY
    rw [tangentProj_eq_of_factor_eq hU hV hS hU' hV' hS' hfac]
    simpa using (hlin.unique hd).symm
  · intro h t ht
    have hc : t - t₀ ≠ 0 := sub_ne_zero.2 ht
    obtain ⟨hdet, hfac⟩ := smul_factor (U := U) (V := V) hS hc
    refine ⟨U, (t - t₀) • S, V, hU, hV, hdet, hfac, ?_⟩
    rw [h]
    simpa using ((hasDerivAt_id t).sub_const t₀).smul_const (U * S * Vᵀ)

end Line

/-! ### Scaling symmetry -/

/-- **Scaling symmetry of the Dirac–Frenkel equation with a constant field.**  Since the tangent
projector is `0`-homogeneous, `P(c Y) = P(Y)`, the curve `t ↦ c Y(t₀ + (t - t₀)/c)` is again a
Dirac–Frenkel solution for every `c ≠ 0`.  (For `c < 0` this includes the time reversal
`Y ↦ -Y(-t)`.)  This symmetry is what produces one-parameter families of continuations out of a
single non-linear one. -/
theorem IsDFSolution.scale {r : ℕ} {G : Matrix m n ℝ} {Y : ℝ → Matrix m n ℝ} {s : Set ℝ}
    (hY : IsDFSolution r G Y s) {c : ℝ} (hc : c ≠ 0) (t₀ : ℝ) :
    IsDFSolution r G (fun t => c • Y (t₀ + (t - t₀) / c)) {t | t₀ + (t - t₀) / c ∈ s} := by
  intro t ht
  obtain ⟨U, S, V, hU, hV, hS, hYt, hd⟩ := hY _ ht
  obtain ⟨hdet, hfac⟩ := smul_factor (U := U) (V := V) hS hc
  refine ⟨U, c • S, V, hU, hV, hdet, by simp only [hYt, hfac], ?_⟩
  have hφ : HasDerivAt (fun t => t₀ + (t - t₀) / c) (1 / c) t := by
    simpa using (((hasDerivAt_id t).sub_const t₀).div_const c).const_add t₀
  have := (hd.scomp t hφ).const_smul c
  rw [smul_smul, mul_one_div_cancel hc, one_smul] at this
  exact this

/-! ### The example: `G = diag(-2, 3)`, rank one, in `ℝ^{2×2}` -/

section Example

/-- The constant field `G₀ = diag(-2, 3)`. -/
def G₀ : Matrix (Fin 2) (Fin 2) ℝ := !![-2, 0; 0, 3]
/-- The `(1,1)` block of `G₀`: velocity of the incoming solution and of its linear continuation. -/
def Zin : Matrix (Fin 2) (Fin 2) ℝ := !![-2, 0; 0, 0]
/-- The `(2,2)` block of `G₀`: velocity of the second linear continuation. -/
def Z₂ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 3]
/-- First unit vector as a `2 × 1` matrix. -/
def e₁ : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]
/-- Second unit vector as a `2 × 1` matrix. -/
def e₂ : Matrix (Fin 2) (Fin 1) ℝ := !![0; 1]
/-- Matrix units. -/
def E₁₁ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
def E₁₂ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
def E₂₁ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
def E₂₂ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 1]

private theorem e₁_orth : e₁ᵀ * e₁ = 1 := by
  ext i j; fin_cases i; fin_cases j; simp [e₁, Matrix.mul_apply, Fin.sum_univ_two]

private theorem e₂_orth : e₂ᵀ * e₂ = 1 := by
  ext i j; fin_cases i; fin_cases j; simp [e₂, Matrix.mul_apply, Fin.sum_univ_two]

private theorem e₁_factor : e₁ * !![(-2 : ℝ)] * e₁ᵀ = Zin := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e₁, Zin, Matrix.mul_apply]

private theorem e₂_factor : e₂ * !![(3 : ℝ)] * e₂ᵀ = Z₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e₂, Z₂, Matrix.mul_apply]

private theorem tangentProj_e₁ : tangentProj e₁ e₁ G₀ = Zin := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tangentProj_apply, e₁, G₀, Zin, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul,
      dotProduct, Function.swap, Matrix.vecHead, Matrix.vecTail]

private theorem tangentProj_e₂ : tangentProj e₂ e₂ G₀ = Z₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tangentProj_apply, e₂, G₀, Z₂, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul,
      dotProduct, Function.swap, Matrix.vecHead, Matrix.vecTail]

private theorem det_one_unit {a : ℝ} (ha : a ≠ 0) :
    IsUnit (!![a] : Matrix (Fin 1) (Fin 1) ℝ).det := by
  rw [Matrix.det_fin_one_of]; exact isUnit_iff_ne_zero.2 ha

/-- **Rank loss in finite time for a constant field.**  `Y(t) = -2 t E₁₁` is the rank-one
Dirac–Frenkel solution of `Ẏ = P(Y) G₀` on `t < 0` (and on `t > 0`): it starts from
`Y(-1) = 2 E₁₁`, its singular value `-2t` tends to zero, and `Y(t) → 0` as `t ↑ 0`.  The exact
solution `A(t) = 2 E₁₁ + (t + 1) G₀ = diag(-2t, 3(t+1))` never has rank `< 1`: the rank loss is an
artefact of the approximation (the best rank-one approximation of `A` switches branches at
`t = -2/5`, the Dirac–Frenkel solution does not). -/
theorem incoming_isDFSolution : IsDFSolution 1 G₀ (fun t => t • Zin) {t | t ≠ 0} := by
  have := (isDFSolution_line_iff (G := G₀) e₁_orth e₁_orth
    (det_one_unit (by norm_num : (-2 : ℝ) ≠ 0)) 0).2
    (by rw [tangentProj_e₁, e₁_factor])
  simpa [e₁_factor] using this

/-- `Y(-1) = 2 E₁₁` and `Y(t) → 0` as `t → 0`. -/
theorem incoming_start_and_limit :
    (-1 : ℝ) • Zin = (2 : ℝ) • E₁₁ ∧ Tendsto (fun t : ℝ => t • Zin) (𝓝[<] 0) (𝓝 0) := by
  refine ⟨?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Zin, E₁₁]
  · have : Tendsto (fun t : ℝ => t • Zin) (𝓝 0) (𝓝 ((0 : ℝ) • Zin)) :=
      (continuous_id.smul continuous_const).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds

/-- **A second linear continuation.**  `Y₂(t) = 3 t E₂₂` is also a rank-one Dirac–Frenkel
solution for `t > 0` with `Y₂(t) → 0` as `t ↓ 0`.  Together with `t ↦ -2 t E₁₁` this shows that
the continuation of the Dirac–Frenkel solution beyond the rank loss is not unique (not even
among curves that are rank one for all `t > 0`): both are the lines of
`isDFSolution_line_iff` for the two invariant blocks of `G₀`.  (`Y₂` is not a `C¹`
continuation: its velocity `3 E₂₂` differs from the incoming velocity `-2 E₁₁`.) -/
theorem second_line_isDFSolution : IsDFSolution 1 G₀ (fun t => t • Z₂) {t | t ≠ 0} := by
  have := (isDFSolution_line_iff (G := G₀) e₂_orth e₂_orth
    (det_one_unit (by norm_num : (3 : ℝ) ≠ 0)) 0).2
    (by rw [tangentProj_e₂, e₂_factor])
  simpa [e₂_factor] using this

theorem lines_ne : (fun t : ℝ => t • Zin) ≠ fun t => t • Z₂ := by
  intro h
  have := congrFun h 1
  simp only [one_smul] at this
  have := congrFun (congrFun this 0) 0
  simp [Zin, Z₂] at this

/-! #### The non-linear continuation -/

/-- `ρ(s) = (1 + s)^{1/3}`. -/
noncomputable def ρ (s : ℝ) : ℝ := (1 + s) ^ ((1 : ℝ) / 3)
/-- `q(s) = √(ρ(s)² - 1)`. -/
noncomputable def q (s : ℝ) : ℝ := √(ρ s ^ 2 - 1)

/-- **The heteroclinic continuation.**  For `s ≥ 0`, with `ρ = (1+s)^{1/3}`, `m = ρ² - 1`,
`q = √m`:  `Yhet(s) = (3 m / ρ) [[-1, -q], [q, m]] = σ u vᵀ` with `σ = 3 ρ m`,
`u = (-1, q)/ρ`, `v = (1, q)/ρ`.  It leaves `0` tangentially to the incoming branch
(`Yhet(s) = -2 s E₁₁ + O(s^{3/2})`) and turns towards the other invariant block
(`Yhet(s) ∼ 3 s E₂₂` as `s → ∞`).  In the self-similar variables `Z = Y/s`, `τ = log s` it is the
heteroclinic orbit from the saddle `-E₁₁·2` to the sink `3 E₂₂` of `Z' = P(Z) G₀ - Z`; the
field `G₀ = diag(-2, 3)` is chosen so that this orbit is elementary. -/
noncomputable def Yhet (s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-3 * (ρ s ^ 2 - 1) / ρ s, -3 * (ρ s ^ 2 - 1) * q s / ρ s;
     3 * (ρ s ^ 2 - 1) * q s / ρ s, 3 * (ρ s ^ 2 - 1) ^ 2 / ρ s]

private theorem fin2_eq_sum (a b c d : ℝ) : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℝ) =
    a • E₁₁ + b • E₁₂ + c • E₂₁ + d • E₂₂ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [E₁₁, E₁₂, E₂₁, E₂₂]

private theorem hasDerivAt_fin2 {a b c d : ℝ → ℝ} {a' b' c' d' t : ℝ} (ha : HasDerivAt a a' t)
    (hb : HasDerivAt b b' t) (hc : HasDerivAt c c' t) (hd : HasDerivAt d d' t) :
    HasDerivAt (fun t => (!![a t, b t; c t, d t] : Matrix (Fin 2) (Fin 2) ℝ))
      !![a', b'; c', d'] t := by
  have e : (fun t => (!![a t, b t; c t, d t] : Matrix (Fin 2) (Fin 2) ℝ)) =
      fun t => a t • E₁₁ + b t • E₁₂ + c t • E₂₁ + d t • E₂₂ := funext fun t => fin2_eq_sum _ _ _ _
  rw [e, fin2_eq_sum]
  exact (((ha.smul_const _).add (hb.smul_const _)).add (hc.smul_const _)).add (hd.smul_const _)

private theorem ρ_pos {s : ℝ} (hs : 0 ≤ s) : 0 < ρ s := Real.rpow_pos_of_pos (by linarith) _

private theorem one_lt_ρ {s : ℝ} (hs : 0 < s) : 1 < ρ s :=
  Real.one_lt_rpow (by linarith) (by norm_num)

private theorem ρ_cube {s : ℝ} (hs : 0 ≤ s) : ρ s ^ 3 = 1 + s := by
  unfold ρ; rw [← Real.rpow_mul_natCast (by linarith)]; norm_num

private theorem q_sq {s : ℝ} (hs : 0 ≤ s) : q s ^ 2 = ρ s ^ 2 - 1 := by
  unfold q
  rw [Real.sq_sqrt]
  have : 1 ≤ ρ s := by
    rcases hs.eq_or_lt with h | h
    · subst h; simp [ρ]
    · exact (one_lt_ρ h).le
  nlinarith

private theorem q_cube {s : ℝ} (hs : 0 ≤ s) : q s ^ 3 = q s * (ρ s ^ 2 - 1) := by
  rw [← q_sq hs]; ring

private theorem q_fourth {s : ℝ} (hs : 0 ≤ s) : q s ^ 4 = (ρ s ^ 2 - 1) ^ 2 := by
  rw [← q_sq hs]; ring

private theorem q_pos {s : ℝ} (hs : 0 < s) : 0 < q s := by
  unfold q; apply Real.sqrt_pos.2; have := one_lt_ρ hs; nlinarith

private theorem hasDerivAt_ρ {s : ℝ} (hs : 0 ≤ s) : HasDerivAt ρ (1 / (3 * ρ s ^ 2)) s := by
  have h := ((hasDerivAt_id s).const_add 1).rpow_const (p := (1 : ℝ) / 3)
    (Or.inl (by simp; linarith))
  simp only [id] at h
  refine h.congr_deriv ?_
  have h1 : (0 : ℝ) ≤ 1 + s := by linarith
  unfold ρ
  rw [← Real.rpow_mul_natCast h1, show ((1 : ℝ) / 3 - 1) = -((1 / 3) * ((2 : ℕ) : ℝ)) by norm_num,
    Real.rpow_neg h1]
  field_simp

private theorem hasDerivAt_m {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt (fun s => ρ s ^ 2 - 1) (2 / (3 * ρ s)) s := by
  have hρ := hasDerivAt_ρ hs
  have hρ0 : ρ s ≠ 0 := (ρ_pos hs).ne'
  have e : (fun s => ρ s ^ 2 - 1) = fun s => ρ s * ρ s - 1 := by funext s; ring
  rw [e]
  refine ((hρ.mul hρ).sub_const 1).congr_deriv ?_
  field_simp; ring

private theorem hasDerivAt_q {s : ℝ} (hs : 0 < s) : HasDerivAt q (1 / (3 * ρ s * q s)) s := by
  have hq := q_pos hs
  have hρ := ρ_pos hs.le
  have hm0 : ρ s ^ 2 - 1 ≠ 0 := by have := one_lt_ρ hs; nlinarith
  have h := (hasDerivAt_m hs.le).sqrt hm0
  refine h.congr_deriv ?_
  unfold q at hq ⊢
  field_simp

/-- The velocity of `Yhet` for `s > 0`, in terms of `ρ` and `q`. -/
noncomputable def Dhet (s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-(ρ s ^ 2 + 1) / ρ s ^ 4, -q s * (2 * ρ s ^ 2 + 1) / ρ s ^ 4;
     q s * (2 * ρ s ^ 2 + 1) / ρ s ^ 4, (ρ s ^ 2 - 1) * (3 * ρ s ^ 2 + 1) / ρ s ^ 4]

private theorem hasDerivAt_Yhet {s : ℝ} (hs : 0 < s) : HasDerivAt Yhet (Dhet s) s := by
  have hρ := hasDerivAt_ρ hs.le
  have hq := hasDerivAt_q hs
  have hρ0 : ρ s ≠ 0 := (ρ_pos hs.le).ne'
  have hq0 : q s ≠ 0 := (q_pos hs).ne'
  have hq2 := q_sq hs.le
  have hq3 := q_cube hs.le
  have hq4 := q_fourth hs.le
  have hm := hasDerivAt_m hs.le
  have hm2 : HasDerivAt (fun s => (ρ s ^ 2 - 1) ^ 2)
      (2 / (3 * ρ s) * (ρ s ^ 2 - 1) + (ρ s ^ 2 - 1) * (2 / (3 * ρ s))) s := by
    have e : (fun s => (ρ s ^ 2 - 1) ^ 2) = fun s => (ρ s ^ 2 - 1) * (ρ s ^ 2 - 1) := by
      funext s; ring
    rw [e]; exact hm.mul hm
  unfold Yhet Dhet
  refine hasDerivAt_fin2 ?_ ?_ ?_ ?_
  · refine ((hm.const_mul (-3)).div hρ hρ0).congr_deriv ?_
    field_simp; ring
  · refine (((hm.const_mul (-3)).mul hq).div hρ hρ0).congr_deriv ?_
    simp only [Pi.mul_apply]
    field_simp; ring_nf; simp only [hq2]; ring
  · refine (((hm.const_mul 3).mul hq).div hρ hρ0).congr_deriv ?_
    simp only [Pi.mul_apply]
    field_simp; ring_nf; simp only [hq2]; ring
  · refine ((hm2.const_mul 3).div hρ hρ0).congr_deriv ?_
    field_simp; ring

/-- Left singular vector of `Yhet`. -/
noncomputable def uhet (s : ℝ) : Matrix (Fin 2) (Fin 1) ℝ := !![-1 / ρ s; q s / ρ s]
/-- Right singular vector of `Yhet`. -/
noncomputable def vhet (s : ℝ) : Matrix (Fin 2) (Fin 1) ℝ := !![1 / ρ s; q s / ρ s]

private theorem uhet_orth {s : ℝ} (hs : 0 < s) : (uhet s)ᵀ * uhet s = 1 := by
  have hρ0 : ρ s ≠ 0 := (ρ_pos hs.le).ne'
  have hq2 := q_sq hs.le
  have hq3 := q_cube hs.le
  have hq4 := q_fourth hs.le
  ext i j; fin_cases i; fin_cases j
  simp [uhet, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp; ring_nf; simp only [hq2]; ring

private theorem vhet_orth {s : ℝ} (hs : 0 < s) : (vhet s)ᵀ * vhet s = 1 := by
  have hρ0 : ρ s ≠ 0 := (ρ_pos hs.le).ne'
  have hq2 := q_sq hs.le
  have hq3 := q_cube hs.le
  have hq4 := q_fourth hs.le
  ext i j; fin_cases i; fin_cases j
  simp [vhet, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp; ring_nf; simp only [hq2]; ring

private theorem Yhet_factor {s : ℝ} (hs : 0 < s) :
    Yhet s = uhet s * !![3 * ρ s * (ρ s ^ 2 - 1)] * (vhet s)ᵀ := by
  have hρ0 : ρ s ≠ 0 := (ρ_pos hs.le).ne'
  have hq2 := q_sq hs.le
  have hq3 := q_cube hs.le
  have hq4 := q_fourth hs.le
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Yhet, uhet, vhet, Matrix.mul_apply]
    field_simp
  · simp [Yhet, uhet, vhet, Matrix.mul_apply]
    field_simp
  · simp [Yhet, uhet, vhet, Matrix.mul_apply]
    field_simp
  · simp [Yhet, uhet, vhet, Matrix.mul_apply]
    field_simp; ring_nf; simp only [hq2]; ring

private theorem tangentProj_het {s : ℝ} (hs : 0 < s) :
    tangentProj (uhet s) (vhet s) G₀ = Dhet s := by
  have hρ0 : ρ s ≠ 0 := (ρ_pos hs.le).ne'
  have hq2 := q_sq hs.le
  have hq3 := q_cube hs.le
  have hq4 := q_fourth hs.le
  ext i j
  fin_cases i <;> fin_cases j
  · simp [tangentProj_apply, uhet, vhet, G₀, Dhet, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.vecMul, dotProduct, Function.swap, Matrix.vecHead, Matrix.vecTail]
    field_simp; ring_nf; simp only [hq2]; ring
  · simp [tangentProj_apply, uhet, vhet, G₀, Dhet, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.vecMul, dotProduct, Function.swap, Matrix.vecHead, Matrix.vecTail]
    field_simp; ring_nf; simp only [hq3]; ring
  · simp [tangentProj_apply, uhet, vhet, G₀, Dhet, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.vecMul, dotProduct, Function.swap, Matrix.vecHead, Matrix.vecTail]
    field_simp; ring_nf; simp only [hq3]; ring
  · simp [tangentProj_apply, uhet, vhet, G₀, Dhet, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.vecMul, dotProduct, Function.swap, Matrix.vecHead, Matrix.vecTail]
    field_simp; ring_nf; simp only [hq2, hq4]; ring

/-- **The heteroclinic curve is a Dirac–Frenkel solution.**  `Yhet` is a rank-one Dirac–Frenkel
solution of the constant field `G₀` on `t > 0`. -/
theorem Yhet_isDFSolution : IsDFSolution 1 G₀ Yhet (Ioi 0) := by
  intro s hs
  have hs : 0 < s := hs
  refine ⟨uhet s, !![3 * ρ s * (ρ s ^ 2 - 1)], vhet s, uhet_orth hs, vhet_orth hs, ?_,
    Yhet_factor hs, ?_⟩
  · apply det_one_unit
    have := one_lt_ρ hs
    have : 0 < ρ s ^ 2 - 1 := by nlinarith
    positivity
  · rw [tangentProj_het hs]; exact hasDerivAt_Yhet hs

/-! #### The junction with the incoming solution -/

private theorem ρ_zero : ρ 0 = 1 := by simp [ρ]

theorem Yhet_zero : Yhet 0 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Yhet, ρ_zero]

private theorem continuous_ρ : Continuous ρ :=
  (continuous_const.add continuous_id).rpow_const fun _ => Or.inr (by norm_num)

private theorem continuous_q : Continuous q :=
  Real.continuous_sqrt.comp ((continuous_ρ.pow 2).sub continuous_const)

private theorem tendsto_ρ : Tendsto ρ (𝓝[>] 0) (𝓝 1) := by
  have := continuous_ρ.tendsto 0
  rw [ρ_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

private theorem tendsto_q : Tendsto q (𝓝[>] 0) (𝓝 0) := by
  have := continuous_q.tendsto 0
  have h0 : q 0 = 0 := by simp [q, ρ_zero]
  rw [h0] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- The difference quotient of `Yhet` at `0`, as a continuous function of `(ρ, q)`. -/
private noncomputable def Φ (r w : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-3 * (r + 1) / (r * (r ^ 2 + r + 1)), -3 * (r + 1) * w / (r * (r ^ 2 + r + 1));
     3 * (r + 1) * w / (r * (r ^ 2 + r + 1)), 3 * (r ^ 2 - 1) * (r + 1) / (r * (r ^ 2 + r + 1))]

private theorem slope_eq' (r w : ℝ) (hr : 0 < r) (ht0 : r ^ 3 - 1 ≠ 0) :
    (r ^ 3 - 1)⁻¹ • (!![-3 * (r ^ 2 - 1) / r, -3 * (r ^ 2 - 1) * w / r;
      3 * (r ^ 2 - 1) * w / r, 3 * (r ^ 2 - 1) ^ 2 / r] : Matrix (Fin 2) (Fin 2) ℝ) = Φ r w := by
  have h1 : r * (r + 1) + 1 ≠ 0 := by positivity
  have h2 : r ≠ 0 := hr.ne'
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Φ]; field_simp; ring
  · simp [Φ]; field_simp; ring
  · simp [Φ]; field_simp; ring
  · simp [Φ]; field_simp; ring

private theorem slope_eq {t : ℝ} (ht : 0 < t) : t⁻¹ • Yhet t = Φ (ρ t) (q t) := by
  have ht' : ρ t ^ 3 - 1 = t := by rw [ρ_cube ht.le]; ring
  have := slope_eq' (ρ t) (q t) (ρ_pos ht.le) (by rw [ht']; exact ht.ne')
  rw [ht'] at this
  exact this

private theorem tendsto_fin2 {α : Type*} {l : Filter α} {a b c d : α → ℝ} {a₀ b₀ c₀ d₀ : ℝ}
    (ha : Tendsto a l (𝓝 a₀)) (hb : Tendsto b l (𝓝 b₀)) (hc : Tendsto c l (𝓝 c₀))
    (hd : Tendsto d l (𝓝 d₀)) :
    Tendsto (fun t => (!![a t, b t; c t, d t] : Matrix (Fin 2) (Fin 2) ℝ)) l
      (𝓝 !![a₀, b₀; c₀, d₀]) := by
  have e : (fun t => (!![a t, b t; c t, d t] : Matrix (Fin 2) (Fin 2) ℝ)) =
      fun t => a t • E₁₁ + b t • E₁₂ + c t • E₂₁ + d t • E₂₂ := funext fun t => fin2_eq_sum _ _ _ _
  rw [e, fin2_eq_sum]
  exact (((ha.smul_const _).add (hb.smul_const _)).add (hc.smul_const _)).add (hd.smul_const _)

private theorem tendsto_slope : Tendsto (fun t => t⁻¹ • Yhet t) (𝓝[>] 0) (𝓝 Zin) := by
  have hr := tendsto_ρ
  have hw := tendsto_q
  have hden : Tendsto (fun t => ρ t * (ρ t ^ 2 + ρ t + 1)) (𝓝[>] 0)
      (𝓝 (1 * (1 ^ 2 + 1 + 1))) :=
    hr.mul (((hr.pow 2).add hr).add tendsto_const_nhds)
  have hden0 : (1 : ℝ) * (1 ^ 2 + 1 + 1) ≠ 0 := by norm_num
  have hΦ : Tendsto (fun t => Φ (ρ t) (q t)) (𝓝[>] 0) (𝓝 (Φ 1 0)) := by
    unfold Φ
    refine tendsto_fin2 ?_ ?_ ?_ ?_
    · exact ((hr.add tendsto_const_nhds).const_mul (-3)).div hden hden0
    · exact (((hr.add tendsto_const_nhds).const_mul (-3)).mul hw).div hden hden0
    · exact (((hr.add tendsto_const_nhds).const_mul 3).mul hw).div hden hden0
    · exact ((((hr.pow 2).sub tendsto_const_nhds).const_mul 3).mul
        (hr.add tendsto_const_nhds)).div hden hden0
  have hΦ1 : Φ 1 0 = Zin := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [Φ, Zin]
  rw [← hΦ1]
  refine hΦ.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (slope_eq ht).symm

/-- **The heteroclinic continuation leaves `0` with the incoming velocity.**  The right
derivative of `Yhet` at the time of rank loss is `Zin = -2 E₁₁`, the velocity of the incoming
solution `t ↦ -2 t E₁₁`. -/
theorem Yhet_hasDerivWithinAt_zero : HasDerivWithinAt Yhet Zin (Ici 0) 0 := by
  have hset : Ici (0 : ℝ) \ {0} = Ioi 0 := by
    ext x; simp [lt_iff_le_and_ne, eq_comm]
  rw [hasDerivWithinAt_iff_tendsto_slope, hset]
  refine tendsto_slope.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t _
  rw [slope_def_module, Yhet_zero, sub_zero, sub_zero]

/-- The incoming solution glued to the heteroclinic continuation. -/
noncomputable def Yglue (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := if t ≤ 0 then t • Zin else Yhet t

/-- **A differentiable continuation through the rank drop that is not the linear one.**  The
glued curve `Yglue` (equal to `-2 t E₁₁` for `t ≤ 0` and to `Yhet` for `t ≥ 0`) is
differentiable at the rank-loss time `t = 0`, with the same derivative `-2 E₁₁` as the linear
continuation `t ↦ -2 t E₁₁`. -/
theorem Yglue_hasDerivAt_zero : HasDerivAt Yglue Zin 0 := by
  have hl : HasDerivWithinAt Yglue Zin (Iic 0) 0 := by
    have : HasDerivWithinAt (fun t : ℝ => t • Zin) Zin (Iic 0) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const Zin).hasDerivWithinAt
    exact this.congr (fun y hy => by simp [Yglue, mem_Iic.1 hy]) (by simp [Yglue])
  have hr : HasDerivWithinAt Yglue Zin (Ici 0) 0 := by
    refine Yhet_hasDerivWithinAt_zero.congr (fun y hy => ?_) (by simp [Yglue, Yhet_zero])
    simp only [Yglue]; split_ifs with h
    · have : y = 0 := le_antisymm h hy
      subst this; simp [Yhet_zero]
    · rfl
  have := hl.union hr
  rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this

/-- The glued curve is a rank-one Dirac–Frenkel solution for all `t ≠ 0`. -/
theorem Yglue_isDFSolution : IsDFSolution 1 G₀ Yglue {t | t ≠ 0} := by
  intro t ht
  rcases lt_or_gt_of_ne ht with h | h
  · obtain ⟨U, S, V, hU, hV, hS, hY, hd⟩ := incoming_isDFSolution t ht
    refine ⟨U, S, V, hU, hV, hS, by simpa [Yglue, h.le] using hY, ?_⟩
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds h] with y hy
    simp [Yglue, (mem_Iio.1 hy).le]
  · obtain ⟨U, S, V, hU, hV, hS, hY, hd⟩ := Yhet_isDFSolution t h
    refine ⟨U, S, V, hU, hV, hS, by simpa [Yglue, not_le.2 h] using hY, ?_⟩
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds h] with y hy
    simp [Yglue, not_le.2 (mem_Ioi.1 hy)]

/-- `Yhet` is not the linear continuation: at `t = 7` (`ρ = 2`) its `(2,2)` entry is `27/2`. -/
theorem Yhet_ne_line : Yhet ≠ fun t => t • Zin := by
  intro h
  have h7 : ρ 7 = 2 := by
    unfold ρ
    rw [show (1 : ℝ) + 7 = 2 ^ 3 by norm_num, show (1 : ℝ) / 3 = ((3 : ℕ) : ℝ)⁻¹ by norm_num,
      Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)]
  have := congrFun (congrFun (congrFun h 7) 1) 1
  simp [Yhet, Zin, h7] at this
  norm_num at this

/-! #### A one-parameter family of differentiable continuations -/

/-- The scaled continuations `Y_c(t) = c Yhet(t / c)`, `c > 0`. -/
noncomputable def Yfam (c t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := c • Yhet (t / c)

/-- Each `Yfam c` is a rank-one Dirac–Frenkel solution on `t > 0` (scaling symmetry). -/
theorem Yfam_isDFSolution {c : ℝ} (hc : 0 < c) : IsDFSolution 1 G₀ (Yfam c) (Ioi 0) := by
  have e : Yfam c = fun t => c • Yhet (0 + (t - 0) / c) := by funext t; simp [Yfam]
  rw [e]
  intro t ht
  exact Yhet_isDFSolution.scale hc.ne' 0 t (by simpa using div_pos ht hc)

/-- The incoming solution glued to `Yfam c`. -/
noncomputable def YglueFam (c t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := c • Yglue (t / c)

theorem Yglue_zero : Yglue 0 = 0 := by simp [Yglue]

/-- **A continuum of differentiable continuations.**  For every `c > 0` the glued curve
`Yglue_c` (equal to `-2 t E₁₁` for `t ≤ 0` and to `Yfam c` for `t ≥ 0`) is differentiable at the
rank-loss time with derivative `-2 E₁₁`, and it is a Dirac–Frenkel solution for all `t ≠ 0`. -/
theorem YglueFam_hasDerivAt_zero {c : ℝ} (hc : 0 < c) : HasDerivAt (YglueFam c) Zin 0 := by
  have h1 : HasDerivAt (fun t : ℝ => t / c) (1 / c) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).div_const c
  have h2 : HasDerivAt Yglue Zin ((fun t : ℝ => t / c) 0) := by simpa using Yglue_hasDerivAt_zero
  have := (h2.scomp (h := fun t : ℝ => t / c) 0 h1).const_smul c
  rw [smul_smul, mul_one_div_cancel hc.ne', one_smul] at this
  exact this

theorem YglueFam_isDFSolution {c : ℝ} (hc : 0 < c) :
    IsDFSolution 1 G₀ (YglueFam c) {t | t ≠ 0} := by
  have e : YglueFam c = fun t => c • Yglue (0 + (t - 0) / c) := by funext t; simp [YglueFam]
  rw [e]
  intro t ht
  exact Yglue_isDFSolution.scale hc.ne' 0 t (by simpa using div_ne_zero ht hc.ne')

theorem YglueFam_eq_incoming {c t : ℝ} (hc : 0 < c) (ht : t ≤ 0) : YglueFam c t = t • Zin := by
  have : t / c ≤ 0 := div_nonpos_of_nonpos_of_nonneg ht hc.le
  simp [YglueFam, Yglue, this, smul_smul, mul_div_cancel₀ _ hc.ne']

/-- The members of the family are pairwise distinct: `c ↦ Yfam c` is injective on `c > 0`
(the ratio of the `(2,2)` and `(1,1)` entries at `t = 1` is `-(ρ(1/c)² - 1)`, strictly monotone
in `c`). -/
theorem Yfam_injective {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') (h : Yfam c = Yfam c') : c = c' := by
  have ha : 0 < ρ (1 / c) := ρ_pos (by positivity)
  have hb : 0 < ρ (1 / c') := ρ_pos (by positivity)
  have hma : 0 < ρ (1 / c) ^ 2 - 1 := by have := one_lt_ρ (by positivity : 0 < 1 / c); nlinarith
  have hA := congrFun (congrFun (congrFun h 1) 0) 0
  have hB := congrFun (congrFun (congrFun h 1) 1) 1
  simp only [Yfam, Yhet, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    smul_eq_mul] at hA hB
  set a := ρ (1 / c) with hadef
  set b := ρ (1 / c') with hbdef
  set κ := c * (a ^ 2 - 1) / a with hκ
  set κ' := c' * (b ^ 2 - 1) / b with hκ'
  have hκpos : 0 < κ := by positivity
  have e1 : κ = κ' := by
    have : -3 * κ = -3 * κ' := by
      rw [hκ, hκ']; rw [show c * (-3 * (a ^ 2 - 1) / a) = -3 * (c * (a ^ 2 - 1) / a) by ring,
        show c' * (-3 * (b ^ 2 - 1) / b) = -3 * (c' * (b ^ 2 - 1) / b) by ring] at hA
      exact hA
    exact mul_left_cancel₀ (by norm_num) this
  have e2 : κ * (a ^ 2 - 1) = κ' * (b ^ 2 - 1) := by
    have : 3 * (κ * (a ^ 2 - 1)) = 3 * (κ' * (b ^ 2 - 1)) := by
      rw [hκ, hκ']; rw [show c * (3 * (a ^ 2 - 1) ^ 2 / a) = 3 * (c * (a ^ 2 - 1) / a * (a ^ 2 - 1))
        by ring, show c' * (3 * (b ^ 2 - 1) ^ 2 / b) = 3 * (c' * (b ^ 2 - 1) / b * (b ^ 2 - 1))
        by ring] at hB
      exact hB
    exact mul_left_cancel₀ (by norm_num) this
  rw [← e1] at e2
  have hab2 : a ^ 2 = b ^ 2 := by
    have := mul_left_cancel₀ hκpos.ne' e2
    linarith
  have hab : a = b := by
    have := (pow_left_inj₀ ha.le hb.le two_ne_zero).1 hab2
    exact this
  have hinj := Real.rpow_left_injOn (x := (1 : ℝ) / 3) (by norm_num)
  have h1 : (1 : ℝ) + 1 / c = 1 + 1 / c' := by
    apply hinj (by exact (by positivity : (0 : ℝ) ≤ 1 + 1 / c))
      (by exact (by positivity : (0 : ℝ) ≤ 1 + 1 / c'))
    change (1 + 1 / c) ^ ((1 : ℝ) / 3) = (1 + 1 / c') ^ ((1 : ℝ) / 3)
    exact hab
  have : 1 / c = 1 / c' := by linarith
  rwa [one_div, one_div, inv_inj] at this

end Example

/-! ### The BUG integrator through the rank drop -/

section BUG

variable {r : ℕ} {G : Matrix m n ℝ}

/-- `(range U, range V)` is an **invariant pair** of `G`: `G` maps `range V` into `range U` and
`Gᵀ` maps `range U` into `range V`.  For the self-similar solutions of `isDFSolution_line_iff`
this is exactly the block condition `(1 - U Uᵀ) G V Vᵀ = 0`, `U Uᵀ G (1 - V Vᵀ) = 0`. -/
def IsInvariantPair {k : Type*} [Fintype k] (G : Matrix m n ℝ) (U : Matrix m k ℝ)
    (V : Matrix n k ℝ) : Prop :=
  U * Uᵀ * (G * V) = G * V ∧ V * Vᵀ * (Gᵀ * U) = Gᵀ * U

/-- **One step of the BUG integrator for a constant field, in matrix form.**  From the factors
`(U, S, V)` of `Y₀ = U S Vᵀ`: K-step `K = U S + h G V`, L-step `L = V Sᵀ + h Gᵀ U` (for a constant
field the exact substep flows are these Euler steps), new orthonormal bases `U₁`, `V₁` that
capture `K` and `L` and lie in the spans of `(K, U)` and `(L, V)`.  Both the fixed-rank BUG
(Ceruti–Lubich, arXiv 2010.02022: `U₁` an orthonormal basis of `range K`) and the rank-adaptive
augmented BUG (Ceruti–Kusch–Lubich, arXiv 2104.05247: `U₁` an orthonormal basis of `range [K, U]`)
are instances; `k` is the number of columns of the new bases.  The new approximation is the
Galerkin step `galerkinStep`. -/
structure IsBUGStepMat (G : Matrix m n ℝ) (h : ℝ) (U : Matrix m (Fin r) ℝ)
    (S : Matrix (Fin r) (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) {k : Type*} [Fintype k]
    [DecidableEq k] (U₁ : Matrix m k ℝ) (V₁ : Matrix n k ℝ) : Prop where
  orthU : U₁ᵀ * U₁ = 1
  orthV : V₁ᵀ * V₁ = 1
  capK : U₁ * U₁ᵀ * (U * S + h • (G * V)) = U * S + h • (G * V)
  capL : V₁ * V₁ᵀ * (V * Sᵀ + h • (Gᵀ * U)) = V * Sᵀ + h • (Gᵀ * U)
  spanU : ∃ A B : Matrix (Fin r) k ℝ, U₁ = (U * S + h • (G * V)) * A + U * B
  spanV : ∃ A B : Matrix (Fin r) k ℝ, V₁ = (V * Sᵀ + h • (Gᵀ * U)) * A + V * B

/-- The Galerkin step `Ŷ₁ = U₁ (U₁ᵀ Y₀ V₁ + h U₁ᵀ G V₁) V₁ᵀ` in the new bases (exact for a constant
field). -/
def galerkinStep (G : Matrix m n ℝ) (h : ℝ) (Y₀ : Matrix m n ℝ) {k : Type*} [Fintype k]
    (U₁ : Matrix m k ℝ) (V₁ : Matrix n k ℝ) : Matrix m n ℝ :=
  U₁ * (U₁ᵀ * Y₀ * V₁ + h • (U₁ᵀ * G * V₁)) * V₁ᵀ

variable {U : Matrix m (Fin r) ℝ} {S : Matrix (Fin r) (Fin r) ℝ} {V : Matrix n (Fin r) ℝ}
  {k : Type*} [Fintype k] [DecidableEq k] {U₁ : Matrix m k ℝ} {V₁ : Matrix n k ℝ} {h : ℝ}

private theorem kStep_eq (hinv : IsInvariantPair G U V) :
    U * S + h • (G * V) = U * (S + h • (Uᵀ * G * V)) := by
  rw [Matrix.mul_add, Matrix.mul_smul]
  congr 2
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc, hinv.1]

private theorem lStep_eq (hinv : IsInvariantPair G U V) :
    V * Sᵀ + h • (Gᵀ * U) = V * (Sᵀ + h • (Vᵀ * Gᵀ * U)) := by
  rw [Matrix.mul_add, Matrix.mul_smul]
  congr 2
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc, hinv.2]

/-- **The BUG step cannot leave an invariant block.**  If `(range U, range V)` is an invariant
pair of `G` and the new bases capture the old ones (automatic for the augmented BUG; for the
fixed-rank BUG see `IsBUGStepMat.capU_of_isUnit`), then the new projectors equal the old ones, the
Galerkin step is exactly `Y₀ + h U Uᵀ G V Vᵀ = U (S + h Uᵀ G V) Vᵀ` — the exact value of the
linear Dirac–Frenkel solution — and the new bases again form an invariant pair.  No rank is
gained and the complementary block of `G` is never seen, whatever the singular values of `S`
(including `S = 0`). -/
theorem IsBUGStepMat.invariant (hs : IsBUGStepMat G h U S V U₁ V₁) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1)
    (hinv : IsInvariantPair G U V) (hcapU : U₁ * U₁ᵀ * U = U) (hcapV : V₁ * V₁ᵀ * V = V) :
    U₁ * U₁ᵀ = U * Uᵀ ∧ V₁ * V₁ᵀ = V * Vᵀ ∧
      galerkinStep G h (U * S * Vᵀ) U₁ V₁ = U * S * Vᵀ + h • (U * Uᵀ * G * (V * Vᵀ)) ∧
      IsInvariantPair G U₁ V₁ := by
  have hUU₁ : U * Uᵀ * U₁ = U₁ := by
    obtain ⟨A, B, hAB⟩ := hs.spanU
    rw [hAB, kStep_eq hinv]
    simp only [Matrix.mul_add, ← Matrix.mul_assoc]
    rw [Matrix.mul_assoc U Uᵀ U, hU, Matrix.mul_one]
  have hVV₁ : V * Vᵀ * V₁ = V₁ := by
    obtain ⟨A, B, hAB⟩ := hs.spanV
    rw [hAB, lStep_eq hinv]
    simp only [Matrix.mul_add, ← Matrix.mul_assoc]
    rw [Matrix.mul_assoc V Vᵀ V, hV, Matrix.mul_one]
  have e1 : U₁ * U₁ᵀ = U * Uᵀ := (mul_transpose_eq_of_capture_of_capture hcapU hUU₁).symm
  have e2 : V₁ * V₁ᵀ = V * Vᵀ := (mul_transpose_eq_of_capture_of_capture hcapV hVV₁).symm
  refine ⟨e1, e2, ?_, ?_, ?_⟩
  · unfold galerkinStep
    have h1 : U₁ * (U₁ᵀ * (U * S * Vᵀ) * V₁) * V₁ᵀ = U * S * Vᵀ := by
      calc U₁ * (U₁ᵀ * (U * S * Vᵀ) * V₁) * V₁ᵀ = U₁ * U₁ᵀ * (U * S * Vᵀ) * (V₁ * V₁ᵀ) := by
            simp only [Matrix.mul_assoc]
        _ = U * S * Vᵀ := by
            rw [e1, e2, Curvature.colProj_mul_factor hU, Curvature.factor_mul_rowProj hV]
    have h2 : U₁ * (U₁ᵀ * G * V₁) * V₁ᵀ = U * Uᵀ * G * (V * Vᵀ) := by
      calc U₁ * (U₁ᵀ * G * V₁) * V₁ᵀ = U₁ * U₁ᵀ * G * (V₁ * V₁ᵀ) := by simp only [Matrix.mul_assoc]
        _ = U * Uᵀ * G * (V * Vᵀ) := by rw [e1, e2]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, h1, h2]
  · -- `G V₁ = G V (Vᵀ V₁)`, and `U Uᵀ G V = G V`
    have hV₁ : V₁ = V * (Vᵀ * V₁) := by rw [← Matrix.mul_assoc, hVV₁]
    calc U₁ * U₁ᵀ * (G * V₁) = U * Uᵀ * (G * (V * (Vᵀ * V₁))) := by rw [e1, ← hV₁]
      _ = U * Uᵀ * (G * V) * (Vᵀ * V₁) := by simp only [Matrix.mul_assoc]
      _ = G * V * (Vᵀ * V₁) := by rw [hinv.1]
      _ = G * V₁ := by rw [Matrix.mul_assoc, ← hV₁]
  · have hU₁ : U₁ = U * (Uᵀ * U₁) := by rw [← Matrix.mul_assoc, hUU₁]
    calc V₁ * V₁ᵀ * (Gᵀ * U₁) = V * Vᵀ * (Gᵀ * (U * (Uᵀ * U₁))) := by rw [e2, ← hU₁]
      _ = V * Vᵀ * (Gᵀ * U) * (Uᵀ * U₁) := by simp only [Matrix.mul_assoc]
      _ = Gᵀ * U * (Uᵀ * U₁) := by rw [hinv.2]
      _ = Gᵀ * U₁ := by rw [Matrix.mul_assoc, ← hU₁]

/-- For the fixed-rank BUG (`k = Fin r`) the new basis captures the old one as soon as
`K = U (S + h Uᵀ G V)` has full rank, i.e. whenever the Galerkin core `S + h Uᵀ G V` is
invertible.  (When it is singular, `K = 0` and the fixed-rank step is not well defined: the
basis of the zero matrix is arbitrary.) -/
theorem IsBUGStepMat.capU_of_isUnit {U₁ : Matrix m (Fin r) ℝ} {V₁ : Matrix n (Fin r) ℝ}
    (hs : IsBUGStepMat G h U S V U₁ V₁) (hinv : IsInvariantPair G U V)
    (hdet : IsUnit (S + h • (Uᵀ * G * V)).det) :
    U₁ * U₁ᵀ * U = U ∧ V₁ * V₁ᵀ * V = V := by
  have hdetT : IsUnit (Sᵀ + h • (Vᵀ * Gᵀ * U)).det := by
    have : Sᵀ + h • (Vᵀ * Gᵀ * U) = (S + h • (Uᵀ * G * V))ᵀ := by
      simp [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [this, Matrix.det_transpose]; exact hdet
  constructor
  · have h1 := hs.capK
    rw [kStep_eq hinv, ← Matrix.mul_assoc] at h1
    set N := S + h • (Uᵀ * G * V) with hN
    calc U₁ * U₁ᵀ * U = U₁ * U₁ᵀ * U * (N * N⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = U * N * N⁻¹ := by rw [← Matrix.mul_assoc, h1]
      _ = U := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
  · have h1 := hs.capL
    rw [lStep_eq hinv, ← Matrix.mul_assoc] at h1
    set N := Sᵀ + h • (Vᵀ * Gᵀ * U) with hN
    calc V₁ * V₁ᵀ * V = V₁ * V₁ᵀ * V * (N * N⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hdetT, Matrix.mul_one]
      _ = V * N * N⁻¹ := by rw [← Matrix.mul_assoc, h1]
      _ = V := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdetT, Matrix.mul_one]

/-- **BUG trajectories on an invariant block are exact, through the rank drop.**  Let
`(Uₖ, Sₖ, Vₖ)` be a BUG trajectory with step `h` (each step an `IsBUGStepMat`, new core from the
Galerkin step) whose new bases capture the old ones, starting from an invariant pair.  Then
`Yₖ = Uₖ Sₖ Vₖᵀ = U₀ (S₀ + k h U₀ᵀ G V₀) V₀ᵀ` for every `k`: exactly the linear Dirac–Frenkel
solution `isDFSolution_line_iff` at `t = k h`, also after the core has become singular. -/
theorem bug_trajectory (U : ℕ → Matrix m (Fin r) ℝ) (S : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (V : ℕ → Matrix n (Fin r) ℝ) (hU0 : (U 0)ᵀ * U 0 = 1) (hV0 : (V 0)ᵀ * V 0 = 1)
    (hinv : IsInvariantPair G (U 0) (V 0))
    (hstep : ∀ j, IsBUGStepMat G h (U j) (S j) (V j) (U (j + 1)) (V (j + 1)))
    (hcap : ∀ j, U (j + 1) * (U (j + 1))ᵀ * U j = U j ∧ V (j + 1) * (V (j + 1))ᵀ * V j = V j)
    (hS : ∀ j, U (j + 1) * S (j + 1) * (V (j + 1))ᵀ =
      galerkinStep G h (U j * S j * (V j)ᵀ) (U (j + 1)) (V (j + 1))) (k : ℕ) :
    U k * S k * (V k)ᵀ = U 0 * (S 0 + (k : ℝ) • (h • ((U 0)ᵀ * G * V 0))) * (V 0)ᵀ := by
  -- the induction carries the projectors, the invariant pair and the orthonormality
  have key : ∀ j, (U j)ᵀ * U j = 1 ∧ (V j)ᵀ * V j = 1 ∧ U j * (U j)ᵀ = U 0 * (U 0)ᵀ ∧
      V j * (V j)ᵀ = V 0 * (V 0)ᵀ ∧ IsInvariantPair G (U j) (V j) ∧
      U j * S j * (V j)ᵀ =
        U 0 * S 0 * (V 0)ᵀ + (j : ℝ) • (h • (U 0 * (U 0)ᵀ * G * (V 0 * (V 0)ᵀ))) := by
    intro j
    induction j with
    | zero => exact ⟨hU0, hV0, rfl, rfl, hinv, by simp⟩
    | succ j ih =>
      obtain ⟨hUj, hVj, hPj, hQj, hinvj, hYj⟩ := ih
      obtain ⟨e1, e2, hgal, hinv'⟩ := (hstep j).invariant hUj hVj hinvj (hcap j).1 (hcap j).2
      refine ⟨(hstep j).orthU, (hstep j).orthV, e1.trans hPj, e2.trans hQj, hinv', ?_⟩
      rw [hS j, hgal, hYj, hPj, hQj]
      push_cast
      rw [add_smul, one_smul, add_assoc]
  obtain ⟨-, -, -, -, -, hY⟩ := key k
  rw [hY, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.smul_mul]
  congr 3
  simp only [Matrix.mul_assoc]

/-- **The BUG integrator selects the linear continuation, exactly, for every step size.**  For
the example `G₀`, any BUG trajectory (fixed-rank or augmented, exact substeps) with step `h`
starting from the factors `(e₁, [2], e₁)` of `Y(-1) = 2 E₁₁`, whose new bases capture the old
ones, satisfies `Yₖ = (-1 + k h) Zin = -2 (-1 + k h) E₁₁`: the exact value of the linear
Dirac–Frenkel solution at `tₖ = -1 + k h`, before, at and after the rank drop at `t = 0`.  The
capture hypothesis holds by construction for the augmented (rank-adaptive) BUG, and for the
fixed-rank BUG whenever `K ≠ 0`, i.e. `(k + 1) h ≠ 1` (`IsBUGStepMat.capU_of_isUnit`).  Hence the
`h → 0` limit of the BUG integrator is the linear continuation `t ↦ -2 t E₁₁`, with zero error,
and the integrator never sees the heteroclinic continuations `Yfam` nor the second block
`t ↦ 3 t E₂₂`: the basis update cannot leave the invariant block `span e₁`. -/
theorem bug_example (h : ℝ) (U : ℕ → Matrix (Fin 2) (Fin 1) ℝ) (S : ℕ → Matrix (Fin 1) (Fin 1) ℝ)
    (V : ℕ → Matrix (Fin 2) (Fin 1) ℝ) (hU0 : U 0 = e₁) (hS0 : S 0 = !![2]) (hV0 : V 0 = e₁)
    (hstep : ∀ j, IsBUGStepMat G₀ h (U j) (S j) (V j) (U (j + 1)) (V (j + 1)))
    (hcap : ∀ j, U (j + 1) * (U (j + 1))ᵀ * U j = U j ∧ V (j + 1) * (V (j + 1))ᵀ * V j = V j)
    (hS : ∀ j, U (j + 1) * S (j + 1) * (V (j + 1))ᵀ =
      galerkinStep G₀ h (U j * S j * (V j)ᵀ) (U (j + 1)) (V (j + 1))) (k : ℕ) :
    U k * S k * (V k)ᵀ = (-1 + k * h) • Zin := by
  have hinv : IsInvariantPair G₀ e₁ e₁ := by
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [e₁, G₀, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct,
            Function.swap, Matrix.vecHead, Matrix.vecTail]
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [e₁, G₀, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct,
            Function.swap, Matrix.vecHead, Matrix.vecTail]
  have hM : e₁ᵀ * G₀ * e₁ = !![-2] := by
    ext i j
    fin_cases i; fin_cases j
    simp [e₁, G₀, Matrix.mul_apply, Fin.sum_univ_two]
  rw [bug_trajectory U S V (by rw [hU0]; exact e₁_orth) (by rw [hV0]; exact e₁_orth)
    (by rw [hU0, hV0]; exact hinv) hstep hcap hS k, hU0, hS0, hV0, hM]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e₁, Zin, Matrix.mul_apply]
  ring

end BUG

end LeanDLRA.Novel.OpRA46
