import LeanDLRA.Foundations.OneSided
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.Curvature
import LeanDLRA.LinearAlgebra.Projection.Defs
import LeanDLRA.FixedRank.Defs
import LeanDLRA.Analysis.Defs

/-!
# Oblique (interpolatory / sketched) projectors in dynamical low-rank approximation

Interpolatory DLRA (DLRA-DEIM, Carrel–Kressner–Nobile–Vandereycken, *Interpolatory dynamical
low-rank approximation: theoretical foundations and algorithms*, arXiv 2510.19518) and sketched
DLRA (Carrel–Grigori, *Sketch low-rank dynamics: orthogonal vs. oblique projections*,
arXiv 2607.03402) replace the orthogonal projector `U Uᵀ` onto the column space of an orthonormal
basis `U ∈ ℝ^{m × r}` by the **oblique projector**

    𝒫 = U (Sᵀ U)⁻¹ Sᵀ ,

where `S ∈ ℝ^{m × r}` is a selection matrix (DEIM: `𝒫 x` interpolates `x` at the selected
rows) or a sketch (`S = Θᵀ Θ U` for a sketching matrix `Θ ∈ ℝ^{ℓ × m}`), and the orthogonal
tangent-space projector `P(Y) Z = U Uᵀ Z + Z V Vᵀ - U Uᵀ Z V Vᵀ` by the oblique tangent-space
projector `P^∠(Y) Z = 𝒫_U Z + Z 𝒫_Vᵀ - 𝒫_U Z 𝒫_Vᵀ` (arXiv 2510.19518, eqs. (12)–(13)).

`IsObliqueProj`, `obliqueProj`, `leftOblique` and `rightOblique` are defined in
`LeanDLRA/LinearAlgebra/Projection/Defs.lean`, and `obliqueTangentProj`, `sketchTangentProj` in
`LeanDLRA/FixedRank/Defs.lean`.

## Abstract theory (any real inner product space)

`IsObliqueProj P Q` says that the continuous linear map `P` is an oblique projector onto the
range of the orthogonal projector `Q`: `P Q = Q` and `Q P = P`.  We prove

* `IsObliqueProj.idem`: `P` is idempotent; `sub_apply_eq`: `(I - P) = (I - P)(I - Q)`
  (arXiv 2510.19518, eq. (14));
* `norm_sub_sq`: `‖x - P x‖² = ‖x - Q x‖² + ‖P (x - Q x)‖²`;
* `norm_sub_le_opNorm` (**DEIM error bound**, Chaturantabut–Sorensen; arXiv 2510.19518,
  eq. (6)): `‖x - P x‖ ≤ ‖P‖ ‖x - Q x‖` for `Q ≠ 0`, together with the quasi-optimality
  `‖x - P x‖ ≤ ‖P‖ ‖x - y‖` for every `y` in the range of `Q`;
* `opNorm_one_sub_eq` (**Szyld's identity** in this setting): `‖I - P‖ = ‖P‖` if `0 ≠ Q ≠ I`
  (used in the proof of Lemma 4 of arXiv 2510.19518);
* `IsObliqueProj.tangent`: if `P_L`, `P_R` are oblique projectors onto commuting orthogonal
  projectors `Q_L`, `Q_R`, and the cross-commutations `P_L Q_R = Q_R P_L`, `P_R Q_L = Q_L P_R`
  hold (`P_L` and `P_R` need not commute), then `tangent P_L P_R = P_L + P_R - P_L P_R` is an
  oblique projector onto the orthogonal tangent projector `tangent Q_L Q_R` (the matrix case is
  arXiv 2510.19518, §3.1; this is the two-factor analogue of its Tucker Lemma 15, which is not
  covered);
* `norm_sub_tangent_le_opNorm` (**Lemma 4** of arXiv 2510.19518):
  `‖x - P^∠ x‖ ≤ ‖P_L‖ ‖P_R‖ ‖x - P x‖`; `opNorm_tangent_le`: `‖P^∠‖ ≤ ‖P_L‖ ‖P_R‖`
  (unconditionally, for `Q_L, Q_R ≠ 0`); `opNorm_one_sub_tangent_eq`: `‖I - P^∠‖ = ‖P^∠‖` when
  the tangent projector satisfies `0 ≠ P ≠ I`;
* `IsObliqueProj.mul`, `norm_sub_mul_le`: the two-sided interpolatory (cross) projector
  `P_L P_R` is an oblique projector onto `Q_L Q_R` and
  `‖x - P_L P_R x‖ ≤ ‖P_L‖ ‖x - Q_L x‖ + ‖P_L‖ ‖P_R‖ ‖x - Q_R x‖` (an elementary triangle
  inequality; not the Sorensen–Embree DEIM-CUR factorisation, see below);
* `norm_sub_le_of_mem_filippov` (**Corollary 9**): every element of the Filippov regularisation
  `⋂_{δ>0} conv f(B(Y,δ) ∩ ℳ)` of a field `f` with `‖f - F‖ ≤ c` on `ℳ` is `c`-close to `F(Y)`,
  if `F` is continuous;
* `norm_sub_le_of_filippov`, `norm_sub_le_of_oblique` (**Theorem 10**: error bound of
  DLRA-DEIM): with a one-sided Lipschitz field `F` (constant `ℓ`), oblique projectors of norm
  `≤ C` and a normal component `≤ ε`,
  `‖Y(t) - A(t)‖ ≤ e^{ℓ(t-a)} ‖Y(a) - A(a)‖ + C ε ∫ₐᵗ e^{ℓ(t-s)} ds`;
* `mem_filippov_of_mem_range`, `ODESolution.oblique_of_mem_range` (**Lemma 7**, existence part
  only, with tangency of the velocity as a hypothesis): a solution of the full model whose
  velocity is tangent solves DLRA-DEIM;
* `norm_projEulerDEIM_sub_le` (**Lemma 11**) and `norm_projEulerDEIM_sub_le_global`
  (**Theorem 12**): local and global error of the projected Euler-DEIM method
  `Y_{n+1} = T(Y_n + h P^∠_n F(Y_n))` with a quasi-best approximation `T` onto `ℳ`:
  `‖Y_n - A(t_n)‖ ≤ e^{L T_f} (δ + T_f (κ g + (1 + κ)(L B h + C ε)))`, where `h g` bounds the
  distance of the exact one-step flow to `ℳ`; `norm_projEulerDEIM_sub_le_global_of_dlra`
  discharges this with `g = ε_d e^{L h}` from DLRA trajectories on `ℳ` with defect `ε_d`;
* `IsObliqueProj.eq_iff_of_sketch` (the deterministic core of **Proposition 4.4** of
  arXiv 2607.03402): if a sketch `σ` maps the oblique projector to an orthogonal one
  (`σ ∘ P^∠ = P̂ ∘ σ`) and does not annihilate the single tangent vector
  `δ = P^∠ z - P z` (the `Z` of Prop. 4.4), then `P^∠ z = P z` iff the sketched normal
  component `σ (z - P z)` is orthogonal to the sketched tangent space (condition (14));
* `IsObliqueProj.norm_sub_le_of_sketch`, `norm_sub_le_of_obliqueSketch` (a quantitative form of
  eq. (15), in the spirit of Remark 4.6 of arXiv 2607.03402, which does not pursue it): if the
  sketch embeds `δ = P^∠ z - P z` from below, `(1 - ε) ‖δ‖ ≤ ‖σ δ‖`, and the oblique residual
  at `δ` is small, `|⟪σ (z - P z), σ δ⟫| ≤ η ‖z - P z‖ ‖δ‖`, then
  `‖P^∠ z - P z‖ ≤ η / (1 - ε)² ‖z - P z‖`, and the oblique sketch DLRA satisfies the DLRA
  error bound with `ε_r` replaced by `(1 + η / (1 - ε)²) ε_r`.  Both hypotheses are imposed
  only at the realized, sketch-dependent `δ`, deterministically, as in Prop. 4.4 (see the
  docstrings for why Corollary 2.3 does not provide them directly).

## Matrices (Frobenius norm, spectral norm `specNorm`)

* `obliqueProj U S = U (Sᵀ U)⁻¹ Sᵀ`: idempotent, `𝒫 U = U`, interpolation property
  `Sᵀ 𝒫 = Sᵀ`, uniqueness (`eq_obliqueProj_mul`), `(I - 𝒫)(I - U Uᵀ) = I - 𝒫`;
  it only depends on the ranges of `U` and `S` (`obliqueProj_mul_right`,
  `obliqueProj_mul_right'`); for `S = U` it is the orthogonal projector `U (UᵀU)⁻¹ Uᵀ`, equal to
  `U₀ U₀ᵀ` for any orthonormal basis `U₀` of the range (`obliqueProj_self_mul_right`:
  orthogonal sketch DLRA is DLRA, arXiv 2607.03402, eqs. (7)–(8); the projector `Π_Ω` of
  arXiv 2410.17091, eq. (7));
* `norm_sub_obliqueProj_mul_le_of_orthonormal`: `‖X - 𝒫 X‖_F ≤ ‖(Sᵀ U)⁻¹‖₂ ‖X - U Uᵀ X‖_F`
  for a selection (orthonormal) `S` (arXiv 2510.19518, eq. (6)); for general `S`,
  `‖X - 𝒫 X‖_F ≤ ‖(Sᵀ U)⁻¹‖₂ ‖S‖₂ ‖X - U Uᵀ X‖_F` and the purely Frobenius bound
  `‖(I - 𝒫) X‖_F ≤ (1 + ‖U‖_F ‖(SᵀU)⁻¹‖_F ‖S‖_F) ‖(I - U Uᵀ) X‖_F`;
* `obliqueTangentProj`: the oblique tangent projector `P^∠(Y)`; it is an oblique projector onto
  `P(Y)`, has the interpolation property `S_Uᵀ P^∠(Y)[Z] S_V = S_Uᵀ Z S_V`, and satisfies
  **Lemma 4** of arXiv 2510.19518:
  `‖Z - P^∠(Y) Z‖_F ≤ ‖(S_Uᵀ U)⁻¹‖₂ ‖(S_Vᵀ V)⁻¹‖₂ ‖Z - P(Y) Z‖_F`,
  `‖P^∠(Y)‖ ≤ ‖(S_Uᵀ U)⁻¹‖₂ ‖(S_Vᵀ V)⁻¹‖₂` and `‖I - P^∠(Y)‖ = ‖P^∠(Y)‖` (if `P(Y) ≠ I`);
  `norm_sub_obliqueTangentProj_le_of_normal`: the interpolatory projected field is
  `C_{m,r} C_{n,r} ε`-close to `F` (the constant of Corollary 9 / Lemma 11);
* two-sided interpolatory (cross) projection `X ↦ 𝒫_U X 𝒫_Vᵀ
  = U (S_UᵀU)⁻¹ (S_Uᵀ X S_V) (VᵀS_V)⁻¹ Vᵀ`: interpolation on the selected cross and
  `‖X - 𝒫_U X 𝒫_Vᵀ‖_F ≤ C_U ‖X - U Uᵀ X‖_F + C_U C_V ‖X - X V Vᵀ‖_F`.  It is built from the
  bases `U`, `V` and the selected cross of `X`; it is *not* the DEIM-CUR factorisation `C U R`
  of Sorensen–Embree, whose factors `C`, `R` are actual columns and rows of `X`;
* sketching (arXiv 2607.03402, Lemma 4.2): for sketch-orthonormal `P` (`(ΘP)ᵀ(ΘP) = I`),
  `P (ΘP)⁺ Θ = P Pᵀ Θᵀ Θ = obliqueProj P (Θᵀ Θ P)`, the sketch maps it to the orthogonal
  projector of the sketched basis (`Θ 𝒫 = (ΘP)(ΘP)ᵀ Θ`), and the two-sided oblique sketch
  projector is, in sketch coordinates, the orthogonal tangent projector at `Θ Y Ωᵀ`;
  `obliqueProj_mul_eq_iff`: `𝒫 X = U Uᵀ X` iff `Sᵀ (I - U Uᵀ) X = 0`;
* `isObliqueProj_sketchTangentProj`, `sketchTangentProj_eq_iff`
  (**Proposition 4.4**, matrix form) and `norm_sketchTangentProj_sub_le` (eq. (15),
  matrix form): the abstract sketch results instantiated with `σ Z = Θ Z Ωᵀ`,
  `P̂ = P_{ΘYΩᵀ}` and sketch-orthonormal bases `P = U R`, `W = V R'`; the examples at the end
  of the file show that their hypotheses hold for a genuinely compressive sketch (`ℓ = 1 < 2`)
  with a genuinely oblique projector.

## Deviations from the papers

* Lemma 4 / eq. (6) are proved with the spectral norm `specNorm` of `U (SᵀU)⁻¹ Sᵀ`, which is
  bounded by `‖(SᵀU)⁻¹‖₂ ‖S‖₂`; for selection matrices (`SᵀS = I`) this is the paper's
  `‖(SᵀU)⁻¹‖₂`.  The abstract versions use the operator norm induced by the Frobenius norm,
  exactly as in arXiv 2510.19518, eq. (15).
* Theorem 12 assumes, in addition to the paper's Assumptions 1–3, a bound `‖F‖ ≤ B` along the
  exact one-step flows (Assumption 4, localised) to make Euler's local error `L B h²` explicit,
  and `norm_projEulerDEIM_sub_le_global` takes as a hypothesis that the exact flow from `Y_n` is
  `h g`-close to `ℳ` after one step.  This is the central analytic step of Kieri–Vandereycken
  (their Lemma 3, used in the paper's Lemma 11); `norm_projEulerDEIM_sub_le_global_of_dlra`
  discharges it, with `g = ε_d e^{L h}`, from a DLRA trajectory starting at `Y_n` that is on `ℳ`
  at `t_{n+1}` and has defect `≤ ε_d` (by `ODESolution.norm_sub_le_of_perturbed_max`); the
  existence of such trajectories (the paper's standing assumption that the DLRA solution stays
  on `ℳ` for one step) remains a hypothesis.  The truncation `T` enters only through the
  quasi-best approximation property `‖T x - x‖ ≤ κ ‖z - x‖` for `z ∈ ℳ` (`κ = 1` for `T_r`);
  `T x ∈ ℳ` is not needed for the error bound and is not assumed.
* Theorem 10 is stated for trajectories with right derivatives in the Filippov set at every
  time of `[a, b)` (the ODE framework of `LeanDLRA.Foundations.ODE`), rather than for absolutely
  continuous solutions satisfying the inclusion almost everywhere.  This is a genuine
  restriction: absolutely continuous solutions whose derivative leaves the Filippov set (or
  fails to exist) on a null set of times are not covered.  The set `filippov` itself coincides
  with eq. (16) of arXiv 2510.19518 (closed convex hull; open versus closed balls are
  immaterial in the intersection over `δ > 0`).
* The results on oblique *sketched* projectors (arXiv 2607.03402) are deterministic: the
  embedding hypotheses are imposed on the realized sketch and only at the specific,
  sketch-dependent tangent vector `δ = P^∠ z - P z`, as in Proposition 4.4 and Remark 4.5.
  Uniform hypotheses over the whole tangent space would be vacuous for compressive sketches
  (`σ Z = Θ Z Ωᵀ` kills `a Vᵀ` for `Θ a = 0`).
-/

open Set Metric
open scoped RealInnerProductSpace

namespace LeanDLRA

/-! ## Abstract oblique projectors -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An orthogonal projector is an oblique projector onto itself. -/
lemma IsOrthProj.isObliqueProj {Q : E →L[ℝ] E} (hQ : IsOrthProj Q) : IsObliqueProj Q Q where
  orth := hQ
  fix x := hQ.idem x
  range x := hQ.idem x

namespace IsObliqueProj

variable {P Q : E →L[ℝ] E}

/-- An oblique projector is idempotent. -/
lemma idem (h : IsObliqueProj P Q) (x : E) : P (P x) = P x := by
  calc P (P x) = P (Q (P x)) := by rw [h.range]
    _ = Q (P x) := h.fix _
    _ = P x := h.range x

lemma idem' (h : IsObliqueProj P Q) : P * P = P := by
  ext x; exact h.idem x

lemma map_sub_proj (h : IsObliqueProj P Q) (x : E) : P (x - Q x) = P x - Q x := by
  rw [map_sub, h.fix]

/-- `(I - P) = (I - P) (I - Q)` (arXiv 2510.19518, eq. (14)). -/
lemma sub_apply_eq (h : IsObliqueProj P Q) (x : E) :
    x - P x = (x - Q x) - P (x - Q x) := by
  rw [h.map_sub_proj]; abel

lemma proj_sub_self (h : IsObliqueProj P Q) (x : E) : Q (x - Q x) = 0 := by
  rw [map_sub, h.orth.idem, sub_self]

lemma inner_sub_proj_apply (h : IsObliqueProj P Q) (x y : E) : ⟪x - Q x, P y⟫ = 0 := by
  rw [← h.range y, real_inner_comm, h.orth.inner_sub_self]

/-- Pythagoras for an oblique projector: `‖x - P x‖² = ‖x - Q x‖² + ‖P (x - Q x)‖²`. -/
lemma norm_sub_sq (h : IsObliqueProj P Q) (x : E) :
    ‖x - P x‖ ^ 2 = ‖x - Q x‖ ^ 2 + ‖P (x - Q x)‖ ^ 2 := by
  rw [h.sub_apply_eq, norm_sub_sq_real, h.inner_sub_proj_apply]; ring

/-- `‖x - P x‖ ≤ ‖I - P‖ ‖x - Q x‖`. -/
lemma norm_sub_le_opNorm_one_sub (h : IsObliqueProj P Q) (x : E) :
    ‖x - P x‖ ≤ ‖1 - P‖ * ‖x - Q x‖ := by
  rw [h.sub_apply_eq]
  exact (1 - P).le_opNorm (x - Q x)

/-- The elementary bound `‖x - P x‖ ≤ (1 + ‖P‖) ‖x - Q x‖`, valid without any condition on
`Q`. -/
lemma norm_sub_le_one_add (h : IsObliqueProj P Q) (x : E) :
    ‖x - P x‖ ≤ (1 + ‖P‖) * ‖x - Q x‖ := by
  rw [h.sub_apply_eq, add_mul, one_mul]
  exact (norm_sub_le _ _).trans (add_le_add le_rfl (P.le_opNorm _))

/-- A nonzero oblique projector has norm at least one. -/
lemma one_le_opNorm (h : IsObliqueProj P Q) (hQ : Q ≠ 0) : 1 ≤ ‖P‖ := by
  obtain ⟨y, hy⟩ : ∃ y, Q y ≠ 0 := by
    by_contra hc
    exact hQ (ContinuousLinearMap.ext fun y => by
      change Q y = 0; by_contra hy; exact hc ⟨y, hy⟩)
  have h1 : ‖Q y‖ ≤ ‖P‖ * ‖Q y‖ := by
    calc ‖Q y‖ = ‖P (Q y)‖ := by rw [h.fix]
      _ ≤ ‖P‖ * ‖Q y‖ := P.le_opNorm _
  have h2 : 0 < ‖Q y‖ := norm_pos_iff.2 hy
  nlinarith

/-- **DEIM error bound** (Chaturantabut–Sorensen; arXiv 2510.19518, eq. (6)): an oblique
projector onto the range of a nonzero orthogonal projector `Q` is quasi-optimal,
`‖x - P x‖ ≤ ‖P‖ ‖x - Q x‖`.

The proof evaluates `P` on the test vector `ν b + β P b`, where `b = x - Q x`, `β = ‖b‖²` and
`ν = ‖P b‖²`, which gives `β + ν ≤ ‖P‖² β`. -/
theorem norm_sub_le_opNorm (h : IsObliqueProj P Q) (hQ : Q ≠ 0) (x : E) :
    ‖x - P x‖ ≤ ‖P‖ * ‖x - Q x‖ := by
  set b := x - Q x with hb
  set c := P b with hc
  have hbc : ⟪b, c⟫ = 0 := h.inner_sub_proj_apply x b
  have hPc : P c = c := h.idem b
  have hsq := h.norm_sub_sq x
  rw [← hb, ← hc] at hsq
  have hP1 := h.one_le_opNorm hQ
  set β := ‖b‖ ^ 2
  set ν := ‖c‖ ^ 2
  have hβ : 0 ≤ β := by positivity
  have hν : 0 ≤ ν := by positivity
  have key : β + ν ≤ ‖P‖ ^ 2 * β := by
    rcases hν.eq_or_lt with hν0 | hνpos
    · rw [← hν0, add_zero]
      have : 1 ≤ ‖P‖ ^ 2 := one_le_pow₀ hP1
      nlinarith
    · set y := ν • b + β • c with hy
      have hPy : P y = (ν + β) • c := by
        rw [hy, map_add, map_smul, map_smul, hPc, ← hc, add_smul]
      have hny : ‖y‖ ^ 2 = ν ^ 2 * β + β ^ 2 * ν := by
        rw [hy, norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right, hbc,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hν, abs_of_nonneg hβ]
        simp only [conj_trivial, mul_zero, add_zero]
        ring
      have hnPy : ‖P y‖ ^ 2 = (ν + β) ^ 2 * ν := by
        rw [hPy, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_pow]
      have hle : ‖P y‖ ^ 2 ≤ ‖P‖ ^ 2 * ‖y‖ ^ 2 := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (P.le_opNorm y) 2
      rw [hnPy, hny] at hle
      by_contra hcon
      push Not at hcon
      have : (ν + β) * (ν * (ν + β)) > ‖P‖ ^ 2 * β * (ν * (ν + β)) :=
        mul_lt_mul_of_pos_right (by linarith) (by positivity)
      nlinarith
  have hfin : ‖x - P x‖ ^ 2 ≤ (‖P‖ * ‖b‖) ^ 2 := by
    rw [hsq, mul_pow]; linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hfin

/-- **Quasi-optimality** of oblique projections: `‖x - P x‖ ≤ ‖P‖ ‖x - y‖` for every `y` in the
range of `Q` (the best approximation error is attained by `Q x`). -/
theorem norm_sub_le_opNorm_mul_norm_sub (h : IsObliqueProj P Q) (hQ : Q ≠ 0) (x y : E)
    (hy : Q y = y) : ‖x - P x‖ ≤ ‖P‖ * ‖x - y‖ :=
  (h.norm_sub_le_opNorm hQ x).trans
    (mul_le_mul_of_nonneg_left (h.orth.norm_sub_le_of_mem_range x y hy) (norm_nonneg _))

/-- Error of the oblique projection of a vector with small normal component: if
`‖x - Q x‖ ≤ ε` and `‖P‖ ≤ C`, then `‖x - P x‖ ≤ C ε` (arXiv 2510.19518, proof of
Corollary 9 and of Lemma 11). -/
theorem norm_sub_le_of_normal (h : IsObliqueProj P Q) (hQ : Q ≠ 0) {x : E} {C ε : ℝ}
    (hx : ‖x - Q x‖ ≤ ε) (hC : ‖P‖ ≤ C) : ‖x - P x‖ ≤ C * ε :=
  (h.norm_sub_le_opNorm hQ x).trans
    (mul_le_mul hC hx (norm_nonneg _) ((norm_nonneg _).trans hC))

/-- `‖I - P‖ ≤ ‖P‖` for an oblique projector onto a nonzero orthogonal projector. -/
theorem opNorm_one_sub_le (h : IsObliqueProj P Q) (hQ : Q ≠ 0) : ‖1 - P‖ ≤ ‖P‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => by
    calc ‖(1 - P) x‖ = ‖x - P x‖ := rfl
      _ ≤ ‖P‖ * ‖x - Q x‖ := h.norm_sub_le_opNorm hQ x
      _ ≤ ‖P‖ * ‖x‖ := mul_le_mul_of_nonneg_left (h.orth.norm_sub_le x) (norm_nonneg _)

/-- `‖P‖ ≤ ‖I - P‖` for an oblique projector onto an orthogonal projector `Q ≠ I`. -/
theorem opNorm_le_opNorm_one_sub (h : IsObliqueProj P Q) (hQ : Q ≠ 1) : ‖P‖ ≤ ‖1 - P‖ := by
  set c := ‖1 - P‖ with hcdef
  have hc0 : 0 ≤ c := norm_nonneg _
  have hker : ∀ b, Q b = 0 → ‖b‖ ^ 2 + ‖P b‖ ^ 2 ≤ c ^ 2 * ‖b‖ ^ 2 := by
    intro b hb
    have h1 := h.norm_sub_sq b
    rw [hb, sub_zero] at h1
    have h2 : ‖b - P b‖ ≤ c * ‖b‖ := (1 - P).le_opNorm b
    have h3 : ‖b - P b‖ ^ 2 ≤ (c * ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    rw [h1, mul_pow] at h3
    linarith
  have hc1 : 1 ≤ c ^ 2 := by
    obtain ⟨y, hy⟩ : ∃ y, Q y ≠ y := by
      by_contra hcon
      exact hQ (ContinuousLinearMap.ext fun y => by
        change Q y = y; by_contra hy; exact hcon ⟨y, hy⟩)
    have hb : Q (y - Q y) = 0 := h.proj_sub_self y
    have hbpos : 0 < ‖y - Q y‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hy))
    have := hker _ hb
    have : 0 < ‖y - Q y‖ ^ 2 := by positivity
    nlinarith [sq_nonneg ‖P (y - Q y)‖]
  refine ContinuousLinearMap.opNorm_le_bound _ hc0 fun x => ?_
  have hb : Q (x - Q x) = 0 := h.proj_sub_self x
  have hPx : P x = Q x + P (x - Q x) := by rw [h.map_sub_proj]; abel
  have hx : ‖x‖ ^ 2 = ‖Q x‖ ^ 2 + ‖x - Q x‖ ^ 2 := (h.orth.norm_sq_add x).symm
  have hkb := hker _ hb
  have htri : ‖P x‖ ≤ ‖Q x‖ + ‖P (x - Q x)‖ := by rw [hPx]; exact norm_add_le _ _
  set α := ‖Q x‖
  set p := ‖P (x - Q x)‖
  set β := ‖x - Q x‖
  have hp0 : 0 ≤ p := norm_nonneg _
  have key : (α + p) ^ 2 ≤ c ^ 2 * (α ^ 2 + β ^ 2) := by
    have hp : p ^ 2 ≤ (c ^ 2 - 1) * β ^ 2 := by linarith
    rcases (sub_nonneg.2 hc1).eq_or_lt with hd0 | hdpos
    · have hp2 : p ^ 2 ≤ 0 := by rw [← hd0] at hp; linarith
      have : p = 0 := by nlinarith
      rw [this]; nlinarith
    · have h2 : 2 * α * p * (c ^ 2 - 1) ≤ ((c ^ 2 - 1) * α ^ 2 + β ^ 2) * (c ^ 2 - 1) := by
        nlinarith [sq_nonneg ((c ^ 2 - 1) * α - p)]
      have h3 : 2 * α * p ≤ (c ^ 2 - 1) * α ^ 2 + β ^ 2 := le_of_mul_le_mul_right h2 hdpos
      nlinarith
  have : ‖P x‖ ^ 2 ≤ (c * ‖x‖) ^ 2 := by
    rw [mul_pow, hx]
    calc ‖P x‖ ^ 2 ≤ (α + p) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) htri 2
      _ ≤ _ := key
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 this

/-- **Szyld's identity** for oblique projectors: `‖I - P‖ = ‖P‖` whenever `0 ≠ Q ≠ I`
(used in the proof of Lemma 4 of arXiv 2510.19518: `‖I - P_U^∠‖₂ = ‖P_U^∠‖₂`). -/
theorem opNorm_one_sub_eq (h : IsObliqueProj P Q) (hQ0 : Q ≠ 0) (hQ1 : Q ≠ 1) :
    ‖1 - P‖ = ‖P‖ :=
  le_antisymm (h.opNorm_one_sub_le hQ0) (h.opNorm_le_opNorm_one_sub hQ1)

/-! ### Two-sided (tangent-space) oblique projectors -/

section Tangent

variable {PL PR QL QR : E →L[ℝ] E}

/-- The key identity behind Lemma 4 of arXiv 2510.19518: `(I - P_L)(I - P_R)(I - Q_L)(I - Q_R)
= (I - P_L)(I - P_R)` when the right oblique projector commutes with the left orthogonal one. -/
lemma normal_normal (hL : IsObliqueProj PL QL) (hR : IsObliqueProj PR QR)
    (hRL : ∀ x, PR (QL x) = QL (PR x)) (x : E) :
    normal PL PR (normal QL QR x) = normal PL PR x := by
  simp only [normal_apply, map_sub, hL.fix, hR.fix, hRL]
  abel

/-- **Oblique tangent-space projector** (abstract form of arXiv 2510.19518, §3.1; the two-factor
analogue of its Tucker Lemma 15, whose three-mode projector (34) is not of this form): if `P_L`,
`P_R` are oblique projectors onto the commuting orthogonal projectors `Q_L`, `Q_R`
(`Q_L Q_R = Q_R Q_L`) and the cross-commutations `P_L Q_R = Q_R P_L`, `P_R Q_L = Q_L P_R` hold,
then `P^∠ = P_L + P_R - P_L P_R` is an oblique projector onto the orthogonal tangent projector
`P = Q_L + Q_R - Q_L Q_R`: `P^∠ P = P` and `P P^∠ = P^∠`.  `P_L` and `P_R` need not commute. -/
theorem tangent (hL : IsObliqueProj PL QL) (hR : IsObliqueProj PR QR)
    (hQ : ∀ x, QL (QR x) = QR (QL x)) (hLR : ∀ x, PL (QR x) = QR (PL x))
    (hRL : ∀ x, PR (QL x) = QL (PR x)) :
    IsObliqueProj (LeanDLRA.tangent PL PR) (LeanDLRA.tangent QL QR) where
  orth := hL.orth.tangent hR.orth hQ
  fix x := by
    have h1 := tangent_apply_add_normal_apply PL PR (LeanDLRA.tangent QL QR x)
    have h2 := tangent_apply_add_normal_apply QL QR x
    have h3 : normal PL PR (LeanDLRA.tangent QL QR x) = 0 := by
      rw [eq_sub_of_add_eq h2, map_sub, normal_normal hL hR hRL, sub_self]
    rw [h3, add_zero] at h1
    exact h1
  range x := by
    have h1 := tangent_apply_add_normal_apply QL QR (LeanDLRA.tangent PL PR x)
    have h3 : normal QL QR (LeanDLRA.tangent PL PR x) = 0 := by
      simp only [normal_apply, tangent_apply, map_sub, map_add, ← hLR, hR.range, hL.range]
      abel
    rw [h3, add_zero] at h1
    exact h1

/-- `x - P^∠ x = (I - P_L)(I - P_R)(x - P x)`, the identity of the proof of Lemma 4 of
arXiv 2510.19518. -/
lemma sub_tangent_eq (hL : IsObliqueProj PL QL) (hR : IsObliqueProj PR QR)
    (hRL : ∀ x, PR (QL x) = QL (PR x)) (x : E) :
    x - LeanDLRA.tangent PL PR x =
      (1 - PL) ((1 - PR) (x - LeanDLRA.tangent QL QR x)) := by
  have h1 := tangent_apply_add_normal_apply PL PR x
  have h2 := tangent_apply_add_normal_apply QL QR x
  rw [← eq_sub_of_add_eq' h1, ← eq_sub_of_add_eq' h2, ← normal_normal hL hR hRL x]
  rfl

/-- `‖x - P^∠ x‖ ≤ ‖I - P_L‖ ‖I - P_R‖ ‖x - P x‖`. -/
theorem norm_sub_tangent_le (hL : IsObliqueProj PL QL) (hR : IsObliqueProj PR QR)
    (hRL : ∀ x, PR (QL x) = QL (PR x)) (x : E) :
    ‖x - LeanDLRA.tangent PL PR x‖ ≤ ‖1 - PL‖ * ‖1 - PR‖ * ‖x - LeanDLRA.tangent QL QR x‖ := by
  rw [sub_tangent_eq hL hR hRL, mul_assoc]
  exact ((1 - PL).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left ((1 - PR).le_opNorm _) (norm_nonneg _))

/-- **Lemma 4 of arXiv 2510.19518** (abstract form): the oblique tangent projection is
quasi-optimal, `‖x - P^∠ x‖ ≤ ‖P_L‖ ‖P_R‖ ‖x - P x‖`. -/
theorem norm_sub_tangent_le_opNorm (hL : IsObliqueProj PL QL) (hR : IsObliqueProj PR QR)
    (hRL : ∀ x, PR (QL x) = QL (PR x)) (hQL : QL ≠ 0) (hQR : QR ≠ 0) (x : E) :
    ‖x - LeanDLRA.tangent PL PR x‖ ≤ ‖PL‖ * ‖PR‖ * ‖x - LeanDLRA.tangent QL QR x‖ :=
  (norm_sub_tangent_le hL hR hRL x).trans <| mul_le_mul_of_nonneg_right
    (mul_le_mul (hL.opNorm_one_sub_le hQL) (hR.opNorm_one_sub_le hQR) (norm_nonneg _)
      (norm_nonneg _)) (norm_nonneg _)

/-- **Two-sided interpolatory (cross) oblique projector**: if `P_L`, `P_R` are oblique projectors
onto the commuting orthogonal projectors `Q_L`, `Q_R` and the cross-commutations
`P_L Q_R = Q_R P_L`, `P_R Q_L = Q_L P_R` hold, then `P_L P_R` is an oblique projector onto
`Q_L Q_R`.  For matrices, `X ↦ 𝒫_U X 𝒫_Vᵀ = U (S_UᵀU)⁻¹ (S_Uᵀ X S_V) (VᵀS_V)⁻¹ Vᵀ` is an
oblique projector onto `X ↦ U Uᵀ X V Vᵀ`; it is built from the bases `U`, `V` and is distinct
from the DEIM-CUR factorisation of Sorensen–Embree (whose factors are columns and rows of
`X`). -/
theorem mul (hL : IsObliqueProj PL QL) (hR : IsObliqueProj PR QR)
    (hQ : ∀ x, QL (QR x) = QR (QL x)) (hLR : ∀ x, PL (QR x) = QR (PL x))
    (hRL : ∀ x, PR (QL x) = QL (PR x)) : IsObliqueProj (PL * PR) (QL * QR) where
  orth := hL.orth.mul hR.orth hQ
  fix x := by
    change PL (PR (QL (QR x))) = QL (QR x)
    rw [hRL, hL.fix, hR.fix]
  range x := by
    change QL (QR (PL (PR x))) = PL (PR x)
    rw [← hLR, hL.range, hR.range]

/-- **Error of the two-sided interpolatory (cross) oblique projection** in terms of the
one-sided orthogonal errors: `‖x - P_L P_R x‖ ≤ ‖P_L‖ ‖x - Q_L x‖ + ‖P_L‖ ‖P_R‖ ‖x - Q_R x‖`, an
elementary consequence of the DEIM bound and the triangle inequality.  No commutativity is
needed.  (For matrices,
`‖X - 𝒫_U X 𝒫_Vᵀ‖ ≤ ‖𝒫_U‖ ‖X - U Uᵀ X‖ + ‖𝒫_U‖ ‖𝒫_V‖ ‖X - X V Vᵀ‖`; this is not the
Sorensen–Embree DEIM-CUR bound.) -/
theorem norm_sub_mul_le (hL : IsObliqueProj PL QL) (hR : IsObliqueProj PR QR) (hQL : QL ≠ 0)
    (hQR : QR ≠ 0) (x : E) :
    ‖x - PL (PR x)‖ ≤ ‖PL‖ * ‖x - QL x‖ + ‖PL‖ * ‖PR‖ * ‖x - QR x‖ := by
  have h : x - PL (PR x) = (x - PL x) + PL (x - PR x) := by rw [map_sub]; abel
  rw [h]
  refine (norm_add_le _ _).trans (add_le_add (hL.norm_sub_le_opNorm hQL x) ?_)
  calc ‖PL (x - PR x)‖ ≤ ‖PL‖ * ‖x - PR x‖ := PL.le_opNorm _
    _ ≤ ‖PL‖ * (‖PR‖ * ‖x - QR x‖) :=
      mul_le_mul_of_nonneg_left (hR.norm_sub_le_opNorm hQR x) (norm_nonneg _)
    _ = ‖PL‖ * ‖PR‖ * ‖x - QR x‖ := by ring

/-- `I - P^∠ = (I - P_L)(I - P_R)`, hence `‖I - P^∠‖ ≤ ‖I - P_L‖ ‖I - P_R‖` for arbitrary
operators `P_L`, `P_R`. -/
theorem _root_.LeanDLRA.opNorm_one_sub_tangent_le (PL PR : E →L[ℝ] E) :
    ‖1 - LeanDLRA.tangent PL PR‖ ≤ ‖1 - PL‖ * ‖1 - PR‖ := by
  rw [← normal_eq_one_sub_tangent]
  exact norm_mul_le _ _

/-- **Lemma 4 of arXiv 2510.19518** (norm of the oblique tangent projector):
`‖P^∠‖ ≤ ‖P_L‖ ‖P_R‖` for `Q_L, Q_R ≠ 0`, unconditionally as in eq. (15) of the paper.  If the
tangent projector `P = tangent Q_L Q_R` is a proper projector, this follows from Szyld's
identity; if `P = I`, then `P^∠ = I` and `‖I‖ ≤ 1 ≤ ‖P_L‖ ‖P_R‖`. -/
theorem opNorm_tangent_le (hL : IsObliqueProj PL QL) (hR : IsObliqueProj PR QR)
    (hQ : ∀ x, QL (QR x) = QR (QL x)) (hLR : ∀ x, PL (QR x) = QR (PL x))
    (hRL : ∀ x, PR (QL x) = QL (PR x)) (hQL : QL ≠ 0) (hQR : QR ≠ 0) :
    ‖LeanDLRA.tangent PL PR‖ ≤ ‖PL‖ * ‖PR‖ := by
  have hP := hL.tangent hR hQ hLR hRL
  by_cases hT : LeanDLRA.tangent QL QR = 1
  · have h1 : LeanDLRA.tangent PL PR = 1 := by
      ext x
      have := hP.fix x
      rw [hT] at this
      exact this
    rw [h1]
    have a := hL.one_le_opNorm hQL
    have b := hR.one_le_opNorm hQR
    calc ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
      _ ≤ ‖PL‖ * ‖PR‖ := by nlinarith
  · exact (hP.opNorm_le_opNorm_one_sub hT).trans <|
      (opNorm_one_sub_tangent_le PL PR).trans <|
        mul_le_mul (hL.opNorm_one_sub_le hQL) (hR.opNorm_one_sub_le hQR) (norm_nonneg _)
          (norm_nonneg _)

/-- **Lemma 4 of arXiv 2510.19518** (Szyld's identity for the oblique tangent projector):
`‖I - P^∠‖ = ‖P^∠‖` when `0 ≠ P ≠ I`. -/
theorem opNorm_one_sub_tangent_eq (hL : IsObliqueProj PL QL) (hR : IsObliqueProj PR QR)
    (hQ : ∀ x, QL (QR x) = QR (QL x)) (hLR : ∀ x, PL (QR x) = QR (PL x))
    (hRL : ∀ x, PR (QL x) = QL (PR x)) (hT0 : LeanDLRA.tangent QL QR ≠ 0)
    (hT : LeanDLRA.tangent QL QR ≠ 1) :
    ‖1 - LeanDLRA.tangent PL PR‖ = ‖LeanDLRA.tangent PL PR‖ :=
  (hL.tangent hR hQ hLR hRL).opNorm_one_sub_eq hT0 hT

end Tangent

end IsObliqueProj

/-! ### Sketched oblique projectors: equivalence with the orthogonal projection -/

section Sketch

variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']

/-- **Deterministic core of Proposition 4.4 of arXiv 2607.03402.**  Let `P^∠` be an oblique
projector onto the orthogonal (tangent) projector `P`, and let the sketch `σ : E → E'` map it
to an orthogonal projector `P̂` of the sketch space (`σ ∘ P^∠ = P̂ ∘ σ`, Lemma 4.2 of
arXiv 2607.03402).  Assume that `σ` does not annihilate the single tangent vector
`δ = P^∠ z - P z`.  Then the oblique projection reproduces the orthogonal one, `P^∠ z = P z`, if
and only if the sketched normal component `σ (z - P z)` is orthogonal to the sketch of every
tangent vector (condition (14) of arXiv 2607.03402).

For the oblique sketch DLRA (`z = F(Y)`, `Ẏ = P^∠ z`), `δ = Ẏ - P_Y F(Y)` is exactly the `Z` of
Prop. 4.4, whose hypothesis (`Θ`, `Ω` embed the column and row spaces of `Z`) gives
`‖σ δ‖ ≥ (1 - ϵ) ‖δ‖ > 0` for `δ ≠ 0`; only this consequence is used here.  Injectivity of `σ`
on the whole tangent space is *not* assumed: it would force `Θ` and `Ω` to be injective, i.e.
no compression. -/
theorem IsObliqueProj.eq_iff_of_sketch {Pob P : E →L[ℝ] E} {Phat : E' →L[ℝ] E'}
    {σ : E →L[ℝ] E'} (h : IsObliqueProj Pob P) (hPhat : IsOrthProj Phat)
    (hσ : ∀ x, σ (Pob x) = Phat (σ x)) (z : E)
    (hinj : σ (Pob z - P z) = 0 → Pob z - P z = 0) :
    Pob z = P z ↔ ∀ δ, P δ = δ → ⟪σ (z - P z), σ δ⟫ = 0 := by
  have hN : Pob (z - P z) = Pob z - P z := h.map_sub_proj z
  constructor
  · intro hz δ hδ
    have h0 : Phat (σ (z - P z)) = 0 := by rw [← hσ, hN, hz, sub_self, map_zero]
    have hδ' : σ δ = Phat (σ δ) := by
      rw [← hσ, ← hδ, h.fix]
    rw [hδ', ← hPhat.symm, h0, inner_zero_left]
  · intro hz
    set δ := Pob (z - P z)
    have hδP : P δ = δ := h.range _
    have h1 : ⟪σ (z - P z), σ δ⟫ = 0 := hz δ hδP
    have h2 : σ δ = Phat (σ (z - P z)) := hσ _
    rw [h2, real_inner_comm, hPhat.inner_self_apply] at h1
    have h3 : σ δ = 0 := by
      rw [h2]; exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1)
    rw [← sub_eq_zero]
    exact hinj (by rw [← hN]; exact h3)

/-- **Approximate equivalence of oblique sketched projection and orthogonal projection**
(deterministic, quantitative form of eq. (15) of arXiv 2607.03402; Remark 4.6 there discusses
this regime but does not pursue a bound).  In the setting of `IsObliqueProj.eq_iff_of_sketch`,
let `n = z - P z` be the normal component and `δ = P^∠ z - P z` (the `Z` of Prop. 4.4), and
assume, for these two vectors only,
* the lower embedding `(1 - ε) ‖δ‖ ≤ ‖σ δ‖`, and
* the oblique residual bound `|⟪σ n, σ δ⟫| ≤ η ‖n‖ ‖δ‖` (note `⟪n, δ⟫ = 0`).

Then `‖P^∠ z - P z‖ ≤ η / (1 - ε)² ‖z - P z‖`: the oblique sketched projection is close to the
orthogonal one when the normal component is small.

On the hypotheses: for a pair `(n, δ)` fixed independently of the sketch, with combined column
and row spaces of dimension `≤ d`, Corollary 2.3 of arXiv 2607.03402 would give both bounds with
`η = 2ε + ε²` for `OSE(d, ε, δ)` sketches.  Here, however, `δ` depends on the sketch, and `n` has
in general full rank, so Corollary 2.3 does not apply directly (Remarks 4.5 and 4.6 of the
paper); the hypotheses are therefore stated deterministically on the realized sketch, as in
Prop. 4.4.  Uniform versions over the whole tangent space would be vacuous for compressive
sketches. -/
theorem IsObliqueProj.norm_sub_le_of_sketch {Pob P : E →L[ℝ] E} {Phat : E' →L[ℝ] E'}
    {σ : E →L[ℝ] E'} (h : IsObliqueProj Pob P) (hPhat : IsOrthProj Phat)
    (hσ : ∀ x, σ (Pob x) = Phat (σ x)) {ε η : ℝ} (hε : ε < 1) (hη : 0 ≤ η) (z : E)
    (hlow : (1 - ε) * ‖Pob z - P z‖ ≤ ‖σ (Pob z - P z)‖)
    (hip : |⟪σ (z - P z), σ (Pob z - P z)⟫| ≤ η * ‖z - P z‖ * ‖Pob z - P z‖) :
    ‖Pob z - P z‖ ≤ η / (1 - ε) ^ 2 * ‖z - P z‖ := by
  set n := z - P z with hn
  set δ := Pob z - P z with hδ
  have hδn : δ = Pob n := (h.map_sub_proj z).symm
  have hσδ : σ δ = Phat (σ n) := by rw [hδn]; exact hσ n
  have hsq : ‖σ δ‖ ^ 2 = ⟪σ n, σ δ⟫ := by
    rw [hσδ, real_inner_comm, hPhat.inner_self_apply]
  have hup : ‖σ δ‖ ^ 2 ≤ η * ‖n‖ * ‖δ‖ := by rw [hsq]; exact (le_abs_self _).trans hip
  have h1ε : 0 < 1 - ε := by linarith
  have key : (1 - ε) ^ 2 * ‖δ‖ ^ 2 ≤ η * ‖n‖ * ‖δ‖ := by
    have := pow_le_pow_left₀ (by positivity) hlow 2
    nlinarith
  rcases (norm_nonneg δ).eq_or_lt with h0 | hpos
  · rw [← h0]; exact mul_nonneg (div_nonneg hη (sq_nonneg _)) (norm_nonneg _)
  · rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith

/-- The oblique sketched field is `(1 + η / (1 - ε)²) ε`-close to the full field when the normal
component is `ε`-small (under the pointwise hypotheses of `IsObliqueProj.norm_sub_le_of_sketch`);
compare with the worst-case constant `‖P^∠‖` of `IsObliqueProj.norm_sub_le_of_normal`. -/
theorem IsObliqueProj.norm_sub_self_le_of_sketch {Pob P : E →L[ℝ] E} {Phat : E' →L[ℝ] E'}
    {σ : E →L[ℝ] E'} (h : IsObliqueProj Pob P) (hPhat : IsOrthProj Phat)
    (hσ : ∀ x, σ (Pob x) = Phat (σ x)) {ε η : ℝ} (hε : ε < 1) (hη : 0 ≤ η) (z : E)
    (hlow : (1 - ε) * ‖Pob z - P z‖ ≤ ‖σ (Pob z - P z)‖)
    (hip : |⟪σ (z - P z), σ (Pob z - P z)⟫| ≤ η * ‖z - P z‖ * ‖Pob z - P z‖) :
    ‖Pob z - z‖ ≤ (1 + η / (1 - ε) ^ 2) * ‖z - P z‖ := by
  have h1 := h.norm_sub_le_of_sketch hPhat hσ hε hη z hlow hip
  calc ‖Pob z - z‖ ≤ ‖Pob z - P z‖ + ‖P z - z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ η / (1 - ε) ^ 2 * ‖z - P z‖ + ‖z - P z‖ := by rw [norm_sub_rev (P z)]; linarith
    _ = (1 + η / (1 - ε) ^ 2) * ‖z - P z‖ := by ring

end Sketch

/-! ### Filippov regularisation and the error bound of DLRA-DEIM -/

section Filippov

/- `filippov` is defined in `LeanDLRA/Analysis/Defs.lean`. -/

/-- **Corollary 9 of arXiv 2510.19518.**  If `‖f z - F z‖ ≤ c` for all `z ∈ ℳ` and `F` is
continuous at `y`, then every element `v` of the Filippov set `𝓕(y)` satisfies
`‖v - F y‖ ≤ c`. -/
theorem norm_sub_le_of_mem_filippov {f F : E → E} {M : Set E} {c : ℝ} {y v : E}
    (hF : ContinuousAt F y) (hf : ∀ z ∈ M, ‖f z - F z‖ ≤ c) (hv : v ∈ filippov f M y) :
    ‖v - F y‖ ≤ c := by
  refine le_of_forall_pos_le_add fun η hη => ?_
  obtain ⟨δ, hδ, hδF⟩ := Metric.continuousAt_iff.1 hF η hη
  have hsub : f '' (ball y δ ∩ M) ⊆ closedBall (F y) (c + η) := by
    rintro _ ⟨z, ⟨hz, hzM⟩, rfl⟩
    rw [mem_closedBall, dist_eq_norm]
    have h1 := hf z hzM
    have h2 : ‖F z - F y‖ < η := by
      rw [← dist_eq_norm]; exact hδF (mem_ball.1 hz)
    calc ‖f z - F y‖ = ‖(f z - F z) + (F z - F y)‖ := by abel_nf
      _ ≤ ‖f z - F z‖ + ‖F z - F y‖ := norm_add_le _ _
      _ ≤ c + η := by linarith
  have hv' : v ∈ closure (convexHull ℝ (f '' (ball y δ ∩ M))) := by
    have := mem_iInter₂.1 hv δ hδ
    exact this
  have hcl : closure (convexHull ℝ (f '' (ball y δ ∩ M))) ⊆ closedBall (F y) (c + η) :=
    closure_minimal (convexHull_min hsub (convex_closedBall _ _)) isClosed_closedBall
  have := hcl hv'
  rwa [mem_closedBall, dist_eq_norm] at this

/-- The field `f(z) = P^∠(z) F(z)` of interpolatory DLRA is `C ε`-close to `F` on `ℳ`, if the
oblique projectors `P^∠(z)` (onto nonzero orthogonal projectors `P(z)`) have norm `≤ C` and the
normal component of `F` is `≤ ε` on `ℳ` (Assumption 3 and Lemma 4 of arXiv 2510.19518). -/
theorem norm_obliqueField_sub_le {F : E → E} {M : Set E} {Pob P : E → E →L[ℝ] E} {C ε : ℝ}
    (hP : ∀ z ∈ M, IsObliqueProj (Pob z) (P z)) (hP0 : ∀ z ∈ M, P z ≠ 0)
    (hC : ∀ z ∈ M, ‖Pob z‖ ≤ C) (hε : ∀ z ∈ M, ‖F z - P z (F z)‖ ≤ ε) :
    ∀ z ∈ M, ‖Pob z (F z) - F z‖ ≤ C * ε := fun z hz => by
  rw [norm_sub_rev]
  exact (hP z hz).norm_sub_le_of_normal (hP0 z hz) (hε z hz) (hC z hz)

/-- **Theorem 10 of arXiv 2510.19518** (error bound for DLRA-DEIM, Filippov form).  Let `A`
solve `A' = F(t, A)` with `F` one-sided Lipschitz with constant `ℓ` and `F t` continuous, and let
`Y` be a continuous trajectory whose right derivative lies, at every `t ∈ [a, b)`, in the
Filippov set of a field `f t` with `‖f t z - F t z‖ ≤ c` on `ℳ` (by
`norm_obliqueField_sub_le`, `c = C_{m,r} C_{n,r} ε_r` for interpolatory DLRA).  Then
`‖Y t - A t‖ ≤ gronwallBound ‖Y a - A a‖ ℓ c (t - a)
  = e^{ℓ(t-a)} ‖Y a - A a‖ + c ∫ₐᵗ e^{ℓ(t-s)} ds`. -/
theorem norm_sub_le_of_filippov {F f : ℝ → E → E} {M : Set E} {ℓ c a b : ℝ} {A Y u : ℝ → E}
    (hF : IsOneSidedLipschitzField F ℓ) (hFc : ∀ t, Continuous (F t))
    (hf : ∀ t, ∀ z ∈ M, ‖f t z - F t z‖ ≤ c) (hA : ODESolution F A a b)
    (hYc : ContinuousOn Y (Icc a b)) (hY : ∀ t ∈ Ico a b, HasDerivWithinAt Y (u t) (Ici t) t)
    (hu : ∀ t ∈ Ico a b, u t ∈ filippov (f t) M (Y t)) :
    ∀ t ∈ Icc a b, ‖Y t - A t‖ ≤ gronwallBound ‖Y a - A a‖ ℓ c (t - a) := by
  intro t ht
  have h := norm_sub_le_gronwallBound_of_oneSided (ηz := 0) hF hYc hY
    (fun s hs => norm_sub_le_of_mem_filippov (hFc s).continuousAt (hf s) (hu s hs))
    hA.cont hA.deriv (fun _ _ => by simp) le_rfl t ht
  rwa [add_zero] at h

/-- **Theorem 10 of arXiv 2510.19518** (classical-solution form): if
`Y' = P^∠(t) F(t, Y)` where, along `Y`, `P^∠(t)` is an oblique projector onto the nonzero
orthogonal projector `P(t)` with `‖P^∠(t)‖ ≤ C` and the normal component satisfies
`‖F(t, Y t) - P(t) F(t, Y t)‖ ≤ ε`, and `A' = F(t, A)` with `F` one-sided Lipschitz (constant
`ℓ`), then `‖Y t - A t‖ ≤ gronwallBound ‖Y a - A a‖ ℓ (C ε) (t - a)`.  The projectors may depend
on `t` arbitrarily (e.g. through `Y(t)` and a piecewise constant index selection). -/
theorem norm_sub_le_of_oblique {F : ℝ → E → E} {Pob P : ℝ → E →L[ℝ] E} {ℓ C ε a b : ℝ}
    {A Y : ℝ → E} (hF : IsOneSidedLipschitzField F ℓ) (hA : ODESolution F A a b)
    (hY : ODESolution (fun t x => Pob t (F t x)) Y a b)
    (hP : ∀ t ∈ Ico a b, IsObliqueProj (Pob t) (P t)) (hP0 : ∀ t ∈ Ico a b, P t ≠ 0)
    (hC : ∀ t ∈ Ico a b, ‖Pob t‖ ≤ C) (hε : ∀ t ∈ Ico a b, ‖F t (Y t) - P t (F t (Y t))‖ ≤ ε) :
    ∀ t ∈ Icc a b, ‖Y t - A t‖ ≤ gronwallBound ‖Y a - A a‖ ℓ (C * ε) (t - a) :=
  ODESolution.norm_sub_le_of_perturbed hA hY hF fun t ht => by
    rw [norm_sub_rev]
    exact (hP t ht).norm_sub_le_of_normal (hP0 t ht) (hε t ht) (hC t ht)

/-- **Error bound for oblique sketch DLRA** (a quantitative trajectory version of eq. (15) of
arXiv 2607.03402, §4.2; Remark 4.6 there leaves such a perturbation argument open): if
`Y' = P^∠(t) F(t, Y)` with oblique sketched projectors satisfying, along `Y` and at every
`t ∈ [a, b)`, the pointwise hypotheses of `IsObliqueProj.norm_sub_le_of_sketch` (constants
`ε < 1`, `η ≥ 0`) at the realized vectors `n_t = F(t, Y t) - P(t) F(t, Y t)` and
`δ_t = P^∠(t) F(t, Y t) - P(t) F(t, Y t) = Ẏ(t) - P(t) F(t, Y t)` (the `Z` of Prop. 4.4), and
the normal component is `≤ ε_r`, and `A' = F(t, A)` with `F` one-sided Lipschitz, then
`‖Y t - A t‖ ≤ gronwallBound ‖Y a - A a‖ ℓ ((1 + η / (1 - ε)²) ε_r) (t - a)`, i.e. the DLRA
bound with `ε_r` inflated only by `1 + η / (1 - ε)²` (not by `‖P^∠‖`).  The hypotheses are
deterministic conditions on the realized sketches (cf. Remark 4.5 of the paper). -/
theorem norm_sub_le_of_obliqueSketch {E' : Type*} [NormedAddCommGroup E']
    [InnerProductSpace ℝ E'] {F : ℝ → E → E} {Pob P : ℝ → E →L[ℝ] E}
    {Phat : ℝ → E' →L[ℝ] E'} {σ : ℝ → E →L[ℝ] E'} {ℓ ε η εr a b : ℝ} {A Y : ℝ → E}
    (hF : IsOneSidedLipschitzField F ℓ) (hA : ODESolution F A a b)
    (hY : ODESolution (fun t x => Pob t (F t x)) Y a b)
    (hP : ∀ t ∈ Ico a b, IsObliqueProj (Pob t) (P t))
    (hPhat : ∀ t ∈ Ico a b, IsOrthProj (Phat t))
    (hσ : ∀ t ∈ Ico a b, ∀ x, σ t (Pob t x) = Phat t (σ t x)) (hε : ε < 1) (hη : 0 ≤ η)
    (hlow : ∀ t ∈ Ico a b, (1 - ε) * ‖Pob t (F t (Y t)) - P t (F t (Y t))‖ ≤
      ‖σ t (Pob t (F t (Y t)) - P t (F t (Y t)))‖)
    (hip : ∀ t ∈ Ico a b,
      |⟪σ t (F t (Y t) - P t (F t (Y t))), σ t (Pob t (F t (Y t)) - P t (F t (Y t)))⟫| ≤
        η * ‖F t (Y t) - P t (F t (Y t))‖ * ‖Pob t (F t (Y t)) - P t (F t (Y t))‖)
    (hεr : ∀ t ∈ Ico a b, ‖F t (Y t) - P t (F t (Y t))‖ ≤ εr) :
    ∀ t ∈ Icc a b,
      ‖Y t - A t‖ ≤ gronwallBound ‖Y a - A a‖ ℓ ((1 + η / (1 - ε) ^ 2) * εr) (t - a) :=
  ODESolution.norm_sub_le_of_perturbed hA hY hF fun t ht =>
    ((hP t ht).norm_sub_self_le_of_sketch (hPhat t ht) (hσ t ht) hε hη _ (hlow t ht)
      (hip t ht)).trans (mul_le_mul_of_nonneg_left (hεr t ht)
        (by have := div_nonneg hη (sq_nonneg (1 - ε)); linarith))

end Filippov

/-! ### Exactness and the projected Euler-DEIM method -/

section EulerDEIM

/-- A point of `ℳ` contributes its own field value to the Filippov set. -/
lemma mem_filippov_self {f : E → E} {M : Set E} {y : E} (hy : y ∈ M) :
    f y ∈ filippov f M y :=
  mem_iInter₂.2 fun _ hδ =>
    subset_closure (subset_convexHull ℝ _ ⟨y, ⟨mem_ball_self hδ, hy⟩, rfl⟩)

/-- **Lemma 7 of arXiv 2510.19518, existence part** (exactness, pointwise Filippov form): if
`y ∈ ℳ` and `F(y)` lies in the range of the orthogonal (tangent) projector `P(y)`, then `F(y)`
belongs to the Filippov set of the interpolatory field `z ↦ P^∠(z) F(z)` at `y`, for every
oblique projector `P^∠(y)` onto `P(y)` (because `P^∠(y)` fixes the range of `P(y)`).  Applied at
every time, a solution of `A' = F(A)` with `A(t) ∈ ℳ` and `Ȧ ∈ T_A ℳ` satisfies the differential
inclusion of DLRA-DEIM.

Not formalized: the derivation of the tangency `Ȧ(t) ∈ T_{A(t)} ℳ` from `A(t) ∈ ℳ` (here the
hypothesis `hT`) and the uniqueness half of Lemma 7 (under QDEIM). -/
theorem mem_filippov_of_mem_range {F : E → E} {M : Set E} {Pob P : E → E →L[ℝ] E} {y : E}
    (hy : y ∈ M) (hP : IsObliqueProj (Pob y) (P y)) (hT : P y (F y) = F y) :
    F y ∈ filippov (fun z => Pob z (F z)) M y := by
  have h : Pob y (F y) = F y := by
    calc Pob y (F y) = Pob y (P y (F y)) := by rw [hT]
      _ = P y (F y) := hP.fix _
      _ = F y := hT
  have := mem_filippov_self (f := fun z => Pob z (F z)) hy
  rwa [h] at this

/-- **Lemma 7 of arXiv 2510.19518, existence part** (exactness, classical trajectory form): if
`A' = F(t, A)` and the velocity `F(t, A(t))` lies in the range of `P(t)` (the tangent space;
in the paper this follows from `A(t) ∈ ℳ_r`, which is not derived here), then `A` also solves
the interpolatory DLRA `Y' = P^∠(t) F(t, Y)` for any oblique projectors `P^∠(t)` onto `P(t)`.
The uniqueness half of Lemma 7 is not formalized. -/
theorem ODESolution.oblique_of_mem_range {F : ℝ → E → E} {Pob P : ℝ → E →L[ℝ] E} {A : ℝ → E}
    {a b : ℝ} (hA : ODESolution F A a b) (hP : ∀ t ∈ Ico a b, IsObliqueProj (Pob t) (P t))
    (hT : ∀ t ∈ Ico a b, P t (F t (A t)) = F t (A t)) :
    ODESolution (fun t x => Pob t (F t x)) A a b where
  cont := hA.cont
  deriv t ht := by
    have h : Pob t (F t (A t)) = F t (A t) := by
      calc Pob t (F t (A t)) = Pob t (P t (F t (A t))) := by rw [hT t ht]
        _ = P t (F t (A t)) := (hP t ht).fix _
        _ = F t (A t) := hT t ht
    change HasDerivWithinAt A (Pob t (F t (A t))) (Ici t) t
    rw [h]
    exact hA.deriv t ht

/-- **Local error of the explicit Euler method**: if `φ` solves `φ' = F(t, φ)` on `[a, b]` and the
field along `φ` deviates from `F(a, φ a)` by at most `K`, then
`‖φ b - (φ a + (b - a) F(a, φ a))‖ ≤ K (b - a)`. -/
theorem ODESolution.norm_sub_euler_le {F : ℝ → E → E} {φ : ℝ → E} {a b K : ℝ} (hab : a ≤ b)
    (hφ : ODESolution F φ a b) (hK : ∀ t ∈ Ico a b, ‖F t (φ t) - F a (φ a)‖ ≤ K) :
    ‖φ b - (φ a + (b - a) • F a (φ a))‖ ≤ K * (b - a) := by
  set v := F a (φ a)
  set g : ℝ → E := fun t => φ t - (t - a) • v with hg
  have hgc : ContinuousOn g (Icc a b) :=
    hφ.cont.sub (((continuous_id.sub continuous_const).smul continuous_const).continuousOn)
  have hgd : ∀ t ∈ Ico a b, HasDerivWithinAt g (F t (φ t) - v) (Ici t) t := fun t ht => by
    have h1 : HasDerivWithinAt (fun s : ℝ => (s - a) • v) ((1 : ℝ) • v) (Ici t) t :=
      ((hasDerivWithinAt_id t _).sub_const a).smul_const v
    rw [one_smul] at h1
    exact (hφ.deriv t ht).sub h1
  have h := norm_image_sub_le_of_norm_deriv_right_le_segment hgc hgd hK b ⟨hab, le_rfl⟩
  have hgb : g b - g a = φ b - (φ a + (b - a) • v) := by
    simp only [hg, sub_self, zero_smul, sub_zero]; abel
  rwa [hgb] at h

/-- **Lemma 11 of arXiv 2510.19518** (local error of projected Euler-DEIM, abstract form).
Let `T` be a quasi-best approximation onto `ℳ` (`‖T x - x‖ ≤ κ ‖z - x‖` for `z ∈ ℳ`; `κ = 1`
for the truncated SVD `T_r` by Eckart–Young), `P^∠` an oblique projector onto the nonzero
orthogonal (tangent) projector `P` with `‖P^∠‖ ≤ C`, and `v = F(y)` with normal component
`‖v - P v‖ ≤ ε`.  If `w = φ^h(y)` is the exact flow, `‖w - (y + h v)‖ ≤ e` (Euler's local error)
and some `z ∈ ℳ` is `d`-close to `w`, then the projected Euler-DEIM step satisfies
`‖T(y + h P^∠ v) - w‖ ≤ κ d + (1 + κ)(e + h C ε)`.

This is the argument of Kieri–Vandereycken (Lemma 3 of their projection-method paper) with the
oblique projection, as in the proof of Lemma 11 of arXiv 2510.19518: `d = O(h ε)` comes from the
DLRA error bound (`ODESolution.norm_sub_le_of_perturbed_max` with zero initial error) and
`e = O(h²)` from `ODESolution.norm_sub_euler_le`. -/
theorem norm_projEulerDEIM_sub_le {T : E → E} {M : Set E} {κ : ℝ}
    (hT : ∀ x, ∀ z ∈ M, ‖T x - x‖ ≤ κ * ‖z - x‖) (hκ : 0 ≤ κ) {Pob P : E →L[ℝ] E}
    (hP : IsObliqueProj Pob P) (hP0 : P ≠ 0) {C ε h e d : ℝ} (hC : ‖Pob‖ ≤ C) (hh : 0 ≤ h)
    {y v w z : E} (hv : ‖v - P v‖ ≤ ε) (hE : ‖w - (y + h • v)‖ ≤ e) (hz : z ∈ M)
    (hd : ‖z - w‖ ≤ d) :
    ‖T (y + h • Pob v) - w‖ ≤ κ * d + (1 + κ) * (e + h * (C * ε)) := by
  set x := y + h • Pob v
  have hPv : ‖Pob v - v‖ ≤ C * ε := by
    rw [norm_sub_rev]; exact hP.norm_sub_le_of_normal hP0 hv hC
  have hxw : ‖x - w‖ ≤ e + h * (C * ε) := by
    have : x - w = h • (Pob v - v) - (w - (y + h • v)) := by
      simp only [x, smul_sub]; abel
    rw [this]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hh]
    nlinarith [mul_le_mul_of_nonneg_left hPv hh]
  have hzx : ‖z - x‖ ≤ d + (e + h * (C * ε)) := by
    calc ‖z - x‖ ≤ ‖z - w‖ + ‖w - x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ d + (e + h * (C * ε)) := by rw [norm_sub_rev w x]; exact add_le_add hd hxw
  calc ‖T x - w‖ ≤ ‖T x - x‖ + ‖x - w‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ κ * (d + (e + h * (C * ε))) + (e + h * (C * ε)) :=
        add_le_add ((hT x z hz).trans (mul_le_mul_of_nonneg_left hzx hκ)) hxw
    _ = κ * d + (1 + κ) * (e + h * (C * ε)) := by ring

/-- **Theorem 12 of arXiv 2510.19518** (global error of projected Euler-DEIM, abstract form).
Let `F` be `L`-Lipschitz (Assumption 1), `A' = F(A)`, and let
`Y_{n+1} = T(Y_n + h P^∠_n F(Y_n))` with oblique projectors `P^∠_n` onto nonzero orthogonal
(tangent) projectors `P_n`, `‖P^∠_n‖ ≤ C` (`C = C_{m,r} C_{n,r}` by Lemma 4) and normal components
`‖F(Y_n) - P_n F(Y_n)‖ ≤ ε` (Assumption 3).  The map `T` enters only through the quasi-best
approximation property `‖T x - x‖ ≤ κ ‖z - x‖` for all `z ∈ ℳ` (`κ = 1` for the truncated SVD
`T_r` by Eckart–Young); `T x ∈ ℳ` is not needed for the bound and is not assumed.  Let `Φ_n` be
the exact flow from `Y_n` on `[t_n, t_{n+1}]`, along which `‖F‖ ≤ B` (Assumption 4, localised).
If `Φ_n(t_{n+1})` is `h g`-close to `ℳ` (hypothesis `hM`), then for `n h ≤ T_f`
`‖Y_n - A(t_n)‖ ≤ e^{L T_f} (‖Y_0 - A(t_0)‖ + T_f (κ g + (1 + κ)(L B h + C ε)))`.

Deviations: `hM` carries the central analytic step of Kieri–Vandereycken (their Lemma 3, used in
the proof of the paper's Lemma 11); `norm_projEulerDEIM_sub_le_global_of_dlra` discharges it with
`g = ε_d e^{L h}` from DLRA trajectories on `ℳ`, which gives the paper's form
`C'(δ + C_{m,r} C_{n,r} ε_r + h)` with explicit constants.  The bound `B` is used for Euler's local
error `L B h²` (the paper refers to Kieri–Vandereycken for this step). -/
theorem norm_projEulerDEIM_sub_le_global {F : E → E} {L B : ℝ}
    (hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) (hL : 0 ≤ L) (hB0 : 0 ≤ B)
    {T : E → E} {M : Set E} {κ : ℝ} (hT : ∀ x, ∀ z ∈ M, ‖T x - x‖ ≤ κ * ‖z - x‖) (hκ : 0 ≤ κ)
    {Pob P : ℕ → E →L[ℝ] E} {C ε g t₀ h : ℝ} (hC0 : 0 ≤ C) (hε0 : 0 ≤ ε) (hg : 0 ≤ g)
    (hh : 0 ≤ h) {N : ℕ} {A : ℝ → E} (hA : ODESolution (fun _ => F) A t₀ (t₀ + N * h))
    {Y : ℕ → E} {Φ : ℕ → ℝ → E}
    (hΦ : ∀ n < N, ODESolution (fun _ => F) (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n)
    (hB : ∀ n < N, ∀ t ∈ Ico (t₀ + n * h) (t₀ + (n + 1) * h), ‖F (Φ n t)‖ ≤ B)
    (hP : ∀ n < N, IsObliqueProj (Pob n) (P n)) (hP0 : ∀ n < N, P n ≠ 0)
    (hC : ∀ n < N, ‖Pob n‖ ≤ C) (hε : ∀ n < N, ‖F (Y n) - P n (F (Y n))‖ ≤ ε)
    (hY : ∀ n < N, Y (n + 1) = T (Y n + h • Pob n (F (Y n))))
    (hM : ∀ n < N, ∃ z ∈ M, ‖z - Φ n (t₀ + (n + 1) * h)‖ ≤ h * g) {Tf : ℝ} :
    ∀ n ≤ N, (n : ℝ) * h ≤ Tf →
      ‖Y n - A (t₀ + n * h)‖ ≤
        Real.exp (L * Tf) * (‖Y 0 - A t₀‖ + Tf * (κ * g + (1 + κ) * (L * B * h + C * ε))) := by
  refine lady_windermere_of_le (fun _ => hF) hL hh hA hΦ hΦ₀ (by positivity) fun n hn => ?_
  obtain ⟨z, hz, hzd⟩ := hM n hn
  have hab : t₀ + n * h ≤ t₀ + (n + 1) * h := by nlinarith
  have hstep : t₀ + (n + 1) * h - (t₀ + n * h) = h := by ring
  -- Euler's local error `L B h²`
  have hK : ∀ t ∈ Ico (t₀ + n * h) (t₀ + (n + 1) * h),
      ‖F (Φ n t) - F (Φ n (t₀ + n * h))‖ ≤ L * (B * h) := fun t ht => by
    have hs := (hΦ n hn).norm_sub_le (B := B) (hB n hn) t ⟨ht.1, ht.2.le⟩
    refine (hF _ _).trans (mul_le_mul_of_nonneg_left (hs.trans ?_) hL)
    exact mul_le_mul_of_nonneg_left (by linarith [ht.2]) hB0
  have hE := (hΦ n hn).norm_sub_euler_le hab hK
  rw [hstep, hΦ₀ n hn] at hE
  have hloc := norm_projEulerDEIM_sub_le hT hκ (hP n hn) (hP0 n hn) (hC n hn) hh
    (hε n hn) hE hz hzd
  rw [hY n hn]
  calc ‖T (Y n + h • Pob n (F (Y n))) - Φ n (t₀ + (n + 1) * h)‖
      ≤ κ * (h * g) + (1 + κ) * (L * (B * h) * h + h * (C * ε)) := hloc
    _ = h * (κ * g + (1 + κ) * (L * B * h + C * ε)) := by ring

/-- **Theorem 12 of arXiv 2510.19518** with the closeness hypothesis discharged by the DLRA error
bound.  In the setting of `norm_projEulerDEIM_sub_le_global`, assume that for every step there is
a trajectory `Ψ_n` on `[t_n, t_{n+1}]` starting at `Y_n`, lying on `ℳ` at `t_{n+1}`, and solving
a perturbed problem `Ψ' = G_n(t, Ψ)` with defect `‖G_n(t, Ψ_n t) - F(Ψ_n t)‖ ≤ ε_d` (e.g. the
orthogonal DLRA `G_n = P(Ψ) F(Ψ)` on `ℳ_r`, whose defect is the normal component, `ε_d = ε_r`
by Assumption 3).  Then `‖Ψ_n(t_{n+1}) - Φ_n(t_{n+1})‖ ≤ h ε_d e^{L h}`
(`ODESolution.norm_sub_le_of_perturbed_max`), and for `n h ≤ T_f`
`‖Y_n - A(t_n)‖ ≤ e^{L T_f} (‖Y_0 - A(t_0)‖ + T_f (κ ε_d e^{L h} + (1 + κ)(L B h + C ε)))`,
i.e. `C'(δ + C_{m,r} C_{n,r} ε_r + h)` for `h ≤ h₀`.  The existence of the trajectories `Ψ_n`
(the DLRA solution from `Y_n` stays on `ℳ` for one step) remains a hypothesis, as in the
paper. -/
theorem norm_projEulerDEIM_sub_le_global_of_dlra {F : E → E} {L B : ℝ}
    (hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) (hL : 0 ≤ L) (hB0 : 0 ≤ B)
    {T : E → E} {M : Set E} {κ : ℝ} (hT : ∀ x, ∀ z ∈ M, ‖T x - x‖ ≤ κ * ‖z - x‖) (hκ : 0 ≤ κ)
    {Pob P : ℕ → E →L[ℝ] E} {C ε εd t₀ h : ℝ} (hC0 : 0 ≤ C) (hε0 : 0 ≤ ε) (hεd : 0 ≤ εd)
    (hh : 0 ≤ h) {N : ℕ} {A : ℝ → E} (hA : ODESolution (fun _ => F) A t₀ (t₀ + N * h))
    {Y : ℕ → E} {Φ : ℕ → ℝ → E}
    (hΦ : ∀ n < N, ODESolution (fun _ => F) (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n)
    (hB : ∀ n < N, ∀ t ∈ Ico (t₀ + n * h) (t₀ + (n + 1) * h), ‖F (Φ n t)‖ ≤ B)
    (hP : ∀ n < N, IsObliqueProj (Pob n) (P n)) (hP0 : ∀ n < N, P n ≠ 0)
    (hC : ∀ n < N, ‖Pob n‖ ≤ C) (hε : ∀ n < N, ‖F (Y n) - P n (F (Y n))‖ ≤ ε)
    (hY : ∀ n < N, Y (n + 1) = T (Y n + h • Pob n (F (Y n))))
    {G : ℕ → ℝ → E → E} {Ψ : ℕ → ℝ → E}
    (hΨ : ∀ n < N, ODESolution (G n) (Ψ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΨ₀ : ∀ n < N, Ψ n (t₀ + n * h) = Y n) (hΨM : ∀ n < N, Ψ n (t₀ + (n + 1) * h) ∈ M)
    (hG : ∀ n < N, ∀ t ∈ Ico (t₀ + n * h) (t₀ + (n + 1) * h),
      ‖G n t (Ψ n t) - F (Ψ n t)‖ ≤ εd) {Tf : ℝ} :
    ∀ n ≤ N, (n : ℝ) * h ≤ Tf →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * Tf) * (‖Y 0 - A t₀‖ +
        Tf * (κ * (εd * Real.exp (L * h)) + (1 + κ) * (L * B * h + C * ε))) := by
  have hFo : IsOneSidedLipschitzField (fun _ : ℝ => F) L :=
    IsLipschitzField.isOneSidedLipschitzField fun _ x y => hF x y
  refine norm_projEulerDEIM_sub_le_global hF hL hB0 hT hκ hC0 hε0 (by positivity) hh hA hΦ hΦ₀
    hB hP hP0 hC hε hY fun n hn => ⟨Ψ n (t₀ + (n + 1) * h), hΨM n hn, ?_⟩
  have hab : t₀ + n * h ≤ t₀ + (n + 1) * h := by nlinarith
  have hstep : t₀ + (n + 1) * h - (t₀ + n * h) = h := by ring
  have h1 := (hΦ n hn).norm_sub_le_of_perturbed_max (hΨ n hn) hFo hεd (hG n hn)
    (t₀ + (n + 1) * h) ⟨hab, le_rfl⟩
  rw [hstep, hΨ₀ n hn, hΦ₀ n hn, sub_self, norm_zero, mul_zero, zero_add,
    max_eq_right (Real.one_le_exp (mul_nonneg hL hh))] at h1
  calc ‖Ψ n (t₀ + (n + 1) * h) - Φ n (t₀ + (n + 1) * h)‖ ≤ εd * h * Real.exp (L * h) := h1
    _ = h * (εd * Real.exp (L * h)) := by ring

/-- Sanity check: every hypothesis of `norm_projEulerDEIM_sub_le_global` is discharged for a
concrete but degenerate instance (`E = ℝ`, `F ≡ 1` with `L = 0`, `B = 1`, exact solution
`A t = t`, `T = id`, `ℳ = ℝ`, `P^∠_n = P_n = I`, step `h = 1`, iterates `Y n = n`, exact
one-step flows `Φ n t = t`); the scheme is exact here.  Genuinely oblique projectors are
exercised by the matrix examples at the end of the file. -/
example : ∀ n : ℕ, n ≤ 3 → (n : ℝ) * 1 ≤ 3 →
    ‖(n : ℝ) - (0 + n * 1)‖ ≤ Real.exp (0 * 3) * (‖((0 : ℕ) : ℝ) - 0‖ +
      3 * (1 * 0 + (1 + 1) * (0 * 1 * 1 + 1 * 0))) :=
  norm_projEulerDEIM_sub_le_global (F := fun _ => (1 : ℝ)) (L := 0) (B := 1) (T := id)
    (M := univ) (κ := 1) (Pob := fun _ => 1) (P := fun _ => 1) (C := 1) (ε := 0) (g := 0)
    (t₀ := 0) (h := 1) (N := 3) (A := fun t => t) (Y := fun n => (n : ℝ)) (Tf := 3)
    (Φ := fun _ t => t) (fun _ _ => by simp) le_rfl zero_le_one (fun _ _ _ => by simp)
    zero_le_one zero_le_one le_rfl le_rfl zero_le_one
    ⟨continuousOn_id, fun t _ => hasDerivWithinAt_id t _⟩
    (fun _ _ => ⟨continuousOn_id, fun t _ => hasDerivWithinAt_id t _⟩)
    (fun _ _ => by simp) (fun _ _ _ _ => by simp)
    (fun _ _ => IsOrthProj.one.isObliqueProj) (fun _ _ => one_ne_zero)
    (fun _ _ => ContinuousLinearMap.norm_id_le) (fun _ _ => by simp) (fun _ _ => by simp)
    (fun n _ => ⟨0 + (n + 1) * 1, mem_univ _, by simp⟩)

end EulerDEIM

end Abstract

/-! ## Matrices -/

section Matrices

open Matrix Curvature
open scoped LeanDLRA.Frobenius

variable {k l m n : Type*}

/-! ### Algebraic properties -/

section Algebra

variable [Fintype k] [DecidableEq k] [Fintype m] {U S : Matrix m k ℝ}

/-- `𝒫 U = U`. -/
theorem obliqueProj_mul_self_left (hSU : IsUnit (Sᵀ * U).det) : obliqueProj U S * U = U := by
  rw [obliqueProj, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hSU,
    Matrix.mul_one]

/-- `𝒫` fixes every matrix with columns in the range of `U`. -/
theorem obliqueProj_mul_of_mul (hSU : IsUnit (Sᵀ * U).det) (C : Matrix k n ℝ) :
    obliqueProj U S * (U * C) = U * C := by
  rw [← Matrix.mul_assoc, obliqueProj_mul_self_left hSU]

/-- `𝒫` is idempotent. -/
theorem obliqueProj_mul_self (hSU : IsUnit (Sᵀ * U).det) :
    obliqueProj U S * obliqueProj U S = obliqueProj U S := by
  have h : obliqueProj U S = U * ((Sᵀ * U)⁻¹ * Sᵀ) := Matrix.mul_assoc _ _ _
  conv_lhs => arg 2; rw [h]
  rw [obliqueProj_mul_of_mul hSU, ← h]

/-- **Interpolation property** `Sᵀ 𝒫 = Sᵀ`: `𝒫 x` agrees with `x` at the selected entries
(arXiv 2510.19518, §3.1). -/
theorem transpose_mul_obliqueProj (hSU : IsUnit (Sᵀ * U).det) :
    Sᵀ * obliqueProj U S = Sᵀ := by
  simp only [obliqueProj, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hSU, Matrix.one_mul]

/-- Interpolation property applied to a matrix: `Sᵀ (𝒫 X) = Sᵀ X`. -/
theorem transpose_mul_obliqueProj_mul (hSU : IsUnit (Sᵀ * U).det) (X : Matrix m n ℝ) :
    Sᵀ * (obliqueProj U S * X) = Sᵀ * X := by
  rw [← Matrix.mul_assoc, transpose_mul_obliqueProj hSU]

/-- **Uniqueness**: `𝒫 X` is the only matrix with columns in the range of `U` that interpolates
`X` (`Sᵀ (U C) = Sᵀ X`). -/
theorem eq_obliqueProj_mul (hSU : IsUnit (Sᵀ * U).det) {X : Matrix m n ℝ} {C : Matrix k n ℝ}
    (h : Sᵀ * (U * C) = Sᵀ * X) : U * C = obliqueProj U S * X := by
  calc U * C = U * ((Sᵀ * U)⁻¹ * (Sᵀ * U) * C) := by
        rw [Matrix.nonsing_inv_mul _ hSU, Matrix.one_mul]
    _ = U * ((Sᵀ * U)⁻¹ * (Sᵀ * (U * C))) := by simp only [Matrix.mul_assoc]
    _ = U * ((Sᵀ * U)⁻¹ * (Sᵀ * X)) := by rw [h]
    _ = obliqueProj U S * X := by simp only [obliqueProj, Matrix.mul_assoc]

/-- The oblique projector only depends on the range of `U`: `𝒫_{U R} = 𝒫_U` for invertible
`R`. -/
theorem obliqueProj_mul_right {R : Matrix k k ℝ} (hR : IsUnit R.det) :
    obliqueProj (U * R) S = obliqueProj U S := by
  simp only [obliqueProj, ← Matrix.mul_assoc, Matrix.mul_inv_rev]
  rw [Matrix.mul_assoc U R R⁻¹, Matrix.mul_nonsing_inv _ hR, Matrix.mul_one]

/-- The oblique projector only depends on the range of the selection / sketch `S`:
`𝒫_{U, S R} = 𝒫_{U, S}` for invertible `R`. -/
theorem obliqueProj_mul_right' {R : Matrix k k ℝ} (hR : IsUnit R.det) :
    obliqueProj U (S * R) = obliqueProj U S := by
  have hRt : IsUnit Rᵀ.det := by rwa [Matrix.det_transpose]
  calc obliqueProj U (S * R) = U * ((Sᵀ * U)⁻¹ * (Rᵀ⁻¹ * Rᵀ) * Sᵀ) := by
        simp only [obliqueProj, Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_inv_rev]
    _ = obliqueProj U S := by
        rw [Matrix.nonsing_inv_mul _ hRt, Matrix.mul_one, obliqueProj, Matrix.mul_assoc]

/-- The transpose of `U (SᵀU)⁻¹ Sᵀ` is `S (UᵀS)⁻¹ Uᵀ`, the right projector `P_V^∠` of
arXiv 2510.19518, eq. (12). -/
theorem obliqueProj_transpose : (obliqueProj U S)ᵀ = S * (Uᵀ * S)⁻¹ * Uᵀ := by
  simp only [obliqueProj, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_nonsing_inv, Matrix.mul_assoc]

/-- With `S = U` the oblique projector is `U (UᵀU)⁻¹ Uᵀ`, which is symmetric (and idempotent
when `UᵀU` is invertible): the orthogonal projector onto the range of `U`
(`Π_Ω = Ω (ΩᵀΩ)⁻¹ Ωᵀ` of arXiv 2410.17091, eq. (7); `P (PᵀP)⁻¹ Pᵀ` of arXiv 2607.03402,
eq. (7)). -/
theorem obliqueProj_self_transpose : (obliqueProj U U)ᵀ = obliqueProj U U :=
  obliqueProj_transpose

/-- `(𝒫)ᵀ S = S`. -/
theorem obliqueProj_transpose_mul (hSU : IsUnit (Sᵀ * U).det) : (obliqueProj U S)ᵀ * S = S := by
  calc (obliqueProj U S)ᵀ * S = (Sᵀ * obliqueProj U S)ᵀ := by
        rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    _ = S := by rw [transpose_mul_obliqueProj hSU, Matrix.transpose_transpose]

/-- `𝒫 U Uᵀ = U Uᵀ` (arXiv 2510.19518, eq. (14)). -/
theorem obliqueProj_mul_proj (hSU : IsUnit (Sᵀ * U).det) :
    obliqueProj U S * (U * Uᵀ) = U * Uᵀ :=
  obliqueProj_mul_of_mul hSU Uᵀ

/-- `(I - 𝒫)(I - U Uᵀ) = I - 𝒫` (arXiv 2510.19518, eq. (14)). -/
theorem one_sub_obliqueProj_mul [DecidableEq m] (hSU : IsUnit (Sᵀ * U).det) :
    (1 - obliqueProj U S) * (1 - U * Uᵀ) = 1 - obliqueProj U S := by
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, obliqueProj_mul_proj hSU,
    sub_self, sub_zero]

/-- `U Uᵀ 𝒫ᵀ = U Uᵀ` (the right-projector form of eq. (14) of arXiv 2510.19518). -/
theorem proj_mul_obliqueProj_transpose (hSU : IsUnit (Sᵀ * U).det) :
    U * Uᵀ * (obliqueProj U S)ᵀ = U * Uᵀ := by
  calc U * Uᵀ * (obliqueProj U S)ᵀ = (obliqueProj U S * (U * Uᵀ))ᵀ := by
        rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    _ = U * Uᵀ := by
        rw [obliqueProj_mul_proj hSU, Matrix.transpose_mul, Matrix.transpose_transpose]

/-- **Equivalence with the orthogonal projection** (one-sided form of Proposition 4.4 of
arXiv 2607.03402): `𝒫 X = U Uᵀ X` iff the normal component `(I - U Uᵀ) X` is invisible to the
selection / sketch, `Sᵀ (X - U Uᵀ X) = 0`. -/
theorem obliqueProj_mul_eq_iff (hSU : IsUnit (Sᵀ * U).det) (X : Matrix m n ℝ) :
    obliqueProj U S * X = U * Uᵀ * X ↔ Sᵀ * (X - U * Uᵀ * X) = 0 := by
  constructor
  · intro h
    rw [Matrix.mul_sub, ← h, transpose_mul_obliqueProj_mul hSU, sub_self]
  · intro h
    have h' : Sᵀ * (U * (Uᵀ * X)) = Sᵀ * X := by
      rw [Matrix.mul_sub, sub_eq_zero] at h
      rw [h, Matrix.mul_assoc U Uᵀ X]
    rw [← eq_obliqueProj_mul hSU h', Matrix.mul_assoc]

variable (hU : Uᵀ * U = 1)
include hU

/-- `U Uᵀ 𝒫 = 𝒫`: the range of `𝒫` is the range of `U`. -/
theorem proj_mul_obliqueProj : U * Uᵀ * obliqueProj U S = obliqueProj U S := by
  simp only [obliqueProj, ← Matrix.mul_assoc]
  rw [Matrix.mul_assoc U Uᵀ U, hU, Matrix.mul_one]

/-- For orthonormal `U`, `U (UᵀU)⁻¹ Uᵀ = U Uᵀ`. -/
theorem obliqueProj_self_of_orthonormal : obliqueProj U U = U * Uᵀ := by
  rw [obliqueProj, hU, inv_one, Matrix.mul_one]

/-- **Orthogonal sketch DLRA is DLRA** (arXiv 2607.03402, eqs. (7)–(8)): for any basis
`P = U R` of the range of an orthonormal `U` (`R` invertible), `P (PᵀP)⁻¹ Pᵀ = U Uᵀ`, so the
tangent projector written in sketch-orthogonal (non-orthonormal) factors is the usual one. -/
theorem obliqueProj_self_mul_right {R : Matrix k k ℝ} (hR : IsUnit R.det) :
    obliqueProj (U * R) (U * R) = U * Uᵀ := by
  rw [obliqueProj_mul_right hR, obliqueProj_mul_right' hR, obliqueProj_self_of_orthonormal hU]

/-- `𝒫ᵀ U Uᵀ = 𝒫ᵀ`. -/
theorem obliqueProj_transpose_mul_proj :
    (obliqueProj U S)ᵀ * (U * Uᵀ) = (obliqueProj U S)ᵀ := by
  calc (obliqueProj U S)ᵀ * (U * Uᵀ) = (U * Uᵀ * obliqueProj U S)ᵀ := by
        rw [Matrix.transpose_mul (U * Uᵀ), Matrix.transpose_mul U, Matrix.transpose_transpose]
    _ = (obliqueProj U S)ᵀ := by rw [proj_mul_obliqueProj hU]

end Algebra

/-! ### Sketched projectors (arXiv 2607.03402) -/

section Sketch

variable [Fintype k] [DecidableEq k] [Fintype m] {p : Type*} [Fintype p]

omit [Fintype k] [DecidableEq k] in
/-- With `S = Θᵀ Θ U` the matrix `Sᵀ U` is the Gram matrix `(ΘU)ᵀ (ΘU)` of the sketched basis. -/
theorem sketch_transpose_mul (Θ : Matrix p m ℝ) (U : Matrix m k ℝ) :
    (Θᵀ * Θ * U)ᵀ * U = (Θ * U)ᵀ * (Θ * U) := by
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- **Lemma 4.2 of arXiv 2607.03402** (compact form): for a sketch-orthonormal basis `P`
(`(ΘP)ᵀ(ΘP) = I`, so `(ΘP)⁺ = (ΘP)ᵀ`) the sketched oblique projector `P (ΘP)⁺ Θ` is
`P Pᵀ Θᵀ Θ = obliqueProj P (Θᵀ Θ P)`. -/
theorem obliqueProj_sketch_eq {Θ : Matrix p m ℝ} {P : Matrix m k ℝ}
    (hP : (Θ * P)ᵀ * (Θ * P) = 1) :
    obliqueProj P (Θᵀ * Θ * P) = P * Pᵀ * Θᵀ * Θ := by
  rw [obliqueProj, sketch_transpose_mul, hP, inv_one, Matrix.mul_one]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- In sketch coordinates the sketched oblique projector is the orthogonal projector of the
sketched basis: `Θ 𝒫 = (ΘP)(ΘP)ᵀ Θ` (arXiv 2607.03402, after Lemma 4.2). -/
theorem sketch_mul_obliqueProj {Θ : Matrix p m ℝ} {P : Matrix m k ℝ}
    (hP : (Θ * P)ᵀ * (Θ * P) = 1) :
    Θ * obliqueProj P (Θᵀ * Θ * P) = Θ * P * (Θ * P)ᵀ * Θ := by
  rw [obliqueProj_sketch_eq hP]
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

/-- **Sketched Galerkin condition**: the residual of the sketched oblique projection is
orthogonal to the sketched basis in the sketched inner product,
`(ΘU)ᵀ Θ (X - 𝒫 X) = 0` (arXiv 2607.03402, eq. (10), one-sided form). -/
theorem sketch_galerkin {Θ : Matrix p m ℝ} {U : Matrix m k ℝ}
    (hG : IsUnit ((Θ * U)ᵀ * (Θ * U)).det) (X : Matrix m n ℝ) :
    (Θ * U)ᵀ * (Θ * (X - obliqueProj U (Θᵀ * Θ * U) * X)) = 0 := by
  have hSU : IsUnit ((Θᵀ * Θ * U)ᵀ * U).det := by rwa [sketch_transpose_mul]
  have h : (Θ * U)ᵀ * (Θ * (X - obliqueProj U (Θᵀ * Θ * U) * X)) =
      (Θᵀ * Θ * U)ᵀ * (X - obliqueProj U (Θᵀ * Θ * U) * X) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [h, Matrix.mul_sub, transpose_mul_obliqueProj_mul hSU, sub_self]

end Sketch

/-! ### Norm bounds -/

section Norms

variable [Fintype k] [DecidableEq k] [Fintype l] [DecidableEq l] [Fintype m] [Fintype n]
  {U S : Matrix m k ℝ}

/-- `‖U (SᵀU)⁻¹ Sᵀ‖₂ ≤ ‖(SᵀU)⁻¹‖₂ ‖S‖₂` for orthonormal `U`. -/
theorem specNorm_obliqueProj_le [DecidableEq m] (hU : Uᵀ * U = 1) :
    specNorm (obliqueProj U S) ≤ specNorm (Sᵀ * U)⁻¹ * specNorm S := by
  have h1 := specNorm_mul_le (U * (Sᵀ * U)⁻¹) Sᵀ
  have h2 := specNorm_mul_le U (Sᵀ * U)⁻¹
  have hU1 := specNorm_le_one_of_orthonormal hU
  rw [specNorm_transpose] at h1
  have := specNorm_nonneg (Sᵀ * U)⁻¹
  have := specNorm_nonneg S
  have := specNorm_nonneg U
  calc specNorm (obliqueProj U S) ≤ specNorm (U * (Sᵀ * U)⁻¹) * specNorm S := h1
    _ ≤ specNorm U * specNorm (Sᵀ * U)⁻¹ * specNorm S := by gcongr
    _ ≤ 1 * specNorm (Sᵀ * U)⁻¹ * specNorm S := by gcongr
    _ = specNorm (Sᵀ * U)⁻¹ * specNorm S := by ring

/-- For a selection matrix (more generally `Sᵀ S = I`), `‖U (SᵀU)⁻¹ Sᵀ‖₂ ≤ ‖(SᵀU)⁻¹‖₂`. -/
theorem specNorm_obliqueProj_le_of_orthonormal [DecidableEq m] (hU : Uᵀ * U = 1)
    (hS : Sᵀ * S = 1) : specNorm (obliqueProj U S) ≤ specNorm (Sᵀ * U)⁻¹ := by
  have h := specNorm_obliqueProj_le (S := S) hU
  have hS1 := specNorm_le_one_of_orthonormal hS
  have := specNorm_nonneg (Sᵀ * U)⁻¹
  nlinarith

/-- The operator norm (induced by the Frobenius norm) of the left oblique projector is at most
the spectral norm of `𝒫`. -/
theorem opNorm_leftOblique_le [DecidableEq m] (U S : Matrix m k ℝ) :
    ‖(leftOblique U S : Matrix m n ℝ →L[ℝ] Matrix m n ℝ)‖ ≤ specNorm (obliqueProj U S) :=
  ContinuousLinearMap.opNorm_le_bound _ (specNorm_nonneg _) fun X => frob_mul_le _ X

/-- The operator norm of the right oblique projector is at most the spectral norm of `𝒫_V`. -/
theorem opNorm_rightOblique_le [DecidableEq n] (V S : Matrix n l ℝ) :
    ‖(rightOblique V S : Matrix m n ℝ →L[ℝ] Matrix m n ℝ)‖ ≤ specNorm (obliqueProj V S) :=
  ContinuousLinearMap.opNorm_le_bound _ (specNorm_nonneg _) fun X => by
    calc ‖rightOblique V S X‖ = ‖X * (obliqueProj V S)ᵀ‖ := rfl
      _ ≤ ‖X‖ * specNorm (obliqueProj V S)ᵀ := frob_mul_le' _ _
      _ = specNorm (obliqueProj V S) * ‖X‖ := by rw [specNorm_transpose, mul_comm]

/-- The left oblique projector is an oblique projector onto `X ↦ U Uᵀ X`. -/
theorem isObliqueProj_leftOblique (hU : Uᵀ * U = 1) (hSU : IsUnit (Sᵀ * U).det) :
    IsObliqueProj (leftOblique U S : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (leftProj U) where
  orth := isOrthProj_leftProj hU
  fix X := by
    change obliqueProj U S * (U * Uᵀ * X) = U * Uᵀ * X
    rw [← Matrix.mul_assoc, obliqueProj_mul_proj hSU]
  range X := by
    change U * Uᵀ * (obliqueProj U S * X) = obliqueProj U S * X
    rw [← Matrix.mul_assoc, proj_mul_obliqueProj hU]

/-- The right oblique projector is an oblique projector onto `X ↦ X V Vᵀ`. -/
theorem isObliqueProj_rightOblique {V S : Matrix n l ℝ} (hV : Vᵀ * V = 1)
    (hSV : IsUnit (Sᵀ * V).det) :
    IsObliqueProj (rightOblique V S : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (rightProj V) where
  orth := isOrthProj_rightProj hV
  fix X := by
    change X * (V * Vᵀ) * (obliqueProj V S)ᵀ = X * (V * Vᵀ)
    rw [Matrix.mul_assoc, proj_mul_obliqueProj_transpose hSV]
  range X := by
    change X * (obliqueProj V S)ᵀ * (V * Vᵀ) = X * (obliqueProj V S)ᵀ
    rw [Matrix.mul_assoc, obliqueProj_transpose_mul_proj hV]

/-- `X ↦ U Uᵀ X` is nonzero on `m × n` matrices if `U` has orthonormal columns and there is at
least one column. -/
theorem leftProj_ne_zero [Nonempty k] [Nonempty n] (hU : Uᵀ * U = 1) :
    (leftProj U : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) ≠ 0 := by
  intro h
  set J : Matrix k n ℝ := Matrix.of fun _ _ => 1
  have h1 : leftProj U (U * J) = U * J := leftProj_mul_left hU J
  rw [h] at h1
  have h1' : (0 : Matrix m n ℝ) = U * J := h1
  have h2 : J = 0 := by rw [← Matrix.one_mul J, ← hU, Matrix.mul_assoc, ← h1', Matrix.mul_zero]
  have h3 := congrFun (congrFun h2 (Classical.arbitrary k)) (Classical.arbitrary n)
  simp [J] at h3

/-- `X ↦ X V Vᵀ` is nonzero on `m × n` matrices if `V` has orthonormal columns and there is at
least one row. -/
theorem rightProj_ne_zero {V : Matrix n l ℝ} [Nonempty l] [Nonempty m] (hV : Vᵀ * V = 1) :
    (rightProj V : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) ≠ 0 := by
  intro h
  set J : Matrix m l ℝ := Matrix.of fun _ _ => 1
  have h1 : rightProj V (J * Vᵀ) = J * Vᵀ := rightProj_mul_transpose hV J
  rw [h] at h1
  have h1' : (0 : Matrix m n ℝ) = J * Vᵀ := h1
  have h2 : J = 0 := by rw [← Matrix.mul_one J, ← hV, ← Matrix.mul_assoc, ← h1', Matrix.zero_mul]
  have h3 := congrFun (congrFun h2 (Classical.arbitrary m)) (Classical.arbitrary l)
  simp [J] at h3

/-- **Quasi-optimality of the interpolatory projection** (DEIM error bound): for orthonormal `U`,
`‖X - 𝒫 X‖_F ≤ ‖𝒫‖₂ ‖X - U Uᵀ X‖_F`. -/
theorem norm_sub_obliqueProj_mul_le [Nonempty k] [DecidableEq m] (hU : Uᵀ * U = 1)
    (hSU : IsUnit (Sᵀ * U).det) (X : Matrix m n ℝ) :
    ‖X - obliqueProj U S * X‖ ≤ specNorm (obliqueProj U S) * ‖X - U * Uᵀ * X‖ := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have hX : X = 0 := Matrix.ext fun _ j => isEmptyElim j
    simp [hX]
  · calc ‖X - obliqueProj U S * X‖ = ‖X - leftOblique U S X‖ := rfl
      _ ≤ ‖(leftOblique U S : Matrix m n ℝ →L[ℝ] Matrix m n ℝ)‖ * ‖X - leftProj U X‖ :=
        (isObliqueProj_leftOblique hU hSU).norm_sub_le_opNorm (leftProj_ne_zero hU) X
      _ ≤ specNorm (obliqueProj U S) * ‖X - U * Uᵀ * X‖ :=
        mul_le_mul_of_nonneg_right (opNorm_leftOblique_le U S) (norm_nonneg _)

/-- **DEIM error bound** for a general selection / sketch `S`:
`‖X - U (SᵀU)⁻¹ Sᵀ X‖_F ≤ ‖(SᵀU)⁻¹‖₂ ‖S‖₂ ‖X - U Uᵀ X‖_F`. -/
theorem norm_sub_obliqueProj_mul_le' [Nonempty k] (hU : Uᵀ * U = 1)
    (hSU : IsUnit (Sᵀ * U).det) (X : Matrix m n ℝ) :
    ‖X - obliqueProj U S * X‖ ≤ specNorm (Sᵀ * U)⁻¹ * specNorm S * ‖X - U * Uᵀ * X‖ := by
  classical
  exact (norm_sub_obliqueProj_mul_le hU hSU X).trans
    (mul_le_mul_of_nonneg_right (specNorm_obliqueProj_le hU) (norm_nonneg _))

/-- **DEIM error bound** (Chaturantabut–Sorensen; arXiv 2510.19518, eq. (6)): for a selection
matrix `S` (`Sᵀ S = I`) and orthonormal `U`,
`‖X - U (SᵀU)⁻¹ Sᵀ X‖_F ≤ ‖(SᵀU)⁻¹‖₂ ‖X - U Uᵀ X‖_F`. -/
theorem norm_sub_obliqueProj_mul_le_of_orthonormal [Nonempty k] (hU : Uᵀ * U = 1)
    (hS : Sᵀ * S = 1) (hSU : IsUnit (Sᵀ * U).det) (X : Matrix m n ℝ) :
    ‖X - obliqueProj U S * X‖ ≤ specNorm (Sᵀ * U)⁻¹ * ‖X - U * Uᵀ * X‖ := by
  classical
  exact (norm_sub_obliqueProj_mul_le hU hSU X).trans
    (mul_le_mul_of_nonneg_right (specNorm_obliqueProj_le_of_orthonormal hU hS) (norm_nonneg _))

/-- Purely Frobenius form of the DEIM bound (no condition on the number of columns):
`‖(I - 𝒫) X‖_F ≤ (1 + ‖U‖_F ‖(SᵀU)⁻¹‖_F ‖S‖_F) ‖(I - U Uᵀ) X‖_F`. -/
theorem norm_one_sub_obliqueProj_mul_le [DecidableEq m] (hU : Uᵀ * U = 1)
    (hSU : IsUnit (Sᵀ * U).det) (X : Matrix m n ℝ) :
    ‖(1 - obliqueProj U S) * X‖ ≤ (1 + ‖U‖ * ‖(Sᵀ * U)⁻¹‖ * ‖S‖) * ‖(1 - U * Uᵀ) * X‖ := by
  have h := (isObliqueProj_leftOblique (n := n) hU hSU).norm_sub_le_one_add X
  have hP : ‖(leftOblique U S : Matrix m n ℝ →L[ℝ] Matrix m n ℝ)‖ ≤
      ‖U‖ * ‖(Sᵀ * U)⁻¹‖ * ‖S‖ := by
    refine (opNorm_leftOblique_le U S).trans ((specNorm_le_frob _).trans ?_)
    calc ‖obliqueProj U S‖ ≤ ‖U * (Sᵀ * U)⁻¹‖ * ‖Sᵀ‖ := Frobenius.norm_mul_le _ _
      _ ≤ ‖U‖ * ‖(Sᵀ * U)⁻¹‖ * ‖S‖ := by
        rw [Frobenius.norm_transpose]
        gcongr
        exact Frobenius.norm_mul_le _ _
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul, Matrix.one_mul]
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

end Norms

/-! ### The oblique tangent-space projector -/

section Tangent

variable [Fintype k] [DecidableEq k] [Fintype l] [DecidableEq l] [Fintype m] [Fintype n]
  {U SU : Matrix m k ℝ} {V SV : Matrix n l ℝ}

/- `obliqueTangentProj`, `obliqueTangentProj_apply` and `sketchTangentProj` are defined in
`LeanDLRA/FixedRank/Defs.lean`. -/

/-- `P^∠(Y)` is an oblique projector onto the orthogonal tangent projector `P(Y)`:
`P^∠(Y) P(Y) = P(Y)`, `P(Y) P^∠(Y) = P^∠(Y)` (arXiv 2510.19518, §3.1; Lemma 15 for Tucker). -/
theorem isObliqueProj_obliqueTangentProj (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hSU : IsUnit (SUᵀ * U).det) (hSV : IsUnit (SVᵀ * V).det) :
    IsObliqueProj (obliqueTangentProj U SU V SV) (tangentProj U V) :=
  (isObliqueProj_leftOblique hU hSU).tangent (isObliqueProj_rightOblique hV hSV)
    (leftProj_rightProj_comm U V) (fun _ => (Matrix.mul_assoc _ _ _).symm)
    (fun _ => Matrix.mul_assoc _ _ _)

/-- `P^∠(Y)` is idempotent. -/
theorem obliqueTangentProj_idem (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hSU : IsUnit (SUᵀ * U).det) (hSV : IsUnit (SVᵀ * V).det) (Z : Matrix m n ℝ) :
    obliqueTangentProj U SU V SV (obliqueTangentProj U SU V SV Z) =
      obliqueTangentProj U SU V SV Z :=
  (isObliqueProj_obliqueTangentProj hU hV hSU hSV).idem Z

/-- **Interpolation property** of the oblique tangent projector:
`S_Uᵀ P^∠(Y)[Z] S_V = S_Uᵀ Z S_V` (arXiv 2510.19518, §3.1). -/
theorem transpose_mul_obliqueTangentProj_mul (hSU : IsUnit (SUᵀ * U).det)
    (hSV : IsUnit (SVᵀ * V).det) (Z : Matrix m n ℝ) :
    SUᵀ * obliqueTangentProj U SU V SV Z * SV = SUᵀ * Z * SV := by
  have h1 : ∀ X : Matrix m l ℝ, SUᵀ * (obliqueProj U SU * X) = SUᵀ * X :=
    transpose_mul_obliqueProj_mul hSU
  have h2 : ∀ X : Matrix m n ℝ, X * ((obliqueProj V SV)ᵀ * SV) = X * SV := fun X => by
    rw [obliqueProj_transpose_mul hSV]
  simp only [obliqueTangentProj_apply, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add,
    Matrix.mul_sub, Matrix.mul_assoc, h2, h1]
  abel

/-- `Z - P^∠(Y) Z = (I - 𝒫_U) (Z - P(Y) Z) (I - 𝒫_Vᵀ)` (proof of Lemma 4 of
arXiv 2510.19518). -/
theorem sub_obliqueTangentProj_eq [DecidableEq m] [DecidableEq n] (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (hSU : IsUnit (SUᵀ * U).det) (hSV : IsUnit (SVᵀ * V).det)
    (Z : Matrix m n ℝ) :
    Z - obliqueTangentProj U SU V SV Z =
      (1 - obliqueProj U SU) * (Z - tangentProj U V Z) * (1 - (obliqueProj V SV)ᵀ) := by
  rw [obliqueTangentProj, IsObliqueProj.sub_tangent_eq (isObliqueProj_leftOblique hU hSU)
    (isObliqueProj_rightOblique hV hSV) (fun X => Matrix.mul_assoc _ _ _), ← tangentProj]
  set W := Z - tangentProj U V Z
  change (W - W * (obliqueProj V SV)ᵀ) - obliqueProj U SU * (W - W * (obliqueProj V SV)ᵀ) = _
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  abel

/-- **Lemma 4 of arXiv 2510.19518** (spectral-norm form):
`‖Z - P^∠(Y) Z‖_F ≤ ‖𝒫_U‖₂ ‖𝒫_V‖₂ ‖Z - P(Y) Z‖_F`. -/
theorem norm_sub_obliqueTangentProj_le [Nonempty k] [Nonempty l] [DecidableEq m]
    [DecidableEq n] (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hSU : IsUnit (SUᵀ * U).det)
    (hSV : IsUnit (SVᵀ * V).det) (Z : Matrix m n ℝ) :
    ‖Z - obliqueTangentProj U SU V SV Z‖ ≤
      specNorm (obliqueProj U SU) * specNorm (obliqueProj V SV) * ‖Z - tangentProj U V Z‖ := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have hZ : Z = 0 := Matrix.ext fun _ j => isEmptyElim j
    simp [hZ]
  rcases isEmpty_or_nonempty m with hm | hm
  · have hZ : Z = 0 := Matrix.ext fun i _ => isEmptyElim i
    simp [hZ]
  refine ((isObliqueProj_leftOblique hU hSU).norm_sub_tangent_le_opNorm
    (isObliqueProj_rightOblique hV hSV) (fun X => Matrix.mul_assoc _ _ _)
    (leftProj_ne_zero hU) (rightProj_ne_zero hV) Z).trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul (opNorm_leftOblique_le _ _)
    (opNorm_rightOblique_le _ _) (norm_nonneg _) (specNorm_nonneg _)) (norm_nonneg _)

/-- **Lemma 4 of arXiv 2510.19518** for selection matrices (`S_Uᵀ S_U = I`, `S_Vᵀ S_V = I`):
`‖Z - P^∠(Y) Z‖_F ≤ ‖(S_Uᵀ U)⁻¹‖₂ ‖(S_Vᵀ V)⁻¹‖₂ ‖Z - P(Y) Z‖_F`, i.e. the constant
`C_{m,r} C_{n,r}`. -/
theorem norm_sub_obliqueTangentProj_le_of_orthonormal [Nonempty k] [Nonempty l]
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hSU' : SUᵀ * SU = 1) (hSV' : SVᵀ * SV = 1)
    (hSU : IsUnit (SUᵀ * U).det) (hSV : IsUnit (SVᵀ * V).det) (Z : Matrix m n ℝ) :
    ‖Z - obliqueTangentProj U SU V SV Z‖ ≤
      specNorm (SUᵀ * U)⁻¹ * specNorm (SVᵀ * V)⁻¹ * ‖Z - tangentProj U V Z‖ := by
  classical
  exact (norm_sub_obliqueTangentProj_le hU hV hSU hSV Z).trans <| mul_le_mul_of_nonneg_right
    (mul_le_mul (specNorm_obliqueProj_le_of_orthonormal hU hSU')
      (specNorm_obliqueProj_le_of_orthonormal hV hSV') (specNorm_nonneg _)
      ((specNorm_nonneg _).trans (specNorm_obliqueProj_le_of_orthonormal hU hSU')))
    (norm_nonneg _)

/-- **Lemma 4 of arXiv 2510.19518** for general selections / sketches:
`‖Z - P^∠(Y) Z‖_F ≤ (‖(S_UᵀU)⁻¹‖₂ ‖S_U‖₂) (‖(S_VᵀV)⁻¹‖₂ ‖S_V‖₂) ‖Z - P(Y) Z‖_F`. -/
theorem norm_sub_obliqueTangentProj_le' [Nonempty k] [Nonempty l]
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hSU : IsUnit (SUᵀ * U).det)
    (hSV : IsUnit (SVᵀ * V).det) (Z : Matrix m n ℝ) :
    ‖Z - obliqueTangentProj U SU V SV Z‖ ≤
      specNorm (SUᵀ * U)⁻¹ * specNorm SU * (specNorm (SVᵀ * V)⁻¹ * specNorm SV) *
        ‖Z - tangentProj U V Z‖ := by
  classical
  exact (norm_sub_obliqueTangentProj_le hU hV hSU hSV Z).trans <| mul_le_mul_of_nonneg_right
    (mul_le_mul (specNorm_obliqueProj_le hU) (specNorm_obliqueProj_le hV) (specNorm_nonneg _)
      ((specNorm_nonneg _).trans (specNorm_obliqueProj_le hU)))
    (norm_nonneg _)

/-- **Error of the interpolatory projected vector field** (arXiv 2510.19518, Corollary 9 /
Lemma 11): if the normal component of `F` at `Y` is `ε`-small,
`‖(I - U Uᵀ) F (I - V Vᵀ)‖_F ≤ ε`, then `‖F - P^∠(Y) F‖_F ≤ ‖(S_UᵀU)⁻¹‖₂ ‖(S_VᵀV)⁻¹‖₂ ε` for
selection matrices. -/
theorem norm_sub_obliqueTangentProj_le_of_normal [Nonempty k] [Nonempty l] [DecidableEq m]
    [DecidableEq n] (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hSU' : SUᵀ * SU = 1)
    (hSV' : SVᵀ * SV = 1) (hSU : IsUnit (SUᵀ * U).det) (hSV : IsUnit (SVᵀ * V).det)
    {F : Matrix m n ℝ} {ε : ℝ} (hF : ‖(1 - U * Uᵀ) * F * (1 - V * Vᵀ)‖ ≤ ε) :
    ‖F - obliqueTangentProj U SU V SV F‖ ≤ specNorm (SUᵀ * U)⁻¹ * specNorm (SVᵀ * V)⁻¹ * ε := by
  have hN : F - tangentProj U V F = (1 - U * Uᵀ) * F * (1 - V * Vᵀ) := by
    rw [sub_eq_iff_eq_add, add_comm]; exact (tangentProj_add_normal U V F).symm
  refine (norm_sub_obliqueTangentProj_le_of_orthonormal hU hV hSU' hSV' hSU hSV F).trans ?_
  rw [hN]
  exact mul_le_mul_of_nonneg_left hF (mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _))

/-- **Lemma 4.2 of arXiv 2607.03402** (explicit form): for sketch-orthonormal bases `P`, `W`
(`(ΘP)ᵀ(ΘP) = I`, `(ΩW)ᵀ(ΩW) = I`), the oblique sketch tangent projector is
`P^{Θ,Ω}_Y Z = P Pᵀ Θᵀ Θ Z - P Pᵀ Θᵀ Θ Z Ωᵀ Ω W Wᵀ + Z Ωᵀ Ω W Wᵀ`. -/
theorem obliqueTangentProj_sketch_eq {p q : Type*} [Fintype p] [Fintype q] {Θ : Matrix p m ℝ}
    {Ω : Matrix q n ℝ} {P : Matrix m k ℝ} {W : Matrix n l ℝ} (hP : (Θ * P)ᵀ * (Θ * P) = 1)
    (hW : (Ω * W)ᵀ * (Ω * W) = 1) (Z : Matrix m n ℝ) :
    obliqueTangentProj P (Θᵀ * Θ * P) W (Ωᵀ * Ω * W) Z =
      P * Pᵀ * Θᵀ * Θ * Z - P * Pᵀ * Θᵀ * Θ * Z * Ωᵀ * Ω * W * Wᵀ + Z * Ωᵀ * Ω * W * Wᵀ := by
  rw [obliqueTangentProj_apply, obliqueProj_sketch_eq hP, obliqueProj_sketch_eq hW]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  abel

/-- **Sketch coordinates** (arXiv 2607.03402, after Lemma 4.2): the oblique sketch tangent
projector becomes the *orthogonal* tangent projector at the sketched point `Θ Y Ωᵀ`:
`Θ (P^{Θ,Ω}_Y Z) Ωᵀ = P_{ΘYΩᵀ}(Θ Z Ωᵀ)` with sketched orthonormal factors `ΘP`, `ΩW`. -/
theorem sketch_obliqueTangentProj {p q : Type*} [Fintype p] [Fintype q] {Θ : Matrix p m ℝ}
    {Ω : Matrix q n ℝ} {P : Matrix m k ℝ} {W : Matrix n l ℝ} (hP : (Θ * P)ᵀ * (Θ * P) = 1)
    (hW : (Ω * W)ᵀ * (Ω * W) = 1) (Z : Matrix m n ℝ) :
    Θ * obliqueTangentProj P (Θᵀ * Θ * P) W (Ωᵀ * Ω * W) Z * Ωᵀ =
      tangentProj (Θ * P) (Ω * W) (Θ * Z * Ωᵀ) := by
  rw [obliqueTangentProj_sketch_eq hP hW, tangentProj_apply]
  simp only [Matrix.transpose_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul,
    Matrix.sub_mul, Matrix.mul_assoc]
  abel

/-! #### Matrix form of Proposition 4.4 and of eq. (15) of arXiv 2607.03402 -/

/-- The oblique tangent projector only depends on the ranges of the bases:
`P^∠` built from `(U R, V R')` equals `P^∠` built from `(U, V)` for invertible `R`, `R'`. -/
theorem obliqueTangentProj_mul_right {R : Matrix k k ℝ} {R' : Matrix l l ℝ} (hR : IsUnit R.det)
    (hR' : IsUnit R'.det) :
    obliqueTangentProj (U * R) SU (V * R') SV = obliqueTangentProj U SU V SV := by
  simp only [obliqueTangentProj, leftOblique, rightOblique, obliqueProj_mul_right hR,
    obliqueProj_mul_right hR']

/-- If `P = U R` is sketch-orthonormal (`(ΘP)ᵀ(ΘP) = I`), then `R` is invertible and so is
`(Θᵀ Θ P)ᵀ U`, the matrix `Sᵀ U` of the sketched oblique projector `𝒫 = U (SᵀU)⁻¹ Sᵀ`. -/
theorem isUnit_det_of_sketch_orthonormal {p : Type*} [Fintype p] {Θ : Matrix p m ℝ}
    {R : Matrix k k ℝ} (hP : (Θ * (U * R))ᵀ * (Θ * (U * R)) = 1) :
    IsUnit R.det ∧ IsUnit ((Θᵀ * Θ * (U * R))ᵀ * U).det := by
  have h : (Θᵀ * Θ * (U * R))ᵀ * U * R = (Θ * (U * R))ᵀ * (Θ * (U * R)) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [hP] at h
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at hd
  exact ⟨IsUnit.of_mul_eq_one_right _ hd, IsUnit.of_mul_eq_one _ hd⟩

/-- The two-sided sketch `Z ↦ Θ Z Ωᵀ` as a continuous linear map (Frobenius norms). -/
noncomputable def sketchCLM {p q : Type*} [Fintype p] [Fintype q] (Θ : Matrix p m ℝ)
    (Ω : Matrix q n ℝ) : Matrix m n ℝ →L[ℝ] Matrix p q ℝ :=
  (Frobenius.rightMulCLM Ωᵀ).comp (Frobenius.leftMulCLM Θ)

/-- `sketchCLM Θ Ω Z = Θ Z Ωᵀ`. -/
@[simp] lemma sketchCLM_apply {p q : Type*} [Fintype p] [Fintype q] (Θ : Matrix p m ℝ)
    (Ω : Matrix q n ℝ) (Z : Matrix m n ℝ) : sketchCLM Θ Ω Z = Θ * Z * Ωᵀ := rfl

/-- The two-sided sketch is the sandwich map `Z ↦ Θ Z Ωᵀ` of the Frobenius layer. -/
theorem sketchCLM_eq_sandwichCLM {p q : Type*} [Fintype p] [Fintype q] (Θ : Matrix p m ℝ)
    (Ω : Matrix q n ℝ) : sketchCLM Θ Ω = Frobenius.sandwichCLM Θ Ωᵀ :=
  ContinuousLinearMap.ext fun _ => rfl

/-- **Setting of Lemma 4.2 and Proposition 4.4 of arXiv 2607.03402.**  Let `U`, `V` be
orthonormal and `P = U R`, `W = V R'` sketch-orthonormal bases of the same ranges
(`(ΘP)ᵀ(ΘP) = I`, `(ΩW)ᵀ(ΩW) = I`; `R`, `R'` are then automatically invertible).  Then the
oblique sketch tangent projector `P^{Θ,Ω}_Y` is an oblique projector onto the orthogonal tangent
projector `P_Y = tangentProj U V` (`T_Y M^{Θ,Ω}_r = T_Y M_r`). -/
theorem isObliqueProj_sketchTangentProj {p q : Type*} [Fintype p] [Fintype q]
    {Θ : Matrix p m ℝ} {Ω : Matrix q n ℝ} {R : Matrix k k ℝ} {R' : Matrix l l ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hP : (Θ * (U * R))ᵀ * (Θ * (U * R)) = 1)
    (hW : (Ω * (V * R'))ᵀ * (Ω * (V * R')) = 1) :
    IsObliqueProj (sketchTangentProj Θ Ω (U * R) (V * R')) (tangentProj U V) := by
  obtain ⟨hR, hSU⟩ := isUnit_det_of_sketch_orthonormal hP
  obtain ⟨hR', hSV⟩ := isUnit_det_of_sketch_orthonormal hW
  rw [sketchTangentProj, obliqueTangentProj_mul_right hR hR']
  exact isObliqueProj_obliqueTangentProj hU hV hSU hSV

/-- **Proposition 4.4 of arXiv 2607.03402** (matrix form; deterministic, as in the paper).  In
the setting of `isObliqueProj_sketchTangentProj`, let `δ = P^{Θ,Ω}_Y Z - P_Y Z`.  If the sketch
does not annihilate this single tangent vector (`Θ δ Ωᵀ = 0 → δ = 0`; for `Z = F(Y)` and
`Ẏ = P^{Θ,Ω}_Y F(Y)`, `δ = Ẏ - P_Y F(Y)` is the `Z` of Prop. 4.4, and the hypothesis that `Θ`,
`Ω` embed its column and row spaces gives `‖Θ δ Ωᵀ‖ ≥ (1 - ϵ) ‖δ‖`), then
`P^{Θ,Ω}_Y Z = P_Y Z` iff condition (14) holds:
`⟪Θ (Z - P_Y Z) Ωᵀ, Θ δY Ωᵀ⟫ = 0` for every tangent `δY`.  No injectivity of `Θ`, `Ω` (i.e. no
`ℓ ≥ m, n`) is required; see the example at the end of the file for `ℓ = 1 < m = n = 2`. -/
theorem sketchTangentProj_eq_iff {p q : Type*} [Fintype p] [Fintype q] {Θ : Matrix p m ℝ}
    {Ω : Matrix q n ℝ} {R : Matrix k k ℝ} {R' : Matrix l l ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1)
    (hP : (Θ * (U * R))ᵀ * (Θ * (U * R)) = 1) (hW : (Ω * (V * R'))ᵀ * (Ω * (V * R')) = 1)
    (Z : Matrix m n ℝ)
    (hZ : Θ * (sketchTangentProj Θ Ω (U * R) (V * R') Z - tangentProj U V Z) * Ωᵀ = 0 →
      sketchTangentProj Θ Ω (U * R) (V * R') Z - tangentProj U V Z = 0) :
    sketchTangentProj Θ Ω (U * R) (V * R') Z = tangentProj U V Z ↔
      ∀ δ, tangentProj U V δ = δ → ⟪Θ * (Z - tangentProj U V Z) * Ωᵀ, Θ * δ * Ωᵀ⟫ = 0 :=
  (isObliqueProj_sketchTangentProj hU hV hP hW).eq_iff_of_sketch (σ := sketchCLM Θ Ω)
    (isOrthProj_tangentProj hP hW) (sketch_obliqueTangentProj hP hW) Z hZ

/-- **Quantitative form of eq. (15) of arXiv 2607.03402** (matrix form; deterministic).  In the
setting of `isObliqueProj_sketchTangentProj`, with `N = Z - P_Y Z` and
`δ = P^{Θ,Ω}_Y Z - P_Y Z`, assume the lower embedding `(1 - ε) ‖δ‖_F ≤ ‖Θ δ Ωᵀ‖_F` and the
oblique-residual bound `|⟪Θ N Ωᵀ, Θ δ Ωᵀ⟫| ≤ η ‖N‖_F ‖δ‖_F` at these two matrices only.  Then
`‖P^{Θ,Ω}_Y Z - P_Y Z‖_F ≤ η / (1 - ε)² ‖Z - P_Y Z‖_F`.  (Corollary 2.3 would give such
bounds with `η = 2ε + ε²` for matrices fixed before the draw of `Θ`, `Ω` and of low rank; `δ`
depends on the draw and `N` need not have low rank, cf. Remarks 4.5 and 4.6, so the hypotheses
are kept on the realized sketch.) -/
theorem norm_sketchTangentProj_sub_le {p q : Type*} [Fintype p] [Fintype q] {Θ : Matrix p m ℝ}
    {Ω : Matrix q n ℝ} {R : Matrix k k ℝ} {R' : Matrix l l ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1)
    (hP : (Θ * (U * R))ᵀ * (Θ * (U * R)) = 1) (hW : (Ω * (V * R'))ᵀ * (Ω * (V * R')) = 1)
    {ε η : ℝ} (hε : ε < 1) (hη : 0 ≤ η) (Z : Matrix m n ℝ)
    (hlow : (1 - ε) * ‖sketchTangentProj Θ Ω (U * R) (V * R') Z - tangentProj U V Z‖ ≤
      ‖Θ * (sketchTangentProj Θ Ω (U * R) (V * R') Z - tangentProj U V Z) * Ωᵀ‖)
    (hip : |⟪Θ * (Z - tangentProj U V Z) * Ωᵀ,
        Θ * (sketchTangentProj Θ Ω (U * R) (V * R') Z - tangentProj U V Z) * Ωᵀ⟫| ≤
      η * ‖Z - tangentProj U V Z‖ *
        ‖sketchTangentProj Θ Ω (U * R) (V * R') Z - tangentProj U V Z‖) :
    ‖sketchTangentProj Θ Ω (U * R) (V * R') Z - tangentProj U V Z‖ ≤
      η / (1 - ε) ^ 2 * ‖Z - tangentProj U V Z‖ :=
  (isObliqueProj_sketchTangentProj hU hV hP hW).norm_sub_le_of_sketch (σ := sketchCLM Θ Ω)
    (isOrthProj_tangentProj hP hW) (sketch_obliqueTangentProj hP hW) hε hη Z hlow hip

/-! #### Two-sided interpolatory (cross) projection and the norm of `P^∠(Y)` -/

/-- **Interpolation property of the two-sided interpolatory (cross) projection**
`𝒫_U X 𝒫_Vᵀ = U (S_UᵀU)⁻¹ (S_Uᵀ X S_V) (VᵀS_V)⁻¹ Vᵀ`: it agrees with `X` on the selected cross,
`S_Uᵀ (𝒫_U X 𝒫_Vᵀ) S_V = S_Uᵀ X S_V`.  (This projection is built from the bases `U`, `V`; it is
distinct from the DEIM-CUR factorisation `C U R` of Sorensen–Embree.) -/
theorem transpose_mul_obliqueProj_mul_mul (hSU : IsUnit (SUᵀ * U).det)
    (hSV : IsUnit (SVᵀ * V).det) (X : Matrix m n ℝ) :
    SUᵀ * (obliqueProj U SU * X * (obliqueProj V SV)ᵀ) * SV = SUᵀ * X * SV := by
  simp only [Matrix.mul_assoc]
  rw [obliqueProj_transpose_mul hSV, transpose_mul_obliqueProj_mul hSU]

/-- **Error of the two-sided interpolatory (cross) projection** (elementary, via
`IsObliqueProj.norm_sub_mul_le`):
`‖X - 𝒫_U X 𝒫_Vᵀ‖_F ≤ ‖𝒫_U‖₂ ‖X - U Uᵀ X‖_F + ‖𝒫_U‖₂ ‖𝒫_V‖₂ ‖X - X V Vᵀ‖_F`. -/
theorem norm_sub_obliqueProj_mul_mul_le [Nonempty k] [Nonempty l] [DecidableEq m]
    [DecidableEq n] (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hSU : IsUnit (SUᵀ * U).det)
    (hSV : IsUnit (SVᵀ * V).det) (X : Matrix m n ℝ) :
    ‖X - obliqueProj U SU * X * (obliqueProj V SV)ᵀ‖ ≤
      specNorm (obliqueProj U SU) * ‖X - U * Uᵀ * X‖ +
        specNorm (obliqueProj U SU) * specNorm (obliqueProj V SV) * ‖X - X * V * Vᵀ‖ := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have hX : X = 0 := Matrix.ext fun _ j => isEmptyElim j
    simp [hX]
  rcases isEmpty_or_nonempty m with hm | hm
  · have hX : X = 0 := Matrix.ext fun i _ => isEmptyElim i
    simp [hX]
  have h := (isObliqueProj_leftOblique (n := n) hU hSU).norm_sub_mul_le
    (isObliqueProj_rightOblique hV hSV) (leftProj_ne_zero hU) (rightProj_ne_zero hV) X
  simp only [leftOblique_apply, rightOblique_apply, leftProj_apply, rightProj_apply,
    ← Matrix.mul_assoc] at h
  refine h.trans (add_le_add (mul_le_mul_of_nonneg_right (opNorm_leftOblique_le _ _)
    (norm_nonneg _)) (mul_le_mul_of_nonneg_right (mul_le_mul (opNorm_leftOblique_le _ _)
      (opNorm_rightOblique_le _ _) (norm_nonneg _) (specNorm_nonneg _)) (norm_nonneg _)))

/-- **Error of the two-sided interpolatory (cross) projection with selection matrices**
(`S_Uᵀ S_U = I`, `S_Vᵀ S_V = I`; not the Sorensen–Embree DEIM-CUR bound):
`‖X - 𝒫_U X 𝒫_Vᵀ‖_F ≤ C_U ‖X - U Uᵀ X‖_F + C_U C_V ‖X - X V Vᵀ‖_F` with
`C_U = ‖(S_UᵀU)⁻¹‖₂`, `C_V = ‖(S_VᵀV)⁻¹‖₂` (the constants of arXiv 2510.19518, eq. (6)). -/
theorem norm_sub_obliqueProj_mul_mul_le_of_orthonormal [Nonempty k] [Nonempty l]
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hSU' : SUᵀ * SU = 1) (hSV' : SVᵀ * SV = 1)
    (hSU : IsUnit (SUᵀ * U).det) (hSV : IsUnit (SVᵀ * V).det) (X : Matrix m n ℝ) :
    ‖X - obliqueProj U SU * X * (obliqueProj V SV)ᵀ‖ ≤
      specNorm (SUᵀ * U)⁻¹ * ‖X - U * Uᵀ * X‖ +
        specNorm (SUᵀ * U)⁻¹ * specNorm (SVᵀ * V)⁻¹ * ‖X - X * V * Vᵀ‖ := by
  classical
  have hCU := specNorm_obliqueProj_le_of_orthonormal hU hSU'
  have hCV := specNorm_obliqueProj_le_of_orthonormal hV hSV'
  refine (norm_sub_obliqueProj_mul_mul_le hU hV hSU hSV X).trans (add_le_add
    (mul_le_mul_of_nonneg_right hCU (norm_nonneg _)) (mul_le_mul_of_nonneg_right
      (mul_le_mul hCU hCV (specNorm_nonneg _) ((specNorm_nonneg _).trans hCU)) (norm_nonneg _)))

/-- **Lemma 4 of arXiv 2510.19518** (operator norm of the oblique tangent projector):
`‖P^∠(Y)‖ ≤ ‖𝒫_U‖₂ ‖𝒫_V‖₂` (operator norm for the Frobenius norm), unconditionally as in
eq. (15) of the paper. -/
theorem opNorm_obliqueTangentProj_le [Nonempty k] [Nonempty l] [Nonempty m] [Nonempty n]
    [DecidableEq m] [DecidableEq n] (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hSU : IsUnit (SUᵀ * U).det) (hSV : IsUnit (SVᵀ * V).det) :
    ‖obliqueTangentProj U SU V SV‖ ≤ specNorm (obliqueProj U SU) * specNorm (obliqueProj V SV) :=
  ((isObliqueProj_leftOblique hU hSU).opNorm_tangent_le (isObliqueProj_rightOblique hV hSV)
    (leftProj_rightProj_comm U V) (fun _ => (Matrix.mul_assoc _ _ _).symm)
    (fun _ => Matrix.mul_assoc _ _ _) (leftProj_ne_zero hU) (rightProj_ne_zero hV)).trans
    (mul_le_mul (opNorm_leftOblique_le _ _) (opNorm_rightOblique_le _ _) (norm_nonneg _)
      (specNorm_nonneg _))

/-- **Lemma 4 of arXiv 2510.19518** for selection matrices:
`‖P^∠(Y)‖ ≤ ‖(S_UᵀU)⁻¹‖₂ ‖(S_VᵀV)⁻¹‖₂ = C_{m,r} C_{n,r}`. -/
theorem opNorm_obliqueTangentProj_le_of_orthonormal [Nonempty k] [Nonempty l] [Nonempty m]
    [Nonempty n] (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hSU' : SUᵀ * SU = 1)
    (hSV' : SVᵀ * SV = 1) (hSU : IsUnit (SUᵀ * U).det) (hSV : IsUnit (SVᵀ * V).det) :
    ‖obliqueTangentProj U SU V SV‖ ≤ specNorm (SUᵀ * U)⁻¹ * specNorm (SVᵀ * V)⁻¹ := by
  classical
  have hCU := specNorm_obliqueProj_le_of_orthonormal hU hSU'
  exact (opNorm_obliqueTangentProj_le hU hV hSU hSV).trans
    (mul_le_mul hCU (specNorm_obliqueProj_le_of_orthonormal hV hSV') (specNorm_nonneg _)
      ((specNorm_nonneg _).trans hCU))

/-- **Szyld's identity for the oblique tangent projector** (Lemma 4 of arXiv 2510.19518):
`‖I - P^∠(Y)‖ = ‖P^∠(Y)‖` when `P(Y) ≠ I` (`P(Y) ≠ 0` follows from `Uᵀ U = I` with `k`, `n`
nonempty). -/
theorem opNorm_one_sub_obliqueTangentProj_eq [Nonempty k] [Nonempty n] (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (hSU : IsUnit (SUᵀ * U).det) (hSV : IsUnit (SVᵀ * V).det)
    (hT : tangentProj U V ≠ 1) :
    ‖1 - obliqueTangentProj U SU V SV‖ = ‖obliqueTangentProj U SU V SV‖ := by
  have hP := isObliqueProj_obliqueTangentProj (SU := SU) (SV := SV) hU hV hSU hSV
  refine hP.opNorm_one_sub_eq ?_ hT
  intro h0
  apply leftProj_ne_zero (m := m) (n := n) hU
  ext1 X
  have h1 : tangentProj U V (leftProj U X) = 0 := by rw [h0, zero_apply]
  rw [tangentProj_apply, leftProj_apply] at h1
  rw [leftProj_apply, zero_apply]
  have hUU : U * Uᵀ * (U * Uᵀ * X) = U * Uᵀ * X := (isOrthProj_leftProj (n := n) hU).idem X
  rw [hUU] at h1
  simpa using h1

end Tangent

end Matrices

open Matrix in
/-- The hypotheses of the DEIM bounds are jointly satisfiable: `U = S = e₁ ∈ ℝ^{2×1}` (the
orthogonal case `𝒫 = U Uᵀ`; see the next example for a genuinely oblique one). -/
example : ∃ U S : Matrix (Fin 2) (Fin 1) ℝ, Uᵀ * U = 1 ∧ Sᵀ * S = 1 ∧ IsUnit (Sᵀ * U).det := by
  let e : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]
  have h : eᵀ * e = 1 := by
    ext i j; fin_cases i; fin_cases j; simp [e, Matrix.mul_apply, Fin.sum_univ_two]
  exact ⟨e, e, h, h, by rw [h, Matrix.det_one]; exact isUnit_one⟩

open Matrix in
open scoped LeanDLRA.Frobenius in
/-- The hypotheses of `opNorm_one_sub_obliqueTangentProj_eq` (Szyld's identity) are jointly
satisfiable: for `U = V = S_U = S_V = e₁ ∈ ℝ^{2×1}` the tangent projector `P(Y)` on `ℝ^{2×2}` is
not the identity. -/
example : ∃ U : Matrix (Fin 2) (Fin 1) ℝ, Uᵀ * U = 1 ∧ IsUnit (Uᵀ * U).det ∧
    (tangentProj U U : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ) ≠ 1 := by
  let e : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]
  have h : eᵀ * e = 1 := by
    ext i j; fin_cases i; fin_cases j; simp [e, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨e, h, by rw [h, Matrix.det_one]; exact isUnit_one, fun hT => ?_⟩
  let Z : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 1]
  have hZ1 : eᵀ * Z = 0 := by
    ext i j; fin_cases i; fin_cases j <;> simp [e, Z, Matrix.mul_apply, Fin.sum_univ_two]
  have hZ2 : Z * e = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [e, Z, Matrix.mul_apply, Fin.sum_univ_two]
  have h1 : tangentProj e e Z = Z := by rw [hT]; rfl
  rw [tangentProj_apply, Matrix.mul_assoc e eᵀ Z, hZ1, hZ2] at h1
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, sub_zero] at h1
  have h2 := congrFun (congrFun h1 1) 1
  simp [Z] at h2

open Matrix in
/-- A **genuinely oblique** DEIM projector: `U = (3/5, 4/5)ᵀ` (orthonormal) and the selection
`S = e₁ ∈ ℝ^{2×1}` satisfy the hypotheses of `norm_sub_obliqueProj_mul_le_of_orthonormal`, with
`(SᵀU)⁻¹ = 5/3 > 1`, and `𝒫 = U (SᵀU)⁻¹ Sᵀ ≠ U Uᵀ` (the interpolation property `Sᵀ 𝒫 = Sᵀ`
fails for `U Uᵀ`). -/
example : ∃ U S : Matrix (Fin 2) (Fin 1) ℝ, Uᵀ * U = 1 ∧ Sᵀ * S = 1 ∧ IsUnit (Sᵀ * U).det ∧
    obliqueProj U S ≠ U * Uᵀ := by
  let U : Matrix (Fin 2) (Fin 1) ℝ := !![3 / 5; 4 / 5]
  let S : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]
  have hU : Uᵀ * U = 1 := by
    ext i j; fin_cases i; fin_cases j; simp [U, Matrix.mul_apply, Fin.sum_univ_two]; norm_num
  have hS : Sᵀ * S = 1 := by
    ext i j; fin_cases i; fin_cases j; simp [S, Matrix.mul_apply, Fin.sum_univ_two]
  have hSU : Sᵀ * U = !![3 / 5] := by
    ext i j; fin_cases i; fin_cases j; simp [U, S, Matrix.mul_apply, Fin.sum_univ_two]
  have hdet : IsUnit (Sᵀ * U).det := by
    rw [hSU, Matrix.det_fin_one_of]; exact isUnit_iff_ne_zero.2 (by norm_num)
  refine ⟨U, S, hU, hS, hdet, fun h => ?_⟩
  have h1 := transpose_mul_obliqueProj hdet
  rw [h] at h1
  have h2 := congrFun (congrFun h1 0) 0
  simp [U, S, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] at h2
  norm_num at h2

open Matrix in
open scoped LeanDLRA.Frobenius in
/-- **Non-vacuity of the sketch results in the compressive regime** (`m = n = 2`, rank `1`,
sketch size `ℓ = 1 < 2`): `Θ = Ω = (1, 1/2)`, `U = V = e₁`, `R = R' = 1` (so `ΘP = 1`), and
`Z = e₂ e₂ᵀ` (a purely normal direction).  The oblique sketch projection differs from the
orthogonal one, `δ = P^{Θ,Ω}_Y Z - P_Y Z = [[-1/4, 1/2], [1/2, 0]] ≠ 0`, and the pointwise
hypotheses of `norm_sketchTangentProj_sub_le` hold with `ε = 2/3`, `η = 1/12`; the resulting
bound `‖δ‖_F ≤ η / (1 - ε)² ‖Z - P_Y Z‖_F = 3/4` is attained. -/
example :
    let Θ : Matrix (Fin 1) (Fin 2) ℝ := !![1, 1 / 2]
    let e : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]
    let R : Matrix (Fin 1) (Fin 1) ℝ := 1
    let P : Matrix (Fin 2) (Fin 1) ℝ := e * R
    let Z : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 1]
    let δ := sketchTangentProj Θ Θ P P Z - tangentProj e e Z
    eᵀ * e = 1 ∧ (Θ * P)ᵀ * (Θ * P) = 1 ∧ δ ≠ 0 ∧
      (1 - 2 / 3) * ‖δ‖ ≤ ‖Θ * δ * Θᵀ‖ ∧
      |⟪Θ * (Z - tangentProj e e Z) * Θᵀ, Θ * δ * Θᵀ⟫| ≤
        1 / 12 * ‖Z - tangentProj e e Z‖ * ‖δ‖ ∧
      ‖δ‖ = 1 / 12 / (1 - 2 / 3) ^ 2 * ‖Z - tangentProj e e Z‖ := by
  intro Θ e R P Z δ
  have he : eᵀ * e = 1 := by
    ext i j; fin_cases i; fin_cases j; simp [e, Matrix.mul_apply, Fin.sum_univ_two]
  have hΘe : Θ * P = 1 := by
    ext i j; fin_cases i; fin_cases j; simp [Θ, P, R, e, Matrix.mul_apply, Fin.sum_univ_two]
  have hP : (Θ * P)ᵀ * (Θ * P) = 1 := by rw [hΘe]; simp
  have hT0 : tangentProj e e Z = 0 := by
    rw [tangentProj_apply]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [e, Z, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have hδ : δ = !![-1 / 4, 1 / 2; 1 / 2, 0] := by
    change sketchTangentProj Θ Θ P P Z - tangentProj e e Z = _
    rw [hT0, sub_zero, sketchTangentProj, obliqueTangentProj_sketch_eq hP hP]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Θ, P, R, e, Z, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have hσδ : Θ * δ * Θᵀ = !![1 / 4] := by
    rw [hδ]; ext i j; fin_cases i; fin_cases j
    simp [Θ, Matrix.mul_apply, Fin.sum_univ_two]; norm_num
  have hσN : Θ * (Z - tangentProj e e Z) * Θᵀ = !![1 / 4] := by
    rw [hT0, sub_zero]; ext i j; fin_cases i; fin_cases j
    simp [Θ, Z, Matrix.mul_apply, Fin.sum_univ_two]; norm_num
  have hnδ : ‖δ‖ = 3 / 4 := by
    rw [hδ, Frobenius.norm_def, Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
    norm_num [Fin.sum_univ_two]
  have hnσδ : ‖(!![1 / 4] : Matrix (Fin 1) (Fin 1) ℝ)‖ = 1 / 4 := by
    rw [Frobenius.norm_def, Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
    norm_num
  have hnN : ‖Z - tangentProj e e Z‖ = 1 := by
    rw [hT0, sub_zero, Frobenius.norm_def]
    simp [Z, Fin.sum_univ_two]
  have hinner : ⟪(!![1 / 4] : Matrix (Fin 1) (Fin 1) ℝ), !![1 / 4]⟫ = 1 / 16 := by
    rw [Frobenius.inner_def]; simp; norm_num
  refine ⟨he, hP, ?_, ?_, ?_, ?_⟩
  · rw [hδ]; intro h
    have := congrFun (congrFun h 0) 1
    simp at this
  · rw [hσδ, hnσδ, hnδ]; norm_num
  · rw [hσδ, hσN, hinner, hnN, hnδ]; norm_num
  · rw [hnδ, hnN]; norm_num

end LeanDLRA
