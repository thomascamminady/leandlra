import LeanDLRA.HighOrder.MidpointBUGGlobal
import LeanDLRA.Integrators.Matrix.AdaptiveBUGStep
import LeanDLRA.Integrators.Matrix.FlowDistance

/-!
# The midpoint BUG step for matrices as a step relation

This file states the midpoint basis-update & Galerkin (BUG) integrator of Ceruti, Einkemmer,
Kusch and Lubich (arXiv:2402.08607, §3, Algorithm 1, the 4r variant) for matrices, as a relation
between the old value `Y₀` and the new value `Y₁` (`StepRel`), and gives the local error of a
step. The error analysis at the level of orthogonal projectors is in
`LeanDLRA/HighOrder/MidpointBUG.lean` and `LeanDLRA/HighOrder/MidpointBUGGlobal.lean`; the local
error of this file is taken from there (`MidpointBUG.IsMidpointBUGStep.hasLocalError`) through
the bridge `MatrixMidpointBUG.IsStep.isMidpointBUGStep`, and is not proved a second time. That
the step relation is a tube-local method, and the existence and the error bound of runs, are
shown in `LeanDLRA/HighOrder/MidpointBUGRun.lean`.

**The step.** Let `Y₀ = U₀ S₀ V₀ᵀ` with `r` orthonormal columns in `U₀` and in `V₀`, and let
`t½ = (t₀ + t₁) / 2`.

* *Half step.* An augmented BUG step (`MatrixBUG.IsRankAdaptiveStep`, without truncation) over
  `[t₀, t½]`: the K- and L-steps from `U₀ S₀` and `V₀ S₀ᵀ`, bases `Uh`, `Vh` whose ranges
  contain the columns of `(K(t½), U₀)` and `(L(t½), V₀)`, and the Galerkin step in these bases.
  Its result is the midpoint predictor `Yh = Uh Sh(t½) Vhᵀ`.
* *Galerkin step.* One evaluation `G = F(t½, Yh)`, bases `Ub`, `Vb` with orthonormal columns
  whose ranges contain the columns of `(Uh, G Vh)` and of `(Vh, Gᵀ Uh)`, and the Galerkin step
  `Sb' = Ubᵀ F(t, Ub Sb Vbᵀ) Vb`, `Sb(t₀) = Ubᵀ U₀ S₀ V₀ᵀ Vb`, over the whole step `[t₀, t₁]`.
  Its result is `Ȳ = Ub Sb(t₁) Vbᵀ`, of rank at most `4 r`.
* *Truncation.* `Ȳ` is replaced by a best approximation of rank at most `r`.

The step relations contain the algorithm only. The sizes `ε`, `ε₂` of the normal parts of the
field, the Lipschitz constant, the bounds of the field and of its derivatives are hypotheses of
the error theorems, not part of the step.

## Main definitions

* `MatrixMidpointBUG.IsStep F t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb`: the half step and the
  Galerkin step at the level of the factors, for any index types of the columns.
* `MatrixMidpointBUG.augmentedRel F r`: the step without truncation, from a factorization with
  `r` columns; the half step has exactly `2 r` columns, the Galerkin bases at most `4 r`.
* `MatrixMidpointBUG.stepRel F r`: the step of the fixed-rank integrator: a best approximation
  of rank at most `r` of a result of `augmentedRel F r`.

## Main results

* `MatrixMidpointBUG.IsStep.isMidpointBUGStep`: a factor step with normal bounds `ε` at the
  results of the K- and L-step and `ε₂` at the midpoint predictor is a step
  `MidpointBUG.IsMidpointBUGStep` for the projectors `leftProj`, `rightProj`, `galerkinProj`.
* `MatrixMidpointBUG.IsStep.hasLocalError`, `MatrixMidpointBUG.augmentedRel.hasLocalError`: the
  local error `C h (h² + h ε + ε₂)` of the step without truncation, `h = t₁ - t₀`, for a field
  of class `C²` with bounded derivatives, with the constant of
  `MidpointBUG.IsMidpointBUGStep.hasLocalError`; the normal bounds are needed only on a tube
  around a reference solution.
* `MatrixMidpointBUG.stepRel.hasLocalError`: the local error
  `h (e^{L H} ε + 2 C (h² + h ε + ε₂))` of the fixed-rank step.
* `MatrixMidpointBUG.isStep_tubeExt_iff_of_near`, `MatrixMidpointBUG.stepRel_tubeExt_iff_of_near`:
  if `‖Y₀ - A t₀‖ + 2 B (t₁ - t₀) < ρ`, the tube extension `tubeExt F A a b ρ` has the same steps
  as `F`.
* `MatrixMidpointBUG.augmentedRel.stepRel_truncation`: the truncated singular value decomposition
  of `Ȳ` is a truncation of the step.

## Implementation notes

The local error rests on `MidpointBUG.IsMidpointBUGStep.hasLocalError`, whose hypotheses on the
field are global: `F` is Lipschitz and bounded everywhere, and the uncurried field is of class
`C²` with bounded first and second derivatives. The third derivative of the exact solution is
bounded through these bounds. These hypotheses cannot be localized through the tube extension
`tubeExt F A a b ρ` as for the first-order integrators: the extension is neither of class `C²`
nor Lipschitz in time. The normal bounds, in contrast, are needed only at the points that
the step visits: at the results `K(t½) V₀ᵀ`, `U₀ L(t½)ᵀ` of the K- and L-step, at the midpoint
predictor `Yh`, and, for the truncation, at the factored rank-`r` points near the exact solution.
With the margin `‖Y₀ - A t₀‖ + 3 B (t₁ - t₀) < ρ` all of them lie in the tube of radius `ρ`
around the reference solution `A`, so the normal bounds are hypotheses on that tube
(`FactoredNormalBoundOn`), as in the paper.

The half step has exactly `2 r` columns, because the second normal bound is assumed at the
factored points with `2 r` columns. When the columns of `(K(t½), U₀)` span a space of smaller
dimension, the basis is completed by further orthonormal columns; this needs `2 r ≤ m` and
`2 r ≤ n` for the existence of a step. The Galerkin bases have at most `4 r` columns each, and
their numbers of columns need not be equal; their existence needs no condition on `m`, `n`.

The truncation to rank `r` is a best approximation. Its cost is the distance of the exact
solution to the matrices of rank at most `r` plus twice the error before truncation
(`norm_bestTrunc_sub_le`). The distance is at most `h ε e^{L h}`, without a term `h²`
(`distLR_flow_le_exp_of_tube`), which keeps the step of second order.

The catalogue structure `IsMidpoint4rStep` of arXiv:2402.08607 has one number of columns for
both Galerkin bases and states the capture of `h F V̂` instead of `F V̂`; for `h > 0` the two
forms are equivalent.

## References

* G. Ceruti, L. Einkemmer, J. Kusch, Ch. Lubich, *A robust second-order low-rank BUG integrator
  based on the midpoint rule*, arXiv:2402.08607.
* G. Ceruti, J. Kusch, Ch. Lubich, *A rank-adaptive robust integrator for dynamical low-rank
  approximation*, arXiv:2104.05247 (BIT Numer. Math. 2022), for the augmented half step.
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace MatrixMidpointBUG

/-! ### The step of the factors -/

section Step

variable {m n k k' l l' : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype k'] [Fintype l]
  [Fintype l'] [DecidableEq k] [DecidableEq k'] [DecidableEq l] [DecidableEq l'] {r : ℕ}

/-- **One step of the midpoint BUG integrator at the level of the factors** (Ceruti, Einkemmer,
Kusch and Lubich, arXiv:2402.08607, §3, Algorithm 1, steps 1 and 2) from `Y₀ = U₀ S₀ V₀ᵀ` at
`t₀` to `t₁`, without truncation. With `t½ = (t₀ + t₁) / 2`:

* `half`: an augmented BUG step over `[t₀, t½]` without truncation, with bases `Uh`, `Vh`; its
  result is the midpoint predictor `Yh = Uh Sh(t½) Vhᵀ`;
* the bases `Ub`, `Vb` have orthonormal columns, the range of `Ub` contains the columns of `Uh`
  and of `F(t½, Yh) Vh`, the range of `Vb` those of `Vh` and of `F(t½, Yh)ᵀ Uh`;
* `Sb` solves the Galerkin equation `Sb' = Ubᵀ F(t, Ub Sb Vbᵀ) Vb` on `[t₀, t₁]` with
  `Sb(t₀) = Ubᵀ U₀ S₀ V₀ᵀ Vb`.

The result of the step is `Ub Sb(t₁) Vbᵀ`. The bases are any orthonormal bases whose ranges
contain the named columns; the algorithm takes orthonormal bases of the spans. -/
structure IsStep (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ t₁ : ℝ) (U₀ : Matrix m (Fin r) ℝ)
    (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ) (Uh : Matrix m k ℝ)
    (Vh : Matrix n k' ℝ) (K : ℝ → Matrix m (Fin r) ℝ) (Lf : ℝ → Matrix n (Fin r) ℝ)
    (Sh : ℝ → Matrix k k' ℝ) (Ub : Matrix m l ℝ) (Vb : Matrix n l' ℝ) (Sb : ℝ → Matrix l l' ℝ) :
    Prop where
  /-- The augmented BUG half step over `[t₀, (t₀ + t₁) / 2]`, without truncation. -/
  half : MatrixBUG.IsRankAdaptiveStep F 0 t₀ ((t₀ + t₁) / 2) U₀ S₀ V₀ Uh Vh K Lf Sh
    (Uh * Sh ((t₀ + t₁) / 2) * Vhᵀ)
  orthUb : Ubᵀ * Ub = 1
  orthVb : Vbᵀ * Vb = 1
  /-- The range of `Ub` contains the columns of `Uh`. -/
  capU : Ub * Ubᵀ * Uh = Uh
  /-- The range of `Vb` contains the columns of `Vh`. -/
  capV : Vb * Vbᵀ * Vh = Vh
  /-- The range of `Ub` contains the columns of `F(t½, Yh) Vh`. -/
  capF : Ub * Ubᵀ * (F ((t₀ + t₁) / 2) (Uh * Sh ((t₀ + t₁) / 2) * Vhᵀ) * Vh) =
    F ((t₀ + t₁) / 2) (Uh * Sh ((t₀ + t₁) / 2) * Vhᵀ) * Vh
  /-- The range of `Vb` contains the columns of `F(t½, Yh)ᵀ Uh`. -/
  capFt : Vb * Vbᵀ * ((F ((t₀ + t₁) / 2) (Uh * Sh ((t₀ + t₁) / 2) * Vhᵀ))ᵀ * Uh) =
    (F ((t₀ + t₁) / 2) (Uh * Sh ((t₀ + t₁) / 2) * Vhᵀ))ᵀ * Uh
  /-- The Galerkin step `Sb' = Ubᵀ F(t, Ub Sb Vbᵀ) Vb` on the whole step. -/
  sSol : ODESolution (MatrixBUG.sField Ub Vb F) Sb t₀ t₁
  /-- `Sb(t₀) = Ubᵀ U₀ S₀ V₀ᵀ Vb`. -/
  sStart : Sb t₀ = Ubᵀ * U₀ * S₀ * (V₀ᵀ * Vb)

variable {F G : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} {U₀ : Matrix m (Fin r) ℝ}
  {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ} {Uh : Matrix m k ℝ}
  {Vh : Matrix n k' ℝ} {K : ℝ → Matrix m (Fin r) ℝ} {Lf : ℝ → Matrix n (Fin r) ℝ}
  {Sh : ℝ → Matrix k k' ℝ} {Ub : Matrix m l ℝ} {Vb : Matrix n l' ℝ} {Sb : ℝ → Matrix l l' ℝ}

/-- The range of `Ub` contains the columns of `U₀`, through `Uh`. -/
theorem IsStep.capU₀ (hs : IsStep F t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb) :
    Ub * Ubᵀ * U₀ = U₀ := by
  calc Ub * Ubᵀ * U₀ = Ub * Ubᵀ * (Uh * Uhᵀ * U₀) := by rw [hs.half.augU]
    _ = (Ub * Ubᵀ * Uh) * Uhᵀ * U₀ := by simp only [Matrix.mul_assoc]
    _ = U₀ := by rw [hs.capU, hs.half.augU]

/-- The range of `Vb` contains the columns of `V₀`, through `Vh`. -/
theorem IsStep.capV₀ (hs : IsStep F t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb) :
    Vb * Vbᵀ * V₀ = V₀ := by
  calc Vb * Vbᵀ * V₀ = Vb * Vbᵀ * (Vh * Vhᵀ * V₀) := by rw [hs.half.augV]
    _ = (Vb * Vbᵀ * Vh) * Vhᵀ * V₀ := by simp only [Matrix.mul_assoc]
    _ = V₀ := by rw [hs.capV, hs.half.augV]

/-- The Galerkin projector of the step fixes the start value `U₀ S₀ V₀ᵀ`. -/
theorem IsStep.galerkinProj_start (hs : IsStep F t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb) :
    galerkinProj Ub Vb (U₀ * S₀ * V₀ᵀ) = U₀ * S₀ * V₀ᵀ := by
  have hT : V₀ᵀ * Vb * Vbᵀ = V₀ᵀ := by
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose hs.capV₀
  rw [galerkinProj_apply]
  calc Ub * Ubᵀ * (U₀ * S₀ * V₀ᵀ) * (Vb * Vbᵀ) = (Ub * Ubᵀ * U₀) * S₀ * (V₀ᵀ * Vb * Vbᵀ) := by
        simp only [Matrix.mul_assoc]
    _ = U₀ * S₀ * V₀ᵀ := by rw [hs.capU₀, hT]

/-- **The Galerkin step starts at `Y₀`**: `Ub Sb(t₀) Vbᵀ = U₀ S₀ V₀ᵀ`, because the ranges of `Ub`
and `Vb` contain those of `U₀` and `V₀` (arXiv:2402.08607, remark after (8)). -/
theorem IsStep.start_eq (hs : IsStep F t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb) :
    Ub * Sb t₀ * Vbᵀ = U₀ * S₀ * V₀ᵀ := by
  rw [← hs.galerkinProj_start, galerkinProj_apply, hs.sStart]
  simp only [Matrix.mul_assoc]

/-- The trajectory `Ub Sb(t) Vbᵀ` solves the Galerkin equation `Y' = galerkinProj Ub Vb F(t, Y)`
in the space of matrices. -/
theorem IsStep.odeSolution_galerkin (hs : IsStep F t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb) :
    ODESolution (fun t x => galerkinProj Ub Vb (F t x)) (fun t => Ub * Sb t * Vbᵀ) t₀ t₁ :=
  MatrixBUG.odeSolution_sField hs.sSol

/-- **Two fields that agree where the step evaluates them have the same steps.** If the half
step is also a step for `G`, and `G` agrees with `F` at the midpoint predictor and along the
Galerkin trajectory `Ub Sb(t) Vbᵀ`, then a step for `F` is a step for `G`. -/
theorem IsStep.congr_field (hs : IsStep F t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb)
    (hhalf : MatrixBUG.IsRankAdaptiveStep G 0 t₀ ((t₀ + t₁) / 2) U₀ S₀ V₀ Uh Vh K Lf Sh
      (Uh * Sh ((t₀ + t₁) / 2) * Vhᵀ))
    (hmid : G ((t₀ + t₁) / 2) (Uh * Sh ((t₀ + t₁) / 2) * Vhᵀ) =
      F ((t₀ + t₁) / 2) (Uh * Sh ((t₀ + t₁) / 2) * Vhᵀ))
    (hS : ∀ t ∈ Ico t₀ t₁, G t (Ub * Sb t * Vbᵀ) = F t (Ub * Sb t * Vbᵀ)) :
    IsStep G t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb where
  half := hhalf
  orthUb := hs.orthUb
  orthVb := hs.orthVb
  capU := hs.capU
  capV := hs.capV
  capF := by rw [hmid]; exact hs.capF
  capFt := by rw [hmid]; exact hs.capFt
  sSol := hs.sSol.congr_field fun t ht => by simp only [MatrixBUG.sField, hS t ht]
  sStart := hs.sStart

variable [DecidableEq m] [DecidableEq n]

/-- **Capture of the field at the midpoint predictor.** The Galerkin projector of the step loses
only the doubly normal part of `G = F(t½, Yh)` with respect to the bases `Uh`, `Vh` of the half
step: `‖(1 - galerkinProj Ub Vb) G‖ ≤ ‖(I - Uh Uhᵀ) G (I - Vh Vhᵀ)‖`
(arXiv:2402.08607, proof of Theorem 1; `MidpointBUG.norm_sub_apply_apply_le_normal`). -/
theorem IsStep.norm_one_sub_galerkinProj_le
    (hs : IsStep F t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb) :
    ‖(1 - galerkinProj Ub Vb) (F ((t₀ + t₁) / 2) (Uh * Sh ((t₀ + t₁) / 2) * Vhᵀ))‖ ≤
      ‖(1 - Uh * Uhᵀ) * F ((t₀ + t₁) / 2) (Uh * Sh ((t₀ + t₁) / 2) * Vhᵀ) *
        (1 - Vh * Vhᵀ)‖ := by
  have hVh : Vhᵀ * Vb * Vbᵀ = Vhᵀ := by
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose hs.capV
  have key : ∀ x : Matrix m n ℝ, Ub * Ubᵀ * (x * Vh) = x * Vh →
      Vb * Vbᵀ * (xᵀ * Uh) = xᵀ * Uh →
      ‖(1 - galerkinProj Ub Vb) x‖ ≤ ‖(1 - Uh * Uhᵀ) * x * (1 - Vh * Vhᵀ)‖ := by
    intro x hcF hcFt
    have hxT : Uhᵀ * x * Vb * Vbᵀ = Uhᵀ * x := by
      simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose hcFt
    have h := MidpointBUG.norm_sub_apply_apply_le_normal (P := leftProj Ub) (Q := rightProj Vb)
      (p := leftProj Uh) (q := rightProj Vh) (isOrthProj_galerkinProj hs.orthUb hs.orthVb)
      (leftProj_rightProj_comm Uh Vh)
      (fun z => by simp only [leftProj_apply, ← Matrix.mul_assoc, hs.capU])
      (fun z => by
        rw [rightProj_apply, rightProj_apply, Matrix.mul_assoc (z * Vh),
          Matrix.mul_assoc (z * Vh), hVh])
      (x := x)
      (by rw [rightProj_apply, leftProj_apply, ← Matrix.mul_assoc (Ub * Ubᵀ) (x * Vh) Vhᵀ, hcF])
      (by
        rw [rightProj_apply, leftProj_apply]
        simp only [Matrix.mul_assoc] at hxT ⊢
        rw [hxT])
    rw [one_sub_leftProj_one_sub_rightProj_apply] at h
    calc ‖(1 - galerkinProj Ub Vb) x‖ = ‖x - leftProj Ub (rightProj Vb x)‖ := rfl
      _ ≤ _ := h
  exact key _ hs.capF hs.capFt

/-- **The factor step is a midpoint BUG step for orthogonal projectors.** Let `ε` bound the
normal part of `F` at the results `K(t½) V₀ᵀ` and `U₀ L(t½)ᵀ` of the K- and L-step of the half
step, in the bases after the half step, at all times of the half step, and let `ε₂` bound the
normal part `(I - Uh Uhᵀ) F(t½, Yh) (I - Vh Vhᵀ)` at the midpoint predictor. Then the step is a
step `MidpointBUG.IsMidpointBUGStep` with step size `t₁ - t₀`, truncation tolerance `0` and the
projectors `P₀ = leftProj U₀`, `Q₀ = rightProj V₀`, `Ph = leftProj Uh`, `Qh = rightProj Vh`,
`R = galerkinProj Ub Vb`. -/
theorem IsStep.isMidpointBUGStep (hs : IsStep F t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb)
    {ε ε₂ : ℝ}
    (hεK : ∀ t ∈ Icc t₀ ((t₀ + t₁) / 2),
      ‖(1 - Uh * Uhᵀ) * F t (K ((t₀ + t₁) / 2) * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε)
    (hεL : ∀ t ∈ Icc t₀ ((t₀ + t₁) / 2),
      ‖(1 - U₀ * U₀ᵀ) * F t (U₀ * (Lf ((t₀ + t₁) / 2))ᵀ) * (1 - Vh * Vhᵀ)‖ ≤ ε)
    (hε₂ : ‖(1 - Uh * Uhᵀ) * F ((t₀ + t₁) / 2) (Uh * Sh ((t₀ + t₁) / 2) * Vhᵀ) *
      (1 - Vh * Vhᵀ)‖ ≤ ε₂) :
    MidpointBUG.IsMidpointBUGStep F ε ε₂ 0 (leftProj U₀) (rightProj V₀) (leftProj Uh)
      (rightProj Vh) (galerkinProj Ub Vb) t₀ (t₁ - t₀) (U₀ * S₀ * V₀ᵀ) (fun t => K t * V₀ᵀ)
      (fun t => U₀ * (Lf t)ᵀ) (fun t => Uh * Sh t * Vhᵀ) (fun t => Ub * Sb t * Vbᵀ)
      (Ub * Sb t₁ * Vbᵀ) := by
  have e₁ : t₀ + (t₁ - t₀) / 2 = (t₀ + t₁) / 2 := by ring
  have e₂ : t₀ + (t₁ - t₀) = t₁ := by ring
  refine ⟨?_, isOrthProj_galerkinProj hs.orthUb hs.orthVb, hs.galerkinProj_start, ?_, ?_,
    hs.start_eq, ?_⟩
  · rw [e₁]
    refine hs.half.isBUGStepCore.isBUGStep (fun t ht => ?_) (fun t ht => ?_)
    · rw [one_sub_leftProj_one_sub_rightProj_apply]
      exact hεK t ht
    · rw [MatrixBUG.one_sub_rightProj_one_sub_leftProj_apply]
      exact hεL t ht
  · rw [e₁]
    exact hs.norm_one_sub_galerkinProj_le.trans hε₂
  · rw [e₂]
    exact hs.odeSolution_galerkin
  · rw [e₂]
    simp

/-- **Local error of the factor step for a field of class `C²`** (arXiv:2402.08607, Theorem 1,
4r variant). Let `F` be `L`-Lipschitz (`L ≥ 0`) and bounded by `B` everywhere, and let the
uncurried field `(t, x) ↦ F t x` be of class `C²` with `‖DF‖ ≤ M₁` and `‖D²F‖ ≤ M₂` everywhere.
Under the normal bounds of `MatrixMidpointBUG.IsStep.isMidpointBUGStep`, a step of size
`0 ≤ h = t₁ - t₀ ≤ H` has local error `C h (h² + h ε + ε₂)` with
`C = midpointBUGConst L M₁ B (M₂ (1 + B)² + M₁² (1 + B)) H`: this is
`MidpointBUG.IsMidpointBUGStep.hasLocalError` for the step of the bridge. -/
theorem IsStep.hasLocalError (hs : IsStep F t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb)
    {ε ε₂ L B M₁ M₂ H : ℝ}
    (hεK : ∀ t ∈ Icc t₀ ((t₀ + t₁) / 2),
      ‖(1 - Uh * Uhᵀ) * F t (K ((t₀ + t₁) / 2) * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε)
    (hεL : ∀ t ∈ Icc t₀ ((t₀ + t₁) / 2),
      ‖(1 - U₀ * U₀ᵀ) * F t (U₀ * (Lf ((t₀ + t₁) / 2))ᵀ) * (1 - Vh * Vhᵀ)‖ ≤ ε)
    (hε₂ : ‖(1 - Uh * Uhᵀ) * F ((t₀ + t₁) / 2) (Uh * Sh ((t₀ + t₁) / 2) * Vhᵀ) *
      (1 - Vh * Vhᵀ)‖ ≤ ε₂)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hF₂ : ContDiff ℝ 2 (Function.uncurry F))
    (hM₁ : ∀ p, ‖fderiv ℝ (Function.uncurry F) p‖ ≤ M₁)
    (hM₂ : ∀ p, ‖iteratedFDeriv ℝ 2 (Function.uncurry F) p‖ ≤ M₂) (h01 : t₀ ≤ t₁)
    (hH : t₁ - t₀ ≤ H) :
    HasLocalError F t₀ t₁ (U₀ * S₀ * V₀ᵀ) (Ub * Sb t₁ * Vbᵀ)
      (MidpointBUG.midpointBUGConst L M₁ B (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) H * (t₁ - t₀) *
        ((t₁ - t₀) ^ 2 + (t₁ - t₀) * ε + ε₂)) := by
  have h := (hs.isMidpointBUGStep hεK hεL hε₂).hasLocalError hF hL hB hF₂ hM₁ hM₂
    (sub_nonneg.2 h01) hH
  have e : t₀ + (t₁ - t₀) = t₁ := by ring
  rw [e, add_zero] at h
  exact h

end Step

/-! ### The step relations -/

section Rel

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ}

/-- **The midpoint BUG step without truncation, as a relation between matrices.**
`augmentedRel F r t₀ t₁ Y₀ Ȳ` holds if `Y₀ = U₀ S₀ V₀ᵀ` for factors with `r` columns and
orthonormal `U₀`, `V₀`, and `Ȳ = Ub Sb(t₁) Vbᵀ` for a step `MatrixMidpointBUG.IsStep` of these
factors over `[t₀, t₁]` in which the half step has exactly `2 r` columns and the Galerkin bases
`Ub`, `Vb` have at most `4 r` columns (arXiv:2402.08607, §3, Algorithm 1 (4r), before the
truncation). When the columns of `(K(t½), U₀)` span less than `2 r` dimensions, the bases of the
half step are completed by further orthonormal columns. -/
def augmentedRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ =>
    ∃ (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
      (Uh : Matrix m (Fin (2 * r)) ℝ) (Vh : Matrix n (Fin (2 * r)) ℝ)
      (K : ℝ → Matrix m (Fin r) ℝ) (Lf : ℝ → Matrix n (Fin r) ℝ)
      (Sh : ℝ → Matrix (Fin (2 * r)) (Fin (2 * r)) ℝ) (l l' : ℕ) (Ub : Matrix m (Fin l) ℝ)
      (Vb : Matrix n (Fin l') ℝ) (Sb : ℝ → Matrix (Fin l) (Fin l') ℝ),
      Y₀ = U₀ * S₀ * V₀ᵀ ∧ l ≤ 4 * r ∧ l' ≤ 4 * r ∧
        IsStep F t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb ∧ Y₁ = Ub * Sb t₁ * Vbᵀ

/-- **The step of the fixed-rank midpoint BUG integrator, as a relation between matrices**
(arXiv:2402.08607, §3, Algorithm 1 (4r), with truncation to rank `r`). `stepRel F r t₀ t₁ Y₀ Y₁`
holds if `Y₁` is a best approximation of rank at most `r` to a result `Ȳ` of the step without
truncation from `Y₀` over `[t₀, t₁]` (`MatrixMidpointBUG.augmentedRel`): `Y₁` has rank at most
`r`, and `‖Y₁ - Ȳ‖` is at most the distance `distLR r Ȳ` of `Ȳ` to the matrices of rank at most
`r`. The relation contains every truncation with this property, in particular the truncated
singular value decomposition of `Ȳ` (`MatrixMidpointBUG.augmentedRel.stepRel_truncation`). -/
def stepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ => ∃ Yh : Matrix m n ℝ, augmentedRel F r t₀ t₁ Y₀ Yh ∧ Y₁.rank ≤ r ∧
    ‖Y₁ - Yh‖ ≤ distLR r Yh

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} {U₀ : Matrix m (Fin r) ℝ}
  {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ} {Uh : Matrix m (Fin (2 * r)) ℝ}
  {Vh : Matrix n (Fin (2 * r)) ℝ} {K : ℝ → Matrix m (Fin r) ℝ} {Lf : ℝ → Matrix n (Fin r) ℝ}
  {Sh : ℝ → Matrix (Fin (2 * r)) (Fin (2 * r)) ℝ} {l l' : ℕ} {Ub : Matrix m (Fin l) ℝ}
  {Vb : Matrix n (Fin l') ℝ} {Sb : ℝ → Matrix (Fin l) (Fin l') ℝ} {Y₀ Y₁ Yh : Matrix m n ℝ}

/-- A factor step with `2 r` columns in the half step and at most `4 r` columns in the Galerkin
bases is a step of the relation `augmentedRel`. -/
theorem IsStep.augmentedRel (hs : IsStep F t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb)
    (hl : l ≤ 4 * r) (hl' : l' ≤ 4 * r) :
    augmentedRel F r t₀ t₁ (U₀ * S₀ * V₀ᵀ) (Ub * Sb t₁ * Vbᵀ) :=
  ⟨U₀, S₀, V₀, Uh, Vh, K, Lf, Sh, l, l', Ub, Vb, Sb, rfl, hl, hl', hs, rfl⟩

/-- A midpoint BUG step can only be started from a matrix of rank at most `r`. -/
theorem augmentedRel.rank_start_le (h : augmentedRel F r t₀ t₁ Y₀ Yh) : Y₀.rank ≤ r := by
  obtain ⟨U₀, S₀, V₀, Uh, Vh, K, Lf, Sh, l, l', Ub, Vb, Sb, rfl, -⟩ := h
  exact rank_mul_mul_transpose_le _ _ _

/-- The result of the step without truncation has rank at most `4 r`. -/
theorem augmentedRel.rank_le (h : augmentedRel F r t₀ t₁ Y₀ Yh) : Yh.rank ≤ 4 * r := by
  obtain ⟨U₀, S₀, V₀, Uh, Vh, K, Lf, Sh, l, l', Ub, Vb, Sb, -, hl, -, -, rfl⟩ := h
  calc (Ub * Sb t₁ * Vbᵀ).rank ≤ (Ub * Sb t₁).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Ub.rank := Matrix.rank_mul_le_left _ _
    _ ≤ l := by simpa using Ub.rank_le_card_width
    _ ≤ 4 * r := hl

/-- **The truncation exists.** Every result of the step without truncation has a best
approximation of rank at most `r`, so it can be completed to a step of the fixed-rank
integrator. -/
theorem augmentedRel.exists_stepRel (h : augmentedRel F r t₀ t₁ Y₀ Yh) :
    ∃ Y₁, stepRel F r t₀ t₁ Y₀ Y₁ := by
  obtain ⟨Z, hZ, hd⟩ := exists_best_approx r Yh
  exact ⟨Z, Yh, h, hZ, by rw [norm_sub_rev, hd]⟩

/-- **The truncated singular value decomposition is a truncation of the step.** The result of
the step without truncation, truncated to its `r` largest singular values, is a step of the
fixed-rank integrator: by the Eckart–Young theorem (`EckartYoung.norm_sub_truncation_le`) it is
a best approximation of rank at most `r`. -/
theorem augmentedRel.stepRel_truncation [DecidableEq n] (h : augmentedRel F r t₀ t₁ Y₀ Yh) :
    stepRel F r t₀ t₁ Y₀ (EckartYoung.truncation Yh r) :=
  ⟨Yh, h, EckartYoung.rank_truncation_le Yh r, by
    rw [norm_sub_rev]
    exact le_distLR_iff.2 fun Z hZ => EckartYoung.norm_sub_truncation_le Yh hZ⟩

/-- The result of a fixed-rank midpoint BUG step has rank at most `r`. -/
theorem stepRel.rank_le (h : stepRel F r t₀ t₁ Y₀ Y₁) : Y₁.rank ≤ r := by
  obtain ⟨Yh, -, hr, -⟩ := h
  exact hr

/-- A fixed-rank midpoint BUG step can only be started from a matrix of rank at most `r`. -/
theorem stepRel.rank_start_le (h : stepRel F r t₀ t₁ Y₀ Y₁) : Y₀.rank ≤ r := by
  obtain ⟨Yh, hYh, -, -⟩ := h
  exact hYh.rank_start_le

/-- All values of a run of the fixed-rank midpoint BUG integrator have rank at most `r`,
provided the start value has. -/
theorem IsRun.rank_le {τ : ℕ → ℝ} {N : ℕ} {Y : ℕ → Matrix m n ℝ}
    (hY : IsRun (stepRel F r) τ N Y) (h0 : (Y 0).rank ≤ r) : ∀ n ≤ N, (Y n).rank ≤ r
  | 0, _ => h0
  | n + 1, hn => (hY.step n hn).rank_le

end Rel

/-! ### Near the reference solution -/

section Tube

variable {m n k k' l l' : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype k'] [Fintype l]
  [Fintype l'] [DecidableEq k] [DecidableEq k'] [DecidableEq l] [DecidableEq l'] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} {U₀ : Matrix m (Fin r) ℝ}
  {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ} {Uh : Matrix m k ℝ}
  {Vh : Matrix n k' ℝ} {K : ℝ → Matrix m (Fin r) ℝ} {Lf : ℝ → Matrix n (Fin r) ℝ}
  {Sh : ℝ → Matrix k k' ℝ} {Ub : Matrix m l ℝ} {Vb : Matrix n l' ℝ} {Sb : ℝ → Matrix l l' ℝ}
  {A : ℝ → Matrix m n ℝ} {a b ρ B : ℝ}

/-- **The step stays in the tube.** Let `F` be bounded by `B` on the tube of radius `ρ` around a
solution `A` over `[a, b] ⊇ [t₀, t₁]`. If `‖U₀ S₀ V₀ᵀ - A t₀‖ + 2 B (t₁ - t₀) < ρ`, then the
midpoint predictor `Uh Sh(t½) Vhᵀ` and the Galerkin trajectory `Ub Sb(t) Vbᵀ`, `t ∈ [t₀, t₁]`,
lie strictly inside the tube: the half step has length `(t₁ - t₀) / 2`, and the Galerkin
trajectory starts at `Y₀` and moves with speed at most `B`. -/
theorem IsStep.norm_sub_lt_of_near (hs : IsStep F t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb)
    (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b)
    (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖U₀ * S₀ * V₀ᵀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) :
    ‖Uh * Sh ((t₀ + t₁) / 2) * Vhᵀ - A ((t₀ + t₁) / 2)‖ < ρ ∧
      ∀ t ∈ Icc t₀ t₁, ‖Ub * Sb t * Vbᵀ - A t‖ < ρ := by
  have hm0 : t₀ ≤ (t₀ + t₁) / 2 := by linarith
  have hm1 : (t₀ + t₁) / 2 ≤ t₁ := by linarith
  have e : 4 * B * ((t₀ + t₁) / 2 - t₀) = 2 * B * (t₁ - t₀) := by ring
  refine ⟨hs.half.isBUGStepCore.norm_galerkin_sub_lt_of_near hFB hB ha (hm1.trans hb)
    (hA.mono le_rfl hm1) (by rw [e]; exact hsmall) _ ⟨hm0, le_rfl⟩, fun t ht => ?_⟩
  exact (ODESolution.near_of_comp_proj (Ψ := galerkinProj Ub Vb) hs.odeSolution_galerkin
    (isOrthProj_galerkinProj hs.orthUb hs.orthVb).norm_le hFB hB ha hb hA
    (by
      change ‖Ub * Sb t₀ * Vbᵀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ
      rw [hs.start_eq]
      exact hsmall) t ht).1

/-- **Near the reference solution, the tube extension has the same steps as the field.** Let `F`
be bounded by `B` on the tube of radius `ρ` around a solution `A` over `[a, b] ⊇ [t₀, t₁]`. If
the start value satisfies `‖U₀ S₀ V₀ᵀ - A t₀‖ + 2 B (t₁ - t₀) < ρ`, then every factor step for
either field stays in the tube, so the steps for `tubeExt F A a b ρ` are exactly the steps for
`F`. -/
theorem isStep_tubeExt_iff_of_near (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B)
    (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖U₀ * S₀ * V₀ᵀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) :
    IsStep (tubeExt F A a b ρ) t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb ↔
      IsStep F t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb := by
  have hm0 : t₀ ≤ (t₀ + t₁) / 2 := by linarith
  have hm1 : (t₀ + t₁) / 2 ≤ t₁ := by linarith
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 h01)
  have hρ : 0 ≤ ρ := by linarith [norm_nonneg (U₀ * S₀ * V₀ᵀ - A t₀)]
  have h4 : ‖U₀ * S₀ * V₀ᵀ - A t₀‖ + 4 * B * ((t₀ + t₁) / 2 - t₀) < ρ := by
    have e : 4 * B * ((t₀ + t₁) / 2 - t₀) = 2 * B * (t₁ - t₀) := by ring
    rw [e]
    exact hsmall
  have hmid : (t₀ + t₁) / 2 ∈ Icc a b := ⟨ha.trans hm0, hm1.trans hb⟩
  have hGB : IsBoundedOnTube (tubeExt F A a b ρ) A a b ρ B :=
    (isBoundedField_tubeExt hFB hB hρ).isBoundedOnTube A a b ρ
  have hGA : ODESolution (tubeExt F A a b ρ) A t₀ t₁ :=
    (odeSolution_tubeExt_iff ha hb fun t _ => by simpa using hρ).2 hA
  constructor
  · intro hs
    obtain ⟨hYh, hS⟩ := hs.norm_sub_lt_of_near hGB hB ha hb h01 hGA hsmall
    exact hs.congr_field ((MatrixBUG.isRankAdaptiveStep_tubeExt_iff_of_near hFB hB ha
      (hm1.trans hb) hm0 (hA.mono le_rfl hm1) h4).1 hs.half) (tubeExt_eq hmid hYh.le).symm
      fun t ht => (tubeExt_eq ⟨ha.trans ht.1, ht.2.le.trans hb⟩
        (hS t (Ico_subset_Icc_self ht)).le).symm
  · intro hs
    obtain ⟨hYh, hS⟩ := hs.norm_sub_lt_of_near hFB hB ha hb h01 hA hsmall
    exact hs.congr_field ((MatrixBUG.isRankAdaptiveStep_tubeExt_iff_of_near hFB hB ha
      (hm1.trans hb) hm0 (hA.mono le_rfl hm1) h4).2 hs.half) (tubeExt_eq hmid hYh.le)
      fun t ht => tubeExt_eq ⟨ha.trans ht.1, ht.2.le.trans hb⟩ (hS t (Ico_subset_Icc_self ht)).le

end Tube

section TubeRel

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
  {t₀ t₁ : ℝ} {Y₀ Y₁ Yh : Matrix m n ℝ} {A : ℝ → Matrix m n ℝ} {a b ρ B : ℝ}

/-- **A step without truncation for the tube extension is a step for the field**, and
conversely, if `‖Y₀ - A t₀‖ + 2 B (t₁ - t₀) < ρ`
(`MatrixMidpointBUG.isStep_tubeExt_iff_of_near`). -/
theorem augmentedRel_tubeExt_iff_of_near (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B)
    (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) :
    augmentedRel (tubeExt F A a b ρ) r t₀ t₁ Y₀ Yh ↔ augmentedRel F r t₀ t₁ Y₀ Yh := by
  constructor
  · rintro ⟨U₀, S₀, V₀, Uh, Vh, K, Lf, Sh, l, l', Ub, Vb, Sb, rfl, hl, hl', hs, rfl⟩
    exact ((isStep_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).1 hs).augmentedRel hl hl'
  · rintro ⟨U₀, S₀, V₀, Uh, Vh, K, Lf, Sh, l, l', Ub, Vb, Sb, rfl, hl, hl', hs, rfl⟩
    exact ((isStep_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).2 hs).augmentedRel hl hl'

/-- **A fixed-rank step for the tube extension is a step for the field**, and conversely, if
`‖Y₀ - A t₀‖ + 2 B (t₁ - t₀) < ρ`. -/
theorem stepRel_tubeExt_iff_of_near (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B)
    (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) :
    stepRel (tubeExt F A a b ρ) r t₀ t₁ Y₀ Y₁ ↔ stepRel F r t₀ t₁ Y₀ Y₁ :=
  ⟨fun ⟨Yh, h, hr⟩ => ⟨Yh, (augmentedRel_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).1 h, hr⟩,
    fun ⟨Yh, h, hr⟩ => ⟨Yh, (augmentedRel_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).2 h, hr⟩⟩

end TubeRel

/-! ### Local error -/

section Error

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} {Y₀ Y₁ Yh : Matrix m n ℝ}
  {A : ℝ → Matrix m n ℝ} {a b ρ ε ε₂ L B M₁ M₂ H : ℝ}

/-- **Local error of the step without truncation, near a reference solution.** Let `F` be
`L`-Lipschitz (`L ≥ 0`) and bounded by `B` everywhere, and let the uncurried field be of class
`C²` with `‖DF‖ ≤ M₁` and `‖D²F‖ ≤ M₂` everywhere. Let the normal part of `F` be at most `ε` at
the factored points with `r` columns and at most `ε₂` at the factored points with `2 r` columns
of the tube of radius `ρ` around a solution `A` over `[a, b] ⊇ [t₀, t₁]`. If
`0 ≤ h = t₁ - t₀ ≤ H` and `‖Y₀ - A t₀‖ + 2 B h < ρ`, then every step of
`MatrixMidpointBUG.augmentedRel F r` from `Y₀` has local error `C h (h² + h ε + ε₂)` with
`C = midpointBUGConst L M₁ B (M₂ (1 + B)² + M₁² (1 + B)) H` (arXiv:2402.08607, Theorem 1, 4r
variant). The margin keeps the results of the K- and L-step and the midpoint predictor in the
tube, where the normal bounds are evaluated. -/
theorem augmentedRel.hasLocalError (h : augmentedRel F r t₀ t₁ Y₀ Yh)
    (hε : FactoredNormalBoundOn F r (tubeSet A a b ρ) ε)
    (hε₂ : FactoredNormalBoundOn F (2 * r) (tubeSet A a b ρ) ε₂)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hF₂ : ContDiff ℝ 2 (Function.uncurry F))
    (hM₁ : ∀ p, ‖fderiv ℝ (Function.uncurry F) p‖ ≤ M₁)
    (hM₂ : ∀ p, ‖iteratedFDeriv ℝ 2 (Function.uncurry F) p‖ ≤ M₂)
    (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hH : t₁ - t₀ ≤ H)
    (hA : ODESolution F A t₀ t₁) (hsmall : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ Y₀ Yh
      (MidpointBUG.midpointBUGConst L M₁ B (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) H * (t₁ - t₀) *
        ((t₁ - t₀) ^ 2 + (t₁ - t₀) * ε + ε₂)) := by
  obtain ⟨U₀, S₀, V₀, Uh, Vh, K, Lf, Sh, l, l', Ub, Vb, Sb, rfl, -, -, hs, rfl⟩ := h
  have hB0 : 0 ≤ B := hB.nonneg
  have hFB : IsBoundedOnTube F A a b ρ B := fun t _ x _ => hB t x
  have hm0 : t₀ ≤ (t₀ + t₁) / 2 := by linarith
  have hm1 : (t₀ + t₁) / 2 ≤ t₁ := by linarith
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB0 (sub_nonneg.2 h01)
  have h2 : ‖U₀ * S₀ * V₀ᵀ - A t₀‖ + 2 * B * ((t₀ + t₁) / 2 - t₀) < ρ := by
    have e : 2 * B * ((t₀ + t₁) / 2 - t₀) = B * (t₁ - t₀) := by ring
    rw [e]
    linarith
  have hmem := hs.half.isBUGStepCore.toBasisUpdate.mem_tubeSet_of_near hFB hB0 ha (hm1.trans hb)
    hm0 (hA.mono le_rfl hm1) h2
  obtain ⟨hYh, -⟩ := hs.norm_sub_lt_of_near hFB hB0 ha hb h01 hA hsmall
  exact hs.hasLocalError (fun t ht => hs.half.norm_kNormal_le hε (hmem 0 t ht))
    (fun t ht => hs.half.norm_lNormal_le hε (hmem 1 t ht))
    (hε₂ _ Uh Vh _ hs.half.orthUa hs.half.orthVa ⟨⟨ha.trans hm0, hm1.trans hb⟩, hYh.le⟩)
    hF hL hB hF₂ hM₁ hM₂ h01 hH

/-- **Local error of the fixed-rank midpoint BUG step near a reference solution.** Under the
hypotheses of `MatrixMidpointBUG.augmentedRel.hasLocalError`, with `ε ≥ 0`, `A` continuous on
`[a, b]` and the larger margin `‖Y₀ - A t₀‖ + 3 B h < ρ`, every step of
`MatrixMidpointBUG.stepRel F r` from `Y₀` has local error

  `h (e^{L H} ε + 2 C (h² + h ε + ε₂))`,  `h = t₁ - t₀`,

with `C = midpointBUGConst L M₁ B (M₂ (1 + B)² + M₁² (1 + B)) H`. The step without truncation
contributes `C h (h² + h ε + ε₂)`. The truncation to rank `r` is a best approximation, so it
costs at most the distance of the exact solution `Φ t₁` to the matrices of rank at most `r` plus
twice the error before truncation (`norm_bestTrunc_sub_le`), and this distance is at most
`h ε e^{L h}` (`distLR_flow_le_exp_of_tube`), without a term `h²`. -/
theorem stepRel.hasLocalError (h : stepRel F r t₀ t₁ Y₀ Y₁)
    (hε : FactoredNormalBoundOn F r (tubeSet A a b ρ) ε) (hε₀ : 0 ≤ ε)
    (hε₂ : FactoredNormalBoundOn F (2 * r) (tubeSet A a b ρ) ε₂)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hF₂ : ContDiff ℝ 2 (Function.uncurry F))
    (hM₁ : ∀ p, ‖fderiv ℝ (Function.uncurry F) p‖ ≤ M₁)
    (hM₂ : ∀ p, ‖iteratedFDeriv ℝ 2 (Function.uncurry F) p‖ ≤ M₂)
    (hAc : ContinuousOn A (Icc a b)) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁)
    (hH : t₁ - t₀ ≤ H) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + 3 * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ Y₀ Y₁ ((t₁ - t₀) * (Real.exp (L * H) * ε +
      2 * MidpointBUG.midpointBUGConst L M₁ B (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) H *
        ((t₁ - t₀) ^ 2 + (t₁ - t₀) * ε + ε₂))) := by
  obtain ⟨Yh, hYh, -, htr⟩ := h
  intro Φ hΦ hΦ₀
  have hB0 : 0 ≤ B := hB.nonneg
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB0 (sub_nonneg.2 h01)
  have h₁ := hYh.hasLocalError hε hε₂ hF hL hB hF₂ hM₁ hM₂ ha hb h01 hH hA (by linarith) Φ hΦ
    hΦ₀
  have h₂ := distLR_flow_le_exp_of_tube hε hε₀ (fun t _ x y _ _ => hF t x y) hL
    (fun t _ x _ => hB t x) hB0 hF₂.continuous.continuousOn hAc ha hb h01 hA hΦ
    (by rw [hΦ₀]; exact hYh.rank_start_le) (by rwa [hΦ₀])
  have h₃ := norm_bestTrunc_sub_le (A₁ := Φ t₁) htr
  have hexp : (t₁ - t₀) * ε * Real.exp (L * (t₁ - t₀)) ≤ (t₁ - t₀) * ε * Real.exp (L * H) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hH hL))
      (mul_nonneg (sub_nonneg.2 h01) hε₀)
  set C := MidpointBUG.midpointBUGConst L M₁ B (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) H
  set X := (t₁ - t₀) ^ 2 + (t₁ - t₀) * ε + ε₂
  have e : (t₁ - t₀) * (Real.exp (L * H) * ε + 2 * C * X) =
      (t₁ - t₀) * ε * Real.exp (L * H) + 2 * (C * (t₁ - t₀) * X) := by ring
  rw [e]
  linarith

end Error

end MatrixMidpointBUG

end LeanDLRA
