import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.Exactness
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Matrix.Interpolation
import LeanDLRA.Research.IntegratorErrorOrder
import LeanDLRA.Randomized.RandomizedBUG

/-!
# Carrel, *Randomized methods for dynamical low-rank approximation* (arXiv 2410.17091)

This module formalizes the deterministic, finite-dimensional content of B. Carrel, *Randomized
methods for dynamical low-rank approximation*, arXiv 2410.17091 (v3, single author; earlier
versions of this file and of `LeanDLRA.RandomizedBUG` wrongly attributed the paper to
Lam–Ceruti–Kressner): the dynamical rangefinder (§2), the dynamical randomized SVD (DRSVD, §3.1)
and the dynamical generalized Nyström method (DGN, §3.2).  Matrices carry the Frobenius norm and
the vector field may depend on time (the paper's autonomous `F` is a special case).  The Gaussian
sketch enters the paper only through "`Vᵀ Ω` has full row rank with probability one"; here this is
the hypothesis that `Vᵀ Ω` has a right inverse `R`, so every result is deterministic.  Not
formalized: that almost-sure statement, the cited Theorem 1.1 (Halko–Martinsson–Tropp) and
Lemma 2.2 (Gaussian norm estimate), the rank-adaptive variants (§2.3, §3.3), the heuristic
`B(h) ≈ A(h) Ω`, and the numerical experiments (§4).

## Main results

* **Lemma 2.1** (idealized dynamical rangefinder `ℬ' = F(A(t)) Ω`, `ℬ(0) = A₀ Ω`):
  `sketch_exact` (`ℬ(t) = A(t) Ω`, the identity in the proof and the remark after the lemma),
  `dynamical_rangefinder_exact`, `range_mul_sketch_eq`, `dynamical_rangefinder_capture`, and the
  full statement `idealized_rangefinder_range_eq`: `Range(Q_h) = Range(A(h))` and
  `A(h) - Q_h Q_hᵀ A(h) = 0`.  The paper says "fix a sketch matrix Ω"; its proof needs the
  full-row-rank condition, and `sketch_range_ne` shows the conclusion fails without it.
* **Eq. (7)** (practical B-step `B' = F(B Ω†) Ω`): `gramPinv`, `projOmega`,
  `projOmega_isOrthProj`, `bStep_iff_projected`; bridges to the core
  (`projOmega_eq_obliqueProj`, `isOrthProjMat_projOmega`, `isOrthProj_rightMulCLM_projOmega`,
  `gramPinv_mul_right`, `projOmega_mul_right`); and the chain `isDRSVDStep_of_sketch`: one
  DRSVD step with the paper's B-step for any sketch `Ω = W R` (`W` orthonormal, `R` invertible)
  whose range contains the row space of `Y₀` is a core `RandomizedBUG.IsDRSVDStep`, so the
  robust bounds `IsDRSVDStep.local_error` and `RandomizedBUG.drsvd_global_error` apply.  The
  paper's plain Gaussian `Ω` is not augmented in this sense (see `LeanDLRA.RandomizedBUG`).
* **Lemma 3.1** (idealized DRSVD): `idealized_drsvd_exact`; with the optional truncation the
  method is exact iff `rank A(h) ≤ r`.  An `example` in `RankCounterexample` instantiates it.
* **Lemmas 3.2 and 3.3 are false as printed** (hypothesis `rank A(h) ≤ r + p`; both outputs
  have rank `≤ r`): `RankCounterexample.drsvd_counterexample` and
  `RankCounterexample.dgn_counterexample` run the complete algorithms (B-step (7), `Q_h`,
  `Q = orth[U₀, Q_h]` as in (13), `W` as in (15) from the transposed rangefinder, C-step (14),
  BCD-step (16), assembly (17)) with `r = p = 1`, `ℓ = q = 0`, `m = n = 3`, verify every printed
  hypothesis, and show that the outputs differ from `A(1)` (`rank A(1) = 2 = r + p`);
  `RankCounterexample.truncation_ne_A_one` shows that this holds for every sketch.  The
  corrected statements (`rank A(h) ≤ r`) are the core theorems `RandomizedBUG.drsvd_exact_iff`
  and `RandomizedBUG.dgn_exact`.
* **Remark after Lemma 3.2** ("the assumption is satisfied in the limit case
  `(r + p) = min{m, n}`"): true for `r + p = m` (`range_inclusion_of_square`), false for
  `r + p = n < m` (`LimitCase.counterexample`, `m = 3`, `n = 1`, `r = 1`, `p = 0`).
* **Algorithm 4, steps 6–9**: `svd_pinv_penrose` (`Ṽ_r Σ_r⁻¹ Ũ_rᵀ` is the Moore–Penrose inverse
  of `Ũ_r Σ_r Ṽ_rᵀ`, so it is a `{1}`-inverse as required by `RandomizedBUG.dgn_exact`) and
  `dgn_assembly_eq` (`U₁ S₁ V₁ᵀ = B(h) T_r(D(h))† C(h)ᵀ`, i.e. the algorithm computes (17)).

Core definitions used: `ODESolution`, `IsDerivRHS`, `IsOrthProj`, `leftProj`, `rightProj`,
`Curvature.IsOrthProjMat`, `obliqueProj`, `EckartYoung.truncation`,
`RandomizedBUG.IsDRSVDStep`.  Local definitions: `gramPinv` and `projOmega` (the paper's `Ω†` and
`Ω Ω†`; `projOmega_eq_obliqueProj` identifies `projOmega Ω` with the core `obliqueProj Ω Ω`; they
are kept because the paper writes the B-step with `Ω†`), and the concrete matrices of the
counterexamples.  Duplicates outside the core: `Novel.OpRS34.pinvT` and `Novel.OpTR37.pinv` are
the same matrix as `gramPinv`.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2410_17091

variable {m n k l s : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype l] [Fintype s]

/-! ## Lemma 2.1: the idealized dynamical rangefinder -/

/-- **Idealized B-step is the sketch of the exact flow** (arXiv 2410.17091, §2.1: the identity
`ℬ(h) = A(h) Ω` in the proof of Lemma 2.1 and the remark after it).  If `A' = F(t, A)` on
`[t₀, t₁]` and `ℬ' = F(t, A(t)) Ω` with `ℬ(t₀) = A(t₀) Ω`, then `ℬ(t) = A(t) Ω` on `[t₀, t₁]`.
The paper's `F` is autonomous; time dependence is allowed here. -/
theorem sketch_exact {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A : ℝ → Matrix m n ℝ}
    {Ω : Matrix n k ℝ} {B : ℝ → Matrix m k ℝ} {t₀ t₁ : ℝ}
    (hA : ODESolution F A t₀ t₁)
    (hB : ODESolution (fun t _ => F t (A t) * Ω) B t₀ t₁) (hB₀ : B t₀ = A t₀ * Ω) :
    ∀ t ∈ Icc t₀ t₁, B t = A t * Ω := by
  intro t ht
  have h := hB.eq_add_map_sub (Frobenius.rightMulCLM Ω) (A' := fun t => F t (A t)) hA.cont
    (fun t ht' => hA.deriv t ht') (fun _ _ => rfl) t ht
  rw [Frobenius.rightMulCLM_apply] at h
  rw [h, hB₀, Matrix.sub_mul]
  abel

omit [Fintype m] in
/-- **Lemma 2.1, deterministic core** (arXiv 2410.17091, Lemma 2.1, the step "`W = V_hᵀ Ω` has
full row rank").  Suppose `A = X Vᵀ` (so `rank A ≤ s`, with `s = r + p` and `V` a basis of the row
space) and `Vᵀ Ω R = 1` for some `R` (full row rank of `Vᵀ Ω`, which the paper obtains with
probability one for a Gaussian `Ω`; here it is a hypothesis).  Then `A = A Ω (R Vᵀ)` and
`rank (A Ω) = rank A`. -/
theorem dynamical_rangefinder_exact [DecidableEq s] {A : Matrix m n ℝ} {Ω : Matrix n k ℝ}
    {X : Matrix m s ℝ} {V : Matrix n s ℝ} (hA : A = X * Vᵀ) {R : Matrix k s ℝ}
    (hR : Vᵀ * Ω * R = 1) :
    A = A * Ω * (R * Vᵀ) ∧ (A * Ω).rank = A.rank := by
  have hA' : A = A * Ω * (R * Vᵀ) := by
    have e : A * Ω * (R * Vᵀ) = X * (Vᵀ * Ω * R) * Vᵀ := by
      rw [hA]; simp only [Matrix.mul_assoc]
    rw [e, hR, Matrix.mul_one, hA]
  refine ⟨hA', le_antisymm (Matrix.rank_mul_le_left _ _) ?_⟩
  calc A.rank = (A * Ω * (R * Vᵀ)).rank := by rw [← hA']
    _ ≤ (A * Ω).rank := Matrix.rank_mul_le_left _ _

omit [Fintype m] in
/-- **Lemma 2.1, range equality** (arXiv 2410.17091, Lemma 2.1, `Range(ℬ(h)) = Range(A(h))`
with `ℬ(h) = A(h) Ω`): under the hypotheses of `dynamical_rangefinder_exact`, the column spaces
of `A Ω` and `A` coincide. -/
theorem range_mul_sketch_eq [DecidableEq s] {A : Matrix m n ℝ} {Ω : Matrix n k ℝ}
    {X : Matrix m s ℝ} {V : Matrix n s ℝ} (hA : A = X * Vᵀ) {R : Matrix k s ℝ}
    (hR : Vᵀ * Ω * R = 1) :
    LinearMap.range (A * Ω).mulVecLin = LinearMap.range A.mulVecLin := by
  refine le_antisymm ?_ ?_
  · rw [Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  · calc LinearMap.range A.mulVecLin
        = LinearMap.range (A * Ω * (R * Vᵀ)).mulVecLin := by
          rw [← (dynamical_rangefinder_exact hA hR).1]
      _ ≤ LinearMap.range (A * Ω).mulVecLin := by
          rw [Matrix.mulVecLin_mul]
          exact LinearMap.range_comp_le_range _ _

/-- **Range part of Lemma 2.1: capture** (arXiv 2410.17091, Lemma 2.1,
`‖A(h) - Q_h Q_hᵀ A(h)‖ = 0`).  Under the hypotheses of `dynamical_rangefinder_exact`, any `Q`
with `Q Qᵀ (A Ω) = A Ω` also satisfies `Q Qᵀ A = A`. -/
theorem dynamical_rangefinder_capture [DecidableEq s] {A : Matrix m n ℝ} {Ω : Matrix n k ℝ}
    {X : Matrix m s ℝ} {V : Matrix n s ℝ} (hA : A = X * Vᵀ) {R : Matrix k s ℝ}
    (hR : Vᵀ * Ω * R = 1) {Q : Matrix m l ℝ} (hcap : Q * Qᵀ * (A * Ω) = A * Ω) :
    Q * Qᵀ * A = A :=
  RandomizedBUG.capture_of_sketch hcap ⟨R * Vᵀ, (dynamical_rangefinder_exact hA hR).1⟩

/-- **Lemma 2.1** (arXiv 2410.17091, Lemma 2.1, deterministic form).  Let `A` solve
`A' = F(t, A)`, let `ℬ` solve the idealized B-step (6) `ℬ' = F(t, A(t)) Ω`, `ℬ(t₀) = A(t₀) Ω`,
and let `Q = orth(ℬ(t₁))`, i.e. `Q Qᵀ ℬ(t₁) = ℬ(t₁)` and `Q = ℬ(t₁) M` for some `M`.  If
`A(t₁) = X Vᵀ` with `s = r + p` columns (`rank A(t₁) ≤ r + p`) and `Vᵀ Ω` has a right inverse,
then `Range(Q) = Range(A(t₁))` and `A(t₁) - Q Qᵀ A(t₁) = 0`.  Deviation: the paper fixes a
Gaussian `Ω` and uses that `Vᵀ Ω` has full row rank with probability one; here that is the
hypothesis `hR` (`sketch_range_ne` shows it cannot be dropped).  Orthonormality of `Q` is not
needed. -/
theorem idealized_rangefinder_range_eq [DecidableEq s] {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {A : ℝ → Matrix m n ℝ} {Ω : Matrix n k ℝ} {B : ℝ → Matrix m k ℝ} {t₀ t₁ : ℝ}
    (ht : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hB : ODESolution (fun t _ => F t (A t) * Ω) B t₀ t₁) (hB₀ : B t₀ = A t₀ * Ω)
    {X : Matrix m s ℝ} {V : Matrix n s ℝ} (hX : A t₁ = X * Vᵀ) {R : Matrix k s ℝ}
    (hR : Vᵀ * Ω * R = 1) {Q : Matrix m l ℝ} (hcap : Q * Qᵀ * B t₁ = B t₁)
    (hspan : ∃ M : Matrix k l ℝ, Q = B t₁ * M) :
    LinearMap.range Q.mulVecLin = LinearMap.range (A t₁).mulVecLin ∧
      A t₁ - Q * Qᵀ * A t₁ = 0 := by
  have hBA : B t₁ = A t₁ * Ω := sketch_exact hA hB hB₀ t₁ ⟨ht, le_rfl⟩
  obtain ⟨M, hM⟩ := hspan
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · rw [← range_mul_sketch_eq hX hR, ← hBA, hM, Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  · rw [← range_mul_sketch_eq hX hR, ← hBA, ← hcap, Matrix.mul_assoc, Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  · rw [dynamical_rangefinder_capture hX hR (by rw [← hBA]; exact hcap), sub_self]

/-- **Lemma 2.1 needs a generic sketch** (arXiv 2410.17091, Lemma 2.1 says "fix a sketch matrix
`Ω`").  For `A = e₁ e₁ᵀ` (rank `1 = r + p`) and the sketch `Ω = e₂`, the sketch `A Ω` vanishes,
so `Range(A Ω) ≠ Range(A)`: the conclusion holds only for sketches with `Vᵀ Ω` of full row rank
(almost every Gaussian `Ω`, as the paper's proof uses). -/
theorem sketch_range_ne :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℝ) (Ω : Matrix (Fin 2) (Fin 1) ℝ),
      A.rank ≤ 1 ∧ A * Ω = 0 ∧
        LinearMap.range (A * Ω).mulVecLin ≠ LinearMap.range A.mulVecLin := by
  have hA : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)
      = (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ) * (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  have hAΩ : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) * (!![0; 1] : Matrix (Fin 2) (Fin 1) ℝ)
      = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  refine ⟨!![1, 0; 0, 0], !![0; 1], ?_, hAΩ, ?_⟩
  · rw [hA]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)
  · intro h
    have hmem := LinearMap.mem_range_self
      (Matrix.mulVecLin (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)) (Pi.single 0 1)
    rw [← h, hAΩ, Matrix.mulVecLin_zero, LinearMap.range_zero, Submodule.mem_bot] at hmem
    have := congrFun hmem 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this

/-- Non-vacuity of `dynamical_rangefinder_exact` with a non-identity sketch: `A = 𝟙 𝟙ᵀ` on
`ℝ^{2×2}` (rank one, `V = 𝟙`), the one-column sketch `Ω = e₁` and `R = 1` (`Vᵀ Ω = 1`). -/
example : (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)
    = (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) * (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)
      * ((1 : Matrix (Fin 1) (Fin 1) ℝ) * (!![1; 1] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ) :=
  (dynamical_rangefinder_exact (X := (!![1; 1] : Matrix (Fin 2) (Fin 1) ℝ))
    (V := (!![1; 1] : Matrix (Fin 2) (Fin 1) ℝ))
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply])
    (by ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply, Fin.sum_univ_two])).1

/-! ## The pseudo-inverse projection of eq. (7) -/

section Projection

variable [DecidableEq k]

/-- The full-column-rank pseudo-inverse `Ω† = (ΩᵀΩ)⁻¹ Ωᵀ` of an `n × k` sketch
(arXiv 2410.17091, §2.2, step 1).  The same matrix as the core `obliqueProj` factor, see
`projOmega_eq_obliqueProj`. -/
noncomputable def gramPinv (Ω : Matrix n k ℝ) : Matrix k n ℝ := (Ωᵀ * Ω)⁻¹ * Ωᵀ

/-- The orthogonal projector `Π_Ω = Ω Ω† = Ω (ΩᵀΩ)⁻¹ Ωᵀ` onto `range Ω` (equal to the core
`obliqueProj Ω Ω` by `projOmega_eq_obliqueProj`). -/
noncomputable def projOmega (Ω : Matrix n k ℝ) : Matrix n n ℝ := Ω * gramPinv Ω

variable {Ω : Matrix n k ℝ}

/-- `Ω† Ω = I` when `ΩᵀΩ` is invertible. -/
lemma gramPinv_mul_self (h : IsUnit (Ωᵀ * Ω).det) : gramPinv Ω * Ω = 1 := by
  unfold gramPinv
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h]

/-- `Ω Ω† Ω = Ω`. -/
lemma projOmega_mul_self (h : IsUnit (Ωᵀ * Ω).det) : projOmega Ω * Ω = Ω := by
  unfold projOmega
  rw [Matrix.mul_assoc, gramPinv_mul_self h, Matrix.mul_one]

/-- `Π_Ω` is an orthogonal projector: idempotent and symmetric. -/
theorem projOmega_isOrthProj (h : IsUnit (Ωᵀ * Ω).det) :
    projOmega Ω * projOmega Ω = projOmega Ω ∧ (projOmega Ω)ᵀ = projOmega Ω := by
  refine ⟨?_, ?_⟩
  · have hc : gramPinv Ω * (Ω * gramPinv Ω) = gramPinv Ω := by
      rw [← Matrix.mul_assoc, gramPinv_mul_self h, Matrix.one_mul]
    unfold projOmega
    rw [Matrix.mul_assoc Ω (gramPinv Ω) (Ω * gramPinv Ω), hc]
  · have hG : ((Ωᵀ * Ω)⁻¹)ᵀ = (Ωᵀ * Ω)⁻¹ := by
      rw [Matrix.transpose_nonsing_inv, Matrix.transpose_mul, Matrix.transpose_transpose]
    unfold projOmega gramPinv
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hG, Matrix.mul_assoc]

/-- **Bridge to the core oblique projector**: `Π_Ω = Ω (ΩᵀΩ)⁻¹ Ωᵀ = obliqueProj Ω Ω`. -/
theorem projOmega_eq_obliqueProj (Ω : Matrix n k ℝ) : projOmega Ω = obliqueProj Ω Ω := by
  simp only [projOmega, gramPinv, obliqueProj, Matrix.mul_assoc]

/-- **Bridge to the core matrix projector predicate**: `Π_Ω` is an `IsOrthProjMat`. -/
theorem isOrthProjMat_projOmega (h : IsUnit (Ωᵀ * Ω).det) :
    Curvature.IsOrthProjMat (projOmega Ω) :=
  ⟨(projOmega_isOrthProj h).2, (projOmega_isOrthProj h).1⟩

/-- **Bridge to the core projector predicate**: `X ↦ X Π_Ω` is an orthogonal projector
(`IsOrthProj`) on `ℝ^{m × n}` with the Frobenius inner product. -/
theorem isOrthProj_rightMulCLM_projOmega (h : IsUnit (Ωᵀ * Ω).det) :
    IsOrthProj (Frobenius.rightMulCLM (projOmega Ω) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) :=
  ErrorOrder.isOrthProj_rightMulCLM (projOmega_isOrthProj h).1 (projOmega_isOrthProj h).2

/-- **Eq. (7) as a projected trajectory** (arXiv 2410.17091, eq. (7); the reformulation is not
stated in the paper).  For a sketch `Ω` of full column rank, `B' = F(B Ω†) Ω` holds if and only if
`Y = B Ω†` solves `Y' = F(Y) Π_Ω`, i.e. the dynamical range finder is a BUG-type K-step with the
random projector `Π_Ω`. -/
theorem bStep_iff_projected {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    (h : IsUnit (Ωᵀ * Ω).det) {Bs : ℝ → Matrix m k ℝ} {a b : ℝ} :
    ODESolution (fun t B => F t (B * gramPinv Ω) * Ω) Bs a b ↔
      ODESolution (fun t Y => F t Y * projOmega Ω) (fun t => Bs t * gramPinv Ω) a b := by
  have hG := gramPinv_mul_self h
  constructor
  · intro hB
    refine RandomizedBUG.odeSolution_map hB (Frobenius.rightMulCLM (gramPinv Ω)) ?_
    intro t _
    simp only [Frobenius.rightMulCLM_apply, projOmega, Matrix.mul_assoc]
  · intro hY
    have h2 := RandomizedBUG.odeSolution_map hY (Frobenius.rightMulCLM Ω)
      (g := fun t B => F t (B * gramPinv Ω) * Ω) ?_
    · convert h2 using 1
      funext t
      simp only [Frobenius.rightMulCLM_apply, Matrix.mul_assoc, hG, Matrix.mul_one]
    · intro t _
      simp only [Frobenius.rightMulCLM_apply, projOmega, Matrix.mul_assoc, hG, Matrix.mul_one]

/-- For `Ω = W R` with orthonormal `W` and invertible `R`, `ΩᵀΩ = RᵀR` is invertible. -/
lemma isUnit_det_gram_mul_right {W : Matrix n k ℝ} (hW : Wᵀ * W = 1) {R : Matrix k k ℝ}
    (hR : IsUnit R.det) : IsUnit ((W * R)ᵀ * (W * R)).det := by
  have hG : (W * R)ᵀ * (W * R) = Rᵀ * R := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Wᵀ, hW, Matrix.one_mul]
  rw [hG, Matrix.det_mul, Matrix.det_transpose]
  exact hR.mul hR

/-- For `Ω = W R` (`W` orthonormal, `R` invertible): `Ω† = R⁻¹ Wᵀ`. -/
theorem gramPinv_mul_right {W : Matrix n k ℝ} (hW : Wᵀ * W = 1) {R : Matrix k k ℝ}
    (hR : IsUnit R.det) : gramPinv (W * R) = R⁻¹ * Wᵀ := by
  have hRt : IsUnit Rᵀ.det := by rwa [Matrix.det_transpose]
  have hG : (W * R)ᵀ * (W * R) = Rᵀ * R := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Wᵀ, hW, Matrix.one_mul]
  unfold gramPinv
  rw [hG, Matrix.mul_inv_rev, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Rᵀ⁻¹,
    Matrix.nonsing_inv_mul _ hRt, Matrix.one_mul]

/-- **The random projector only depends on the range of the sketch**: for `Ω = W R` (`W`
orthonormal, `R` invertible), `Π_Ω = W Wᵀ`, from the core `obliqueProj_self_mul_right`.  Hence
`X ↦ X Π_Ω` is the core `rightProj W`. -/
theorem projOmega_mul_right {W : Matrix n k ℝ} (hW : Wᵀ * W = 1) {R : Matrix k k ℝ}
    (hR : IsUnit R.det) : projOmega (W * R) = W * Wᵀ := by
  rw [projOmega_eq_obliqueProj]
  exact obliqueProj_self_mul_right hW hR

/-- **The paper's B-step feeds the core robust DRSVD analysis** (arXiv 2410.17091, eqs. (7),
(13), (14) and Algorithm 3 with `q = 0`; chain to `RandomizedBUG.IsDRSVDStep`).  Let the sketch
be `Ω = W R` with orthonormal `W` and invertible `R` (every sketch of full column rank has this
form), let `B' = F(B Ω†) Ω`, `B(t₀) = Y₀ Ω` (eq. (7)), let `Q` be orthonormal with
`Q Qᵀ B(t₁) = B(t₁)`, let `C' = F(Q Cᵀ)ᵀ Q`, `C(t₀) = Y₀ᵀ Q` (eq. (14)), and let `Y₁` be within
`ϑ` of `Q C(t₁)ᵀ` (e.g. its truncation `T_r`).  If the sketch is augmented, `Y₀ W Wᵀ = Y₀`, and
`ε` bounds the doubly-normal part of `F` at `Y_B(t₁) = B(t₁) Ω†`, then these data form an
`IsDRSVDStep` with the projectors `rightProj W` and `leftProj Q`; hence
`IsDRSVDStep.local_error` and `RandomizedBUG.drsvd_global_error` bound the error of the paper's
method.  Deviation: the paper sketches with a plain Gaussian `Ω`, which is not augmented (the
augmentation hypothesis `haug` fails almost surely); this theorem covers the augmented variant. -/
theorem isDRSVDStep_of_sketch [DecidableEq l] {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {ε ϑ t₀ t₁ : ℝ} {Y₀ Y₁ : Matrix m n ℝ} {W : Matrix n k ℝ} (hW : Wᵀ * W = 1)
    {R : Matrix k k ℝ} (hR : IsUnit R.det) {Q : Matrix m l ℝ} (hQ : Qᵀ * Q = 1)
    {Bs : ℝ → Matrix m k ℝ}
    (hB : ODESolution (fun t B => F t (B * gramPinv (W * R)) * (W * R)) Bs t₀ t₁)
    (hB₀ : Bs t₀ = Y₀ * (W * R)) (haug : Y₀ * W * Wᵀ = Y₀) (hcap : Q * Qᵀ * Bs t₁ = Bs t₁)
    (hε : ∀ t ∈ Icc t₀ t₁,
      ‖(1 - leftProj Q) ((1 - rightProj W) (F t (Bs t₁ * gramPinv (W * R))))‖ ≤ ε)
    {Cs : ℝ → Matrix n l ℝ} (hC : ODESolution (fun t C => (F t (Q * Cᵀ))ᵀ * Q) Cs t₀ t₁)
    (hC₀ : Cs t₀ = Y₀ᵀ * Q) (htr : ‖Y₁ - Q * (Cs t₁)ᵀ‖ ≤ ϑ) :
    RandomizedBUG.IsDRSVDStep F ε ϑ (rightProj W) (leftProj Q) t₀ t₁ Y₀
      (fun t => Bs t * gramPinv (W * R)) (fun t => Q * (Cs t)ᵀ) Y₁ where
  projΩ := isOrthProj_rightProj hW
  projP := isOrthProj_leftProj hQ
  bSol := by
    have h := (bStep_iff_projected (isUnit_det_gram_mul_right hW hR)).1 hB
    have hf : (fun t Y => F t Y * projOmega (W * R)) = fun t Y => rightProj W (F t Y) := by
      funext t Y
      rw [projOmega_mul_right hW hR, rightProj_apply, Matrix.mul_assoc]
    rwa [hf] at h
  bStart := by
    have hP : W * R * gramPinv (W * R) = W * Wᵀ := projOmega_mul_right hW hR
    change Bs t₀ * gramPinv (W * R) = Y₀
    rw [hB₀, Matrix.mul_assoc, hP, ← Matrix.mul_assoc, haug]
  rangeCap := by
    change Q * Qᵀ * (Bs t₁ * gramPinv (W * R)) = Bs t₁ * gramPinv (W * R)
    rw [← Matrix.mul_assoc, hcap]
  bNormal := hε
  cSol := RandomizedBUG.cStep_full hC
  cStart := by
    simp only [hC₀, leftProj_apply, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc]
  trunc := htr

end Projection

/-! ## Lemma 3.1: the idealized dynamical randomized SVD -/

/-- **Lemma 3.1** (arXiv 2410.17091, Lemma 3.1, deterministic form).  With the idealized
rangefinder of `idealized_rangefinder_range_eq` (only the capture `Q Qᵀ ℬ(t₁) = ℬ(t₁)` is used)
and the idealized C-step (12) `C' = F(t, A(t))ᵀ Q`, `C(t₀) = A(t₀)ᵀ Q`: `C(t₁) = A(t₁)ᵀ Q` and
`A₁ = Q C(t₁)ᵀ = A(t₁)` (the paper's `A₁ = Q Ũ Σ Vᵀ` with `Ũ Σ Vᵀ = svd(C(h)ᵀ)` is `Q C(h)ᵀ`).
With the optional truncation mentioned before the lemma, `T_r(A₁) = A(t₁)` iff
`rank A(t₁) ≤ r`.  Deviation: the full-row-rank property of `Vᵀ Ω` (almost sure for a Gaussian
`Ω` in the paper) is the hypothesis `hR`. -/
theorem idealized_drsvd_exact [DecidableEq s] [DecidableEq n]
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A : ℝ → Matrix m n ℝ} {Ω : Matrix n k ℝ}
    {B : ℝ → Matrix m k ℝ} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hB : ODESolution (fun t _ => F t (A t) * Ω) B t₀ t₁) (hB₀ : B t₀ = A t₀ * Ω)
    {X : Matrix m s ℝ} {V : Matrix n s ℝ} (hX : A t₁ = X * Vᵀ) {R : Matrix k s ℝ}
    (hR : Vᵀ * Ω * R = 1) {Q : Matrix m l ℝ} (hcap : Q * Qᵀ * B t₁ = B t₁)
    {C : ℝ → Matrix n l ℝ} (hC : ODESolution (fun t _ => (F t (A t))ᵀ * Q) C t₀ t₁)
    (hC₀ : C t₀ = (A t₀)ᵀ * Q) :
    C t₁ = (A t₁)ᵀ * Q ∧ Q * (C t₁)ᵀ = A t₁ ∧
      ∀ r : ℕ, EckartYoung.truncation (Q * (C t₁)ᵀ) r = A t₁ ↔ (A t₁).rank ≤ r := by
  have hD : IsDerivRHS (fun t _ => F t (A t)) A t₀ t₁ :=
    ⟨hA.cont, fun t ht _ => hA.deriv t ht⟩
  have hBA : B t₁ = A t₁ * Ω := sketch_exact hA hB hB₀ t₁ ⟨ht, le_rfl⟩
  have hcapA : Q * Qᵀ * A t₁ = A t₁ :=
    dynamical_rangefinder_capture hX hR (by rw [← hBA]; exact hcap)
  refine ⟨(RandomizedBUG.cStep_exact hD hC hC₀ t₁ ⟨ht, le_rfl⟩).1,
    (RandomizedBUG.drsvd_exact_iff ht hD hC hC₀ hcapA 0).1,
    fun r => (RandomizedBUG.drsvd_exact_iff ht hD hC hC₀ hcapA r).2⟩

/-! ## Lemmas 3.2 and 3.3 as printed: a complete counterexample -/

namespace RankCounterexample

/-- `e₁ ∈ ℝ^{3×1}`: the initial bases `U₀ = V₀ = e₁` (`r = 1`). -/
noncomputable def e₁ : Matrix (Fin 3) (Fin 1) ℝ := !![1; 0; 0]

/-- `Y₀ = A₀ = e₁ e₁ᵀ = diag(1, 0, 0)`. -/
noncomputable def Y₀ : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 0, 0; 0, 0, 0]

/-- `G = diag(-1, 1, 1)`. -/
noncomputable def G : Matrix (Fin 3) (Fin 3) ℝ := !![-1, 0, 0; 0, 1, 0; 0, 0, 1]

/-- The autonomous vector field `F ≡ G`. -/
noncomputable def F : ℝ → Matrix (Fin 3) (Fin 3) ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun _ _ => G

/-- The exact solution `A(t) = Y₀ + t G = diag(1 - t, t, t)`. -/
noncomputable def A (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := Y₀ + t • G

/-- The sketch `Ω = [e₂, e₃]` (`r + p = 2` columns, orthonormal, hence `Ω† = Ωᵀ`). -/
noncomputable def Ω : Matrix (Fin 3) (Fin 2) ℝ := !![0, 0; 1, 0; 0, 1]

/-- The range basis `Q = I₃` (`2r + p = 3` columns) and the co-range basis `W = I₃`
(`2r + p + ℓ = 3` columns, `ℓ = 0`). -/
noncomputable def Q : Matrix (Fin 3) (Fin 3) ℝ := 1

/-- The co-range basis `W = I₃`. -/
noncomputable def W : Matrix (Fin 3) (Fin 3) ℝ := 1

/-- B-step (7) trajectory `B(t) = Y₀ Ω + t G Ω`. -/
noncomputable def Bs (t : ℝ) : Matrix (Fin 3) (Fin 2) ℝ := Y₀ * Ω + t • (G * Ω)

/-- B-step of the transposed rangefinder (for `W_h` in (15)): `B(t) = Y₀ᵀ Ω + t Gᵀ Ω`. -/
noncomputable def Bt (t : ℝ) : Matrix (Fin 3) (Fin 2) ℝ := Y₀ᵀ * Ω + t • (Gᵀ * Ω)

/-- C-step (14) trajectory `C(t) = Y₀ᵀ Q + t Gᵀ Q`. -/
noncomputable def Cs (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := Y₀ᵀ * Q + t • (Gᵀ * Q)

/-- DGN B-step (16) trajectory `B(t) = Y₀ W + t G W`. -/
noncomputable def Bd (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := Y₀ * W + t • (G * W)

/-- DGN D-step (16) trajectory `D(t) = Qᵀ Y₀ W + t Qᵀ G W`. -/
noncomputable def Ds (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := Qᵀ * Y₀ * W + t • (Qᵀ * G * W)

/-- `F ≡ G` is the derivative of `A`. -/
lemma isDerivRHS_A : IsDerivRHS F A 0 1 := Exactness.isDerivRHS_add_smul Y₀ G 0 1

/-- `A` solves the full problem (1) `A' = F(A)`. -/
lemma A_ode : ODESolution F A 0 1 :=
  Exactness.odeSolution_add_smul_of_const (c := G) (fun _ _ => rfl) Y₀ 0 1

/-- `A₀ = Y₀ = U₀ S₀ V₀ᵀ` with `U₀ = V₀ = e₁`, `S₀ = 1`. -/
lemma A_zero : A 0 = e₁ * (1 : Matrix (Fin 1) (Fin 1) ℝ) * e₁ᵀ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [A, Y₀, e₁, Matrix.vecMul, dotProduct]

/-- `U₀ = V₀ = e₁` has orthonormal columns. -/
lemma e₁_orth : e₁ᵀ * e₁ = 1 := by
  ext i j; fin_cases i; fin_cases j; simp [e₁, Matrix.mul_apply, Fin.sum_univ_three]

/-- The sketch has orthonormal columns. -/
lemma Ω_orth : Ωᵀ * Ω = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Ω, Matrix.mul_apply, Fin.sum_univ_three]

/-- `A(1) = diag(0, 1, 1) = Ω Ωᵀ`. -/
lemma A_one_eq : A 1 = Ω * Ωᵀ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [A, Y₀, G, Ω, Matrix.mul_apply, Fin.sum_univ_two]

/-- `A(1) Ω = Ω`. -/
lemma A_one_mul_Ω : A 1 * Ω = Ω := by
  rw [A_one_eq, Matrix.mul_assoc, Ω_orth, Matrix.mul_one]

/-- `rank A(1) = 2 = r + p`. -/
lemma rank_A_one : (A 1).rank = 2 := by
  refine le_antisymm ?_ ?_
  · rw [A_one_eq]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width Ω)
  · calc 2 = (Ωᵀ * Ω).rank := by rw [Ω_orth, Matrix.rank_one, Fintype.card_fin]
      _ ≤ Ω.rank := Matrix.rank_mul_le_right _ _
      _ = (A 1 * Ω).rank := by rw [A_one_mul_Ω]
      _ ≤ (A 1).rank := Matrix.rank_mul_le_left _ _

/-- `Bs` solves the B-step (7). -/
lemma Bs_ode : ODESolution (fun t B => F t (B * gramPinv Ω) * Ω) Bs 0 1 :=
  Exactness.odeSolution_add_smul_of_const (c := G * Ω) (fun _ _ => rfl) (Y₀ * Ω) 0 1

/-- `B(1) = A(1) Ω = Ω`, so `Q_h = orth(B(1)) = Ω`. -/
lemma Bs_one : Bs 1 = Ω :=
  calc Bs 1 = A 1 * Ω := by simp [Bs, A, Matrix.add_mul]
    _ = Ω := A_one_mul_Ω

/-- `Bt` solves the B-step of the transposed problem (`X ↦ F(Xᵀ)ᵀ`). -/
lemma Bt_ode : ODESolution (fun t B => (F t (B * gramPinv Ω)ᵀ)ᵀ * Ω) Bt 0 1 :=
  Exactness.odeSolution_add_smul_of_const (c := Gᵀ * Ω) (fun _ _ => rfl) (Y₀ᵀ * Ω) 0 1

/-- `B(1) = Ω` for the transposed rangefinder, so `W_h = Ω`. -/
lemma Bt_one : Bt 1 = Ω := by
  have hY : Y₀ᵀ = Y₀ := by ext i j; fin_cases i <;> fin_cases j <;> simp [Y₀]
  have hG : Gᵀ = G := by ext i j; fin_cases i <;> fin_cases j <;> simp [G]
  rw [Bt, hY, hG]
  exact Bs_one

/-- `[e₁, Ω] [e₁, Ω]ᵀ = I₃`: the columns `e₁, e₂, e₃` of `[U₀, Q_h]` are orthonormal, so
`orth([U₀, Q_h]) = I₃` (up to an orthogonal change of basis). -/
lemma fromCols_mul_transpose : Matrix.fromCols e₁ Ω * (Matrix.fromCols e₁ Ω)ᵀ = 1 := by
  rw [Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [e₁, Ω, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- `Cs` solves the C-step (14). -/
lemma Cs_ode : ODESolution (fun t C => (F t (Q * Cᵀ))ᵀ * Q) Cs 0 1 :=
  Exactness.odeSolution_add_smul_of_const (c := Gᵀ * Q) (fun _ _ => rfl) (Y₀ᵀ * Q) 0 1

/-- `Bd` solves the B-step of (16). -/
lemma Bd_ode : ODESolution (fun t B => F t (B * Wᵀ) * W) Bd 0 1 :=
  Exactness.odeSolution_add_smul_of_const (c := G * W) (fun _ _ => rfl) (Y₀ * W) 0 1

/-- `Ds` solves the D-step of (16). -/
lemma Ds_ode : ODESolution (fun t D => Qᵀ * F t (Q * D * Wᵀ) * W) Ds 0 1 :=
  Exactness.odeSolution_add_smul_of_const (c := Qᵀ * G * W) (fun _ _ => rfl) (Qᵀ * Y₀ * W) 0 1

/-- **Every rank-one truncation misses `A(1)`**: `T_1(M) ≠ A(1)` for every `M`, since
`rank T_1(M) ≤ 1 < 2 = rank A(1)`.  So DRSVD fails on this problem for every sketch `Ω` and
every range basis `Q`, not only for the realization chosen below. -/
theorem truncation_ne_A_one (M : Matrix (Fin 3) (Fin 3) ℝ) :
    EckartYoung.truncation M 1 ≠ A 1 := by
  intro h
  have := EckartYoung.rank_truncation_le M 1
  rw [h, rank_A_one] at this
  omega

/-- **Counterexample to Lemma 3.2 of arXiv 2410.17091 as printed** (`r = p = 1`, `q = 0`,
`m = n = 3`).  All hypotheses of the printed lemma hold: `A` solves (1) with the autonomous field
`F ≡ G`; `A₀ = Y₀ = U₀ S₀ V₀ᵀ` with `U₀ = V₀ = e₁`, `S₀ = 1`; `rank A(1) ≤ r + p`; `Q` is as
in (13): the sketch `Ω ∈ ℝ^{3×2}` has orthonormal columns (so `ΩᵀΩ` is invertible), the B-step
(7) solution satisfies `B(0) = Y₀ Ω` and `B(1) = Ω`, so `Q_h = orth(B(1)) = Ω`, and
`Q = I₃ = orth([U₀, Q_h])` (it is orthonormal, captures `[U₀, Q_h]` and lies in its range); and
`Range(A(t)) ⊆ Range(Q)` for all `t ∈ [0, 1]`.  The C-step (14) reproduces `A(1)` before
truncation, `Q C(1)ᵀ = A(1)`, but `rank A(1) = 2` and the DRSVD output `T_1(Q C(1)ᵀ)` (the
paper's `T_r(U_h Σ_h V_hᵀ)` with `U_h Σ_h V_hᵀ = Q C(h)ᵀ`) differs from `A(1)`.  The corrected
statement, with `rank A(h) ≤ r`, is `RandomizedBUG.drsvd_exact_iff`. -/
theorem drsvd_counterexample :
    ODESolution F A 0 1 ∧ A 0 = e₁ * (1 : Matrix (Fin 1) (Fin 1) ℝ) * e₁ᵀ ∧ e₁ᵀ * e₁ = 1 ∧
      (A 1).rank ≤ 1 + 1 ∧
      Ωᵀ * Ω = 1 ∧ ODESolution (fun t B => F t (B * gramPinv Ω) * Ω) Bs 0 1 ∧
      Bs 0 = A 0 * Ω ∧ Bs 1 = Ω ∧
      Qᵀ * Q = 1 ∧ Q * Qᵀ * Matrix.fromCols e₁ Ω = Matrix.fromCols e₁ Ω ∧
      Q = Matrix.fromCols e₁ Ω * (Matrix.fromCols e₁ Ω)ᵀ ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Q * Qᵀ * A t = A t) ∧
      ODESolution (fun t C => (F t (Q * Cᵀ))ᵀ * Q) Cs 0 1 ∧ Cs 0 = (A 0)ᵀ * Q ∧
      Q * (Cs 1)ᵀ = A 1 ∧ (A 1).rank = 2 ∧
      EckartYoung.truncation (Q * (Cs 1)ᵀ) 1 ≠ A 1 := by
  have hC₀ : Cs 0 = (A 0)ᵀ * Q := by simp [Cs, A]
  have hcap : Q * Qᵀ * A 1 = A 1 := by simp [Q]
  refine ⟨A_ode, A_zero, e₁_orth, by rw [rank_A_one], Ω_orth, Bs_ode, by simp [Bs, A], Bs_one,
    by simp [Q], by simp [Q], by rw [fromCols_mul_transpose]; rfl, fun t _ => by simp [Q],
    Cs_ode, hC₀, ?_, rank_A_one, truncation_ne_A_one _⟩
  exact (RandomizedBUG.drsvd_exact_iff zero_le_one isDerivRHS_A Cs_ode hC₀ hcap 1).1

/-- **Counterexample to Lemma 3.3 of arXiv 2410.17091 as printed** (`r = p = 1`, `ℓ = q = 0`,
`m = n = 3`).  In addition to the data of `drsvd_counterexample`: `W` is as in (15): the
transposed rangefinder (field `X ↦ F(Xᵀ)ᵀ`, start `Y₀ᵀ Ω`) has `B(1) = Ω`, so `W_h = Ω` and
`W = I₃ = orth([V₀, W_h])`; `Range(A(t)ᵀ) ⊆ Range(W)` for all `t`; and `B`, `C`, `D` solve the
BCD-step (16) with `B(0) = A₀ W`, `C(0) = A₀ᵀ Q`, `D(0) = Qᵀ A₀ W`.  Then for every `G'` with
`G' T_1(D(1)) G' = G'` (one of the Penrose equations, so in particular for the pseudo-inverse
`T_1(D(1))†` of (17)) the DGN output `B(1) G' C(1)ᵀ` differs from `A(1)`, because it has rank
`≤ 1 < 2 = rank A(1)`.  The corrected statement is `RandomizedBUG.dgn_exact`. -/
theorem dgn_counterexample :
    ODESolution (fun t B => (F t (B * gramPinv Ω)ᵀ)ᵀ * Ω) Bt 0 1 ∧ Bt 0 = (A 0)ᵀ * Ω ∧
      Bt 1 = Ω ∧ Wᵀ * W = 1 ∧ W * Wᵀ * Matrix.fromCols e₁ Ω = Matrix.fromCols e₁ Ω ∧
      W = Matrix.fromCols e₁ Ω * (Matrix.fromCols e₁ Ω)ᵀ ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Q * Qᵀ * A t = A t ∧ W * Wᵀ * (A t)ᵀ = (A t)ᵀ) ∧
      ODESolution (fun t B => F t (B * Wᵀ) * W) Bd 0 1 ∧ Bd 0 = A 0 * W ∧
      ODESolution (fun t C => (F t (Q * Cᵀ))ᵀ * Q) Cs 0 1 ∧ Cs 0 = (A 0)ᵀ * Q ∧
      ODESolution (fun t D => Qᵀ * F t (Q * D * Wᵀ) * W) Ds 0 1 ∧ Ds 0 = Qᵀ * A 0 * W ∧
      (A 1).rank ≤ 1 + 1 ∧
      ∀ G' : Matrix (Fin 3) (Fin 3) ℝ,
        G' * EckartYoung.truncation (Ds 1) 1 * G' = G' → Bd 1 * G' * (Cs 1)ᵀ ≠ A 1 := by
  refine ⟨Bt_ode, by simp [Bt, A], Bt_one, by simp [W], by simp [W],
    by rw [fromCols_mul_transpose]; rfl, fun t _ => ⟨by simp [Q], by simp [W]⟩,
    Bd_ode, by simp [Bd, A], Cs_ode, by simp [Cs, A], Ds_ode, by simp [Ds, A],
    by rw [rank_A_one], ?_⟩
  intro G' hG' h
  have h1 : G'.rank ≤ 1 := by
    calc G'.rank = (G' * EckartYoung.truncation (Ds 1) 1 * G').rank := by rw [hG']
      _ ≤ (G' * EckartYoung.truncation (Ds 1) 1).rank := Matrix.rank_mul_le_left _ _
      _ ≤ (EckartYoung.truncation (Ds 1) 1).rank := Matrix.rank_mul_le_right _ _
      _ ≤ 1 := EckartYoung.rank_truncation_le _ _
  have h2 := (RandomizedBUG.rank_assembly_le (Bd 1) G' (Cs 1)).trans h1
  rw [h, rank_A_one] at h2
  omega

/-- **Lemma 3.1 holds on the same problem** (non-vacuity of `idealized_drsvd_exact`): with the
idealized rangefinder `ℬ = Bs` (here `F(A(t)) Ω = G Ω`), `Q_h = Ω`, `A(1) = Ω Ωᵀ` (`V = Ω`,
`R = 1`) and the idealized C-step `C(t) = Y₀ᵀ Ω + t Gᵀ Ω`, the idealized DRSVD without truncation
is exact, `Ω C(1)ᵀ = A(1)`, although `rank A(1) = r + p = 2`. -/
example : Ω * (Y₀ᵀ * Ω + (1 : ℝ) • (Gᵀ * Ω))ᵀ = A 1 :=
  (idealized_drsvd_exact (s := Fin 2) zero_le_one A_ode
    (Exactness.odeSolution_add_smul_of_const (c := G * Ω) (fun _ _ => rfl) (Y₀ * Ω) 0 1)
    (by simp [A]) A_one_eq (R := 1) (by rw [Matrix.mul_one, Ω_orth])
    (by rw [show Y₀ * Ω + (1 : ℝ) • (G * Ω) = Bs 1 from rfl, Bs_one, Matrix.mul_assoc, Ω_orth,
      Matrix.mul_one])
    (Exactness.odeSolution_add_smul_of_const (c := Gᵀ * Ω) (fun _ _ => rfl) (Y₀ᵀ * Ω) 0 1)
    (by simp [A])).2.1

end RankCounterexample

/-! ## The remark after Lemma 3.2: the limit case `r + p = min{m, n}` -/

omit [Fintype n] in
/-- **Remark after Lemma 3.2, case `r + p = m`** (arXiv 2410.17091, p. 12).  If `Q_h` has
`r + p = m` orthonormal columns (a square orthogonal matrix) and `Q = orth([U₀, Q_h])` captures
`Q_h`, then `Q Qᵀ X = X` for every `X`; in particular `Range(A(t)) ⊆ Range(Q)` for all `t`. -/
theorem range_inclusion_of_square [DecidableEq m] {Qh : Matrix m m ℝ} (hQh : Qhᵀ * Qh = 1)
    {Q : Matrix m l ℝ} (hcap : Q * Qᵀ * Qh = Qh) (X : Matrix m n ℝ) : Q * Qᵀ * X = X := by
  have h1 : Qh * Qhᵀ = 1 := mul_eq_one_comm.mp hQh
  calc Q * Qᵀ * X = Q * Qᵀ * (Qh * Qhᵀ * X) := by rw [h1, Matrix.one_mul]
    _ = Q * Qᵀ * Qh * Qhᵀ * X := by simp only [Matrix.mul_assoc]
    _ = X := by rw [hcap, h1, Matrix.one_mul]

namespace LimitCase

/-- `U₀ = e₁ ∈ ℝ^{3×1}`. -/
noncomputable def U₀ : Matrix (Fin 3) (Fin 1) ℝ := !![1; 0; 0]

/-- The exact solution `a(t) = (1, t, t²)ᵀ ∈ ℝ^{3×1}`. -/
noncomputable def a (t : ℝ) : Matrix (Fin 3) (Fin 1) ℝ := !![1; t; t ^ 2]

/-- The autonomous affine field `F(X) = (0, 1, 2 X₂)ᵀ`, so that `a' = F(a)`. -/
noncomputable def F (X : Matrix (Fin 3) (Fin 1) ℝ) : Matrix (Fin 3) (Fin 1) ℝ :=
  !![0; 1; 2 * X 1 0]

/-- The matrix `[U₀, a(1/2), a(1)]`. -/
noncomputable def M : Matrix (Fin 3) (Fin 3) ℝ := !![1, 1, 1; 0, 1 / 2, 1; 0, 1 / 4, 1]

/-- `a' = F(a)`. -/
lemma a_hasDerivAt (t : ℝ) : HasDerivAt a (F (a t)) t := by
  have h := (((hasDerivAt_id t).smul_const (!![0; 1; 0] : Matrix (Fin 3) (Fin 1) ℝ)).add
    ((hasDerivAt_pow 2 t).smul_const (!![0; 0; 1] : Matrix (Fin 3) (Fin 1) ℝ))).const_add
    (!![1; 0; 0] : Matrix (Fin 3) (Fin 1) ℝ)
  convert h using 1
  · funext x
    ext i j; fin_cases i <;> fin_cases j <;> simp [a]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [F, a]

/-- `a` solves the full problem (1) on `[0, 1]`. -/
lemma a_ode : ODESolution (fun _ X => F X) a 0 1 :=
  ⟨(continuous_iff_continuousAt.2 fun t => (a_hasDerivAt t).continuousAt).continuousOn,
    fun t _ => (a_hasDerivAt t).hasDerivWithinAt⟩

/-- **The remark after Lemma 3.2 fails for `r + p = n < m`** (arXiv 2410.17091, p. 12: "the
assumption is satisfied in the limit case `(r + p) = min{m, n}`").  Take `m = 3`, `n = 1`, `r = 1`,
`p = 0` (so `r + p = 1 = n = min{m, n}`), the autonomous field `F` and the solution
`A(t) = a(t) = (1, t, t²)ᵀ`; `A₀ = Y₀ = U₀ S₀ V₀ᵀ` with `U₀ = e₁`, `S₀ = V₀ = 1`.  For the sketch
`Ω = 1` (`Ω† = 1`) the B-step (7) is solved by `B = A`, so `Q_h = orth(B(1))` spans `a(1)`, and
`Q = orth([U₀, Q_h])` has `2r + p = 2` columns and captures `U₀` and `a(1)`; such an orthonormal
`Q` exists.  But **no** `Q ∈ ℝ^{3×2}` that captures `U₀` and `a(1)` captures `a(1/2)`, because
`U₀, a(1/2), a(1)` are linearly independent: the range inclusion of Lemma 3.2 fails at `t = 1/2`.
(`range_inclusion_of_square` proves the remark for `r + p = m`.) -/
theorem counterexample :
    ODESolution (fun _ X => F X) a 0 1 ∧
      a 0 = U₀ * (1 : Matrix (Fin 1) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ ∧
      U₀ᵀ * U₀ = 1 ∧ (a 1).rank ≤ 1 + 0 ∧
      ODESolution (fun _ B => F (B * gramPinv (1 : Matrix (Fin 1) (Fin 1) ℝ))
        * (1 : Matrix (Fin 1) (Fin 1) ℝ)) a 0 1 ∧
      (∃ Q : Matrix (Fin 3) (Fin 2) ℝ, Qᵀ * Q = 1 ∧ Q * Qᵀ * U₀ = U₀ ∧ Q * Qᵀ * a 1 = a 1) ∧
      ∀ Q : Matrix (Fin 3) (Fin 2) ℝ, Q * Qᵀ * U₀ = U₀ → Q * Qᵀ * a 1 = a 1 →
        Q * Qᵀ * a (1 / 2) ≠ a (1 / 2) := by
  have hpinv : gramPinv (1 : Matrix (Fin 1) (Fin 1) ℝ) = 1 := by simp [gramPinv]
  refine ⟨a_ode, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [a, U₀]
  · ext i j; fin_cases i; fin_cases j; simp [U₀, Matrix.mul_apply, Fin.sum_univ_three]
  · exact Matrix.rank_le_width _
  · simpa [hpinv] using a_ode
  · have h2 : (√2)⁻¹ * (√2)⁻¹ = (2 : ℝ)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
    refine ⟨!![1, 0; 0, (√2)⁻¹; 0, (√2)⁻¹], ?_, ?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.mul_apply, Fin.sum_univ_three, h2]
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [U₀, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct,
          Fin.sum_univ_two]
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [a, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct,
          Fin.sum_univ_two, h2] <;> norm_num
  · intro Q hU hB hmid
    have key : ∀ (v : Matrix (Fin 3) (Fin 1) ℝ) (j : Fin 3), (∀ k, M k j = v k 0) →
        Q * Qᵀ * v = v → ∀ i, (Q * Qᵀ * M) i j = M i j := by
      intro v j hv hPv i
      have h := congrFun (congrFun hPv i) 0
      simp only [Matrix.mul_apply] at h ⊢
      simp only [hv]
      exact h
    have hPM : Q * Qᵀ * M = M := by
      ext i j
      fin_cases j
      · exact key U₀ 0 (fun k => by fin_cases k <;> simp [M, U₀]) hU i
      · exact key (a (1 / 2)) 1 (fun k => by fin_cases k <;> norm_num [M, a]) hmid i
      · exact key (a 1) 2 (fun k => by fin_cases k <;> simp [M, a]) hB i
    have hdet : IsUnit M.det := by
      rw [Matrix.det_fin_three]
      simp [M]
      norm_num
    have hrank : M.rank = 3 := by
      rw [Matrix.rank_of_isUnit M ((Matrix.isUnit_iff_isUnit_det M).2 hdet), Fintype.card_fin]
    have hle : M.rank ≤ 2 :=
      calc M.rank = (Q * Qᵀ * M).rank := by rw [hPM]
        _ ≤ (Q * Qᵀ).rank := Matrix.rank_mul_le_left _ _
        _ ≤ Q.rank := Matrix.rank_mul_le_left _ _
        _ ≤ 2 := Matrix.rank_le_width Q
    omega

end LimitCase

/-! ## Algorithm 4: assembly of the DGN solution -/

section Assembly

variable {p q r : Type*} [Fintype p] [Fintype q] [Fintype r] [DecidableEq r]

/-- **Pseudo-inverse of a truncated SVD** (arXiv 2410.17091, §1.1 "`(U Σ Vᵀ)† = V Σ⁻¹ Uᵀ`" and
Algorithm 4, steps 6–8).  If `Ũ_r`, `Ṽ_r` have orthonormal columns and `Σ_r` is invertible, then
`G = Ṽ_r Σ_r⁻¹ Ũ_rᵀ` satisfies the four Penrose equations for `X = Ũ_r Σ_r Ṽ_rᵀ`, i.e. it is the
Moore–Penrose inverse `T_r(D)†` of (17).  In particular `X G X = X`, the `{1}`-inverse hypothesis
of `RandomizedBUG.dgn_exact`.  (`Σ_r` need not be diagonal.) -/
theorem svd_pinv_penrose {Ur : Matrix p r ℝ} {Sr : Matrix r r ℝ} {Vr : Matrix q r ℝ}
    (hU : Urᵀ * Ur = 1) (hV : Vrᵀ * Vr = 1) (hS : IsUnit Sr.det) :
    Ur * Sr * Vrᵀ * (Vr * Sr⁻¹ * Urᵀ) * (Ur * Sr * Vrᵀ) = Ur * Sr * Vrᵀ ∧
      Vr * Sr⁻¹ * Urᵀ * (Ur * Sr * Vrᵀ) * (Vr * Sr⁻¹ * Urᵀ) = Vr * Sr⁻¹ * Urᵀ ∧
      (Ur * Sr * Vrᵀ * (Vr * Sr⁻¹ * Urᵀ))ᵀ = Ur * Sr * Vrᵀ * (Vr * Sr⁻¹ * Urᵀ) ∧
      (Vr * Sr⁻¹ * Urᵀ * (Ur * Sr * Vrᵀ))ᵀ = Vr * Sr⁻¹ * Urᵀ * (Ur * Sr * Vrᵀ) := by
  have hXG : Ur * Sr * Vrᵀ * (Vr * Sr⁻¹ * Urᵀ) = Ur * Urᵀ := by
    calc _ = Ur * (Sr * (Vrᵀ * Vr) * Sr⁻¹) * Urᵀ := by simp only [Matrix.mul_assoc]
      _ = Ur * Urᵀ := by
        rw [hV, Matrix.mul_one, Matrix.mul_nonsing_inv _ hS, Matrix.mul_one]
  have hGX : Vr * Sr⁻¹ * Urᵀ * (Ur * Sr * Vrᵀ) = Vr * Vrᵀ := by
    calc _ = Vr * (Sr⁻¹ * (Urᵀ * Ur) * Sr) * Vrᵀ := by simp only [Matrix.mul_assoc]
      _ = Vr * Vrᵀ := by
        rw [hU, Matrix.mul_one, Matrix.nonsing_inv_mul _ hS, Matrix.mul_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hXG]
    calc _ = Ur * (Urᵀ * Ur) * Sr * Vrᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, Matrix.mul_one]
  · rw [hGX]
    calc _ = Vr * (Vrᵀ * Vr) * Sr⁻¹ * Urᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV, Matrix.mul_one]
  · rw [hXG, Matrix.transpose_mul, Matrix.transpose_transpose]
  · rw [hGX, Matrix.transpose_mul, Matrix.transpose_transpose]

omit [Fintype m] [Fintype n] in
/-- **Algorithm 4 computes (17)** (arXiv 2410.17091, Algorithm 4, step 8).  If
`U₁ R₁ = B(h) Ṽ_r` and `V₁ R₂ = C(h) Ũ_r` (the two QR decompositions) and
`S₁ = R₁ Σ_r⁻¹ R₂ᵀ`, then `U₁ S₁ V₁ᵀ = B(h) (Ṽ_r Σ_r⁻¹ Ũ_rᵀ) C(h)ᵀ = B(h) T_r(D(h))† C(h)ᵀ`
(by `svd_pinv_penrose`).  Orthonormality of `U₁`, `V₁` is not needed for the identity. -/
theorem dgn_assembly_eq {Ur : Matrix p r ℝ} {Sr : Matrix r r ℝ} {Vr : Matrix q r ℝ}
    {Bh : Matrix m q ℝ} {Ch : Matrix n p ℝ} {U₁ : Matrix m r ℝ} {V₁ : Matrix n r ℝ}
    {R₁ R₂ : Matrix r r ℝ} (h₁ : U₁ * R₁ = Bh * Vr) (h₂ : V₁ * R₂ = Ch * Ur) :
    U₁ * (R₁ * Sr⁻¹ * R₂ᵀ) * V₁ᵀ = Bh * (Vr * Sr⁻¹ * Urᵀ) * Chᵀ := by
  calc U₁ * (R₁ * Sr⁻¹ * R₂ᵀ) * V₁ᵀ = U₁ * R₁ * Sr⁻¹ * (V₁ * R₂)ᵀ := by
        rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = Bh * (Vr * Sr⁻¹ * Urᵀ) * Chᵀ := by
        rw [h₁, h₂, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]

end Assembly

end LeanDLRA.Literature.P2410_17091
