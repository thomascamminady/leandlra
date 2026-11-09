import LeanDLRA.Integrators.EulerBUG
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2209.00550: Predictor-corrector rank adaptivity for DLRA

Matrix-level (finite-dimensional) core of three statements of Hauck–Schnake, arXiv 2209.00550:

* `sepForm_eq_inner` (Prop. 3.2 / Def. 3.3): a separable bilinear form
  `a(W, Z) = Σ_κ Σ (A_κ)_{ki} (B_κ)_{lj} W_{ij} Z_{kl}` equals `⟪Σ_κ A_κ W B_κᵀ, Z⟫_F`, i.e. it is
  induced by the operator `sepOp A B W = Σ_κ A_κ W B_κᵀ`;
* `tangentEuler_residual`, `rank_normal_sepOp_le` (Sec. 4.3 / Prop. 5.2): the tangent-Euler
  residual is `Δt (I - C Cᵀ) F(U) (I - D Dᵀ)` and for `N`-separable `F` it has rank `≤ N r`;
* `norm_sq_sub_eq_of_orthProj`, `matrix_norm_sq_sub_eq` (Sec. 5.3.2): Pythagoras for the
  culling error, making the residual estimator sharp.

Thm. 4.1 / Lemma 4.1 (projected BUG with forward Euler) are already proved in
`LeanDLRA.Integrators.EulerBUG` (`eulerBug_local_error`, `eulerBug_global_error`).  Props. 3.4-3.5
(upwind DG operator) are finite-element specific and are not formalized.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2209_00550

section Separable

variable {m n ι : Type*} [Fintype m] [Fintype n] [Fintype ι]

/-- The operator `W ↦ Σ_κ A_κ W B_κᵀ` of an `N`-separable operator (arXiv 2209.00550, Def. 3.3,
matrix form; the index type `ι` of the sum has `N` elements). -/
def sepOp (A : ι → Matrix m m ℝ) (B : ι → Matrix n n ℝ) (W : Matrix m n ℝ) : Matrix m n ℝ :=
  ∑ κ, A κ * W * (B κ)ᵀ

/-- The separable bilinear form of arXiv 2209.00550, Def. 3.2 / Prop. 3.2, written in coordinates
of the tensor-product basis: `a(W, Z) = Σ_κ Σ_{i,j,k,l} (A_κ)_{ki} (B_κ)_{lj} W_{ij} Z_{kl}`
(the middle expression of (3.10)). -/
def sepForm (A : ι → Matrix m m ℝ) (B : ι → Matrix n n ℝ) (W Z : Matrix m n ℝ) : ℝ :=
  ∑ κ, ∑ i, ∑ j, ∑ k, ∑ l, A κ k i * B κ l j * W i j * Z k l

/-- **Prop. 3.2 (arXiv 2209.00550), matrix form.**  The separable bilinear form `sepForm A B`
is induced by the operator `L W = Σ_κ A_κ W B_κᵀ`, in the Frobenius inner product:
`a(W, Z) = ⟪L W, Z⟫_F`.  Difference from the paper: finite-element basis functions are abstracted
away; `A_κ`, `B_κ` are the (square) matrices of the factors of the form in a basis, with
`A_κ : m × m` and `B_κ : n × n` as in Def. 3.3. -/
theorem sepForm_eq_inner (A : ι → Matrix m m ℝ) (B : ι → Matrix n n ℝ) (W Z : Matrix m n ℝ) :
    sepForm A B W Z = ⟪sepOp A B W, Z⟫ := by
  rw [Frobenius.inner_def, sepForm, sepOp]
  simp only [Matrix.sum_apply, Finset.sum_mul]
  have hc : ∀ κ : ι, ∑ k, ∑ l, (A κ * W * (B κ)ᵀ) k l * Z k l = ∑ i, ∑ j, ∑ k, ∑ l,
      A κ k i * B κ l j * W i j * Z k l := fun κ => by
    have key : ∀ k l, (A κ * W * (B κ)ᵀ) k l = ∑ i, ∑ j, A κ k i * B κ l j * W i j := by
      intro k l
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    simp only [key, Finset.sum_mul]
    -- reorder Σ_i Σ_j Σ_k Σ_l to Σ_k Σ_l Σ_i Σ_j
    have h1 : ∀ f : m → n → m → n → ℝ,
        ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
      intro f
      calc ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ i, ∑ k, ∑ j, ∑ l, f i j k l :=
            Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = ∑ k, ∑ i, ∑ j, ∑ l, f i j k l := Finset.sum_comm
        _ = ∑ k, ∑ i, ∑ l, ∑ j, f i j k l :=
            Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l :=
            Finset.sum_congr rfl fun k _ => Finset.sum_comm
    exact (h1 fun i j k l => A κ k i * B κ l j * W i j * Z k l).symm
  calc ∑ κ, ∑ i, ∑ j, ∑ k, ∑ l, A κ k i * B κ l j * W i j * Z k l
      = ∑ κ, ∑ k, ∑ l, (A κ * W * (B κ)ᵀ) k l * Z k l :=
        Finset.sum_congr rfl fun κ _ => (hc κ).symm
    _ = ∑ k, ∑ l, ∑ κ, (A κ * W * (B κ)ᵀ) k l * Z k l := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_comm

end Separable

section Residual

variable {m n k k' : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype k']
  [DecidableEq m] [DecidableEq n]

/-- **Tangent-Euler residual (arXiv 2209.00550, Sec. 4.3 / Prop. 5.2).**  For the forward Euler
step `U_FE = Y + h F` (with `F = F(Y)`) and the tangent-Euler step
`Y + h P(Y) F` (`P(Y) Z = C Cᵀ Z + Z D Dᵀ - C Cᵀ Z D Dᵀ`, the tangent projector at
`Y = C S Dᵀ`), the difference is the normal component:
`U_FE - U^{n+1} = h (I - C Cᵀ) F (I - D Dᵀ)`.
The identity is purely algebraic, so no orthonormality of `C`, `D` and no assumption on `Y` is
needed. -/
theorem tangentEuler_residual (C : Matrix m k ℝ) (D : Matrix n k' ℝ) (Y F : Matrix m n ℝ)
    (h : ℝ) :
    (Y + h • F) - (Y + h • tangentProj C D F) = h • ((1 - C * Cᵀ) * F * (1 - D * Dᵀ)) := by
  have e : (1 - C * Cᵀ) * F * (1 - D * Dᵀ) = F - tangentProj C D F :=
    eq_sub_of_add_eq' (tangentProj_add_normal C D F)
  rw [e, smul_sub]
  abel

/-- **Rank of the tangent-Euler residual (arXiv 2209.00550, Prop. 5.2).**  Let
`Y = C S Dᵀ` have rank `≤ r` (`C : m × r`, `S : r × r`, `D : n × r`) and let `F` be
`N`-separable, `F(Y) = Σ_{κ<N} A_κ Y B_κᵀ`.  Then the normal component
`(I - C₀ C₀ᵀ) F(Y) (I - D₀ D₀ᵀ)` of `F(Y)` with respect to *any* pair of matrices `C₀`, `D₀`
(in particular the bases of `Y`) has rank at most `N r`. The residual itself is
`rank_tangentEuler_residual_le` (Prop. 5.2 (ii)).  Not covered: the bound `(N + 2) r` of
Prop. 5.2 (i) for Algorithms 4.1 and 4.3. -/
theorem rank_normal_sepOp_le {N r : ℕ} (A : Fin N → Matrix m m ℝ) (B : Fin N → Matrix n n ℝ)
    (C : Matrix m (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ) (D : Matrix n (Fin r) ℝ)
    (C₀ : Matrix m k ℝ) (D₀ : Matrix n k' ℝ) :
    ((1 - C₀ * C₀ᵀ) * sepOp A B (C * S * Dᵀ) * (1 - D₀ * D₀ᵀ)).rank ≤ N * r := by
  set L : Matrix m (Fin N × Fin r) ℝ := Matrix.of fun i p => (A p.1 * C * S) i p.2 with hL
  set R : Matrix (Fin N × Fin r) n ℝ := Matrix.of fun p j => (Dᵀ * (B p.1)ᵀ) p.2 j with hR
  have hX : sepOp A B (C * S * Dᵀ) = L * R := by
    ext i j
    simp only [sepOp, Matrix.sum_apply]
    have e : ∀ κ : Fin N, A κ * (C * S * Dᵀ) * (B κ)ᵀ = (A κ * C * S) * (Dᵀ * (B κ)ᵀ) := fun κ => by
      simp [Matrix.mul_assoc]
    simp only [e]
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [Matrix.mul_apply]
    rfl
  have h1 : (L * R).rank ≤ N * r := by
    calc (L * R).rank ≤ L.rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin N × Fin r) := Matrix.rank_le_card_width _
      _ = N * r := by simp
  rw [hX]
  exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans h1)

omit [DecidableEq m] [DecidableEq n] in
/-- **Prop. 5.2 (ii) (arXiv 2209.00550).**  For `N`-separable `F` and `U^n = C S Dᵀ` of rank
`≤ r`, the residual `R = U_FE - U^{n+1}` (5.3) of the tangent-Euler step (Algorithm 4.2, (4.12))
has rank at most `N r`.  The tangent projector may be taken with respect to any `C₀`, `D₀` (the
paper uses the orthonormal bases of `U^n`). -/
theorem rank_tangentEuler_residual_le {N r : ℕ} (A : Fin N → Matrix m m ℝ)
    (B : Fin N → Matrix n n ℝ) (C : Matrix m (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ)
    (D : Matrix n (Fin r) ℝ) (C₀ : Matrix m k ℝ) (D₀ : Matrix n k' ℝ) (h : ℝ) :
    ((C * S * Dᵀ + h • sepOp A B (C * S * Dᵀ))
      - (C * S * Dᵀ + h • tangentProj C₀ D₀ (sepOp A B (C * S * Dᵀ)))).rank ≤ N * r := by
  classical
  rw [tangentEuler_residual, Matrix.smul_eq_diagonal_mul]
  exact (Matrix.rank_mul_le_right _ _).trans (rank_normal_sepOp_le A B C S D C₀ D₀)

end Residual

section Culling

/-- **Sharp residual estimator (arXiv 2209.00550, Sec. 5.3.2), abstract form.**  Let `P_H` be an
orthogonal projector on an inner product space, `y = U_FE` the forward Euler step and `z = U^{n+1}`
any element of the range of `P_H` (e.g. the culled/truncated predictor).  With the residual
`R = y - P_H y` and the culling error `P_H y - z` (`P_H y = U_P` the predictor), Pythagoras gives
`‖y - z‖² = ‖R‖² + ‖P_H y - z‖²`.  This is the orthogonality of `R` and `U_P^{n+1} - U^{n+1}` that
Sec. 5.3.2 (and Sec. 4.4) states in words for the projected unconventional integrator
(Algorithm 4.3, where `U_P = P_H U_FE` by (4.18)); the paper prints no equation for it. -/
theorem norm_sq_sub_eq_of_orthProj {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {P : E →L[ℝ] E} (hP : IsOrthProj P) (y z : E) (hz : P z = z) :
    ‖y - z‖ ^ 2 = ‖y - P y‖ ^ 2 + ‖P y - z‖ ^ 2 := by
  have hdec : y - z = (y - P y) + (P y - z) := by abel
  have horth : ⟪y - P y, P y - z⟫ = 0 := by
    have : P y - z = P (y - z) := by rw [map_sub, hz]
    rw [this, real_inner_comm, hP.inner_sub_self]
  rw [hdec, norm_add_sq_real, horth]
  ring

/-- **Sharpness of the estimator (arXiv 2209.00550, Sec. 5.3.2).**  Under the hypotheses of
`norm_sq_sub_eq_of_orthProj`, the residual norm is a lower bound for the full error:
`‖y - P_H y‖ ≤ ‖y - z‖`.  This is a consequence of the orthogonality, not a printed statement;
it concerns the exact `‖R‖`, not the randomized estimator `ν` of (5.10).  The matching
equality statement is `norm_sq_sub_eq_of_orthProj`. -/
theorem norm_residual_le_of_orthProj {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {P : E →L[ℝ] E} (hP : IsOrthProj P) (y z : E) (hz : P z = z) :
    ‖y - P y‖ ≤ ‖y - z‖ :=
  hP.norm_sub_le_of_mem_range y z hz

/-- **Matrix form of Sec. 5.3.2 (arXiv 2209.00550).**  For `C₁`, `D₁` with orthonormal columns
(the augmented bases, `P_H X = C₁ C₁ᵀ X D₁ D₁ᵀ`), `Y = U_FE` and any `Z = U^{n+1}` whose columns and
rows lie in the span of the bases (`P_H Z = Z`):
`‖Y - Z‖² = ‖Y - P_H Y‖² + ‖P_H Y - Z‖²`. -/
theorem matrix_norm_sq_sub_eq {m n k k' : Type*} [Fintype m] [Fintype n] [Fintype k]
    [Fintype k'] [DecidableEq k] [DecidableEq k'] {C₁ : Matrix m k ℝ} {D₁ : Matrix n k' ℝ}
    (hC : C₁ᵀ * C₁ = 1) (hD : D₁ᵀ * D₁ = 1) (Y Z : Matrix m n ℝ)
    (hZ : C₁ * C₁ᵀ * Z * D₁ * D₁ᵀ = Z) :
    ‖Y - Z‖ ^ 2 = ‖Y - C₁ * C₁ᵀ * Y * D₁ * D₁ᵀ‖ ^ 2 + ‖C₁ * C₁ᵀ * Y * D₁ * D₁ᵀ - Z‖ ^ 2 := by
  have hP := isOrthProj_leftProj_mul_rightProj (m := m) (n := n) hC hD
  have := norm_sq_sub_eq_of_orthProj hP Y Z (by simpa [Matrix.mul_assoc] using hZ)
  simpa [Matrix.mul_assoc] using this

/-- Non-vacuity of the separable setting: one term with `A = 1`, `B = 1` is the identity
operator, and the form is the Frobenius inner product. -/
example {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (W Z : Matrix m n ℝ) :
    sepOp (fun _ : Fin 1 => (1 : Matrix m m ℝ)) (fun _ : Fin 1 => (1 : Matrix n n ℝ)) W = W ∧
      sepForm (fun _ : Fin 1 => (1 : Matrix m m ℝ)) (fun _ : Fin 1 => (1 : Matrix n n ℝ)) W Z
        = ⟪W, Z⟫ := by
  have h : sepOp (fun _ : Fin 1 => (1 : Matrix m m ℝ)) (fun _ : Fin 1 => (1 : Matrix n n ℝ)) W
      = W := by simp [sepOp]
  exact ⟨h, by rw [sepForm_eq_inner, h]⟩

end Culling

end LeanDLRA.Literature.P2209_00550
