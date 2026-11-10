import LeanDLRA.Analysis.Defs
import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.Interpolation
import LeanDLRA.HighOrder.RungeKuttaBUG
import LeanDLRA.Randomized.ObliqueBUG

/-!
# Interpolative DLRA for quantized tensor trains (arXiv 2512.15703)

Ye–Yang, *Time integration of quantized tensor trains using the interpolative dynamical low-rank
approximation*, arXiv 2512.15703.  The paper states no theorems; this module proves the algebraic
and structural facts its algorithms rest on, in matrix form: the tensor-train environment
`|L, φ, R⟩` is an arbitrary matrix `E` (interpolating functions) and `⟨𝓘, σ, 𝓙|` an arbitrary
matrix `S` (a selection where it matters, `sel ι`).  **Sec. 3.1.2**: `interpProj_canonical`
(`S E = I` ⇒ `Π = E S` is idempotent, `Π E = E`, `S Π = S`; for `E = U (SᵀU)⁻¹` this is the
library's `obliqueProj_mul_self`), the oversampled case `oversampled_interpProj` (`E = T (S T)⁺`
with `S T` of full column rank: `Π² = Π`, `Π T = T`), with `lsInv_penrose` (`(AᵀA)⁻¹Aᵀ` is the
Moore–Penrose inverse), `oversampled_idem_of_reflexive` (only `G (S T) G = G` is needed),
`oversampled_leastSquares` (`Π` is the least-squares fit at the sample points) and
`oversampled_not_interpolatory` (`S Π ≠ S` in general).  **Sec. 3.2**: `oblique_conversion`
(eqs. (30)–(32), (36)–(37): `S E_X = I`, `Π_QX = Π_XX = E_Q (S E_Q)⁻¹ S`, `Π_XQ = E_Q E_Qᵀ`;
built on `ObliqueBUG.obliqueConversion`), `cross_conversion` and `cross_core_eq` (eqs. (24),
(28)–(31) for one bond `T = L M R`), `dlrP_full` (the DLR-P core equation evaluates `f` only at
the interpolation points and lifts to `ẋ = Π_QQ A Π_QX f(x)`), `dlrP_iff_dlrX` (DLR-P and DLR-X
solutions correspond exactly under `M_X = S E_Q M_Q` when `S E_Q` is invertible) and
`selection_not_left_invertible` (the paper's remark that `(S E_Q)⁻¹ S A ≠ E_Qᵀ A` without the
projection `E_Q E_Qᵀ`).  **Sec. 3.3**: a Galerkin Runge–Kutta step whose basis contains all
stage values and `y_{n+1}` is a solution of the Galerkin equations for any tableau
(`galerkinRK_of_fix_stages`) and equals the full step for explicit tableaux
(`galerkinRK_eq_of_fix_stages`, `galerkinRK_eq_of_fix_derivs`) or under a contraction condition
(`galerkinRK_unique`); hence `apRK4_eq_rk4` (target `[M(t) k₁ k₂ k₃ M(t+Δt)]`) and `apCN_eq_cn`
(target `[M(t) M(t+Δt)]`).  **Sec. 4.1**: `dlrx_upwind` (effective shifts `S S^± E` return the
exact neighbour values, so an arbitrary branch-dependent flux is evaluated only at the selected
points and the DLR-X step is the interpolative projection `Π` of the full upwind step) and
`dlrx_upwind_error` (`‖G(u) - Π G(u)‖ ≤ (1 + ‖Π‖) ‖G(u) - E c‖` for every `c`).

Not formalized: the observed convergence orders (4 for AP-RK4, 2 for AP-CN, 2 for projector
splitting, explained in the paper only by the Lie–Trotter splitting) and all other numerical
claims; the tensor-train/QTT structure (sweeps over cores, the CUR decimation and rank
truncation), so the exactness results concern one Galerkin step with a fixed projector; the
Feiguin–White target `[M(t) M(t+Δt/3) M(t+2Δt/3) M(t+Δt)]`; Crank–Nicolson with fields at
`t_{n+1/2}` (we use the trapezoidal rule); the specific Burgers interface value of eq. (45),
whose first two printed cases carry the same condition (`u_{j+1} > u_j`, `(u_{j+1} + u_j) / 2 > 0`)
with different values (PDF p. 22), so the flux is kept arbitrary and every reading of (45) is
covered.  The Burgers grid of Sec. 4.1 is taken periodic (`Fin n` with cyclic shifts `S^±`); the
paper does not state the boundary condition of this example.  In `dlrx_upwind_error` the norm is
the max-norm of `Fin n → ℝ` (any norm would do).
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2512_15703

open Matrix

/-! ## Sec. 3.1.2: the interpolative projector `Π = E S` -/

section Idempotent

variable {N K p r : Type*} [Fintype N] [Fintype K] [Fintype p] [Fintype r]

/-- **Interpolative projector, canonical case** (arXiv 2512.15703, Sec. 3.1.2, eq. (23)).
If the interpolating functions `E` are dual to the selection `S` (`S E = I`), then `Π = E S` is
an (oblique) projector: `Π² = Π`; it reproduces the interpolating functions (`Π E = E`) and it
interpolates (`S Π = S`).  Matrices of arbitrary index types stand for the paper's
`|L, φ, R⟩` (`E`) and `⟨I, σ, J|` (`S`).  For `E = U (SᵀU)⁻¹` the idempotence is the library's
`obliqueProj_mul_self`. -/
theorem interpProj_canonical [DecidableEq K] {E : Matrix N K ℝ} {S : Matrix K N ℝ}
    (hSE : S * E = 1) :
    E * S * (E * S) = E * S ∧ E * S * E = E ∧ S * (E * S) = S := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc S, hSE, Matrix.one_mul]
  · rw [Matrix.mul_assoc, hSE, Matrix.mul_one]
  · rw [← Matrix.mul_assoc, hSE, Matrix.one_mul]

/-- The least-squares inverse `A⁺ = (Aᵀ A)⁻¹ Aᵀ` (the Moore–Penrose inverse of a matrix of full
column rank, see `lsInv_penrose`). -/
noncomputable def lsInv [DecidableEq r] (A : Matrix p r ℝ) : Matrix r p ℝ := (Aᵀ * A)⁻¹ * Aᵀ

/-- Full column rank (`A x = 0 → x = 0`) makes the Gram matrix `Aᵀ A` invertible. -/
theorem isUnit_det_gram [DecidableEq r] {A : Matrix p r ℝ} (hA : Function.Injective A.mulVec) :
    IsUnit (Aᵀ * A).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have h0 : x - y ∈ LinearMap.ker (Aᵀ * A).mulVecLin := by
    change (Aᵀ * A) *ᵥ (x - y) = 0
    rw [Matrix.mulVec_sub, hxy, sub_self]
  rw [Matrix.ker_mulVecLin_transpose_mul_self] at h0
  change A *ᵥ (x - y) = 0 at h0
  rw [Matrix.mulVec_sub, sub_eq_zero] at h0
  exact hA h0

/-- `A⁺ = (AᵀA)⁻¹Aᵀ` satisfies the four Penrose equations when `A` has full column rank, so it is
the Moore–Penrose pseudo-inverse `A⁺` of the paper; moreover `A⁺ A = I`. -/
theorem lsInv_penrose [DecidableEq r] {A : Matrix p r ℝ} (hA : Function.Injective A.mulVec) :
    lsInv A * A = 1 ∧ A * lsInv A * A = A ∧ lsInv A * A * lsInv A = lsInv A ∧
      (A * lsInv A)ᵀ = A * lsInv A ∧ (lsInv A * A)ᵀ = lsInv A * A := by
  have hG : IsUnit (Aᵀ * A).det := isUnit_det_gram hA
  have h1 : lsInv A * A = 1 := by
    rw [lsInv, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hG]
  refine ⟨h1, by rw [Matrix.mul_assoc, h1, Matrix.mul_one], by rw [h1, Matrix.one_mul], ?_,
    by rw [h1, Matrix.transpose_one]⟩
  rw [lsInv, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_nonsing_inv, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc]

/-- Idempotence only needs the second Penrose equation `G (S T) G = G`, which the Moore–Penrose
inverse `(S T)⁺` satisfies for every `S T` (no rank condition). -/
theorem oversampled_idem_of_reflexive {T : Matrix N r ℝ} {S : Matrix p N ℝ} {G : Matrix r p ℝ}
    (hG : G * (S * T) * G = G) : T * G * S * (T * G * S) = T * G * S := by
  calc T * G * S * (T * G * S) = T * (G * (S * T) * G) * S := by simp only [Matrix.mul_assoc]
    _ = T * G * S := by rw [hG]

/-- **Interpolative projector, oversampled case** (arXiv 2512.15703, Sec. 3.1.2).  With `p ≥ r`
selected points (`S : p × N`) and a basis `T : N × r` whose sampled matrix `S T` has full column
rank, the interpolating functions `E = T (S T)⁺` give an idempotent `Π = E S` that reproduces
the basis, `Π T = T` (so `range Π = range T`), and `E` is a left inverse of the selection on the
basis, `(S T)⁺ (S T) = I` (the paper's `T̂⁻¹ T̂ = I`).  Unlike the canonical case `S Π ≠ S` in
general: see `oversampled_leastSquares` for what `Π` does at the sample points. -/
theorem oversampled_interpProj [DecidableEq r] {T : Matrix N r ℝ} {S : Matrix p N ℝ}
    (hST : Function.Injective (S * T).mulVec) :
    T * lsInv (S * T) * S * (T * lsInv (S * T) * S) = T * lsInv (S * T) * S ∧
      T * lsInv (S * T) * S * T = T ∧ lsInv (S * T) * (S * T) = 1 := by
  obtain ⟨h1, -, h3, -, -⟩ := lsInv_penrose hST
  refine ⟨oversampled_idem_of_reflexive h3, ?_, h1⟩
  rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one]

/-- Normal equations and optimality of `c⋆ = A⁺ b` for a matrix `A` of full column rank. -/
theorem leastSquares_aux [DecidableEq r] {A : Matrix p r ℝ} (hA : Function.Injective A.mulVec)
    (b : p → ℝ) (c : r → ℝ) :
    Aᵀ *ᵥ (b - A *ᵥ (lsInv A *ᵥ b)) = 0 ∧
      (b - A *ᵥ (lsInv A *ᵥ b)) ⬝ᵥ (b - A *ᵥ (lsInv A *ᵥ b)) ≤ (b - A *ᵥ c) ⬝ᵥ (b - A *ᵥ c) := by
  have hG : IsUnit (Aᵀ * A).det := isUnit_det_gram hA
  have hAG : Aᵀ * A * lsInv A = Aᵀ := by
    rw [lsInv, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.one_mul]
  have hnormal : Aᵀ *ᵥ (b - A *ᵥ (lsInv A *ᵥ b)) = 0 := by
    have h2 : Aᵀ *ᵥ (A *ᵥ (lsInv A *ᵥ b)) = Aᵀ *ᵥ b := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hAG]
    rw [Matrix.mulVec_sub, h2, sub_self]
  refine ⟨hnormal, ?_⟩
  set res := b - A *ᵥ (lsInv A *ᵥ b) with hres
  have hsplit : b - A *ᵥ c = res + A *ᵥ (lsInv A *ᵥ b - c) := by
    rw [hres, Matrix.mulVec_sub]; abel
  have hcross : res ⬝ᵥ (A *ᵥ (lsInv A *ᵥ b - c)) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hnormal, zero_dotProduct]
  have hcross' : (A *ᵥ (lsInv A *ᵥ b - c)) ⬝ᵥ res = 0 := by rw [dotProduct_comm, hcross]
  rw [hsplit, add_dotProduct, dotProduct_add, dotProduct_add, hcross, hcross']
  have : 0 ≤ (A *ᵥ (lsInv A *ᵥ b - c)) ⬝ᵥ (A *ᵥ (lsInv A *ᵥ b - c)) :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  linarith

/-- **The oversampled projection is a least-squares fit at the sample points**
(arXiv 2512.15703, Sec. 3.1.2).  For `x`, the coefficients `c⋆ = (S T)⁺ S x` of `Π x = T c⋆`
satisfy the normal equations `(S T)ᵀ (S x - S T c⋆) = 0` and minimise the sampled residual:
`‖S x - S T c⋆‖² ≤ ‖S x - S T c‖²` for every `c` (Euclidean norm, written with `⬝ᵥ`). -/
theorem oversampled_leastSquares [DecidableEq r] {T : Matrix N r ℝ} {S : Matrix p N ℝ}
    (hST : Function.Injective (S * T).mulVec) (x : N → ℝ) (c : r → ℝ) :
    (S * T)ᵀ *ᵥ (S *ᵥ x - (S * T) *ᵥ (lsInv (S * T) *ᵥ (S *ᵥ x))) = 0 ∧
      (S *ᵥ x - (S * T) *ᵥ (lsInv (S * T) *ᵥ (S *ᵥ x))) ⬝ᵥ
          (S *ᵥ x - (S * T) *ᵥ (lsInv (S * T) *ᵥ (S *ᵥ x))) ≤
        (S *ᵥ x - (S * T) *ᵥ c) ⬝ᵥ (S *ᵥ x - (S * T) *ᵥ c) :=
  leastSquares_aux hST (S *ᵥ x) c

/-- **Oversampling gives a non-interpolatory projector** (arXiv 2512.15703, Sec. 3.1.2): for
`T = e₁ ∈ ℝ^{2×1}` sampled at both grid points (`S = I`, `p = 2 > r = 1`), `S T` has full column
rank and `Π = T (S T)⁺ S` is idempotent, but `S Π ≠ S`. -/
theorem oversampled_not_interpolatory :
    let T : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]
    let S : Matrix (Fin 2) (Fin 2) ℝ := 1
    Function.Injective (S * T).mulVec ∧
      T * lsInv (S * T) * S * (T * lsInv (S * T) * S) = T * lsInv (S * T) * S ∧
      S * (T * lsInv (S * T) * S) ≠ S := by
  intro T S
  have hinj : Function.Injective (S * T).mulVec := by
    intro x y hxy
    have := congrFun hxy 0
    simp [S, T, Matrix.mulVec, dotProduct] at this
    funext i; fin_cases i; simpa using this
  refine ⟨hinj, (oversampled_interpProj hinj).1, fun h => ?_⟩
  have := congrFun (congrFun h 1) 1
  simp [S, T, Matrix.mul_apply, Matrix.vecMul, dotProduct] at this

end Idempotent

/-! ## Sec. 3.2: oblique conversion and the DLR-P dynamics -/

section Conversion

variable {N K : Type*} [Fintype N] [Fintype K] [DecidableEq K]

/-- The interpolative basis `E_X = E_Q (S E_Q)⁻¹` built from an orthonormal basis `E_Q` and a
selection `S` (arXiv 2512.15703, eq. (32)). -/
noncomputable def interpBasis (EQ : Matrix N K ℝ) (S : Matrix K N ℝ) : Matrix N K ℝ :=
  EQ * (S * EQ)⁻¹

/-- **Oblique conversion** (arXiv 2512.15703, Sec. 3.2, eqs. (30)–(32), (36)–(37)).  Let `E_Q`
have orthonormal columns (`E_Q^† = E_Qᵀ`) and let `S E_Q` be invertible.  Then
`E_X = E_Q (S E_Q)⁻¹` is dual to the selection (`S E_X = I`), spans the same space
(`E_X (S E_Q) = E_Q`), and

* `Π_XX = E_X S` is the DEIM projector `obliqueProj E_Q Sᵀ = E_Q (S E_Q)⁻¹ S`;
* eq. (36): `Π_QX = E_Q E_Qᵀ E_X S = E_Q (S E_Q)⁻¹ S`, so `Π_QX = Π_XX`;
* eq. (37): `Π_XQ = E_X S E_Q E_Qᵀ = E_Q E_Qᵀ = Π_QQ` (the orthogonal projector).

`S E_X = I` and the formula for `Π_XX` reuse `ObliqueBUG.obliqueConversion` (with the selection
written as `Sᵀ`); eqs. (36) and (37) reuse `proj_mul_obliqueProj` and `obliqueProj_mul_proj`. -/
theorem oblique_conversion {EQ : Matrix N K ℝ} {S : Matrix K N ℝ} (hQ : EQᵀ * EQ = 1)
    (hS : IsUnit (S * EQ).det) :
    S * interpBasis EQ S = 1 ∧ interpBasis EQ S * (S * EQ) = EQ ∧
      interpBasis EQ S * S = obliqueProj EQ Sᵀ ∧
      EQ * EQᵀ * interpBasis EQ S * S = EQ * (S * EQ)⁻¹ * S ∧
      interpBasis EQ S * S * (EQ * EQᵀ) = EQ * EQᵀ := by
  have hS' : IsUnit ((Sᵀ)ᵀ * EQ).det := by rwa [Matrix.transpose_transpose]
  obtain ⟨h1, h2⟩ := ObliqueBUG.obliqueConversion hS'
  rw [Matrix.transpose_transpose] at h1 h2
  have hXS : interpBasis EQ S * S = obliqueProj EQ Sᵀ := h2
  refine ⟨h1, ?_, hXS, ?_, ?_⟩
  · rw [interpBasis, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hS, Matrix.mul_one]
  · rw [Matrix.mul_assoc _ (interpBasis EQ S), hXS, proj_mul_obliqueProj hQ, obliqueProj,
      Matrix.transpose_transpose]
  · rw [hXS, obliqueProj_mul_proj hS']

end Conversion

section Cross

variable {m n r r' : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype r'] [DecidableEq r]
  [DecidableEq r']

/-- **Basis conversion of a tensor-train bond** (arXiv 2512.15703, eqs. (28)–(31)), for the
unfolding `T = L_Q M_Q R_Q` at one core.  `S_I` selects the rows `𝓘` and `S_J` the columns `𝓙`, so
`L_Q[𝓘,:] = S_I L_Q` and `R_Q[:,𝓙] = R_Q S_J`; both are assumed invertible.  With
`L_X = L_Q (L_Q[𝓘,:])⁻¹` (eq. (30)), `R_X = (R_Q[:,𝓙])⁻¹ R_Q` (eq. (31)) and
`M_X = L_Q[𝓘,:] M_Q R_Q[:,𝓙]` (eq. (28)):

* `M_X = T[𝓘,𝓙] = S_I T S_J` (the interpolative core is the cross of `T`);
* `T = L_X M_X R_X` (the same tensor in the interpolative basis);
* eq. (29): `M_Q = (L_Q[𝓘,:])⁻¹ M_X (R_Q[:,𝓙])⁻¹`;
* `L_X[𝓘,:] = I` and `R_X[:,𝓙] = I` (the interpolating functions are cardinal).

The bases need not be orthonormal.  The tensor-train structure (`L`, `R` themselves products of
cores) is not modelled: `L_Q`, `R_Q` are arbitrary matrices. -/
theorem cross_conversion {LQ : Matrix m r ℝ} {RQ : Matrix r' n ℝ} {SI : Matrix r m ℝ}
    {SJ : Matrix n r' ℝ} (hL : IsUnit (SI * LQ).det) (hR : IsUnit (RQ * SJ).det)
    (MQ : Matrix r r' ℝ) :
    SI * LQ * MQ * (RQ * SJ) = SI * (LQ * MQ * RQ) * SJ ∧
      LQ * MQ * RQ = LQ * (SI * LQ)⁻¹ * (SI * LQ * MQ * (RQ * SJ)) * ((RQ * SJ)⁻¹ * RQ) ∧
      MQ = (SI * LQ)⁻¹ * (SI * LQ * MQ * (RQ * SJ)) * (RQ * SJ)⁻¹ ∧
      SI * (LQ * (SI * LQ)⁻¹) = 1 ∧ (RQ * SJ)⁻¹ * RQ * SJ = 1 := by
  have hL1 : (SI * LQ)⁻¹ * (SI * LQ) = 1 := Matrix.nonsing_inv_mul _ hL
  have hR1 : RQ * SJ * (RQ * SJ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hR
  refine ⟨by simp only [Matrix.mul_assoc], ?_, ?_, ?_, ?_⟩
  · calc LQ * MQ * RQ = LQ * ((SI * LQ)⁻¹ * (SI * LQ)) * MQ * ((RQ * SJ) * (RQ * SJ)⁻¹) * RQ := by
          rw [hL1, hR1, Matrix.mul_one, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  · calc MQ = (SI * LQ)⁻¹ * (SI * LQ) * MQ * ((RQ * SJ) * (RQ * SJ)⁻¹) := by
          rw [hL1, hR1, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  · rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hL]
  · rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hR]

/-- **The interpolative core is the cross of the tensor** (arXiv 2512.15703, eq. (24)): if the
interpolating functions are cardinal (`S_I L_X = I`, `R_X S_J = I`), every `T = L_X M R_X` in
their span has core `M = T[𝓘,𝓙] = S_I T S_J`.  Hence the projector `T ↦ L_X (S_I T S_J) R_X`
reproduces such tensors and its core needs only the `|𝓘| |𝓙|` entries `T[𝓘,𝓙]`. -/
theorem cross_core_eq {LX : Matrix m r ℝ} {RX : Matrix r' n ℝ} {SI : Matrix r m ℝ}
    {SJ : Matrix n r' ℝ} (hLX : SI * LX = 1) (hRX : RX * SJ = 1) (M : Matrix r r' ℝ) :
    SI * (LX * M * RX) * SJ = M := by
  calc SI * (LX * M * RX) * SJ = (SI * LX) * M * (RX * SJ) := by simp only [Matrix.mul_assoc]
    _ = M := by rw [hLX, hRX, Matrix.one_mul, Matrix.mul_one]

end Cross

/-! ### DLR-P dynamics -/

section DLRP

variable {N K : Type*} [Fintype N] [DecidableEq N] [Fintype K] [DecidableEq K]

/-- The selection matrix with rows `e_{ι(i)}ᵀ`: `(S x)_i = x_{ι(i)}`. -/
def sel (ι : K → N) : Matrix K N ℝ := Matrix.of fun i n => if ι i = n then 1 else 0

omit [Fintype K] [DecidableEq K] in
lemma sel_mulVec (ι : K → N) (x : N → ℝ) : sel ι *ᵥ x = fun i => x (ι i) := by
  ext i
  simp [sel, Matrix.mulVec, dotProduct]

omit [Fintype K] [DecidableEq K] in
/-- An element-wise nonlinearity commutes with a selection: `S f(x) = f(S x)`. -/
lemma sel_mulVec_comp (ι : K → N) (φ : ℝ → ℝ) (x : N → ℝ) :
    sel ι *ᵥ (fun n => φ (x n)) = fun i => φ ((sel ι *ᵥ x) i) := by
  rw [sel_mulVec, sel_mulVec]

/-- The **DLR-P core field** (arXiv 2512.15703, Sec. 3.2) for `∂ₜ x = A f(x)` with an element-wise
`f = φ`: `Ṁ_Q = (E_Qᵀ A E_Q) (S E_Q)⁻¹ f(S E_Q M_Q)`.  The nonlinearity is evaluated only at the
`|K|` interpolation points. -/
noncomputable def fieldP (EQ : Matrix N K ℝ) (S : Matrix K N ℝ) (A : Matrix N N ℝ) (φ : ℝ → ℝ)
    (M : K → ℝ) : K → ℝ :=
  (EQᵀ * A * EQ) *ᵥ ((S * EQ)⁻¹ *ᵥ fun i => φ (((S * EQ) *ᵥ M) i))

/-- The **interpolative (DLR-X) core field** (arXiv 2512.15703, Sec. 3.2):
`Ṁ_X = (S E_Q E_Qᵀ A E_X) f(M_X)`. -/
noncomputable def fieldX (EQ : Matrix N K ℝ) (S : Matrix K N ℝ) (A : Matrix N N ℝ) (φ : ℝ → ℝ)
    (M : K → ℝ) : K → ℝ :=
  (S * EQ * EQᵀ * A * interpBasis EQ S) *ᵥ fun i => φ (M i)

omit [DecidableEq N] [DecidableEq K] in
/-- The image of a solution of `ẏ = f(t, y)` under a matrix `B` with `B f(t, x) = g(t, B x)`
solves `ż = g(t, z)`. -/
theorem odeSolution_mulVec {K' : Type*} [Fintype K'] (B : Matrix K' K ℝ)
    {f : ℝ → (K → ℝ) → (K → ℝ)} {g : ℝ → (K' → ℝ) → (K' → ℝ)}
    (hfg : ∀ t x, B *ᵥ f t x = g t (B *ᵥ x)) {y : ℝ → K → ℝ} {a b : ℝ}
    (hy : ODESolution f y a b) : ODESolution g (fun t => B *ᵥ y t) a b := by
  let Lc : (K → ℝ) →L[ℝ] (K' → ℝ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin B)
  have hLc : ∀ v, Lc v = B *ᵥ v := fun v => rfl
  refine ⟨?_, fun t ht => ?_⟩
  · have := Lc.continuous.comp_continuousOn hy.cont
    simpa [Function.comp_def, hLc] using this
  · have h := Lc.hasFDerivAt.comp_hasDerivWithinAt t (hy.deriv t ht)
    rw [hLc, hfg] at h
    simpa [Function.comp_def, hLc] using h

/-- **DLR-P is the oblique Petrov–Galerkin DLRA, with `f` evaluated only at the interpolation
points** (arXiv 2512.15703, Sec. 3.2).  For a selection `S = sel ι` and any `E_Q`, the DLR-P core
field lifts to the full-space field
`E_Q Ṁ_Q = Π_QQ A Π_QX f(E_Q M_Q)`, with `Π_QQ = E_Q E_Qᵀ` and the DEIM projector
`Π_QX = E_Q (S E_Q)⁻¹ S`; hence a solution `M_Q` of the core equation gives a solution
`x = E_Q M_Q` of `ẋ = Π_QQ A Π_QX f(x)`.  For orthonormal `E_Q` this is the orthogonal Galerkin
projection of `A` applied to the interpolant `Π_QX f(x)` of the nonlinearity, which by
`sel_mulVec_comp` only uses the values `f(x)_{ι(i)} = φ(x_{ι(i)})`. -/
theorem dlrP_full {EQ : Matrix N K ℝ} {ι : K → N} (A : Matrix N N ℝ) (φ : ℝ → ℝ)
    {MQ : ℝ → K → ℝ} {a b : ℝ} (hM : ODESolution (fun _ => fieldP EQ (sel ι) A φ) MQ a b) :
    (∀ M, EQ *ᵥ fieldP EQ (sel ι) A φ M =
      (EQ * EQᵀ * A * obliqueProj EQ (sel ι)ᵀ) *ᵥ (fun n => φ ((EQ *ᵥ M) n))) ∧
    ODESolution (fun _ x => (EQ * EQᵀ * A * obliqueProj EQ (sel ι)ᵀ) *ᵥ (fun n => φ (x n)))
      (fun t => EQ *ᵥ MQ t) a b := by
  have key : ∀ M, EQ *ᵥ fieldP EQ (sel ι) A φ M =
      (EQ * EQᵀ * A * obliqueProj EQ (sel ι)ᵀ) *ᵥ (fun n => φ ((EQ *ᵥ M) n)) := by
    intro M
    have hre : EQ * EQᵀ * A * obliqueProj EQ (sel ι)ᵀ =
        EQ * EQᵀ * A * EQ * (sel ι * EQ)⁻¹ * sel ι := by
      rw [obliqueProj, Matrix.transpose_transpose]; simp only [Matrix.mul_assoc]
    rw [hre, ← Matrix.mulVec_mulVec _ _ (sel ι), sel_mulVec_comp,
      Matrix.mulVec_mulVec M (sel ι) EQ, fieldP]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  exact ⟨key, odeSolution_mulVec EQ (fun _ M => key M) hM⟩

omit [DecidableEq N] in
/-- **DLR-P and interpolative DLR-X dynamics coincide** (arXiv 2512.15703, Sec. 3.2).  If `S E_Q`
is invertible, the conversion `M_X = (S E_Q) M_Q` (eq. (28)) maps solutions of the DLR-P core
equation `Ṁ_Q = (E_Qᵀ A E_Q)(S E_Q)⁻¹ f(S E_Q M_Q)` exactly onto solutions of the DLR-X core
equation `Ṁ_X = (S E_Q E_Qᵀ A E_X) f(M_X)`, and both represent the same state:
`E_Q M_Q(t) = E_X M_X(t)`.  (`S` is an arbitrary matrix here; the identity behind it is
`(S E_Q)⁻¹ S E_Q E_Qᵀ A = E_Qᵀ A`.) -/
theorem dlrP_iff_dlrX {EQ : Matrix N K ℝ} {S : Matrix K N ℝ} (hS : IsUnit (S * EQ).det)
    (A : Matrix N N ℝ) (φ : ℝ → ℝ) {MQ : ℝ → K → ℝ} {a b : ℝ} :
    (ODESolution (fun _ => fieldP EQ S A φ) MQ a b ↔
      ODESolution (fun _ => fieldX EQ S A φ) (fun t => (S * EQ) *ᵥ MQ t) a b) ∧
    ∀ t, EQ *ᵥ MQ t = interpBasis EQ S *ᵥ ((S * EQ) *ᵥ MQ t) := by
  have hinv : (S * EQ)⁻¹ * (S * EQ) = 1 := Matrix.nonsing_inv_mul _ hS
  have hinv' : (S * EQ) * (S * EQ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hS
  have hconj : ∀ M, (S * EQ) *ᵥ fieldP EQ S A φ M = fieldX EQ S A φ ((S * EQ) *ᵥ M) := by
    intro M
    simp only [fieldP, fieldX, interpBasis, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  refine ⟨⟨odeSolution_mulVec (S * EQ) (fun _ M => hconj M), fun hX => ?_⟩, fun t => ?_⟩
  · have hconj' : ∀ M, (S * EQ)⁻¹ *ᵥ fieldX EQ S A φ M = fieldP EQ S A φ ((S * EQ)⁻¹ *ᵥ M) := by
      intro M
      have := hconj ((S * EQ)⁻¹ *ᵥ M)
      rw [Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec] at this
      rw [← this, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    have := odeSolution_mulVec (S * EQ)⁻¹ (fun _ M => hconj' M) hX
    simpa [Matrix.mulVec_mulVec, hinv] using this
  · rw [interpBasis, Matrix.mulVec_mulVec, Matrix.mul_assoc, hinv, Matrix.mul_one]

/-- **The orthogonal projection `E_Q E_Qᵀ` is needed in the DLR-P field** (arXiv 2512.15703,
Sec. 3.2: "`(S E_Q)⁻¹ S A ≠ E_Q^† A`").  For `E_Q = (3/5, 4/5)ᵀ` (orthonormal), the selection of the
first point (`S E_Q = 3/5` invertible) and `A = I`, `(S E_Q)⁻¹ S A ≠ E_Qᵀ A`, while
`(S E_Q)⁻¹ S E_Q E_Qᵀ A = E_Qᵀ A` (here with `A = I`; in general whenever `S E_Q` is
invertible). -/
theorem selection_not_left_invertible :
    let EQ : Matrix (Fin 2) (Fin 1) ℝ := !![3 / 5; 4 / 5]
    let S : Matrix (Fin 1) (Fin 2) ℝ := sel fun _ => 0
    EQᵀ * EQ = 1 ∧ IsUnit (S * EQ).det ∧ (S * EQ)⁻¹ * S ≠ EQᵀ ∧
      (S * EQ)⁻¹ * S * EQ * EQᵀ = EQᵀ := by
  intro EQ S
  have hSE : S * EQ = !![3 / 5] := by
    ext i j; fin_cases i; fin_cases j; simp [S, EQ, sel, Matrix.mul_apply]
  have hdet : IsUnit (S * EQ).det := by
    rw [hSE]; simp [Matrix.det_unique]
  refine ⟨?_, hdet, fun h => ?_, ?_⟩
  · ext i j; fin_cases i; fin_cases j; simp [EQ, Matrix.mul_apply]; norm_num
  · have h1 := congrFun (congrFun h 0) 1
    simp [S, EQ, sel, Matrix.mul_apply] at h1
    norm_num at h1
  · rw [Matrix.mul_assoc _ S EQ, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]

end DLRP

/-! ## Sec. 3.3: Galerkin Runge–Kutta steps on a stage-targeting basis -/

section RungeKutta

open RungeKuttaBUG

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An idempotent map fixes its range. -/
lemma fix_of_mem_range {P : E →L[ℝ] E} (hP : IsIdempotentElem P) {x : E} (hx : x ∈ Set.range P) :
    P x = x := by
  obtain ⟨w, rfl⟩ := hx
  have := congrArg (fun T : E →L[ℝ] E => T w) hP.eq
  simpa using this

/-- **The full Runge–Kutta step is a Galerkin step** (arXiv 2512.15703, Sec. 3.3, any tableau,
explicit or implicit).  If the stage projectors fix the stage values `Z i` of the full RK step and
the final projector fixes its result `z₁`, then `(Z, z₁)` solves the Galerkin RK equations
`Y i = R i (y + h ∑ⱼ aᵢⱼ F(Y j))`, `y₁ = R_f (y + h ∑ᵢ bᵢ F(Y i))`
(`RungeKuttaBUG.IsGalerkinRKStep`). -/
theorem galerkinRK_of_fix_stages {s : ℕ} {F : ℝ → E → E} {a : Fin s → Fin s → ℝ}
    {b c : Fin s → ℝ} {R : Fin s → E →L[ℝ] E} {Rf : E →L[ℝ] E} {t h : ℝ} {y : E}
    {Z : Fin s → E} {z₁ : E} (hZ : IsGalerkinRKStep F a b c (fun _ => 1) 1 t h y Z z₁)
    (hRZ : ∀ i, R i (Z i) = Z i) (hRf : Rf z₁ = z₁) :
    IsGalerkinRKStep F a b c R Rf t h y Z z₁ := by
  refine ⟨fun i => ?_, ?_⟩
  · have hZi := hZ.1 i
    simp only [one_apply_eq_self] at hZi
    rw [← hZi, hRZ i]
  · have hz := hZ.2
    simp only [one_apply_eq_self] at hz
    rw [← hz, hRf]

/-- **Galerkin RK = full RK when the basis contains all stage values** (arXiv 2512.15703,
Sec. 3.3, explicit tableaux such as RK4).  If the stage projectors fix the stage values `Z i` and
the final projector fixes the result `z₁` of the full explicit RK step, the Galerkin RK step
coincides with the full one (stages and result).  Compared with
`RungeKuttaBUG.galerkinRK_eq_rk`, the final projector only has to fix `z₁ = y_{n+1}`, not `y`
and the weighted stage derivatives. -/
theorem galerkinRK_eq_of_fix_stages {s : ℕ} {F : ℝ → E → E} {a : Fin s → Fin s → ℝ}
    {b c : Fin s → ℝ} (ha : ∀ i j, i ≤ j → a i j = 0) {R : Fin s → E →L[ℝ] E} {Rf : E →L[ℝ] E}
    {t h : ℝ} {y : E} {Y Z : Fin s → E} {y₁ z₁ : E}
    (hG : IsGalerkinRKStep F a b c R Rf t h y Y y₁)
    (hZ : IsGalerkinRKStep F a b c (fun _ => 1) 1 t h y Z z₁)
    (hRZ : ∀ i, R i (Z i) = Z i) (hRf : Rf z₁ = z₁) : Y = Z ∧ y₁ = z₁ := by
  have key : ∀ k : ℕ, ∀ i : Fin s, i.val < k → Y i = Z i := by
    intro k
    induction k with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ k ih =>
      intro i hi
      have hsum : ∑ j, a i j • F (t + c j * h) (Y j) = ∑ j, a i j • F (t + c j * h) (Z j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hw : a i j = 0
        · simp [hw]
        · have hji : j < i := lt_of_not_ge fun hij => hw (ha i j hij)
          rw [ih j (by have : j.val < i.val := hji; omega)]
      have hZi := hZ.1 i
      simp only [one_apply_eq_self] at hZi
      rw [hG.1 i, hsum, ← hZi, hRZ i]
  have hYZ : Y = Z := funext fun i => key s i i.isLt
  refine ⟨hYZ, ?_⟩
  have hz := hZ.2
  simp only [one_apply_eq_self] at hz
  rw [hG.2, hYZ, ← hz, hRf]

/-- **Uniqueness of Galerkin RK stages** for implicit tableaux (needed for Crank–Nicolson): if
`F` is `L`-Lipschitz and `‖R i‖ |h| L ∑ⱼ |aᵢⱼ| ≤ q < 1` for every stage, two solutions of the
Galerkin RK equations coincide. -/
theorem galerkinRK_unique {s : ℕ} {F : ℝ → E → E} {a : Fin s → Fin s → ℝ} {b c : Fin s → ℝ}
    {R : Fin s → E →L[ℝ] E} {Rf : E →L[ℝ] E} {t h : ℝ} {y : E} {Y Y' : Fin s → E}
    {y₁ y₁' : E} {L q : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hq : q < 1)
    (hR : ∀ i, ‖R i‖ * (|h| * (L * ∑ j, |a i j|)) ≤ q)
    (hG : IsGalerkinRKStep F a b c R Rf t h y Y y₁)
    (hG' : IsGalerkinRKStep F a b c R Rf t h y Y' y₁') : Y = Y' ∧ y₁ = y₁' := by
  have hYY : Y = Y' := by
    rcases isEmpty_or_nonempty (Fin s) with hs | hs
    · funext i; exact isEmptyElim i
    obtain ⟨i0, hi0⟩ := Finite.exists_max fun i => ‖Y i - Y' i‖
    have hstage : ∀ i, ‖Y i - Y' i‖ ≤ q * ‖Y i0 - Y' i0‖ := by
      intro i
      have hdiff : Y i - Y' i = R i (h • ∑ j, a i j •
          (F (t + c j * h) (Y j) - F (t + c j * h) (Y' j))) := by
        rw [hG.1 i, hG'.1 i, ← map_sub]
        congr 1
        simp only [smul_sub, Finset.sum_sub_distrib]
        abel
      have hsum : ‖∑ j, a i j • (F (t + c j * h) (Y j) - F (t + c j * h) (Y' j))‖ ≤
          L * (∑ j, |a i j|) * ‖Y i0 - Y' i0‖ := by
        calc _ ≤ ∑ j, ‖a i j • (F (t + c j * h) (Y j) - F (t + c j * h) (Y' j))‖ :=
              norm_sum_le _ _
          _ ≤ ∑ j, |a i j| * (L * ‖Y i0 - Y' i0‖) := Finset.sum_le_sum fun j _ => by
              rw [norm_smul, Real.norm_eq_abs]
              exact mul_le_mul_of_nonneg_left
                ((hF _ _ _).trans (mul_le_mul_of_nonneg_left (hi0 j) hL)) (abs_nonneg _)
          _ = L * (∑ j, |a i j|) * ‖Y i0 - Y' i0‖ := by rw [← Finset.sum_mul]; ring
      rw [hdiff]
      calc _ ≤ ‖R i‖ * ‖h • ∑ j, a i j • (F (t + c j * h) (Y j) - F (t + c j * h) (Y' j))‖ :=
            (R i).le_opNorm _
        _ ≤ ‖R i‖ * (|h| * (L * (∑ j, |a i j|) * ‖Y i0 - Y' i0‖)) := by
            rw [norm_smul, Real.norm_eq_abs]
            gcongr
        _ = ‖R i‖ * (|h| * (L * ∑ j, |a i j|)) * ‖Y i0 - Y' i0‖ := by ring
        _ ≤ q * ‖Y i0 - Y' i0‖ := mul_le_mul_of_nonneg_right (hR i) (norm_nonneg _)
    have hD0 : ‖Y i0 - Y' i0‖ ≤ 0 := by nlinarith [hstage i0, norm_nonneg (Y i0 - Y' i0)]
    funext i
    exact sub_eq_zero.1 (norm_le_zero_iff.1 ((hi0 i).trans hD0))
  refine ⟨hYY, ?_⟩
  rw [hG.2, hG'.2, hYY]

/-- **Stage-derivative targets suffice for explicit RK** (arXiv 2512.15703, Sec. 3.3, target
`[M(t) k₁ … k_{s-1} M(t+Δt)]`).  For an explicit tableau, if the stage projectors fix `y` and
the stage derivatives `kⱼ = F(t + cⱼ h, Z j)` entering the stages, and the final projector fixes
`y_{n+1} = z₁`, the Galerkin RK step equals the full one.  The last derivative `k_s` (and any
derivative entering only through the weights `b`) need not be captured. -/
theorem galerkinRK_eq_of_fix_derivs {s : ℕ} {F : ℝ → E → E} {a : Fin s → Fin s → ℝ}
    {b c : Fin s → ℝ} (ha : ∀ i j, i ≤ j → a i j = 0) {R : Fin s → E →L[ℝ] E} {Rf : E →L[ℝ] E}
    {t h : ℝ} {y : E} {Y Z : Fin s → E} {y₁ z₁ : E}
    (hG : IsGalerkinRKStep F a b c R Rf t h y Y y₁)
    (hZ : IsGalerkinRKStep F a b c (fun _ => 1) 1 t h y Z z₁) (hy : ∀ i, R i y = y)
    (hk : ∀ i j, a i j ≠ 0 → R i (F (t + c j * h) (Z j)) = F (t + c j * h) (Z j))
    (hRf : Rf z₁ = z₁) : Y = Z ∧ y₁ = z₁ := by
  refine galerkinRK_eq_of_fix_stages ha hG hZ (fun i => ?_) hRf
  have hZi := hZ.1 i
  simp only [one_apply_eq_self] at hZi
  rw [hZi]
  exact proj_comb_eq (hy i) (hk i) h

/-! The classical fourth-order Runge–Kutta method is the core tableau `ButcherTableau.rk4`; the
arrays `rk4A`, `rk4B`, `rk4C` of an earlier version of this file were its arrays over `ℝ` (same
definitions; unification batch C8). -/

/-- **AP-RK4 with the target `[M(t) k₁ k₂ k₃ M(t+Δt)]` reproduces RK4** (arXiv 2512.15703,
Sec. 3.3).  If the range of the projector `P` (`P² = P`, orthogonal or interpolative) contains
`y_n`, the first three stage derivatives `k₁, k₂, k₃` and the result `y_{n+1}` of the full
classical RK4 step, then the Galerkin RK4 step with `P` coincides with the full RK4 step.  By
induction over the steps (not formalized here), if the target is captured at every step, the
projected trajectory is the RK4 trajectory; the fourth order of RK4 itself is not proved here.
The paper's per-core sweep and the subsequent rank truncation are not modelled; its
observed orders (4 for AP-RK4, 2 for AP-CN, 2 for projector splitting) are numerical and are not
formalized. -/
theorem apRK4_eq_rk4 {F : ℝ → E → E} {P : E →L[ℝ] E} (hP : IsIdempotentElem P) {t h : ℝ}
    {y : E} {Y Z : Fin 4 → E} {y₁ z₁ : E}
    (hZ : IsGalerkinRKStep F ButcherTableau.rk4.a ButcherTableau.rk4.b ButcherTableau.rk4.c
      (fun _ => 1) 1 t h y Z z₁)
    (hG : IsGalerkinRKStep F ButcherTableau.rk4.a ButcherTableau.rk4.b ButcherTableau.rk4.c
      (fun _ => P) P t h y Y y₁) (hy : y ∈ Set.range P)
    (hk : ∀ j : Fin 4, j ≠ 3 → F (t + ButcherTableau.rk4.c j * h) (Z j) ∈ Set.range P)
    (hz : z₁ ∈ Set.range P) : Y = Z ∧ y₁ = z₁ := by
  have ha : ∀ i j : Fin 4, i ≤ j → (ButcherTableau.rk4 : ButcherTableau ℝ 4).a i j = 0 :=
    ButcherTableau.rk4_isExplicit
  have h3 : ∀ i : Fin 4, (ButcherTableau.rk4 : ButcherTableau ℝ 4).a i 3 = 0 := fun i =>
    ButcherTableau.rk4_isExplicit i 3 (Fin.le_last i)
  refine galerkinRK_eq_of_fix_derivs ha hG hZ (fun _ => fix_of_mem_range hP hy)
    (fun i j hij => fix_of_mem_range hP (hk j fun hj => hij (hj ▸ h3 i))) (fix_of_mem_range hP hz)

/-- Butcher tableau of the Crank–Nicolson (trapezoidal, 2-stage Lobatto IIIA) method. -/
noncomputable def cnA : Fin 2 → Fin 2 → ℝ := ![![0, 0], ![1 / 2, 1 / 2]]

/-- Weights of Crank–Nicolson. -/
noncomputable def cnB : Fin 2 → ℝ := ![1 / 2, 1 / 2]

/-- Nodes of Crank–Nicolson. -/
noncomputable def cnC : Fin 2 → ℝ := ![0, 1]

/-- **AP-CN with the target `[M(t) M(t+Δt)]` reproduces Crank–Nicolson** (arXiv 2512.15703,
Sec. 3.3).  Let `(Z, z₁)` be a full Crank–Nicolson step `z₁ = y + h/2 (F(t, y) + F(t+h, z₁))`
(written as the 2-stage Lobatto IIIA method, so `Z 0 = y`, `Z 1 = z₁`).  If the range of the
projector `P` contains `y_n = y` and `y_{n+1} = z₁`, then the full step solves the Galerkin CN
equations with `P`; if moreover `F` is `L`-Lipschitz with `‖P‖ |h| L < 1`, every Galerkin CN step
equals it.  Hence, if the target is captured at every step, AP-CN reproduces the CN trajectory
(the induction over the steps and the second order of CN are not formalized here).  Here
Crank–Nicolson is the trapezoidal rule; the paper's linear examples use it with the field at
`t_{n+1/2}`, which is not modelled. -/
theorem apCN_eq_cn {F : ℝ → E → E} {P : E →L[ℝ] E} (hP : IsIdempotentElem P) {t h : ℝ} {y : E}
    {Z : Fin 2 → E} {z₁ : E} (hZ : IsGalerkinRKStep F cnA cnB cnC (fun _ => 1) 1 t h y Z z₁)
    (hy : y ∈ Set.range P) (hz : z₁ ∈ Set.range P) :
    IsGalerkinRKStep F cnA cnB cnC (fun _ => P) P t h y Z z₁ ∧
      ∀ {L : ℝ}, IsLipschitzField F L → 0 ≤ L → ‖P‖ * (|h| * L) < 1 →
        ∀ {Y : Fin 2 → E} {y₁ : E}, IsGalerkinRKStep F cnA cnB cnC (fun _ => P) P t h y Y y₁ →
          Y = Z ∧ y₁ = z₁ := by
  have hZ0 : Z 0 = y := by
    have := hZ.1 0
    simpa [cnA, Fin.sum_univ_two] using this
  have hZ1 : Z 1 = z₁ := by
    have h1 := hZ.1 1
    have h2 := hZ.2
    simp only [one_apply_eq_self] at h1 h2
    rw [h1, h2]
    simp [cnA, cnB, Fin.sum_univ_two]
  have hstage : ∀ i, P (Z i) = Z i := by
    rw [Fin.forall_fin_two, hZ0, hZ1]
    exact ⟨fix_of_mem_range hP hy, fix_of_mem_range hP hz⟩
  have hGal := galerkinRK_of_fix_stages (R := fun _ => P) hZ hstage (fix_of_mem_range hP hz)
  refine ⟨hGal, fun {L} hF hL hc {Y} {y₁} hG => ?_⟩
  have hR : ∀ i, ‖(fun _ => P : Fin 2 → E →L[ℝ] E) i‖ * (|h| * (L * ∑ j, |cnA i j|)) ≤
      ‖P‖ * (|h| * L) := by
    have h0 : ∑ j, |cnA 0 j| = 0 := by simp [cnA, Fin.sum_univ_two]
    have h1 : ∑ j, |cnA 1 j| = 1 := by norm_num [cnA, Fin.sum_univ_two]
    rw [Fin.forall_fin_two]
    dsimp only
    refine ⟨?_, ?_⟩
    · rw [h0, mul_zero, mul_zero, mul_zero]; positivity
    · rw [h1, mul_one]
  exact galerkinRK_unique hF hL hc hR hG hGal

end RungeKutta

/-! ## Sec. 4.1: interpolative DLRA with nonlinear (upwind) fluxes -/

section Upwind

variable {n : ℕ} [NeZero n] {K : Type*} [Fintype K] [DecidableEq K]

/-- One step of a conservative scheme on the periodic grid `ℤ/n` with an arbitrary (possibly
branch-dependent) numerical flux `φ`:
`u_j ↦ u_j - λ (φ(u_j, u_{j+1}) - φ(u_{j-1}, u_j))`.  For Burgers' equation (arXiv 2512.15703,
eqs. (44)–(45)) `φ(u_j, u_{j+1}) = ũ_{j+1/2}²` with the upwind interface value `ũ_{j+1/2}`
chosen by cases on the signs of `u_{j+1} - u_j` and `u_j + u_{j+1}`, and `λ = Δt/Δx`. -/
def upwindStep (φ : ℝ → ℝ → ℝ) (lam : ℝ) (u : Fin n → ℝ) : Fin n → ℝ :=
  fun j => u j - lam * (φ (u j) (u (j + 1)) - φ (u (j - 1)) (u j))

/-- The **DLR-X core update** of the upwind scheme (arXiv 2512.15703, Sec. 4.1, "Solving"):
on the core `M` (the values at the interpolation points) with the effective shift matrices
`S^±_eff` (eq. (46)), `M_i ↦ M_i - λ (φ(M_i, (S⁺_eff M)_i) - φ((S⁻_eff M)_i, M_i))`.  It evaluates
the flux `φ` at only `2 |K|` pairs (instead of `2 n` for the full grid). -/
def dlrxUpwindStep (φ : ℝ → ℝ → ℝ) (lam : ℝ) (Sp Sm : Matrix K K ℝ) (M : K → ℝ) : K → ℝ :=
  fun i => M i - lam * (φ (M i) ((Sp *ᵥ M) i) - φ ((Sm *ᵥ M) i) (M i))

/-- **Interpolative DLRA handles branch-dependent upwind fluxes exactly at the selected points**
(arXiv 2512.15703, Sec. 4.1, eq. (46) and the "Solving" step).  Let `S = sel ι` select the grid
points `𝓘 = ι(K)` and let the interpolating functions `E` be cardinal (`S E = I`); let
`S^± = sel (· ± 1)` be the periodic shifts and `S^±_eff = S S^± E` (eq. (46)).  For a state on the
manifold, `u = E M`:

* `S^±_eff M = u[𝓘 ± 1]` and `M = u[𝓘]`: the effective shifts return the exact neighbouring grid
  values, so the branch-dependent flux sees the same arguments as in the full scheme;
* the DLR-X core update equals the full upwind step at the selected points,
  `M' = (upwindStep u)[𝓘]`;
* the new state is the interpolative projection of the full step: `E M' = Π (upwindStep u)` with
  `Π = E S`.

The flux `φ` is arbitrary (no continuity or monotonicity is used).  The decimation (CUR basis
update) of the paper is not modelled. -/
theorem dlrx_upwind {E : Matrix (Fin n) K ℝ} {ι : K → Fin n} (hSE : sel ι * E = 1)
    (φ : ℝ → ℝ → ℝ) (lam : ℝ) (M : K → ℝ) :
    (sel ι * sel (fun j : Fin n => j + 1) * E) *ᵥ M = (fun i => (E *ᵥ M) (ι i + 1)) ∧
      (sel ι * sel (fun j : Fin n => j - 1) * E) *ᵥ M = (fun i => (E *ᵥ M) (ι i - 1)) ∧
      M = (fun i => (E *ᵥ M) (ι i)) ∧
      dlrxUpwindStep φ lam (sel ι * sel (fun j : Fin n => j + 1) * E)
          (sel ι * sel (fun j : Fin n => j - 1) * E) M =
        (fun i => upwindStep φ lam (E *ᵥ M) (ι i)) ∧
      E *ᵥ dlrxUpwindStep φ lam (sel ι * sel (fun j : Fin n => j + 1) * E)
          (sel ι * sel (fun j : Fin n => j - 1) * E) M =
        (E * sel ι) *ᵥ upwindStep φ lam (E *ᵥ M) := by
  have hp : (sel ι * sel (fun j : Fin n => j + 1) * E) *ᵥ M = fun i => (E *ᵥ M) (ι i + 1) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, sel_mulVec, sel_mulVec]
  have hm : (sel ι * sel (fun j : Fin n => j - 1) * E) *ᵥ M = fun i => (E *ᵥ M) (ι i - 1) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, sel_mulVec, sel_mulVec]
  have h0 : M = fun i => (E *ᵥ M) (ι i) := by
    rw [← sel_mulVec, Matrix.mulVec_mulVec, hSE, Matrix.one_mulVec]
  have hstep : dlrxUpwindStep φ lam (sel ι * sel (fun j : Fin n => j + 1) * E)
      (sel ι * sel (fun j : Fin n => j - 1) * E) M =
      (fun i => upwindStep φ lam (E *ᵥ M) (ι i)) := by
    funext i
    have h0i : M i = (E *ᵥ M) (ι i) := congrFun h0 i
    simp only [dlrxUpwindStep, upwindStep, hp, hm]
    rw [h0i]
  refine ⟨hp, hm, h0, hstep, ?_⟩
  rw [hstep, ← Matrix.mulVec_mulVec, sel_mulVec]

/-- Lebesgue-type bound for any linear map `P` fixing `w`: `‖x - P x‖ ≤ (1 + ‖P‖) ‖x - w‖`. -/
theorem norm_sub_le_one_add_of_fix {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (P : V →L[ℝ] V) {x w : V} (hw : P w = w) : ‖x - P x‖ ≤ (1 + ‖P‖) * ‖x - w‖ := by
  have : x - P x = (x - w) - P (x - w) := by rw [map_sub, hw]; abel
  rw [this, add_mul, one_mul]
  exact (norm_sub_le _ _).trans (add_le_add le_rfl (P.le_opNorm _))

/-- **Error of the interpolative upwind step** (arXiv 2512.15703, Sec. 4.1; collocation DLRA
normal-component bound `(1 + ‖Π‖) ‖(I - P) F‖`).  With `Π = E S` acting on grid functions (as a
continuous linear map; `‖Π‖` is the operator norm for the max-norm of `Fin n → ℝ`, i.e. the
Lebesgue constant of the interpolation), the DLR-X state after one upwind step deviates from the
full upwind step by at most `(1 + ‖Π‖)` times the distance of the full step to *any* element
`E c` of the approximation space; with `E c = P (upwindStep u)` for a projector `P` onto
`range E` this is `(1 + ‖Π‖) ‖(I - P) upwindStep u‖`. -/
theorem dlrx_upwind_error {E : Matrix (Fin n) K ℝ} {ι : K → Fin n} (hSE : sel ι * E = 1)
    (φ : ℝ → ℝ → ℝ) (lam : ℝ) (M c : K → ℝ) :
    ‖upwindStep φ lam (E *ᵥ M) -
        E *ᵥ dlrxUpwindStep φ lam (sel ι * sel (fun j : Fin n => j + 1) * E)
          (sel ι * sel (fun j : Fin n => j - 1) * E) M‖ ≤
      (1 + ‖LinearMap.toContinuousLinearMap (Matrix.mulVecLin (E * sel ι))‖) *
        ‖upwindStep φ lam (E *ᵥ M) - E *ᵥ c‖ := by
  rw [(dlrx_upwind hSE φ lam M).2.2.2.2]
  refine norm_sub_le_one_add_of_fix (LinearMap.toContinuousLinearMap
    (Matrix.mulVecLin (E * sel ι))) ?_
  change (E * sel ι) *ᵥ (E *ᵥ c) = E *ᵥ c
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hSE, Matrix.mul_one]

omit [Fintype K] [DecidableEq K] in
/-- Cardinal interpolating functions exist for any injective selection: `S Sᵀ = I`. -/
theorem sel_mul_transpose {N : Type*} [Fintype N] [DecidableEq N] {ι : K → N}
    (hι : Function.Injective ι) [DecidableEq K] : sel ι * (sel ι)ᵀ = 1 := by
  ext i i'
  simp [sel, Matrix.mul_apply, Matrix.one_apply, hι.eq_iff]

end Upwind

/-- The Runge–Kutta matrix of classical RK4, replaced by the core `ButcherTableau.rk4.a`. -/
@[deprecated "use `ButcherTableau.rk4.a`" (since := "2026-11-10")]
noncomputable def rk4A : Fin 4 → Fin 4 → ℝ := ButcherTableau.rk4.a

/-- The weights of classical RK4, replaced by the core `ButcherTableau.rk4.b`. -/
@[deprecated "use `ButcherTableau.rk4.b`" (since := "2026-11-10")]
noncomputable def rk4B : Fin 4 → ℝ := ButcherTableau.rk4.b

/-- The nodes of classical RK4, replaced by the core `ButcherTableau.rk4.c`. -/
@[deprecated "use `ButcherTableau.rk4.c`" (since := "2026-11-10")]
noncomputable def rk4C : Fin 4 → ℝ := ButcherTableau.rk4.c

end LeanDLRA.Literature.P2512_15703
