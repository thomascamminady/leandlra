import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Stability.Conservation

/-!
# Energy-stable conservative DLRA for the Su–Olson problem (arXiv 2307.07538, part a)

Baumann, Einkemmer, Klingenberg, Kusch, *Energy stable and conservative dynamical low-rank
approximation for the Su–Olson problem*.  This module proves the paper's energy results for its
actual discretization, not for an abstract core: the periodic stencils `Dˣ`, `Dˣˣ`, `D⁺` on `ZMod n`
and summation by parts (Lemma 1: `Dx_transpose`, `Dxx_transpose`, `Dxx_eq`, `Dx_quadratic`,
`Dxx_quadratic`, `Dxx_nonpos`); the exact semi-discrete energy law for the augmented S-step coupled
to the internal energy (Theorem 1: `hasDerivAt_energy`, `energy_antitone`); the instability of the
naive IMEX scheme (Theorem 2: `naive_not_energy_stable`); the key inequality (Lemma 2: `lemma2`,
with its exact value `lemma2_eq` and the variants `lemma2_sharp`, `lemma2'`, `lemma2_sharp'`); and
one full step of the coupled implicit scheme (16) with conservative truncation (Theorem 3:
`theorem3`, `theorem3_sharp`), written out substep by substep in `IsCoupledStep` and
`IsConservativeTruncation`.  Theorem 4 is in the companion module, part b.

## Differences from the paper

* **`theorem3` assumes `e₀ ∈ range V⁰`, which the paper does not state.**  The paper's proof
  tests with `u¹` and removes the Galerkin projection (`P^V P^X u¹ = u¹` for `k ≠ 0`), which
  requires `u★ (1 - e₀ e₀ᵀ)` to stay in the Galerkin space; this holds if `e₀ ∈ range V★`.  The
  paper says nothing on this, and nothing on how `V⁰` is built.  From the second step on the
  hypothesis holds by construction (`V₁_e₀`, the first column of `V̂ = [e₁, V^rem]`), so
  `theorem3` can be iterated, and it covers the first step if `V⁰` contains `e₀`.  It cannot be
  dropped from the sharp form: `not_energy_stable_without_e₀` is a proved example (`n = 3`,
  `N = 2`, spectrum `±κ`, `Δt κ = Δx`) in which all other hypotheses of `theorem3_sharp` hold and
  the energy increases, and `legendreTwo_not_energy_stable` instantiates it with the true `N = 2`
  Legendre matrix at `Δt = √3 Δx`, where `Δt |σ_k| = Δx`.  Neither of these is a counterexample to
  the printed statement, whose condition is `Δt ≤ Δx` for the Legendre matrix.  Whether the printed
  statement holds without `e₀ ∈ range V⁰` is not decided here.
* **`σ ≥ 0` is a hypothesis** of Theorems 1 and 3.  The paper does not state it; its proofs need it.
* **"Strictly negative" in the proof of Theorem 1 is false.**  The theorem says `≤ 0`, which is what
  holds; the right-hand side vanishes at the equilibrium (`energy_rate_eq_zero_at_equilibrium`).
* **`|σ_k| ≤ 1` is proved**, where the paper asserts it (`IsEigenDecomp.abs_le_one`): `A` is the
  compression of multiplication by `μ ∈ [-1, 1]`, so the bound holds for every orthonormal family
  (`momentMatrix_quadratic_le`).  `momentMatrix` is defined by the paper's integrals, for continuous
  orthonormal `P`.  `IsOrthonormalFamily` is instantiated for `N = 2` (`legendreTwo`); the
  orthonormality of the Legendre polynomials of every degree is not formalized.
* **Truncation.** Theorem 3 is formalized with the conservative truncation of Section 6; the
  paper's (16) also allows the truncation of its reference [6].  The paper notes only that the
  zeroth moment is unchanged; that the norm does not increase is what its Theorem 3 needs, and we
  prove it (`IsConservativeTruncation.norm_le`).
  `IsConservativeTruncation` allows any orthonormal `U`, and `svd_truncation_eq_left_proj` shows the
  SVD truncation of Section 6 has this form.
* **Lemma 2** is proved without a Fourier transform: `Dˣ ± Dˣˣ` is a single upwind difference, which
  gives the same exact value.  The paper's flux has transposed stencils (`flux`); `lemma2'` is the
  variant with `Dˣ`, `Dˣˣ`.  Only the sharp condition `Δt |σ_k| ≤ Δx` is used.
* **Theorem 2** is proved for all `σ, Δt > 0`, all grids and all matrices `A`, `|A|`, which is what
  the paper's proof gives (it states existence).  We fix `u¹ = 1` and `α` the midpoint of its
  interval.
* **Stencils** act on `ZMod n`, so for `n ≤ 2`, where the printed entries collide, the matrices are
  the periodic stencils, by adding the contributions.  `|A|` is defined from any eigendecomposition;
  `exists_isEigenDecomp` shows one exists.
* **(16f)** is printed with the condition `k ≠ 0` on `L_{mk}`.  We read it as `m ≠ 0`, the moment
  index, as the paper's relation between `u¹` and `u★` at the start of the proof of Theorem 3
  requires (`IsCoupledStep.augmented_eq`, which we derive).  A column reading would contradict it.
* **Indices.**  (9a) and (16a) print `D^x_{qp} K_{pj}` with `p` also the free index of the left
  side; `kStar` reads `Dˣ K`, as in (9c) and (16c), which `sStepField` and `sStar` follow.  Lemma 2
  prints the transposed stencils `D_{ji} u_{jk}`; this is the adjoint that arises in the proof of
  Theorem 3 (`inner_transport_adjoint`), and `flux` keeps it.  (16d) prints `A_{0ℓ}`; `rhsR` uses
  `A_{ℓ0}`, the same since `A` is symmetric.
* **QR factorizations** are recorded by what they give: orthonormal columns, and a range containing
  the factored columns.  The result depends on the bases only through these ranges.
* The paper describes `⟨·⟩_μ` only in words, as integration over `μ ∈ [-1, 1]` (Section 2.1), and
  calls the `P_n` normalized Legendre polynomials, so the weight `w` is a parameter.  Checked
  against the arXiv v2 PDF.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2307_07538

/-! ### Periodic stencils and summation by parts -/

/-- The central first difference `(Dˣ y)ₚ = (yₚ₊₁ - yₚ₋₁) / (2 Δx)` on a periodic grid. -/
noncomputable def Dx (n : ℕ) [NeZero n] (Δx : ℝ) : Matrix (ZMod n) (ZMod n) ℝ :=
  Matrix.of fun p q => ((if q = p + 1 then 1 else 0) - (if q = p - 1 then 1 else 0)) / (2 * Δx)

/-- The stabilizing second difference `(Dˣˣ y)ₚ = (yₚ₊₁ - 2 yₚ + yₚ₋₁) / (2 Δx)`. -/
noncomputable def Dxx (n : ℕ) [NeZero n] (Δx : ℝ) : Matrix (ZMod n) (ZMod n) ℝ :=
  Matrix.of fun p q =>
    ((if q = p + 1 then 1 else 0) - 2 * (if q = p then 1 else 0) + (if q = p - 1 then 1 else 0)) /
      (2 * Δx)

/-- The forward difference `(D⁺ y)ₚ = (yₚ₊₁ - yₚ) / √(2 Δx)`. -/
noncomputable def Dplus (n : ℕ) [NeZero n] (Δx : ℝ) : Matrix (ZMod n) (ZMod n) ℝ :=
  Matrix.of fun p q => ((if q = p + 1 then 1 else 0) - (if q = p then 1 else 0)) / √(2 * Δx)

/-- Moving the shift across an equation in `ZMod n`. -/
private theorem iff_add_one {n : ℕ} (p q : ZMod n) : p = q + 1 ↔ q = p - 1 :=
  ⟨fun h => by rw [h]; ring, fun h => by rw [h]; ring⟩

/-- Moving the shift across an equation in `ZMod n`. -/
private theorem iff_sub_one {n : ℕ} (p q : ZMod n) : p = q - 1 ↔ q = p + 1 :=
  ⟨fun h => by rw [h]; ring, fun h => by rw [h]; ring⟩

variable {n : ℕ} [NeZero n]

section Stencil

variable {κ : Type*}

/-- The stencil of `Dˣ` (arXiv 2307.07538, Section 3), acting on the columns of `u`. -/
theorem Dx_mul_apply (Δx : ℝ) (u : Matrix (ZMod n) κ ℝ) (p : ZMod n) (k : κ) :
    (Dx n Δx * u) p k = (u (p + 1) k - u (p - 1) k) / (2 * Δx) := by
  simp only [Matrix.mul_apply, Dx, Matrix.of_apply, div_mul_eq_mul_div, ← Finset.sum_div,
    sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- The stencil of `Dˣˣ` (arXiv 2307.07538, Section 3), acting on the columns of `u`. -/
theorem Dxx_mul_apply (Δx : ℝ) (u : Matrix (ZMod n) κ ℝ) (p : ZMod n) (k : κ) :
    (Dxx n Δx * u) p k = (u (p + 1) k - 2 * u p k + u (p - 1) k) / (2 * Δx) := by
  simp only [Matrix.mul_apply, Dxx, Matrix.of_apply, div_mul_eq_mul_div, ← Finset.sum_div,
    add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    mul_assoc, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The stencil of `D⁺` (arXiv 2307.07538, Section 3), acting on the columns of `u`. -/
theorem Dplus_mul_apply (Δx : ℝ) (u : Matrix (ZMod n) κ ℝ) (p : ZMod n) (k : κ) :
    (Dplus n Δx * u) p k = (u (p + 1) k - u p k) / √(2 * Δx) := by
  simp only [Matrix.mul_apply, Dplus, Matrix.of_apply, div_mul_eq_mul_div, ← Finset.sum_div,
    sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- The stencil of `(D⁺)ᵀ` (arXiv 2307.07538, used for Lemma 1). -/
theorem Dplus_transpose_mul_apply (Δx : ℝ) (u : Matrix (ZMod n) κ ℝ) (p : ZMod n) (k : κ) :
    ((Dplus n Δx)ᵀ * u) p k = (u (p - 1) k - u p k) / √(2 * Δx) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Dplus, Matrix.of_apply, iff_add_one,
    div_mul_eq_mul_div, ← Finset.sum_div, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_true]

end Stencil

/-- **Lemma 1** (arXiv 2307.07538, first part): `Dˣ` is skew. -/
theorem Dx_transpose (Δx : ℝ) : (Dx n Δx)ᵀ = -Dx n Δx := by
  ext p q
  have h1 := iff_add_one p q
  have h2 := iff_sub_one p q
  simp only [Matrix.transpose_apply, Dx, Matrix.of_apply, Matrix.neg_apply, h1, h2]
  ring

/-- **Lemma 1** (arXiv 2307.07538, second part): `Dˣˣ` is symmetric. -/
theorem Dxx_transpose (Δx : ℝ) : (Dxx n Δx)ᵀ = Dxx n Δx := by
  ext p q
  have h1 := iff_add_one p q
  have h2 := iff_sub_one p q
  have h3 : p = q ↔ q = p := eq_comm
  simp only [Matrix.transpose_apply, Dxx, Matrix.of_apply, h1, h2, h3]
  ring

/-- **Lemma 1** (arXiv 2307.07538, third part): `Dˣˣ = -(D⁺)ᵀ D⁺`.  The paper uses this in the form
`z ⬝ Dˣˣ z = -‖D⁺ z‖²`, see `Dxx_quadratic`. -/
theorem Dxx_eq {Δx : ℝ} (hΔx : 0 < Δx) : Dxx n Δx = -((Dplus n Δx)ᵀ * Dplus n Δx) := by
  have hs : √(2 * Δx) * √(2 * Δx) = 2 * Δx := Real.mul_self_sqrt (by positivity)
  have key : ∀ (w : Matrix (ZMod n) (ZMod n) ℝ) (p q : ZMod n),
      ((Dplus n Δx)ᵀ * (Dplus n Δx * w)) p q = -(Dxx n Δx * w) p q := by
    intro w p q
    rw [Dplus_transpose_mul_apply, Dplus_mul_apply, Dplus_mul_apply, Dxx_mul_apply,
      sub_add_cancel, ← sub_div, div_div, hs]
    ring
  ext p q
  have := key 1 p q
  rw [Matrix.mul_one, Matrix.mul_one] at this
  rw [Matrix.neg_apply, this, neg_neg]

/-- **Lemma 1** (arXiv 2307.07538), bilinear form of skewness: `y ⬝ Dˣ z = -z ⬝ Dˣ y`. -/
theorem Dx_bilinear (Δx : ℝ) (y z : ZMod n → ℝ) :
    y ⬝ᵥ (Dx n Δx *ᵥ z) = -(z ⬝ᵥ (Dx n Δx *ᵥ y)) := by
  have h : y ᵥ* Dx n Δx = -(Dx n Δx *ᵥ y) := by
    rw [← Matrix.mulVec_transpose, Dx_transpose, Matrix.neg_mulVec]
  rw [Matrix.dotProduct_mulVec, h, neg_dotProduct, dotProduct_comm]

/-- **Lemma 1** (arXiv 2307.07538): `z ⬝ Dˣ z = 0`. -/
theorem Dx_quadratic (Δx : ℝ) (z : ZMod n → ℝ) : z ⬝ᵥ (Dx n Δx *ᵥ z) = 0 := by
  have := Dx_bilinear Δx z z
  linarith

/-- **Lemma 1** (arXiv 2307.07538): `z ⬝ Dˣˣ z = -∑ₚ ((D⁺ z)ₚ)²`. -/
theorem Dxx_quadratic {Δx : ℝ} (hΔx : 0 < Δx) (z : ZMod n → ℝ) :
    z ⬝ᵥ (Dxx n Δx *ᵥ z) = -∑ p, (Dplus n Δx *ᵥ z) p ^ 2 := by
  rw [Dxx_eq hΔx, Matrix.neg_mulVec, dotProduct_neg, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.transpose_transpose]
  simp only [dotProduct, sq]

/-- **Lemma 1** (arXiv 2307.07538): `Dˣˣ` is negative semidefinite. -/
theorem Dxx_nonpos {Δx : ℝ} (hΔx : 0 < Δx) (z : ZMod n → ℝ) : z ⬝ᵥ (Dxx n Δx *ᵥ z) ≤ 0 := by
  rw [Dxx_quadratic hΔx]
  exact neg_nonpos.2 (Finset.sum_nonneg fun p _ => sq_nonneg _)

/-! ### The angular matrix -/

variable {N : ℕ}

/-- The matrix function `Q diag(f) Qᵀ`. -/
noncomputable def specFn (Q : Matrix (Fin N) (Fin N) ℝ) (f : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Q * Matrix.diagonal f * Qᵀ

/-- `|A| = Q |M| Qᵀ`, for the eigendecomposition `A = Q M Qᵀ`, `M = diag(s)`. -/
noncomputable def absA (Q : Matrix (Fin N) (Fin N) ℝ) (s : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  specFn Q fun k => |s k|

/-- `|A|^{1/2} = Q |M|^{1/2} Qᵀ`. -/
noncomputable def sqrtAbsA (Q : Matrix (Fin N) (Fin N) ℝ) (s : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  specFn Q fun k => √|s k|

/-- `A = Q M Qᵀ` with `Q` orthogonal and `M = diag(s)`. -/
structure IsEigenDecomp (A Q : Matrix (Fin N) (Fin N) ℝ) (s : Fin N → ℝ) : Prop where
  orth : Qᵀ * Q = 1
  eq : A = specFn Q s

section Spectral

variable {A Q : Matrix (Fin N) (Fin N) ℝ} {s : Fin N → ℝ}

/-- `Q` is orthogonal from both sides (arXiv 2307.07538, Section 3). -/
theorem IsEigenDecomp.orth' (d : IsEigenDecomp A Q s) : Q * Qᵀ = 1 :=
  mul_eq_one_comm.1 d.orth

/-- `Q diag(f) Qᵀ` is symmetric (arXiv 2307.07538, Section 3). -/
theorem specFn_transpose (Q : Matrix (Fin N) (Fin N) ℝ) (f : Fin N → ℝ) :
    (specFn Q f)ᵀ = specFn Q f := by
  simp [specFn, Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]

/-- Matrix functions multiply pointwise on the spectrum. -/
theorem specFn_mul_self (hQ : Qᵀ * Q = 1) (f g : Fin N → ℝ) :
    specFn Q f * specFn Q g = specFn Q (fun k => f k * g k) := by
  have : Q * Matrix.diagonal f * Qᵀ * (Q * Matrix.diagonal g * Qᵀ)
      = Q * Matrix.diagonal f * (Qᵀ * Q) * Matrix.diagonal g * Qᵀ := by
    simp only [Matrix.mul_assoc]
  rw [specFn, specFn, this, hQ, Matrix.mul_one, Matrix.mul_assoc Q, Matrix.diagonal_mul_diagonal,
    specFn]

/-- `Q` diagonalizes `Q diag(f) Qᵀ`. -/
theorem specFn_mul_Q (hQ : Qᵀ * Q = 1) (f : Fin N → ℝ) :
    specFn Q f * Q = Q * Matrix.diagonal f := by
  rw [specFn, Matrix.mul_assoc, hQ, Matrix.mul_one]

/-- `|A|^{1/2} |A|^{1/2} = |A|`. -/
theorem sqrtAbsA_mul_self (hQ : Qᵀ * Q = 1) (s : Fin N → ℝ) :
    sqrtAbsA Q s * sqrtAbsA Q s = absA Q s := by
  rw [sqrtAbsA, specFn_mul_self hQ, absA]
  congr 1
  funext k
  exact Real.mul_self_sqrt (abs_nonneg _)

/-- The angular matrix is symmetric (arXiv 2307.07538, Section 3). -/
theorem IsEigenDecomp.symm (d : IsEigenDecomp A Q s) : Aᵀ = A := by
  rw [d.eq, specFn_transpose]

/-- The eigenvalues of `A`, read off the quadratic form. -/
theorem IsEigenDecomp.eigenvalue (d : IsEigenDecomp A Q s) (k : Fin N) :
    s k = (fun m => Q m k) ⬝ᵥ (A *ᵥ fun m => Q m k) := by
  have h : Qᵀ * (A * Q) = Matrix.diagonal s := by
    rw [d.eq, specFn_mul_Q d.orth, ← Matrix.mul_assoc, d.orth, Matrix.one_mul]
  have h' := congrFun (congrFun h k) k
  rw [Matrix.diagonal_apply_eq] at h'
  rw [← h']
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec]

/-- The eigenvectors have unit length. -/
theorem IsEigenDecomp.column_norm (d : IsEigenDecomp A Q s) (k : Fin N) :
    (fun m => Q m k) ⬝ᵥ (fun m => Q m k) = 1 := by
  have h' := congrFun (congrFun d.orth k) k
  simpa [Matrix.mul_apply, dotProduct] using h'

/-- Every symmetric matrix has an eigendecomposition, so `IsEigenDecomp` is never vacuous. -/
theorem exists_isEigenDecomp (hA : Aᵀ = A) : ∃ Q s, IsEigenDecomp A Q s := by
  have hH : A.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hA]
  refine ⟨hH.eigenvectorUnitary, hH.eigenvalues, ?_, ?_⟩
  · have := Matrix.mem_unitaryGroup_iff'.1 hH.eigenvectorUnitary.2
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  · have := hH.spectral_theorem
    simpa [specFn, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp_def] using this

end Spectral

/-! ### The Legendre moment matrix `A = (⟨P_m, μ P_n⟩_μ)` and the bound `|σ_k| ≤ 1` -/

/-- The angular inner product `⟨f, g⟩_μ = w ∫_{-1}^{1} f g dμ`.  The weight `w > 0` is a parameter
so that both conventions, `w = 1/2` (for which `P₀ = 1`) and `w = 1`, are covered. -/
noncomputable def angularInner (w : ℝ) (f g : ℝ → ℝ) : ℝ := w * ∫ μ in (-1 : ℝ)..1, f μ * g μ

/-- Orthonormal continuous functions on `[-1, 1]`, such as the normalized Legendre polynomials. -/
structure IsOrthonormalFamily (w : ℝ) (P : Fin N → ℝ → ℝ) : Prop where
  pos : 0 < w
  cont : ∀ m, Continuous (P m)
  orthonormal : ∀ m k, angularInner w (P m) (P k) = if m = k then 1 else 0

/-- The matrix `A_{mn} = ⟨P_m, μ P_n⟩_μ`. -/
noncomputable def momentMatrix (w : ℝ) (P : Fin N → ℝ → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun m k => angularInner w (P m) (fun μ => μ * P k μ)

/-- `A_{mn} = ⟨P_m, μ P_n⟩_μ` is symmetric (arXiv 2307.07538, Section 3). -/
theorem momentMatrix_transpose (w : ℝ) (P : Fin N → ℝ → ℝ) :
    (momentMatrix w P)ᵀ = momentMatrix w P := by
  ext m k
  simp only [Matrix.transpose_apply, momentMatrix, Matrix.of_apply, angularInner]
  congr 1
  apply intervalIntegral.integral_congr
  intro μ _
  ring

/-- Exchanging a double sum and an integral of continuous functions. -/
private theorem integral_double_sum {g : Fin N → Fin N → ℝ → ℝ} (hg : ∀ m k, Continuous (g m k)) :
    ∫ μ in (-1 : ℝ)..1, ∑ m, ∑ k, g m k μ = ∑ m, ∑ k, ∫ μ in (-1 : ℝ)..1, g m k μ := by
  rw [intervalIntegral.integral_finsetSum fun m _ =>
    (continuous_finsetSum _ fun k _ => hg m k).intervalIntegrable _ _]
  exact Finset.sum_congr rfl fun m _ =>
    intervalIntegral.integral_finsetSum fun k _ => (hg m k).intervalIntegrable _ _

/-- The bound on the paper's matrix, as a quadratic form: `|x ⬝ A x| ≤ x ⬝ x`.  The paper uses
`|σ_k| ≤ 1` without proof. Since `A` is the compression of multiplication by `μ ∈ [-1, 1]`, it holds
for every orthonormal family. -/
theorem momentMatrix_quadratic_le {w : ℝ} {P : Fin N → ℝ → ℝ} (hP : IsOrthonormalFamily w P)
    (x : Fin N → ℝ) : |x ⬝ᵥ (momentMatrix w P *ᵥ x)| ≤ x ⬝ᵥ x := by
  set f : ℝ → ℝ := fun μ => ∑ m, x m * P m μ with hf
  have hfc : Continuous f := continuous_finsetSum _ fun m _ => continuous_const.mul (hP.cont m)
  have hsq : ∀ μ, f μ ^ 2 = ∑ m, ∑ k, (x m * P m μ) * (x k * P k μ) := by
    intro μ
    rw [sq, hf, Finset.sum_mul_sum]
  have h1 : x ⬝ᵥ (momentMatrix w P *ᵥ x) = w * ∫ μ in (-1 : ℝ)..1, μ * f μ ^ 2 := by
    have hc : ∀ m k, Continuous fun μ => x m * x k * (P m μ * (μ * P k μ)) := fun m k =>
      continuous_const.mul ((hP.cont m).mul (continuous_id.mul (hP.cont k)))
    have : ∀ μ, μ * f μ ^ 2 = ∑ m, ∑ k, x m * x k * (P m μ * (μ * P k μ)) := by
      intro μ
      rw [hsq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [this]
    rw [integral_double_sum hc]
    simp only [intervalIntegral.integral_const_mul, dotProduct, Matrix.mulVec, momentMatrix,
      Matrix.of_apply, angularInner, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => by ring
  have h2 : x ⬝ᵥ x = w * ∫ μ in (-1 : ℝ)..1, f μ ^ 2 := by
    have hc : ∀ m k, Continuous fun μ => (x m * P m μ) * (x k * P k μ) := fun m k =>
      (continuous_const.mul (hP.cont m)).mul (continuous_const.mul (hP.cont k))
    simp only [hsq]
    rw [integral_double_sum hc, Finset.mul_sum]
    have h3 : ∀ m k, ∫ μ in (-1 : ℝ)..1, (x m * P m μ) * (x k * P k μ)
        = x m * x k * ∫ μ in (-1 : ℝ)..1, P m μ * P k μ := by
      intro m k
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun μ _ => by ring
    have h4 : ∀ m k, w * (x m * x k * ∫ μ in (-1 : ℝ)..1, P m μ * P k μ)
        = x m * x k * (if m = k then 1 else 0) := by
      intro m k
      rw [← hP.orthonormal m k, angularInner]
      ring
    simp only [h3, Finset.mul_sum, h4, dotProduct, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
  have hi1 : IntervalIntegrable (fun μ => μ * f μ ^ 2) MeasureTheory.volume (-1) 1 :=
    (continuous_id.mul (hfc.pow 2)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun μ => f μ ^ 2) MeasureTheory.volume (-1) 1 :=
    (hfc.pow 2).intervalIntegrable _ _
  have hu : (∫ μ in (-1 : ℝ)..1, μ * f μ ^ 2) ≤ ∫ μ in (-1 : ℝ)..1, f μ ^ 2 :=
    intervalIntegral.integral_mono_on (by norm_num) hi1 hi2 fun μ hμ => by
      nlinarith [sq_nonneg (f μ), hμ.2]
  have hl : (∫ μ in (-1 : ℝ)..1, -f μ ^ 2) ≤ ∫ μ in (-1 : ℝ)..1, μ * f μ ^ 2 :=
    intervalIntegral.integral_mono_on (by norm_num) hi2.neg hi1 fun μ hμ => by
      nlinarith [sq_nonneg (f μ), hμ.1]
  rw [intervalIntegral.integral_neg] at hl
  rw [h1, h2, abs_le]
  have hw := hP.pos
  constructor <;> nlinarith

/-- `|σ_k| ≤ 1` for the eigenvalues of the moment matrix (used without proof in arXiv 2307.07538,
Lemma 2). -/
theorem IsEigenDecomp.abs_le_one {w : ℝ} {P : Fin N → ℝ → ℝ} {Q : Matrix (Fin N) (Fin N) ℝ}
    {s : Fin N → ℝ} (d : IsEigenDecomp (momentMatrix w P) Q s) (hP : IsOrthonormalFamily w P)
    (k : Fin N) : |s k| ≤ 1 := by
  have := momentMatrix_quadratic_le hP fun m => Q m k
  rwa [← d.eigenvalue, d.column_norm] at this

/-! ### Lemma 2 -/

/-- One column of Lemma 2.  The upwind structure `Dˣ ± Dˣˣ` turns the flux into a single forward or
backward difference, so no Fourier transform is needed. -/
private theorem sum_flux_sq {Δx : ℝ} (hΔx : Δx ≠ 0) (s : ℝ) (z : ZMod n → ℝ) :
    ∑ p, (-((z (p + 1) - z (p - 1)) / (2 * Δx)) * s
        - (z (p + 1) - 2 * z p + z (p - 1)) / (2 * Δx) * |s|) ^ 2
      = s ^ 2 / Δx ^ 2 * ∑ p, (z (p + 1) - z p) ^ 2 := by
  rcases le_or_gt 0 s with hs | hs
  · rw [abs_of_nonneg hs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    field_simp
    ring
  · have h := Equiv.sum_comp (Equiv.addRight (1 : ZMod n)) fun p => (z p - z (p - 1)) ^ 2
    simp only [Equiv.coe_addRight, add_sub_cancel_right] at h
    rw [abs_of_neg hs, h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    field_simp
    ring

section LemmaTwo

variable {A Q : Matrix (Fin N) (Fin N) ℝ} {s : Fin N → ℝ} {κ : Type*} [Fintype κ]

/-- The flux of Lemma 2, in the paper's index form `(Dˣ)ᵀ u A - (Dˣˣ)ᵀ u |A|`. -/
noncomputable def flux (Δx : ℝ) (A Aa : Matrix (Fin N) (Fin N) ℝ)
    (u : Matrix (ZMod n) (Fin N) ℝ) : Matrix (ZMod n) (Fin N) ℝ :=
  (Dx n Δx)ᵀ * u * A - (Dxx n Δx)ᵀ * u * Aa

/-- The squared flux in the eigenbasis of `A`: with `ũ = u Q` and the forward differences
`δ = ũ_{p+1,k} - ũ_{p,k}`, `‖flux‖² = ∑ σ_k² δ² / Δx²`. -/
theorem norm_flux_sq (d : IsEigenDecomp A Q s) {Δx : ℝ} (hΔx : Δx ≠ 0)
    (u : Matrix (ZMod n) (Fin N) ℝ) :
    ‖flux Δx A (absA Q s) u‖ ^ 2
      = ∑ k, ∑ p, s k ^ 2 / Δx ^ 2 * ((u * Q) (p + 1) k - (u * Q) p k) ^ 2 := by
  have hQ : ‖flux Δx A (absA Q s) u * Q‖ = ‖flux Δx A (absA Q s) u‖ := by
    have := Frobenius.norm_mul_transpose_of_orthonormal (V := Qᵀ)
      (by rw [Matrix.transpose_transpose]; exact d.orth') (flux Δx A (absA Q s) u)
    rwa [Matrix.transpose_transpose] at this
  have hM : flux Δx A (absA Q s) u * Q
      = -(Dx n Δx * (u * Q) * Matrix.diagonal s)
        - Dxx n Δx * (u * Q) * Matrix.diagonal fun k => |s k| := by
    have h1 : A * Q = Q * Matrix.diagonal s := by rw [d.eq, specFn_mul_Q d.orth]
    have h2 : absA Q s * Q = Q * Matrix.diagonal (fun k => |s k|) := specFn_mul_Q d.orth _
    rw [flux, Dx_transpose, Dxx_transpose, Matrix.sub_mul, Matrix.mul_assoc _ A,
      Matrix.mul_assoc _ (absA Q s), h1, h2, Matrix.neg_mul, Matrix.neg_mul]
    simp only [Matrix.mul_assoc]
  rw [← hQ, hM, Frobenius.norm_sq_eq_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := sum_flux_sq hΔx (s k) fun p => (u * Q) p k
  rw [Finset.mul_sum] at this
  rw [← this]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.mul_diagonal, Dx_mul_apply, Dxx_mul_apply]
  ring

/-- The dissipation in the eigenbasis of `A`: `‖D⁺ u |A|^{1/2}‖² = ∑ |σ_k| δ² / (2 Δx)`. -/
theorem norm_dissipation_sq (d : IsEigenDecomp A Q s) {Δx : ℝ} (hΔx : 0 < Δx)
    (u : Matrix (ZMod n) (Fin N) ℝ) :
    ‖Dplus n Δx * u * sqrtAbsA Q s‖ ^ 2
      = ∑ k, ∑ p, |s k| / (2 * Δx) * ((u * Q) (p + 1) k - (u * Q) p k) ^ 2 := by
  have hQ : ‖Dplus n Δx * u * sqrtAbsA Q s * Q‖ = ‖Dplus n Δx * u * sqrtAbsA Q s‖ := by
    have := Frobenius.norm_mul_transpose_of_orthonormal (V := Qᵀ)
      (by rw [Matrix.transpose_transpose]; exact d.orth') (Dplus n Δx * u * sqrtAbsA Q s)
    rwa [Matrix.transpose_transpose] at this
  have hM : Dplus n Δx * u * sqrtAbsA Q s * Q
      = Dplus n Δx * (u * Q) * Matrix.diagonal fun k => √|s k| := by
    rw [Matrix.mul_assoc _ _ Q, show sqrtAbsA Q s * Q = _ from specFn_mul_Q d.orth _]
    simp only [Matrix.mul_assoc]
  rw [← hQ, hM, Frobenius.norm_sq_eq_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.mul_diagonal, Dplus_mul_apply, mul_pow, div_pow, Real.sq_sqrt (abs_nonneg _),
    Real.sq_sqrt (by positivity)]
  ring

/-- **Lemma 2 with the exact value** (arXiv 2307.07538, Lemma 2 and the last display of its proof).
For an eigendecomposition `A = Q diag(σ) Qᵀ` and `ũ = u Q`,

  `(Δt/2) ‖(Dˣ)ᵀ u A - (Dˣˣ)ᵀ u |A|‖² - ‖D⁺ u |A|^{1/2}‖²
     = ∑ₖ ∑ₚ |σ_k| / (2 Δx) * (Δt |σ_k| / Δx - 1) * (ũ_{p+1,k} - ũ_{p,k})²`.

The paper gets this by discrete Fourier transform. We use `Dˣ ± Dˣˣ`, a single upwind difference. -/
theorem lemma2_eq (d : IsEigenDecomp A Q s) {Δx : ℝ} (hΔx : 0 < Δx) (Δt : ℝ)
    (u : Matrix (ZMod n) (Fin N) ℝ) :
    Δt / 2 * ‖flux Δx A (absA Q s) u‖ ^ 2 - ‖Dplus n Δx * u * sqrtAbsA Q s‖ ^ 2
      = ∑ k, ∑ p, |s k| / (2 * Δx) * (Δt * |s k| / Δx - 1)
          * ((u * Q) (p + 1) k - (u * Q) p k) ^ 2 := by
  rw [norm_flux_sq d hΔx.ne', norm_dissipation_sq d hΔx, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hs : s k ^ 2 = |s k| * |s k| := by rw [← sq, sq_abs]
  rw [hs]
  field_simp

/-- **Lemma 2** (arXiv 2307.07538) in its sharp form, as derived in the paper's proof: if
`Δt |σ_k| ≤ Δx` for all `k`, then `(Δt/2) ‖(Dˣ)ᵀ u A - (Dˣˣ)ᵀ u |A|‖² ≤ ‖D⁺ u |A|^{1/2}‖²`. -/
theorem lemma2_sharp (d : IsEigenDecomp A Q s) {Δx Δt : ℝ} (hΔx : 0 < Δx)
    (hcfl : ∀ k, Δt * |s k| ≤ Δx) (u : Matrix (ZMod n) (Fin N) ℝ) :
    Δt / 2 * ‖flux Δx A (absA Q s) u‖ ^ 2 - ‖Dplus n Δx * u * sqrtAbsA Q s‖ ^ 2 ≤ 0 := by
  rw [lemma2_eq d hΔx]
  refine Finset.sum_nonpos fun k _ => Finset.sum_nonpos fun p _ => ?_
  have h1 : Δt * |s k| / Δx - 1 ≤ 0 := by
    rw [sub_nonpos, div_le_one hΔx]
    exact hcfl k
  have h2 : 0 ≤ |s k| / (2 * Δx) := by positivity
  exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos h2 h1) (sq_nonneg _)

/-- **Lemma 2** (arXiv 2307.07538) for the paper's matrix: if `A_{mn} = ⟨P_m, μ P_n⟩_μ` for an
orthonormal family (e.g. normalized Legendre polynomials) and `Δt ≤ Δx`, then
`(Δt/2) ‖(Dˣ)ᵀ u A - (Dˣˣ)ᵀ u |A|‖² - ‖D⁺ u |A|^{1/2}‖² ≤ 0`.  The bound `|σ_k| ≤ 1`, which the
paper asserts, is proved in `IsEigenDecomp.abs_le_one`.  The flux is the one printed in the paper,
with the transposed stencils; `lemma2'` is the variant with `Dˣ`, `Dˣˣ` themselves. -/
theorem lemma2 {w : ℝ} {P : Fin N → ℝ → ℝ} (hP : IsOrthonormalFamily w P)
    (d : IsEigenDecomp (momentMatrix w P) Q s) {Δx Δt : ℝ} (hΔx : 0 < Δx) (hΔt : 0 ≤ Δt)
    (hcfl : Δt ≤ Δx) (u : Matrix (ZMod n) (Fin N) ℝ) :
    Δt / 2 * ‖flux Δx (momentMatrix w P) (absA Q s) u‖ ^ 2
      - ‖Dplus n Δx * u * sqrtAbsA Q s‖ ^ 2 ≤ 0 :=
  lemma2_sharp d hΔx (fun k => by
    nlinarith [d.abs_le_one hP k, abs_nonneg (s k)]) u

/-- The variant of `lemma2_sharp` with `Dˣ u A - Dˣˣ u |A|` in place of the printed
`(Dˣ)ᵀ u A - (Dˣˣ)ᵀ u |A|`.  It follows by applying `lemma2_sharp` to `-A`. -/
theorem lemma2_sharp' (d : IsEigenDecomp A Q s) {Δx Δt : ℝ} (hΔx : 0 < Δx)
    (hcfl : ∀ k, Δt * |s k| ≤ Δx) (u : Matrix (ZMod n) (Fin N) ℝ) :
    Δt / 2 * ‖Dx n Δx * u * A - Dxx n Δx * u * absA Q s‖ ^ 2
      - ‖Dplus n Δx * u * sqrtAbsA Q s‖ ^ 2 ≤ 0 := by
  have d' : IsEigenDecomp (-A) Q (fun k => -s k) := ⟨d.orth, by
    rw [d.eq, specFn, specFn, ← Matrix.diagonal_neg, Matrix.mul_neg, Matrix.neg_mul]⟩
  have hab : absA Q (fun k => -s k) = absA Q s := by simp [absA]
  have hsq : sqrtAbsA Q (fun k => -s k) = sqrtAbsA Q s := by simp [sqrtAbsA]
  have := lemma2_sharp d' hΔx (by simpa using hcfl) u
  rw [hab, hsq, flux, Dx_transpose, Dxx_transpose] at this
  have e : -Dx n Δx * u * -A - Dxx n Δx * u * absA Q s
      = Dx n Δx * u * A - Dxx n Δx * u * absA Q s := by
    simp [Matrix.neg_mul, Matrix.mul_neg]
  rwa [e] at this

/-- `lemma2_sharp'` for the paper's matrix under `Δt ≤ Δx`. -/
theorem lemma2' {w : ℝ} {P : Fin N → ℝ → ℝ} (hP : IsOrthonormalFamily w P)
    (d : IsEigenDecomp (momentMatrix w P) Q s) {Δx Δt : ℝ} (hΔx : 0 < Δx) (hΔt : 0 ≤ Δt)
    (hcfl : Δt ≤ Δx) (u : Matrix (ZMod n) (Fin N) ℝ) :
    Δt / 2 * ‖Dx n Δx * u * momentMatrix w P - Dxx n Δx * u * absA Q s‖ ^ 2
      - ‖Dplus n Δx * u * sqrtAbsA Q s‖ ^ 2 ≤ 0 :=
  lemma2_sharp' d hΔx (fun k => by
    nlinarith [d.abs_le_one hP k, abs_nonneg (s k)]) u

end LemmaTwo

/-! ### The zeroth moment -/

section Zeroth

variable [NeZero N]

/-- The projector `e₀ e₀ᵀ` onto the zeroth moment. -/
noncomputable def E0 (N : ℕ) [NeZero N] : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal fun m => if m = 0 then 1 else 0

/-- The matrix `B e₀ᵀ`, whose zeroth column is `B` and whose other columns vanish. -/
noncomputable def zeroCol (N : ℕ) [NeZero N] (B : ZMod n → ℝ) : Matrix (ZMod n) (Fin N) ℝ :=
  Matrix.of fun p m => if m = 0 then B p else 0

/-- `e₀ e₀ᵀ` is symmetric. -/
theorem E0_transpose : (E0 N)ᵀ = E0 N := Matrix.diagonal_transpose _

/-- `e₀ e₀ᵀ` is idempotent. -/
theorem E0_mul_E0 : E0 N * E0 N = E0 N := by
  rw [E0, Matrix.diagonal_mul_diagonal]
  congr 1
  funext m
  split_ifs <;> simp

/-- Right multiplication by `e₀ e₀ᵀ` keeps the zeroth column. -/
theorem mul_E0_apply {κ : Type*} (M : Matrix κ (Fin N) ℝ) (p : κ) (m : Fin N) :
    (M * E0 N) p m = if m = 0 then M p 0 else 0 := by
  rw [E0, Matrix.mul_diagonal]
  split_ifs with h
  · rw [h, mul_one]
  · rw [mul_zero]

/-- Right multiplication by `1 - e₀ e₀ᵀ` removes the zeroth column. -/
theorem mul_sub_E0_apply {κ : Type*} (M : Matrix κ (Fin N) ℝ) (p : κ) (m : Fin N) :
    (M * (1 - E0 N) : Matrix κ (Fin N) ℝ) p m = if m = 0 then 0 else M p m := by
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply, mul_E0_apply]
  split_ifs with h
  · rw [h, sub_self]
  · rw [sub_zero]

omit [NeZero n] in
/-- `B e₀ᵀ` is fixed by `e₀ e₀ᵀ`. -/
theorem zeroCol_mul_E0 (B : ZMod n → ℝ) :
    zeroCol N B * E0 N = zeroCol N B := by
  ext p m
  rw [mul_E0_apply]
  simp only [zeroCol, Matrix.of_apply, ite_true]

/-- Testing with `B e₀ᵀ` sees only the zeroth column. -/
theorem inner_zeroCol (M : Matrix (ZMod n) (Fin N) ℝ) (B : ZMod n → ℝ) :
    ⟪M, zeroCol N B⟫ = ∑ p, M p 0 * B p := by
  rw [Frobenius.inner_def]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [zeroCol, Matrix.of_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

/-- The zeroth column splits off the Frobenius norm. -/
theorem norm_sq_split (M : Matrix (ZMod n) (Fin N) ℝ) :
    ‖M‖ ^ 2 = ‖M * (1 - E0 N)‖ ^ 2 + ∑ p, M p 0 ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum, Frobenius.norm_sq_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h : ∀ m, M p m ^ 2
      = (M * (1 - E0 N) : Matrix (ZMod n) (Fin N) ℝ) p m ^ 2 + if m = 0 then M p 0 ^ 2 else 0 := by
    intro m
    rw [mul_sub_E0_apply]
    split_ifs with hm
    · rw [hm]; ring
    · ring
  rw [Finset.sum_congr rfl fun m _ => h m, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]

/-- The non-zeroth moments, in the form printed in Theorem 1 of the paper. -/
theorem norm_sub_E0_sq (M : Matrix (ZMod n) (Fin N) ℝ) :
    ‖M * (1 - E0 N)‖ ^ 2 = ∑ p, ∑ m ∈ Finset.univ.erase 0, M p m ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin N)), mul_sub_E0_apply]
  simp only [ite_true, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [mul_sub_E0_apply]
  simp [Finset.ne_of_mem_erase hm]

end Zeroth

/-! ### Transport -/

section Transport

variable {A Q : Matrix (Fin N) (Fin N) ℝ} {s : Fin N → ℝ}

/-- The transport operator `G u = -Dˣ u A + Dˣˣ u |A|`. -/
noncomputable def transport (Δx : ℝ) (A Aa : Matrix (Fin N) (Fin N) ℝ)
    (u : Matrix (ZMod n) (Fin N) ℝ) : Matrix (ZMod n) (Fin N) ℝ :=
  -(Dx n Δx * u * A) + Dxx n Δx * u * Aa

/-- Testing the transport operator with `u`: advection drops out and the stabilization gives
`⟪G u, u⟫ = -‖D⁺ u |A|^{1/2}‖²`.  This is steps 2-4 of the proof of Theorem 1 of the paper. -/
theorem inner_transport_self (d : IsEigenDecomp A Q s) {Δx : ℝ} (hΔx : 0 < Δx)
    (u : Matrix (ZMod n) (Fin N) ℝ) :
    ⟪transport Δx A (absA Q s) u, u⟫ = -‖Dplus n Δx * u * sqrtAbsA Q s‖ ^ 2 := by
  have h1 : ⟪Dx n Δx * u * A, u⟫ = 0 := by
    have e : ⟪Dx n Δx * u * A, u⟫ = -⟪Dx n Δx * u * A, u⟫ := by
      calc ⟪Dx n Δx * u * A, u⟫ = ⟪Dx n Δx * u, u * Aᵀ⟫ := Frobenius.inner_mul_right _ _ _
        _ = ⟪u, (Dx n Δx)ᵀ * (u * Aᵀ)⟫ := Frobenius.inner_mul_left _ _ _
        _ = -⟪u, Dx n Δx * (u * A)⟫ := by
            rw [Dx_transpose, d.symm, Matrix.neg_mul, inner_neg_right]
        _ = -⟪Dx n Δx * u * A, u⟫ := by
            rw [Matrix.mul_assoc, real_inner_comm]
    linarith
  have hR : (sqrtAbsA Q s)ᵀ = sqrtAbsA Q s := specFn_transpose _ _
  have h2 : ⟪Dxx n Δx * u * absA Q s, u⟫ = -‖Dplus n Δx * u * sqrtAbsA Q s‖ ^ 2 := by
    set R := sqrtAbsA Q s with hRdef
    set W := Dplus n Δx * u * R with hW
    have e : Dxx n Δx * u * absA Q s = -((Dplus n Δx)ᵀ * W * R) := by
      rw [← sqrtAbsA_mul_self d.orth s, Dxx_eq hΔx, ← hRdef, hW]
      simp only [Matrix.neg_mul, Matrix.mul_assoc]
    rw [e, inner_neg_left, Frobenius.inner_mul_right, Frobenius.inner_mul_left,
      Matrix.transpose_transpose, hR, ← Matrix.mul_assoc, ← hW, real_inner_self_eq_norm_sq]
  rw [transport, inner_add_left, inner_neg_left, h1, h2]
  ring

/-- `G` is linear; we need the additivity of its action on a difference. -/
theorem transport_sub (Δx : ℝ) (A Aa : Matrix (Fin N) (Fin N) ℝ)
    (u v : Matrix (ZMod n) (Fin N) ℝ) :
    transport Δx A Aa (u - v) = transport Δx A Aa u - transport Δx A Aa v := by
  simp only [transport, Matrix.mul_sub, Matrix.sub_mul]
  abel

/-- The adjoint of `G` is minus the flux of Lemma 2, which is why the paper's Lemma 2 has transposed
stencils. -/
theorem inner_transport_adjoint (d : IsEigenDecomp A Q s) (Δx : ℝ)
    (z w : Matrix (ZMod n) (Fin N) ℝ) :
    ⟪transport Δx A (absA Q s) z, w⟫ = -⟪z, flux Δx A (absA Q s) w⟫ := by
  have hAa : (absA Q s)ᵀ = absA Q s := specFn_transpose _ _
  have h1 : ⟪Dx n Δx * z * A, w⟫ = ⟪z, (Dx n Δx)ᵀ * w * A⟫ := by
    rw [Frobenius.inner_mul_right, Frobenius.inner_mul_left, d.symm, Matrix.mul_assoc]
  have h2 : ⟪Dxx n Δx * z * absA Q s, w⟫ = ⟪z, (Dxx n Δx)ᵀ * w * absA Q s⟫ := by
    rw [Frobenius.inner_mul_right, Frobenius.inner_mul_left, hAa, Matrix.mul_assoc]
  rw [transport, flux, inner_add_left, inner_neg_left, h1, h2, inner_sub_right]
  ring

end Transport

/-! ### Theorem 1: the semi-discrete energy law -/

section ThmOne

variable [NeZero N] {A Q : Matrix (Fin N) (Fin N) ℝ} {s : Fin N → ℝ}
  {r r' : Type*} [Fintype r] [Fintype r']

/-- The right-hand side of the augmented S-step (9c) of the paper,
`Ṡ = -X̂ᵀ Dˣ X̂ S V̂ᵀ A V̂ + X̂ᵀ Dˣˣ X̂ S V̂ᵀ |A| V̂ + σ (X̂ᵀ B e₀ᵀ V̂ - S)`. -/
noncomputable def sStepField (Δx σ : ℝ) (A Aa : Matrix (Fin N) (Fin N) ℝ)
    (X : Matrix (ZMod n) r ℝ) (V : Matrix (Fin N) r' ℝ) (S : Matrix r r' ℝ) (B : ZMod n → ℝ) :
    Matrix r r' ℝ :=
  -(Xᵀ * Dx n Δx * X * S * Vᵀ * A * V) + Xᵀ * Dxx n Δx * X * S * Vᵀ * Aa * V
    + σ • (Xᵀ * zeroCol N B * V - S)

/-- The S-step field (9c) of arXiv 2307.07538 is a Galerkin projection of the full field. -/
theorem sStepField_eq (Δx σ : ℝ) (A Aa : Matrix (Fin N) (Fin N) ℝ)
    (X : Matrix (ZMod n) r ℝ) (V : Matrix (Fin N) r' ℝ) (S : Matrix r r' ℝ) (B : ZMod n → ℝ) :
    sStepField Δx σ A Aa X V S B
      = Xᵀ * (transport Δx A Aa (X * S * Vᵀ) + σ • zeroCol N B) * V - σ • S := by
  simp only [sStepField, transport, Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, smul_sub]
  abel

/-- **Theorem 1** (arXiv 2307.07538, semi-discrete energy law).  Let `X̂`, `V̂` have orthonormal
columns and let `(S, B)` solve the augmented S-step (9c) coupled to the internal energy (9d).  Then
`u = X̂ S V̂ᵀ` and `E = ½ ‖u‖² + ½ ‖B‖²` satisfy the paper's identity

  `dE/dt = -‖D⁺ u |A|^{1/2}‖² - σ (∑ₚ (u_{p0} - B_p)² + ∑ₚ ∑_{m ≠ 0} u_{pm}²)`.

This is the actual Su–Olson operator with periodic stencils, not an abstract dissipative field. -/
theorem hasDerivAt_energy [DecidableEq r] [DecidableEq r'] (d : IsEigenDecomp A Q s) {Δx σ : ℝ}
    (hΔx : 0 < Δx)
    {X : Matrix (ZMod n) r ℝ} {V : Matrix (Fin N) r' ℝ} (hX : Xᵀ * X = 1) (hV : Vᵀ * V = 1)
    {S : ℝ → Matrix r r' ℝ} {B : ℝ → ZMod n → ℝ} {t : ℝ}
    (hS : HasDerivAt S (sStepField Δx σ A (absA Q s) X V (S t) (B t)) t)
    (hB : ∀ p, HasDerivAt (fun τ => B τ p) (σ * ((X * S t * Vᵀ) p 0 - B t p)) t) :
    HasDerivAt (fun τ => (1 / 2 : ℝ) * ‖X * S τ * Vᵀ‖ ^ 2 + (1 / 2 : ℝ) * ∑ p, B τ p ^ 2)
      (-‖Dplus n Δx * (X * S t * Vᵀ) * sqrtAbsA Q s‖ ^ 2
        - σ * (∑ p, ((X * S t * Vᵀ) p 0 - B t p) ^ 2
          + ∑ p, ∑ m ∈ Finset.univ.erase 0, (X * S t * Vᵀ) p m ^ 2)) t := by
  have hiso : ∀ T : Matrix r r' ℝ, ‖X * T * Vᵀ‖ = ‖T‖ := fun T => by
    rw [Matrix.mul_assoc, Frobenius.norm_mul_of_orthonormal hX,
      Frobenius.norm_mul_transpose_of_orthonormal hV]
  set u := X * S t * Vᵀ with hu
  have h1 : HasDerivAt (fun τ => (1 / 2 : ℝ) * ‖X * S τ * Vᵀ‖ ^ 2)
      ((1 / 2 : ℝ) * (2 * ⟪S t, sStepField Δx σ A (absA Q s) X V (S t) (B t)⟫)) t := by
    simp only [hiso]
    exact hS.norm_sq.const_mul _
  have h2 : HasDerivAt (fun τ => (1 / 2 : ℝ) * ∑ p, B τ p ^ 2)
      ((1 / 2 : ℝ) * ∑ p, 2 * B t p * (σ * (u p 0 - B t p))) t := by
    refine HasDerivAt.const_mul _ ?_
    have := HasDerivAt.fun_sum (u := Finset.univ) fun p _ => (hB p).pow 2
    simpa using this
  have hin : ⟪S t, sStepField Δx σ A (absA Q s) X V (S t) (B t)⟫
      = -‖Dplus n Δx * u * sqrtAbsA Q s‖ ^ 2 + σ * ∑ p, u p 0 * B t p - σ * ‖u‖ ^ 2 := by
    rw [sStepField_eq, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
      Frobenius.inner_mul_right', Frobenius.inner_mul_left', Matrix.transpose_transpose,
      ← Matrix.mul_assoc, ← hu, inner_add_right, inner_smul_right, inner_zeroCol,
      real_inner_comm, inner_transport_self d hΔx, ← hiso (S t), ← hu]
  refine (h1.add h2).congr_deriv ?_
  rw [hin, norm_sq_split u, norm_sub_E0_sq, Finset.mul_sum (a := (1 / 2 : ℝ))]
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_add, mul_sub,
    Finset.mul_sum]
  have e1 : ∀ p, (1 / 2 : ℝ) * (2 * B t p * (σ * u p 0)) = σ * (B t p * u p 0) := fun p => by ring
  have e2 : ∀ p, (1 / 2 : ℝ) * (2 * B t p * (σ * B t p)) = σ * B t p ^ 2 := fun p => by ring
  have e3 : ∀ p, σ * (2 * u p 0 * B t p) = 2 * (σ * (B t p * u p 0)) := fun p => by ring
  have e4 : ∑ p, u p 0 * B t p = ∑ p, B t p * u p 0 :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  simp only [e1, e2, e3, ← Finset.mul_sum]
  rw [e4]
  ring

/-- **Theorem 1** (arXiv 2307.07538): the right-hand side of the energy law is `≤ 0` for `σ ≥ 0`,
which the paper does not state as a hypothesis.  Its proof calls the right-hand side "strictly
negative", but only `≤ 0` holds, see `energy_rate_eq_zero_at_equilibrium`. -/
theorem energy_rate_nonpos {u : Matrix (ZMod n) (Fin N) ℝ} {B : ZMod n → ℝ} {σ : ℝ} (hσ : 0 ≤ σ)
    (D : ℝ) (hD : 0 ≤ D) :
    -D - σ * (∑ p, (u p 0 - B p) ^ 2 + ∑ p, ∑ m ∈ Finset.univ.erase 0, u p m ^ 2) ≤ 0 := by
  have h1 : 0 ≤ ∑ p, (u p 0 - B p) ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
  have h2 : 0 ≤ ∑ p, ∑ m ∈ Finset.univ.erase 0, u p m ^ 2 :=
    Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun m _ => sq_nonneg _
  have := mul_nonneg hσ (add_nonneg h1 h2)
  linarith

/-- The "strictly negative" of the proof of Theorem 1 of arXiv 2307.07538 is false: at the
equilibrium `u = c e₀ᵀ`, `B = c` with `c` constant in space, the right-hand side of the energy law
vanishes. -/
theorem energy_rate_eq_zero_at_equilibrium (Δx σ c : ℝ) (R : Matrix (Fin N) (Fin N) ℝ) :
    -‖Dplus n Δx * zeroCol N (fun _ : ZMod n => c) * R‖ ^ 2
      - σ * (∑ p : ZMod n, ((zeroCol N (fun _ => c) : Matrix (ZMod n) (Fin N) ℝ) p 0 - c) ^ 2
        + ∑ p : ZMod n, ∑ m ∈ Finset.univ.erase 0,
            (zeroCol N (fun _ => c) : Matrix (ZMod n) (Fin N) ℝ) p m ^ 2) = 0 := by
  have h : Dplus n Δx * (zeroCol N fun _ : ZMod n => c) = 0 := by
    ext p m
    rw [Dplus_mul_apply]
    simp [zeroCol]
  have h1 : ∀ p : ZMod n, (zeroCol N (fun _ => c) : Matrix (ZMod n) (Fin N) ℝ) p 0 = c :=
    fun p => by simp [zeroCol]
  have h2 : ∀ (p : ZMod n), ∀ m ∈ Finset.univ.erase (0 : Fin N),
      (zeroCol N (fun _ => c) : Matrix (ZMod n) (Fin N) ℝ) p m ^ 2 = 0 := fun p m hm => by
    simp [zeroCol, Finset.ne_of_mem_erase hm]
  rw [h, Matrix.zero_mul, norm_zero]
  simp only [h1, sub_self, Finset.sum_congr rfl fun p _ => Finset.sum_eq_zero (h2 p)]
  simp

/-- **Theorem 1** (arXiv 2307.07538): along a solution of the augmented S-step (9c) coupled to the
internal energy (9d), `E = ½ ‖u‖² + ½ ‖B‖²` is nonincreasing, for `σ ≥ 0`. -/
theorem energy_antitone [DecidableEq r] [DecidableEq r'] (d : IsEigenDecomp A Q s) {Δx σ : ℝ}
    (hΔx : 0 < Δx) (hσ : 0 ≤ σ) {X : Matrix (ZMod n) r ℝ} {V : Matrix (Fin N) r' ℝ}
    (hX : Xᵀ * X = 1) (hV : Vᵀ * V = 1) {S : ℝ → Matrix r r' ℝ} {B : ℝ → ZMod n → ℝ}
    (hS : ∀ t, HasDerivAt S (sStepField Δx σ A (absA Q s) X V (S t) (B t)) t)
    (hB : ∀ t p, HasDerivAt (fun τ => B τ p) (σ * ((X * S t * Vᵀ) p 0 - B t p)) t) :
    Antitone fun τ => (1 / 2 : ℝ) * ‖X * S τ * Vᵀ‖ ^ 2 + (1 / 2 : ℝ) * ∑ p, B τ p ^ 2 := by
  have h := fun t => hasDerivAt_energy d hΔx hX hV (hS t) (hB t)
  refine antitone_of_deriv_nonpos (fun t => (h t).differentiableAt) fun t => ?_
  rw [(h t).deriv]
  exact energy_rate_nonpos hσ _ (sq_nonneg _)

end ThmOne

/-! ### Scheme (16) -/

section Scheme

variable [NeZero N] {r r' a a' c b b' ρ t t' : Type*}
  [Fintype r] [Fintype r'] [Fintype a] [Fintype a'] [Fintype c] [Fintype b] [Fintype b']
  [Fintype ρ] [Fintype t] [Fintype t']
  [DecidableEq a] [DecidableEq a'] [DecidableEq c] [DecidableEq b] [DecidableEq b']
  [DecidableEq ρ] [DecidableEq t] [DecidableEq t']

/-- The explicit K-step (16a): `K★ = K⁰ - Δt Dˣ K⁰ V⁰ᵀ A V⁰ + Δt Dˣˣ K⁰ V⁰ᵀ |A| V⁰`. -/
noncomputable def kStar (Δx Δt : ℝ) (A Aa : Matrix (Fin N) (Fin N) ℝ)
    (X₀ : Matrix (ZMod n) r ℝ) (S₀ : Matrix r r' ℝ) (V₀ : Matrix (Fin N) r' ℝ) :
    Matrix (ZMod n) r' ℝ :=
  X₀ * S₀ - Δt • (Dx n Δx * (X₀ * S₀) * V₀ᵀ * A * V₀)
    + Δt • (Dxx n Δx * (X₀ * S₀) * V₀ᵀ * Aa * V₀)

/-- The explicit L-step (16b):
`L★ = L⁰ - Δt A L⁰ (X⁰ᵀ Dˣ X⁰)ᵀ + Δt |A| L⁰ (X⁰ᵀ Dˣˣ X⁰)ᵀ`. -/
noncomputable def lStar (Δx Δt : ℝ) (A Aa : Matrix (Fin N) (Fin N) ℝ)
    (X₀ : Matrix (ZMod n) r ℝ) (S₀ : Matrix r r' ℝ) (V₀ : Matrix (Fin N) r' ℝ) :
    Matrix (Fin N) r ℝ :=
  V₀ * S₀ᵀ - Δt • (A * (V₀ * S₀ᵀ) * (X₀ᵀ * Dx n Δx * X₀)ᵀ)
    + Δt • (Aa * (V₀ * S₀ᵀ) * (X₀ᵀ * Dxx n Δx * X₀)ᵀ)

/-- The projected initial value `S̃⁰ = X★ᵀ X⁰ S⁰ V⁰ᵀ V★` of the S-step. -/
noncomputable def sTilde (X₀ : Matrix (ZMod n) r ℝ) (S₀ : Matrix r r' ℝ)
    (V₀ : Matrix (Fin N) r' ℝ) (Xs : Matrix (ZMod n) a ℝ) (Vs : Matrix (Fin N) a' ℝ) :
    Matrix a a' ℝ :=
  Xsᵀ * X₀ * S₀ * V₀ᵀ * Vs

/-- The explicit Galerkin S-step (16c). -/
noncomputable def sStar (Δx Δt : ℝ) (A Aa : Matrix (Fin N) (Fin N) ℝ)
    (Xs : Matrix (ZMod n) a ℝ) (Vs : Matrix (Fin N) a' ℝ) (St : Matrix a a' ℝ) : Matrix a a' ℝ :=
  St - Δt • (Xsᵀ * Dx n Δx * Xs * St * Vsᵀ * A * Vs)
    + Δt • (Xsᵀ * Dxx n Δx * Xs * St * Vsᵀ * Aa * Vs)

/-- The explicit part `R` of (16d): the zeroth moment of the *full* transport update, without the
Galerkin projection. -/
noncomputable def rhsR (Δx Δt : ℝ) (A Aa : Matrix (Fin N) (Fin N) ℝ)
    (X₀ : Matrix (ZMod n) r ℝ) (S₀ : Matrix r r' ℝ) (V₀ : Matrix (Fin N) r' ℝ)
    (Xs : Matrix (ZMod n) a ℝ) (Vs : Matrix (Fin N) a' ℝ) (St : Matrix a a' ℝ) (j : ZMod n) : ℝ :=
  (X₀ * S₀ * V₀ᵀ) j 0 - Δt * (Dx n Δx * Xs * St * Vsᵀ * A) j 0
    + Δt * (Dxx n Δx * Xs * St * Vsᵀ * Aa) j 0

/-- The opacity correction (16f): the non-zeroth moments of `L` are divided by `1 + Δt σ`.  See the
module docstring for the index printed in (16f). -/
noncomputable def scatL {κ : Type*} (σ Δt : ℝ) (L : Matrix (Fin N) κ ℝ) : Matrix (Fin N) κ ℝ :=
  Matrix.of fun m k => if m = 0 then L m k else L m k / (1 + Δt * σ)

/-- **One step of scheme (16)** of arXiv 2307.07538, up to the truncation.  The fields are, in
order, the augmented bases of (16a), (16b); the S-step (16c); the coupled solve (16d), (16e); the
opacity correction (16f); the augmentation (16g); and the update (16h).

A QR factorization `X★ R = [K★, X⁰]` is recorded through what it gives: `X★` has orthonormal
columns and its range contains `K★` and `X⁰`. -/
structure IsCoupledStep (Δx Δt σ : ℝ) (A Aa : Matrix (Fin N) (Fin N) ℝ)
    (X₀ : Matrix (ZMod n) r ℝ) (S₀ : Matrix r r' ℝ) (V₀ : Matrix (Fin N) r' ℝ) (B₀ : ZMod n → ℝ)
    (Xs : Matrix (ZMod n) a ℝ) (Vs : Matrix (Fin N) a' ℝ) (Ss : Matrix a a' ℝ)
    (uh B₁ : ZMod n → ℝ) (Vc : Matrix (Fin N) c ℝ) (Sc : Matrix a c ℝ)
    (Xt : Matrix (ZMod n) b ℝ) (Vt : Matrix (Fin N) b' ℝ) (St : Matrix b b' ℝ) : Prop where
  Xs_orth : Xsᵀ * Xs = 1
  Vs_orth : Vsᵀ * Vs = 1
  Xs_K : Xs * Xsᵀ * kStar Δx Δt A Aa X₀ S₀ V₀ = kStar Δx Δt A Aa X₀ S₀ V₀
  Xs_X₀ : Xs * Xsᵀ * X₀ = X₀
  Vs_L : Vs * Vsᵀ * lStar Δx Δt A Aa X₀ S₀ V₀ = lStar Δx Δt A Aa X₀ S₀ V₀
  Vs_V₀ : Vs * Vsᵀ * V₀ = V₀
  Ss_eq : Ss = sStar Δx Δt A Aa Xs Vs (sTilde X₀ S₀ V₀ Xs Vs)
  uh_eq : ∀ j, uh j = rhsR Δx Δt A Aa X₀ S₀ V₀ Xs Vs (sTilde X₀ S₀ V₀ Xs Vs) j
    + σ * Δt * (B₁ j - uh j)
  B₁_eq : ∀ j, B₁ j = B₀ j + σ * Δt * (uh j - B₁ j)
  Vc_orth : Vcᵀ * Vc = 1
  scat_eq : Vc * Scᵀ = scatL σ Δt (Vs * Ssᵀ)
  Xt_orth : Xtᵀ * Xt = 1
  Vt_orth : Vtᵀ * Vt = 1
  Xt_uh : (Xt * Xtᵀ) *ᵥ uh = uh
  Xt_Xs : Xt * Xtᵀ * Xs = Xs
  Vt_e₀ : Vt * Vtᵀ * E0 N = E0 N
  Vt_Vc : Vt * Vtᵀ * Vc = Vc
  St_eq : St = Xtᵀ * Xs * Sc * Vcᵀ * (1 - E0 N) * Vt + Xtᵀ * zeroCol N uh * Vt

/-- **The conservative truncation** of Section 6 of arXiv 2307.07538: `X¹ S¹ V¹ᵀ` keeps the zeroth
moment of `Y` exactly and replaces the remainder `Y (1 - e₀ e₀ᵀ)` by `U Uᵀ Y (1 - e₀ e₀ᵀ)`, for an
orthonormal `U`.  Taking for `U` the leading left singular vectors `X^rem` of the remainder gives
the paper's truncation, by `svd_truncation_eq_left_proj`.  Section 6 builds `V̂ = [e₁, V^rem]` and
`V̂ = V¹ R²`, which is recorded in `V₁_e₀`: the new angular basis contains `e₀`. -/
structure IsConservativeTruncation (U : Matrix (ZMod n) ρ ℝ) (Y : Matrix (ZMod n) (Fin N) ℝ)
    (X₁ : Matrix (ZMod n) t ℝ) (S₁ : Matrix t t' ℝ) (V₁ : Matrix (Fin N) t' ℝ) : Prop where
  U_orth : Uᵀ * U = 1
  X₁_orth : X₁ᵀ * X₁ = 1
  V₁_orth : V₁ᵀ * V₁ = 1
  eq : X₁ * S₁ * V₁ᵀ = Y * E0 N + U * Uᵀ * (Y * (1 - E0 N))
  V₁_e₀ : V₁ * V₁ᵀ * E0 N = E0 N

omit [DecidableEq ρ] in
/-- The truncated SVD is a left projection: if `Z = U₁ D₁ + U₂ D₂` (with `D₁ = Σ₁ W₁ᵀ`,
`D₂ = Σ₂ W₂ᵀ`), `U₁ᵀ U₁ = 1` and
`U₁ᵀ U₂ = 0`, then the kept part is `U₁ D₁ = U₁ U₁ᵀ Z`.  So `IsConservativeTruncation` covers
step 4 of the paper's truncation for every threshold. -/
theorem svd_truncation_eq_left_proj {W : Type*}
    {U₁ : Matrix (ZMod n) t ℝ} {U₂ : Matrix (ZMod n) ρ ℝ}
    {D₁ : Matrix t W ℝ} {D₂ : Matrix ρ W ℝ} {Z : Matrix (ZMod n) W ℝ}
    (h1 : U₁ᵀ * U₁ = 1) (h2 : U₁ᵀ * U₂ = 0) (hZ : Z = U₁ * D₁ + U₂ * D₂) :
    U₁ * D₁ = U₁ * U₁ᵀ * Z := by
  rw [hZ, Matrix.mul_add, ← Matrix.mul_assoc, Matrix.mul_assoc U₁ U₁ᵀ U₁, h1, Matrix.mul_one,
    ← Matrix.mul_assoc, Matrix.mul_assoc U₁ U₁ᵀ U₂, h2, Matrix.mul_zero, Matrix.zero_mul, add_zero]

section Step

variable {Δx Δt σ : ℝ} {A Aa : Matrix (Fin N) (Fin N) ℝ}
  {X₀ : Matrix (ZMod n) r ℝ} {S₀ : Matrix r r' ℝ} {V₀ : Matrix (Fin N) r' ℝ} {B₀ : ZMod n → ℝ}
  {Xs : Matrix (ZMod n) a ℝ} {Vs : Matrix (Fin N) a' ℝ} {Ss : Matrix a a' ℝ}
  {uh B₁ : ZMod n → ℝ} {Vc : Matrix (Fin N) c ℝ} {Sc : Matrix a c ℝ}
  {Xt : Matrix (ZMod n) b ℝ} {Vt : Matrix (Fin N) b' ℝ} {St : Matrix b b' ℝ}

omit [NeZero N] [DecidableEq a] [DecidableEq a'] in
/-- The Galerkin initial value reproduces `u⁰`, as the augmented bases contain the old ones. -/
theorem tilde_eq_of (hX : Xs * Xsᵀ * X₀ = X₀) (hV : Vs * Vsᵀ * V₀ = V₀) :
    Xs * sTilde X₀ S₀ V₀ Xs Vs * Vsᵀ = X₀ * S₀ * V₀ᵀ := by
  have e : Xs * (Xsᵀ * X₀ * S₀ * V₀ᵀ * Vs) * Vsᵀ = Xs * Xsᵀ * X₀ * S₀ * (Vs * Vsᵀ * V₀)ᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [sTilde, e, hX, hV]

/-- `tilde_eq_of` for a step of scheme (16) of arXiv 2307.07538. -/
theorem IsCoupledStep.tilde_eq
    (h : IsCoupledStep Δx Δt σ A Aa X₀ S₀ V₀ B₀ Xs Vs Ss uh B₁ Vc Sc Xt Vt St) :
    Xs * sTilde X₀ S₀ V₀ Xs Vs * Vsᵀ = X₀ * S₀ * V₀ᵀ :=
  tilde_eq_of h.Xs_X₀ h.Vs_V₀

/-- `u★ = X★ S★ V★ᵀ` is the Galerkin projection `P_X y P_V` of the full update
`y = u⁰ + Δt G u⁰`. -/
theorem IsCoupledStep.uStar_eq
    (h : IsCoupledStep Δx Δt σ A Aa X₀ S₀ V₀ B₀ Xs Vs Ss uh B₁ Vc Sc Xt Vt St) :
    Xs * Ss * Vsᵀ = Xs * Xsᵀ * (X₀ * S₀ * V₀ᵀ + Δt • transport Δx A Aa (X₀ * S₀ * V₀ᵀ))
      * (Vs * Vsᵀ) := by
  set T := sTilde X₀ S₀ V₀ Xs Vs with hT
  rw [← h.tilde_eq, h.Ss_eq, ← hT, sStar, transport]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg,
    Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_neg]
  have e0 : Xs * Xsᵀ * (Xs * T * Vsᵀ) * (Vs * Vsᵀ) = Xs * T * Vsᵀ := by
    calc Xs * Xsᵀ * (Xs * T * Vsᵀ) * (Vs * Vsᵀ) = Xs * (Xsᵀ * Xs) * T * (Vsᵀ * Vs) * Vsᵀ := by
          simp only [Matrix.mul_assoc]
      _ = Xs * T * Vsᵀ := by rw [h.Xs_orth, h.Vs_orth, Matrix.mul_one, Matrix.mul_one]
  have e1 : ∀ M : Matrix (Fin N) (Fin N) ℝ, ∀ D : Matrix (ZMod n) (ZMod n) ℝ,
      Xs * (Xsᵀ * D * Xs * T * Vsᵀ * M * Vs) * Vsᵀ
        = Xs * Xsᵀ * (D * (Xs * T * Vsᵀ) * M) * (Vs * Vsᵀ) := fun M D => by
    simp only [Matrix.mul_assoc]
  rw [e0, e1, e1]
  abel

omit [DecidableEq a] [DecidableEq a'] in
/-- The explicit part `R` of (16d) is the zeroth column of `y = u⁰ + Δt G u⁰`. -/
theorem rhsR_eq_of (hX : Xs * Xsᵀ * X₀ = X₀) (hV : Vs * Vsᵀ * V₀ = V₀) (j : ZMod n) :
    rhsR Δx Δt A Aa X₀ S₀ V₀ Xs Vs (sTilde X₀ S₀ V₀ Xs Vs) j
      = (X₀ * S₀ * V₀ᵀ + Δt • transport Δx A Aa (X₀ * S₀ * V₀ᵀ)) j 0 := by
  have e1 : ∀ (M : Matrix (Fin N) (Fin N) ℝ) (D : Matrix (ZMod n) (ZMod n) ℝ),
      D * Xs * sTilde X₀ S₀ V₀ Xs Vs * Vsᵀ * M = D * (X₀ * S₀ * V₀ᵀ) * M := fun M D => by
    rw [← tilde_eq_of hX hV]
    simp only [Matrix.mul_assoc]
  rw [rhsR, e1, e1, transport]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
  ring

/-- `rhsR_eq_of` for a step of scheme (16) of arXiv 2307.07538. -/
theorem IsCoupledStep.rhsR_eq
    (h : IsCoupledStep Δx Δt σ A Aa X₀ S₀ V₀ B₀ Xs Vs Ss uh B₁ Vc Sc Xt Vt St) (j : ZMod n) :
    rhsR Δx Δt A Aa X₀ S₀ V₀ Xs Vs (sTilde X₀ S₀ V₀ Xs Vs) j
      = (X₀ * S₀ * V₀ᵀ + Δt • transport Δx A Aa (X₀ * S₀ * V₀ᵀ)) j 0 :=
  rhsR_eq_of h.Xs_X₀ h.Vs_V₀ j

omit [NeZero n] [NeZero N] [DecidableEq a] [DecidableEq a'] in
/-- The K-step (16a) is the full update tested with `V⁰`. -/
theorem kStar_eq [NeZero n] [NeZero N] [DecidableEq r'] (hV : V₀ᵀ * V₀ = 1) :
    kStar Δx Δt A Aa X₀ S₀ V₀
      = (X₀ * S₀ * V₀ᵀ + Δt • transport Δx A Aa (X₀ * S₀ * V₀ᵀ)) * V₀ := by
  have e0 : X₀ * S₀ * V₀ᵀ * V₀ = X₀ * S₀ := by
    rw [Matrix.mul_assoc (X₀ * S₀), hV, Matrix.mul_one]
  simp only [kStar, transport, Matrix.add_mul, Matrix.smul_mul, Matrix.neg_mul, e0,
    smul_add, smul_neg, ← Matrix.mul_assoc]
  abel

omit [NeZero n] [NeZero N] [DecidableEq a] [DecidableEq a'] in
/-- The L-step (16b) is the full update tested with `X⁰`, for symmetric `A`, `|A|`. -/
theorem lStar_eq [NeZero n] [NeZero N] [DecidableEq r] (hX : X₀ᵀ * X₀ = 1) (hA : Aᵀ = A)
    (hAa : Aaᵀ = Aa) :
    lStar Δx Δt A Aa X₀ S₀ V₀
      = (X₀ * S₀ * V₀ᵀ + Δt • transport Δx A Aa (X₀ * S₀ * V₀ᵀ))ᵀ * X₀ := by
  have e0 : (X₀ * S₀ * V₀ᵀ)ᵀ * X₀ = V₀ * S₀ᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, hX,
      Matrix.mul_one]
  have e1 : ∀ D : Matrix (ZMod n) (ZMod n) ℝ, ∀ M : Matrix (Fin N) (Fin N) ℝ, Mᵀ = M →
      (D * (X₀ * S₀ * V₀ᵀ) * M)ᵀ * X₀ = M * (V₀ * S₀ᵀ) * (X₀ᵀ * D * X₀)ᵀ := by
    intro D M hM
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hM, Matrix.mul_assoc]
  simp only [lStar, transport, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_neg,
    Matrix.add_mul, Matrix.smul_mul, Matrix.neg_mul, e0, e1 _ _ hA, e1 _ _ hAa, smul_add, smul_neg]
  abel

/-- By construction of (16f)–(16h), the augmented solution is
`u¹ = u★ (1 - e₀ e₀ᵀ) / (1 + σ Δt) + û e₀ᵀ`, the relation stated at the start of the proof of
Theorem 3 of the paper.  We derive it from the fields of `IsCoupledStep`. -/
theorem IsCoupledStep.augmented_eq
    (h : IsCoupledStep Δx Δt σ A Aa X₀ S₀ V₀ B₀ Xs Vs Ss uh B₁ Vc Sc Xt Vt St) :
    Xt * St * Vtᵀ
      = (1 + Δt * σ)⁻¹ • ((Xs * Ss * Vsᵀ) * (1 - E0 N)) + zeroCol N uh := by
  have hE : E0 N * (Vt * Vtᵀ) = E0 N := by
    have := congrArg Matrix.transpose h.Vt_e₀
    simpa [Matrix.transpose_mul, E0_transpose, Matrix.mul_assoc] using this
  have hVc : Vcᵀ * (Vt * Vtᵀ) = Vcᵀ := by
    have := congrArg Matrix.transpose h.Vt_Vc
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  have hL : Xt * Xtᵀ * zeroCol N uh = zeroCol N uh := by
    ext p m
    by_cases hm : m = 0
    · subst hm
      have := congrFun h.Xt_uh p
      simpa [zeroCol, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    · simp [zeroCol, Matrix.mul_apply, hm]
  have hR : zeroCol N uh * (Vt * Vtᵀ) = zeroCol N uh := by
    rw [← zeroCol_mul_E0, Matrix.mul_assoc, hE]
  have hrem : Vcᵀ * (1 - E0 N) * (Vt * Vtᵀ) = Vcᵀ * (1 - E0 N) := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hVc, Matrix.mul_assoc, hE]
  have h1 : Xt * St * Vtᵀ = Xs * Sc * (Vcᵀ * (1 - E0 N)) + zeroCol N uh := by
    have e : Xt * (Xtᵀ * Xs * Sc * Vcᵀ * (1 - E0 N) * Vt + Xtᵀ * zeroCol N uh * Vt) * Vtᵀ
        = (Xt * Xtᵀ * Xs) * Sc * (Vcᵀ * (1 - E0 N) * (Vt * Vtᵀ))
          + (Xt * Xtᵀ * zeroCol N uh) * (Vt * Vtᵀ) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    rw [h.St_eq, e, h.Xt_Xs, hrem, hL, hR]
  have hSc : Sc * Vcᵀ = (Vc * Scᵀ)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have h2 : Sc * Vcᵀ * (1 - E0 N) = (1 + Δt * σ)⁻¹ • (Ss * Vsᵀ * (1 - E0 N)) := by
    rw [hSc, h.scat_eq]
    ext k m
    rw [mul_sub_E0_apply, Matrix.smul_apply, mul_sub_E0_apply]
    by_cases hm : m = 0
    · simp [hm]
    · simp only [hm, scatL, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, ite_false,
        div_eq_inv_mul, smul_eq_mul]
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
  have h3 : Xs * Sc * (Vcᵀ * (1 - E0 N)) = Xs * (Sc * Vcᵀ * (1 - E0 N)) := by
    simp only [Matrix.mul_assoc]
  have h4 : Xs * (Ss * Vsᵀ * (1 - E0 N)) = Xs * Ss * Vsᵀ * (1 - E0 N) := by
    simp only [Matrix.mul_assoc]
  rw [h1, h3, h2, Matrix.mul_smul, h4]

/-- The norm of the augmented solution: `‖u¹‖² = ‖u★ (1 - e₀ e₀ᵀ)‖² / (1 + σΔt)² + ‖û‖²`.  This
needs no assumption on `e₀` and `V★`. -/
theorem IsCoupledStep.norm_augmented_sq
    (h : IsCoupledStep Δx Δt σ A Aa X₀ S₀ V₀ B₀ Xs Vs Ss uh B₁ Vc Sc Xt Vt St) :
    ‖Xt * St * Vtᵀ‖ ^ 2 = ((1 + Δt * σ)⁻¹) ^ 2 * ‖(Xs * Ss * Vsᵀ) * (1 - E0 N)‖ ^ 2
      + ∑ j, uh j ^ 2 := by
  have hidem : (1 - E0 N) * (1 - E0 N) = 1 - E0 N := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, E0_mul_E0, sub_self,
      sub_zero]
  have hz : zeroCol N uh * (1 - E0 N) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, zeroCol_mul_E0, sub_self]
  have hw1 : (Xt * St * Vtᵀ) * (1 - E0 N)
      = (1 + Δt * σ)⁻¹ • ((Xs * Ss * Vsᵀ) * (1 - E0 N)) := by
    rw [h.augmented_eq, Matrix.add_mul, Matrix.smul_mul, hz, add_zero,
      Matrix.mul_assoc (Xs * Ss * Vsᵀ), hidem]
  have hw0 : ∀ p, (Xt * St * Vtᵀ) p 0 = uh p := by
    intro p
    rw [h.augmented_eq, Matrix.add_apply, Matrix.smul_apply, mul_sub_E0_apply]
    simp [zeroCol]
  rw [norm_sq_split (Xt * St * Vtᵀ), hw1, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  simp only [hw0]

/-- If `e₀` lies in the range of the old basis `V⁰`, it lies in the range of `V★ ⊇ V⁰`. -/
theorem IsCoupledStep.e₀_mem
    (h : IsCoupledStep Δx Δt σ A Aa X₀ S₀ V₀ B₀ Xs Vs Ss uh B₁ Vc Sc Xt Vt St)
    (he₀ : V₀ * V₀ᵀ * E0 N = E0 N) : Vs * Vsᵀ * E0 N = E0 N := by
  rw [← he₀, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h.Vs_V₀]

/-- The test identity of the proof of Theorem 3: testing the scheme with `u¹` gives
`(1 + σΔt) ‖u¹‖² = ⟪y, u¹⟫ + σΔt ⟪B¹, û⟫` with the full update `y = u⁰ + Δt G u⁰`.

**This is where `e₀ ∈ range V★` is needed**, a fact the paper's proof uses without saying so:
`u★ (1 - e₀ e₀ᵀ)` has to stay in the Galerkin space. See `not_energy_stable_without_e₀`. -/
theorem IsCoupledStep.test_identity
    (h : IsCoupledStep Δx Δt σ A Aa X₀ S₀ V₀ B₀ Xs Vs Ss uh B₁ Vc Sc Xt Vt St)
    (hne : 1 + Δt * σ ≠ 0) (he₀ : Vs * Vsᵀ * E0 N = E0 N) :
    (1 + σ * Δt) * ‖Xt * St * Vtᵀ‖ ^ 2
      = ⟪X₀ * S₀ * V₀ᵀ + Δt • transport Δx A Aa (X₀ * S₀ * V₀ᵀ), Xt * St * Vtᵀ⟫
        + σ * Δt * ∑ j, B₁ j * uh j := by
  set y := X₀ * S₀ * V₀ᵀ + Δt • transport Δx A Aa (X₀ * S₀ * V₀ᵀ) with hy
  set us := Xs * Ss * Vsᵀ with hus
  set w := Xt * St * Vtᵀ with hw
  set w' := us * (1 - E0 N) with hw'
  set e := (1 + Δt * σ)⁻¹ with he
  have hwe : w = e • w' + zeroCol N uh := h.augmented_eq
  have hPXsymm : (Xs * Xsᵀ)ᵀ = Xs * Xsᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hPVsymm : (Vs * Vsᵀ)ᵀ = Vs * Vsᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hPXus : Xs * Xsᵀ * us = us := by
    calc Xs * Xsᵀ * us = Xs * (Xsᵀ * Xs) * Ss * Vsᵀ := by simp only [hus, Matrix.mul_assoc]
      _ = us := by rw [h.Xs_orth, Matrix.mul_one]
  have husPV : us * (Vs * Vsᵀ) = us := by
    calc us * (Vs * Vsᵀ) = Xs * Ss * (Vsᵀ * Vs) * Vsᵀ := by simp only [hus, Matrix.mul_assoc]
      _ = us := by rw [h.Vs_orth, Matrix.mul_one]
  have hE : E0 N * (Vs * Vsᵀ) = E0 N := by
    have := congrArg Matrix.transpose he₀
    rwa [Matrix.transpose_mul, hPVsymm, E0_transpose] at this
  have hfix : Xs * Xsᵀ * w' * (Vs * Vsᵀ) = w' := by
    calc Xs * Xsᵀ * w' * (Vs * Vsᵀ) = (Xs * Xsᵀ * us) * (1 - E0 N) * (Vs * Vsᵀ) := by
          simp only [hw', Matrix.mul_assoc]
      _ = us * (Vs * Vsᵀ) - us * (E0 N * (Vs * Vsᵀ)) := by
          rw [hPXus, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.mul_assoc us (E0 N)]
      _ = w' := by rw [husPV, hE, hw', Matrix.mul_sub, Matrix.mul_one]
  have husy : us = Xs * Xsᵀ * y * (Vs * Vsᵀ) := h.uStar_eq
  have hy' : ⟪y, w'⟫ = ⟪us, w'⟫ := by
    calc ⟪y, w'⟫ = ⟪y, Xs * Xsᵀ * w' * (Vs * Vsᵀ)⟫ := by rw [hfix]
      _ = ⟪y * (Vs * Vsᵀ)ᵀ, Xs * Xsᵀ * w'⟫ := Frobenius.inner_mul_right' _ _ _
      _ = ⟪(Xs * Xsᵀ)ᵀ * (y * (Vs * Vsᵀ)ᵀ), w'⟫ := Frobenius.inner_mul_left' _ _ _
      _ = ⟪us, w'⟫ := by
          have e : (Xs * Xsᵀ) * (y * (Vs * Vsᵀ)) = us := by
            rw [husy, Matrix.mul_assoc (Xs * Xsᵀ) y]
          rw [hPXsymm, hPVsymm, e]
  have hidem : (1 - E0 N) * (1 - E0 N) = 1 - E0 N := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, E0_mul_E0, sub_self,
      sub_zero]
  have hsym : (1 - E0 N)ᵀ = 1 - E0 N := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, E0_transpose]
  have hus' : ⟪us, w'⟫ = ‖w'‖ ^ 2 := by
    have e1 : ⟪us, w'⟫ = ⟪us * (1 - E0 N)ᵀ, us⟫ := Frobenius.inner_mul_right' _ _ _
    have e2 : ⟪w', w'⟫ = ⟪us * (1 - E0 N) * (1 - E0 N)ᵀ, us⟫ :=
      Frobenius.inner_mul_right' _ _ _
    rw [← real_inner_self_eq_norm_sq, e1, e2, hsym, Matrix.mul_assoc us, hidem]
  have hnorm : ‖w‖ ^ 2 = e ^ 2 * ‖w'‖ ^ 2 + ∑ j, uh j ^ 2 := h.norm_augmented_sq
  have hinner : ⟪y, w⟫ = e * ‖w'‖ ^ 2 + ∑ j, y j 0 * uh j := by
    rw [hwe, inner_add_right, inner_smul_right, hy', hus', inner_zeroCol]
  have huh : ∀ j, (1 + σ * Δt) * uh j = y j 0 + σ * Δt * B₁ j := by
    intro j
    have h1 := h.uh_eq j
    rw [h.rhsR_eq j, ← hy] at h1
    linarith
  have he1 : e * (1 + σ * Δt) = 1 := by
    rw [he, mul_comm σ Δt]
    exact inv_mul_cancel₀ hne
  have hsum : (1 + σ * Δt) * ∑ j, uh j ^ 2 = ∑ j, y j 0 * uh j + σ * Δt * ∑ j, B₁ j * uh j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := huh j
    calc (1 + σ * Δt) * uh j ^ 2 = ((1 + σ * Δt) * uh j) * uh j := by ring
      _ = y j 0 * uh j + σ * Δt * (B₁ j * uh j) := by rw [this]; ring
  have hmain : (1 + σ * Δt) * (e ^ 2 * ‖w'‖ ^ 2) = e * ‖w'‖ ^ 2 := by
    calc (1 + σ * Δt) * (e ^ 2 * ‖w'‖ ^ 2) = (e * (1 + σ * Δt)) * (e * ‖w'‖ ^ 2) := by ring
      _ = e * ‖w'‖ ^ 2 := by rw [he1, one_mul]
  rw [hnorm, hinner, mul_add, hmain, hsum]
  ring

variable {Q : Matrix (Fin N) (Fin N) ℝ} {s : Fin N → ℝ}

omit [NeZero N] in
/-- The estimate for `u` in Step 2 and Step 4 of the proof of Theorem 3: from the test identity,
Young's inequality, summation by parts and Lemma 2. -/
private theorem energy_u (d : IsEigenDecomp A Q s) (hΔx : 0 < Δx) (hΔt : 0 ≤ Δt)
    (hcfl : ∀ k, Δt * |s k| ≤ Δx) {u₀ w : Matrix (ZMod n) (Fin N) ℝ} {τ R : ℝ}
    (htest : (1 + τ) * ‖w‖ ^ 2 = ⟪u₀ + Δt • transport Δx A (absA Q s) u₀, w⟫ + R) :
    (1 / 2 + τ) * ‖w‖ ^ 2 ≤ 1 / 2 * ‖u₀‖ ^ 2 + R := by
  have hsplit : ⟪transport Δx A (absA Q s) u₀, w⟫
      = ⟪transport Δx A (absA Q s) w, w⟫ + ⟪transport Δx A (absA Q s) (u₀ - w), w⟫ := by
    rw [transport_sub, inner_sub_left]
    ring
  have hself := inner_transport_self d hΔx w
  have hadj := inner_transport_adjoint d Δx (u₀ - w) w
  have hL2 := lemma2_sharp d hΔx hcfl w
  set F := flux Δx A (absA Q s) w
  set D := ‖Dplus n Δx * w * sqrtAbsA Q s‖ ^ 2 with hD
  have hyoung : 0 ≤ ‖(u₀ - w) + Δt • F‖ ^ 2 := sq_nonneg _
  rw [norm_add_sq_real, norm_smul, inner_smul_right, mul_pow, Real.norm_eq_abs, sq_abs,
    norm_sub_sq_real] at hyoung
  rw [inner_add_left, inner_smul_left, hsplit, hself, hadj] at htest
  simp only [conj_trivial] at htest
  have hb := mul_nonpos_of_nonneg_of_nonpos hΔt hL2
  have e1 : Δt * (Δt / 2 * ‖F‖ ^ 2 - D) = 1 / 2 * (Δt ^ 2 * ‖F‖ ^ 2) - Δt * D := by ring
  rw [e1] at hb
  have e2 : (1 + τ) * ‖w‖ ^ 2 = ‖w‖ ^ 2 + τ * ‖w‖ ^ 2 := by ring
  have e3 : (1 / 2 + τ) * ‖w‖ ^ 2 = 1 / 2 * ‖w‖ ^ 2 + τ * ‖w‖ ^ 2 := by ring
  have e4 : Δt * (-D + -⟪u₀ - w, F⟫) = -(Δt * D) - Δt * ⟪u₀ - w, F⟫ := by ring
  have e5 : 2 * (Δt * ⟪u₀ - w, F⟫) = 2 * Δt * ⟪u₀ - w, F⟫ := by ring
  rw [e2, e4] at htest
  rw [e3]
  linarith

/-- The estimate for `B`, Step 1 of the proof of Theorem 3. -/
private theorem energy_B {τ : ℝ} (hB : ∀ j, B₁ j = B₀ j + τ * (uh j - B₁ j)) :
    (1 / 2 + τ) * ∑ j, B₁ j ^ 2 ≤ 1 / 2 * ∑ j, B₀ j ^ 2 + τ * ∑ j, B₁ j * uh j := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have h := hB j
  have e : (1 + τ) * B₁ j ^ 2 = B₀ j * B₁ j + τ * (B₁ j * uh j) := by
    have : (1 + τ) * B₁ j = B₀ j + τ * uh j := by linarith
    calc (1 + τ) * B₁ j ^ 2 = ((1 + τ) * B₁ j) * B₁ j := by ring
      _ = B₀ j * B₁ j + τ * (B₁ j * uh j) := by rw [this]; ring
  nlinarith [sq_nonneg (B₀ j - B₁ j)]

/-- **Energy stability of the augmented solution** (arXiv 2307.07538, the core of Theorem 3, before
truncation).  Under the sharp condition `Δt |σ_k| ≤ Δx` and `e₀ ∈ range V⁰`,
`‖B¹‖² + ‖X̃¹ S̃¹ Ṽ¹ᵀ‖² ≤ ‖B⁰‖² + ‖X⁰ S⁰ V⁰ᵀ‖²`. -/
theorem IsCoupledStep.energy_augmented_le
    (h : IsCoupledStep Δx Δt σ A (absA Q s) X₀ S₀ V₀ B₀ Xs Vs Ss uh B₁ Vc Sc Xt Vt St)
    (d : IsEigenDecomp A Q s) (he₀ : V₀ * V₀ᵀ * E0 N = E0 N) (hΔx : 0 < Δx) (hΔt : 0 ≤ Δt)
    (hσ : 0 ≤ σ) (hcfl : ∀ k, Δt * |s k| ≤ Δx) :
    ∑ j, B₁ j ^ 2 + ‖Xt * St * Vtᵀ‖ ^ 2 ≤ ∑ j, B₀ j ^ 2 + ‖X₀ * S₀ * V₀ᵀ‖ ^ 2 := by
  have hτ : 0 ≤ σ * Δt := mul_nonneg hσ hΔt
  have hne : 1 + Δt * σ ≠ 0 := by
    have : 0 ≤ Δt * σ := mul_nonneg hΔt hσ
    linarith
  have h1 := energy_u d hΔx hΔt hcfl (h.test_identity hne (h.e₀_mem he₀))
  have h2 := energy_B (τ := σ * Δt) h.B₁_eq
  set w := Xt * St * Vtᵀ with hw
  have hw0 : ∀ p, w p 0 = uh p := by
    intro p
    rw [hw, h.augmented_eq, Matrix.add_apply, Matrix.smul_apply, mul_sub_E0_apply]
    simp [zeroCol]
  have hsplit := norm_sq_split w
  simp only [hw0] at hsplit
  have hrem : 0 ≤ ‖w * (1 - E0 N)‖ ^ 2 := sq_nonneg _
  have hsq : 0 ≤ ∑ j, (uh j - B₁ j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hexp : ∑ j, (uh j - B₁ j) ^ 2 = ∑ j, uh j ^ 2 - 2 * ∑ j, B₁ j * uh j + ∑ j, B₁ j ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hkey : 0 ≤ σ * Δt * (‖w‖ ^ 2 + ∑ j, B₁ j ^ 2 - 2 * ∑ j, B₁ j * uh j) :=
    mul_nonneg hτ (by linarith)
  linarith

/-- The truncation does not increase the norm.  The paper only observes that it leaves the zeroth
moment alone; norm control comes from `norm_consTrunc_le` and the orthogonality of `U Uᵀ`. -/
theorem IsConservativeTruncation.norm_le {U : Matrix (ZMod n) ρ ℝ}
    {Y : Matrix (ZMod n) (Fin N) ℝ} {X₁ : Matrix (ZMod n) t ℝ} {S₁ : Matrix t t' ℝ}
    {V₁ : Matrix (Fin N) t' ℝ} (h : IsConservativeTruncation U Y X₁ S₁ V₁) :
    ‖X₁ * S₁ * V₁ᵀ‖ ≤ ‖Y‖ := by
  have hC : IsOrthProj (Frobenius.rightMulCLM (m := ZMod n) (E0 N)) := by
    refine ⟨fun x => ?_, fun x y => ?_⟩
    · simp only [Frobenius.rightMulCLM_apply, Matrix.mul_assoc, E0_mul_E0]
    · simp only [Frobenius.rightMulCLM_apply]
      rw [Frobenius.inner_mul_right, E0_transpose]
  have hU := isOrthProj_leftProj (n := Fin N) h.U_orth
  have hsub : Y - Y * E0 N = Y * (1 - E0 N) := by rw [Matrix.mul_sub, Matrix.mul_one]
  have hT : Frobenius.rightMulCLM (m := ZMod n) (E0 N)
      ((fun z => U * Uᵀ * z) (Y - Frobenius.rightMulCLM (m := ZMod n) (E0 N) Y)) = 0 := by
    simp only [Frobenius.rightMulCLM_apply, hsub, Matrix.mul_assoc]
    rw [Matrix.sub_mul, Matrix.one_mul, E0_mul_E0, sub_self]
    simp
  have hle := norm_consTrunc_le (T := fun z => U * Uᵀ * z) hC hT (hU.norm_le _)
  have e : consTrunc (Frobenius.rightMulCLM (m := ZMod n) (E0 N)) (fun z => U * Uᵀ * z) Y
      = X₁ * S₁ * V₁ᵀ := by
    rw [h.eq, consTrunc]
    simp only [Frobenius.rightMulCLM_apply, hsub]
  rwa [e] at hle

/-- The truncation leaves the zeroth moment unchanged. -/
theorem IsConservativeTruncation.zeroth_moment {U : Matrix (ZMod n) ρ ℝ}
    {Y : Matrix (ZMod n) (Fin N) ℝ} {X₁ : Matrix (ZMod n) t ℝ} {S₁ : Matrix t t' ℝ}
    {V₁ : Matrix (Fin N) t' ℝ} (h : IsConservativeTruncation U Y X₁ S₁ V₁) (p : ZMod n) :
    (X₁ * S₁ * V₁ᵀ) p 0 = Y p 0 := by
  have h0 : ∀ q : ρ, (Uᵀ * (Y * (1 - E0 N)) : Matrix ρ (Fin N) ℝ) q 0 = 0 := fun q => by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [mul_sub_E0_apply]
    simp
  have h1 : (U * Uᵀ * (Y * (1 - E0 N)) : Matrix (ZMod n) (Fin N) ℝ) p 0 = 0 := by
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [h0, mul_zero]
  rw [h.eq, Matrix.add_apply, h1, add_zero, mul_E0_apply]
  simp

/-- **Theorem 3** (arXiv 2307.07538) in the sharp form its proof gives: one step of scheme (16)
followed by the conservative truncation satisfies
`‖B¹‖² + ‖X¹ S¹ V¹ᵀ‖² ≤ ‖B⁰‖² + ‖X⁰ S⁰ V⁰ᵀ‖²` if `Δt |σ_k| ≤ Δx` for all `k`, `σ ≥ 0` and
`e₀ ∈ range V⁰`.

The last hypothesis is **not in the paper**, and it cannot be dropped: see
`not_energy_stable_without_e₀`.  It is an invariant of the scheme (`V₁_e₀`), so it holds at every
step after the first, and at the first if `V⁰` is chosen to contain `e₀`.  The paper states neither
`σ ≥ 0` (its proof needs it) nor that the truncation does not increase the norm (proved in
`IsConservativeTruncation.norm_le`). -/
theorem theorem3_sharp {U : Matrix (ZMod n) ρ ℝ} {X₁ : Matrix (ZMod n) t ℝ} {S₁ : Matrix t t' ℝ}
    {V₁ : Matrix (Fin N) t' ℝ}
    (h : IsCoupledStep Δx Δt σ A (absA Q s) X₀ S₀ V₀ B₀ Xs Vs Ss uh B₁ Vc Sc Xt Vt St)
    (htr : IsConservativeTruncation U (Xt * St * Vtᵀ) X₁ S₁ V₁)
    (d : IsEigenDecomp A Q s) (he₀ : V₀ * V₀ᵀ * E0 N = E0 N) (hΔx : 0 < Δx) (hΔt : 0 ≤ Δt)
    (hσ : 0 ≤ σ) (hcfl : ∀ k, Δt * |s k| ≤ Δx) :
    ∑ j, B₁ j ^ 2 + ‖X₁ * S₁ * V₁ᵀ‖ ^ 2 ≤ ∑ j, B₀ j ^ 2 + ‖X₀ * S₀ * V₀ᵀ‖ ^ 2 := by
  have h1 := h.energy_augmented_le d he₀ hΔx hΔt hσ hcfl
  have h2 := htr.norm_le
  have h3 : ‖X₁ * S₁ * V₁ᵀ‖ ^ 2 ≤ ‖Xt * St * Vtᵀ‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  linarith

/-- **Theorem 3** (arXiv 2307.07538): for the paper's matrix `A_{mn} = ⟨P_m, μ P_n⟩_μ` and
`Δt ≤ Δx`, one step of the coupled implicit scheme (16) with conservative truncation satisfies
`‖B¹‖² + ‖X¹ S¹ V¹ᵀ‖² ≤ ‖B⁰‖² + ‖X⁰ S⁰ V⁰ᵀ‖²`.  As in `theorem3_sharp`, `e₀ ∈ range V⁰` and `σ ≥ 0`
are added to the paper's statement.  The bound `|σ_k| ≤ 1` is derived. -/
theorem theorem3 {w : ℝ} {P : Fin N → ℝ → ℝ} (hP : IsOrthonormalFamily w P)
    {U : Matrix (ZMod n) ρ ℝ} {X₁ : Matrix (ZMod n) t ℝ} {S₁ : Matrix t t' ℝ}
    {V₁ : Matrix (Fin N) t' ℝ}
    (h : IsCoupledStep Δx Δt σ (momentMatrix w P) (absA Q s) X₀ S₀ V₀ B₀
      Xs Vs Ss uh B₁ Vc Sc Xt Vt St)
    (htr : IsConservativeTruncation U (Xt * St * Vtᵀ) X₁ S₁ V₁)
    (d : IsEigenDecomp (momentMatrix w P) Q s) (he₀ : V₀ * V₀ᵀ * E0 N = E0 N) (hΔx : 0 < Δx)
    (hΔt : 0 ≤ Δt) (hσ : 0 ≤ σ) (hcfl : Δt ≤ Δx) :
    ∑ j, B₁ j ^ 2 + ‖X₁ * S₁ * V₁ᵀ‖ ^ 2 ≤ ∑ j, B₀ j ^ 2 + ‖X₀ * S₀ * V₀ᵀ‖ ^ 2 :=
  theorem3_sharp h htr d he₀ hΔx hΔt hσ fun k => by
    nlinarith [d.abs_le_one hP k, abs_nonneg (s k)]

/-- Scheme (16) is solvable for all data, so the hypotheses of `theorem3` can hold, with the full
bases `X★ = X̃¹ = 1`, `V★ = V^{★,scat} = Ṽ¹ = 1`.  The coupled system (16d), (16e) has the explicit
solution given in the proof. -/
theorem exists_isCoupledStep (Δx Δt σ : ℝ) (A Aa : Matrix (Fin N) (Fin N) ℝ)
    (X₀ : Matrix (ZMod n) r ℝ) (S₀ : Matrix r r' ℝ) (V₀ : Matrix (Fin N) r' ℝ) (B₀ : ZMod n → ℝ)
    (hτ : 0 ≤ σ * Δt) :
    ∃ (Ss : Matrix (ZMod n) (Fin N) ℝ) (uh B₁ : ZMod n → ℝ) (Sc : Matrix (ZMod n) (Fin N) ℝ)
      (St : Matrix (ZMod n) (Fin N) ℝ),
      IsCoupledStep Δx Δt σ A Aa X₀ S₀ V₀ B₀ (1 : Matrix (ZMod n) (ZMod n) ℝ)
        (1 : Matrix (Fin N) (Fin N) ℝ) Ss uh B₁ (1 : Matrix (Fin N) (Fin N) ℝ) Sc
        (1 : Matrix (ZMod n) (ZMod n) ℝ) (1 : Matrix (Fin N) (Fin N) ℝ) St := by
  set τ : ℝ := σ * Δt with hτdef
  have h1 : 1 + τ ≠ 0 := by linarith
  have h2 : 1 + 2 * τ ≠ 0 := by linarith
  set T := sTilde X₀ S₀ V₀ (1 : Matrix (ZMod n) (ZMod n) ℝ) (1 : Matrix (Fin N) (Fin N) ℝ) with hT
  set Ss := sStar Δx Δt A Aa (1 : Matrix (ZMod n) (ZMod n) ℝ) (1 : Matrix (Fin N) (Fin N) ℝ) T
    with hSs
  set R := rhsR Δx Δt A Aa X₀ S₀ V₀ (1 : Matrix (ZMod n) (ZMod n) ℝ)
    (1 : Matrix (Fin N) (Fin N) ℝ) T with hR
  let uh : ZMod n → ℝ := fun j => ((1 + τ) * R j + τ * B₀ j) / (1 + 2 * τ)
  let B₁ : ZMod n → ℝ := fun j => (B₀ j + τ * uh j) / (1 + τ)
  let Sc : Matrix (ZMod n) (Fin N) ℝ := (scatL σ Δt Ssᵀ)ᵀ
  let St : Matrix (ZMod n) (Fin N) ℝ :=
    (1 : Matrix (ZMod n) (ZMod n) ℝ)ᵀ * (1 : Matrix (ZMod n) (ZMod n) ℝ) * Sc
        * (1 : Matrix (Fin N) (Fin N) ℝ)ᵀ * (1 - E0 N) * (1 : Matrix (Fin N) (Fin N) ℝ)
      + (1 : Matrix (ZMod n) (ZMod n) ℝ)ᵀ * zeroCol N uh * (1 : Matrix (Fin N) (Fin N) ℝ)
  refine ⟨Ss, uh, B₁, Sc, St, ?_⟩
  refine ⟨by simp, by simp, by simp, by simp, by simp, by simp, rfl, ?_, ?_, by simp, ?_, by simp,
    by simp, by simp, by simp, by simp, by simp, rfl⟩
  · intro j
    simp only [B₁, uh]
    field_simp
    ring
  · intro j
    simp only [B₁]
    field_simp
    ring
  · simp [Sc]

/-- A conservative truncation exists for every `Y`, namely no truncation at all (`U = 1`).  It is
the case `ϑ = 0` of Section 6 of arXiv 2307.07538. -/
theorem exists_isConservativeTruncation (Y : Matrix (ZMod n) (Fin N) ℝ) :
    IsConservativeTruncation (1 : Matrix (ZMod n) (ZMod n) ℝ) Y
      (1 : Matrix (ZMod n) (ZMod n) ℝ) Y (1 : Matrix (Fin N) (Fin N) ℝ) := by
  refine ⟨by simp, by simp, by simp, ?_, by simp⟩
  simp [Matrix.mul_sub]

end Step

end Scheme

/-! ### Theorem 2: the naive IMEX scheme is not energy stable -/

section Naive

variable [NeZero N] {r r' a a' : Type*} [Fintype r] [Fintype r'] [Fintype a] [Fintype a']
  [DecidableEq a] [DecidableEq a']

/-- **The naive IMEX scheme** (12) of arXiv 2307.07538: (12a) and (12b) treat transport and `B`
explicitly and absorption implicitly, the bases are augmented, (12c) is the corresponding S-step
and (12d) updates `B` with the new zeroth moment.  The paper does not truncate here. -/
structure IsNaiveStep (Δx Δt σ : ℝ) (A Aa : Matrix (Fin N) (Fin N) ℝ)
    (X₀ : Matrix (ZMod n) r ℝ) (S₀ : Matrix r r' ℝ) (V₀ : Matrix (Fin N) r' ℝ) (B₀ : ZMod n → ℝ)
    (K₁ : Matrix (ZMod n) r' ℝ) (L₁ : Matrix (Fin N) r ℝ)
    (Xh : Matrix (ZMod n) a ℝ) (Vh : Matrix (Fin N) a' ℝ) (Sh : Matrix a a' ℝ)
    (B₁ : ZMod n → ℝ) : Prop where
  K_eq : K₁ = kStar Δx Δt A Aa X₀ S₀ V₀ + σ • (Δt • (zeroCol N B₀ * V₀) - Δt • K₁)
  L_eq : L₁ = lStar Δx Δt A Aa X₀ S₀ V₀ + σ • (Δt • ((zeroCol N B₀)ᵀ * X₀) - Δt • L₁)
  Xh_orth : Xhᵀ * Xh = 1
  Vh_orth : Vhᵀ * Vh = 1
  Xh_K : Xh * Xhᵀ * K₁ = K₁
  Xh_X₀ : Xh * Xhᵀ * X₀ = X₀
  Vh_L : Vh * Vhᵀ * L₁ = L₁
  Vh_V₀ : Vh * Vhᵀ * V₀ = V₀
  S_eq : Sh = sStar Δx Δt A Aa Xh Vh (sTilde X₀ S₀ V₀ Xh Vh)
    + σ • (Δt • (Xhᵀ * zeroCol N B₀ * Vh) - Δt • Sh)
  B_eq : ∀ p, B₁ p = B₀ p + σ * Δt * ((Xh * Sh * Vhᵀ) p 0 - B₁ p)

/-- **Theorem 2** (arXiv 2307.07538): the naive scheme (12) is not energy stable.  For all `σ > 0`,
all `Δt > 0`, all grids and every angular matrix, there is rank-one data for which
`E¹ > E⁰`, where `E = ½ ‖u‖² + ½ ‖B‖²`.  The data are the paper's spatially constant
`u⁰ = (u¹ - σΔt α (1 + σΔt)) e₀ᵀ`, `B⁰ = u¹ + α (1 + σΔt)` with `u¹ = 1` and
`α = σΔt / (2 (1 + σΔt + (σΔt)² + (σΔt)³ / 2))`, the midpoint of the paper's interval for `α`. -/
theorem naive_not_energy_stable (Δx : ℝ) {Δt σ : ℝ} (hΔt : 0 < Δt) (hσ : 0 < σ)
    (A Aa : Matrix (Fin N) (Fin N) ℝ) :
    ∃ (X₀ : Matrix (ZMod n) Unit ℝ) (S₀ : Matrix Unit Unit ℝ) (V₀ : Matrix (Fin N) Unit ℝ)
      (B₀ : ZMod n → ℝ) (K₁ : Matrix (ZMod n) Unit ℝ) (L₁ : Matrix (Fin N) Unit ℝ)
      (Xh : Matrix (ZMod n) Unit ℝ) (Vh : Matrix (Fin N) Unit ℝ) (Sh : Matrix Unit Unit ℝ)
      (B₁ : ZMod n → ℝ),
      X₀ᵀ * X₀ = 1 ∧ V₀ᵀ * V₀ = 1 ∧ IsNaiveStep Δx Δt σ A Aa X₀ S₀ V₀ B₀ K₁ L₁ Xh Vh Sh B₁ ∧
      1 / 2 * ‖X₀ * S₀ * V₀ᵀ‖ ^ 2 + 1 / 2 * ∑ p, B₀ p ^ 2
        < 1 / 2 * ‖Xh * Sh * Vhᵀ‖ ^ 2 + 1 / 2 * ∑ p, B₁ p ^ 2 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  set ν : ℝ := √(n : ℝ) with hνdef
  have hν : 0 < ν := Real.sqrt_pos.2 hn
  have hνν : ν * ν = n := Real.mul_self_sqrt hn.le
  set τ : ℝ := σ * Δt with hτdef
  have hτ : 0 < τ := mul_pos hσ hΔt
  set κ : ℝ := 1 + τ + τ ^ 2 + τ ^ 3 / 2 with hκdef
  have hκ : 0 < κ := by positivity
  set α : ℝ := τ / (2 * κ) with hαdef
  have hα : 0 < α := by positivity
  have hακ : α * κ = τ / 2 := by rw [hαdef]; field_simp
  set c₀ : ℝ := 1 - τ * α * (1 + τ) with hc₀
  set b₀ : ℝ := 1 + α * (1 + τ) with hb₀
  set b₁ : ℝ := 1 + α with hb₁
  have hsum : ∑ _p : ZMod n, ν⁻¹ = ν := by
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, ← hνν]
    field_simp
  let X₀ : Matrix (ZMod n) Unit ℝ := Matrix.of fun _ _ => ν⁻¹
  let S₀ : Matrix Unit Unit ℝ := Matrix.of fun _ _ => c₀ * ν
  let V₀ : Matrix (Fin N) Unit ℝ := Matrix.of fun m _ => if m = 0 then 1 else 0
  let Sh : Matrix Unit Unit ℝ := Matrix.of fun _ _ => ν
  have hD1 : Dx n Δx * X₀ = 0 := by
    ext p k
    simp [Dx_mul_apply, X₀]
  have hD2 : Dxx n Δx * X₀ = 0 := by
    ext p k
    rw [Dxx_mul_apply]
    simp only [X₀, Matrix.of_apply, Matrix.zero_apply]
    ring
  have hX : X₀ᵀ * X₀ = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, X₀, Matrix.of_apply, Matrix.one_apply_eq,
      Subsingleton.elim i j]
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, ← hνν]
    field_simp
  have hV : V₀ᵀ * V₀ = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, V₀, Matrix.of_apply, Matrix.one_apply_eq,
      Subsingleton.elim i j]
    simp
  have hk : kStar Δx Δt A Aa X₀ S₀ V₀ = X₀ * S₀ := by
    simp only [kStar, ← Matrix.mul_assoc, hD1, hD2, Matrix.zero_mul, smul_zero, sub_zero, add_zero]
  have hl : lStar Δx Δt A Aa X₀ S₀ V₀ = V₀ * S₀ᵀ := by
    have e1 : X₀ᵀ * Dx n Δx * X₀ = 0 := by rw [Matrix.mul_assoc, hD1, Matrix.mul_zero]
    have e2 : X₀ᵀ * Dxx n Δx * X₀ = 0 := by rw [Matrix.mul_assoc, hD2, Matrix.mul_zero]
    simp only [lStar, e1, e2, Matrix.transpose_zero, Matrix.mul_zero, smul_zero, sub_zero, add_zero]
  have hst : sTilde X₀ S₀ V₀ X₀ V₀ = S₀ := by
    have e : X₀ᵀ * X₀ * S₀ * V₀ᵀ * V₀ = (X₀ᵀ * X₀) * S₀ * (V₀ᵀ * V₀) := by
      simp only [Matrix.mul_assoc]
    rw [sTilde, e, hX, hV, Matrix.one_mul, Matrix.mul_one]
  have hss : sStar Δx Δt A Aa X₀ V₀ S₀ = S₀ := by
    have e1 : X₀ᵀ * Dx n Δx * X₀ = 0 := by rw [Matrix.mul_assoc, hD1, Matrix.mul_zero]
    have e2 : X₀ᵀ * Dxx n Δx * X₀ = 0 := by rw [Matrix.mul_assoc, hD2, Matrix.mul_zero]
    simp only [sStar, e1, e2, Matrix.zero_mul, smul_zero, sub_zero, add_zero]
  have hcc : (1 + τ) * 1 = c₀ + τ * b₀ := by rw [hc₀, hb₀]; ring
  have hbb : b₁ = b₀ + τ * (1 - b₁) := by rw [hb₁, hb₀]; ring
  have hPX : ∀ Z : Matrix (ZMod n) Unit ℝ, (∀ p q, Z p () = Z q ()) → X₀ * X₀ᵀ * Z = Z := by
    intro Z hZ
    ext p ⟨⟩
    simp only [Matrix.mul_apply, Matrix.transpose_apply, X₀, Matrix.of_apply, Finset.sum_const,
      Finset.card_univ, Fintype.card_unit, one_smul]
    simp only [← Finset.mul_sum]
    rw [show ∑ q, Z q () = (n : ℝ) * Z p () by
      rw [Finset.sum_congr rfl fun q _ => hZ q p, Finset.sum_const, Finset.card_univ, ZMod.card,
        nsmul_eq_mul], ← hνν]
    field_simp
  have hPV : ∀ Z : Matrix (Fin N) Unit ℝ, (∀ m, m ≠ 0 → Z m () = 0) → V₀ * V₀ᵀ * Z = Z := by
    intro Z hZ
    ext m ⟨⟩
    by_cases hm : m = 0
    · subst hm
      simp [Matrix.mul_apply, V₀]
    · simp [Matrix.mul_apply, V₀, hm, hZ m hm]
  have hu : ∀ c : ℝ, X₀ * (Matrix.of fun _ _ => c * ν : Matrix Unit Unit ℝ) * V₀ᵀ
      = zeroCol N (fun _ => c) := by
    intro c
    ext p m
    simp [Matrix.mul_apply, X₀, V₀, zeroCol]
    field_simp
  have hnorm : ∀ c : ℝ, ‖(zeroCol N fun _ => c : Matrix (ZMod n) (Fin N) ℝ)‖ ^ 2 = n * c ^ 2 := by
    intro c
    rw [Frobenius.norm_sq_eq_sum]
    have : ∀ p : ZMod n,
        ∑ m, (zeroCol N (fun _ => c) : Matrix (ZMod n) (Fin N) ℝ) p m ^ 2 = c ^ 2 := by
      intro p
      simp [zeroCol, ite_pow, Finset.sum_ite_eq']
    simp only [this, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have hconst : ∀ c : ℝ, ∑ _p : ZMod n, c ^ 2 = n * c ^ 2 := fun c => by
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have e2 : X₀ * Sh * V₀ᵀ = zeroCol N fun _ => (1 : ℝ) := by
    have := hu 1
    simpa [Sh] using this
  have hZ : ∀ (p : ZMod n) (k : Unit), (zeroCol N (fun _ : ZMod n => b₀) * V₀) p k = b₀ := by
    intro p k
    simp [Matrix.mul_apply, zeroCol, V₀]
  have hZ' : ∀ (k k' : Unit), (X₀ᵀ * zeroCol N (fun _ : ZMod n => b₀) * V₀) k k' = b₀ * ν := by
    intro k k'
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    simp only [hZ, Matrix.transpose_apply, X₀, Matrix.of_apply, ← Finset.sum_mul, hsum]
    ring
  have hXS : ∀ p (k : Unit), (X₀ * S₀) p k = c₀ := by
    intro p k
    simp [Matrix.mul_apply, X₀, S₀]
    field_simp
  refine ⟨X₀, S₀, V₀, fun _ => b₀, Matrix.of fun _ _ => 1, Matrix.of fun m _ =>
    if m = 0 then ν else 0, X₀, V₀, Sh, fun _ => b₁, hX, hV, ?_, ?_⟩
  · refine ⟨?_, ?_, hX, hV, hPX _ (fun _ _ => rfl), hPX _ (fun _ _ => rfl), hPV _ ?_, hPV _ ?_,
      ?_, ?_⟩
    · rw [hk]
      ext p k
      simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, hXS, hZ,
        smul_eq_mul]
      linear_combination hcc
    · rw [hl]
      ext m k
      by_cases hm : m = 0
      · subst hm
        have e : ((zeroCol N fun _ : ZMod n => b₀)ᵀ * X₀) 0 k = b₀ * ν := by
          simp only [Matrix.mul_apply, Matrix.transpose_apply, zeroCol, X₀, Matrix.of_apply,
            ite_true, ← Finset.mul_sum, hsum]
        simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, e,
          smul_eq_mul, ite_true, Matrix.mul_apply, Matrix.transpose_apply, V₀, S₀]
        simp only [Fintype.sum_unique, one_mul]
        linear_combination ν * hcc
      · simp [Matrix.mul_apply, V₀, zeroCol, hm]
    · intro m hm
      simp [hm]
    · intro m hm
      simp [V₀, hm]
    · rw [hst, hss]
      ext k k'
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, hZ', smul_eq_mul, Sh, S₀,
        Matrix.of_apply]
      linear_combination ν * hcc
    · intro p
      rw [e2]
      simp only [zeroCol, Matrix.of_apply, ite_true]
      exact hbb
  · have e1 : X₀ * S₀ * V₀ᵀ = zeroCol N fun _ => c₀ := hu c₀
    rw [e1, e2, hnorm, hnorm, hconst, hconst]
    have hid : (1 : ℝ) ^ 2 + b₁ ^ 2 - (c₀ ^ 2 + b₀ ^ 2) = 2 * τ * α * (τ - α * κ) := by
      rw [hc₀, hb₀, hb₁, hκdef]
      ring
    rw [hακ] at hid
    have hpos : 0 < 2 * τ * α * (τ - τ / 2) := by
      have : τ - τ / 2 = τ / 2 := by ring
      rw [this]
      positivity
    have h3 : c₀ ^ 2 + b₀ ^ 2 < 1 ^ 2 + b₁ ^ 2 := by linarith
    nlinarith

end Naive

/-! ### The hypothesis `e₀ ∈ range V⁰` cannot be dropped -/

section Counterexample

/-- The matrix `[[0, 1], [1, 0]]`.  The true `N = 2` Legendre matrix is `swapM / √3`, see
`momentMatrix_legendreTwo`. -/
def swapM : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- The orthogonal eigenvector matrix of `swapM`. -/
noncomputable def Q₂ : Matrix (Fin 2) (Fin 2) ℝ := (√2)⁻¹ • !![1, 1; 1, -1]

/-- `(1/√2)² = 1/2`. -/
private theorem sqrt_two_inv_sq : (√2)⁻¹ * (√2)⁻¹ = (1 / 2 : ℝ) := by
  have h : √2 * √2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
  rw [← mul_inv, h]
  norm_num

/-- The entries of `swapM`. -/
private theorem swapM_apply :
    swapM 0 0 = 0 ∧ swapM 0 1 = 1 ∧ swapM 1 0 = 1 ∧ swapM 1 1 = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The entries of `Q₂`. -/
private theorem Q₂_apply :
    Q₂ 0 0 = (√2)⁻¹ ∧ Q₂ 0 1 = (√2)⁻¹ ∧ Q₂ 1 0 = (√2)⁻¹ ∧ Q₂ 1 1 = -(√2)⁻¹ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Q₂]

/-- `κ swapM` has the eigendecomposition `Q₂ diag(κ, -κ) Q₂ᵀ`. -/
theorem isEigenDecomp_swap (κ : ℝ) : IsEigenDecomp (κ • swapM) Q₂ ![κ, -κ] := by
  have h := sqrt_two_inv_sq
  obtain ⟨q00, q01, q10, q11⟩ := Q₂_apply
  obtain ⟨s00, s01, s10, s11⟩ := swapM_apply
  have hs0 : (![κ, -κ] : Fin 2 → ℝ) 0 = κ := rfl
  have hs1 : (![κ, -κ] : Fin 2 → ℝ) 1 = -κ := rfl
  refine ⟨?_, ?_⟩
  · ext i j
    revert i j
    simp only [Fin.forall_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
      q00, q01, q10, q11, Matrix.one_apply_eq, Matrix.one_apply_ne (zero_ne_one (α := Fin 2)),
      Matrix.one_apply_ne (one_ne_zero (α := Fin 2))]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · linear_combination 2 * h
    · ring
    · ring
    · linear_combination 2 * h
  · ext i j
    rw [specFn, Matrix.mul_apply]
    revert i j
    simp only [Fin.forall_fin_two, Matrix.smul_apply, Matrix.mul_diagonal, Fin.sum_univ_two,
      Matrix.transpose_apply, smul_eq_mul, q00, q01, q10, q11, s00, s01, s10, s11, hs0, hs1]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · ring
    · linear_combination (-2 * κ) * h
    · linear_combination (-2 * κ) * h
    · ring

/-- `|κ swapM| = κ` for `κ ≥ 0`. -/
theorem absA_swap {κ : ℝ} (hκ : 0 ≤ κ) : absA Q₂ ![κ, -κ] = κ • 1 := by
  have hf : (fun k => |(![κ, -κ] : Fin 2 → ℝ) k|) = fun _ => κ := by
    funext k
    fin_cases k <;> simp [abs_of_nonneg hκ]
  have hd : Matrix.diagonal (fun _ : Fin 2 => κ) = κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [absA, specFn, hf, hd, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    (isEigenDecomp_swap κ).orth']

/-- A sum over the three cells of the counterexample. -/
private theorem sum_zmod3 (f : ZMod 3 → ℝ) : ∑ p, f p = f 0 + f 1 + f 2 :=
  Fin.sum_univ_three f

/-- The spatial basis `δ₀` of the counterexample. -/
private noncomputable def cx₀ : Matrix (ZMod 3) Unit ℝ :=
  Matrix.of fun p _ => if p = 0 then 1 else 0

/-- The angular basis `(3/5, 4/5)` of the counterexample, which does not contain `e₀`. -/
private noncomputable def cv₀ : Matrix (Fin 2) Unit ℝ := Matrix.of fun m _ => ![3 / 5, 4 / 5] m

/-- The full transport update of the counterexample. -/
private noncomputable def cY : Matrix (ZMod 3) (Fin 2) ℝ :=
  Matrix.of fun p m => if p = 1 then 7 / 10 else if p = 2 then ![-1 / 10, 1 / 10] m else 0

/-- `δ₀` is a unit vector. -/
private theorem cx₀_orth : cx₀ᵀ * cx₀ = 1 := by
  ext i j
  simp [Matrix.mul_apply, cx₀, Subsingleton.elim i j]

/-- `(3/5, 4/5)` is a unit vector. -/
private theorem cv₀_orth : cv₀ᵀ * cv₀ = 1 := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_two, cv₀, Subsingleton.elim i j]
  norm_num

/-- The initial value `u⁰` of the counterexample, entrywise. -/
private theorem cu_eq : cx₀ * (1 : Matrix Unit Unit ℝ) * cv₀ᵀ
    = (Matrix.of fun p m => if p = 0 then ![3 / 5, 4 / 5] m else 0 :
        Matrix (ZMod 3) (Fin 2) ℝ) := by
  ext p m
  simp [Matrix.mul_apply, cx₀, cv₀]

/-- Right multiplication by `swapM` exchanges the two columns. -/
private theorem swap_apply (M : Matrix (ZMod 3) (Fin 2) ℝ) (p : ZMod 3) :
    (M * swapM) p 0 = M p 1 ∧ (M * swapM) p 1 = M p 0 := by
  obtain ⟨s00, s01, s10, s11⟩ := swapM_apply
  simp only [Matrix.mul_apply, Fin.sum_univ_two, s00, s01, s10, s11, mul_zero, mul_one, zero_add,
    add_zero, and_self]

/-- In the counterexample, `y = u⁰ + Δt G u⁰` is a pair of pure shifts: `Δt κ = Δx` is the
sharp CFL number, at which the upwind fluxes of Lemma 2 transport exactly one cell. -/
private theorem cY_eq {κ Δx Δt : ℝ} (hκ : 0 < κ) (hΔx : 0 < Δx) (hcfl : Δt * κ = Δx) :
    cx₀ * (1 : Matrix Unit Unit ℝ) * cv₀ᵀ
      + Δt • transport Δx (κ • swapM) (κ • 1) (cx₀ * (1 : Matrix Unit Unit ℝ) * cv₀ᵀ) = cY := by
  have hΔt : Δt ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hcfl
    exact hΔx.ne hcfl
  have a1 : (0 : ZMod 3) + 1 = 1 := by decide
  have a2 : (0 : ZMod 3) - 1 = 2 := by decide
  have a3 : (1 : ZMod 3) + 1 = 2 := by decide
  have a4 : (1 : ZMod 3) - 1 = 0 := by decide
  have a5 : (2 : ZMod 3) + 1 = 0 := by decide
  have a6 : (2 : ZMod 3) - 1 = 1 := by decide
  have b1 : (1 : ZMod 3) ≠ 0 := by decide
  have b2 : (2 : ZMod 3) ≠ 0 := by decide
  have b3 : (2 : ZMod 3) ≠ 1 := by decide
  have b4 : (0 : ZMod 3) ≠ 1 := by decide
  have b5 : (0 : ZMod 3) ≠ 2 := by decide
  subst hcfl
  rw [cu_eq]
  ext p m
  have hp : p = 0 ∨ p = 1 ∨ p = 2 := by
    revert p
    decide
  have hs0 : ∀ M : Matrix (ZMod 3) (Fin 2) ℝ, (M * swapM) p 0 = M p 1 :=
    fun M => (swap_apply M p).1
  have hs1 : ∀ M : Matrix (ZMod 3) (Fin 2) ℝ, (M * swapM) p 1 = M p 0 :=
    fun M => (swap_apply M p).2
  simp only [transport, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul,
    Matrix.mul_smul, Matrix.mul_one, Dxx_mul_apply]
  fin_cases m
  all_goals
    simp only [Fin.zero_eta, Fin.mk_one, hs0, hs1, Dx_mul_apply]
    rcases hp with rfl | rfl | rfl
  all_goals
    simp only [a1, a2, a3, a4, a5, a6, Matrix.of_apply, cY, b1, b2, b3, b4, b5, ite_true, ite_false,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    norm_num

/-- The value of the K-step of the counterexample. -/
private noncomputable def cK : Matrix (ZMod 3) Unit ℝ := cY * cv₀

/-- `K★ = (0, 49/50, 1/50)` in the counterexample. -/
private theorem cK_apply :
    cK 0 () = 0 ∧ cK 1 () = 49 / 50 ∧ cK 2 () = 1 / 50 := by
  have b3 : (2 : ZMod 3) ≠ 1 := by decide
  have b4 : (0 : ZMod 3) ≠ 1 := by decide
  have b5 : (0 : ZMod 3) ≠ 2 := by decide
  simp only [cK, Matrix.mul_apply, Fin.sum_univ_two, cY, cv₀, Matrix.of_apply, b3, b4, b5,
    ite_true, ite_false, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- The zeroth moment of the full update of the counterexample. -/
private theorem cY_zero : cY 0 0 = 0 ∧ cY 1 0 = 7 / 10 ∧ cY 2 0 = -1 / 10 := by
  have b3 : (2 : ZMod 3) ≠ 1 := by decide
  have b4 : (0 : ZMod 3) ≠ 1 := by decide
  have b5 : (0 : ZMod 3) ≠ 2 := by decide
  simp only [cY, Matrix.of_apply, b3, b4, b5, ite_true, ite_false, Matrix.cons_val_zero, and_self]

/-- `√2402`, the norm of `50 K★` in the counterexample. -/
private noncomputable def cξ : ℝ := √2402

/-- `√2402 √2402 = 2402`. -/
private theorem cξ_mul : cξ * cξ = 2402 := Real.mul_self_sqrt (by norm_num)

/-- `√2402 > 0`. -/
private theorem cξ_pos : 0 < cξ := Real.sqrt_pos.2 (by norm_num)

/-- The orthonormalization `X★ = [K★ / ‖K★‖, δ₀]` of `[K★, X⁰]`. -/
private noncomputable def cXs : Matrix (ZMod 3) (Fin 2) ℝ :=
  Matrix.of fun p k => if k = 0 then cK p () * (50 / cξ) else cx₀ p ()

/-- `X★` of the counterexample has orthonormal columns. -/
private theorem cXs_orth : cXsᵀ * cXs = 1 := by
  obtain ⟨k0, k1, k2⟩ := cK_apply
  have hξ := cξ_mul
  have hξ0 : cξ ≠ 0 := cξ_pos.ne'
  have b1 : (1 : ZMod 3) ≠ 0 := by decide
  have b2 : (2 : ZMod 3) ≠ 0 := by decide
  ext i j
  revert i j
  simp only [Fin.forall_fin_two, Matrix.mul_apply, sum_zmod3, Matrix.transpose_apply, cXs,
    Matrix.of_apply, ite_true, one_ne_zero, ite_false, k0, k1, k2, cx₀, b1, b2,
    Matrix.one_apply_eq, Matrix.one_apply_ne (zero_ne_one (α := Fin 2)),
    Matrix.one_apply_ne (one_ne_zero (α := Fin 2))]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · field_simp
    linear_combination (-1 : ℝ) * hξ
  · ring
  · ring
  · ring

/-- The projector `X Xᵀ` fixes the range of `X`. -/
private theorem proj_fix {a : Type*} [Fintype a] [DecidableEq a] {κ : Type*}
    {X : Matrix (ZMod 3) a ℝ} (hX : Xᵀ * X = 1) (C : Matrix a κ ℝ) :
    X * Xᵀ * (X * C) = X * C := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Xᵀ, hX, Matrix.one_mul]

/-- `K★` lies in the range of `X★`. -/
private theorem cXs_K : cXs * cXsᵀ * cK = cK := by
  have hξ0 : cξ ≠ 0 := cξ_pos.ne'
  have e : cK = cXs * (Matrix.of fun k _ => if k = 0 then cξ / 50 else 0 :
      Matrix (Fin 2) Unit ℝ) := by
    ext p ⟨⟩
    simp only [Matrix.mul_apply, Fin.sum_univ_two, cXs, Matrix.of_apply, ite_true, one_ne_zero,
      ite_false, mul_zero, add_zero]
    field_simp
  rw [e]
  exact proj_fix cXs_orth _

/-- `X⁰` lies in the range of `X★`. -/
private theorem cXs_X₀ : cXs * cXsᵀ * cx₀ = cx₀ := by
  have e : cx₀ = cXs * (Matrix.of fun k _ => if k = 0 then 0 else 1 :
      Matrix (Fin 2) Unit ℝ) := by
    ext p ⟨⟩
    simp only [Matrix.mul_apply, Fin.sum_univ_two, cXs, Matrix.of_apply, ite_true, one_ne_zero,
      ite_false, mul_zero, zero_add, mul_one]
  rw [e]
  exact proj_fix cXs_orth _

/-- `V★ = V⁰` fixes `V⁰`. -/
private theorem cv₀_fix : cv₀ * cv₀ᵀ * cv₀ = cv₀ := by
  rw [Matrix.mul_assoc, cv₀_orth, Matrix.mul_one]

/-- The numerical inequality behind the counterexample: `E¹ > 1 = E⁰` for `0 ≤ τ ≤ 1/100`. -/
private theorem cx_energy_ineq {τ : ℝ} (hτ : 0 ≤ τ) (hsmall : τ ≤ 1 / 100) :
    0 + 1 < (τ / (1 + 2 * τ)) ^ 2 * (1 / 2)
      + (((1 + τ)⁻¹) ^ 2 * (38432 / 62500) + ((1 + τ) / (1 + 2 * τ)) ^ 2 * (1 / 2)) := by
  have h1τ : 0 < 1 + 2 * τ := by linarith
  have h1τ' : 0 < 1 + τ := by linarith
  set x : ℝ := ((1 + τ)⁻¹) ^ 2 with hx
  have hx1 : x * (1 + τ) ^ 2 = 1 := by
    rw [hx, ← mul_pow, inv_mul_cancel₀ h1τ'.ne', one_pow]
  have hxpos : 0 < x := by positivity
  have hτ2 : (1 + τ) ^ 2 ≤ 10201 / 10000 := by nlinarith
  have hxl : 98 / 100 ≤ x := by nlinarith
  set y : ℝ := ((1 + 2 * τ)⁻¹) ^ 2 with hyy
  have hy1 : y * (1 + 2 * τ) ^ 2 = 1 := by
    rw [hyy, ← mul_pow, inv_mul_cancel₀ h1τ.ne', one_pow]
  have hypos : 0 < y := by positivity
  have hsq : (τ / (1 + 2 * τ)) ^ 2 * (1 / 2) + ((1 + τ) / (1 + 2 * τ)) ^ 2 * (1 / 2)
      = y * ((1 + τ) ^ 2 + τ ^ 2) * (1 / 2) := by
    rw [hyy, div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hyl : 96 / 100 ≤ y * ((1 + τ) ^ 2 + τ ^ 2) := by
    have h3 : 96 / 100 * (1 + 2 * τ) ^ 2 ≤ (1 + τ) ^ 2 + τ ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h3 hypos.le]
  linarith only [hsq, hxl, hyl]

/-- The conclusion of `not_energy_stable_without_e₀`: there is rank-one orthonormal data with
`B⁰ = 0` and `e₀ ∉ range V⁰` for which one step of scheme (16) with conservative truncation, on
`n = 3` cells with `N = 2` moments, meets the sharp condition `Δt |σ_k| ≤ Δx` and increases the
energy. -/
def IsEnergyIncreasingStep (Δx Δt σ : ℝ) (A Q : Matrix (Fin 2) (Fin 2) ℝ) (s : Fin 2 → ℝ) : Prop :=
  ∃ (X₀ : Matrix (ZMod 3) Unit ℝ) (S₀ : Matrix Unit Unit ℝ) (V₀ : Matrix (Fin 2) Unit ℝ)
    (Xs : Matrix (ZMod 3) (Fin 2) ℝ) (Vs : Matrix (Fin 2) Unit ℝ) (Ss : Matrix (Fin 2) Unit ℝ)
    (uh B₁ : ZMod 3 → ℝ) (Vc : Matrix (Fin 2) (Fin 2) ℝ) (Sc : Matrix (Fin 2) (Fin 2) ℝ)
    (Xt : Matrix (ZMod 3) (ZMod 3) ℝ) (Vt : Matrix (Fin 2) (Fin 2) ℝ)
    (St : Matrix (ZMod 3) (Fin 2) ℝ) (X₁ : Matrix (ZMod 3) (ZMod 3) ℝ)
    (S₁ : Matrix (ZMod 3) (Fin 2) ℝ) (V₁ : Matrix (Fin 2) (Fin 2) ℝ),
    X₀ᵀ * X₀ = 1 ∧ V₀ᵀ * V₀ = 1 ∧ V₀ * V₀ᵀ * E0 2 ≠ E0 2 ∧
    IsCoupledStep Δx Δt σ A (absA Q s) X₀ S₀ V₀ 0 Xs Vs Ss uh B₁ Vc Sc Xt Vt St ∧
    IsConservativeTruncation (1 : Matrix (ZMod 3) (ZMod 3) ℝ) (Xt * St * Vtᵀ) X₁ S₁ V₁ ∧
    (∀ k, Δt * |s k| ≤ Δx) ∧
    ∑ j, (0 : ZMod 3 → ℝ) j ^ 2 + ‖X₀ * S₀ * V₀ᵀ‖ ^ 2 < ∑ j, B₁ j ^ 2 + ‖X₁ * S₁ * V₁ᵀ‖ ^ 2

/-- **`e₀ ∈ range V⁰` cannot be dropped from `theorem3_sharp`.**  arXiv 2307.07538, Theorem 3 does
not assume it, and its proof uses it silently.  Take `n = 3`, `N = 2`, `A = κ swapM` with
eigenvalues `±κ`, `Δt κ = Δx`, `0 ≤ σ Δt ≤ 1/100`, `B⁰ = 0` and `u⁰ = δ₀ (3/5, 4/5)`.  Then scheme
(16) with conservative truncation increases the energy.  The bases are the ones the paper
prescribes: `X★` spans `[K★, X⁰]`, and `V★ = V⁰` because `L★ = 0`.

This does **not** decide `Δt ≤ Δx` for the Legendre matrix: there `|σ_k| < 1`.  Taking `κ = 1/√3`
gives the true `N = 2` matrix with `Δt = √3 Δx`, see `legendreTwo_not_energy_stable`. -/
theorem not_energy_stable_without_e₀ {κ Δx Δt σ : ℝ} {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hAeq : A = κ • swapM) (hκ : 0 < κ) (hΔx : 0 < Δx) (hcfl : Δt * κ = Δx) (hσ : 0 ≤ σ)
    (hsmall : σ * Δt ≤ 1 / 100) : IsEnergyIncreasingStep Δx Δt σ A Q₂ ![κ, -κ] := by
  subst hAeq
  have hΔt : 0 < Δt := by
    by_contra h
    have : Δt * κ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 h) hκ.le
    linarith
  set τ : ℝ := σ * Δt with hτdef
  have hτ : 0 ≤ τ := mul_nonneg hσ hΔt.le
  have h1τ : 0 < 1 + 2 * τ := by linarith
  have h1τ' : 0 < 1 + τ := by linarith
  have hAb := absA_swap hκ.le
  have hA : (κ • swapM)ᵀ = κ • swapM := (isEigenDecomp_swap κ).symm
  have hAa : (κ • (1 : Matrix (Fin 2) (Fin 2) ℝ))ᵀ = κ • 1 := by
    rw [Matrix.transpose_smul, Matrix.transpose_one]
  have hy := cY_eq hκ hΔx hcfl
  set A : Matrix (Fin 2) (Fin 2) ℝ := κ • swapM with hAdef
  set Aa : Matrix (Fin 2) (Fin 2) ℝ := κ • 1 with hAadef
  have hk : kStar Δx Δt A Aa cx₀ 1 cv₀ = cK := by rw [kStar_eq cv₀_orth, hy, cK]
  have hl : lStar Δx Δt A Aa cx₀ 1 cv₀ = 0 := by
    rw [lStar_eq cx₀_orth hA hAa, hy]
    ext m ⟨⟩
    have h2 : ∀ p : ZMod 3, cY p m * cx₀ p () = 0 := by
      intro p
      by_cases hp : p = 0
      · subst hp
        simp [cY, show (0 : ZMod 3) ≠ 1 by decide, show (0 : ZMod 3) ≠ 2 by decide]
      · simp [cx₀, hp]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, h2, Finset.sum_const_zero,
      Matrix.zero_apply]
  set St₀ := sTilde cx₀ 1 cv₀ cXs cv₀ with hSt₀
  set Ss := sStar Δx Δt A Aa cXs cv₀ St₀ with hSs
  let R : ZMod 3 → ℝ := fun j => cY j 0
  let uh : ZMod 3 → ℝ := fun j => (1 + τ) / (1 + 2 * τ) * R j
  let B₁ : ZMod 3 → ℝ := fun j => τ / (1 + 2 * τ) * R j
  let Sc : Matrix (Fin 2) (Fin 2) ℝ := (scatL σ Δt (cv₀ * Ssᵀ))ᵀ
  let St : Matrix (ZMod 3) (Fin 2) ℝ :=
    (1 : Matrix (ZMod 3) (ZMod 3) ℝ)ᵀ * cXs * Sc * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * (1 - E0 2)
        * (1 : Matrix (Fin 2) (Fin 2) ℝ)
      + (1 : Matrix (ZMod 3) (ZMod 3) ℝ)ᵀ * zeroCol 2 uh * (1 : Matrix (Fin 2) (Fin 2) ℝ)
  have hstep : IsCoupledStep Δx Δt σ A Aa cx₀ 1 cv₀ 0 cXs cv₀ Ss uh B₁ 1 Sc 1 1 St := by
    have hR : ∀ j, rhsR Δx Δt A Aa cx₀ 1 cv₀ cXs cv₀ St₀ j = R j := by
      intro j
      rw [hSt₀, rhsR_eq_of cXs_X₀ cv₀_fix, hy]
    refine ⟨cXs_orth, cv₀_orth, ?_, cXs_X₀, ?_, cv₀_fix, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, rfl⟩
    · rw [hk]
      exact cXs_K
    · rw [hl, Matrix.mul_zero]
    · intro j
      rw [hR]
      simp only [uh, B₁]
      field_simp
      ring
    · intro j
      simp only [uh, B₁, Pi.zero_apply]
      field_simp
      ring
    · simp
    · simp [Sc]
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
  have htrunc : IsConservativeTruncation (1 : Matrix (ZMod 3) (ZMod 3) ℝ)
      ((1 : Matrix (ZMod 3) (ZMod 3) ℝ) * St * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ)
      (1 : Matrix (ZMod 3) (ZMod 3) ℝ) St (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    refine ⟨by simp, by simp, by simp, ?_, by simp⟩
    simp [Matrix.mul_sub]
  have hcfl' : ∀ k, Δt * |(![κ, -κ] : Fin 2 → ℝ) k| ≤ Δx := by
    intro k
    have h0 : |(![κ, -κ] : Fin 2 → ℝ) 0| = κ := abs_of_pos hκ
    have h1 : |(![κ, -κ] : Fin 2 → ℝ) 1| = κ := by
      change |-κ| = κ
      rw [abs_neg, abs_of_pos hκ]
    revert k
    simp only [Fin.forall_fin_two, h0, h1, hcfl, le_refl, and_self]
  have hstep' : IsCoupledStep Δx Δt σ A (absA Q₂ ![κ, -κ]) cx₀ 1 cv₀ 0 cXs cv₀ Ss uh B₁ 1 Sc 1 1
      St := by
    rw [hAb]
    exact hstep
  have hup : ∑ j, (0 : ZMod 3 → ℝ) j ^ 2 + ‖cx₀ * (1 : Matrix Unit Unit ℝ) * cv₀ᵀ‖ ^ 2
      < ∑ j, B₁ j ^ 2 + ‖(1 : Matrix (ZMod 3) (ZMod 3) ℝ) * St
          * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ‖ ^ 2 := by
    obtain ⟨k0, k1, k2⟩ := cK_apply
    obtain ⟨y0, y1, y2⟩ := cY_zero
    have hus : cXs * Ss * cv₀ᵀ = cK * cv₀ᵀ := by
      have h1 := hstep.uStar_eq
      rw [hy] at h1
      rw [h1]
      calc cXs * cXsᵀ * cY * (cv₀ * cv₀ᵀ) = cXs * cXsᵀ * (cY * cv₀) * cv₀ᵀ := by
            simp only [Matrix.mul_assoc]
        _ = cK * cv₀ᵀ := by rw [show cY * cv₀ = cK from rfl, cXs_K]
    have hrem : ‖cXs * Ss * cv₀ᵀ * (1 - E0 2)‖ ^ 2 = 38432 / 62500 := by
      rw [hus, Frobenius.norm_sq_eq_sum, sum_zmod3]
      have hv : ∀ p, (cK * cv₀ᵀ) p 1 = cK p () * (4 / 5) := by
        intro p
        simp [Matrix.mul_apply, cv₀]
      simp only [Fin.sum_univ_two, mul_sub_E0_apply, one_ne_zero, ite_true, ite_false, hv, k0, k1,
        k2]
      norm_num
    have hu0 : ‖cx₀ * (1 : Matrix Unit Unit ℝ) * cv₀ᵀ‖ ^ 2 = 1 := by
      rw [cu_eq, Frobenius.norm_sq_eq_sum, sum_zmod3]
      simp only [Fin.sum_univ_two, Matrix.of_apply, ite_true, ite_false,
        show (1 : ZMod 3) ≠ 0 by decide, show (2 : ZMod 3) ≠ 0 by decide, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      norm_num
    have hB₁ : ∑ j, B₁ j ^ 2 = (τ / (1 + 2 * τ)) ^ 2 * (1 / 2) := by
      rw [sum_zmod3]
      simp only [B₁, R, y0, y1, y2]
      ring
    have huh : ∑ j, uh j ^ 2 = ((1 + τ) / (1 + 2 * τ)) ^ 2 * (1 / 2) := by
      rw [sum_zmod3]
      simp only [uh, R, y0, y1, y2]
      ring
    have hnorm := hstep.norm_augmented_sq
    rw [hrem, huh, mul_comm Δt σ, ← hτdef] at hnorm
    have hz : ∑ j, (0 : ZMod 3 → ℝ) j ^ 2 = 0 := by simp
    rw [hz, hu0, hnorm, hB₁]
    exact cx_energy_ineq hτ hsmall
  have hne : cv₀ * cv₀ᵀ * E0 2 ≠ E0 2 := by
    intro he₀
    have := theorem3_sharp hstep' htrunc (isEigenDecomp_swap κ) he₀ hΔx hΔt.le hσ hcfl'
    exact absurd hup (not_lt.2 this)
  exact ⟨cx₀, 1, cv₀, cXs, cv₀, Ss, uh, B₁, 1, Sc, 1, 1, St, 1, St, 1, cx₀_orth, cv₀_orth, hne,
    hstep', htrunc, hcfl', hup⟩

end Counterexample

/-! ### The true `N = 2` Legendre matrix -/

section Legendre

/-- The normalized Legendre polynomials `P₀ = 1`, `P₁ = √3 μ` for `⟨f, g⟩_μ = ½ ∫_{-1}^1 f g`. -/
noncomputable def legendreTwo : Fin 2 → ℝ → ℝ := ![fun _ => 1, fun μ => √3 * μ]

/-- The moments of `μ` on `[-1, 1]` that enter the `N = 2` Legendre matrix. -/
private theorem integral_moments :
    (∫ _ in (-1 : ℝ)..1, (1 : ℝ)) = 2 ∧ (∫ μ in (-1 : ℝ)..1, μ) = 0 ∧
      (∫ μ in (-1 : ℝ)..1, μ ^ 2) = 2 / 3 ∧ (∫ μ in (-1 : ℝ)..1, μ ^ 3) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [integral_one]
    norm_num
  · rw [integral_id]
    norm_num
  · rw [integral_pow]
    norm_num
  · rw [integral_pow]
    norm_num

/-- The hypotheses of `lemma2` and `theorem3` hold for the true `N = 2` Legendre family, so these
theorems are not vacuous.  Orthonormality of the Legendre polynomials of every degree is not
formalized here. -/
theorem isOrthonormalFamily_legendreTwo : IsOrthonormalFamily (1 / 2) legendreTwo := by
  obtain ⟨i0, i1, i2, -⟩ := integral_moments
  have h3 : √3 * √3 = (3 : ℝ) := Real.mul_self_sqrt (by norm_num)
  refine ⟨by norm_num, fun m => ?_, fun m k => ?_⟩
  · revert m
    simp only [Fin.forall_fin_two]
    exact ⟨continuous_const, continuous_const.mul continuous_id⟩
  · have e3 : ∀ μ : ℝ, (√3 * μ) * (√3 * μ) = 3 * μ ^ 2 := fun μ => by
      linear_combination μ ^ 2 * h3
    have e5 : (∫ μ in (-1 : ℝ)..1, √3 * μ) = 0 := by
      rw [intervalIntegral.integral_const_mul, i1, mul_zero]
    revert m k
    simp only [Fin.forall_fin_two, angularInner, legendreTwo, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_one, one_mul, e3, e5, intervalIntegral.integral_const_mul, i0, i2,
      ite_true, zero_ne_one, one_ne_zero, ite_false]
    norm_num

/-- The paper's matrix for `N = 2` is `A = [[0, 1/√3], [1/√3, 0]]`. -/
theorem momentMatrix_legendreTwo :
    momentMatrix (1 / 2) legendreTwo = (1 / √3) • swapM := by
  obtain ⟨-, i1, i2, i3⟩ := integral_moments
  obtain ⟨s00, s01, s10, s11⟩ := swapM_apply
  have h3 : √3 * √3 = (3 : ℝ) := Real.mul_self_sqrt (by norm_num)
  have h0 : √3 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have e1 : ∀ μ : ℝ, (1 : ℝ) * (μ * 1) = μ := fun μ => by ring
  have e2 : ∀ μ : ℝ, (1 : ℝ) * (μ * (√3 * μ)) = √3 * μ ^ 2 := fun μ => by ring
  have e3 : ∀ μ : ℝ, (√3 * μ) * (μ * 1) = √3 * μ ^ 2 := fun μ => by ring
  have e4 : ∀ μ : ℝ, (√3 * μ) * (μ * (√3 * μ)) = 3 * μ ^ 3 := fun μ => by
    linear_combination μ ^ 3 * h3
  ext m k
  revert m k
  simp only [Fin.forall_fin_two, momentMatrix, Matrix.of_apply, angularInner, legendreTwo,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.smul_apply, smul_eq_mul, s00, s01, s10, s11,
    e1, e2, e3, e4, intervalIntegral.integral_const_mul, i1, i2, i3]
  refine ⟨⟨by norm_num, ?_⟩, ?_, by norm_num⟩ <;>
    · field_simp
      linear_combination h3

/-- **Counterexample for the true `N = 2` Legendre matrix under the condition the proof of Theorem 3
of arXiv 2307.07538 actually uses.**  For `A = ⟨P_m, μ P_n⟩_μ`, `N = 2`, and `Δt = √3 Δx`, so
`Δt |σ_k| = Δx`, the scheme with `e₀ ∉ range V⁰` can increase the energy.  This is outside the
paper's `Δt ≤ Δx`. -/
theorem legendreTwo_not_energy_stable {Δx σ : ℝ} (hΔx : 0 < Δx) (hσ : 0 ≤ σ)
    (hsmall : σ * (√3 * Δx) ≤ 1 / 100) :
    IsEnergyIncreasingStep Δx (√3 * Δx) σ (momentMatrix (1 / 2) legendreTwo) Q₂
      ![1 / √3, -(1 / √3)] := by
  have h0 : √3 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  refine not_energy_stable_without_e₀ momentMatrix_legendreTwo (by positivity) hΔx ?_ hσ hsmall
  field_simp

end Legendre

end LeanDLRA.Literature.P2307_07538
