import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.Matrix.Projectors

/-!
# Energy stability of IMEX, IMEX-S and IMEX-S-BUG (arXiv 2602.12337, Sec. 3 and 4)

Li, Jiang, Zhang, Xiong, *Temporal-Stability-Enhanced and Energy-Stable Dynamical Low-Rank
Approximation for Multiscale Linear Kinetic Transport Equations*.  This module writes out the fully
discrete schemes of Sec. 3.2, 3.3 and 4.1 in `d` space dimensions (`Grid`, `Coeff`, the operators
`𝒜`, `𝒜*`, `ℋ`, `𝒥`, `ℬ`, `R`, `Π`, the inner products `⟨·,·⟩`, `⟨·,·⟩_w`, the energy `E_θ`, the
steps `Grid.IsIMEXStep`, `Grid.IsIMEXSStep`, `Grid.IsIMEXSBUGStep`) and proves the stability theory
of the paper for these schemes, not for an abstract core: Lemmas 3.1-3.3 (`Grid.lemma_3_1`,
`Grid.lemma_3_2`, `Grid.lemma_3_3`), the summation by parts `Grid.sbp_H_J`, Thm. 3.1
(`Grid.theorem_3_1`), Thm. 3.2 (`Grid.theorem_3_2`), Cor. 3.3 (`Grid.corollary_3_3`,
`Grid.corollary_3_3_diffusive`), Thm. 4.1 (`Grid.theorem_4_1`), their versions along trajectories,
and the zero-density constraint of Sec. 4.3 (`Grid.zero_moment_of_lam`, `Grid.zeroDensity_lStep`,
`Grid.zeroDensity_qr`).  `Grid.existsUnique_density`, `Grid.exists_imexStep`,
`Grid.exists_imexSStep`, `Grid.exists_imexSBUGStep` and `slab_cfl` show that the hypotheses hold for
all data.  The sibling module `LeanDLRA.Literature.Kinetic.P2602_12337b` treats Sec. 4.2 on a
one-dimensional grid; the abstract variant with the macro equation for the low-rank `G^{n+1}` is
`LeanDLRA.OpenProblems.Stability.macroMicro_galerkin_energy_le`.

## Differences from the paper

* **The proof of Thm. 4.1 in the paper has a gap, the theorem is true.**  The density of IMEX-S-BUG
  comes first, from the Schur complement built with `Gⁿ` (p. 16), so it satisfies the macro
  equation with the full-rank update `G* = R ((1/Δt) Gⁿ - (1/ε) 𝒜(Gⁿ) Π - (1/ε²) 𝒥(ρⁿ⁺¹))`, not
  with the low-rank `Gⁿ⁺¹`.  The paper's proof says that the remainder parallels Thm. 3.2 (p. 20),
  where the coupling terms cancel; here they leave `Δt ⟨𝒥(ρⁿ⁺¹), G* - Gⁿ⁺¹⟩_w`, which the paper does
  not treat. `Grid.schur_energy_core` is a
  different argument that covers this term, and with it the scheme as stated. Write
  `Λ = 1 + Δt σ^s/ε² + Δt σ^a`, `y = (Δt/ε²) 𝒥(ρⁿ⁺¹)`, `L = G̃ⁿ - (Δt/ε) 𝒜(G̃ⁿ) Π`, and `L₂` for the
  same expression in `N = Gⁿ - G̃ⁿ`.  Eliminating `G* = Λ⁻¹ (L + L₂ - y)` from the macro equation
  and using `⟨Λ Gⁿ⁺¹, Gⁿ⁺¹⟩_w ≤ ⟨Λ⁻¹ (L - y), L - y⟩_w` gives
  `|D_Ω|/ε² (‖ρⁿ⁺¹‖² - ‖ρⁿ‖²) + ⟨Λ Gⁿ⁺¹, Gⁿ⁺¹⟩_w ≤ ⟨Λ⁻¹ L, L⟩_w + ⟨Λ⁻¹ L₂, L₂⟩_w`, because the mixed
  term `2 ⟨Λ⁻¹ y, L₂⟩_w` is absorbed by `-⟨Λ⁻¹ y, y⟩_w`.  Then (3.11) is exactly what makes the
  explicit advection step bounded by `1 + (1 - θ) Δt σ₀/ε²` (`Grid.advection_bound`), and
  `‖G̃ⁿ‖_w² + ‖N‖_w² = ‖Gⁿ‖_w²`.  For `G̃ⁿ = Gⁿ` the same argument proves Thm. 3.2, so that
  Lemma 3.1 is needed only for Thm. 3.1, where the proof follows the paper.  The bases play no role:
  Thm. 4.1 holds for arbitrary orthonormal `X¹`, `V¹` with `1ᵀ M V¹ = 0`
  (`Grid.galerkin_energy`), of any size, so also for the augmented bases of Sec. 4.2.
* The paper does not print `𝒟^{(j),±}`.  Here they are the periodic one-sided differences of an
  arbitrary permutation `shift j` of the grid, with step `Δx_j`.  This covers all periodic Cartesian
  grids; `ρ` and `G` are on one index set, using `N_ρ = N_g`, as in the matrix notation of the
  paper.
* `∑ w_k = |D_Ω|` and `∑ w_k Ω_k^{(j)} = 0` are hypotheses (`Grid.sum_w`, `Grid.sum_w_Om`).  The
  paper uses them tacitly: they hold for its symmetric quadrature and they make `Gⁿ w = 0`
  invariant, which is derived here rather than assumed (only `G⁰ w = 0` is needed).
* `‖Ω‖_∞` is any bound `Ωmax`, `min_j Δx^{(j)}` any lower bound `hmin`, `C_A` any number `≥ 1`.  The
  conditions are weakest at the exact values and `C_A = 1`, which is the paper's case, so this
  contains the statements of the paper.  `C_A = 1` needs no property of `S_N`.
* The absorption `σ^a` may differ between the `ρ` and the `G` grid (`Coeff.sigAm`, `Coeff.sigA`).
* The steps K, L, S of the paper print `K`, `L`, `S` without a superscript inside `ℬ`.  They are
  read as `Kⁿ`, `Lⁿ`, `S̃ⁿ`, as in the proof of Thm. 4.1, which uses `𝒜(G̃ⁿ)`.  QR is used only
  through `X¹ᵀ X¹ = 1`, `K¹ = X¹ T`, so that rank-deficient `K¹` are covered.
* Not formalized: the low-rank scheme IMEX-BUG with explicit `ρⁿ` and the values `C_B^{(j)} = 1/2`,
  which are properties of the Chebyshev-Legendre quadrature.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

namespace LeanDLRA.Literature.P2602_12337

/-- The phase-space discretization of Sec. 3.2 in `d` space dimensions: a periodic spatial grid `ι`
with a shift per direction and the ordinates `μ` of an `S_N` quadrature. -/
structure Grid (d : ℕ) (ι μ : Type*) [Fintype μ] where
  /-- The periodic shift of the grid in direction `j`. -/
  shift : Fin d → Equiv.Perm ι
  /-- The mesh size `Δx^{(j)}`. -/
  dx : Fin d → ℝ
  dx_pos : ∀ j, 0 < dx j
  /-- The ordinates `Ω_k^{(j)}`. -/
  Om : Fin d → μ → ℝ
  /-- The quadrature weights `w_k`. -/
  w : μ → ℝ
  w_pos : ∀ k, 0 < w k
  /-- The measure `|D_Ω|`. -/
  DOm : ℝ
  DOm_pos : 0 < DOm
  /-- The quadrature integrates `1`. -/
  sum_w : ∑ k, w k = DOm
  /-- The quadrature integrates the odd moments `Ω^{(j)}` to zero. -/
  sum_w_Om : ∀ j, ∑ k, w k * Om j k = 0

/-- The scales and coefficients: `ε`, `Δt`, `σ₀ˢ`, the diagonal scattering `σ^s ≥ σ₀ˢ > 0` and the
diagonal absorption `σ^a ≥ 0` on the micro and macro grid. -/
structure Coeff (ι : Type*) where
  /-- The Knudsen number `ε`. -/
  eps : ℝ
  /-- The time step `Δt`. -/
  dt : ℝ
  /-- The lower bound `σ₀ˢ` of the scattering. -/
  sig0 : ℝ
  /-- The scattering `σ^s`. -/
  sigS : ι → ℝ
  /-- The absorption `σ^a` in the micro equation. -/
  sigA : ι → ℝ
  /-- The absorption `σ^a` in the macro equation. -/
  sigAm : ι → ℝ
  eps_pos : 0 < eps
  dt_pos : 0 < dt
  sig0_pos : 0 < sig0
  sig0_le : ∀ i, sig0 ≤ sigS i
  sigA_nonneg : ∀ i, 0 ≤ sigA i
  sigAm_nonneg : ∀ i, 0 ≤ sigAm i

variable {d : ℕ} {ι μ : Type*} [Fintype ι] [DecidableEq ι] [Fintype μ] [DecidableEq μ]

namespace Coeff

variable (C : Coeff ι)

/-- The diagonal `Λ = 1 + Δt σ^s/ε² + Δt σ^a` of the implicit part of the micro equation. -/
noncomputable def lam (i : ι) : ℝ := 1 + C.dt * C.sigS i / C.eps ^ 2 + C.dt * C.sigA i

lemma one_add_le_lam (i : ι) : 1 + C.dt * C.sig0 / C.eps ^ 2 ≤ C.lam i := by
  have h1 := C.dt_pos
  have h2 := pow_pos C.eps_pos 2
  have h3 := C.sig0_le i
  have h4 := C.sigA_nonneg i
  have h5 : C.dt * C.sig0 / C.eps ^ 2 ≤ C.dt * C.sigS i / C.eps ^ 2 := by gcongr
  have h6 : 0 ≤ C.dt * C.sigA i := mul_nonneg h1.le h4
  rw [lam]
  linarith

lemma lam_pos (i : ι) : 0 < C.lam i := by
  have h1 := C.dt_pos
  have h2 := pow_pos C.eps_pos 2
  have h3 := C.sig0_pos
  have : 0 ≤ C.dt * C.sig0 / C.eps ^ 2 := by positivity
  linarith [C.one_add_le_lam i]

end Coeff

namespace Grid

variable (P : Grid d ι μ)

/-- The forward difference `𝒟^{(j),+}` of the periodic grid. -/
noncomputable def Dp (j : Fin d) : Matrix ι ι ℝ :=
  Matrix.of fun i i' =>
    ((if P.shift j i = i' then 1 else 0) - (if i = i' then 1 else 0)) / P.dx j

/-- The backward difference `𝒟^{(j),-}` of the periodic grid. -/
noncomputable def Dm (j : Fin d) : Matrix ι ι ℝ :=
  Matrix.of fun i i' =>
    ((if i = i' then 1 else 0) - (if (P.shift j).symm i = i' then 1 else 0)) / P.dx j

/-- `Q^{(j)} = diag(Ω_k^{(j)})`. -/
def Q (j : Fin d) : Matrix μ μ ℝ := Matrix.diagonal (P.Om j)

/-- `|Q^{(j)}|`. -/
noncomputable def absQ (j : Fin d) : Matrix μ μ ℝ := Matrix.diagonal fun k => |P.Om j k|

/-- `Q^{(j),+} = (Q^{(j)} + |Q^{(j)}|) / 2`. -/
noncomputable def Qp (j : Fin d) : Matrix μ μ ℝ := (1 / 2 : ℝ) • (P.Q j + P.absQ j)

/-- `Q^{(j),-} = (Q^{(j)} - |Q^{(j)}|) / 2`. -/
noncomputable def Qm (j : Fin d) : Matrix μ μ ℝ := (1 / 2 : ℝ) • (P.Q j - P.absQ j)

/-- `M = diag(√w_k)`. -/
noncomputable def M : Matrix μ μ ℝ := Matrix.diagonal fun k => √(P.w k)

/-- `M⁻¹`. -/
noncomputable def Minv : Matrix μ μ ℝ := Matrix.diagonal fun k => (√(P.w k))⁻¹

/-- The projector `Π = I - |D_Ω|⁻¹ w 1ᵀ` that removes the angular average. -/
noncomputable def Pi : Matrix μ μ ℝ :=
  1 - (1 / P.DOm) • Matrix.vecMulVec P.w (fun _ => (1 : ℝ))

/-- The upwind operator `𝒜(G) = ∑_j (𝒟^{(j),-} G Q^{(j),+} + 𝒟^{(j),+} G Q^{(j),-})`. -/
noncomputable def A (G : Matrix ι μ ℝ) : Matrix ι μ ℝ :=
  ∑ j, (P.Dm j * G * P.Qp j + P.Dp j * G * P.Qm j)

/-- The adjoint `𝒜*(G) = -∑_j (𝒟^{(j),-} G Q^{(j),-} + 𝒟^{(j),+} G Q^{(j),+})`. -/
noncomputable def Astar (G : Matrix ι μ ℝ) : Matrix ι μ ℝ :=
  -∑ j, (P.Dm j * G * P.Qm j + P.Dp j * G * P.Qp j)

/-- The macro flux `ℋ(G) = |D_Ω|⁻¹ ∑_j 𝒟^{(j),-} G Q^{(j)} w`. -/
noncomputable def H (G : Matrix ι μ ℝ) : ι → ℝ :=
  (1 / P.DOm) • ∑ j, (P.Dm j).mulVec ((G * P.Q j).mulVec P.w)

/-- The density gradient `𝒥(ρ) = ∑_j 𝒟^{(j),+} ρ 1ᵀ Q^{(j)}`. -/
noncomputable def J (ρ : ι → ℝ) : Matrix ι μ ℝ :=
  ∑ j, Matrix.vecMulVec ((P.Dp j).mulVec ρ) (Matrix.vecMul (fun _ => (1 : ℝ)) (P.Q j))

/-- The cell volume `∏_j Δx^{(j)}`. -/
noncomputable def vol : ℝ := ∏ j, P.dx j

/-- `⟨f₁, f₂⟩ = (∏_j Δx^{(j)}) f₁ᵀ f₂`. -/
noncomputable def ipv (f₁ f₂ : ι → ℝ) : ℝ := P.vol * (f₁ ⬝ᵥ f₂)

/-- `⟨F₁, F₂⟩_w = (∏_j Δx^{(j)}) Tr(F₁ M² F₂ᵀ)`. -/
noncomputable def ipw (F₁ F₂ : Matrix ι μ ℝ) : ℝ :=
  P.vol * Matrix.trace (F₁ * (P.M * P.M) * F₂ᵀ)

/-- Definition 3.1: `E_θ = |D_Ω| ‖ρ‖² + ε² ‖G‖_w² + (1 - θ) Δt σ₀ˢ ‖G‖_w²`. -/
noncomputable def energy (C : Coeff ι) (θ : ℝ) (ρ : ι → ℝ) (G : Matrix ι μ ℝ) : ℝ :=
  P.DOm * P.ipv ρ ρ + C.eps ^ 2 * P.ipw G G + (1 - θ) * C.dt * C.sig0 * P.ipw G G

/-! entries -/

section entries

variable {κ : Type*} [Fintype κ]

lemma Dp_mul_apply (j : Fin d) (G : Matrix ι κ ℝ) (i : ι) (k : κ) :
    (P.Dp j * G) i k = (G (P.shift j i) k - G i k) / P.dx j := by
  rw [Matrix.mul_apply]
  have h : ∀ x, P.Dp j i x * G x k =
      ((if P.shift j i = x then G x k else 0) - (if i = x then G x k else 0)) / P.dx j := by
    intro x
    simp only [Dp, Matrix.of_apply]
    split_ifs <;> ring
  simp only [h, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]

lemma Dm_mul_apply (j : Fin d) (G : Matrix ι κ ℝ) (i : ι) (k : κ) :
    (P.Dm j * G) i k = (G i k - G ((P.shift j).symm i) k) / P.dx j := by
  rw [Matrix.mul_apply]
  have h : ∀ x, P.Dm j i x * G x k =
      ((if i = x then G x k else 0) - (if (P.shift j).symm i = x then G x k else 0)) / P.dx j := by
    intro x
    simp only [Dm, Matrix.of_apply]
    split_ifs <;> ring
  simp only [h, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]

end entries

lemma Dp_mulVec_apply (j : Fin d) (f : ι → ℝ) (i : ι) :
    (P.Dp j).mulVec f i = (f (P.shift j i) - f i) / P.dx j := by
  simp only [Matrix.mulVec, dotProduct]
  have h : ∀ x, P.Dp j i x * f x =
      ((if P.shift j i = x then f x else 0) - (if i = x then f x else 0)) / P.dx j := by
    intro x
    simp only [Dp, Matrix.of_apply]
    split_ifs <;> ring
  simp only [h, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]

lemma Dm_mulVec_apply (j : Fin d) (f : ι → ℝ) (i : ι) :
    (P.Dm j).mulVec f i = (f i - f ((P.shift j).symm i)) / P.dx j := by
  simp only [Matrix.mulVec, dotProduct]
  have h : ∀ x, P.Dm j i x * f x =
      ((if i = x then f x else 0) - (if (P.shift j).symm i = x then f x else 0)) / P.dx j := by
    intro x
    simp only [Dm, Matrix.of_apply]
    split_ifs <;> ring
  simp only [h, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]

lemma Q_eq (j : Fin d) : P.Q j = Matrix.diagonal (P.Om j) := rfl

lemma Qp_eq (j : Fin d) : P.Qp j = Matrix.diagonal fun k => (P.Om j k + |P.Om j k|) / 2 := by
  ext k l
  by_cases h : k = l
  · subst h; simp [Qp, Q, absQ]; ring
  · simp [Qp, Q, absQ, h]

lemma Qm_eq (j : Fin d) : P.Qm j = Matrix.diagonal fun k => (P.Om j k - |P.Om j k|) / 2 := by
  ext k l
  by_cases h : k = l
  · subst h; simp [Qm, Q, absQ]; ring
  · simp [Qm, Q, absQ, h]

lemma M_mul_M : P.M * P.M = Matrix.diagonal P.w := by
  simp only [M, Matrix.diagonal_mul_diagonal]
  congr 1; ext k
  exact Real.mul_self_sqrt (P.w_pos k).le

lemma ipw_apply (F₁ F₂ : Matrix ι μ ℝ) :
    P.ipw F₁ F₂ = P.vol * ∑ i, ∑ k, F₁ i k * P.w k * F₂ i k := by
  simp only [ipw, M_mul_M, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.transpose_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [hb]
  · simp

lemma ipv_apply (f₁ f₂ : ι → ℝ) : P.ipv f₁ f₂ = P.vol * ∑ i, f₁ i * f₂ i := rfl

lemma vol_pos : 0 < P.vol := Finset.prod_pos fun j _ => P.dx_pos j


/-! bilinearity -/

lemma ipw_add_left (F₁ F₂ F₃ : Matrix ι μ ℝ) :
    P.ipw (F₁ + F₂) F₃ = P.ipw F₁ F₃ + P.ipw F₂ F₃ := by
  simp only [ipw_apply, Matrix.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

lemma ipw_comm (F₁ F₂ : Matrix ι μ ℝ) : P.ipw F₁ F₂ = P.ipw F₂ F₁ := by
  simp only [ipw_apply]
  congr 1
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

lemma ipw_smul_left (c : ℝ) (F₁ F₂ : Matrix ι μ ℝ) :
    P.ipw (c • F₁) F₂ = c * P.ipw F₁ F₂ := by
  simp only [ipw_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

lemma ipw_neg_left (F₁ F₂ : Matrix ι μ ℝ) : P.ipw (-F₁) F₂ = -P.ipw F₁ F₂ := by
  have := P.ipw_smul_left (-1) F₁ F₂
  simpa using this

lemma ipw_sub_left (F₁ F₂ F₃ : Matrix ι μ ℝ) :
    P.ipw (F₁ - F₂) F₃ = P.ipw F₁ F₃ - P.ipw F₂ F₃ := by
  rw [sub_eq_add_neg, ipw_add_left, ipw_neg_left]; ring

lemma ipw_add_right (F₁ F₂ F₃ : Matrix ι μ ℝ) :
    P.ipw F₁ (F₂ + F₃) = P.ipw F₁ F₂ + P.ipw F₁ F₃ := by
  rw [ipw_comm, ipw_add_left, P.ipw_comm F₂, P.ipw_comm F₃]

lemma ipw_smul_right (c : ℝ) (F₁ F₂ : Matrix ι μ ℝ) :
    P.ipw F₁ (c • F₂) = c * P.ipw F₁ F₂ := by
  rw [ipw_comm, ipw_smul_left, ipw_comm]

lemma ipw_sub_right (F₁ F₂ F₃ : Matrix ι μ ℝ) :
    P.ipw F₁ (F₂ - F₃) = P.ipw F₁ F₂ - P.ipw F₁ F₃ := by
  rw [ipw_comm, ipw_sub_left, P.ipw_comm F₂, P.ipw_comm F₃]

lemma ipw_sum_left {κ : Type*} (s : Finset κ) (B : κ → Matrix ι μ ℝ) (F : Matrix ι μ ℝ) :
    P.ipw (∑ j ∈ s, B j) F = ∑ j ∈ s, P.ipw (B j) F := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ipw_apply]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ipw_add_left, ih]

lemma ipw_self_nonneg (F : Matrix ι μ ℝ) : 0 ≤ P.ipw F F := by
  rw [ipw_apply]
  refine mul_nonneg P.vol_pos.le (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => ?_)
  have := P.w_pos k
  nlinarith [mul_nonneg this.le (mul_self_nonneg (F i k))]

/-- Young's inequality for the weighted inner product. -/
lemma two_mul_ipw_le (F₁ F₂ : Matrix ι μ ℝ) :
    2 * P.ipw F₁ F₂ ≤ P.ipw F₁ F₁ + P.ipw F₂ F₂ := by
  have := P.ipw_self_nonneg (F₁ - F₂)
  simp only [ipw_sub_left, ipw_sub_right, P.ipw_comm F₂ F₁] at this
  linarith

lemma ipw_dg_left (c : ι → ℝ) (F₁ F₂ : Matrix ι μ ℝ) :
    P.ipw (Matrix.diagonal c * F₁) F₂ = P.vol * ∑ i, c i * ∑ k, F₁ i k * P.w k * F₂ i k := by
  rw [ipw_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diagonal_mul]
  ring

lemma ipw_dg_comm (c : ι → ℝ) (F₁ F₂ : Matrix ι μ ℝ) :
    P.ipw (Matrix.diagonal c * F₁) F₂ = P.ipw F₁ (Matrix.diagonal c * F₂) := by
  rw [ipw_dg_left, P.ipw_comm F₁, ipw_dg_left]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring

lemma ipw_dg_nonneg {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) (F : Matrix ι μ ℝ) :
    0 ≤ P.ipw (Matrix.diagonal c * F) F := by
  rw [ipw_dg_left]
  refine mul_nonneg P.vol_pos.le (Finset.sum_nonneg fun i _ => mul_nonneg (hc i) ?_)
  refine Finset.sum_nonneg fun k _ => ?_
  have := P.w_pos k
  nlinarith [mul_nonneg this.le (mul_self_nonneg (F i k))]

lemma ipw_dg_const (t : ℝ) (F₁ F₂ : Matrix ι μ ℝ) :
    P.ipw (Matrix.diagonal (fun _ : ι => t) * F₁) F₂ = t * P.ipw F₁ F₂ := by
  rw [ipw_dg_left, ipw_apply, ← Finset.mul_sum, mul_left_comm]

lemma ipw_dg_sub_nonneg {c c' : ι → ℝ} (h : ∀ i, c i ≤ c' i) (F : Matrix ι μ ℝ) :
    P.ipw (Matrix.diagonal c * F) F ≤ P.ipw (Matrix.diagonal c' * F) F := by
  have h' := P.ipw_dg_nonneg (c := fun i => c' i - c i) (fun i => sub_nonneg.2 (h i)) F
  rw [ipw_dg_left] at h'
  rw [ipw_dg_left, ipw_dg_left]
  have e : ∑ i, (c' i - c i) * ∑ k, F i k * P.w k * F i k =
      ∑ i, c' i * ∑ k, F i k * P.w k * F i k - ∑ i, c i * ∑ k, F i k * P.w k * F i k := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e] at h'
  nlinarith [P.vol_pos]

/-! summation by parts -/

lemma sum_comp_symm (τ : Equiv.Perm ι) (f : ι → ℝ) : ∑ i, f (τ.symm i) = ∑ i, f i :=
  Equiv.sum_comp τ.symm f

lemma sum_comp (τ : Equiv.Perm ι) (f : ι → ℝ) : ∑ i, f (τ i) = ∑ i, f i :=
  Equiv.sum_comp τ f

lemma sum_shift_mul (τ : Equiv.Perm ι) (u v : ι → ℝ) :
    ∑ i, u (τ.symm i) * v i = ∑ i, u i * v (τ i) := by
  rw [← sum_comp τ]
  simp

lemma ipw_Dm (j : Fin d) (q : μ → ℝ) (F₁ F₂ : Matrix ι μ ℝ) :
    P.ipw (P.Dm j * F₁ * Matrix.diagonal q) F₂ = -P.ipw F₁ (P.Dp j * F₂ * Matrix.diagonal q) := by
  simp only [ipw_apply, Matrix.mul_diagonal, Dm_mul_apply, Dp_mul_apply]
  have L : ∀ f : ι → μ → ℝ, ∑ i, ∑ k, f i k = ∑ k, ∑ i, f i k := fun f => Finset.sum_comm
  rw [← mul_neg, L, L, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have h := sum_shift_mul (P.shift j) (fun i => F₁ i k) (fun i => F₂ i k)
  have e1 : ∑ i, (F₁ i k - F₁ ((P.shift j).symm i) k) / P.dx j * q k * P.w k * F₂ i k =
      q k * P.w k / P.dx j * (∑ i, F₁ i k * F₂ i k - ∑ i, F₁ ((P.shift j).symm i) k * F₂ i k) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, F₁ i k * P.w k * ((F₂ (P.shift j i) k - F₂ i k) / P.dx j * q k) =
      q k * P.w k / P.dx j * (∑ i, F₁ i k * F₂ (P.shift j i) k - ∑ i, F₁ i k * F₂ i k) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2, h]
  ring

lemma ipw_Dp (j : Fin d) (q : μ → ℝ) (F₁ F₂ : Matrix ι μ ℝ) :
    P.ipw (P.Dp j * F₁ * Matrix.diagonal q) F₂ = -P.ipw F₁ (P.Dm j * F₂ * Matrix.diagonal q) := by
  rw [ipw_comm, P.ipw_comm F₁, ipw_Dm, neg_neg]

lemma ipw_A_adj (F₁ F₂ : Matrix ι μ ℝ) : P.ipw (P.A F₁) F₂ = P.ipw F₁ (P.Astar F₂) := by
  simp only [A, Astar, ipw_sum_left, ipw_add_left]
  rw [P.ipw_comm F₁, ← neg_one_smul ℝ (∑ j, _), ipw_smul_left, ipw_sum_left, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Qp_eq, Qm_eq, ipw_Dm, ipw_Dp, ipw_add_left, P.ipw_comm F₁, P.ipw_comm F₁]
  ring

lemma sum_shift_sub_sq (τ : Equiv.Perm ι) (u : ι → ℝ) :
    ∑ i, (u (τ i) - u i) ^ 2 = 2 * ∑ i, u i ^ 2 - 2 * ∑ i, u (τ i) * u i := by
  have h := sum_comp τ (fun i => u i ^ 2)
  have e : ∑ i, (u (τ i) - u i) ^ 2 =
      ∑ i, u (τ i) ^ 2 + ∑ i, u i ^ 2 - 2 * ∑ i, u (τ i) * u i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, h]; ring

/-- Upwind dissipation of one direction: the core of Lemma 3.1. -/
lemma ipw_upwind_self (j : Fin d) (F : Matrix ι μ ℝ) :
    P.ipw (P.Dm j * F * P.Qp j + P.Dp j * F * P.Qm j) F =
      P.dx j / 2 * P.ipw (P.Dp j * F * P.absQ j) (P.Dp j * F) := by
  have hdx := (P.dx_pos j).ne'
  have L : ∀ f : ι → μ → ℝ, ∑ i, ∑ k, f i k = ∑ k, ∑ i, f i k := fun f => Finset.sum_comm
  simp only [ipw_apply, Qp_eq, Qm_eq, absQ, Matrix.add_apply, Matrix.mul_diagonal, Dm_mul_apply,
    Dp_mul_apply]
  rw [L, L, mul_left_comm (P.dx j / 2), Finset.mul_sum _ _ (P.dx j / 2)]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : ∑ i, F ((P.shift j).symm i) k * F i k = ∑ i, F i k * F (P.shift j i) k :=
    sum_shift_mul (P.shift j) (fun i => F i k) (fun i => F i k)
  have h2 : ∑ i, (F (P.shift j i) k - F i k) ^ 2 =
      2 * ∑ i, F i k ^ 2 - 2 * ∑ i, F (P.shift j i) k * F i k :=
    sum_shift_sub_sq (P.shift j) (fun i => F i k)
  have hc : ∑ i, F i k * F (P.shift j i) k = ∑ i, F (P.shift j i) k * F i k :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hs : ∑ i, F i k * F i k = ∑ i, F i k ^ 2 :=
    Finset.sum_congr rfl fun i _ => (sq _).symm
  set q := P.Om j k
  set a := P.w k
  have e1 : ∑ i, ((F i k - F ((P.shift j).symm i) k) / P.dx j * ((q + |q|) / 2) +
        (F (P.shift j i) k - F i k) / P.dx j * ((q - |q|) / 2)) * a * F i k =
      a / P.dx j * (((q + |q|) / 2) * (∑ i, F i k * F i k -
          ∑ i, F ((P.shift j).symm i) k * F i k) +
        ((q - |q|) / 2) * (∑ i, F (P.shift j i) k * F i k - ∑ i, F i k * F i k)) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, (F (P.shift j i) k - F i k) / P.dx j * |q| * a *
        ((F (P.shift j i) k - F i k) / P.dx j) =
      |q| * a / P.dx j ^ 2 * ∑ i, (F (P.shift j i) k - F i k) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2, h2, h1, hc, hs]
  field_simp
  ring

/-- The upwind dissipation `∑_j (Δx^{(j)}/2) ⟨𝒟^{(j),+} F |Q^{(j)}|, 𝒟^{(j),+} F⟩_w`. -/
noncomputable def dis (F : Matrix ι μ ℝ) : ℝ :=
  ∑ j, P.dx j / 2 * P.ipw (P.Dp j * F * P.absQ j) (P.Dp j * F)

lemma ipw_A_self (F : Matrix ι μ ℝ) : P.ipw (P.A F) F = P.dis F := by
  simp only [A, ipw_sum_left, dis, ipw_upwind_self]

/-- **Lemma 3.1** (arXiv 2602.12337).  The summation-by-parts identity
`⟨𝒜(Gⁿ), Gⁿ⁺¹⟩_w = ∑_j (Δx^{(j)}/2) ⟨𝒟^{(j),+} Gⁿ⁺¹ |Q^{(j)}|, 𝒟^{(j),+} Gⁿ⁺¹⟩_w
- ⟨𝒜*(Gⁿ⁺¹), Gⁿ⁺¹ - Gⁿ⟩_w`, for arbitrary `Gⁿ`, `Gⁿ⁺¹`.  The difference operators are those of the
periodic grid `Grid`, which the paper does not print. -/
theorem lemma_3_1 (G G' : Matrix ι μ ℝ) :
    P.ipw (P.A G) G' =
      ∑ j, P.dx j / 2 * P.ipw (P.Dp j * G' * P.absQ j) (P.Dp j * G') -
        P.ipw (P.Astar G') (G' - G) := by
  have h1 := P.ipw_A_adj G G'
  have h2 := P.ipw_A_adj G' G'
  have h3 := P.ipw_A_self G'
  rw [ipw_sub_right, P.ipw_comm (P.Astar G') G', P.ipw_comm (P.Astar G') G, ← h1, ← h2, h3]
  simp [dis]

/-- The squared `ℓ²` norm of column `k` of `D^{(j),+} F`. -/
noncomputable def nrm (F : Matrix ι μ ℝ) (j : Fin d) (k : μ) : ℝ :=
  ∑ i, ((P.Dp j * F) i k) ^ 2

lemma nrm_nonneg (F : Matrix ι μ ℝ) (j : Fin d) (k : μ) : 0 ≤ P.nrm F j k :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma sum_Dm_sq (F : Matrix ι μ ℝ) (j : Fin d) (k : μ) :
    ∑ i, ((P.Dm j * F) i k) ^ 2 = P.nrm F j k := by
  rw [nrm, ← sum_comp_symm (P.shift j) (fun i => ((P.Dp j * F) i k) ^ 2)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Dm_mul_apply, Dp_mul_apply]

lemma nrm_le (F : Matrix ι μ ℝ) (j : Fin d) (k : μ) :
    P.nrm F j k ≤ 4 / P.dx j ^ 2 * ∑ i, F i k ^ 2 := by
  have hdx := P.dx_pos j
  have h := sum_comp (P.shift j) (fun i => F i k ^ 2)
  have e : P.nrm F j k = 1 / P.dx j ^ 2 * ∑ i, (F (P.shift j i) k - F i k) ^ 2 := by
    rw [nrm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Dp_mul_apply]
    field_simp
  have hle : ∑ i, (F (P.shift j i) k - F i k) ^ 2 ≤ 4 * ∑ i, F i k ^ 2 := by
    have : ∑ i, (F (P.shift j i) k - F i k) ^ 2 ≤
        2 * ∑ i, F (P.shift j i) k ^ 2 + 2 * ∑ i, F i k ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (F (P.shift j i) k + F i k)]
    rw [h] at this
    linarith
  rw [e]
  calc 1 / P.dx j ^ 2 * ∑ i, (F (P.shift j i) k - F i k) ^ 2
      ≤ 1 / P.dx j ^ 2 * (4 * ∑ i, F i k ^ 2) := by gcongr
    _ = 4 / P.dx j ^ 2 * ∑ i, F i k ^ 2 := by ring

lemma ipw_combo (j : Fin d) {c₁ c₂ : μ → ℝ} (hc : ∀ k, c₁ k * c₂ k = 0) (F : Matrix ι μ ℝ) :
    P.ipw (P.Dm j * F * Matrix.diagonal c₁ + P.Dp j * F * Matrix.diagonal c₂)
        (P.Dm j * F * Matrix.diagonal c₁ + P.Dp j * F * Matrix.diagonal c₂) =
      P.vol * ∑ k, P.w k * (c₁ k ^ 2 + c₂ k ^ 2) * P.nrm F j k := by
  have L : ∀ f : ι → μ → ℝ, ∑ i, ∑ k, f i k = ∑ k, ∑ i, f i k := fun f => Finset.sum_comm
  simp only [ipw_apply, Matrix.add_apply, Matrix.mul_diagonal]
  rw [L]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 := P.sum_Dm_sq F j k
  have e : ∑ i, ((P.Dm j * F) i k * c₁ k + (P.Dp j * F) i k * c₂ k) * P.w k *
        ((P.Dm j * F) i k * c₁ k + (P.Dp j * F) i k * c₂ k) =
      P.w k * (c₁ k ^ 2 * ∑ i, ((P.Dm j * F) i k) ^ 2 + c₂ k ^ 2 * P.nrm F j k) := by
    rw [nrm, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hc k
    linear_combination (2 * P.w k * (P.Dm j * F) i k * (P.Dp j * F) i k) * this
  rw [e, h1]
  ring

lemma ipw_abs_abs (j : Fin d) (F : Matrix ι μ ℝ) :
    P.ipw (P.Dp j * F * P.absQ j) (P.Dp j * F * P.absQ j) =
      P.vol * ∑ k, P.w k * P.Om j k ^ 2 * P.nrm F j k := by
  have L : ∀ f : ι → μ → ℝ, ∑ i, ∑ k, f i k = ∑ k, ∑ i, f i k := fun f => Finset.sum_comm
  simp only [ipw_apply, absQ, Matrix.mul_diagonal]
  rw [L]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [nrm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : |P.Om j k| * |P.Om j k| = P.Om j k ^ 2 := by rw [← sq, sq_abs]
  linear_combination ((P.Dp j * F) i k) ^ 2 * P.w k * this

lemma ipw_abs (j : Fin d) (F : Matrix ι μ ℝ) :
    P.ipw (P.Dp j * F * P.absQ j) (P.Dp j * F) =
      P.vol * ∑ k, P.w k * |P.Om j k| * P.nrm F j k := by
  have L : ∀ f : ι → μ → ℝ, ∑ i, ∑ k, f i k = ∑ k, ∑ i, f i k := fun f => Finset.sum_comm
  simp only [ipw_apply, absQ, Matrix.mul_diagonal]
  rw [L]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [nrm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma ipw_Dp_self (j : Fin d) (F : Matrix ι μ ℝ) :
    P.ipw (P.Dp j * F) (P.Dp j * F) = P.vol * ∑ k, P.w k * P.nrm F j k := by
  have L : ∀ f : ι → μ → ℝ, ∑ i, ∑ k, f i k = ∑ k, ∑ i, f i k := fun f => Finset.sum_comm
  simp only [ipw_apply]
  rw [L]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [nrm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma ipw_self_eq (F : Matrix ι μ ℝ) :
    P.ipw F F = P.vol * ∑ k, P.w k * ∑ i, F i k ^ 2 := by
  have L : ∀ f : ι → μ → ℝ, ∑ i, ∑ k, f i k = ∑ k, ∑ i, f i k := fun f => Finset.sum_comm
  simp only [ipw_apply]
  rw [L]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `‖D^{(j),+} F‖_w² ≤ (4 / Δx_j²) ‖F‖_w²`. -/
lemma ipw_Dp_self_le (j : Fin d) (F : Matrix ι μ ℝ) :
    P.ipw (P.Dp j * F) (P.Dp j * F) ≤ 4 / P.dx j ^ 2 * P.ipw F F := by
  rw [ipw_Dp_self, ipw_self_eq, mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ P.vol_pos.le
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have := P.nrm_le F j k
  have hw := P.w_pos k
  calc P.w k * P.nrm F j k ≤ P.w k * (4 / P.dx j ^ 2 * ∑ i, F i k ^ 2) := by gcongr
    _ = 4 / P.dx j ^ 2 * (P.w k * ∑ i, F i k ^ 2) := by ring

lemma ipw_sum_sq_le (B : Fin d → Matrix ι μ ℝ) :
    P.ipw (∑ j, B j) (∑ j, B j) ≤ d * ∑ j, P.ipw (B j) (B j) := by
  simp only [ipw_apply, Matrix.sum_apply]
  rw [← Finset.mul_sum, mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ P.vol_pos.le
  have L : ∀ f : Fin d → ι → μ → ℝ, ∑ j, ∑ i, ∑ k, f j i k = ∑ i, ∑ k, ∑ j, f j i k := by
    intro f
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [L, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => B j i k)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  have hw := P.w_pos k
  calc (∑ j, B j i k) * P.w k * ∑ j, B j i k = P.w k * (∑ j, B j i k) ^ 2 := by ring
    _ ≤ P.w k * ((d : ℝ) * ∑ j, B j i k ^ 2) := by gcongr
    _ = (d : ℝ) * ∑ j, B j i k * P.w k * B j i k := by
        rw [mul_left_comm, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun j _ => by ring

/-- Lemma 3.2 with `C_A = 1`, for a generic zero-product pair of angular factors. -/
private lemma ipw_sum_combo_le {c₁ c₂ : Fin d → μ → ℝ} (hc : ∀ j k, c₁ j k * c₂ j k = 0)
    (hsq : ∀ j k, c₁ j k ^ 2 + c₂ j k ^ 2 = P.Om j k ^ 2) (F : Matrix ι μ ℝ) :
    P.ipw (∑ j, (P.Dm j * F * Matrix.diagonal (c₁ j) + P.Dp j * F * Matrix.diagonal (c₂ j)))
        (∑ j, (P.Dm j * F * Matrix.diagonal (c₁ j) + P.Dp j * F * Matrix.diagonal (c₂ j))) ≤
      d * ∑ j, P.ipw (P.Dp j * F * P.absQ j) (P.Dp j * F * P.absQ j) := by
  refine (P.ipw_sum_sq_le _).trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ipw_combo _ _ (hc j), ipw_abs_abs]
  simp only [hsq]

private lemma qp_mul_qm (q : ℝ) : (q + |q|) / 2 * ((q - |q|) / 2) = 0 := by
  have : |q| * |q| = q * q := abs_mul_abs_self q
  linear_combination (-1 / 4 : ℝ) * this

private lemma qp_sq_add_qm_sq (q : ℝ) : ((q + |q|) / 2) ^ 2 + ((q - |q|) / 2) ^ 2 = q ^ 2 := by
  have : |q| * |q| = q * q := abs_mul_abs_self q
  linear_combination (1 / 2 : ℝ) * this

/-- The bound of Lemma 3.2 for `A` itself. -/
lemma ipw_A_A_le (F : Matrix ι μ ℝ) :
    P.ipw (P.A F) (P.A F) ≤
      d * ∑ j, P.ipw (P.Dp j * F * P.absQ j) (P.Dp j * F * P.absQ j) := by
  simp only [A, Qp_eq, Qm_eq]
  exact P.ipw_sum_combo_le (fun j k => qp_mul_qm _) (fun j k => qp_sq_add_qm_sq _) F

/-- **Lemma 3.2** (arXiv 2602.12337).  `‖𝒜*(G)‖_w² ≤ C_A d ∑_j ‖𝒟^{(j),+} G |Q^{(j)}|‖_w²`.
The paper has `C_A = 1` for `S_N`; this holds for every `C_A ≥ 1` and needs no property of the
quadrature. -/
theorem lemma_3_2 {CA : ℝ} (hCA : 1 ≤ CA) (G : Matrix ι μ ℝ) :
    P.ipw (P.Astar G) (P.Astar G) ≤
      CA * d * ∑ j, P.ipw (P.Dp j * G * P.absQ j) (P.Dp j * G * P.absQ j) := by
  have h : P.ipw (P.Astar G) (P.Astar G) ≤
      d * ∑ j, P.ipw (P.Dp j * G * P.absQ j) (P.Dp j * G * P.absQ j) := by
    simp only [Astar, Qp_eq, Qm_eq]
    have e : ∀ X : Matrix ι μ ℝ, P.ipw (-X) (-X) = P.ipw X X := by
      intro X
      rw [ipw_neg_left, P.ipw_comm X (-X), ipw_neg_left, neg_neg]
    rw [e]
    exact P.ipw_sum_combo_le (fun j k => by rw [mul_comm]; exact qp_mul_qm _)
      (fun j k => by rw [add_comm]; exact qp_sq_add_qm_sq _) G
  have hnn : 0 ≤ (d : ℝ) * ∑ j, P.ipw (P.Dp j * G * P.absQ j) (P.Dp j * G * P.absQ j) :=
    mul_nonneg (Nat.cast_nonneg d) (Finset.sum_nonneg fun j _ => P.ipw_self_nonneg _)
  nlinarith

/-! ### Flux operators -/

lemma J_apply (ρ : ι → ℝ) (i : ι) (k : μ) :
    P.J ρ i k = ∑ j, (P.Dp j).mulVec ρ i * P.Om j k := by
  simp [J, Matrix.sum_apply, Matrix.vecMulVec_apply, Q, Matrix.vecMul_diagonal]

lemma flux_apply (G : Matrix ι μ ℝ) (j : Fin d) (i : ι) :
    (G * P.Q j).mulVec P.w i = ∑ k, G i k * P.Om j k * P.w k := by
  simp [Matrix.mulVec, dotProduct, Q, Matrix.mul_diagonal]

lemma H_apply (G : Matrix ι μ ℝ) (i : ι) :
    P.H G i = 1 / P.DOm * ∑ j, (P.Dm j).mulVec ((G * P.Q j).mulVec P.w) i := by
  simp [H, Finset.sum_apply]

lemma H_add (G₁ G₂ : Matrix ι μ ℝ) : P.H (G₁ + G₂) = P.H G₁ + P.H G₂ := by
  simp only [H, Matrix.add_mul, Matrix.add_mulVec, Matrix.mulVec_add, Finset.sum_add_distrib,
    smul_add]

lemma H_smul (c : ℝ) (G : Matrix ι μ ℝ) : P.H (c • G) = c • P.H G := by
  simp only [H, Matrix.smul_mul, Matrix.smul_mulVec, Matrix.mulVec_smul, ← Finset.smul_sum]
  rw [smul_comm]

lemma H_sub (G₁ G₂ : Matrix ι μ ℝ) : P.H (G₁ - G₂) = P.H G₁ - P.H G₂ := by
  have h := P.H_smul (-1) G₂
  rw [sub_eq_add_neg, ← neg_one_smul ℝ G₂, H_add, h, neg_one_smul, sub_eq_add_neg]

lemma sum_Dp_mul (j : Fin d) (f g : ι → ℝ) :
    ∑ i, (P.Dp j).mulVec f i * g i = -∑ i, f i * (P.Dm j).mulVec g i := by
  simp only [Dp_mulVec_apply, Dm_mulVec_apply]
  have h := sum_shift_mul (P.shift j) g f
  have h' : ∑ i, f i * g ((P.shift j).symm i) = ∑ i, f (P.shift j i) * g i := by
    rw [Finset.sum_congr rfl fun i _ => mul_comm (f i) _, h]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have e1 : ∑ i, (f (P.shift j i) - f i) / P.dx j * g i =
      (∑ i, f (P.shift j i) * g i - ∑ i, f i * g i) / P.dx j := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, f i * ((g i - g ((P.shift j).symm i)) / P.dx j) =
      (∑ i, f i * g i - ∑ i, f i * g ((P.shift j).symm i)) / P.dx j := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2, h']
  ring

/-- The summation by parts `|D_Ω| ⟨ρ, ℋ(G)⟩ = -⟨𝒥(ρ), G⟩_w` in the proof of Thm. 3.1 of
arXiv 2602.12337. -/
theorem sbp_H_J (ρ : ι → ℝ) (G : Matrix ι μ ℝ) :
    P.DOm * P.ipv ρ (P.H G) = -P.ipw (P.J ρ) G := by
  have hD := P.DOm_pos.ne'
  have e1 : P.DOm * P.ipv ρ (P.H G) =
      P.vol * ∑ j, ∑ i, ρ i * (P.Dm j).mulVec ((G * P.Q j).mulVec P.w) i := by
    rw [ipv_apply, mul_left_comm]
    congr 1
    rw [Finset.mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [H_apply, ← Finset.mul_sum]
    field_simp
  have e2 : P.ipw (P.J ρ) G =
      P.vol * ∑ j, ∑ i, (P.Dp j).mulVec ρ i * (G * P.Q j).mulVec P.w i := by
    have L : ∀ f : Fin d → ι → ℝ, ∑ j, ∑ i, f j i = ∑ i, ∑ j, f j i := fun f => Finset.sum_comm
    rw [ipw_apply, L]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [J_apply, flux_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2, ← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl fun j _ => (by rw [sum_Dp_mul, neg_neg])

/-- The quadrature Cauchy--Schwarz constant `C_B^{(j)} = |D_Ω|⁻¹ wᵀ |Ω^{(j)}| 1`. -/
noncomputable def Cb (j : Fin d) : ℝ := 1 / P.DOm * ∑ k, P.w k * |P.Om j k|

lemma Cb_nonneg (j : Fin d) : 0 ≤ P.Cb j :=
  mul_nonneg (by have := P.DOm_pos; positivity)
    (Finset.sum_nonneg fun k _ => mul_nonneg (P.w_pos k).le (abs_nonneg _))

lemma quad_cs (j : Fin d) (x : μ → ℝ) :
    (∑ k, x k * P.Om j k * P.w k) ^ 2 ≤
      (∑ k, P.w k * |P.Om j k|) * ∑ k, P.w k * |P.Om j k| * x k ^ 2 := by
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _
    (fun k _ => mul_nonneg (P.w_pos k).le (abs_nonneg _))
    (fun k _ => mul_nonneg (mul_nonneg (P.w_pos k).le (abs_nonneg _)) (sq_nonneg _))
    (fun k _ => le_of_eq ?_)
  have : |P.Om j k| * |P.Om j k| = P.Om j k * P.Om j k := abs_mul_abs_self _
  linear_combination (-(P.w k) ^ 2 * x k ^ 2) * this

/-- **Lemma 3.3** (arXiv 2602.12337).  `Q^{(j)} w wᵀ (Q^{(j)})ᵀ ≤ C_B^{(j)} |D_Ω| |Q^{(j)}| M²` in
the Loewner order, with `C_B^{(j)} = |D_Ω|⁻¹ wᵀ |Ω^{(j)}| 1`. -/
theorem lemma_3_3 (j : Fin d) :
    ((P.Cb j * P.DOm) • (P.absQ j * (P.M * P.M)) -
      Matrix.vecMulVec ((P.Q j).mulVec P.w) ((P.Q j).mulVec P.w)).PosSemidef := by
  have hD := P.DOm_pos.ne'
  have hentry : ∀ k l, ((P.Cb j * P.DOm) • (P.absQ j * (P.M * P.M)) -
      Matrix.vecMulVec ((P.Q j).mulVec P.w) ((P.Q j).mulVec P.w)) k l =
      (∑ m, P.w m * |P.Om j m|) * (if k = l then |P.Om j k| * P.w k else 0) -
        (P.Om j k * P.w k) * (P.Om j l * P.w l) := by
    intro k l
    have hc : P.Cb j * P.DOm = ∑ m, P.w m * |P.Om j m| := by
      rw [Cb]; field_simp
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, hc, M_mul_M, absQ,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, Matrix.vecMulVec_apply, Q,
      Matrix.mulVec_diagonal]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext k l
    rw [Matrix.conjTranspose_apply, star_trivial, hentry, hentry]
    by_cases h : k = l
    · subst h; ring
    · have h' : ¬ l = k := fun e => h e.symm
      simp only [h, h', ite_false]; ring
  · have h := P.quad_cs j x
    have e : star x ⬝ᵥ (((P.Cb j * P.DOm) • (P.absQ j * (P.M * P.M)) -
        Matrix.vecMulVec ((P.Q j).mulVec P.w) ((P.Q j).mulVec P.w)).mulVec x) =
        (∑ k, P.w k * |P.Om j k|) * ∑ k, P.w k * |P.Om j k| * x k ^ 2 -
          (∑ k, x k * P.Om j k * P.w k) ^ 2 := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, hentry]
      have : ∀ k, x k * ∑ l, ((∑ m, P.w m * |P.Om j m|) *
            (if k = l then |P.Om j k| * P.w k else 0) -
            (P.Om j k * P.w k) * (P.Om j l * P.w l)) * x l =
          (∑ m, P.w m * |P.Om j m|) * (P.w k * |P.Om j k| * x k ^ 2) -
            (x k * P.Om j k * P.w k) * ∑ l, x l * P.Om j l * P.w l := by
        intro k
        simp only [sub_mul, Finset.sum_sub_distrib, mul_ite, ite_mul, mul_zero, zero_mul,
          Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_sub, Finset.mul_sum]
        congr 1
        · ring
        · exact Finset.sum_congr rfl fun l _ => by ring
      simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, sq]
    rw [e]
    linarith

/-- `|D_Ω| ‖H(G)‖² ≤ d ∑_j C_B^{(j)} ⟨D^{(j),+} G |Q^{(j)}|, D^{(j),+} G⟩_w`. -/
lemma H_sq_le (G : Matrix ι μ ℝ) :
    P.DOm * P.ipv (P.H G) (P.H G) ≤
      d * ∑ j, P.Cb j * (P.vol * ∑ k, P.w k * |P.Om j k| * P.nrm G j k) := by
  have hD := P.DOm_pos
  have hvol := P.vol_pos
  set f : Fin d → ι → ℝ := fun j => (G * P.Q j).mulVec P.w with hf
  -- pointwise Cauchy--Schwarz in the angle
  have hDp : ∀ j i, (P.Dp j).mulVec (f j) i = ∑ k, (P.Dp j * G) i k * P.Om j k * P.w k := by
    intro j i
    rw [Dp_mulVec_apply]
    simp only [hf, flux_apply, Dp_mul_apply, ← Finset.sum_sub_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hshift : ∀ j, ∑ i, ((P.Dm j).mulVec (f j) i) ^ 2 = ∑ i, ((P.Dp j).mulVec (f j) i) ^ 2 := by
    intro j
    rw [← sum_comp (P.shift j) (fun i => ((P.Dm j).mulVec (f j) i) ^ 2)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Dm_mulVec_apply, Dp_mulVec_apply]
  have hcs : ∀ j, ∑ i, ((P.Dp j).mulVec (f j) i) ^ 2 ≤
      P.DOm * P.Cb j * ∑ k, P.w k * |P.Om j k| * P.nrm G j k := by
    intro j
    have hc : P.DOm * P.Cb j = ∑ m, P.w m * |P.Om j m| := by
      rw [Cb]; field_simp
    rw [hc]
    have e : ∑ k, P.w k * |P.Om j k| * P.nrm G j k =
        ∑ i, ∑ k, P.w k * |P.Om j k| * ((P.Dp j * G) i k) ^ 2 := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => by rw [nrm, Finset.mul_sum]
    rw [e, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hDp]
    exact P.quad_cs j _
  have hsum : ∑ i, (∑ j, (P.Dm j).mulVec (f j) i) ^ 2 ≤
      d * ∑ j, ∑ i, ((P.Dm j).mulVec (f j) i) ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun j => (P.Dm j).mulVec (f j) i)
    simpa only [Finset.card_univ, Fintype.card_fin] using h
  have e : P.DOm * P.ipv (P.H G) (P.H G) =
      P.vol / P.DOm * ∑ i, (∑ j, (P.Dm j).mulVec (f j) i) ^ 2 := by
    have hH : ∀ i, P.H G i * P.H G i = (1 / P.DOm) ^ 2 * (∑ j, (P.Dm j).mulVec (f j) i) ^ 2 := by
      intro i
      rw [H_apply]
      ring
    rw [ipv_apply, Finset.sum_congr rfl fun i _ => hH i, ← Finset.mul_sum]
    field_simp
  rw [e]
  have hA : 0 ≤ P.vol / P.DOm := by positivity
  calc P.vol / P.DOm * ∑ i, (∑ j, (P.Dm j).mulVec (f j) i) ^ 2
      ≤ P.vol / P.DOm * (d * ∑ j, ∑ i, ((P.Dm j).mulVec (f j) i) ^ 2) :=
        mul_le_mul_of_nonneg_left hsum hA
    _ ≤ P.vol / P.DOm *
        (d * ∑ j, P.DOm * P.Cb j * ∑ k, P.w k * |P.Om j k| * P.nrm G j k) := by
        refine mul_le_mul_of_nonneg_left ?_ hA
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg d)
        refine Finset.sum_le_sum fun j _ => ?_
        rw [hshift]
        exact hcs j
    _ = d * ∑ j, P.Cb j * (P.vol * ∑ k, P.w k * |P.Om j k| * P.nrm G j k) := by
        rw [mul_left_comm]
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        field_simp

/-! ### The projector `Π = I - |D_Ω|⁻¹ w 1ᵀ` -/

lemma Pi_mulVec_w : P.Pi.mulVec P.w = 0 := by
  have hD := P.DOm_pos.ne'
  ext k
  have e : (Matrix.vecMulVec P.w (fun _ => (1 : ℝ))).mulVec P.w k = P.w k * P.DOm := by
    simp [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, ← Finset.mul_sum, P.sum_w]
  simp only [Pi, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, e, Pi.zero_apply]
  field_simp
  ring

lemma mul_Pi_apply (Z : Matrix ι μ ℝ) (i : ι) (k : μ) :
    (Z * P.Pi) i k = Z i k - 1 / P.DOm * ∑ l, Z i l * P.w l := by
  rw [Pi, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.mul_apply]
  simp [Matrix.vecMulVec_apply]

lemma sum_mul_w_eq_zero {F : Matrix ι μ ℝ} (hF : F.mulVec P.w = 0) (i : ι) :
    ∑ k, F i k * P.w k = 0 := by
  have := congrFun hF i
  simpa [Matrix.mulVec, dotProduct] using this

lemma mul_Pi_of_zero {F : Matrix ι μ ℝ} (hF : F.mulVec P.w = 0) : F * P.Pi = F := by
  ext i k
  rw [mul_Pi_apply, P.sum_mul_w_eq_zero hF i]
  simp

lemma mul_Pi_mulVec_w (Z : Matrix ι μ ℝ) : (Z * P.Pi).mulVec P.w = 0 := by
  rw [← Matrix.mulVec_mulVec, Pi_mulVec_w, Matrix.mulVec_zero]

lemma J_mulVec_w (ρ : ι → ℝ) : (P.J ρ).mulVec P.w = 0 := by
  ext i
  have e : (P.J ρ).mulVec P.w i = ∑ k, P.J ρ i k * P.w k := rfl
  rw [e, Pi.zero_apply]
  simp only [J_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  have := P.sum_w_Om j
  calc ∑ k, (P.Dp j).mulVec ρ i * P.Om j k * P.w k
      = (P.Dp j).mulVec ρ i * ∑ k, P.w k * P.Om j k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = 0 := by rw [this, mul_zero]

lemma ipw_mul_Pi_left (Z : Matrix ι μ ℝ) {F : Matrix ι μ ℝ} (hF : F.mulVec P.w = 0) :
    P.ipw (Z * P.Pi) F = P.ipw Z F := by
  simp only [ipw_apply, mul_Pi_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := P.sum_mul_w_eq_zero hF i
  set c := 1 / P.DOm * ∑ l, Z i l * P.w l
  have e : ∑ k, (Z i k - c) * P.w k * F i k =
      ∑ k, Z i k * P.w k * F i k - c * ∑ k, F i k * P.w k := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e, h, mul_zero, sub_zero]

/-- `Π` is a contraction of `‖·‖_w`. -/
lemma ipw_mul_Pi_self_le (Z : Matrix ι μ ℝ) : P.ipw (Z * P.Pi) (Z * P.Pi) ≤ P.ipw Z Z := by
  have hD := P.DOm_pos
  have hw : ∀ i, ∑ k, (Z * P.Pi) i k * P.w k = 0 := by
    intro i
    exact P.sum_mul_w_eq_zero (P.mul_Pi_mulVec_w Z) i
  have h1 : P.ipw (Z * P.Pi) (Z * P.Pi) = P.ipw Z (Z * P.Pi) :=
    P.ipw_mul_Pi_left Z (P.mul_Pi_mulVec_w Z)
  have h2 := P.two_mul_ipw_le Z (Z * P.Pi)
  linarith

lemma A_add (F₁ F₂ : Matrix ι μ ℝ) : P.A (F₁ + F₂) = P.A F₁ + P.A F₂ := by
  simp only [A, Matrix.mul_add, Matrix.add_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by abel

/-! ### Dissipation and the CFL number -/

section Bounds

variable {Ωmax hmin : ℝ}

lemma ipw_abs_nonneg (j : Fin d) (F : Matrix ι μ ℝ) :
    0 ≤ P.ipw (P.Dp j * F * P.absQ j) (P.Dp j * F) := by
  rw [ipw_abs]
  exact mul_nonneg P.vol_pos.le (Finset.sum_nonneg fun k _ =>
    mul_nonneg (mul_nonneg (P.w_pos k).le (abs_nonneg _)) (P.nrm_nonneg F j k))

lemma dis_nonneg (F : Matrix ι μ ℝ) : 0 ≤ P.dis F :=
  Finset.sum_nonneg fun j _ =>
    mul_nonneg (div_nonneg (P.dx_pos j).le (by norm_num)) (P.ipw_abs_nonneg j F)

lemma ipw_abs_abs_le (hΩ : ∀ j k, |P.Om j k| ≤ Ωmax) (j : Fin d) (F : Matrix ι μ ℝ) :
    P.ipw (P.Dp j * F * P.absQ j) (P.Dp j * F * P.absQ j) ≤
      Ωmax * P.ipw (P.Dp j * F * P.absQ j) (P.Dp j * F) := by
  rw [ipw_abs_abs, ipw_abs, mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ P.vol_pos.le
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have hn := P.nrm_nonneg F j k
  have hw := (P.w_pos k).le
  have h := hΩ j k
  have ha := abs_nonneg (P.Om j k)
  have e : P.Om j k ^ 2 = |P.Om j k| * |P.Om j k| := by rw [← sq, sq_abs]
  rw [e]
  have : |P.Om j k| * |P.Om j k| ≤ Ωmax * |P.Om j k| := mul_le_mul_of_nonneg_right h ha
  calc P.w k * (|P.Om j k| * |P.Om j k|) * P.nrm F j k
      ≤ P.w k * (Ωmax * |P.Om j k|) * P.nrm F j k := by gcongr
    _ = Ωmax * (P.w k * |P.Om j k| * P.nrm F j k) := by ring

lemma ipw_abs_le (hΩ : ∀ j k, |P.Om j k| ≤ Ωmax) (j : Fin d) (F : Matrix ι μ ℝ) :
    P.ipw (P.Dp j * F * P.absQ j) (P.Dp j * F) ≤
      Ωmax * P.ipw (P.Dp j * F) (P.Dp j * F) := by
  rw [ipw_abs, ipw_Dp_self, mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ P.vol_pos.le
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have hn := P.nrm_nonneg F j k
  have hw := (P.w_pos k).le
  have h := hΩ j k
  calc P.w k * |P.Om j k| * P.nrm F j k ≤ P.w k * Ωmax * P.nrm F j k := by gcongr
    _ = Ωmax * (P.w k * P.nrm F j k) := by ring

/-- `‖A F‖_w² ≤ ℓ ⟨A F, F⟩_w` with `ℓ = 2 d ‖Ω‖ / min Δx`. -/
lemma ipw_A_A_le_dis (hΩ0 : 0 < Ωmax) (hΩ : ∀ j k, |P.Om j k| ≤ Ωmax) (hh0 : 0 < hmin)
    (hh : ∀ j, hmin ≤ P.dx j) (F : Matrix ι μ ℝ) :
    P.ipw (P.A F) (P.A F) ≤ 2 * d * Ωmax / hmin * P.dis F := by
  refine (P.ipw_A_A_le F).trans ?_
  have e : 2 * (d : ℝ) * Ωmax / hmin * P.dis F =
      d * ∑ j, Ωmax * (P.dx j / hmin) * P.ipw (P.Dp j * F * P.absQ j) (P.Dp j * F) := by
    rw [dis, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg d)
  refine Finset.sum_le_sum fun j _ => ?_
  refine (P.ipw_abs_abs_le hΩ j F).trans ?_
  have h1 : 1 ≤ P.dx j / hmin := (one_le_div hh0).2 (hh j)
  have h2 := P.ipw_abs_nonneg j F
  nlinarith [mul_nonneg hΩ0.le h2]

/-- `⟨A F, F⟩_w ≤ ℓ ‖F‖_w²` with `ℓ = 2 d ‖Ω‖ / min Δx`. -/
lemma dis_le (hΩ0 : 0 < Ωmax) (hΩ : ∀ j k, |P.Om j k| ≤ Ωmax) (hh0 : 0 < hmin)
    (hh : ∀ j, hmin ≤ P.dx j) (F : Matrix ι μ ℝ) :
    P.dis F ≤ 2 * d * Ωmax / hmin * P.ipw F F := by
  have hg := P.ipw_self_nonneg F
  have key : ∀ j, P.dx j / 2 * P.ipw (P.Dp j * F * P.absQ j) (P.Dp j * F) ≤
      2 * Ωmax / hmin * P.ipw F F := by
    intro j
    have hdx := P.dx_pos j
    have h1 := P.ipw_abs_le hΩ j F
    have h2 := P.ipw_Dp_self_le j F
    have h3 : P.ipw (P.Dp j * F * P.absQ j) (P.Dp j * F) ≤
        Ωmax * (4 / P.dx j ^ 2 * P.ipw F F) :=
      h1.trans (mul_le_mul_of_nonneg_left h2 hΩ0.le)
    calc P.dx j / 2 * P.ipw (P.Dp j * F * P.absQ j) (P.Dp j * F)
        ≤ P.dx j / 2 * (Ωmax * (4 / P.dx j ^ 2 * P.ipw F F)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 2 * Ωmax / P.dx j * P.ipw F F := by field_simp; ring
      _ ≤ 2 * Ωmax / hmin * P.ipw F F := by
          refine mul_le_mul_of_nonneg_right ?_ hg
          exact div_le_div_of_nonneg_left (by positivity) hh0 (hh j)
  calc P.dis F ≤ ∑ _j : Fin d, 2 * Ωmax / hmin * P.ipw F F :=
        Finset.sum_le_sum fun j _ => key j
    _ = 2 * d * Ωmax / hmin * P.ipw F F := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

private lemma real_bound {g D n a l s : ℝ} (hg : 0 ≤ g) (hD : 0 ≤ D) (hDl : D ≤ l * g)
    (hn : n ≤ l * D) (ha : 0 ≤ a) (hs : 0 ≤ s) (hκ : a * l ≤ 2 + s) :
    g - 2 * a * D + a ^ 2 * n ≤ (1 + s) ^ 2 * g := by
  have h1 : a ^ 2 * n ≤ a ^ 2 * (l * D) := mul_le_mul_of_nonneg_left hn (sq_nonneg a)
  have hg1 : g ≤ (1 + s) ^ 2 * g := by nlinarith [mul_nonneg hg hs, mul_nonneg hg (sq_nonneg s)]
  by_cases hc : a * l ≤ 2
  · have : a * (a * l - 2) * D ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos ha (by linarith)) hD
    nlinarith
  · have hc' : 2 < a * l := not_le.1 hc
    have h2 : a * (a * l - 2) * D ≤ a * (a * l - 2) * (l * g) :=
      mul_le_mul_of_nonneg_left hDl (mul_nonneg ha (by linarith))
    have h3 : (a * l - 1) ^ 2 ≤ (1 + s) ^ 2 := by
      apply pow_le_pow_left₀ <;> linarith
    have h4 : (a * l - 1) ^ 2 * g ≤ (1 + s) ^ 2 * g := mul_le_mul_of_nonneg_right h3 hg
    nlinarith

/-- Stability of the explicit advection step under the CFL number `a ℓ ≤ 2 + s`. -/
lemma advection_bound {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (hΩ0 : 0 < Ωmax)
    (hΩ : ∀ j k, |P.Om j k| ≤ Ωmax) (hh0 : 0 < hmin) (hh : ∀ j, hmin ≤ P.dx j)
    (hκ : a * (2 * d * Ωmax / hmin) ≤ 2 + s) (F : Matrix ι μ ℝ) :
    P.ipw (F - a • P.A F) (F - a • P.A F) ≤ (1 + s) ^ 2 * P.ipw F F := by
  have h := real_bound (P.ipw_self_nonneg F) (P.dis_nonneg F) (P.dis_le hΩ0 hΩ hh0 hh F)
    (P.ipw_A_A_le_dis hΩ0 hΩ hh0 hh F) ha hs hκ
  have e : P.ipw (F - a • P.A F) (F - a • P.A F) =
      P.ipw F F - 2 * a * P.dis F + a ^ 2 * P.ipw (P.A F) (P.A F) := by
    simp only [ipw_sub_left, ipw_sub_right, ipw_smul_left, ipw_smul_right]
    rw [P.ipw_comm F (P.A F), ipw_A_self]
    ring
  rw [e]
  exact h

end Bounds

/-! ### The discrete `ρ` inner product -/

lemma ipv_comm (f₁ f₂ : ι → ℝ) : P.ipv f₁ f₂ = P.ipv f₂ f₁ := by
  simp only [ipv, dotProduct_comm]

lemma ipv_add_right (f₁ f₂ f₃ : ι → ℝ) : P.ipv f₁ (f₂ + f₃) = P.ipv f₁ f₂ + P.ipv f₁ f₃ := by
  simp only [ipv, dotProduct_add, mul_add]

lemma ipv_smul_right (c : ℝ) (f₁ f₂ : ι → ℝ) : P.ipv f₁ (c • f₂) = c * P.ipv f₁ f₂ := by
  simp only [ipv, dotProduct_smul, smul_eq_mul]
  ring

lemma ipv_sub_right (f₁ f₂ f₃ : ι → ℝ) : P.ipv f₁ (f₂ - f₃) = P.ipv f₁ f₂ - P.ipv f₁ f₃ := by
  simp only [ipv, dotProduct_sub, mul_sub]

lemma ipv_self_nonneg (f : ι → ℝ) : 0 ≤ P.ipv f f :=
  mul_nonneg P.vol_pos.le (Finset.sum_nonneg fun i _ => mul_self_nonneg (f i))

/-- Absorption is dissipative in the macro equation. -/
lemma ipv_absorb_nonneg {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) (f : ι → ℝ) :
    0 ≤ P.ipv f (fun i => c i * f i) := by
  refine mul_nonneg P.vol_pos.le (Finset.sum_nonneg fun i _ => ?_)
  have := mul_nonneg (hc i) (mul_self_nonneg (f i))
  simp only
  nlinarith

/-! ### The schemes -/

/-- The fully discrete IMEX scheme (3.7) of arXiv 2602.12337, with `ρ'`, `G'` at level `n + 1`. -/
structure IsIMEXStep (C : Coeff ι) (Φ ρ : ι → ℝ) (G : Matrix ι μ ℝ) (ρ' : ι → ℝ)
    (G' : Matrix ι μ ℝ) : Prop where
  macroEq : (1 / C.dt) • (ρ' - ρ) + P.H G' = -(fun i => C.sigAm i * ρ' i) + Φ
  microEq : (1 / C.dt) • (G' - G) + (1 / C.eps) • (P.A G * P.Pi) =
    -(1 / C.eps ^ 2) • P.J ρ - (1 / C.eps ^ 2) • (Matrix.diagonal C.sigS * G') -
      Matrix.diagonal C.sigA * G'

/-- The fully discrete IMEX-S scheme (3.8) of arXiv 2602.12337: `𝒥` acts on the new density. -/
structure IsIMEXSStep (C : Coeff ι) (Φ ρ : ι → ℝ) (G : Matrix ι μ ℝ) (ρ' : ι → ℝ)
    (G' : Matrix ι μ ℝ) : Prop where
  macroEq : (1 / C.dt) • (ρ' - ρ) + P.H G' = -(fun i => C.sigAm i * ρ' i) + Φ
  microEq : (1 / C.dt) • (G' - G) + (1 / C.eps) • (P.A G * P.Pi) =
    -(1 / C.eps ^ 2) • P.J ρ' - (1 / C.eps ^ 2) • (Matrix.diagonal C.sigS * G') -
      Matrix.diagonal C.sigA * G'

/-- The micro equation solved for the implicit part. -/
lemma lam_mul_of_micro (C : Coeff ι) {G G' : Matrix ι μ ℝ} {ρJ : ι → ℝ}
    (h : (1 / C.dt) • (G' - G) + (1 / C.eps) • (P.A G * P.Pi) =
      -(1 / C.eps ^ 2) • P.J ρJ - (1 / C.eps ^ 2) • (Matrix.diagonal C.sigS * G') -
        Matrix.diagonal C.sigA * G') :
    Matrix.diagonal C.lam * G' =
      G - (C.dt / C.eps) • (P.A G * P.Pi) - (C.dt / C.eps ^ 2) • P.J ρJ := by
  have hdt := C.dt_pos.ne'
  have heps := C.eps_pos.ne'
  ext i k
  have h' := congrFun (congrFun h i) k
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.diagonal_mul] at h'
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_mul, Coeff.lam]
  field_simp at h' ⊢
  linarith

/-- The zero-density constraint `G w = 0` of arXiv 2602.12337 (used in Thm. 3.1 and Sec. 4.3) is
propagated by the micro equation of both IMEX and IMEX-S, whatever the density in `𝒥`. -/
lemma zero_moment_of_lam (C : Coeff ι) {G G' : Matrix ι μ ℝ} {ρJ : ι → ℝ}
    (h : Matrix.diagonal C.lam * G' =
      G - (C.dt / C.eps) • (P.A G * P.Pi) - (C.dt / C.eps ^ 2) • P.J ρJ)
    (hG : G.mulVec P.w = 0) : G'.mulVec P.w = 0 := by
  have h0 : (G - (C.dt / C.eps) • (P.A G * P.Pi) - (C.dt / C.eps ^ 2) • P.J ρJ).mulVec P.w = 0 := by
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, hG, mul_Pi_mulVec_w, J_mulVec_w, smul_zero,
      sub_zero]
  rw [← h, ← Matrix.mulVec_mulVec] at h0
  ext i
  have h2 := congrFun h0 i
  rw [Matrix.mulVec_diagonal, Pi.zero_apply] at h2
  simpa [(C.lam_pos i).ne'] using h2

lemma ipv_neg_right (f₁ f₂ : ι → ℝ) : P.ipv f₁ (-f₂) = -P.ipv f₁ f₂ := by
  simp only [ipv, dotProduct_neg, mul_neg]

lemma ipv_self_sub (f₁ f₂ : ι → ℝ) :
    P.ipv (f₁ - f₂) (f₁ - f₂) = P.ipv f₁ f₁ - 2 * P.ipv f₁ f₂ + P.ipv f₂ f₂ := by
  simp only [ipv_apply, Pi.sub_apply]
  have e : ∑ i, (f₁ i - f₂ i) * (f₁ i - f₂ i) =
      ∑ i, f₁ i * f₁ i - 2 * ∑ i, f₁ i * f₂ i + ∑ i, f₂ i * f₂ i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  ring

lemma diag_inv_mul_diag {c : ι → ℝ} (hc : ∀ i, 0 < c i) :
    Matrix.diagonal (fun i => (c i)⁻¹) * Matrix.diagonal c = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  exact inv_mul_cancel₀ (hc i).ne'

lemma diag_mul_diag_inv {c : ι → ℝ} (hc : ∀ i, 0 < c i) :
    Matrix.diagonal c * Matrix.diagonal (fun i => (c i)⁻¹) = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  exact mul_inv_cancel₀ (hc i).ne'

/-- Young's inequality with a positive diagonal weight. -/
lemma ipw_young_dg {c : ι → ℝ} (hc : ∀ i, 0 < c i) (X W : Matrix ι μ ℝ) :
    2 * P.ipw W X ≤
      P.ipw (Matrix.diagonal c * X) X + P.ipw (Matrix.diagonal (fun i => (c i)⁻¹) * W) W := by
  have h := P.ipw_dg_nonneg (c := c) (fun i => (hc i).le)
    (X - Matrix.diagonal (fun i => (c i)⁻¹) * W)
  have e1 : Matrix.diagonal c * (X - Matrix.diagonal (fun i => (c i)⁻¹) * W) =
      Matrix.diagonal c * X - W := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, diag_mul_diag_inv hc, Matrix.one_mul]
  rw [e1] at h
  have e2 : P.ipw (Matrix.diagonal c * X) (Matrix.diagonal (fun i => (c i)⁻¹) * W) = P.ipw X W := by
    rw [ipw_dg_comm, ← Matrix.mul_assoc, diag_mul_diag_inv hc, Matrix.one_mul]
  simp only [ipw_sub_left, ipw_sub_right, e2] at h
  rw [P.ipw_comm W (Matrix.diagonal (fun i => (c i)⁻¹) * W), P.ipw_comm X W] at h
  linarith

section Core

variable {θ CA Ωmax hmin : ℝ}

/-- The CFL condition (3.11) reads `(Δt/ε) ℓ ≤ 2 + (1 - θ) Δt σ₀/ε²`,
with `ℓ = 2 d ‖Ω‖ / min_j Δx^{(j)}`. -/
private lemma cfl_real {ε dt σ : ℝ} (hε : 0 < ε) (hdt : 0 < dt) (hΩ0 : 0 < Ωmax) (hh0 : 0 < hmin)
    (hCA : 1 ≤ CA)
    (hcfl : (ε * CA * d / (2 * hmin) - (1 - θ) * σ / (4 * Ωmax)) * dt ≤ ε ^ 2 / (2 * Ωmax)) :
    dt / ε * (2 * d * Ωmax / hmin) ≤ 2 + (1 - θ) * (dt * σ / ε ^ 2) := by
  have hpos : 0 < 4 * Ωmax / ε ^ 2 := by positivity
  have h := mul_le_mul_of_nonneg_left hcfl hpos.le
  have e1 : 4 * Ωmax / ε ^ 2 * ((ε * CA * d / (2 * hmin) - (1 - θ) * σ / (4 * Ωmax)) * dt) =
      CA * (dt / ε * (2 * d * Ωmax / hmin)) - (1 - θ) * (dt * σ / ε ^ 2) := by
    field_simp
    ring
  have e2 : 4 * Ωmax / ε ^ 2 * (ε ^ 2 / (2 * Ωmax)) = 2 := by
    field_simp
    ring
  rw [e1, e2] at h
  have hnn : 0 ≤ dt / ε * (2 * d * Ωmax / hmin) := by positivity
  nlinarith

private lemma final_arith {m r1 r0 g1 g0 q s u e : ℝ} (h2 : m * (r1 - r0) ≤ 2 * e * q)
    (h7 : e * ((1 + u) * g1 + 2 * q) ≤ e * ((1 + s) * g0))
    (h8 : e * ((1 + s) * g1) ≤ e * ((1 + u) * g1)) :
    m * r1 + e * g1 + e * s * g1 ≤ m * r0 + e * g0 + e * s * g0 := by
  nlinarith

/-- The energy argument behind Thm. 3.2 and Thm. 4.1 of arXiv 2602.12337, which is not the one of
the paper; see the module docstring.  `ρ'` solves the macro equation with the full-rank update
from `G`, while `G'` only has to satisfy the tested Galerkin identity from a `⟨·,·⟩_w`-orthogonal
part `Gt` of `G`.  Under (3.11) the energy does not increase. -/
theorem schur_energy_core (C : Coeff ι) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hCA : 1 ≤ CA)
    (hΩ0 : 0 < Ωmax) (hΩ : ∀ j k, |P.Om j k| ≤ Ωmax) (hh0 : 0 < hmin) (hh : ∀ j, hmin ≤ P.dx j)
    (hcfl : (C.eps * CA * d / (2 * hmin) - (1 - θ) * C.sig0 / (4 * Ωmax)) * C.dt ≤
      C.eps ^ 2 / (2 * Ωmax))
    {ρ ρ' : ι → ℝ} {G Gt G' : Matrix ι μ ℝ}
    (hG : G.mulVec P.w = 0) (hGt : Gt.mulVec P.w = 0) (horth : P.ipw Gt (G - Gt) = 0)
    (hmacro : (1 / C.dt) • (ρ' - ρ) +
        P.H (Matrix.diagonal (fun i => (C.lam i)⁻¹) *
          (G - (C.dt / C.eps) • (P.A G * P.Pi) - (C.dt / C.eps ^ 2) • P.J ρ')) =
      -(fun i => C.sigAm i * ρ' i))
    (htest : P.ipw (Matrix.diagonal C.lam * G') G' =
      P.ipw (Gt - (C.dt / C.eps) • (P.A Gt * P.Pi) - (C.dt / C.eps ^ 2) • P.J ρ') G') :
    P.energy C θ ρ' G' ≤ P.energy C θ ρ G := by
  have hdt := C.dt_pos
  have heps := C.eps_pos
  have hsig := C.sig0_pos
  have hD := P.DOm_pos
  set a := C.dt / C.eps with ha
  set c := C.dt / C.eps ^ 2 with hc
  set u := C.dt * C.sig0 / C.eps ^ 2 with hu
  have hu0 : 0 ≤ u := by positivity
  set s := (1 - θ) * u with hs
  have hs0 : 0 ≤ s := mul_nonneg (by linarith) hu0
  have hsu : s ≤ u := by nlinarith
  have hκ : a * (2 * d * Ωmax / hmin) ≤ 2 + s := cfl_real heps hdt hΩ0 hh0 hCA hcfl
  have ha0 : 0 ≤ a := by positivity
  -- the advection-part operator
  set B : Matrix ι μ ℝ → Matrix ι μ ℝ := fun F => F - a • (P.A F * P.Pi) with hB
  have hBbound : ∀ F : Matrix ι μ ℝ, F.mulVec P.w = 0 →
      P.ipw (B F) (B F) ≤ (1 + s) ^ 2 * P.ipw F F := by
    intro F hF
    have e : B F = (F - a • P.A F) * P.Pi := by
      simp only [hB, Matrix.sub_mul, Matrix.smul_mul, P.mul_Pi_of_zero hF]
    rw [e]
    exact (P.ipw_mul_Pi_self_le _).trans (P.advection_bound ha0 hs0 hΩ0 hΩ hh0 hh hκ F)
  set N := G - Gt with hN
  have hNw : N.mulVec P.w = 0 := by
    rw [hN, Matrix.sub_mulVec, hG, hGt, sub_zero]
  have hGN : G = Gt + N := by rw [hN]; abel
  set y := c • P.J ρ' with hy
  set L := B Gt with hL
  set L2 := B N with hL2
  have hBG : B G = L + L2 := by
    rw [hL, hL2]
    simp only [hB]
    rw [hGN, A_add, Matrix.add_mul, smul_add]
    abel
  set Li : ι → ℝ := fun i => (C.lam i)⁻¹ with hLi
  have hLi0 : ∀ i, 0 < Li i := fun i => inv_pos.2 (C.lam_pos i)
  -- the implicit micro test
  have h1 : P.ipw (Matrix.diagonal C.lam * G') G' ≤
      P.ipw (Matrix.diagonal Li * (L - y)) (L - y) := by
    have hy' := P.ipw_young_dg C.lam_pos G' (L - y)
    have ht : P.ipw (L - y) G' = P.ipw (Matrix.diagonal C.lam * G') G' := htest.symm
    rw [ht] at hy'
    linarith
  -- the macro test
  have hsG := P.sbp_H_J ρ' (Matrix.diagonal Li * (B G - y))
  have h2 : P.DOm * (P.ipv ρ' ρ' - P.ipv ρ ρ) ≤
      2 * C.eps ^ 2 * P.ipw (Matrix.diagonal Li * y) (L + L2 - y) := by
    have hm := congrArg (P.ipv ρ') hmacro
    change P.ipv ρ' ((1 / C.dt) • (ρ' - ρ) + P.H (Matrix.diagonal Li * (B G - y))) = _ at hm
    rw [ipv_add_right, ipv_smul_right, ipv_sub_right, ipv_neg_right] at hm
    have hab := P.ipv_absorb_nonneg C.sigAm_nonneg ρ'
    have hrd := P.ipv_self_nonneg (ρ' - ρ)
    rw [ipv_self_sub] at hrd
    have ej : P.ipw (P.J ρ') (Matrix.diagonal Li * (B G - y)) * C.dt =
        C.eps ^ 2 * P.ipw (Matrix.diagonal Li * y) (L + L2 - y) := by
      rw [← hBG, P.ipw_dg_comm Li y, hy, ipw_smul_left, hc]
      field_simp
    set σt := P.ipv ρ' (fun i => C.sigAm i * ρ' i)
    set Aρ := P.ipv ρ' (P.H (Matrix.diagonal Li * (B G - y)))
    set X := P.ipw (P.J ρ') (Matrix.diagonal Li * (B G - y))
    have hx : 1 / C.dt * (P.ipv ρ' ρ' - P.ipv ρ' ρ) = -σt - Aρ := by linarith
    have hx2 : P.ipv ρ' ρ' - P.ipv ρ' ρ = C.dt * (-σt - Aρ) := by
      rw [← hx]
      field_simp
    have hx3 : P.DOm * (P.ipv ρ' ρ' - P.ipv ρ' ρ) =
        C.dt * X - P.DOm * C.dt * σt := by
      rw [hx2]
      linear_combination (-C.dt) * hsG
    have h4 : 0 ≤ P.DOm * C.dt * σt := by positivity
    have h5 := mul_nonneg hD.le hrd
    have h6 : P.ipv ρ ρ' = P.ipv ρ' ρ := P.ipv_comm _ _
    nlinarith
  -- the weighted bilinear form
  set Q : Matrix ι μ ℝ → Matrix ι μ ℝ → ℝ := fun F₁ F₂ => P.ipw (Matrix.diagonal Li * F₁) F₂
    with hQ
  have hsym : ∀ F₁ F₂, Q F₁ F₂ = Q F₂ F₁ := by
    intro F₁ F₂
    simp only [hQ]
    rw [ipw_dg_comm, P.ipw_comm]
  have h3 : 2 * Q y (L + L2 - y) + Q (L - y) (L - y) = Q L L + 2 * Q y L2 - Q y y := by
    have e := hsym L y
    simp only [hQ] at e ⊢
    simp only [Matrix.mul_sub, ipw_sub_left, ipw_sub_right, ipw_add_right]
    rw [e]
    ring
  have h4 : 2 * Q y L2 ≤ Q y y + Q L2 L2 := by
    have hn := P.ipw_dg_nonneg (c := Li) (fun i => (hLi0 i).le) (y - L2)
    have e := hsym L2 y
    simp only [hQ] at e ⊢
    simp only [Matrix.mul_sub, ipw_sub_left, ipw_sub_right] at hn
    rw [e] at hn
    linarith
  have hu1 : 0 < 1 + u := by linarith
  have hQle : ∀ F : Matrix ι μ ℝ, Q F F ≤ (1 + u)⁻¹ * P.ipw F F := by
    intro F
    have hle : ∀ i, Li i ≤ (1 + u)⁻¹ := fun i =>
      inv_anti₀ hu1 (C.one_add_le_lam i)
    have := P.ipw_dg_sub_nonneg (c := Li) (c' := fun _ => (1 + u)⁻¹) hle F
    rwa [ipw_dg_const] at this
  have hL1 : Q L L ≤ (1 + u)⁻¹ * ((1 + s) ^ 2 * P.ipw Gt Gt) :=
    (hQle L).trans (mul_le_mul_of_nonneg_left (hBbound Gt hGt) (inv_pos.2 hu1).le)
  have hL2' : Q L2 L2 ≤ (1 + u)⁻¹ * ((1 + s) ^ 2 * P.ipw N N) :=
    (hQle L2).trans (mul_le_mul_of_nonneg_left (hBbound N hNw) (inv_pos.2 hu1).le)
  have hg0 : P.ipw G G = P.ipw Gt Gt + P.ipw N N := by
    have e1 : P.ipw Gt N = 0 := horth
    have e2 : P.ipw N Gt = 0 := by rw [P.ipw_comm]; exact horth
    calc P.ipw G G = P.ipw (Gt + N) (Gt + N) := by rw [← hGN]
      _ = P.ipw Gt Gt + P.ipw N N := by
          simp only [ipw_add_left, ipw_add_right]
          rw [e1, e2]
          ring
  have hlow : (1 + u) * P.ipw G' G' ≤ P.ipw (Matrix.diagonal C.lam * G') G' := by
    have := P.ipw_dg_sub_nonneg (c := fun _ => 1 + u) (c' := C.lam) C.one_add_le_lam G'
    rwa [ipw_dg_const] at this
  have hfrac : (1 + u)⁻¹ * (1 + s) ^ 2 ≤ 1 + s := by
    rw [inv_mul_le_iff₀ hu1]
    nlinarith
  have hg0nn := P.ipw_self_nonneg G
  have hg1nn := P.ipw_self_nonneg G'
  have hsum : P.ipw (Matrix.diagonal C.lam * G') G' + 2 * Q y (L + L2 - y) ≤
      (1 + s) * P.ipw G G := by
    have hb : Q L L + Q L2 L2 ≤ (1 + u)⁻¹ * (1 + s) ^ 2 * P.ipw G G := by
      rw [hg0]
      calc Q L L + Q L2 L2
          ≤ (1 + u)⁻¹ * ((1 + s) ^ 2 * P.ipw Gt Gt) + (1 + u)⁻¹ * ((1 + s) ^ 2 * P.ipw N N) :=
            add_le_add hL1 hL2'
        _ = _ := by ring
    have hb2 : (1 + u)⁻¹ * (1 + s) ^ 2 * P.ipw G G ≤ (1 + s) * P.ipw G G :=
      mul_le_mul_of_nonneg_right hfrac hg0nn
    have h1' : P.ipw (Matrix.diagonal C.lam * G') G' ≤ Q (L - y) (L - y) := h1
    linarith
  have hE : (1 - θ) * C.dt * C.sig0 = C.eps ^ 2 * s := by
    rw [hs, hu]
    field_simp
  have heps2 : 0 < C.eps ^ 2 := by positivity
  simp only [energy]
  rw [hE]
  have h2' : P.DOm * (P.ipv ρ' ρ' - P.ipv ρ ρ) ≤ 2 * C.eps ^ 2 * Q y (L + L2 - y) := h2
  have h7 : C.eps ^ 2 * ((1 + u) * P.ipw G' G' + 2 * Q y (L + L2 - y)) ≤
      C.eps ^ 2 * ((1 + s) * P.ipw G G) :=
    mul_le_mul_of_nonneg_left (by linarith) heps2.le
  have h8 : C.eps ^ 2 * ((1 + s) * P.ipw G' G') ≤ C.eps ^ 2 * ((1 + u) * P.ipw G' G') :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hg1nn) heps2.le
  exact final_arith h2' h7 h8

/-- **Thm. 3.2** (arXiv 2602.12337).  For `Φ = 0`, `θ ∈ [0, 1]` the full-rank IMEX-S scheme (3.8) is
`θ`-stable, `E_θⁿ⁺¹ ≤ E_θⁿ`, under (3.11):
`(ε C_A d / (2 min_j Δx^{(j)}) - (1 - θ) σ₀ / (4 ‖Ω‖)) Δt ≤ ε² / (2 ‖Ω‖)`.
`Ωmax` is any bound of `|Ω|`, `hmin` any lower bound of the `Δx^{(j)}`, `C_A ≥ 1`.  The proof is the
special case `G̃ = G` of `schur_energy_core` and not the one of the paper. -/
theorem theorem_3_2 (C : Coeff ι) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hCA : 1 ≤ CA)
    (hΩ0 : 0 < Ωmax) (hΩ : ∀ j k, |P.Om j k| ≤ Ωmax) (hh0 : 0 < hmin) (hh : ∀ j, hmin ≤ P.dx j)
    (hcfl : (C.eps * CA * d / (2 * hmin) - (1 - θ) * C.sig0 / (4 * Ωmax)) * C.dt ≤
      C.eps ^ 2 / (2 * Ωmax))
    {ρ ρ' : ι → ℝ} {G G' : Matrix ι μ ℝ} (hG : G.mulVec P.w = 0)
    (hstep : P.IsIMEXSStep C 0 ρ G ρ' G') :
    P.energy C θ ρ' G' ≤ P.energy C θ ρ G := by
  have hlam := P.lam_mul_of_micro C hstep.microEq
  have hG' : G' = Matrix.diagonal (fun i => (C.lam i)⁻¹) *
      (G - (C.dt / C.eps) • (P.A G * P.Pi) - (C.dt / C.eps ^ 2) • P.J ρ') := by
    rw [← hlam, ← Matrix.mul_assoc, diag_inv_mul_diag C.lam_pos, Matrix.one_mul]
  refine P.schur_energy_core C hθ0 hθ1 hCA hΩ0 hΩ hh0 hh hcfl hG hG ?_ ?_ ?_
  · simp [ipw_apply]
  · rw [← hG']
    simpa using hstep.macroEq
  · rw [hlam]

/-- **Thm. 3.2** (arXiv 2602.12337) in the form of Definition 3.1: `E_θⁿ⁺¹ ≤ E_θⁿ` for all `n`,
where the zero-density constraint is needed only at `n = 0`. -/
theorem theorem_3_2_trajectory (C : Coeff ι) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hCA : 1 ≤ CA)
    (hΩ0 : 0 < Ωmax) (hΩ : ∀ j k, |P.Om j k| ≤ Ωmax) (hh0 : 0 < hmin) (hh : ∀ j, hmin ≤ P.dx j)
    (hcfl : (C.eps * CA * d / (2 * hmin) - (1 - θ) * C.sig0 / (4 * Ωmax)) * C.dt ≤
      C.eps ^ 2 / (2 * Ωmax))
    {ρ : ℕ → ι → ℝ} {G : ℕ → Matrix ι μ ℝ} (hG0 : (G 0).mulVec P.w = 0)
    (hstep : ∀ n, P.IsIMEXSStep C 0 (ρ n) (G n) (ρ (n + 1)) (G (n + 1))) (n : ℕ) :
    P.energy C θ (ρ (n + 1)) (G (n + 1)) ≤ P.energy C θ (ρ n) (G n) := by
  have hz : ∀ n, (G n).mulVec P.w = 0 := by
    intro n
    induction n with
    | zero => exact hG0
    | succ n ih => exact P.zero_moment_of_lam C (P.lam_mul_of_micro C (hstep n).microEq) ih
  exact P.theorem_3_2 C hθ0 hθ1 hCA hΩ0 hΩ hh0 hh hcfl (hz n) (hstep n)

/-- **Thm. 3.2, unconditional case, and Cor. 3.3** (arXiv 2602.12337).  If
`ε C_A d / (2 min_j Δx^{(j)}) ≤ (1 - θ) σ₀ / (4 ‖Ω‖)`, then IMEX-S is `θ`-stable for every `Δt > 0`
(the Coeff `C` has an arbitrary positive `dt`).  The unconditional clause of Cor. 3.3 is the case
`θ = 0`; its conditional clause (3.12) is `theorem_3_2` at `θ = 0`. -/
theorem corollary_3_3 (C : Coeff ι) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hCA : 1 ≤ CA)
    (hΩ0 : 0 < Ωmax) (hΩ : ∀ j k, |P.Om j k| ≤ Ωmax) (hh0 : 0 < hmin) (hh : ∀ j, hmin ≤ P.dx j)
    (hcond : C.eps * CA * d / (2 * hmin) ≤ (1 - θ) * C.sig0 / (4 * Ωmax))
    {ρ ρ' : ι → ℝ} {G G' : Matrix ι μ ℝ} (hG : G.mulVec P.w = 0)
    (hstep : P.IsIMEXSStep C 0 ρ G ρ' G') :
    P.energy C θ ρ' G' ≤ P.energy C θ ρ G := by
  refine P.theorem_3_2 C hθ0 hθ1 hCA hΩ0 hΩ hh0 hh ?_ hG hstep
  have h1 : (C.eps * CA * d / (2 * hmin) - (1 - θ) * C.sig0 / (4 * Ωmax)) * C.dt ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) C.dt_pos.le
  have h2 : 0 ≤ C.eps ^ 2 / (2 * Ωmax) := by positivity
  linarith

/-- **The unconditional clause of Thm. 3.2 and Cor. 3.3, solved for `ε`** (arXiv 2602.12337).
If `ε ≤ (1 - θ) σ₀ / (2 C_A d ‖Ω‖) min_j Δx^{(j)}` (so `ε = O(Δx)`, the diffusive regime), IMEX-S
is `θ`-stable for every `Δt > 0`.  The condition is that of `corollary_3_3` rearranged; the paper
does not print it in this form. -/
theorem corollary_3_3_diffusive (C : Coeff ι) (hd : 0 < d) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hCA : 1 ≤ CA) (hΩ0 : 0 < Ωmax) (hΩ : ∀ j k, |P.Om j k| ≤ Ωmax) (hh0 : 0 < hmin)
    (hh : ∀ j, hmin ≤ P.dx j)
    (hε : C.eps ≤ (1 - θ) * C.sig0 / (2 * CA * d * Ωmax) * hmin)
    {ρ ρ' : ι → ℝ} {G G' : Matrix ι μ ℝ} (hG : G.mulVec P.w = 0)
    (hstep : P.IsIMEXSStep C 0 ρ G ρ' G') :
    P.energy C θ ρ' G' ≤ P.energy C θ ρ G := by
  refine P.corollary_3_3 C hθ0 hθ1 hCA hΩ0 hΩ hh0 hh ?_ hG hstep
  have hd' : (0 : ℝ) < d := Nat.cast_pos.2 hd
  have hCA' : 0 < CA := by linarith
  have hpos : 0 < CA * d / (2 * hmin) := by positivity
  have h := mul_le_mul_of_nonneg_left hε hpos.le
  calc C.eps * CA * d / (2 * hmin) = CA * d / (2 * hmin) * C.eps := by ring
    _ ≤ CA * d / (2 * hmin) * ((1 - θ) * C.sig0 / (2 * CA * d * Ωmax) * hmin) := h
    _ = (1 - θ) * C.sig0 / (4 * Ωmax) := by
        field_simp
        ring

end Core

section Thm31

variable {CA Ωmax : ℝ}

lemma ipv_self_add (f₁ f₂ : ι → ℝ) :
    P.ipv (f₁ + f₂) (f₁ + f₂) = P.ipv f₁ f₁ + 2 * P.ipv f₁ f₂ + P.ipv f₂ f₂ := by
  simp only [ipv_apply, Pi.add_apply]
  have e : ∑ i, (f₁ i + f₂ i) * (f₁ i + f₂ i) =
      ∑ i, f₁ i * f₁ i + 2 * ∑ i, f₁ i * f₂ i + ∑ i, f₂ i * f₂ i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  ring

private lemma cfl_31 {dt ε σ b Ω a E dd : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (hdt : 0 < dt)
    (hb : 0 < b) (hdd : 0 < dd) (hΩ : 0 < Ω) (hE : 0 ≤ E) (hCA : 1 ≤ CA) (ha : 0 ≤ a)
    (haΩ : a ≤ Ω)
    (h : dt ≤ ε * (b / dd) / (CA * Ω + E) + σ * (b / dd) ^ 2 / (2 * CA * Ω ^ 2 + 2 * E * Ω)) :
    dt * dd * (E * a + a ^ 2) ≤ ε * b * a + σ * b ^ 2 / (2 * dd) := by
  have hCA0 : 0 < CA := by linarith
  have hD : 0 < CA * Ω + E := by positivity
  have e : 2 * CA * Ω ^ 2 + 2 * E * Ω = 2 * Ω * (CA * Ω + E) := by ring
  rw [e] at h
  have h1 : dt * (CA * Ω + E) ≤ ε * (b / dd) + σ * (b / dd) ^ 2 / (2 * Ω) := by
    have h' := mul_le_mul_of_nonneg_right h hD.le
    have e2 : (ε * (b / dd) / (CA * Ω + E) + σ * (b / dd) ^ 2 / (2 * Ω * (CA * Ω + E))) *
        (CA * Ω + E) = ε * (b / dd) + σ * (b / dd) ^ 2 / (2 * Ω) := by
      field_simp
    linarith
  have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hdd.le ha)
  have e3 : dd * a * (ε * (b / dd) + σ * (b / dd) ^ 2 / (2 * Ω)) =
      ε * b * a + σ * b ^ 2 / (2 * dd) * (a / Ω) := by
    field_simp
  rw [e3] at h2
  have h3 : a / Ω ≤ 1 := (div_le_one hΩ).2 haΩ
  have h4 : 0 ≤ σ * b ^ 2 / (2 * dd) := by positivity
  have h5 : σ * b ^ 2 / (2 * dd) * (a / Ω) ≤ σ * b ^ 2 / (2 * dd) := by nlinarith
  have h6 : E * a + a ^ 2 ≤ a * (CA * Ω + E) := by
    have : a ≤ CA * Ω := by nlinarith
    nlinarith
  have h7 : dt * dd * (E * a + a ^ 2) ≤ dt * dd * (a * (CA * Ω + E)) :=
    mul_le_mul_of_nonneg_left h6 (by positivity)
  have e4 : dt * dd * (a * (CA * Ω + E)) = dd * a * (dt * (CA * Ω + E)) := by ring
  linarith

private lemma thm31_arith
    {m r1 r0 r01 rd g1 g0 g01 gd e t σ u a c cA dis ast jG Ar Ar0 sg hh as2 R : ℝ}
    (he : 0 < e) (ht : 0 < t) (hm : 0 < m)
    (ea : e ^ 2 * a = e * t) (ec : e ^ 2 * c = t) (eu : e ^ 2 * u = t * σ)
    (hR : R = g01 - a * cA - c * jG) (hlow : (1 + u) * g1 ≤ R)
    (hgd : gd = g1 - 2 * g01 + g0) (hcA : cA = dis - ast)
    (hM2 : 1 / t * (r1 - r01) + Ar = -sg) (hsg : 0 ≤ sg) (hrd : rd = r1 - 2 * r01 + r0)
    (hS : m * Ar0 = -jG)
    (Y1 : 0 ≤ rd + 2 * t * (Ar - Ar0) + t ^ 2 * hh)
    (Y2 : 0 ≤ e ^ 2 * gd - 2 * e * t * ast + t ^ 2 * as2)
    (K : t * (m * hh + as2) ≤ 2 * e * dis + 2 * σ * g1) :
    m * r1 + e ^ 2 * g1 ≤ m * r0 + e ^ 2 * g0 := by
  have h1 : e ^ 2 * ((1 + u) * g1) ≤ e ^ 2 * (g01 - a * cA - c * jG) := by
    rw [← hR]
    exact mul_le_mul_of_nonneg_left hlow (by positivity)
  have h2 : e ^ 2 * (g01 - a * cA - c * jG) = e ^ 2 * g01 - e * t * cA - t * jG := by
    linear_combination (-cA) * ea + (-jG) * ec
  have h3 : e ^ 2 * ((1 + u) * g1) = e ^ 2 * g1 + t * σ * g1 := by
    linear_combination g1 * eu
  have h4 : r1 - r01 = t * (-sg - Ar) := by
    have h : 1 / t * (r1 - r01) = -sg - Ar := by linarith
    rw [← h]
    field_simp
  have h5 := mul_nonneg hm.le Y1
  have h6 := mul_le_mul_of_nonneg_left K ht.le
  have h7 : t * (m * Ar0) = -(t * jG) := by rw [hS]; ring
  have h8 : m * (r1 - r01) = m * (t * (-sg - Ar)) := by rw [h4]
  have h9 : 0 ≤ m * t * sg := by positivity
  subst hgd hcA hrd
  nlinarith

/-- **Thm. 3.1** (arXiv 2602.12337).  For `Φ = 0` the full-rank IMEX scheme (3.7) is `1`-stable,
`E_1ⁿ⁺¹ ≤ E_1ⁿ`, under the hyperbolic-parabolic CFL condition
`Δt ≤ min_j (ε (Δx^{(j)}/d) / (C_A ‖Ω‖ + C_B^{(j)}) +
σ₀ (Δx^{(j)}/d)² / (2 C_A ‖Ω‖² + 2 C_B^{(j)} ‖Ω‖))`.  `Ωmax` is any bound of `|Ω|`, `C_A ≥ 1`, and
`G w = 0` is the zero-density constraint.  The proof follows the paper. -/
theorem theorem_3_1 (C : Coeff ι) (hd : 0 < d) (hCA : 1 ≤ CA) (hΩ0 : 0 < Ωmax)
    (hΩ : ∀ j k, |P.Om j k| ≤ Ωmax)
    (hcfl : ∀ j, C.dt ≤ C.eps * (P.dx j / d) / (CA * Ωmax + P.Cb j) +
      C.sig0 * (P.dx j / d) ^ 2 / (2 * CA * Ωmax ^ 2 + 2 * P.Cb j * Ωmax))
    {ρ ρ' : ι → ℝ} {G G' : Matrix ι μ ℝ} (hG : G.mulVec P.w = 0)
    (hstep : P.IsIMEXStep C 0 ρ G ρ' G') :
    P.energy C 1 ρ' G' ≤ P.energy C 1 ρ G := by
  have hdt := C.dt_pos
  have heps := C.eps_pos
  have hsig := C.sig0_pos
  have hD := P.DOm_pos
  have hd' : (0 : ℝ) < d := Nat.cast_pos.2 hd
  have hlam := P.lam_mul_of_micro C hstep.microEq
  have hG' := P.zero_moment_of_lam C hlam hG
  set T1 : Fin d → ℝ := fun j => P.ipw (P.Dp j * G' * P.absQ j) (P.Dp j * G') with hT1
  set T2 : Fin d → ℝ := fun j => P.ipw (P.Dp j * G' * P.absQ j) (P.Dp j * G' * P.absQ j) with hT2
  set T3 : Fin d → ℝ := fun j => P.ipw (P.Dp j * G') (P.Dp j * G') with hT3
  -- the pointwise CFL
  have hkey : ∀ j, C.dt * d * (P.Cb j * T1 j + T2 j) ≤
      C.eps * P.dx j * T1 j + C.sig0 * P.dx j ^ 2 / (2 * d) * T3 j := by
    intro j
    have hk : ∀ k, C.dt * d * (P.Cb j * (P.w k * |P.Om j k| * P.nrm G' j k) +
          P.w k * P.Om j k ^ 2 * P.nrm G' j k) ≤
        C.eps * P.dx j * (P.w k * |P.Om j k| * P.nrm G' j k) +
          C.sig0 * P.dx j ^ 2 / (2 * d) * (P.w k * P.nrm G' j k) := by
      intro k
      have hc := cfl_31 (a := |P.Om j k|) heps hsig hdt (P.dx_pos j) hd' hΩ0 (P.Cb_nonneg j) hCA
        (abs_nonneg _) (hΩ j k) (hcfl j)
      rw [sq_abs] at hc
      have hnn : 0 ≤ P.w k * P.nrm G' j k := mul_nonneg (P.w_pos k).le (P.nrm_nonneg G' j k)
      have := mul_le_mul_of_nonneg_right hc hnn
      linarith
    have hs := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hk k
    simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hs
    have := mul_le_mul_of_nonneg_left hs P.vol_pos.le
    simp only [hT1, hT2, hT3, ipw_abs, ipw_abs_abs, ipw_Dp_self]
    linarith
  -- the three bounds
  have hH := P.H_sq_le G'
  have hAs := P.lemma_3_2 (CA := 1) le_rfl G'
  have hT3le : ∀ j, P.dx j ^ 2 * T3 j ≤ 4 * P.ipw G' G' := by
    intro j
    have h := P.ipw_Dp_self_le j G'
    have hdx := P.dx_pos j
    have e : P.dx j ^ 2 * (4 / P.dx j ^ 2 * P.ipw G' G') = 4 * P.ipw G' G' := by
      field_simp
    have := mul_le_mul_of_nonneg_left h (sq_nonneg (P.dx j))
    linarith
  have hK : C.dt * (P.DOm * P.ipv (P.H G') (P.H G') + P.ipw (P.Astar G') (P.Astar G')) ≤
      2 * C.eps * P.dis G' + 2 * C.sig0 * P.ipw G' G' := by
    have h1 : P.DOm * P.ipv (P.H G') (P.H G') + P.ipw (P.Astar G') (P.Astar G') ≤
        d * ∑ j, (P.Cb j * T1 j + T2 j) := by
      have e1 : ∀ j, P.vol * ∑ k, P.w k * |P.Om j k| * P.nrm G' j k = T1 j := fun j =>
        (P.ipw_abs j G').symm
      simp only [e1] at hH
      rw [Finset.sum_add_distrib, mul_add]
      have e2 : (1 : ℝ) * d * ∑ j, T2 j = d * ∑ j, T2 j := by ring
      rw [e2] at hAs
      exact add_le_add hH hAs
    have h2 : C.dt * d * ∑ j, (P.Cb j * T1 j + T2 j) ≤
        ∑ j, (C.eps * P.dx j * T1 j + C.sig0 * P.dx j ^ 2 / (2 * d) * T3 j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => hkey j
    have h3 : ∑ j, C.eps * P.dx j * T1 j = 2 * C.eps * P.dis G' := by
      rw [dis, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by simp only [hT1]; ring
    have h4 : ∑ j, C.sig0 * P.dx j ^ 2 / (2 * d) * T3 j ≤ 2 * C.sig0 * P.ipw G' G' := by
      have hb : ∀ j, C.sig0 * P.dx j ^ 2 / (2 * d) * T3 j ≤
          C.sig0 / (2 * d) * (4 * P.ipw G' G') := by
        intro j
        have := mul_le_mul_of_nonneg_left (hT3le j) (show 0 ≤ C.sig0 / (2 * d) by positivity)
        calc C.sig0 * P.dx j ^ 2 / (2 * d) * T3 j
            = C.sig0 / (2 * d) * (P.dx j ^ 2 * T3 j) := by ring
          _ ≤ _ := this
      calc ∑ j, C.sig0 * P.dx j ^ 2 / (2 * d) * T3 j
          ≤ ∑ _j : Fin d, C.sig0 / (2 * d) * (4 * P.ipw G' G') :=
            Finset.sum_le_sum fun j _ => hb j
        _ = 2 * C.sig0 * P.ipw G' G' := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            field_simp
            ring
    have e6 : ∑ j, (C.eps * P.dx j * T1 j + C.sig0 * P.dx j ^ 2 / (2 * d) * T3 j) =
        ∑ j, C.eps * P.dx j * T1 j + ∑ j, C.sig0 * P.dx j ^ 2 / (2 * d) * T3 j :=
      Finset.sum_add_distrib
    rw [e6, h3] at h2
    have h5 := mul_le_mul_of_nonneg_left h1 hdt.le
    have e5 : C.dt * (d * ∑ j, (P.Cb j * T1 j + T2 j)) =
        C.dt * d * ∑ j, (P.Cb j * T1 j + T2 j) := by ring
    linarith
  have hR : P.ipw (Matrix.diagonal C.lam * G') G' =
      P.ipw G G' - C.dt / C.eps * P.ipw (P.A G) G' - C.dt / C.eps ^ 2 * P.ipw (P.J ρ) G' := by
    rw [hlam, ipw_sub_left, ipw_sub_left, ipw_smul_left, ipw_smul_left, P.ipw_mul_Pi_left _ hG']
  have hlow : (1 + C.dt * C.sig0 / C.eps ^ 2) * P.ipw G' G' ≤
      P.ipw (Matrix.diagonal C.lam * G') G' := by
    have := P.ipw_dg_sub_nonneg (c := fun _ => 1 + C.dt * C.sig0 / C.eps ^ 2) (c' := C.lam)
      C.one_add_le_lam G'
    rwa [ipw_dg_const] at this
  have hgd : P.ipw (G' - G) (G' - G) = P.ipw G' G' - 2 * P.ipw G G' + P.ipw G G := by
    simp only [ipw_sub_left, ipw_sub_right]
    rw [P.ipw_comm G' G]
    ring
  have hM2 : 1 / C.dt * (P.ipv ρ' ρ' - P.ipv ρ' ρ) + P.ipv ρ' (P.H G') =
      -P.ipv ρ' (fun i => C.sigAm i * ρ' i) := by
    have hm := congrArg (P.ipv ρ') hstep.macroEq
    rw [ipv_add_right, ipv_smul_right, ipv_sub_right, add_zero, ipv_neg_right] at hm
    exact hm
  have hY1 : 0 ≤ P.ipv (ρ' - ρ) (ρ' - ρ) +
      2 * C.dt * (P.ipv ρ' (P.H G') - P.ipv ρ (P.H G')) +
        C.dt ^ 2 * P.ipv (P.H G') (P.H G') := by
    have h := P.ipv_self_nonneg ((ρ' - ρ) + C.dt • P.H G')
    have e : P.ipv (C.dt • P.H G') (C.dt • P.H G') = C.dt ^ 2 * P.ipv (P.H G') (P.H G') := by
      rw [ipv_smul_right, P.ipv_comm (C.dt • P.H G'), ipv_smul_right]
      ring
    have e' : P.ipv (ρ' - ρ) (P.H G') = P.ipv ρ' (P.H G') - P.ipv ρ (P.H G') := by
      rw [P.ipv_comm (ρ' - ρ), ipv_sub_right, P.ipv_comm (P.H G') ρ', P.ipv_comm (P.H G') ρ]
    rw [ipv_self_add, e, ipv_smul_right, e'] at h
    linarith
  have hY2 : 0 ≤ C.eps ^ 2 * P.ipw (G' - G) (G' - G) -
      2 * C.eps * C.dt * P.ipw (P.Astar G') (G' - G) +
        C.dt ^ 2 * P.ipw (P.Astar G') (P.Astar G') := by
    have h := P.ipw_self_nonneg (C.eps • (G' - G) - C.dt • P.Astar G')
    simp only [ipw_sub_left, ipw_sub_right, ipw_smul_left, ipw_smul_right] at h ⊢
    rw [P.ipw_comm G' (P.Astar G'), P.ipw_comm G (P.Astar G')] at h
    nlinarith
  have hfinal := thm31_arith (m := P.DOm) (r1 := P.ipv ρ' ρ') (r0 := P.ipv ρ ρ)
    (r01 := P.ipv ρ' ρ) (rd := P.ipv (ρ' - ρ) (ρ' - ρ)) (g1 := P.ipw G' G') (g0 := P.ipw G G)
    (g01 := P.ipw G G') (gd := P.ipw (G' - G) (G' - G)) (e := C.eps) (t := C.dt)
    (σ := C.sig0) (u := C.dt * C.sig0 / C.eps ^ 2) (a := C.dt / C.eps) (c := C.dt / C.eps ^ 2)
    (cA := P.ipw (P.A G) G') (dis := P.dis G') (ast := P.ipw (P.Astar G') (G' - G))
    (jG := P.ipw (P.J ρ) G') (Ar := P.ipv ρ' (P.H G')) (Ar0 := P.ipv ρ (P.H G'))
    (sg := P.ipv ρ' (fun i => C.sigAm i * ρ' i)) (hh := P.ipv (P.H G') (P.H G'))
    (as2 := P.ipw (P.Astar G') (P.Astar G')) (R := P.ipw (Matrix.diagonal C.lam * G') G')
    heps hdt hD (by field_simp) (by field_simp) (by field_simp) hR hlow hgd
    (P.lemma_3_1 G G') hM2 (P.ipv_absorb_nonneg C.sigAm_nonneg ρ')
    (by rw [ipv_self_sub]) (P.sbp_H_J ρ G') hY1 hY2 hK
  simp only [energy, sub_self, zero_mul, add_zero]
  exact hfinal

/-- **Thm. 3.1** (arXiv 2602.12337) in the form of Definition 3.1: `E_1ⁿ⁺¹ ≤ E_1ⁿ` for all `n`,
where the zero-density constraint is needed only at `n = 0`. -/
theorem theorem_3_1_trajectory (C : Coeff ι) (hd : 0 < d) (hCA : 1 ≤ CA) (hΩ0 : 0 < Ωmax)
    (hΩ : ∀ j k, |P.Om j k| ≤ Ωmax)
    (hcfl : ∀ j, C.dt ≤ C.eps * (P.dx j / d) / (CA * Ωmax + P.Cb j) +
      C.sig0 * (P.dx j / d) ^ 2 / (2 * CA * Ωmax ^ 2 + 2 * P.Cb j * Ωmax))
    {ρ : ℕ → ι → ℝ} {G : ℕ → Matrix ι μ ℝ} (hG0 : (G 0).mulVec P.w = 0)
    (hstep : ∀ n, P.IsIMEXStep C 0 (ρ n) (G n) (ρ (n + 1)) (G (n + 1))) (n : ℕ) :
    P.energy C 1 (ρ (n + 1)) (G (n + 1)) ≤ P.energy C 1 (ρ n) (G n) := by
  have hz : ∀ n, (G n).mulVec P.w = 0 := by
    intro n
    induction n with
    | zero => exact hG0
    | succ n ih => exact P.zero_moment_of_lam C (P.lam_mul_of_micro C (hstep n).microEq) ih
  exact P.theorem_3_1 C hd hCA hΩ0 hΩ hcfl (hz n) (hstep n)

end Thm31

section LowRank

variable {r r' : Type*} [Fintype r] [DecidableEq r] [Fintype r'] [DecidableEq r']

/-- The resolvent `R = (1/Δt + σ^s/ε² + σ^a)⁻¹`. -/
noncomputable def RR (C : Coeff ι) : Matrix ι ι ℝ :=
  Matrix.diagonal fun i => (1 / C.dt + C.sigS i / C.eps ^ 2 + C.sigA i)⁻¹

/-- `ℬ(Y) = 𝒜(Y M⁻¹) (I - |D_Ω|⁻¹ w 1ᵀ) M`. -/
noncomputable def B (Y : Matrix ι μ ℝ) : Matrix ι μ ℝ := P.A (Y * P.Minv) * P.Pi * P.M

/-- The micro variable with `G M = X S Vᵀ`. -/
noncomputable def lowRankG {r : Type*} [Fintype r] (X : Matrix ι r ℝ) (S : Matrix r r ℝ)
    (V : Matrix μ r ℝ) : Matrix ι μ ℝ := X * S * Vᵀ * P.Minv

/-- The constraint `1ᵀ M Y = 0`. -/
def ZeroDensity {r : Type*} (Y : Matrix μ r ℝ) : Prop :=
  Matrix.vecMul (fun _ => (1 : ℝ)) (P.M * Y) = 0

lemma Minv_mul_M : P.Minv * P.M = 1 := by
  rw [M, Minv, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext k
  exact inv_mul_cancel₀ (Real.sqrt_pos.2 (P.w_pos k)).ne'

lemma M_mul_Minv : P.M * P.Minv = 1 := by
  rw [M, Minv, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext k
  exact mul_inv_cancel₀ (Real.sqrt_pos.2 (P.w_pos k)).ne'

lemma Minv_transpose : P.Minvᵀ = P.Minv := Matrix.diagonal_transpose _

lemma zeroDensity_iff {r : Type*} (Y : Matrix μ r ℝ) :
    P.ZeroDensity Y ↔ ∀ c, ∑ k, √(P.w k) * Y k c = 0 := by
  have e : ∀ c, Matrix.vecMul (fun _ => (1 : ℝ)) (P.M * Y) c = ∑ k, √(P.w k) * Y k c := by
    intro c
    simp [Matrix.vecMul, dotProduct, M, Matrix.diagonal_mul]
  constructor
  · intro h c
    rw [← e, h]
    rfl
  · intro h
    ext c
    rw [e, h]
    rfl

lemma mulVec_w_lowRankG {X : Matrix ι r ℝ} {S : Matrix r r ℝ} {V : Matrix μ r ℝ}
    (h : P.ZeroDensity V) : (P.lowRankG X S V).mulVec P.w = 0 := by
  have hV := (P.zeroDensity_iff V).1 h
  ext i
  have e1 : (P.lowRankG X S V).mulVec P.w i = ∑ k, (X * S * Vᵀ) i k * √(P.w k) := by
    simp only [lowRankG, Matrix.mulVec, dotProduct, Minv, Matrix.mul_diagonal]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hw := P.w_pos k
    have hs := Real.sqrt_pos.2 hw
    have : (√(P.w k))⁻¹ * P.w k = √(P.w k) := by
      nth_rewrite 2 [← Real.mul_self_sqrt hw.le]
      field_simp
    rw [mul_assoc, this]
  have e2 : ∀ k, (X * S * Vᵀ) i k = ∑ c, (X * S) i c * V k c := fun k => by
    rw [Matrix.mul_apply]
    rfl
  rw [e1, Pi.zero_apply]
  simp only [e2, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun c _ => ?_
  calc ∑ k, (X * S) i c * V k c * √(P.w k) = (X * S) i c * ∑ k, √(P.w k) * V k c := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = 0 := by rw [hV, mul_zero]

/-- Testing against a low-rank matrix is testing the Galerkin coefficients. -/
lemma ipw_lowRankG (Z : Matrix ι μ ℝ) (X' : Matrix ι r' ℝ) (S' : Matrix r' r' ℝ)
    (V' : Matrix μ r' ℝ) :
    P.ipw Z (P.lowRankG X' S' V') = P.vol * Matrix.trace ((X'ᵀ * Z * P.M * V') * S'ᵀ) := by
  rw [ipw, lowRankG]
  congr 1
  have e : Z * (P.M * P.M) * (X' * S' * V'ᵀ * P.Minv)ᵀ = (Z * P.M * V' * S'ᵀ) * X'ᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Minv_transpose,
      Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P.M P.Minv, M_mul_Minv, Matrix.one_mul]
  rw [e, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

lemma T_lowRankG {X' : Matrix ι r' ℝ} {V' : Matrix μ r' ℝ} (hX : X'ᵀ * X' = 1) (hV : V'ᵀ * V' = 1)
    (S' : Matrix r' r' ℝ) : X'ᵀ * P.lowRankG X' S' V' * P.M * V' = S' := by
  calc X'ᵀ * P.lowRankG X' S' V' * P.M * V'
      = (X'ᵀ * X') * S' * (V'ᵀ * ((P.Minv * P.M) * V')) := by
        simp only [lowRankG, Matrix.mul_assoc]
    _ = S' := by rw [hX, Minv_mul_M, Matrix.one_mul, Matrix.one_mul, hV, Matrix.mul_one]

lemma T_diag_lowRankG {X' : Matrix ι r' ℝ} {V' : Matrix μ r' ℝ} (hV : V'ᵀ * V' = 1)
    (c : ι → ℝ) (S' : Matrix r' r' ℝ) :
    X'ᵀ * (Matrix.diagonal c * P.lowRankG X' S' V') * P.M * V' =
      X'ᵀ * Matrix.diagonal c * X' * S' := by
  calc X'ᵀ * (Matrix.diagonal c * P.lowRankG X' S' V') * P.M * V'
      = X'ᵀ * Matrix.diagonal c * X' * S' * (V'ᵀ * ((P.Minv * P.M) * V')) := by
        simp only [lowRankG, Matrix.mul_assoc]
    _ = X'ᵀ * Matrix.diagonal c * X' * S' := by
        rw [Minv_mul_M, Matrix.one_mul, hV, Matrix.mul_one]

/-- The Schur-complement density equation is the macro equation for the full-rank update. -/
lemma macro_of_density (C : Coeff ι) {Φ ρ ρ' : ι → ℝ} {G : Matrix ι μ ℝ}
    (h : (1 / C.dt) • ρ' + (fun i => C.sigAm i * ρ' i) -
        (1 / C.eps ^ 2) • P.H (RR C * P.J ρ') =
      (1 / C.dt) • ρ + Φ - P.H (RR C * ((1 / C.dt) • G - (1 / C.eps) • (P.A G * P.Pi)))) :
    (1 / C.dt) • (ρ' - ρ) +
        P.H (Matrix.diagonal (fun i => (C.lam i)⁻¹) *
          (G - (C.dt / C.eps) • (P.A G * P.Pi) - (C.dt / C.eps ^ 2) • P.J ρ')) =
      -(fun i => C.sigAm i * ρ' i) + Φ := by
  have hdt := C.dt_pos.ne'
  have heps := C.eps_pos.ne'
  have e : Matrix.diagonal (fun i => (C.lam i)⁻¹) *
        (G - (C.dt / C.eps) • (P.A G * P.Pi) - (C.dt / C.eps ^ 2) • P.J ρ') =
      RR C * ((1 / C.dt) • G - (1 / C.eps) • (P.A G * P.Pi)) -
        (1 / C.eps ^ 2) • (RR C * P.J ρ') := by
    ext i k
    have hl := (C.lam_pos i).ne'
    have e1 : (1 / C.dt + C.sigS i / C.eps ^ 2 + C.sigA i)⁻¹ = C.dt * (C.lam i)⁻¹ := by
      have : 1 / C.dt + C.sigS i / C.eps ^ 2 + C.sigA i = C.lam i / C.dt := by
        rw [Coeff.lam]
        field_simp
      rw [this, inv_div, div_eq_mul_inv]
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_mul, RR, e1]
    field_simp
  rw [e, H_sub, H_smul]
  ext i
  have h' := congrFun h i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at h' ⊢
  linarith

section Galerkin

variable {θ CA Ωmax hmin : ℝ}

/-- The energy estimate of the S-step of arXiv 2602.12337 in arbitrary orthonormal bases `X'`, `V'`
with `1ᵀ M V' = 0`, of any size: the density is the Schur-complement density built with `G`, and
`St` is the Galerkin projection of `G`.  This contains Thm. 4.1 and covers augmented bases. -/
theorem galerkin_energy (C : Coeff ι) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hCA : 1 ≤ CA)
    (hΩ0 : 0 < Ωmax) (hΩ : ∀ j k, |P.Om j k| ≤ Ωmax) (hh0 : 0 < hmin) (hh : ∀ j, hmin ≤ P.dx j)
    (hcfl : (C.eps * CA * d / (2 * hmin) - (1 - θ) * C.sig0 / (4 * Ωmax)) * C.dt ≤
      C.eps ^ 2 / (2 * Ωmax))
    {ρ ρ' : ι → ℝ} {G : Matrix ι μ ℝ} {X' : Matrix ι r' ℝ} {St S' : Matrix r' r' ℝ}
    {V' : Matrix μ r' ℝ} (hG : G.mulVec P.w = 0) (hX : X'ᵀ * X' = 1) (hV : V'ᵀ * V' = 1)
    (hz : P.ZeroDensity V') (hSt : St = X'ᵀ * G * P.M * V')
    (hdens : (1 / C.dt) • ρ' + (fun i => C.sigAm i * ρ' i) -
        (1 / C.eps ^ 2) • P.H (RR C * P.J ρ') =
      (1 / C.dt) • ρ + 0 - P.H (RR C * ((1 / C.dt) • G - (1 / C.eps) • (P.A G * P.Pi))))
    (hS : (1 / C.dt) • (S' - St) =
      -(1 / C.eps) • (X'ᵀ * P.B (X' * St * V'ᵀ) * V') -
        (1 / C.eps ^ 2) • (X'ᵀ * P.J ρ' * P.M * V') -
        (1 / C.eps ^ 2) • (X'ᵀ * Matrix.diagonal C.sigS * X' * S') -
        X'ᵀ * Matrix.diagonal C.sigA * X' * S') :
    P.energy C θ ρ' (P.lowRankG X' S' V') ≤ P.energy C θ ρ G := by
  have hdt := C.dt_pos.ne'
  have heps := C.eps_pos.ne'
  set Gt := P.lowRankG X' St V' with hGt
  set G' := P.lowRankG X' S' V' with hG'
  have hmac := P.macro_of_density C hdens
  rw [add_zero] at hmac
  refine P.schur_energy_core (Gt := Gt) C hθ0 hθ1 hCA hΩ0 hΩ hh0 hh hcfl hG
    (P.mulVec_w_lowRankG hz) ?_ hmac ?_
  · -- `G̃` is the `⟨·,·⟩_w`-orthogonal projection of `G`
    rw [P.ipw_comm, hGt, ipw_lowRankG]
    have e : X'ᵀ * (G - P.lowRankG X' St V') * P.M * V' = 0 := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, P.T_lowRankG hX hV, hSt, sub_self]
    rw [e]
    simp
  · -- the tested S-step
    have hW : X'ᵀ * (Matrix.diagonal C.lam * G' -
        (Gt - (C.dt / C.eps) • (P.A Gt * P.Pi) - (C.dt / C.eps ^ 2) • P.J ρ')) * P.M * V' = 0 := by
      have e1 : Matrix.diagonal C.lam = 1 + (C.dt / C.eps ^ 2) • Matrix.diagonal C.sigS +
          C.dt • Matrix.diagonal C.sigA := by
        ext i l
        by_cases h : i = l
        · subst h
          simp [Coeff.lam, Matrix.add_apply, Matrix.smul_apply]
          ring
        · simp [h, Matrix.add_apply, Matrix.smul_apply]
      set Y₁ := X'ᵀ * P.B (X' * St * V'ᵀ) * V' with hY₁
      set Y₂ := X'ᵀ * P.J ρ' * P.M * V' with hY₂
      set Y₃ := X'ᵀ * Matrix.diagonal C.sigS * X' * S' with hY₃
      set Y₄ := X'ᵀ * Matrix.diagonal C.sigA * X' * S' with hY₄
      have hS' : S' - St = -((C.dt / C.eps) • Y₁) - (C.dt / C.eps ^ 2) • Y₂ -
          (C.dt / C.eps ^ 2) • Y₃ - C.dt • Y₄ := by
        ext a b
        have h' := congrFun (congrFun hS a) b
        simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply] at h' ⊢
        field_simp at h' ⊢
        linarith
      have hY₁' : X'ᵀ * (P.A Gt * P.Pi) * P.M * V' = Y₁ := by
        simp only [hY₁, B, hGt, lowRankG, Matrix.mul_assoc]
      have hlam : X'ᵀ * Matrix.diagonal C.lam * X' * S' =
          S' + (C.dt / C.eps ^ 2) • Y₃ + C.dt • Y₄ := by
        rw [e1]
        simp only [hY₃, hY₄, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul,
          Matrix.smul_mul, hX, Matrix.one_mul]
      have eT : X'ᵀ * (Matrix.diagonal C.lam * G' -
          (Gt - (C.dt / C.eps) • (P.A Gt * P.Pi) - (C.dt / C.eps ^ 2) • P.J ρ')) * P.M * V' =
          X'ᵀ * Matrix.diagonal C.lam * X' * S' - St + (C.dt / C.eps) • Y₁ +
            (C.dt / C.eps ^ 2) • Y₂ := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
        rw [hG', P.T_diag_lowRankG hV, hGt, P.T_lowRankG hX hV, ← hGt, hY₁']
        abel
      rw [eT, hlam]
      calc S' + (C.dt / C.eps ^ 2) • Y₃ + C.dt • Y₄ - St + (C.dt / C.eps) • Y₁ +
            (C.dt / C.eps ^ 2) • Y₂
          = (S' - St) + (C.dt / C.eps ^ 2) • Y₃ + C.dt • Y₄ + (C.dt / C.eps) • Y₁ +
            (C.dt / C.eps ^ 2) • Y₂ := by abel
        _ = 0 := by rw [hS']; abel
    have : P.ipw (Matrix.diagonal C.lam * G' -
        (Gt - (C.dt / C.eps) • (P.A Gt * P.Pi) - (C.dt / C.eps ^ 2) • P.J ρ')) G' = 0 := by
      rw [hG', ipw_lowRankG, ← hG', hW]
      simp
    rw [ipw_sub_left] at this
    linarith

/-- One step of the IMEX-S-BUG integrator of Sec. 4.1 of arXiv 2602.12337, with `G M = X S Vᵀ`: the
density from the Schur complement built with the low-rank `Gⁿ`, the K- and L-step with `ρ'`, the new
bases (`X'`, `V'` are the QR factors of `K'`, `L'`, in the basis of Sec. 4.3 for `V'`), and the
S-step with `S̃ = X'ᵀ X S Vᵀ V'`.  The new rank `r'` is free. -/
structure IsIMEXSBUGStep (C : Coeff ι) (Φ ρ : ι → ℝ) (X : Matrix ι r ℝ) (S : Matrix r r ℝ)
    (V : Matrix μ r ℝ) (ρ' : ι → ℝ) (K' : Matrix ι r ℝ) (L' : Matrix μ r ℝ)
    (X' : Matrix ι r' ℝ) (S' : Matrix r' r' ℝ) (V' : Matrix μ r' ℝ) : Prop where
  density : (1 / C.dt) • ρ' + (fun i => C.sigAm i * ρ' i) -
      (1 / C.eps ^ 2) • P.H (RR C * P.J ρ') =
    (1 / C.dt) • ρ + Φ - P.H (RR C * ((1 / C.dt) • P.lowRankG X S V -
      (1 / C.eps) • (P.A (P.lowRankG X S V) * P.Pi)))
  kStep : (1 / C.dt) • (K' - X * S) =
    -(1 / C.eps) • (P.B (X * S * Vᵀ) * V) - (1 / C.eps ^ 2) • (P.J ρ' * P.M * V) -
      (1 / C.eps ^ 2) • (Matrix.diagonal C.sigS * K') - Matrix.diagonal C.sigA * K'
  lStep : (1 / C.dt) • (L' - V * Sᵀ) =
    -(1 / C.eps) • ((P.B (X * S * Vᵀ))ᵀ * X) - (1 / C.eps ^ 2) • (P.M * (P.J ρ')ᵀ * X) -
      (1 / C.eps ^ 2) • (L' * (Xᵀ * Matrix.diagonal C.sigS * X)) -
      L' * (Xᵀ * Matrix.diagonal C.sigA * X)
  orthX' : X'ᵀ * X' = 1
  orthV' : V'ᵀ * V' = 1
  capK : ∃ T : Matrix r' r ℝ, K' = X' * T
  capL : ∃ T : Matrix r' r ℝ, L' = V' * T
  zeroV' : P.ZeroDensity V'
  sStep : (1 / C.dt) • (S' - X'ᵀ * X * S * Vᵀ * V') =
    -(1 / C.eps) • (X'ᵀ * P.B (X' * (X'ᵀ * X * S * Vᵀ * V') * V'ᵀ) * V') -
      (1 / C.eps ^ 2) • (X'ᵀ * P.J ρ' * P.M * V') -
      (1 / C.eps ^ 2) • (X'ᵀ * Matrix.diagonal C.sigS * X' * S') -
      X'ᵀ * Matrix.diagonal C.sigA * X' * S'

/-- **Thm. 4.1** (arXiv 2602.12337).  For `Φ = 0`, the scheme IMEX-S-BUG with the energy-consistent
factorization `G M = X S Vᵀ` is `θ`-stable under the CFL condition (3.11) of IMEX-S.  The scheme is
the one of the paper, with the Schur-complement density and the zero-density constraint
`1ᵀ M V = 0` of Sec. 4.3 (assumed for `Vⁿ`, part of the step for `Vⁿ⁺¹`).  The proof of the paper
does not apply to this density, see the module docstring; this one is `galerkin_energy`. -/
theorem theorem_4_1 (C : Coeff ι) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hCA : 1 ≤ CA)
    (hΩ0 : 0 < Ωmax) (hΩ : ∀ j k, |P.Om j k| ≤ Ωmax) (hh0 : 0 < hmin) (hh : ∀ j, hmin ≤ P.dx j)
    (hcfl : (C.eps * CA * d / (2 * hmin) - (1 - θ) * C.sig0 / (4 * Ωmax)) * C.dt ≤
      C.eps ^ 2 / (2 * Ωmax))
    {ρ ρ' : ι → ℝ} {X : Matrix ι r ℝ} {S : Matrix r r ℝ} {V : Matrix μ r ℝ}
    {K' : Matrix ι r ℝ} {L' : Matrix μ r ℝ} {X' : Matrix ι r' ℝ} {S' : Matrix r' r' ℝ}
    {V' : Matrix μ r' ℝ} (hz : P.ZeroDensity V)
    (hstep : P.IsIMEXSBUGStep C 0 ρ X S V ρ' K' L' X' S' V') :
    P.energy C θ ρ' (P.lowRankG X' S' V') ≤ P.energy C θ ρ (P.lowRankG X S V) := by
  refine P.galerkin_energy C hθ0 hθ1 hCA hΩ0 hΩ hh0 hh hcfl (P.mulVec_w_lowRankG hz)
    hstep.orthX' hstep.orthV' hstep.zeroV' ?_ hstep.density hstep.sStep
  calc X'ᵀ * X * S * Vᵀ * V' = X'ᵀ * (X * (S * (Vᵀ * V'))) := by simp only [Matrix.mul_assoc]
    _ = X'ᵀ * (X * (S * (Vᵀ * ((P.Minv * P.M) * V')))) := by rw [Minv_mul_M, Matrix.one_mul]
    _ = X'ᵀ * P.lowRankG X S V * P.M * V' := by simp only [lowRankG, Matrix.mul_assoc]

/-- **Thm. 4.1** (arXiv 2602.12337) in the form of Definition 3.1: `E_θⁿ⁺¹ ≤ E_θⁿ` for all `n`. -/
theorem theorem_4_1_trajectory (C : Coeff ι) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hCA : 1 ≤ CA)
    (hΩ0 : 0 < Ωmax) (hΩ : ∀ j k, |P.Om j k| ≤ Ωmax) (hh0 : 0 < hmin) (hh : ∀ j, hmin ≤ P.dx j)
    (hcfl : (C.eps * CA * d / (2 * hmin) - (1 - θ) * C.sig0 / (4 * Ωmax)) * C.dt ≤
      C.eps ^ 2 / (2 * Ωmax))
    {ρ : ℕ → ι → ℝ} {X : ℕ → Matrix ι r ℝ} {S : ℕ → Matrix r r ℝ} {V : ℕ → Matrix μ r ℝ}
    {K : ℕ → Matrix ι r ℝ} {L : ℕ → Matrix μ r ℝ} (h0 : P.ZeroDensity (V 0))
    (hstep : ∀ n, P.IsIMEXSBUGStep C 0 (ρ n) (X n) (S n) (V n) (ρ (n + 1)) (K n) (L n)
      (X (n + 1)) (S (n + 1)) (V (n + 1))) (n : ℕ) :
    P.energy C θ (ρ (n + 1)) (P.lowRankG (X (n + 1)) (S (n + 1)) (V (n + 1))) ≤
      P.energy C θ (ρ n) (P.lowRankG (X n) (S n) (V n)) := by
  have hz : P.ZeroDensity (V n) := by
    cases n with
    | zero => exact h0
    | succ n => exact (hstep n).zeroV'
  exact P.theorem_4_1 C hθ0 hθ1 hCA hΩ0 hΩ hh0 hh hcfl hz (hstep n)

end Galerkin

/-! ### Sec. 4.3: the zero-density constraint -/

private lemma quad_nonneg {X : Matrix ι r ℝ} {D : ι → ℝ} (hD : ∀ i, 0 ≤ D i) (l : r → ℝ) :
    0 ≤ Matrix.vecMul l (Xᵀ * Matrix.diagonal D * X) ⬝ᵥ l := by
  have e : Matrix.vecMul l (Xᵀ * Matrix.diagonal D * X) ⬝ᵥ l =
      X.mulVec l ⬝ᵥ (Matrix.diagonal D).mulVec (X.mulVec l) := by
    rw [← Matrix.dotProduct_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rw [e]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [Matrix.mulVec_diagonal]
  have := mul_nonneg (hD i) (mul_self_nonneg (X.mulVec l i))
  nlinarith

lemma zeroDensity_iff_vecMul {r : Type*} (Y : Matrix μ r ℝ) :
    P.ZeroDensity Y ↔ Matrix.vecMul (fun k => √(P.w k)) Y = 0 := by
  have e : Matrix.vecMul (fun _ => (1 : ℝ)) P.M = fun k => √(P.w k) := by
    ext k
    simp [M, Matrix.vecMul_diagonal]
  rw [ZeroDensity, ← Matrix.vecMul_vecMul, e]

lemma M_mulVec_sqrt : P.M.mulVec (fun k => √(P.w k)) = P.w := by
  ext k
  rw [M, Matrix.mulVec_diagonal]
  exact Real.mul_self_sqrt (P.w_pos k).le

lemma vecMul_sqrt_M : Matrix.vecMul (fun k => √(P.w k)) P.M = P.w := by
  ext k
  rw [M, Matrix.vecMul_diagonal]
  exact Real.mul_self_sqrt (P.w_pos k).le

lemma B_mulVec_sqrt (Y : Matrix ι μ ℝ) : (P.B Y).mulVec (fun k => √(P.w k)) = 0 := by
  rw [B, ← Matrix.mulVec_mulVec, M_mulVec_sqrt, mul_Pi_mulVec_w]

/-- **Sec. 4.3** (arXiv 2602.12337).  If `1ᵀ M Lⁿ = 0`, then the L-step keeps `1ᵀ M Lⁿ⁺¹ = 0`,
whatever the argument `Y` of `ℬ`, the density and the basis `X`. -/
theorem zeroDensity_lStep (C : Coeff ι) {X : Matrix ι r ℝ} {Y : Matrix ι μ ℝ} {ρ' : ι → ℝ}
    {L L' : Matrix μ r ℝ} (hL : P.ZeroDensity L)
    (hstep : (1 / C.dt) • (L' - L) =
      -(1 / C.eps) • ((P.B Y)ᵀ * X) - (1 / C.eps ^ 2) • (P.M * (P.J ρ')ᵀ * X) -
        (1 / C.eps ^ 2) • (L' * (Xᵀ * Matrix.diagonal C.sigS * X)) -
        L' * (Xᵀ * Matrix.diagonal C.sigA * X)) :
    P.ZeroDensity L' := by
  have hdt := C.dt_pos
  have heps := C.eps_pos
  rw [zeroDensity_iff_vecMul] at hL ⊢
  set m : μ → ℝ := fun k => √(P.w k) with hm
  set l := Matrix.vecMul m L' with hl
  have h1 := congrArg (Matrix.vecMul m) hstep
  have hb : Matrix.vecMul m ((P.B Y)ᵀ * X) = 0 := by
    rw [← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, B_mulVec_sqrt, Matrix.zero_vecMul]
  have hj : Matrix.vecMul m (P.M * (P.J ρ')ᵀ * X) = 0 := by
    rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, vecMul_sqrt_M, Matrix.vecMul_transpose,
      J_mulVec_w, Matrix.zero_vecMul]
  have hs : ∀ Z : Matrix r r ℝ, Matrix.vecMul m (L' * Z) = Matrix.vecMul l Z := fun Z => by
    rw [hl, Matrix.vecMul_vecMul]
  simp only [Matrix.vecMul_sub, Matrix.vecMul_smul, hb, hj, hs, hL, smul_zero, sub_zero] at h1
  have h2 := congrArg (fun x => x ⬝ᵥ l) h1
  simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul, zero_dotProduct] at h2
  have q1 := quad_nonneg (X := X) C.sigA_nonneg l
  have q2 : 0 ≤ Matrix.vecMul l (Xᵀ * Matrix.diagonal C.sigS * X) ⬝ᵥ l :=
    quad_nonneg (fun i => C.sig0_pos.le.trans (C.sig0_le i)) l
  have q3 : 0 ≤ 1 / C.eps ^ 2 * Matrix.vecMul l (Xᵀ * Matrix.diagonal C.sigS * X) ⬝ᵥ l :=
    mul_nonneg (by positivity) q2
  have q4 : l ⬝ᵥ l ≤ 0 := by
    have : 1 / C.dt * (l ⬝ᵥ l) ≤ 0 := by linarith
    have hp : 0 < 1 / C.dt := by positivity
    by_contra hc
    have : 0 < 1 / C.dt * (l ⬝ᵥ l) := mul_pos hp (not_le.1 hc)
    linarith
  have q5 : l ⬝ᵥ l = 0 := le_antisymm q4 (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
  exact dotProduct_self_eq_zero.1 q5

private lemma mulVec_transpose_mulVec_of_dot_eq_zero {κ : Type*} [Fintype κ] [DecidableEq κ]
    {Z : Matrix μ κ ℝ} (hZ : Zᵀ * Z = 1) (hZ1 : P.ZeroDensity Z)
    (hcard : Fintype.card κ + 1 = Fintype.card μ) {c : μ → ℝ}
    (hc : (fun k => √(P.w k)) ⬝ᵥ c = 0) : Z.mulVec (Zᵀ.mulVec c) = c := by
  rw [zeroDensity_iff_vecMul] at hZ1
  set m : μ → ℝ := fun k => √(P.w k) with hm
  let φ : (μ → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x => m ⬝ᵥ x
      map_add' := dotProduct_add m
      map_smul' := fun a x => by simp [dotProduct_smul] }
  have hφ : ∀ x, φ x = m ⬝ᵥ x := fun _ => rfl
  have hmm : φ m = P.DOm := by
    rw [hφ, ← P.sum_w]
    exact Finset.sum_congr rfl fun k _ => Real.mul_self_sqrt (P.w_pos k).le
  have hsurj : LinearMap.range φ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    refine ⟨(y / P.DOm) • m, ?_⟩
    rw [map_smul, hmm, smul_eq_mul]
    have := P.DOm_pos.ne'
    field_simp
  have hker : Module.finrank ℝ (LinearMap.ker φ) + 1 = Fintype.card μ := by
    have h := LinearMap.finrank_range_add_finrank_ker φ
    rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_fintype_fun_eq_card] at h
    omega
  have hinj : Function.Injective Z.mulVecLin := by
    intro x y hxy
    have h := congrArg (Zᵀ.mulVec) hxy
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hZ] using h
  have hrange : Module.finrank ℝ (LinearMap.range Z.mulVecLin) = Fintype.card κ := by
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card]
  have hle : LinearMap.range Z.mulVecLin ≤ LinearMap.ker φ := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker, hφ, Matrix.mulVecLin_apply, Matrix.dotProduct_mulVec, hZ1,
      zero_dotProduct]
  have heq : LinearMap.range Z.mulVecLin = LinearMap.ker φ :=
    Submodule.eq_of_le_of_finrank_eq hle (by omega)
  have hmem : c ∈ LinearMap.range Z.mulVecLin := by
    rw [heq, LinearMap.mem_ker, hφ]
    exact hc
  obtain ⟨v, rfl⟩ := hmem
  simp [Matrix.mulVec_mulVec, hZ]

/-- **Sec. 4.3** (arXiv 2602.12337).  Let `Z` have `N_Ω - 1` orthonormal columns with
`1ᵀ M Z = 0`, and let `Zᵀ Lⁿ⁺¹ = Q̃ R̃` be a QR factorization.  Then `Vⁿ⁺¹ = Z Q̃` is orthonormal,
satisfies the constraint `1ᵀ M Vⁿ⁺¹ = 0` by construction, and `Lⁿ⁺¹ = Vⁿ⁺¹ R̃`.  The last claim uses
`1ᵀ M Lⁿ⁺¹ = 0`, which the paper states and which replaces its step `Lⁿ⁺¹ = Z Zᵀ Lⁿ⁺¹`. -/
theorem zeroDensity_qr {κ : Type*} [Fintype κ] [DecidableEq κ] {Z : Matrix μ κ ℝ}
    (hZ : Zᵀ * Z = 1) (hZ1 : P.ZeroDensity Z) (hcard : Fintype.card κ + 1 = Fintype.card μ)
    {L' : Matrix μ r ℝ} (hL : P.ZeroDensity L') {Qt : Matrix κ r ℝ} {Rt : Matrix r r ℝ}
    (hQ : Qtᵀ * Qt = 1) (hqr : Zᵀ * L' = Qt * Rt) :
    (Z * Qt)ᵀ * (Z * Qt) = 1 ∧ P.ZeroDensity (Z * Qt) ∧ L' = (Z * Qt) * Rt := by
  refine ⟨?_, ?_, ?_⟩
  · calc (Z * Qt)ᵀ * (Z * Qt) = Qtᵀ * ((Zᵀ * Z) * Qt) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hZ, Matrix.one_mul, hQ]
  · rw [zeroDensity_iff_vecMul] at hZ1 ⊢
    rw [← Matrix.vecMul_vecMul, hZ1, Matrix.zero_vecMul]
  · rw [zeroDensity_iff_vecMul] at hL
    have h : ∀ c, Z.mulVec (Zᵀ.mulVec fun k => L' k c) = fun k => L' k c := by
      intro c
      refine P.mulVec_transpose_mulVec_of_dot_eq_zero hZ hZ1 hcard ?_
      exact congrFun hL c
    rw [Matrix.mul_assoc, ← hqr]
    ext k c
    exact (congrFun (h c) k).symm

/-! ### Well-posedness of the implicit steps -/

lemma J_add (f₁ f₂ : ι → ℝ) : P.J (f₁ + f₂) = P.J f₁ + P.J f₂ := by
  ext i k
  simp only [J_apply, Matrix.add_apply, Matrix.mulVec_add, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]

lemma J_smul (c : ℝ) (f : ι → ℝ) : P.J (c • f) = c • P.J f := by
  ext i k
  simp only [J_apply, Matrix.smul_apply, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma RR_entry_pos (C : Coeff ι) (i : ι) :
    0 < (1 / C.dt + C.sigS i / C.eps ^ 2 + C.sigA i)⁻¹ := by
  have h1 := C.dt_pos
  have h2 := C.sigA_nonneg i
  have h3 : 0 ≤ C.sigS i := C.sig0_pos.le.trans (C.sig0_le i)
  have h4 : 0 ≤ C.sigS i / C.eps ^ 2 := by positivity
  have h5 : 0 < 1 / C.dt := by positivity
  exact inv_pos.2 (by linarith)

/-- The Schur complement of Sec. 3.1 of arXiv 2602.12337 is invertible: the density equation of
IMEX-S and IMEX-S-BUG has a unique solution for every right-hand side. -/
theorem existsUnique_density (C : Coeff ι) (b : ι → ℝ) :
    ∃! ρ' : ι → ℝ, (1 / C.dt) • ρ' + (fun i => C.sigAm i * ρ' i) -
      (1 / C.eps ^ 2) • P.H (RR C * P.J ρ') = b := by
  have hdt := C.dt_pos
  have heps := C.eps_pos
  have hD := P.DOm_pos
  let T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
    { toFun := fun f => (1 / C.dt) • f + (fun i => C.sigAm i * f i) -
        (1 / C.eps ^ 2) • P.H (RR C * P.J f)
      map_add' := fun f g => by
        have e : (fun i => C.sigAm i * (f + g) i) =
            (fun i => C.sigAm i * f i) + fun i => C.sigAm i * g i := by
          ext i
          simp [mul_add]
        rw [J_add, Matrix.mul_add, H_add, e, smul_add, smul_add]
        abel
      map_smul' := fun a f => by
        have e : (fun i => C.sigAm i * (a • f) i) = a • (fun i => C.sigAm i * f i) := by
          ext i
          simp only [Pi.smul_apply, smul_eq_mul]
          ring
        rw [J_smul, Matrix.mul_smul, H_smul, e, RingHom.id_apply, smul_sub, smul_add,
          smul_comm a (1 / C.dt), smul_comm a (1 / C.eps ^ 2)] }
  have hT : ∀ f, T f = (1 / C.dt) • f + (fun i => C.sigAm i * f i) -
      (1 / C.eps ^ 2) • P.H (RR C * P.J f) := fun _ => rfl
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    have h := congrArg (P.ipv f) hf
    rw [hT, ipv_sub_right, ipv_add_right, ipv_smul_right, ipv_smul_right] at h
    have hab := P.ipv_absorb_nonneg C.sigAm_nonneg f
    have hsb := P.sbp_H_J f (RR C * P.J f)
    have hq : 0 ≤ P.ipw (P.J f) (RR C * P.J f) := by
      rw [RR, ← ipw_dg_comm]
      exact P.ipw_dg_nonneg (fun i => (RR_entry_pos C i).le) _
    have hz : P.ipv f 0 = 0 := by simp [ipv]
    rw [hz] at h
    have hp : 0 ≤ P.ipv f f := P.ipv_self_nonneg f
    have hH : P.ipv f (P.H (RR C * P.J f)) ≤ 0 := by
      have : P.DOm * P.ipv f (P.H (RR C * P.J f)) ≤ 0 := by linarith
      by_contra hc
      have := mul_pos hD (not_le.1 hc)
      linarith
    have h1 : 0 ≤ -(1 / C.eps ^ 2 * P.ipv f (P.H (RR C * P.J f))) := by
      have : 1 / C.eps ^ 2 * P.ipv f (P.H (RR C * P.J f)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hH
      linarith
    have h2 : 1 / C.dt * P.ipv f f ≤ 0 := by linarith
    have h3 : P.ipv f f ≤ 0 := by
      by_contra hc
      have : 0 < 1 / C.dt * P.ipv f f := mul_pos (by positivity) (not_le.1 hc)
      linarith
    have h4 : f ⬝ᵥ f = 0 := by
      have h5 : P.ipv f f = 0 := le_antisymm h3 hp
      have h6 : P.vol * (f ⬝ᵥ f) = 0 := h5
      exact (mul_eq_zero.1 h6).resolve_left P.vol_pos.ne'
    exact dotProduct_self_eq_zero.1 h4
  have hsurj : Function.Surjective T := LinearMap.injective_iff_surjective.1 hinj
  obtain ⟨f, hf⟩ := hsurj b
  exact ⟨f, hf, fun g hg => hinj (hg.trans hf.symm)⟩

/-- Non-vacuity: the implicit scheme (3.8) of arXiv 2602.12337 has a solution for all data. -/
theorem exists_imexSStep (C : Coeff ι) (Φ ρ : ι → ℝ) (G : Matrix ι μ ℝ) :
    ∃ ρ' G', P.IsIMEXSStep C Φ ρ G ρ' G' := by
  have hdt := C.dt_pos.ne'
  have heps := C.eps_pos.ne'
  obtain ⟨ρ', hρ', -⟩ := P.existsUnique_density C
    ((1 / C.dt) • ρ + Φ - P.H (RR C * ((1 / C.dt) • G - (1 / C.eps) • (P.A G * P.Pi))))
  set G' := RR C * ((1 / C.dt) • G - (1 / C.eps) • (P.A G * P.Pi) - (1 / C.eps ^ 2) • P.J ρ')
    with hG'
  refine ⟨ρ', G', ?_, ?_⟩
  · have e : G' = RR C * ((1 / C.dt) • G - (1 / C.eps) • (P.A G * P.Pi)) -
        (1 / C.eps ^ 2) • (RR C * P.J ρ') := by
      rw [hG', Matrix.mul_sub, Matrix.mul_smul]
    rw [e, H_sub, H_smul]
    ext i
    have h' := congrFun hρ' i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at h' ⊢
    field_simp at h' ⊢
    linarith
  · ext i k
    have hl : 1 / C.dt + C.sigS i / C.eps ^ 2 + C.sigA i ≠ 0 := (inv_pos.1 (RR_entry_pos C i)).ne'
    have e : G' i k = (1 / C.dt + C.sigS i / C.eps ^ 2 + C.sigA i)⁻¹ *
        ((1 / C.dt) * G i k - (1 / C.eps) * (P.A G * P.Pi) i k -
          (1 / C.eps ^ 2) * P.J ρ' i k) := by
      simp only [hG', RR, Matrix.diagonal_mul, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    have e' : (1 / C.dt + C.sigS i / C.eps ^ 2 + C.sigA i) * G' i k =
        (1 / C.dt) * G i k - (1 / C.eps) * (P.A G * P.Pi) i k -
          (1 / C.eps ^ 2) * P.J ρ' i k := by
      rw [e, mul_inv_cancel_left₀ hl]
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.diagonal_mul]
    have e'' : 1 / C.dt * (G' i k - G i k) + 1 / C.eps * (P.A G * P.Pi) i k =
        -(1 / C.eps ^ 2) * P.J ρ' i k - 1 / C.eps ^ 2 * (C.sigS i * G' i k) -
          C.sigA i * G' i k := by
      have e3 : (1 / C.dt + C.sigS i / C.eps ^ 2 + C.sigA i) * G' i k =
          1 / C.dt * G' i k + 1 / C.eps ^ 2 * (C.sigS i * G' i k) + C.sigA i * G' i k := by
        ring
      rw [e3] at e'
      linarith
    exact e''

private lemma step_rearrange {E : Type*} [AddCommGroup E] {x y z w R : E}
    (h : x + y + z = w + R) : x - w = R - y - z := by
  have e : x - w = (x + y + z) - w - y - z := by abel
  rw [e, h]
  abel

/-- The implicit part of the L- and S-steps is invertible. -/
private lemma isUnit_stiff {q : Type*} [Fintype q] [DecidableEq q] (C : Coeff ι)
    (X : Matrix ι q ℝ) :
    IsUnit ((1 / C.dt) • (1 : Matrix q q ℝ) +
      (1 / C.eps ^ 2) • (Xᵀ * Matrix.diagonal C.sigS * X) +
        Xᵀ * Matrix.diagonal C.sigA * X) := by
  have hdt := C.dt_pos
  have heps := C.eps_pos
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro a b hab
  have hab' : a - b = 0 := by
    set A := (1 / C.dt) • (1 : Matrix q q ℝ) +
      (1 / C.eps ^ 2) • (Xᵀ * Matrix.diagonal C.sigS * X) + Xᵀ * Matrix.diagonal C.sigA * X
      with hA
    set l := a - b with hl
    have h0 : A.mulVec l = 0 := by
      rw [hl, Matrix.mulVec_sub, sub_eq_zero]
      exact hab
    have h1 : l ⬝ᵥ A.mulVec l = 0 := by rw [h0, dotProduct_zero]
    rw [Matrix.dotProduct_mulVec, hA] at h1
    simp only [Matrix.vecMul_add, Matrix.vecMul_smul, Matrix.vecMul_one, add_dotProduct,
      smul_dotProduct, smul_eq_mul] at h1
    have q1 : 0 ≤ Matrix.vecMul l (Xᵀ * Matrix.diagonal C.sigA * X) ⬝ᵥ l :=
      quad_nonneg C.sigA_nonneg l
    have q2 : 0 ≤ Matrix.vecMul l (Xᵀ * Matrix.diagonal C.sigS * X) ⬝ᵥ l :=
      quad_nonneg (fun i => C.sig0_pos.le.trans (C.sig0_le i)) l
    have q3 : 0 ≤ 1 / C.eps ^ 2 * Matrix.vecMul l (Xᵀ * Matrix.diagonal C.sigS * X) ⬝ᵥ l :=
      mul_nonneg (by positivity) q2
    have q4 : l ⬝ᵥ l ≤ 0 := by
      have : 1 / C.dt * (l ⬝ᵥ l) ≤ 0 := by linarith
      by_contra hc
      have : 0 < 1 / C.dt * (l ⬝ᵥ l) := mul_pos (by positivity) (not_le.1 hc)
      linarith
    exact dotProduct_self_eq_zero.1
      (le_antisymm q4 (Finset.sum_nonneg fun i _ => mul_self_nonneg _))
  exact sub_eq_zero.1 hab'

/-- The K-step is solved by the resolvent `R`. -/
private lemma solve_diag {q : Type*} [Fintype q] (C : Coeff ι) (W : Matrix ι q ℝ) :
    (1 / C.dt) • (RR C * W) + (1 / C.eps ^ 2) • (Matrix.diagonal C.sigS * (RR C * W)) +
      Matrix.diagonal C.sigA * (RR C * W) = W := by
  ext i k
  have hl : 1 / C.dt + C.sigS i / C.eps ^ 2 + C.sigA i ≠ 0 := (inv_pos.1 (RR_entry_pos C i)).ne'
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_mul, RR]
  have e : ∀ t : ℝ, 1 / C.dt * (t * W i k) + 1 / C.eps ^ 2 * (C.sigS i * (t * W i k)) +
      C.sigA i * (t * W i k) =
        (1 / C.dt + C.sigS i / C.eps ^ 2 + C.sigA i) * t * W i k := fun t => by ring
  rw [e, mul_inv_cancel₀ hl, one_mul]

lemma zeroDensity_mul {q q' : Type*} [Fintype q] {V : Matrix μ q ℝ} (hz : P.ZeroDensity V)
    (T : Matrix q q' ℝ) : P.ZeroDensity (V * T) := by
  rw [zeroDensity_iff_vecMul] at hz ⊢
  rw [← Matrix.vecMul_vecMul, hz, Matrix.zero_vecMul]

/-- A zero-density matrix has its columns in the orthogonal complement of `M 1`: a QR factor with
the same property exists. -/
private lemma exists_zeroDensity_capture {s : ℕ} (hs : s + 1 ≤ Fintype.card μ)
    {L : Matrix μ (Fin s) ℝ} (hL : P.ZeroDensity L) :
    ∃ U : Matrix μ (Fin s) ℝ, Uᵀ * U = 1 ∧ P.ZeroDensity U ∧ ∃ T : Matrix (Fin s) (Fin s) ℝ,
      L = U * T := by
  have hD := P.DOm_pos
  have hsq : 0 < √P.DOm := Real.sqrt_pos.2 hD
  have hL' := (P.zeroDensity_iff L).1 hL
  set U₀ : Matrix μ Unit ℝ := Matrix.of fun k _ => √(P.w k) / √P.DOm with hU₀
  have hU : U₀ᵀ * U₀ = 1 := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hU₀, Matrix.of_apply,
      Matrix.one_apply_eq, Unit.ext a b]
    have : ∀ k, √(P.w k) / √P.DOm * (√(P.w k) / √P.DOm) = P.w k / P.DOm := by
      intro k
      rw [div_mul_div_comm, Real.mul_self_sqrt (P.w_pos k).le, Real.mul_self_sqrt hD.le]
    simp only [this, ← Finset.sum_div, P.sum_w]
    exact div_self hD.ne'
  have hUL : U₀ᵀ * L = 0 := by
    ext a c
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hU₀, Matrix.of_apply, Matrix.zero_apply]
    have e : ∑ k, √(P.w k) / √P.DOm * L k c = (∑ k, √(P.w k) * L k c) / √P.DOm := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e, hL', zero_div]
  have hproj : (1 - U₀ * U₀ᵀ) * L = L := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hUL, Matrix.mul_zero, sub_zero]
  obtain ⟨U, hUU, hUU₀, hcap⟩ := exists_orthonormal_capture_compl U₀ hU L
    (s := s) (by rw [hproj]; simpa using L.rank_le_card_width)
    (by rw [Fintype.card_unit]; omega)
  rw [hproj] at hcap
  refine ⟨U, hUU, ?_, Uᵀ * L, ?_⟩
  · rw [zeroDensity_iff]
    intro c
    have h := congrFun (congrFun hUU₀ c) ()
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hU₀, Matrix.of_apply,
      Matrix.zero_apply] at h
    have e : ∑ k, U k c * (√(P.w k) / √P.DOm) = (∑ k, √(P.w k) * U k c) / √P.DOm := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e, div_eq_zero_iff] at h
    exact h.resolve_right hsq.ne'
  · rw [← Matrix.mul_assoc, hcap]

/-- Non-vacuity: an IMEX-S-BUG step of arXiv 2602.12337 exists for all data of rank `s` with
`1ᵀ M V = 0`, if `s ≤ N_g` and `s + 1 ≤ N_Ω`. -/
theorem exists_imexSBUGStep (C : Coeff ι) (Φ ρ : ι → ℝ) {s : ℕ} (hs : s ≤ Fintype.card ι)
    (hs' : s + 1 ≤ Fintype.card μ) (X : Matrix ι (Fin s) ℝ) (S : Matrix (Fin s) (Fin s) ℝ)
    (V : Matrix μ (Fin s) ℝ) (hz : P.ZeroDensity V) :
    ∃ (ρ' : ι → ℝ) (K' : Matrix ι (Fin s) ℝ) (L' : Matrix μ (Fin s) ℝ)
      (X' : Matrix ι (Fin s) ℝ) (S' : Matrix (Fin s) (Fin s) ℝ) (V' : Matrix μ (Fin s) ℝ),
      P.IsIMEXSBUGStep C Φ ρ X S V ρ' K' L' X' S' V' := by
  set G := P.lowRankG X S V with hG
  obtain ⟨ρ', hρ', -⟩ := P.existsUnique_density C
    ((1 / C.dt) • ρ + Φ - P.H (RR C * ((1 / C.dt) • G - (1 / C.eps) • (P.A G * P.Pi))))
  -- the K-step
  set WK := (1 / C.dt) • (X * S) + (-(1 / C.eps) • (P.B (X * S * Vᵀ) * V) -
    (1 / C.eps ^ 2) • (P.J ρ' * P.M * V)) with hWK
  set K' := RR C * WK with hK'
  have hkStep : (1 / C.dt) • (K' - X * S) =
      -(1 / C.eps) • (P.B (X * S * Vᵀ) * V) - (1 / C.eps ^ 2) • (P.J ρ' * P.M * V) -
        (1 / C.eps ^ 2) • (Matrix.diagonal C.sigS * K') - Matrix.diagonal C.sigA * K' := by
    rw [smul_sub]
    exact step_rearrange (solve_diag C WK)
  -- the L-step
  set A := (1 / C.dt) • (1 : Matrix (Fin s) (Fin s) ℝ) +
    (1 / C.eps ^ 2) • (Xᵀ * Matrix.diagonal C.sigS * X) + Xᵀ * Matrix.diagonal C.sigA * X
    with hA
  have hAu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 (isUnit_stiff C X)
  set WL := (1 / C.dt) • (V * Sᵀ) + (-(1 / C.eps) • ((P.B (X * S * Vᵀ))ᵀ * X) -
    (1 / C.eps ^ 2) • (P.M * (P.J ρ')ᵀ * X)) with hWL
  set L' := WL * A⁻¹ with hL'
  have hLA : L' * A = WL := by
    rw [hL', Matrix.mul_assoc, Matrix.nonsing_inv_mul A hAu, Matrix.mul_one]
  have hlStep : (1 / C.dt) • (L' - V * Sᵀ) =
      -(1 / C.eps) • ((P.B (X * S * Vᵀ))ᵀ * X) - (1 / C.eps ^ 2) • (P.M * (P.J ρ')ᵀ * X) -
        (1 / C.eps ^ 2) • (L' * (Xᵀ * Matrix.diagonal C.sigS * X)) -
        L' * (Xᵀ * Matrix.diagonal C.sigA * X) := by
    rw [smul_sub]
    refine step_rearrange ?_
    have e : (1 / C.dt) • L' + (1 / C.eps ^ 2) • (L' * (Xᵀ * Matrix.diagonal C.sigS * X)) +
        L' * (Xᵀ * Matrix.diagonal C.sigA * X) = L' * A := by
      rw [hA]
      simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
    exact e.trans hLA
  have hzL : P.ZeroDensity L' :=
    P.zeroDensity_lStep C (P.zeroDensity_mul hz Sᵀ) hlStep
  -- the new bases
  obtain ⟨X', hX', hcapX⟩ := exists_orthonormal_capture_of_le_card K' hs
  obtain ⟨V', hV', hzV', T, hT⟩ := P.exists_zeroDensity_capture hs' hzL
  -- the S-step
  set St := X'ᵀ * X * S * Vᵀ * V' with hSt
  set A' := (1 / C.dt) • (1 : Matrix (Fin s) (Fin s) ℝ) +
    (1 / C.eps ^ 2) • (X'ᵀ * Matrix.diagonal C.sigS * X') + X'ᵀ * Matrix.diagonal C.sigA * X'
    with hA'
  have hAu' : IsUnit A'.det := (Matrix.isUnit_iff_isUnit_det A').1 (isUnit_stiff C X')
  set WS := (1 / C.dt) • St + (-(1 / C.eps) • (X'ᵀ * P.B (X' * St * V'ᵀ) * V') -
    (1 / C.eps ^ 2) • (X'ᵀ * P.J ρ' * P.M * V')) with hWS
  set S' := A'⁻¹ * WS with hS'
  have hAS : A' * S' = WS := by
    rw [hS', ← Matrix.mul_assoc, Matrix.mul_nonsing_inv A' hAu', Matrix.one_mul]
  have hsStep : (1 / C.dt) • (S' - St) =
      -(1 / C.eps) • (X'ᵀ * P.B (X' * St * V'ᵀ) * V') -
        (1 / C.eps ^ 2) • (X'ᵀ * P.J ρ' * P.M * V') -
        (1 / C.eps ^ 2) • (X'ᵀ * Matrix.diagonal C.sigS * X' * S') -
        X'ᵀ * Matrix.diagonal C.sigA * X' * S' := by
    rw [smul_sub]
    refine step_rearrange ?_
    have e : (1 / C.dt) • S' + (1 / C.eps ^ 2) • (X'ᵀ * Matrix.diagonal C.sigS * X' * S') +
        X'ᵀ * Matrix.diagonal C.sigA * X' * S' = A' * S' := by
      rw [hA']
      simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul]
    exact e.trans hAS
  exact ⟨ρ', K', L', X', S', V', hρ', hkStep, hlStep, hX', hV',
    ⟨X'ᵀ * K', by rw [← Matrix.mul_assoc, hcapX]⟩, ⟨T, hT⟩, hzV', hsStep⟩

/-- Non-vacuity: the scheme (3.7) of arXiv 2602.12337 has a solution for all data. -/
theorem exists_imexStep (C : Coeff ι) (Φ ρ : ι → ℝ) (G : Matrix ι μ ℝ) :
    ∃ ρ' G', P.IsIMEXStep C Φ ρ G ρ' G' := by
  have hdt := C.dt_pos
  set W := (1 / C.dt) • G - (1 / C.eps) • (P.A G * P.Pi) - (1 / C.eps ^ 2) • P.J ρ with hW
  set G' := RR C * W with hG'
  have hsolve := solve_diag C W
  refine ⟨fun i => (1 / C.dt + C.sigAm i)⁻¹ * ((1 / C.dt) * ρ i - P.H G' i + Φ i), G', ?_, ?_⟩
  · ext i
    have hp : 0 < 1 / C.dt + C.sigAm i := by
      have : 0 < 1 / C.dt := by positivity
      linarith [C.sigAm_nonneg i]
    set t := (1 / C.dt + C.sigAm i)⁻¹ * ((1 / C.dt) * ρ i - P.H G' i + Φ i) with ht
    have e : (1 / C.dt + C.sigAm i) * t = (1 / C.dt) * ρ i - P.H G' i + Φ i := by
      rw [ht, mul_inv_cancel_left₀ hp.ne']
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.neg_apply]
    linarith
  · ext i k
    have h' := congrFun (congrFun hsolve i) k
    simp only [hW, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h' ⊢
    linarith

end LowRank

end Grid

/-! ### A concrete instance -/

/-- The one-dimensional periodic grid `ZMod N` with spacing `h`, with the two ordinates `±1` and
unit weights (`|D_Ω| = 2`). -/
noncomputable def slab (N : ℕ) [NeZero N] (h : ℝ) (hh : 0 < h) : Grid 1 (ZMod N) (Fin 2) where
  shift _ := Equiv.addRight 1
  dx _ := h
  dx_pos _ := hh
  Om _ := ![1, -1]
  w _ := 1
  w_pos _ := one_pos
  DOm := 2
  DOm_pos := two_pos
  sum_w := by norm_num [Fin.sum_univ_two]
  sum_w_Om _ := by simp [Fin.sum_univ_two]

/-- Unit coefficients `ε = Δt = σ₀ = σ^s = 1`, `σ^a = 0`. -/
noncomputable def unitCoeff (ι : Type*) : Coeff ι where
  eps := 1
  dt := 1
  sig0 := 1
  sigS _ := 1
  sigA _ := 0
  sigAm _ := 0
  eps_pos := one_pos
  dt_pos := one_pos
  sig0_pos := one_pos
  sig0_le _ := le_rfl
  sigA_nonneg _ := le_rfl
  sigAm_nonneg _ := le_rfl

/-- Non-vacuity: on `slab N 2` with unit coefficients, the CFL conditions (3.10) and (3.11)
(`θ = 1`, `C_A = ‖Ω‖ = 1`, `min Δx = 2`) hold, so `Grid.theorem_3_1`, `Grid.theorem_3_2` and
`Grid.theorem_4_1` apply; the steps themselves exist by `Grid.exists_imexStep`,
`Grid.exists_imexSStep` and `Grid.exists_imexSBUGStep`. -/
theorem slab_cfl (N : ℕ) [NeZero N] :
    (∀ j k, |(slab N 2 two_pos).Om j k| ≤ 1) ∧
    (∀ j, (2 : ℝ) ≤ (slab N 2 two_pos).dx j) ∧
    ((unitCoeff (ZMod N)).eps * 1 * (1 : ℕ) / (2 * 2) -
        (1 - 1) * (unitCoeff (ZMod N)).sig0 / (4 * 1)) * (unitCoeff (ZMod N)).dt ≤
      (unitCoeff (ZMod N)).eps ^ 2 / (2 * 1) ∧
    ∀ j, (unitCoeff (ZMod N)).dt ≤
      (unitCoeff (ZMod N)).eps * ((slab N 2 two_pos).dx j / (1 : ℕ)) /
          (1 * 1 + (slab N 2 two_pos).Cb j) +
        (unitCoeff (ZMod N)).sig0 * ((slab N 2 two_pos).dx j / (1 : ℕ)) ^ 2 /
          (2 * 1 * 1 ^ 2 + 2 * (slab N 2 two_pos).Cb j * 1) := by
  have hCb : ∀ j, (slab N 2 two_pos).Cb j = 1 := by
    intro j
    norm_num [Grid.Cb, slab, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j k
    fin_cases k <;> simp [slab]
  · intro j
    simp [slab]
  · norm_num [unitCoeff]
  · intro j
    rw [hCb]
    norm_num [unitCoeff, slab]

end LeanDLRA.Literature.P2602_12337
