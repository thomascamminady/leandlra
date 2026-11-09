import LeanDLRA.Matrix.Projectors
import LeanDLRA.Integrators.ParallelBUG
import LeanDLRA.Foundations.OneSided
import LeanDLRA.Matrix.Interpolation
import LeanDLRA.Literature.Randomized.P2408_16591a

/-!
# Results of arXiv 2601.18705: SN-like and PN-like DLRA for thermal radiative transfer

Haut, Loffeld, Einkemmer, Guthrey, Brunner, Schill, *Efficient SN-like and PN-like Dynamic Low
Rank methods for Thermal Radiative Transfer* (arXiv 2601.18705v1).  The paper is a methods paper
without numbered theorems; this module formalizes the mathematical claims of its derivations in
finite dimensions: space is discretized by `m` and angle by `n` degrees of freedom, so
`ψ = X S Wᵀ ∈ ℝ^{m×n}` with `X ∈ ℝ^{m×r}`, `W ∈ ℝ^{n×r}`, `K = X S`, `L = W Sᵀ` (the
`K_j`, `L_i` of (14) are the columns), inner products are Frobenius/Euclidean (quadrature weights
absorbed), and integrals over `𝕊²` are finite quadratures.  The PDE operators themselves
(streaming `Ω·∇`, the finite-element and DG matrices, the DSA asymptotics of Sec. 4.5 / App. 7.2)
are not built; where a result needs them, their algebraic properties are hypotheses, stated as
such.

## Results

* Sec. 2.2, eqs. (4)–(8): `newton_temperature_step` (Newton linearization of the backward
  Euler temperature step gives (5) with `σ_s` of (6)).  The printed (7) and (8) contain an extra
  `ρ c_v T₀` term: `printed_eq8_not_solution`, `printed_eq7_not_source` (counterexamples) and
  `printed_eq78_of_dropped_T0` (they linearize `ρ c_v T = Δt σ (φ - 4π B(T))` instead of (4)).
* Eqs. (16)–(20), App. 7.1: `hasDerivAt_kls` (eq. (17)), `kls_derivs_of_gauge` (eq. (16), which
  needs the gauge conditions `Xᵀ Ẋ = 0`, `Wᵀ Ẇ = 0` that the paper uses implicitly;
  `kls_derivs_need_gauge` shows orthonormality alone does not suffice),
  `galerkin_kls_eq_tangentProj` and `hasDerivAt_eq_tangentProj` (the Galerkin conditions
  (18)–(20) make the PN-like DLR equations the Dirac–Frenkel flow `ψ̇ = P(ψ) F(ψ)` with the core
  `tangentProj`).
* Eqs. (21)–(24): `pnStep` (the update (24)), `pnStep_eq_fromCols` and `rank_pnStep_le` (rank at
  most `2r`, with the paper's factor `Y`), `tangentProj_pnStep` (the update lies in the tangent
  space at `ψ₀`), `pnStep_eq` and `pnStep_eq_parallelBUG_add` (bridge to the core
  `parallelBUG`), `pnStep_explicit` (with explicit Euler substeps (24) is
  `ψ₀ + h P(ψ₀) F₀`), `pnSubsteps_galerkin` (the backward Euler substeps (21)–(23) are core
  Galerkin implicit Euler steps) and `pnSubsteps_norm_le` (each substep is non-expansive for a
  dissipative field; not in the paper).
* Sec. 3.1–3.2: `isOrthProj_evenPart`, `isOrthProj_oddPart` (eq. (30), core `IsOrthProj`),
  `parity_split` and `evenParity_equations` (eq. (28) as printed, and eq. (26) with the
  scattering source `σ_s φ₊ / (4π)` added to `Q₊`, which the printed (26) omits; abstract
  operators, boundary conditions not included), `inner_one_of_const_mode`,
  `scalarFlux_of_const_mode`, `scattering_galerkin_of_const_mode` (with `W₀,₀ = 1/√(4π)` the
  scattering term of (31) only couples to `K₀⁺`, with coefficient `1`, where the printed (31)
  shows `√(1/(4π))`), and the positive definiteness of the K-step systems:
  `posDef_transpose_mul_mul_of_orthonormal`, `reduced_system_unique` (Galerkin reduction of an
  SPD operator, abstract core), `posDef_evenParity_kStep` (the SPD property for the structure
  `Gᵀ D G + M_t` of a discretized even-parity operator).
* Sec. 3.3: `lStep_reduced`, `lStep_of_reduced` (the L-step (36) is equivalent to the
  `r × r` system `L̄ - C̄ M_s L̄ / (4π) = ζ̄` plus independent solves per angle).
* Sec. 4.1, App. 7.2.1: `selection_transpose_mul`, `collocation_coeffs` (`K = Ŵ⁻¹ Ψ`),
  `collocation_flux_eq_oblique` (the flux `βᵀ Ŵ⁻¹ Ψ` is the quadrature of the core
  interpolatory projector `obliqueProj` applied to `ψ`), `collocation_flux_exact` (exact on
  `span W`, as used in App. 7.2.1).
* Sec. 4.2: `deim_points_injective` (DEIM selects distinct angles) and `deim_isUnit_det` (the
  collocation matrix is invertible), using `IsDEIM` and `deim_res_facts` of the formalization of
  arXiv 2408.16591.
* Sec. 4.3, Algorithm 1: `snLStep_galerkin` (the row-constraint step (39)–(40) is a core Galerkin
  implicit Euler step on the new spatial basis) and `snLStep_norm_le` (the SN-like update is
  non-expansive for a dissipative field whatever angles are selected; not in the paper).

## Core definitions used, local definitions added

Core: `tangentProj`, `leftProj`, `rightProj`, `IsOrthProj`, `parallelBUG`, `obliqueProj`,
`galerkin_implicitEuler_norm_le_of_dissipative`, the Frobenius calculus
(`LeanDLRA.Frobenius.hasDerivAt_mul_mul`); from arXiv 2408.16591: `IsDEIM`, `deim_res_facts`,
`deimInv_of_le`.  Local: `pnStep`, the update (24), with the bridge `pnStep_eq_parallelBUG_add`
to the core `parallelBUG` (the two differ unless `P₀ yK + Q₀ yL = 2 yS`).

## Not formalized

The SN sweeps and source iteration of eq. (38) and the convergence of the fixed-point iteration;
the DSA derivation (Sec. 4.5, App. 7.2), which is an asymptotic `O(ε)` argument together with DG
integration-by-parts identities; the identity `∫_{𝕊²} Ω_i Ω_j = 4π δ_ij / 3`; the truncated SVD
after (24); the numerical experiments of Sec. 5 (ray effects).  No error bound for either scheme
is stated in the paper or proved here.
-/

open Set Filter Topology Finset Real
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2601_18705

/-! ### Section 2.2: Newton linearization of the temperature equation -/

section Newton

/-- **Newton-linearized backward Euler temperature step** (arXiv 2601.18705, Sec. 2.2,
eqs. (4)–(8); pointwise in `x`, so a statement about real numbers).  Write `ρcv = ρ c_v(T₀)`,
`σ = σ(T₀)`, `B₀ = B(T₀)`, `dB = ∂B/∂T (T₀)`, `h = Δt`, and replace `B(T)` in (4) by its
linearization `B₀ + dB (T - T₀)`.  If `D = ρcv + 4π h σ dB ≠ 0`, the new temperature is

  `T = T₀ + h σ (φ - 4π B₀) / D`,

and the linearized emission `σ B(T)` on the right of (1) becomes `σ_s φ / (4π) + q` with the
pseudo-scattering opacity `σ_s = (4π h σ dB / D) σ` of eq. (6) and the source
`q = σ B₀ - σ dB (4π h σ B₀) / D`.  This is the transport equation (5).

Deviation: the printed eqs. (7) and (8) carry an additional term `ρ c_v(T₀) T₀` in the numerator;
`printed_eq8_not_solution` and `printed_eq7_not_source` show that the printed formulas do not
follow from (4), and `printed_eq78_of_dropped_T0` shows that they are the linearization of
`ρ c_v T = Δt σ (φ - 4π B(T))`, i.e. of (4) with `T₀` dropped on the left.  The formulas above
are the ones that follow from (4); `σ_s` agrees with the printed (6). -/
theorem newton_temperature_step {ρcv σ B₀ dB h φ T₀ T : ℝ}
    (hD : ρcv + 4 * π * h * σ * dB ≠ 0)
    (hT : ρcv * (T - T₀) = h * σ * (φ - 4 * π * (B₀ + dB * (T - T₀)))) :
    T = T₀ + h * σ * (φ - 4 * π * B₀) / (ρcv + 4 * π * h * σ * dB) ∧
      σ * (B₀ + dB * (T - T₀)) =
        1 / (4 * π) * (4 * π * h * σ * dB / (ρcv + 4 * π * h * σ * dB) * σ) * φ
          + (σ * B₀ - σ * dB * (4 * π * h * σ * B₀) / (ρcv + 4 * π * h * σ * dB)) := by
  have hT' : T - T₀ = h * σ * (φ - 4 * π * B₀) / (ρcv + 4 * π * h * σ * dB) := by
    rw [eq_div_iff hD]
    linear_combination hT
  refine ⟨by rw [← hT']; ring, ?_⟩
  rw [hT']
  field_simp
  ring

/-- **The printed eq. (8) does not solve the linearized eq. (4)** (arXiv 2601.18705, Sec. 2.2).
The printed update `T = T₀ + (Δt σ (φ - 4π B₀) - ρ c_v T₀) / (ρ c_v + 4π Δt σ ∂B/∂T)` fails
already for `Δt = 0`, where (4) forces `T = T₀` but the printed formula gives `T = 0`. -/
theorem printed_eq8_not_solution :
    ¬ ∀ ρcv σ B₀ dB h φ T₀ T : ℝ, ρcv + 4 * π * h * σ * dB ≠ 0 →
      ρcv * (T - T₀) = h * σ * (φ - 4 * π * (B₀ + dB * (T - T₀))) →
      T = T₀ + (h * σ * (φ - 4 * π * B₀) - ρcv * T₀) / (ρcv + 4 * π * h * σ * dB) := by
  intro H
  have := H 1 0 0 0 0 0 1 1 (by norm_num) (by norm_num)
  norm_num at this

/-- **The printed eq. (7) is not the source term of (5)** (arXiv 2601.18705, Sec. 2.2).  With the
printed `q(T₀) = σ B₀ - σ ∂B/∂T (4π Δt σ B₀ + ρ c_v T₀) / (ρ c_v + 4π σ Δt ∂B/∂T)` and `σ_s`
from (6), the identity `σ B(T) = σ_s φ / (4π) + q` (linearized `B`, `T` solving the linearized
(4)) fails: for `Δt = 0`, `ρ c_v = σ = ∂B/∂T = T₀ = T = 1`, `B₀ = φ = 0` the left side is `0` and
the right side is `-1`. -/
theorem printed_eq7_not_source :
    ¬ ∀ ρcv σ B₀ dB h φ T₀ T : ℝ, ρcv + 4 * π * h * σ * dB ≠ 0 →
      ρcv * (T - T₀) = h * σ * (φ - 4 * π * (B₀ + dB * (T - T₀))) →
      σ * (B₀ + dB * (T - T₀)) =
        1 / (4 * π) * (4 * π * h * σ * dB / (ρcv + 4 * π * h * σ * dB) * σ) * φ
          + (σ * B₀ - σ * dB * (4 * π * h * σ * B₀ + ρcv * T₀)
            / (ρcv + 4 * π * σ * h * dB)) := by
  intro H
  have := H 1 1 0 1 0 0 1 1 (by norm_num) (by norm_num)
  norm_num at this

/-- **Where the printed eqs. (7)–(8) come from** (arXiv 2601.18705, Sec. 2.2; diagnosis of the
deviation noted in `newton_temperature_step`).  If `T` solves `ρ c_v T = Δt σ (φ - 4π B(T))`
with `B` linearized about `T₀` (eq. (4) with `T₀` dropped on the left), then `T` is given by the
printed (8) and `σ B(T) = σ_s φ / (4π) + q` with the printed (6) and (7). -/
theorem printed_eq78_of_dropped_T0 {ρcv σ B₀ dB h φ T₀ T : ℝ}
    (hD : ρcv + 4 * π * h * σ * dB ≠ 0)
    (hT : ρcv * T = h * σ * (φ - 4 * π * (B₀ + dB * (T - T₀)))) :
    T = T₀ + (h * σ * (φ - 4 * π * B₀) - ρcv * T₀) / (ρcv + 4 * π * h * σ * dB) ∧
      σ * (B₀ + dB * (T - T₀)) =
        1 / (4 * π) * (4 * π * h * σ * dB / (ρcv + 4 * π * h * σ * dB) * σ) * φ
          + (σ * B₀ - σ * dB * (4 * π * h * σ * B₀ + ρcv * T₀)
            / (ρcv + 4 * π * σ * h * dB)) := by
  have hT' : T - T₀ = (h * σ * (φ - 4 * π * B₀) - ρcv * T₀) / (ρcv + 4 * π * h * σ * dB) := by
    rw [eq_div_iff hD]
    linear_combination hT
  have hD' : ρcv + 4 * π * σ * h * dB ≠ 0 := by
    convert hD using 1; ring
  refine ⟨by rw [← hT']; ring, ?_⟩
  rw [hT']
  field_simp
  ring

end Newton

/-! ### Section 3.1–3.2: positive definiteness of the even-parity K-step systems -/

section PosDef

variable {l m k : Type*} [Fintype l] [Fintype m] [Fintype k] [DecidableEq k]

set_option linter.unusedFintypeInType false in
/-- **Even-parity reduced systems are SPD** (arXiv 2601.18705, Sec. 3.2, the remark after
(33)–(34); abstract core).  If `M` is symmetric positive definite and the columns of `U` are
orthonormal (`Uᵀ U = 1`), then the Galerkin-reduced matrix `Uᵀ M U` is symmetric positive
definite.  Here `M` is the (space-discretized) even-parity operator and `U` the matrix of the
angular basis, so `Uᵀ M U` is the matrix of the K-step system.  Only the injectivity of `U` is
used.  That the full even-parity operator is SPD is a hypothesis here; for the structure
`Gᵀ D G + M_t` of a discretized `-Ω·∇(σ_t⁻¹ Ω·∇·) + σ_t` it is derived in
`posDef_evenParity_kStep`. -/
theorem posDef_transpose_mul_mul_of_orthonormal {M : Matrix m m ℝ} (hM : M.PosDef)
    {U : Matrix m k ℝ} (hU : Uᵀ * U = 1) : (Uᵀ * M * U).PosDef := by
  have hinj : Function.Injective U.mulVec := by
    intro x y hxy
    have h := congrArg (Uᵀ.mulVec) hxy
    simpa [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec] using h
  have h := hM.conjTranspose_mul_mul_same hinj
  simpa using h

/-- **Reduced linear systems are uniquely solvable** (arXiv 2601.18705, Sec. 3.2; abstract core).
Under the hypotheses of `posDef_transpose_mul_mul_of_orthonormal`, for every right-hand side `b`
the system `(Uᵀ M U) x = b` has exactly one solution. -/
theorem reduced_system_unique {M : Matrix m m ℝ} (hM : M.PosDef)
    {U : Matrix m k ℝ} (hU : Uᵀ * U = 1) (b : k → ℝ) :
    ∃! x : k → ℝ, (Uᵀ * M * U) *ᵥ x = b := by
  have hA : (Uᵀ * M * U).PosDef := posDef_transpose_mul_mul_of_orthonormal hM hU
  have hdet : IsUnit (Uᵀ * M * U).det := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
  have hex : (Uᵀ * M * U) *ᵥ ((Uᵀ * M * U)⁻¹ *ᵥ b) = b := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  exact ⟨(Uᵀ * M * U)⁻¹ *ᵥ b, hex, fun y hy => hA.mulVec_injective (hy.trans hex.symm)⟩

/-- Instance of `reduced_system_unique`: with `M = I` and `U = (1, 0)ᵀ` the reduced system is
the scalar equation `1 · x = 3`, uniquely solvable. -/
example : ∃! x : Fin 1 → ℝ,
    ((!![(1 : ℝ); 0] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ * (1 : Matrix (Fin 2) (Fin 2) ℝ)
      * !![(1 : ℝ); 0]) *ᵥ x = ![3] := by
  apply reduced_system_unique Matrix.PosDef.one
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]

set_option linter.unusedFintypeInType false in
/-- **The even-parity K-step matrix is SPD** (arXiv 2601.18705, Sec. 3.2, remark after
(33)–(34); finite-dimensional form).  A conforming discretization of the even-parity operator
`-Ω·∇(σ_t⁻¹ Ω·∇ ψ) + σ_t ψ` (with the boundary term `|n·Ω|` of (27)/(29) put into `D`) has the
form `Gᵀ D G + M_t`, where `G` discretizes `Ω·∇` for all angles, `D` is positive semidefinite
(the weights `σ_t⁻¹` and the boundary term) and `M_t` is positive definite (the `σ_t` mass,
`σ_t > 0`).  Its Galerkin reduction `Uᵀ (Gᵀ D G + M_t) U` onto an orthonormal angular basis
`U`, the K-step matrix of (33), is SPD.  The concrete finite-element matrices are not built
here; only this structure is used. -/
theorem posDef_evenParity_kStep {G : Matrix l m ℝ} {D : Matrix l l ℝ} (hD : D.PosSemidef)
    {Mt : Matrix m m ℝ} (hMt : Mt.PosDef) {U : Matrix m k ℝ} (hU : Uᵀ * U = 1) :
    (Uᵀ * (Gᵀ * D * G + Mt) * U).PosDef := by
  have hG : (Gᵀ * D * G).PosSemidef := by
    simpa using hD.conjTranspose_mul_mul_same G
  exact posDef_transpose_mul_mul_of_orthonormal (Matrix.PosDef.posSemidef_add hG hMt) hU

end PosDef

/-! ### Section 3 and Appendix 7.1: the K-, L-, S-equations and the tangent projection -/

section KLS

open scoped LeanDLRA.Frobenius

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]

/-- **Eq. (17): the derivative of `ψ = X S Wᵀ` in K-, L-, S-form** (arXiv 2601.18705, eq. (17),
proved in Appendix 7.1; finite-dimensional form).  Discretize space by `m` and angle by `n`
degrees of freedom, so `ψ = X S Wᵀ ∈ ℝ^{m×n}` with `X ∈ ℝ^{m×r}`, `W ∈ ℝ^{n×r}`, `K = X S` (the
`K_j` of (14) are the columns) and `L = W Sᵀ` (the `L_i`).  For differentiable factors,
`∂ψ/∂t = K̇ Wᵀ + X L̇ᵀ - X Ṡ Wᵀ`, which is (17).  Neither orthonormality nor a gauge condition is
needed. -/
theorem hasDerivAt_kls {X : ℝ → Matrix m r ℝ} {S : ℝ → Matrix r r ℝ} {W : ℝ → Matrix n r ℝ}
    {X' : Matrix m r ℝ} {S' : Matrix r r ℝ} {W' : Matrix n r ℝ} {K' : Matrix m r ℝ}
    {L' : Matrix n r ℝ} {t : ℝ} (hX : HasDerivAt X X' t) (hS : HasDerivAt S S' t)
    (hW : HasDerivAt W W' t) (hK : HasDerivAt (fun τ => X τ * S τ) K' t)
    (hL : HasDerivAt (fun τ => W τ * (S τ)ᵀ) L' t) :
    HasDerivAt (fun τ => X τ * S τ * (W τ)ᵀ)
      (K' * (W t)ᵀ + X t * L'ᵀ - X t * S' * (W t)ᵀ) t := by
  have hK' : K' = X' * S t + X t * S' := hK.unique (Frobenius.hasDerivAt_mul hX hS)
  have hL' : L' = W' * (S t)ᵀ + W t * S'ᵀ :=
    hL.unique (Frobenius.hasDerivAt_mul hW (Frobenius.hasDerivAt_transpose hS))
  have h := Frobenius.hasDerivAt_mul_mul hX hS (Frobenius.hasDerivAt_transpose hW)
  convert h using 1
  rw [hK', hL']
  simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
  abel

/-- **Eq. (16) under the gauge conditions** (arXiv 2601.18705, eq. (16) and Appendix 7.1;
finite-dimensional form).  If at time `t` the factors are orthonormal (`Xᵀ X = 1`, `Wᵀ W = 1`,
eqs. (10)–(11)) and gauge-fixed (`Xᵀ Ẋ = 0`, `Wᵀ Ẇ = 0`), then
`K̇ = ψ̇ W`, `L̇ = ψ̇ᵀ X` and `Ṡ = Xᵀ ψ̇ W`, i.e. `K̇_j = ⟨∂ψ/∂t, W_j⟩`, `L̇_j = ⟨∂ψ/∂t, X_j⟩`,
`Ṡ_ij = ⟨∂ψ/∂t, X_i W_j⟩`.

Deviation: the paper derives (16) "using the orthogonality constraints (10)–(11)"; its appendix
uses the gauge conditions implicitly.  They are needed: orthonormality alone does not give (16),
see `kls_derivs_need_gauge`. -/
theorem kls_derivs_of_gauge [DecidableEq r] {X : ℝ → Matrix m r ℝ} {S : ℝ → Matrix r r ℝ}
    {W : ℝ → Matrix n r ℝ} {X' : Matrix m r ℝ} {S' : Matrix r r ℝ} {W' : Matrix n r ℝ}
    {K' : Matrix m r ℝ} {L' : Matrix n r ℝ} {Y' : Matrix m n ℝ} {t : ℝ}
    (hXo : (X t)ᵀ * X t = 1) (hWo : (W t)ᵀ * W t = 1) (hgX : (X t)ᵀ * X' = 0)
    (hgW : (W t)ᵀ * W' = 0) (hX : HasDerivAt X X' t) (hS : HasDerivAt S S' t)
    (hW : HasDerivAt W W' t) (hK : HasDerivAt (fun τ => X τ * S τ) K' t)
    (hL : HasDerivAt (fun τ => W τ * (S τ)ᵀ) L' t)
    (hY : HasDerivAt (fun τ => X τ * S τ * (W τ)ᵀ) Y' t) :
    K' = Y' * W t ∧ L' = Y'ᵀ * X t ∧ S' = (X t)ᵀ * Y' * W t := by
  have hK' : K' = X' * S t + X t * S' := hK.unique (Frobenius.hasDerivAt_mul hX hS)
  have hL' : L' = W' * (S t)ᵀ + W t * S'ᵀ :=
    hL.unique (Frobenius.hasDerivAt_mul hW (Frobenius.hasDerivAt_transpose hS))
  have hY' : Y' = X' * S t * (W t)ᵀ + X t * S' * (W t)ᵀ + X t * S t * W'ᵀ :=
    hY.unique (Frobenius.hasDerivAt_mul_mul hX hS (Frobenius.hasDerivAt_transpose hW))
  have hgW' : W'ᵀ * W t = 0 := by
    rw [← Matrix.transpose_transpose (W'ᵀ * W t), Matrix.transpose_mul,
      Matrix.transpose_transpose, hgW, Matrix.transpose_zero]
  have hgX' : X'ᵀ * X t = 0 := by
    rw [← Matrix.transpose_transpose (X'ᵀ * X t), Matrix.transpose_mul,
      Matrix.transpose_transpose, hgX, Matrix.transpose_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [hK', hY']
    simp only [Matrix.add_mul, Matrix.mul_assoc, hWo, hgW', Matrix.mul_one, Matrix.mul_zero,
      add_zero]
  · rw [hL', hY']
    simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.add_mul, Matrix.mul_assoc, hXo, hgX', Matrix.mul_one, Matrix.mul_zero, zero_add]
    abel
  · rw [hY']
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hWo, hgW', Matrix.mul_one,
      Matrix.mul_zero, add_zero]
    simp only [← Matrix.mul_assoc, hXo, hgX, Matrix.one_mul, Matrix.zero_mul, zero_add]

/-- **The gauge conditions cannot be dropped from (16)** (arXiv 2601.18705, eq. (16)).  The
rotation `X(τ) = [[cos τ, -sin τ], [sin τ, cos τ]]` is orthonormal for every `τ`; with the
constant factors `S = W = 1` the curve `ψ = X S Wᵀ = X` has `L = W Sᵀ = 1`, so `L̇ = 0`, while
`⟨∂ψ/∂t, X⟩ = ψ̇ᵀ X` is nonzero at `τ = 0`.  So (16) does not follow from the orthonormality
(10)–(11) alone; it needs the gauge `Xᵀ Ẋ = 0` (`kls_derivs_of_gauge`). -/
theorem kls_derivs_need_gauge :
    ∃ (X : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (Y' : Matrix (Fin 2) (Fin 2) ℝ),
      (∀ τ, (X τ)ᵀ * X τ = 1) ∧
      HasDerivAt (fun τ => X τ * (1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ)
        Y' 0 ∧
      Y'ᵀ * X 0 ≠ 0 := by
  set J : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0] with hJ
  refine ⟨fun τ => Real.cos τ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + Real.sin τ • J, J, ?_, ?_, ?_⟩
  · intro τ
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hJ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
      nlinarith [Real.cos_sq_add_sin_sq τ]
  · have e : (fun τ : ℝ => (Real.cos τ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + Real.sin τ • J) *
        (1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ) =
        fun τ => Real.cos τ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + Real.sin τ • J := by
      funext τ
      rw [Matrix.transpose_one, Matrix.mul_one, Matrix.mul_one]
    rw [e]
    exact (((Real.hasDerivAt_cos 0).smul_const _).add
      ((Real.hasDerivAt_sin 0).smul_const J)).congr_deriv (by simp)
  · intro h
    have := congrFun (congrFun h 0) 1
    simp [hJ, Matrix.mul_apply, Fin.sum_univ_two] at this

/-- **Galerkin conditions (18)–(20) give the tangent projection** (arXiv 2601.18705, eqs.
(17)–(20); finite-dimensional form).  With `F = ℒψ + q` evaluated at the current low-rank state,
the Galerkin conditions read `K̇ = F W`, `L̇ = Fᵀ X`, `Ṡ = Xᵀ F W`.  Inserted into (17) they give
`K̇ Wᵀ + X L̇ᵀ - X Ṡ Wᵀ = X Xᵀ F + F W Wᵀ - X Xᵀ F W Wᵀ = P(Y) F`, the orthogonal projection of
`F` onto the tangent space of the rank-`r` manifold at `Y = X S Wᵀ` (`tangentProj`). -/
theorem galerkin_kls_eq_tangentProj (X : Matrix m r ℝ) (W : Matrix n r ℝ) (F : Matrix m n ℝ) :
    F * W * Wᵀ + X * (Fᵀ * X)ᵀ - X * (Xᵀ * F * W) * Wᵀ = tangentProj X W F := by
  rw [tangentProj_apply]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  abel

/-- **The PN-like DLR equations are the Dirac–Frenkel projected flow** (arXiv 2601.18705,
Sec. 3, eqs. (15)–(20); finite-dimensional form).  If the factors of `ψ = X S Wᵀ` are
differentiable at `t` and their K-, L-, S-derivatives satisfy the Galerkin conditions (18)–(20)
for the field `F` (`F t ψ = ℒψ + q`), then `ψ̇ = P(ψ) F(t, ψ)` with `P(ψ) = tangentProj X W`,
the DLRA equation of Koch–Lubich (compare `LeanDLRA.hasDerivAt_factorProduct_of_factorODE`). -/
theorem hasDerivAt_eq_tangentProj {X : ℝ → Matrix m r ℝ} {S : ℝ → Matrix r r ℝ}
    {W : ℝ → Matrix n r ℝ} {X' : Matrix m r ℝ} {S' : Matrix r r ℝ} {W' : Matrix n r ℝ}
    {K' : Matrix m r ℝ} {L' : Matrix n r ℝ} {t : ℝ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    (hX : HasDerivAt X X' t) (hS : HasDerivAt S S' t) (hW : HasDerivAt W W' t)
    (hK : HasDerivAt (fun τ => X τ * S τ) K' t) (hL : HasDerivAt (fun τ => W τ * (S τ)ᵀ) L' t)
    (hK' : K' = F t (X t * S t * (W t)ᵀ) * W t)
    (hL' : L' = (F t (X t * S t * (W t)ᵀ))ᵀ * X t)
    (hS' : S' = (X t)ᵀ * F t (X t * S t * (W t)ᵀ) * W t) :
    HasDerivAt (fun τ => X τ * S τ * (W τ)ᵀ)
      (tangentProj (X t) (W t) (F t (X t * S t * (W t)ᵀ))) t := by
  have h := hasDerivAt_kls hX hS hW hK hL
  rwa [hK', hL', hS', galerkin_kls_eq_tangentProj] at h

end KLS

/-! ### Section 3: the time-discrete PN-like step (21)–(24) -/

section Step

open scoped LeanDLRA.Frobenius

variable {m n r : Type*} [Fintype r]

/-- **The PN-like update (24)** (arXiv 2601.18705, eq. (24); finite-dimensional form): with
lagged bases `X₀`, `W₀`, starting value `ψ₀ = X₀ S₀ W₀ᵀ`, `K₀ = X₀ S₀`, `L₀ = W₀ S₀ᵀ`, and the
solutions `K`, `L`, `S` of the substeps (21)–(23),
`ψ₁ = ψ₀ + (K - K₀) W₀ᵀ + X₀ (L - L₀)ᵀ - X₀ (S - S₀) W₀ᵀ`.

Relation to the core: the parallel BUG update `LeanDLRA.parallelBUG` of Ceruti–Kusch–Lubich
combines the same three substep values differently (`pnStep_eq_parallelBUG_add`); the two agree
when the substeps are explicit Euler steps (`pnStep_explicit`), not in general, which is why a
separate definition is used. -/
def pnStep (X₀ : Matrix m r ℝ) (S₀ : Matrix r r ℝ) (W₀ : Matrix n r ℝ) (K : Matrix m r ℝ)
    (L : Matrix n r ℝ) (S : Matrix r r ℝ) : Matrix m n ℝ :=
  X₀ * S₀ * W₀ᵀ + (K - X₀ * S₀) * W₀ᵀ + X₀ * (L - W₀ * S₀ᵀ)ᵀ - X₀ * (S - S₀) * W₀ᵀ

/-- **(24) has rank at most `2r`** (arXiv 2601.18705, after eq. (24)): `ψ₁ = Y Zᵀ` with the
`2r` columns `Y = [K - K₀ - X₀ (S - S₀), X₀]` (the paper's `Y_j`) and `Z = [W₀, L]` (the paper
leaves `Z` unspecified). -/
theorem pnStep_eq_fromCols (X₀ : Matrix m r ℝ) (S₀ : Matrix r r ℝ) (W₀ : Matrix n r ℝ)
    (K : Matrix m r ℝ) (L : Matrix n r ℝ) (S : Matrix r r ℝ) :
    pnStep X₀ S₀ W₀ K L S =
      Matrix.fromCols (K - X₀ * S₀ - X₀ * (S - S₀)) X₀ * (Matrix.fromCols W₀ L)ᵀ := by
  rw [Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows, pnStep]
  simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

/-- **(24) increases the rank from `r` to at most `2r`** (arXiv 2601.18705, after eq. (24)). -/
theorem rank_pnStep_le [Fintype n] (X₀ : Matrix m r ℝ) (S₀ : Matrix r r ℝ) (W₀ : Matrix n r ℝ)
    (K : Matrix m r ℝ) (L : Matrix n r ℝ) (S : Matrix r r ℝ) :
    (pnStep X₀ S₀ W₀ K L S).rank ≤ 2 * Fintype.card r := by
  rw [pnStep_eq_fromCols]
  refine (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans ?_)
  rw [Fintype.card_sum]
  omega

/-- **The update (24) lies in the tangent space at `ψ₀`** (arXiv 2601.18705, eq. (24)): for
orthonormal `X₀`, `W₀` the tangent-space projector `P(ψ₀) = tangentProj X₀ W₀` fixes `ψ₁`. -/
theorem tangentProj_pnStep [Fintype m] [Fintype n] [DecidableEq r]
    {X₀ : Matrix m r ℝ} {W₀ : Matrix n r ℝ} (hX : X₀ᵀ * X₀ = 1)
    (hW : W₀ᵀ * W₀ = 1) (S₀ : Matrix r r ℝ) (K : Matrix m r ℝ) (L : Matrix n r ℝ)
    (S : Matrix r r ℝ) :
    tangentProj X₀ W₀ (pnStep X₀ S₀ W₀ K L S) = pnStep X₀ S₀ W₀ K L S := by
  refine (tangentProj_eq_self_iff hX hW _).mpr ⟨Lᵀ, K - X₀ * S₀ - X₀ * (S - S₀), ?_⟩
  rw [pnStep]
  simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

/-- **(24) in terms of the full-space substep values** (arXiv 2601.18705, eq. (24)): with
`yK = K W₀ᵀ`, `yL = X₀ Lᵀ`, `yS = X₀ S W₀ᵀ`, `ψ₁ = yK + yL - yS`. -/
theorem pnStep_eq (X₀ : Matrix m r ℝ) (S₀ : Matrix r r ℝ) (W₀ : Matrix n r ℝ)
    (K : Matrix m r ℝ) (L : Matrix n r ℝ) (S : Matrix r r ℝ) :
    pnStep X₀ S₀ W₀ K L S = K * W₀ᵀ + X₀ * Lᵀ - X₀ * S * W₀ᵀ := by
  rw [pnStep]
  simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

/-- **Bridge to the core parallel BUG update** (arXiv 2601.18705, eq. (24), compared with
arXiv 2304.05660, §3.1).  With `P₀ = leftProj X₀`, `Q₀ = rightProj W₀` and the substep values
`yK = K W₀ᵀ`, `yL = X₀ Lᵀ`, `yS = X₀ S W₀ᵀ`,
`ψ₁ = parallelBUG P₀ Q₀ yK yL yS + (P₀ yK - yS) + (Q₀ yL - yS)`, so (24) is the parallel BUG
update exactly when `P₀ yK + Q₀ yL = 2 yS`. -/
theorem pnStep_eq_parallelBUG_add [Fintype m] [Fintype n]
    (X₀ : Matrix m r ℝ) (S₀ : Matrix r r ℝ) (W₀ : Matrix n r ℝ)
    (K : Matrix m r ℝ) (L : Matrix n r ℝ) (S : Matrix r r ℝ) :
    pnStep X₀ S₀ W₀ K L S =
      parallelBUG (leftProj X₀) (rightProj W₀) (K * W₀ᵀ) (X₀ * Lᵀ) (X₀ * S * W₀ᵀ)
        + (leftProj X₀ (K * W₀ᵀ) - X₀ * S * W₀ᵀ) + (rightProj W₀ (X₀ * Lᵀ) - X₀ * S * W₀ᵀ) := by
  rw [pnStep_eq, parallelBUG]
  simp only [sub_apply, one_apply_eq_self]
  abel

/-- **With explicit Euler substeps, (24) is the tangent-projected Euler step** (arXiv
2601.18705, eqs. (17) and (24), with (21)–(23) discretized by explicit instead of backward
Euler; this is the consistency of (24) with `ψ = ψ₀ + Δt ∂ψ/∂t`).  If `K = K₀ + h F₀ W₀`,
`L = L₀ + h F₀ᵀ X₀`, `S = S₀ + h X₀ᵀ F₀ W₀`, then `ψ₁ = ψ₀ + h P(ψ₀) F₀`.  In this case (24)
coincides with the parallel BUG update (`LeanDLRA.parallelBUG_euler`). -/
theorem pnStep_explicit [Fintype m] [Fintype n]
    (X₀ : Matrix m r ℝ) (S₀ : Matrix r r ℝ) (W₀ : Matrix n r ℝ)
    (F₀ : Matrix m n ℝ) (h : ℝ) :
    pnStep X₀ S₀ W₀ (X₀ * S₀ + h • (F₀ * W₀)) (W₀ * S₀ᵀ + h • (F₀ᵀ * X₀))
        (S₀ + h • (X₀ᵀ * F₀ * W₀)) =
      X₀ * S₀ * W₀ᵀ + h • tangentProj X₀ W₀ F₀ := by
  rw [pnStep, ← galerkin_kls_eq_tangentProj]
  simp only [add_sub_cancel_left, Matrix.smul_mul, Matrix.mul_smul, Matrix.transpose_smul,
    smul_sub, smul_add]
  abel

/-- **The backward Euler substeps (21)–(23) are Galerkin implicit Euler steps** (arXiv
2601.18705, eqs. (21)–(23); finite-dimensional form, `h = Δt`, `F t ψ = ℒψ + q`).  For
orthonormal lagged bases, with `ψ₀ = X₀ S₀ W₀ᵀ`, the K-, L- and S-substeps read
`yK = Q₀ (ψ₀ + h F(yK))`, `yL = P₀ (ψ₀ + h F(yL))`, `yS = P₀ Q₀ (ψ₀ + h F(yS))` for the
full-space values `yK = K W₀ᵀ`, `yL = X₀ Lᵀ`, `yS = X₀ S W₀ᵀ`, with `P₀ = leftProj X₀`,
`Q₀ = rightProj W₀`: the form used by the core (`LeanDLRA.galerkin_implicitEuler_stability`). -/
theorem pnSubsteps_galerkin [Fintype m] [Fintype n] [DecidableEq r]
    {X₀ : Matrix m r ℝ} {W₀ : Matrix n r ℝ} (hX : X₀ᵀ * X₀ = 1)
    (hW : W₀ᵀ * W₀ = 1) {S₀ S : Matrix r r ℝ} {K : Matrix m r ℝ} {L : Matrix n r ℝ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t h : ℝ}
    (hK : K - X₀ * S₀ = h • (F t (K * W₀ᵀ) * W₀))
    (hL : L - W₀ * S₀ᵀ = h • ((F t (X₀ * Lᵀ))ᵀ * X₀))
    (hS : S - S₀ = h • (X₀ᵀ * F t (X₀ * S * W₀ᵀ) * W₀)) :
    K * W₀ᵀ = rightProj W₀ (X₀ * S₀ * W₀ᵀ + h • F t (K * W₀ᵀ)) ∧
      X₀ * Lᵀ = leftProj X₀ (X₀ * S₀ * W₀ᵀ + h • F t (X₀ * Lᵀ)) ∧
      X₀ * S * W₀ᵀ =
        leftProj X₀ (rightProj W₀ (X₀ * S₀ * W₀ᵀ + h • F t (X₀ * S * W₀ᵀ))) := by
  rw [sub_eq_iff_eq_add'] at hK hL hS
  refine ⟨?_, ?_, ?_⟩
  · conv_lhs => rw [hK]
    simp only [rightProj_apply, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc, hW,
      Matrix.mul_one]
  · conv_lhs => rw [hL]
    simp only [leftProj_apply, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc]
    simp only [← Matrix.mul_assoc, hX, Matrix.one_mul]
  · conv_lhs => rw [hS]
    simp only [leftProj_rightProj_apply, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul]
    simp only [← Matrix.mul_assoc, hX, Matrix.one_mul]
    simp only [Matrix.mul_assoc, hW, Matrix.mul_one]

/-- **Each PN-like substep is non-expansive for dissipative transport** (consequence of
`pnSubsteps_galerkin` and the core `LeanDLRA.galerkin_implicitEuler_norm_le_of_dissipative`; not
stated in arXiv 2601.18705).  If `⟪F t ψ, ψ⟫ ≤ 0` for all `ψ` (e.g. the transport operator with
vacuum inflow, absorption and scattering with `σ_s ≤ σ_t`, and `q = 0`) and `h ≥ 0`, then
`‖K W₀ᵀ‖`, `‖X₀ Lᵀ‖`, `‖X₀ S W₀ᵀ‖` are all at most `‖ψ₀‖`.  This does not bound `ψ₁` of
(24) by `‖ψ₀‖`, since (24) combines the three values as `yK + yL - yS`. -/
theorem pnSubsteps_norm_le [Fintype m] [Fintype n] [DecidableEq r]
    {X₀ : Matrix m r ℝ} {W₀ : Matrix n r ℝ} (hX : X₀ᵀ * X₀ = 1)
    (hW : W₀ᵀ * W₀ = 1) {S₀ S : Matrix r r ℝ} {K : Matrix m r ℝ} {L : Matrix n r ℝ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t h : ℝ} (hh : 0 ≤ h) (hF : ∀ ψ, ⟪F t ψ, ψ⟫ ≤ 0)
    (hK : K - X₀ * S₀ = h • (F t (K * W₀ᵀ) * W₀))
    (hL : L - W₀ * S₀ᵀ = h • ((F t (X₀ * Lᵀ))ᵀ * X₀))
    (hS : S - S₀ = h • (X₀ᵀ * F t (X₀ * S * W₀ᵀ) * W₀)) :
    ‖K * W₀ᵀ‖ ≤ ‖X₀ * S₀ * W₀ᵀ‖ ∧ ‖X₀ * Lᵀ‖ ≤ ‖X₀ * S₀ * W₀ᵀ‖ ∧
      ‖X₀ * S * W₀ᵀ‖ ≤ ‖X₀ * S₀ * W₀ᵀ‖ := by
  obtain ⟨h1, h2, h3⟩ := pnSubsteps_galerkin hX hW hK hL hS
  refine ⟨galerkin_implicitEuler_norm_le_of_dissipative (isOrthProj_rightProj hW) hh hF h1,
    galerkin_implicitEuler_norm_le_of_dissipative (isOrthProj_leftProj hX) hh hF h2, ?_⟩
  exact galerkin_implicitEuler_norm_le_of_dissipative
    (isOrthProj_leftProj_mul_rightProj hX hW) hh hF h3

/-! ### Section 4.3 and Algorithm 1: the row-constraint (L) step of the SN-like method -/

/-- **The SN-like L-step is a Galerkin implicit Euler step** (arXiv 2601.18705, eqs.
(39)–(40) and Algorithm 1, steps 6–7; finite-dimensional form).  After the collocation K-step
has produced the new spatial basis `X₁`, step 6 projects the initial condition,
`L̃⁽⁰⁾ = ψ₀ᵀ X₁` (`L̃_j = ⟨ψ⁽⁰⁾, X_j⟩`), and step 7 solves the Galerkin system (40), i.e.
`L - L̃⁽⁰⁾ = h F(X₁ Lᵀ)ᵀ X₁` with `h = c Δt` and `F ψ = -Ω·∇ψ - σψ + σ_s φ / (4π) + q`.  The
new solution `ψ₁ = X₁ Lᵀ` then satisfies `ψ₁ = P₁ (ψ₀ + h F(ψ₁))` with `P₁ = leftProj X₁`.  No
orthonormality is needed for this identity. -/
theorem snLStep_galerkin [Fintype m] [Fintype n]
    {X₁ : Matrix m r ℝ} {ψ₀ : Matrix m n ℝ} {L : Matrix n r ℝ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t h : ℝ}
    (hL : L - ψ₀ᵀ * X₁ = h • ((F t (X₁ * Lᵀ))ᵀ * X₁)) :
    X₁ * Lᵀ = leftProj X₁ (ψ₀ + h • F t (X₁ * Lᵀ)) := by
  rw [sub_eq_iff_eq_add'] at hL
  conv_lhs => rw [hL]
  simp only [leftProj_apply, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc]

/-- **The SN-like update is non-expansive for dissipative transport, whatever angles the
collocation step selects** (consequence of `snLStep_galerkin` and the core
`LeanDLRA.galerkin_implicitEuler_norm_le_of_dissipative`; not stated in arXiv 2601.18705).  If
the new spatial basis is orthonormal (`X₁ᵀ X₁ = 1`, Algorithm 1 step 5), `h ≥ 0` and
`⟪F t ψ, ψ⟫ ≤ 0` for all `ψ`, then the result `ψ₁ = X₁ Lᵀ` of steps 6–7 satisfies
`‖ψ₁‖ ≤ ‖ψ₀‖`.  The bound does not depend on the selected angles or on the collocation step
that produced `X₁`; step 8 (`L = W Sᵀ`) does not change `ψ₁`. -/
theorem snLStep_norm_le [Fintype m] [Fintype n] [DecidableEq r]
    {X₁ : Matrix m r ℝ} (hX₁ : X₁ᵀ * X₁ = 1) {ψ₀ : Matrix m n ℝ}
    {L : Matrix n r ℝ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t h : ℝ} (hh : 0 ≤ h)
    (hF : ∀ ψ, ⟪F t ψ, ψ⟫ ≤ 0) (hL : L - ψ₀ᵀ * X₁ = h • ((F t (X₁ * Lᵀ))ᵀ * X₁)) :
    ‖X₁ * Lᵀ‖ ≤ ‖ψ₀‖ :=
  galerkin_implicitEuler_norm_le_of_dissipative (isOrthProj_leftProj hX₁) hh hF
    (snLStep_galerkin hL)

/-- Non-vacuity of `snLStep_norm_le`: for the dissipative field `F ψ = -ψ`, the L-step (40) has
the solution `L = (1 + h)⁻¹ ψ₀ᵀ X₁`, and the bound applies. -/
example [Fintype m] [Fintype n] [DecidableEq r] {X₁ : Matrix m r ℝ} (hX₁ : X₁ᵀ * X₁ = 1)
    (ψ₀ : Matrix m n ℝ) {h : ℝ} (hh : 0 ≤ h) :
    ‖X₁ * ((1 + h)⁻¹ • (ψ₀ᵀ * X₁))ᵀ‖ ≤ ‖ψ₀‖ := by
  refine snLStep_norm_le hX₁ (F := fun _ ψ => -ψ) (t := 0) hh (fun ψ => ?_) ?_
  · show ⟪-ψ, ψ⟫ ≤ 0
    rw [inner_neg_left, neg_nonpos]
    exact real_inner_self_nonneg
  · show (1 + h)⁻¹ • (ψ₀ᵀ * X₁) - ψ₀ᵀ * X₁ =
      h • ((-(X₁ * ((1 + h)⁻¹ • (ψ₀ᵀ * X₁))ᵀ))ᵀ * X₁)
    have e : (-(X₁ * ((1 + h)⁻¹ • (ψ₀ᵀ * X₁))ᵀ))ᵀ * X₁ = -((1 + h)⁻¹ • (ψ₀ᵀ * X₁)) := by
      rw [Matrix.transpose_neg, Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.neg_mul]
      simp only [Matrix.mul_assoc, hX₁, Matrix.mul_one]
    have h1 : (1 + h) ≠ 0 := by linarith
    have hc : (1 + h)⁻¹ - 1 = -(h * (1 + h)⁻¹) := by
      field_simp
      ring
    rw [e, smul_neg, smul_smul, ← neg_smul, ← hc, sub_smul, one_smul]

end Step

/-! ### Section 3.1: even and odd parts in angle -/

section Parity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The even part `ψ₊ = (ψ + Jψ)/2` is an orthogonal projection** (arXiv 2601.18705,
Sec. 3.1 and eq. (30); abstract form).  `J` is the parity map `ψ(Ω) ↦ ψ(-Ω)`: an involution that
is self-adjoint (on `L²(𝕊²)`, or on an antipodally symmetric quadrature, it is an isometric
involution). -/
theorem isOrthProj_evenPart {J : E →L[ℝ] E} (hJ : ∀ x, J (J x) = x)
    (hJs : ∀ x y, ⟪J x, y⟫ = ⟪x, J y⟫) : IsOrthProj ((2 : ℝ)⁻¹ • (1 + J)) where
  idem x := by
    simp only [smul_apply, add_apply,
      one_apply_eq_self, map_smul, map_add, hJ]
    module
  symm x y := by
    simp only [smul_apply, add_apply,
      one_apply_eq_self, real_inner_smul_left, real_inner_smul_right,
      inner_add_left, inner_add_right, hJs]

/-- **The odd part `ψ₋ = (ψ - Jψ)/2` is an orthogonal projection** (arXiv 2601.18705, Sec. 3.1
and eq. (30); abstract form), complementary to `isOrthProj_evenPart`. -/
theorem isOrthProj_oddPart {J : E →L[ℝ] E} (hJ : ∀ x, J (J x) = x)
    (hJs : ∀ x y, ⟪J x, y⟫ = ⟪x, J y⟫) : IsOrthProj ((2 : ℝ)⁻¹ • (1 - J)) where
  idem x := by
    simp only [smul_apply, sub_apply,
      one_apply_eq_self, map_smul, map_sub, hJ]
    module
  symm x y := by
    simp only [smul_apply, sub_apply,
      one_apply_eq_self, real_inner_smul_left, real_inner_smul_right,
      inner_sub_left, inner_sub_right, hJs]

end Parity

section EvenParity

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Even and odd parts of the transport equation (25)** (arXiv 2601.18705, Sec. 3.1; abstract
form).  Let `J` be the parity involution, `T` the streaming operator `Ω·∇` (odd:
`J T = -T J`), `Sg` the multiplication by `σ_t` and `Sc` the isotropic scattering
`ψ ↦ σ_s φ / (4π)` (both even), with `Sc` vanishing on odd functions.  If
`T ψ + Sg ψ - Sc ψ = Q` (eq. (25)), then with `ψ± = (ψ ± Jψ)/2`, `Q± = (Q ± JQ)/2`:
`T ψ₋ + Sg ψ₊ - Sc ψ₊ = Q₊` and `T ψ₊ + Sg ψ₋ = Q₋`.  The boundary conditions are not part of
this abstract statement. -/
theorem parity_split {J T Sg Sc : V →ₗ[ℝ] V} (hJ : ∀ x, J (J x) = x)
    (hT : ∀ x, J (T x) = -T (J x)) (hSg : ∀ x, J (Sg x) = Sg (J x))
    (hSc : ∀ x, J (Sc x) = Sc (J x)) (hSc0 : ∀ x, J x = -x → Sc x = 0) {ψ Q : V}
    (hψ : T ψ + Sg ψ - Sc ψ = Q) :
    T ((2 : ℝ)⁻¹ • (ψ - J ψ)) + Sg ((2 : ℝ)⁻¹ • (ψ + J ψ)) - Sc ((2 : ℝ)⁻¹ • (ψ + J ψ)) =
        (2 : ℝ)⁻¹ • (Q + J Q) ∧
      T ((2 : ℝ)⁻¹ • (ψ + J ψ)) + Sg ((2 : ℝ)⁻¹ • (ψ - J ψ)) = (2 : ℝ)⁻¹ • (Q - J Q) := by
  have hJQ : J Q = -T (J ψ) + Sg (J ψ) - Sc (J ψ) := by
    rw [← hψ, map_sub, map_add, hT, hSg, hSc]
  have hodd : Sc ψ - Sc (J ψ) = 0 := by
    rw [← map_sub]
    exact hSc0 _ (by rw [map_sub, hJ, neg_sub])
  simp only [map_smul, map_add, map_sub]
  constructor
  · rw [hJQ, ← hψ]
    module
  · rw [hJQ, ← hψ]
    linear_combination (norm := module) (2 : ℝ)⁻¹ • hodd

/-- **The even-parity equations (28) and (26)** (arXiv 2601.18705, Sec. 3.1, eqs. (26), (28);
abstract form, notation of `parity_split`, `Sgi` a left inverse of `Sg` (multiplication by
`1/σ_t`)).  From (25):

* (28): `-T Sgi T ψ₊ + Sg ψ₊ - Sc ψ₊ = Q₊ - T Sgi Q₋`, exactly as printed;
* (26), corrected: `-T Sgi T ψ₋ + Sg ψ₋ = Q₋ - T Sgi (Q₊ + Sc ψ₊)`.

Deviation: the printed (26) has `Q₊` in place of `Q₊ + Sc ψ₊ = Q₊ + σ_s φ / (4π)`; the two agree
when there is no scattering (`σ_s = 0`) or when the scattering source is counted as part of
`Q₊`. -/
theorem evenParity_equations {J T Sg Sgi Sc : V →ₗ[ℝ] V} (hJ : ∀ x, J (J x) = x)
    (hT : ∀ x, J (T x) = -T (J x)) (hSg : ∀ x, J (Sg x) = Sg (J x))
    (hSgi : ∀ x, Sgi (Sg x) = x) (hSc : ∀ x, J (Sc x) = Sc (J x))
    (hSc0 : ∀ x, J x = -x → Sc x = 0) {ψ Q ψp ψm Qp Qm : V} (hψ : T ψ + Sg ψ - Sc ψ = Q)
    (hψp : ψp = (2 : ℝ)⁻¹ • (ψ + J ψ)) (hψm : ψm = (2 : ℝ)⁻¹ • (ψ - J ψ))
    (hQp : Qp = (2 : ℝ)⁻¹ • (Q + J Q)) (hQm : Qm = (2 : ℝ)⁻¹ • (Q - J Q)) :
    -T (Sgi (T ψp)) + Sg ψp - Sc ψp = Qp - T (Sgi Qm) ∧
      -T (Sgi (T ψm)) + Sg ψm = Qm - T (Sgi (Qp + Sc ψp)) := by
  obtain ⟨he, ho⟩ := parity_split hJ hT hSg hSc hSc0 hψ
  rw [← hψp, ← hψm, ← hQp] at he
  rw [← hψp, ← hψm, ← hQm] at ho
  have hm : ψm = Sgi (Qm - T ψp) := by
    rw [← ho, add_sub_cancel_left, hSgi]
  have hp : ψp = Sgi (Qp + Sc ψp - T ψm) := by
    rw [← he]
    have : T ψm + Sg ψp - Sc ψp + Sc ψp - T ψm = Sg ψp := by abel
    rw [this, hSgi]
  constructor
  · have h := he
    rw [hm, map_sub, map_sub] at h
    rw [← h]
    abel
  · have h := ho
    rw [hp, map_sub, map_sub] at h
    rw [← h, map_add]
    abel

end EvenParity

/-! ### Section 3.2: the constant angular mode and the scattering term -/

section ConstantMode

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {ι : Type*}

/-- **Moments of an orthonormal angular basis containing the constant** (arXiv 2601.18705,
Sec. 3.2, "we always enforce `W₀,₀ = 1/√(4π)`"; abstract form).  Let `one` be the constant
function (`‖one‖² = ∫_{𝕊²} 1 = 4π`) and `W` an orthonormal family with `W i₀ = one / ‖one‖`.
Then `∫ W_j = ⟪one, W j⟫` is `‖one‖ = √(4π)` for `j = i₀` and `0` otherwise. -/
theorem inner_one_of_const_mode [DecidableEq ι] {W : ι → H} (hW : Orthonormal ℝ W) {one : H}
    {i₀ : ι} (h0 : W i₀ = ‖one‖⁻¹ • one) (j : ι) : ⟪one, W j⟫ = if j = i₀ then ‖one‖ else 0 := by
  have hne : ‖one‖ ≠ 0 := by
    intro h
    have h1 := hW.1 i₀
    rw [h0, h, inv_zero, zero_smul, norm_zero] at h1
    exact zero_ne_one h1
  have hone : one = ‖one‖ • W i₀ := by
    rw [h0, smul_smul, mul_inv_cancel₀ hne, one_smul]
  rw [hone, real_inner_smul_left, orthonormal_iff_ite.mp hW i₀ j, norm_smul, hW.1 i₀,
    mul_one, Real.norm_of_nonneg (norm_nonneg _)]
  by_cases hj : j = i₀
  · simp [hj]
  · simp [hj, Ne.symm hj]

/-- **The scalar flux only sees the constant mode** (arXiv 2601.18705, Sec. 3.2): for
`ψ = Σ_j K_j W_j` (at a fixed `x`), `φ = ⟪one, ψ⟫ = ‖one‖ K_{i₀} = √(4π) K₀`. -/
theorem scalarFlux_of_const_mode [Fintype ι] {W : ι → H} (hW : Orthonormal ℝ W) {one : H} {i₀ : ι}
    (h0 : W i₀ = ‖one‖⁻¹ • one) (K : ι → ℝ) : ⟪one, ∑ j, K j • W j⟫ = ‖one‖ * K i₀ := by
  classical
  simp only [inner_sum, real_inner_smul_right, inner_one_of_const_mode hW h0, mul_ite,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- **The projected scattering term of the K-step** (arXiv 2601.18705, eq. (31), the term
`δ_{j',0} σ_s K₀⁺`; abstract form).  Let `J` be the parity involution (self-adjoint) with
`J one = one`, `W` orthonormal with `W i₀ = one / ‖one‖`, `W⁺ j = (W j + J W j)/2` (eq. (30)) and
`ψ₊ = Σ_j K_j W⁺_j`.  Projecting the scattering source `σ_s φ₊ / ‖one‖²` (with
`‖one‖² = 4π`, so this is `σ_s φ₊ / (4π)`) onto `W⁺ j` gives `σ_s K_{i₀}` for `j = i₀` and `0`
otherwise: the scattering couples only to the constant mode, which is why the K-step needs no
iteration.  In (31) it enters with a minus sign (it comes from `-σ_s φ₊ / (4π)` in (28)).

Deviation: the printed (31) shows the coefficient `+√(1/(4π))` in front of `δ_{j',0} σ_s K₀⁺`;
the projection computed here has coefficient `1` (and the sign of (28) is `-`). -/
theorem scattering_galerkin_of_const_mode [Fintype ι] [DecidableEq ι] {W : ι → H}
    (hW : Orthonormal ℝ W) {one : H} {i₀ : ι}
    (h0 : W i₀ = ‖one‖⁻¹ • one) {J : H →L[ℝ] H} (hJs : ∀ x y, ⟪J x, y⟫ = ⟪x, J y⟫)
    (hJ1 : J one = one) (σs : ℝ) (K : ι → ℝ) (j : ι) :
    ⟪(σs / ‖one‖ ^ 2 * ⟪one, ∑ i, K i • ((2 : ℝ)⁻¹ • (W i + J (W i)))⟫) • one,
        (2 : ℝ)⁻¹ • (W j + J (W j))⟫ = if j = i₀ then σs * K i₀ else 0 := by
  have hne : ‖one‖ ≠ 0 := by
    intro h
    have h1 := hW.1 i₀
    rw [h0, h, inv_zero, zero_smul, norm_zero] at h1
    exact zero_ne_one h1
  have hplus : ∀ i, ⟪one, (2 : ℝ)⁻¹ • (W i + J (W i))⟫ = ⟪one, W i⟫ := by
    intro i
    rw [real_inner_smul_right, inner_add_right, ← hJs, hJ1]
    ring
  have hflux : ⟪one, ∑ i, K i • ((2 : ℝ)⁻¹ • (W i + J (W i)))⟫ = ‖one‖ * K i₀ := by
    simp only [inner_sum, real_inner_smul_right]
    simp only [← real_inner_smul_right, ← inner_sum]
    have : ⟪one, ∑ i, K i • ((2 : ℝ)⁻¹ • (W i + J (W i)))⟫ = ∑ i, K i * ⟪one, W i⟫ := by
      simp only [inner_sum, real_inner_smul_right, hplus]
    rw [this, ← scalarFlux_of_const_mode hW h0 K]
    simp only [inner_sum, real_inner_smul_right]
  rw [real_inner_smul_left, hplus, inner_one_of_const_mode hW h0, hflux]
  split_ifs
  · field_simp
  · ring

end ConstantMode

/-! ### Section 3.3: reduction of the PN-like L-step to an `r × r` system -/

section LStepReduction

variable {r a : Type*} [Fintype r] [DecidableEq r] [Fintype a]

/-- **The L-step reduces to an `r × r` system for the angular mean** (arXiv 2601.18705,
Sec. 3.3, eqs. (35)–(36) and the system for `L̄`; finite-dimensional form).  Replace `∫_{𝕊²}` by
a quadrature `Σ_Ω w_Ω` over finitely many angles.  If `L(Ω)` solves (36),
`B(Ω) L(Ω) - M_s L̄ / (4π) = q(Ω)` with `L̄ = Σ_Ω w_Ω L(Ω)`, and every `B(Ω)` is invertible, then
`L̄ - C̄ M_s L̄ / (4π) = ζ̄` with `C̄ = Σ_Ω w_Ω B(Ω)⁻¹` and `ζ̄ = Σ_Ω w_Ω B(Ω)⁻¹ q(Ω)`. -/
theorem lStep_reduced {w : a → ℝ} {B : a → Matrix r r ℝ} {Ms : Matrix r r ℝ} {q L : a → r → ℝ}
    (hB : ∀ Ω, IsUnit (B Ω).det)
    (hL : ∀ Ω, B Ω *ᵥ L Ω - (4 * π)⁻¹ • (Ms *ᵥ ∑ Ω', w Ω' • L Ω') = q Ω) :
    (∑ Ω, w Ω • L Ω) - (∑ Ω, w Ω • (B Ω)⁻¹) *ᵥ ((4 * π)⁻¹ • (Ms *ᵥ ∑ Ω, w Ω • L Ω)) =
      ∑ Ω, w Ω • ((B Ω)⁻¹ *ᵥ q Ω) := by
  set Lb := ∑ Ω, w Ω • L Ω with hLb
  have hLΩ : ∀ Ω, L Ω = (B Ω)⁻¹ *ᵥ q Ω + (B Ω)⁻¹ *ᵥ ((4 * π)⁻¹ • (Ms *ᵥ Lb)) := by
    intro Ω
    rw [← Matrix.mulVec_add, ← hL Ω, sub_add_cancel, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (hB Ω), Matrix.one_mulVec]
  have hsum : Lb = ∑ Ω, w Ω • ((B Ω)⁻¹ *ᵥ q Ω) +
      ∑ Ω, w Ω • ((B Ω)⁻¹ *ᵥ ((4 * π)⁻¹ • (Ms *ᵥ Lb))) := by
    conv_lhs => rw [hLb]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun Ω _ => ?_
    conv_lhs => rw [hLΩ Ω]
    rw [smul_add]
  rw [Matrix.sum_mulVec]
  simp only [Matrix.smul_mulVec]
  rw [sub_eq_iff_eq_add]
  exact hsum

/-- **Converse of `lStep_reduced`** (arXiv 2601.18705, Sec. 3.3: "Once we solve for `L̄`, we solve
equation (36) for each angle independently").  If `Λ` solves the reduced system
`Λ - C̄ M_s Λ / (4π) = ζ̄`, then `L(Ω) = B(Ω)⁻¹ (q(Ω) + M_s Λ / (4π))` has angular mean `Λ` and
solves (36) at every angle. -/
theorem lStep_of_reduced {w : a → ℝ} {B : a → Matrix r r ℝ} {Ms : Matrix r r ℝ} {q : a → r → ℝ}
    (hB : ∀ Ω, IsUnit (B Ω).det) {Λ : r → ℝ}
    (hΛ : Λ - (∑ Ω, w Ω • (B Ω)⁻¹) *ᵥ ((4 * π)⁻¹ • (Ms *ᵥ Λ)) =
      ∑ Ω, w Ω • ((B Ω)⁻¹ *ᵥ q Ω)) :
    ∑ Ω, w Ω • ((B Ω)⁻¹ *ᵥ (q Ω + (4 * π)⁻¹ • (Ms *ᵥ Λ))) = Λ ∧
      ∀ Ω, B Ω *ᵥ ((B Ω)⁻¹ *ᵥ (q Ω + (4 * π)⁻¹ • (Ms *ᵥ Λ))) -
        (4 * π)⁻¹ • (Ms *ᵥ ∑ Ω', w Ω' • ((B Ω')⁻¹ *ᵥ (q Ω' + (4 * π)⁻¹ • (Ms *ᵥ Λ)))) =
          q Ω := by
  have hmean : ∑ Ω, w Ω • ((B Ω)⁻¹ *ᵥ (q Ω + (4 * π)⁻¹ • (Ms *ᵥ Λ))) = Λ := by
    simp only [Matrix.mulVec_add, smul_add, Finset.sum_add_distrib]
    rw [← hΛ, Matrix.sum_mulVec]
    simp only [Matrix.smul_mulVec]
    abel
  refine ⟨hmean, fun Ω => ?_⟩
  rw [hmean, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hB Ω), Matrix.one_mulVec,
    add_sub_cancel_right]

end LStepReduction

/-! ### Section 4.1 and Appendix 7.2.1: collocation and the scalar flux -/

section Collocation

variable {n r : Type*}

/-- The selection matrix `S = I(:, p)` of the angles `p` turns `Sᵀ W` into the collocation
matrix `Ŵ_{ij} = W_j(Ω⁽ⁱ⁾)` of arXiv 2601.18705, Sec. 4.1. -/
theorem selection_transpose_mul [Fintype n] [DecidableEq n] (W : Matrix n r ℝ) (p : r → n) :
    ((1 : Matrix n n ℝ).submatrix id p)ᵀ * W = W.submatrix p id := by
  ext i j
  simp [Matrix.mul_apply, Matrix.one_apply]

/-- **Collocation recovers the coefficients** (arXiv 2601.18705, Sec. 4.1: `Ψ = Ŵ K`,
`K = Ŵ⁻¹ Ψ`).  If `ψ(x, ·) = Σ_j K_j(x) W_j` (here `W *ᵥ c`) and the collocation matrix
`Ŵ = W(p, :)` is invertible, the values `Ψ_i = ψ(x, Ω⁽ⁱ⁾)` at the selected angles determine the
coefficients: `Ŵ⁻¹ Ψ = c`. -/
theorem collocation_coeffs [Fintype r] [DecidableEq r] {W : Matrix n r ℝ} {p : r → n}
    (hW : IsUnit (W.submatrix p id).det) (c : r → ℝ) :
    (W.submatrix p id)⁻¹ *ᵥ (fun i => (W *ᵥ c) (p i)) = c := by
  have h : (fun i => (W *ᵥ c) (p i)) = W.submatrix p id *ᵥ c := by
    funext i
    simp [Matrix.mulVec, dotProduct]
  rw [h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hW, Matrix.one_mulVec]

/-- **The collocation flux is the quadrature of the DEIM interpolant** (arXiv 2601.18705,
Sec. 4.1, `∫ψ dΩ ≈ βᵀ Ŵ⁻¹ Ψ`, with `β_j = ∫ W_j`; finite-dimensional form).  With a quadrature
`∫ f = w ⬝ᵥ f` and `β = Wᵀ w`, the collocation value `βᵀ Ŵ⁻¹ Ψ` equals the exact quadrature of
`𝒫 f`, where `𝒫 = W (Sᵀ W)⁻¹ Sᵀ` is the core interpolatory (oblique) projector
`LeanDLRA.obliqueProj` for the selection matrix `S` of the angles `p`.  So the error of the
scalar flux is `w ⬝ᵥ (f - 𝒫 f)`, which the core DEIM bounds (`LeanDLRA.norm_sub_obliqueProj_mul_le`)
control. -/
theorem collocation_flux_eq_oblique [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r]
    {W : Matrix n r ℝ} {p : r → n}
    (w f : n → ℝ) :
    (Wᵀ *ᵥ w) ⬝ᵥ ((W.submatrix p id)⁻¹ *ᵥ (fun i => f (p i))) =
      w ⬝ᵥ (obliqueProj W ((1 : Matrix n n ℝ).submatrix id p) *ᵥ f) := by
  have hf : (fun i => f (p i)) = ((1 : Matrix n n ℝ).submatrix id p)ᵀ *ᵥ f := by
    funext i
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  rw [obliqueProj, selection_transpose_mul, hf, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  simp only [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

/-- **The collocation flux is exact on the span of the angular basis** (arXiv 2601.18705,
Sec. 4.1 and Appendix 7.2.1, where it is applied to `f = Ω_i Ω_j`).  If `f = W c` and the
collocation matrix `Ŵ` is invertible, then `βᵀ Ŵ⁻¹ Ψ = ∫ f`. -/
theorem collocation_flux_exact [Fintype n] [Fintype r] [DecidableEq r] {W : Matrix n r ℝ}
    {p : r → n}
    (hW : IsUnit (W.submatrix p id).det) (w : n → ℝ) (c : r → ℝ) :
    (Wᵀ *ᵥ w) ⬝ᵥ ((W.submatrix p id)⁻¹ *ᵥ (fun i => (W *ᵥ c) (p i))) = w ⬝ᵥ (W *ᵥ c) := by
  rw [collocation_coeffs hW, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

end Collocation

/-! ### Section 4.2: DEIM selects distinct angles with an invertible collocation matrix -/

section DEIM

open LeanDLRA.Literature.P2408_16591

variable {N r : ℕ}

/-- **DEIM selects distinct angles** (arXiv 2601.18705, Sec. 4.2: "`R_j(Ω⁽ⁱ⁾) = 0`, therefore
`Ω⁽ʲ⁾ ∉ {Ω⁽¹⁾, …, Ω⁽ʲ⁻¹⁾}`"; finite-dimensional form: the angles are chosen among `N`
discrete directions).  For an orthonormal angular basis `W` and a DEIM selection `p`
(`IsDEIM`, from the formalization of arXiv 2408.16591), the residual of step `j` vanishes at
the earlier points and not at `p j` (`deim_res_facts`), so `p` is injective.  The paper's
argument tacitly needs `R_j ≠ 0`, which orthonormality provides. -/
theorem deim_points_injective {W : Matrix (Fin N) (Fin r) ℝ} {p : Fin r → Fin N}
    (hW : Wᵀ * W = 1) (hp : IsDEIM W p) : Function.Injective p := by
  have key : ∀ i j : Fin r, i < j → p i ≠ p j := by
    intro i j hij hpij
    obtain ⟨h1, -, h3⟩ := deim_res_facts hW hp j.isLt (deimInv_of_le hW hp j.val j.isLt.le)
    have h := h1 i hij
    simp only [Fin.eta] at h h3
    rw [hpij] at h
    exact h3 h
  intro i j hij
  rcases lt_trichotomy i j with h | h | h
  · exact absurd hij (key i j h)
  · exact h
  · exact absurd hij.symm (key j i h)

/-- **The DEIM collocation matrix is invertible** (arXiv 2601.18705, Sec. 4.1–4.3, used for
`K = Ŵ⁻¹ Ψ` and in Algorithm 1, step 4).  For orthonormal `W` and a DEIM selection `p`,
`Ŵ = W(p, :)` is invertible, so `collocation_coeffs` and `collocation_flux_exact` apply. -/
theorem deim_isUnit_det {W : Matrix (Fin N) (Fin r) ℝ} {p : Fin r → Fin N}
    (hW : Wᵀ * W = 1) (hp : IsDEIM W p) : IsUnit (W.submatrix p id).det := by
  obtain ⟨⟨C, -, hC⟩, hB⟩ := deimInv_of_le hW hp r le_rfl
  have hinj := deim_points_injective hW hp
  refine Matrix.isUnit_det_of_right_inverse (B := C.submatrix id p) ?_
  ext i j
  have h1 : (W.submatrix p id * C.submatrix id p) i j = deimProj W p r (p i) (p j) := by
    rw [hC]
    simp [Matrix.mul_apply]
  rw [h1, hB i i.isLt, Matrix.one_apply, Matrix.one_apply]
  simp [hinj.eq_iff]

end DEIM

end LeanDLRA.Literature.P2601_18705
