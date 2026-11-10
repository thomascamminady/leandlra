import LeanDLRA.Foundations.Localization
import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.ProjectorSplitting
import LeanDLRA.Literature.Kinetic.P2303_01856a
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Projectors
import LeanDLRA.LinearAlgebra.LowRank.SepRank

/-!
# Results of arXiv 1902.00424: projector-splitting DLRA for Vlasov-Maxwell, divergence correction

Einkemmer, Ostermann and Piazzola propose a dynamical low-rank integrator for the Vlasov-Maxwell
equations and a Lagrange-multiplier correction of the electric field that enforces Gauss' law. This
module proves the discrete Maxwell theory of their scheme on real grids, the low-rank structure in
the linear regime and the reduction of the projected equations to (15)-(17). **Maxwell part (Secs.
2, 5).** `IsCompatible` says what a discretization has to satisfy, and it is proved for the
periodic Yee scheme, `isCompatible_periodicYee`, and for spectral differentiation on an odd grid,
`isCompatible_spectral`, the discretization of the paper's experiments. On such a grid (27) is
always solvable, `IsCompatible.exists_isPoisson`: the zero mean that solvability needs is derived
(the paper does not discuss solvability), and the
singular `Δ̃` is handled, which `divergence_correction` of `OpenProblems/Conservation/Part4a`
excludes by assuming `D Dᵀ` invertible, an assumption that never holds on these grids. `gauss_law`
is (26), `gauss_iff_isPoisson` its converse, `algorithm2_main` the statement for all steps of
Algorithm 2, with `magnetic_div_free`, `divD_curlD` and its converse `commute_of_divD_curlD`.
Further: `IsCompatible.corrected_best_approx` (the correction is the Leray projection),
`gauss_solvable_iff` (the numerical mass is forced), `correction_zero_iff`, `gauss_defect_doubled`,
`predictor_truncation_le` and `magnetic_truncation_le` (second-order consistency of the staggered
Maxwell steps). **Linear regime (Sec. 3).** `IsModeSolution` is (6)-(8) for a velocity measure and
pointwise in `v`; `IsModeSolution.eq_zero`, `IsModeSolution.unique`, `unexcited_modes_vanish` and
`linear_regime_rank`, which is (9), need only `∫ (1 + |v|)² |∇ᵥ f⁰| dμ < ∞`. In the continuous
setting the paper starts from the Fourier-transformed system (6)-(8) and so do these theorems: the
expansion of `f` in Fourier modes is a hypothesis of `linear_regime_rank`, and
`solves_linearized_of_modes` proves the converse, that the sum (9) solves the linearized equations
in physical space. For the 1D spatial spectral model of Sec. 6 the statement is closed in physical
space: `IsSpectralSolution.modes` is the Fourier transform of the equations and
`spectral_linear_regime_rank` has no such hypothesis. Beyond the paper, `linearized_ksl_exact` and
`ksl_exact_of_invariant`: a KSL step with frozen fields is exact, for every step size, if the new
left basis spans a subspace invariant for the field, with `ε = 0`
(`exists_isKSLStep_of_invariant`); that is DLRA exactness for `r ≥ m + 1`. **Splitting (Sec. 4).**
On a phase-space grid with arbitrary difference matrices, `PhaseGrid.vlasov` is the Vlasov operator
with frozen fields and `PhaseGrid.kStep_reduction`, `sStep_reduction`, `lStep_reduction` are (12) ⇒
(15), (13) ⇒ (16), (14) ⇒ (17), in the coordinates and coefficients of the paper.
`isKSLStep_of_reduced` makes the solutions of (15)-(17) a step of the library's `IsKSLStep`,
`tangentProj_eq_splitting` is (11) (the projector properties are in `Matrix/Projectors`:
`isOrthProj_tangentProj`, `mem_range_tangentProj`), and `frozen_ksl_local_error` with
`PhaseGrid.norm_vlasov_sub_vlasov_le` is the local error with fields frozen at the beginning of the
step. **False claims of the paper, with proofs.** (1) Gauss' law does not follow from the
continuity equation with the sign of (2), `∂ₜ E = ∇ × B - j`, for `j = ∫ v f dv`:
`gauss_not_propagated`, `exists_gauss_violation`, `gauss_not_propagated_continuous`. For the
species of (1), (3) the sign has to be `+ j`, `predictor_gauss_of_continuity`; the theorems on
(23)-(27) hold for any `j`. (2) Eq. (16) as printed, with `d³_kl`, is wrong, it has to be `d³_ik`:
`sStep_printed_false`. (3) The spectral solution `φ̂ₖ = -ĝₖ / k²` of Sec. 6 has the wrong sign:
`poisson_printed_false`, `exists_poisson_printed_false`, `spectral_poisson`. The paper's move to
odd grids is necessary, not a convenience: `gauss_unsolvable_even_grid`,
`not_isCompatible_even_grid`. **Differences and omissions.** The quadrature weights are absorbed in
the grid functions in Sec. 4, and the core `S` may be rectangular. The Fourier transform on the
continuous torus is not formalized, see above; for the same reason `spectral_linear_regime_rank` is
1D in `x`, with `∇̃ = (∂̃ₓ, 0, 0)`, as in Secs. 6-10. Second order of the low-rank part of
Algorithm 1 is not proved: the paper gives no proof, and it is not robust, by
`strangKSL_not_robust_second_order_rankTwo` of `Corrections/StrangNotRobust`; only the Maxwell part
is covered, by a truncation bound and not a global error bound. Non-vacuity:
`exists_isModeSolution`, `exists_isSpectralSolution`, `exists_isAlgorithm2`,
`exists_isKSLStep_of_invariant`.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace LeanDLRA.Literature.P1902_00424

open LeanDLRA Matrix

/-! ### Discrete vector calculus -/

section Calculus

variable {G : Type*} [Fintype G]

/-- A discrete vector field on the grid `G`, by components. -/
abbrev VectorField (G : Type*) := Fin 3 → G → ℝ

/-- The discrete gradient `∇̃ u` built from the difference matrices `D`. -/
def gradD (D : Fin 3 → Matrix G G ℝ) (u : G → ℝ) : VectorField G := fun a => D a *ᵥ u

/-- The discrete divergence `∇̃ · F`. -/
def divD (D : Fin 3 → Matrix G G ℝ) (F : VectorField G) : G → ℝ := ∑ a, D a *ᵥ F a

/-- The discrete curl `∇̃ × F`. -/
def curlD (D : Fin 3 → Matrix G G ℝ) (F : VectorField G) : VectorField G :=
  ![D 1 *ᵥ F 2 - D 2 *ᵥ F 1, D 2 *ᵥ F 0 - D 0 *ᵥ F 2, D 0 *ᵥ F 1 - D 1 *ᵥ F 0]

/-- The mean `|Ω|⁻¹ ∫ ρ` over the grid. -/
noncomputable def mean (ρ : G → ℝ) : ℝ := (∑ x, ρ x) / Fintype.card G

/-- The right-hand side `|Ω|⁻¹ ∫ ρ - ρ` of Gauss' law (3), (26). -/
noncomputable def gaussRhs (ρ : G → ℝ) : G → ℝ := fun x => mean ρ - ρ x

/-- The squared discrete `L²` norm of a vector field. -/
def l2Sq (F : VectorField G) : ℝ := ∑ a, ∑ x, F a x ^ 2

/-- Auxiliary for arXiv 1902.00424, Secs. 2, 5. -/
theorem divD_add (D : Fin 3 → Matrix G G ℝ) (F F' : VectorField G) :
    divD D (F + F') = divD D F + divD D F' := by
  simp only [divD, Pi.add_apply, mulVec_add, Finset.sum_add_distrib]

/-- Auxiliary for arXiv 1902.00424, Secs. 2, 5. -/
theorem divD_sub (D : Fin 3 → Matrix G G ℝ) (F F' : VectorField G) :
    divD D (F - F') = divD D F - divD D F' := by
  simp only [divD, Pi.sub_apply, mulVec_sub, Finset.sum_sub_distrib]

/-- Auxiliary for arXiv 1902.00424, Secs. 2, 5. -/
theorem divD_smul (D : Fin 3 → Matrix G G ℝ) (c : ℝ) (F : VectorField G) :
    divD D (c • F) = c • divD D F := by
  simp only [divD, Pi.smul_apply, mulVec_smul, Finset.smul_sum]

/-- **Discrete div-curl identity** (arXiv 1902.00424, Sec. 2).  If the components of `∇̃` commute,
as they do for spectral differentiation and for the one-sided differences of the Yee scheme, then
`∇̃ · (∇̃ × F) = 0`.  The paper takes this as the requirement on `∇̃`; here it is derived from
commutation, which is also necessary (`commute_of_divD_curlD`). -/
theorem divD_curlD {D : Fin 3 → Matrix G G ℝ} (hD : ∀ a b, Commute (D a) (D b))
    (F : VectorField G) : divD D (curlD D F) = 0 := by
  have h01 := (hD 0 1).eq
  have h02 := (hD 0 2).eq
  have h12 := (hD 1 2).eq
  simp only [divD, curlD, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, mulVec_sub, mulVec_mulVec, h01, h02, h12]
  abel

/-- Auxiliary for arXiv 1902.00424, Secs. 2, 5.  Conversely `∇̃ · (∇̃ × ·) = 0` forces the
components of `∇̃` to commute. -/
theorem commute_of_divD_curlD {D : Fin 3 → Matrix G G ℝ}
    (hD : ∀ F, divD D (curlD D F) = 0) (a b : Fin 3) : Commute (D a) (D b) := by
  have h01 : D 0 * D 1 = D 1 * D 0 := by
    refine Matrix.ext_iff_mulVec.2 fun u => ?_
    have h := hD ![0, 0, u]
    simpa [divD, curlD, Fin.sum_univ_three, mulVec_neg, mulVec_mulVec, add_neg_eq_zero] using h
  have h12 : D 1 * D 2 = D 2 * D 1 := by
    refine Matrix.ext_iff_mulVec.2 fun u => ?_
    have h := hD ![u, 0, 0]
    simpa [divD, curlD, Fin.sum_univ_three, mulVec_neg, mulVec_mulVec, add_neg_eq_zero] using h
  have h20 : D 2 * D 0 = D 0 * D 2 := by
    refine Matrix.ext_iff_mulVec.2 fun u => ?_
    have h := hD ![0, u, 0]
    have h' : -((D 0 * D 2) *ᵥ u) + (D 2 * D 0) *ᵥ u = 0 := by
      simpa [divD, curlD, Fin.sum_univ_three, mulVec_neg, mulVec_mulVec] using h
    exact (neg_add_eq_zero.1 h').symm
  change D a * D b = D b * D a
  fin_cases a <;> fin_cases b <;> simp [h01, h12, h20]

/-- Auxiliary for arXiv 1902.00424, Secs. 2, 5.  `∇̃ × ∇̃ u = 0` for commuting differences: the
correction of Sec. 5 is curl-free. -/
theorem curlD_gradD {D : Fin 3 → Matrix G G ℝ} (hD : ∀ a b, Commute (D a) (D b)) (u : G → ℝ) :
    curlD D (gradD D u) = 0 := by
  have h01 := (hD 0 1).eq
  have h02 := (hD 0 2).eq
  have h12 := (hD 1 2).eq
  funext a x
  fin_cases a <;>
    simp [curlD, gradD, mulVec_mulVec, h01, h02, h12]

/-- Auxiliary for arXiv 1902.00424, Secs. 2, 5. -/
theorem curlD_sub (D : Fin 3 → Matrix G G ℝ) (F F' : VectorField G) :
    curlD D (F - F') = curlD D F - curlD D F' := by
  funext a x
  fin_cases a <;> simp [curlD, mulVec_sub] <;> ring

/-- Auxiliary for arXiv 1902.00424, Secs. 2, 5. -/
theorem curlD_smul (D : Fin 3 → Matrix G G ℝ) (c : ℝ) (F : VectorField G) :
    curlD D (c • F) = c • curlD D F := by
  funext a x
  fin_cases a <;> simp [curlD, mulVec_smul] <;> ring

/-- Auxiliary for arXiv 1902.00424, Secs. 2, 5. -/
theorem l2Sq_add (F F' : VectorField G) :
    l2Sq (F + F') = l2Sq F + 2 * ∑ a, F a ⬝ᵥ F' a + l2Sq F' := by
  simp only [l2Sq, dotProduct, Pi.add_apply, add_sq, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => by ring

/-- Auxiliary for arXiv 1902.00424, Secs. 2, 5. -/
theorem l2Sq_nonneg (F : VectorField G) : 0 ≤ l2Sq F :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Auxiliary for arXiv 1902.00424, Secs. 2, 5. -/
theorem l2Sq_eq_zero {F : VectorField G} (h : l2Sq F = 0) : F = 0 := by
  funext a x
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun a _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)).1 h a (Finset.mem_univ a)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).1 h1 x (Finset.mem_univ x)
  exact pow_eq_zero_iff (two_ne_zero) |>.1 h2

/-- Auxiliary for arXiv 1902.00424, Secs. 2, 5. -/
theorem sum_gaussRhs (ρ : G → ℝ) : ∑ x, gaussRhs ρ x = 0 := by
  classical
  by_cases hG : IsEmpty G
  · simp
  · have : Nonempty G := not_isEmpty_iff.1 hG
    have hc : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    simp only [gaussRhs, mean, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    field_simp
    ring

/-- The discrete operators of a compatible spatial discretization: `dp` are the differences used
for `∇̃ φ` and for `∇̃ × E`, `dm` the ones used for `∇̃ · E` and `∇̃ × B`.  For the Yee scheme these
are forward and backward differences (`isCompatible_yee`); for spectral differentiation `dp = dm`.
The conditions are: the differences commute, `∇̃ ·` is minus the adjoint of `∇̃` and the joint
kernel of `dp` consists exactly of the constants (the grid is connected). -/
structure IsCompatible (dp dm : Fin 3 → Matrix G G ℝ) : Prop where
  comm : ∀ a b, Commute (dp a) (dp b)
  adj : ∀ a, dm a = -(dp a)ᵀ
  ker : ∀ u : G → ℝ, (∀ a, dp a *ᵥ u = 0) ↔ ∃ c : ℝ, u = fun _ => c

/-- The electric update (23): `Ē = Eⁿ + τ ∇̃ × B - τ j`. -/
def predictor (dm : Fin 3 → Matrix G G ℝ) (τ : ℝ) (En B j : VectorField G) : VectorField G :=
  En + τ • curlD dm B - τ • j

/-- The right-hand side of the Poisson problem (27). -/
noncomputable def poissonRhs (dm : Fin 3 → Matrix G G ℝ) (τ : ℝ) (En j : VectorField G)
    (ρ : G → ℝ) : G → ℝ :=
  fun x => (gaussRhs ρ x - divD dm En x) / τ + divD dm j x

/-- The Poisson problem (27): `-Δ̃ φ = (|Ω|⁻¹ ∫ ρ - ρ - ∇̃ · Eⁿ) / τ + ∇̃ · j`, with
`Δ̃ = ∇̃ · ∇̃` the discrete Laplacian. -/
def IsPoisson (dp dm : Fin 3 → Matrix G G ℝ) (τ : ℝ) (En j : VectorField G) (ρ φ : G → ℝ) :
    Prop :=
  -divD dm (gradD dp φ) = poissonRhs dm τ En j ρ

/-- The correction (25): `Eⁿ⁺¹ = Ē - τ ∇̃ φ`. -/
def corrected (dp : Fin 3 → Matrix G G ℝ) (τ : ℝ) (Ebar : VectorField G) (φ : G → ℝ) :
    VectorField G :=
  Ebar - τ • gradD dp φ

/-- Auxiliary for arXiv 1902.00424, Secs. 2, 5. -/
theorem divD_predictor {dm : Fin 3 → Matrix G G ℝ} (hdm : ∀ a b, Commute (dm a) (dm b)) (τ : ℝ)
    (En B j : VectorField G) : divD dm (predictor dm τ En B j) = divD dm En - τ • divD dm j := by
  rw [predictor, divD_sub, divD_add, divD_smul, divD_smul, divD_curlD hdm, smul_zero, add_zero]

/-- **Discrete Gauss law** (arXiv 1902.00424, Sec. 5, (23)-(27)).  If `Ē` is computed by (23) and
`φ` solves (27), the corrected field (25) satisfies `∇̃ · Eⁿ⁺¹ = |Ω|⁻¹ ∫ ρⁿ⁺¹ - ρⁿ⁺¹`, (26),
exactly, whatever `Eⁿ`, `B`, `j` and `ρⁿ⁺¹` are.  Only `∇̃ · (∇̃ × ·) = 0` is used here.
Solvability of (27) is `IsCompatible.exists_isPoisson`. -/
theorem gauss_law {dp dm : Fin 3 → Matrix G G ℝ} (hdm : ∀ a b, Commute (dm a) (dm b)) {τ : ℝ}
    (hτ : τ ≠ 0) {En B j : VectorField G} {ρ φ : G → ℝ} (hφ : IsPoisson dp dm τ En j ρ φ) :
    divD dm (corrected dp τ (predictor dm τ En B j) φ) = gaussRhs ρ := by
  funext x
  have h := congrFun hφ x
  simp only [Pi.neg_apply, poissonRhs] at h
  have h' : divD dm (gradD dp φ) x = -((gaussRhs ρ x - divD dm En x) / τ + divD dm j x) := by
    rw [← h, neg_neg]
  rw [corrected, divD_sub, divD_predictor hdm, divD_smul]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h']
  field_simp
  ring

/-- **(27) is equivalent to (26)** (arXiv 1902.00424, Sec. 5, where (27) is obtained from (25) and
(26)): for `Eⁿ⁺¹ = Ē - τ ∇̃ φ`, Gauss' law holds if and only if `φ` solves (27). -/
theorem gauss_iff_isPoisson {dp dm : Fin 3 → Matrix G G ℝ} (hdm : ∀ a b, Commute (dm a) (dm b))
    {τ : ℝ} (hτ : τ ≠ 0) {En B j : VectorField G} {ρ φ : G → ℝ} :
    divD dm (corrected dp τ (predictor dm τ En B j) φ) = gaussRhs ρ ↔
      IsPoisson dp dm τ En j ρ φ := by
  refine ⟨fun h => ?_, gauss_law hdm hτ⟩
  funext x
  have h1 := congrFun h x
  rw [corrected, divD_sub, divD_predictor hdm, divD_smul] at h1
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1
  simp only [Pi.neg_apply, poissonRhs]
  field_simp
  linarith

/-- Auxiliary for arXiv 1902.00424, Secs. 2, 5.  If the potential of (27) is used with the opposite
sign in (25), the defect of Gauss' law is doubled instead of removed. This is the effect of the
printed sign in `poisson_printed_false`. -/
theorem gauss_defect_doubled {dp dm : Fin 3 → Matrix G G ℝ}
    (hdm : ∀ a b, Commute (dm a) (dm b)) {τ : ℝ} (hτ : τ ≠ 0) {En B j : VectorField G}
    {ρ φ : G → ℝ} (hφ : IsPoisson dp dm τ En j ρ φ) :
    divD dm (corrected dp τ (predictor dm τ En B j) (-φ)) - gaussRhs ρ =
      (2 : ℝ) • (divD dm (predictor dm τ En B j) - gaussRhs ρ) := by
  have h1 := gauss_law (B := B) hdm hτ hφ
  have hg : gradD dp (-φ) = -gradD dp φ := by
    funext a
    simp only [gradD, mulVec_neg, Pi.neg_apply]
  have h2 : corrected dp τ (predictor dm τ En B j) φ =
      predictor dm τ En B j - τ • gradD dp φ := rfl
  have h3 : corrected dp τ (predictor dm τ En B j) (-φ) =
      predictor dm τ En B j + τ • gradD dp φ := by
    rw [corrected, hg, smul_neg, sub_neg_eq_add]
  rw [h2, divD_sub] at h1
  rw [h3, divD_add, ← h1, two_smul]
  abel

namespace IsCompatible

variable {dp dm : Fin 3 → Matrix G G ℝ}

/-- Auxiliary for arXiv 1902.00424, Secs. 2, 5.  The second family of differences commutes as well.
-/
theorem comm_dm (h : IsCompatible dp dm) (a b : Fin 3) : Commute (dm a) (dm b) := by
  have h1 := (h.comm b a).eq
  change dm a * dm b = dm b * dm a
  rw [h.adj, h.adj, neg_mul_neg, neg_mul_neg, ← transpose_mul, ← transpose_mul, h1]

/-- Auxiliary for arXiv 1902.00424, Secs. 2, 5. -/
theorem dp_const (h : IsCompatible dp dm) (a : Fin 3) (c : ℝ) : dp a *ᵥ (fun _ => c) = 0 :=
  (h.ker _).2 ⟨c, rfl⟩ a

/-- Auxiliary for arXiv 1902.00424, Secs. 2, 5. -/
theorem dot_dm (h : IsCompatible dp dm) (a : Fin 3) (u w : G → ℝ) :
    u ⬝ᵥ (dm a *ᵥ w) = -((dp a *ᵥ u) ⬝ᵥ w) := by
  rw [dotProduct_mulVec, h.adj, vecMul_neg, vecMul_transpose, neg_dotProduct]

/-- Auxiliary for arXiv 1902.00424, Secs. 2, 5.  Summation by parts on the grid: `∑ₓ u ∇̃ · F = -∑ₓ
∇̃ u · F`. -/
theorem dot_divD (h : IsCompatible dp dm) (u : G → ℝ) (F : VectorField G) :
    u ⬝ᵥ divD dm F = -∑ a, gradD dp u a ⬝ᵥ F a := by
  rw [divD, dotProduct_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun a _ => h.dot_dm a u (F a)

/-- Auxiliary for arXiv 1902.00424, Secs. 2, 5.  A discrete divergence has zero sum: `∫ ∇̃ · F =
0`. -/
theorem sum_divD (h : IsCompatible dp dm) (F : VectorField G) : ∑ x, divD dm F x = 0 := by
  have h1 := h.dot_divD (fun _ => 1) F
  have h2 : gradD dp (fun _ => (1 : ℝ)) = 0 := by
    funext a
    exact h.dp_const a 1
  simpa [dotProduct, h2] using h1

/-- Auxiliary for arXiv 1902.00424, Secs. 2, 5. -/
theorem grad_eq_zero_of_lap (h : IsCompatible dp dm) {u : G → ℝ}
    (hu : divD dm (gradD dp u) = 0) : gradD dp u = 0 := by
  have h1 := h.dot_divD u (gradD dp u)
  rw [hu, dotProduct_zero] at h1
  have h2 : ∑ a, gradD dp u a ⬝ᵥ gradD dp u a = 0 := by linarith
  funext a
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => by
    simpa [dotProduct] using Finset.sum_nonneg fun x _ => mul_self_nonneg (gradD dp u a x))).1
    h2 a (Finset.mem_univ a)
  exact dotProduct_self_eq_zero.1 h3

/-- Auxiliary for arXiv 1902.00424, Secs. 2, 5. -/
theorem eq_zero_of_lap (h : IsCompatible dp dm) {u : G → ℝ} (hs : ∑ x, u x = 0)
    (hu : divD dm (gradD dp u) = 0) : u = 0 := by
  obtain ⟨c, hc⟩ := (h.ker u).1 (fun a => congrFun (h.grad_eq_zero_of_lap hu) a)
  funext x
  have : Nonempty G := ⟨x⟩
  have hcard : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hc0 : c = 0 := by
    rw [hc] at hs
    simpa [hcard] using hs
  simp [hc, hc0]

/-- Auxiliary for arXiv 1902.00424, Secs. 2, 5.  **Solvability of the periodic discrete Poisson
problem.** For a compatible discretization `Δ̃ φ = g` has a zero-mean solution whenever `g` has
zero mean. `Δ̃` is singular, so this is the statement that `divergence_correction` of
`OpenProblems/Conservation/Part4a`, which assumes `D Dᵀ` invertible, does not cover. -/
theorem exists_poisson (h : IsCompatible dp dm) {g : G → ℝ} (hg : ∑ x, g x = 0) :
    ∃ φ : G → ℝ, ∑ x, φ x = 0 ∧ divD dm (gradD dp φ) = g := by
  let Z : Submodule ℝ (G → ℝ) :=
    { carrier := {u | ∑ x, u x = 0}
      add_mem' := fun {u v} (hu : ∑ x, u x = 0) (hv : ∑ x, v x = 0) => by
        change ∑ x, (u x + v x) = 0
        rw [Finset.sum_add_distrib, hu, hv, add_zero]
      zero_mem' := by simp
      smul_mem' := fun c u (hu : ∑ x, u x = 0) => by
        change ∑ x, c * u x = 0
        rw [← Finset.mul_sum, hu, mul_zero] }
  let A : (G → ℝ) →ₗ[ℝ] (G → ℝ) := Matrix.mulVecLin (∑ a, dm a * dp a)
  have hA : ∀ u, A u = divD dm (gradD dp u) := fun u => by
    simp only [A, mulVecLin_apply, divD, gradD, Matrix.sum_mulVec, mulVec_mulVec]
  have hAZ : ∀ u ∈ Z, A u ∈ Z := fun u _ => by
    change ∑ x, A u x = 0
    rw [hA]
    exact h.sum_divD _
  let T : Z →ₗ[ℝ] Z := A.restrict hAZ
  have hT : Function.Injective T := by
    refine (injective_iff_map_eq_zero T).2 fun u hu => ?_
    have h1 : A (u : G → ℝ) = 0 := congrArg Subtype.val hu
    rw [hA] at h1
    exact Subtype.ext (h.eq_zero_of_lap u.2 h1)
  obtain ⟨φ, hφ⟩ := (LinearMap.injective_iff_surjective.1 hT) ⟨g, hg⟩
  have h2 : A (φ : G → ℝ) = g := congrArg Subtype.val hφ
  exact ⟨φ, φ.2, by rw [← hA, h2]⟩

/-- Auxiliary for arXiv 1902.00424, Secs. 2, 5. -/
theorem sum_poissonRhs (h : IsCompatible dp dm) (τ : ℝ) (En j : VectorField G) (ρ : G → ℝ) :
    ∑ x, poissonRhs dm τ En j ρ x = 0 := by
  simp only [poissonRhs, Finset.sum_add_distrib, div_eq_mul_inv, ← Finset.sum_mul,
    Finset.sum_sub_distrib, sum_gaussRhs, h.sum_divD]
  simp

/-- **The Poisson problem (27) is always solvable** (arXiv 1902.00424, Sec. 5; the paper does not
state solvability).  The zero mean of the right-hand side, which solvability of the singular `Δ̃`
needs and which the choice `φ̂₀ = 0` of Sec. 6 takes for granted, is a consequence: its three terms
are `ρ` minus its numerical mean and two discrete divergences.  The solution is unique up to a
constant (`IsCompatible.gradD_eq_of_isPoisson`). -/
theorem exists_isPoisson (h : IsCompatible dp dm) (τ : ℝ) (En j : VectorField G) (ρ : G → ℝ) :
    ∃ φ : G → ℝ, ∑ x, φ x = 0 ∧ IsPoisson dp dm τ En j ρ φ := by
  have hs : ∑ x, -poissonRhs dm τ En j ρ x = 0 := by
    rw [Finset.sum_neg_distrib, h.sum_poissonRhs, neg_zero]
  obtain ⟨φ, h0, hφ⟩ := h.exists_poisson hs
  exact ⟨φ, h0, by rw [IsPoisson, hφ]; funext x; simp⟩

/-- Auxiliary for arXiv 1902.00424, Secs. 2, 5.  Two solutions of (27) have the same gradient, so
`Eⁿ⁺¹` does not depend on the choice of `φ`, and differ by a constant. -/
theorem gradD_eq_of_isPoisson (h : IsCompatible dp dm) {τ : ℝ} {En j : VectorField G}
    {ρ φ φ' : G → ℝ} (hφ : IsPoisson dp dm τ En j ρ φ) (hφ' : IsPoisson dp dm τ En j ρ φ') :
    gradD dp φ = gradD dp φ' ∧ ∃ c : ℝ, φ - φ' = fun _ => c := by
  have hg : gradD dp (φ - φ') = gradD dp φ - gradD dp φ' := by
    funext a
    simp only [gradD, mulVec_sub, Pi.sub_apply]
  have hl : divD dm (gradD dp (φ - φ')) = 0 := by
    rw [hg, divD_sub]
    have := hφ.trans hφ'.symm
    rw [neg_inj] at this
    rw [this, sub_self]
  have h0 := h.grad_eq_zero_of_lap hl
  refine ⟨sub_eq_zero.1 (hg ▸ h0), (h.ker _).1 fun a => congrFun h0 a⟩

/-- **The divergence correction is the orthogonal (Leray) projection** onto the affine set of
fields with the prescribed divergence (arXiv 1902.00424, Sec. 5; the paper does not state this):
`Ē - Eⁿ⁺¹ = τ ∇̃ φ` is orthogonal to every divergence-free field, hence Pythagoras holds for every
competitor `E'`.  This needs `∇̃ · = -∇̃ᵀ`, which holds for the Yee scheme and for spectral
differentiation. -/
theorem l2Sq_sub_corrected (h : IsCompatible dp dm) (τ : ℝ) (Ebar : VectorField G) (φ : G → ℝ)
    {E' : VectorField G} (hE' : divD dm E' = divD dm (corrected dp τ Ebar φ)) :
    l2Sq (Ebar - E') =
      l2Sq (Ebar - corrected dp τ Ebar φ) + l2Sq (corrected dp τ Ebar φ - E') := by
  set W := corrected dp τ Ebar φ - E' with hW
  have hdW : divD dm W = 0 := by rw [hW, divD_sub, hE', sub_self]
  have hsum : ∑ a, (Ebar - corrected dp τ Ebar φ) a ⬝ᵥ W a = 0 := by
    have h1 := h.dot_divD φ W
    rw [hdW, dotProduct_zero] at h1
    have h2 : ∑ a, gradD dp φ a ⬝ᵥ W a = 0 := by linarith
    have h3 : ∀ a, (Ebar - corrected dp τ Ebar φ) a ⬝ᵥ W a = τ * (gradD dp φ a ⬝ᵥ W a) := by
      intro a
      simp [corrected, smul_dotProduct]
    simp only [h3, ← Finset.mul_sum, h2, mul_zero]
  have hsplit : Ebar - E' = (Ebar - corrected dp τ Ebar φ) + W := by rw [hW]; abel
  rw [hsplit, l2Sq_add, hsum, mul_zero, add_zero]

/-- Auxiliary for arXiv 1902.00424, Secs. 2, 5.  **`Eⁿ⁺¹` is the unique best approximation of `Ē`**
in the set `{E' : ∇̃ · E' = ∇̃ · Eⁿ⁺¹}`. -/
theorem corrected_best_approx (h : IsCompatible dp dm) (τ : ℝ) (Ebar : VectorField G) (φ : G → ℝ)
    {E' : VectorField G} (hE' : divD dm E' = divD dm (corrected dp τ Ebar φ)) :
    l2Sq (Ebar - corrected dp τ Ebar φ) ≤ l2Sq (Ebar - E') ∧
      (l2Sq (Ebar - E') = l2Sq (Ebar - corrected dp τ Ebar φ) →
        E' = corrected dp τ Ebar φ) := by
  have h1 := h.l2Sq_sub_corrected τ Ebar φ hE'
  refine ⟨by linarith [l2Sq_nonneg (corrected dp τ Ebar φ - E')], fun h2 => ?_⟩
  have h3 : l2Sq (corrected dp τ Ebar φ - E') = 0 := by linarith
  exact (sub_eq_zero.1 (l2Sq_eq_zero h3)).symm

/-- **The numerical mass is forced in the constraint** (arXiv 1902.00424, Sec. 5, which stresses
that the numerical and not the analytic mass has to be used in (26)).  On a compatible grid
`∇̃ · E = c - ρ` has a solution if and only if `c` is the numerical mean of `ρ`.  The low-rank
integrator is not mass conserving, so the analytic mass gives an unsolvable constraint as soon as
the mass has drifted. -/
theorem gauss_solvable_iff [Nonempty G] (h : IsCompatible dp dm) (ρ : G → ℝ) (c : ℝ) :
    (∃ F : VectorField G, divD dm F = fun x => c - ρ x) ↔ c = mean ρ := by
  have hcard : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  constructor
  · rintro ⟨F, hF⟩
    have h1 := h.sum_divD F
    rw [hF] at h1
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
    rw [mean, eq_div_iff hcard]
    linarith
  · rintro rfl
    obtain ⟨φ, -, hφ⟩ := h.exists_poisson (sum_gaussRhs ρ)
    exact ⟨gradD dp φ, hφ⟩

end IsCompatible

/-- **Div-free magnetic field** (arXiv 1902.00424, Sec. 2, (19)): the update
`B⁺ = B - τ ∇̃ × E` keeps `∇̃ · B = 0` when `∇̃ · (∇̃ × ·) = 0`. -/
theorem magnetic_div_free {D : Fin 3 → Matrix G G ℝ} (hD : ∀ a b, Commute (D a) (D b)) (τ : ℝ)
    {B E : VectorField G} (hB : divD D B = 0) : divD D (B - τ • curlD D E) = 0 := by
  rw [divD_sub, divD_smul, divD_curlD hD, smul_zero, hB, sub_zero]

/-- Auxiliary for arXiv 1902.00424, Secs. 2, 5.  The correction acts on the longitudinal part only:
`∇̃ × Eⁿ⁺¹ = ∇̃ × Ē`, so that step 6 of Algorithm 2 gives the same `B` as without correction
applied to `Ē`. -/
theorem curlD_corrected {dp : Fin 3 → Matrix G G ℝ} (hdp : ∀ a b, Commute (dp a) (dp b)) (τ : ℝ)
    (Ebar : VectorField G) (φ : G → ℝ) :
    curlD dp (corrected dp τ Ebar φ) = curlD dp Ebar := by
  rw [corrected, curlD_sub, curlD_smul, curlD_gradD hdp, smul_zero, sub_zero]

/-- Auxiliary for arXiv 1902.00424, Secs. 2, 5.  The defect of Gauss' law without correction. If
`Eⁿ` satisfies Gauss' law for `ρⁿ`, the field `Ē` of (23) satisfies it for `ρⁿ⁺¹` iff `(ρⁿ⁺¹ - ρⁿ)
/ τ - ∇̃ · j = (|Ω|⁻¹ ∫ ρⁿ⁺¹ - |Ω|⁻¹ ∫ ρⁿ) / τ`. Note the sign of `∇̃ · j`: see
`gauss_not_propagated`. -/
theorem predictor_gauss_iff {dm : Fin 3 → Matrix G G ℝ} (hdm : ∀ a b, Commute (dm a) (dm b))
    {τ : ℝ} (hτ : τ ≠ 0) {En B j : VectorField G} {ρ ρ' : G → ℝ} (hE : divD dm En = gaussRhs ρ) :
    divD dm (predictor dm τ En B j) = gaussRhs ρ' ↔
      ∀ x, (ρ' x - ρ x) / τ - divD dm j x = (mean ρ' - mean ρ) / τ := by
  rw [divD_predictor hdm, hE]
  constructor
  · intro h x
    have h1 := congrFun h x
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, gaussRhs] at h1
    field_simp
    linarith
  · intro h
    funext x
    have h1 := h x
    field_simp at h1
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, gaussRhs]
    linarith

/-- **The correction is inactive exactly when (23) already satisfies Gauss' law.**  Not stated in
arXiv 1902.00424, it makes precise the motivation of Sec. 5.  If `Eⁿ`
satisfies Gauss' law for `ρⁿ`, the correction `τ ∇̃ φ` of (25) vanishes iff
`(ρⁿ⁺¹ - ρⁿ) / τ - ∇̃ · j = (|Ω|⁻¹ ∫ ρⁿ⁺¹ - |Ω|⁻¹ ∫ ρⁿ) / τ`.  So `φ` measures precisely the
failure of the discrete charge balance of the low-rank integrator. -/
theorem correction_zero_iff {dp dm : Fin 3 → Matrix G G ℝ} (h : IsCompatible dp dm) {τ : ℝ}
    (hτ : τ ≠ 0) {En j : VectorField G} {ρ ρ' φ : G → ℝ} (hE : divD dm En = gaussRhs ρ)
    (hφ : IsPoisson dp dm τ En j ρ' φ) :
    gradD dp φ = 0 ↔ ∀ x, (ρ' x - ρ x) / τ - divD dm j x = (mean ρ' - mean ρ) / τ := by
  have hrhs : ∀ x, poissonRhs dm τ En j ρ' x =
      (mean ρ' - mean ρ) / τ - ((ρ' x - ρ x) / τ - divD dm j x) := by
    intro x
    simp only [poissonRhs, hE, gaussRhs]
    field_simp
    ring
  constructor
  · intro h0 x
    have h1 := congrFun hφ x
    rw [h0] at h1
    have h2 : divD dm (0 : VectorField G) = 0 := by simp [divD]
    rw [h2, hrhs] at h1
    simp only [Pi.neg_apply, Pi.zero_apply, neg_zero] at h1
    linarith
  · intro h0
    refine h.grad_eq_zero_of_lap ?_
    funext x
    have h1 := congrFun hφ x
    rw [hrhs, h0 x, sub_self] at h1
    simpa using h1

/-- **False claim of arXiv 1902.00424, Secs. 2 and 5: Gauss' law does not follow from the
continuity equation with the sign of (2).**  The paper derives (3) from the continuity equation
`∂ₜ ρ + ∇ · j = 0`, with `j = ∫ v f dv`, and the Vlasov equation (1) does give that equation.  But
(2), `∂ₜ E = ∇ × B - j`, has the wrong sign for it: differentiating (3) along (2) gives
`∂ₜ ρ = + ∇ · j`, so that the defect of (3) changes at the rate `-2 ∇ · j`.  Here is the discrete
form.  If `Eⁿ` satisfies Gauss' law and the charge satisfies the discrete continuity equation
`(ρⁿ⁺¹ - ρⁿ) / τ + ∇̃ · j = 0`, then the field of (23) satisfies Gauss' law if and only if
`∇̃ · j = 0`.  The right sign for electrons, the species of (1) and (3), is `∂ₜ E = ∇ × B + j`: see
`predictor_gauss_of_continuity`.  The printed sign recurs in (7), (18), (23), (27), (29), (30).  The
theorems on (23)-(27) hold for any `j`, so they hold verbatim for the repaired sign, with `-j`. -/
theorem gauss_not_propagated {dp dm : Fin 3 → Matrix G G ℝ} (h : IsCompatible dp dm) {τ : ℝ}
    (hτ : τ ≠ 0) {En B j : VectorField G} {ρ ρ' : G → ℝ} (hE : divD dm En = gaussRhs ρ)
    (hcont : ∀ x, (ρ' x - ρ x) / τ + divD dm j x = 0) :
    divD dm (predictor dm τ En B j) = gaussRhs ρ' ↔ divD dm j = 0 := by
  have hsum : ∑ x, ρ' x = ∑ x, ρ x := by
    have h1 : ∑ x, ((ρ' x - ρ x) / τ + divD dm j x) = 0 :=
      Finset.sum_eq_zero fun x _ => hcont x
    rw [Finset.sum_add_distrib, h.sum_divD, add_zero, ← Finset.sum_div, div_eq_zero_iff] at h1
    rw [Finset.sum_sub_distrib] at h1
    exact sub_eq_zero.1 (h1.resolve_right hτ)
  have hmean : mean ρ' = mean ρ := by rw [mean, mean, hsum]
  rw [predictor_gauss_iff h.comm_dm hτ hE, hmean, sub_self, zero_div]
  constructor
  · intro h1
    funext x
    have h2 := h1 x
    have h3 := hcont x
    simp only [Pi.zero_apply]
    linarith
  · intro h1 x
    have h3 := hcont x
    rw [h1] at h3 ⊢
    simpa using h3

/-- With the sign `∂ₜ E = ∇ × B + j` the discrete continuity equation does propagate Gauss' law:
this is the statement of arXiv 1902.00424, Sec. 2, with the sign of (2) repaired. -/
theorem predictor_gauss_of_continuity {dm : Fin 3 → Matrix G G ℝ}
    (hdm : ∀ a b, Commute (dm a) (dm b)) {τ : ℝ} (hτ : τ ≠ 0) {En B j : VectorField G}
    {ρ ρ' : G → ℝ} (hE : divD dm En = gaussRhs ρ)
    (hcont : ∀ x, (ρ' x - ρ x) / τ + divD dm j x = (mean ρ' - mean ρ) / τ) :
    divD dm (predictor dm τ En B (-j)) = gaussRhs ρ' := by
  have hneg : divD dm (-j) = -divD dm j := by
    simp only [divD, Pi.neg_apply, mulVec_neg, Finset.sum_neg_distrib]
  refine (predictor_gauss_iff hdm hτ hE).2 fun x => ?_
  rw [hneg, Pi.neg_apply, sub_neg_eq_add]
  exact hcont x

/-- One run of Algorithm 2 of arXiv 1902.00424 for its Maxwell part.  `E n` is `Eⁿ`, `B n` is
`Bⁿ⁺¹ᐟ²`, and `ρ`, `j` are whatever the low-rank integrator returned: `ρ (n + 1)` is `ρⁿ⁺¹` and
`j n` is `jⁿ⁺¹ᐟ²`. -/
structure IsAlgorithm2 (dp dm : Fin 3 → Matrix G G ℝ) (τ : ℝ) (ρ : ℕ → G → ℝ)
    (j E B : ℕ → VectorField G) (φ : ℕ → G → ℝ) : Prop where
  poisson : ∀ n, IsPoisson dp dm τ (E n) (j n) (ρ (n + 1)) (φ n)
  efield : ∀ n, E (n + 1) = corrected dp τ (predictor dm τ (E n) (B n) (j n)) (φ n)
  bfield : ∀ n, B (n + 1) = B n - τ • curlD dp (E (n + 1))

namespace IsAlgorithm2

variable {dp dm : Fin 3 → Matrix G G ℝ} {τ : ℝ} {ρ : ℕ → G → ℝ} {j E B : ℕ → VectorField G}
  {φ : ℕ → G → ℝ}

/-- **Algorithm 2 enforces Gauss' law** (arXiv 1902.00424, Sec. 5): after every step,
`∇̃ · Eⁿ⁺¹ = |Ω|⁻¹ ∫ ρⁿ⁺¹ - ρⁿ⁺¹` exactly, without any assumption on the charge and the current
the low-rank integrator produces and on the initial field. -/
theorem gauss (hs : IsAlgorithm2 dp dm τ ρ j E B φ) (hdm : ∀ a b, Commute (dm a) (dm b))
    (hτ : τ ≠ 0) (n : ℕ) : divD dm (E (n + 1)) = gaussRhs (ρ (n + 1)) := by
  rw [hs.efield]
  exact gauss_law hdm hτ (hs.poisson n)

/-- **Algorithm 2 keeps the magnetic field divergence-free** (arXiv 1902.00424, Sec. 2). -/
theorem div_free (hs : IsAlgorithm2 dp dm τ ρ j E B φ) (hdp : ∀ a b, Commute (dp a) (dp b))
    (hB : divD dp (B 0) = 0) (n : ℕ) : divD dp (B n) = 0 := by
  induction n with
  | zero => exact hB
  | succ n ih =>
    rw [hs.bfield]
    exact magnetic_div_free hdp τ ih

end IsAlgorithm2

/-- Auxiliary for arXiv 1902.00424, Secs. 2, 5.  **Algorithm 2 runs**: on a compatible grid, from
any initial fields and for any sequences of charge and current, it produces a sequence of fields;
`τ ≠ 0` is not needed for this. -/
theorem exists_isAlgorithm2 {dp dm : Fin 3 → Matrix G G ℝ} (h : IsCompatible dp dm) (τ : ℝ)
    (ρ : ℕ → G → ℝ) (j : ℕ → VectorField G) (E₀ B₀ : VectorField G) :
    ∃ (E B : ℕ → VectorField G) (φ : ℕ → G → ℝ),
      E 0 = E₀ ∧ B 0 = B₀ ∧ IsAlgorithm2 dp dm τ ρ j E B φ := by
  classical
  let pot : ℕ → VectorField G → G → ℝ := fun n En =>
    (h.exists_isPoisson τ En (j n) (ρ (n + 1))).choose
  have hpot : ∀ n En, IsPoisson dp dm τ En (j n) (ρ (n + 1)) (pot n En) := fun n En =>
    (h.exists_isPoisson τ En (j n) (ρ (n + 1))).choose_spec.2
  let next : ℕ → VectorField G × VectorField G → VectorField G × VectorField G := fun n s =>
    let E' := corrected dp τ (predictor dm τ s.1 s.2 (j n)) (pot n s.1)
    (E', s.2 - τ • curlD dp E')
  let st : ℕ → VectorField G × VectorField G := fun n => Nat.rec (E₀, B₀) next n
  refine ⟨fun n => (st n).1, fun n => (st n).2, fun n => pot n (st n).1, rfl, rfl, ?_⟩
  exact ⟨fun n => hpot n _, fun _ => rfl, fun _ => rfl⟩

/-- **Main theorem on Algorithm 2** (arXiv 1902.00424, Secs. 2 and 5).  On a compatible grid, such
as the periodic Yee grid (`isCompatible_periodicYee`) or the odd spectral grid
(`isCompatible_spectral`), and for any `τ ≠ 0`, any charge and current sequences and any initial
fields with `∇̃ · B⁰ = 0`, Algorithm 2 has a run; each of its runs satisfies Gauss' law (26) after
every step and keeps `∇̃ · B = 0`.  Eⁿ⁺¹ is independent of the choice of the potentials
(`IsCompatible.gradD_eq_of_isPoisson`). -/
theorem algorithm2_main {dp dm : Fin 3 → Matrix G G ℝ} (h : IsCompatible dp dm) {τ : ℝ}
    (hτ : τ ≠ 0) (ρ : ℕ → G → ℝ) (j : ℕ → VectorField G) (E₀ B₀ : VectorField G)
    (hB₀ : divD dp B₀ = 0) :
    ∃ (E B : ℕ → VectorField G) (φ : ℕ → G → ℝ), E 0 = E₀ ∧ B 0 = B₀ ∧
      IsAlgorithm2 dp dm τ ρ j E B φ ∧ (∀ n, divD dm (E (n + 1)) = gaussRhs (ρ (n + 1))) ∧
      ∀ n, divD dp (B n) = 0 := by
  obtain ⟨E, B, φ, hE, hB, hs⟩ := exists_isAlgorithm2 h τ ρ j E₀ B₀
  exact ⟨E, B, φ, hE, hB, hs, hs.gauss h.comm_dm hτ, hs.div_free h.comm (hB ▸ hB₀)⟩

/-- Auxiliary for arXiv 1902.00424, Secs. 2, 5.  A violation of Gauss' law under exact charge
conservation, for the sign printed in (2), on every compatible grid with at least two points: all
of `gauss_not_propagated`'s hypotheses hold and Gauss' law fails. -/
theorem exists_gauss_violation [Nontrivial G] {dp dm : Fin 3 → Matrix G G ℝ}
    (h : IsCompatible dp dm) {τ : ℝ} (hτ : τ ≠ 0) :
    ∃ (En B j : VectorField G) (ρ ρ' : G → ℝ), divD dm En = gaussRhs ρ ∧
      (∀ x, (ρ' x - ρ x) / τ + divD dm j x = 0) ∧
      divD dm (predictor dm τ En B j) ≠ gaussRhs ρ' := by
  classical
  obtain ⟨x₀, x₁, hx⟩ := exists_pair_ne G
  let g : G → ℝ := fun x => (if x = x₀ then 1 else 0) - (if x = x₁ then 1 else 0)
  have hg : ∑ x, g x = 0 := by simp [g, Finset.sum_sub_distrib]
  have hg0 : g x₀ = 1 := by simp [g, hx]
  obtain ⟨φ, -, hφ⟩ := h.exists_poisson hg
  refine ⟨0, 0, gradD dp φ, fun _ => 0, fun x => -(τ * g x), ?_, ?_, ?_⟩
  · funext x
    simp [divD, gaussRhs, mean]
  · intro x
    rw [hφ]
    field_simp
    ring
  · intro hG
    have hcont : ∀ x, (-(τ * g x) - 0) / τ + divD dm (gradD dp φ) x = 0 := by
      intro x
      rw [hφ]
      field_simp
      ring
    have hE : divD dm (0 : VectorField G) = gaussRhs fun _ : G => (0 : ℝ) := by
      funext x
      simp [divD, gaussRhs, mean]
    have h1 := (gauss_not_propagated h hτ hE hcont).1 hG
    rw [hφ] at h1
    have h2 := congrFun h1 x₀
    rw [hg0] at h2
    exact one_ne_zero h2

/-- The false claim of `gauss_not_propagated` at the continuous level, in the 1D form (29), (31) of
arXiv 1902.00424, Sec. 6, with `B = 0`:
`E t x = -t sin x`, `j t x = sin x`, `ρ t x = 1 - t cos x`, `n₀ = 1` satisfy (29) `∂ₜ E = -j`, the
continuity equation `∂ₜ ρ + ∂ₓ j = 0` and Gauss' law at `t = 0`, and `n₀` is the mean of `ρ` over a
period; but `∂ₓ E = -t cos x` while `n₀ - ρ = t cos x`. -/
theorem gauss_not_propagated_continuous :
    (∀ t x : ℝ, HasDerivAt (fun s => -s * Real.sin x) (-Real.sin x) t) ∧
      (∀ t x : ℝ, HasDerivAt (fun s => 1 - s * Real.cos x) (-Real.cos x) t) ∧
      (∀ x : ℝ, HasDerivAt Real.sin (Real.cos x) x) ∧
      (∀ t x : ℝ, HasDerivAt (fun y => -t * Real.sin y) (-t * Real.cos x) x) ∧
      (∀ t x : ℝ, -t * Real.cos x = 1 - (1 - t * Real.cos x) ↔ t = 0 ∨ Real.cos x = 0) := by
  refine ⟨fun t x => ?_, fun t x => ?_, Real.hasDerivAt_sin, fun t x => ?_, fun t x => ?_⟩
  · simpa using (hasDerivAt_id t).neg.mul_const (Real.sin x)
  · simpa using ((hasDerivAt_id t).mul_const (Real.cos x)).const_sub 1
  · exact (Real.hasDerivAt_sin x).const_mul (-t)
  · constructor
    · intro h
      have : t * Real.cos x = 0 := by linarith
      exact mul_eq_zero.1 this
    · rintro (h | h) <;> simp [h]

end Calculus

/-! ### The Yee scheme on a periodic grid -/

section Yee

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The forward differences `(u (x + eₐ) - u x) / hₐ` on a finite abelian group with grid steps
`eₐ` and mesh widths `hₐ`. -/
noncomputable def yeeFwd (e : Fin 3 → G) (h : Fin 3 → ℝ) : Fin 3 → Matrix G G ℝ := fun a =>
  Matrix.of fun x y => ((if y = x + e a then 1 else 0) - (if y = x then 1 else 0)) / h a

/-- The backward differences `(u x - u (x - eₐ)) / hₐ`. -/
noncomputable def yeeBwd (e : Fin 3 → G) (h : Fin 3 → ℝ) : Fin 3 → Matrix G G ℝ := fun a =>
  Matrix.of fun x y => ((if y = x then 1 else 0) - (if x = y + e a then 1 else 0)) / h a

/-- Auxiliary for arXiv 1902.00424, Sec. 2. -/
theorem yeeFwd_mulVec (e : Fin 3 → G) (h : Fin 3 → ℝ) (a : Fin 3) (u : G → ℝ) :
    yeeFwd e h a *ᵥ u = fun x => (u (x + e a) - u x) / h a := by
  funext x
  simp [yeeFwd, mulVec, dotProduct, sub_mul, div_mul_eq_mul_div, ← Finset.sum_div,
    Finset.sum_sub_distrib]

/-- Auxiliary for arXiv 1902.00424, Sec. 2. -/
theorem yeeBwd_mulVec (e : Fin 3 → G) (h : Fin 3 → ℝ) (a : Fin 3) (u : G → ℝ) :
    yeeBwd e h a *ᵥ u = fun x => (u x - u (x - e a)) / h a := by
  funext x
  have hx : ∀ y, (x = y + e a) ↔ (y = x - e a) := fun y => by
    rw [eq_sub_iff_add_eq, eq_comm]
  simp [yeeBwd, mulVec, dotProduct, sub_mul, div_mul_eq_mul_div, ← Finset.sum_div,
    Finset.sum_sub_distrib, hx]

/-- Auxiliary for arXiv 1902.00424, Sec. 2. -/
theorem yeeBwd_eq (e : Fin 3 → G) (h : Fin 3 → ℝ) (a : Fin 3) :
    yeeBwd e h a = -(yeeFwd e h a)ᵀ := by
  ext x y
  have h1 : (-(yeeFwd e h a)ᵀ) x y = -(yeeFwd e h a y x) := rfl
  rw [h1]
  simp only [yeeBwd, yeeFwd, of_apply]
  rw [← neg_div, neg_sub]
  simp only [eq_comm (a := y) (b := x)]

/-- **The periodic Yee scheme is compatible** (arXiv 1902.00424, Sec. 2): on any finite abelian
group generated by the grid steps, forward differences (for `∇̃ φ`, `∇̃ × E`, `∇̃ · B`) and backward
differences (for `∇̃ · E`, `∇̃ × B`) satisfy `IsCompatible`.  Connectedness of the grid, i.e. that
only constants have zero gradient, is derived from the generation hypothesis. -/
theorem isCompatible_yee {e : Fin 3 → G} {h : Fin 3 → ℝ} (hh : ∀ a, h a ≠ 0)
    (hgen : AddSubgroup.closure (Set.range e) = ⊤) : IsCompatible (yeeFwd e h) (yeeBwd e h) where
  comm a b := by
    refine Matrix.ext_iff_mulVec.2 fun u => ?_
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    funext x
    simp only [yeeFwd_mulVec, add_right_comm]
    ring
  adj := yeeBwd_eq e h
  ker u := by
    constructor
    · intro hu
      have hstep : ∀ a x, u (x + e a) = u x := fun a x => by
        have h1 := congrFun (hu a) x
        rw [yeeFwd_mulVec] at h1
        simpa [hh a, sub_eq_zero] using h1
      let H : AddSubgroup G :=
        { carrier := {s | ∀ x, u (x + s) = u x}
          add_mem' := fun {s t} (hs : ∀ x, u (x + s) = u x) (ht : ∀ x, u (x + t) = u x) => by
            intro x
            rw [← add_assoc, ht, hs]
          zero_mem' := fun x => by simp
          neg_mem' := fun {s} (hs : ∀ x, u (x + s) = u x) => by
            intro x
            have := hs (x + -s)
            rw [neg_add_cancel_right] at this
            exact this.symm }
      have hH : (⊤ : AddSubgroup G) ≤ H := by
        rw [← hgen, AddSubgroup.closure_le]
        rintro _ ⟨a, rfl⟩
        exact fun x => hstep a x
      refine ⟨u 0, funext fun x => ?_⟩
      have := (hH (AddSubgroup.mem_top x) : ∀ y, u (y + x) = u y) 0
      rwa [zero_add] at this
    · rintro ⟨c, rfl⟩ a
      rw [yeeFwd_mulVec]
      funext x
      simp

end Yee

section PeriodicGrid

/-- The periodic grid with `n a` points in direction `a`.  The paper's cases `dₓ = 1, 2` are
`n = ![N, 1, 1]` and `n = ![N, N', 1]`: `ZMod 1` is trivial and the differences in that direction
vanish. -/
abbrev PeriodicGrid (n : Fin 3 → ℕ) := ∀ a, ZMod (n a)

/-- The unit grid step in direction `a`. -/
def gridStep (n : Fin 3 → ℕ) (a : Fin 3) : PeriodicGrid n := Pi.single a 1

variable (n : Fin 3 → ℕ) [∀ a, NeZero (n a)]

/-- Auxiliary for arXiv 1902.00424, Sec. 2. -/
theorem closure_gridStep : AddSubgroup.closure (Set.range (gridStep n)) = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro x -
  have hx : x = ∑ a, (x a).val • gridStep n a := by
    funext b
    rw [Finset.sum_apply, Finset.sum_eq_single b]
    · simp [gridStep]
    · intro c _ hc
      simp [gridStep, Pi.single_eq_of_ne hc.symm]
    · simp
  rw [hx]
  exact sum_mem fun a _ => nsmul_mem (AddSubgroup.subset_closure (Set.mem_range_self a)) _

/-- Auxiliary for arXiv 1902.00424, Sec. 2.  **The Yee discretization on the periodic grid is
compatible.** So on this grid (27) is always solvable (`IsCompatible.exists_isPoisson`), Algorithm
2 runs (`exists_isAlgorithm2`) and enforces (26) (`IsAlgorithm2.gauss`), and `∇̃ · B` stays zero
(`IsAlgorithm2.div_free`). -/
theorem isCompatible_periodicYee {h : Fin 3 → ℝ} (hh : ∀ a, h a ≠ 0) :
    IsCompatible (yeeFwd (gridStep n) h) (yeeBwd (gridStep n) h) :=
  isCompatible_yee hh (closure_gridStep n)

end PeriodicGrid

/-! ### Low rank in the linear regime -/

section LinearRegime

open MeasureTheory
open Complex (I)

/-- The embedding of real vectors into complex ones. -/
def toC (v : Fin 3 → ℝ) : Fin 3 → ℂ := fun a => (v a : ℂ)

private theorem norm_toC (v : Fin 3 → ℝ) : ‖toC v‖ = ‖v‖ := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun a => ?_
    simpa [toC] using norm_le_pi_norm v a
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun a => ?_
    have := norm_le_pi_norm (toC v) a
    simpa [toC] using this

private theorem norm_dot_le (x y : Fin 3 → ℂ) : ‖x ⬝ᵥ y‖ ≤ 3 * (‖x‖ * ‖y‖) := by
  have h : ∀ a, ‖x a * y a‖ ≤ ‖x‖ * ‖y‖ := fun a => by
    rw [norm_mul]
    exact mul_le_mul (norm_le_pi_norm x a) (norm_le_pi_norm y a) (norm_nonneg _) (norm_nonneg _)
  have h1 : ‖x ⬝ᵥ y‖ ≤ ∑ a, ‖x a * y a‖ := by
    simpa [dotProduct] using norm_sum_le Finset.univ fun a => x a * y a
  have h2 : ∑ a, ‖x a * y a‖ ≤ 3 * (‖x‖ * ‖y‖) := by
    calc _ ≤ ∑ _a : Fin 3, ‖x‖ * ‖y‖ := Finset.sum_le_sum fun a _ => h a
      _ = _ := by simp
  exact h1.trans h2

private theorem norm_cross_le (x y : Fin 3 → ℂ) : ‖x ⨯₃ y‖ ≤ 2 * (‖x‖ * ‖y‖) := by
  have hm : ∀ a b, ‖x a * y b‖ ≤ ‖x‖ * ‖y‖ := fun a b => by
    rw [norm_mul]
    exact mul_le_mul (norm_le_pi_norm x a) (norm_le_pi_norm y b) (norm_nonneg _) (norm_nonneg _)
  have hs : ∀ a b c d, ‖x a * y b - x c * y d‖ ≤ 2 * (‖x‖ * ‖y‖) := fun a b c d => by
    have := norm_sub_le (x a * y b) (x c * y d)
    linarith [hm a b, hm c d]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun a => ?_
  rw [cross_apply]
  fin_cases a
  · exact hs 1 2 2 1
  · exact hs 2 0 0 2
  · exact hs 0 1 1 0

/-- `(f, E, B)` solves the system (6)-(8) of arXiv 1902.00424, for one Fourier mode `k`, on
`[0, T]`:

    ∂ₜ f̂(t, v) + i (v · k) f̂(t, v) - (Ê(t) + v × B̂(t)) · ∇ᵥ f⁰(v) = 0,
    ∂ₜ Ê(t) = i k × B̂(t) - s - ∫ v f̂(t, v) dμ(v),
    ∂ₜ B̂(t) = -i k × Ê(t).

Here `g = ∇ᵥ f⁰`, `μ` is the velocity measure (Lebesgue measure on `Ω_v`, or a quadrature rule) and
`s = j⁰ δ_{k,0}` is the source of (7).  Equation (6) holds for every `v`.  The derivatives are the
right derivatives of `ODESolution`, which only makes the solution class larger, and the current
`∫ v f̂ dμ` is required to exist. -/
structure IsModeSolution (μ : Measure (Fin 3 → ℝ)) (g : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (s : Fin 3 → ℂ) (k : Fin 3 → ℝ) (T : ℝ) (f : ℝ → (Fin 3 → ℝ) → ℂ)
    (E B : ℝ → Fin 3 → ℂ) : Prop where
  vlasov : ∀ v, ODESolution (fun t z => -(I * ((v ⬝ᵥ k : ℝ) : ℂ)) * z +
    (E t + toC v ⨯₃ B t) ⬝ᵥ toC (g v)) (fun t => f t v) 0 T
  ampere : ODESolution (fun t _ => I • (toC k ⨯₃ B t) - s - ∫ v, f t v • toC v ∂μ) E 0 T
  faraday : ODESolution (fun t _ => -(I • (toC k ⨯₃ E t))) B 0 T
  integrable : ∀ t ∈ Icc (0 : ℝ) T, Integrable (fun v => f t v • toC v) μ

private theorem hasDerivAt_phase (ω t : ℝ) :
    HasDerivAt (fun r : ℝ => Complex.exp (I * ω * r))
      (Complex.exp (I * ω * t) * (I * ω)) t := by
  have h1 : HasDerivAt (fun r : ℝ => I * ω * (r : ℂ)) (I * ω) t := by
    simpa using ((hasDerivAt_id t).ofReal_comp).const_mul (I * (ω : ℂ))
  have h2 : HasDerivAt (fun r : ℝ => Complex.exp (I * ω * r))
      ((I * ω) • Complex.exp (I * ω * t)) t := (Complex.hasDerivAt_exp (I * ω * t)).scomp t h1
  rw [smul_eq_mul] at h2
  exact h2.congr_deriv (mul_comm _ _)

private theorem norm_phase (ω t : ℝ) : ‖Complex.exp (I * ω * t)‖ = 1 := by
  have h : I * (ω : ℂ) * (t : ℂ) = ((ω * t : ℝ) : ℂ) * I := by push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- **Uniqueness of the zero solution of (6)-(8)** (arXiv 1902.00424, Sec. 3): with zero source and
zero initial data, the mode stays zero, `f̂ = 0`, `Ê = 0`, `B̂ = 0`.  The only assumption on the
equilibrium is the moment bound `∫ (1 + |v|)² |∇ᵥ f⁰| dμ < ∞`, which holds for a Gaussian on `ℝ³`
and for every bounded `∇ᵥ f⁰` on a bounded `Ω_v`; the operator of (6)-(8) is not assumed bounded
(`v · k` need not be).  The proof removes the transport term `i (v · k)` by an integrating factor
and applies Grönwall to `∫₀ᵗ (|Ê| + |B̂|) + ∫₀ᵗ ∫₀ˢ (|Ê| + |B̂|)`. -/
theorem IsModeSolution.eq_zero {μ : Measure (Fin 3 → ℝ)} {g : (Fin 3 → ℝ) → Fin 3 → ℝ}
    {k : Fin 3 → ℝ} {T : ℝ} {f : ℝ → (Fin 3 → ℝ) → ℂ} {E B : ℝ → Fin 3 → ℂ}
    (h : IsModeSolution μ g 0 k T f E B)
    (hμ : Integrable (fun v => (1 + ‖v‖) ^ 2 * ‖g v‖) μ)
    (hf0 : ∀ v, f 0 v = 0) (hE0 : E 0 = 0) (hB0 : B 0 = 0) :
    ∀ t ∈ Icc (0 : ℝ) T, (∀ v, f t v = 0) ∧ E t = 0 ∧ B t = 0 := by
  intro t₀ ht₀
  have hT : 0 ≤ T := ht₀.1.trans ht₀.2
  let e : ℝ → ℝ := fun t => ‖E t‖ + ‖B t‖
  have he : ContinuousOn e (Icc 0 T) := h.ampere.cont.norm.add h.faraday.cont.norm
  let e' : ℝ → ℝ := Set.IccExtend hT (fun t : Icc (0 : ℝ) T => e t)
  have he'c : Continuous e' := (continuousOn_iff_continuous_domRestrict.1 he).Icc_extend'
  have he'eq : ∀ t ∈ Icc (0 : ℝ) T, e' t = e t := fun t ht => IccExtend_of_mem hT _ ht
  have he'nn : ∀ t, 0 ≤ e' t := fun t => by
    change 0 ≤ ‖E _‖ + ‖B _‖
    positivity
  let W : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, e' s
  have hWd : ∀ t, HasDerivAt W (e' t) t := fun t =>
    (he'c.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hWc : Continuous W := continuous_iff_continuousAt.2 fun t => (hWd t).continuousAt
  let U : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, W s
  have hUd : ∀ t, HasDerivAt U (W t) t := fun t =>
    (hWc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hUc : Continuous U := continuous_iff_continuousAt.2 fun t => (hUd t).continuousAt
  have hW0 : W 0 = 0 := intervalIntegral.integral_same
  have hU0 : U 0 = 0 := intervalIntegral.integral_same
  have hWnn : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ W t := fun t ht =>
    intervalIntegral.integral_nonneg ht.1 fun s _ => he'nn s
  have hUnn : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ U t := fun t ht =>
    intervalIntegral.integral_nonneg ht.1 fun s hs => hWnn s ⟨hs.1, hs.2.trans ht.2⟩
  -- pointwise bound of `f`
  have hfb : ∀ v, ∀ t ∈ Icc (0 : ℝ) T, ‖f t v‖ ≤ 6 * (1 + ‖v‖) * ‖g v‖ * W t := by
    intro v t ht
    set ω : ℝ := v ⬝ᵥ k with hω
    let c : ℝ := 6 * (1 + ‖v‖) * ‖g v‖
    have hc : 0 ≤ c := by positivity
    let F : ℝ → ℂ := fun r => Complex.exp (I * ω * r) * f r v
    let F' : ℝ → ℂ := fun r => Complex.exp (I * ω * r) * ((E r + toC v ⨯₃ B r) ⬝ᵥ toC (g v))
    have hsol := h.vlasov v
    have hFc : ContinuousOn F (Icc 0 T) :=
      (continuous_iff_continuousAt.2 fun r =>
        (hasDerivAt_phase ω r).continuousAt).continuousOn.mul hsol.cont
    have hFd : ∀ r ∈ Ico (0 : ℝ) T, HasDerivWithinAt F (F' r) (Ici r) r := by
      intro r hr
      have h1 := (hasDerivAt_phase ω r).hasDerivWithinAt (s := Ici r)
      have h2 := hsol.deriv r hr
      have h3 := h1.mul h2
      refine h3.congr_deriv ?_
      simp only [F']
      ring
    have hF'b : ∀ r ∈ Ico (0 : ℝ) T, ‖F' r‖ ≤ c * e' r := by
      intro r hr
      have hr' : r ∈ Icc (0 : ℝ) T := ⟨hr.1, hr.2.le⟩
      rw [he'eq r hr']
      simp only [F', norm_mul, norm_phase, one_mul]
      have h1 := norm_dot_le (E r + toC v ⨯₃ B r) (toC (g v))
      have h2 := norm_cross_le (toC v) (B r)
      have h3 := norm_add_le (E r) (toC v ⨯₃ B r)
      rw [norm_toC] at h1 h2
      have h4 : ‖E r + toC v ⨯₃ B r‖ ≤ 2 * (1 + ‖v‖) * e r := by
        simp only [e]
        nlinarith [norm_nonneg v, norm_nonneg (E r), norm_nonneg (B r)]
      calc _ ≤ 3 * (‖E r + toC v ⨯₃ B r‖ * ‖g v‖) := h1
        _ ≤ 3 * (2 * (1 + ‖v‖) * e r * ‖g v‖) := by gcongr
        _ = c * e r := by simp only [c]; ring
    have hb := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := F) (f' := F')
      (B := fun r => c * W r) (B' := fun r => c * e' r) hFc hFd
      (by simp [F, hf0, hW0]) (fun r => (hWd r).const_mul c) hF'b ht
    have hnorm : ‖F t‖ = ‖f t v‖ := by
      simp only [F, norm_mul, norm_phase, one_mul]
    rwa [hnorm] at hb
  -- bound of the current
  let K : ℝ := 6 * ∫ v, (1 + ‖v‖) ^ 2 * ‖g v‖ ∂μ
  have hK : 0 ≤ K := mul_nonneg (by norm_num) (integral_nonneg fun v => by positivity)
  have hJ : ∀ t ∈ Icc (0 : ℝ) T, ‖∫ v, f t v • toC v ∂μ‖ ≤ K * W t := by
    intro t ht
    have h1 : ∀ v, ‖f t v • toC v‖ ≤ (6 * W t) * ((1 + ‖v‖) ^ 2 * ‖g v‖) := by
      intro v
      rw [norm_smul, norm_toC]
      have h2 := hfb v t ht
      have hw := hWnn t ht
      calc ‖f t v‖ * ‖v‖ ≤ (6 * (1 + ‖v‖) * ‖g v‖ * W t) * (1 + ‖v‖) :=
            mul_le_mul h2 (by linarith) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have h2 := norm_integral_le_of_norm_le (hμ.const_mul (6 * W t))
      (Filter.Eventually.of_forall h1)
    rw [integral_const_mul] at h2
    calc _ ≤ _ := h2
      _ = K * W t := by simp only [K]; ring
  -- bounds of `E` and `B`
  have hBb : ∀ t ∈ Icc (0 : ℝ) T, ‖B t‖ ≤ 2 * ‖k‖ * W t := by
    intro t ht
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := B)
      (f' := fun r => -(I • (toC k ⨯₃ E r))) (B := fun r => 2 * ‖k‖ * W r)
      (B' := fun r => 2 * ‖k‖ * e' r) h.faraday.cont h.faraday.deriv
      (by simp [hB0, hW0]) (fun r => (hWd r).const_mul _) (fun r hr => ?_) ht
    have hr' : r ∈ Icc (0 : ℝ) T := ⟨hr.1, hr.2.le⟩
    rw [he'eq r hr', norm_neg, norm_smul, Complex.norm_I, one_mul]
    have h1 := norm_cross_le (toC k) (E r)
    rw [norm_toC] at h1
    have h2 : ‖E r‖ ≤ e r := by simp only [e]; linarith [norm_nonneg (B r)]
    calc _ ≤ 2 * (‖k‖ * ‖E r‖) := h1
      _ ≤ 2 * (‖k‖ * e r) := by gcongr
      _ = _ := by ring
  have hEb : ∀ t ∈ Icc (0 : ℝ) T, ‖E t‖ ≤ 2 * ‖k‖ * W t + K * U t := by
    intro t ht
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := E)
      (f' := fun r => I • (toC k ⨯₃ B r) - 0 - ∫ v, f r v • toC v ∂μ)
      (B := fun r => 2 * ‖k‖ * W r + K * U r)
      (B' := fun r => 2 * ‖k‖ * e' r + K * W r) h.ampere.cont h.ampere.deriv
      (by simp [hE0, hW0, hU0]) (fun r => ((hWd r).const_mul _).add ((hUd r).const_mul _))
      (fun r hr => ?_) ht
    have hr' : r ∈ Icc (0 : ℝ) T := ⟨hr.1, hr.2.le⟩
    rw [he'eq r hr', sub_zero]
    have h1 := norm_cross_le (toC k) (B r)
    rw [norm_toC] at h1
    have h2 : ‖B r‖ ≤ e r := by simp only [e]; linarith [norm_nonneg (E r)]
    have h3 := hJ r hr'
    have h4 := norm_sub_le (I • (toC k ⨯₃ B r)) (∫ v, f r v • toC v ∂μ)
    rw [norm_smul, Complex.norm_I, one_mul] at h4
    have h5 : ‖k‖ * ‖B r‖ ≤ ‖k‖ * e r := by gcongr
    linarith
  -- Grönwall
  let L : ℝ := 4 * ‖k‖ + 1 + K
  have hY : ∀ t ∈ Icc (0 : ℝ) T, ‖W t + U t‖ ≤ gronwallBound 0 L 0 (t - 0) := by
    refine norm_le_gronwallBound_of_norm_deriv_right_le (f' := fun r => e' r + W r)
      (hWc.add hUc).continuousOn (fun r _ => ((hWd r).add (hUd r)).hasDerivWithinAt)
      (by simp [hW0, hU0]) (fun r hr => ?_)
    have hr' : r ∈ Icc (0 : ℝ) T := ⟨hr.1, hr.2.le⟩
    have hw := hWnn r hr'
    have hu := hUnn r hr'
    have h1 := hEb r hr'
    have h2 := hBb r hr'
    have he2 := he'eq r hr'
    have he3 : e' r ≤ 4 * ‖k‖ * W r + K * U r := by
      rw [he2]
      simp only [e]
      linarith
    rw [Real.norm_of_nonneg (by linarith [he'nn r]), Real.norm_of_nonneg (by linarith), add_zero]
    have hk : 0 ≤ ‖k‖ * U r := by positivity
    have hK2 : 0 ≤ K * W r := by positivity
    simp only [L]
    nlinarith
  have hY0 := hY t₀ ht₀
  rw [gronwallBound_ε0_δ0, norm_le_zero_iff] at hY0
  have hw0 : W t₀ = 0 := by linarith [hWnn t₀ ht₀, hUnn t₀ ht₀]
  have hu0 : U t₀ = 0 := by linarith [hWnn t₀ ht₀, hUnn t₀ ht₀]
  refine ⟨fun v => ?_, ?_, ?_⟩
  · have := hfb v t₀ ht₀
    rw [hw0, mul_zero] at this
    exact norm_le_zero_iff.1 this
  · have := hEb t₀ ht₀
    rw [hw0, hu0, mul_zero, mul_zero, add_zero] at this
    exact norm_le_zero_iff.1 this
  · have := hBb t₀ ht₀
    rw [hw0, mul_zero] at this
    exact norm_le_zero_iff.1 this

/-- Auxiliary for arXiv 1902.00424, Sec. 3.  The difference of two solutions of (6)-(8) with the
same source solves the homogeneous system. -/
theorem IsModeSolution.sub {μ : Measure (Fin 3 → ℝ)} {g : (Fin 3 → ℝ) → Fin 3 → ℝ}
    {s : Fin 3 → ℂ} {k : Fin 3 → ℝ} {T : ℝ} {f f' : ℝ → (Fin 3 → ℝ) → ℂ}
    {E E' B B' : ℝ → Fin 3 → ℂ} (h : IsModeSolution μ g s k T f E B)
    (h' : IsModeSolution μ g s k T f' E' B') :
    IsModeSolution μ g 0 k T (f - f') (E - E') (B - B') where
  vlasov v := by
    refine ⟨(h.vlasov v).cont.sub (h'.vlasov v).cont, fun t ht => ?_⟩
    refine ((h.vlasov v).deriv t ht).sub ((h'.vlasov v).deriv t ht) |>.congr_deriv ?_
    simp only [Pi.sub_apply, map_sub, mul_sub, sub_dotProduct, add_dotProduct]
    ring
  ampere := by
    refine ⟨h.ampere.cont.sub h'.ampere.cont, fun t ht => ?_⟩
    refine (h.ampere.deriv t ht).sub (h'.ampere.deriv t ht) |>.congr_deriv ?_
    have ht' : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.le⟩
    have hi : ∫ v, (f - f') t v • toC v ∂μ =
        (∫ v, f t v • toC v ∂μ) - ∫ v, f' t v • toC v ∂μ := by
      rw [← integral_sub (h.integrable t ht') (h'.integrable t ht')]
      simp only [Pi.sub_apply, sub_smul]
    rw [hi]
    simp only [Pi.sub_apply, map_sub, smul_sub]
    abel
  faraday := by
    refine ⟨h.faraday.cont.sub h'.faraday.cont, fun t ht => ?_⟩
    refine (h.faraday.deriv t ht).sub (h'.faraday.deriv t ht) |>.congr_deriv ?_
    simp only [Pi.sub_apply, map_sub, smul_sub]
    abel
  integrable t ht := by
    refine ((h.integrable t ht).sub (h'.integrable t ht)).congr (ae_of_all _ fun v => ?_)
    simp only [Pi.sub_apply, sub_smul]

/-- **Uniqueness for the Fourier-mode system (6)-(8)** (arXiv 1902.00424, Sec. 3): for any source,
two solutions with the same initial data coincide on `[0, T]`.  See `IsModeSolution.eq_zero`. -/
theorem IsModeSolution.unique {μ : Measure (Fin 3 → ℝ)} {g : (Fin 3 → ℝ) → Fin 3 → ℝ}
    {s : Fin 3 → ℂ} {k : Fin 3 → ℝ} {T : ℝ} {f f' : ℝ → (Fin 3 → ℝ) → ℂ}
    {E E' B B' : ℝ → Fin 3 → ℂ} (h : IsModeSolution μ g s k T f E B)
    (h' : IsModeSolution μ g s k T f' E' B')
    (hμ : Integrable (fun v => (1 + ‖v‖) ^ 2 * ‖g v‖) μ) (hf0 : ∀ v, f 0 v = f' 0 v)
    (hE0 : E 0 = E' 0) (hB0 : B 0 = B' 0) :
    ∀ t ∈ Icc (0 : ℝ) T, (∀ v, f t v = f' t v) ∧ E t = E' t ∧ B t = B' t := by
  intro t ht
  obtain ⟨h1, h2, h3⟩ := (h.sub h').eq_zero hμ (fun v => by simp [hf0])
    (by simp [hE0]) (by simp [hB0]) t ht
  exact ⟨fun v => sub_eq_zero.1 (h1 v), sub_eq_zero.1 h2, sub_eq_zero.1 h3⟩

/-- **Unexcited Fourier modes stay zero** (arXiv 1902.00424, Sec. 3).  Let `(f i, E i, B i)` be
solutions of (6)-(8) for the wave vectors `κ i`, with source `j⁰ δ_{κ i, 0}`.  Let `S` contain every
index with `κ i = 0`, and let the initial data of `f` and `B` vanish outside `S`.  If `E` is
initialized by Gauss' law in Fourier space, `Ê_k(0) = (i k / k²) ∫ f̂_k(0, v) dv` for `k ≠ 0`, then
`f i`, `E i`, `B i` vanish identically for `i ∉ S`.  With `S = {k₀ = 0, k₁, …, k_m}` this is the
paper's statement; the constant mode is excited by `j⁰`, and it is why `0` must be in `S`. -/
theorem unexcited_modes_vanish {ι : Type*} {μ : Measure (Fin 3 → ℝ)}
    {g : (Fin 3 → ℝ) → Fin 3 → ℝ} {j0 : Fin 3 → ℂ} {κ : ι → Fin 3 → ℝ} {T : ℝ}
    {f : ι → ℝ → (Fin 3 → ℝ) → ℂ} {E B : ι → ℝ → Fin 3 → ℂ}
    (hsol : ∀ i, IsModeSolution μ g (if κ i = 0 then j0 else 0) (κ i) T (f i) (E i) (B i))
    (hμ : Integrable (fun v => (1 + ‖v‖) ^ 2 * ‖g v‖) μ) {S : Finset ι}
    (hS : ∀ i, κ i = 0 → i ∈ S) (hf0 : ∀ i ∉ S, ∀ v, f i 0 v = 0) (hB0 : ∀ i ∉ S, B i 0 = 0)
    (hE0 : ∀ i, κ i ≠ 0 →
      E i 0 = ((I / ((κ i ⬝ᵥ κ i : ℝ) : ℂ)) * ∫ v, f i 0 v ∂μ) • toC (κ i)) :
    ∀ i ∉ S, ∀ t ∈ Icc (0 : ℝ) T, (∀ v, f i t v = 0) ∧ E i t = 0 ∧ B i t = 0 := by
  intro i hi
  have hk : κ i ≠ 0 := fun h => hi (hS i h)
  have hs : (if κ i = 0 then j0 else 0) = 0 := by simp [hk]
  have hsol' := hsol i
  rw [hs] at hsol'
  refine hsol'.eq_zero hμ (hf0 i hi) ?_ (hB0 i hi)
  rw [hE0 i hk]
  simp [hf0 i hi]

/-- `u` has rank at most `r` in the sense of (10) of arXiv 1902.00424: it is a sum of `r` products
of a function of the first variable and a function of the second. -/
def HasSepRankLE {X Y : Type*} (u : X → Y → ℂ) (r : ℕ) : Prop :=
  ∃ (a : Fin r → X → ℂ) (b : Fin r → Y → ℂ), ∀ x y, u x y = ∑ i, a i x * b i y

/-- Auxiliary for arXiv 1902.00424, Sec. 3.  Separation rank bounds the rank of every matrix of
samples: the discretized `f` on any grid. -/
theorem HasSepRankLE.rank_le {X Y p q : Type*} [Finite p] [Fintype q] {u : X → Y → ℂ} {r : ℕ}
    (h : HasSepRankLE u r) (xs : p → X) (ys : q → Y) :
    (Matrix.of fun i j => u (xs i) (ys j)).rank ≤ r := by
  classical
  have := Fintype.ofFinite p
  obtain ⟨a, b, hu⟩ := h
  have h1 : (Matrix.of fun i j => u (xs i) (ys j)) =
      (Matrix.of fun i l => a l (xs i)) * (Matrix.of fun l j => b l (ys j)) := by
    ext i j
    simp [Matrix.mul_apply, hu]
  rw [h1]
  exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans (by simp))

/-- The plane wave `e^{i k · x}`. -/
noncomputable def planeWave (k x : Fin 3 → ℝ) : ℂ := Complex.exp (I * ((k ⬝ᵥ x : ℝ) : ℂ))

/-- A finite sum of separated terms, one of them with a constant first factor, plus a function of
the second variable, has separation rank at most the number of terms. -/
private theorem hasSepRankLE_of_sum {ι X Y : Type*} [DecidableEq ι] {S : Finset ι} {i₀ : ι}
    (hi₀ : i₀ ∈ S) (e : ι → X → ℂ) (he : ∀ x, e i₀ x = 1) (c : ι → Y → ℂ) (f0 : Y → ℂ)
    {u : X → Y → ℂ} (hu : ∀ x y, u x y = f0 y + ∑ i ∈ S, c i y * e i x) :
    HasSepRankLE u S.card := by
  let σ := S.equivFin
  refine ⟨fun l x => e (σ.symm l) x,
    fun l y => (if (σ.symm l : ι) = i₀ then f0 y else 0) + c (σ.symm l) y, fun x y => ?_⟩
  have h1 : ∀ w : S → ℂ, ∑ l, w (σ.symm l) = ∑ i, w i := fun w => σ.symm.sum_comp w
  rw [hu, h1 (fun i => e i x * ((if (i : ι) = i₀ then f0 y else 0) + c i y)),
    Finset.sum_coe_sort S (fun i => e i x * ((if i = i₀ then f0 y else 0) + c i y))]
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', hi₀,
    ite_true, he, one_mul]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **Rank bound in the linear regime, (9) of arXiv 1902.00424** (Sec. 3).  In the setting of
`unexcited_modes_vanish`, let `f⁰ + F t` be a function whose perturbation `F t` has the `f i t` as
Fourier coefficients.  Then `F t x v = ∑_{i ∈ S} f̂_i(t, v) e^{i κ_i x}` and, as soon as `S`
contains an index of the zero wave vector, `f⁰(v) + F t x v` has rank at most `|S|`.  With
`S = {k₀ = 0, k₁, …, k_m}` the rank is at most `m + 1`, for all `t`.

The paper starts from (6)-(8) after a Fourier transform in `x`; so does this theorem, and the
expansion of `F` in Fourier modes is its hypothesis `hF`.  In the converse direction,
`solves_linearized_of_modes` shows that the finite sum does solve the linearized equations in
physical space. -/
theorem linear_regime_rank {ι : Type*} {μ : Measure (Fin 3 → ℝ)}
    {g : (Fin 3 → ℝ) → Fin 3 → ℝ} {j0 : Fin 3 → ℂ} {κ : ι → Fin 3 → ℝ} {T : ℝ}
    {f : ι → ℝ → (Fin 3 → ℝ) → ℂ} {E B : ι → ℝ → Fin 3 → ℂ}
    (hsol : ∀ i, IsModeSolution μ g (if κ i = 0 then j0 else 0) (κ i) T (f i) (E i) (B i))
    (hμ : Integrable (fun v => (1 + ‖v‖) ^ 2 * ‖g v‖) μ) {S : Finset ι}
    (hS : ∀ i, κ i = 0 → i ∈ S) (hf0 : ∀ i ∉ S, ∀ v, f i 0 v = 0) (hB0 : ∀ i ∉ S, B i 0 = 0)
    (hE0 : ∀ i, κ i ≠ 0 →
      E i 0 = ((I / ((κ i ⬝ᵥ κ i : ℝ) : ℂ)) * ∫ v, f i 0 v ∂μ) • toC (κ i))
    {i₀ : ι} (hi₀ : κ i₀ = 0) (f0 : (Fin 3 → ℝ) → ℂ) {F : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℂ}
    (hF : ∀ t x v, HasSum (fun i => f i t v * planeWave (κ i) x) (F t x v)) :
    ∀ t ∈ Icc (0 : ℝ) T,
      (∀ x v, F t x v = ∑ i ∈ S, f i t v * planeWave (κ i) x) ∧
        HasSepRankLE (fun x v => f0 v + F t x v) S.card := by
  classical
  intro t ht
  have hvan := unexcited_modes_vanish hsol hμ hS hf0 hB0 hE0
  have hsum : ∀ x v, F t x v = ∑ i ∈ S, f i t v * planeWave (κ i) x := fun x v =>
    (hF t x v).unique (hasSum_sum_of_ne_finset_zero fun i hi => by
      rw [(hvan i hi t ht).1 v, zero_mul])
  refine ⟨hsum, hasSepRankLE_of_sum (hS i₀ hi₀) (fun i x => planeWave (κ i) x)
    (fun x => by simp [planeWave, hi₀]) (fun i v => f i t v) f0 fun x v => by rw [hsum]⟩

/-- A partial derivative `∂ₐ u`, of a complex function on `ℝ³`. -/
noncomputable def partialD (a : Fin 3) (u : (Fin 3 → ℝ) → ℂ) (x : Fin 3 → ℝ) : ℂ :=
  lineDeriv ℝ u x (Pi.single a 1)

/-- The curl `∇ × u` of a complex vector field on `ℝ³`. -/
noncomputable def curlC (u : (Fin 3 → ℝ) → Fin 3 → ℂ) (x : Fin 3 → ℝ) : Fin 3 → ℂ :=
  ![partialD 1 (fun y => u y 2) x - partialD 2 (fun y => u y 1) x,
    partialD 2 (fun y => u y 0) x - partialD 0 (fun y => u y 2) x,
    partialD 0 (fun y => u y 1) x - partialD 1 (fun y => u y 0) x]

private theorem hasDerivAt_planeWave (k x : Fin 3 → ℝ) (a : Fin 3) :
    HasDerivAt (fun r : ℝ => planeWave k (x + r • Pi.single a 1))
      (I * k a * planeWave k x) 0 := by
  have h1 : ∀ r : ℝ, planeWave k (x + r • Pi.single a 1) =
      planeWave k x * Complex.exp (I * (k a : ℝ) * r) := by
    intro r
    rw [planeWave, planeWave, ← Complex.exp_add]
    congr 1
    simp only [dotProduct_add, dotProduct_smul, dotProduct_single, smul_eq_mul, mul_one]
    push_cast
    ring
  have h2 := (hasDerivAt_phase (k a) 0).const_mul (planeWave k x)
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at h2
  have h3 : (fun r : ℝ => planeWave k (x + r • Pi.single a 1)) =
      fun r : ℝ => planeWave k x * Complex.exp (I * (k a : ℝ) * r) := funext h1
  rw [h3]
  exact h2.congr_deriv (by ring)

private theorem partialD_sum_planeWave {ι : Type*} (S : Finset ι) (κ : ι → Fin 3 → ℝ)
    (c : ι → ℂ) (a : Fin 3) (x : Fin 3 → ℝ) :
    partialD a (fun y => ∑ i ∈ S, c i * planeWave (κ i) y) x =
      ∑ i ∈ S, I * κ i a * c i * planeWave (κ i) x := by
  have h : HasDerivAt (fun r : ℝ => ∑ i ∈ S, c i * planeWave (κ i) (x + r • Pi.single a 1))
      (∑ i ∈ S, c i * (I * κ i a * planeWave (κ i) x)) 0 :=
    HasDerivAt.fun_sum fun i _ => (hasDerivAt_planeWave (κ i) x a).const_mul (c i)
  have h1 : partialD a (fun y => ∑ i ∈ S, c i * planeWave (κ i) y) x =
      ∑ i ∈ S, c i * (I * κ i a * planeWave (κ i) x) := h.deriv
  rw [h1]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem curlC_sum_planeWave {ι : Type*} (S : Finset ι) (κ : ι → Fin 3 → ℝ)
    (c : ι → Fin 3 → ℂ) (x : Fin 3 → ℝ) :
    curlC (fun y => ∑ i ∈ S, planeWave (κ i) y • c i) x =
      ∑ i ∈ S, planeWave (κ i) x • (I • (toC (κ i) ⨯₃ c i)) := by
  have hpd : ∀ a d, partialD a (fun y => ∑ i ∈ S, planeWave (κ i) y * c i d) x =
      ∑ i ∈ S, I * κ i a * c i d * planeWave (κ i) x := fun a d => by
    have h1 : (fun y => ∑ i ∈ S, planeWave (κ i) y * c i d) =
        fun y => ∑ i ∈ S, c i d * planeWave (κ i) y := by
      funext y
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [h1]
    exact partialD_sum_planeWave S κ (fun i => c i d) a x
  funext b
  simp only [curlC, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hpd, cross_apply, toC]
  fin_cases b <;>
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.zero_eta,
        Fin.mk_one, Fin.reduceFinMk, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring

/-- **The modes solve the linearized equations in physical space** (arXiv 1902.00424, Sec. 3).  If
`(f i, E i, B i)` solve (6)-(8) and `0` is the wave vector of exactly one index of the finite set
`S`, then `f¹ = ∑_{i ∈ S} f̂_i e^{i κ_i x}`, `E¹ = ∑ Ê_i e^{i κ_i x}`, `B¹ = ∑ B̂_i e^{i κ_i x}`
solve

    ∂ₜ f¹ + v · ∇ₓ f¹ - (E¹ + v × B¹) · ∇ᵥ f⁰ = 0,
    ∂ₜ E¹ = ∇ × B¹ - j⁰ - ∫ v f¹ dv,
    ∂ₜ B¹ = -∇ × E¹,

for every `x` and `v`.  So (6)-(8) is the Fourier side of the paper's linearized system, and the
sum (9) is a solution of it. -/
theorem solves_linearized_of_modes {ι : Type*} {μ : Measure (Fin 3 → ℝ)}
    {g : (Fin 3 → ℝ) → Fin 3 → ℝ} {j0 : Fin 3 → ℂ} {κ : ι → Fin 3 → ℝ} {T : ℝ}
    {f : ι → ℝ → (Fin 3 → ℝ) → ℂ} {E B : ι → ℝ → Fin 3 → ℂ}
    (hsol : ∀ i, IsModeSolution μ g (if κ i = 0 then j0 else 0) (κ i) T (f i) (E i) (B i))
    {S : Finset ι} {i₀ : ι} (hi₀ : i₀ ∈ S) (hκ₀ : κ i₀ = 0) (huniq : ∀ i ∈ S, κ i = 0 → i = i₀)
    {f1 : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℂ} {E1 B1 : ℝ → (Fin 3 → ℝ) → Fin 3 → ℂ}
    (hf1 : f1 = fun t x v => ∑ i ∈ S, f i t v * planeWave (κ i) x)
    (hE1 : E1 = fun t x => ∑ i ∈ S, planeWave (κ i) x • E i t)
    (hB1 : B1 = fun t x => ∑ i ∈ S, planeWave (κ i) x • B i t) :
    (∀ x v, ODESolution (fun t _ => -∑ a, (v a : ℂ) * partialD a (fun y => f1 t y v) x +
        (E1 t x + toC v ⨯₃ B1 t x) ⬝ᵥ toC (g v)) (fun t => f1 t x v) 0 T) ∧
      (∀ x, ODESolution (fun t _ => curlC (B1 t) x - j0 - ∫ v, f1 t x v • toC v ∂μ)
        (fun t => E1 t x) 0 T) ∧
      (∀ x, ODESolution (fun t _ => -curlC (E1 t) x) (fun t => B1 t x) 0 T) := by
  subst hf1 hE1 hB1
  refine ⟨fun x v => ⟨?_, fun t ht => ?_⟩, fun x => ⟨?_, fun t ht => ?_⟩,
    fun x => ⟨?_, fun t ht => ?_⟩⟩
  · exact continuousOn_finsetSum _ fun i _ =>
      ((hsol i).vlasov v).cont.mul continuousOn_const
  · have h1 := HasDerivWithinAt.fun_sum (u := S) (fun i _ =>
      (((hsol i).vlasov v).deriv t ht).mul_const (planeWave (κ i) x))
    refine h1.congr_deriv ?_
    beta_reduce
    have h2 : ∀ a, partialD a (fun y => ∑ i ∈ S, f i t v * planeWave (κ i) y) x =
        ∑ i ∈ S, I * κ i a * f i t v * planeWave (κ i) x := fun a =>
      partialD_sum_planeWave S κ (fun i => f i t v) a x
    have h3 : -∑ a, (v a : ℂ) * ∑ i ∈ S, I * κ i a * f i t v * planeWave (κ i) x =
        ∑ i ∈ S, -(I * ((v ⬝ᵥ κ i : ℝ) : ℂ)) * f i t v * planeWave (κ i) x := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [dotProduct, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum,
        Finset.sum_mul, neg_mul]
      exact congrArg _ (Finset.sum_congr rfl fun a _ => by ring)
    have h4 : ((∑ i ∈ S, planeWave (κ i) x • E i t) +
        toC v ⨯₃ ∑ i ∈ S, planeWave (κ i) x • B i t) ⬝ᵥ toC (g v) =
        ∑ i ∈ S, (E i t + toC v ⨯₃ B i t) ⬝ᵥ toC (g v) * planeWave (κ i) x := by
      simp only [map_sum, map_smul, add_dotProduct, sum_dotProduct, smul_dotProduct, smul_eq_mul,
        add_mul, Finset.sum_add_distrib]
      exact congrArg₂ _ (Finset.sum_congr rfl fun i _ => mul_comm _ _)
        (Finset.sum_congr rfl fun i _ => mul_comm _ _)
    simp only [h2, h3, h4, add_mul, Finset.sum_add_distrib]
  · exact continuousOn_finsetSum _ fun i _ => (hsol i).ampere.cont.const_smul (planeWave (κ i) x)
  · have h1 := HasDerivWithinAt.fun_sum (u := S) (fun i _ =>
      ((hsol i).ampere.deriv t ht).const_smul (planeWave (κ i) x))
    refine h1.congr_deriv ?_
    beta_reduce
    have ht' : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.le⟩
    have hsrc : ∑ i ∈ S, planeWave (κ i) x • (if κ i = 0 then j0 else 0) = j0 := by
      rw [Finset.sum_eq_single i₀]
      · simp [planeWave, hκ₀]
      · intro i hi hne
        have hk : κ i ≠ 0 := fun h => hne (huniq i hi h)
        simp [hk]
      · exact fun h => (h hi₀).elim
    have hcur : ∫ v, (∑ i ∈ S, f i t v * planeWave (κ i) x) • toC v ∂μ =
        ∑ i ∈ S, planeWave (κ i) x • ∫ v, f i t v • toC v ∂μ := by
      have h2 : ∀ v, (∑ i ∈ S, f i t v * planeWave (κ i) x) • toC v =
          ∑ i ∈ S, planeWave (κ i) x • (f i t v • toC v) := fun v => by
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul, mul_comm]
      simp only [h2]
      have h3 := integral_finsetSum (μ := μ) S
        (f := fun i v => planeWave (κ i) x • (f i t v • toC v))
        fun i _ => ((hsol i).integrable t ht').smul (planeWave (κ i) x)
      rw [h3]
      exact Finset.sum_congr rfl fun i _ => integral_smul _ _
    rw [curlC_sum_planeWave, hcur]
    simp only [smul_sub, Finset.sum_sub_distrib, hsrc]
  · exact continuousOn_finsetSum _ fun i _ => (hsol i).faraday.cont.const_smul (planeWave (κ i) x)
  · have h1 := HasDerivWithinAt.fun_sum (u := S) (fun i _ =>
      ((hsol i).faraday.deriv t ht).const_smul (planeWave (κ i) x))
    refine h1.congr_deriv ?_
    beta_reduce
    rw [curlC_sum_planeWave]
    simp only [smul_neg, Finset.sum_neg_distrib]

/-- Auxiliary for arXiv 1902.00424, Sec. 3.  Non-vacuity of `IsModeSolution`: free streaming `f̂(t,
v) = e^{-i (v · k) t} h(v)` with `Ê = 0`, `B̂ = 0` is a nonzero solution of (6)-(8), for a velocity
measure concentrated at `v = 0`, where the current vanishes, and any `∇ᵥ f⁰`, any `k` and any `h`.
The moment bound holds as well. -/
theorem exists_isModeSolution (g : (Fin 3 → ℝ) → Fin 3 → ℝ) (k : Fin 3 → ℝ) (T : ℝ)
    (h : (Fin 3 → ℝ) → ℂ) :
    Integrable (fun v => (1 + ‖v‖) ^ 2 * ‖g v‖) (Measure.dirac (0 : Fin 3 → ℝ)) ∧
    IsModeSolution (Measure.dirac 0) g 0 k T
      (fun t v => Complex.exp (I * (-(v ⬝ᵥ k) : ℝ) * t) * h v) (fun _ => 0) (fun _ => 0) := by
  refine ⟨integrable_dirac (by simp), ?_⟩
  have hzero : ∀ t : ℝ,
      ∫ v, (Complex.exp (I * (-(v ⬝ᵥ k) : ℝ) * t) * h v) • toC v ∂(Measure.dirac 0) = 0 :=
    fun t => by
      rw [integral_dirac]
      have h0 : toC 0 = 0 := by
        funext a
        simp [toC]
      rw [h0, smul_zero]
  refine ⟨fun v => ⟨?_, fun t _ => ?_⟩, ⟨continuousOn_const, fun t _ => ?_⟩,
    ⟨continuousOn_const, fun t _ => ?_⟩, fun t _ => integrable_dirac (by simp)⟩
  · exact (continuous_iff_continuousAt.2 fun r =>
      ((hasDerivAt_phase (-(v ⬝ᵥ k)) r).mul_const (h v)).continuousAt).continuousOn
  · have h1 := ((hasDerivAt_phase (-(v ⬝ᵥ k)) t).mul_const (h v)).hasDerivWithinAt (s := Ici t)
    refine h1.congr_deriv ?_
    simp only [map_zero, add_zero, zero_dotProduct, Complex.ofReal_neg]
    ring
  · rw [hzero]
    simpa using hasDerivWithinAt_const t (Ici t) (0 : Fin 3 → ℂ)
  · simpa using hasDerivWithinAt_const t (Ici t) (0 : Fin 3 → ℂ)

end LinearRegime

/-! ### The projector-splitting substeps -/

section Substeps

open scoped LeanDLRA.Frobenius

variable {m n p r : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype r]

/-- A phase-space discretization: difference matrices `Dx`, `Dv` in `x` and `v`, which may be
spectral or of finite differences, and the velocity nodes `vel`.  A grid function `f` is a matrix
with rows `x` and columns `v`.  Quadrature weights are absorbed in the grid functions, so that the
`L²` inner products of the paper are Euclidean. -/
structure PhaseGrid (m n : Type*) where
  Dx : Fin 3 → Matrix m m ℝ
  Dv : Fin 3 → Matrix n n ℝ
  vel : n → Fin 3 → ℝ

/-- The coefficients `d¹[F]`, `d³[F]` of arXiv 1902.00424: `∫ Xᵢ F Xₖ dx`. -/
def dF (X : Matrix m p ℝ) (F : VectorField m) (a : Fin 3) (i k : p) : ℝ :=
  ∑ x, X x i * F a x * X x k

namespace PhaseGrid

variable (g : PhaseGrid m n)

/-- The matrix of `f ↦ (∇ᵥ f × v)ₐ`, acting on `f` from the right. -/
def crossMat (a : Fin 3) : Matrix n n ℝ :=
  Matrix.of fun u w => ((fun b => g.Dv b w u) ⨯₃ g.vel w) a

/-- The discrete Vlasov operator `f ↦ v · ∇̃ₓ f - (E + v × B) · ∇̃ᵥ f` of (12)-(14), with frozen
fields `E`, `B`. -/
def vlasov (E B : VectorField m) (f : Matrix m n ℝ) : Matrix m n ℝ :=
  Matrix.of fun x w => ∑ a, g.vel w a * (g.Dx a * f) x w -
    ∑ a, (E a x + (g.vel w ⨯₃ fun b => B b x) a) * (f * (g.Dv a)ᵀ) x w

/-- The coefficient `c¹_jl = ∫ v V_j V_l dv`, component `a`. -/
def c1 (V : Matrix n r ℝ) (a : Fin 3) (j l : r) : ℝ := ∑ w, g.vel w a * V w j * V w l

/-- The coefficient `c²_jl = ∫ V_j ∇ᵥ V_l dv`, component `a`. -/
def c2 (V : Matrix n r ℝ) (a : Fin 3) (j l : r) : ℝ := ∑ w, V w j * (g.Dv a * V) w l

/-- The coefficient `c³_jl = ∫ V_j (∇ᵥ V_l × v) dv`, component `a`. -/
def c3 (V : Matrix n r ℝ) (a : Fin 3) (j l : r) : ℝ :=
  ∑ w, V w j * ((fun b => (g.Dv b * V) w l) ⨯₃ g.vel w) a

/-- The coefficient `d²_ik = ∫ X_i ∇ₓ X_k dx`, component `a`. -/
def d2 (X : Matrix m p ℝ) (a : Fin 3) (i k : p) : ℝ := ∑ x, X x i * (g.Dx a * X) x k

/-- The right-hand side of the K-step equation (15). -/
def kRhs (V : Matrix n r ℝ) (E B : VectorField m) (K : Matrix m r ℝ) : Matrix m r ℝ :=
  Matrix.of fun x j => -∑ l, ∑ a, g.c1 V a j l * (g.Dx a * K) x l +
    ∑ l, ∑ a, g.c2 V a j l * E a x * K x l + ∑ l, ∑ a, g.c3 V a j l * B a x * K x l

/-- The right-hand side of the S-step equation (16), with the index of `d³` corrected:
`d³_ik`, where the paper prints `d³_kl` (`sRhsPrinted`). -/
def sRhs (X : Matrix m p ℝ) (V : Matrix n r ℝ) (E B : VectorField m) (S : Matrix p r ℝ) :
    Matrix p r ℝ :=
  Matrix.of fun i j => ∑ k, ∑ l, (∑ a, (g.c1 V a j l * g.d2 X a i k -
    g.c2 V a j l * dF X E a i k - g.c3 V a j l * dF X B a i k)) * S k l

/-- The right-hand side of the S-step equation (16) as printed in the paper, with `d³_kl`. -/
def sRhsPrinted (X : Matrix m p ℝ) (V : Matrix n p ℝ) (E B : VectorField m) (S : Matrix p p ℝ) :
    Matrix p p ℝ :=
  Matrix.of fun i j => ∑ k, ∑ l, (∑ a, (g.c1 V a j l * g.d2 X a i k -
    g.c2 V a j l * dF X E a i k - g.c3 V a j l * dF X B a k l)) * S k l

/-- The right-hand side of the L-step equation (17). -/
def lRhs (X : Matrix m p ℝ) (E B : VectorField m) (L : Matrix p n ℝ) : Matrix p n ℝ :=
  Matrix.of fun i w => -∑ k, ∑ a, g.d2 X a i k * g.vel w a * L k w +
    ∑ k, ∑ a, dF X E a i k * (L * (g.Dv a)ᵀ) k w +
    ∑ k, ∑ a, dF X B a i k * ((fun b => (L * (g.Dv b)ᵀ) k w) ⨯₃ g.vel w) a

/-- Auxiliary for arXiv 1902.00424, Sec. 4. -/
theorem mul_crossMat {k : Type*} (f : Matrix k n ℝ) (a : Fin 3) (x : k) (w : n) :
    (f * g.crossMat a) x w = ((fun b => (f * (g.Dv b)ᵀ) x w) ⨯₃ g.vel w) a := by
  simp only [Matrix.mul_apply, crossMat, of_apply, transpose_apply, cross_apply]
  fin_cases a <;>
    · simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul,
        mul_assoc]

variable [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq r]

/-- Auxiliary for arXiv 1902.00424, Sec. 4.  The Vlasov operator is a sum of sandwiches `A f C`. -/
theorem vlasov_eq (E B : VectorField m) (f : Matrix m n ℝ) :
    g.vlasov E B f = ∑ a, g.Dx a * f * Matrix.diagonal (fun w => g.vel w a) -
      ∑ a, Matrix.diagonal (E a) * f * (g.Dv a)ᵀ -
      ∑ a, Matrix.diagonal (B a) * f * g.crossMat a := by
  ext x w
  have h1 : ∀ a, (g.Dx a * f * Matrix.diagonal fun w => g.vel w a) x w =
      g.vel w a * (g.Dx a * f) x w := fun a => by
    rw [Matrix.mul_diagonal, mul_comm]
  have h2 : ∀ (c : m → ℝ) (C : Matrix n n ℝ),
      (Matrix.diagonal c * f * C) x w = c x * (f * C) x w :=
    fun c C => by rw [Matrix.mul_assoc, Matrix.diagonal_mul]
  have h3 : ∑ a, (g.vel w ⨯₃ fun b => B b x) a * (f * (g.Dv a)ᵀ) x w =
      ∑ a, B a x * ((fun b => (f * (g.Dv b)ᵀ) x w) ⨯₃ g.vel w) a := by
    simp only [Fin.sum_univ_three, cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val]
    ring
  simp only [vlasov, of_apply, Matrix.sub_apply, Matrix.sum_apply, h1, h2, mul_crossMat,
    add_mul, Finset.sum_add_distrib]
  rw [h3]
  ring

/-- Auxiliary for arXiv 1902.00424, Sec. 4. -/
theorem c1_eq (V : Matrix n r ℝ) (a : Fin 3) (j l : r) :
    g.c1 V a j l = (Vᵀ * Matrix.diagonal (fun w => g.vel w a) * V) l j := by
  rw [c1, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Matrix.mul_diagonal, transpose_apply]
  ring

/-- Auxiliary for arXiv 1902.00424, Sec. 4. -/
theorem c2_eq (V : Matrix n r ℝ) (a : Fin 3) (j l : r) :
    g.c2 V a j l = (Vᵀ * (g.Dv a)ᵀ * V) l j := by
  rw [← transpose_mul, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun w _ => by rw [transpose_apply, mul_comm]

/-- Auxiliary for arXiv 1902.00424, Sec. 4. -/
theorem c3_eq (V : Matrix n r ℝ) (a : Fin 3) (j l : r) :
    g.c3 V a j l = (Vᵀ * g.crossMat a * V) l j := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [mul_crossMat, mul_comm]
  simp only [← transpose_mul, transpose_apply]

/-- Auxiliary for arXiv 1902.00424, Sec. 4. -/
theorem d2_eq (X : Matrix m p ℝ) (a : Fin 3) (i k : p) :
    g.d2 X a i k = (Xᵀ * g.Dx a * X) i k := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  rfl

end PhaseGrid

/-- Auxiliary for arXiv 1902.00424, Sec. 4. -/
theorem dF_eq [DecidableEq m] (X : Matrix m p ℝ) (F : VectorField m) (a : Fin 3) (i k : p) :
    dF X F a i k = (Xᵀ * Matrix.diagonal (F a) * X) i k := by
  rw [dF, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.mul_diagonal, transpose_apply]

namespace PhaseGrid

variable (g : PhaseGrid m n) [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq r]

/-- **K-step, (12) ⇒ (15)** (arXiv 1902.00424, Sec. 4).  With `f = K Vᵀ` the projected equation
`∂ₜ f = -P_V̄ (v · ∇ₓ f - (E + v × B) · ∇ᵥ f)` is `∂ₜ K = -(v · ∇ₓ f - …) V`, and its right-hand
side is that of (15), in the coefficients `c¹`, `c²`, `c³`, at grid level and for any difference
matrices.  The rewriting `(v × B) · ∇ᵥ V = (∇ᵥ V × v) · B` is proved in `vlasov_eq`. -/
theorem kStep_reduction (V : Matrix n r ℝ) (E B : VectorField m) (K : Matrix m r ℝ) :
    -(g.vlasov E B (K * Vᵀ)) * V = g.kRhs V E B K := by
  ext x j
  have t1 : ∀ a, (g.Dx a * (K * Vᵀ) * Matrix.diagonal (fun w => g.vel w a) * V) x j =
      ∑ l, g.c1 V a j l * (g.Dx a * K) x l := fun a => by
    have h : g.Dx a * (K * Vᵀ) * Matrix.diagonal (fun w => g.vel w a) * V =
        (g.Dx a * K) * (Vᵀ * Matrix.diagonal (fun w => g.vel w a) * V) := by
      simp only [Matrix.mul_assoc]
    rw [h, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => by rw [g.c1_eq, mul_comm]
  have t2 : ∀ a, (Matrix.diagonal (E a) * (K * Vᵀ) * (g.Dv a)ᵀ * V) x j =
      ∑ l, g.c2 V a j l * E a x * K x l := fun a => by
    have h : Matrix.diagonal (E a) * (K * Vᵀ) * (g.Dv a)ᵀ * V =
        (Matrix.diagonal (E a) * K) * (Vᵀ * (g.Dv a)ᵀ * V) := by
      simp only [Matrix.mul_assoc]
    rw [h, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [g.c2_eq, Matrix.diagonal_mul]
    ring
  have t3 : ∀ a, (Matrix.diagonal (B a) * (K * Vᵀ) * g.crossMat a * V) x j =
      ∑ l, g.c3 V a j l * B a x * K x l := fun a => by
    have h : Matrix.diagonal (B a) * (K * Vᵀ) * g.crossMat a * V =
        (Matrix.diagonal (B a) * K) * (Vᵀ * g.crossMat a * V) := by
      simp only [Matrix.mul_assoc]
    rw [h, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [g.c3_eq, Matrix.diagonal_mul]
    ring
  rw [vlasov_eq]
  simp only [Matrix.neg_mul, Matrix.sub_mul, Matrix.sum_mul, Matrix.neg_apply, Matrix.sub_apply,
    Matrix.sum_apply, t1, t2, t3, kRhs, of_apply]
  rw [Finset.sum_comm (f := fun a l => g.c1 V a j l * (g.Dx a * K) x l),
    Finset.sum_comm (f := fun a l => g.c2 V a j l * E a x * K x l),
    Finset.sum_comm (f := fun a l => g.c3 V a j l * B a x * K x l)]
  ring

/-- **S-step, (13) ⇒ (16)** (arXiv 1902.00424, Sec. 4).  With `f = X S Vᵀ`, the equation
`∂ₜ f = P_V̄ P_X̄ (v · ∇ₓ f - (E + v × B) · ∇ᵥ f)` is `∂ₜ S = Xᵀ (v · ∇ₓ f - …) V`, whose right-hand
side is (16) with `d³_ik`.  The paper prints `d³_kl`: see `sStep_printed_false`. -/
theorem sStep_reduction (X : Matrix m p ℝ) (V : Matrix n r ℝ) (E B : VectorField m)
    (S : Matrix p r ℝ) :
    Xᵀ * g.vlasov E B (X * S * Vᵀ) * V = g.sRhs X V E B S := by
  ext i j
  have triple : ∀ (P : Matrix p p ℝ) (Q : Matrix r r ℝ),
      (P * S * Q) i j = ∑ k, ∑ l, Q l j * P i k * S k l := fun P Q => by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have t1 : ∀ a,
      (Xᵀ * (g.Dx a * (X * S * Vᵀ) * Matrix.diagonal (fun w => g.vel w a)) * V) i j =
      ∑ k, ∑ l, g.c1 V a j l * g.d2 X a i k * S k l := fun a => by
    have h : Xᵀ * (g.Dx a * (X * S * Vᵀ) * Matrix.diagonal (fun w => g.vel w a)) * V =
        (Xᵀ * g.Dx a * X) * S * (Vᵀ * Matrix.diagonal (fun w => g.vel w a) * V) := by
      simp only [Matrix.mul_assoc]
    rw [h, triple]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
      rw [g.c1_eq, g.d2_eq]
  have t2 : ∀ a, (Xᵀ * (Matrix.diagonal (E a) * (X * S * Vᵀ) * (g.Dv a)ᵀ) * V) i j =
      ∑ k, ∑ l, g.c2 V a j l * dF X E a i k * S k l := fun a => by
    have h : Xᵀ * (Matrix.diagonal (E a) * (X * S * Vᵀ) * (g.Dv a)ᵀ) * V =
        (Xᵀ * Matrix.diagonal (E a) * X) * S * (Vᵀ * (g.Dv a)ᵀ * V) := by
      simp only [Matrix.mul_assoc]
    rw [h, triple]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
      rw [g.c2_eq, dF_eq]
  have t3 : ∀ a, (Xᵀ * (Matrix.diagonal (B a) * (X * S * Vᵀ) * g.crossMat a) * V) i j =
      ∑ k, ∑ l, g.c3 V a j l * dF X B a i k * S k l := fun a => by
    have h : Xᵀ * (Matrix.diagonal (B a) * (X * S * Vᵀ) * g.crossMat a) * V =
        (Xᵀ * Matrix.diagonal (B a) * X) * S * (Vᵀ * g.crossMat a * V) := by
      simp only [Matrix.mul_assoc]
    rw [h, triple]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
      rw [g.c3_eq, dF_eq]
  rw [vlasov_eq]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.sub_apply,
    Matrix.sum_apply, t1, t2, t3, sRhs, of_apply]
  simp only [Finset.sum_mul, sub_mul, Finset.sum_sub_distrib]
  have hswap : ∀ h : Fin 3 → p → r → ℝ, ∑ a, ∑ k, ∑ l, h a k l = ∑ k, ∑ l, ∑ a, h a k l := by
    intro h
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_comm
  rw [hswap, hswap, hswap]

/-- **L-step, (14) ⇒ (17)** (arXiv 1902.00424, Sec. 4).  With `f = X L` the projected equation
`∂ₜ f = -P_X̄ (v · ∇ₓ f - (E + v × B) · ∇ᵥ f)` is `∂ₜ L = -Xᵀ (v · ∇ₓ f - …)`, and its right-hand
side is that of (17). -/
theorem lStep_reduction (X : Matrix m p ℝ) (E B : VectorField m) (L : Matrix p n ℝ) :
    -(Xᵀ * g.vlasov E B (X * L)) = g.lRhs X E B L := by
  ext i w
  have t1 : ∀ a, (Xᵀ * (g.Dx a * (X * L) * Matrix.diagonal fun w => g.vel w a)) i w =
      ∑ k, g.d2 X a i k * g.vel w a * L k w := fun a => by
    have h : Xᵀ * (g.Dx a * (X * L) * Matrix.diagonal fun w => g.vel w a) =
        ((Xᵀ * g.Dx a * X) * L) * Matrix.diagonal fun w => g.vel w a := by
      simp only [Matrix.mul_assoc]
    rw [h, Matrix.mul_diagonal, Matrix.mul_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by rw [g.d2_eq]; ring
  have t2 : ∀ a, (Xᵀ * (Matrix.diagonal (E a) * (X * L) * (g.Dv a)ᵀ)) i w =
      ∑ k, dF X E a i k * (L * (g.Dv a)ᵀ) k w := fun a => by
    have h : Xᵀ * (Matrix.diagonal (E a) * (X * L) * (g.Dv a)ᵀ) =
        (Xᵀ * Matrix.diagonal (E a) * X) * (L * (g.Dv a)ᵀ) := by
      simp only [Matrix.mul_assoc]
    rw [h, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [dF_eq]
  have t3 : ∀ a, (Xᵀ * (Matrix.diagonal (B a) * (X * L) * g.crossMat a)) i w =
      ∑ k, dF X B a i k * ((fun b => (L * (g.Dv b)ᵀ) k w) ⨯₃ g.vel w) a := fun a => by
    have h : Xᵀ * (Matrix.diagonal (B a) * (X * L) * g.crossMat a) =
        (Xᵀ * Matrix.diagonal (B a) * X) * (L * g.crossMat a) := by
      simp only [Matrix.mul_assoc]
    rw [h, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [dF_eq, mul_crossMat]
  rw [vlasov_eq]
  simp only [Matrix.mul_sub, Matrix.mul_sum, Matrix.neg_apply, Matrix.sub_apply, Matrix.sum_apply,
    t1, t2, t3, lRhs, of_apply]
  rw [Finset.sum_comm (f := fun a k => g.d2 X a i k * g.vel w a * L k w),
    Finset.sum_comm (f := fun a k => dF X E a i k * (L * (g.Dv a)ᵀ) k w),
    Finset.sum_comm (f := fun a k => dF X B a i k *
      ((fun b => (L * (g.Dv b)ᵀ) k w) ⨯₃ g.vel w) a)]
  ring

end PhaseGrid

/-- **Eq. (16) as printed in arXiv 1902.00424 is false**: the projected S-step `(13)` does not have
the right-hand side with `d³_kl[B]`; `d³_ik[B]` is right (`PhaseGrid.sStep_reduction`).  Here are
explicit data on two grid points, with `X = V = 1`, `E = 0`, `∇̃ₓ = 0`, for which the two disagree.
The printed index is a misprint: (17) has `d³_ik`. -/
theorem sStep_printed_false :
    ∃ (g : PhaseGrid (Fin 2) (Fin 2)) (E B : VectorField (Fin 2))
      (X V S : Matrix (Fin 2) (Fin 2) ℝ), Xᵀ * X = 1 ∧ Vᵀ * V = 1 ∧
        Xᵀ * g.vlasov E B (X * S * Vᵀ) * V ≠ g.sRhsPrinted X V E B S := by
  refine ⟨⟨fun _ => 0, fun a => if a = 0 then 1 else 0, fun _ => ![0, 1, 0]⟩, 0,
    fun a x => if a = 2 ∧ x = 0 then 1 else 0, 1, 1, !![0, 1; 0, 0], by simp, by simp, ?_⟩
  intro h
  rw [PhaseGrid.sStep_reduction] at h
  have h1 := congrFun (congrFun h 0) 1
  simp [PhaseGrid.sRhs, PhaseGrid.sRhsPrinted, PhaseGrid.c1, PhaseGrid.c2, PhaseGrid.c3,
    PhaseGrid.d2, dF, Fin.sum_univ_three, cross_apply, Matrix.one_apply] at h1

/-- An `ODESolution` is transported by a continuous linear map that intertwines the fields. -/
private theorem odeSolution_map {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (Φ : E →L[ℝ] F) {f : ℝ → E → E} {f' : ℝ → F → F}
    {y : ℝ → E} {a b : ℝ} (hy : ODESolution f y a b)
    (h : ∀ t ∈ Ico a b, Φ (f t (y t)) = f' t (Φ (y t))) :
    ODESolution f' (fun t => Φ (y t)) a b :=
  ⟨Φ.continuous.comp_continuousOn hy.cont, fun t ht => by
    rw [← h t ht]
    exact Φ.hasFDerivAt.comp_hasDerivWithinAt t (hy.deriv t ht)⟩

variable [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq r]

/-- **Eq. (11)** of arXiv 1902.00424: the tangent projector of the library, `tangentProj`, is
`P_V̄ - P_V̄ P_X̄ + P_X̄`, so that the three right-hand sides (12), (13), (14) add up to the
projected equation.  That `tangentProj` is the orthogonal projector with the tangent space
as its range is `isOrthProj_tangentProj` and `mem_range_tangentProj`. -/
theorem tangentProj_eq_splitting (U : Matrix m p ℝ) (V : Matrix n r ℝ) (Z : Matrix m n ℝ) :
    tangentProj U V Z = rightProj V Z - leftProj U (rightProj V Z) + leftProj U Z := by
  rw [tangentProj_apply, leftProj_apply, leftProj_apply, rightProj_apply']
  simp only [Matrix.mul_assoc]
  abel

/-- **The reduced equations (15)-(17) are one step of the projector-splitting integrator**
(arXiv 1902.00424, Sec. 4, Lie splitting with frozen fields).  If `K`, `S`, `L` solve (15), (16)
(with `d³_ik`), (17) with the bases and initial values of the paper, then `K V₀ᵀ`, `X₁ S V₀ᵀ`,
`X₁ L` are the substeps of the library's `IsKSLStep` for the field
`F(Y) = -(v · ∇̃ₓ Y - (E + v × B) · ∇̃ᵥ Y)`.  So all abstract KSL results apply to the discrete
Vlasov equation.  The QR factorizations
are the hypotheses `hqr`; the projector (11) is `tangentProj` of `Matrix/Projectors`. -/
theorem isKSLStep_of_reduced (g : PhaseGrid m n) (E B : VectorField m) {V₀ : Matrix n r ℝ}
    {X₁ : Matrix m p ℝ} (hV : V₀ᵀ * V₀ = 1) (hX : X₁ᵀ * X₁ = 1) {K : ℝ → Matrix m r ℝ}
    {S : ℝ → Matrix p r ℝ} {L : ℝ → Matrix p n ℝ} {t₀ t₁ : ℝ} {Y₀ : Matrix m n ℝ}
    (hK : ODESolution (fun _ K => g.kRhs V₀ E B K) K t₀ t₁) (hK₀ : K t₀ * V₀ᵀ = Y₀)
    {S₁ : Matrix p r ℝ} (hqr : K t₁ = X₁ * S₁)
    (hS : ODESolution (fun _ S => g.sRhs X₁ V₀ E B S) S t₀ t₁) (hS₀ : S t₀ = S₁)
    (hL : ODESolution (fun _ L => g.lRhs X₁ E B L) L t₀ t₁) (hL₀ : L t₀ = S t₁ * V₀ᵀ) {ε : ℝ}
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - leftProj X₁) ((1 - rightProj V₀)
      (-g.vlasov E B (K t₁ * V₀ᵀ)))‖ ≤ ε) :
    IsKSLStep (fun _ Y => -g.vlasov E B Y) ε (leftProj X₁) (rightProj V₀) t₀ t₁ Y₀
      (fun t => K t * V₀ᵀ) (fun t => X₁ * S t * V₀ᵀ) (fun t => X₁ * L t) where
  projP₁ := isOrthProj_leftProj hX
  projQ₀ := isOrthProj_rightProj hV
  kSol := by
    refine odeSolution_map (Frobenius.rightMulCLM V₀ᵀ) hK fun t _ => ?_
    rw [Frobenius.rightMulCLM_apply, Frobenius.rightMulCLM_apply, ← g.kStep_reduction,
      rightProj_apply', Matrix.mul_assoc]
  kStart := hK₀
  kCap := by
    change X₁ * X₁ᵀ * (K t₁ * V₀ᵀ) = K t₁ * V₀ᵀ
    rw [hqr, Matrix.mul_assoc X₁ X₁ᵀ, ← Matrix.mul_assoc X₁ᵀ, ← Matrix.mul_assoc X₁ᵀ, hX,
      Matrix.one_mul, Matrix.mul_assoc]
  kNormal := hε
  sSol := by
    let Φ : Matrix p r ℝ →L[ℝ] Matrix m n ℝ :=
      (Frobenius.leftMulCLM X₁).comp (Frobenius.rightMulCLM V₀ᵀ)
    have hΦ : ∀ Z, Φ Z = X₁ * Z * V₀ᵀ := fun Z => (Matrix.mul_assoc _ _ _).symm
    have h1 : ODESolution (fun _ Y => -leftProj X₁ (rightProj V₀ (-g.vlasov E B Y)))
        (fun t => Φ (S t)) t₀ t₁ := odeSolution_map Φ hS fun t _ => by
      rw [hΦ, hΦ, ← g.sStep_reduction, map_neg, map_neg, neg_neg, leftProj_apply,
        rightProj_apply']
      simp only [Matrix.mul_assoc]
    simpa only [hΦ] using h1
  sStart := by
    change X₁ * S t₀ * V₀ᵀ = K t₁ * V₀ᵀ
    rw [hS₀, hqr]
  lSol := by
    refine odeSolution_map (Frobenius.leftMulCLM X₁) hL fun t _ => ?_
    simp only [Frobenius.leftMulCLM_apply, ← g.lStep_reduction]
    rw [map_neg, leftProj_apply, Matrix.mul_neg, Matrix.mul_assoc]
  lStart := by
    change X₁ * L t₀ = X₁ * S t₁ * V₀ᵀ
    rw [hL₀, Matrix.mul_assoc]

end Substeps

/-! ### Exactness of the splitting in the linear regime -/

section Exact

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Auxiliary for arXiv 1902.00424, Sec. 3.  Time reversal of a solution of an autonomous equation.
The solutions of the library have right derivatives; the fundamental theorem of calculus turns them
into two-sided ones. -/
theorem ODESolution.reverse {G : E → E} (hG : Continuous G) {y : ℝ → E} {a b : ℝ}
    (hy : ODESolution (fun _ => G) y a b) (hab : a ≤ b) :
    ODESolution (fun _ x => -G x) (fun t => y (a + b - t)) a b := by
  let w : ℝ → E := Set.IccExtend hab (fun t : Icc a b => G (y t))
  have hw0 : ContinuousOn (fun t => G (y t)) (Icc a b) := hG.comp_continuousOn hy.cont
  have hwc : Continuous w := (continuousOn_iff_continuous_domRestrict.1 hw0).Icc_extend'
  have hweq : ∀ t ∈ Icc a b, w t = G (y t) := fun t ht => IccExtend_of_mem hab _ ht
  let Z : ℝ → E := fun t => y a + ∫ s in a..t, w s
  have hZd : ∀ t, HasDerivAt Z (w t) t := fun t => by
    have h1 := (hwc.integral_hasStrictDerivAt a t).hasDerivAt
    exact h1.const_add (y a)
  have hZc : Continuous Z := continuous_iff_continuousAt.2 fun t => (hZd t).continuousAt
  have hyZ : ∀ t ∈ Icc a b, y t = Z t := by
    have h1 := constant_of_has_deriv_right_zero (f := fun t => y t - Z t)
      (hy.cont.sub hZc.continuousOn) (fun t ht => ?_)
    · intro t ht
      have h2 := h1 t ht
      have h3 : Z a = y a := by simp [Z]
      simp only [h3, sub_self] at h2
      exact sub_eq_zero.1 h2
    · have h2 := (hy.deriv t ht).sub (hZd t).hasDerivWithinAt
      rw [hweq t ⟨ht.1, ht.2.le⟩, sub_self] at h2
      exact h2
  have hmem : ∀ t ∈ Icc a b, a + b - t ∈ Icc a b := fun t ht =>
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  refine ⟨hy.cont.comp (by fun_prop) hmem, fun t ht => ?_⟩
  have ht' : t ∈ Icc a b := ⟨ht.1, ht.2.le⟩
  have h1 : HasDerivAt (fun r => Z (a + b - r)) (-w (a + b - t)) t := by
    have h2 : HasDerivAt (fun r : ℝ => a + b - r) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub (a + b)
    have h3 : HasDerivAt (fun r => Z (a + b - r)) ((-1 : ℝ) • w (a + b - t)) t :=
      (hZd (a + b - t)).scomp t h2
    simpa using h3
  have h4 : HasDerivWithinAt (fun r => Z (a + b - r)) (-G (y (a + b - t))) (Ici t) t := by
    rw [← hweq _ (hmem t ht')]
    exact h1.hasDerivWithinAt
  refine h4.congr_of_eventuallyEq ?_ (hyZ _ (hmem t ht'))
  filter_upwards [Icc_mem_nhdsGE_of_mem ht] with r hr
  exact hyZ _ (hmem r hr)

/-- Auxiliary for arXiv 1902.00424, Sec. 3.  A solution stays in a closed range `P = 1` if the
field maps the range into itself. -/
theorem ODESolution.stays_in_range {f : ℝ → E → E} {L : ℝ} (hf : IsLipschitzField f L)
    {P : E →L[ℝ] E} (hP : IsOrthProj P)
    (hinv : ∀ t x, P x = x → P (f t x) = f t x) {y : ℝ → E} {a b : ℝ}
    (hy : ODESolution f y a b) (h0 : P (y a) = y a) :
    ∀ t ∈ Icc a b, P (y t) = y t := by
  have hPP : ∀ x, P (P x) = P x := fun x => by
    have := congrArg (fun Q : E →L[ℝ] E => Q x) hP.idem'
    simpa using this
  have hd : ∀ t ∈ Ico a b, HasDerivWithinAt (fun r => y r - P (y r))
      (f t (y t) - P (f t (y t))) (Ici t) t := fun t ht =>
    (hy.deriv t ht).sub (P.hasFDerivAt.comp_hasDerivWithinAt t (hy.deriv t ht))
  have hb := norm_le_gronwallBound_of_norm_deriv_right_le (δ := 0) (K := L) (ε := 0)
    (hy.cont.sub (P.continuous.comp_continuousOn hy.cont)) hd (by simp [h0]) (fun t _ => by
      have h1 : f t (y t) - P (f t (y t)) =
          (f t (y t) - f t (P (y t))) - P (f t (y t) - f t (P (y t))) := by
        rw [map_sub, hinv t _ (hPP _)]
        abel
      rw [h1, add_zero]
      exact (hP.norm_sub_le _).trans (hf t _ _))
  intro t ht
  have h2 := hb t ht
  rw [gronwallBound_ε0_δ0, norm_le_zero_iff] at h2
  exact (sub_eq_zero.1 h2).symm

/-- **Exactness of the projector-splitting step on an invariant subspace.**  This is not stated in
arXiv 1902.00424, it is the mechanism behind the observation of Sec. 3 that small ranks suffice in
the linear regime.  Let the field `G` be autonomous, i.e. let the fields be frozen as in Sec. 4, and
let `P₁` commute with `Q₀`.  If the range of the new left projector `P₁` is invariant under `G` and
contains `Y₀`, then one KSL step reproduces the exact solution, for every step size, whatever the
singular values are: the K-step is undone by the S-step, which is its time reversal, and the L-step
is the full equation.  It is not one of the exactness theorems of `Integrators/Exactness`, which
need a `Y`-independent field. -/
theorem ksl_exact_of_invariant {G : E → E} {L ε : ℝ} (hG : IsLipschitzField (fun _ => G) L)
    (hL : 0 ≤ L) {P₁ Q₀ : E →L[ℝ] E} {t₀ t₁ : ℝ} {Y₀ : E} {YK YS YL A : ℝ → E}
    (hs : IsKSLStep (fun _ => G) ε P₁ Q₀ t₀ t₁ Y₀ YK YS YL) (h01 : t₀ ≤ t₁)
    (hc : ∀ x, P₁ (Q₀ x) = Q₀ (P₁ x)) (hinv : ∀ x, P₁ x = x → P₁ (G x) = G x)
    (hY₀ : P₁ Y₀ = Y₀) (hA : ODESolution (fun _ => G) A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    YL t₁ = A t₁ := by
  have hP := hs.projP₁
  have hQ := hs.projQ₀
  have hPP : ∀ x, P₁ (P₁ x) = P₁ x := fun x => by
    have := congrArg (fun R : E →L[ℝ] E => R x) hP.idem'
    simpa using this
  have hGc : Continuous G := (hG.lipschitzWith hL 0).continuous
  have hLQ : IsLipschitzField (fun _ x => Q₀ (G x)) L := hG.comp_contraction Q₀ hQ.norm_le
  have hLP : IsLipschitzField (fun _ x => P₁ (G x)) L := hG.comp_contraction P₁ hP.norm_le
  have hLS : IsLipschitzField (fun _ x => -P₁ (Q₀ (G x))) L :=
    hG.comp_contraction (-(P₁.comp Q₀)) fun x => by
      simpa using (hP.norm_le _).trans (hQ.norm_le _)
  -- the K-step stays in the range of `P₁`
  have hKr := ODESolution.stays_in_range hLQ hP
    (fun _ x hx => by rw [hc, hinv x hx]) hs.kSol (by rw [hs.kStart, hY₀])
  -- the S-step is the time reversal of the K-step
  have hrev : ODESolution (fun _ x => -Q₀ (G x)) (fun t => YK (t₀ + t₁ - t)) t₀ t₁ :=
    ODESolution.reverse (G := fun x => Q₀ (G x)) (Q₀.continuous.comp hGc) hs.kSol h01
  have hmem : ∀ t ∈ Icc t₀ t₁, t₀ + t₁ - t ∈ Icc t₀ t₁ := fun t ht =>
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hS' : ODESolution (fun _ x => -P₁ (Q₀ (G x))) (fun t => YK (t₀ + t₁ - t)) t₀ t₁ :=
    ⟨hrev.cont, fun t ht => by
      have h1 := hrev.deriv t ht
      have hx := hKr _ (hmem t ⟨ht.1, ht.2.le⟩)
      rw [hc, hinv _ hx]
      exact h1⟩
  have hSeq := ODESolution.eqOn hs.sSol hS' hLS hL (by simp [hs.sStart])
  have hS1 : YS t₁ = Y₀ := by
    have h1 := hSeq ⟨h01, le_rfl⟩
    simpa [hs.kStart] using h1
  -- the L-step is the full equation
  have hLr := ODESolution.stays_in_range hLP hP (fun _ x _ => hPP _) hs.lSol
    (by rw [hs.lStart, hS1, hY₀])
  have hL' : ODESolution (fun _ => G) YL t₀ t₁ := ⟨hs.lSol.cont, fun t ht => by
    have h1 := hs.lSol.deriv t ht
    have hx := hLr t ⟨ht.1, ht.2.le⟩
    rw [hinv _ hx] at h1
    exact h1⟩
  exact hL'.eqOn hA hG hL (by rw [hs.lStart, hS1, hA₀]) ⟨h01, le_rfl⟩

/-- Auxiliary for arXiv 1902.00424, Sec. 3.  Non-vacuity of `ksl_exact_of_invariant`, and `ε = 0`:
under its hypotheses a KSL step and the exact solution exist on every interval, and the normal
component of the step vanishes. -/
theorem exists_isKSLStep_of_invariant {G : E → E} {L : ℝ} (hG : IsLipschitzField (fun _ => G) L)
    (hL : 0 ≤ L) {P₁ Q₀ : E →L[ℝ] E} (hP : IsOrthProj P₁) (hQ : IsOrthProj Q₀) {t₀ t₁ : ℝ}
    (h01 : t₀ ≤ t₁) (hc : ∀ x, P₁ (Q₀ x) = Q₀ (P₁ x)) (hinv : ∀ x, P₁ x = x → P₁ (G x) = G x)
    {Y₀ : E} (hY₀ : P₁ Y₀ = Y₀) :
    (∃ YK YS YL, IsKSLStep (fun _ => G) 0 P₁ Q₀ t₀ t₁ Y₀ YK YS YL) ∧
      ∃ A, ODESolution (fun _ => G) A t₀ t₁ ∧ A t₀ = Y₀ := by
  have hGc : Continuous G := (hG.lipschitzWith hL 0).continuous
  have hLQ : IsLipschitzField (fun _ x => Q₀ (G x)) L := hG.comp_contraction Q₀ hQ.norm_le
  have hLP : IsLipschitzField (fun _ x => P₁ (G x)) L := hG.comp_contraction P₁ hP.norm_le
  have hLS : IsLipschitzField (fun _ x => -P₁ (Q₀ (G x))) L :=
    hG.comp_contraction (-(P₁.comp Q₀)) fun x => by
      simpa using (hP.norm_le _).trans (hQ.norm_le _)
  have hex : ∀ (F : ℝ → E → E), IsLipschitzField F L → (∀ t, F t 0 = F 0 0) →
      (∀ x t, F t x = F 0 x) → ∀ y₀, ∃ y, ODESolution F y t₀ t₁ ∧ y t₀ = y₀ := by
    intro F hF h0 hx y₀
    refine exists_ODESolution_of_linearGrowth (K := ‖F 0 0‖) hF hL (fun t _ => by rw [h0])
      (fun x => ?_) h01 y₀
    exact (continuousOn_const (c := F 0 x)).congr fun t _ => hx x t
  obtain ⟨YK, hK, hK₀⟩ := hex (fun _ x => Q₀ (G x)) hLQ (fun _ => rfl) (fun _ _ => rfl) Y₀
  obtain ⟨YS, hS, hS₀⟩ := hex (fun _ x => -P₁ (Q₀ (G x))) hLS (fun _ => rfl) (fun _ _ => rfl)
    (YK t₁)
  obtain ⟨YL, hL', hL₀⟩ := hex (fun _ x => P₁ (G x)) hLP (fun _ => rfl) (fun _ _ => rfl) (YS t₁)
  obtain ⟨A, hA, hA₀⟩ := hex (fun _ => G) hG (fun _ => rfl) (fun _ _ => rfl) Y₀
  have hKr := ODESolution.stays_in_range hLQ hP
    (fun _ x hx => by rw [hc, hinv x hx]) hK (by rw [hK₀, hY₀])
  refine ⟨⟨YK, YS, YL, ⟨hP, hQ, hK, hK₀, hKr t₁ ⟨h01, le_rfl⟩, fun t _ => ?_, hS, hS₀, hL',
    hL₀⟩⟩, A, hA, hA₀⟩
  have hx := hKr t₁ ⟨h01, le_rfl⟩
  have h1 : P₁ (G (YK t₁) - Q₀ (G (YK t₁))) = G (YK t₁) - Q₀ (G (YK t₁)) := by
    rw [map_sub, hc, hinv _ hx]
  simp [h1]

end Exact

/-! ### The linearized field and frozen fields -/

section Fields

open scoped LeanDLRA.Frobenius

variable {m n p r : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype r]
  [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq r]

private theorem norm_sandwich_le (A : Matrix m m ℝ) (f : Matrix m n ℝ) (C : Matrix n n ℝ) :
    ‖A * f * C‖ ≤ ‖A‖ * ‖C‖ * ‖f‖ := by
  calc ‖A * f * C‖ ≤ ‖A * f‖ * ‖C‖ := Frobenius.norm_mul_le _ _
    _ ≤ (‖A‖ * ‖f‖) * ‖C‖ := by
      gcongr
      exact Frobenius.norm_mul_le _ _
    _ = _ := by ring

namespace PhaseGrid

variable (g : PhaseGrid m n)

/-- The source `(E + v × B) · ∇ᵥ f⁰` of the linearized equation, with `gf = ∇ᵥ f⁰`. -/
def source (E B : VectorField m) (gf : n → Fin 3 → ℝ) : Matrix m n ℝ :=
  Matrix.of fun x w => ∑ a, (E a x + (g.vel w ⨯₃ fun b => B b x) a) * gf w a

/-- The field `Y ↦ -v · ∇̃ₓ Y + C` of the linearized Vlasov equation of Sec. 3 of arXiv 1902.00424,
with frozen source `C`. -/
def linearized (C Y : Matrix m n ℝ) : Matrix m n ℝ :=
  -∑ a, g.Dx a * Y * Matrix.diagonal (fun w => g.vel w a) + C

/-- Auxiliary for arXiv 1902.00424, Secs. 3, 4. -/
theorem source_eq (E B : VectorField m) (gf : n → Fin 3 → ℝ) :
    g.source E B gf = ∑ a, Matrix.vecMulVec (E a) (fun w => gf w a) +
      ∑ a, Matrix.vecMulVec (B a) (fun w => (gf w ⨯₃ g.vel w) a) := by
  ext x w
  simp only [source, of_apply, Matrix.add_apply, Matrix.sum_apply, vecMulVec_apply, add_mul,
    Finset.sum_add_distrib]
  congr 1
  simp only [Fin.sum_univ_three, cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  ring

/-- Auxiliary for arXiv 1902.00424, Secs. 3, 4.  If the fields lie in the range of `U`, so does the
source of the linearized equation. This is the statement that only the excited modes occur in `E¹`
and `B¹`. -/
theorem source_mem (E B : VectorField m) (gf : n → Fin 3 → ℝ) {U : Matrix m p ℝ}
    (hE : ∀ a, (U * Uᵀ) *ᵥ E a = E a) (hB : ∀ a, (U * Uᵀ) *ᵥ B a = B a) :
    U * Uᵀ * g.source E B gf = g.source E B gf := by
  rw [source_eq, Matrix.mul_add, Matrix.mul_sum, Matrix.mul_sum]
  simp only [Matrix.mul_vecMulVec, hE, hB]

/-- Auxiliary for arXiv 1902.00424, Secs. 3, 4. -/
theorem isLipschitzField_linearized (C : Matrix m n ℝ) :
    IsLipschitzField (fun _ => g.linearized C)
      (∑ a, ‖g.Dx a‖ * ‖Matrix.diagonal (fun w => g.vel w a)‖) := by
  intro _ Y Z
  have h1 : g.linearized C Y - g.linearized C Z =
      -∑ a, g.Dx a * (Y - Z) * Matrix.diagonal (fun w => g.vel w a) := by
    simp only [linearized, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]
    abel
  rw [h1, norm_neg, Finset.sum_mul]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sandwich_le _ _ _)

/-- Auxiliary for arXiv 1902.00424, Secs. 3, 4.  The range of `U` is invariant for the linearized
field if it is invariant under `∇̃ₓ` and contains the source. -/
theorem leftProj_linearized {C Y : Matrix m n ℝ} {U : Matrix m p ℝ} (hU : Uᵀ * U = 1)
    (hDx : ∀ a, ∃ M : Matrix p p ℝ, g.Dx a * U = U * M) (hC : U * Uᵀ * C = C)
    (hY : U * Uᵀ * Y = Y) : U * Uᵀ * g.linearized C Y = g.linearized C Y := by
  have h1 : ∀ a, U * Uᵀ * (g.Dx a * Y * Matrix.diagonal (fun w => g.vel w a)) =
      g.Dx a * Y * Matrix.diagonal (fun w => g.vel w a) := by
    intro a
    obtain ⟨M, hM⟩ := hDx a
    have h2 : g.Dx a * Y = U * (M * (Uᵀ * Y)) := by
      conv_lhs => rw [← hY, Matrix.mul_assoc, ← Matrix.mul_assoc, hM]
      simp only [Matrix.mul_assoc]
    have h3 : U * Uᵀ * (U * (M * (Uᵀ * Y))) = U * (M * (Uᵀ * Y)) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul]
    rw [h2, ← Matrix.mul_assoc, h3]
  rw [linearized, Matrix.mul_add, Matrix.mul_neg, Matrix.mul_sum, hC]
  simp only [h1]

end PhaseGrid

/-- **Exactness of the splitting for the linearized equation** (cf. arXiv 1902.00424, Sec. 3, which
states the low-rank structure of the solution, not this).  Let the columns of `U` span a subspace
of grid functions in `x` that is invariant under `∇̃ₓ`, such as the span of the excited Fourier
modes, and that contains the frozen source, and let `Y₀` have its columns in it.  If the new left
basis of a KSL step is `U`, the step reproduces the exact solution of the linearized equation, for
every `τ`.  So the integrator of Sec. 4 is exact for ranks `r ≥ m + 1`, when `U` is the mode basis.
The number of columns of `V₀` is arbitrary. -/
theorem linearized_ksl_exact (g : PhaseGrid m n) {C : Matrix m n ℝ} {U : Matrix m p ℝ}
    (hU : Uᵀ * U = 1) (hDx : ∀ a, ∃ M : Matrix p p ℝ, g.Dx a * U = U * M) (hC : U * Uᵀ * C = C)
    {V₀ : Matrix n r ℝ} {ε t₀ t₁ : ℝ} {Y₀ : Matrix m n ℝ} {YK YS YL A : ℝ → Matrix m n ℝ}
    (hs : IsKSLStep (fun _ => g.linearized C) ε (leftProj U) (rightProj V₀) t₀ t₁ Y₀ YK YS YL)
    (h01 : t₀ ≤ t₁) (hY₀ : U * Uᵀ * Y₀ = Y₀)
    (hA : ODESolution (fun _ => g.linearized C) A t₀ t₁) (hA₀ : A t₀ = Y₀) : YL t₁ = A t₁ := by
  have hL : (0 : ℝ) ≤ ∑ a, ‖g.Dx a‖ * ‖Matrix.diagonal (fun w => g.vel w a)‖ :=
    Finset.sum_nonneg fun _ _ => by positivity
  exact ksl_exact_of_invariant (g.isLipschitzField_linearized C) hL hs h01
    (fun x => leftProj_rightProj_comm U V₀ x)
    (fun x hx => g.leftProj_linearized hU hDx hC hx) hY₀ hA hA₀

namespace PhaseGrid

variable (g : PhaseGrid m n)

/-- A Lipschitz constant of the frozen Vlasov field. -/
noncomputable def lipConst (E B : VectorField m) : ℝ :=
  ∑ a, ‖g.Dx a‖ * ‖Matrix.diagonal (fun w => g.vel w a)‖ +
    ∑ a, ‖Matrix.diagonal (E a)‖ * ‖(g.Dv a)ᵀ‖ + ∑ a, ‖Matrix.diagonal (B a)‖ * ‖g.crossMat a‖

/-- Auxiliary for arXiv 1902.00424, Secs. 3, 4. -/
theorem lipConst_nonneg (E B : VectorField m) : 0 ≤ g.lipConst E B := by
  simp only [lipConst]
  positivity

/-- Auxiliary for arXiv 1902.00424, Secs. 3, 4. -/
theorem norm_vlasov_le (E B : VectorField m) (f : Matrix m n ℝ) :
    ‖g.vlasov E B f‖ ≤ g.lipConst E B * ‖f‖ := by
  rw [vlasov_eq, lipConst, add_mul, add_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) ?_)
  all_goals exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sandwich_le _ _ _)

/-- Auxiliary for arXiv 1902.00424, Secs. 3, 4. -/
theorem vlasov_sub (E B : VectorField m) (f h : Matrix m n ℝ) :
    g.vlasov E B (f - h) = g.vlasov E B f - g.vlasov E B h := by
  simp only [vlasov_eq, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]
  abel

/-- Auxiliary for arXiv 1902.00424, Secs. 3, 4. -/
theorem isLipschitzField_vlasov (E B : VectorField m) :
    IsLipschitzField (fun _ Y => -g.vlasov E B Y) (g.lipConst E B) := fun _ Y Z => by
  have h1 : -g.vlasov E B Y - -g.vlasov E B Z = -g.vlasov E B (Y - Z) := by
    rw [vlasov_sub]
    abel
  rw [h1, norm_neg]
  exact g.norm_vlasov_le E B _

/-- **The frozen-field defect** (arXiv 1902.00424, Sec. 4, where (15)-(17) are solved with the
fields at the beginning of the step): the defect is linear in the change of the fields. -/
theorem norm_vlasov_sub_vlasov_le (E B E' B' : VectorField m) (f : Matrix m n ℝ) :
    ‖g.vlasov E B f - g.vlasov E' B' f‖ ≤
      (∑ a, ‖Matrix.diagonal (E a - E' a)‖ * ‖(g.Dv a)ᵀ‖ +
        ∑ a, ‖Matrix.diagonal (B a - B' a)‖ * ‖g.crossMat a‖) * ‖f‖ := by
  have h1 : g.vlasov E B f - g.vlasov E' B' f =
      -∑ a, Matrix.diagonal (E a - E' a) * f * (g.Dv a)ᵀ -
        ∑ a, Matrix.diagonal (B a - B' a) * f * g.crossMat a := by
    have hd : ∀ u v : m → ℝ, Matrix.diagonal (u - v) = Matrix.diagonal u - Matrix.diagonal v :=
      fun u v => by
        ext i j
        by_cases h : i = j <;> simp [h]
    simp only [vlasov_eq, hd, Matrix.sub_mul, Finset.sum_sub_distrib]
    abel
  rw [h1, add_mul, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_neg]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sandwich_le _ _ _)
  · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sandwich_le _ _ _)

/-- Auxiliary for arXiv 1902.00424, Secs. 3, 4.  A bound of the frozen Vlasov field on a tube
around a bounded curve. -/
theorem isBoundedOnTube_vlasov (E B : VectorField m) {A : ℝ → Matrix m n ℝ} {a b ρ M : ℝ}
    (hM : ∀ t ∈ Icc a b, ‖A t‖ ≤ M) :
    IsBoundedOnTube (fun _ Y => -g.vlasov E B Y) A a b ρ (g.lipConst E B * (M + ρ)) := by
  intro t ht x hx
  rw [norm_neg]
  refine (g.norm_vlasov_le E B x).trans (mul_le_mul_of_nonneg_left ?_ (g.lipConst_nonneg E B))
  have h1 := norm_sub_norm_le x (A t)
  linarith [hM t ht]

end PhaseGrid

/-- **Local error of the Lie splitting of Sec. 4 with frozen fields** (arXiv 1902.00424, Sec. 4).
The step uses `E`, `B` at the beginning of the step, as the paper's numerical scheme does, whereas
the exact solution `A` sees the fields `E t`, `B t`.  If `Af` is the exact solution with frozen
fields, `‖Af‖ ≤ M`, the defect is bounded by `η` along `A` and the step is small, then the error is
the robust KSL error plus the effect of the defect:

    ‖YL t₁ - A t₁‖ ≤ h (11 Λ B h + ε) + gronwallBound 0 Λ η h,

with `Λ = lipConst` and `B = Λ (M + ρ)`.  For fields that are Lipschitz in time, `η = O(h)` by
`norm_vlasov_sub_vlasov_le`, and the frozen-field contribution is `O(h²)`.  The Vlasov field is not
bounded, so this goes through `ksl_local_error_of_tube`. -/
theorem frozen_ksl_local_error (g : PhaseGrid m n) {E B : ℝ → VectorField m} {t₀ t₁ h ε ρ M η : ℝ}
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) {P₁ Q₀ : Matrix m n ℝ →L[ℝ] Matrix m n ℝ}
    {Y₀ : Matrix m n ℝ} {YK YS YL A Af : ℝ → Matrix m n ℝ}
    (hs : IsKSLStep (fun _ Y => -g.vlasov (E t₀) (B t₀) Y) ε P₁ Q₀ t₀ t₁ Y₀ YK YS YL)
    (hA : ODESolution (fun t Y => -g.vlasov (E t) (B t) Y) A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (hAf : ODESolution (fun _ Y => -g.vlasov (E t₀) (B t₀) Y) Af t₀ t₁) (hAf₀ : Af t₀ = Y₀)
    (hM : ∀ t ∈ Icc t₀ t₁, ‖Af t‖ ≤ M) (hM0 : 0 ≤ M) (hρ : 0 ≤ ρ)
    (hη : ∀ t ∈ Ico t₀ t₁, ‖g.vlasov (E t) (B t) (A t) - g.vlasov (E t₀) (B t₀) (A t)‖ ≤ η)
    (hsmall : 4 * (g.lipConst (E t₀) (B t₀) * (M + ρ)) * h < ρ) :
    ‖YL t₁ - A t₁‖ ≤ h * (11 * g.lipConst (E t₀) (B t₀) *
        (g.lipConst (E t₀) (B t₀) * (M + ρ)) * h + ε) +
      gronwallBound 0 (g.lipConst (E t₀) (B t₀)) η h := by
  set Λ := g.lipConst (E t₀) (B t₀) with hΛ
  have hΛ0 : 0 ≤ Λ := g.lipConst_nonneg _ _
  have hL := g.isLipschitzField_vlasov (E t₀) (B t₀)
  have h1 := LeanDLRA.Literature.P2303_01856.ksl_local_error_of_tube hs hL hΛ0
    (g.isBoundedOnTube_vlasov (E t₀) (B t₀) hM) (by positivity) ht₁ hh hAf hAf₀ hsmall
  have h2 := norm_sub_le_gronwallBound hL hΛ0 (δ := 0) (ηy := 0) (ηz := η)
    hAf.cont hAf.deriv (fun t _ => by simp) hA.cont hA.deriv
    (fun t ht => by
      have h3 : -g.vlasov (E t) (B t) (A t) - -g.vlasov (E t₀) (B t₀) (A t) =
          -(g.vlasov (E t) (B t) (A t) - g.vlasov (E t₀) (B t₀) (A t)) := by abel
      rw [h3, norm_neg]
      exact hη t ht)
    (by simp [hA₀, hAf₀]) t₁ ⟨by linarith, le_rfl⟩
  have hlen : t₁ - t₀ = h := by linarith
  rw [hlen, zero_add] at h2
  calc ‖YL t₁ - A t₁‖ = ‖(YL t₁ - Af t₁) + (Af t₁ - A t₁)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖YL t₁ - Af t₁‖ + ‖Af t₁ - A t₁‖ := norm_add_le _ _
    _ ≤ _ := add_le_add h1 h2

end Fields

/-! ### The staggered time stepping -/

section Leapfrog

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Auxiliary for arXiv 1902.00424, Alg. 1.  The midpoint rule for a `C³` curve in a normed space:
`‖y (c + r) - y (c - r) - 2 r y'(c)‖ ≤ M r³ / 3`. -/
theorem norm_midpoint_error_le {y y1 y2 y3 : ℝ → E} {c r M : ℝ} (hr : 0 ≤ r)
    (h1 : ∀ t ∈ Icc (c - r) (c + r), HasDerivAt y (y1 t) t)
    (h2 : ∀ t ∈ Icc (c - r) (c + r), HasDerivAt y1 (y2 t) t)
    (h3 : ∀ t ∈ Icc (c - r) (c + r), HasDerivAt y2 (y3 t) t)
    (hM : ∀ t ∈ Icc (c - r) (c + r), ‖y3 t‖ ≤ M) :
    ‖y (c + r) - y (c - r) - (2 * r) • y1 c‖ ≤ M * r ^ 3 / 3 := by
  have hp : ∀ s ∈ Icc (0 : ℝ) r, c + s ∈ Icc (c - r) (c + r) := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hm : ∀ s ∈ Icc (0 : ℝ) r, c - s ∈ Icc (c - r) (c + r) := fun s hs =>
    ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have D3 : ∀ s ∈ Icc (0 : ℝ) r, HasDerivAt (fun q => y2 (c + q) - y2 (c - q))
      (y3 (c + s) + y3 (c - s)) s := fun s hs => by
    have h4 := ((h3 _ (hp s hs)).comp_const_add c s).fun_sub
      ((h3 _ (hm s hs)).comp_const_sub c s)
    simpa only [sub_neg_eq_add] using h4
  have D2 : ∀ s ∈ Icc (0 : ℝ) r, HasDerivAt (fun q => y1 (c + q) + y1 (c - q) - (2 : ℝ) • y1 c)
      (y2 (c + s) - y2 (c - s)) s := fun s hs => by
    have h4 := (((h2 _ (hp s hs)).comp_const_add c s).fun_add
      ((h2 _ (hm s hs)).comp_const_sub c s)).sub_const ((2 : ℝ) • y1 c)
    simpa only [sub_eq_add_neg] using h4
  have D1 : ∀ s ∈ Icc (0 : ℝ) r, HasDerivAt (fun q => y (c + q) - y (c - q) - (2 * q) • y1 c)
      (y1 (c + s) + y1 (c - s) - (2 : ℝ) • y1 c) s := fun s hs => by
    have h4 := (((h1 _ (hp s hs)).comp_const_add c s).fun_sub
      ((h1 _ (hm s hs)).comp_const_sub c s)).fun_sub
      (((hasDerivAt_id s).const_mul (2 : ℝ)).smul_const (y1 c))
    simpa only [sub_neg_eq_add, mul_one, id] using h4
  have ha : ∀ s ∈ Icc (0 : ℝ) r, ‖y2 (c + s) - y2 (c - s)‖ ≤ 2 * M * s := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := fun q => y2 (c + q) - y2 (c - q)) (f' := fun s => y3 (c + s) + y3 (c - s))
      (B := fun s => 2 * M * s) (B' := fun _ => 2 * M)
      (fun s hs => (D3 s hs).continuousAt.continuousWithinAt)
      (fun s hs => (D3 s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt) (by simp)
      (fun s => by simpa using (hasDerivAt_id s).const_mul (2 * M)) (fun s hs => ?_)
    have h4 := hM _ (hp s ⟨hs.1, hs.2.le⟩)
    have h5 := hM _ (hm s ⟨hs.1, hs.2.le⟩)
    linarith [norm_add_le (y3 (c + s)) (y3 (c - s))]
  have hb : ∀ s ∈ Icc (0 : ℝ) r, ‖y1 (c + s) + y1 (c - s) - (2 : ℝ) • y1 c‖ ≤ M * s ^ 2 := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := fun q => y1 (c + q) + y1 (c - q) - (2 : ℝ) • y1 c)
      (f' := fun s => y2 (c + s) - y2 (c - s))
      (B := fun s => M * s ^ 2) (B' := fun s => 2 * M * s)
      (fun s hs => (D2 s hs).continuousAt.continuousWithinAt)
      (fun s hs => (D2 s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt) (by simp [two_smul])
      (fun s => ?_) (fun s hs => ha s ⟨hs.1, hs.2.le⟩)
    exact ((hasDerivAt_pow 2 s).const_mul M).congr_deriv (by simp; ring)
  have hd : ∀ s ∈ Icc (0 : ℝ) r, ‖y (c + s) - y (c - s) - (2 * s) • y1 c‖ ≤ M * s ^ 3 / 3 := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := fun q => y (c + q) - y (c - q) - (2 * q) • y1 c)
      (f' := fun s => y1 (c + s) + y1 (c - s) - (2 : ℝ) • y1 c)
      (B := fun s => M * s ^ 3 / 3) (B' := fun s => M * s ^ 2)
      (fun s hs => (D1 s hs).continuousAt.continuousWithinAt)
      (fun s hs => (D1 s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt) (by simp)
      (fun s => ?_) (fun s hs => hb s ⟨hs.1, hs.2.le⟩)
    exact (((hasDerivAt_pow 3 s).const_mul M).div_const 3).congr_deriv (by simp; ring)
  exact hd r ⟨hr, le_rfl⟩

/-- **The staggered electric step has local truncation error `O(τ³)`** (arXiv 1902.00424, Algorithm
1, step 12, and (23)).  If `E` is `C³` in time and solves the semi-discrete equation (2) at the
midpoint, then (23) reproduces `E (t + τ)` up to `M τ³ / 24`, with `M` a bound of `∂ₜ³ E`. -/
theorem predictor_truncation_le {G : Type*} [Fintype G] {dm : Fin 3 → Matrix G G ℝ}
    {E E1 E2 E3 B j : ℝ → VectorField G} {t τ M : ℝ} (hτ : 0 ≤ τ)
    (h1 : ∀ s ∈ Icc t (t + τ), HasDerivAt E (E1 s) s)
    (h2 : ∀ s ∈ Icc t (t + τ), HasDerivAt E1 (E2 s) s)
    (h3 : ∀ s ∈ Icc t (t + τ), HasDerivAt E2 (E3 s) s)
    (hM : ∀ s ∈ Icc t (t + τ), ‖E3 s‖ ≤ M)
    (hE : E1 (t + τ / 2) = curlD dm (B (t + τ / 2)) - j (t + τ / 2)) :
    ‖E (t + τ) - predictor dm τ (E t) (B (t + τ / 2)) (j (t + τ / 2))‖ ≤ M * τ ^ 3 / 24 := by
  have hl : t + τ / 2 - τ / 2 = t := by ring
  have hr : t + τ / 2 + τ / 2 = t + τ := by ring
  have h := norm_midpoint_error_le (c := t + τ / 2) (r := τ / 2) (y := E) (y1 := E1) (y2 := E2)
    (y3 := E3) (M := M) (by positivity) (by rwa [hl, hr]) (by rwa [hl, hr]) (by rwa [hl, hr])
    (by rwa [hl, hr])
  rw [hl, hr, hE] at h
  have h4 : E (t + τ) - predictor dm τ (E t) (B (t + τ / 2)) (j (t + τ / 2)) =
      E (t + τ) - E t - (2 * (τ / 2)) • (curlD dm (B (t + τ / 2)) - j (t + τ / 2)) := by
    rw [predictor, show 2 * (τ / 2) = τ by ring, smul_sub]
    abel
  rw [h4]
  calc _ ≤ M * (τ / 2) ^ 3 / 3 := h
    _ = _ := by ring

/-- **The staggered magnetic step has local truncation error `O(τ³)`** (arXiv 1902.00424, Algorithm
1, step 13): `‖B (t + 3 τ / 2) - (B (t + τ / 2) - τ ∇̃ × E (t + τ))‖ ≤ M τ³ / 24`, if `B` is `C³` in
time and solves (4) at `t + τ`.  Together with `predictor_truncation_le` this is the second-order
consistency of the Maxwell part of Algorithm 1.  Second order of the low-rank part is not
formalized here, and it is not robust: see `strangKSL_not_robust_second_order_rankTwo`. -/
theorem magnetic_truncation_le {G : Type*} [Fintype G] {dp : Fin 3 → Matrix G G ℝ}
    {B B1 B2 B3 E : ℝ → VectorField G} {t τ M : ℝ} (hτ : 0 ≤ τ)
    (h1 : ∀ s ∈ Icc (t + τ / 2) (t + 3 * τ / 2), HasDerivAt B (B1 s) s)
    (h2 : ∀ s ∈ Icc (t + τ / 2) (t + 3 * τ / 2), HasDerivAt B1 (B2 s) s)
    (h3 : ∀ s ∈ Icc (t + τ / 2) (t + 3 * τ / 2), HasDerivAt B2 (B3 s) s)
    (hM : ∀ s ∈ Icc (t + τ / 2) (t + 3 * τ / 2), ‖B3 s‖ ≤ M)
    (hB : B1 (t + τ) = -curlD dp (E (t + τ))) :
    ‖B (t + 3 * τ / 2) - (B (t + τ / 2) - τ • curlD dp (E (t + τ)))‖ ≤ M * τ ^ 3 / 24 := by
  have hl : t + τ - τ / 2 = t + τ / 2 := by ring
  have hr : t + τ + τ / 2 = t + 3 * τ / 2 := by ring
  have h := norm_midpoint_error_le (c := t + τ) (r := τ / 2) (y := B) (y1 := B1) (y2 := B2)
    (y3 := B3) (M := M) (by positivity) (by rwa [hl, hr]) (by rwa [hl, hr]) (by rwa [hl, hr])
    (by rwa [hl, hr])
  rw [hl, hr, hB] at h
  have h4 : B (t + 3 * τ / 2) - (B (t + τ / 2) - τ • curlD dp (E (t + τ))) =
      B (t + 3 * τ / 2) - B (t + τ / 2) - (2 * (τ / 2)) • -curlD dp (E (t + τ)) := by
    rw [show 2 * (τ / 2) = τ by ring, smul_neg]
    abel
  rw [h4]
  calc _ ≤ M * (τ / 2) ^ 3 / 3 := h
    _ = _ := by ring

end Leapfrog

/-! ### Spectral differentiation -/

section Spectral

open Complex (I)
open ComplexConjugate

variable {N : ℕ} [NeZero N]

/-- The kernel of the spectral derivative with symbol `i κ`, `(N)⁻¹ ∑ₖ i κₖ e^{2 π i k z / N}`. -/
noncomputable def specKernel (κ : ZMod N → ℝ) (z : ZMod N) : ℂ :=
  (N : ℂ)⁻¹ * ∑ k, (I * (κ k : ℂ)) * ZMod.stdAddChar (k * z)

/-- The spectral derivative on the periodic grid `ZMod N`, as a real matrix. -/
noncomputable def specMat (κ : ZMod N → ℝ) : Matrix (ZMod N) (ZMod N) ℝ :=
  Matrix.of fun x y => (specKernel κ (x - y)).re

/-- The spectral gradient of the 1D model of Sec. 6 of arXiv 1902.00424: `∂ₓ` in the first
direction and zero in the two others. -/
noncomputable def spec1 (κ : ZMod N → ℝ) : Fin 3 → Matrix (ZMod N) (ZMod N) ℝ :=
  ![specMat κ, 0, 0]

private theorem conj_stdAddChar (a : ZMod N) :
    conj (ZMod.stdAddChar a) = ZMod.stdAddChar (-a) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

private theorem specKernel_neg {κ : ZMod N → ℝ} (hκ : ∀ k, κ (-k) = -κ k) (z : ZMod N) :
    specKernel κ (-z) = -specKernel κ z := by
  have h1 := Equiv.sum_comp (Equiv.neg (ZMod N))
    fun k => (I * (κ k : ℂ)) * ZMod.stdAddChar (k * (-z))
  simp only [specKernel]
  rw [← h1, ← mul_neg, ← Finset.sum_neg_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
  simp only [Equiv.neg_apply, hκ, neg_mul_neg, Complex.ofReal_neg]
  ring

private theorem conj_specKernel {κ : ZMod N → ℝ} (hκ : ∀ k, κ (-k) = -κ k) (z : ZMod N) :
    conj (specKernel κ z) = specKernel κ z := by
  have h1 := Equiv.sum_comp (Equiv.neg (ZMod N))
    fun k => (I * (κ k : ℂ)) * ZMod.stdAddChar (k * z)
  simp only [specKernel, map_mul, map_sum, map_inv₀, Complex.conj_natCast, Complex.conj_I,
    Complex.conj_ofReal, conj_stdAddChar]
  rw [← h1]
  refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
  simp only [Equiv.neg_apply, hκ, Complex.ofReal_neg, neg_mul, mul_neg]

private theorem ofReal_specKernel_re {κ : ZMod N → ℝ} (hκ : ∀ k, κ (-k) = -κ k) (z : ZMod N) :
    ((specKernel κ z).re : ℂ) = specKernel κ z :=
  Complex.conj_eq_iff_re.1 (conj_specKernel hκ z)

/-- The spectral derivative of a real function, in Fourier space: multiplication by `i κ`, for the
wave numbers of arXiv 1902.00424, Sec. 6, by `i k`. -/
theorem ofReal_specMat_mulVec {κ : ZMod N → ℝ} (hκ : ∀ k, κ (-k) = -κ k) (u : ZMod N → ℝ) :
    (fun x => ((specMat κ *ᵥ u) x : ℂ)) =
      ZMod.dft.symm (fun k => (I * (κ k : ℂ)) * ZMod.dft (fun y => (u y : ℂ)) k) := by
  funext x
  simp only [mulVec, dotProduct, specMat, of_apply, Complex.ofReal_sum, Complex.ofReal_mul,
    ofReal_specKernel_re hκ, ZMod.invDFT_apply, ZMod.dft_apply, smul_eq_mul]
  simp only [specKernel, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun y _ => ?_
  have h1 : (ZMod.stdAddChar (k * (x - y)) : ℂ) =
      ZMod.stdAddChar (k * x) * ZMod.stdAddChar (-(y * k)) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [h1]
  ring

/-- Auxiliary for arXiv 1902.00424, Sec. 6.  The discrete Fourier transform of a spectral
derivative. -/
theorem dft_specMat {κ : ZMod N → ℝ} (hκ : ∀ k, κ (-k) = -κ k) (u : ZMod N → ℝ) (k : ZMod N) :
    ZMod.dft (fun x => ((specMat κ *ᵥ u) x : ℂ)) k =
      (I * (κ k : ℂ)) * ZMod.dft (fun y => (u y : ℂ)) k := by
  rw [ofReal_specMat_mulVec hκ, LinearEquiv.apply_symm_apply]

/-- Auxiliary for arXiv 1902.00424, Sec. 6.  For an odd symbol the spectral derivative is a skew
matrix. -/
theorem specMat_skew {κ : ZMod N → ℝ} (hκ : ∀ k, κ (-k) = -κ k) :
    specMat κ = -(specMat κ)ᵀ := by
  ext x y
  have h1 : (-(specMat κ)ᵀ) x y = -(specKernel κ (y - x)).re := rfl
  rw [h1, show y - x = -(x - y) by ring, specKernel_neg hκ, Complex.neg_re, neg_neg]
  rfl

/-- Auxiliary for arXiv 1902.00424, Sec. 6.  For an odd symbol the spectral derivative of a
constant vanishes. -/
theorem specMat_const {κ : ZMod N → ℝ} (hκ : ∀ k, κ (-k) = -κ k) (c : ℝ) :
    specMat κ *ᵥ (fun _ => c) = 0 := by
  funext x
  have hs : ∑ z, (specKernel κ z).re = 0 := by
    have h1 : ∑ z, (specKernel κ (-z)).re = ∑ z, (specKernel κ z).re :=
      Equiv.sum_comp (Equiv.neg (ZMod N)) fun z => (specKernel κ z).re
    simp only [specKernel_neg hκ, Complex.neg_re, Finset.sum_neg_distrib] at h1
    linarith
  have h2 : ∑ y, (specKernel κ (x - y)).re = ∑ z, (specKernel κ z).re :=
    Equiv.sum_comp (Equiv.subLeft x) fun z => (specKernel κ z).re
  simp only [mulVec, dotProduct, specMat, of_apply, ← Finset.sum_mul, h2, hs, zero_mul,
    Pi.zero_apply]

/-- **Spectral differentiation is compatible** (arXiv 1902.00424, Secs. 2 and 6) when the symbol is
odd, so that the derivative of a real function is real, and vanishes only at the zero mode.  The
result is a real skew matrix, with the constants as its kernel. -/
theorem isCompatible_spec {κ : ZMod N → ℝ} (hκ : ∀ k, κ (-k) = -κ k)
    (hκ0 : ∀ k, k ≠ 0 → κ k ≠ 0) : IsCompatible (spec1 κ) (spec1 κ) := by
  have hskew := specMat_skew hκ
  refine ⟨fun a b => ?_, fun a => ?_, fun u => ⟨fun h => ?_, ?_⟩⟩
  · have h0 : ∀ c, spec1 κ c = 0 ∨ spec1 κ c = specMat κ := fun c => by
      fin_cases c
      · exact Or.inr rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
    rcases h0 a with ha | ha <;> rcases h0 b with hb | hb <;> rw [ha, hb] <;>
      first
        | exact Commute.zero_left _
        | exact Commute.zero_right _
  · fin_cases a
    · exact hskew
    · simp [spec1]
    · simp [spec1]
  · have h0 : specMat κ *ᵥ u = 0 := h 0
    have h1 := ofReal_specMat_mulVec hκ u
    rw [h0] at h1
    have h2 : ZMod.dft.symm (fun k => (I * (κ k : ℂ)) * ZMod.dft (fun y => (u y : ℂ)) k) = 0 := by
      rw [← h1]
      funext x
      simp
    have h3 := (LinearEquiv.map_eq_zero_iff _).1 h2
    have h4 : ∀ k, k ≠ 0 → ZMod.dft (fun y => (u y : ℂ)) k = 0 := by
      intro k hk
      have h5 := congrFun h3 k
      have h6 : (κ k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hκ0 k hk)
      simpa [h6] using h5
    have h5 : ∀ x, (u x : ℂ) = (N : ℂ)⁻¹ * ZMod.dft (fun y => (u y : ℂ)) 0 := by
      intro x
      have h6 := congrFun (ZMod.dft.symm_apply_apply (fun y => (u y : ℂ))) x
      rw [ZMod.invDFT_apply, Finset.sum_eq_single 0] at h6
      · simpa using h6.symm
      · intro k _ hk
        rw [h4 k hk, smul_zero]
      · simp
    refine ⟨u 0, funext fun x => ?_⟩
    exact Complex.ofReal_injective ((h5 x).trans (h5 0).symm)
  · rintro ⟨c, rfl⟩ a
    fin_cases a
    · exact specMat_const hκ c
    · simp [spec1]
    · simp [spec1]

/-- The wave numbers of the paper on a domain of length `L`: `2 π k / L` for `|k| < N / 2`. -/
noncomputable def waveNumber (L : ℝ) (k : ZMod N) : ℝ := 2 * Real.pi / L * k.valMinAbs

/-- **Spectral differentiation on an odd grid is compatible** (arXiv 1902.00424, Sec. 6, which uses
an odd number of grid points in all experiments).  So all results on (23)-(27) hold for the
discretization of the paper's numerical experiments.  Even grids: `gauss_unsolvable_even_grid`. -/
theorem isCompatible_spectral (hN : Odd N) {L : ℝ} (hL : L ≠ 0) :
    IsCompatible (spec1 (waveNumber (N := N) L)) (spec1 (waveNumber L)) := by
  refine isCompatible_spec (fun k => ?_) fun k hk => ?_
  · have h1 : 2 * k.val ≠ N := fun h => by
      obtain ⟨c, hc⟩ := hN
      omega
    rw [waveNumber, waveNumber, ZMod.valMinAbs_neg_of_ne_half h1]
    push_cast
    ring
  · have h1 : k.valMinAbs ≠ 0 := fun h => hk ((ZMod.valMinAbs_eq_zero k).1 h)
    have h2 : (k.valMinAbs : ℝ) ≠ 0 := Int.cast_ne_zero.2 h1
    have h3 := Real.pi_ne_zero
    simp only [waveNumber]
    positivity

/-- A real spectral derivative annihilates the Nyquist mode: an odd real symbol vanishes at
`k = N / 2`, where `-k = k`.  This is the reason for the remark of arXiv 1902.00424, Sec. 6, that
the imaginary entry `φ̂_{n/2}` is lost on an even grid. -/
theorem symbol_nyquist {κ : ZMod N → ℝ} (hκ : ∀ k, κ (-k) = -κ k) {k : ZMod N}
    (h : 2 * k.val = N) : κ k = 0 := by
  have h1 : -k = k := (ZMod.neg_eq_self_iff k).2 (Or.inr h)
  have h2 := hκ k
  rw [h1] at h2
  linarith

/-- **On an even grid the spectral discrete Gauss law is not solvable** (arXiv 1902.00424, Sec. 6).
For `N` even and any odd real symbol, so for any differentiation that maps real functions to real
functions, there is a charge `ρ`, namely the Nyquist mode, such that `∂̃ₓ E₁ = |Ω|⁻¹ ∫ ρ - ρ` has no
solution.  So the requirement of the paper to use an odd number of grid points is necessary, and
Algorithm 2 cannot enforce Gauss' law on an even grid.  In particular `IsCompatible` fails. -/
theorem gauss_unsolvable_even_grid (hN : Even N) (h2 : 2 ≤ N) {κ : ZMod N → ℝ}
    (hκ : ∀ k, κ (-k) = -κ k) :
    ∃ ρ : ZMod N → ℝ, ∀ F : VectorField (ZMod N), divD (spec1 κ) F ≠ gaussRhs ρ := by
  obtain ⟨c, hc⟩ := hN
  have hlt : c < N := by omega
  let k₀ : ZMod N := (c : ℕ)
  have hval : k₀.val = c := ZMod.val_natCast_of_lt hlt
  have hk : 2 * k₀.val = N := by omega
  have hk0 : k₀ ≠ 0 := fun h => by
    rw [h, ZMod.val_zero] at hval
    omega
  have hneg : -k₀ = k₀ := (ZMod.neg_eq_self_iff k₀).2 (Or.inr hk)
  have hprim := ZMod.isPrimitive_stdAddChar N
  let w : ZMod N → ℂ := fun x => ZMod.stdAddChar (x * k₀)
  have hconj : ∀ x, conj (w x) = w x := fun x => by
    simp only [w, conj_stdAddChar]
    rw [← mul_neg, hneg]
  have hre : ∀ x, ((w x).re : ℂ) = w x := fun x => Complex.conj_eq_iff_re.1 (hconj x)
  have hsq : ∀ x, (w x).re * (w x).re = 1 := fun x => by
    have h1 : w x * w x = 1 := by
      simp only [w]
      rw [← AddChar.map_add_eq_mul]
      have h3 : x * k₀ + x * k₀ = 0 := by
        have h4 : k₀ + k₀ = 0 := by
          nth_rw 2 [← hneg]
          exact add_neg_cancel k₀
        rw [← mul_add, h4, mul_zero]
      rw [h3, AddChar.map_zero_eq_one]
    have h4 : (((w x).re * (w x).re : ℝ) : ℂ) = 1 := by
      push_cast
      rw [hre, h1]
    exact_mod_cast h4
  let u : ZMod N → ℝ := fun x => (w x).re
  have hsum : ∑ x, u x = 0 := by
    have h1 : ∑ x, w x = 0 := by
      have h3 := AddChar.sum_mulShift k₀ hprim
      simpa [hk0, w] using h3
    have h3 : ((∑ x, u x : ℝ) : ℂ) = 0 := by
      push_cast
      simp only [u, hre, h1]
    exact_mod_cast h3
  have hdft : ∀ k, (I * (κ k : ℂ)) * ZMod.dft (fun y => (u y : ℂ)) k = 0 := by
    intro k
    by_cases hkk : k = k₀
    · rw [hkk, symbol_nyquist hκ hk]
      simp
    · have h1 : ZMod.dft (fun y => (u y : ℂ)) k = 0 := by
        rw [ZMod.dft_apply]
        have h3 : ∀ j : ZMod N, ZMod.stdAddChar (-(j * k)) • ((u j : ℝ) : ℂ) =
            ZMod.stdAddChar (j * (k₀ - k)) := fun j => by
          simp only [u, hre, w, smul_eq_mul]
          rw [← AddChar.map_add_eq_mul]
          congr 1
          ring
        simp only [h3]
        have h4 := AddChar.sum_mulShift (k₀ - k) hprim
        simpa [sub_ne_zero.2 (Ne.symm hkk)] using h4
      rw [h1, mul_zero]
  have hDu : specMat κ *ᵥ u = 0 := by
    have h1 := ofReal_specMat_mulVec hκ u
    simp only [hdft] at h1
    funext x
    have h3 := congrFun h1 x
    have h4 : ZMod.dft.symm (fun _ : ZMod N => (0 : ℂ)) x = 0 := by
      have h5 : (fun _ : ZMod N => (0 : ℂ)) = 0 := rfl
      rw [h5, map_zero]
      rfl
    rw [h4] at h3
    exact_mod_cast h3
  refine ⟨u, fun F hF => ?_⟩
  have hdiv : divD (spec1 κ) F = specMat κ *ᵥ F 0 := by
    simp [divD, spec1, Fin.sum_univ_three]
  have hgauss : gaussRhs u = -u := by
    funext x
    simp [gaussRhs, mean, hsum]
  rw [hdiv, hgauss] at hF
  have h1 : u ⬝ᵥ (specMat κ *ᵥ F 0) = 0 := by
    rw [dotProduct_mulVec, specMat_skew hκ, vecMul_neg, vecMul_transpose, hDu, neg_zero,
      zero_dotProduct]
  rw [hF] at h1
  have h3 : u ⬝ᵥ -u = -(N : ℝ) := by
    simp only [dotProduct, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    simp only [u, hsq]
    simp [ZMod.card]
  rw [h3] at h1
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  exact hN0 (by linarith)

/-- Auxiliary for arXiv 1902.00424, Sec. 6.  The spectral gradient of an even grid is never
compatible, whatever the odd symbol. -/
theorem not_isCompatible_even_grid (hN : Even N) (h2 : 2 ≤ N) {κ : ZMod N → ℝ}
    (hκ : ∀ k, κ (-k) = -κ k) : ¬IsCompatible (spec1 κ) (spec1 κ) := fun hc => by
  obtain ⟨ρ, hρ⟩ := gauss_unsolvable_even_grid hN h2 hκ
  obtain ⟨φ, -, hφ⟩ := hc.exists_poisson (sum_gaussRhs ρ)
  exact hρ _ hφ

/-- Auxiliary for arXiv 1902.00424, Sec. 6.  **The Poisson problem (27) in spectral space**: if `φ`
solves (27), with right-hand side `g`, then `κₖ² φ̂ₖ = ĝₖ`. So for `κₖ ≠ 0` the solution is `φ̂ₖ =
ĝₖ / κₖ²`, with a plus sign, because `-∂ₓ²` has symbol `+κ²`. Compare `poisson_printed_false`. -/
theorem spectral_poisson {κ : ZMod N → ℝ} (hκ : ∀ k, κ (-k) = -κ k) {τ : ℝ}
    {En j : VectorField (ZMod N)} {ρ φ : ZMod N → ℝ}
    (hφ : IsPoisson (spec1 κ) (spec1 κ) τ En j ρ φ) (k : ZMod N) :
    (κ k : ℂ) ^ 2 * ZMod.dft (fun x => (φ x : ℂ)) k =
      ZMod.dft (fun x => (poissonRhs (spec1 κ) τ En j ρ x : ℂ)) k := by
  have hdiv : divD (spec1 κ) (gradD (spec1 κ) φ) = specMat κ *ᵥ (specMat κ *ᵥ φ) := by
    simp [divD, gradD, spec1, Fin.sum_univ_three]
  have h1 : (fun x => (poissonRhs (spec1 κ) τ En j ρ x : ℂ)) =
      -(fun x => ((specMat κ *ᵥ (specMat κ *ᵥ φ)) x : ℂ)) := by
    funext x
    have h2 := congrFun hφ x
    rw [hdiv] at h2
    simp only [Pi.neg_apply] at h2 ⊢
    rw [← h2]
    push_cast
    rfl
  rw [h1, map_neg, Pi.neg_apply, dft_specMat hκ, dft_specMat hκ]
  have hI : I * I = -1 := Complex.I_mul_I
  linear_combination ((κ k : ℂ) ^ 2 * ZMod.dft (fun x => (φ x : ℂ)) k) * hI

/-- **False claim of arXiv 1902.00424, Sec. 6.**  The paper states the solution of (27) in spectral
space as `φ̂ₖ = -ĝₖ / k²`, with `g` the right-hand side of (27).  This has the wrong sign: at every
mode with `κₖ ≠ 0` and `ĝₖ ≠ 0` the true solution has `φ̂ₖ = +ĝₖ / κₖ²` (`spectral_poisson`).  With
the printed sign, (25) would double the defect of Gauss' law instead of removing it
(`gauss_defect_doubled`).  The next displayed formula of the paper,
`(∂ₓ φ)^ₖ = -(i / k) φ̂ₖ`, is a misprint as well: differentiation is multiplication of `φ̂ₖ` by
`i k` (`dft_specMat`), as the text before it says. -/
theorem poisson_printed_false {κ : ZMod N → ℝ} (hκ : ∀ k, κ (-k) = -κ k) {τ : ℝ}
    {En j : VectorField (ZMod N)} {ρ φ : ZMod N → ℝ}
    (hφ : IsPoisson (spec1 κ) (spec1 κ) τ En j ρ φ) {k : ZMod N} (hk : κ k ≠ 0)
    (hg : ZMod.dft (fun x => (poissonRhs (spec1 κ) τ En j ρ x : ℂ)) k ≠ 0) :
    ZMod.dft (fun x => (φ x : ℂ)) k ≠
      -(1 / (κ k : ℂ) ^ 2) * ZMod.dft (fun x => (poissonRhs (spec1 κ) τ En j ρ x : ℂ)) k := by
  intro h
  have h1 := spectral_poisson hκ hφ k
  have h2 : (κ k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hk
  set G := ZMod.dft (fun x => (poissonRhs (spec1 κ) τ En j ρ x : ℂ)) k with hG
  have h3 : (κ k : ℂ) ^ 2 * (-(1 / (κ k : ℂ) ^ 2) * G) = -G := by
    field_simp
  rw [h, h3] at h1
  exact hg (by linear_combination (-1 / 2 : ℂ) * h1)

/-- Auxiliary for arXiv 1902.00424, Sec. 6.  The hypotheses of `poisson_printed_false` can be met:
on every odd grid with at least three points, for the wave numbers of the paper, the solution of
(27) for a point charge violates the printed formula at the first mode. -/
theorem exists_poisson_printed_false (hN : Odd N) (h3 : 3 ≤ N) {L : ℝ} (hL : L ≠ 0) :
    ∃ (ρ φ : ZMod N → ℝ), IsPoisson (spec1 (waveNumber L)) (spec1 (waveNumber L)) 1 0 0 ρ φ ∧
      ∃ k : ZMod N, waveNumber L k ≠ 0 ∧
        ZMod.dft (fun x => (φ x : ℂ)) k ≠ -(1 / (waveNumber L k : ℂ) ^ 2) *
          ZMod.dft (fun x => (poissonRhs (spec1 (waveNumber L)) 1 0 0 ρ x : ℂ)) k := by
  classical
  have : Fact (1 < N) := ⟨by omega⟩
  have hc := isCompatible_spectral (N := N) hN hL
  have hodd : ∀ k : ZMod N, waveNumber L (-k) = -waveNumber L k := fun k => by
    have h1 : 2 * k.val ≠ N := fun h => by
      obtain ⟨c, hc⟩ := hN
      omega
    rw [waveNumber, waveNumber, ZMod.valMinAbs_neg_of_ne_half h1]
    push_cast
    ring
  have hne : (1 : ZMod N) ≠ 0 := one_ne_zero
  have hk : waveNumber (N := N) L 1 ≠ 0 := fun h => by
    have h1 : ((1 : ZMod N).valMinAbs : ℝ) ≠ 0 :=
      Int.cast_ne_zero.2 fun h2 => hne ((ZMod.valMinAbs_eq_zero _).1 h2)
    have h2 := Real.pi_ne_zero
    simp only [waveNumber, mul_eq_zero, div_eq_zero_iff] at h
    simp_all
  let ρ : ZMod N → ℝ := fun x => if x = 0 then 1 else 0
  obtain ⟨φ, -, hφ⟩ := hc.exists_isPoisson 1 0 0 ρ
  refine ⟨ρ, φ, hφ, 1, hk, poisson_printed_false hodd hφ hk ?_⟩
  have h1 : ∀ x, poissonRhs (spec1 (waveNumber (N := N) L)) 1 0 0 ρ x = gaussRhs ρ x := fun x => by
    simp [poissonRhs, divD]
  have hsum : ∑ j : ZMod N, (ZMod.stdAddChar (-(j * 1)) : ℂ) = 0 := by
    have h2 := AddChar.sum_mulShift (-1 : ZMod N) (ZMod.isPrimitive_stdAddChar N)
    simpa [hne, mul_neg] using h2
  simp only [h1, ZMod.dft_apply, gaussRhs, smul_eq_mul, Complex.ofReal_sub, mul_sub,
    Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, zero_mul, zero_sub, neg_ne_zero]
  have h2 : ∑ x : ZMod N, (ZMod.stdAddChar (-(x * 1)) : ℂ) * (ρ x : ℂ) = 1 := by
    rw [Finset.sum_eq_single 0]
    · simp [ρ]
    · intro b _ hb
      simp [ρ, hb]
    · simp
  rw [h2]
  exact one_ne_zero

end Spectral

/-! ### The linear regime on the spectral grid, in physical space -/

section SpectralLinear

open MeasureTheory
open Complex (I)

variable {N : ℕ} [NeZero N]

/-- The discrete Fourier coefficient `N⁻¹ ∑ₓ u x e^{-2 π i k x / N}` of a real grid function. -/
noncomputable def gridCoeff (k : ZMod N) (u : ZMod N → ℝ) : ℂ :=
  (N : ℂ)⁻¹ * ZMod.dft (fun x => (u x : ℂ)) k

/-- Auxiliary for arXiv 1902.00424, Sec. 3. -/
theorem gridCoeff_apply (k : ZMod N) (u : ZMod N → ℝ) :
    gridCoeff k u = (N : ℂ)⁻¹ * ∑ x, ZMod.stdAddChar (-(x * k)) * (u x : ℂ) := by
  simp only [gridCoeff, ZMod.dft_apply, smul_eq_mul]

/-- The Fourier coefficient as a continuous linear map. -/
noncomputable def gridCoeffCLM (k : ZMod N) : (ZMod N → ℝ) →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := gridCoeff k
      map_add' := fun u w => by
        simp only [gridCoeff_apply, Pi.add_apply, Complex.ofReal_add, mul_add,
          Finset.sum_add_distrib]
      map_smul' := fun c u => by
        simp only [gridCoeff_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul,
          RingHom.id_apply, Complex.real_smul]
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring }

/-- Auxiliary for arXiv 1902.00424, Sec. 3. -/
@[simp] theorem gridCoeffCLM_apply (k : ZMod N) (u : ZMod N → ℝ) :
    gridCoeffCLM k u = gridCoeff k u := rfl

/-- Auxiliary for arXiv 1902.00424, Sec. 3. -/
theorem gridCoeff_specMat {κ : ZMod N → ℝ} (hκ : ∀ k, κ (-k) = -κ k) (k : ZMod N)
    (u : ZMod N → ℝ) : gridCoeff k (specMat κ *ᵥ u) = (I * (κ k : ℂ)) * gridCoeff k u := by
  simp only [gridCoeff]
  rw [dft_specMat hκ]
  ring

/-- Auxiliary for arXiv 1902.00424, Sec. 3. -/
theorem gridCoeff_const (k : ZMod N) (c : ℝ) :
    gridCoeff k (fun _ => c) = if k = 0 then (c : ℂ) else 0 := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have h1 : ∑ x : ZMod N, (ZMod.stdAddChar (x * -k) : ℂ) = if -k = 0 then (N : ℂ) else 0 := by
    have h2 := AddChar.sum_mulShift (-k) (ZMod.isPrimitive_stdAddChar N)
    simpa [ZMod.card] using h2
  have h2 : ∑ x : ZMod N, (ZMod.stdAddChar (-(x * k)) : ℂ) * (c : ℂ) =
      (∑ x : ZMod N, (ZMod.stdAddChar (x * -k) : ℂ)) * (c : ℂ) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by rw [mul_neg]
  rw [gridCoeff_apply, h2, h1]
  by_cases hk : k = 0
  · simp [hk]
    field_simp
  · simp [hk]

/-- Auxiliary for arXiv 1902.00424, Sec. 3.  Fourier inversion: a grid function is the sum of its
modes. -/
theorem sum_gridCoeff (u : ZMod N → ℝ) (x : ZMod N) :
    (u x : ℂ) = ∑ k, gridCoeff k u * ZMod.stdAddChar (k * x) := by
  have h6 := congrFun (ZMod.dft.symm_apply_apply (fun y => (u y : ℂ))) x
  rw [ZMod.invDFT_apply] at h6
  rw [← h6, Finset.smul_sum]
  simp only [gridCoeff, smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The wave vector of the 1D model of Sec. 6 of arXiv 1902.00424. -/
def waveVec (κ : ZMod N → ℝ) (k : ZMod N) : Fin 3 → ℝ := ![κ k, 0, 0]

/-- `(f, E, B)` solves the linearized Vlasov-Maxwell equations of Sec. 3 of arXiv 1902.00424 on
`[0, T]`, in physical space, for the 1D spatial model of Sec. 6 with spectral differentiation
`∇̃ = (∂̃ₓ, 0, 0)` and the velocity measure `μ`, `g = ∇ᵥ f⁰`:

    ∂ₜ f + v · ∇̃ₓ f - (E + v × B) · ∇ᵥ f⁰ = 0,
    ∂ₜ E = ∇̃ × B - j⁰ - ∫ v f dμ,
    ∂ₜ B = -∇̃ × E. -/
structure IsSpectralSolution (μ : Measure (Fin 3 → ℝ)) (g : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (j0 : Fin 3 → ℝ) (κ : ZMod N → ℝ) (T : ℝ) (f : ℝ → ZMod N → (Fin 3 → ℝ) → ℝ)
    (E B : ℝ → VectorField (ZMod N)) : Prop where
  vlasov : ∀ x v, ODESolution (fun t _ => -∑ a, v a * (spec1 κ a *ᵥ fun y => f t y v) x +
    ((fun a => E t a x) + v ⨯₃ fun a => B t a x) ⬝ᵥ g v) (fun t => f t x v) 0 T
  ampere : ODESolution (fun t _ => curlD (spec1 κ) (B t) - (fun a _ => j0 a) -
    fun a x => ∫ v, v a * f t x v ∂μ) E 0 T
  faraday : ODESolution (fun t _ => -curlD (spec1 κ) (E t)) B 0 T
  integrable : ∀ t ∈ Icc (0 : ℝ) T, ∀ x a, Integrable (fun v => v a * f t x v) μ

/-- The Fourier coefficients of a discrete vector field. -/
noncomputable def fieldCoeff (k : ZMod N) : VectorField (ZMod N) →L[ℝ] (Fin 3 → ℂ) :=
  ContinuousLinearMap.pi fun a => (gridCoeffCLM k).comp (ContinuousLinearMap.proj a)

/-- Auxiliary for arXiv 1902.00424, Sec. 3. -/
theorem fieldCoeff_apply (k : ZMod N) (F : VectorField (ZMod N)) (a : Fin 3) :
    fieldCoeff k F a = gridCoeff k (F a) := rfl

/-- Auxiliary for arXiv 1902.00424, Sec. 3.  The spectral curl in Fourier space is `i k ×`. -/
theorem fieldCoeff_curlD {κ : ZMod N → ℝ} (hκ : ∀ k, κ (-k) = -κ k) (k : ZMod N)
    (F : VectorField (ZMod N)) :
    fieldCoeff k (curlD (spec1 κ) F) = I • (toC (waveVec κ k) ⨯₃ fieldCoeff k F) := by
  have hz : gridCoeff k (0 : ZMod N → ℝ) = 0 := map_zero (gridCoeffCLM k)
  have hn : ∀ u : ZMod N → ℝ, gridCoeff k (-u) = -gridCoeff k u := fun u =>
    map_neg (gridCoeffCLM k) u
  funext a
  rw [fieldCoeff_apply, Pi.smul_apply, cross_apply]
  fin_cases a
  · simp [curlD, spec1, hz, toC, waveVec]
  · simp [curlD, spec1, hn, toC, waveVec, gridCoeff_specMat hκ, fieldCoeff_apply]
    ring
  · simp [curlD, spec1, toC, waveVec, gridCoeff_specMat hκ, fieldCoeff_apply]
    ring

/-- **The physical-space linearized system decouples into the Fourier modes (6)-(8)** (arXiv
1902.00424, Sec. 3), for the 1D spectral model.  The Fourier coefficients of a solution of
`IsSpectralSolution` solve (6)-(8) with the wave vector `(κₖ, 0, 0)` and the source
`j⁰ δ_{k, 0}`. -/
theorem IsSpectralSolution.modes {μ : Measure (Fin 3 → ℝ)} {g : (Fin 3 → ℝ) → Fin 3 → ℝ}
    {j0 : Fin 3 → ℝ} {κ : ZMod N → ℝ} {T : ℝ} {f : ℝ → ZMod N → (Fin 3 → ℝ) → ℝ}
    {E B : ℝ → VectorField (ZMod N)} (h : IsSpectralSolution μ g j0 κ T f E B)
    (hκ : ∀ k, κ (-k) = -κ k) (hκ0 : ∀ k, k ≠ 0 → κ k ≠ 0) (k : ZMod N) :
    IsModeSolution μ g (if waveVec κ k = 0 then toC j0 else 0) (waveVec κ k) T
      (fun t v => gridCoeff k fun x => f t x v) (fun t => fieldCoeff k (E t))
      (fun t => fieldCoeff k (B t)) := by
  have hκz : κ 0 = 0 := by
    have h1 := hκ 0
    rw [neg_zero] at h1
    linarith
  have hW : waveVec κ k = 0 ↔ k = 0 := by
    constructor
    · intro h1
      by_contra hk
      exact hκ0 k hk (congrFun h1 0)
    · rintro rfl
      funext a
      fin_cases a <;> simp [waveVec, hκz]
  have hsrc : fieldCoeff k (fun a _ => j0 a) = if waveVec κ k = 0 then toC j0 else 0 := by
    funext a
    rw [fieldCoeff_apply, gridCoeff_const]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hW.2 h1) h2
    · exact absurd (hW.1 h2) h1
    · rfl
  have hcomp : ∀ t v a, (gridCoeff k (fun x => f t x v) • toC v) a =
      gridCoeff k (fun x => v a * f t x v) := fun t v a => by
    have h1 : (fun x => v a * f t x v) = v a • fun x => f t x v := by
      funext x
      simp
    rw [h1]
    have h2 := map_smul (gridCoeffCLM k) (v a) (fun x => f t x v)
    simp only [gridCoeffCLM_apply] at h2
    rw [h2, Complex.real_smul]
    simp [toC, mul_comm]
  have hexp : ∀ t v a, gridCoeff k (fun x => v a * f t x v) =
      (N : ℂ)⁻¹ * ∑ x, ZMod.stdAddChar (-(x * k)) * ((v a * f t x v : ℝ) : ℂ) := fun t v a =>
    gridCoeff_apply k _
  have hint : ∀ t ∈ Icc (0 : ℝ) T, ∀ a,
      Integrable (fun v => gridCoeff k (fun x => v a * f t x v)) μ := fun t ht a => by
    simp only [hexp]
    exact (integrable_finsetSum _ fun x _ => (h.integrable t ht x a).ofReal.const_mul _).const_mul _
  refine ⟨fun v => ?_, ?_, ?_, fun t ht => ?_⟩
  · have hy : ODESolution (fun t _ => fun x => -∑ a, v a * (spec1 κ a *ᵥ fun y => f t y v) x +
        ((fun a => E t a x) + v ⨯₃ fun a => B t a x) ⬝ᵥ g v) (fun t x => f t x v) 0 T :=
      ⟨continuousOn_pi.2 fun x => (h.vlasov x v).cont, fun t ht =>
        hasDerivWithinAt_pi.2 fun x => (h.vlasov x v).deriv t ht⟩
    refine odeSolution_map (gridCoeffCLM k) hy fun t _ => ?_
    have hR : (fun x => -∑ a, v a * (spec1 κ a *ᵥ fun y => f t y v) x +
        ((fun a => E t a x) + v ⨯₃ fun a => B t a x) ⬝ᵥ g v) =
        -(v 0 • (specMat κ *ᵥ fun y => f t y v)) +
          (g v 0 • E t 0 + g v 1 • E t 1 + g v 2 • E t 2) +
          ((g v ⨯₃ v) 0 • B t 0 + (g v ⨯₃ v) 1 • B t 1 + (g v ⨯₃ v) 2 • B t 2) := by
      funext x
      simp [Fin.sum_univ_three, spec1, dotProduct, cross_apply]
      ring
    rw [hR]
    simp only [map_add, map_neg, map_smul, gridCoeffCLM_apply, gridCoeff_specMat hκ,
      Complex.real_smul]
    simp only [dotProduct, Fin.sum_univ_three, Pi.add_apply, cross_apply, toC, fieldCoeff_apply,
      waveVec]
    simp
    ring
  · refine odeSolution_map (fieldCoeff k) h.ampere fun t ht => ?_
    have hcur : fieldCoeff k (fun a x => ∫ v, v a * f t x v ∂μ) =
        ∫ v, gridCoeff k (fun x => f t x v) • toC v ∂μ := by
      funext a
      have ht' : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.le⟩
      have hi : ∀ b, Integrable (fun v => (gridCoeff k (fun x => f t x v) • toC v) b) μ :=
        fun b => by
          simp only [hcomp]
          exact hint t ht' b
      rw [fieldCoeff_apply, eval_integral hi]
      simp only [hcomp, hexp]
      rw [integral_const_mul, integral_finsetSum _ fun x _ =>
        (h.integrable t ht' x a).ofReal.const_mul _, gridCoeff_apply]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [integral_const_mul]
      exact congrArg _ (integral_ofReal (𝕜 := ℂ) (f := fun v => v a * f t x v)).symm
    rw [map_sub, map_sub, fieldCoeff_curlD hκ, hsrc, hcur]
  · refine odeSolution_map (fieldCoeff k) h.faraday fun t _ => ?_
    rw [map_neg, fieldCoeff_curlD hκ]
  · refine Integrable.of_eval fun a => ?_
    simp only [hcomp]
    exact hint t ht a

/-- **Low rank in the linear regime, in physical space** (arXiv 1902.00424, Sec. 3, for the 1D
spectral model of Sec. 6).  Let `(f, E, B)` solve the linearized Vlasov-Maxwell equations on the
spectral grid.  If the initial data of `f` and `B` have Fourier modes only in `S ∋ 0` and `E` is
initialized by Gauss' law in Fourier space, then no other mode is ever excited, and for all
`t ∈ [0, T]`

    f(t, x, v) = ∑_{k ∈ S} f̂_k(t, v) e^{2 π i k x / N},

which is (9).  So `f⁰(v) + f(t, x, v)` has rank at most `|S|`, that is `m + 1` for
`S = {k₀ = 0, k₁, …, k_m}`.  This has no hypothesis about Fourier series: on the grid the Fourier
transform of the physical-space equations is `IsSpectralSolution.modes`. -/
theorem spectral_linear_regime_rank {μ : Measure (Fin 3 → ℝ)} {g : (Fin 3 → ℝ) → Fin 3 → ℝ}
    {j0 : Fin 3 → ℝ} {κ : ZMod N → ℝ} {T : ℝ} {f : ℝ → ZMod N → (Fin 3 → ℝ) → ℝ}
    {E B : ℝ → VectorField (ZMod N)} (h : IsSpectralSolution μ g j0 κ T f E B)
    (hκ : ∀ k, κ (-k) = -κ k) (hκ0 : ∀ k, k ≠ 0 → κ k ≠ 0)
    (hμ : Integrable (fun v => (1 + ‖v‖) ^ 2 * ‖g v‖) μ) {S : Finset (ZMod N)} (hS : 0 ∈ S)
    (hf0 : ∀ k ∉ S, ∀ v, gridCoeff k (fun x => f 0 x v) = 0)
    (hB0 : ∀ k ∉ S, fieldCoeff k (B 0) = 0)
    (hE0 : ∀ k, k ≠ 0 → fieldCoeff k (E 0) =
      ((I / ((waveVec κ k ⬝ᵥ waveVec κ k : ℝ) : ℂ)) *
        ∫ v, gridCoeff k (fun x => f 0 x v) ∂μ) • toC (waveVec κ k))
    (f0 : (Fin 3 → ℝ) → ℂ) :
    ∀ t ∈ Icc (0 : ℝ) T,
      (∀ x v, (f t x v : ℂ) =
        ∑ k ∈ S, gridCoeff k (fun y => f t y v) * ZMod.stdAddChar (k * x)) ∧
      HasSepRankLE (fun x v => f0 v + (f t x v : ℂ)) S.card := by
  classical
  intro t ht
  have hzero : ∀ k, waveVec κ k = 0 → k = 0 := fun k h1 => by
    by_contra hk
    exact hκ0 k hk (congrFun h1 0)
  have hvan := unexcited_modes_vanish (ι := ZMod N) (κ := waveVec κ)
    (f := fun k t v => gridCoeff k fun x => f t x v) (E := fun k t => fieldCoeff k (E t))
    (B := fun k t => fieldCoeff k (B t)) (fun k => h.modes hκ hκ0 k) hμ
    (fun k hk => by rw [hzero k hk]; exact hS) hf0 hB0
    (fun k hk => hE0 k fun h1 => hk (by
      rw [h1]
      funext a
      have hκz : κ 0 = 0 := by
        have h2 := hκ 0
        rw [neg_zero] at h2
        linarith
      fin_cases a <;> simp [waveVec, hκz]))
  have hsum : ∀ x v, (f t x v : ℂ) =
      ∑ k ∈ S, gridCoeff k (fun y => f t y v) * ZMod.stdAddChar (k * x) := fun x v => by
    rw [sum_gridCoeff (fun y => f t y v) x]
    refine (Finset.sum_subset (Finset.subset_univ S) fun k _ hk => ?_).symm
    rw [(hvan k hk t ht).1 v, zero_mul]
  refine ⟨hsum, hasSepRankLE_of_sum hS (fun k x => ZMod.stdAddChar (k * x))
    (fun x => by simp) (fun k v => gridCoeff k fun y => f t y v) f0 fun x v => by rw [hsum]⟩

/-- Auxiliary for arXiv 1902.00424, Sec. 3.  Non-vacuity of `IsSpectralSolution` and of
`spectral_linear_regime_rank`: on any grid and for any odd symbol, a function `h` of `v` alone,
with zero fields, is a solution for a velocity measure concentrated at `v = 0`, where the current
vanishes; the initial data have the single mode `0`. -/
theorem exists_isSpectralSolution {κ : ZMod N → ℝ} (hκ : ∀ k, κ (-k) = -κ k) (T : ℝ)
    (h : (Fin 3 → ℝ) → ℝ) :
    IsSpectralSolution (Measure.dirac (0 : Fin 3 → ℝ)) (fun _ => 0) 0 κ T (fun _ _ v => h v)
      (fun _ => 0) (fun _ => 0) := by
  have hD : ∀ (a : Fin 3) (c : ℝ), spec1 κ a *ᵥ (fun _ => c) = 0 := fun a c => by
    fin_cases a
    · exact specMat_const hκ c
    · simp [spec1]
    · simp [spec1]
  have hcurl : curlD (spec1 κ) (0 : VectorField (ZMod N)) = 0 := by
    funext a x
    fin_cases a <;> simp [curlD]
  have hJ : ∀ a : Fin 3, ∫ v, v a * h v ∂Measure.dirac (0 : Fin 3 → ℝ) = 0 := fun a => by
    rw [integral_dirac]
    simp
  refine ⟨fun x v => ⟨continuousOn_const, fun t _ => ?_⟩, ⟨continuousOn_const, fun t _ => ?_⟩,
    ⟨continuousOn_const, fun t _ => ?_⟩, fun t _ x a => integrable_dirac (by simp)⟩
  · simpa [hD] using hasDerivWithinAt_const t (Ici t) (h v)
  · have h1 : curlD (spec1 κ) ((fun _ => 0 : ℝ → VectorField (ZMod N)) t) -
        (fun a _ => (0 : Fin 3 → ℝ) a) - (fun a _ => ∫ v, v a * h v ∂Measure.dirac 0) = 0 := by
      funext a x
      simp [hcurl, hJ]
    rw [h1]
    exact hasDerivWithinAt_const t (Ici t) (0 : VectorField (ZMod N))
  · have h1 : -curlD (spec1 κ) ((fun _ => 0 : ℝ → VectorField (ZMod N)) t) = 0 := by
      simp [hcurl]
    rw [h1]
    exact hasDerivWithinAt_const t (Ici t) (0 : VectorField (ZMod N))

end SpectralLinear

/-! ### The separation rank in the core vocabulary -/

section KineticCore

/-- **The separation rank through the core**: `HasSepRankLE u r` of this file is the core
`LeanDLRA.HasSepRankLE` over the ring `ℂ`. -/
theorem hasSepRankLE_iff_core {X Y : Type*} (u : X → Y → ℂ) (r : ℕ) :
    HasSepRankLE u r ↔ LeanDLRA.HasSepRankLE ℂ u r := Iff.rfl

/-- The bridge at nonzero data: `x y + 1` has separation rank at most `2` over `ℂ`. -/
example : HasSepRankLE (fun x y : ℂ => x * y + 1) 2 :=
  (hasSepRankLE_iff_core _ 2).2
    (LeanDLRA.HasSepRankLE.of_sum ![fun x => x, fun _ => 1] ![fun y => y, fun _ => 1]
      (fun x y => by simp [Fin.sum_univ_two]) (by simp))

end KineticCore

end LeanDLRA.Literature.P1902_00424
