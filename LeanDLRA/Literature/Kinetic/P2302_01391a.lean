import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Foundations.Localization
import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors

/-!
# arXiv 2302.01391: macro-micro decomposition for shallow water moment equations

Koellermeier, Krah and Kusch reduce the hyperbolic shallow water moment equations (HSWME) by
splitting the state into a macro part `U = (h, h u_m)` and a micro part `V = (h α₁, …, h α_N)`,
and applying POD-Galerkin or BUG to `V` only.  The paper is numerical and states no theorems.  This
module proves its structural claims for the discrete scheme itself: the transport matrix (11),
(14), the path-conservative Lax–Friedrichs scheme (22)–(25) of Appendix A on a periodic grid
`Fin Nx`, and the friction (12), (15)–(17), (21) with the implicit K-, L- and S-steps of
Sec. 6.2.2, all as concrete definitions, not as an abstract core.

Equation numbers are those of the arXiv v2 PDF (16 July 2024).  Many displays there carry no number;
they are cited by section and content.

## Main results

* **Decomposition and conservation (Secs. 2, 3.2, 4.1, 6.1, App. A).**  `fullStep_eq`: one step of
  the undecomposed scheme is the macro step plus the micro step.  `Afull_height_row`,
  `macroF_height` (local flux form), `totalMass_conserved`: the total mass is exactly constant for
  arbitrary micro states, hence for POD and BUG of every rank.  `macroF_congr`: the micro state
  reaches the macro step only through `α₁`.  `blockBasis_orthonormal`, `fromCols_mul_blockBasis`:
  the projector `Π = id ⊕ Π_micro` of the macro-micro reduction.
* **Consistency with the SWE (Secs. 2, 7.1, 8).**  `Aswe_fluxJacobian`, `swe_of_rank_eq_zero` (rank
  zero gives the SWE scheme and SWE friction), `tendsto_macroF_swe` (limit as `V → 0`).
* **Friction (Sec. 4.2).**  `frictionSource_eq`: Eq. (15) from Eq. (12).  `viscC_quad_nonneg`,
  `wDot_G₁`, `wDot_G₂`: dissipativity in the energy `M = diag(1 / (2 k + 1))`.  `Dmat_isUnit`:
  `D_j` is invertible for all `Δt ≥ 0`, which the paper uses without proof.  `backwardEuler_iff`:
  Eqs. (16) and (17) are equivalent.  `wDot_backwardEuler_le`: unconditional `M`-stability.
* **Friction in BUG form (Sec. 6.2.2).**  `fricField_row`, `friction_kStep_iff`,
  `friction_lStep_iff`, `friction_sStep_iff`: implicit Euler for the K-, L- and S-steps is
  the three implicit systems of Sec. 6.2.2.  `friction_lStep_existsUnique`: the L-step is always
  uniquely solvable.
* **Caveat for the Euclidean Galerkin steps.**  `reducedFriction_antidissipative`, `Khat_singular`,
  `friction_kStep_no_solution`: for an orthonormal `W`, every `N ≥ 2` and the paper's `ν = 10`,
  `λ = 1/1000` the reduced friction operator is positive and the implicit K-step system of
  Sec. 6.2.2 can be singular, because the friction is dissipative in `M`, not in the Euclidean
  norm.  The paper does not claim solvability, so this is a gap, not an error.  `KhatM_isUnit` is
  the repair: `M`-Galerkin matrices.
* **POD (Sec. 5.1).**  The error identity after Eq. (18) and the Eckart–Young–Mirsky optimality are
  already `LeanDLRA.EckartYoung.sq_norm_sub_truncation`, `norm_sub_truncation_le`, so they are not
  repeated.  New here: `pod_error`, `pod_optimal` for the snapshot matrix `V^POD`;
  `sq_norm_truncation`, `Ecum_eq` for the energy criterion `E_cum`.
* **BUG for the micro transport (Sec. 6.2.1).**  `microF_kStep`, `microF_lStep`, `microF_sStep`:
  the K-, L- and S-right-hand sides in terms of the reduced data, the displays of Sec. 6.2.1.
  `microF_isLipschitz`, `microBUG_global_error`: robust error bound with frozen macro state.

## False or inconsistent as printed

Checked in the arXiv v2 PDF, each with its proved replacement.

* The energy criterion `E_cum` of Sec. 5.1 has unsquared norms: `Ecum_printed_false`, corrected
  in `Ecum_eq`.
* The matrix `G₁` displayed after Eq. (15) has shifted indices: `G₁printed_singular` shows that
  the printed matrix is antidissipative.  `G₁` is the repair, derived from Eq. (12) in
  `frictionSource_eq`.  The display of `a_{i,j}` after Eq. (12), with `i = 0, …, N` as in
  Eq. (12), has the same shift.  That `G₁` is the true friction rests on the identification of
  `viscC` with `½ ∫₀¹ φ_k' φ_l'`, which is checked outside Lean (see below).
* The macro and micro transport updates at the end of Appendix A show `+ Δt / (2 Δx)`, and the
  second line of Eq. (25) shows `+ 1 / (2 Δx)`.  Eq. (24) expands to the minus sign, see
  `fullStep_eq`; the display of `[F_v]_j` in Sec. 6.2.1 has the minus sign too.
* The `Ṡ` display of the S-step in Sec. 6.2.1 mixes `Ṡ`, `S` and `Sᵀ`: the correct form is
  `microF_sStep`.  The last terms of the `L̇` and `Ṡ` displays show no `∑_j`; that is not an
  error, since the paper declares Einstein's summation convention there.  `microF_lStep` writes
  the sum.

## Differences from the paper and what is not covered

* The grid is periodic, as in the paper's smooth tests.  The macro friction is left arbitrary in
  `totalMass_conserved`, because the paper gives no formula for it and the result needs only that
  `h` stays fixed.
* Interface values are the averages `faceAvg` of `h`, `u_m`, `α₁`, as in the displays of
  `A_{j+1,uu}`, …, `A_{j+1,vv}` after Eq. (25).  Eq. (23) instead evaluates `A` at the average
  `(Q_j + Q_{j+1}) / 2` of the conservative variables, which gives other values of `u_m` and `α₁`.
  The display of `A_{j+1,uu}` leaves the interface value of `h` implicit; mass conservation
  depends on none of these choices.
* In `microF`, the coefficients `B`, `ub`, `ab` are parameters, since the paper does not fix the
  time level of `α₁` in `A_{j,vv}`; the K-, L- and S-identities hold for any such choice.
* `viscC` is a definition.  Its identification with `½ ∫₀¹ φ_k' φ_l'` for the polynomials (10) is
  not proved here (it was checked by exact integration outside Lean up to degree 6).  The Lean
  results use only its algebraic form.
* The cost claim `O(r² (N_x + N))` is an operation count, not a theorem; `microF_kStep` and its
  companions give the structure behind it.  The `O(r³ N³)` L-step cost is likewise not formalised.
* There is no error analysis of the coupled macro-micro scheme, and none in the paper.
  `microBUG_global_error` freezes `U`, and the normal-component bound `ε` is a hypothesis.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2302_01391

noncomputable section

/-! ### The transport matrix (Eqs. 11, 14) -/

section Model

variable {Nx N : ℕ}

/-- The block `A_uu` of Eq. (14). -/
def Auu (g h u a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; g * h - u ^ 2 - a ^ 2 / 3, 2 * u]

/-- The block `A_uv` of Eq. (14): only the entry `2 α₁ / 3` is non-zero. -/
def Auv [NeZero N] (a : ℝ) : Matrix (Fin 2) (Fin N) ℝ :=
  fun i k => if i = 1 ∧ k = 0 then 2 / 3 * a else 0

/-- The block `A_vu` of Eq. (14): rows `(-2 u α₁, 2 α₁)` and `(-2 α₁² / 3, 0)`, then zero. -/
def Avu (u a : ℝ) : Matrix (Fin N) (Fin 2) ℝ :=
  fun k l =>
    if k.val = 0 then (if l = 0 then -2 * u * a else 2 * a)
    else if k.val = 1 then (if l = 0 then -(2 / 3) * a ^ 2 else 0) else 0

/-- The constant tridiagonal matrix `𝐀` of Eq. (11) and Appendix A: for the moment `k = i + 1` the
superdiagonal entry is `(k + 2) / (2 k + 3)` and the subdiagonal entry is `(k - 1) / (2 k - 1)`. -/
def Acoup (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i l =>
    if l.val = i.val + 1 then ((i.val : ℝ) + 3) / (2 * i.val + 5)
    else if i.val = l.val + 1 then (i.val : ℝ) / (2 * i.val + 1) else 0

/-- The block `A_vv = α₁ 𝐀 + u_m I` of Eq. (14) and of `A_{j+1,vv}` in Appendix A. -/
def Avv (N : ℕ) (u a : ℝ) : Matrix (Fin N) (Fin N) ℝ := a • Acoup N + u • 1

/-- The full HSWME transport matrix `A(q)` of Eqs. (11), (14). -/
def Afull [NeZero N] (g h u a : ℝ) : Matrix (Fin 2 ⊕ Fin N) (Fin 2 ⊕ Fin N) ℝ :=
  Matrix.fromBlocks (Auu g h u a) (Auv a) (Avu u a) (Avv N u a)

/-- **Eq. (11), first row** (arXiv 2302.01391): the row of `A(q)` for the water height is
`(0, 1, 0, …, 0)`, whatever the state: the height equation `∂ₜ h + ∂ₓ (h u_m) = 0` does not see the
micro variables.  This is the reason for the mass conservation of the macro-micro scheme. -/
theorem Afull_height_row [NeZero N] (g h u a : ℝ) (y : Fin 2 ⊕ Fin N → ℝ) :
    (Afull g h u a *ᵥ y) (Sum.inl 0) = y (Sum.inl 1) := by
  simp [Afull, Matrix.mulVec, dotProduct, Auu, Auv, Fin.sum_univ_two]

/-! ### The path-conservative Lax–Friedrichs scheme on a periodic grid (App. A, Eqs. 22–25) -/

variable [NeZero Nx]

/-- The water height `h_j`. -/
def height (U : Matrix (Fin Nx) (Fin 2) ℝ) (j : Fin Nx) : ℝ := U j 0

/-- The mean velocity `u_{m,j} = (h u_m)_j / h_j`. -/
def velocity (U : Matrix (Fin Nx) (Fin 2) ℝ) (j : Fin Nx) : ℝ := U j 1 / U j 0

/-- The first moment `α_{1,j} = (h α₁)_j / h_j`. -/
def firstMoment [NeZero N] (U : Matrix (Fin Nx) (Fin 2) ℝ) (V : Matrix (Fin Nx) (Fin N) ℝ)
    (j : Fin Nx) : ℝ := V j 0 / U j 0

/-- Interface average `½ (f_{j-1} + f_j)`: the paper's matrix `A_j` lives on the interface
between the cells `j - 1` and `j`, see `Ã_{j,vv}` in Sec. 6.2.1 and `A_{j+1,vv}` in Appendix A. -/
def faceAvg (f : Fin Nx → ℝ) (j : Fin Nx) : ℝ := (f (j - 1) + f j) / 2

/-- The macro right-hand side `F_u(U, V)`, the first block row of Eq. (25) (whose Euler step is the
macro update at the end of Appendix A), with all interface values obtained by `faceAvg`. -/
def macroF [NeZero N] (g Δx Δt : ℝ) (U : Matrix (Fin Nx) (Fin 2) ℝ)
    (V : Matrix (Fin Nx) (Fin N) ℝ) : Matrix (Fin Nx) (Fin 2) ℝ :=
  let hb := faceAvg (height U)
  let ub := faceAvg (velocity U)
  let ab := faceAvg (firstMoment U V)
  fun j =>
    (1 / (2 * Δt)) • (U (j - 1) - (2 : ℝ) • U j + U (j + 1))
      - (1 / (2 * Δx)) • (Auu g (hb (j + 1)) (ub (j + 1)) (ab (j + 1)) *ᵥ (U (j + 1) - U j)
          + Auv (ab (j + 1)) *ᵥ (V (j + 1) - V j))
      - (1 / (2 * Δx)) • (Auu g (hb j) (ub j) (ab j) *ᵥ (U j - U (j - 1))
          + Auv (ab j) *ᵥ (V j - V (j - 1)))

/-- The micro right-hand side `F_v(U, V)` of Eq. (25) and Sec. 6.2.1, for given interface blocks
`B j = A_{j,vu}` and interface values `ub j`, `ab j` of `u_m`, `α₁` in `A_{j,vv} = ab_j 𝐀 + ub_j I`.
The paper does not fix the time level of `α₁` here, so these are parameters. -/
def microF (Δx Δt : ℝ) (B : Fin Nx → Matrix (Fin N) (Fin 2) ℝ) (ub ab : Fin Nx → ℝ)
    (U : Matrix (Fin Nx) (Fin 2) ℝ) (V : Matrix (Fin Nx) (Fin N) ℝ) :
    Matrix (Fin Nx) (Fin N) ℝ :=
  fun j =>
    (1 / (2 * Δt)) • (V (j - 1) - (2 : ℝ) • V j + V (j + 1))
      - (1 / (2 * Δx)) • (B (j + 1) *ᵥ (U (j + 1) - U j)
          + Avv N (ub (j + 1)) (ab (j + 1)) *ᵥ (V (j + 1) - V j))
      - (1 / (2 * Δx)) • (B j *ᵥ (U j - U (j - 1)) + Avv N (ub j) (ab j) *ᵥ (V j - V (j - 1)))

/-- One explicit Euler step of the undecomposed scheme, Eqs. (22)–(24), for `Q = [U V]`:
`Q_j⁺ = Q_j - (Δt/Δx) (A⁻_{j+1} (Q_{j+1} - Q_j) + A⁺_j (Q_j - Q_{j-1}))` with
`A^± = ½ (A ± (Δx/Δt) I)`. -/
def fullStep [NeZero N] (g Δx Δt : ℝ) (U : Matrix (Fin Nx) (Fin 2) ℝ)
    (V : Matrix (Fin Nx) (Fin N) ℝ) : Matrix (Fin Nx) (Fin 2 ⊕ Fin N) ℝ :=
  let Q := Matrix.fromCols U V
  let A := fun j => Afull (N := N) g (faceAvg (height U) j) (faceAvg (velocity U) j)
    (faceAvg (firstMoment U V) j)
  fun j =>
    Q j - (Δt / Δx) •
      (((1 / 2 : ℝ) • (A (j + 1) - (Δx / Δt) • (1 : Matrix _ _ ℝ))) *ᵥ (Q (j + 1) - Q j)
        + ((1 / 2 : ℝ) • (A j + (Δx / Δt) • (1 : Matrix _ _ ℝ))) *ᵥ (Q j - Q (j - 1)))

private lemma elim_sub {ι κ : Type*} (a b : ι → ℝ) (c d : κ → ℝ) :
    Sum.elim a c - Sum.elim b d = Sum.elim (a - b) (c - d) := by
  funext x
  cases x <;> rfl

private lemma Afull_mulVec_elim [NeZero N] (g h u a : ℝ) (x : Fin 2 → ℝ) (y : Fin N → ℝ) :
    Afull g h u a *ᵥ Sum.elim x y =
      Sum.elim (Auu g h u a *ᵥ x + Auv a *ᵥ y) (Avu u a *ᵥ x + Avv N u a *ᵥ y) := by
  simp [Afull, Matrix.fromBlocks_mulVec]

private lemma step_scalar {Δx Δt : ℝ} (hΔx : Δx ≠ 0) (hΔt : Δt ≠ 0) (y ym yp a₀ a₁ b₀ b₁ : ℝ) :
    y - Δt / Δx * (1 / 2 * (a₁ + b₁ - Δx / Δt * (yp - y)) + 1 / 2 * (a₀ + b₀ + Δx / Δt * (y - ym)))
      = y + Δt * (1 / (2 * Δt) * (ym - 2 * y + yp) - 1 / (2 * Δx) * (a₁ + b₁)
          - 1 / (2 * Δx) * (a₀ + b₀)) := by
  field_simp
  ring

/-- **The macro-micro decomposition introduces no error** (arXiv 2302.01391, Sec. 2, Eq. 24 and
the updates at the end of Appendix A): one step of the undecomposed scheme for `Q = [U V]` is
exactly the macro update in the first two columns and the micro update in the others, both from
time level `n`.  Solving them in sequence, with `Ũ` in the micro step (step 1b), is a splitting
that the paper itself says does introduce an error; no bound for that error is given here or
there.

The macro and micro updates at the end of Appendix A have a plus sign in front of `Δt / (2 Δx)`, and
Eq. (25) one in front of `1 / (2 Δx)`; expanding Eq. (24) gives the minus sign used here, which is
also the sign of `[F_v]_j` in Sec. 6.2.1. -/
theorem fullStep_eq [NeZero N] (g : ℝ) {Δx Δt : ℝ} (hΔx : Δx ≠ 0) (hΔt : Δt ≠ 0)
    (U : Matrix (Fin Nx) (Fin 2) ℝ) (V : Matrix (Fin Nx) (Fin N) ℝ) :
    fullStep g Δx Δt U V = Matrix.fromCols (U + Δt • macroF g Δx Δt U V)
      (V + Δt • microF Δx Δt (fun j => Avu (faceAvg (velocity U) j) (faceAvg (firstMoment U V) j))
        (faceAvg (velocity U)) (faceAvg (firstMoment U V)) U V) := by
  have hQ : ∀ i, Matrix.fromCols U V i = Sum.elim (U i) (V i) := fun _ => rfl
  funext j x
  rcases x with l | k
  · simp only [Matrix.fromCols_apply_inl, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    simp only [fullStep, hQ, elim_sub, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.add_mulVec,
      Matrix.one_mulVec, Afull_mulVec_elim, macroF, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Sum.elim_inl]
    exact step_scalar hΔx hΔt _ _ _ _ _ _ _
  · simp only [Matrix.fromCols_apply_inr, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    simp only [fullStep, hQ, elim_sub, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.add_mulVec,
      Matrix.one_mulVec, Afull_mulVec_elim, microF, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Sum.elim_inr]
    exact step_scalar hΔx hΔt _ _ _ _ _ _ _

/-! ### Mass conservation (Secs. 2, 3.2, 4.1, 6.1 and Appendix A) -/

private lemma Auu_mulVec_zero (g h u a : ℝ) (x : Fin 2 → ℝ) : (Auu g h u a *ᵥ x) 0 = x 1 := by
  simp [Auu, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private lemma Auu_mulVec_one (g h u a : ℝ) (x : Fin 2 → ℝ) :
    (Auu g h u a *ᵥ x) 1 = (g * h - u ^ 2 - a ^ 2 / 3) * x 0 + 2 * u * x 1 := by
  simp [Auu, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private lemma Auv_mulVec_zero [NeZero N] (a : ℝ) (y : Fin N → ℝ) : (Auv a *ᵥ y) 0 = 0 := by
  simp [Auv, Matrix.mulVec, dotProduct]

private lemma Auv_mulVec_one [NeZero N] (a : ℝ) (y : Fin N → ℝ) :
    (Auv a *ᵥ y) 1 = 2 / 3 * a * y 0 := by
  simp [Auv, Matrix.mulVec, dotProduct]

/-- The numerical mass flux through the interface `j`:
`½ ((h u_m)_{j-1} + (h u_m)_j) - (Δx / (2 Δt)) (h_j - h_{j-1})`. -/
def massFlux (Δx Δt : ℝ) (U : Matrix (Fin Nx) (Fin 2) ℝ) (j : Fin Nx) : ℝ :=
  (U (j - 1) 1 + U j 1) / 2 - Δx / (2 * Δt) * (U j 0 - U (j - 1) 0)

private lemma sum_shift_sub (f : Fin Nx → ℝ) : ∑ j, (f (j + 1) - f j) = 0 := by
  rw [Finset.sum_sub_distrib, sub_eq_zero]
  exact Equiv.sum_comp (Equiv.addRight (1 : Fin Nx)) f

/-- **Local conservation form of the height equation** (arXiv 2302.01391, Sec. 6.1, "ensures
local mass conservation"): the height row of the macro right-hand side is a difference of numerical
fluxes, whatever the micro state `V` is. -/
theorem macroF_height [NeZero N] (g : ℝ) {Δx Δt : ℝ} (hΔx : Δx ≠ 0) (hΔt : Δt ≠ 0)
    (U : Matrix (Fin Nx) (Fin 2) ℝ) (V : Matrix (Fin Nx) (Fin N) ℝ) (j : Fin Nx) :
    macroF g Δx Δt U V j 0 = -(1 / Δx) * (massFlux Δx Δt U (j + 1) - massFlux Δx Δt U j) := by
  simp only [macroF, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Auu_mulVec_zero,
    Auv_mulVec_zero, massFlux, add_sub_cancel_right]
  field_simp
  ring

/-- The total mass is unchanged by the macro right-hand side, whatever `V` is (arXiv 2302.01391,
Sec. 4.1, the summed form of `macroF_height`). -/
theorem sum_macroF_height [NeZero N] (g : ℝ) {Δx Δt : ℝ} (hΔx : Δx ≠ 0) (hΔt : Δt ≠ 0)
    (U : Matrix (Fin Nx) (Fin 2) ℝ) (V : Matrix (Fin Nx) (Fin N) ℝ) :
    ∑ j, macroF g Δx Δt U V j 0 = 0 := by
  simp_rw [macroF_height g hΔx hΔt]
  rw [← Finset.mul_sum, sum_shift_sub, mul_zero]

/-- **Exact mass conservation of the macro-micro scheme** (arXiv 2302.01391, Secs. 2, 3.2, 4.1,
6.1 and Appendix A; the paper's main structural claim, stated there without proof).  On a periodic
grid, let the macro transport (step 1a) be the explicit Euler step `Ũ = U + Δt F_u(U, V)` and let
the friction step leave the height unchanged (`h⁺ = h̃`, steps 2a, 2b).  Then the total mass
`∑_j h_j` is constant in time.

Nothing is assumed on the micro states `V n`: they can come from the full scheme, from POD-Galerkin
or from BUG, with any rank.  Nothing is assumed on the momentum update of the friction step either.
Contrast `fixedRankBUG_changes_mass` in `OpenProblems/Conservation/Part2b`: a BUG step on a matrix
state containing the conserved quantity changes the mass. -/
theorem totalMass_conserved [NeZero N] (g : ℝ) {Δx Δt : ℝ} (hΔx : Δx ≠ 0) (hΔt : Δt ≠ 0)
    {U Ut : ℕ → Matrix (Fin Nx) (Fin 2) ℝ} {V : ℕ → Matrix (Fin Nx) (Fin N) ℝ}
    (hmacro : ∀ n, Ut n = U n + Δt • macroF g Δx Δt (U n) (V n))
    (hfric : ∀ n j, U (n + 1) j 0 = Ut n j 0) (n : ℕ) :
    ∑ j, U n j 0 = ∑ j, U 0 j 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← ih]
    simp_rw [hfric n, hmacro n, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_macroF_height g hΔx hΔt, mul_zero, add_zero]

/-- **The micro state enters the macro dynamics only through `α₁`** (arXiv 2302.01391, remark after
Eq. 11): two micro states with the same first moment give the same macro right-hand side. -/
theorem macroF_congr [NeZero N] (g Δx Δt : ℝ) (U : Matrix (Fin Nx) (Fin 2) ℝ)
    {V V' : Matrix (Fin Nx) (Fin N) ℝ} (h : ∀ j, V j 0 = V' j 0) :
    macroF g Δx Δt U V = macroF g Δx Δt U V' := by
  have ha : firstMoment U V = firstMoment U V' := by
    funext j
    simp only [firstMoment, h]
  funext j l
  fin_cases l
  · simp only [macroF, Fin.zero_eta, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Auu_mulVec_zero, Auv_mulVec_zero]
  · simp only [macroF, Fin.mk_one, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Auu_mulVec_one, Auv_mulVec_one, ha, h]

/-! ### The macro-micro projector -/

/-- The block basis `W̃ = I₂ ⊕ W` of the macro-micro reduction: the macro columns are kept and the
micro columns are projected on the range of `W`. -/
def blockBasis {r : ℕ} (W : Matrix (Fin N) (Fin r) ℝ) :
    Matrix (Fin 2 ⊕ Fin N) (Fin 2 ⊕ Fin r) ℝ :=
  Matrix.fromBlocks 1 0 0 W

/-- `W̃` has orthonormal columns if `W` has, so `Π = W̃ W̃ᵀ` is a `rightProj` of the library
(arXiv 2302.01391, Secs. 2, 6.1, header note `Π = id ⊕ Π_micro`). -/
theorem blockBasis_orthonormal {r : ℕ} {W : Matrix (Fin N) (Fin r) ℝ} (hW : Wᵀ * W = 1) :
    (blockBasis W)ᵀ * blockBasis W = 1 := by
  simp [blockBasis, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, hW,
    Matrix.fromBlocks_one]

omit [NeZero Nx] in
/-- **Only the micro moments are reduced** (arXiv 2302.01391, Secs. 2, 6.1; header note
`Π = id ⊕ Π_micro`): the right projector of the block basis leaves `U` alone and acts as
`V ↦ V W Wᵀ` on the micro columns.  So every invariant supported on the macro columns, such as the
total mass, is unchanged by `Π`: this is the projector form of `totalMass_conserved`. -/
theorem fromCols_mul_blockBasis {r : ℕ} (U : Matrix (Fin Nx) (Fin 2) ℝ)
    (V : Matrix (Fin Nx) (Fin N) ℝ) (W : Matrix (Fin N) (Fin r) ℝ) :
    Matrix.fromCols U V * (blockBasis W * (blockBasis W)ᵀ) = Matrix.fromCols U (V * (W * Wᵀ)) := by
  simp [blockBasis, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromCols_mul_fromBlocks]

/-! ### Consistency with the shallow water equations (Secs. 2, 7.1, 8) -/

/-- The transport matrix of the shallow water equations (8) in the variables `(h, h u_m)`. -/
def Aswe (g h u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; g * h - u ^ 2, 2 * u]

/-- **`Aswe` is the flux Jacobian of Eq. (8)** (arXiv 2302.01391, Eq. 8): along any differentiable
`x ↦ (h, m)` with `h ≠ 0`, `Aswe (h, m / h) (h', m')` is the derivative of the flux
`(m, m² / h + g h² / 2)`.  So `∂ₜ q + Aswe ∂ₓ q = 0` is the transport part of the conservative
system (8). -/
theorem Aswe_fluxJacobian (g : ℝ) {h m : ℝ → ℝ} {h' m' x : ℝ} (hh : HasDerivAt h h' x)
    (hm : HasDerivAt m m' x) (h0 : h x ≠ 0) :
    HasDerivAt m ((Aswe g (h x) (m x / h x) *ᵥ ![h', m']) 0) x ∧
      HasDerivAt (fun y => m y ^ 2 / h y + g * h y ^ 2 / 2)
        ((Aswe g (h x) (m x / h x) *ᵥ ![h', m']) 1) x := by
  have h1 : (Aswe g (h x) (m x / h x) *ᵥ ![h', m']) 0 = m' := by
    simp [Aswe, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h2 : (Aswe g (h x) (m x / h x) *ᵥ ![h', m']) 1
      = (g * h x - (m x / h x) ^ 2) * h' + 2 * (m x / h x) * m' := by
    simp [Aswe, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [h1, h2]
  refine ⟨hm, ?_⟩
  have key := ((hm.fun_pow 2).fun_div hh h0).fun_add (((hh.fun_pow 2).const_mul g).div_const 2)
  convert key using 1
  field_simp
  ring

/-- The Lax–Friedrichs scheme (same stencil as `macroF`) for the shallow water equations (8). -/
def sweF (g Δx Δt : ℝ) (U : Matrix (Fin Nx) (Fin 2) ℝ) : Matrix (Fin Nx) (Fin 2) ℝ :=
  let hb := faceAvg (height U)
  let ub := faceAvg (velocity U)
  fun j =>
    (1 / (2 * Δt)) • (U (j - 1) - (2 : ℝ) • U j + U (j + 1))
      - (1 / (2 * Δx)) • (Aswe g (hb (j + 1)) (ub (j + 1)) *ᵥ (U (j + 1) - U j))
      - (1 / (2 * Δx)) • (Aswe g (hb j) (ub j) *ᵥ (U j - U (j - 1)))

private lemma Auu_zero (g h u : ℝ) : Auu g h u 0 = Aswe g h u := by
  simp [Auu, Aswe]

private lemma Auv_zero [NeZero N] : (Auv 0 : Matrix (Fin 2) (Fin N) ℝ) = 0 := by
  ext i k
  simp [Auv]

/-- The macro scheme with vanishing micro part is the SWE scheme (arXiv 2302.01391, Secs. 2, 8). -/
theorem macroF_zero [NeZero N] (g Δx Δt : ℝ) (U : Matrix (Fin Nx) (Fin 2) ℝ) :
    macroF g Δx Δt U (0 : Matrix (Fin Nx) (Fin N) ℝ) = sweF g Δx Δt U := by
  have ha : firstMoment U (0 : Matrix (Fin Nx) (Fin N) ℝ) = 0 := by
    funext j
    simp [firstMoment]
  have hb : faceAvg (0 : Fin Nx → ℝ) = 0 := by
    funext j
    simp [faceAvg]
  funext j l
  simp only [macroF, sweF, ha, hb, Pi.zero_apply, Auu_zero, Auv_zero, Matrix.zero_mulVec, add_zero]

/-- **Consistency with the SWE at rank zero** (arXiv 2302.01391, Secs. 7.1, 8: "the decomposition
allows to recover the naive SWE for vanishing truncation rank").  If the micro state has rank `0`,
as every `V = X S Wᵀ` with `r = 0` does, the macro transport is the SWE scheme and the friction
acting on the momentum (Eq. 12 with `i = 0`, where `a_{0,j} = 0`) is the SWE friction `-(ν / λ) u_m`
of Eq. (8). -/
theorem swe_of_rank_eq_zero [NeZero N] (g Δx Δt ν lam : ℝ) (U : Matrix (Fin Nx) (Fin 2) ℝ)
    {V : Matrix (Fin Nx) (Fin N) ℝ} (hV : V.rank = 0) :
    macroF g Δx Δt U V = sweF g Δx Δt U ∧
      ∀ j, -(ν / lam) * (velocity U j + ∑ k, V j k / U j 0) = -(ν / lam) * velocity U j := by
  have hV0 : V = 0 := by
    have h1 : LinearMap.range V.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp hV
    have h2 : V.mulVecLin = 0 := LinearMap.range_eq_bot.mp h1
    ext j k
    have h3 := congrFun (congrArg (fun T => T (Pi.single k 1)) h2) j
    simpa using h3
  subst hV0
  exact ⟨macroF_zero g Δx Δt U, fun j => by simp⟩

/-- The macro right-hand side depends continuously on the micro state (arXiv 2302.01391, Sec. 2,
the regularity behind `tendsto_macroF_swe`). -/
theorem continuous_macroF [NeZero N] (g Δx Δt : ℝ) (U : Matrix (Fin Nx) (Fin 2) ℝ) :
    Continuous (macroF g Δx Δt U : Matrix (Fin Nx) (Fin N) ℝ → _) := by
  have hV : ∀ i k, Continuous fun V : Matrix (Fin Nx) (Fin N) ℝ => V i k :=
    fun i k => continuous_id.matrix_elem i k
  have ha : ∀ j, Continuous fun V : Matrix (Fin Nx) (Fin N) ℝ =>
      faceAvg (firstMoment U V) j := fun j => by
    simp only [faceAvg, firstMoment]
    exact (((hV _ _).div_const _).add ((hV _ _).div_const _)).div_const _
  refine continuous_matrix fun j l => ?_
  fin_cases l
  · simp only [macroF, Fin.zero_eta, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Auu_mulVec_zero, Auv_mulVec_zero]
    exact continuous_const
  · simp only [macroF, Fin.mk_one, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Auu_mulVec_one, Auv_mulVec_one]
    have h1 := ha (j + 1)
    have h2 := ha j
    have h3 := hV (j + 1) 0
    have h4 := hV j 0
    have h5 := hV (j - 1) 0
    fun_prop

/-- **Consistency with the SWE as the micro part vanishes** (arXiv 2302.01391, Sec. 2: consistency
"with the SWE when the microscopic part tends to zero"): as `V → 0`, the macro right-hand side tends
to the SWE right-hand side. -/
theorem tendsto_macroF_swe [NeZero N] (g Δx Δt : ℝ) (U : Matrix (Fin Nx) (Fin 2) ℝ) :
    Tendsto (macroF g Δx Δt U : Matrix (Fin Nx) (Fin N) ℝ → _) (𝓝 0) (𝓝 (sweF g Δx Δt U)) := by
  have h := (continuous_macroF (N := N) g Δx Δt U).tendsto 0
  rwa [macroF_zero] at h

end Model

/-! ### The friction step (Eqs. 12, 15–17) -/

section Friction

variable {N : ℕ}

/-- `2 k + 1` for the moment `k = i + 1`.  Its inverse is `∫₀¹ φ_k²`. -/
def oddW (i : Fin N) : ℝ := 2 * (i : ℝ) + 3

private lemma oddW_pos (i : Fin N) : 0 < oddW i := by
  unfold oddW
  positivity

/-- The matrix `c_{kl} = min(k, l) (min(k, l) + 1)` for `k + l` even, `0` otherwise, for the moments
`k = i + 1`, `l = j + 1`: `½ ∫₀¹ φ_k' φ_l'` for the Legendre polynomials of Eq. (10). -/
def viscC (i j : Fin N) : ℝ :=
  if Even (i.val + j.val) then
    (((min i.val j.val : ℕ) : ℝ) + 1) * (((min i.val j.val : ℕ) : ℝ) + 2) else 0

/-- The viscous friction matrix `G₁`, with entries `-2 ν (2 k + 1) c_{kl}`.  This is the `G₁`
displayed after Eq. (15), with the indices of Eq. (12) and its `a_{i,j}` repaired, see
`frictionSource_eq` and `G₁printed`. -/
def G₁ (N : ℕ) (ν : ℝ) : Matrix (Fin N) (Fin N) ℝ := fun i j => -2 * ν * oddW i * viscC i j

/-- The vector `g_ν` with entries `-(ν / λ) (2 k + 1)` of Sec. 4.2. -/
def gv (N : ℕ) (ν lam : ℝ) : Fin N → ℝ := fun i => -(ν / lam) * oddW i

/-- The bottom friction matrix `G₂ = g_ν 𝟙ᵀ`. -/
def G₂ (N : ℕ) (ν lam : ℝ) : Matrix (Fin N) (Fin N) ℝ := Matrix.vecMulVec (gv N ν lam) fun _ => 1

/-- The friction source of Eq. (12) for the moments `k = i + 1 ≥ 1`, with `a_{kl} = c_{kl} / 2`.

The display of `a_{i,j}` after Eq. (12) has `min(i - 1, j)` and "`i + j` odd", which is right only
if its `i` is the moment index plus one, while Eq. (12) runs over `i = 0, …, N`.  With that shift
it is the `a_{kl}` used here, and `c_{kl} = ½ ∫₀¹ φ_k' φ_l'`. -/
def frictionSource (ν lam h u : ℝ) (α : Fin N → ℝ) : Fin N → ℝ := fun i =>
  -(ν / lam) * oddW i * (u + ∑ j, α j) - ν / h * 4 * oddW i * ∑ j, viscC i j / 2 * α j

private lemma G₁_mulVec (ν : ℝ) (x : Fin N → ℝ) (i : Fin N) :
    (G₁ N ν *ᵥ x) i = -2 * ν * oddW i * ∑ j, viscC i j * x j := by
  simp only [Matrix.mulVec, dotProduct, G₁, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

private lemma G₂_mulVec (ν lam : ℝ) (x : Fin N → ℝ) (i : Fin N) :
    (G₂ N ν lam *ᵥ x) i = gv N ν lam i * ∑ j, x j := by
  simp [Matrix.mulVec, dotProduct, G₂, Matrix.vecMulVec_apply, Finset.mul_sum]

/-- **Eq. (15) from Eq. (12)** (arXiv 2302.01391, Sec. 4.2): for `V = h α`, the friction source is
`h⁻² G₁ V + h⁻¹ G₂ V + u_m g_ν`.

This pins down `G₁`.  The `G₁` printed after Eq. (15) is not the matrix of Eq. (12): see
`G₁printed`. -/
theorem frictionSource_eq (ν lam u : ℝ) {h : ℝ} (hh : h ≠ 0) (α : Fin N → ℝ) :
    frictionSource ν lam h u α =
      (1 / h ^ 2) • (G₁ N ν *ᵥ (h • α)) + (1 / h) • (G₂ N ν lam *ᵥ (h • α)) + u • gv N ν lam := by
  funext i
  have e1 : ∑ j, viscC i j / 2 * α j = (∑ j, viscC i j * α j) / 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∑ j, viscC i j * (h * α j) = h * ∑ j, viscC i j * α j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e3 : ∑ j, h * α j = h * ∑ j, α j := by
    rw [Finset.mul_sum]
  simp only [frictionSource, Pi.add_apply, Pi.smul_apply, smul_eq_mul, G₁_mulVec, G₂_mulVec, gv,
    e1, e2, e3]
  field_simp
  ring

/-! The matrix `c` is positive semidefinite, with the explicit factorisation
`c_{kl} = ∑_{ℓ ≤ min(k, l), ℓ ≡ k ≡ l} (4 ℓ + 2)` (zero-based `ℓ`). -/

private def chi (l i : ℕ) : ℝ := if l ≤ i ∧ Even (i + l) then 1 else 0

private lemma sum_parity (m : ℕ) :
    ∑ l ∈ range (m + 1), (if Even (m + l) then 4 * (l : ℝ) + 2 else 0)
      = ((m : ℝ) + 1) * ((m : ℝ) + 2) := by
  induction m using Nat.twoStepInduction with
  | zero => simp
  | one =>
    norm_num [Finset.sum_range_succ, Nat.even_add_one]
  | more m ih _ =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have h1 : ∀ l ∈ range (m + 1), (if Even (m + 2 + l) then 4 * (l : ℝ) + 2 else 0)
        = if Even (m + l) then 4 * (l : ℝ) + 2 else 0 := by
      intro l _
      have : Even (m + 2 + l) ↔ Even (m + l) := by
        rw [show m + 2 + l = m + l + 2 by ring]
        simp [Nat.even_add]
      simp only [this]
    rw [Finset.sum_congr rfl h1, ih]
    have h2 : Even (m + 2 + (m + 2)) := ⟨m + 2, rfl⟩
    have h3 : ¬ Even (m + 2 + (m + 1)) := by
      rw [Nat.not_even_iff_odd]
      exact ⟨m + 1, by ring⟩
    rw [ite_eq_right h3, ite_eq_left h2]
    push_cast
    ring

private lemma viscC_eq_sum (i j : Fin N) :
    viscC i j = ∑ l : Fin N, (4 * ((l : ℕ) : ℝ) + 2) * chi l i * chi l j := by
  rw [Fin.sum_univ_eq_sum_range (fun l => (4 * (l : ℝ) + 2) * chi l i * chi l j) N]
  by_cases hE : Even (i.val + j.val)
  · set m := min i.val j.val with hm
    have hmN : m < N := lt_of_le_of_lt (min_le_left _ _) i.isLt
    have hi : ∀ l, Even (i.val + l) ↔ Even (m + l) := by
      intro l
      rcases le_total i.val j.val with h | h
      · rw [hm, min_eq_left h]
      · rw [hm, min_eq_right h]
        have := Nat.even_add.1 hE
        simp only [Nat.even_add, this]
    have hj : ∀ l, Even (j.val + l) ↔ Even (m + l) := by
      intro l
      rcases le_total i.val j.val with h | h
      · rw [hm, min_eq_left h]
        have := Nat.even_add.1 hE
        simp only [Nat.even_add, this]
      · rw [hm, min_eq_right h]
    have term : ∀ l : ℕ, (4 * (l : ℝ) + 2) * chi l i * chi l j =
        if l ≤ m then (if Even (m + l) then 4 * (l : ℝ) + 2 else 0) else 0 := by
      intro l
      have hle : l ≤ m ↔ l ≤ i.val ∧ l ≤ j.val := by
        rw [hm]
        exact le_min_iff
      simp only [chi, hi, hj, hle]
      by_cases h1 : l ≤ i.val <;> by_cases h2 : l ≤ j.val <;> by_cases h3 : Even (m + l) <;>
        simp [h1, h2, h3]
    rw [Finset.sum_congr rfl fun l _ => term l]
    have hsub : range (m + 1) ⊆ range N := by
      intro l hl
      rw [Finset.mem_range] at hl ⊢
      omega
    rw [← Finset.sum_subset hsub]
    · rw [Finset.sum_congr rfl fun l hl => ite_eq_left (by rw [Finset.mem_range] at hl; omega),
        sum_parity]
      simp [viscC, hE, hm]
    · intro l _ hl
      rw [Finset.mem_range] at hl
      rw [ite_eq_right (by omega)]
  · have hz : viscC i j = 0 := by simp [viscC, hE]
    rw [hz]
    symm
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases h1 : Even (i.val + l)
    · have h2 : ¬ Even (j.val + l) := by
        intro h2
        apply hE
        have := Nat.even_add.1 h1
        have := Nat.even_add.1 h2
        rw [Nat.even_add]
        tauto
      simp [chi, h2]
    · simp [chi, h1]

/-- **The viscous friction form is positive semidefinite** (arXiv 2302.01391, implicit in Sec. 4.2;
not stated there). -/
theorem viscC_quad_nonneg (x : Fin N → ℝ) : 0 ≤ ∑ i, ∑ j, viscC i j * x i * x j := by
  have h : ∑ i, ∑ j, viscC i j * x i * x j
      = ∑ l : Fin N, (4 * ((l : ℕ) : ℝ) + 2) * (∑ i : Fin N, chi l i * x i) ^ 2 := by
    calc ∑ i, ∑ j, viscC i j * x i * x j
        = ∑ i : Fin N, ∑ j : Fin N, ∑ l : Fin N,
            (4 * ((l : ℕ) : ℝ) + 2) * (chi l i * x i) * (chi l j * x j) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [viscC_eq_sum, Finset.sum_mul, Finset.sum_mul]
          exact Finset.sum_congr rfl fun l _ => by ring
      _ = ∑ i : Fin N, ∑ l : Fin N, ∑ j : Fin N,
            (4 * ((l : ℕ) : ℝ) + 2) * (chi l i * x i) * (chi l j * x j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ l : Fin N, ∑ i : Fin N, ∑ j : Fin N,
            (4 * ((l : ℕ) : ℝ) + 2) * (chi l i * x i) * (chi l j * x j) :=
          Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
  rw [h]
  exact Finset.sum_nonneg fun l _ => by positivity

/-- The weighted inner product `xᵀ M y` with `M = diag(1 / (2 k + 1))`, the Gram matrix of the
Legendre polynomials `φ_k`: this is the energy in which the friction is dissipative. -/
def wDot (x y : Fin N → ℝ) : ℝ := ∑ i, x i * y i / oddW i

private lemma wDot_self_nonneg (x : Fin N → ℝ) : 0 ≤ wDot x x :=
  Finset.sum_nonneg fun i _ => div_nonneg (mul_self_nonneg _) (oddW_pos i).le

private lemma eq_zero_of_wDot_self_le {x : Fin N → ℝ} (h : wDot x x ≤ 0) : x = 0 := by
  have h0 : wDot x x = 0 := le_antisymm h (wDot_self_nonneg x)
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
    div_nonneg (mul_self_nonneg (x i)) (oddW_pos i).le).1 h0
  funext i
  have h2 := h1 i (Finset.mem_univ i)
  rw [div_eq_zero_iff] at h2
  rcases h2 with h2 | h2
  · simpa using h2
  · exact absurd h2 (oddW_pos i).ne'

private lemma wDot_sub_right (x y z : Fin N → ℝ) : wDot x (y - z) = wDot x y - wDot x z := by
  simp only [wDot, ← Finset.sum_sub_distrib, Pi.sub_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

private lemma wDot_smul_right (c : ℝ) (x y : Fin N → ℝ) : wDot x (c • y) = c * wDot x y := by
  simp only [wDot, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `xᵀ M G₁ x = -2 ν ∑ c_{kl} x_k x_l` (arXiv 2302.01391, `G₁` after Eq. 15 with repaired indices;
the energy form is not in the paper). -/
theorem wDot_G₁ (ν : ℝ) (x : Fin N → ℝ) :
    wDot x (G₁ N ν *ᵥ x) = -2 * ν * ∑ i, ∑ j, viscC i j * x i * x j := by
  simp only [wDot, G₁_mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hw := (oddW_pos i).ne'
  field_simp
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- `xᵀ M G₂ x = -(ν / λ) (∑ x_k)²` (arXiv 2302.01391, Sec. 4.2, `G₂ = g_ν 𝟙ᵀ`; the energy form is
not in the paper). -/
theorem wDot_G₂ (ν lam : ℝ) (x : Fin N → ℝ) :
    wDot x (G₂ N ν lam *ᵥ x) = -(ν / lam) * (∑ i, x i) ^ 2 := by
  have : ∀ i, x i * (G₂ N ν lam *ᵥ x) i / oddW i = -(ν / lam) * (x i * ∑ j, x j) := by
    intro i
    have hw := (oddW_pos i).ne'
    rw [G₂_mulVec, gv]
    field_simp
  simp only [wDot, this]
  rw [← Finset.mul_sum, ← Finset.sum_mul, sq]

/-- `D_j = I - (Δt / h²) G₁ - (Δt / h) G₂`, displayed between Eqs. (16) and (17). -/
def Dmat (ν lam Δt h : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  1 - (Δt / h ^ 2) • G₁ N ν - (Δt / h) • G₂ N ν lam

private lemma Dmat_mulVec (ν lam Δt h : ℝ) (x : Fin N → ℝ) :
    Dmat ν lam Δt h *ᵥ x = x - (Δt / h ^ 2) • (G₁ N ν *ᵥ x) - (Δt / h) • (G₂ N ν lam *ᵥ x) := by
  simp [Dmat, Matrix.sub_mulVec, Matrix.smul_mulVec]

/-- The energy inequality behind `Dmat_isUnit` and `wDot_backwardEuler_le`: `xᵀ M x ≤ xᵀ M D x`
(arXiv 2302.01391, `D_j` before Eq. 17; not in the paper). -/
theorem wDot_le_wDot_Dmat {ν lam Δt h : ℝ} (hν : 0 ≤ ν) (hlam : 0 < lam) (hΔt : 0 ≤ Δt)
    (hh : 0 < h) (x : Fin N → ℝ) : wDot x x ≤ wDot x (Dmat ν lam Δt h *ᵥ x) := by
  rw [Dmat_mulVec, wDot_sub_right, wDot_sub_right, wDot_smul_right, wDot_smul_right, wDot_G₁,
    wDot_G₂]
  have h1 := viscC_quad_nonneg x
  have h2 : 0 ≤ Δt / h ^ 2 * (2 * ν * ∑ i, ∑ j, viscC i j * x i * x j) := by positivity
  have h3 : 0 ≤ Δt / h * (ν / lam * (∑ i, x i) ^ 2) := by positivity
  nlinarith

/-- **`D_j` is invertible for every time step** (arXiv 2302.01391, Eq. 17: the paper inverts `D_j`
and notes that the inverse can be precomputed, without proving that it exists).  For `ν ≥ 0`,
`λ > 0`, `h > 0`, `Δt ≥ 0`. -/
theorem Dmat_isUnit {ν lam Δt h : ℝ} (hν : 0 ≤ ν) (hlam : 0 < lam) (hΔt : 0 ≤ Δt) (hh : 0 < h) :
    IsUnit (Dmat (N := N) ν lam Δt h) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have hz : Dmat (N := N) ν lam Δt h *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, sub_eq_zero]
    exact hxy
  have h1 := wDot_le_wDot_Dmat hν hlam hΔt hh (x - y)
  rw [hz] at h1
  have h2 : wDot (x - y) 0 = 0 := by simp [wDot]
  rw [h2] at h1
  exact sub_eq_zero.1 (eq_zero_of_wDot_self_le h1)

/-- **Backward Euler for the micro friction, Eqs. (16)–(17)** (arXiv 2302.01391, Sec. 4.2):
the implicit equation (16) has exactly the solution (17),
`V⁺ = D⁻¹ (V + Δt u_m g_ν)`, for every `Δt ≥ 0`, `h > 0`, `ν ≥ 0`, `λ > 0`.
`D` does not depend on `u_m` or the `α_i`, which is the paper's precomputation remark. -/
theorem backwardEuler_iff {ν lam Δt h : ℝ} (hν : 0 ≤ ν) (hlam : 0 < lam) (hΔt : 0 ≤ Δt)
    (hh : 0 < h) (u : ℝ) (V V₁ : Fin N → ℝ) :
    V₁ = V + Δt • ((1 / h ^ 2) • (G₁ N ν *ᵥ V₁) + (1 / h) • (G₂ N ν lam *ᵥ V₁) + u • gv N ν lam) ↔
      V₁ = (Dmat ν lam Δt h)⁻¹ *ᵥ (V + (Δt * u) • gv N ν lam) := by
  have hD := Dmat_isUnit (N := N) hν hlam hΔt hh
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hD
  have step : V₁ = V + Δt • ((1 / h ^ 2) • (G₁ N ν *ᵥ V₁) + (1 / h) • (G₂ N ν lam *ᵥ V₁)
      + u • gv N ν lam) ↔ Dmat ν lam Δt h *ᵥ V₁ = V + (Δt * u) • gv N ν lam := by
    rw [Dmat_mulVec]
    have e1 : Δt / h ^ 2 = Δt * (1 / h ^ 2) := by ring
    have e2 : Δt / h = Δt * (1 / h) := by ring
    rw [e1, e2]
    constructor
    · intro h1
      funext i
      have := congrFun h1 i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
      linarith
    · intro h1
      funext i
      have := congrFun h1 i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
      linarith
  rw [step]
  constructor
  · intro h1
    rw [← h1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  · intro h1
    rw [h1, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

/-- **Unconditional stability of the micro friction step** (arXiv 2302.01391, Sec. 4.2 uses the
implicit step "to overcome stability issues" and proves nothing): the solution of (16) satisfies
`‖V⁺‖_M ≤ ‖V + Δt u_m g_ν‖_M` in the energy `M = diag(1 / (2 k + 1))`, for every `Δt ≥ 0`.  In this
norm friction is contractive; its Euclidean Galerkin projection need not be, see
`reducedFriction_antidissipative`. -/
theorem wDot_backwardEuler_le {ν lam Δt h : ℝ} (hν : 0 ≤ ν) (hlam : 0 < lam) (hΔt : 0 ≤ Δt)
    (hh : 0 < h) {x b : Fin N → ℝ} (hx : Dmat ν lam Δt h *ᵥ x = b) : wDot x x ≤ wDot b b := by
  have h1 := wDot_le_wDot_Dmat hν hlam hΔt hh x
  rw [hx] at h1
  have h2 := wDot_self_nonneg (x - b)
  have h3 : wDot (x - b) (x - b) = wDot x x - 2 * wDot x b + wDot b b := by
    simp only [wDot, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum,
      Pi.sub_apply]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith

/-- The matrix `G₁` displayed after Eq. (15), **as printed**, with `i, j ∈ {1, …, N}`: the entry is
`-2 ν (2 (i - 1) + 1) min(i, j) (min(i, j) + 1)` if `i + 1 + j` is even, else `0`. -/
def G₁printed (N : ℕ) (ν : ℝ) : Matrix (Fin N) (Fin N) ℝ := fun i j =>
  if Even ((i.val + 1) + 1 + (j.val + 1)) then
    -2 * ν * (2 * (i.val : ℝ) + 1) * ((min (i.val + 1) (j.val + 1) : ℕ) : ℝ)
      * (((min (i.val + 1) (j.val + 1) : ℕ) : ℝ) + 1) else 0

/-- **The `G₁` printed after Eq. (15) is not the friction matrix** (arXiv 2302.01391, Sec. 4.2).
For two moments and every `ν > 0`, `I - Δt G₁printed` is singular at `Δt = √3 / (12 ν)`, so the
printed matrix has the positive eigenvalue `4 √3 ν`, while the true matrix `G₁` is dissipative
(`Dmat_isUnit`).  The printed indices are shifted against Eq. (12) and its `a_{i,j}`: `i` is the
moment index plus one, and `min(i, j)` must be `min(i - 1, j)`.  With this repair it is `G₁`. -/
theorem G₁printed_singular {ν : ℝ} (hν : 0 < ν) :
    ∃ Δt : ℝ, 0 < Δt ∧ (1 - Δt • G₁printed 2 ν).det = 0 := by
  have h00 : G₁printed 2 ν 0 0 = 0 := by simp [G₁printed, Nat.even_iff]
  have h11 : G₁printed 2 ν 1 1 = 0 := by simp [G₁printed, Nat.even_iff]
  have h01 : G₁printed 2 ν 0 1 = -4 * ν := by
    norm_num [G₁printed, Nat.even_iff]
    ring
  have h10 : G₁printed 2 ν 1 0 = -12 * ν := by
    norm_num [G₁printed, Nat.even_iff]
    ring
  refine ⟨√3 / (12 * ν), by positivity, ?_⟩
  rw [Matrix.det_fin_two]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, h00, h01, h10, h11,
    Matrix.one_apply_eq, Matrix.one_apply_ne (zero_ne_one (α := Fin 2)),
    Matrix.one_apply_ne (one_ne_zero (α := Fin 2))]
  have key : √3 / (12 * ν) * ν = √3 / 12 := by field_simp
  have e : (1 - √3 / (12 * ν) * 0) * (1 - √3 / (12 * ν) * 0)
      - (0 - √3 / (12 * ν) * (-4 * ν)) * (0 - √3 / (12 * ν) * (-12 * ν))
      = 1 - 48 * (√3 / (12 * ν) * ν) ^ 2 := by ring
  rw [e, key, div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

end Friction

/-! ### The friction step in BUG form (Sec. 6.2.2, Eq. 21) -/

section ReducedFriction

variable {Nx N r : ℕ}

/-- The friction field of Eq. (21): `h⁻² V G₁ᵀ + h⁻¹ V G₂ᵀ + u_m g_νᵀ`, with `h⁻²`, `h⁻¹` diagonal
and `u_m` a column vector (the paper calls it diagonal, but only the vector makes `u_m g_νᵀ`
well-typed). -/
def fricField (ν lam : ℝ) (h u : Fin Nx → ℝ) (V : Matrix (Fin Nx) (Fin N) ℝ) :
    Matrix (Fin Nx) (Fin N) ℝ :=
  Matrix.diagonal (fun j => (h j)⁻¹ ^ 2) * V * (G₁ N ν)ᵀ
    + Matrix.diagonal (fun j => (h j)⁻¹) * V * (G₂ N ν lam)ᵀ
    + Matrix.vecMulVec u (gv N ν lam)

private lemma row_diagonal_mul {ι : Type*} [Fintype ι] (d : Fin Nx → ℝ)
    (K : Matrix (Fin Nx) ι ℝ) (G : Matrix ι ι ℝ) (j : Fin Nx) :
    (Matrix.diagonal d * K * Gᵀ) j = d j • (G *ᵥ K j) := by
  funext k
  rw [Matrix.mul_apply]
  simp only [Matrix.diagonal_mul, Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
    dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- **The first display of Sec. 6.2.2 (Eq. (15)) is the row form of Eq. (21)** (arXiv 2302.01391).
-/
theorem fricField_row (ν lam : ℝ) (h u : Fin Nx → ℝ) (V : Matrix (Fin Nx) (Fin N) ℝ) (j : Fin Nx) :
    fricField ν lam h u V j =
      (h j)⁻¹ ^ 2 • (G₁ N ν *ᵥ V j) + (h j)⁻¹ • (G₂ N ν lam *ᵥ V j) + u j • gv N ν lam := by
  funext k
  have h1 := congrFun (row_diagonal_mul (fun j => (h j)⁻¹ ^ 2) V (G₁ N ν) j) k
  have h2 := congrFun (row_diagonal_mul (fun j => (h j)⁻¹) V (G₂ N ν lam) j) k
  simp only [fricField, Matrix.add_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply] at h1 h2 ⊢
  rw [h1, h2]

private lemma step_iff {E : Type*} [AddCommGroup E] [Module ℝ E] (x y a b c : E) (t : ℝ) :
    x = y + t • (a + b + c) ↔ x - t • a - t • b = y + t • c := by
  constructor
  · intro h
    rw [h]
    module
  · intro h
    have e : x = (x - t • a - t • b) + t • a + t • b := by module
    rw [e, h]
    module

/-- The left-hand side matrix `I_r - Δt h⁻² Ĝ₁ - Δt h⁻¹ Ĝ₂` of the implicit K-step of Sec. 6.2.2,
with the Euclidean Galerkin matrices `Ĝ = Wᵀ G W`. -/
def Khat (ν lam Δt h : ℝ) (W : Matrix (Fin N) (Fin r) ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  1 - (Δt * h⁻¹ ^ 2) • (Wᵀ * G₁ N ν * W) - (Δt * h⁻¹) • (Wᵀ * G₂ N ν lam * W)

/-- **The implicit K-step of the friction** (arXiv 2302.01391, Sec. 6.2.2): the
implicit Euler step `K⁺ = K + Δt F(K⁺ Wᵀ) W` of the BUG K-step for the field (21) is, cell by cell,
`(I_r - Δt h_j⁻² Ĝ₁ - Δt h_j⁻¹ Ĝ₂) K⁺_j = K_j + Δt u_{m,j} Wᵀ g_ν`.  This is the `kstep` field of
`IsMatrixImplicitBUGStep`.  Solvability is another matter, see `Khat_singular`. -/
theorem friction_kStep_iff (ν lam Δt : ℝ) (h u : Fin Nx → ℝ) (W : Matrix (Fin N) (Fin r) ℝ)
    (K₀ K₁ : Matrix (Fin Nx) (Fin r) ℝ) :
    K₁ = K₀ + Δt • (fricField ν lam h u (K₁ * Wᵀ) * W) ↔
      ∀ j, Khat ν lam Δt (h j) W *ᵥ K₁ j = K₀ j + (Δt * u j) • (Wᵀ *ᵥ gv N ν lam) := by
  have hF : ∀ j, (fricField ν lam h u (K₁ * Wᵀ) * W) j =
      (h j)⁻¹ ^ 2 • ((Wᵀ * G₁ N ν * W) *ᵥ K₁ j) + (h j)⁻¹ • ((Wᵀ * G₂ N ν lam * W) *ᵥ K₁ j)
        + u j • (Wᵀ *ᵥ gv N ν lam) := by
    intro j
    have e : fricField ν lam h u (K₁ * Wᵀ) * W =
        Matrix.diagonal (fun j => (h j)⁻¹ ^ 2) * K₁ * (Wᵀ * G₁ N ν * W)ᵀ
          + Matrix.diagonal (fun j => (h j)⁻¹) * K₁ * (Wᵀ * G₂ N ν lam * W)ᵀ
          + Matrix.vecMulVec u (Wᵀ *ᵥ gv N ν lam) := by
      simp only [fricField, Matrix.add_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.mul_assoc, Matrix.vecMulVec_mul, Matrix.mulVec_transpose]
    rw [e]
    funext k
    have h1 := congrFun (row_diagonal_mul (fun j => (h j)⁻¹ ^ 2) K₁ (Wᵀ * G₁ N ν * W) j) k
    have h2 := congrFun (row_diagonal_mul (fun j => (h j)⁻¹) K₁ (Wᵀ * G₂ N ν lam * W) j) k
    simp only [Matrix.add_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.vecMulVec_apply] at h1 h2 ⊢
    rw [h1, h2]
  have hrow : (K₁ = K₀ + Δt • (fricField ν lam h u (K₁ * Wᵀ) * W)) ↔
      ∀ j, K₁ j = K₀ j + Δt • (fricField ν lam h u (K₁ * Wᵀ) * W) j :=
    ⟨fun h j => congrFun h j, fun h => funext h⟩
  rw [hrow]
  refine forall_congr' fun j => ?_
  rw [hF j, step_iff]
  have e2 : Khat ν lam Δt (h j) W *ᵥ K₁ j = K₁ j - Δt • (h j)⁻¹ ^ 2 • ((Wᵀ * G₁ N ν * W) *ᵥ K₁ j)
      - Δt • (h j)⁻¹ • ((Wᵀ * G₂ N ν lam * W) *ᵥ K₁ j) := by
    simp only [Khat, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, smul_smul]
  rw [e2, smul_smul Δt (u j)]

/-- **The implicit L-step of the friction** (arXiv 2302.01391, Sec. 6.2.2): the
implicit Euler step `L⁺ = L + Δt F(X L⁺ᵀ)ᵀ X` of the BUG L-step for the field (21) is the Sylvester
equation `L⁺ - Δt G₁ L⁺ ĥ⁻² - Δt G₂ L⁺ ĥ⁻¹ = L + Δt g_ν u_mᵀ X` with `ĥ⁻² = Xᵀ h⁻² X`,
`ĥ⁻¹ = Xᵀ h⁻¹ X`, the `lstep` field of `IsMatrixImplicitBUGStep`. -/
theorem friction_lStep_iff (ν lam Δt : ℝ) (h u : Fin Nx → ℝ) (X : Matrix (Fin Nx) (Fin r) ℝ)
    (L₀ L₁ : Matrix (Fin N) (Fin r) ℝ) :
    L₁ = L₀ + Δt • ((fricField ν lam h u (X * L₁ᵀ))ᵀ * X) ↔
      L₁ - Δt • (G₁ N ν * L₁ * (Xᵀ * Matrix.diagonal (fun j => (h j)⁻¹ ^ 2) * X))
        - Δt • (G₂ N ν lam * L₁ * (Xᵀ * Matrix.diagonal (fun j => (h j)⁻¹) * X))
        = L₀ + Δt • (Matrix.vecMulVec (gv N ν lam) u * X) := by
  have e : (fricField ν lam h u (X * L₁ᵀ))ᵀ * X =
      G₁ N ν * L₁ * (Xᵀ * Matrix.diagonal (fun j => (h j)⁻¹ ^ 2) * X)
        + G₂ N ν lam * L₁ * (Xᵀ * Matrix.diagonal (fun j => (h j)⁻¹) * X)
        + Matrix.vecMulVec (gv N ν lam) u * X := by
    simp only [fricField, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.diagonal_transpose, Matrix.transpose_vecMulVec, Matrix.add_mul, Matrix.mul_assoc]
  rw [e, step_iff]

/-- **The implicit S-step of the friction** (arXiv 2302.01391, Sec. 6.2.2): the
implicit Euler step `S⁺ = S + Δt Xᵀ F(X S⁺ Wᵀ) W` for the field (21) is the equation
`S⁺ - Δt ĥ⁻² S⁺ Ĝ₁ᵀ - Δt ĥ⁻¹ S⁺ Ĝ₂ᵀ = S + Δt Xᵀ u_m g_νᵀ W`.  The paper defines `Ĝ` with `W¹`;
the implicit S-step needs the updated basis `W²`, which is the `W` here. -/
theorem friction_sStep_iff (ν lam Δt : ℝ) (h u : Fin Nx → ℝ) (X : Matrix (Fin Nx) (Fin r) ℝ)
    (W : Matrix (Fin N) (Fin r) ℝ) (S₀ S₁ : Matrix (Fin r) (Fin r) ℝ) :
    S₁ = S₀ + Δt • (Xᵀ * fricField ν lam h u (X * S₁ * Wᵀ) * W) ↔
      S₁ - Δt • ((Xᵀ * Matrix.diagonal (fun j => (h j)⁻¹ ^ 2) * X) * S₁ * (Wᵀ * G₁ N ν * W)ᵀ)
        - Δt • ((Xᵀ * Matrix.diagonal (fun j => (h j)⁻¹) * X) * S₁ * (Wᵀ * G₂ N ν lam * W)ᵀ)
        = S₀ + Δt • (Xᵀ * Matrix.vecMulVec u (gv N ν lam) * W) := by
  have e : Xᵀ * fricField ν lam h u (X * S₁ * Wᵀ) * W =
      (Xᵀ * Matrix.diagonal (fun j => (h j)⁻¹ ^ 2) * X) * S₁ * (Wᵀ * G₁ N ν * W)ᵀ
        + (Xᵀ * Matrix.diagonal (fun j => (h j)⁻¹) * X) * S₁ * (Wᵀ * G₂ N ν lam * W)ᵀ
        + Xᵀ * Matrix.vecMulVec u (gv N ν lam) * W := by
    simp only [fricField, Matrix.mul_add, Matrix.add_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [e, step_iff]

/-- The weighted Frobenius pairing `tr(Pᵀ M Q)` of `N × r` matrices. -/
private def tDot (P Q : Matrix (Fin N) (Fin r) ℝ) : ℝ :=
  ∑ c, wDot (fun i => P i c) (fun i => Q i c)

private lemma tDot_vecMulVec (L : Matrix (Fin N) (Fin r) ℝ) (a : Fin N → ℝ) (b : Fin r → ℝ) :
    tDot L (Matrix.vecMulVec a b) = wDot (L *ᵥ b) a := by
  simp only [tDot, wDot, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, Finset.sum_div]
  exact Finset.sum_congr rfl fun c _ => by ring

private lemma quad_sandwich (X : Matrix (Fin Nx) (Fin r) ℝ) (d : Fin Nx → ℝ) :
    Xᵀ * Matrix.diagonal d * X = ∑ j, d j • Matrix.vecMulVec (X j) (X j) := by
  ext a b
  rw [Matrix.mul_apply, Matrix.sum_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply]
  exact Finset.sum_congr rfl fun j _ => by ring

private lemma tDot_sum (L : Matrix (Fin N) (Fin r) ℝ) {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Fin N) (Fin r) ℝ) : tDot L (∑ j ∈ s, f j) = ∑ j ∈ s, tDot L (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tDot, wDot]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    simp only [tDot, wDot, ← Finset.sum_add_distrib, Matrix.add_apply]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => by ring

private lemma tDot_smul (L P : Matrix (Fin N) (Fin r) ℝ) (c : ℝ) :
    tDot L (c • P) = c * tDot L P := by
  simp only [tDot, wDot, Finset.mul_sum, Matrix.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => by ring

private lemma tDot_sub (L P Q : Matrix (Fin N) (Fin r) ℝ) :
    tDot L (P - Q) = tDot L P - tDot L Q := by
  simp only [tDot, wDot, ← Finset.sum_sub_distrib, Matrix.sub_apply]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => by ring

private lemma tDot_mul_sandwich (A : Matrix (Fin N) (Fin N) ℝ) (L : Matrix (Fin N) (Fin r) ℝ)
    (X : Matrix (Fin Nx) (Fin r) ℝ) (d : Fin Nx → ℝ) :
    tDot L (A * L * (Xᵀ * Matrix.diagonal d * X))
      = ∑ j, d j * wDot (L *ᵥ X j) (A *ᵥ (L *ᵥ X j)) := by
  rw [quad_sandwich, Matrix.mul_sum, tDot_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_smul, tDot_smul, Matrix.mul_vecMulVec, tDot_vecMulVec, ← Matrix.mulVec_mulVec]

/-- **The implicit L-step of the friction is always uniquely solvable** (arXiv 2302.01391,
Sec. 6.2.2, implicit L-step; not stated there): for all `Δt ≥ 0`, `ν ≥ 0`, `λ > 0`, positive
`h_j`, every `X` and every right-hand side, the implicit L-step (a Sylvester equation) has exactly
one solution.  The reason is that
the left projector `X Xᵀ` commutes with the weight `M`, which acts from the right.  Contrast
`Khat_singular`. -/
theorem friction_lStep_existsUnique {ν lam Δt : ℝ} (hν : 0 ≤ ν) (hlam : 0 < lam) (hΔt : 0 ≤ Δt)
    {h : Fin Nx → ℝ} (hh : ∀ j, 0 < h j) (X : Matrix (Fin Nx) (Fin r) ℝ)
    (R : Matrix (Fin N) (Fin r) ℝ) :
    ∃! L : Matrix (Fin N) (Fin r) ℝ,
      L - Δt • (G₁ N ν * L * (Xᵀ * Matrix.diagonal (fun j => (h j)⁻¹ ^ 2) * X))
        - Δt • (G₂ N ν lam * L * (Xᵀ * Matrix.diagonal (fun j => (h j)⁻¹) * X)) = R := by
  set E₂ := Xᵀ * Matrix.diagonal (fun j => (h j)⁻¹ ^ 2) * X with hE₂
  set E₁ := Xᵀ * Matrix.diagonal (fun j => (h j)⁻¹) * X with hE₁
  let T : Matrix (Fin N) (Fin r) ℝ →ₗ[ℝ] Matrix (Fin N) (Fin r) ℝ :=
    { toFun := fun L => L - Δt • (G₁ N ν * L * E₂) - Δt • (G₂ N ν lam * L * E₁)
      map_add' := fun A B => by
        simp only [Matrix.mul_add, Matrix.add_mul, smul_add]
        abel
      map_smul' := fun c A => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, smul_sub, smul_comm Δt c] }
  have hinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro L hL
    have hL' : L - Δt • (G₁ N ν * L * E₂) - Δt • (G₂ N ν lam * L * E₁) = 0 := hL
    have h1 : tDot L (L - Δt • (G₁ N ν * L * E₂) - Δt • (G₂ N ν lam * L * E₁)) = 0 := by
      rw [hL']
      simp [tDot, wDot]
    rw [tDot_sub, tDot_sub, tDot_smul, tDot_smul, hE₂, hE₁, tDot_mul_sandwich,
      tDot_mul_sandwich] at h1
    have h2 : ∑ j, (h j)⁻¹ ^ 2 * wDot (L *ᵥ X j) (G₁ N ν *ᵥ (L *ᵥ X j)) ≤ 0 := by
      refine Finset.sum_nonpos fun j _ => ?_
      have := viscC_quad_nonneg (L *ᵥ X j)
      rw [wDot_G₁]
      have hj : 0 ≤ (h j)⁻¹ ^ 2 := by positivity
      nlinarith [mul_nonneg (mul_nonneg hj hν) this]
    have h3 : ∑ j, (h j)⁻¹ * wDot (L *ᵥ X j) (G₂ N ν lam *ᵥ (L *ᵥ X j)) ≤ 0 := by
      refine Finset.sum_nonpos fun j _ => ?_
      rw [wDot_G₂]
      have hj : 0 ≤ (h j)⁻¹ := (inv_pos.2 (hh j)).le
      have : 0 ≤ (h j)⁻¹ * (ν / lam * (∑ i, (L *ᵥ X j) i) ^ 2) := by positivity
      nlinarith
    have h4 : tDot L L ≤ 0 := by
      nlinarith [mul_nonneg hΔt (neg_nonneg.2 h2), mul_nonneg hΔt (neg_nonneg.2 h3)]
    have h5 : ∀ c, wDot (fun i => L i c) (fun i => L i c) = 0 := by
      have hn : ∀ c ∈ Finset.univ, 0 ≤ wDot (fun i => L i c) (fun i => L i c) :=
        fun c _ => wDot_self_nonneg _
      have h0 : tDot L L = 0 := le_antisymm h4 (Finset.sum_nonneg hn)
      exact fun c => (Finset.sum_eq_zero_iff_of_nonneg hn).1 h0 c (Finset.mem_univ c)
    ext i c
    exact congrFun (eq_zero_of_wDot_self_le (h5 c).le) i
  have hsurj : Function.Surjective T := LinearMap.injective_iff_surjective.1 hinj
  obtain ⟨L, hL⟩ := hsurj R
  exact ⟨L, hL, fun L' hL' => hinj (hL'.trans hL.symm)⟩

/-- The unit vector `W = (-4/5, 3/5, 0, …, 0)ᵀ`, the rank-one basis of the counterexample. -/
def Wex (N : ℕ) : Matrix (Fin N) (Fin 1) ℝ :=
  fun i _ => if i.val = 0 then -4 / 5 else if i.val = 1 then 3 / 5 else 0

private lemma sum_Wex {N : ℕ} (hN : 2 ≤ N) (f : Fin N → ℝ) :
    ∑ i, Wex N i 0 * f i = -4 / 5 * f ⟨0, by omega⟩ + 3 / 5 * f ⟨1, by omega⟩ := by
  rw [Finset.sum_eq_add (⟨0, by omega⟩ : Fin N) (⟨1, by omega⟩ : Fin N) (by simp [Fin.ext_iff])
    (fun c _ hc => ?_) (by simp) (by simp)]
  · simp [Wex]
  · have h0 : c.val ≠ 0 := fun h => hc.1 (Fin.ext h)
    have h1 : c.val ≠ 1 := fun h => hc.2 (Fin.ext h)
    simp [Wex, h0, h1]

private lemma galerkin_Wex {N : ℕ} (hN : 2 ≤ N) (G : Matrix (Fin N) (Fin N) ℝ) :
    ((Wex N)ᵀ * G * Wex N) 0 0 =
      16 / 25 * G ⟨0, by omega⟩ ⟨0, by omega⟩ - 12 / 25 * G ⟨0, by omega⟩ ⟨1, by omega⟩
        - 12 / 25 * G ⟨1, by omega⟩ ⟨0, by omega⟩ + 9 / 25 * G ⟨1, by omega⟩ ⟨1, by omega⟩ := by
  have e : ((Wex N)ᵀ * G * Wex N) 0 0 = ∑ i, Wex N i 0 * ∑ j, Wex N j 0 * G i j := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e, sum_Wex hN, sum_Wex hN, sum_Wex hN]
  ring

/-- `Wex N` is orthonormal, so `Khat_singular` concerns an admissible basis of arXiv 2302.01391. -/
theorem Wex_orthonormal {N : ℕ} (hN : 2 ≤ N) : (Wex N)ᵀ * Wex N = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  have e : ((Wex N)ᵀ * Wex N) 0 0 = ∑ i, Wex N i 0 * Wex N i 0 := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
  simp only [Fin.zero_eta, Fin.isValue, e, sum_Wex hN (fun i => Wex N i 0)]
  norm_num [Wex]

private lemma G₁_zero_zero {N : ℕ} (h0 : 0 < N) : G₁ N 10 ⟨0, h0⟩ ⟨0, h0⟩ = -120 := by
  norm_num [G₁, oddW, viscC]

private lemma G₁_zero_one {N : ℕ} (h0 : 0 < N) (h1 : 1 < N) : G₁ N 10 ⟨0, h0⟩ ⟨1, h1⟩ = 0 := by
  norm_num [G₁, oddW, viscC]

private lemma G₁_one_zero {N : ℕ} (h0 : 0 < N) (h1 : 1 < N) : G₁ N 10 ⟨1, h1⟩ ⟨0, h0⟩ = 0 := by
  norm_num [G₁, oddW, viscC]

private lemma G₁_one_one {N : ℕ} (h1 : 1 < N) : G₁ N 10 ⟨1, h1⟩ ⟨1, h1⟩ = -600 := by
  norm_num [G₁, oddW, viscC]

private lemma G₂_apply {N : ℕ} (i j : Fin N) : G₂ N 10 (1 / 1000) i j = -10000 * oddW i := by
  norm_num [G₂, gv, Matrix.vecMulVec_apply]

/-- The Euclidean Galerkin values `Ĝ₁ = -7320 / 25`, `Ĝ₂ = 1200` of the counterexample. -/
private lemma Ghat_Wex {N : ℕ} (hN : 2 ≤ N) :
    ((Wex N)ᵀ * G₁ N 10 * Wex N) 0 0 = -7320 / 25 ∧
      ((Wex N)ᵀ * G₂ N 10 (1 / 1000) * Wex N) 0 0 = 1200 := by
  constructor
  · rw [galerkin_Wex hN, G₁_zero_zero, G₁_zero_one, G₁_one_zero, G₁_one_one]
    norm_num
  · rw [galerkin_Wex hN, G₂_apply, G₂_apply, G₂_apply, G₂_apply]
    norm_num [oddW]

/-- **Euclidean Galerkin projection does not preserve the friction's dissipativity** (arXiv
2302.01391, Secs. 5.2.2, 6.2.2, not claimed there).  For every `N ≥ 2`, the paper's parameters
`ν = 10`, `λ = 1/1000`, `h = 1` and the orthonormal `W = Wex N`, the reduced friction operator is
the positive number `h⁻² Ĝ₁ + h⁻¹ Ĝ₂ = 907.2`: the reduced model `k̇ = 907.2 k` grows exponentially,
for both POD-Galerkin and the K-step, although the full friction is `M`-dissipative
(`Dmat_isUnit`). -/
theorem reducedFriction_antidissipative {N : ℕ} (hN : 2 ≤ N) :
    ((Wex N)ᵀ * G₁ N 10 * Wex N + (Wex N)ᵀ * G₂ N 10 (1 / 1000) * Wex N) 0 0 = 4536 / 5 := by
  rw [Matrix.add_apply, (Ghat_Wex hN).1, (Ghat_Wex hN).2]
  norm_num

/-- **The implicit K-step system can be singular** (arXiv 2302.01391, Sec. 6.2.2; the paper solves
it without discussing solvability).  For every `N ≥ 2`, at the paper's `ν = 10`, `λ = 1/1000` with
`h = 1`, orthonormal `W = Wex N` and `Δt = 5/4536`, the matrix of that system vanishes.  Unlike
`D_j` (`Dmat_isUnit`) and the L-step (`friction_lStep_existsUnique`), solvability of the K-step
for an arbitrary Euclidean orthonormal basis fails.  With one cell, `X = 1`, the implicit S-step
is the same scalar equation. -/
theorem Khat_singular {N : ℕ} (hN : 2 ≤ N) : Khat 10 (1 / 1000) (5 / 4536) 1 (Wex N) = 0 := by
  ext i j
  fin_cases i
  fin_cases j
  simp only [Fin.zero_eta, Fin.isValue, Khat, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply_eq, (Ghat_Wex hN).1, (Ghat_Wex hN).2, Matrix.zero_apply]
  norm_num

/-- **The implicit K-step can have no solution** (arXiv 2302.01391, Sec. 6.2.2): for the data of
`Khat_singular` with `u_m = 0` and a non-zero `K`, on any grid, no `K⁺` satisfies the implicit Euler
K-step of the friction. -/
theorem friction_kStep_no_solution [NeZero Nx] {N : ℕ} (hN : 2 ≤ N) :
    ¬ ∃ K₁ : Matrix (Fin Nx) (Fin 1) ℝ,
      K₁ = Matrix.of (fun _ _ => 1) + (5 / 4536 : ℝ) •
        (fricField 10 (1 / 1000) (fun _ => 1) (fun _ => 0) (K₁ * (Wex N)ᵀ) * Wex N) := by
  rintro ⟨K₁, hK⟩
  have h0 := (friction_kStep_iff 10 (1 / 1000) (5 / 4536) (fun _ => 1) (fun _ => 0) (Wex N)
    (Matrix.of fun _ _ => 1) K₁).1 hK 0
  simp only [Khat_singular hN, Matrix.zero_mulVec, mul_zero, zero_smul, add_zero] at h0
  have h1 := congrFun h0 0
  simp at h1

/-- The energy matrix `M = diag(1 / (2 k + 1))` of `wDot`. -/
def Mw (N : ℕ) : Matrix (Fin N) (Fin N) ℝ := Matrix.diagonal fun i => (oddW i)⁻¹

/-- The matrix of the implicit K-step with the `M`-Galerkin matrices `Wᵀ M G W` in place of
`Wᵀ G W`. -/
def KhatM (ν lam Δt h : ℝ) (W : Matrix (Fin N) (Fin r) ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  1 - (Δt * h⁻¹ ^ 2) • (Wᵀ * Mw N * G₁ N ν * W) - (Δt * h⁻¹) • (Wᵀ * Mw N * G₂ N ν lam * W)

/-- **In the energy inner product the K-step is always solvable** (not in arXiv 2302.01391; this is
the repair of `Khat_singular`).  For the `M`-Galerkin matrices `Wᵀ M G W`, which are the K-step
matrices for a basis with `Wᵀ M W = I` and the `M`-orthogonal projection, the matrix of the
implicit K-step is invertible for all `Δt ≥ 0`, `h > 0`.  The proof does not use `Wᵀ M W = I`. -/
theorem KhatM_isUnit {ν lam Δt h : ℝ} (hν : 0 ≤ ν) (hlam : 0 < lam) (hΔt : 0 ≤ Δt)
    (hh : 0 < h) (W : Matrix (Fin N) (Fin r) ℝ) : IsUnit (KhatM ν lam Δt h W) := by
  have key : ∀ (G : Matrix (Fin N) (Fin N) ℝ) (z : Fin r → ℝ),
      z ⬝ᵥ ((Wᵀ * Mw N * G * W) *ᵥ z) = wDot (W *ᵥ z) (G *ᵥ (W *ᵥ z)) := by
    intro G z
    have e : (Wᵀ * Mw N * G * W) *ᵥ z = Wᵀ *ᵥ (Mw N *ᵥ (G *ᵥ (W *ᵥ z))) := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [e, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    simp only [dotProduct, wDot, Mw, Matrix.mulVec_diagonal]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have hz : KhatM ν lam Δt h W *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, sub_eq_zero]
    exact hxy
  set z := x - y with hzdef
  have h1 : z ⬝ᵥ (KhatM ν lam Δt h W *ᵥ z) = z ⬝ᵥ z
      - (Δt * h⁻¹ ^ 2) * wDot (W *ᵥ z) (G₁ N ν *ᵥ (W *ᵥ z))
      - (Δt * h⁻¹) * wDot (W *ᵥ z) (G₂ N ν lam *ᵥ (W *ᵥ z)) := by
    rw [← key, ← key, KhatM]
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul]
  rw [hz, dotProduct_zero, wDot_G₁, wDot_G₂] at h1
  have h2 := viscC_quad_nonneg (W *ᵥ z)
  have h3 : 0 ≤ Δt * h⁻¹ ^ 2 * (2 * ν * ∑ i, ∑ j, viscC i j * (W *ᵥ z) i * (W *ᵥ z) j) := by
    positivity
  have h4 : 0 ≤ Δt * h⁻¹ * (ν / lam * (∑ i, (W *ᵥ z) i) ^ 2) := by positivity
  have h5 : z ⬝ᵥ z ≤ 0 := by nlinarith
  have h6 : z ⬝ᵥ z = 0 := le_antisymm h5 (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
  exact sub_eq_zero.1 (dotProduct_self_eq_zero.1 h6)

end ReducedFriction

/-! ### POD (Sec. 5.1, Eq. 18) -/

section POD

open scoped LeanDLRA.Frobenius
open LeanDLRA.EckartYoung

variable {Nt Nx N : ℕ}

/-- The snapshot matrix `V^POD ∈ ℝ^{(N_x N_t) × N}` of Sec. 5.1: the matrices `V⁰, …, V^{N_t-1}`
stacked on top of each other. -/
def snapshotMatrix (Vs : Fin Nt → Matrix (Fin Nx) (Fin N) ℝ) :
    Matrix (Fin Nt × Fin Nx) (Fin N) ℝ := fun p k => Vs p.1 p.2 k

private lemma snapshotMatrix_mul (Vs : Fin Nt → Matrix (Fin Nx) (Fin N) ℝ)
    (P : Matrix (Fin N) (Fin N) ℝ) :
    snapshotMatrix Vs * P = snapshotMatrix fun n => Vs n * P := by
  ext p k
  simp [snapshotMatrix, Matrix.mul_apply]

private lemma sq_norm_snapshotMatrix (Vs : Fin Nt → Matrix (Fin Nx) (Fin N) ℝ) :
    ‖snapshotMatrix Vs‖ ^ 2 = ∑ n, ‖Vs n‖ ^ 2 := by
  simp only [LeanDLRA.Frobenius.norm_sq_eq_sum, snapshotMatrix, Fintype.sum_prod_type]

private lemma sq_norm_snapshot_sub (Vs : Fin Nt → Matrix (Fin Nx) (Fin N) ℝ)
    (P : Matrix (Fin N) (Fin N) ℝ) :
    ‖snapshotMatrix Vs - snapshotMatrix Vs * P‖ ^ 2 = ∑ n, ‖Vs n - Vs n * P‖ ^ 2 := by
  rw [snapshotMatrix_mul, ← sq_norm_snapshotMatrix]
  rfl

/-- **POD basis, Eq. (18)** (arXiv 2302.01391, Sec. 5.1).  For the top `r` right singular
vectors `W` of the snapshot matrix, the projection error over all snapshots is the tail of the
squared singular values of `V^POD`, in zero-based indexing `∑_{r ≤ i < N} σ_i²`.  The underlying
error identity after Eq. (18) for one matrix is `LeanDLRA.EckartYoung.sq_norm_sub_truncation`. -/
theorem pod_error (Vs : Fin Nt → Matrix (Fin Nx) (Fin N) ℝ) (r : ℕ) :
    let W := topRightSingularVectors (snapshotMatrix Vs) r
    ∑ n, ‖Vs n - Vs n * (W * Wᵀ)‖ ^ 2 =
      ∑ i ∈ Ico r N, (Matrix.toEuclideanLin (snapshotMatrix Vs)).singularValues i ^ 2 := by
  intro W
  have h := sq_norm_sub_truncation (snapshotMatrix Vs) r
  rw [Fintype.card_fin, truncation, Matrix.mul_assoc] at h
  rw [← sq_norm_snapshot_sub, h]

/-- **Optimality of the POD basis** (arXiv 2302.01391, Sec. 5.1, from Eckart–Young–Mirsky): no
`N × r` pair `W`, `W'` does better than the POD projection over the snapshots.  In particular this
holds for every orthonormal `W = W'`. -/
theorem pod_optimal (Vs : Fin Nt → Matrix (Fin Nx) (Fin N) ℝ) {r : ℕ}
    (W W' : Matrix (Fin N) (Fin r) ℝ) :
    ∑ i ∈ Ico r N, (Matrix.toEuclideanLin (snapshotMatrix Vs)).singularValues i ^ 2 ≤
      ∑ n, ‖Vs n - Vs n * (W * W'ᵀ)‖ ^ 2 := by
  have hrank : (snapshotMatrix Vs * W * W'ᵀ).rank ≤ r := by
    calc (snapshotMatrix Vs * W * W'ᵀ).rank ≤ (snapshotMatrix Vs * W).rank :=
          Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin r) := Matrix.rank_le_card_width _
      _ = r := Fintype.card_fin r
  have h := sum_sq_singularValues_le_sq_norm_sub (snapshotMatrix Vs) _ hrank
  rw [Fintype.card_fin, Matrix.mul_assoc] at h
  rwa [← sq_norm_snapshot_sub]

private lemma sq_norm_truncation_add {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (r : ℕ) :
    ‖truncation A r‖ ^ 2 + ‖A - truncation A r‖ ^ 2 = ‖A‖ ^ 2 := by
  have hP := LeanDLRA.isOrthProj_rightProj (m := m)
    (transpose_mul_topRightSingularVectors A r)
  have h1 := hP.norm_sq_add A
  have e : LeanDLRA.rightProj (topRightSingularVectors A r) A = truncation A r := by
    rw [LeanDLRA.rightProj_apply, truncation]
  rwa [e] at h1

/-- `‖V_r‖_F² = ∑_{i < r} σ_i²`: the energy of the truncated SVD (arXiv 2302.01391, numerator of
`E_cum` in Sec. 5.1). -/
theorem sq_norm_truncation {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (r : ℕ) :
    ‖truncation A r‖ ^ 2 =
      ∑ i ∈ range (min r (Fintype.card n)), (Matrix.toEuclideanLin A).singularValues i ^ 2 := by
  have h1 := sq_norm_truncation_add A r
  rw [sq_norm_sub_truncation, sq_norm_eq_sum_sq_singularValues A] at h1
  set f := fun i => (Matrix.toEuclideanLin A).singularValues i ^ 2 with hf
  have h2 : ∑ i ∈ Ico r (Fintype.card n), f i
      = ∑ i ∈ Ico (min r (Fintype.card n)) (Fintype.card n), f i := by
    rcases le_total r (Fintype.card n) with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, Finset.Ico_self, Finset.Ico_eq_empty (by omega)]
  have h3 := Finset.sum_range_add_sum_Ico f (min_le_right r (Fintype.card n))
  linarith

/-- **The energy criterion `E_cum`, corrected** (arXiv 2302.01391, Sec. 5.1): the energy captured
by the rank-`r` POD is `‖V_r‖_F² / ‖V‖_F² = ∑_{i<r} σ_i² / ∑_i σ_i²`.  The paper prints the left
side with unsquared norms, see `Ecum_printed_false`. -/
theorem Ecum_eq {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n ℝ) (r : ℕ) :
    ‖truncation A r‖ ^ 2 / ‖A‖ ^ 2 =
      (∑ i ∈ range (min r (Fintype.card n)), (Matrix.toEuclideanLin A).singularValues i ^ 2)
        / ∑ i ∈ range (Fintype.card n), (Matrix.toEuclideanLin A).singularValues i ^ 2 := by
  rw [sq_norm_truncation, sq_norm_eq_sum_sq_singularValues A]

/-- **`E_cum` as printed is false** (arXiv 2302.01391, Sec. 5.1): the printed identity
`‖V_r‖_F / ‖V‖_F = ∑_{k ≤ r} σ_k² / ∑_k σ_k²` fails for the `2 × 2` identity with `r = 1`.  The
norms on the left must be squared, see `Ecum_eq`. -/
theorem Ecum_printed_false :
    let A : Matrix (Fin 2) (Fin 2) ℝ := 1
    ‖truncation A 1‖ / ‖A‖ ≠
      (∑ i ∈ range (min 1 2), (Matrix.toEuclideanLin A).singularValues i ^ 2)
        / ∑ i ∈ range 2, (Matrix.toEuclideanLin A).singularValues i ^ 2 := by
  intro A hEq
  have hA2 : ‖A‖ ^ 2 = 2 := by
    rw [LeanDLRA.Frobenius.norm_sq_eq_sum]
    norm_num [A, Fin.sum_univ_two, Matrix.one_apply]
  have hApos : 0 < ‖A‖ := by
    rcases (norm_nonneg A).lt_or_eq with h | h
    · exact h
    · rw [← h] at hA2
      norm_num at hA2
  have hE := Ecum_eq A 1
  simp only [Fintype.card_fin] at hE
  rw [← hEq] at hE
  set t := ‖truncation A 1‖ / ‖A‖ with ht
  have h2 : t ^ 2 = t := by
    rw [ht, div_pow]
    exact hE
  have hpy := sq_norm_truncation_add A 1
  have hT : ‖truncation A 1‖ = t * ‖A‖ := by
    rw [ht]
    field_simp
  have hcases : t = 0 ∨ t = 1 := by
    have h3 : t * (t - 1) = 0 := by nlinarith
    rcases mul_eq_zero.1 h3 with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rcases hcases with h0 | h1
  · have hT0 : truncation A 1 = 0 := by
      rw [← norm_eq_zero, hT, h0, zero_mul]
    have hB := norm_sub_truncation_le A (Matrix.rank_vecMulVec_le ![(1 : ℝ), 0] ![(1 : ℝ), 0])
    rw [hT0, sub_zero] at hB
    have hAB : ‖A - Matrix.vecMulVec ![(1 : ℝ), 0] ![(1 : ℝ), 0]‖ ^ 2 = 1 := by
      rw [LeanDLRA.Frobenius.norm_sq_eq_sum]
      norm_num [A, Fin.sum_univ_two, Matrix.one_apply, Matrix.vecMulVec_apply]
    have h3 := pow_le_pow_left₀ (norm_nonneg A) hB 2
    rw [hA2, hAB] at h3
    norm_num at h3
  · have hsq : ‖A - truncation A 1‖ ^ 2 = 0 := by
      rw [hT, h1] at hpy
      nlinarith
    have hTA : A = truncation A 1 :=
      sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq))
    have hr := rank_truncation_le A 1
    rw [← hTA] at hr
    have hrA : A.rank = 2 := by simp [A]
    omega

end POD

/-! ### The BUG substeps of the micro transport (Sec. 6.2.1) -/

section Transport

variable {Nx N r : ℕ} [NeZero Nx]

/-- The reduced block `Ã_{j,vv} = ab_j Wᵀ 𝐀 W + ub_j I_r` of Sec. 6.2.1. -/
def AvvRed (W : Matrix (Fin N) (Fin r) ℝ) (u a : ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  a • (Wᵀ * Acoup N * W) + u • 1

private lemma row_mul {a b c : Type*} [Fintype b] (M : Matrix a b ℝ) (W : Matrix b c ℝ) (j : a) :
    (M * W) j = Wᵀ *ᵥ M j := by
  funext k
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]

/-- **The K-step of the micro transport** (arXiv 2302.01391, Sec. 6.2.1): for
orthonormal `W`, the right-hand side `F_v(U, K Wᵀ) W` of the K-step is the same stencil in the
`r`-dimensional variables `K_j`, with `A_{j,vu}` replaced by `Wᵀ A_{j,vu}` and `A_{j,vv}` by the
reduced `r × r` matrix `Ã_{j,vv}`.  So the K-step only needs `Wᵀ 𝐀 W`, the structure behind the
paper's cost claim `O(r² (N_x + N))`; the operation count itself is not a theorem.  The same
identity is the
POD-Galerkin transport of Sec. 5.2.1 (with Eq. 19) for a fixed `W`. -/
theorem microF_kStep {W : Matrix (Fin N) (Fin r) ℝ} (hW : Wᵀ * W = 1) (Δx Δt : ℝ)
    (B : Fin Nx → Matrix (Fin N) (Fin 2) ℝ) (ub ab : Fin Nx → ℝ) (U : Matrix (Fin Nx) (Fin 2) ℝ)
    (K : Matrix (Fin Nx) (Fin r) ℝ) (j : Fin Nx) :
    (microF Δx Δt B ub ab U (K * Wᵀ) * W) j =
      (1 / (2 * Δt)) • (K (j - 1) - (2 : ℝ) • K j + K (j + 1))
        - (1 / (2 * Δx)) • (Wᵀ *ᵥ (B (j + 1) *ᵥ (U (j + 1) - U j))
            + AvvRed W (ub (j + 1)) (ab (j + 1)) *ᵥ (K (j + 1) - K j))
        - (1 / (2 * Δx)) • (Wᵀ *ᵥ (B j *ᵥ (U j - U (j - 1)))
            + AvvRed W (ub j) (ab j) *ᵥ (K j - K (j - 1))) := by
  have hrow : ∀ i, (K * Wᵀ) i = W *ᵥ K i := fun i => by
    rw [row_mul, Matrix.transpose_transpose]
  have h1 : ∀ x : Fin r → ℝ, Wᵀ *ᵥ (W *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, hW, Matrix.one_mulVec]
  have h2 : ∀ (u a : ℝ) (x : Fin r → ℝ), Wᵀ *ᵥ (Avv N u a *ᵥ (W *ᵥ x)) = AvvRed W u a *ᵥ x := by
    intro u a x
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    simp only [AvvRed, Avv, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hW, Matrix.mul_assoc]
  have hl : ∀ a b c : Fin r → ℝ, W *ᵥ a - (2 : ℝ) • W *ᵥ b + W *ᵥ c
      = W *ᵥ (a - (2 : ℝ) • b + c) := fun a b c => by
    rw [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul]
  have hd : ∀ a b : Fin r → ℝ, W *ᵥ a - W *ᵥ b = W *ᵥ (a - b) := fun a b => by
    rw [Matrix.mulVec_sub]
  rw [row_mul]
  simp only [microF, hrow, hl, hd]
  simp only [Matrix.mulVec_sub Wᵀ, Matrix.mulVec_add Wᵀ, Matrix.mulVec_smul Wᵀ, h1, h2]

/-- `X̃ = ∑_j (X_{j-1} - 2 X_j + X_{j+1}) X_jᵀ`, Sec. 6.2.1. -/
def Xtilde (X : Matrix (Fin Nx) (Fin r) ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  ∑ j, Matrix.vecMulVec (X (j - 1) - (2 : ℝ) • X j + X (j + 1)) (X j)

/-- `f̃₊ = ∑_j (f_{j+1} + f_j) (X_{j+1} - X_j) X_jᵀ`, Sec. 6.2.1, with `f = α₁` or `f = u_m`. -/
def fPlus (f : Fin Nx → ℝ) (X : Matrix (Fin Nx) (Fin r) ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  ∑ j, (f (j + 1) + f j) • Matrix.vecMulVec (X (j + 1) - X j) (X j)

/-- `f̃₋ = ∑_j (f_j + f_{j-1}) (X_j - X_{j-1}) X_jᵀ`, defined "accordingly" in Sec. 6.2.1. -/
def fMinus (f : Fin Nx → ℝ) (X : Matrix (Fin Nx) (Fin r) ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  ∑ j, (f j + f (j - 1)) • Matrix.vecMulVec (X j - X (j - 1)) (X j)

/-- **The L-step of the micro transport** (arXiv 2302.01391, Sec. 6.2.1): the right-hand
side `F_v(U, X Lᵀ)ᵀ X` of the L-step is
`(1/2Δt) L X̃ - (1/4Δx) (𝐀 L (α̃₊ + α̃₋) + L (ũ₊ + ũ₋)) - (1/2Δx) ∑_j (A_{j+1,vu} (U_{j+1} - U_j) +
A_{j,vu} (U_j - U_{j-1})) X_jᵀ`.  The paper writes the sum over `j` by Einstein's convention. -/
theorem microF_lStep (Δx Δt : ℝ) (B : Fin Nx → Matrix (Fin N) (Fin 2) ℝ) (u a : Fin Nx → ℝ)
    (U : Matrix (Fin Nx) (Fin 2) ℝ) (X : Matrix (Fin Nx) (Fin r) ℝ)
    (L : Matrix (Fin N) (Fin r) ℝ) :
    (microF Δx Δt B (faceAvg u) (faceAvg a) U (X * Lᵀ))ᵀ * X =
      (1 / (2 * Δt)) • (L * Xtilde X)
        - (1 / (4 * Δx)) • (Acoup N * L * (fPlus a X + fMinus a X) + L * (fPlus u X + fMinus u X))
        - (1 / (2 * Δx)) • ∑ j, (Matrix.vecMulVec (B (j + 1) *ᵥ (U (j + 1) - U j)) (X j)
            + Matrix.vecMulVec (B j *ᵥ (U j - U (j - 1))) (X j)) := by
  have hrow : ∀ i, (X * Lᵀ) i = L *ᵥ X i := fun i => by
    rw [row_mul, Matrix.transpose_transpose]
  have hsum : ∀ F : Matrix (Fin Nx) (Fin N) ℝ,
      Fᵀ * X = ∑ j, Matrix.vecMulVec (F j) (X j) := fun F => by
    ext i c
    simp [Matrix.mul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply]
  have hl : ∀ a b c : Fin r → ℝ, L *ᵥ a - (2 : ℝ) • L *ᵥ b + L *ᵥ c
      = L *ᵥ (a - (2 : ℝ) • b + c) := fun a b c => by
    rw [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul]
  have hd : ∀ a b : Fin r → ℝ, L *ᵥ a - L *ᵥ b = L *ᵥ (a - b) := fun a b => by
    rw [Matrix.mulVec_sub]
  have hA : ∀ (p q : ℝ) (d y : Fin r → ℝ),
      Matrix.vecMulVec (Avv N p q *ᵥ (L *ᵥ d)) y =
        q • (Acoup N * L * Matrix.vecMulVec d y) + p • (L * Matrix.vecMulVec d y) := by
    intro p q d y
    have e : Avv N p q *ᵥ (L *ᵥ d) = q • ((Acoup N * L) *ᵥ d) + p • (L *ᵥ d) := by
      rw [Avv, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        Matrix.mulVec_mulVec]
    rw [e, Matrix.add_vecMulVec, Matrix.smul_vecMulVec, Matrix.smul_vecMulVec,
      Matrix.mul_vecMulVec, Matrix.mul_vecMulVec]
  have term : ∀ j, Matrix.vecMulVec (microF Δx Δt B (faceAvg u) (faceAvg a) U (X * Lᵀ) j) (X j) =
      (1 / (2 * Δt)) • (L * Matrix.vecMulVec (X (j - 1) - (2 : ℝ) • X j + X (j + 1)) (X j))
        - (1 / (4 * Δx)) • (Acoup N * L *
              ((a (j + 1) + a j) • Matrix.vecMulVec (X (j + 1) - X j) (X j)
                + (a j + a (j - 1)) • Matrix.vecMulVec (X j - X (j - 1)) (X j))
            + L * ((u (j + 1) + u j) • Matrix.vecMulVec (X (j + 1) - X j) (X j)
              + (u j + u (j - 1)) • Matrix.vecMulVec (X j - X (j - 1)) (X j)))
        - (1 / (2 * Δx)) • (Matrix.vecMulVec (B (j + 1) *ᵥ (U (j + 1) - U j)) (X j)
            + Matrix.vecMulVec (B j *ᵥ (U j - U (j - 1))) (X j)) := by
    intro j
    have hm : microF Δx Δt B (faceAvg u) (faceAvg a) U (X * Lᵀ) j =
        (1 / (2 * Δt)) • (L *ᵥ (X (j - 1) - (2 : ℝ) • X j + X (j + 1)))
          - (1 / (2 * Δx)) • (B (j + 1) *ᵥ (U (j + 1) - U j)
              + Avv N (faceAvg u (j + 1)) (faceAvg a (j + 1)) *ᵥ (L *ᵥ (X (j + 1) - X j)))
          - (1 / (2 * Δx)) • (B j *ᵥ (U j - U (j - 1))
              + Avv N (faceAvg u j) (faceAvg a j) *ᵥ (L *ᵥ (X j - X (j - 1)))) := by
      simp only [microF, hrow, hl, hd]
    rw [hm, Matrix.sub_vecMulVec, Matrix.sub_vecMulVec, Matrix.smul_vecMulVec,
      Matrix.smul_vecMulVec, Matrix.smul_vecMulVec, Matrix.add_vecMulVec, Matrix.add_vecMulVec,
      hA, hA, ← Matrix.mul_vecMulVec L]
    simp only [faceAvg, add_sub_cancel_right, Matrix.mul_add, Matrix.mul_smul]
    module
  rw [hsum]
  simp_rw [term]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.smul_sum, Xtilde, fPlus,
    fMinus, Matrix.mul_add, Matrix.mul_sum, Matrix.mul_smul]

/-- **The S-step of the micro transport, corrected** (arXiv 2302.01391, Sec. 6.2.1).
For orthonormal `W`, the right-hand side `Xᵀ F_v(U, X S Wᵀ) W` of the S-step satisfies
`Ṡᵀ = (1/2Δt) Sᵀ X̃ - (1/4Δx) (Wᵀ 𝐀 W Sᵀ (α̃₊ + α̃₋) + Sᵀ (ũ₊ + ũ₋)) - (1/2Δx) ∑_j (…) X_jᵀ`.

The `Ṡ` display of Sec. 6.2.1 writes `Ṡ` and `S X̃` here; both must carry a transpose, as its
remaining terms do. -/
theorem microF_sStep {W : Matrix (Fin N) (Fin r) ℝ} (hW : Wᵀ * W = 1) (Δx Δt : ℝ)
    (B : Fin Nx → Matrix (Fin N) (Fin 2) ℝ) (u a : Fin Nx → ℝ) (U : Matrix (Fin Nx) (Fin 2) ℝ)
    (X : Matrix (Fin Nx) (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ) :
    (Xᵀ * microF Δx Δt B (faceAvg u) (faceAvg a) U (X * S * Wᵀ) * W)ᵀ =
      (1 / (2 * Δt)) • (Sᵀ * Xtilde X)
        - (1 / (4 * Δx)) • ((Wᵀ * Acoup N * W) * Sᵀ * (fPlus a X + fMinus a X)
            + Sᵀ * (fPlus u X + fMinus u X))
        - (1 / (2 * Δx)) • ∑ j, (Matrix.vecMulVec (Wᵀ *ᵥ (B (j + 1) *ᵥ (U (j + 1) - U j))) (X j)
            + Matrix.vecMulVec (Wᵀ *ᵥ (B j *ᵥ (U j - U (j - 1)))) (X j)) := by
  have hL := microF_lStep Δx Δt B u a U X (W * Sᵀ)
  have e1 : X * (W * Sᵀ)ᵀ = X * S * Wᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [e1] at hL
  have e2 : (Xᵀ * microF Δx Δt B (faceAvg u) (faceAvg a) U (X * S * Wᵀ) * W)ᵀ
      = Wᵀ * ((microF Δx Δt B (faceAvg u) (faceAvg a) U (X * S * Wᵀ))ᵀ * X) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have e3 : ∀ M : Matrix (Fin r) (Fin r) ℝ, Wᵀ * (W * Sᵀ * M) = Sᵀ * M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hW, Matrix.one_mul]
  have e4 : ∀ M : Matrix (Fin r) (Fin r) ℝ,
      Wᵀ * (Acoup N * (W * Sᵀ) * M) = (Wᵀ * Acoup N * W) * Sᵀ * M := fun M => by
    simp only [Matrix.mul_assoc]
  rw [e2, hL]
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_sum, e3, e4,
    Matrix.mul_vecMulVec]

end Transport

/-! ### Robust error of BUG for the frozen-macro micro transport -/

section BUGError

open scoped LeanDLRA.Frobenius

variable {Nx N : ℕ} [NeZero Nx]

/-- The micro transport (arXiv 2302.01391, Sec. 6.2.1) with frozen macro state and coefficients is
an affine field, hence globally Lipschitz.  It is unbounded unless it is constant, so
`bug_global_error_le` does not apply directly and the tube version is needed. -/
theorem microF_isLipschitz (Δx Δt : ℝ) (B : Fin Nx → Matrix (Fin N) (Fin 2) ℝ) (ub ab : Fin Nx → ℝ)
    (U : Matrix (Fin Nx) (Fin 2) ℝ) :
    ∃ L, 0 ≤ L ∧ IsLipschitzField (fun _ V => microF Δx Δt B ub ab U V) L := by
  have hz : ∀ i, (0 : Matrix (Fin Nx) (Fin 2) ℝ) i = 0 := fun _ => rfl
  let T : Matrix (Fin Nx) (Fin N) ℝ →ₗ[ℝ] Matrix (Fin Nx) (Fin N) ℝ :=
    { toFun := fun V => microF Δx Δt B ub ab 0 V
      map_add' := fun V V' => by
        have ha : ∀ i, (V + V') i = V i + V' i := fun _ => rfl
        funext j
        change microF Δx Δt B ub ab 0 (V + V') j
          = microF Δx Δt B ub ab 0 V j + microF Δx Δt B ub ab 0 V' j
        simp only [microF, ha, hz, sub_self, Matrix.mulVec_zero, zero_add, Matrix.mulVec_sub,
          Matrix.mulVec_add]
        module
      map_smul' := fun c V => by
        have hs : ∀ i, (c • V) i = c • V i := fun _ => rfl
        funext j
        change microF Δx Δt B ub ab 0 (c • V) j = c • microF Δx Δt B ub ab 0 V j
        simp only [microF, hs, hz, sub_self, Matrix.mulVec_zero, zero_add, Matrix.mulVec_sub,
          Matrix.mulVec_smul]
        module }
  have hT : ∀ V V', microF Δx Δt B ub ab U V - microF Δx Δt B ub ab U V' = T (V - V') := by
    intro V V'
    have hs : ∀ i, (V - V') i = V i - V' i := fun _ => rfl
    funext j
    change microF Δx Δt B ub ab U V j - microF Δx Δt B ub ab U V' j
      = microF Δx Δt B ub ab 0 (V - V') j
    simp only [microF, hs, hz, sub_self, Matrix.mulVec_zero, zero_add, Matrix.mulVec_sub]
    module
  let C := LinearMap.toContinuousLinearMap T
  refine ⟨‖C‖, norm_nonneg _, fun _ V V' => ?_⟩
  change ‖microF Δx Δt B ub ab U V - microF Δx Δt B ub ab U V'‖ ≤ ‖C‖ * ‖V - V'‖
  rw [hT]
  exact C.le_opNorm (V - V')

/-- **Robust error of BUG for the micro transport with frozen macro state** (header note of
arXiv 2302.01391, Sec. 6.2.1; the paper itself has no error analysis).  For fixed `U` and fixed
coefficients, let `Y k` be BUG approximations of `V̇ = F_v(U, V)` and `A` the exact solution.  With
any Lipschitz constant `L` of the affine field (`microF_isLipschitz`), `B₀` bounding the field along
`A`, and `M = bugGlobalBound L (B₀ + L ρ) H T δ ε h` the Ceruti–Lubich constant, if
`M + 4 (B₀ + L ρ) h < ρ` then `‖Y k - A t_k‖ ≤ M`, independently of singular values.

The tube form is used because the affine field is unbounded, so `bug_global_error_le` does not
apply as it stands.  Freezing `U` and the coefficients is the setting of step 1b; the coupled
macro-micro error is not covered, and `ε` is a hypothesis through `IsBUGStep`. -/
theorem microBUG_global_error {Δx Δt : ℝ} {Bv : Fin Nx → Matrix (Fin N) (Fin 2) ℝ}
    {ub ab : Fin Nx → ℝ} {U : Matrix (Fin Nx) (Fin 2) ℝ} {L B₀ ρ ε H t₀ h δ T : ℝ} {n : ℕ}
    {A : ℝ → Matrix (Fin Nx) (Fin N) ℝ}
    (hF : IsLipschitzField (fun _ V => microF Δx Δt Bv ub ab U V) L) (hL : 0 ≤ L) (hρ : 0 ≤ ρ)
    (hB₀ : ∀ t ∈ Icc t₀ (t₀ + n * h), ‖microF Δx Δt Bv ub ab U (A t)‖ ≤ B₀) (hB₀0 : 0 ≤ B₀)
    (hε : 0 ≤ ε) (hh : 0 ≤ h) (hhH : h ≤ H)
    (hA : ODESolution (fun _ V => microF Δx Δt Bv ub ab U V) A t₀ (t₀ + n * h))
    {P Q : ℕ → Matrix (Fin Nx) (Fin N) ℝ →L[ℝ] Matrix (Fin Nx) (Fin N) ℝ}
    {Y : ℕ → Matrix (Fin Nx) (Fin N) ℝ} {YK YL YS Φ : ℕ → ℝ → Matrix (Fin Nx) (Fin N) ℝ}
    (hstep : ∀ k < n, IsBUGStep (fun _ V => microF Δx Δt Bv ub ab U V) ε (P k) (Q k) (P (k + 1))
      (Q (k + 1)) (t₀ + k * h) (t₀ + (k + 1) * h) (Y k) (YK k) (YL k) (YS k))
    (hY : ∀ k < n, Y (k + 1) = YS k (t₀ + (k + 1) * h))
    (hΦ : ∀ k < n, ODESolution (fun _ V => microF Δx Δt Bv ub ab U V) (Φ k) (t₀ + k * h)
      (t₀ + (k + 1) * h))
    (hΦ₀ : ∀ k < n, Φ k (t₀ + k * h) = Y k) (hδ : ‖Y 0 - A t₀‖ ≤ δ) (hnT : n * h ≤ T)
    (hsmall : bugGlobalBound L (B₀ + L * ρ) H T δ ε h + 4 * (B₀ + L * ρ) * h < ρ) :
    ∀ k ≤ n, ‖Y k - A (t₀ + k * h)‖ ≤ bugGlobalBound L (B₀ + L * ρ) H T δ ε h := by
  have hbd : IsBoundedOnTube (fun _ V => microF Δx Δt Bv ub ab U V) A t₀ (t₀ + n * h) ρ
      (B₀ + L * ρ) := by
    intro t ht x hx
    have h1 : ‖microF Δx Δt Bv ub ab U x - microF Δx Δt Bv ub ab U (A t)‖ ≤ L * ‖x - A t‖ :=
      hF t x (A t)
    have h2 := norm_add_le (microF Δx Δt Bv ub ab U x - microF Δx Δt Bv ub ab U (A t))
      (microF Δx Δt Bv ub ab U (A t))
    rw [sub_add_cancel] at h2
    have h3 := hB₀ t ht
    have h4 := mul_le_mul_of_nonneg_left hx hL
    change ‖microF Δx Δt Bv ub ab U x‖ ≤ B₀ + L * ρ
    linarith
  exact bug_global_error_le_of_tube (hF.isLipschitzOnTube A _ _ _) hL hbd
    (add_nonneg hB₀0 (mul_nonneg hL hρ)) hε hh hhH hA hstep hY hΦ hΦ₀ hδ hnT hsmall

end BUGError

end

end LeanDLRA.Literature.P2302_01391
