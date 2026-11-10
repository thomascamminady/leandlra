import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Integrators.ProjectorSplitting
import LeanDLRA.Foundations.Existence
import LeanDLRA.OpenProblems.Stiff.Part2a
import LeanDLRA.FixedRank.TangentSpace

/-!
# Results of arXiv 1803.10473: Low-rank Lie-Trotter splitting for stiff matrix ODEs

Ostermann, Piazzola, Walach, *Convergence of a low-rank Lie–Trotter splitting for stiff matrix
differential equations* (arXiv 1803.10473). The paper splits `Ẋ = AX + XA* + G(t, X)` on
`ℂ^{m×m}` (Frobenius norm) into the stiff linear part, solved exactly by
`Φ^A_τ(Z) = e^{τA} Z e^{τA*}`, and the nonlinear part `Ẋ = G(t, X)`, whose dynamical low-rank
approximation is solved by the projector-splitting integrator `Φ̃^G_τ`; the low-rank Lie–Trotter
splitting is `I_τ = Φ^A_τ ∘ Φ̃^G_τ` (eq. (7)).

We work with real matrices, where the paper's conjugate transpose `A*` becomes `Aᵀ`, and with the
Frobenius inner product of `LeanDLRA.Frobenius`.

## Sec. 3.2 and Sec. 8 (rank and tangent-space facts)

* `stiff_derivative_mem_tangent` (Sec. 3.2): `A Y + Y Aᵀ` lies in the range of the tangent
  projector `P(Y)` for `Y = U S Vᵀ` with orthonormal `U`, `V` (any core `S`).
* `rank_exp_congr` (Sec. 3.2): `e^{tA} Y e^{tAᵀ}` has the rank of `Y`. The paper cites
  Helmke–Moore for this and does not prove it.
* `riccati_term_tangent` (Sec. 8): `P(Y)(Y K Y) = Y K Y`, the identity behind the splitting of the
  Riccati nonlinearity `G = Q - Y K Y` into `M = P(Y)Q - YKY` and `R = Q - P(Y)Q`.
* `sylvesterFlow_self_eq`: the stiff flow `Φ^A_t Z = e^{tA} Z e^{tAᵀ}` is the library's
  `sylvesterFlow A A t Z` (`OpenProblems/Stiff/Part2Defs`), which all statements below use.

## Sec. 5.2 and 5.3 (error analysis)

The abstract results live on a real inner product space `E`, with the stiff flow over one step
an arbitrary map `Φ` satisfying the paper's bound (10) at `t = τ` in Lipschitz form,
`‖Φ x - Φ y‖ ≤ e^{τω} ‖x - y‖` (for the linear flow `Φ^A_τ` this is (10)). One step of the
projector-splitting integrator is the core structure `IsKSLStep`
(`Integrators/ProjectorSplitting.lean`); the paper's Assumption 1(c) (normal component of `G`
of size `ε`) enters through its field `kNormal`, which for matrices follows from the manifold form
`‖(I - P(Y)) G(t, Y)‖ ≤ ε` by `ksl_kNormal_of_manifold`, and from the factor ODEs of the matrix
algorithm by `MatrixKSL.IsStep.isKSLStep`.

* `lieTrotter_step_stability` (proof of Prop. 2, first display): the full-rank step
  `L_τ = Φ^A_τ ∘ Φ^G_τ` is Lipschitz with constant `e^{(L+ω)τ}`.
* `lowRank_lieTrotter_local_error` (**Lemma 1**): `‖(Φ^A_τ ∘ Φ^G_τ)(Y) - (Φ^A_τ ∘ Φ̃^G_τ)(Y)‖
  ≤ b₁ ε τ + b₂ τ²` with `b₁ = e^{τω}`, `b₂ = 11 L B e^{τω}`; it is the core robust local error
  `IsKSLStep.local_error` pushed through (10). `lowRank_lieTrotter_local_error_le` gives the
  paper's constants `b₁ = e^{τω}(3e^{Lτ}+4)`, `b₂ = e^{τω}(4BLe^{Lτ}+9BL)`, which are larger.
* `lowRank_vs_fullRank_lieTrotter` (**Proposition 2**): `‖(Φ^A_τ ∘ Φ^G_τ)ⁿ(Y⁰) -
  (Φ^A_τ ∘ Φ̃^G_τ)ⁿ(Y⁰)‖ ≤ c₂ ε + c₃ τ` for `n τ ≤ T`, with `c₂ = T e^{(L+ω⁺)T}`,
  `c₃ = 11 L B T e^{(L+ω⁺)T}`, `ω⁺ = max ω 0`. For `L = 0` (differential Lyapunov equations,
  Sec. 7) `c₃ = 0`, as remarked in the paper.
* `fullRank_lieTrotter_propagation` (proof of Thm. 1, `E_δ`): the full-rank splitting propagates
  a perturbation of the initial value by at most `e^{(L+ω⁺)T}`.
* `lowRank_lieTrotter_error_of_fullRank` (**Theorem 1, conditional on Proposition 1**): if the
  full-rank splitting from `X⁰` has error `≤ C τ (1 + |log τ|)` (Proposition 1), then the low-rank
  splitting has error `≤ c₀ τ (1 + |log τ|) + c₁ δ + c₂ ε`. The proof is the paper's
  decomposition `E_sp + E_δ + E_lr`. Proposition 1 itself and the unconditional Theorem 1 are in
  `LeanDLRA.Literature.Stiff.P1803_10473b`.
* Matrix forms with `Φ^A_τ = sylvesterFlow A A τ` and hypothesis (10) as printed:
  `lowRank_lieTrotter_local_error_matrix` (Lemma 1), `lowRank_vs_fullRank_lieTrotter_matrix`
  (Prop. 2). `sylvesterFlow_bound_of_negSemidef`: (10) holds with `ω = 0` for every symmetric
  negative semidefinite `A` (discrete Laplacians), by `sylvester_dissipative_smoothing`.

## Deviations from the paper

* Real matrices (or a real inner product space) instead of `ℂ^{m×m}`.
* **Global instead of local constants.** Assumption 1(b) only asks `G` to be `C¹` near the exact
  solution, giving local Lipschitz and bound constants `L`, `B` valid within distance `γ`
  (eq. (12)); the paper keeps the iterates in that neighbourhood by a choice of `τ₀` it does not
  carry out. We assume `IsLipschitzField G L` and `IsBoundedField G B` globally, as the core
  projector-splitting theory does, and then need no `τ₀` and no condition `‖Yⁿ⁻¹ - Y(tₙ₋₁)‖ ≤ γ`.
* The normal-component bound is used in the core form `IsKSLStep.kNormal` (at the K-step result
  of each step), see above.
* The exact substep flows that appear in the statements (`Φ^G` from the full-rank iterates) are
  hypotheses (`ODESolution`), as in the core; the auxiliary flows of the proofs are constructed
  with `exists_ODESolution`, for which `G` is assumed continuous in `t`.
* Constants are explicit. Lemma 1 is proved with smaller constants than printed (the printed
  bound follows, `lowRank_lieTrotter_local_error_le`).

Core definitions used: `tangentProj`, `IsKSLStep`, `ODESolution`, `IsLipschitzField`,
`IsBoundedField`, `sylvesterFlow`. No new definitions. Duplicates to merge later: the flow
`e^{tA} Z e^{tAᵀ}` is also `linFlow` (P2506_15259a) and `mexp` (OpRA44, P2111_07160a);
`stiff_derivative_mem_tangent` duplicates `stiff_derivative_mem_tangent'` (P2010_05249a).
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P1803_10473

open LeanDLRA LeanDLRA.OpenProblems.Stiff

variable {k k' m : Type*} [Fintype k] [Fintype k'] [Fintype m]

/-- **arXiv 1803.10473, Sec. 3.2 (tangent part).** For `Y = U S Vᵀ` with orthonormal `U`, `V`, the
matrix `A Y + Y Aᵀ = (A U) S Vᵀ + U (S (A V)ᵀ)` is a tangent vector at `Y`: it lies in the range of
the tangent projector `P(Y)` of the rank-`r` manifold. The core `S` need not be invertible. This is
the case `A_x = A`, `A_y = Aᵀ` of the core `LeanDLRA.mul_add_mul_mem_range_tangentProj`. -/
theorem stiff_derivative_mem_tangent [DecidableEq k] [DecidableEq k'] {U : Matrix m k ℝ}
    {V : Matrix m k' ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (S : Matrix k k' ℝ)
    (A : Matrix m m ℝ) :
    A * (U * S * Vᵀ) + (U * S * Vᵀ) * Aᵀ ∈
      LinearMap.range (tangentProj U V : Matrix m m ℝ →ₗ[ℝ] Matrix m m ℝ) :=
  mul_add_mul_mem_range_tangentProj hU hV S A Aᵀ

/-- **arXiv 1803.10473, Sec. 3.2 (rank part).** The congruence flow `Y ↦ e^{tA} Y e^{tAᵀ}` preserves
the rank of `Y = U S Vᵀ` for every `t`, since `e^{tA}` and `e^{tAᵀ}` are invertible. The paper
states this with a reference to Helmke–Moore. -/
theorem rank_exp_congr [DecidableEq m] {U : Matrix m k ℝ} {V : Matrix m k' ℝ}
    (S : Matrix k k' ℝ) (A : Matrix m m ℝ) (t : ℝ) :
    (NormedSpace.exp (t • A) * (U * S * Vᵀ) * NormedSpace.exp (t • Aᵀ)).rank =
      (U * S * Vᵀ).rank := by
  have hA : IsUnit (NormedSpace.exp (t • A)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp (𝔸 := ℝ) _)
  have hB : IsUnit (NormedSpace.exp (t • Aᵀ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp (𝔸 := ℝ) _)
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hB,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hA]

/-- **arXiv 1803.10473, Sec. 8: the Riccati term is tangent.** For `Y = U S Vᵀ` with orthonormal
`U` and any square `K`, the tangent projector fixes `Y K Y`, i.e. `P(Y)(Y K Y) = Y K Y`. The paper
also uses the orthonormality of `V`; it is not needed. -/
theorem riccati_term_tangent [DecidableEq k] {U : Matrix m k ℝ} {V : Matrix m k' ℝ}
    (hU : Uᵀ * U = 1) (S : Matrix k k' ℝ) (K : Matrix m m ℝ) :
    tangentProj U V (U * S * Vᵀ * K * (U * S * Vᵀ)) = U * S * Vᵀ * K * (U * S * Vᵀ) := by
  have h : U * S * Vᵀ * K * (U * S * Vᵀ) = U * (S * Vᵀ * K * U * S * Vᵀ) := by
    simp only [Matrix.mul_assoc]
  rw [h]
  exact tangentProj_mul_left hU V _

/-- Non-vacuity: the orthonormality hypotheses hold for the identity bases, so the tangent and
Riccati statements apply, e.g. with `U = V = 1`, `S = 1`. -/
example (K : Matrix (Fin 2) (Fin 2) ℝ) :
    tangentProj (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
        ((1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ) *
          (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * K * ((1 : Matrix (Fin 2) (Fin 2) ℝ) *
          (1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ)) =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ) *
          (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * K * ((1 : Matrix (Fin 2) (Fin 2) ℝ) *
          (1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ) :=
  riccati_term_tangent (V := (1 : Matrix (Fin 2) (Fin 2) ℝ)) (by simp) _ K

/-! ### The stiff flow as `sylvesterFlow` -/

section StiffFlow

variable [DecidableEq m]

/-- **The stiff flow of arXiv 1803.10473, eq. (13).** The exact flow `Φ^A_t Z = e^{tA} Z e^{tA*}`
of `Ẋ = AX + XA*` (real case `A* = Aᵀ`) is the library's Sylvester flow `sylvesterFlow A A t Z`
(`e^{tA} Z (e^{tA})ᵀ`). -/
theorem sylvesterFlow_self_eq (A : Matrix m m ℝ) (t : ℝ) (Z : Matrix m m ℝ) :
    sylvesterFlow A A t Z = NormedSpace.exp (t • A) * Z * NormedSpace.exp (t • Aᵀ) := by
  change NormedSpace.exp (t • A) * Z * (NormedSpace.exp (t • A))ᵀ = _
  rw [← Matrix.transpose_smul, Matrix.exp_transpose]

/-- The stiff flow at time `0` is the identity. -/
theorem sylvesterFlow_zero_time (A Z : Matrix m m ℝ) : sylvesterFlow A A 0 Z = Z := by
  simp [sylvesterFlow]

/-- The stiff flow is linear: `Φ^A_t X - Φ^A_t Y = Φ^A_t (X - Y)`. -/
theorem sylvesterFlow_sub (A : Matrix m m ℝ) (t : ℝ) (X Y : Matrix m m ℝ) :
    sylvesterFlow A A t X - sylvesterFlow A A t Y = sylvesterFlow A A t (X - Y) := by
  simp only [sylvesterFlow, Matrix.mul_sub, Matrix.sub_mul]

/-- `Φ^A_t` maps `A Z + Z Aᵀ` to `A (Φ^A_t Z) + (Φ^A_t Z) Aᵀ`, since `A` commutes with `e^{tA}`;
so the left side of the paper's smoothing bound (11), `e^{tA}(AZ + ZA*)e^{tA*}`, is the Lyapunov
operator applied to the flow. -/
theorem sylvesterFlow_lyapunov (A : Matrix m m ℝ) (t : ℝ) (Z : Matrix m m ℝ) :
    sylvesterFlow A A t (A * Z + Z * Aᵀ) =
      A * sylvesterFlow A A t Z + sylvesterFlow A A t Z * Aᵀ := by
  have hc : A * NormedSpace.exp (t • A) = NormedSpace.exp (t • A) * A :=
    (((Commute.refl A).smul_right t).exp_right).eq
  have hcT : (NormedSpace.exp (t • A))ᵀ * Aᵀ = Aᵀ * (NormedSpace.exp (t • A))ᵀ := by
    rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, hc]
  have hc' : ∀ W : Matrix m m ℝ,
      NormedSpace.exp (t • A) * (A * W) = A * (NormedSpace.exp (t • A) * W) := fun W => by
    rw [← Matrix.mul_assoc, ← hc, Matrix.mul_assoc]
  simp only [sylvesterFlow, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hcT, hc']

end StiffFlow

/-! ### The low-rank Lie–Trotter splitting (abstract form) -/

section Splitting

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Discrete Grönwall inequality in the form `e (k+1) ≤ e^{K τ} (e k + d)`. -/
private lemma le_exp_mul_of_rec {e : ℕ → ℝ} {K τ d : ℝ} {N : ℕ} (hK : 0 ≤ K) (hτ : 0 ≤ τ)
    (hd : 0 ≤ d) (he : ∀ k < N, e (k + 1) ≤ Real.exp (K * τ) * (e k + d)) :
    ∀ n ≤ N, e n ≤ Real.exp (K * (n * τ)) * (e 0 + n * d) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have h2 := he n (by omega)
    have hnτ : (0 : ℝ) ≤ n * τ := mul_nonneg (Nat.cast_nonneg _) hτ
    have hexp : Real.exp (K * τ) * Real.exp (K * (n * τ)) =
        Real.exp (K * (((n + 1 : ℕ) : ℝ) * τ)) := by
      rw [← Real.exp_add]; push_cast; ring_nf
    have hle : Real.exp (K * τ) ≤ Real.exp (K * (((n + 1 : ℕ) : ℝ) * τ)) := by
      apply Real.exp_le_exp.2
      push_cast
      nlinarith [mul_nonneg hK hnτ]
    calc e (n + 1) ≤ Real.exp (K * τ) * (e n + d) := h2
      _ ≤ Real.exp (K * τ) * (Real.exp (K * (n * τ)) * (e 0 + n * d) + d) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = Real.exp (K * (((n + 1 : ℕ) : ℝ) * τ)) * (e 0 + n * d) + Real.exp (K * τ) * d := by
          rw [← hexp]; ring
      _ ≤ Real.exp (K * (((n + 1 : ℕ) : ℝ) * τ)) * (e 0 + n * d)
          + Real.exp (K * (((n + 1 : ℕ) : ℝ) * τ)) * d := by
          have := mul_le_mul_of_nonneg_right hle hd
          linarith
      _ = Real.exp (K * (((n + 1 : ℕ) : ℝ) * τ)) * (e 0 + ((n + 1 : ℕ) : ℝ) * d) := by
          push_cast; ring

omit [InnerProductSpace ℝ E] in
/-- The one-step Lipschitz bound `e^{τω}` of the stiff flow implies the bound `e^{τ ω⁺}`. -/
private lemma lip_max {Φ : E → E} {ω τ : ℝ} (hτ : 0 ≤ τ)
    (hΦ : ∀ x y, ‖Φ x - Φ y‖ ≤ Real.exp (τ * ω) * ‖x - y‖) :
    ∀ x y, ‖Φ x - Φ y‖ ≤ Real.exp (τ * max ω 0) * ‖x - y‖ := fun x y =>
  (hΦ x y).trans (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (le_max_left _ _) hτ)) (norm_nonneg _))

/-- **Stability of the full-rank Lie–Trotter step** (arXiv 1803.10473, proof of Proposition 2,
first display). If the stiff flow `Φ` over one step satisfies (10) in the form
`‖Φ x - Φ y‖ ≤ e^{τω} ‖x - y‖` and `V`, `W` solve `Ẋ = G(t, X)` with `G` `L`-Lipschitz on a
step `[t₀, t₁]`, `t₁ = t₀ + τ`, then `‖Φ(V t₁) - Φ(W t₁)‖ ≤ e^{(L+ω)τ} ‖V t₀ - W t₀‖`, i.e.
`‖L_τ(Ŷ) - L_τ(Ỹ)‖ ≤ e^{(L+ω)τ} ‖Ŷ - Ỹ‖` for `L_τ = Φ^A_τ ∘ Φ^G_τ`. The paper states it for
`Ŷ, Ỹ` on the low-rank manifold; no rank condition is needed. -/
theorem lieTrotter_step_stability {G : ℝ → E → E} {L ω τ t₀ t₁ : ℝ}
    (hG : IsLipschitzField G L) (hL : 0 ≤ L) (ht₁ : t₁ = t₀ + τ) (hτ : 0 ≤ τ) {Φ : E → E}
    (hΦ : ∀ x y, ‖Φ x - Φ y‖ ≤ Real.exp (τ * ω) * ‖x - y‖) {V W : ℝ → E}
    (hV : ODESolution G V t₀ t₁) (hW : ODESolution G W t₀ t₁) :
    ‖Φ (V t₁) - Φ (W t₁)‖ ≤ Real.exp ((L + ω) * τ) * ‖V t₀ - W t₀‖ := by
  have h1 := hV.norm_sub_le_exp hG hL hW t₁ ⟨by linarith, le_rfl⟩
  rw [show t₁ - t₀ = τ by linarith] at h1
  calc ‖Φ (V t₁) - Φ (W t₁)‖ ≤ Real.exp (τ * ω) * ‖V t₁ - W t₁‖ := hΦ _ _
    _ ≤ Real.exp (τ * ω) * (Real.exp (L * τ) * ‖V t₀ - W t₀‖) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = Real.exp ((L + ω) * τ) * ‖V t₀ - W t₀‖ := by
        rw [← mul_assoc, ← Real.exp_add, show τ * ω + L * τ = (L + ω) * τ by ring]

/-- **arXiv 1803.10473, Lemma 1** (local error of the low-rank versus the full-rank splitting).
Let `G` be `L`-Lipschitz and bounded by `B`, let the stiff flow `Φ` over one step satisfy (10) in
the form `‖Φ x - Φ y‖ ≤ e^{τω} ‖x - y‖`, let `X₂` be the exact solution of `Ẋ = G(t, X)` on
`[t₀, t₁]`, `t₁ = t₀ + τ`, from `X₂ t₀ = Y` (so `Φ^G_τ(Y) = X₂ t₁`), and let one step of the
projector-splitting integrator from `Y` (`IsKSLStep`, normal-component bound `ε`) give
`Φ̃^G_τ(Y) = YL t₁`. Then

    ‖(Φ^A_τ ∘ Φ^G_τ)(Y) - (Φ^A_τ ∘ Φ̃^G_τ)(Y)‖ ≤ b₁ ε τ + b₂ τ²,   b₁ = e^{τω}, b₂ = 11 L B e^{τω}.

The paper's proof is the same (bound (10), then the local error of the projector-splitting
integrator from Kieri–Lubich–Walach, here the core `IsKSLStep.local_error`), with the larger
constants of `lowRank_lieTrotter_local_error_le`. Deviations: `L`, `B` are global (the paper's
are local, hence its condition `‖Yⁿ⁻¹ - Y(tₙ₋₁)‖ ≤ γ`, which is not needed here). -/
theorem lowRank_lieTrotter_local_error {G : ℝ → E → E} {L B ε ω τ t₀ t₁ : ℝ}
    (hG : IsLipschitzField G L) (hL : 0 ≤ L) (hB : IsBoundedField G B) (ht₁ : t₁ = t₀ + τ)
    (hτ : 0 ≤ τ) {Φ : E → E} (hΦ : ∀ x y, ‖Φ x - Φ y‖ ≤ Real.exp (τ * ω) * ‖x - y‖)
    {Y : E} {X₂ : ℝ → E} (hX₂ : ODESolution G X₂ t₀ t₁) (hX₂₀ : X₂ t₀ = Y)
    {P Q : E →L[ℝ] E} {YK YS YL : ℝ → E} (hs : IsKSLStep G ε P Q t₀ t₁ Y YK YS YL) :
    ‖Φ (X₂ t₁) - Φ (YL t₁)‖ ≤
      Real.exp (τ * ω) * ε * τ + 11 * L * B * Real.exp (τ * ω) * τ ^ 2 := by
  have h1 := hs.local_error hG hL hB ht₁ hτ hX₂ hX₂₀
  calc ‖Φ (X₂ t₁) - Φ (YL t₁)‖ ≤ Real.exp (τ * ω) * ‖X₂ t₁ - YL t₁‖ := hΦ _ _
    _ ≤ Real.exp (τ * ω) * (τ * (11 * L * B * τ + ε)) := by
        rw [norm_sub_rev]
        exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = _ := by ring

/-- **arXiv 1803.10473, Lemma 1, with the printed constants** `b₁ = e^{τω}(3e^{Lτ}+4)` and
`b₂ = e^{τω}(4BLe^{Lτ}+9BL)` (end of the proof of Lemma 1). Corollary of
`lowRank_lieTrotter_local_error`, whose constants are smaller. -/
theorem lowRank_lieTrotter_local_error_le {G : ℝ → E → E} {L B ε ω τ t₀ t₁ : ℝ}
    (hG : IsLipschitzField G L) (hL : 0 ≤ L) (hB : IsBoundedField G B) (ht₁ : t₁ = t₀ + τ)
    (hτ : 0 ≤ τ) {Φ : E → E} (hΦ : ∀ x y, ‖Φ x - Φ y‖ ≤ Real.exp (τ * ω) * ‖x - y‖)
    {Y : E} {X₂ : ℝ → E} (hX₂ : ODESolution G X₂ t₀ t₁) (hX₂₀ : X₂ t₀ = Y)
    {P Q : E →L[ℝ] E} {YK YS YL : ℝ → E} (hs : IsKSLStep G ε P Q t₀ t₁ Y YK YS YL) :
    ‖Φ (X₂ t₁) - Φ (YL t₁)‖ ≤
      Real.exp (τ * ω) * (3 * Real.exp (L * τ) + 4) * ε * τ
        + Real.exp (τ * ω) * (4 * B * L * Real.exp (L * τ) + 9 * B * L) * τ ^ 2 := by
  have h := lowRank_lieTrotter_local_error hG hL hB ht₁ hτ hΦ hX₂ hX₂₀ hs
  have hε : 0 ≤ ε := hs.eps_nonneg (by linarith)
  have hB0 : 0 ≤ B := hB.nonneg
  have he1 : 1 ≤ Real.exp (L * τ) := Real.one_le_exp (mul_nonneg hL hτ)
  have hE : 0 < Real.exp (τ * ω) := Real.exp_pos _
  have h0 : 0 ≤ Real.exp (τ * ω) * ε * τ := mul_nonneg (mul_nonneg hE.le hε) hτ
  have h0' : 0 ≤ L * B * Real.exp (τ * ω) * τ ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg hL hB0) hE.le) (sq_nonneg τ)
  have h1 : Real.exp (τ * ω) * ε * τ ≤
      Real.exp (τ * ω) * (3 * Real.exp (L * τ) + 4) * ε * τ := by
    nlinarith [mul_nonneg h0 (show 0 ≤ 3 * Real.exp (L * τ) + 3 by linarith)]
  have h2 : 11 * L * B * Real.exp (τ * ω) * τ ^ 2 ≤
      Real.exp (τ * ω) * (4 * B * L * Real.exp (L * τ) + 9 * B * L) * τ ^ 2 := by
    nlinarith [mul_nonneg h0' (show 0 ≤ 4 * Real.exp (L * τ) - 2 by linarith)]
  linarith

/-- **arXiv 1803.10473, Proposition 2** (low-rank versus full-rank Lie–Trotter splitting). Let
`G` be `L`-Lipschitz, bounded by `B` and continuous in `t`, let the stiff flow `Φ` over one step
satisfy (10) in the form `‖Φ x - Φ y‖ ≤ e^{τω} ‖x - y‖`, and let `tₖ = t₀ + k τ`. Let `X` be the
full-rank splitting `X (k+1) = Φ (V k tₖ₊₁)` with `V k` the exact flow of `Ẋ = G(t, X)` on
`[tₖ, tₖ₊₁]` from `X k`, and `Y` the low-rank splitting `Y (k+1) = Φ (YL k tₖ₊₁)` with one step
of the projector-splitting integrator from `Y k` (`IsKSLStep`, normal-component bound `ε ≥ 0`),
both from the same `X 0 = Y 0 = Y⁰`. Then for `n ≤ N` with `n τ ≤ T`

    ‖Eⁿ_lr‖ = ‖X n - Y n‖ ≤ c₂ ε + c₃ τ,   c₂ = T e^{(L+ω⁺)T},  c₃ = 11 L B T e^{(L+ω⁺)T},

with `ω⁺ = max ω 0`; the constants depend only on `ω`, `L`, `B`, `T`. Proof as in the paper:
stability (`lieTrotter_step_stability`) and Lemma 1 (`lowRank_lieTrotter_local_error`) give
`‖Eᵏ⁺¹_lr‖ ≤ e^{(L+ω⁺)τ} (‖Eᵏ_lr‖ + τ (11 L B τ + ε))`, solved by a discrete Grönwall
inequality. Deviation: global `L`, `B` (see the module docstring). -/
theorem lowRank_vs_fullRank_lieTrotter [CompleteSpace E] {G : ℝ → E → E}
    {L B ε ω τ t₀ T : ℝ} (hG : IsLipschitzField G L) (hL : 0 ≤ L) (hB : IsBoundedField G B)
    (hGc : ∀ x, Continuous fun t => G t x) (hε : 0 ≤ ε) (hτ : 0 ≤ τ) {Φ : E → E}
    (hΦ : ∀ x y, ‖Φ x - Φ y‖ ≤ Real.exp (τ * ω) * ‖x - y‖) {N : ℕ} {X Y : ℕ → E}
    {V : ℕ → ℝ → E} (hV : ∀ k < N, ODESolution G (V k) (t₀ + k * τ) (t₀ + (k + 1) * τ))
    (hV₀ : ∀ k < N, V k (t₀ + k * τ) = X k)
    (hX : ∀ k < N, X (k + 1) = Φ (V k (t₀ + (k + 1) * τ))) {P Q : ℕ → E →L[ℝ] E}
    {YK YS YL : ℕ → ℝ → E}
    (hstep : ∀ k < N, IsKSLStep G ε (P k) (Q k) (t₀ + k * τ) (t₀ + (k + 1) * τ) (Y k) (YK k)
      (YS k) (YL k))
    (hY : ∀ k < N, Y (k + 1) = Φ (YL k (t₀ + (k + 1) * τ))) (h0 : X 0 = Y 0) :
    ∀ n ≤ N, (n : ℝ) * τ ≤ T →
      ‖X n - Y n‖ ≤ T * Real.exp ((L + max ω 0) * T) * ε
        + 11 * L * B * T * Real.exp ((L + max ω 0) * T) * τ := by
  set K := L + max ω 0 with hKdef
  have hK : 0 ≤ K := add_nonneg hL (le_max_right _ _)
  have hB0 : 0 ≤ B := hB.nonneg
  have hΦ' := lip_max hτ hΦ
  have hg : 0 ≤ 11 * L * B * τ + ε :=
    add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL) hB0) hτ) hε
  have hd : 0 ≤ τ * (11 * L * B * τ + ε) := mul_nonneg hτ hg
  have hrec : ∀ k < N, ‖X (k + 1) - Y (k + 1)‖ ≤
      Real.exp (K * τ) * (‖X k - Y k‖ + τ * (11 * L * B * τ + ε)) := by
    intro k hk
    have ht : t₀ + (k + 1) * τ = t₀ + k * τ + τ := by ring
    obtain ⟨W, hW, hW₀⟩ := exists_ODESolution hG hB hGc
      (show t₀ + k * τ ≤ t₀ + (k + 1) * τ by linarith) (Y k)
    have hstab := lieTrotter_step_stability hG hL ht hτ hΦ' (hV k hk) hW
    have hloc := lowRank_lieTrotter_local_error hG hL hB ht hτ hΦ' hW hW₀ (hstep k hk)
    rw [hV₀ k hk, hW₀, ← hKdef] at hstab
    have htri := norm_sub_le_norm_sub_add_norm_sub (Φ (V k (t₀ + (k + 1) * τ)))
      (Φ (W (t₀ + (k + 1) * τ))) (Φ (YL k (t₀ + (k + 1) * τ)))
    have hexp : Real.exp (τ * max ω 0) ≤ Real.exp (K * τ) :=
      Real.exp_le_exp.2 (by rw [hKdef]; nlinarith [mul_nonneg hL hτ])
    have hloc' : Real.exp (τ * max ω 0) * ε * τ + 11 * L * B * Real.exp (τ * max ω 0) * τ ^ 2
        ≤ Real.exp (K * τ) * (τ * (11 * L * B * τ + ε)) := by
      have := mul_le_mul_of_nonneg_right hexp hd
      nlinarith
    rw [hX k hk, hY k hk]
    have hmul : Real.exp (K * τ) * (‖X k - Y k‖ + τ * (11 * L * B * τ + ε)) =
        Real.exp (K * τ) * ‖X k - Y k‖ + Real.exp (K * τ) * (τ * (11 * L * B * τ + ε)) := by
      ring
    rw [hmul]
    linarith
  intro n hn hT
  have h1 : ‖X n - Y n‖ ≤
      Real.exp (K * (n * τ)) * (‖X 0 - Y 0‖ + n * (τ * (11 * L * B * τ + ε))) :=
    le_exp_mul_of_rec (e := fun k => ‖X k - Y k‖) hK hτ hd hrec n hn
  rw [h0, sub_self, norm_zero, zero_add] at h1
  have h2 : (n : ℝ) * (τ * (11 * L * B * τ + ε)) ≤ T * (11 * L * B * τ + ε) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hT hg
  have h3 : Real.exp (K * (n * τ)) ≤ Real.exp (K * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hT hK)
  have hnd : 0 ≤ (n : ℝ) * (τ * (11 * L * B * τ + ε)) := mul_nonneg (Nat.cast_nonneg _) hd
  calc ‖X n - Y n‖ ≤ Real.exp (K * (n * τ)) * (n * (τ * (11 * L * B * τ + ε))) := h1
    _ ≤ Real.exp (K * T) * (T * (11 * L * B * τ + ε)) :=
        mul_le_mul h3 h2 hnd (Real.exp_pos _).le
    _ = _ := by ring

/-- **Propagation of the initial error by the full-rank splitting** (arXiv 1803.10473, proof of
Theorem 1, the term `E_δ`). Two runs `Z`, `X` of the full-rank Lie–Trotter splitting
(`X (k+1) = Φ (V k tₖ₊₁)`, `V k` the exact flow of `Ẋ = G(t, X)` from `X k`) satisfy
`‖Z n - X n‖ ≤ e^{(L+ω⁺)T} ‖Z 0 - X 0‖` for `n τ ≤ T`. -/
theorem fullRank_lieTrotter_propagation {G : ℝ → E → E} {L ω τ t₀ T : ℝ}
    (hG : IsLipschitzField G L) (hL : 0 ≤ L) (hτ : 0 ≤ τ) {Φ : E → E}
    (hΦ : ∀ x y, ‖Φ x - Φ y‖ ≤ Real.exp (τ * ω) * ‖x - y‖) {N : ℕ} {Z X : ℕ → E}
    {U V : ℕ → ℝ → E} (hU : ∀ k < N, ODESolution G (U k) (t₀ + k * τ) (t₀ + (k + 1) * τ))
    (hU₀ : ∀ k < N, U k (t₀ + k * τ) = Z k)
    (hZ : ∀ k < N, Z (k + 1) = Φ (U k (t₀ + (k + 1) * τ)))
    (hV : ∀ k < N, ODESolution G (V k) (t₀ + k * τ) (t₀ + (k + 1) * τ))
    (hV₀ : ∀ k < N, V k (t₀ + k * τ) = X k)
    (hX : ∀ k < N, X (k + 1) = Φ (V k (t₀ + (k + 1) * τ))) :
    ∀ n ≤ N, (n : ℝ) * τ ≤ T → ‖Z n - X n‖ ≤ Real.exp ((L + max ω 0) * T) * ‖Z 0 - X 0‖ := by
  set K := L + max ω 0 with hKdef
  have hK : 0 ≤ K := add_nonneg hL (le_max_right _ _)
  have hΦ' := lip_max hτ hΦ
  have hrec : ∀ k < N, ‖Z (k + 1) - X (k + 1)‖ ≤ Real.exp (K * τ) * (‖Z k - X k‖ + 0) := by
    intro k hk
    have h := lieTrotter_step_stability hG hL (show t₀ + (k + 1) * τ = t₀ + k * τ + τ by ring)
      hτ hΦ' (hU k hk) (hV k hk)
    rw [hU₀ k hk, hV₀ k hk, ← hKdef] at h
    rw [hZ k hk, hX k hk, add_zero]
    exact h
  intro n hn hT
  have h1 : ‖Z n - X n‖ ≤ Real.exp (K * (n * τ)) * (‖Z 0 - X 0‖ + n * 0) :=
    le_exp_mul_of_rec (e := fun k => ‖Z k - X k‖) hK hτ le_rfl hrec n hn
  rw [mul_zero, add_zero] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hT hK)) (norm_nonneg _))

/-- **arXiv 1803.10473, Theorem 1, conditional on Proposition 1.** Under the hypotheses of
`lowRank_vs_fullRank_lieTrotter` (with `τ > 0`), let `X` be the exact solution of
`Ẋ = AX + XA* + G(t, X)` and `Z` the full-rank Lie–Trotter splitting started at `Z 0 = X⁰`
(exact `G`-flows `U k`), and **assume the conclusion of Proposition 1**,
`‖X(t₀ + n τ) - Z n‖ ≤ C τ (1 + |log τ|)` for `n τ ≤ T` (proved in
`LeanDLRA.Literature.Stiff.P1803_10473b`). If the low-rank splitting starts at `Y 0` with
`‖Z 0 - Y 0‖ ≤ δ`, then for `n ≤ N` with `n τ ≤ T`

    ‖X(t₀ + n τ) - Iⁿ_τ(Y⁰)‖ ≤ c₀ τ (1 + |log τ|) + c₁ δ + c₂ ε

with `c₀ = C + 11 L B T e^{(L+ω⁺)T}`, `c₁ = e^{(L+ω⁺)T}`, `c₂ = T e^{(L+ω⁺)T}`. Proof as in
the paper (Sec. 5.3): the error is `E_sp + E_δ + E_lr`, bounded by Proposition 1 (assumed),
`fullRank_lieTrotter_propagation` and Proposition 2. The full-rank splitting from `Y⁰` used in
the proof is constructed here. -/
theorem lowRank_lieTrotter_error_of_fullRank [CompleteSpace E] {G : ℝ → E → E}
    {L B ε ω τ t₀ T C δ : ℝ} (hG : IsLipschitzField G L) (hL : 0 ≤ L) (hB : IsBoundedField G B)
    (hGc : ∀ x, Continuous fun t => G t x) (hε : 0 ≤ ε) (hτ : 0 < τ) {Φ : E → E}
    (hΦ : ∀ x y, ‖Φ x - Φ y‖ ≤ Real.exp (τ * ω) * ‖x - y‖) {N : ℕ} {X : ℝ → E} {Z Y : ℕ → E}
    {U : ℕ → ℝ → E} (hU : ∀ k < N, ODESolution G (U k) (t₀ + k * τ) (t₀ + (k + 1) * τ))
    (hU₀ : ∀ k < N, U k (t₀ + k * τ) = Z k)
    (hZ : ∀ k < N, Z (k + 1) = Φ (U k (t₀ + (k + 1) * τ)))
    (hsp : ∀ n ≤ N, (n : ℝ) * τ ≤ T → ‖X (t₀ + n * τ) - Z n‖ ≤ C * τ * (1 + |Real.log τ|))
    {P Q : ℕ → E →L[ℝ] E} {YK YS YL : ℕ → ℝ → E}
    (hstep : ∀ k < N, IsKSLStep G ε (P k) (Q k) (t₀ + k * τ) (t₀ + (k + 1) * τ) (Y k) (YK k)
      (YS k) (YL k))
    (hY : ∀ k < N, Y (k + 1) = Φ (YL k (t₀ + (k + 1) * τ))) (hδ : ‖Z 0 - Y 0‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * τ ≤ T →
      ‖X (t₀ + n * τ) - Y n‖ ≤
        (C + 11 * L * B * T * Real.exp ((L + max ω 0) * T)) * τ * (1 + |Real.log τ|)
          + Real.exp ((L + max ω 0) * T) * δ + T * Real.exp ((L + max ω 0) * T) * ε := by
  have hle : ∀ k : ℕ, t₀ + k * τ ≤ t₀ + (k + 1) * τ := fun k => by nlinarith
  choose F hF hF₀ using fun (k : ℕ) (z : E) => exists_ODESolution hG hB hGc (hle k) z
  let Xf : ℕ → E := fun n =>
    Nat.rec (motive := fun _ => E) (Y 0) (fun k x => Φ (F k x (t₀ + (k + 1) * τ))) n
  have hXf0 : Xf 0 = Y 0 := rfl
  have hXfs : ∀ k, Xf (k + 1) = Φ (F k (Xf k) (t₀ + (k + 1) * τ)) := fun k => rfl
  intro n hn hT
  have hT0 : 0 ≤ T := le_trans (mul_nonneg (Nat.cast_nonneg _) hτ.le) hT
  have hlr := lowRank_vs_fullRank_lieTrotter hG hL hB hGc hε hτ.le hΦ
    (V := fun k => F k (Xf k)) (fun k _ => hF k (Xf k)) (fun k _ => hF₀ k (Xf k))
    (fun k _ => hXfs k) hstep hY hXf0 n hn hT
  have hpr := fullRank_lieTrotter_propagation hG hL hτ.le hΦ (V := fun k => F k (Xf k)) hU hU₀
    hZ (fun k _ => hF k (Xf k)) (fun k _ => hF₀ k (Xf k)) (fun k _ => hXfs k) n hn hT
  rw [hXf0] at hpr
  have hsp' := hsp n hn hT
  have htri : ‖X (t₀ + n * τ) - Y n‖ ≤
      ‖X (t₀ + n * τ) - Z n‖ + ‖Z n - Xf n‖ + ‖Xf n - Y n‖ := by
    have e1 := norm_sub_le_norm_sub_add_norm_sub (X (t₀ + n * τ)) (Z n) (Y n)
    have e2 := norm_sub_le_norm_sub_add_norm_sub (Z n) (Xf n) (Y n)
    linarith
  have hlog : τ ≤ τ * (1 + |Real.log τ|) := le_mul_of_one_le_right hτ.le
    (by linarith [abs_nonneg (Real.log τ)])
  have hc : 0 ≤ 11 * L * B * T * Real.exp ((L + max ω 0) * T) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL) hB.nonneg) hT0)
      (Real.exp_pos _).le
  have hδ' : Real.exp ((L + max ω 0) * T) * ‖Z 0 - Y 0‖ ≤ Real.exp ((L + max ω 0) * T) * δ :=
    mul_le_mul_of_nonneg_left hδ (Real.exp_pos _).le
  have h4 : 11 * L * B * T * Real.exp ((L + max ω 0) * T) * τ ≤
      11 * L * B * T * Real.exp ((L + max ω 0) * T) * (τ * (1 + |Real.log τ|)) :=
    mul_le_mul_of_nonneg_left hlog hc
  have hexpand : (C + 11 * L * B * T * Real.exp ((L + max ω 0) * T)) * τ * (1 + |Real.log τ|) =
      C * τ * (1 + |Real.log τ|) +
        11 * L * B * T * Real.exp ((L + max ω 0) * T) * (τ * (1 + |Real.log τ|)) := by ring
  rw [hexpand]
  linarith

end Splitting

/-! ### Matrix form (the paper's setting, real case) -/

section MatrixForm

open scoped LeanDLRA.Frobenius

variable [DecidableEq m]

/-- Bound (10) of arXiv 1803.10473, `‖e^{tA} Z e^{tA*}‖ ≤ e^{tω} ‖Z‖` for `t > 0`, in the
Lipschitz form used by the abstract results, for every `τ ≥ 0`. -/
theorem norm_sylvesterFlow_sub_le {A : Matrix m m ℝ} {ω τ : ℝ} (hτ : 0 ≤ τ)
    (h10 : ∀ t > 0, ∀ Z : Matrix m m ℝ, ‖sylvesterFlow A A t Z‖ ≤ Real.exp (t * ω) * ‖Z‖)
    (X Y : Matrix m m ℝ) :
    ‖sylvesterFlow A A τ X - sylvesterFlow A A τ Y‖ ≤ Real.exp (τ * ω) * ‖X - Y‖ := by
  rw [sylvesterFlow_sub]
  rcases hτ.eq_or_lt with rfl | hτ'
  · rw [sylvesterFlow_zero_time, zero_mul, Real.exp_zero, one_mul]
  · exact h10 τ hτ' _

/-- **Assumption 1(a), bound (10), for discrete Laplacians.** If `-A` is positive semidefinite
(e.g. a finite-difference Laplacian), then `‖e^{tA} Z e^{tAᵀ}‖ ≤ e^{t·0} ‖Z‖` for all `t > 0`:
(10) holds with `ω = 0` (`sylvester_dissipative_smoothing`, OP-ST-14). -/
theorem sylvesterFlow_bound_of_negSemidef {A : Matrix m m ℝ} (hA : (-A).PosSemidef) :
    ∀ t > 0, ∀ Z : Matrix m m ℝ, ‖sylvesterFlow A A t Z‖ ≤ Real.exp (t * 0) * ‖Z‖ :=
  fun t ht Z => by
    rw [mul_zero, Real.exp_zero, one_mul]
    exact (sylvester_dissipative_smoothing hA hA ht.le Z).2.1

/-- **arXiv 1803.10473, Lemma 1, matrix form.** For `Ẋ = AX + XAᵀ + G(t, X)` on real `m × m`
matrices (Frobenius norm) with bound (10) `‖e^{tA} Z e^{tAᵀ}‖ ≤ e^{tω} ‖Z‖` (`t > 0`), `G`
`L`-Lipschitz and bounded by `B`, the exact `G`-flow `X₂` from `Y` and one step of the
projector-splitting integrator from `Y` (`IsKSLStep`, obtained from the factor ODEs by
`MatrixKSL.IsStep.isKSLStep`), the low-rank and full-rank Lie–Trotter steps differ by at most
`b₁ ε τ + b₂ τ²` with the paper's constants. See `lowRank_lieTrotter_local_error` for smaller
constants and the deviations. -/
theorem lowRank_lieTrotter_local_error_matrix {G : ℝ → Matrix m m ℝ → Matrix m m ℝ}
    {A : Matrix m m ℝ} {L B ε ω τ t₀ t₁ : ℝ} (hG : IsLipschitzField G L) (hL : 0 ≤ L)
    (hB : IsBoundedField G B)
    (h10 : ∀ t > 0, ∀ Z : Matrix m m ℝ, ‖sylvesterFlow A A t Z‖ ≤ Real.exp (t * ω) * ‖Z‖)
    (ht₁ : t₁ = t₀ + τ) (hτ : 0 ≤ τ) {Y : Matrix m m ℝ} {X₂ : ℝ → Matrix m m ℝ}
    (hX₂ : ODESolution G X₂ t₀ t₁) (hX₂₀ : X₂ t₀ = Y)
    {P Q : Matrix m m ℝ →L[ℝ] Matrix m m ℝ} {YK YS YL : ℝ → Matrix m m ℝ}
    (hs : IsKSLStep G ε P Q t₀ t₁ Y YK YS YL) :
    ‖sylvesterFlow A A τ (X₂ t₁) - sylvesterFlow A A τ (YL t₁)‖ ≤
      Real.exp (τ * ω) * (3 * Real.exp (L * τ) + 4) * ε * τ
        + Real.exp (τ * ω) * (4 * B * L * Real.exp (L * τ) + 9 * B * L) * τ ^ 2 :=
  lowRank_lieTrotter_local_error_le (Φ := sylvesterFlow A A τ) hG hL hB ht₁ hτ
    (norm_sylvesterFlow_sub_le hτ h10) hX₂ hX₂₀ hs

/-- **arXiv 1803.10473, Proposition 2, matrix form.** The low-rank Lie–Trotter splitting
`Yₖ₊₁ = e^{τA} Φ̃^G_τ(Yₖ) e^{τAᵀ}` and the full-rank one `Xₖ₊₁ = e^{τA} Φ^G_τ(Xₖ) e^{τAᵀ}`, from
the same `X₀ = Y₀`, satisfy `‖Xₙ - Yₙ‖ ≤ c₂ ε + c₃ τ` for `n τ ≤ T`, with
`c₂ = T e^{(L+ω⁺)T}`, `c₃ = 11 L B T e^{(L+ω⁺)T}`. See `lowRank_vs_fullRank_lieTrotter`. -/
theorem lowRank_vs_fullRank_lieTrotter_matrix {G : ℝ → Matrix m m ℝ → Matrix m m ℝ}
    {A : Matrix m m ℝ} {L B ε ω τ t₀ T : ℝ} (hG : IsLipschitzField G L) (hL : 0 ≤ L)
    (hB : IsBoundedField G B) (hGc : ∀ x, Continuous fun t => G t x) (hε : 0 ≤ ε) (hτ : 0 ≤ τ)
    (h10 : ∀ t > 0, ∀ Z : Matrix m m ℝ, ‖sylvesterFlow A A t Z‖ ≤ Real.exp (t * ω) * ‖Z‖)
    {N : ℕ} {X Y : ℕ → Matrix m m ℝ} {V : ℕ → ℝ → Matrix m m ℝ}
    (hV : ∀ k < N, ODESolution G (V k) (t₀ + k * τ) (t₀ + (k + 1) * τ))
    (hV₀ : ∀ k < N, V k (t₀ + k * τ) = X k)
    (hX : ∀ k < N, X (k + 1) = sylvesterFlow A A τ (V k (t₀ + (k + 1) * τ)))
    {P Q : ℕ → Matrix m m ℝ →L[ℝ] Matrix m m ℝ} {YK YS YL : ℕ → ℝ → Matrix m m ℝ}
    (hstep : ∀ k < N, IsKSLStep G ε (P k) (Q k) (t₀ + k * τ) (t₀ + (k + 1) * τ) (Y k) (YK k)
      (YS k) (YL k))
    (hY : ∀ k < N, Y (k + 1) = sylvesterFlow A A τ (YL k (t₀ + (k + 1) * τ)))
    (h0 : X 0 = Y 0) :
    ∀ n ≤ N, (n : ℝ) * τ ≤ T →
      ‖X n - Y n‖ ≤ T * Real.exp ((L + max ω 0) * T) * ε
        + 11 * L * B * T * Real.exp ((L + max ω 0) * T) * τ :=
  lowRank_vs_fullRank_lieTrotter (Φ := sylvesterFlow A A τ) hG hL hB hGc hε hτ
    (norm_sylvesterFlow_sub_le hτ h10) hV hV₀ hX hstep hY h0

end MatrixForm

/-! ### Satisfiability of the hypotheses -/

section Examples

open LeanDLRA.KSLExample

/-- Non-vacuity of Proposition 2 (and of Lemma 1, which it uses): one step on `E = ℂ ≅ ℝ²` with
the constant field `G ≡ 1 + i` (`L = 0`), the identity as stiff flow (`ω = 0`), and the KSL
step `KSLExample.isKSLStep` with rank-one projectors onto the real axis and `ε = 1`. The
full-rank splitting gives `X 1 = 1 + i`, the low-rank one `Y 1 = 1`, and the bound
`c₂ ε + c₃ τ = 1` of `lowRank_vs_fullRank_lieTrotter` is attained: `‖X 1 - Y 1‖ = ‖i‖ = 1`. -/
example : ‖(if (1 : ℕ) = 0 then (0 : ℂ) else 1 + Complex.I) - (if (1 : ℕ) = 0 then (0 : ℂ) else 1)‖
      ≤ 1 * Real.exp ((0 + max 0 0) * 1) * 1
        + 11 * 0 * ‖1 + Complex.I‖ * 1 * Real.exp ((0 + max 0 0) * 1) * 1 :=
  lowRank_vs_fullRank_lieTrotter (E := ℂ) (G := fun _ _ => 1 + Complex.I) (L := 0)
    (B := ‖1 + Complex.I‖) (ε := 1) (ω := 0) (τ := 1) (t₀ := 0) (T := 1) (Φ := id) (N := 1)
    (X := fun k => if k = 0 then 0 else 1 + Complex.I) (Y := fun k => if k = 0 then 0 else 1)
    (V := fun _ t => 0 + (t : ℂ) * (1 + Complex.I)) (P := fun _ => reProj)
    (Q := fun _ => reProj) (YK := fun _ t => 0 + (t : ℂ) * 1)
    (YS := fun _ t => 1 + (t : ℂ) * (-1)) (YL := fun _ t => 0 + (t : ℂ) * 1)
    (fun _ _ _ => by simp) le_rfl (fun _ _ => le_rfl) (fun _ => continuous_const) zero_le_one
    zero_le_one (fun x y => by simp) (fun _ _ => odeSolution_affine (fun _ _ => rfl) _ _ _)
    (fun k hk => by rw [Nat.lt_one_iff.1 hk]; simp)
    (fun k hk => by rw [Nat.lt_one_iff.1 hk]; simp)
    (fun k hk => by rw [Nat.lt_one_iff.1 hk]; simpa using isKSLStep)
    (fun k hk => by rw [Nat.lt_one_iff.1 hk]; simp)
    (by simp) 1 le_rfl (by norm_num)

/-- The bound in the previous example is attained. -/
example : ‖(1 + Complex.I) - (1 : ℂ)‖ = 1 * Real.exp ((0 + max 0 0) * 1) * 1
      + 11 * 0 * ‖1 + Complex.I‖ * 1 * Real.exp ((0 + max 0 0) * 1) * 1 := by
  simp

end Examples

end LeanDLRA.Literature.P1803_10473
