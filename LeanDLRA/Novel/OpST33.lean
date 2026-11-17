import LeanDLRA.Novel.KineticAP

/-!
# AP of low-rank implicit steps for nonlinear BGK models (OP-ST-33)

Open problem OP-ST-33 of `docs/catalogue/survey/open-problems.json`, part (b): asymptotic
preservation of
low-rank schemes for *nonlinear* BGK models, where the Maxwellian `M[f]` depends on the state and
has no low-rank form.  `LeanDLRA.Novel.KineticAP` treats the linear case (fixed equilibrium
direction `M`).  Here the equilibrium is `𝓜 (f Ψ)`, an arbitrary function of the moments
`f Ψ ∈ ℝ^{X × J}` of `f ∈ ℝ^{X × V}` against the collision invariants `Ψ ∈ ℝ^{V × J}`, subject
only to moment matching `𝓜 μ Ψ = μ` on an admissible set `A` (`IsMaxwellianOn`); the collision
frequency `ν (f Ψ)` may depend on the state as well.  The implicit low-rank step is the
nonlinear fixed-point problem (`IsBGKStep`)

  `f = P (w + s ν[f] (𝓜[f] - f))`, `P = U Uᵀ · V Vᵀ`, `s = Δt / ε`.

## Results

* `moments_eq`: if the collision invariants lie in the velocity basis (`V Vᵀ Ψ = Ψ`), every
  solution has the moments `f Ψ = U Uᵀ (w Ψ)`, for every `s`: the nonlinearity is resolved by the
  conservation structure, exactly as in the full scheme.
* `existsUnique_bgkStep`: the nonlinear step then has exactly one admissible solution.
* `ceLimit`, `norm_sub_ceLimit_le`, `norm_sub_ceLimit_ge`, `tendsto_ceLimit`: the limit as
  `s → ∞` is the `ν`-weighted Galerkin projection `Π_ν 𝓜[μ*] V Vᵀ` of the Maxwellian of the
  projected moments `μ* = U Uᵀ (w Ψ)`, with the two-sided rate
  `‖P w - y‖ / (1 + s σ₁) ≤ ‖f - y‖ ≤ ‖P w - y‖ / (1 + s σ₀)`.  The weighted projection is the
  orthogonal one for constant `ν` (`ceLimit_const`), where the step is explicit
  (`bgkStep_const_eq`) and the rate is an equality (`norm_sub_const_eq`).
* `ceLimit_eq_iff`: the limit is the Maxwellian itself iff `𝓜[μ*]` lies in the low-rank space;
  `ceLimit_mul_Ψ`, `ceLimit_mul_flux`: its moments are `μ*` and, when `V Vᵀ Φ = Φ` for the flux
  invariants `Φ = diag(v) Ψ`, its kinetic fluxes are `Π_ν 𝓜[μ*] Φ`, the exact Euler flux of the
  Maxwellian when `U` is square (`weightedProj_eq_one`).
* `moment_update_sub_le`, `moment_update_full_sub_le`: for the transport–relaxation scheme, the
  moment update of the low-rank scheme is within `|τ| ‖D‖ ‖Φ‖ ‖P w - y‖ / (1 + s σ₀)` of one step
  `μ ↦ μ - τ D 𝓜[μ] Φ` of the kinetic scheme for the discrete Euler system: the fluid limit is
  captured, with an explicit rate, exactly when `Ψ, Φ ∈ range V`.
* Instance and counterexample on the three-velocity model `v ∈ {-1, 0, 1}` with invariants
  `1, v`: `maxw3` is the exponential-family Maxwellian `exp(a + b v)` with exact discrete
  moments (`isMaxwellianOn_maxw3Map`, `maxw3_exp_family`, `maxw3_pos`); the rank-2 velocity
  basis `V₂ = span {1, v}` contains `Ψ` but not `Φ` (`V₂_captures_Ψ`, `V₂_not_captures_Φ`), its
  limit fluxes are `(j, 2ρ/3)` for *every* Maxwellian model (`p1_flux`), and they differ from
  the Euler flux of `maxw3` as soon as the momentum is nonzero (`maxw3_flux_ne`,
  `ceLimit_flux_ne`): the low-rank scheme is asymptotic preserving towards the wrong, linear,
  fluid limit.

## What is not covered

The admissibility `μ* = U Uᵀ (w Ψ) ∈ A` is a genuine hypothesis: the spatial projection can leave
the realizable set (produce `|j| ≥ ρ` in a cell), and then the nonlinear step has no admissible
solution.  Nothing is said about the velocity basis *not* containing the collision invariants (in
the linear case the mass is lost, `KineticAP.bgk_le_of_not_mem`), about bounds uniform over many
steps, or about parts (a), (c), (d) of OP-ST-33.  Compare arXiv 2502.08951 (penalisation with a
fixed Maxwellian) and
arXiv 2601.11900 (frozen field); the mechanism is the one of `KineticAP.bgk_tendsto_iff`, applied
after the moments are resolved.
-/

open Set Filter Topology
open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius

namespace LeanDLRA.Novel.OpST33

open LeanDLRA LeanDLRA.Frobenius LeanDLRA.Novel.KineticAP

set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

section General

variable {m n J k k' : Type*} [Fintype m] [Fintype n] [Fintype J] [Fintype k] [Fintype k']
  [DecidableEq m] [DecidableEq k] [DecidableEq k']

/-- `𝓜` is a Maxwellian map for the collision invariants `Ψ` on the admissible set `A`: the
equilibrium `𝓜 μ ∈ ℝ^{X × V}` has the prescribed moments `𝓜 μ Ψ = μ`.  Nothing else (no form,
no linearity, no low rank) is assumed. -/
def IsMaxwellianOn (𝓜 : Matrix m J ℝ → Matrix m n ℝ) (Ψ : Matrix n J ℝ)
    (A : Set (Matrix m J ℝ)) : Prop :=
  ∀ μ ∈ A, 𝓜 μ * Ψ = μ

/-- The implicit nonlinear BGK Galerkin step on `range U ⊗ range V`:
`f = U Uᵀ (w + s ν[f Ψ] (𝓜[f Ψ] - f)) V Vᵀ`, with state-dependent collision frequency `ν` and
Maxwellian `𝓜`; `s = Δt / ε`. -/
def IsBGKStep (ν : Matrix m J ℝ → m → ℝ) (𝓜 : Matrix m J ℝ → Matrix m n ℝ) (Ψ : Matrix n J ℝ)
    (U : Matrix m k ℝ) (V : Matrix n k' ℝ) (s : ℝ) (w f : Matrix m n ℝ) : Prop :=
  f = galerkinProj U V (w + s • (Matrix.diagonal (ν (f * Ψ)) * (𝓜 (f * Ψ) - f)))

variable {ν : Matrix m J ℝ → m → ℝ} {𝓜 : Matrix m J ℝ → Matrix m n ℝ} {Ψ : Matrix n J ℝ}
  {U : Matrix m k ℝ} {V : Matrix n k' ℝ} {A : Set (Matrix m J ℝ)} {s : ℝ} {w f : Matrix m n ℝ}
  {σ₀ σ₁ : ℝ}

omit [DecidableEq k] [DecidableEq k'] in
/-- **Conservation resolves the nonlinearity.**  If the collision invariants lie in the velocity
basis, any admissible solution of the nonlinear implicit step has the moments `U Uᵀ (w Ψ)`, for
every `s ≥ 0` and whatever `ν` and `𝓜` are: the Maxwellian of the new state is known before the
step is solved, as in the full-rank scheme. -/
theorem moments_eq (hΨ : V * Vᵀ * Ψ = Ψ) (hM : IsMaxwellianOn 𝓜 Ψ A)
    (hf : IsBGKStep ν 𝓜 Ψ U V s w f) (hA : f * Ψ ∈ A) : f * Ψ = U * Uᵀ * (w * Ψ) := by
  have hΨ' : V * (Vᵀ * Ψ) = Ψ := by rw [← Matrix.mul_assoc]; exact hΨ
  conv_lhs => rw [hf]
  simp only [galerkinProj_apply, Matrix.mul_assoc, hΨ', Matrix.add_mul, Matrix.smul_mul,
    Matrix.sub_mul, hM _ hA, sub_self, Matrix.mul_zero, smul_zero, add_zero]

omit [DecidableEq k] [DecidableEq k'] in
private theorem scatter_isRelaxation {σ : m → ℝ} (hσ : IsCrossSection σ σ₀ σ₁) :
    IsRelaxation (scatter σ : Matrix m J ℝ →L[ℝ] Matrix m J ℝ) where
  symm x y := by
    rw [scatter_apply, scatter_apply, inner_neg_left, inner_neg_right, inner_diagonal_comm]
  nonpos x := by
    rw [scatter_apply, inner_neg_left]
    have h1 := hσ.lower_inner x
    have h2 : 0 ≤ σ₀ * ‖x‖ ^ 2 := by have := hσ.pos; positivity
    linarith

omit [DecidableEq m] [DecidableEq k'] in
private theorem leftProj_idem_mul (hU : Uᵀ * U = 1) (Z : Matrix m J ℝ) :
    U * Uᵀ * (U * Uᵀ * Z) = U * Uᵀ * Z := by
  have hUU : U * Uᵀ * (U * Uᵀ) = U * Uᵀ := by
    rw [Matrix.mul_assoc U Uᵀ (U * Uᵀ), ← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul]
  rw [← Matrix.mul_assoc, hUU]

/-- The projected moments `μ* = U Uᵀ (w Ψ)` are admissible, and the collision frequency there is
a cross-section: then the nonlinear implicit step has exactly one admissible solution. -/
theorem existsUnique_bgkStep (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hΨ : V * Vᵀ * Ψ = Ψ)
    (hM : IsMaxwellianOn 𝓜 Ψ A) (hμ : U * Uᵀ * (w * Ψ) ∈ A)
    (hν : IsCrossSection (ν (U * Uᵀ * (w * Ψ))) σ₀ σ₁) (hs : 0 ≤ s) :
    ∃! f, IsBGKStep ν 𝓜 Ψ U V s w f ∧ f * Ψ ∈ A := by
  set μ := U * Uᵀ * (w * Ψ) with hμdef
  set σ := ν μ with hσdef
  set M := 𝓜 μ with hMdef
  have hP := isOrthProj_galerkinProj (n := n) hU hV
  have hC := scatter_isRelaxation (J := n) hν
  have hMΨ : M * Ψ = μ := hM μ hμ
  have hμU : U * Uᵀ * μ = μ := leftProj_idem_mul hU _
  have hΨ' : V * (Vᵀ * Ψ) = Ψ := by rw [← Matrix.mul_assoc]; exact hΨ
  -- the moment equation of the linear problem with Maxwellian `M`
  have hmom : ∀ g : Matrix m n ℝ,
      g = galerkinProj U V (w + s • (scatter σ g + Matrix.diagonal σ * M)) →
      g * Ψ - μ = leftProj U (0 + s • (scatter σ (g * Ψ - μ) + 0)) := by
    intro g hg
    have h2 : (w + s • (scatter σ g + Matrix.diagonal σ * M)) * Ψ =
        w * Ψ + s • (Matrix.diagonal σ * (μ - g * Ψ)) := by
      simp only [Matrix.add_mul, Matrix.smul_mul, scatter_apply, Matrix.neg_mul, Matrix.mul_assoc,
        hMΨ, Matrix.mul_sub]
      abel_nf
    have h1 : g * Ψ = μ + s • (U * Uᵀ * (Matrix.diagonal σ * (μ - g * Ψ))) := by
      conv_lhs => rw [hg]
      rw [galerkinProj_apply, Matrix.mul_assoc _ (V * Vᵀ), hΨ, Matrix.mul_assoc (U * Uᵀ), h2,
        Matrix.mul_add, Matrix.mul_smul]
    simp only [leftProj_apply, scatter_apply, zero_add, add_zero, Matrix.mul_neg, Matrix.mul_smul]
    rw [sub_eq_iff_eq_add]
    conv_lhs => rw [h1]
    rw [← neg_sub, Matrix.mul_neg, Matrix.mul_neg, smul_neg]
    abel
  obtain ⟨f, hf, -⟩ := existsUnique_step hP hC hs w (Matrix.diagonal σ * M)
  have hCJ := scatter_isRelaxation (J := J) hν
  obtain ⟨v₀, -, huniq⟩ := existsUnique_step (isOrthProj_leftProj (n := J) hU) hCJ hs
    (0 : Matrix m J ℝ) 0
  have hδ0 : ∀ g : Matrix m n ℝ,
      g = galerkinProj U V (w + s • (scatter σ g + Matrix.diagonal σ * M)) → g * Ψ = μ := by
    intro g hg
    have h1 := huniq _ (hmom g hg)
    have h2 := huniq 0 (by simp)
    exact sub_eq_zero.1 (h1.trans h2.symm)
  have hfΨ : f * Ψ = μ := hδ0 f hf
  refine ⟨f, ⟨?_, by rw [hfΨ]; exact hμ⟩, ?_⟩
  · unfold IsBGKStep
    rw [hfΨ, ← hσdef, ← hMdef, Matrix.mul_sub, ← neg_add_eq_sub, ← scatter_apply]
    exact hf
  · rintro f' ⟨hf', hA'⟩
    have hf'Ψ : f' * Ψ = μ := moments_eq hΨ hM hf' hA'
    have hlin : f' = galerkinProj U V (w + s • (scatter σ f' + Matrix.diagonal σ * M)) := by
      have := hf'
      unfold IsBGKStep at this
      rw [hf'Ψ, ← hσdef, ← hMdef, Matrix.mul_sub, ← neg_add_eq_sub, ← scatter_apply] at this
      exact this
    obtain ⟨v₁, -, huniq'⟩ := existsUnique_step hP hC hs w (Matrix.diagonal σ * M)
    rw [huniq' f' hlin, huniq' f hf]

/-! ### The limit `s → ∞` and its rate -/

/-- The `σ`-weighted projection `U (Uᵀ σ U)⁻¹ Uᵀ σ` onto `range U` (`weightedProj_mul_self`,
`leftProj_mul_weightedProj`): the orthogonal projection `U Uᵀ` for constant `σ`
(`weightedProj_const`) and the identity when `U` is square (`weightedProj_eq_one`). -/
noncomputable def weightedProj (σ : m → ℝ) (U : Matrix m k ℝ) : Matrix m m ℝ :=
  U * (stiffness σ U)⁻¹ * Uᵀ * Matrix.diagonal σ

/-- The limit of the implicit low-rank step as `s → ∞`, for the Maxwellian `M` of the projected
moments: the `σ`-weighted Galerkin projection `Π_σ M V Vᵀ` of `M` onto `range U ⊗ range V`
(`galerkinProj_ceLimit`, `ceLimit_limitEq`, `norm_sub_ceLimit_le`). -/
noncomputable def ceLimit (σ : m → ℝ) (U : Matrix m k ℝ) (V : Matrix n k' ℝ)
    (M : Matrix m n ℝ) : Matrix m n ℝ :=
  weightedProj σ U * M * (V * Vᵀ)

variable {σ : m → ℝ} {M : Matrix m n ℝ}

theorem weightedProj_mul_self (hσ : IsCrossSection σ σ₀ σ₁) (hU : Uᵀ * U = 1) :
    weightedProj σ U * U = U := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 (hσ.isUnit_stiffness hU)
  unfold weightedProj
  rw [Matrix.mul_assoc _ (Matrix.diagonal σ), Matrix.mul_assoc _ Uᵀ,
    ← Matrix.mul_assoc Uᵀ, ← stiffness, Matrix.mul_assoc U, Matrix.nonsing_inv_mul _ hdet,
    Matrix.mul_one]

theorem leftProj_mul_weightedProj (hU : Uᵀ * U = 1) :
    U * Uᵀ * weightedProj σ U = weightedProj σ U := by
  unfold weightedProj
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul]

private theorem transpose_diagonal_weightedProj (hσ : IsCrossSection σ σ₀ σ₁) (hU : Uᵀ * U = 1)
    (X : Matrix m n ℝ) :
    Uᵀ * (Matrix.diagonal σ * (weightedProj σ U * X)) = Uᵀ * (Matrix.diagonal σ * X) := by
  unfold weightedProj
  have h : Uᵀ * (Matrix.diagonal σ * (U * (stiffness σ U)⁻¹ * Uᵀ * Matrix.diagonal σ * X)) =
      stiffness σ U * (stiffness σ U)⁻¹ * (Uᵀ * (Matrix.diagonal σ * X)) := by
    rw [stiffness]; simp only [Matrix.mul_assoc]
  rw [h, stiffness_mul_inv hσ hU, Matrix.one_mul]

theorem galerkinProj_ceLimit (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    galerkinProj U V (ceLimit σ U V M) = ceLimit σ U V M := by
  have hVV : V * Vᵀ * (V * Vᵀ) = V * Vᵀ := by
    rw [Matrix.mul_assoc V Vᵀ, ← Matrix.mul_assoc Vᵀ V, hV, Matrix.one_mul]
  rw [galerkinProj_apply, ceLimit]
  calc U * Uᵀ * (weightedProj σ U * M * (V * Vᵀ)) * (V * Vᵀ)
      = (U * Uᵀ * weightedProj σ U) * M * ((V * Vᵀ) * (V * Vᵀ)) := by
        simp only [Matrix.mul_assoc]
    _ = weightedProj σ U * M * (V * Vᵀ) := by rw [leftProj_mul_weightedProj hU, hVV]

/-- `ceLimit` solves the Galerkin Chapman–Enskog problem `P (σ (M - y)) = 0`. -/
theorem ceLimit_limitEq (hσ : IsCrossSection σ σ₀ σ₁) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    galerkinProj U V (scatter σ (ceLimit σ U V M) + Matrix.diagonal σ * M) = 0 := by
  have hVV : Vᵀ * (V * Vᵀ) = Vᵀ := by rw [← Matrix.mul_assoc, hV, Matrix.one_mul]
  rw [galerkinProj_apply, scatter_apply, ceLimit]
  simp only [Matrix.mul_add, Matrix.mul_neg, Matrix.add_mul, Matrix.neg_mul, Matrix.mul_assoc, hVV,
    transpose_diagonal_weightedProj hσ hU]
  exact neg_add_cancel _

omit [DecidableEq k] [DecidableEq k'] in
/-- Once the moments are known, the nonlinear step is the linear implicit step with the fixed
Maxwellian `𝓜 μ*` and cross-section `ν μ*`. -/
theorem IsBGKStep.eq_linear (hΨ : V * Vᵀ * Ψ = Ψ) (hM : IsMaxwellianOn 𝓜 Ψ A)
    (hf : IsBGKStep ν 𝓜 Ψ U V s w f) (hA : f * Ψ ∈ A) :
    f = galerkinProj U V (w + s • (scatter (ν (U * Uᵀ * (w * Ψ))) f +
      Matrix.diagonal (ν (U * Uᵀ * (w * Ψ))) * 𝓜 (U * Uᵀ * (w * Ψ)))) := by
  have hfΨ := moments_eq hΨ hM hf hA
  have := hf
  unfold IsBGKStep at this
  rw [hfΨ, Matrix.mul_sub, ← neg_add_eq_sub, ← scatter_apply] at this
  exact this

/-- **Rate of the nonlinear low-rank BGK step.**  With the collision invariants in the velocity
basis, the admissible solution of the nonlinear implicit step satisfies
`‖f - y‖ ≤ ‖P w - y‖ / (1 + s σ₀)`, where `y = ceLimit` is the `ν`-weighted projection of the
Maxwellian `𝓜 μ*` of the projected moments `μ* = U Uᵀ (w Ψ)` and `σ₀` the lower bound of the
collision frequency at `μ*`.  The gap is the full `σ₀`: no loss from the low-rank constraint and
none from the nonlinearity.  Compare `KineticAP.bgk_le_of_mem` (linear case). -/
theorem norm_sub_ceLimit_le (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hΨ : V * Vᵀ * Ψ = Ψ)
    (hM : IsMaxwellianOn 𝓜 Ψ A) (hν : IsCrossSection (ν (U * Uᵀ * (w * Ψ))) σ₀ σ₁) (hs : 0 ≤ s)
    (hf : IsBGKStep ν 𝓜 Ψ U V s w f) (hA : f * Ψ ∈ A) :
    ‖f - ceLimit (ν (U * Uᵀ * (w * Ψ))) U V (𝓜 (U * Uᵀ * (w * Ψ)))‖ ≤
      ‖galerkinProj U V w - ceLimit (ν (U * Uᵀ * (w * Ψ))) U V (𝓜 (U * Uᵀ * (w * Ψ)))‖ /
        (1 + s * σ₀) := by
  refine coercive_relax_le (isOrthProj_galerkinProj hU hV) hν.pos.le ?_ hs
    (hf.eq_linear hΨ hM hA) (galerkinProj_ceLimit hU hV) (ceLimit_limitEq hν hU hV)
  intro x _
  rw [scatter_apply, inner_neg_left, neg_neg]
  exact hν.lower_inner x

/-- The matching lower bound `‖P w - y‖ ≤ (1 + s σ₁) ‖f - y‖`: the rate `1 / (1 + s σ)` is exact
up to the ratio `σ₁ / σ₀` of the collision frequency. -/
theorem norm_sub_ceLimit_ge (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hΨ : V * Vᵀ * Ψ = Ψ)
    (hM : IsMaxwellianOn 𝓜 Ψ A) (hν : IsCrossSection (ν (U * Uᵀ * (w * Ψ))) σ₀ σ₁) (hs : 0 ≤ s)
    (hf : IsBGKStep ν 𝓜 Ψ U V s w f) (hA : f * Ψ ∈ A) :
    ‖galerkinProj U V w - ceLimit (ν (U * Uᵀ * (w * Ψ))) U V (𝓜 (U * Uᵀ * (w * Ψ)))‖ ≤
      (1 + s * σ₁) * ‖f - ceLimit (ν (U * Uᵀ * (w * Ψ))) U V (𝓜 (U * Uᵀ * (w * Ψ)))‖ := by
  have hP := isOrthProj_galerkinProj (n := n) hU hV
  refine coercive_relax_ge hP ?_ hs (hf.eq_linear hΨ hM hA) (galerkinProj_ceLimit hU hV)
    (ceLimit_limitEq hν hU hV)
  intro x _
  rw [scatter_apply, map_neg, norm_neg]
  exact (hP.norm_le _).trans (hν.norm_diagonal_mul_le x)

/-- **The limit of the nonlinear low-rank step** as `s = Δt/ε → ∞` is `ceLimit`: the weighted
projection of the Maxwellian of the projected moments. -/
theorem tendsto_ceLimit (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hΨ : V * Vᵀ * Ψ = Ψ)
    (hM : IsMaxwellianOn 𝓜 Ψ A) (hν : IsCrossSection (ν (U * Uᵀ * (w * Ψ))) σ₀ σ₁)
    {f : ℝ → Matrix m n ℝ} (hf : ∀ s, 0 ≤ s → IsBGKStep ν 𝓜 Ψ U V s w (f s))
    (hA : ∀ s, 0 ≤ s → f s * Ψ ∈ A) :
    Tendsto f atTop (𝓝 (ceLimit (ν (U * Uᵀ * (w * Ψ))) U V (𝓜 (U * Uᵀ * (w * Ψ))))) := by
  have hlim : Tendsto (fun s : ℝ =>
      ‖galerkinProj U V w - ceLimit (ν (U * Uᵀ * (w * Ψ))) U V (𝓜 (U * Uᵀ * (w * Ψ)))‖ /
        (1 + s * σ₀)) atTop (𝓝 0) :=
    Tendsto.const_div_atTop
      (tendsto_atTop_add_const_left _ _ (tendsto_id.atTop_mul_const hν.pos)) _
  refine tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim)
  filter_upwards [eventually_ge_atTop 0] with s hs using
    norm_sub_ceLimit_le hU hV hΨ hM hν hs (hf s hs) (hA s hs)

/-- The limit is the Maxwellian itself iff the Maxwellian lies in the low-rank space. -/
theorem ceLimit_eq_iff (hσ : IsCrossSection σ σ₀ σ₁) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    ceLimit σ U V M = M ↔ galerkinProj U V M = M := by
  constructor
  · intro h
    have := galerkinProj_ceLimit (σ := σ) (M := M) hU hV
    rwa [h] at this
  · intro h
    have hVV : V * Vᵀ * (V * Vᵀ) = V * Vᵀ := by
      rw [Matrix.mul_assoc V Vᵀ, ← Matrix.mul_assoc Vᵀ V, hV, Matrix.one_mul]
    rw [ceLimit]
    conv_lhs => rw [← h, galerkinProj_apply]
    calc weightedProj σ U * (U * Uᵀ * M * (V * Vᵀ)) * (V * Vᵀ)
        = (weightedProj σ U * U) * Uᵀ * M * ((V * Vᵀ) * (V * Vᵀ)) := by
          simp only [Matrix.mul_assoc]
      _ = M := by rw [weightedProj_mul_self hσ hU, hVV, ← galerkinProj_apply, h]

omit [DecidableEq k'] in
/-- The moments of the limit are the projected moments `μ*`. -/
theorem ceLimit_mul_Ψ (hσ : IsCrossSection σ σ₀ σ₁) (hU : Uᵀ * U = 1) (hΨ : V * Vᵀ * Ψ = Ψ)
    {μ : Matrix m J ℝ} (hMΨ : M * Ψ = μ) (hμU : U * Uᵀ * μ = μ) : ceLimit σ U V M * Ψ = μ := by
  have hW : weightedProj σ U * μ = μ := by
    conv_lhs => rw [← hμU]
    rw [Matrix.mul_assoc U, ← Matrix.mul_assoc _ U, weightedProj_mul_self hσ hU,
      ← Matrix.mul_assoc, hμU]
  rw [ceLimit, Matrix.mul_assoc, hΨ, Matrix.mul_assoc, hMΨ, hW]

omit [DecidableEq k'] in
/-- If the flux invariants `Φ = diag(v) Ψ` lie in the velocity basis, the kinetic fluxes of the
limit are the weighted projection of the Euler flux `M Φ` of the Maxwellian. -/
theorem ceLimit_mul_flux {Φ : Matrix n J ℝ} (hΦ : V * Vᵀ * Φ = Φ) :
    ceLimit σ U V M * Φ = weightedProj σ U * (M * Φ) := by
  rw [ceLimit, Matrix.mul_assoc, hΦ, Matrix.mul_assoc]

/-- For a square (full) spatial basis the weighted projection is the identity. -/
theorem weightedProj_eq_one (hσ : IsCrossSection σ σ₀ σ₁) (hU : Uᵀ * U = 1)
    (hU' : U * Uᵀ = 1) : weightedProj σ U = 1 := by
  have hne : ∀ i, σ i ≠ 0 := fun i => (hσ.pos.trans_le (hσ.lower i)).ne'
  have hDD : Matrix.diagonal σ * Matrix.diagonal (fun i => (σ i)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    exact mul_inv_cancel₀ (hne i)
  have hDD' : Matrix.diagonal (fun i => (σ i)⁻¹) * Matrix.diagonal σ = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    exact inv_mul_cancel₀ (hne i)
  have hinv : (stiffness σ U)⁻¹ = Uᵀ * Matrix.diagonal (fun i => (σ i)⁻¹) * U := by
    apply Matrix.inv_eq_right_inv
    rw [stiffness]
    calc Uᵀ * Matrix.diagonal σ * U * (Uᵀ * Matrix.diagonal (fun i => (σ i)⁻¹) * U)
        = Uᵀ * (Matrix.diagonal σ * ((U * Uᵀ) * (Matrix.diagonal (fun i => (σ i)⁻¹) * U))) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU', Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal σ), hDD,
          Matrix.one_mul, hU]
  unfold weightedProj
  rw [hinv]
  calc U * (Uᵀ * Matrix.diagonal (fun i => (σ i)⁻¹) * U) * Uᵀ * Matrix.diagonal σ
      = (U * Uᵀ) * (Matrix.diagonal (fun i => (σ i)⁻¹) * ((U * Uᵀ) * Matrix.diagonal σ)) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hU', Matrix.one_mul, Matrix.one_mul, hDD']

/-- For a constant collision frequency the weighted projection is the orthogonal one. -/
theorem weightedProj_const {c : ℝ} (hc : 0 < c) (hU : Uᵀ * U = 1) :
    weightedProj (fun _ : m => c) U = U * Uᵀ := by
  have hS : stiffness (fun _ : m => c) U = c • (1 : Matrix k k ℝ) := by
    rw [stiffness, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      hU]
  have hinv : (stiffness (fun _ : m => c) U)⁻¹ = c⁻¹ • (1 : Matrix k k ℝ) := by
    apply Matrix.inv_eq_right_inv
    rw [hS, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc.ne', one_smul,
      Matrix.one_mul]
  unfold weightedProj
  rw [hinv, ← Matrix.smul_one_eq_diagonal]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul, mul_inv_cancel₀ hc.ne',
    one_smul]

omit [DecidableEq k'] in
/-- For constant collision frequency the limit is the orthogonal projection `P M` of the
Maxwellian onto the low-rank space. -/
theorem ceLimit_const {c : ℝ} (hc : 0 < c) (hU : Uᵀ * U = 1) :
    ceLimit (fun _ : m => c) U V M = galerkinProj U V M := by
  rw [ceLimit, weightedProj_const hc hU, galerkinProj_apply]

/-- **Constant collision frequency: the nonlinear step is explicit.**  With `Ψ ∈ range V` the
unique admissible solution is `f = (P w + s c P 𝓜[μ*]) / (1 + s c)`: the implicit nonlinear
problem reduces to one evaluation of the Maxwellian at the projected moments. -/
theorem bgkStep_const_eq {c : ℝ} (hc : 0 < c) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hΨ : V * Vᵀ * Ψ = Ψ) (hM : IsMaxwellianOn 𝓜 Ψ A) (hs : 0 ≤ s)
    (hf : IsBGKStep (fun _ _ => c) 𝓜 Ψ U V s w f) (hA : f * Ψ ∈ A) :
    f = (1 + s * c)⁻¹ •
      (galerkinProj U V w + (s * c) • galerkinProj U V (𝓜 (U * Uᵀ * (w * Ψ)))) := by
  have hP := isOrthProj_galerkinProj (n := n) hU hV
  have hlin := hf.eq_linear hΨ hM hA
  have hPf : galerkinProj U V f = f := by
    rw [hlin]
    exact hP.idem _
  have h1 : f = galerkinProj U V w + (s * c) • galerkinProj U V (𝓜 (U * Uᵀ * (w * Ψ))) -
      (s * c) • f := by
    conv_lhs => rw [hlin]
    rw [scatter_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul,
      Matrix.smul_mul, Matrix.one_mul, map_add, map_smul, map_add, map_neg, map_smul, map_smul,
      hPf, smul_add, smul_neg, smul_smul, smul_smul]
    abel_nf
  have h2 : (1 + s * c) • f = galerkinProj U V w +
      (s * c) • galerkinProj U V (𝓜 (U * Uᵀ * (w * Ψ))) := by
    have h3 := congrArg (fun z => z + (s * c) • f) h1
    simp only [sub_add_cancel] at h3
    rw [add_smul, one_smul]
    exact h3
  have hpos : (1 + s * c) ≠ 0 := by positivity
  rw [← h2, smul_smul, inv_mul_cancel₀ hpos, one_smul]

/-- **Constant collision frequency: the rate is an equality**,
`‖f - P 𝓜[μ*]‖ = ‖P (w - 𝓜[μ*])‖ / (1 + s c)`.  The AP defect of the limit is therefore exactly
`‖(1 - P) 𝓜[μ*]‖`, the distance of the Maxwellian of the projected moments to the low-rank
space. -/
theorem norm_sub_const_eq {c : ℝ} (hc : 0 < c) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hΨ : V * Vᵀ * Ψ = Ψ) (hM : IsMaxwellianOn 𝓜 Ψ A) (hs : 0 ≤ s)
    (hf : IsBGKStep (fun _ _ => c) 𝓜 Ψ U V s w f) (hA : f * Ψ ∈ A) :
    ‖f - galerkinProj U V (𝓜 (U * Uᵀ * (w * Ψ)))‖ =
      ‖galerkinProj U V (w - 𝓜 (U * Uᵀ * (w * Ψ)))‖ / (1 + s * c) := by
  have hpos : 0 < 1 + s * c := by positivity
  set PM := galerkinProj U V (𝓜 (U * Uᵀ * (w * Ψ))) with hPM
  set Pw := galerkinProj U V w with hPw
  have hk : (1 + s * c)⁻¹ * (s * c) - 1 = -(1 + s * c)⁻¹ := by
    field_simp
    ring
  have h1 : (1 + s * c)⁻¹ • (Pw + (s * c) • PM) - PM = (1 + s * c)⁻¹ • (Pw - PM) := by
    calc (1 + s * c)⁻¹ • (Pw + (s * c) • PM) - PM
        = (1 + s * c)⁻¹ • Pw + ((1 + s * c)⁻¹ * (s * c) - 1) • PM := by
          simp only [smul_add, smul_smul, sub_smul, one_smul]
          abel
      _ = (1 + s * c)⁻¹ • (Pw - PM) := by rw [hk, neg_smul, ← sub_eq_add_neg, ← smul_sub]
  rw [bgkStep_const_eq hc hU hV hΨ hM hs hf hA, ← hPM, ← hPw, h1, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.2 hpos.le), div_eq_inv_mul, map_sub]

/-! ### The fluid limit: moments of the transport–relaxation scheme -/

section Fluid

variable [DecidableEq n]

omit [DecidableEq k] [DecidableEq k'] in
/-- The explicit transport step `g ↦ g - τ D g diag(v)`: `D` a spatial difference operator, `v`
the velocities. -/
def transport (D : Matrix m m ℝ) (v : n → ℝ) (τ : ℝ) (g : Matrix m n ℝ) : Matrix m n ℝ :=
  g - τ • (D * g * Matrix.diagonal v)

omit [DecidableEq m] [DecidableEq k] [DecidableEq k'] in
/-- The moments after transport: `μ - τ D (g Φ)` with the kinetic fluxes `g Φ`, `Φ = diag(v) Ψ`. -/
theorem transport_mul (D : Matrix m m ℝ) (v : n → ℝ) (τ : ℝ) (g : Matrix m n ℝ)
    (Ψ : Matrix n J ℝ) :
    transport D v τ g * Ψ = g * Ψ - τ • (D * (g * (Matrix.diagonal v * Ψ))) := by
  simp only [transport, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc]

omit [DecidableEq k'] in
/-- **The limit scheme is a kinetic scheme for the Euler system.**  In the limit `s → ∞` the
state after relaxation is `y = ceLimit σ U V M` with `M = 𝓜 μ`; if `Ψ` and `Φ = diag(v) Ψ` lie
in the velocity basis, the projected moments after the next transport step are
`U Uᵀ (μ - τ D Π_σ (M Φ))`: the moments move by the Euler flux `F(μ) = 𝓜(μ) Φ` of the Maxwellian,
filtered by the spatial basis (`weightedProj_eq_one`: no filter for a full spatial basis). -/
theorem limit_moment_update (hσ : IsCrossSection σ σ₀ σ₁) (hU : Uᵀ * U = 1)
    (hΨ : V * Vᵀ * Ψ = Ψ) {v : n → ℝ}
    (hΦ : V * Vᵀ * (Matrix.diagonal v * Ψ) = Matrix.diagonal v * Ψ) {μ : Matrix m J ℝ}
    (hMΨ : M * Ψ = μ) (hμU : U * Uᵀ * μ = μ) (D : Matrix m m ℝ) (τ : ℝ) :
    U * Uᵀ * (transport D v τ (ceLimit σ U V M) * Ψ) =
      U * Uᵀ * (μ - τ • (D * (weightedProj σ U * (M * (Matrix.diagonal v * Ψ))))) := by
  rw [transport_mul, ceLimit_mul_Ψ hσ hU hΨ hMΨ hμU, ceLimit_mul_flux hΦ]

/-- **The fluid limit is captured, with a rate.**  Let `f` be the admissible relaxation output
from `w` (moments `μ* = U Uᵀ (w Ψ)`), and `f'` the admissible relaxation output after the transport
step applied to `f` (with any `s'`).  If `Ψ` and `Φ = diag(v) Ψ` lie in the velocity basis, the
moments of `f'` differ from one step `U Uᵀ (μ* - τ D Π_ν 𝓜[μ*] Φ)` of the (spatially filtered)
kinetic Euler scheme by at most `|τ| ‖D‖ ‖Φ‖ ‖P w - y‖ / (1 + s σ₀)`. -/
theorem moment_update_sub_le (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hΨ : V * Vᵀ * Ψ = Ψ)
    (hM : IsMaxwellianOn 𝓜 Ψ A) (hν : IsCrossSection (ν (U * Uᵀ * (w * Ψ))) σ₀ σ₁) (hs : 0 ≤ s)
    (hf : IsBGKStep ν 𝓜 Ψ U V s w f) (hA : f * Ψ ∈ A) {D : Matrix m m ℝ} {v : n → ℝ} {τ s' : ℝ}
    (hΦ : V * Vᵀ * (Matrix.diagonal v * Ψ) = Matrix.diagonal v * Ψ) {f' : Matrix m n ℝ}
    (hf' : IsBGKStep ν 𝓜 Ψ U V s' (transport D v τ f) f') (hA' : f' * Ψ ∈ A) :
    ‖f' * Ψ - U * Uᵀ * (U * Uᵀ * (w * Ψ) - τ • (D * (weightedProj (ν (U * Uᵀ * (w * Ψ))) U *
        (𝓜 (U * Uᵀ * (w * Ψ)) * (Matrix.diagonal v * Ψ)))))‖ ≤
      |τ| * ‖D‖ * ‖Matrix.diagonal v * Ψ‖ *
        (‖galerkinProj U V w - ceLimit (ν (U * Uᵀ * (w * Ψ))) U V (𝓜 (U * Uᵀ * (w * Ψ)))‖ /
          (1 + s * σ₀)) := by
  set μ := U * Uᵀ * (w * Ψ) with hμdef
  set y := ceLimit (ν μ) U V (𝓜 μ) with hy
  set Φ := Matrix.diagonal v * Ψ with hΦdef
  have hfΨ : f * Ψ = μ := moments_eq hΨ hM hf hA
  have hμA : μ ∈ A := hfΨ ▸ hA
  have hμU : U * Uᵀ * μ = μ := leftProj_idem_mul hU _
  have hyΨ : y * Ψ = μ := ceLimit_mul_Ψ hν hU hΨ (hM μ hμA) hμU
  have hf'Ψ := moments_eq hΨ hM hf' hA'
  have hdiff : f' * Ψ - U * Uᵀ * (μ - τ • (D * (weightedProj (ν μ) U * (𝓜 μ * Φ)))) =
      U * Uᵀ * (-(τ • (D * ((f - y) * Φ)))) := by
    rw [hf'Ψ, transport_mul, hfΨ, ← ceLimit_mul_flux hΦ, ← hy, ← hyΨ, ← Matrix.mul_sub]
    congr 1
    simp only [Matrix.sub_mul, Matrix.mul_sub, smul_sub]
    abel
  have hfy := norm_sub_ceLimit_le hU hV hΨ hM hν hs hf hA
  rw [hdiff]
  calc ‖U * Uᵀ * (-(τ • (D * ((f - y) * Φ))))‖
      ≤ ‖-(τ • (D * ((f - y) * Φ)))‖ := (isOrthProj_leftProj (n := J) hU).norm_le _
    _ = |τ| * ‖D * ((f - y) * Φ)‖ := by rw [norm_neg, norm_smul, Real.norm_eq_abs]
    _ ≤ |τ| * (‖D‖ * (‖f - y‖ * ‖Φ‖)) := by
        gcongr
        exact (Frobenius.norm_mul_le _ _).trans (by gcongr; exact Frobenius.norm_mul_le _ _)
    _ ≤ |τ| * (‖D‖ * ((‖galerkinProj U V w - y‖ / (1 + s * σ₀)) * ‖Φ‖)) := by gcongr
    _ = _ := by ring

/-- **Full spatial resolution: the fluid limit is the kinetic Euler scheme.**  With a square
spatial basis (`U Uᵀ = 1`) and `Ψ, Φ ∈ range V`, the moments of the low-rank scheme are within
`|τ| ‖D‖ ‖Φ‖ ‖P w - y‖ / (1 + s σ₀)` of `μ - τ D 𝓜(μ) Φ`, one step of the explicit kinetic
scheme for the discrete Euler system with the exact Maxwellian flux: the velocity rank
needed for the fluid limit is the number of independent columns of `(Ψ, diag(v) Ψ)`, not the
rank of the Maxwellian. -/
theorem moment_update_full_sub_le (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1) (hV : Vᵀ * V = 1)
    (hΨ : V * Vᵀ * Ψ = Ψ) (hM : IsMaxwellianOn 𝓜 Ψ A) (hν : IsCrossSection (ν (w * Ψ)) σ₀ σ₁)
    (hs : 0 ≤ s) (hf : IsBGKStep ν 𝓜 Ψ U V s w f) (hA : f * Ψ ∈ A) {D : Matrix m m ℝ}
    {v : n → ℝ} {τ s' : ℝ} (hΦ : V * Vᵀ * (Matrix.diagonal v * Ψ) = Matrix.diagonal v * Ψ)
    {f' : Matrix m n ℝ} (hf' : IsBGKStep ν 𝓜 Ψ U V s' (transport D v τ f) f') (hA' : f' * Ψ ∈ A) :
    ‖f' * Ψ - (w * Ψ - τ • (D * (𝓜 (w * Ψ) * (Matrix.diagonal v * Ψ))))‖ ≤
      |τ| * ‖D‖ * ‖Matrix.diagonal v * Ψ‖ *
        (‖galerkinProj U V w - ceLimit (ν (w * Ψ)) U V (𝓜 (w * Ψ))‖ / (1 + s * σ₀)) := by
  have hν' : IsCrossSection (ν (U * Uᵀ * (w * Ψ))) σ₀ σ₁ := by rwa [hU', Matrix.one_mul]
  have h := moment_update_sub_le hU hV hΨ hM hν' hs hf hA hΦ hf' hA'
  simp only [hU', Matrix.one_mul] at h
  rwa [weightedProj_eq_one hν hU hU', Matrix.one_mul] at h

end Fluid

end General

/-! ### Instance and counterexample: three velocities, invariants `1, v` -/

section ThreeVelocity

variable {m : Type*} [Fintype m]

/-- The velocities `-1, 0, 1`. -/
def vel3 : Fin 3 → ℝ := ![-1, 0, 1]

/-- The collision invariants `1` and `v` of the three-velocity model, as columns. -/
def Ψ3 : Matrix (Fin 3) (Fin 2) ℝ := !![1, -1; 1, 0; 1, 1]

/-- The flux invariants `v, v²` of the three-velocity model, as columns. -/
def Φ3 : Matrix (Fin 3) (Fin 2) ℝ := !![-1, 1; 0, 0; 1, 1]

theorem diagonal_vel3_mul_Ψ3 : Matrix.diagonal vel3 * Ψ3 = Φ3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vel3, Ψ3, Φ3, Matrix.mul_apply, Fin.sum_univ_three]

/-- The parameter `t = e^b` of the exponential-family Maxwellian `exp(a + b v)` with mean velocity
`u ∈ (-1, 1)`: the positive root of `(1 - u) t² - u t - (1 + u) = 0`. -/
noncomputable def maxwT (u : ℝ) : ℝ := (u + √(4 - 3 * u ^ 2)) / (2 * (1 - u))

theorem maxwT_root {u : ℝ} (hu : |u| < 1) :
    (1 - u) * maxwT u ^ 2 - u * maxwT u - (1 + u) = 0 := by
  have hu1 : 0 < 1 - u := by linarith [(abs_lt.1 hu).2]
  have hu2 : u ^ 2 < 1 := by nlinarith [abs_lt.1 hu, abs_nonneg u, sq_abs u]
  set r := √(4 - 3 * u ^ 2) with hr
  have hr2 : r ^ 2 = 4 - 3 * u ^ 2 := Real.sq_sqrt (by nlinarith)
  set t := maxwT u with ht
  have htdef : 2 * (1 - u) * t = u + r := by
    rw [ht, maxwT, ← hr, mul_div_cancel₀ _ (by positivity)]
  have h4 : 4 * (1 - u) * ((1 - u) * t ^ 2 - u * t - (1 + u)) = 0 := by
    linear_combination (2 * (1 - u) * t + (u + r) - 2 * u) * htdef + hr2
  rcases mul_eq_zero.1 h4 with h | h
  · exact absurd h (by positivity)
  · exact h

theorem maxwT_pos {u : ℝ} (hu : |u| < 1) : 0 < maxwT u := by
  have hu1 : 0 < 1 - u := by linarith [(abs_lt.1 hu).2]
  have hu2 : u ^ 2 < 1 := by nlinarith [abs_lt.1 hu, abs_nonneg u, sq_abs u]
  have hlt : |u| < √(4 - 3 * u ^ 2) := by
    rw [Real.lt_sqrt (abs_nonneg u), sq_abs]
    linarith
  have : 0 < u + √(4 - 3 * u ^ 2) := by linarith [neg_abs_le u]
  exact div_pos this (by positivity)

theorem maxwT_eq_one_iff {u : ℝ} (hu : |u| < 1) : maxwT u = 1 ↔ u = 0 := by
  constructor
  · intro h
    have := maxwT_root hu
    rw [h] at this
    linarith
  · rintro rfl
    have h4 : √(4 - 3 * (0 : ℝ) ^ 2) = 2 := by
      rw [show (4 : ℝ) - 3 * 0 ^ 2 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [maxwT, h4]
    norm_num

/-- The discrete Maxwellian with density `ρ` and momentum `j` on the velocities `-1, 0, 1`:
`c (t⁻¹, 1, t)` with `t = maxwT (j / ρ)` and `c = ρ / (t⁻¹ + 1 + t)`.  It is the exponential
family member `exp(a + b v)`, `e^a = c`, `e^b = t` (`maxw3_exp_family`), with the exact discrete
moments `ρ, j` (`maxw3_mass`, `maxw3_momentum`) whenever `|j| < ρ`: a genuinely nonlinear
function of the moments. -/
noncomputable def maxw3 (ρ j : ℝ) : Fin 3 → ℝ :=
  ![ρ / ((maxwT (j / ρ))⁻¹ + 1 + maxwT (j / ρ)) * (maxwT (j / ρ))⁻¹,
    ρ / ((maxwT (j / ρ))⁻¹ + 1 + maxwT (j / ρ)),
    ρ / ((maxwT (j / ρ))⁻¹ + 1 + maxwT (j / ρ)) * maxwT (j / ρ)]

/-- The realizable moments of the three-velocity model: `|j| < ρ` in every cell. -/
def realizable3 : Set (Matrix m (Fin 2) ℝ) := {μ | ∀ x, |μ x 1| < μ x 0}

/-- The Maxwellian map `μ ↦ 𝓜 μ`, cell by cell. -/
noncomputable def maxw3Map (μ : Matrix m (Fin 2) ℝ) : Matrix m (Fin 3) ℝ :=
  Matrix.of fun x i => maxw3 (μ x 0) (μ x 1) i

variable {ρ j : ℝ}

private theorem abs_div_lt_one (h : |j| < ρ) : |j / ρ| < 1 := by
  have hρ : 0 < ρ := (abs_nonneg j).trans_lt h
  rw [abs_div, abs_of_pos hρ, div_lt_one hρ]
  exact h

theorem maxw3_pos (h : |j| < ρ) (i : Fin 3) : 0 < maxw3 ρ j i := by
  have hρ : 0 < ρ := (abs_nonneg j).trans_lt h
  have ht := maxwT_pos (abs_div_lt_one h)
  have hc : 0 < ρ / ((maxwT (j / ρ))⁻¹ + 1 + maxwT (j / ρ)) := by positivity
  fin_cases i <;>
    simp only [maxw3, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    positivity

theorem maxw3_exp_family (h : |j| < ρ) : maxw3 ρ j 1 ^ 2 = maxw3 ρ j 0 * maxw3 ρ j 2 := by
  have ht := maxwT_pos (abs_div_lt_one h)
  simp only [maxw3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  field_simp

theorem maxw3_mass (h : |j| < ρ) : maxw3 ρ j 0 + maxw3 ρ j 1 + maxw3 ρ j 2 = ρ := by
  have ht := maxwT_pos (abs_div_lt_one h)
  simp only [maxw3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  have hS : (maxwT (j / ρ))⁻¹ + 1 + maxwT (j / ρ) ≠ 0 := by positivity
  rw [show ∀ c t : ℝ, c * t⁻¹ + c + c * t = c * (t⁻¹ + 1 + t) by intros; ring,
    div_mul_cancel₀ _ hS]

theorem maxw3_momentum (h : |j| < ρ) : -maxw3 ρ j 0 + maxw3 ρ j 2 = j := by
  have hρ : 0 < ρ := (abs_nonneg j).trans_lt h
  have hu := abs_div_lt_one h
  have ht := maxwT_pos hu
  have hroot := maxwT_root hu
  simp only [maxw3, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  set t := maxwT (j / ρ) with htdef
  set c := ρ / (t⁻¹ + 1 + t) with hcdef
  have hS : t⁻¹ + 1 + t ≠ 0 := by positivity
  have hc : c * (t⁻¹ + 1 + t) = ρ := div_mul_cancel₀ ρ hS
  have hc' : c * (1 + t + t ^ 2) = ρ * t := by
    rw [← hc]
    field_simp
  have e1 : ρ * (j / ρ) = j := mul_div_cancel₀ j hρ.ne'
  have hroot' : (ρ - j) * t ^ 2 - j * t - (ρ + j) = 0 := by
    linear_combination ρ * hroot + (t ^ 2 + t + 1) * e1
  have hq : 0 < 1 + t + t ^ 2 := by positivity
  have h3 : (c * (t ^ 2 - 1) - j * t) * (1 + t + t ^ 2) = 0 := by
    linear_combination (t ^ 2 - 1) * hc' + t * hroot'
  have h4 : c * (t ^ 2 - 1) = j * t := by
    rcases mul_eq_zero.1 h3 with h | h
    · linarith
    · exact absurd h hq.ne'
  apply mul_right_cancel₀ ht.ne'
  rw [add_mul, neg_mul, mul_assoc, inv_mul_cancel₀ ht.ne', mul_one]
  linear_combination h4

/-- The three-velocity exponential-family Maxwellian is a Maxwellian map for the invariants
`1, v` on the realizable set: the hypotheses of the general theorems are satisfiable by a
nonlinear model. -/
theorem isMaxwellianOn_maxw3Map : IsMaxwellianOn (maxw3Map (m := m)) Ψ3 realizable3 := by
  intro μ hμ
  ext x i
  have h1 := maxw3_mass (hμ x)
  have h2 := maxw3_momentum (hμ x)
  fin_cases i <;> simp [maxw3Map, Ψ3, Matrix.mul_apply, Fin.sum_univ_three] <;> linarith

/-- The orthonormal basis `(1/√3, v/√2)` of `span {1, v} ⊂ ℝ³`: the rank-2 velocity space spanned
by the collision invariants themselves. -/
noncomputable def V₂ : Matrix (Fin 3) (Fin 2) ℝ :=
  !![(√3)⁻¹, -(√2)⁻¹; (√3)⁻¹, 0; (√3)⁻¹, (√2)⁻¹]

private theorem sqrt3_inv_sq : (√3)⁻¹ * (√3)⁻¹ = 1 / 3 := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
  norm_num

private theorem sqrt2_inv_sq : (√2)⁻¹ * (√2)⁻¹ = 1 / 2 := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem V₂_orth : V₂ᵀ * V₂ = 1 := by
  have ha := sqrt3_inv_sq
  have hb := sqrt2_inv_sq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [V₂, Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith [ha, hb]

/-- `V₂ V₂ᵀ` as a matrix. -/
theorem V₂_mul_transpose :
    V₂ * V₂ᵀ = !![5 / 6, 1 / 3, -(1 / 6); 1 / 3, 1 / 3, 1 / 3; -(1 / 6), 1 / 3, 5 / 6] := by
  have ha := sqrt3_inv_sq
  have hb := sqrt2_inv_sq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [V₂, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [ha, hb]

/-- The collision invariants lie in `range V₂`. -/
theorem V₂_captures_Ψ : V₂ * V₂ᵀ * Ψ3 = Ψ3 := by
  rw [V₂_mul_transpose]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Ψ3, Matrix.mul_apply, Fin.sum_univ_three]

/-- The projected flux invariants: `v` is kept, `v²` is replaced by the constant `2/3`. -/
theorem V₂_mul_Φ3 : V₂ * V₂ᵀ * Φ3 = !![-1, 2 / 3; 0, 2 / 3; 1, 2 / 3] := by
  rw [V₂_mul_transpose]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Φ3, Matrix.mul_apply, Fin.sum_univ_three]

/-- The flux invariant `v²` does not lie in `range V₂`. -/
theorem V₂_not_captures_Φ : V₂ * V₂ᵀ * Φ3 ≠ Φ3 := by
  rw [V₂_mul_Φ3]
  intro h
  have := congrFun (congrFun h 0) 1
  norm_num [Φ3] at this

/-- **The rank-2 limit has the fluxes of the linear P₁ system, for every Maxwellian model.**  For
any state `g`, the kinetic fluxes of its projection `g V₂ V₂ᵀ` are `(j, 2ρ/3)`: the limit
moment system of the rank-2 scheme is `∂ₜρ + ∂ₓj = 0`, `∂ₜj + (2/3) ∂ₓρ = 0`, whatever the
Maxwellian is. -/
theorem p1_flux (g : Matrix m (Fin 3) ℝ) :
    g * (V₂ * V₂ᵀ) * Φ3 = Matrix.of fun x => ![g x 2 - g x 0, 2 / 3 * (g x 0 + g x 1 + g x 2)] := by
  rw [Matrix.mul_assoc, V₂_mul_Φ3]
  ext x i
  fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- The Euler energy flux `⟨v² 𝓜⟩ = M₋ + M₊` of the exponential-family Maxwellian differs from
the P₁ value `2ρ/3` as soon as `j ≠ 0`. -/
theorem maxw3_flux_ne (h : |j| < ρ) (hj : j ≠ 0) : maxw3 ρ j 0 + maxw3 ρ j 2 ≠ 2 / 3 * ρ := by
  have hρ : 0 < ρ := (abs_nonneg j).trans_lt h
  have hu := abs_div_lt_one h
  have ht := maxwT_pos hu
  intro heq
  have hmass := maxw3_mass h
  simp only [maxw3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at heq hmass
  set t := maxwT (j / ρ) with htdef
  set c := ρ / (t⁻¹ + 1 + t) with hcdef
  have hc : 0 < c := by positivity
  have h1 : t⁻¹ + t = 2 := by
    have : c * (t⁻¹ + t) = 2 / 3 * (c * (t⁻¹ + 1 + t)) := by linear_combination heq - 2 / 3 * hmass
    have h2 : c * (3 * (t⁻¹ + t) - 2 * (t⁻¹ + 1 + t)) = 0 := by linear_combination 3 * this
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hc.ne'
    · linarith
  have h2 : (t - 1) ^ 2 = 0 := by
    have : t * (t⁻¹ + t) = t * 2 := by rw [h1]
    rw [mul_add, mul_inv_cancel₀ ht.ne'] at this
    linear_combination this
  have ht1 : t = 1 := by nlinarith [sq_nonneg (t - 1)]
  have hu0 : j / ρ = 0 := (maxwT_eq_one_iff hu).1 ht1
  exact hj ((div_eq_zero_iff.1 hu0).resolve_right hρ.ne')

/-- **Counterexample: the rank-2 low-rank scheme is AP to the wrong fluid limit.**  With full
spatial resolution (`U = 1`), any collision frequency, and the velocity basis `V₂ = span {1, v}`
(which contains the collision invariants, so `moments_eq`, `existsUnique_bgkStep` and
`norm_sub_ceLimit_le` apply), the limit `s → ∞` of the nonlinear BGK step has the kinetic fluxes
`(j, 2ρ/3)`, while the Maxwellian of the same moments has the Euler fluxes `(j, M₋ + M₊)`; they
differ in every cell with nonzero momentum.  The rank-3 basis (`V = 1`) satisfies
`V Vᵀ Φ = Φ` and captures the Euler fluxes by `moment_update_full_sub_le`. -/
theorem ceLimit_flux_ne [DecidableEq m] {σ : m → ℝ} {σ₀ σ₁ : ℝ} (hσ : IsCrossSection σ σ₀ σ₁)
    {μ : Matrix m (Fin 2) ℝ} (hμ : μ ∈ realizable3) {x : m} (hx : μ x 1 ≠ 0) :
    ceLimit σ (1 : Matrix m m ℝ) V₂ (maxw3Map μ) * Φ3 ≠ maxw3Map μ * Φ3 := by
  intro h
  have h1 : (1 : Matrix m m ℝ)ᵀ * 1 = 1 := by rw [Matrix.transpose_one, Matrix.one_mul]
  have h1' : (1 : Matrix m m ℝ) * 1ᵀ = 1 := by rw [Matrix.transpose_one, Matrix.mul_one]
  rw [ceLimit, weightedProj_eq_one hσ h1 h1', Matrix.one_mul, p1_flux] at h
  have h2 := congrFun (congrFun h x) 1
  have hmass := maxw3_mass (hμ x)
  simp [maxw3Map, Φ3, Matrix.mul_apply, Fin.sum_univ_three] at h2
  exact maxw3_flux_ne (hμ x) hx (by linarith)

end ThreeVelocity

end LeanDLRA.Novel.OpST33
