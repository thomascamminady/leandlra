import LeanDLRA.Novel.EpsRank

/-!
# Uniform-in-`ε` error bounds for low-rank kinetic schemes (OP-ST-21)

Open problem OP-ST-21 of `docs/survey/open-problems.json`: error bounds for low-rank kinetic
schemes in the diffusive scaling with constants independent of `ε`.  Setting of `EpsRank`:
`f ∈ ℝ^{X × V}`, `∂_t f + ε⁻¹ D f diag(μ) = σ ε⁻² (⟨f⟩ ⊗ 1 - f)`, skew-symmetric `D`,
quadrature `(μ_v, w_v)`, weighted norm `‖f‖_w = ‖weighted q f‖`, full implicit Euler `F_n`,
isotropic data `F₀ = ρ₀ ⊗ 1`.

## The low-rank error, uniformly in `ε` and `τ`

A *velocity Galerkin projector* `P` (`IsVelocityGalerkin`) is the `w`-orthogonal projector onto a
subspace containing the isotropic matrices; the Galerkin scheme is `G_{n+1} = G_n + τ P L G_{n+1}`
(`IsGalerkinEuler`; `P = id` is implicit Euler, `isGalerkinEuler_id_iff`).  Trajectories exist
(`exists_galerkinEuler`), and the two-moment projector `proj2` onto `ℝ^X ⊗ span {1, μ}` is an
instance whose iterates have rank `≤ 2` (`isVelocityGalerkin_proj2`, `rank_proj2_le`).

* `galerkin_sub_full_le`: if the Galerkin space contains `1, μ, …, μ^{k-1}`, then for all
  `ε, σ, τ > 0` and all `n`,
  `‖G_n - F_n‖_w ≤ (ε m / σ)^k ‖D^k ρ₀‖₂ (1 + t_n m ‖D‖_F / ε)`.
* `galerkin_sub_full_le_cfl`, `rank2_sub_full_le`: with `k ≥ 2`, `⟨μ⟩ = 0` and
  `τ (m ‖D‖_F)² ≤ σ/2`, for `n ≤ N`, `T = N τ`,
  `‖G_n - F_n‖_w ≤ (ε m / σ)^k ‖D^k ρ₀‖₂ (2 + 4 T (m ‖D‖_F)² / σ)`:
  the rank-`k` scheme is `O(ε^k)`-close to the full solution, uniformly in `ε` and `τ`.  The
  mechanism is `avg_P_genL_sub`: once `μ` is in the Galerkin space the defect has zero average,
  so it is damped by the relaxation before it reaches the macroscopic variable.

Both are consequences of the Galerkin energy contraction (`galerkin_contract`) and the moment bound
`exists_moment_approx` of `EpsRank`.  Numerically (Gauss–Legendre, `k = 2, 3`) the error is
`≈ 0.7 ε²` resp. `≈ 0.3 ε³`, independent of `τ`, so the second bound has the right order.

## The time error is not uniform over all steps

`telegraph_layer_error`, `no_uniform_first_order`: on the telegraph model with isotropic data,
the first implicit Euler step at `τ = ε²/σ` has error `≥ ε K / (16 σ) = Θ(√τ)` against the exact
semi-discrete flow.  So the bound `‖Y^n - f(t_n)‖ ≤ C τ` asked for in OP-ST-21 cannot hold with
`C` independent of `ε` and uniformly in `n` for data that are only isotropic; any `ε`-term in such
a bound has exponent at most one.  Every scheme that reduces to implicit Euler on two velocities
(rank `≥ 2`, `proj2`) inherits this.

## What stays open

The full time error at a *fixed* final time.  Numerically, `‖F_N - f(T)‖_w / τ ≈ 0.06` for
`ε ∈ [10⁻³, 10⁻¹]` and all `τ`, including `τ = ε²`: implicit Euler appears to be uniformly first
order at fixed `T` for isotropic data, the initial-layer error above being damped by the
relaxation.  This is not proved here; it needs bounds on `∂_t² f` through the initial layer and the
discrete damping of microscopic defects, and would complete the uniform bound for the Galerkin
schemes against the exact solution by the triangle inequality.  Everything here is for linear
isotropic scattering with `D` skew-symmetric; BGK, nonlinear models and adaptive bases are not
covered.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Novel.OpST21

open LeanDLRA
open LeanDLRA.Novel.EpsRank hiding Quadrature
open LeanDLRA.Kinetic (Quadrature)

section Weighted

variable {X V : Type*} [Fintype X] [Fintype V]

/-- The quadrature-weighted inner product `⟨f, g⟩_w = ∑_{i,v} w_v f_{iv} g_{iv}` on
`ℝ^{X × V}`, i.e. the Frobenius inner product of the weighted matrices. -/
noncomputable def winner (q : Quadrature V) (f g : Matrix X V ℝ) : ℝ :=
  ⟪weighted q f, weighted q g⟫

theorem winner_def (q : Quadrature V) (f g : Matrix X V ℝ) :
    winner q f g = ∑ i, ∑ v, q.w v * (f i v * g i v) := by
  rw [winner, Frobenius.inner_def]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun v _ => ?_
  simp only [weighted, Matrix.of_apply]
  rw [show √(q.w v) * f i v * (√(q.w v) * g i v) = (√(q.w v) * √(q.w v)) * (f i v * g i v) by
    ring, Real.mul_self_sqrt (q.w_pos v).le]

theorem winner_self (q : Quadrature V) (f : Matrix X V ℝ) :
    winner q f f = ‖weighted q f‖ ^ 2 := real_inner_self_eq_norm_sq _

theorem winner_comm (q : Quadrature V) (f g : Matrix X V ℝ) : winner q f g = winner q g f :=
  real_inner_comm _ _

theorem winner_le (q : Quadrature V) (f g : Matrix X V ℝ) :
    winner q f g ≤ ‖weighted q f‖ * ‖weighted q g‖ := real_inner_le_norm _ _

theorem abs_winner_le (q : Quadrature V) (f g : Matrix X V ℝ) :
    |winner q f g| ≤ ‖weighted q f‖ * ‖weighted q g‖ := abs_real_inner_le_norm _ _

omit [Fintype X] in
theorem weighted_add (q : Quadrature V) (f g : Matrix X V ℝ) :
    weighted q (f + g) = weighted q f + weighted q g := (weightedL q).map_add f g

omit [Fintype X] in
theorem weighted_sub (q : Quadrature V) (f g : Matrix X V ℝ) :
    weighted q (f - g) = weighted q f - weighted q g := (weightedL q).map_sub f g

omit [Fintype X] in
theorem weighted_smul (q : Quadrature V) (r : ℝ) (f : Matrix X V ℝ) :
    weighted q (r • f) = r • weighted q f := (weightedL q).map_smul r f

omit [Fintype X] in
theorem weighted_zero (q : Quadrature V) : weighted q (0 : Matrix X V ℝ) = 0 :=
  (weightedL q).map_zero

theorem winner_add_left (q : Quadrature V) (f g h : Matrix X V ℝ) :
    winner q (f + g) h = winner q f h + winner q g h := by
  rw [winner, weighted_add, inner_add_left]; rfl

theorem winner_sub_left (q : Quadrature V) (f g h : Matrix X V ℝ) :
    winner q (f - g) h = winner q f h - winner q g h := by
  rw [winner, weighted_sub, inner_sub_left]; rfl

theorem winner_smul_left (q : Quadrature V) (r : ℝ) (f h : Matrix X V ℝ) :
    winner q (r • f) h = r * winner q f h := by
  rw [winner, weighted_smul, real_inner_smul_left]; rfl

theorem winner_add_right (q : Quadrature V) (f g h : Matrix X V ℝ) :
    winner q h (f + g) = winner q h f + winner q h g := by
  rw [winner_comm, winner_add_left, winner_comm q f, winner_comm q g]

theorem winner_sub_right (q : Quadrature V) (f g h : Matrix X V ℝ) :
    winner q h (f - g) = winner q h f - winner q h g := by
  rw [winner_comm, winner_sub_left, winner_comm q f, winner_comm q g]

theorem winner_smul_right (q : Quadrature V) (r : ℝ) (f h : Matrix X V ℝ) :
    winner q h (r • f) = r * winner q h f := by
  rw [winner_comm, winner_smul_left, winner_comm]

theorem winner_zero_left (q : Quadrature V) (h : Matrix X V ℝ) : winner q 0 h = 0 := by
  rw [winner, weighted_zero, inner_zero_left]

/-- `⟨f, ρ ⊗ 1⟩_w = ∑_i ρ_i ⟨f⟩_i`. -/
theorem winner_iso (q : Quadrature V) (f : Matrix X V ℝ) (ρ : X → ℝ) :
    winner q f (iso ρ) = ∑ i, avg q f i * ρ i := by
  rw [winner_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [iso, Matrix.of_apply, avg, Finset.sum_mul]
  exact Finset.sum_congr rfl fun v _ => by ring

/-- The transport term is skew for the weighted inner product, for skew-symmetric `D`. -/
theorem winner_transport_self {D : Matrix X X ℝ} (hD : D.transpose = -D) (q : Quadrature V)
    (f : Matrix X V ℝ) : winner q (transport D q f) f = 0 := by
  rw [winner_def, Finset.sum_comm]
  refine Finset.sum_eq_zero fun v _ => ?_
  have h1 := skew_quad hD (fun i => f i v)
  have h2 : ∀ i, (D * f) i v = D.mulVec (fun i => f i v) i := fun i => by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  calc ∑ i, q.w v * (transport D q f i v * f i v)
      = (q.w v * q.μ v) * ∑ i, f i v * D.mulVec (fun i => f i v) i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← h2 i]
        simp only [transport, Matrix.of_apply]
        ring
    _ = 0 := by rw [h1, mul_zero]

/-- The scattering term is dissipative for the weighted inner product. -/
theorem winner_iso_avg_sub_self_nonpos (q : Quadrature V) (f : Matrix X V ℝ) :
    winner q (iso (avg q f) - f) f ≤ 0 := by
  rw [winner_def]
  refine Finset.sum_nonpos fun i _ => ?_
  have h := sum_w_mul_avg_sub_le q f i
  refine le_of_eq_of_le (Finset.sum_congr rfl fun v _ => ?_) h
  simp only [Matrix.sub_apply, iso, Matrix.of_apply]
  ring

theorem genL_apply (D : Matrix X X ℝ) (q : Quadrature V) (ε σ : ℝ) (f : Matrix X V ℝ) :
    genL D q ε σ f = (σ / ε ^ 2) • (iso (avg q f) - f) - ε⁻¹ • transport D q f := rfl

/-- **Dissipativity of the generator** in the weighted inner product, for skew-symmetric `D`. -/
theorem winner_genL_self_nonpos {D : Matrix X X ℝ} (hD : D.transpose = -D) (q : Quadrature V)
    {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (f : Matrix X V ℝ) :
    winner q (genL D q ε σ f) f ≤ 0 := by
  rw [genL_apply, winner_sub_left, winner_smul_left, winner_smul_left, winner_transport_self hD,
    mul_zero, sub_zero]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (winner_iso_avg_sub_self_nonpos q f)

/-- `‖D f diag(μ)‖_w ≤ m ‖D‖_F ‖f‖_w`. -/
theorem norm_weighted_transport_le {D : Matrix X X ℝ} {q : Quadrature V} {m : ℝ} (hm0 : 0 ≤ m)
    (hm : ∀ v, |q.μ v| ≤ m) (f : Matrix X V ℝ) :
    ‖weighted q (transport D q f)‖ ≤ m * ‖D‖ * ‖weighted q f‖ := by
  rw [transport_eq_mul]
  calc ‖weighted q (D * scaleMu q f)‖ ≤ ‖D‖ * ‖weighted q (scaleMu q f)‖ :=
        norm_weighted_mul_le D q _
    _ ≤ ‖D‖ * (m * ‖weighted q f‖) :=
        mul_le_mul_of_nonneg_left (norm_weighted_scaleMu_le hm0 hm f) (norm_nonneg _)
    _ = m * ‖D‖ * ‖weighted q f‖ := by ring

end Weighted

section Galerkin

variable {X V : Type*} [Fintype X] [Fintype V]

/-- A **velocity Galerkin projector**: `P` is the `L²(w)`-orthogonal projector onto a subspace of
`ℝ^{X × V}` that contains every isotropic matrix `ρ ⊗ 1` (the space `ℝ^X ⊗ 𝒱` with `1 ∈ 𝒱`
is the intended case). -/
structure IsVelocityGalerkin (q : Quadrature V) (P : Matrix X V ℝ →ₗ[ℝ] Matrix X V ℝ) :
    Prop where
  idem : ∀ f, P (P f) = P f
  symm : ∀ f g, winner q (P f) g = winner q f (P g)
  iso_fixed : ∀ ρ : X → ℝ, P (iso ρ) = iso ρ

namespace IsVelocityGalerkin

variable {q : Quadrature V} {P : Matrix X V ℝ →ₗ[ℝ] Matrix X V ℝ} (hP : IsVelocityGalerkin q P)
include hP

/-- The residual `f - P f` is orthogonal to the range. -/
theorem winner_sub_eq_zero (f g : Matrix X V ℝ) : winner q (f - P f) (P g) = 0 := by
  rw [← hP.symm, map_sub, hP.idem, sub_self, winner_zero_left]

/-- Best approximation: `‖f - P f‖_w ≤ ‖f - Y‖_w` whenever `P Y = Y`. -/
theorem norm_sub_le (f : Matrix X V ℝ) {Y : Matrix X V ℝ} (hY : P Y = Y) :
    ‖weighted q (f - P f)‖ ≤ ‖weighted q (f - Y)‖ := by
  have h1 : f - Y = (f - P f) + (P f - Y) := by abel
  have h2 : P f - Y = P (f - Y) := by rw [map_sub, hY]
  have h3 : ‖weighted q (f - Y)‖ ^ 2 = ‖weighted q (f - P f)‖ ^ 2 + ‖weighted q (P f - Y)‖ ^ 2 := by
    rw [h1, weighted_add, norm_add_sq_real]
    have h4 : ⟪weighted q (f - P f), weighted q (P f - Y)⟫ = 0 := by
      change winner q (f - P f) (P f - Y) = 0
      rw [h2]; exact hP.winner_sub_eq_zero f (f - Y)
    rw [h4]; ring
  have h5 : ‖weighted q (f - P f)‖ ^ 2 ≤ ‖weighted q (f - Y)‖ ^ 2 := by
    rw [h3]; nlinarith [sq_nonneg ‖weighted q (P f - Y)‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h5

/-- `P` is a contraction for the weighted norm. -/
theorem norm_le (f : Matrix X V ℝ) : ‖weighted q (P f)‖ ≤ ‖weighted q f‖ := by
  have h1 : ‖weighted q (P f)‖ ^ 2 ≤ ‖weighted q f‖ * ‖weighted q (P f)‖ := by
    rw [← winner_self, hP.symm, hP.idem]
    exact winner_le q f (P f)
  by_cases h0 : ‖weighted q (P f)‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖weighted q (P f)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    rw [sq] at h1
    exact le_of_mul_le_mul_right h1 hpos

/-- `P` preserves the velocity average (`1` is in the Galerkin space). -/
theorem avg_eq (f : Matrix X V ℝ) : avg q (P f) = avg q f := by
  classical
  funext i
  have h1 : ∀ g : Matrix X V ℝ, winner q g (iso (Pi.single i 1)) = avg q g i := fun g => by
    rw [winner_iso]
    simp [Pi.single_apply]
  rw [← h1, ← h1, hP.symm, hP.iso_fixed]

end IsVelocityGalerkin

/-- **The Galerkin implicit Euler scheme**: `G_{n+1} = G_n + τ P L G_{n+1}`, with every iterate in
the range of `P`.  For `P = id` this is the fully implicit scheme `IsImplicitEuler`. -/
def IsGalerkinEuler (P : Matrix X V ℝ →ₗ[ℝ] Matrix X V ℝ) (D : Matrix X X ℝ) (q : Quadrature V)
    (ε σ τ : ℝ) (G : ℕ → Matrix X V ℝ) : Prop :=
  ∀ n, P (G n) = G n ∧ G (n + 1) = G n + τ • P (genL D q ε σ (G (n + 1)))

/-- The solved form of an implicit Euler step: `p = f + τ L p`. -/
theorem IsStep.eq_add_smul {D : Matrix X X ℝ} {q : Quadrature V} {ε σ τ : ℝ} (hτ : 0 < τ)
    {f p : Matrix X V ℝ} (h : IsStep D q ε σ τ p f p) : p = f + τ • genL D q ε σ p := by
  have h1 := isStep_iff_stepOp.1 h
  rw [stepOp_eq] at h1
  have h2 := congrArg (fun x => τ • x) h1
  simp only [smul_sub, smul_smul, mul_inv_cancel₀ hτ.ne', one_smul] at h2
  rw [← h2]; abel

/-- `P = id` recovers the implicit Euler scheme. -/
theorem isGalerkinEuler_id_iff {D : Matrix X X ℝ} {q : Quadrature V} {ε σ τ : ℝ} (hτ : 0 < τ)
    {F : ℕ → Matrix X V ℝ} :
    IsGalerkinEuler LinearMap.id D q ε σ τ F ↔ IsImplicitEuler D q ε σ τ F := by
  constructor
  · intro h n
    have h1 := (h n).2
    simp only [LinearMap.id_apply] at h1
    have h2 : τ⁻¹ • F (n + 1) = τ⁻¹ • F n + genL D q ε σ (F (n + 1)) := by
      conv_lhs => rw [h1]
      rw [smul_add, smul_smul, inv_mul_cancel₀ hτ.ne', one_smul]
    rw [isStep_iff_stepOp, stepOp_eq, h2]
    abel
  · intro h n
    exact ⟨rfl, IsStep.eq_add_smul hτ (h n)⟩

variable {D : Matrix X X ℝ} {q : Quadrature V} {P : Matrix X V ℝ →ₗ[ℝ] Matrix X V ℝ} {ε σ τ : ℝ}

/-- **Energy contraction of a Galerkin step with a perturbation.**  If `E = E₀ + τ P L E` with
`P E = E`, then `‖E‖_w ≤ ‖E₀‖_w`, for skew-symmetric `D`. -/
theorem galerkin_contract (hP : IsVelocityGalerkin q P) (hD : D.transpose = -D) (hε : 0 < ε)
    (hσ : 0 < σ) (hτ : 0 < τ) {E₀ E : Matrix X V ℝ} (hE : P E = E)
    (h : E = E₀ + τ • P (genL D q ε σ E)) : ‖weighted q E‖ ≤ ‖weighted q E₀‖ := by
  have h1 : ‖weighted q E‖ ^ 2 ≤ ‖weighted q E₀‖ * ‖weighted q E‖ := by
    have h2 : winner q E E = winner q E₀ E + τ * winner q (genL D q ε σ E) E := by
      have h3 : winner q E E = winner q (E₀ + τ • P (genL D q ε σ E)) E := by rw [← h]
      rw [h3, winner_add_left, winner_smul_left, hP.symm, hE]
    rw [← winner_self, h2]
    have h3 := winner_genL_self_nonpos hD q hε hσ E
    have h4 := winner_le q E₀ E
    nlinarith
  by_cases h0 : ‖weighted q E‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖weighted q E‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    rw [sq] at h1
    exact le_of_mul_le_mul_right h1 hpos

/-- The Galerkin scheme is energy stable. -/
theorem IsGalerkinEuler.norm_le (hP : IsVelocityGalerkin q P) (hD : D.transpose = -D)
    (hε : 0 < ε) (hσ : 0 < σ) (hτ : 0 < τ) {G : ℕ → Matrix X V ℝ}
    (hG : IsGalerkinEuler P D q ε σ τ G) (n : ℕ) :
    ‖weighted q (G (n + 1))‖ ≤ ‖weighted q (G n)‖ :=
  galerkin_contract hP hD hε hσ hτ (hG (n + 1)).1 (hG n).2

/-- The Galerkin defect: on the residual `f - P f` the projected generator reduces to the
projected transport term. -/
theorem P_genL_sub (hP : IsVelocityGalerkin q P) (f : Matrix X V ℝ) :
    P (genL D q ε σ (f - P f)) = -ε⁻¹ • P (transport D q (f - P f)) := by
  have h1 : avg q (f - P f) = 0 := by rw [avg_sub, hP.avg_eq, sub_self]
  have h2 : P (f - P f) = 0 := by rw [map_sub, hP.idem, sub_self]
  have h0 : (iso (0 : X → ℝ) : Matrix X V ℝ) = 0 := by ext i v; simp [iso]
  rw [genL_apply, h1, h0, zero_sub, map_sub, map_smul, map_smul, map_neg, h2, neg_zero,
    smul_zero, zero_sub, neg_smul]

/-- **The Galerkin error recursion.**  With `E_n = G_n - P F_n` and the defect
`d_n = P L (F_{n+1} - P F_{n+1})`: `E_{n+1} = (E_n - τ d_n) + τ P L E_{n+1}`. -/
theorem galerkin_error_rec (hτ : 0 < τ) {F G : ℕ → Matrix X V ℝ}
    (hF : IsImplicitEuler D q ε σ τ F) (hG : IsGalerkinEuler P D q ε σ τ G) (n : ℕ) :
    G (n + 1) - P (F (n + 1)) =
      ((G n - P (F n)) - τ • P (genL D q ε σ (F (n + 1) - P (F (n + 1))))) +
        τ • P (genL D q ε σ (G (n + 1) - P (F (n + 1)))) := by
  have hFs : F (n + 1) = F n + τ • genL D q ε σ (F (n + 1)) := IsStep.eq_add_smul hτ (hF n)
  have hGs := (hG n).2
  have h1 : P (F (n + 1)) = P (F n) + τ • P (genL D q ε σ (F (n + 1))) := by
    conv_lhs => rw [hFs]
    rw [map_add, map_smul]
  have h2 : G (n + 1) - P (F (n + 1)) = (G n - P (F n)) +
      τ • (P (genL D q ε σ (G (n + 1))) - P (genL D q ε σ (F (n + 1)))) := by
    conv_lhs => rw [hGs, h1]
    module
  have h3 : P (genL D q ε σ (G (n + 1))) - P (genL D q ε σ (F (n + 1))) =
      P (genL D q ε σ (G (n + 1) - P (F (n + 1)))) -
        P (genL D q ε σ (F (n + 1) - P (F (n + 1)))) := by
    have h4 : (G (n + 1) - P (F (n + 1))) - (F (n + 1) - P (F (n + 1))) =
        G (n + 1) - F (n + 1) := by abel
    rw [← map_sub, ← map_sub, ← map_sub, ← map_sub, h4]
  set Z := P (genL D q ε σ (G (n + 1) - P (F (n + 1)))) with hZ
  set d := P (genL D q ε σ (F (n + 1) - P (F (n + 1)))) with hd
  rw [h2, h3, smul_sub]
  abel

omit [Fintype X] in
/-- `A * vand q k` is a sum of monomial matrices. -/
theorem mul_vand_eq_sum (q : Quadrature V) {k : ℕ} (A : Matrix X (Fin k) ℝ) :
    A * vand q k = ∑ j : Fin k, mon q j (fun i => A i j) := by
  ext i v
  rw [Matrix.sum_apply, Matrix.mul_apply]
  simp only [mon, vand, Matrix.of_apply]

/-- A Galerkin space containing `1, μ, …, μ^{k-1}` is within `(ε m / σ)^k ‖D^k ρ₀‖₂` of every
iterate of the full implicit scheme started from well-prepared data. -/
theorem norm_sub_P_le [DecidableEq X] {m : ℝ} (hD : D.transpose = -D) (hε : 0 < ε) (hσ : 0 < σ)
    (hτ : 0 < τ) (hm0 : 0 ≤ m) (hm : ∀ v, |q.μ v| ≤ m) {k : ℕ}
    (hk : ∀ j < k, ∀ u : X → ℝ, P (mon q j u) = mon q j u) {F : ℕ → Matrix X V ℝ} {ρ₀ : X → ℝ}
    (hF : IsImplicitEuler D q ε σ τ F) (hF0 : F 0 = iso ρ₀) (hP : IsVelocityGalerkin q P)
    (n : ℕ) :
    ‖weighted q (F n - P (F n))‖ ≤ (ε * m / σ) ^ k * l2 ((D ^ k).mulVec ρ₀) := by
  obtain ⟨A, hA⟩ := exists_moment_approx hD hε hσ hτ hm0 hm hF hF0 k n
  refine (hP.norm_sub_le (F n) (Y := A * vand q k) ?_).trans hA
  rw [mul_vand_eq_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ => hk j j.2 _

/-- **Uniform-in-`ε` bound, Galerkin versus full scheme, no step-size condition.**  For
skew-symmetric `D`, `|μ| ≤ m`, a velocity Galerkin space containing `1, μ, …, μ^{k-1}`, and both
schemes started from `ρ₀ ⊗ 1`,
`‖G_n - F_n‖_w ≤ (ε m / σ)^k ‖D^k ρ₀‖₂ (1 + t_n m ‖D‖_F / ε)`
for all `ε, σ, τ > 0` and all `n`.  The constant does not depend on `ε` or `τ`: with `k ≥ 2` the
rank-`k` Galerkin scheme is `O(ε^{k-1} (ε + t_n))`-close to the full discrete-velocity solution,
uniformly in the stiffness.  It matters because it isolates the low-rank part of the error of a
kinetic low-rank scheme from the time-discretisation error, and bounds it uniformly in `ε`.  The
proof is the Galerkin energy estimate plus the moment bound `exists_moment_approx` of `EpsRank`;
see `docs/survey/open-problems.json` OP-ST-21. -/
theorem galerkin_sub_full_le [DecidableEq X] {m : ℝ} (hD : D.transpose = -D) (hε : 0 < ε)
    (hσ : 0 < σ) (hτ : 0 < τ) (hm0 : 0 ≤ m) (hm : ∀ v, |q.μ v| ≤ m)
    (hP : IsVelocityGalerkin q P) {k : ℕ}
    (hk : ∀ j < k, ∀ u : X → ℝ, P (mon q j u) = mon q j u) {F G : ℕ → Matrix X V ℝ}
    {ρ₀ : X → ℝ} (hF : IsImplicitEuler D q ε σ τ F) (hF0 : F 0 = iso ρ₀)
    (hG : IsGalerkinEuler P D q ε σ τ G) (hG0 : G 0 = iso ρ₀) (n : ℕ) :
    ‖weighted q (G n - F n)‖ ≤
      (ε * m / σ) ^ k * l2 ((D ^ k).mulVec ρ₀) * (1 + n * τ * m * ‖D‖ / ε) := by
  set δ := (ε * m / σ) ^ k * l2 ((D ^ k).mulVec ρ₀) with hδ
  have hδ0 : 0 ≤ δ := mul_nonneg (by positivity) (l2_nonneg _)
  have happrox : ∀ n, ‖weighted q (F n - P (F n))‖ ≤ δ := fun n =>
    norm_sub_P_le hD hε hσ hτ hm0 hm hk hF hF0 hP n
  -- the error against the projected full solution
  have key : ∀ n, ‖weighted q (G n - P (F n))‖ ≤ n * (τ * m * ‖D‖ / ε * δ) := by
    intro n
    induction n with
    | zero =>
      rw [hG0, hF0, hP.iso_fixed, sub_self, weighted_zero, norm_zero]
      simp
    | succ n ih =>
      have hPE : P (G (n + 1) - P (F (n + 1))) = G (n + 1) - P (F (n + 1)) := by
        rw [map_sub, (hG (n + 1)).1, hP.idem]
      set d := P (genL D q ε σ (F (n + 1) - P (F (n + 1)))) with hd
      have hrec := galerkin_error_rec hτ hF hG n
      have hcon := galerkin_contract hP hD hε hσ hτ hPE hrec
      have hdn : ‖weighted q d‖ ≤ m * ‖D‖ / ε * δ := by
        rw [hd, P_genL_sub hP, weighted_smul, norm_smul, Real.norm_eq_abs, abs_neg,
          abs_inv, abs_of_pos hε]
        calc ε⁻¹ * ‖weighted q (P (transport D q (F (n + 1) - P (F (n + 1)))))‖
            ≤ ε⁻¹ * (m * ‖D‖ * δ) := by
              gcongr
              refine (hP.norm_le _).trans ?_
              refine (norm_weighted_transport_le hm0 hm _).trans ?_
              gcongr
              exact happrox (n + 1)
          _ = m * ‖D‖ / ε * δ := by ring
      calc ‖weighted q (G (n + 1) - P (F (n + 1)))‖
          ≤ ‖weighted q (G n - P (F n) - τ • d)‖ := hcon
        _ ≤ ‖weighted q (G n - P (F n))‖ + ‖weighted q (τ • d)‖ := by
            rw [weighted_sub]; exact norm_sub_le _ _
        _ ≤ n * (τ * m * ‖D‖ / ε * δ) + τ * (m * ‖D‖ / ε * δ) := by
            rw [weighted_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hτ]
            gcongr
        _ = ((n + 1 : ℕ) : ℝ) * (τ * m * ‖D‖ / ε * δ) := by push_cast; ring
  have h1 : G n - F n = (G n - P (F n)) - (F n - P (F n)) := by abel
  calc ‖weighted q (G n - F n)‖
      ≤ ‖weighted q (G n - P (F n))‖ + ‖weighted q (F n - P (F n))‖ := by
        rw [h1, weighted_sub]; exact norm_sub_le _ _
    _ ≤ n * (τ * m * ‖D‖ / ε * δ) + δ := add_le_add (key n) (happrox n)
    _ = δ * (1 + n * τ * m * ‖D‖ / ε) := by ring

end Galerkin

section Sharp

variable {X V : Type*} [Fintype X] [Fintype V] {D : Matrix X X ℝ} {q : Quadrature V}
  {P : Matrix X V ℝ →ₗ[ℝ] Matrix X V ℝ} {ε σ τ : ℝ}

omit [Fintype X] in
/-- The micro part `f - ⟨f⟩ ⊗ 1` has zero average. -/
theorem avg_sub_iso_avg (q : Quadrature V) (f : Matrix X V ℝ) :
    avg q (f - iso (avg q f)) = 0 := by
  rw [avg_sub, avg_iso, sub_self]

/-- A matrix with zero average is `w`-orthogonal to every isotropic matrix. -/
theorem winner_iso_eq_zero (q : Quadrature V) (u : X → ℝ) {g : Matrix X V ℝ}
    (hg : avg q g = 0) : winner q (iso u) g = 0 := by
  rw [winner_comm, winner_iso, hg]; simp

/-- Pairing with a zero-average matrix only sees the micro part. -/
theorem winner_eq_winner_micro (q : Quadrature V) (f : Matrix X V ℝ) {g : Matrix X V ℝ}
    (hg : avg q g = 0) : winner q f g = winner q (f - iso (avg q f)) g := by
  rw [winner_sub_left, winner_iso_eq_zero q _ hg, sub_zero]

theorem transport_add (D : Matrix X X ℝ) (q : Quadrature V) (x y : Matrix X V ℝ) :
    transport D q (x + y) = transport D q x + transport D q y := (transportL D q).map_add x y

omit [Fintype X] in
theorem scaleMu_add (q : Quadrature V) (x y : Matrix X V ℝ) :
    scaleMu q (x + y) = scaleMu q x + scaleMu q y := by
  ext i v; simp [scaleMu, mul_add]

/-- The average of the generator: scattering conserves mass, transport moves the flux. -/
theorem avg_genL (D : Matrix X X ℝ) (q : Quadrature V) (ε σ : ℝ) (f : Matrix X V ℝ) :
    avg q (genL D q ε σ f) = -ε⁻¹ • D.mulVec (avg q (scaleMu q f)) := by
  rw [genL_apply, avg_sub, avg_smul, avg_smul, avg_sub, avg_iso, sub_self, smul_zero, zero_sub,
    transport_eq_mul, avg_mul, neg_smul]

omit [Fintype X] in
/-- With `⟨μ⟩ = 0` the isotropic part carries no flux. -/
theorem avg_scaleMu_iso (q : Quadrature V) (hμ : ∑ v, q.w v * q.μ v = 0) (u : X → ℝ) :
    avg q (scaleMu q (iso u : Matrix X V ℝ)) = 0 := by
  funext i
  simp only [avg, scaleMu, iso, Matrix.of_apply, Pi.zero_apply]
  rw [show ∑ v, q.w v * (q.μ v * u i) = (∑ v, q.w v * q.μ v) * u i by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun v _ => by ring, hμ, zero_mul]

/-- The flux of `f` is the pairing with `e_i ⊗ μ`. -/
theorem avg_scaleMu_apply [DecidableEq X] (q : Quadrature V) (f : Matrix X V ℝ) (i : X) :
    avg q (scaleMu q f) i = winner q f (mon q 1 (Pi.single i 1)) := by
  rw [winner_def, Finset.sum_eq_single i]
  · simp only [avg, scaleMu, mon, Matrix.of_apply, Pi.single_eq_same, pow_one]
    exact Finset.sum_congr rfl fun v _ => by ring
  · intro i' _ hi'
    simp [mon, Pi.single_eq_of_ne hi']
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **The Galerkin defect is purely microscopic** when `μ` lies in the Galerkin space: the
projected generator applied to the residual `f - P f` has zero average. -/
theorem avg_P_genL_sub (hP : IsVelocityGalerkin q P)
    (hmon1 : ∀ u : X → ℝ, P (mon q 1 u) = mon q 1 u) (f : Matrix X V ℝ) :
    avg q (P (genL D q ε σ (f - P f))) = 0 := by
  classical
  rw [hP.avg_eq, avg_genL]
  have h : avg q (scaleMu q (f - P f)) = 0 := by
    funext i
    rw [avg_scaleMu_apply, ← hmon1, hP.winner_sub_eq_zero]
    rfl
  rw [h, Matrix.mulVec_zero, smul_zero]

/-- One perturbed Galerkin step, total energy: `‖E‖² ≤ ‖E₀‖ ‖E‖ + τ ‖d‖ ‖g‖` with `g` the micro
part of `E`, when the perturbation `d` has zero average. -/
theorem step_total (hP : IsVelocityGalerkin q P) (hD : D.transpose = -D) (hε : 0 < ε)
    (hσ : 0 < σ) (hτ : 0 < τ) {E₀ E d : Matrix X V ℝ} (hE : P E = E) (hd0 : avg q d = 0)
    (h : E = (E₀ - τ • d) + τ • P (genL D q ε σ E)) :
    ‖weighted q E‖ ^ 2 ≤ ‖weighted q E₀‖ * ‖weighted q E‖ +
      τ * (‖weighted q d‖ * ‖weighted q (E - iso (avg q E))‖) := by
  have h1 : winner q E E = winner q E₀ E - τ * winner q d E + τ * winner q (genL D q ε σ E) E := by
    have h3 : winner q E E = winner q ((E₀ - τ • d) + τ • P (genL D q ε σ E)) E := by rw [← h]
    rw [h3, winner_add_left, winner_sub_left, winner_smul_left, winner_smul_left, hP.symm, hE]
  have h2 : winner q d E = winner q d (E - iso (avg q E)) := by
    rw [winner_comm, winner_eq_winner_micro q E hd0, winner_comm]
  rw [← winner_self, h1, h2]
  have h3 := mul_nonpos_of_nonneg_of_nonpos hτ.le (winner_genL_self_nonpos hD q hε hσ E)
  have h4 := winner_le q E₀ E
  have h5 := abs_winner_le q d (E - iso (avg q E))
  have h6 := neg_abs_le (winner q d (E - iso (avg q E)))
  have h7 : τ * (-winner q d (E - iso (avg q E))) ≤
      τ * (‖weighted q d‖ * ‖weighted q (E - iso (avg q E))‖) :=
    mul_le_mul_of_nonneg_left (by linarith) hτ.le
  linarith

/-- One perturbed Galerkin step, micro energy:
`(1 + τ σ / ε²) ‖g‖ ≤ ‖g₀‖ + τ ‖d‖ + (τ/ε) m ‖D‖ ‖⟨E⟩‖₂`. -/
theorem step_micro {m : ℝ} (hP : IsVelocityGalerkin q P) (hD : D.transpose = -D) (hε : 0 < ε)
    (hτ : 0 < τ) (hm0 : 0 ≤ m) (hm : ∀ v, |q.μ v| ≤ m) {E₀ E d : Matrix X V ℝ}
    (hE : P E = E) (h : E = (E₀ - τ • d) + τ • P (genL D q ε σ E)) :
    (1 + τ * σ / ε ^ 2) * ‖weighted q (E - iso (avg q E))‖ ≤
      ‖weighted q (E₀ - iso (avg q E₀))‖ + τ * ‖weighted q d‖ +
        τ / ε * (m * ‖D‖) * l2 (avg q E) := by
  set g := E - iso (avg q E) with hgdef
  set g₀ := E₀ - iso (avg q E₀) with hg₀def
  set a := avg q E with hadef
  have hg : avg q g = 0 := avg_sub_iso_avg q E
  have hPg : P g = g := by rw [hgdef, map_sub, hE, hP.iso_fixed]
  have hEg : E = iso a + g := by rw [hgdef]; abel
  -- the energy identity
  have h1 : winner q E g = ‖weighted q g‖ ^ 2 := by
    rw [winner_eq_winner_micro q E hg, ← winner_self]
  have h2 : winner q E g = winner q g₀ g - τ * winner q d g + τ * winner q (genL D q ε σ E) g := by
    have h3 : winner q E g = winner q ((E₀ - τ • d) + τ • P (genL D q ε σ E)) g := by rw [← h]
    rw [h3, winner_add_left, winner_sub_left, winner_smul_left, winner_smul_left, hP.symm, hPg,
      winner_eq_winner_micro q E₀ hg]
  have h4 : winner q (genL D q ε σ E) g =
      -(σ / ε ^ 2) * ‖weighted q g‖ ^ 2 - ε⁻¹ * winner q (transport D q (iso a)) g := by
    rw [genL_apply, winner_sub_left, winner_smul_left, winner_smul_left]
    have h5 : iso (avg q E) - E = -g := by rw [hgdef]; abel
    have h6 : transport D q E = transport D q (iso a) + transport D q g := by
      conv_lhs => rw [hEg]
      exact transport_add D q _ _
    rw [h5, h6, winner_add_left, winner_transport_self hD, add_zero, ← winner_self]
    have h7 : winner q (-g) g = -winner q g g := by
      rw [show -g = (-1 : ℝ) • g by simp, winner_smul_left]; ring
    rw [h7]; ring
  -- bounds on the three terms
  have hb1 := winner_le q g₀ g
  have hb2 : -winner q d g ≤ ‖weighted q d‖ * ‖weighted q g‖ := by
    have := abs_winner_le q d g
    linarith [neg_abs_le (winner q d g)]
  have hb3 : -winner q (transport D q (iso a)) g ≤ m * ‖D‖ * l2 a * ‖weighted q g‖ := by
    have h8 := abs_winner_le q (transport D q (iso a)) g
    have h9 := norm_weighted_transport_le (D := D) hm0 hm (iso a : Matrix X V ℝ)
    rw [norm_weighted_iso] at h9
    have h10 := neg_abs_le (winner q (transport D q (iso a)) g)
    have h11 : ‖weighted q (transport D q (iso a))‖ * ‖weighted q g‖ ≤
        m * ‖D‖ * l2 a * ‖weighted q g‖ := mul_le_mul_of_nonneg_right h9 (norm_nonneg _)
    linarith
  have hεi : 0 < ε⁻¹ := inv_pos.mpr hε
  have key : ‖weighted q g‖ ^ 2 + τ * (σ / ε ^ 2) * ‖weighted q g‖ ^ 2 ≤
      (‖weighted q g₀‖ + τ * ‖weighted q d‖ + τ / ε * (m * ‖D‖) * l2 a) * ‖weighted q g‖ := by
    have e1 : τ * winner q (genL D q ε σ E) g =
        -(τ * (σ / ε ^ 2) * ‖weighted q g‖ ^ 2) - τ * ε⁻¹ * winner q (transport D q (iso a)) g := by
      rw [h4]; ring
    have e2 : τ * ε⁻¹ * (-winner q (transport D q (iso a)) g) ≤
        τ * ε⁻¹ * (m * ‖D‖ * l2 a * ‖weighted q g‖) :=
      mul_le_mul_of_nonneg_left hb3 (by positivity)
    have e3 : τ * (-winner q d g) ≤ τ * (‖weighted q d‖ * ‖weighted q g‖) :=
      mul_le_mul_of_nonneg_left hb2 hτ.le
    have e4 : τ / ε = τ * ε⁻¹ := div_eq_mul_inv τ ε
    rw [e4]
    nlinarith [h1, h2, e1, e2, e3, hb1]
  by_cases h0 : ‖weighted q g‖ = 0
  · rw [h0, mul_zero]
    have := l2_nonneg a
    positivity
  · have hpos : 0 < ‖weighted q g‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have key' : (1 + τ * σ / ε ^ 2) * ‖weighted q g‖ * ‖weighted q g‖ ≤
        (‖weighted q g₀‖ + τ * ‖weighted q d‖ + τ / ε * (m * ‖D‖) * l2 a) * ‖weighted q g‖ := by
      have : (1 + τ * σ / ε ^ 2) * ‖weighted q g‖ * ‖weighted q g‖ =
          ‖weighted q g‖ ^ 2 + τ * (σ / ε ^ 2) * ‖weighted q g‖ ^ 2 := by ring
      rw [this]; exact key
    exact le_of_mul_le_mul_right key' hpos

/-- One perturbed Galerkin step, macro part: `‖⟨E⟩‖₂ ≤ ‖⟨E₀⟩‖₂ + (τ/ε) m ‖D‖ ‖g‖`, for a
quadrature with `⟨μ⟩ = 0`. -/
theorem step_macro {m : ℝ} (hP : IsVelocityGalerkin q P) (hε : 0 < ε) (hτ : 0 < τ) (hm0 : 0 ≤ m)
    (hm : ∀ v, |q.μ v| ≤ m) (hμ : ∑ v, q.w v * q.μ v = 0) {E₀ E d : Matrix X V ℝ}
    (hd0 : avg q d = 0) (h : E = (E₀ - τ • d) + τ • P (genL D q ε σ E)) :
    l2 (avg q E) ≤ l2 (avg q E₀) + τ / ε * (m * ‖D‖) * ‖weighted q (E - iso (avg q E))‖ := by
  set g := E - iso (avg q E) with hgdef
  have hEg : E = iso (avg q E) + g := by rw [hgdef]; abel
  have h1 : avg q E = avg q E₀ + (-(τ / ε)) • D.mulVec (avg q (scaleMu q g)) := by
    have h2 : avg q E = avg q ((E₀ - τ • d) + τ • P (genL D q ε σ E)) := by rw [← h]
    rw [h2, avg_add, avg_sub, avg_smul, hd0, smul_zero, sub_zero, avg_smul, hP.avg_eq, avg_genL]
    have h3 : avg q (scaleMu q E) = avg q (scaleMu q g) := by
      conv_lhs => rw [hEg]
      rw [scaleMu_add, avg_add, avg_scaleMu_iso q hμ, zero_add]
    rw [h3, smul_smul]
    have h4 : τ * -ε⁻¹ = -(τ / ε) := by ring
    rw [h4]
  have h4 : l2 (avg q E) ≤ l2 (avg q E₀) + |-(τ / ε)| * l2 (D.mulVec (avg q (scaleMu q g))) := by
    rw [h1]
    refine (l2_add_le q _ _).trans ?_
    rw [l2_smul]
  have h5 : l2 (D.mulVec (avg q (scaleMu q g))) ≤ ‖D‖ * (m * ‖weighted q g‖) := by
    refine (l2_mulVec_le D _).trans ?_
    refine mul_le_mul_of_nonneg_left ((l2_avg_le q _).trans ?_) (norm_nonneg _)
    exact norm_weighted_scaleMu_le hm0 hm g
  have h6 : |-(τ / ε)| = τ / ε := by rw [abs_neg, abs_of_pos (by positivity)]
  rw [h6] at h4
  calc l2 (avg q E) ≤ l2 (avg q E₀) + τ / ε * l2 (D.mulVec (avg q (scaleMu q g))) := h4
    _ ≤ l2 (avg q E₀) + τ / ε * (‖D‖ * (m * ‖weighted q g‖)) := by gcongr
    _ = l2 (avg q E₀) + τ / ε * (m * ‖D‖) * ‖weighted q g‖ := by ring

/-- **Sharp-order uniform bound, Galerkin versus full scheme, under a parabolic CFL condition.**
For skew-symmetric `D`, `|μ| ≤ m`, `⟨μ⟩ = 0`, a velocity Galerkin space containing
`1, μ, …, μ^{k-1}` with `k ≥ 2`, the step-size condition `τ (m ‖D‖_F)² ≤ σ/2`, and both schemes
started from `ρ₀ ⊗ 1`: for all `n ≤ N`
`‖G_n - F_n‖_w ≤ (ε m / σ)^k ‖D^k ρ₀‖₂ (2 + 4 T (m ‖D‖_F)² / σ)`, `T = N τ`.
Compared with `galerkin_sub_full_le`, the factor `t_n m ‖D‖ / ε` is replaced by a constant: the
rank-`k` Galerkin scheme is within `O(ε^k)` of the full solution, uniformly in `ε` and `τ`, which is
the order observed numerically.  The mechanism is that the Galerkin defect has zero average as soon
as `μ` lies in the Galerkin space (`avg_P_genL_sub`), so it only feeds the relaxed micro variable;
its macroscopic effect is then `O(ε)` smaller.  See OP-ST-21. -/
theorem galerkin_sub_full_le_cfl [DecidableEq X] {m : ℝ} (hD : D.transpose = -D) (hε : 0 < ε)
    (hσ : 0 < σ) (hτ : 0 < τ) (hm0 : 0 ≤ m) (hm : ∀ v, |q.μ v| ≤ m)
    (hμ : ∑ v, q.w v * q.μ v = 0) (hP : IsVelocityGalerkin q P) {k : ℕ} (hk2 : 2 ≤ k)
    (hk : ∀ j < k, ∀ u : X → ℝ, P (mon q j u) = mon q j u)
    (hcfl : τ * (m * ‖D‖) ^ 2 ≤ σ / 2) {F G : ℕ → Matrix X V ℝ} {ρ₀ : X → ℝ}
    (hF : IsImplicitEuler D q ε σ τ F) (hF0 : F 0 = iso ρ₀)
    (hG : IsGalerkinEuler P D q ε σ τ G) (hG0 : G 0 = iso ρ₀) {N n : ℕ} (hn : n ≤ N) :
    ‖weighted q (G n - F n)‖ ≤ (ε * m / σ) ^ k * l2 ((D ^ k).mulVec ρ₀) *
      (2 + 4 * (N * τ) * (m * ‖D‖) ^ 2 / σ) := by
  set δ := (ε * m / σ) ^ k * l2 ((D ^ k).mulVec ρ₀) with hδ
  have hδ0 : 0 ≤ δ := mul_nonneg (by positivity) (l2_nonneg _)
  set B := m * ‖D‖ with hB
  have hB0 : 0 ≤ B := by positivity
  set T := (N : ℝ) * τ with hT
  have hT0 : 0 ≤ T := by positivity
  set c := 4 * T * B ^ 2 / σ with hc
  have hc0 : 0 ≤ c := by positivity
  set A := δ * (1 + c) with hA
  have hA0 : 0 ≤ A := by positivity
  set ξ := 2 * ε * B / σ * (δ + A) with hξ
  have hξ0 : 0 ≤ ξ := by positivity
  set H := B / ε * δ with hH
  have hH0 : 0 ≤ H := by positivity
  set θ := τ * σ / ε ^ 2 with hθ
  have hθ0 : 0 < θ := by positivity
  set r := τ / ε * B with hr
  have hr0 : 0 ≤ r := by positivity
  have happrox : ∀ n, ‖weighted q (F n - P (F n))‖ ≤ δ := fun n =>
    norm_sub_P_le hD hε hσ hτ hm0 hm hk hF hF0 hP n
  have hmon1 : ∀ u : X → ℝ, P (mon q 1 u) = mon q 1 u := fun u => hk 1 (by omega) u
  -- the error, its defect, and their properties
  have hPE : ∀ n, P (G n - P (F n)) = G n - P (F n) := fun n => by
    rw [map_sub, (hG n).1, hP.idem]
  have hd0 : ∀ n, avg q (P (genL D q ε σ (F (n + 1) - P (F (n + 1))))) = 0 := fun n =>
    avg_P_genL_sub hP hmon1 _
  have hdn : ∀ n, ‖weighted q (P (genL D q ε σ (F (n + 1) - P (F (n + 1)))))‖ ≤ H := fun n => by
    rw [P_genL_sub hP, weighted_smul, norm_smul, Real.norm_eq_abs, abs_neg, abs_inv,
      abs_of_pos hε, hH, hB]
    calc ε⁻¹ * ‖weighted q (P (transport D q (F (n + 1) - P (F (n + 1)))))‖
        ≤ ε⁻¹ * (m * ‖D‖ * δ) := by
          gcongr
          refine (hP.norm_le _).trans ?_
          refine (norm_weighted_transport_le hm0 hm _).trans ?_
          gcongr
          exact happrox (n + 1)
      _ = m * ‖D‖ / ε * δ := by ring
  -- the constants
  have hNA : (N : ℝ) * (2 * τ * H * ξ) ≤ A ^ 2 := by
    have h3 : (N : ℝ) * (2 * τ * H * ξ) = c * (δ * (δ + A)) := by
      rw [hH, hξ, hc, hT]; field_simp; ring
    rw [h3, hA]
    nlinarith [mul_nonneg hδ0 hδ0, mul_nonneg hc0 hc0, mul_nonneg (mul_nonneg hδ0 hδ0) hc0]
  have hr2 : r ^ 2 ≤ θ / 2 := by
    rw [hr, hθ, hB]
    have h1 : τ * (m * ‖D‖) ^ 2 * (τ / ε ^ 2) ≤ σ / 2 * (τ / ε ^ 2) :=
      mul_le_mul_of_nonneg_right hcfl (by positivity)
    have h2 : (τ / ε * (m * ‖D‖)) ^ 2 = τ * (m * ‖D‖) ^ 2 * (τ / ε ^ 2) := by
      field_simp
    have h3 : τ * σ / ε ^ 2 / 2 = σ / 2 * (τ / ε ^ 2) := by ring
    rw [h2, h3]; exact h1
  have hrξ : r * (δ + A) = θ * ξ / 2 := by
    rw [hr, hθ, hξ]; field_simp
  have hτH : τ * H = r * δ := by rw [hH, hr]; ring
  have hle_A : ∀ n ≤ N, ‖weighted q (G n - P (F n))‖ ^ 2 ≤ n * (2 * τ * H * ξ) →
      ‖weighted q (G n - P (F n))‖ ≤ A := fun n hn h => by
    have h1 : ‖weighted q (G n - P (F n))‖ ^ 2 ≤ A ^ 2 := by
      refine h.trans (le_trans ?_ hNA)
      gcongr
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hA0 two_ne_zero).mp h1
  -- the induction
  have key : ∀ n, n ≤ N →
      ‖weighted q ((G n - P (F n)) - iso (avg q (G n - P (F n))))‖ ≤ ξ ∧
        ‖weighted q (G n - P (F n))‖ ^ 2 ≤ n * (2 * τ * H * ξ) := by
    intro n
    induction n with
    | zero =>
      intro _
      have h0 : G 0 - P (F 0) = 0 := by rw [hG0, hF0, hP.iso_fixed, sub_self]
      have h00 : avg q (0 : Matrix X V ℝ) = 0 := by funext i; simp [avg]
      have h01 : (iso (0 : X → ℝ) : Matrix X V ℝ) = 0 := by ext i v; simp [iso]
      rw [h0, h00, h01, sub_zero, weighted_zero, norm_zero]
      simp [hξ0]
    | succ n ih =>
      intro hn1
      obtain ⟨ihx, iha⟩ := ih (by omega)
      have haA := hle_A n (by omega) iha
      have hy0 : l2 (avg q (G n - P (F n))) ≤ A := (l2_avg_le q _).trans haA
      have hrec := galerkin_error_rec hτ hF hG n
      have hmic := step_micro hP hD hε hτ hm0 hm (hPE (n + 1)) hrec
      have hmac := step_macro hP hε hτ hm0 hm hμ (hd0 n) hrec
      have htot := step_total hP hD hε hσ hτ (hPE (n + 1)) (hd0 n) hrec
      have hdn' := hdn n
      have hx'0 : 0 ≤ ‖weighted q ((G (n + 1) - P (F (n + 1))) -
        iso (avg q (G (n + 1) - P (F (n + 1)))))‖ := norm_nonneg _
      rw [← hB, ← hr, ← hθ] at hmic
      rw [← hB, ← hr] at hmac
      generalize ‖weighted q ((G (n + 1) - P (F (n + 1))) -
        iso (avg q (G (n + 1) - P (F (n + 1)))))‖ = x' at hmic hmac htot hx'0 ⊢
      generalize l2 (avg q (G (n + 1) - P (F (n + 1)))) = y' at hmic hmac
      generalize ‖weighted q (G (n + 1) - P (F (n + 1)))‖ = a' at htot ⊢
      generalize ‖weighted q (G n - P (F n))‖ = a at htot iha haA
      generalize ‖weighted q ((G n - P (F n)) - iso (avg q (G n - P (F n))))‖ = x at hmic ihx
      generalize l2 (avg q (G n - P (F n))) = y at hmac hy0
      generalize ‖weighted q (P (genL D q ε σ (F (n + 1) - P (F (n + 1)))))‖ = dd at hmic htot hdn'
      -- micro bound
      have hx : x' ≤ ξ := by
        have e1 : r * y' ≤ r * A + r ^ 2 * x' := by
          have : r * y' ≤ r * (A + r * x') :=
            mul_le_mul_of_nonneg_left (by linarith only [hmac, hy0]) hr0
          linarith only [this]
        have e2 : r ^ 2 * x' ≤ θ / 2 * x' := mul_le_mul_of_nonneg_right hr2 hx'0
        have e3 : τ * dd ≤ τ * H := mul_le_mul_of_nonneg_left hdn' hτ.le
        have e5 : r * δ + r * A = θ * ξ / 2 := by rw [← mul_add]; exact hrξ
        have e6 : (1 + θ / 2) * x' ≤ (1 + θ / 2) * ξ := by
          linarith only [hmic, e1, e2, e3, hτH, ihx, e5]
        exact le_of_mul_le_mul_left e6 (by positivity)
      refine ⟨hx, ?_⟩
      -- total bound
      have h6 : a' ^ 2 ≤ a * a' + τ * (H * ξ) := by
        refine htot.trans ?_
        have : dd * x' ≤ H * ξ := mul_le_mul hdn' hx hx'0 hH0
        have := mul_le_mul_of_nonneg_left this hτ.le
        linarith only [this]
      have h7 : a * a' ≤ (a ^ 2 + a' ^ 2) / 2 := by nlinarith only [sq_nonneg (a - a')]
      have h8 : a' ^ 2 ≤ a ^ 2 + 2 * τ * H * ξ := by linarith only [h6, h7]
      calc a' ^ 2 ≤ a ^ 2 + 2 * τ * H * ξ := h8
        _ ≤ n * (2 * τ * H * ξ) + 2 * τ * H * ξ := by linarith only [iha]
        _ = ((n + 1 : ℕ) : ℝ) * (2 * τ * H * ξ) := by push_cast; ring
  have hEA := hle_A n hn (key n hn).2
  have h1 : G n - F n = (G n - P (F n)) - (F n - P (F n)) := by abel
  calc ‖weighted q (G n - F n)‖
      ≤ ‖weighted q (G n - P (F n))‖ + ‖weighted q (F n - P (F n))‖ := by
        rw [h1, weighted_sub]; exact norm_sub_le _ _
    _ ≤ A + δ := add_le_add hEA (happrox n)
    _ = δ * (2 + 4 * (N * τ) * (m * ‖D‖) ^ 2 / σ) := by rw [hA, hc, hT, hB]; ring

end Sharp

section TwoMoment

variable {X V : Type*} [Fintype X] [Fintype V]

/-- The second moment `⟨μ²⟩` of the quadrature. -/
def mu2 (q : Quadrature V) : ℝ := ∑ v, q.w v * q.μ v ^ 2

omit [Fintype X] in
theorem avg_mon1 (q : Quadrature V) (hμ : ∑ v, q.w v * q.μ v = 0) (u : X → ℝ) :
    avg q (mon q 1 u) = 0 := by
  funext i
  simp only [avg, mon, Matrix.of_apply, pow_one, Pi.zero_apply]
  rw [show ∑ v, q.w v * (u i * q.μ v) = (∑ v, q.w v * q.μ v) * u i by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun v _ => by ring, hμ, zero_mul]

omit [Fintype X] in
theorem avg_scaleMu_mon1 (q : Quadrature V) (u : X → ℝ) :
    avg q (scaleMu q (mon q 1 u)) = mu2 q • u := by
  funext i
  simp only [avg, scaleMu, mon, Matrix.of_apply, pow_one, Pi.smul_apply, smul_eq_mul, mu2,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun v _ => by ring

omit [Fintype X] in
theorem mon1_add (q : Quadrature V) (u w : X → ℝ) :
    mon q 1 (u + w) = mon q 1 u + mon q 1 w := by
  ext i v; simp [mon, add_mul]

omit [Fintype X] in
theorem mon1_smul (q : Quadrature V) (r : ℝ) (u : X → ℝ) :
    mon q 1 (r • u) = r • mon q 1 u := by
  ext i v; simp [mon, mul_assoc]

/-- `⟨e ⊗ μ, g⟩_w = ∑_i e_i ⟨μ g⟩_i`. -/
theorem winner_mon1 (q : Quadrature V) (b : X → ℝ) (g : Matrix X V ℝ) :
    winner q (mon q 1 b) g = ∑ i, b i * avg q (scaleMu q g) i := by
  rw [winner_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mon, scaleMu, avg, Matrix.of_apply, pow_one, Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ => by ring

/-- **The two-moment Galerkin projector** onto `ℝ^X ⊗ span {1, μ}`:
`P f = ⟨f⟩ ⊗ 1 + ⟨μ²⟩⁻¹ ⟨μ f⟩ ⊗ μ`.  Its range consists of the matrices of rank at most two with
rows in the span of the equilibrium `1` and the Chapman–Enskog direction `μ`. -/
noncomputable def proj2 (q : Quadrature V) : Matrix X V ℝ →ₗ[ℝ] Matrix X V ℝ where
  toFun f := iso (avg q f) + (mu2 q)⁻¹ • mon q 1 (avg q (scaleMu q f))
  map_add' x y := by
    rw [avg_add, iso_add, scaleMu_add, avg_add, mon1_add]
    module
  map_smul' r x := by
    have h1 : scaleMu q (r • x) = r • scaleMu q x := by ext i v; simp [scaleMu]; ring
    rw [avg_smul, iso_smul, h1, avg_smul, mon1_smul, RingHom.id_apply]
    module

omit [Fintype X] in
theorem proj2_apply (q : Quadrature V) (f : Matrix X V ℝ) :
    proj2 q f = iso (avg q f) + (mu2 q)⁻¹ • mon q 1 (avg q (scaleMu q f)) := rfl

omit [Fintype X] in
theorem mon1_zero (q : Quadrature V) : mon q 1 (0 : X → ℝ) = 0 := by
  ext i v; simp [mon]

omit [Fintype X] in
/-- `proj2` fixes the isotropic matrices. -/
theorem proj2_iso (q : Quadrature V) (hμ : ∑ v, q.w v * q.μ v = 0) (ρ : X → ℝ) :
    proj2 q (iso ρ : Matrix X V ℝ) = iso ρ := by
  rw [proj2_apply, avg_iso, avg_scaleMu_iso q hμ, mon1_zero, smul_zero, add_zero]

omit [Fintype X] in
/-- `proj2` fixes the matrices `u ⊗ μ`. -/
theorem proj2_mon1 (q : Quadrature V) (hμ : ∑ v, q.w v * q.μ v = 0) (hμ2 : mu2 q ≠ 0)
    (u : X → ℝ) : proj2 q (mon q 1 u) = mon q 1 u := by
  rw [proj2_apply, avg_mon1 q hμ, avg_scaleMu_mon1, mon1_smul]
  have h0 : (iso (0 : X → ℝ) : Matrix X V ℝ) = 0 := by ext i v; simp [iso]
  rw [h0, zero_add, smul_smul, inv_mul_cancel₀ hμ2, one_smul]

/-- The weighted pairing of `proj2 f` with `g`. -/
theorem proj2_winner (q : Quadrature V) (f g : Matrix X V ℝ) :
    winner q (proj2 q f) g = ∑ i, avg q f i * avg q g i +
      (mu2 q)⁻¹ * ∑ i, avg q (scaleMu q f) i * avg q (scaleMu q g) i := by
  rw [proj2_apply, winner_add_left, winner_smul_left, winner_comm q (iso _), winner_iso,
    winner_mon1, show (∑ i, avg q g i * avg q f i) = ∑ i, avg q f i * avg q g i from
      Finset.sum_congr rfl fun i _ => mul_comm _ _]

/-- **`proj2` is a velocity Galerkin projector** for every quadrature with `⟨μ⟩ = 0` and
`⟨μ²⟩ ≠ 0`. -/
theorem isVelocityGalerkin_proj2 (q : Quadrature V) (hμ : ∑ v, q.w v * q.μ v = 0)
    (hμ2 : mu2 q ≠ 0) : IsVelocityGalerkin q (proj2 (X := X) q) where
  idem f := by
    rw [proj2_apply (f := f), map_add, map_smul, proj2_iso q hμ, proj2_mon1 q hμ hμ2]
  symm f g := by
    rw [proj2_winner, winner_comm, proj2_winner,
      show (∑ i, avg q g i * avg q f i) = ∑ i, avg q f i * avg q g i from
        Finset.sum_congr rfl fun i _ => mul_comm _ _,
      show (∑ i, avg q (scaleMu q g) i * avg q (scaleMu q f) i) =
          ∑ i, avg q (scaleMu q f) i * avg q (scaleMu q g) i from
        Finset.sum_congr rfl fun i _ => mul_comm _ _]
  iso_fixed := proj2_iso q hμ

omit [Fintype X] in
/-- `proj2` fixes `1` and `μ`: the hypothesis `hk` of the main theorems with `k = 2`. -/
theorem proj2_mon (q : Quadrature V) (hμ : ∑ v, q.w v * q.μ v = 0) (hμ2 : mu2 q ≠ 0) :
    ∀ j < 2, ∀ u : X → ℝ, proj2 q (mon q j u) = mon q j u := by
  intro j hj u
  interval_cases j
  · rw [← iso_eq_mon]; exact proj2_iso q hμ u
  · exact proj2_mon1 q hμ hμ2 u

omit [Fintype X] in
/-- Every matrix in the range of `proj2` has rank at most two. -/
theorem rank_proj2_le [Finite X] (q : Quadrature V) (f : Matrix X V ℝ) :
    (proj2 q f).rank ≤ 2 := by
  set u : ℕ → X → ℝ := fun j => if j = 0 then avg q f else (mu2 q)⁻¹ • avg q (scaleMu q f)
    with hu
  obtain ⟨A, hA⟩ := exists_sum_mon_eq q 1 2 u
  have h1 : proj2 q f = A * vand q 2 := by
    rw [← hA, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, pow_one, one_smul, one_smul, proj2_apply, iso_eq_mon q, hu]
    simp only [ite_true, one_ne_zero, ite_false]
    rw [mon1_smul]
  rw [h1]
  exact rank_mul_vand_le q A

/-- `⟨μ²⟩ > 0` as soon as some node is nonzero. -/
theorem mu2_pos (q : Quadrature V) {v₀ : V} (hv : q.μ v₀ ≠ 0) : 0 < mu2 q := by
  unfold mu2
  refine Finset.sum_pos' (fun v _ => mul_nonneg (q.w_pos v).le (sq_nonneg _))
    ⟨v₀, Finset.mem_univ _, mul_pos (q.w_pos v₀) (by positivity)⟩

end TwoMoment

section Existence

variable {X V : Type*} [Fintype X] [Fintype V] {D : Matrix X X ℝ} {q : Quadrature V}
  {P : Matrix X V ℝ →ₗ[ℝ] Matrix X V ℝ} {ε σ τ : ℝ}

/-- **Well-posedness of the Galerkin step**: for skew-symmetric `D` and every `ε, σ, τ > 0`, the
implicit Galerkin equation `p = f + τ P L p` has exactly one solution for each `f`. -/
theorem existsUnique_galerkin_step (hP : IsVelocityGalerkin q P) (hD : D.transpose = -D)
    (hε : 0 < ε) (hσ : 0 < σ) (hτ : 0 < τ) (f : Matrix X V ℝ) :
    ∃! p : Matrix X V ℝ, p = f + τ • P (genL D q ε σ p) := by
  set T : Matrix X V ℝ →ₗ[ℝ] Matrix X V ℝ := LinearMap.id - τ • (P ∘ₗ genL D q ε σ) with hT
  have hTapp : ∀ p, T p = p - τ • P (genL D q ε σ p) := fun p => by
    simp [hT]
  have inj : Function.Injective T := by
    refine (injective_iff_map_eq_zero _).2 fun p hp => ?_
    rw [hTapp, sub_eq_zero] at hp
    have hPp : P p = p := by
      conv_lhs => rw [hp]
      rw [map_smul, hP.idem, ← hp]
    have h1 : p = 0 + τ • P (genL D q ε σ p) := by rw [zero_add]; exact hp
    have h2 := galerkin_contract hP hD hε hσ hτ hPp h1
    rw [weighted_zero, norm_zero] at h2
    exact eq_zero_of_weighted q (norm_le_zero_iff.mp h2)
  obtain ⟨p, hp⟩ := LinearMap.injective_iff_surjective.1 inj f
  rw [hTapp, sub_eq_iff_eq_add] at hp
  refine ⟨p, hp, fun p' hp' => inj ?_⟩
  have e1 : T p = f := by rw [hTapp, sub_eq_iff_eq_add]; exact hp
  have e2 : T p' = f := by rw [hTapp, sub_eq_iff_eq_add]; exact hp'
  exact e2.trans e1.symm

/-- **Existence of Galerkin trajectories**: the hypotheses of the main theorems can be met for
every initial value in the range of `P`. -/
theorem exists_galerkinEuler (hP : IsVelocityGalerkin q P) (hD : D.transpose = -D) (hε : 0 < ε)
    (hσ : 0 < σ) (hτ : 0 < τ) {G₀ : Matrix X V ℝ} (hG₀ : P G₀ = G₀) :
    ∃ G : ℕ → Matrix X V ℝ, G 0 = G₀ ∧ IsGalerkinEuler P D q ε σ τ G := by
  -- one step: from `f` in the range to the solution, which is again in the range
  have step : ∀ f : Matrix X V ℝ, P f = f →
      ∃ p, P p = p ∧ p = f + τ • P (genL D q ε σ p) := fun f hf => by
    obtain ⟨p, hp, -⟩ := existsUnique_galerkin_step hP hD hε hσ hτ f
    refine ⟨p, ?_, hp⟩
    conv_lhs => rw [hp]
    rw [map_add, map_smul, hP.idem, hf, ← hp]
  -- iterate on the subtype of the range
  choose S hS using fun f : {f : Matrix X V ℝ // P f = f} => step f.1 f.2
  let next : {f : Matrix X V ℝ // P f = f} → {f : Matrix X V ℝ // P f = f} :=
    fun f => ⟨S f, (hS f).1⟩
  let Gs : ℕ → {f : Matrix X V ℝ // P f = f} := fun n => Nat.rec ⟨G₀, hG₀⟩ (fun _ y => next y) n
  refine ⟨fun n => (Gs n).1, rfl, fun n => ⟨(Gs n).2, ?_⟩⟩
  exact (hS (Gs n)).2

end Existence

section Layer

/-- Entries of a solution of the semi-discrete equation are differentiable, with the entries of
the generator as derivatives. -/
theorem hasDerivAt_entry {X V : Type*} [Fintype X] [Fintype V] {D : Matrix X X ℝ}
    {q : Quadrature V} {ε σ : ℝ} {y : ℝ → Matrix X V ℝ}
    (hy : ∀ s, HasDerivAt y (genL D q ε σ (y s)) s) (i : X) (v : V) (s : ℝ) :
    HasDerivAt (fun s => y s i v) (genL D q ε σ (y s) i v) s := by
  have h := (LinearMap.toContinuousLinearMap
    (Matrix.entryLinearMap ℝ ℝ i v)).hasFDerivAt.comp_hasDerivAt s (hy s)
  convert h using 1 <;> rfl

theorem antitoneOn_Ici_of_hasDerivAt {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (h : ∀ x, 0 < x → f' x ≤ 0) : AntitoneOn f (Set.Ici 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (fun x _ => (hf x).continuousAt.continuousWithinAt)
    (fun x _ => (hf x).differentiableAt.differentiableWithinAt) fun x hx => ?_
  rw [interior_Ici] at hx
  rw [(hf x).deriv]
  exact h x hx

theorem monotoneOn_Icc_of_hasDerivAt {f f' : ℝ → ℝ} {a b : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (h : ∀ x, a < x → x < b → 0 ≤ f' x) : MonotoneOn f (Set.Icc a b) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc a b)
    (fun x _ => (hf x).continuousAt.continuousWithinAt)
    (fun x _ => (hf x).differentiableAt.differentiableWithinAt) fun x hx => ?_
  rw [interior_Icc] at hx
  rw [(hf x).deriv]
  exact h x hx.1 hx.2

/-- The four entries of the telegraph generator `-ε⁻¹ D f diag(μ) + σ ε⁻² (⟨f⟩ - f)` with
`D = rot K`, `μ = ±1`, `w = 1/2`. -/
theorem genL_telegraph (K ε σ : ℝ) (f : Matrix (Fin 2) (Fin 2) ℝ) :
    genL (rot K) telegraph ε σ f 0 0 =
        σ / ε ^ 2 * ((f 0 0 + f 0 1) / 2 - f 0 0) - ε⁻¹ * (K * f 1 0) ∧
      genL (rot K) telegraph ε σ f 0 1 =
        σ / ε ^ 2 * ((f 0 0 + f 0 1) / 2 - f 0 1) + ε⁻¹ * (K * f 1 1) ∧
      genL (rot K) telegraph ε σ f 1 0 =
        σ / ε ^ 2 * ((f 1 0 + f 1 1) / 2 - f 1 0) + ε⁻¹ * (K * f 0 0) ∧
      genL (rot K) telegraph ε σ f 1 1 =
        σ / ε ^ 2 * ((f 1 0 + f 1 1) / 2 - f 1 1) - ε⁻¹ * (K * f 0 1) := by
  simp only [genL_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, iso, Matrix.of_apply,
    avg, telegraph, transport, rot, Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    one_div]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- **Uniform first order fails inside the initial layer.**  Telegraph model (two velocities
`±1`, one Fourier mode `rot K`), isotropic data `ρ₀ ⊗ 1` with `ρ₀ = e₁`, time step `τ = ε²/σ`
and `K ε ≤ σ/10`: the error of the first implicit Euler step against the exact semi-discrete flow
is at least `ε K / (16 σ) = K √τ / (16 √σ)`.  So no bound `‖F_n - f(t_n)‖ ≤ C τ` with `C`
independent of `ε` holds uniformly in `n`, for isotropic ("well-prepared" in the sense of the
AP literature) data: the uniform rate over all `n` is at most `1/2`, and any `ε`-term in a uniform
bound must have exponent `≤ 1`.  Every low-rank scheme that reduces to implicit Euler on this
two-velocity model (rank `≥ 2`, or `proj2`) inherits the bound.  Numerically the error at a
fixed final time is uniformly `O(τ)`; this is an initial-layer effect on the micro variable. -/
theorem telegraph_layer_error {ε σ K : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (hK : 0 ≤ K)
    (hsmall : K * ε ≤ σ / 10) {y : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hy : ∀ s, HasDerivAt y (genL (rot K) telegraph ε σ (y s)) s) (hy0 : y 0 = iso ![1, 0])
    {F : ℕ → Matrix (Fin 2) (Fin 2) ℝ} (hF : IsImplicitEuler (rot K) telegraph ε σ (ε ^ 2 / σ) F)
    (hF0 : F 0 = iso ![1, 0]) :
    ε * K / (16 * σ) ≤ ‖weighted telegraph (y (ε ^ 2 / σ) - F 1)‖ := by
  set τ := ε ^ 2 / σ with hτdef
  have hτ : 0 < τ := by positivity
  have hε2τ : ε ^ 2 / τ = σ := by rw [hτdef]; field_simp
  -- (A) the implicit Euler iterate
  have hF1 : F 1 = teleSol ((σ + ε ^ 2 / τ) / (σ + ε ^ 2 / τ + τ * K ^ 2))
      (ε * K / (σ + ε ^ 2 / τ)) := by
    refine (existsUnique_step (rot_skew K) hε hσ hτ (F 0)).unique (hF 0) ?_
    rw [hF0]; exact teleSol_step hε hσ hτ
  have hF10 : F 1 1 0 =
      (σ + ε ^ 2 / τ) / (σ + ε ^ 2 / τ + τ * K ^ 2) * (ε * K / (σ + ε ^ 2 / τ)) := by
    rw [hF1]; simp [teleSol]
  have hF11 : F 1 1 1 = -F 1 1 0 := by
    rw [hF1]; simp [teleSol]
  have hF10_le : F 1 1 0 ≤ ε * K / (2 * σ) := by
    rw [hF10, hε2τ]
    have h1 : 0 ≤ τ * K ^ 2 := by positivity
    rw [show (σ + σ) / (σ + σ + τ * K ^ 2) * (ε * K / (σ + σ)) = ε * K / (σ + σ + τ * K ^ 2) by
      field_simp]
    gcongr
    linarith
  -- (B) the entries of the flow and their derivatives
  have hd := fun i v s => hasDerivAt_entry hy i v s
  have ha : ∀ t, HasDerivAt (fun t => y t 0 0)
      (σ / ε ^ 2 * ((y t 0 0 + y t 0 1) / 2 - y t 0 0) - ε⁻¹ * (K * y t 1 0)) t := fun t =>
    (hd 0 0 t).congr_deriv (genL_telegraph K ε σ (y t)).1
  have ha1 : ∀ t, HasDerivAt (fun t => y t 0 1)
      (σ / ε ^ 2 * ((y t 0 0 + y t 0 1) / 2 - y t 0 1) + ε⁻¹ * (K * y t 1 1)) t := fun t =>
    (hd 0 1 t).congr_deriv (genL_telegraph K ε σ (y t)).2.1
  have hb : ∀ t, HasDerivAt (fun t => y t 1 0)
      (σ / ε ^ 2 * ((y t 1 0 + y t 1 1) / 2 - y t 1 0) + ε⁻¹ * (K * y t 0 0)) t := fun t =>
    (hd 1 0 t).congr_deriv (genL_telegraph K ε σ (y t)).2.2.1
  have hb1 : ∀ t, HasDerivAt (fun t => y t 1 1)
      (σ / ε ^ 2 * ((y t 1 0 + y t 1 1) / 2 - y t 1 1) - ε⁻¹ * (K * y t 0 1)) t := fun t =>
    (hd 1 1 t).congr_deriv (genL_telegraph K ε σ (y t)).2.2.2
  have hy00 : y 0 0 0 = 1 := by rw [hy0]; simp [iso]
  have hy01 : y 0 0 1 = 1 := by rw [hy0]; simp [iso]
  have hy10 : y 0 1 0 = 0 := by rw [hy0]; simp [iso]
  have hy11 : y 0 1 1 = 0 := by rw [hy0]; simp [iso]
  -- (C) the invariant subspace: u = y₀₀ - y₀₁ and v = y₁₀ + y₁₁ vanish for t ≥ 0
  have hu : ∀ t, HasDerivAt (fun t => y t 0 0 - y t 0 1)
      (-(σ / ε ^ 2) * (y t 0 0 - y t 0 1) - ε⁻¹ * K * (y t 1 0 + y t 1 1)) t := fun t =>
    ((ha t).sub (ha1 t)).congr_deriv (by ring)
  have hv : ∀ t, HasDerivAt (fun t => y t 1 0 + y t 1 1)
      (ε⁻¹ * K * (y t 0 0 - y t 0 1)) t := fun t =>
    ((hb t).add (hb1 t)).congr_deriv (by ring)
  have hφ : ∀ t, HasDerivAt (fun t => (y t 0 0 - y t 0 1) ^ 2 + (y t 1 0 + y t 1 1) ^ 2)
      (-(2 * (σ / ε ^ 2)) * (y t 0 0 - y t 0 1) ^ 2) t := fun t => by
    have h := ((hu t).pow 2).add ((hv t).pow 2)
    refine h.congr_deriv ?_
    push_cast
    ring
  have hφanti := antitoneOn_Ici_of_hasDerivAt hφ fun t _ => by
    have : 0 ≤ 2 * (σ / ε ^ 2) * (y t 0 0 - y t 0 1) ^ 2 := by positivity
    linarith
  have hinv : ∀ t, 0 ≤ t → y t 0 1 = y t 0 0 ∧ y t 1 1 = -y t 1 0 := fun t ht => by
    have h1 := hφanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
    simp only [hy00, hy01, hy10, hy11, sub_self, add_zero] at h1
    norm_num at h1
    have hA := sq_nonneg (y t 0 0 - y t 0 1)
    have hB := sq_nonneg (y t 1 0 + y t 1 1)
    have h2 : (y t 0 0 - y t 0 1) ^ 2 = 0 := by linarith
    have h3 : (y t 1 0 + y t 1 1) ^ 2 = 0 := by linarith
    have h2' : y t 0 0 - y t 0 1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp h2
    have h3' : y t 1 0 + y t 1 1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp h3
    constructor
    · linarith
    · linarith
  -- (D) dissipativity: a² + b² ≤ 1 for t ≥ 0
  have hψ : ∀ t, HasDerivAt (fun t => y t 0 0 ^ 2 + y t 1 0 ^ 2)
      (2 * y t 0 0 * (σ / ε ^ 2 * ((y t 0 0 + y t 0 1) / 2 - y t 0 0) - ε⁻¹ * (K * y t 1 0)) +
        2 * y t 1 0 * (σ / ε ^ 2 * ((y t 1 0 + y t 1 1) / 2 - y t 1 0) + ε⁻¹ * (K * y t 0 0)))
      t := fun t => by
    have h := ((ha t).pow 2).add ((hb t).pow 2)
    refine h.congr_deriv ?_
    push_cast
    ring
  have hψanti := antitoneOn_Ici_of_hasDerivAt hψ fun t ht => by
    obtain ⟨h1, h2⟩ := hinv t ht.le
    rw [h1, h2]
    have : 0 ≤ 2 * (σ / ε ^ 2) * y t 1 0 ^ 2 := by positivity
    nlinarith
  have hb_le : ∀ t, 0 ≤ t → y t 1 0 ≤ 1 := fun t ht => by
    have h1 := hψanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
    simp only [hy00, hy10] at h1
    norm_num at h1
    nlinarith [sq_nonneg (y t 0 0), sq_nonneg (y t 1 0 - 1)]
  -- (E) the macro variable stays close to one on `[0, τ]`
  have hΨ : ∀ t, HasDerivAt (fun t => y t 0 0 + ε⁻¹ * K * t)
      (σ / ε ^ 2 * ((y t 0 0 + y t 0 1) / 2 - y t 0 0) - ε⁻¹ * (K * y t 1 0) + ε⁻¹ * K) t :=
    fun t => by
      have h := (ha t).add ((hasDerivAt_id t).const_mul (ε⁻¹ * K))
      convert h using 1 <;> first | rfl | simp
  have hΨmono := monotoneOn_Icc_of_hasDerivAt (a := 0) (b := τ) hΨ fun t ht _ => by
    obtain ⟨h1, -⟩ := hinv t ht.le
    rw [h1]
    have h2 := hb_le t ht.le
    have : 0 ≤ ε⁻¹ * K * (1 - y t 1 0) := by
      apply mul_nonneg (by positivity); linarith
    nlinarith
  have hKε : K * ε / σ ≤ 1 / 10 := by rw [div_le_iff₀ hσ]; linarith
  have ha_ge : ∀ t, 0 ≤ t → t ≤ τ → 9 / 10 ≤ y t 0 0 := fun t ht0 htτ => by
    have h1 := hΨmono (Set.left_mem_Icc.mpr hτ.le) ⟨ht0, htτ⟩ ht0
    simp only [hy00, mul_zero, add_zero] at h1
    have h2 : ε⁻¹ * K * t ≤ ε⁻¹ * K * τ := by gcongr
    have h3 : ε⁻¹ * K * τ = K * ε / σ := by rw [hτdef]; field_simp
    linarith
  -- (F) Duhamel: `e^{σ t/ε²} b(t) - (9/10)(ε K/σ)(e^{σ t/ε²} - 1)` is nondecreasing on `[0, τ]`
  set c := σ / ε ^ 2 with hcdef
  have hc : 0 < c := by positivity
  have hcτ : c * τ = 1 := by rw [hcdef, hτdef]; field_simp
  have hexp : ∀ t, HasDerivAt (fun t => Real.exp (c * t)) (Real.exp (c * t) * c) t := fun t => by
    have h := ((hasDerivAt_id t).const_mul c).exp
    simpa using h
  set κ := 9 / 10 * (ε * K / σ) with hκdef
  have hκc : κ * c = ε⁻¹ * K * (9 / 10) := by rw [hκdef, hcdef]; field_simp
  have hΦ : ∀ t, HasDerivAt (fun t => Real.exp (c * t) * y t 1 0 - κ * (Real.exp (c * t) - 1))
      (Real.exp (c * t) * c * y t 1 0 + Real.exp (c * t) *
        (σ / ε ^ 2 * ((y t 1 0 + y t 1 1) / 2 - y t 1 0) + ε⁻¹ * (K * y t 0 0)) -
          κ * (Real.exp (c * t) * c)) t := fun t =>
    ((hexp t).mul (hb t)).sub (((hexp t).sub_const 1).const_mul κ)
  have hΦmono := monotoneOn_Icc_of_hasDerivAt (a := 0) (b := τ) hΦ fun t ht0 htτ => by
    obtain ⟨-, h2⟩ := hinv t ht0.le
    rw [h2]
    have h3 := ha_ge t ht0.le htτ.le
    have h4 : 0 ≤ Real.exp (c * t) * (ε⁻¹ * K * (y t 0 0 - 9 / 10)) := by
      apply mul_nonneg (Real.exp_pos _).le
      apply mul_nonneg (by positivity); linarith
    have h5 : Real.exp (c * t) * c * y t 1 0 + Real.exp (c * t) *
        (σ / ε ^ 2 * ((y t 1 0 + -y t 1 0) / 2 - y t 1 0) + ε⁻¹ * (K * y t 0 0)) -
          κ * (Real.exp (c * t) * c) = Real.exp (c * t) * (ε⁻¹ * K * (y t 0 0 - 9 / 10)) := by
      rw [hcdef] at hκc ⊢
      have : κ * (Real.exp (σ / ε ^ 2 * t) * (σ / ε ^ 2)) =
          Real.exp (σ / ε ^ 2 * t) * (ε⁻¹ * K * (9 / 10)) := by rw [← hκc]; ring
      rw [this]; ring
    rw [h5]; exact h4
  have hΦτ := hΦmono (Set.left_mem_Icc.mpr hτ.le) (Set.right_mem_Icc.mpr hτ.le) hτ.le
  simp only [mul_zero, Real.exp_zero, hy10, sub_self, hcτ] at hΦτ
  -- (G) the lower bound on `b(τ)`
  have hE := Real.exp_one_gt_d9
  have hE0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hbτ : κ * (Real.exp 1 - 1) / Real.exp 1 ≤ y τ 1 0 := by
    rw [div_le_iff₀ hE0]
    have : Real.exp 1 * y τ 1 0 = y τ 1 0 * Real.exp 1 := mul_comm _ _
    linarith
  rw [hκdef] at hbτ
  have hεKσ : 0 ≤ ε * K / σ := by positivity
  have hgap : ε * K / (16 * σ) ≤ y τ 1 0 - F 1 1 0 := by
    have h1 : 9 / 10 * (Real.exp 1 - 1) / Real.exp 1 - 1 / 2 ≥ 1 / 16 := by
      rw [ge_iff_le, le_sub_iff_add_le, le_div_iff₀ hE0]
      linarith
    have h2 : ε * K / (16 * σ) = ε * K / σ * (1 / 16) := by field_simp
    have h3 : ε * K / (2 * σ) = ε * K / σ * (1 / 2) := by field_simp
    have h4 : 9 / 10 * (ε * K / σ) * (Real.exp 1 - 1) / Real.exp 1 =
        ε * K / σ * (9 / 10 * (Real.exp 1 - 1) / Real.exp 1) := by field_simp
    rw [h2]
    have h5 : ε * K / σ * (1 / 16) ≤ ε * K / σ * (9 / 10 * (Real.exp 1 - 1) / Real.exp 1 - 1 / 2) :=
      mul_le_mul_of_nonneg_left h1.le hεKσ
    rw [h4] at hbτ
    rw [h3] at hF10_le
    linarith
  -- (H) the norm of the error dominates the `(1, ·)` entries
  have hgap0 : 0 ≤ y τ 1 0 - F 1 1 0 := le_trans (by positivity) hgap
  have hnorm : (y τ 1 0 - F 1 1 0) ^ 2 ≤ ‖weighted telegraph (y τ - F 1)‖ ^ 2 := by
    rw [sq_norm_weighted]
    have hw : ∀ v, telegraph.w v = 1 / 2 := by intro v; fin_cases v <;> simp [telegraph]
    simp only [Fin.sum_univ_two, hw, Matrix.sub_apply]
    obtain ⟨-, h2⟩ := hinv τ hτ.le
    rw [h2, hF11]
    nlinarith [sq_nonneg (y τ 0 0 - F 1 0 0), sq_nonneg (y τ 0 1 - F 1 0 1)]
  have := (pow_le_pow_iff_left₀ hgap0 (norm_nonneg _) two_ne_zero).mp hnorm
  linarith

/-- **No uniform first-order bound over all steps.**  For every `C` there are `ε, τ > 0`, a
solution `y` of the semi-discrete telegraph equation (`σ = K = 1`) with isotropic data, and an
implicit Euler trajectory `F` from the same data, whose first-step error exceeds `C τ`.  The
objects exist (`exists_flow`, `existsUnique_implicitEuler`), so the statement is not vacuous. -/
theorem no_uniform_first_order (C : ℝ) :
    ∃ ε τ : ℝ, 0 < ε ∧ 0 < τ ∧ ∃ y : ℝ → Matrix (Fin 2) (Fin 2) ℝ,
      (∀ s, HasDerivAt y (genL (rot 1) telegraph ε 1 (y s)) s) ∧ y 0 = iso ![1, 0] ∧
      ∃ F : ℕ → Matrix (Fin 2) (Fin 2) ℝ, F 0 = iso ![1, 0] ∧
        IsImplicitEuler (rot 1) telegraph ε 1 τ F ∧
        C * τ < ‖weighted telegraph (y τ - F 1)‖ := by
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set ε := min (1 / 10) (1 / (32 * (C' + 1))) with hεdef
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε ≤ 1 / 10 := min_le_left _ _
  have hε2 : ε ≤ 1 / (32 * (C' + 1)) := min_le_right _ _
  obtain ⟨y, hy0, hy⟩ := exists_flow (rot 1) telegraph ε 1 (iso ![1, 0])
  have hτ : 0 < ε ^ 2 / 1 := by positivity
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ := existsUnique_implicitEuler (q := telegraph) (rot_skew 1) hε one_pos
    hτ (iso ![1, 0])
  refine ⟨ε, ε ^ 2 / 1, hε, hτ, y, hy, hy0, F, hF0, hF, ?_⟩
  have h1 := telegraph_layer_error hε one_pos zero_le_one (by linarith) hy hy0 hF hF0
  have h2 : C * (ε ^ 2 / 1) < ε * 1 / (16 * 1) := by
    have h3 : ε * (32 * (C' + 1)) ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at hε2; linarith
    have h4 : C ≤ C' := le_max_left _ _
    have h5 : C * ε ^ 2 ≤ C' * ε ^ 2 := mul_le_mul_of_nonneg_right h4 (by positivity)
    have h6 : C' * ε ^ 2 < ε / 16 := by nlinarith
    linarith
  linarith

/-- **The rank-two scheme.**  Instantiation of `galerkin_sub_full_le_cfl` with the two-moment
projector `proj2`: under `⟨μ⟩ = 0`, `⟨μ²⟩ ≠ 0` and the step-size condition, the Galerkin scheme
with frozen velocity basis `{1, μ}`, whose iterates have rank at most two (`rank_proj2_le`), stays
within `(ε m / σ)² ‖D² ρ₀‖₂ (2 + 4 T (m ‖D‖_F)² / σ)` of the full discrete-velocity solution,
uniformly in `ε` and `τ`. -/
theorem rank2_sub_full_le {X V : Type*} [Fintype X] [Fintype V] [DecidableEq X]
    {D : Matrix X X ℝ} {q : Quadrature V} {ε σ τ m : ℝ} (hD : D.transpose = -D) (hε : 0 < ε)
    (hσ : 0 < σ) (hτ : 0 < τ) (hm0 : 0 ≤ m) (hm : ∀ v, |q.μ v| ≤ m)
    (hμ : ∑ v, q.w v * q.μ v = 0) (hμ2 : mu2 q ≠ 0) (hcfl : τ * (m * ‖D‖) ^ 2 ≤ σ / 2)
    {F G : ℕ → Matrix X V ℝ} {ρ₀ : X → ℝ} (hF : IsImplicitEuler D q ε σ τ F) (hF0 : F 0 = iso ρ₀)
    (hG : IsGalerkinEuler (proj2 q) D q ε σ τ G) (hG0 : G 0 = iso ρ₀) {N n : ℕ} (hn : n ≤ N) :
    ‖weighted q (G n - F n)‖ ≤ (ε * m / σ) ^ 2 * l2 ((D ^ 2).mulVec ρ₀) *
      (2 + 4 * (N * τ) * (m * ‖D‖) ^ 2 / σ) :=
  galerkin_sub_full_le_cfl hD hε hσ hτ hm0 hm hμ (isVelocityGalerkin_proj2 q hμ hμ2) le_rfl
    (proj2_mon q hμ hμ2) hcfl hF hF0 hG hG0 hn

end Layer

end LeanDLRA.Novel.OpST21
