import LeanDLRA.Classical.SVD
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.OpenProblems.Curated.Classicala
import LeanDLRA.OpenProblems.Stability.Part3c
import LeanDLRA.Kinetic.LowRank

/-!
# Quasi-conservative dynamical low-rank approximation for Vlasov (arXiv 1807.02338)

Einkemmer, Lubich, *A quasi-conservative dynamical low-rank algorithm for the Vlasov equation*,
Sections 3 and 5; Section 4 is a separate module.  We work with the actual operator
`F(f) = -v·∇ₓf + E·∇ᵥf` on `ℝ^d × ℝ^d` (`vlasovF`), with density, momentum and momentum flux given
by integrals (`rho`, `momentum`, `stress`) and with `f = ∑ K_j V_j = ∑ X_k S_kl V_l = ∑ X_k L_k`.
For the corrected K-, S- and L-step (3.5), (3.9), (3.12), which add (3.4) to the splitting, we
compute the residuals of the conservation laws, show that the projected laws are equivalent to the
systems (3.8), and solve those by the minimum-norm solution when the rows of `[α; β]` are
independent.  We prove the same for the post-step correction of Sec. 5 after an arbitrary inner
solver, and we prove Remarks 1 and 2.

## Main results

* Steps 1, 2: `kStep_residual`, `kStep_laws_iff`, `kStep_quasiConservative`, `sStep_residual`,
  `sStep_laws_iff`, `sStep_quasiConservative`.
* Step 3: `lStep_residual`, `rhsL_lowRank_eq_zero`, `lStep_laws_iff`, `lStep_projectedLaws`.
* The laws themselves: `moment_vlasovF_lowRank` is (3.1), (3.2) at a separated function.
* (3.8): `minNormSol_spec`, `one_add_le_of_rows`, `exists_ne_mulVec_eq`,
  `eq_minNormSol_of_card_eq`, `minNormSol_rows_le`.
* The second lines of (3.5), (3.9), (3.12): `inner_V_correction`, `innerXV_correction`,
  `inner_X_correction`.
* Sec. 5: `kStep_discrete_iff`, `sStep_discrete_iff`, `lStep_discrete_iff`.
* Remark 1: `sigmaMinL2_coreK`, `sigmaMinL2_coreK_transpose`, `kAnsatz_blowup`,
  `minNormSol_norm_le`, `kAnsatz_same_correction`.
* Remark 2: `minimal_velocity_correction`, `minimal_correction_spurious`, `ansatz_mem_submodule`,
  `ansatz_tendsto_zero`.
* Instances: two `example`s for Steps 1, 2 and the moving solution `lStep_translate_laws`.

## Claims of the paper that fail as printed

* **The sign of `Eρ` in (3.14) and in the `d_i` after it is wrong.**  It disagrees with its own
  left side, with (3.7), and with the Step 3 formula of Sec. 5: the term is `+⟨X_i, Eρ⟩` in (3.14)
  and `-⟨X_i, Eρ⟩` in `d_i`.  The printed `d_i` equals `2 ⟨X_i, E_a ρ⟩` (`printedD_eq`) and it is
  nonzero in an example where the correct right-hand side vanishes (`printed_3_14_false`).
* **Consequence, beyond the paper.**  The paper notes `b_i = 0` in Step 3.  With the correct sign
  also `d_i = 0` (`rhsL_lowRank_eq_zero`), so the time-continuous L-step needs no correction at all:
  it satisfies both projected laws, and the minimum-norm correction is zero.
* **Remark 1 overstates.**  `σ_min(K) = σ_min(S)` holds and the coefficients of the K-ansatz do blow
  up.  But the inference that "the correction overall becomes quite large" fails at `K = X S` for
  invertible `S`: the minimum-norm K-ansatz gives exactly the same correction function as the
  `X`-ansatz (`kAnsatz_same_correction`).  Only its coefficients are large.
* "(Multiple) solutions" of (3.8) needs `r > 1 + d` (`exists_ne_mulVec_eq`); for `r = 1 + d` the
  solution is unique (`eq_minNormSol_of_card_eq`).

## Misprints corrected without comment in the statements

Sec. 5, Step 1 mixes the indices `i`, `k` and writes `∑_k λ_kj α_j` for `∑_j λ_kj α_j`.  Sec. 5,
Step 2 has a single sum `∑_j ⟨X_i, ∇X_j⟩ S_ij β_j` for `∑_kj ⟨X_i, ∇X_k⟩ S_kj · β_j`, similarly
for `γ_j`, and `⟨E⁰, X_j⟩` for `⟨X_i, E⁰ X_k⟩`.  Sec. 5, Step 3 omits the weight `v` in the first
term of `d_i`.  (3.12) and Remark 2 cite (2.5) for (2.7).  We use what the paper's derivations
give, written with the flux: `rhsKDisc`, `rhsSDisc`, `rhsLDisc`.

## Modelling choices

* `E` is an arbitrary vector field, so `E = E(f)` is covered; the Poisson equation is never used.
* `μ` is an arbitrary measure on `ℝ^d`, which covers any `Ω_x`, and `∇ₓ` is `fderiv` on `ℝ^d`, so
  functions on a torus enter through their periodic extension.
* `ν` is arbitrary in Steps 1, 2 and in Sec. 5, including quadrature rules.  In Step 3, where one
  integrates by parts, `ν` is a Haar measure, so `Ω_v = ℝ^d`, and the paper's "`L_k` goes to zero as
  `|v| → ∞`" becomes the integrability in `IsVelocityProfile`.  A periodic or bounded `Ω_v` is not
  covered there.
* `⟨·,·⟩ₓᵥ` is an iterated integral, in the order in which it arises: `x` outside in Steps 1, 2 and
  `v` outside in Step 3.  Integrability hypotheses only say that the printed inner products exist.
* The time-continuous statements are at a fixed time `t`.  As in the paper, existence of solutions
  of the corrected equations is not addressed, and the `Kₛ`, `Sₛ`, `Lₛ` are assumed to solve them.
* `V` need not be orthonormal in Steps 1, 2; orthonormality only identifies (3.5) with (2.5) plus
  (3.4), see `inner_V_correction`.
* The library's `kStep_moment_hasDerivWithinAt` and `constrainedDF_solution` are the abstract
  relatives of `lStep_residual` and `minNormSol_spec`.  They do not cover the Vlasov operator or the
  matrix `[α; β]`, so they are not used.  Remark 2 is about a case where the right-hand side is
  nonzero: for the exact L-step on `ℝ^d` the constant there vanishes by `rhsL_lowRank_eq_zero`.
-/

open Set Filter Topology Finset MeasureTheory
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P1807_02338

/-! ### Minimum-norm solutions of the moment systems -/

section MinNorm

variable {ι n κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [Fintype κ]

/-- The minimum-norm solution `Aᵀ (A Aᵀ)⁻¹ b` of `A y = b`. -/
noncomputable def minNormSol (A : Matrix ι n ℝ) (b : ι → ℝ) : n → ℝ :=
  Aᵀ *ᵥ ((A * Aᵀ)⁻¹ *ᵥ b)

omit [DecidableEq ι] in
/-- Moving a matrix across the dot product. -/
lemma transpose_mulVec_dotProduct (A : Matrix ι n ℝ) (q : ι → ℝ) (y : n → ℝ) :
    (Aᵀ *ᵥ q) ⬝ᵥ y = q ⬝ᵥ (A *ᵥ y) := by
  rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]

/-- Independent rows make `A Aᵀ` invertible. -/
lemma isUnit_det_mul_transpose {A : Matrix ι n ℝ} (hA : LinearIndependent ℝ A.row) :
    IsUnit (A * Aᵀ).det := by
  rw [isUnit_iff_ne_zero, Ne, ← Matrix.exists_mulVec_eq_zero_iff]
  rintro ⟨x, hx0, hx⟩
  apply hx0
  have h1 : (Aᵀ *ᵥ x) ⬝ᵥ (Aᵀ *ᵥ x) = 0 := by
    have h : (Aᵀ *ᵥ x) ⬝ᵥ (Aᵀ *ᵥ x) = x ⬝ᵥ ((A * Aᵀ) *ᵥ x) := by
      rw [transpose_mulVec_dotProduct, Matrix.mulVec_mulVec]
    rw [h, hx, dotProduct_zero]
  have h2 : Aᵀ *ᵥ x = 0 := dotProduct_self_eq_zero.mp h1
  have h3 : ∑ i, x i • A.row i = 0 := by
    ext j
    have := congrFun h2 j
    simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm, Matrix.row] using this
  exact funext fun i => Fintype.linearIndependent_iff.mp hA x h3 i

/-- **(3.8), feasibility** (arXiv 1807.02338): the minimum-norm solution solves the system. -/
theorem mulVec_minNormSol {A : Matrix ι n ℝ} (hA : LinearIndependent ℝ A.row) (b : ι → ℝ) :
    A *ᵥ minNormSol A b = b := by
  rw [minNormSol, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_det_mul_transpose hA), Matrix.one_mulVec]

/-- Pythagoras for the minimum-norm solution. -/
lemma dotProduct_self_eq_of_mulVec_eq {A : Matrix ι n ℝ} (hA : LinearIndependent ℝ A.row)
    {b : ι → ℝ} {y : n → ℝ} (hy : A *ᵥ y = b) :
    y ⬝ᵥ y = minNormSol A b ⬝ᵥ minNormSol A b +
      (y - minNormSol A b) ⬝ᵥ (y - minNormSol A b) := by
  set s := minNormSol A b with hs
  have hz : A *ᵥ (y - s) = 0 := by
    rw [Matrix.mulVec_sub, hy, mulVec_minNormSol hA, sub_self]
  have horth : s ⬝ᵥ (y - s) = 0 := by
    calc s ⬝ᵥ (y - s) = (Aᵀ *ᵥ ((A * Aᵀ)⁻¹ *ᵥ b)) ⬝ᵥ (y - s) := rfl
      _ = 0 := by rw [transpose_mulVec_dotProduct, hz, dotProduct_zero]
  have hy' : y = s + (y - s) := by abel
  calc y ⬝ᵥ y = (s + (y - s)) ⬝ᵥ (s + (y - s)) := by rw [← hy']
    _ = s ⬝ᵥ s + (s ⬝ᵥ (y - s) + (y - s) ⬝ᵥ s) + (y - s) ⬝ᵥ (y - s) := by
      simp only [add_dotProduct, dotProduct_add]; ring
    _ = s ⬝ᵥ s + (y - s) ⬝ᵥ (y - s) := by
      rw [dotProduct_comm (y - s) s, horth]; ring

/-- **(3.8), solvability and minimality** (arXiv 1807.02338).  If the rows of `A = [α; β]` are
independent, `A y = b` has the unique solution `Aᵀ (A Aᵀ)⁻¹ b` of smallest Euclidean norm. -/
theorem minNormSol_spec {A : Matrix ι n ℝ} (hA : LinearIndependent ℝ A.row) (b : ι → ℝ) :
    A *ᵥ minNormSol A b = b ∧
      ∀ y, A *ᵥ y = b → minNormSol A b ⬝ᵥ minNormSol A b ≤ y ⬝ᵥ y ∧
        (y ⬝ᵥ y = minNormSol A b ⬝ᵥ minNormSol A b → y = minNormSol A b) := by
  refine ⟨mulVec_minNormSol hA b, fun y hy => ?_⟩
  have h := dotProduct_self_eq_of_mulVec_eq hA hy
  refine ⟨?_, fun heq => ?_⟩
  · have : 0 ≤ (y - minNormSol A b) ⬝ᵥ (y - minNormSol A b) := by
      simpa [dotProduct, mul_self_nonneg] using
        Finset.sum_nonneg fun i _ => mul_self_nonneg ((y - minNormSol A b) i)
    linarith
  · have h0 : (y - minNormSol A b) ⬝ᵥ (y - minNormSol A b) = 0 := by linarith
    exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp h0)

omit [DecidableEq ι] in
/-- **(3.8), `r ≥ 1 + d`** (arXiv 1807.02338): rows are independent only if there are at least as
many unknowns as equations. -/
theorem card_le_of_rows {A : Matrix ι n ℝ} (hA : LinearIndependent ℝ A.row) :
    Fintype.card ι ≤ Fintype.card n := by
  simpa using hA.fintype_card_le_finrank

/-- **(3.8), "multiple solutions"** (arXiv 1807.02338): with strictly more unknowns than equations
the solution is not unique.  For `r = 1 + d` it is unique, so the paper's "(multiple)" needs
`r > 1 + d`. -/
theorem exists_ne_mulVec_eq {A : Matrix ι n ℝ} (hA : LinearIndependent ℝ A.row)
    (hlt : Fintype.card ι < Fintype.card n) (b : ι → ℝ) :
    ∃ y, y ≠ minNormSol A b ∧ A *ᵥ y = b := by
  classical
  have hker : LinearMap.ker A.mulVecLin ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hlt)
  obtain ⟨z, hz, hz0⟩ := (Submodule.ne_bot_iff _).mp hker
  refine ⟨minNormSol A b + z, fun h => hz0 (by simpa using h), ?_⟩
  rw [Matrix.mulVec_add, mulVec_minNormSol hA, show A *ᵥ z = 0 from hz, add_zero]

/-- **(3.8), uniqueness for `r = 1 + d`** (arXiv 1807.02338): with as many unknowns as equations
the minimum-norm solution is the only solution. -/
theorem eq_minNormSol_of_card_eq {A : Matrix ι n ℝ} (hA : LinearIndependent ℝ A.row)
    (hcard : Fintype.card ι = Fintype.card n) {b : ι → ℝ} {y : n → ℝ} (hy : A *ᵥ y = b) :
    y = minNormSol A b := by
  classical
  have hsurj : Function.Surjective A.mulVecLin := fun c =>
    ⟨minNormSol A c, mulVec_minNormSol hA c⟩
  have hfin : Module.finrank ℝ (n → ℝ) = Module.finrank ℝ (ι → ℝ) := by simp [hcard]
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).2 hsurj
  exact hinj (by simp [hy, mulVec_minNormSol hA])

/-- **(3.8), decoupling** (arXiv 1807.02338): the row-wise minimum-norm solutions minimise the
Euclidean norm of the whole coefficient array `λ`, since "the equations for different `i`
decouple". -/
theorem minNormSol_rows_le {A : Matrix ι n ℝ} (hA : LinearIndependent ℝ A.row) (R : κ → ι → ℝ)
    (Λ : κ → n → ℝ) (hΛ : ∀ k, A *ᵥ Λ k = R k) :
    ∑ k, ∑ j, minNormSol A (R k) j ^ 2 ≤ ∑ k, ∑ j, Λ k j ^ 2 := by
  refine Finset.sum_le_sum fun k _ => ?_
  have h := ((minNormSol_spec hA (R k)).2 (Λ k) (hΛ k)).1
  simpa [dotProduct, sq] using h

/-- **Remark 1, the `X⁰`-ansatz is robust** (arXiv 1807.02338): the size of the minimum-norm
solution is bounded by the right-hand side and the smallest singular value `s` of `[α; β]`, without
any dependence on the core `S`.  Uses `multiplier_le` of the library. -/
theorem minNormSol_norm_le {A : Matrix ι n ℝ} (hA : LinearIndependent ℝ A.row) {s : ℝ} (hs : 0 < s)
    (hsA : ∀ q : ι → ℝ, s ^ 2 * (q ⬝ᵥ q) ≤ (Aᵀ *ᵥ q) ⬝ᵥ (Aᵀ *ᵥ q)) (b : ι → ℝ) :
    Real.sqrt (minNormSol A b ⬝ᵥ minNormSol A b) ≤ Real.sqrt (b ⬝ᵥ b) / s := by
  set q : ι → ℝ := (A * Aᵀ)⁻¹ *ᵥ b with hq
  set y : n → ℝ := minNormSol A b with hy
  have hyq : Aᵀ *ᵥ q = y := rfl
  have h1 : Real.sqrt (q ⬝ᵥ q) ≤ Real.sqrt (y ⬝ᵥ y) / s :=
    OpenProblems.Stability.multiplier_le hs hsA hyq
  have hyy : y ⬝ᵥ y = q ⬝ᵥ b := by
    have hAy : A *ᵥ y = b := mulVec_minNormSol hA b
    calc y ⬝ᵥ y = (Aᵀ *ᵥ q) ⬝ᵥ y := by rw [hyq]
      _ = q ⬝ᵥ (A *ᵥ y) := transpose_mulVec_dotProduct A q y
      _ = q ⬝ᵥ b := by rw [hAy]
  have hcs : q ⬝ᵥ b ≤ Real.sqrt (q ⬝ᵥ q) * Real.sqrt (b ⬝ᵥ b) := by
    have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ q b
    simpa [dotProduct, sq] using this
  set t := Real.sqrt (y ⬝ᵥ y) with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have htt : t * t = y ⬝ᵥ y := Real.mul_self_sqrt (by
    simpa [dotProduct] using Finset.sum_nonneg fun i _ => mul_self_nonneg (y i))
  have hb0 : 0 ≤ Real.sqrt (b ⬝ᵥ b) := Real.sqrt_nonneg _
  rw [le_div_iff₀ hs]
  rcases ht0.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]; exact hb0
  · have h2 : t * t ≤ t / s * Real.sqrt (b ⬝ᵥ b) := by
      calc t * t = q ⬝ᵥ b := by rw [htt, hyy]
        _ ≤ _ := hcs
        _ ≤ t / s * Real.sqrt (b ⬝ᵥ b) := mul_le_mul_of_nonneg_right h1 hb0
    have h3 : t * (t * s) ≤ t * Real.sqrt (b ⬝ᵥ b) := by
      have : t / s * Real.sqrt (b ⬝ᵥ b) * s = t * Real.sqrt (b ⬝ᵥ b) := by field_simp
      nlinarith
    exact le_of_mul_le_mul_left h3 hpos

end MinNorm

/-! ### Phase space, moments and the Vlasov operator -/

section Setting

/-- Physical space and velocity space `ℝ^d`. -/
abbrev PS (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d r : ℕ}

/-- The partial derivative `∂_a g`. -/
noncomputable def pd (a : Fin d) (g : PS d → ℝ) (x : PS d) : ℝ :=
  fderiv ℝ g x (EuclideanSpace.single a 1)

/-- The density `ρ(x) = ∫ f(x, v) dv`. -/
noncomputable def rho (ν : Measure (PS d)) (f : PS d → PS d → ℝ) (x : PS d) : ℝ :=
  ∫ v, f x v ∂ν

/-- The component `(ρu)_a(x) = ∫ v_a f(x, v) dv` of the momentum density. -/
noncomputable def momentum (ν : Measure (PS d)) (f : PS d → PS d → ℝ) (a : Fin d) (x : PS d) : ℝ :=
  ∫ v, v a * f x v ∂ν

/-- The component `(ρu ⊗ u)_{ab}(x) = ∫ v_a v_b f(x, v) dv` of the momentum flux. -/
noncomputable def stress (ν : Measure (PS d)) (f : PS d → PS d → ℝ) (a b : Fin d) (x : PS d) : ℝ :=
  ∫ v, v a * v b * f x v ∂ν

/-- `∇·(ρu)`. -/
noncomputable def divMomentum (ν : Measure (PS d)) (f : PS d → PS d → ℝ) (x : PS d) : ℝ :=
  ∑ a, pd a (momentum ν f a) x

/-- The component `(∇·(ρu ⊗ u))_a = ∑_b ∂_b (ρu ⊗ u)_{ab}`. -/
noncomputable def divStress (ν : Measure (PS d)) (f : PS d → PS d → ℝ) (a : Fin d) (x : PS d) : ℝ :=
  ∑ b, pd b (stress ν f a b) x

/-- The Vlasov right-hand side `F(f) = -v·∇ₓf + E·∇ᵥf` of (1.1) for a given field `E`.  In the
Vlasov-Poisson equation `E = E(f)`; none of the results below uses the Poisson equation. -/
noncomputable def vlasovF (E : PS d → PS d) (f : PS d → PS d → ℝ) (x v : PS d) : ℝ :=
  -fderiv ℝ (fun y => f y v) x v + fderiv ℝ (fun w => f x w) v (E x)

/-- The weights `1, v₁, …, v_d` of the conserved moments; `none` is mass, `some a` is momentum. -/
def wt : Option (Fin d) → PS d → ℝ
  | none, _ => 1
  | some a, v => v a

/-- The moment `∫ w_m(v) f(x, v) dv`: the density for `m = none`, `(ρu)_a` for `m = some a`. -/
noncomputable def moment (ν : Measure (PS d)) (m : Option (Fin d)) (f : PS d → PS d → ℝ)
    (x : PS d) : ℝ :=
  ∫ v, wt m v * f x v ∂ν

/-- The flux term of the conservation laws (3.1), (3.2): `∇·(ρu)` for mass and
`(∇·(ρu ⊗ u))_a + E_a ρ` for momentum. -/
noncomputable def flux (ν : Measure (PS d)) (E : PS d → PS d) (f : PS d → PS d → ℝ) :
    Option (Fin d) → PS d → ℝ
  | none, x => divMomentum ν f x
  | some a, x => divStress ν f a x + E x a * rho ν f x

/-- The `(1 + d) × r` matrix `[α; β]` of (3.8), with `α_j = ∫ V_j dv`, `β_j = ∫ v V_j dv`. -/
noncomputable def momentMatrix (ν : Measure (PS d)) (V : Fin r → PS d → ℝ) :
    Matrix (Option (Fin d)) (Fin r) ℝ :=
  Matrix.of fun m j => ∫ v, wt m v * V j v ∂ν

/-- A separated function `∑_j A_j(x) B_j(v)`: this is `f = ∑ K_j V_j` and `f = ∑ X_k L_k`. -/
def lowRank (A B : Fin r → PS d → ℝ) (x v : PS d) : ℝ := ∑ j, A j x * B j v

/-- `K_l = ∑_k X_k S_{kl}`. -/
def coreK (X : Fin r → PS d → ℝ) (S : Matrix (Fin r) (Fin r) ℝ) (l : Fin r) (x : PS d) : ℝ :=
  ∑ k, X k x * S k l

/-- The projector `P_X̄ g = ∑_i ⟨X_i, g⟩ₓ X_i`. -/
noncomputable def proj {α : Type*} [MeasurableSpace α] (μ : Measure α) (X : Fin r → α → ℝ)
    (g : α → ℝ) (x : α) : ℝ :=
  ∑ i, (∫ y, X i y * g y ∂μ) * X i x

/-- Orthonormality in `L²(μ)`. -/
structure IsOrthonormalL2 {α : Type*} [MeasurableSpace α] (μ : Measure α) (X : Fin r → α → ℝ) :
    Prop where
  memLp : ∀ i, MemLp (X i) 2 μ
  inner_eq : ∀ i k, ∫ x, X i x * X k x ∂μ = if i = k then 1 else 0

section Orthonormal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {X : Fin r → α → ℝ}

lemma IsOrthonormalL2.integrable_mul (hX : IsOrthonormalL2 μ X) (i k : Fin r) :
    Integrable (fun x => X i x * X k x) μ :=
  (hX.memLp i).integrable_mul (hX.memLp k)

/-- The basic expansion: `⟨X_i, ∑_k D_k X_k + Φ⟩ = D_i + ⟨X_i, Φ⟩`. -/
lemma IsOrthonormalL2.integral_mul_sum_add (hX : IsOrthonormalL2 μ X) (i : Fin r) (D : Fin r → ℝ)
    {Φ : α → ℝ} (hΦ : Integrable (fun x => X i x * Φ x) μ) :
    ∫ x, X i x * (∑ k, X k x * D k + Φ x) ∂μ = D i + ∫ x, X i x * Φ x ∂μ := by
  have h : (fun x => X i x * (∑ k, X k x * D k + Φ x)) =
      fun x => ∑ k, (X i x * X k x) * D k + X i x * Φ x := by
    funext x
    rw [mul_add, mul_sum]
    simp only [mul_assoc]
  rw [h, integral_add (integrable_finsetSum _ fun k _ => (hX.integrable_mul i k).mul_const _) hΦ,
    integral_finsetSum _ fun k _ => (hX.integrable_mul i k).mul_const _]
  simp_rw [integral_mul_const, hX.inner_eq]
  simp

/-- **(3.3), projected form** (arXiv 1807.02338): `P_X̄ g = 0` means `⟨X_i, g⟩ = 0` for all `i`.
This turns the projected laws into the bracketed equations of (3.6), (3.7). -/
theorem proj_eq_zero_iff (hX : IsOrthonormalL2 μ X) (g : α → ℝ) :
    proj μ X g = 0 ↔ ∀ i, ∫ x, X i x * g x ∂μ = 0 := by
  constructor
  · intro h i
    set c : Fin r → ℝ := fun k => ∫ y, X k y * g y ∂μ with hc
    have h1 := hX.integral_mul_sum_add i c (Φ := fun _ => 0) (by simp)
    have h2 : ∀ x, ∑ k, X k x * c k = 0 := fun x => by
      have := congrFun h x
      simpa [proj, mul_comm] using this
    simpa [h2] using h1.symm
  · intro h
    funext x
    simp [proj, h]

end Orthonormal

variable {ν : Measure (PS d)}

@[simp] lemma wt_none (v : PS d) : wt none v = 1 := rfl
@[simp] lemma wt_some (a : Fin d) (v : PS d) : wt (some a) v = v a := rfl

lemma moment_none (f : PS d → PS d → ℝ) : moment ν none f = rho ν f := by
  funext x
  simp [moment, rho]

lemma moment_some (a : Fin d) (f : PS d → PS d → ℝ) : moment ν (some a) f = momentum ν f a := rfl

/-- Velocity integrals of a separated function. -/
lemma integral_weight_lowRank (w : PS d → ℝ) {A B : Fin r → PS d → ℝ}
    (hB : ∀ j, Integrable (fun v => w v * B j v) ν) (x : PS d) :
    ∫ v, w v * lowRank A B x v ∂ν = ∑ j, A j x * ∫ v, w v * B j v ∂ν := by
  have h : ∀ v, w v * lowRank A B x v = ∑ j, A j x * (w v * B j v) := fun v => by
    rw [lowRank, mul_sum]
    exact sum_congr rfl fun j _ => by ring
  simp_rw [h]
  rw [integral_finsetSum _ fun j _ => (hB j).const_mul _]
  simp_rw [integral_const_mul]

lemma moment_lowRank {m : Option (Fin d)} {A B : Fin r → PS d → ℝ}
    (hB : ∀ j, Integrable (fun v => wt m v * B j v) ν) (x : PS d) :
    moment ν m (lowRank A B) x = ∑ j, A j x * ∫ v, wt m v * B j v ∂ν :=
  integral_weight_lowRank _ hB x

lemma rho_lowRank {A B : Fin r → PS d → ℝ} (hB : ∀ j, Integrable (B j) ν) (x : PS d) :
    rho ν (lowRank A B) x = ∑ j, A j x * ∫ v, B j v ∂ν := by
  have := integral_weight_lowRank (ν := ν) (A := A) (B := B) (fun _ => 1) (by simpa using hB) x
  simpa [rho] using this

/-- `∂_a` of a finite combination. -/
lemma pd_sum_mul {A : Fin r → PS d → ℝ} (a : Fin d) (c : Fin r → ℝ) {x : PS d}
    (hA : ∀ j, DifferentiableAt ℝ (A j) x) :
    pd a (fun y => ∑ j, A j y * c j) x = ∑ j, pd a (A j) x * c j := by
  have h : HasFDerivAt (fun y => ∑ j, A j y * c j)
      (∑ j, c j • fderiv ℝ (A j) x) x :=
    HasFDerivAt.fun_sum fun j _ => by
      simpa using (hA j).hasFDerivAt.mul_const (c j)
  simp [pd, h.fderiv, mul_comm]

/-- The paper's `∇·(ρu) = ∑_j ∇K_j · β_j`. -/
lemma divMomentum_lowRank {A B : Fin r → PS d → ℝ}
    (hB : ∀ a j, Integrable (fun v => v a * B j v) ν) {x : PS d}
    (hA : ∀ j, DifferentiableAt ℝ (A j) x) :
    divMomentum ν (lowRank A B) x = ∑ a, ∑ j, pd a (A j) x * ∫ v, v a * B j v ∂ν := by
  refine sum_congr rfl fun a _ => ?_
  have h : momentum ν (lowRank A B) a = fun y => ∑ j, A j y * ∫ v, v a * B j v ∂ν := by
    funext y
    exact integral_weight_lowRank (fun v => v a) (hB a) y
  rw [h, pd_sum_mul a _ hA]

/-- The paper's `∇·(ρu ⊗ u) = ∑_j ∇K_j · γ_j`. -/
lemma divStress_lowRank {A B : Fin r → PS d → ℝ}
    (hB : ∀ a b j, Integrable (fun v => v a * v b * B j v) ν) (a : Fin d) {x : PS d}
    (hA : ∀ j, DifferentiableAt ℝ (A j) x) :
    divStress ν (lowRank A B) a x = ∑ b, ∑ j, pd b (A j) x * ∫ v, v a * v b * B j v ∂ν := by
  refine sum_congr rfl fun b _ => ?_
  have h : stress ν (lowRank A B) a b = fun y => ∑ j, A j y * ∫ v, v a * v b * B j v ∂ν := by
    funext y
    exact integral_weight_lowRank (fun v => v a * v b) (hB a b) y
  rw [h, pd_sum_mul b _ hA]

/-- `w·∇g = ∑_a w_a ∂_a g`. -/
lemma fderiv_apply_eq_sum_pd (g : PS d → ℝ) (x w : PS d) :
    fderiv ℝ g x w = ∑ a, w a * pd a g x := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr w]
  simp [pd, map_sum]

/-- The Vlasov operator on a separated function. -/
lemma vlasovF_lowRank (E : PS d → PS d) {A B : Fin r → PS d → ℝ} (x v : PS d)
    (hA : ∀ j, DifferentiableAt ℝ (A j) x) (hB : ∀ j, DifferentiableAt ℝ (B j) v) :
    vlasovF E (lowRank A B) x v =
      ∑ j, (-(∑ a, v a * pd a (A j) x) * B j v + A j x * ∑ b, E x b * pd b (B j) v) := by
  have h1 : HasFDerivAt (fun y => lowRank A B y v) (∑ j, B j v • fderiv ℝ (A j) x) x :=
    HasFDerivAt.fun_sum fun j _ => by
      simpa using (hA j).hasFDerivAt.mul_const (B j v)
  have h2 : HasFDerivAt (fun w => lowRank A B x w) (∑ j, A j x • fderiv ℝ (B j) v) v :=
    HasFDerivAt.fun_sum fun j _ => by
      simpa using (hB j).hasFDerivAt.const_mul (A j x)
  simp only [vlasovF, h1.fderiv, h2.fderiv]
  simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul, fderiv_apply_eq_sum_pd]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  exact sum_congr rfl fun j _ => by ring

end Setting

/-! ### The projected conservation laws and the three corrected substeps -/

section Laws

variable {d r : ℕ} {μ ν : Measure (PS d)} {X V : Fin r → PS d → ℝ} {E : ℝ → PS d → PS d} {t : ℝ}

/-- The projected local conservation laws (3.3) at time `t`:
`P_X̄ (∂ₜρ + ∇·(ρu)) = 0` and `P_X̄ (∂ₜ(ρu) + ∇·(ρu ⊗ u) + Eρ) = 0`. -/
def ProjectedLaws (μ ν : Measure (PS d)) (X : Fin r → PS d → ℝ) (E : ℝ → PS d → PS d)
    (f : ℝ → PS d → PS d → ℝ) (t : ℝ) : Prop :=
  proj μ X (fun x => deriv (fun s => rho ν (f s) x) t + divMomentum ν (f t) x) = 0 ∧
    ∀ a, proj μ X (fun x => deriv (fun s => momentum ν (f s) a x) t + divStress ν (f t) a x +
      E t x a * rho ν (f t) x) = 0

/-- The projected laws (3.10), (3.11) of the S-step, which runs backward in time:
`P_X̄ (∂ₜρ - ∇·(ρu)) = 0` and `P_X̄ (∂ₜ(ρu) - ∇·(ρu ⊗ u) - Eρ) = 0`. -/
def ProjectedLawsBackward (μ ν : Measure (PS d)) (X : Fin r → PS d → ℝ) (E : ℝ → PS d → PS d)
    (f : ℝ → PS d → PS d → ℝ) (t : ℝ) : Prop :=
  proj μ X (fun x => deriv (fun s => rho ν (f s) x) t - divMomentum ν (f t) x) = 0 ∧
    ∀ a, proj μ X (fun x => deriv (fun s => momentum ν (f s) a x) t - divStress ν (f t) a x -
      E t x a * rho ν (f t) x) = 0

lemma projectedLaws_iff {f : ℝ → PS d → PS d → ℝ} :
    ProjectedLaws μ ν X E f t ↔ ∀ m, proj μ X (fun x =>
      deriv (fun s => moment ν m (f s) x) t + flux ν (E t) (f t) m x) = 0 := by
  rw [Option.forall]
  simp only [flux, moment_none, moment_some, ProjectedLaws, add_assoc]

lemma projectedLawsBackward_iff {f : ℝ → PS d → PS d → ℝ} :
    ProjectedLawsBackward μ ν X E f t ↔ ∀ m, proj μ X (fun x =>
      deriv (fun s => moment ν m (f s) x) t - flux ν (E t) (f t) m x) = 0 := by
  rw [Option.forall]
  simp only [flux, moment_none, moment_some, ProjectedLawsBackward, sub_sub]

/-- `⟨X V, G⟩ₓᵥ`, as the iterated integral `∫ X(x) ∫ V(v) G(x, v) dv dx`. -/
noncomputable def innerXV (μ ν : Measure (PS d)) (X V : PS d → ℝ) (G : PS d → PS d → ℝ) : ℝ :=
  ∫ x, X x * ∫ v, V v * G x v ∂ν ∂μ

/-- The right-hand side `b_i` (`m = none`) and `(d_i)_a` (`m = some a`) of (3.8) in Steps 1 and 2:
`b_i = -∑_j ⟨X_i V_j, F(f)⟩ₓᵥ α_j - ⟨X_i, ∇·(ρu)⟩ₓ` and
`d_i = -∑_j ⟨X_i V_j, F(f)⟩ₓᵥ β_j - ⟨X_i, ∇·(ρu ⊗ u) + E ρ⟩ₓ`. -/
noncomputable def rhsKS (μ ν : Measure (PS d)) (X V : Fin r → PS d → ℝ) (E : PS d → PS d)
    (f : PS d → PS d → ℝ) (m : Option (Fin d)) (i : Fin r) : ℝ :=
  -∑ j, innerXV μ ν (X i) (V j) (vlasovF E f) * momentMatrix ν V m j -
    ∫ x, X i x * flux ν E f m x ∂μ

/-- The right-hand side of (3.8) in Step 3, with the sign of `Eρ` of the law (3.3):
`-⟨X_i, w_m F(f)⟩ₓᵥ - ⟨X_i, flux⟩ₓ`.  It vanishes, see `rhsL_lowRank_eq_zero`. -/
noncomputable def rhsL (μ ν : Measure (PS d)) (X : Fin r → PS d → ℝ) (E : PS d → PS d)
    (f : PS d → PS d → ℝ) (m : Option (Fin d)) (i : Fin r) : ℝ :=
  -(∫ v, wt m v * ∫ x, X i x * vlasovF E f x v ∂μ ∂ν) - ∫ x, X i x * flux ν E f m x ∂μ

/-- Sorting the corrected K-step right-hand side by the basis functions. -/
private lemma sum_corrected (G : Fin r → ℝ) (lam : Matrix (Fin r) (Fin r) ℝ) (Y c : Fin r → ℝ) :
    ∑ j, (G j + ∑ k, lam k j * Y k) * c j =
      ∑ k, Y k * (∑ j, lam k j * c j) + ∑ j, G j * c j := by
  simp only [add_mul, sum_add_distrib, sum_mul, mul_sum]
  rw [add_comm, sum_comm]
  congr 1
  exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring

/-- **Step 1, (3.6), (3.7)** (arXiv 1807.02338).  Let `K` solve the corrected K-step (3.5)
`∂ₜK_j = ⟨V_j, F(f)⟩ᵥ + ∑_k λ_kj X_k` for `f = ∑_l K_l V_l`.  Then the `X_i`-component of the
residual of the conservation law `m` is `∑_j λ_ij α_j - b_i` (`m = none`), respectively
`∑_j λ_ij β_j - d_i` (`m = some a`).  The vector field `E` is arbitrary, so that `E = E(f)` is
covered.  The integrability hypotheses say that the inner products in (3.6), (3.7) exist. -/
theorem kStep_residual (hX : IsOrthonormalL2 μ X)
    (hV : ∀ m j, Integrable (fun v => wt m v * V j v) ν)
    {K : ℝ → Fin r → PS d → ℝ} {lam : Matrix (Fin r) (Fin r) ℝ}
    (hK : ∀ j x, HasDerivAt (fun s => K s j x)
      ((∫ v, V j v * vlasovF (E t) (lowRank (K t) V) x v ∂ν) + ∑ k, lam k j * X k x) t)
    (hF : ∀ i j, Integrable
      (fun x => X i x * ∫ v, V j v * vlasovF (E t) (lowRank (K t) V) x v ∂ν) μ)
    (hΦ : ∀ i m, Integrable (fun x => X i x * flux ν (E t) (lowRank (K t) V) m x) μ)
    (m : Option (Fin d)) (i : Fin r) :
    ∫ x, X i x * (deriv (fun s => moment ν m (lowRank (K s) V) x) t +
        flux ν (E t) (lowRank (K t) V) m x) ∂μ =
      (momentMatrix ν V *ᵥ lam i) m - rhsKS μ ν X V (E t) (lowRank (K t) V) m i := by
  set A := momentMatrix ν V with hA
  set G : Fin r → PS d → ℝ := fun j x => ∫ v, V j v * vlasovF (E t) (lowRank (K t) V) x v ∂ν
    with hG
  set Φ : PS d → ℝ := flux ν (E t) (lowRank (K t) V) m with hΦdef
  have hderiv : ∀ x, deriv (fun s => moment ν m (lowRank (K s) V) x) t =
      ∑ j, (G j x + ∑ k, lam k j * X k x) * A m j := fun x => by
    have h : (fun s => moment ν m (lowRank (K s) V) x) = fun s => ∑ j, K s j x * A m j := by
      funext s
      exact moment_lowRank (hV m) x
    rw [h]
    exact (HasDerivAt.fun_sum fun j _ => (hK j x).mul_const (A m j)).deriv
  have hint : ∫ x, X i x * (deriv (fun s => moment ν m (lowRank (K s) V) x) t + Φ x) ∂μ =
      ∫ x, X i x * (∑ k, X k x * (∑ j, lam k j * A m j) + (∑ j, G j x * A m j + Φ x)) ∂μ := by
    congr 1
    funext x
    rw [hderiv x, sum_corrected (fun j => G j x) lam (fun k => X k x) (A m), add_assoc]
  have h1 : Integrable (fun x => X i x * (∑ j, G j x * A m j + Φ x)) μ := by
    have h2 : (fun x => X i x * (∑ j, G j x * A m j + Φ x)) =
        fun x => ∑ j, X i x * G j x * A m j + X i x * Φ x := by
      funext x
      rw [mul_add, mul_sum]
      simp only [mul_assoc]
    rw [h2]
    exact (integrable_finsetSum _ fun j _ => (hF i j).mul_const _).add (hΦ i m)
  rw [hint, hX.integral_mul_sum_add i _ h1]
  have h3 : ∫ x, X i x * (∑ j, G j x * A m j + Φ x) ∂μ =
      ∑ j, innerXV μ ν (X i) (V j) (vlasovF (E t) (lowRank (K t) V)) * A m j +
        ∫ x, X i x * Φ x ∂μ := by
    have h2 : (fun x => X i x * (∑ j, G j x * A m j + Φ x)) =
        fun x => ∑ j, X i x * G j x * A m j + X i x * Φ x := by
      funext x
      rw [mul_add, mul_sum]
      simp only [mul_assoc]
    rw [h2, integral_add (integrable_finsetSum _ fun j _ => (hF i j).mul_const _) (hΦ i m),
      integral_finsetSum _ fun j _ => (hF i j).mul_const _]
    simp_rw [integral_mul_const]
    rfl
  rw [h3, rhsKS]
  simp only [Matrix.mulVec, dotProduct]
  have h4 : ∑ j, lam i j * A m j = ∑ j, A m j * lam i j := sum_congr rfl fun j _ => mul_comm _ _
  rw [h4]
  ring

/-- **Step 2, (3.10), (3.11)** (arXiv 1807.02338).  Let `S` solve the corrected S-step (3.9)
`∂ₜS_ij = -⟨X_i V_j, F(f)⟩ₓᵥ - λ_ij` for `f = ∑_kl X_k S_kl V_l`.  Then the `X_i`-component of the
residual of the backward law `m` is `b_i - ∑_j λ_ij α_j`, respectively `d_i - ∑_j λ_ij β_j`. -/
theorem sStep_residual (hX : IsOrthonormalL2 μ X)
    (hV : ∀ m j, Integrable (fun v => wt m v * V j v) ν)
    {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {lam : Matrix (Fin r) (Fin r) ℝ}
    (hS : ∀ i j, HasDerivAt (fun s => S s i j)
      (-innerXV μ ν (X i) (V j) (vlasovF (E t) (lowRank (coreK X (S t)) V)) - lam i j) t)
    (hΦ : ∀ i m, Integrable (fun x => X i x * flux ν (E t) (lowRank (coreK X (S t)) V) m x) μ)
    (m : Option (Fin d)) (i : Fin r) :
    ∫ x, X i x * (deriv (fun s => moment ν m (lowRank (coreK X (S s)) V) x) t -
        flux ν (E t) (lowRank (coreK X (S t)) V) m x) ∂μ =
      rhsKS μ ν X V (E t) (lowRank (coreK X (S t)) V) m i - (momentMatrix ν V *ᵥ lam i) m := by
  set A := momentMatrix ν V with hA
  set f₀ := lowRank (coreK X (S t)) V with hf₀
  set Φ : PS d → ℝ := flux ν (E t) f₀ m with hΦdef
  set D : Fin r → ℝ := fun k => ∑ l, (-innerXV μ ν (X k) (V l) (vlasovF (E t) f₀) - lam k l) * A m l
    with hD
  have hderiv : ∀ x, deriv (fun s => moment ν m (lowRank (coreK X (S s)) V) x) t =
      ∑ k, X k x * D k := fun x => by
    have h : (fun s => moment ν m (lowRank (coreK X (S s)) V) x) =
        fun s => ∑ k, X k x * ∑ l, S s k l * A m l := by
      funext s
      rw [moment_lowRank (hV m) x]
      simp only [coreK, sum_mul]
      rw [sum_comm]
      refine sum_congr rfl fun k _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun l _ => ?_
      simp only [hA, momentMatrix, Matrix.of_apply]
      ring
    rw [h]
    exact (HasDerivAt.fun_sum fun k _ => (HasDerivAt.fun_sum fun l _ =>
      (hS k l).mul_const (A m l)).const_mul (X k x)).deriv
  have h1 : ∫ x, X i x * (deriv (fun s => moment ν m (lowRank (coreK X (S s)) V) x) t - Φ x) ∂μ =
      ∫ x, X i x * (∑ k, X k x * D k + -Φ x) ∂μ := by
    congr 1
    funext x
    rw [hderiv x, sub_eq_add_neg]
  have hΦ' : Integrable (fun x => X i x * -Φ x) μ := by
    simpa using (hΦ i m).neg
  rw [h1, hX.integral_mul_sum_add i D hΦ', rhsKS]
  have h2 : ∫ x, X i x * -Φ x ∂μ = -∫ x, X i x * Φ x ∂μ := by
    simp only [mul_neg, integral_neg]
  rw [h2]
  simp only [hD, Matrix.mulVec, dotProduct, sub_mul, neg_mul, sum_sub_distrib, sum_neg_distrib]
  have h4 : ∑ j, lam i j * A m j = ∑ j, A m j * lam i j := sum_congr rfl fun j _ => mul_comm _ _
  rw [h4]
  ring

lemma abs_coord_le (a : Fin d) (v : PS d) : |v a| ≤ ‖v‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v a

lemma abs_wt_le (m : Option (Fin d)) (v : PS d) : |wt m v| ≤ 1 + ‖v‖ := by
  cases m with
  | none => simp
  | some a => simpa using (abs_coord_le a v).trans (by linarith [norm_nonneg v])

lemma continuous_coord (a : Fin d) : Continuous fun v : PS d => v a := by fun_prop

lemma continuous_wt (m : Option (Fin d)) : Continuous (wt m : PS d → ℝ) := by
  cases m with
  | none => exact continuous_const
  | some a => exact continuous_coord a

/-- A function with an integrable first moment has all the moments `w_m`. -/
lemma integrable_wt_of_weighted {h : PS d → ℝ} (hh : Integrable (fun v => (1 + ‖v‖) * h v) ν)
    (m : Option (Fin d)) : Integrable (fun v => wt m v * h v) ν := by
  have hne : ∀ v : PS d, 1 + ‖v‖ ≠ 0 := fun v => by positivity
  have hm : AEStronglyMeasurable h ν := by
    have e : h = fun v => (1 + ‖v‖)⁻¹ * ((1 + ‖v‖) * h v) := by
      funext v
      field_simp [hne v]
    rw [e]
    exact (Continuous.inv₀ (by fun_prop) hne).aestronglyMeasurable.mul hh.aestronglyMeasurable
  refine hh.mono ((continuous_wt m).aestronglyMeasurable.mul hm) (ae_of_all _ fun v => ?_)
  rw [norm_mul, norm_mul, Real.norm_eq_abs (wt m v), Real.norm_eq_abs (1 + ‖v‖),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖v‖)]
  exact mul_le_mul_of_nonneg_right (abs_wt_le m v) (norm_nonneg _)

/-- Regularity in time used to differentiate velocity moments under the integral sign: near `t`,
the curve `g` has integrable first moments, it has the time derivative `g'`, and `(1 + |v|) g'` has
an integrable majorant. -/
structure IsDominatedCurve (ν : Measure (PS d)) (g g' : ℝ → PS d → ℝ) (t : ℝ) : Prop where
  integrable : ∀ᶠ s in 𝓝 t, Integrable (fun v => (1 + ‖v‖) * g s v) ν
  aesm' : AEStronglyMeasurable (g' t) ν
  dominated : ∃ ε > 0, ∃ b : PS d → ℝ, Integrable b ν ∧ ∀ᵐ v ∂ν, ∀ s ∈ Metric.ball t ε,
    HasDerivAt (fun τ => g τ v) (g' s v) s ∧ (1 + ‖v‖) * |g' s v| ≤ b v

/-- Differentiation of velocity moments under the integral sign. -/
lemma IsDominatedCurve.hasDerivAt_moment {g g' : ℝ → PS d → ℝ} (h : IsDominatedCurve ν g g' t)
    (m : Option (Fin d)) :
    Integrable (fun v => wt m v * g' t v) ν ∧
      HasDerivAt (fun s => ∫ v, wt m v * g s v ∂ν) (∫ v, wt m v * g' t v ∂ν) t := by
  obtain ⟨ε, hε, b, hb, hbd⟩ := h.dominated
  have hbound : ∀ v, ∀ s, (1 + ‖v‖) * |g' s v| ≤ b v → ‖wt m v * g' s v‖ ≤ b v := fun v s hv => by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (abs_wt_le m v) (abs_nonneg _)).trans hv
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := b)
    (F := fun s v => wt m v * g s v) (F' := fun s v => wt m v * g' s v)
    (Metric.ball_mem_nhds t hε) ?_ ?_ ?_ ?_ hb ?_
  · filter_upwards [h.integrable] with s hs
    exact (integrable_wt_of_weighted hs m).aestronglyMeasurable
  · exact integrable_wt_of_weighted h.integrable.self_of_nhds m
  · exact (continuous_wt m).aestronglyMeasurable.mul h.aesm'
  · filter_upwards [hbd] with v hv s hs
    exact hbound v s (hv s hs).2
  · filter_upwards [hbd] with v hv s hs
    exact (hv s hs).1.const_mul _

/-- **Step 3, (3.13), (3.14) with the sign of `Eρ` corrected** (arXiv 1807.02338).  Let `L` solve
the corrected L-step (3.12) `∂ₜL_i = ⟨X_i, F(f)⟩ₓ + ∑_l λ_il V_l` for `f = ∑_k X_k L_k`; the
hypothesis `hL` contains this equation for times near `t`, and the regularity to differentiate
moments in time.  Then the `X_i`-component of the residual of the law `m` is
`(∑_l λ_il α_l or β_l) - rhsL`.  As printed, (3.14) has `-⟨X_i, Eρ⟩`; the correct term is
`+⟨X_i, Eρ⟩`, see `printedD_eq`. -/
theorem lStep_residual (hX : IsOrthonormalL2 μ X)
    (hV : ∀ m j, Integrable (fun v => wt m v * V j v) ν)
    {L : ℝ → Fin r → PS d → ℝ} {lam : ℝ → Matrix (Fin r) (Fin r) ℝ}
    (hL : ∀ k, IsDominatedCurve ν (fun s => L s k)
      (fun s v => (∫ x, X k x * vlasovF (E s) (lowRank X (L s)) x v ∂μ) + ∑ l, lam s k l * V l v) t)
    (hΦ : ∀ i m, Integrable (fun x => X i x * flux ν (E t) (lowRank X (L t)) m x) μ)
    (m : Option (Fin d)) (i : Fin r) :
    ∫ x, X i x * (deriv (fun s => moment ν m (lowRank X (L s)) x) t +
        flux ν (E t) (lowRank X (L t)) m x) ∂μ =
      (momentMatrix ν V *ᵥ lam t i) m - rhsL (ν := ν) μ X (E t) (lowRank X (L t)) m i := by
  set A := momentMatrix ν V with hA
  set I : Fin r → PS d → ℝ := fun k v => ∫ x, X k x * vlasovF (E t) (lowRank X (L t)) x v ∂μ with hI
  set Φ : PS d → ℝ := flux ν (E t) (lowRank X (L t)) m with hΦdef
  set D : Fin r → ℝ := fun k => (∫ v, wt m v * I k v ∂ν) + ∑ l, lam t k l * A m l with hD
  have hsplit : ∀ k, ∫ v, wt m v * (I k v + ∑ l, lam t k l * V l v) ∂ν = D k := fun k => by
    have hVsum : Integrable (fun v => ∑ l, lam t k l * (wt m v * V l v)) ν :=
      integrable_finsetSum _ fun l _ => (hV m l).const_mul _
    have htot := ((hL k).hasDerivAt_moment m).1
    have e : ∀ v, wt m v * (I k v + ∑ l, lam t k l * V l v) =
        wt m v * I k v + ∑ l, lam t k l * (wt m v * V l v) := fun v => by
      rw [mul_add, mul_sum]
      congr 1
      exact sum_congr rfl fun l _ => by ring
    have hIint : Integrable (fun v => wt m v * I k v) ν := by
      have e' : (fun v => wt m v * I k v) = fun v =>
          wt m v * (I k v + ∑ l, lam t k l * V l v) - ∑ l, lam t k l * (wt m v * V l v) := by
        funext v
        rw [e]
        ring
      rw [e']
      exact htot.sub hVsum
    simp_rw [e]
    rw [integral_add hIint hVsum, integral_finsetSum _ fun l _ => (hV m l).const_mul _]
    simp_rw [integral_const_mul]
    rfl
  have hderiv : ∀ x, HasDerivAt (fun s => moment ν m (lowRank X (L s)) x) (∑ k, X k x * D k) t :=
    fun x => by
      have h1 : HasDerivAt (fun s => ∑ k, X k x * ∫ v, wt m v * L s k v ∂ν)
          (∑ k, X k x * D k) t := by
        refine HasDerivAt.fun_sum fun k _ => ?_
        rw [← hsplit k]
        exact ((hL k).hasDerivAt_moment m).2.const_mul _
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [eventually_all.2 fun k => (hL k).integrable] with s hs
      exact moment_lowRank (fun k => integrable_wt_of_weighted (hs k) m) x
  have h1 : ∫ x, X i x * (deriv (fun s => moment ν m (lowRank X (L s)) x) t + Φ x) ∂μ =
      ∫ x, X i x * (∑ k, X k x * D k + Φ x) ∂μ := by
    congr 1
    funext x
    rw [(hderiv x).deriv]
  rw [h1, hX.integral_mul_sum_add i D (hΦ i m), rhsL]
  simp only [hD, Matrix.mulVec, dotProduct]
  have h4 : ∑ l, lam t i l * A m l = ∑ l, A m l * lam t i l := sum_congr rfl fun j _ => mul_comm _ _
  rw [h4]
  ring

/-! ### Main theorems for the three substeps -/

/-- **Step 1, (3.3) ⟺ (3.8)** (arXiv 1807.02338).  For the corrected K-step (3.5) the projected laws
(3.3) hold at time `t` exactly when `λ` solves the decoupled systems `[α; β] λ_i = [b_i; d_i]`. -/
theorem kStep_laws_iff (hX : IsOrthonormalL2 μ X)
    (hV : ∀ m j, Integrable (fun v => wt m v * V j v) ν)
    {K : ℝ → Fin r → PS d → ℝ} {lam : Matrix (Fin r) (Fin r) ℝ}
    (hK : ∀ j x, HasDerivAt (fun s => K s j x)
      ((∫ v, V j v * vlasovF (E t) (lowRank (K t) V) x v ∂ν) + ∑ k, lam k j * X k x) t)
    (hF : ∀ i j, Integrable
      (fun x => X i x * ∫ v, V j v * vlasovF (E t) (lowRank (K t) V) x v ∂ν) μ)
    (hΦ : ∀ i m, Integrable (fun x => X i x * flux ν (E t) (lowRank (K t) V) m x) μ) :
    ProjectedLaws μ ν X E (fun s => lowRank (K s) V) t ↔
      ∀ i, momentMatrix ν V *ᵥ lam i = fun m => rhsKS μ ν X V (E t) (lowRank (K t) V) m i := by
  rw [projectedLaws_iff]
  simp only [proj_eq_zero_iff hX, kStep_residual hX hV hK hF hΦ, sub_eq_zero]
  exact ⟨fun h i => funext fun m => h m i, fun h m i => congrFun (h i) m⟩

/-- **Step 1, main theorem** (arXiv 1807.02338, Sec. 3).  If the rows of `[α; β]` are independent
and `λ` is the minimum-norm solution of (3.8), the corrected K-step satisfies the projected
continuity equation and momentum balance (3.3).  Minimality of `λ` is `minNormSol_spec`. -/
theorem kStep_quasiConservative (hX : IsOrthonormalL2 μ X)
    (hV : ∀ m j, Integrable (fun v => wt m v * V j v) ν)
    (hrows : LinearIndependent ℝ (momentMatrix ν V).row)
    {K : ℝ → Fin r → PS d → ℝ} {lam : Matrix (Fin r) (Fin r) ℝ}
    (hlam : ∀ i, lam i = minNormSol (momentMatrix ν V)
      fun m => rhsKS μ ν X V (E t) (lowRank (K t) V) m i)
    (hK : ∀ j x, HasDerivAt (fun s => K s j x)
      ((∫ v, V j v * vlasovF (E t) (lowRank (K t) V) x v ∂ν) + ∑ k, lam k j * X k x) t)
    (hF : ∀ i j, Integrable
      (fun x => X i x * ∫ v, V j v * vlasovF (E t) (lowRank (K t) V) x v ∂ν) μ)
    (hΦ : ∀ i m, Integrable (fun x => X i x * flux ν (E t) (lowRank (K t) V) m x) μ) :
    ProjectedLaws μ ν X E (fun s => lowRank (K s) V) t :=
  (kStep_laws_iff hX hV hK hF hΦ).2 fun i => by rw [hlam i]; exact mulVec_minNormSol hrows _

/-- **Step 2, (3.10), (3.11) ⟺ (3.8)** (arXiv 1807.02338). -/
theorem sStep_laws_iff (hX : IsOrthonormalL2 μ X)
    (hV : ∀ m j, Integrable (fun v => wt m v * V j v) ν)
    {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {lam : Matrix (Fin r) (Fin r) ℝ}
    (hS : ∀ i j, HasDerivAt (fun s => S s i j)
      (-innerXV μ ν (X i) (V j) (vlasovF (E t) (lowRank (coreK X (S t)) V)) - lam i j) t)
    (hΦ : ∀ i m, Integrable (fun x => X i x * flux ν (E t) (lowRank (coreK X (S t)) V) m x) μ) :
    ProjectedLawsBackward μ ν X E (fun s => lowRank (coreK X (S s)) V) t ↔
      ∀ i, momentMatrix ν V *ᵥ lam i =
        fun m => rhsKS μ ν X V (E t) (lowRank (coreK X (S t)) V) m i := by
  rw [projectedLawsBackward_iff]
  simp only [proj_eq_zero_iff hX, sStep_residual hX hV hS hΦ, sub_eq_zero]
  exact ⟨fun h i => funext fun m => (h m i).symm, fun h m i => (congrFun (h i) m).symm⟩

/-- **Step 2, main theorem** (arXiv 1807.02338, Sec. 3).  If the rows of `[α; β]` are independent
and `λ` is the minimum-norm solution of (3.8), the corrected S-step satisfies (3.10), (3.11). -/
theorem sStep_quasiConservative (hX : IsOrthonormalL2 μ X)
    (hV : ∀ m j, Integrable (fun v => wt m v * V j v) ν)
    (hrows : LinearIndependent ℝ (momentMatrix ν V).row)
    {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {lam : Matrix (Fin r) (Fin r) ℝ}
    (hlam : ∀ i, lam i = minNormSol (momentMatrix ν V)
      fun m => rhsKS μ ν X V (E t) (lowRank (coreK X (S t)) V) m i)
    (hS : ∀ i j, HasDerivAt (fun s => S s i j)
      (-innerXV μ ν (X i) (V j) (vlasovF (E t) (lowRank (coreK X (S t)) V)) - lam i j) t)
    (hΦ : ∀ i m, Integrable (fun x => X i x * flux ν (E t) (lowRank (coreK X (S t)) V) m x) μ) :
    ProjectedLawsBackward μ ν X E (fun s => lowRank (coreK X (S s)) V) t :=
  (sStep_laws_iff hX hV hS hΦ).2 fun i => by rw [hlam i]; exact mulVec_minNormSol hrows _

/-! ### Integration by parts in velocity: the L-step needs no correction -/

/-- Decay of a velocity profile, standing in for the paper's "`L_k` goes to zero as `|v| → ∞`":
`g` is differentiable, `(1 + |v|²) g` and `(1 + |v|) ∇g` are integrable. -/
structure IsVelocityProfile (ν : Measure (PS d)) (g : PS d → ℝ) : Prop where
  differentiable : Differentiable ℝ g
  integrable : Integrable (fun v => (1 + ‖v‖ ^ 2) * g v) ν
  integrable_pd : ∀ b, Integrable (fun v => (1 + ‖v‖) * pd b g v) ν

lemma IsVelocityProfile.integrable_mul {g : PS d → ℝ} (hg : IsVelocityProfile ν g) {φ : PS d → ℝ}
    (hφ : Continuous φ) (h : ∀ v, |φ v| ≤ 2 * (1 + ‖v‖ ^ 2)) :
    Integrable (fun v => φ v * g v) ν := by
  refine (hg.integrable.const_mul 2).mono
    (hφ.aestronglyMeasurable.mul hg.differentiable.continuous.aestronglyMeasurable)
    (ae_of_all _ fun v => ?_)
  have hp : (0 : ℝ) ≤ 1 + ‖v‖ ^ 2 := by positivity
  rw [norm_mul, norm_mul, norm_mul, Real.norm_eq_abs (φ v), Real.norm_eq_abs (1 + ‖v‖ ^ 2),
    abs_of_nonneg hp, Real.norm_eq_abs (2 : ℝ), abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc |φ v| * ‖g v‖ ≤ 2 * (1 + ‖v‖ ^ 2) * ‖g v‖ :=
        mul_le_mul_of_nonneg_right (h v) (norm_nonneg _)
    _ = 2 * ((1 + ‖v‖ ^ 2) * ‖g v‖) := by ring

lemma IsVelocityProfile.integrable_wt {g : PS d → ℝ} (hg : IsVelocityProfile ν g)
    (m : Option (Fin d)) : Integrable (fun v => wt m v * g v) ν :=
  hg.integrable_mul (continuous_wt m) fun v => (abs_wt_le m v).trans (by
    nlinarith [sq_nonneg (‖v‖ - 1), norm_nonneg v])

lemma IsVelocityProfile.integrable_self {g : PS d → ℝ} (hg : IsVelocityProfile ν g) :
    Integrable g ν := by
  simpa using hg.integrable_wt none

lemma IsVelocityProfile.integrable_coord {g : PS d → ℝ} (hg : IsVelocityProfile ν g) (a : Fin d) :
    Integrable (fun v => v a * g v) ν :=
  hg.integrable_wt (some a)

lemma IsVelocityProfile.integrable_coord_coord {g : PS d → ℝ} (hg : IsVelocityProfile ν g)
    (a b : Fin d) : Integrable (fun v => v a * v b * g v) ν :=
  hg.integrable_mul ((continuous_coord a).mul (continuous_coord b)) fun v => by
    rw [abs_mul]
    have h1 := abs_coord_le a v
    have h2 := abs_coord_le b v
    have h3 : |v a| * |v b| ≤ ‖v‖ * ‖v‖ := mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
    nlinarith [sq_nonneg ‖v‖]

lemma IsVelocityProfile.integrable_wt_coord {g : PS d → ℝ} (hg : IsVelocityProfile ν g)
    (m : Option (Fin d)) (a : Fin d) : Integrable (fun v => wt m v * (v a * g v)) ν := by
  have h := hg.integrable_mul (φ := fun v => wt m v * v a)
    ((continuous_wt m).mul (continuous_coord a)) fun v => by
    rw [abs_mul]
    have h1 := abs_wt_le m v
    have h2 := abs_coord_le a v
    have h3 : |wt m v| * |v a| ≤ (1 + ‖v‖) * ‖v‖ :=
      mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    nlinarith [sq_nonneg (‖v‖ - 1), norm_nonneg v]
  simpa only [mul_assoc] using h

lemma IsVelocityProfile.integrable_wt_pd {g : PS d → ℝ} (hg : IsVelocityProfile ν g)
    (m : Option (Fin d)) (b : Fin d) : Integrable (fun v => wt m v * pd b g v) ν :=
  integrable_wt_of_weighted (hg.integrable_pd b) m

lemma differentiable_wt (m : Option (Fin d)) : Differentiable ℝ (wt m : PS d → ℝ) := by
  cases m with
  | none => exact differentiable_const _
  | some a => exact (EuclideanSpace.proj (𝕜 := ℝ) a : PS d →L[ℝ] ℝ).differentiable

lemma pd_wt_none (b : Fin d) (v : PS d) : pd b (wt none) v = 0 := by
  have h : (wt none : PS d → ℝ) = fun _ => 1 := rfl
  simp [pd, h]

lemma pd_wt_some (c b : Fin d) (v : PS d) : pd b (wt (some c)) v = if c = b then 1 else 0 := by
  have h : HasFDerivAt (wt (some c)) (EuclideanSpace.proj (𝕜 := ℝ) c : PS d →L[ℝ] ℝ) v :=
    (EuclideanSpace.proj (𝕜 := ℝ) c : PS d →L[ℝ] ℝ).hasFDerivAt
  simp [pd, h.fderiv, PiLp.single_apply]

/-- Integration by parts in `v` against the weights. -/
lemma IsVelocityProfile.integral_wt_pd [ν.IsAddHaarMeasure] {g : PS d → ℝ}
    (hg : IsVelocityProfile ν g) (m : Option (Fin d)) (b : Fin d) :
    ∫ v, wt m v * pd b g v ∂ν = -∫ v, pd b (wt m) v * g v ∂ν := by
  have h1 : Integrable (fun v => pd b (wt m) v * g v) ν := by
    cases m with
    | none => simp [pd_wt_none]
    | some c =>
      simp only [pd_wt_some]
      exact hg.integrable_self.const_mul _
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 (hg.integrable_wt_pd m b)
    (hg.integrable_wt m) (fun x _ => differentiable_wt m x) (fun x _ => hg.differentiable x)

/-- `∫ ∂_b g dv = 0`: the term that makes `b_i` vanish in Step 3. -/
lemma IsVelocityProfile.integral_pd [ν.IsAddHaarMeasure] {g : PS d → ℝ}
    (hg : IsVelocityProfile ν g) (b : Fin d) : ∫ v, pd b g v ∂ν = 0 := by
  have h := hg.integral_wt_pd none b
  simpa [pd_wt_none] using h

/-- `∫ v_c ∂_b g dv = -δ_cb ∫ g dv`: the term that produces `-Eρ` in the momentum balance. -/
lemma IsVelocityProfile.integral_coord_pd [ν.IsAddHaarMeasure] {g : PS d → ℝ}
    (hg : IsVelocityProfile ν g) (c b : Fin d) :
    ∫ v, v c * pd b g v ∂ν = -if c = b then ∫ v, g v ∂ν else 0 := by
  have h := hg.integral_wt_pd (some c) b
  simp only [pd_wt_some, wt_some, ite_mul, one_mul, zero_mul] at h
  rw [h]
  split_ifs <;> simp

/-- Velocity integral of a transport-type expression
`∑_k (-∑_a p_ak v_a L_k + ∑_b q_bk ∂_b L_k)`. -/
lemma integral_transport {L : Fin r → PS d → ℝ} (hL : ∀ k, IsVelocityProfile ν (L k))
    (p q : Fin d → Fin r → ℝ) (m : Option (Fin d)) :
    ∫ v, wt m v * ∑ k, (-(∑ a, p a k * (v a * L k v)) + ∑ b, q b k * pd b (L k) v) ∂ν =
      ∑ k, (-(∑ a, p a k * ∫ v, wt m v * (v a * L k v) ∂ν) +
        ∑ b, q b k * ∫ v, wt m v * pd b (L k) v ∂ν) := by
  have e : ∀ v : PS d, wt m v * ∑ k, (-(∑ a, p a k * (v a * L k v)) + ∑ b, q b k * pd b (L k) v) =
      ∑ k, (-(∑ a, p a k * (wt m v * (v a * L k v))) + ∑ b, q b k * (wt m v * pd b (L k) v)) :=
    fun v => by
      rw [mul_sum]
      refine sum_congr rfl fun k _ => ?_
      rw [mul_add, mul_neg, mul_sum, mul_sum]
      congr 1
      · congr 1
        exact sum_congr rfl fun a _ => by ring
      · exact sum_congr rfl fun b _ => by ring
  simp_rw [e]
  have i1 : ∀ k, Integrable (fun v => ∑ a, p a k * (wt m v * (v a * L k v))) ν := fun k =>
    integrable_finsetSum _ fun a _ => ((hL k).integrable_wt_coord m a).const_mul _
  have i2 : ∀ k, Integrable (fun v => ∑ b, q b k * (wt m v * pd b (L k) v)) ν := fun k =>
    integrable_finsetSum _ fun b _ => ((hL k).integrable_wt_pd m b).const_mul _
  have i1' : ∀ k, Integrable (fun v => -∑ a, p a k * (wt m v * (v a * L k v))) ν := fun k =>
    (i1 k).neg
  have i3 : ∀ k, Integrable (fun v => -(∑ a, p a k * (wt m v * (v a * L k v))) +
      ∑ b, q b k * (wt m v * pd b (L k) v)) ν := fun k => (i1' k).add (i2 k)
  rw [integral_finsetSum _ fun k _ => i3 k]
  refine sum_congr rfl fun k _ => ?_
  rw [integral_add (i1' k) (i2 k), integral_neg,
    integral_finsetSum _ fun a _ => ((hL k).integrable_wt_coord m a).const_mul _,
    integral_finsetSum _ fun b _ => ((hL k).integrable_wt_pd m b).const_mul _]
  simp_rw [integral_const_mul]

/-- `F(f)` for `f = ∑ X_k L_k`, sorted as in `integral_transport`. -/
lemma vlasovF_lowRank' (E : PS d → PS d) {A B : Fin r → PS d → ℝ} (x v : PS d)
    (hA : ∀ j, DifferentiableAt ℝ (A j) x) (hB : ∀ j, DifferentiableAt ℝ (B j) v) :
    vlasovF E (lowRank A B) x v =
      ∑ k, (-(∑ a, pd a (A k) x * (v a * B k v)) + ∑ b, (A k x * E x b) * pd b (B k) v) := by
  rw [vlasovF_lowRank E x v hA hB]
  refine sum_congr rfl fun k _ => ?_
  rw [neg_mul, sum_mul, mul_sum]
  congr 1
  · congr 1
    exact sum_congr rfl fun a _ => by ring
  · exact sum_congr rfl fun b _ => by ring

/-- **(3.1), (3.2)** (arXiv 1807.02338): the moment identity behind the continuity equation and the
momentum balance.  For `f = ∑ A_k L_k` with decay in `v` on `Ω_v = ℝ^d`, we have
`∫ w_m F(f) dv = -flux_m`, that is `∫ F(f) dv = -∇·(ρu)` and
`∫ v_a F(f) dv = -(∇·(ρu ⊗ u))_a - E_a ρ`.  Stated for separated `f`, which is the only case the
algorithm uses; this also fixes the sign of `Eρ` in the laws. -/
theorem moment_vlasovF_lowRank [ν.IsAddHaarMeasure] (E₀ : PS d → PS d) {A L : Fin r → PS d → ℝ}
    (hL : ∀ k, IsVelocityProfile ν (L k)) {x : PS d} (hA : ∀ k, DifferentiableAt ℝ (A k) x)
    (m : Option (Fin d)) :
    ∫ v, wt m v * vlasovF E₀ (lowRank A L) x v ∂ν = -flux ν E₀ (lowRank A L) m x := by
  have hF : ∀ v, vlasovF E₀ (lowRank A L) x v = _ := fun v =>
    vlasovF_lowRank' E₀ x v hA fun k => (hL k).differentiable v
  simp_rw [hF]
  rw [integral_transport hL (fun a k => pd a (A k) x) (fun b k => A k x * E₀ x b) m]
  cases m with
  | none =>
    simp only [wt_none, one_mul, (hL _).integral_pd, mul_zero, sum_const_zero, add_zero]
    rw [flux, divMomentum_lowRank (fun a j => (hL j).integrable_coord a) hA, sum_neg_distrib,
      sum_comm]
  | some c =>
    simp only [wt_some, (hL _).integral_coord_pd, mul_neg, mul_ite, mul_zero, sum_neg_distrib,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [flux, divStress_lowRank (fun a b j => (hL j).integrable_coord_coord a b) c hA,
      rho_lowRank (fun j => (hL j).integrable_self) x, mul_sum, sum_add_distrib,
      neg_add, sum_comm]
    simp only [mul_assoc, mul_left_comm (E₀ x c), sum_neg_distrib]

/-- The integral of `∑_k (-∑_a u_ka + ∑_b w_kb)`. -/
private lemma integral_sum_neg_add {α ι₁ ι₂ ι₃ : Type*} [MeasurableSpace α] {ρ₀ : Measure α}
    [Fintype ι₁] [Fintype ι₂] [Fintype ι₃] (u : ι₁ → ι₂ → α → ℝ) (w : ι₁ → ι₃ → α → ℝ)
    (hu : ∀ k a, Integrable (u k a) ρ₀) (hw : ∀ k b, Integrable (w k b) ρ₀) :
    ∫ y, ∑ k, (-(∑ a, u k a y) + ∑ b, w k b y) ∂ρ₀ =
      ∑ k, (-(∑ a, ∫ y, u k a y ∂ρ₀) + ∑ b, ∫ y, w k b y ∂ρ₀) := by
  have i1 : ∀ k, Integrable (fun y => ∑ a, u k a y) ρ₀ := fun k =>
    integrable_finsetSum _ fun a _ => hu k a
  have i1' : ∀ k, Integrable (fun y => -∑ a, u k a y) ρ₀ := fun k => (i1 k).neg
  have i2 : ∀ k, Integrable (fun y => ∑ b, w k b y) ρ₀ := fun k =>
    integrable_finsetSum _ fun b _ => hw k b
  have i3 : ∀ k, Integrable (fun y => -(∑ a, u k a y) + ∑ b, w k b y) ρ₀ := fun k =>
    (i1' k).add (i2 k)
  rw [integral_finsetSum _ fun k _ => i3 k]
  refine sum_congr rfl fun k _ => ?_
  rw [integral_add (i1' k) (i2 k), integral_neg, integral_finsetSum _ fun a _ => hu k a,
    integral_finsetSum _ fun b _ => hw k b]

section LStep

variable {E₀ : PS d → PS d} {L : Fin r → PS d → ℝ}

/-- `⟨X_i, F(f)⟩ₓ` for `f = ∑ X_k L_k`: the coefficients `⟨X_i, ∇X_k⟩ₓ` and `⟨X_i, E X_k⟩ₓ` of the
L-equation (2.7). -/
lemma integral_X_vlasovF (hXd : ∀ k, Differentiable ℝ (X k)) (hLd : ∀ k, Differentiable ℝ (L k))
    (i : Fin r) (hc : ∀ a k, Integrable (fun x => X i x * pd a (X k) x) μ)
    (he : ∀ b k, Integrable (fun x => X i x * (X k x * E₀ x b)) μ) (v : PS d) :
    ∫ x, X i x * vlasovF E₀ (lowRank X L) x v ∂μ =
      ∑ k, (-(∑ a, (∫ x, X i x * pd a (X k) x ∂μ) * (v a * L k v)) +
        ∑ b, (∫ x, X i x * (X k x * E₀ x b) ∂μ) * pd b (L k) v) := by
  have e : ∀ x, X i x * vlasovF E₀ (lowRank X L) x v =
      ∑ k, (-(∑ a, (X i x * pd a (X k) x) * (v a * L k v)) +
        ∑ b, (X i x * (X k x * E₀ x b)) * pd b (L k) v) := fun x => by
    rw [vlasovF_lowRank' E₀ x v (fun k => hXd k x) (fun k => hLd k v), mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [mul_add, mul_neg, mul_sum, mul_sum]
    congr 1
    · congr 1
      exact sum_congr rfl fun a _ => by ring
    · exact sum_congr rfl fun b _ => by ring
  simp_rw [e]
  rw [integral_sum_neg_add _ _ (fun k a => (hc a k).mul_const _)
    (fun k b => (he b k).mul_const _)]
  simp_rw [integral_mul_const]

lemma X_mul_divMomentum (hL : ∀ k, IsVelocityProfile ν (L k)) (hXd : ∀ k, Differentiable ℝ (X k))
    (i : Fin r) (x : PS d) :
    X i x * divMomentum ν (lowRank X L) x =
      ∑ a, ∑ k, (X i x * pd a (X k) x) * ∫ v, v a * L k v ∂ν := by
  rw [divMomentum_lowRank (fun a j => (hL j).integrable_coord a) fun k => hXd k x, mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun k _ => by ring

lemma X_mul_divStress (hL : ∀ k, IsVelocityProfile ν (L k)) (hXd : ∀ k, Differentiable ℝ (X k))
    (i : Fin r) (c : Fin d) (x : PS d) :
    X i x * divStress ν (lowRank X L) c x =
      ∑ b, ∑ k, (X i x * pd b (X k) x) * ∫ v, v c * v b * L k v ∂ν := by
  rw [divStress_lowRank (fun a b j => (hL j).integrable_coord_coord a b) c fun k => hXd k x,
    mul_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun k _ => by ring

lemma X_mul_E_rho (hL : ∀ k, IsVelocityProfile ν (L k)) (i : Fin r) (c : Fin d) (x : PS d) :
    X i x * (E₀ x c * rho ν (lowRank X L) x) =
      ∑ k, (X i x * (X k x * E₀ x c)) * ∫ v, L k v ∂ν := by
  rw [rho_lowRank (fun j => (hL j).integrable_self) x, mul_sum, mul_sum]
  exact sum_congr rfl fun k _ => by ring

lemma integrable_X_divMomentum (hL : ∀ k, IsVelocityProfile ν (L k))
    (hXd : ∀ k, Differentiable ℝ (X k)) (i : Fin r)
    (hc : ∀ a k, Integrable (fun x => X i x * pd a (X k) x) μ) :
    Integrable (fun x => X i x * divMomentum ν (lowRank X L) x) μ := by
  simp_rw [X_mul_divMomentum hL hXd i]
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun k _ => (hc a k).mul_const _

lemma integrable_X_divStress (hL : ∀ k, IsVelocityProfile ν (L k))
    (hXd : ∀ k, Differentiable ℝ (X k)) (i : Fin r) (c : Fin d)
    (hc : ∀ a k, Integrable (fun x => X i x * pd a (X k) x) μ) :
    Integrable (fun x => X i x * divStress ν (lowRank X L) c x) μ := by
  simp_rw [X_mul_divStress hL hXd i c]
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun k _ => (hc a k).mul_const _

lemma integrable_X_E_rho (hL : ∀ k, IsVelocityProfile ν (L k)) (i : Fin r) (c : Fin d)
    (he : ∀ b k, Integrable (fun x => X i x * (X k x * E₀ x b)) μ) :
    Integrable (fun x => X i x * (E₀ x c * rho ν (lowRank X L) x)) μ := by
  simp_rw [X_mul_E_rho hL i c]
  exact integrable_finsetSum _ fun k _ => (he c k).mul_const _

lemma integrable_X_flux (hL : ∀ k, IsVelocityProfile ν (L k)) (hXd : ∀ k, Differentiable ℝ (X k))
    (i : Fin r) (m : Option (Fin d)) (hc : ∀ a k, Integrable (fun x => X i x * pd a (X k) x) μ)
    (he : ∀ b k, Integrable (fun x => X i x * (X k x * E₀ x b)) μ) :
    Integrable (fun x => X i x * flux ν E₀ (lowRank X L) m x) μ := by
  cases m with
  | none => exact integrable_X_divMomentum hL hXd i hc
  | some c =>
    simp only [flux, mul_add]
    exact (integrable_X_divStress hL hXd i c hc).add (integrable_X_E_rho hL i c he)

/-- **Step 3: `b_i = 0`, and also `d_i = 0`** (arXiv 1807.02338, Sec. 3, "step 3 already satisfies
the continuity equation").  For `f = ∑ X_k L_k` with `L_k` decaying in `v`, on `Ω_v = ℝ^d`, both
right-hand sides of (3.8) in Step 3 vanish:
`⟨X_i, F(f)⟩ₓᵥ + ⟨X_i, ∇·(ρu)⟩ₓ = 0` and `⟨X_i, v_a F(f)⟩ₓᵥ + ⟨X_i, ∇·(ρu ⊗ u)_a + E_a ρ⟩ₓ = 0`.
The first is the paper's claim.  The second goes beyond the paper: it says that Step 3 conserves the
projected momentum as well, which the sign error in (3.14) hides (`printedD_eq`).  This is the PDE
flux identity, by integration by parts in `v`; orthonormality is not used. -/
theorem rhsL_lowRank_eq_zero [ν.IsAddHaarMeasure] (hL : ∀ k, IsVelocityProfile ν (L k))
    (hXd : ∀ k, Differentiable ℝ (X k)) (i : Fin r)
    (hc : ∀ a k, Integrable (fun x => X i x * pd a (X k) x) μ)
    (he : ∀ b k, Integrable (fun x => X i x * (X k x * E₀ x b)) μ) (m : Option (Fin d)) :
    rhsL (ν := ν) μ X E₀ (lowRank X L) m i = 0 := by
  have hI := integral_X_vlasovF (L := L) (μ := μ) hXd (fun k => (hL k).differentiable) i hc he
  rw [rhsL]
  simp_rw [hI]
  rw [integral_transport hL _ _ m]
  cases m with
  | none =>
    simp only [wt_none, one_mul, (hL _).integral_pd, mul_zero, sum_const_zero, add_zero]
    simp only [flux]
    simp_rw [X_mul_divMomentum hL hXd i]
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun k _ => (hc a k).mul_const _]
    simp_rw [integral_finsetSum _ fun k _ => (hc _ k).mul_const _, integral_mul_const]
    rw [sum_comm (γ := Fin d), sum_neg_distrib, neg_neg, sub_self]
  | some c =>
    simp only [wt_some, (hL _).integral_coord_pd, mul_neg, mul_ite, mul_zero, sum_neg_distrib,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp only [flux, mul_add]
    rw [integral_add (integrable_X_divStress hL hXd i c hc) (integrable_X_E_rho hL i c he)]
    simp_rw [X_mul_divStress hL hXd i c, X_mul_E_rho hL i c]
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun k _ => (hc a k).mul_const _,
      integral_finsetSum _ fun k _ => (he c k).mul_const _]
    simp_rw [integral_finsetSum _ fun k _ => (hc _ k).mul_const _, integral_mul_const]
    rw [sum_add_distrib, sum_comm (γ := Fin d)]
    simp only [sum_neg_distrib, mul_assoc]
    ring

/-- The right-hand side `d_i` as printed after (3.14), with `+⟨X_i, Eρ⟩`, against the sign in the
law (3.3), in (3.7) and in the Step 3 formula of Sec. 5. -/
noncomputable def printedD (μ ν : Measure (PS d)) (X : Fin r → PS d → ℝ) (E₀ : PS d → PS d)
    (f : PS d → PS d → ℝ) (a : Fin d) (i : Fin r) : ℝ :=
  -(∫ v, v a * ∫ x, X i x * vlasovF E₀ f x v ∂μ ∂ν) - (∫ x, X i x * divStress ν f a x ∂μ) +
    ∫ x, X i x * (E₀ x a * rho ν f x) ∂μ

/-- **Sign error in (3.14)** (arXiv 1807.02338).  The printed `d_i` equals `2 ⟨X_i, E_a ρ⟩`, while
the correct right-hand side vanishes (`rhsL_lowRank_eq_zero`).  So the printed (3.14) is not the
expansion of its own left-hand side, and a solution `λ` of the printed system violates the projected
momentum balance by `2 ⟨X_i, E_a ρ⟩`. -/
theorem printedD_eq [ν.IsAddHaarMeasure] (hL : ∀ k, IsVelocityProfile ν (L k))
    (hXd : ∀ k, Differentiable ℝ (X k)) (i : Fin r) (c : Fin d)
    (hc : ∀ a k, Integrable (fun x => X i x * pd a (X k) x) μ)
    (he : ∀ b k, Integrable (fun x => X i x * (X k x * E₀ x b)) μ) :
    printedD μ ν X E₀ (lowRank X L) c i =
      2 * ∫ x, X i x * (E₀ x c * rho ν (lowRank X L) x) ∂μ := by
  have h := rhsL_lowRank_eq_zero (μ := μ) (E₀ := E₀) hL hXd i hc he (some c)
  simp only [rhsL, flux, wt_some, mul_add] at h
  rw [integral_add (integrable_X_divStress hL hXd i c hc) (integrable_X_E_rho hL i c he)] at h
  rw [printedD]
  linarith

end LStep

/-- **Step 3, the minimal correction vanishes** (arXiv 1807.02338): the minimum-norm solution of
the zero right-hand side is zero. -/
theorem minNormSol_zero {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n]
    (A : Matrix ι n ℝ) : minNormSol A 0 = 0 := by
  simp [minNormSol]

/-- **Step 3, projected laws ⟺ (3.8) with zero right-hand side** (arXiv 1807.02338).  With the sign
of (3.14) corrected, (3.8) for Step 3 reads `[α; β] λ_i = 0`. -/
theorem lStep_laws_iff [ν.IsAddHaarMeasure] (hX : IsOrthonormalL2 μ X)
    (hV : ∀ m j, Integrable (fun v => wt m v * V j v) ν) (hXd : ∀ k, Differentiable ℝ (X k))
    (hc : ∀ i a k, Integrable (fun x => X i x * pd a (X k) x) μ)
    (he : ∀ i b k, Integrable (fun x => X i x * (X k x * E t x b)) μ)
    {L : ℝ → Fin r → PS d → ℝ} {lam : ℝ → Matrix (Fin r) (Fin r) ℝ}
    (hprof : ∀ k, IsVelocityProfile ν (L t k))
    (hL : ∀ k, IsDominatedCurve ν (fun s => L s k) (fun s v =>
      (∫ x, X k x * vlasovF (E s) (lowRank X (L s)) x v ∂μ) + ∑ l, lam s k l * V l v) t) :
    ProjectedLaws μ ν X E (fun s => lowRank X (L s)) t ↔
      ∀ i, momentMatrix ν V *ᵥ lam t i = 0 := by
  have hΦ : ∀ i m, Integrable (fun x => X i x * flux ν (E t) (lowRank X (L t)) m x) μ :=
    fun i m => integrable_X_flux hprof hXd i m (hc i) (he i)
  rw [projectedLaws_iff]
  simp only [proj_eq_zero_iff hX, lStep_residual hX hV hL hΦ,
    rhsL_lowRank_eq_zero hprof hXd _ (hc _) (he _), sub_zero]
  exact ⟨fun h i => funext fun m => h m i, fun h m i => congrFun (h i) m⟩

/-- **Step 3, main theorem** (arXiv 1807.02338, Sec. 3).  The uncorrected L-step (2.7)
`∂ₜL_i = ⟨X_i, F(f)⟩ₓ` already satisfies both projected laws (3.3).  The paper states this for the
continuity equation; for the momentum balance it is new, and contradicts the printed (3.14). -/
theorem lStep_projectedLaws [ν.IsAddHaarMeasure] (hX : IsOrthonormalL2 μ X)
    (hXd : ∀ k, Differentiable ℝ (X k))
    (hc : ∀ i a k, Integrable (fun x => X i x * pd a (X k) x) μ)
    (he : ∀ i b k, Integrable (fun x => X i x * (X k x * E t x b)) μ)
    {L : ℝ → Fin r → PS d → ℝ} (hprof : ∀ k, IsVelocityProfile ν (L t k))
    (hL : ∀ k, IsDominatedCurve ν (fun s => L s k)
      (fun s v => ∫ x, X k x * vlasovF (E s) (lowRank X (L s)) x v ∂μ) t) :
    ProjectedLaws μ ν X E (fun s => lowRank X (L s)) t := by
  have hV : ∀ (m : Option (Fin d)) (j : Fin r),
      Integrable (fun v => wt m v * (0 : Fin r → PS d → ℝ) j v) ν := fun m j => by simp
  refine (lStep_laws_iff (V := 0) (lam := 0) hX hV hXd hc he hprof ?_).2 fun i =>
    Matrix.mulVec_zero _
  simpa using hL

/-! ### Sec. 5: the discrete correction after an arbitrary inner solver -/

/-- The time-discrete projected laws of Sec. 5:
`P_X̄ (ρ¹ - ρ⁰ + τ ∇·(ρ⁰u⁰)) = 0` and `P_X̄ (ρ¹u¹ - ρ⁰u⁰ + τ ∇·(ρ⁰u⁰ ⊗ u⁰) + τ E⁰ρ⁰) = 0`. -/
def DiscreteLaws (μ ν : Measure (PS d)) (X : Fin r → PS d → ℝ) (E₀ : PS d → PS d)
    (f₀ f₁ : PS d → PS d → ℝ) (τ : ℝ) : Prop :=
  proj μ X (fun x => rho ν f₁ x - rho ν f₀ x + τ * divMomentum ν f₀ x) = 0 ∧
    ∀ a, proj μ X (fun x => momentum ν f₁ a x - momentum ν f₀ a x + τ * divStress ν f₀ a x +
      τ * (E₀ x a * rho ν f₀ x)) = 0

/-- The time-discrete analogue of (3.10), (3.11) for the S-step, which runs backward. -/
def DiscreteLawsBackward (μ ν : Measure (PS d)) (X : Fin r → PS d → ℝ) (E₀ : PS d → PS d)
    (f₀ f₁ : PS d → PS d → ℝ) (τ : ℝ) : Prop :=
  proj μ X (fun x => rho ν f₁ x - rho ν f₀ x - τ * divMomentum ν f₀ x) = 0 ∧
    ∀ a, proj μ X (fun x => momentum ν f₁ a x - momentum ν f₀ a x - τ * divStress ν f₀ a x -
      τ * (E₀ x a * rho ν f₀ x)) = 0

lemma discreteLaws_iff {E₀ : PS d → PS d} {f₀ f₁ : PS d → PS d → ℝ} {τ : ℝ} :
    DiscreteLaws μ ν X E₀ f₀ f₁ τ ↔ ∀ m, proj μ X (fun x =>
      moment ν m f₁ x - moment ν m f₀ x + τ * flux ν E₀ f₀ m x) = 0 := by
  rw [Option.forall]
  simp only [flux, moment_none, moment_some, DiscreteLaws, mul_add, add_assoc, sub_eq_add_neg]

lemma discreteLawsBackward_iff {E₀ : PS d → PS d} {f₀ f₁ : PS d → PS d → ℝ} {τ : ℝ} :
    DiscreteLawsBackward μ ν X E₀ f₀ f₁ τ ↔ ∀ m, proj μ X (fun x =>
      moment ν m f₁ x - moment ν m f₀ x - τ * flux ν E₀ f₀ m x) = 0 := by
  rw [Option.forall]
  simp only [flux, moment_none, moment_some, DiscreteLawsBackward, mul_add, sub_eq_add_neg, neg_add,
    add_assoc]

/-- The right-hand side of (3.8) of Sec. 5 for Step 1: with `∇·(ρ⁰u⁰) = ∑_j ∇K⁰_j · β_j`,
`b_i = -∑_j ⟨X_i, (K*_j - K⁰_j)/τ⟩ₓ α_j - ⟨X_i, ∇·(ρ⁰u⁰)⟩ₓ`, and `d_i` likewise with
`β_j` and the flux `∇·(ρ⁰u⁰ ⊗ u⁰) + E⁰ρ⁰`. -/
noncomputable def rhsKDisc (μ ν : Measure (PS d)) (X V : Fin r → PS d → ℝ) (E₀ : PS d → PS d)
    (K₀ Kstar : Fin r → PS d → ℝ) (τ : ℝ) (m : Option (Fin d)) (i : Fin r) : ℝ :=
  -∑ j, (∫ x, X i x * ((Kstar j x - K₀ j x) / τ) ∂μ) * momentMatrix ν V m j -
    ∫ x, X i x * flux ν E₀ (lowRank K₀ V) m x ∂μ

/-- The right-hand side of (3.8) of Sec. 5 for Step 2. -/
noncomputable def rhsSDisc (μ ν : Measure (PS d)) (X V : Fin r → PS d → ℝ) (E₀ : PS d → PS d)
    (S₀ Sstar : Matrix (Fin r) (Fin r) ℝ) (τ : ℝ) (m : Option (Fin d)) (i : Fin r) : ℝ :=
  ∑ j, (Sstar i j - S₀ i j) / τ * momentMatrix ν V m j -
    ∫ x, X i x * flux ν E₀ (lowRank (coreK X S₀) V) m x ∂μ

/-- The right-hand side of (3.8) of Sec. 5 for Step 3. -/
noncomputable def rhsLDisc (μ ν : Measure (PS d)) (X : Fin r → PS d → ℝ) (E₀ : PS d → PS d)
    (L₀ Lstar : Fin r → PS d → ℝ) (τ : ℝ) (m : Option (Fin d)) (i : Fin r) : ℝ :=
  -(∫ v, wt m v * ((Lstar i v - L₀ i v) / τ) ∂ν) -
    ∫ x, X i x * flux ν E₀ (lowRank X L₀) m x ∂μ

variable {E₀ : PS d → PS d} {τ : ℝ}

/-- **Sec. 5, Step 1, residual** (arXiv 1807.02338).  After an arbitrary inner solver producing
`K*` from `K⁰`, the update `K¹_j = K*_j + τ ∑_k λ_kj X_k` gives the `X_i`-component
`τ (∑_j λ_ij α_j - b_i)` of the discrete residual, and likewise with `β_j`, `d_i`. -/
theorem kStep_discrete_residual (hX : IsOrthonormalL2 μ X)
    (hV : ∀ m j, Integrable (fun v => wt m v * V j v) ν) (hτ : τ ≠ 0)
    {K₀ Kstar : Fin r → PS d → ℝ} (lam : Matrix (Fin r) (Fin r) ℝ)
    (hstar : ∀ i j, Integrable (fun x => X i x * (Kstar j x - K₀ j x)) μ)
    (hΦ : ∀ i m, Integrable (fun x => X i x * flux ν E₀ (lowRank K₀ V) m x) μ)
    (m : Option (Fin d)) (i : Fin r) :
    ∫ x, X i x * (moment ν m (lowRank (fun j x => Kstar j x + τ * ∑ k, lam k j * X k x) V) x -
        moment ν m (lowRank K₀ V) x + τ * flux ν E₀ (lowRank K₀ V) m x) ∂μ =
      τ * ((momentMatrix ν V *ᵥ lam i) m - rhsKDisc μ ν X V E₀ K₀ Kstar τ m i) := by
  set A := momentMatrix ν V with hA
  set Φ : PS d → ℝ := flux ν E₀ (lowRank K₀ V) m with hΦdef
  have hm : ∀ K' : Fin r → PS d → ℝ, ∀ x, moment ν m (lowRank K' V) x = ∑ j, K' j x * A m j :=
    fun K' x => moment_lowRank (hV m) x
  have e : ∀ x, moment ν m (lowRank (fun j x => Kstar j x + τ * ∑ k, lam k j * X k x) V) x -
      moment ν m (lowRank K₀ V) x + τ * Φ x =
      ∑ k, X k x * (τ * ∑ j, lam k j * A m j) +
        (∑ j, (Kstar j x - K₀ j x) * A m j + τ * Φ x) := fun x => by
    rw [hm, hm]
    have h1 : ∑ j, (Kstar j x + τ * ∑ k, lam k j * X k x) * A m j =
        ∑ k, X k x * (τ * ∑ j, lam k j * A m j) + ∑ j, Kstar j x * A m j := by
      have := sum_corrected (fun j => Kstar j x) (τ • lam) (fun k => X k x) (A m)
      simp only [Matrix.smul_apply, smul_eq_mul, ← mul_sum, mul_assoc] at this
      rw [this]
    rw [h1]
    simp only [sub_mul, sum_sub_distrib]
    ring
  have h1 : ∀ j, Integrable (fun x => X i x * (Kstar j x - K₀ j x) * A m j) μ := fun j =>
    (hstar i j).mul_const _
  have h2 : Integrable (fun x => X i x * (τ * Φ x)) μ := by
    have := (hΦ i m).const_mul τ
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only
    ring
  have e2 : ∀ x, X i x * (∑ j, (Kstar j x - K₀ j x) * A m j + τ * Φ x) =
      ∑ j, X i x * (Kstar j x - K₀ j x) * A m j + X i x * (τ * Φ x) := fun x => by
    rw [mul_add, mul_sum]
    simp only [mul_assoc]
  have hint : Integrable (fun x => X i x * (∑ j, (Kstar j x - K₀ j x) * A m j + τ * Φ x)) μ := by
    simp_rw [e2]
    exact (integrable_finsetSum _ fun j _ => h1 j).add h2
  simp_rw [e]
  rw [hX.integral_mul_sum_add i _ hint]
  simp_rw [e2]
  rw [integral_add (integrable_finsetSum _ fun j _ => h1 j) h2,
    integral_finsetSum _ fun j _ => h1 j, rhsKDisc]
  simp_rw [integral_mul_const]
  have e3 : ∀ j, ∫ x, X i x * ((Kstar j x - K₀ j x) / τ) ∂μ =
      (∫ x, X i x * (Kstar j x - K₀ j x) ∂μ) / τ := fun j => by
    rw [← integral_div]
    congr 1
    funext x
    ring
  have e4 : ∫ x, X i x * (τ * Φ x) ∂μ = τ * ∫ x, X i x * Φ x ∂μ := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  simp_rw [e3]
  rw [e4]
  simp only [Matrix.mulVec, dotProduct]
  have h4 : ∑ j, lam i j * A m j = ∑ j, A m j * lam i j := sum_congr rfl fun j _ => mul_comm _ _
  rw [h4]
  simp only [div_mul_eq_mul_div, ← sum_div]
  field_simp
  ring

/-- **Sec. 5, Step 1, main theorem** (arXiv 1807.02338).  The discrete projected laws hold exactly
when `λ` solves (3.8) with the Sec. 5 right-hand side.  In particular they hold for the minimum-norm
`λ` if the rows of `[α; β]` are independent, whichever solver produced `K*`. -/
theorem kStep_discrete_iff (hX : IsOrthonormalL2 μ X)
    (hV : ∀ m j, Integrable (fun v => wt m v * V j v) ν) (hτ : τ ≠ 0)
    {K₀ Kstar : Fin r → PS d → ℝ} (lam : Matrix (Fin r) (Fin r) ℝ)
    (hstar : ∀ i j, Integrable (fun x => X i x * (Kstar j x - K₀ j x)) μ)
    (hΦ : ∀ i m, Integrable (fun x => X i x * flux ν E₀ (lowRank K₀ V) m x) μ) :
    DiscreteLaws μ ν X E₀ (lowRank K₀ V)
        (lowRank (fun j x => Kstar j x + τ * ∑ k, lam k j * X k x) V) τ ↔
      ∀ i, momentMatrix ν V *ᵥ lam i = fun m => rhsKDisc μ ν X V E₀ K₀ Kstar τ m i := by
  rw [discreteLaws_iff]
  simp only [proj_eq_zero_iff hX, kStep_discrete_residual hX hV hτ lam hstar hΦ, mul_eq_zero, hτ,
    false_or, sub_eq_zero]
  exact ⟨fun h i => funext fun m => h m i, fun h m i => congrFun (h i) m⟩

/-- `moment` of `f = ∑_kl X_k S_kl V_l`. -/
lemma moment_coreK (hV : ∀ m j, Integrable (fun v => wt m v * V j v) ν)
    (S : Matrix (Fin r) (Fin r) ℝ) (m : Option (Fin d)) (x : PS d) :
    moment ν m (lowRank (coreK X S) V) x = ∑ k, X k x * ∑ l, S k l * momentMatrix ν V m l := by
  rw [moment_lowRank (hV m) x]
  simp only [coreK, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun l _ => ?_
  simp only [momentMatrix, Matrix.of_apply]
  ring

/-- **Sec. 5, Step 2, residual** (arXiv 1807.02338).  The update is `S¹ = S* - τ λ`, the sign being
that of (3.9).  The paper's displayed formula has index misprints (a single sum over `j` with
`⟨X_i, ∇X_j⟩ S_ij`, and `⟨E⁰, X_j⟩` without `X_i`); the form below, with the flux
`⟨X_i, ∇·(ρu)⟩ₓ = ∑_kj ⟨X_i, ∇X_k⟩ₓ S_kj · β_j`, is what its derivation gives. -/
theorem sStep_discrete_residual (hX : IsOrthonormalL2 μ X)
    (hV : ∀ m j, Integrable (fun v => wt m v * V j v) ν) (hτ : τ ≠ 0)
    {S₀ Sstar : Matrix (Fin r) (Fin r) ℝ} (lam : Matrix (Fin r) (Fin r) ℝ)
    (hΦ : ∀ i m, Integrable (fun x => X i x * flux ν E₀ (lowRank (coreK X S₀) V) m x) μ)
    (m : Option (Fin d)) (i : Fin r) :
    ∫ x, X i x * (moment ν m (lowRank (coreK X (Sstar - τ • lam)) V) x -
        moment ν m (lowRank (coreK X S₀) V) x - τ * flux ν E₀ (lowRank (coreK X S₀) V) m x) ∂μ =
      τ * (rhsSDisc μ ν X V E₀ S₀ Sstar τ m i - (momentMatrix ν V *ᵥ lam i) m) := by
  set A := momentMatrix ν V with hA
  set Φ : PS d → ℝ := flux ν E₀ (lowRank (coreK X S₀) V) m with hΦdef
  have e : ∀ x, moment ν m (lowRank (coreK X (Sstar - τ • lam)) V) x -
      moment ν m (lowRank (coreK X S₀) V) x - τ * Φ x =
      ∑ k, X k x * (∑ l, (Sstar - τ • lam) k l * A m l - ∑ l, S₀ k l * A m l) + -(τ * Φ x) :=
    fun x => by
      rw [moment_coreK hV, moment_coreK hV]
      simp only [mul_sub, sum_sub_distrib]
      ring
  have h2 : Integrable (fun x => X i x * -(τ * Φ x)) μ := by
    have := ((hΦ i m).const_mul τ).neg
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only [Pi.neg_apply]
    ring
  simp_rw [e]
  rw [hX.integral_mul_sum_add i _ h2, rhsSDisc]
  have e4 : ∫ x, X i x * -(τ * Φ x) ∂μ = -(τ * ∫ x, X i x * Φ x ∂μ) := by
    rw [← integral_const_mul, ← integral_neg]
    congr 1
    funext x
    ring
  rw [e4]
  simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, sub_mul,
    sum_sub_distrib, div_mul_eq_mul_div, ← sum_div, mul_assoc, ← mul_sum]
  have h4 : ∑ j, lam i j * A m j = ∑ j, A m j * lam i j := sum_congr rfl fun j _ => mul_comm _ _
  rw [h4]
  field_simp
  ring

/-- **Sec. 5, Step 2, main theorem** (arXiv 1807.02338).  The discrete backward laws hold exactly
when `λ` solves (3.8) with the Sec. 5 right-hand side, whichever solver produced `S*`. -/
theorem sStep_discrete_iff (hX : IsOrthonormalL2 μ X)
    (hV : ∀ m j, Integrable (fun v => wt m v * V j v) ν) (hτ : τ ≠ 0)
    {S₀ Sstar : Matrix (Fin r) (Fin r) ℝ} (lam : Matrix (Fin r) (Fin r) ℝ)
    (hΦ : ∀ i m, Integrable (fun x => X i x * flux ν E₀ (lowRank (coreK X S₀) V) m x) μ) :
    DiscreteLawsBackward μ ν X E₀ (lowRank (coreK X S₀) V)
        (lowRank (coreK X (Sstar - τ • lam)) V) τ ↔
      ∀ i, momentMatrix ν V *ᵥ lam i = fun m => rhsSDisc μ ν X V E₀ S₀ Sstar τ m i := by
  rw [discreteLawsBackward_iff]
  simp only [proj_eq_zero_iff hX, sStep_discrete_residual hX hV hτ lam hΦ, mul_eq_zero, hτ,
    false_or, sub_eq_zero]
  exact ⟨fun h i => funext fun m => (h m i).symm, fun h m i => (congrFun (h i) m).symm⟩

/-- **Sec. 5, Step 3, residual** (arXiv 1807.02338).  The update is
`L¹_i = L*_i + τ ∑_l λ_il V_l`.  In the paper's `d_i` for this step the first term reads
`⟨(L*_i - L⁰_i)/τ⟩ᵥ` with the weight `v` missing; the form below has it. -/
theorem lStep_discrete_residual (hX : IsOrthonormalL2 μ X)
    (hV : ∀ m j, Integrable (fun v => wt m v * V j v) ν) (hτ : τ ≠ 0)
    {L₀ Lstar : Fin r → PS d → ℝ} (lam : Matrix (Fin r) (Fin r) ℝ)
    (hL₀ : ∀ m k, Integrable (fun v => wt m v * L₀ k v) ν)
    (hLstar : ∀ m k, Integrable (fun v => wt m v * Lstar k v) ν)
    (hΦ : ∀ i m, Integrable (fun x => X i x * flux ν E₀ (lowRank X L₀) m x) μ)
    (m : Option (Fin d)) (i : Fin r) :
    ∫ x, X i x * (moment ν m (lowRank X fun k v => Lstar k v + τ * ∑ l, lam k l * V l v) x -
        moment ν m (lowRank X L₀) x + τ * flux ν E₀ (lowRank X L₀) m x) ∂μ =
      τ * ((momentMatrix ν V *ᵥ lam i) m - rhsLDisc (ν := ν) μ X E₀ L₀ Lstar τ m i) := by
  set A := momentMatrix ν V with hA
  set Φ : PS d → ℝ := flux ν E₀ (lowRank X L₀) m with hΦdef
  have hsum : ∀ k, Integrable (fun v => ∑ l, lam k l * (wt m v * V l v)) ν := fun k =>
    integrable_finsetSum _ fun l _ => (hV m l).const_mul _
  have hw : ∀ k v, wt m v * (Lstar k v + τ * ∑ l, lam k l * V l v) =
      wt m v * Lstar k v + τ * ∑ l, lam k l * (wt m v * V l v) := fun k v => by
    rw [mul_add, mul_left_comm, mul_sum]
    congr 2
    exact sum_congr rfl fun l _ => by ring
  have hL₁ : ∀ k, Integrable (fun v => wt m v * (Lstar k v + τ * ∑ l, lam k l * V l v)) ν :=
    fun k => by
      simp_rw [hw]
      exact (hLstar m k).add ((hsum k).const_mul τ)
  have hmom : ∀ k, ∫ v, wt m v * (Lstar k v + τ * ∑ l, lam k l * V l v) ∂ν =
      (∫ v, wt m v * Lstar k v ∂ν) + τ * ∑ l, lam k l * A m l := fun k => by
    simp_rw [hw]
    rw [integral_add (hLstar m k) ((hsum k).const_mul τ), integral_const_mul,
      integral_finsetSum _ fun l _ => (hV m l).const_mul _]
    simp_rw [integral_const_mul]
    rfl
  have e : ∀ x, moment ν m (lowRank X fun k v => Lstar k v + τ * ∑ l, lam k l * V l v) x -
      moment ν m (lowRank X L₀) x + τ * Φ x =
      ∑ k, X k x * ((∫ v, wt m v * Lstar k v ∂ν) + τ * (∑ l, lam k l * A m l) -
        ∫ v, wt m v * L₀ k v ∂ν) + τ * Φ x := fun x => by
    rw [moment_lowRank hL₁ x, moment_lowRank (hL₀ m) x]
    simp only [hmom, mul_sub, sum_sub_distrib]
  have h2 : Integrable (fun x => X i x * (τ * Φ x)) μ := by
    have := (hΦ i m).const_mul τ
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only
    ring
  simp_rw [e]
  rw [hX.integral_mul_sum_add i _ h2, rhsLDisc]
  have e4 : ∫ x, X i x * (τ * Φ x) ∂μ = τ * ∫ x, X i x * Φ x ∂μ := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  have e5 : ∫ v, wt m v * ((Lstar i v - L₀ i v) / τ) ∂ν =
      ((∫ v, wt m v * Lstar i v ∂ν) - ∫ v, wt m v * L₀ i v ∂ν) / τ := by
    rw [← integral_sub (hLstar m i) (hL₀ m i), ← integral_div]
    congr 1
    funext v
    ring
  rw [e4, e5]
  simp only [Matrix.mulVec, dotProduct]
  have h4 : ∑ j, lam i j * A m j = ∑ j, A m j * lam i j := sum_congr rfl fun j _ => mul_comm _ _
  rw [h4]
  field_simp
  ring

/-- **Sec. 5, Step 3, main theorem** (arXiv 1807.02338).  The discrete laws hold exactly when `λ`
solves (3.8) with the Sec. 5 right-hand side, whichever solver produced `L*`.  Unlike the
time-continuous case the right-hand side need not vanish here. -/
theorem lStep_discrete_iff (hX : IsOrthonormalL2 μ X)
    (hV : ∀ m j, Integrable (fun v => wt m v * V j v) ν) (hτ : τ ≠ 0)
    {L₀ Lstar : Fin r → PS d → ℝ} (lam : Matrix (Fin r) (Fin r) ℝ)
    (hL₀ : ∀ m k, Integrable (fun v => wt m v * L₀ k v) ν)
    (hLstar : ∀ m k, Integrable (fun v => wt m v * Lstar k v) ν)
    (hΦ : ∀ i m, Integrable (fun x => X i x * flux ν E₀ (lowRank X L₀) m x) μ) :
    DiscreteLaws μ ν X E₀ (lowRank X L₀)
        (lowRank X fun k v => Lstar k v + τ * ∑ l, lam k l * V l v) τ ↔
      ∀ i, momentMatrix ν V *ᵥ lam i = fun m => rhsLDisc (ν := ν) μ X E₀ L₀ Lstar τ m i := by
  rw [discreteLaws_iff]
  simp only [proj_eq_zero_iff hX, lStep_discrete_residual hX hV hτ lam hL₀ hLstar hΦ, mul_eq_zero,
    hτ, false_or, sub_eq_zero]
  exact ⟨fun h i => funext fun m => h m i, fun h m i => congrFun (h i) m⟩

/-! ### The correction (3.4) inside the three substeps -/

/-- The correction (3.4): `∑_kl λ_kl X_k V_l`. -/
def correction (X V : Fin r → PS d → ℝ) (lam : Matrix (Fin r) (Fin r) ℝ) (x v : PS d) : ℝ :=
  ∑ k, ∑ l, lam k l * X k x * V l v

/-- **Second line of (3.5)** (arXiv 1807.02338): by orthonormality of `V`,
`⟨V_j, G + ∑_kl λ_kl X_k V_l⟩ᵥ = ⟨V_j, G⟩ᵥ + ∑_k λ_kj X_k`.  So (3.5) is the K-equation (2.5) with
the correction (3.4) added to `F(f)`. -/
theorem inner_V_correction (hV : IsOrthonormalL2 ν V) (lam : Matrix (Fin r) (Fin r) ℝ) (x : PS d)
    {G : PS d → ℝ} (hG : ∀ j, Integrable (fun v => V j v * G v) ν) (j : Fin r) :
    ∫ v, V j v * (G v + correction X V lam x v) ∂ν =
      (∫ v, V j v * G v ∂ν) + ∑ k, lam k j * X k x := by
  have e : ∀ v, G v + correction X V lam x v = ∑ l, V l v * (∑ k, lam k l * X k x) + G v :=
    fun v => by
      rw [correction, add_comm, sum_comm]
      congr 1
      refine sum_congr rfl fun l _ => ?_
      rw [mul_sum]
      exact sum_congr rfl fun k _ => by ring
  simp_rw [e]
  rw [hV.integral_mul_sum_add j _ (hG j), add_comm]

/-- **Second line of (3.12)** (arXiv 1807.02338): by orthonormality of `X`,
`⟨X_i, G + ∑_kl λ_kl X_k V_l⟩ₓ = ⟨X_i, G⟩ₓ + ∑_l λ_il V_l`. -/
theorem inner_X_correction (hX : IsOrthonormalL2 μ X) (lam : Matrix (Fin r) (Fin r) ℝ) (v : PS d)
    {G : PS d → ℝ} (hG : ∀ i, Integrable (fun x => X i x * G x) μ) (i : Fin r) :
    ∫ x, X i x * (G x + correction X V lam x v) ∂μ =
      (∫ x, X i x * G x ∂μ) + ∑ l, lam i l * V l v := by
  have e : ∀ x, G x + correction X V lam x v = ∑ k, X k x * (∑ l, lam k l * V l v) + G x :=
    fun x => by
      rw [correction, add_comm]
      congr 1
      refine sum_congr rfl fun k _ => ?_
      rw [mul_sum]
      exact sum_congr rfl fun l _ => by ring
  simp_rw [e]
  rw [hX.integral_mul_sum_add i _ (hG i), add_comm]

/-- **Second line of (3.9)** (arXiv 1807.02338):
`⟨X_i V_j, G + ∑_kl λ_kl X_k V_l⟩ₓᵥ = ⟨X_i V_j, G⟩ₓᵥ + λ_ij`. -/
theorem innerXV_correction (hX : IsOrthonormalL2 μ X) (hV : IsOrthonormalL2 ν V)
    (lam : Matrix (Fin r) (Fin r) ℝ) {G : PS d → PS d → ℝ}
    (hG : ∀ x j, Integrable (fun v => V j v * G x v) ν) (i j : Fin r)
    (hGX : Integrable (fun x => X i x * ∫ v, V j v * G x v ∂ν) μ) :
    innerXV μ ν (X i) (V j) (fun x v => G x v + correction X V lam x v) =
      innerXV μ ν (X i) (V j) G + lam i j := by
  have e : ∀ x, ∫ v, V j v * (G x v + correction X V lam x v) ∂ν =
      ∑ k, X k x * lam k j + ∫ v, V j v * G x v ∂ν := fun x => by
    rw [inner_V_correction hV lam x (hG x), add_comm]
    congr 1
    exact sum_congr rfl fun k _ => mul_comm _ _
  simp only [innerXV, e]
  rw [hX.integral_mul_sum_add i _ hGX, add_comm]

/-! ### Remark 1: conditioning -/

/-- **Sec. 3, the Euclidean norm of `λ`** (arXiv 1807.02338): `‖∑ y_i X_i‖² = ∑ y_i²` for
orthonormal `X_i`, so the Euclidean norm of the coefficients of the correction is its `L²` norm. -/
theorem IsOrthonormalL2.integral_sum_sq {α : Type*} [MeasurableSpace α] {μ₀ : Measure α}
    {Y : Fin r → α → ℝ} (hY : IsOrthonormalL2 μ₀ Y) (y : Fin r → ℝ) :
    ∫ x, (∑ i, y i * Y i x) ^ 2 ∂μ₀ = ∑ i, y i ^ 2 := by
  have e : ∀ x, (∑ i, y i * Y i x) ^ 2 = ∑ i, ∑ k, y i * y k * (Y i x * Y k x) := fun x => by
    rw [sq, sum_mul_sum]
    exact sum_congr rfl fun i _ => sum_congr rfl fun k _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
    (hY.integrable_mul i k).const_mul _]
  simp_rw [integral_finsetSum _ fun k _ => (hY.integrable_mul _ k).const_mul _,
    integral_const_mul, hY.inner_eq]
  simp [sq]

/-- The smallest singular value `min_{|z| = 1} ‖∑_j z_j K_j‖_{L²}` of the family
`K = (K_1, …, K_r)`, seen as a map `ℝ^r → L²(μ)`. -/
noncomputable def sigmaMinL2 (μ : Measure (PS d)) (K : Fin r → PS d → ℝ) : ℝ :=
  sInf ((fun z : EuclideanSpace ℝ (Fin r) =>
    Real.sqrt (∫ x, (∑ j, z j * K j x) ^ 2 ∂μ)) '' Metric.sphere 0 1)

lemma sum_mul_coreK (S : Matrix (Fin r) (Fin r) ℝ) (z : Fin r → ℝ) (x : PS d) :
    ∑ j, z j * coreK X S j x = ∑ k, (S *ᵥ z) k * X k x := by
  simp only [coreK, Matrix.mulVec, dotProduct, mul_sum, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun k _ => sum_congr rfl fun j _ => by ring

/-- **Remark 1, the isometry** (arXiv 1807.02338): `‖X S z‖ = ‖S z‖`. -/
theorem sqrt_integral_coreK (hX : IsOrthonormalL2 μ X) (S : Matrix (Fin r) (Fin r) ℝ)
    (z : EuclideanSpace ℝ (Fin r)) :
    Real.sqrt (∫ x, (∑ j, z j * coreK X S j x) ^ 2 ∂μ) = ‖Matrix.toEuclideanLin S z‖ := by
  simp_rw [sum_mul_coreK]
  rw [hX.integral_sum_sq, EuclideanSpace.norm_eq]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  simp [Matrix.toLpLin_apply]

/-- **Remark 1** (arXiv 1807.02338): "the smallest singular value of `K = (K_1, …, K_r)` is equal to
that of `S`", for `K_j = ∑_i X_i S_ij` with orthonormal `X_i`.  Here `K` is a map `ℝ^r → L²(μ)` and
the right-hand side is Mathlib's `r`-th singular value of `S`. -/
theorem sigmaMinL2_coreK (hr : 0 < r) (hX : IsOrthonormalL2 μ X) (S : Matrix (Fin r) (Fin r) ℝ) :
    sigmaMinL2 μ (coreK X S) = (Matrix.toEuclideanLin S).singularValues (r - 1) := by
  set T := Matrix.toEuclideanLin S with hT
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin r)) = r := by simp
  have hlt : r - 1 < Module.finrank ℝ (EuclideanSpace ℝ (Fin r)) := by rw [hfin]; omega
  refine IsLeast.csInf_eq ⟨⟨T.rightSingularBasis ⟨r - 1, hlt⟩, ?_, ?_⟩, ?_⟩
  · simp
  · simp only
    rw [sqrt_integral_coreK hX S]
    exact T.norm_apply_rightSingularBasis ⟨r - 1, hlt⟩
  · rintro _ ⟨z, hz, rfl⟩
    have hz1 : ‖z‖ = 1 := by simpa using hz
    have h := T.singularValues_mul_norm_le z
    rw [hfin, hz1, mul_one] at h
    simp only
    rw [sqrt_integral_coreK hX S]
    exact h

/-- **Remark 1, "the situation is analogous for `V⁰` and `L`"** (arXiv 1807.02338): for
`L_i = ∑_j S_ij V_j` with orthonormal `V_j` (`coreK V Sᵀ i = L_i`), the smallest singular value of
`L` is again that of `S`. -/
theorem sigmaMinL2_coreK_transpose (hr : 0 < r) (hV : IsOrthonormalL2 ν V)
    (S : Matrix (Fin r) (Fin r) ℝ) :
    sigmaMinL2 ν (coreK V Sᵀ) = (Matrix.toEuclideanLin S).singularValues (r - 1) := by
  rw [sigmaMinL2_coreK hr hV, SVD.singularValues_transpose]

/-- **Remark 1, the K-ansatz** (arXiv 1807.02338): for a correction `∑_k C_kj K_k` in place of
`∑_k λ_kj X_k` and `K = X S`, the contribution to the `X_i`-component of the law `m` is
`(S C Aᵀ)_im`.  So the K-ansatz leads to the coupled system `S C [α; β]ᵀ = R`, not to (3.8). -/
theorem kAnsatz_contribution {ι : Type*} (hX : IsOrthonormalL2 μ X)
    (S C : Matrix (Fin r) (Fin r) ℝ) (A : Matrix ι (Fin r) ℝ) (i : Fin r) (m : ι) :
    ∫ x, X i x * ∑ j, (∑ k, C k j * coreK X S k x) * A m j ∂μ = (S * C * Aᵀ) i m := by
  have e : ∀ x, ∑ j, (∑ k, C k j * coreK X S k x) * A m j =
      ∑ l, X l x * (S * C * Aᵀ) l m + 0 := fun x => by
    have h1 : ∀ j, ∑ k, C k j * coreK X S k x = ∑ l, (S * C) l j * X l x := fun j =>
      sum_mul_coreK S (fun k => C k j) x
    simp only [h1, sum_mul, add_zero]
    rw [sum_comm]
    refine sum_congr rfl fun l _ => ?_
    rw [Matrix.mul_apply, mul_sum]
    exact sum_congr rfl fun j _ => by rw [Matrix.transpose_apply]; ring
  simp_rw [e]
  rw [hX.integral_mul_sum_add i _ (by simp)]
  simp

open scoped LeanDLRA.Frobenius in
/-- `‖M y‖ ≤ ‖M‖_F ‖y‖`. -/
lemma norm_toEuclideanLin_le {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
    (M : Matrix ι n ℝ) (y : EuclideanSpace ℝ n) : ‖Matrix.toEuclideanLin M y‖ ≤ ‖M‖ * ‖y‖ := by
  have h1 : ‖Matrix.toEuclideanLin M y‖ ^ 2 ≤ (‖M‖ * ‖y‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq]
    have hM : ‖M‖ ^ 2 = ∑ i, ∑ j, M i j ^ 2 := by
      rw [LeanDLRA.Frobenius.norm_sq_eq_sum]
    rw [hM, sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (M i) y.ofLp
    simpa [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct] using h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h1

open scoped LeanDLRA.Frobenius in
/-- **Remark 1, blow-up of the coefficients** (arXiv 1807.02338).  Any coefficient matrix `C` of
the K-ansatz solves `S C Aᵀ = R` (`kAnsatz_contribution`), and then, for a unit vector `z`,
`‖Rᵀ z‖ ≤ σ_min(S) ‖C‖ ‖A‖`.  So `‖C‖` is at least `‖Rᵀ z‖ / (σ_min(S) ‖A‖)`: the coefficients blow
up as `σ_min(S) → 0` unless the right-hand side vanishes in the direction `z`.  The coefficients of
the `X⁰`-ansatz are bounded independently of `S`, see `minNormSol_norm_le`. -/
theorem kAnsatz_blowup {ι : Type*} [Fintype ι] (hr : 0 < r)
    {S C : Matrix (Fin r) (Fin r) ℝ} {A : Matrix ι (Fin r) ℝ} {R : Matrix (Fin r) ι ℝ}
    (hsys : S * C * Aᵀ = R) :
    ∃ z : EuclideanSpace ℝ (Fin r), ‖z‖ = 1 ∧ ‖Matrix.toEuclideanLin Rᵀ z‖ ≤
      (Matrix.toEuclideanLin S).singularValues (r - 1) * ‖C‖ * ‖A‖ := by
  set T := Matrix.toEuclideanLin Sᵀ with hT
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin r)) = r := by simp
  have hlt : r - 1 < Module.finrank ℝ (EuclideanSpace ℝ (Fin r)) := by rw [hfin]; omega
  set z := T.rightSingularBasis ⟨r - 1, hlt⟩ with hz
  have hz1 : ‖z‖ = 1 := (T.rightSingularBasis).orthonormal.1 ⟨r - 1, hlt⟩
  have hTz : ‖T z‖ = (Matrix.toEuclideanLin S).singularValues (r - 1) := by
    have := T.norm_apply_rightSingularBasis ⟨r - 1, hlt⟩
    simp only [hT, SVD.singularValues_transpose] at this
    exact this
  refine ⟨z, hz1, ?_⟩
  have hR : Rᵀ = (A * Cᵀ) * Sᵀ := by
    rw [← hsys]
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have hcomp : Matrix.toEuclideanLin Rᵀ z = Matrix.toEuclideanLin (A * Cᵀ) (T z) := by
    rw [hR, Matrix.toLpLin_mul_same]
    rfl
  rw [hcomp]
  calc ‖Matrix.toEuclideanLin (A * Cᵀ) (T z)‖ ≤ ‖A * Cᵀ‖ * ‖T z‖ := norm_toEuclideanLin_le _ _
    _ ≤ (‖A‖ * ‖C‖) * ‖T z‖ := by
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have := LeanDLRA.Frobenius.norm_mul_le A Cᵀ
      rwa [LeanDLRA.Frobenius.norm_transpose] at this
    _ = (Matrix.toEuclideanLin S).singularValues (r - 1) * ‖C‖ * ‖A‖ := by rw [hTz]; ring

/-- **Remark 1, the correction function does not grow** (arXiv 1807.02338).  Let `K = X S` with
invertible `S`, and let `[α; β]` have independent rows.  The row-wise minimum-norm `C` solves the
K-ansatz system `S C Aᵀ = R`, it has the smallest Euclidean norm among all solutions, and
`∑_k C_kj K_k = ∑_i λ_ij X_i` with `λ` the minimum-norm solution of (3.8).  So at `K = X S` the
coefficients blow up (`kAnsatz_blowup`) but the correction function is the same as for the
`X`-ansatz: the remark's inference "this implies that the correction overall becomes quite large"
fails at this point.  Only the coefficients are large. -/
theorem kAnsatz_same_correction {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι (Fin r) ℝ} (hA : LinearIndependent ℝ A.row) {S : Matrix (Fin r) (Fin r) ℝ}
    (hS : IsUnit S.det) (R : Matrix (Fin r) ι ℝ) :
    let C : Matrix (Fin r) (Fin r) ℝ := Matrix.of fun k => minNormSol A ((S⁻¹ * R) k)
    S * C * Aᵀ = R ∧
      (∀ C' : Matrix (Fin r) (Fin r) ℝ, S * C' * Aᵀ = R →
        ∑ k, ∑ j, C k j ^ 2 ≤ ∑ k, ∑ j, C' k j ^ 2) ∧
      ∀ j x, ∑ k, C k j * coreK X S k x = ∑ i, minNormSol A (R i) j * X i x := by
  intro C
  have hsol : ∀ b : ι → ℝ, ∀ j, minNormSol A b j = ∑ m, (Aᵀ * (A * Aᵀ)⁻¹) j m * b m :=
    fun b j => by
    simp only [minNormSol, Matrix.mulVec_mulVec]
    rfl
  have hC : C = S⁻¹ * R * (Aᵀ * (A * Aᵀ)⁻¹)ᵀ := by
    ext k j
    rw [Matrix.mul_apply]
    simp only [C, Matrix.of_apply, hsol, Matrix.transpose_apply]
    exact sum_congr rfl fun m _ => mul_comm _ _
  have hSC : S * C = R * (Aᵀ * (A * Aᵀ)⁻¹)ᵀ := by
    rw [hC, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hS, Matrix.one_mul]
  refine ⟨?_, fun C' hC' => ?_, fun j x => ?_⟩
  · have h1 : (Aᵀ * (A * Aᵀ)⁻¹)ᵀ * Aᵀ = 1 := by
      have h2 : (A * Aᵀ)⁻¹ᵀ * (A * Aᵀ)ᵀ = 1 := by
        rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ (isUnit_det_mul_transpose hA),
          Matrix.transpose_one]
      simpa [Matrix.transpose_mul, Matrix.mul_assoc] using h2
    rw [hSC, Matrix.mul_assoc, h1, Matrix.mul_one]
  · have h1 : C' * Aᵀ = S⁻¹ * R := by
      rw [← hC', ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hS,
        Matrix.one_mul]
    refine minNormSol_rows_le hA (fun k => (S⁻¹ * R) k) (fun k => C' k) fun k => ?_
    funext m
    have h2 := congrFun (congrFun h1 k) m
    rw [Matrix.mul_apply] at h2
    simp only [Matrix.mulVec, dotProduct]
    rw [← h2]
    exact sum_congr rfl fun j _ => by rw [Matrix.transpose_apply]; exact mul_comm _ _
  · have h3 : ∀ i, minNormSol A (R i) j = (S * C) i j := fun i => by
      rw [hSC, hsol, Matrix.mul_apply]
      exact sum_congr rfl fun m _ => by rw [Matrix.transpose_apply]; exact mul_comm _ _
    simp only [h3]
    exact sum_mul_coreK S (fun k => C k j) x

/-! ### Remark 2: a general velocity correction -/

/-- **Remark 2, the minimal correction** (arXiv 1807.02338).  On a finite measure space `(Ω_v, ν)`
the `L²`-minimal `R` with `∫ R dv = c` is the constant `c / |Ω_v|`, and it is unique up to null
sets.  In the paper `c = -⟨X_i, F(f)⟩ₓᵥ - ⟨X_i, ∇·(ρu)⟩ₓ`.  (By `rhsL_lowRank_eq_zero` that `c`
vanishes for the exact L-step without boundary terms, so the remark is about the case where it does
not, such as after a space discretization.) -/
theorem minimal_velocity_correction {α : Type*} [MeasurableSpace α] (ν₀ : Measure α)
    [IsFiniteMeasure ν₀] [NeZero ν₀] (c : ℝ) :
    ∫ _v, c / ν₀.real univ ∂ν₀ = c ∧
      ∀ R₀ : α → ℝ, MemLp R₀ 2 ν₀ → ∫ v, R₀ v ∂ν₀ = c →
        ∫ _v, (c / ν₀.real univ) ^ 2 ∂ν₀ ≤ ∫ v, R₀ v ^ 2 ∂ν₀ ∧
        (∫ v, R₀ v ^ 2 ∂ν₀ = ∫ _v, (c / ν₀.real univ) ^ 2 ∂ν₀ →
          R₀ =ᵐ[ν₀] fun _ => c / ν₀.real univ) := by
  have hw : 0 < ν₀.real univ := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr (NeZero.ne ν₀))
      (measure_ne_top _ _)
  set w := ν₀.real univ with hwdef
  set κ := c / w with hκ
  have hκw : w * κ = c := by rw [hκ]; field_simp
  refine ⟨by rw [integral_const, smul_eq_mul, hκw], fun R₀ hR hint => ?_⟩
  have hR₁ : Integrable R₀ ν₀ := hR.integrable one_le_two
  have hR₂ : Integrable (fun v => R₀ v ^ 2) ν₀ := hR.integrable_sq
  have hconst : ∫ _v, κ ^ 2 ∂ν₀ = κ * c := by
    rw [integral_const, smul_eq_mul, ← hκw]
    ring
  have hexp : ∫ v, (R₀ v - κ) ^ 2 ∂ν₀ = ∫ v, R₀ v ^ 2 ∂ν₀ - κ * c := by
    have e : ∀ v, (R₀ v - κ) ^ 2 = R₀ v ^ 2 - 2 * κ * R₀ v + κ ^ 2 := fun v => by ring
    simp_rw [e]
    have i1 : Integrable (fun v => R₀ v ^ 2 - 2 * κ * R₀ v) ν₀ := hR₂.sub (hR₁.const_mul _)
    rw [integral_add i1 (integrable_const _), integral_sub hR₂ (hR₁.const_mul _),
      integral_const_mul, hint, hconst]
    ring
  have hnn : 0 ≤ ∫ v, (R₀ v - κ) ^ 2 ∂ν₀ := integral_nonneg fun v => sq_nonneg _
  rw [hconst]
  refine ⟨by linarith, fun heq => ?_⟩
  have h0 : ∫ v, (R₀ v - κ) ^ 2 ∂ν₀ = 0 := by linarith
  have hint' : Integrable (fun v => (R₀ v - κ) ^ 2) ν₀ := by
    have e : (fun v => (R₀ v - κ) ^ 2) = fun v => R₀ v ^ 2 - 2 * κ * R₀ v + κ ^ 2 := by
      funext v
      ring
    rw [e]
    have i1 : Integrable (fun v => R₀ v ^ 2 - 2 * κ * R₀ v) ν₀ := hR₂.sub (hR₁.const_mul _)
    exact i1.add (integrable_const _)
  have h1 := (integral_eq_zero_iff_of_nonneg (fun v => sq_nonneg (R₀ v - κ)) hint').mp h0
  filter_upwards [h1] with v hv
  have : (R₀ v - κ) ^ 2 = 0 := hv
  have := pow_eq_zero_iff (two_ne_zero) |>.mp this
  linarith

/-- **Remark 2, spurious mass** (arXiv 1807.02338).  For `c ≠ 0` the minimal correction does not
vanish at any velocity, and it does not tend to zero along any filter (for instance at large
velocities). -/
theorem minimal_correction_spurious {α : Type*} {l : Filter α} [l.NeBot] {κ : ℝ} (hκ : κ ≠ 0) :
    ¬ Tendsto (fun _ : α => κ) l (𝓝 0) := by
  rw [tendsto_const_nhds_iff]
  exact hκ

/-- **Remark 2, closure** (arXiv 1807.02338): "any property of the `V⁰_j` that is invariant under
taking linear combinations is preserved by our approach". -/
theorem ansatz_mem_submodule {β : Type*} (P : Submodule ℝ (β → ℝ)) {W : Fin r → β → ℝ}
    (hW : ∀ j, W j ∈ P) (lam : Fin r → ℝ) : (fun v => ∑ j, lam j * W j v) ∈ P := by
  have e : (fun v => ∑ j, lam j * W j v) = ∑ j, lam j • W j := by
    funext v
    simp
  rw [e]
  exact Submodule.sum_mem _ fun j _ => P.smul_mem _ (hW j)

/-- **Remark 2, decay** (arXiv 1807.02338): the ansatz inherits the decay of the `V_j`, in contrast
to the minimal correction (`minimal_correction_spurious`). -/
theorem ansatz_tendsto_zero {β : Type*} {l : Filter β} {W : Fin r → β → ℝ}
    (hW : ∀ j, Tendsto (W j) l (𝓝 0)) (lam : Fin r → ℝ) :
    Tendsto (fun v => ∑ j, lam j * W j v) l (𝓝 0) := by
  have h := tendsto_finsetSum Finset.univ fun j (_ : j ∈ Finset.univ) => (hW j).const_mul (lam j)
  simpa using h

/-- **(3.8), `r ≥ 1 + d`** (arXiv 1807.02338): independent rows of `[α; β]` force `r ≥ 1 + d`, as
the paper supposes. -/
theorem one_add_le_of_rows (h : LinearIndependent ℝ (momentMatrix ν V).row) : 1 + d ≤ r := by
  have := card_le_of_rows h
  simpa [add_comm] using this

end Laws

/-! ### Instances: the hypotheses can hold -/

section Instances

/-- The unit vector of `ℝ¹`. -/
noncomputable def e₁ : PS 1 := EuclideanSpace.single 0 1

/-- Two points `±1`, a quadrature rule in `v` (and in `x`). -/
noncomputable def twoPoint : Measure (PS 1) := Measure.dirac (-e₁) + Measure.dirac e₁

/-- `1/√2` and `v/√2`, orthonormal for `twoPoint`, with `1, v` in their span. -/
noncomputable def twoBasis : Fin 2 → PS 1 → ℝ := ![fun _ => 1 / √2, fun v => v 0 / √2]

lemma integrable_twoPoint (f : PS 1 → ℝ) : Integrable f twoPoint :=
  (integrable_dirac (by simp)).add_measure (integrable_dirac (by simp))

lemma integral_twoPoint (f : PS 1 → ℝ) : ∫ v, f v ∂twoPoint = f (-e₁) + f e₁ := by
  rw [twoPoint, integral_add_measure (integrable_dirac (by simp)) (integrable_dirac (by simp)),
    integral_dirac, integral_dirac]

lemma e₁_apply : e₁ 0 = 1 := by simp [e₁]

private lemma sqrt_two_mul : (1 / √2 : ℝ) * (1 / √2) = 1 / 2 := by
  have h : √2 * √2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
  rw [div_mul_div_comm, h, one_mul]

lemma isOrthonormalL2_twoBasis : IsOrthonormalL2 twoPoint twoBasis where
  memLp i := (memLp_two_iff_integrable_sq (integrable_twoPoint _).aestronglyMeasurable).2
    (integrable_twoPoint _)
  inner_eq i k := by
    have h := sqrt_two_mul
    rw [integral_twoPoint]
    fin_cases i <;> fin_cases k <;>
      simp [twoBasis, e₁_apply, div_eq_mul_inv] at h ⊢ <;> nlinarith [h]

lemma twoBasis_moment_none_zero : momentMatrix twoPoint twoBasis none 0 = √2 := by
  have h : √2 * √2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
  have hne : (√2 : ℝ) ≠ 0 := by positivity
  simp only [momentMatrix, Matrix.of_apply, integral_twoPoint]
  simp [twoBasis]
  field_simp
  linarith

lemma twoBasis_moment_none_one : momentMatrix twoPoint twoBasis none 1 = 0 := by
  simp only [momentMatrix, Matrix.of_apply, integral_twoPoint]
  simp [twoBasis, e₁_apply]
  ring

lemma twoBasis_moment_some_zero : momentMatrix twoPoint twoBasis (some 0) 0 = 0 := by
  simp only [momentMatrix, Matrix.of_apply, integral_twoPoint]
  simp [twoBasis, e₁_apply]

lemma twoBasis_moment_some_one : momentMatrix twoPoint twoBasis (some 0) 1 = √2 := by
  have h : √2 * √2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
  have hne : (√2 : ℝ) ≠ 0 := by positivity
  simp only [momentMatrix, Matrix.of_apply, integral_twoPoint]
  simp [twoBasis, e₁_apply]
  field_simp
  linarith

/-- The rows of `[α; β]` are independent for `d = 1`, `r = 2 = 1 + d`. -/
lemma rows_twoBasis : LinearIndependent ℝ (momentMatrix twoPoint twoBasis).row := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hne : (√2 : ℝ) ≠ 0 := by positivity
  have h0 := congrFun hg 0
  have h1 := congrFun hg 1
  simp only [Fintype.sum_option, Fin.sum_univ_one, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.row, twoBasis_moment_none_zero, twoBasis_moment_none_one,
    twoBasis_moment_some_zero, twoBasis_moment_some_one, Pi.zero_apply, mul_zero, add_zero,
    zero_add, mul_eq_zero, hne, or_false] at h0 h1
  intro m
  cases m with
  | none => exact h0
  | some a =>
    rw [Fin.fin_one_eq_zero a]
    exact h1

/-- The core `S` with first row `c` and second row `0`: then `f = ∑ X_k S_kl V_l` does not depend
on `x`, since `X_0` is constant. -/
def steadyCore (c : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of ![c, 0]

lemma coreK_steady (c : Fin 2 → ℝ) (l : Fin 2) (x : PS 1) :
    coreK twoBasis (steadyCore c) l x = 1 / √2 * c l := by
  simp [coreK, steadyCore, Fin.sum_univ_two, twoBasis]

/-- A function of `v` alone has no flux when `E = 0`. -/
lemma flux_zero_of_indep {d : ℕ} {ν : Measure (PS d)} {f : PS d → PS d → ℝ} {h : PS d → ℝ}
    (hf : ∀ x v, f x v = h v) (m : Option (Fin d)) (x : PS d) : flux ν 0 f m x = 0 := by
  have h1 : ∀ a, momentum ν f a = fun _ => ∫ v, v a * h v ∂ν := fun a => by
    funext y
    simp only [momentum, hf]
  have h2 : ∀ a b, stress ν f a b = fun _ => ∫ v, v a * v b * h v ∂ν := fun a b => by
    funext y
    simp only [stress, hf]
  cases m with
  | none => simp [flux, divMomentum, pd, h1]
  | some a => simp [flux, divStress, pd, h2]

/-- A function of `v` alone is left alone by `F` when `E = 0`. -/
lemma vlasovF_zero_of_indep {d : ℕ} {f : PS d → PS d → ℝ} {h : PS d → ℝ}
    (hf : ∀ x v, f x v = h v) (x v : PS d) : vlasovF 0 f x v = 0 := by
  have h1 : (fun y => f y v) = fun _ => h v := funext fun y => hf y v
  simp [vlasovF, h1]

/-- Non-vacuity of `kStep_quasiConservative`: all its hypotheses hold for `d = 1`, `r = 2`, a
two-point velocity rule and a steady state. -/
example (c : Fin 2 → ℝ) (t : ℝ) :
    ProjectedLaws twoPoint twoPoint twoBasis 0
      (fun _ => lowRank (coreK twoBasis (steadyCore c)) twoBasis) t := by
  have hf : ∀ x v, lowRank (coreK twoBasis (steadyCore c)) twoBasis x v =
      ∑ j, 1 / √2 * c j * twoBasis j v := fun x v => by
    simp only [lowRank, coreK_steady]
  refine kStep_quasiConservative (V := twoBasis) (lam := 0) isOrthonormalL2_twoBasis
    (fun m j => integrable_twoPoint _) rows_twoBasis (fun i => ?_) (fun j x => ?_)
    (fun i j => integrable_twoPoint _) (fun i m => integrable_twoPoint _)
  · have hrhs : (fun m => rhsKS twoPoint twoPoint twoBasis twoBasis ((0 : ℝ → PS 1 → PS 1) t)
        (lowRank (coreK twoBasis (steadyCore c)) twoBasis) m i) = 0 := by
      funext m
      simp [rhsKS, innerXV, vlasovF_zero_of_indep hf, flux_zero_of_indep hf]
    rw [hrhs, minNormSol_zero]
    rfl
  · simpa [vlasovF_zero_of_indep hf] using hasDerivAt_const t _

/-- Non-vacuity of `sStep_quasiConservative`, for the same data. -/
example (c : Fin 2 → ℝ) (t : ℝ) :
    ProjectedLawsBackward twoPoint twoPoint twoBasis 0
      (fun _ => lowRank (coreK twoBasis (steadyCore c)) twoBasis) t := by
  have hf : ∀ x v, lowRank (coreK twoBasis (steadyCore c)) twoBasis x v =
      ∑ j, 1 / √2 * c j * twoBasis j v := fun x v => by
    simp only [lowRank, coreK_steady]
  refine sStep_quasiConservative (V := twoBasis) (lam := 0) (S := fun _ => steadyCore c)
    isOrthonormalL2_twoBasis (fun m j => integrable_twoPoint _) rows_twoBasis (fun i => ?_)
    (fun i j => ?_) (fun i m => integrable_twoPoint _)
  · have hrhs : (fun m => rhsKS twoPoint twoPoint twoBasis twoBasis ((0 : ℝ → PS 1 → PS 1) t)
        (lowRank (coreK twoBasis (steadyCore c)) twoBasis) m i) = 0 := by
      funext m
      simp [rhsKS, innerXV, vlasovF_zero_of_indep hf, flux_zero_of_indep hf]
    rw [hrhs, minNormSol_zero]
    rfl
  · simpa [innerXV, vlasovF_zero_of_indep hf] using hasDerivAt_const t _

variable {d : ℕ} {ν : Measure (PS d)}

/-- The single basis function `X ≡ 1`. -/
abbrev oneX (d : ℕ) : Fin 1 → PS d → ℝ := fun _ _ => 1

/-- The constant unit field `e_a`. -/
noncomputable abbrev unitField (a : Fin d) : PS d → PS d := fun _ => EuclideanSpace.single a (1 : ℝ)

lemma continuous_pd {g : PS d → ℝ} (hg : ContDiff ℝ 2 g) (w : PS d) :
    Continuous fun v => fderiv ℝ g v w :=
  (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- Smooth functions of compact support are velocity profiles. -/
lemma isVelocityProfile_of_hasCompactSupport [ν.IsAddHaarMeasure] {g : PS d → ℝ}
    (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport g) : IsVelocityProfile ν g where
  differentiable := hg.differentiable (by norm_num)
  integrable := Continuous.integrable_of_hasCompactSupport (by
    have := hg.continuous
    fun_prop) hc.mul_left
  integrable_pd b := Continuous.integrable_of_hasCompactSupport (by
    have := continuous_pd hg (EuclideanSpace.single b 1)
    simp only [pd]
    fun_prop) (hc.fderiv_apply (𝕜 := ℝ) _).mul_left

lemma hasCompactSupport_translate {g : PS d → ℝ} (hc : HasCompactSupport g) (c : PS d) :
    HasCompactSupport fun v => g (v + c) :=
  hc.comp_homeomorph (Homeomorph.addRight c)

/-- The translating profile `g(v + s e)`: differentiating moments in time is justified. -/
lemma isDominatedCurve_translate [ν.IsAddHaarMeasure] {g : PS d → ℝ} (hg : ContDiff ℝ 2 g)
    (hc : HasCompactSupport g) (e : PS d) (t : ℝ) :
    IsDominatedCurve ν (fun s v => g (v + s • e)) (fun s v => fderiv ℝ g (v + s • e) e) t := by
  have hcont' : Continuous fun v => fderiv ℝ g v e := continuous_pd hg e
  have hcomp : HasCompactSupport fun v => fderiv ℝ g v e := hc.fderiv_apply (𝕜 := ℝ) e
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuous hcont'
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  obtain ⟨R, hR⟩ := hcomp.isCompact.isBounded.subset_closedBall (0 : PS d)
  refine ⟨Eventually.of_forall fun s => ?_, ?_, ?_⟩
  · have h1 : ContDiff ℝ 2 fun v => g (v + s • e) := hg.comp (contDiff_id.add contDiff_const)
    have h2 := hasCompactSupport_translate hc (s • e)
    exact Continuous.integrable_of_hasCompactSupport (by
      have := h1.continuous
      fun_prop) h2.mul_left
  · exact (hcont'.comp (continuous_id.add continuous_const)).aestronglyMeasurable
  · set R' := R + (|t| + 1) * ‖e‖ with hR'
    refine ⟨1, one_pos, (Metric.closedBall (0 : PS d) R').indicator fun _ => (1 + R') * C, ?_,
      ae_of_all _ fun v s hs => ⟨?_, ?_⟩⟩
    · rw [integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
      exact continuous_const.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
    · have h1 : HasDerivAt (fun τ : ℝ => v + τ • e) e s := by
        simpa using ((hasDerivAt_id s).smul_const e).const_add v
      exact ((hg.differentiable (by norm_num) (v + s • e)).hasFDerivAt).comp_hasDerivAt s h1
    · have hs' : |s| ≤ |t| + 1 := by
        have h1 : |s - t| < 1 := by simpa [Real.dist_eq] using hs
        have h2 : |s| ≤ |s - t| + |t| := by simpa using abs_add_le (s - t) t
        linarith
      have hse : ‖s • e‖ ≤ (|t| + 1) * ‖e‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right hs' (norm_nonneg _)
      by_cases hv : v ∈ Metric.closedBall (0 : PS d) R'
      · rw [Set.indicator_of_mem hv]
        have hv' : ‖v‖ ≤ R' := by simpa using hv
        have := hC (v + s • e)
        rw [Real.norm_eq_abs] at this
        exact mul_le_mul (by linarith) this (abs_nonneg _) (by linarith [norm_nonneg v])
      · rw [Set.indicator_of_notMem hv]
        have hv' : R' < ‖v‖ := by simpa using hv
        have hout : v + s • e ∉ tsupport fun v => fderiv ℝ g v e := fun hmem => by
          have h2 : ‖v + s • e‖ ≤ R := by simpa using hR hmem
          have h3 : ‖v‖ ≤ ‖v + s • e‖ + ‖s • e‖ := by
            simpa using norm_sub_le (v + s • e) (s • e)
          linarith
        rw [image_eq_zero_of_notMem_tsupport hout]
        simp

/-- The constant function `1` is orthonormal for a probability measure. -/
lemma isOrthonormalL2_one (μ : Measure (PS d)) [IsProbabilityMeasure μ] :
    IsOrthonormalL2 μ (oneX d) where
  memLp _ := memLp_const 1
  inner_eq i k := by simp [Subsingleton.elim i k]

lemma integrable_oneX (μ : Measure (PS d)) [IsProbabilityMeasure μ] (a b : Fin d) (i k : Fin 1) :
    Integrable (fun x : PS d => oneX d i x * (oneX d k x * unitField a x b)) μ := by
  have h : (fun x : PS d => oneX d i x * (oneX d k x * unitField a x b)) =
      fun _ => (1 : ℝ) * (1 * (EuclideanSpace.single a (1 : ℝ) : PS d) b) := rfl
  rw [h]
  exact integrable_const _

/-- **Step 3, a time-dependent instance** (arXiv 1807.02338, Sec. 3).  A translating profile
`φ(v + s e_a)` under the constant field `e_a` is an exact solution of the L-step (2.7) with `X ≡ 1`,
and of Vlasov's equation.  This shows that the hypotheses of `lStep_projectedLaws` hold for a
solution that really moves, and it is an independent check of the sign in the momentum balance: the
mass moves to lower velocities, so `∂ₜ(ρu) = -Eρ`. -/
theorem lStep_translate_laws (a : Fin d) (μ : Measure (PS d)) [IsProbabilityMeasure μ]
    [ν.IsAddHaarMeasure] {φ : PS d → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (t : ℝ) :
    ProjectedLaws μ ν (oneX d) (fun _ => unitField a)
      (fun s => lowRank (oneX d) fun _ v => φ (v + s • EuclideanSpace.single a (1 : ℝ))) t := by
  set e : PS d := EuclideanSpace.single a (1 : ℝ) with he
  have hF : ∀ (s : ℝ) (v : PS d),
      (∫ x, (1 : ℝ) * vlasovF (unitField a)
        (lowRank (oneX d) fun _ v => φ (v + s • e)) x v ∂μ) =
      fderiv ℝ φ (v + s • e) e := fun s v => by
    have h1 : (fun y => lowRank (oneX d) (fun _ v => φ (v + s • e)) y v) =
        fun _ => φ (v + s • e) := by
      funext y
      simp [lowRank]
    have h3 : ∀ x : PS d, vlasovF (unitField a)
        (lowRank (oneX d) fun _ v => φ (v + s • e)) x v = fderiv ℝ φ (v + s • e) e := fun x => by
      have h4 : (fun w => lowRank (oneX d) (fun _ v => φ (v + s • e)) x w) =
          fun w => φ (w + s • e) := by
        funext w
        simp [lowRank]
      simp only [vlasovF, h1, h4, fderiv_comp_add_right]
      simp [he]
    simp [h3]
  refine lStep_projectedLaws (isOrthonormalL2_one μ) (fun _ => differentiable_const _) ?_ ?_
    (fun _ => isVelocityProfile_of_hasCompactSupport
      (hφ.comp (contDiff_id.add contDiff_const)) (hasCompactSupport_translate hc _)) fun k => ?_
  · intro i a k
    simp [pd]
  · exact fun i b k => integrable_oneX μ a b i k
  · simp only [hF]
    exact isDominatedCurve_translate hφ hc e t

/-- **The printed (3.14) is false** (arXiv 1807.02338).  For `X ≡ 1`, a constant field `e_a` and any
nonzero bump `φ ≥ 0`, the correct right-hand side of (3.8) in Step 3 vanishes while the printed
`d_i` does not. -/
theorem printed_3_14_false (a : Fin d) (μ : Measure (PS d)) [IsProbabilityMeasure μ]
    [ν.IsAddHaarMeasure] {c : PS d} (φ : ContDiffBump c) :
    rhsL (ν := ν) μ (oneX d) (unitField a) (lowRank (oneX d) fun _ v => φ v) (some a) 0 = 0 ∧
      printedD μ ν (oneX d) (unitField a) (lowRank (oneX d) fun _ v => φ v) a 0 ≠ 0 := by
  have hL : ∀ _ : Fin 1, IsVelocityProfile ν (fun v => φ v) := fun _ =>
    isVelocityProfile_of_hasCompactSupport φ.contDiff φ.hasCompactSupport
  have hXd : ∀ k : Fin 1, Differentiable ℝ (oneX d k) := fun _ => differentiable_const _
  have hc : ∀ (a' : Fin d) (k : Fin 1), Integrable (fun x : PS d => oneX d 0 x *
      pd a' (oneX d k) x) μ := fun a' k => by simp [pd]
  have he : ∀ (b : Fin d) (k : Fin 1), Integrable (fun x : PS d => oneX d 0 x * (oneX d k x *
      unitField a x b)) μ := fun b k => integrable_oneX μ a b 0 k
  refine ⟨rhsL_lowRank_eq_zero hL hXd 0 hc he (some a), ?_⟩
  rw [printedD_eq hL hXd 0 a hc he]
  have hpos : 0 < ∫ v, φ v ∂ν := φ.integral_pos
  have hrho : ∀ x : PS d, rho ν (lowRank (oneX d) fun _ v => φ v) x = ∫ v, φ v ∂ν := fun x => by
    simp [rho, lowRank]
  simp [hrho, hpos.ne']

end Instances

/-! ### The ansatz, the moments and orthonormality in the core kinetic vocabulary -/

section KineticCore

variable {d r : ℕ}

/-- **The ansatz through the core**: the separated function `∑_j A_j(x) B_j(v)` is the core
`Kinetic.lowRankAnsatz` with the weight `1` and the identity as coefficient matrix. -/
theorem lowRank_eq_lowRankAnsatz (A B : Fin r → PS d → ℝ) :
    lowRank A B = Kinetic.lowRankAnsatz 1 A 1 B := by
  funext x v
  exact (Kinetic.lowRankAnsatz_one_one A B x v).symm

/-- The separated function with `r` terms has separation rank at most `r`. -/
theorem hasSepRankLE_lowRank (A B : Fin r → PS d → ℝ) : HasSepRankLE ℝ (lowRank A B) r :=
  ⟨A, B, fun _ _ => rfl⟩

/-- **The density through the core**: `rho` is the core `Kinetic.velocityMoment` with the function
`1`. -/
theorem rho_eq_velocityMoment (ν : Measure (PS d)) (f : PS d → PS d → ℝ) :
    rho ν f = Kinetic.velocityMoment ν 1 f := by
  funext x
  simp [rho, Kinetic.velocityMoment_apply]

/-- The component `a` of the momentum density is the core velocity moment with the function
`v ↦ v_a`. -/
theorem momentum_eq_velocityMoment (ν : Measure (PS d)) (f : PS d → PS d → ℝ) (a : Fin d) :
    momentum ν f a = Kinetic.velocityMoment ν (fun v => v a) f := rfl

/-- The component `(a, b)` of the momentum flux is the core velocity moment with the function
`v ↦ v_a v_b`. -/
theorem stress_eq_velocityMoment (ν : Measure (PS d)) (f : PS d → PS d → ℝ) (a b : Fin d) :
    stress ν f a b = Kinetic.velocityMoment ν (fun v => v a * v b) f := rfl

/-- The conserved moment with index `m` is the core velocity moment with the weight `wt m`. -/
theorem moment_eq_velocityMoment (ν : Measure (PS d)) (m : Option (Fin d))
    (f : PS d → PS d → ℝ) : moment ν m f = Kinetic.velocityMoment ν (wt m) f := rfl

/-- The entries `α_j`, `β_j` of the moment matrix are the core velocity moments of the function
`V_j`, read as a phase-space function that does not depend on `x`. -/
theorem momentMatrix_apply_eq_velocityMoment (ν : Measure (PS d)) (V : Fin r → PS d → ℝ)
    (m : Option (Fin d)) (j : Fin r) (x : PS d) :
    momentMatrix ν V m j = Kinetic.velocityMoment ν (wt m) (fun _ : PS d => V j) x := rfl

/-- **Orthonormality through the core**: `IsOrthonormalL2` of this file is the core
`Kinetic.IsOrthonormalWrt` for families indexed by `Fin r`. -/
theorem isOrthonormalL2_iff_isOrthonormalWrt {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (X : Fin r → α → ℝ) : IsOrthonormalL2 μ X ↔ Kinetic.IsOrthonormalWrt μ X :=
  ⟨fun h => ⟨h.memLp, h.inner_eq⟩, fun h => ⟨h.memLp, h.inner_eq⟩⟩

/-- The bridges at nonzero data: one term with `A = 2`, `B = 3` has the value `6`; for the Dirac
mass at the origin the density of `f = 2` is `2`; the constant `1` is orthonormal for the Dirac
mass. -/
example :
    lowRank (d := 1) (fun (_ : Fin 1) _ => 2) (fun _ _ => 3) 0 0 = 6 ∧
      rho (d := 1) (Measure.dirac 0) (fun _ _ => 2) 0 = 2 ∧
      IsOrthonormalL2 (Measure.dirac (0 : ℝ)) (fun (_ : Fin 1) (_ : ℝ) => (1 : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [lowRank_eq_lowRankAnsatz, Kinetic.lowRankAnsatz_one_one]
    norm_num
  · rw [rho_eq_velocityMoment, Kinetic.velocityMoment_apply]
    simp
  · rw [isOrthonormalL2_iff_isOrthonormalWrt]
    exact ⟨fun _ => memLp_const 1, fun i j => by simp [Subsingleton.elim i j]⟩

end KineticCore

end LeanDLRA.Literature.P1807_02338
