import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Tensor.TT.ProjectorSplitting

/-!
# Results of arXiv 2512.14950: Dynamical tensor-train approximation for kinetic equations

Wang–Hu evolve the velocity distribution of kinetic equations as a tensor train (three velocity
modes, one tensor train per spatial grid point) with a fully discrete projector-splitting
integrator. The general tensor-train statements are proved in the core (`Tensor/TT/`) for any
number of modes; this module records them against the paper and proves the paper-specific
statements of §4.

* §2, operation 1, Eq. (2.2) (scaling): `Tensor.tt_update_smul`, `Tensor.tt_update_self_smul`.
* §2, operation 2, Eq. (2.3) (sum, TT-rank `(r₁+s₁, r₂+s₂)`): `Tensor.rank_unfold_tt_add_le`.
* §2, operation 3, Eq. (2.4) (single varying core): `Tensor.tt_update_add`.
* §2, operation 4, Eq. (2.5) (elementwise inverse): `Tensor.tt_inv_rankOne`,
  `Tensor.tt_mul_tt_inv_rankOne`.
* §2, operation 5, Eq. (2.6) (Hadamard with rank one): `Tensor.tt_hadamard_rankOne`.
* §2, operation 6, Eq. (2.7) (sum of entries): `Tensor.sum_tt`.
* §2, operations 7–8, Eqs. (2.8)–(2.15) (orthonormalization): `Tensor.tt_gauge`.
* §3, Steps 1–5 (core and bond updates): `Tensor.IsTTKSLDiscreteStep.fwd_eq_tt`, `bwd_eq_ttBond`,
  `Tensor.tt_update_ttCoreCoeff`, `Tensor.ttBond_ttBondCoeff`, `Tensor.capture_of_qr`.
* §3 with forward Euler, Eqs. (4.8), (4.17), (4.24); "Lie–Trotter splitting" (§3.2):
  `Tensor.IsTTKSLDiscreteStep.euler_fwd`, `euler_bwd`, `euler_consistency`; `bgk_euler_consistency`.
* §4.1, exact BGK solution (4.6): `bgkHomog_solves`, `bgk_exact_hasDerivAt`.
* §4.1, conserved moments: `bgk_exact_inner_eq`.
* §4.1, Maxwellian (4.4) has TT-rank `(1, 1)`: `rank_unfold_gaussGrid_le_one`,
  `gaussGrid_eq_smul_tt` (`gaussTensor_hasTTRankLE` for three modes).
* §4.1, exact solution has TT-rank `(3, 3)`: `bgk_exact_rank_unfold_le_three`
  (`bgkHomog_hasTTRankLE_of_add` for three modes).
* §4.4, IMEX scheme (4.28), maps (4.31)–(4.32): `imex_step_iff`, `imex_step_eq`, `imex_backward_eq`.
* §4.4, moment equation (4.30): `imex_inner_eq`.

The statements are finite-dimensional: tensors on velocity grids with the Frobenius (Euclidean)
norm. The TT-rank of a tensor at a cut is the rank of the corresponding unfolding (Oseledets'
definition); the local three-index `HasTTRankLE` of the earlier formalization is the special
case of three modes and is kept for compatibility. `bgkHomog_hasTTRankLE` assumes a separable
initial value, which is stronger than the paper's sum of two Gaussians (4.5);
`bgkHomog_hasTTRankLE_of_add` and `bgk_exact_rank_unfold_le_three` cover the printed case.
`bgk_euler_consistency` proves the algebraic part of the first-order claim only (one sweep is
the Euler step of the tangent-projected equation up to `O(Δt²)`); the convergence orders seen in
Figures 1–3, the second-order Strang variant (§3.2), the cost estimates of §3.1, the analytic
solutions (4.14) and (4.21) of the heat and Fokker–Planck equations and the VAFP experiments of
§4.5 are not formalized. Core definitions used: `Tensor`, `Tensor.unfold`, `Tensor.tt`,
`Tensor.TTCores`, `Tensor.IsTTKSLDiscreteStep`, `Tensor.ttTangentProj`. Local definitions:
`unf1`, `unf2`, `HasTTRankLE`, `IsSeparable`, `bgkHomog`, `gaussTensor` (three-index arrays,
earlier formalization) and `gaussGrid` (a Gaussian on a grid, with the bridge
`gaussGrid_eq_smul_tt` to a rank-one tensor train).
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2512_14950

variable {m n p : ℕ}

/-- Bond-1 unfolding of a 3-index tensor: rows indexed by the first mode. -/
def unf1 (f : Fin m → Fin n → Fin p → ℝ) : Matrix (Fin m) (Fin n × Fin p) ℝ :=
  fun i jk => f i jk.1 jk.2

/-- Bond-2 unfolding of a 3-index tensor: columns indexed by the last mode. -/
def unf2 (f : Fin m → Fin n → Fin p → ℝ) : Matrix (Fin m × Fin n) (Fin p) ℝ :=
  fun ij k => f ij.1 ij.2 k

/-- TT-rank at most `(r₁, r₂)`: the two unfoldings have matrix rank at most `r₁`, `r₂`. -/
def HasTTRankLE (r₁ r₂ : ℕ) (f : Fin m → Fin n → Fin p → ℝ) : Prop :=
  (unf1 f).rank ≤ r₁ ∧ (unf2 f).rank ≤ r₂

/-- Separable (rank-one) tensor `f i j k = a i * b j * c k`. -/
def IsSeparable (f : Fin m → Fin n → Fin p → ℝ) : Prop :=
  ∃ (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin p → ℝ), ∀ i j k, f i j k = a i * b j * c k

/-- Matrix rank is subadditive. -/
lemma rank_add_le_mat {ι κ : Type*} [Fintype κ] {A B : Matrix ι κ ℝ} :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Scaling does not increase matrix rank. -/
lemma rank_smul_le_mat {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] (c : ℝ)
    (A : Matrix ι κ ℝ) : (c • A).rank ≤ A.rank := by
  have h : c • A = (c • (1 : Matrix ι ι ℝ)) * A := by
    rw [Matrix.smul_mul, Matrix.one_mul]
  rw [h]
  exact Matrix.rank_mul_le_right _ _

lemma unf1_add (f g : Fin m → Fin n → Fin p → ℝ) : unf1 (f + g) = unf1 f + unf1 g := by
  ext i jk; rfl

lemma unf2_add (f g : Fin m → Fin n → Fin p → ℝ) : unf2 (f + g) = unf2 f + unf2 g := by
  ext ij k; rfl

lemma unf1_smul (c : ℝ) (f : Fin m → Fin n → Fin p → ℝ) : unf1 (c • f) = c • unf1 f := by
  ext i jk; rfl

lemma unf2_smul (c : ℝ) (f : Fin m → Fin n → Fin p → ℝ) : unf2 (c • f) = c • unf2 f := by
  ext ij k; rfl

/-- A separable tensor has TT-rank `(1,1)`. -/
theorem separable_hasTTRankLE {f : Fin m → Fin n → Fin p → ℝ} (hf : IsSeparable f) :
    HasTTRankLE 1 1 f := by
  obtain ⟨a, b, c, h⟩ := hf
  constructor
  · have e : unf1 f = Matrix.vecMulVec a (fun jk : Fin n × Fin p => b jk.1 * c jk.2) := by
      ext i jk
      simp only [unf1, Matrix.vecMulVec_apply, h]
      ring
    rw [e]
    exact Matrix.rank_vecMulVec_le _ _
  · have e : unf2 f = Matrix.vecMulVec (fun ij : Fin m × Fin n => a ij.1 * b ij.2) c := by
      ext ij k
      simp only [unf2, Matrix.vecMulVec_apply, h]
    rw [e]
    exact Matrix.rank_vecMulVec_le _ _

/-- The exact homogeneous BGK solution `(1 − e^{−ηt}) M + e^{−ηt} f₀` (Sec. 4.1). -/
noncomputable def bgkHomog (η : ℝ) (M f₀ : Fin m → Fin n → Fin p → ℝ) (t : ℝ) :
    Fin m → Fin n → Fin p → ℝ :=
  (1 - Real.exp (-η * t)) • M + Real.exp (-η * t) • f₀

/-- The exact homogeneous BGK solution solves `∂ₜ f = η (M − f)` with `f(0) = f₀`, for a fixed
equilibrium `M` (Sec. 4.1). -/
theorem bgkHomog_solves (η : ℝ) (M f₀ : Fin m → Fin n → Fin p → ℝ) :
    bgkHomog η M f₀ 0 = f₀ ∧
      ∀ t : ℝ, HasDerivAt (bgkHomog η M f₀) (η • (M - bgkHomog η M f₀ t)) t := by
  refine ⟨?_, fun t => ?_⟩
  · simp [bgkHomog]
  · have hs : HasDerivAt (fun t : ℝ => 1 - Real.exp (-η * t))
        (-(Real.exp (-η * t) * (-η))) t := by
      have := ((hasDerivAt_id t).const_mul (-η)).exp.const_sub 1
      simpa using this
    have he : HasDerivAt (fun t : ℝ => Real.exp (-η * t)) (Real.exp (-η * t) * (-η)) t := by
      have := ((hasDerivAt_id t).const_mul (-η)).exp
      simpa using this
    have h1 := hs.smul_const M
    have h2 := he.smul_const f₀
    have key := h1.add h2
    unfold bgkHomog
    convert key using 1
    module

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Subadditivity for two rank-one sums: a combination of two rank-`≤ 1` matrices has rank `≤ 3`. -/
lemma rank_comb_le_three {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {A B : Matrix ι κ ℝ} (hA : A.rank ≤ 1) (hB : B.rank ≤ 1)
    (s e : ℝ) : (s • A + e • B).rank ≤ 3 := by
  have h1 := rank_add_le_mat (A := s • A) (B := e • B)
  have h2 := rank_smul_le_mat s A
  have h3 := rank_smul_le_mat e B
  omega

/-- Sec. 4.1, special case: the exact homogeneous BGK solution has TT-rank at most `(3,3)` for all
`t` when the equilibrium `M` and the initial data `f₀` are both separable. This hypothesis is
stronger than the paper's, whose `f₀` is a sum of two Gaussians (4.5); the printed case is
`bgkHomog_hasTTRankLE_of_add`. (Here the rank is even at most `2`.) -/
theorem bgkHomog_hasTTRankLE (η : ℝ) {M f₀ : Fin m → Fin n → Fin p → ℝ}
    (hM : IsSeparable M) (hf₀ : IsSeparable f₀) (t : ℝ) :
    HasTTRankLE 3 3 (bgkHomog η M f₀ t) := by
  obtain ⟨hM1, hM2⟩ := separable_hasTTRankLE hM
  obtain ⟨hf1, hf2⟩ := separable_hasTTRankLE hf₀
  have e1 : unf1 (bgkHomog η M f₀ t) =
      (1 - Real.exp (-η * t)) • unf1 M + Real.exp (-η * t) • unf1 f₀ := by
    rw [bgkHomog, unf1_add, unf1_smul, unf1_smul]
  have e2 : unf2 (bgkHomog η M f₀ t) =
      (1 - Real.exp (-η * t)) • unf2 M + Real.exp (-η * t) • unf2 f₀ := by
    rw [bgkHomog, unf2_add, unf2_smul, unf2_smul]
  refine ⟨?_, ?_⟩
  · rw [e1]
    exact rank_comb_le_three hM1 hf1 _ _
  · rw [e2]
    exact rank_comb_le_three hM2 hf2 _ _

/-- The isotropic Gaussian (Maxwellian shape) on a grid, as a tensor. The normalising constant
`(2π)^{-3/2}` is omitted; it scales the tensor and does not change TT-rank. -/
noncomputable def gaussTensor (x : Fin m → ℝ) (y : Fin n → ℝ) (z : Fin p → ℝ) :
    Fin m → Fin n → Fin p → ℝ :=
  fun i j k => Real.exp (-(x i ^ 2) / 2) * Real.exp (-(y j ^ 2) / 2) * Real.exp (-(z k ^ 2) / 2)

lemma gaussTensor_separable (x : Fin m → ℝ) (y : Fin n → ℝ) (z : Fin p → ℝ) :
    IsSeparable (gaussTensor x y z) :=
  ⟨fun i => Real.exp (-(x i ^ 2) / 2), fun j => Real.exp (-(y j ^ 2) / 2),
    fun k => Real.exp (-(z k ^ 2) / 2), fun _ _ _ => rfl⟩

/-- The Maxwellian-shaped Gaussian tensor has TT-rank `(1,1)` (Sec. 4.1). -/
theorem gaussTensor_hasTTRankLE (x : Fin m → ℝ) (y : Fin n → ℝ) (z : Fin p → ℝ) :
    HasTTRankLE 1 1 (gaussTensor x y z) :=
  separable_hasTTRankLE (gaussTensor_separable x y z)

/-- Non-vacuity: a Gaussian Maxwellian and a Gaussian initial datum satisfy the hypotheses of
`bgkHomog_hasTTRankLE`, with TT-rank at most `(3,3)` along the whole trajectory. -/
example (η : ℝ) (t : ℝ) (x : Fin 4 → ℝ) (y : Fin 4 → ℝ) (z : Fin 4 → ℝ) :
    HasTTRankLE 3 3 (bgkHomog η (gaussTensor x y z) (gaussTensor z x y) t) :=
  bgkHomog_hasTTRankLE η (gaussTensor_separable x y z) (gaussTensor_separable z x y) t

/-- Sec. 4.1, Eqs. (4.5)–(4.7): the exact homogeneous BGK solution has TT-rank at most `(3,3)`
for all `t` when the equilibrium `M` is separable and the initial value is a sum `f₁ + f₂` of two
separable tensors (the paper's sum of two Gaussians (4.5)), by operations 1 and 2 of §2. -/
theorem bgkHomog_hasTTRankLE_of_add (η : ℝ) {M f₁ f₂ : Fin m → Fin n → Fin p → ℝ}
    (hM : IsSeparable M) (h₁ : IsSeparable f₁) (h₂ : IsSeparable f₂) (t : ℝ) :
    HasTTRankLE 3 3 (bgkHomog η M (f₁ + f₂) t) := by
  obtain ⟨hM1, hM2⟩ := separable_hasTTRankLE hM
  obtain ⟨h11, h12⟩ := separable_hasTTRankLE h₁
  obtain ⟨h21, h22⟩ := separable_hasTTRankLE h₂
  set s := 1 - Real.exp (-η * t)
  set e := Real.exp (-η * t)
  have key : ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] {A B C : Matrix ι κ ℝ},
      A.rank ≤ 1 → B.rank ≤ 1 → C.rank ≤ 1 → (s • A + (e • B + e • C)).rank ≤ 3 := by
    intro ι κ _ _ _ A B C hA hB hC
    have h1 := rank_add_le_mat (A := s • A) (B := e • B + e • C)
    have h2 := rank_add_le_mat (A := e • B) (B := e • C)
    have h3 := rank_smul_le_mat s A
    have h4 := rank_smul_le_mat e B
    have h5 := rank_smul_le_mat e C
    omega
  refine ⟨?_, ?_⟩
  · rw [bgkHomog, smul_add, unf1_add, unf1_add, unf1_smul, unf1_smul, unf1_smul]
    exact key hM1 h11 h21
  · rw [bgkHomog, smul_add, unf2_add, unf2_add, unf2_smul, unf2_smul, unf2_smul]
    exact key hM2 h12 h22

/-! ### Tensors with any number of modes (core `Tensor` and unfoldings) -/

section Tensors

open LeanDLRA.Tensor

variable {d : ℕ} {ι : Fin d → Type*} [∀ i, Fintype (ι i)]

set_option linter.unusedFintypeInType false in
/-- Sec. 4.1, Eq. (4.6): the exact solution `f(t) = (1 - e^{-ηt}) M + e^{-ηt} f₀` of the spatially
homogeneous BGK equation `∂ₜ f = η (M - f)` with a fixed equilibrium `M`, for tensors with any
number of modes. -/
theorem bgk_exact_hasDerivAt (η : ℝ) (M f₀ : Tensor ι) (t : ℝ) :
    HasDerivAt (fun s => (1 - Real.exp (-η * s)) • M + Real.exp (-η * s) • f₀)
      (η • (M - ((1 - Real.exp (-η * t)) • M + Real.exp (-η * t) • f₀))) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-η * s)) (Real.exp (-η * t) * (-η)) t := by
    simpa using ((hasDerivAt_id t).const_mul (-η)).exp
  have hs : HasDerivAt (fun s : ℝ => 1 - Real.exp (-η * s)) (-(Real.exp (-η * t) * (-η))) t :=
    he.const_sub 1
  convert (hs.smul_const M).add (he.smul_const f₀) using 1
  module

/-- Sec. 4.1, "n, u and T remain constant in time, and so does the Maxwellian": if the
equilibrium `M` has the same moment `⟪φ, ·⟫` as the initial value (e.g. the discrete mass,
momentum and energy, `φ = 1, v, |v|²` times the cell volume), then so has the exact solution at
every time, so `M` stays the equilibrium of `f(t)`. -/
theorem bgk_exact_inner_eq (η t : ℝ) {M f₀ φ : Tensor ι} (hM : ⟪φ, M⟫ = ⟪φ, f₀⟫) :
    ⟪φ, (1 - Real.exp (-η * t)) • M + Real.exp (-η * t) • f₀⟫ = ⟪φ, f₀⟫ := by
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hM]
  ring

/-- A Gaussian `c exp(-∑ᵢ (vᵢ(xᵢ) - uᵢ)² / (2T))` on the grid with coordinates `vᵢ : ιᵢ → ℝ`
(the Maxwellian (4.2) with `c = n (2πT)^{-3/2}` for three velocity modes). -/
noncomputable def gaussGrid (v : ∀ i, ι i → ℝ) (c : ℝ) (u : Fin d → ℝ) (T : ℝ) : Tensor ι :=
  WithLp.toLp 2 fun x => c * Real.exp (-(∑ i, (v i (x i) - u i) ^ 2) / (2 * T))

omit [∀ i, Fintype (ι i)] in
/-- **The Maxwellian is a rank-one tensor train** (arXiv 2512.14950, Eq. (4.4)): the Gaussian on
a grid is `c` times the tensor train with one-element bonds and cores
`C_i(x_i) = exp(-(vᵢ(xᵢ) - uᵢ)² / (2T))` (bridge from `gaussGrid` to the core `Tensor.tt`). -/
theorem gaussGrid_eq_smul_tt (v : ∀ i, ι i → ℝ) (c : ℝ) (u : Fin d → ℝ) (T : ℝ) :
    gaussGrid v c u T = c • tt (β := fun _ => Unit)
      (fun i _ y _ => Real.exp (-(v i y - u i) ^ 2 / (2 * T))) := by
  ext x
  rw [PiLp.smul_apply, tt_rankOne, smul_eq_mul, gaussGrid, PiLp.toLp_apply, ← Real.exp_sum,
    ← Finset.sum_div, Finset.sum_neg_distrib]

/-- Scaling does not increase the rank of an unfolding. -/
lemma rank_unfold_smul_le (p : Fin d → Prop) [DecidablePred p] (c : ℝ)
    (X : Tensor ι) : (unfold p (c • X)).rank ≤ (unfold p X).rank := by
  rw [unfold_smul]
  classical
  exact rank_smul_le_mat c _

/-- **TT-rank `(1, 1)` of the Maxwellian** (arXiv 2512.14950, after Eq. (4.4)): every unfolding of
a Gaussian on a grid has rank at most one. -/
theorem rank_unfold_gaussGrid_le_one (v : ∀ i, ι i → ℝ) (c : ℝ) (u : Fin d → ℝ) (T : ℝ)
    {k : ℕ} (hk : k ≤ d) :
    (unfold (fun i : Fin d => i.val < k) (gaussGrid v c u T)).rank ≤ 1 := by
  rw [gaussGrid_eq_smul_tt]
  refine (rank_unfold_smul_le _ c _).trans ?_
  simpa using rank_unfold_tt_le (β := fun _ => Unit)
    (fun i _ y _ => Real.exp (-(v i y - u i) ^ 2 / (2 * T))) k hk

/-- **The exact BGK solution has TT-rank `(3, 3)`** (arXiv 2512.14950, §4.1, after Eq. (4.7)):
with a Gaussian equilibrium (4.2) and the sum of two Gaussians (4.5) as initial value, every
unfolding of the exact solution (4.6) has rank at most `3`, for every number of modes and at
every time. -/
theorem bgk_exact_rank_unfold_le_three (η t : ℝ) (v : ∀ i, ι i → ℝ) (c c₁ c₂ T T₁ T₂ : ℝ)
    (u u₁ u₂ : Fin d → ℝ) {k : ℕ} (hk : k ≤ d) :
    (unfold (fun i : Fin d => i.val < k) ((1 - Real.exp (-η * t)) • gaussGrid v c u T +
      Real.exp (-η * t) • (gaussGrid v c₁ u₁ T₁ + gaussGrid v c₂ u₂ T₂))).rank ≤ 3 := by
  have h0 := rank_unfold_gaussGrid_le_one v c u T hk
  have h1 := rank_unfold_gaussGrid_le_one v c₁ u₁ T₁ hk
  have h2 := rank_unfold_gaussGrid_le_one v c₂ u₂ T₂ hk
  have a := rank_unfold_add_le (fun i : Fin d => i.val < k)
    ((1 - Real.exp (-η * t)) • gaussGrid v c u T)
    (Real.exp (-η * t) • (gaussGrid v c₁ u₁ T₁ + gaussGrid v c₂ u₂ T₂))
  have b := rank_unfold_smul_le (fun i : Fin d => i.val < k) (1 - Real.exp (-η * t))
    (gaussGrid v c u T)
  have c' := rank_unfold_smul_le (fun i : Fin d => i.val < k) (Real.exp (-η * t))
    (gaussGrid v c₁ u₁ T₁ + gaussGrid v c₂ u₂ T₂)
  have e := rank_unfold_add_le (fun i : Fin d => i.val < k) (gaussGrid v c₁ u₁ T₁)
    (gaussGrid v c₂ u₂ T₂)
  omega

/-- **The first-order scheme for the homogeneous BGK equation is a Lie–Trotter splitting of the
projected Euler step** (arXiv 2512.14950, §3 with the forward Euler maps (4.8),
`G(f) = f + Δt η (M - f)`, `H(f) = f - Δt η (M - f)`): for one step of the fully discrete TT
projector-splitting scheme with `d ≥ 1` cores and `Δt ≥ 0`,
`‖f_{2d-1} - (f₀ + Δt P η (M - f₀))‖ ≤ |η| B Δt² (2d - 1)(d - 1)` with `P = ttTangentProj A B`
and `B` a bound of `‖η (M - f_j)‖` along the sweep. This is the algebraic part of the first-order
claim; the observed convergence order (Figure 1) is not formalized. -/
theorem bgk_euler_consistency {β : ℕ → Type*} [∀ k, Fintype (β k)] [∀ k, DecidableEq (β k)]
    [Unique (β 0)] [Subsingleton (β d)] {G H : ℕ → Tensor ι → Tensor ι} {A B : TTCores ι β}
    {Y : ℕ → Tensor ι} (hs : IsTTKSLDiscreteStep G H A B Y) {η Δt Bd : ℝ} {M : Tensor ι}
    (hG : ∀ k f, G k f = f + Δt • (η • (M - f))) (hH : ∀ k f, H k f = f - Δt • (η • (M - f)))
    (hB : ∀ j < 2 * d - 1, ‖η • (M - Y j)‖ ≤ Bd) (hΔt : 0 ≤ Δt) (hd : 0 < d) :
    ‖Y (2 * d - 1) - (Y 0 + Δt • ttTangentProj A B (η • (M - Y 0)))‖ ≤
      |η| * Bd * Δt ^ 2 * ((2 * d - 1) * (d - 1) : ℕ) :=
  hs.euler_consistency (F := fun f => η • (M - f)) hG hH
    (fun x y => by
      show ‖η • (M - x) - η • (M - y)‖ ≤ |η| * ‖x - y‖
      rw [← smul_sub, sub_sub_sub_cancel_left, norm_smul, Real.norm_eq_abs, norm_sub_rev])
    hB (abs_nonneg η) hΔt hd

omit [∀ i, Fintype (ι i)] in
/-- **The IMEX scheme** (arXiv 2512.14950, Eq. (4.28), multiplied by `Δt`):
`f' - f + Δt T f = Δt η (M - f')` with an explicit transport term `T f` (the upwind term
`v⁽¹⁾ D_x^{up} f` of (4.29)) holds iff `(1 + Δt η) f' = f - Δt T f + Δt η M`. -/
theorem imex_step_iff {f f' M Tf : Tensor ι} {η Δt : ℝ} :
    f' - f + Δt • Tf = Δt • (η • (M - f')) ↔
      (1 + Δt * η) • f' = f - Δt • Tf + (Δt * η) • M := by
  constructor <;> intro h
  · linear_combination (norm := module) h
  · linear_combination (norm := module) h

omit [∀ i, Fintype (ι i)] in
/-- **The forward IMEX map** (arXiv 2512.14950, Eq. (4.31)): for `1 + Δt η ≠ 0` the IMEX step is
`f' = (f - Δt T f + Δt η M) / (1 + Δt η)`. -/
theorem imex_step_eq {f f' M Tf : Tensor ι} {η Δt : ℝ} (hη : 1 + Δt * η ≠ 0)
    (h : f' - f + Δt • Tf = Δt • (η • (M - f'))) :
    f' = (1 + Δt * η)⁻¹ • (f - Δt • Tf + (Δt * η) • M) := by
  rw [← imex_step_iff.1 h, inv_smul_smul₀ hη]

omit [∀ i, Fintype (ι i)] in
/-- **The backward IMEX map** (arXiv 2512.14950, Eq. (4.32)) is the forward map with `-Δt`:
`(f + Δt T f - Δt η M) / (1 - Δt η)`. -/
theorem imex_backward_eq (f M Tf : Tensor ι) (η Δt : ℝ) :
    (1 - Δt * η)⁻¹ • (f + Δt • Tf - (Δt * η) • M) =
      (1 + -Δt * η)⁻¹ • (f - (-Δt) • Tf + (-Δt * η) • M) := by
  congr 1
  · ring
  · module

/-- **Moment equation of the IMEX scheme** (arXiv 2512.14950, Eq. (4.30)): if the BGK operator is
conservative for the moment `⟪φ, ·⟫` at the new time (`⟪φ, M⟫ = ⟪φ, f'⟫`), taking the moment of
the scheme (4.28) gives `⟪φ, f'⟫ - ⟪φ, f⟫ + Δt ⟪φ, T f⟫ = 0`. -/
theorem imex_inner_eq {f f' M Tf φ : Tensor ι} {η Δt : ℝ}
    (h : f' - f + Δt • Tf = Δt • (η • (M - f'))) (hM : ⟪φ, M⟫ = ⟪φ, f'⟫) :
    ⟪φ, f'⟫ - ⟪φ, f⟫ + Δt * ⟪φ, Tf⟫ = 0 := by
  have := congrArg (fun z => ⟪φ, z⟫) h
  simp only [inner_add_right, inner_sub_right, real_inner_smul_right, hM, sub_self,
    mul_zero] at this
  exact this

end Tensors

/-- Non-vacuity of `bgkHomog_hasTTRankLE_of_add`: a Gaussian equilibrium and a sum of two
Gaussians, as in (4.5). -/
example (η t : ℝ) (x y z : Fin 4 → ℝ) :
    HasTTRankLE 3 3 (bgkHomog η (gaussTensor x y z) (gaussTensor z x y + gaussTensor y z x) t) :=
  bgkHomog_hasTTRankLE_of_add η (gaussTensor_separable x y z) (gaussTensor_separable z x y)
    (gaussTensor_separable y z x) t

end LeanDLRA.Literature.P2512_14950
