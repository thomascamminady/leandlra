import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Stiff.ImplicitSolvability

/-!
# Results of arXiv 2308.05914: Semi-implicit DLR discontinuous Galerkin for emission/absorption

Abstract cores, on a real inner product space `E`, of results of Yin–Endeve–Hauck–Schnake
(arXiv 2308.05914), checked against the PDF.

* **Prop. 3.5 (i), weighted Galerkin = weighted minimal defect.**
  `weighted_galerkin_iff_minimizer`: for a symmetric positive semidefinite weight `W` (the
  paper's `A₁`-inner product `⟪W·,·⟫`), a subspace `T` (the tangent space `𝒯_F̂ M_r`) and a
  vector `g` (the paper's `G(F̂) A₁⁻¹`), a vector `v ∈ T` satisfies the Galerkin condition
  `⟪W (v - g), t⟫ = 0` for all `t ∈ T` (eq. (3.19a)) iff it minimizes `u ↦ ⟪W (u - g), u - g⟫`
  over `u ∈ T` (eq. (3.11)).
  Not formalized: Prop. 3.5 (ii) and (iii) (the factor equations of motion (3.20) and the
  coupled `K`, `L`, `S` system (3.21)), Cor. 3.2 (the DG scheme as a Galerkin problem), and
  Lemma 4.2 (equivalence of the substeps (4.4)–(4.7) with the DG scheme (4.12)).
* **Lemma 4.3, solvability of a DG substep.**  `dg_substep_existsUnique`: on a
  finite-dimensional space, for every `h > 0` and every `x₀`, the weak substep
  `x₁ ∈ K`, `⟪x₁ - x₀, w⟫ = h (⟪η, w⟫ - ⟪A x₁, w⟫)` for all `w ∈ K`, has exactly one solution.
  Here `A` is an abstract operator with the coercivity `μ ‖x‖² ≤ ⟪A x, x⟫`, which is the
  paper's Assumption 2.1 (`⟪χ f, f⟫ ≥ χ_min ‖f‖²`, `μ = χ_min`).  The lemma is the abstract
  core of Lemma 4.3 only; the paper's well-posedness of the matrix substeps is not formalized.
* **Lemma 4.4, L² stability.**  `dg_step_norm_le` is the one-step bound
  `(1 + h μ) ‖x₁‖ ≤ ‖x₀‖ + h ‖η‖` (eq. (4.19)).  `dg_stability` is the induction with
  `c = 1/(1 + h μ)`, giving `‖x_n‖ ≤ cⁿ ‖f₀‖ + (1 - cⁿ)/μ ‖η‖` (eq. (4.17)), under the
  paper's hypothesis `‖x₀‖ ≤ ‖f₀‖`.  The forcing `η` is kept.
  `dg_scheme_exists_stable` combines Lemmas 4.3 and 4.4: a sequence solving the scheme exists
  and satisfies the stability bound, so the hypotheses of `dg_stability` are not vacuous.

**Abstractions.**  The paper works in `L²(Ω, ε² dε)` with the matrix Galerkin structure of
Section 3.  The multiplication operator `A = χ(ε)` is replaced by an abstract `A : E →L[ℝ] E`
with the coercivity above.  The subspaces `K n` are abstract, and the finite-element structure
is not used.  The existence part of Lemma 4.3 uses finite dimension of `E` in place of
finite dimension of `V_h`.

**Core definitions reused.**  `IsOrthProj` (Foundations/Projector),
`existsUnique_linear_implicitGalerkin` (Stiff/ImplicitSolvability), and Mathlib's
`Submodule.starProjection`.  The module adds no new structures.

**Left out, with reasons.**  Lemmas 4.5–4.8 (equilibrium capture) and Theorem 4.10 (one-step
contraction) depend on the rank-one equilibrium of Section 4.3 and on the Appendix C
estimates, which are not formalized here.  Lemma 4.11 and Theorem 4.12 are in the sibling
slice `Lit2308_05914b`.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2308_05914

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Two real numbers `β`, `γ` with `γ ≥ 0` and `0 ≤ 2 s β + s² γ` for every `s` force `β = 0`. -/
lemma quad_nonneg_zero {β γ : ℝ} (hγ : 0 ≤ γ) (key : ∀ s : ℝ, 0 ≤ 2 * s * β + s ^ 2 * γ) :
    β = 0 := by
  have hne : γ + 1 ≠ 0 := by linarith
  have e : (γ + 1) ^ 2 * (2 * (-β / (γ + 1)) * β + (-β / (γ + 1)) ^ 2 * γ)
      = -(β ^ 2 * (γ + 2)) := by
    field_simp
    ring
  have h3 : 0 ≤ -(β ^ 2 * (γ + 2)) := by
    rw [← e]
    exact mul_nonneg (sq_nonneg _) (key _)
  have h4 : β ^ 2 ≤ 0 := by nlinarith [sq_nonneg β]
  have h5 : β ^ 2 = 0 := le_antisymm h4 (sq_nonneg β)
  exact (pow_eq_zero_iff two_ne_zero).mp h5

/-- **Prop. 3.5 (i), abstract core** (arXiv 2308.05914, eq. (3.19a) ⇔ eq. (3.11)).
Let `W` be a symmetric positive semidefinite operator (the weight `A₁`), `T` a subspace
(the tangent space `𝒯_F̂ M_r`), `g` the vector `G(F̂) A₁⁻¹`, and `v ∈ T`.  Then `v` satisfies the
weighted Galerkin condition `⟪W (v - g), t⟫ = 0` for all `t ∈ T` iff `v` minimizes
`u ↦ ⟪W (u - g), u - g⟫` over `u ∈ T`.  The paper's `(·,·)_{A₁}` is `⟪W ·, ·⟫`. -/
theorem weighted_galerkin_iff_minimizer {W : E →L[ℝ] E} (hWs : ∀ x y, ⟪W x, y⟫ = ⟪x, W y⟫)
    (hWp : ∀ x, 0 ≤ ⟪W x, x⟫) (T : Submodule ℝ E) (g v : E) (hv : v ∈ T) :
    (∀ t ∈ T, ⟪W (v - g), t⟫ = 0) ↔
      (∀ u ∈ T, ⟪W (v - g), v - g⟫ ≤ ⟪W (u - g), u - g⟫) := by
  have hsym : ∀ x y : E, ⟪W x, y⟫ = ⟪W y, x⟫ := fun x y => by rw [hWs, real_inner_comm]
  have expand : ∀ a b : E, ⟪W (a + b), a + b⟫ = ⟪W a, a⟫ + 2 * ⟪W a, b⟫ + ⟪W b, b⟫ := by
    intro a b
    rw [map_add]
    simp only [inner_add_left, inner_add_right]
    rw [hsym b a]
    ring
  have expS : ∀ (a b : E) (s : ℝ), ⟪W (a + s • b), a + s • b⟫
      = ⟪W a, a⟫ + 2 * s * ⟪W a, b⟫ + s ^ 2 * ⟪W b, b⟫ := by
    intro a b s
    rw [expand]
    simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
    ring
  constructor
  · intro hG u hu
    have hd : u - v ∈ T := T.sub_mem hu hv
    have hsplit : u - g = (v - g) + (u - v) := by abel
    rw [hsplit, expand, hG (u - v) hd]
    linarith [hWp (u - v)]
  · intro hmin t ht
    have key : ∀ s : ℝ, 0 ≤ 2 * s * ⟪W (v - g), t⟫ + s ^ 2 * ⟪W t, t⟫ := by
      intro s
      have hu : v + s • t ∈ T := T.add_mem hv (T.smul_mem s ht)
      have h1 := hmin _ hu
      rw [show v + s • t - g = (v - g) + s • t by abel, expS] at h1
      linarith
    exact quad_nonneg_zero (hWp t) key

/-- **Lemma 4.3, existence and uniqueness of a DG substep, abstract core** (arXiv 2308.05914,
Lemma 4.3).  Let `E` be finite-dimensional, `A` coercive with `μ ‖x‖² ≤ ⟪A x, x⟫` and `μ > 0`,
and `h > 0`.  For a subspace `K` and data `η`, `x₀`, the weak substep `x₁ ∈ K` with
`⟪x₁ - x₀, w⟫ = h (⟪η, w⟫ - ⟪A x₁, w⟫)` for all `w ∈ K` (the paper's
`(D_t f, w) = A(f, w)` with `A(f, w) = (η, w) - (χ f, w)`) has exactly one solution.
Proof: the weak form is the projected stage `x₁ = P (x₀ + h η - h A x₁)`, with `P` the
orthogonal projector onto `K`, which is uniquely solvable by
`existsUnique_linear_implicitGalerkin`. -/
theorem dg_substep_existsUnique [FiniteDimensional ℝ E] {A : E →L[ℝ] E} {μ h : ℝ}
    (hμ : 0 < μ) (hh : 0 < h) (hA : ∀ x, μ * ‖x‖ ^ 2 ≤ ⟪A x, x⟫) (K : Submodule ℝ E)
    (η x0 : E) :
    ∃! x1 : E, x1 ∈ K ∧ ∀ w ∈ K, ⟪x1 - x0, w⟫ = h * (⟪η, w⟫ - ⟪A x1, w⟫) := by
  have hP : IsOrthProj (K.starProjection : E →L[ℝ] E) :=
    ⟨fun x => Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem K x),
      fun x y => Submodule.inner_starProjection_left_eq_right K x y⟩
  have hPw : ∀ w ∈ K, (K.starProjection : E →L[ℝ] E) w = w :=
    fun w hw => Submodule.starProjection_eq_self_iff.mpr hw
  have hmem : ∀ x, (K.starProjection : E →L[ℝ] E) x ∈ K :=
    fun x => Submodule.starProjection_apply_mem K x
  have hzero : ∀ u : E, (K.starProjection : E →L[ℝ] E) u = 0 ↔ ∀ w ∈ K, ⟪u, w⟫ = 0 := by
    intro u
    constructor
    · intro hu w hw
      have : ⟪(K.starProjection : E →L[ℝ] E) u, w⟫ = ⟪u, w⟫ := by
        rw [hP.symm, hPw w hw]
      rw [← this, hu, inner_zero_left]
    · intro hu
      have h1 := hu _ (hmem u)
      have h2 : ⟪(K.starProjection : E →L[ℝ] E) u, (K.starProjection : E →L[ℝ] E) u⟫ = 0 := by
        rw [hP.symm, hP.idem]
        exact h1
      exact inner_self_eq_zero.mp h2
  have hu : ∀ (x1 w : E), ⟪x1 - (x0 + h • η + h • (-A) x1), w⟫
      = ⟪x1 - x0, w⟫ - h * (⟪η, w⟫ - ⟪A x1, w⟫) := by
    intro x1 w
    have e : x1 - (x0 + h • η + h • (-A) x1) = (x1 - x0) - h • (η - A x1) := by
      simp only [neg_apply, smul_neg, smul_sub]
      abel
    rw [e]
    simp only [inner_sub_left, real_inner_smul_left]
  have key : ∀ x1 : E, (x1 ∈ K ∧ ∀ w ∈ K, ⟪x1 - x0, w⟫ = h * (⟪η, w⟫ - ⟪A x1, w⟫)) ↔
      x1 = (K.starProjection : E →L[ℝ] E) (x0 + h • η + h • (-A) x1) := by
    intro x1
    constructor
    · rintro ⟨hx1, hw⟩
      have hPu : (K.starProjection : E →L[ℝ] E) (x1 - (x0 + h • η + h • (-A) x1)) = 0 := by
        rw [hzero]
        intro w hwK
        rw [hu x1 w, hw w hwK, sub_self]
      rw [map_sub, hPw x1 hx1] at hPu
      exact sub_eq_zero.mp hPu
    · intro hx1
      have hxK : x1 ∈ K := by rw [hx1]; exact hmem _
      refine ⟨hxK, fun w hwK => ?_⟩
      have hPu : (K.starProjection : E →L[ℝ] E) (x1 - (x0 + h • η + h • (-A) x1)) = 0 := by
        rw [map_sub, ← hx1, hPw x1 hxK, sub_self]
      have := (hzero _).mp hPu w hwK
      rw [hu x1 w] at this
      exact sub_eq_zero.mp this
  have hhα : h * (-μ) < 1 := by nlinarith [mul_pos hh hμ]
  have hT : ∀ x : E, (K.starProjection : E →L[ℝ] E) x = x → ⟪(-A) x, x⟫ ≤ (-μ) * ‖x‖ ^ 2 := by
    intro x _
    rw [neg_apply, inner_neg_left]
    linarith [hA x]
  obtain ⟨x1, hx1, huniq⟩ :=
    (existsUnique_linear_implicitGalerkin (P := (K.starProjection : E →L[ℝ] E)) (T := -A) hP
      hh.le hhα hT (x0 + h • η)).1
  exact ⟨x1, (key x1).2 hx1, fun y hy => huniq y ((key y).1 hy)⟩

/-- Algebraic identity behind the geometric sum: with `c (1 + h μ) = 1`,
`c (cⁿ F + (1 - cⁿ)/μ N + h N) = c^{n+1} F + (1 - c^{n+1})/μ N`. -/
lemma geom_identity (c μ h F N : ℝ) (hμ : μ ≠ 0) (hc : c * (1 + h * μ) = 1) (n : ℕ) :
    c * (c ^ n * F + (1 - c ^ n) / μ * N + h * N)
      = c ^ (n + 1) * F + (1 - c ^ (n + 1)) / μ * N := by
  have e : c * h * μ = 1 - c := by linear_combination hc
  have e2 : c * h * N = (1 - c) / μ * N := by
    rw [← e]
    field_simp
  rw [pow_succ]
  linear_combination e2

/-- **Lemma 4.4, one-step stability, abstract core** (arXiv 2308.05914, eqs. (4.18)–(4.19)).
If `x₁ ∈ K` solves the weak substep `⟪x₁ - x₀, w⟫ = h (⟪η, w⟫ - ⟪A x₁, w⟫)` for `w ∈ K`,
and `μ ‖x‖² ≤ ⟪A x, x⟫`, then `(1 + h μ) ‖x₁‖ ≤ ‖x₀‖ + h ‖η‖`. -/
theorem dg_step_norm_le {A : E →L[ℝ] E} {μ h : ℝ} (hh : 0 ≤ h)
    (hA : ∀ x, μ * ‖x‖ ^ 2 ≤ ⟪A x, x⟫) (K : Submodule ℝ E) {η xn xn1 : E}
    (hmem : xn1 ∈ K) (hweak : ∀ w ∈ K, ⟪xn1 - xn, w⟫ = h * (⟪η, w⟫ - ⟪A xn1, w⟫)) :
    (1 + h * μ) * ‖xn1‖ ≤ ‖xn‖ + h * ‖η‖ := by
  have h1 := hweak xn1 hmem
  have e1 : ⟪xn1 - xn, xn1⟫ = ‖xn1‖ ^ 2 - ⟪xn, xn1⟫ := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq]
  have h1' : ‖xn1‖ ^ 2 - ⟪xn, xn1⟫ = h * ⟪η, xn1⟫ - h * ⟪A xn1, xn1⟫ := by
    rw [← e1, h1]
    ring
  have hx : ⟪xn, xn1⟫ ≤ ‖xn‖ * ‖xn1‖ := real_inner_le_norm _ _
  have he : ⟪η, xn1⟫ ≤ ‖η‖ * ‖xn1‖ := real_inner_le_norm _ _
  have hA1 : h * (μ * ‖xn1‖ ^ 2) ≤ h * ⟪A xn1, xn1⟫ := mul_le_mul_of_nonneg_left (hA xn1) hh
  have he' : h * ⟪η, xn1⟫ ≤ h * (‖η‖ * ‖xn1‖) := mul_le_mul_of_nonneg_left he hh
  have hmain : (1 + h * μ) * ‖xn1‖ * ‖xn1‖ ≤ (‖xn‖ + h * ‖η‖) * ‖xn1‖ := by
    nlinarith [h1', hx, he', hA1]
  by_cases h0 : ‖xn1‖ = 0
  · rw [h0, mul_zero]
    have := mul_nonneg hh (norm_nonneg η)
    linarith [norm_nonneg xn]
  · have hpos : 0 < ‖xn1‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    exact le_of_mul_le_mul_right hmain hpos

/-- **Lemma 4.4, L² stability, abstract core** (arXiv 2308.05914, Lemma 4.4, eq. (4.17)).
Assume `μ ‖x‖² ≤ ⟪A x, x⟫` (the paper's Assumption 2.1, `μ = χ_min`), `h > 0` (`Δt`), and a
sequence `x` solving the weak DG scheme `⟪x_{n+1} - x_n, w⟫ = h (⟪η, w⟫ - ⟪A x_{n+1}, w⟫)`
for `w ∈ K n`, with `x_{n+1} ∈ K n` and `‖x₀‖ ≤ ‖f₀‖`.  Then, with `c = 1/(1 + h μ)`,
`‖x_n‖ ≤ cⁿ ‖f₀‖ + (1 - cⁿ)/μ ‖η‖` for all `n`. -/
theorem dg_stability {A : E →L[ℝ] E} {μ h : ℝ} (hμ : 0 < μ) (hh : 0 < h)
    (hA : ∀ x, μ * ‖x‖ ^ 2 ≤ ⟪A x, x⟫) (K : ℕ → Submodule ℝ E) {η f0 : E} (x : ℕ → E)
    (hx0 : ‖x 0‖ ≤ ‖f0‖) (hmem : ∀ n, x (n + 1) ∈ K n)
    (hweak : ∀ n, ∀ w ∈ K n, ⟪x (n + 1) - x n, w⟫ = h * (⟪η, w⟫ - ⟪A (x (n + 1)), w⟫)) :
    ∀ n : ℕ, ‖x n‖ ≤ (1 / (1 + h * μ)) ^ n * ‖f0‖ + (1 - (1 / (1 + h * μ)) ^ n) / μ * ‖η‖ := by
  have hpos1 : 0 < 1 + h * μ := by
    have := mul_pos hh hμ
    linarith
  have hc0 : 0 ≤ 1 / (1 + h * μ) := by positivity
  have hc : 1 / (1 + h * μ) * (1 + h * μ) = 1 := one_div_mul_cancel hpos1.ne'
  intro n
  induction n with
  | zero => simpa using hx0
  | succ n ih =>
    have hs := dg_step_norm_le hh.le hA (K n) (hmem n) (hweak n)
    calc ‖x (n + 1)‖ = 1 / (1 + h * μ) * ((1 + h * μ) * ‖x (n + 1)‖) := by
          rw [← mul_assoc, hc, one_mul]
      _ ≤ 1 / (1 + h * μ) * (‖x n‖ + h * ‖η‖) := mul_le_mul_of_nonneg_left hs hc0
      _ ≤ 1 / (1 + h * μ) * ((1 / (1 + h * μ)) ^ n * ‖f0‖
            + (1 - (1 / (1 + h * μ)) ^ n) / μ * ‖η‖ + h * ‖η‖) :=
          mul_le_mul_of_nonneg_left (by linarith [ih]) hc0
      _ = (1 / (1 + h * μ)) ^ (n + 1) * ‖f0‖
            + (1 - (1 / (1 + h * μ)) ^ (n + 1)) / μ * ‖η‖ :=
          geom_identity _ _ _ _ _ hμ.ne' hc n

/-- **Lemmas 4.3 and 4.4 combined, non-vacuity witness** (arXiv 2308.05914, Lemmas 4.3–4.4).
On a finite-dimensional space, the DG scheme with coercive `A`, `h > 0` and any subspaces `K n`
has a solution sequence starting at `f₀` that satisfies the stability bound of Lemma 4.4.  The
sequence is built by applying `dg_substep_existsUnique` at each step. -/
theorem dg_scheme_exists_stable [FiniteDimensional ℝ E] {A : E →L[ℝ] E} {μ h : ℝ}
    (hμ : 0 < μ) (hh : 0 < h) (hA : ∀ x, μ * ‖x‖ ^ 2 ≤ ⟪A x, x⟫) (K : ℕ → Submodule ℝ E)
    (η f0 : E) :
    ∃ x : ℕ → E, x 0 = f0 ∧ (∀ n, x (n + 1) ∈ K n) ∧
      (∀ n, ∀ w ∈ K n, ⟪x (n + 1) - x n, w⟫ = h * (⟪η, w⟫ - ⟪A (x (n + 1)), w⟫)) ∧
      ∀ n : ℕ, ‖x n‖ ≤ (1 / (1 + h * μ)) ^ n * ‖f0‖ + (1 - (1 / (1 + h * μ)) ^ n) / μ * ‖η‖ := by
  have hex : ∀ (n : ℕ) (y : E), ∃ z : E, z ∈ K n ∧
      ∀ w ∈ K n, ⟪z - y, w⟫ = h * (⟪η, w⟫ - ⟪A z, w⟫) :=
    fun n y => by
      obtain ⟨z, hz, _⟩ := dg_substep_existsUnique hμ hh hA (K n) η y
      exact ⟨z, hz⟩
  choose g hg using hex
  let x : ℕ → E := fun n => Nat.rec (motive := fun _ => E) f0 (fun k xk => g k xk) n
  have hx : ∀ n, x (n + 1) = g n (x n) := fun n => rfl
  have hx0 : x 0 = f0 := rfl
  have hmem : ∀ n, x (n + 1) ∈ K n := fun n => by rw [hx n]; exact (hg n (x n)).1
  have hweak : ∀ n, ∀ w ∈ K n, ⟪x (n + 1) - x n, w⟫ = h * (⟪η, w⟫ - ⟪A (x (n + 1)), w⟫) :=
    fun n w hw => by rw [hx n]; exact (hg n (x n)).2 w hw
  exact ⟨x, hx0, hmem, hweak, dg_stability hμ hh hA K x (by rw [hx0]) hmem hweak⟩

end LeanDLRA.Literature.P2308_05914
