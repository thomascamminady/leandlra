import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2111.14540: empirical Dirac–Frenkel projection (Sec. 6, eqs. (22)–(24))

**What is proved.** The empirical (sample-averaged) Dirac–Frenkel problem

  `Ȧ = argmin_{B ∈ T} (1/M) ∑_k |(B φ)(x_k) − F(t, Aφ)(x_k)|²`,

is a least-squares problem over a linear tangent space `T`. In the abstract core we take a
linear sampling map `s : E → ℝ^M` (`s B = (Bφ(x_k))_k`), a data vector `f ∈ ℝ^M` (the samples
of the right-hand side), and a subspace `T ⊆ E` (the tangent space). Then, for `M > 0`:

* `exists_empirical_minimizer`: a minimizer over `T` exists (`E` finite-dimensional);
* `empRisk_isMin_iff_normal`: `B ∈ T` is a minimizer iff the **normal equations**
  `∑_k (s B − f)_k (s C)_k = 0` hold for all `C ∈ T`, i.e. the residual is orthogonal to the
  sampled tangent space;
* `empirical_minimizer_image_unique`: any two minimizers have the same samples `s B`;
* `empirical_minimizer_unique`: if `s` is injective on `T` (definiteness of the sample
  semi-inner product on `T`, the hypothesis the paper needs for uniqueness), the minimizer is
  unique;
* `tangent_empirical_minimizer`: for a rank-`r` matrix `Y = U S Vᵀ` with orthonormal `U`, `V`,
  the minimizer over the matrix tangent space `{U B + C Vᵀ}` exists and is of this form.

The minimal-defect (continuous) Dirac–Frenkel property is not repeated here; it is already in
the library (`IsOrthProj.norm_apply_sub_le`, `IsOrthProj.diracFrenkel_tfae`).

Core definitions used: `tangentProj` and `mem_range_tangentProj` from `LeanDLRA.Matrix.Projectors`.
Local definitions added: `Samples` (abbreviation for `EuclideanSpace ℝ (Fin M)`) and `empRisk`.

**Differences from the paper.**
* The paper's objects are TT tensors. The TT tangent space (Thm. 4, Cor. 1) and the sampling
  `B ↦ (Bφ(x_k))_k` are not formalized, since the library has no TT infrastructure. The
  sampling map is an arbitrary linear map `s`, and the tangent space is an arbitrary subspace
  `T`; the matrix corollary instantiates `T` with the rank-`r` matrix tangent space, which is the
  `d = 2` analogue.
* The empirical risk is `(1/M) ∑_k (…)²`; the factor `1/M` (positive, since `M > 0`) does not
  change the minimizers, and `empRisk_eq_norm_sq` relates it to the Euclidean norm.
* Sampling points `x_k ~ ρ` and the Monte Carlo approximation error (Eq. (24) vs. the `L²`
  projection) are not formalized; the statement is purely algebraic in the samples.
* The time-dependent ODE (23) `Ȧ = argmin …` is not formalized: only the pointwise-in-time
  minimization problem is treated.
* The step-and-truncate explicit Euler scheme (Sec. 6, `A_{ℓ+1} = R(A_ℓ + τ ΔA_ℓ)`) is not
  formalized: the paper gives no error analysis for it, and the truncation `R` needs the TT-SVD.
* Theorem 5 (quasi-optimality, quoted from Lubich 2013) is not formalized: the paper quotes it
  without proof and its constant depends on TT curvature bounds that are not available here.
  The abstract comparison with curvature as a hypothesis lives in
  `LeanDLRA/Dynamics/ContinuousDLRA.lean` (`ODESolution.dlra_quasiOptimal`).
-/

open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2111_14540

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {M : ℕ}

/-- The sampled space `ℝ^M` (with the Euclidean inner product). -/
abbrev Samples (M : ℕ) : Type := EuclideanSpace ℝ (Fin M)

/-- The empirical risk `(1/M) ∑_k ((s B)_k − f_k)²` of the coefficient `B` against the sampled
data `f`, where `s` is the (linear) sampling map. -/
noncomputable def empRisk (s : E →ₗ[ℝ] Samples M) (f : Samples M) (B : E) : ℝ :=
  (1 / (M : ℝ)) * ∑ k, ((s B) k - f k) ^ 2

/-- The empirical risk is `(1/M)` times the squared Euclidean distance of the samples. -/
lemma empRisk_eq_norm_sq (s : E →ₗ[ℝ] Samples M) (f : Samples M) (B : E) :
    empRisk s f B = (1 / (M : ℝ)) * ‖s B - f‖ ^ 2 := by
  unfold empRisk
  rw [EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

/-- The Euclidean inner product of sampled vectors is the sum of the products of the entries. -/
lemma inner_samples_eq_sum (x y : Samples M) : ⟪x, y⟫ = ∑ k, x k * y k := by
  simp [PiLp.inner_apply, mul_comm]

/-- The sampled residual inner product written as a sum over the samples. -/
lemma sum_residual_eq_inner (s : E →ₗ[ℝ] Samples M) (f : Samples M) (B C : E) :
    ∑ k, ((s B) k - f k) * (s C) k = ⟪s B - f, s C⟫ := by
  rw [inner_samples_eq_sum]
  simp

lemma empRisk_le_iff (hM : 0 < M) (s : E →ₗ[ℝ] Samples M) (f : Samples M) (B C : E) :
    empRisk s f B ≤ empRisk s f C ↔ ‖s B - f‖ ^ 2 ≤ ‖s C - f‖ ^ 2 := by
  have hc : 0 < 1 / (M : ℝ) := by positivity
  rw [empRisk_eq_norm_sq, empRisk_eq_norm_sq]
  exact ⟨fun h => le_of_mul_le_mul_left h hc, fun h => mul_le_mul_of_nonneg_left h hc.le⟩

/-- **Normal equations for the empirical Dirac–Frenkel minimizer.** `B ∈ T` minimizes the
empirical risk over `T` iff the sampled residual `s B − f` is orthogonal to the sampled tangent
space `s(T)`, i.e. `∑_k (s B − f)_k (s C)_k = 0` for all `C ∈ T`. -/
theorem empRisk_isMin_iff_normal (hM : 0 < M) (s : E →ₗ[ℝ] Samples M) (f : Samples M)
    {T : Submodule ℝ E} {B : E} (hB : B ∈ T) :
    (∀ C ∈ T, empRisk s f B ≤ empRisk s f C) ↔
      ∀ C ∈ T, ∑ k, ((s B) k - f k) * (s C) k = 0 := by
  simp only [sum_residual_eq_inner]
  constructor
  · intro h C hC
    set a : ℝ := ⟪s B - f, s C⟫ with ha
    have key : ∀ t : ℝ, 0 ≤ 2 * t * a + t ^ 2 * ‖s C‖ ^ 2 := by
      intro t
      have hmem : B + t • C ∈ T := T.add_mem hB (T.smul_mem t hC)
      have h1 := (empRisk_le_iff hM s f B (B + t • C)).1 (h _ hmem)
      have hsplit : s (B + t • C) - f = (s B - f) + t • s C := by
        rw [map_add, map_smul]; abel
      rw [hsplit, norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
        sq_abs] at h1
      linarith
    set q : ℝ := ‖s C‖ ^ 2 with hqdef
    have hq : 0 ≤ q := by positivity
    have hq1 : 0 < q + 1 := by positivity
    have e : 2 * (-a / (q + 1)) * a + (-a / (q + 1)) ^ 2 * q
        = -(a ^ 2 * (q + 2)) / (q + 1) ^ 2 := by
      field_simp
      ring
    have h3 := key (-a / (q + 1))
    rw [e] at h3
    have h4 : 0 ≤ -(a ^ 2 * (q + 2)) := by
      have hY : 0 < (q + 1) ^ 2 := by positivity
      have := (le_div_iff₀ hY).1 (by simpa using h3)
      linarith
    have h5 : a ^ 2 = 0 := by nlinarith [sq_nonneg a]
    exact pow_eq_zero_iff two_ne_zero |>.1 h5
  · intro h C hC
    rw [empRisk_le_iff hM]
    have hC' : ⟪s B - f, s (C - B)⟫ = 0 := h (C - B) (T.sub_mem hC hB)
    have hsplit : s C - f = (s B - f) + s (C - B) := by
      rw [map_sub]; abel
    rw [hsplit, norm_add_sq_real, hC']
    nlinarith [sq_nonneg ‖s (C - B)‖]

/-- **Existence of the empirical Dirac–Frenkel minimizer.** Over a subspace `T` of a
finite-dimensional space, the empirical risk attains its minimum. -/
theorem exists_empirical_minimizer [FiniteDimensional ℝ E] (hM : 0 < M)
    (s : E →ₗ[ℝ] Samples M) (f : Samples M) (T : Submodule ℝ E) :
    ∃ B ∈ T, ∀ C ∈ T, empRisk s f B ≤ empRisk s f C := by
  set S : Submodule ℝ (Samples M) := T.map s with hS
  set p : Samples M := S.starProjection f with hp
  have hpS : p ∈ S := S.starProjection_apply_mem f
  obtain ⟨B, hBT, hBp⟩ := Submodule.mem_map.1 hpS
  refine ⟨B, hBT, ?_⟩
  rw [empRisk_isMin_iff_normal hM s f hBT]
  intro C hC
  have hCS : s C ∈ S := Submodule.mem_map_of_mem hC
  have hperp : f - p ∈ Sᗮ := S.sub_starProjection_mem_orthogonal f
  have h0 : ⟪s C, f - p⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hCS hperp
  have h1 : ⟪s B - f, s C⟫ = 0 := by
    rw [hBp]
    have : p - f = -(f - p) := by abel
    rw [this, inner_neg_left, real_inner_comm, h0, neg_zero]
  rw [sum_residual_eq_inner]
  exact h1

/-- **Uniqueness of the empirical minimizer's samples.** Any two minimizers `B₁`, `B₂` of the
empirical risk over `T` have the same samples, `s B₁ = s B₂`. -/
theorem empirical_minimizer_image_unique (hM : 0 < M) (s : E →ₗ[ℝ] Samples M) (f : Samples M)
    {T : Submodule ℝ E} {B₁ B₂ : E} (h₁ : B₁ ∈ T) (h₂ : B₂ ∈ T)
    (m₁ : ∀ C ∈ T, empRisk s f B₁ ≤ empRisk s f C) (m₂ : ∀ C ∈ T, empRisk s f B₂ ≤ empRisk s f C) :
    s B₁ = s B₂ := by
  have n₁ := (empRisk_isMin_iff_normal hM s f h₁).1 m₁ (B₁ - B₂) (T.sub_mem h₁ h₂)
  have n₂ := (empRisk_isMin_iff_normal hM s f h₂).1 m₂ (B₁ - B₂) (T.sub_mem h₁ h₂)
  rw [sum_residual_eq_inner, map_sub] at n₁ n₂
  have hd : ⟪s B₁ - s B₂, s B₁ - s B₂⟫ = 0 := by
    have e : s B₁ - s B₂ = (s B₁ - f) - (s B₂ - f) := by abel
    calc ⟪s B₁ - s B₂, s B₁ - s B₂⟫ = ⟪(s B₁ - f) - (s B₂ - f), s B₁ - s B₂⟫ := by rw [← e]
      _ = ⟪s B₁ - f, s B₁ - s B₂⟫ - ⟪s B₂ - f, s B₁ - s B₂⟫ := inner_sub_left _ _ _
      _ = 0 := by rw [n₁, n₂, sub_zero]
  exact sub_eq_zero.1 (inner_self_eq_zero.1 hd)

/-- **Uniqueness of the empirical Dirac–Frenkel velocity.** If the sampling map `s` is injective on
`T` (the sample semi-inner product is definite on the tangent space, the hypothesis the paper
needs for uniqueness of the minimizer in (24)), the empirical minimizer is unique. -/
theorem empirical_minimizer_unique (hM : 0 < M) (s : E →ₗ[ℝ] Samples M) (f : Samples M)
    {T : Submodule ℝ E} (hinj : ∀ C ∈ T, s C = 0 → C = 0) {B₁ B₂ : E} (h₁ : B₁ ∈ T)
    (h₂ : B₂ ∈ T) (m₁ : ∀ C ∈ T, empRisk s f B₁ ≤ empRisk s f C)
    (m₂ : ∀ C ∈ T, empRisk s f B₂ ≤ empRisk s f C) : B₁ = B₂ := by
  have hs := empirical_minimizer_image_unique hM s f h₁ h₂ m₁ m₂
  have h0 : s (B₁ - B₂) = 0 := by rw [map_sub, hs, sub_self]
  exact sub_eq_zero.1 (hinj _ (T.sub_mem h₁ h₂) h0)

/-- The injectivity hypothesis `hinj` of `empirical_minimizer_unique` is satisfiable: the identity
sampling map is injective on every subspace. -/
example : ∀ C ∈ (⊤ : Submodule ℝ (Samples M)), (LinearMap.id : Samples M →ₗ[ℝ] Samples M) C = 0 →
    C = 0 :=
  fun _ _ h => h

section Tangent

variable {m n k k' : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype k']
  [DecidableEq k] [DecidableEq k']

/-- **Empirical Dirac–Frenkel velocity on the rank-`r` matrix tangent space** (the `d = 2` case
of the TT tangent space of Thm. 4).  For `U`, `V` with orthonormal columns, the tangent space
`{U B + C Vᵀ}` of Koch–Lubich (`mem_range_tangentProj`) contains a minimizer of the empirical
risk, and that minimizer has the form `U B + C Vᵀ`. -/
theorem tangent_empirical_minimizer {U : Matrix m k ℝ} {V : Matrix n k' ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (hM : 0 < M) (s : Matrix m n ℝ →ₗ[ℝ] Samples M) (f : Samples M) :
    ∃ Y : Matrix m n ℝ, (∃ (B : Matrix k n ℝ) (C : Matrix m k' ℝ), Y = U * B + C * Vᵀ) ∧
      ∀ Z : Matrix m n ℝ, (∃ (B : Matrix k n ℝ) (C : Matrix m k' ℝ), Z = U * B + C * Vᵀ) →
        empRisk s f Y ≤ empRisk s f Z := by
  obtain ⟨Y, hY, hmin⟩ := exists_empirical_minimizer (E := Matrix m n ℝ) hM s f
    (LinearMap.range (tangentProj U V : Matrix m n ℝ →ₗ[ℝ] Matrix m n ℝ))
  exact ⟨Y, (mem_range_tangentProj hU hV Y).1 hY, fun Z hZ =>
    hmin Z ((mem_range_tangentProj hU hV Z).2 hZ)⟩

end Tangent

end LeanDLRA.Literature.P2111_14540
