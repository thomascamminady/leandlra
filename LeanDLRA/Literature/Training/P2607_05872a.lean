import LeanDLRA.Classical.SVD
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Orthonormal

/-!
# Results of arXiv 2607.05872: No subspace to track: non-identifiability in low-rank training

This module formalizes the theorems of N. Thomas, *No Subspace to Track* (`U_old`, `U_new` are
orthonormal frames, `R = U_newᵀ U_old`, except in Theorem 1, where `U' = U R`).  **Theorem 1** is
proved for the genuine Haar probability measure `haarO r` of the compact group `O(r)`
(`blind_estimator_lower_bound_haar`, and for every left-invariant probability measure in
`blind_estimator_mse`, `blind_estimator_lower_bound`, `blind_estimator_eq_floor_iff`, `carry_mse`,
`carry_mse_eq_factor_mul_floor`); its moments, eq. (6), are `haar_moment_two`, `haar_moment_four`,
`haar_moment_two_two`, derived from invariance under permutations and one reflection instead of the
Weingarten calculus and the `Beta` law, which are not formalized, and eq. (7) is `variance_vStar`.
**Proposition 3** is `mmse_transport_gaussian` for `g ∼ N(0, σ² 1)` and `mmse_transport` for any `g`
with `E[g gᵀ] = σ² 1`.  **Proposition 4** is `coverage_eq_spectral_mass`, as a quotient of
expectations.  **Eq. (2)** is `chordalDist_isLeast` (Procrustes form, from the SVD),
`chordalDist_mem_Icc` (the range), `chordalDist_eq_sqrt_iff` (maximal iff orthogonal),
`chordalDist_eq_zero_iff` and `chordalDist_mul_orthogonal`.  Three printed claims are false as
stated, and each counterexample is proved here: `E[γ_g]` in Proposition 4 and eq. (4) is not the
spectral mass (`expected_energyFraction_ne_spectral_mass`), only the quotient of expectations is;
`√(2r)` is not the maximum of the raw Frobenius distance of two frames, as Appendix A says
(`raw_distance_exceeds_ceiling`), only of the sign-corrected one; and the formula for `v*` in
Theorem 1 needs uncorrelated coordinates, which the paper does not state
(`vStar_requires_uncorrelated`, `newBasis_secondMoment`).  Not treated: the heuristic factor
`(r - k⋆) / 2` of Remark 2 and the representation-theoretic reading there, the expected raw distance
of Appendix A under random signs, and the empirical content of the paper.
-/

open Set Filter Topology Finset MeasureTheory
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2607_05872

/-! ### Second moments of a random vector -/

section SecondMoment

variable {Ω : Type*} [MeasurableSpace Ω] {m k : Type*} [Fintype m] [Fintype k]

/-- The second-moment matrix `Σ_g = E[g gᵀ]` of a random vector `g`. -/
noncomputable def secondMoment {l : Type*} (P : Measure Ω) (g : Ω → l → ℝ) : Matrix l l ℝ :=
  Matrix.of fun a b => ∫ ω, g ω a * g ω b ∂P

/-- All entries of `g gᵀ` are integrable, i.e. `g` has finite second moments. -/
def HasSecondMoments {l : Type*} (P : Measure Ω) (g : Ω → l → ℝ) : Prop :=
  ∀ a b, Integrable (fun ω => g ω a * g ω b) P

variable {P : Measure Ω} {g : Ω → m → ℝ}

private lemma dot_mul_dot (u v x : m → ℝ) :
    (u ⬝ᵥ x) * (v ⬝ᵥ x) = ∑ a, ∑ b, u a * v b * (x a * x b) := by
  simp only [dotProduct]
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

private lemma integrable_dot_mul_dot (hg : HasSecondMoments P g) (u v : m → ℝ) :
    Integrable (fun ω => (u ⬝ᵥ g ω) * (v ⬝ᵥ g ω)) P := by
  simp only [dot_mul_dot]
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    (hg a b).const_mul _

private lemma integral_dot_mul_dot (hg : HasSecondMoments P g) (u v : m → ℝ) :
    ∫ ω, (u ⬝ᵥ g ω) * (v ⬝ᵥ g ω) ∂P = u ⬝ᵥ (secondMoment P g *ᵥ v) := by
  simp only [dot_mul_dot]
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hg a b).const_mul _]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, secondMoment, Matrix.of_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => (hg a b).const_mul _]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul]
  ring

omit [Fintype k] in
/-- Linear images of `g` have finite second moments. -/
lemma HasSecondMoments.mulVec (hg : HasSecondMoments P g) (B : Matrix k m ℝ) :
    HasSecondMoments P (fun ω => B *ᵥ g ω) :=
  fun a b => integrable_dot_mul_dot hg (B a) (B b)

omit [Fintype k] in
/-- `E[(B g) (B g)ᵀ] = B Σ_g Bᵀ` (arXiv 2607.05872, proofs of Prop. 3 and Prop. 4). -/
theorem secondMoment_mulVec (hg : HasSecondMoments P g) (B : Matrix k m ℝ) :
    secondMoment P (fun ω => B *ᵥ g ω) = B * secondMoment P g * Bᵀ := by
  ext a b
  simp only [secondMoment, Matrix.of_apply]
  change ∫ ω, (B a ⬝ᵥ g ω) * (B b ⬝ᵥ g ω) ∂P = _
  rw [integral_dot_mul_dot hg]
  rw [Matrix.mul_assoc, Matrix.mul_apply']
  rfl

/-- `E ‖g‖² = tr Σ_g` (arXiv 2607.05872, proof of Prop. 4). -/
theorem integral_sum_sq (hg : HasSecondMoments P g) :
    ∫ ω, ∑ a, g ω a ^ 2 ∂P = Matrix.trace (secondMoment P g) := by
  have e : ∀ ω, ∑ a, g ω a ^ 2 = ∑ a, g ω a * g ω a := fun ω =>
    Finset.sum_congr rfl fun a _ => sq _
  simp_rw [e]
  rw [integral_finsetSum _ fun a _ => hg a a]
  simp [Matrix.trace, secondMoment]

end SecondMoment

/-! ### The orthogonal group `O(r)` and its Haar measure -/

/-- The real orthogonal group `O(r)`, with the topology and the Borel `σ`-algebra induced from
`ℝ^{r × r}`. -/
abbrev O (r : ℕ) : Type := Matrix.orthogonalGroup (Fin r) ℝ

variable {r : ℕ}

lemma O.transpose_mul_self (R : O r) : (R.1)ᵀ * R.1 = 1 :=
  (Matrix.mem_orthogonalGroup_iff' (Fin r) ℝ).1 R.2

/-- Every column of an orthogonal matrix is a unit vector. -/
lemma O.sum_sq_col (R : O r) (i : Fin r) : ∑ j, R.1 j i ^ 2 = 1 := by
  have h := congrFun (congrFun (O.transpose_mul_self R) i) i
  simpa [Matrix.mul_apply, sq] using h

lemma O.abs_entry_le (R : O r) (j i : Fin r) : |R.1 j i| ≤ 1 := by
  have h : R.1 j i ^ 2 ≤ 1 := by
    rw [← O.sum_sq_col R i]
    exact Finset.single_le_sum (f := fun j => R.1 j i ^ 2) (fun _ _ => sq_nonneg _) (mem_univ j)
  exact sq_le_one_iff_abs_le_one _ |>.1 h

/-- `O(r)` is compact: it is closed and its entries are bounded by `1`. -/
instance : CompactSpace (O r) := by
  have hbox : IsCompact (Set.pi univ fun _ : Fin r => Set.pi univ fun _ : Fin r =>
      Icc (-1 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  have hcl : IsClosed ((Matrix.orthogonalGroup (Fin r) ℝ : Submonoid _) :
      Set (Matrix (Fin r) (Fin r) ℝ)) := isClosed_unitary
  refine isCompact_iff_compactSpace.1 (IsCompact.of_isClosed_subset hbox hcl ?_)
  intro M hM j _ i _
  exact abs_le.1 (O.abs_entry_le ⟨M, hM⟩ j i)

/-- The Haar probability measure on `O(r)`. -/
noncomputable def haarO (r : ℕ) : Measure (O r) := Measure.haarMeasure ⊤

instance : IsProbabilityMeasure (haarO r) :=
  ⟨by simpa [haarO] using
    Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (O r)))⟩

instance : (haarO r).IsMulLeftInvariant := by unfold haarO; infer_instance

@[fun_prop] lemma continuous_entry (j i : Fin r) : Continuous fun R : O r => R.1 j i :=
  continuous_subtype_val.matrix_elem j i

private lemma integrable_cont (μ : Measure (O r)) [IsFiniteMeasure μ] {f : O r → ℝ}
    (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (.of_compactSpace f)

/-- The permutation matrix of `σ`, as an element of `O(r)`. -/
private noncomputable def permO (σ : Equiv.Perm (Fin r)) : O r :=
  ⟨(1 : Matrix (Fin r) (Fin r) ℝ).submatrix σ id, by
    rw [Matrix.mem_orthogonalGroup_iff]
    ext a b
    simp [Matrix.mul_apply, Matrix.one_apply, eq_comm]⟩

private lemma permO_mul (σ : Equiv.Perm (Fin r)) (R : O r) :
    (permO σ * R).1 = R.1.submatrix σ id := by
  ext a b
  simp [permO, Matrix.mul_apply, Matrix.one_apply]

/-- The Householder vector `e_j + 2 e_k`. -/
private noncomputable def hv (j k : Fin r) : Fin r → ℝ := Pi.single j 1 + Pi.single k 2

private lemma hv_dot (j k : Fin r) (x : Fin r → ℝ) : hv j k ⬝ᵥ x = x j + 2 * x k := by
  simp [hv, add_dotProduct, single_dotProduct]

private lemma hv_self {j k : Fin r} (hjk : j ≠ k) : hv j k ⬝ᵥ hv j k = 5 := by
  rw [hv_dot]
  simp [hv, hjk, hjk.symm]
  norm_num

/-- The Householder reflection `1 - (2/5) v vᵀ`, `v = e_j + 2 e_k`, as an element of `O(r)`.  It
acts on the `(j, k)` plane as `(x_j, x_k) ↦ ((3 x_j - 4 x_k) / 5, (-4 x_j - 3 x_k) / 5)`. -/
private noncomputable def reflO {j k : Fin r} (hjk : j ≠ k) : O r :=
  ⟨1 - (2 / 5 : ℝ) • Matrix.vecMulVec (hv j k) (hv j k), by
    rw [Matrix.mem_orthogonalGroup_iff]
    have ht : (Matrix.vecMulVec (hv j k) (hv j k))ᵀ = Matrix.vecMulVec (hv j k) (hv j k) := by
      ext a b; simp [Matrix.vecMulVec_apply, mul_comm]
    have hs : Matrix.vecMulVec (hv j k) (hv j k) * Matrix.vecMulVec (hv j k) (hv j k) =
        (5 : ℝ) • Matrix.vecMulVec (hv j k) (hv j k) := by
      rw [Matrix.vecMulVec_mul_vecMulVec, hv_self hjk]
      ext a b; simp [Matrix.vecMulVec_apply]; ring
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, ht]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, hs, smul_smul]
    ext a b
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring⟩

private lemma reflO_mul_apply {j k : Fin r} (hjk : j ≠ k) (R : O r) (a i : Fin r) :
    (reflO hjk * R).1 a i = R.1 a i - 2 / 5 * hv j k a * (R.1 j i + 2 * R.1 k i) := by
  have h : ∀ x : Fin r → ℝ, ∑ c, hv j k c * x c = x j + 2 * x k := by
    intro x; simpa [dotProduct] using hv_dot j k x
  have := h fun c => R.1 c i
  simp only [reflO, Submonoid.coe_mul, Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, sub_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← this, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun c _ => by ring

private lemma reflO_left {j k : Fin r} (hjk : j ≠ k) (R : O r) (i : Fin r) :
    (reflO hjk * R).1 j i = (3 * R.1 j i - 4 * R.1 k i) / 5 := by
  rw [reflO_mul_apply]
  simp [hv, hjk]
  ring

private lemma reflO_right {j k : Fin r} (hjk : j ≠ k) (R : O r) (i : Fin r) :
    (reflO hjk * R).1 k i = (-4 * R.1 j i - 3 * R.1 k i) / 5 := by
  rw [reflO_mul_apply]
  simp [hv, hjk.symm]
  ring

/-! ### The Haar moments of a column (paper, eq. (6)) -/

section Moments

variable (μ : Measure (O r)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]

omit [IsProbabilityMeasure μ] in
private lemma integral_perm (σ : Equiv.Perm (Fin r)) (f : Matrix (Fin r) (Fin r) ℝ → ℝ) :
    ∫ R : O r, f (R.1.submatrix σ id) ∂μ = ∫ R : O r, f R.1 ∂μ := by
  have h := integral_mul_left_eq_self (μ := μ) (fun R : O r => f R.1) (permO σ)
  simpa only [permO_mul] using h

omit [IsProbabilityMeasure μ] in
private lemma moment2_eq (i j k : Fin r) :
    ∫ R : O r, R.1 j i ^ 2 ∂μ = ∫ R : O r, R.1 k i ^ 2 ∂μ := by
  simpa using integral_perm μ (Equiv.swap j k) (fun M => M k i ^ 2)

omit [IsProbabilityMeasure μ] in
private lemma moment4_eq (i j k : Fin r) :
    ∫ R : O r, R.1 j i ^ 4 ∂μ = ∫ R : O r, R.1 k i ^ 4 ∂μ := by
  simpa using integral_perm μ (Equiv.swap j k) (fun M => M k i ^ 4)

omit [IsProbabilityMeasure μ] in
private lemma moment31_eq (i j k : Fin r) :
    ∫ R : O r, R.1 j i ^ 3 * R.1 k i ∂μ = ∫ R : O r, R.1 k i ^ 3 * R.1 j i ∂μ := by
  simpa using integral_perm μ (Equiv.swap j k) (fun M => M k i ^ 3 * M j i)

/-- The key rotation identity: `E x_j⁴ = 3 E x_j² x_k²` for `j ≠ k`, from invariance of the law of
a column under one reflection of the `(j, k)` plane. -/
private lemma moment4_eq_three {j k : Fin r} (hjk : j ≠ k) (i : Fin r) :
    ∫ R : O r, R.1 j i ^ 4 ∂μ = 3 * ∫ R : O r, R.1 j i ^ 2 * R.1 k i ^ 2 ∂μ := by
  have h1 := integral_mul_left_eq_self (μ := μ) (fun R : O r => R.1 j i ^ 4) (reflO hjk)
  have h2 := integral_mul_left_eq_self (μ := μ) (fun R : O r => R.1 k i ^ 4) (reflO hjk)
  simp only [reflO_left, reflO_right] at h1 h2
  have h3 : ∫ R : O r, ((3 * R.1 j i - 4 * R.1 k i) / 5) ^ 4 +
        ((-4 * R.1 j i - 3 * R.1 k i) / 5) ^ 4 ∂μ =
      337 / 625 * (∫ R : O r, R.1 j i ^ 4 ∂μ) + 336 / 625 * (∫ R : O r, R.1 j i ^ 3 * R.1 k i ∂μ) +
        1728 / 625 * (∫ R : O r, R.1 j i ^ 2 * R.1 k i ^ 2 ∂μ) -
        336 / 625 * (∫ R : O r, R.1 k i ^ 3 * R.1 j i ∂μ) +
        337 / 625 * (∫ R : O r, R.1 k i ^ 4 ∂μ) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
      ← integral_const_mul, ← integral_add, ← integral_add, ← integral_sub, ← integral_add]
    · exact integral_congr_ae (.of_forall fun R => by simp only []; ring)
    all_goals exact integrable_cont μ (by fun_prop)
  rw [integral_add (integrable_cont μ (by fun_prop)) (integrable_cont μ (by fun_prop)), h1, h2,
    moment31_eq μ i k j, ← moment4_eq μ i j k] at h3
  have hc := moment31_eq μ i j k
  linarith

omit [μ.IsMulLeftInvariant] in
private lemma sum_moment2 (i : Fin r) : ∑ j, ∫ R : O r, R.1 j i ^ 2 ∂μ = 1 := by
  rw [← integral_finsetSum _ fun j _ => integrable_cont μ (by fun_prop)]
  simp [O.sum_sq_col]

omit [μ.IsMulLeftInvariant] in
private lemma sum_moment22 (i : Fin r) :
    ∑ j, ∑ k, ∫ R : O r, R.1 j i ^ 2 * R.1 k i ^ 2 ∂μ = 1 := by
  have h : ∀ j, ∑ k, ∫ R : O r, R.1 j i ^ 2 * R.1 k i ^ 2 ∂μ =
      ∫ R : O r, ∑ k, R.1 j i ^ 2 * R.1 k i ^ 2 ∂μ := fun j =>
    (integral_finsetSum _ fun k _ => integrable_cont μ (by fun_prop)).symm
  simp_rw [h]
  rw [← integral_finsetSum _ fun j _ => integrable_cont μ (by fun_prop)]
  have : ∀ R : O r, ∑ j, ∑ k, R.1 j i ^ 2 * R.1 k i ^ 2 = 1 := fun R => by
    rw [← Finset.sum_mul_sum, O.sum_sq_col, one_mul]
  simp [this]

/-- **Second Haar moment** (arXiv 2607.05872, Appendix B, eq. (6)): `E[R_ji²] = 1/r`, for every
left-invariant probability measure on `O(r)`. -/
theorem haar_moment_two (i j : Fin r) : ∫ R : O r, R.1 j i ^ 2 ∂μ = 1 / r := by
  have hr : (r : ℝ) ≠ 0 := by
    have : 0 < r := i.pos
    positivity
  have h := sum_moment2 μ i
  simp_rw [moment2_eq μ i _ j] at h
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  field_simp
  linarith

/-- **Mixed fourth Haar moments** in one formula: `E[R_ji² R_ki²] = (1 + 2 δ_jk) / (r (r + 2))`. -/
private lemma moment22_eq (i j k : Fin r) :
    ∫ R : O r, R.1 j i ^ 2 * R.1 k i ^ 2 ∂μ = (1 + if j = k then 2 else 0) / (r * (r + 2)) := by
  have hr : (r : ℝ) ≠ 0 := by
    have : 0 < r := i.pos
    positivity
  have hr2 : (r : ℝ) + 2 ≠ 0 := by positivity
  set A := ∫ R : O r, R.1 i i ^ 4 ∂μ with hA
  have hm : ∀ a b : Fin r, ∫ R : O r, R.1 a i ^ 2 * R.1 b i ^ 2 ∂μ =
      A / 3 + if a = b then 2 * A / 3 else 0 := by
    intro a b
    split_ifs with hab
    · subst hab
      have : ∀ R : O r, R.1 a i ^ 2 * R.1 a i ^ 2 = R.1 a i ^ 4 := fun R => by ring
      simp_rw [this]
      rw [moment4_eq μ i a i]
      ring
    · have := moment4_eq_three μ hab i
      rw [moment4_eq μ i a i] at this
      rw [add_zero]
      linarith
  have h := sum_moment22 μ i
  simp_rw [hm, Finset.sum_add_distrib] at h
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true] at h
  have hA' : A * (r * (r + 2)) = 3 := by
    have : ∑ a : Fin r, (2 * A / 3) = r * (2 * A / 3) := by simp
    nlinarith
  have hA'' : A = 3 / (r * (r + 2)) := by
    field_simp
    linarith
  rw [hm, hA'']
  split_ifs
  · field_simp
  · field_simp
    simp

/-- **Fourth Haar moment** (arXiv 2607.05872, Appendix B, eq. (6)): `E[R_ji⁴] = 3 / (r (r + 2))`.
The paper quotes this from the sphere moments; here it is derived from invariance. -/
theorem haar_moment_four (i j : Fin r) :
    ∫ R : O r, R.1 j i ^ 4 ∂μ = 3 / (r * (r + 2)) := by
  have h := moment22_eq μ i j j
  have e : ∀ R : O r, R.1 j i ^ 2 * R.1 j i ^ 2 = R.1 j i ^ 4 := fun R => by ring
  simp_rw [e] at h
  rw [h]
  norm_num

/-- **Mixed Haar moment** (arXiv 2607.05872, Appendix B, eq. (6)):
`E[R_ji² R_ki²] = 1 / (r (r + 2))` for `j ≠ k`. -/
theorem haar_moment_two_two {j k : Fin r} (hjk : j ≠ k) (i : Fin r) :
    ∫ R : O r, R.1 j i ^ 2 * R.1 k i ^ 2 ∂μ = 1 / (r * (r + 2)) := by
  simpa [hjk] using moment22_eq μ i j k

end Moments

/-! ### Theorem 1: the blind-estimator lower bound -/

/-- The paper's optimal new-basis second moment `v*(U R)_i = ∑_j λ_j R_ji²`. -/
noncomputable def vStar (lam : Fin r → ℝ) (R : Matrix (Fin r) (Fin r) ℝ) (i : Fin r) : ℝ :=
  ∑ j, lam j * R j i ^ 2

/-- The mean `λ̄ = (1 / r) ∑_j λ_j`. -/
noncomputable def lamBar (lam : Fin r → ℝ) : ℝ := (∑ j, lam j) / r

/-- The paper's `Var(λ) = (1 / r) ∑_j (λ_j - λ̄)²` (its proof uses `r Var(λ) = S₂ - S₁² / r`). -/
noncomputable def lamVar (lam : Fin r → ℝ) : ℝ := (∑ j, (lam j - lamBar lam) ^ 2) / r

/-- The identity `r Var(λ) = S₂ - S₁² / r` (arXiv 2607.05872, Appendix B). -/
theorem mul_lamVar (hr : 0 < r) (lam : Fin r → ℝ) :
    r * lamVar lam = ∑ j, lam j ^ 2 - (∑ j, lam j) ^ 2 / r := by
  have hr' : (r : ℝ) ≠ 0 := by positivity
  have h : ∑ j, (lam j - lamBar lam) ^ 2 =
      ∑ j, lam j ^ 2 - 2 * lamBar lam * ∑ j, lam j + r * lamBar lam ^ 2 := by
    calc ∑ j, (lam j - lamBar lam) ^ 2
        = ∑ j, (lam j ^ 2 - 2 * lamBar lam * lam j + lamBar lam ^ 2) :=
          Finset.sum_congr rfl fun j _ => by ring
      _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_const,
            card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [lamVar, mul_div_cancel₀ _ hr', h, lamBar]
  field_simp
  ring

section Blind

variable (μ : Measure (O r)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]

/-- The mean of `v*` (arXiv 2607.05872, proof of Theorem 1): `E_R[v*_i] = λ̄`. -/
theorem integral_vStar (lam : Fin r → ℝ) (i : Fin r) :
    ∫ R : O r, vStar lam R.1 i ∂μ = lamBar lam := by
  simp only [vStar]
  rw [integral_finsetSum _ fun j _ => integrable_cont μ (by fun_prop)]
  simp_rw [integral_const_mul, haar_moment_two μ i, lamBar, div_eq_mul_inv, one_mul,
    Finset.sum_mul]

/-- The second moment of `v*` (arXiv 2607.05872, Appendix B):
`E_R[(v*_i)²] = (2 S₂ + S₁²) / (r (r + 2))`. -/
theorem integral_vStar_sq (lam : Fin r → ℝ) (i : Fin r) :
    ∫ R : O r, vStar lam R.1 i ^ 2 ∂μ =
      (2 * ∑ j, lam j ^ 2 + (∑ j, lam j) ^ 2) / (r * (r + 2)) := by
  have e : ∀ R : O r, vStar lam R.1 i ^ 2 =
      ∑ j, ∑ k, lam j * lam k * (R.1 j i ^ 2 * R.1 k i ^ 2) := fun R => by
    rw [vStar, sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun k _ => integrable_cont μ (by fun_prop)]
  have h : ∀ j, ∫ R : O r, ∑ k, lam j * lam k * (R.1 j i ^ 2 * R.1 k i ^ 2) ∂μ =
      ∑ k, (lam j * lam k / (r * (r + 2)) +
        if j = k then 2 * lam j * lam k / (r * (r + 2)) else 0) := by
    intro j
    rw [integral_finsetSum _ fun k _ => integrable_cont μ (by fun_prop)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, moment22_eq μ i j k]
    split_ifs <;> ring
  simp_rw [h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [sq (∑ j, lam j), Finset.sum_mul_sum]
  simp only [add_div, Finset.sum_div, Finset.mul_sum]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The variance of `v*` (arXiv 2607.05872, Appendix B, eq. (7)):
`Var_R(v*_i) = 2 Var(λ) / (r + 2)`. -/
theorem variance_vStar (lam : Fin r → ℝ) (i : Fin r) :
    ProbabilityTheory.variance (fun R : O r => vStar lam R.1 i) μ = 2 * lamVar lam / (r + 2) := by
  have hr : 0 < r := i.pos
  have hr' : (r : ℝ) ≠ 0 := by positivity
  have hc : Continuous fun R : O r => vStar lam R.1 i := by unfold vStar; fun_prop
  rw [ProbabilityTheory.variance_eq_integral hc.aemeasurable, integral_vStar]
  have e : ∀ R : O r, (vStar lam R.1 i - lamBar lam) ^ 2 =
      vStar lam R.1 i ^ 2 - 2 * lamBar lam * vStar lam R.1 i + lamBar lam ^ 2 := fun R => by ring
  simp_rw [e]
  rw [integral_add (integrable_cont μ (by fun_prop)) (integrable_const _),
    integral_sub (integrable_cont μ (by fun_prop)) (integrable_cont μ (by fun_prop)),
    integral_const_mul, integral_vStar, integral_vStar_sq, integral_const]
  have hv := mul_lamVar hr lam
  have hb : lamBar lam = (∑ j, lam j) / r := rfl
  have hv' : lamVar lam = (∑ j, lam j ^ 2 - (∑ j, lam j) ^ 2 / r) / r := by
    rw [← hv]; field_simp
  simp only [probReal_univ, one_smul, hb, hv']
  field_simp
  ring

/-- Bias–variance decomposition of one coordinate: `E_R[(c - v*_i)²] = (c - λ̄)² + Var_R(v*_i)`. -/
private lemma integral_sub_vStar_sq (lam : Fin r → ℝ) (c : ℝ) (i : Fin r) :
    ∫ R : O r, (c - vStar lam R.1 i) ^ 2 ∂μ = (c - lamBar lam) ^ 2 + 2 * lamVar lam / (r + 2) := by
  have hc : Continuous fun R : O r => vStar lam R.1 i := by unfold vStar; fun_prop
  rw [← variance_vStar μ lam i, ProbabilityTheory.variance_eq_integral hc.aemeasurable,
    integral_vStar]
  have e : ∀ R : O r, (c - vStar lam R.1 i) ^ 2 = (vStar lam R.1 i - lamBar lam) ^ 2 +
      2 * (lamBar lam - c) * (vStar lam R.1 i - lamBar lam) + (c - lamBar lam) ^ 2 := fun R => by
    ring
  simp_rw [e]
  rw [integral_add (integrable_cont μ (by fun_prop)) (integrable_const _),
    integral_add (integrable_cont μ (by fun_prop)) (integrable_cont μ (by fun_prop)),
    integral_const_mul, integral_sub (integrable_cont μ (by fun_prop)) (integrable_const _),
    integral_vStar, integral_const]
  simp
  ring

/-- **Theorem 1, the identity in eq. (5)** (arXiv 2607.05872, Appendix B), for every left-invariant
probability measure on `O(r)` (in particular `haarO r`, see `blind_estimator_lower_bound_haar`):

  `E_R ∑_i (v̂_i - v*_i)² = ∑_i (v̂_i - λ̄)² + 2 r Var(λ) / (r + 2)`.

A blind estimator is a function of `λ` alone, so for fixed `λ` it is a fixed vector; the statement
quantifies over all fixed vectors `v̂` and all `λ`, hence covers every such function. -/
theorem blind_estimator_mse (lam vhat : Fin r → ℝ) :
    ∫ R : O r, ∑ i, (vhat i - vStar lam R.1 i) ^ 2 ∂μ =
      ∑ i, (vhat i - lamBar lam) ^ 2 + 2 * r * lamVar lam / (r + 2) := by
  have hc : ∀ i, Continuous fun R : O r => (vhat i - vStar lam R.1 i) ^ 2 := fun i => by
    unfold vStar; fun_prop
  rw [integral_finsetSum _ fun i _ => integrable_cont μ (hc i)]
  simp_rw [integral_sub_vStar_sq μ lam, Finset.sum_add_distrib]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **Theorem 1, the lower bound in eq. (5)** (arXiv 2607.05872, Appendix B). -/
theorem blind_estimator_lower_bound (lam vhat : Fin r → ℝ) :
    2 * r * lamVar lam / (r + 2) ≤ ∫ R : O r, ∑ i, (vhat i - vStar lam R.1 i) ^ 2 ∂μ := by
  rw [blind_estimator_mse]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- **Theorem 1, the equality case** (arXiv 2607.05872, Appendix B): the floor is attained exactly
by the mean predictor `v̂ = λ̄ 1`. -/
theorem blind_estimator_eq_floor_iff (lam vhat : Fin r → ℝ) :
    ∫ R : O r, ∑ i, (vhat i - vStar lam R.1 i) ^ 2 ∂μ = 2 * r * lamVar lam / (r + 2) ↔
      vhat = fun _ => lamBar lam := by
  rw [blind_estimator_mse, add_eq_right,
    Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _]
  simp only [Finset.mem_univ, forall_true_left, sq_eq_zero_iff, sub_eq_zero]
  exact ⟨fun h => funext h, fun h i => congrFun h i⟩

/-- **Theorem 1, canonical carry** (arXiv 2607.05872, Appendix B): `v̂ = λ` costs
`E_R ∑_i (λ_i - v*_i)² = r (r + 4) Var(λ) / (r + 2)`. -/
theorem carry_mse (hr : 0 < r) (lam : Fin r → ℝ) :
    ∫ R : O r, ∑ i, (lam i - vStar lam R.1 i) ^ 2 ∂μ = r * (r + 4) * lamVar lam / (r + 2) := by
  have hr' : (r : ℝ) ≠ 0 := by positivity
  have hs : ∑ i, (lam i - lamBar lam) ^ 2 = r * lamVar lam := by
    rw [lamVar]; field_simp
  rw [blind_estimator_mse, hs]
  field_simp
  ring

/-- **Theorem 1, the suboptimality factor** (arXiv 2607.05872, Appendix B): canonical carry costs
exactly `(r + 4) / 2` times the floor. -/
theorem carry_mse_eq_factor_mul_floor (hr : 0 < r) (lam : Fin r → ℝ) :
    ∫ R : O r, ∑ i, (lam i - vStar lam R.1 i) ^ 2 ∂μ =
      ((r + 4) / 2) * (2 * r * lamVar lam / (r + 2)) := by
  rw [carry_mse μ hr]
  field_simp

end Blind

/-- **Theorem 1 (blind-estimator lower bound)**, arXiv 2607.05872, Appendix B, for `R` distributed
according to the Haar measure of `O(r)`: the identity and the bound of eq. (5), its equality case,
the carry cost, and the factor `(r + 4) / 2`.

The moments are derived from Haar invariance, with no Weingarten calculus and no input on the
sphere (`haar_moment_two`, `haar_moment_four`, `haar_moment_two_two`).  The paper's `Beta` law of
`R_ji²` is not used and not formalized.  The heuristic of Remark 2 (factor `(r - k⋆) / 2`) is not a
theorem of the paper and is not treated.  The form of `v*` is the subject of
`newBasis_secondMoment`, which also records the assumption the paper leaves implicit. -/
theorem blind_estimator_lower_bound_haar (hr : 0 < r) (lam vhat : Fin r → ℝ) :
    (∫ R : O r, ∑ i, (vhat i - vStar lam R.1 i) ^ 2 ∂haarO r =
        ∑ i, (vhat i - lamBar lam) ^ 2 + 2 * r * lamVar lam / (r + 2)) ∧
      (2 * r * lamVar lam / (r + 2) ≤ ∫ R : O r, ∑ i, (vhat i - vStar lam R.1 i) ^ 2 ∂haarO r) ∧
      (∫ R : O r, ∑ i, (vhat i - vStar lam R.1 i) ^ 2 ∂haarO r = 2 * r * lamVar lam / (r + 2) ↔
        vhat = fun _ => lamBar lam) ∧
      (∫ R : O r, ∑ i, (lam i - vStar lam R.1 i) ^ 2 ∂haarO r =
        r * (r + 4) * lamVar lam / (r + 2)) ∧
      (∫ R : O r, ∑ i, (lam i - vStar lam R.1 i) ^ 2 ∂haarO r =
        ((r + 4) / 2) * (2 * r * lamVar lam / (r + 2))) :=
  ⟨blind_estimator_mse _ lam vhat, blind_estimator_lower_bound _ lam vhat,
    blind_estimator_eq_floor_iff _ lam vhat, carry_mse _ hr lam,
    carry_mse_eq_factor_mul_floor _ hr lam⟩

/-- **The form of `v*`** (arXiv 2607.05872, Theorem 1).  Let `g = Uᵀ G` have uncorrelated
coordinates, `E[g gᵀ] = diag(λ)`.  Then the second moments in the new basis `U' = U R` are exactly
`v*(U')_i = ∑_j λ_j R_ji²`, for every fixed `R`.

Difference from the paper: it assumes only `λ_i = E[g_i²]`, but the formula also needs the
off-diagonal second moments to vanish (`vStar_requires_uncorrelated`).  With this assumption, which
the paper leaves implicit, `v*` is what Theorem 1 says it is. -/
theorem newBasis_secondMoment {Ω m : Type*} [MeasurableSpace Ω] [Fintype m] {P : Measure Ω}
    {G : Ω → m → ℝ} (U : Matrix m (Fin r) ℝ) {lam : Fin r → ℝ}
    (hg : HasSecondMoments P fun ω => Uᵀ *ᵥ G ω)
    (hdiag : secondMoment P (fun ω => Uᵀ *ᵥ G ω) = Matrix.diagonal lam)
    (R : Matrix (Fin r) (Fin r) ℝ) (i : Fin r) :
    ∫ ω, ((U * R)ᵀ *ᵥ G ω) i ^ 2 ∂P = vStar lam R i := by
  have e : ∀ ω, (U * R)ᵀ *ᵥ G ω = Rᵀ *ᵥ (Uᵀ *ᵥ G ω) := fun ω => by
    rw [Matrix.transpose_mul, Matrix.mulVec_mulVec]
  have h := congrFun (congrFun (secondMoment_mulVec hg Rᵀ) i) i
  rw [hdiag, Matrix.transpose_transpose] at h
  simp only [secondMoment, Matrix.of_apply] at h
  simp_rw [e, sq]
  rw [h, vStar, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_diagonal, Matrix.transpose_apply]
  ring

/-- **The formula for `v*` fails without uncorrelated coordinates** (arXiv 2607.05872, Theorem 1,
"the optimal new-basis values are ..."): for the deterministic gradient `g = (1, 1)`, with
`λ = (1, 1)` and the reflection `R = (1 / 5) [[3, 4], [4, -3]]`, the new second moment of the first
coordinate is `49 / 25`, while `∑_j λ_j R_j0² = 1`.  See `newBasis_secondMoment`. -/
theorem vStar_requires_uncorrelated :
    ∃ (P : Measure Unit) (_ : IsProbabilityMeasure P) (g : Unit → Fin 2 → ℝ) (R : O 2)
      (lam : Fin 2 → ℝ), (∀ a, lam a = ∫ ω, g ω a ^ 2 ∂P) ∧
        ∫ ω, (R.1ᵀ *ᵥ g ω) 0 ^ 2 ∂P ≠ vStar lam R.1 0 := by
  have hR : (!![3 / 5, 4 / 5; 4 / 5, -3 / 5] : Matrix (Fin 2) (Fin 2) ℝ) ∈
      Matrix.orthogonalGroup (Fin 2) ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  refine ⟨Measure.dirac (), inferInstance, fun _ => ![1, 1], ⟨_, hR⟩, ![1, 1], ?_, ?_⟩
  · intro a
    fin_cases a <;> simp
  · simp [vStar, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    norm_num

/-! ### Proposition 3: first-moment transport -/

section Transport

open scoped LeanDLRA.Frobenius

variable {Ω : Type*} [MeasurableSpace Ω] {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m]
  [DecidableEq k]

/-- The mean squared error `E ‖U_newᵀ g - A U_oldᵀ g‖²` of the linear estimator `A` of the new
coordinates `m̂ = U_newᵀ g` from the old coordinates `m = U_oldᵀ g`. -/
noncomputable def transportMSE (P : Measure Ω) (g : Ω → m → ℝ) (Unew Uold : Matrix m k ℝ)
    (A : Matrix k k ℝ) : ℝ :=
  ∫ ω, ∑ i, ((Unewᵀ *ᵥ g ω) i - (A *ᵥ (Uoldᵀ *ᵥ g ω)) i) ^ 2 ∂P

/-- The Pythagorean splitting behind Prop. 3 (Frobenius norm):
`‖U_newᵀ - A U_oldᵀ‖² = ‖R - A‖² + ‖U_newᵀ (1 - U_old U_oldᵀ)‖²`, with `R = U_newᵀ U_old`. -/
private lemma norm_sq_transport (Unew : Matrix m k ℝ) {Uold : Matrix m k ℝ}
    (hold : Uoldᵀ * Uold = 1) (A : Matrix k k ℝ) :
    ‖Unewᵀ - A * Uoldᵀ‖ ^ 2 =
      ‖Unewᵀ * Uold - A‖ ^ 2 + ‖Unewᵀ * (1 - Uold * Uoldᵀ)‖ ^ 2 := by
  have hsplit : Unewᵀ - A * Uoldᵀ =
      (Unewᵀ * Uold - A) * Uoldᵀ + Unewᵀ * (1 - Uold * Uoldᵀ) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
    abel
  have hperp : ⟪(Unewᵀ * Uold - A) * Uoldᵀ, Unewᵀ * (1 - Uold * Uoldᵀ)⟫ = 0 := by
    have hz : Unewᵀ * (1 - Uold * Uoldᵀ) * Uold = 0 := by
      rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hold, Matrix.mul_one,
        sub_self, Matrix.mul_zero]
    rw [LeanDLRA.Frobenius.inner_mul_right, Matrix.transpose_transpose, hz, inner_zero_right]
  rw [hsplit, norm_add_sq_real, hperp, LeanDLRA.Frobenius.norm_mul_transpose_of_orthonormal hold]
  ring

variable {P : Measure Ω} {g : Ω → m → ℝ} {s : ℝ}

omit [Fintype k] in
/-- **Prop. 3, isotropy of the old coordinates** (arXiv 2607.05872, Appendix C, proof): if
`E[g gᵀ] = σ² 1` and `U_oldᵀ U_old = 1`, then `Cov(U_oldᵀ g) = σ² 1`.  Here `s = σ²`. -/
theorem secondMoment_old_coordinates (hg : HasSecondMoments P g)
    (hiso : secondMoment P g = s • 1) {Uold : Matrix m k ℝ} (hold : Uoldᵀ * Uold = 1) :
    secondMoment P (fun ω => Uoldᵀ *ᵥ g ω) = s • 1 := by
  rw [secondMoment_mulVec hg, hiso, Matrix.transpose_transpose, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, hold]

/-- **Prop. 3, the error formula** (arXiv 2607.05872, Appendix C, proof): for isotropic `g`,
`E[g gᵀ] = σ² 1` with `s = σ²`,

  `E ‖m̂ - A m‖² = σ² ‖R - A‖² + σ² ‖U_newᵀ (1 - U_old U_oldᵀ)‖²`,   `R = U_newᵀ U_old`.

Difference from the paper: only the second moment of `g` is used, not Gaussianity; the Gaussian
case is `mmse_transport_gaussian`. -/
theorem transportMSE_eq (hg : HasSecondMoments P g) (hiso : secondMoment P g = s • 1)
    (Unew : Matrix m k ℝ) {Uold : Matrix m k ℝ} (hold : Uoldᵀ * Uold = 1) (A : Matrix k k ℝ) :
    transportMSE P g Unew Uold A =
      s * (‖Unewᵀ * Uold - A‖ ^ 2 + ‖Unewᵀ * (1 - Uold * Uoldᵀ)‖ ^ 2) := by
  have e : ∀ ω, ∑ i, ((Unewᵀ *ᵥ g ω) i - (A *ᵥ (Uoldᵀ *ᵥ g ω)) i) ^ 2 =
      ∑ i, ((Unewᵀ - A * Uoldᵀ) *ᵥ g ω) i ^ 2 := fun ω => by
    rw [Matrix.sub_mulVec, Matrix.mulVec_mulVec]
    rfl
  simp only [transportMSE, e]
  rw [integral_sum_sq (hg.mulVec _), secondMoment_mulVec hg, hiso, ← norm_sq_transport _ hold,
    LeanDLRA.Frobenius.norm_sq_eq_sum, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.trace_smul, smul_eq_mul]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, sq]

/-- The irreducible error: `‖U_newᵀ (1 - U_old U_oldᵀ)‖² = r - ‖U_newᵀ U_old‖²`. -/
private lemma norm_sq_residual {Unew Uold : Matrix m k ℝ}
    (hnew : Unewᵀ * Unew = 1) (hold : Uoldᵀ * Uold = 1) :
    ‖Unewᵀ * (1 - Uold * Uoldᵀ)‖ ^ 2 = Fintype.card k - ‖Unewᵀ * Uold‖ ^ 2 := by
  have h := norm_sq_transport Unew hold 0
  have hn : ‖Unewᵀ‖ ^ 2 = Fintype.card k := by
    rw [LeanDLRA.Frobenius.norm_transpose, ← real_inner_self_eq_norm_sq,
      LeanDLRA.Frobenius.inner_eq_trace, hnew, Matrix.trace_one]
  simp only [Matrix.zero_mul, sub_zero, hn] at h
  linarith

/-- **Proposition 3 (MMSE first-moment transport)**, arXiv 2607.05872, Appendix C.  For isotropic
`g` (`E[g gᵀ] = σ² 1`, `σ² = s > 0`), among linear estimators `A m` of `m̂ = U_newᵀ g` from
`m = U_oldᵀ g` the mean squared error is minimized by `A = R = U_newᵀ U_old`, this minimizer is
unique, and the minimum is `σ² (r - ‖R‖²)`.

Difference from the paper: Gaussianity is replaced by the weaker isotropy of the second moment
(the Gaussian case is `mmse_transport_gaussian`); uniqueness and the minimum value are in the
paper's proof, not in its statement. -/
theorem mmse_transport (hg : HasSecondMoments P g) (hiso : secondMoment P g = s • 1) (hs : 0 < s)
    {Unew Uold : Matrix m k ℝ} (hnew : Unewᵀ * Unew = 1) (hold : Uoldᵀ * Uold = 1) :
    (∀ A, transportMSE P g Unew Uold (Unewᵀ * Uold) ≤ transportMSE P g Unew Uold A) ∧
      (∀ A, transportMSE P g Unew Uold A = transportMSE P g Unew Uold (Unewᵀ * Uold) →
        A = Unewᵀ * Uold) ∧
      transportMSE P g Unew Uold (Unewᵀ * Uold) =
        s * (Fintype.card k - ‖Unewᵀ * Uold‖ ^ 2) := by
  refine ⟨fun A => ?_, fun A hA => ?_, ?_⟩
  · rw [transportMSE_eq hg hiso Unew hold, transportMSE_eq hg hiso Unew hold]
    simp only [sub_self, norm_zero]
    gcongr
    positivity
  · rw [transportMSE_eq hg hiso Unew hold, transportMSE_eq hg hiso Unew hold] at hA
    simp only [sub_self, norm_zero] at hA
    have h0 : ‖Unewᵀ * Uold - A‖ ^ 2 = 0 := by
      have := mul_left_cancel₀ hs.ne' hA
      nlinarith
    have h1 : Unewᵀ * Uold - A = 0 := norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0)
    exact (sub_eq_zero.1 h1).symm
  · rw [transportMSE_eq hg hiso Unew hold, norm_sq_residual hnew hold]
    simp

end Transport

/-! The Gaussian law of Proposition 3. -/

section Gaussian

open ProbabilityTheory

variable {m : Type*} [Fintype m] [DecidableEq m]

private lemma memLp_coord (S : Matrix m m ℝ) (a : m) :
    MemLp (fun x : EuclideanSpace ℝ m => x a) 2 (multivariateGaussian 0 S) :=
  (EuclideanSpace.proj a : EuclideanSpace ℝ m →L[ℝ] ℝ).comp_memLp' IsGaussian.memLp_two_id

private lemma integral_coord (S : Matrix m m ℝ) (a : m) :
    ∫ x : EuclideanSpace ℝ m, x a ∂(multivariateGaussian 0 S) = 0 := by
  have h := (EuclideanSpace.proj a : EuclideanSpace ℝ m →L[ℝ] ℝ).integral_comp_comm
    (μ := multivariateGaussian (0 : EuclideanSpace ℝ m) S) (φ := fun x => x)
    IsGaussian.integrable_id
  simpa using h

/-- The hypothesis of Prop. 3 (arXiv 2607.05872, Appendix C): the law `N(0, σ² 1)`, with
`s = σ² ≥ 0`, is isotropic with finite second moments. -/
theorem gaussian_isotropic {s : ℝ} (hs : 0 ≤ s) :
    HasSecondMoments (multivariateGaussian (0 : EuclideanSpace ℝ m) (s • 1))
        (fun x : EuclideanSpace ℝ m => x.ofLp) ∧
      secondMoment (multivariateGaussian (0 : EuclideanSpace ℝ m) (s • 1))
        (fun x : EuclideanSpace ℝ m => x.ofLp) = s • 1 := by
  have hS : (s • (1 : Matrix m m ℝ)).PosSemidef := Matrix.PosSemidef.one.smul hs
  refine ⟨fun a b => (memLp_coord _ a).integrable_mul (memLp_coord _ b), ?_⟩
  ext a b
  have h := covariance_eval_multivariateGaussian (μ := 0) hS a b
  rw [covariance_eq_sub (memLp_coord _ a) (memLp_coord _ b)] at h
  simpa [secondMoment, integral_coord] using h

/-- **Proposition 3 (MMSE first-moment transport)** in the exact setting of arXiv 2607.05872,
Appendix C: `g ∼ N(0, σ² 1)`, `σ² = s > 0`, realized as Mathlib's `multivariateGaussian`. -/
theorem mmse_transport_gaussian {k : Type*} [Fintype k] [DecidableEq k] {s : ℝ} (hs : 0 < s)
    {Unew Uold : Matrix m k ℝ} (hnew : Unewᵀ * Unew = 1) (hold : Uoldᵀ * Uold = 1) :
    letI P := multivariateGaussian (0 : EuclideanSpace ℝ m) (s • 1)
    letI g := fun x : EuclideanSpace ℝ m => x.ofLp
    (∀ A, transportMSE P g Unew Uold (Unewᵀ * Uold) ≤ transportMSE P g Unew Uold A) ∧
      (∀ A, transportMSE P g Unew Uold A = transportMSE P g Unew Uold (Unewᵀ * Uold) →
        A = Unewᵀ * Uold) := by
  have h := gaussian_isotropic (m := m) hs.le
  have := mmse_transport h.1 h.2 hs hnew hold
  exact ⟨this.1, this.2.1⟩

end Gaussian

/-! ### Proposition 4: coverage -/

section Coverage

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}

/-- The captured energy fraction `γ_g = ‖U Uᵀ g‖² / ‖g‖²` (paper, eq. (3), for a gradient
vector). -/
noncomputable def energyFraction {m k : Type*} [Fintype m] [Fintype k] (U : Matrix m k ℝ)
    (g : m → ℝ) : ℝ :=
  (∑ a, ((U * Uᵀ) *ᵥ g) a ^ 2) / ∑ a, g a ^ 2

/-- **Proposition 4 (coverage), as a ratio of means**, arXiv 2607.05872, Appendix D.  Let
`Σ_g = E[g gᵀ]` have the orthonormal eigenvectors `V` with eigenvalues `lam`, and let `U` span the
first `r` of them (`U Uᵀ` is the orthogonal projector onto their span).  Then
`E ‖U Uᵀ g‖² = ∑_{i ≤ r} λ_i`, `E ‖g‖² = ∑_i λ_i`, and hence their quotient is
`∑_{i ≤ r} λ_i / ∑_i λ_i`, which is exactly what the paper's proof computes.

Differences from the paper: its statement reads `E_g[γ_g]`, the expectation of the quotient, which
is false in general (`expected_energyFraction_ne_spectral_mass`); the true statement is the quotient
of expectations, and this is also how the paper's proof goes.  The ordering `λ₁ ≥ ⋯ ≥ λₙ` is not
needed, so it is not assumed: the identity holds for any `r` eigenvectors listed first.  The energy
fraction enters the descent bound of `LeanDLRA.Training`, `loss_projGradStep_le_energyFraction`. -/
theorem coverage_eq_spectral_mass (hr : r ≤ n) {g : Ω → Fin n → ℝ} (hg : HasSecondMoments P g)
    {V : Matrix (Fin n) (Fin n) ℝ} {lam : Fin n → ℝ} (hV : Vᵀ * V = 1)
    (hS : secondMoment P g * V = V * Matrix.diagonal lam) {U : Matrix (Fin n) (Fin r) ℝ}
    (hU : U * Uᵀ = V.submatrix id (Fin.castLE hr) * (V.submatrix id (Fin.castLE hr))ᵀ) :
    (∫ ω, ∑ a, ((U * Uᵀ) *ᵥ g ω) a ^ 2 ∂P = ∑ i, lam (Fin.castLE hr i)) ∧
      (∫ ω, ∑ a, g ω a ^ 2 ∂P = ∑ i, lam i) ∧
      (∫ ω, ∑ a, ((U * Uᵀ) *ᵥ g ω) a ^ 2 ∂P) / (∫ ω, ∑ a, g ω a ^ 2 ∂P) =
        (∑ i, lam (Fin.castLE hr i)) / ∑ i, lam i := by
  set c := Fin.castLE hr with hc
  set W := V.submatrix id c with hW
  set D : Matrix (Fin r) (Fin r) ℝ := Matrix.diagonal (lam ∘ c) with hD
  set S := secondMoment P g with hSdef
  have hWW : Wᵀ * W = 1 := by
    have h : Wᵀ * W = (Vᵀ * V).submatrix c c := by
      ext i j
      simp [hW, Matrix.mul_apply]
    rw [h, hV, Matrix.submatrix_one _ (Fin.castLE_injective hr)]
  have hSW : S * W = W * D := by
    ext a i
    have h := congrFun (congrFun hS a) (c i)
    rw [Matrix.mul_diagonal, Matrix.mul_apply] at h
    rw [hD, Matrix.mul_diagonal, Matrix.mul_apply]
    exact h
  have hnum : ∫ ω, ∑ a, ((U * Uᵀ) *ᵥ g ω) a ^ 2 ∂P = ∑ i, lam (c i) := by
    rw [integral_sum_sq (hg.mulVec _), secondMoment_mulVec hg, hU, ← hSdef]
    have h : W * Wᵀ * S * (W * Wᵀ)ᵀ = W * D * Wᵀ := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
      calc W * Wᵀ * S * (W * Wᵀ) = W * Wᵀ * (S * W) * Wᵀ := by simp only [Matrix.mul_assoc]
        _ = W * (Wᵀ * W) * D * Wᵀ := by rw [hSW]; simp only [Matrix.mul_assoc]
        _ = W * D * Wᵀ := by rw [hWW, Matrix.mul_one]
    rw [h, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hWW, Matrix.one_mul, hD,
      Matrix.trace_diagonal]
    rfl
  have hden : ∫ ω, ∑ a, g ω a ^ 2 ∂P = ∑ i, lam i := by
    rw [integral_sum_sq hg, ← hSdef]
    have hVV : V * Vᵀ = 1 := mul_eq_one_comm.1 hV
    have h : S = V * Matrix.diagonal lam * Vᵀ := by
      rw [← hS, Matrix.mul_assoc, hVV, Matrix.mul_one]
    rw [h, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul, Matrix.trace_diagonal]
  exact ⟨hnum, hden, by rw [hnum, hden]⟩

/-- The fair coin on `Bool`. -/
private noncomputable def coin : Measure Bool :=
  (2⁻¹ : ENNReal) • (Measure.dirac false + Measure.dirac true)

private lemma coin_prob : IsProbabilityMeasure coin := ⟨by
  simp only [coin, _root_.smul_apply, _root_.add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two]
  exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top⟩

private lemma integrable_coin (f : Bool → ℝ) : Integrable f coin := by
  have := coin_prob
  exact Integrable.of_finite

private lemma integral_coin (f : Bool → ℝ) : ∫ b, f b ∂coin = (f false + f true) / 2 := by
  have hf1 : Integrable f (Measure.dirac false) := Integrable.of_finite
  have hf2 : Integrable f (Measure.dirac true) := Integrable.of_finite
  rw [coin, integral_smul_measure, integral_add_measure hf1 hf2, integral_dirac, integral_dirac]
  simp
  ring

/-- The gradient of the counterexample: `(2, 0)` or `(0, 1)`, each with probability `1 / 2`. -/
private noncomputable def coinGrad : Bool → Fin 2 → ℝ := fun b => if b then ![0, 1] else ![2, 0]

/-- **Proposition 4 as printed is false** (arXiv 2607.05872, Appendix D and eq. (4)).  All
hypotheses hold, with `n = 2`, `r = 1`, `V = 1`, `λ = (2, 1/2)` and `U = e₁`, for the gradient
equal to `(2, 0)` or `(0, 1)` with probability `1 / 2` each.  But `E[γ_g] = 1 / 2`, whereas
`∑_{i ≤ r} λ_i / ∑_i λ_i = 4 / 5`.  The correct statement, a quotient of expectations, is
`coverage_eq_spectral_mass`. -/
theorem expected_energyFraction_ne_spectral_mass :
    ∃ (P : Measure Bool) (_ : IsProbabilityMeasure P) (g : Bool → Fin 2 → ℝ) (lam : Fin 2 → ℝ)
      (V : Matrix (Fin 2) (Fin 2) ℝ) (U : Matrix (Fin 2) (Fin 1) ℝ) (hr : 1 ≤ 2),
      HasSecondMoments P g ∧ Antitone lam ∧ Vᵀ * V = 1 ∧
      secondMoment P g * V = V * Matrix.diagonal lam ∧ Uᵀ * U = 1 ∧
      U = V.submatrix id (Fin.castLE hr) ∧
      ∫ ω, energyFraction U (g ω) ∂P ≠ (∑ i, lam (Fin.castLE hr i)) / ∑ i, lam i := by
  refine ⟨coin, coin_prob, coinGrad, ![2, 1 / 2], 1,
    (1 : Matrix (Fin 2) (Fin 2) ℝ).submatrix id (Fin.castLE (by norm_num)), by norm_num,
    fun a b => integrable_coin _, ?_, by simp, ?_, ?_, rfl, ?_⟩
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
    norm_num
  · ext a b
    fin_cases a <;> fin_cases b <;>
      simp [secondMoment, integral_coin, coinGrad]
  · ext a b
    fin_cases a
    fin_cases b
    simp [Matrix.mul_apply, Matrix.one_apply]
  · rw [integral_coin]
    simp [energyFraction, coinGrad, Fin.sum_univ_two, Matrix.mulVec, Matrix.mul_apply,
      dotProduct, Matrix.one_apply]
    norm_num

end Coverage

/-! ### Eq. (2): the chordal distance -/

section Chordal

open scoped LeanDLRA.Frobenius

/-- Diagonal entries of `Xᵀ Y` are at most `1` if `X` and `Y` have orthonormal columns. -/
private lemma diag_le_one {l k : Type*} [Fintype l] [DecidableEq k]
    {X Y : Matrix l k ℝ} (hX : Xᵀ * X = 1) (hY : Yᵀ * Y = 1) (i : k) : (Xᵀ * Y) i i ≤ 1 := by
  have h1 := congrFun (congrFun hX i) i
  have h2 := congrFun (congrFun hY i) i
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h1 h2 ⊢
  have h3 : ∑ a, X a i * Y a i ≤ ∑ a, (X a i * X a i + Y a i * Y a i) / 2 :=
    Finset.sum_le_sum fun a _ => by nlinarith [sq_nonneg (X a i - Y a i)]
  rw [← Finset.sum_div, Finset.sum_add_distrib, h1, h2] at h3
  linarith

/-- Orthonormal columns extend to an orthogonal matrix. -/
private lemma exists_orth_extension {ρ r : ℕ} (hρ : ρ ≤ r) {W : Matrix (Fin r) (Fin ρ) ℝ}
    (hW : Wᵀ * W = 1) :
    ∃ B : Matrix (Fin r) (Fin r) ℝ, Bᵀ * B = 1 ∧ W = B.submatrix id (Fin.castLE hρ) := by
  classical
  let v : Fin r → EuclideanSpace ℝ (Fin r) := fun j =>
    if h : j.1 < ρ then WithLp.toLp 2 (W.col ⟨j.1, h⟩) else 0
  let s : Set (Fin r) := {j | j.1 < ρ}
  have hv : Orthonormal ℝ (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    have ha' : a.1 < ρ := ha
    have hb' : b.1 < ρ := hb
    have h := congrFun (congrFun hW ⟨a.1, ha'⟩) ⟨b.1, hb'⟩
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h
    simp only [Set.domRestrict, v, ha', hb', dite_eq_left, PiLp.inner_apply,
      RCLike.inner_apply, conj_trivial, Matrix.col_apply, Subtype.mk.injEq, Fin.mk.injEq,
      ← Fin.ext_iff] at h ⊢
    rw [← h]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (by simp) hv
  refine ⟨ofCols b, transpose_ofCols_mul_ofCols b.orthonormal, ?_⟩
  ext a j
  have hj : (Fin.castLE hρ j).1 < ρ := j.2
  have h := hb (Fin.castLE hρ j) hj
  simp [ofCols_apply, h, v]

/-- Two frames with the same number of orthonormal columns differ by an orthogonal matrix. -/
private lemma exists_orth_map {ρ r : ℕ} (hρ : ρ ≤ r) {W Z : Matrix (Fin r) (Fin ρ) ℝ}
    (hW : Wᵀ * W = 1) (hZ : Zᵀ * Z = 1) :
    ∃ Q : Matrix (Fin r) (Fin r) ℝ, Qᵀ * Q = 1 ∧ Q * Z = W := by
  obtain ⟨A, hA, rfl⟩ := exists_orth_extension hρ hW
  obtain ⟨B, hB, rfl⟩ := exists_orth_extension hρ hZ
  have hBB : B * Bᵀ = 1 := mul_eq_one_comm.1 hB
  refine ⟨A * Bᵀ, ?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc Aᵀ,
      hA, Matrix.one_mul, hBB]
  · set E := (1 : Matrix (Fin r) (Fin r) ℝ).submatrix id (Fin.castLE hρ)
    have hsub : ∀ M : Matrix (Fin r) (Fin r) ℝ, M.submatrix id (Fin.castLE hρ) = M * E :=
      fun M => by
        ext a j
        simp [E, Matrix.mul_apply, Matrix.one_apply]
    rw [hsub A, hsub B, Matrix.mul_assoc, ← Matrix.mul_assoc Bᵀ, hB, Matrix.one_mul]

/-- Only the first `rank R` singular values of `R` are nonzero. -/
private lemma sum_singularValues {r : ℕ} (R : Matrix (Fin r) (Fin r) ℝ) :
    ∑ i : Fin r, (Matrix.toEuclideanLin R).singularValues i =
      ∑ j : Fin R.rank, (Matrix.toEuclideanLin R).singularValues j := by
  have hρ : R.rank ≤ r := by simpa using R.rank_le_width
  rw [Fin.sum_univ_eq_sum_range (fun i => (Matrix.toEuclideanLin R).singularValues i) r,
    Fin.sum_univ_eq_sum_range (fun i => (Matrix.toEuclideanLin R).singularValues i) R.rank]
  symm
  refine Finset.sum_subset (Finset.range_subset_range.2 hρ) fun x _ hx => ?_
  rw [LinearMap.singularValues_eq_zero_iff_le_finrank_range, ← LeanDLRA.SVD.rank_eq_finrank_range]
  simpa using hx

/-- Nuclear-norm duality, upper bound: `tr(Qᵀ R) ≤ ∑ σ_i(R)` for orthogonal `Q`. -/
private lemma trace_le_sum_singularValues {r : ℕ} (R Q : Matrix (Fin r) (Fin r) ℝ)
    (hQ : Qᵀ * Q = 1) :
    Matrix.trace (Qᵀ * R) ≤ ∑ i : Fin r, (Matrix.toEuclideanLin R).singularValues i := by
  obtain ⟨W, Z, σ, hW, hZ, -, -, hσ, hR⟩ := LeanDLRA.SVD.exists_svd R rfl
  have hQZ : (Q * Z)ᵀ * (Q * Z) = 1 := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Qᵀ, hQ, Matrix.one_mul, hZ]
  have e : Matrix.trace (Qᵀ * R) = ∑ j, ((Q * Z)ᵀ * W) j j * σ j := by
    conv_lhs => rw [hR]
    have h : Qᵀ * (W * Matrix.diagonal σ * Zᵀ) = Qᵀ * W * Matrix.diagonal σ * Zᵀ := by
      simp only [Matrix.mul_assoc]
    rw [h, Matrix.trace_mul_comm, Matrix.transpose_mul]
    simp only [Matrix.trace, Matrix.diag, ← Matrix.mul_assoc, Matrix.mul_diagonal]
  rw [e, sum_singularValues]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 := diag_le_one hQZ hW j
  have h2 : 0 ≤ σ j := by
    rw [hσ]
    exact LinearMap.singularValues_nonneg _ _
  rw [hσ j] at h2 ⊢
  nlinarith

/-- Nuclear-norm duality, attainment: `tr(Qᵀ R) = ∑ σ_i(R)` for some orthogonal `Q`. -/
private lemma exists_trace_eq_sum_singularValues {r : ℕ} (R : Matrix (Fin r) (Fin r) ℝ) :
    ∃ Q : Matrix (Fin r) (Fin r) ℝ, Qᵀ * Q = 1 ∧
      Matrix.trace (Qᵀ * R) = ∑ i : Fin r, (Matrix.toEuclideanLin R).singularValues i := by
  have hρ : R.rank ≤ r := by simpa using R.rank_le_width
  obtain ⟨W, Z, σ, hW, hZ, -, -, hσ, hR⟩ := LeanDLRA.SVD.exists_svd R rfl
  obtain ⟨Q, hQ, hQZ⟩ := exists_orth_map hρ hW hZ
  refine ⟨Q, hQ, ?_⟩
  have e : Matrix.trace (Qᵀ * R) = ∑ j, ((Q * Z)ᵀ * W) j j * σ j := by
    conv_lhs => rw [hR]
    have h : Qᵀ * (W * Matrix.diagonal σ * Zᵀ) = Qᵀ * W * Matrix.diagonal σ * Zᵀ := by
      simp only [Matrix.mul_assoc]
    rw [h, Matrix.trace_mul_comm, Matrix.transpose_mul]
    simp only [Matrix.trace, Matrix.diag, ← Matrix.mul_assoc, Matrix.mul_diagonal]
  rw [e, hQZ, hW, sum_singularValues]
  exact Finset.sum_congr rfl fun j _ => by simp [hσ]

variable {m : Type*} [Fintype m]

/-- `cos θ_i = σ_i(U_newᵀ U_old)`, the paper's definition (Appendix A), with the singular values in
decreasing order and `0`-based indices. -/
noncomputable def cosAngle (Unew Uold : Matrix m (Fin r) ℝ) (i : Fin r) : ℝ :=
  (Matrix.toEuclideanLin (Unewᵀ * Uold)).singularValues i

/-- The principal angles `θ_i = arccos σ_i(U_newᵀ U_old)` between `range U_new` and
`range U_old`. -/
noncomputable def angle (Unew Uold : Matrix m (Fin r) ℝ) (i : Fin r) : ℝ :=
  Real.arccos (cosAngle Unew Uold i)

/-- The paper's sign-corrected distance, eq. (2): `‖ΔU‖_F = (2 r - 2 ∑ᵢ cos θ_i)^{1/2}`. -/
noncomputable def chordalDist (Unew Uold : Matrix m (Fin r) ℝ) : ℝ :=
  √(2 * r - 2 * ∑ i, Real.cos (angle Unew Uold i))

/-- `cos θ_i ≥ 0` (arXiv 2607.05872, Appendix A: the `cos θ_i` are singular values). -/
theorem cosAngle_nonneg (Unew Uold : Matrix m (Fin r) ℝ) (i : Fin r) :
    0 ≤ cosAngle Unew Uold i :=
  LinearMap.singularValues_nonneg _ _

variable {Unew Uold : Matrix m (Fin r) ℝ}

/-- The singular values of the cross-Gram matrix of two frames are at most `1`, so that the
principal angles of arXiv 2607.05872, eq. (2), are well defined. -/
theorem cosAngle_le_one (hnew : Unewᵀ * Unew = 1) (hold : Uoldᵀ * Uold = 1) (i : Fin r) :
    cosAngle Unew Uold i ≤ 1 := by
  by_cases hi : i.1 < (Unewᵀ * Uold).rank
  · obtain ⟨W, Z, σ, hW, hZ, -, -, hσ, hR⟩ := LeanDLRA.SVD.exists_svd (Unewᵀ * Uold) rfl
    have hD : (Unew * W)ᵀ * (Uold * Z) = Matrix.diagonal σ := by
      have h : (Unew * W)ᵀ * (Uold * Z) = Wᵀ * (Unewᵀ * Uold) * Z := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
      have h2 : Wᵀ * (W * Matrix.diagonal σ * Zᵀ) * Z =
          (Wᵀ * W) * Matrix.diagonal σ * (Zᵀ * Z) := by
        simp only [Matrix.mul_assoc]
      rw [h]
      refine (congrArg (fun X => Wᵀ * X * Z) hR).trans ?_
      rw [h2, hW, hZ, Matrix.one_mul, Matrix.mul_one]
    have h1 : (Unew * W)ᵀ * (Unew * W) = 1 := by
      rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Unewᵀ, hnew, Matrix.one_mul,
        hW]
    have h2 : (Uold * Z)ᵀ * (Uold * Z) = 1 := by
      rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uoldᵀ, hold, Matrix.one_mul,
        hZ]
    have h3 := diag_le_one h1 h2 ⟨i.1, hi⟩
    rw [hD, Matrix.diagonal_apply_eq, hσ] at h3
    exact h3
  · have h : cosAngle Unew Uold i = 0 := by
      rw [cosAngle, LinearMap.singularValues_eq_zero_iff_le_finrank_range,
        ← LeanDLRA.SVD.rank_eq_finrank_range]
      exact not_lt.1 hi
    rw [h]
    exact zero_le_one

/-- `cos θ_i = σ_i(U_newᵀ U_old)` for the angles `θ_i` of arXiv 2607.05872, eq. (2). -/
theorem cos_angle (hnew : Unewᵀ * Unew = 1) (hold : Uoldᵀ * Uold = 1) (i : Fin r) :
    Real.cos (angle Unew Uold i) = cosAngle Unew Uold i :=
  Real.cos_arccos (by linarith [cosAngle_nonneg Unew Uold i]) (cosAngle_le_one hnew hold i)

/-- The angles of arXiv 2607.05872, eq. (2), lie in `[0, π / 2]`. -/
theorem angle_mem_Icc (Unew Uold : Matrix m (Fin r) ℝ) (i : Fin r) :
    angle Unew Uold i ∈ Set.Icc 0 (Real.pi / 2) :=
  ⟨Real.arccos_nonneg _, Real.arccos_le_pi_div_two.2 (cosAngle_nonneg Unew Uold i)⟩

private lemma chordalDist_eq (hnew : Unewᵀ * Unew = 1) (hold : Uoldᵀ * Uold = 1) :
    chordalDist Unew Uold = √(2 * r - 2 * ∑ i, cosAngle Unew Uold i) := by
  simp only [chordalDist, cos_angle hnew hold]

private lemma sum_cosAngle_le (hnew : Unewᵀ * Unew = 1) (hold : Uoldᵀ * Uold = 1) :
    ∑ i, cosAngle Unew Uold i ≤ r := by
  calc ∑ i, cosAngle Unew Uold i ≤ ∑ _i : Fin r, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => cosAngle_le_one hnew hold i
    _ = r := by simp

private lemma sum_cosAngle_nonneg (Unew Uold : Matrix m (Fin r) ℝ) :
    0 ≤ ∑ i, cosAngle Unew Uold i :=
  Finset.sum_nonneg fun i _ => cosAngle_nonneg Unew Uold i

/-- The expansion of the squared Frobenius distance of two frames. -/
private lemma norm_sq_frames {Q : Matrix (Fin r) (Fin r) ℝ} (hnew : Unewᵀ * Unew = 1)
    (hold : Uoldᵀ * Uold = 1) (hQ : Qᵀ * Q = 1) :
    ‖Unew * Q - Uold‖ ^ 2 = 2 * r - 2 * Matrix.trace (Qᵀ * (Unewᵀ * Uold)) := by
  have h1 : ‖Unew * Q‖ ^ 2 = r := by
    rw [LeanDLRA.Frobenius.norm_mul_of_orthonormal hnew, ← real_inner_self_eq_norm_sq,
      LeanDLRA.Frobenius.inner_eq_trace, hQ, Matrix.trace_one, Fintype.card_fin]
  have h2 : ‖Uold‖ ^ 2 = r := by
    rw [← real_inner_self_eq_norm_sq, LeanDLRA.Frobenius.inner_eq_trace, hold, Matrix.trace_one,
      Fintype.card_fin]
  rw [norm_sub_sq_real, h1, h2, LeanDLRA.Frobenius.inner_eq_trace, Matrix.transpose_mul,
    Matrix.mul_assoc]
  ring

/-- **Appendix A, the raw identity** (arXiv 2607.05872): `‖U_new - U_old‖_F² = 2 r - 2 tr(U_newᵀ
U_old)` for two frames. -/
theorem norm_sub_sq_eq (hnew : Unewᵀ * Unew = 1) (hold : Uoldᵀ * Uold = 1) :
    ‖Unew - Uold‖ ^ 2 = 2 * r - 2 * Matrix.trace (Unewᵀ * Uold) := by
  have h := norm_sq_frames (Q := 1) hnew hold (by simp)
  simpa using h

/-- **Eq. (2), Procrustes form** (arXiv 2607.05872, §2 and Appendix A): the sign-corrected distance
is the Frobenius distance of the frames after the best orthogonal change of basis of `U_new`,

  `(2 r - 2 ∑ᵢ cos θ_i)^{1/2} = min_{Q ∈ O(r)} ‖U_new Q - U_old‖_F`,
  `cos θ_i = σ_i(U_newᵀ U_old)`.

The paper defines `‖ΔU‖_F` by the left side and calls it the chordal Frobenius distance of the
frames; this theorem is the statement that justifies that name. -/
theorem chordalDist_isLeast (hnew : Unewᵀ * Unew = 1) (hold : Uoldᵀ * Uold = 1) :
    IsLeast (Set.range fun Q : O r => ‖Unew * Q.1 - Uold‖) (chordalDist Unew Uold) := by
  obtain ⟨Q, hQ, htr⟩ := exists_trace_eq_sum_singularValues (Unewᵀ * Uold)
  rw [chordalDist_eq hnew hold]
  constructor
  · refine ⟨⟨Q, (Matrix.mem_orthogonalGroup_iff' (Fin r) ℝ).2 hQ⟩, ?_⟩
    change ‖Unew * Q - Uold‖ = _
    rw [← Real.sqrt_sq (norm_nonneg (Unew * Q - Uold)), norm_sq_frames hnew hold hQ, htr]
    rfl
  · rintro _ ⟨Q', rfl⟩
    have hQ' : Q'.1ᵀ * Q'.1 = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin r) ℝ).1 Q'.2
    change _ ≤ ‖Unew * Q'.1 - Uold‖
    rw [← Real.sqrt_sq (norm_nonneg (Unew * Q'.1 - Uold)), norm_sq_frames hnew hold hQ']
    refine Real.sqrt_le_sqrt ?_
    have := trace_le_sum_singularValues (Unewᵀ * Uold) Q'.1 hQ'
    simp only [cosAngle]
    linarith

/-- **Eq. (2), the bounds** (arXiv 2607.05872, §2): `0 ≤ ‖ΔU‖_F ≤ √(2 r)`. -/
theorem chordalDist_mem_Icc (hnew : Unewᵀ * Unew = 1) (hold : Uoldᵀ * Uold = 1) :
    chordalDist Unew Uold ∈ Set.Icc 0 √(2 * r) := by
  rw [chordalDist_eq hnew hold]
  exact ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt (by linarith [sum_cosAngle_nonneg Unew Uold])⟩

private lemma sum_cosAngle_eq_zero_iff :
    ∑ i, cosAngle Unew Uold i = 0 ↔ Unewᵀ * Uold = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => cosAngle_nonneg Unew Uold i]
  constructor
  · intro h
    have hT : (Matrix.toEuclideanLin (Unewᵀ * Uold)).singularValues = 0 := by
      ext n
      by_cases hn : n < r
      · exact h ⟨n, hn⟩ (Finset.mem_univ _)
      · exact LinearMap.singularValues_of_finrank_le _ (by simpa using hn)
    exact (Matrix.toEuclideanLin).map_eq_zero_iff.1
      ((LinearMap.singularValues_eq_zero_iff _).1 hT)
  · intro h i _
    simp [cosAngle, h, LinearMap.singularValues_zero]

/-- **Eq. (2), the maximum** (arXiv 2607.05872, §2): `‖ΔU‖_F = √(2 r)` if and only if
`U_newᵀ U_old = 0`, i.e. the two subspaces are orthogonal, if and only if all `θ_i = π / 2`.  (Such
frames exist only if `m ≥ 2 r`.) -/
theorem chordalDist_eq_sqrt_iff (hnew : Unewᵀ * Unew = 1) (hold : Uoldᵀ * Uold = 1) :
    (chordalDist Unew Uold = √(2 * r) ↔ Unewᵀ * Uold = 0) ∧
      (chordalDist Unew Uold = √(2 * r) ↔ ∀ i, angle Unew Uold i = Real.pi / 2) := by
  have h1 : chordalDist Unew Uold = √(2 * r) ↔ ∑ i, cosAngle Unew Uold i = 0 := by
    rw [chordalDist_eq hnew hold,
      Real.sqrt_inj (by linarith [sum_cosAngle_le hnew hold]) (by positivity)]
    constructor <;> intro h <;> linarith
  have h2 : ∑ i, cosAngle Unew Uold i = 0 ↔ ∀ i, angle Unew Uold i = Real.pi / 2 := by
    rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => cosAngle_nonneg Unew Uold i]
    simp [angle, Real.arccos_eq_pi_div_two]
  exact ⟨h1.trans sum_cosAngle_eq_zero_iff, h1.trans h2⟩

/-- **Eq. (2), the value `0`** (arXiv 2607.05872, §2): `‖ΔU‖_F = 0` if and only if the subspace is
unchanged, `U_new U_newᵀ = U_old U_oldᵀ`. -/
theorem chordalDist_eq_zero_iff (hnew : Unewᵀ * Unew = 1) (hold : Uoldᵀ * Uold = 1) :
    chordalDist Unew Uold = 0 ↔ Unew * Unewᵀ = Uold * Uoldᵀ := by
  have hleast := chordalDist_isLeast hnew hold
  constructor
  · intro h
    obtain ⟨Q, hQ⟩ := hleast.1
    rw [h] at hQ
    have h0 : Unew * Q.1 = Uold := sub_eq_zero.1 (norm_eq_zero.1 hQ)
    have hQ' : Q.1 * Q.1ᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin r) ℝ).1 Q.2
    rw [← h0, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Q.1, hQ', Matrix.one_mul]
  · intro h
    have hQ : (Unewᵀ * Uold)ᵀ * (Unewᵀ * Uold) = 1 := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
        ← Matrix.mul_assoc Unew, h, Matrix.mul_assoc, hold, Matrix.mul_one, hold]
    have hU : Unew * (Unewᵀ * Uold) = Uold := by
      rw [← Matrix.mul_assoc, h, Matrix.mul_assoc, hold, Matrix.mul_one]
    have h1 := hleast.2 ⟨⟨Unewᵀ * Uold, (Matrix.mem_orthogonalGroup_iff' (Fin r) ℝ).2 hQ⟩, rfl⟩
    simp only [hU, sub_self, norm_zero] at h1
    exact le_antisymm h1 (chordalDist_mem_Icc hnew hold).1

/-- **Eq. (2), sign invariance** (arXiv 2607.05872, Appendix A: "sign-invariant by construction"):
`‖ΔU‖_F` does not change under an orthogonal change of basis of either frame, in particular under
column sign flips.  It depends only on the two subspaces. -/
theorem chordalDist_mul_orthogonal (hnew : Unewᵀ * Unew = 1) (hold : Uoldᵀ * Uold = 1)
    (Q₁ Q₂ : O r) : chordalDist (Unew * Q₁.1) (Uold * Q₂.1) = chordalDist Unew Uold := by
  have h₁ : Q₁.1ᵀ * Q₁.1 = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin r) ℝ).1 Q₁.2
  have h₂ : Q₂.1ᵀ * Q₂.1 = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin r) ℝ).1 Q₂.2
  have h₂' : Q₂.1 * Q₂.1ᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin r) ℝ).1 Q₂.2
  have hnew' : (Unew * Q₁.1)ᵀ * (Unew * Q₁.1) = 1 := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Unewᵀ, hnew, Matrix.one_mul, h₁]
  have hold' : (Uold * Q₂.1)ᵀ * (Uold * Q₂.1) = 1 := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uoldᵀ, hold, Matrix.one_mul, h₂]
  have key : ∀ Q : O r, ‖Unew * Q₁.1 * Q.1 - Uold * Q₂.1‖ =
      ‖Unew * (Q₁ * Q * Q₂⁻¹).1 - Uold‖ := fun Q => by
    have hinv : (Q₂⁻¹).1 = Q₂.1ᵀ := rfl
    have h : Unew * (Q₁ * Q * Q₂⁻¹).1 - Uold = (Unew * Q₁.1 * Q.1 - Uold * Q₂.1) * Q₂.1ᵀ := by
      simp only [Submonoid.coe_mul, Matrix.sub_mul, Matrix.mul_assoc, h₂', Matrix.mul_one, hinv]
    rw [h, LeanDLRA.Frobenius.norm_mul_transpose_of_orthonormal h₂]
  have hL := chordalDist_isLeast hnew hold
  have hL' := chordalDist_isLeast hnew' hold'
  refine le_antisymm ?_ ?_
  · obtain ⟨Q, hQ⟩ := hL.1
    rw [← hQ]
    have := hL'.2 ⟨Q₁⁻¹ * Q * Q₂, rfl⟩
    simp only at this
    refine this.trans (le_of_eq ?_)
    rw [key]
    simp [mul_assoc]
  · obtain ⟨Q, hQ⟩ := hL'.1
    rw [← hQ]
    simp only
    rw [key]
    exact hL.2 ⟨_, rfl⟩

/-- **Appendix A, sign alignment** (arXiv 2607.05872): aligning the column signs of `U_new` and then
taking the Frobenius difference upper-bounds `‖ΔU‖_F`. -/
theorem chordalDist_le_signAligned (hnew : Unewᵀ * Unew = 1) (hold : Uoldᵀ * Uold = 1)
    {s : Fin r → ℝ} (hs : ∀ i, s i ^ 2 = 1) :
    chordalDist Unew Uold ≤ ‖Unew * Matrix.diagonal s - Uold‖ := by
  have hD : (Matrix.diagonal s)ᵀ * Matrix.diagonal s = 1 := by
    rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    simpa [sq] using hs i
  exact (chordalDist_isLeast hnew hold).2
    ⟨⟨Matrix.diagonal s, (Matrix.mem_orthogonalGroup_iff' (Fin r) ℝ).2 hD⟩, rfl⟩

/-- **Appendix A, equality case of the sign alignment** (arXiv 2607.05872): if the columns of the
two frames are principal vectors, i.e. `U_newᵀ U_old = diag(c)` with `c ≥ 0`, then `‖ΔU‖_F` is the
raw Frobenius distance `‖U_new - U_old‖_F`. -/
theorem chordalDist_eq_norm_sub_of_principal (hnew : Unewᵀ * Unew = 1) (hold : Uoldᵀ * Uold = 1)
    {c : Fin r → ℝ} (hc : ∀ i, 0 ≤ c i) (hR : Unewᵀ * Uold = Matrix.diagonal c) :
    chordalDist Unew Uold = ‖Unew - Uold‖ := by
  have hleast := chordalDist_isLeast hnew hold
  refine le_antisymm ?_ ?_
  · have h := hleast.2 ⟨1, rfl⟩
    simpa using h
  · obtain ⟨Q, hQ⟩ := hleast.1
    rw [← hQ]
    have hQ' : Q.1ᵀ * Q.1 = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin r) ℝ).1 Q.2
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    rw [norm_sub_sq_eq hnew hold, norm_sq_frames hnew hold hQ', hR]
    have h : Matrix.trace (Q.1ᵀ * Matrix.diagonal c) ≤ Matrix.trace (Matrix.diagonal c) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal, Matrix.transpose_apply,
        Matrix.diagonal_apply_eq]
      refine Finset.sum_le_sum fun i _ => ?_
      have := (abs_le.1 (O.abs_entry_le Q i i)).2
      nlinarith [hc i]
    linarith

/-- **The appendix's remark on the ceiling is false for the raw distance** (arXiv 2607.05872,
Appendix A: `√(2r)` "is the maximum Frobenius distance between two `m × r` orthonormal matrices").
For `U_new = -U_old` the raw distance is `2 √r > √(2 r)`.  The ceiling `√(2 r)` is correct for the
sign-corrected `‖ΔU‖_F` of eq. (2) (`chordalDist_mem_Icc`), which is what the paper reports. -/
theorem raw_distance_exceeds_ceiling (hr : 0 < r) (hold : Uoldᵀ * Uold = 1) :
    ((-Uold)ᵀ * (-Uold) = 1) ∧ ‖-Uold - Uold‖ = 2 * √r ∧ √(2 * r) < ‖-Uold - Uold‖ := by
  have h1 : (-Uold)ᵀ * (-Uold) = 1 := by
    rw [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg, hold]
  have h2 : ‖-Uold - Uold‖ ^ 2 = 4 * r := by
    have h := norm_sub_sq_eq h1 hold
    rw [Matrix.transpose_neg, Matrix.neg_mul, hold, Matrix.trace_neg, Matrix.trace_one,
      Fintype.card_fin] at h
    rw [h]
    ring
  have h3 : ‖-Uold - Uold‖ = 2 * √r := by
    rw [← Real.sqrt_sq (norm_nonneg (-Uold - Uold)), h2]
    rw [show (4 : ℝ) * r = 2 ^ 2 * r by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq (by simp)]
  refine ⟨h1, h3, ?_⟩
  rw [h3, show (2 : ℝ) * r = 2 * r from rfl, Real.sqrt_mul (by positivity)]
  have hr' : 0 < √(r : ℝ) := Real.sqrt_pos.2 (by positivity)
  have h4 : √(2 : ℝ) < 2 := by
    rw [Real.sqrt_lt' (by positivity)]
    norm_num
  exact mul_lt_mul_of_pos_right h4 hr'

end Chordal

end LeanDLRA.Literature.P2607_05872
