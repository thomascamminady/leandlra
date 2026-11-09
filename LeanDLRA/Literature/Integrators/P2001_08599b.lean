import LeanDLRA.Integrators.BUG
import LeanDLRA.LinearAlgebra.Factorization.Defs
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2001.08599: Chart-based splitting from the fibre-bundle structure of M_r

The explicit chart `θ_Z` of Section 2.1 (arXiv 2001.08599) on the neighbourhood
`U_Z = {(U + U⊥ X) H (V + V⊥ Y)ᵀ : (X, Y, H) ∈ ℝ^{(n-r)×r} × ℝ^{(m-r)×r} × GL_r}` of a rank-`r`
matrix `Z = U G Vᵀ`, with `U⁺ = (UᵀU)⁻¹Uᵀ`.  This is the chart-level content of
Proposition 2.1: the
chart map is a bijection from `U_Z` onto the full parameter space
`ℝ^{(n-r)×r} × ℝ^{(m-r)×r} × GL_r` with the stated inverse, `U_Z` consists of rank-`r`
matrices and contains `Z` with `θ_Z(Z) = (0,0,G)`,
and the parameter space has dimension `r(n+m-r)`.  Mathlib has no Grassmannian manifold or the
required analytic structure, so smoothness of transition maps, openness of `U_Z`, and the principal
`GL_r`-bundle structure are not formalized.

The paper's `U⁺ = (UᵀU)⁻¹Uᵀ` is the core Gram pseudoinverse `Matrix.gramPinv`
(`LinearAlgebra/Factorization/Defs.lean`), which is the Moore–Penrose inverse for the
full-column-rank bases used here (`Matrix.gramPinv_eq_pinv`).  The local `pinv` of an earlier
version of this file was the same definition (unification batch C1).
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2001_08599

variable {ι κ ρ σ τ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ] [Fintype σ] [Fintype τ]
  [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ]

/-- Data of the paper: `U` (`n × r`) of full column rank and `U⊥` (`n × (n-r)`) of full column
rank with `U⊥ᵀ U = 0`; the number of columns adds up to `n`. -/
structure IsChartBasis (U : Matrix ι ρ ℝ) (Up : Matrix ι σ ℝ) : Prop where
  gram : IsUnit (Uᵀ * U).det
  gram_perp : IsUnit (Upᵀ * Up).det
  orth : Upᵀ * U = 0
  card_eq : Fintype.card ρ + Fintype.card σ = Fintype.card ι

/-- The inverse chart `θ_Z⁻¹ (X, Y, H) = (U + U⊥ X) H (V + V⊥ Y)ᵀ`. -/
def chartInv (U : Matrix ι ρ ℝ) (Up : Matrix ι σ ℝ) (V : Matrix κ ρ ℝ) (Vp : Matrix κ τ ℝ)
    (p : Matrix σ ρ ℝ × Matrix τ ρ ℝ × Matrix ρ ρ ℝ) : Matrix ι κ ℝ :=
  (U + Up * p.1) * p.2.2 * (V + Vp * p.2.1)ᵀ

/-- The parameter space `ℝ^{(n-r)×r} × ℝ^{(m-r)×r} × GL_r`. -/
def params : Set (Matrix σ ρ ℝ × Matrix τ ρ ℝ × Matrix ρ ρ ℝ) := {p | IsUnit p.2.2.det}

/-- The neighbourhood `U_Z`. -/
def nbhd (U : Matrix ι ρ ℝ) (Up : Matrix ι σ ℝ) (V : Matrix κ ρ ℝ) (Vp : Matrix κ τ ℝ) :
    Set (Matrix ι κ ℝ) :=
  chartInv U Up V Vp '' params

/-- The chart `θ_Z (W) = (U⊥⁺ W (V⁺)ᵀ (U⁺ W (V⁺)ᵀ)⁻¹, V⊥⁺ Wᵀ (U⁺)ᵀ (V⁺ Wᵀ (U⁺)ᵀ)⁻¹, U⁺ W (V⁺)ᵀ)`. -/
noncomputable def chart (U : Matrix ι ρ ℝ) (Up : Matrix ι σ ℝ) (V : Matrix κ ρ ℝ)
    (Vp : Matrix κ τ ℝ) (W : Matrix ι κ ℝ) :
    Matrix σ ρ ℝ × Matrix τ ρ ℝ × Matrix ρ ρ ℝ :=
  (Up.gramPinv * W * (V.gramPinv)ᵀ * (U.gramPinv * W * (V.gramPinv)ᵀ)⁻¹,
   Vp.gramPinv * Wᵀ * (U.gramPinv)ᵀ * (V.gramPinv * Wᵀ * (U.gramPinv)ᵀ)⁻¹,
   U.gramPinv * W * (V.gramPinv)ᵀ)

section
variable {U : Matrix ι ρ ℝ} {Up : Matrix ι σ ℝ} {V : Matrix κ ρ ℝ} {Vp : Matrix κ τ ℝ}

/-- `A⁺ A = 1` for `A` of full column rank (the core `Matrix.gramPinv_mul_self`). -/
lemma pinv_mul_self {a b : Type*} [Fintype a] [Fintype b] [DecidableEq b] {A : Matrix a b ℝ}
    (h : IsUnit (Aᵀ * A).det) : A.gramPinv * A = 1 :=
  Matrix.gramPinv_mul_self h

/-- `U⁺ U⊥ = 0`. -/
lemma pinv_mul_perp (hU : IsChartBasis U Up) : U.gramPinv * Up = 0 := by
  unfold Matrix.gramPinv
  have : Uᵀ * Up = 0 := by
    have := congrArg Matrix.transpose hU.orth
    simpa [Matrix.transpose_mul] using this
  rw [Matrix.mul_assoc, this, Matrix.mul_zero]

/-- `U⁺ (U + U⊥ X) = 1`. -/
lemma pinv_mul_chartLeft (hU : IsChartBasis U Up) (X : Matrix σ ρ ℝ) :
    U.gramPinv * (U + Up * X) = 1 := by
  rw [Matrix.mul_add, pinv_mul_self hU.gram, ← Matrix.mul_assoc, pinv_mul_perp hU]
  simp

/-- `U⊥⁺ (U + U⊥ X) = X`. -/
lemma pinvperp_mul_chartLeft (hU : IsChartBasis U Up) (X : Matrix σ ρ ℝ) :
    Up.gramPinv * (U + Up * X) = X := by
  rw [Matrix.mul_add, ← Matrix.mul_assoc, pinv_mul_self hU.gram_perp]
  have : Up.gramPinv * U = 0 := by
    unfold Matrix.gramPinv
    rw [Matrix.mul_assoc, hU.orth, Matrix.mul_zero]
  rw [this]; simp

/-- `(A + A⊥ Z)ᵀ (A⁺)ᵀ = 1`. -/
lemma chartT_mul_pinvT {a c : Type*} [Fintype a] [Fintype c] [DecidableEq c]
    {A : Matrix a ρ ℝ} {Ap : Matrix a c ℝ} (hA : IsChartBasis A Ap) (Z : Matrix c ρ ℝ) :
    (A + Ap * Z)ᵀ * (A.gramPinv)ᵀ = 1 := by
  rw [← Matrix.transpose_mul, pinv_mul_chartLeft hA, Matrix.transpose_one]

end

/-- **Prop. 2.1 (chart part)**, arXiv 2001.08599, Prop. 2.1: `θ_Z` is a left inverse of the
parametrisation `θ_Z⁻¹` on the whole parameter space `ℝ^{(n-r)×r} × ℝ^{(m-r)×r} × GL_r`,
i.e. `θ_Z (θ_Z⁻¹ (X,Y,H)) = (X,Y,H)` for every `H ∈ GL_r`.  Here `U⁺ = (UᵀU)⁻¹Uᵀ`, and
`U⊥`, `V⊥` are as in the paper.  Only the chart part of the proposition is proved. -/
theorem chart_chartInv {U : Matrix ι ρ ℝ} {Up : Matrix ι σ ℝ} {V : Matrix κ ρ ℝ}
    {Vp : Matrix κ τ ℝ} (hU : IsChartBasis U Up) (hV : IsChartBasis V Vp)
    {p : Matrix σ ρ ℝ × Matrix τ ρ ℝ × Matrix ρ ρ ℝ} (hp : p ∈ params) :
    chart U Up V Vp (chartInv U Up V Vp p) = p := by
  obtain ⟨X, Y, H⟩ := p
  have hdet : IsUnit H.det := hp
  have hdetT : IsUnit Hᵀ.det := by simpa using hdet
  have key1 : U.gramPinv * chartInv U Up V Vp (X, Y, H) * (V.gramPinv)ᵀ = H := by
    calc _ = (U.gramPinv * (U + Up * X)) * H * ((V + Vp * Y)ᵀ * (V.gramPinv)ᵀ) := by
          simp only [chartInv, Matrix.mul_assoc]
      _ = H := by rw [pinv_mul_chartLeft hU, chartT_mul_pinvT hV Y]; simp
  have key2 : Up.gramPinv * chartInv U Up V Vp (X, Y, H) * (V.gramPinv)ᵀ = X * H := by
    calc _ = (Up.gramPinv * (U + Up * X)) * H * ((V + Vp * Y)ᵀ * (V.gramPinv)ᵀ) := by
          simp only [chartInv, Matrix.mul_assoc]
      _ = X * H := by rw [pinvperp_mul_chartLeft hU, chartT_mul_pinvT hV Y]; simp
  have key3 : V.gramPinv * (chartInv U Up V Vp (X, Y, H))ᵀ * (U.gramPinv)ᵀ = Hᵀ := by
    calc _ = (V.gramPinv * (V + Vp * Y)) * Hᵀ * ((U + Up * X)ᵀ * (U.gramPinv)ᵀ) := by
          simp only [chartInv, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = Hᵀ := by rw [pinv_mul_chartLeft hV, chartT_mul_pinvT hU X]; simp
  have key4 : Vp.gramPinv * (chartInv U Up V Vp (X, Y, H))ᵀ * (U.gramPinv)ᵀ = Y * Hᵀ := by
    calc _ = (Vp.gramPinv * (V + Vp * Y)) * Hᵀ * ((U + Up * X)ᵀ * (U.gramPinv)ᵀ) := by
          simp only [chartInv, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = Y * Hᵀ := by rw [pinvperp_mul_chartLeft hV, chartT_mul_pinvT hU X]; simp
  unfold chart
  simp only [Prod.mk.injEq]
  rw [key1, key2, key3, key4]
  refine ⟨?_, ?_, rfl⟩
  · rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
  · rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdetT, Matrix.mul_one]

/-- **Prop. 2.1 (chart part)**, arXiv 2001.08599, Prop. 2.1: `θ_Z` is a bijection from the
neighbourhood `U_Z = {(U + U⊥X) H (V + V⊥Y)ᵀ}` onto the parameter space
`ℝ^{(n-r)×r} × ℝ^{(m-r)×r} × GL_r`, with inverse `(X,Y,H) ↦ (U + U⊥X) H (V + V⊥Y)ᵀ`
(unique parametrisation).  Only the chart part of the proposition is proved. -/
theorem chart_bijOn {U : Matrix ι ρ ℝ} {Up : Matrix ι σ ℝ} {V : Matrix κ ρ ℝ}
    {Vp : Matrix κ τ ℝ} (hU : IsChartBasis U Up) (hV : IsChartBasis V Vp) :
    BijOn (chart U Up V Vp) (nbhd U Up V Vp) params := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    rwa [chart_chartInv hU hV hp]
  · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ h
    rw [chart_chartInv hU hV hp, chart_chartInv hU hV hq] at h
    rw [h]
  · intro p hp
    exact ⟨_, ⟨p, hp, rfl⟩, chart_chartInv hU hV hp⟩

/-- **Prop. 2.1 (chart part)**, arXiv 2001.08599, Prop. 2.1: the parametrisation
`θ_Z⁻¹ (X,Y,H) = (U + U⊥X) H (V + V⊥Y)ᵀ` is injective on `ℝ^{(n-r)×r} × ℝ^{(m-r)×r} × GL_r`. -/
theorem chartInv_injOn {U : Matrix ι ρ ℝ} {Up : Matrix ι σ ℝ} {V : Matrix κ ρ ℝ}
    {Vp : Matrix κ τ ℝ} (hU : IsChartBasis U Up) (hV : IsChartBasis V Vp) :
    InjOn (chartInv U Up V Vp) params := by
  intro p hp q hq h
  have := congrArg (chart U Up V Vp) h
  rwa [chart_chartInv hU hV hp, chart_chartInv hU hV hq] at this

/-- **Prop. 2.1 (chart part)**, arXiv 2001.08599, Prop. 2.1: every matrix of `U_Z` has rank
exactly `r` (so `U_Z ⊆ M_r(ℝ^{n×m})`), where `r = card ρ`. -/
theorem rank_of_mem_nbhd {U : Matrix ι ρ ℝ} {Up : Matrix ι σ ℝ} {V : Matrix κ ρ ℝ}
    {Vp : Matrix κ τ ℝ} (hU : IsChartBasis U Up) (hV : IsChartBasis V Vp)
    {W : Matrix ι κ ℝ} (hW : W ∈ nbhd U Up V Vp) : W.rank = Fintype.card ρ := by
  obtain ⟨⟨X, Y, H⟩, hp, rfl⟩ := hW
  have hdet : IsUnit H.det := hp
  have hH : H.rank = Fintype.card ρ := by
    rw [Matrix.rank_of_isUnit H ((Matrix.isUnit_iff_isUnit_det H).2 hdet)]
  have hle : (chartInv U Up V Vp (X, Y, H)).rank ≤ H.rank := by
    unfold chartInv
    calc _ ≤ ((U + Up * X) * H).rank := Matrix.rank_mul_le_left _ _
      _ ≤ H.rank := Matrix.rank_mul_le_right _ _
  have key1 : U.gramPinv * chartInv U Up V Vp (X, Y, H) * (V.gramPinv)ᵀ = H := by
    calc _ = (U.gramPinv * (U + Up * X)) * H * ((V + Vp * Y)ᵀ * (V.gramPinv)ᵀ) := by
          simp only [chartInv, Matrix.mul_assoc]
      _ = H := by rw [pinv_mul_chartLeft hU, chartT_mul_pinvT hV Y]; simp
  have hge : H.rank ≤ (chartInv U Up V Vp (X, Y, H)).rank := by
    calc H.rank = (U.gramPinv * chartInv U Up V Vp (X, Y, H) * (V.gramPinv)ᵀ).rank := by rw [key1]
      _ ≤ (U.gramPinv * chartInv U Up V Vp (X, Y, H)).rank := Matrix.rank_mul_le_left _ _
      _ ≤ _ := Matrix.rank_mul_le_right _ _
  exact le_antisymm (hle.trans hH.le) (hH ▸ hge)

/-- **Prop. 2.1 (chart part)**, arXiv 2001.08599, Prop. 2.1 and Sect. 2.1: for `Z = U G Vᵀ` with
`G ∈ GL_r`, `Z ∈ U_Z` and `θ_Z(Z) = (0, 0, G)`. -/
theorem chart_base {U : Matrix ι ρ ℝ} {Up : Matrix ι σ ℝ} {V : Matrix κ ρ ℝ}
    {Vp : Matrix κ τ ℝ} (hU : IsChartBasis U Up) (hV : IsChartBasis V Vp)
    {G : Matrix ρ ρ ℝ} (hG : IsUnit G.det) :
    U * G * Vᵀ ∈ nbhd U Up V Vp ∧ chart U Up V Vp (U * G * Vᵀ) = (0, 0, G) := by
  have hp : ((0 : Matrix σ ρ ℝ), (0 : Matrix τ ρ ℝ), G) ∈ params := hG
  have h : chartInv U Up V Vp (0, 0, G) = U * G * Vᵀ := by simp [chartInv]
  refine ⟨⟨_, hp, h⟩, ?_⟩
  rw [← h]
  exact chart_chartInv hU hV hp

omit [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ] in
/-- **Prop. 2.1 (dimension)**, arXiv 2001.08599, Prop. 2.1: the parameter space
`ℝ^{(n-r)×r} × ℝ^{(m-r)×r} × ℝ^{r×r}` (the model space of the manifold) has dimension
`r(n+m-r)`, where `n = card ι`, `m = card κ`, `r = card ρ`, `n - r = card σ`, `m - r = card τ`.
Only the dimension of the model space is proved, not that `M_r` is a manifold. -/
theorem finrank_params (hσ : Fintype.card ρ + Fintype.card σ = Fintype.card ι)
    (hτ : Fintype.card ρ + Fintype.card τ = Fintype.card κ) :
    Module.finrank ℝ (Matrix σ ρ ℝ × Matrix τ ρ ℝ × Matrix ρ ρ ℝ) =
      Fintype.card ρ * (Fintype.card ι + Fintype.card κ - Fintype.card ρ) := by
  simp only [Module.finrank_prod, Module.finrank_matrix, Module.finrank_self]
  have h1 : Fintype.card ι + Fintype.card κ - Fintype.card ρ
      = Fintype.card ρ + Fintype.card σ + Fintype.card τ := by omega
  rw [h1]; ring

/-- Non-vacuity: the hypotheses of the chart theorems hold, e.g. for the coordinate splitting
`ι = ρ ⊕ σ`, `U = [I; 0]`, `U⊥ = [0; I]`. -/
theorem isChartBasis_example :
    IsChartBasis (ι := ρ ⊕ σ)
      (Matrix.of fun (i : ρ ⊕ σ) (j : ρ) => if i = Sum.inl j then (1 : ℝ) else 0)
      (Matrix.of fun (i : ρ ⊕ σ) (k : σ) => if i = Sum.inr k then (1 : ℝ) else 0) := by
  have h1 : (Matrix.of fun (i : ρ ⊕ σ) (j : ρ) => if i = Sum.inl j then (1 : ℝ) else 0)ᵀ *
      (Matrix.of fun (i : ρ ⊕ σ) (j : ρ) => if i = Sum.inl j then (1 : ℝ) else 0) = 1 := by
    ext a b
    simp [Matrix.mul_apply, Matrix.one_apply, Matrix.transpose_apply, eq_comm]
  have h2 : (Matrix.of fun (i : ρ ⊕ σ) (j : σ) => if i = Sum.inr j then (1 : ℝ) else 0)ᵀ *
      (Matrix.of fun (i : ρ ⊕ σ) (j : σ) => if i = Sum.inr j then (1 : ℝ) else 0) = 1 := by
    ext a b
    simp [Matrix.mul_apply, Matrix.one_apply, Matrix.transpose_apply, eq_comm]
  refine ⟨?_, ?_, ?_, by simp⟩
  · rw [h1]; simp
  · rw [h2]; simp
  · ext a b
    simp [Matrix.mul_apply]

/-- The local Gram pseudoinverse of this file, replaced by the core `Matrix.gramPinv` (same
definition, `(AᵀA)⁻¹Aᵀ`). -/
@[deprecated (since := "2026-11-09")] alias pinv := Matrix.gramPinv

end LeanDLRA.Literature.P2001_08599
