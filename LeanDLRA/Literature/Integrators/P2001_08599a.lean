import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.Exactness
import LeanDLRA.LinearAlgebra.Factorization.Defs
import LeanDLRA.Literature.Integrators.P2001_08599b
import LeanDLRA.Matrix.GaugeODE
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2001.08599: Chart-based splitting from the fibre-bundle structure of M_r

Formalized parts of "A new splitting algorithm for dynamical low-rank approximation motivated by
the fibre bundle structure of matrix manifolds":

* **Prop. 2.2 / eq. (7)** (`prop_2_2`, `tangentEquiv`): for `Z = U G Vᵀ` with `U`, `V` of full
  column rank, `G` invertible, `U⊥`, `V⊥` bases of the orthogonal complements, the tangent map
  `(δX, δY, δH) ↦ U⊥ δX G Vᵀ + U G (V⊥ δY)ᵀ + U δH Vᵀ` is injective, its range is
  `{U B + C Vᵀ}`, and the pseudo-inverse formulas of (7) invert it.  The hypotheses are
  shown satisfiable by `isChartData_example`.
* **Eqs. (8)-(9)** (`tangentMap_eq_tangentProjection_iff`): `T_Z i (Ẋ, Ẏ, Ḣ) = P_T F` iff the chart
  ODE right-hand sides of (9) hold, pointwise, with `P_T F = P_U⊥ F P_V + P_U F P_V⊥ + P_U F P_V`;
  for orthonormal `U`, `V` this is the library's `tangentProj`.  The orthonormal-gauge
  factor ODEs (13) are already in `LeanDLRA.hasDerivAt_factorProduct_tangentProj_iff_factorODE`
  (`Matrix/GaugeODE.lean`) and are not repeated.
* **Eqs. (17)-(18)** (`splitting_direct_sum`): `P₁ + P₂ + P₃ = P_T` with pairwise
  orthogonal orthogonal-projector summands (the "direct sum decomposition of the tangent space"
  stated after (18)); the splitting integrator, Prop. A.1 (the sub-flows (27)-(29)) and the error
  analysis are not formalized.
* **Lemma 3.11** (`lemma_3_11`, `ksl_iterate_eq`, `chart_iterate_eq`): one KSL step and one
  chart-based step (explicit flux, QR encoded by its defining equations, orthonormal `U₀`, `V₀`)
  coincide, and both equal `Y₀ + h F Q₀ + h P₁ F (1 - Q₀)` (the formula from the proof of the
  cited KSL exactness theorem, arXiv 1301.1058, Theorem 4.1).  The paper's claim is for whole
  sequences; only one step is formalized.
* **Prop. 3.12** (`prop_3_12`, `prop_3_12_literal_false`): as stated in the paper (bounded
  rank `r`, no further condition) the exactness claim is false when the QR factor of a
  rank-deficient `K₁` is arbitrary, even for `A(t)` of rank exactly `r`; with rank exactly `r` at
  `t_{k-1}` and `V(t_k)ᵀ V(t_{k-1})` invertible it is proved via Lemma 3.11 and the library's KSL
  exactness.

## Pseudoinverses and chart data

The paper's `U⁺ = (UᵀU)⁻¹Uᵀ` is the core Gram pseudoinverse `Matrix.gramPinv`
(`LinearAlgebra/Factorization/Defs.lean`); it is the Moore–Penrose inverse for the
full-column-rank matrices used here (`Matrix.gramPinv_eq_pinv`).  The local `pinvL` of an earlier
version of this file was the same definition (unification batch C1).  The data `IsChartData` of
Section 2.1 is equivalent to two `IsChartBasis` (the chart data of `P2001_08599b`) and an invertible
`G` (`isChartData_iff`): the completeness `U U⁺ + U⊥ U⊥⁺ = 1` is the dimension count
`r + (n - r) = n`.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2001_08599

variable {m n r p q : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype p] [Fintype q]
  [DecidableEq r] [DecidableEq p] [DecidableEq q]

/-! ### The chart and its tangent map (Section 2.1) -/

/-- The data of Section 2.1: `U ∈ ℝ^{m×r}`, `V ∈ ℝ^{n×r}` of full column rank, `G` invertible,
and matrices `Up = U⊥`, `Vp = V⊥` of full column rank with `U⊥ᵀ U = 0`, `V⊥ᵀ V = 0`, spanning the
orthogonal complements (`U U⁺ + U⊥ U⊥⁺ = 1`, which for `U⊥ ∈ ℝ^{m×(m-r)}` of full column rank
with `U⊥ᵀ U = 0` is equivalent to the dimension count). -/
structure IsChartData [DecidableEq m] [DecidableEq n]
    (U : Matrix m r ℝ) (V : Matrix n r ℝ) (Up : Matrix m p ℝ)
    (Vp : Matrix n q ℝ) (G : Matrix r r ℝ) : Prop where
  isUnit_U : IsUnit (Uᵀ * U).det
  isUnit_V : IsUnit (Vᵀ * V).det
  isUnit_Up : IsUnit (Upᵀ * Up).det
  isUnit_Vp : IsUnit (Vpᵀ * Vp).det
  isUnit_G : IsUnit G.det
  Up_orth : Upᵀ * U = 0
  Vp_orth : Vpᵀ * V = 0
  compl_U : U * U.gramPinv + Up * Up.gramPinv = 1
  compl_V : V * V.gramPinv + Vp * Vp.gramPinv = 1

/-- The tangent map `T_Z i : (δX, δY, δH) ↦ U⊥ δX G Vᵀ + U G (V⊥ δY)ᵀ + U δH Vᵀ`. -/
noncomputable def tangentMap (U : Matrix m r ℝ) (V : Matrix n r ℝ) (Up : Matrix m p ℝ)
    (Vp : Matrix n q ℝ) (G : Matrix r r ℝ) :
    (Matrix p r ℝ × Matrix q r ℝ × Matrix r r ℝ) →ₗ[ℝ] Matrix m n ℝ where
  toFun x := Up * x.1 * G * Vᵀ + U * G * (Vp * x.2.1)ᵀ + U * x.2.2 * Vᵀ
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Matrix.mul_add, Matrix.add_mul, Matrix.transpose_add]
    abel
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.transpose_smul, smul_add]

/-- The explicit inverse of Proposition 2.2 / eq. (7). -/
noncomputable def tangentInv (U : Matrix m r ℝ) (V : Matrix n r ℝ) (Up : Matrix m p ℝ)
    (Vp : Matrix n q ℝ) (G : Matrix r r ℝ) (W : Matrix m n ℝ) :
    Matrix p r ℝ × Matrix q r ℝ × Matrix r r ℝ :=
  (Up.gramPinv * W * (V.gramPinv)ᵀ * G⁻¹, Vp.gramPinv * Wᵀ * (U.gramPinv)ᵀ * (G⁻¹)ᵀ,
    U.gramPinv * W * (V.gramPinv)ᵀ)

section
variable [DecidableEq m] [DecidableEq n]
  {U : Matrix m r ℝ} {V : Matrix n r ℝ} {Up : Matrix m p ℝ} {Vp : Matrix n q ℝ}
  {G : Matrix r r ℝ}

omit [DecidableEq m] [DecidableEq n] in
/-- `M⁺ M = 1` for `M` of full column rank (the core `Matrix.gramPinv_mul_self`). -/
lemma pinvL_mul {M : Matrix m r ℝ} (hU : IsUnit (Mᵀ * M).det) : M.gramPinv * M = 1 :=
  Matrix.gramPinv_mul_self hU

omit [DecidableEq m] [DecidableEq n] in
/-- `(M⁺)ᵀ = M (MᵀM)⁻¹` (the core `Matrix.transpose_gramPinv`). -/
lemma transpose_pinvL {M : Matrix m r ℝ} : (M.gramPinv)ᵀ = M * (Mᵀ * M)⁻¹ :=
  Matrix.transpose_gramPinv M

omit [DecidableEq m] [DecidableEq n] in
/-- `Mᵀ (M⁺)ᵀ = 1` for `M` of full column rank. -/
lemma transpose_mul_pinvL_transpose {M : Matrix m r ℝ} (hU : IsUnit (Mᵀ * M).det) :
    Mᵀ * (M.gramPinv)ᵀ = 1 := by
  rw [transpose_pinvL, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU]

/-- `U⊥⁺ U = 0`. -/
lemma pinvL_Up_mul_U (hc : IsChartData U V Up Vp G) : Up.gramPinv * U = 0 := by
  unfold Matrix.gramPinv
  rw [Matrix.mul_assoc, hc.Up_orth, Matrix.mul_zero]

/-- `U⁺ U⊥ = 0`. -/
lemma pinvL_U_mul_Up (hc : IsChartData U V Up Vp G) : U.gramPinv * Up = 0 := by
  unfold Matrix.gramPinv
  have : Uᵀ * Up = 0 := by
    have := congrArg Matrix.transpose hc.Up_orth
    simpa [Matrix.transpose_mul] using this
  rw [Matrix.mul_assoc, this, Matrix.mul_zero]

/-- `U⊥ᵀ (U⁺)ᵀ = 0`. -/
lemma Up_transpose_mul_pinvL (hc : IsChartData U V Up Vp G) : Upᵀ * (U.gramPinv)ᵀ = 0 := by
  have := congrArg Matrix.transpose (pinvL_U_mul_Up hc)
  simpa [Matrix.transpose_mul] using this

/-- `V⊥⁺ V = 0`. -/
lemma pinvL_Vp_mul_V (hc : IsChartData U V Up Vp G) : Vp.gramPinv * V = 0 := by
  unfold Matrix.gramPinv
  rw [Matrix.mul_assoc, hc.Vp_orth, Matrix.mul_zero]

/-- `V⁺ V⊥ = 0`. -/
lemma pinvL_V_mul_Vp (hc : IsChartData U V Up Vp G) : V.gramPinv * Vp = 0 := by
  unfold Matrix.gramPinv
  have : Vᵀ * Vp = 0 := by
    have := congrArg Matrix.transpose hc.Vp_orth
    simpa [Matrix.transpose_mul] using this
  rw [Matrix.mul_assoc, this, Matrix.mul_zero]

/-- `V⊥ᵀ (V⁺)ᵀ = 0`. -/
lemma Vp_transpose_mul_pinvL (hc : IsChartData U V Up Vp G) : Vpᵀ * (V.gramPinv)ᵀ = 0 := by
  have := congrArg Matrix.transpose (pinvL_V_mul_Vp hc)
  simpa [Matrix.transpose_mul] using this

omit [DecidableEq m] [DecidableEq n] in
/-- Completeness of a chart basis: for `A`, `A⊥` of full column rank with `A⊥ᵀ A = 0`, the
identity `A A⁺ + A⊥ A⊥⁺ = 1` holds iff the numbers of columns add up to the number of rows. -/
private theorem add_mul_gramPinv_eq_one_iff {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c] {A : Matrix a b ℝ} {Ap : Matrix a c ℝ}
    (hA : IsUnit (Aᵀ * A).det) (hAp : IsUnit (Apᵀ * Ap).det) (horth : Apᵀ * A = 0) :
    A * A.gramPinv + Ap * Ap.gramPinv = 1 ↔
      Fintype.card b + Fintype.card c = Fintype.card a := by
  constructor
  · intro h
    have ht := congrArg Matrix.trace h
    rw [Matrix.trace_add, Matrix.trace_mul_comm A, Matrix.trace_mul_comm Ap,
      Matrix.gramPinv_mul_self hA, Matrix.gramPinv_mul_self hAp, Matrix.trace_one,
      Matrix.trace_one, Matrix.trace_one] at ht
    exact_mod_cast ht
  · intro h
    have horth' : Aᵀ * Ap = 0 := by
      simpa [Matrix.transpose_mul] using congrArg Matrix.transpose horth
    have e : a ≃ b ⊕ c := Fintype.equivOfCardEq (by rw [Fintype.card_sum, h])
    rw [← Matrix.fromCols_mul_fromRows, Matrix.fromCols_mul_fromRows_eq_one_comm e,
      Matrix.fromRows_mul_fromCols, Matrix.gramPinv_mul_self hA, Matrix.gramPinv_mul_self hAp,
      Matrix.gramPinv_def A, Matrix.mul_assoc, horth', Matrix.mul_zero, Matrix.gramPinv_def Ap,
      Matrix.mul_assoc, horth, Matrix.mul_zero, Matrix.fromBlocks_one]

/-- **The two chart data of Section 2.1 agree.** `IsChartData U V U⊥ V⊥ G` (completeness written
as `U U⁺ + U⊥ U⊥⁺ = 1`) holds iff `(U, U⊥)` and `(V, V⊥)` are `IsChartBasis` (the chart data of
`P2001_08599b`, completeness written as the dimension count `r + (m - r) = m`) and `G` is
invertible. -/
theorem isChartData_iff :
    IsChartData U V Up Vp G ↔ IsChartBasis U Up ∧ IsChartBasis V Vp ∧ IsUnit G.det := by
  constructor
  · intro hc
    exact ⟨⟨hc.isUnit_U, hc.isUnit_Up, hc.Up_orth,
        (add_mul_gramPinv_eq_one_iff hc.isUnit_U hc.isUnit_Up hc.Up_orth).1 hc.compl_U⟩,
      ⟨hc.isUnit_V, hc.isUnit_Vp, hc.Vp_orth,
        (add_mul_gramPinv_eq_one_iff hc.isUnit_V hc.isUnit_Vp hc.Vp_orth).1 hc.compl_V⟩,
      hc.isUnit_G⟩
  · rintro ⟨hU, hV, hG⟩
    exact ⟨hU.gram, hV.gram, hU.gram_perp, hV.gram_perp, hG, hU.orth, hV.orth,
      (add_mul_gramPinv_eq_one_iff hU.gram hU.gram_perp hU.orth).2 hU.card_eq,
      (add_mul_gramPinv_eq_one_iff hV.gram hV.gram_perp hV.orth).2 hV.card_eq⟩

/-- `T_Z i` has the left inverse of eq. (7). -/
theorem tangentInv_tangentMap (hc : IsChartData U V Up Vp G)
    (x : Matrix p r ℝ × Matrix q r ℝ × Matrix r r ℝ) :
    tangentInv U V Up Vp G (tangentMap U V Up Vp G x) = x := by
  obtain ⟨X, Y, H⟩ := x
  have a1 := pinvL_mul hc.isUnit_Up
  have a2 := pinvL_Up_mul_U hc
  have a3 := pinvL_U_mul_Up hc
  have a4 := transpose_mul_pinvL_transpose hc.isUnit_V
  have a5 := pinvL_mul hc.isUnit_V
  have a6 := Up_transpose_mul_pinvL hc
  have a7 := Vp_transpose_mul_pinvL hc
  have a8 := pinvL_Vp_mul_V hc
  have a9 := pinvL_mul hc.isUnit_Vp
  have a10 := pinvL_mul hc.isUnit_U
  have a11 := transpose_mul_pinvL_transpose hc.isUnit_U
  have hG : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv _ hc.isUnit_G
  have hG' : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul _ hc.isUnit_G
  have hGt : (G⁻¹)ᵀ * Gᵀ = 1 := by
    rw [← Matrix.transpose_mul, hG, Matrix.transpose_one]
  have hGt' : Gᵀ * (G⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hG', Matrix.transpose_one]
  simp only [tangentInv, tangentMap, LinearMap.coe_mk, AddHom.coe_mk]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · have t1 : Up.gramPinv * (Up * X * G * Vᵀ) * (V.gramPinv)ᵀ * G⁻¹ = X := by
      calc _ = (Up.gramPinv * Up) * X * G * (Vᵀ * (V.gramPinv)ᵀ) * G⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = X := by rw [a1, a4]; simp [Matrix.mul_assoc, hG]
    have t2 : Up.gramPinv * (U * G * (Vp * Y)ᵀ) * (V.gramPinv)ᵀ * G⁻¹ = 0 := by
      calc _ = (Up.gramPinv * U) * (G * (Vp * Y)ᵀ * (V.gramPinv)ᵀ * G⁻¹) := by
            simp only [Matrix.mul_assoc]
        _ = 0 := by rw [a2]; simp
    have t3 : Up.gramPinv * (U * H * Vᵀ) * (V.gramPinv)ᵀ * G⁻¹ = 0 := by
      calc _ = (Up.gramPinv * U) * (H * Vᵀ * (V.gramPinv)ᵀ * G⁻¹) := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [a2]; simp
    calc _ = Up.gramPinv * (Up * X * G * Vᵀ) * (V.gramPinv)ᵀ * G⁻¹
          + Up.gramPinv * (U * G * (Vp * Y)ᵀ) * (V.gramPinv)ᵀ * G⁻¹
          + Up.gramPinv * (U * H * Vᵀ) * (V.gramPinv)ᵀ * G⁻¹ := by
            simp only [Matrix.mul_add, Matrix.add_mul]
      _ = X := by rw [t1, t2, t3]; simp
  · have t1 : Vp.gramPinv * (Up * X * G * Vᵀ)ᵀ * (U.gramPinv)ᵀ * (G⁻¹)ᵀ = 0 := by
      calc _ = (Vp.gramPinv * V) * (Gᵀ * Xᵀ * (Upᵀ * (U.gramPinv)ᵀ) * (G⁻¹)ᵀ) := by
            simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
        _ = 0 := by rw [a8]; simp
    have t2 : Vp.gramPinv * (U * G * (Vp * Y)ᵀ)ᵀ * (U.gramPinv)ᵀ * (G⁻¹)ᵀ = Y := by
      calc _ = (Vp.gramPinv * Vp) * Y * (Gᵀ * (Uᵀ * (U.gramPinv)ᵀ) * (G⁻¹)ᵀ) := by
            simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
        _ = Y := by rw [a9, a11]; simp [hGt']
    have t3 : Vp.gramPinv * (U * H * Vᵀ)ᵀ * (U.gramPinv)ᵀ * (G⁻¹)ᵀ = 0 := by
      calc _ = (Vp.gramPinv * V) * (Hᵀ * (Uᵀ * (U.gramPinv)ᵀ) * (G⁻¹)ᵀ) := by
            simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
        _ = 0 := by rw [a8]; simp
    calc _ = Vp.gramPinv * (Up * X * G * Vᵀ)ᵀ * (U.gramPinv)ᵀ * (G⁻¹)ᵀ
          + Vp.gramPinv * (U * G * (Vp * Y)ᵀ)ᵀ * (U.gramPinv)ᵀ * (G⁻¹)ᵀ
          + Vp.gramPinv * (U * H * Vᵀ)ᵀ * (U.gramPinv)ᵀ * (G⁻¹)ᵀ := by
            simp only [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]
      _ = Y := by rw [t1, t2, t3]; simp
  · have t1 : U.gramPinv * (Up * X * G * Vᵀ) * (V.gramPinv)ᵀ = 0 := by
      calc _ = (U.gramPinv * Up) * (X * G * (Vᵀ * (V.gramPinv)ᵀ)) := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [a3]; simp
    have t2 : U.gramPinv * (U * G * (Vp * Y)ᵀ) * (V.gramPinv)ᵀ = 0 := by
      calc _ = (U.gramPinv * U) * G * Yᵀ * (Vpᵀ * (V.gramPinv)ᵀ) := by
            simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = 0 := by rw [a7]; simp
    have t3 : U.gramPinv * (U * H * Vᵀ) * (V.gramPinv)ᵀ = H := by
      calc _ = (U.gramPinv * U) * H * (Vᵀ * (V.gramPinv)ᵀ) := by simp only [Matrix.mul_assoc]
        _ = H := by rw [a10, a4]; simp
    calc _ = U.gramPinv * (Up * X * G * Vᵀ) * (V.gramPinv)ᵀ
          + U.gramPinv * (U * G * (Vp * Y)ᵀ) * (V.gramPinv)ᵀ
          + U.gramPinv * (U * H * Vᵀ) * (V.gramPinv)ᵀ := by
            simp only [Matrix.mul_add, Matrix.add_mul]
      _ = H := by rw [t1, t2, t3]; simp

omit [DecidableEq m] [DecidableEq n] in
/-- `M M⁺` is symmetric (the core `Matrix.transpose_mul_gramPinv`). -/
lemma mul_pinvL_symm {M : Matrix m r ℝ} : (M * M.gramPinv)ᵀ = M * M.gramPinv :=
  Matrix.transpose_mul_gramPinv M

/-- `T_Z i` is injective (Proposition 2.2). -/
theorem tangentMap_injective (hc : IsChartData U V Up Vp G) :
    Function.Injective (tangentMap U V Up Vp G) := fun x y h => by
  rw [← tangentInv_tangentMap hc x, h, tangentInv_tangentMap hc y]

/-- The tangent space `T_Z M_r` is the range of `T_Z i`; it consists of the matrices `U B + C Vᵀ`
(this also gives surjectivity of `T_Z i` onto that space; the completeness `U U⁺ + U⊥ U⊥⁺ = 1` is
used here). -/
theorem mem_range_tangentMap_iff (hc : IsChartData U V Up Vp G) (W : Matrix m n ℝ) :
    W ∈ LinearMap.range (tangentMap U V Up Vp G) ↔
      ∃ (B : Matrix r n ℝ) (C : Matrix m r ℝ), W = U * B + C * Vᵀ := by
  constructor
  · rintro ⟨⟨X, Y, H⟩, rfl⟩
    refine ⟨G * (Vp * Y)ᵀ, Up * X * G + U * H, ?_⟩
    simp only [tangentMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.add_mul,
      Matrix.mul_assoc]
    abel
  · rintro ⟨B, C, rfl⟩
    have hG : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv _ hc.isUnit_G
    have hG' : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul _ hc.isUnit_G
    have hUp : Up * Up.gramPinv = 1 - U * U.gramPinv := eq_sub_of_add_eq' hc.compl_U
    have hVp : Vp * Vp.gramPinv = 1 - V * V.gramPinv := eq_sub_of_add_eq' hc.compl_V
    refine ⟨(Up.gramPinv * C * G⁻¹, Vp.gramPinv * Bᵀ * (G⁻¹)ᵀ,
      B * V * (Vᵀ * V)⁻¹ + U.gramPinv * C), ?_⟩
    have e1 : Up * (Up.gramPinv * C * G⁻¹) * G * Vᵀ = (Up * Up.gramPinv) * C * Vᵀ := by
      calc _ = (Up * Up.gramPinv) * C * (G⁻¹ * G) * Vᵀ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hG']; simp
    have e2 : U * G * (Vp * (Vp.gramPinv * Bᵀ * (G⁻¹)ᵀ))ᵀ = U * B * (Vp * Vp.gramPinv) := by
      calc _ = U * (G * G⁻¹) * B * (Vp * Vp.gramPinv)ᵀ := by
            simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
        _ = _ := by rw [hG, mul_pinvL_symm]; simp
    have e3 : U * (B * V * (Vᵀ * V)⁻¹ + U.gramPinv * C) * Vᵀ
        = U * B * (V * V.gramPinv) + (U * U.gramPinv) * C * Vᵀ := by
      unfold Matrix.gramPinv; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    simp only [tangentMap, LinearMap.coe_mk, AddHom.coe_mk]
    rw [e1, e2, e3, hUp, hVp]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    abel

/-- **Proposition 2.2 as a linear equivalence**: `T_Z i` is an isomorphism of
`ℝ^{(m-r)×r} × ℝ^{(n-r)×r} × ℝ^{r×r}` onto the tangent space `T_Z M_r`. -/
noncomputable def tangentEquiv (hc : IsChartData U V Up Vp G) :
    (Matrix p r ℝ × Matrix q r ℝ × Matrix r r ℝ) ≃ₗ[ℝ]
      LinearMap.range (tangentMap U V Up Vp G) :=
  LinearEquiv.ofInjective _ (tangentMap_injective hc)

/-- **Proposition 2.2, eq. (7)** (arXiv 2001.08599, Prop. 2.2 and eq. (7)).  With
`Z = U G Vᵀ`, `U, V` of full column rank, `G` invertible and `U⊥`, `V⊥` as in Section 2.1,
the inverse of the isomorphism `T_Z i : (δX, δY, δH) ↦ U⊥ δX G Vᵀ + U G (V⊥ δY)ᵀ + U δH Vᵀ` onto
`T_Z M_r` is `δW ↦ (U⊥⁺ δW (V⁺)ᵀ G⁻¹, V⊥⁺ δWᵀ (U⁺)ᵀ G⁻ᵀ, U⁺ δW (V⁺)ᵀ)`.  Precisely: this map
is a left inverse of `T_Z i` on the whole parameter space (`tangentInv_tangentMap`) and a right
inverse on the tangent space, hence the inverse of `T_Z i` onto `T_Z M_r`; the paper writes the
formula for all `δW ∈ ℝ^{n×m}`, where it is a right inverse only on `T_Z M_r`.  `T_Z M_r` is
`range (T_Z i) = {U B + C Vᵀ}`.  The complement condition
`U U⁺ + U⊥ U⊥⁺ = 1` is the content of "`U⊥` is a basis of `range(U)⊥`". -/
theorem prop_2_2 (hc : IsChartData U V Up Vp G) :
    (∀ x, tangentInv U V Up Vp G (tangentMap U V Up Vp G x) = x) ∧
    (∀ W ∈ LinearMap.range (tangentMap U V Up Vp G),
      tangentMap U V Up Vp G (tangentInv U V Up Vp G W) = W) ∧
    (∀ W, W ∈ LinearMap.range (tangentMap U V Up Vp G) ↔
      ∃ (B : Matrix r n ℝ) (C : Matrix m r ℝ), W = U * B + C * Vᵀ) ∧
    Function.Injective (tangentMap U V Up Vp G) :=
  ⟨tangentInv_tangentMap hc, by
    rintro _ ⟨x, rfl⟩
    rw [tangentInv_tangentMap hc], mem_range_tangentMap_iff hc, tangentMap_injective hc⟩

/-- **Eqs. (8)–(9)**: the tangent-space projection written as in (8),
`P_T F = P_U⊥ F P_V + P_U F P_V⊥ + P_U F P_V` with `P_U = U U⁺`, `P_V = V V⁺`. -/
noncomputable def tangentProjection (U : Matrix m r ℝ) (V : Matrix n r ℝ) (F : Matrix m n ℝ) :
    Matrix m n ℝ :=
  (1 - U * U.gramPinv) * F * (V * V.gramPinv) + (U * U.gramPinv) * F * (1 - V * V.gramPinv)
    + (U * U.gramPinv) * F * (V * V.gramPinv)

/-- Core of eqs. (8)–(9): `T_Z i` applied to the right-hand side of (9) is
`P_T F = P_U⊥ F P_V + P_U F P_V⊥ + P_U F P_V`. -/
theorem tangentMap_tangentInv (hc : IsChartData U V Up Vp G) (F : Matrix m n ℝ) :
    tangentMap U V Up Vp G (tangentInv U V Up Vp G F) = tangentProjection U V F := by
  have hG : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv _ hc.isUnit_G
  have hG' : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul _ hc.isUnit_G
  have hUp : Up * Up.gramPinv = 1 - U * U.gramPinv := eq_sub_of_add_eq' hc.compl_U
  have hVp : Vp * Vp.gramPinv = 1 - V * V.gramPinv := eq_sub_of_add_eq' hc.compl_V
  have e1 : Up * (Up.gramPinv * F * (V.gramPinv)ᵀ * G⁻¹) * G * Vᵀ
      = (Up * Up.gramPinv) * F * (V * V.gramPinv) := by
    calc _ = (Up * Up.gramPinv) * F * ((V.gramPinv)ᵀ * (G⁻¹ * G) * Vᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hG', Matrix.mul_one, ← Matrix.transpose_mul, mul_pinvL_symm]
  have e2 : U * G * (Vp * (Vp.gramPinv * Fᵀ * (U.gramPinv)ᵀ * (G⁻¹)ᵀ))ᵀ
      = (U * U.gramPinv) * F * (Vp * Vp.gramPinv) := by
    calc _ = U * (G * G⁻¹) * (U.gramPinv) * F * (Vp * Vp.gramPinv)ᵀ := by
          simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = _ := by rw [hG, mul_pinvL_symm]; simp [Matrix.mul_assoc]
  have e3 : U * (U.gramPinv * F * (V.gramPinv)ᵀ) * Vᵀ =
      (U * U.gramPinv) * F * (V * V.gramPinv) := by
    calc _ = (U * U.gramPinv) * F * ((V.gramPinv)ᵀ * Vᵀ) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [← Matrix.transpose_mul, mul_pinvL_symm]
  simp only [tangentMap, tangentInv, LinearMap.coe_mk, AddHom.coe_mk]
  rw [e1, e2, e3, hUp, hVp]
  rfl

/-- **Eqs. (8) ⇔ (9)** (arXiv 2001.08599, eqs. (8)–(9)): the parameters `(Ẋ, Ẏ, Ḣ)` satisfy
`T_Z i (Ẋ, Ẏ, Ḣ) = P_T F` (i.e. `Ż = P_T F(Z)`) iff they satisfy
`Ẋ = U⊥⁺ F (V⁺)ᵀ G⁻¹`, `Ẏ = V⊥⁺ Fᵀ (U⁺)ᵀ G⁻ᵀ`, `Ḣ = U⁺ F (V⁺)ᵀ`.  Here `F` stands for the
value `F(Z)` at one instant; this is the pointwise algebraic content of the passage from (8) to
(9). -/
theorem tangentMap_eq_tangentProjection_iff (hc : IsChartData U V Up Vp G) (F : Matrix m n ℝ)
    (x : Matrix p r ℝ × Matrix q r ℝ × Matrix r r ℝ) :
    tangentMap U V Up Vp G x = tangentProjection U V F ↔ x = tangentInv U V Up Vp G F := by
  constructor
  · intro h
    exact tangentMap_injective hc (h.trans (tangentMap_tangentInv hc F).symm)
  · rintro rfl
    exact tangentMap_tangentInv hc F

end

/-! ### Orthonormal case: link with `tangentProj` -/

section Orthonormal

open scoped LeanDLRA.Frobenius

variable [DecidableEq m] [DecidableEq n] {U : Matrix m r ℝ} {V : Matrix n r ℝ}
  {Up : Matrix m p ℝ} {Vp : Matrix n q ℝ} {G : Matrix r r ℝ}

omit [DecidableEq m] [DecidableEq p] in
/-- `M⁺ = Mᵀ` for orthonormal columns (the core `Matrix.gramPinv_eq_transpose`). -/
lemma pinvL_of_orthonormal {M : Matrix m r ℝ} (hM : Mᵀ * M = 1) : M.gramPinv = Mᵀ :=
  Matrix.gramPinv_eq_transpose hM

/-- For orthonormal `U`, `V` (`U⁺ = Uᵀ`) the projection `P_T F` of eq. (8) is the library's
tangent-space projector `tangentProj U V`. -/
theorem tangentProjection_eq_tangentProj (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (F : Matrix m n ℝ) : tangentProjection U V F = tangentProj U V F := by
  rw [tangentProj_apply, tangentProjection, pinvL_of_orthonormal hU, pinvL_of_orthonormal hV]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  abel

/-- For orthonormal `U`, `V` the tangent space `range (T_Z i)` of Prop. 2.2 is the range of the
orthogonal projector `tangentProj U V` onto the tangent space (`mem_range_tangentProj`). -/
theorem range_tangentMap_eq_range_tangentProj (hc : IsChartData U V Up Vp G) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) :
    LinearMap.range (tangentMap U V Up Vp G) =
      LinearMap.range (tangentProj U V : Matrix m n ℝ →ₗ[ℝ] Matrix m n ℝ) := by
  ext W
  rw [mem_range_tangentMap_iff hc, mem_range_tangentProj hU hV]

end Orthonormal

/-! ### The three-term splitting (eqs. (17)–(18), Appendix A) -/

section Splitting

open scoped LeanDLRA.Frobenius

variable {P : Matrix m m ℝ} {Q : Matrix n n ℝ}

/-- Left multiplication by a symmetric idempotent matrix is an orthogonal projector on the
space of matrices with the Frobenius inner product. -/
theorem isOrthProj_leftMul (hP : P * P = P) (hs : Pᵀ = P) :
    IsOrthProj (Frobenius.leftMulCLM P : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) where
  idem X := by simp only [Frobenius.leftMulCLM_apply, ← Matrix.mul_assoc, hP]
  symm X Y := by
    simp only [Frobenius.leftMulCLM_apply]
    rw [Frobenius.inner_mul_left, hs]

/-- Right multiplication by a symmetric idempotent matrix is an orthogonal projector. -/
theorem isOrthProj_rightMul (hQ : Q * Q = Q) (hs : Qᵀ = Q) :
    IsOrthProj (Frobenius.rightMulCLM Q : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) where
  idem X := by simp only [Frobenius.rightMulCLM_apply, Matrix.mul_assoc, hQ]
  symm X Y := by
    simp only [Frobenius.rightMulCLM_apply]
    rw [Frobenius.inner_mul_right, hs]

/-- The three projections of eq. (18): `P₁ A = P_U A P_V`, `P₂ A = P_U⊥ A P_V`,
`P₃ A = P_U A P_V⊥`, for symmetric idempotent `P = P_U`, `Q = P_V` (so that `P_U⊥ = 1 - P_U`
etc.). -/
noncomputable def splitP₁ (P : Matrix m m ℝ) (Q : Matrix n n ℝ) :
    Matrix m n ℝ →L[ℝ] Matrix m n ℝ := Frobenius.leftMulCLM P * Frobenius.rightMulCLM Q

/-- See `splitP₁`. -/
noncomputable def splitP₂ (P : Matrix m m ℝ) (Q : Matrix n n ℝ) :
    Matrix m n ℝ →L[ℝ] Matrix m n ℝ := (1 - Frobenius.leftMulCLM P) * Frobenius.rightMulCLM Q

/-- See `splitP₁`. -/
noncomputable def splitP₃ (P : Matrix m m ℝ) (Q : Matrix n n ℝ) :
    Matrix m n ℝ →L[ℝ] Matrix m n ℝ := Frobenius.leftMulCLM P * (1 - Frobenius.rightMulCLM Q)

lemma leftMul_rightMul_comm (P : Matrix m m ℝ) (Q : Matrix n n ℝ) (X : Matrix m n ℝ) :
    Frobenius.leftMulCLM P (Frobenius.rightMulCLM Q X) =
      Frobenius.rightMulCLM Q (Frobenius.leftMulCLM P X) := by
  simp [Matrix.mul_assoc]

lemma splitP₁_apply (A : Matrix m n ℝ) : splitP₁ P Q A = P * (A * Q) := rfl

lemma splitP₂_apply (A : Matrix m n ℝ) : splitP₂ P Q A = A * Q - P * (A * Q) := rfl

lemma splitP₃_apply (A : Matrix m n ℝ) : splitP₃ P Q A = P * (A - A * Q) := by
  simp [splitP₃, Matrix.mul_sub]

/-- **Eqs. (17)–(18)** (arXiv 2001.08599; the direct-sum remark after (18)).  For
symmetric idempotent `P = P_U`, `Q = P_V` (orthogonal projectors; for `U`, `V` of full column
rank `P_U = U U⁺`, see `isOrthProj_leftMul` and `Matrix.gramPinv`), the maps `P₁ = P_U · P_V`,
`P₂ = P_U⊥ · P_V`, `P₃ = P_U · P_V⊥` satisfy `P₁ + P₂ + P₃ = P_T`, where
`P_T A = P_U A + A P_V - P_U A P_V` is the tangent-space projection, each `Pᵢ` is an orthogonal
projector, and the `Pᵢ` are pairwise orthogonal (`Pᵢ Pⱼ = 0` for `i ≠ j`).  Hence the sum is a
direct sum of the ranges, which is the "direct sum decomposition of the tangent space".  The
Lie splitting integrator itself (the H-, X-, Y-sub-flows of Prop. A.1) and its error analysis are
not formalized. -/
theorem splitting_direct_sum (hP : P * P = P) (hPs : Pᵀ = P) (hQ : Q * Q = Q) (hQs : Qᵀ = Q) :
    (∀ A : Matrix m n ℝ,
      splitP₁ P Q A + splitP₂ P Q A + splitP₃ P Q A = P * A + A * Q - P * A * Q) ∧
    IsOrthProj (splitP₁ P Q) ∧ IsOrthProj (splitP₂ P Q) ∧ IsOrthProj (splitP₃ P Q) ∧
    (∀ A, splitP₁ P Q (splitP₂ P Q A) = 0) ∧ (∀ A, splitP₂ P Q (splitP₁ P Q A) = 0) ∧
    (∀ A, splitP₁ P Q (splitP₃ P Q A) = 0) ∧ (∀ A, splitP₃ P Q (splitP₁ P Q A) = 0) ∧
    (∀ A, splitP₂ P Q (splitP₃ P Q A) = 0) ∧ (∀ A, splitP₃ P Q (splitP₂ P Q A) = 0) := by
  have hP2 : ∀ X : Matrix m n ℝ, P * (P * X) = P * X := fun X => by
    rw [← Matrix.mul_assoc, hP]
  have hLP := isOrthProj_leftMul (n := n) hP hPs
  have hRQ := isOrthProj_rightMul (m := m) hQ hQs
  have hc := leftMul_rightMul_comm (n := n) P Q
  refine ⟨fun A => ?_, (hLP.mul hRQ hc), ((hLP.compl).mul hRQ ?_), (hLP.mul hRQ.compl ?_), ?_⟩
  · simp only [splitP₁_apply, splitP₂_apply, splitP₃_apply, Matrix.mul_sub,
      Matrix.mul_assoc]
    abel
  · intro X
    simp only [sub_apply, one_apply_eq_self, map_sub, hc]
  · intro X
    simp only [sub_apply, one_apply_eq_self, map_sub, hc]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro A <;>
      simp only [splitP₁_apply, splitP₂_apply, splitP₃_apply, Matrix.mul_sub, Matrix.sub_mul,
        Matrix.mul_assoc, hP2, hQ, sub_self, Matrix.mul_zero]

/-- `U U⁺` (`P_U` of the paper) is a symmetric idempotent matrix when `U` has full column rank. -/
theorem mulPinvL_idem {M : Matrix m r ℝ} (hM : IsUnit (Mᵀ * M).det) :
    (M * M.gramPinv) * (M * M.gramPinv) = M * M.gramPinv := by
  calc _ = M * (M.gramPinv * M) * M.gramPinv := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [pinvL_mul hM, Matrix.mul_one]

/-- Eq. (8) in the form of (17)–(18): `P_T F = P₁ F + P₂ F + P₃ F` with `P_U = U U⁺`,
`P_V = V V⁺`. -/
theorem tangentProjection_eq_sum [DecidableEq m] [DecidableEq n] (U : Matrix m r ℝ)
    (V : Matrix n r ℝ) (F : Matrix m n ℝ) :
    tangentProjection U V F =
      splitP₁ (U * U.gramPinv) (V * V.gramPinv) F + splitP₂ (U * U.gramPinv) (V * V.gramPinv) F
        + splitP₃ (U * U.gramPinv) (V * V.gramPinv) F := by
  unfold tangentProjection
  simp only [splitP₁_apply, splitP₂_apply, splitP₃_apply, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one]
  abel

end Splitting

/-! ### KSL versus chart-based algorithm (Lemma 3.11, Proposition 3.12) -/

section Algorithms

variable [DecidableEq m] [DecidableEq n]

/-- One step of the KSL algorithm (Algorithm 3.5) with explicit flux `F = F(t_{k-1})`, step `h`,
and starting from `Z₀ = U₀ G₀ V₀ᵀ`.  The QR factorizations are encoded by their defining
properties: `U₁ Ĝ₁ = K₁ = U₀ G₀ + h F V₀` with `U₁ᵀ U₁ = 1`, and `V₁ G₁ᵀ = L₁ = V₀ G̃₁ᵀ + h Fᵀ U₁`
with `V₁ᵀ V₁ = 1`, where `G̃₁ = Ĝ₁ - h U₁ᵀ F V₀`.  The new iterate is `U₁ G₁ V₁ᵀ`. -/
structure IsKSLAlg (h : ℝ) (F : Matrix m n ℝ) (U₀ : Matrix m r ℝ) (G₀ : Matrix r r ℝ)
    (V₀ : Matrix n r ℝ) (U₁ : Matrix m r ℝ) (Gh : Matrix r r ℝ) (V₁ : Matrix n r ℝ)
    (G₁ : Matrix r r ℝ) : Prop where
  orth_U₁ : U₁ᵀ * U₁ = 1
  qr_K : U₁ * Gh = U₀ * G₀ + h • (F * V₀)
  orth_V₁ : V₁ᵀ * V₁ = 1
  qr_L : V₁ * G₁ᵀ = V₀ * (Gh - h • (U₁ᵀ * F * V₀))ᵀ + h • (Fᵀ * U₁)

/-- One step of the chart-based algorithm (Algorithm 3.6) with explicit flux `F = F(t_{k-1})`,
for `U₀`, `V₀` with orthonormal columns (so `U₀⁺ = U₀ᵀ`, `U₀⊥ U₀⊥⁺ = 1 - U₀ U₀ᵀ`, as in
Remark 3.10), `H₀ = G₀`: `Ĥ₁ = G₀ + h U₀ᵀ F V₀`; `U₁ H̃₁ = U₀ Ĥ₁ + h (1 - U₀U₀ᵀ) F V₀`;
`V₁ H₁ᵀ = V₀ H̃₁ᵀ + h (1 - V₀V₀ᵀ) Fᵀ U₁`, both with orthonormal new bases.  The new iterate
is `U₁ H₁ V₁ᵀ`. -/
structure IsChartAlg (h : ℝ) (F : Matrix m n ℝ) (U₀ : Matrix m r ℝ) (G₀ : Matrix r r ℝ)
    (V₀ : Matrix n r ℝ) (U₁ : Matrix m r ℝ) (Ht : Matrix r r ℝ) (V₁ : Matrix n r ℝ)
    (H₁ : Matrix r r ℝ) : Prop where
  orth_U₀ : U₀ᵀ * U₀ = 1
  orth_V₀ : V₀ᵀ * V₀ = 1
  orth_U₁ : U₁ᵀ * U₁ = 1
  qr_X : U₁ * Ht = U₀ * (G₀ + h • (U₀ᵀ * F * V₀)) + h • ((1 - U₀ * U₀ᵀ) * F * V₀)
  orth_V₁ : V₁ᵀ * V₁ = 1
  qr_Y : V₁ * H₁ᵀ = V₀ * Htᵀ + h • ((1 - V₀ * V₀ᵀ) * Fᵀ * U₁)

variable {h : ℝ} {F : Matrix m n ℝ} {U₀ U₁ : Matrix m r ℝ} {V₀ V₁ : Matrix n r ℝ}
  {G₀ Gh G₁ : Matrix r r ℝ}

omit [DecidableEq r] [DecidableEq n] in
lemma chart_K_eq (U₀ : Matrix m r ℝ) (G₀ : Matrix r r ℝ) (V₀ : Matrix n r ℝ) :
    U₀ * (G₀ + h • (U₀ᵀ * F * V₀)) + h • ((1 - U₀ * U₀ᵀ) * F * V₀)
      = U₀ * G₀ + h • (F * V₀) := by
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc,
    smul_sub]
  abel

omit [DecidableEq r] [DecidableEq m] in
lemma chart_L_eq (V₀ : Matrix n r ℝ) (U₁ : Matrix m r ℝ) (Gh : Matrix r r ℝ) :
    V₀ * Ghᵀ + h • ((1 - V₀ * V₀ᵀ) * Fᵀ * U₁)
      = V₀ * (Gh - h • (U₁ᵀ * F * V₀))ᵀ + h • (Fᵀ * U₁) := by
  simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.mul_sub, Matrix.mul_smul, Matrix.sub_mul, Matrix.one_mul,
    Matrix.mul_assoc, smul_sub]
  abel

/-- **Lemma 3.11** (arXiv 2001.08599), for `Z`-independent flux `F`: with orthonormal `U₀`, `V₀`
(the paper's proof uses `P_{U₀} = U₀U₀ᵀ`; for `k ≥ 2` they come from QR factorizations),
one step of the KSL algorithm and one step of the chart-based algorithm, run with the same step
size and flux, produce the same data.  Precisely, `(U₁, Ĝ₁, V₁, G₁)` is a valid QR-based KSL step
iff the same four matrices form a valid chart-based step (`H̃₁ = Ĝ₁`), so with a deterministic
QR routine, which is applied to the same matrix `K₁ = K̄₁` and then to the same `L₁ = L̄₁`
(these are the identities `K̄₁ = K₁`, `L̄₁ = L₁` of the paper's proof), the two iterates
`Z¹ = U₁ G₁ V₁ᵀ` coincide.  Here `F` is the single value `F(t_{k-1})`.  The paper's claim is for
the whole sequence `{Zᵏ}`; it follows from the one-step statement by induction, which is not
formalized. -/
theorem lemma_3_11 (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) :
    IsKSLAlg h F U₀ G₀ V₀ U₁ Gh V₁ G₁ ↔ IsChartAlg h F U₀ G₀ V₀ U₁ Gh V₁ G₁ := by
  constructor
  · intro k
    refine ⟨hU₀, hV₀, k.orth_U₁, ?_, k.orth_V₁, ?_⟩
    · rw [chart_K_eq]; exact k.qr_K
    · rw [chart_L_eq]; exact k.qr_L
  · intro c
    refine ⟨c.orth_U₁, ?_, c.orth_V₁, ?_⟩
    · rw [← chart_K_eq]; exact c.qr_X
    · rw [← chart_L_eq]; exact c.qr_Y

omit [DecidableEq m] in
/-- **Explicit form of one step**: for a KSL (equivalently, chart) step from `Z₀ = U₀ G₀ V₀ᵀ`
the new iterate is
`Z¹ = Z₀ + h F Q₀ + h P₁ F (1 - Q₀)` with `Q₀ = V₀ V₀ᵀ` and `P₁ = U₁ U₁ᵀ`; no orthonormality is
needed.  This formula is not displayed in arXiv 2001.08599: it is the computation in the proof of
the KSL exactness theorem that the proof of Prop. 3.12 cites ([15, Theorem 4.1], i.e.
arXiv 1301.1058, Theorem 4.1, with `ΔA = h F`). -/
theorem ksl_iterate_eq (k : IsKSLAlg h F U₀ G₀ V₀ U₁ Gh V₁ G₁) :
    U₁ * G₁ * V₁ᵀ = U₀ * G₀ * V₀ᵀ + h • (F * (V₀ * V₀ᵀ))
      + h • (U₁ * U₁ᵀ * F * (1 - V₀ * V₀ᵀ)) := by
  have hL := congrArg Matrix.transpose k.qr_L
  simp only [Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_smul,
    Matrix.transpose_sub, Matrix.transpose_transpose] at hL
  have h1 : U₁ * G₁ * V₁ᵀ = U₁ * (V₁ * G₁ᵀ)ᵀ := by
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have hK : U₁ * Gh * V₀ᵀ = U₀ * G₀ * V₀ᵀ + h • (F * V₀ * V₀ᵀ) := by
    rw [k.qr_K]; simp [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [h1, k.qr_L]
  simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_add, Matrix.mul_sub,
    Matrix.mul_smul, Matrix.mul_assoc, Matrix.mul_one, smul_sub] at hK ⊢
  rw [hK]
  abel

/-- The same formula for one step of the chart-based algorithm (via `lemma_3_11`):
`Z¹ = Z₀ + h F Q₀ + h P₁ F (1 - Q₀)`. -/
theorem chart_iterate_eq (c : IsChartAlg h F U₀ G₀ V₀ U₁ Gh V₁ G₁) :
    U₁ * G₁ * V₁ᵀ = U₀ * G₀ * V₀ᵀ + h • (F * (V₀ * V₀ᵀ))
      + h • (U₁ * U₁ᵀ * F * (1 - V₀ * V₀ᵀ)) :=
  ksl_iterate_eq ((lemma_3_11 c.orth_U₀ c.orth_V₀).2 c)

/-- **Proposition 3.12, corrected** (arXiv 2001.08599, Prop. 3.12).  Let the previous iterate be
exact, `A₀ = U₀ G₀ V₀ᵀ` with `V₀ᵀ V₀ = 1`, let `h F = A₁ - A₀` (the increment of the proposition,
`Δt F(t_{k-1}) = A(t_k) - A(t_{k-1})`), and let one chart-based step be performed (any valid QR
factors).  If `A₀ = Ue₀ Se₀ Ve₀ᵀ` has rank exactly `r` (`Ue₀ᵀ Ue₀ = 1`, `Se₀` invertible) and
`A₁ = Ue₁ Se₁ Ve₁ᵀ` has rank at most `r`, with `Ve₁ᵀ Ve₀` invertible, then `Z¹ = A₁`.
The paper's statement only assumes "bounded rank `r`"; the two extra conditions (rank exactly
`r` at `t_{k-1}`, invertibility of `V(t_k)ᵀ V(t_{k-1})`) are the hypotheses of the library's
`ksl_exact_of_factors`.  The cited [15, Theorem 4.1] (arXiv 1301.1058) states KSL exactness for
rank at most `r` without them; its proof assumes the invertibility and treats the singular case
by a perturbation argument.  Without the invertibility the statement is false for an admissible
QR factor, even when `A(t)` has rank exactly `r` for all `t` (`prop_3_12_literal_false`).  The
proof transfers `ksl_exact_of_factors` via `lemma_3_11`.  The implicit start `Z⁰ = A(t₀)` (needed
for `Zᵏ = A(tᵏ)`) is the hypothesis `hY₀`. -/
theorem prop_3_12 {A₀ A₁ : Matrix m n ℝ} {Ue₀ Ue₁ : Matrix m r ℝ} {Se₀ Se₁ : Matrix r r ℝ}
    {Ve₀ Ve₁ : Matrix n r ℝ} (hA₀ : A₀ = Ue₀ * Se₀ * Ve₀ᵀ) (hA₁ : A₁ = Ue₁ * Se₁ * Ve₁ᵀ)
    (hUe₀ : Ue₀ᵀ * Ue₀ = 1) (hSe₀ : IsUnit Se₀) (hVV : IsUnit (Ve₁ᵀ * Ve₀))
    (hV₀ : V₀ᵀ * V₀ = 1) (hY₀ : U₀ * G₀ * V₀ᵀ = A₀) (hF : h • F = A₁ - A₀)
    (c : IsChartAlg h F U₀ G₀ V₀ U₁ Gh V₁ G₁) :
    U₁ * G₁ * V₁ᵀ = A₁ := by
  have k := (lemma_3_11 c.orth_U₀ c.orth_V₀).2 c
  refine Exactness.ksl_exact_of_factors hA₀ hA₁ hUe₀ hSe₀ hVV hV₀ hY₀ (K₁ := U₀ * G₀ + h • (F * V₀))
    (U₁ := U₁) (Ŝ₁ := Gh) (St₀ := Gh - U₁ᵀ * (A₁ - A₀) * V₀)
    (L₁ := V₀ * (Gh - U₁ᵀ * (A₁ - A₀) * V₀)ᵀ + (A₁ - A₀)ᵀ * U₁) ?_ k.orth_U₁ k.qr_K rfl rfl ?_
  · rw [← hF, Matrix.smul_mul]
  · rw [← hF]
    simpa [Matrix.smul_mul, Matrix.mul_smul, Matrix.transpose_smul, Matrix.mul_assoc] using k.qr_L

end Algorithms

/-! ### Failure of Proposition 3.12 as literally stated, and non-vacuity -/

section Examples

/-- The first basis vector of `ℝ²` as a `2 × 1` matrix. -/
def e₁ : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

/-- The second basis vector of `ℝ²` as a `2 × 1` matrix. -/
def e₂ : Matrix (Fin 2) (Fin 1) ℝ := !![0; 1]

/-- Entry computation for the `2 × 1` example matrices. -/
local macro "e_simp" : tactic =>
  `(tactic| simp [e₁, e₂, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two, Matrix.vecMul,
    dotProduct] <;> try norm_num)

/-- **Proposition 3.12 is false as literally stated** (arXiv 2001.08599, Prop. 3.12, hypothesis
"`A(t)` has bounded rank `r` for all `t`").  The curve `A(t) = e₁ ((1-t) e₁ + t e₂)ᵀ` has rank
`r = 1` for all `t`, `Δt = 1`, and the increment is `Δt F(t₀) = A(1) - A(0)`.  Starting from
the exact factorization `A(0) = e₁ · 1 · e₁ᵀ`, the chart-based algorithm admits a valid
QR step (`K₁ = 0`, so `U₁ = e₂` is an admissible orthonormal basis) whose result `Z¹ = 0` differs
from `A(1) = e₁ e₂ᵀ`.  Here `V(1)ᵀ V(0) = e₂ᵀ e₁ = 0`, so the invertibility hypothesis of
`prop_3_12` fails.  The failure uses the freedom in the QR factorization of the rank-deficient
`K₁ = 0` (with `U₁ = e₁` this particular step is exact).  For the rank-one path from `e₁e₁ᵀ` to
`e₂e₂ᵀ` the choice `U₁ = e₁` fails as well, for the KSL step
(`LeanDLRA.Exactness.RankOneExample.not_exact_of_degenerate`), hence for the chart step by
`lemma_3_11`. -/
theorem prop_3_12_literal_false :
    ∃ (A : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (u v : ℝ → Matrix (Fin 2) (Fin 1) ℝ),
      (∀ t, A t = u t * (v t)ᵀ) ∧
      ∃ (U₀ V₀ U₁ V₁ : Matrix (Fin 2) (Fin 1) ℝ) (G₀ Gh G₁ : Matrix (Fin 1) (Fin 1) ℝ),
        U₀ * G₀ * V₀ᵀ = A 0 ∧ IsChartAlg (1 : ℝ) (A 1 - A 0) U₀ G₀ V₀ U₁ Gh V₁ G₁ ∧
          U₁ * G₁ * V₁ᵀ ≠ A 1 := by
  refine ⟨fun t => e₁ * ((1 - t) • e₁ + t • e₂)ᵀ, fun _ => e₁, fun t => (1 - t) • e₁ + t • e₂,
    fun t => rfl, e₁, e₁, e₂, e₁, 1, 0, 0, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [e₁, e₂, Matrix.mul_apply]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [e₁, e₂, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
        Matrix.one_apply]
  · intro h
    have := congrFun (congrFun h 0) 1
    simp [e₁, e₂, Matrix.mul_apply] at this

lemma e₁_orth : e₁ᵀ * e₁ = 1 := by
  ext i j; fin_cases i; fin_cases j
  e_simp

lemma e₂_orth : e₂ᵀ * e₂ = 1 := by
  ext i j; fin_cases i; fin_cases j
  simp [e₂, Matrix.mul_apply, Fin.sum_univ_two]

/-- Non-vacuity of Proposition 2.2: the hypotheses `IsChartData` hold for `U = V = e₁`,
`U⊥ = V⊥ = e₂`, `G = 1`. -/
theorem isChartData_example : IsChartData e₁ e₁ e₂ e₂ (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e₁_orth]; simp
  · rw [e₁_orth]; simp
  · rw [e₂_orth]; simp
  · rw [e₂_orth]; simp
  · simp
  · ext i j; fin_cases i; fin_cases j; e_simp
  · ext i j; fin_cases i; fin_cases j; e_simp
  · rw [pinvL_of_orthonormal e₁_orth, pinvL_of_orthonormal e₂_orth]
    ext i j; fin_cases i <;> fin_cases j <;>
      e_simp
  · rw [pinvL_of_orthonormal e₁_orth, pinvL_of_orthonormal e₂_orth]
    ext i j; fin_cases i <;> fin_cases j <;>
      e_simp

/-- Non-vacuity of Proposition 3.12 (corrected): `A₀ = e₁ e₁ᵀ`, `A₁ = 2 e₁ e₁ᵀ`, `h = 1`,
`F = A₁ - A₀`; a valid chart step exists and, as `prop_3_12` predicts, returns `A₁`. -/
example : ∃ (U₁ V₁ : Matrix (Fin 2) (Fin 1) ℝ) (Gh G₁ : Matrix (Fin 1) (Fin 1) ℝ),
    IsChartAlg (1 : ℝ) (e₁ * e₁ᵀ) e₁ 1 e₁ U₁ Gh V₁ G₁ ∧
      U₁ * G₁ * V₁ᵀ = (2 : ℝ) • (e₁ * e₁ᵀ) := by
  have hc : IsChartAlg (1 : ℝ) (e₁ * e₁ᵀ) e₁ 1 e₁ e₁ ((2 : ℝ) • 1) e₁ ((2 : ℝ) • 1) := by
    refine ⟨e₁_orth, e₁_orth, e₁_orth, ?_, e₁_orth, ?_⟩ <;> ext i j <;> fin_cases i <;>
      fin_cases j <;> e_simp
  refine ⟨e₁, e₁, (2 : ℝ) • 1, (2 : ℝ) • 1, hc, ?_⟩
  have := prop_3_12 (h := 1) (F := e₁ * e₁ᵀ) (A₀ := e₁ * e₁ᵀ) (A₁ := (2 : ℝ) • (e₁ * e₁ᵀ))
    (Ue₀ := e₁) (Ue₁ := e₁) (Se₀ := 1) (Se₁ := (2 : ℝ) • 1) (Ve₀ := e₁) (Ve₁ := e₁) (by simp)
    (by
      ext i j; fin_cases i <;> fin_cases j <;>
        e_simp)
    e₁_orth isUnit_one (by rw [e₁_orth]; exact isUnit_one) e₁_orth (by simp) (by
      ext i j; fin_cases i <;> fin_cases j <;> e_simp)
    hc
  exact this

end Examples


/-- The local Gram pseudoinverse of this file, replaced by the core `Matrix.gramPinv` (same
definition, `(UᵀU)⁻¹Uᵀ`). -/
@[deprecated (since := "2026-11-09")] alias pinvL := Matrix.gramPinv

end LeanDLRA.Literature.P2001_08599
