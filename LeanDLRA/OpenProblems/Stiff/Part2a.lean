import LeanDLRA.OpenProblems.Stiff.Part2Defs
import LeanDLRA.Foundations.ODE
import LeanDLRA.Foundations.OneSided
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Stability.Energy
import LeanDLRA.Integrators.BUG
import LeanDLRA.Stiff.ImplicitSolvability
import LeanDLRA.Matrix.LowRankDistance
import LeanDLRA.Matrix.Frobenius

/-!
# Open problems OP-ST-13, OP-ST-14, OP-ST-15
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.OpenProblems.Stiff

open LeanDLRA

open scoped LeanDLRA.Frobenius

private theorem exp_apply_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (T : E →L[ℝ] E) (x : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • T) x) (T (NormedSpace.exp (t • T) x)) t := by
  have h := (hasDerivAt_exp_smul_const' T t).clm_apply (hasDerivAt_const t x)
  simpa using h

private theorem norm_exp_smul_apply_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (T : E →L[ℝ] E) {ℓ : ℝ} (hT : ∀ y, ⟪T y, y⟫ ≤ ℓ * ‖y‖ ^ 2) {s : ℝ}
    (hs : 0 ≤ s) (x : E) : ‖NormedSpace.exp (s • T) x‖ ≤ Real.exp (ℓ * s) * ‖x‖ := by
  have hy : ODESolution (fun _ v => T v) (fun s : ℝ => NormedSpace.exp (s • T) x) 0 s :=
    ⟨fun t _ => (exp_apply_hasDerivAt T x t).continuousAt.continuousWithinAt,
      fun t _ => (exp_apply_hasDerivAt T x t).hasDerivWithinAt⟩
  have hz : ODESolution (fun _ v => T v) (fun _ : ℝ => (0 : E)) 0 s :=
    ⟨continuousOn_const, fun t _ => by simpa using (hasDerivAt_const t (0 : E)).hasDerivWithinAt⟩
  have h := hy.norm_sub_le_exp_of_inner_le hz (ℓ := ℓ) (fun t _ => by simpa using hT _) s
    ⟨hs, le_rfl⟩
  simpa using h

private theorem comm_exp_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (𝒜 𝒢 : E →L[ℝ] E) {Cc : ℝ} (hskew : ∀ x, ⟪𝒜 x, x⟫ = 0)
    (hC : ‖𝒜 * 𝒢 - 𝒢 * 𝒜‖ ≤ Cc) {s : ℝ} (hs : 0 ≤ s) (w : E) :
    ‖NormedSpace.exp (s • 𝒜) (𝒢 w) - 𝒢 (NormedSpace.exp (s • 𝒜) w)‖ ≤ Cc * ‖w‖ * s := by
  have hA : ∀ y, ⟪𝒜 y, y⟫ ≤ 0 * ‖y‖ ^ 2 := fun y => by simp [hskew y]
  have hE : ∀ r : ℝ, 0 ≤ r → ∀ x, ‖NormedSpace.exp (r • 𝒜) x‖ ≤ ‖x‖ := fun r hr x => by
    simpa using norm_exp_smul_apply_le 𝒜 hA hr x
  set φ : ℝ → E := fun r => NormedSpace.exp (r • 𝒜) (𝒢 (NormedSpace.exp ((s - r) • 𝒜) w)) with hφ
  have hd : ∀ r : ℝ, HasDerivAt φ (NormedSpace.exp (r • 𝒜)
      ((𝒜 * 𝒢 - 𝒢 * 𝒜) (NormedSpace.exp ((s - r) • 𝒜) w))) r := by
    intro r
    have h1 : HasDerivAt (fun r : ℝ => NormedSpace.exp ((s - r) • 𝒜) w)
        (-(𝒜 (NormedSpace.exp ((s - r) • 𝒜) w))) r := by
      have h0 := exp_apply_hasDerivAt 𝒜 w (s - r)
      have h2 : HasDerivAt (fun r : ℝ => s - r) (-1) r := by
        simpa using (hasDerivAt_id r).const_sub s
      have := h0.scomp r h2
      simpa [Function.comp_def] using this
    have h3 := (𝒢.hasFDerivAt.comp_hasDerivAt r h1)
    have h4 := (hasDerivAt_exp_smul_const 𝒜 r).clm_apply h3
    refine h4.congr_deriv ?_
    have hcomm : ∀ v, (𝒜 * 𝒢 - 𝒢 * 𝒜) v = 𝒜 (𝒢 v) - 𝒢 (𝒜 v) := fun v => rfl
    have hmul : ∀ (T : E →L[ℝ] E) v, (T * 𝒜) v = T (𝒜 v) := fun T v => rfl
    simp only [map_neg, hcomm, hmul, map_sub, Function.comp_apply]
    abel
  have hCc : 0 ≤ Cc := (norm_nonneg _).trans hC
  have hb : ∀ r ∈ Ico 0 s, ‖NormedSpace.exp (r • 𝒜)
      ((𝒜 * 𝒢 - 𝒢 * 𝒜) (NormedSpace.exp ((s - r) • 𝒜) w))‖ ≤ Cc * ‖w‖ := by
    intro r hr
    calc _ ≤ ‖(𝒜 * 𝒢 - 𝒢 * 𝒜) (NormedSpace.exp ((s - r) • 𝒜) w)‖ := hE r hr.1 _
      _ ≤ ‖𝒜 * 𝒢 - 𝒢 * 𝒜‖ * ‖NormedSpace.exp ((s - r) • 𝒜) w‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ Cc * ‖w‖ := by
        refine mul_le_mul hC (hE _ (by linarith [hr.2]) w) (norm_nonneg _) hCc
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := φ) (a := 0) (b := s)
    (f' := fun r => NormedSpace.exp (r • 𝒜)
      ((𝒜 * 𝒢 - 𝒢 * 𝒜) (NormedSpace.exp ((s - r) • 𝒜) w)))
    (fun r _ => (hd r).hasDerivWithinAt) hb s ⟨hs, le_rfl⟩
  simpa [hφ, mul_comm] using h

private theorem inner_le_of_norm_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (𝒢 : E →L[ℝ] E) {LG : ℝ} (hG : ‖𝒢‖ ≤ LG) (y : E) : ⟪𝒢 y, y⟫ ≤ LG * ‖y‖ ^ 2 := by
  calc ⟪𝒢 y, y⟫ ≤ ‖𝒢 y‖ * ‖y‖ := real_inner_le_norm _ _
    _ ≤ (‖𝒢‖ * ‖y‖) * ‖y‖ := mul_le_mul_of_nonneg_right (𝒢.le_opNorm y) (norm_nonneg _)
    _ ≤ LG * ‖y‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_right hG (mul_self_nonneg ‖y‖)
      rw [sq]
      linarith

private theorem splitting_local {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (𝒜 𝒢 : E →L[ℝ] E) {LG Cc R τ : ℝ} (hskew : ∀ x, ⟪𝒜 x, x⟫ = 0)
    (hG : ‖𝒢‖ ≤ LG) (hC : ‖𝒜 * 𝒢 - 𝒢 * 𝒜‖ ≤ Cc) (hτ : 0 ≤ τ) (hτL : τ * LG ≤ 1) (v : E)
    (hv : ‖v‖ ≤ R) :
    ‖NormedSpace.exp (τ • 𝒜) (NormedSpace.exp (τ • 𝒢) v) -
      NormedSpace.exp (τ • (𝒜 + 𝒢)) v‖ ≤ Real.exp 2 * Cc * R * τ ^ 2 := by
  have hLG : 0 ≤ LG := (norm_nonneg _).trans hG
  have hCc : 0 ≤ Cc := (norm_nonneg _).trans hC
  have hR : 0 ≤ R := (norm_nonneg _).trans hv
  have hGd := inner_le_of_norm_le 𝒢 hG
  have hB : ∀ y, ⟪(𝒜 + 𝒢) y, y⟫ ≤ LG * ‖y‖ ^ 2 := fun y => by
    simpa [inner_add_left, hskew y] using hGd y
  have hF : IsOneSidedLipschitzField (fun (_ : ℝ) (v : E) => (𝒜 + 𝒢) v) LG := fun t x y => by
    simpa [map_sub] using hB (x - y)
  have hy : ∀ s : ℝ, HasDerivAt (fun s : ℝ => NormedSpace.exp (s • 𝒜) (NormedSpace.exp (s • 𝒢) v))
      (𝒜 (NormedSpace.exp (s • 𝒜) (NormedSpace.exp (s • 𝒢) v)) +
        NormedSpace.exp (s • 𝒜) (𝒢 (NormedSpace.exp (s • 𝒢) v))) s := fun s =>
    ((hasDerivAt_exp_smul_const' 𝒜 s).clm_apply (exp_apply_hasDerivAt 𝒢 v s)).congr_deriv rfl
  have hz := fun s : ℝ => exp_apply_hasDerivAt (𝒜 + 𝒢) v s
  have key := norm_sub_le_exp_mul_add_of_oneSided hF hLG (y := fun s : ℝ =>
      NormedSpace.exp (s • 𝒜) (NormedSpace.exp (s • 𝒢) v))
    (z := fun s : ℝ => NormedSpace.exp (s • (𝒜 + 𝒢)) v) (a := 0) (b := τ)
    (ηy := Cc * (Real.exp 1 * R) * τ) (ηz := 0) (δ := 0)
    (fun t _ => (hy t).continuousAt.continuousWithinAt)
    (fun t _ => (hy t).hasDerivWithinAt) ?_
    (fun t _ => (hz t).continuousAt.continuousWithinAt)
    (fun t _ => (hz t).hasDerivWithinAt) (fun t _ => by simp) (by simp) τ ⟨hτ, le_rfl⟩
  · calc _ ≤ Real.exp (LG * (τ - 0)) * (0 + (Cc * (Real.exp 1 * R) * τ + 0) * (τ - 0)) := key
      _ ≤ Real.exp 1 * (0 + (Cc * (Real.exp 1 * R) * τ + 0) * (τ - 0)) := by
        refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) ?_
        have : 0 ≤ Cc * (Real.exp 1 * R) * τ := by positivity
        nlinarith
      _ = Real.exp 2 * Cc * R * τ ^ 2 := by
        have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        rw [this]; ring
  · intro s hs
    have hw := norm_exp_smul_apply_le 𝒢 hGd hs.1 v
    have hcomm := comm_exp_le 𝒜 𝒢 hskew hC hs.1 (NormedSpace.exp (s • 𝒢) v)
    have hLs : Real.exp (LG * s) ≤ Real.exp 1 :=
      Real.exp_le_exp.2 (by nlinarith [hs.2, hLG])
    have hwn : ‖NormedSpace.exp (s • 𝒢) v‖ ≤ Real.exp 1 * R :=
      hw.trans (mul_le_mul hLs hv (norm_nonneg _) (Real.exp_pos 1).le)
    calc _ = ‖NormedSpace.exp (s • 𝒜) (𝒢 (NormedSpace.exp (s • 𝒢) v)) -
          𝒢 (NormedSpace.exp (s • 𝒜) (NormedSpace.exp (s • 𝒢) v))‖ := by
          congr 1
          simp only [add_apply]
          abel
      _ ≤ Cc * ‖NormedSpace.exp (s • 𝒢) v‖ * s := hcomm
      _ ≤ Cc * (Real.exp 1 * R) * τ := by
        have h1 : Cc * ‖NormedSpace.exp (s • 𝒢) v‖ ≤ Cc * (Real.exp 1 * R) :=
          mul_le_mul_of_nonneg_left hwn hCc
        exact mul_le_mul h1 hs.2.le hs.1 (by positivity)

/-- OP-ST-13 (source: arXiv 1803.10473 "straightforward modification", 2010.05249 proposed
extension).  Lie splitting `Y_{n+1} = e^{τ𝒜} Ψₙ` with a *skew* (isometric, non-smoothing) stiff
generator `𝒜` (periodic transport, unitary Schrödinger) and a low-rank substep `Ψₙ` approximating
`e^{τ𝒢} Yₙ` up to `δ`.  Under a commutator bound `‖[𝒜, 𝒢]‖ ≤ C_c` (uniform in the mesh for
smooth data) the method is first order,
`‖Yₙ - u(tₙ)‖ ≤ e^{L_G tₙ} (‖Y₀ - u₀‖ + n (δ + c₀ C_c R τ²))`, with an absolute constant `c₀`
and `R` bounding the exact solution; no `|log τ|`. -/
theorem lieSplitting_skew_global : ∃ c₀ : ℝ, 0 ≤ c₀ ∧
    ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      (𝒜 𝒢 : E →L[ℝ] E) (LG Cc R δ τ : ℝ) (N : ℕ) (u₀ : E) (Y Ψ : ℕ → E),
      (∀ x, ⟪𝒜 x, x⟫ = 0) → ‖𝒢‖ ≤ LG → ‖𝒜 * 𝒢 - 𝒢 * 𝒜‖ ≤ Cc → 0 ≤ τ → τ * LG ≤ 1 →
      (∀ k ≤ N, ‖NormedSpace.exp (((k : ℝ) * τ) • (𝒜 + 𝒢)) u₀‖ ≤ R) →
      (∀ n < N, ‖Ψ n - NormedSpace.exp (τ • 𝒢) (Y n)‖ ≤ δ) →
      (∀ n < N, Y (n + 1) = NormedSpace.exp (τ • 𝒜) (Ψ n)) →
      ∀ n ≤ N, ‖Y n - NormedSpace.exp (((n : ℝ) * τ) • (𝒜 + 𝒢)) u₀‖ ≤
        Real.exp (LG * (n * τ)) * (‖Y 0 - u₀‖ + n * (δ + c₀ * Cc * R * τ ^ 2)) := by
  refine ⟨Real.exp 2, (Real.exp_pos 2).le, ?_⟩
  intro E _ _ _ 𝒜 𝒢 LG Cc R δ τ N u₀ Y Ψ hskew hG hC hτ hτL hR hΨ hY n hn
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  let : NormedAlgebra ℚ (E →L[ℝ] E) := NormedAlgebra.restrictScalars ℚ ℝ _
  have hLG : 0 ≤ LG := (norm_nonneg _).trans hG
  have hCc : 0 ≤ Cc := (norm_nonneg _).trans hC
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR 0 (Nat.zero_le _))
  have hGd := inner_le_of_norm_le 𝒢 hG
  have hA : ∀ y, ⟪𝒜 y, y⟫ ≤ 0 * ‖y‖ ^ 2 := fun y => by simp [hskew y]
  set loc : ℝ := Real.exp 2 * Cc * R * τ ^ 2 with hloc
  have hloc0 : 0 ≤ loc := by positivity
  set u : ℕ → E := fun k => NormedSpace.exp (((k : ℝ) * τ) • (𝒜 + 𝒢)) u₀ with hu_def
  have hu : ∀ k, u (k + 1) = NormedSpace.exp (τ • (𝒜 + 𝒢)) (u k) := by
    intro k
    have h1 : (((k + 1 : ℕ) : ℝ) * τ) • (𝒜 + 𝒢) = τ • (𝒜 + 𝒢) + (((k : ℝ) * τ) • (𝒜 + 𝒢)) := by
      push_cast; module
    have h2 : Commute (τ • (𝒜 + 𝒢)) (((k : ℝ) * τ) • (𝒜 + 𝒢)) :=
      ((Commute.refl (𝒜 + 𝒢)).smul_left τ).smul_right _
    simp only [hu_def]
    rw [h1, NormedSpace.exp_add_of_commute h2]
    rfl
  have claim : ∀ k ≤ N, ‖Y k - u k‖ ≤
      Real.exp (LG * (k * τ)) * (‖Y 0 - u₀‖ + k * (δ + loc)) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp [hu_def]
    | succ k ih =>
      intro hk
      have hkN : k < N := hk
      have ih' := ih hkN.le
      have hδ : 0 ≤ δ := (norm_nonneg _).trans (hΨ k hkN)
      have hd : 0 ≤ δ + loc := add_nonneg hδ hloc0
      have hexpA : ∀ x : E, ‖NormedSpace.exp (τ • 𝒜) x‖ ≤ ‖x‖ := fun x => by
        simpa using norm_exp_smul_apply_le 𝒜 hA hτ x
      have hexpG : ∀ x : E, ‖NormedSpace.exp (τ • 𝒢) x‖ ≤ Real.exp (LG * τ) * ‖x‖ := fun x =>
        norm_exp_smul_apply_le 𝒢 hGd hτ x
      have hl := splitting_local 𝒜 𝒢 hskew hG hC hτ hτL (u k) (hR k hkN.le)
      have e1 : Y (k + 1) - u (k + 1) =
          NormedSpace.exp (τ • 𝒜) (Ψ k - NormedSpace.exp (τ • 𝒢) (Y k)) +
          NormedSpace.exp (τ • 𝒜) (NormedSpace.exp (τ • 𝒢) (Y k - u k)) +
          (NormedSpace.exp (τ • 𝒜) (NormedSpace.exp (τ • 𝒢) (u k)) -
            NormedSpace.exp (τ • (𝒜 + 𝒢)) (u k)) := by
        rw [hY k hkN, hu k]
        simp only [map_sub]
        abel
      have hstep : ‖Y (k + 1) - u (k + 1)‖ ≤ δ + Real.exp (LG * τ) * ‖Y k - u k‖ + loc := by
        rw [e1]
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) hl)
        · exact (hexpA _).trans (hΨ k hkN)
        · exact (hexpA _).trans (hexpG _)
      have hE1 : Real.exp (LG * τ) * Real.exp (LG * (k * τ)) =
          Real.exp (LG * ((k + 1 : ℕ) * τ)) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      have hEk : 1 ≤ Real.exp (LG * ((k + 1 : ℕ) * τ)) :=
        Real.one_le_exp (by positivity)
      have hE1p := Real.exp_pos (LG * τ)
      have h5 := mul_le_mul_of_nonneg_left ih' hE1p.le
      rw [← hE1] at hEk ⊢
      push_cast
      have h6 : 0 ≤ Real.exp (LG * τ) * Real.exp (LG * (k * τ)) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hEk hd, hstep, h5]
  exact claim n hn

section Sylvester

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

private theorem symm_negSemidef_decomp {A : Matrix m m ℝ} (hA : (-A).PosSemidef) :
    ∃ (U : Matrix m m ℝ) (d : m → ℝ), Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧ (∀ i, d i ≤ 0) ∧
      A = U * Matrix.diagonal d * Uᵀ := by
  have hH := hA.isHermitian
  have hspec := hH.spectral_theorem
  have hU : (hH.eigenvectorUnitary : Matrix m m ℝ) ∈ Matrix.unitaryGroup m ℝ :=
    (hH.eigenvectorUnitary).2
  refine ⟨(hH.eigenvectorUnitary : Matrix m m ℝ), fun i => -(hH.eigenvalues i), ?_, ?_, ?_, ?_⟩
  · have := Matrix.mem_unitaryGroup_iff'.1 hU
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  · have := Matrix.mem_unitaryGroup_iff.1 hU
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  · intro i
    have := hA.eigenvalues_nonneg i
    linarith
  · have h2 : -A = (hH.eigenvectorUnitary : Matrix m m ℝ) * Matrix.diagonal hH.eigenvalues *
        star (hH.eigenvectorUnitary : Matrix m m ℝ) := by
      simpa using hspec
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h2
    have h5 : Matrix.diagonal (fun i => -(hH.eigenvalues i)) = -Matrix.diagonal hH.eigenvalues := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    calc A = -(-A) := (neg_neg A).symm
      _ = -((hH.eigenvectorUnitary : Matrix m m ℝ) * Matrix.diagonal hH.eigenvalues *
          (hH.eigenvectorUnitary : Matrix m m ℝ)ᵀ) := congrArg Neg.neg h2
      _ = _ := by rw [h5, Matrix.mul_neg, Matrix.neg_mul]

private theorem sylvesterFlow_eq {U : Matrix m m ℝ} {V : Matrix n n ℝ} {d : m → ℝ} {e : n → ℝ}
    (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1) (hV : Vᵀ * V = 1) (hV' : V * Vᵀ = 1) (t : ℝ)
    (Z : Matrix m n ℝ) :
    sylvesterFlow (U * Matrix.diagonal d * Uᵀ) (V * Matrix.diagonal e * Vᵀ) t Z =
      U * (Matrix.diagonal (fun i => Real.exp (t * d i)) * (Uᵀ * Z * V) *
        Matrix.diagonal (fun j => Real.exp (t * e j))) * Vᵀ := by
  have hunitU : IsUnit U := ⟨⟨U, Uᵀ, hU', hU⟩, rfl⟩
  have hunitV : IsUnit V := ⟨⟨V, Vᵀ, hV', hV⟩, rfl⟩
  have hinvU : U⁻¹ = Uᵀ := Matrix.inv_eq_right_inv hU'
  have hinvV : V⁻¹ = Vᵀ := Matrix.inv_eq_right_inv hV'
  have hD : ∀ c : m → ℝ, Matrix.diagonal (fun i => t * c i) = t • Matrix.diagonal c := by
    intro c
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hD' : ∀ c : n → ℝ, Matrix.diagonal (fun i => t * c i) = t • Matrix.diagonal c := by
    intro c
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hA : t • (U * Matrix.diagonal d * Uᵀ) = U * Matrix.diagonal (fun i => t * d i) * U⁻¹ := by
    rw [hinvU, hD, Matrix.mul_smul, Matrix.smul_mul]
  have hB : t • (V * Matrix.diagonal e * Vᵀ) = V * Matrix.diagonal (fun j => t * e j) * V⁻¹ := by
    rw [hinvV, hD', Matrix.mul_smul, Matrix.smul_mul]
  unfold sylvesterFlow
  rw [hA, hB, Matrix.exp_conj U _ hunitU, Matrix.exp_conj V _ hunitV, Matrix.exp_diagonal,
    Matrix.exp_diagonal, hinvU, hinvV, Pi.exp_def, Pi.exp_def]
  simp only [← Real.exp_eq_exp_ℝ, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.diagonal_transpose, Matrix.mul_assoc]

private theorem sq_mul_exp_neg_le {x : ℝ} (hx : 0 ≤ x) :
    (x * Real.exp (-x)) ^ 2 ≤ Real.exp (-1) ^ 2 := by
  have h1 := Real.add_one_le_exp (x - 1)
  have h3 : x * Real.exp (-x) ≤ Real.exp (-1) :=
    calc x * Real.exp (-x) ≤ Real.exp (x - 1) * Real.exp (-x) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ = Real.exp (-1) := by rw [← Real.exp_add]; congr 1; ring
  exact pow_le_pow_left₀ (mul_nonneg hx (Real.exp_pos _).le) h3 2

private theorem sylvester_core {U : Matrix m m ℝ} {V : Matrix n n ℝ} {d : m → ℝ} {e : n → ℝ}
    (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1) (hV : Vᵀ * V = 1) (hV' : V * Vᵀ = 1)
    (hd : ∀ i, d i ≤ 0) (he : ∀ j, e j ≤ 0) {t : ℝ} (ht : 0 ≤ t) (Z : Matrix m n ℝ) :
    ⟪(U * Matrix.diagonal d * Uᵀ) * Z + Z * (V * Matrix.diagonal e * Vᵀ)ᵀ, Z⟫ ≤ 0 ∧
      ‖sylvesterFlow (U * Matrix.diagonal d * Uᵀ) (V * Matrix.diagonal e * Vᵀ) t Z‖ ≤ ‖Z‖ ∧
      ‖t • ((U * Matrix.diagonal d * Uᵀ) *
          sylvesterFlow (U * Matrix.diagonal d * Uᵀ) (V * Matrix.diagonal e * Vᵀ) t Z +
        sylvesterFlow (U * Matrix.diagonal d * Uᵀ) (V * Matrix.diagonal e * Vᵀ) t Z *
          (V * Matrix.diagonal e * Vᵀ)ᵀ)‖ ≤ Real.exp (-1) * ‖Z‖ := by
  have hU1 : ∀ (X : Matrix m n ℝ), U * (Uᵀ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hU', Matrix.one_mul]
  have hU2 : ∀ (X : Matrix m n ℝ), Uᵀ * (U * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  have hV1 : ∀ (X : Matrix m n ℝ), (X * V) * Vᵀ = X := fun X => by
    rw [Matrix.mul_assoc, hV', Matrix.mul_one]
  have hV2 : ∀ (X : Matrix m n ℝ), (X * Vᵀ) * V = X := fun X => by
    rw [Matrix.mul_assoc, hV, Matrix.mul_one]
  have hBT : (V * Matrix.diagonal e * Vᵀ)ᵀ = V * Matrix.diagonal e * Vᵀ := by
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  set Zp : Matrix m n ℝ := Uᵀ * Z * V with hZp
  set M : (m → n → ℝ) → Matrix m n ℝ := fun φ => Matrix.of fun i j => φ i j * Zp i j with hM
  set Φ : (m → n → ℝ) → Matrix m n ℝ := fun φ => U * M φ * Vᵀ with hΦ
  have hV3 : ∀ Y : Matrix n n ℝ, Vᵀ * (V * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hV, Matrix.one_mul]
  have hZ : Z = Φ (fun _ _ => 1) := by
    have h1 : M (fun _ _ => 1) = Zp := by ext i j; simp [hM]
    simp only [hΦ, h1, hZp, Matrix.mul_assoc]
    rw [hV', Matrix.mul_one, hU1]
  have hAΦ : ∀ φ, (U * Matrix.diagonal d * Uᵀ) * Φ φ = Φ (fun i j => d i * φ i j) := by
    intro φ
    have hDM : Matrix.diagonal d * M φ = M (fun i j => d i * φ i j) := by
      ext i j; simp [hM, Matrix.diagonal_mul]; ring
    calc _ = U * (Matrix.diagonal d * M φ) * Vᵀ := by simp only [hΦ, Matrix.mul_assoc, hU2]
      _ = _ := by rw [hDM]
  have hΦB : ∀ φ, Φ φ * (V * Matrix.diagonal e * Vᵀ) = Φ (fun i j => φ i j * e j) := by
    intro φ
    have hME : M φ * Matrix.diagonal e = M (fun i j => φ i j * e j) := by
      ext i j; simp [hM, Matrix.mul_diagonal]; ring
    calc _ = U * (M φ * Matrix.diagonal e) * Vᵀ := by simp only [hΦ, Matrix.mul_assoc, hV3]
      _ = _ := by rw [hME]
  have hflow : sylvesterFlow (U * Matrix.diagonal d * Uᵀ) (V * Matrix.diagonal e * Vᵀ) t Z =
      Φ (fun i j => Real.exp (t * d i) * Real.exp (t * e j)) := by
    rw [sylvesterFlow_eq hU hU' hV hV']
    have : Matrix.diagonal (fun i => Real.exp (t * d i)) * Zp *
        Matrix.diagonal (fun j => Real.exp (t * e j)) =
        M (fun i j => Real.exp (t * d i) * Real.exp (t * e j)) := by
      ext i j; simp [hM, Matrix.diagonal_mul, Matrix.mul_diagonal]; ring
    simp only [hΦ, hZp] at this ⊢
    rw [this]
  have hadd : ∀ φ ψ, Φ φ + Φ ψ = Φ (fun i j => φ i j + ψ i j) := by
    intro φ ψ
    have : M φ + M ψ = M (fun i j => φ i j + ψ i j) := by
      ext i j; simp [hM]; ring
    calc Φ φ + Φ ψ = U * (M φ + M ψ) * Vᵀ := by
          simp only [hΦ]; rw [Matrix.mul_add, Matrix.add_mul]
      _ = _ := by rw [this]
  have hsmul : ∀ φ, t • Φ φ = Φ (fun i j => t * φ i j) := by
    intro φ
    have : t • M φ = M (fun i j => t * φ i j) := by
      ext i j; simp [hM]; ring
    calc t • Φ φ = U * (t • M φ) * Vᵀ := by
          simp only [hΦ]; rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = _ := by rw [this]
  have hnorm : ∀ φ, ‖Φ φ‖ ^ 2 = ∑ i, ∑ j, (φ i j * Zp i j) ^ 2 := by
    intro φ
    have : ‖Φ φ‖ = ‖M φ‖ := by
      simp only [hΦ]
      rw [LeanDLRA.Frobenius.norm_mul_transpose_of_orthonormal hV,
        LeanDLRA.Frobenius.norm_mul_of_orthonormal hU]
    rw [this, LeanDLRA.Frobenius.norm_sq_eq_sum]
    rfl
  have hinner : ∀ φ ψ, ⟪Φ φ, Φ ψ⟫ = ∑ i, ∑ j, (φ i j * Zp i j) * (ψ i j * Zp i j) := by
    intro φ ψ
    have h1 : ⟪Φ φ, Φ ψ⟫ = ⟪M φ, M ψ⟫ := by
      simp only [hΦ]
      rw [LeanDLRA.Frobenius.inner_mul_right, Matrix.transpose_transpose, hV2,
        LeanDLRA.Frobenius.inner_mul_mul_of_orthonormal hU]
    rw [h1, LeanDLRA.Frobenius.inner_def]
    rfl
  have hAZ : (U * Matrix.diagonal d * Uᵀ) * Z + Z * (V * Matrix.diagonal e * Vᵀ)ᵀ =
      Φ (fun i j => d i + e j) := by
    have e1 := hAΦ (fun _ _ => 1)
    have e2 := hΦB (fun _ _ => 1)
    rw [← hZ] at e1 e2
    rw [hBT, e1, e2, hadd]
    simp only [mul_one, one_mul]
  have hfz : ‖Z‖ ^ 2 = ∑ i, ∑ j, Zp i j ^ 2 := by
    have := hnorm (fun _ _ => 1)
    rw [← hZ] at this
    simpa using this
  have hf0 : ∀ i j, 0 ≤ Real.exp (t * d i) * Real.exp (t * e j) := fun i j =>
    mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hfs : ∀ i j, Real.exp (t * d i) * Real.exp (t * e j) = Real.exp (t * (d i + e j)) :=
    fun i j => by rw [← Real.exp_add]; congr 1; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hAZ]
    rw [hZ]
    rw [hinner]
    refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j _ => ?_
    have h1 : d i + e j ≤ 0 := add_nonpos (hd i) (he j)
    nlinarith [sq_nonneg (Zp i j)]
  · rw [hflow]
    refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [hnorm, hfz]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have h1 : Real.exp (t * d i) * Real.exp (t * e j) ≤ 1 := by
      rw [hfs]
      exact Real.exp_le_one_iff.2 (by nlinarith [hd i, he j])
    have h2 := hf0 i j
    nlinarith [sq_nonneg (Zp i j), mul_nonneg h2 (sq_nonneg (Zp i j))]
  · rw [hflow, hAΦ, hBT, hΦB, hadd, hsmul]
    refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
    rw [hnorm, mul_pow, hfz, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have hs : d i + e j ≤ 0 := add_nonpos (hd i) (he j)
    have hx : 0 ≤ -(t * (d i + e j)) := by nlinarith
    have hk := sq_mul_exp_neg_le hx
    have hg : t * (d i * (Real.exp (t * d i) * Real.exp (t * e j)) +
        Real.exp (t * d i) * Real.exp (t * e j) * e j) =
        -(-(t * (d i + e j)) * Real.exp (-(-(t * (d i + e j))))) := by
      rw [hfs, neg_neg]; ring
    rw [hg, mul_pow, neg_sq]
    nlinarith [mul_le_mul_of_nonneg_right hk (sq_nonneg (Zp i j))]

/-- OP-ST-14 (source: Lumer–Phillips / literature constants cited in arXiv 1906.01369,
2010.05249; matrix form).  For symmetric negative semidefinite `A`, `B` (discrete Laplacians)
the Sylvester generator `𝒜 Z = A Z + Z Bᵀ` is dissipative in the Frobenius inner product, its
flow `e^{t𝒜} Z = e^{tA} Z e^{tB}ᵀ` is non-expansive, and it smooths with the grid-independent
constant `1/e`: `‖t 𝒜 (e^{t𝒜} Z)‖ ≤ e⁻¹ ‖Z‖`. -/
theorem sylvester_dissipative_smoothing {A : Matrix m m ℝ} {B : Matrix n n ℝ}
    (hA : (-A).PosSemidef) (hB : (-B).PosSemidef) {t : ℝ} (ht : 0 ≤ t) (Z : Matrix m n ℝ) :
    ⟪A * Z + Z * Bᵀ, Z⟫ ≤ 0 ∧
      ‖sylvesterFlow A B t Z‖ ≤ ‖Z‖ ∧
      ‖t • (A * sylvesterFlow A B t Z + sylvesterFlow A B t Z * Bᵀ)‖ ≤ Real.exp (-1) * ‖Z‖ := by
  obtain ⟨U, d, hU, hU', hd, rfl⟩ := symm_negSemidef_decomp hA
  obtain ⟨V, e, hV, hV', he, rfl⟩ := symm_negSemidef_decomp hB
  exact sylvester_core hU hU' hV hV' hd he ht Z

private theorem toeplitz_partial_le {g : ℕ → ℝ} (hgk : ∀ k, 1 ≤ k → g k ≤ 0) {m M : ℕ}
    (h : m ≤ M) : ∑ k ∈ range M, g (k + 1) ≤ ∑ k ∈ range m, g (k + 1) := by
  rw [← Finset.sum_range_add_sum_Ico _ h]
  have : ∑ k ∈ Ico m M, g (k + 1) ≤ 0 :=
    Finset.sum_nonpos fun k _ => hgk _ (by omega)
  linarith

private theorem toeplitz_Icc_eq (g : ℕ → ℝ) (M : ℕ) :
    ∑ k ∈ Icc 1 M, g k = ∑ k ∈ range M, g (k + 1) := by
  induction M with
  | zero => simp
  | succ M ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

private theorem toeplitz_rowsum_nonneg {N : ℕ} {g : ℕ → ℝ}
    (hgk : ∀ k, 1 ≤ k → g k ≤ 0) (hsum : ∀ M, 0 ≤ g 0 + 2 * ∑ k ∈ Icc 1 M, g k) (i : Fin N) :
    0 ≤ ∑ j : Fin N, g (Int.natAbs ((i : ℤ) - j)) := by
  have hi := i.2
  rw [Fin.sum_univ_eq_sum_range (fun j => g (Int.natAbs ((i : ℤ) - j))) N]
  rw [← Finset.sum_range_add_sum_Ico _ (show (i : ℕ) + 1 ≤ N by omega), Finset.sum_range_succ]
  have h1 : ∑ j ∈ range (i : ℕ), g (Int.natAbs ((i : ℤ) - j)) =
      ∑ k ∈ range (i : ℕ), g (k + 1) := by
    rw [← Finset.sum_range_reflect (fun k => g (k + 1)) (i : ℕ)]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    congr 1
    omega
  have h2 : ∑ j ∈ Ico ((i : ℕ) + 1) N, g (Int.natAbs ((i : ℤ) - j)) =
      ∑ k ∈ range (N - ((i : ℕ) + 1)), g (k + 1) := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun j hj => ?_
    congr 1
    omega
  rw [h1, h2]
  have h3 := toeplitz_partial_le hgk (m := (i : ℕ)) (M := N - 1) (by omega)
  have h4 := toeplitz_partial_le hgk (m := N - ((i : ℕ) + 1)) (M := N - 1) (by omega)
  have h5 := hsum (N - 1)
  rw [toeplitz_Icc_eq] at h5
  simp only [Int.sub_self, Int.natAbs_zero]
  linarith

/-- OP-ST-14 (diagonal dominance lemma).  A symmetric Toeplitz matrix `G_{ij} = g_{|i-j|}` with
`g₀ > 0 ≥ g_k` (`k ≥ 1`) and nonnegative truncated symbol `g₀ + 2 ∑_{k=1}^{M} g_k ≥ 0` (discrete
fractional Laplacian stencils, `∑_{k ∈ ℤ} g_k = 0`) is positive semidefinite, so `-G` generates a
contraction. -/
theorem toeplitz_posSemidef_of_diagDominant {N : ℕ} {g : ℕ → ℝ} (hg0 : 0 < g 0)
    (hgk : ∀ k, 1 ≤ k → g k ≤ 0) (hsum : ∀ M, 0 ≤ g 0 + 2 * ∑ k ∈ Icc 1 M, g k) :
    (Matrix.of fun i j : Fin N => g (Int.natAbs ((i : ℤ) - j))).PosSemidef := by
  set G : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun i j : Fin N => g (Int.natAbs ((i : ℤ) - j))
    with hG
  have hsymm : ∀ i j, G i j = G j i := by
    intro i j
    simp only [hG, Matrix.of_apply]
    congr 1
    omega
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext i j
    simp [Matrix.conjTranspose_apply, hsymm i j]
  · have _ := hg0
    have hr : ∀ i, 0 ≤ ∑ j, G i j := fun i => toeplitz_rowsum_nonneg hgk hsum i
    have hoff : ∀ i j, i ≠ j → G i j ≤ 0 := by
      intro i j hij
      have : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
      exact hgk _ (by omega)
    have e1 : ∑ i, ∑ j, G i j * x j ^ 2 = ∑ i, ∑ j, G i j * x i ^ 2 := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hsymm]
    have ha : 0 ≤ ∑ i, (∑ j, G i j) * x i ^ 2 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hr i) (sq_nonneg _)
    have hb : 0 ≤ ∑ i, ∑ j, (-G i j) * (x i - x j) ^ 2 := by
      refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
      by_cases hij : i = j
      · subst hij; simp
      · exact mul_nonneg (neg_nonneg.2 (hoff i j hij)) (sq_nonneg _)
    have hterm : ∀ i j, (-G i j) * (x i - x j) ^ 2 =
        -(G i j * x i ^ 2) + 2 * (x i * (G i j * x j)) - G i j * x j ^ 2 := fun i j => by ring
    simp only [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      ← Finset.mul_sum, e1] at hb
    simp only [Finset.sum_mul] at ha
    simp only [star_trivial, dotProduct, Matrix.mulVec]
    linarith

end Sylvester

private theorem smoothing_aux {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (S : E →L[ℝ] E) (hsym : ∀ x y, ⟪S x, y⟫ = ⟪x, S y⟫)
    (hneg : ∀ x, ⟪S x, x⟫ ≤ 0) (y : ℝ → E) (hy : ∀ t, HasDerivAt y (S (y t)) t) {t : ℝ}
    (ht : 0 ≤ t) : ‖t • S (y t)‖ ≤ Real.exp (-1) * ‖y 0‖ := by
  have hT : (S : E →ₗ[ℝ] E).IsSymmetric := fun x y => hsym x y
  let b := hT.eigenvectorBasis rfl
  let lam := hT.eigenvalues rfl
  have hb : ∀ i, S (b i) = lam i • b i := fun i => hT.apply_eigenvectorBasis rfl i
  have hlam : ∀ i, lam i ≤ 0 := fun i => by
    have h1 := hneg (b i)
    have hn1 : ‖b i‖ = 1 := b.orthonormal.1 i
    rw [hb i, real_inner_smul_left, real_inner_self_eq_norm_sq, hn1] at h1
    simpa using h1
  have hc : ∀ i τ, ⟪b i, y τ⟫ = Real.exp (lam i * τ) * ⟪b i, y 0⟫ := by
    intro i τ
    have hg : ∀ σ : ℝ, HasDerivAt (fun σ => Real.exp (-(lam i * σ)) * ⟪b i, y σ⟫) 0 σ := by
      intro σ
      have h1 : HasDerivAt (fun σ : ℝ => Real.exp (-(lam i * σ)))
          (Real.exp (-(lam i * σ)) * (-(lam i))) σ := by
        have := ((hasDerivAt_id σ).const_mul (lam i)).neg.exp
        simpa using this
      have h2 : HasDerivAt (fun σ => ⟪b i, y σ⟫) (lam i * ⟪b i, y σ⟫) σ := by
        have := (hasDerivAt_const σ (b i)).inner ℝ (hy σ)
        simpa [← hsym, hb i, inner_smul_left] using this
      have := h1.mul h2
      convert this using 1
      ring
    have hconst := is_const_of_deriv_eq_zero (f := fun σ => Real.exp (-(lam i * σ)) * ⟪b i, y σ⟫)
      (fun σ => (hg σ).differentiableAt) (fun σ => (hg σ).deriv) τ 0
    simp only [mul_zero, neg_zero, Real.exp_zero, one_mul] at hconst
    have : Real.exp (lam i * τ) * Real.exp (-(lam i * τ)) = 1 := by
      rw [← Real.exp_add]; simp
    calc ⟪b i, y τ⟫ = Real.exp (lam i * τ) * (Real.exp (-(lam i * τ)) * ⟪b i, y τ⟫) := by
          rw [← mul_assoc, this, one_mul]
      _ = _ := by rw [hconst]
  have hnorm : ‖t • S (y t)‖ ^ 2 = ∑ i, (t * lam i * Real.exp (lam i * t) * ⟪b i, y 0⟫) ^ 2 := by
    rw [← b.sum_sq_norm_inner_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.norm_eq_abs, sq_abs, inner_smul_right, ← hsym, hb i, inner_smul_left, hc i t]
    simp only [conj_trivial]
    ring
  have h0 : ‖y 0‖ ^ 2 = ∑ i, ⟪b i, y 0⟫ ^ 2 := by
    rw [← b.sum_sq_norm_inner_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
  have hterm : ∀ i, (t * lam i * Real.exp (lam i * t)) ^ 2 ≤ Real.exp (-1) ^ 2 := by
    intro i
    obtain ⟨x, hx0, hx⟩ : ∃ x : ℝ, 0 ≤ x ∧ x = -(t * lam i) :=
      ⟨-(t * lam i), by nlinarith [hlam i], rfl⟩
    have e1 : t * lam i * Real.exp (lam i * t) = -(x * Real.exp (-x)) := by
      rw [show lam i * t = -x by rw [hx]; ring, show t * lam i = -x by rw [hx]; ring]
      ring
    have h3 : x * Real.exp (-x) ≤ Real.exp (-1) := by
      have h1 := Real.add_one_le_exp (x - 1)
      calc x * Real.exp (-x) ≤ Real.exp (x - 1) * Real.exp (-x) :=
            mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
        _ = Real.exp (-1) := by rw [← Real.exp_add]; congr 1; ring
    rw [e1, neg_sq]
    exact pow_le_pow_left₀ (mul_nonneg hx0 (Real.exp_pos _).le) h3 2
  have hsq : ‖t • S (y t)‖ ^ 2 ≤ (Real.exp (-1) * ‖y 0‖) ^ 2 := by
    rw [hnorm, mul_pow, h0, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (hterm i) (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hsq

private theorem norm_exp_skew_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (T : E →L[ℝ] E) (hT : ∀ y, ⟪T y, y⟫ = 0) (s : ℝ) (x : E) :
    ‖NormedSpace.exp (s • T) x‖ ≤ ‖x‖ := by
  rcases le_total 0 s with hs | hs
  · simpa using norm_exp_smul_apply_le T (ℓ := 0) (fun y => by simp [hT y]) hs x
  · have h := norm_exp_smul_apply_le (-T) (ℓ := 0)
      (fun y => by simp [hT y]) (neg_nonneg.2 hs) x
    have : (-s) • -T = s • T := by simp
    rw [this] at h
    simpa using h

/-- OP-ST-14 (complex case, abstract core).  Complex matrices are a real inner product space with
a complex structure `J` (`J² = -1`, `J` skew).  For `H` symmetric negative semidefinite commuting
with `J` and `ν > 0`, the generator `𝒢 = (ν + i η) H = ν H + η J H` is dissipative and smooths
with the grid-independent constant `|ν + i η| / (e ν)`. -/
theorem complexSylvester_dissipative_smoothing {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {H J : E →L[ℝ] E}
    (hHsym : ∀ x y, ⟪H x, y⟫ = ⟪x, H y⟫) (hHneg : ∀ x, ⟪H x, x⟫ ≤ 0)
    (hJJ : ∀ x, J (J x) = -x) (hJskew : ∀ x y, ⟪J x, y⟫ = -⟪x, J y⟫)
    (hHJ : ∀ x, H (J x) = J (H x)) {ν η t : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) :
    (∀ x, ⟪(ν • H + η • (J * H)) x, x⟫ ≤ 0) ∧
      ‖NormedSpace.exp (t • (ν • H + η • (J * H)))‖ ≤ 1 ∧
      ‖(t • (ν • H + η • (J * H))) * NormedSpace.exp (t • (ν • H + η • (J * H)))‖ ≤
        Real.sqrt (ν ^ 2 + η ^ 2) / (Real.exp 1 * ν) := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  let : NormedAlgebra ℚ (E →L[ℝ] E) := NormedAlgebra.restrictScalars ℚ ℝ _
  set K : E →L[ℝ] E := J * H with hK
  have hKapp : ∀ x, K x = J (H x) := fun x => rfl
  have hJx : ∀ x, ⟪J x, x⟫ = 0 := fun x => by
    have := hJskew x x
    have h2 := real_inner_comm x (J x)
    linarith
  have hKskew : ∀ x, ⟪K x, x⟫ = 0 := fun x => by
    have h1 : ⟪K x, x⟫ = -⟪x, K x⟫ := by
      rw [hKapp x, hJskew, hHsym, hHJ]
    have h2 := real_inner_comm x (K x)
    linarith
  set G : E →L[ℝ] E := ν • H + η • K with hG
  have hGapp : ∀ x, G x = ν • H x + η • J (H x) := fun x => rfl
  have hG1 : ∀ x, ⟪G x, x⟫ ≤ 0 := fun x => by
    rw [hGapp, inner_add_left, inner_smul_left, inner_smul_left, ← hKapp, hKskew]
    simpa using mul_nonpos_of_nonneg_of_nonpos hν.le (hHneg x)
  refine ⟨hG1, ?_, ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    simpa using norm_exp_smul_apply_le G (ℓ := 0) (fun y => by simpa using hG1 y) ht x
  · have hHK : Commute H K := by
      ext x
      change H (J (H x)) = J (H (H x))
      rw [hHJ]
    have hKexp : ∀ r : ℝ, Commute K (NormedSpace.exp (r • K)) := fun r =>
      ((Commute.refl K).smul_right r).exp_right
    have hHexp : ∀ r : ℝ, Commute H (NormedSpace.exp (r • K)) := fun r =>
      (hHK.smul_right r).exp_right
    have hGexp : ∀ r : ℝ, Commute G (NormedSpace.exp (r • K)) := fun r =>
      ((hHexp r).smul_left ν).add_left ((hKexp r).smul_left η)
    have hsplit : t • G = (t * η) • K + t • (ν • H) := by
      rw [hG]; module
    have hcomm2 : Commute ((t * η) • K) (t • (ν • H)) :=
      ((hHK.symm.smul_left (t * η)).smul_right ν).smul_right t
    have hexpG : NormedSpace.exp (t • G) =
        NormedSpace.exp ((t * η) • K) * NormedSpace.exp (t • (ν • H)) := by
      rw [hsplit]; exact NormedSpace.exp_add_of_commute hcomm2
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
    have hsym : ∀ x y, ⟪(ν • H) x, y⟫ = ⟪x, (ν • H) y⟫ := fun x y => by
      simp [inner_smul_left, inner_smul_right, hHsym x y]
    have hneg : ∀ x, ⟪(ν • H) x, x⟫ ≤ 0 := fun x => by
      simpa [inner_smul_left] using mul_nonpos_of_nonneg_of_nonpos hν.le (hHneg x)
    have hw : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => NormedSpace.exp (τ • (ν • H)) x)
        ((ν • H) (NormedSpace.exp (τ • (ν • H)) x)) τ := fun τ =>
      exp_apply_hasDerivAt (ν • H) x τ
    have hsm := smoothing_aux (ν • H) hsym hneg _ hw ht
    simp only [zero_smul, NormedSpace.exp_zero, one_apply_eq_self] at hsm
    set z := NormedSpace.exp (t • (ν • H)) x with hz
    set p := H z with hp
    have hJp : ∀ p : E, ‖ν • p + η • J p‖ = Real.sqrt (ν ^ 2 + η ^ 2) * ‖p‖ := by
      intro p
      have h1 : ‖J p‖ ^ 2 = ‖p‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hJskew, hJJ,
          inner_neg_right, neg_neg]
      have h2 : ⟪ν • p, η • J p⟫ = 0 := by
        rw [inner_smul_left, inner_smul_right, real_inner_comm, hJx]; simp
      have h3 : ‖ν • p + η • J p‖ ^ 2 = (ν ^ 2 + η ^ 2) * ‖p‖ ^ 2 := by
        rw [norm_add_sq_real, h2, norm_smul, norm_smul, mul_pow, mul_pow, h1]
        simp only [Real.norm_eq_abs, sq_abs]
        ring
      rw [← Real.sqrt_sq (norm_nonneg (ν • p + η • J p)), h3, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (norm_nonneg p)]
    have hval : ((t • G) * NormedSpace.exp (t • G)) x =
        NormedSpace.exp ((t * η) • K) (t • (ν • p + η • J p)) := by
      have h1 : G (NormedSpace.exp ((t * η) • K) z) = NormedSpace.exp ((t * η) • K) (G z) :=
        congrArg (fun T : E →L[ℝ] E => T z) (hGexp (t * η)).eq
      rw [hexpG]
      change t • G (NormedSpace.exp ((t * η) • K) z) = _
      rw [h1, ← map_smul, hGapp]
    have hn1 : ‖((t • G) * NormedSpace.exp (t • G)) x‖ ≤ t * (Real.sqrt (ν ^ 2 + η ^ 2) * ‖p‖) := by
      rw [hval]
      refine (norm_exp_skew_le K hKskew _ _).trans ?_
      rw [norm_smul, hJp, Real.norm_eq_abs, abs_of_nonneg ht]
    have hn2 : t * (ν * ‖p‖) ≤ Real.exp (-1) * ‖x‖ := by
      have := hsm
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at this
      change t * ‖ν • p‖ ≤ _ at this
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hν] at this
      exact this
    have hn3 : t * ‖p‖ ≤ Real.exp (-1) * ‖x‖ / ν := by
      rw [le_div_iff₀ hν]; nlinarith
    have hq : 0 ≤ Real.sqrt (ν ^ 2 + η ^ 2) := Real.sqrt_nonneg _
    calc _ ≤ _ := hn1
      _ = Real.sqrt (ν ^ 2 + η ^ 2) * (t * ‖p‖) := by ring
      _ ≤ Real.sqrt (ν ^ 2 + η ^ 2) * (Real.exp (-1) * ‖x‖ / ν) :=
          mul_le_mul_of_nonneg_left hn3 hq
      _ = Real.sqrt (ν ^ 2 + η ^ 2) / (Real.exp 1 * ν) * ‖x‖ := by
          rw [Real.exp_neg]; field_simp

section Necessity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- OP-ST-15 (source: arXiv 2006.05211, 2307.07538, 2411.06844; eigenmode counterexample).  If
an unstable eigenvector `w` of the full explicit Euler step (`|1 + hλ| > 1`, e.g. `λ ~ -c/h_x²`
with `dt > 2 h_x²/c`) lies in every Galerkin space, the explicit-Euler DLRA iterates equal the
full iterates `(1 + hλ)ⁿ w` and blow up: the CFL restriction is necessary. -/
theorem galerkinEuler_unstable_of_eigen {A : E →L[ℝ] E} {P : ℕ → E →L[ℝ] E}
    (hP : ∀ n, IsOrthProj (P n)) {w : E} {lam h : ℝ} (hw : A w = lam • w)
    (hfix : ∀ n, P n w = w) (hamp : 1 < |1 + h * lam|) :
    (∀ n, galerkinEulerIter P (fun _ x => A x) h w n = (1 + h * lam) ^ n • w) ∧
      (w ≠ 0 → Tendsto (fun n => ‖galerkinEulerIter P (fun _ x => A x) h w n‖) atTop atTop) := by
  have _ := hP 0
  have key : ∀ n, galerkinEulerIter P (fun _ x => A x) h w n = (1 + h * lam) ^ n • w := by
    intro n
    induction n with
    | zero => simp [galerkinEulerIter]
    | succ n ih =>
      have hPz : P n ((1 + h * lam) ^ n • w) = (1 + h * lam) ^ n • w := by
        rw [map_smul, hfix]
      have hstep : (1 + h * lam) ^ n • w + h • A ((1 + h * lam) ^ n • w) =
          (1 + h * lam) ^ (n + 1) • w := by
        rw [map_smul, hw, smul_smul, smul_smul, ← add_smul]
        congr 1
        ring
      rw [galerkinEulerIter, galerkinEulerStep, ih, hPz, eulerStep, hstep, map_smul, hfix]
  refine ⟨key, fun hw0 => ?_⟩
  simp only [key, norm_smul, norm_pow, Real.norm_eq_abs]
  exact Filter.Tendsto.atTop_mul_const (norm_pos_iff.2 hw0)
    (tendsto_pow_atTop_atTop_of_one_lt hamp)

/-- OP-ST-15 (central differences, source: arXiv 2411.06844).  For a skew field `A` with an
invariant rotation plane (`A (A x) = -ω² x`, e.g. a Fourier mode with `ω = v sin ν / dx`) captured
by the Galerkin spaces, explicit Euler amplifies exactly by `(1 + h²ω²)` in the squared norm per
step, so `(1 + h²ω²)^{T/h}` stays bounded iff `h ≲ dx²/(v² T)`. -/
theorem galerkinEuler_skew_growth {A : E →L[ℝ] E} {P : ℕ → E →L[ℝ] E}
    (hP : ∀ n, IsOrthProj (P n)) (hskew : ∀ y, ⟪A y, y⟫ = 0) {x : E} {ω h : ℝ}
    (hAA : A (A x) = -(ω ^ 2) • x) (hfix : ∀ n, P n x = x) (hfixA : ∀ n, P n (A x) = A x)
    (n : ℕ) :
    ‖galerkinEulerIter P (fun _ y => A y) h x n‖ ^ 2 = (1 + h ^ 2 * ω ^ 2) ^ n * ‖x‖ ^ 2 := by
  have _ := hP 0
  have hpol : ∀ y z, ⟪A y, z⟫ = -⟪y, A z⟫ := by
    intro y z
    have h1 := hskew (y + z)
    simp only [map_add, inner_add_left, inner_add_right, hskew y, hskew z] at h1
    rw [real_inner_comm y (A z)] at h1
    linarith
  have hA2 : ∀ a b : ℝ, A (A (a • x + b • A x)) = -(ω ^ 2) • (a • x + b • A x) := by
    intro a b
    simp only [map_add, map_smul, hAA]
    module
  have hspan : ∀ a b : ℝ, ∀ k, P k (a • x + b • A x) = a • x + b • A x := by
    intro a b k
    rw [map_add, map_smul, map_smul, hfix, hfixA]
  have hstep : ∀ a b : ℝ, eulerStep (fun y => A y) h (a • x + b • A x) =
      (a - h * b * ω ^ 2) • x + (b + h * a) • A x := by
    intro a b
    simp only [eulerStep, map_add, map_smul, hAA]
    module
  have inv : ∀ n, ∃ a b : ℝ, galerkinEulerIter P (fun _ y => A y) h x n = a • x + b • A x := by
    intro n
    induction n with
    | zero => exact ⟨1, 0, by simp [galerkinEulerIter]⟩
    | succ n ih =>
      obtain ⟨a, b, hz⟩ := ih
      refine ⟨a - h * b * ω ^ 2, b + h * a, ?_⟩
      rw [galerkinEulerIter, galerkinEulerStep, hz, hspan, hstep, hspan]
  induction n with
  | zero => simp [galerkinEulerIter]
  | succ n ih =>
    obtain ⟨a, b, hz⟩ := inv n
    have hnorm : ‖galerkinEulerIter P (fun _ y => A y) h x (n + 1)‖ =
        ‖eulerStep (fun y => A y) h (galerkinEulerIter P (fun _ y => A y) h x n)‖ := by
      rw [galerkinEulerIter, galerkinEulerStep, hz, hspan, hstep, hspan, ← hstep, ← hz]
    rw [hnorm, norm_eulerStep_sq, hskew, pow_succ]
    have hAz : ‖A (galerkinEulerIter P (fun _ y => A y) h x n)‖ ^ 2 =
        ω ^ 2 * ‖galerkinEulerIter P (fun _ y => A y) h x n‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hpol, hz, hA2,
        inner_smul_right, ← hz]
      ring
    rw [hAz]
    linear_combination (1 + h ^ 2 * ω ^ 2) * ih

end Necessity

section Splitting

end Splitting

section SAT

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end SAT

end LeanDLRA.OpenProblems.Stiff
