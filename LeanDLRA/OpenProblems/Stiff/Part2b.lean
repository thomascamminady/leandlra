import LeanDLRA.OpenProblems.Stiff.Part2Defs
import LeanDLRA.Foundations.OneSided
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Stability.Energy
import LeanDLRA.Integrators.BUG
import LeanDLRA.Stiff.ImplicitSolvability
import LeanDLRA.Matrix.LowRankDistance
import LeanDLRA.Matrix.Frobenius

/-!
# Open problems OP-ST-16, OP-ST-17, OP-ST-18, OP-ST-19
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.OpenProblems.Stiff

open LeanDLRA

open scoped LeanDLRA.Frobenius

section Sylvester

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

end Sylvester

section Necessity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Necessity

private theorem line_ode_aux {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (v e : V)
    {f f' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t) (F : ℝ → V → V)
    (hF : ∀ t, F t (v + f t • e) = f' t • e) (a b : ℝ) :
    ODESolution F (fun t => v + f t • e) a b := by
  have hd : ∀ t, HasDerivAt (fun t => v + f t • e) (f' t • e) t := fun t =>
    ((hf t).smul_const e).const_add v
  refine ⟨fun t _ => (hd t).continuousAt.continuousWithinAt, fun t _ => ?_⟩
  rw [hF t]
  exact (hd t).hasDerivWithinAt

private theorem line_ode_aux2 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (e : V)
    {f f' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t) (F : ℝ → V → V)
    (hF : ∀ t, F t (f t • e) = f' t • e) (a b : ℝ) :
    ODESolution F (fun t => f t • e) a b := by
  have := line_ode_aux 0 e hf F (by simpa using hF) a b
  simpa using this

private theorem rankOne_orthProj_aux {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (w : V) :
    IsOrthProj ((‖w‖ ^ 2)⁻¹ • (innerSL ℝ w).smulRight w : V →L[ℝ] V) := by
  by_cases hw : w = 0
  · subst hw
    constructor <;> simp
  · have hn : ‖w‖ ^ 2 ≠ 0 := by positivity
    constructor
    · intro x
      simp only [smul_apply, ContinuousLinearMap.smulRight_apply,
        innerSL_apply_apply, inner_smul_right, real_inner_self_eq_norm_sq, smul_smul]
      congr 1
      field_simp
    · intro x y
      simp only [smul_apply, ContinuousLinearMap.smulRight_apply,
        innerSL_apply_apply, inner_smul_left, inner_smul_right, conj_trivial]
      rw [real_inner_comm w x]
      ring

private theorem bug_cex_aux (κ : ℝ) (hκ : 0 < κ) :
    ∃ (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
      (P₀ Q₀ P₁ Q₁ : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
      (Y₀ : EuclideanSpace ℝ (Fin 2)) (YK YL YS Ex : ℝ → EuclideanSpace ℝ (Fin 2)),
      IsOneSidedLipschitzField (fun _ x => A x) 0 ∧
      IsBUGStep (fun _ x => A x) 0 P₀ Q₀ P₁ Q₁ 0 (1 / κ) Y₀ YK YL YS ∧
      ODESolution (fun _ x => A x) Ex 0 (1 / κ) ∧ Ex 0 = Y₀ ∧ ‖Y₀‖ = Real.sqrt 2 ∧
      (1 / 20 : ℝ) ≤ ‖YS (1 / κ) - Ex (1 / κ)‖ := by
  have : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin 2)) := IsBoundedSMul.continuousSMul
  set e1 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1 with he1
  set e2 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1 with he2
  have i11 : ⟪e1, e1⟫ = 1 := by simp [he1]
  have i22 : ⟪e2, e2⟫ = 1 := by simp [he2]
  have i12 : ⟪e1, e2⟫ = 0 := by
    rw [he1, he2, EuclideanSpace.inner_single_left]; simp
  have i21 : ⟪e2, e1⟫ = 0 := by
    rw [he1, he2, EuclideanSpace.inner_single_left]; simp
  set A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    (-κ) • (innerSL ℝ e2).smulRight e2 with hA
  have hAx : ∀ x, A x = (-κ * ⟪e2, x⟫) • e2 := by
    intro x
    simp [hA, mul_smul]
  set ρ : ℝ := Real.exp (-1) with hρ
  have hρ0 : 0 < ρ := Real.exp_pos _
  set w : EuclideanSpace ℝ (Fin 2) := e1 + ρ • e2 with hw
  have iw2 : ⟪e2, w⟫ = ρ := by
    rw [hw, inner_add_right, inner_smul_right, i21, i22]; ring
  have iw : ⟪w, w⟫ = 1 + ρ ^ 2 := by
    rw [hw]
    simp only [inner_add_right, inner_add_left, inner_smul_left, inner_smul_right, i11, i12, i21,
      i22, conj_trivial]
    ring
  have hwn : ‖w‖ ^ 2 = 1 + ρ ^ 2 := by rw [← real_inner_self_eq_norm_sq]; exact iw
  set Y₀ : EuclideanSpace ℝ (Fin 2) := e1 + e2 with hY₀
  have iwY : ⟪w, Y₀⟫ = 1 + ρ := by
    rw [hw, hY₀]
    simp only [inner_add_right, inner_add_left, inner_smul_left, i11, i12,
      i21, i22, conj_trivial]
    ring
  have iwe2 : ⟪w, e2⟫ = ρ := by rw [real_inner_comm]; exact iw2
  set Q₁ : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    (‖w‖ ^ 2)⁻¹ • (innerSL ℝ w).smulRight w with hQ₁
  have hQx : ∀ x, Q₁ x = ((1 + ρ ^ 2)⁻¹ * ⟪w, x⟫) • w := by
    intro x
    simp [hQ₁, hwn, mul_smul]
  have hQ₁proj : IsOrthProj Q₁ := rankOne_orthProj_aux w
  set lam : ℝ := κ * ρ ^ 2 / (1 + ρ ^ 2) with hlam
  have hρ2 : 0 < 1 + ρ ^ 2 := by positivity
  have hQAw : ∀ s : ℝ, Q₁ (A (s • w)) = (-lam * s) • w := by
    intro s
    rw [hAx, inner_smul_right, iw2, map_smul, hQx, iwe2, smul_smul]
    congr 1
    rw [hlam]; field_simp
  set c : ℝ := (1 + ρ) / (1 + ρ ^ 2) with hc
  set Ex : ℝ → EuclideanSpace ℝ (Fin 2) := fun t => e1 + Real.exp (-κ * t) • e2 with hEx
  set YS : ℝ → EuclideanSpace ℝ (Fin 2) := fun t => (c * Real.exp (-lam * t)) • w with hYS
  have hExode : ∀ F : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      (∀ t x, F t x = A x) → ODESolution F Ex 0 (1 / κ) := by
    intro F hF
    refine line_ode_aux e1 e2 (f := fun t => Real.exp (-κ * t))
      (f' := fun t => -κ * Real.exp (-κ * t)) ?_ F ?_ 0 (1 / κ)
    · intro t
      have := ((hasDerivAt_id' t).const_mul (-κ)).exp
      convert this using 1
      ring
    · intro t
      rw [hF, hAx, inner_add_right, inner_smul_right, i21, i22]
      congr 1; ring
  have hEx1 : Ex (1 / κ) = w := by
    simp only [hEx, hw, hρ]
    congr 3
    field_simp
  have hExY : Ex 0 = Y₀ := by simp [hEx, hY₀]
  have hQw : Q₁ w = w := by
    rw [hQx, iw, inv_mul_cancel₀ hρ2.ne', one_smul]
  have hQY : Q₁ Y₀ = c • w := by
    rw [hQx, iwY, hc, div_eq_inv_mul]
  have hYSode : ODESolution (fun _ x => (1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] _) (Q₁ (A x))) YS 0
      (1 / κ) := by
    refine line_ode_aux2 w (f := fun t => c * Real.exp (-lam * t))
      (f' := fun t => -lam * (c * Real.exp (-lam * t))) ?_ _ ?_ 0 (1 / κ)
    · intro t
      have := (((hasDerivAt_id' t).const_mul (-lam)).exp).const_mul c
      convert this using 1
      ring
    · intro t
      simp only [one_apply_eq_self]
      exact hQAw _
  have hYS1 : YS (1 / κ) - Ex (1 / κ) = (c * Real.exp (-(ρ ^ 2 / (1 + ρ ^ 2))) - 1) • w := by
    rw [hEx1]
    simp only [hYS]
    have : -lam * (1 / κ) = -(ρ ^ 2 / (1 + ρ ^ 2)) := by
      rw [hlam]; field_simp
    rw [this, sub_smul, one_smul]
  have hY0n : ‖Y₀‖ ^ 2 = 2 := by
    rw [← real_inner_self_eq_norm_sq, hY₀]
    simp only [inner_add_right, inner_add_left, i11, i12, i21, i22]
    norm_num
  have hρlo : (367 / 1000 : ℝ) ≤ ρ ∧ ρ ≤ 369 / 1000 := by
    have h1 := Real.exp_one_gt_d9
    have h2 := Real.exp_one_lt_d9
    have e : ρ = (Real.exp 1)⁻¹ := by rw [hρ, Real.exp_neg]
    rw [e]
    constructor
    · rw [le_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
      linarith
    · rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      linarith
  have hsbound : 1 + 1 / 20 ≤ c * Real.exp (-(ρ ^ 2 / (1 + ρ ^ 2))) := by
    have hx : 1 / (1 + ρ ^ 2) ≤ Real.exp (-(ρ ^ 2 / (1 + ρ ^ 2))) := by
      have := Real.add_one_le_exp (-(ρ ^ 2 / (1 + ρ ^ 2)))
      have e : 1 / (1 + ρ ^ 2) = -(ρ ^ 2 / (1 + ρ ^ 2)) + 1 := by field_simp; ring
      rw [e]; exact this
    have hc0 : 0 ≤ c := by rw [hc]; positivity
    have h3 : c * (1 / (1 + ρ ^ 2)) ≤ c * Real.exp (-(ρ ^ 2 / (1 + ρ ^ 2))) :=
      mul_le_mul_of_nonneg_left hx hc0
    refine le_trans ?_ h3
    rw [hc, div_mul_div_comm, mul_one, le_div_iff₀ (by positivity)]
    have hsq : ρ ^ 2 ≤ 1362 / 10000 := by nlinarith [hρlo.1, hρlo.2]
    have hsq' : (1 + ρ ^ 2) * (1 + ρ ^ 2) ≤ (11362 / 10000) * (11362 / 10000) := by
      have : 0 ≤ ρ ^ 2 := by positivity
      nlinarith only [this, hsq]
    nlinarith only [hρlo.1, hρlo.2, hsq, hsq']
  have hwn1 : 1 ≤ ‖w‖ := by
    by_contra hlt
    have := pow_lt_one₀ (norm_nonneg w) (not_le.1 hlt) two_ne_zero
    rw [hwn] at this
    linarith [sq_nonneg ρ]
  refine ⟨A, 1, 1, 1, Q₁, Y₀, Ex, Ex, YS, Ex, ?_, ?_, hExode _ (fun _ _ => rfl), hExY, ?_, ?_⟩
  · have hos : ∀ z, ⟪A z, z⟫ ≤ 0 := by
      intro z
      rw [hAx, inner_smul_left]
      simp only [conj_trivial]
      have h := mul_nonneg hκ.le (mul_self_nonneg ⟪e2, z⟫)
      linarith
    intro t x y
    have := hos (x - y)
    rw [map_sub] at this
    simpa using this
  · refine ⟨IsOrthProj.one, IsOrthProj.one, IsOrthProj.one, hQ₁proj, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · intro x; simp
    · exact hExode _ (fun _ _ => rfl)
    · exact hExY
    · simp
    · intro t _; simp
    · exact hExode _ (fun _ _ => rfl)
    · exact hExY
    · rw [hEx1]; exact hQw
    · intro t _; simp
    · exact hYSode
    · rw [hQY]; simp [hYS, hc]
  · rw [← hY0n, Real.sqrt_sq (norm_nonneg _)]
  · rw [hYS1, norm_smul, Real.norm_eq_abs]
    have : 1 / 20 ≤ |c * Real.exp (-(ρ ^ 2 / (1 + ρ ^ 2))) - 1| := by
      rw [abs_of_nonneg (by linarith)]; linarith
    calc (1 / 20 : ℝ) ≤ |c * Real.exp (-(ρ ^ 2 / (1 + ρ ^ 2))) - 1| * 1 := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hwn1 (abs_nonneg _)

/-- OP-ST-16 (source: survey computation; explains failures in arXiv 2312.00172, 2410.17091).
No stiffness-robust bound `‖Y₁ - A(t₁)‖ ≤ C(ℓ, ε, ‖Y₀‖) hᵖ` (`p > 0`) holds for one exact BUG
step, even restricted to linear fields on `ℝ^{1×2}`: the family `F(Y) = Y diag(0, -κ)`
(`ℓ = 0`, `ε = 0`) with `h = 1/κ` has local error `≈ 0.0523 ‖Y₀‖` for every `κ`. -/
theorem no_oneSided_bug_bound :
    ¬ ∃ (C : ℝ → ℝ → ℝ → ℝ) (p : ℝ), 0 < p ∧
      ∀ (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) (ℓ ε h : ℝ)
        (P₀ Q₀ P₁ Q₁ : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
        (Y₀ : EuclideanSpace ℝ (Fin 2)) (YK YL YS Ex : ℝ → EuclideanSpace ℝ (Fin 2)),
        0 < h → IsOneSidedLipschitzField (fun _ x => A x) ℓ →
        IsBUGStep (fun _ x => A x) ε P₀ Q₀ P₁ Q₁ 0 h Y₀ YK YL YS →
        ODESolution (fun _ x => A x) Ex 0 h → Ex 0 = Y₀ →
        ‖YS h - Ex h‖ ≤ C ℓ ε ‖Y₀‖ * h ^ p := by
  rintro ⟨C, p, hp, H⟩
  set C0 : ℝ := |C 0 0 (Real.sqrt 2)| with hC0
  have hC0n : 0 ≤ C0 := abs_nonneg _
  set h : ℝ := ((1 / 20) / (C0 + 1)) ^ p⁻¹ with hh
  have hhpos : 0 < h := Real.rpow_pos_of_pos (by positivity) _
  have hhp : h ^ p = (1 / 20) / (C0 + 1) := by
    rw [hh]; exact Real.rpow_inv_rpow (by positivity) hp.ne'
  obtain ⟨A, P₀, Q₀, P₁, Q₁, Y₀, YK, YL, YS, Ex, hos, hbug, hode, hEx0, hY0, hlow⟩ :=
    bug_cex_aux h⁻¹ (inv_pos.2 hhpos)
  have e : 1 / h⁻¹ = h := by rw [one_div, inv_inv]
  rw [e] at hbug hode hlow
  have key := H A 0 0 h P₀ Q₀ P₁ Q₁ Y₀ YK YL YS Ex hhpos hos hbug hode hEx0
  rw [hY0] at key
  have hpow : 0 ≤ h ^ p := (Real.rpow_pos_of_pos hhpos _).le
  have h1 : C 0 0 (Real.sqrt 2) * h ^ p ≤ C0 * h ^ p :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hpow
  have h2 : C0 * h ^ p < 1 / 20 := by
    rw [hhp, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- OP-ST-17 (source: arXiv 2305.11532; existence of the whole scheme on `M_{≤ r}`).  For a
continuous energy bounded below and every `h > 0`, starting from `rank X₀ ≤ r`, there is a
minimising-movement sequence on the closed set `M_{≤ r}` and it is unconditionally energy
stable: `ℰ(X_{k+1}) + ‖X_{k+1} - X_k‖²/(2h) ≤ ℰ(X_k)`. -/
theorem mm_lowRank_sequence {m n : Type*} [Fintype m] [Fintype n] {r : ℕ}
    {ℰ : Matrix m n ℝ → ℝ} (hℰ : Continuous ℰ) {lb : ℝ} (hlb : ∀ X, lb ≤ ℰ X) {h : ℝ}
    (hh : 0 < h) {X₀ : Matrix m n ℝ} (hX₀ : X₀.rank ≤ r) :
    ∃ X : ℕ → Matrix m n ℝ, X 0 = X₀ ∧ ∀ k, X (k + 1) ∈ lowRankSet m n r ∧
      (∀ Z ∈ lowRankSet m n r, mmObjective ℰ h (X k) (X (k + 1)) ≤ mmObjective ℰ h (X k) Z) ∧
      ℰ (X (k + 1)) + ‖X (k + 1) - X k‖ ^ 2 / (2 * h) ≤ ℰ (X k) := by
  have key : ∀ Y : Matrix m n ℝ, ∃ Z : Matrix m n ℝ, Y.rank ≤ r →
      Z ∈ lowRankSet m n r ∧
      (∀ W ∈ lowRankSet m n r, mmObjective ℰ h Y Z ≤ mmObjective ℰ h Y W) := by
    intro Y
    by_cases hY : Y.rank ≤ r
    · obtain ⟨Z, hZ, hmin⟩ := mm_exists_minimizer (isClosed_lowRankSet r) (X₀ := Y) hY hℰ hlb hh
      exact ⟨Z, fun _ => ⟨hZ, hmin⟩⟩
    · exact ⟨Y, fun h' => absurd h' hY⟩
  choose F hF using key
  let X : ℕ → Matrix m n ℝ := fun k => Nat.rec X₀ (fun _ Y => F Y) k
  have hX0 : X 0 = X₀ := rfl
  have hXs : ∀ k, X (k + 1) = F (X k) := fun k => rfl
  have hrank : ∀ k, (X k).rank ≤ r := by
    intro k
    induction k with
    | zero => exact hX₀
    | succ k ih => rw [hXs]; exact (hF _ ih).1
  refine ⟨X, hX0, fun k => ?_⟩
  have h1 := hF _ (hrank k)
  rw [hXs]
  refine ⟨h1.1, h1.2, ?_⟩
  exact mm_energy_le (h1.2 _ (hrank k))

section Splitting

private theorem rank_triple_aux {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (P : Matrix m m ℝ) (Q : Matrix n n ℝ) (Y : Matrix m n ℝ)
    (hP : IsUnit P.det) (hQ : IsUnit Q.det) : (P * Y * Qᵀ).rank = Y.rank := by
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (by rwa [Matrix.det_transpose]),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hP]

/-- OP-ST-18 (a) (source: PERK-DEIM).  The Sylvester flow `Y ↦ e^{tA} Y e^{tB}ᵀ` maps rank-`r`
matrices to rank-`r` matrices, so the stiff linear substep needs no projection. -/
theorem sylvesterFlow_rank_eq {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m m ℝ) (B : Matrix n n ℝ) (t : ℝ) (Y : Matrix m n ℝ) :
    (sylvesterFlow A B t Y).rank = Y.rank := by
  unfold sylvesterFlow
  refine rank_triple_aux _ _ _ ?_ ?_
  · exact (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp (𝔸 := ℝ) (t • A))
  · exact (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp (𝔸 := ℝ) (t • B))

/-- OP-ST-18 (b) (source: Lie splitting with randomized substeps DRSVD/DGN).  Composed Lady
Windermere fan: a non-expansive stiff flow `S = e^{τ𝒜}` (`μ₂(A) ≤ 0`, mesh-independent), an
`e^{L_N τ}`-Lipschitz flow `Φ_N` of the non-stiff nonlinearity, low-rank substeps with error `δ`
and exact Lie splitting error `c_s τ²` give `‖Yₙ - uₙ‖ ≤ e^{L_N tₙ} (‖Y₀ - u₀‖ + n (c_s τ² + δ))`.
-/
theorem lieSplitting_generic_global {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {S : E →L[ℝ] E} (hS : ∀ x, ‖S x‖ ≤ ‖x‖) {ΦN : E → E} {LN τ cs δ : ℝ}
    (hΦ : ∀ x y, ‖ΦN x - ΦN y‖ ≤ Real.exp (LN * τ) * ‖x - y‖) (hLN : 0 ≤ LN) (hτ : 0 ≤ τ)
    {N : ℕ} {u Y Ψ : ℕ → E} (hsplit : ∀ n < N, ‖S (ΦN (u n)) - u (n + 1)‖ ≤ cs * τ ^ 2)
    (hsub : ∀ n < N, ‖Ψ n - ΦN (Y n)‖ ≤ δ) (hY : ∀ n < N, Y (n + 1) = S (Ψ n)) :
    ∀ n ≤ N, ‖Y n - u n‖ ≤ Real.exp (LN * (n * τ)) * (‖Y 0 - u 0‖ + n * (cs * τ ^ 2 + δ)) := by
  have key : ∀ n, n ≤ N → ‖Y n - u n‖ ≤
      Real.exp (LN * (n * τ)) * (‖Y 0 - u 0‖ + n * (cs * τ ^ 2 + δ)) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hnN : n < N := hn
      have ih' := ih hnN.le
      have hs := hsplit n hnN
      have hb := hsub n hnN
      have hd : 0 ≤ cs * τ ^ 2 + δ := by
        have := norm_nonneg (S (ΦN (u n)) - u (n + 1))
        have := norm_nonneg (Ψ n - ΦN (Y n))
        linarith
      have h1 : 1 ≤ Real.exp (LN * (n * τ)) := Real.one_le_exp (by positivity)
      have h2 : 1 ≤ Real.exp (LN * τ) := Real.one_le_exp (by positivity)
      have hsplitE : Real.exp (LN * ((n + 1 : ℕ) * τ)) =
          Real.exp (LN * (n * τ)) * Real.exp (LN * τ) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      have step : ‖Y (n + 1) - u (n + 1)‖ ≤
          Real.exp (LN * τ) * ‖Y n - u n‖ + (cs * τ ^ 2 + δ) := by
        have a1 : Y (n + 1) - u (n + 1) =
            S (Ψ n - ΦN (u n)) + (S (ΦN (u n)) - u (n + 1)) := by
          rw [hY n hnN, map_sub]; abel
        have a2 : ‖S (Ψ n - ΦN (u n))‖ ≤ ‖Ψ n - ΦN (u n)‖ := hS _
        have a3 : ‖Ψ n - ΦN (u n)‖ ≤ ‖Ψ n - ΦN (Y n)‖ + ‖ΦN (Y n) - ΦN (u n)‖ := by
          have := norm_add_le (Ψ n - ΦN (Y n)) (ΦN (Y n) - ΦN (u n))
          simpa using this
        have a4 := hΦ (Y n) (u n)
        have a5 := norm_add_le (S (Ψ n - ΦN (u n))) (S (ΦN (u n)) - u (n + 1))
        rw [a1]
        linarith
      rw [hsplitE]
      have hcast : ((n + 1 : ℕ) : ℝ) = n + 1 := by push_cast; ring
      rw [hcast]
      have hpos : 0 ≤ Real.exp (LN * τ) := (Real.exp_pos _).le
      have m1 : Real.exp (LN * τ) * ‖Y n - u n‖ ≤ Real.exp (LN * τ) *
          (Real.exp (LN * (n * τ)) * (‖Y 0 - u 0‖ + n * (cs * τ ^ 2 + δ))) :=
        mul_le_mul_of_nonneg_left ih' hpos
      have m2 : (cs * τ ^ 2 + δ) ≤ Real.exp (LN * (n * τ)) * Real.exp (LN * τ) *
          (cs * τ ^ 2 + δ) := by
        have : 1 ≤ Real.exp (LN * (n * τ)) * Real.exp (LN * τ) := by nlinarith
        nlinarith
      nlinarith
  exact key

/-- OP-ST-18 (c) (obstacle for mesh independence).  The Allen–Cahn nonlinearity `X - X.^3` is
Lipschitz in the Frobenius norm with constant `1 + 3c²` on the max-norm ball `|X_{ij}| ≤ c`; a
mesh-independent analysis therefore needs uniform max-norm bounds on the low-rank iterates. -/
theorem allenCahn_frobenius_lipschitz {m n : Type*} [Fintype m] [Fintype n] {c : ℝ}
    {X Y : Matrix m n ℝ} (hX : ∀ i j, |X i j| ≤ c) (hY : ∀ i j, |Y i j| ≤ c) :
    ‖(Matrix.of fun i j => X i j - X i j ^ 3) - Matrix.of fun i j => Y i j - Y i j ^ 3‖ ≤
      (1 + 3 * c ^ 2) * ‖X - Y‖ := by
  have hc : ∀ i j, |(X i j - X i j ^ 3) - (Y i j - Y i j ^ 3)| ≤
      (1 + 3 * c ^ 2) * |X i j - Y i j| := by
    intro i j
    have hx := abs_le.1 (hX i j)
    have hy := abs_le.1 (hY i j)
    have e : (X i j - X i j ^ 3) - (Y i j - Y i j ^ 3) =
        (X i j - Y i j) * (1 - (X i j ^ 2 + X i j * Y i j + Y i j ^ 2)) := by ring
    rw [e, abs_mul]
    have hq : |1 - (X i j ^ 2 + X i j * Y i j + Y i j ^ 2)| ≤ 1 + 3 * c ^ 2 := by
      have hc0 : 0 ≤ c := (abs_nonneg _).trans (hX i j)
      have q1 : X i j ^ 2 ≤ c ^ 2 := by nlinarith
      have q2 : Y i j ^ 2 ≤ c ^ 2 := by nlinarith
      have q3 : |X i j * Y i j| ≤ c ^ 2 := by
        rw [abs_mul, sq]; exact mul_le_mul (hX i j) (hY i j) (abs_nonneg _) hc0
      have q4 := abs_le.1 q3
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (X i j), sq_nonneg (Y i j)]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hq (abs_nonneg _)
  set K : ℝ := 1 + 3 * c ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  rw [Frobenius.norm_def, Frobenius.norm_def]
  have : √(∑ i, ∑ j, (((Matrix.of fun i j => X i j - X i j ^ 3) -
      Matrix.of fun i j => Y i j - Y i j ^ 3) i j) ^ 2) ≤
      √(K ^ 2 * ∑ i, ∑ j, ((X - Y) i j) ^ 2) := by
    apply Real.sqrt_le_sqrt
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro j _
    have := hc i j
    simp only [Matrix.sub_apply, Matrix.of_apply] at this ⊢
    calc _ = |X i j - X i j ^ 3 - (Y i j - Y i j ^ 3)| ^ 2 := (sq_abs _).symm
      _ ≤ (K * |X i j - Y i j|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = K ^ 2 * (X i j - Y i j) ^ 2 := by rw [mul_pow, sq_abs]
  refine this.trans_eq ?_
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hK0]

end Splitting

section SAT

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem euler_defect_aux {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {L : E →L[ℝ] E} {g : ℝ → E} {τ M : ℝ} (hτ : 0 ≤ τ) {N : ℕ} {U : ℝ → E}
    (hU : ODESolution (fun t x => L x + g t) U 0 (N * τ))
    (hM : ∀ s ∈ Icc (0 : ℝ) (N * τ), ∀ t ∈ Icc (0 : ℝ) (N * τ),
      ‖(L (U t) + g t) - (L (U s) + g s)‖ ≤ M * |t - s|) {n : ℕ} (hn : n < N) :
    ‖U ((n + 1 : ℕ) * τ) - U (n * τ) - τ • (L (U (n * τ)) + g (n * τ))‖ ≤ τ / 2 * M * τ := by
  have hNτ : ((n + 1 : ℕ) : ℝ) * τ ≤ N * τ :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hτ
  have hnτ : (n : ℝ) * τ ≤ ((n + 1 : ℕ) : ℝ) * τ :=
    mul_le_mul_of_nonneg_right (by push_cast; linarith) hτ
  have hn0 : 0 ≤ (n : ℝ) * τ := by positivity
  set t0 : ℝ := n * τ with ht0
  have hcast : ((n + 1 : ℕ) : ℝ) * τ = t0 + τ := by rw [ht0]; push_cast; ring
  rw [hcast] at hNτ ⊢
  set φ : ℝ → E := fun r => U (t0 + r) - U t0 - r • (L (U t0) + g t0) with hφ
  have hcont : ContinuousOn φ (Icc 0 τ) := by
    have h1 : ContinuousOn (fun r : ℝ => U (t0 + r)) (Icc 0 τ) := by
      refine hU.cont.comp (continuousOn_const.add continuousOn_id) ?_
      intro r hr
      exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
    exact (h1.sub continuousOn_const).sub (continuousOn_id.smul continuousOn_const)
  have hder : ∀ r ∈ Ico (0 : ℝ) τ, HasDerivWithinAt φ
      ((L (U (t0 + r)) + g (t0 + r)) - (L (U t0) + g t0)) (Ici r) r := by
    intro r hr
    have hmem : t0 + r ∈ Ico (0 : ℝ) (N * τ) := ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have h1 := hU.deriv (t0 + r) hmem
    have h2 : HasDerivWithinAt (fun r : ℝ => t0 + r) 1 (Ici r) r :=
      ((hasDerivAt_id r).const_add t0).hasDerivWithinAt
    have h3 := HasDerivWithinAt.scomp r h1 h2 (fun x hx => by
      simp only [Set.mem_Ici] at hx ⊢; linarith)
    have h4 : HasDerivWithinAt (fun r : ℝ => r • (L (U t0) + g t0)) (L (U t0) + g t0)
        (Ici r) r := by
      simpa using ((hasDerivAt_id r).smul_const (L (U t0) + g t0)).hasDerivWithinAt
    have h5 := (h3.sub_const (U t0)).sub h4
    convert h5 using 1
    · funext r
      simp [hφ, smul_add, sub_sub]
    · rw [one_smul]
  have hB : ∀ x : ℝ, HasDerivAt (fun r : ℝ => M * r ^ 2 / 2) (M * x) x := by
    intro x
    have := ((hasDerivAt_pow 2 x).const_mul M).div_const 2
    convert this using 1
    simp; ring
  have := image_norm_le_of_norm_deriv_right_le_deriv_boundary hcont hder
    (B := fun r : ℝ => M * r ^ 2 / 2) (B' := fun r => M * r) (by simp [hφ]) hB
    (fun r hr => by
      have hmem : t0 + r ∈ Icc (0 : ℝ) (N * τ) := ⟨by linarith [hr.1], by linarith [hr.2]⟩
      have hmem0 : t0 ∈ Icc (0 : ℝ) (N * τ) := ⟨hn0, by linarith⟩
      have := hM t0 hmem0 (t0 + r) hmem
      rwa [add_sub_cancel_left, abs_of_nonneg hr.1] at this) (x := τ) ⟨hτ, le_rfl⟩
  simpa [hφ, ht0] using this.trans_eq (by ring)

/-- OP-ST-19 (source: arXiv 2609.02721).  Forward Euler for `U' = L_h U + g(t)` with the
discrete stability `‖I + τ L_h‖ ≤ 1` has error `‖uₙ - U(tₙ)‖ ≤ tₙ (τ/2) M`, where `M` is the
time-Lipschitz constant of `U'` (a bound on `‖U''‖`): first order with a mesh-independent
constant although the stiffness is `~ 1/h`. -/
theorem forwardEuler_meshIndep_error {L : E →L[ℝ] E} {g : ℝ → E} {τ M : ℝ} (hτ : 0 ≤ τ)
    (hstab : ∀ x, ‖x + τ • L x‖ ≤ ‖x‖) {N : ℕ} {U : ℝ → E}
    (hU : ODESolution (fun t x => L x + g t) U 0 (N * τ))
    (hM : ∀ s ∈ Icc (0 : ℝ) (N * τ), ∀ t ∈ Icc (0 : ℝ) (N * τ),
      ‖(L (U t) + g t) - (L (U s) + g s)‖ ≤ M * |t - s|)
    {u : ℕ → E} (hu0 : u 0 = U 0) (hu : ∀ n < N, u (n + 1) = u n + τ • (L (u n) + g (n * τ))) :
    ∀ n ≤ N, ‖u n - U (n * τ)‖ ≤ n * τ * (τ / 2 * M) := by
  intro n
  induction n with
  | zero => intro _; simp [hu0]
  | succ n ih =>
    intro hn
    have hnN : n < N := hn
    have ih' := ih hnN.le
    have hd := euler_defect_aux hτ hU hM hnN
    rw [hu n hnN]
    have e1 : u n + τ • (L (u n) + g (n * τ)) - U ((n + 1 : ℕ) * τ) =
        ((u n - U (n * τ)) + τ • L (u n - U (n * τ))) -
        (U ((n + 1 : ℕ) * τ) - U (n * τ) - τ • (L (U (n * τ)) + g (n * τ))) := by
      simp only [map_sub, smul_sub, smul_add]; abel
    rw [e1]
    have h1 := norm_sub_le ((u n - U (n * τ)) + τ • L (u n - U (n * τ)))
      (U ((n + 1 : ℕ) * τ) - U (n * τ) - τ • (L (U (n * τ)) + g (n * τ)))
    have h2 := hstab (u n - U (n * τ))
    have hc : ((n + 1 : ℕ) : ℝ) = n + 1 := by push_cast; ring
    refine (show _ ≤ (n : ℝ) * τ * (τ / 2 * M) + τ / 2 * M * τ by linarith).trans_eq ?_
    rw [hc]; ring

end SAT

end LeanDLRA.OpenProblems.Stiff
