import LeanDLRA.Literature.HighOrder.P2608_12893a

/-!
# Desingularized substeps for arXiv 2608.12893 (Strang projector splitting)

Continuation of `LeanDLRA.Literature.P2608_12893` (module `P2608_12893a`), on the family
`F_{j,η}(t, X) = M_η(X) + R_j(t)`, `M_η(X) = q_η(X) (Ω X - X Ω)`.

## Main results

* `Rot s = e^{sΩ}` (rotation in the `(e₁, e₃)` plane) and `Rot2 x = e^{x J}` with
  `J = [[0, 1], [-1, 0]]`: derivatives, orthogonality, `‖Rot s - 1‖ ≤ √2 |s|`.
* The interaction picture of the factor equations (arXiv 2608.12893, Lemma A.1, (A.38)–(A.39),
  now with the forcing): if `K' = c (Ω K - K B) + f` with `B = β J` and `σ' = c`, then
  `Rot(-σ) K Rot2(β σ)` has derivative `Rot(-σ) f Rot2(β σ)` (`hasDerivWithinAt_conjK`); the
  same for the S equation (`hasDerivWithinAt_conjS`).
* For the exact K, L and S substeps of `F_{j,η}` (the core `MatrixKSL.kField`, `lField`, `sField`)
  on `[t₀, t₁]`: the `M_η` part is exactly a rotation by the angle `σ = ∫ q_η` (`|σ| ≤ 2 (t - t₀)`),
  and up to this rotation the substep is the substep of the forcing alone (`M_η` omitted, the
  `h⁰` equations of Appendix A.2, solved in `leading_cycle`), with error
  `≤ 6 ε_j (t₁ - t₀)(t - t₀)` (`kStep_rot`, `lStep_rot`, `sStep_rot`). On a substep of length
  `O(h_j)` this is `O(h_j⁴)`, relative order `h_j` against the retained singular value `h_j³`:
  the mechanism behind the desingularized coordinates of Appendix A.1 and the remark before
  (A.54) that every `q_η` comes with a factor `h`.
* The same for the full equation (`hasDerivWithinAt_conjFull`, `flow_rot`): on `[0, T]`,
  `T ≤ 4 j h_j`, the solution from `Y⁰_j` is `e^{σΩ} (E₁₁ + h_j³ W(t/h_j)) e^{-σΩ}` up to
  `6 ε_j T t` (`flow_periodic`), cf. (4.24) and (A.52).

## Not proved

Lemma 4.1 (the projector expansions (4.3)), Lemma 4.2, Prop. 5.1, Lemmas A.2–A.3 and hence an
unconditional Thm 3.1 lower bound (3.20). With the results here, Lemma 4.1 at order `h_j⁰` would
follow from `leading_cycle` and a perturbation bound for the column and row spaces of rank-two
`3 × 2` factors with second singular value of order `h_j³`; Lemma 4.2 needs in addition the
second-order expansion of the rotation angles `σ_{i,η}` (their `η`-dependence enters at order
`h_j²`) and the explicit sum (4.20)–(4.22); Prop. 5.1 needs these uniformly in the block start
and the first-exit argument (5.18)–(5.24). None of this is formalized.

## Core definitions

`ODESolution`, `MatrixKSL.kField`, `sField`, `lField`, `rightProj`, `IsOrthProj`, the Frobenius
norm (`LeanDLRA.Frobenius`); from `P2608_12893a`: `Om`, `qη`, `Mη`, `Rj`, `Fj`, `εj`,
`norm_Rj_le`. `Rot`, `Rot2`, `J2` are the explicit exponentials `e^{sΩ}`, `e^{xJ}`.
-/

open Set Filter Topology
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2608_12893

open LeanDLRA

local notation "M₃" => Matrix (Fin 3) (Fin 3) ℝ
local notation "M₃₂" => Matrix (Fin 3) (Fin 2) ℝ
local notation "M₂" => Matrix (Fin 2) (Fin 2) ℝ

/-! ### The rotations `e^{sΩ}` and `e^{xJ}` -/

/-- `J = [[0, 1], [-1, 0]]`; every skew `2 × 2` matrix is a multiple of it. -/
def J2 : M₂ := !![0, 1; -1, 0]

/-- `e^{sΩ}`, `Ω = E₃₁ - E₁₃`: the rotation by `s` in the `(e₁, e₃)` plane. -/
noncomputable def Rot (s : ℝ) : M₃ :=
  !![Real.cos s, 0, -Real.sin s; 0, 1, 0; Real.sin s, 0, Real.cos s]

/-- `e^{xJ}`. -/
noncomputable def Rot2 (x : ℝ) : M₂ := !![Real.cos x, Real.sin x; -Real.sin x, Real.cos x]

/-- `diag(1, 0, 1)`. -/
private def D13 : M₃ := !![1, 0, 0; 0, 0, 0; 0, 0, 1]

private theorem Rot_eq (s : ℝ) :
    Rot s = Real.cos s • D13 + Real.sin s • Om + !![0, 0, 0; 0, 1, 0; 0, 0, 0] := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [Rot, D13, Om]

private theorem Rot2_eq (x : ℝ) : Rot2 x = Real.cos x • (1 : M₂) + Real.sin x • J2 := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [Rot2, J2]

theorem Om_mul_Rot (s : ℝ) : Om * Rot s = Rot s * Om := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [Rot, Om, Matrix.mul_apply, Fin.sum_univ_three]

theorem J2_mul_Rot2 (x : ℝ) : J2 * Rot2 x = Rot2 x * J2 := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [Rot2, J2, Matrix.mul_apply, Fin.sum_univ_two]

/-- `(e^{sΩ})' = Ω e^{sΩ}`. -/
theorem hasDerivAt_Rot (s : ℝ) : HasDerivAt Rot (Om * Rot s) s := by
  have h := ((Real.hasDerivAt_cos s).smul_const D13).add ((Real.hasDerivAt_sin s).smul_const Om)
  have h' := (h.add_const (!![0, 0, 0; 0, 1, 0; 0, 0, 0] : M₃)).congr_of_eventuallyEq
    (Eventually.of_forall fun s => Rot_eq s)
  refine h'.congr_deriv ?_
  ext i k
  fin_cases i <;> fin_cases k <;> simp [Rot, D13, Om, Matrix.mul_apply, Fin.sum_univ_three]

/-- `(e^{xJ})' = J e^{xJ}`. -/
theorem hasDerivAt_Rot2 (x : ℝ) : HasDerivAt Rot2 (J2 * Rot2 x) x := by
  have h := ((Real.hasDerivAt_cos x).smul_const (1 : M₂)).add
    ((Real.hasDerivAt_sin x).smul_const J2)
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun x => Rot2_eq x)).congr_deriv ?_
  ext i k
  fin_cases i <;> fin_cases k <;> simp [Rot2, J2, Matrix.mul_apply, Fin.sum_univ_two]

theorem continuous_Rot : Continuous Rot :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_Rot s).continuousAt

theorem continuous_Rot2 : Continuous Rot2 :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_Rot2 x).continuousAt

theorem Rot_zero : Rot 0 = 1 := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [Rot]

theorem Rot2_zero : Rot2 0 = 1 := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [Rot2]

theorem Rot2_orth (x : ℝ) : (Rot2 x)ᵀ * Rot2 x = 1 := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [Rot2, Matrix.mul_apply, Fin.sum_univ_two, ← sq, Real.cos_sq_add_sin_sq,
      Real.sin_sq_add_cos_sq] <;> ring

theorem Rot_orth (s : ℝ) : (Rot s)ᵀ * Rot s = 1 := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [Rot, Matrix.mul_apply, Fin.sum_univ_three, ← sq, Real.cos_sq_add_sin_sq,
      Real.sin_sq_add_cos_sq] <;> ring

theorem Rot2_transpose (x : ℝ) : (Rot2 x)ᵀ = Rot2 (-x) := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [Rot2]

private theorem one_sub_cos_le (x : ℝ) : 1 - Real.cos x ≤ x ^ 2 / 2 := by
  linarith [Real.one_sub_sq_div_two_le_cos (x := x)]

/-- `‖e^{sΩ} - 1‖ ≤ √2 |s|`. -/
theorem norm_Rot_sub_one (s : ℝ) : ‖Rot s - 1‖ ≤ √2 * |s| := by
  have h : ‖Rot s - 1‖ ^ 2 = 4 * (1 - Real.cos s) := by
    rw [Frobenius.norm_sq_eq_sum]
    simp [Rot, Fin.sum_univ_three, Matrix.one_apply]
    nlinarith [Real.sin_sq_add_cos_sq s]
  have h2 : ‖Rot s - 1‖ ^ 2 ≤ (√2 * |s|) ^ 2 := by
    rw [h, mul_pow, Real.sq_sqrt (by norm_num), sq_abs]
    nlinarith [one_sub_cos_le s]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

/-- `‖e^{xJ} - 1‖ ≤ √2 |x|`. -/
theorem norm_Rot2_sub_one (x : ℝ) : ‖Rot2 x - 1‖ ≤ √2 * |x| := by
  have h : ‖Rot2 x - 1‖ ^ 2 = 4 * (1 - Real.cos x) := by
    rw [Frobenius.norm_sq_eq_sum]
    simp [Rot2, Fin.sum_univ_two, Matrix.one_apply]
    nlinarith [Real.sin_sq_add_cos_sq x]
  have h2 : ‖Rot2 x - 1‖ ^ 2 ≤ (√2 * |x|) ^ 2 := by
    rw [h, mul_pow, Real.sq_sqrt (by norm_num), sq_abs]
    nlinarith [one_sub_cos_le x]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

private theorem norm_mul_Rot2 {m : Type*} [Fintype m] (X : Matrix m (Fin 2) ℝ) (x : ℝ) :
    ‖X * Rot2 x‖ = ‖X‖ := by
  have h := Frobenius.norm_mul_transpose_of_orthonormal (Rot2_orth (-x)) X
  rwa [Rot2_transpose, neg_neg] at h

private theorem norm_Rot2_mul {n : Type*} [Fintype n] (X : Matrix (Fin 2) n ℝ) (x : ℝ) :
    ‖Rot2 x * X‖ = ‖X‖ :=
  Frobenius.norm_mul_of_orthonormal (Rot2_orth x) X

/-- A skew `2 × 2` matrix is `B₀₁ J`. -/
theorem skew_eq_smul_J2 {B : M₂} (hB : Bᵀ = -B) : B = B 0 1 • J2 := by
  have e : ∀ i k, B k i = -B i k := fun i k => by
    have := congrFun (congrFun hB i) k
    simpa using this
  have h00 : B 0 0 = 0 := by linarith [e 0 0]
  have h11 : B 1 1 = 0 := by linarith [e 1 1]
  have h10 : B 1 0 = -B 0 1 := e 0 1
  ext i k
  fin_cases i <;> fin_cases k <;> simp [J2, h00, h11, h10]

/-- `Vᵀ Ω V` is skew. -/
theorem skew_VOmV (V : M₃₂) : (Vᵀ * Om * V)ᵀ = -(Vᵀ * Om * V) := by
  have hO : Omᵀ = -Om := by
    ext i k
    fin_cases i <;> fin_cases k <;> simp [Om]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hO]
  simp [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

/-- For `V` with orthonormal columns, `|(Vᵀ Ω V)₀₁| ≤ 1`. -/
theorem abs_VOmV_le {V : M₃₂} (hV : Vᵀ * V = 1) : |(Vᵀ * Om * V) 0 1| ≤ 1 := by
  have h0 : V 0 0 ^ 2 + V 1 0 ^ 2 + V 2 0 ^ 2 = 1 := by
    have := congrFun (congrFun hV 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_three, ← sq] using this
  have h1 : V 0 1 ^ 2 + V 1 1 ^ 2 + V 2 1 ^ 2 = 1 := by
    have := congrFun (congrFun hV 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_three, ← sq] using this
  have e : (Vᵀ * Om * V) 0 1 = V 2 0 * V 0 1 - V 0 0 * V 2 1 := by
    simp [Om, Matrix.mul_apply, Fin.sum_univ_three]
    ring
  rw [e, abs_le]
  constructor <;> nlinarith [sq_nonneg (V 0 0 * V 0 1 + V 2 0 * V 2 1), sq_nonneg (V 1 0),
    sq_nonneg (V 1 1), sq_nonneg (V 2 0 * V 0 1 - V 0 0 * V 2 1 - 1),
    sq_nonneg (V 2 0 * V 0 1 - V 0 0 * V 2 1 + 1)]

/-! ### The interaction picture -/

/-- **Interaction picture of the K and L equations** (arXiv 2608.12893, (A.38) with a forcing).
If `K' = c (Ω K - K (β J)) + f` and `σ' = c`, then `Rot(-σ) K Rot2(β σ)` has derivative
`Rot(-σ) f Rot2(β σ)`: the `c`-part is exactly the rotation. -/
theorem hasDerivWithinAt_conjK {Y f : ℝ → M₃₂} {c σ : ℝ → ℝ} {β : ℝ} {s : Set ℝ} {t : ℝ}
    (hY : HasDerivWithinAt Y (c t • (Om * Y t - Y t * (β • J2)) + f t) s t)
    (hσ : HasDerivWithinAt σ (c t) s t) :
    HasDerivWithinAt (fun t => Rot (-σ t) * Y t * Rot2 (β * σ t))
      (Rot (-σ t) * f t * Rot2 (β * σ t)) s t := by
  have h1 := (hasDerivAt_Rot (-σ t)).scomp_hasDerivWithinAt t hσ.neg
  have h2 := (hasDerivAt_Rot2 (β * σ t)).scomp_hasDerivWithinAt t (hσ.const_mul β)
  refine (Frobenius.hasDerivWithinAt_mul_mul h1 hY h2).congr_deriv ?_
  rw [Om_mul_Rot]
  simp only [Function.comp_apply, Pi.neg_apply, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  module

/-- **Interaction picture of the S equation** (arXiv 2608.12893, (A.39) with a forcing). If
`S' = c (S (β J) - (α J) S) + g` and `σ' = c`, then `Rot2(α σ) S Rot2(-β σ)` has derivative
`Rot2(α σ) g Rot2(-β σ)`. -/
theorem hasDerivWithinAt_conjS {S g : ℝ → M₂} {c σ : ℝ → ℝ} {α β : ℝ} {s : Set ℝ} {t : ℝ}
    (hS : HasDerivWithinAt S (c t • (S t * (β • J2) - (α • J2) * S t) + g t) s t)
    (hσ : HasDerivWithinAt σ (c t) s t) :
    HasDerivWithinAt (fun t => Rot2 (α * σ t) * S t * Rot2 (-(β * σ t)))
      (Rot2 (α * σ t) * g t * Rot2 (-(β * σ t))) s t := by
  have h1 := (hasDerivAt_Rot2 (α * σ t)).scomp_hasDerivWithinAt t (hσ.const_mul α)
  have h2 := (hasDerivAt_Rot2 (-(β * σ t))).scomp_hasDerivWithinAt t (hσ.const_mul β).neg
  refine (Frobenius.hasDerivWithinAt_mul_mul h1 hS h2).congr_deriv ?_
  rw [J2_mul_Rot2 (α * σ t)]
  simp only [Function.comp_apply, Pi.neg_apply, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  module

/-! ### The rotation angle `σ = ∫ q_η` -/

private theorem continuous_qη (η : ℝ) : Continuous (qη η) := by
  have he : Continuous fun X : M₃ => X 2 0 := by
    have e : (fun X : M₃ => X 2 0) = fun X => ⟪E31, X⟫ := by
      funext X
      rw [Frobenius.inner_def]
      simp [E31, Fin.sum_univ_three]
    rw [e]
    exact continuous_const.inner continuous_id
  have ht : Continuous Real.tanh := by
    have e : Real.tanh = fun x => Real.sinh x / Real.cosh x :=
      funext fun x => Real.tanh_eq_sinh_div_cosh x
    rw [e]
    exact Real.continuous_sinh.div Real.continuous_cosh fun x => (Real.cosh_pos x).ne'
  change Continuous fun X : M₃ => (1 + η * Real.tanh (X 2 0)) / √(1 + ‖X‖ ^ 2)
  exact (continuous_const.add (continuous_const.mul (ht.comp he))).div
    (continuous_const.add (continuous_norm.pow 2)).sqrt
    fun X => (Real.sqrt_pos.2 (by positivity)).ne'

private theorem abs_qη_le {η : ℝ} (hη : |η| ≤ 1) (X : M₃) : |qη η X| ≤ 2 := by
  have ht := Real.abs_tanh_lt_one (X 2 0)
  have hs : 1 ≤ √(1 + ‖X‖ ^ 2) := by
    rw [Real.one_le_sqrt]
    nlinarith [sq_nonneg ‖X‖]
  have hn : |1 + η * Real.tanh (X 2 0)| ≤ 2 := by
    calc |1 + η * Real.tanh (X 2 0)| ≤ |1| + |η| * |Real.tanh (X 2 0)| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ 2 := by rw [abs_one]; nlinarith [abs_nonneg η, abs_nonneg (Real.tanh (X 2 0))]
  rw [qη, abs_div, abs_of_pos (by linarith : (0 : ℝ) < √(1 + ‖X‖ ^ 2)),
    div_le_iff₀ (by linarith)]
  nlinarith [abs_nonneg (1 + η * Real.tanh (X 2 0))]

/-- A rotation angle: for `c` continuous on `[t₀, t₁]` with `|c| ≤ 2` there is `σ` with
`σ t₀ = 0`, right derivative `c` on `[t₀, t₁)` and `|σ t| ≤ 2 (t - t₀)`. -/
private theorem exists_angle {c : ℝ → ℝ} {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁)
    (hc : ContinuousOn c (Icc t₀ t₁)) (hb : ∀ t ∈ Icc t₀ t₁, |c t| ≤ 2) :
    ∃ σ : ℝ → ℝ, σ t₀ = 0 ∧ ContinuousOn σ (Icc t₀ t₁) ∧
      (∀ t ∈ Ico t₀ t₁, HasDerivWithinAt σ (c t) (Ici t) t) ∧
      ∀ t ∈ Icc t₀ t₁, |σ t| ≤ 2 * (t - t₀) := by
  set c' : ℝ → ℝ := fun t => c (projIcc t₀ t₁ h01 t)
  have hc' : Continuous c' :=
    hc.comp_continuous (continuous_subtype_val.comp continuous_projIcc) fun t =>
      (projIcc t₀ t₁ h01 t).2
  have hb' : ∀ x, ‖c' x‖ ≤ 2 := fun x => hb _ (projIcc t₀ t₁ h01 x).2
  have hd : ∀ t, HasDerivAt (fun u => ∫ x in t₀..u, c' x) (c' t) t := fun t =>
    (hc'.integral_hasStrictDerivAt t₀ t).hasDerivAt
  refine ⟨fun u => ∫ x in t₀..u, c' x, by simp,
    (continuous_iff_continuousAt.2 fun t => (hd t).continuousAt).continuousOn,
    fun t ht => ?_, fun t ht => ?_⟩
  · have e : c' t = c t := by
      simp [c', projIcc_of_mem h01 (Ico_subset_Icc_self ht)]
    rw [← e]
    exact (hd t).hasDerivWithinAt
  · have := intervalIntegral.norm_integral_le_of_norm_le_const (a := t₀) (b := t)
      (fun x _ => hb' x)
    rwa [abs_of_nonneg (by linarith [ht.1] : 0 ≤ t - t₀)] at this

private theorem continuousOn_mul' {m l n : Type*} [Fintype m] [Fintype l] [Fintype n]
    {A : ℝ → Matrix m l ℝ} {B : ℝ → Matrix l n ℝ} {s : Set ℝ} (hA : ContinuousOn A s)
    (hB : ContinuousOn B s) : ContinuousOn (fun t => A t * B t) s :=
  ((Frobenius.mulCLM (m := m) (l := l) (n := n)).continuous.comp_continuousOn hA).clm_apply hB

/-! ### Comparison with the forcing alone -/

/-- The K/L equation, up to the rotations, is its forcing part, with error
`≤ 6 ε (t₁ - t₀)(t - t₀)`. -/
private theorem conjK_bound {Y YR f : ℝ → M₃₂} {c σ : ℝ → ℝ} {β ε : ℝ} {t₀ t₁ : ℝ}
    (hYc : ContinuousOn Y (Icc t₀ t₁))
    (hY : ∀ t ∈ Ico t₀ t₁,
      HasDerivWithinAt Y (c t • (Om * Y t - Y t * (β • J2)) + f t) (Ici t) t)
    (hσc : ContinuousOn σ (Icc t₀ t₁)) (hσ : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt σ (c t) (Ici t) t)
    (hσ0 : σ t₀ = 0) (hσb : ∀ t ∈ Icc t₀ t₁, |σ t| ≤ 2 * (t - t₀))
    (hYRc : ContinuousOn YR (Icc t₀ t₁))
    (hYR : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt YR (f t) (Ici t) t) (h0 : YR t₀ = Y t₀)
    (hβ : |β| ≤ 1) (hf : ∀ t ∈ Ico t₀ t₁, ‖f t‖ ≤ ε) :
    ∀ t ∈ Icc t₀ t₁, ‖Rot (-σ t) * Y t * Rot2 (β * σ t) - YR t‖ ≤
      6 * ε * (t₁ - t₀) * (t - t₀) := by
  set D : ℝ → M₃₂ := fun t => Rot (-σ t) * Y t * Rot2 (β * σ t) - YR t with hD
  have hDc : ContinuousOn D (Icc t₀ t₁) :=
    (continuousOn_mul' (continuousOn_mul' (continuous_Rot.comp_continuousOn hσc.neg) hYc)
      (continuous_Rot2.comp_continuousOn (continuousOn_const.mul hσc))).sub hYRc
  have hDd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt D
      (Rot (-σ t) * f t * Rot2 (β * σ t) - f t) (Ici t) t := fun t ht =>
    (hasDerivWithinAt_conjK (hY t ht) (hσ t ht)).sub (hYR t ht)
  have hD0 : D t₀ = 0 := by
    simp [hD, hσ0, Rot_zero, Rot2_zero, h0]
  have hbound : ∀ t ∈ Ico t₀ t₁, ‖Rot (-σ t) * f t * Rot2 (β * σ t) - f t‖ ≤
      6 * ε * (t₁ - t₀) := by
    intro t ht
    have hs := hσb t (Ico_subset_Icc_self ht)
    have hsT : |σ t| ≤ 2 * (t₁ - t₀) := hs.trans (by linarith [ht.2])
    have e : Rot (-σ t) * f t * Rot2 (β * σ t) - f t =
        (Rot (-σ t) - 1) * (f t * Rot2 (β * σ t)) + f t * (Rot2 (β * σ t) - 1) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
        Matrix.mul_assoc]
      abel
    have n1 : ‖(Rot (-σ t) - 1) * (f t * Rot2 (β * σ t))‖ ≤ √2 * |σ t| * ‖f t‖ := by
      calc _ ≤ ‖Rot (-σ t) - 1‖ * ‖f t * Rot2 (β * σ t)‖ := Frobenius.norm_mul_le _ _
        _ ≤ √2 * |σ t| * ‖f t‖ := by
          rw [norm_mul_Rot2]
          have := norm_Rot_sub_one (-σ t)
          rw [abs_neg] at this
          exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    have n2 : ‖f t * (Rot2 (β * σ t) - 1)‖ ≤ ‖f t‖ * (√2 * |σ t|) := by
      calc _ ≤ ‖f t‖ * ‖Rot2 (β * σ t) - 1‖ := Frobenius.norm_mul_le _ _
        _ ≤ ‖f t‖ * (√2 * |σ t|) := by
          refine mul_le_mul_of_nonneg_left ((norm_Rot2_sub_one _).trans ?_) (norm_nonneg _)
          rw [abs_mul]
          have := abs_nonneg (σ t)
          have : |β| * |σ t| ≤ |σ t| := by nlinarith
          nlinarith [Real.sqrt_nonneg 2]
    have hf' := hf t ht
    have hs2 : √2 ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have hfn := norm_nonneg (f t)
    have hsn := abs_nonneg (σ t)
    rw [e]
    calc _ ≤ ‖(Rot (-σ t) - 1) * (f t * Rot2 (β * σ t))‖ + ‖f t * (Rot2 (β * σ t) - 1)‖ :=
          norm_add_le _ _
      _ ≤ 2 * √2 * |σ t| * ‖f t‖ := by nlinarith
      _ ≤ 2 * (3 / 2) * (2 * (t₁ - t₀)) * ε := by
          have h3 : |σ t| * ‖f t‖ ≤ 2 * (t₁ - t₀) * ε := mul_le_mul hsT hf' hfn
            (by linarith [ht.1, ht.2])
          nlinarith [Real.sqrt_nonneg 2, mul_nonneg hsn hfn]
      _ ≤ 6 * ε * (t₁ - t₀) := by nlinarith [mul_nonneg hsn hfn]
  intro t ht
  have := norm_image_sub_le_of_norm_deriv_right_le_segment hDc hDd hbound t ht
  rwa [hD0, sub_zero] at this

/-- The S equation, up to the rotations, is its forcing part, with error
`≤ 6 ε (t₁ - t₀)(t - t₀)`. -/
private theorem conjS_bound {S SR g : ℝ → M₂} {c σ : ℝ → ℝ} {α β ε : ℝ} {t₀ t₁ : ℝ}
    (hSc : ContinuousOn S (Icc t₀ t₁))
    (hS : ∀ t ∈ Ico t₀ t₁,
      HasDerivWithinAt S (c t • (S t * (β • J2) - (α • J2) * S t) + g t) (Ici t) t)
    (hσc : ContinuousOn σ (Icc t₀ t₁)) (hσ : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt σ (c t) (Ici t) t)
    (hσ0 : σ t₀ = 0) (hσb : ∀ t ∈ Icc t₀ t₁, |σ t| ≤ 2 * (t - t₀))
    (hSRc : ContinuousOn SR (Icc t₀ t₁))
    (hSR : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt SR (g t) (Ici t) t) (h0 : SR t₀ = S t₀)
    (hα : |α| ≤ 1) (hβ : |β| ≤ 1) (hg : ∀ t ∈ Ico t₀ t₁, ‖g t‖ ≤ ε) :
    ∀ t ∈ Icc t₀ t₁, ‖Rot2 (α * σ t) * S t * Rot2 (-(β * σ t)) - SR t‖ ≤
      6 * ε * (t₁ - t₀) * (t - t₀) := by
  set D : ℝ → M₂ := fun t => Rot2 (α * σ t) * S t * Rot2 (-(β * σ t)) - SR t with hD
  have hDc : ContinuousOn D (Icc t₀ t₁) :=
    (continuousOn_mul' (continuousOn_mul'
      (continuous_Rot2.comp_continuousOn (continuousOn_const.mul hσc)) hSc)
      (continuous_Rot2.comp_continuousOn (continuousOn_const.mul hσc).neg)).sub hSRc
  have hDd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt D
      (Rot2 (α * σ t) * g t * Rot2 (-(β * σ t)) - g t) (Ici t) t := fun t ht =>
    (hasDerivWithinAt_conjS (hS t ht) (hσ t ht)).sub (hSR t ht)
  have hD0 : D t₀ = 0 := by
    simp [hD, hσ0, Rot2_zero, h0]
  have hbound : ∀ t ∈ Ico t₀ t₁, ‖Rot2 (α * σ t) * g t * Rot2 (-(β * σ t)) - g t‖ ≤
      6 * ε * (t₁ - t₀) := by
    intro t ht
    have hs := hσb t (Ico_subset_Icc_self ht)
    have hsT : |σ t| ≤ 2 * (t₁ - t₀) := hs.trans (by linarith [ht.2])
    have e : Rot2 (α * σ t) * g t * Rot2 (-(β * σ t)) - g t =
        (Rot2 (α * σ t) - 1) * (g t * Rot2 (-(β * σ t))) + g t * (Rot2 (-(β * σ t)) - 1) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
        Matrix.mul_assoc]
      abel
    have hsn := abs_nonneg (σ t)
    have n1 : ‖(Rot2 (α * σ t) - 1) * (g t * Rot2 (-(β * σ t)))‖ ≤ √2 * |σ t| * ‖g t‖ := by
      calc _ ≤ ‖Rot2 (α * σ t) - 1‖ * ‖g t * Rot2 (-(β * σ t))‖ := Frobenius.norm_mul_le _ _
        _ ≤ √2 * |σ t| * ‖g t‖ := by
          rw [norm_mul_Rot2]
          refine mul_le_mul_of_nonneg_right ((norm_Rot2_sub_one _).trans ?_) (norm_nonneg _)
          rw [abs_mul]
          have : |α| * |σ t| ≤ |σ t| := by nlinarith
          nlinarith [Real.sqrt_nonneg 2]
    have n2 : ‖g t * (Rot2 (-(β * σ t)) - 1)‖ ≤ ‖g t‖ * (√2 * |σ t|) := by
      calc _ ≤ ‖g t‖ * ‖Rot2 (-(β * σ t)) - 1‖ := Frobenius.norm_mul_le _ _
        _ ≤ ‖g t‖ * (√2 * |σ t|) := by
          refine mul_le_mul_of_nonneg_left ((norm_Rot2_sub_one _).trans ?_) (norm_nonneg _)
          rw [abs_neg, abs_mul]
          have : |β| * |σ t| ≤ |σ t| := by nlinarith
          nlinarith [Real.sqrt_nonneg 2]
    have hg' := hg t ht
    have hs2 : √2 ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have hgn := norm_nonneg (g t)
    rw [e]
    calc _ ≤ ‖(Rot2 (α * σ t) - 1) * (g t * Rot2 (-(β * σ t)))‖ +
          ‖g t * (Rot2 (-(β * σ t)) - 1)‖ := norm_add_le _ _
      _ ≤ 2 * √2 * |σ t| * ‖g t‖ := by nlinarith
      _ ≤ 2 * (3 / 2) * (2 * (t₁ - t₀)) * ε := by
          have h3 : |σ t| * ‖g t‖ ≤ 2 * (t₁ - t₀) * ε := mul_le_mul hsT hg' hgn
            (by linarith [ht.1, ht.2])
          nlinarith [Real.sqrt_nonneg 2, mul_nonneg hsn hgn]
      _ ≤ 6 * ε * (t₁ - t₀) := by nlinarith [mul_nonneg hsn hgn]
  intro t ht
  have := norm_image_sub_le_of_norm_deriv_right_le_segment hDc hDd hbound t ht
  rwa [hD0, sub_zero] at this

/-! ### The substeps of `F_{j,η}` -/

private theorem norm_mul_le_of_orth {m : Type*} [Fintype m] {V : M₃₂} (hV : Vᵀ * V = 1)
    (R : Matrix m (Fin 3) ℝ) : ‖R * V‖ ≤ ‖R‖ := by
  have h := Frobenius.norm_mul_transpose_of_orthonormal hV (R * V)
  rw [← h, Matrix.mul_assoc, ← rightProj_apply']
  exact (isOrthProj_rightProj hV).norm_le R

private theorem kField_Fj {j : ℕ} {η : ℝ} {V : M₃₂} (hV : Vᵀ * V = 1) (t : ℝ) (K : M₃₂) :
    MatrixKSL.kField V (Fj j η) t K =
      qη η (K * Vᵀ) • (Om * K - K * ((Vᵀ * Om * V) 0 1 • J2)) + Rj j t * V := by
  rw [← skew_eq_smul_J2 (skew_VOmV V)]
  simp only [MatrixKSL.kField, Fj, Mη, comm, Matrix.add_mul, Matrix.smul_mul, Matrix.sub_mul,
    Matrix.mul_assoc, hV, Matrix.mul_one]

private theorem lField_Fj {j : ℕ} {η : ℝ} {U : M₃₂} (hU : Uᵀ * U = 1) (t : ℝ) (L : M₃₂) :
    MatrixKSL.lField U (Fj j η) t L =
      qη η (U * Lᵀ) • (Om * L - L * ((Uᵀ * Om * U) 0 1 • J2)) + (Rj j t)ᵀ * U := by
  have hO : Omᵀ = -Om := by
    ext i k
    fin_cases i <;> fin_cases k <;> simp [Om]
  rw [← skew_eq_smul_J2 (skew_VOmV U)]
  simp only [MatrixKSL.lField, Fj, Mη, comm, Matrix.transpose_add, Matrix.transpose_smul,
    Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose, hO, Matrix.add_mul,
    Matrix.smul_mul, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, hU,
    Matrix.mul_one]
  module

private theorem sField_Fj {j : ℕ} {η : ℝ} {U V : M₃₂} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (t : ℝ) (S : M₂) : MatrixKSL.sField U V (Fj j η) t S =
      qη η (U * S * Vᵀ) • (S * ((Vᵀ * Om * V) 0 1 • J2) - ((Uᵀ * Om * U) 0 1 • J2) * S) +
        -(Uᵀ * Rj j t * V) := by
  rw [← skew_eq_smul_J2 (skew_VOmV U), ← skew_eq_smul_J2 (skew_VOmV V)]
  simp only [MatrixKSL.sField, Fj, Mη, comm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hV, Matrix.mul_one]
  simp only [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul]
  module

/-- **K substep of `F_{j,η}`: rotation and forcing** (arXiv 2608.12893, Appendix A; Lemma A.1
with the forcing). Let `K` be an exact K substep `K' = F_{j,η}(t, K Vᵀ) V` on `[t₀, t₁]`
(`MatrixKSL.kField V (Fj j η)`, `V` column-orthonormal, `|η| ≤ 1`) and `K_R` the K substep of the
forcing alone, `K_R' = R_j(t) V`, from the same start. Then there is a rotation angle `σ`
(`σ t₀ = 0`, `σ' = q_η(K Vᵀ)`, `|σ t| ≤ 2 (t - t₀)`) such that
`‖e^{-σΩ} K(t) e^{β σ J} - K_R(t)‖ ≤ 6 ε_j (t₁ - t₀)(t - t₀)`, `β = (Vᵀ Ω V)₀₁`. -/
theorem kStep_rot {j : ℕ} {η : ℝ} (hη : |η| ≤ 1) {V : M₃₂} (hV : Vᵀ * V = 1)
    {K KR : ℝ → M₃₂} {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁)
    (hK : ODESolution (MatrixKSL.kField V (Fj j η)) K t₀ t₁)
    (hKR : ODESolution (MatrixKSL.kField V (fun t _ => Rj j t)) KR t₀ t₁) (h0 : KR t₀ = K t₀) :
    ∃ σ : ℝ → ℝ, σ t₀ = 0 ∧
      (∀ t ∈ Ico t₀ t₁, HasDerivWithinAt σ (qη η (K t * Vᵀ)) (Ici t) t) ∧
      ∀ t ∈ Icc t₀ t₁, |σ t| ≤ 2 * (t - t₀) ∧
        ‖Rot (-σ t) * K t * Rot2 ((Vᵀ * Om * V) 0 1 * σ t) - KR t‖ ≤
          6 * εj j * (t₁ - t₀) * (t - t₀) := by
  have hcc : ContinuousOn (fun t => qη η (K t * Vᵀ)) (Icc t₀ t₁) :=
    (continuous_qη η).comp_continuousOn (continuousOn_mul' hK.cont continuousOn_const)
  obtain ⟨σ, hσ0, hσc, hσd, hσb⟩ := exists_angle h01 hcc fun t _ => abs_qη_le hη _
  refine ⟨σ, hσ0, hσd, fun t ht => ⟨hσb t ht, ?_⟩⟩
  refine conjK_bound (c := fun t => qη η (K t * Vᵀ)) (f := fun t => Rj j t * V) hK.cont
    (fun t ht => ?_) hσc hσd hσ0 hσb hKR.cont (fun t ht => hKR.deriv t ht) h0
    (abs_VOmV_le hV) (fun t _ => (norm_mul_le_of_orth hV _).trans (norm_Rj_le j t)) t ht
  have := hK.deriv t ht
  rwa [kField_Fj hV] at this

/-- **L substep of `F_{j,η}`: rotation and forcing** (arXiv 2608.12893, Appendix A; Lemma A.1
with the forcing). As `kStep_rot` for the exact L substep `L' = F_{j,η}(t, U Lᵀ)ᵀ U`
(`MatrixKSL.lField U (Fj j η)`) and the L substep of the forcing alone, `L_R' = R_j(t)ᵀ U`, with
`β = (Uᵀ Ω U)₀₁`. -/
theorem lStep_rot {j : ℕ} {η : ℝ} (hη : |η| ≤ 1) {U : M₃₂} (hU : Uᵀ * U = 1)
    {L LR : ℝ → M₃₂} {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁)
    (hL : ODESolution (MatrixKSL.lField U (Fj j η)) L t₀ t₁)
    (hLR : ODESolution (MatrixKSL.lField U (fun t _ => Rj j t)) LR t₀ t₁) (h0 : LR t₀ = L t₀) :
    ∃ σ : ℝ → ℝ, σ t₀ = 0 ∧
      (∀ t ∈ Ico t₀ t₁, HasDerivWithinAt σ (qη η (U * (L t)ᵀ)) (Ici t) t) ∧
      ∀ t ∈ Icc t₀ t₁, |σ t| ≤ 2 * (t - t₀) ∧
        ‖Rot (-σ t) * L t * Rot2 ((Uᵀ * Om * U) 0 1 * σ t) - LR t‖ ≤
          6 * εj j * (t₁ - t₀) * (t - t₀) := by
  have hcc : ContinuousOn (fun t => qη η (U * (L t)ᵀ)) (Icc t₀ t₁) :=
    (continuous_qη η).comp_continuousOn (continuousOn_mul' continuousOn_const
      ((Frobenius.transposeCLM (m := Fin 3) (n := Fin 2)).continuous.comp_continuousOn hL.cont))
  obtain ⟨σ, hσ0, hσc, hσd, hσb⟩ := exists_angle h01 hcc fun t _ => abs_qη_le hη _
  refine ⟨σ, hσ0, hσd, fun t ht => ⟨hσb t ht, ?_⟩⟩
  refine conjK_bound (c := fun t => qη η (U * (L t)ᵀ)) (f := fun t => (Rj j t)ᵀ * U) hL.cont
    (fun t ht => ?_) hσc hσd hσ0 hσb hLR.cont (fun t ht => hLR.deriv t ht) h0
    (abs_VOmV_le hU) (fun t _ => ?_) t ht
  · have := hL.deriv t ht
    rwa [lField_Fj hU] at this
  · refine (norm_mul_le_of_orth hU _).trans ?_
    rw [Frobenius.norm_transpose]
    exact norm_Rj_le j t

/-- **S substep of `F_{j,η}`: rotation and forcing** (arXiv 2608.12893, Appendix A; Lemma A.1
with the forcing). Let `S` be an exact S substep `S' = -Uᵀ F_{j,η}(t, U S Vᵀ) V` on `[t₀, t₁]`
(`MatrixKSL.sField U V (Fj j η)`, `U, V` column-orthonormal) and `S_R` the S substep of the
forcing alone, `S_R' = -Uᵀ R_j(t) V`, from the same start. Then there is `σ` (`σ t₀ = 0`,
`σ' = q_η(U S Vᵀ)`, `|σ t| ≤ 2 (t - t₀)`) with
`‖e^{α σ J} S(t) e^{-β σ J} - S_R(t)‖ ≤ 6 ε_j (t₁ - t₀)(t - t₀)`, `α = (Uᵀ Ω U)₀₁`,
`β = (Vᵀ Ω V)₀₁`. -/
theorem sStep_rot {j : ℕ} {η : ℝ} (hη : |η| ≤ 1) {U V : M₃₂} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) {S SR : ℝ → M₂} {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁)
    (hS : ODESolution (MatrixKSL.sField U V (Fj j η)) S t₀ t₁)
    (hSR : ODESolution (MatrixKSL.sField U V (fun t _ => Rj j t)) SR t₀ t₁)
    (h0 : SR t₀ = S t₀) :
    ∃ σ : ℝ → ℝ, σ t₀ = 0 ∧
      (∀ t ∈ Ico t₀ t₁, HasDerivWithinAt σ (qη η (U * S t * Vᵀ)) (Ici t) t) ∧
      ∀ t ∈ Icc t₀ t₁, |σ t| ≤ 2 * (t - t₀) ∧
        ‖Rot2 ((Uᵀ * Om * U) 0 1 * σ t) * S t * Rot2 (-((Vᵀ * Om * V) 0 1 * σ t)) - SR t‖ ≤
          6 * εj j * (t₁ - t₀) * (t - t₀) := by
  have hcc : ContinuousOn (fun t => qη η (U * S t * Vᵀ)) (Icc t₀ t₁) :=
    (continuous_qη η).comp_continuousOn
      (continuousOn_mul' (continuousOn_mul' continuousOn_const hS.cont) continuousOn_const)
  obtain ⟨σ, hσ0, hσc, hσd, hσb⟩ := exists_angle h01 hcc fun t _ => abs_qη_le hη _
  refine ⟨σ, hσ0, hσd, fun t ht => ⟨hσb t ht, ?_⟩⟩
  refine conjS_bound (c := fun t => qη η (U * S t * Vᵀ)) (g := fun t => -(Uᵀ * Rj j t * V))
    hS.cont (fun t ht => ?_) hσc hσd hσ0 hσb hSR.cont (fun t ht => ?_) h0
    (abs_VOmV_le hU) (abs_VOmV_le hV) (fun t _ => ?_) t ht
  · have := hS.deriv t ht
    rwa [sField_Fj hU hV] at this
  · have := hSR.deriv t ht
    simpa [MatrixKSL.sField] using this
  · rw [norm_neg]
    calc ‖Uᵀ * Rj j t * V‖ ≤ ‖Uᵀ * Rj j t‖ := norm_mul_le_of_orth hV _
      _ = ‖(Rj j t)ᵀ * U‖ := by
          rw [← Frobenius.norm_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]
      _ ≤ ‖(Rj j t)ᵀ‖ := norm_mul_le_of_orth hU _
      _ ≤ εj j := by rw [Frobenius.norm_transpose]; exact norm_Rj_le j t

/-! ### The full flow -/

theorem Rot_transpose (s : ℝ) : (Rot s)ᵀ = Rot (-s) := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [Rot]

private theorem norm_mul_Rot (X : M₃) (s : ℝ) : ‖X * Rot s‖ = ‖X‖ := by
  have h := Frobenius.norm_mul_transpose_of_orthonormal (Rot_orth (-s)) X
  rwa [Rot_transpose, neg_neg] at h

/-- **Interaction picture of the full equation**: if `A' = c (Ω A - A Ω) + f` and `σ' = c`, then
`e^{-σΩ} A e^{σΩ}` has derivative `e^{-σΩ} f e^{σΩ}`. -/
theorem hasDerivWithinAt_conjFull {A f : ℝ → M₃} {c σ : ℝ → ℝ} {s : Set ℝ} {t : ℝ}
    (hA : HasDerivWithinAt A (c t • (Om * A t - A t * Om) + f t) s t)
    (hσ : HasDerivWithinAt σ (c t) s t) :
    HasDerivWithinAt (fun t => Rot (-σ t) * A t * Rot (σ t))
      (Rot (-σ t) * f t * Rot (σ t)) s t := by
  have h1 := (hasDerivAt_Rot (-σ t)).scomp_hasDerivWithinAt t hσ.neg
  have h2 := (hasDerivAt_Rot (σ t)).scomp_hasDerivWithinAt t hσ
  refine (Frobenius.hasDerivWithinAt_mul_mul h1 hA h2).congr_deriv ?_
  rw [Om_mul_Rot (-σ t)]
  simp only [Function.comp_apply, Pi.neg_apply, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  module

/-- **The full flow of `F_{j,η}`: rotation and forcing** (arXiv 2608.12893, (A.52), (4.24)–(4.27)).
Let `A` solve `A' = F_{j,η}(t, A)` on `[t₀, t₁]` (`|η| ≤ 1`) and `A_R` solve the equation of the
forcing alone, `A_R' = R_j(t)`, from the same start. Then there is `σ` (`σ t₀ = 0`,
`σ' = q_η(A)`, `|σ t| ≤ 2 (t - t₀)`) with
`‖e^{-σΩ} A(t) e^{σΩ} - A_R(t)‖ ≤ 6 ε_j (t₁ - t₀)(t - t₀)`. -/
theorem flow_rot {j : ℕ} {η : ℝ} (hη : |η| ≤ 1) {A AR : ℝ → M₃} {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁)
    (hA : ODESolution (Fj j η) A t₀ t₁) (hAR : ODESolution (fun t _ => Rj j t) AR t₀ t₁)
    (h0 : AR t₀ = A t₀) :
    ∃ σ : ℝ → ℝ, σ t₀ = 0 ∧ (∀ t ∈ Ico t₀ t₁, HasDerivWithinAt σ (qη η (A t)) (Ici t) t) ∧
      ∀ t ∈ Icc t₀ t₁, |σ t| ≤ 2 * (t - t₀) ∧
        ‖Rot (-σ t) * A t * Rot (σ t) - AR t‖ ≤ 6 * εj j * (t₁ - t₀) * (t - t₀) := by
  obtain ⟨σ, hσ0, hσc, hσd, hσb⟩ := exists_angle h01
    ((continuous_qη η).comp_continuousOn hA.cont) fun t _ => abs_qη_le hη _
  refine ⟨σ, hσ0, hσd, fun t ht => ⟨hσb t ht, ?_⟩⟩
  set D : ℝ → M₃ := fun t => Rot (-σ t) * A t * Rot (σ t) - AR t with hD
  have hDc : ContinuousOn D (Icc t₀ t₁) :=
    (continuousOn_mul' (continuousOn_mul' (continuous_Rot.comp_continuousOn hσc.neg) hA.cont)
      (continuous_Rot.comp_continuousOn hσc)).sub hAR.cont
  have hDd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt D
      (Rot (-σ t) * Rj j t * Rot (σ t) - Rj j t) (Ici t) t := fun t ht =>
    (hasDerivWithinAt_conjFull (c := fun t => qη η (A t)) (hA.deriv t ht) (hσd t ht)).sub
      (hAR.deriv t ht)
  have hD0 : D t₀ = 0 := by
    simp [hD, hσ0, Rot_zero, h0]
  have hbound : ∀ t ∈ Ico t₀ t₁, ‖Rot (-σ t) * Rj j t * Rot (σ t) - Rj j t‖ ≤
      6 * εj j * (t₁ - t₀) := by
    intro t ht
    have hsT : |σ t| ≤ 2 * (t₁ - t₀) := (hσb t (Ico_subset_Icc_self ht)).trans
      (by linarith [ht.2])
    have e : Rot (-σ t) * Rj j t * Rot (σ t) - Rj j t =
        (Rot (-σ t) - 1) * (Rj j t * Rot (σ t)) + Rj j t * (Rot (σ t) - 1) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
        Matrix.mul_assoc]
      abel
    have hR := norm_Rj_le j t
    have hRn := norm_nonneg (Rj j t)
    have hsn := abs_nonneg (σ t)
    have n1 : ‖(Rot (-σ t) - 1) * (Rj j t * Rot (σ t))‖ ≤ √2 * |σ t| * ‖Rj j t‖ := by
      calc _ ≤ ‖Rot (-σ t) - 1‖ * ‖Rj j t * Rot (σ t)‖ := Frobenius.norm_mul_le _ _
        _ ≤ √2 * |σ t| * ‖Rj j t‖ := by
          rw [norm_mul_Rot]
          have := norm_Rot_sub_one (-σ t)
          rw [abs_neg] at this
          exact mul_le_mul_of_nonneg_right this hRn
    have n2 : ‖Rj j t * (Rot (σ t) - 1)‖ ≤ ‖Rj j t‖ * (√2 * |σ t|) :=
      (Frobenius.norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_Rot_sub_one _) hRn)
    have hs2 : √2 ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    rw [e]
    calc _ ≤ ‖(Rot (-σ t) - 1) * (Rj j t * Rot (σ t))‖ + ‖Rj j t * (Rot (σ t) - 1)‖ :=
          norm_add_le _ _
      _ ≤ 2 * √2 * |σ t| * ‖Rj j t‖ := by nlinarith
      _ ≤ 2 * (3 / 2) * (2 * (t₁ - t₀)) * εj j := by
          have h3 : |σ t| * ‖Rj j t‖ ≤ 2 * (t₁ - t₀) * εj j := mul_le_mul hsT hR hRn
            (by linarith [ht.1, ht.2])
          nlinarith [Real.sqrt_nonneg 2, mul_nonneg hsn hRn]
      _ ≤ 6 * εj j * (t₁ - t₀) := by nlinarith [mul_nonneg hsn hRn]
  have := norm_image_sub_le_of_norm_deriv_right_le_segment hDc hDd hbound t ht
  rwa [hD0, sub_zero] at this

/-- **The exact solution on the periodic blocks** (arXiv 2608.12893, §3 and (4.24), (A.52)). For
`|η| ≤ 1`, the solution of `A' = F_{j,η}(t, A)`, `A(0) = Y⁰_j`, on `[0, T]` with
`T ≤ 4 j h_j` is, up to a rotation `e^{σΩ}` by `|σ(t)| ≤ 2t`, the solution `E₁₁ + h_j³ W(t/h_j)`
of the forcing alone: `‖e^{-σΩ} A(t) e^{σΩ} - (E₁₁ + h_j³ W(t/h_j))‖ ≤ 6 ε_j T t`. So its retained
singular values stay `1` and `h_j³ + O(j² h_j⁴)` while the second singular directions turn with
`ν(t/h_j)`, the mechanism of the counterexample. -/
theorem flow_periodic {j : ℕ} {η : ℝ} (hη : |η| ≤ 1) {A : ℝ → M₃} {T : ℝ}
    (hT0 : 0 ≤ T) (hT : T ≤ 4 * j * hj j) (hA : ODESolution (Fj j η) A 0 T) (hA0 : A 0 = Y0 j) :
    ∃ σ : ℝ → ℝ, σ 0 = 0 ∧ ∀ t ∈ Icc 0 T, |σ t| ≤ 2 * t ∧
      ‖Rot (-σ t) * A t * Rot (σ t) - (E11 + hj j ^ 3 • W (t / hj j))‖ ≤ 6 * εj j * T * t := by
  have hh : 0 < hj j := by unfold hj; positivity
  have hAR : ODESolution (fun t _ => Rj j t) (fun t => E11 + hj j ^ 3 • W (t / hj j)) 0 T := by
    have hd : ∀ t, HasDerivAt (fun t => E11 + hj j ^ 3 • W (t / hj j))
        (hj j ^ 3 • ((1 / hj j) • Wd (t / hj j))) t := fun t => by
      have h1 : HasDerivAt (fun t : ℝ => t / hj j) (1 / hj j) t := by
        simpa using (hasDerivAt_id t).div_const (hj j)
      exact (((hasDerivAt_W (t / hj j)).scomp t h1).const_smul (hj j ^ 3)).const_add E11
    refine ⟨(continuous_iff_continuousAt.2 fun t => (hd t).continuousAt).continuousOn,
      fun t ht => ?_⟩
    have hle : t ≤ 4 * j * hj j := (le_of_lt ht.2).trans hT
    have e : Rj j t = hj j ^ 3 • ((1 / hj j) • Wd (t / hj j)) := by
      simp only [Rj, th, dth, hle, ↓reduceIte, smul_smul]
    rw [e]
    exact (hd t).hasDerivWithinAt
  have h0 : E11 + hj j ^ 3 • W (0 / hj j) = A 0 := by
    rw [hA0, zero_div]
    have hW : W 0 = E22 := by
      ext i k
      fin_cases i <;> fin_cases k <;> simp [W, nu, E22, Matrix.vecMulVec_apply]
    rw [hW, Y0]
  obtain ⟨σ, hσ0, -, hσ⟩ := flow_rot hη hT0 hA hAR h0
  exact ⟨σ, hσ0, fun t ht => by simpa using hσ t ht⟩

end LeanDLRA.Literature.P2608_12893
