import LeanDLRA.Tensor.Unfolding
import LeanDLRA.Integrators.TuckerBUG

/-!
# Tucker tensors: mode projectors, mode-wise interpolation and the Tucker integrators

The Tucker integrators of `LeanDLRA/Integrators/TuckerBUG.lean` (Tucker BUG, rank-adaptive and
parallel Tucker BUG; Ceruti–Lubich, arXiv 2010.02022, §5; Ceruti–Kusch–Lubich, arXiv
2104.05247, §4.2; Ceruti–Kusch–Lubich–Sulz, arXiv 2412.00858, §3) are stated for an abstract
family of mode projectors `P₁ i` and co-range projectors `Q₀ i`, assumed to be orthogonal
projectors and to commute. This file realizes them on actual tensors with `d` modes
(`Tensor ι`, `ι : Fin d → Type*`) and derives these structural hypotheses:

* the mode projectors `X ↦ X ×ᵢ Uᵢ Uᵢᵀ` (`modeProj i (U i)`) of orthonormal bases are pairwise
  commuting orthogonal projectors, so their product `∏ᵢ P₁ i` (`modeProd`) is the orthogonal
  projector `X ↦ X ×₁ U₁U₁ᵀ ⋯ ×_d U_dU_dᵀ`; it fixes the Tucker tensors `C ×ᵢ Uᵢ`;
* the co-range projectors `Q₀ i = actOn {j ≠ i} (V⁰ᵢ V⁰ᵢᵀ)` (acting on the modes `≠ i`, i.e. on
  the columns of `Matᵢ`) are orthogonal projectors commuting with the mode-`i` projector;
* `isTuckerBUGStep_of_orthonormal`: a Tucker BUG step whose projectors are given by orthonormal
  bases is an `IsTuckerBUGStep` as soon as its ODE, capture and normal-component conditions hold,
  so the robust error bounds (`tucker_local_error`, `tucker_global_error_le`) apply to it.

It also provides the mode-wise interpolation property used by tensor DEIM / cross methods
(Ghahremani–Babaee, arXiv 2401.04249, Eq. (12) for three modes; Dektor–Peng–Venturi, arXiv
2402.18721): if each matrix `Aᵢ` has unit rows at the sampled indices `Sᵢ` (as the oblique
projectors `Uᵢ (Sᵢᵀ Uᵢ)⁻¹ Sᵢᵀ` do), then `Z ×₁ A₁ ⋯ ×_d A_d` agrees with `Z` at every sampled
multi-index (`modeProd_modeAct_apply_eq`).

## Main results

* `isOrthProj_modeProd_modeProj`, `modeProj_comm_family`: the product of mode projectors.
* `modeProd_modeProj_tucker`: `(∏ᵢ P_{Uᵢ}) (C ×ᵢ Uᵢ) = C ×ᵢ Uᵢ`.
* `isOrthProj_coRangeProj`, `modeProj_comm_coRangeProj`: the co-range projectors.
* `isTuckerBUGStep_of_orthonormal`, `isParTuckerBUGStep_of_orthonormal`: concrete Tucker BUG and
  parallel Tucker BUG steps; `modeProj_modeProj_of_orth`.
* `modeAct_apply_eq_of_row_eq_one`, `modeProd_apply_apply_eq`, `modeProd_modeAct_apply_eq`:
  mode-wise interpolation.
-/

open scoped Matrix RealInnerProductSpace

namespace LeanDLRA.Tensor

variable {d : ℕ} {ι : Fin d → Type*} [∀ i, Fintype (ι i)]

/-! ### Mode projectors and their product -/

section ModeProjectors

variable {r : Fin d → Type*} [∀ i, Fintype (r i)]

/-- Mode projectors of different modes commute; as a family indexed by the modes. -/
theorem modeProj_comm_family (U : ∀ i, Matrix (ι i) (r i) ℝ) (i j : Fin d) (X : Tensor ι) :
    modeProj i (U i) (modeProj j (U j) X) = modeProj j (U j) (modeProj i (U i) X) := by
  by_cases hij : i = j
  · subst hij; rfl
  · exact modeProj_comm hij _ _ X

/-- The product `∏ᵢ P_{Uᵢ}` of the mode projectors of orthonormal bases is an orthogonal
projector (the core projector `Π` of the Tucker BUG integrator). -/
theorem isOrthProj_modeProd_modeProj [∀ i, DecidableEq (r i)] {U : ∀ i, Matrix (ι i) (r i) ℝ}
    (hU : ∀ i, (U i)ᵀ * U i = 1) : IsOrthProj (modeProd fun i => modeProj i (U i)) :=
  IsOrthProj.modeProd (fun i => isOrthProj_modeProj i (hU i)) (modeProj_comm_family U)

/-- A Tucker tensor is fixed by the product of the mode projectors of its orthonormal bases. -/
theorem modeProd_modeProj_tucker [∀ i, DecidableEq (r i)] {U : ∀ i, Matrix (ι i) (r i) ℝ}
    (hU : ∀ i, (U i)ᵀ * U i = 1) (C : Tensor r) :
    modeProd (fun i => modeProj i (U i)) (tucker C U) = tucker C U :=
  modeProd_apply_eq_self fun i => modeProj_tucker i (hU i) C

end ModeProjectors

/-! ### Co-range projectors -/

section CoRange

variable {s : Type*} [Fintype s] [DecidableEq s]

/-- The co-range projector `Q₀ = actOn {j ≠ i} (V Vᵀ)` of a matrix `V` with orthonormal columns
(rows indexed by the modes `≠ i`, i.e. the columns of the mode-`i` matricization) is an orthogonal
projector. -/
theorem isOrthProj_coRangeProj (i : Fin d) {V : Matrix (∀ k : {k : Fin d // k ≠ i}, ι k) s ℝ}
    (hV : Vᵀ * V = 1) : IsOrthProj (actOn (· ≠ i) (V * Vᵀ)) :=
  isOrthProj_actOn_mul_transpose _ hV

omit [DecidableEq s] in
/-- The mode-`i` projector commutes with the co-range projector of `Matᵢ`. -/
theorem modeProj_comm_coRangeProj (i : Fin d) {r : Type*} [Fintype r] (U : Matrix (ι i) r ℝ)
    (V : Matrix (∀ k : {k : Fin d // k ≠ i}, ι k) s ℝ) (X : Tensor ι) :
    modeProj i U (actOn (· ≠ i) (V * Vᵀ) X) = actOn (· ≠ i) (V * Vᵀ) (modeProj i U X) :=
  actOn_comm_of_disjoint _ (fun _ hk hk' => hk' hk) _ _ X

end CoRange

/-! ### Concrete Tucker BUG steps -/

/-- **Concrete Tucker BUG steps.** A step of the Tucker BUG integrator whose new mode bases
`U¹ᵢ` and co-range bases `V⁰ᵢ` have orthonormal columns, with `K`-step trajectories `YK i`,
capture `P_{U¹ᵢ} Kᵢ(t₁) = Kᵢ(t₁)`, doubly-normal bound `ε` and Galerkin core trajectory `YS`,
satisfies `IsTuckerBUGStep` with `P₁ i = modeProj i (U¹ i)` and
`Q₀ i = actOn {j ≠ i} (V⁰ᵢ V⁰ᵢᵀ)`: orthogonality and commutation of the projectors are
derived, not assumed. Hence the robust local and global error bounds of Ceruti–Lubich
(arXiv 2010.02022, Lemma 7 and Thm 7: `IsTuckerBUGStep.local_error_le`,
`tucker_global_error_le`) hold for it. -/
theorem isTuckerBUGStep_of_orthonormal {r s : Fin d → Type*} [∀ i, Fintype (r i)]
    [∀ i, DecidableEq (r i)] [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)]
    {U₁ : ∀ i, Matrix (ι i) (r i) ℝ} (hU₁ : ∀ i, (U₁ i)ᵀ * U₁ i = 1)
    {V₀ : ∀ i, Matrix (∀ k : {k : Fin d // k ≠ i}, ι k) (s i) ℝ}
    (hV₀ : ∀ i, (V₀ i)ᵀ * V₀ i = 1) {F : ℝ → Tensor ι → Tensor ι} {ε t₀ t₁ : ℝ}
    {Y₀ : Tensor ι} {YK : Fin d → ℝ → Tensor ι} {YS : ℝ → Tensor ι}
    (hK : ∀ i, ODESolution (fun t x => actOn (· ≠ i) (V₀ i * (V₀ i)ᵀ) (F t x)) (YK i) t₀ t₁)
    (hK₀ : ∀ i, YK i t₀ = Y₀) (hcap : ∀ i, modeProj i (U₁ i) (YK i t₁) = YK i t₁)
    (hε : ∀ i, ∀ t ∈ Set.Icc t₀ t₁, ‖(1 - modeProj i (U₁ i))
      ((1 - actOn (· ≠ i) (V₀ i * (V₀ i)ᵀ)) (F t (YK i t₁)))‖ ≤ ε)
    (hS : ODESolution (fun t x => modeProd (fun i => modeProj i (U₁ i)) (F t x)) YS t₀ t₁)
    (hS₀ : YS t₀ = modeProd (fun i => modeProj i (U₁ i)) Y₀) :
    IsTuckerBUGStep F ε (fun i => actOn (· ≠ i) (V₀ i * (V₀ i)ᵀ))
      (fun i => modeProj i (U₁ i)) t₀ t₁ Y₀ YK YS where
  projQ₀ i := isOrthProj_coRangeProj i (hV₀ i)
  projP₁ i := isOrthProj_modeProj i (hU₁ i)
  comm₁ := modeProj_comm_family U₁
  kSol := hK
  kStart := hK₀
  kCap := hcap
  kNormal := hε
  sSol := hS
  sStart := hS₀

/-- `X ×ₖ 0 = 0`. -/
@[simp] theorem modeAct_zero (k : Fin d) :
    modeAct k (0 : Matrix (ι k) (ι k) ℝ) = (0 : Tensor ι →L[ℝ] Tensor ι) := by
  simp [modeAct, Matrix.submatrix_zero]

/-- Mode projectors of mutually orthogonal bases of the same mode annihilate each other. -/
theorem modeProj_modeProj_of_orth (k : Fin d) {r s : Type*} [Fintype r] [Fintype s]
    {U : Matrix (ι k) r ℝ} {V : Matrix (ι k) s ℝ} (hUV : Uᵀ * V = 0) (X : Tensor ι) :
    modeProj k U (modeProj k V X) = 0 := by
  rw [modeProj, modeProj, modeAct_modeAct, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hUV,
    Matrix.zero_mul, Matrix.mul_zero, modeAct_zero]
  rfl

/-- **Concrete parallel Tucker BUG steps** (Ceruti–Kusch–Lubich–Sulz, arXiv 2412.00858, §3).
With old bases `U⁰ᵢ` and new directions `Ũᵢ` (both with orthonormal columns, `U⁰ᵢᵀ Ũᵢ = 0`)
and co-range bases `V⁰ᵢ`, the mode projectors `P₀ i = modeProj i (U⁰ i)`,
`Pa i = modeProj i (Ũ i)` and `Q₀ i = actOn {j ≠ i} (V⁰ᵢ V⁰ᵢᵀ)` satisfy all structural hypotheses
of `IsParTuckerBUGStep` (orthogonality, `P₀ i Pa i = 0`, commutation), so the robust error bound
of Thm 3.1 (`par_tucker_global_error_le`) holds for such steps. -/
theorem isParTuckerBUGStep_of_orthonormal {r ra s : Fin d → Type*} [∀ i, Fintype (r i)]
    [∀ i, DecidableEq (r i)] [∀ i, Fintype (ra i)] [∀ i, DecidableEq (ra i)]
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)]
    {U₀ : ∀ i, Matrix (ι i) (r i) ℝ} (hU₀ : ∀ i, (U₀ i)ᵀ * U₀ i = 1)
    {Ua : ∀ i, Matrix (ι i) (ra i) ℝ} (hUa : ∀ i, (Ua i)ᵀ * Ua i = 1)
    (horth : ∀ i, (U₀ i)ᵀ * Ua i = 0)
    {V₀ : ∀ i, Matrix (∀ k : {k : Fin d // k ≠ i}, ι k) (s i) ℝ}
    (hV₀ : ∀ i, (V₀ i)ᵀ * V₀ i = 1) {F : ℝ → Tensor ι → Tensor ι} {ε t₀ t₁ : ℝ}
    {Y₀ : Tensor ι} {YK : Fin d → ℝ → Tensor ι} {YC : ℝ → Tensor ι}
    (h₀ : ∀ i, modeProj i (U₀ i) Y₀ = Y₀)
    (hK : ∀ i, ODESolution (fun t x => actOn (· ≠ i) (V₀ i * (V₀ i)ᵀ) (F t x)) (YK i) t₀ t₁)
    (hK₀ : ∀ i, YK i t₀ = Y₀)
    (hcap : ∀ i, (modeProj i (U₀ i) + modeProj i (Ua i)) (YK i t₁) = YK i t₁)
    (hε : ∀ i, ∀ t ∈ Set.Icc t₀ t₁, ‖(1 - (modeProj i (U₀ i) + modeProj i (Ua i)))
      ((1 - actOn (· ≠ i) (V₀ i * (V₀ i)ᵀ)) (F t (YK i t₁)))‖ ≤ ε)
    (hC : ODESolution (fun t x => modeProd (fun i => modeProj i (U₀ i)) (F t x)) YC t₀ t₁)
    (hC₀ : YC t₀ = Y₀)
    (hn : ‖F t₀ Y₀ - modeProdLeOne (fun i => modeProj i (U₀ i))
      (fun i => 1 - modeProj i (U₀ i)) (F t₀ Y₀)‖ ≤ ε) :
    IsParTuckerBUGStep F ε (fun i => actOn (· ≠ i) (V₀ i * (V₀ i)ᵀ))
      (fun i => modeProj i (U₀ i)) (fun i => modeProj i (Ua i)) t₀ t₁ Y₀ YK YC where
  projQ₀ i := isOrthProj_coRangeProj i (hV₀ i)
  projP₀ i := isOrthProj_modeProj i (hU₀ i)
  projPa i := isOrthProj_modeProj i (hUa i)
  orth i x := modeProj_modeProj_of_orth i (horth i) x
  comm₀₀ := modeProj_comm_family U₀
  comm₀a i j x := by
    by_cases hij : i = j
    · subst hij
      rw [modeProj_modeProj_of_orth i (horth i), modeProj_modeProj_of_orth i
        (by rw [← Matrix.transpose_transpose (U₀ i), ← Matrix.transpose_mul, horth i,
          Matrix.transpose_zero])]
    · exact modeProj_comm hij _ _ x
  commaa := modeProj_comm_family Ua
  start₀ := h₀
  kSol := hK
  kStart := hK₀
  kCap := hcap
  kNormal := hε
  cSol := hC
  cStart := hC₀
  normal₀ := hn

/-! ### Mode-wise interpolation -/

section Interpolation

/-- A product of operators each of which reproduces every tensor at `x` reproduces it too. -/
theorem modeProd_apply_apply_eq {P : Fin d → Tensor ι →L[ℝ] Tensor ι} {x : ∀ i, ι i}
    (hP : ∀ i W, P i W x = W x) (Z : Tensor ι) : modeProd P Z x = Z x := by
  have key : ∀ l : List (Tensor ι →L[ℝ] Tensor ι), (∀ T ∈ l, ∀ W, T W x = W x) →
      ∀ W, l.prod W x = W x := by
    intro l
    induction l with
    | nil => intro _ W; rfl
    | cons T l ih =>
      intro h W
      rw [List.prod_cons]
      change T (l.prod W) x = W x
      rw [h T List.mem_cons_self, ih fun T' hT' => h T' (List.mem_cons_of_mem T hT')]
  exact key _ (fun T hT => by obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hT; exact hP i) Z

variable [∀ i, DecidableEq (ι i)]

/-- If the row of `A` at the index `x k` is the unit row, then `(Z ×ₖ A)(x) = Z(x)`. -/
theorem modeAct_apply_eq_of_row_eq_one (k : Fin d) {A : Matrix (ι k) (ι k) ℝ} (Z : Tensor ι)
    {x : ∀ i, ι i} (hA : ∀ c, A (x k) c = (1 : Matrix (ι k) (ι k) ℝ) (x k) c) :
    modeAct k A Z x = Z x := by
  simp [modeAct_apply, hA, Matrix.one_apply]

/-- **Mode-wise (DEIM) interpolation** (arXiv 2401.04249, Eq. (12) for `d = 3`): if every `Aᵢ`
has unit rows at the sampled indices `Sᵢ`, then `Z ×₁ A₁ ⋯ ×_d A_d` agrees with `Z` at every
multi-index whose entries are all sampled. For the oblique (DEIM) projectors
`Aᵢ = Uᵢ (Sᵢᵀ Uᵢ)⁻¹ Sᵢᵀ` the unit-row property is `Sᵢᵀ Aᵢ = Sᵢᵀ`. -/
theorem modeProd_modeAct_apply_eq (A : ∀ i, Matrix (ι i) (ι i) ℝ) (S : ∀ i, Set (ι i))
    (hA : ∀ i, ∀ a ∈ S i, ∀ c, A i a c = (1 : Matrix (ι i) (ι i) ℝ) a c) (Z : Tensor ι)
    {x : ∀ i, ι i} (hx : ∀ i, x i ∈ S i) :
    modeProd (fun i => modeAct i (A i)) Z x = Z x :=
  modeProd_apply_apply_eq (fun i W => modeAct_apply_eq_of_row_eq_one i W (hA i _ (hx i))) Z

end Interpolation

end LeanDLRA.Tensor
