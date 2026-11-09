import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.Interpolation
import LeanDLRA.Integrators.Matrix.BUG
import LeanDLRA.Integrators.Matrix.ProjectorSplitting
import LeanDLRA.Randomized.ObliqueBUG
import LeanDLRA.Literature.Randomized.P2408_16591a

/-!
# arXiv 2411.15990: DEIM, the interpolatory projector-splitting and the BUC integrators

Dektor and Einkemmer, *Interpolatory dynamical low-rank approximation for the 3+3d
Boltzmann–BGK equation*.  The paper has no numbered theorems; it defines two interpolatory
integrators and the DEIM index selection that makes them well defined.  This module formalizes,
in finite dimensions (the semi-discrete scheme of §3.1.1, real matrices, Frobenius norm), the
algorithm, the interpolatory projection (13), the substeps (21)–(23) and (27)–(29), and the
claims about them that the paper makes, phrased in the library's core definitions
(`obliqueProj`, `obliqueTangentProj`, `leftOblique`, `rightOblique`, `ODESolution`,
`MatrixKSL.IsStep`, `ObliqueBUG.IsObliqueBUGStep`).

## Algorithm 1 (DEIM)

* `IsDEIMStep`, `IsDEIMSelection`: the greedy selection in interpolation form (lines 1–2 and
  4–7 of Algorithm 1; ties in the arg max allowed).
* `det_submatrix_ne_zero_of_isDEIMSelection`: for `M` of full column rank, every DEIM selection
  gives an invertible `M(l,:)`.
* `eq_zero_of_mulVec_apply_eq_zero`, `exists_interp`: the interpolation problem of line 5 is
  uniquely solvable at every step; `exists_isDEIMSelection`,
  `exists_isDEIMSelection_of_orthonormal`: **Algorithm 1 never stalls** (§3.1: for orthonormal
  bases a sampling algorithm always yields well-defined interpolatory projectors).
* `isDEIM_of_isDEIMSelection`, `isDEIMSelection_of_isDEIM`: under full column rank,
  `IsDEIMSelection` is equivalent to `P2408_16591.IsDEIM` (the universally quantified form of
  `Literature/Randomized/P2408_16591a`).
* `deim_growth_bound_of_isDEIMSelection` (printed constant `(1 + √(2n))^{r-1} / ‖m₁‖_∞`),
  `deim_growth_bound_sharp_of_isDEIMSelection` (`1 + √n`), `specNorm_inv_le_of_isDEIMSelection`
  (`‖M(l,:)⁻¹‖₂ ≤ √n (1 + √n)^{r-1}` uniformly) and `specNorm_obliqueProj_sel_le` (Lebesgue
  constant of the DEIM projector): the Chaturantabut–Sorensen growth bound of the paper's
  reference [7], **not stated in arXiv 2411.15990**, obtained from
  `P2408_16591.deim_growth_bound` through the bridge.

## Eq. (13): the interpolatory tangent projection

* `obliqueTangentProj_sel_apply`: with selections `I(:,ℐ)`, `I(:,𝒥)` the library's
  `obliqueTangentProj` is the right-hand side of (13) in the discrete form of §3.1.1.
* `obliqueTangentProj_sel_interp` (and `transpose_mul_obliqueTangentProj`,
  `obliqueTangentProj_mul` for general test matrices): it interpolates `h` on all selected rows
  and on all selected columns, as claimed after (13).  That (13) is an oblique projection onto
  the tangent space is the core lemma `isObliqueProj_obliqueTangentProj`.

## Eqs. (21)–(23): interpolatory projector splitting

* `interpKField`, `collocField`, `interpLField` (verbatim forms `interpKField_sel`,
  `collocField_sel`, `interpLField_sel`) and `IsInterpKSLStep`: one step at the factor level.
* `odeSolution_interpKField`, `odeSolution_neg_collocField`, `odeSolution_interpLField`,
  `IsInterpKSLStep.fullSpace`: the substeps lift to the full-space flows
  `Y' = F 𝒫_Vᵀ`, `Y' = -𝒫_X F 𝒫_Vᵀ`, `Y' = 𝒫_X F`, and `rightOblique_sub_add_leftOblique`: these
  are the three terms of (13), i.e. (21)–(23) is the Lie–Trotter splitting of (13).
* `isInterpKSLStep_self_iff`: with the orthonormal bases as test matrices the step is exactly
  the orthogonal projector-splitting step `MatrixKSL.IsStep` (so its error bounds apply there).

## Eqs. (27)–(29): basis update and collocate (BUC)

* `IsBUCStep` (before truncation), `IsBUCStep.ys_start`: the augmented S-step starts at
  `f(t₀)` exactly (§3.2); `odeSolution_collocField`: the S-step flow is `𝒫_X̂ F 𝒫_V̂ᵀ`.
* `IsBUCStep.isObliqueBUGStep`: a BUC step is an `ObliqueBUG.IsObliqueBUGStep`, so the library's
  robust local and global error bounds for interpolatory BUG apply; with DEIM indices,
  `IsBUCStep.local_error_le_of_deim` gives a local error bound with the explicit Lebesgue
  constant `√N (1 + √N)^{R-1}` (a chain not stated in the paper, which has no error analysis).
* `collocField_sel_cross`: the BUC S-step velocity interpolates `h` on the cross `ℐ̂ × 𝒥̂`;
  `bucSStep_not_interp_row`: it does **not** interpolate on the remaining entries of the selected
  rows, so the sentence of §3.2 (p. 11) "`∂ₜ f(t)` interpolates `h(t)` whenever `i ∈ ℐ̂` or
  `j ∈ 𝒥̂`" holds only with "and" (checked in the printed PDF; counterexample with `r = 1`,
  `X̂ = V̂ ∈ ℝ^{3×2}`).

## Deviations and scope

* Finite dimensions only: the continuous formulation (4)–(16) on `L²(Ω_x × Ω_v)` is replaced by
  the semi-discrete matrix scheme (17)–(29); the Boltzmann–BGK right-hand side (18)–(20) is an
  arbitrary field `F : ℝ → ℝ^{N_x×N_v} → ℝ^{N_x×N_v}`, evaluated in each substep at the current
  substep value (`K V₀ᵀ`, `X₁ S̃ V₀ᵀ`, `X₁ Lᵀ`, `X̂ Ŝ V̂ᵀ`), which the paper leaves implicit.
* DEIM is formalized for matrices of full column rank (Algorithm 1 only requires `n ≥ r`, but
  line 5 needs invertible blocks; the paper applies DEIM to orthonormal bases).
* The substep structures take general test matrices `S_I`, `S_J`; DEIM is the instance
  `S = I(:,ℐ)` (`P2408_16591.sel`).  QR steps enter only through orthonormality and capture
  (`K(t₁) = X₁ R₁`; for BUC `X̂ X̂ᵀ K(t₁) = K(t₁)`, `X̂ X̂ᵀ X₀ = X₀`), and the BUC truncation step
  is not included.
* Not formalized: the "Ensure" line of Algorithm 1 ("minimizing condition number"), which the
  text itself describes as the goal of a greedy heuristic; the computational costs; the
  Boltzmann–BGK moments (19)–(20); oversampling variants; an error bound for the interpolatory
  projector-splitting integrator with genuinely oblique test matrices (the paper states none,
  and the library's KSL analysis needs orthogonal projectors).
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2411_15990

open LeanDLRA.Curvature

variable {n r : ℕ}

/-- Step `j` of the greedy DEIM selection (arXiv 2411.15990, Algorithm 1, lines 1–2 for `j = 0`
and lines 4–7 otherwise; indices are 0-based), in interpolation form. `l : Fin r → Fin n` are
the selected rows and `c` is the coefficient vector of the interpolant of column `j` on the
columns `< j`, which must match column `j` at the rows `l i` for `i < j`. The new index `l j`
maximises the absolute residual `|M i j - (M c) i|` (any maximiser; ties are allowed).
The coefficients are required to be supported on `k < j`; when `M` has full column rank and the
earlier steps are DEIM steps, the leading block `M(l i, k)_{i,k<j}` is invertible
(`eq_zero_of_mulVec_apply_eq_zero`), so `c` exists (`exists_interp`), is unique and is the
paper's `M(l,1:j-1)⁻¹ m(l)` padded by zeros. -/
def IsDEIMStep (M : Matrix (Fin n) (Fin r) ℝ) (l : Fin r → Fin n) (j : Fin r) : Prop :=
  ∃ c : Fin r → ℝ, (∀ k, j ≤ k → c k = 0) ∧
    (∀ i, i < j → ∑ k, M (l i) k * c k = M (l i) j) ∧
    ∀ i : Fin n, |M i j - ∑ k, M i k * c k| ≤ |M (l j) j - ∑ k, M (l j) k * c k|

/-- A complete greedy DEIM selection: every step `j` is a `IsDEIMStep`. -/
def IsDEIMSelection (M : Matrix (Fin n) (Fin r) ℝ) (l : Fin r → Fin n) : Prop :=
  ∀ j, IsDEIMStep M l j

/-- **DEIM well-posedness (arXiv 2411.15990, Algorithm 1; the invertibility part).**
If `M ∈ ℝ^{n×r}` has full column rank and `l` is a greedy DEIM selection for `M`, then the
selected square block `M(l,:)` is invertible. The proof writes `M T = N` with `T = 1 - C`
unit upper triangular, `N(l a, b) = 0` for `a < b` and `N(l b, b) ≠ 0`. -/
theorem det_submatrix_ne_zero_of_isDEIMSelection (M : Matrix (Fin n) (Fin r) ℝ)
    (hM : ∀ v : Fin r → ℝ, M.mulVec v = 0 → v = 0) {l : Fin r → Fin n}
    (hl : IsDEIMSelection M l) : (M.submatrix l id).det ≠ 0 := by
  choose c hc0 hcint hcmax using hl
  -- the coefficient matrix `C k j = c j k` and the unit triangular matrix `T = 1 - C`
  set T : Matrix (Fin r) (Fin r) ℝ := 1 - Matrix.of fun k j => c j k with hT
  set N : Matrix (Fin n) (Fin r) ℝ := M * T with hN
  have hTent : ∀ k j, T k j = (if k = j then 1 else 0) - c j k := by
    intro k j
    simp [hT, Matrix.one_apply]
  have hNent : ∀ i j, N i j = M i j - ∑ k, M i k * c j k := by
    intro i j
    simp only [hN, Matrix.mul_apply, hTent, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one,
      mul_zero]
    simp
  have hTup : T.IsUpperTriangular := by
    intro i j hji
    have hji' : j < i := hji
    simp [hTent, hji'.ne', hc0 j i hji'.le]
  have hTdiag : ∀ j, T j j = 1 := by
    intro j
    simp [hTent, hc0 j j le_rfl]
  have hTdet : T.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hTup]
    simp [hTdiag]
  -- the interpolation property: `N(l a, b) = 0` for `a < b`
  have hzero : ∀ a b, a < b → N (l a) b = 0 := by
    intro a b hab
    rw [hNent, hcint b a hab, sub_self]
  -- the residual is not identically zero: column `b` of `T` is nonzero
  have hdiag : ∀ b, N (l b) b ≠ 0 := by
    intro b
    have hex : ∃ i, N i b ≠ 0 := by
      by_contra hcon
      have hcon' : ∀ i, N i b = 0 := fun i => by
        by_contra h
        exact hcon ⟨i, h⟩
      have hv : M.mulVec (fun k => T k b) = 0 := by
        funext i
        have := hcon' i
        rw [hN, Matrix.mul_apply] at this
        simpa [Matrix.mulVec, dotProduct] using this
      have h0 := hM _ hv
      have := congrFun h0 b
      rw [hTdiag b] at this
      exact one_ne_zero this
    obtain ⟨i, hi⟩ := hex
    have hle := hcmax b i
    rw [← hNent, ← hNent] at hle
    intro hzb
    rw [hzb, abs_zero] at hle
    exact hi (abs_nonpos_iff.mp hle)
  -- `M(l,:) * T` is lower triangular with nonzero diagonal
  have hA : (M.submatrix l id * T).IsLowerTriangular := by
    intro a b hab
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
    have := hzero a b hab
    rw [hN, Matrix.mul_apply] at this
    exact this
  have hdetA : (M.submatrix l id * T).det ≠ 0 := by
    rw [(hA.det_ne_zero_iff)]
    intro i
    have := hdiag i
    simpa [Matrix.diag, Matrix.mul_apply, hN] using this
  rw [Matrix.det_mul, hTdet, mul_one] at hdetA
  exact hdetA

/-- **Non-vacuity.** The identity matrix with `l = ![0, 1]` satisfies the DEIM step conditions
(the coefficients may be taken to be zero), so `IsDEIMSelection` is not vacuous. -/
theorem isDEIMSelection_identity : IsDEIMSelection (1 : Matrix (Fin 2) (Fin 2) ℝ) ![0, 1] := by
  intro j
  refine ⟨0, fun k _ => rfl, fun i hi => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [Matrix.one_apply]
  · fin_cases j <;> fin_cases i <;> simp [Matrix.one_apply]

/-- Step `j` of a DEIM selection only depends on the indices `l i`, `i ≤ j`. -/
theorem IsDEIMStep.congr {M : Matrix (Fin n) (Fin r) ℝ} {l l' : Fin r → Fin n} {j : Fin r}
    (h : IsDEIMStep M l j) (hll : ∀ i, i ≤ j → l' i = l i) : IsDEIMStep M l' j := by
  obtain ⟨c, hc0, hci, hcm⟩ := h
  refine ⟨c, hc0, fun i hi => ?_, fun i => ?_⟩
  · rw [hll i hi.le]; exact hci i hi
  · rw [hll j le_rfl]; exact hcm i

/-- `(M (e_j - c))_i = M i j - ∑ₖ M i k c k` (the DEIM residual of column `j`). -/
lemma mulVec_single_sub_apply (M : Matrix (Fin n) (Fin r) ℝ) (j : Fin r) (c : Fin r → ℝ)
    (i : Fin n) : (M *ᵥ (Pi.single j 1 - c)) i = M i j - ∑ k, M i k * c k := by
  rw [Matrix.mulVec_sub, Pi.sub_apply, Matrix.mulVec_single_one]
  rfl

/-- The DEIM residual at the selected index is nonzero when `M` has full column rank: otherwise
the greedy maximum forces the whole residual `M (e_j - c)` to vanish, and `e_j - c ≠ 0`. -/
theorem residual_ne_zero {M : Matrix (Fin n) (Fin r) ℝ}
    (hM : ∀ v : Fin r → ℝ, M *ᵥ v = 0 → v = 0) {l : Fin r → Fin n} {j : Fin r}
    {c : Fin r → ℝ} (hc0 : ∀ k, j ≤ k → c k = 0)
    (hcm : ∀ i : Fin n, |M i j - ∑ k, M i k * c k| ≤ |M (l j) j - ∑ k, M (l j) k * c k|) :
    M (l j) j - ∑ k, M (l j) k * c k ≠ 0 := by
  intro h0
  have hv : M *ᵥ (Pi.single j 1 - c) = 0 := by
    funext i
    rw [mulVec_single_sub_apply]
    have := hcm i
    rw [h0, abs_zero] at this
    exact abs_nonpos_iff.mp this
  have := congrFun (hM _ hv) j
  simp [hc0 j le_rfl] at this

/-- **Unisolvence of the DEIM interpolation problem.**  If `M` has full column rank and the
first `k` greedy steps of `l` are DEIM steps, then a coefficient vector `d` supported on the
first `k` columns whose combination `M d` vanishes at the selected rows `l i`, `i < k`, is zero.
Equivalently, the leading block `M(l(1:k), 1:k)` is invertible. -/
theorem eq_zero_of_mulVec_apply_eq_zero {M : Matrix (Fin n) (Fin r) ℝ}
    (hM : ∀ v : Fin r → ℝ, M *ᵥ v = 0 → v = 0) {l : Fin r → Fin n} {k : ℕ}
    (hl : ∀ j : Fin r, (j : ℕ) < k → IsDEIMStep M l j) {d : Fin r → ℝ}
    (hd0 : ∀ i : Fin r, k ≤ (i : ℕ) → d i = 0)
    (hdi : ∀ i : Fin r, (i : ℕ) < k → (M *ᵥ d) (l i) = 0) : d = 0 := by
  choose! c hc0 hci hcm using hl
  suffices H : ∀ p ≤ k, ∀ d : Fin r → ℝ, (∀ i : Fin r, p ≤ (i : ℕ) → d i = 0) →
      (∀ i : Fin r, (i : ℕ) < p → (M *ᵥ d) (l i) = 0) → d = 0 from H k le_rfl d hd0 hdi
  intro p
  induction p with
  | zero => intro _ d hd _; funext i; exact hd i (Nat.zero_le _)
  | succ p ih =>
    intro hp d hd hdi
    by_cases hpr : p < r
    · set pp : Fin r := ⟨p, hpr⟩ with hpp
      have hpk : (pp : ℕ) < k := by simp [hpp]; omega
      set α := d pp
      set w : Fin r → ℝ := Pi.single pp 1 - c pp with hw
      have hwM : ∀ i, (M *ᵥ w) i = M i pp - ∑ x, M i x * c pp x :=
        fun i => mulVec_single_sub_apply M pp (c pp) i
      have hd' : d - α • w = 0 := by
        refine ih (by omega) _ (fun i hi => ?_) (fun i hi => ?_)
        · rcases (show (pp : ℕ) = i ∨ (pp : ℕ) < i by simp [hpp]; omega) with h | h
          · have hi' : i = pp := Fin.ext h.symm
            subst hi'
            simp [hw, α, hc0 pp hpk pp le_rfl]
          · have h1 : d i = 0 := hd i (by simp [hpp] at h; omega)
            have h2 : c pp i = 0 := hc0 pp hpk i (Fin.le_def.2 h.le)
            have h3 : (Pi.single pp (1 : ℝ) : Fin r → ℝ) i = 0 := by
              rw [Pi.single_apply, ite_eq_right (fun h' => by rw [h'] at h; exact lt_irrefl _ h)]
            simp [hw, h1, h2, h3]
        · have hi' : i < pp := Fin.lt_def.2 (by simp [hpp]; omega)
          rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, hwM,
            hci pp hpk i hi', hdi i (by omega), sub_self, smul_zero, sub_self]
      have hdα : d = α • w := sub_eq_zero.1 hd'
      have hres := residual_ne_zero hM (hc0 pp hpk) (hcm pp hpk)
      have hα : α = 0 := by
        have h := hdi pp (by simp [hpp])
        rw [hdα, Matrix.mulVec_smul, Pi.smul_apply, hwM, smul_eq_mul] at h
        exact (mul_eq_zero.1 h).resolve_right hres
      rw [hdα, hα, zero_smul]
    · exact ih (by omega) d (fun i hi => absurd i.isLt (by omega))
        (fun i hi => hdi i (by omega))

/-- **The DEIM interpolation problem is solvable.**  Under the hypotheses of
`eq_zero_of_mulVec_apply_eq_zero`, for any prescribed values `y i` (`i < k`) there is a
coefficient vector `c` supported on the first `k` columns with `(M c)(l i) = y i` for `i < k`. -/
theorem exists_interp {M : Matrix (Fin n) (Fin r) ℝ}
    (hM : ∀ v : Fin r → ℝ, M *ᵥ v = 0 → v = 0) {l : Fin r → Fin n} {k : ℕ}
    (hl : ∀ j : Fin r, (j : ℕ) < k → IsDEIMStep M l j) (y : Fin r → ℝ) :
    ∃ c : Fin r → ℝ, (∀ i : Fin r, k ≤ (i : ℕ) → c i = 0) ∧
      ∀ i : Fin r, (i : ℕ) < k → (M *ᵥ c) (l i) = y i := by
  classical
  set A : Matrix (Fin r) (Fin r) ℝ := Matrix.of fun i x =>
    if (i : ℕ) < k then M (l i) x else (1 : Matrix (Fin r) (Fin r) ℝ) i x with hA
  have hAapp : ∀ v i, (A *ᵥ v) i = if (i : ℕ) < k then (M *ᵥ v) (l i) else v i := by
    intro v i
    by_cases hi : (i : ℕ) < k
    · simp [hA, hi, Matrix.mulVec, dotProduct]
    · simp [hA, hi, Matrix.mulVec, dotProduct, Matrix.one_apply]
  have hinj : Function.Injective A.mulVec := by
    intro v w hvw
    have h0 : A *ᵥ (v - w) = 0 := by rw [Matrix.mulVec_sub]; exact sub_eq_zero.2 hvw
    refine sub_eq_zero.1 (eq_zero_of_mulVec_apply_eq_zero hM hl (fun i hi => ?_) fun i hi => ?_)
    · have := congrFun h0 i
      rwa [hAapp, ite_eq_right (by omega)] at this
    · have := congrFun h0 i
      rwa [hAapp, ite_eq_left hi] at this
  have hsurj : Function.Surjective A.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.2 (Matrix.mulVec_injective_iff_isUnit.1 hinj)
  obtain ⟨c, hc⟩ := hsurj fun i => if (i : ℕ) < k then y i else 0
  refine ⟨c, fun i hi => ?_, fun i hi => ?_⟩
  · have := congrFun hc i
    rwa [hAapp, ite_eq_right (by omega), ite_eq_right (by omega)] at this
  · have := congrFun hc i
    rwa [hAapp, ite_eq_left hi, ite_eq_left hi] at this

/-- **Algorithm 1 never stalls** (arXiv 2411.15990, Algorithm 1; the paper's claim, §3.1, that
for orthonormal bases a sparse sampling algorithm always yields well-defined interpolatory
projectors).  Every `M ∈ ℝ^{n×r}` with full column rank (in particular every `M` with
orthonormal columns, `exists_isDEIMSelection_of_orthonormal`) has a greedy DEIM selection: at
each step the interpolation problem of line 5 is uniquely solvable, and the arg max of line 7
exists.  Ties in the arg max are allowed (any maximiser is a DEIM step). -/
theorem exists_isDEIMSelection (M : Matrix (Fin n) (Fin r) ℝ)
    (hM : ∀ v : Fin r → ℝ, M *ᵥ v = 0 → v = 0) : ∃ l : Fin r → Fin n, IsDEIMSelection M l := by
  classical
  suffices H : ∀ k ≤ r, ∃ l : Fin r → Fin n, ∀ j : Fin r, (j : ℕ) < k → IsDEIMStep M l j by
    obtain ⟨l, hl⟩ := H r le_rfl
    exact ⟨l, fun j => hl j j.isLt⟩
  intro k
  induction k with
  | zero =>
    intro _
    rcases isEmpty_or_nonempty (Fin r) with hr | ⟨⟨j₀⟩⟩
    · exact ⟨fun j => isEmptyElim j, fun j => isEmptyElim j⟩
    · have hn : Nonempty (Fin n) := by
        by_contra hn
        rw [not_nonempty_iff] at hn
        have := congrFun (hM (Pi.single j₀ 1) (funext fun i => isEmptyElim i)) j₀
        simp at this
      exact ⟨fun _ => Classical.arbitrary _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk
    obtain ⟨l, hl⟩ := ih (by omega)
    set kk : Fin r := ⟨k, by omega⟩ with hkk
    obtain ⟨c, hc0, hci⟩ := exists_interp hM hl fun i => M (l i) kk
    have : Nonempty (Fin n) := ⟨l kk⟩
    obtain ⟨q, hq⟩ := Finite.exists_max fun i => |M i kk - (M *ᵥ c) i|
    refine ⟨Function.update l kk q, fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hjk | hjk
    · refine (hl j hjk).congr fun i hi => Function.update_of_ne (fun h => ?_) _ _
      have : (i : ℕ) = k := by rw [h]
      have : (i : ℕ) ≤ j := hi
      omega
    · have hj' : j = kk := Fin.ext hjk
      subst hj'
      refine ⟨c, fun x hx => hc0 x hx, fun i hi => ?_, fun i => ?_⟩
      · rw [Function.update_of_ne (ne_of_lt hi)]
        exact hci i hi
      · rw [Function.update_self]
        exact hq i

/-- Orthonormal columns give full column rank. -/
lemma mulVec_eq_zero_of_orthonormal {M : Matrix (Fin n) (Fin r) ℝ} (hM : Mᵀ * M = 1)
    (v : Fin r → ℝ) (hv : M *ᵥ v = 0) : v = 0 := by
  have h := congrArg (Mᵀ *ᵥ ·) hv
  simp only [Matrix.mulVec_mulVec, hM, Matrix.one_mulVec, Matrix.mulVec_zero] at h
  exact h

/-- **Algorithm 1 never stalls on an orthonormal basis** (the setting of arXiv 2411.15990,
§3.1: "when the bases `X` and `V` are orthonormal, it is always possible to find a collection
of points that yield well-defined interpolatory projectors"): a DEIM selection exists and the
selected block `M(l,:)` is invertible. -/
theorem exists_isDEIMSelection_of_orthonormal {M : Matrix (Fin n) (Fin r) ℝ} (hM : Mᵀ * M = 1) :
    ∃ l : Fin r → Fin n, IsDEIMSelection M l ∧ (M.submatrix l id).det ≠ 0 := by
  obtain ⟨l, hl⟩ := exists_isDEIMSelection M (mulVec_eq_zero_of_orthonormal hM)
  exact ⟨l, hl, det_submatrix_ne_zero_of_isDEIMSelection M
    (mulVec_eq_zero_of_orthonormal hM) hl⟩

/-- **Bridge to `P2408_16591.IsDEIM`.**  Under full column rank, a DEIM selection in the
existential form `IsDEIMSelection` (Algorithm 1 of arXiv 2411.15990) satisfies the universal
form `IsDEIM` of `Literature/Randomized/P2408_16591a` (the greedy inequality for *every*
interpolant), because the interpolant is unique (`eq_zero_of_mulVec_apply_eq_zero`). -/
theorem isDEIM_of_isDEIMSelection {M : Matrix (Fin n) (Fin r) ℝ}
    (hM : ∀ v : Fin r → ℝ, M *ᵥ v = 0 → v = 0) {l : Fin r → Fin n}
    (hl : IsDEIMSelection M l) : P2408_16591.IsDEIM M l := by
  intro j c hc0 hci i
  obtain ⟨c', hc0', hci', hcm'⟩ := hl j
  have hd : c - c' = 0 := by
    refine eq_zero_of_mulVec_apply_eq_zero hM (k := j) (fun j' _ => hl j') (fun x hx => ?_)
      (fun x hx => ?_)
    · have hx' : j ≤ x := Fin.le_def.2 hx
      simp [hc0 x hx', hc0' x hx']
    · have hx' : x < j := Fin.lt_def.2 hx
      rw [Matrix.mulVec_sub, Pi.sub_apply, hci x hx']
      exact sub_eq_zero.2 (hci' x hx').symm
  have hcc : c = c' := sub_eq_zero.1 hd
  subst hcc
  exact hcm' i

/-- **Converse bridge.**  Under full column rank, `P2408_16591.IsDEIM` implies
`IsDEIMSelection`: the interpolant required by each step exists (`exists_interp`). -/
theorem isDEIMSelection_of_isDEIM {M : Matrix (Fin n) (Fin r) ℝ}
    (hM : ∀ v : Fin r → ℝ, M *ᵥ v = 0 → v = 0) {l : Fin r → Fin n}
    (hl : P2408_16591.IsDEIM M l) : IsDEIMSelection M l := by
  suffices H : ∀ k : ℕ, ∀ j : Fin r, (j : ℕ) < k → IsDEIMStep M l j from
    fun j => H _ j (Nat.lt_succ_self _)
  intro k
  induction k with
  | zero => intro j hj; exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hjk | hjk
    · exact ih j hjk
    · obtain ⟨c, hc0, hci⟩ := exists_interp hM (k := j) (fun j' hj' => ih j' (by omega))
        fun i => M (l i) j
      exact ⟨c, fun x hx => hc0 x (Fin.le_def.1 hx), fun i hi => hci i (Fin.lt_def.1 hi),
        hl j c (fun x hx => hc0 x (Fin.le_def.1 hx)) (fun i hi => hci i (Fin.lt_def.1 hi))⟩

/-- **DEIM growth bound** (Chaturantabut–Sorensen, the reference [7] of arXiv 2411.15990 for
Algorithm 1; *not stated in arXiv 2411.15990*, which only calls DEIM a greedy algorithm for
small condition numbers).  For `M ∈ ℝ^{n×r}` with orthonormal columns, `r ≥ 1`, and a DEIM
selection `l` (Algorithm 1), `M(l,:)` is invertible and
`‖M(l,:)⁻¹‖₂ ≤ (1 + √(2n))^{r-1} / ‖m₁‖_∞` (the printed constant), where `m₁` is the first
column.  Derived from `P2408_16591.eq20_deim_bound` through `isDEIM_of_isDEIMSelection`;
`deim_growth_bound_sharp_of_isDEIMSelection` has the sharper factor `1 + √n`. -/
theorem deim_growth_bound_of_isDEIMSelection {M : Matrix (Fin n) (Fin r) ℝ} (hr : 0 < r)
    (hM : Mᵀ * M = 1) {l : Fin r → Fin n} (hl : IsDEIMSelection M l) :
    IsUnit (M.submatrix l id).det ∧
      specNorm (M.submatrix l id)⁻¹ ≤ (1 + √(2 * n)) ^ (r - 1) / ‖fun i => M i ⟨0, hr⟩‖ := by
  have hD := isDEIM_of_isDEIMSelection (mulVec_eq_zero_of_orthonormal hM) hl
  exact ⟨(P2408_16591.deim_growth_bound hr hM hD).1, P2408_16591.eq20_deim_bound hr hM hD⟩

/-- **DEIM growth bound, sharper constant**: `‖M(l,:)⁻¹‖₂ ≤ (1 + √n)^{r-1} / ‖m₁‖_∞`
(`P2408_16591.deim_growth_bound`). -/
theorem deim_growth_bound_sharp_of_isDEIMSelection {M : Matrix (Fin n) (Fin r) ℝ} (hr : 0 < r)
    (hM : Mᵀ * M = 1) {l : Fin r → Fin n} (hl : IsDEIMSelection M l) :
    specNorm (M.submatrix l id)⁻¹ ≤ (1 + √n) ^ (r - 1) / ‖fun i => M i ⟨0, hr⟩‖ :=
  (P2408_16591.deim_growth_bound hr hM
    (isDEIM_of_isDEIMSelection (mulVec_eq_zero_of_orthonormal hM) hl)).2

/-- A unit vector has a large entry: `1 ≤ √n ‖m_j‖_∞` for every column `m_j` of an orthonormal
`M ∈ ℝ^{n×r}`. -/
lemma one_le_sqrt_mul_norm_col {M : Matrix (Fin n) (Fin r) ℝ} (hM : Mᵀ * M = 1) (j : Fin r) :
    1 ≤ √n * ‖fun i => M i j‖ := by
  set s := ‖fun i => M i j‖ with hs
  have hs0 : 0 ≤ s := norm_nonneg _
  have hle : ∀ i, |M i j| ≤ s := fun i => by
    have := norm_le_pi_norm (fun i => M i j) i
    simpa using this
  have h1 : ∑ i, M i j * M i j = 1 := by
    have := congrFun (congrFun hM j) j
    simpa [Matrix.mul_apply] using this
  have h2 : (1 : ℝ) ≤ n * s ^ 2 := by
    calc (1 : ℝ) = ∑ i, M i j * M i j := h1.symm
      _ ≤ ∑ _i : Fin n, s ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := hle i
          have h0 := abs_nonneg (M i j)
          nlinarith [abs_mul_abs_self (M i j)]
      _ = n * s ^ 2 := by simp
  have hsq : (√n * s) ^ 2 = n * s ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  nlinarith [Real.sqrt_nonneg (n : ℝ), mul_nonneg (Real.sqrt_nonneg (n : ℝ)) hs0]

/-- **Uniform DEIM Lebesgue constant.**  For orthonormal `M ∈ ℝ^{n×r}` and a DEIM selection,
`‖M(l,:)⁻¹‖₂ ≤ √n (1 + √n)^{r-1}`, independently of `M` (since `‖m₁‖_∞ ≥ 1/√n`).  Not stated
in arXiv 2411.15990; a corollary of `deim_growth_bound_sharp_of_isDEIMSelection`. -/
theorem specNorm_inv_le_of_isDEIMSelection {M : Matrix (Fin n) (Fin r) ℝ} (hr : 0 < r)
    (hM : Mᵀ * M = 1) {l : Fin r → Fin n} (hl : IsDEIMSelection M l) :
    specNorm (M.submatrix l id)⁻¹ ≤ √n * (1 + √n) ^ (r - 1) := by
  have h := deim_growth_bound_sharp_of_isDEIMSelection hr hM hl
  have h1 := one_le_sqrt_mul_norm_col hM ⟨0, hr⟩
  set s := ‖fun i => M i (⟨0, hr⟩ : Fin r)‖
  have hs : 0 < s := by
    by_contra hs
    have : s = 0 := le_antisymm (not_lt.1 hs) (norm_nonneg _)
    rw [this, mul_zero] at h1
    linarith
  have hB : 0 ≤ (1 + √(n : ℝ)) ^ (r - 1) := by positivity
  refine h.trans ?_
  rw [div_le_iff₀ hs]
  calc (1 + √(n : ℝ)) ^ (r - 1) = (1 + √n) ^ (r - 1) * 1 := (mul_one _).symm
    _ ≤ (1 + √n) ^ (r - 1) * (√n * s) := mul_le_mul_of_nonneg_left h1 hB
    _ = √n * (1 + √n) ^ (r - 1) * s := by ring


/-! ### Eq. (13): the interpolatory tangent projection -/

section Interpolatory

variable {m n k k' : Type*} [Fintype m] [Fintype n] [Fintype k] [DecidableEq k] [Fintype k']
  [DecidableEq k']

/-- **Row interpolation of the interpolatory tangent projection** (arXiv 2411.15990, §3.1, the
property `∂ₜ f_r(𝐱, v) = h(𝐱, v)` of eq. (13)): if `S_Uᵀ U` is invertible, the oblique tangent
projection reproduces `Z` on the rows selected by `S_U`: `S_Uᵀ P^∠(Y)[Z] = S_Uᵀ Z`. -/
theorem transpose_mul_obliqueTangentProj {U SU : Matrix m k ℝ} {V SV : Matrix n k' ℝ}
    (hSU : IsUnit (SUᵀ * U).det) (Z : Matrix m n ℝ) :
    SUᵀ * obliqueTangentProj U SU V SV Z = SUᵀ * Z := by
  simp only [obliqueTangentProj_apply, Matrix.mul_add, Matrix.mul_sub, ← Matrix.mul_assoc,
    transpose_mul_obliqueProj hSU]
  abel

/-- **Column interpolation of the interpolatory tangent projection** (arXiv 2411.15990, §3.1,
the property `∂ₜ f_r(x, 𝐯) = h(x, 𝐯)` of eq. (13)): if `S_Vᵀ V` is invertible,
`P^∠(Y)[Z] S_V = Z S_V`. -/
theorem obliqueTangentProj_mul {U SU : Matrix m k ℝ} {V SV : Matrix n k' ℝ}
    (hSV : IsUnit (SVᵀ * V).det) (Z : Matrix m n ℝ) :
    obliqueTangentProj U SU V SV Z * SV = Z * SV := by
  simp only [obliqueTangentProj_apply, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc,
    obliqueProj_transpose_mul hSV]
  abel

/-! ### Eqs. (21)–(23) and (27)–(29): the interpolatory substep fields -/

/-- The interpolatory **K-step field** of eqs. (21) and (27) of arXiv 2411.15990 with a test
matrix `S_J` (for DEIM, the selection `I(:, 𝒥)`): `K ↦ F(t, K V₀ᵀ) S_J (S_Jᵀ V₀)⁻ᵀ`, i.e.
`h(t, :, 𝒥) V(t₀, 𝒥, :)⁻ᵀ` (`interpKField_sel`). -/
noncomputable def interpKField (V₀ SJ : Matrix n k' ℝ) (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t : ℝ)
    (K : Matrix m k' ℝ) : Matrix m k' ℝ :=
  F t (K * V₀ᵀ) * SJ * ((SJᵀ * V₀)⁻¹)ᵀ

/-- The interpolatory **L-step field** of eqs. (23) and (28) of arXiv 2411.15990 with a test
matrix `S_I`: `L ↦ (S_Iᵀ F(t, U Lᵀ))ᵀ (S_Iᵀ U)⁻ᵀ`, i.e. `h(t, ℐ, :)ᵀ X(ℐ, :)⁻ᵀ`
(`interpLField_sel`); `U = X(t₁)` in (23) and `U = X(t₀)` in (28). -/
noncomputable def interpLField (U SI : Matrix m k ℝ) (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t : ℝ)
    (L : Matrix n k ℝ) : Matrix n k ℝ :=
  (SIᵀ * F t (U * Lᵀ))ᵀ * ((SIᵀ * U)⁻¹)ᵀ

/-- The **collocation field** `S ↦ (S_Iᵀ U)⁻¹ (S_Iᵀ F(t, U S Vᵀ) S_J) (S_Jᵀ V)⁻ᵀ`, i.e.
`X(ℐ, :)⁻¹ h(t, ℐ, 𝒥) V(𝒥, :)⁻ᵀ` (`collocField_sel`): the S-step (29) of BUC
(arXiv 2411.15990); with a minus sign, the backward S-step (22) of the interpolatory projector
splitting integrator. -/
noncomputable def collocField (U SI : Matrix m k ℝ) (V SJ : Matrix n k' ℝ)
    (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t : ℝ) (S : Matrix k k' ℝ) : Matrix k k' ℝ :=
  (SIᵀ * U)⁻¹ * (SIᵀ * F t (U * S * Vᵀ) * SJ) * ((SJᵀ * V)⁻¹)ᵀ

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ}

/-- **K-step lift** (eqs. (21), (27)).  If `K' = F(t, K V₀ᵀ) S_J (S_Jᵀ V₀)⁻ᵀ`, then
`Y_K = K V₀ᵀ` solves `Y_K' = F(t, Y_K) 𝒫_{V₀}ᵀ`, the right oblique projection
`rightOblique V₀ S_J` (the K-step map of `ObliqueBUG.IsObliqueBUGStep`). -/
theorem odeSolution_interpKField {V₀ SJ : Matrix n k' ℝ} {K : ℝ → Matrix m k' ℝ}
    (hK : ODESolution (interpKField V₀ SJ F) K t₀ t₁) :
    ODESolution (fun t x => rightOblique V₀ SJ (F t x)) (fun t => K t * V₀ᵀ) t₀ t₁ :=
  MatrixBUG.odeSolution_comp_clm hK (Frobenius.rightMulCLM V₀ᵀ) fun t x => by
    simp only [Frobenius.rightMulCLM_apply, rightOblique_apply, interpKField, obliqueProj,
      Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- **L-step lift** (eqs. (23), (28)).  If `L' = (S_Iᵀ F(t, U Lᵀ))ᵀ (S_Iᵀ U)⁻ᵀ`, then
`Y_L = U Lᵀ` solves `Y_L' = 𝒫_U F(t, Y_L)`, the left oblique projection `leftOblique U S_I`. -/
theorem odeSolution_interpLField {U SI : Matrix m k ℝ} {Lf : ℝ → Matrix n k ℝ}
    (hL : ODESolution (interpLField U SI F) Lf t₀ t₁) :
    ODESolution (fun t x => leftOblique U SI (F t x)) (fun t => U * (Lf t)ᵀ) t₀ t₁ :=
  MatrixBUG.odeSolution_comp_clm hL ((Frobenius.leftMulCLM U).comp Frobenius.transposeCLM)
    fun t x => by
      simp only [ContinuousLinearMap.comp_apply, Frobenius.leftMulCLM_apply,
        Frobenius.transposeCLM_apply, leftOblique_apply, interpLField, obliqueProj,
        Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- **Collocation S-step lift** (eq. (29)).  If `S' = (S_Iᵀ U)⁻¹ (S_Iᵀ F(t, U S Vᵀ) S_J)
(S_Jᵀ V)⁻ᵀ`, then `Y_S = U S Vᵀ` solves `Y_S' = 𝒫_U F(t, Y_S) 𝒫_Vᵀ`, the two-sided
interpolatory projection `leftOblique U S_I ∘ rightOblique V S_J`. -/
theorem odeSolution_collocField {U SI : Matrix m k ℝ} {V SJ : Matrix n k' ℝ}
    {S : ℝ → Matrix k k' ℝ} (hS : ODESolution (collocField U SI V SJ F) S t₀ t₁) :
    ODESolution (fun t x => leftOblique U SI (rightOblique V SJ (F t x)))
      (fun t => U * S t * Vᵀ) t₀ t₁ :=
  MatrixBUG.odeSolution_comp_clm hS ((Frobenius.rightMulCLM Vᵀ).comp (Frobenius.leftMulCLM U))
    fun t x => by
      simp only [ContinuousLinearMap.comp_apply, Frobenius.leftMulCLM_apply,
        Frobenius.rightMulCLM_apply, leftOblique_apply, rightOblique_apply, collocField,
        obliqueProj, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- **Backward S-step lift** (eq. (22)).  If `S' = -(S_Iᵀ U)⁻¹ (S_Iᵀ F(t, U S V₀ᵀ) S_J)
(S_Jᵀ V₀)⁻ᵀ`, then `Y_S = U S V₀ᵀ` solves `Y_S' = -𝒫_U F(t, Y_S) 𝒫_{V₀}ᵀ`. -/
theorem odeSolution_neg_collocField {U SI : Matrix m k ℝ} {V₀ SJ : Matrix n k' ℝ}
    {S : ℝ → Matrix k k' ℝ}
    (hS : ODESolution (fun t x => -collocField U SI V₀ SJ F t x) S t₀ t₁) :
    ODESolution (fun t x => -leftOblique U SI (rightOblique V₀ SJ (F t x)))
      (fun t => U * S t * V₀ᵀ) t₀ t₁ :=
  MatrixBUG.odeSolution_comp_clm hS ((Frobenius.rightMulCLM V₀ᵀ).comp (Frobenius.leftMulCLM U))
    fun t x => by
      simp only [ContinuousLinearMap.comp_apply, Frobenius.leftMulCLM_apply,
        Frobenius.rightMulCLM_apply, leftOblique_apply, rightOblique_apply, collocField,
        obliqueProj, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
        Matrix.mul_neg, Matrix.neg_mul]

/-- **The three substeps split eq. (13)** (arXiv 2411.15990, §3.1: "to integrate (13) we use
operator splitting ... three substeps").  The lifted right-hand sides of the K-step (21),
backward S-step (22) and L-step (23) add up to the interpolatory tangent projection (13):
`Z 𝒫_Vᵀ - 𝒫_U Z 𝒫_Vᵀ + 𝒫_U Z = P^∠(Y)[Z]`. -/
theorem rightOblique_sub_add_leftOblique (U SU : Matrix m k ℝ) (V SV : Matrix n k' ℝ)
    (Z : Matrix m n ℝ) :
    rightOblique V SV Z - leftOblique U SU (rightOblique V SV Z) + leftOblique U SU Z =
      obliqueTangentProj U SU V SV Z := by
  simp only [rightOblique_apply, leftOblique_apply, obliqueTangentProj_apply, Matrix.mul_assoc]
  abel

omit [Fintype m] in
/-- Under orthonormality the interpolatory K-step field with the orthogonal test matrix
`S_J = V₀` is the K-step field of the orthogonal projector-splitting / BUG integrator. -/
lemma interpKField_self {V₀ : Matrix n k' ℝ} (hV₀ : V₀ᵀ * V₀ = 1) :
    interpKField V₀ V₀ F = MatrixKSL.kField V₀ F := by
  funext t K
  simp [interpKField, MatrixKSL.kField, hV₀]

omit [Fintype n] in
/-- With `S_I = U` orthonormal, the interpolatory L-step field is the orthogonal one. -/
lemma interpLField_self {U : Matrix m k ℝ} (hU : Uᵀ * U = 1) :
    interpLField U U F = MatrixKSL.lField U F := by
  funext t L
  simp [interpLField, MatrixKSL.lField, hU, Matrix.transpose_mul]

/-- With `S_I = U`, `S_J = V` orthonormal, the collocation field is the Galerkin field
`S ↦ Uᵀ F(t, U S Vᵀ) V`. -/
lemma collocField_self {U : Matrix m k ℝ} {V : Matrix n k' ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) : collocField U U V V F = MatrixBUG.sField U V F := by
  funext t S
  simp [collocField, MatrixBUG.sField, hU, hV]

end Interpolatory

/-! ### The interpolatory projector-splitting integrator, eqs. (21)–(23) -/

section KSL

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]

/-- **One step of the interpolatory projector-splitting integrator** (arXiv 2411.15990,
§3.1.1, eqs. (21)–(23)) from `f(t₀) = X₀ S₀ V₀ᵀ` (`V₀` orthonormal) to `t₁`, at the level of
the factors, with test matrices `S_J` (columns, for DEIM `I(:, 𝒥)` with `𝒥 = DEIM(V₀)`) and
`S_I` (rows, `I(:, ℐ)` with `ℐ = DEIM(X₁)`):

* K-step (21): `K' = h(t, :, 𝒥) V₀(𝒥, :)⁻ᵀ`, `K(t₀) = X₀ S₀`, QR `K(t₁) = X₁ R₁`;
* backward S-step (22): `S̃' = -X₁(ℐ, :)⁻¹ h(t, ℐ, 𝒥) V₀(𝒥, :)⁻ᵀ`, `S̃(t₀) = R₁`;
* L-step (23): `L' = h(t, ℐ, :)ᵀ X₁(ℐ, :)⁻ᵀ`, `L(t₀) = V₀ S̃(t₁)ᵀ`; the new value is
  `f(t₁) = X₁ L(t₁)ᵀ` (`= X₁ S₁ V₁ᵀ` after the final QR `L(t₁) = V₁ S₁ᵀ`).

Here `h(t) = F(t, f)` is evaluated at the current substep value `f = K V₀ᵀ`, `X₁ S̃ V₀ᵀ`,
`X₁ Lᵀ` (as in the orthogonal projector-splitting integrator; the paper suppresses this
argument). -/
structure IsInterpKSLStep (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ t₁ : ℝ)
    (X₀ : Matrix m r ℝ) (S₀ : Matrix r r ℝ) (V₀ SJ : Matrix n r ℝ) (X₁ SI : Matrix m r ℝ)
    (R₁ : Matrix r r ℝ) (K : ℝ → Matrix m r ℝ) (S : ℝ → Matrix r r ℝ)
    (Lf : ℝ → Matrix n r ℝ) : Prop where
  orthV₀ : V₀ᵀ * V₀ = 1
  /-- K-step (21). -/
  kSol : ODESolution (interpKField V₀ SJ F) K t₀ t₁
  kStart : K t₀ = X₀ * S₀
  orthX₁ : X₁ᵀ * X₁ = 1
  /-- QR decomposition `K(t₁) = X(t₁) R(t₁)`. -/
  kQR : K t₁ = X₁ * R₁
  /-- Backward S-step (22). -/
  sSol : ODESolution (fun t x => -collocField X₁ SI V₀ SJ F t x) S t₀ t₁
  sStart : S t₀ = R₁
  /-- L-step (23). -/
  lSol : ODESolution (interpLField X₁ SI F) Lf t₀ t₁
  lStart : Lf t₀ = V₀ * (S t₁)ᵀ

namespace IsInterpKSLStep

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} {X₀ X₁ SI : Matrix m r ℝ}
  {S₀ R₁ : Matrix r r ℝ} {V₀ SJ : Matrix n r ℝ} {K : ℝ → Matrix m r ℝ}
  {S : ℝ → Matrix r r ℝ} {Lf : ℝ → Matrix n r ℝ}

/-- **The substeps in the full space** (arXiv 2411.15990, §3.1): with
`R_K = rightOblique V₀ S_J` (`Z ↦ Z 𝒫_{V₀}ᵀ`) and `P_I = leftOblique X₁ S_I`
(`Z ↦ 𝒫_{X₁} Z`), the trajectories `Y_K = K V₀ᵀ`, `Y_S = X₁ S̃ V₀ᵀ`, `Y_L = X₁ Lᵀ` solve
`Y_K' = R_K F`, `Y_S' = -P_I R_K F`, `Y_L' = P_I F` (the three terms of eq. (13),
`rightOblique_sub_add_leftOblique`) and are chained: `Y_K(t₀) = f(t₀)`,
`Y_S(t₀) = Y_K(t₁)`, `Y_L(t₀) = Y_S(t₁)`. -/
theorem fullSpace (hs : IsInterpKSLStep F t₀ t₁ X₀ S₀ V₀ SJ X₁ SI R₁ K S Lf) :
    ODESolution (fun t x => rightOblique V₀ SJ (F t x)) (fun t => K t * V₀ᵀ) t₀ t₁ ∧
      ODESolution (fun t x => -leftOblique X₁ SI (rightOblique V₀ SJ (F t x)))
        (fun t => X₁ * S t * V₀ᵀ) t₀ t₁ ∧
      ODESolution (fun t x => leftOblique X₁ SI (F t x)) (fun t => X₁ * (Lf t)ᵀ) t₀ t₁ ∧
      K t₀ * V₀ᵀ = X₀ * S₀ * V₀ᵀ ∧ X₁ * S t₀ * V₀ᵀ = K t₁ * V₀ᵀ ∧
      X₁ * (Lf t₀)ᵀ = X₁ * S t₁ * V₀ᵀ := by
  refine ⟨odeSolution_interpKField hs.kSol, odeSolution_neg_collocField hs.sSol,
    odeSolution_interpLField hs.lSol, by rw [hs.kStart], by rw [hs.sStart, hs.kQR], ?_⟩
  rw [hs.lStart, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- The new approximation lies in the range of the new left basis: `X₁ X₁ᵀ f(t₁) = f(t₁)`. -/
theorem mem_range (hs : IsInterpKSLStep F t₀ t₁ X₀ S₀ V₀ SJ X₁ SI R₁ K S Lf) :
    leftProj X₁ (X₁ * (Lf t₁)ᵀ) = X₁ * (Lf t₁)ᵀ :=
  leftProj_mul_left hs.orthX₁ _

end IsInterpKSLStep

/-- **The orthogonal projector-splitting integrator is the special case `S_J = V₀`,
`S_I = X₁`.**  With the orthonormal bases themselves as test matrices, one step of the
interpolatory projector-splitting integrator (21)–(23) is exactly one step of the
Lubich–Oseledets projector-splitting (KSL) integrator `MatrixKSL.IsStep` (eqs. (10)–(12) of
arXiv 2411.15990 in matrix form), and conversely.  Hence the robust error bounds
`MatrixKSL.IsStep.local_error` and `MatrixKSL.global_error` apply to this special case. -/
theorem isInterpKSLStep_self_iff {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ}
    {X₀ X₁ : Matrix m r ℝ} {S₀ R₁ : Matrix r r ℝ} {V₀ : Matrix n r ℝ} {K : ℝ → Matrix m r ℝ}
    {S : ℝ → Matrix r r ℝ} {Lf : ℝ → Matrix n r ℝ} (hX₁ : X₁ᵀ * X₁ = 1) :
    IsInterpKSLStep F t₀ t₁ X₀ S₀ V₀ V₀ X₁ X₁ R₁ K S Lf ↔
      MatrixKSL.IsStep F t₀ t₁ X₀ S₀ V₀ X₁ R₁ K S Lf := by
  have hS : ∀ hV₀ : V₀ᵀ * V₀ = 1, (fun t x => -collocField X₁ X₁ V₀ V₀ F t x) =
      MatrixKSL.sField X₁ V₀ F := fun hV₀ => by
    funext t x
    rw [collocField_self hX₁ hV₀]
    rfl
  constructor
  · intro hs
    refine ⟨hs.orthV₀, ?_, hs.kStart, hs.orthX₁, hs.kQR, ?_, hs.sStart, ?_, hs.lStart⟩
    · rw [← interpKField_self hs.orthV₀]; exact hs.kSol
    · rw [← hS hs.orthV₀]; exact hs.sSol
    · rw [← interpLField_self hX₁]; exact hs.lSol
  · intro hs
    refine ⟨hs.orthV₀, ?_, hs.kStart, hs.orthU₁, hs.kQR, ?_, hs.sStart, ?_, hs.lStart⟩
    · rw [interpKField_self hs.orthV₀]; exact hs.kSol
    · rw [hS hs.orthV₀]; exact hs.sSol
    · rw [interpLField_self hX₁]; exact hs.lSol

end KSL

/-! ### The basis update and collocate (BUC) integrator, eqs. (27)–(29) -/

section BUC

variable {m n r k k' : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq r] [Fintype k]
  [DecidableEq k] [Fintype k'] [DecidableEq k']

/-- **One step of the basis update and collocate (BUC) integrator** (arXiv 2411.15990, §3.2,
eqs. (27)–(29)) from `f(t₀) = X₀ S₀ V₀ᵀ` (`X₀`, `V₀` orthonormal) to `t₁`, before the
truncation step, at the level of the factors, with test matrices `S_I`, `S_J` (for DEIM, the
selections `ℐ = DEIM(X₀)`, `𝒥 = DEIM(V₀)`) and `Ŝ_I`, `Ŝ_J` (`ℐ̂ = DEIM(X̂)`,
`𝒥̂ = DEIM(V̂)`):

* K-step (27): `K' = h(t, :, 𝒥) V₀(𝒥, :)⁻ᵀ`, `K(t₀) = X₀ S₀`; the augmented basis `X̂`
  (`k` columns, `2r` in the paper) is orthonormal and its range contains those of `K(t₁)` and
  `X₀` (the QR decomposition `[K(t₁), X₀] = X̂ R`);
* L-step (28): `L' = h(t, ℐ, :)ᵀ X₀(ℐ, :)⁻ᵀ`, `L(t₀) = V₀ S₀ᵀ`; likewise `V̂` for
  `[L(t₁), V₀]`;
* S-step (29): `Ŝ' = X̂(ℐ̂, :)⁻¹ h(t, ℐ̂, 𝒥̂) V̂(𝒥̂, :)⁻ᵀ`, `Ŝ(t₀) = M̂ S₀ N̂ᵀ` with
  `M̂ = X̂ᵀ X₀`, `N̂ = V̂ᵀ V₀`.

The (untruncated) new value is `X̂ Ŝ(t₁) V̂ᵀ`; `h(t) = F(t, f)` is evaluated at the current
substep value `K V₀ᵀ`, `X₀ Lᵀ`, `X̂ Ŝ V̂ᵀ`. -/
structure IsBUCStep (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ t₁ : ℝ) (X₀ SI : Matrix m r ℝ)
    (S₀ : Matrix r r ℝ) (V₀ SJ : Matrix n r ℝ) (Xa SIa : Matrix m k ℝ) (Va SJa : Matrix n k' ℝ)
    (K : ℝ → Matrix m r ℝ) (Lf : ℝ → Matrix n r ℝ) (Sa : ℝ → Matrix k k' ℝ) : Prop where
  orthX₀ : X₀ᵀ * X₀ = 1
  orthV₀ : V₀ᵀ * V₀ = 1
  /-- K-step (27). -/
  kSol : ODESolution (interpKField V₀ SJ F) K t₀ t₁
  kStart : K t₀ = X₀ * S₀
  /-- L-step (28). -/
  lSol : ODESolution (interpLField X₀ SI F) Lf t₀ t₁
  lStart : Lf t₀ = V₀ * S₀ᵀ
  orthXa : Xaᵀ * Xa = 1
  /-- `X̂` captures `K(t₁)`. -/
  kCap : Xa * Xaᵀ * K t₁ = K t₁
  /-- `X̂` captures `X₀` (augmentation). -/
  augX : Xa * Xaᵀ * X₀ = X₀
  orthVa : Vaᵀ * Va = 1
  /-- `V̂` captures `L(t₁)`. -/
  lCap : Va * Vaᵀ * Lf t₁ = Lf t₁
  /-- `V̂` captures `V₀` (augmentation). -/
  augV : Va * Vaᵀ * V₀ = V₀
  /-- Collocation S-step (29). -/
  sSol : ODESolution (collocField Xa SIa Va SJa F) Sa t₀ t₁
  /-- `Ŝ(t₀) = M̂ S₀ N̂ᵀ`. -/
  sStart : Sa t₀ = Xaᵀ * X₀ * S₀ * (V₀ᵀ * Va)

namespace IsBUCStep

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} {X₀ SI : Matrix m r ℝ}
  {S₀ : Matrix r r ℝ} {V₀ SJ : Matrix n r ℝ} {Xa SIa : Matrix m k ℝ} {Va SJa : Matrix n k' ℝ}
  {K : ℝ → Matrix m r ℝ} {Lf : ℝ → Matrix n r ℝ} {Sa : ℝ → Matrix k k' ℝ}

/-- **BUC represents the initial value exactly** (arXiv 2411.15990, §3.2: "we augment with
`X(t₀)`, `V(t₀)` so that the initial value `f(t₀)` can be represented exactly"):
`X̂ Ŝ(t₀) V̂ᵀ = X̂ M̂ S₀ N̂ᵀ V̂ᵀ = f(t₀)`. -/
theorem ys_start (hs : IsBUCStep F t₀ t₁ X₀ SI S₀ V₀ SJ Xa SIa Va SJa K Lf Sa) :
    Xa * Sa t₀ * Vaᵀ = X₀ * S₀ * V₀ᵀ := by
  have hT : V₀ᵀ * Va * Vaᵀ = V₀ᵀ := by
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose hs.augV
  rw [hs.sStart]
  calc Xa * (Xaᵀ * X₀ * S₀ * (V₀ᵀ * Va)) * Vaᵀ
      = Xa * Xaᵀ * X₀ * S₀ * (V₀ᵀ * Va * Vaᵀ) := by simp only [Matrix.mul_assoc]
    _ = X₀ * S₀ * V₀ᵀ := by rw [hs.augX, hT]

/-- **BUC is an interpolatory BUG step** (connection to the robust error analysis of
`ObliqueBUG`).  The factor trajectories of one BUC step satisfy all hypotheses of
`ObliqueBUG.IsObliqueBUGStep` with the oblique maps `R_K = rightOblique V₀ S_J`,
`R_L = leftOblique X₀ S_I`, `P_A = leftOblique X̂ Ŝ_I`, `Q_A = rightOblique V̂ Ŝ_J` onto the
orthogonal projectors of `V₀`, `X₀`, `X̂`, `V̂`, provided the four selected blocks
`S_Jᵀ V₀`, `S_Iᵀ X₀`, `Ŝ_Iᵀ X̂`, `Ŝ_Jᵀ V̂` are invertible, their oblique projectors have spectral
norm `≤ η` (Lebesgue constant), and the doubly-normal components of `F` at `K(t₁) V₀ᵀ` and
`X₀ L(t₁)ᵀ` are `≤ ε` (the paper states no error bound; these are the hypotheses of the
library's oblique BUG analysis). -/
theorem isObliqueBUGStep [DecidableEq m] [DecidableEq n] [Nonempty m] [Nonempty n] [Nonempty r]
    [Nonempty k] [Nonempty k']
    (hs : IsBUCStep F t₀ t₁ X₀ SI S₀ V₀ SJ Xa SIa Va SJa K Lf Sa)
    (hSI : IsUnit (SIᵀ * X₀).det) (hSJ : IsUnit (SJᵀ * V₀).det)
    (hSIa : IsUnit (SIaᵀ * Xa).det) (hSJa : IsUnit (SJaᵀ * Va).det) {η : ℝ}
    (hηK : specNorm (obliqueProj V₀ SJ) ≤ η) (hηL : specNorm (obliqueProj X₀ SI) ≤ η)
    (hηA : specNorm (obliqueProj Xa SIa) ≤ η) (hηB : specNorm (obliqueProj Va SJa) ≤ η)
    {ε : ℝ}
    (hεK : ∀ t ∈ Icc t₀ t₁, ‖(1 - Xa * Xaᵀ) * F t (K t₁ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε)
    (hεL : ∀ t ∈ Icc t₀ t₁, ‖(1 - X₀ * X₀ᵀ) * F t (X₀ * (Lf t₁)ᵀ) * (1 - Va * Vaᵀ)‖ ≤ ε) :
    ObliqueBUG.IsObliqueBUGStep F ε η (leftProj X₀) (rightProj V₀) (leftProj Xa) (rightProj Va)
      (rightOblique V₀ SJ) (leftOblique X₀ SI) (leftOblique Xa SIa) (rightOblique Va SJa) t₀ t₁
      (X₀ * S₀ * V₀ᵀ) (fun t => K t * V₀ᵀ) (fun t => X₀ * (Lf t)ᵀ)
      (fun t => Xa * Sa t * Vaᵀ) where
  obliqueK := isObliqueProj_rightOblique hs.orthV₀ hSJ
  obliqueL := isObliqueProj_leftOblique hs.orthX₀ hSI
  ne_Q₀ := rightProj_ne_zero hs.orthV₀
  ne_P₀ := leftProj_ne_zero hs.orthX₀
  projP₁ := isOrthProj_leftProj hs.orthXa
  projQ₁ := isOrthProj_rightProj hs.orthVa
  commK x := by
    simp only [leftProj_apply, rightOblique_apply, Matrix.mul_assoc]
  commL x := by
    simp only [rightProj_apply, leftOblique_apply, Matrix.mul_assoc]
  obliqueA := isObliqueProj_leftOblique hs.orthXa hSIa
  obliqueB := isObliqueProj_rightOblique hs.orthVa hSJa
  ne_P₁ := leftProj_ne_zero hs.orthXa
  ne_Q₁ := rightProj_ne_zero hs.orthVa
  normRK := (opNorm_rightOblique_le V₀ SJ).trans hηK
  normRL := (opNorm_leftOblique_le X₀ SI).trans hηL
  normPA := (opNorm_leftOblique_le Xa SIa).trans hηA
  normQA := (opNorm_rightOblique_le Va SJa).trans hηB
  kSol := odeSolution_interpKField hs.kSol
  kStart := by rw [hs.kStart]
  kCap := by rw [leftProj_apply, ← Matrix.mul_assoc, hs.kCap]
  kNormal t ht := by
    rw [one_sub_leftProj_one_sub_rightProj_apply]
    exact hεK t ht
  lSol := odeSolution_interpLField hs.lSol
  lStart := by
    rw [hs.lStart, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  lCap := by
    have hT : (Lf t₁)ᵀ * Va * Vaᵀ = (Lf t₁)ᵀ := by
      simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose hs.lCap
    rw [rightProj_apply, Matrix.mul_assoc X₀, Matrix.mul_assoc X₀, hT]
  lNormal t ht := by
    rw [MatrixBUG.one_sub_rightProj_one_sub_leftProj_apply]
    exact hεL t ht
  sSol := odeSolution_collocField hs.sSol
  sStart := by
    have hP : leftProj Xa (X₀ * S₀ * V₀ᵀ) = X₀ * S₀ * V₀ᵀ := by
      rw [leftProj_apply, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hs.augX, Matrix.mul_assoc]
    have hQ : rightProj Va (X₀ * S₀ * V₀ᵀ) = X₀ * S₀ * V₀ᵀ := by
      have hT : V₀ᵀ * Va * Vaᵀ = V₀ᵀ := by
        simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose hs.augV
      simp only [rightProj_apply, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc V₀ᵀ Va, hT]
    have h := ObliqueBUG.buc_start_eq (isObliqueProj_leftOblique hs.orthXa hSIa)
      (isObliqueProj_rightOblique hs.orthVa hSJa) hP hQ
    change Xa * Sa t₀ * Vaᵀ = _
    rw [hs.ys_start, h.1]

end IsBUCStep

end BUC


/-! ### The DEIM selection in the paper's index notation -/

section Selection

open LeanDLRA.Literature.P2408_16591 (sel sel_transpose_mul mul_sel)

variable {m n k k' : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [Fintype k]
  [DecidableEq k] [Fintype k'] [DecidableEq k']

omit [Fintype k] [DecidableEq k] [Fintype k'] [DecidableEq k'] in
/-- `Sᵀ Z S' = Z(ℐ, 𝒥)` for the selections `S = I(:, ℐ)`, `S' = I(:, 𝒥)`. -/
lemma sel_transpose_mul_mul_sel (I : k → m) (J : k' → n) (Z : Matrix m n ℝ) :
    (sel I)ᵀ * Z * sel J = Z.submatrix I J := by
  rw [sel_transpose_mul, mul_sel, Matrix.submatrix_submatrix]
  rfl

/-- **Eq. (13) of arXiv 2411.15990, discrete form** (§3.1.1): with interpolation indices `ℐ`
(rows) and `𝒥` (columns), the oblique tangent projector `obliqueTangentProj X I(:,ℐ) V I(:,𝒥)`
of the library is
`h ↦ h(:, 𝒥) V(𝒥,:)⁻ᵀ Vᵀ - X X(ℐ,:)⁻¹ h(ℐ, 𝒥) V(𝒥,:)⁻ᵀ Vᵀ + X X(ℐ,:)⁻¹ h(ℐ, :)`.
(An algebraic identity; `⁻¹` is Mathlib's `Matrix.inv`, the inverse when it exists.) -/
theorem obliqueTangentProj_sel_apply (X : Matrix m k ℝ) (V : Matrix n k' ℝ) (I : k → m)
    (J : k' → n) (h : Matrix m n ℝ) :
    obliqueTangentProj X (sel I) V (sel J) h =
      h.submatrix id J * ((V.submatrix J id)⁻¹)ᵀ * Vᵀ
        - X * (X.submatrix I id)⁻¹ * h.submatrix I J * ((V.submatrix J id)⁻¹)ᵀ * Vᵀ
        + X * (X.submatrix I id)⁻¹ * h.submatrix I id := by
  have hP : obliqueProj X (sel I) = X * (X.submatrix I id)⁻¹ * (sel I)ᵀ := by
    rw [obliqueProj, sel_transpose_mul]
  have hQ : (obliqueProj V (sel J))ᵀ = sel J * (((V.submatrix J id)⁻¹)ᵀ * Vᵀ) := by
    rw [obliqueProj, sel_transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose]
  have hA : obliqueProj X (sel I) * h = X * (X.submatrix I id)⁻¹ * h.submatrix I id := by
    rw [hP, Matrix.mul_assoc _ (sel I)ᵀ, sel_transpose_mul]
  have hB : h * (obliqueProj V (sel J))ᵀ =
      h.submatrix id J * ((V.submatrix J id)⁻¹)ᵀ * Vᵀ := by
    rw [hQ, ← Matrix.mul_assoc, mul_sel, Matrix.mul_assoc]
  have hC : obliqueProj X (sel I) * h * (obliqueProj V (sel J))ᵀ =
      X * (X.submatrix I id)⁻¹ * h.submatrix I J * ((V.submatrix J id)⁻¹)ᵀ * Vᵀ := by
    rw [hA, hQ]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (h.submatrix I id) (sel J), mul_sel, Matrix.submatrix_submatrix]
    rfl
  rw [obliqueTangentProj_apply, hC, hA, hB]
  abel

/-- **Interpolation property of eq. (13)** (arXiv 2411.15990, §3.1: "`∂ₜ f_r(𝐱, v) = h(𝐱, v)`
and `∂ₜ f(x, 𝐯) = h(x, 𝐯)`, i.e. `∂ₜ f_r` interpolates `h` whenever `x ∈ 𝐱` or `v ∈ 𝐯`"):
if `X(ℐ,:)` and `V(𝒥,:)` are invertible, the interpolatory tangent projection of `h` agrees with
`h` on all selected rows and on all selected columns. -/
theorem obliqueTangentProj_sel_interp {X : Matrix m k ℝ} {V : Matrix n k' ℝ} {I : k → m}
    {J : k' → n} (hI : IsUnit (X.submatrix I id).det) (hJ : IsUnit (V.submatrix J id).det)
    (h : Matrix m n ℝ) :
    (obliqueTangentProj X (sel I) V (sel J) h).submatrix I id = h.submatrix I id ∧
      (obliqueTangentProj X (sel I) V (sel J) h).submatrix id J = h.submatrix id J := by
  have hI' : IsUnit ((sel I)ᵀ * X).det := by rwa [sel_transpose_mul]
  have hJ' : IsUnit ((sel J)ᵀ * V).det := by rwa [sel_transpose_mul]
  constructor
  · rw [← sel_transpose_mul, ← sel_transpose_mul]
    exact transpose_mul_obliqueTangentProj hI' h
  · rw [← mul_sel, ← mul_sel]
    exact obliqueTangentProj_mul hJ' h

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}

omit [Fintype m] [DecidableEq m] in
/-- The K-step field in the paper's notation: `interpKField V₀ I(:,𝒥) F t K =
h(t, :, 𝒥) V₀(𝒥, :)⁻ᵀ` with `h(t) = F(t, K V₀ᵀ)` (eqs. (21), (27)). -/
lemma interpKField_sel (V₀ : Matrix n k' ℝ) (J : k' → n) (t : ℝ) (K : Matrix m k' ℝ) :
    interpKField V₀ (sel J) F t K =
      (F t (K * V₀ᵀ)).submatrix id J * ((V₀.submatrix J id)⁻¹)ᵀ := by
  rw [interpKField, mul_sel, sel_transpose_mul]

omit [Fintype n] [DecidableEq n] in
/-- The L-step field in the paper's notation: `h(t, ℐ, :)ᵀ X(ℐ, :)⁻ᵀ` with
`h(t) = F(t, X Lᵀ)` (eqs. (23), (28)). -/
lemma interpLField_sel (X : Matrix m k ℝ) (I : k → m) (t : ℝ) (L : Matrix n k ℝ) :
    interpLField X (sel I) F t L =
      ((F t (X * Lᵀ)).submatrix I id)ᵀ * ((X.submatrix I id)⁻¹)ᵀ := by
  rw [interpLField, sel_transpose_mul, sel_transpose_mul]

/-- The collocation field in the paper's notation: `X(ℐ, :)⁻¹ h(t, ℐ, 𝒥) V(𝒥, :)⁻ᵀ` with
`h(t) = F(t, X S Vᵀ)` (eq. (29); with a minus sign eq. (22)). -/
lemma collocField_sel (X : Matrix m k ℝ) (I : k → m) (V : Matrix n k' ℝ) (J : k' → n) (t : ℝ)
    (S : Matrix k k' ℝ) :
    collocField X (sel I) V (sel J) F t S =
      (X.submatrix I id)⁻¹ * (F t (X * S * Vᵀ)).submatrix I J * ((V.submatrix J id)⁻¹)ᵀ := by
  rw [collocField, sel_transpose_mul_mul_sel, sel_transpose_mul, sel_transpose_mul]

/-- **The BUC S-step collocates on the cross** (arXiv 2411.15990, §3.2): if `X̂(ℐ̂,:)` and
`V̂(𝒥̂,:)` are invertible, the S-step velocity `∂ₜ f = X̂ Ŝ' V̂ᵀ` of eq. (29) agrees with
`h = F(t, X̂ Ŝ V̂ᵀ)` at all entries `(i, j) ∈ ℐ̂ × 𝒥̂`.  See `bucSStep_not_interp_row` for the
failure on the rest of the selected rows. -/
theorem collocField_sel_cross {X : Matrix m k ℝ} {I : k → m} {V : Matrix n k' ℝ} {J : k' → n}
    (hI : IsUnit (X.submatrix I id).det) (hJ : IsUnit (V.submatrix J id).det) (t : ℝ)
    (S : Matrix k k' ℝ) :
    (X * collocField X (sel I) V (sel J) F t S * Vᵀ).submatrix I J =
      (F t (X * S * Vᵀ)).submatrix I J := by
  have hI' : IsUnit ((sel I)ᵀ * X).det := by rwa [sel_transpose_mul]
  have hJ' : IsUnit ((sel J)ᵀ * V).det := by rwa [sel_transpose_mul]
  have hE : X * collocField X (sel I) V (sel J) F t S * Vᵀ =
      obliqueProj X (sel I) * F t (X * S * Vᵀ) * (obliqueProj V (sel J))ᵀ := by
    simp only [collocField, obliqueProj, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc]
  rw [hE, ← sel_transpose_mul_mul_sel, ← sel_transpose_mul_mul_sel,
    transpose_mul_obliqueProj_mul_mul hI' hJ']

end Selection

/-- **The BUC S-step does not interpolate on the selected rows** (counterexample to the
literal reading of arXiv 2411.15990, §3.2, p. 11: "we compute a coefficient matrix `Ŝ(t)` so
that `∂ₜ f(t)` interpolates `h(t)` whenever `i ∈ ℐ̂` or `j ∈ 𝒥̂`").  Take `r = 1`, the augmented
bases `X̂ = V̂ = [e₁, e₂] ∈ ℝ^{3×2}` (`2r = 2` orthonormal columns), their DEIM indices
`ℐ̂ = 𝒥̂ = (1, 2)` (so `X̂(ℐ̂,:) = V̂(𝒥̂,:) = I₂`) and the constant field `h = 𝟙𝟙ᵀ ∈ ℝ^{3×3}`.  The
S-step velocity `X̂ Ŝ' V̂ᵀ` of eq. (29) vanishes in the third column, so it differs from `h` at
`(1, 3)` although `1 ∈ ℐ̂`.  It does agree with `h` on the cross `ℐ̂ × 𝒥̂`
(`collocField_sel_cross`), which is all that the `|ℐ̂| |𝒥̂|` collocation conditions on the
`|ℐ̂| × |𝒥̂|` matrix `Ŝ'` can enforce; the printed "or" holds with "and". -/
theorem bucSStep_not_interp_row :
    let X : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 1; 0, 0]
    let I : Fin 2 → Fin 3 := ![0, 1]
    let h : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun _ _ => 1
    Xᵀ * X = 1 ∧ IsDEIMSelection X I ∧ IsUnit (X.submatrix I id).det ∧
      (X * collocField X (P2408_16591.sel I) X (P2408_16591.sel I) (fun _ _ => h) 0 0 * Xᵀ)
        (I 0) 2 ≠ h (I 0) 2 := by
  intro X I h
  have hXI : X.submatrix I id = 1 := by
    ext a b; fin_cases a <;> fin_cases b <;> simp [X, I]
  refine ⟨?_, fun j => ⟨0, fun c _ => rfl, fun i hi => ?_, fun i => ?_⟩, ?_, ?_⟩
  · ext a b; fin_cases a <;> fin_cases b <;> simp [X, Matrix.mul_apply, Fin.sum_univ_succ]
  · fin_cases i <;> fin_cases j <;> simp_all [X, I]
  · fin_cases j <;> fin_cases i <;> simp [X, I]
  · rw [hXI, Matrix.det_one]; exact isUnit_one
  · rw [collocField_sel, hXI]
    simp [X, I, h, Matrix.mul_apply, Fin.sum_univ_succ]

/-! ### DEIM Lebesgue constants and the error of BUC with DEIM indices (not in the paper) -/

section Chain

open LeanDLRA.Literature.P2408_16591 (sel sel_transpose_mul sel_orthonormal
  injective_of_isUnit_det)

/-- `√N (1 + √N)^{R-1}` is monotone in `N` and `R`. -/
lemma deimConst_mono {N N' R R' : ℕ} (hN : N ≤ N') (hR : R ≤ R') :
    √(N : ℝ) * (1 + √(N : ℝ)) ^ (R - 1) ≤ √(N' : ℝ) * (1 + √(N' : ℝ)) ^ (R' - 1) := by
  have h1 : √(N : ℝ) ≤ √(N' : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hN)
  have h2 : (1 + √(N : ℝ)) ^ (R - 1) ≤ (1 + √(N' : ℝ)) ^ (R - 1) :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have h3 : (1 + √(N' : ℝ)) ^ (R - 1) ≤ (1 + √(N' : ℝ)) ^ (R' - 1) :=
    pow_le_pow_right₀ (by linarith [Real.sqrt_nonneg (N' : ℝ)]) (by omega)
  calc √(N : ℝ) * (1 + √(N : ℝ)) ^ (R - 1) ≤ √(N' : ℝ) * (1 + √(N' : ℝ)) ^ (R - 1) :=
        mul_le_mul h1 h2 (by positivity) (Real.sqrt_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)

/-- **Lebesgue constant of the DEIM interpolatory projector.**  For orthonormal
`U ∈ ℝ^{N×R}` (`R ≥ 1`) and a DEIM selection `ℐ` (Algorithm 1 of arXiv 2411.15990), the
selected block is invertible and the oblique projector `𝒫 = U U(ℐ,:)⁻¹ I(:,ℐ)ᵀ` of the
interpolatory projection (13) satisfies `‖𝒫‖₂ ≤ ‖U(ℐ,:)⁻¹‖₂ ≤ √N (1 + √N)^{R-1}`.  Not stated in
the paper (which only asks for "well-conditioned" `X(ℐ,:)`); a corollary of the DEIM growth
bound. -/
theorem specNorm_obliqueProj_sel_le {N R : ℕ} {U : Matrix (Fin N) (Fin R) ℝ} (hR : 0 < R)
    (hU : Uᵀ * U = 1) {I : Fin R → Fin N} (hI : IsDEIMSelection U I) :
    IsUnit ((sel I)ᵀ * U).det ∧
      specNorm (obliqueProj U (sel I)) ≤ √(N : ℝ) * (1 + √(N : ℝ)) ^ (R - 1) := by
  have hdet := det_submatrix_ne_zero_of_isDEIMSelection U (mulVec_eq_zero_of_orthonormal hU) hI
  have hunit : IsUnit (U.submatrix I id).det := isUnit_iff_ne_zero.2 hdet
  have hinj : Function.Injective I := injective_of_isUnit_det (s := id) hunit
  refine ⟨by rwa [sel_transpose_mul], ?_⟩
  refine (specNorm_obliqueProj_le_of_orthonormal hU (sel_orthonormal hinj)).trans ?_
  rw [sel_transpose_mul]
  exact specNorm_inv_le_of_isDEIMSelection hR hU hI

/-- **Robust local error of BUC with DEIM indices** (a new chain, not stated in
arXiv 2411.15990, which gives no error analysis).  Let one BUC step (eqs. (27)–(29),
`IsBUCStep`) use DEIM selections `ℐ = DEIM(X₀)`, `𝒥 = DEIM(V₀)`, `ℐ̂ = DEIM(X̂)`, `𝒥̂ = DEIM(V̂)`
(Algorithm 1) on bases with `r`, `k̂_X`, `k̂_V` columns in `ℝ^{N_x}`, `ℝ^{N_v}`, all at most `R`
columns and `N` rows.  If `F` is `L`-Lipschitz and bounded by `B`, `A` is the exact solution
from `A(t₀) = X₀ S₀ V₀ᵀ`, `0 ≤ h = t₁ - t₀ ≤ H`, and the doubly-normal components of `F` at
`K(t₁) V₀ᵀ` and `X₀ L(t₁)ᵀ` are `≤ ε`, then the (untruncated) BUC value satisfies
`‖X̂ Ŝ(t₁) V̂ᵀ - A(t₁)‖ ≤ h (C₁(η) ε + C₂(η) h)` with `η = √N (1 + √N)^{R-1}` and the constants
`ObliqueBUG.obC₁`, `ObliqueBUG.obC₂` of the library's interpolatory BUG analysis.  The constant
`η` does not depend on the singular values of the solution, only on `N` and `R` (it is,
however, exponential in `R`, which is the worst case of the DEIM growth bound). -/
theorem IsBUCStep.local_error_le_of_deim {Nx Nv r ka kb N R : ℕ}
    {F : ℝ → Matrix (Fin Nx) (Fin Nv) ℝ → Matrix (Fin Nx) (Fin Nv) ℝ} {t₀ t₁ : ℝ}
    {X₀ : Matrix (Fin Nx) (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ}
    {V₀ : Matrix (Fin Nv) (Fin r) ℝ} {Xa : Matrix (Fin Nx) (Fin ka) ℝ}
    {Va : Matrix (Fin Nv) (Fin kb) ℝ} {I : Fin r → Fin Nx} {J : Fin r → Fin Nv}
    {Ia : Fin ka → Fin Nx} {Ja : Fin kb → Fin Nv} {K : ℝ → Matrix (Fin Nx) (Fin r) ℝ}
    {Lf : ℝ → Matrix (Fin Nv) (Fin r) ℝ} {Sa : ℝ → Matrix (Fin ka) (Fin kb) ℝ}
    (hs : IsBUCStep F t₀ t₁ X₀ (sel I) S₀ V₀ (sel J) Xa (sel Ia) Va (sel Ja) K Lf Sa)
    (hI : IsDEIMSelection X₀ I) (hJ : IsDEIMSelection V₀ J) (hIa : IsDEIMSelection Xa Ia)
    (hJa : IsDEIMSelection Va Ja) (hr : 0 < r) (hka : 0 < ka) (hkb : 0 < kb) (hNx : Nx ≤ N)
    (hNv : Nv ≤ N) (hrR : r ≤ R) (hkaR : ka ≤ R) (hkbR : kb ≤ R) {L B ε h H : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hhH : h ≤ H) {A : ℝ → Matrix (Fin Nx) (Fin Nv) ℝ}
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = X₀ * S₀ * V₀ᵀ)
    (hεK : ∀ t ∈ Icc t₀ t₁, ‖(1 - Xa * Xaᵀ) * F t (K t₁ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε)
    (hεL : ∀ t ∈ Icc t₀ t₁, ‖(1 - X₀ * X₀ᵀ) * F t (X₀ * (Lf t₁)ᵀ) * (1 - Va * Vaᵀ)‖ ≤ ε) :
    ‖Xa * Sa t₁ * Vaᵀ - A t₁‖ ≤
      h * (ObliqueBUG.obC₁ (√(N : ℝ) * (1 + √(N : ℝ)) ^ (R - 1)) L H * ε +
        ObliqueBUG.obC₂ (√(N : ℝ) * (1 + √(N : ℝ)) ^ (R - 1)) L B H * h) := by
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have : Nonempty (Fin ka) := ⟨⟨0, hka⟩⟩
  have : Nonempty (Fin kb) := ⟨⟨0, hkb⟩⟩
  have : Nonempty (Fin Nx) := ⟨I ⟨0, hr⟩⟩
  have : Nonempty (Fin Nv) := ⟨J ⟨0, hr⟩⟩
  obtain ⟨hI1, hI2⟩ := specNorm_obliqueProj_sel_le hr hs.orthX₀ hI
  obtain ⟨hJ1, hJ2⟩ := specNorm_obliqueProj_sel_le hr hs.orthV₀ hJ
  obtain ⟨hIa1, hIa2⟩ := specNorm_obliqueProj_sel_le hka hs.orthXa hIa
  obtain ⟨hJa1, hJa2⟩ := specNorm_obliqueProj_sel_le hkb hs.orthVa hJa
  have hstep := hs.isObliqueBUGStep hI1 hJ1 hIa1 hJa1
    (hJ2.trans (deimConst_mono hNv hrR)) (hI2.trans (deimConst_mono hNx hrR))
    (hIa2.trans (deimConst_mono hNx hkaR)) (hJa2.trans (deimConst_mono hNv hkbR)) hεK hεL
  exact hstep.local_error_le hF hL hB ht₁ hh hhH hA hA₀

end Chain

/-! ### Non-vacuity -/

section Examples

/-- A constant trajectory solves an ODE whose field vanishes along it. -/
private lemma odeSolution_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E → E}
    {y₀ : E} (hf : ∀ t, f t y₀ = 0) (a b : ℝ) : ODESolution f (fun _ => y₀) a b where
  cont := continuousOn_const
  deriv t _ := by rw [hf]; exact hasDerivWithinAt_const t _ y₀

/-- **Non-vacuity of `IsInterpKSLStep` and `IsBUCStep`.**  For the zero field on `ℝ^{1×1}` and
all factors and test matrices equal to `1`, constant factor trajectories form one step of the
interpolatory projector-splitting integrator (21)–(23) and one BUC step (27)–(29), and the
extra hypotheses of `IsBUCStep.isObliqueBUGStep` hold with `η = 1`, `ε = 0`. -/
example :
    let F : ℝ → Matrix (Fin 1) (Fin 1) ℝ → Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => 0
    let O : Matrix (Fin 1) (Fin 1) ℝ := 1
    IsInterpKSLStep F 0 1 O O O O O O O (fun _ => O) (fun _ => O) (fun _ => O) ∧
      IsBUCStep F 0 1 O O O O O O O O O (fun _ => O) (fun _ => O) (fun _ => O) ∧
      IsUnit (Oᵀ * O).det ∧ specNorm (obliqueProj O O) ≤ 1 ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ‖(1 - O * Oᵀ) * F t (O * Oᵀ) * (1 - O * Oᵀ)‖ ≤ 0 := by
  intro F O
  have hO : Oᵀ * O = 1 := by simp [O]
  refine ⟨⟨hO, odeSolution_const (fun t => by simp [interpKField, F]) _ _, by simp [O], hO,
    by simp [O], odeSolution_const (fun t => by simp [collocField, F]) _ _, rfl,
    odeSolution_const (fun t => by simp [interpLField, F]) _ _, by simp [O]⟩,
    ⟨hO, hO, odeSolution_const (fun t => by simp [interpKField, F]) _ _, by simp [O],
    odeSolution_const (fun t => by simp [interpLField, F]) _ _, by simp [O], hO, by simp [O],
    by simp [O], hO, by simp [O], by simp [O],
    odeSolution_const (fun t => by simp [collocField, F]) _ _, by simp [O]⟩,
    by rw [hO, Matrix.det_one]; exact isUnit_one, ?_, fun t _ => by simp [F]⟩
  have hP : obliqueProj O O = 1 := by simp [obliqueProj, O]
  rw [hP]
  exact specNorm_one_le

/-- **Non-vacuity of `IsBUCStep.local_error_le_of_deim`.**  On `ℝ^{1×1}` with the zero field,
all factors `1`, the (unique) DEIM index `0` for every basis, the constant exact solution and
`ε = L = B = 0`, all hypotheses hold (the bound then reads `‖Ŷ₁ - A(t₁)‖ ≤ 0`). -/
example :
    let F : ℝ → Matrix (Fin 1) (Fin 1) ℝ → Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => 0
    let O : Matrix (Fin 1) (Fin 1) ℝ := 1
    let I : Fin 1 → Fin 1 := ![0]
    IsBUCStep F 0 1 O (P2408_16591.sel I) O O (P2408_16591.sel I) O (P2408_16591.sel I) O
      (P2408_16591.sel I) (fun _ => O) (fun _ => O) (fun _ => O) ∧ IsDEIMSelection O I ∧
      IsLipschitzField F 0 ∧ IsBoundedField F 0 ∧ ODESolution F (fun _ => O * O * Oᵀ) 0 1 ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ‖(1 - O * Oᵀ) * F t (O * Oᵀ) * (1 - O * Oᵀ)‖ ≤ 0 := by
  intro F O I
  have hO : Oᵀ * O = 1 := by simp [O]
  have hS : P2408_16591.sel I = O := by
    ext a b; fin_cases a; fin_cases b; rfl
  rw [hS]
  refine ⟨⟨hO, hO, odeSolution_const (fun t => by simp [interpKField, F]) _ _, by simp [O],
    odeSolution_const (fun t => by simp [interpLField, F]) _ _, by simp [O], hO, by simp [O],
    by simp [O], hO, by simp [O], by simp [O],
    odeSolution_const (fun t => by simp [collocField, F]) _ _, by simp [O]⟩,
    fun j => ⟨0, fun _ _ => rfl, fun i hi => ?_, fun i => ?_⟩, fun _ _ _ => by simp [F],
    fun _ _ => by simp [F], odeSolution_const (fun t => by simp [F]) _ _,
    fun t _ => by simp [F]⟩
  · fin_cases i; fin_cases j; exact absurd hi (lt_irrefl _)
  · fin_cases i; fin_cases j; simp [O, I]

end Examples

end LeanDLRA.Literature.P2411_15990
