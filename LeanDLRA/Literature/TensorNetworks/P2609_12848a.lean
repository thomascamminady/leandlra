import LeanDLRA.Matrix.LowRankDistance
import LeanDLRA.Tensor.TT.AugmentedBUG
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Results of arXiv 2609.12848: Diversifying time evolution of matrix product states using BUGs

Kapás–Sulz–Verhoeven–Werner–Legeza–Lubich formulate the augmented and the midpoint BUG
integrators for matrix product states (MPS) and compare them numerically with projector-splitting
TDVP. The mathematical statements of the paper are structural; they are proved here and in the
core (`Tensor/TT/`) for real tensor trains, and through an explicit realification for the
complex Schrödinger equation.

* Eqs. (2)–(3): left/right canonical tensors give orthonormal bases:
  `Tensor.ttLeft_transpose_mul_self`, `Tensor.ttRight_transpose_mul_self`.
* §II B: augmented BUG for MPS (sweeps (6)–(10), rotation, Galerkin step, truncation (11)–(12)):
  `Tensor.IsTTAugBUGStep` (with `m = n`).
* §II B: the augmented bases contain the old bases, the rotated core is exact:
  `Tensor.IsTTAugLeftSweep.augL`, `Tensor.IsTTAugRightSweep.augR`,
  `Tensor.IsTTAugGalerkinStep.start_eq`.
* §II B: the core is a (`2M × 2M`) bond matrix in the augmented bases:
  `Tensor.IsTTAugGalerkinStep.eq_ttBond`.
* §II B: `dim α̃ = rank K̃ ≤ dim β̃ = 2 dim β`; §II C: bases of up to `4M`: `rank_augmented_le`,
  `rank_augmented_four_le`.
* footnote 2: `[A, K(t₁)]` instead of `[K(t₀), K(t₁)]`: `range_augmented_le`, `range_augmented_eq`.
* §I: BUG integrators "preserve norm and energy for unitary dynamics in the absence of truncation":
  `Tensor.IsTTAugBUGStep.norm_eq`, `Tensor.IsTTAugBUGStep.energy_eq`,
  `Tensor.IsTTMidpointBUGStep.norm_eq`, `Tensor.IsTTMidpointBUGStep.energy_eq`; complex form
  `schrodinger_augmentedGalerkin_norm_eq`, `schrodinger_augmentedGalerkin_energy_eq`.
* §I: single-site PS-TDVP preserves norm and energy: `Tensor.IsTTKSLStep.norm_eq`,
  `Tensor.IsTTKSLStep.energy_eq`.
* §II B: no truncation for the first `m < log M / log d` sites: `distLR_unfold_eq_zero_of_lt_log`,
  `distLR_unfold_tensor_eq_zero_of_pow_le`, `distLR_unfold_tensor_eq_zero_of_pow_le_right`.

Differences from the paper. Tensor trains are real; the complex Schrödinger equation enters
through the realification bridge `realify_schrodinger_inner_self` (for a complex Hilbert space
with its real inner product `Re⟪·,·⟫`, the field `-i H` with Hermitian `H` satisfies
`Re⟪-i H x, x⟫ = 0`, and `J = -i` is skew and commutes with complex-linear projectors), which
turns the abstract conservation theorems of the augmented Galerkin step into the complex
statements; the complex MPS projectors themselves are not formalized. For the real TT step,
energy conservation carries the commutation of `J` with the Galerkin projector as a hypothesis.
The midpoint integrator enters only through its Galerkin step (`Tensor.IsTTMidpointBUGStep`); its
second order, the FLOP counts and all numerical results (§III) are not formalized. In footnote 2
the two augmentations give the same spaces when the old core `C` is invertible
(`range_augmented_eq`); in general only the inclusion `range_augmented_le` holds. The bond
dimension near the chain ends is the rank of the unfolding at the cut (`Tensor.unfold`); the local
`unfold` of the earlier formalization (with `Fin.append`) has the same rank
(`rank_unfold_eq_rank_tensor_unfold`). Core definitions used: `Tensor`, `Tensor.unfold`,
`Tensor.IsTTAugBUGStep`, `IsAugmentedGalerkinStep`, `distLR`. Local definition: `unfold`.
-/

open Set Filter Topology Finset
open scoped Matrix LeanDLRA.Frobenius RealInnerProductSpace ComplexConjugate

namespace LeanDLRA.Literature.P2609_12848

/-- The unfolding of a chain `ψ` of `k + l` sites across the cut after the first `k` sites: the
row index runs over the left sites, the column index over the right sites. -/
def unfold {d k l : ℕ} (ψ : (Fin (k + l) → Fin d) → ℝ) : Matrix (Fin k → Fin d) (Fin l → Fin d) ℝ :=
  Matrix.of fun a b => ψ (Fin.append a b)

/-- Bond dimension at the cut after the first `k` sites is at most `d ^ k`, the number of
left configurations (arXiv 2609.12848, Secs. II A–B). -/
theorem rank_unfold_le_left {d k l : ℕ} (ψ : (Fin (k + l) → Fin d) → ℝ) :
    (unfold ψ).rank ≤ d ^ k := by
  refine (Matrix.rank_le_card_height _).trans ?_
  simp

/-- Bond dimension at the cut after the first `k` sites is at most `d ^ l`, the number of right
configurations. -/
theorem rank_unfold_le_right {d k l : ℕ} (ψ : (Fin (k + l) → Fin d) → ℝ) :
    (unfold ψ).rank ≤ d ^ l := by
  refine (Matrix.rank_le_card_width _).trans ?_
  simp

/-- The bond dimension is at most the smaller of the two mode products. -/
theorem rank_unfold_le_min {d k l : ℕ} (ψ : (Fin (k + l) → Fin d) → ℝ) :
    (unfold ψ).rank ≤ min (d ^ k) (d ^ l) :=
  le_min (rank_unfold_le_left ψ) (rank_unfold_le_right ψ)

/-- Near the chain end, with bond cap `M` and `d ^ m ≤ M`, the bond dimension across the cut after
`m` sites is at most `M`, so the truncation to bond dimension `M` has zero error: no truncation
occurs (arXiv 2609.12848, Secs. II A–B). -/
theorem distLR_unfold_eq_zero_of_pow_le {d m l M : ℕ} (ψ : (Fin (m + l) → Fin d) → ℝ)
    (hdM : d ^ m ≤ M) : LeanDLRA.distLR M (unfold ψ) = 0 :=
  LeanDLRA.distLR_eq_zero_of_rank_le ((rank_unfold_le_left ψ).trans hdM)

/-- The paper's range: for `m < log M / log d` (with `2 ≤ d` and `0 < M`) the first `m` sites carry
bond dimension at most `d ^ m < M`, so no truncation occurs there. -/
theorem distLR_unfold_eq_zero_of_lt_log {d m l M : ℕ} (ψ : (Fin (m + l) → Fin d) → ℝ)
    (hd : 2 ≤ d) (hM : 0 < M) (hm : (m : ℝ) < Real.log M / Real.log d) :
    LeanDLRA.distLR M (unfold ψ) = 0 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hlogd : 0 < Real.log d := Real.log_pos (by exact_mod_cast (by omega : 1 < d))
  have h1 : (m : ℝ) * Real.log d < Real.log M := by
    rwa [lt_div_iff₀ hlogd] at hm
  have h2 : Real.log ((d : ℝ) ^ m) < Real.log M := by
    rw [Real.log_pow]; exact h1
  have hpos : (0 : ℝ) < (d : ℝ) ^ m := pow_pos hd' m
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have h3 : (d : ℝ) ^ m < M := (Real.log_lt_log_iff hpos hMpos).1 h2
  have h4 : d ^ m ≤ M := by exact_mod_cast h3.le
  exact distLR_unfold_eq_zero_of_pow_le ψ h4

/-- Non-vacuity: `d = 2`, `M = 8`, `m = 2` satisfies `m < log M / log d` (since
`log 8 / log 2 = 3`), so the no-truncation statement applies to the chain with `m = 2` left sites
and `l = 3` right sites. -/
example (ψ : (Fin (2 + 3) → Fin 2) → ℝ) : LeanDLRA.distLR 8 (unfold ψ) = 0 := by
  apply distLR_unfold_eq_zero_of_lt_log ψ (by norm_num) (by norm_num)
  have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  norm_num only [Nat.cast_ofNat]
  rw [h8, lt_div_iff₀ hlog2]
  linarith

/-! ### Bond dimensions near the chain ends, for core tensors -/

section CoreTensor

/-- The first `k` of `N` sites. -/
private def leftSites {N : ℕ} (k : ℕ) (hk : k ≤ N) : {i : Fin N // i.val < k} ≃ Fin k where
  toFun i := ⟨i.1.val, i.2⟩
  invFun j := ⟨⟨j.val, by omega⟩, j.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The last `N - k` of `N` sites. -/
private def rightSites {N : ℕ} (k : ℕ) (hk : k ≤ N) :
    {i : Fin N // ¬ i.val < k} ≃ Fin (N - k) where
  toFun i := ⟨i.1.val - k, by have := i.1.2; omega⟩
  invFun j := ⟨⟨k + j.val, by omega⟩, by simp⟩
  left_inv i := Subtype.ext (Fin.ext (by have := i.2; simp; omega))
  right_inv j := Fin.ext (by simp)

/-- **Bond dimension near the left end** (arXiv 2609.12848, §II B): for an MPS on `N` sites with
local dimension `d`, the rank of the unfolding at the cut after `k` sites is at most `d ^ k`. -/
theorem rank_unfold_le_pow_left {N d : ℕ} (X : Tensor (fun _ : Fin N => Fin d)) {k : ℕ}
    (hk : k ≤ N) : (Tensor.unfold (fun i : Fin N => i.val < k) X).rank ≤ d ^ k := by
  refine (Matrix.rank_le_card_height _).trans (le_of_eq ?_)
  simp only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fintype.card_congr (leftSites k hk)]

/-- **Bond dimension near the right end**: the rank of the unfolding at the cut after `k` sites
is at most `d ^ (N - k)`. -/
theorem rank_unfold_le_pow_right {N d : ℕ} (X : Tensor (fun _ : Fin N => Fin d)) {k : ℕ}
    (hk : k ≤ N) : (Tensor.unfold (fun i : Fin N => i.val < k) X).rank ≤ d ^ (N - k) := by
  refine (Matrix.rank_le_card_width _).trans (le_of_eq ?_)
  simp only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fintype.card_congr (rightSites k hk)]

/-- **No truncation near the left end** (arXiv 2609.12848, §II B): if `d ^ k ≤ M`, truncating the
unfolding at the cut after `k` sites to bond dimension `M` changes nothing. -/
theorem distLR_unfold_tensor_eq_zero_of_pow_le {N d : ℕ} (X : Tensor (fun _ : Fin N => Fin d))
    {k M : ℕ} (hk : k ≤ N) (hdM : d ^ k ≤ M) :
    distLR M (Tensor.unfold (fun i : Fin N => i.val < k) X) = 0 :=
  distLR_eq_zero_of_rank_le ((rank_unfold_le_pow_left X hk).trans hdM)

/-- **No truncation near the right end** (the mirrored statement of arXiv 2609.12848, §II B). -/
theorem distLR_unfold_tensor_eq_zero_of_pow_le_right {N d : ℕ}
    (X : Tensor (fun _ : Fin N => Fin d)) {k M : ℕ} (hk : k ≤ N) (hdM : d ^ (N - k) ≤ M) :
    distLR M (Tensor.unfold (fun i : Fin N => i.val < k) X) = 0 :=
  distLR_eq_zero_of_rank_le ((rank_unfold_le_pow_right X hk).trans hdM)

/-- **Bridge to the core unfolding**: the local unfolding of a chain of `k + l` sites (with
`Fin.append`) has the same rank as the core unfolding `Tensor.unfold` at the cut after `k`
sites. -/
theorem rank_unfold_eq_rank_tensor_unfold {d k l : ℕ} (ψ : (Fin (k + l) → Fin d) → ℝ) :
    (unfold ψ).rank =
      (Tensor.unfold (fun i : Fin (k + l) => i.val < k)
        (WithLp.toLp 2 ψ : Tensor (fun _ : Fin (k + l) => Fin d))).rank := by
  have hM : Tensor.unfold (fun i : Fin (k + l) => i.val < k)
      (WithLp.toLp 2 ψ : Tensor (fun _ : Fin (k + l) => Fin d)) =
      (unfold ψ).submatrix
        (Equiv.arrowCongr (leftSites k (Nat.le_add_right k l)) (Equiv.refl (Fin d)))
        (Equiv.arrowCongr ((rightSites k (Nat.le_add_right k l)).trans (finCongr (by omega)))
          (Equiv.refl (Fin d))) := by
    ext a b
    simp only [Matrix.submatrix_apply, unfold, Matrix.of_apply, Tensor.unfold_apply]
    congr 1
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have hj : (Fin.castAdd l j).val < k := j.2
      rw [Fin.append_left, Tensor.merge, dite_eq_left_of_eq_true (eq_true hj)]
      rfl
    · have hj : ¬ (Fin.natAdd k j).val < k := by simp
      rw [Fin.append_right, Tensor.merge, dite_eq_right_of_eq_false (eq_false hj)]
      rfl
  rw [hM, Matrix.rank_submatrix]

end CoreTensor

/-! ### Augmented bases -/

section Augmented

variable {m r : Type*} [Fintype r]

/-- arXiv 2609.12848, §II B, after Eq. (8): the augmented matrix `K̃ = [K(t₀), K(t₁)]` has rank
at most `2 dim β`, so the new bond dimension `dim α̃ = rank K̃` is at most `dim β̃ = 2 dim β`. -/
theorem rank_augmented_le (K₀ K₁ : Matrix m r ℝ) :
    (Matrix.fromCols K₀ K₁).rank ≤ 2 * Fintype.card r := by
  have h := (Matrix.fromCols K₀ K₁).rank_le_card_width
  simp only [Fintype.card_sum] at h
  omega

/-- arXiv 2609.12848, §II C, step (ii): the bases of the midpoint integrator, built from four
blocks of bond dimension `M`, have dimension at most `4 M`. -/
theorem rank_augmented_four_le (K₀ K₁ K₂ K₃ : Matrix m r ℝ) :
    (Matrix.fromCols (Matrix.fromCols K₀ K₁) (Matrix.fromCols K₂ K₃)).rank ≤
      4 * Fintype.card r := by
  have h := (Matrix.fromCols (Matrix.fromCols K₀ K₁) (Matrix.fromCols K₂ K₃)).rank_le_card_width
  simp only [Fintype.card_sum] at h
  omega

/-- arXiv 2609.12848, footnote 2, inclusion: the augmentation `[K(t₀), K(t₁)]` with
`K(t₀) = A C` spans a subspace of the span of the augmentation `[A, K(t₁)]` of Ref. [51]. -/
theorem range_augmented_le {s : Type*} [Fintype s] (A : Matrix m s ℝ) (C : Matrix s r ℝ)
    (K₁ : Matrix m r ℝ) :
    LinearMap.range (A * C).mulVecLin ⊔ LinearMap.range K₁.mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range K₁.mulVecLin := by
  refine sup_le_sup_right ?_ _
  rw [Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _

/-- arXiv 2609.12848, footnote 2, equality: if the old core `C` is invertible, the two
augmentations span the same space ("our choice results in the same augmented spaces"). For a
singular core only `range_augmented_le` holds. -/
theorem range_augmented_eq [DecidableEq r] (A : Matrix m r ℝ) {C : Matrix r r ℝ}
    (hC : IsUnit C.det) (K₁ : Matrix m r ℝ) :
    LinearMap.range (A * C).mulVecLin ⊔ LinearMap.range K₁.mulVecLin =
      LinearMap.range A.mulVecLin ⊔ LinearMap.range K₁.mulVecLin := by
  refine le_antisymm (range_augmented_le A C K₁) (sup_le_sup_right ?_ _)
  have hA : A = A * C * C⁻¹ := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv C hC, Matrix.mul_one]
  calc LinearMap.range A.mulVecLin = LinearMap.range (A * C * C⁻¹).mulVecLin := by rw [← hA]
    _ = LinearMap.range ((A * C).mulVecLin ∘ₗ C⁻¹.mulVecLin) := by
      rw [Matrix.mulVecLin_mul (A * C) C⁻¹]
    _ ≤ LinearMap.range (A * C).mulVecLin := LinearMap.range_comp_le_range _ _

end Augmented

/-! ### Unitary dynamics: the realification bridge -/

section Realification

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [InnerProductSpace ℝ E]

/-- **Realification of the Schrödinger field.** On a complex Hilbert space whose real inner
product is `Re⟪·,·⟫` (`hre`), the Schrödinger field `x ↦ -i H x` with a Hermitian `H` satisfies
`⟪-i H x, x⟫ = 0`: unitary dynamics is skew in the real inner product. -/
theorem realify_schrodinger_inner_self
    (hre : ∀ x y : E, ⟪x, y⟫ = (inner ℂ x y).re) {H : E → E}
    (hH : ∀ x y, inner ℂ (H x) y = inner ℂ x (H y)) (x : E) :
    ⟪-(Complex.I • H x), x⟫ = 0 := by
  have hreal : (inner ℂ (H x) x).im = 0 := by
    have h1 : conj (inner ℂ (H x) x) = inner ℂ (H x) x := by
      rw [inner_conj_symm, ← hH]
    exact Complex.conj_eq_iff_im.1 h1
  rw [hre, inner_neg_left, inner_smul_left, Complex.neg_re, Complex.mul_re, Complex.conj_I]
  simp [hreal]

/-- **Norm conservation of an augmented Galerkin step for the Schrödinger equation** (arXiv
2609.12848, §I, for complex states through the realification): for `F(t, x) = -i H(t) x` with
Hermitian `H(t)`, every augmented Galerkin step (any real orthogonal Galerkin projector containing
`Y₀`, e.g. the realified complex MPS-BUG projector) conserves the norm before the truncation, and
changes it by at most `ϑ` with the truncation. -/
theorem schrodinger_augmentedGalerkin_norm_eq
    (hre : ∀ x y : E, ⟪x, y⟫ = (inner ℂ x y).re) {H : ℝ → E → E}
    (hH : ∀ t x y, inner ℂ (H t x) y = inner ℂ x (H t y)) {ϑ t₀ t₁ : ℝ} {R : E →L[ℝ] E}
    {Y₀ Y₁ : E} {YS : ℝ → E}
    (hs : IsAugmentedGalerkinStep (fun t x => -(Complex.I • H t x)) ϑ R t₀ t₁ Y₀ YS Y₁)
    (h01 : t₀ ≤ t₁) : ‖YS t₁‖ = ‖Y₀‖ ∧ |‖Y₁‖ - ‖Y₀‖| ≤ ϑ :=
  hs.abs_norm_sub_le h01 fun t x _ => realify_schrodinger_inner_self hre (hH t) x

/-- **Energy conservation of an augmented Galerkin step for the Schrödinger equation** (arXiv
2609.12848, §I, through the realification): for `F(x) = J (g x)` with the realified `J = -i`
(given as a real-linear map with `J z = -(i z)`), a Galerkin projector `R` commuting with `J`
(e.g. a complex-linear projector) and an energy `ℰ` with gradient `g`, the energy is conserved
before the truncation and changes by at most `β ϑ` with it. -/
theorem schrodinger_augmentedGalerkin_energy_eq
    (hre : ∀ x y : E, ⟪x, y⟫ = (inner ℂ x y).re) {J : E →L[ℝ] E}
    (hJdef : ∀ z, J z = -(Complex.I • z)) {ϑ t₀ t₁ : ℝ} {R : E →L[ℝ] E}
    (hJR : ∀ z, J (R z) = R (J z)) {g : E → E} {ℰ : E → ℝ}
    (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x) {Y₀ Y₁ : E} {YS : ℝ → E}
    (hs : IsAugmentedGalerkinStep (fun _ x => J (g x)) ϑ R t₀ t₁ Y₀ YS Y₁) (h01 : t₀ ≤ t₁)
    {β : ℝ} (hβ : ∀ w ∈ segment ℝ (YS t₁) Y₁, ‖g w‖ ≤ β) :
    ℰ (YS t₁) = ℰ Y₀ ∧ |ℰ Y₁ - ℰ Y₀| ≤ β * ϑ :=
  hs.energy_sub_le_of_skew h01 hℰ
    (fun z => by rw [hJdef]; exact realify_schrodinger_inner_self hre (H := id) (fun _ _ => rfl) z)
    hJR (fun _ _ => rfl) hβ

/-- Non-vacuity of the realification hypothesis: on `ℂ`, the real inner product is the real part
of the complex one. -/
example : ∀ x y : ℂ, ⟪x, y⟫ = (inner ℂ x y).re := fun x y => by
  simp [Complex.inner, mul_comm]

end Realification

end LeanDLRA.Literature.P2609_12848
