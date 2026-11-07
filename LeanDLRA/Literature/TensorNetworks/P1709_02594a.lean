import LeanDLRA.Integrators.Exactness

/-!
# Results of arXiv 1709.02594: projector splitting for rank-constrained Tucker tensors

This module formalizes the mode-invariance part of the Tucker tangent-space lemma of arXiv
1709.02594 for order-three tensors. Tucker tensors are written as `C ×₁ U₁ ×₂ U₂ ×₃ U₃` on
`n₁ → n₂ → n₃ → ℝ`. The rank-`(s₁, s₂, s₃)` Tucker set consists of all such tensors with
`C : Fin s₁ → Fin s₂ → Fin s₃ → ℝ` and factor matrices `Uᵢ` with `sᵢ` columns. The theorems
`tuckerSet3_invariant_mode1`, `..._mode2` and `..._mode3` say that multiplying any single mode
by an arbitrary matrix keeps a Tucker tensor in the Tucker set. Orthogonal projectors are a special
case, so this gives the paper's invariance under mode projections, with `P` general.

Results of the paper that are **not** in this module:

* **Algorithm 1 (nested Tucker PSI)**: not formalized. It needs an iterated abstract KSL step over
  unfoldings, and the unfolding bookkeeping is absent.
* **Thm 3 (exactness)**: the `d = 2` case is already in the library as
  `LeanDLRA.Exactness.ksl_exact` (Lubich–Oseledets matrix KSL), so it is not
  duplicated here. The general-`d` statement is not formalized.
* **Thm 4 (robust error bound)**: not formalized. The abstract route would need the inexact-KSL
  local bound (`ksl_local_error_inexact`) iterated over modes. The Tucker BUG analogue is
  `tucker_global_error_le`.
* **Lemma, tangent inclusion `T_Y M ⊂ ∩ᵢ T_Y Mᵢ`**: not formalized, because the Tucker tangent space
  is not defined in this module. Only the invariance part is proved, and only for order three.
* **Thm 5 (equivalence with Lubich 2015)**: not formalized. The Kronecker identity
  `Mat₁(C ×₁ U₁ ×₂ U₂ ×₃ U₃) = U₁ Mat₁(C) (U₂ ⊗ U₃)ᵀ` is in `wip/done/TensorNetworksPart3a.lean`
  but not in the library.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P1709_02594

variable {n₁ n₂ n₃ r₁ r₂ r₃ : Type*} [Fintype n₁] [Fintype n₂] [Fintype n₃]
  [Fintype r₁] [Fintype r₂] [Fintype r₃]

/-- The Tucker tensor `C ×₁ U₁ ×₂ U₂ ×₃ U₃`, `(a, b, c) ↦ ∑ᵢⱼₖ U₁ₐᵢ U₂_bⱼ U₃_ck Cᵢⱼₖ`. -/
def tuckerTensor3 (C : r₁ → r₂ → r₃ → ℝ) (U₁ : Matrix n₁ r₁ ℝ) (U₂ : Matrix n₂ r₂ ℝ)
    (U₃ : Matrix n₃ r₃ ℝ) : n₁ → n₂ → n₃ → ℝ :=
  fun a b c => ∑ i, ∑ j, ∑ k, U₁ a i * U₂ b j * U₃ c k * C i j k

/-- The mode-one product `P ×₁ T`, `(a, b, c) ↦ ∑ₐ' P a a' T a' b c`. -/
def modeProd1 (P : Matrix n₁ n₁ ℝ) (T : n₁ → n₂ → n₃ → ℝ) : n₁ → n₂ → n₃ → ℝ :=
  fun a b c => ∑ a', P a a' * T a' b c

/-- The mode-two product `T ×₂ P`. -/
def modeProd2 (P : Matrix n₂ n₂ ℝ) (T : n₁ → n₂ → n₃ → ℝ) : n₁ → n₂ → n₃ → ℝ :=
  fun a b c => ∑ b', P b b' * T a b' c

/-- The mode-three product `T ×₃ P`. -/
def modeProd3 (P : Matrix n₃ n₃ ℝ) (T : n₁ → n₂ → n₃ → ℝ) : n₁ → n₂ → n₃ → ℝ :=
  fun a b c => ∑ c', P c c' * T a b c'

/-- The Tucker set of multilinear rank at most `(s₁, s₂, s₃)` in `n₁ → n₂ → n₃ → ℝ`: all tensors
`C ×₁ U₁ ×₂ U₂ ×₃ U₃` with core `C` of size `s₁ × s₂ × s₃` and factor matrices `Uᵢ` with `sᵢ`
columns. -/
def tuckerSet3 (s₁ s₂ s₃ : ℕ) (n₁ n₂ n₃ : Type*) [Fintype n₁] [Fintype n₂] [Fintype n₃] :
    Set (n₁ → n₂ → n₃ → ℝ) :=
  {T | ∃ (C : Fin s₁ → Fin s₂ → Fin s₃ → ℝ) (U₁ : Matrix n₁ (Fin s₁) ℝ)
      (U₂ : Matrix n₂ (Fin s₂) ℝ) (U₃ : Matrix n₃ (Fin s₃) ℝ),
      T = tuckerTensor3 C U₁ U₂ U₃}

omit [Fintype n₂] [Fintype n₃] in
/-- Mode-one multiplication of a Tucker tensor acts on the first factor: `P ×₁ T` has
factor `P U₁`. -/
private theorem modeProd1_tuckerTensor3 (C : r₁ → r₂ → r₃ → ℝ) (U₁ : Matrix n₁ r₁ ℝ)
    (U₂ : Matrix n₂ r₂ ℝ) (U₃ : Matrix n₃ r₃ ℝ) (P : Matrix n₁ n₁ ℝ) :
    modeProd1 P (tuckerTensor3 C U₁ U₂ U₃) = tuckerTensor3 C (P * U₁) U₂ U₃ := by
  funext a b c
  simp only [modeProd1, tuckerTensor3, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

omit [Fintype n₁] [Fintype n₃] in
/-- Mode-two multiplication of a Tucker tensor acts on the second factor. -/
private theorem modeProd2_tuckerTensor3 (C : r₁ → r₂ → r₃ → ℝ) (U₁ : Matrix n₁ r₁ ℝ)
    (U₂ : Matrix n₂ r₂ ℝ) (U₃ : Matrix n₃ r₃ ℝ) (P : Matrix n₂ n₂ ℝ) :
    modeProd2 P (tuckerTensor3 C U₁ U₂ U₃) = tuckerTensor3 C U₁ (P * U₂) U₃ := by
  funext a b c
  simp only [modeProd2, tuckerTensor3, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

omit [Fintype n₁] [Fintype n₂] in
/-- Mode-three multiplication of a Tucker tensor acts on the third factor. -/
private theorem modeProd3_tuckerTensor3 (C : r₁ → r₂ → r₃ → ℝ) (U₁ : Matrix n₁ r₁ ℝ)
    (U₂ : Matrix n₂ r₂ ℝ) (U₃ : Matrix n₃ r₃ ℝ) (P : Matrix n₃ n₃ ℝ) :
    modeProd3 P (tuckerTensor3 C U₁ U₂ U₃) = tuckerTensor3 C U₁ U₂ (P * U₃) := by
  funext a b c
  simp only [modeProd3, tuckerTensor3, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- **Invariance of the Tucker set under mode-one multiplication** (Lubich–Vandereycken–Walach,
arXiv 1709.02594, invariance part of the Tucker tangent-space lemma, order three). For every
rank-`(s₁, s₂, s₃)` Tucker tensor `T` and every matrix `P`, the tensor `P ×₁ T` again has
multilinear rank at most `(s₁, s₂, s₃)`. The paper's mode projections are the case of orthogonal
projectors `P`. -/
theorem tuckerSet3_invariant_mode1 {s₁ s₂ s₃ : ℕ} {T : n₁ → n₂ → n₃ → ℝ}
    (hT : T ∈ tuckerSet3 s₁ s₂ s₃ n₁ n₂ n₃) (P : Matrix n₁ n₁ ℝ) :
    modeProd1 P T ∈ tuckerSet3 s₁ s₂ s₃ n₁ n₂ n₃ := by
  obtain ⟨C, U₁, U₂, U₃, rfl⟩ := hT
  exact ⟨C, P * U₁, U₂, U₃, modeProd1_tuckerTensor3 C U₁ U₂ U₃ P⟩

/-- **Invariance of the Tucker set under mode-two multiplication** (arXiv 1709.02594, invariance
part, order three). -/
theorem tuckerSet3_invariant_mode2 {s₁ s₂ s₃ : ℕ} {T : n₁ → n₂ → n₃ → ℝ}
    (hT : T ∈ tuckerSet3 s₁ s₂ s₃ n₁ n₂ n₃) (P : Matrix n₂ n₂ ℝ) :
    modeProd2 P T ∈ tuckerSet3 s₁ s₂ s₃ n₁ n₂ n₃ := by
  obtain ⟨C, U₁, U₂, U₃, rfl⟩ := hT
  exact ⟨C, U₁, P * U₂, U₃, modeProd2_tuckerTensor3 C U₁ U₂ U₃ P⟩

/-- **Invariance of the Tucker set under mode-three multiplication** (arXiv 1709.02594, invariance
part, order three). -/
theorem tuckerSet3_invariant_mode3 {s₁ s₂ s₃ : ℕ} {T : n₁ → n₂ → n₃ → ℝ}
    (hT : T ∈ tuckerSet3 s₁ s₂ s₃ n₁ n₂ n₃) (P : Matrix n₃ n₃ ℝ) :
    modeProd3 P T ∈ tuckerSet3 s₁ s₂ s₃ n₁ n₂ n₃ := by
  obtain ⟨C, U₁, U₂, U₃, rfl⟩ := hT
  exact ⟨C, U₁, U₂, P * U₃, modeProd3_tuckerTensor3 C U₁ U₂ U₃ P⟩

/-- Non-vacuity: the zero tensor lies in the rank-`(1, 1, 1)` Tucker set on two-point index sets. -/
example : (fun _ _ _ => (0 : ℝ)) ∈ tuckerSet3 1 1 1 (Fin 2) (Fin 2) (Fin 2) :=
  ⟨fun _ _ _ => 0, 0, 0, 0, by funext a b c; simp [tuckerTensor3]⟩

end LeanDLRA.Literature.P1709_02594
