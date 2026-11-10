import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.TuckerBUG
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.HighOrder.MidpointBUG
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Matrix.LowRankDistance
import LeanDLRA.Tensor.Defs
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Definitions for TensorNetworks Part3

Local definitions used by the theorems of the corresponding modules. On three modes the Tucker
tensor `Tensor.tucker` of the core is `tucker3` (`tucker_apply_eq_tucker3`).
-/

open Set Finset Filter Topology
open scoped RealInnerProductSpace

universe u

namespace LeanDLRA.OpenProblems.TensorNetworks

open LeanDLRA

section Tensor3

variable {n₁ n₂ n₃ r₁ r₂ r₃ : Type*} [Fintype r₁] [Fintype r₂] [Fintype r₃]

/-- The Tucker tensor `C ×₁ U₁ ×₂ U₂ ×₃ U₃`,
`(a, b, c) ↦ ∑_{i,j,k} U₁ a i U₂ b j U₃ c k C i j k`. -/
def tucker3 (C : r₁ → r₂ → r₃ → ℝ) (U₁ : Matrix n₁ r₁ ℝ) (U₂ : Matrix n₂ r₂ ℝ)
    (U₃ : Matrix n₃ r₃ ℝ) : n₁ → n₂ → n₃ → ℝ :=
  fun a b c => ∑ i, ∑ j, ∑ k, U₁ a i * U₂ b j * U₃ c k * C i j k

/-- The mode-1 matricization `Mat₁(T) ∈ ℝ^{n₁ × (n₂ n₃)}`. -/
def mat1 {n₁ n₂ n₃ : Type*} (T : n₁ → n₂ → n₃ → ℝ) : Matrix n₁ (n₂ × n₃) ℝ :=
  Matrix.of fun a bc => T a bc.1 bc.2

end Tensor3

section Tucker3

open scoped Matrix Kronecker

end Tucker3

section SStep

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end SStep

section Hierarchical

open scoped Matrix LeanDLRA.Frobenius

variable {m₁ m₂ n : Type*} [Fintype m₁] [Fintype m₂] [Fintype n]

/-- The two-level (hierarchical) low-rank matrices: `Y = U C Wᵀ` with `r` columns and every
column of `U` (a function of the two subgroups `m₁ × m₂`) itself of rank `≤ r'` across the inner
cut — a binary tree tensor network with ranks `(r, r', ·)`. -/
def hierSet (m₁ m₂ n : Type*) [Fintype m₁] [Fintype m₂] [Fintype n] (r r' : ℕ) :
    Set (Matrix (m₁ × m₂) n ℝ) :=
  {Y | ∃ (U : Matrix (m₁ × m₂) (Fin r) ℝ) (C : Matrix (Fin r) (Fin r) ℝ)
      (W : Matrix n (Fin r) ℝ), Y = U * C * Wᵀ ∧
      ∀ k, (Matrix.of fun (a : m₁) (b : m₂) => U (a, b) k).rank ≤ r'}

end Hierarchical

section Reversal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Reversal

section Equilibrium

open scoped Matrix LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

end Equilibrium

section Symmetric

open scoped Matrix

end Symmetric

section GaussSeidel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One block Gauss–Seidel sweep for `min_{y ∈ V₀ ⊕ ⋯ ⊕ V_{K-1}} ‖y - b‖_G` started at `0`:
`y_{k+1} = y_k + P k (b - y_k)` with `P k` the (`G`-orthogonal) projector onto the block `V_k`. -/
def gsIter (P : ℕ → E →L[ℝ] E) (b : E) : ℕ → E
  | 0 => 0
  | k + 1 => gsIter P b k + P k (b - gsIter P b k)

/-- Error propagation of the sweep: `e_{k+1} = (1 - P k) e_k`. -/
def gsErrIter (P : ℕ → E →L[ℝ] E) (e : E) : ℕ → E
  | 0 => e
  | k + 1 => gsErrIter P e k - P k (gsErrIter P e k)

end GaussSeidel

section Certified

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Certified

section Curvature

open scoped Matrix LeanDLRA.Frobenius

end Curvature

section RAIL

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end RAIL

section SecondOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end SecondOrder

section Conditioning

open scoped Matrix Kronecker

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The spectral condition number `‖A‖₂ ‖A⁻¹‖₂`. -/
noncomputable def condNum {k : Type*} [Fintype k] [DecidableEq k] (A : Matrix k k ℝ) : ℝ :=
  Curvature.specNorm A * Curvature.specNorm A⁻¹

end Conditioning

section Restriction

open scoped Matrix

end Restriction

section CP

/-- `T` has CP rank at most `r`: `T = ∑_{l < r} aₗ ⊗ bₗ ⊗ cₗ`. -/
def cpRankLE {n : Type*} (r : ℕ) (T : n → n → n → ℝ) : Prop :=
  ∃ a b c : Fin r → n → ℝ, T = fun i j k => ∑ l, a l i * b l j * c l k

/-- The de Silva–Lim tensor `W = e₁⊗e₁⊗e₂ + e₁⊗e₂⊗e₁ + e₂⊗e₁⊗e₁` (indices `0, 1`). -/
def wTensor : Fin 2 → Fin 2 → Fin 2 → ℝ :=
  fun i j k => if i.val + j.val + k.val = 1 then 1 else 0

/-- The rank-2 approximants `N ((a + b/N)^{⊗3} - a^{⊗3})` with `a = e₁`, `b = e₂`. -/
noncomputable def cpApprox (N : ℕ) : Fin 2 → Fin 2 → Fin 2 → ℝ :=
  fun i j k =>
    let v : Fin 2 → ℝ := fun l => if l = 0 then 1 else 1 / (N : ℝ)
    let a : Fin 2 → ℝ := fun l => if l = 0 then 1 else 0
    (N : ℝ) * (v i * v j * v k - a i * a j * a k)

end CP

section SchmidtGradient

end SchmidtGradient

section TuckerThreeModes

/-- The multi-index on three modes with the entries `i`, `j`, `k`. -/
def tripleIndex {ρ : Fin 3 → Type*} (i : ρ 0) (j : ρ 1) (k : ρ 2) : ∀ m, ρ m
  | 0 => i
  | 1 => j
  | 2 => k

/-- Multi-indices on three modes are triples. -/
def tripleIndexEquiv (ρ : Fin 3 → Type*) : ρ 0 × ρ 1 × ρ 2 ≃ ∀ m, ρ m where
  toFun p := tripleIndex p.1 p.2.1 p.2.2
  invFun y := (y 0, y 1, y 2)
  left_inv _ := rfl
  right_inv y := by
    funext m
    fin_cases m <;> rfl

/-- **Bridge to the core.** On three modes the Tucker tensor `Tensor.tucker C U` of the core is
`tucker3` of the core tensor and the three basis matrices, entry by entry. -/
theorem tucker_apply_eq_tucker3 {ι ρ : Fin 3 → Type*} [∀ m, Fintype (ρ m)] (C : Tensor ρ)
    (U : ∀ m, Matrix (ι m) (ρ m) ℝ) (x : ∀ m, ι m) :
    Tensor.tucker C U x =
      tucker3 (fun i j k => C (tripleIndex i j k)) (U 0) (U 1) (U 2) (x 0) (x 1) (x 2) := by
  calc Tensor.tucker C U x
      = ∑ y, (∏ m, U m (x m) (y m)) * C y := rfl
    _ = ∑ p : ρ 0 × ρ 1 × ρ 2, (∏ m, U m (x m) (tripleIndex p.1 p.2.1 p.2.2 m)) *
          C (tripleIndex p.1 p.2.1 p.2.2) :=
        ((tripleIndexEquiv ρ).sum_comp fun y => (∏ m, U m (x m) (y m)) * C y).symm
    _ = ∑ i, ∑ j, ∑ k, (∏ m, U m (x m) (tripleIndex i j k m)) * C (tripleIndex i j k) := by
        simp only [Fintype.sum_prod_type]
    _ = tucker3 (fun i j k => C (tripleIndex i j k)) (U 0) (U 1) (U 2) (x 0) (x 1) (x 2) := by
        simp only [Fin.prod_univ_three]
        rfl

/-- Non-vacuity of `tucker_apply_eq_tucker3` with nonzero data: for modes of size one, the core
entry `2` and the basis entries `3`, both sides are `3 * 3 * 3 * 2 = 54`. -/
example : Tensor.tucker (ι := fun _ : Fin 3 => Fin 1) (ρ := fun _ => Fin 1)
    (WithLp.toLp 2 fun _ => 2) (fun _ => Matrix.of fun _ _ => 3) (fun _ => 0) = 54 := by
  rw [tucker_apply_eq_tucker3]
  norm_num [tucker3]

end TuckerThreeModes

end LeanDLRA.OpenProblems.TensorNetworks
