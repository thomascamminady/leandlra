import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2503.04932: 3d-RAIL low-rank IMEX for convection-diffusion

This module formalizes **Theorem 3.2** (unconditional stability before truncation) of
arXiv 2503.04932, for the diffusion part of the first-order implicit scheme. Tensors are
`Tens p q r := Fin p → Fin q → Fin r → ℝ`, with the Frobenius norm `frob2` (squared) and the
mode products `mode1`, `mode2`, `mode3` of the paper. The Kronecker sum `kronSum` is the
diffusion operator `F_x ×₁ + F_y ×₂ + F_z ×₃` of the paper's G-step (3.18), whose reduced
version uses the bases `Ṽ` through `reduce`.

**Proved (Theorem 3.2, diffusion part).** If `F_x, F_y, F_z` are symmetric negative
semidefinite, `Ṽ` (new) and `V` (old) have orthonormal columns, `h ≥ 0`, and `G^{n+1}` solves
`(I − h·Kronecker sum of ṼᵀF Ṽ) G^{n+1} = B` with `B = G^n ×₁ (ṼₓᵀVₓ) ×₂ (ṼᵧᵀVᵧ) ×₃ (Ṽ_zᵀV_z)`
as in (3.19), then `‖G^{n+1}‖_F ≤ ‖G^n‖_F` (`rail3d_first_order_diffusion_stable`). The printed
statement is `‖Ĝ^{n+1}‖_F ≤ ‖Ĝ^n‖_F` for the cores before truncation; without truncation the core
`G^n` of the previous step is `Ĝ^n`.

**Differences from the paper.**
* The explicit convection terms and the source terms of (3.8), (3.18) and (3.19) are not
  included. The printed statement names "the first-order implicit RAIL-3D scheme"; its proof
  works with the update `Ĝ^{n+1} ×₁ (I − A) − Ĝ^{n+1} ×₂ B − Ĝ^{n+1} ×₃ C = Ĝ^n`, which has no
  convection or source terms. This module proves the bound for that diffusion step only and
  says nothing about the scheme with those terms.
* The right-hand side keeps the overlap matrices `ṼᵀV` of (3.19) (the paper's proof writes the
  right-hand side as `Ĝ^n`); they are contractions, which the proof uses.
* The time step is `h ≥ 0` (the paper leaves the sign of `Δt` implicit).
* Symmetry of `F` is part of the hypothesis `IsNegSemidef`; the proof uses only the quadratic
  form `⟪Fv, v⟫ ≤ 0`.
* The reduced augmentation and QR construction of `Ṽ` are not modelled. Only the property
  used by the proof is assumed: `Ṽ` has orthonormal columns.

**Left out.**
* Theorem 2.1 (truncated HOSVD quasi-optimality, cited from [15, 43]): not formalized. It needs
  mode-`n` unfoldings and Eckart–Young for each unfolding, which are not built here.
* Corollary A.1 (direct solver for the Kronecker-structured core equation via a Schur
  decomposition and Sylvester solves, extending Theorem 2.1 of [74]): not formalized.
* The K-steps, the high-order IMEX-RK scheme, the truncation and the LoMaC procedure: not
  formalized.

**Core definitions reused.** The file does not use the core `IsOrthProj`, `IsBUGStep` or
`IsLipschitzField`: the tensor objects of the paper have no core counterpart. The Galerkin
norm argument is the same as the abstract dissipative Galerkin lemma in
`LeanDLRA/Foundations/OneSided.lean`, reproved here for the tensor step.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2503_04932

/-- A real `p × q × r` tensor, stored as a function of its three indices. -/
abbrev Tens (p q r : ℕ) := Fin p → Fin q → Fin r → ℝ

/-- Squared Frobenius norm of a tensor. -/
def frob2 {p q r : ℕ} (G : Tens p q r) : ℝ := ∑ i, ∑ j, ∑ k, G i j k ^ 2

/-- Mode-1 product `G ×₁ A`, `(G ×₁ A)ᵢⱼₖ = ∑ᵢ' Aᵢᵢ' Gᵢ'ⱼₖ`. -/
def mode1 {p p' q r : ℕ} (A : Matrix (Fin p) (Fin p') ℝ) (G : Tens p' q r) : Tens p q r :=
  fun i j k => ∑ i', A i i' * G i' j k

/-- Mode-2 product `G ×₂ A`. -/
def mode2 {p q q' r : ℕ} (A : Matrix (Fin q) (Fin q') ℝ) (G : Tens p q' r) : Tens p q r :=
  fun i j k => ∑ j', A j j' * G i j' k

/-- Mode-3 product `G ×₃ A`. -/
def mode3 {p q r r' : ℕ} (A : Matrix (Fin r) (Fin r') ℝ) (G : Tens p q r') : Tens p q r :=
  fun i j k => ∑ k', A k k' * G i j k'

/-- The diffusion operator `F_x ×₁ + F_y ×₂ + F_z ×₃` (Kronecker sum) of the G-step (3.18). -/
def kronSum {p q r : ℕ} (Fx : Matrix (Fin p) (Fin p) ℝ) (Fy : Matrix (Fin q) (Fin q) ℝ)
    (Fz : Matrix (Fin r) (Fin r) ℝ) (G : Tens p q r) : Tens p q r :=
  fun i j k => mode1 Fx G i j k + mode2 Fy G i j k + mode3 Fz G i j k

/-- A symmetric negative semidefinite matrix: symmetric and `xᵀ F x ≤ 0` for all `x`. -/
def IsNegSemidef {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Fᵀ = F ∧ ∀ x : Fin n → ℝ, ∑ i, ∑ j, x i * F i j * x j ≤ 0

/-- The columns of `V` are orthonormal: `Vᵀ V = I`. -/
def IsOrthonormalCols {N s : ℕ} (V : Matrix (Fin N) (Fin s) ℝ) : Prop :=
  ∀ a b, ∑ n, V n a * V n b = if a = b then 1 else 0

/-- The reduced operator `Vᵀ F V` of a basis `V` (the paper's `Ṽᵀ F Ṽ`). -/
def reduce {N s : ℕ} (V : Matrix (Fin N) (Fin s) ℝ) (F : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin s) (Fin s) ℝ :=
  fun a b => ∑ n, ∑ m, V n a * F n m * V m b

/-- The overlap matrix `Wᵀ V` between two bases (the paper's `Ṽᵀ Vⁿ`). -/
def crossProd {N s t : ℕ} (W : Matrix (Fin N) (Fin s) ℝ) (V : Matrix (Fin N) (Fin t) ℝ) :
    Matrix (Fin s) (Fin t) ℝ :=
  fun a i => ∑ n, W n a * V n i

/-- A matrix `A` is a contraction: `‖A x‖ ≤ ‖x‖` for all `x`. -/
def IsContraction {p p' : ℕ} (A : Matrix (Fin p) (Fin p') ℝ) : Prop :=
  ∀ x : Fin p' → ℝ, ∑ i, (∑ i', A i i' * x i') ^ 2 ≤ ∑ i', x i' ^ 2

/-! ### Reordering finite sums -/

lemma sum_ijk_eq_jki {p q r : ℕ} (f : Fin p → Fin q → Fin r → ℝ) :
    ∑ i, ∑ j, ∑ k, f i j k = ∑ j, ∑ k, ∑ i, f i j k := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_comm

lemma sum_ijk_eq_ikj {p q r : ℕ} (f : Fin p → Fin q → Fin r → ℝ) :
    ∑ i, ∑ j, ∑ k, f i j k = ∑ i, ∑ k, ∑ j, f i j k :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_comm

lemma sum4_swap {A B C D : ℕ} (f : Fin A → Fin B → Fin C → Fin D → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
        refine Finset.sum_congr rfl fun c _ => ?_
        calc ∑ a, ∑ b, ∑ d, f a b c d = ∑ a, ∑ d, ∑ b, f a b c d :=
              Finset.sum_congr rfl fun a _ => Finset.sum_comm
          _ = ∑ d, ∑ a, ∑ b, f a b c d := Finset.sum_comm

/-! ### Quadratic forms of the diffusion operator -/

lemma mode1_ip_le {p q r : ℕ} {A : Matrix (Fin p) (Fin p) ℝ} (hA : IsNegSemidef A)
    (G : Tens p q r) : ∑ i, ∑ j, ∑ k, G i j k * mode1 A G i j k ≤ 0 := by
  rw [sum_ijk_eq_jki]
  refine Finset.sum_nonpos fun j _ => Finset.sum_nonpos fun k _ => ?_
  calc ∑ i, G i j k * mode1 A G i j k
        = ∑ i, ∑ i', (fun i => G i j k) i * A i i' * (fun i => G i j k) i' := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [mode1, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i' _ => by ring
    _ ≤ 0 := hA.2 (fun i => G i j k)

lemma mode2_ip_le {p q r : ℕ} {A : Matrix (Fin q) (Fin q) ℝ} (hA : IsNegSemidef A)
    (G : Tens p q r) : ∑ i, ∑ j, ∑ k, G i j k * mode2 A G i j k ≤ 0 := by
  rw [sum_ijk_eq_ikj]
  refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun k _ => ?_
  calc ∑ j, G i j k * mode2 A G i j k
        = ∑ j, ∑ j', (fun j => G i j k) j * A j j' * (fun j => G i j k) j' := by
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [mode2, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j' _ => by ring
    _ ≤ 0 := hA.2 (fun j => G i j k)

lemma mode3_ip_le {p q r : ℕ} {A : Matrix (Fin r) (Fin r) ℝ} (hA : IsNegSemidef A)
    (G : Tens p q r) : ∑ i, ∑ j, ∑ k, G i j k * mode3 A G i j k ≤ 0 := by
  refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j _ => ?_
  calc ∑ k, G i j k * mode3 A G i j k
        = ∑ k, ∑ k', (fun k => G i j k) k * A k k' * (fun k => G i j k) k' := by
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [mode3, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k' _ => by ring
    _ ≤ 0 := hA.2 (fun k => G i j k)

/-- The diffusion operator is dissipative: `⟪G, (F_x ⊕ F_y ⊕ F_z) G⟫ ≤ 0` when each `F` is
symmetric negative semidefinite. -/
lemma ip_kronSum_le {p q r : ℕ} {Fx : Matrix (Fin p) (Fin p) ℝ} {Fy : Matrix (Fin q) (Fin q) ℝ}
    {Fz : Matrix (Fin r) (Fin r) ℝ} (hx : IsNegSemidef Fx) (hy : IsNegSemidef Fy)
    (hz : IsNegSemidef Fz) (G : Tens p q r) :
    ∑ i, ∑ j, ∑ k, G i j k * kronSum Fx Fy Fz G i j k ≤ 0 := by
  have e : ∀ i j k, G i j k * kronSum Fx Fy Fz G i j k
      = G i j k * mode1 Fx G i j k + G i j k * mode2 Fy G i j k
        + G i j k * mode3 Fz G i j k := by
    intro i j k
    simp only [kronSum]
    ring
  simp only [e, Finset.sum_add_distrib]
  linarith [mode1_ip_le hx G, mode2_ip_le hy G, mode3_ip_le hz G]

/-- The reduced operator `Vᵀ F V` of a symmetric negative semidefinite `F` is again symmetric
negative semidefinite (this is what makes the reduced G-step dissipative). -/
lemma reduce_nsd {N s : ℕ} {F : Matrix (Fin N) (Fin N) ℝ} (hF : IsNegSemidef F)
    (V : Matrix (Fin N) (Fin s) ℝ) : IsNegSemidef (reduce V F) := by
  have hs : ∀ n m, F m n = F n m := fun n m => by
    have := congrFun (congrFun hF.1 n) m
    simpa using this
  refine ⟨?_, ?_⟩
  · ext a b
    simp only [reduce, Matrix.transpose_apply]
    calc ∑ n, ∑ m, V n b * F n m * V m a = ∑ n, ∑ m, V n b * F m n * V m a :=
          Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => by rw [hs]
      _ = ∑ m, ∑ n, V n b * F m n * V m a := Finset.sum_comm
      _ = ∑ n, ∑ m, V n a * F n m * V m b :=
          Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => by ring
  · intro x
    have key : ∀ a b, x a * reduce V F a b * x b
        = ∑ n, ∑ m, (V n a * x a) * F n m * (V m b * x b) := by
      intro a b
      simp only [reduce, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => by ring
    have e2 : ∑ n, ∑ m, (∑ a, V n a * x a) * F n m * (∑ b, V m b * x b)
        = ∑ n, ∑ m, ∑ a, ∑ b, (V n a * x a) * F n m * (V m b * x b) := by
      refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
      simp only [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm
    calc ∑ a, ∑ b, x a * reduce V F a b * x b
        = ∑ a, ∑ b, ∑ n, ∑ m, (V n a * x a) * F n m * (V m b * x b) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => key a b
      _ = ∑ n, ∑ m, ∑ a, ∑ b, (V n a * x a) * F n m * (V m b * x b) :=
          sum4_swap (fun a b n m => (V n a * x a) * F n m * (V m b * x b))
      _ = ∑ n, ∑ m, (∑ a, V n a * x a) * F n m * (∑ b, V m b * x b) := e2.symm
      _ ≤ 0 := hF.2 (fun n => ∑ a, V n a * x a)

/-! ### Orthonormal bases are contractions -/

/-- Projection onto orthonormal columns is a contraction: `‖Wᵀ y‖ ≤ ‖y‖`. -/
lemma proj_contract {N s : ℕ} {W : Matrix (Fin N) (Fin s) ℝ} (hW : IsOrthonormalCols W)
    (y : Fin N → ℝ) : ∑ a, (∑ n, W n a * y n) ^ 2 ≤ ∑ n, y n ^ 2 := by
  obtain ⟨z, hz⟩ : ∃ z : Fin s → ℝ, ∀ a, z a = ∑ n, W n a * y n := ⟨_, fun a => rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : Fin N → ℝ, ∀ n, w n = ∑ a, W n a * z a := ⟨_, fun n => rfl⟩
  have hww : ∑ n, w n ^ 2 = ∑ a, z a ^ 2 := by
    calc ∑ n, w n ^ 2 = ∑ n, ∑ a, ∑ b, z a * z b * (W n a * W n b) := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [hw n, sq, Finset.sum_mul_sum]
          exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
      _ = ∑ a, ∑ n, ∑ b, z a * z b * (W n a * W n b) := Finset.sum_comm
      _ = ∑ a, ∑ b, ∑ n, z a * z b * (W n a * W n b) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ a, ∑ b, z a * z b * (if a = b then 1 else 0) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
            rw [← hW a b, Finset.mul_sum]
      _ = ∑ a, z a ^ 2 := Finset.sum_congr rfl fun a _ => by simp [sq]
  have hdot : ∑ n, y n * w n = ∑ a, z a ^ 2 := by
    calc ∑ n, y n * w n = ∑ n, ∑ a, y n * (W n a * z a) :=
          Finset.sum_congr rfl fun n _ => by
            rw [hw n, Finset.mul_sum]
      _ = ∑ a, ∑ n, y n * (W n a * z a) := Finset.sum_comm
      _ = ∑ a, z a * z a := Finset.sum_congr rfl fun a _ => by
          have h1 : ∑ n, y n * (W n a * z a) = z a * ∑ n, W n a * y n := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun n _ => by ring
          rw [h1, ← hz a]
      _ = ∑ a, z a ^ 2 := Finset.sum_congr rfl fun a _ => by ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ y w
  rw [hdot, hww] at hcs
  have hS0 : 0 ≤ ∑ a, z a ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
  have hgoal : ∑ a, (∑ n, W n a * y n) ^ 2 = ∑ a, z a ^ 2 :=
    Finset.sum_congr rfl fun a _ => by rw [hz a]
  rw [hgoal]
  have hY : 0 ≤ ∑ n, y n ^ 2 := Finset.sum_nonneg fun n _ => sq_nonneg _
  nlinarith [hS0, hY, hcs]

/-- The overlap `Wᵀ V` of two orthonormal bases is a contraction. -/
lemma crossProd_contraction {N s t : ℕ} {W : Matrix (Fin N) (Fin s) ℝ}
    {V : Matrix (Fin N) (Fin t) ℝ} (hW : IsOrthonormalCols W) (hV : IsOrthonormalCols V) :
    IsContraction (crossProd W V) := by
  intro x
  have hy : ∀ a, ∑ i, crossProd W V a i * x i = ∑ n, W n a * (∑ i, V n i * x i) := by
    intro a
    simp only [crossProd, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun i _ => by ring
  have hnorm : ∑ n, (∑ i, V n i * x i) ^ 2 = ∑ i, x i ^ 2 := by
    calc ∑ n, (∑ i, V n i * x i) ^ 2 = ∑ n, ∑ i, ∑ j, x i * x j * (V n i * V n j) := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [sq, Finset.sum_mul_sum]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ i, ∑ n, ∑ j, x i * x j * (V n i * V n j) := Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ n, x i * x j * (V n i * V n j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i, ∑ j, x i * x j * (if i = j then 1 else 0) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
            rw [← hV i j, Finset.mul_sum]
      _ = ∑ i, x i ^ 2 := Finset.sum_congr rfl fun i _ => by simp [sq]
  have h1 := proj_contract hW (fun n => ∑ i, V n i * x i)
  calc ∑ a, (∑ i, crossProd W V a i * x i) ^ 2
      = ∑ a, (∑ n, W n a * (∑ i, V n i * x i)) ^ 2 :=
        Finset.sum_congr rfl fun a _ => by rw [hy a]
    _ ≤ ∑ n, (∑ i, V n i * x i) ^ 2 := h1
    _ = ∑ i, x i ^ 2 := hnorm

/-! ### Contractive mode products do not increase the Frobenius norm -/

lemma mode1_frob_le {p p' q r : ℕ} {A : Matrix (Fin p) (Fin p') ℝ} (hA : IsContraction A)
    (G : Tens p' q r) : frob2 (mode1 A G) ≤ frob2 G := by
  have e1 : frob2 (mode1 A G) = ∑ j, ∑ k, ∑ i, mode1 A G i j k ^ 2 := by
    unfold frob2; exact sum_ijk_eq_jki _
  have e2 : frob2 G = ∑ j, ∑ k, ∑ i, G i j k ^ 2 := by
    unfold frob2; exact sum_ijk_eq_jki _
  rw [e1, e2]
  exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hA (fun i => G i j k)

lemma mode2_frob_le {p q q' r : ℕ} {A : Matrix (Fin q) (Fin q') ℝ} (hA : IsContraction A)
    (G : Tens p q' r) : frob2 (mode2 A G) ≤ frob2 G := by
  have e1 : frob2 (mode2 A G) = ∑ i, ∑ k, ∑ j, mode2 A G i j k ^ 2 := by
    unfold frob2; exact sum_ijk_eq_ikj _
  have e2 : frob2 G = ∑ i, ∑ k, ∑ j, G i j k ^ 2 := by
    unfold frob2; exact sum_ijk_eq_ikj _
  rw [e1, e2]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => hA (fun j => G i j k)

lemma mode3_frob_le {p q r r' : ℕ} {A : Matrix (Fin r) (Fin r') ℝ} (hA : IsContraction A)
    (G : Tens p q r') : frob2 (mode3 A G) ≤ frob2 G := by
  unfold frob2
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hA (fun k => G i j k)

/-! ### The implicit Galerkin step is norm-nonincreasing -/

/-- If `G − h·(Kronecker sum) G = B` with `h ≥ 0` and a dissipative Kronecker sum, then
`‖G‖_F ≤ ‖B‖_F`. -/
lemma galerkin_step_frob_le {p q r : ℕ} {Fx : Matrix (Fin p) (Fin p) ℝ}
    {Fy : Matrix (Fin q) (Fin q) ℝ} {Fz : Matrix (Fin r) (Fin r) ℝ}
    (hx : IsNegSemidef Fx) (hy : IsNegSemidef Fy) (hz : IsNegSemidef Fz) {h : ℝ} (hh : 0 ≤ h)
    (Gn B : Tens p q r) (hG : ∀ i j k, Gn i j k - h * kronSum Fx Fy Fz Gn i j k = B i j k) :
    frob2 Gn ≤ frob2 B := by
  have hK := ip_kronSum_le hx hy hz Gn
  have hB' : ∀ i j k, Gn i j k * B i j k
      = Gn i j k ^ 2 - h * (Gn i j k * kronSum Fx Fy Fz Gn i j k) := by
    intro i j k
    rw [← hG i j k]
    ring
  have hT : ∑ i, ∑ j, ∑ k, Gn i j k * B i j k
      = frob2 Gn - h * ∑ i, ∑ j, ∑ k, Gn i j k * kronSum Fx Fy Fz Gn i j k := by
    unfold frob2
    simp only [hB', Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hcs : (∑ i, ∑ j, ∑ k, Gn i j k * B i j k) ^ 2 ≤ frob2 Gn * frob2 B := by
    have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin p × Fin q × Fin r))
      (fun x => Gn x.1 x.2.1 x.2.2) (fun x => B x.1 x.2.1 x.2.2)
    unfold frob2
    simpa only [Fintype.sum_prod_type, sq] using this
  have hpos : 0 ≤ frob2 Gn :=
    Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => sq_nonneg _
  have hBpos : 0 ≤ frob2 B :=
    Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => sq_nonneg _
  have hS : frob2 Gn ≤ ∑ i, ∑ j, ∑ k, Gn i j k * B i j k := by
    rw [hT]
    nlinarith [hK, hh]
  have hS2 : frob2 Gn * frob2 Gn ≤ (∑ i, ∑ j, ∑ k, Gn i j k * B i j k)
      * (∑ i, ∑ j, ∑ k, Gn i j k * B i j k) := mul_self_le_mul_self hpos hS
  nlinarith [hS2, hcs, hpos, hBpos]

/-! ### Theorem 3.2 (diffusion part) -/

/-- **Theorem 3.2, diffusion part (arXiv 2503.04932).**  Let `F_x, F_y, F_z` be symmetric negative
semidefinite. Let `Vₓ, V_y, V_z` be the orthonormal factor matrices of the current core `G`, and
`Ṽₓ, Ṽ_y, Ṽ_z` the orthonormal new bases. Let `G^{n+1}` solve the implicit Galerkin equation
`(I − h·(ṼₓᵀFₓṼₓ ⊕ ṼᵧᵀFᵧṼᵧ ⊕ Ṽ_zᵀF_zṼ_z)) G^{n+1} = B` with
`B = G ×₁ (ṼₓᵀVₓ) ×₂ (ṼᵧᵀVᵧ) ×₃ (Ṽ_zᵀV_z)` as in (3.19), and `h ≥ 0`. Then
`‖G^{n+1}‖_F ≤ ‖G‖_F`.

Differences from the paper: the explicit convection and source terms of (3.8), (3.18) and (3.19)
are omitted (this is the diffusion part only, as in the paper's proof), the time step is `h ≥ 0`,
and the bound is against the previous core `G` (the paper's `Ĝ^n` when no truncation is done). -/
theorem rail3d_first_order_diffusion_stable {Nx Ny Nz rx ry rz sx sy sz : ℕ}
    (Fx : Matrix (Fin Nx) (Fin Nx) ℝ) (Fy : Matrix (Fin Ny) (Fin Ny) ℝ)
    (Fz : Matrix (Fin Nz) (Fin Nz) ℝ)
    (hFx : IsNegSemidef Fx) (hFy : IsNegSemidef Fy) (hFz : IsNegSemidef Fz)
    (Vx : Matrix (Fin Nx) (Fin rx) ℝ) (Vy : Matrix (Fin Ny) (Fin ry) ℝ)
    (Vz : Matrix (Fin Nz) (Fin rz) ℝ)
    (Wx : Matrix (Fin Nx) (Fin sx) ℝ) (Wy : Matrix (Fin Ny) (Fin sy) ℝ)
    (Wz : Matrix (Fin Nz) (Fin sz) ℝ)
    (hVx : IsOrthonormalCols Vx) (hVy : IsOrthonormalCols Vy) (hVz : IsOrthonormalCols Vz)
    (hWx : IsOrthonormalCols Wx) (hWy : IsOrthonormalCols Wy) (hWz : IsOrthonormalCols Wz)
    (G : Tens rx ry rz) (Gn : Tens sx sy sz) {h : ℝ} (hh : 0 ≤ h)
    (hstep : ∀ i j k, Gn i j k - h * kronSum (reduce Wx Fx) (reduce Wy Fy) (reduce Wz Fz) Gn i j k
      = mode3 (crossProd Wz Vz) (mode2 (crossProd Wy Vy) (mode1 (crossProd Wx Vx) G)) i j k) :
    Real.sqrt (frob2 Gn) ≤ Real.sqrt (frob2 G) := by
  have hA := crossProd_contraction hWx hVx
  have hB := crossProd_contraction hWy hVy
  have hC := crossProd_contraction hWz hVz
  have hchain : frob2
      (mode3 (crossProd Wz Vz) (mode2 (crossProd Wy Vy) (mode1 (crossProd Wx Vx) G))) ≤ frob2 G :=
    (mode3_frob_le hC _).trans ((mode2_frob_le hB _).trans (mode1_frob_le hA G))
  have hstep' := galerkin_step_frob_le (reduce_nsd hFx Wx) (reduce_nsd hFy Wy)
    (reduce_nsd hFz Wz) hh Gn _ hstep
  exact Real.sqrt_le_sqrt (hstep'.trans hchain)

/-! ### Non-vacuity: the hypotheses of Theorem 3.2 hold for a concrete example -/

/-- `F = -1` on `ℝ¹` is symmetric negative semidefinite. -/
example : IsNegSemidef (fun _ _ : Fin 1 => (-1 : ℝ) : Matrix (Fin 1) (Fin 1) ℝ) :=
  ⟨rfl, fun x => by simp; nlinarith [sq_nonneg (x 0)]⟩

/-- The identity `1 × 1` basis has orthonormal columns. -/
example : IsOrthonormalCols (fun _ _ : Fin 1 => (1 : ℝ) : Matrix (Fin 1) (Fin 1) ℝ) := by
  intro a b
  fin_cases a
  fin_cases b
  simp

end LeanDLRA.Literature.P2503_04932
