import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.Exactness
import LeanDLRA.LinearAlgebra.Factorization.Defs
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2509.15113: Low-rank surrogates for black-box layers (I-PSI)

This module formalizes Algorithm 1 (the implicit projector-splitting integrator, I-PSI) and
Theorem 1 of Chertkov, Basharin, Saygin, Frolov, Straupe, Oseledets, *Low-rank surrogate modeling
and stochastic zero-order optimization for training of neural networks with black-box layers*.
`QueryProg` models programs that see a black box only through forward queries, and `ipsi` is
Algorithm 1, line by line, in that model; the query count `numQueries_ipsi` is therefore a statement
about the algorithm and not an assumption. On a linear box `f ω x = A ω x` with increment
`ΔA = A ω₁ - A ω₀` the output is `U₁ U₁ᵀ (Y₀ + ΔA)` plus the error of the probes
(`surrogate_run_ipsi`), the exact deviation from the tangent-space projection is
`(U₁ U₁ᵀ - U₀ U₀ᵀ) ΔA (I - V₀ V₀ᵀ)` (`proj_sub_tangent_eq`), and hence
`‖E[U₁ S₁ V₁ᵀ] - P(Y₀)(Y₀ + ΔA)‖_F ≤ ‖S₀⁻¹‖₂ ‖ΔA‖₂ ‖ΔA‖_F` for every unbiased probe law
(`theorem_1`, and `theorem_1_gaussian` for normalized Gaussian probes). The mean, variance and
mean-square error of the Gaussian estimator are computed as well, and the `σ_r`-free bound by the
doubly normal part of `ΔA` is `norm_digitalPart_exact_sub_le`.

## Differences from the paper

* The paper states Theorem 1 with `O(‖ΔA‖²)` and no constant, and proves the accuracy claim by
  a citation. Here the constant is `‖S₀⁻¹‖₂ = σ_r(Y₀)⁻¹`, with no smallness condition on `ΔA`.
* The theorem is stated for the mean of the output, the only reading under which an assumption on
  the mean of the estimator can give `O(‖ΔA‖²)`: a single draw has mean-square error
  `‖(U₁ U₁ᵀ - U₀ U₀ᵀ) ΔA (I - V₀ V₀ᵀ)‖_F² + (d_inp + 1) ‖ΔAᵀ U₁‖_F² / M`
  (`integral_norm_sq_ipsi_sub_tangent_gaussian`), which is in general first order in `ΔA`. The
  pathwise bound with the actual probe error is `norm_ipsi_sub_tangent_le`.
* "The perturbed black-box matrix" is read as `Y₀ + ΔA`, the only matrix the algorithm sees. For
  the matrix `A ω₁` itself, an initial defect is added, see `norm_matE_ipsi_sub_tangent_box`.
* `U₁, V₁ ∈ ℳ_r` is read as: `U₁`, `V₁` are orthonormal and the surrogate has rank at most `r`
  (`run_ipsi_factors`). Rank exactly `r` needs a condition (`rank_proj_eq`).
* QR factorizations are only required to give `K = Q R` with `Qᵀ Q = 1`, which covers the
  paper's QR also for rank-deficient input. The probes are an input of `ipsi`, and they are
  independent of `U₁`, which is computed before they are used.

## Claims of the paper that fail

* Eq. (4) and line 16 of Algorithm 1 have no factor `1 / M`, so the printed estimator has mean
  `M ΔAᵀ U₁` and is not unbiased for `M ≠ 1` (`matE_probeEst_ne`), and the printed algorithm then
  misses the tangent projection at first order (`matE_ipsi_printed`,
  `norm_matE_ipsi_printed_sub_tangent_ge`). The hypothesis of Theorem 1 holds for
  the weight `w = 1 / M` (`matE_probeEst_normalized`).
* The sentence in the proof of Theorem 1 that the splitting integrator is exact for updates in
  the tangent space is false (`tangent_increment_not_exact`). This example also shows that the rate
  and the curvature constant cannot be improved.

## Not formalized

Algorithm 2 (the training step) and the zeroth-order gradient estimate (3) are not treated.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2509_15113

open LeanDLRA LeanDLRA.Curvature MeasureTheory ProbabilityTheory
open scoped LeanDLRA.Frobenius

/-! ### Forward-query programs -/

/-- A program with forward access to a black box `f : Ω → (n → ℝ) → (m → ℝ)`: it either stops with
a result, or it asks for the value of the box at weights `ω` and input `x` and continues with the
answer. The continuation sees nothing of the box but the answer, so the result of a program
depends on the box only through the answers to the queries that are counted. -/
inductive QueryProg (Ω n m α : Type*) where
  | done (a : α) : QueryProg Ω n m α
  | ask (ω : Ω) (x : n → ℝ) (k : (m → ℝ) → QueryProg Ω n m α) : QueryProg Ω n m α

namespace QueryProg

variable {Ω n m α β : Type*}

/-- Sequential composition. -/
def bind : QueryProg Ω n m α → (α → QueryProg Ω n m β) → QueryProg Ω n m β
  | done a, g => g a
  | ask ω x k, g => ask ω x fun y => (k y).bind g

/-- The result of a program on the black box `f`. -/
def run (f : Ω → (n → ℝ) → (m → ℝ)) : QueryProg Ω n m α → α
  | done a => a
  | ask ω x k => run f (k (f ω x))

/-- The number of forward queries a program makes on the black box `f`. -/
def numQueries (f : Ω → (n → ℝ) → (m → ℝ)) : QueryProg Ω n m α → ℕ
  | done _ => 0
  | ask ω x k => 1 + numQueries f (k (f ω x))

/-- The result of a sequential composition. -/
theorem run_bind (f : Ω → (n → ℝ) → (m → ℝ)) (p : QueryProg Ω n m α)
    (g : α → QueryProg Ω n m β) : run f (p.bind g) = run f (g (run f p)) := by
  induction p with
  | done a => rfl
  | ask ω x k ih => exact ih _

/-- The query count of a sequential composition. -/
theorem numQueries_bind (f : Ω → (n → ℝ) → (m → ℝ)) (p : QueryProg Ω n m α)
    (g : α → QueryProg Ω n m β) :
    numQueries f (p.bind g) = numQueries f p + numQueries f (g (run f p)) := by
  induction p with
  | done a => simp [bind, numQueries, run]
  | ask ω x k ih => simp [bind, numQueries, run, ih, add_assoc]

/-- The loop `for j ← 1 to k`: runs the programs `g 0, …, g (k - 1)` in turn and collects their
results. -/
def forLoop : (k : ℕ) → (Fin k → QueryProg Ω n m α) → QueryProg Ω n m (Fin k → α)
  | 0, _ => done Fin.elim0
  | k + 1, g => (g 0).bind fun a => (forLoop k fun i => g i.succ).bind fun b =>
      done (Fin.cons a b)

/-- The result of a loop. -/
theorem run_forLoop (f : Ω → (n → ℝ) → (m → ℝ)) (k : ℕ) (g : Fin k → QueryProg Ω n m α) :
    run f (forLoop k g) = fun i => run f (g i) := by
  induction k with
  | zero => funext i; exact i.elim0
  | succ k ih =>
    funext i
    simp only [forLoop, run_bind, ih]
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [run]

/-- A loop of `k` programs with `c` queries each makes `k c` queries. -/
theorem numQueries_forLoop (f : Ω → (n → ℝ) → (m → ℝ)) (k c : ℕ)
    (g : Fin k → QueryProg Ω n m α) (hg : ∀ i, numQueries f (g i) = c) :
    numQueries f (forLoop k g) = k * c := by
  induction k with
  | zero => simp [forLoop, numQueries]
  | succ k ih =>
    have h := ih (fun i => g i.succ) fun i => hg _
    simp only [forLoop, numQueries_bind, hg, numQueries, h]
    ring

/-- One difference query `f ω₁ x - f ω₀ x`, as in lines 4 and 14 of Algorithm 1. -/
def diffQuery (ω₀ ω₁ : Ω) (x : n → ℝ) : QueryProg Ω n m (m → ℝ) :=
  ask ω₁ x fun y₁ => ask ω₀ x fun y₀ => done (y₁ - y₀)

@[simp] theorem run_diffQuery (f : Ω → (n → ℝ) → (m → ℝ)) (ω₀ ω₁ : Ω) (x : n → ℝ) :
    run f (diffQuery ω₀ ω₁ x) = f ω₁ x - f ω₀ x := rfl

@[simp] theorem numQueries_diffQuery (f : Ω → (n → ℝ) → (m → ℝ)) (ω₀ ω₁ : Ω) (x : n → ℝ) :
    numQueries f (diffQuery ω₀ ω₁ x) = 2 := rfl

end QueryProg

open QueryProg

/-! ### Algorithm 1 -/

section Algorithm

variable {Ω n m : Type*} [Fintype m] {r M : ℕ}

/-- A QR routine for `a × r` matrices: every input `K` is factored as `K = Q R` with `Qᵀ Q = 1`.
Triangularity of `R` is not asked for, since no result uses it, so all results below hold in
particular for the QR factorization of the paper, also for rank-deficient input. -/
structure IsQRRoutine {a : Type*} [Fintype a]
    (qr : Matrix a (Fin r) ℝ → Matrix a (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ) : Prop where
  orth : ∀ K, (qr K).1ᵀ * (qr K).1 = 1
  fact : ∀ K, (qr K).1 * (qr K).2 = K

/-- QR routines (lines 9 and 19 of Algorithm 1 of arXiv 2509.15113) exist as soon as there is room
for `r` orthonormal columns. -/
theorem exists_isQRRoutine {a : Type*} [Fintype a] (h : r ≤ Fintype.card a) :
    ∃ qr : Matrix a (Fin r) ℝ → Matrix a (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ,
      IsQRRoutine qr := by
  choose U hU hK using fun K : Matrix a (Fin r) ℝ => exists_orthonormal_capture_of_le_card K h
  refine ⟨fun K => (U K, (U K)ᵀ * K), ⟨hU, fun K => ?_⟩⟩
  simpa [Matrix.mul_assoc] using hK K

/-- **Bridge to the core frames.** A QR routine returns, for every input `K`, an orthonormal frame
capturing `K` (`Matrix.IsOrthCapture`, `Qᵀ Q = 1`, `Q Qᵀ K = K`) together with `R = Qᵀ K`, and
conversely. So `IsQRRoutine` is the capture hypothesis of the core step structures, made
algorithmic. -/
theorem isQRRoutine_iff {a : Type*} [Fintype a]
    {qr : Matrix a (Fin r) ℝ → Matrix a (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ} :
    IsQRRoutine qr ↔ ∀ K, Matrix.IsOrthCapture (qr K).1 K ∧ (qr K).2 = (qr K).1ᵀ * K := by
  constructor
  · intro h K
    refine ⟨Matrix.isOrthCapture_iff.2 ⟨h.orth K, (qr K).2, (h.fact K).symm⟩, ?_⟩
    calc (qr K).2 = (qr K).1ᵀ * ((qr K).1 * (qr K).2) := by
          rw [← Matrix.mul_assoc, h.orth K, Matrix.one_mul]
      _ = (qr K).1ᵀ * K := by rw [h.fact K]
  · intro h
    refine ⟨fun K => (h K).1.orth, fun K => ?_⟩
    rw [(h K).2, ← Matrix.mul_assoc, (h K).1.capture]

/-- The first factor of a QR routine is an orthonormal frame capturing the input. -/
theorem IsQRRoutine.isOrthCapture {a : Type*} [Fintype a]
    {qr : Matrix a (Fin r) ℝ → Matrix a (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ}
    (h : IsQRRoutine qr) (K : Matrix a (Fin r) ℝ) : Matrix.IsOrthCapture (qr K).1 K :=
  (isQRRoutine_iff.1 h K).1

/-- A routine returning thin QR factorizations in the sense of the core `Matrix.IsQR` (upper
triangular `R`) is a QR routine. -/
theorem isQRRoutine_of_isQR {a : Type*} [Fintype a]
    {qr : Matrix a (Fin r) ℝ → Matrix a (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ}
    (h : ∀ K, Matrix.IsQR K (qr K).1 (qr K).2) : IsQRRoutine qr :=
  ⟨fun K => (h K).orth, fun K => (h K).eq.symm⟩

/-- **Separating example.** `IsQRRoutine` does not imply `Matrix.IsQR`: the routine
`K ↦ (J, Jᵀ K)` with the swap `J` is a QR routine, but for `K = 1` its `R = Jᵀ` is not upper
triangular. -/
example : ∃ qr : Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) (Fin 2) ℝ,
    IsQRRoutine qr ∧ ¬Matrix.IsQR 1 (qr 1).1 (qr 1).2 := by
  have hJ : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * !![0, 1; 1, 0] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hJ' : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) * !![0, 1; 1, 0]ᵀ = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨fun K => (!![0, 1; 1, 0], !![0, 1; 1, 0]ᵀ * K), ⟨fun _ => hJ, fun K => ?_⟩, ?_⟩
  · simp only [← Matrix.mul_assoc, hJ', Matrix.one_mul]
  · intro h
    have := h.upper (i := 1) (j := 0) (by decide)
    simp at this

/-- The stochastic projection of eq. (4) from the answers `y j` to the probes `z j`:
`P₂ = w ∑ⱼ zⱼ yⱼᵀ U`. The paper has `w = 1` (lines 14 and 16 of Algorithm 1). -/
noncomputable def probeSum (w : ℝ) (z : Fin M → n → ℝ) (y : Fin M → m → ℝ)
    (U : Matrix m (Fin r) ℝ) : Matrix n (Fin r) ℝ :=
  w • ∑ j, Matrix.vecMulVec (z j) (y j ᵥ* U)

/-- **Algorithm 1 (I-PSI)**, arXiv 2509.15113, line by line, as a program with forward access to
the black box: `qrL`, `qrR` are the QR routines of lines 9 and 19, `U₀, S₀, V₀` the factors of the
surrogate, `ω₀, ω₁` the weights before and after the update, `z` the `M = M_sm` probes of line 13
and `w` the weight of the sum in line 16 (`w = 1` in the paper). The result is `(U₁, S₁, V₁)`.
The random probes are an input of the program: they are drawn independently of everything else,
and the probabilistic statements below integrate over this input. -/
noncomputable def ipsi (qrL : Matrix m (Fin r) ℝ → Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ)
    (qrR : Matrix n (Fin r) ℝ → Matrix n (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ)
    (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
    (ω₀ ω₁ : Ω) (w : ℝ) (z : Fin M → n → ℝ) :
    QueryProg Ω n m (Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ) :=
  (forLoop r fun j => diffQuery ω₀ ω₁ fun i => V₀ i j).bind fun p =>
    let P₁ : Matrix m (Fin r) ℝ := Matrix.of fun i j => p j i
    let K₁ := U₀ * S₀ + P₁
    let U₁ := (qrL K₁).1
    let S₀' := (qrL K₁).2
    let S₀'' := S₀' - U₁ᵀ * P₁
    (forLoop M fun j => diffQuery ω₀ ω₁ (z j)).bind fun y =>
      let P₂ := probeSum w z y U₁
      let L₁ := V₀ * S₀''ᵀ + P₂
      let V₁ := (qrR L₁).1
      let S₁ := (qrR L₁).2ᵀ
      done (U₁, S₁, V₁)

/-- **Theorem 1 of arXiv 2509.15113, query count**: Algorithm 1 uses exactly
`N_queries = 2 r + 2 M_sm` forward queries, whatever the black box is (it need not even be
linear), the factors, the probes and the dimensions `d_inp = card n`, `d_out = card m`. -/
theorem numQueries_ipsi (f : Ω → (n → ℝ) → (m → ℝ))
    (qrL : Matrix m (Fin r) ℝ → Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ)
    (qrR : Matrix n (Fin r) ℝ → Matrix n (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ)
    (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
    (ω₀ ω₁ : Ω) (w : ℝ) (z : Fin M → n → ℝ) :
    numQueries f (ipsi qrL qrR U₀ S₀ V₀ ω₀ ω₁ w z) = 2 * r + 2 * M := by
  simp only [ipsi, numQueries_bind, numQueries_forLoop f _ 2 _ fun _ => numQueries_diffQuery ..,
    numQueries]
  ring

/-- The surrogate `Y = U S Vᵀ` of a triple of factors. -/
def surrogate (Y : Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ) :
    Matrix m n ℝ :=
  Y.1 * Y.2.1 * Y.2.2ᵀ

variable [Fintype n]

/-- The basis `U₁` of line 9 in terms of `ΔA`. It does not depend on the probes. -/
def leftBasis (qrL : Matrix m (Fin r) ℝ → Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ)
    (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
    (ΔA : Matrix m n ℝ) : Matrix m (Fin r) ℝ :=
  (qrL (U₀ * S₀ + ΔA * V₀)).1

/-- Lines 8–21 of Algorithm 1 for a linear box with increment `ΔA`, for any matrix `P₂`. -/
def digitalPart (qrL : Matrix m (Fin r) ℝ → Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ)
    (qrR : Matrix n (Fin r) ℝ → Matrix n (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ)
    (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
    (ΔA : Matrix m n ℝ) (P₂ : Matrix n (Fin r) ℝ) :
    Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ :=
  let U₁ := leftBasis qrL U₀ S₀ V₀ ΔA
  let L₁ := V₀ * ((qrL (U₀ * S₀ + ΔA * V₀)).2 - U₁ᵀ * (ΔA * V₀))ᵀ + P₂
  (U₁, (qrR L₁).2ᵀ, (qrR L₁).1)

/-- The estimator of eq. (4) with weight `w` for the increment `ΔA`: `w ∑ⱼ zⱼ (ΔA zⱼ)ᵀ U`. -/
noncomputable def probeEst (w : ℝ) (z : Fin M → n → ℝ) (ΔA : Matrix m n ℝ)
    (U : Matrix m (Fin r) ℝ) : Matrix n (Fin r) ℝ :=
  probeSum w z (fun j => ΔA *ᵥ z j) U

/-- For a linear black box `f ω x = A ω x`, Algorithm 1 of arXiv 2509.15113 is lines 8–21 with
`P₁ = ΔA V₀` and with `P₂` the estimator of eq. (4), where `ΔA = A ω₁ - A ω₀`. -/
theorem run_ipsi {f : Ω → (n → ℝ) → (m → ℝ)} {A : Ω → Matrix m n ℝ}
    (hf : ∀ ω x, f ω x = A ω *ᵥ x)
    (qrL : Matrix m (Fin r) ℝ → Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ)
    (qrR : Matrix n (Fin r) ℝ → Matrix n (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ)
    (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
    (ω₀ ω₁ : Ω) (w : ℝ) (z : Fin M → n → ℝ) :
    run f (ipsi qrL qrR U₀ S₀ V₀ ω₀ ω₁ w z) =
      digitalPart qrL qrR U₀ S₀ V₀ (A ω₁ - A ω₀)
        (probeEst w z (A ω₁ - A ω₀) (leftBasis qrL U₀ S₀ V₀ (A ω₁ - A ω₀))) := by
  have hP : (Matrix.of fun i j => (A ω₁ *ᵥ (fun i => V₀ i j) - A ω₀ *ᵥ fun i => V₀ i j) i) =
      (A ω₁ - A ω₀) * V₀ := by
    ext i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.sub_apply, sub_mul,
      Finset.sum_sub_distrib]
  have hy : (fun j => A ω₁ *ᵥ z j - A ω₀ *ᵥ z j) = fun j => (A ω₁ - A ω₀) *ᵥ z j := by
    funext j; rw [Matrix.sub_mulVec]
  simp only [ipsi, run_bind, run_forLoop, run_diffQuery, hf, run, hP, hy]
  rfl

/-- Lines 8–21 of Algorithm 1 of arXiv 2509.15113: with `Y₀ = U₀ S₀ V₀ᵀ` and any `P₂`, the output is
`U₁ S₁ V₁ᵀ = U₁ U₁ᵀ (Y₀ + ΔA) + U₁ (P₂ - ΔAᵀ U₁)ᵀ`. For `P₂ = ΔAᵀ U₁` this is the step of
`Exactness.ksl_eq_proj`, which is used in the proof. -/
theorem surrogate_digitalPart
    {qrL : Matrix m (Fin r) ℝ → Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ}
    {qrR : Matrix n (Fin r) ℝ → Matrix n (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ}
    (hL : IsQRRoutine qrL) (hR : IsQRRoutine qrR)
    (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
    (ΔA : Matrix m n ℝ) (P₂ : Matrix n (Fin r) ℝ) :
    surrogate (digitalPart qrL qrR U₀ S₀ V₀ ΔA P₂) =
      leftBasis qrL U₀ S₀ V₀ ΔA * (leftBasis qrL U₀ S₀ V₀ ΔA)ᵀ * (U₀ * S₀ * V₀ᵀ + ΔA) +
      leftBasis qrL U₀ S₀ V₀ ΔA * (P₂ - ΔAᵀ * leftBasis qrL U₀ S₀ V₀ ΔA)ᵀ := by
  set U₁ := leftBasis qrL U₀ S₀ V₀ ΔA with hU₁
  set K₁ := U₀ * S₀ + ΔA * V₀ with hK₁
  have hU := hL.orth K₁
  have hF := hL.fact K₁
  have hR₁ : (qrL K₁).2 = U₁ᵀ * K₁ := by
    calc (qrL K₁).2 = ((qrL K₁).1ᵀ * (qrL K₁).1) * (qrL K₁).2 := by rw [hU, Matrix.one_mul]
      _ = (qrL K₁).1ᵀ * ((qrL K₁).1 * (qrL K₁).2) := Matrix.mul_assoc _ _ _
      _ = U₁ᵀ * K₁ := by rw [hF]; rfl
  set St := (qrL K₁).2 - U₁ᵀ * (ΔA * V₀) with hSt
  set Lex := V₀ * Stᵀ + ΔAᵀ * U₁ with hLex
  have hks := Exactness.ksl_eq_proj (A₀ := U₀ * S₀ * V₀ᵀ) (A₁ := U₀ * S₀ * V₀ᵀ + ΔA) rfl
    (K₁ := K₁) (U₁ := U₁) (Ŝ₁ := (qrL K₁).2) (St₀ := St) (L₁ := Lex)
    (by rw [add_sub_cancel_left]) hR₁ (by rw [add_sub_cancel_left, Matrix.mul_assoc])
    (by rw [add_sub_cancel_left])
  have hOut : surrogate (digitalPart qrL qrR U₀ S₀ V₀ ΔA P₂) =
      U₁ * (V₀ * Stᵀ + P₂)ᵀ := by
    change U₁ * (qrR (V₀ * Stᵀ + P₂)).2ᵀ * (qrR (V₀ * Stᵀ + P₂)).1ᵀ = _
    calc _ = U₁ * ((qrR (V₀ * Stᵀ + P₂)).1 * (qrR (V₀ * Stᵀ + P₂)).2)ᵀ := by
          rw [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hR.fact]
  rw [hOut, ← hks.2, ← Matrix.mul_add, ← Matrix.transpose_add]
  congr 2
  rw [hLex]
  abel

end Algorithm

/-! ### The tangent-space comparison -/

section FirstOrder

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ}
  {U₀ U₁ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
  {ΔA : Matrix m n ℝ}

/-- Expansion behind `proj_sub_tangent_eq`, for Theorem 1 of arXiv 2509.15113. -/
private theorem expand_aux [DecidableEq n] (P₁ P₀ : Matrix m m ℝ) (Q₀ : Matrix n n ℝ)
    (Y₀ D : Matrix m n ℝ) (h : P₁ * (Y₀ + D * Q₀) = Y₀ + D * Q₀) :
    P₁ * (Y₀ + D) - (Y₀ + (P₀ * D + D * Q₀ - P₀ * D * Q₀)) = (P₁ - P₀) * D * (1 - Q₀) := by
  have h' : P₁ * Y₀ + P₁ * D * Q₀ = Y₀ + D * Q₀ := by
    rw [← h, Matrix.mul_add, Matrix.mul_assoc]
  have e : (P₁ - P₀) * D * (1 - Q₀) = P₁ * D - P₁ * D * Q₀ - (P₀ * D - P₀ * D * Q₀) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one]
    abel
  rw [e, Matrix.mul_add]
  have : P₁ * Y₀ = Y₀ + D * Q₀ - P₁ * D * Q₀ := by rw [← h']; abel
  rw [this]
  abel

/-- The capture property of line 9 of Algorithm 1 of arXiv 2509.15113 gives
`U₁ U₁ᵀ (Y₀ + ΔA V₀ V₀ᵀ) = Y₀ + ΔA V₀ V₀ᵀ`. -/
private theorem capture_aux (hcap : U₁ * U₁ᵀ * (U₀ * S₀ + ΔA * V₀) = U₀ * S₀ + ΔA * V₀) :
    U₁ * U₁ᵀ * (U₀ * S₀ * V₀ᵀ + ΔA * (V₀ * V₀ᵀ)) = U₀ * S₀ * V₀ᵀ + ΔA * (V₀ * V₀ᵀ) := by
  have h := congrArg (· * V₀ᵀ) hcap
  simpa only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc] using h

/-- **Exact form of the first-order claim of Theorem 1, arXiv 2509.15113.** For the update with
the exact `P₂ = ΔAᵀ U₁`, whose output is `U₁ U₁ᵀ (Y₀ + ΔA)`, the deviation from the tangent-space
projection `P(Y₀)(Y₀ + ΔA) = Y₀ + P(Y₀) ΔA` is
`U₁ U₁ᵀ (Y₀ + ΔA) - P(Y₀)(Y₀ + ΔA) = (U₁ U₁ᵀ - U₀ U₀ᵀ) ΔA (I - V₀ V₀ᵀ)`.
Nothing is assumed on `S₀`, and of `U₁` only that its range captures `K₁`. -/
theorem proj_sub_tangent_eq [DecidableEq n] (hU₀ : U₀ᵀ * U₀ = 1)
    (hcap : U₁ * U₁ᵀ * (U₀ * S₀ + ΔA * V₀) = U₀ * S₀ + ΔA * V₀) :
    U₁ * U₁ᵀ * (U₀ * S₀ * V₀ᵀ + ΔA) - tangentProj U₀ V₀ (U₀ * S₀ * V₀ᵀ + ΔA) =
      (U₁ * U₁ᵀ - U₀ * U₀ᵀ) * ΔA * (1 - V₀ * V₀ᵀ) := by
  rw [map_add, tangentProj_mul_mul_transpose hU₀, tangentProj_apply]
  have h := expand_aux (U₁ * U₁ᵀ) (U₀ * U₀ᵀ) (V₀ * V₀ᵀ) (U₀ * S₀ * V₀ᵀ) ΔA (capture_aux hcap)
  simpa only [Matrix.mul_assoc] using h

/-- **The `σ_r`-free form** recorded for Theorem 1 of arXiv 2509.15113: the update with exact `P₂`
misses `Y₀ + ΔA` exactly by the doubly normal part of `ΔA`,
`U₁ U₁ᵀ (Y₀ + ΔA) - (Y₀ + ΔA) = -(I - U₁ U₁ᵀ) ΔA (I - V₀ V₀ᵀ)`. Nothing is assumed on `S₀`. -/
theorem proj_sub_add_eq [DecidableEq m] [DecidableEq n]
    (hcap : U₁ * U₁ᵀ * (U₀ * S₀ + ΔA * V₀) = U₀ * S₀ + ΔA * V₀) :
    U₁ * U₁ᵀ * (U₀ * S₀ * V₀ᵀ + ΔA) - (U₀ * S₀ * V₀ᵀ + ΔA) =
      -((1 - U₁ * U₁ᵀ) * ΔA * (1 - V₀ * V₀ᵀ)) := by
  have h := expand_aux (U₁ * U₁ᵀ) 1 (V₀ * V₀ᵀ) (U₀ * S₀ * V₀ᵀ) ΔA (capture_aux hcap)
  simp only [Matrix.one_mul, add_sub_cancel_right] at h
  rw [h, ← neg_sub (U₁ * U₁ᵀ) 1, Matrix.neg_mul, Matrix.neg_mul, neg_neg]

/-- **First-order bound of Theorem 1 of arXiv 2509.15113**, for the update with exact `P₂`. If
`U₀ᵀ U₀ = 1`, `S₀` is invertible (so `Y₀ = U₀ S₀ V₀ᵀ` has rank `r` for orthonormal `V₀`) and the
orthonormal `U₁` captures `K₁ = U₀ S₀ + ΔA V₀`, then
`‖U₁ U₁ᵀ (Y₀ + ΔA) - P(Y₀)(Y₀ + ΔA)‖_F ≤ ‖S₀⁻¹‖₂ ‖ΔA V₀‖₂ ‖ΔA (I - V₀ V₀ᵀ)‖_F`.
The paper gives no constant; `‖S₀⁻¹‖₂ = σ_r(Y₀)⁻¹` is the curvature that its proof alludes to.
No smallness of `ΔA` is needed. -/
theorem norm_proj_sub_tangent_le [DecidableEq n] (hU₀ : U₀ᵀ * U₀ = 1) (hU₁ : U₁ᵀ * U₁ = 1)
    (hS : IsUnit S₀.det) (hcap : U₁ * U₁ᵀ * (U₀ * S₀ + ΔA * V₀) = U₀ * S₀ + ΔA * V₀) :
    ‖U₁ * U₁ᵀ * (U₀ * S₀ * V₀ᵀ + ΔA) - tangentProj U₀ V₀ (U₀ * S₀ * V₀ᵀ + ΔA)‖ ≤
      specNorm S₀⁻¹ * specNorm (ΔA * V₀) * ‖ΔA * (1 - V₀ * V₀ᵀ)‖ := by
  classical
  have hXG : U₀ * S₀ * (S₀⁻¹ * U₀ᵀ) = U₀ * U₀ᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc S₀, Matrix.mul_nonsing_inv _ hS, Matrix.one_mul]
  have hG : specNorm (S₀⁻¹ * U₀ᵀ) ≤ specNorm S₀⁻¹ := by
    have h2 : specNorm U₀ᵀ ≤ 1 := by
      rw [specNorm_transpose]; exact specNorm_le_one_of_orthonormal hU₀
    calc specNorm (S₀⁻¹ * U₀ᵀ) ≤ specNorm S₀⁻¹ * specNorm U₀ᵀ := specNorm_mul_le _ _
      _ ≤ specNorm S₀⁻¹ * 1 := mul_le_mul_of_nonneg_left h2 (specNorm_nonneg _)
      _ = specNorm S₀⁻¹ := mul_one _
  have hb := norm_colProj_sub_mul_le hU₀ hU₁ hXG hcap (ΔA * (1 - V₀ * V₀ᵀ))
  rw [add_sub_cancel_left] at hb
  rw [proj_sub_tangent_eq hU₀ hcap, Matrix.mul_assoc]
  refine hb.trans ?_
  have := specNorm_nonneg (ΔA * V₀)
  have := norm_nonneg (ΔA * (1 - V₀ * V₀ᵀ))
  gcongr

/-- `‖ΔA V₀‖₂ ≤ ‖ΔA‖₂` for orthonormal `V₀`, for Theorem 1 of arXiv 2509.15113. -/
private theorem specNorm_mul_orthonormal_le [DecidableEq n] (hV₀ : V₀ᵀ * V₀ = 1) :
    specNorm (ΔA * V₀) ≤ specNorm ΔA := by
  calc specNorm (ΔA * V₀) ≤ specNorm ΔA * specNorm V₀ := specNorm_mul_le _ _
    _ ≤ specNorm ΔA * 1 :=
      mul_le_mul_of_nonneg_left (specNorm_le_one_of_orthonormal hV₀) (specNorm_nonneg _)
    _ = specNorm ΔA := mul_one _

/-- Coarser form of `norm_proj_sub_tangent_le`, the `O(‖ΔA‖²)` of Theorem 1 of arXiv 2509.15113:
the right-hand side is at most `‖S₀⁻¹‖₂ ‖ΔA‖_F²`, see `specNorm_le_frob`. -/
theorem norm_proj_sub_tangent_le' [DecidableEq n] (hU₀ : U₀ᵀ * U₀ = 1) (hU₁ : U₁ᵀ * U₁ = 1)
    (hV₀ : V₀ᵀ * V₀ = 1) (hS : IsUnit S₀.det)
    (hcap : U₁ * U₁ᵀ * (U₀ * S₀ + ΔA * V₀) = U₀ * S₀ + ΔA * V₀) :
    ‖U₁ * U₁ᵀ * (U₀ * S₀ * V₀ᵀ + ΔA) - tangentProj U₀ V₀ (U₀ * S₀ * V₀ᵀ + ΔA)‖ ≤
      specNorm S₀⁻¹ * specNorm ΔA * ‖ΔA‖ := by
  refine (norm_proj_sub_tangent_le hU₀ hU₁ hS hcap).trans ?_
  have h1 := specNorm_mul_orthonormal_le (ΔA := ΔA) hV₀
  have h2 : ‖ΔA * (1 - V₀ * V₀ᵀ)‖ ≤ ‖ΔA‖ :=
    (isOrthProjMat_mul_transpose hV₀).compl.norm_mul_le' _
  have h3 := specNorm_nonneg S₀⁻¹
  have h4 := specNorm_nonneg (ΔA * V₀)
  have h5 := norm_nonneg (ΔA * (1 - V₀ * V₀ᵀ))
  have h6 := specNorm_nonneg ΔA
  gcongr

/-- `S₀ + C` is invertible when `‖S₀⁻¹‖₂ ‖C‖₂ < 1`, for Theorem 1 of arXiv 2509.15113. -/
private theorem isUnit_add_of_small {C : Matrix (Fin r) (Fin r) ℝ} (hS : IsUnit S₀.det)
    (h : specNorm S₀⁻¹ * specNorm C < 1) : IsUnit (S₀ + C) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro a b hab
  have h0 : (S₀ + C) *ᵥ (a - b) = 0 := by
    rw [Matrix.mulVec_sub]
    exact sub_eq_zero.mpr hab
  have hv : a - b = -((S₀⁻¹ * C) *ᵥ (a - b)) := by
    have h1 := congrArg (S₀⁻¹ *ᵥ ·) h0
    simp only [Matrix.add_mulVec, Matrix.mulVec_add, Matrix.mulVec_zero, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hS, Matrix.one_mulVec] at h1
    exact eq_neg_of_add_eq_zero_left h1
  have hn := norm_toEuclideanLin_le (S₀⁻¹ * C) (WithLp.toLp 2 (a - b))
  have he : Matrix.toEuclideanLin (S₀⁻¹ * C) (WithLp.toLp 2 (a - b)) =
      -(WithLp.toLp 2 (a - b) : EuclideanSpace ℝ (Fin r)) := by
    rw [Matrix.toLpLin_apply]
    conv_rhs => rw [hv]
    simp
  rw [he, norm_neg] at hn
  have hm : specNorm (S₀⁻¹ * C) < 1 := (specNorm_mul_le _ _).trans_lt h
  have hz : ‖(WithLp.toLp 2 (a - b) : EuclideanSpace ℝ (Fin r))‖ = 0 := by
    by_contra hne
    have hp := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    nlinarith
  rw [norm_eq_zero] at hz
  have := congrArg WithLp.ofLp hz
  simpa [sub_eq_zero] using this

/-- **The exact update stays on `ℳ_r`.** If `U₀ᵀ U₀ = 1`, `V₀ᵀ V₀ = 1`, `S₀` is invertible and
`‖ΔA‖₂ < σ_r(Y₀)` in the form `‖S₀⁻¹‖₂ ‖ΔA‖₂ < 1`, then `U₁ U₁ᵀ (Y₀ + ΔA)` has rank exactly `r`.
Theorem 1 of arXiv 2509.15113 says the update stays on `ℳ_r` without a condition, but one is
needed, since `ΔA = -Y₀` gives the zero matrix. -/
theorem rank_proj_eq [DecidableEq n] (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1)
    (hS : IsUnit S₀.det) (hsmall : specNorm S₀⁻¹ * specNorm ΔA < 1)
    (hcap : U₁ * U₁ᵀ * (U₀ * S₀ + ΔA * V₀) = U₀ * S₀ + ΔA * V₀) :
    (U₁ * U₁ᵀ * (U₀ * S₀ * V₀ᵀ + ΔA)).rank = r := by
  classical
  have hC : specNorm (U₀ᵀ * (ΔA * V₀)) ≤ specNorm ΔA := by
    have h2 : specNorm U₀ᵀ ≤ 1 := by
      rw [specNorm_transpose]; exact specNorm_le_one_of_orthonormal hU₀
    calc specNorm (U₀ᵀ * (ΔA * V₀)) ≤ specNorm U₀ᵀ * specNorm (ΔA * V₀) := specNorm_mul_le _ _
      _ ≤ 1 * specNorm ΔA := mul_le_mul h2 (specNorm_mul_orthonormal_le hV₀) (specNorm_nonneg _)
          zero_le_one
      _ = specNorm ΔA := one_mul _
  have hunit : IsUnit (S₀ + U₀ᵀ * (ΔA * V₀)) := isUnit_add_of_small hS
    ((mul_le_mul_of_nonneg_left hC (specNorm_nonneg _)).trans_lt hsmall)
  have hX : U₁ * U₁ᵀ * (U₀ * S₀ * V₀ᵀ + ΔA) * V₀ = U₀ * S₀ + ΔA * V₀ := by
    rw [Matrix.mul_assoc _ _ V₀, Matrix.add_mul, Matrix.mul_assoc _ V₀ᵀ, hV₀, Matrix.mul_one,
      hcap]
  have hK : U₀ᵀ * (U₀ * S₀ + ΔA * V₀) = S₀ + U₀ᵀ * (ΔA * V₀) := by
    rw [Matrix.mul_add, ← Matrix.mul_assoc, hU₀, Matrix.one_mul]
  apply le_antisymm
  · calc (U₁ * U₁ᵀ * (U₀ * S₀ * V₀ᵀ + ΔA)).rank ≤ U₁.rank := by
          rw [Matrix.mul_assoc]; exact Matrix.rank_mul_le_left _ _
      _ ≤ r := by simpa using U₁.rank_le_card_width
  · calc r = (S₀ + U₀ᵀ * (ΔA * V₀)).rank := by
          rw [Matrix.rank_of_isUnit _ hunit, Fintype.card_fin]
      _ = (U₀ᵀ * (U₁ * U₁ᵀ * (U₀ * S₀ * V₀ᵀ + ΔA) * V₀)).rank := by rw [hX, hK]
      _ ≤ (U₁ * U₁ᵀ * (U₀ * S₀ * V₀ᵀ + ΔA) * V₀).rank := Matrix.rank_mul_le_right _ _
      _ ≤ _ := Matrix.rank_mul_le_left _ _

end FirstOrder

/-! ### Expectations of random matrices -/

section Expectation

variable {X a b : Type*} [MeasurableSpace X]

/-- The expectation of a random matrix, taken entry by entry. -/
noncomputable def matE (ν : Measure X) (F : X → Matrix a b ℝ) : Matrix a b ℝ :=
  Matrix.of fun i j => ∫ x, F x i j ∂ν

@[simp] theorem matE_apply (ν : Measure X) (F : X → Matrix a b ℝ) (i : a) (j : b) :
    matE ν F i j = ∫ x, F x i j ∂ν := rfl

variable {m n : Type*} {r : ℕ} {ν : Measure X} [IsProbabilityMeasure ν]
  {U : Matrix m (Fin r) ℝ} {Est : X → Matrix n (Fin r) ℝ} {B : Matrix n (Fin r) ℝ}

/-- The entries of `U (Est - B)ᵀ` are integrable. -/
private theorem integrable_perturbation (hint : ∀ i j, Integrable (fun x => Est x i j) ν)
    (i : m) (j : n) : Integrable (fun x => (U * (Est x - B)ᵀ) i j) ν := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.sub_apply]
  exact integrable_finsetSum _ fun k _ => ((hint j k).sub (integrable_const _)).const_mul _

/-- For Theorem 1 of arXiv 2509.15113: an estimator `Est` with mean `B` gives a perturbation
`U (Est - B)ᵀ` with mean zero. -/
theorem matE_perturbation (hint : ∀ i j, Integrable (fun x => Est x i j) ν)
    (hunb : matE ν Est = B) : matE ν (fun x => U * (Est x - B)ᵀ) = 0 := by
  ext i j
  have h : ∀ k, ∫ x, Est x j k ∂ν = B j k := fun k => by rw [← hunb]; rfl
  have hf : ∀ k ∈ Finset.univ, Integrable (fun x => U i k * (Est x j k - B j k)) ν := fun k _ =>
    ((hint j k).sub (integrable_const _)).const_mul _
  simp only [matE_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.sub_apply,
    Matrix.zero_apply]
  rw [integral_finsetSum _ hf]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [integral_const_mul, integral_sub (hint j k) (integrable_const _), h k]
  simp

/-- For Theorem 1 of arXiv 2509.15113: bias of the output in terms of the bias of the estimator,
`E[C + U (Est - B)ᵀ] = C + U (E[Est] - B)ᵀ`. -/
theorem matE_add_mul_transpose (C : Matrix m n ℝ)
    (hint : ∀ i j, Integrable (fun x => Est x i j) ν) :
    matE ν (fun x => C + U * (Est x - B)ᵀ) = C + U * (matE ν Est - B)ᵀ := by
  have h0 : matE ν (fun x => U * (Est x - matE ν Est)ᵀ) = 0 := matE_perturbation hint rfl
  have e : ∀ x, U * (Est x - B)ᵀ = U * (Est x - matE ν Est)ᵀ + U * (matE ν Est - B)ᵀ := by
    intro x
    rw [← Matrix.mul_add, ← Matrix.transpose_add, sub_add_sub_cancel]
  ext i j
  have h1 := congrFun (congrFun h0 i) j
  simp only [matE_apply, Matrix.zero_apply] at h1
  have h2 : Integrable
      (fun x => (U * (Est x - matE ν Est)ᵀ) i j + (U * (matE ν Est - B)ᵀ) i j) ν :=
    (integrable_perturbation hint i j).add (integrable_const _)
  simp only [matE_apply, Matrix.add_apply, e]
  rw [integral_add (integrable_const _) h2,
    integral_add (integrable_perturbation hint i j) (integrable_const _), h1]
  simp

variable [Fintype m] [Fintype n]

/-- **Mean-square error of an unbiased perturbation**, for Theorem 1 of arXiv 2509.15113: for
`Uᵀ U = 1` and an estimator `Est` with
mean `B` and finite second moments,
`E ‖D + U (Est - B)ᵀ‖_F² = ‖D‖_F² + E ‖Est - B‖_F²`. -/
theorem integral_norm_sq_add_perturbation (D : Matrix m n ℝ) (hU : Uᵀ * U = 1)
    (hint : ∀ i j, MemLp (fun x => Est x i j) 2 ν) (hunb : matE ν Est = B) :
    ∫ x, ‖D + U * (Est x - B)ᵀ‖ ^ 2 ∂ν = ‖D‖ ^ 2 + ∫ x, ‖Est x - B‖ ^ 2 ∂ν := by
  have hint1 : ∀ i j, Integrable (fun x => Est x i j) ν := fun i j =>
    (hint i j).integrable (by norm_num)
  have hp : ∀ x, ‖D + U * (Est x - B)ᵀ‖ ^ 2 =
      ‖D‖ ^ 2 + 2 * ⟪D, U * (Est x - B)ᵀ⟫ + ‖Est x - B‖ ^ 2 := by
    intro x
    rw [norm_add_sq_real, Frobenius.norm_mul_of_orthonormal hU, Frobenius.norm_transpose]
  have hin : Integrable (fun x => ‖Est x - B‖ ^ 2) ν := by
    simp only [Frobenius.norm_sq_eq_sum, Matrix.sub_apply]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      ((hint i j).sub (memLp_const _)).integrable_sq
  have hij : ∀ i, ∀ j ∈ Finset.univ,
      Integrable (fun x => D i j * (U * (Est x - B)ᵀ) i j) ν := fun i j _ =>
    (integrable_perturbation hint1 i j).const_mul _
  have hinner : Integrable (fun x => ⟪D, U * (Est x - B)ᵀ⟫) ν := by
    simp only [Frobenius.inner_def]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ (hij i)
  have hzero : ∫ x, ⟪D, U * (Est x - B)ᵀ⟫ ∂ν = 0 := by
    have h0 := matE_perturbation (U := U) hint1 hunb
    simp only [Frobenius.inner_def]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ (hij i)]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_finsetSum _ (hij i)]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_const_mul]
    have h1 := congrFun (congrFun h0 i) j
    simp only [matE_apply, Matrix.zero_apply] at h1
    rw [h1, mul_zero]
  have h2 : Integrable (fun x => ‖D‖ ^ 2 + 2 * ⟪D, U * (Est x - B)ᵀ⟫) ν :=
    (integrable_const _).add (hinner.const_mul 2)
  simp only [hp]
  rw [integral_add h2 hin, integral_add (integrable_const _) (hinner.const_mul 2),
    integral_const_mul, hzero]
  simp

end Expectation

/-! ### Gaussian probes -/

section Gaussian

local notation "γ₁" => gaussianReal 0 1

variable {n : Type*} [Fintype n]

/-- The law `N(0, I)` of a probe `z ∈ ℝ^{d_inp}`: independent standard Gaussian coordinates. -/
noncomputable def stdNormal (n : Type*) [Fintype n] : Measure (n → ℝ) :=
  Measure.pi fun _ => γ₁

/-- `N(0, I)` is a probability measure. -/
instance : IsProbabilityMeasure (stdNormal n) := by
  unfold stdNormal; infer_instance

/-- The joint law of `M` independent probes `z₁, …, z_M ∼ N(0, I)`. -/
noncomputable def gaussianProbes (M : ℕ) (n : Type*) [Fintype n] : Measure (Fin M → n → ℝ) :=
  Measure.pi fun _ => stdNormal n

/-- The joint law of the probes is a probability measure. -/
instance {M : ℕ} : IsProbabilityMeasure (gaussianProbes M n) := by
  unfold gaussianProbes; infer_instance

/-- The derivative of `p(t) exp(t² / 2)`, for the moments of the Gaussian. -/
private theorem deriv_poly_mul_exp (p p' : ℝ → ℝ) (h : ∀ t, HasDerivAt p (p' t) t) :
    deriv (fun t => p t * Real.exp (t ^ 2 / 2)) =
      fun t => (p' t + t * p t) * Real.exp (t ^ 2 / 2) := by
  funext t
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (t ^ 2 / 2)) (Real.exp (t ^ 2 / 2) * t) t := by
    have h0 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) t t := by
      have := (hasDerivAt_pow 2 t).div_const 2
      simpa using this
    exact h0.exp
  have := (h t).fun_mul h1
  rw [this.deriv]
  ring

/-- The second moment of `N(0, 1)`. -/
private theorem moment_two : ∫ x, x ^ 2 ∂γ₁ = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa using h

/-- The fourth moment of `N(0, 1)`, from the fourth derivative of its moment generating function. -/
private theorem moment_four : ∫ x, x ^ 4 ∂γ₁ = 3 := by
  have h : ∫ x, x ^ 4 ∂γ₁ = iteratedDeriv 4 (mgf (fun x => x) γ₁) 0 := by
    rw [iteratedDeriv_mgf_zero] <;> simp
  rw [h, mgf_fun_id_gaussianReal]
  have e0 : (fun t : ℝ => Real.exp (0 * t + (1 : NNReal) * t ^ 2 / 2)) =
      fun t => (fun _ => (1 : ℝ)) t * Real.exp (t ^ 2 / 2) := by
    funext t; simp
  rw [e0]
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [deriv_poly_mul_exp (fun _ => 1) (fun _ => 0) fun t => hasDerivAt_const t 1]
  have e1 : (fun t : ℝ => (0 + t * 1) * Real.exp (t ^ 2 / 2)) =
      fun t => (fun t => t) t * Real.exp (t ^ 2 / 2) := by funext t; simp
  rw [e1, deriv_poly_mul_exp (fun t => t) (fun _ => 1) fun t => hasDerivAt_id t]
  have d2 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => 1 + t * t) (2 * t) t := fun t => by
    have := ((hasDerivAt_id' t).fun_mul (hasDerivAt_id' t)).const_add 1
    convert this using 1
    ring
  rw [deriv_poly_mul_exp (fun t => 1 + t * t) (fun t => 2 * t) d2]
  have d3 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => 2 * t + t * (1 + t * t)) (3 + 3 * t ^ 2) t := by
    intro t
    have := ((hasDerivAt_id' t).const_mul 2).fun_add ((hasDerivAt_id' t).fun_mul (d2 t))
    convert this using 1
    ring
  rw [deriv_poly_mul_exp (fun t => 2 * t + t * (1 + t * t)) (fun t => 3 + 3 * t ^ 2) d3]
  simp


/-- All moments of `N(0, 1)` are finite. -/
private theorem integrable_pow_gaussian (k : ℕ) : Integrable (fun x : ℝ => x ^ k) γ₁ := by
  have h : (0 : ℝ) ∈ interior (integrableExpSet (fun x : ℝ => x) γ₁) := by simp
  exact integrable_pow_of_mem_interior_integrableExpSet h k

/-- Monomials in a Gaussian vector are integrable. -/
private theorem integrable_prod_pow (e : n → ℕ) :
    Integrable (fun z : n → ℝ => ∏ i, z i ^ e i) (stdNormal n) :=
  Integrable.fintype_prod (f := fun i x => x ^ e i) fun i => integrable_pow_gaussian (e i)

/-- The coordinates of a Gaussian vector are independent. -/
private theorem integral_prod_pow (e : n → ℕ) :
    ∫ z, ∏ i, z i ^ e i ∂stdNormal n = ∏ i, ∫ x, x ^ e i ∂γ₁ :=
  integral_fintype_prod_eq_prod fun i x => x ^ e i

/-- The zeroth moment of `N(0, 1)`. -/
private theorem moment_zero : ∫ x, x ^ 0 ∂γ₁ = 1 := by simp

/-- The first moment of `N(0, 1)`. -/
private theorem moment_one : ∫ x, x ^ 1 ∂γ₁ = 0 := by simp

/-- Selecting one coordinate by a product of powers. -/
private theorem prod_pow_ite [DecidableEq n] (z : n → ℝ) (a : n) :
    ∏ i, z i ^ (if i = a then 1 else 0) = z a := by
  simp [pow_ite, Finset.prod_ite_eq']

/-- A quadratic monomial as a product of powers. -/
private theorem prod_pow_two [DecidableEq n] (z : n → ℝ) (a b : n) :
    ∏ i, z i ^ ((if i = a then 1 else 0) + (if i = b then 1 else 0)) = z a * z b := by
  simp_rw [pow_add, Finset.prod_mul_distrib, prod_pow_ite]

/-- A quartic monomial as a product of powers. -/
private theorem prod_pow_four [DecidableEq n] (z : n → ℝ) (a b c d : n) :
    ∏ i, z i ^ ((if i = a then 1 else 0) + (if i = b then 1 else 0) +
      (if i = c then 1 else 0) + (if i = d then 1 else 0)) = z a * z b * z c * z d := by
  simp_rw [pow_add, Finset.prod_mul_distrib, prod_pow_ite]

/-- Quadratic monomials in `z ∼ N(0, I)` are integrable. -/
theorem integrable_two (a b : n) :
    Integrable (fun z : n → ℝ => z a * z b) (stdNormal n) := by
  classical
  simpa only [prod_pow_two] using integrable_prod_pow fun i =>
    (if i = a then 1 else 0) + (if i = b then 1 else 0)

/-- Quartic monomials in `z ∼ N(0, I)` are integrable. -/
theorem integrable_four (a b c d : n) :
    Integrable (fun z : n → ℝ => z a * z b * z c * z d) (stdNormal n) := by
  classical
  simpa only [prod_pow_four] using integrable_prod_pow fun i =>
    (if i = a then 1 else 0) + (if i = b then 1 else 0) + (if i = c then 1 else 0) +
      (if i = d then 1 else 0)

/-- Covariance of `z ∼ N(0, I)`: `E[z_a z_b] = δ_ab`. -/
theorem integral_two [DecidableEq n] (a b : n) :
    ∫ z, z a * z b ∂stdNormal n = if a = b then 1 else 0 := by
  have h := integral_prod_pow (n := n) fun i =>
    (if i = a then 1 else 0) + (if i = b then 1 else 0)
  simp only [prod_pow_two] at h
  rw [h]
  split_ifs with hab
  · subst hab
    refine Finset.prod_eq_one fun i _ => ?_
    by_cases hi : i = a
    · simp [hi, moment_two]
    · simp [hi]
  · refine Finset.prod_eq_zero (Finset.mem_univ a) ?_
    simp [hab]

/-- The fourth moments of `z ∼ N(0, I)` that enter the variance of eq. (4) of arXiv 2509.15113:
`E[z_a² z_l z_l'] = δ_ll' + 2 δ_la δ_l'a`. -/
theorem integral_four [DecidableEq n] (a l l' : n) :
    ∫ z, z a * z a * z l * z l' ∂stdNormal n =
      (if l = l' then 1 else 0) + (if l = a ∧ l' = a then 2 else 0) := by
  have h := integral_prod_pow (n := n) fun i =>
    (if i = a then 1 else 0) + (if i = a then 1 else 0) + (if i = l then 1 else 0) +
      (if i = l' then 1 else 0)
  simp only [prod_pow_four] at h
  rw [h]
  by_cases hll : l = l'
  · subst hll
    by_cases hla : l = a
    · subst hla
      rw [Finset.prod_eq_single l]
      · simp [moment_four]; norm_num
      · intro i _ hi; simp [hi]
      · simp
    · simp only [ite_true, hla, false_and, ite_false, add_zero]
      refine Finset.prod_eq_one fun i _ => ?_
      by_cases h1 : i = a
      · subst h1; simp [Ne.symm hla, moment_two]
      · by_cases h2 : i = l
        · subst h2; simp [h1, moment_two]
        · simp [h1, h2]
  · have h0 : ¬ (l = a ∧ l' = a) := fun h => hll (h.1.trans h.2.symm)
    simp only [hll, h0, ite_false, add_zero]
    by_cases hla : l = a
    · have hla' : l' ≠ a := fun h => hll (hla.trans h.symm)
      refine Finset.prod_eq_zero (Finset.mem_univ l') ?_
      simp [hla', Ne.symm hll]
    · refine Finset.prod_eq_zero (Finset.mem_univ l) ?_
      simp [hla, hll]


/-- The entry `z_a (zᵀ b)` of `z zᵀ b`. -/
def quad (a : n) (b z : n → ℝ) : ℝ := z a * ∑ l, z l * b l

/-- `quad` as a sum. -/
private theorem quad_eq (a : n) (b z : n → ℝ) : quad a b z = ∑ l, z a * z l * b l := by
  simp only [quad, Finset.mul_sum, mul_assoc]

/-- The square of `quad` as a double sum. -/
private theorem quad_sq_eq (a : n) (b z : n → ℝ) :
    quad a b z ^ 2 = ∑ l, ∑ l', z a * z a * z l * z l' * (b l * b l') := by
  have h : ∑ l, ∑ l', z a * z a * z l * z l' * (b l * b l') =
      z a * z a * ((∑ l, z l * b l) * ∑ l', z l' * b l') := by
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l' _ => ?_
    ring
  rw [h, quad]
  ring

/-- `quad` is integrable. -/
private theorem integrable_quad (a : n) (b : n → ℝ) : Integrable (quad a b) (stdNormal n) := by
  have : quad a b = fun z => ∑ l, z a * z l * b l := funext (quad_eq a b)
  rw [this]
  exact integrable_finsetSum _ fun l _ => (integrable_two a l).mul_const _

/-- The square of `quad` is integrable. -/
private theorem integrable_quad_sq (a : n) (b : n → ℝ) :
    Integrable (fun z => quad a b z ^ 2) (stdNormal n) := by
  simp only [quad_sq_eq]
  exact integrable_finsetSum _ fun l _ => integrable_finsetSum _ fun l' _ =>
    (integrable_four a a l l').mul_const _

/-- `quad` is measurable. -/
private theorem measurable_quad (a : n) (b : n → ℝ) : Measurable (quad a b) := by
  unfold quad
  fun_prop

/-- `quad` is square integrable. -/
private theorem memLp_quad (a : n) (b : n → ℝ) : MemLp (quad a b) 2 (stdNormal n) :=
  (memLp_two_iff_integrable_sq (measurable_quad a b).aestronglyMeasurable).2
    (integrable_quad_sq a b)

/-- `E[z_a (zᵀ b)] = b_a`. -/
private theorem integral_quad (a : n) (b : n → ℝ) :
    ∫ z, quad a b z ∂stdNormal n = b a := by
  classical
  simp only [quad_eq]
  rw [integral_finsetSum _ fun l _ => (integrable_two a l).mul_const _]
  simp only [integral_mul_const, integral_two]
  simp

/-- `E[(z_a (zᵀ b))²] = ‖b‖² + 2 b_a²`. -/
private theorem integral_quad_sq (a : n) (b : n → ℝ) :
    ∫ z, quad a b z ^ 2 ∂stdNormal n = ∑ l, b l ^ 2 + 2 * b a ^ 2 := by
  classical
  simp only [quad_sq_eq]
  rw [integral_finsetSum _ fun l _ => integrable_finsetSum _ fun l' _ =>
    (integrable_four a a l l').mul_const _]
  simp_rw [integral_finsetSum _ fun l' _ => (integrable_four a a _ l').mul_const _,
    integral_mul_const, integral_four, add_mul, Finset.sum_add_distrib]
  congr 1
  · simp [sq]
  · rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single a]
      · simp; ring
      · intro l' _ h; simp [h]
      · simp
    · intro l _ h
      simp [h]
    · simp

/-- `Var[z_a (zᵀ b)] = ‖b‖² + b_a²`. -/
private theorem variance_quad (a : n) (b : n → ℝ) :
    Var[quad a b; stdNormal n] = ∑ l, b l ^ 2 + b a ^ 2 := by
  rw [variance_eq_sub (memLp_quad a b)]
  have h : (quad a b ^ 2) = fun z => quad a b z ^ 2 := rfl
  rw [h, integral_quad_sq, integral_quad]
  ring

/-- A function of the `j`-th probe has the law of a function of `z ∼ N(0, I)`. -/
private theorem integral_eval {M : ℕ} (j : Fin M) {g : (n → ℝ) → ℝ} (hg : Measurable g) :
    ∫ Z, g (Z j) ∂gaussianProbes M n = ∫ z, g z ∂stdNormal n := by
  have h := measurePreserving_eval (fun _ : Fin M => stdNormal n) j
  rw [← h.map_eq, integral_map h.measurable.aemeasurable hg.aestronglyMeasurable]
  rfl

/-- Integrability of a function of the `j`-th probe. -/
private theorem integrable_eval {M : ℕ} (j : Fin M) {g : (n → ℝ) → ℝ}
    (hg : Integrable g (stdNormal n)) :
    Integrable (fun Z : Fin M → n → ℝ => g (Z j)) (gaussianProbes M n) := by
  have h := measurePreserving_eval (fun _ : Fin M => stdNormal n) j
  exact h.integrable_comp_of_integrable hg

/-- One entry of the estimator of eq. (4) of arXiv 2509.15113, mean over independent probes. -/
theorem integral_sum_quad {M : ℕ} (a : n) (b : n → ℝ) (w : ℝ) :
    ∫ Z, w * ∑ j, quad a b (Z j) ∂gaussianProbes M n = w * M * b a := by
  rw [integral_const_mul, integral_finsetSum _ fun j _ => integrable_eval j (integrable_quad a b)]
  simp only [integral_eval _ (measurable_quad a b), integral_quad]
  simp [mul_assoc]

/-- One entry of the estimator of eq. (4) of arXiv 2509.15113 is square integrable. -/
theorem memLp_sum_quad {M : ℕ} (a : n) (b : n → ℝ) (w : ℝ) :
    MemLp (fun Z : Fin M → n → ℝ => w * ∑ j, quad a b (Z j)) 2 (gaussianProbes M n) := by
  refine MemLp.const_mul ?_ w
  refine memLp_finsetSum _ fun j _ => ?_
  exact (memLp_quad a b).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin M => stdNormal n) j)

/-- One entry of the estimator of eq. (4) of arXiv 2509.15113: variance over independent probes. -/
theorem variance_sum_quad {M : ℕ} (a : n) (b : n → ℝ) (w : ℝ) :
    Var[fun Z : Fin M → n → ℝ => w * ∑ j, quad a b (Z j); gaussianProbes M n] =
      w ^ 2 * M * (∑ l, b l ^ 2 + b a ^ 2) := by
  have h := variance_sum_pi (μ := fun _ : Fin M => stdNormal n)
    (X := fun _ => quad a b) fun _ => memLp_quad a b
  have e : (fun Z : Fin M → n → ℝ => w * ∑ j, quad a b (Z j)) =
      fun Z => w * (∑ j : Fin M, fun Z : Fin M → n → ℝ => quad a b (Z j)) Z := by
    funext Z; simp
  rw [e, variance_const_mul]
  change w ^ 2 * Var[_; Measure.pi fun _ : Fin M => stdNormal n] = _
  rw [h]
  simp only [variance_quad, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- One entry of the normalized estimator of eq. (4) of arXiv 2509.15113: mean-square deviation. -/
theorem integral_sq_sub_sum_quad {M : ℕ} (hM : 0 < M) (a : n) (b : n → ℝ) :
    ∫ Z, ((1 / (M : ℝ)) * ∑ j, quad a b (Z j) - b a) ^ 2 ∂gaussianProbes M n =
      (∑ l, b l ^ 2 + b a ^ 2) / M := by
  have hM' : (M : ℝ) ≠ 0 := by positivity
  have hmean := integral_sum_quad (M := M) a b (1 / (M : ℝ))
  have hmean' : 1 / (M : ℝ) * M * b a = b a := by field_simp
  rw [hmean'] at hmean
  have hv := variance_sum_quad (M := M) a b (1 / (M : ℝ))
  rw [variance_eq_integral (memLp_sum_quad a b _).aemeasurable, hmean] at hv
  rw [hv]
  field_simp



variable {m : Type*} [Fintype m] {r M : ℕ}

/-- The entries of the estimator of eq. (4) of arXiv 2509.15113: `(ΔA z)ᵀ U = zᵀ ΔAᵀ U`. -/
theorem probeEst_apply (w : ℝ) (Z : Fin M → n → ℝ) (ΔA : Matrix m n ℝ) (U : Matrix m (Fin r) ℝ)
    (a : n) (k : Fin r) :
    probeEst w Z ΔA U a k = w * ∑ j, quad a (fun l => (ΔAᵀ * U) l k) (Z j) := by
  simp only [probeEst, probeSum, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    Matrix.vecMulVec_apply]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [quad, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul]
  rfl

/-- **Mean of the estimator of eq. (4)** for independent `zⱼ ∼ N(0, I)` and any fixed `U`:
`E[w ∑ⱼ zⱼ (ΔA zⱼ)ᵀ U] = w M ΔAᵀ U`. -/
theorem matE_probeEst (w : ℝ) (ΔA : Matrix m n ℝ) (U : Matrix m (Fin r) ℝ) :
    matE (gaussianProbes M n) (fun Z => probeEst w Z ΔA U) = (w * M) • (ΔAᵀ * U) := by
  ext a k
  simp only [matE_apply, probeEst_apply, integral_sum_quad, Matrix.smul_apply, smul_eq_mul]

/-- The normalized estimator `(1 / M) ∑ⱼ zⱼ (ΔA zⱼ)ᵀ U` is unbiased, so the hypothesis of
Theorem 1 of arXiv 2509.15113 can be met. -/
theorem matE_probeEst_normalized (hM : 0 < M) (ΔA : Matrix m n ℝ) (U : Matrix m (Fin r) ℝ) :
    matE (gaussianProbes M n) (fun Z => probeEst (1 / (M : ℝ)) Z ΔA U) = ΔAᵀ * U := by
  have hM' : (M : ℝ) ≠ 0 := by positivity
  rw [matE_probeEst, one_div, inv_mul_cancel₀ hM', one_smul]

/-- **The estimator as printed is biased.** Eq. (4) and line 16 of Algorithm 1 of arXiv 2509.15113
have no factor `1 / M`, so for `M ≠ 1` and `ΔAᵀ U ≠ 0` the hypothesis "the stochastic projection in
Eq. (4) is unbiased" of Theorem 1 does not hold for `zⱼ ∼ N(0, I)`: the mean is `M ΔAᵀ U`. -/
theorem matE_probeEst_ne (hM : M ≠ 1) {ΔA : Matrix m n ℝ} {U : Matrix m (Fin r) ℝ}
    (hB : ΔAᵀ * U ≠ 0) :
    matE (gaussianProbes M n) (fun Z => probeEst 1 Z ΔA U) ≠ ΔAᵀ * U := by
  rw [matE_probeEst, one_mul]
  intro h
  have h1 : ((M : ℝ) - 1) • (ΔAᵀ * U) = 0 := by rw [sub_smul, h, one_smul, sub_self]
  rcases smul_eq_zero.mp h1 with h2 | h2
  · exact hM (by exact_mod_cast sub_eq_zero.mp h2)
  · exact hB h2

/-- The entries of the estimator of eq. (4) of arXiv 2509.15113 are square integrable for Gaussian
probes. -/
theorem memLp_probeEst (w : ℝ) (ΔA : Matrix m n ℝ) (U : Matrix m (Fin r) ℝ) (a : n) (k : Fin r) :
    MemLp (fun Z => probeEst w Z ΔA U a k) 2 (gaussianProbes M n) := by
  simp only [probeEst_apply]
  exact memLp_sum_quad a _ w

/-- **Variance of the normalized estimator**: for independent `zⱼ ∼ N(0, I)` in `ℝ^{d_inp}`,
`E ‖(1 / M) ∑ⱼ zⱼ (ΔA zⱼ)ᵀ U - ΔAᵀ U‖_F² = (d_inp + 1) ‖ΔAᵀ U‖_F² / M`. This is not in the paper;
it says how large the error of the probes is, which Theorem 1 leaves open. -/
theorem integral_norm_sq_probeEst_sub (hM : 0 < M) (ΔA : Matrix m n ℝ)
    (U : Matrix m (Fin r) ℝ) :
    ∫ Z, ‖probeEst (1 / (M : ℝ)) Z ΔA U - ΔAᵀ * U‖ ^ 2 ∂gaussianProbes M n =
      (Fintype.card n + 1) * ‖ΔAᵀ * U‖ ^ 2 / M := by
  set B := ΔAᵀ * U with hB
  have e : ∀ Z : Fin M → n → ℝ, ‖probeEst (1 / (M : ℝ)) Z ΔA U - B‖ ^ 2 =
      ∑ a, ∑ k, ((1 / (M : ℝ)) * ∑ j, quad a (fun l => B l k) (Z j) - B a k) ^ 2 := by
    intro Z
    rw [Frobenius.norm_sq_eq_sum]
    simp only [Matrix.sub_apply, probeEst_apply, ← hB]
  have hi : ∀ (a : n) (k : Fin r), Integrable (fun Z : Fin M → n → ℝ =>
      ((1 / (M : ℝ)) * ∑ j, quad a (fun l => B l k) (Z j) - B a k) ^ 2) (gaussianProbes M n) :=
    fun a k => ((memLp_sum_quad a _ _).sub (memLp_const _)).integrable_sq
  simp only [e]
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun k _ => hi a k]
  simp_rw [integral_finsetSum _ fun k _ => hi _ k]
  have h1 := fun a k => integral_sq_sub_sum_quad hM a fun l => B l k
  simp only [h1]
  have h2 : ∑ a : n, ∑ k : Fin r, ∑ l, B l k ^ 2 = Fintype.card n * ‖B‖ ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum, Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun i j => B i j ^ 2)]
    simp
  have h3 : ∑ a : n, ∑ k : Fin r, B a k ^ 2 = ‖B‖ ^ 2 := (Frobenius.norm_sq_eq_sum B).symm
  calc ∑ a : n, ∑ k : Fin r, (∑ l, B l k ^ 2 + B a k ^ 2) / (M : ℝ)
      = (∑ a : n, ∑ k : Fin r, ∑ l, B l k ^ 2 + ∑ a : n, ∑ k : Fin r, B a k ^ 2) / M := by
        simp only [add_div, Finset.sum_add_distrib, Finset.sum_div]
    _ = _ := by rw [h2, h3]; ring

end Gaussian

/-! ### Theorem 1 -/

section Theorem1

variable {Ω n m : Type*} [Fintype m] [Fintype n] {r M : ℕ}
  {f : Ω → (n → ℝ) → (m → ℝ)} {A : Ω → Matrix m n ℝ}
  {qrL : Matrix m (Fin r) ℝ → Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ}
  {qrR : Matrix n (Fin r) ℝ → Matrix n (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ}
  {U₀ U₁ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
  {ΔA : Matrix m n ℝ} {ω₀ ω₁ : Ω} {w : ℝ}

/-- The basis of line 9 of Algorithm 1 of arXiv 2509.15113 is orthonormal. -/
theorem leftBasis_orth (hL : IsQRRoutine qrL) (hU₁ : leftBasis qrL U₀ S₀ V₀ ΔA = U₁) :
    U₁ᵀ * U₁ = 1 := by
  rw [← hU₁]; exact hL.orth _

/-- The basis of line 9 of Algorithm 1 of arXiv 2509.15113 captures `K₁ = U₀ S₀ + ΔA V₀`. -/
theorem leftBasis_capture (hL : IsQRRoutine qrL) (hU₁ : leftBasis qrL U₀ S₀ V₀ ΔA = U₁) :
    U₁ * U₁ᵀ * (U₀ * S₀ + ΔA * V₀) = U₀ * S₀ + ΔA * V₀ := by
  rw [← hU₁]
  exact mul_transpose_mul_eq_of_eq_mul (hL.orth _) (hL.fact _).symm

/-- Lines 8–21 of Algorithm 1 of arXiv 2509.15113 with the exact `P₂ = ΔAᵀ U₁` return
`U₁ U₁ᵀ (Y₀ + ΔA)`: this is one step of the projector-splitting integrator for `F(t, Y) = ΔA` on
`[0, 1]` (`Exactness.ksl_eq_proj`). -/
theorem surrogate_digitalPart_exact (hL : IsQRRoutine qrL) (hR : IsQRRoutine qrR)
    (hU₁ : leftBasis qrL U₀ S₀ V₀ ΔA = U₁) :
    surrogate (digitalPart qrL qrR U₀ S₀ V₀ ΔA (ΔAᵀ * U₁)) =
      U₁ * U₁ᵀ * (U₀ * S₀ * V₀ᵀ + ΔA) := by
  rw [surrogate_digitalPart hL hR, hU₁, sub_self, Matrix.transpose_zero, Matrix.mul_zero,
    add_zero]

/-- **Algorithm 1 of arXiv 2509.15113 on a linear box.** Whatever the probes `z`, the output is
`U₁ S₁ V₁ᵀ = U₁ U₁ᵀ (Y₀ + ΔA) + U₁ (P₂ - ΔAᵀ U₁)ᵀ`, the exact projector-splitting update plus the
error of the probes; `P₂` is the estimator of eq. (4). -/
theorem surrogate_run_ipsi (hf : ∀ ω x, f ω x = A ω *ᵥ x) (hL : IsQRRoutine qrL)
    (hR : IsQRRoutine qrR) (hΔ : A ω₁ - A ω₀ = ΔA) (hU₁ : leftBasis qrL U₀ S₀ V₀ ΔA = U₁)
    (z : Fin M → n → ℝ) :
    surrogate (run f (ipsi qrL qrR U₀ S₀ V₀ ω₀ ω₁ w z)) =
      U₁ * U₁ᵀ * (U₀ * S₀ * V₀ᵀ + ΔA) + U₁ * (probeEst w z ΔA U₁ - ΔAᵀ * U₁)ᵀ := by
  rw [run_ipsi hf, hΔ, hU₁, surrogate_digitalPart hL hR, hU₁]

/-- The factors returned by Algorithm 1 of arXiv 2509.15113 on a linear box: `U₁` is the basis of
line 9 (it does not depend on the probes), `U₁` and `V₁` are orthonormal, and the surrogate has
rank at most `r`. -/
theorem run_ipsi_factors (hf : ∀ ω x, f ω x = A ω *ᵥ x) (hL : IsQRRoutine qrL)
    (hR : IsQRRoutine qrR) (hΔ : A ω₁ - A ω₀ = ΔA) (hU₁ : leftBasis qrL U₀ S₀ V₀ ΔA = U₁)
    (z : Fin M → n → ℝ) :
    (run f (ipsi qrL qrR U₀ S₀ V₀ ω₀ ω₁ w z)).1 = U₁ ∧ U₁ᵀ * U₁ = 1 ∧
      (run f (ipsi qrL qrR U₀ S₀ V₀ ω₀ ω₁ w z)).2.2ᵀ *
        (run f (ipsi qrL qrR U₀ S₀ V₀ ω₀ ω₁ w z)).2.2 = 1 ∧
      (surrogate (run f (ipsi qrL qrR U₀ S₀ V₀ ω₀ ω₁ w z))).rank ≤ r := by
  rw [run_ipsi hf, hΔ, hU₁]
  exact ⟨hU₁, leftBasis_orth hL hU₁, hR.orth _, rank_mul_mul_transpose_le _ _ _⟩

/-- **Mean of the output of Algorithm 1 of arXiv 2509.15113**, for any law `ν` of the probes with
integrable estimator: `E[U₁ S₁ V₁ᵀ] = U₁ U₁ᵀ (Y₀ + ΔA) + U₁ (E[P₂] - ΔAᵀ U₁)ᵀ`. -/
theorem matE_ipsi (hf : ∀ ω x, f ω x = A ω *ᵥ x) (hL : IsQRRoutine qrL) (hR : IsQRRoutine qrR)
    (hΔ : A ω₁ - A ω₀ = ΔA) (hU₁ : leftBasis qrL U₀ S₀ V₀ ΔA = U₁)
    (ν : Measure (Fin M → n → ℝ)) [IsProbabilityMeasure ν]
    (hint : ∀ i j, Integrable (fun z => probeEst w z ΔA U₁ i j) ν) :
    matE ν (fun z => surrogate (run f (ipsi qrL qrR U₀ S₀ V₀ ω₀ ω₁ w z))) =
      U₁ * U₁ᵀ * (U₀ * S₀ * V₀ᵀ + ΔA) +
        U₁ * (matE ν (fun z => probeEst w z ΔA U₁) - ΔAᵀ * U₁)ᵀ := by
  simp only [surrogate_run_ipsi hf hL hR hΔ hU₁]
  exact matE_add_mul_transpose _ hint

/-- **The printed estimator breaks the first-order claim.** With `zⱼ ∼ N(0, I)` and the weight
`w = 1` of line 16 of Algorithm 1, the mean of the output is
`E[U₁ S₁ V₁ᵀ] = U₁ U₁ᵀ (Y₀ + ΔA) + (M - 1) U₁ U₁ᵀ ΔA`, which differs from the exact update at first
order in `ΔA` unless `M = 1`. Here `P₂` has mean `M ΔAᵀ U₁`, see `matE_probeEst_ne`. -/
theorem matE_ipsi_printed (hf : ∀ ω x, f ω x = A ω *ᵥ x) (hL : IsQRRoutine qrL)
    (hR : IsQRRoutine qrR) (hΔ : A ω₁ - A ω₀ = ΔA) (hU₁ : leftBasis qrL U₀ S₀ V₀ ΔA = U₁) :
    matE (gaussianProbes M n) (fun z => surrogate (run f (ipsi qrL qrR U₀ S₀ V₀ ω₀ ω₁ 1 z))) =
      U₁ * U₁ᵀ * (U₀ * S₀ * V₀ᵀ + ΔA) + ((M : ℝ) - 1) • (U₁ * U₁ᵀ * ΔA) := by
  have e : (M : ℝ) • (ΔAᵀ * U₁) - ΔAᵀ * U₁ = ((M : ℝ) - 1) • (ΔAᵀ * U₁) := by
    rw [sub_smul, one_smul]
  rw [matE_ipsi hf hL hR hΔ hU₁ _ fun i j =>
    (memLp_probeEst 1 ΔA U₁ i j).integrable (by norm_num), matE_probeEst, one_mul, e]
  simp only [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_smul, Matrix.mul_assoc]

variable [DecidableEq n]

/-- **Pathwise form of Theorem 1 of arXiv 2509.15113.** For every choice of the probes,
`‖U₁ S₁ V₁ᵀ - P(Y₀)(Y₀ + ΔA)‖_F ≤ ‖S₀⁻¹‖₂ ‖ΔA‖₂ ‖ΔA‖_F + ‖P₂ - ΔAᵀ U₁‖_F`. No assumption on the
probes is made: the second term is the actual error of the stochastic projection. -/
theorem norm_ipsi_sub_tangent_le (hf : ∀ ω x, f ω x = A ω *ᵥ x) (hL : IsQRRoutine qrL)
    (hR : IsQRRoutine qrR) (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hS : IsUnit S₀.det)
    (hΔ : A ω₁ - A ω₀ = ΔA) (hU₁ : leftBasis qrL U₀ S₀ V₀ ΔA = U₁) (z : Fin M → n → ℝ) :
    ‖surrogate (run f (ipsi qrL qrR U₀ S₀ V₀ ω₀ ω₁ w z)) -
        tangentProj U₀ V₀ (U₀ * S₀ * V₀ᵀ + ΔA)‖ ≤
      specNorm S₀⁻¹ * specNorm ΔA * ‖ΔA‖ + ‖probeEst w z ΔA U₁ - ΔAᵀ * U₁‖ := by
  have hO := leftBasis_orth hL hU₁
  have hb := norm_proj_sub_tangent_le' hU₀ hO hV₀ hS (leftBasis_capture hL hU₁)
  rw [surrogate_run_ipsi hf hL hR hΔ hU₁, add_sub_right_comm]
  refine (norm_add_le _ _).trans (add_le_add hb ?_)
  rw [Frobenius.norm_mul_of_orthonormal hO, Frobenius.norm_transpose]

/-- **Theorem 1 of arXiv 2509.15113.** Let the black box be linear, `f ω x = A ω x`, with increment
`ΔA = A ω₁ - A ω₀`, and let `Y₀ = U₀ S₀ V₀ᵀ` with orthonormal `U₀`, `V₀` and invertible `S₀`, so
that `Y₀` lies on the manifold `ℳ_r`. Assume the stochastic projection is unbiased: `ν` is a law of
the probes under which the estimator of eq. (4), with weight `w`, is integrable with mean
`ΔAᵀ U₁`. Then, for all probes, Algorithm 1 makes exactly `2 r + 2 M` forward queries and returns
orthonormal `U₁`, `V₁` with a surrogate of rank at most `r`, and its mean satisfies
`‖E[U₁ S₁ V₁ᵀ] - P(Y₀)(Y₀ + ΔA)‖_F ≤ ‖S₀⁻¹‖₂ ‖ΔA‖₂ ‖ΔA‖_F`, with `P(Y₀)` the orthogonal projector
onto the tangent space of `ℳ_r` at `Y₀`.

Differences from the paper. The paper gives no constant: here it is `‖S₀⁻¹‖₂ = σ_r(Y₀)⁻¹`, and
no smallness of `ΔA` is needed. The paper's "perturbed black-box matrix" is `Y₀ + ΔA`, the only
matrix the algorithm sees; see `norm_matE_ipsi_sub_tangent_box` for `A ω₁`. The conclusion holds
for the mean, not for each draw, see `integral_norm_sq_ipsi_sub_tangent_gaussian`. The hypothesis
holds for `w = 1 / M` (`matE_probeEst_normalized`), not for the printed `w = 1` when `M ≠ 1`
(`matE_probeEst_ne`). -/
theorem theorem_1 (hf : ∀ ω x, f ω x = A ω *ᵥ x) (hL : IsQRRoutine qrL) (hR : IsQRRoutine qrR)
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hS : IsUnit S₀.det)
    (hΔ : A ω₁ - A ω₀ = ΔA) (hU₁ : leftBasis qrL U₀ S₀ V₀ ΔA = U₁)
    (ν : Measure (Fin M → n → ℝ)) [IsProbabilityMeasure ν]
    (hint : ∀ i j, Integrable (fun z => probeEst w z ΔA U₁ i j) ν)
    (hunb : matE ν (fun z => probeEst w z ΔA U₁) = ΔAᵀ * U₁) :
    (∀ z : Fin M → n → ℝ, numQueries f (ipsi qrL qrR U₀ S₀ V₀ ω₀ ω₁ w z) = 2 * r + 2 * M) ∧
    (∀ z : Fin M → n → ℝ, (run f (ipsi qrL qrR U₀ S₀ V₀ ω₀ ω₁ w z)).1 = U₁ ∧ U₁ᵀ * U₁ = 1 ∧
      (run f (ipsi qrL qrR U₀ S₀ V₀ ω₀ ω₁ w z)).2.2ᵀ *
        (run f (ipsi qrL qrR U₀ S₀ V₀ ω₀ ω₁ w z)).2.2 = 1 ∧
      (surrogate (run f (ipsi qrL qrR U₀ S₀ V₀ ω₀ ω₁ w z))).rank ≤ r) ∧
    ‖matE ν (fun z => surrogate (run f (ipsi qrL qrR U₀ S₀ V₀ ω₀ ω₁ w z))) -
        tangentProj U₀ V₀ (U₀ * S₀ * V₀ᵀ + ΔA)‖ ≤
      specNorm S₀⁻¹ * specNorm ΔA * ‖ΔA‖ := by
  refine ⟨fun z => numQueries_ipsi f _ _ _ _ _ _ _ _ _,
    fun z => run_ipsi_factors hf hL hR hΔ hU₁ z, ?_⟩
  rw [matE_ipsi hf hL hR hΔ hU₁ ν hint, hunb, sub_self, Matrix.transpose_zero, Matrix.mul_zero,
    add_zero]
  exact norm_proj_sub_tangent_le' hU₀ (leftBasis_orth hL hU₁) hV₀ hS (leftBasis_capture hL hU₁)

/-- The conclusion of Theorem 1 of arXiv 2509.15113 for the matrix `A ω₁` of the box itself:
`‖E[U₁ S₁ V₁ᵀ] - P(Y₀) A(ω₁)‖_F ≤ ‖Y₀ - P(Y₀) A(ω₀)‖_F + ‖S₀⁻¹‖₂ ‖ΔA‖₂ ‖ΔA‖_F`. The first term
vanishes when `A(ω₀) - Y₀` is normal to `ℳ_r` at `Y₀`, for instance when `Y₀ = A(ω₀)`, and it does
not depend on `ΔA`: the algorithm cannot repair an initial defect, since it only sees `ΔA`. -/
theorem norm_matE_ipsi_sub_tangent_box (hf : ∀ ω x, f ω x = A ω *ᵥ x) (hL : IsQRRoutine qrL)
    (hR : IsQRRoutine qrR) (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hS : IsUnit S₀.det)
    (hΔ : A ω₁ - A ω₀ = ΔA) (hU₁ : leftBasis qrL U₀ S₀ V₀ ΔA = U₁)
    (ν : Measure (Fin M → n → ℝ)) [IsProbabilityMeasure ν]
    (hint : ∀ i j, Integrable (fun z => probeEst w z ΔA U₁ i j) ν)
    (hunb : matE ν (fun z => probeEst w z ΔA U₁) = ΔAᵀ * U₁) :
    ‖matE ν (fun z => surrogate (run f (ipsi qrL qrR U₀ S₀ V₀ ω₀ ω₁ w z))) -
        tangentProj U₀ V₀ (A ω₁)‖ ≤
      ‖U₀ * S₀ * V₀ᵀ - tangentProj U₀ V₀ (A ω₀)‖ + specNorm S₀⁻¹ * specNorm ΔA * ‖ΔA‖ := by
  have hb := (theorem_1 hf hL hR hU₀ hV₀ hS hΔ hU₁ ν hint hunb).2.2
  have e : tangentProj U₀ V₀ (A ω₁) = tangentProj U₀ V₀ (A ω₀) + tangentProj U₀ V₀ ΔA := by
    rw [← map_add, ← hΔ, add_sub_cancel]
  have e' : tangentProj U₀ V₀ (U₀ * S₀ * V₀ᵀ + ΔA) =
      U₀ * S₀ * V₀ᵀ + tangentProj U₀ V₀ ΔA := by
    rw [map_add, tangentProj_mul_mul_transpose hU₀]
  rw [e'] at hb
  rw [e]
  set E := matE ν (fun z => surrogate (run f (ipsi qrL qrR U₀ S₀ V₀ ω₀ ω₁ w z)))
  have e'' : E - (tangentProj U₀ V₀ (A ω₀) + tangentProj U₀ V₀ ΔA) =
      (U₀ * S₀ * V₀ᵀ - tangentProj U₀ V₀ (A ω₀)) +
        (E - (U₀ * S₀ * V₀ᵀ + tangentProj U₀ V₀ ΔA)) := by abel
  rw [e'']
  exact (norm_add_le _ _).trans (by gcongr)

/-- **Mean-square error of Algorithm 1 of arXiv 2509.15113**: under the hypotheses of `theorem_1`
with square-integrable estimator,
`E ‖U₁ S₁ V₁ᵀ - P(Y₀)(Y₀ + ΔA)‖_F² = ‖(U₁ U₁ᵀ - U₀ U₀ᵀ) ΔA (I - V₀ V₀ᵀ)‖_F² + E ‖P₂ - ΔAᵀ U₁‖_F²`:
the second-order bias and the variance of the probes add up. -/
theorem integral_norm_sq_ipsi_sub_tangent (hf : ∀ ω x, f ω x = A ω *ᵥ x) (hL : IsQRRoutine qrL)
    (hR : IsQRRoutine qrR) (hU₀ : U₀ᵀ * U₀ = 1)
    (hΔ : A ω₁ - A ω₀ = ΔA) (hU₁ : leftBasis qrL U₀ S₀ V₀ ΔA = U₁)
    (ν : Measure (Fin M → n → ℝ)) [IsProbabilityMeasure ν]
    (hint : ∀ i j, MemLp (fun z => probeEst w z ΔA U₁ i j) 2 ν)
    (hunb : matE ν (fun z => probeEst w z ΔA U₁) = ΔAᵀ * U₁) :
    ∫ z, ‖surrogate (run f (ipsi qrL qrR U₀ S₀ V₀ ω₀ ω₁ w z)) -
        tangentProj U₀ V₀ (U₀ * S₀ * V₀ᵀ + ΔA)‖ ^ 2 ∂ν =
      ‖(U₁ * U₁ᵀ - U₀ * U₀ᵀ) * ΔA * (1 - V₀ * V₀ᵀ)‖ ^ 2 +
        ∫ z, ‖probeEst w z ΔA U₁ - ΔAᵀ * U₁‖ ^ 2 ∂ν := by
  rw [← integral_norm_sq_add_perturbation _ (leftBasis_orth hL hU₁) hint hunb]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [surrogate_run_ipsi hf hL hR hΔ hU₁, add_sub_right_comm,
    proj_sub_tangent_eq hU₀ (leftBasis_capture hL hU₁)]

/-- **Second-moment form of Theorem 1 of arXiv 2509.15113 for the normalized Gaussian estimator**,
which is not in the paper. For independent `zⱼ ∼ N(0, I)` in `ℝ^{d_inp}` and weight `w = 1 / M`,
`E ‖U₁ S₁ V₁ᵀ - P(Y₀)(Y₀ + ΔA)‖_F² =
‖(U₁ U₁ᵀ - U₀ U₀ᵀ) ΔA (I - V₀ V₀ᵀ)‖_F² + (d_inp + 1) ‖ΔAᵀ U₁‖_F² / M`.
So a single draw of the surrogate is only `O(‖ΔA‖ √(d_inp / M))` accurate, in general first order
in `ΔA`: the bound `O(‖ΔA‖²)` of the paper holds for the mean and not for the realized surrogate. -/
theorem integral_norm_sq_ipsi_sub_tangent_gaussian (hM : 0 < M) (hf : ∀ ω x, f ω x = A ω *ᵥ x)
    (hL : IsQRRoutine qrL) (hR : IsQRRoutine qrR) (hU₀ : U₀ᵀ * U₀ = 1)
    (hΔ : A ω₁ - A ω₀ = ΔA) (hU₁ : leftBasis qrL U₀ S₀ V₀ ΔA = U₁) :
    ∫ z, ‖surrogate (run f (ipsi qrL qrR U₀ S₀ V₀ ω₀ ω₁ (1 / (M : ℝ)) z)) -
        tangentProj U₀ V₀ (U₀ * S₀ * V₀ᵀ + ΔA)‖ ^ 2 ∂gaussianProbes M n =
      ‖(U₁ * U₁ᵀ - U₀ * U₀ᵀ) * ΔA * (1 - V₀ * V₀ᵀ)‖ ^ 2 +
        (Fintype.card n + 1) * ‖ΔAᵀ * U₁‖ ^ 2 / M := by
  rw [integral_norm_sq_ipsi_sub_tangent hf hL hR hU₀ hΔ hU₁ _ (memLp_probeEst _ _ _)
    (matE_probeEst_normalized hM _ _), integral_norm_sq_probeEst_sub hM]

/-- With weight `w = 1 / M` and independent `zⱼ ∼ N(0, I)`, the hypotheses on the probes in
`theorem_1` hold, so the first-order bound of Theorem 1 of arXiv 2509.15113 holds unconditionally:
`‖E[U₁ S₁ V₁ᵀ] - P(Y₀)(Y₀ + ΔA)‖_F ≤ ‖S₀⁻¹‖₂ ‖ΔA‖₂ ‖ΔA‖_F`. -/
theorem theorem_1_gaussian (hM : 0 < M) (hf : ∀ ω x, f ω x = A ω *ᵥ x) (hL : IsQRRoutine qrL)
    (hR : IsQRRoutine qrR) (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hS : IsUnit S₀.det)
    (hΔ : A ω₁ - A ω₀ = ΔA) (hU₁ : leftBasis qrL U₀ S₀ V₀ ΔA = U₁) :
    ‖matE (gaussianProbes M n)
        (fun z => surrogate (run f (ipsi qrL qrR U₀ S₀ V₀ ω₀ ω₁ (1 / (M : ℝ)) z))) -
        tangentProj U₀ V₀ (U₀ * S₀ * V₀ᵀ + ΔA)‖ ≤
      specNorm S₀⁻¹ * specNorm ΔA * ‖ΔA‖ :=
  (theorem_1 hf hL hR hU₀ hV₀ hS hΔ hU₁ _
    (fun i j => (memLp_probeEst _ ΔA U₁ i j).integrable (by norm_num))
    (matE_probeEst_normalized hM _ _)).2.2

/-- The printed estimator misses the tangent projection at first order: with `w = 1` and
`zⱼ ∼ N(0, I)`, for `1 ≤ M`,
`(M - 1) ‖U₁ᵀ ΔA‖_F - ‖S₀⁻¹‖₂ ‖ΔA‖₂ ‖ΔA‖_F ≤ ‖E[U₁ S₁ V₁ᵀ] - P(Y₀)(Y₀ + ΔA)‖_F`.
So the conclusion of Theorem 1 of arXiv 2509.15113 fails for Algorithm 1 as printed when `M ≥ 2`,
unless `U₁ᵀ ΔA` is of second order. This does not contradict the theorem, whose hypothesis of
unbiasedness fails here, see `matE_probeEst_ne`. -/
theorem norm_matE_ipsi_printed_sub_tangent_ge (hM : 1 ≤ M) (hf : ∀ ω x, f ω x = A ω *ᵥ x)
    (hL : IsQRRoutine qrL) (hR : IsQRRoutine qrR) (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1)
    (hS : IsUnit S₀.det) (hΔ : A ω₁ - A ω₀ = ΔA) (hU₁ : leftBasis qrL U₀ S₀ V₀ ΔA = U₁) :
    ((M : ℝ) - 1) * ‖U₁ᵀ * ΔA‖ - specNorm S₀⁻¹ * specNorm ΔA * ‖ΔA‖ ≤
      ‖matE (gaussianProbes M n) (fun z => surrogate (run f (ipsi qrL qrR U₀ S₀ V₀ ω₀ ω₁ 1 z))) -
        tangentProj U₀ V₀ (U₀ * S₀ * V₀ᵀ + ΔA)‖ := by
  have hO := leftBasis_orth hL hU₁
  have hb := norm_proj_sub_tangent_le' hU₀ hO hV₀ hS (leftBasis_capture hL hU₁)
  have hM' : (0 : ℝ) ≤ (M : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast hM)
  have hn : ‖((M : ℝ) - 1) • (U₁ * U₁ᵀ * ΔA)‖ = ((M : ℝ) - 1) * ‖U₁ᵀ * ΔA‖ := by
    rw [norm_smul, Matrix.mul_assoc, Frobenius.norm_mul_of_orthonormal hO, Real.norm_eq_abs,
      abs_of_nonneg hM']
  rw [matE_ipsi_printed hf hL hR hΔ hU₁, add_sub_right_comm, ← hn]
  have h1 := norm_sub_norm_le (((M : ℝ) - 1) • (U₁ * U₁ᵀ * ΔA))
    (-(U₁ * U₁ᵀ * (U₀ * S₀ * V₀ᵀ + ΔA) - tangentProj U₀ V₀ (U₀ * S₀ * V₀ᵀ + ΔA)))
  rw [norm_neg, sub_neg_eq_add, add_comm (((M : ℝ) - 1) • _)] at h1
  linarith

/-- **The `σ_r`-free deterministic bound** for lines 8–21 with exact `P₂`, recorded for Theorem 1
of arXiv 2509.15113: if the doubly normal part of the increment satisfies
`‖(I - U₁ U₁ᵀ) ΔA (I - V₀ V₀ᵀ)‖_F ≤ ε`, then `‖U₁ S₁ V₁ᵀ - (Y₀ + ΔA)‖_F ≤ ε`, whatever `S₀` is.
By `proj_sub_add_eq` this is an equality with the normal part. It is the local error bound of
projector splitting with Lipschitz constant zero. -/
theorem norm_digitalPart_exact_sub_le [DecidableEq m] {ε : ℝ} (hL : IsQRRoutine qrL)
    (hR : IsQRRoutine qrR) (hU₁ : leftBasis qrL U₀ S₀ V₀ ΔA = U₁)
    (hε : ‖(1 - U₁ * U₁ᵀ) * ΔA * (1 - V₀ * V₀ᵀ)‖ ≤ ε) :
    ‖surrogate (digitalPart qrL qrR U₀ S₀ V₀ ΔA (ΔAᵀ * U₁)) - (U₀ * S₀ * V₀ᵀ + ΔA)‖ ≤ ε := by
  rw [surrogate_digitalPart_exact hL hR hU₁, proj_sub_add_eq (leftBasis_capture hL hU₁), norm_neg]
  exact hε

/-- Lines 8–21 of Algorithm 1 of arXiv 2509.15113 with exact `P₂` return a surrogate of rank exactly
`r` when `‖ΔA‖₂ < σ_r(Y₀)`, see `rank_proj_eq`. -/
theorem rank_digitalPart_exact (hL : IsQRRoutine qrL) (hR : IsQRRoutine qrR)
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hS : IsUnit S₀.det)
    (hsmall : specNorm S₀⁻¹ * specNorm ΔA < 1) (hU₁ : leftBasis qrL U₀ S₀ V₀ ΔA = U₁) :
    (surrogate (digitalPart qrL qrR U₀ S₀ V₀ ΔA (ΔAᵀ * U₁))).rank = r := by
  rw [surrogate_digitalPart_exact hL hR hU₁]
  exact rank_proj_eq hU₀ hV₀ hS hsmall (leftBasis_capture hL hU₁)

end Theorem1

/-! ### Sharpness -/

section Sharpness

/-- The first coordinate vector of `ℝ²`, as a matrix with one column. -/
def e₁ : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

/-- A `1 × 1` core. -/
def core (σ : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := !![σ]

/-- The symmetric increment `[[0, ε], [ε, 0]]`. It is tangent at `diag(σ, 0)`. -/
def tangentIncrement (ε : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, ε; ε, 0]

/-- An entry of `e₁`. -/
private theorem e₁_zero : e₁ 0 0 = 1 := rfl

/-- An entry of `e₁`. -/
private theorem e₁_one : e₁ 1 0 = 0 := rfl

/-- The entry of `core σ`. -/
private theorem core_apply (σ : ℝ) : core σ 0 0 = σ := rfl

/-- The entries of `tangentIncrement ε`. -/
private theorem tangentIncrement_apply (ε : ℝ) :
    tangentIncrement ε 0 0 = 0 ∧ tangentIncrement ε 0 1 = ε ∧ tangentIncrement ε 1 0 = ε ∧
      tangentIncrement ε 1 1 = 0 := ⟨rfl, rfl, rfl, rfl⟩

/-- `e₁` has orthonormal columns. -/
private theorem e₁_orth : e₁ᵀ * e₁ = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply, Fin.sum_univ_two, e₁_zero, e₁_one]

/-- **A tangent increment that is not reproduced; the second-order term is really there.** Take
`Y₀ = diag(σ, 0) = e₁ σ e₁ᵀ` with `σ > 0`, the increment `ΔA = [[0, ε], [ε, 0]]`, tangent at `Y₀`,
and any QR routines. Then the update of lines 8–21 with exact `P₂` satisfies
`‖U₁ S₁ V₁ᵀ - P(Y₀)(Y₀ + ΔA)‖_F = ε² / √(σ² + ε²)`.

This shows three things about Theorem 1 of arXiv 2509.15113. The rate `O(‖ΔA‖²)` cannot be
improved. The curvature constant is needed: `norm_proj_sub_tangent_le` gives `ε² / σ` here, which
is attained in the limit `ε / σ → 0`. And the sentence in the paper's proof that the
splitting integrator is "exact for updates lying within the tangent space" is false for `ε ≠ 0`.
The exactness of Lubich–Oseledets is for `Y₀ + ΔA` of rank `r`, not for tangent `ΔA`. -/
theorem tangent_increment_not_exact {σ ε : ℝ} (hσ : 0 < σ)
    {qrL : Matrix (Fin 2) (Fin 1) ℝ → Matrix (Fin 2) (Fin 1) ℝ × Matrix (Fin 1) (Fin 1) ℝ}
    {qrR : Matrix (Fin 2) (Fin 1) ℝ → Matrix (Fin 2) (Fin 1) ℝ × Matrix (Fin 1) (Fin 1) ℝ}
    (hL : IsQRRoutine qrL) (hR : IsQRRoutine qrR) {U₁ : Matrix (Fin 2) (Fin 1) ℝ}
    (hU₁ : leftBasis qrL e₁ (core σ) e₁ (tangentIncrement ε) = U₁) :
    tangentProj e₁ e₁ (tangentIncrement ε) = tangentIncrement ε ∧
      ‖surrogate (digitalPart qrL qrR e₁ (core σ) e₁ (tangentIncrement ε)
          ((tangentIncrement ε)ᵀ * U₁)) -
        tangentProj e₁ e₁ (e₁ * core σ * e₁ᵀ + tangentIncrement ε)‖ =
        ε ^ 2 / √(σ ^ 2 + ε ^ 2) := by
  obtain ⟨t00, t01, t10, t11⟩ := tangentIncrement_apply ε
  have hT : tangentProj e₁ e₁ (tangentIncrement ε) = tangentIncrement ε := by
    refine (tangentProj_eq_self_iff e₁_orth e₁_orth _).2
      ⟨e₁ᵀ * tangentIncrement ε, tangentIncrement ε * e₁, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, e₁_zero, e₁_one, t00, t01, t10, t11]
  refine ⟨hT, ?_⟩
  have hO := leftBasis_orth hL hU₁
  have hC := leftBasis_capture hL hU₁
  have hX : tangentProj e₁ e₁ (e₁ * core σ * e₁ᵀ + tangentIncrement ε) =
      e₁ * core σ * e₁ᵀ + tangentIncrement ε := by
    rw [map_add, tangentProj_mul_mul_transpose e₁_orth, hT]
  rw [surrogate_digitalPart_exact hL hR hU₁, hX]
  set p := U₁ 0 0 with hp
  set q := U₁ 1 0 with hq
  have h1 : p ^ 2 + q ^ 2 = 1 := by
    have := congrFun (congrFun hO 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, sq] using this
  have h2 : p * (p * σ + q * ε) = σ := by
    have := congrFun (congrFun hC 0) 0
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.transpose_apply, Fin.sum_univ_two,
      Fin.sum_univ_one, e₁_zero, e₁_one, core_apply, t00, t01, t10, t11] at this
    linear_combination this
  have h3 : q * (p * σ + q * ε) = ε := by
    have := congrFun (congrFun hC 1) 0
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.transpose_apply, Fin.sum_univ_two,
      Fin.sum_univ_one, e₁_zero, e₁_one, core_apply, t00, t01, t10, t11] at this
    linear_combination this
  set D := U₁ * U₁ᵀ * (e₁ * core σ * e₁ᵀ + tangentIncrement ε) -
    (e₁ * core σ * e₁ᵀ + tangentIncrement ε) with hD
  have d00 : D 0 0 = 0 := by
    simp only [hD, Matrix.sub_apply, Matrix.mul_apply, Matrix.add_apply, Matrix.transpose_apply,
      Fin.sum_univ_two, Fin.sum_univ_one, e₁_zero, e₁_one, core_apply, t00, t10]
    linear_combination h2
  have d01 : D 0 1 = (p ^ 2 - 1) * ε := by
    simp only [hD, Matrix.sub_apply, Matrix.mul_apply, Matrix.add_apply, Matrix.transpose_apply,
      Fin.sum_univ_two, Fin.sum_univ_one, e₁_zero, e₁_one, core_apply, t01, t11]
    ring
  have d10 : D 1 0 = 0 := by
    simp only [hD, Matrix.sub_apply, Matrix.mul_apply, Matrix.add_apply, Matrix.transpose_apply,
      Fin.sum_univ_two, Fin.sum_univ_one, e₁_zero, e₁_one, core_apply, t00, t10]
    linear_combination h3
  have d11 : D 1 1 = p * q * ε := by
    simp only [hD, Matrix.sub_apply, Matrix.mul_apply, Matrix.add_apply, Matrix.transpose_apply,
      Fin.sum_univ_two, Fin.sum_univ_one, e₁_zero, e₁_one, core_apply, t01, t11]
    ring
  have hn : ‖D‖ ^ 2 = ε ^ 2 * q ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum]
    simp only [Fin.sum_univ_two, d00, d01, d10, d11]
    linear_combination ε ^ 2 * (p ^ 2 - 1) * h1
  have ht : (p * σ + q * ε) ^ 2 = σ ^ 2 + ε ^ 2 := by
    linear_combination (-(p * σ + q * ε) ^ 2) * h1 + (p * (p * σ + q * ε) + σ) * h2 +
      (q * (p * σ + q * ε) + ε) * h3
  have hc : 0 < σ ^ 2 + ε ^ 2 := by positivity
  have hr := Real.sqrt_pos.mpr hc
  rw [eq_div_iff hr.ne']
  refine (sq_eq_sq₀ (by positivity) (by positivity)).1 ?_
  rw [mul_pow, hn, Real.sq_sqrt hc.le]
  linear_combination ε ^ 2 * (q * (p * σ + q * ε) + ε) * h3 - ε ^ 2 * q ^ 2 * ht

/-- Non-vacuity of `theorem_1`: QR routines exist, and the factors of
`tangent_increment_not_exact` satisfy the hypotheses. The hypotheses on the probes hold by
`theorem_1_gaussian`. -/
example {σ : ℝ} (hσ : 0 < σ) :
    (∃ qr : Matrix (Fin 2) (Fin 1) ℝ → Matrix (Fin 2) (Fin 1) ℝ × Matrix (Fin 1) (Fin 1) ℝ,
      IsQRRoutine qr) ∧ e₁ᵀ * e₁ = 1 ∧ IsUnit (core σ).det :=
  ⟨exists_isQRRoutine (by simp), e₁_orth, by simpa [core] using hσ.ne'⟩

end Sharpness

end LeanDLRA.Literature.P2509_15113
