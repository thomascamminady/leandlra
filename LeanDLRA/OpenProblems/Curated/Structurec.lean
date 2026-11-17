import LeanDLRA.Stability.Conservation
import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.ParallelBUG
import LeanDLRA.Integrators.ProjectorSplitting
import LeanDLRA.Integrators.RankAdaptiveBUG
import LeanDLRA.Matrix.Curvature

/-!
# Open problems OP-PA-11, OP-RA-30, OP-TN-27, OP-TR-09
-/

open Set
open scoped RealInnerProductSpace

namespace LeanDLRA

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Abstract

section Matrix

open Matrix
open scoped LeanDLRA.Frobenius

variable {m n k r : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype r] [DecidableEq m]
  [DecidableEq n] [DecidableEq k] [DecidableEq r]

omit [DecidableEq n] in
private theorem galerkin_S_eq {U : Matrix n k ℝ} (hU : Uᵀ * U = 1) (B : Matrix n n ℝ)
    (S : Matrix k k ℝ) :
    Uᵀ * (B * (U * S * Uᵀ) - U * S * Uᵀ * B) * U = (Uᵀ * B * U) * S - S * (Uᵀ * B * U) := by
  have h1 : Uᵀ * (B * (U * S * Uᵀ) - U * S * Uᵀ * B) * U
      = Uᵀ * B * U * S * (Uᵀ * U) - (Uᵀ * U) * S * (Uᵀ * B * U) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  rw [h1, hU]; simp

omit [Fintype m] [Fintype n] [Fintype r] [DecidableEq m] [DecidableEq n] [DecidableEq r] in
private theorem hasDerivWithinAt_pow_aux {S : ℝ → Matrix k k ℝ} {S' : Matrix k k ℝ} {s : Set ℝ}
    {t : ℝ} (h : HasDerivWithinAt S S' s t) (j : ℕ) :
    HasDerivWithinAt (fun t => S t ^ j)
      (∑ i ∈ Finset.range j, S t ^ i * S' * S t ^ (j - 1 - i)) s t := by
  induction j with
  | zero => simpa using hasDerivWithinAt_const t s (1 : Matrix k k ℝ)
  | succ j ih =>
    have hd := Frobenius.hasDerivWithinAt_mul ih h
    have e : ∀ i ∈ Finset.range j,
        S t ^ i * S' * S t ^ (j - 1 - i) * S t = S t ^ i * S' * S t ^ (j + 1 - 1 - i) := by
      intro i hi
      have hi' := Finset.mem_range.1 hi
      have : j + 1 - 1 - i = (j - 1 - i) + 1 := by omega
      rw [this, pow_succ, Matrix.mul_assoc _ (S t ^ (j - 1 - i))]
    have hf : (fun t => S t ^ (j + 1)) = fun t => S t ^ j * S t := by
      funext t; exact pow_succ _ _
    rw [hf]
    convert hd using 1
    rw [Finset.sum_range_succ, Finset.sum_mul, Finset.sum_congr rfl e]
    simp

omit [Fintype m] [Fintype n] [Fintype r] [DecidableEq m] [DecidableEq n] [DecidableEq r] in
private theorem trace_pow_comm_zero (X C : Matrix k k ℝ) (p : ℕ) :
    trace (X ^ p * (C * X - X * C)) = 0 := by
  have h1 : trace (X ^ p * (C * X)) = trace (X ^ (p + 1) * C) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← pow_succ']
  have h2 : trace (X ^ p * (X * C)) = trace (X ^ (p + 1) * C) := by
    rw [← Matrix.mul_assoc, ← pow_succ]
  rw [Matrix.mul_sub, Matrix.trace_sub, h1, h2, sub_self]

omit [DecidableEq n] in
/-- **The Galerkin S-step of an isospectral flow is isospectral** (source: research idea;
isospectral flows `Ȧ = [B(A), A]`, e.g. Toda and double-bracket flows). For `Y = U S Uᵀ` with
`Uᵀ U = 1`, the Galerkin S-step `Ṡ = Uᵀ [B(t, U S Uᵀ), U S Uᵀ] U` equals `[Uᵀ B U, S]`, so all
trace invariants `tr(Sʲ)` (hence the spectrum of `S`) are conserved. -/
theorem galerkin_isospectral_trace_pow {U : Matrix n k ℝ} (hU : Uᵀ * U = 1)
    {Bf : ℝ → Matrix n n ℝ → Matrix n n ℝ} {S : ℝ → Matrix k k ℝ} {a b : ℝ}
    (hS : ODESolution (fun t S => Uᵀ * (Bf t (U * S * Uᵀ) * (U * S * Uᵀ) -
      U * S * Uᵀ * Bf t (U * S * Uᵀ)) * U) S a b) (j : ℕ) :
    ∀ t ∈ Icc a b, trace (S t ^ j) = trace (S a ^ j) := by
  have hcont : ContinuousOn (fun t => trace (S t ^ j)) (Icc a b) := by
    have hmul : Continuous (fun p : Matrix k k ℝ × Matrix k k ℝ => p.1 * p.2) :=
      (Frobenius.mulCLM : Matrix k k ℝ →L[ℝ] Matrix k k ℝ →L[ℝ] Matrix k k ℝ).continuous₂
    have h1 : ∀ i : ℕ, ContinuousOn (fun t => S t ^ i) (Icc a b) := by
      intro i
      induction i with
      | zero => simpa using continuousOn_const
      | succ i ih =>
        simp only [pow_succ]
        have h2 := hmul.comp_continuousOn (ih.prodMk hS.cont)
        exact h2
    have h2 := (LinearMap.toContinuousLinearMap
      (Matrix.traceLinearMap k ℝ ℝ)).continuous.comp_continuousOn (h1 j)
    exact h2
  refine constant_of_has_deriv_right_zero hcont ?_
  intro x hx
  have h1 := hasDerivWithinAt_pow_aux (hS.deriv x hx) j
  let tr : Matrix k k ℝ →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (Matrix.traceLinearMap k ℝ ℝ)
  have h2 := tr.hasFDerivAt.comp_hasDerivWithinAt x h1
  have hz : ∀ i ∈ Finset.range j, trace (S x ^ i * (Uᵀ * (Bf x (U * S x * Uᵀ) *
      (U * S x * Uᵀ) - U * S x * Uᵀ * Bf x (U * S x * Uᵀ)) * U) * S x ^ (j - 1 - i)) = 0 := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    rw [galerkin_S_eq hU, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← pow_add,
      show j - 1 - i + i = j - 1 by omega]
    exact trace_pow_comm_zero _ _ _
  have htr : ∀ X, tr X = Matrix.trace X := fun X => rfl
  rw [htr, Matrix.trace_sum, Finset.sum_eq_zero hz] at h2
  exact h2

private theorem trace_conj_pow {U : Matrix n k ℝ} (hU : Uᵀ * U = 1) (S : Matrix k k ℝ) (j : ℕ) :
    trace ((U * S * Uᵀ) ^ (j + 1)) = trace (S ^ (j + 1)) := by
  have h : ∀ i : ℕ, (U * S * Uᵀ) ^ (i + 1) = U * S ^ (i + 1) * Uᵀ := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, ih, pow_succ S (i + 1)]
      calc U * S ^ (i + 1) * Uᵀ * (U * S * Uᵀ)
          = U * S ^ (i + 1) * (Uᵀ * U) * S * Uᵀ := by simp only [Matrix.mul_assoc]
        _ = U * (S ^ (i + 1) * S) * Uᵀ := by rw [hU]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [h, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

/-- **Augmented BUG conserves the spectrum of an isospectral flow before truncation** (source:
research idea, complementing arXiv 2104.05247, Thm 3). If the augmented basis `Û` (`Ûᵀ Û = 1`)
contains the column and row ranges of the starting value (`Û Ûᵀ Y₀ = Y₀ = Y₀ Û Ûᵀ`), then the
untruncated output `Ŷ₁ = Û Ŝ(t₁) Ûᵀ` of the Galerkin S-step for `Ẏ = [B(t, Y), Y]` satisfies
`tr(Ŷ₁ʲ) = tr(Y₀ʲ)` for all `j` (trivially for `j = 0`): the nonzero spectrum is conserved
exactly. (Fixed-rank BUG, whose basis need not contain `Y₀`, need not have this property.) -/
theorem augBug_isospectral {U : Matrix n k ℝ} (hU : Uᵀ * U = 1) {Y₀ : Matrix n n ℝ}
    (hY₀l : U * Uᵀ * Y₀ = Y₀) (hY₀r : Y₀ * (U * Uᵀ) = Y₀)
    {Bf : ℝ → Matrix n n ℝ → Matrix n n ℝ} {S : ℝ → Matrix k k ℝ} {a b : ℝ} (hab : a ≤ b)
    (hS : ODESolution (fun t S => Uᵀ * (Bf t (U * S * Uᵀ) * (U * S * Uᵀ) -
      U * S * Uᵀ * Bf t (U * S * Uᵀ)) * U) S a b) (hS₀ : S a = Uᵀ * Y₀ * U) (j : ℕ) :
    trace ((U * S b * Uᵀ) ^ j) = trace (Y₀ ^ j) := by
  have hb := galerkin_isospectral_trace_pow hU hS j b ⟨hab, le_rfl⟩
  have hY : Y₀ = U * (Uᵀ * Y₀ * U) * Uᵀ := by
    calc Y₀ = Y₀ * (U * Uᵀ) := hY₀r.symm
      _ = (U * Uᵀ * Y₀) * (U * Uᵀ) := by rw [hY₀l]
      _ = U * (Uᵀ * Y₀ * U) * Uᵀ := by simp only [Matrix.mul_assoc]
  cases j with
  | zero => simp
  | succ j =>
    rw [trace_conj_pow hU, hb, hS₀, hY, trace_conj_pow hU, ← hY]

omit [Fintype m] [Fintype n] [Fintype r] [DecidableEq m] [DecidableEq n] [DecidableEq r] in
private theorem exists_right_exp (N : Matrix k k ℝ) (a : ℝ) :
    ∃ Ψ : ℝ → Matrix k k ℝ, Ψ a = 1 ∧ ∀ t, HasDerivAt Ψ (Ψ t * N) t := by
  classical
  let x : (Matrix k k ℝ →L[ℝ] Matrix k k ℝ) :=
    (Frobenius.mulCLM : Matrix k k ℝ →L[ℝ] Matrix k k ℝ →L[ℝ] Matrix k k ℝ).flip N
  refine ⟨fun t => (NormedSpace.exp (((t - a) : ℝ) • x)) 1, by simp, fun t => ?_⟩
  have h1 := (hasDerivAt_exp_smul_const' x (t - a)).comp_sub_const t a
  have h2 := h1.clm_apply (hasDerivAt_const t (1 : Matrix k k ℝ))
  simpa [x] using h2

omit [Fintype m] [Fintype n] [Fintype r] [DecidableEq m] [DecidableEq n] [DecidableEq r] in
private theorem exists_left_exp (N : Matrix k k ℝ) (a : ℝ) :
    ∃ Φ : ℝ → Matrix k k ℝ, Φ a = 1 ∧ ∀ t, HasDerivAt Φ (N * Φ t) t := by
  classical
  let x : (Matrix k k ℝ →L[ℝ] Matrix k k ℝ) :=
    (Frobenius.mulCLM : Matrix k k ℝ →L[ℝ] Matrix k k ℝ →L[ℝ] Matrix k k ℝ) N
  refine ⟨fun t => (NormedSpace.exp (((t - a) : ℝ) • x)) 1, by simp, fun t => ?_⟩
  have h1 := (hasDerivAt_exp_smul_const' x (t - a)).comp_sub_const t a
  have h2 := h1.clm_apply (hasDerivAt_const t (1 : Matrix k k ℝ))
  simpa [x] using h2

omit [Fintype m] [Fintype n] [Fintype r] [DecidableEq m] [DecidableEq n] [DecidableEq r] in
private theorem mul_inv_of_exp {M : Matrix k k ℝ} {Ψ Φ : ℝ → Matrix k k ℝ} {a : ℝ}
    (hΨ : ∀ t, HasDerivAt Ψ (Ψ t * -M) t) (hΦ : ∀ t, HasDerivAt Φ (M * Φ t) t)
    (hΨa : Ψ a = 1) (hΦa : Φ a = 1) (t : ℝ) : Ψ t * Φ t = 1 := by
  have hd : ∀ t, HasDerivAt (fun t => Ψ t * Φ t) 0 t := by
    intro t
    have := Frobenius.hasDerivAt_mul (hΨ t) (hΦ t)
    convert this using 1
    simp [Matrix.mul_assoc]
  have := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) t a
  simpa [hΨa, hΦa] using this

omit [Fintype m] [Fintype n] [Fintype r] [DecidableEq m] [DecidableEq n] [DecidableEq r]
  [DecidableEq k] in
private theorem exists_quadCLM (v : k → ℝ) :
    ∃ q : Matrix k k ℝ →L[ℝ] ℝ, ∀ Z, q Z = v ⬝ᵥ (Z *ᵥ v) := by
  let f : Matrix k k ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun Z => v ⬝ᵥ (Z *ᵥ v)
      map_add' := fun Z Z' => by simp [Matrix.add_mulVec, dotProduct_add]
      map_smul' := fun c Z => by simp [Matrix.smul_mulVec, dotProduct_smul] }
  exact ⟨LinearMap.toContinuousLinearMap f, fun Z => rfl⟩

omit [Fintype m] [Fintype n] [Fintype r] [DecidableEq m] [DecidableEq n] [DecidableEq r]
  [DecidableEq k] in
private theorem posSemidef_of_deriv {Z : ℝ → Matrix k k ℝ} {D : ℝ → Matrix k k ℝ} {a b : ℝ}
    (hZ : ContinuousOn Z (Icc a b)) (hd : ∀ t ∈ Ico a b, HasDerivWithinAt Z (D t) (Ici t) t)
    (hD : ∀ t ∈ Ico a b, (D t).PosSemidef) (h0 : (Z a).PosSemidef) :
    ∀ t ∈ Icc a b, (Z t).PosSemidef := by
  have hsymm : ∀ t ∈ Icc a b, Z t - (Z t)ᵀ = Z a - (Z a)ᵀ := by
    refine constant_of_has_deriv_right_zero (f := fun t => Z t - (Z t)ᵀ) ?_ ?_
    · exact hZ.sub
        ((Frobenius.transposeCLM : Matrix k k ℝ →L[ℝ] Matrix k k ℝ).continuous.comp_continuousOn hZ)
    · intro t ht
      have := (hd t ht).sub (Frobenius.hasDerivWithinAt_transpose (hd t ht))
      have h2 : D t - (D t)ᵀ = 0 := by
        have := (hD t ht).isHermitian
        rw [sub_eq_zero]
        simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using this.symm
      rwa [h2] at this
  intro t ht
  have hherm : (Z t).IsHermitian := by
    have h1 := hsymm t ht
    have h2 : Z a - (Z a)ᵀ = 0 := by
      have := h0.isHermitian
      rw [sub_eq_zero]
      simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using this.symm
    rw [h2, sub_eq_zero] at h1
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using h1.symm
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm fun v => ?_
  obtain ⟨q, hq⟩ := exists_quadCLM v
  have hf : ContinuousOn (fun t => -q (Z t)) (Icc a b) := (q.continuous.comp_continuousOn hZ).neg
  have key := image_le_of_deriv_right_le_deriv_boundary (a := a) (b := b) hf
    (f' := fun t => -q (D t)) (B := fun _ => -q (Z a)) (B' := fun _ => 0)
    (fun t ht => ((q.hasFDerivAt.comp_hasDerivWithinAt t (hd t ht)).neg))
    le_rfl continuousOn_const (fun t _ => hasDerivWithinAt_const _ _ _)
    (fun t ht => by
      have := (hD t ht).dotProduct_mulVec_nonneg v
      rw [hq]
      simpa using this) ht
  have h0v := h0.dotProduct_mulVec_nonneg v
  simp only [hq, star_trivial] at key h0v ⊢
  linarith

omit [Fintype m] [Fintype n] [Fintype r] [DecidableEq m] [DecidableEq n] [DecidableEq r]
  [DecidableEq k] in
private theorem continuousOn_mul' {f g : ℝ → Matrix k k ℝ} {s : Set ℝ} (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) : ContinuousOn (fun t => f t * g t) s :=
  have h := ((Frobenius.mulCLM : Matrix k k ℝ →L[ℝ] Matrix k k ℝ →L[ℝ] Matrix k k ℝ).continuous₂
    ).comp_continuousOn (hf.prodMk hg)
  h

omit [DecidableEq n] in
/-- **The BUG S-step preserves positive semidefiniteness for differential Lyapunov equations**
(source: research idea; low-rank Lyapunov/Riccati DLRA, conservation with positivity). For
`Ẏ = A Y + Y Aᵀ + W` with `W ⪰ 0` and an orthonormal basis `U`, the Galerkin S-step
`Ṡ = Uᵀ (A (U S Uᵀ) + (U S Uᵀ) Aᵀ + W) U` started from `S(a) = Uᵀ Y₀ U` with `Y₀ ⪰ 0` keeps
`U S(t) Uᵀ ⪰ 0`. -/
theorem lyapunov_galerkin_posSemidef {U : Matrix n k ℝ} (hU : Uᵀ * U = 1)
    {A W Y₀ : Matrix n n ℝ} (hW : W.PosSemidef) (hY₀ : Y₀.PosSemidef) {S : ℝ → Matrix k k ℝ}
    {a b : ℝ}
    (hS : ODESolution (fun _ S => Uᵀ * (A * (U * S * Uᵀ) + U * S * Uᵀ * Aᵀ + W) * U) S a b)
    (hS₀ : S a = Uᵀ * Y₀ * U) :
    ∀ t ∈ Icc a b, (U * S t * Uᵀ).PosSemidef := by
  intro t ht
  have hR : (Uᵀ * W * U).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hW.conjTranspose_mul_mul_same U
  have hSd : ∀ x ∈ Ico a b, HasDerivWithinAt S
      (Uᵀ * A * U * S x + S x * (Uᵀ * A * U)ᵀ + Uᵀ * W * U) (Ici x) x := by
    intro x hx
    have h := hS.deriv x hx
    convert h using 1
    have : Uᵀ * (A * (U * S x * Uᵀ) + U * S x * Uᵀ * Aᵀ + W) * U
        = Uᵀ * A * U * S x * (Uᵀ * U) + (Uᵀ * U) * S x * (Uᵀ * Aᵀ * U) + Uᵀ * W * U := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    rw [this, hU]
    simp [Matrix.mul_assoc]
  obtain ⟨Ψ, hΨa, hΨ⟩ := exists_right_exp (-(Uᵀ * A * U)) a
  obtain ⟨Φ, hΦa, hΦ⟩ := exists_left_exp (Uᵀ * A * U) a
  have hinv := mul_inv_of_exp hΨ hΦ hΨa hΦa
  have hinv' : ∀ t, Φ t * Ψ t = 1 := fun t => mul_eq_one_comm.1 (hinv t)
  have hΨc : Continuous Ψ := continuous_iff_continuousAt.2 fun t => (hΨ t).continuousAt
  have hZc : ContinuousOn (fun t => Ψ t * S t * (Ψ t)ᵀ) (Icc a b) := by
    refine continuousOn_mul' (continuousOn_mul' hΨc.continuousOn hS.cont) ?_
    exact (Frobenius.transposeCLM : Matrix k k ℝ →L[ℝ] Matrix k k ℝ).continuous.comp_continuousOn
      hΨc.continuousOn
  have hZd : ∀ x ∈ Ico a b, HasDerivWithinAt (fun t => Ψ t * S t * (Ψ t)ᵀ)
      (Ψ x * (Uᵀ * W * U) * (Ψ x)ᵀ) (Ici x) x := by
    intro x hx
    have h := Frobenius.hasDerivWithinAt_mul_mul (hΨ x).hasDerivWithinAt (hSd x hx)
      (Frobenius.hasDerivWithinAt_transpose (hΨ x).hasDerivWithinAt)
    convert h using 1
    simp only [Matrix.transpose_mul, Matrix.transpose_neg, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    abel
  have hDp : ∀ x ∈ Ico a b, (Ψ x * (Uᵀ * W * U) * (Ψ x)ᵀ).PosSemidef := by
    intro x _
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hR.mul_mul_conjTranspose_same (Ψ x)
  have h0 : (Ψ a * S a * (Ψ a)ᵀ).PosSemidef := by
    rw [hΨa, hS₀]
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hY₀.conjTranspose_mul_mul_same U
  have hZ := posSemidef_of_deriv hZc hZd hDp h0 t ht
  have hSt : S t = Φ t * (Ψ t * S t * (Ψ t)ᵀ) * (Φ t)ᵀ := by
    have h1 : (Ψ t)ᵀ * (Φ t)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, hinv' t, Matrix.transpose_one]
    calc S t = (Φ t * Ψ t) * S t * ((Ψ t)ᵀ * (Φ t)ᵀ) := by rw [hinv' t, h1]; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  have hS2 : (S t).PosSemidef := by
    rw [hSt]
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hZ.mul_mul_conjTranspose_same (Φ t)
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hS2.mul_mul_conjTranspose_same U

omit [DecidableEq m] [DecidableEq n] [Fintype k] [DecidableEq k] in
private theorem ksl_core {U : Matrix m r ℝ} {V : Matrix n r ℝ} {T G : Matrix r r ℝ}
    {X : Matrix n r ℝ} {Y : Matrix m r ℝ} (hV : Vᵀ * V = 1) (hX : Xᵀ * V = 0)
    (hTG : T * G = 1) {σ : ℝ} (hG : Curvature.specNorm G ≤ σ) {P : Matrix m m ℝ}
    (hP : Curvature.IsOrthProjMat P)
    (hcap : P * ((U * T * Vᵀ + U * Xᵀ + Y * Vᵀ) * V) = (U * T * Vᵀ + U * Xᵀ + Y * Vᵀ) * V) :
    ‖P * (U * T * Vᵀ + U * Xᵀ + Y * Vᵀ) - (U * T * Vᵀ + U * Xᵀ + Y * Vᵀ)‖ ≤
      ‖Y‖ * σ * ‖X‖ := by
  classical
  have hZV : (U * T * Vᵀ + U * Xᵀ + Y * Vᵀ) * V = U * T + Y := by
    have : (U * T * Vᵀ + U * Xᵀ + Y * Vᵀ) * V = U * T * (Vᵀ * V) + U * (Xᵀ * V) + Y * (Vᵀ * V) := by
      simp only [Matrix.add_mul, Matrix.mul_assoc]
    rw [this, hV, hX]
    simp
  have h1 : (1 - P) * (U * T) = -((1 - P) * Y) := by
    have : (1 - P) * (U * T + Y) = 0 := by
      rw [← hZV, Matrix.sub_mul, Matrix.one_mul, hcap, sub_self]
    rw [Matrix.mul_add] at this
    exact eq_neg_of_add_eq_zero_left this
  have h2 : (1 - P) * U = -((1 - P) * Y * G) := by
    calc (1 - P) * U = (1 - P) * U * (T * G) := by rw [hTG, Matrix.mul_one]
      _ = ((1 - P) * (U * T)) * G := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.neg_mul, Matrix.mul_assoc]
  have h3 : (1 - P) * (U * T * Vᵀ + U * Xᵀ + Y * Vᵀ) = -((1 - P) * (Y * G * Xᵀ)) := by
    have e1 : (1 - P) * (U * T * Vᵀ) = -((1 - P) * Y) * Vᵀ := by
      rw [← h1, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    have e2 : (1 - P) * (U * Xᵀ) = -((1 - P) * (Y * G * Xᵀ)) := by
      rw [← Matrix.mul_assoc, h2]
      simp only [Matrix.neg_mul, Matrix.mul_assoc]
    rw [Matrix.mul_add, Matrix.mul_add, e1, e2]
    simp only [Matrix.neg_mul, Matrix.mul_assoc]
    abel
  have h4 : P * (U * T * Vᵀ + U * Xᵀ + Y * Vᵀ) - (U * T * Vᵀ + U * Xᵀ + Y * Vᵀ) =
      (1 - P) * (Y * G * Xᵀ) := by
    have : P * (U * T * Vᵀ + U * Xᵀ + Y * Vᵀ) - (U * T * Vᵀ + U * Xᵀ + Y * Vᵀ) =
        -((1 - P) * (U * T * Vᵀ + U * Xᵀ + Y * Vᵀ)) := by
      rw [Matrix.sub_mul, Matrix.one_mul]; abel
    rw [this, h3, neg_neg]
  rw [h4]
  calc ‖(1 - P) * (Y * G * Xᵀ)‖ ≤ ‖Y * G * Xᵀ‖ := hP.compl.norm_mul_le _
    _ ≤ Curvature.specNorm (Y * G) * ‖Xᵀ‖ := Curvature.frob_mul_le _ _
    _ ≤ ‖Y * G‖ * ‖X‖ := by
        rw [Frobenius.norm_transpose]
        exact mul_le_mul_of_nonneg_right (Curvature.specNorm_le_frob _) (norm_nonneg _)
    _ ≤ ‖Y‖ * Curvature.specNorm G * ‖X‖ :=
        mul_le_mul_of_nonneg_right (Curvature.frob_mul_le' _ _) (norm_nonneg _)
    _ ≤ ‖Y‖ * σ * ‖X‖ := by
        gcongr

omit [DecidableEq m] [DecidableEq n] in
private theorem ksl_inv {S₀ M : Matrix r r ℝ} {ρ : ℝ}
    (hS₀ : ∀ v : EuclideanSpace ℝ r, ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S₀ v‖)
    (hM : Curvature.specNorm M < ρ) :
    ∃ G : Matrix r r ℝ, (S₀ + M) * G = 1 ∧ G * (S₀ + M) = 1 ∧
      Curvature.specNorm G ≤ (ρ - Curvature.specNorm M)⁻¹ := by
  have hρ' : 0 < ρ - Curvature.specNorm M := sub_pos.2 hM
  have hb : ∀ v : EuclideanSpace ℝ r, (ρ - Curvature.specNorm M) * ‖v‖ ≤
      ‖Matrix.toEuclideanLin (S₀ + M) v‖ := by
    intro v
    have h1 := hS₀ v
    have h2 := Curvature.norm_toEuclideanLin_le M v
    have h3 : Matrix.toEuclideanLin S₀ v =
        Matrix.toEuclideanLin (S₀ + M) v - Matrix.toEuclideanLin M v := by
      rw [map_add]; simp
    have h4 := norm_sub_le (Matrix.toEuclideanLin (S₀ + M) v) (Matrix.toEuclideanLin M v)
    rw [← h3] at h4
    nlinarith
  have hdet := Curvature.isUnit_det_of_bounded_below hρ' hb
  exact ⟨(S₀ + M)⁻¹, Matrix.mul_nonsing_inv _ hdet, Matrix.nonsing_inv_mul _ hdet,
    Curvature.specNorm_inv_le hρ' hb⟩

omit [DecidableEq m] [DecidableEq n] in
/-- **One KSL step is a second-order retraction** (source: OP-TR-09; arXiv 1301.1058, §6;
proved in Absil–Oseledets 2015, Thm 3.3, as cited in arXiv 2309.06125, §3). Let
`A = U₀ S₀ V₀ᵀ` with orthonormal factors and `σ_min(S₀) ≥ ρ`, and let
`B = U₀ M V₀ᵀ + U₀ Xᵀ + Y V₀ᵀ` be tangent (`Xᵀ V₀ = 0`, `U₀ᵀ Y = 0`) with `‖M‖₂ < ρ`. If the new
left projector `P₁` captures the K-step value `(A + B) V₀`, the KSL output `P₁ (A + B)` for the
constant field `B` satisfies `‖P₁ (A + B) - (A + B)‖ ≤ ‖Y‖ ‖X‖ / (ρ - ‖M‖₂)`, i.e.
`O(‖B‖² / σ_r)`. -/
theorem ksl_retraction_error_le {U₀ : Matrix m r ℝ} {V₀ : Matrix n r ℝ} {S₀ M : Matrix r r ℝ}
    {X : Matrix n r ℝ} {Y : Matrix m r ℝ} (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1)
    (hX : Xᵀ * V₀ = 0) (hY : U₀ᵀ * Y = 0) {ρ : ℝ} (hρ : 0 < ρ)
    (hS₀ : ∀ v : EuclideanSpace ℝ r, ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S₀ v‖)
    (hM : Curvature.specNorm M < ρ) {P₁ : Matrix m m ℝ} (hP₁ : Curvature.IsOrthProjMat P₁)
    (hcap : P₁ * ((U₀ * S₀ * V₀ᵀ + (U₀ * M * V₀ᵀ + U₀ * Xᵀ + Y * V₀ᵀ)) * V₀) =
      (U₀ * S₀ * V₀ᵀ + (U₀ * M * V₀ᵀ + U₀ * Xᵀ + Y * V₀ᵀ)) * V₀) :
    ‖P₁ * (U₀ * S₀ * V₀ᵀ + (U₀ * M * V₀ᵀ + U₀ * Xᵀ + Y * V₀ᵀ)) -
        (U₀ * S₀ * V₀ᵀ + (U₀ * M * V₀ᵀ + U₀ * Xᵀ + Y * V₀ᵀ))‖ ≤
      ‖Y‖ * ‖X‖ / (ρ - Curvature.specNorm M) := by
  have _ := hU₀
  have _ := hY
  have _ := hρ
  obtain ⟨G, hTG, -, hG⟩ := ksl_inv hS₀ hM
  have hZ : U₀ * S₀ * V₀ᵀ + (U₀ * M * V₀ᵀ + U₀ * Xᵀ + Y * V₀ᵀ) =
      U₀ * (S₀ + M) * V₀ᵀ + U₀ * Xᵀ + Y * V₀ᵀ := by
    rw [Matrix.mul_add, Matrix.add_mul]; abel
  rw [hZ] at hcap ⊢
  have := ksl_core hV₀ hX hTG hG hP₁ hcap
  calc _ ≤ _ := this
    _ = _ := by field_simp

omit [DecidableEq m] [DecidableEq n] in
/-- **One BUG step is a second-order retraction** (source: arXiv 2309.06125, Prop. 1; OP-TR-09,
OP-TN-27). In the setting of `ksl_retraction_error_le`, if moreover the new right projector `Q₁`
captures the L-step value `(A + B)ᵀ U₀`, the BUG output `P₁ (A + B) Q₁` for the constant field `B`
satisfies `‖P₁ (A + B) Q₁ - (A + B)‖ ≤ 2 ‖Y‖ ‖X‖ / (ρ - ‖M‖₂)`. -/
theorem bug_retraction_error_le {U₀ : Matrix m r ℝ} {V₀ : Matrix n r ℝ} {S₀ M : Matrix r r ℝ}
    {X : Matrix n r ℝ} {Y : Matrix m r ℝ} (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1)
    (hX : Xᵀ * V₀ = 0) (hY : U₀ᵀ * Y = 0) {ρ : ℝ} (hρ : 0 < ρ)
    (hS₀ : ∀ v : EuclideanSpace ℝ r, ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S₀ v‖)
    (hM : Curvature.specNorm M < ρ) {P₁ : Matrix m m ℝ} (hP₁ : Curvature.IsOrthProjMat P₁)
    {Q₁ : Matrix n n ℝ} (hQ₁ : Curvature.IsOrthProjMat Q₁)
    (hcapP : P₁ * ((U₀ * S₀ * V₀ᵀ + (U₀ * M * V₀ᵀ + U₀ * Xᵀ + Y * V₀ᵀ)) * V₀) =
      (U₀ * S₀ * V₀ᵀ + (U₀ * M * V₀ᵀ + U₀ * Xᵀ + Y * V₀ᵀ)) * V₀)
    (hcapQ : Q₁ * ((U₀ * S₀ * V₀ᵀ + (U₀ * M * V₀ᵀ + U₀ * Xᵀ + Y * V₀ᵀ))ᵀ * U₀) =
      (U₀ * S₀ * V₀ᵀ + (U₀ * M * V₀ᵀ + U₀ * Xᵀ + Y * V₀ᵀ))ᵀ * U₀) :
    ‖P₁ * (U₀ * S₀ * V₀ᵀ + (U₀ * M * V₀ᵀ + U₀ * Xᵀ + Y * V₀ᵀ)) * Q₁ -
        (U₀ * S₀ * V₀ᵀ + (U₀ * M * V₀ᵀ + U₀ * Xᵀ + Y * V₀ᵀ))‖ ≤
      2 * (‖Y‖ * ‖X‖) / (ρ - Curvature.specNorm M) := by
  have _ := hρ
  obtain ⟨G, hTG, hGT, hG⟩ := ksl_inv hS₀ hM
  have hZ : U₀ * S₀ * V₀ᵀ + (U₀ * M * V₀ᵀ + U₀ * Xᵀ + Y * V₀ᵀ) =
      U₀ * (S₀ + M) * V₀ᵀ + U₀ * Xᵀ + Y * V₀ᵀ := by
    rw [Matrix.mul_add, Matrix.add_mul]; abel
  have hZt : (U₀ * (S₀ + M) * V₀ᵀ + U₀ * Xᵀ + Y * V₀ᵀ)ᵀ =
      V₀ * (S₀ + M)ᵀ * U₀ᵀ + V₀ * Yᵀ + X * U₀ᵀ := by
    simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc]
    abel
  rw [hZ] at hcapP hcapQ ⊢
  rw [hZt] at hcapQ
  have h1 := ksl_core hV₀ hX hTG hG hP₁ hcapP
  have hYU : Yᵀ * U₀ = 0 := by
    have := congrArg Matrix.transpose hY
    simpa [Matrix.transpose_mul] using this
  have hG' : Curvature.specNorm Gᵀ ≤ (ρ - Curvature.specNorm M)⁻¹ := by
    rw [Curvature.specNorm_transpose]; exact hG
  have hTG' : (S₀ + M)ᵀ * Gᵀ = 1 := by
    rw [← Matrix.transpose_mul, hGT, Matrix.transpose_one]
  have h2 := ksl_core (U := V₀) (V := U₀) (X := Y) (Y := X) hU₀ hYU hTG' hG' hQ₁ hcapQ
  rw [← hZt] at h2
  have h3 : ‖(U₀ * (S₀ + M) * V₀ᵀ + U₀ * Xᵀ + Y * V₀ᵀ) * Q₁ -
      (U₀ * (S₀ + M) * V₀ᵀ + U₀ * Xᵀ + Y * V₀ᵀ)‖ ≤
      ‖X‖ * (ρ - Curvature.specNorm M)⁻¹ * ‖Y‖ := by
    have e : (U₀ * (S₀ + M) * V₀ᵀ + U₀ * Xᵀ + Y * V₀ᵀ) * Q₁ -
        (U₀ * (S₀ + M) * V₀ᵀ + U₀ * Xᵀ + Y * V₀ᵀ) =
        (Q₁ * (U₀ * (S₀ + M) * V₀ᵀ + U₀ * Xᵀ + Y * V₀ᵀ)ᵀ -
          (U₀ * (S₀ + M) * V₀ᵀ + U₀ * Xᵀ + Y * V₀ᵀ)ᵀ)ᵀ := by
      rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose, hQ₁.symm]
    rw [e, Frobenius.norm_transpose]
    exact h2
  set Z := U₀ * (S₀ + M) * V₀ᵀ + U₀ * Xᵀ + Y * V₀ᵀ with hZdef
  have h4 := hQ₁.norm_mul_le' (P₁ * Z - Z)
  have e : P₁ * Z * Q₁ - Z = (P₁ * Z - Z) * Q₁ + (Z * Q₁ - Z) := by
    rw [Matrix.sub_mul]; abel
  rw [e]
  calc _ ≤ ‖(P₁ * Z - Z) * Q₁‖ + ‖Z * Q₁ - Z‖ := norm_add_le _ _
    _ ≤ ‖P₁ * Z - Z‖ + ‖Z * Q₁ - Z‖ := by gcongr
    _ ≤ ‖Y‖ * (ρ - Curvature.specNorm M)⁻¹ * ‖X‖ +
        ‖X‖ * (ρ - Curvature.specNorm M)⁻¹ * ‖Y‖ := add_le_add h1 h3
    _ = _ := by field_simp; ring

/-- **Second-order distance of a tangent step to the low-rank manifold** (source: OP-RA-30,
OP-PA-11; arXiv 2111.14540, §6; arXiv 2309.06125, §6). If `X = U S Vᵀ` with orthonormal `U`, `V`,
`σ_min(S) ≥ ρ > 0`, and `Z` is tangent at `X` (`(1 - U Uᵀ) Z (1 - V Vᵀ) = 0`), then some matrix
of rank at most `r` lies within `‖Z‖² / ρ` of `X + Z`. Hence the SVD retraction (equivalently, the
untruncated parallel BUG Euler step followed by truncation, `parallelBUG_euler`) is of second
order. -/
theorem exists_rank_le_norm_sub_le_sq {U : Matrix m r ℝ} {V : Matrix n r ℝ} {S : Matrix r r ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {ρ : ℝ} (hρ : 0 < ρ)
    (hS : ∀ v : EuclideanSpace ℝ r, ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖) {Z : Matrix m n ℝ}
    (hZ : (1 - U * Uᵀ) * Z * (1 - V * Vᵀ) = 0) :
    ∃ W : Matrix m n ℝ, W.rank ≤ Fintype.card r ∧ ‖U * S * Vᵀ + Z - W‖ ≤ ‖Z‖ ^ 2 / ρ := by
  have hdet := Curvature.isUnit_det_of_bounded_below hρ hS
  have hP : Curvature.IsOrthProjMat (U * Uᵀ) := Curvature.isOrthProjMat_mul_transpose hU
  have hQ : Curvature.IsOrthProjMat (V * Vᵀ) := Curvature.isOrthProjMat_mul_transpose hV
  have hXG : U * S * Vᵀ * (V * S⁻¹ * Uᵀ) = U * Uᵀ := Curvature.factor_mul_ginv hV hdet
  have hGX : V * S⁻¹ * Uᵀ * (U * S * Vᵀ) = V * Vᵀ := Curvature.ginv_mul_factor hU hdet
  have hXGX : U * S * Vᵀ * (V * S⁻¹ * Uᵀ) * (U * S * Vᵀ) = U * S * Vᵀ :=
    Curvature.factor_ginv_factor hU hV hdet
  have hZ' : Z * (1 - V * Vᵀ) = U * Uᵀ * Z * (1 - V * Vᵀ) := by
    have : (1 - U * Uᵀ) * Z * (1 - V * Vᵀ) = Z * (1 - V * Vᵀ) - U * Uᵀ * Z * (1 - V * Vᵀ) := by
      rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul]
    rw [hZ, eq_comm, sub_eq_zero] at this
    exact this
  have hT : U * S * Vᵀ + Z - (U * S * Vᵀ + Z * (V * Vᵀ)) * (V * S⁻¹ * Uᵀ) *
      (U * S * Vᵀ + U * Uᵀ * Z * (1 - V * Vᵀ)) =
      -(Z * (V * Vᵀ) * (V * S⁻¹ * Uᵀ) * (U * Uᵀ * Z * (1 - V * Vᵀ))) := by
    generalize U * S * Vᵀ = X at *
    generalize V * S⁻¹ * Uᵀ = G at *
    have hPP := hP.idem
    have hQQ := hQ.idem
    generalize U * Uᵀ = P at *
    generalize V * Vᵀ = Q at *
    have e : (X + Z * Q) * G * (X + P * Z * (1 - Q)) =
        X * G * X + X * G * (P * Z * (1 - Q)) + Z * Q * (G * X) +
        Z * Q * G * (P * Z * (1 - Q)) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
      abel
    have f1 : X * G * (P * Z * (1 - Q)) = P * Z * (1 - Q) := by
      rw [hXG, ← Matrix.mul_assoc P (P * Z), ← Matrix.mul_assoc P P, hPP]
    have f2 : Z * Q * (G * X) = Z * Q := by
      rw [hGX, Matrix.mul_assoc, hQQ]
    rw [e, hXGX, f1, f2, ← hZ', Matrix.mul_sub, Matrix.mul_one]
    abel
  have hWeq : (U * S * Vᵀ + Z * (V * Vᵀ)) * (V * S⁻¹ * Uᵀ) *
      (U * S * Vᵀ + U * Uᵀ * Z * (1 - V * Vᵀ)) =
      ((U * S * Vᵀ + Z * (V * Vᵀ)) * V * S⁻¹) *
        (Uᵀ * (U * S * Vᵀ + U * Uᵀ * Z * (1 - V * Vᵀ))) := by
    simp only [Matrix.mul_assoc]
  refine ⟨(U * S * Vᵀ + Z * (V * Vᵀ)) * (V * S⁻¹ * Uᵀ) *
      (U * S * Vᵀ + U * Uᵀ * Z * (1 - V * Vᵀ)), ?_, ?_⟩
  · rw [hWeq]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)
  · rw [hT, norm_neg]
    have hG := Curvature.specNorm_ginv_le hρ hU hV hS
    have hQn : ‖Z * (V * Vᵀ)‖ ≤ ‖Z‖ := hQ.norm_mul_le' Z
    have hPn1 : ‖U * Uᵀ * Z * (1 - V * Vᵀ)‖ ≤ ‖U * Uᵀ * Z‖ :=
      hQ.compl.norm_mul_le' (U * Uᵀ * Z)
    have hPn2 : ‖U * Uᵀ * Z‖ ≤ ‖Z‖ := hP.norm_mul_le Z
    have hPn : Curvature.specNorm (U * Uᵀ * Z * (1 - V * Vᵀ)) ≤ ‖Z‖ :=
      (Curvature.specNorm_le_frob _).trans (hPn1.trans hPn2)
    have hnn := Curvature.specNorm_nonneg (V * S⁻¹ * Uᵀ)
    have hnn' := Curvature.specNorm_nonneg (U * Uᵀ * Z * (1 - V * Vᵀ))
    calc ‖Z * (V * Vᵀ) * (V * S⁻¹ * Uᵀ) * (U * Uᵀ * Z * (1 - V * Vᵀ))‖
        ≤ ‖Z * (V * Vᵀ) * (V * S⁻¹ * Uᵀ)‖ *
          Curvature.specNorm (U * Uᵀ * Z * (1 - V * Vᵀ)) := Curvature.frob_mul_le' _ _
      _ ≤ (‖Z * (V * Vᵀ)‖ * Curvature.specNorm (V * S⁻¹ * Uᵀ)) * ‖Z‖ := by
          exact mul_le_mul_of_nonneg_right (Curvature.frob_mul_le' _ _) (by positivity) |>.trans
            (by gcongr)
      _ ≤ (‖Z‖ * ρ⁻¹) * ‖Z‖ := by gcongr
      _ = ‖Z‖ ^ 2 / ρ := by field_simp

end Matrix

end LeanDLRA
