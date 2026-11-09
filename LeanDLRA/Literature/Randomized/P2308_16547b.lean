import LeanDLRA.Literature.Foundations.P2008_07427a
import LeanDLRA.Literature.RankAdaptive.P2007_13153b
import LeanDLRA.Literature.Training.P2506_17475a

/-!
# Results of arXiv 2308.16547: Adaptive symplectic hyper-reduction (Proposition 3)

The a posteriori error bound of Proposition 3 for the symplectic dynamical low-rank approximation
of a parametric Hamiltonian system on `ℝ^{2N × p}` (Frobenius norm, `2N = ι ⊕ ι`, `2n = κ ⊕ κ`,
canonical `J = symplJ`).  With `∇H(W) = [∇H_{η_1}(W_1) | … | ∇H_{η_p}(W_p)]` (`gradH`),
`X_H = J_{2N} ∇H` (`XH`), the tangent projection (5) `projT` (shown equal to `tangentPi` of
arXiv 2008.07427, so it is a Frobenius-orthogonal projector for ortho-symplectic `A` and invertible
`M(Z)`), the indicator `r̃` (22) (`rTilde`) and the angle `θ` (20) (`theta`):

* `XH_lipschitz`: `X_H` is Lipschitz with `L = (∑_k ℓ_k²)^{1/2}` if each `X_{H_{η_k}}` is
  `ℓ_k`-Lipschitz;
* `rTilde_eq_norm_mul_sin`: `r̃(W) = ‖∇H(W)‖_F sin θ(W)` (the projector's orthogonality is
  derived, not assumed);
* `proposition_3`: `‖E(t)‖_F ≤ ‖E(t̄)‖_F e^{L(t-t̄)} + ∫_{t̄}^t r̃(W(τ)) e^{L(t-τ)} dτ`, and the
  integral equals `∫_{t̄}^t ‖∇H(W(τ))‖_F sin θ(W(τ)) e^{L(t-τ)} dτ`, with the time-dependent
  defect (Grönwall with integral forcing, `P2007_13153.error_bound_integral`); continuity of the
  defect is derived from continuity of the factors `A`, `Z`.

Scope: the paper states the bound for the "(hyper-)reduced" solution; its proof uses
`Ẇ = Π X_H(W)`, i.e. the reduced flow (4), and this formalization covers exactly that case.  The
hyper-reduced flow (24), whose velocity is built from the hyper-reduced Hamiltonian instead of
`Π X_H(W)`, is not formalized, and nothing is claimed about it here.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2308_16547

open LeanDLRA.Literature.P2008_07427

variable {ι κ p : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype p]

/-- The gradient matrix `∇H(W) = [∇H_{η_1}(W_1) | … | ∇H_{η_p}(W_p)] ∈ ℝ^{2N × p}` of eq. (2),
where `g k : ℝ^{2N} → ℝ^{2N}` is the gradient of the Hamiltonian `H_{η_k}` of the `k`-th
parameter and `W_k` is the `k`-th column of `W`. -/
def gradH (g : p → (ι ⊕ ι → ℝ) → (ι ⊕ ι → ℝ)) (W : Matrix (ι ⊕ ι) p ℝ) :
    Matrix (ι ⊕ ι) p ℝ :=
  Matrix.of fun i k => g k (fun j => W j k) i

/-- The Hamiltonian vector field `X_{H_{η_k}} = J_{2N} ∇H_{η_k}` of the `k`-th parameter. -/
def XHk (g : p → (ι ⊕ ι → ℝ) → (ι ⊕ ι → ℝ)) (k : p) (x : ι ⊕ ι → ℝ) : ι ⊕ ι → ℝ :=
  symplJ ι *ᵥ g k x

/-- The matrix-valued Hamiltonian vector field `X_H(W) = J_{2N} ∇H(W)` of eq. (2). -/
def XH (g : p → (ι ⊕ ι → ℝ) → (ι ⊕ ι → ℝ)) (W : Matrix (ι ⊕ ι) p ℝ) : Matrix (ι ⊕ ι) p ℝ :=
  symplJ ι * gradH g W

omit [Fintype p] in
/-- The `k`-th column of `X_H(W)` is `X_{H_{η_k}}(W_k)`. -/
lemma XH_apply (g : p → (ι ⊕ ι → ℝ) → (ι ⊕ ι → ℝ)) (W : Matrix (ι ⊕ ι) p ℝ) (i : ι ⊕ ι)
    (k : p) : XH g W i k = XHk g k (fun j => W j k) i := by
  simp [XH, XHk, gradH, Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- `M(Z) = Z Zᵀ + J_{2n}ᵀ Z Zᵀ J_{2n}` (after eq. (5)). -/
def Mmat (Z : Matrix (κ ⊕ κ) p ℝ) : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ :=
  Z * Zᵀ + (symplJ κ)ᵀ * (Z * Zᵀ) * symplJ κ

/-- The projection of eq. (5) onto the tangent space at `W = A Z`:
`Π(X) = (I_{2N} - A Aᵀ)(X Zᵀ + J_{2N} X Zᵀ J_{2n}ᵀ) M(Z)⁻¹ Z + A Aᵀ X`. -/
noncomputable def projT (A : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ) (Z : Matrix (κ ⊕ κ) p ℝ)
    (X : Matrix (ι ⊕ ι) p ℝ) : Matrix (ι ⊕ ι) p ℝ :=
  (1 - A * Aᵀ) * (X * Zᵀ + symplJ ι * X * Zᵀ * (symplJ κ)ᵀ) * (Mmat Z)⁻¹ * Z + A * Aᵀ * X

/-- The error indicator `r̃(W) = ‖X_H(W) - Π X_H(W)‖_F` of eq. (22), with `Π` the projection (5)
built from the factors `A`, `Z` of `W`. -/
noncomputable def rTilde (g : p → (ι ⊕ ι → ℝ) → (ι ⊕ ι → ℝ)) (A : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ)
    (Z : Matrix (κ ⊕ κ) p ℝ) (W : Matrix (ι ⊕ ι) p ℝ) : ℝ :=
  ‖XH g W - projT A Z (XH g W)‖

/-- The angle `θ(W) = arccos(‖Π X_H(W)‖_F / ‖X_H(W)‖_F)` of eq. (20) (with Lean's convention
`0 / 0 = 0`, so `θ = π/2` when `X_H(W) = 0`). -/
noncomputable def theta (g : p → (ι ⊕ ι → ℝ) → (ι ⊕ ι → ℝ)) (A : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ)
    (Z : Matrix (κ ⊕ κ) p ℝ) (W : Matrix (ι ⊕ ι) p ℝ) : ℝ :=
  Real.arccos (‖projT A Z (XH g W)‖ / ‖XH g W‖)

/-- `M(Z)` is the matrix `S` of arXiv 2008.07427, Prop. 4.3, for the transposed coefficients. -/
lemma Mmat_eq (Z : Matrix (κ ⊕ κ) p ℝ) : Mmat Z = Smat Zᵀ := by
  rw [Mmat, Smat, Matrix.transpose_transpose, symplJ_transpose_mul_mul]

/-- The projection (5) is the projection `tangentPi` of arXiv 2008.07427, Prop. 4.3, written
for the transposed coefficient matrix. -/
lemma projT_eq (A : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ) (Z : Matrix (κ ⊕ κ) p ℝ)
    (X : Matrix (ι ⊕ ι) p ℝ) : projT A Z X = tangentPi A Zᵀ X := by
  simp [projT, tangentPi, Fmat, Mmat_eq, Matrix.mul_assoc]

omit [Fintype κ] [DecidableEq κ] in
/-- `‖X_H(W)‖_F = ‖∇H(W)‖_F`, since `J_{2N}` is orthogonal. -/
lemma norm_XH (g : p → (ι ⊕ ι → ℝ) → (ι ⊕ ι → ℝ)) (W : Matrix (ι ⊕ ι) p ℝ) :
    ‖XH g W‖ = ‖gradH g W‖ :=
  Frobenius.norm_mul_of_orthonormal symplJ_transpose_mul _

/-- **arXiv 2308.16547, Proposition 3, second line (the identity `r̃ = ‖∇H‖_F sin θ`).**
For an ortho-symplectic `A` and `Z` with `M(Z)` invertible,
`r̃(W) = ‖∇H(W)‖_F sin(θ(W))`.  The paper justifies this by "`Π` is an orthogonal projection with
respect to the Frobenius norm"; here this is derived (`isOrthProj_tangentPi`), together with
`‖J_{2N} ∇H‖_F = ‖∇H‖_F`. -/
theorem rTilde_eq_norm_mul_sin (g : p → (ι ⊕ ι → ℝ) → (ι ⊕ ι → ℝ))
    {A : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ} {Z : Matrix (κ ⊕ κ) p ℝ} (hA : IsOrthosymplectic A)
    (hM : IsUnit (Mmat Z).det) (W : Matrix (ι ⊕ ι) p ℝ) :
    rTilde g A Z W = ‖gradH g W‖ * Real.sin (theta g A Z W) := by
  have hP := isOrthProj_tangentPi hA (Z := Zᵀ) (by rwa [← Mmat_eq])
  have h1 := hP.norm_sq_add (XH g W)
  simp only [tangentPiCLM_apply] at h1
  rw [rTilde, theta, projT_eq, ← norm_XH, Real.sin_arccos]
  set a := ‖XH g W‖ with ha
  set b := ‖tangentPi A Zᵀ (XH g W)‖ with hb
  set c := ‖XH g W - tangentPi A Zᵀ (XH g W)‖ with hc
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hc0 : 0 ≤ c := norm_nonneg _
  rcases eq_or_lt_of_le ha0 with h0 | hpos
  · rw [← h0, zero_mul]
    nlinarith
  · have e : c = √(a ^ 2 * (1 - (b / a) ^ 2)) := by
      rw [show a ^ 2 * (1 - (b / a) ^ 2) = c ^ 2 by field_simp; linarith, Real.sqrt_sq hc0]
    rw [e, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha0]

/-- **arXiv 2308.16547, Proposition 3, the Lipschitz constant.**  If each parameter's
Hamiltonian vector field `X_{H_{η_k}}` is `ℓ_k`-Lipschitz for the Euclidean norm of `ℝ^{2N}`,
then the matrix field `X_H` is Lipschitz for the Frobenius norm with constant
`L = (∑_k ℓ_k²)^{1/2}`. -/
theorem XH_lipschitz {g : p → (ι ⊕ ι → ℝ) → (ι ⊕ ι → ℝ)} {ℓ : p → ℝ}
    (hℓ : ∀ k x y, √(∑ i, (XHk g k x i - XHk g k y i) ^ 2) ≤ ℓ k * √(∑ i, (x i - y i) ^ 2)) :
    IsLipschitzField (fun _ => XH g) √(∑ k, ℓ k ^ 2) := by
  intro _ W V
  have hsq : ∀ k, ∑ i, (XHk g k (fun j => W j k) i - XHk g k (fun j => V j k) i) ^ 2 ≤
      ℓ k ^ 2 * ∑ i, (W i k - V i k) ^ 2 := by
    intro k
    have h := hℓ k (fun j => W j k) (fun j => V j k)
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
    rwa [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), mul_pow,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at this
  have hcol : ∀ k, ∑ i, (W i k - V i k) ^ 2 ≤ ‖W - V‖ ^ 2 := by
    intro k
    rw [Frobenius.norm_sq_eq_sum, Finset.sum_comm]
    simp only [Matrix.sub_apply]
    exact Finset.single_le_sum (f := fun k => ∑ i, (W i k - V i k) ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ k)
  have key : ‖XH g W - XH g V‖ ^ 2 ≤ (√(∑ k, ℓ k ^ 2) * ‖W - V‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      Frobenius.norm_sq_eq_sum, Finset.sum_comm, Finset.sum_mul]
    refine Finset.sum_le_sum fun k _ => ?_
    simp only [Matrix.sub_apply, XH_apply]
    exact (hsq k).trans (mul_le_mul_of_nonneg_left (hcol k) (sq_nonneg _))
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) two_ne_zero).1 key

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype p] in
private lemma continuousOn_mmul {m n o : Type*} [Fintype m] [Fintype n] [Fintype o]
    {f : ℝ → Matrix m n ℝ} {h : ℝ → Matrix n o ℝ} {s : Set ℝ} (hf : ContinuousOn f s)
    (hh : ContinuousOn h s) : ContinuousOn (fun t => f t * h t) s :=
  (continuous_fst.matrix_mul continuous_snd).comp_continuousOn (hf.prodMk hh)

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype p] in
private lemma continuousOn_transpose {m n : Type*} [Fintype m] [Fintype n]
    {f : ℝ → Matrix m n ℝ} {s : Set ℝ} (hf : ContinuousOn f s) :
    ContinuousOn (fun t => (f t)ᵀ) s :=
  continuous_id.matrix_transpose.comp_continuousOn hf

/-- The indicator `t ↦ r̃(W(t))` is continuous along continuous factors with `M(Z)` invertible. -/
lemma continuousOn_rTilde {g : p → (ι ⊕ ι → ℝ) → (ι ⊕ ι → ℝ)} (hX : Continuous (XH g))
    {A : ℝ → Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ} {Z : ℝ → Matrix (κ ⊕ κ) p ℝ}
    {W : ℝ → Matrix (ι ⊕ ι) p ℝ} {s : Set ℝ} (hAc : ContinuousOn A s) (hZc : ContinuousOn Z s)
    (hWc : ContinuousOn W s) (hM : ∀ t ∈ s, IsUnit (Mmat (Z t)).det) :
    ContinuousOn (fun t => rTilde g (A t) (Z t) (W t)) s := by
  have hXc : ContinuousOn (fun t => XH g (W t)) s := hX.comp_continuousOn hWc
  have hAt := continuousOn_transpose hAc
  have hZt := continuousOn_transpose hZc
  have hMc : ContinuousOn (fun t => Mmat (Z t)) s := by
    unfold Mmat
    exact (continuousOn_mmul hZc hZt).add (continuousOn_mmul (continuousOn_mmul
      continuousOn_const (continuousOn_mmul hZc hZt)) continuousOn_const)
  have hMi := P2506_17475.continuousOn_matrix_inv hMc hM
  have hAA := continuousOn_mmul hAc hAt
  have hP : ContinuousOn (fun t => projT (A t) (Z t) (XH g (W t))) s := by
    unfold projT
    refine (continuousOn_mmul (continuousOn_mmul (continuousOn_mmul
      (continuousOn_const.sub hAA) ((continuousOn_mmul hXc hZt).add (continuousOn_mmul
        (continuousOn_mmul (continuousOn_mmul continuousOn_const hXc) hZt) continuousOn_const)))
      hMi) hZc).add (continuousOn_mmul hAA hXc)
  exact (hXc.sub hP).norm

/-- **arXiv 2308.16547, Proposition 3 (a posteriori error bound).**  Let `X_{H_{η_k}}` be
`ℓ_k`-Lipschitz (Euclidean norm on `ℝ^{2N}`) for every parameter, `L = (∑_k ℓ_k²)^{1/2}`, let `𝒲`
solve the full order model (2) `𝒲̇ = X_H(𝒲)` on `[t̄, T]`, and let the reduced state `W` solve the
reduced dynamics (4) `Ẇ = Π_{T_W 𝓜_n} X_H(W)` on `[t̄, T]`, where the projection is given by
formula (5) with continuous factors `A(t)` (ortho-symplectic) and `Z(t)` (with `M(Z(t))`
invertible).  Then for every `t ∈ [t̄, T]`, with `E = 𝒲 - W`,
`‖E(t)‖_F ≤ ‖E(t̄)‖_F e^{L(t-t̄)} + ∫_{t̄}^t r̃(W(τ)) e^{L(t-τ)} dτ`, and the integral equals
`∫_{t̄}^t ‖∇H(W(τ))‖_F sin(θ(W(τ))) e^{L(t-τ)} dτ`.

Differences from the paper: the paper says "(hyper-)reduced"; this theorem (like the paper's
proof, which uses `Ẇ = Π X_H(W)`) is for the reduced flow (4)/(6) only; the hyper-reduced
flow (24) is not covered.  The factorization
`W = A Z` is not needed: any continuous `A`, `Z` defining the projector along `W` will do, in
particular those of (6).  Solutions are only required to be continuous with right derivatives;
the gradients `∇H_{η_k}` are arbitrary maps (their only use is through the Lipschitz bound and
the identity `X_H = J_{2N} ∇H`). -/
theorem proposition_3 {g : p → (ι ⊕ ι → ℝ) → (ι ⊕ ι → ℝ)} {ℓ : p → ℝ}
    (hℓ : ∀ k x y, √(∑ i, (XHk g k x i - XHk g k y i) ^ 2) ≤ ℓ k * √(∑ i, (x i - y i) ^ 2))
    {A : ℝ → Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ} {Z : ℝ → Matrix (κ ⊕ κ) p ℝ} {tbar T : ℝ}
    (hA : ∀ t ∈ Icc tbar T, IsOrthosymplectic (A t))
    (hM : ∀ t ∈ Icc tbar T, IsUnit (Mmat (Z t)).det)
    (hAc : ContinuousOn A (Icc tbar T)) (hZc : ContinuousOn Z (Icc tbar T))
    {Wfull W : ℝ → Matrix (ι ⊕ ι) p ℝ}
    (hfull : ODESolution (fun _ x => XH g x) Wfull tbar T)
    (hred : ODESolution (fun t x => projT (A t) (Z t) (XH g x)) W tbar T) :
    ∀ t ∈ Icc tbar T,
      ‖Wfull t - W t‖ ≤ ‖Wfull tbar - W tbar‖ * Real.exp (√(∑ k, ℓ k ^ 2) * (t - tbar)) +
        ∫ τ in tbar..t, rTilde g (A τ) (Z τ) (W τ) * Real.exp (√(∑ k, ℓ k ^ 2) * (t - τ)) ∧
      ∫ τ in tbar..t, rTilde g (A τ) (Z τ) (W τ) * Real.exp (√(∑ k, ℓ k ^ 2) * (t - τ)) =
        ∫ τ in tbar..t, ‖gradH g (W τ)‖ * Real.sin (theta g (A τ) (Z τ) (W τ)) *
          Real.exp (√(∑ k, ℓ k ^ 2) * (t - τ)) := by
  intro t ht
  have hLip := XH_lipschitz hℓ
  have hXc : Continuous (XH g) :=
    (LipschitzWith.of_dist_le_mul (K := ⟨√(∑ k, ℓ k ^ 2), Real.sqrt_nonneg _⟩) fun x y => by
      rw [dist_eq_norm, dist_eq_norm]; exact hLip 0 x y).continuous
  have hred' : ODESolution (fun t x => tangentPiCLM (A t) (Z t)ᵀ (XH g x)) W tbar T := by
    simpa only [projT_eq, tangentPiCLM_apply] using hred
  have hdef : ContinuousOn (fun s => ‖(1 - tangentPiCLM (A s) (Z s)ᵀ) (XH g (W s))‖)
      (Icc tbar T) :=
    (continuousOn_rTilde hXc hAc hZc hred.cont hM).congr fun s _ => by
      simp [rTilde, projT_eq]
  refine ⟨?_, ?_⟩
  · have h := P2007_13153.error_bound_integral hLip hfull hred' hdef t ht
    have e : ∀ s, Real.exp (√(∑ k, ℓ k ^ 2) * (t - s)) *
        ‖(1 - tangentPiCLM (A s) (Z s)ᵀ) (XH g (W s))‖ =
        rTilde g (A s) (Z s) (W s) * Real.exp (√(∑ k, ℓ k ^ 2) * (t - s)) := fun s => by
      simp [rTilde, projT_eq, mul_comm]
    simp only [e] at h
    rw [norm_sub_rev, norm_sub_rev (Wfull tbar), mul_comm (‖W tbar - Wfull tbar‖)]
    exact h
  · refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [uIcc_of_le ht.1] at hτ
    have hτ' : τ ∈ Icc tbar T := ⟨hτ.1, hτ.2.trans ht.2⟩
    simp only [rTilde_eq_norm_mul_sin g (hA τ hτ') (hM τ hτ')]

/-- Non-vacuity: with `N = n = 1`, `p = 2`, `A = I_2` (ortho-symplectic) and `Z = I_2`
(`M(Z) = 2 I` invertible) all hypotheses of `proposition_3` are met, here for `∇H = 0` and
constant solutions. -/
example := proposition_3 (ι := Fin 1) (κ := Fin 1) (p := Fin 1 ⊕ Fin 1) (g := fun _ _ => 0)
    (ℓ := fun _ => 0) (A := fun _ => 1) (Z := fun _ => 1) (tbar := 0) (T := 1)
    (Wfull := fun _ => 0) (W := fun _ => 0)
    (fun _ _ _ => by simp [XHk])
    (fun _ _ => ⟨by simp, by simp⟩)
    (fun _ _ => by
      have : Mmat (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) = (2 : ℝ) • 1 := by
        simp [Mmat, symplJ_transpose_mul, two_smul]
      rw [this, Matrix.det_smul, Matrix.det_one, mul_one]
      exact (pow_ne_zero _ two_ne_zero).isUnit)
    continuousOn_const continuousOn_const
    ⟨continuousOn_const, fun t _ => by
      have h0 : XH (fun (_ : Fin 1 ⊕ Fin 1) (_ : Fin 1 ⊕ Fin 1 → ℝ) => (0 : Fin 1 ⊕ Fin 1 → ℝ))
          0 = 0 := by ext i j; simp [XH, gradH, Matrix.mul_apply]
      simpa [h0] using hasDerivWithinAt_const t (Ici t)
        (0 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)⟩
    ⟨continuousOn_const, fun t _ => by
      have h0 : XH (fun (_ : Fin 1 ⊕ Fin 1) (_ : Fin 1 ⊕ Fin 1 → ℝ) => (0 : Fin 1 ⊕ Fin 1 → ℝ))
          0 = 0 := by ext i j; simp [XH, gradH, Matrix.mul_apply]
      simpa [h0, projT] using hasDerivWithinAt_const t (Ici t)
        (0 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)⟩

end LeanDLRA.Literature.P2308_16547
