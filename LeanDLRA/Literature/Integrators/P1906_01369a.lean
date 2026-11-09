import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Foundations.ODE
import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.Exactness
import LeanDLRA.Integrators.KStep
import LeanDLRA.Integrators.Matrix.BUG
import LeanDLRA.Integrators.Matrix.Symmetry
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 1906.01369: Symmetric and skew-symmetric low-rank integrators

Ceruti–Lubich, *Time integration of symmetric and anti-symmetric low-rank matrices and Tucker
tensors*.  Throughout `σ = 1` (symmetric) or `σ = -1` (skew-symmetric) is handled uniformly via
`LeanDLRA.Symmetry.IsTwistSymm`, and `MapsTwistSymm σ F` is the paper's condition (5) that `F`
maps (skew-)symmetric matrices to (skew-)symmetric matrices (weaker than the twist-equivariance
used in `LeanDLRA.Symmetry`).  This module proves:

* `isTwistSymm_of_odeSolution_of_maps`: under (5) and a Lipschitz bound the exact flow preserves
  (skew-)symmetry (Gronwall argument on the non-symmetric part).
* `algorithm1_isTwistSymm` (`algorithm1_symmetric`, `algorithm1_skew`): **Algorithm 1** preserves
  (skew-)symmetry with a single K-step and no L-step, for every new basis `U₁`.
* `theorem3_exact`: **Theorem 3** exactness of Algorithm 1 for `F = Ȧ`.
* `two_sided_projection_error`: **Lemma 1** (second half of its proof),
  `‖U₁U₁ᵀA₁U₁U₁ᵀ − A₁‖ ≤ 2θ` from `‖(I − U₁U₁ᵀ)A₁‖ ≤ θ` and (skew-)symmetry of `A₁`; with
  `IsSymStep.capture_left` (`θ = h(4LBh + ε)`, smaller than the paper's `ϑ(h, ε)`) this gives
  Lemma 1.
* `IsSymStep` and `IsSymStep.capture_left`, `.local_error`, `.local_error_le`,
  `global_error`, `global_error_le`: **Lemma 2 and Theorem 4**, the robust local error
  `h(c₁ε + c₂h)` and global error `c₀δ + c₁ε + c₂h` of Algorithm 1, independent of small
  singular values; the (skew-)symmetry of the exact flows and of all iterates is derived, not
  assumed (`isTwistSymm_iterate`).  The hypotheses on `F` are global: `F` is Lipschitz and
  bounded for all `t`, and the normal-component bound (`MatrixBUG.FactoredNormalBound`) holds for
  all rank-`ρ` factorizations `U S Vᵀ`, not only near `A(t)` as in condition 2 of the paper's
  Theorem 2; this is stronger than the paper's assumption.
* `tucker_symm_exact_abstract`: abstract core of **Algorithm 2 + Theorem 5**, **conditional** on
  the library's recoverability hypothesis (`Exactness.IsRecoverable`), which stands in for the
  multilinear-rank and overlap assumptions of Theorem 5 (its derivation from them is not
  formalized): one K-step in mode one and the mode-permutation symmetry of `A(t₁)` give
  exactness of the one-basis (anti-)symmetric Tucker integrator, on an abstract real normed space
  (no tensor mode products in Mathlib; the paper's tensors are complex).

Each main statement has a satisfiability `example` built on the rank-one data of
`LeanDLRA.Exactness.RankOneExample`.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P1906_01369

open LeanDLRA.Symmetry (IsTwistSymm)

variable {n r k : Type*} [Fintype n] [Fintype r] [Fintype k]

/-- `F(t, ·)` maps `σ`-symmetric matrices to `σ`-symmetric matrices (`σ = 1`: symmetric to
symmetric; `σ = -1`: skew-symmetric to skew-symmetric); this is condition (5) of the paper. -/
def MapsTwistSymm (σ : ℝ) (F : ℝ → Matrix n n ℝ → Matrix n n ℝ) : Prop :=
  ∀ t X, IsTwistSymm σ X → IsTwistSymm σ (F t X)

/-- **The exact flow preserves (skew-)symmetry** under the paper's hypothesis (5) only. -/
theorem isTwistSymm_of_odeSolution_of_maps {σ L : ℝ} (hσ : σ * σ = 1)
    {F : ℝ → Matrix n n ℝ → Matrix n n ℝ} (hF : MapsTwistSymm σ F)
    (hL : IsLipschitzField F L) {A : ℝ → Matrix n n ℝ} {t₀ t₁ : ℝ}
    (hA : ODESolution F A t₀ t₁) (h0 : IsTwistSymm σ (A t₀)) :
    ∀ t ∈ Icc t₀ t₁, IsTwistSymm σ (A t) := by
  let Φ : Matrix n n ℝ →L[ℝ] Matrix n n ℝ := σ • Frobenius.transposeCLM
  have hΦ : ∀ X, Φ X = σ • Xᵀ := fun X => rfl
  have hinv : ∀ X, Φ (Φ X) = X := fun X => by
    rw [hΦ, hΦ, Matrix.transpose_smul, Matrix.transpose_transpose, smul_smul, hσ, one_smul]
  have hσabs : |σ| = 1 := by
    have : |σ| * |σ| = 1 := by rw [← abs_mul, hσ, abs_one]
    nlinarith [abs_nonneg σ]
  have hnorm : ∀ X, ‖Φ X‖ = ‖X‖ := fun X => by
    rw [hΦ, norm_smul, Real.norm_eq_abs, hσabs, one_mul, Frobenius.norm_transpose]
  have hfix : ∀ X, Φ X = X ↔ IsTwistSymm σ X := fun X => by
    unfold IsTwistSymm
    rw [hΦ]
    constructor
    · intro h
      calc Xᵀ = (σ * σ) • Xᵀ := by rw [hσ, one_smul]
        _ = σ • X := by rw [← smul_smul, h]
    · intro h
      rw [h, smul_smul, hσ, one_smul]
  set d : ℝ → Matrix n n ℝ := fun t => A t - Φ (A t) with hd
  have hdc : ContinuousOn d (Icc t₀ t₁) :=
    hA.cont.sub (Φ.continuous.comp_continuousOn hA.cont)
  have hdd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt d (F t (A t) - Φ (F t (A t))) (Ici t) t :=
    fun t ht => (hA.deriv t ht).sub (Φ.hasFDerivAt.comp_hasDerivWithinAt t (hA.deriv t ht))
  have hbound : ∀ t ∈ Ico t₀ t₁, ‖F t (A t) - Φ (F t (A t))‖ ≤ L * ‖d t‖ + 0 := by
    intro t _
    set z : Matrix n n ℝ := (1 / 2 : ℝ) • (A t + Φ (A t)) with hz
    have hΦz : Φ z = z := by
      rw [hz, map_smul, map_add, hinv, add_comm]
    have hFz : Φ (F t z) = F t z := (hfix _).2 (hF t z ((hfix z).1 hΦz))
    have hAz : A t - z = (1 / 2 : ℝ) • d t := by
      rw [hz, hd]; simp only; module
    have h1 : F t (A t) - Φ (F t (A t)) = (F t (A t) - F t z) - Φ (F t (A t) - F t z) := by
      rw [map_sub, hFz]; abel
    rw [add_zero, h1]
    calc ‖(F t (A t) - F t z) - Φ (F t (A t) - F t z)‖
        ≤ ‖F t (A t) - F t z‖ + ‖Φ (F t (A t) - F t z)‖ := norm_sub_le _ _
      _ = 2 * ‖F t (A t) - F t z‖ := by rw [hnorm]; ring
      _ ≤ 2 * (L * ‖A t - z‖) := by gcongr; exact hL t _ _
      _ = L * ‖d t‖ := by
        rw [hAz, norm_smul, Real.norm_eq_abs]
        rw [abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]; ring
  have hd0 : ‖d t₀‖ ≤ 0 := by
    have : d t₀ = 0 := by
      rw [hd]; simp only
      rw [(hfix _).2 h0, sub_self]
    rw [this, norm_zero]
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le hdc hdd hd0 hbound
  intro t ht
  have h2 := hg t ht
  rw [gronwallBound_ε0_δ0] at h2
  have h3 : d t = 0 := norm_le_zero_iff.1 h2
  exact (hfix _).1 (sub_eq_zero.1 h3).symm


/-- **Algorithm 1: symmetry preservation** (arXiv 1906.01369, Algorithm 1 and the statement
following eq. (5)).  Let `F` map `σ`-symmetric matrices to `σ`-symmetric matrices (the paper's
condition (5), `σ = 1` symmetric, `σ = -1` skew-symmetric) and be Lipschitz (this is only used to
make the Galerkin step well posed through Gronwall's inequality), and let `Y₀ = U₀ S₀ U₀ᵀ` with
`S₀` `σ`-symmetric.  If `S` solves the S-step `S' = U₁ᵀ F(t, U₁ S U₁ᵀ) U₁`,
`S(t₀) = (U₁ᵀU₀) S₀ (U₀ᵀU₁)` for any new basis `U₁`, then `S(t₁)` and
`Y₁ = U₁ S(t₁) U₁ᵀ` are `σ`-symmetric.  No L-step is needed since the right basis is `U₁` as well.

Differences from the paper: the K-step only serves to produce `U₁` (QR of `K(t₁)`), and the
conclusion holds for **every** `U₁` (of any width `k`, orthonormal or not), so the K-step is not
among the hypotheses.  Compared with `LeanDLRA.Symmetry.bug_isTwistSymm` the hypothesis here is the
paper's (5), weaker than twist-equivariance `F(t, σYᵀ) = σF(t, Y)ᵀ`; it is proved by a Gronwall
argument on the non-`σ`-symmetric part. -/
theorem algorithm1_isTwistSymm {σ L : ℝ} (hσ : σ * σ = 1)
    {F : ℝ → Matrix n n ℝ → Matrix n n ℝ} (hF : MapsTwistSymm σ F) (hL : IsLipschitzField F L)
    {U₀ : Matrix n r ℝ} {S₀ : Matrix r r ℝ} (hS₀ : IsTwistSymm σ S₀) {t₀ t₁ : ℝ}
    {U₁ : Matrix n k ℝ} {S : ℝ → Matrix k k ℝ}
    (hS : ODESolution (MatrixBUG.sField U₁ U₁ F) S t₀ t₁)
    (hS0 : S t₀ = U₁ᵀ * U₀ * S₀ * (U₀ᵀ * U₁)) (ht : t₀ ≤ t₁) :
    (∀ t ∈ Icc t₀ t₁, IsTwistSymm σ (S t)) ∧ IsTwistSymm σ (U₁ * S t₁ * U₁ᵀ) := by
  have hmap : MapsTwistSymm σ (MatrixBUG.sField U₁ U₁ F) := by
    intro t X hX
    have h1 : IsTwistSymm σ (F t (U₁ * X * U₁ᵀ)) := hF t _ (hX.mul_mul_transpose U₁)
    have h2 := h1.mul_mul_transpose U₁ᵀ
    rwa [Matrix.transpose_transpose] at h2
  obtain ⟨L', hL'⟩ := Symmetry.exists_lipschitzField_sField hL U₁ U₁
  have h0 : IsTwistSymm σ (S t₀) := by
    have h := hS₀.mul_mul_transpose (U₁ᵀ * U₀)
    rw [hS0]
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using h
  have hsym := isTwistSymm_of_odeSolution_of_maps hσ hmap hL' hS h0
  exact ⟨hsym, (hsym t₁ ⟨ht, le_rfl⟩).mul_mul_transpose U₁⟩

/-- **Algorithm 1, symmetric case** (arXiv 1906.01369, Algorithm 1 with `F` mapping symmetric
matrices to symmetric matrices): `S(t₁)` and `Y₁ = U₁ S(t₁) U₁ᵀ` are symmetric.  See
`algorithm1_isTwistSymm` for the differences from the paper. -/
theorem algorithm1_symmetric {L : ℝ} {F : ℝ → Matrix n n ℝ → Matrix n n ℝ}
    (hF : ∀ t X, X.IsSymm → (F t X).IsSymm) (hL : IsLipschitzField F L)
    {U₀ : Matrix n r ℝ} {S₀ : Matrix r r ℝ} (hS₀ : S₀.IsSymm) {t₀ t₁ : ℝ}
    {U₁ : Matrix n k ℝ} {S : ℝ → Matrix k k ℝ}
    (hS : ODESolution (MatrixBUG.sField U₁ U₁ F) S t₀ t₁)
    (hS0 : S t₀ = U₁ᵀ * U₀ * S₀ * (U₀ᵀ * U₁)) (ht : t₀ ≤ t₁) :
    (S t₁).IsSymm ∧ (U₁ * S t₁ * U₁ᵀ).IsSymm := by
  have h := algorithm1_isTwistSymm (σ := 1) (by norm_num)
    (fun t X hX => (Symmetry.isTwistSymm_one_iff _).2
      (hF t X ((Symmetry.isTwistSymm_one_iff _).1 hX))) hL
    ((Symmetry.isTwistSymm_one_iff _).2 hS₀) hS hS0 ht
  exact ⟨(Symmetry.isTwistSymm_one_iff _).1 (h.1 t₁ ⟨ht, le_rfl⟩),
    (Symmetry.isTwistSymm_one_iff _).1 h.2⟩

/-- **Algorithm 1, skew-symmetric case** (arXiv 1906.01369, Algorithm 1 with `F` mapping
skew-symmetric matrices to skew-symmetric matrices): `S(t₁)` and `Y₁ = U₁ S(t₁) U₁ᵀ` are
skew-symmetric.  See `algorithm1_isTwistSymm` for the differences from the paper. -/
theorem algorithm1_skew {L : ℝ} {F : ℝ → Matrix n n ℝ → Matrix n n ℝ}
    (hF : ∀ t X, Xᵀ = -X → (F t X)ᵀ = -F t X) (hL : IsLipschitzField F L)
    {U₀ : Matrix n r ℝ} {S₀ : Matrix r r ℝ} (hS₀ : S₀ᵀ = -S₀) {t₀ t₁ : ℝ}
    {U₁ : Matrix n k ℝ} {S : ℝ → Matrix k k ℝ}
    (hS : ODESolution (MatrixBUG.sField U₁ U₁ F) S t₀ t₁)
    (hS0 : S t₀ = U₁ᵀ * U₀ * S₀ * (U₀ᵀ * U₁)) (ht : t₀ ≤ t₁) :
    (S t₁)ᵀ = -S t₁ ∧ (U₁ * S t₁ * U₁ᵀ)ᵀ = -(U₁ * S t₁ * U₁ᵀ) := by
  have h := algorithm1_isTwistSymm (σ := -1) (by norm_num)
    (fun t X hX => (Symmetry.isTwistSymm_neg_one_iff _).2
      (hF t X ((Symmetry.isTwistSymm_neg_one_iff _).1 hX))) hL
    ((Symmetry.isTwistSymm_neg_one_iff _).2 hS₀) hS hS0 ht
  exact ⟨(Symmetry.isTwistSymm_neg_one_iff _).1 (h.1 t₁ ⟨ht, le_rfl⟩),
    (Symmetry.isTwistSymm_neg_one_iff _).1 h.2⟩

/-! ### Satisfiability of the hypotheses of Algorithm 1 -/

section AlgorithmExample

open LeanDLRA.Exactness.RankOneExample

/-- The hypotheses of `algorithm1_symmetric` are satisfiable with a non-constant field:
`F(t, Y) = Y` (symmetric-to-symmetric, `1`-Lipschitz) on `2 × 2` matrices with the unit vector
`u = (3/5, 4/5)` as the new basis, the S-step reduces to `S' = S`, `S(t) = eᵗ`. -/
example : (u * (Real.exp 1 • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * uᵀ).IsSymm := by
  have hu : uᵀ * u = 1 := u_orth
  have hsol : ODESolution (MatrixBUG.sField u u (fun (_ : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℝ) => Y))
      (fun t => Real.exp t • (1 : Matrix (Fin 1) (Fin 1) ℝ)) 0 1 := by
    refine ⟨by fun_prop, fun t _ => ?_⟩
    have h : HasDerivAt (fun t : ℝ => Real.exp t • (1 : Matrix (Fin 1) (Fin 1) ℝ))
        (Real.exp t • (1 : Matrix (Fin 1) (Fin 1) ℝ)) t :=
      (Real.hasDerivAt_exp t).smul_const _
    refine h.hasDerivWithinAt.congr_deriv ?_
    simp only [MatrixBUG.sField, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hu,
      Matrix.mul_one]
  exact (algorithm1_symmetric (S₀ := (1 : Matrix (Fin 1) (Fin 1) ℝ)) (U₀ := u) (L := 1)
    (fun t X hX => hX) (fun _ x y => by rw [one_mul]) Matrix.isSymm_one hsol (by
      simp only [Real.exp_zero, one_smul, hu, Matrix.mul_one]) zero_le_one).2

end AlgorithmExample

/-! ### Theorem 3: exactness -/

/-- **Theorem 3, exactness of the symmetric / skew-symmetric integrator** (arXiv 1906.01369,
Theorem 3).  Let `F(t, Y) = Ȧ(t)` (`IsDerivRHS F A t₀ t₁`, as in the exactness statements of the
library), where `A(t₀) = Ue₀ Se₀ Ue₀ᵀ` and `A(t₁) = Ue₁ Se₁ Ue₁ᵀ` have rank at most `r`, `A(t₁)`
is `σ`-symmetric (`σ = 1`: symmetric, `σ = -1`: skew-symmetric; the symmetry of `A(t₀)` is not
used), `Ue₀ᵀUe₀ = 1`, `Se₀` invertible and `Ue₁ᵀ Ue₀` invertible.  Run Algorithm 1 from
`Y₀ = U₀ S₀ U₀ᵀ = A(t₀)` (`U₀ᵀU₀ = 1`): K-step
`K' = F(t, K U₀ᵀ) U₀`, `K(t₀) = U₀S₀`, any new basis `U₁` capturing `K(t₁)`
(`U₁U₁ᵀ K(t₁) = K(t₁)`, e.g. from a QR factorization), and the S-step
`S' = U₁ᵀ F(t, U₁ S U₁ᵀ) U₁`, `S(t₀) = (U₁ᵀU₀) S₀ (U₀ᵀU₁)`.  Then
`Y₁ = U₁ S(t₁) U₁ᵀ = A(t₁)` and `U₁U₁ᵀ A(t₁) U₁U₁ᵀ = A(t₁)`.

Differences from the paper: only the endpoints `t₀`, `t₁` of the factorizations are used; `Se₁`
may be singular, `Ue₁` and `U₁` need not be orthonormal.  The paper's theorem is stated for
`A(t) = U(t)S(t)U(t)ᵀ` on the whole interval; this is not needed.  The algorithm has no L-step; the
proof shows that the L-step result `L(t₁) = σ K(t₁)` would be captured by `U₁` as well, and then
uses `LeanDLRA.Exactness.bug_exact_of_factors` (with `V = U`). -/
theorem theorem3_exact [DecidableEq r] {σ : ℝ} (hσ : σ * σ = 1)
    {F : ℝ → Matrix n n ℝ → Matrix n n ℝ} {A : ℝ → Matrix n n ℝ} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) {Ue₀ Ue₁ : Matrix n r ℝ} {Se₀ Se₁ : Matrix r r ℝ}
    (hA₀ : A t₀ = Ue₀ * Se₀ * Ue₀ᵀ) (hA₁ : A t₁ = Ue₁ * Se₁ * Ue₁ᵀ)
    (hsym₁ : IsTwistSymm σ (A t₁)) (hUe₀ : Ue₀ᵀ * Ue₀ = 1) (hSe₀ : IsUnit Se₀)
    (hUU : IsUnit (Ue₁ᵀ * Ue₀)) {U₀ : Matrix n r ℝ} {S₀ : Matrix r r ℝ} (hU₀ : U₀ᵀ * U₀ = 1)
    (hY₀ : U₀ * S₀ * U₀ᵀ = A t₀) {K : ℝ → Matrix n r ℝ}
    (hK : ODESolution (fun t K => F t (K * U₀ᵀ) * U₀) K t₀ t₁) (hK₀ : K t₀ = U₀ * S₀)
    {U₁ : Matrix n k ℝ} (hU₁ : U₁ * U₁ᵀ * K t₁ = K t₁) {Sf : ℝ → Matrix k k ℝ}
    (hSf : ODESolution (fun t S => U₁ᵀ * F t (U₁ * S * U₁ᵀ) * U₁) Sf t₀ t₁)
    (hSf₀ : Sf t₀ = U₁ᵀ * U₀ * S₀ * (U₀ᵀ * U₁)) :
    U₁ * Sf t₁ * U₁ᵀ = A t₁ ∧ U₁ * U₁ᵀ * A t₁ * (U₁ * U₁ᵀ) = A t₁ := by
  have h1 : t₁ ∈ Icc t₀ t₁ := ⟨ht, le_rfl⟩
  have eK := Exactness.kStepODE_eq_add hA hK t₁ h1
  have eS := Exactness.factorODE_eq_add hA U₁ᵀ U₁ (fun S => U₁ * S * U₁ᵀ) (fun _ _ => rfl) hSf
    t₁ h1
  rw [hK₀] at eK
  rw [hSf₀] at eS
  have hUV : IsUnit (Ue₁ᵀ * U₀) :=
    Exactness.isUnit_transpose_mul_of_eq' (hY₀.trans hA₀) hUe₀ hSe₀ hUU
  have hLK : U₀ * S₀ᵀ + (A t₁ - A t₀)ᵀ * U₀ = σ • (U₀ * S₀ + (A t₁ - A t₀) * U₀) := by
    rw [Exactness.lStep_eq hU₀ hY₀, Exactness.kStep_eq hU₀ hY₀, hsym₁, Matrix.smul_mul]
  have hV₁ : U₁ * U₁ᵀ * (U₀ * S₀ᵀ + (A t₁ - A t₀)ᵀ * U₀) = U₀ * S₀ᵀ + (A t₁ - A t₀)ᵀ * U₀ := by
    rw [hLK, Matrix.mul_smul, ← eK, hU₁]
  have hK1 : U₁ * U₁ᵀ * (U₀ * S₀ + (A t₁ - A t₀) * U₀) = U₀ * S₀ + (A t₁ - A t₀) * U₀ := by
    rw [← eK, hU₁]
  have hS₁ : Sf t₁ = U₁ᵀ * U₀ * S₀ * (U₁ᵀ * U₀)ᵀ + U₁ᵀ * (A t₁ - A t₀) * U₁ := by
    rw [eS, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hmain : U₁ * Sf t₁ * U₁ᵀ = A t₁ :=
    Exactness.bug_exact_of_factors (Ve₀ := Ue₀) (Ve₁ := Ue₁) hA₀ hA₁ hUe₀ hUe₀ hSe₀ hUU hUU hU₀
      hU₀ hY₀ (K₁ := U₀ * S₀ + (A t₁ - A t₀) * U₀) (L₁ := U₀ * S₀ᵀ + (A t₁ - A t₀)ᵀ * U₀)
      rfl rfl hK1 hV₁ hS₁
  refine ⟨hmain, ?_⟩
  have hP1 : U₁ * U₁ᵀ * A t₁ = A t₁ :=
    Exactness.left_capture (U := Ue₁) (S := Se₁) (V := Ue₁) hU₀ hY₀ hA₁ hUV hK1
  have h := congrArg Matrix.transpose hP1
  have hsym' : (A t₁)ᵀ = σ • A t₁ := hsym₁
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hsym'] at h
  rw [hP1]
  rw [Matrix.smul_mul] at h
  have hss : ∀ X : Matrix n n ℝ, σ • (σ • X) = X := fun X => by rw [smul_smul, hσ, one_smul]
  calc A t₁ * (U₁ * U₁ᵀ) = σ • (σ • (A t₁ * (U₁ * U₁ᵀ))) := (hss _).symm
    _ = σ • (σ • A t₁) := by rw [h]
    _ = A t₁ := hss _

section Theorem3Example

open LeanDLRA.Exactness LeanDLRA.Exactness.RankOneExample

/-- The hypotheses of `theorem3_exact` are satisfiable with `A(t₁) ≠ A(t₀)`: `n = 2`, `r = 1`,
`σ = 1`, `A(t) = A₀ + t (A₁ - A₀)` with `A₀ = e₁e₁ᵀ`, `A₁ = u uᵀ`, `u = (3/5, 4/5)`, so that
`uᵀe₁ = 3/5` is invertible.  The K-step is `K(t) = e₁ + t (A₁ - A₀) e₁`, the new basis is `u`, and
the S-step is `S(t) = (uᵀe₁)(e₁ᵀu) + t uᵀ(A₁ - A₀)u`. -/
example : u * (uᵀ * e₁ * S₀ * (e₁ᵀ * u) + (1 : ℝ) • (uᵀ * (A₁ - A₀) * u)) * uᵀ = Apath 1 ∧
    A₁ ≠ A₀ := by
  refine ⟨?_, A₁_ne_A₀⟩
  have hsym : IsTwistSymm 1 (Apath 1) := by
    rw [Apath_one, A₁_eq]
    simp [IsTwistSymm, S₀, Matrix.transpose_mul]
  exact (theorem3_exact (σ := 1) (by norm_num) (F := fun _ _ => A₁ - A₀) (A := Apath)
    zero_le_one (isDerivRHS_add_smul A₀ (A₁ - A₀) 0 1) (Ue₀ := e₁) (Se₀ := S₀) (Ue₁ := u)
    (Se₁ := S₀) (Apath_zero.trans Y₀_eq.symm)
    (Apath_one.trans A₁_eq) hsym e₁_orth (by simp [S₀]) isUnit_u_e₁ e₁_orth
    (Y₀_eq.trans Apath_zero.symm) (K := fun t => e₁ * S₀ + t • ((A₁ - A₀) * e₁))
    (odeSolution_add_smul_of_const (fun _ _ => rfl) _ 0 1) (by simp)
    (by simp only [one_smul]; exact capture_K)
    (Sf := fun t => uᵀ * e₁ * S₀ * (e₁ᵀ * u) + t • (uᵀ * (A₁ - A₀) * u))
    (odeSolution_add_smul_of_const (fun _ _ => rfl) _ 0 1) (by simp)).1

end Theorem3Example

/-! ### Lemma 1 and the robust error bounds (Lemma 2, Theorem 4) -/

/-- `σ * σ = 1` forces `|σ| = 1`. -/
lemma abs_eq_one_of_mul_self_eq_one {σ : ℝ} (hσ : σ * σ = 1) : |σ| = 1 := by
  have : |σ| * |σ| = 1 := by rw [← abs_mul, hσ, abs_one]
  nlinarith [abs_nonneg σ]

/-- **Lemma 1, two-sided projection error** (arXiv 1906.01369, Lemma 1, second half of the proof).
Let `U₁` have orthonormal columns and let `A₁` be `σ`-symmetric (symmetric for `σ = 1`,
skew-symmetric for `σ = -1`) with `‖(I - U₁U₁ᵀ) A₁‖ ≤ θ`.  Then `‖U₁U₁ᵀ A₁ U₁U₁ᵀ - A₁‖ ≤ 2θ`.
(The right factor is handled by (skew-)symmetry of `A₁`: `A₁ (I - U₁U₁ᵀ) = σ ((I - U₁U₁ᵀ) A₁)ᵀ`.)
The paper obtains `‖(I - U₁U₁ᵀ)A₁‖ ≤ ϑ(h, ε) = (4e^{Lh}BL + 9BL)h² + (3e^{Lh} + 4)εh` from the
local error of the projector-splitting integrator ([10, Theorem 2.1]); here the bound
`θ = h(4LBh + ε)` (at most `ϑ(h, ε)` for `L, B, ε, h ≥ 0`) is `IsSymStep.capture_left` below. -/
theorem two_sided_projection_error [DecidableEq n] [DecidableEq k] {σ : ℝ} (hσ : σ * σ = 1)
    {U₁ : Matrix n k ℝ} (hU₁ : U₁ᵀ * U₁ = 1) {A : Matrix n n ℝ} (hA : IsTwistSymm σ A) {θ : ℝ}
    (hθ : ‖(1 - U₁ * U₁ᵀ) * A‖ ≤ θ) : ‖U₁ * U₁ᵀ * A * (U₁ * U₁ᵀ) - A‖ ≤ 2 * θ := by
  set P : Matrix n n ℝ := U₁ * U₁ᵀ with hP
  have hdec : P * A * P - A = -((1 - P) * A) - P * (A * (1 - P)) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    abel
  have hPt : (1 - P)ᵀ = 1 - P := by
    rw [hP, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
      Matrix.transpose_transpose]
  have hAt : A * (1 - P) = σ • ((1 - P) * A)ᵀ := by
    rw [Matrix.transpose_mul, hPt, show Aᵀ = σ • A from hA, Matrix.smul_mul, smul_smul, hσ,
      one_smul]
  have h1 : ‖P * (A * (1 - P))‖ ≤ ‖(1 - P) * A‖ := by
    have h := (isOrthProj_leftProj (n := n) hU₁).norm_le (A * (1 - P))
    rw [leftProj_apply] at h
    refine h.trans_eq ?_
    rw [hAt, norm_smul, Real.norm_eq_abs, abs_eq_one_of_mul_self_eq_one hσ, one_mul,
      Frobenius.norm_transpose]
  rw [hdec, ← neg_add', norm_neg]
  calc ‖(1 - P) * A + P * (A * (1 - P))‖ ≤ ‖(1 - P) * A‖ + ‖P * (A * (1 - P))‖ := norm_add_le _ _
    _ ≤ 2 * θ := by linarith

section Errors

variable {ρ : ℕ} [DecidableEq n]

/-- **One step of Algorithm 1** (arXiv 1906.01369), at the level of the factors, from
`Y₀ = U₀ S₀ U₀ᵀ` at `t₀` to `t₁`: K-step `K' = F(t, K U₀ᵀ) U₀`, `K(t₀) = U₀ S₀`; a new orthonormal
basis `U₁` capturing `K(t₁)` (the QR step, `U₁U₁ᵀ K(t₁) = K(t₁)`); Galerkin S-step
`S' = U₁ᵀ F(t, U₁ S U₁ᵀ) U₁`, `S(t₀) = (U₁ᵀU₀) S₀ (U₀ᵀU₁)`.  The new approximation is
`Y₁ = U₁ S(t₁) U₁ᵀ`.  There is no L-step: the right basis is `U₁` as well. -/
structure IsSymStep (F : ℝ → Matrix n n ℝ → Matrix n n ℝ) (t₀ t₁ : ℝ)
    (U₀ : Matrix n (Fin ρ) ℝ) (S₀ : Matrix (Fin ρ) (Fin ρ) ℝ) (U₁ : Matrix n (Fin ρ) ℝ)
    (K : ℝ → Matrix n (Fin ρ) ℝ) (S : ℝ → Matrix (Fin ρ) (Fin ρ) ℝ) : Prop where
  orthU₀ : U₀ᵀ * U₀ = 1
  kSol : ODESolution (MatrixBUG.kField U₀ F) K t₀ t₁
  kStart : K t₀ = U₀ * S₀
  orthU₁ : U₁ᵀ * U₁ = 1
  kCap : U₁ * U₁ᵀ * K t₁ = K t₁
  sSol : ODESolution (MatrixBUG.sField U₁ U₁ F) S t₀ t₁
  sStart : S t₀ = U₁ᵀ * U₀ * S₀ * (U₀ᵀ * U₁)

namespace IsSymStep

variable {F : ℝ → Matrix n n ℝ → Matrix n n ℝ} {t₀ t₁ : ℝ} {U₀ U₁ : Matrix n (Fin ρ) ℝ}
  {S₀ : Matrix (Fin ρ) (Fin ρ) ℝ} {K : ℝ → Matrix n (Fin ρ) ℝ}
  {S : ℝ → Matrix (Fin ρ) (Fin ρ) ℝ} {L B ε h : ℝ} {A : ℝ → Matrix n n ℝ}

/-- **Left capture** (arXiv 1906.01369, the first half of the proof of Lemma 1): the new basis
captures the exact solution, `‖(I - U₁U₁ᵀ) A(t₁)‖ ≤ h (4 L B h + ε)`, under the normal-component
assumption at rank `ρ` (`FactoredNormalBound`, the library's global form of the paper's
assumption on `‖(I - P(Y)) F(t, Y)‖`, required for all rank-`ρ` factorizations rather than near
`A(t)`).  The paper derives the weaker bound `ϑ(h, ε)` from the local error of the
projector-splitting integrator; here the library's K-step estimate `kstep_capture` is used.
Only the K-step enters; no symmetry is used. -/
theorem capture_left (hs : IsSymStep F t₀ t₁ U₀ S₀ U₁ K S)
    (hε : MatrixBUG.FactoredNormalBound F ρ ε) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁)
    (hA₀ : A t₀ = U₀ * S₀ * U₀ᵀ) :
    ‖(1 - U₁ * U₁ᵀ) * A t₁‖ ≤ h * (4 * L * B * h + ε) := by
  have h1 := kstep_capture hF hL hB (isOrthProj_leftProj hs.orthU₁)
    (isOrthProj_rightProj hs.orthU₀) ht₁ hh hA (MatrixBUG.odeSolution_kField hs.kSol)
    (YK := fun t => K t * U₀ᵀ)
    (by simp only [hs.kStart, hA₀, Matrix.mul_assoc])
    (by simp only [leftProj_apply, ← Matrix.mul_assoc, hs.kCap])
    (fun t _ => MatrixBUG.kNormal_le hε hs.orthU₁ hs.orthU₁
      (by rw [Matrix.mul_assoc, hs.orthU₁, Matrix.mul_one]) hs.kCap hs.orthU₀ t)
  rwa [one_sub_leftProj_apply] at h1

/-- The normal-component assumption forces `ε ≥ 0` (applied at the K-step of a step). -/
lemma eps_nonneg (hs : IsSymStep F t₀ t₁ U₀ S₀ U₁ K S)
    (hε : MatrixBUG.FactoredNormalBound F ρ ε) : 0 ≤ ε :=
  (norm_nonneg _).trans (MatrixBUG.kNormal_le hε hs.orthU₁ hs.orthU₁
    (by rw [Matrix.mul_assoc, hs.orthU₁, Matrix.mul_one]) hs.kCap hs.orthU₀ t₀)

/-- **Lemma 2 (local error), explicit form** (arXiv 1906.01369, Lemma 2).  Let `F` be
`L`-Lipschitz (`L ≥ 0`), bounded by `B`, map `σ`-symmetric matrices to `σ`-symmetric matrices
(condition (5)) and satisfy the factored normal-component assumption at rank `ρ` with bound `ε`.
Let `A' = F(t, A)` on `[t₀, t₁]`, `t₁ = t₀ + h`, with `A(t₀) = Y₀ = U₀ S₀ U₀ᵀ`, `S₀` `σ`-symmetric,
`U₀ᵀU₀ = 1`.  Then one step of Algorithm 1 satisfies, with `ϑ = h (4 L B h + ε)`,

    ‖U₁ S(t₁) U₁ᵀ - A(t₁)‖ ≤ (e^{L h} - 1)(B h + 2ϑ) + 2ϑ.

The bound does not depend on singular values.  Differences from the paper: the paper's final
form is `h(c₁ε + c₂h)` (see `local_error_le`); the symmetry of the exact solution `A` is not
assumed but derived (`isTwistSymm_of_odeSolution_of_maps`); the K-step capture and Lemma 1 are
used for the left and (via symmetry) the right basis, so no L-step is needed; the
normal-component hypothesis is the global `FactoredNormalBound` (see `capture_left`), stronger
than the paper's condition 2, and `F` is Lipschitz and bounded for all `t`. -/
theorem local_error {σ : ℝ} (hσ : σ * σ = 1) (hs : IsSymStep F t₀ t₁ U₀ S₀ U₁ K S)
    (hFs : MapsTwistSymm σ F) (hS₀ : IsTwistSymm σ S₀)
    (hε : MatrixBUG.FactoredNormalBound F ρ ε) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁)
    (hA₀ : A t₀ = U₀ * S₀ * U₀ᵀ) :
    ‖U₁ * S t₁ * U₁ᵀ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (B * h + 2 * (h * (4 * L * B * h + ε)))
      + 2 * (h * (4 * L * B * h + ε)) := by
  have hle : t₀ ≤ t₁ := by linarith
  have hAsym := isTwistSymm_of_odeSolution_of_maps hσ hFs hF hA
    (by rw [hA₀]; exact hS₀.mul_mul_transpose U₀) t₁ ⟨hle, le_rfl⟩
  have hcap := two_sided_projection_error hσ hs.orthU₁ hAsym
    (hs.capture_left hε hF hL hB ht₁ hh hA hA₀)
  have hP := isOrthProj_leftProj (n := n) hs.orthU₁
  have hQ := isOrthProj_rightProj (m := n) hs.orthU₁
  have hc : ∀ x : Matrix n n ℝ, leftProj U₁ (rightProj U₁ x) = rightProj U₁ (leftProj U₁ x) :=
    fun x => leftProj_rightProj_comm U₁ U₁ x
  refine galerkin_step_error (R := leftProj U₁ * rightProj U₁) (hP.mul hQ hc) hF hL hB ht₁ hh hA
    (MatrixBUG.odeSolution_sField hs.sSol) ?_ ?_
  · rw [hs.sStart, hA₀]
    simp only [mul_apply_eq_comp, leftProj_apply, rightProj_apply, Matrix.mul_assoc]
  · rw [norm_sub_rev]
    simpa [mul_apply_eq_comp, leftProj_apply, rightProj_apply, Matrix.mul_assoc]
      using hcap

/-- **Lemma 2 (local error), `O`-form** (arXiv 1906.01369, Lemma 2).  Under the hypotheses of
`local_error`, for `0 ≤ h ≤ H`:
`‖U₁ S(t₁) U₁ᵀ - A(t₁)‖ ≤ h (c₁ ε + c₂ h)` with `c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H`
(the library's explicit constants `c₁ = 2 + 2 L H e^{L H}`, `c₂ = L B (8 + e^{L H}(1 + 8 L H))`),
independent of the singular values of `A` and of the factors. -/
theorem local_error_le {σ : ℝ} (hσ : σ * σ = 1) (hs : IsSymStep F t₀ t₁ U₀ S₀ U₁ K S)
    (hFs : MapsTwistSymm σ F) (hS₀ : IsTwistSymm σ S₀)
    (hε : MatrixBUG.FactoredNormalBound F ρ ε) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) {H : ℝ} (hhH : h ≤ H)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = U₀ * S₀ * U₀ᵀ) :
    ‖U₁ * S t₁ * U₁ᵀ - A t₁‖ ≤ h * (bugC₁ L H * ε + bugC₂ L B H * h) :=
  (hs.local_error hσ hFs hS₀ hε hF hL hB ht₁ hh hA hA₀).trans
    (bug_bound_le hL hB.nonneg (hs.eps_nonneg hε) hh hhH)

end IsSymStep

omit [DecidableEq n] in
/-- **Algorithm 1 over several steps stays (skew-)symmetric**: if `Sm 0` is `σ`-symmetric and
step `j` goes from `(U j, Sm j)` to `(U (j+1), Sm (j+1) = S j (t_{j+1}))`, every `Sm j`
(hence every `Y j = U j * Sm j * (U j)ᵀ`) is `σ`-symmetric. -/
theorem isTwistSymm_iterate {σ L : ℝ} (hσ : σ * σ = 1) {F : ℝ → Matrix n n ℝ → Matrix n n ℝ}
    (hFs : MapsTwistSymm σ F) (hF : IsLipschitzField F L) {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ}
    {U : ℕ → Matrix n (Fin ρ) ℝ} {Sm : ℕ → Matrix (Fin ρ) (Fin ρ) ℝ}
    {K : ℕ → ℝ → Matrix n (Fin ρ) ℝ} {S : ℕ → ℝ → Matrix (Fin ρ) (Fin ρ) ℝ}
    (hS₀ : IsTwistSymm σ (Sm 0))
    (hstep : ∀ j < N, IsSymStep F (t₀ + j * h) (t₀ + (j + 1) * h) (U j) (Sm j) (U (j + 1))
      (K j) (S j))
    (hSm : ∀ j < N, Sm (j + 1) = S j (t₀ + (j + 1) * h)) :
    ∀ j ≤ N, IsTwistSymm σ (Sm j) := by
  intro j
  induction j with
  | zero => exact fun _ => hS₀
  | succ j ih =>
    intro hj
    have hjN : j < N := hj
    have hle : t₀ + j * h ≤ t₀ + (j + 1) * h := by nlinarith
    have h1 := algorithm1_isTwistSymm hσ hFs hF (ih hjN.le) (hstep j hjN).sSol
      (hstep j hjN).sStart hle
    rw [hSm j hjN]
    exact h1.1 _ ⟨hle, le_rfl⟩

/-- **Theorem 4, robust global error bound of Algorithm 1** (arXiv 1906.01369, Theorem 4, in the
explicit form `‖Yⱼ - A(tⱼ)‖ ≤ e^{L j h}(‖Y₀ - A(t₀)‖ + j h (c₁ ε + c₂ h))`).  Let `F` be
`L`-Lipschitz (`L ≥ 0`), bounded by `B`, map `σ`-symmetric to `σ`-symmetric matrices (condition
(5)), satisfy the factored normal-component assumption at rank `ρ` with `0 ≤ ε`, and let
`A' = F(t, A)` on `[t₀, t₀ + N h]`.  Let `Y₀ = U 0 * Sm 0 * (U 0)ᵀ` with `Sm 0` `σ`-symmetric, and
for `j < N` let step `j` (`IsSymStep`) lead to `Y (j+1) = U (j+1) * Sm (j+1) * (U (j+1))ᵀ`,
`Sm (j+1) = S j (t_{j+1})`; `Φ j` is the exact flow on `[tⱼ, tⱼ₊₁]` started at `Yⱼ`.  Then for
`j ≤ N`, `c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H`, `0 ≤ h ≤ H`.

Differences from the paper: the paper assumes `A(t)` (skew-)symmetric; here only `Y₀` is, and the
symmetry of the exact flows `Φ j` is derived (`A` itself need not be symmetric).  The
normal-component hypothesis is the global `FactoredNormalBound` (see `IsSymStep.capture_left`),
stronger than condition 2 of the paper's Theorem 2, and `F` is Lipschitz and bounded for all
`t`. -/
theorem global_error {σ L B ε : ℝ} (hσ : σ * σ = 1) {F : ℝ → Matrix n n ℝ → Matrix n n ℝ}
    (hFs : MapsTwistSymm σ F) (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hε : MatrixBUG.FactoredNormalBound F ρ ε) {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ}
    {A : ℝ → Matrix n n ℝ} (hA : ODESolution F A t₀ (t₀ + N * h))
    {U : ℕ → Matrix n (Fin ρ) ℝ} {Sm : ℕ → Matrix (Fin ρ) (Fin ρ) ℝ}
    {K : ℕ → ℝ → Matrix n (Fin ρ) ℝ} {S : ℕ → ℝ → Matrix (Fin ρ) (Fin ρ) ℝ}
    {Φ : ℕ → ℝ → Matrix n n ℝ} (hS₀ : IsTwistSymm σ (Sm 0))
    (hstep : ∀ j < N, IsSymStep F (t₀ + j * h) (t₀ + (j + 1) * h) (U j) (Sm j) (U (j + 1))
      (K j) (S j))
    (hSm : ∀ j < N, Sm (j + 1) = S j (t₀ + (j + 1) * h))
    (hΦ : ∀ j < N, ODESolution F (Φ j) (t₀ + j * h) (t₀ + (j + 1) * h))
    (hΦ₀ : ∀ j < N, Φ j (t₀ + j * h) = U j * Sm j * (U j)ᵀ) :
    ∀ j ≤ N, ‖U j * Sm j * (U j)ᵀ - A (t₀ + j * h)‖ ≤ Real.exp (L * (j * h)) *
      (‖U 0 * Sm 0 * (U 0)ᵀ - A t₀‖ + j * h * (bugC₁ L H * ε + bugC₂ L B H * h)) := by
  have hsymm := isTwistSymm_iterate hσ hFs hF hh hS₀ hstep hSm
  have hloc : ∀ j < N, ‖U (j + 1) * Sm (j + 1) * (U (j + 1))ᵀ - Φ j (t₀ + (j + 1) * h)‖ ≤
      h * (bugC₁ L H * ε + bugC₂ L B H * h) := by
    intro j hj
    rw [hSm j hj]
    exact (hstep j hj).local_error_le hσ hFs (hsymm j hj.le) hε hF hL hB (by ring) hh hhH (hΦ j hj)
      (hΦ₀ j hj)
  intro j hj
  calc _ ≤ _ := lady_windermere (Y := fun j => U j * Sm j * (U j)ᵀ) hF hL hh hA hΦ hΦ₀ hloc j hj
    _ = _ := by ring

/-- **Theorem 4, robust global error bound of Algorithm 1, final form** (arXiv 1906.01369,
Theorem 4): under the hypotheses of `global_error`, with `0 ≤ ε`, `‖Y₀ - A(t₀)‖ ≤ δ` and
`j h ≤ T`,

    ‖Yⱼ - A(tⱼ)‖ ≤ c₀ δ + c₁' ε + c₂' h,

with `c₀ = e^{L T}`, `c₁' = T e^{L T} bugC₁ L H`, `c₂' = T e^{L T} bugC₂ L B H` depending only on
`L`, `B`, `T` and the step-size bound `H`, not on singular values of `A` or of the `Sm j`.  The
hypotheses differ from the paper's as in `global_error`. -/
theorem global_error_le {σ L B ε : ℝ} (hσ : σ * σ = 1) {F : ℝ → Matrix n n ℝ → Matrix n n ℝ}
    (hFs : MapsTwistSymm σ F) (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hε : MatrixBUG.FactoredNormalBound F ρ ε) (hε₀ : 0 ≤ ε) {t₀ h H : ℝ} (hh : 0 ≤ h)
    (hhH : h ≤ H) {N : ℕ} {A : ℝ → Matrix n n ℝ} (hA : ODESolution F A t₀ (t₀ + N * h))
    {U : ℕ → Matrix n (Fin ρ) ℝ} {Sm : ℕ → Matrix (Fin ρ) (Fin ρ) ℝ}
    {K : ℕ → ℝ → Matrix n (Fin ρ) ℝ} {S : ℕ → ℝ → Matrix (Fin ρ) (Fin ρ) ℝ}
    {Φ : ℕ → ℝ → Matrix n n ℝ} (hS₀ : IsTwistSymm σ (Sm 0))
    (hstep : ∀ j < N, IsSymStep F (t₀ + j * h) (t₀ + (j + 1) * h) (U j) (Sm j) (U (j + 1))
      (K j) (S j))
    (hSm : ∀ j < N, Sm (j + 1) = S j (t₀ + (j + 1) * h))
    (hΦ : ∀ j < N, ODESolution F (Φ j) (t₀ + j * h) (t₀ + (j + 1) * h))
    (hΦ₀ : ∀ j < N, Φ j (t₀ + j * h) = U j * Sm j * (U j)ᵀ) {δ T : ℝ}
    (hδ : ‖U 0 * Sm 0 * (U 0)ᵀ - A t₀‖ ≤ δ) :
    ∀ j ≤ N, (j : ℝ) * h ≤ T →
      ‖U j * Sm j * (U j)ᵀ - A (t₀ + j * h)‖ ≤ Real.exp (L * T) * δ
        + T * Real.exp (L * T) * bugC₁ L H * ε + T * Real.exp (L * T) * bugC₂ L B H * h := by
  have hsymm := isTwistSymm_iterate hσ hFs hF hh hS₀ hstep hSm
  have hH : 0 ≤ H := hh.trans hhH
  have hg : 0 ≤ bugC₁ L H * ε + bugC₂ L B H * h :=
    add_nonneg (mul_nonneg (bugC₁_nonneg hL hH) hε₀)
      (mul_nonneg (bugC₂_nonneg hL hB.nonneg hH) hh)
  have hloc : ∀ j < N, ‖U (j + 1) * Sm (j + 1) * (U (j + 1))ᵀ - Φ j (t₀ + (j + 1) * h)‖ ≤
      h * (bugC₁ L H * ε + bugC₂ L B H * h) := by
    intro j hj
    rw [hSm j hj]
    exact (hstep j hj).local_error_le hσ hFs (hsymm j hj.le) hε hF hL hB (by ring) hh hhH (hΦ j hj)
      (hΦ₀ j hj)
  intro j hj hT
  have h1 := lady_windermere_of_le (Y := fun j => U j * Sm j * (U j)ᵀ) hF hL hh hA hΦ hΦ₀ hg
    hloc j hj hT
  have h2 : Real.exp (L * T) * (‖U 0 * Sm 0 * (U 0)ᵀ - A t₀‖
      + T * (bugC₁ L H * ε + bugC₂ L B H * h))
      ≤ Real.exp (L * T) * (δ + T * (bugC₁ L H * ε + bugC₂ L B H * h)) :=
    mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  calc _ ≤ _ := h1.trans h2
    _ = _ := by ring

end Errors

section StepExample

open LeanDLRA.Exactness LeanDLRA.Exactness.RankOneExample

/-- The hypotheses of `IsSymStep.local_error_le` are satisfiable with `A₁ ≠ A₀`: `2 × 2`
symmetric matrices, rank `ρ = 1`, the constant symmetric field `F(t, Y) = A₁ - A₀` (so `L = 0`,
`B = ε = ‖A₁ - A₀‖`), exact solution `A(t) = A₀ + t(A₁ - A₀)`, old basis `e₁`, new basis
`u = (3/5, 4/5)` (a genuine K-step capture), affine K- and S-step solutions. -/
example : ‖u * (uᵀ * e₁ * S₀ * (e₁ᵀ * u) + (1 : ℝ) • (uᵀ * (A₁ - A₀) * u)) * uᵀ - Apath 1‖ ≤
    1 * (bugC₁ 0 1 * ‖A₁ - A₀‖ + bugC₂ 0 ‖A₁ - A₀‖ 1 * 1) := by
  have hsymC : IsTwistSymm 1 (A₁ - A₀) := by
    simp [IsTwistSymm, A₁, A₀, Matrix.transpose_mul]
  have hstep : IsSymStep (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => A₁ - A₀) 0 1 e₁ S₀ u
      (fun t => e₁ * S₀ + t • ((A₁ - A₀) * e₁))
      (fun t => uᵀ * e₁ * S₀ * (e₁ᵀ * u) + t • (uᵀ * (A₁ - A₀) * u)) :=
    { orthU₀ := e₁_orth
      kSol := odeSolution_add_smul_of_const (fun _ _ => rfl) _ 0 1
      kStart := by simp
      orthU₁ := u_orth
      kCap := by simp only [one_smul]; exact capture_K
      sSol := odeSolution_add_smul_of_const (fun _ _ => rfl) _ 0 1
      sStart := by simp }
  have h := hstep.local_error_le (σ := 1) (by norm_num) (fun _ _ _ => hsymC)
    (S₀ := S₀) (by simp [IsTwistSymm, S₀]) (ε := ‖A₁ - A₀‖)
    (MatrixBUG.factoredNormalBound_const _ 1)
    (L := 0) (B := ‖A₁ - A₀‖) (fun _ x y => by simp) le_rfl (fun _ _ => le_rfl)
    (h := 1) (H := 1) (A := Apath) (by norm_num) zero_le_one le_rfl
    ⟨by unfold Apath; fun_prop, fun t _ => by
      unfold Apath
      have := (hasDerivAt_id t).smul_const (A₁ - A₀) |>.const_add A₀
      simpa using this.hasDerivWithinAt⟩
    (by rw [Apath_zero]; exact (Y₀_eq).symm)
  simpa only [one_smul] using h

end StepExample

/-! ### Algorithm 2 and Theorem 5: (anti-)symmetric Tucker exactness, abstract core -/

section Tucker

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Algorithm 2 + Theorem 5, abstract core: exactness of the one-basis (anti-)symmetric Tucker
integrator** (arXiv 1906.01369, Algorithm 2 and Theorem 5), **conditional on the recoverability
hypothesis `hrec`** (see below).

Mathlib has no mode products of tensors, so this is stated on an abstract real normed space `E`
(the tensors; the paper's tensors are complex), exactly as the library does for the general Tucker
BUG integrator (`LeanDLRA.Exactness.tucker_exact_abstract`).  The data are:

* `Q₀`, `P₀`: the co-range projector `X ↦ Mat₁⁻¹(Mat₁(X) V⁰ V⁰ᵀ)` and the new-basis projector
  `X ↦ X ×₁ U¹U¹ᵀ` of **mode 1 only** (index `0`): Algorithm 2 runs a single K-step, in mode 1,
  and uses its basis `U¹` in all `d + 1` modes;
* `τ i`: the operator permuting mode `i` with mode `1` (an involution in the paper; this is not
  needed in the proof), so that
  the mode-`i` basis projector is `P i = τ i P₀ τ i` (`X ↦ X ×ᵢ U¹U¹ᵀ`);
* `A(t₁)` is symmetric or anti-symmetric under these permutations: `τ i A(t₁) = c A(t₁)` with
  `c * c = 1` (`c = 1` symmetric; for an anti-symmetric tensor `c = -1` for a transposition);
* the mode-1 K-step `YK' = Q₀ F(t, YK)`, `YK(t₀) = A(t₀) = Q₀ A(t₀)`, with capture
  `P₀ YK(t₁) = YK(t₁)`, and the non-degeneracy hypothesis of the library
  (`LeanDLRA.Exactness.IsRecoverable`: `A(t₁)` is recoverable from `Q₀ A(t₁)` modulo a class
  `𝓛 ∋ P₀`; for matrices it follows from the invertibility of `U(t₁)ᵀU(t₀)`);
* the core step `y' = (∏ᵢ Pᵢ) F(t, y)`, `y(t₀) = (∏ᵢ Pᵢ) A(t₀)` (the Galerkin step
  `Ċ = F(t, C ×ᵢ U¹) ×ᵢ U¹ᵀ`, `C(t₀) = C₀ ×ᵢ (U¹ᵀU⁰)` in full-space form).

Then `y(t₁) = A(t₁)` for `F(t, Y) = Ȧ(t)`.  The mode symmetry transfers the capture
`P₀ A(t₁) = A(t₁)` of mode 1 to every mode (`P i A = τ i P₀ τ i A = c τ i P₀ A = c τ i A = A`),
which is the step of the paper that replaces the `d` K-steps of the non-symmetric Tucker
integrator.  Differences from the paper: the matricizations, the identification of `Q₀`, `P₀`, `τ i`
with tensor operators and the derivation of the recoverability hypothesis from the
multilinear-rank and overlap assumptions of Theorem 5 are not formalized.  The result is therefore
conditional: the paper obtains the capture `P₀ A(t₁) = A(t₁)` from those assumptions via the
exactness of the Tucker projector-splitting integrator ([18, Theorem 4.1]); here it follows from
`hrec`, and for a class `𝓛` tailored to `P₀` (such as `{P₀}`) `hrec` is essentially that capture
itself. -/
theorem tucker_symm_exact_abstract {F : ℝ → E → E} {A : ℝ → E} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) {d : ℕ} {Q₀ P₀ : E →L[ℝ] E} {τ P : Fin (d + 1) → E →L[ℝ] E}
    (hP : ∀ i x, P i x = τ i (P₀ (τ i x)))
    (hsym : ∀ i, ∃ c : ℝ, c * c = 1 ∧ τ i (A t₁) = c • A t₁) {YK : ℝ → E}
    (hYK : ODESolution (fun t Y => Q₀ (F t Y)) YK t₀ t₁) (hK0 : YK t₀ = A t₀)
    (hQ : Q₀ (A t₀) = A t₀) (hcap : P₀ (YK t₁) = YK t₁) {𝓛 : Set (E →L[ℝ] E)} (hP𝓛 : P₀ ∈ 𝓛)
    (hrec : Exactness.IsRecoverable 𝓛 Q₀ (A t₁)) {y : ℝ → E}
    (hy : ODESolution (fun t Y => (List.ofFn P).prod (F t Y)) y t₀ t₁)
    (h0 : y t₀ = (List.ofFn P).prod (A t₀)) : y t₁ = A t₁ := by
  have hP0 : P₀ (A t₁) = A t₁ := Exactness.capture_abstract ht hA hYK hK0 hQ hcap hP𝓛 hrec
  have hPi : ∀ i, P i (A t₁) = A t₁ := by
    intro i
    obtain ⟨c, hc, hτA⟩ := hsym i
    rw [hP, hτA, map_smul, map_smul, hP0, hτA, smul_smul, hc, one_smul]
  refine Exactness.galerkin_exact ht hA hy h0 rfl (Exactness.list_prod_apply_eq_self ?_)
  intro T' hT'
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hT'
  exact hPi i

end Tucker

section TuckerExample

open LeanDLRA.Exactness LeanDLRA.Exactness.RankOneExample

/-- The hypotheses of `tucker_symm_exact_abstract` are satisfiable non-trivially: for `d + 1 = 2`
modes on symmetric `2 × 2` matrices (`τ = ![id, transpose]`, `P₀ = uuᵀ·`, hence
`P 1 = ·uuᵀ`), with the rank-one data of `RankOneExample` (`A₀ = e₁e₁ᵀ`, `A₁ = uuᵀ ≠ A₀`,
`u = (3/5, 4/5)`), the single K-step in mode 1 gives the basis `u`, and the core step with the
one basis `u` in both modes returns `A₁`.  (For two modes the Tucker core step is the BUG S-step.)
-/
example :
    (List.ofFn ![(leftProj u : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ),
        rightProj u]).prod A₀ +
      (List.ofFn ![(leftProj u : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ),
        rightProj u]).prod (A₁ - A₀) = A₁ ∧ A₁ ≠ A₀ := by
  refine ⟨?_, A₁_ne_A₀⟩
  have hA₁ : Apath 1 = u * S₀ * uᵀ := Apath_one.trans A₁_eq
  have h := tucker_symm_exact_abstract (F := fun _ _ => A₁ - A₀) (A := Apath) zero_le_one
    (isDerivRHS_add_smul A₀ (A₁ - A₀) 0 1) (d := 1)
    (P := ![leftProj u, rightProj u])
    (τ := ![ContinuousLinearMap.id ℝ (Matrix (Fin 2) (Fin 2) ℝ), Frobenius.transposeCLM])
    (P₀ := leftProj u) (Q₀ := rightProj e₁)
    (fun i x => by
      fin_cases i
      · simp
      · simp [leftProj_apply, rightProj_apply, Matrix.transpose_mul, Matrix.mul_assoc])
    (fun i => by
      fin_cases i
      · exact ⟨1, by norm_num, by simp⟩
      · refine ⟨1, by norm_num, ?_⟩
        rw [Apath_one, A₁_eq]
        simp [S₀, Matrix.transpose_mul])
    (YK := fun t => A₀ + t • rightProj e₁ (A₁ - A₀))
    (odeSolution_add_smul_of_const (fun _ _ => rfl) _ 0 1) (by simp [Apath_zero])
    (by simpa [Apath_zero] using rightProj_e₁_A₀)
    (by
      have h := leftProj_u_kStep
      rw [← one_smul ℝ (rightProj e₁ (A₁ - A₀))] at h
      exact h)
    (𝓛 := leftMulClass) (leftProj_mem_leftMulClass u)
    (isRecoverable_leftMulClass_of_isUnit e₁_orth hA₁ isUnit_u_e₁)
    (y := fun t => (List.ofFn ![(leftProj u : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] _),
        rightProj u]).prod A₀ +
      t • (List.ofFn ![(leftProj u : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] _), rightProj u]).prod
        (A₁ - A₀))
    (odeSolution_add_smul_of_const (fun _ _ => rfl) _ 0 1) (by simp [Apath_zero])
  simpa only [one_smul, Apath_one] using h

end TuckerExample

end LeanDLRA.Literature.P1906_01369
