import LeanDLRA.Matrix.Projectors
import LeanDLRA.Foundations.ODE

/-!
# Preservation of symmetry and skew-symmetry by the BUG integrator

Ceruti–Lubich, *An unconventional robust integrator for dynamical low-rank approximation*
([CerutiLubich2022, §3.5], **Theorem 5**) and Ceruti–Kusch–Lubich, *A rank-adaptive robust
integrator for dynamical low-rank approximation* ([CerutiKuschLubich2022, §2.3], **Theorem 3**)
consider square matrix ODEs `Ẏ = F(t, Y)` whose right-hand side satisfies

* (7) `F(t, Yᵀ)ᵀ = F(t, Y)` (symmetric case), or
* (8) `F(t, Yᵀ)ᵀ = -F(t, -Y)` (skew-symmetric case),

(numbering of Ceruti–Lubich; Ceruti–Kusch–Lubich write them as (10) `F(t, Y)ᵀ = F(t, Yᵀ)` and
(11) `F(t, Y)ᵀ = -F(t, -Yᵀ)`, which are equivalent to (7), (8) by the substitution `Y ↦ Yᵀ`)

and show that one step of the basis-update & Galerkin (BUG) integrator started from
`Y₀ = U₀ S₀ U₀ᵀ` with `S₀` symmetric (resp. skew-symmetric) yields a symmetric (resp.
skew-symmetric) approximation `Y₁ = U₁ S₁ U₁ᵀ`.

## Unified formulation

Both cases are treated at once with a sign `σ` (`σ * σ = 1`, i.e. `σ = 1` or `σ = -1`):

* `IsTwistSymm σ X : Xᵀ = σ • X` (symmetric for `σ = 1`, skew-symmetric for `σ = -1`);
* `IsTwistEquivariant σ F : F(t, σ Yᵀ) = σ F(t, Y)ᵀ`, i.e. `F(t, ·)` commutes with the involution
  `τ_σ Y = σ Yᵀ`.  We prove `IsTwistEquivariant 1 F ↔ (7)` and `IsTwistEquivariant (-1) F ↔ (8)`
  (`isTwistEquivariant_one_iff`, `isTwistEquivariant_neg_one_iff`).

## Main results

* `isTwistSymm_of_odeSolution`: the exact flow of a Lipschitz, `τ_σ`-equivariant `F` preserves
  `σ`-symmetry (the remark after (7)–(8) in both papers).  Proof: `σ A(t)ᵀ` solves the same ODE
  with the same initial value; uniqueness (`ODESolution.eqOn`).
* `lStep_eq_smul_kStep`: for `V₀ = U₀`, `S₀ᵀ = σ S₀`, the L-step `L' = F(t, U₀ Lᵀ)ᵀ U₀`,
  `L(t₀) = U₀ S₀ᵀ` and the K-step `K' = F(t, K U₀ᵀ) U₀`, `K(t₀) = U₀ S₀` satisfy `L(t) = σ K(t)`
  (map `K ↦ σ K` intertwines the two factor ODEs; uniqueness).  Hence a QR factorization
  `K(t₁) = U₁ R₁` gives the QR factorization `L(t₁) = U₁ (σ R₁)`, so one may take `V₁ = U₁`.
* `sStep_isTwistSymm`: with `V₁ = U₁` the S-step `S' = U₁ᵀ F(t, U₁ S U₁ᵀ) U₁` is again
  `τ_σ`-equivariant, so `S(t)` stays `σ`-symmetric when `S(t₀) = M S₀ Mᵀ`, `M = U₁ᵀ U₀`.
* `bug_isTwistSymm` (**CL Theorem 5**): one BUG step yields `L(t₁) = U₁ (σ R₁)`, a `σ`-symmetric
  `S₁ = S(t₁)` and a `σ`-symmetric `Y₁ = U₁ S₁ U₁ᵀ`; `bug_symm` and `bug_skew` are the two cases
  stated with (7) and (8).
* `bug_isTwistSymm_of_proj_eq`: the result does not depend on the choice of the orthonormal basis
  `V₁` of the L-step as long as it spans the same space as `U₁` (`V₁ V₁ᵀ = U₁ U₁ᵀ`, e.g.
  `V₁ = -U₁` from a sign-normalized QR of `-K(t₁)`): `Y₁ = U₁ S(t₁) V₁ᵀ` is `σ`-symmetric.  The
  proof goes through the full-space Galerkin ODE `Y' = Π F(t, Y) Π`, `Π = U₁ U₁ᵀ`
  (`galerkin_isTwistSymm`).
* `proj_eq_of_mul_eq`, `bug_isTwistSymm_qr` (**CL Theorem 5 with arbitrary QR factors**): if
  `K(t₁) = U₁ R₁` with `R₁` invertible (i.e. `K(t₁)` has full column rank), then *every*
  orthonormal factor `V₁` of `L(t₁) = V₁ R̃₁` satisfies `V₁ V₁ᵀ = U₁ U₁ᵀ`, and `Y₁` is
  `σ`-symmetric.
* `bug_not_symm_of_rank_deficient` (**counterexample**): without full column rank of `K(t₁)`,
  independent QR completions of `K(t₁)` and `L(t₁)` break symmetry (`2 × 2`, rank 1,
  `K(t₁) = L(t₁) = 0`), so the "`V₁ = U₁`" of the CL proof is a *consistent choice* of QR factors.
* `augBug_isTwistSymm` (**CKL Theorem 3**, augmented Galerkin step *before truncation*): for the
  rank-adaptive BUG integrator, `L(t₁) = σ K(t₁)` and `V₀ = U₀`, so the ranges of `(L(t₁), V₀)`
  and `(K(t₁), U₀)` coincide and one may take `V̂ = Û`; the augmented Galerkin solution `Ŝ(t₁)`
  and `Ŷ₁ = Û Ŝ(t₁) Ûᵀ` are `σ`-symmetric.
* Truncation (`isTwistSymm_trunc`, `not_isTwistSymm_neg_one_of_odd`, `even_card_of_trunc_skew`):
  a truncated SVD `P Σ Qᵀ` of a `σ`-symmetric `Ŝ` is `σ`-symmetric whenever the left and right
  truncated singular subspaces coincide (`P Pᵀ = Q Qᵀ`; for `σ = 1` this holds when there is a gap
  `σ_{r₁} > σ_{r₁+1}`), whereas a factorization `P T Qᵀ` with orthonormal `P`, `Q`, invertible
  `T` and an **odd** number of columns is never skew-symmetric.
* `augBug_trunc_not_skew` (**counterexample to CKL Theorem 3, skew case, with truncation**):
  `4 × 4`, rank 2, the singular values of `Ŝ(t₁)` are `(2, 2, 1, 1)`, the CKL rank rule picks
  `r₁ = 3` for every tolerance `ϑ ∈ [1, √2)`, and no rank-3 matrix is skew-symmetric.  So CKL
  Theorem 3 as published (which includes the truncation) is false in the skew-symmetric case;
  the statement proved here is the pre-truncation one.
* Satisfiability: `example`s with explicit orthonormal bases and nonzero results for the symmetric
  case (`2 × 2`, rank 1), the skew-symmetric case (`3 × 3`, rank 2), the sign-flipped basis
  `V₁ = -U₁`, and the augmented basis of the rank-adaptive integrator, all with constant fields
  `F ≡ C` (affine substep flows); they show joint satisfiability with non-degenerate data
  (orthonormal bases, invertible `S₀`, `Y₁ ≠ 0`).  One further example uses the non-constant
  linear field `F(t, Y) = A Y + Y Aᵀ` (`A` nilpotent), which satisfies both (7) and (8) and has a
  non-affine (exponential) S-step flow.

## The projector-splitting integrator

The remark before CL Theorem 5 states that symmetry preservation "does not hold for the
projector-splitting integrator".  We define one KSL step (`IsKSLStep`, K-step, backward S-step,
L-step with the updated basis `U₁`) and prove:

* `IsKSLStep.eq_const` (structural reason; the computation of Lubich–Oseledets,
  [LubichOseledets2014, §3.2] and proof of Thm 4.1, with increment `ΔA = h C`): for a constant field
  `F(t, Y) = C`, `Y₁ = Y₀ + h (C Q₀ + P₁ C (I - Q₀))` with `P₁ = U₁ U₁ᵀ`, `Q₀ = V₀ V₀ᵀ`: the left
  factor is updated before the right one, so the increment is an ordered (non-transpose-invariant)
  splitting;
* `ksl_not_symm`, `ksl_not_skew_rank_two`: explicit Lipschitz `F` satisfying (7), resp. (8), and
  (skew-)symmetric `Y₀ = U₀ S₀ U₀ᵀ` with `U₀ᵀ U₀ = 1` and **invertible** `S₀` (rank 1 in `ℝ²ˣ²`,
  resp. rank 2 in `ℝ⁴ˣ⁴`) for which a KSL step exists and *every* KSL step (any QR factors) returns
  a matrix that is not (skew-)symmetric.  `ksl_not_skew` is a smaller skew witness with the
  degenerate data `r = 1`, `S₀ = 0` (outside the rank-`r` setting with invertible `S₀`).  (In
  numerical tests, `3 × 3` rank-2 constant skew fields gave skew-symmetric KSL results, which is
  why the non-degenerate skew witness is `4 × 4`.)

## Formalization choices

* All substeps are written at the factor level as `ODESolution`s of the explicit factor fields
  `kField`, `lField`, `sField` (with the Frobenius norm, `open scoped LeanDLRA.Frobenius`).
  The orthonormality of `U₀`, `U₁` is **not** needed for symmetry preservation and is not
  assumed; the QR factorization enters only through `K(t₁) = U₁ R₁` (or a capture hypothesis).
* `F` is assumed globally Lipschitz in `Y` (assumption 1 of both papers); this is only used for
  uniqueness of the substep solutions, and any Lipschitz constant (even negative) is allowed.
* Generalization: the new basis may have any number `k` of columns (covering the augmented
  bases with `2r` columns of the rank-adaptive integrator).
* The SVD-based truncation step of the rank-adaptive integrator is not formalized as an
  algorithm (no SVD is formalized here); its effect is analysed through explicit factorizations
  (`isTwistSymm_trunc`, `not_isTwistSymm_neg_one_of_odd`, `augBug_trunc_not_skew`).
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace Symmetry

/-! ### Abstract ODE tools -/

section Abstract

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E']

omit [NormedSpace ℝ E] in
/-- An `L`-Lipschitz field is also `max L 0`-Lipschitz (so the sign of `L` never matters). -/
theorem lipschitzField_max_zero {F : ℝ → E → E} {L : ℝ} (hF : IsLipschitzField F L) :
    IsLipschitzField F (max L 0) := fun t x y =>
  (hF t x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

/-- Conjugating a Lipschitz field by continuous linear maps, `x ↦ Ψ (F t (Φ x))`, gives a
Lipschitz field with constant `‖Ψ‖ L ‖Φ‖`. -/
theorem lipschitzField_comp_clm {F : ℝ → E → E} {L : ℝ} (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (Φ : E' →L[ℝ] E) (Ψ : E →L[ℝ] E') :
    IsLipschitzField (fun t x => Ψ (F t (Φ x))) (‖Ψ‖ * L * ‖Φ‖) := fun t x y => by
  calc ‖Ψ (F t (Φ x)) - Ψ (F t (Φ y))‖ = ‖Ψ (F t (Φ x) - F t (Φ y))‖ := by rw [map_sub]
    _ ≤ ‖Ψ‖ * ‖F t (Φ x) - F t (Φ y)‖ := Ψ.le_opNorm _
    _ ≤ ‖Ψ‖ * (L * ‖Φ x - Φ y‖) := mul_le_mul_of_nonneg_left (hF t _ _) (norm_nonneg _)
    _ = ‖Ψ‖ * (L * ‖Φ (x - y)‖) := by rw [map_sub]
    _ ≤ ‖Ψ‖ * (L * (‖Φ‖ * ‖x - y‖)) := by
        gcongr
        exact Φ.le_opNorm _
    _ = ‖Ψ‖ * L * ‖Φ‖ * ‖x - y‖ := by ring

/-- A conjugated Lipschitz field `x ↦ Ψ (F t (Φ x))` is Lipschitz for some constant. -/
theorem exists_lipschitzField_comp_clm {F : ℝ → E → E} {L : ℝ} (hF : IsLipschitzField F L)
    (Φ : E' →L[ℝ] E) (Ψ : E →L[ℝ] E') :
    ∃ L', IsLipschitzField (fun t x => Ψ (F t (Φ x))) L' :=
  ⟨_, lipschitzField_comp_clm (lipschitzField_max_zero hF) (le_max_right _ _) Φ Ψ⟩

/-- **Intertwining.**  If a continuous linear map `Φ` satisfies `g t (Φ x) = Φ (f t x)`, then it
maps solutions of `y' = f(t, y)` to solutions of `z' = g(t, z)`. -/
theorem odeSolution_map {f : ℝ → E → E} {g : ℝ → E' → E'} {y : ℝ → E} {a b : ℝ}
    (hy : ODESolution f y a b) (Φ : E →L[ℝ] E') (h : ∀ t x, g t (Φ x) = Φ (f t x)) :
    ODESolution g (fun t => Φ (y t)) a b where
  cont := Φ.continuous.comp_continuousOn hy.cont
  deriv t ht := by
    rw [h]
    exact Φ.hasFDerivAt.comp_hasDerivWithinAt t (hy.deriv t ht)

/-- Uniqueness for a Lipschitz field with an arbitrary (possibly negative) constant. -/
theorem eqOn_of_lipschitzField {f : ℝ → E → E} {L : ℝ} (hf : IsLipschitzField f L)
    {y z : ℝ → E} {a b : ℝ} (hy : ODESolution f y a b) (hz : ODESolution f z a b)
    (h0 : y a = z a) : EqOn y z (Icc a b) :=
  hy.eqOn hz (lipschitzField_max_zero hf) (le_max_right _ _) h0

/-- Uniqueness for a field that is Lipschitz with some constant. -/
theorem eqOn_of_exists_lipschitzField {f : ℝ → E → E} (hf : ∃ L, IsLipschitzField f L)
    {y z : ℝ → E} {a b : ℝ} (hy : ODESolution f y a b) (hz : ODESolution f z a b)
    (h0 : y a = z a) : EqOn y z (Icc a b) :=
  eqOn_of_lipschitzField hf.choose_spec hy hz h0

/-- An affine function `t ↦ y₀ + (t - a) c` solves the ODE with constant field `c`. -/
theorem odeSolution_affine (y₀ c : E) (a b : ℝ) :
    ODESolution (fun _ _ => c) (fun t => y₀ + (t - a) • c) a b where
  cont := by fun_prop
  deriv t _ := by
    have h : HasDerivAt (fun t : ℝ => y₀ + (t - a) • c) c t := by
      simpa using (((hasDerivAt_id t).sub_const a).smul_const c).const_add y₀
    exact h.hasDerivWithinAt

/-- Every solution of the ODE with constant field `c` is affine: `y(b) = y(a) + (b - a) c`. -/
theorem odeSolution_const_eq {c : E} {y : ℝ → E} {a b : ℝ}
    (hy : ODESolution (fun _ _ => c) y a b) (hab : a ≤ b) : y b = y a + (b - a) • c :=
  hy.eqOn (odeSolution_affine (y a) c a b) (L := 0) (fun _ _ _ => by simp) le_rfl (by simp)
    ⟨hab, le_rfl⟩

end Abstract

/-! ### Twisted symmetry -/

section Twist

variable {k m n r : Type*}

/-- `X` is `σ`-symmetric: `Xᵀ = σ • X`.  For `σ = 1` this is symmetry, for `σ = -1`
skew-symmetry. -/
def IsTwistSymm (σ : ℝ) (X : Matrix k k ℝ) : Prop := Xᵀ = σ • X

/-- `F` is equivariant under the involution `Y ↦ σ Yᵀ`: `F(t, σ Yᵀ) = σ F(t, Y)ᵀ`. -/
def IsTwistEquivariant (σ : ℝ) (F : ℝ → Matrix n n ℝ → Matrix n n ℝ) : Prop :=
  ∀ t Y, F t (σ • Yᵀ) = σ • (F t Y)ᵀ

/-- Condition (7) of Ceruti–Lubich ([CerutiLubich2022]): `F(t, Yᵀ)ᵀ = F(t, Y)`. -/
def SymmCondition (F : ℝ → Matrix n n ℝ → Matrix n n ℝ) : Prop :=
  ∀ t Y, (F t Yᵀ)ᵀ = F t Y

/-- Condition (8) of Ceruti–Lubich ([CerutiLubich2022]): `F(t, Yᵀ)ᵀ = -F(t, -Y)`. -/
def SkewCondition (F : ℝ → Matrix n n ℝ → Matrix n n ℝ) : Prop :=
  ∀ t Y, (F t Yᵀ)ᵀ = -F t (-Y)

theorem isTwistSymm_one_iff (X : Matrix k k ℝ) : IsTwistSymm 1 X ↔ X.IsSymm := by
  simp [IsTwistSymm, Matrix.IsSymm]

theorem isTwistSymm_neg_one_iff (X : Matrix k k ℝ) : IsTwistSymm (-1) X ↔ Xᵀ = -X := by
  simp [IsTwistSymm]

/-- Condition (7) is equivariance under transposition. -/
theorem isTwistEquivariant_one_iff (F : ℝ → Matrix n n ℝ → Matrix n n ℝ) :
    IsTwistEquivariant 1 F ↔ SymmCondition F := by
  simp only [IsTwistEquivariant, SymmCondition, one_smul]
  constructor
  · intro h t Y
    rw [h, Matrix.transpose_transpose]
  · intro h t Y
    rw [← h t Y, Matrix.transpose_transpose]

/-- Condition (8) is equivariance under `Y ↦ -Yᵀ`. -/
theorem isTwistEquivariant_neg_one_iff (F : ℝ → Matrix n n ℝ → Matrix n n ℝ) :
    IsTwistEquivariant (-1) F ↔ SkewCondition F := by
  simp only [IsTwistEquivariant, SkewCondition, neg_one_smul]
  constructor
  · intro h t Y
    have := h t (-Y)
    rw [Matrix.transpose_neg, neg_neg] at this
    rw [this, Matrix.transpose_neg, Matrix.transpose_transpose]
  · intro h t Y
    have := h t (-Y)
    rw [neg_neg, Matrix.transpose_neg] at this
    rw [← Matrix.transpose_transpose (F t (-Yᵀ)), this, Matrix.transpose_neg]

/-- `σ`-symmetry is preserved by congruence: `S` `σ`-symmetric implies `M S Mᵀ` `σ`-symmetric. -/
theorem IsTwistSymm.mul_mul_transpose [Fintype k] {σ : ℝ} {S : Matrix k k ℝ}
    (hS : IsTwistSymm σ S) (M : Matrix m k ℝ) : IsTwistSymm σ (M * S * Mᵀ) := by
  unfold IsTwistSymm at hS ⊢
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hS,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]

/-- The exact flow of a Lipschitz, `τ_σ`-equivariant right-hand side preserves `σ`-symmetry:
`σ A(t)ᵀ` solves the same ODE with the same initial value (remark after (7)–(8) in
Ceruti–Lubich, [CerutiLubich2022, §3.5], and Ceruti–Kusch–Lubich, [CerutiKuschLubich2022, §2.3]). -/
theorem isTwistSymm_of_odeSolution [Fintype n] {σ L : ℝ} (hσ : σ * σ = 1)
    {F : ℝ → Matrix n n ℝ → Matrix n n ℝ} (hF : IsTwistEquivariant σ F)
    (hL : IsLipschitzField F L) {A : ℝ → Matrix n n ℝ} {t₀ t₁ : ℝ}
    (hA : ODESolution F A t₀ t₁) (h0 : IsTwistSymm σ (A t₀)) :
    ∀ t ∈ Icc t₀ t₁, IsTwistSymm σ (A t) := by
  let Φ : Matrix n n ℝ →L[ℝ] Matrix n n ℝ := σ • Frobenius.transposeCLM
  have hΦ : ∀ X, Φ X = σ • Xᵀ := fun X => rfl
  have hB := odeSolution_map hA Φ (g := F) fun t x => by rw [hΦ, hΦ, hF]
  have heq := eqOn_of_lipschitzField hL hA hB (by
    change A t₀ = Φ (A t₀)
    rw [hΦ, h0, smul_smul, hσ, one_smul])
  intro t ht
  have h1 : A t = σ • (A t)ᵀ := (heq ht).trans (hΦ _)
  unfold IsTwistSymm
  calc (A t)ᵀ = (σ * σ) • (A t)ᵀ := by rw [hσ, one_smul]
    _ = σ • A t := by rw [← smul_smul, ← h1]

end Twist

/-! ### Factor fields of the BUG integrator -/

section Factor

variable {k k' m n r : Type*} [Fintype k] [Fintype k'] [Fintype m] [Fintype n] [Fintype r]

/-- The K-step field `K ↦ F(t, K V₀ᵀ) V₀` (Ceruti–Lubich, [CerutiLubich2022, §3.1]). -/
def kField (V₀ : Matrix n r ℝ) (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t : ℝ)
    (K : Matrix m r ℝ) : Matrix m r ℝ :=
  F t (K * V₀ᵀ) * V₀

/-- The L-step field `L ↦ F(t, U₀ Lᵀ)ᵀ U₀` (Ceruti–Lubich, [CerutiLubich2022, §3.1]). -/
def lField (U₀ : Matrix m r ℝ) (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t : ℝ)
    (L : Matrix n r ℝ) : Matrix n r ℝ :=
  (F t (U₀ * Lᵀ))ᵀ * U₀

/-- The S-step (Galerkin) field `S ↦ U₁ᵀ F(t, U₁ S V₁ᵀ) V₁` (Ceruti–Lubich, [CerutiLubich2022],
§3.1). -/
def sField (U₁ : Matrix m k ℝ) (V₁ : Matrix n k' ℝ) (F : ℝ → Matrix m n ℝ → Matrix m n ℝ)
    (t : ℝ) (S : Matrix k k' ℝ) : Matrix k k' ℝ :=
  U₁ᵀ * F t (U₁ * S * V₁ᵀ) * V₁

/-- The full-space Galerkin field `Y ↦ P F(t, Y) Q` (for `P = U₁ U₁ᵀ`, `Q = V₁ V₁ᵀ` this is
`Y ↦ P₁ Q₁ F(t, Y)` in the notation of the abstract integrators). -/
def galField (P : Matrix m m ℝ) (Q : Matrix n n ℝ) (F : ℝ → Matrix m n ℝ → Matrix m n ℝ)
    (t : ℝ) (Y : Matrix m n ℝ) : Matrix m n ℝ :=
  P * F t Y * Q

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L : ℝ}

theorem exists_lipschitzField_kField (hF : IsLipschitzField F L) (V₀ : Matrix n r ℝ) :
    ∃ L', IsLipschitzField (kField V₀ F) L' :=
  exists_lipschitzField_comp_clm hF (Frobenius.rightMulCLM V₀ᵀ) (Frobenius.rightMulCLM V₀)

theorem exists_lipschitzField_lField (hF : IsLipschitzField F L) (U₀ : Matrix m r ℝ) :
    ∃ L', IsLipschitzField (lField U₀ F) L' :=
  exists_lipschitzField_comp_clm hF
    ((Frobenius.leftMulCLM U₀).comp Frobenius.transposeCLM)
    ((Frobenius.rightMulCLM U₀).comp Frobenius.transposeCLM)

theorem exists_lipschitzField_sField (hF : IsLipschitzField F L) (U₁ : Matrix m k ℝ)
    (V₁ : Matrix n k' ℝ) : ∃ L', IsLipschitzField (sField U₁ V₁ F) L' :=
  exists_lipschitzField_comp_clm hF
    ((Frobenius.rightMulCLM V₁ᵀ).comp (Frobenius.leftMulCLM U₁))
    ((Frobenius.rightMulCLM V₁).comp (Frobenius.leftMulCLM U₁ᵀ))

theorem exists_lipschitzField_galField (hF : IsLipschitzField F L) (P : Matrix m m ℝ)
    (Q : Matrix n n ℝ) : ∃ L', IsLipschitzField (galField P Q F) L' :=
  exists_lipschitzField_comp_clm hF (ContinuousLinearMap.id ℝ _)
    ((Frobenius.rightMulCLM Q).comp (Frobenius.leftMulCLM P))

/-- The factor S-step lifts to the full-space Galerkin ODE: if `S' = U₁ᵀ F(t, U₁ S V₁ᵀ) V₁`, then
`Y = U₁ S V₁ᵀ` solves `Y' = U₁ U₁ᵀ F(t, Y) V₁ V₁ᵀ`. -/
theorem odeSolution_galField_of_sField {U₁ : Matrix m k ℝ} {V₁ : Matrix n k' ℝ}
    {S : ℝ → Matrix k k' ℝ} {t₀ t₁ : ℝ} (hS : ODESolution (sField U₁ V₁ F) S t₀ t₁) :
    ODESolution (galField (U₁ * U₁ᵀ) (V₁ * V₁ᵀ) F) (fun t => U₁ * S t * V₁ᵀ) t₀ t₁ :=
  odeSolution_map hS ((Frobenius.rightMulCLM V₁ᵀ).comp (Frobenius.leftMulCLM U₁)) fun t X => by
    simp only [ContinuousLinearMap.comp_apply, Frobenius.leftMulCLM_apply,
      Frobenius.rightMulCLM_apply, galField, sField, Matrix.mul_assoc]

end Factor

/-! ### Symmetry preservation by the substeps -/

section Steps

variable {k k' n r : Type*} [Fintype k] [Fintype k'] [Fintype n] [Fintype r]
  {σ L : ℝ} {F : ℝ → Matrix n n ℝ → Matrix n n ℝ} {t₀ t₁ : ℝ}

/-- The map `K ↦ σ K` intertwines the K-step and L-step fields (for `V₀ = U₀`):
`lField U₀ F t (σ K) = σ kField U₀ F t K`.  This is the identity "the L-step is the K-step for
the transposed function" of Ceruti–Lubich ([CerutiLubich2022, §3.1] and proof of Thm 5). -/
theorem lField_smul (hF : IsTwistEquivariant σ F) (U₀ : Matrix n r ℝ) (t : ℝ)
    (K : Matrix n r ℝ) : lField U₀ F t (σ • K) = σ • kField U₀ F t K := by
  have h1 : U₀ * (σ • K)ᵀ = σ • (K * U₀ᵀ)ᵀ := by
    rw [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_smul]
  simp only [lField, kField]
  rw [h1, hF, Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.smul_mul]

/-- `σ K(t)` solves the L-step ODE whenever `K(t)` solves the K-step ODE (for `V₀ = U₀`). -/
theorem odeSolution_lField_smul (hF : IsTwistEquivariant σ F) {U₀ : Matrix n r ℝ}
    {K : ℝ → Matrix n r ℝ} (hK : ODESolution (kField U₀ F) K t₀ t₁) :
    ODESolution (lField U₀ F) (fun t => σ • K t) t₀ t₁ :=
  odeSolution_map hK (σ • ContinuousLinearMap.id ℝ (Matrix n r ℝ)) fun t x =>
    lField_smul hF U₀ t x

/-- **The L-step coincides with the K-step** (proof of Ceruti–Lubich, [CerutiLubich2022, Thm. 5]).
For `Y₀ = U₀ S₀ U₀ᵀ` with `S₀ᵀ = σ S₀` and a `τ_σ`-equivariant Lipschitz `F`, the solutions of
`K' = F(t, K U₀ᵀ) U₀`, `K(t₀) = U₀ S₀` and `L' = F(t, U₀ Lᵀ)ᵀ U₀`, `L(t₀) = U₀ S₀ᵀ` satisfy
`L(t) = σ K(t)`. -/
theorem lStep_eq_smul_kStep (hF : IsTwistEquivariant σ F) (hL : IsLipschitzField F L)
    {U₀ : Matrix n r ℝ} {S₀ : Matrix r r ℝ} (hS₀ : IsTwistSymm σ S₀)
    {K Lf : ℝ → Matrix n r ℝ} (hK : ODESolution (kField U₀ F) K t₀ t₁) (hK0 : K t₀ = U₀ * S₀)
    (hLs : ODESolution (lField U₀ F) Lf t₀ t₁) (hL0 : Lf t₀ = U₀ * S₀ᵀ) :
    ∀ t ∈ Icc t₀ t₁, Lf t = σ • K t :=
  eqOn_of_exists_lipschitzField (exists_lipschitzField_lField hL U₀) hLs
    (odeSolution_lField_smul hF hK) (by rw [hL0, hK0, hS₀, Matrix.mul_smul])

/-- With `V₀ = U₀`, the S-step field `S ↦ U₁ᵀ F(t, U₁ S U₁ᵀ) U₁` (i.e. `V₁ = U₁`) inherits the
`τ_σ`-equivariance of `F`. -/
theorem sField_isTwistEquivariant (hF : IsTwistEquivariant σ F) (U₁ : Matrix n k ℝ) :
    IsTwistEquivariant σ (sField U₁ U₁ F) := by
  intro t S
  have h1 : U₁ * (σ • Sᵀ) * U₁ᵀ = σ • (U₁ * S * U₁ᵀ)ᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_assoc]
  simp only [sField]
  rw [h1, hF]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_assoc]

/-- The full-space Galerkin field `Y ↦ P F(t, Y) Pᵀ` inherits the `τ_σ`-equivariance of `F`. -/
theorem galField_isTwistEquivariant (hF : IsTwistEquivariant σ F) (P : Matrix n n ℝ) :
    IsTwistEquivariant σ (galField P Pᵀ F) := by
  intro t Y
  simp only [galField]
  rw [hF]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_assoc]

/-- **The S-step preserves `σ`-symmetry** (proof of Ceruti–Lubich, [CerutiLubich2022, Thm. 5]):
if `S' = U₁ᵀ F(t, U₁ S U₁ᵀ) U₁` and `S(t₀)` is `σ`-symmetric, then so is `S(t)`. -/
theorem sStep_isTwistSymm (hσ : σ * σ = 1) (hF : IsTwistEquivariant σ F)
    (hL : IsLipschitzField F L) {U₁ : Matrix n k ℝ} {S : ℝ → Matrix k k ℝ}
    (hS : ODESolution (sField U₁ U₁ F) S t₀ t₁) (h0 : IsTwistSymm σ (S t₀)) :
    ∀ t ∈ Icc t₀ t₁, IsTwistSymm σ (S t) :=
  isTwistSymm_of_odeSolution hσ (sField_isTwistEquivariant hF U₁)
    (exists_lipschitzField_sField hL U₁ U₁).choose_spec hS h0

/-- **The full-space Galerkin step preserves `σ`-symmetry**: if `Y' = P F(t, Y) Pᵀ` and `Y(t₀)`
is `σ`-symmetric, then so is `Y(t)`. -/
theorem galerkin_isTwistSymm (hσ : σ * σ = 1) (hF : IsTwistEquivariant σ F)
    (hL : IsLipschitzField F L) {P : Matrix n n ℝ} {Y : ℝ → Matrix n n ℝ}
    (hY : ODESolution (galField P Pᵀ F) Y t₀ t₁) (h0 : IsTwistSymm σ (Y t₀)) :
    ∀ t ∈ Icc t₀ t₁, IsTwistSymm σ (Y t) :=
  isTwistSymm_of_odeSolution hσ (galField_isTwistEquivariant hF P)
    (exists_lipschitzField_galField hL P Pᵀ).choose_spec hY h0

end Steps

/-! ### One step of the BUG integrator -/

section BUG

variable {k k' n r : Type*} [Fintype k] [Fintype k'] [Fintype n] [Fintype r]
  {σ L : ℝ} {F : ℝ → Matrix n n ℝ → Matrix n n ℝ} {t₀ t₁ : ℝ}

/-- If `Y₀ = U₀ S₀ U₀ᵀ` is `σ`-symmetric and `U₀` has orthonormal columns, then `S₀` is
`σ`-symmetric (so the hypothesis of Ceruti–Lubich, Thm 5, on `Y₀` gives the one on `S₀`). -/
theorem isTwistSymm_of_mul_mul_transpose [DecidableEq r] {U₀ : Matrix n r ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) {S₀ : Matrix r r ℝ} (hY₀ : IsTwistSymm σ (U₀ * S₀ * U₀ᵀ)) :
    IsTwistSymm σ S₀ := by
  have h := hY₀.mul_mul_transpose U₀ᵀ
  rwa [Matrix.transpose_transpose,
    show U₀ᵀ * (U₀ * S₀ * U₀ᵀ) * U₀ = (U₀ᵀ * U₀) * S₀ * (U₀ᵀ * U₀) by
      simp only [Matrix.mul_assoc], hU₀, Matrix.one_mul, Matrix.mul_one] at h

/-- **Symmetry preservation of the BUG integrator** (Ceruti–Lubich, [CerutiLubich2022],
**Theorem 5**, unified for `σ = ±1`).  Let `F` be Lipschitz and `τ_σ`-equivariant
(`F(t, σ Yᵀ) = σ F(t, Y)ᵀ`, equivalent to (7) for `σ = 1` and to (8) for `σ = -1`), and let
`Y₀ = U₀ S₀ U₀ᵀ` with `S₀ᵀ = σ S₀` (so `V₀ = U₀`).  Run one step of the BUG integrator:

* K-step `K' = F(t, K U₀ᵀ) U₀`, `K(t₀) = U₀ S₀`, with a (QR) factorization `K(t₁) = U₁ R₁`;
* L-step `L' = F(t, U₀ Lᵀ)ᵀ U₀`, `L(t₀) = U₀ S₀ᵀ`;
* S-step with `V₁ = U₁`: `S' = U₁ᵀ F(t, U₁ S U₁ᵀ) U₁`, `S(t₀) = M S₀ Mᵀ`, `M = N = U₁ᵀ U₀`.

Then `L(t₁) = U₁ (σ R₁)`, so `V₁ = U₁` (with triangular factor `σ R₁`) is an admissible
factorization of the L-step result, and both `S₁ = S(t₁)` and `Y₁ = U₁ S₁ U₁ᵀ` are
`σ`-symmetric.  Orthonormality of `U₀`, `U₁` is not needed; the new basis may have any number
of columns.

The statement uses the consistent choice `V₁ = U₁` of the CL proof.  For an independently
computed QR factor `V₁` of `L(t₁)` see `bug_isTwistSymm_qr` (valid when `K(t₁)` has full column
rank) and the counterexample `bug_not_symm_of_rank_deficient` (rank-deficient `K(t₁)`). -/
theorem bug_isTwistSymm (hσ : σ * σ = 1) (hF : IsTwistEquivariant σ F)
    (hL : IsLipschitzField F L) {U₀ : Matrix n r ℝ} {S₀ : Matrix r r ℝ}
    (hS₀ : IsTwistSymm σ S₀) {K Lf : ℝ → Matrix n r ℝ}
    (hK : ODESolution (kField U₀ F) K t₀ t₁) (hK0 : K t₀ = U₀ * S₀)
    (hLs : ODESolution (lField U₀ F) Lf t₀ t₁) (hL0 : Lf t₀ = U₀ * S₀ᵀ)
    {U₁ : Matrix n k ℝ} {R₁ : Matrix k r ℝ} (hQR : K t₁ = U₁ * R₁)
    {S : ℝ → Matrix k k ℝ} (hS : ODESolution (sField U₁ U₁ F) S t₀ t₁)
    (hS0 : S t₀ = U₁ᵀ * U₀ * S₀ * (U₁ᵀ * U₀)ᵀ) (ht : t₀ ≤ t₁) :
    Lf t₁ = U₁ * (σ • R₁) ∧ IsTwistSymm σ (S t₁) ∧ IsTwistSymm σ (U₁ * S t₁ * U₁ᵀ) := by
  have hLK := lStep_eq_smul_kStep hF hL hS₀ hK hK0 hLs hL0 t₁ ⟨ht, le_rfl⟩
  have hS1 := sStep_isTwistSymm hσ hF hL hS (by rw [hS0]; exact hS₀.mul_mul_transpose _)
    t₁ ⟨ht, le_rfl⟩
  exact ⟨by rw [hLK, hQR, Matrix.mul_smul], hS1, hS1.mul_mul_transpose U₁⟩

/-- **Independence of the choice of `V₁`.**  In the setting of `bug_isTwistSymm`, let `V₁` be any
basis of the L-step with the same projector as `U₁` (`V₁ V₁ᵀ = U₁ U₁ᵀ`, e.g. `V₁ = U₁`, or
`V₁ = -U₁` from a sign-normalized QR decomposition of `L(t₁) = σ K(t₁)`), and run the S-step
`S' = U₁ᵀ F(t, U₁ S V₁ᵀ) V₁`, `S(t₀) = M S₀ Nᵀ`, `M = U₁ᵀ U₀`, `N = V₁ᵀ U₀`.  Then
`Y₁ = U₁ S(t₁) V₁ᵀ` is `σ`-symmetric.  (Proof: `U₁ S V₁ᵀ` solves the full-space Galerkin ODE
`Y' = P F(t, Y) Pᵀ`, `P = U₁ U₁ᵀ`, from the `σ`-symmetric value `P Y₀ Pᵀ`.)

The hypothesis `V₁ V₁ᵀ = U₁ U₁ᵀ` is automatic for QR factors when `K(t₁)` has full column rank
(`proj_eq_of_mul_eq`, `bug_isTwistSymm_qr`), but it can fail for legitimate QR factors when
`K(t₁)` is rank-deficient, and then `Y₁` need not be symmetric
(`bug_not_symm_of_rank_deficient`). -/
theorem bug_isTwistSymm_of_proj_eq (hσ : σ * σ = 1) (hF : IsTwistEquivariant σ F)
    (hL : IsLipschitzField F L) {U₀ : Matrix n r ℝ} {S₀ : Matrix r r ℝ}
    (hS₀ : IsTwistSymm σ S₀) {U₁ : Matrix n k ℝ} {V₁ : Matrix n k' ℝ}
    (hUV : V₁ * V₁ᵀ = U₁ * U₁ᵀ) {S : ℝ → Matrix k k' ℝ}
    (hS : ODESolution (sField U₁ V₁ F) S t₀ t₁) (hS0 : S t₀ = U₁ᵀ * U₀ * S₀ * (V₁ᵀ * U₀)ᵀ)
    (ht : t₀ ≤ t₁) : IsTwistSymm σ (U₁ * S t₁ * V₁ᵀ) := by
  have hY := odeSolution_galField_of_sField hS
  have hP : V₁ * V₁ᵀ = (U₁ * U₁ᵀ)ᵀ := by
    rw [hUV, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [hP] at hY
  have h0 : IsTwistSymm σ (U₁ * S t₀ * V₁ᵀ) := by
    have : U₁ * S t₀ * V₁ᵀ = (U₁ * U₁ᵀ) * (U₀ * S₀ * U₀ᵀ) * (U₁ * U₁ᵀ)ᵀ := by
      rw [← hP, hS0]
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [this]
    exact (hS₀.mul_mul_transpose U₀).mul_mul_transpose _
  exact galerkin_isTwistSymm hσ hF hL hY h0 t₁ ⟨ht, le_rfl⟩

/-- **QR factors of the K- and L-steps span the same space.**  If `U₁`, `V₁` have orthonormal
columns, `R₁` is invertible and `V₁ R₂ = U₁ R₁` (e.g. `L(t₁) = σ K(t₁)` with QR factorizations
`K(t₁) = U₁ R₁`, `L(t₁) = V₁ R̃₁`, `R₂ = R̃₁`, and `σ R₁` in place of `R₁`), then
`V₁ V₁ᵀ = U₁ U₁ᵀ`.  (Proof: `U₁ = V₁ W` with `W = R₂ R₁⁻¹` orthogonal.) -/
theorem proj_eq_of_mul_eq [DecidableEq r] {U₁ V₁ : Matrix n r ℝ} {R₁ R₂ : Matrix r r ℝ}
    (hU : U₁ᵀ * U₁ = 1) (hV : V₁ᵀ * V₁ = 1) (hR : R₁.det ≠ 0) (h : V₁ * R₂ = U₁ * R₁) :
    V₁ * V₁ᵀ = U₁ * U₁ᵀ := by
  have hU' : U₁ = V₁ * (R₂ * R₁⁻¹) := by
    rw [← Matrix.mul_assoc, h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hR),
      Matrix.mul_one]
  obtain ⟨W, hW⟩ : ∃ W, W = R₂ * R₁⁻¹ := ⟨_, rfl⟩
  rw [← hW] at hU'
  clear hW
  have hW : Wᵀ * W = 1 := by
    calc Wᵀ * W = (V₁ * W)ᵀ * (V₁ * W) := by
          rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc V₁ᵀ, hV, Matrix.one_mul]
      _ = 1 := by rw [← hU']; exact hU
  have hW' : W * Wᵀ = 1 := mul_eq_one_comm.1 hW
  rw [hU', Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc W, hW', Matrix.one_mul]

/-- **Ceruti–Lubich, Theorem 5, with arbitrary QR factors** ([CerutiLubich2022, Thm. 5]).  In the
setting of `bug_isTwistSymm` with `r`-column bases, let `K(t₁) = U₁ R₁` and `L(t₁) = V₁ R̃₁` be
*independently computed* factorizations with orthonormal `U₁`, `V₁`, and assume `R₁` invertible,
i.e. `K(t₁)` has full column rank.  Then `V₁ V₁ᵀ = U₁ U₁ᵀ` and the BUG result
`Y₁ = U₁ S(t₁) V₁ᵀ` (S-step with `U₁`, `V₁`, `S(t₀) = M S₀ Nᵀ`) is `σ`-symmetric.  The full-rank
assumption cannot be dropped: `bug_not_symm_of_rank_deficient`. -/
theorem bug_isTwistSymm_qr [DecidableEq r] (hσ : σ * σ = 1) (hF : IsTwistEquivariant σ F)
    (hL : IsLipschitzField F L) {U₀ : Matrix n r ℝ} {S₀ : Matrix r r ℝ}
    (hS₀ : IsTwistSymm σ S₀) {K Lf : ℝ → Matrix n r ℝ}
    (hK : ODESolution (kField U₀ F) K t₀ t₁) (hK0 : K t₀ = U₀ * S₀)
    (hLs : ODESolution (lField U₀ F) Lf t₀ t₁) (hL0 : Lf t₀ = U₀ * S₀ᵀ)
    {U₁ V₁ : Matrix n r ℝ} {R₁ R₂ : Matrix r r ℝ} (hU₁ : U₁ᵀ * U₁ = 1) (hV₁ : V₁ᵀ * V₁ = 1)
    (hQR : K t₁ = U₁ * R₁) (hR₁ : R₁.det ≠ 0) (hQRL : Lf t₁ = V₁ * R₂)
    {S : ℝ → Matrix r r ℝ} (hS : ODESolution (sField U₁ V₁ F) S t₀ t₁)
    (hS0 : S t₀ = U₁ᵀ * U₀ * S₀ * (V₁ᵀ * U₀)ᵀ) (ht : t₀ ≤ t₁) :
    V₁ * V₁ᵀ = U₁ * U₁ᵀ ∧ IsTwistSymm σ (U₁ * S t₁ * V₁ᵀ) := by
  have hLK := lStep_eq_smul_kStep hF hL hS₀ hK hK0 hLs hL0 t₁ ⟨ht, le_rfl⟩
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    simp at hσ
  have hUV : V₁ * V₁ᵀ = U₁ * U₁ᵀ := proj_eq_of_mul_eq (R₁ := σ • R₁) hU₁ hV₁
    (by rw [Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ hσ0) hR₁)
    (by rw [← hQRL, hLK, hQR, Matrix.mul_smul])
  exact ⟨hUV, bug_isTwistSymm_of_proj_eq hσ hF hL hS₀ hUV hS hS0 ht⟩

/-- **Symmetry preservation of the rank-adaptive BUG integrator** (Ceruti–Kusch–Lubich,
[CerutiKuschLubich2022], **Theorem 3**, augmented Galerkin step *before truncation*). In the setting
of `bug_isTwistSymm`, the L-step result is `L(t₁) = σ K(t₁)` and `V₀ = U₀`, so (as `σ ≠ 0`) the
matrices `(L(t₁), V₀)` and `(K(t₁), U₀)` have the same range: an orthonormal basis `Û` of the latter
is also one of the former, i.e. `V̂ = Û` is an admissible augmented basis for the L-step. (When
`(K(t₁), U₀)` has full rank `2r`, `Û` is determined up to an orthogonal change of basis, which does
not affect `Û Ŝ Ûᵀ`; when it is rank-deficient, independently computed bases may differ, as in
`bug_not_symm_of_rank_deficient`.) We record the first point as `L(t₁) = σ K(t₁)` and, if `Û`
captures `K(t₁)`, `Û Ûᵀ L(t₁) = L(t₁)`.

The augmented S-step `Ŝ' = Ûᵀ F(t, Û Ŝ Ûᵀ) Û`, `Ŝ(t₀) = M̂ S₀ M̂ᵀ`, `M̂ = Ûᵀ U₀`, then yields
`σ`-symmetric `Ŝ(t₁)` and `Ŷ₁ = Û Ŝ(t₁) Ûᵀ`; this part holds for *any* `Û` (it does not use the
capture hypothesis).

**Truncation.**  CKL Theorem 3 as published includes the truncation of `Ŝ(t₁)` to rank `r₁`
(minimal `r₁` with `(∑_{j > r₁} σ_j²)^{1/2} ≤ ϑ`).  For `σ = 1` the truncated SVD stays symmetric
whenever `σ_{r₁} > σ_{r₁+1}` (then the left and right truncated singular subspaces coincide,
`isTwistSymm_trunc`), but an arbitrary SVD with a tie `λ, -λ` at the cut can break symmetry
(e.g. `diag(1, -1)` truncated to rank 1 with left vector `(1, 1)/√2`).  For `σ = -1` the
singular values of `Ŝ(t₁)` come in equal pairs, and when the rank rule picks an **odd** `r₁` the
truncated `Y₁` has odd rank and cannot be skew-symmetric for any choice of singular vectors
(`not_isTwistSymm_neg_one_of_odd`).  This happens: `augBug_trunc_not_skew`.  So the
skew-symmetric case of CKL Theorem 3 with truncation is false; what is proved here is the
pre-truncation statement. -/
theorem augBug_isTwistSymm (hσ : σ * σ = 1) (hF : IsTwistEquivariant σ F)
    (hL : IsLipschitzField F L) {U₀ : Matrix n r ℝ} {S₀ : Matrix r r ℝ}
    (hS₀ : IsTwistSymm σ S₀) {K Lf : ℝ → Matrix n r ℝ}
    (hK : ODESolution (kField U₀ F) K t₀ t₁) (hK0 : K t₀ = U₀ * S₀)
    (hLs : ODESolution (lField U₀ F) Lf t₀ t₁) (hL0 : Lf t₀ = U₀ * S₀ᵀ)
    {Û : Matrix n k ℝ} (hcap : Û * Ûᵀ * K t₁ = K t₁)
    {Ŝ : ℝ → Matrix k k ℝ} (hS : ODESolution (sField Û Û F) Ŝ t₀ t₁)
    (hS0 : Ŝ t₀ = Ûᵀ * U₀ * S₀ * (Ûᵀ * U₀)ᵀ) (ht : t₀ ≤ t₁) :
    Lf t₁ = σ • K t₁ ∧ Û * Ûᵀ * Lf t₁ = Lf t₁ ∧ IsTwistSymm σ (Ŝ t₁) ∧
      IsTwistSymm σ (Û * Ŝ t₁ * Ûᵀ) := by
  have hLK := lStep_eq_smul_kStep hF hL hS₀ hK hK0 hLs hL0 t₁ ⟨ht, le_rfl⟩
  have hS1 := sStep_isTwistSymm hσ hF hL hS (by rw [hS0]; exact hS₀.mul_mul_transpose _)
    t₁ ⟨ht, le_rfl⟩
  exact ⟨hLK, by rw [hLK, Matrix.mul_smul, hcap], hS1, hS1.mul_mul_transpose Û⟩

/-- **Ceruti–Lubich, Theorem 5, symmetric case**: under condition (7), `S₀` symmetric, one BUG
step gives `L(t₁) = K(t₁)`, symmetric `S₁` and symmetric `Y₁ = U₁ S₁ U₁ᵀ`. -/
theorem bug_symm (hF : SymmCondition F) (hL : IsLipschitzField F L) {U₀ : Matrix n r ℝ}
    {S₀ : Matrix r r ℝ} (hS₀ : S₀.IsSymm) {K Lf : ℝ → Matrix n r ℝ}
    (hK : ODESolution (kField U₀ F) K t₀ t₁) (hK0 : K t₀ = U₀ * S₀)
    (hLs : ODESolution (lField U₀ F) Lf t₀ t₁) (hL0 : Lf t₀ = U₀ * S₀ᵀ)
    {U₁ : Matrix n k ℝ} {R₁ : Matrix k r ℝ} (hQR : K t₁ = U₁ * R₁)
    {S : ℝ → Matrix k k ℝ} (hS : ODESolution (sField U₁ U₁ F) S t₀ t₁)
    (hS0 : S t₀ = U₁ᵀ * U₀ * S₀ * (U₁ᵀ * U₀)ᵀ) (ht : t₀ ≤ t₁) :
    Lf t₁ = K t₁ ∧ (S t₁).IsSymm ∧ (U₁ * S t₁ * U₁ᵀ).IsSymm := by
  have h := bug_isTwistSymm (σ := 1) (by norm_num) ((isTwistEquivariant_one_iff F).2 hF) hL
    ((isTwistSymm_one_iff S₀).2 hS₀) hK hK0 hLs hL0 hQR hS hS0 ht
  refine ⟨by rw [h.1, hQR, one_smul], (isTwistSymm_one_iff _).1 h.2.1,
    (isTwistSymm_one_iff _).1 h.2.2⟩

/-- **Ceruti–Lubich, Theorem 5, skew-symmetric case**: under condition (8), `S₀` skew-symmetric,
one BUG step gives `L(t₁) = -K(t₁)`, skew-symmetric `S₁` and skew-symmetric
`Y₁ = U₁ S₁ U₁ᵀ`. -/
theorem bug_skew (hF : SkewCondition F) (hL : IsLipschitzField F L) {U₀ : Matrix n r ℝ}
    {S₀ : Matrix r r ℝ} (hS₀ : S₀ᵀ = -S₀) {K Lf : ℝ → Matrix n r ℝ}
    (hK : ODESolution (kField U₀ F) K t₀ t₁) (hK0 : K t₀ = U₀ * S₀)
    (hLs : ODESolution (lField U₀ F) Lf t₀ t₁) (hL0 : Lf t₀ = U₀ * S₀ᵀ)
    {U₁ : Matrix n k ℝ} {R₁ : Matrix k r ℝ} (hQR : K t₁ = U₁ * R₁)
    {S : ℝ → Matrix k k ℝ} (hS : ODESolution (sField U₁ U₁ F) S t₀ t₁)
    (hS0 : S t₀ = U₁ᵀ * U₀ * S₀ * (U₁ᵀ * U₀)ᵀ) (ht : t₀ ≤ t₁) :
    Lf t₁ = -K t₁ ∧ (S t₁)ᵀ = -S t₁ ∧ (U₁ * S t₁ * U₁ᵀ)ᵀ = -(U₁ * S t₁ * U₁ᵀ) := by
  have h := bug_isTwistSymm (σ := -1) (by norm_num) ((isTwistEquivariant_neg_one_iff F).2 hF)
    hL ((isTwistSymm_neg_one_iff S₀).2 hS₀) hK hK0 hLs hL0 hQR hS hS0 ht
  refine ⟨by rw [h.1, hQR, neg_one_smul, Matrix.mul_neg], (isTwistSymm_neg_one_iff _).1 h.2.1,
    (isTwistSymm_neg_one_iff _).1 h.2.2⟩

end BUG

/-! ### Truncation of a `σ`-symmetric core -/

section Truncation

variable {k n r : Type*} [Fintype k] [Fintype n] [Fintype r]

/-- **A factorization of odd rank is never skew-symmetric.**  If `P`, `Q` have orthonormal
columns, `T` is invertible and the number of columns is odd, then `P T Qᵀ` is not
skew-symmetric.  (Proof: skewness gives `Tᵀ = -(Qᵀ P) T (Qᵀ P)`; taking determinants,
`det T (1 + det(Qᵀ P)²) = 0`.)  This is the obstruction to the skew-symmetric case of
Ceruti–Kusch–Lubich ([CerutiKuschLubich2022]), Theorem 3, after truncation to odd rank; see
`augBug_trunc_not_skew`. -/
theorem not_isTwistSymm_neg_one_of_odd [DecidableEq r] (hr : Odd (Fintype.card r))
    {P Q : Matrix n r ℝ}
    (hP : Pᵀ * P = 1) (hQ : Qᵀ * Q = 1) {T : Matrix r r ℝ} (hT : T.det ≠ 0) :
    ¬ IsTwistSymm (-1) (P * T * Qᵀ) := by
  intro h
  unfold IsTwistSymm at h
  have e1 : Q * Tᵀ = -(P * T * (Qᵀ * P)) := by
    have := congrArg (· * P) h
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, neg_one_smul,
      Matrix.neg_mul, Matrix.mul_assoc, hP, Matrix.mul_one] at this
    rw [this, Matrix.mul_assoc P T]
  have e2 : Tᵀ = -((Qᵀ * P) * T * (Qᵀ * P)) := by
    have := congrArg (Qᵀ * ·) e1
    simp only [← Matrix.mul_assoc, hQ, Matrix.one_mul, Matrix.mul_neg] at this
    rw [this, Matrix.mul_assoc _ Qᵀ P]
  have e3 := congrArg Matrix.det e2
  rw [Matrix.det_transpose, Matrix.det_neg, hr.neg_one_pow, Matrix.det_mul, Matrix.det_mul] at e3
  have : T.det * (1 + (Qᵀ * P).det ^ 2) = 0 := by linear_combination e3
  rcases mul_eq_zero.1 this with h0 | h0
  · exact hT h0
  · nlinarith [sq_nonneg (Qᵀ * P).det]

/-- **Structure-preserving truncation.**  Let `Ŝ` be `σ`-symmetric and let `P`, `Q` (`r₁`
columns) and `D` satisfy the truncated-SVD relations `Ŝ Q = P D` and `Ŝᵀ P = Q Dᵀ` (e.g.
the leading `r₁` left and right singular vectors and `D = diag(σ₁, …, σ_{r₁})`).  If the left and
right truncated singular subspaces coincide, `P Pᵀ = Q Qᵀ`, then the truncation `P D Qᵀ`
(`= P Pᵀ Ŝ = Ŝ P Pᵀ`) is `σ`-symmetric, hence so is the rank-adaptive result `Û P D Qᵀ Ûᵀ`
(`IsTwistSymm.mul_mul_transpose`).

For a `σ`-symmetric `Ŝ` one has `Ŝ Ŝᵀ = Ŝᵀ Ŝ`, so when `σ_{r₁} > σ_{r₁+1}` both `P Pᵀ` and
`Q Qᵀ` are the (unique) spectral projector of this matrix for its `r₁` largest eigenvalues and the
hypothesis holds (this spectral argument is not formalized here).  For `σ = -1` and invertible
`D` it also forces `r₁` to be even (`even_card_of_trunc_skew`). -/
theorem isTwistSymm_trunc {σ : ℝ} {Ŝ : Matrix k k ℝ} (hS : IsTwistSymm σ Ŝ)
    {P Q : Matrix k r ℝ} {D : Matrix r r ℝ} (hright : Ŝ * Q = P * D) (hleft : Ŝᵀ * P = Q * Dᵀ)
    (hPQ : P * Pᵀ = Q * Qᵀ) : IsTwistSymm σ (P * D * Qᵀ) := by
  have h1 : P * D * Qᵀ = P * Pᵀ * Ŝ := by
    have := congrArg Matrix.transpose hleft
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_transpose] at this
    rw [Matrix.mul_assoc P Pᵀ, this, Matrix.mul_assoc]
  have h2 : P * D * Qᵀ = Ŝ * (P * Pᵀ) := by
    rw [← hright, hPQ, Matrix.mul_assoc]
  unfold IsTwistSymm at hS ⊢
  rw [h1, Matrix.transpose_mul, hS, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.smul_mul, ← h2, h1]

/-- In the skew-symmetric case, a structure-preserving truncation (`P Pᵀ = Q Qᵀ`) to an invertible
core is only possible for an even rank `r₁`. -/
theorem even_card_of_trunc_skew [DecidableEq r] {Ŝ : Matrix k k ℝ} (hS : IsTwistSymm (-1) Ŝ)
    {P Q : Matrix k r ℝ} {D : Matrix r r ℝ} (hP : Pᵀ * P = 1) (hQ : Qᵀ * Q = 1)
    (hD : D.det ≠ 0) (hright : Ŝ * Q = P * D) (hleft : Ŝᵀ * P = Q * Dᵀ)
    (hPQ : P * Pᵀ = Q * Qᵀ) : Even (Fintype.card r) := by
  by_contra hodd
  exact not_isTwistSymm_neg_one_of_odd (Nat.not_even_iff_odd.1 hodd) hP hQ hD
    (isTwistSymm_trunc hS hright hleft hPQ)

end Truncation

/-! ### Satisfiability of the hypotheses

The hypotheses of the BUG theorems are jointly satisfiable with orthonormal bases and nonzero
results.  We mostly use constant (hence Lipschitz) right-hand sides `F(t, Y) = C`, for which all
substep solutions are affine in `t` (`odeSolution_affine`); the last example has a non-constant
linear field. -/

section Examples

/-- Symmetric case (`bug_symm`): `C = [[0, 4], [4, -3]]`, `Y₀ = 3 e₁ e₁ᵀ` (`U₀ = e₁`, `S₀ = 3`),
`h = 1`.  Then `K(1) = (3, 4)ᵀ = U₁ R₁` with `U₁ = (3/5, 4/5)ᵀ`, `R₁ = 5`, and
`S(t) = 27/25 + 48 t/25`, so `Y₁ = 3 U₁ U₁ᵀ ≠ 0`. -/
example : ∃ (F : ℝ → Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (U₀ U₁ : Matrix (Fin 2) (Fin 1) ℝ) (S₀ R₁ : Matrix (Fin 1) (Fin 1) ℝ)
    (K Lf : ℝ → Matrix (Fin 2) (Fin 1) ℝ) (S : ℝ → Matrix (Fin 1) (Fin 1) ℝ),
    SymmCondition F ∧ IsLipschitzField F 0 ∧ U₀ᵀ * U₀ = 1 ∧ S₀.IsSymm ∧
    ODESolution (kField U₀ F) K 0 1 ∧ K 0 = U₀ * S₀ ∧
    ODESolution (lField U₀ F) Lf 0 1 ∧ Lf 0 = U₀ * S₀ᵀ ∧
    U₁ᵀ * U₁ = 1 ∧ K 1 = U₁ * R₁ ∧
    ODESolution (sField U₁ U₁ F) S 0 1 ∧ S 0 = U₁ᵀ * U₀ * S₀ * (U₁ᵀ * U₀)ᵀ ∧
    U₁ * S 1 * U₁ᵀ ≠ 0 := by
  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin 2) (Fin 2) ℝ, C = !![0, 4; 4, -3] := ⟨_, rfl⟩
  obtain ⟨U₀, hU₀⟩ : ∃ U₀ : Matrix (Fin 2) (Fin 1) ℝ, U₀ = !![1; 0] := ⟨_, rfl⟩
  obtain ⟨U₁, hU₁⟩ : ∃ U₁ : Matrix (Fin 2) (Fin 1) ℝ, U₁ = !![3/5; 4/5] := ⟨_, rfl⟩
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Matrix (Fin 1) (Fin 1) ℝ, S₀ = !![3] := ⟨_, rfl⟩
  obtain ⟨R₁, hR₁⟩ : ∃ R₁ : Matrix (Fin 1) (Fin 1) ℝ, R₁ = !![5] := ⟨_, rfl⟩
  refine ⟨fun _ _ => C, U₀, U₁, S₀, R₁, fun t => U₀ * S₀ + (t - 0) • (C * U₀),
    fun t => U₀ * S₀ᵀ + (t - 0) • (Cᵀ * U₀),
    fun t => U₁ᵀ * U₀ * S₀ * (U₁ᵀ * U₀)ᵀ + (t - 0) • (U₁ᵀ * C * U₁), fun _ _ => ?_,
    fun _ _ _ => by simp, ?_, ?_, odeSolution_affine _ _ _ _, by simp, odeSolution_affine _ _ _ _,
    by simp, ?_, ?_, odeSolution_affine _ _ _ _, by simp, ?_⟩
  · subst hC
    ext i j; fin_cases i <;> fin_cases j <;> simp
  · subst hU₀
    ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
  · subst hS₀
    ext i j; fin_cases i; fin_cases j; simp
  · subst hU₁
    ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]; norm_num
  · subst hC hU₀ hU₁ hS₀ hR₁
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply,
      Fin.sum_univ_two, Fin.sum_univ_one, Matrix.zero_apply, smul_eq_mul] at h00
    subst hC hU₀ hU₁ hS₀
    norm_num at h00

/-- Skew-symmetric case (`bug_skew`), rank 2 in `ℝ³ˣ³`: `C = [[0, 0, -3], [0, 0, 0], [3, 0, 0]]`,
`U₀ = [e₁, e₂]`, `S₀ = [[0, 4], [-4, 0]]`, `h = 1`.  Then `K(1) = [[0, 4], [-4, 0], [3, 0]] = U₁ R₁`
with `U₁ = [[0, 1], [-4/5, 0], [3/5, 0]]`, `R₁ = diag(5, 4)`, and `S(1) = [[0, 5], [-5, 0]]`. -/
example : ∃ (F : ℝ → Matrix (Fin 3) (Fin 3) ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (U₀ U₁ : Matrix (Fin 3) (Fin 2) ℝ) (S₀ R₁ : Matrix (Fin 2) (Fin 2) ℝ)
    (K Lf : ℝ → Matrix (Fin 3) (Fin 2) ℝ) (S : ℝ → Matrix (Fin 2) (Fin 2) ℝ),
    SkewCondition F ∧ IsLipschitzField F 0 ∧ U₀ᵀ * U₀ = 1 ∧ S₀ᵀ = -S₀ ∧
    ODESolution (kField U₀ F) K 0 1 ∧ K 0 = U₀ * S₀ ∧
    ODESolution (lField U₀ F) Lf 0 1 ∧ Lf 0 = U₀ * S₀ᵀ ∧
    U₁ᵀ * U₁ = 1 ∧ K 1 = U₁ * R₁ ∧
    ODESolution (sField U₁ U₁ F) S 0 1 ∧ S 0 = U₁ᵀ * U₀ * S₀ * (U₁ᵀ * U₀)ᵀ ∧
    U₁ * S 1 * U₁ᵀ ≠ 0 := by
  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin 3) (Fin 3) ℝ, C = !![0, 0, -3; 0, 0, 0; 3, 0, 0] :=
    ⟨_, rfl⟩
  obtain ⟨U₀, hU₀⟩ : ∃ U₀ : Matrix (Fin 3) (Fin 2) ℝ, U₀ = !![1, 0; 0, 1; 0, 0] := ⟨_, rfl⟩
  obtain ⟨U₁, hU₁⟩ : ∃ U₁ : Matrix (Fin 3) (Fin 2) ℝ, U₁ = !![0, 1; -4/5, 0; 3/5, 0] :=
    ⟨_, rfl⟩
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Matrix (Fin 2) (Fin 2) ℝ, S₀ = !![0, 4; -4, 0] := ⟨_, rfl⟩
  obtain ⟨R₁, hR₁⟩ : ∃ R₁ : Matrix (Fin 2) (Fin 2) ℝ, R₁ = !![5, 0; 0, 4] := ⟨_, rfl⟩
  refine ⟨fun _ _ => C, U₀, U₁, S₀, R₁, fun t => U₀ * S₀ + (t - 0) • (C * U₀),
    fun t => U₀ * S₀ᵀ + (t - 0) • (Cᵀ * U₀),
    fun t => U₁ᵀ * U₀ * S₀ * (U₁ᵀ * U₀)ᵀ + (t - 0) • (U₁ᵀ * C * U₁), fun _ _ => ?_,
    fun _ _ _ => by simp, ?_, ?_, odeSolution_affine _ _ _ _, by simp, odeSolution_affine _ _ _ _,
    by simp, ?_, ?_, odeSolution_affine _ _ _ _, by simp, ?_⟩
  · subst hC
    ext i j; fin_cases i <;> fin_cases j <;> simp
  · subst hU₀
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  · subst hS₀
    ext i j; fin_cases i <;> fin_cases j <;> simp
  · subst hU₁
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
  · subst hC hU₀ hU₁ hS₀ hR₁
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply,
      Fin.sum_univ_two, Fin.sum_univ_three, Matrix.zero_apply, smul_eq_mul] at h01
    subst hC hU₀ hU₁ hS₀
    norm_num at h01

/-- Independence of the choice of `V₁` (`bug_isTwistSymm_of_proj_eq`), symmetric data of the first
example with the sign-flipped basis `V₁ = -U₁`: `S(t) = -27/25 - 48 t/25`, `Y₁ = 3 U₁ U₁ᵀ`. -/
example : ∃ (F : ℝ → Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (U₀ U₁ V₁ : Matrix (Fin 2) (Fin 1) ℝ) (S₀ : Matrix (Fin 1) (Fin 1) ℝ)
    (S : ℝ → Matrix (Fin 1) (Fin 1) ℝ),
    IsTwistEquivariant 1 F ∧ IsLipschitzField F 0 ∧ IsTwistSymm 1 S₀ ∧
    U₁ᵀ * U₁ = 1 ∧ V₁ᵀ * V₁ = 1 ∧ V₁ * V₁ᵀ = U₁ * U₁ᵀ ∧ V₁ ≠ U₁ ∧
    ODESolution (sField U₁ V₁ F) S 0 1 ∧ S 0 = U₁ᵀ * U₀ * S₀ * (V₁ᵀ * U₀)ᵀ ∧
    U₁ * S 1 * V₁ᵀ ≠ 0 := by
  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin 2) (Fin 2) ℝ, C = !![0, 4; 4, -3] := ⟨_, rfl⟩
  obtain ⟨U₀, hU₀⟩ : ∃ U₀ : Matrix (Fin 2) (Fin 1) ℝ, U₀ = !![1; 0] := ⟨_, rfl⟩
  obtain ⟨U₁, hU₁⟩ : ∃ U₁ : Matrix (Fin 2) (Fin 1) ℝ, U₁ = !![3/5; 4/5] := ⟨_, rfl⟩
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Matrix (Fin 1) (Fin 1) ℝ, S₀ = !![3] := ⟨_, rfl⟩
  have hU₁o : U₁ᵀ * U₁ = 1 := by
    subst hU₁
    ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]; norm_num
  refine ⟨fun _ _ => C, U₀, U₁, -U₁, S₀,
    fun t => U₁ᵀ * U₀ * S₀ * ((-U₁)ᵀ * U₀)ᵀ + (t - 0) • (U₁ᵀ * C * -U₁), fun _ _ => ?_,
    fun _ _ _ => by simp, ?_, hU₁o, by simpa using hU₁o, by simp, fun h => ?_,
    odeSolution_affine _ _ _ _, by simp, ?_⟩
  · subst hC
    ext i j; fin_cases i <;> fin_cases j <;> simp
  · subst hS₀
    ext i j; fin_cases i; fin_cases j; simp
  · have h0 := congrFun (congrFun h 0) 0
    subst hU₁
    norm_num at h0
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply,
      Matrix.neg_apply, Fin.sum_univ_two, Fin.sum_univ_one, Matrix.zero_apply, smul_eq_mul] at h00
    subst hC hU₀ hU₁ hS₀
    norm_num at h00

/-- Rank-adaptive case (`augBug_isTwistSymm`), symmetric data of the first example: the augmented
basis `Û` of `[K(1), U₀] = [(3, 4)ᵀ, e₁]` (`2r = 2` columns) is `Û = I`, and
`Ŝ(t) = Y₀ + t C`, `Ŷ₁ = [[3, 4], [4, -3]]` (here the exact solution). -/
example : ∃ (F : ℝ → Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (U₀ : Matrix (Fin 2) (Fin 1) ℝ) (Û : Matrix (Fin 2) (Fin 2) ℝ) (S₀ : Matrix (Fin 1) (Fin 1) ℝ)
    (K Lf : ℝ → Matrix (Fin 2) (Fin 1) ℝ) (Ŝ : ℝ → Matrix (Fin 2) (Fin 2) ℝ),
    IsTwistEquivariant 1 F ∧ IsLipschitzField F 0 ∧ U₀ᵀ * U₀ = 1 ∧ IsTwistSymm 1 S₀ ∧
    ODESolution (kField U₀ F) K 0 1 ∧ K 0 = U₀ * S₀ ∧
    ODESolution (lField U₀ F) Lf 0 1 ∧ Lf 0 = U₀ * S₀ᵀ ∧
    Ûᵀ * Û = 1 ∧ Û * Ûᵀ * K 1 = K 1 ∧ Û * Ûᵀ * U₀ = U₀ ∧
    ODESolution (sField Û Û F) Ŝ 0 1 ∧ Ŝ 0 = Ûᵀ * U₀ * S₀ * (Ûᵀ * U₀)ᵀ ∧
    Û * Ŝ 1 * Ûᵀ ≠ 0 := by
  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin 2) (Fin 2) ℝ, C = !![0, 4; 4, -3] := ⟨_, rfl⟩
  obtain ⟨U₀, hU₀⟩ : ∃ U₀ : Matrix (Fin 2) (Fin 1) ℝ, U₀ = !![1; 0] := ⟨_, rfl⟩
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Matrix (Fin 1) (Fin 1) ℝ, S₀ = !![3] := ⟨_, rfl⟩
  refine ⟨fun _ _ => C, U₀, 1, S₀, fun t => U₀ * S₀ + (t - 0) • (C * U₀),
    fun t => U₀ * S₀ᵀ + (t - 0) • (Cᵀ * U₀),
    fun t => (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * U₀ * S₀ * ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * U₀)ᵀ +
      (t - 0) • ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * C * 1), fun _ _ => ?_,
    fun _ _ _ => by simp, ?_, ?_, odeSolution_affine _ _ _ _, by simp, odeSolution_affine _ _ _ _,
    by simp, by simp, by simp, by simp, odeSolution_affine _ _ _ _, by simp, ?_⟩
  · subst hC
    ext i j; fin_cases i <;> fin_cases j <;> simp
  · subst hU₀
    ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
  · subst hS₀
    ext i j; fin_cases i; fin_cases j; simp
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.add_apply,
      Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_one,
      Matrix.zero_apply, smul_eq_mul] at h01
    subst hC hU₀ hS₀
    norm_num at h01

/-- Non-constant right-hand side (`bug_symm`): `F(t, Y) = A Y + Y Aᵀ` with nilpotent
`A = [[0, 1], [0, 0]]` is linear (hence Lipschitz), not constant, and satisfies both (7) and (8).
With `U₀ = e₂`, `S₀ = 4`, `h = 3/4`: since `U₀ᵀ A U₀ = 0` and `A² = 0`, the K- and L-steps are
`K(t) = L(t) = (I + t A) U₀ S₀`, `K(3/4) = (3, 4)ᵀ = U₁ R₁` with `U₁ = (3/5, 4/5)ᵀ`, `R₁ = 5`, and
the S-step is the scalar ODE `S' = 2 (U₁ᵀ A U₁) S = (24/25) S`, with the non-affine solution
`S(t) = e^{24 t/25} · 64/25`; `Y₁ = U₁ S(3/4) U₁ᵀ ≠ 0`. -/
example : ∃ (F : ℝ → Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) (L : ℝ)
    (U₀ U₁ : Matrix (Fin 2) (Fin 1) ℝ) (S₀ R₁ : Matrix (Fin 1) (Fin 1) ℝ)
    (K Lf : ℝ → Matrix (Fin 2) (Fin 1) ℝ) (S : ℝ → Matrix (Fin 1) (Fin 1) ℝ),
    SymmCondition F ∧ SkewCondition F ∧ IsLipschitzField F L ∧ F 0 1 ≠ F 0 0 ∧
    U₀ᵀ * U₀ = 1 ∧ S₀.IsSymm ∧
    ODESolution (kField U₀ F) K 0 (3 / 4) ∧ K 0 = U₀ * S₀ ∧
    ODESolution (lField U₀ F) Lf 0 (3 / 4) ∧ Lf 0 = U₀ * S₀ᵀ ∧
    U₁ᵀ * U₁ = 1 ∧ K (3 / 4) = U₁ * R₁ ∧
    ODESolution (sField U₁ U₁ F) S 0 (3 / 4) ∧ S 0 = U₁ᵀ * U₀ * S₀ * (U₁ᵀ * U₀)ᵀ ∧
    U₁ * S (3 / 4) * U₁ᵀ ≠ 0 := by
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin 2) (Fin 2) ℝ, A = !![0, 1; 0, 0] := ⟨_, rfl⟩
  obtain ⟨U₀, hU₀⟩ : ∃ U₀ : Matrix (Fin 2) (Fin 1) ℝ, U₀ = !![0; 1] := ⟨_, rfl⟩
  obtain ⟨U₁, hU₁⟩ : ∃ U₁ : Matrix (Fin 2) (Fin 1) ℝ, U₁ = !![3/5; 4/5] := ⟨_, rfl⟩
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Matrix (Fin 1) (Fin 1) ℝ, S₀ = !![4] := ⟨_, rfl⟩
  let F : ℝ → Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun _ Y => A * Y + Y * Aᵀ
  let Ψ : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
    Frobenius.leftMulCLM A + Frobenius.rightMulCLM Aᵀ
  have hΨ : ∀ t x y, F t x - F t y = Ψ (x - y) := fun t x y => by
    simp only [F, Ψ, add_apply, Frobenius.leftMulCLM_apply,
      Frobenius.rightMulCLM_apply, Matrix.mul_sub, Matrix.sub_mul]
    abel
  -- solutions of `X' = A X` with `A² = 0` starting at `X₀` are `X₀ + t A X₀`
  have hlin : ∀ (f : ℝ → Matrix (Fin 2) (Fin 1) ℝ → Matrix (Fin 2) (Fin 1) ℝ)
      (X₀ : Matrix (Fin 2) (Fin 1) ℝ), (∀ t X, f t X = A * X) → A * A = 0 →
      ODESolution f (fun t => X₀ + (t - 0) • (A * X₀)) 0 (3 / 4) := by
    intro f X₀ hf hA2
    have h := odeSolution_affine X₀ (A * X₀) 0 (3 / 4)
    refine ⟨h.cont, fun t ht => ?_⟩
    rw [hf, Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc, hA2, Matrix.zero_mul, smul_zero,
      add_zero]
    exact h.deriv t ht
  have hA2 : A * A = 0 := by
    subst hA
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  have hS : ODESolution (sField U₁ U₁ F) (fun t => Real.exp (24 / 25 * t) •
      (U₁ᵀ * U₀ * S₀ * (U₁ᵀ * U₀)ᵀ)) 0 (3 / 4) := by
    have hf : ∀ t X, sField U₁ U₁ F t X = (24 / 25 : ℝ) • X := by
      intro t X
      subst hA hU₁
      ext i j; fin_cases i; fin_cases j
      simp only [sField, F, Matrix.mul_apply, Matrix.add_apply, Matrix.transpose_apply,
        Matrix.smul_apply, Fin.sum_univ_two, Fin.sum_univ_one, smul_eq_mul]
      norm_num
      ring
    refine ⟨by fun_prop, fun t _ => ?_⟩
    rw [hf, smul_smul]
    have h := (((hasDerivAt_id t).const_mul (24 / 25 : ℝ)).exp).smul_const
      (U₁ᵀ * U₀ * S₀ * (U₁ᵀ * U₀)ᵀ)
    simp only [id, mul_one] at h
    rw [mul_comm]
    exact h.hasDerivWithinAt
  refine ⟨F, ‖Ψ‖, U₀, U₁, S₀, !![5], fun t => U₀ * S₀ + (t - 0) • (A * (U₀ * S₀)),
    fun t => U₀ * S₀ᵀ + (t - 0) • (A * (U₀ * S₀ᵀ)),
    fun t => Real.exp (24 / 25 * t) • (U₁ᵀ * U₀ * S₀ * (U₁ᵀ * U₀)ᵀ), fun _ _ => ?_, fun _ _ => ?_,
    fun t x y => by rw [hΨ t x y]; exact Ψ.le_opNorm _, ?_, ?_, ?_,
    hlin _ _ (fun t K => ?_) hA2, by simp, hlin _ _ (fun t L => ?_) hA2, by simp, ?_, ?_, hS,
    by simp, ?_⟩
  · simp only [F, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose]
    abel
  · simp only [F, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_neg, Matrix.neg_mul]
    abel
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    subst hA
    simp [F] at h01
  · subst hU₀
    ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
  · subst hS₀
    ext i j; fin_cases i; fin_cases j; simp
  · subst hA hU₀
    ext i j; fin_cases i <;> fin_cases j <;>
      simp only [kField, F, Matrix.mul_apply, Matrix.add_apply, Matrix.transpose_apply,
        Fin.sum_univ_two, Fin.sum_univ_one] <;> norm_num
  · subst hA hU₀
    ext i j; fin_cases i <;> fin_cases j <;>
      simp only [lField, F, Matrix.mul_apply, Matrix.add_apply, Matrix.transpose_apply,
        Fin.sum_univ_two, Fin.sum_univ_one] <;> norm_num
  · subst hU₁
    ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]; norm_num
  · subst hA hU₀ hU₁ hS₀
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply]
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.transpose_apply,
      Fin.sum_univ_two, Fin.sum_univ_one, Matrix.zero_apply, smul_eq_mul] at h00
    subst hU₀ hU₁ hS₀
    norm_num at h00

end Examples

/-! ### Counterexamples for the BUG integrators -/

section Counterexamples

/-- **Counterexample: CL Theorem 5 with independent QR factors of a rank-deficient `K(t₁)`.**
`n = 2`, `r = 1`, constant symmetric `F ≡ C = diag(-1, 1)` (condition (7)), `U₀ = e₁`, `S₀ = 1`,
`h = 1`.  Then `K(1) = L(1) = 0`, so `U₁ = e₂` (`R₁ = 0`) and `V₁ = (3/5, 4/5)ᵀ` (`R̃₁ = 0`) are
legitimate QR factors, the S-step gives `S(0) = 0`, `S(1) = 4/5`, and
`Y₁ = U₁ S(1) V₁ᵀ = [[0, 0], [12/25, 16/25]]` is not symmetric.  The "`V₁ = U₁`" in the proof of
CL Theorem 5 is therefore a consistent choice of QR factors; with independent choices the theorem
needs full column rank of `K(t₁)` (`bug_isTwistSymm_qr`). -/
theorem bug_not_symm_of_rank_deficient : ∃ (C : Matrix (Fin 2) (Fin 2) ℝ)
    (U₀ U₁ V₁ : Matrix (Fin 2) (Fin 1) ℝ) (S₀ R₁ R₂ : Matrix (Fin 1) (Fin 1) ℝ)
    (K Lf : ℝ → Matrix (Fin 2) (Fin 1) ℝ) (S : ℝ → Matrix (Fin 1) (Fin 1) ℝ),
    SymmCondition (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => C) ∧
    IsLipschitzField (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => C) 0 ∧
    U₀ᵀ * U₀ = 1 ∧ S₀.IsSymm ∧ S₀.det ≠ 0 ∧
    ODESolution (kField U₀ fun _ _ => C) K 0 1 ∧ K 0 = U₀ * S₀ ∧
    ODESolution (lField U₀ fun _ _ => C) Lf 0 1 ∧ Lf 0 = U₀ * S₀ᵀ ∧
    U₁ᵀ * U₁ = 1 ∧ K 1 = U₁ * R₁ ∧ V₁ᵀ * V₁ = 1 ∧ Lf 1 = V₁ * R₂ ∧
    ODESolution (sField U₁ V₁ fun _ _ => C) S 0 1 ∧ S 0 = U₁ᵀ * U₀ * S₀ * (V₁ᵀ * U₀)ᵀ ∧
    ¬ (U₁ * S 1 * V₁ᵀ).IsSymm := by
  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin 2) (Fin 2) ℝ, C = !![-1, 0; 0, 1] := ⟨_, rfl⟩
  obtain ⟨U₀, hU₀⟩ : ∃ U₀ : Matrix (Fin 2) (Fin 1) ℝ, U₀ = !![1; 0] := ⟨_, rfl⟩
  obtain ⟨U₁, hU₁⟩ : ∃ U₁ : Matrix (Fin 2) (Fin 1) ℝ, U₁ = !![0; 1] := ⟨_, rfl⟩
  obtain ⟨V₁, hV₁⟩ : ∃ V₁ : Matrix (Fin 2) (Fin 1) ℝ, V₁ = !![3/5; 4/5] := ⟨_, rfl⟩
  refine ⟨C, U₀, U₁, V₁, 1, 0, 0, fun t => U₀ * (1 : Matrix (Fin 1) (Fin 1) ℝ) + (t - 0) • (C * U₀),
    fun t => U₀ * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ + (t - 0) • (Cᵀ * U₀),
    fun t => U₁ᵀ * U₀ * 1 * (V₁ᵀ * U₀)ᵀ + (t - 0) • (U₁ᵀ * C * V₁), fun _ _ => ?_,
    fun _ _ _ => by simp, ?_, by simp, by simp, odeSolution_affine _ _ _ _, by simp,
    odeSolution_affine _ _ _ _, by simp, ?_, ?_, ?_, ?_, odeSolution_affine _ _ _ _, by simp, ?_⟩
  · subst hC
    ext i j; fin_cases i <;> fin_cases j <;> simp
  · subst hU₀
    ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
  · subst hU₁
    ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
  · subst hC hU₀
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  · subst hV₁
    ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]; norm_num
  · subst hC hU₀
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  · intro h
    have h01 := Matrix.IsSymm.ext_iff.1 h 0 1
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply,
      Fin.sum_univ_two, Fin.sum_univ_one, smul_eq_mul, Matrix.one_apply] at h01
    subst hC hU₀ hU₁ hV₁
    norm_num at h01

/-- **Counterexample: CKL Theorem 3 with truncation fails in the skew-symmetric case**
(Ceruti–Kusch–Lubich, [CerutiKuschLubich2022, Thm. 3], read with the truncation step 3 of §2.1).
`n = 4`, `r = 2`, `U₀ = [e₁, e₂]`, `S₀ = [[0, 1], [-1, 0]]` (invertible), constant skew
`F ≡ C` (condition (8)), `h = 1`.  Then `(K(1), U₀)` has full rank `4` (we exhibit `W₁`, `W₂` with
`K(1) W₁ + U₀ W₂ = I`), so `Û = I` is the augmented basis (and `V̂ = Û` by `augBug_isTwistSymm`),
and the augmented Galerkin step gives
`Ŝ(1) = Y₀ + C = 2 (e₁e₃ᵀ - e₃e₁ᵀ) + (e₂e₄ᵀ - e₄e₂ᵀ) = P diag(2, 2, 1, 1) Qᵀ`
with orthogonal `P`, `Q`, i.e. the singular values are `(2, 2, 1, 1)`.  The CKL rank rule
(minimal `r₁` with `(∑_{j > r₁} σ_j²)^{1/2} ≤ ϑ`) gives `r₁ = 3` for every `ϑ ∈ [1, √2)`
(tails `1` for `r₁ = 3` and `√2` for `r₁ = 2`), and then **no** rank-3 result
`Y₁ = U₁ S₁ V₁ᵀ` (orthonormal `U₁ = Û P₁`, `V₁ = Û Q₁`, invertible `S₁`; any choice of singular
vectors) is skew-symmetric (`not_isTwistSymm_neg_one_of_odd`). -/
theorem augBug_trunc_not_skew : ∃ (C : Matrix (Fin 4) (Fin 4) ℝ) (U₀ : Matrix (Fin 4) (Fin 2) ℝ)
    (S₀ : Matrix (Fin 2) (Fin 2) ℝ) (K Lf : ℝ → Matrix (Fin 4) (Fin 2) ℝ)
    (Û : Matrix (Fin 4) (Fin 4) ℝ) (Ŝ : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (P Q : Matrix (Fin 4) (Fin 4) ℝ),
    SkewCondition (fun (_ : ℝ) (_ : Matrix (Fin 4) (Fin 4) ℝ) => C) ∧
    IsLipschitzField (fun (_ : ℝ) (_ : Matrix (Fin 4) (Fin 4) ℝ) => C) 0 ∧
    U₀ᵀ * U₀ = 1 ∧ S₀ᵀ = -S₀ ∧ S₀.det ≠ 0 ∧
    ODESolution (kField U₀ fun _ _ => C) K 0 1 ∧ K 0 = U₀ * S₀ ∧
    ODESolution (lField U₀ fun _ _ => C) Lf 0 1 ∧ Lf 0 = U₀ * S₀ᵀ ∧
    (∃ W₁ W₂ : Matrix (Fin 2) (Fin 4) ℝ, K 1 * W₁ + U₀ * W₂ = 1) ∧ Ûᵀ * Û = 1 ∧
    ODESolution (sField Û Û fun _ _ => C) Ŝ 0 1 ∧ Ŝ 0 = Ûᵀ * U₀ * S₀ * (Ûᵀ * U₀)ᵀ ∧
    Pᵀ * P = 1 ∧ Qᵀ * Q = 1 ∧ Ŝ 1 = P * Matrix.diagonal ![2, 2, 1, 1] * Qᵀ ∧
    ∀ (U₁ V₁ : Matrix (Fin 4) (Fin 3) ℝ) (S₁ : Matrix (Fin 3) (Fin 3) ℝ),
      U₁ᵀ * U₁ = 1 → V₁ᵀ * V₁ = 1 → S₁.det ≠ 0 → ¬ IsTwistSymm (-1) (U₁ * S₁ * V₁ᵀ) := by
  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin 4) (Fin 4) ℝ,
      C = !![0, -1, 2, 0; 1, 0, 0, 1; -2, 0, 0, 0; 0, -1, 0, 0] := ⟨_, rfl⟩
  obtain ⟨U₀, hU₀⟩ : ∃ U₀ : Matrix (Fin 4) (Fin 2) ℝ, U₀ = !![1, 0; 0, 1; 0, 0; 0, 0] :=
    ⟨_, rfl⟩
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Matrix (Fin 2) (Fin 2) ℝ, S₀ = !![0, 1; -1, 0] := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin 4) (Fin 4) ℝ,
      P = !![1, 0, 0, 0; 0, 0, 1, 0; 0, -1, 0, 0; 0, 0, 0, -1] := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin 4) (Fin 4) ℝ,
      Q = !![0, 1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0] := ⟨_, rfl⟩
  refine ⟨C, U₀, S₀, fun t => U₀ * S₀ + (t - 0) • (C * U₀),
    fun t => U₀ * S₀ᵀ + (t - 0) • (Cᵀ * U₀), 1,
    fun t => (1 : Matrix (Fin 4) (Fin 4) ℝ)ᵀ * U₀ * S₀ * ((1 : Matrix (Fin 4) (Fin 4) ℝ)ᵀ * U₀)ᵀ +
      (t - 0) • ((1 : Matrix (Fin 4) (Fin 4) ℝ)ᵀ * C * 1), P, Q, fun _ _ => ?_,
    fun _ _ _ => by simp, ?_, ?_, ?_, odeSolution_affine _ _ _ _, by simp,
    odeSolution_affine _ _ _ _, by simp,
    ⟨!![0, 0, -1/2, 0; 0, 0, 0, -1], !![1, 0, 0, 0; 0, 1, 0, 0], ?_⟩, by simp,
    odeSolution_affine _ _ _ _, by simp, ?_, ?_, ?_, fun U₁ V₁ S₁ hU₁ hV₁ hS₁ =>
      not_isTwistSymm_neg_one_of_odd (by decide) hU₁ hV₁ hS₁⟩
  · subst hC
    ext i j; fin_cases i <;> fin_cases j <;> simp
  · subst hU₀
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  · subst hS₀
    ext i j; fin_cases i <;> fin_cases j <;> simp
  · subst hS₀
    simp [Matrix.det_fin_two]
  · subst hC hU₀ hS₀
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
  · subst hP
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  · subst hQ
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  · subst hC hU₀ hS₀ hP hQ
    ext i j; fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
        Matrix.transpose_apply, Matrix.one_apply,
        Matrix.diagonal_apply, Fin.sum_univ_four, Fin.sum_univ_two, smul_eq_mul] <;>
      norm_num

end Counterexamples

/-! ### The projector-splitting integrator does not preserve symmetry -/

section KSL

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]

/-- One step of the **projector-splitting (KSL) integrator** of Lubich–Oseledets, as recalled in
Ceruti–Lubich ([CerutiLubich2022, §2]), from `Y₀ = U₀ S₀ V₀ᵀ` to `Y₁ = U₁ S₁ V₁ᵀ`:

1. K-step: `K' = F(t, K V₀ᵀ) V₀`, `K(t₀) = U₀ S₀`, QR factorization `K(t₁) = U₁ Ŝ₁`;
2. S-step (backward): `S' = -U₁ᵀ F(t, U₁ S V₀ᵀ) V₀`, `S(t₀) = Ŝ₁`, `S̃₀ = S(t₁)`;
3. L-step: `L' = F(t, U₁ Lᵀ)ᵀ U₁`, `L(t₀) = V₀ S̃₀ᵀ`, QR factorization `L(t₁) = V₁ S₁ᵀ`.

The QR factors are only required to have orthonormal columns (triangularity plays no role). -/
def IsKSLStep (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ t₁ : ℝ) (U₀ : Matrix m r ℝ)
    (S₀ : Matrix r r ℝ) (V₀ : Matrix n r ℝ) (U₁ : Matrix m r ℝ) (S₁ : Matrix r r ℝ)
    (V₁ : Matrix n r ℝ) : Prop :=
  ∃ (K : ℝ → Matrix m r ℝ) (Ŝ₁ : Matrix r r ℝ) (S : ℝ → Matrix r r ℝ) (Lf : ℝ → Matrix n r ℝ),
    ODESolution (kField V₀ F) K t₀ t₁ ∧ K t₀ = U₀ * S₀ ∧ U₁ᵀ * U₁ = 1 ∧ K t₁ = U₁ * Ŝ₁ ∧
    ODESolution (fun t S => -sField U₁ V₀ F t S) S t₀ t₁ ∧ S t₀ = Ŝ₁ ∧
    ODESolution (lField U₁ F) Lf t₀ t₁ ∧ Lf t₀ = V₀ * (S t₁)ᵀ ∧
    V₁ᵀ * V₁ = 1 ∧ Lf t₁ = V₁ * S₁ᵀ

/-- **Structure of the KSL step for a constant field** `F(t, Y) = C`: with `P₁ = U₁ U₁ᵀ`,
`Q₀ = V₀ V₀ᵀ`, one step gives
`Y₁ = U₁ S₁ V₁ᵀ = Y₀ + (t₁ - t₀) (C Q₀ + P₁ C (I - Q₀))`.
This is the computation of Lubich–Oseledets ([LubichOseledets2014, §3.2] and proof of Theorem 4.1),
`Y₁ = Y₀ + ΔA Q₀ + P₁ ΔA (I - Q₀)`, for the increment `ΔA = (t₁ - t₀) C` of a constant field.
The increment is the *ordered* splitting `C Q₀ + P₁ C (I - Q₀)` of the tangent projection, built
with the old basis on the right and the new basis on the left.  Its transpose (for `V₀ = U₀`,
`Cᵀ = ±C`) is `±(P₀ C + (I - P₀) C P₁)`, which uses the new basis on the right; this asymmetry is
the structural reason why the projector-splitting integrator does not preserve (skew-)symmetry
(`ksl_not_symm`, `ksl_not_skew`).  The orthonormality of the QR factors is not needed here. -/
theorem IsKSLStep.eq_const [DecidableEq n] {C : Matrix m n ℝ} {t₀ t₁ : ℝ}
    {U₀ U₁ : Matrix m r ℝ} {S₀ S₁ : Matrix r r ℝ} {V₀ V₁ : Matrix n r ℝ}
    (h : IsKSLStep (fun _ _ => C) t₀ t₁ U₀ S₀ V₀ U₁ S₁ V₁) (ht : t₀ ≤ t₁) :
    U₁ * S₁ * V₁ᵀ = U₀ * S₀ * V₀ᵀ +
      (t₁ - t₀) • (C * (V₀ * V₀ᵀ) + U₁ * U₁ᵀ * C * (1 - V₀ * V₀ᵀ)) := by
  obtain ⟨K, Ŝ₁, S, Lf, hK, hK0, -, hQR, hS, hS0, hLs, hL0, -, hL1⟩ := h
  have hK1 := odeSolution_const_eq (c := C * V₀) hK ht
  have hS1 := odeSolution_const_eq (c := -(U₁ᵀ * C * V₀)) hS ht
  have hLf1 := odeSolution_const_eq (c := Cᵀ * U₁) hLs ht
  have key : U₁ * (Ŝ₁ * V₀ᵀ) = U₀ * (S₀ * V₀ᵀ) + (t₁ - t₀) • (C * (V₀ * V₀ᵀ)) := by
    rw [← Matrix.mul_assoc, ← hQR, hK1, hK0]
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [Matrix.mul_assoc, ← Matrix.transpose_transpose S₁, ← Matrix.transpose_mul, ← hL1, hLf1,
    hL0, hS1, hS0]
  simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_neg, Matrix.mul_add, Matrix.mul_smul,
    Matrix.mul_neg, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, smul_add, key]
  module

/-- Converse construction: for a constant field `F(t, Y) = C`, explicit (affine) substep
solutions give a KSL step as soon as the two factorizations hold. -/
theorem isKSLStep_const {C : Matrix m n ℝ} {t₀ t₁ : ℝ} {U₀ U₁ : Matrix m r ℝ}
    {S₀ Ŝ₁ S₁ : Matrix r r ℝ} {V₀ V₁ : Matrix n r ℝ} (hU₁ : U₁ᵀ * U₁ = 1)
    (hQR : U₀ * S₀ + (t₁ - t₀) • (C * V₀) = U₁ * Ŝ₁) (hV₁ : V₁ᵀ * V₁ = 1)
    (hL : V₀ * (Ŝ₁ + (t₁ - t₀) • -(U₁ᵀ * C * V₀))ᵀ + (t₁ - t₀) • (Cᵀ * U₁) = V₁ * S₁ᵀ) :
    IsKSLStep (fun _ _ => C) t₀ t₁ U₀ S₀ V₀ U₁ S₁ V₁ :=
  ⟨fun t => U₀ * S₀ + (t - t₀) • (C * V₀), Ŝ₁, fun t => Ŝ₁ + (t - t₀) • -(U₁ᵀ * C * V₀),
    fun t => V₀ * (Ŝ₁ + (t₁ - t₀) • -(U₁ᵀ * C * V₀))ᵀ + (t - t₀) • (Cᵀ * U₁),
    odeSolution_affine _ _ _ _, by simp, hU₁, hQR,
    odeSolution_affine Ŝ₁ (-(U₁ᵀ * C * V₀)) _ _, by simp, odeSolution_affine _ _ _ _, by simp, hV₁,
    hL⟩

/-- **The projector-splitting integrator does not preserve symmetry** (remark before Theorem 5
of Ceruti–Lubich, [CerutiLubich2022, §3.5]).  There are a symmetric, constant (hence Lipschitz)
right-hand side satisfying (7) and a symmetric initial value `Y₀ = U₀ S₀ U₀ᵀ` (`U₀ᵀ U₀ = 1`,
`S₀` symmetric, `V₀ = U₀`) for which a KSL step exists, and **every** KSL step (for every choice of
the QR factors and substep solutions) produces a non-symmetric `Y₁ = U₁ S₁ V₁ᵀ`.

Explicitly: `C = [[0, 4], [4, -3]]`, `U₀ = e₁`, `S₀ = 3`, `h = 1`.  By `IsKSLStep.eq_const`,
`Y₁ = Y₀ + C P₀ + P₁ C (I - P₀) = [[3, 0], [4, 0]]`, whereas the exact solution
`Y₀ + C = [[3, 4], [4, -3]]` and the BUG approximation `3 U₁ U₁ᵀ` (`U₁ = (3/5, 4/5)ᵀ`, see the
first example above and `bug_symm`) are symmetric. -/
theorem ksl_not_symm : ∃ (C : Matrix (Fin 2) (Fin 2) ℝ) (U₀ : Matrix (Fin 2) (Fin 1) ℝ)
    (S₀ : Matrix (Fin 1) (Fin 1) ℝ),
    SymmCondition (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => C) ∧
    IsLipschitzField (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => C) 0 ∧
    U₀ᵀ * U₀ = 1 ∧ S₀.IsSymm ∧
    (∃ U₁ S₁ V₁, IsKSLStep (fun _ _ => C) 0 1 U₀ S₀ U₀ U₁ S₁ V₁) ∧
    ∀ U₁ S₁ V₁, IsKSLStep (fun _ _ => C) 0 1 U₀ S₀ U₀ U₁ S₁ V₁ → ¬ (U₁ * S₁ * V₁ᵀ).IsSymm := by
  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin 2) (Fin 2) ℝ, C = !![0, 4; 4, -3] := ⟨_, rfl⟩
  obtain ⟨U₀, hU₀⟩ : ∃ U₀ : Matrix (Fin 2) (Fin 1) ℝ, U₀ = !![1; 0] := ⟨_, rfl⟩
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Matrix (Fin 1) (Fin 1) ℝ, S₀ = !![3] := ⟨_, rfl⟩
  refine ⟨C, U₀, S₀, fun _ _ => ?_, fun _ _ _ => by simp, ?_, ?_,
    ⟨!![3/5; 4/5], !![5], !![1; 0], isKSLStep_const (Ŝ₁ := !![5]) ?_ ?_ ?_ ?_⟩, ?_⟩
  · subst hC
    ext i j; fin_cases i <;> fin_cases j <;> simp
  · subst hU₀
    ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
  · subst hS₀
    ext i j; fin_cases i; fin_cases j; simp
  · ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]; norm_num
  · subst hC hU₀ hS₀
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  · ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
  · subst hC hU₀
    ext i j; fin_cases i <;> fin_cases j <;>
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.mul_apply,
        Matrix.transpose_apply, Fin.sum_univ_two, Fin.sum_univ_one, smul_eq_mul] <;>
      norm_num
  · intro U₁ S₁ V₁ h hsym
    have hY := h.eq_const zero_le_one
    obtain ⟨K, Ŝ₁, -, -, hK, hK0, -, hQR, -⟩ := h
    have hK1 := odeSolution_const_eq (c := C * U₀) hK zero_le_one
    rw [hK0, hQR] at hK1
    have e1 := congrFun (congrFun hK1 0) 0
    have e2 := congrFun (congrFun hK1 1) 0
    have h01 := Matrix.IsSymm.ext_iff.1 hsym 0 1
    rw [hY] at h01
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply,
      Matrix.sub_apply, Fin.sum_univ_two, Fin.sum_univ_one, smul_eq_mul] at e1 e2 h01
    subst hC hU₀ hS₀
    norm_num [Matrix.one_apply] at e1 e2 h01
    have hs : Ŝ₁ 0 0 ^ 2 = 0 := by
      linear_combination (Ŝ₁ 0 0 ^ 2 / 4) * h01 +
        (U₁ 0 0 * Ŝ₁ 0 0 + 3 - 3 / 4 * (U₁ 1 0 * Ŝ₁ 0 0)) * e1 - 9 / 4 * e2
    rw [pow_eq_zero_iff two_ne_zero] at hs
    rw [hs, mul_zero] at e1
    norm_num at e1

/-- **The projector-splitting integrator does not preserve skew-symmetry** (remark before
Theorem 5 of Ceruti–Lubich, [CerutiLubich2022, §3.5]).  There are a skew-symmetric, constant (hence
Lipschitz) right-hand side satisfying (8) and a skew-symmetric initial value `Y₀ = U₀ S₀ U₀ᵀ`
(`U₀ᵀ U₀ = 1`, `S₀ᵀ = -S₀`, `V₀ = U₀`) for which a KSL step exists, and every KSL step produces a
`Y₁ = U₁ S₁ V₁ᵀ` that is not skew-symmetric.

Explicitly: `C = [[0, 1], [-1, 0]]`, `U₀ = e₁`, `S₀ = 0` (rank `r = 1`, where the only
skew-symmetric core is `0`), `h = 1`: `Y₁ = C P₀ + P₁ C (I - P₀) = [[0, 0], [-1, 0]]`, while the BUG
step returns the skew-symmetric `Y₁ = 0` (`bug_skew`).

These data are **degenerate** (`Y₀ = 0`, `S₀` not invertible), i.e. outside the rank-`r`
factorization `Y₀ = U₀ S₀ V₀ᵀ` with invertible `S₀` of the papers; see `ksl_not_skew_rank_two`
for a non-degenerate witness. -/
theorem ksl_not_skew : ∃ (C : Matrix (Fin 2) (Fin 2) ℝ) (U₀ : Matrix (Fin 2) (Fin 1) ℝ)
    (S₀ : Matrix (Fin 1) (Fin 1) ℝ),
    SkewCondition (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => C) ∧
    IsLipschitzField (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => C) 0 ∧
    U₀ᵀ * U₀ = 1 ∧ S₀ᵀ = -S₀ ∧
    (∃ U₁ S₁ V₁, IsKSLStep (fun _ _ => C) 0 1 U₀ S₀ U₀ U₁ S₁ V₁) ∧
    ∀ U₁ S₁ V₁, IsKSLStep (fun _ _ => C) 0 1 U₀ S₀ U₀ U₁ S₁ V₁ →
      (U₁ * S₁ * V₁ᵀ)ᵀ ≠ -(U₁ * S₁ * V₁ᵀ) := by
  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin 2) (Fin 2) ℝ, C = !![0, 1; -1, 0] := ⟨_, rfl⟩
  obtain ⟨U₀, hU₀⟩ : ∃ U₀ : Matrix (Fin 2) (Fin 1) ℝ, U₀ = !![1; 0] := ⟨_, rfl⟩
  refine ⟨C, U₀, 0, fun _ _ => ?_, fun _ _ _ => by simp, ?_, by simp,
    ⟨!![0; -1], !![1], !![1; 0], isKSLStep_const (Ŝ₁ := !![1]) ?_ ?_ ?_ ?_⟩, ?_⟩
  · subst hC
    ext i j; fin_cases i <;> fin_cases j <;> simp
  · subst hU₀
    ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
  · ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
  · subst hC hU₀
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  · ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
  · subst hC hU₀
    ext i j; fin_cases i <;> fin_cases j <;>
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.mul_apply,
        Matrix.transpose_apply, Fin.sum_univ_two, Fin.sum_univ_one, smul_eq_mul] <;>
      norm_num
  · intro U₁ S₁ V₁ h hskew
    have hY := h.eq_const zero_le_one
    obtain ⟨K, Ŝ₁, -, -, hK, hK0, -, hQR, -⟩ := h
    have hK1 := odeSolution_const_eq (c := C * U₀) hK zero_le_one
    rw [hK0, hQR] at hK1
    have e1 := congrFun (congrFun hK1 0) 0
    have e2 := congrFun (congrFun hK1 1) 0
    have h01 := congrFun (congrFun hskew 0) 1
    rw [Matrix.transpose_apply, Matrix.neg_apply, hY] at h01
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply,
      Matrix.sub_apply, Fin.sum_univ_two, Fin.sum_univ_one, smul_eq_mul] at e1 e2 h01
    subst hC hU₀
    norm_num [Matrix.one_apply] at e1 e2 h01
    rcases e1 with hu | hs
    · rw [hu] at h01
      norm_num at h01
    · rw [hs, mul_zero] at e2
      norm_num at e2

/-- **The projector-splitting integrator does not preserve skew-symmetry, non-degenerate
witness** (remark before Theorem 5 of Ceruti–Lubich, [CerutiLubich2022, §3.5]).  `n = 4`, `r = 2`,
`U₀ = [e₁, e₂]`, invertible skew `S₀ = [[0, 4], [-4, 0]]`,
`C = 3 (e₃e₁ᵀ - e₁e₃ᵀ) + 3 (e₄e₂ᵀ - e₂e₄ᵀ)` (condition (8)), `h = 1`.  Then
`K(1) = [[0, 4], [-4, 0], [3, 0], [0, 3]]` has full column rank with `K(1)ᵀ K(1) = 25 I`, so for
every QR factorization `K(1) = U₁ Ŝ₁` the projector is `P₁ = K(1) K(1)ᵀ / 25`; by
`IsKSLStep.eq_const`, `Y₁ + Y₁ᵀ = (27/25) (e₁e₃ᵀ + e₃e₁ᵀ + e₂e₄ᵀ + e₄e₂ᵀ) ≠ 0` for **every** KSL
step.  A KSL step exists (`U₁ = K(1)/5`, and `L(1)` has orthogonal columns of norm `√769/5`). -/
theorem ksl_not_skew_rank_two : ∃ (C : Matrix (Fin 4) (Fin 4) ℝ) (U₀ : Matrix (Fin 4) (Fin 2) ℝ)
    (S₀ : Matrix (Fin 2) (Fin 2) ℝ),
    SkewCondition (fun (_ : ℝ) (_ : Matrix (Fin 4) (Fin 4) ℝ) => C) ∧
    IsLipschitzField (fun (_ : ℝ) (_ : Matrix (Fin 4) (Fin 4) ℝ) => C) 0 ∧
    U₀ᵀ * U₀ = 1 ∧ S₀ᵀ = -S₀ ∧ S₀.det ≠ 0 ∧
    (∃ U₁ S₁ V₁, IsKSLStep (fun _ _ => C) 0 1 U₀ S₀ U₀ U₁ S₁ V₁) ∧
    ∀ U₁ S₁ V₁, IsKSLStep (fun _ _ => C) 0 1 U₀ S₀ U₀ U₁ S₁ V₁ →
      (U₁ * S₁ * V₁ᵀ)ᵀ ≠ -(U₁ * S₁ * V₁ᵀ) := by
  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin 4) (Fin 4) ℝ,
      C = !![0, 0, -3, 0; 0, 0, 0, -3; 3, 0, 0, 0; 0, 3, 0, 0] := ⟨_, rfl⟩
  obtain ⟨U₀, hU₀⟩ : ∃ U₀ : Matrix (Fin 4) (Fin 2) ℝ, U₀ = !![1, 0; 0, 1; 0, 0; 0, 0] :=
    ⟨_, rfl⟩
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Matrix (Fin 2) (Fin 2) ℝ, S₀ = !![0, 4; -4, 0] := ⟨_, rfl⟩
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : Matrix (Fin 4) (Fin 2) ℝ, K₁ = !![0, 4; -4, 0; 3, 0; 0, 3] :=
    ⟨_, rfl⟩
  have hK : U₀ * S₀ + (1 - 0 : ℝ) • (C * U₀) = K₁ := by
    subst hC hU₀ hS₀ hK₁
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
  obtain ⟨L₁, hL₁⟩ : ∃ L₁ : Matrix (Fin 4) (Fin 2) ℝ, L₁ = !![5, 0; 0, 5; 0, -12/5; 12/5, 0] :=
    ⟨_, rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = Real.sqrt (769 / 25) := ⟨_, rfl⟩
  have hμ2 : μ * μ = 769 / 25 := by rw [hμ]; exact Real.mul_self_sqrt (by norm_num)
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    norm_num at hμ2
  refine ⟨C, U₀, S₀, fun _ _ => ?_, fun _ _ _ => by simp, ?_, ?_, ?_,
    ⟨!![0, 4/5; -4/5, 0; 3/5, 0; 0, 3/5], μ • 1, μ⁻¹ • L₁,
      isKSLStep_const (Ŝ₁ := !![5, 0; 0, 5]) ?_ ?_ ?_ ?_⟩, ?_⟩
  · subst hC
    ext i j; fin_cases i <;> fin_cases j <;> simp
  · subst hU₀
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  · subst hS₀
    ext i j; fin_cases i <;> fin_cases j <;> simp
  · subst hS₀
    simp [Matrix.det_fin_two]
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
  · rw [hK, hK₁]
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
  · have hLL : L₁ᵀ * L₁ = (769 / 25 : ℝ) • 1 := by
      subst hL₁
      ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hLL, smul_smul, smul_smul,
      ← hμ2]
    field_simp
    simp
  · rw [Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_one, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
    subst hC hU₀ hL₁
    ext i j; fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
        Matrix.transpose_apply, Matrix.neg_apply,
        Fin.sum_univ_four, Fin.sum_univ_two, smul_eq_mul] <;>
      norm_num
  · intro U₁ S₁ V₁ h hskew
    have hY := h.eq_const zero_le_one
    obtain ⟨K, Ŝ₁, -, -, hKs, hK0, hU₁, hQR, -⟩ := h
    have hK1 := odeSolution_const_eq (c := C * U₀) hKs zero_le_one
    rw [hK0, hQR, hK] at hK1
    have hKK : K₁ᵀ * K₁ = (25 : ℝ) • 1 := by
      subst hK₁
      ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
    have hSS : ((1 / 25 : ℝ) • Ŝ₁ᵀ) * Ŝ₁ = 1 := by
      have : Ŝ₁ᵀ * Ŝ₁ = (25 : ℝ) • 1 := by
        rw [← hKK, ← hK1, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U₁ᵀ, hU₁,
          Matrix.one_mul]
      rw [Matrix.smul_mul, this, smul_smul]
      norm_num
    have hSS' : Ŝ₁ * Ŝ₁ᵀ = (25 : ℝ) • 1 := by
      have := mul_eq_one_comm.1 hSS
      rw [Matrix.mul_smul] at this
      rw [← one_smul ℝ (Ŝ₁ * Ŝ₁ᵀ), ← this, smul_smul]
      norm_num
    have hP : U₁ * U₁ᵀ = (1 / 25 : ℝ) • (K₁ * K₁ᵀ) := by
      rw [← hK1, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Ŝ₁, hSS',
        Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, smul_smul]
      norm_num
    rw [hP] at hY
    have h02 := congrFun (congrFun hskew 0) 2
    rw [Matrix.transpose_apply, Matrix.neg_apply, hY] at h02
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply,
      Matrix.sub_apply, Matrix.one_apply, Fin.sum_univ_four, Fin.sum_univ_two,
      smul_eq_mul] at h02
    subst hC hU₀ hS₀ hK₁
    norm_num at h02

end KSL

end Symmetry

end LeanDLRA
