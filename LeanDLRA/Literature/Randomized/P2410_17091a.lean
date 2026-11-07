import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.Exactness
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Randomized.RandomizedBUG

/-!
# Results of arXiv 2410.17091: Randomized DLRA (DRSVD/DGN)

Formalized here, for the sketch `Ω` of the dynamical range finder, are three results of
Lam–Ceruti–Kressner (arXiv 2410.17091, §2):

* `sketch_exact` (Lemma 2.1, first part): for `Ḃ = F(A(t)) Ω`, `B(0) = A₀ Ω`, one has
  `B(t) = A(t) Ω` when `A' = F(A)`. Stated for matrices with the Frobenius norm.
* `dynamical_rangefinder_exact` and `dynamical_rangefinder_capture` (Lemma 2.1, range part): if
  `A = X Vᵀ` for some `V` (equivalently `rank A ≤ s`, with `s = r + p` as in the paper) and the
  `s × k` matrix `Vᵀ Ω` has a right inverse (full row rank), then `A = A Ω Z` for some `Z`, the
  ranks of `A` and `A Ω` agree, and any range basis capturing `A Ω` captures `A`. The paper's
  almost-sure statement for Gaussian `Ω` is not formalized; only the deterministic core is.
* `bStep_iff_projected` (eq. (7)): with the full-column-rank pseudo-inverse
  `Ω† = (ΩᵀΩ)⁻¹Ωᵀ` (`gramPinv`) and `Π_Ω = Ω Ω†` (`projOmega`), the equation `Ḃ = F(B Ω†) Ω`
  is equivalent to `Ẏ = F(Y) Π_Ω` for `Y = B Ω†`. `projOmega_isOrthProj` records that `Π_Ω` is an
  orthogonal projector (idempotent and symmetric).

Already in the library and not duplicated here (see `LeanDLRA.RandomizedBUG`): the exactness of
DRSVD and DGN (Lemmas 3.2 and 3.3, in the corrected form `rank A(h) ≤ r`: `drsvd_exact_iff`,
`dgn_exact`, with the counterexample `Counterexample.drsvd_not_exact` to the paper's
`rank ≤ r + p`), the augmented sketch, the B-step as a BUG K-step (`bStep_full`, for orthonormal
`W`), and the robust error analysis (`IsDRSVDStep`, `drsvd_global_error`). Not formalized: the
Gaussian almost-sure range statement, the non-augmented error term, and the heuristic
`B(h) ≈ A(h)Ω`.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2410_17091

variable {m n k l s : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype l] [Fintype s]

/-- **Lemma 2.1, exact sketch** (arXiv 2410.17091, Lemma 2.1, first statement).  If `A' = F(t, A)`
on `[t₀, t₁]` and `B' = F(t, A(t)) Ω` with `B(t₀) = A(t₀) Ω`, then `B(t) = A(t) Ω` on `[t₀, t₁]`. -/
theorem sketch_exact {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A : ℝ → Matrix m n ℝ}
    {Ω : Matrix n k ℝ} {B : ℝ → Matrix m k ℝ} {t₀ t₁ : ℝ}
    (hA : ODESolution F A t₀ t₁)
    (hB : ODESolution (fun t _ => F t (A t) * Ω) B t₀ t₁) (hB₀ : B t₀ = A t₀ * Ω) :
    ∀ t ∈ Icc t₀ t₁, B t = A t * Ω := by
  intro t ht
  have h := hB.eq_add_map_sub (Frobenius.rightMulCLM Ω) (A' := fun t => F t (A t)) hA.cont
    (fun t ht' => hA.deriv t ht') (fun _ _ => rfl) t ht
  rw [Frobenius.rightMulCLM_apply] at h
  rw [h, hB₀, Matrix.sub_mul]
  abel

omit [Fintype m] in
/-- **Range part of Lemma 2.1, deterministic core.**  Suppose `A = X Vᵀ` (so `rank A ≤ s`, with
`s = r + p` and `V` a basis of the row space) and `Vᵀ Ω R = 1` for some `R` (full row rank of
`Vᵀ Ω`).  Then `A = A Ω (R Vᵀ)` and `rank (A Ω) = rank A`. -/
theorem dynamical_rangefinder_exact [DecidableEq s] {A : Matrix m n ℝ} {Ω : Matrix n k ℝ}
    {X : Matrix m s ℝ} {V : Matrix n s ℝ} (hA : A = X * Vᵀ) {R : Matrix k s ℝ}
    (hR : Vᵀ * Ω * R = 1) :
    A = A * Ω * (R * Vᵀ) ∧ (A * Ω).rank = A.rank := by
  have hA' : A = A * Ω * (R * Vᵀ) := by
    have e : A * Ω * (R * Vᵀ) = X * (Vᵀ * Ω * R) * Vᵀ := by
      rw [hA]; simp only [Matrix.mul_assoc]
    rw [e, hR, Matrix.mul_one, hA]
  refine ⟨hA', le_antisymm (Matrix.rank_mul_le_left _ _) ?_⟩
  calc A.rank = (A * Ω * (R * Vᵀ)).rank := by rw [← hA']
    _ ≤ (A * Ω).rank := Matrix.rank_mul_le_left _ _

/-- **Range part of Lemma 2.1: capture.**  Under the hypotheses of `dynamical_rangefinder_exact`,
any `Q` with `Q Qᵀ (A Ω) = A Ω` also satisfies `Q Qᵀ A = A`; for orthonormal `Q` this says that the
range of `orth(B(h))` equals the range of `A(h)` (`B(h) = A(h) Ω`). -/
theorem dynamical_rangefinder_capture [DecidableEq s] {A : Matrix m n ℝ} {Ω : Matrix n k ℝ}
    {X : Matrix m s ℝ} {V : Matrix n s ℝ} (hA : A = X * Vᵀ) {R : Matrix k s ℝ}
    (hR : Vᵀ * Ω * R = 1) {Q : Matrix m l ℝ} (hcap : Q * Qᵀ * (A * Ω) = A * Ω) :
    Q * Qᵀ * A = A :=
  RandomizedBUG.capture_of_sketch hcap ⟨R * Vᵀ, (dynamical_rangefinder_exact hA hR).1⟩

example : (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ := by simp

/-! ## The pseudo-inverse projection of eq. (7) -/

section Projection

variable [DecidableEq k]

/-- The full-column-rank pseudo-inverse `Ω† = (ΩᵀΩ)⁻¹ Ωᵀ` of an `n × k` sketch. -/
noncomputable def gramPinv (Ω : Matrix n k ℝ) : Matrix k n ℝ := (Ωᵀ * Ω)⁻¹ * Ωᵀ

/-- The orthogonal projector `Π_Ω = Ω Ω† = Ω (ΩᵀΩ)⁻¹ Ωᵀ` onto `range Ω`. -/
noncomputable def projOmega (Ω : Matrix n k ℝ) : Matrix n n ℝ := Ω * gramPinv Ω

variable {Ω : Matrix n k ℝ}

/-- `Ω† Ω = I` when `ΩᵀΩ` is invertible. -/
lemma gramPinv_mul_self (h : IsUnit (Ωᵀ * Ω).det) : gramPinv Ω * Ω = 1 := by
  unfold gramPinv
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h]

/-- `Ω Ω† Ω = Ω`. -/
lemma projOmega_mul_self (h : IsUnit (Ωᵀ * Ω).det) : projOmega Ω * Ω = Ω := by
  unfold projOmega
  rw [Matrix.mul_assoc, gramPinv_mul_self h, Matrix.mul_one]

/-- `Π_Ω` is an orthogonal projector: idempotent and symmetric. -/
theorem projOmega_isOrthProj (h : IsUnit (Ωᵀ * Ω).det) :
    projOmega Ω * projOmega Ω = projOmega Ω ∧ (projOmega Ω)ᵀ = projOmega Ω := by
  refine ⟨?_, ?_⟩
  · have hc : gramPinv Ω * (Ω * gramPinv Ω) = gramPinv Ω := by
      rw [← Matrix.mul_assoc, gramPinv_mul_self h, Matrix.one_mul]
    unfold projOmega
    rw [Matrix.mul_assoc Ω (gramPinv Ω) (Ω * gramPinv Ω), hc]
  · have hG : ((Ωᵀ * Ω)⁻¹)ᵀ = (Ωᵀ * Ω)⁻¹ := by
      rw [Matrix.transpose_nonsing_inv, Matrix.transpose_mul, Matrix.transpose_transpose]
    unfold projOmega gramPinv
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hG, Matrix.mul_assoc]

/-- **Eq. (7) as a projected trajectory** (arXiv 2410.17091, eq. (7)).  For a sketch `Ω` of full
column rank, `B' = F(B Ω†) Ω` holds if and only if `Y = B Ω†` solves `Y' = F(Y) Π_Ω`, i.e. the
dynamical range finder is a BUG-type K-step with the random projector `Π_Ω`. -/
theorem bStep_iff_projected {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    (h : IsUnit (Ωᵀ * Ω).det) {Bs : ℝ → Matrix m k ℝ} {a b : ℝ} :
    ODESolution (fun t B => F t (B * gramPinv Ω) * Ω) Bs a b ↔
      ODESolution (fun t Y => F t Y * projOmega Ω) (fun t => Bs t * gramPinv Ω) a b := by
  have hG := gramPinv_mul_self h
  constructor
  · intro hB
    refine RandomizedBUG.odeSolution_map hB (Frobenius.rightMulCLM (gramPinv Ω)) ?_
    intro t _
    simp only [Frobenius.rightMulCLM_apply, projOmega, Matrix.mul_assoc]
  · intro hY
    have h2 := RandomizedBUG.odeSolution_map hY (Frobenius.rightMulCLM Ω)
      (g := fun t B => F t (B * gramPinv Ω) * Ω) ?_
    · convert h2 using 1
      funext t
      simp only [Frobenius.rightMulCLM_apply, Matrix.mul_assoc, hG, Matrix.mul_one]
    · intro t _
      simp only [Frobenius.rightMulCLM_apply, projOmega, Matrix.mul_assoc, hG, Matrix.mul_one]

end Projection

end LeanDLRA.Literature.P2410_17091
