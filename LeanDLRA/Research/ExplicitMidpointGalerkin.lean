import LeanDLRA.HighOrder.MidpointBUG
import LeanDLRA.Integrators.Matrix.BUG
import LeanDLRA.Research.AugmentationRank
import LeanDLRA.Research.ExplicitMidpointCapture

/-!
# The explicit midpoint Galerkin step in augmented bases

A step from the factored point `Y₀ = U₀ S₀ V₀ᵀ` with step size `h`:

* explicit predictor `Z = Y₀ + (h/2) P₀ F(t₀, Y₀)` with the tangent projector
  `P₀ = tangentProj U₀ V₀`; no differential equation is solved for it;
* one evaluation `G = F(t₀ + h/2, Z)`;
* augmented bases `Ua`, `Va` with orthonormal columns whose ranges contain those of
  `(U₀, G V₀)` and `(V₀, Gᵀ U₀)`;
* either the Galerkin flow of `galerkinProj Ua Va` on the whole step, started at `Y₀`, or the
  explicit update `Y₁ = Y₀ + h • galerkinProj Ua Va G`.

The two capture defects

`θ = ‖(1 - Ua Uaᵀ) G (1 - V₀ V₀ᵀ)‖`, `θ' = ‖(1 - U₀ U₀ᵀ) G (1 - Va Vaᵀ)‖`

are parameters of the statements of this file, with one exception: for the explicit update,
`norm_update_sub_le_cube_add` bounds both by `C₁ h² + C₂ ε`
(`LeanDLRA.norm_capture_defect_le_sq_add` of `LeanDLRA.Research.ExplicitMidpointCapture`) and
obtains a local error `O(h³ + h ε)`. The Galerkin step (`galerkin_local_error`) is not combined
with those bounds here, and no global error bound for a run of steps is stated.

## Main statements

* `LeanDLRA.ODESolution.norm_midpoint_defect_le`: the midpoint-rule defect
  `‖A(t₀ + h) - A t₀ - h F(t₀ + h/2, A(t₀ + h/2))‖ ≤ M₃ h³/24` of an exact solution of class
  `C³`, with the sharp constant of `LeanDLRA.MidpointBUG.midpoint_defect_le_sharp`.
* `LeanDLRA.ODESolution.norm_half_step_sub_le`: the Taylor bound
  `‖A(t₀ + h/2) - A t₀ - (h/2) F(t₀, A t₀)‖ ≤ M₂ h²/8` of an exact solution of class `C²`.
* `LeanDLRA.ExplicitMidpoint.sub_galerkin_eq_of_capture`: the part of `G` outside the
  Galerkin space is the sum of two terms, one for each capture defect.
* `LeanDLRA.ExplicitMidpoint.norm_one_sub_galerkinProj_le_of_capture`:
  `‖(1 - galerkinProj Ua Va) G‖ ≤ θ + θ'`.
* `LeanDLRA.ExplicitMidpoint.norm_predictor_sub_le`: the predictor error
  `‖Z - A(t₀ + h/2)‖ ≤ M₂ h²/8 + (h/2) ε` under the factored normal bound at `Y₀`.
* `LeanDLRA.ExplicitMidpoint.galerkin_local_error`: the local error of the Galerkin step, an
  instance of `LeanDLRA.MidpointBUG.midpointGalerkin_local_error`.
* `LeanDLRA.ExplicitMidpoint.norm_update_sub_le`: the local error
  `h (θ + θ') + L h² ε/2 + h³ (M₃/24 + L M₂/8)` of the explicit update.
* `LeanDLRA.ExplicitMidpoint.norm_update_sub_le_cube_add`: with the capture defects bounded, the
  local error `h³ (2 C₁ + M₃/24 + L M₂/8) + h ε (2 C₂ + L h/2)` of the explicit update.

## Implementation notes

The bounds `M₂`, `M₃` are bounds of the iterated derivatives of the exact solution within the
step interval, as in `LeanDLRA.MidpointBUG.midpointGalerkin_local_error`. The Galerkin step
inherits the global hypotheses of that theorem (`IsLipschitzField`, `IsBoundedField`, a
time-Lipschitz field); the explicit update needs the Lipschitz bound only on a region `D` that
contains the predictor and the exact solution at the midpoint.

## References

* [CerutiEtAl2024b] G. Ceruti, L. Einkemmer, J. Kusch, Ch. Lubich, *A robust second-order
  low-rank BUG integrator based on the midpoint rule*.
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

/-! ### Two quadrature facts about exact solutions -/

section Solution

variable {E : Type*} [NormedAddCommGroup E]

/-- A derivative within `[a, b]` of a solution of `y' = F(t, y)` is the field along the solution
at every `t ∈ [a, b)`. -/
theorem ODESolution.eq_field_of_hasDerivWithinAt [NormedSpace ℝ E] {F : ℝ → E → E}
    {A a₁ : ℝ → E} {a b : ℝ} (hA : ODESolution F A a b)
    (ha₁ : ∀ x ∈ Icc a b, HasDerivWithinAt A (a₁ x) (Icc a b) x) :
    ∀ t ∈ Ico a b, a₁ t = F t (A t) := fun t ht =>
  (uniqueDiffOn_Icc ht.2 t ⟨le_rfl, ht.2.le⟩).eq_deriv _
    ((ha₁ t (Ico_subset_Icc_self ht)).mono (Icc_subset_Icc_left ht.1))
    ((hA.deriv t ht).mono Icc_subset_Ici_self)

/-- **Midpoint-rule defect of an exact solution.** If the solution `A` of `y' = F(t, y)` is of
class `C³` on `[t₀, t₀ + h]`, `h > 0`, with third derivative bounded by `M₃`, then
`‖A(t₀ + h) - A t₀ - h F(t₀ + h/2, A(t₀ + h/2))‖ ≤ M₃ h³/24`. -/
theorem ODESolution.norm_midpoint_defect_le [InnerProductSpace ℝ E] {F : ℝ → E → E}
    {A : ℝ → E} {t₀ h M₃ : ℝ} (hh : 0 < h) (hA : ODESolution F A t₀ (t₀ + h))
    (hA3 : ContDiffOn ℝ 3 A (Icc t₀ (t₀ + h)))
    (hM₃ : ∀ t ∈ Icc t₀ (t₀ + h), ‖iteratedDerivWithin 3 A (Icc t₀ (t₀ + h)) t‖ ≤ M₃) :
    ‖A (t₀ + h) - A t₀ - h • F (t₀ + h / 2) (A (t₀ + h / 2))‖ ≤ M₃ * h ^ 3 / 24 := by
  obtain ⟨hc, hw, hd⟩ := MidpointBUG.contDiffOn_three_data hh hA3
  have hm : t₀ + h / 2 ∈ Ico t₀ (t₀ + h) := ⟨by linarith, by linarith⟩
  have h1 := hA.eq_field_of_hasDerivWithinAt (a₁ := iteratedDerivWithin 1 A (Icc t₀ (t₀ + h)))
    (fun x hx => by
      have := hw 0 (by norm_num) x hx
      rwa [iteratedDerivWithin_zero] at this) _ hm
  have := MidpointBUG.midpoint_defect_le_sharp (A := A) hh hA.cont (hc 1 (by norm_num))
    (hc 2 (by norm_num))
    (fun x hx => by simpa [iteratedDerivWithin_zero] using hd 0 (by norm_num) x hx)
    (hd 1 (by norm_num)) (hd 2 (by norm_num)) (fun x hx => hM₃ x (Ioo_subset_Icc_self hx))
  rwa [h1] at this

/-- **Taylor bound of an exact solution at the half step.** If the solution `A` of
`y' = F(t, y)` is of class `C²` on `[t₀, t₀ + h]`, `h > 0`, with second derivative bounded by
`M₂`, then `‖A(t₀ + h/2) - A t₀ - (h/2) F(t₀, A t₀)‖ ≤ M₂ h²/8`. -/
theorem ODESolution.norm_half_step_sub_le [InnerProductSpace ℝ E] {F : ℝ → E → E}
    {A : ℝ → E} {t₀ h M₂ : ℝ} (hh : 0 < h) (hA : ODESolution F A t₀ (t₀ + h))
    (hA2 : ContDiffOn ℝ 2 A (Icc t₀ (t₀ + h)))
    (hM₂ : ∀ t ∈ Icc t₀ (t₀ + h), ‖iteratedDerivWithin 2 A (Icc t₀ (t₀ + h)) t‖ ≤ M₂) :
    ‖A (t₀ + h / 2) - A t₀ - (h / 2) • F t₀ (A t₀)‖ ≤ M₂ * h ^ 2 / 8 := by
  have hab : t₀ < t₀ + h := by linarith
  obtain ⟨hc, hdiff⟩ :=
    (contDiffOn_nat_iff_continuousOn_differentiableOn_deriv (uniqueDiffOn_Icc hab)).1 hA2
  have hw : ∀ k < 2, ∀ x ∈ Icc t₀ (t₀ + h),
      HasDerivWithinAt (iteratedDerivWithin k A (Icc t₀ (t₀ + h)))
        (iteratedDerivWithin (k + 1) A (Icc t₀ (t₀ + h)) x) (Icc t₀ (t₀ + h)) x := by
    intro k hk x hx
    rw [iteratedDerivWithin_succ]
    exact ((hdiff k hk) x hx).hasDerivWithinAt
  have hr : ∀ k < 2, ∀ x ∈ Ico t₀ (t₀ + h),
      HasDerivWithinAt (iteratedDerivWithin k A (Icc t₀ (t₀ + h)))
        (iteratedDerivWithin (k + 1) A (Icc t₀ (t₀ + h)) x) (Ici x) x := fun k hk x hx =>
    (hw k hk x (Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hx)
  have h1 := hA.eq_field_of_hasDerivWithinAt (a₁ := iteratedDerivWithin 1 A (Icc t₀ (t₀ + h)))
    (fun x hx => by
      have := hw 0 (by norm_num) x hx
      rwa [iteratedDerivWithin_zero] at this) t₀ ⟨le_rfl, hab⟩
  have T := MidpointBUG.norm_taylor_one_le (g := A)
    (g₁ := iteratedDerivWithin 1 A (Icc t₀ (t₀ + h)))
    (g₂ := iteratedDerivWithin 2 A (Icc t₀ (t₀ + h))) (a := t₀) (b := t₀ + h) (M := M₂) hA.cont
    (fun s hs => by
      have := hr 0 (by norm_num) s hs
      rwa [iteratedDerivWithin_zero] at this)
    (hc 1 (by norm_num)) (fun s hs => hr 1 (by norm_num) s hs)
    (fun s hs => hM₂ s (Ico_subset_Icc_self hs)) (t₀ + h / 2) ⟨by linarith, by linarith⟩
  rw [h1, add_sub_cancel_left] at T
  calc _ ≤ M₂ * (h / 2) ^ 2 / 2 := T
    _ = M₂ * h ^ 2 / 8 := by ring

end Solution

namespace ExplicitMidpoint

variable {m n k k' : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype k'] [DecidableEq m]
  [DecidableEq n] {r : ℕ} {U₀ : Matrix m (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
  {Ua : Matrix m k ℝ} {Va : Matrix n k' ℝ} {G : Matrix m n ℝ}

/-! ### The part of the field outside the Galerkin space -/

/-- **Splitting of the Galerkin defect.** If the range of `Ua` contains the columns of `G V₀`
and the range of `Va` contains the columns of `Gᵀ U₀`, then
`G - Ua Uaᵀ G Va Vaᵀ = (1 - Ua Uaᵀ) G (1 - V₀ V₀ᵀ) + Ua Uaᵀ (1 - U₀ U₀ᵀ) G (1 - Va Vaᵀ)`. -/
theorem sub_galerkin_eq_of_capture (kCap : Ua * Uaᵀ * (G * V₀) = G * V₀)
    (lCap : Va * Vaᵀ * (Gᵀ * U₀) = Gᵀ * U₀) :
    G - Ua * Uaᵀ * G * (Va * Vaᵀ) =
      (1 - Ua * Uaᵀ) * G * (1 - V₀ * V₀ᵀ) +
        Ua * Uaᵀ * ((1 - U₀ * U₀ᵀ) * G * (1 - Va * Vaᵀ)) := by
  have h₁ : (1 - Ua * Uaᵀ) * G * (V₀ * V₀ᵀ) = 0 := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc (1 - Ua * Uaᵀ) G V₀, Matrix.sub_mul,
      Matrix.one_mul, kCap, sub_self, Matrix.zero_mul]
  have hL : U₀ᵀ * G * (Va * Vaᵀ) = U₀ᵀ * G := by
    have h := congrArg Matrix.transpose lCap
    rwa [Matrix.transpose_mul (Va * Vaᵀ) (Gᵀ * U₀), Matrix.transpose_mul Gᵀ U₀,
      Matrix.transpose_transpose, Matrix.transpose_mul Va Vaᵀ,
      Matrix.transpose_transpose] at h
  have h₂ : U₀ᵀ * G * (1 - Va * Vaᵀ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hL, sub_self]
  have hA : (1 - Ua * Uaᵀ) * G * (1 - V₀ * V₀ᵀ) = (1 - Ua * Uaᵀ) * G := by
    rw [Matrix.mul_sub, Matrix.mul_one, h₁, sub_zero]
  have hB : (1 - U₀ * U₀ᵀ) * G * (1 - Va * Vaᵀ) = G * (1 - Va * Vaᵀ) := by
    rw [Matrix.sub_mul 1, Matrix.one_mul, Matrix.sub_mul G, Matrix.mul_assoc U₀,
      Matrix.mul_assoc U₀, h₂, Matrix.mul_zero, sub_zero]
  rw [hA, hB, Matrix.sub_mul 1, Matrix.one_mul, Matrix.mul_sub G, Matrix.mul_one,
    Matrix.mul_sub (Ua * Uaᵀ), ← Matrix.mul_assoc (Ua * Uaᵀ) G]
  abel

/-- **Capture of the field by the augmented bases.** With the two capture defects bounded by
`θ` and `θ'`, the field value `G` is `θ + θ'` away from the Galerkin space of `Ua`, `Va`. -/
theorem norm_one_sub_galerkinProj_le_of_capture [DecidableEq k] (hUa : Uaᵀ * Ua = 1)
    (kCap : Ua * Uaᵀ * (G * V₀) = G * V₀) (lCap : Va * Vaᵀ * (Gᵀ * U₀) = Gᵀ * U₀) {θ θ' : ℝ}
    (hθ : ‖(1 - Ua * Uaᵀ) * G * (1 - V₀ * V₀ᵀ)‖ ≤ θ)
    (hθ' : ‖(1 - U₀ * U₀ᵀ) * G * (1 - Va * Vaᵀ)‖ ≤ θ') :
    ‖(1 - galerkinProj Ua Va) G‖ ≤ θ + θ' := by
  have h : (1 - galerkinProj Ua Va) G = (1 - Ua * Uaᵀ) * G * (1 - V₀ * V₀ᵀ) +
      Ua * Uaᵀ * ((1 - U₀ * U₀ᵀ) * G * (1 - Va * Vaᵀ)) := by
    change G - galerkinProj Ua Va G = _
    rw [galerkinProj_apply]
    exact sub_galerkin_eq_of_capture kCap lCap
  rw [h]
  refine (norm_add_le _ _).trans (add_le_add hθ ?_)
  rw [← leftProj_apply Ua]
  exact ((isOrthProj_leftProj hUa).norm_le _).trans hθ'

/-! ### The predictor -/

/-- **Error of the explicit predictor.** Let `A` solve `y' = F(t, y)` from `A t₀ = U₀ S₀ V₀ᵀ`,
of class `C²` on `[t₀, t₀ + h]` with second derivative bounded by `M₂`, and let the normal
component of `F` be at most `ε` at the factored point `(U₀, S₀, V₀)`. Then the predictor
`Z = Y₀ + (h/2) P₀ F(t₀, Y₀)`, `P₀ = tangentProj U₀ V₀`, satisfies
`‖Z - A(t₀ + h/2)‖ ≤ M₂ h²/8 + (h/2) ε`. -/
theorem norm_predictor_sub_le {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {D : Set (ℝ × Matrix m n ℝ)} {ε M₂ : ℝ} (hN : FactoredNormalBoundOn F r D ε)
    {S₀ : Matrix (Fin r) (Fin r) ℝ} (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) {t₀ h : ℝ}
    (hh : 0 < h) (hD₀ : (t₀, U₀ * S₀ * V₀ᵀ) ∈ D) {A : ℝ → Matrix m n ℝ}
    (hA : ODESolution F A t₀ (t₀ + h)) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ)
    (hA2 : ContDiffOn ℝ 2 A (Icc t₀ (t₀ + h)))
    (hM₂ : ∀ t ∈ Icc t₀ (t₀ + h), ‖iteratedDerivWithin 2 A (Icc t₀ (t₀ + h)) t‖ ≤ M₂)
    {Z : Matrix m n ℝ}
    (hZ : Z = U₀ * S₀ * V₀ᵀ + (h / 2) • tangentProj U₀ V₀ (F t₀ (U₀ * S₀ * V₀ᵀ))) :
    ‖Z - A (t₀ + h / 2)‖ ≤ M₂ * h ^ 2 / 8 + h / 2 * ε := by
  have hT := hA.norm_half_step_sub_le hh hA2 hM₂
  rw [hA₀] at hT
  have hnorm := hN t₀ U₀ V₀ S₀ hU₀ hV₀ hD₀
  have hsplit := eq_sub_of_add_eq' (tangentProj_add_normal U₀ V₀ (F t₀ (U₀ * S₀ * V₀ᵀ)))
  have e : Z - A (t₀ + h / 2) =
      -(A (t₀ + h / 2) - U₀ * S₀ * V₀ᵀ - (h / 2) • F t₀ (U₀ * S₀ * V₀ᵀ)) -
        (h / 2) • ((1 - U₀ * U₀ᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)) := by
    rw [hZ, hsplit]
    module
  rw [e]
  calc _ ≤ ‖-(A (t₀ + h / 2) - U₀ * S₀ * V₀ᵀ - (h / 2) • F t₀ (U₀ * S₀ * V₀ᵀ))‖ +
        ‖(h / 2) • ((1 - U₀ * U₀ᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ) * (1 - V₀ * V₀ᵀ))‖ :=
        norm_sub_le _ _
    _ ≤ M₂ * h ^ 2 / 8 + h / 2 * ε := by
        rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < h / 2)]
        exact add_le_add hT (mul_le_mul_of_nonneg_left hnorm (by linarith))

/-! ### The local errors -/

/-- **Local error of the Galerkin step in the augmented bases** (the robust midpoint Galerkin
step of [CerutiEtAl2024b], Theorem 1, with the explicit predictor in place of a half step). Let
`Ua`, `Va` contain `U₀`, `V₀` and capture `G V₀`, `Gᵀ U₀` for `G = F(t₀ + h/2, Z)`, with capture
defects at most `θ`, `θ'`, and let `YS` solve the Galerkin equation `Y' = galerkinProj Ua Va F`
from `Y₀`. With `η = M₂ h²/8 + (h/2) ε` the local error is at most
`(e^{L h} - 1) h ((L B + Lₜ) h/2 + L η + θ + θ') + h (L η + θ + θ') + M₃ h³/24`. -/
theorem galerkin_local_error [DecidableEq k] [DecidableEq k']
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {D : Set (ℝ × Matrix m n ℝ)}
    {L Lₜ B ε M₂ M₃ θ θ' : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hFt : ∀ s t x, ‖F s x - F t x‖ ≤ Lₜ * |s - t|)
    (hN : FactoredNormalBoundOn F r D ε) {S₀ : Matrix (Fin r) (Fin r) ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) {t₀ h : ℝ} (hh : 0 < h)
    (hD₀ : (t₀, U₀ * S₀ * V₀ᵀ) ∈ D) {A : ℝ → Matrix m n ℝ} (hA : ODESolution F A t₀ (t₀ + h))
    (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) (hA3 : ContDiffOn ℝ 3 A (Icc t₀ (t₀ + h)))
    (hM₂ : ∀ t ∈ Icc t₀ (t₀ + h), ‖iteratedDerivWithin 2 A (Icc t₀ (t₀ + h)) t‖ ≤ M₂)
    (hM₃ : ∀ t ∈ Icc t₀ (t₀ + h), ‖iteratedDerivWithin 3 A (Icc t₀ (t₀ + h)) t‖ ≤ M₃)
    {Z : Matrix m n ℝ}
    (hZ : Z = U₀ * S₀ * V₀ᵀ + (h / 2) • tangentProj U₀ V₀ (F t₀ (U₀ * S₀ * V₀ᵀ)))
    (hG : G = F (t₀ + h / 2) Z) (hUa : Uaᵀ * Ua = 1) (hVa : Vaᵀ * Va = 1)
    (augU : Ua * Uaᵀ * U₀ = U₀) (augV : Va * Vaᵀ * V₀ = V₀)
    (kCap : Ua * Uaᵀ * (G * V₀) = G * V₀) (lCap : Va * Vaᵀ * (Gᵀ * U₀) = Gᵀ * U₀)
    (hθ : ‖(1 - Ua * Uaᵀ) * G * (1 - V₀ * V₀ᵀ)‖ ≤ θ)
    (hθ' : ‖(1 - U₀ * U₀ᵀ) * G * (1 - Va * Vaᵀ)‖ ≤ θ') {YS : ℝ → Matrix m n ℝ}
    (hS : ODESolution (fun t X => galerkinProj Ua Va (F t X)) YS t₀ (t₀ + h))
    (hS₀ : YS t₀ = U₀ * S₀ * V₀ᵀ) :
    ‖YS (t₀ + h) - A (t₀ + h)‖ ≤
      (Real.exp (L * h) - 1) *
          (h * ((L * B + Lₜ) * h / 2 + L * (M₂ * h ^ 2 / 8 + h / 2 * ε) + (θ + θ'))) +
        (h * (L * (M₂ * h ^ 2 / 8 + h / 2 * ε) + (θ + θ')) + M₃ * h ^ 3 / 24) := by
  have hV : V₀ᵀ * (Va * Vaᵀ) = V₀ᵀ := by
    have h := congrArg Matrix.transpose augV
    rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at h
  have hfix : galerkinProj Ua Va (A t₀) = A t₀ := by
    rw [hA₀, galerkinProj_apply]
    calc Ua * Uaᵀ * (U₀ * S₀ * V₀ᵀ) * (Va * Vaᵀ)
        = Ua * Uaᵀ * U₀ * S₀ * (V₀ᵀ * (Va * Vaᵀ)) := by simp only [Matrix.mul_assoc]
      _ = U₀ * S₀ * V₀ᵀ := by rw [augU, hV]
  have hYh := norm_predictor_sub_le hN hU₀ hV₀ hh hD₀ hA hA₀ (hA3.of_le (by norm_num)) hM₂ hZ
  have hnormal : ‖(1 - galerkinProj Ua Va) (F (t₀ + h / 2) Z)‖ ≤ θ + θ' := by
    rw [← hG]
    exact norm_one_sub_galerkinProj_le_of_capture hUa kCap lCap hθ hθ'
  exact MidpointBUG.midpointGalerkin_local_error (isOrthProj_galerkinProj hUa hVa) hF hL hB hFt
    rfl hh.le hA hA3 hM₃ hfix hYh hnormal hS (hS₀.trans hA₀.symm)

/-- **Local error of the explicit update** `Y₁ = Y₀ + h • galerkinProj Ua Va G`, two
evaluations of `F` and no differential equation. Under the hypotheses on the predictor and the
capture defects of `galerkin_local_error`, with `F` Lipschitz with constant `L` on a region `D`
that contains `(t₀, Y₀)`, `(t₀ + h/2, Z)` and `(t₀ + h/2, A(t₀ + h/2))`,
`‖Y₁ - A(t₀ + h)‖ ≤ h (θ + θ') + L h² ε/2 + h³ (M₃/24 + L M₂/8)`. -/
theorem norm_update_sub_le [DecidableEq k] {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {D : Set (ℝ × Matrix m n ℝ)} {L ε M₂ M₃ θ θ' : ℝ} (hF : IsLipschitzFieldOn F D L)
    (hL : 0 ≤ L) (hN : FactoredNormalBoundOn F r D ε) {S₀ : Matrix (Fin r) (Fin r) ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) {t₀ h : ℝ} (hh : 0 < h)
    (hD₀ : (t₀, U₀ * S₀ * V₀ᵀ) ∈ D) {A : ℝ → Matrix m n ℝ} (hA : ODESolution F A t₀ (t₀ + h))
    (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) (hA3 : ContDiffOn ℝ 3 A (Icc t₀ (t₀ + h)))
    (hM₂ : ∀ t ∈ Icc t₀ (t₀ + h), ‖iteratedDerivWithin 2 A (Icc t₀ (t₀ + h)) t‖ ≤ M₂)
    (hM₃ : ∀ t ∈ Icc t₀ (t₀ + h), ‖iteratedDerivWithin 3 A (Icc t₀ (t₀ + h)) t‖ ≤ M₃)
    {Z : Matrix m n ℝ}
    (hZ : Z = U₀ * S₀ * V₀ᵀ + (h / 2) • tangentProj U₀ V₀ (F t₀ (U₀ * S₀ * V₀ᵀ)))
    (hDZ : (t₀ + h / 2, Z) ∈ D) (hDA : (t₀ + h / 2, A (t₀ + h / 2)) ∈ D)
    (hG : G = F (t₀ + h / 2) Z) (hUa : Uaᵀ * Ua = 1)
    (kCap : Ua * Uaᵀ * (G * V₀) = G * V₀) (lCap : Va * Vaᵀ * (Gᵀ * U₀) = Gᵀ * U₀)
    (hθ : ‖(1 - Ua * Uaᵀ) * G * (1 - V₀ * V₀ᵀ)‖ ≤ θ)
    (hθ' : ‖(1 - U₀ * U₀ᵀ) * G * (1 - Va * Vaᵀ)‖ ≤ θ') :
    ‖U₀ * S₀ * V₀ᵀ + h • galerkinProj Ua Va G - A (t₀ + h)‖ ≤
      h * (θ + θ') + L * h ^ 2 * ε / 2 + h ^ 3 * (M₃ / 24 + L * M₂ / 8) := by
  set Am := A (t₀ + h / 2)
  have hq := hA.norm_midpoint_defect_le hh hA3 hM₃
  have hYh := norm_predictor_sub_le hN hU₀ hV₀ hh hD₀ hA hA₀ (hA3.of_le (by norm_num)) hM₂ hZ
  have hLip : ‖G - F (t₀ + h / 2) Am‖ ≤ L * ‖Z - Am‖ := hG ▸ hF hDZ hDA
  have hcap : ‖G - galerkinProj Ua Va G‖ ≤ θ + θ' :=
    norm_one_sub_galerkinProj_le_of_capture hUa kCap lCap hθ hθ'
  have e : U₀ * S₀ * V₀ᵀ + h • galerkinProj Ua Va G - A (t₀ + h) =
      -(A (t₀ + h) - A t₀ - h • F (t₀ + h / 2) Am) + h • (G - F (t₀ + h / 2) Am) -
        h • (G - galerkinProj Ua Va G) := by
    rw [hA₀]
    module
  rw [e]
  have hh' : ‖h‖ = h := by rw [Real.norm_eq_abs, abs_of_pos hh]
  calc _ ≤ ‖-(A (t₀ + h) - A t₀ - h • F (t₀ + h / 2) Am)‖ + ‖h • (G - F (t₀ + h / 2) Am)‖ +
        ‖h • (G - galerkinProj Ua Va G)‖ := norm_sub_le_of_le (norm_add_le _ _) le_rfl
    _ ≤ M₃ * h ^ 3 / 24 + h * (L * (M₂ * h ^ 2 / 8 + h / 2 * ε)) + h * (θ + θ') := by
        rw [norm_neg, norm_smul, norm_smul, hh']
        refine add_le_add (add_le_add hq (mul_le_mul_of_nonneg_left ?_ hh.le))
          (mul_le_mul_of_nonneg_left hcap hh.le)
        exact hLip.trans (mul_le_mul_of_nonneg_left hYh hL)
    _ = _ := by ring

/-- **Local error of order `h³ + h ε` of the explicit update** `Y₁ = Y₀ + h • galerkinProj Ua Va G`:
`norm_update_sub_le` with the two capture defects bounded by `norm_capture_defect_le_sq_add` and
`norm_capture_defect_right_le_sq_add`. Let `F` satisfy, on a region `D` that contains
`[t₀, t₀ + h] × closedBall (U₀ S₀ V₀ᵀ) ρ` and the point `(t₀ + h/2, A(t₀ + h/2))` of the exact
solution, the factored normal bound with defect `ε`, a Lipschitz bound `L`, a bound `B` and a
Lipschitz bound `Lₜ` in time; let `r` be smaller than both dimensions, `0 < h ≤ H`, and let
`κ`, `D₁`, `D₂` and the side condition be as in `norm_capture_defect_le_sq_add`. Then

`‖Y₁ - A(t₀ + h)‖ ≤ h³ (2 C₁ + M₃/24 + L M₂/8) + h ε (2 C₂ + L h/2)`

with the constants `C₁`, `C₂` of `norm_capture_defect_le_sq_add`, which contain `‖S₀‖` but no
inverse of `S₀`. A global error bound for a run of such steps is not stated. -/
theorem norm_update_sub_le_cube_add [DecidableEq k] [DecidableEq k']
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {D : Set (ℝ × Matrix m n ℝ)}
    {ε L Lₜ B ρ H κ D₁ D₂ M₂ M₃ : ℝ}
    (hN : FactoredNormalBoundOn F r D ε) (hL : IsLipschitzFieldOn F D L) (hL0 : 0 ≤ L)
    (hB : IsBoundedFieldOn F D B)
    (hFt : ∀ s t X, (s, X) ∈ D → (t, X) ∈ D → ‖F s X - F t X‖ ≤ Lₜ * |s - t|)
    (hrm : r < Fintype.card m) (hrn : r < Fintype.card n) {S₀ : Matrix (Fin r) (Fin r) ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) {t₀ h : ℝ} (hh : 0 < h) (hH : h ≤ H) (hρ : 0 < ρ)
    (hD : ∀ t ∈ Icc t₀ (t₀ + h), ∀ X, ‖X - U₀ * S₀ * V₀ᵀ‖ ≤ ρ → (t, X) ∈ D)
    (hκ : Real.sqrt r * (1 / 2 + max L (2 * B / ρ)) ≤ κ)
    (hD₁ : Real.sqrt r * H * max L (2 * B / ρ) / 2 + (2 * κ * B + κ ^ 2 * ‖S₀‖) / 4 +
      H * κ ^ 2 * B / 8 ≤ D₁)
    (hD₂ : Real.sqrt r * H * (1 + max L (2 * B / ρ) / 2) ≤ D₂)
    (hsmall : h / 2 * B + (D₁ * h ^ 2 + D₂ * ε) ≤ ρ / 2) {A : ℝ → Matrix m n ℝ}
    (hA : ODESolution F A t₀ (t₀ + h)) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ)
    (hA3 : ContDiffOn ℝ 3 A (Icc t₀ (t₀ + h)))
    (hM₂ : ∀ t ∈ Icc t₀ (t₀ + h), ‖iteratedDerivWithin 2 A (Icc t₀ (t₀ + h)) t‖ ≤ M₂)
    (hM₃ : ∀ t ∈ Icc t₀ (t₀ + h), ‖iteratedDerivWithin 3 A (Icc t₀ (t₀ + h)) t‖ ≤ M₃)
    (hDA : (t₀ + h / 2, A (t₀ + h / 2)) ∈ D) {Z : Matrix m n ℝ}
    (hZ : Z = U₀ * S₀ * V₀ᵀ + (h / 2) • tangentProj U₀ V₀ (F t₀ (U₀ * S₀ * V₀ᵀ)))
    (hG : G = F (t₀ + h / 2) Z) (hUa : Uaᵀ * Ua = 1) (hVa : Vaᵀ * Va = 1)
    (augU : Ua * Uaᵀ * U₀ = U₀) (augV : Va * Vaᵀ * V₀ = V₀)
    (kCap : Ua * Uaᵀ * (G * V₀) = G * V₀) (lCap : Va * Vaᵀ * (Gᵀ * U₀) = Gᵀ * U₀) :
    ‖U₀ * S₀ * V₀ᵀ + h • galerkinProj Ua Va G - A (t₀ + h)‖ ≤
      h ^ 3 * (2 * ((L + κ + H / 2 * L * κ) * D₁ + Real.sqrt r * max L (2 * B / ρ) / 2 +
          κ * (L * B + Lₜ + B * κ) / 4) + M₃ / 24 + L * M₂ / 8) +
        h * ε * (2 * ((L + κ + H / 2 * L * κ) * D₂ + 1 +
          Real.sqrt r * (1 + max L (2 * B / ρ) / 2)) + L * h / 2) := by
  have hY₀D : (t₀, U₀ * S₀ * V₀ᵀ) ∈ D :=
    hD t₀ ⟨le_rfl, by linarith⟩ _ (by rw [sub_self, norm_zero]; exact hρ.le)
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hN t₀ U₀ V₀ S₀ hU₀ hV₀ hY₀D)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB hY₀D)
  have hH0 : 0 ≤ H := hh.le.trans hH
  have hLm0 : 0 ≤ max L (2 * B / ρ) := hL0.trans (le_max_left _ _)
  have hq0 : 0 ≤ Real.sqrt r := Real.sqrt_nonneg _
  have hκ0 : 0 ≤ κ := le_trans (mul_nonneg hq0 (by linarith)) hκ
  have hD₁0 : 0 ≤ D₁ := le_trans (add_nonneg (add_nonneg
    (div_nonneg (mul_nonneg (mul_nonneg hq0 hH0) hLm0) two_pos.le)
    (div_nonneg (add_nonneg (mul_nonneg (mul_nonneg two_pos.le hκ0) hB0)
      (mul_nonneg (sq_nonneg κ) (norm_nonneg _))) (by norm_num)))
    (div_nonneg (mul_nonneg (mul_nonneg hH0 (sq_nonneg κ)) hB0) (by norm_num))) hD₁
  have hD₂0 : 0 ≤ D₂ := le_trans (mul_nonneg (mul_nonneg hq0 hH0) (by linarith)) hD₂
  have hZY : ‖Z - U₀ * S₀ * V₀ᵀ‖ ≤ h / 2 * B := by
    rw [hZ, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
    exact mul_le_mul_of_nonneg_left
      (((isOrthProj_tangentProj hU₀ hV₀).norm_le _).trans (hB hY₀D)) (by linarith)
  have hDZ : (t₀ + h / 2, Z) ∈ D := hD _ ⟨by linarith, by linarith⟩ Z
    (by nlinarith [mul_nonneg hD₁0 (sq_nonneg h), mul_nonneg hD₂0 hε])
  have hθ := norm_capture_defect_le_sq_add hN hL hL0 hB hFt hrm hrn hU₀ hV₀ hh hH hρ hD hκ hD₁
    hD₂ hsmall hZ hG hUa augU kCap
  have hθ' := norm_capture_defect_right_le_sq_add hN hL hL0 hB hFt hrm hrn hU₀ hV₀ hh hH hρ hD hκ
    hD₁ hD₂ hsmall hZ hG hVa augV lCap
  refine (norm_update_sub_le hL hL0 hN hU₀ hV₀ hh hY₀D hA hA₀ hA3 hM₂ hM₃ hZ hDZ hDA hG hUa kCap
    lCap hθ hθ').trans (le_of_eq ?_)
  ring

/-! ### Non-vacuity -/

section Examples

open AugmentationRank AugmentationRank.Examples

/-- Bounds of the second and third derivatives within `[t₀, t₀ + h]` of a curve of class `C³`
there, by compactness. -/
private theorem exists_iteratedDerivWithin_bounds {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {A : ℝ → E} {t₀ h : ℝ} (hh : 0 < h)
    (hA3 : ContDiffOn ℝ 3 A (Icc t₀ (t₀ + h))) :
    ∃ M₂ M₃ : ℝ, (∀ t ∈ Icc t₀ (t₀ + h), ‖iteratedDerivWithin 2 A (Icc t₀ (t₀ + h)) t‖ ≤ M₂) ∧
      ∀ t ∈ Icc t₀ (t₀ + h), ‖iteratedDerivWithin 3 A (Icc t₀ (t₀ + h)) t‖ ≤ M₃ := by
  obtain ⟨hc, -, -⟩ := MidpointBUG.contDiffOn_three_data hh hA3
  obtain ⟨M₂, hM₂⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc 2 (by norm_num))
  obtain ⟨M₃, hM₃⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc 3 le_rfl)
  exact ⟨M₂, M₃, hM₂, hM₃⟩

/-- The derivatives of order two and three of an affine curve vanish on an interval. -/
private theorem iteratedDerivWithin_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y C : E) {a b : ℝ} (hab : a < b) {n : ℕ} (hn : n = 2 ∨ n = 3) {t : ℝ} (ht : t ∈ Icc a b) :
    iteratedDerivWithin n (fun t : ℝ => Y + (t - a) • C) (Icc a b) t = 0 := by
  have hd : deriv (fun t : ℝ => Y + (t - a) • C) = fun _ => C := by
    funext s
    exact ((((hasDerivAt_id s).sub_const a).smul_const C).const_add Y).deriv.trans (one_smul ℝ C)
  rcases hn with rfl | rfl
  · rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab) (by fun_prop) ht,
      iteratedDeriv_succ', iteratedDeriv_one, hd]
    simp
  · rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab) (by fun_prop) ht,
      iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_one, hd]
    simp

/-- The exact solution of `rowField` from `e₁ e₁ᵀ` with its coefficients written out. -/
private theorem exactSolution_eq : exactSolution = fun t : ℝ =>
    (!![1, 0; 0, 0; 0, 0] : Matrix (Fin 3) (Fin 2) ℝ) + t • !![0, 1; 1, 0; 0, 0] +
      t ^ 2 • !![0, 0; 0, 1; 1 / 2, 0] + t ^ 3 • !![0, 0; 0, 0; 0, 1 / 2] := rfl

/-- The exact solution of `rowField` is a polynomial curve. -/
private theorem contDiffOn_exactSolution (s : Set ℝ) : ContDiffOn ℝ 3 exactSolution s := by
  rw [exactSolution_eq]
  fun_prop

/-- The left basis `[e₁, (4 e₂ + 3 e₃)/5]`, an orthonormal basis of the range of `[U₀, G V₀]` for
the explicit step on `rowField` from `e₁ e₁ᵀ` with `h = 3/2`. -/
private noncomputable def rowLeft : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 4 / 5; 0, 3 / 5]

/-- The predictor of the explicit step on `rowField` from `e₁ e₁ᵀ` with `h = 3/2`. -/
private noncomputable def rowPredictor : Matrix (Fin 3) (Fin 2) ℝ :=
  startLeft * (1 : Matrix (Fin 1) (Fin 1) ℝ) * startRightᵀ +
    (3 / 2 / 2 : ℝ) • tangentProj startLeft startRight
      (rowField (startLeft * (1 : Matrix (Fin 1) (Fin 1) ℝ) * startRightᵀ))

/-- The start `Y₀ = e₁ e₁ᵀ`. -/
private theorem startPoint_eq :
    startLeft * (1 : Matrix (Fin 1) (Fin 1) ℝ) * startRightᵀ = !![1, 0; 0, 0; 0, 0] := by
  rw [← exactSolution_zero, exactSolution_eq]
  simp

/-- The predictor `Z = Y₀ + (3/4) P₀ F(Y₀)`, `F(Y₀) = e₁ e₂ᵀ + e₂ e₁ᵀ`, written out. -/
private theorem rowPredictor_eq : rowPredictor = !![1, 3 / 4; 3 / 4, 0; 0, 0] := by
  rw [rowPredictor, startPoint_eq]
  ext i j
  simp only [tangentProj_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, Fin.sum_univ_one,
    Matrix.transpose_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> norm_num [rowField, startLeft, startRight]

/-- The left basis `rowLeft` has orthonormal columns. -/
private theorem orth_rowLeft : rowLeftᵀ * rowLeft = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> norm_num [rowLeft]

/-- The left basis `rowLeft` captures `G V₀` for `G = rowField Z`. -/
private theorem kCap_rowLeft :
    rowLeft * rowLeftᵀ * (rowField rowPredictor * startRight) =
      rowField rowPredictor * startRight := by
  rw [rowPredictor_eq]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> norm_num [rowLeft, rowField, startRight]

/-- **Non-vacuity of `ODESolution.norm_midpoint_defect_le`, `ODESolution.norm_half_step_sub_le`
and `norm_predictor_sub_le`** on the field `rowField` (normal component zero at every rank-one
point) from `Y₀ = e₁ e₁ᵀ` with `h = 3/2`. The derivative bounds `M₂`, `M₃` of the cubic exact
solution are only asserted to exist (by compactness): the statement shows that the hypotheses
can be met, and as an existential over `M₂`, `M₃` it is not a quantitative bound. -/
example : ∃ M₂ M₃ : ℝ,
    ‖exactSolution (0 + 3 / 2) - exactSolution 0 -
        (3 / 2 : ℝ) • rowField (exactSolution (0 + 3 / 2 / 2))‖ ≤ M₃ * (3 / 2) ^ 3 / 24 ∧
      ‖exactSolution (0 + 3 / 2 / 2) - exactSolution 0 -
          (3 / 2 / 2 : ℝ) • rowField (exactSolution 0)‖ ≤ M₂ * (3 / 2) ^ 2 / 8 ∧
      ‖rowPredictor - exactSolution (0 + 3 / 2 / 2)‖ ≤ M₂ * (3 / 2) ^ 2 / 8 + 3 / 2 / 2 * 0 := by
  have hh : (0 : ℝ) < 3 / 2 := by norm_num
  obtain ⟨M₂, M₃, hM₂, hM₃⟩ :=
    exists_iteratedDerivWithin_bounds (t₀ := 0) hh (contDiffOn_exactSolution _)
  exact ⟨M₂, M₃,
    (odeSolution_exactSolution (0 + 3 / 2)).norm_midpoint_defect_le hh
      (contDiffOn_exactSolution _) hM₃,
    (odeSolution_exactSolution (0 + 3 / 2)).norm_half_step_sub_le hh
      ((contDiffOn_exactSolution _).of_le (by norm_num)) hM₂,
    norm_predictor_sub_le (F := fun _ => rowField) (Z := rowPredictor)
      factoredNormalBoundOn_rowField startLeft_orth startRight_orth hh (mem_univ _)
      (odeSolution_exactSolution (0 + 3 / 2)) exactSolution_zero
      ((contDiffOn_exactSolution _).of_le (by norm_num)) hM₂ rfl⟩

/-- **Non-vacuity of `norm_update_sub_le`** on the field `rowField` from `Y₀ = e₁ e₁ᵀ` with
`h = 3/2` (every rank-adaptive BUG step with a two-column left basis has error at least `h²/2`
there, `error_ge_of_isRankAdaptiveStep`): the bases `Ua = [e₁, (4 e₂ + 3 e₃)/5]` and `Va = I₂`,
`ε = 0`, the capture defects `θ`, `θ'` taken as the norms themselves, and the Lipschitz
bound on the three points that the theorem compares. As in the previous example, `L`, `M₂`,
`M₃` are only asserted to exist: the statement shows that the hypotheses can be met, not a
quantitative bound. -/
example : ∃ L M₂ M₃ : ℝ,
    ‖startLeft * (1 : Matrix (Fin 1) (Fin 1) ℝ) * startRightᵀ +
        (3 / 2 : ℝ) • galerkinProj rowLeft (1 : Matrix (Fin 2) (Fin 2) ℝ) (rowField rowPredictor) -
        exactSolution (0 + 3 / 2)‖ ≤
      3 / 2 * (‖(1 - rowLeft * rowLeftᵀ) * rowField rowPredictor *
            (1 - startRight * startRightᵀ)‖ +
          ‖(1 - startLeft * startLeftᵀ) * rowField rowPredictor *
            (1 - (1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ)‖) +
        L * (3 / 2) ^ 2 * 0 / 2 + (3 / 2) ^ 3 * (M₃ / 24 + L * M₂ / 8) := by
  have hh : (0 : ℝ) < 3 / 2 := by norm_num
  obtain ⟨M₂, M₃, hM₂, hM₃⟩ :=
    exists_iteratedDerivWithin_bounds (t₀ := 0) hh (contDiffOn_exactSolution _)
  set D : Set (ℝ × Matrix (Fin 3) (Fin 2) ℝ) :=
    {(0, startLeft * (1 : Matrix (Fin 1) (Fin 1) ℝ) * startRightᵀ),
      (0 + 3 / 2 / 2, rowPredictor), (0 + 3 / 2 / 2, exactSolution (0 + 3 / 2 / 2))} with hD
  have hne : rowPredictor - exactSolution (0 + 3 / 2 / 2) ≠ 0 := by
    intro h0
    have := congrFun (congrFun h0 1) 1
    rw [rowPredictor_eq, exactSolution_eq] at this
    norm_num at this
  set L := ‖rowField rowPredictor - rowField (exactSolution (0 + 3 / 2 / 2))‖ /
    ‖rowPredictor - exactSolution (0 + 3 / 2 / 2)‖ with hL
  have hLZ : ‖rowField rowPredictor - rowField (exactSolution (0 + 3 / 2 / 2))‖ ≤
      L * ‖rowPredictor - exactSolution (0 + 3 / 2 / 2)‖ := by
    rw [hL, div_mul_cancel₀ _ (norm_ne_zero_iff.2 hne)]
  have hLip : IsLipschitzFieldOn (fun _ => rowField) D L := by
    intro t x y hx hy
    simp only [hD, mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at hx hy
    rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hy with ⟨ht, rfl⟩ | ⟨ht, rfl⟩ | ⟨ht, rfl⟩
    all_goals first
      | (simp; done)
      | (norm_num at ht; done)
      | with_reducible exact hLZ
      | (rw [norm_sub_rev, norm_sub_rev (exactSolution _)]; with_reducible exact hLZ)
  refine ⟨L, M₂, M₃, norm_update_sub_le (F := fun _ => rowField) (D := D) (t₀ := 0) (h := 3 / 2)
    (A := exactSolution) (Z := rowPredictor) (G := rowField rowPredictor) (Ua := rowLeft)
    (Va := (1 : Matrix (Fin 2) (Fin 2) ℝ)) hLip
    (div_nonneg (norm_nonneg _) (norm_nonneg _))
    (factoredNormalBoundOn_rowField.mono (subset_univ _) le_rfl) startLeft_orth startRight_orth hh
    (mem_insert _ _) (odeSolution_exactSolution _) exactSolution_zero
    (contDiffOn_exactSolution _) hM₂ hM₃ rfl (mem_insert_of_mem _ (mem_insert _ _))
    (mem_insert_of_mem _ (mem_insert_of_mem _ (mem_singleton _))) rfl orth_rowLeft kCap_rowLeft
    (by simp) le_rfl le_rfl⟩

/-- A constant field whose third row leaves the left basis `[e₁, e₂]`. -/
private noncomputable def constField : Matrix (Fin 3) (Fin 2) ℝ := !![0, 1; 1, 0; 0, 1]

/-- The left basis `[e₁, e₂]` has orthonormal columns. -/
private theorem orth_augmentedLeft : augmentedLeftᵀ * augmentedLeft = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> norm_num [augmentedLeft]

/-- The left basis `[e₁, e₂]` contains `U₀ = e₁`. -/
private theorem augU_augmentedLeft : augmentedLeft * augmentedLeftᵀ * startLeft = startLeft := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> norm_num [augmentedLeft, startLeft]

/-- The left basis `[e₁, e₂]` captures `C V₀ = e₂`. -/
private theorem kCap_augmentedLeft :
    augmentedLeft * augmentedLeftᵀ * (constField * startRight) = constField * startRight := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> norm_num [augmentedLeft, constField, startRight]

/-- **Non-vacuity of `galerkin_local_error`**: the constant field `F ≡ C`,
`C = [[0, 1], [1, 0], [0, 1]]` (`L = Lₜ = 1`, `B = ε = ‖C‖`), the start `Y₀ = e₁ e₁ᵀ`, the bases
`Ua = [e₁, e₂]`, `Va = I₂`, every `h > 0`; the capture defect
`θ = ‖(1 - Ua Uaᵀ) C (1 - V₀ V₀ᵀ)‖` and `θ'` are taken as the norms themselves; the exact
solution `Y₀ + t C` is affine, so its derivative bounds are `M₂ = M₃ = 0`. -/
example {h : ℝ} (hh : 0 < h) :
    ‖(startLeft * (1 : Matrix (Fin 1) (Fin 1) ℝ) * startRightᵀ +
          (0 + h - 0) • galerkinProj augmentedLeft (1 : Matrix (Fin 2) (Fin 2) ℝ) constField) -
        (startLeft * (1 : Matrix (Fin 1) (Fin 1) ℝ) * startRightᵀ + (0 + h - 0) • constField)‖ ≤
      (Real.exp (1 * h) - 1) *
          (h * ((1 * ‖constField‖ + 1) * h / 2 + 1 * (0 * h ^ 2 / 8 + h / 2 * ‖constField‖) +
            (‖(1 - augmentedLeft * augmentedLeftᵀ) * constField *
              (1 - startRight * startRightᵀ)‖ +
              ‖(1 - startLeft * startLeftᵀ) * constField *
                (1 - (1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ)‖))) +
        (h * (1 * (0 * h ^ 2 / 8 + h / 2 * ‖constField‖) +
            (‖(1 - augmentedLeft * augmentedLeftᵀ) * constField *
              (1 - startRight * startRightᵀ)‖ +
              ‖(1 - startLeft * startLeftᵀ) * constField *
                (1 - (1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ)‖)) +
          0 * h ^ 3 / 24) := by
  have hA3 : ContDiffOn ℝ 3 (fun t : ℝ =>
      startLeft * (1 : Matrix (Fin 1) (Fin 1) ℝ) * startRightᵀ + (t - 0) • constField)
      (Icc 0 (0 + h)) := by fun_prop
  have hM₂ : ∀ t ∈ Icc (0 : ℝ) (0 + h), ‖iteratedDerivWithin 2 (fun t : ℝ =>
      startLeft * (1 : Matrix (Fin 1) (Fin 1) ℝ) * startRightᵀ + (t - 0) • constField)
        (Icc 0 (0 + h)) t‖ ≤ 0 := fun t ht => by
    rw [iteratedDerivWithin_affine _ _ (by linarith) (Or.inl rfl) ht, norm_zero]
  have hM₃ : ∀ t ∈ Icc (0 : ℝ) (0 + h), ‖iteratedDerivWithin 3 (fun t : ℝ =>
      startLeft * (1 : Matrix (Fin 1) (Fin 1) ℝ) * startRightᵀ + (t - 0) • constField)
        (Icc 0 (0 + h)) t‖ ≤ 0 := fun t ht => by
    rw [iteratedDerivWithin_affine _ _ (by linarith) (Or.inr rfl) ht, norm_zero]
  exact galerkin_local_error (F := fun _ _ => constField) (D := univ) (t₀ := 0) (h := h)
    (Lₜ := 1) (B := ‖constField‖) (S₀ := 1) (G := constField) (Ua := augmentedLeft)
    (Va := (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (A := fun t => startLeft * (1 : Matrix (Fin 1) (Fin 1) ℝ) * startRightᵀ + (t - 0) • constField)
    (YS := fun t => startLeft * (1 : Matrix (Fin 1) (Fin 1) ℝ) * startRightᵀ +
      (t - 0) • galerkinProj augmentedLeft (1 : Matrix (Fin 2) (Fin 2) ℝ) constField)
    (fun _ _ _ => by simp) zero_le_one (fun _ _ => le_rfl) (fun _ _ _ => by simp)
    (factoredNormalBound_iff_univ.1 (MatrixBUG.factoredNormalBound_const constField 1))
    startLeft_orth startRight_orth hh (mem_univ _) (MatrixBUG.odeSolution_affine _ _ _ _)
    (by simp) hA3 hM₂ hM₃ rfl rfl orth_augmentedLeft (by simp) augU_augmentedLeft (by simp)
    kCap_augmentedLeft (by simp) le_rfl le_rfl (MatrixBUG.odeSolution_affine _ _ _ _)
    (by simp)

/-- **Non-vacuity of `norm_update_sub_le_cube_add`**: the constant field `F ≡ C`,
`C = [[0, 1], [1, 0], [0, 1]]` (`L = Lₜ = 0`, `B = ε = ‖C‖`), the start `Y₀ = e₁ e₁ᵀ`, the bases
`Ua = [e₁, e₂]`, `Va = I₂`, `h = H = 1/2`, `ρ = 16`, `κ = 1`, `D₁ = 2`, `D₂ = 1`; the exact
solution `Y₀ + t C` is affine, so its derivative bounds are `M₂ = M₃ = 0`. -/
example :
    ‖startLeft * (1 : Matrix (Fin 1) (Fin 1) ℝ) * startRightᵀ +
        (1 / 2 : ℝ) • galerkinProj augmentedLeft (1 : Matrix (Fin 2) (Fin 2) ℝ) constField -
      (startLeft * (1 : Matrix (Fin 1) (Fin 1) ℝ) * startRightᵀ +
        ((0 : ℝ) + 1 / 2 - 0) • constField)‖ ≤
      (1 / 2) ^ 3 * (6 + 0 / 24) + 1 / 2 * ‖constField‖ * 7 := by
  have hh : (0 : ℝ) < 1 / 2 := by norm_num
  have hA3 : ContDiffOn ℝ 3 (fun t : ℝ =>
      startLeft * (1 : Matrix (Fin 1) (Fin 1) ℝ) * startRightᵀ + (t - 0) • constField)
      (Icc 0 (0 + 1 / 2)) := by fun_prop
  have hM₂ : ∀ t ∈ Icc (0 : ℝ) (0 + 1 / 2), ‖iteratedDerivWithin 2 (fun t : ℝ =>
      startLeft * (1 : Matrix (Fin 1) (Fin 1) ℝ) * startRightᵀ + (t - 0) • constField)
        (Icc 0 (0 + 1 / 2)) t‖ ≤ 0 := fun t ht => by
    rw [iteratedDerivWithin_affine _ _ (by norm_num) (Or.inl rfl) ht, norm_zero]
  have hM₃ : ∀ t ∈ Icc (0 : ℝ) (0 + 1 / 2), ‖iteratedDerivWithin 3 (fun t : ℝ =>
      startLeft * (1 : Matrix (Fin 1) (Fin 1) ℝ) * startRightᵀ + (t - 0) • constField)
        (Icc 0 (0 + 1 / 2)) t‖ ≤ 0 := fun t ht => by
    rw [iteratedDerivWithin_affine _ _ (by norm_num) (Or.inr rfl) ht, norm_zero]
  have hc0 := norm_nonneg constField
  have hc2 : ‖constField‖ ≤ 2 := by
    have h3 : ‖constField‖ ^ 2 = 3 := by
      rw [Frobenius.norm_sq_eq_sum]
      simp only [Fin.sum_univ_three, Fin.sum_univ_two]
      norm_num [constField]
    nlinarith [h3]
  have hmax : max (0 : ℝ) (2 * ‖constField‖ / 16) = ‖constField‖ / 8 := by
    rw [max_eq_right (by positivity)]; ring
  have hsq : Real.sqrt ((1 : ℕ) : ℝ) = 1 := by simp
  have hone : ‖(1 : Matrix (Fin 1) (Fin 1) ℝ)‖ = 1 := by
    have h : ‖(1 : Matrix (Fin 1) (Fin 1) ℝ)‖ ^ 2 = 1 := by
      rw [Frobenius.norm_sq_eq_sum]
      simp
    nlinarith [norm_nonneg (1 : Matrix (Fin 1) (Fin 1) ℝ)]
  refine (norm_update_sub_le_cube_add (F := fun _ _ => constField)
    (D := univ) (L := 0) (Lₜ := 0) (B := ‖constField‖) (ρ := 16) (H := 1 / 2) (κ := 1)
    (D₁ := 2) (D₂ := 1) (t₀ := 0) (h := 1 / 2) (S₀ := 1) (G := constField)
    (Ua := augmentedLeft) (Va := (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (A := fun t => startLeft * (1 : Matrix (Fin 1) (Fin 1) ℝ) * startRightᵀ + (t - 0) • constField)
    (factoredNormalBound_iff_univ.1 (MatrixBUG.factoredNormalBound_const constField 1))
    (by intro _ _ _ _ _; simp) le_rfl (by intro _ _ _; exact le_rfl) (fun _ _ _ _ _ => by simp)
    (by simp) (by simp) startLeft_orth startRight_orth hh le_rfl (by norm_num)
    (fun _ _ _ _ => mem_univ _) ?_ ?_ ?_ ?_ (MatrixBUG.odeSolution_affine _ _ _ _) (by simp) hA3
    hM₂ hM₃ (mem_univ _) rfl rfl orth_augmentedLeft (by simp) augU_augmentedLeft (by simp)
    kCap_augmentedLeft (by simp)).trans ?_
  · rw [hsq, hmax]
    linarith
  · rw [hsq, hmax, hone]
    linarith
  · rw [hsq, hmax]
    linarith
  · linarith
  · rw [hsq, hmax]
    linarith [mul_nonneg hc0 (sub_nonneg.2 hc2)]

end Examples

end ExplicitMidpoint

end LeanDLRA
