import LeanDLRA.Stiff.DualWeightedResidual
import LeanDLRA.Classical.EckartYoung

/-!
# Two-sided error enclosure by a certified companion

Let `A` be a reference (the exact solution, or a full-rank scheme), `Y` the run whose error is
wanted and `Y'` a companion (a run of higher rank, or with smaller steps) together with a
certified bound `‖Y' - A‖ ≤ β`. Then

  `‖Y - Y'‖ - β ≤ ‖Y - A‖ ≤ ‖Y - Y'‖ + β`,

with the distance `‖Y - Y'‖`, which is computed from the factors of `Y` and `Y'`. When the
companion is much more accurate than the run, the enclosure is narrow even if the certificate
`β` of the companion overestimates the error of the companion by a large factor: both sides are
within `2 β` of the error of `Y`. This is the hierarchical estimator of reduced-basis and finite
element theory with its saturation constant replaced by a certified bound of the finer solution.

The certificate `β` can be any of the a posteriori bounds of the library. Two are stated here
for a companion sequence: the residual bound against the implicit Euler scheme
(`norm_sub_nonlinear_reference_le`) and the defect bound of a continuous curve through the
companion's iterates with a stepwise bound of its defect (one-sided Lipschitz field). For an
affine field and the cubic Hermite interpolant of the iterates, the defect on a step is the
explicit polynomial of `hermite_defect_eq`, whose norm the bound needs.

## Main results

* `abs_norm_sub_sub_norm_sub_le_of_norm_sub_le`: the enclosure in any seminormed group.
* `abs_norm_sub_sub_norm_sub_le_of_implicitEuler`: with `β` from the residuals of the companion
  against the implicit Euler scheme.
* `abs_norm_sub_sub_norm_sub_le_of_defect_steps`: with `β` from a stepwise defect bound of a
  curve through the companion and the recursion `q (n + 1) ≥ gronwallBound (q n) ℓ (η n) h`.
* `norm_truncation_sub_le_and_le_norm_sub_add`: the truncated SVD `T_r(Y')` of the companion,
  with the certificate `‖Y' - T_r(Y')‖ + β`, is never worse than the enclosure of any run of
  rank `≤ r`: a run certified through the companion at tolerance `tol` has a compressed
  companion of the same rank that is certified at `tol` as well.
* `hermite_defect_eq`: for an affine field `x ↦ L x + g`, the defect of the cubic Hermite
  interpolant of `(y₀, f₀)` and `(y₁, f₁)` at `θ ∈ [0, 1]` is `θ (1 - θ) (E₀ + θ E₁)` with
  `E₀ = (6/h)(y₁ - y₀) - 4 f₀ - 2 f₁ - h L f₀` and `E₁ = 2 f₀ - 2 f₁ + h L f₀ + h L f₁`.
-/

open Set Finset
open scoped RealInnerProductSpace

namespace LeanDLRA

section Enclosure

variable {G : Type*} [SeminormedAddCommGroup G]

/-- **Two-sided enclosure by a certified companion.** If `‖y' - a‖ ≤ β`, then the error
`‖y - a‖` differs from the computable distance `‖y - y'‖` by at most `β`. -/
theorem abs_norm_sub_sub_norm_sub_le_of_norm_sub_le {y y' a : G} {β : ℝ}
    (hβ : ‖y' - a‖ ≤ β) : |‖y - a‖ - ‖y - y'‖| ≤ β := by
  have h := abs_norm_sub_norm_le (y - a) (y - y')
  rw [show y - a - (y - y') = y' - a by abel] at h
  exact h.trans hβ

/-- The enclosure of `abs_norm_sub_sub_norm_sub_le_of_norm_sub_le` as a lower and an upper
bound: `‖y - y'‖ - β ≤ ‖y - a‖ ≤ ‖y - y'‖ + β`. -/
theorem norm_sub_sub_le_and_le_add_of_norm_sub_le {y y' a : G} {β : ℝ}
    (hβ : ‖y' - a‖ ≤ β) : ‖y - y'‖ - β ≤ ‖y - a‖ ∧ ‖y - a‖ ≤ ‖y - y'‖ + β := by
  have h := abs_le.1 (abs_norm_sub_sub_norm_sub_le_of_norm_sub_le (y := y) hβ)
  constructor <;> linarith [h.1, h.2]

/-- The hypothesis of `abs_norm_sub_sub_norm_sub_le_of_norm_sub_le` holds with `β ≠ 0`: the
run `1`, the companion `1/10` and the reference `0` in `ℝ`, `β = 1/10`. -/
example : |‖(1 : ℝ) - 0‖ - ‖(1 : ℝ) - 1 / 10‖| ≤ 1 / 10 :=
  abs_norm_sub_sub_norm_sub_le_of_norm_sub_le (by norm_num)

end Enclosure

section ImplicitEuler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Enclosure with a companion certified against the implicit Euler scheme.** Let `A` be the
implicit Euler scheme `A_{k+1} = A_k + h F_k(A_{k+1})`, `Y` any sequence (the run) and `Y'` any
sequence (the companion), with the one-sided inequality of `F_k` at the pairs
`(Y'_{k+1}, A_{k+1})` and `h ℓ < 1`. Then `‖Y_n - A_n‖` differs from `‖Y_n - Y'_n‖` by at most
`max(1, (1 - h ℓ)⁻¹)ⁿ (‖Y'_0 - A_0‖ + ∑_{k<n} ‖Y'_{k+1} - Y'_k - h F_k(Y'_{k+1})‖)`, the bound
`norm_sub_nonlinear_reference_le` of the companion. -/
theorem abs_norm_sub_sub_norm_sub_le_of_implicitEuler {F : ℕ → E → E} {h ℓ : ℝ} {N : ℕ}
    {A Y Y' : ℕ → E} (hh : 0 ≤ h) (hℓ : h * ℓ < 1)
    (hF : ∀ k < N, ⟪F k (Y' (k + 1)) - F k (A (k + 1)), Y' (k + 1) - A (k + 1)⟫
      ≤ ℓ * ‖Y' (k + 1) - A (k + 1)‖ ^ 2)
    (hA : ∀ k < N, A (k + 1) = A k + h • F k (A (k + 1))) :
    ∀ n ≤ N, |‖Y n - A n‖ - ‖Y n - Y' n‖| ≤ max 1 (1 - h * ℓ)⁻¹ ^ n * (‖Y' 0 - A 0‖
      + ∑ k ∈ range n, ‖Y' (k + 1) - Y' k - h • F k (Y' (k + 1))‖) := fun n hn =>
  abs_norm_sub_sub_norm_sub_le_of_norm_sub_le
    (norm_sub_nonlinear_reference_le (Y := Y') hh hℓ hF hA n hn)

/-- The hypotheses of `abs_norm_sub_sub_norm_sub_le_of_implicitEuler` hold with nonzero data:
`F x = -x` on `ℝ` (`ℓ = -1`), `h = 1`, the scheme `A n = (1/2)ⁿ`, one step. -/
example (Y Y' : ℕ → ℝ) :
    |‖Y 1 - (1 / 2 : ℝ) ^ 1‖ - ‖Y 1 - Y' 1‖| ≤ max 1 (1 - 1 * (-1 : ℝ))⁻¹ ^ 1 *
      (‖Y' 0 - (1 / 2 : ℝ) ^ 0‖ + ∑ k ∈ range 1, ‖Y' (k + 1) - Y' k - (1 : ℝ) • -Y' (k + 1)‖) :=
  abs_norm_sub_sub_norm_sub_le_of_implicitEuler (F := fun _ x => -x) (A := fun n => (1 / 2) ^ n)
    (h := 1) (ℓ := -1) (N := 1) zero_le_one (by norm_num)
    (fun k _ => by
      change ⟪-Y' (k + 1) - -(1 / 2 : ℝ) ^ (k + 1), Y' (k + 1) - (1 / 2) ^ (k + 1)⟫
        ≤ -1 * ‖Y' (k + 1) - (1 / 2) ^ (k + 1)‖ ^ 2
      rw [show -Y' (k + 1) - -(1 / 2 : ℝ) ^ (k + 1) = -(Y' (k + 1) - (1 / 2) ^ (k + 1)) by ring,
        inner_neg_left, real_inner_self_eq_norm_sq]
      linarith)
    (fun k _ => by
      change (1 / 2 : ℝ) ^ (k + 1) = (1 / 2) ^ k + (1 : ℝ) • -(1 / 2 : ℝ) ^ (k + 1)
      rw [one_smul, pow_succ]
      ring) 1 le_rfl

/-- **Enclosure with a companion curve and a stepwise defect bound.** On the grid
`tₙ = t₀ + n h`, let `A` solve `A' = F(t, A)` with `F` one-sided Lipschitz with constant `ℓ`,
let `Y'` be a continuous curve with right derivative `u` (for example an interpolant of the
companion's iterates) whose defect satisfies `‖u t - F(t, Y' t)‖ ≤ η n` on the `n`-th step, and
let `‖Y' t₀ - A t₀‖ ≤ q 0` and `gronwallBound (q n) ℓ (η n) h ≤ q (n + 1)`. Then for any
sequence `Y` (the run), `‖Y n - A tₙ‖` differs from `‖Y n - Y' tₙ‖` by at most `q n`. -/
theorem abs_norm_sub_sub_norm_sub_le_of_defect_steps {F : ℝ → E → E} {ℓ : ℝ}
    (hF : IsOneSidedLipschitzField F ℓ) {t₀ h : ℝ} (hh : 0 ≤ h) {K : ℕ} {A Y' u : ℝ → E}
    {Y : ℕ → E} (hA : ODESolution F A t₀ (t₀ + K * h))
    (hc : ContinuousOn Y' (Icc t₀ (t₀ + K * h)))
    (hd : ∀ t ∈ Ico t₀ (t₀ + K * h), HasDerivWithinAt Y' (u t) (Ici t) t) {η q : ℕ → ℝ}
    (hη : ∀ n < K, ∀ t ∈ Ico (t₀ + n * h) (t₀ + (n + 1) * h), ‖u t - F t (Y' t)‖ ≤ η n)
    (h0 : ‖Y' t₀ - A t₀‖ ≤ q 0)
    (hq : ∀ n < K, gronwallBound (q n) ℓ (η n) h ≤ q (n + 1)) :
    ∀ n ≤ K, |‖Y n - A (t₀ + n * h)‖ - ‖Y n - Y' (t₀ + n * h)‖| ≤ q n := by
  have key : ∀ n ≤ K, ‖Y' (t₀ + n * h) - A (t₀ + n * h)‖ ≤ q n := by
    intro n
    induction n with
    | zero => intro _; simpa using h0
    | succ n ih =>
      intro hn
      have hnK : n < K := hn
      have hn' : (n : ℝ) + 1 ≤ K := by exact_mod_cast hn
      have hnh : 0 ≤ (n : ℝ) * h := mul_nonneg (Nat.cast_nonneg n) hh
      have hKh : ((n : ℝ) + 1) * h ≤ K * h := mul_le_mul_of_nonneg_right hn' hh
      have hle : t₀ + n * h ≤ t₀ + (n + 1) * h := by nlinarith
      have hsub : Icc (t₀ + n * h) (t₀ + (n + 1) * h) ⊆ Icc t₀ (t₀ + K * h) :=
        Icc_subset_Icc (by linarith) (by linarith)
      have hsub' : Ico (t₀ + n * h) (t₀ + (n + 1) * h) ⊆ Ico t₀ (t₀ + K * h) :=
        Ico_subset_Ico (by linarith) (by linarith)
      have h1 := norm_sub_le_gronwallBound_of_oneSided hF (y := Y') (z := A) (u := u)
        (w := fun t => F t (A t)) (ηy := η n) (ηz := 0) (hc.mono hsub)
        (fun t ht => hd t (hsub' ht)) (hη n hnK) (hA.cont.mono hsub)
        (fun t ht => hA.deriv t (hsub' ht)) (fun t _ => by simp) (ih hnK.le)
        (t₀ + (n + 1) * h) (right_mem_Icc.2 hle)
      have h2 : t₀ + ((n : ℝ) + 1) * h - (t₀ + n * h) = h := by ring
      rw [h2, add_zero] at h1
      have hcast : ((n + 1 : ℕ) : ℝ) = n + 1 := by push_cast; ring
      rw [hcast]
      exact h1.trans (hq n hnK)
  exact fun n hn => abs_norm_sub_sub_norm_sub_le_of_norm_sub_le (key n hn)

/-- The hypotheses of `abs_norm_sub_sub_norm_sub_le_of_defect_steps` hold with nonzero
constants: `x' = -x` on `[0, 1]` (`ℓ = -1`), one step `h = 1`, the companion curve `1 - t` with
defect `-t`, `η 0 = 1`, `q 0 = 0`, `q 1 = gronwallBound 0 (-1) 1 1`. -/
example (Y : ℕ → ℝ) :
    |‖Y 1 - Real.exp (-(0 + (1 : ℕ) * 1))‖ - ‖Y 1 - (1 - (0 + (1 : ℕ) * 1))‖| ≤
      (fun n : ℕ => if n = 0 then (0 : ℝ) else gronwallBound 0 (-1) 1 1) 1 := by
  refine abs_norm_sub_sub_norm_sub_le_of_defect_steps (F := fun _ x => -x) (ℓ := -1) (t₀ := 0)
    (h := 1) (q := fun n : ℕ => if n = 0 then (0 : ℝ) else gronwallBound 0 (-1) 1 1)
    (fun t x y => ?_) zero_le_one (K := 1) (A := fun t => Real.exp (-t))
    (Y' := fun t => 1 - t) (u := fun _ => -1) ?_ (by fun_prop) (fun t _ => ?_)
    (η := fun _ => 1) ?_ (by simp) ?_ 1 le_rfl
  · rw [show -x - -y = -(x - y) by ring, inner_neg_left, real_inner_self_eq_norm_sq]
    linarith
  · refine ⟨by fun_prop, fun t _ => ?_⟩
    have := ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).hasDerivWithinAt
      (s := Ici t)
    simpa [Function.comp_def] using this
  · simpa using ((hasDerivAt_id t).const_sub (1 : ℝ)).hasDerivWithinAt
  · intro n hn t ht
    have hn0 : n = 0 := by omega
    subst hn0
    simp only [Nat.cast_zero, zero_mul, add_zero, zero_add, one_mul] at ht
    rw [show -1 - -(1 - t) = -t by ring, norm_neg, Real.norm_of_nonneg ht.1]
    exact ht.2.le
  · intro n hn
    have hn0 : n = 0 := by omega
    subst hn0
    simp

end ImplicitEuler

section Compression

open scoped LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **Certified compression of the companion dominates the companion enclosure.** If
`‖Y' - A‖ ≤ β` and `rank B ≤ r`, the truncated SVD `T_r(Y')` satisfies
`‖T_r(Y') - A‖ ≤ ‖Y' - T_r(Y')‖ + β`, and this computable certificate is at most the upper
enclosure `‖B - Y'‖ + β` of the rank-`r` run `B` (Eckart–Young). -/
theorem norm_truncation_sub_le_and_le_norm_sub_add {Y' A B : Matrix m n ℝ} {r : ℕ} {β : ℝ}
    (hβ : ‖Y' - A‖ ≤ β) (hB : B.rank ≤ r) :
    ‖EckartYoung.truncation Y' r - A‖ ≤ ‖Y' - EckartYoung.truncation Y' r‖ + β ∧
      ‖Y' - EckartYoung.truncation Y' r‖ + β ≤ ‖B - Y'‖ + β := by
  constructor
  · have h := norm_sub_le_norm_sub_add_norm_sub (EckartYoung.truncation Y' r) Y' A
    rw [norm_sub_rev (EckartYoung.truncation Y' r) Y'] at h
    linarith
  · have h := EckartYoung.norm_sub_truncation_le Y' hB
    rw [norm_sub_rev Y' B] at h
    linarith

/-- The hypotheses of `norm_truncation_sub_le_and_le_norm_sub_add` hold with `β ≠ 0`: the
companion `1` and the reference `0` (`2 × 2`), `β = ‖1‖`, the run `B = 0` of rank `0`. -/
example : ‖EckartYoung.truncation (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 - 0‖ ≤
      ‖(1 : Matrix (Fin 2) (Fin 2) ℝ) - EckartYoung.truncation 1 0‖
        + ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ :=
  (norm_truncation_sub_le_and_le_norm_sub_add (A := 0) (B := 0) (by simp)
    (by simp [Matrix.rank_zero])).1

end Compression

section Hermite

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **Defect of the cubic Hermite interpolant for an affine field.** Let `f₀ = L y₀ + g` and
`f₁ = L y₁ + g`. The cubic Hermite interpolant on a step of length `h`, in the variable
`θ ∈ [0, 1]`, is `(2θ³ - 3θ² + 1) y₀ + h (θ³ - 2θ² + θ) f₀ + (3θ² - 2θ³) y₁ + h (θ³ - θ²) f₁`;
its derivative in time is
`((6θ² - 6θ)/h) y₀ + (3θ² - 4θ + 1) f₀ + ((6θ - 6θ²)/h) y₁ + (3θ² - 2θ) f₁`. The derivative
minus the field at the interpolant is `θ (1 - θ) (E₀ + θ E₁)` with
`E₀ = (6/h)(y₁ - y₀) - 4 f₀ - 2 f₁ - h L f₀` and `E₁ = 2 f₀ - 2 f₁ + h L f₀ + h L f₁`. -/
theorem hermite_defect_eq (L : E →ₗ[ℝ] E) {g y₀ y₁ f₀ f₁ : E} (hf₀ : f₀ = L y₀ + g)
    (hf₁ : f₁ = L y₁ + g) (h θ : ℝ) :
    ((6 * θ ^ 2 - 6 * θ) / h) • y₀ + (3 * θ ^ 2 - 4 * θ + 1) • f₀
        + ((6 * θ - 6 * θ ^ 2) / h) • y₁ + (3 * θ ^ 2 - 2 * θ) • f₁
      - (L ((2 * θ ^ 3 - 3 * θ ^ 2 + 1) • y₀ + (h * (θ ^ 3 - 2 * θ ^ 2 + θ)) • f₀
        + (3 * θ ^ 2 - 2 * θ ^ 3) • y₁ + (h * (θ ^ 3 - θ ^ 2)) • f₁) + g)
      = (θ * (1 - θ)) • ((6 / h) • (y₁ - y₀) - (4 : ℝ) • f₀ - (2 : ℝ) • f₁ - h • L f₀
        + θ • ((2 : ℝ) • f₀ - (2 : ℝ) • f₁ + h • L f₀ + h • L f₁)) := by
  have e₀ : L y₀ = f₀ - g := by rw [hf₀]; abel
  have e₁ : L y₁ = f₁ - g := by rw [hf₁]; abel
  simp only [map_add, map_smul, e₀, e₁]
  module

/-- `hermite_defect_eq` on `ℝ` with `L = 2`, `g = 1`, `y₀ = 1`, `y₁ = 3`, `h = 1/2`. -/
example (θ : ℝ) :
    ((6 * θ ^ 2 - 6 * θ) / (1 / 2)) • (1 : ℝ) + (3 * θ ^ 2 - 4 * θ + 1) • (3 : ℝ)
        + ((6 * θ - 6 * θ ^ 2) / (1 / 2)) • (3 : ℝ) + (3 * θ ^ 2 - 2 * θ) • (7 : ℝ)
      - ((2 : ℝ) • ((2 * θ ^ 3 - 3 * θ ^ 2 + 1) • (1 : ℝ) + (1 / 2 * (θ ^ 3 - 2 * θ ^ 2 + θ)) • 3
        + (3 * θ ^ 2 - 2 * θ ^ 3) • 3 + (1 / 2 * (θ ^ 3 - θ ^ 2)) • 7) + 1)
      = (θ * (1 - θ)) • (((6 : ℝ) / (1 / 2)) • ((3 : ℝ) - 1) - (4 : ℝ) • 3 - (2 : ℝ) • 7
        - (1 / 2 : ℝ) • (2 : ℝ) • (3 : ℝ) + θ • ((2 : ℝ) • 3 - (2 : ℝ) • 7
        + (1 / 2 : ℝ) • (2 : ℝ) • (3 : ℝ) + (1 / 2 : ℝ) • (2 : ℝ) • (7 : ℝ))) :=
  hermite_defect_eq (E := ℝ) ((2 : ℝ) • LinearMap.id) (g := 1) (y₀ := 1) (y₁ := 3) (f₀ := 3)
    (f₁ := 7) (by norm_num) (by norm_num) (1 / 2) θ

end Hermite

end LeanDLRA
