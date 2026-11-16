import LeanDLRA.Integrators.Matrix.BUGRun
import LeanDLRA.Integrators.PerturbedField
import LeanDLRA.Integrators.Matrix.ProjectorSplitting

/-!
# The BUG integrator applied to a surrogate model: existence of a run and error bound

In model reduction the integrator is often run on a surrogate field `Ft` (a cheaper or
hyper-reduced model, frozen coefficients, a learned closure) instead of the true field `F`. This
file combines the run theorem of the fixed-rank basis-update & Galerkin (BUG) integrator for
matrices near a solution (`MatrixBUG.exists_run_norm_sub_le`) with the perturbation bound for
the exact solutions (`PerturbedField.surrogate_grid_le`): the integrator, run on `Ft`, exists
and stays within the error bound of the surrogate problem plus `T e^{L T} η` of the true
solution, where `η` bounds the model error `‖F(t, A t) - Ft(t, A t)‖` along the true solution
`A`.

## Main results

* `PerturbedField.surrogate_bug_exists_run_norm_sub_le`: existence of a run on the surrogate
  field and the error bound with respect to the true solution.
* `PerturbedField.surrogate_bug_isRun_norm_sub_le`: the same bound for every run.

## Implementation notes

The surrogate problem is posed around the surrogate solution `At` with `At t₀ = A t₀`: the
surrogate field is bounded by `B`, continuous and has normal part at most `ε` on the tube of
radius `ρ` around `At` (`DLRAProblem Ft At …`, `FactoredNormalBoundOn Ft r …`). The comparison
of `At` with `A` is Grönwall's inequality and uses that `Ft` is `L`-Lipschitz everywhere
(`PerturbedField.surrogate_norm_sub_le`); nothing is assumed about the true field `F` except that
`A` solves it. These are corollaries of the run theorem of the BUG integrator; the step relation
is `MatrixBUG.stepRel Ft r` and no step relation in two fields is introduced.

## References

* G. Ceruti, J. Kusch, Ch. Lubich, *A rank-adaptive robust integrator for dynamical low-rank
  approximation*, arXiv:2104.05247 (the integrator; the fixed-rank form is arXiv:2010.02022).
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace PerturbedField

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}
  {F Ft : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A At : ℝ → Matrix m n ℝ}
  {t₀ h H T ρ L B ε η δ : ℝ} {N : ℕ}

/-- **Every run of the BUG integrator on a surrogate field satisfies the error bound with
respect to the true solution.** Let `Ft` be `L`-Lipschitz everywhere, let `At` solve
`Y' = Ft(t, Y)` with `At t₀ = A t₀`, and let `Ft` be bounded by `B`, continuous and with normal
part at most `ε` at the rank-`r` matrices on the tube of radius `ρ` around `At` over
`[t₀, t₀ + N h]`. Let `A` solve the true model `Y' = F(t, Y)` with model error
`‖F(t, A t) - Ft(t, A t)‖ ≤ η` along `A`. Then every run `Y` of the fixed-rank BUG integrator
for `Ft` with `0 ≤ h ≤ H`, `N h ≤ T`, `‖Y 0 - A t₀‖ ≤ δ` and
`bugGlobalBound L B H T δ ε h + 4 B h < ρ` satisfies

  `‖Y n - A (t₀ + n h)‖ ≤ bugGlobalBound L B H T δ ε h + T e^{L T} η`  for all `n ≤ N`. -/
theorem surrogate_bug_isRun_norm_sub_le {Y : ℕ → Matrix m n ℝ}
    (hFt : IsLipschitzField Ft L) (hP : DLRAProblem Ft At t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry Ft) (tubeSet At t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn Ft r (tubeSet At t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hA : ODESolution F A t₀ (t₀ + N * h))
    (hη : ∀ t ∈ Ico t₀ (t₀ + N * h), ‖F t (A t) - Ft t (A t)‖ ≤ η) (hη₀ : 0 ≤ η)
    (hAt₀ : At t₀ = A t₀) (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T)
    (hsmall : bugGlobalBound L B H T δ ε h + 4 * B * h < ρ)
    (hY : IsRun (MatrixBUG.stepRel Ft r) (uniformGrid t₀ h) N Y) (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ bugGlobalBound L B H T δ ε h + T * Real.exp (L * T) * η := by
  intro k hk
  have h₁ := MatrixBUG.IsRun.norm_sub_le hP hc hε hε₀ hh hhH hNT hsmall hY (by rwa [hAt₀]) k hk
  have h₂ := surrogate_grid_le hFt hP.L_nonneg hη₀ hh hA hP.sol hη hAt₀ hk
    ((mul_le_mul_of_nonneg_right (Nat.cast_le.2 hk) hh).trans hNT)
  have h₃ := norm_sub_le_norm_sub_add_norm_sub (Y k) (At (t₀ + k * h)) (A (t₀ + k * h))
  linarith

/-- **The BUG integrator on a surrogate field: existence of a run and error bound with respect to
the true solution.** Under the hypotheses of `PerturbedField.surrogate_bug_isRun_norm_sub_le`,
with `r ≤ m`, `r ≤ n`, from every start value `Y₀` of rank at most `r` with `‖Y₀ - A t₀‖ ≤ δ`
there is a run `Y 0 = Y₀, …, Y N` of the fixed-rank BUG integrator for `Ft`, all of rank at most
`r`, with

  `‖Y n - A (t₀ + n h)‖ ≤ bugGlobalBound L B H T δ ε h + T e^{L T} η`  for all `n ≤ N`.

The model error enters additively, with the factor `T e^{L T}` of a perturbation of the field. -/
theorem surrogate_bug_exists_run_norm_sub_le
    (hFt : IsLipschitzField Ft L) (hP : DLRAProblem Ft At t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry Ft) (tubeSet At t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn Ft r (tubeSet At t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hA : ODESolution F A t₀ (t₀ + N * h))
    (hη : ∀ t ∈ Ico t₀ (t₀ + N * h), ‖F t (A t) - Ft t (A t)‖ ≤ η) (hη₀ : 0 ≤ η)
    (hAt₀ : At t₀ = A t₀) (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : bugGlobalBound L B H T δ ε h + 4 * B * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (MatrixBUG.stepRel Ft r) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, (Y n).rank ≤ r ∧
        ‖Y n - A (t₀ + n * h)‖ ≤ bugGlobalBound L B H T δ ε h + T * Real.exp (L * T) * η := by
  obtain ⟨Y, hY0, hY, -⟩ := MatrixBUG.exists_run_norm_sub_le hP hc hε hε₀ hh hhH hNT hrm hrn hY₀
    (by rwa [hAt₀]) hsmall
  refine ⟨Y, hY0, hY, fun k hk => ⟨?_, ?_⟩⟩
  · exact MatrixBUG.IsRun.rank_le hY (by rw [hY0]; exact hY₀) k hk
  · exact surrogate_bug_isRun_norm_sub_le hFt hP hc hε hε₀ hA hη hη₀ hAt₀ hh hhH hNT hsmall hY
      (by rwa [hY0]) k hk

/-- **Non-vacuity.** The surrogate field `Ft(t, Y) = Y / max ‖Y‖ 1` is `2`-Lipschitz, bounded by
`1` and has no normal component (`MatrixKSL.radial_normal_eq_zero`); the true field
`F(t, Y) = Ft(t, Y) + G` differs from it by the constant `G`, so `η = ‖G‖`. For solutions `A` of
the true and `At` of the surrogate model with the same start value, the BUG integrator on the
surrogate field can be run from every `Y₀` of rank at most `r`, and the run stays within
`e^{2 T} δ + T e^{2 T} c₂ h + T e^{2 T} ‖G‖` of the true solution, `c₂ = bugC₂ 2 1 H`. -/
example (G : Matrix m n ℝ) (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    (hA : ODESolution (fun (_ : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z + G) A t₀
      (t₀ + N * h))
    (hAt : ODESolution (fun (_ : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z) At t₀ (t₀ + N * h))
    (hAt₀ : At t₀ = A t₀) (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T) {Y₀ : Matrix m n ℝ}
    (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - A t₀‖ ≤ δ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧
      IsRun (MatrixBUG.stepRel (fun (_ : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z) r)
        (uniformGrid t₀ h) N Y ∧
      ∀ j ≤ N, (Y j).rank ≤ r ∧ ‖Y j - A (t₀ + j * h)‖ ≤
        bugGlobalBound 2 1 H T δ 0 h + T * Real.exp (2 * T) * ‖G‖ := by
  have hlip : IsLipschitzField (fun (_ : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z) 2 :=
    fun _ X Y => MatrixKSL.norm_radial_sub_le X Y
  have hcont : Continuous fun Z : Matrix m n ℝ => MatrixKSL.radial Z :=
    (LipschitzWith.of_dist_le' (K := 2) fun X Y => by
      rw [dist_eq_norm, dist_eq_norm]; exact MatrixKSL.norm_radial_sub_le X Y).continuous
  exact surrogate_bug_exists_run_norm_sub_le (ε := 0)
    (ρ := bugGlobalBound 2 1 H T δ 0 h + 4 * 1 * h + 1) hlip
    ⟨hAt, by norm_num, by norm_num, fun _ _ X Y _ _ => MatrixKSL.norm_radial_sub_le X Y,
      fun _ _ X _ => MatrixKSL.norm_radial_le X⟩
    (hcont.comp continuous_snd).continuousOn
    (fun t U V S hU hV _ => MatrixKSL.radial_normal_eq_zero t U S V hU hV) le_rfl hA
    (fun t _ => by simp) (norm_nonneg G) hAt₀ hh hhH hNT hrm hrn hY₀ hδ (lt_add_one _)

end PerturbedField

end LeanDLRA
