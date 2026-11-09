import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Foundations.Localization
import LeanDLRA.Foundations.ODE
import LeanDLRA.Foundations.Projector
import LeanDLRA.HighOrder.RungeKuttaBUG
import LeanDLRA.Literature.HighOrder.P2502_07040b
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2502.07040: convergence of the RK-BUG integrator

This module proves the convergence analysis of the RK-BUG integrator of Nobile–Riffaud on real
matrices, for Algorithm 2 as formalised in the companion module
`LeanDLRA.Literature.HighOrder.P2502_07040b` (`IsRKBUGStep`, `IsRKBUGSolution`: `orth` bases of
the concatenated ranges, Galerkin core, best rank-`r` truncation), with the paper's constants.
Proved: Sec. 2.1, the augmented update is the Galerkin projection `Π` of the Euler-type step, `Π`
fixes `Y_k` and every tangent projection `P_{Y_j} F_j` of nonzero weight
(`IsAugmentedUpdate.exists_galerkin`, `eulerBUG_galerkin`, `galerkinProj_tangentProj`);
Proposition 3, (22) and (23) (`norm_sub_galerkin_final_le`, `norm_sub_galerkin_stage_le`); Lemma 4
with the paper's `C_i` (`IsRKBUGStep.stage_error`, `IsRKBUGRun.stage_error`); Theorem 1 with the
paper's `C` (`IsRKBUGStep.local_error`, `IsRKBUGRun.local_error`); Theorem 2 with the paper's `C'
= max {e^{L T}, C (e^{L T} - 1) / L}` (`IsRKBUGRun.global_error`, and
`IsRKBUGRun.global_error_paper` with `V_r` of radius `max {R₁, R₂}` and `γ̄_r` of Proposition 4);
and Remark 2 at full rank (`epsR_eq_zero_of_full`, `IsRKBUGRun.global_error_full_rank`). The
projection error `ε_r` is the actual supremum over `V_r` (`epsR`, finite by `le_epsR`); that the
stages lie in `V_r` is the companion's `stage_mem_nbhdV` (Lemmas 1, 2, Proposition 2), the exact
flows from the iterates are constructed, and the truncation constant is the companion's `γ̄_r`, so
the only hypothesis beyond the paper's assumptions is Proposition 5. The local and global error
bounds are therefore conditional on Proposition 5 (hypothesis `IsRKLocalError`, resp. `hRK`). No
listed claim is false.

Differences from the paper. (1) The local error of the underlying Runge–Kutta method (Proposition
5, a citation of Hairer–Nørsett–Wanner) is the hypothesis `IsRKLocalError`, required on `V_r`
only; it is proved for explicit Euler (`isRKLocalError_euler`), and `euler_instance` satisfies all
hypotheses of Theorem 2 at once. (2) In `global_error` the truncation constant is any `γ` bounding
the truncation errors of the run (`TruncBound`); the paper's `γ_r` is by definition such a bound,
and `global_error_paper` uses `γ̄_r`, whose constant carries `max {C_b, maxᵢ ∑ⱼ |a_{ij}|}` instead
of `C_b` (see the companion). (3) Following the companion, `V_r` uses `rank ≤ r` (the paper's
`M_r`, rank exactly `r`, does not contain truncations that lose rank); `ε_r` is then the supremum
over all orthonormal factorisations. `global_error` takes any set `𝒱 ⊆ V_r` containing the stages,
so the paper's rank-`r` set is covered too (`global_error_rank_eq`, assuming the stages have rank
`r`, as the paper tacitly does). (4) `0 ≤ c_i ≤ 1` and `s > 0` are assumed (`IsRKBUGRun`), so that
the stage times lie in `[0, T]` and the first stage is `Y_k`. (5) The step-wise statements
(`IsRKBUGStep.stage_error`, `IsRKBUGStep.local_error`) take a bound `ε` on the tangent-projection
defects of the stages; along a run it is derived that `ε = ε_r` works. The abstract
`LeanDLRA.RungeKuttaBUG.rkBUG_global_error` assumes the normal components and has another
constant; it is not used.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2502_07040

open LeanDLRA

/-! ### The Galerkin projector of the augmented bases (Sec. 2.1, Proposition 3) -/

section Galerkin

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {p q k l r : ℕ}

/-- The Galerkin projector `Π X = Û Ûᵀ X V̂ V̂ᵀ` onto the matrices `Û S V̂ᵀ`. -/
noncomputable def galerkinProj (Uh : Matrix ι (Fin p) ℝ) (Vh : Matrix κ (Fin q) ℝ) :
    Matrix ι κ ℝ →L[ℝ] Matrix ι κ ℝ :=
  leftProj Uh * rightProj Vh

/-- `Π X = Û (Ûᵀ X V̂) V̂ᵀ`: the Galerkin coefficient matrix `Ŝ = Ûᵀ X V̂` of the S-step. -/
lemma galerkinProj_apply (Uh : Matrix ι (Fin p) ℝ) (Vh : Matrix κ (Fin q) ℝ) (X : Matrix ι κ ℝ) :
    galerkinProj Uh Vh X = Uh * (Uhᵀ * X * Vh) * Vhᵀ :=
  leftProj_rightProj_apply Uh Vh X

/-- `Π` is an orthogonal projector for the Frobenius inner product. -/
lemma isOrthProj_galerkinProj {Uh : Matrix ι (Fin p) ℝ} {Vh : Matrix κ (Fin q) ℝ}
    (hU : Uhᵀ * Uh = 1) (hV : Vhᵀ * Vh = 1) : IsOrthProj (galerkinProj Uh Vh) :=
  isOrthProj_leftProj_mul_rightProj hU hV

/-- The augmented bases `Û`, `V̂` **contain the tangent data** of `(U, V, G)`: the columns of `U`
and `G V` lie in the range of `Û`, the columns of `V` and `Gᵀ U` in the range of `V̂`. These are the
columns which the K- and L-steps of arXiv 2502.07040 (Sec. 2.1, 2.2) put into `orth(·)`. -/
structure Contains (Uh : Matrix ι (Fin p) ℝ) (Vh : Matrix κ (Fin q) ℝ) (U : Matrix ι (Fin k) ℝ)
    (V : Matrix κ (Fin l) ℝ) (G : Matrix ι κ ℝ) : Prop where
  capU : Uh * Uhᵀ * U = U
  capV : Vh * Vhᵀ * V = V
  capGV : Uh * Uhᵀ * (G * V) = G * V
  capGU : Vh * Vhᵀ * (Gᵀ * U) = Gᵀ * U

/-- **`Π` fixes the tangent projection** (arXiv 2502.07040, the step of the proof of Prop. 3 that
the paper writes as `range Φ ⊆ span Û`, `range Ψ ⊆ span V̂`): if `Û`, `V̂` contain `U`, `G V`, `V`,
`Gᵀ U`, then `Û Ûᵀ (P G) V̂ V̂ᵀ = P G` for `P G = U Uᵀ G + G V Vᵀ - U Uᵀ G V Vᵀ`. No
orthonormality is needed for this identity. -/
theorem galerkinProj_tangentProj {Uh : Matrix ι (Fin p) ℝ} {Vh : Matrix κ (Fin q) ℝ}
    {U : Matrix ι (Fin k) ℝ} {V : Matrix κ (Fin l) ℝ} {G : Matrix ι κ ℝ}
    (hc : Contains Uh Vh U V G) : galerkinProj Uh Vh (tangentProj U V G) = tangentProj U V G := by
  have hsymm : (Vh * Vhᵀ)ᵀ = Vh * Vhᵀ := by simp [Matrix.transpose_mul]
  have hVB : Vᵀ * (Vh * Vhᵀ) = Vᵀ := by
    have := congrArg Matrix.transpose hc.capV
    rwa [Matrix.transpose_mul, hsymm] at this
  have hGB : Uᵀ * G * (Vh * Vhᵀ) = Uᵀ * G := by
    have := congrArg Matrix.transpose hc.capGU
    simpa only [Matrix.transpose_mul, hsymm, Matrix.transpose_transpose] using this
  have hgal : ∀ X : Matrix ι κ ℝ, galerkinProj Uh Vh X = Uh * Uhᵀ * X * (Vh * Vhᵀ) := fun X => by
    rw [galerkinProj_apply]
    simp only [Matrix.mul_assoc]
  have h1 : Uh * Uhᵀ * (U * Uᵀ * G) * (Vh * Vhᵀ) = U * Uᵀ * G := by
    calc Uh * Uhᵀ * (U * Uᵀ * G) * (Vh * Vhᵀ)
        = (Uh * Uhᵀ * U) * (Uᵀ * G * (Vh * Vhᵀ)) := by simp only [Matrix.mul_assoc]
      _ = U * Uᵀ * G := by rw [hc.capU, hGB, Matrix.mul_assoc]
  have h2 : Uh * Uhᵀ * (G * V * Vᵀ) * (Vh * Vhᵀ) = G * V * Vᵀ := by
    calc Uh * Uhᵀ * (G * V * Vᵀ) * (Vh * Vhᵀ)
        = (Uh * Uhᵀ * (G * V)) * (Vᵀ * (Vh * Vhᵀ)) := by simp only [Matrix.mul_assoc]
      _ = G * V * Vᵀ := by rw [hc.capGV, hVB]
  have h3 : Uh * Uhᵀ * (U * Uᵀ * G * V * Vᵀ) * (Vh * Vhᵀ) = U * Uᵀ * G * V * Vᵀ := by
    calc Uh * Uhᵀ * (U * Uᵀ * G * V * Vᵀ) * (Vh * Vhᵀ)
        = (Uh * Uhᵀ * U) * (Uᵀ * G * V) * (Vᵀ * (Vh * Vhᵀ)) := by simp only [Matrix.mul_assoc]
      _ = U * Uᵀ * G * V * Vᵀ := by rw [hc.capU, hVB]; simp only [Matrix.mul_assoc]
  rw [hgal, tangentProj_apply, Matrix.mul_sub, Matrix.mul_add, Matrix.sub_mul, Matrix.add_mul,
    h1, h2, h3]

/-- **Galerkin at least as accurate as the tangent projection** (arXiv 2502.07040, Prop. 3, the
step common to (22) and (23)): `‖G - Π G‖ ≤ ‖G - P G‖` when `Û`, `V̂` contain the tangent data. -/
theorem norm_sub_galerkinProj_le {Uh : Matrix ι (Fin p) ℝ} {Vh : Matrix κ (Fin q) ℝ}
    {U : Matrix ι (Fin k) ℝ} {V : Matrix κ (Fin l) ℝ} {G : Matrix ι κ ℝ}
    (hU : Uhᵀ * Uh = 1) (hV : Vhᵀ * Vh = 1) (hc : Contains Uh Vh U V G) :
    ‖G - galerkinProj Uh Vh G‖ ≤ ‖G - tangentProj U V G‖ :=
  (isOrthProj_galerkinProj hU hV).norm_sub_le_of_mem_range G _ (galerkinProj_tangentProj hc)

/-- `Π` fixes `U S Vᵀ` when `Û`, `V̂` contain `U`, `V`. -/
lemma galerkinProj_factored {Uh : Matrix ι (Fin p) ℝ} {Vh : Matrix κ (Fin q) ℝ}
    {U : Matrix ι (Fin k) ℝ} {V : Matrix κ (Fin l) ℝ} (S : Matrix (Fin k) (Fin l) ℝ)
    (hU : Uh * Uhᵀ * U = U) (hV : Vh * Vhᵀ * V = V) :
    galerkinProj Uh Vh (U * S * Vᵀ) = U * S * Vᵀ := by
  have hsymm : (Vh * Vhᵀ)ᵀ = Vh * Vhᵀ := by simp [Matrix.transpose_mul]
  have hVB : Vᵀ * (Vh * Vhᵀ) = Vᵀ := by
    have := congrArg Matrix.transpose hV
    rwa [Matrix.transpose_mul, hsymm] at this
  rw [galerkinProj_apply]
  calc Uh * (Uhᵀ * (U * S * Vᵀ) * Vh) * Vhᵀ = (Uh * Uhᵀ * U) * S * (Vᵀ * (Vh * Vhᵀ)) := by
        simp only [Matrix.mul_assoc]
    _ = U * S * Vᵀ := by rw [hU, hVB]

/-- **Forward-Euler BUG as Galerkin projection** (arXiv 2502.07040, Sec. 2.1).  Let
`Y = U S Vᵀ`, and let `Û`, `V̂` be orthonormal and contain `U`, `G V`, respectively `V`, `Gᵀ U`
(in the paper `Û = orth[U, G V]`, `V̂ = orth[V, Gᵀ U]`, `G = F(t, Y)`; the inclusion is what is
needed).  With `Ŝ = Ûᵀ (Y + h G) V̂` the augmented solution `Ŷ = Û Ŝ V̂ᵀ` satisfies:

1. `Ŷ = Π (Y + h G)`, with `Π X = Û Ûᵀ X V̂ V̂ᵀ` the Galerkin projector;
2. `Π Y = Y`;
3. `Π (P G) = P G`, where `P` is the tangent projector at `Y`;
4. `Π (Y + h P G) = Y + h P G`: the bases represent the projected step exactly;
5. `Ŝ` solves the least-squares problem `min_S ‖Û S V̂ᵀ - (Y + h G)‖`;
6. `‖G - Π G‖ ≤ ‖G - P G‖`. -/
theorem eulerBUG_galerkin {Uh : Matrix ι (Fin p) ℝ} {Vh : Matrix κ (Fin q) ℝ}
    {U : Matrix ι (Fin r) ℝ} {V : Matrix κ (Fin r) ℝ} {G : Matrix ι κ ℝ}
    (hU : Uhᵀ * Uh = 1) (hV : Vhᵀ * Vh = 1) (hc : Contains Uh Vh U V G)
    (S : Matrix (Fin r) (Fin r) ℝ) (h : ℝ) :
    let Y := U * S * Vᵀ
    let Yh := Uh * (Uhᵀ * (Y + h • G) * Vh) * Vhᵀ
    Yh = galerkinProj Uh Vh (Y + h • G) ∧ galerkinProj Uh Vh Y = Y ∧
      galerkinProj Uh Vh (tangentProj U V G) = tangentProj U V G ∧
      galerkinProj Uh Vh (Y + h • tangentProj U V G) = Y + h • tangentProj U V G ∧
      (∀ S' : Matrix (Fin p) (Fin q) ℝ, ‖(Y + h • G) - Yh‖ ≤ ‖(Y + h • G) - Uh * S' * Vhᵀ‖) ∧
      ‖G - galerkinProj Uh Vh G‖ ≤ ‖G - tangentProj U V G‖ := by
  intro Y Yh
  have hY : galerkinProj Uh Vh Y = Y := galerkinProj_factored S hc.capU hc.capV
  have hT := galerkinProj_tangentProj hc
  have hYh : Yh = galerkinProj Uh Vh (Y + h • G) := (galerkinProj_apply Uh Vh _).symm
  refine ⟨hYh, hY, hT, by rw [map_add, map_smul, hY, hT], fun S' => ?_,
    norm_sub_galerkinProj_le hU hV hc⟩
  rw [hYh]
  refine (isOrthProj_galerkinProj hU hV).norm_sub_le_of_mem_range _ _ ?_
  exact galerkinProj_factored S' (by rw [Matrix.mul_assoc, hU, Matrix.mul_one])
    (by rw [Matrix.mul_assoc, hV, Matrix.mul_one])

end Galerkin

/-! ### Explicit Runge–Kutta stages and the constants of Lemma 4 and Theorem 1 -/

section RK

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {s : ℕ}

/-- A sum over a subtype of `Fin s` equals the full sum when the summand vanishes off the
subtype. -/
lemma sum_subtype_eq {M : Type*} [AddCommMonoid M] (P : Fin s → Prop) [DecidablePred P]
    (f : Fin s → M) (hf : ∀ j, ¬ P j → f j = 0) : ∑ j : {j // P j}, f j = ∑ j, f j := by
  rw [← Finset.sum_subtype (Finset.univ.filter P) (by simp) f]
  exact Finset.sum_filter_of_ne fun j _ hj => by_contra fun hP => hj (hf j hP)

/-- The stages `Z_i = y + h ∑_{j<i} a_{ij} F(t + c_j h, Z_j)` of the explicit Runge–Kutta method
started at `y` at time `t` (arXiv 2502.07040, the "unprojected" stages of Lemma 4). -/
noncomputable def rkStage (F : ℝ → E → E) (a : Fin s → Fin s → ℝ) (c : Fin s → ℝ) (t h : ℝ) (y : E)
    (i : Fin s) : E :=
  y + h • ∑ j : {j // j < i}, a i j • F (t + c j * h) (rkStage F a c t h y j)
termination_by i
decreasing_by exact j.2

/-- The result `y + h ∑_i b_i F(t + c_i h, Z_i)` of the explicit Runge–Kutta step. -/
noncomputable def rkResult (F : ℝ → E → E) (a : Fin s → Fin s → ℝ) (b c : Fin s → ℝ) (t h : ℝ)
    (y : E) : E :=
  y + h • ∑ i, b i • F (t + c i * h) (rkStage F a c t h y i)

/-- For an explicit tableau the stage sum may be taken over all `j`. -/
lemma rkStage_eq {F : ℝ → E → E} {a : Fin s → Fin s → ℝ} (ha : ∀ i j, i ≤ j → a i j = 0)
    (c : Fin s → ℝ) (t h : ℝ) (y : E) (i : Fin s) :
    rkStage F a c t h y i = y + h • ∑ j, a i j • F (t + c j * h) (rkStage F a c t h y j) := by
  rw [rkStage, sum_subtype_eq (fun j => j < i)
    (fun j => a i j • F (t + c j * h) (rkStage F a c t h y j))
    (fun j hj => by rw [ha i j (not_lt.mp hj), zero_smul])]

/-- The stage constants of arXiv 2502.07040, Lemma 4: `C₁ = 0` and, for `i ≥ 2`,
`C_i = max {∑_{j<i} |a_{ij}| (1 + L C_j h₀), 1 + ∑_{j<i} |a_{ij}| L C_j h₀}`. -/
noncomputable def stageConst (a : Fin s → Fin s → ℝ) (L h₀ : ℝ) (i : Fin s) : ℝ :=
  if (i : ℕ) = 0 then 0 else
    max (∑ j : {j // j < i}, |a i j| * (1 + L * stageConst a L h₀ j * h₀))
      (1 + ∑ j : {j // j < i}, |a i j| * L * stageConst a L h₀ j * h₀)
termination_by i
decreasing_by all_goals exact j.2

/-- The constant `max {∑ |w_j| (1 + L C_j h₀), 1 + ∑ |w_j| L C_j h₀}` for the weights `w`; for
`w = a i` this is `C_i` (`i ≥ 2`). -/
noncomputable def rowConst (a : Fin s → Fin s → ℝ) (w : Fin s → ℝ) (L h₀ : ℝ) : ℝ :=
  max (∑ j, |w j| * (1 + L * stageConst a L h₀ j * h₀))
    (1 + ∑ j, |w j| * L * stageConst a L h₀ j * h₀)

/-- The constant of arXiv 2502.07040, Theorem 1:
`C = max {∑ |b_i| (1 + L C_i h₀), 1 + ∑ |b_i| L C_i h₀, C_L}`. -/
noncomputable def localConst (a : Fin s → Fin s → ℝ) (b : Fin s → ℝ) (L h₀ CL : ℝ) : ℝ :=
  max (rowConst a b L h₀) CL

/-- `C_i = rowConst (a i)` for `i ≥ 2` and an explicit tableau. -/
lemma stageConst_eq_rowConst {a : Fin s → Fin s → ℝ} (ha : ∀ i j, i ≤ j → a i j = 0) (L h₀ : ℝ)
    {i : Fin s} (hi : (i : ℕ) ≠ 0) : stageConst a L h₀ i = rowConst a (a i) L h₀ := by
  rw [stageConst]
  simp only [hi, ↓reduceIte]
  rw [rowConst, sum_subtype_eq (fun j => j < i)
    (fun j => |a i j| * (1 + L * stageConst a L h₀ j * h₀))
    (fun j hj => by rw [ha i j (not_lt.mp hj)]; simp), sum_subtype_eq (fun j => j < i)
    (fun j => |a i j| * L * stageConst a L h₀ j * h₀)
    (fun j hj => by rw [ha i j (not_lt.mp hj)]; simp)]

lemma stageConst_nonneg (a : Fin s → Fin s → ℝ) {L h₀ : ℝ} (hL : 0 ≤ L) (hh₀ : 0 ≤ h₀)
    (i : Fin s) : 0 ≤ stageConst a L h₀ i := by
  induction i using (wellFounded_lt (α := Fin s)).induction with
  | _ i ih =>
    rw [stageConst]
    split_ifs with hi
    · exact le_rfl
    · refine le_max_of_le_right (add_nonneg zero_le_one (Finset.sum_nonneg fun j _ => ?_))
      have := ih j j.2
      positivity

/-- `C ≥ 1`: the constant of Theorem 1 is positive. -/
lemma one_le_localConst (a : Fin s → Fin s → ℝ) (b : Fin s → ℝ) {L h₀ : ℝ} (hL : 0 ≤ L)
    (hh₀ : 0 ≤ h₀) (CL : ℝ) : 1 ≤ localConst a b L h₀ CL := by
  refine le_max_of_le_left (le_max_of_le_right ?_)
  have : 0 ≤ ∑ j, |b j| * L * stageConst a L h₀ j * h₀ := Finset.sum_nonneg fun j _ => by
    have := stageConst_nonneg a hL hh₀ j
    positivity
  linarith

/-- The elementary estimate behind Lemma 4 and Theorem 1. -/
lemma comb_le_rowConst (a : Fin s → Fin s → ℝ) (w : Fin s → ℝ) {L h₀ h ε γ : ℝ} (hL : 0 ≤ L)
    (hh₀ : 0 ≤ h₀) (hhh₀ : h ≤ h₀) (hε : 0 ≤ ε) (hγ : 0 ≤ γ) :
    γ + ∑ j, |w j| * (L * (stageConst a L h₀ j * h * (ε + γ)) + ε) ≤
      rowConst a w L h₀ * (ε + γ) := by
  set A := ∑ j, |w j| * (1 + L * stageConst a L h₀ j * h₀) with hA
  set B := 1 + ∑ j, |w j| * L * stageConst a L h₀ j * h₀ with hB
  have hterm : ∀ j, |w j| * (L * (stageConst a L h₀ j * h * (ε + γ)) + ε) ≤
      |w j| * (1 + L * stageConst a L h₀ j * h₀) * ε +
        |w j| * L * stageConst a L h₀ j * h₀ * γ := fun j => by
    have hC := stageConst_nonneg a hL hh₀ j
    have hw := abs_nonneg (w j)
    have hmono : L * stageConst a L h₀ j * h ≤ L * stageConst a L h₀ j * h₀ :=
      mul_le_mul_of_nonneg_left hhh₀ (mul_nonneg hL hC)
    have h1 : L * (stageConst a L h₀ j * h * (ε + γ)) + ε ≤
        (1 + L * stageConst a L h₀ j * h₀) * ε + L * stageConst a L h₀ j * h₀ * γ := by
      have := mul_le_mul_of_nonneg_right hmono (add_nonneg hε hγ)
      nlinarith
    calc |w j| * (L * (stageConst a L h₀ j * h * (ε + γ)) + ε)
        ≤ |w j| * ((1 + L * stageConst a L h₀ j * h₀) * ε + L * stageConst a L h₀ j * h₀ * γ) :=
          mul_le_mul_of_nonneg_left h1 hw
      _ = _ := by ring
  have hsum : ∑ j, |w j| * (L * (stageConst a L h₀ j * h * (ε + γ)) + ε) ≤
      A * ε + (B - 1) * γ := by
    calc _ ≤ ∑ j, (|w j| * (1 + L * stageConst a L h₀ j * h₀) * ε +
          |w j| * L * stageConst a L h₀ j * h₀ * γ) := Finset.sum_le_sum fun j _ => hterm j
      _ = A * ε + (B - 1) * γ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hA, hB]
        ring
  have hAle : A ≤ rowConst a w L h₀ := le_max_left _ _
  have hBle : B ≤ rowConst a w L h₀ := le_max_right _ _
  have := mul_le_mul_of_nonneg_right hAle hε
  have := mul_le_mul_of_nonneg_right hBle hγ
  nlinarith

/-- One Runge–Kutta step with projected stages, in abstract form: the first stage is the starting
value; every other stage and the result are, up to `h γ`, the image of the Runge–Kutta combination
under a linear map `R` fixing `y` whose normal components `(1 - R) F_j` are `≤ ε` for the weights
`≠ 0`. A step of Algorithm 2 is of this form with `R = Π` (`IsRKBUGStep.toProjected`). -/
structure IsProjectedStep (F : ℝ → E → E) (a : Fin s → Fin s → ℝ) (b c : Fin s → ℝ)
    (ε γ t h : ℝ) (y : E) (Y : Fin s → E) (y₁ : E) : Prop where
  first : ∀ i : Fin s, (i : ℕ) = 0 → Y i = y
  stage : ∀ i : Fin s, (i : ℕ) ≠ 0 → ∃ R : E →L[ℝ] E, R y = y ∧
    (∀ j, a i j ≠ 0 → ‖(1 - R) (F (t + c j * h) (Y j))‖ ≤ ε) ∧
    ‖Y i - R (y + h • ∑ j, a i j • F (t + c j * h) (Y j))‖ ≤ h * γ
  final : ∃ R : E →L[ℝ] E, R y = y ∧
    (∀ j, b j ≠ 0 → ‖(1 - R) (F (t + c j * h) (Y j))‖ ≤ ε) ∧
    ‖y₁ - R (y + h • ∑ j, b j • F (t + c j * h) (Y j))‖ ≤ h * γ

/-- **Stage error, abstract form** (arXiv 2502.07040, Lemma 4, with the paper's constants `C_i`):
`‖Y_i - Z_i‖ ≤ C_i h (ε + γ)`, with `Z_i` the unprojected Runge–Kutta stages from `y`.  The
Lipschitz bound is only needed at the stage times. -/
theorem stage_error_le {F : ℝ → E → E} {a : Fin s → Fin s → ℝ} {b c : Fin s → ℝ}
    (ha : ∀ i j, i ≤ j → a i j = 0) {L h₀ ε γ t h : ℝ} {y y₁ : E} {Y : Fin s → E} (hL : 0 ≤ L)
    (hF : ∀ i x z, ‖F (t + c i * h) x - F (t + c i * h) z‖ ≤ L * ‖x - z‖) (hh : 0 ≤ h)
    (hhh₀ : h ≤ h₀) (hε : 0 ≤ ε) (hγ : 0 ≤ γ) (hS : IsProjectedStep F a b c ε γ t h y Y y₁)
    (i : Fin s) : ‖Y i - rkStage F a c t h y i‖ ≤ stageConst a L h₀ i * h * (ε + γ) := by
  have hh₀ : 0 ≤ h₀ := hh.trans hhh₀
  induction i using (wellFounded_lt (α := Fin s)).induction with
  | _ i ih =>
    by_cases hi : (i : ℕ) = 0
    · have hno : ∀ j, a i j = 0 := fun j => ha i j (Fin.le_def.2 (by omega))
      rw [hS.first i hi, rkStage_eq ha]
      simp [hno, stageConst, hi]
    · obtain ⟨R, hRy, hRn, hRs⟩ := hS.stage i hi
      have h2 := RungeKuttaBUG.norm_proj_comb_sub_le (R := R) (w := a i)
        (u := fun j => F (t + c j * h) (Y j))
        (v := fun j => F (t + c j * h) (rkStage F a c t h y j)) hRy hh hRn
      have hterm : ∑ j, |a i j| * (‖F (t + c j * h) (Y j) -
          F (t + c j * h) (rkStage F a c t h y j)‖ + ε) ≤
          ∑ j, |a i j| * (L * (stageConst a L h₀ j * h * (ε + γ)) + ε) := by
        refine Finset.sum_le_sum fun j _ => ?_
        by_cases hji : j < i
        · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have := (hF j _ _).trans (mul_le_mul_of_nonneg_left (ih j hji) hL)
          linarith
        · simp [ha i j (not_lt.mp hji)]
      have hcomb := comb_le_rowConst a (a i) hL hh₀ hhh₀ hε hγ
      rw [← stageConst_eq_rowConst ha L h₀ hi] at hcomb
      calc ‖Y i - rkStage F a c t h y i‖
          ≤ ‖Y i - R (y + h • ∑ j, a i j • F (t + c j * h) (Y j))‖ +
            ‖R (y + h • ∑ j, a i j • F (t + c j * h) (Y j)) - rkStage F a c t h y i‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ h * γ + h * ∑ j, |a i j| * (L * (stageConst a L h₀ j * h * (ε + γ)) + ε) := by
            rw [rkStage_eq ha c t h y i]
            exact add_le_add hRs (h2.trans (mul_le_mul_of_nonneg_left hterm hh))
        _ = h * (γ + ∑ j, |a i j| * (L * (stageConst a L h₀ j * h * (ε + γ)) + ε)) := by ring
        _ ≤ h * (stageConst a L h₀ i * (ε + γ)) := mul_le_mul_of_nonneg_left hcomb hh
        _ = stageConst a L h₀ i * h * (ε + γ) := by ring

/-- The result of the step is within `rowConst b · h (ε + γ)` of the unprojected Runge–Kutta
result (arXiv 2502.07040, proof of Theorem 1, the first two terms of the decomposition). -/
theorem result_error_le {F : ℝ → E → E} {a : Fin s → Fin s → ℝ} {b c : Fin s → ℝ}
    (ha : ∀ i j, i ≤ j → a i j = 0) {L h₀ ε γ t h : ℝ} {y y₁ : E} {Y : Fin s → E} (hL : 0 ≤ L)
    (hF : ∀ i x z, ‖F (t + c i * h) x - F (t + c i * h) z‖ ≤ L * ‖x - z‖) (hh : 0 ≤ h)
    (hhh₀ : h ≤ h₀) (hε : 0 ≤ ε) (hγ : 0 ≤ γ) (hS : IsProjectedStep F a b c ε γ t h y Y y₁) :
    ‖y₁ - rkResult F a b c t h y‖ ≤ rowConst a b L h₀ * h * (ε + γ) := by
  have hh₀ : 0 ≤ h₀ := hh.trans hhh₀
  obtain ⟨R, hRy, hRn, hRs⟩ := hS.final
  have h2 := RungeKuttaBUG.norm_proj_comb_sub_le (R := R) (w := b)
    (u := fun j => F (t + c j * h) (Y j))
    (v := fun j => F (t + c j * h) (rkStage F a c t h y j)) hRy hh hRn
  have hterm : ∑ j, |b j| * (‖F (t + c j * h) (Y j) -
      F (t + c j * h) (rkStage F a c t h y j)‖ + ε) ≤
      ∑ j, |b j| * (L * (stageConst a L h₀ j * h * (ε + γ)) + ε) := by
    refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have := (hF j _ _).trans (mul_le_mul_of_nonneg_left
      (stage_error_le ha hL hF hh hhh₀ hε hγ hS j) hL)
    linarith
  have hcomb := comb_le_rowConst a b hL hh₀ hhh₀ hε hγ
  calc ‖y₁ - rkResult F a b c t h y‖
      ≤ ‖y₁ - R (y + h • ∑ j, b j • F (t + c j * h) (Y j))‖ +
        ‖R (y + h • ∑ j, b j • F (t + c j * h) (Y j)) - rkResult F a b c t h y‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ h * γ + h * ∑ j, |b j| * (L * (stageConst a L h₀ j * h * (ε + γ)) + ε) :=
        add_le_add hRs (h2.trans (mul_le_mul_of_nonneg_left hterm hh))
    _ = h * (γ + ∑ j, |b j| * (L * (stageConst a L h₀ j * h * (ε + γ)) + ε)) := by ring
    _ ≤ h * (rowConst a b L h₀ * (ε + γ)) := mul_le_mul_of_nonneg_left hcomb hh
    _ = rowConst a b L h₀ * h * (ε + γ) := by ring

end RK

/-! ### Algorithm 2: Proposition 3, Lemma 4 and Theorem 1 for one step -/

section Step

variable {n m r s : ℕ}

lemma colSpan_le_smul {d : ℕ} {ι : Type*} {c : ℝ} (hc : c ≠ 0) (A : Matrix (Fin d) ι ℝ) :
    colSpan A ≤ colSpan (c • A) := by
  have := colSpan_smul_le c⁻¹ (c • A)
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

/-- The columns of nonzero weight lie in the augmented space. -/
lemma le_augSpace {d : ℕ} (U₀ : Matrix (Fin d) (Fin r) ℝ) {w : Fin s → ℝ}
    (U G : Fin s → Matrix (Fin d) (Fin r) ℝ) {j : Fin s} (hj : w j ≠ 0) :
    colSpan (U j) ≤ augSpace U₀ w U G ∧ colSpan (G j) ≤ augSpace U₀ w U G :=
  ⟨(colSpan_le_smul hj _).trans (le_sup_of_le_right (le_iSup_of_le j le_sup_left)),
    (colSpan_le_smul hj _).trans (le_sup_of_le_right (le_iSup_of_le j le_sup_right))⟩

variable {p q : ℕ} {Uh : Matrix (Fin n) (Fin p) ℝ} {Vh : Matrix (Fin m) (Fin q) ℝ}
  {Yk Ynew : LowRank n m r} {Ys : Fin s → LowRank n m r} {Fs : Fin s → Matrix (Fin n) (Fin m) ℝ}
  {w : Fin s → ℝ}

/-- The paper's bases `Û = orth[U_k, w_j U_j, w_j F_j V_j]`, `V̂ = orth[V_k, w_j V_j, w_j F_jᵀ U_j]`
contain the tangent data of every stage of nonzero weight. -/
theorem contains_of_isOrthOf
    (hU : IsOrthOf Uh (augSpace Yk.U w (fun i => (Ys i).U) fun i => Fs i * (Ys i).V))
    (hV : IsOrthOf Vh (augSpace Yk.V w (fun i => (Ys i).V) fun i => (Fs i)ᵀ * (Ys i).U))
    {j : Fin s} (hj : w j ≠ 0) : Contains Uh Vh (Ys j).U (Ys j).V (Fs j) := by
  have h1 := le_augSpace Yk.U (fun i => (Ys i).U) (fun i => Fs i * (Ys i).V) hj
  have h2 := le_augSpace Yk.V (fun i => (Ys i).V) (fun i => (Fs i)ᵀ * (Ys i).U) hj
  rw [← hU.colSpan_eq] at h1
  rw [← hV.colSpan_eq] at h2
  exact ⟨capture_of_colSpan_le hU.orthonormal h1.1, capture_of_colSpan_le hV.orthonormal h2.1,
    capture_of_colSpan_le hU.orthonormal h1.2, capture_of_colSpan_le hV.orthonormal h2.2⟩

/-- The Galerkin projector of the paper's bases fixes `Y_k`. -/
theorem fix_of_isOrthOf
    (hU : IsOrthOf Uh (augSpace Yk.U w (fun i => (Ys i).U) fun i => Fs i * (Ys i).V))
    (hV : IsOrthOf Vh (augSpace Yk.V w (fun i => (Ys i).V) fun i => (Fs i)ᵀ * (Ys i).U)) :
    galerkinProj Uh Vh Yk.mat = Yk.mat :=
  galerkinProj_factored Yk.S
    (capture_of_colSpan_le hU.orthonormal (by rw [hU.colSpan_eq]; exact le_sup_left))
    (capture_of_colSpan_le hV.orthonormal (by rw [hV.colSpan_eq]; exact le_sup_left))

/-- **Proposition 3** of arXiv 2502.07040, (22) for `w = b` and (23) for `w = a_{i·}`: for the
bases `Û`, `V̂` of an update of Algorithm 2 and `w_j ≠ 0`,
`‖F_j - Û Ûᵀ F_j V̂ V̂ᵀ‖ ≤ ‖F_j - P_{Y_j}(F_j)‖`. -/
theorem norm_sub_galerkin_le_of_isOrthOf
    (hU : IsOrthOf Uh (augSpace Yk.U w (fun i => (Ys i).U) fun i => Fs i * (Ys i).V))
    (hV : IsOrthOf Vh (augSpace Yk.V w (fun i => (Ys i).V) fun i => (Fs i)ᵀ * (Ys i).U))
    {j : Fin s} (hj : w j ≠ 0) :
    ‖Fs j - galerkinProj Uh Vh (Fs j)‖ ≤ ‖Fs j - tangentProj (Ys j).U (Ys j).V (Fs j)‖ :=
  norm_sub_galerkinProj_le hU.orthonormal hV.orthonormal (contains_of_isOrthOf hU hV hj)

/-- **Sec. 2.1 of arXiv 2502.07040 for every update of Algorithm 2**: there are orthonormal bases
`Û`, `V̂` (the paper's `orth`) such that `Ŷ = Π (Y_k + h ∑_j w_j F_j)` with the orthogonal
projector `Π X = Û Ûᵀ X V̂ V̂ᵀ`, `Π Y_k = Y_k`, `Π (P_{Y_j} F_j) = P_{Y_j} F_j` and
`‖F_j - Π F_j‖ ≤ ‖F_j - P_{Y_j} F_j‖` for `w_j ≠ 0`, and `Y_new` is a best rank-`r`
approximation of `Ŷ`. -/
theorem IsAugmentedUpdate.exists_galerkin {h : ℝ} {Yhat : Matrix (Fin n) (Fin m) ℝ}
    (hup : IsAugmentedUpdate Yk Ys Fs h w Yhat Ynew) :
    ∃ (p q : ℕ) (Uh : Matrix (Fin n) (Fin p) ℝ) (Vh : Matrix (Fin m) (Fin q) ℝ),
      IsOrthProj (galerkinProj Uh Vh) ∧
      Yhat = galerkinProj Uh Vh (Yk.mat + h • ∑ j, w j • Fs j) ∧
      galerkinProj Uh Vh Yk.mat = Yk.mat ∧
      (∀ j, w j ≠ 0 →
        galerkinProj Uh Vh (tangentProj (Ys j).U (Ys j).V (Fs j)) =
          tangentProj (Ys j).U (Ys j).V (Fs j) ∧
        ‖Fs j - galerkinProj Uh Vh (Fs j)‖ ≤ ‖Fs j - tangentProj (Ys j).U (Ys j).V (Fs j)‖) ∧
      IsBestRankApprox r Yhat Ynew.mat := by
  obtain ⟨p, q, Uh, Vh, hU, hV, hY, hbest⟩ := hup
  exact ⟨p, q, Uh, Vh, isOrthProj_galerkinProj hU.orthonormal hV.orthonormal,
    hY.trans (galerkinProj_apply Uh Vh _).symm, fix_of_isOrthOf hU hV,
    fun j hj => ⟨galerkinProj_tangentProj (contains_of_isOrthOf hU hV hj),
      norm_sub_galerkin_le_of_isOrthOf hU hV hj⟩, hbest⟩

variable {F : ℝ → Matrix (Fin n) (Fin m) ℝ → Matrix (Fin n) (Fin m) ℝ} {tab : ExplicitRK s}
  {h t ε γ L h₀ : ℝ} {Yhs : Fin s → Matrix (Fin n) (Fin m) ℝ} {Yh : Matrix (Fin n) (Fin m) ℝ}
  {Ynext : LowRank n m r}

/-- **Proposition 3, inequality (22)** of arXiv 2502.07040: in a step of Algorithm 2, for
`b_i ≠ 0` and the bases `Û_{k+1}`, `V̂_{k+1}` of the final update,
`‖F_{ki} - Û_{k+1} Û_{k+1}ᵀ F_{ki} V̂_{k+1} V̂_{k+1}ᵀ‖ ≤ ‖F_{ki} - P_{Y_{ki}}(F_{ki})‖`. -/
theorem norm_sub_galerkin_final_le
    (hU : IsOrthOf Uh (augSpace Yk.U tab.b (fun i => (Ys i).U)
      fun i => F (t + tab.c i * h) (Ys i).mat * (Ys i).V))
    (hV : IsOrthOf Vh (augSpace Yk.V tab.b (fun i => (Ys i).V)
      fun i => (F (t + tab.c i * h) (Ys i).mat)ᵀ * (Ys i).U)) {i : Fin s} (hi : tab.b i ≠ 0) :
    ‖F (t + tab.c i * h) (Ys i).mat - galerkinProj Uh Vh (F (t + tab.c i * h) (Ys i).mat)‖ ≤
      ‖F (t + tab.c i * h) (Ys i).mat -
        tangentProj (Ys i).U (Ys i).V (F (t + tab.c i * h) (Ys i).mat)‖ :=
  norm_sub_galerkin_le_of_isOrthOf (Fs := fun j => F (t + tab.c j * h) (Ys j).mat) hU hV hi

/-- **Proposition 3, inequality (23)** of arXiv 2502.07040: in a step of Algorithm 2, for
`a_{ij} ≠ 0` and the bases `Û_{ki}`, `V̂_{ki}` of the update of stage `i`,
`‖F_{kj} - Û_{ki} Û_{ki}ᵀ F_{kj} V̂_{ki} V̂_{ki}ᵀ‖ ≤ ‖F_{kj} - P_{Y_{kj}}(F_{kj})‖`. -/
theorem norm_sub_galerkin_stage_le {i : Fin s}
    (hU : IsOrthOf Uh (augSpace Yk.U (tab.a i) (fun i => (Ys i).U)
      fun i => F (t + tab.c i * h) (Ys i).mat * (Ys i).V))
    (hV : IsOrthOf Vh (augSpace Yk.V (tab.a i) (fun i => (Ys i).V)
      fun i => (F (t + tab.c i * h) (Ys i).mat)ᵀ * (Ys i).U)) {j : Fin s} (hij : tab.a i j ≠ 0) :
    ‖F (t + tab.c j * h) (Ys j).mat - galerkinProj Uh Vh (F (t + tab.c j * h) (Ys j).mat)‖ ≤
      ‖F (t + tab.c j * h) (Ys j).mat -
        tangentProj (Ys j).U (Ys j).V (F (t + tab.c j * h) (Ys j).mat)‖ :=
  norm_sub_galerkin_le_of_isOrthOf (Fs := fun j => F (t + tab.c j * h) (Ys j).mat) hU hV hij

/-- `γ` bounds the truncation errors `‖Ŷ - 𝓡(Ŷ)‖ ≤ h γ` of a step, at the stages `i ≥ 2` and at
the result.  The constant `γ_r` of arXiv 2502.07040, Sec. 3.2, is by definition the smallest such
`γ` for all steps started in `V_r`; Proposition 4 (`truncation_error_gamma`) provides `γ̄_r`. -/
def TruncBound (Ys : Fin s → LowRank n m r) (Yhs : Fin s → Matrix (Fin n) (Fin m) ℝ)
    (Yh : Matrix (Fin n) (Fin m) ℝ) (Ynext : LowRank n m r) (h γ : ℝ) : Prop :=
  (∀ i : Fin s, (i : ℕ) ≠ 0 → ‖Yhs i - (Ys i).mat‖ ≤ h * γ) ∧ ‖Yh - Ynext.mat‖ ≤ h * γ

lemma one_sub_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (R : E →L[ℝ] E)
    (x : E) : (1 - R) x = x - R x :=
  rfl

/-- A step of Algorithm 2 whose stages have tangent-projection defects `≤ ε` and whose truncations
are `≤ h γ` is a projected Runge–Kutta step, with `R = Π` (via Proposition 3). -/
theorem IsRKBUGStep.toProjected (step : IsRKBUGStep F tab h t Yk Ys Yhs Yh Ynext)
    (hε : ∀ j, ‖F (t + tab.c j * h) (Ys j).mat -
      tangentProj (Ys j).U (Ys j).V (F (t + tab.c j * h) (Ys j).mat)‖ ≤ ε)
    (hγ : TruncBound Ys Yhs Yh Ynext h γ) :
    IsProjectedStep F tab.a tab.b tab.c ε γ t h Yk.mat (fun i => (Ys i).mat) Ynext.mat where
  first i hi := by simp only [step.first i hi]
  stage i hi := by
    obtain ⟨p, q, Uh, Vh, hU, hV, hY, -⟩ := step.stage i hi
    refine ⟨galerkinProj Uh Vh, fix_of_isOrthOf hU hV, fun j hj => ?_, ?_⟩
    · rw [one_sub_apply]
      exact (norm_sub_galerkin_le_of_isOrthOf hU hV hj).trans (hε j)
    · have hY' : galerkinProj Uh Vh (Yk.mat + h • ∑ j, tab.a i j • F (t + tab.c j * h) (Ys j).mat) =
          Yhs i := (galerkinProj_apply Uh Vh _).trans hY.symm
      rw [hY', norm_sub_rev]
      exact hγ.1 i hi
  final := by
    obtain ⟨p, q, Uh, Vh, hU, hV, hY, -⟩ := step.final
    refine ⟨galerkinProj Uh Vh, fix_of_isOrthOf hU hV, fun j hj => ?_, ?_⟩
    · rw [one_sub_apply]
      exact (norm_sub_galerkin_le_of_isOrthOf hU hV hj).trans (hε j)
    · have hY' : galerkinProj Uh Vh (Yk.mat + h • ∑ j, tab.b j • F (t + tab.c j * h) (Ys j).mat) =
          Yh := (galerkinProj_apply Uh Vh _).trans hY.symm
      rw [hY', norm_sub_rev]
      exact hγ.2

/-- **Lemma 4** of arXiv 2502.07040 for one step of Algorithm 2: if the tangent-projection defects
of the stages are `≤ ε` and the truncations `≤ h γ`, then `‖Y_{ki} - Z_{ki}‖ ≤ C_i h (ε + γ)`,
`Z_{ki}` the unprojected Runge–Kutta stages from `Y_k`, with the paper's `C_i`. -/
theorem IsRKBUGStep.stage_error (step : IsRKBUGStep F tab h t Yk Ys Yhs Yh Ynext) (hL : 0 ≤ L)
    (hLip : ∀ i Z₁ Z₂, ‖F (t + tab.c i * h) Z₁ - F (t + tab.c i * h) Z₂‖ ≤ L * ‖Z₁ - Z₂‖)
    (hh : 0 ≤ h) (hhh₀ : h ≤ h₀) (hε0 : 0 ≤ ε) (hγ0 : 0 ≤ γ)
    (hε : ∀ j, ‖F (t + tab.c j * h) (Ys j).mat -
      tangentProj (Ys j).U (Ys j).V (F (t + tab.c j * h) (Ys j).mat)‖ ≤ ε)
    (hγ : TruncBound Ys Yhs Yh Ynext h γ) (i : Fin s) :
    ‖(Ys i).mat - rkStage F tab.a tab.c t h Yk.mat i‖ ≤ stageConst tab.a L h₀ i * h * (ε + γ) :=
  stage_error_le tab.a_eq_zero hL hLip hh hhh₀ hε0 hγ0 (step.toProjected hε hγ) i

/-- **Theorem 1** of arXiv 2502.07040 for one step of Algorithm 2: if `Φ` is the value at `t + h`
of the exact flow from `Y_k` and the Runge–Kutta method has local error
`‖Z_{k+1} - Φ‖ ≤ C_L h^{p+1}` (Proposition 5 there, a hypothesis here), then
`‖Y_{k+1} - Φ‖ ≤ C h (ε + γ + h^p)` with `C = max {∑ |b_i| (1 + L C_i h₀), 1 + ∑ |b_i| L C_i h₀,
C_L}`. Conditional on Proposition 5 (the hypothesis `hRK`). -/
theorem IsRKBUGStep.local_error (step : IsRKBUGStep F tab h t Yk Ys Yhs Yh Ynext) (hL : 0 ≤ L)
    (hLip : ∀ i Z₁ Z₂, ‖F (t + tab.c i * h) Z₁ - F (t + tab.c i * h) Z₂‖ ≤ L * ‖Z₁ - Z₂‖)
    (hh : 0 ≤ h) (hhh₀ : h ≤ h₀) (hε0 : 0 ≤ ε) (hγ0 : 0 ≤ γ)
    (hε : ∀ j, ‖F (t + tab.c j * h) (Ys j).mat -
      tangentProj (Ys j).U (Ys j).V (F (t + tab.c j * h) (Ys j).mat)‖ ≤ ε)
    (hγ : TruncBound Ys Yhs Yh Ynext h γ) {Φ : Matrix (Fin n) (Fin m) ℝ} {CL : ℝ} {p : ℕ}
    (hRK : ‖rkResult F tab.a tab.b tab.c t h Yk.mat - Φ‖ ≤ CL * h ^ (p + 1)) :
    ‖Ynext.mat - Φ‖ ≤ localConst tab.a tab.b L h₀ CL * h * (ε + γ + h ^ p) := by
  have h1 := result_error_le tab.a_eq_zero hL hLip hh hhh₀ hε0 hγ0 (step.toProjected hε hγ)
  have hA : rowConst tab.a tab.b L h₀ ≤ localConst tab.a tab.b L h₀ CL := le_max_left _ _
  have hC : CL ≤ localConst tab.a tab.b L h₀ CL := le_max_right _ _
  have h2 : rowConst tab.a tab.b L h₀ * h * (ε + γ) ≤
      localConst tab.a tab.b L h₀ CL * h * (ε + γ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hh) (add_nonneg hε0 hγ0)
  have h3 : CL * h ^ (p + 1) ≤ localConst tab.a tab.b L h₀ CL * h ^ (p + 1) :=
    mul_le_mul_of_nonneg_right hC (pow_nonneg hh _)
  calc ‖Ynext.mat - Φ‖
      ≤ ‖Ynext.mat - rkResult F tab.a tab.b tab.c t h Yk.mat‖ +
        ‖rkResult F tab.a tab.b tab.c t h Yk.mat - Φ‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ localConst tab.a tab.b L h₀ CL * h * (ε + γ) +
        localConst tab.a tab.b L h₀ CL * h ^ (p + 1) := add_le_add (h1.trans h2) (hRK.trans h3)
    _ = localConst tab.a tab.b L h₀ CL * h * (ε + γ + h ^ p) := by ring

end Step

/-! ### Fan recursion and frozen fields -/

section Global

/-- The fan recursion of arXiv 2502.07040, Theorem 2: `e_{k+1} ≤ e^{L h} e_k + d` gives
`e_k ≤ e^{L k h} e₀ + d / (L h) (e^{L k h} - 1)`, the discrete form of
`∑_{k} h e^{L (N-k) h} ≤ (e^{L N h} - 1) / L`. -/
lemma fan_bound {u : ℕ → ℝ} {L h d δ : ℝ} {N : ℕ} (hL : 0 < L) (hh : 0 < h) (hd : 0 ≤ d)
    (h0 : u 0 ≤ δ) (hstep : ∀ k < N, u (k + 1) ≤ Real.exp (L * h) * u k + d) :
    ∀ k ≤ N, u k ≤ Real.exp (L * (k * h)) * δ + d / (L * h) * (Real.exp (L * (k * h)) - 1) := by
  intro k
  induction k with
  | zero => intro _; simpa using h0
  | succ k ih =>
    intro hk
    have hu := ih (by omega)
    have hLh : 0 < L * h := mul_pos hL hh
    set D := d / (L * h) with hD
    have hD0 : 0 ≤ D := div_nonneg hd hLh.le
    have hDL : D * (L * h) = d := div_mul_cancel₀ d hLh.ne'
    have hexp : Real.exp (L * ((k + 1 : ℕ) * h)) = Real.exp (L * h) * Real.exp (L * (k * h)) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    have hEh : L * h ≤ Real.exp (L * h) - 1 := by linarith [Real.add_one_le_exp (L * h)]
    have hmul := mul_le_mul_of_nonneg_left hEh hD0
    have hpos : 0 < Real.exp (L * h) := Real.exp_pos _
    have h1 := mul_le_mul_of_nonneg_left hu hpos.le
    have h2 := hstep k (by omega)
    rw [hexp]
    nlinarith

/-- `F` frozen outside `[0, T]`, so that a field which is Lipschitz only on `[0, T]` (Assumption 1
of arXiv 2502.07040) can be used with the library's results for fields Lipschitz for all times. -/
def clampField {E : Type*} (F : ℝ → E → E) (T : ℝ) : ℝ → E → E :=
  fun t x => F (max 0 (min t T)) x

lemma clampField_of_mem {E : Type*} {F : ℝ → E → E} {T t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : E) :
    clampField F T t x = F t x := by
  simp [clampField, min_eq_left ht.2, max_eq_right ht.1]

lemma isLipschitzField_clampField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E → E} {T L : ℝ} (hT : 0 ≤ T)
    (hF : ∀ t ∈ Icc (0 : ℝ) T, ∀ x y, ‖F t x - F t y‖ ≤ L * ‖x - y‖) :
    IsLipschitzField (clampField F T) L :=
  fun _ x y => hF _ ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩ x y

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- On `[a, b] ⊆ [0, T]`, solutions of `F` are solutions of the frozen field. -/
lemma solution_clamp {F : ℝ → E → E} {T a b : ℝ} {y : ℝ → E} (ha : 0 ≤ a) (hb : b ≤ T)
    (hy : ODESolution F y a b) : ODESolution (clampField F T) y a b where
  cont := hy.cont
  deriv t ht := by
    rw [clampField_of_mem ⟨ha.trans ht.1, ht.2.le.trans hb⟩]
    exact hy.deriv t ht

/-- On `[a, b] ⊆ [0, T]`, solutions of the frozen field are solutions of `F`. -/
lemma solution_unclamp {F : ℝ → E → E} {T a b : ℝ} {y : ℝ → E} (ha : 0 ≤ a) (hb : b ≤ T)
    (hy : ODESolution (clampField F T) y a b) : ODESolution F y a b where
  cont := hy.cont
  deriv t ht := by
    rw [← clampField_of_mem (F := F) ⟨ha.trans ht.1, ht.2.le.trans hb⟩]
    exact hy.deriv t ht

end Global

/-! ### The projection error `ε_r` and the integrator on `[0, T]` -/

section Run

variable {n m r s : ℕ}

/-- The projection error
`ε_r = sup_{t ∈ [0, T]} sup_{Z ∈ 𝒱} ‖F(t, Z) - P_Z(F(t, Z))‖_F` of arXiv 2502.07040, Sec. 3.2,
for `𝒱 = V_r`.  `P_Z` is computed from an orthonormal factorisation `Z = U S Vᵀ` (`LowRank`); for
rank exactly `r` it does not depend on it, and otherwise the supremum runs over all of them. -/
noncomputable def epsR (r : ℕ) (F : ℝ → Matrix (Fin n) (Fin m) ℝ → Matrix (Fin n) (Fin m) ℝ)
    (T : ℝ) (𝒱 : Set (Matrix (Fin n) (Fin m) ℝ)) : ℝ :=
  sSup {e : ℝ | ∃ t ∈ Icc (0 : ℝ) T, ∃ Z : LowRank n m r, Z.mat ∈ 𝒱 ∧
    e = ‖F t Z.mat - tangentProj Z.U Z.V (F t Z.mat)‖}

/-- The classical local error of the Runge–Kutta method on `𝒱` (arXiv 2502.07040, Proposition 5,
which cites the order theory of Hairer–Nørsett–Wanner): for every `t ∈ [0, T - h]`, `Z ∈ 𝒱` and
solution `φ` of `Ẋ = F(t, X)` on `[t, t + h]` with `φ t = Z`, the Runge–Kutta step from `Z` is
within `C_L h^{p+1}` of `φ (t + h)`. -/
def IsRKLocalError (F : ℝ → Matrix (Fin n) (Fin m) ℝ → Matrix (Fin n) (Fin m) ℝ)
    (tab : ExplicitRK s) (p : ℕ) (CL h T : ℝ) (𝒱 : Set (Matrix (Fin n) (Fin m) ℝ)) : Prop :=
  ∀ t, 0 ≤ t → t + h ≤ T → ∀ Z ∈ 𝒱, ∀ φ : ℝ → Matrix (Fin n) (Fin m) ℝ,
    ODESolution F φ t (t + h) → φ t = Z →
      ‖rkResult F tab.a tab.b tab.c t h Z - φ (t + h)‖ ≤ CL * h ^ (p + 1)

/-- The constant `C' = max {e^{L T}, C (e^{L T} - 1) / L}` of arXiv 2502.07040, Theorem 2. -/
noncomputable def globalConst (tab : ExplicitRK s) (L T h₀ CL : ℝ) : ℝ :=
  max (Real.exp (L * T)) (localConst tab.a tab.b L h₀ CL * (Real.exp (L * T) - 1) / L)

/-- A run of Algorithm 2 on `[0, N h] ⊆ [0, T]` under the assumptions of arXiv 2502.07040, Sec. 3:
Assumption 1, `s > 0` stages with nodes in `[0, 1]`, `0 < h ≤ h₀`. -/
structure IsRKBUGRun (F : ℝ → Matrix (Fin n) (Fin m) ℝ → Matrix (Fin n) (Fin m) ℝ)
    (tab : ExplicitRK s) (L T h₀ h : ℝ) (N : ℕ) (Y : ℕ → LowRank n m r)
    (Ys : ℕ → Fin s → LowRank n m r) (Yhs : ℕ → Fin s → Matrix (Fin n) (Fin m) ℝ)
    (Yh : ℕ → Matrix (Fin n) (Fin m) ℝ) : Prop where
  stages_pos : 0 < s
  assumption1 : Assumption1 F L T
  nodes : ∀ i, 0 ≤ tab.c i ∧ tab.c i ≤ 1
  h_pos : 0 < h
  h_le : h ≤ h₀
  time : (N : ℝ) * h ≤ T
  sol : IsRKBUGSolution F tab h N Y Ys Yhs Yh

variable {F : ℝ → Matrix (Fin n) (Fin m) ℝ → Matrix (Fin n) (Fin m) ℝ} {L T h₀ h : ℝ}
  {tab : ExplicitRK s} {N : ℕ} {Y : ℕ → LowRank n m r} {Ys : ℕ → Fin s → LowRank n m r}
  {Yhs : ℕ → Fin s → Matrix (Fin n) (Fin m) ℝ} {Yh : ℕ → Matrix (Fin n) (Fin m) ℝ}

/-- `ε_r` bounds every defect in `𝒱 ⊆ V_r`: the supremum is finite, since `V_r` is bounded, `F`
is Lipschitz in the state and continuous in time. -/
theorem le_epsR (hA : Assumption1 F L T) {𝒱 : Set (Matrix (Fin n) (Fin m) ℝ)}
    {Z₀ : Matrix (Fin n) (Fin m) ℝ} {R : ℝ} (hsub : 𝒱 ⊆ nbhdV Z₀ R r) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) (Z : LowRank n m r) (hZ : Z.mat ∈ 𝒱) :
    ‖F t Z.mat - tangentProj Z.U Z.V (F t Z.mat)‖ ≤ epsR r F T 𝒱 := by
  refine le_csSup ⟨supF F T Z₀ + L * R, ?_⟩ ⟨t, ht, Z, hZ, rfl⟩
  rintro e ⟨t', ht', Z', hZ', rfl⟩
  have h1 := (isOrthProj_tangentProj Z'.U_orth Z'.V_orth).norm_sub_le (F t' Z'.mat)
  have h2 := norm_F_le (hA.lip t' ht') Z'.mat Z₀
  have h3 := mul_le_mul_of_nonneg_left (hsub hZ').2 hA.pos.le
  have h4 := norm_le_supF hA Z₀ ht'
  linarith

lemma epsR_nonneg (r : ℕ) (F : ℝ → Matrix (Fin n) (Fin m) ℝ → Matrix (Fin n) (Fin m) ℝ) (T : ℝ)
    (𝒱 : Set (Matrix (Fin n) (Fin m) ℝ)) : 0 ≤ epsR r F T 𝒱 := by
  refine Real.sSup_nonneg ?_
  rintro e ⟨_, _, _, _, rfl⟩
  exact norm_nonneg _

/-- `ε_r` vanishes at full rank, `r ≥ min {n, m}` (arXiv 2502.07040, Sec. 3.2): the tangent
projector is then the identity. -/
theorem epsR_eq_zero_of_full (hr : min n m ≤ r)
    (F : ℝ → Matrix (Fin n) (Fin m) ℝ → Matrix (Fin n) (Fin m) ℝ) (T : ℝ)
    (𝒱 : Set (Matrix (Fin n) (Fin m) ℝ)) : epsR r F T 𝒱 = 0 := by
  refine le_antisymm (Real.sSup_le ?_ le_rfl) (epsR_nonneg _ _ _ _)
  rintro e ⟨t, -, Z, -, rfl⟩
  have hrn : r ≤ n := Z.le_left
  have hrm : r ≤ m := Z.le_right
  rw [tangentProj_apply]
  rcases le_total n m with hnm | hnm
  · have hrn' : r = n := le_antisymm hrn (by rwa [min_eq_left hnm] at hr)
    have e₁ : Fin r ≃ Fin n := finCongr hrn'
    have hUU : Z.U * Z.Uᵀ = 1 := (Matrix.mul_eq_one_comm_of_equiv e₁).mp Z.U_orth
    simp only [hUU, Matrix.one_mul, Matrix.mul_assoc]
    simp
  · have hrm' : r = m := le_antisymm hrm (by rwa [min_eq_right hnm] at hr)
    have e₁ : Fin r ≃ Fin m := finCongr hrm'
    have hVV : Z.V * Z.Vᵀ = 1 := (Matrix.mul_eq_one_comm_of_equiv e₁).mp Z.V_orth
    simp only [Matrix.mul_assoc, hVV, Matrix.mul_one]
    simp

/-- `γ̄_r ≥ 0` for `B ≥ 0`. -/
lemma gammaBar_nonneg (tab : ExplicitRK s) (B : ℝ) (hB : 0 ≤ B) : 0 ≤ gammaBar tab n m r B := by
  have hCb : 0 ≤ tab.Cb := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hmax : 0 ≤ max tab.Cb (⨆ i, tab.Ca i) := le_max_of_le_left hCb
  exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hmax) hB

namespace IsRKBUGRun

variable (hR : IsRKBUGRun F tab L T h₀ h N Y Ys Yhs Yh) {𝒱 : Set (Matrix (Fin n) (Fin m) ℝ)}
  {R γ CL : ℝ} {p : ℕ}
include hR

lemma T_nonneg : 0 ≤ T :=
  (mul_nonneg (Nat.cast_nonneg N) hR.h_pos.le).trans hR.time

lemma h₀_nonneg : 0 ≤ h₀ := hR.h_pos.le.trans hR.h_le

lemma stage_time {k : ℕ} (hk : k < N) (i : Fin s) : (k : ℝ) * h + tab.c i * h ∈ Icc 0 T :=
  time_mem hR.nodes hR.h_pos.le hR.time hk i

lemma lipschitz_stage {k : ℕ} (hk : k < N) (i : Fin s) (Z₁ Z₂ : Matrix (Fin n) (Fin m) ℝ) :
    ‖F ((k : ℝ) * h + tab.c i * h) Z₁ - F ((k : ℝ) * h + tab.c i * h) Z₂‖ ≤ L * ‖Z₁ - Z₂‖ :=
  hR.assumption1.lip _ (hR.stage_time hk i) Z₁ Z₂

lemma step_time {k : ℕ} (hk : k < N) : (k : ℝ) * h + h ≤ N * h := by
  have hk' : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
  have := mul_le_mul_of_nonneg_right hk' hR.h_pos.le
  linarith

lemma step_nonneg (k : ℕ) : 0 ≤ (k : ℝ) * h := mul_nonneg (Nat.cast_nonneg k) hR.h_pos.le

/-- The iterates `Y_k`, `k < N`, lie in every set containing the stages (the first stage is
`Y_k`). -/
theorem iterate_mem (h𝒱 : ∀ k < N, ∀ i, (Ys k i).mat ∈ 𝒱) {k : ℕ} (hk : k < N) :
    (Y k).mat ∈ 𝒱 := by
  have := h𝒱 k hk ⟨0, hR.stages_pos⟩
  rwa [(hR.sol k hk).first ⟨0, hR.stages_pos⟩ rfl] at this

/-- Along the run the tangent-projection defects of the stages are bounded by `ε_r`. -/
theorem defect_le (h𝒱 : ∀ k < N, ∀ i, (Ys k i).mat ∈ 𝒱)
    (hsub : 𝒱 ⊆ nbhdV (Y 0).mat R r) {k : ℕ} (hk : k < N) (i : Fin s) :
    ‖F ((k : ℝ) * h + tab.c i * h) (Ys k i).mat - tangentProj (Ys k i).U (Ys k i).V
      (F ((k : ℝ) * h + tab.c i * h) (Ys k i).mat)‖ ≤ epsR r F T 𝒱 :=
  le_epsR hR.assumption1 hsub (hR.stage_time hk i) (Ys k i) (h𝒱 k hk i)

/-- **Lemma 4** of arXiv 2502.07040 (stage error): for `h ≤ h₀`, the stages of each step satisfy
`‖Y_{ki} - Z_{ki}‖ ≤ C_i h (ε_r + γ)`, with `Z_{ki}` the unprojected Runge–Kutta stages from `Y_k`
and the paper's `C₁ = 0`,
`C_i = max {∑_{j<i} |a_{ij}| (1 + L C_j h₀), 1 + ∑_{j<i} |a_{ij}| L C_j h₀}`.
Here `𝒱 ⊆ V_r` contains the stages and `γ` bounds the truncation errors. -/
theorem stage_error (h𝒱 : ∀ k < N, ∀ i, (Ys k i).mat ∈ 𝒱) (hsub : 𝒱 ⊆ nbhdV (Y 0).mat R r)
    (hγ0 : 0 ≤ γ) (hγ : ∀ k < N, TruncBound (Ys k) (Yhs k) (Yh k) (Y (k + 1)) h γ) {k : ℕ}
    (hk : k < N) (i : Fin s) :
    ‖(Ys k i).mat - rkStage F tab.a tab.c (k * h) h (Y k).mat i‖ ≤
      stageConst tab.a L h₀ i * h * (epsR r F T 𝒱 + γ) :=
  (hR.sol k hk).stage_error hR.assumption1.pos.le (hR.lipschitz_stage hk) hR.h_pos.le hR.h_le
    (epsR_nonneg _ _ _ _) hγ0 (hR.defect_le h𝒱 hsub hk) (hγ k hk) i

/-- **Theorem 1** of arXiv 2502.07040 (local error): for `h ≤ h₀`, if `φ` solves `Ẋ = F(t, X)` on
`[t_k, t_{k+1}]` with `φ(t_k) = Y_k`, then `‖Y_{k+1} - φ(t_{k+1})‖ ≤ C h (ε_r + γ + h^p)` with the
paper's `C = max {∑ |b_i| (1 + L C_i h₀), 1 + ∑ |b_i| L C_i h₀, C_L}`.  Conditional on
Proposition 5, which is the hypothesis `IsRKLocalError` on `𝒱`. -/
theorem local_error (h𝒱 : ∀ k < N, ∀ i, (Ys k i).mat ∈ 𝒱) (hsub : 𝒱 ⊆ nbhdV (Y 0).mat R r)
    (hγ0 : 0 ≤ γ) (hγ : ∀ k < N, TruncBound (Ys k) (Yhs k) (Yh k) (Y (k + 1)) h γ)
    (hRK : IsRKLocalError F tab p CL h T 𝒱) {k : ℕ} (hk : k < N)
    {φ : ℝ → Matrix (Fin n) (Fin m) ℝ} (hφ : ODESolution F φ (k * h) (k * h + h))
    (hφ0 : φ (k * h) = (Y k).mat) :
    ‖(Y (k + 1)).mat - φ (k * h + h)‖ ≤
      localConst tab.a tab.b L h₀ CL * h * (epsR r F T 𝒱 + γ + h ^ p) :=
  (hR.sol k hk).local_error hR.assumption1.pos.le (hR.lipschitz_stage hk) hR.h_pos.le hR.h_le
    (epsR_nonneg _ _ _ _) hγ0 (hR.defect_le h𝒱 hsub hk) (hγ k hk)
    (hRK _ (hR.step_nonneg k) ((hR.step_time hk).trans hR.time) _ (hR.iterate_mem h𝒱 hk) φ hφ
      hφ0)

/-- The exact flow over one step exists: `F` is Lipschitz and continuous in time, so `Ẋ = F(t, X)`
has a solution on `[t_k, t_{k+1}]` from every starting value. -/
lemma exists_flow {k : ℕ} (hk : k < N) (Z : Matrix (Fin n) (Fin m) ℝ) :
    ∃ φ : ℝ → Matrix (Fin n) (Fin m) ℝ, ODESolution F φ (k * h) (k * h + h) ∧ φ (k * h) = Z := by
  have hk0 := hR.step_nonneg k
  have hkT := (hR.step_time hk).trans hR.time
  have hsub : Icc ((k : ℝ) * h) (k * h + h) ⊆ Icc 0 T := Icc_subset_Icc hk0 hkT
  obtain ⟨φ, hφ, hφ0⟩ := exists_ODESolution_of_linearGrowth (F := clampField F T)
    (K := supF F T 0) (isLipschitzField_clampField hR.T_nonneg hR.assumption1.lip)
    hR.assumption1.pos.le
    (fun t ht => by
      rw [clampField_of_mem (hsub ht)]
      exact norm_le_supF hR.assumption1 0 (hsub ht))
    (fun x => ((hR.assumption1.cont x).mono hsub).congr fun t ht => clampField_of_mem (hsub ht) x)
    (by linarith [hR.h_pos]) Z
  exact ⟨φ, solution_unclamp hk0 hkT hφ, hφ0⟩

/-- **Theorem 2** of arXiv 2502.07040 (global error), with the paper's constant:
`‖X(t_N) - Y_N‖ ≤ C' (δ_r + ε_r + γ + h^p)`, `δ_r = ‖X₀ - Y₀‖`,
`C' = max {e^{L T}, C (e^{L T} - 1) / L}`, for `N h ≤ T` and `h ≤ h₀`.  Here `ε_r` is the
supremum over any `𝒱 ⊆ V_r` containing the stages and `γ` bounds the truncation errors.
Conditional on Proposition 5, which is the hypothesis `hRK`.  The exact flows from the iterates are
constructed. -/
theorem global_error (h𝒱 : ∀ k < N, ∀ i, (Ys k i).mat ∈ 𝒱) (hsub : 𝒱 ⊆ nbhdV (Y 0).mat R r)
    (hγ0 : 0 ≤ γ) (hγ : ∀ k < N, TruncBound (Ys k) (Yhs k) (Yh k) (Y (k + 1)) h γ)
    (hRK : IsRKLocalError F tab p CL h T 𝒱) {X : ℝ → Matrix (Fin n) (Fin m) ℝ}
    (hX : ODESolution F X 0 (N * h)) :
    ‖X (N * h) - (Y N).mat‖ ≤ globalConst tab L T h₀ CL *
      (‖X 0 - (Y 0).mat‖ + epsR r F T 𝒱 + γ + h ^ p) := by
  have hL := hR.assumption1.pos
  have hh := hR.h_pos
  have hT := hR.T_nonneg
  have hC1 := one_le_localConst tab.a tab.b hL.le hR.h₀_nonneg CL
  set ε := epsR r F T 𝒱 with hε
  set C := localConst tab.a tab.b L h₀ CL with hC
  set Q := ε + γ + h ^ p with hQ
  set δ := ‖X 0 - (Y 0).mat‖ with hδ
  have hQ0 : 0 ≤ Q := add_nonneg (add_nonneg (epsR_nonneg _ _ _ _) hγ0) (pow_nonneg hh.le p)
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hd0 : 0 ≤ C * h * Q := by positivity
  have hstep : ∀ k < N, ‖(Y (k + 1)).mat - X ((k + 1 : ℕ) * h)‖ ≤
      Real.exp (L * h) * ‖(Y k).mat - X (k * h)‖ + C * h * Q := by
    intro k hk
    have hk0 := hR.step_nonneg k
    have hkN := hR.step_time hk
    have hkT := hkN.trans hR.time
    have hab : (k : ℝ) * h ≤ k * h + h := by linarith
    obtain ⟨φ, hφ, hφ0⟩ := hR.exists_flow hk (Y k).mat
    have hloc := hR.local_error h𝒱 hsub hγ0 hγ hRK hk hφ hφ0
    have hXk : ODESolution F X (k * h) (k * h + h) := hX.mono hk0 hkN
    have hflow := ODESolution.norm_sub_le_exp
      (isLipschitzField_clampField hT hR.assumption1.lip) hL.le (solution_clamp hk0 hkT hφ)
      (solution_clamp hk0 hkT hXk) (k * h + h) ⟨hab, le_rfl⟩
    have hsub' : (k : ℝ) * h + h - k * h = h := by ring
    rw [hsub', hφ0] at hflow
    have hcast : (((k + 1 : ℕ) : ℝ)) * h = k * h + h := by
      push_cast
      ring
    rw [hcast]
    calc ‖(Y (k + 1)).mat - X (k * h + h)‖
        ≤ ‖(Y (k + 1)).mat - φ (k * h + h)‖ + ‖φ (k * h + h) - X (k * h + h)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := by linarith
  have h0 : ‖(Y 0).mat - X (((0 : ℕ) : ℝ) * h)‖ ≤ δ := by
    rw [hδ, norm_sub_rev]
    simp
  have hfan := fan_bound (u := fun k => ‖(Y k).mat - X (k * h)‖) hL hh hd0 h0 hstep N le_rfl
  have hLT : Real.exp (L * (N * h)) ≤ Real.exp (L * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hR.time hL.le)
  have hD : C * h * Q / (L * h) = C * Q / L := by
    field_simp
  have hmain : ‖(Y N).mat - X (N * h)‖ ≤
      Real.exp (L * T) * δ + C * (Real.exp (L * T) - 1) / L * Q := by
    have hCQ : 0 ≤ C * Q / L := by positivity
    have h1 := mul_le_mul_of_nonneg_right hLT hδ0
    have h2 : C * Q / L * (Real.exp (L * (N * h)) - 1) ≤ C * Q / L * (Real.exp (L * T) - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hCQ
    have h3 : C * Q / L * (Real.exp (L * T) - 1) = C * (Real.exp (L * T) - 1) / L * Q := by ring
    have h4 := hfan
    rw [hD] at h4
    linarith
  have hA : Real.exp (L * T) ≤ globalConst tab L T h₀ CL := le_max_left _ _
  have hB : C * (Real.exp (L * T) - 1) / L ≤ globalConst tab L T h₀ CL := le_max_right _ _
  rw [norm_sub_rev]
  calc ‖(Y N).mat - X (N * h)‖
      ≤ Real.exp (L * T) * δ + C * (Real.exp (L * T) - 1) / L * Q := hmain
    _ ≤ globalConst tab L T h₀ CL * δ + globalConst tab L T h₀ CL * Q :=
        add_le_add (mul_le_mul_of_nonneg_right hA hδ0) (mul_le_mul_of_nonneg_right hB hQ0)
    _ = globalConst tab L T h₀ CL * (δ + ε + γ + h ^ p) := by
        rw [hQ]
        ring

/-- The truncation bound of Proposition 4 (`truncation_error_gamma`) in the form `TruncBound`. -/
theorem truncBound_gammaBar {k : ℕ} (hk : k < N) :
    TruncBound (Ys k) (Yhs k) (Yh k) (Y (k + 1)) h (gammaBar tab n m r
      (boundB F T (Y 0).mat (max (R₁ F L T (Y 0).mat) (R₂ tab F L T h₀ (Y 0).mat)) r)) := by
  obtain ⟨h1, h2⟩ := truncation_error_gamma hR.stages_pos hR.assumption1 hR.nodes hR.h_pos.le
    hR.h_le hR.time hR.sol hk
  exact ⟨h2, h1⟩

/-- **Theorem 2** of arXiv 2502.07040 with all the paper's quantities: `V_r` of radius
`max {R₁, R₂}` (rank `≤ r`, see the module docstring), `ε_r` the supremum over `V_r`, and `γ̄_r` of
Proposition 4 for `γ_r`:
`‖X(t_N) - Y_N‖ ≤ C' (δ_r + ε_r + γ̄_r + h^p)`, `C' = max {e^{L T}, C (e^{L T} - 1) / L}`.
Conditional on Proposition 5, which is the hypothesis `hRK`. -/
theorem global_error_paper
    (hRK : IsRKLocalError F tab p CL h T
      (nbhdV (Y 0).mat (max (R₁ F L T (Y 0).mat) (R₂ tab F L T h₀ (Y 0).mat)) r))
    {X : ℝ → Matrix (Fin n) (Fin m) ℝ} (hX : ODESolution F X 0 (N * h)) :
    ‖X (N * h) - (Y N).mat‖ ≤ globalConst tab L T h₀ CL *
      (‖X 0 - (Y 0).mat‖ +
        epsR r F T (nbhdV (Y 0).mat (max (R₁ F L T (Y 0).mat) (R₂ tab F L T h₀ (Y 0).mat)) r) +
        gammaBar tab n m r
          (boundB F T (Y 0).mat (max (R₁ F L T (Y 0).mat) (R₂ tab F L T h₀ (Y 0).mat)) r) +
        h ^ p) := by
  refine hR.global_error (fun k hk i => ?_) subset_rfl (gammaBar_nonneg tab _ boundB_nonneg)
    (fun k hk => hR.truncBound_gammaBar hk) hRK hX
  have := stage_mem_nbhdV hR.assumption1 hR.nodes hR.h_pos.le hR.h_le hR.time hR.sol hk i
  exact ⟨this.1, this.2.trans (le_max_right _ _)⟩

/-- **Theorem 2** of arXiv 2502.07040 with the paper's manifold `M_r` of rank exactly `r`: if all
stages have rank `r` (which the paper tacitly assumes), `ε_r` may be taken over
`V_r ∩ M_r`, for every radius `R ≥ R₂`. Conditional on Proposition 5 (the hypothesis `hRK`). -/
theorem global_error_rank_eq (hrank : ∀ k < N, ∀ i, (Ys k i).mat.rank = r)
    (hR₂ : R₂ tab F L T h₀ (Y 0).mat ≤ R) (hγ0 : 0 ≤ γ)
    (hγ : ∀ k < N, TruncBound (Ys k) (Yhs k) (Yh k) (Y (k + 1)) h γ)
    (hRK : IsRKLocalError F tab p CL h T {Z | Z ∈ nbhdV (Y 0).mat R r ∧ Z.rank = r})
    {X : ℝ → Matrix (Fin n) (Fin m) ℝ} (hX : ODESolution F X 0 (N * h)) :
    ‖X (N * h) - (Y N).mat‖ ≤ globalConst tab L T h₀ CL *
      (‖X 0 - (Y 0).mat‖ + epsR r F T {Z | Z ∈ nbhdV (Y 0).mat R r ∧ Z.rank = r} + γ +
        h ^ p) := by
  refine hR.global_error (𝒱 := {Z | Z ∈ nbhdV (Y 0).mat R r ∧ Z.rank = r}) (R := R)
    (fun k hk i => ⟨?_, hrank k hk i⟩) (fun _ hZ => hZ.1) hγ0 hγ hRK hX
  have := stage_mem_nbhdV hR.assumption1 hR.nodes hR.h_pos.le hR.h_le hR.time hR.sol hk i
  exact ⟨this.1, this.2.trans hR₂⟩

/-- **Remark 2** of arXiv 2502.07040 at full rank: for `r ≥ min {n, m}` the projection error and
`γ̄_r` vanish and `‖X(t_N) - Y_N‖ ≤ C' (δ_r + h^p)`: the integrator has the order of the
Runge–Kutta method. Conditional on Proposition 5 (the hypothesis `hRK`). -/
theorem global_error_full_rank (hr : min n m ≤ r)
    (hRK : IsRKLocalError F tab p CL h T
      (nbhdV (Y 0).mat (max (R₁ F L T (Y 0).mat) (R₂ tab F L T h₀ (Y 0).mat)) r))
    {X : ℝ → Matrix (Fin n) (Fin m) ℝ} (hX : ODESolution F X 0 (N * h)) :
    ‖X (N * h) - (Y N).mat‖ ≤ globalConst tab L T h₀ CL * (‖X 0 - (Y 0).mat‖ + h ^ p) := by
  have := hR.global_error_paper hRK hX
  rwa [epsR_eq_zero_of_full hr, gammaBar_eq_zero tab _ hr, add_zero, add_zero] at this

end IsRKBUGRun

end Run

/-! ### Non-vacuity: Proposition 5 for explicit Euler, and all hypotheses at once -/

section Euler

variable {n m r : ℕ}

/-- The explicit Euler tableau `a = 0`, `b = 1`, `c = 0`. -/
def eulerTab : ExplicitRK 1 := ⟨fun _ _ => 0, fun _ => 1, fun _ => 0, fun _ _ _ => rfl⟩

/-- **The hypothesis `IsRKLocalError` (Proposition 5 of arXiv 2502.07040) holds for explicit Euler**
(order `p = 1`) and an autonomous bounded `L`-Lipschitz field `G`, with `C_L = L B`, on all of
`ℝ^{n × m}`.  This is an instance, not the general order theory. -/
theorem isRKLocalError_euler {G : Matrix (Fin n) (Fin m) ℝ → Matrix (Fin n) (Fin m) ℝ}
    {L B h T : ℝ} (hL : 0 ≤ L) (hG : ∀ X Y, ‖G X - G Y‖ ≤ L * ‖X - Y‖) (hB : ∀ X, ‖G X‖ ≤ B)
    (hh : 0 ≤ h) (𝒱 : Set (Matrix (Fin n) (Fin m) ℝ)) :
    IsRKLocalError (fun _ => G) eulerTab 1 (L * B) h T 𝒱 := by
  intro t _ _ Z _ φ hφ hφ0
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hres : rkResult (fun _ => G) eulerTab.a eulerTab.b eulerTab.c t h Z = Z + h • G Z := by
    have hst : rkStage (fun _ => G) eulerTab.a eulerTab.c t h Z 0 = Z := by
      rw [rkStage_eq eulerTab.a_eq_zero]
      simp [eulerTab]
    rw [rkResult, Fin.sum_univ_one, hst]
    simp [eulerTab]
  have hmove := hφ.norm_sub_le (B := B) fun s _ => hB _
  let g : ℝ → Matrix (Fin n) (Fin m) ℝ := fun s => φ s - (s - t) • G Z
  have hg : ODESolution (fun s _ => G (φ s) - G Z) g t (t + h) :=
    { cont := hφ.cont.sub (((continuous_id.sub continuous_const).smul
        continuous_const).continuousOn)
      deriv := fun s hs => by
        have h1 : HasDerivWithinAt (fun s : ℝ => (s - t) • G Z) ((1 : ℝ) • G Z) (Ici s) s :=
          (((hasDerivAt_id s).sub_const t).smul_const (G Z)).hasDerivWithinAt
        have h2 := (hφ.deriv s hs).sub h1
        rwa [one_smul] at h2 }
  have hbound := hg.norm_sub_le (B := L * B * h) (fun s hs => by
    have h1 := hmove s (Ico_subset_Icc_self hs)
    rw [hφ0] at h1
    have h2 : B * (s - t) ≤ B * h := mul_le_mul_of_nonneg_left (by linarith [hs.2]) hB0
    calc ‖G (φ s) - G Z‖ ≤ L * ‖φ s - Z‖ := hG _ _
      _ ≤ L * (B * h) := mul_le_mul_of_nonneg_left (h1.trans h2) hL
      _ = L * B * h := by ring) (t + h) ⟨by linarith, le_rfl⟩
  have hg0 : g t = Z := by simp [g, hφ0]
  have hgh : g (t + h) = φ (t + h) - h • G Z := by simp [g]
  rw [hres, norm_sub_rev]
  have heq : φ (t + h) - (Z + h • G Z) = g (t + h) - g t := by
    rw [hg0, hgh]
    abel
  rw [heq]
  calc ‖g (t + h) - g t‖ ≤ L * B * h * (t + h - t) := hbound
    _ = L * B * h ^ (1 + 1) := by ring

/-- **All hypotheses of Theorem 2 of arXiv 2502.07040 hold at once** (non-vacuity): for explicit
Euler, any bounded `L`-Lipschitz autonomous field with `L > 0`, `0 < h`, `N h ≤ T` and any initial
value, Algorithm 2 has a run (`exists_rkbug_solution`) satisfying `IsRKBUGRun`, and its error obeys
`global_error_paper` with `p = 1`, `C_L = L B`. -/
theorem euler_instance {G : Matrix (Fin n) (Fin m) ℝ → Matrix (Fin n) (Fin m) ℝ} {L B T h : ℝ}
    {N : ℕ} (hL : 0 < L) (hG : ∀ X Y, ‖G X - G Y‖ ≤ L * ‖X - Y‖) (hB : ∀ X, ‖G X‖ ≤ B)
    (hh : 0 < h) (hT : (N : ℝ) * h ≤ T) (Y₀ : LowRank n m r) :
    ∃ (Y : ℕ → LowRank n m r) (Ys : ℕ → Fin 1 → LowRank n m r)
      (Yhs : ℕ → Fin 1 → Matrix (Fin n) (Fin m) ℝ) (Yh : ℕ → Matrix (Fin n) (Fin m) ℝ),
      Y 0 = Y₀ ∧ IsRKBUGRun (fun _ => G) eulerTab L T h h N Y Ys Yhs Yh ∧
      ∀ X : ℝ → Matrix (Fin n) (Fin m) ℝ, ODESolution (fun _ => G) X 0 (N * h) →
        ‖X (N * h) - (Y N).mat‖ ≤ globalConst eulerTab L T h (L * B) *
          (‖X 0 - (Y 0).mat‖ + epsR r (fun _ => G) T (nbhdV (Y 0).mat
            (max (R₁ (fun _ => G) L T (Y 0).mat) (R₂ eulerTab (fun _ => G) L T h (Y 0).mat)) r) +
          gammaBar eulerTab n m r (boundB (fun _ => G) T (Y 0).mat
            (max (R₁ (fun _ => G) L T (Y 0).mat) (R₂ eulerTab (fun _ => G) L T h (Y 0).mat)) r) +
          h ^ 1) := by
  obtain ⟨Y, Ys, Yhs, Yh, hY0, hsol⟩ := exists_rkbug_solution (fun _ => G) eulerTab h N Y₀
  have hR : IsRKBUGRun (fun _ => G) eulerTab L T h h N Y Ys Yhs Yh :=
    ⟨Nat.one_pos, ⟨hL, fun _ => continuousOn_const, fun _ _ X Y => hG X Y⟩,
      fun _ => ⟨le_rfl, zero_le_one⟩, hh, le_rfl, hT, hsol⟩
  exact ⟨Y, Ys, Yhs, Yh, hY0, hR, fun X hX =>
    hR.global_error_paper (isRKLocalError_euler hL.le hG hB hh.le _) hX⟩

end Euler

end LeanDLRA.Literature.P2502_07040
