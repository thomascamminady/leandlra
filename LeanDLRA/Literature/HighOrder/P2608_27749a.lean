import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.HighOrder.RungeKuttaBUG

/-!
# Results of arXiv 2608.27749: High-order robust BUG integrators (basis consistency, Lemma 2)

Property P2 of the BUG-p bases (Sec. 3.1) and the argument of Lemma 2 in an abstract form:
if the product projector `P Q` (`P = U Uᵀ ·`, `Q = · V Vᵀ`) fixes the starting value and the
stage derivatives of a full Runge–Kutta step, then it fixes the Runge–Kutta result, and therefore
captures the exact solution at least as well as that result does
(`‖A − P Q A‖ ≤ ‖A − Y_RK‖`, the paper's argument gives the constant `2`).  The results are
**conditional on** a local error bound for the Runge–Kutta step (hypothesis `hK`; the paper cites
[24, Theorem 6]).

**Difference from Lemma 2 of the paper.**  The paper compares with the *projected* Runge–Kutta
result `Y_PRK = Yₙ + h ∑ bᵢ Z̄ᵢ`, `Z̄ᵢ = P(Y₍ᵢ₎) F₍ᵢ₎` at the truncated stages `Y₍ᵢ₎`, and its bases
(10a)–(10b) fix the `Z̄ᵢ` (by Lemma 1).  Here the comparison is with the *full* Runge–Kutta step,
and the projector must fix the full stage derivatives `F(t + cᵢ h, Zᵢ)`, which the bases
(10a)–(10b) need not do.  So the theorems below have the structure of Lemma 2 but do not apply
verbatim to the paper's bases.

Abstract counterparts of Sec. 3.1 (P1–P2 ⇒ local and global error), of Lemma 1 (stage span) and
of Remark 2 are in the library (`RungeKuttaBUG.bugP_local_error`, `bugP_global_error`,
`rk_stage_mem`, `rk_result_mem`, `galerkinRK_stage_mem_of_nested`, `norm_bestTrunc_sub_le`); they
take capture estimates as hypotheses and are not Theorem 1 as printed.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2608_27749

open LeanDLRA RungeKuttaBUG

/-- **Lemma 2 (consistency P2 for RK bases), abstract core** (after arXiv 2608.27749, Lemma 2).
Let `R` be an orthogonal projector (`R = P Q`) fixing the starting value `y` and every stage
derivative `F(t + cᵢ h, Zᵢ)` of the full explicit Runge–Kutta step with nonzero weight `bᵢ`.
**Conditional on** the local error bound `‖a₁ − z₁‖ ≤ K` of the full Runge–Kutta result `z₁`
(e.g. `K = c₁ h^{p+1} + c₂ h ε_r`): `‖R a₁ − a₁‖ ≤ K`.  Differences from the paper: the paper
compares with the projected Runge–Kutta result `Y_PRK` and its bases fix the projected stage
directions `Z̄ᵢ`, not the full `F(t + cᵢ h, Zᵢ)` (see the module docstring); and the constant is
`1` instead of the `2` of the paper's argument (which bounds `‖A − PQA‖ ≤ 2‖A − Y_PRK‖` via a
triangle inequality; the orthogonal-projection best-approximation property gives `1`). -/
theorem consistency_P2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {s : ℕ}
    {F : ℝ → E → E} {a : Fin s → Fin s → ℝ} {b c : Fin s → ℝ} {t h : ℝ} {y z₁ a₁ : E}
    {Z : Fin s → E} {R : E →L[ℝ] E} {K : ℝ} (hR : IsOrthProj R)
    (hZ : IsGalerkinRKStep F a b c (fun _ => 1) 1 t h y Z z₁) (hy : R y = y)
    (hF : ∀ i, b i ≠ 0 → R (F (t + c i * h) (Z i)) = F (t + c i * h) (Z i))
    (hK : ‖a₁ - z₁‖ ≤ K) : ‖R a₁ - a₁‖ ≤ K := by
  have hz : R z₁ = z₁ := rk_result_mem hZ hy hF
  rw [norm_sub_rev]
  exact (hR.norm_sub_le_of_mem_range a₁ z₁ hz).trans hK

/-- **Lemma 2 (consistency P2 for RK bases), matrix form** (after arXiv 2608.27749, Lemma 2).
For `U`, `V` with orthonormal columns, a full Runge–Kutta step from `y` with
`U Uᵀ y V Vᵀ = y` whose stage derivatives with nonzero weight satisfy
`U Uᵀ F V Vᵀ = F`, and, **conditional on** the local error bound
`‖a₁ − z₁‖ ≤ c₁ h^{p+1} + c₂ h ε` for the exact value `a₁`:

    ‖U Uᵀ a₁ V Vᵀ − a₁‖ ≤ c₁ h^{p+1} + c₂ h ε.

Differences from the paper as for `consistency_P2`: full instead of projected Runge–Kutta step
(the bases (10a)–(10b) need not fix the full stage derivatives), and constant `1` in place
of `2`. -/
theorem consistency_P2_matrix {m n k k' : Type*} [Fintype m] [Fintype n] [Fintype k]
    [Fintype k'] [DecidableEq k] [DecidableEq k'] {s : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {a : Fin s → Fin s → ℝ} {b c : Fin s → ℝ}
    {t h : ℝ} {y z₁ a₁ : Matrix m n ℝ} {Z : Fin s → Matrix m n ℝ}
    {U : Matrix m k ℝ} {V : Matrix n k' ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    {p : ℕ} {c₁ c₂ ε : ℝ}
    (hZ : IsGalerkinRKStep F a b c (fun _ => 1) 1 t h y Z z₁)
    (hy : U * Uᵀ * y * (V * Vᵀ) = y)
    (hF : ∀ i, b i ≠ 0 →
      U * Uᵀ * F (t + c i * h) (Z i) * (V * Vᵀ) = F (t + c i * h) (Z i))
    (hK : ‖a₁ - z₁‖ ≤ c₁ * h ^ (p + 1) + c₂ * h * ε) :
    ‖U * Uᵀ * a₁ * (V * Vᵀ) - a₁‖ ≤ c₁ * h ^ (p + 1) + c₂ * h * ε := by
  have hP := isOrthProj_leftProj_mul_rightProj (m := m) (n := n) hU hV
  have key := consistency_P2 (R := (leftProj U * rightProj V : Matrix m n ℝ →L[ℝ] _)) hP hZ
    (by simpa [Matrix.mul_assoc] using hy) (fun i hi => by simpa [Matrix.mul_assoc] using hF i hi)
    hK
  simpa [Matrix.mul_assoc] using key

/-- Non-vacuity: with full bases (`U = V = 1`) and the explicit Euler step, the hypotheses of
`consistency_P2_matrix` hold and the theorem applies to any data. -/
example (F : ℝ → Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) (t h : ℝ)
    (y a₁ : Matrix (Fin 2) (Fin 2) ℝ) (c₁ c₂ ε : ℝ)
    (hK : ‖a₁ - (y + h • F t y)‖ ≤ c₁ * h ^ (1 + 1) + c₂ * h * ε) :
    ‖(1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * a₁ *
        ((1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ) - a₁‖ ≤
      c₁ * h ^ (1 + 1) + c₂ * h * ε :=
  consistency_P2_matrix (s := 1) (a := fun _ _ => 0) (b := fun _ => 1) (c := fun _ => 0)
    (F := F) (Z := fun _ => y) (y := y) (t := t)
    (h := h) (z₁ := y + h • F t y) (U := 1) (V := 1) (by simp) (by simp)
    ⟨fun i => by simp, by simp⟩ (by simp) (fun i _ => by simp) hK

end LeanDLRA.Literature.P2608_27749
