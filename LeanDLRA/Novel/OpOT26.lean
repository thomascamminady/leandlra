import LeanDLRA.Dynamics.ContinuousDLRA
import LeanDLRA.Matrix.LowRankDistance
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Classical.WeylSingular

/-!
# Quasi-optimality of DLRA with respect to the best rank-`r` approximation (OP-OT-26)

Open problem OP-OT-26 of `docs/catalogue/survey/open-problems.json` (arXiv 1301.1058 Sec. 5.2,
arXiv 2309.06125 Sec. 5.1, arXiv 2402.03586 Sec. 4, arXiv 2608.17157 Sec. 7.1).  The question: is
the error of the dynamical low-rank approximation
`Ẏ = P(Y) Ȧ` bounded by a constant times the best rank-`r` error `dist(A(t), M_r)`, presumably
under a gap `σ_r - σ_{r+1} ≥ ρ`, and when does such a bound fail?  The library proves
Koch–Lubich quasi-optimality (`ODESolution.dlra_quasiOptimal_integral`) with the *integral*
`∫ ‖A - X‖` of the best-approximation error on the right-hand side.

## What is proved

* **The `sup`-bound holds under a gap on the DLRA solution**
  (`norm_sub_le_of_infDist_le`, `norm_sub_le_of_infDist_le'`, `dlra_norm_sub_le_distLR`).
  If `Y(t) = U S Vᵀ` solves `Ẏ = P(Y) Ȧ` on `[a, b]` with `σ_r(Y(t)) ≥ ρ > 0`,
  `dist(A(t), M_{≤ r}) ≤ d` and `‖Ȧ‖ ≤ μ`, and the data are small in the sense
  `(4√2/ρ) (d + e^{(4√2/ρ) μ (b-a)} (2 ‖Y(a) - A(a)‖ + 3 d)) < 1`, then
  `‖Y(t) - A(t)‖ ≤ e^{(4√2/ρ) μ (t - a)} (2 ‖Y(a) - A(a)‖ + 3 d)`.
  The right-hand side is the *supremum* `d` of the best-approximation error, not its integral.
  Mechanism: write `E = A - Y = T + N` (tangential and normal parts at `Y(t)`).  Since
  `Ė = (1 - P(Y)) Ȧ` is normal, the tangential part grows only through the rotation of the
  tangent space, `D⁺‖T‖ ≤ γ ‖Ẏ‖ ‖E‖` (`frequently_slope_tangent_lt`, a Dini-derivative
  estimate from the Lipschitz bound of the projector), while the normal part is controlled
  pointwise, `‖N‖ ≤ dist(A, M_r) + γ ‖B - Y‖²` with `B` a best approximation
  (`norm_normal_le`, curvature bound).  Grönwall for `‖T‖` and a continuity argument for the
  smallness condition give the result.  The hypotheses are verified on matrices from
  `Curvature.koch_lubich_tangentProj` (Lipschitz, `γ = 2√2/ρ`) and, after transporting the
  gap from `Y` to `B` by Weyl's inequality
  (`WeylSingular.forall_mul_norm_le_core_of_specNorm_sub_le`), from
  `Curvature.koch_lubich_normal` (curvature, `2/ρ`).
* **Counterexample A: the ratio blows up at rate `1/gap` after a crossing** (`cxA_*`).
  `A(t) = diag(δ, t)`, `Y(0) = A(0)`.  The velocity `e₂e₂ᵀ` is normal at `Y`, so the DLRA solution
  is stationary (`cxA_odeSolution`), `‖Y(t) - A(t)‖ = t` (the trivial bound `∫‖Ȧ‖` is attained,
  `cxA_norm_sub`), while `dist(A(t), M_{≤ 1}) = min(δ, t)` (`cxA_distLR`, exact Eckart–Young
  value without SVD).  The singular values cross at `t = δ` and afterwards
  `‖Y(t) - A(t)‖ = (t/δ) dist(A(t), M_{≤ 1})` (`cxA_ratio`): the ratio grows linearly in
  time at rate `1/δ`, with the supremum version `dist ≤ δ` along the path (`cxA_sup_distLR`).
  Without a gap nothing beyond the trivial bound holds.
* **Counterexample B: pointwise quasi-optimality fails even under a uniform gap** (`cxB_*`).
  `Y(t) = w(t) w(t)ᵀ` with `w = (cos t, sin t)` and `A = Y + E`,
  `Ė = α (1 - 2 cos 2t) w⊥ w⊥ᵀ` normal at `Y`.  Then `Y` solves the DLRA equation exactly
  (`cxB_odeSolution`), `A(0) = Y(0)`, `σ₁(Y) ≡ 1`, `dist(A(t), M_{≤ 1}) ≤ 3|α| t` and
  `‖A(t) w(t)‖ ≥ 1 - 3|α| t` (so the gap of `A` stays `≥ 1 - 6|α|t`), but
  `A(π) = (1 + απ) e₁e₁ᵀ` has rank one while `‖Y(π) - A(π)‖ = |α| π` (`cxB_norm_sub_pi`,
  `cxB_distLR_pi`).  The DLRA error has memory: the bound can only involve
  `sup_{s ≤ t} dist(A(s), M_r)` (or `∫‖Ė‖`), never `dist(A(t), M_r)` alone.
* **Counterexample C: the gap must hold along the whole trajectory** (`cxC_*`).
  `A_δ(t) = diag(δ + φ(1-t), φ(t-1))` with a smooth transition `φ`: `Y_δ(0) = A_δ(0)` has gap
  `1 + δ`, the velocity `Ȧ_δ` does not depend on `δ`, `dist(A_δ(s), M_{≤ 1}) ≤ δ` for all `s`,
  yet `‖Y_δ(2) - A_δ(2)‖ = 1`.  So no bound `C(T, ‖Ȧ‖, σ_r(Y(0))) · sup_s dist(A(s), M_r)`
  exists; the hypothesis `σ_r(Y(t)) ≥ ρ` for all `t` in `dlra_norm_sub_le_distLR` cannot be
  weakened to a gap at the initial time.

## What stays open

The constant `e^{(4√2/ρ) μ T}` is of Koch–Lubich type; whether the exponential dependence on
`μ T / ρ` is sharp for the `sup`-bound is not known (a linearised `2 × 2` computation suggests a
polynomial constant).  The gap is assumed for the DLRA solution `Y`; a version with the gap on
`A` alone (and a bootstrap through Weyl's inequality) is not done.  The discrete (integrator)
version with `C h^p` and the rank-`q` tracking phenomenon (Lubich–Oseledets, Thm. 4.2) are not
treated.
-/

open Set Filter Topology Metric
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Novel.OpOT26

open LeanDLRA

/-! ### The abstract estimate -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {P : ℝ → E →L[ℝ] E} {Y A A' : ℝ → E} {M : Set E} {a b γ μ d : ℝ}

/-- The normal component of `A - Y` at `Y` is controlled by the distance of `A` to `M` plus a
curvature term: `‖(1 - P) (A - Y)‖ ≤ d + γ (d + ‖A - Y‖)²`. -/
private theorem norm_normal_le {t : ℝ} (hP : IsOrthProj (P t)) (hγ : 0 ≤ γ) (hM : M.Nonempty)
    (hcurv : ∀ B ∈ M, ‖(1 - P t) (B - Y t)‖ ≤ γ * ‖B - Y t‖ ^ 2)
    (hd : infDist (A t) M ≤ d) :
    ‖(1 - P t) (A t - Y t)‖ ≤ d + γ * (d + ‖A t - Y t‖) ^ 2 := by
  have key : ∀ ε > 0,
      ‖(1 - P t) (A t - Y t)‖ ≤ (d + ε) + γ * ((d + ε) + ‖A t - Y t‖) ^ 2 := by
    intro ε hε
    obtain ⟨B, hB, hAB⟩ := (infDist_lt_iff hM).1 (lt_of_le_of_lt hd (lt_add_of_pos_right d hε))
    rw [dist_eq_norm] at hAB
    have hAB' : ‖A t - B‖ ≤ d + ε := hAB.le
    have hBY : ‖B - Y t‖ ≤ (d + ε) + ‖A t - Y t‖ := by
      calc ‖B - Y t‖ = ‖(B - A t) + (A t - Y t)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖B - A t‖ + ‖A t - Y t‖ := norm_add_le _ _
        _ ≤ (d + ε) + ‖A t - Y t‖ := by rw [norm_sub_rev]; gcongr
    have hsplit : (1 - P t) (A t - Y t) = (1 - P t) (A t - B) + (1 - P t) (B - Y t) := by
      rw [← map_add, sub_add_sub_cancel]
    calc ‖(1 - P t) (A t - Y t)‖
        = ‖(1 - P t) (A t - B) + (1 - P t) (B - Y t)‖ := by rw [hsplit]
      _ ≤ ‖(1 - P t) (A t - B)‖ + ‖(1 - P t) (B - Y t)‖ := norm_add_le _ _
      _ ≤ ‖A t - B‖ + γ * ‖B - Y t‖ ^ 2 := add_le_add (hP.compl.norm_le _) (hcurv B hB)
      _ ≤ (d + ε) + γ * ((d + ε) + ‖A t - Y t‖) ^ 2 := by gcongr
  have hcont : ContinuousAt (fun ε : ℝ => (d + ε) + γ * ((d + ε) + ‖A t - Y t‖) ^ 2) 0 := by
    fun_prop
  have hlim : Tendsto (fun ε : ℝ => (d + ε) + γ * ((d + ε) + ‖A t - Y t‖) ^ 2) (𝓝[>] 0)
      (𝓝 (d + γ * (d + ‖A t - Y t‖) ^ 2)) := by
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)

/-- Under the smallness condition `2 γ (d + ‖A - Y‖) ≤ 1`, the full error is controlled by its
tangential part: `‖A - Y‖ ≤ 2 ‖P (A - Y)‖ + 3 d`. -/
private theorem norm_le_two_tangent_add {t : ℝ} (hP : IsOrthProj (P t)) (hγ : 0 ≤ γ)
    (hM : M.Nonempty) (hcurv : ∀ B ∈ M, ‖(1 - P t) (B - Y t)‖ ≤ γ * ‖B - Y t‖ ^ 2)
    (hd : infDist (A t) M ≤ d) (hsmall : 2 * γ * (d + ‖A t - Y t‖) ≤ 1) :
    ‖A t - Y t‖ ≤ 2 * ‖P t (A t - Y t)‖ + 3 * d := by
  have hN := norm_normal_le hP hγ hM hcurv hd
  have hd0 : 0 ≤ d := infDist_nonneg.trans hd
  have he0 : 0 ≤ ‖A t - Y t‖ := norm_nonneg _
  have hsplit : A t - Y t = P t (A t - Y t) + (1 - P t) (A t - Y t) := by simp
  have htri : ‖A t - Y t‖ ≤ ‖P t (A t - Y t)‖ + ‖(1 - P t) (A t - Y t)‖ := by
    conv_lhs => rw [hsplit]
    exact norm_add_le _ _
  have hq : γ * (d + ‖A t - Y t‖) ^ 2 ≤ (1 / 2) * (d + ‖A t - Y t‖) := by
    have : γ * (d + ‖A t - Y t‖) ≤ 1 / 2 := by linarith
    calc γ * (d + ‖A t - Y t‖) ^ 2 = (γ * (d + ‖A t - Y t‖)) * (d + ‖A t - Y t‖) := by ring
      _ ≤ (1 / 2) * (d + ‖A t - Y t‖) := by gcongr
  linarith

/-- **Dini slope of the tangential error.**  At a point `x` where `Y` solves `Ẏ = P(x) Ȧ(x)` and
the projector is Lipschitz along the trajectory, the right Dini derivative of
`z ↦ ‖P(z) (A z - Y z)‖` is at most `γ μ ‖A x - Y x‖`: the tangential part of the error only
grows through the rotation of the tangent space, never directly through `Ȧ`. -/
private theorem frequently_slope_tangent_lt {x : ℝ} (hax : a ≤ x) (hxb : x < b)
    (hPx : IsOrthProj (P x))
    (hYd : HasDerivWithinAt Y (P x (A' x)) (Ici x) x)
    (hAd : HasDerivWithinAt A (A' x) (Ici x) x) (hμ : ‖A' x‖ ≤ μ) (hγ : 0 ≤ γ)
    (hLip : ∀ z ∈ Icc a b, ∀ v, ‖P z v - P x v‖ ≤ γ * ‖Y z - Y x‖ * ‖v‖)
    {r : ℝ} (hr : γ * μ * ‖A x - Y x‖ < r) :
    ∃ᶠ z in 𝓝[>] x,
      (z - x)⁻¹ * (‖P z (A z - Y z)‖ - ‖P x (A x - Y x)‖) < r := by
  have hEd : HasDerivWithinAt (fun z => A z - Y z) (A' x - P x (A' x)) (Ici x) x := hAd.sub hYd
  have hnot : x ∉ Ioi x := fun h => lt_irrefl x h
  -- (1) the slope of `Y` tends to the velocity
  have t1 : Tendsto (fun z => ‖slope Y x z‖) (𝓝[>] x) (𝓝 ‖P x (A' x)‖) :=
    ((hasDerivWithinAt_iff_tendsto_slope' hnot).1 hYd.Ioi_of_Ici).norm
  -- (2) `Ef` is right-continuous at `x`
  have t2 : Tendsto (fun z => ‖A z - Y z‖) (𝓝[>] x) (𝓝 ‖A x - Y x‖) := by
    have := hEd.continuousWithinAt
    exact (this.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)).norm
  -- (3) `P x` applied to the slope of `Ef` tends to `P x Ė = 0`
  have t3 : Tendsto (fun z => ‖P x (slope (fun z => A z - Y z) x z)‖) (𝓝[>] x) (𝓝 0) := by
    have := (hasDerivWithinAt_iff_tendsto_slope' hnot).1 hEd.Ioi_of_Ici
    have h2 := ((P x).continuous.tendsto _).comp this
    have h0 : P x (A' x - P x (A' x)) = 0 := by
      rw [map_sub, hPx.idem, sub_self]
    rw [h0] at h2
    simpa using h2.norm
  have tg : Tendsto (fun z => γ * ‖slope Y x z‖ * ‖A z - Y z‖ +
      ‖P x (slope (fun z => A z - Y z) x z)‖) (𝓝[>] x)
      (𝓝 (γ * ‖P x (A' x)‖ * ‖A x - Y x‖ + 0)) :=
    ((t1.const_mul γ).mul t2).add t3
  have hℓ : γ * ‖P x (A' x)‖ * ‖A x - Y x‖ + 0 < r := by
    have : ‖P x (A' x)‖ ≤ μ := (hPx.norm_le _).trans hμ
    have : γ * ‖P x (A' x)‖ * ‖A x - Y x‖ ≤ γ * μ * ‖A x - Y x‖ := by gcongr
    linarith
  have hev := tg.eventually_lt_const hℓ
  have hIoo : Ioo x b ∈ 𝓝[>] x := Ioo_mem_nhdsGT hxb
  refine (hev.and hIoo).frequently.mono ?_
  rintro z ⟨hz, hzx, hzb⟩
  have hc : 0 < (z - x)⁻¹ := inv_pos.2 (sub_pos.2 hzx)
  have hzI : z ∈ Icc a b := ⟨hax.trans hzx.le, hzb.le⟩
  -- slope bound
  have hT : ‖P z (A z - Y z)‖ - ‖P x (A x - Y x)‖ ≤
      γ * ‖Y z - Y x‖ * ‖A z - Y z‖ + ‖P x ((A z - Y z) - (A x - Y x))‖ := by
    have hsplit : P z (A z - Y z) - P x (A x - Y x) =
        (P z (A z - Y z) - P x (A z - Y z)) + P x ((A z - Y z) - (A x - Y x)) := by
      simp only [map_sub]; abel
    calc ‖P z (A z - Y z)‖ - ‖P x (A x - Y x)‖
        ≤ ‖P z (A z - Y z) - P x (A x - Y x)‖ := norm_sub_norm_le _ _
      _ = ‖(P z (A z - Y z) - P x (A z - Y z)) + P x ((A z - Y z) - (A x - Y x))‖ := by
          rw [hsplit]
      _ ≤ ‖P z (A z - Y z) - P x (A z - Y z)‖ + ‖P x ((A z - Y z) - (A x - Y x))‖ :=
          norm_add_le _ _
      _ ≤ γ * ‖Y z - Y x‖ * ‖A z - Y z‖ + ‖P x ((A z - Y z) - (A x - Y x))‖ := by
          gcongr; exact hLip z hzI _
  have hslopeY : ‖slope Y x z‖ = (z - x)⁻¹ * ‖Y z - Y x‖ := by
    rw [slope_def_module, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have hslopeE : ‖P x (slope (fun z => A z - Y z) x z)‖ =
      (z - x)⁻¹ * ‖P x ((A z - Y z) - (A x - Y x))‖ := by
    rw [slope_def_module, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  calc (z - x)⁻¹ * (‖P z (A z - Y z)‖ - ‖P x (A x - Y x)‖)
      ≤ (z - x)⁻¹ * (γ * ‖Y z - Y x‖ * ‖A z - Y z‖ + ‖P x ((A z - Y z) - (A x - Y x))‖) := by
        gcongr
    _ = γ * ‖slope Y x z‖ * ‖A z - Y z‖ + ‖P x (slope (fun z => A z - Y z) x z)‖ := by
        rw [hslopeY, hslopeE]; ring
    _ < r := hz

/-- Continuity of the tangential error `z ↦ P(z) (A z - Y z)` on `[a, b]`, from the Lipschitz
bound on the projector along the (continuous) trajectory. -/
private theorem continuousOn_tangent (hYc : ContinuousOn Y (Icc a b))
    (hAc : ContinuousOn A (Icc a b))
    (hLip : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ z, ‖P t z - P s z‖ ≤ γ * ‖Y t - Y s‖ * ‖z‖)
    (hP : ∀ t ∈ Icc a b, IsOrthProj (P t)) :
    ContinuousOn (fun z => P z (A z - Y z)) (Icc a b) := by
  intro s hs
  have hEc : ContinuousWithinAt (fun z => A z - Y z) (Icc a b) s :=
    (hAc s hs).sub (hYc s hs)
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hg : Tendsto (fun z => γ * ‖Y z - Y s‖ * ‖A z - Y z‖ + ‖(A z - Y z) - (A s - Y s)‖)
      (𝓝[Icc a b] s)
      (𝓝 (γ * ‖Y s - Y s‖ * ‖A s - Y s‖ + ‖(A s - Y s) - (A s - Y s)‖)) :=
    (((((hYc s hs).sub tendsto_const_nhds).norm.const_mul γ).mul hEc.norm)).add
      ((hEc.sub tendsto_const_nhds).norm)
  simp only [sub_self, norm_zero, mul_zero, zero_mul, add_zero] at hg
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (eventually_nhdsWithin_of_forall fun z hz => ?_) hg
  have hsplit : P z (A z - Y z) - P s (A s - Y s) =
      (P z (A z - Y z) - P s (A z - Y z)) + P s ((A z - Y z) - (A s - Y s)) := by
    simp only [map_sub]; abel
  rw [hsplit]
  calc ‖(P z (A z - Y z) - P s (A z - Y z)) + P s ((A z - Y z) - (A s - Y s))‖
      ≤ ‖P z (A z - Y z) - P s (A z - Y z)‖ + ‖P s ((A z - Y z) - (A s - Y s))‖ :=
        norm_add_le _ _
    _ ≤ γ * ‖Y z - Y s‖ * ‖A z - Y z‖ + ‖(A z - Y z) - (A s - Y s)‖ :=
        add_le_add (hLip s hs z hz _) ((hP s hs).norm_le _)

/-- **Quasi-optimality with respect to `sup dist(A, M)`, conditional form.**  Let `Y` solve the
DLRA equation `Ẏ = P(t) Ȧ(t)` on `[a, b]` with orthogonal projectors `P(t)` (the tangent
projector at `Y(t)`) which are `γ`-Lipschitz along the trajectory and satisfy the curvature
bound `‖(1 - P(t)) (B - Y(t))‖ ≤ γ ‖B - Y(t)‖²` for every `B ∈ M` (the manifold).  If
`dist(A(t), M) ≤ d`, `‖Ȧ‖ ≤ μ` and the a priori smallness `2 γ (d + ‖A - Y‖) ≤ 1` holds on
`[a, b]`, then

  `‖Y(t) - A(t)‖ ≤ e^{2 γ μ (t - a)} (2 ‖Y(a) - A(a)‖ + 3 d)`.

The error is bounded by the *supremum* of the best-approximation error, not by the integral
`∫ ‖Ė‖` of Koch–Lubich (2007, Thm. 5.1): the only growth mechanism of the error is the rotation
of the tangent space (`frequently_slope_tangent_lt`), and the normal component of the error is
pointwise controlled by `dist(A, M)` up to curvature (`norm_normal_le`). -/
theorem norm_sub_le_of_infDist_le
    (hY : ODESolution (fun t _ => P t (A' t)) Y a b) (hP : ∀ t ∈ Icc a b, IsOrthProj (P t))
    (hAc : ContinuousOn A (Icc a b)) (hA : ∀ t ∈ Ico a b, HasDerivWithinAt A (A' t) (Ici t) t)
    (hμ : ∀ t ∈ Ico a b, ‖A' t‖ ≤ μ) (hγ : 0 ≤ γ) (hM : M.Nonempty)
    (hLip : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ z, ‖P t z - P s z‖ ≤ γ * ‖Y t - Y s‖ * ‖z‖)
    (hcurv : ∀ t ∈ Icc a b, ∀ B ∈ M, ‖(1 - P t) (B - Y t)‖ ≤ γ * ‖B - Y t‖ ^ 2)
    (hd : ∀ t ∈ Icc a b, infDist (A t) M ≤ d)
    (hsmall : ∀ t ∈ Icc a b, 2 * γ * (d + ‖Y t - A t‖) ≤ 1) :
    ∀ t ∈ Icc a b,
      ‖Y t - A t‖ ≤ Real.exp (2 * γ * μ * (t - a)) * (2 * ‖Y a - A a‖ + 3 * d) := by
  intro t ht
  have hd0 : 0 ≤ d := infDist_nonneg.trans (hd a (left_mem_Icc.2 (ht.1.trans ht.2)))
  rcases eq_or_lt_of_le ht.1 with hat | hat
  · subst hat
    rw [sub_self, mul_zero, Real.exp_zero, one_mul]
    linarith [norm_nonneg (Y a - A a)]
  have hab : a < b := hat.trans_le ht.2
  have hμ0 : 0 ≤ μ := (norm_nonneg _).trans (hμ a ⟨le_rfl, hab⟩)
  -- the a priori bound `‖E‖ ≤ 2 ‖T‖ + 3 d`
  have hE : ∀ s ∈ Icc a b, ‖A s - Y s‖ ≤ 2 * ‖P s (A s - Y s)‖ + 3 * d := fun s hs =>
    norm_le_two_tangent_add (hP s hs) hγ hM (hcurv s hs) (hd s hs)
      (by rw [norm_sub_rev]; exact hsmall s hs)
  -- Grönwall for `f = ‖T‖`
  have hG := le_gronwallBound_of_liminf_deriv_right_le (a := a) (b := b)
    (f := fun z => ‖P z (A z - Y z)‖) (f' := fun x => γ * μ * ‖A x - Y x‖)
    (δ := ‖P a (A a - Y a)‖) (K := 2 * γ * μ) (ε := 3 * γ * μ * d)
    ((continuous_norm.comp_continuousOn (continuousOn_tangent hY.cont hAc hLip hP)))
    (fun x hx r hr => frequently_slope_tangent_lt hx.1 hx.2 (hP x (Ico_subset_Icc_self hx))
      (hY.deriv x hx) (hA x hx) (hμ x hx) hγ
      (fun z hz v => hLip x (Ico_subset_Icc_self hx) z hz v) hr)
    le_rfl
    (fun x hx => by
      have h := hE x (Ico_subset_Icc_self hx)
      have hγμ : 0 ≤ γ * μ := mul_nonneg hγ hμ0
      calc γ * μ * ‖A x - Y x‖ ≤ γ * μ * (2 * ‖P x (A x - Y x)‖ + 3 * d) := by gcongr
        _ = 2 * γ * μ * ‖P x (A x - Y x)‖ + 3 * γ * μ * d := by ring)
    t ht
  have hTa : ‖P a (A a - Y a)‖ ≤ ‖Y a - A a‖ := by
    rw [norm_sub_rev (Y a)]; exact (hP a (left_mem_Icc.2 hab.le)).norm_le _
  have hEt := hE t ht
  rw [norm_sub_rev]
  have hexp : 0 < Real.exp (2 * γ * μ * (t - a)) := Real.exp_pos _
  rcases eq_or_ne (2 * γ * μ) 0 with hK | hK
  · have hε : 3 * γ * μ * d = 0 := by
      have : γ * μ = 0 := by linarith
      rw [show 3 * γ * μ * d = 3 * (γ * μ) * d by ring, this]; ring
    rw [hK, hε, gronwallBound_K0] at hG
    simp only [zero_mul, add_zero] at hG
    rw [hK, zero_mul, Real.exp_zero, one_mul]
    linarith
  · rw [gronwallBound_of_K_ne_0 hK] at hG
    simp only at hG
    have hdiv : 3 * γ * μ * d / (2 * γ * μ) = 3 / 2 * d := by
      rw [div_eq_iff hK]; ring
    rw [hdiv] at hG
    have hexp1 : 1 ≤ Real.exp (2 * γ * μ * (t - a)) :=
      Real.one_le_exp (by positivity)
    nlinarith [hG, hEt, hTa, hexp1, hd0, norm_nonneg (P a (A a - Y a))]

/-- **Quasi-optimality with respect to `sup dist(A, M)`.**  As `norm_sub_le_of_infDist_le`, but
the a priori smallness of the error is replaced by smallness of the data: if
`2 γ (d + e^{2 γ μ (b - a)} (2 ‖Y(a) - A(a)‖ + 3 d)) < 1`, then on `[a, b]`

  `‖Y(t) - A(t)‖ ≤ e^{2 γ μ (t - a)} (2 ‖Y(a) - A(a)‖ + 3 d)`.

Proof: continuity induction (the set of times up to which the smallness holds is closed by
continuity and open by the conditional estimate). -/
theorem norm_sub_le_of_infDist_le'
    (hY : ODESolution (fun t _ => P t (A' t)) Y a b) (hP : ∀ t ∈ Icc a b, IsOrthProj (P t))
    (hAc : ContinuousOn A (Icc a b)) (hA : ∀ t ∈ Ico a b, HasDerivWithinAt A (A' t) (Ici t) t)
    (hμ : ∀ t ∈ Ico a b, ‖A' t‖ ≤ μ) (hγ : 0 ≤ γ) (hM : M.Nonempty)
    (hLip : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ z, ‖P t z - P s z‖ ≤ γ * ‖Y t - Y s‖ * ‖z‖)
    (hcurv : ∀ t ∈ Icc a b, ∀ B ∈ M, ‖(1 - P t) (B - Y t)‖ ≤ γ * ‖B - Y t‖ ^ 2)
    (hd : ∀ t ∈ Icc a b, infDist (A t) M ≤ d)
    (hsmall : 2 * γ * (d + Real.exp (2 * γ * μ * (b - a)) * (2 * ‖Y a - A a‖ + 3 * d)) < 1) :
    ∀ t ∈ Icc a b,
      ‖Y t - A t‖ ≤ Real.exp (2 * γ * μ * (t - a)) * (2 * ‖Y a - A a‖ + 3 * d) := by
  intro t ht
  have hab : a ≤ b := ht.1.trans ht.2
  have hd0 : 0 ≤ d := infDist_nonneg.trans (hd a (left_mem_Icc.2 hab))
  rcases eq_or_lt_of_le hab with hab' | hab'
  · subst hab'
    have hta : t = a := le_antisymm ht.2 ht.1
    subst hta
    rw [sub_self, mul_zero, Real.exp_zero, one_mul]
    linarith [norm_nonneg (Y t - A t)]
  have hμ0 : 0 ≤ μ := (norm_nonneg _).trans (hμ a ⟨le_rfl, hab'⟩)
  have hγμ : 0 ≤ 2 * γ * μ := by positivity
  have hgc : ContinuousOn (fun u => ‖Y u - A u‖) (Icc a b) := (hY.cont.sub hAc).norm
  -- the conditional estimate on `[a, τ]`
  have cond : ∀ τ ∈ Icc a b, (∀ u ∈ Icc a τ, 2 * γ * (d + ‖Y u - A u‖) ≤ 1) →
      ∀ u ∈ Icc a τ,
        ‖Y u - A u‖ ≤ Real.exp (2 * γ * μ * (u - a)) * (2 * ‖Y a - A a‖ + 3 * d) := by
    intro τ hτ hsm
    have hsub : Icc a τ ⊆ Icc a b := Icc_subset_Icc_right hτ.2
    have hsub' : Ico a τ ⊆ Ico a b := Ico_subset_Ico_right hτ.2
    have hY' : ODESolution (fun t _ => P t (A' t)) Y a τ :=
      ⟨hY.cont.mono hsub, fun u hu => hY.deriv u (hsub' hu)⟩
    exact norm_sub_le_of_infDist_le hY' (fun u hu => hP u (hsub hu)) (hAc.mono hsub)
      (fun u hu => hA u (hsub' hu)) (fun u hu => hμ u (hsub' hu)) hγ hM
      (fun s hs t ht z => hLip s (hsub hs) t (hsub ht) z) (fun u hu => hcurv u (hsub hu))
      (fun u hu => hd u (hsub hu)) hsm
  -- the uniform bound `R`
  have hR : ∀ u ∈ Icc a b, Real.exp (2 * γ * μ * (u - a)) * (2 * ‖Y a - A a‖ + 3 * d) ≤
      Real.exp (2 * γ * μ * (b - a)) * (2 * ‖Y a - A a‖ + 3 * d) := by
    intro u hu
    gcongr
    exact hu.2
  have hR1 : ‖Y a - A a‖ ≤ Real.exp (2 * γ * μ * (b - a)) * (2 * ‖Y a - A a‖ + 3 * d) := by
    have h1 : 1 ≤ Real.exp (2 * γ * μ * (b - a)) := Real.one_le_exp (by nlinarith)
    nlinarith [norm_nonneg (Y a - A a)]
  -- the set of good times
  set S : Set ℝ := {τ | τ ∈ Icc a b ∧ ∀ u ∈ Icc a τ, 2 * γ * (d + ‖Y u - A u‖) ≤ 1} with hS
  have haS : a ∈ S := by
    refine ⟨left_mem_Icc.2 hab, fun u hu => ?_⟩
    have hua : u = a := le_antisymm hu.2 hu.1
    subst hua
    nlinarith
  have hSbdd : BddAbove S := ⟨b, fun τ hτ => hτ.1.2⟩
  have hSne : S.Nonempty := ⟨a, haS⟩
  have hτa : a ≤ sSup S := le_csSup hSbdd haS
  have hτb : sSup S ≤ b := csSup_le hSne fun x hx => hx.1.2
  -- below the supremum the smallness holds
  have h1 : ∀ u ∈ Ico a (sSup S), 2 * γ * (d + ‖Y u - A u‖) ≤ 1 := by
    intro u hu
    obtain ⟨σ, hσS, huσ⟩ := exists_lt_of_lt_csSup hSne hu.2
    exact hσS.2 u ⟨hu.1, huσ.le⟩
  -- the supremum is a good time (closedness)
  have hτS : sSup S ∈ S := by
    refine ⟨⟨hτa, hτb⟩, fun u hu => ?_⟩
    rcases eq_or_lt_of_le hu.2 with huτ | huτ
    · rcases eq_or_lt_of_le hτa with haτ | haτ
      · rw [huτ, ← haτ]; exact haS.2 a (left_mem_Icc.2 le_rfl)
      · have hC : IsClosed {u | u ∈ Icc a b ∧ 2 * γ * (d + ‖Y u - A u‖) ≤ 1} := by
          have hc : ContinuousOn (fun u => 2 * γ * (d + ‖Y u - A u‖)) (Icc a b) := by
            exact (hgc.const_add d).const_mul _ |>.congr fun _ _ => rfl
          exact hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
        have hsub : Ico a (sSup S) ⊆ {u | u ∈ Icc a b ∧ 2 * γ * (d + ‖Y u - A u‖) ≤ 1} :=
          fun u hu => ⟨⟨hu.1, hu.2.le.trans hτb⟩, h1 u hu⟩
        have hcl := closure_minimal hsub hC
        rw [closure_Ico haτ.ne] at hcl
        rw [huτ]
        exact (hcl (right_mem_Icc.2 haτ.le)).2
    · exact h1 u ⟨hu.1, huτ⟩
  -- the supremum is `b` (openness)
  have hτeq : sSup S = b := by
    by_contra hne
    have hτltb : sSup S < b := lt_of_le_of_ne hτb hne
    have hgτ : ‖Y (sSup S) - A (sSup S)‖ ≤
        Real.exp (2 * γ * μ * (b - a)) * (2 * ‖Y a - A a‖ + 3 * d) :=
      (cond _ ⟨hτa, hτb⟩ hτS.2 _ (right_mem_Icc.2 hτa)).trans (hR _ ⟨hτa, hτb⟩)
    have hhτ : 2 * γ * (d + ‖Y (sSup S) - A (sSup S)‖) < 1 := by nlinarith
    have hcont : ContinuousWithinAt (fun u => 2 * γ * (d + ‖Y u - A u‖)) (Icc a b) (sSup S) :=
      ((hgc _ ⟨hτa, hτb⟩).const_add d).const_mul _
    obtain ⟨δ', hδ'pos, hδ'⟩ := Metric.continuousWithinAt_iff.1 hcont
      (1 - 2 * γ * (d + ‖Y (sSup S) - A (sSup S)‖)) (by linarith)
    have hσS : min b (sSup S + δ' / 2) ∈ S := by
      refine ⟨⟨hτa.trans (le_min hτltb.le (by linarith)), min_le_left _ _⟩, fun u hu => ?_⟩
      rcases le_or_gt u (sSup S) with huτ | huτ
      · exact hτS.2 u ⟨hu.1, huτ⟩
      · have hub : u ≤ b := hu.2.trans (min_le_left _ _)
        have hud : u ≤ sSup S + δ' / 2 := hu.2.trans (min_le_right _ _)
        have hdist : dist u (sSup S) < δ' := by
          rw [Real.dist_eq, abs_of_pos (sub_pos.2 huτ)]; linarith
        have := hδ' ⟨hu.1, hub⟩ hdist
        rw [Real.dist_eq, abs_sub_lt_iff] at this
        linarith [this.1]
    have hlt : sSup S < min b (sSup S + δ' / 2) := lt_min hτltb (by linarith)
    exact absurd (le_csSup hSbdd hσS) (not_le.2 hlt)
  exact cond b (right_mem_Icc.2 hab) (hτeq ▸ hτS.2) t ht

end Abstract

/-! ### Matrices: the tangent projector of a factored trajectory with `σ_r(Y) ≥ ρ` -/

section MatrixVersion

open Curvature WeylSingular

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}

/-- Lipschitz bound for the tangent projector along a factored trajectory: at a time `s` with
`σ_r(Y(s)) ≥ ρ`, `‖P(Y(t)) z - P(Y(s)) z‖ ≤ 2 √2 ρ⁻¹ ‖Y(t) - Y(s)‖ ‖z‖` (Koch–Lubich 2007,
Lemma 4.2, via `Curvature.koch_lubich_tangentProj`). -/
private theorem lip_tangentProj {U : ℝ → Matrix m (Fin r) ℝ} {S : ℝ → Matrix (Fin r) (Fin r) ℝ}
    {V : ℝ → Matrix n (Fin r) ℝ} {Y : ℝ → Matrix m n ℝ} {ρ : ℝ} (hρ : 0 < ρ) {s t : ℝ}
    (hYs : Y s = U s * S s * (V s)ᵀ) (hYt : Y t = U t * S t * (V t)ᵀ)
    (hUs : (U s)ᵀ * U s = 1) (hVs : (V s)ᵀ * V s = 1) (hUt : (U t)ᵀ * U t = 1)
    (hVt : (V t)ᵀ * V t = 1)
    (hσ : ρ ≤ (Matrix.toEuclideanLin (Y s)).singularValues (r - 1)) (z : Matrix m n ℝ) :
    ‖tangentProj (U t) (V t) z - tangentProj (U s) (V s) z‖ ≤
      2 * √2 / ρ * ‖Y t - Y s‖ * ‖z‖ := by
  have hσ' : ρ ≤ (Matrix.toEuclideanLin (Y s)).singularValues (Fintype.card (Fin r) - 1) := by
    rwa [Fintype.card_fin]
  have hS : ∀ v : EuclideanSpace ℝ (Fin r), ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin (S s) v‖ :=
    mul_norm_le_norm_toEuclideanLin_core hUs hVs hYs hρ hσ'
  have h := koch_lubich_tangentProj (S' := S t) hρ hUs hVs hUt hVt hS z
  rw [← hYt, ← hYs] at h
  calc ‖tangentProj (U t) (V t) z - tangentProj (U s) (V s) z‖
      ≤ 2 * √2 * ρ⁻¹ * ‖Y t - Y s‖ * specNorm z := h
    _ ≤ 2 * √2 / ρ * ‖Y t - Y s‖ * ‖z‖ := by
        rw [div_eq_mul_inv]
        gcongr
        exact specNorm_le_frob z

/-- Curvature bound at a rank-`r` matrix `Y = U S Vᵀ` with `σ_r(Y) ≥ ρ`: for every `B` of rank
`≤ r`, `‖(1 - P(Y)) (B - Y)‖ ≤ (2/ρ) ‖B - Y‖²`.  For `‖B - Y‖ ≥ ρ/2` this is trivial; otherwise
Weyl's inequality gives `σ_r(B) ≥ ρ/2` and `Curvature.koch_lubich_normal` applies. -/
private theorem curv_tangentProj {U : Matrix m (Fin r) ℝ} {S : Matrix (Fin r) (Fin r) ℝ}
    {V : Matrix n (Fin r) ℝ} {Y : Matrix m n ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hY : Y = U * S * Vᵀ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hσ : ρ ≤ (Matrix.toEuclideanLin Y).singularValues (r - 1))
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    {B : Matrix m n ℝ} (hB : B.rank ≤ r) :
    ‖(1 - tangentProj U V) (B - Y)‖ ≤ 2 / ρ * ‖B - Y‖ ^ 2 := by
  have hnormal : (1 - tangentProj U V) (B - Y) = (1 - U * Uᵀ) * (B - Y) * (1 - V * Vᵀ) := by
    have h := tangentProj_add_normal U V (B - Y)
    rw [sub_apply, one_apply_eq_self]
    exact (sub_eq_of_eq_add' h.symm).symm ▸ rfl
  rcases le_or_gt (ρ / 2) ‖B - Y‖ with h | h
  · have hP : IsOrthProj (tangentProj U V : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) :=
      isOrthProj_tangentProj hU hV
    have h1 : 1 ≤ 2 / ρ * ‖B - Y‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hρ]; linarith
    calc ‖(1 - tangentProj U V) (B - Y)‖ ≤ ‖B - Y‖ := hP.compl.norm_le _
      _ = 1 * ‖B - Y‖ := (one_mul _).symm
      _ ≤ (2 / ρ * ‖B - Y‖) * ‖B - Y‖ := by gcongr
      _ = 2 / ρ * ‖B - Y‖ ^ 2 := by ring
  · obtain ⟨U', S', V', hU', hV', hB'⟩ := exists_factor_of_rank_le hB hrm hrn
    have hσ' : ρ ≤ (Matrix.toEuclideanLin Y).singularValues (Fintype.card (Fin r) - 1) := by
      rwa [Fintype.card_fin]
    have hspec : specNorm (B - Y) ≤ (1 / 2) * ρ :=
      (specNorm_le_frob _).trans (by linarith)
    have hS' : ∀ v : EuclideanSpace ℝ (Fin r),
        (1 - 1 / 2) * ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S' v‖ := fun v =>
      forall_mul_norm_le_core_of_specNorm_sub_le hU' hV' hB' hρ (by norm_num) hσ' hspec v
    have hkl := koch_lubich_normal (S' := S) (ρ := (1 - 1 / 2) * ρ) (by positivity) hU' hV' hU hV
      hS'
    rw [← hY, ← hB'] at hkl
    have hneg : (1 - U * Uᵀ) * (B - Y) * (1 - V * Vᵀ) =
        -((1 - U * Uᵀ) * (Y - B) * (1 - V * Vᵀ)) := by
      rw [← neg_sub Y B, Matrix.mul_neg, Matrix.neg_mul]
    rw [hnormal, hneg, norm_neg, norm_sub_rev B Y]
    calc ‖(1 - U * Uᵀ) * (Y - B) * (1 - V * Vᵀ)‖ ≤ ((1 - 1 / 2) * ρ)⁻¹ * ‖Y - B‖ ^ 2 := hkl
      _ = 2 / ρ * ‖Y - B‖ ^ 2 := by
          congr 1
          field_simp
          ring

/-- **Quasi-optimality of DLRA with respect to `sup_s dist(A(s), M_{≤ r})`, on matrices.**
Let `Y(t) = U(t) S(t) V(t)ᵀ` (orthonormal factors, `r ≤ min(m, n)`) solve the DLRA equation
`Ẏ = P(Y) Ȧ` on `[a, b]`, with `P(Y) = tangentProj U V` the tangent projector of the rank-`r`
manifold, and suppose the **gap** `σ_r(Y(t)) ≥ ρ > 0` along the DLRA solution.  If
`dist(A(t), M_{≤ r}) ≤ d` on `[a, b]`, `‖Ȧ‖ ≤ μ`, and the data are small,
`(4 √2 / ρ) (d + e^{(4 √2 / ρ) μ (b - a)} (2 ‖Y(a) - A(a)‖ + 3 d)) < 1`, then

  `‖Y(t) - A(t)‖ ≤ e^{(4 √2 / ρ) μ (t - a)} (2 ‖Y(a) - A(a)‖ + 3 d)`.

This is the bound `‖Y - A‖ ≤ C sup_s dist(A(s), M_r)` asked for in OP-OT-26, with `C` of
Koch–Lubich type (`e^{c μ T / ρ}`), under the gap for the DLRA solution `Y` rather than for the
best approximation of `A`.  Koch–Lubich (2007, Thm. 5.1) bound the error by `∫ ‖Ė‖`, which is not
controlled by `sup ‖E‖`.  The gap cannot be dropped and the bound cannot be made pointwise in
`dist(A(t), M_r)`: see the counterexamples `cxA_*` and `cxB_*` below. -/
theorem dlra_norm_sub_le_distLR {U : ℝ → Matrix m (Fin r) ℝ} {S : ℝ → Matrix (Fin r) (Fin r) ℝ}
    {V : ℝ → Matrix n (Fin r) ℝ} {Y A A' : ℝ → Matrix m n ℝ} {a b ρ μ d : ℝ} (hρ : 0 < ρ)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    (hYf : ∀ t ∈ Icc a b, Y t = U t * S t * (V t)ᵀ)
    (hU : ∀ t ∈ Icc a b, (U t)ᵀ * U t = 1) (hV : ∀ t ∈ Icc a b, (V t)ᵀ * V t = 1)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (Matrix.toEuclideanLin (Y t)).singularValues (r - 1))
    (hY : ODESolution (fun t _ => tangentProj (U t) (V t) (A' t)) Y a b)
    (hAc : ContinuousOn A (Icc a b)) (hA : ∀ t ∈ Ico a b, HasDerivWithinAt A (A' t) (Ici t) t)
    (hμ : ∀ t ∈ Ico a b, ‖A' t‖ ≤ μ) (hd : ∀ t ∈ Icc a b, distLR r (A t) ≤ d)
    (hsmall : 4 * √2 / ρ *
      (d + Real.exp (4 * √2 / ρ * μ * (b - a)) * (2 * ‖Y a - A a‖ + 3 * d)) < 1) :
    ∀ t ∈ Icc a b,
      ‖Y t - A t‖ ≤ Real.exp (4 * √2 / ρ * μ * (t - a)) * (2 * ‖Y a - A a‖ + 3 * d) := by
  have hγ : 0 ≤ 2 * √2 / ρ := by positivity
  have hK : ∀ x : ℝ, 2 * (2 * √2 / ρ) * μ * x = 4 * √2 / ρ * μ * x := fun x => by ring
  have hsmall' : 2 * (2 * √2 / ρ) *
      (d + Real.exp (2 * (2 * √2 / ρ) * μ * (b - a)) * (2 * ‖Y a - A a‖ + 3 * d)) < 1 := by
    rw [hK]; convert hsmall using 2; ring
  have h := norm_sub_le_of_infDist_le' (P := fun t => tangentProj (U t) (V t))
    (M := lowRankSet m n r) hY (fun t ht => isOrthProj_tangentProj (hU t ht) (hV t ht)) hAc hA hμ
    hγ (lowRankSet_nonempty r)
    (fun s hs t ht z => lip_tangentProj hρ (hYf s hs) (hYf t ht) (hU s hs) (hV s hs) (hU t ht)
      (hV t ht) (hσ s hs) z)
    (fun t ht B hB => by
      have h1 := curv_tangentProj hρ (hYf t ht) (hU t ht) (hV t ht) (hσ t ht) hrm hrn hB
      have h2 : 2 / ρ ≤ 2 * √2 / ρ := by
        apply div_le_div_of_nonneg_right _ hρ.le
        nlinarith [Real.one_lt_sqrt_two]
      calc ‖(1 - tangentProj (U t) (V t)) (B - Y t)‖ ≤ 2 / ρ * ‖B - Y t‖ ^ 2 := h1
        _ ≤ 2 * √2 / ρ * ‖B - Y t‖ ^ 2 := by gcongr)
    hd hsmall'
  intro t ht
  rw [← hK]
  exact h t ht

end MatrixVersion

/-! ### Counterexamples on `2 × 2` matrices -/

section Counterexamples

open Frobenius

/-- `e₁ = (1, 0)ᵀ`. -/
def e₁ : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

/-- `e₂ = (0, 1)ᵀ`. -/
def e₂ : Matrix (Fin 2) (Fin 1) ℝ := !![0; 1]

/-- `E₁₁ = e₁ e₁ᵀ`. -/
def E₁₁ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- `E₂₂ = e₂ e₂ᵀ`. -/
def E₂₂ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 1]

/-- `E₁₂ = e₁ e₂ᵀ + e₂ e₁ᵀ`. -/
def E₁₂ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

theorem e₁_orth : e₁ᵀ * e₁ = 1 := by
  ext i j; fin_cases i; fin_cases j; simp [e₁, Matrix.mul_apply, Fin.sum_univ_two]

theorem norm_E₁₁ : ‖E₁₁‖ = 1 := by
  rw [norm_def]; simp [E₁₁, Fin.sum_univ_two]

theorem norm_E₂₂ : ‖E₂₂‖ = 1 := by
  rw [norm_def]; simp [E₂₂, Fin.sum_univ_two]

theorem rank_smul_E₁₁_le (c : ℝ) : (c • E₁₁).rank ≤ 1 := by
  have : c • E₁₁ = Matrix.vecMulVec ![c, 0] ![1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [E₁₁, Matrix.vecMulVec_apply]
  rw [this]; exact Matrix.rank_vecMulVec_le _ _

theorem rank_smul_E₂₂_le (c : ℝ) : (c • E₂₂).rank ≤ 1 := by
  have : c • E₂₂ = Matrix.vecMulVec ![0, c] ![0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [E₂₂, Matrix.vecMulVec_apply]
  rw [this]; exact Matrix.rank_vecMulVec_le _ _

/-! #### Counterexample A: a stationary DLRA solution and a crossing of singular values

`A(t) = diag(δ, t)`, `Y(0) = A(0) = diag(δ, 0)`.  The velocity `Ȧ = e₂ e₂ᵀ` is normal to the
rank-one manifold at `Y`, so the DLRA solution is stationary, `Y(t) = diag(δ, 0)`, while the
singular values `δ` and `t` of `A(t)` cross at `t = δ`. -/

/-- `A(t) = diag(δ, t)`. -/
def cxA_A (δ t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := δ • E₁₁ + t • E₂₂

/-- `Y = diag(δ, 0)`. -/
def cxA_Y (δ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := δ • E₁₁

/-- `Y = e₁ (δ) e₁ᵀ`: rank one with singular value `δ`. -/
theorem cxA_Y_eq (δ : ℝ) : cxA_Y δ = e₁ * (δ • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * e₁ᵀ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cxA_Y, E₁₁, e₁, Matrix.mul_apply]

theorem cxA_hasDerivAt_A (δ t : ℝ) : HasDerivAt (cxA_A δ) E₂₂ t := by
  have := ((hasDerivAt_id t).smul_const E₂₂).const_add (δ • E₁₁)
  have hA : cxA_A δ = fun t => δ • E₁₁ + t • E₂₂ := rfl
  rw [hA]
  simpa using this

/-- `Ȧ = e₂ e₂ᵀ` is normal at `Y = diag(δ, 0)`. -/
theorem tangentProj_e₁_E₂₂ : tangentProj e₁ e₁ E₂₂ = 0 := by
  rw [tangentProj_apply]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [e₁, E₂₂, Matrix.vecHead,
      Matrix.vecTail]

/-- **The DLRA solution is stationary**: `Y(t) ≡ diag(δ, 0)` solves `Ẏ = P(Y) Ȧ` with
`Ȧ = e₂ e₂ᵀ`, `P(Y) = tangentProj e₁ e₁`, on every `[0, T]`. -/
theorem cxA_odeSolution (δ T : ℝ) :
    ODESolution (fun _ _ => tangentProj e₁ e₁ E₂₂) (fun _ => cxA_Y δ) 0 T :=
  ⟨continuousOn_const, fun t _ => by
    rw [tangentProj_e₁_E₂₂]; exact (hasDerivAt_const t _).hasDerivWithinAt⟩

theorem cxA_init (δ : ℝ) : cxA_Y δ = cxA_A δ 0 := by simp [cxA_Y, cxA_A]

/-- The DLRA error is `‖Y(t) - A(t)‖ = t`, exactly the trivial bound `∫₀ᵗ ‖Ȧ‖ = t`. -/
theorem cxA_norm_sub (δ t : ℝ) : ‖cxA_Y δ - cxA_A δ t‖ = |t| := by
  have : cxA_Y δ - cxA_A δ t = (-t) • E₂₂ := by
    simp only [cxA_Y, cxA_A, neg_smul]; abel
  rw [this, norm_smul, norm_E₂₂, mul_one, Real.norm_eq_abs, abs_neg]

/-- **The best rank-one error is `min(δ, t)`**: `dist(A(t), M_{≤ 1}) = min δ t`. -/
theorem cxA_distLR {δ t : ℝ} (hδ : 0 ≤ δ) (ht : 0 ≤ t) : distLR 1 (cxA_A δ t) = min δ t := by
  apply le_antisymm
  · rcases le_total δ t with h | h
    · rw [min_eq_left h]
      calc distLR 1 (cxA_A δ t) ≤ ‖cxA_A δ t - t • E₂₂‖ :=
            distLR_le_norm_sub (rank_smul_E₂₂_le t)
        _ = δ := by
            rw [show cxA_A δ t - t • E₂₂ = δ • E₁₁ by simp [cxA_A], norm_smul, norm_E₁₁,
              mul_one, Real.norm_eq_abs, abs_of_nonneg hδ]
    · rw [min_eq_right h]
      calc distLR 1 (cxA_A δ t) ≤ ‖cxA_A δ t - δ • E₁₁‖ :=
            distLR_le_norm_sub (rank_smul_E₁₁_le δ)
        _ = t := by
            rw [show cxA_A δ t - δ • E₁₁ = t • E₂₂ by simp [cxA_A], norm_smul, norm_E₂₂,
              mul_one, Real.norm_eq_abs, abs_of_nonneg ht]
  · have hdiag : cxA_A δ t = Matrix.diagonal ![δ, t] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [cxA_A, E₁₁, E₂₂]
    rw [hdiag]
    refine le_distLR_diagonal (le_min hδ ht) (fun i => ?_) (by simp)
    fin_cases i
    · simp [abs_of_nonneg hδ]
    · simp [abs_of_nonneg ht]

/-- **Blow-up of the ratio after the crossing.**  For `t ≥ δ > 0`,
`‖Y(t) - A(t)‖ = (t / δ) · dist(A(t), M_{≤ 1})`: the ratio of the DLRA error to the best
rank-one error grows linearly, at rate `1/δ = 1 / (initial gap)`. -/
theorem cxA_ratio {δ t : ℝ} (hδ : 0 < δ) (ht : δ ≤ t) :
    ‖cxA_Y δ - cxA_A δ t‖ = (t / δ) * distLR 1 (cxA_A δ t) := by
  rw [cxA_norm_sub, cxA_distLR hδ.le (hδ.le.trans ht), min_eq_left ht,
    abs_of_nonneg (hδ.le.trans ht)]
  field_simp

/-- Along the whole path the best rank-one error stays `≤ δ`, so also the ratio
`‖Y(t) - A(t)‖ / sup_{s ≤ t} dist(A(s), M_{≤ 1}) ≥ t / δ` is unbounded. -/
theorem cxA_sup_distLR {δ s : ℝ} (hδ : 0 ≤ δ) (hs : 0 ≤ s) : distLR 1 (cxA_A δ s) ≤ δ := by
  rw [cxA_distLR hδ hs]; exact min_le_left _ _

/-! #### Counterexample B: the error has memory (pointwise quasi-optimality fails under a gap)

`Y(t) = w(t) w(t)ᵀ` with `w(t) = (cos t, sin t)`, and `A(t) = Y(t) + E(t)` where
`Ė(t) = α (1 - 2 cos 2t) w⊥(t) w⊥(t)ᵀ` is normal at `Y(t)`.  Then `Y` solves the DLRA equation
exactly, `A(0) = Y(0)`, `σ₁(Y) ≡ 1`, `A(t)` stays within `3 |α| t` of the rank-one manifold, but
`A(π) = (1 + α π) e₁ e₁ᵀ` has rank one while `‖Y(π) - A(π)‖ = |α| π`. -/

/-- `w(t) = (cos t, sin t)ᵀ`. -/
noncomputable def cw (t : ℝ) : Matrix (Fin 2) (Fin 1) ℝ := Real.cos t • e₁ + Real.sin t • e₂

/-- `w⊥(t) = ẇ(t) = (-sin t, cos t)ᵀ`. -/
noncomputable def cwd (t : ℝ) : Matrix (Fin 2) (Fin 1) ℝ := (-Real.sin t) • e₁ + Real.cos t • e₂

theorem hasDerivAt_cw (t : ℝ) : HasDerivAt cw (cwd t) t :=
  ((Real.hasDerivAt_cos t).smul_const e₁).add ((Real.hasDerivAt_sin t).smul_const e₂)

theorem cw_orth (t : ℝ) : (cw t)ᵀ * cw t = 1 := by
  ext i j; fin_cases i; fin_cases j
  simp [cw, e₁, e₂, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination Real.cos_sq_add_sin_sq t

theorem cw_cwd (t : ℝ) : (cw t)ᵀ * cwd t = 0 := by
  ext i j; fin_cases i; fin_cases j
  simp [cw, cwd, e₁, e₂, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem cwd_cw (t : ℝ) : (cwd t)ᵀ * cw t = 0 := by
  ext i j; fin_cases i; fin_cases j
  simp [cw, cwd, e₁, e₂, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem norm_cw (t : ℝ) : ‖cw t‖ = 1 := by
  rw [norm_def]
  simp [cw, e₁, e₂, Fin.sum_univ_two]

theorem norm_cwd_mul_transpose (t : ℝ) : ‖cwd t * (cwd t)ᵀ‖ = 1 := by
  rw [norm_def]
  have h : ∑ i, ∑ j, (cwd t * (cwd t)ᵀ) i j ^ 2 = 1 := by
    simp [cwd, e₁, e₂, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (Real.sin t ^ 2 + Real.cos t ^ 2 + 1) * Real.sin_sq_add_cos_sq t
  rw [h, Real.sqrt_one]

/-- `Y(t) = w(t) w(t)ᵀ`. -/
noncomputable def cxB_Y (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := cw t * (cw t)ᵀ

/-- `Ẏ(t) = w⊥ wᵀ + w w⊥ᵀ`. -/
noncomputable def cxB_Y' (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := cwd t * (cw t)ᵀ + cw t * (cwd t)ᵀ

theorem cxB_hasDerivAt_Y (t : ℝ) : HasDerivAt cxB_Y (cxB_Y' t) t :=
  hasDerivAt_mul (hasDerivAt_cw t) (hasDerivAt_transpose (hasDerivAt_cw t))

/-- `Y(t) = w(t) · 1 · w(t)ᵀ` with `w(t)ᵀ w(t) = 1`: a rank-one matrix with singular value `1`
for every `t` (the gap on the DLRA solution is `ρ = 1`). -/
theorem cxB_Y_factor (t : ℝ) :
    cxB_Y t = cw t * (1 : Matrix (Fin 1) (Fin 1) ℝ) * (cw t)ᵀ ∧ (cw t)ᵀ * cw t = 1 :=
  ⟨by rw [cxB_Y, Matrix.mul_one], cw_orth t⟩

theorem rank_cxB_Y_le (t : ℝ) : (cxB_Y t).rank ≤ 1 :=
  (Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_card_width (cw t))

/-- The entries of `E(t)`: `∫₀ᵗ (1 - 2 cos 2u) sin² u du = t - ¾ sin 2t + ⅛ sin 4t`, written in
`sin t`, `cos t`. -/
noncomputable def f₁ (t : ℝ) : ℝ :=
  t - 3 / 2 * (Real.sin t * Real.cos t) +
    1 / 2 * (Real.sin t * Real.cos t) * (Real.cos t ^ 2 - Real.sin t ^ 2)

/-- `-∫₀ᵗ (1 - 2 cos 2u) sin u cos u du = -¼ (1 - cos 2t) + ⅛ (1 - cos 4t)`. -/
noncomputable def f₂ (t : ℝ) : ℝ := -(Real.sin t ^ 2) / 2 + Real.sin t ^ 2 * Real.cos t ^ 2

/-- `∫₀ᵗ (1 - 2 cos 2u) cos² u du = -¼ sin 2t - ⅛ sin 4t`. -/
noncomputable def f₃ (t : ℝ) : ℝ :=
  -(Real.sin t * Real.cos t) / 2 - (Real.sin t * Real.cos t) * (Real.cos t ^ 2 - Real.sin t ^ 2) / 2

/-- `E(t) = α ∫₀ᵗ (1 - 2 cos 2u) w⊥(u) w⊥(u)ᵀ du`. -/
noncomputable def cxB_E (α t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  α • (f₁ t • E₁₁ + f₂ t • E₁₂ + f₃ t • E₂₂)

/-- `Ė(t) = α (1 - 2 cos 2t) w⊥(t) w⊥(t)ᵀ`, with `cos 2t = cos² t - sin² t`. -/
noncomputable def cxB_Ed (α t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (α * (1 - 2 * (Real.cos t ^ 2 - Real.sin t ^ 2))) • (cwd t * (cwd t)ᵀ)

/-- `A(t) = Y(t) + E(t)`. -/
noncomputable def cxB_A (α t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := cxB_Y t + cxB_E α t

/-- `Ȧ(t) = Ẏ(t) + Ė(t)`. -/
noncomputable def cxB_A' (α t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := cxB_Y' t + cxB_Ed α t

theorem cxB_hasDerivAt_E (α t : ℝ) : HasDerivAt (cxB_E α) (cxB_Ed α t) t := by
  have hs := Real.hasDerivAt_sin t
  have hc := Real.hasDerivAt_cos t
  have hsc := hs.mul hc
  have hc2 := hc.pow 2
  have hs2 := hs.pow 2
  have h1 : HasDerivAt f₁ _ t :=
    ((hasDerivAt_id t).sub (hsc.const_mul (3 / 2))).add ((hsc.const_mul (1 / 2)).mul (hc2.sub hs2))
  have h2 : HasDerivAt f₂ _ t := ((hs2.neg).div_const 2).add (hs2.mul hc2)
  have h3 : HasDerivAt f₃ _ t :=
    ((hsc.neg).div_const 2).sub ((hsc.mul (hc2.sub hs2)).div_const 2)
  have h : HasDerivAt (cxB_E α) _ t :=
    (((h1.smul_const E₁₁).add (h2.smul_const E₁₂)).add (h3.smul_const E₂₂)).const_smul α
  refine h.congr_deriv ?_
  have hpyth := Real.sin_sq_add_cos_sq t
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [cxB_Ed, cwd, e₁, e₂, E₁₁, E₁₂, E₂₂, Matrix.vecHead,
      Matrix.vecTail]
  · linear_combination (-(α * (3 * Real.sin t ^ 2 - Real.cos t ^ 2 + 2) / 2)) * hpyth
  · ring
  · ring
  · linear_combination (-(α * (Real.sin t ^ 2 - 3 * Real.cos t ^ 2) / 2)) * hpyth

theorem cxB_hasDerivAt_A (α t : ℝ) : HasDerivAt (cxB_A α) (cxB_A' α t) t :=
  (cxB_hasDerivAt_Y t).add (cxB_hasDerivAt_E α t)

/-- **`Y` solves the DLRA equation**: `P(Y(t)) Ȧ(t) = Ẏ(t)`, because `Ė` is normal at `Y`. -/
theorem cxB_tangentProj (α t : ℝ) : tangentProj (cw t) (cw t) (cxB_A' α t) = cxB_Y' t := by
  have h1 : ∀ X : Matrix (Fin 1) (Fin 2) ℝ, (cw t)ᵀ * (cw t * X) = X := fun X => by
    rw [← Matrix.mul_assoc, cw_orth, Matrix.one_mul]
  have h2 : ∀ X : Matrix (Fin 1) (Fin 2) ℝ, (cw t)ᵀ * (cwd t * X) = 0 := fun X => by
    rw [← Matrix.mul_assoc, cw_cwd, Matrix.zero_mul]
  have h3 : ∀ X : Matrix (Fin 1) (Fin 2) ℝ, (cwd t)ᵀ * (cw t * X) = 0 := fun X => by
    rw [← Matrix.mul_assoc, cwd_cw, Matrix.zero_mul]
  rw [tangentProj_apply]
  unfold cxB_A' cxB_Y' cxB_Ed
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
    h1, h2, h3, Matrix.mul_zero, smul_zero, add_zero, zero_add]
  abel

/-- **The DLRA solution** on `[0, T]`, in the form of `dlra_norm_sub_le_distLR`:
`Ẏ = tangentProj (w t) (w t) Ȧ(t)`. -/
theorem cxB_odeSolution (α T : ℝ) :
    ODESolution (fun t _ => tangentProj (cw t) (cw t) (cxB_A' α t)) cxB_Y 0 T :=
  ⟨fun t _ => (cxB_hasDerivAt_Y t).continuousAt.continuousWithinAt, fun t _ => by
    rw [cxB_tangentProj]; exact (cxB_hasDerivAt_Y t).hasDerivWithinAt⟩

/-- Exact initial data: `A(0) = Y(0)`. -/
theorem cxB_init (α : ℝ) : cxB_A α 0 = cxB_Y 0 := by
  simp [cxB_A, cxB_E, f₁, f₂, f₃]

theorem cxB_Y_pi : cxB_Y Real.pi = E₁₁ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [cxB_Y, cw, e₁, e₂, E₁₁, Matrix.mul_apply]

/-- **`A(π)` has rank one**: `A(π) = (1 + α π) e₁ e₁ᵀ`. -/
theorem cxB_A_pi (α : ℝ) : cxB_A α Real.pi = (1 + α * Real.pi) • E₁₁ := by
  rw [cxB_A, cxB_Y_pi]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [cxB_E, f₁, f₂, f₃, E₁₁, E₁₂, E₂₂]

/-- `dist(A(π), M_{≤ 1}) = 0`. -/
theorem cxB_distLR_pi (α : ℝ) : distLR 1 (cxB_A α Real.pi) = 0 := by
  rw [cxB_A_pi]; exact distLR_eq_zero_of_rank_le (rank_smul_E₁₁_le _)

/-- **The DLRA error at `t = π` is `|α| π > 0`** although the best rank-one error vanishes:
the ratio `‖Y(π) - A(π)‖ / dist(A(π), M_{≤ 1})` is `+∞`. -/
theorem cxB_norm_sub_pi (α : ℝ) : ‖cxB_Y Real.pi - cxB_A α Real.pi‖ = |α| * Real.pi := by
  rw [cxB_Y_pi, cxB_A_pi, show E₁₁ - (1 + α * Real.pi) • E₁₁ = (-(α * Real.pi)) • E₁₁ by
    rw [neg_smul, add_smul, one_smul]; abel, norm_smul, norm_E₁₁, mul_one, Real.norm_eq_abs,
    abs_neg, abs_mul, abs_of_pos Real.pi_pos]

/-- `‖Ė(t)‖ ≤ 3 |α|`. -/
theorem norm_cxB_Ed_le (α t : ℝ) : ‖cxB_Ed α t‖ ≤ 3 * |α| := by
  rw [cxB_Ed, norm_smul, norm_cwd_mul_transpose, mul_one, Real.norm_eq_abs, abs_mul]
  have hpyth := Real.sin_sq_add_cos_sq t
  have h1 : |1 - 2 * (Real.cos t ^ 2 - Real.sin t ^ 2)| ≤ 3 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (Real.sin t), sq_nonneg (Real.cos t)]
  calc |α| * |1 - 2 * (Real.cos t ^ 2 - Real.sin t ^ 2)| ≤ |α| * 3 := by gcongr
    _ = 3 * |α| := by ring

/-- **`A` stays near the manifold**: `‖A(t) - Y(t)‖ = ‖E(t)‖ ≤ 3 |α| t` for `t ≥ 0`. -/
theorem norm_cxB_E_le {α t : ℝ} (ht : 0 ≤ t) : ‖cxB_E α t‖ ≤ 3 * |α| * t := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := cxB_E α) (f' := cxB_Ed α)
    (s := Icc 0 t) (C := 3 * |α|)
    (fun u _ => (cxB_hasDerivAt_E α u).hasDerivWithinAt) (fun u _ => norm_cxB_Ed_le α u)
    (convex_Icc 0 t) (left_mem_Icc.2 ht) (right_mem_Icc.2 ht)
  have h0 : cxB_E α 0 = 0 := by simp [cxB_E, f₁, f₂, f₃]
  rw [h0, sub_zero, sub_zero, Real.norm_eq_abs, abs_of_nonneg ht] at h
  exact h

/-- `dist(A(t), M_{≤ 1}) ≤ 3 |α| t`: the best rank-one error is `O(α)` on `[0, π]`. -/
theorem cxB_distLR_le {α t : ℝ} (ht : 0 ≤ t) : distLR 1 (cxB_A α t) ≤ 3 * |α| * t :=
  (distLR_le_norm_sub (rank_cxB_Y_le t)).trans
    (by rw [cxB_A, add_sub_cancel_left]; exact norm_cxB_E_le ht)

/-- `‖A(t) w(t)‖ ≥ 1 - 3 |α| t`: the largest singular value of `A(t)` stays close to `1`, so the
gap `σ₁(A) - σ₂(A) ≥ 1 - 6 |α| t` holds along the whole path (`σ₂ = dist(A, M_{≤ 1})` for
`2 × 2` matrices). -/
theorem norm_cxB_A_mul_cw {α t : ℝ} (ht : 0 ≤ t) : 1 - 3 * |α| * t ≤ ‖cxB_A α t * cw t‖ := by
  have hA : cxB_A α t * cw t = cw t + cxB_E α t * cw t := by
    rw [cxB_A, Matrix.add_mul, cxB_Y, Matrix.mul_assoc, cw_orth, Matrix.mul_one]
  have hE : ‖cxB_E α t * cw t‖ ≤ 3 * |α| * t := by
    calc ‖cxB_E α t * cw t‖ ≤ ‖cxB_E α t‖ * ‖cw t‖ := norm_mul_le _ _
      _ = ‖cxB_E α t‖ := by rw [norm_cw, mul_one]
      _ ≤ 3 * |α| * t := norm_cxB_E_le ht
  have htri := norm_sub_le (cw t + cxB_E α t * cw t) (cxB_E α t * cw t)
  rw [add_sub_cancel_right, norm_cw] at htri
  rw [hA]
  linarith

/-! #### Counterexample C: the gap must hold along the whole trajectory

`A_δ(t) = diag(δ + φ(1 - t), φ(t - 1))` with `φ` a smooth transition (`φ = 0` on `(-∞, 0]`,
`φ = 1` on `[1, ∞)`).  The DLRA solution is `Y_δ(t) = diag(δ + φ(1 - t), 0)`, with
`Y_δ(0) = A_δ(0) = diag(1 + δ, 0)` (gap `1 + δ ≥ 1` at the start), the velocity `Ȧ_δ` does not
depend on `δ`, and `dist(A_δ(s), M_{≤ 1}) ≤ δ` for all `s ≥ 0`, yet `‖Y_δ(2) - A_δ(2)‖ = 1`.
So no bound `‖Y - A‖ ≤ C(T, ‖Ȧ‖, σ_r(Y(0))) sup_s dist(A(s), M_r)` can hold: the gap in
`dlra_norm_sub_le_distLR` must be assumed along the whole trajectory. -/

/-- The smooth transition `φ`. -/
noncomputable def φ : ℝ → ℝ := Real.smoothTransition

theorem hasDerivAt_φ (x : ℝ) : HasDerivAt φ (deriv φ x) x :=
  ((Real.smoothTransition.contDiff (n := 1)).differentiable_one x).hasDerivAt

/-- `a_δ(t) = δ + φ(1 - t)`: the surviving singular value of `Y_δ(t)`. -/
noncomputable def cxC_a (δ t : ℝ) : ℝ := δ + φ (1 - t)

/-- `b(t) = φ(t - 1)`: the singular value of `A_δ(t)` that the DLRA solution never sees. -/
noncomputable def cxC_b (t : ℝ) : ℝ := φ (t - 1)

/-- `A_δ(t) = diag(a_δ(t), b(t))`. -/
noncomputable def cxC_A (δ t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := cxA_A (cxC_a δ t) (cxC_b t)

/-- `Y_δ(t) = diag(a_δ(t), 0)`. -/
noncomputable def cxC_Y (δ t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := cxA_Y (cxC_a δ t)

/-- `Ȧ(t) = diag(-φ'(1 - t), φ'(t - 1))`; it does not depend on `δ`. -/
noncomputable def cxC_A' (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (-deriv φ (1 - t)) • E₁₁ + deriv φ (t - 1) • E₂₂

theorem cxC_hasDerivAt_a (δ t : ℝ) : HasDerivAt (cxC_a δ) (-deriv φ (1 - t)) t := by
  have h := ((hasDerivAt_φ (1 - t)).comp t ((hasDerivAt_id t).const_sub 1)).const_add δ
  have ha : cxC_a δ = fun t => δ + φ (1 - t) := rfl
  rw [ha]
  simpa using h

theorem cxC_hasDerivAt_b (t : ℝ) : HasDerivAt cxC_b (deriv φ (t - 1)) t := by
  have h := (hasDerivAt_φ (t - 1)).comp t ((hasDerivAt_id t).sub_const 1)
  have hb : cxC_b = fun t => φ (t - 1) := rfl
  rw [hb, mul_one] at *
  exact h

/-- `Ȧ_δ(t) = cxC_A' t` for every `δ`. -/
theorem cxC_hasDerivAt_A (δ t : ℝ) : HasDerivAt (cxC_A δ) (cxC_A' t) t :=
  ((cxC_hasDerivAt_a δ t).smul_const E₁₁).add ((cxC_hasDerivAt_b t).smul_const E₂₂)

/-- The tangent projector at `diag(a, 0)` keeps the `(1,1)` entry of a diagonal matrix. -/
theorem tangentProj_e₁_diag (a b : ℝ) : tangentProj e₁ e₁ (a • E₁₁ + b • E₂₂) = a • E₁₁ := by
  rw [tangentProj_apply]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [e₁, E₁₁, E₂₂,
      Matrix.vecHead, Matrix.vecTail]

/-- **`Y_δ` solves the DLRA equation** `Ẏ = P(Y) Ȧ_δ` on `[0, T]`. -/
theorem cxC_odeSolution (δ T : ℝ) :
    ODESolution (fun t _ => tangentProj e₁ e₁ (cxC_A' t)) (cxC_Y δ) 0 T :=
  ⟨fun t _ => ((cxC_hasDerivAt_a δ t).smul_const E₁₁).continuousAt.continuousWithinAt,
    fun t _ => by
      rw [cxC_A', tangentProj_e₁_diag]
      exact ((cxC_hasDerivAt_a δ t).smul_const E₁₁).hasDerivWithinAt⟩

/-- Exact initial data with gap `1 + δ`: `Y_δ(0) = A_δ(0) = diag(1 + δ, 0)`. -/
theorem cxC_init (δ : ℝ) : cxC_Y δ 0 = cxC_A δ 0 ∧ cxC_a δ 0 = 1 + δ := by
  have hb : cxC_b 0 = 0 := Real.smoothTransition.zero_of_nonpos (by norm_num)
  have ha : cxC_a δ 0 = 1 + δ := by
    rw [cxC_a, φ, sub_zero, Real.smoothTransition.one, add_comm]
  exact ⟨by rw [cxC_Y, cxC_A, hb, cxA_init], ha⟩

/-- The surviving singular value stays `≥ δ`: `Y_δ(t) = e₁ (a_δ t) e₁ᵀ` with `a_δ(t) ≥ δ`. -/
theorem cxC_a_ge (δ t : ℝ) : δ ≤ cxC_a δ t :=
  le_add_of_nonneg_right (Real.smoothTransition.nonneg _)

theorem cxC_b_nonneg (t : ℝ) : 0 ≤ cxC_b t := Real.smoothTransition.nonneg _

/-- The DLRA error is `b(t) = φ(t - 1)`; at `t = 2` it equals `1`. -/
theorem cxC_norm_sub (δ t : ℝ) : ‖cxC_Y δ t - cxC_A δ t‖ = cxC_b t := by
  rw [cxC_Y, cxC_A, cxA_norm_sub, abs_of_nonneg (cxC_b_nonneg t)]

theorem cxC_norm_sub_two (δ : ℝ) : ‖cxC_Y δ 2 - cxC_A δ 2‖ = 1 := by
  rw [cxC_norm_sub, cxC_b, φ]
  exact Real.smoothTransition.one_of_one_le (by norm_num)

/-- **The best rank-one error never exceeds `δ`**: `dist(A_δ(s), M_{≤ 1}) ≤ δ` for every `s`. -/
theorem cxC_distLR_le {δ s : ℝ} (hδ : 0 ≤ δ) : distLR 1 (cxC_A δ s) ≤ δ := by
  rw [cxC_A, cxA_distLR (hδ.trans (cxC_a_ge δ s)) (cxC_b_nonneg s)]
  rcases le_total s 1 with h | h
  · have hb : cxC_b s = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    rw [hb]; exact (min_le_right _ _).trans hδ
  · have ha : cxC_a δ s = δ := by
      rw [cxC_a, φ, Real.smoothTransition.zero_of_nonpos (by linarith), add_zero]
    rw [ha]; exact min_le_left _ _

end Counterexamples

end LeanDLRA.Novel.OpOT26
