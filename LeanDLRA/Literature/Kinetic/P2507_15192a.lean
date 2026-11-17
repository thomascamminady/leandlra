import LeanDLRA.Foundations.Galerkin
import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.Matrix.Projectors
import LeanDLRA.OpenProblems.Stability.Part1d
import LeanDLRA.Stability.Energy

/-!
# Results of arXiv 2507.15192: stability of projector-splitting integrators (Zhang–Hu)

This module formalises the forward Euler discretise-then-project projector-splitting integrator
(DtP–PSI) of Zhang and Hu for the periodic model `U̇ = -(1/(2Δx)) M₁ U A - (λ/(2Δx)) M₂ U`, with
the concrete shift matrices `shiftPlus`, `shiftMinus` on `Fin N`, the differences `M₁`, `M₂`, the
Rusanov Lax–Friedrichs field `fLF` and the factored substeps `kStep`, `sStep`, `lStep`, `dtpStep`
(over any field with involution: `ℝ` for the scheme, `ℂ` for the Fourier analysis).  It proves
Lemma 3.4 (`lemma_3_4`); Theorem 3.3 for this concrete scheme (`dtp_L2_stable`, for all `n`:
`dtp_L2_stable_iter`), through `dtpStep_eq_kslEulerStep`, which identifies the scheme with the
library's `kslEulerStep`, and the abstract form `ksl_stable_of_transport`, which feeds the substep
estimates (3.12), (3.18) into `kslSplitStep_energy_le`; Prop. 3.2 (`dtp_singleMode_factor`,
`ampP_normSq`, `ampP_normSq_of_max`, `hDtP_le_one`, `one_lt_hDtP`, `hDtP_iff`,
`dtp_amplification_iff`, `dtp_mode_stable`); and Prop. 4.2 for the parabolic θ-scheme `IsThetaStep`
(`theta_singleMode`, `theta_singleMode_exists`, `gTheta_zero`, `gTheta_tendsto`, `theta_unbounded`).
Differences from the paper.  Lemma 3.4 holds on any real Hilbert space, also for `ν = 0`, and
`W ≻ 0` comes with the bound `W ⪰ 1/9`; its proof is a direct quadratic-form computation from
`(I-E)*(I-E) ⪯ H` and `(I-E)(I-E)* ⪯ H`, without the paper's spectral mapping step.  Theorem 3.3
allows every `λ ≥ ‖A‖₂` (the paper's `λ_max = ‖A‖₂` is the case of equality) and runs on the full
space with the compression `P T P` instead of the reduced `r × r` operators; the seminorm
`|U|²_{1,x} = ⟪U, M₂ U⟫` is written `‖(I - E₊) U‖²`, using `M₂ = (I - E₊)ᵀ (I - E₊)`.  In Prop. 3.2
the modes are complex, so `ᴴ` replaces `ᵀ` (the only reading under which `x_m` is orthonormal); the
paper's tacit assumption that the projectors fix the mode is not assumed, the formula is proved for
every rank, every `V` and every orthonormal `X` with `K¹ = X S⁽¹⁾`, which includes real bases of
`span(Re x_m, Im x_m)`.  The stable direction of the threshold uses the library's
`dtp_singleMode_stable`.  In Prop. 4.2 the mode has rank one (`X⁰ = x_m`, `V⁰ = v_k`, `r = Unit`),
every solution of the implicit equations is treated (uniqueness and existence are proved, for
`θ ψ ≠ 1`), and the blow-up holds for every `θ > 0`: the paper's exclusion `θ ≠ 1/2` is not needed.
The case `θ = 1` is in the library as `allBackwardKSL_amplification` and `allBackwardKSL_unstable`.
The PtD results (Prop. 3.5, Thm 3.6, Lemma 3.7) are not listed for this module and not treated.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2507_15192

section Abstract

variable {𝓧 : Type*} [NormedAddCommGroup 𝓧] [InnerProductSpace ℝ 𝓧]

private theorem convex_step {y s : 𝓧} {ν q : ℝ} (hs : ‖s‖ ≤ ‖y‖)
    (hq : q = 2 * ‖y‖ ^ 2 - 2 * ⟪y, s⟫) :
    ‖(1 - ν) • y + ν • s‖ ^ 2 ≤ ‖y‖ ^ 2 - ν * (1 - ν) * q := by
  have h1 : ‖(1 - ν) • y + ν • s‖ ^ 2 =
      (1 - ν) ^ 2 * ‖y‖ ^ 2 + 2 * (ν * (1 - ν)) * ⟪y, s⟫ + ν ^ 2 * ‖s‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
    ring
  have h2 : ‖s‖ ^ 2 ≤ ‖y‖ ^ 2 := by gcongr
  rw [h1, hq]
  nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg ν)]

private theorem lemma34_form [CompleteSpace 𝓧] (E : 𝓧 →L[ℝ] 𝓧) (hE : ‖E‖ ≤ 1) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν ≤ 1 / 3) (x : 𝓧) :
    let H : 𝓧 →L[ℝ] 𝓧 := (2 : ℝ) • 1 - (E + ContinuousLinearMap.adjoint E)
    let y := x + ν • (x - E x)
    ‖y‖ ^ 2 - ν * (1 - ν) * ⟪y, H y⟫ ≤ ‖x‖ ^ 2 + ν * (1 - ν) * ⟪x, H x⟫ := by
  intro H y
  set Es := ContinuousLinearMap.adjoint E with hEs
  have hEb : ∀ z, ‖E z‖ ≤ ‖z‖ := fun z => by
    simpa using E.le_of_opNorm_le hE z
  have hEsb : ∀ z, ‖Es z‖ ≤ ‖z‖ := fun z => by
    have : ‖Es‖ ≤ 1 := by rw [hEs, LinearIsometryEquiv.norm_map]; exact hE
    simpa using Es.le_of_opNorm_le this z
  have hHa : ∀ z, H z = (z - E z) + (z - Es z) := fun z => by
    simp only [H, sub_apply, smul_apply, one_apply_eq_self, add_apply, ← hEs]
    module
  have hadj : ∀ u v, ⟪u, Es v⟫ = ⟪E u, v⟫ := fun u v => by
    rw [hEs, ContinuousLinearMap.adjoint_inner_right]
  have hq : ∀ z, ⟪z, H z⟫ = 2 * ‖z‖ ^ 2 - 2 * ⟪z, E z⟫ := fun z => by
    rw [hHa, inner_add_right, inner_sub_right, inner_sub_right, hadj, real_inner_self_eq_norm_sq,
      real_inner_comm z (E z)]
    ring
  have hsym : ∀ u v, ⟪u, H v⟫ = ⟪H u, v⟫ := fun u v => by
    have h1 : ⟪Es u, v⟫ = ⟪u, E v⟫ := by
      rw [real_inner_comm, hadj, real_inner_comm]
    rw [hHa, hHa, inner_add_right, inner_add_left, inner_sub_right, inner_sub_right,
      inner_sub_left, inner_sub_left, hadj, h1]
    ring
  set b := x - E x with hb
  set c := x - Es x with hc
  have hBq : ‖b‖ ^ 2 ≤ ⟪x, H x⟫ := by
    rw [hq, hb, norm_sub_sq_real]
    have : ‖E x‖ ^ 2 ≤ ‖x‖ ^ 2 := by gcongr; exact hEb x
    linarith
  have hCq : ‖c‖ ^ 2 ≤ ⟪x, H x⟫ := by
    rw [hq, hc, norm_sub_sq_real, hadj, real_inner_comm x (E x)]
    have : ‖Es x‖ ^ 2 ≤ ‖x‖ ^ 2 := by gcongr; exact hEsb x
    linarith
  have hqb : 0 ≤ ⟪b, H b⟫ := by
    rw [hq]
    have h1 : ⟪b, E b⟫ ≤ ‖b‖ * ‖E b‖ := real_inner_le_norm _ _
    have h2 : ‖b‖ * ‖E b‖ ≤ ‖b‖ * ‖b‖ := by gcongr; exact hEb b
    nlinarith
  have hxb : 2 * ⟪x, b⟫ = ⟪x, H x⟫ := by
    rw [hq, hb, inner_sub_right, real_inner_self_eq_norm_sq]
    ring
  have hy1 : ‖y‖ ^ 2 = ‖x‖ ^ 2 + ν * ⟪x, H x⟫ + ν ^ 2 * ‖b‖ ^ 2 := by
    change ‖x + ν • b‖ ^ 2 = _
    rw [norm_add_sq_real, norm_smul, real_inner_smul_right, mul_pow, Real.norm_eq_abs, sq_abs,
      ← hxb]
    ring
  have hHxe : H x = b + c := hHa x
  have hy2 : ⟪y, H y⟫ = ⟪x, H x⟫ + 2 * ν * (‖b‖ ^ 2 + ⟪b, c⟫) + ν ^ 2 * ⟪b, H b⟫ := by
    have h1 : ⟪x, H b⟫ = ⟪b, H x⟫ := by rw [hsym, real_inner_comm]
    have h2 : ⟪b, H x⟫ = ‖b‖ ^ 2 + ⟪b, c⟫ := by
      rw [hHxe, inner_add_right, real_inner_self_eq_norm_sq]
    change ⟪x + ν • b, H (x + ν • b)⟫ = _
    rw [map_add, map_smul, inner_add_left, inner_add_right, inner_add_right, real_inner_smul_left,
      real_inner_smul_left, real_inner_smul_right, real_inner_smul_right, h1, h2]
    ring
  have hhh : ‖b + c‖ ^ 2 = ‖b‖ ^ 2 + 2 * ⟪b, c⟫ + ‖c‖ ^ 2 := norm_add_sq_real b c
  rw [hy1, hy2]
  set q := ⟪x, H x⟫
  set B := ‖b‖ ^ 2
  set C := ‖c‖ ^ 2
  set bc := ⟪b, c⟫
  set qb := ⟪b, H b⟫
  have hhh0 : 0 ≤ B + 2 * bc + C := by rw [← hhh]; positivity
  have ha : 0 ≤ ν * (1 - ν) := mul_nonneg hν0 (by linarith)
  have hk : ‖x‖ ^ 2 + ν * q + ν ^ 2 * B - ν * (1 - ν) * (q + 2 * ν * (B + bc) + ν ^ 2 * qb)
      - (‖x‖ ^ 2 + ν * (1 - ν) * q) =
      - (ν ^ 3 * (q - B)) - (ν * (ν * (1 - ν)) * (q - C)) - (ν * (ν * (1 - ν)) * (B + 2 * bc + C))
        - (ν ^ 2 * (ν * (1 - ν)) * qb) - (ν * (1 - 3 * ν) * q) := by
    ring
  have t1 : 0 ≤ ν ^ 3 * (q - B) := mul_nonneg (by positivity) (by linarith)
  have t2 : 0 ≤ ν * (ν * (1 - ν)) * (q - C) := mul_nonneg (by positivity) (by linarith)
  have t3 : 0 ≤ ν * (ν * (1 - ν)) * (B + 2 * bc + C) := mul_nonneg (by positivity) hhh0
  have t4 : 0 ≤ ν ^ 2 * (ν * (1 - ν)) * qb := mul_nonneg (by positivity) hqb
  have hq0 : 0 ≤ q := le_trans (by positivity) hBq
  have t5 : 0 ≤ ν * (1 - 3 * ν) * q := mul_nonneg (mul_nonneg hν0 (by linarith)) hq0
  linarith

/-- **Lemma 3.4** (arXiv 2507.15192).  Let `‖E‖ ≤ 1`, `H = 2 I - (E + E*)`,
`W = I - ν(1-ν) H` and `Q = I + ν (I - E)`.  If `ν ≤ 1/3`, then `W ≻ 0` and
`Q* W Q ⪯ I + ν(1-ν) H`, the last in the Loewner order of `ContinuousLinearMap`.  Differences from
the paper: any real Hilbert space instead of `ℝ^{r×r}` with the Frobenius inner product; `ν = 0` is
allowed; `W ≻ 0` is stated as self-adjointness with the lower bound `1/9`. -/
theorem lemma_3_4 [CompleteSpace 𝓧] {E : 𝓧 →L[ℝ] 𝓧} (hE : ‖E‖ ≤ 1) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν ≤ 1 / 3) :
    let H : 𝓧 →L[ℝ] 𝓧 := (2 : ℝ) • 1 - (E + ContinuousLinearMap.adjoint E)
    let W : 𝓧 →L[ℝ] 𝓧 := 1 - (ν * (1 - ν)) • H
    let Q : 𝓧 →L[ℝ] 𝓧 := 1 + ν • (1 - E)
    IsSelfAdjoint W ∧ (∀ x, (1 / 9) * ‖x‖ ^ 2 ≤ ⟪x, W x⟫) ∧
      ContinuousLinearMap.adjoint Q ∘L W ∘L Q ≤ 1 + (ν * (1 - ν)) • H := by
  intro H W Q
  have ha : 0 ≤ ν * (1 - ν) := mul_nonneg hν0 (by linarith)
  have hEb : ∀ z, ‖E z‖ ≤ ‖z‖ := fun z => by
    simpa using E.le_of_opNorm_le hE z
  have hadj : ∀ z, ⟪z, ContinuousLinearMap.adjoint E z⟫ = ⟪z, E z⟫ := fun z => by
    rw [ContinuousLinearMap.adjoint_inner_right, real_inner_comm]
  have hH : IsSelfAdjoint H := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro u v
    change ⟪H u, v⟫ = ⟪u, H v⟫
    simp only [H, sub_apply, smul_apply, one_apply_eq_self, add_apply]
    rw [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right]
    ring
  have hW : IsSelfAdjoint W :=
    (IsSelfAdjoint.one _).sub ((IsSelfAdjoint.all _).smul hH)
  refine ⟨hW, fun x => ?_, ?_⟩
  · have h1 : ⟪x, H x⟫ = 2 * ‖x‖ ^ 2 - 2 * ⟪x, E x⟫ := by
      simp only [H, sub_apply, smul_apply, one_apply_eq_self, add_apply]
      rw [inner_sub_right, inner_add_right, hadj, real_inner_smul_right,
        real_inner_self_eq_norm_sq]
      ring
    have h2 : -⟪x, E x⟫ ≤ ‖x‖ ^ 2 := by
      have h3 := abs_real_inner_le_norm x (E x)
      have h4 := neg_abs_le ⟪x, E x⟫
      have h5 : ‖x‖ * ‖E x‖ ≤ ‖x‖ * ‖x‖ := by gcongr; exact hEb x
      nlinarith
    have h6 : ⟪x, W x⟫ = ‖x‖ ^ 2 - ν * (1 - ν) * ⟪x, H x⟫ := by
      simp only [W, sub_apply, smul_apply, one_apply_eq_self]
      rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [h6, h1]
    have h7 : ν * (1 - ν) ≤ 2 / 9 := by nlinarith
    have h8 : 0 ≤ ‖x‖ ^ 2 := by positivity
    nlinarith
  · have hsa : IsSelfAdjoint ((1 : 𝓧 →L[ℝ] 𝓧) + (ν * (1 - ν)) • H) :=
      (IsSelfAdjoint.one _).add ((IsSelfAdjoint.all _).smul hH)
    have hsb : IsSelfAdjoint (ContinuousLinearMap.adjoint Q ∘L W ∘L Q) := hW.adjoint_conj Q
    rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_def']
    refine ⟨hsa.sub hsb, fun x => ?_⟩
    have h := lemma34_form E hE hν0 hν x
    have hQ : x + ν • (x - E x) = Q x := by
      simp only [Q, add_apply, smul_apply, sub_apply, one_apply_eq_self]
    have e1 : ⟪(ContinuousLinearMap.adjoint Q ∘L W ∘L Q) x, x⟫ =
        ‖Q x‖ ^ 2 - ν * (1 - ν) * ⟪Q x, H (Q x)⟫ := by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
      change ⟪Q x, Q x - (ν * (1 - ν)) • H (Q x)⟫ = _ 
      rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    have e2 : ⟪((1 : 𝓧 →L[ℝ] 𝓧) + (ν * (1 - ν)) • H) x, x⟫ =
        ‖x‖ ^ 2 + ν * (1 - ν) * ⟪x, H x⟫ := by
      rw [real_inner_comm]
      change ⟪x, x + (ν * (1 - ν)) • H x⟫ = _
      rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real, sub_apply, inner_sub_left,
      e1, e2]
    have h' : ‖Q x‖ ^ 2 - ν * (1 - ν) * ⟪Q x, H (Q x)⟫ ≤ ‖x‖ ^ 2 + ν * (1 - ν) * ⟪x, H x⟫ := by
      rw [← hQ]
      exact h
    linarith

/-- The K-step estimate (3.12): the K-step dissipates the mixed `L²–H¹` energy. -/
private theorem ksl_kStep_energy {T D Q₀ : 𝓧 →L[ℝ] 𝓧} (hT : ∀ x, ‖T x‖ ≤ ‖x‖)
    (hD : ∀ x, ‖D x‖ ^ 2 = 2 * ‖x‖ ^ 2 - 2 * ⟪x, T x⟫) (hDT : ∀ x, D (T x) = T (D x))
    (hQ₀ : IsOrthProj Q₀) (hDQ : ∀ x, D (Q₀ x) = Q₀ (D x)) {G : 𝓧 → 𝓧} {h ν : ℝ}
    (hG : ∀ y, h • G y = ν • (T y - y)) (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) {x : 𝓧} (hx : Q₀ x = x) :
    ‖kslK Q₀ G h x‖ ^ 2 + ν * (1 - ν) * ‖D (kslK Q₀ G h x)‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  have ha : 0 ≤ ν * (1 - ν) := mul_nonneg hν0 (by linarith)
  set w := (1 - ν) • x + ν • T x with hw
  have hK : kslK Q₀ G h x = Q₀ w := by
    have h1 : w = x + h • G x := by
      rw [hG, hw]
      module
    rw [kslK, h1, map_add, hx, map_smul]
  have hw1 : ‖w‖ ^ 2 ≤ ‖x‖ ^ 2 - ν * (1 - ν) * ‖D x‖ ^ 2 := convex_step (hT x) (hD x)
  have hw2 : ‖D w‖ ^ 2 ≤ ‖D x‖ ^ 2 := by
    have h1 := convex_step (ν := ν) (hT (D x)) (hD (D x))
    have h0 : D w = (1 - ν) • D x + ν • T (D x) := by
      rw [hw, map_add, map_smul, map_smul, hDT]
    rw [h0]
    have : 0 ≤ ν * (1 - ν) * ‖D (D x)‖ ^ 2 := by positivity
    linarith
  have h1 : ‖Q₀ w‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    gcongr
    exact hQ₀.norm_le w
  have h2 : ‖D (Q₀ w)‖ ^ 2 ≤ ‖D w‖ ^ 2 := by
    rw [hDQ]
    gcongr
    exact hQ₀.norm_le (D w)
  rw [hK]
  nlinarith [mul_le_mul_of_nonneg_left (h2.trans hw2) ha]

/-- The S-step estimate (3.18), from Lemma 3.4: `‖S z‖² - a |S z|₁² ≤ ‖z‖² + a |z|₁²`. -/
private theorem ksl_sStep_energy [CompleteSpace 𝓧] {T D P₁ Q₀ : 𝓧 →L[ℝ] 𝓧}
    (hT : ∀ x, ‖T x‖ ≤ ‖x‖) (hD : ∀ x, ‖D x‖ ^ 2 = 2 * ‖x‖ ^ 2 - 2 * ⟪x, T x⟫)
    (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀) (hc : ∀ x, P₁ (Q₀ x) = Q₀ (P₁ x)) {G : 𝓧 → 𝓧}
    {h ν : ℝ} (hG : ∀ y, h • G y = ν • (T y - y)) (hν0 : 0 ≤ ν) (hν : ν ≤ 1 / 3) {z : 𝓧}
    (hz₁ : P₁ z = z) (hz₀ : Q₀ z = z) :
    ‖kslS P₁ Q₀ G h z‖ ^ 2 - ν * (1 - ν) * ‖D (kslS P₁ Q₀ G h z)‖ ^ 2 ≤
      ‖z‖ ^ 2 + ν * (1 - ν) * ‖D z‖ ^ 2 := by
  set P : 𝓧 →L[ℝ] 𝓧 := P₁ * Q₀ with hP
  have hPo : IsOrthProj P := hP₁.mul hQ₀ hc
  set E' : 𝓧 →L[ℝ] 𝓧 := P ∘L T ∘L P with hE'
  have hE'b : ‖E'‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]
    exact (hPo.norm_le _).trans ((hT _).trans (hPo.norm_le _))
  have hPz : P z = z := by
    change P₁ (Q₀ z) = z
    rw [hz₀, hz₁]
  have hy : kslS P₁ Q₀ G h z = z + ν • (z - E' z) := by
    have h1 : E' z = P (T z) := by
      simp only [hE', ContinuousLinearMap.comp_apply]
      rw [hPz]
    have h2 : P₁ (Q₀ (h • G z)) = ν • (P (T z) - z) := by
      rw [hG, map_smul, map_smul, map_sub, map_sub, hz₀, hz₁]
      rfl
    rw [kslS, hz₁, h1, ← map_smul, ← map_smul, h2]
    module
  have hPy : P (kslS P₁ Q₀ G h z) = kslS P₁ Q₀ G h z := by
    have h1 : P (P₁ (Q₀ (G z))) = P₁ (Q₀ (G z)) := hPo.idem _
    rw [kslS, hz₁, map_sub, map_smul, hPz, h1]
  have hform : ∀ y, P y = y →
      ⟪y, ((2 : ℝ) • (1 : 𝓧 →L[ℝ] 𝓧) - (E' + ContinuousLinearMap.adjoint E')) y⟫ = ‖D y‖ ^ 2 := by
    intro y hy
    have h1 : ⟪y, E' y⟫ = ⟪y, T y⟫ := by
      simp only [hE', ContinuousLinearMap.comp_apply]
      rw [hy, real_inner_comm, hPo.inner_apply_left_of_mem _ hy, real_inner_comm]
    have h2 : ⟪y, ContinuousLinearMap.adjoint E' y⟫ = ⟪y, T y⟫ := by
      rw [ContinuousLinearMap.adjoint_inner_right, real_inner_comm, h1]
    simp only [sub_apply, smul_apply, one_apply_eq_self, add_apply]
    rw [inner_sub_right, inner_add_right, h1, h2, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hD]
    ring
  have h1 := lemma34_form E' hE'b hν0 hν z
  simp only at h1
  rw [← hy, hform _ hPy, hform z hPz] at h1
  exact h1

/-- The L-step estimate: `‖L w‖² ≤ ‖w‖² - a |w|₁²`. -/
private theorem ksl_lStep_energy {T D P₁ : 𝓧 →L[ℝ] 𝓧} (hT : ∀ x, ‖T x‖ ≤ ‖x‖)
    (hD : ∀ x, ‖D x‖ ^ 2 = 2 * ‖x‖ ^ 2 - 2 * ⟪x, T x⟫) (hP₁ : IsOrthProj P₁) {G : 𝓧 → 𝓧}
    {h ν : ℝ} (hG : ∀ y, h • G y = ν • (T y - y)) {w : 𝓧} (hw : P₁ w = w) :
    ‖kslL P₁ G h w‖ ^ 2 ≤ ‖w‖ ^ 2 - ν * (1 - ν) * ‖D w‖ ^ 2 := by
  have h1 : kslL P₁ G h w = (1 - ν) • w + ν • P₁ (T w) := by
    rw [kslL, ← map_smul, hG, map_smul, map_sub, hw]
    module
  have h2 : ⟪w, P₁ (T w)⟫ = ⟪w, T w⟫ := by
    rw [real_inner_comm, hP₁.inner_apply_left_of_mem _ hw, real_inner_comm]
  rw [h1]
  refine convex_step ((hP₁.norm_le _).trans (hT _)) ?_
  rw [hD, h2]

/-- **Abstract form of Theorem 3.3** (arXiv 2507.15192), for the library's explicit Euler KSL step
`kslEulerStep`.  Let `P₁, Q₀` be commuting orthogonal projectors and let `h G = ν (T - I)`, where
`T` is a contraction and `D` a bounded operator commuting with `T` and `Q₀` such that
`‖D x‖² = 2 ‖x‖² - 2 ⟪x, T x⟫`, i.e. `DᵀD = 2 I - T - Tᵀ` (for the Lax–Friedrichs field, `D` is the
forward difference and `‖D ·‖²` is the `H¹_x` seminorm).  If `0 ≤ ν ≤ 1/3`, then the KSL step is
`L²`-stable on the inputs of the integrator.  The proof feeds the estimates (3.12), (3.18) and
Lemma 3.4 into `kslSplitStep_energy_le`, with `𝓔₁ = ‖·‖² + ν(1-ν)‖D ·‖²` and
`𝓔₂ = ‖·‖² - ν(1-ν)‖D ·‖²`. -/
theorem ksl_stable_of_transport [CompleteSpace 𝓧] {T D P₁ Q₀ : 𝓧 →L[ℝ] 𝓧}
    (hT : ∀ x, ‖T x‖ ≤ ‖x‖) (hD : ∀ x, ‖D x‖ ^ 2 = 2 * ‖x‖ ^ 2 - 2 * ⟪x, T x⟫)
    (hDT : ∀ x, D (T x) = T (D x)) (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀)
    (hc : ∀ x, P₁ (Q₀ x) = Q₀ (P₁ x)) (hDQ : ∀ x, D (Q₀ x) = Q₀ (D x)) {G : 𝓧 → 𝓧} {h ν : ℝ}
    (hG : ∀ y, h • G y = ν • (T y - y)) (hν0 : 0 ≤ ν) (hν : ν ≤ 1 / 3) {x : 𝓧} (hx : Q₀ x = x)
    (hx₁ : P₁ (kslK Q₀ G h x) = kslK Q₀ G h x) :
    ‖kslEulerStep P₁ Q₀ G h x‖ ≤ ‖x‖ := by
  have h1 := kslSplitStep_energy_le (𝓔₀ := fun y => ‖y‖ ^ 2)
    (𝓔₁ := fun y => ‖y‖ ^ 2 + ν * (1 - ν) * ‖D y‖ ^ 2)
    (𝓔₂ := fun y => ‖y‖ ^ 2 - ν * (1 - ν) * ‖D y‖ ^ 2) (𝓔₃ := fun y => ‖y‖ ^ 2)
    hP₁ hQ₀ hc (FK := G) (FS := G) (FL := G) (h := h)
    (fun y hy => ksl_kStep_energy hT hD hDT hQ₀ hDQ hG hν0 (by linarith) hy)
    (fun z hz₁ hz₀ => ksl_sStep_energy hT hD hP₁ hQ₀ hc hG hν0 hν hz₁ hz₀)
    (fun w hw _ => ksl_lStep_energy hT hD hP₁ hG hw) hx hx₁
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1

end Abstract

section Scheme

/-- The forward periodic shift `(E₊ x)_j = x_{j+1}` on a grid with `N` points. -/
def shiftPlus (𝕜 : Type*) [Zero 𝕜] [One 𝕜] (N : ℕ) [NeZero N] : Matrix (Fin N) (Fin N) 𝕜 :=
  Matrix.of fun i j => if j = i + 1 then 1 else 0

/-- The backward periodic shift `(E₋ x)_j = x_{j-1}` on a grid with `N` points. -/
def shiftMinus (𝕜 : Type*) [Zero 𝕜] [One 𝕜] (N : ℕ) [NeZero N] : Matrix (Fin N) (Fin N) 𝕜 :=
  Matrix.of fun i j => if j + 1 = i then 1 else 0

/-- The central difference matrix `M₁ = E₊ - E₋` of arXiv 2507.15192. -/
def M₁ (𝕜 : Type*) [Ring 𝕜] (N : ℕ) [NeZero N] : Matrix (Fin N) (Fin N) 𝕜 :=
  shiftPlus 𝕜 N - shiftMinus 𝕜 N

/-- The second difference matrix `M₂ = 2 I - E₊ - E₋` of arXiv 2507.15192. -/
def M₂ (𝕜 : Type*) [Ring 𝕜] (N : ℕ) [NeZero N] : Matrix (Fin N) (Fin N) 𝕜 :=
  (2 : 𝕜) • 1 - shiftPlus 𝕜 N - shiftMinus 𝕜 N

variable {𝕜 : Type*} {N : ℕ} [NeZero N] {n r : Type*} [Fintype n] [Fintype r]

/-- The Lax–Friedrichs (Rusanov) field `F_LF(U) = -(1/(2Δx)) M₁ U A - (λ/(2Δx)) M₂ U`. -/
def fLF [Field 𝕜] (dx lam : 𝕜) (A : Matrix n n 𝕜) (U : Matrix (Fin N) n 𝕜) :
    Matrix (Fin N) n 𝕜 :=
  -((2 * dx)⁻¹ • (M₁ 𝕜 N * U * A)) - (lam / (2 * dx)) • (M₂ 𝕜 N * U)

/-- The forward Euler K-step `K ↦ K + Δt F(K Vᴴ) V`. -/
def kStep [Field 𝕜] [StarRing 𝕜] (F : Matrix (Fin N) n 𝕜 → Matrix (Fin N) n 𝕜) (dt : 𝕜)
    (K : Matrix (Fin N) r 𝕜) (V : Matrix n r 𝕜) : Matrix (Fin N) r 𝕜 :=
  K + dt • (F (K * Vᴴ) * V)

/-- The forward Euler S-step `S ↦ S - Δt Xᴴ F(X S Vᴴ) V` (backward in time). -/
def sStep [Field 𝕜] [StarRing 𝕜] (F : Matrix (Fin N) n 𝕜 → Matrix (Fin N) n 𝕜) (dt : 𝕜)
    (X : Matrix (Fin N) r 𝕜) (S : Matrix r r 𝕜) (V : Matrix n r 𝕜) : Matrix r r 𝕜 :=
  S - dt • (Xᴴ * F (X * S * Vᴴ) * V)

/-- The forward Euler L-step `L ↦ L + Δt Xᴴ F(X L)`. -/
def lStep [Field 𝕜] [StarRing 𝕜] (F : Matrix (Fin N) n 𝕜 → Matrix (Fin N) n 𝕜) (dt : 𝕜)
    (X : Matrix (Fin N) r 𝕜) (L : Matrix r n 𝕜) : Matrix r n 𝕜 :=
  L + dt • (Xᴴ * F (X * L))

/-- The result `Uⁿ⁺¹ = Xⁿ⁺¹ Lⁿ⁺¹` of a DtP–PSI step: `X` is the new basis, `S₁` the factor of the
QR decomposition `K¹ = X S₁` of the K-step result, and `V` the old co-range basis. -/
def dtpStep [Field 𝕜] [StarRing 𝕜] (F : Matrix (Fin N) n 𝕜 → Matrix (Fin N) n 𝕜) (dt : 𝕜)
    (X : Matrix (Fin N) r 𝕜) (S₁ : Matrix r r 𝕜) (V : Matrix n r 𝕜) : Matrix (Fin N) n 𝕜 :=
  X * lStep F dt X (sStep F dt X S₁ V * Vᴴ)

section Shift

variable [Ring 𝕜] {m : Type*}

private lemma shiftPlus_mul_apply (Z : Matrix (Fin N) m 𝕜) (i : Fin N) (j : m) :
    (shiftPlus 𝕜 N * Z) i j = Z (i + 1) j := by
  simp [Matrix.mul_apply, shiftPlus]

private lemma shiftMinus_mul_apply (Z : Matrix (Fin N) m 𝕜) (i : Fin N) (j : m) :
    (shiftMinus 𝕜 N * Z) i j = Z (i - 1) j := by
  simp [Matrix.mul_apply, shiftMinus, ← eq_sub_iff_add_eq]

private lemma shiftPlus_mul_shiftMinus : shiftPlus 𝕜 N * shiftMinus 𝕜 N = 1 := by
  ext i j
  rw [shiftPlus_mul_apply]
  simp [shiftMinus, Matrix.one_apply, eq_comm]

private lemma shiftMinus_mul_shiftPlus : shiftMinus 𝕜 N * shiftPlus 𝕜 N = 1 := by
  ext i j
  rw [shiftMinus_mul_apply]
  simp [shiftPlus, Matrix.one_apply, eq_comm]

private lemma transpose_shiftPlus : (shiftPlus 𝕜 N)ᵀ = shiftMinus 𝕜 N := by
  ext i j
  simp [shiftPlus, shiftMinus, eq_comm]

private lemma transpose_shiftMinus : (shiftMinus 𝕜 N)ᵀ = shiftPlus 𝕜 N := by
  rw [← transpose_shiftPlus, Matrix.transpose_transpose]

end Shift

end Scheme

section RealScheme

open scoped LeanDLRA.Frobenius
open LeanDLRA.Curvature

variable {N : ℕ} [NeZero N] {n r : Type*} [Fintype n] [Fintype r]

/-- `G = ½ (E₊ + E₋) = I - ½ M₂`. -/
private noncomputable def gMat (N : ℕ) [NeZero N] : Matrix (Fin N) (Fin N) ℝ :=
  (1 / 2 : ℝ) • (shiftPlus ℝ N + shiftMinus ℝ N)

/-- `H = ½ M₁`. -/
private noncomputable def hMat (N : ℕ) [NeZero N] : Matrix (Fin N) (Fin N) ℝ :=
  (1 / 2 : ℝ) • M₁ ℝ N

/-- The forward difference `D = I - E₊`, with `Dᵀ D = M₂`. -/
private def dMat (N : ℕ) [NeZero N] : Matrix (Fin N) (Fin N) ℝ := 1 - shiftPlus ℝ N

private lemma gMat_transpose : (gMat N)ᵀ = gMat N := by
  simp only [gMat, Matrix.transpose_smul, Matrix.transpose_add, transpose_shiftPlus,
    transpose_shiftMinus, add_comm]

private lemma hMat_transpose : (hMat N)ᵀ = -hMat N := by
  simp only [hMat, M₁, Matrix.transpose_smul, Matrix.transpose_sub, transpose_shiftPlus,
    transpose_shiftMinus]
  module

private lemma gMat_mul_hMat : gMat N * hMat N = hMat N * gMat N := by
  have h₁ := shiftPlus_mul_shiftMinus (𝕜 := ℝ) (N := N)
  have h₂ := shiftMinus_mul_shiftPlus (𝕜 := ℝ) (N := N)
  simp only [gMat, hMat, M₁, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.sub_mul, Matrix.mul_sub, h₁, h₂]
  module

private lemma gMat_sq_sub : gMat N * gMat N + (hMat N)ᵀ * hMat N = 1 := by
  have h₁ := shiftPlus_mul_shiftMinus (𝕜 := ℝ) (N := N)
  have h₂ := shiftMinus_mul_shiftPlus (𝕜 := ℝ) (N := N)
  rw [hMat_transpose]
  simp only [gMat, hMat, M₁, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.neg_mul, h₁, h₂]
  module

private lemma dMat_transpose_mul : (dMat N)ᵀ * dMat N = (2 : ℝ) • (1 - gMat N) := by
  have h₂ := shiftMinus_mul_shiftPlus (𝕜 := ℝ) (N := N)
  simp only [dMat, gMat, Matrix.transpose_sub, Matrix.transpose_one, transpose_shiftPlus,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, h₂]
  module

private lemma dMat_mul_gMat : dMat N * gMat N = gMat N * dMat N := by
  have h₁ := shiftPlus_mul_shiftMinus (𝕜 := ℝ) (N := N)
  have h₂ := shiftMinus_mul_shiftPlus (𝕜 := ℝ) (N := N)
  simp only [gMat, dMat, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, h₁, h₂]
  module

private lemma dMat_mul_hMat : dMat N * hMat N = hMat N * dMat N := by
  have h₁ := shiftPlus_mul_shiftMinus (𝕜 := ℝ) (N := N)
  have h₂ := shiftMinus_mul_shiftPlus (𝕜 := ℝ) (N := N)
  simp only [hMat, M₁, dMat, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, h₁, h₂]
  module

omit [NeZero N] in
/-- A skew factor against a symmetric factor has vanishing trace pairing. -/
private lemma inner_skew_sym {C : Matrix (Fin N) (Fin N) ℝ} (hC : Cᵀ = -C) {B : Matrix n n ℝ}
    (hB : Bᵀ = B) (Y : Matrix (Fin N) n ℝ) : ⟪Y, C * Y * B⟫ = 0 := by
  have h : ⟪Y, C * Y * B⟫ = -⟪Y, C * Y * B⟫ := by
    calc ⟪Y, C * Y * B⟫ = ⟪Y * Bᵀ, C * Y⟫ := Frobenius.inner_mul_right' _ _ _
      _ = ⟪Cᵀ * (Y * Bᵀ), Y⟫ := Frobenius.inner_mul_left' _ _ _
      _ = -⟪C * Y * B, Y⟫ := by
        rw [hC, hB, Matrix.neg_mul, inner_neg_left, Matrix.mul_assoc]
      _ = -⟪Y, C * Y * B⟫ := by rw [real_inner_comm]
  linarith

/-- The transport operator `𝒯(Y) = (I - ½ M₂) Y - ½ M₁ Y Â` of the proof of Thm 3.3. -/
private noncomputable def tCLM (B : Matrix n n ℝ) :
    Matrix (Fin N) n ℝ →L[ℝ] Matrix (Fin N) n ℝ :=
  Frobenius.leftMulCLM (gMat N) - (Frobenius.rightMulCLM B) ∘L (Frobenius.leftMulCLM (hMat N))

private lemma tCLM_apply (B : Matrix n n ℝ) (Y : Matrix (Fin N) n ℝ) :
    tCLM B Y = gMat N * Y - hMat N * Y * B := rfl

private lemma tCLM_contract {B : Matrix n n ℝ} (hB : Bᵀ = B) (hB1 : ∀ Z : Matrix (Fin N) n ℝ,
    ‖Z * B‖ ≤ ‖Z‖) (Y : Matrix (Fin N) n ℝ) : ‖tCLM B Y‖ ≤ ‖Y‖ := by
  have hc : ⟪gMat N * Y, hMat N * Y * B⟫ = 0 := by
    rw [Matrix.mul_assoc, Frobenius.inner_mul_left, gMat_transpose, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc]
    apply inner_skew_sym _ hB
    rw [Matrix.transpose_mul, hMat_transpose, gMat_transpose, Matrix.neg_mul, gMat_mul_hMat]
  have h1 : ‖tCLM B Y‖ ^ 2 = ‖gMat N * Y‖ ^ 2 + ‖hMat N * Y * B‖ ^ 2 := by
    rw [tCLM_apply, norm_sub_sq_real, hc]
    ring
  have h2 : ‖gMat N * Y‖ ^ 2 + ‖hMat N * Y‖ ^ 2 = ‖Y‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      Frobenius.inner_mul_left, Frobenius.inner_mul_left (hMat N), ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, ← inner_add_right, ← Matrix.add_mul, gMat_transpose, gMat_sq_sub,
      Matrix.one_mul]
  have h3 : ‖hMat N * Y * B‖ ^ 2 ≤ ‖hMat N * Y‖ ^ 2 := by
    gcongr
    exact hB1 _
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by linarith)

private lemma tCLM_comm (B : Matrix n n ℝ) (Y : Matrix (Fin N) n ℝ) :
    dMat N * tCLM B Y = tCLM B (dMat N * Y) := by
  simp only [tCLM_apply, Matrix.mul_sub, ← Matrix.mul_assoc, dMat_mul_gMat, dMat_mul_hMat]

private lemma dMat_norm_sq {B : Matrix n n ℝ} (hB : Bᵀ = B) (Y : Matrix (Fin N) n ℝ) :
    ‖dMat N * Y‖ ^ 2 = 2 * ‖Y‖ ^ 2 - 2 * ⟪Y, tCLM B Y⟫ := by
  rw [tCLM_apply, inner_sub_right, inner_skew_sym hMat_transpose hB,
    ← real_inner_self_eq_norm_sq, Frobenius.inner_mul_left, ← Matrix.mul_assoc,
    dMat_transpose_mul, Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, real_inner_smul_right,
    inner_sub_right, real_inner_self_eq_norm_sq]
  ring

omit [NeZero N] in
private lemma dtp_kslK_eq {G : Matrix (Fin N) n ℝ → Matrix (Fin N) n ℝ} {dt : ℝ}
    {K₀ X : Matrix (Fin N) r ℝ} {V : Matrix n r ℝ} {S₁ : Matrix r r ℝ}
    (hQR : kStep G dt K₀ V = X * S₁) :
    kslK (rightProj V) G dt (K₀ * Vᵀ) = X * S₁ * Vᵀ := by
  rw [← hQR, kStep, kslK, rightProj_apply, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.add_mul, Matrix.smul_mul]

omit [NeZero N] in
/-- **Equivalent projected form** (arXiv 2507.15192, eqs. after (3.6)): the factored DtP–PSI step
(3.4)–(3.6) is the full-space step `kslEulerStep` of the library, with the left projector
`P₁ = X Xᵀ ·` of the new basis and the right projector `Q₀ = · V Vᵀ` of the old co-basis. -/
theorem dtpStep_eq_kslEulerStep [DecidableEq r] {G : Matrix (Fin N) n ℝ → Matrix (Fin N) n ℝ}
    {dt : ℝ} {K₀ X : Matrix (Fin N) r ℝ} {V : Matrix n r ℝ} {S₁ : Matrix r r ℝ}
    (hX : Xᵀ * X = 1) (hQR : kStep G dt K₀ V = X * S₁) :
    dtpStep G dt X S₁ V = kslEulerStep (leftProj X) (rightProj V) G dt (K₀ * Vᵀ) := by
  have hL : ∀ S : Matrix r n ℝ, leftProj X (X * S) = X * S := fun S => by
    rw [leftProj_apply, Matrix.mul_assoc X Xᵀ, ← Matrix.mul_assoc Xᵀ, hX, Matrix.one_mul]
  have hS : kslS (leftProj X) (rightProj V) G dt (X * S₁ * Vᵀ) =
      X * sStep G dt X S₁ V * Vᵀ := by
    rw [Matrix.mul_assoc X S₁, kslS, hL, sStep, ← Matrix.mul_assoc X S₁, leftProj_apply,
      rightProj_apply, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc X S₁]
    simp only [Matrix.mul_assoc]
  rw [kslEulerStep, dtp_kslK_eq hQR, hS, dtpStep, lStep, kslL, leftProj_apply,
    Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.mul_add, Matrix.mul_smul]
  simp only [Matrix.mul_assoc]

/-- **Theorem 3.3** (arXiv 2507.15192).  For the periodic grid with `N` points, symmetric `A`,
`λ ≥ ‖A‖₂`, `Δt ≥ 0`, `Δx > 0` and `ν = λ Δt/Δx ≤ 1/3`, one forward Euler DtP–PSI step with the
Lax–Friedrichs field does not increase the Frobenius norm: with `Uⁿ = K₀ Vᵀ`, `VᵀV = 1`, and the QR
step `K¹ = X S₁`, `XᵀX = 1`, one has `‖Uⁿ⁺¹‖_F ≤ ‖Uⁿ‖_F`.  In the paper `λ = λ_max = ‖A‖₂`, the case
of equality in `hlam`.  Such `X`, `S₁` exist by `exists_dtp_qr`. -/
theorem dtp_L2_stable [DecidableEq n] [DecidableEq r] {A : Matrix n n ℝ} (hA : Aᵀ = A)
    {lam dt dx : ℝ} (hlam : specNorm A ≤ lam) (hdt : 0 ≤ dt) (hdx : 0 < dx)
    (hν : lam * dt / dx ≤ 1 / 3) {K₀ X : Matrix (Fin N) r ℝ} {V : Matrix n r ℝ}
    {S₁ : Matrix r r ℝ} (hV : Vᵀ * V = 1) (hX : Xᵀ * X = 1)
    (hQR : kStep (fLF dx lam A) dt K₀ V = X * S₁) :
    ‖dtpStep (fLF dx lam A) dt X S₁ V‖ ≤ ‖K₀ * Vᵀ‖ := by
  have hlam0 : 0 ≤ lam := (specNorm_nonneg A).trans hlam
  set ν := lam * dt / dx with hνd
  have hν0 : 0 ≤ ν := by positivity
  set B : Matrix n n ℝ := lam⁻¹ • A with hB
  have hBs : Bᵀ = B := by rw [hB, Matrix.transpose_smul, hA]
  have hAB : A = lam • B := by
    rcases hlam0.eq_or_lt with h0 | hpos
    · have h1 : ‖(1 : Matrix n n ℝ) * A‖ ≤ ‖(1 : Matrix n n ℝ)‖ * specNorm A := frob_mul_le' _ _
      have h2 : specNorm A = 0 := le_antisymm (by rw [← h0] at hlam; exact hlam)
        (specNorm_nonneg A)
      rw [h2, mul_zero, Matrix.one_mul] at h1
      have h3 : A = 0 := norm_le_zero_iff.1 h1
      rw [hB, h3]
      simp
    · rw [hB, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  have hB1 : ∀ Z : Matrix (Fin N) n ℝ, ‖Z * B‖ ≤ ‖Z‖ := by
    intro Z
    have h1 : ‖Z * A‖ ≤ ‖Z‖ * lam :=
      (frob_mul_le' Z A).trans (mul_le_mul_of_nonneg_left hlam (norm_nonneg _))
    rw [hB, Matrix.mul_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 hlam0)]
    rcases hlam0.eq_or_lt with h0 | hpos
    · rw [← h0]
      simp
    · calc lam⁻¹ * ‖Z * A‖ ≤ lam⁻¹ * (‖Z‖ * lam) := by gcongr
        _ = ‖Z‖ := by field_simp
  have hF : ∀ Y : Matrix (Fin N) n ℝ, dt • fLF dx lam A Y = ν • (tCLM B Y - Y) := by
    intro Y
    have hG : gMat N * Y - Y = (-(1 / 2 : ℝ)) • (M₂ ℝ N * Y) := by
      simp only [gMat, M₂, Matrix.smul_mul, Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul]
      module
    have hH : hMat N * Y * B = (1 / 2 : ℝ) • (M₁ ℝ N * Y * B) := by
      simp only [hMat, Matrix.smul_mul]
    have hT : tCLM B Y - Y = (-(1 / 2 : ℝ)) • (M₂ ℝ N * Y) -
        (1 / 2 : ℝ) • (M₁ ℝ N * Y * B) := by
      rw [tCLM_apply, sub_right_comm, hG, hH]
    rw [hT, fLF]
    nth_rw 1 [hAB]
    rw [Matrix.mul_smul, hνd]
    module
  have hK₁ := dtp_kslK_eq (G := fLF dx lam A) (dt := dt) (K₀ := K₀) (V := V) hQR
  have hP : leftProj X (kslK (rightProj V) (fLF dx lam A) dt (K₀ * Vᵀ)) =
      kslK (rightProj V) (fLF dx lam A) dt (K₀ * Vᵀ) := by
    rw [hK₁, leftProj_apply]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc X Xᵀ X, hX, Matrix.mul_one]
  have hQ : rightProj V (K₀ * Vᵀ) = K₀ * Vᵀ := by
    rw [rightProj_apply, Matrix.mul_assoc K₀, hV, Matrix.mul_one]
  rw [dtpStep_eq_kslEulerStep hX hQR]
  exact ksl_stable_of_transport (T := tCLM B) (D := Frobenius.leftMulCLM (dMat N))
    (tCLM_contract hBs hB1) (dMat_norm_sq hBs) (tCLM_comm B) (isOrthProj_leftProj hX)
    (isOrthProj_rightProj hV) (leftProj_rightProj_comm X V)
    (fun Y => by simp [Matrix.mul_assoc]) hF hν0 hν hQ hP

/-- **Theorem 3.3, for all `n`** (arXiv 2507.15192).  For a sequence of factorised iterates
`Uⁿ = Xⁿ Sⁿ (Vⁿ)ᵀ` produced by the DtP–PSI scheme (with `K¹ = Xⁿ⁺¹ S⁽¹⁾` and
`Lⁿ⁺¹ = Sⁿ⁺¹ (Vⁿ⁺¹)ᵀ`, the transpose of the QR step of the paper), `‖Uⁿ⁺¹‖_F ≤ ‖Uⁿ‖_F` for every
`n`, hence `‖Uⁿ‖_F ≤ ‖U⁰‖_F`. -/
theorem dtp_L2_stable_iter [DecidableEq n] [DecidableEq r] {A : Matrix n n ℝ} (hA : Aᵀ = A)
    {lam dt dx : ℝ} (hlam : specNorm A ≤ lam) (hdt : 0 ≤ dt) (hdx : 0 < dx)
    (hν : lam * dt / dx ≤ 1 / 3) {X : ℕ → Matrix (Fin N) r ℝ} {V : ℕ → Matrix n r ℝ}
    {S Sb : ℕ → Matrix r r ℝ} (hV : ∀ k, (V k)ᵀ * V k = 1) (hX : ∀ k, (X k)ᵀ * X k = 1)
    (hK : ∀ k, kStep (fLF dx lam A) dt (X k * S k) (V k) = X (k + 1) * Sb k)
    (hL : ∀ k, lStep (fLF dx lam A) dt (X (k + 1))
      (sStep (fLF dx lam A) dt (X (k + 1)) (Sb k) (V k) * (V k)ᵀ) = S (k + 1) * (V (k + 1))ᵀ) :
    (∀ k, ‖X (k + 1) * S (k + 1) * (V (k + 1))ᵀ‖ ≤ ‖X k * S k * (V k)ᵀ‖) ∧
      ∀ k, ‖X k * S k * (V k)ᵀ‖ ≤ ‖X 0 * S 0 * (V 0)ᵀ‖ := by
  have hstep : ∀ k, ‖X (k + 1) * S (k + 1) * (V (k + 1))ᵀ‖ ≤ ‖X k * S k * (V k)ᵀ‖ := by
    intro k
    have h := dtp_L2_stable hA hlam hdt hdx hν (hV k) (hX (k + 1)) (hK k)
    rw [dtpStep, Matrix.conjTranspose_eq_transpose_of_trivial, hL k, ← Matrix.mul_assoc] at h
    exact h
  refine ⟨hstep, fun k => ?_⟩
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (hstep k).trans ih

omit [NeZero N] in
/-- The QR step of the DtP–PSI scheme is always possible for `r ≤ N`, so the hypotheses of
`dtp_L2_stable` can be met for every `K₀`, every field and every `V`: there are `X` and `S₁` with
`Xᵀ X = 1` and `K¹ = X S₁` (the rank-deficient case included). -/
theorem exists_dtp_qr {r : ℕ} (hr : r ≤ N) (F : Matrix (Fin N) n ℝ → Matrix (Fin N) n ℝ) (dt : ℝ)
    (K₀ : Matrix (Fin N) (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) :
    ∃ (X : Matrix (Fin N) (Fin r) ℝ) (S₁ : Matrix (Fin r) (Fin r) ℝ),
      Xᵀ * X = 1 ∧ kStep F dt K₀ V = X * S₁ := by
  obtain ⟨X, hX, hK⟩ := exists_orthonormal_capture_of_le_card (kStep F dt K₀ V)
    (by simpa using hr)
  exact ⟨X, Xᵀ * kStep F dt K₀ V, hX, by rw [← Matrix.mul_assoc]; exact hK.symm⟩

end RealScheme

section SingleMode

variable {N : ℕ} [NeZero N] {n r : Type*} [Fintype r]

omit [NeZero N] in
/-- The computation behind Prop. 3.2 (arXiv 2507.15192), for any field with involution: on an
eigenstate `U₀` of a homogeneous field, with `Δt F(c U₀) = c (p - 1) U₀`, the K-, S- and L-steps
multiply by `p`, `2 - p` and `p`, for every orthonormal `V`, `X` with `K₀ Vᴴ = U₀`, `K¹ = X S₁`. -/
theorem dtpStep_of_eigen [Fintype n] {𝕜 : Type*} [Field 𝕜] [StarRing 𝕜] [DecidableEq r]
    {F : Matrix (Fin N) n 𝕜 → Matrix (Fin N) n 𝕜} {dt p : 𝕜} {U₀ : Matrix (Fin N) n 𝕜}
    (hF : ∀ c : 𝕜, dt • F (c • U₀) = (c * (p - 1)) • U₀)
    {K₀ X : Matrix (Fin N) r 𝕜} {V : Matrix n r 𝕜} {S₁ : Matrix r r 𝕜}
    (hV : Vᴴ * V = 1) (hX : Xᴴ * X = 1) (hK : K₀ * Vᴴ = U₀)
    (hQR : kStep F dt K₀ V = X * S₁) :
    dtpStep F dt X S₁ V = (p ^ 2 * (2 - p)) • U₀ := by
  have hF1 : dt • F U₀ = (p - 1) • U₀ := by simpa using hF 1
  have hUV : U₀ * V = K₀ := by
    rw [← hK, Matrix.mul_assoc, hV, Matrix.mul_one]
  have hK₁ : X * S₁ = p • K₀ := by
    rw [← hQR, kStep, hK, ← Matrix.smul_mul, hF1, Matrix.smul_mul, hUV]
    module
  have hu₁ : X * S₁ * Vᴴ = p • U₀ := by
    rw [hK₁, Matrix.smul_mul, hK]
  have hXU : p • (Xᴴ * U₀) = S₁ * Vᴴ := by
    rw [← Matrix.mul_smul, ← hu₁, Matrix.mul_assoc X S₁, ← Matrix.mul_assoc Xᴴ X, hX,
      Matrix.one_mul]
  have hS₂ : sStep F dt X S₁ V = (2 - p) • S₁ := by
    have h1 : dt • (Xᴴ * F (p • U₀) * V) = (p * (p - 1)) • (Xᴴ * K₀) := by
      calc dt • (Xᴴ * F (p • U₀) * V) = Xᴴ * (dt • F (p • U₀)) * V := by
            rw [Matrix.mul_smul, Matrix.smul_mul]
        _ = Xᴴ * ((p * (p - 1)) • U₀) * V := by rw [hF]
        _ = (p * (p - 1)) • (Xᴴ * (U₀ * V)) := by
            rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
        _ = (p * (p - 1)) • (Xᴴ * K₀) := by rw [hUV]
    have h2 : p • (Xᴴ * K₀) = S₁ := by
      rw [← Matrix.mul_smul, ← hK₁, ← Matrix.mul_assoc, hX, Matrix.one_mul]
    rw [sStep, hu₁, h1]
    calc S₁ - (p * (p - 1)) • (Xᴴ * K₀) = S₁ - (p - 1) • (p • (Xᴴ * K₀)) := by
          rw [smul_smul, mul_comm]
      _ = (2 - p) • S₁ := by
          rw [h2]
          module
  have hL : lStep F dt X (sStep F dt X S₁ V * Vᴴ) = ((2 - p) * p) • (S₁ * Vᴴ) := by
    have h1 : X * (sStep F dt X S₁ V * Vᴴ) = ((2 - p) * p) • U₀ := by
      rw [hS₂, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, hu₁, smul_smul]
    have h3 : dt • (Xᴴ * F (((2 - p) * p) • U₀)) = (((2 - p) * p) * (p - 1)) • (Xᴴ * U₀) := by
      rw [← Matrix.mul_smul, hF, Matrix.mul_smul]
    have h2 : (((2 - p) * p) * (p - 1)) • (Xᴴ * U₀) = ((2 - p) * (p - 1)) • (S₁ * Vᴴ) := by
      rw [← hXU, smul_smul]
      congr 1
      ring
    rw [lStep, h1, h3, h2, hS₂, Matrix.smul_mul]
    module
  rw [dtpStep, hL, Matrix.mul_smul, ← Matrix.mul_assoc, hu₁, smul_smul]
  congr 1
  ring

/-- The wave number `α_m = 2π m / N`. -/
noncomputable def alphaM (N m : ℕ) : ℝ := 2 * Real.pi * m / N

/-- The symbol `y_m = 1 - cos α_m` of `M₂ / 2`. -/
noncomputable def yM (N m : ℕ) : ℝ := 1 - Real.cos (alphaM N m)

/-- The symbol `z_m = sin α_m` of `M₁ / (2 i)`. -/
noncomputable def zM (N m : ℕ) : ℝ := Real.sin (alphaM N m)

/-- The phase `ζ = e^{i α_m}`. -/
noncomputable def zetaM (N m : ℕ) : ℂ := Complex.exp (Complex.I * alphaM N m)

/-- The Fourier mode `(x_m)_j = N^{-1/2} e^{i j α_m}`, `j = 1, …, N` (`Fin N` counts from `0`). -/
noncomputable def fourierMode (N m : ℕ) (j : Fin N) : ℂ :=
  ((Real.sqrt N : ℝ) : ℂ)⁻¹ * zetaM N m ^ (j.val + 1)

/-- The rank-one single-mode state `x_m vᵀ`. -/
noncomputable def singleMode (N m : ℕ) (v : n → ℝ) : Matrix (Fin N) n ℂ :=
  Matrix.vecMulVec (fourierMode N m) fun i => (v i : ℂ)

/-- The factor `p = 1 - ν y - i ν_k z`. -/
noncomputable def ampP (ν νk y z : ℝ) : ℂ := 1 - ν * y - Complex.I * νk * z

omit [NeZero N] in
private lemma zetaM_pow (m : ℕ) (hN : N ≠ 0) : zetaM N m ^ N = 1 := by
  have h : (N : ℂ) * (Complex.I * (alphaM N m : ℂ)) = (m : ℂ) * (2 * Real.pi * Complex.I) := by
    have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
    simp only [alphaM]
    push_cast
    field_simp
  rw [zetaM, ← Complex.exp_nat_mul, h, Complex.exp_nat_mul_two_pi_mul_I]

private lemma fourierMode_add_one (m : ℕ) (i : Fin N) :
    fourierMode N m (i + 1) = zetaM N m * fourierMode N m i := by
  have hN : N ≠ 0 := NeZero.ne N
  have h1 : zetaM N m ^ ((i + 1 : Fin N).val) = zetaM N m ^ (i.val + 1) := by
    rw [pow_eq_pow_mod (i.val + 1) (zetaM_pow m hN)]
    congr 1
    rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  simp only [fourierMode]
  rw [pow_succ _ ((i + 1 : Fin N).val), h1]
  ring

private lemma zetaM_ne_zero (N m : ℕ) : zetaM N m ≠ 0 := Complex.exp_ne_zero _

private lemma zetaM_inv (N m : ℕ) :
    (zetaM N m)⁻¹ = Real.cos (alphaM N m) - Complex.I * Real.sin (alphaM N m) := by
  rw [zetaM, ← Complex.exp_neg]
  have : -(Complex.I * (alphaM N m : ℂ)) = ((-alphaM N m : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
    Real.sin_neg]
  push_cast
  ring

private lemma zetaM_eq (N m : ℕ) :
    zetaM N m = Real.cos (alphaM N m) + Complex.I * Real.sin (alphaM N m) := by
  rw [zetaM, mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

private lemma shiftPlus_mul_singleMode (m : ℕ) (v : n → ℝ) :
    shiftPlus ℂ N * singleMode N m v = zetaM N m • singleMode N m v := by
  ext i j
  rw [shiftPlus_mul_apply]
  simp only [singleMode, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul,
    fourierMode_add_one]
  ring

private lemma shiftMinus_mul_singleMode (m : ℕ) (v : n → ℝ) :
    shiftMinus ℂ N * singleMode N m v = (zetaM N m)⁻¹ • singleMode N m v := by
  have h : singleMode N m v = zetaM N m • (shiftMinus ℂ N * singleMode N m v) := by
    rw [← Matrix.mul_smul, ← shiftPlus_mul_singleMode, ← Matrix.mul_assoc,
      shiftMinus_mul_shiftPlus, Matrix.one_mul]
  nth_rw 2 [h]
  rw [smul_smul, inv_mul_cancel₀ (zetaM_ne_zero N m), one_smul]

private lemma M₁_mul_singleMode (m : ℕ) (v : n → ℝ) :
    M₁ ℂ N * singleMode N m v = (2 * Complex.I * zM N m) • singleMode N m v := by
  rw [M₁, Matrix.sub_mul, shiftPlus_mul_singleMode, shiftMinus_mul_singleMode, ← sub_smul,
    zetaM_inv]
  nth_rw 1 [zetaM_eq]
  congr 1
  simp only [zM]
  ring

private lemma M₂_mul_singleMode (m : ℕ) (v : n → ℝ) :
    M₂ ℂ N * singleMode N m v = (2 * yM N m : ℂ) • singleMode N m v := by
  rw [M₂, Matrix.sub_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
    shiftPlus_mul_singleMode, shiftMinus_mul_singleMode, ← sub_smul, ← sub_smul, zetaM_inv]
  nth_rw 1 [zetaM_eq]
  congr 1
  simp only [yM]
  push_cast
  ring

omit [NeZero N] in
private lemma singleMode_mul_A [Fintype n] (m : ℕ) {A : Matrix n n ℝ} (hA : Aᵀ = A)
    {v : n → ℝ} {lamk : ℝ} (hv : A.mulVec v = lamk • v) :
    singleMode N m v * A.map (fun a : ℝ => (a : ℂ)) = (lamk : ℂ) • singleMode N m v := by
  have hv' : ∀ j, ∑ k, v k * A k j = lamk * v j := by
    intro j
    have h := congrFun hv j
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    rw [← h]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := congrFun (congrFun hA k) j
    simp only [Matrix.transpose_apply] at this
    rw [mul_comm, ← this]
  ext i j
  simp only [singleMode, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.map_apply,
    Matrix.smul_apply, smul_eq_mul]
  have h := congrArg (fun a : ℝ => (a : ℂ)) (hv' j)
  simp only [Complex.ofReal_sum, Complex.ofReal_mul] at h
  calc ∑ k, fourierMode N m i * (v k : ℂ) * (A k j : ℂ)
      = fourierMode N m i * ∑ k, (v k : ℂ) * (A k j : ℂ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = (lamk : ℂ) * (fourierMode N m i * (v j : ℂ)) := by
        rw [h]
        ring

/-- The Lax–Friedrichs field acts on the mode as multiplication by `p - 1`. -/
private lemma fLF_singleMode [Fintype n] (m : ℕ) {A : Matrix n n ℝ} (hA : Aᵀ = A)
    {v : n → ℝ} {lamk : ℝ} (hv : A.mulVec v = lamk • v) {lam dt dx : ℝ} (hdx : dx ≠ 0) (c : ℂ) :
    (dt : ℂ) • fLF (dx : ℂ) (lam : ℂ) (A.map fun a : ℝ => (a : ℂ)) (c • singleMode N m v) =
      (c * (ampP (lam * dt / dx) (lamk * dt / dx) (yM N m) (zM N m) - 1)) •
        singleMode N m v := by
  have hdx' : (dx : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hdx
  simp only [fLF, Matrix.mul_smul, Matrix.smul_mul]
  rw [Matrix.mul_assoc, singleMode_mul_A m hA hv, Matrix.mul_smul, M₁_mul_singleMode,
    M₂_mul_singleMode]
  simp only [ampP]
  push_cast
  field_simp
  module

/-- **Prop. 3.2, amplification factor** (arXiv 2507.15192).  If `A v_k = λ_k v_k`, one DtP–PSI step
from `Uⁿ = x_m v_kᵀ` gives `Uⁿ⁺¹ = g Uⁿ` with `g = p² (2 - p)`, `p = 1 - ν y_m - i ν_k z_m`,
`ν = λ Δt/Δx`, `ν_k = λ_k Δt/Δx`.  The mode is complex, so the scheme is taken over `ℂ` with `ᴴ` in
place of `ᵀ`.  The paper's tacit assumption that the projectors act trivially on the mode is not
needed: `V`, `K₀` with `K₀ Vᴴ = Uⁿ` and the orthonormal `X` with `K¹ = X S₁` are arbitrary, of any
rank.  `dtp_singleMode_instance` exhibits an instance. -/
theorem dtp_singleMode_factor [Fintype n] [DecidableEq r] (m : ℕ) {A : Matrix n n ℝ}
    (hA : Aᵀ = A) {v : n → ℝ} {lamk : ℝ} (hv : A.mulVec v = lamk • v) {lam dt dx : ℝ}
    (hdx : dx ≠ 0) {K₀ X : Matrix (Fin N) r ℂ} {V : Matrix n r ℂ} {S₁ : Matrix r r ℂ}
    (hV : Vᴴ * V = 1) (hX : Xᴴ * X = 1) (hK : K₀ * Vᴴ = singleMode N m v)
    (hQR : kStep (fLF (dx : ℂ) (lam : ℂ) (A.map fun a : ℝ => (a : ℂ))) (dt : ℂ) K₀ V = X * S₁) :
    let p := ampP (lam * dt / dx) (lamk * dt / dx) (yM N m) (zM N m)
    dtpStep (fLF (dx : ℂ) (lam : ℂ) (A.map fun a : ℝ => (a : ℂ))) (dt : ℂ) X S₁ V =
      (p ^ 2 * (2 - p)) • singleMode N m v :=
  dtpStep_of_eigen (fLF_singleMode m hA hv hdx) hV hX hK hQR

/-- The one-column matrix with column `x`. -/
def colMat {ι : Type*} (x : ι → ℂ) : Matrix ι Unit ℂ := Matrix.of fun i _ => x i

/-- The Fourier mode of arXiv 2507.15192 has unit norm: `x_mᴴ x_m = 1`. -/
theorem fourierMode_orthonormal (m : ℕ) :
    (colMat (fourierMode N m))ᴴ * colMat (fourierMode N m) = 1 := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hz : ‖zetaM N m‖ = 1 := by
    rw [zetaM, mul_comm]
    exact Complex.norm_exp_ofReal_mul_I _
  have h1 : ∀ j : Fin N, star (fourierMode N m j) * fourierMode N m j = ((N : ℝ) : ℂ)⁻¹ := by
    intro j
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [fourierMode, norm_mul, norm_pow, hz, one_pow, mul_one, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    push_cast
    rfl
  ext i j
  simp only [Matrix.mul_apply, colMat, Matrix.conjTranspose_apply, Matrix.of_apply, h1,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Matrix.one_apply_eq]
  have : ((N : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  simp [this]

omit [NeZero N] in
private lemma colMat_real_orthonormal [Fintype n] {v : n → ℝ} (hv1 : v ⬝ᵥ v = 1) :
    (colMat fun i => (v i : ℂ))ᴴ * (colMat fun i => (v i : ℂ)) = 1 := by
  ext i j
  have h : ∑ k, star ((v k : ℝ) : ℂ) * ((v k : ℝ) : ℂ) = 1 := by
    have h' := congrArg (fun a : ℝ => (a : ℂ)) hv1
    simp only [dotProduct, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_one] at h'
    simpa using h'
  simpa [colMat, Matrix.mul_apply, Matrix.one_apply] using h

omit [NeZero N] in
private lemma colMat_mul_colMat (m : ℕ) (v : n → ℝ) :
    colMat (fourierMode N m) * (colMat fun i => (v i : ℂ))ᴴ = singleMode N m v := by
  ext i j
  simp [colMat, singleMode, Matrix.mul_apply, Matrix.vecMulVec_apply]

/-- Non-vacuity of Prop. 3.2 (arXiv 2507.15192): for a unit eigenvector `v` of `A` its hypotheses
hold with `K₀ = X = x_m`, `V = v` and `S₁ = p`. -/
theorem dtp_singleMode_instance [Fintype n] (m : ℕ) {A : Matrix n n ℝ}
    (hA : Aᵀ = A) {v : n → ℝ} {lamk : ℝ} (hv : A.mulVec v = lamk • v) (hv1 : v ⬝ᵥ v = 1)
    {lam dt dx : ℝ} (hdx : dx ≠ 0) :
    let K := colMat (fourierMode N m)
    let V := colMat fun i => (v i : ℂ)
    Vᴴ * V = 1 ∧ Kᴴ * K = 1 ∧ K * Vᴴ = singleMode N m v ∧
      kStep (fLF (dx : ℂ) (lam : ℂ) (A.map fun a : ℝ => (a : ℂ))) (dt : ℂ) K V =
        K * (ampP (lam * dt / dx) (lamk * dt / dx) (yM N m) (zM N m) •
          (1 : Matrix Unit Unit ℂ)) := by
  intro K V
  have hV : Vᴴ * V = 1 := colMat_real_orthonormal hv1
  have hKV : K * Vᴴ = singleMode N m v := colMat_mul_colMat m v
  refine ⟨hV, fourierMode_orthonormal m, hKV, ?_⟩
  have hF := fLF_singleMode (N := N) m hA hv hdx (lam := lam) (dt := dt) 1
  rw [one_smul, one_mul] at hF
  rw [kStep, hKV, ← Matrix.smul_mul, hF, Matrix.smul_mul, ← hKV, Matrix.mul_assoc, hV,
    Matrix.mul_one, Matrix.mul_smul, Matrix.mul_one]
  module

/-- **Prop. 3.2, modulus** (arXiv 2507.15192):
`|g|² = ((1 - ν y)² + ν_k² z²)² ((1 + ν y)² + ν_k² z²)`, here for all real `ν, ν_k, y, z`. -/
theorem ampP_normSq (ν νk y z : ℝ) :
    let p := ampP ν νk y z
    ‖p ^ 2 * (2 - p)‖ ^ 2 = ((1 - ν * y) ^ 2 + νk ^ 2 * z ^ 2) ^ 2 *
      ((1 + ν * y) ^ 2 + νk ^ 2 * z ^ 2) := by
  intro p
  have h1 : Complex.normSq p = (1 - ν * y) ^ 2 + νk ^ 2 * z ^ 2 := by
    simp [p, ampP, Complex.normSq_apply]
    ring
  have h2 : Complex.normSq (2 - p) = (1 + ν * y) ^ 2 + νk ^ 2 * z ^ 2 := by
    simp [p, ampP, Complex.normSq_apply]
    ring
  rw [Complex.sq_norm, map_mul, map_pow, h1, h2]

/-- The symbols of arXiv 2507.15192, Sect. 2: `z_m² = y_m (2 - y_m)` and `y_m ∈ [0, 2]`. -/
theorem yM_zM (N m : ℕ) :
    zM N m ^ 2 = yM N m * (2 - yM N m) ∧ 0 ≤ yM N m ∧ yM N m ≤ 2 := by
  have h := Real.sin_sq_add_cos_sq (alphaM N m)
  have h1 := Real.cos_le_one (alphaM N m)
  have h2 := Real.neg_one_le_cos (alphaM N m)
  simp only [yM, zM]
  refine ⟨by linear_combination h, by linarith, by linarith⟩

/-- The amplification function `h_DtP(y, ν) = [1 + 2 y ν (ν - 1)]² [1 + 2 y ν (ν + 1)]`. -/
noncomputable def hDtP (y ν : ℝ) : ℝ :=
  (1 + 2 * y * ν * (ν - 1)) ^ 2 * (1 + 2 * y * ν * (ν + 1))

/-- **Prop. 3.2, maximal speed** (arXiv 2507.15192): if `|λ_k| = λ_max`, i.e. `ν_k² = ν²`, and
`z² = y (2 - y)`, then `|g|² = h_DtP(y, ν)`. -/
theorem ampP_normSq_of_max {ν νk y z : ℝ} (hνk : νk ^ 2 = ν ^ 2) (hz : z ^ 2 = y * (2 - y)) :
    let p := ampP ν νk y z
    ‖p ^ 2 * (2 - p)‖ ^ 2 = hDtP y ν := by
  have h := ampP_normSq ν νk y z
  simp only at h ⊢
  rw [h, hνk, hz, hDtP]
  ring

/-- **Prop. 3.2, stable range** (arXiv 2507.15192): `h_DtP(y, ν) ≤ 1` for `y ∈ [0, 2]` and
`0 ≤ ν ≤ 1/3`.  This follows from the library's `dtp_singleMode_stable`. -/
theorem hDtP_le_one {ν y : ℝ} (hν0 : 0 ≤ ν) (hν : ν ≤ 1 / 3) (hy0 : 0 ≤ y) (hy2 : y ≤ 2) :
    hDtP y ν ≤ 1 := by
  set θ := Real.arccos (1 - y) with hθ
  have hc : Real.cos θ = 1 - y := Real.cos_arccos (by linarith) (by linarith)
  have hs : Real.sin θ ^ 2 = y * (2 - y) := by
    have := Real.sin_sq_add_cos_sq θ
    rw [hc] at this
    linear_combination this
  have h1 := LeanDLRA.OpenProblems.Stability.dtp_singleMode_stable hν0 hν θ
  have h2 := ampP_normSq_of_max (ν := ν) (νk := ν) (y := y) (z := Real.sin θ) rfl hs
  simp only at h1 h2
  have hp : ampP ν ν y (Real.sin θ) =
      1 - (ν : ℂ) * (1 - (Real.cos θ : ℂ)) - Complex.I * ν * (Real.sin θ : ℂ) := by
    rw [ampP, hc]
    push_cast
    ring
  rw [hp] at h2
  rw [← h2]
  exact pow_le_one₀ (norm_nonneg _) h1

/-- **Prop. 3.2, instability** (arXiv 2507.15192): `h_DtP(y, ν) > 1` for all sufficiently small
`y > 0` when `ν > 1/3`. -/
theorem one_lt_hDtP {ν : ℝ} (hν : 1 / 3 < ν) : ∀ᶠ y in 𝓝[>] 0, 1 < hDtP y ν := by
  have hν0 : 0 < ν := by linarith
  set q : ℝ → ℝ := fun y => (3 * ν - 1) + (2 * y * ν) * ((3 * ν + 1) * (ν - 1)) +
    (2 * y * ν) ^ 2 * ((ν - 1) ^ 2 * (ν + 1)) with hq
  have hc : Continuous q := by fun_prop
  have h0 : 0 < q 0 := by simp [hq]; linarith
  have hev : ∀ᶠ y in 𝓝 (0 : ℝ), 0 < q y := hc.continuousAt.eventually (lt_mem_nhds h0)
  filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy hy0
  have hk : hDtP y ν - 1 = 2 * y * ν * q y := by
    simp only [hDtP, hq]
    ring
  have : 0 < 2 * y * ν * q y := by
    have hy0' : 0 < y := hy0
    positivity
  linarith

/-- **Prop. 3.2, threshold** (arXiv 2507.15192): `h_DtP(y, ν) ≤ 1` for all `y ∈ [0, 2]` iff
`ν ≤ 1/3`, for `ν ≥ 0`. -/
theorem hDtP_iff {ν : ℝ} (hν0 : 0 ≤ ν) : (∀ y ∈ Icc (0 : ℝ) 2, hDtP y ν ≤ 1) ↔ ν ≤ 1 / 3 := by
  constructor
  · intro h
    by_contra hlt
    have hev := one_lt_hDtP (not_le.1 hlt)
    have hmem : ∀ᶠ y in 𝓝[>] (0 : ℝ), y ∈ Ioo (0 : ℝ) 2 := Ioo_mem_nhdsGT (by norm_num)
    obtain ⟨y, hy1, hy2⟩ := (hev.and hmem).exists
    exact absurd (h y ⟨hy2.1.le, hy2.2.le⟩) (not_le.2 hy1)
  · exact fun h y hy => hDtP_le_one hν0 h hy.1 hy.2

/-- **Prop. 3.2, all modes** (arXiv 2507.15192): for `0 ≤ ν ≤ 1/3`, `|g| ≤ 1` also when
`|ν_k| ≤ ν`, for every symbol with `y ∈ [0, 2]`, `z² = y (2 - y)`.  The paper states the bound for
`|λ_k| = λ_max` only; the general case follows from the monotonicity of the formula for `|g|²`. -/
theorem dtp_mode_stable {ν νk y z : ℝ} (hν0 : 0 ≤ ν) (hν : ν ≤ 1 / 3) (hνk : νk ^ 2 ≤ ν ^ 2)
    (hy0 : 0 ≤ y) (hy2 : y ≤ 2) (hz : z ^ 2 = y * (2 - y)) :
    let p := ampP ν νk y z
    ‖p ^ 2 * (2 - p)‖ ≤ 1 := by
  intro p
  have h := ampP_normSq ν νk y z
  simp only at h
  have h1 : νk ^ 2 * z ^ 2 ≤ ν ^ 2 * z ^ 2 := by gcongr
  have hh := hDtP_le_one hν0 hν hy0 hy2
  have h2 : ‖p ^ 2 * (2 - p)‖ ^ 2 ≤ hDtP y ν := by
    have h3 : hDtP y ν = ((1 - ν * y) ^ 2 + ν ^ 2 * z ^ 2) ^ 2 *
        ((1 + ν * y) ^ 2 + ν ^ 2 * z ^ 2) := by
      rw [hz, hDtP]
      ring
    rw [h, h3]
    gcongr
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 (h2.trans hh)

/-- **Prop. 3.2** (arXiv 2507.15192), the threshold stated on the amplification factor: for a
maximal-speed mode (`ν_k² = ν²`, i.e. `|λ_k| = λ_max`), `|g| ≤ 1` for every symbol `(y, z)` with
`y ∈ [0, 2]` and `z² = y (2 - y)` iff `ν ≤ 1/3`. -/
theorem dtp_amplification_iff {ν νk : ℝ} (hν0 : 0 ≤ ν) (hνk : νk ^ 2 = ν ^ 2) :
    (∀ y ∈ Icc (0 : ℝ) 2, ∀ z : ℝ, z ^ 2 = y * (2 - y) →
      ‖ampP ν νk y z ^ 2 * (2 - ampP ν νk y z)‖ ≤ 1) ↔ ν ≤ 1 / 3 := by
  rw [← hDtP_iff hν0]
  constructor
  · intro h y hy
    have hyy : 0 ≤ y * (2 - y) := mul_nonneg hy.1 (by linarith [hy.2])
    have hz : Real.sqrt (y * (2 - y)) ^ 2 = y * (2 - y) := Real.sq_sqrt hyy
    have h1 := ampP_normSq_of_max (νk := νk) (ν := ν) hνk hz
    simp only at h1
    rw [← h1]
    exact pow_le_one₀ (norm_nonneg _) (h y hy _ hz)
  · intro h y hy z hz
    have h1 := ampP_normSq_of_max (νk := νk) (ν := ν) hνk hz
    simp only at h1
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 (h1.le.trans (h y hy))

end SingleMode

section Theta

variable {N : ℕ} [NeZero N] {n : Type*} [Fintype n]

/-- The equations of one parabolic θ-step (Sect. 4): backward Euler K- and L-steps and a θ-weighted
S-step, with `Ã = Vᴴ A V`, `M_{2,X} = Xᴴ M₂ X` and `τ = Δt / Δx²`.  Over `ℝ`, `ᴴ` is `ᵀ`. -/
structure IsThetaStep {r : Type*} [Fintype r] [DecidableEq r] {𝕜 : Type*} [Field 𝕜] [StarRing 𝕜]
    (τ θ : 𝕜) (A : Matrix n n 𝕜) (K₀ K₁ X : Matrix (Fin N) r 𝕜) (V : Matrix n r 𝕜)
    (S₁ S₂ : Matrix r r 𝕜) (L₁ : Matrix r n 𝕜) : Prop where
  orth : Xᴴ * X = 1
  kEq : K₁ = K₀ - τ • (M₂ 𝕜 N * K₁ * (Vᴴ * A * V))
  qr : K₁ = X * S₁
  sEq : S₂ = S₁ + τ • (Xᴴ * M₂ 𝕜 N * X * ((1 - θ) • S₁ + θ • S₂) * (Vᴴ * A * V))
  lEq : L₁ = S₂ * Vᴴ - τ • (Xᴴ * M₂ 𝕜 N * X * L₁ * A)

/-- The single-mode amplification factor
`g_θ(ψ) = (1 + (1 - θ) ψ) / ((1 + ψ)² (1 - θ ψ))`. -/
noncomputable def gTheta (θ ψ : ℝ) : ℝ := (1 + (1 - θ) * ψ) / ((1 + ψ) ^ 2 * (1 - θ * ψ))

open scoped ComplexOrder in
private lemma eq_zero_of_add_mul {a b c' : Type*} [Finite a] [Fintype b] [Fintype c']
    {Z : Matrix a b ℂ} {B : Matrix c' b ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : Z + (c : ℂ) • (Z * (Bᴴ * B)) = 0) : Z = 0 := by
  classical
  have := Fintype.ofFinite a
  have h1 : (Z * Zᴴ).trace + (c : ℂ) * ((B * Zᴴ)ᴴ * (B * Zᴴ)).trace = 0 := by
    have h2 := congrArg (fun M => (M * Zᴴ).trace) h
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
      Matrix.zero_mul, Matrix.trace_zero, smul_eq_mul] at h2
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simpa only [Matrix.mul_assoc] using h2
  have h3 : 0 ≤ (Z * Zᴴ).trace := (Matrix.posSemidef_self_mul_conjTranspose Z).trace_nonneg
  have h4 : 0 ≤ ((B * Zᴴ)ᴴ * (B * Zᴴ)).trace :=
    (Matrix.posSemidef_conjTranspose_mul_self _).trace_nonneg
  have h5 : (Z * Zᴴ).trace = 0 := by
    have h3' := Complex.le_def.1 h3
    have h4' := Complex.le_def.1 h4
    have h6 := congrArg Complex.re h1
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, Complex.zero_re] at h6
    have h7 : 0 ≤ c * ((B * Zᴴ)ᴴ * (B * Zᴴ)).trace.re := mul_nonneg hc (by simpa using h4'.1)
    have h8 : 0 ≤ (Z * Zᴴ).trace.re := by simpa using h3'.1
    apply Complex.ext
    · simp only [Complex.zero_re]
      linarith
    · simpa using h3'.2.symm
  exact Matrix.trace_mul_conjTranspose_self_eq_zero_iff.1 h5

private lemma conjTranspose_shiftPlus : (shiftPlus ℂ N)ᴴ = shiftMinus ℂ N := by
  ext i j
  simp only [Matrix.conjTranspose_apply, shiftPlus, shiftMinus, Matrix.of_apply]
  split_ifs <;> simp_all [eq_comm]

private lemma M₂_eq_conjTranspose_mul :
    M₂ ℂ N = (1 - shiftPlus ℂ N)ᴴ * (1 - shiftPlus ℂ N) := by
  have h₂ := shiftMinus_mul_shiftPlus (𝕜 := ℂ) (N := N)
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, conjTranspose_shiftPlus,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, h₂, M₂]
  module

private lemma eq_zero_of_add_M₂ {s : Type*} [Finite s] {Z : Matrix (Fin N) s ℂ} {c : ℝ}
    (hc : 0 ≤ c) (h : Z + (c : ℂ) • (M₂ ℂ N * Z) = 0) : Z = 0 := by
  have hH : (M₂ ℂ N)ᴴ = M₂ ℂ N := by
    rw [M₂_eq_conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have h1 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hH,
    Matrix.conjTranspose_zero, Complex.star_def, Complex.conj_ofReal] at h1
  rw [M₂_eq_conjTranspose_mul] at h1
  have h2 := eq_zero_of_add_mul hc h1
  simpa using congrArg Matrix.conjTranspose h2

open scoped MatrixOrder in
private lemma exists_factor {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    ∃ B : Matrix n n ℝ, A = Bᵀ * B := by
  classical
  have h0 : 0 ≤ A := Matrix.nonneg_iff_posSemidef.2 hA
  have h1 : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A h0
  have h2 : (CFC.sqrt A).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg A)).isHermitian
  have h3 : (CFC.sqrt A)ᵀ = CFC.sqrt A := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact h2
  exact ⟨CFC.sqrt A, by rw [h3, h1]⟩

private lemma eq_zero_of_add_A {s : Type*} [Finite s] {A : Matrix n n ℝ} (hA : A.PosSemidef)
    {Z : Matrix s n ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : Z + (c : ℂ) • (Z * A.map fun a : ℝ => (a : ℂ)) = 0) : Z = 0 := by
  obtain ⟨B, hB⟩ := exists_factor hA
  have hAc : (A.map fun a : ℝ => (a : ℂ)) =
      (B.map fun a : ℝ => (a : ℂ))ᴴ * B.map fun a : ℝ => (a : ℂ) := by
    ext i j
    rw [hB]
    simp [Matrix.mul_apply]
  rw [hAc] at h
  exact eq_zero_of_add_mul hc h

omit [NeZero N] in
private lemma colMat_fourier_eq (m : ℕ) :
    colMat (fourierMode N m) = singleMode N m (fun _ : Unit => (1 : ℝ)) := by
  ext i j
  simp [colMat, singleMode, Matrix.vecMulVec_apply]

private lemma M₂_mul_colMat (m : ℕ) :
    M₂ ℂ N * colMat (fourierMode N m) = (2 * yM N m : ℂ) • colMat (fourierMode N m) := by
  rw [colMat_fourier_eq, M₂_mul_singleMode]

private lemma map_mul_colMat {A : Matrix n n ℝ} {v : n → ℝ} {lamk : ℝ}
    (hv : A.mulVec v = lamk • v) :
    (A.map fun a : ℝ => (a : ℂ)) * (colMat fun i => (v i : ℂ)) =
      (lamk : ℂ) • colMat fun i => (v i : ℂ) := by
  ext i j
  have h := congrArg (fun a : ℝ => (a : ℂ)) (congrFun hv i)
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Complex.ofReal_sum,
    Complex.ofReal_mul] at h
  simpa [Matrix.mul_apply, colMat] using h

private lemma colMat_conj_mul_map {A : Matrix n n ℝ} (hA : A.IsHermitian) {v : n → ℝ} {lamk : ℝ}
    (hv : A.mulVec v = lamk • v) :
    (colMat fun i => (v i : ℂ))ᴴ * (A.map fun a : ℝ => (a : ℂ)) =
      (lamk : ℂ) • (colMat fun i => (v i : ℂ))ᴴ := by
  have hH : (A.map fun a : ℝ => (a : ℂ))ᴴ = A.map fun a : ℝ => (a : ℂ) := by
    ext i j
    have := congrFun (congrFun hA i) j
    simp only [Matrix.conjTranspose_apply, star_trivial] at this
    simp [this]
  have h := congrArg Matrix.conjTranspose (map_mul_colMat hv)
  simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, hH] using h

/-- **Prop. 4.2, amplification factor** (arXiv 2507.15192).  Let `A ⪰ 0`, `A v_k = λ_k v_k`,
`‖v_k‖ = 1`, `τ = Δt/Δx² ≥ 0` and `ψ = 2 λ_k τ y_m = 2 μ_k y_m`.  If `θ ψ ≠ 1`, then every solution
of the equations of the θ-step from `Uⁿ = x_m v_kᵀ` has `Uⁿ⁺¹ = g_θ(ψ) Uⁿ`.  Differences from the
paper: rank one with `X⁰ = x_m`, `V⁰ = v_k`; the mode is complex, so `ᴴ` replaces `ᵀ`; the new basis
`X` is not assumed, it is a multiple of `x_m` by the QR step.  Solutions exist by
`theta_singleMode_exists`. -/
theorem theta_singleMode (m : ℕ) {A : Matrix n n ℝ} (hA : A.PosSemidef)
    {v : n → ℝ} {lamk : ℝ} (hv : A.mulVec v = lamk • v) (hv1 : v ⬝ᵥ v = 1) {τ θ : ℝ} (hτ : 0 ≤ τ)
    (hθ : 1 - θ * (2 * (lamk * τ) * yM N m) ≠ 0)
    {K₁ X : Matrix (Fin N) Unit ℂ} {S₁ S₂ : Matrix Unit Unit ℂ} {L₁ : Matrix Unit n ℂ}
    (hstep : IsThetaStep (τ : ℂ) (θ : ℂ) (A.map fun a : ℝ => (a : ℂ)) (colMat (fourierMode N m))
      K₁ X (colMat fun i => (v i : ℂ)) S₁ S₂ L₁) :
    X * L₁ = ((gTheta θ (2 * (lamk * τ) * yM N m) : ℝ) : ℂ) • singleMode N m v := by
  set K := colMat (fourierMode N m) with hKdef
  set Vc : Matrix n Unit ℂ := colMat fun i => (v i : ℂ) with hVdef
  set Ac : Matrix n n ℂ := A.map fun a : ℝ => (a : ℂ) with hAdef
  set y := yM N m with hy
  set ψ := 2 * (lamk * τ) * y with hψ
  have hlamk : 0 ≤ lamk := by
    have h := hA.dotProduct_mulVec_nonneg v
    simpa [hv, dotProduct_smul, hv1] using h
  have hy0 : 0 ≤ y := (yM_zM N m).2.1
  have hψ0 : 0 ≤ ψ := by positivity
  have hψc : ((1 : ℂ) + ψ) ≠ 0 := by
    have : (1 + ψ : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  have hVV : Vcᴴ * Vc = 1 := colMat_real_orthonormal hv1
  have hKK : Kᴴ * K = 1 := fourierMode_orthonormal m
  have hVA : Vcᴴ * Ac = (lamk : ℂ) • Vcᴴ := colMat_conj_mul_map hA.isHermitian hv
  have hVt : Vcᴴ * Ac * Vc = (lamk : ℂ) • 1 := by
    rw [hVA, Matrix.smul_mul, hVV]
  have hM2K : M₂ ℂ N * K = (2 * y : ℂ) • K := M₂_mul_colMat m
  set a : ℂ := (1 + ψ : ℂ)⁻¹ with ha
  have ha1 : a * (1 + ψ) = 1 := inv_mul_cancel₀ hψc
  have hψe : (ψ : ℂ) = 2 * ((lamk : ℂ) * τ) * y := by
    rw [hψ]
    push_cast
    ring
  -- K-step
  have hK₁ : K₁ = a • K := by
    have h1 : K₁ + ((lamk * τ : ℝ) : ℂ) • (M₂ ℂ N * K₁) = K := by
      have h2 := hstep.kEq
      rw [hVt, Matrix.mul_smul, Matrix.mul_one, smul_smul] at h2
      push_cast
      rw [mul_comm (lamk : ℂ)]
      nth_rw 1 [h2]
      abel
    have hs : a + ((lamk * τ : ℝ) : ℂ) * a * (2 * y) = 1 := by
      push_cast
      linear_combination ha1 - a * hψe
    have h3 := eq_zero_of_add_M₂ (Z := K₁ - a • K) (c := lamk * τ) (by positivity) (by
      rw [Matrix.mul_sub, Matrix.mul_smul, hM2K, smul_sub, smul_smul, smul_smul, sub_add_sub_comm,
        h1, ← add_smul, hs, one_smul, sub_self])
    exact sub_eq_zero.1 h3
  -- the basis `X` is a multiple of `x_m`
  set s : ℂ := S₁ () () with hs
  have hS₁ : S₁ = s • 1 := by
    ext i j
    cases i
    cases j
    simp [hs]
  have hXs : s • X = a • K := by
    rw [← hK₁, hstep.qr, hS₁, Matrix.mul_smul, Matrix.mul_one]
  have ha0 : a ≠ 0 := inv_ne_zero hψc
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hXs
    have hK0 : K = 0 := (smul_eq_zero.1 hXs.symm).resolve_left ha0
    rw [hK0] at hKK
    simp at hKK
  have hX : X = (s⁻¹ * a) • K := by
    rw [mul_smul, ← hXs, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  have hM2X : M₂ ℂ N * X = (2 * y : ℂ) • X := by
    rw [hX, Matrix.mul_smul, hM2K, smul_comm]
  have hMX : Xᴴ * M₂ ℂ N * X = (2 * y : ℂ) • 1 := by
    rw [Matrix.mul_assoc, hM2X, Matrix.mul_smul, hstep.orth]
  -- S-step
  have hc : (1 : ℂ) - θ * ψ ≠ 0 := by
    have : ((1 - θ * ψ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hθ
    simpa using this
  set b : ℂ := ((1 : ℂ) + (1 - θ) * ψ) / (1 - θ * ψ) with hb
  have hS₂ : S₂ = b • S₁ := by
    have h := hstep.sEq
    rw [hMX, hVt] at h
    have hW : ∀ W : Matrix Unit Unit ℂ,
        (τ : ℂ) • (((2 * y : ℂ) • (1 : Matrix Unit Unit ℂ)) * W * ((lamk : ℂ) • 1)) =
          (ψ : ℂ) • W := by
      intro W
      rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, smul_smul,
        hψe]
      congr 1
      ring
    rw [hW] at h
    have h2 : ((1 : ℂ) - θ * ψ) • S₂ = ((1 : ℂ) + (1 - θ) * ψ) • S₁ := by
      linear_combination (norm := module) h
    rw [hb, div_eq_inv_mul, mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hc, one_smul]
  -- L-step
  have hL₁ : L₁ = a • (S₂ * Vcᴴ) := by
    have h1 : L₁ + ((2 * y * τ : ℝ) : ℂ) • (L₁ * Ac) = S₂ * Vcᴴ := by
      have h2 := hstep.lEq
      rw [hMX, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, smul_smul] at h2
      push_cast
      linear_combination (norm := module) h2
    have hs' : a + ((2 * y * τ : ℝ) : ℂ) * a * lamk = 1 := by
      push_cast
      linear_combination ha1 - a * hψe
    have h3 := eq_zero_of_add_A hA (Z := L₁ - a • (S₂ * Vcᴴ)) (c := 2 * y * τ) (by positivity) (by
      rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc S₂, hVA, Matrix.mul_smul, smul_sub,
        smul_smul, smul_smul, sub_add_sub_comm, h1, ← add_smul, hs', one_smul, sub_self])
    exact sub_eq_zero.1 h3
  have hXS₂ : X * S₂ = (b * a) • K := by
    rw [hS₂, Matrix.mul_smul, ← hstep.qr, hK₁, smul_smul]
  rw [hL₁, Matrix.mul_smul, ← Matrix.mul_assoc, hXS₂, Matrix.smul_mul, hKdef, hVdef,
    colMat_mul_colMat, smul_smul]
  congr 1
  have h1ψ : (1 + (ψ : ℂ)) ≠ 0 := hψc
  simp only [gTheta]
  push_cast
  rw [ha, hb]
  field_simp

/-- Non-vacuity of Prop. 4.2 (arXiv 2507.15192): under the hypotheses of `theta_singleMode`, the
equations of the θ-step from the mode have a solution. -/
theorem theta_singleMode_exists (m : ℕ) {A : Matrix n n ℝ} (hA : A.PosSemidef) {v : n → ℝ}
    {lamk : ℝ} (hv : A.mulVec v = lamk • v) (hv1 : v ⬝ᵥ v = 1) {τ θ : ℝ} (hτ : 0 ≤ τ)
    (hθ : 1 - θ * (2 * (lamk * τ) * yM N m) ≠ 0) :
    ∃ (K₁ X : Matrix (Fin N) Unit ℂ) (S₁ S₂ : Matrix Unit Unit ℂ) (L₁ : Matrix Unit n ℂ),
      IsThetaStep (τ : ℂ) (θ : ℂ) (A.map fun a : ℝ => (a : ℂ)) (colMat (fourierMode N m))
        K₁ X (colMat fun i => (v i : ℂ)) S₁ S₂ L₁ := by
  set K := colMat (fourierMode N m) with hKdef
  set Vc : Matrix n Unit ℂ := colMat fun i => (v i : ℂ) with hVdef
  set Ac : Matrix n n ℂ := A.map fun a : ℝ => (a : ℂ) with hAdef
  set y := yM N m with hy
  set ψ := 2 * (lamk * τ) * y with hψ
  have hlamk : 0 ≤ lamk := by
    have h := hA.dotProduct_mulVec_nonneg v
    simpa [hv, dotProduct_smul, hv1] using h
  have hy0 : 0 ≤ y := (yM_zM N m).2.1
  have hψ0 : 0 ≤ ψ := by positivity
  have hψc : ((1 : ℂ) + ψ) ≠ 0 := by
    have : (1 + ψ : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  have hc : (1 : ℂ) - θ * ψ ≠ 0 := by
    have : ((1 - θ * ψ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hθ
    simpa using this
  have hVV : Vcᴴ * Vc = 1 := colMat_real_orthonormal hv1
  have hKK : Kᴴ * K = 1 := fourierMode_orthonormal m
  have hVA : Vcᴴ * Ac = (lamk : ℂ) • Vcᴴ := colMat_conj_mul_map hA.isHermitian hv
  have hVt : Vcᴴ * Ac * Vc = (lamk : ℂ) • 1 := by
    rw [hVA, Matrix.smul_mul, hVV]
  have hM2K : M₂ ℂ N * K = (2 * y : ℂ) • K := M₂_mul_colMat m
  have hMX : Kᴴ * M₂ ℂ N * K = (2 * y : ℂ) • 1 := by
    rw [Matrix.mul_assoc, hM2K, Matrix.mul_smul, hKK]
  set a : ℂ := (1 + ψ : ℂ)⁻¹ with ha
  have ha1 : a * (1 + ψ) = 1 := inv_mul_cancel₀ hψc
  have hψe : (ψ : ℂ) = 2 * ((lamk : ℂ) * τ) * y := by
    rw [hψ]
    push_cast
    ring
  set b : ℂ := ((1 : ℂ) + (1 - θ) * ψ) / (1 - θ * ψ) with hb
  have hb1 : b * (1 - θ * ψ) = (1 : ℂ) + (1 - θ) * ψ := div_mul_cancel₀ _ hc
  refine ⟨a • K, K, a • 1, (b * a) • 1, (a * b * a) • Vcᴴ, ⟨hKK, ?_, ?_, ?_, ?_⟩⟩
  · rw [hVt, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul, hM2K, smul_smul, smul_smul,
      smul_smul]
    have h1 : (1 : ℂ) - τ * lamk * a * (2 * y) = a := by
      linear_combination (-1 : ℂ) * ha1 + a * hψe
    nth_rw 1 [← h1]
    rw [sub_smul, one_smul]
  · rw [Matrix.mul_smul, Matrix.mul_one]
  · have hW : ∀ W : Matrix Unit Unit ℂ,
        (τ : ℂ) • (((2 * y : ℂ) • (1 : Matrix Unit Unit ℂ)) * W * ((lamk : ℂ) • 1)) =
          ((τ : ℂ) * (2 * y) * lamk) • W := by
      intro W
      rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, smul_smul]
      congr 1
      ring
    have key : b * a = a + (τ : ℂ) * (2 * y) * lamk * ((1 - θ) * a + θ * (b * a)) := by
      linear_combination a * hb1 + ((θ : ℂ) * a * b + (1 - θ) * a) * hψe
    rw [hMX, hVt, hW]
    calc (b * a) • (1 : Matrix Unit Unit ℂ)
        = (a + (τ : ℂ) * (2 * y) * lamk * ((1 - θ) * a + θ * (b * a))) • 1 := by rw [← key]
      _ = _ := by module
  · have key : a * b * a = b * a - (τ : ℂ) * (2 * y) * (a * b * a) * lamk := by
      linear_combination (b * a) * ha1 - (b * a * a) * hψe
    have h1 : ((2 * y : ℂ) • (1 : Matrix Unit Unit ℂ)) * ((a * b * a) • Vcᴴ) * Ac =
        ((2 * y : ℂ) * (a * b * a) * lamk) • Vcᴴ := by
      rw [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.smul_mul, hVA, smul_smul,
        smul_smul]
    rw [hMX, h1, Matrix.smul_mul, Matrix.one_mul]
    calc (a * b * a) • Vcᴴ
        = (b * a - (τ : ℂ) * (2 * y) * (a * b * a) * lamk) • Vcᴴ := by rw [← key]
      _ = _ := by module

/-- **Prop. 4.2, `θ = 0`** (arXiv 2507.15192): `g₀(ψ) = 1 / (1 + ψ) ∈ (0, 1]` for `ψ ≥ 0`. -/
theorem gTheta_zero {ψ : ℝ} (hψ : 0 ≤ ψ) :
    gTheta 0 ψ = 1 / (1 + ψ) ∧ 0 < gTheta 0 ψ ∧ gTheta 0 ψ ≤ 1 := by
  have h1 : 0 < 1 + ψ := by linarith
  have h : gTheta 0 ψ = 1 / (1 + ψ) := by
    simp only [gTheta]
    field_simp
    ring
  refine ⟨h, ?_, ?_⟩
  · rw [h]
    positivity
  · rw [h, div_le_one h1]
    linarith

/-- **Prop. 4.2, `θ > 0`** (arXiv 2507.15192): `g_θ(ψ) → +∞` as `ψ → 1/θ` from below.  The paper
assumes `θ ≠ 1/2` as well; this is not needed. -/
theorem gTheta_tendsto {θ : ℝ} (hθ : 0 < θ) : Tendsto (gTheta θ) (𝓝[<] (1 / θ)) atTop := by
  have hd : (1 + 1 / θ) ≠ 0 := by positivity
  have hnum : Tendsto (fun ψ : ℝ => (1 + (1 - θ) * ψ) / (1 + ψ) ^ 2) (𝓝[<] (1 / θ))
      (𝓝 ((1 + (1 - θ) * (1 / θ)) / (1 + 1 / θ) ^ 2)) := by
    refine ContinuousAt.tendsto ?_ |>.mono_left nhdsWithin_le_nhds
    refine ContinuousAt.div₀ (by fun_prop) (by fun_prop) ?_
    positivity
  have hC : 0 < (1 + (1 - θ) * (1 / θ)) / (1 + 1 / θ) ^ 2 := by
    have : 1 + (1 - θ) * (1 / θ) = 1 / θ := by
      field_simp
      ring
    rw [this]
    positivity
  have hden : Tendsto (fun ψ : ℝ => (1 - θ * ψ)⁻¹) (𝓝[<] (1 / θ)) atTop := by
    have hg : Tendsto (fun ψ : ℝ => 1 - θ * ψ) (𝓝[<] (1 / θ)) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have h1 : Tendsto (fun ψ : ℝ => 1 - θ * ψ) (𝓝 (1 / θ)) (𝓝 (1 - θ * (1 / θ))) :=
          (by fun_prop : Continuous fun ψ : ℝ => 1 - θ * ψ).tendsto _
        have h2 : 1 - θ * (1 / θ) = 0 := by
          field_simp
          ring
        rw [h2] at h1
        exact h1.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ψ hψ
        have h3 : ψ < 1 / θ := hψ
        rw [lt_div_iff₀ hθ] at h3
        simp only [Set.mem_Ioi]
        linarith
    exact tendsto_inv_nhdsGT_zero.comp hg
  refine (hnum.pos_mul_atTop hC hden).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ψ _
  simp only [gTheta, div_eq_mul_inv, mul_inv]
  ring

/-- **Prop. 4.2** (arXiv 2507.15192): every `θ > 0` fails to be unconditionally stable.  For a mode
with `λ_k > 0` and `y_m > 0` the amplification factor `g_θ(ψ_{m,k})`, `ψ_{m,k} = 2 λ_k τ y_m`,
exceeds every bound for suitable `τ = Δt/Δx²` with `θ ψ_{m,k} < 1`, so that the θ-step is well
defined (`theta_singleMode`, `theta_singleMode_exists`). -/
theorem theta_unbounded {θ lamk y : ℝ} (hθ : 0 < θ) (hlamk : 0 < lamk) (hy : 0 < y) (C : ℝ) :
    ∃ τ : ℝ, 0 < τ ∧ θ * (2 * (lamk * τ) * y) < 1 ∧ C < gTheta θ (2 * (lamk * τ) * y) := by
  have hev := (gTheta_tendsto hθ).eventually (eventually_gt_atTop C)
  have hmem : ∀ᶠ ψ in 𝓝[<] (1 / θ), ψ ∈ Ioo (0 : ℝ) (1 / θ) :=
    Ioo_mem_nhdsLT (by positivity)
  obtain ⟨ψ, hψ1, hψ2⟩ := (hev.and hmem).exists
  have hψe : 2 * (lamk * (ψ / (2 * lamk * y))) * y = ψ := by
    field_simp
  refine ⟨ψ / (2 * lamk * y), div_pos hψ2.1 (by positivity), ?_, ?_⟩
  · rw [hψe]
    have := hψ2.2
    rwa [lt_div_iff₀ hθ, mul_comm] at this
  · rw [hψe]
    exact hψ1

end Theta

end LeanDLRA.Literature.P2507_15192
