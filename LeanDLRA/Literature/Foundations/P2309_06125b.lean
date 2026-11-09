import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2309.06125: Low-rank retractions and DLRA (accelerated forward Euler)

This module proves the abstract core of Sec. 4.1.3, eq. (38): accelerated forward Euler with a
second-order retraction has local error `O(Δt³)`.  The manifold `M_r` of rank-`r` matrices is
abstracted to an arbitrary subset `M` of a normed space with a tangent projector `Π` at the base
point `Y₀`; the only manifold fact used is `NormalAccelDeterminedByVelocity` (the normal
acceleration of a `C²` curve in `M` depends only on its velocity, i.e. the second fundamental form
exists), a standard fact for embedded `C²` submanifolds that is a hypothesis here.  For `M_r` it is
not proved in the library, so the `M_r` case of the result is conditional on it.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2309_06125

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A `C³` function on an open set of `ℝ` containing `0` whose value, velocity and acceleration
vanish at `0` is `O(h³)` near `0`. -/
theorem isBigO_cube_of_jet_zero {d : ℝ → E} {s : Set ℝ} (hs : IsOpen s) (h0 : (0 : ℝ) ∈ s)
    (hd : ContDiffOn ℝ 3 d s) (d0 : d 0 = 0) (d1 : deriv d 0 = 0)
    (d2 : deriv (deriv d) 0 = 0) : d =O[𝓝 0] fun h : ℝ => h ^ 3 := by
  have h1 : ContDiffOn ℝ 2 (deriv d) s := by
    have := (contDiffOn_succ_iff_deriv_of_isOpen hs (n := 2)).1 hd
    exact this.2.2
  have h2 : ContDiffOn ℝ 1 (deriv (deriv d)) s := by
    have := (contDiffOn_succ_iff_deriv_of_isOpen hs (n := 1)).1 h1
    exact this.2.2
  have h3 : ContinuousOn (deriv (deriv (deriv d))) s := by
    have := (contDiffOn_succ_iff_deriv_of_isOpen hs (n := 0)).1 h2
    exact this.2.2.continuousOn
  have hd1 : DifferentiableOn ℝ d s := ((contDiffOn_succ_iff_deriv_of_isOpen hs (n := 2)).1 hd).1
  have hd2 : DifferentiableOn ℝ (deriv d) s :=
    ((contDiffOn_succ_iff_deriv_of_isOpen hs (n := 1)).1 h1).1
  have hd3 : DifferentiableOn ℝ (deriv (deriv d)) s :=
    ((contDiffOn_succ_iff_deriv_of_isOpen hs (n := 0)).1 h2).1
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hs 0 h0
  have hsub : Icc (-(r / 2)) (r / 2) ⊆ s := by
    intro x hx
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact (abs_le.2 ⟨hx.1, hx.2⟩).trans_lt (by linarith)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -(r / 2)) (b := r / 2)).exists_bound_of_continuousOn
    (h3.mono hsub)
  have hrr : 0 < r / 2 := by positivity
  have hmem : ∀ x : ℝ, |x| ≤ r / 2 → x ∈ s := fun x hx => hsub (abs_le.1 hx)
  -- bound on `d''`
  have b2 : ∀ x : ℝ, |x| ≤ r / 2 → ‖deriv (deriv d) x‖ ≤ M * |x| := by
    intro x hx
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv (deriv d))
      (s := Icc (-(r / 2)) (r / 2)) (C := M) (x := 0) (y := x)
      (fun y hy => (hd3 y (hsub hy)).differentiableAt (hs.mem_nhds (hsub hy)))
      (fun y hy => hM y hy) (convex_Icc _ _) (by constructor <;> linarith)
      (abs_le.1 hx)
    simpa [d2] using this
  have b1 : ∀ x : ℝ, |x| ≤ r / 2 → ‖deriv d x‖ ≤ M * |x| ^ 2 := by
    intro x hx
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv d)
      (s := Icc (-|x|) |x|) (C := M * |x|) (x := 0) (y := x)
      (fun y hy => (hd2 y (hmem y ((abs_le.2 hy).trans hx))).differentiableAt
        (hs.mem_nhds (hmem y ((abs_le.2 hy).trans hx))))
      (fun y hy => by
        have hy' : |y| ≤ |x| := abs_le.2 hy
        calc ‖deriv (deriv d) y‖ ≤ M * |y| := b2 y (hy'.trans hx)
          _ ≤ M * |x| := mul_le_mul_of_nonneg_left hy' (le_trans (norm_nonneg _)
              (by simpa using hM 0 (by constructor <;> linarith))))
      (convex_Icc _ _) (by constructor <;> linarith [abs_nonneg x])
      (abs_le.1 le_rfl)
    simpa [d1, sq, mul_assoc] using this
  have b0 : ∀ x : ℝ, |x| ≤ r / 2 → ‖d x‖ ≤ M * |x| ^ 3 := by
    intro x hx
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := d)
      (s := Icc (-|x|) |x|) (C := M * |x| ^ 2) (x := 0) (y := x)
      (fun y hy => (hd1 y (hmem y ((abs_le.2 hy).trans hx))).differentiableAt
        (hs.mem_nhds (hmem y ((abs_le.2 hy).trans hx))))
      (fun y hy => by
        have hy' : |y| ≤ |x| := abs_le.2 hy
        calc ‖deriv d y‖ ≤ M * |y| ^ 2 := b1 y (hy'.trans hx)
          _ ≤ M * |x| ^ 2 := mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (abs_nonneg _) hy' 2) (le_trans (norm_nonneg _)
              (by simpa using hM 0 (by constructor <;> linarith))))
      (convex_Icc _ _) (by constructor <;> linarith [abs_nonneg x])
      (abs_le.1 le_rfl)
    simpa [d0, sq, pow_succ, mul_assoc] using this
  refine Asymptotics.IsBigO.of_bound M ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hrr] with x hx
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
  simpa [Real.norm_eq_abs, abs_pow] using b0 x hx.le


/-- The quadratic curve `h ↦ h v + (h²/2) a` fed to a retraction in the accelerated Euler step. -/
noncomputable def quadCurve (v a : E) (h : ℝ) : E := h • v + (h ^ 2 / 2) • a

theorem hasDerivAt_quadCurve (v a : E) (h : ℝ) :
    HasDerivAt (quadCurve v a) (v + h • a) h := by
  have h1 : HasDerivAt (fun h : ℝ => h • v) v h := by simpa using (hasDerivAt_id h).smul_const v
  have h2 : HasDerivAt (fun h : ℝ => (h ^ 2 / 2) • a) (h • a) h := by
    have : HasDerivAt (fun h : ℝ => h ^ 2 / 2) h h := by
      simpa using ((hasDerivAt_pow 2 h).div_const 2)
    simpa using this.smul_const a
  exact h1.add h2

/-- Second derivative of a `C²` map along `quadCurve`: `D²R(0)(v,v) + DR(0) a`. -/
theorem deriv_deriv_comp_quadCurve {R : E → E} (hR : ContDiff ℝ 2 R) (v a : E) :
    deriv (deriv (fun h => R (quadCurve v a h))) 0 =
      fderiv ℝ (fderiv ℝ R) 0 v v + fderiv ℝ R 0 a := by
  have hd1 : ∀ h : ℝ, HasDerivAt (fun h => R (quadCurve v a h))
      (fderiv ℝ R (quadCurve v a h) (v + h • a)) h := fun h =>
    ((hR.differentiable (by norm_num)).differentiableAt.hasFDerivAt).comp_hasDerivAt h
      (hasDerivAt_quadCurve v a h)
  have hfun : deriv (fun h => R (quadCurve v a h)) =
      fun h => fderiv ℝ R (quadCurve v a h) (v + h • a) := funext fun h => (hd1 h).deriv
  rw [hfun]
  have hF : ContDiff ℝ 1 (fderiv ℝ R) := hR.fderiv_right (by norm_num)
  have hq0 : quadCurve v a 0 = 0 := by simp [quadCurve]
  have hA : HasDerivAt (fun h => fderiv ℝ R (quadCurve v a h))
      (fderiv ℝ (fderiv ℝ R) (quadCurve v a 0) (v + (0 : ℝ) • a)) 0 :=
    ((hF.differentiable (by norm_num)).differentiableAt.hasFDerivAt).comp_hasDerivAt 0
      (hasDerivAt_quadCurve v a 0)
  have hB : HasDerivAt (fun h : ℝ => v + h • a) a 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const a |>.const_add v
  have := hA.clm_apply hB
  rw [this.deriv]
  simp [hq0]


/-- The manifold fact behind second-order retractions: two `C²` curves in `M` through `Y₀` with
the same velocity have the same normal acceleration `(1 - Π) c''(0)` (the second fundamental
form of `M` at `Y₀` evaluated on the velocity).  `Π` is the tangent projector at `Y₀`.  This is a
standard property of embedded `C²` submanifolds, such as the manifold `M_r` of rank-`r` matrices;
it is not proved in the library for `M_r` (only for the parabola below). -/
def NormalAccelDeterminedByVelocity (M : Set E) (Pi : E →L[ℝ] E) (Y₀ : E) : Prop :=
  ∀ c d : ℝ → E, ContDiffAt ℝ 2 c 0 → ContDiffAt ℝ 2 d 0 → c 0 = Y₀ → d 0 = Y₀ →
    (∀ᶠ t in 𝓝 0, c t ∈ M) → (∀ᶠ t in 𝓝 0, d t ∈ M) → deriv c 0 = deriv d 0 →
    (1 - Pi) (deriv (deriv c) 0) = (1 - Pi) (deriv (deriv d) 0)

/-- **Accelerated forward Euler with a second-order retraction has local error `O(Δt³)`**
(arXiv 2309.06125, Sec. 4.1.3, eq. (38)).

Abstract core, stated on a normed space `E` instead of `M_r ⊆ ℝ^{m×n}`.  Data: a set `M` (the
manifold), a projector `Π` (tangent projector at `Y₀`, only idempotency is assumed), and the
manifold fact `NormalAccelDeterminedByVelocity` (true for every embedded `C²` submanifold).
`R` is the retraction `R_{Y₀}` extended to all of `E` (replace a retraction defined on the tangent
space `range Π` by `R ∘ Π`); it is `C³`, maps tangent vectors into `M`, satisfies `R 0 = Y₀`, is
the identity to first order on the tangent space (`DR(0) z = z`) and is **second order**: the
curve `s ↦ R(s z)` has tangentially vanishing acceleration, `Π (d²/ds² R(s z))(0) = 0`.
`Y` is a `C³` curve in `M` on an open set containing `t₀` (the DLRA solution) with tangent
velocity `Π Ẏ(t₀) = Ẏ(t₀)`.  The accelerated Euler step is
`Y₁ = R(Δt Ẏ(t₀) + ½ Δt² Π Ÿ(t₀))`, where `Π Ÿ(t₀) = Π DF[Π F] + W(Π F, Π⊥ F)` is the tangential
acceleration of the DLRA solution (Prop. 6 of the paper).  Conclusion: `Y(t₀ + Δt) - Y₁ = O(Δt³)`
as `Δt → 0`.  Differences from the paper: manifold `M_r` abstracted as above, and the paper's
appeal to (28) (from [Sé23]) replaced by a direct jet argument; `R` is required to be `C³` on all
of `E` and `M`-valued on all of `range Π`, while a retraction is only defined near `0` (stronger
hypothesis).  Conditional for `M_r`: `NormalAccelDeterminedByVelocity` is assumed, not proved,
there. -/
theorem accelerated_euler_local_error (M : Set E) (Pi : E →L[ℝ] E) (hPi : ∀ x, Pi (Pi x) = Pi x)
    (Y₀ : E) (hII : NormalAccelDeterminedByVelocity M Pi Y₀)
    (R : E → E) (hR : ContDiff ℝ 3 R) (hRM : ∀ z ∈ range Pi, R z ∈ M) (hR0 : R 0 = Y₀)
    (hR1 : ∀ z ∈ range Pi, fderiv ℝ R 0 z = z)
    (hR2 : ∀ z ∈ range Pi, Pi (deriv (deriv fun s : ℝ => R (s • z)) 0) = 0)
    (Y : ℝ → E) (t₀ : ℝ) (S : Set ℝ) (hS : IsOpen S) (ht₀ : t₀ ∈ S)
    (hY : ContDiffOn ℝ 3 Y S) (hYM : ∀ t ∈ S, Y t ∈ M) (hY0 : Y t₀ = Y₀)
    (hv : Pi (deriv Y t₀) = deriv Y t₀) :
    (fun h : ℝ => Y (t₀ + h) - R (quadCurve (deriv Y t₀) (Pi (deriv (deriv Y) t₀)) h))
      =O[𝓝 0] fun h : ℝ => h ^ 3 := by
  set v := deriv Y t₀ with hvdef
  set a := Pi (deriv (deriv Y) t₀) with hadef
  have hrange : ∀ x, Pi x ∈ range Pi := fun x => ⟨x, rfl⟩
  have hvT : v ∈ range Pi := ⟨v, hv⟩
  have haT : a ∈ range Pi := hrange _
  have hmemT : ∀ x ∈ range Pi, Pi x = x := by rintro _ ⟨y, rfl⟩; exact hPi y
  have haa : Pi a = a := hmemT a haT
  -- the retraction curve
  set ρ : ℝ → E := fun h => R (quadCurve v a h) with hρ
  have hcq : ContDiff ℝ 3 (quadCurve v a) := by
    unfold quadCurve; fun_prop
  have hρsm : ContDiff ℝ 3 ρ := hR.comp hcq
  have hqT : ∀ h, quadCurve v a h ∈ range Pi := fun h =>
    ⟨quadCurve v a h, by simp [quadCurve, map_add, map_smul, hv, haa]⟩
  have hρM : ∀ h, ρ h ∈ M := fun h => hRM _ (hqT h)
  have hq0 : quadCurve v a 0 = 0 := by simp [quadCurve]
  have hρ0 : ρ 0 = Y₀ := by simp [hρ, hq0, hR0]
  have hρ1 : deriv ρ 0 = v := by
    have := ((hR.differentiable (by norm_num)).differentiableAt.hasFDerivAt).comp_hasDerivAt
      (0 : ℝ) (hasDerivAt_quadCurve v a 0)
    simp only [hρ]
    rw [show (fun h => R (quadCurve v a h)) = R ∘ quadCurve v a from rfl, this.deriv, hq0]
    simpa using hR1 v hvT
  have hρ2 : deriv (deriv ρ) 0 = fderiv ℝ (fderiv ℝ R) 0 v v + a := by
    rw [hρ, deriv_deriv_comp_quadCurve (hR.of_le (by norm_num)), hR1 a haT]
  -- second order condition, using the same computation with `a = 0`
  have hD2 : Pi (fderiv ℝ (fderiv ℝ R) 0 v v) = 0 := by
    have := deriv_deriv_comp_quadCurve (hR.of_le (by norm_num)) v 0
    have hfun : (fun s : ℝ => R (s • v)) = fun h => R (quadCurve v 0 h) := by
      funext s; simp [quadCurve]
    have h2 := hR2 v hvT
    rw [hfun, this] at h2
    simpa using h2
  -- the exact solution, shifted
  set Z : ℝ → E := fun h => Y (t₀ + h) with hZ
  set S' : Set ℝ := (fun h => t₀ + h) ⁻¹' S with hS'
  have hS'o : IsOpen S' := hS.preimage (continuous_const.add continuous_id)
  have h0S' : (0 : ℝ) ∈ S' := by simpa [hS'] using ht₀
  have hZsm : ContDiffOn ℝ 3 Z S' :=
    hY.comp (contDiff_const.add contDiff_id).contDiffOn (fun h hh => hh)
  have hZ1 : ∀ h, deriv Z h = deriv Y (t₀ + h) := fun h => deriv_comp_const_add (f := Y) t₀ h
  have hZ1f : deriv Z = fun h => deriv Y (t₀ + h) := funext hZ1
  have hZ2 : deriv (deriv Z) 0 = deriv (deriv Y) t₀ := by
    rw [hZ1f]; simpa using deriv_comp_const_add (f := deriv Y) t₀ (0 : ℝ)
  have hZat : ContDiffAt ℝ 2 Z 0 :=
    (hZsm.contDiffAt (hS'o.mem_nhds h0S')).of_le (by norm_num)
  have hZ0 : Z 0 = Y₀ := by simp [hZ, hY0]
  have hZ1' : deriv Z 0 = v := by rw [hZ1]; simp [hvdef]
  have hZM : ∀ᶠ t in 𝓝 (0 : ℝ), Z t ∈ M :=
    Filter.mem_of_superset (hS'o.mem_nhds h0S') (fun t ht => hYM _ ht)
  have key := hII Z ρ hZat (hρsm.contDiffAt.of_le (by norm_num)) hZ0 hρ0 hZM
    (Filter.Eventually.of_forall hρM) (by rw [hZ1', hρ1])
  have hPZ : Pi (deriv (deriv Z) 0) = a := by rw [hZ2]
  have hPρ : Pi (deriv (deriv ρ) 0) = a := by
    rw [hρ2, map_add, hD2, zero_add, haa]
  have hacc : deriv (deriv Z) 0 = deriv (deriv ρ) 0 := by
    have e1 : ∀ w : E, w = Pi w + (1 - Pi) w := fun w => by simp
    rw [e1 (deriv (deriv Z) 0), e1 (deriv (deriv ρ) 0), hPZ, hPρ, key]
  -- difference
  have hdsm : ContDiffOn ℝ 3 (fun h => Z h - ρ h) S' := hZsm.sub hρsm.contDiffOn
  have hdiff : ∀ h ∈ S', DifferentiableAt ℝ Z h := fun h hh =>
    (hZsm.differentiableOn (by norm_num) h hh).differentiableAt (hS'o.mem_nhds hh)
  have hρdiff : ∀ h, DifferentiableAt ℝ ρ h := fun h =>
    (hρsm.differentiable (by norm_num)) h
  have hderiv : deriv (fun h => Z h - ρ h) =ᶠ[𝓝 0] fun h => deriv Z h - deriv ρ h := by
    filter_upwards [hS'o.mem_nhds h0S'] with h hh
    exact deriv_fun_sub (hdiff h hh) (hρdiff h)
  have hZd2 : DifferentiableAt ℝ (deriv Z) 0 := by
    have h2 : ContDiffOn ℝ 2 (deriv Z) S' :=
      ((contDiffOn_succ_iff_deriv_of_isOpen hS'o (n := 2)).1 hZsm).2.2
    exact (h2.differentiableOn (by norm_num) 0 h0S').differentiableAt (hS'o.mem_nhds h0S')
  have hρd2 : DifferentiableAt ℝ (deriv ρ) 0 := by
    have : ContDiff ℝ 2 (deriv ρ) := ((contDiff_succ_iff_deriv (n := 2)).1 hρsm).2.2
    exact (this.differentiable (by norm_num)) 0
  have d1 : deriv (fun h => Z h - ρ h) 0 = 0 := by
    rw [deriv_fun_sub (hdiff 0 h0S') (hρdiff 0), hZ1', hρ1, sub_self]
  have d2 : deriv (deriv fun h => Z h - ρ h) 0 = 0 := by
    rw [hderiv.deriv_eq, deriv_fun_sub hZd2 hρd2, hacc, sub_self]
  have hbig := isBigO_cube_of_jet_zero hS'o h0S' hdsm (by simp [hZ0, hρ0]) d1 d2
  exact hbig


/-! ### Non-vacuity: the parabola `M = {(x, x²)} ⊆ ℝ × ℝ` at `Y₀ = 0` -/

namespace Parabola

/-- The parabola `{(x, x²)}`. -/
def M : Set (ℝ × ℝ) := {p | p.2 = p.1 ^ 2}

/-- The tangent projector at the origin: projection onto the first axis. -/
noncomputable def Pi : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.inl ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ ℝ ℝ)

@[simp] theorem Pi_apply (p : ℝ × ℝ) : Pi p = (p.1, 0) := rfl

/-- A second-order retraction at the origin: `R(z) = (z₁, z₁²)`. -/
def R (z : ℝ × ℝ) : ℝ × ℝ := (z.1, z.1 ^ 2)

theorem second_deriv_snd {c1 c2 : ℝ → ℝ} (h1 : ContDiffAt ℝ 2 c1 0)
    (h0 : c1 0 = 0) (he : ∀ᶠ t in 𝓝 (0 : ℝ), c2 t = c1 t ^ 2) :
    deriv (deriv c2) 0 = 2 * (deriv c1 0) ^ 2 := by
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ContDiffAt ℝ 2 c1 t := h1.eventually (by simp)
  have hd : deriv c2 =ᶠ[𝓝 0] fun t => 2 * c1 t * deriv c1 t := by
    filter_upwards [he.eventually_nhds, hev] with t ht hc
    have hdt : DifferentiableAt ℝ c1 t := hc.differentiableAt (by norm_num)
    have e : deriv c2 t = deriv (fun x => c1 x ^ 2) t :=
      Filter.EventuallyEq.deriv_eq (show c2 =ᶠ[𝓝 t] fun x => c1 x ^ 2 from ht)
    rw [e]
    have := hdt.hasDerivAt.fun_pow 2
    simpa [mul_assoc] using this.deriv
  rw [hd.deriv_eq]
  have hc1 : DifferentiableAt ℝ c1 0 := h1.differentiableAt (by norm_num)
  have hc1' : DifferentiableAt ℝ (deriv c1) 0 :=
    (h1.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h : HasDerivAt (fun t => 2 * c1 t * deriv c1 t)
      (2 * deriv c1 0 * deriv c1 0 + 2 * c1 0 * deriv (deriv c1) 0) 0 :=
    (hc1.hasDerivAt.const_mul 2).mul hc1'.hasDerivAt
  rw [h.deriv]
  simp [h0]
  ring

theorem hasDerivAt_fst' {c : ℝ → ℝ × ℝ} {c' : ℝ × ℝ} {x : ℝ} (h : HasDerivAt c c' x) :
    HasDerivAt (fun t => (c t).1) c'.1 x :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt x h

theorem hasDerivAt_snd' {c : ℝ → ℝ × ℝ} {c' : ℝ × ℝ} {x : ℝ} (h : HasDerivAt c c' x) :
    HasDerivAt (fun t => (c t).2) c'.2 x :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt x h

theorem deriv_fst_snd {c : ℝ → ℝ × ℝ} (hc : ContDiffAt ℝ 2 c 0) :
    (deriv c 0).1 = deriv (fun t => (c t).1) 0 ∧
    (deriv (deriv c) 0).2 = deriv (deriv fun t => (c t).2) 0 := by
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ContDiffAt ℝ 2 c t := hc.eventually (by simp)
  have hdc : DifferentiableAt ℝ c 0 := hc.differentiableAt (by norm_num)
  have hdd : DifferentiableAt ℝ (deriv c) 0 :=
    (hc.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  refine ⟨(hasDerivAt_fst' hdc.hasDerivAt).deriv.symm, ?_⟩
  have e : deriv (fun t => (c t).2) =ᶠ[𝓝 0] fun t => (deriv c t).2 := by
    filter_upwards [hev] with t ht
    exact (hasDerivAt_snd' (ht.differentiableAt (by norm_num)).hasDerivAt).deriv
  rw [e.deriv_eq]
  exact (hasDerivAt_snd' hdd.hasDerivAt).deriv.symm

theorem normalAccel : NormalAccelDeterminedByVelocity M Pi 0 := by
  intro c d hc hd hc0 hd0 hcM hdM hv
  have key : ∀ c : ℝ → ℝ × ℝ, ContDiffAt ℝ 2 c 0 → c 0 = 0 → (∀ᶠ t in 𝓝 (0 : ℝ), c t ∈ M) →
      (deriv (deriv c) 0).2 = 2 * ((deriv c 0).1) ^ 2 := by
    intro c hc hc0 hcM
    rw [(deriv_fst_snd hc).2, (deriv_fst_snd hc).1]
    exact second_deriv_snd (c1 := fun t => (c t).1) (c2 := fun t => (c t).2)
      (contDiffAt_fst.comp 0 hc) (by simp [hc0]) hcM
  ext
  · simp
  · simp [key c hc hc0 hcM, key d hd hd0 hdM, hv]

theorem R_contDiff : ContDiff ℝ 3 R := by unfold R; fun_prop

theorem range_Pi (z : ℝ × ℝ) (hz : z ∈ Set.range Pi) : z.2 = 0 := by
  obtain ⟨y, rfl⟩ := hz
  simp

theorem fderiv_R_zero (z : ℝ × ℝ) : fderiv ℝ R 0 z = (z.1, 0) := by
  have h : HasFDerivAt R
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (((2 : ℝ) * (0 : ℝ × ℝ).1) •
        (ContinuousLinearMap.fst ℝ ℝ ℝ))) 0 := by
    unfold R
    refine (hasFDerivAt_fst).prodMk ?_
    simpa using (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (0 : ℝ × ℝ))).pow 2
  rw [h.fderiv]
  simp

theorem deriv_deriv_R (z : ℝ × ℝ) :
    deriv (deriv fun s : ℝ => R (s • z)) 0 = (0, 2 * z.1 ^ 2) := by
  have h1 : ∀ s : ℝ, HasDerivAt (fun s : ℝ => R (s • z)) (z.1, 2 * s * z.1 ^ 2) s := by
    intro s
    have a : HasDerivAt (fun s : ℝ => s * z.1) z.1 s := by
      simpa using (hasDerivAt_id s).mul_const z.1
    have b : HasDerivAt (fun s : ℝ => (s * z.1) ^ 2) (2 * s * z.1 ^ 2) s := by
      have := a.fun_pow 2
      convert this using 1; ring
    simpa [R] using a.prodMk b
  have h2 : deriv (fun s : ℝ => R (s • z)) = fun s => (z.1, 2 * s * z.1 ^ 2) :=
    funext fun s => (h1 s).deriv
  rw [h2]
  have : HasDerivAt (fun s : ℝ => (z.1, 2 * s * z.1 ^ 2)) (0, 2 * z.1 ^ 2) 0 := by
    refine (hasDerivAt_const _ _).prodMk ?_
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const (z.1 ^ 2)
  exact this.deriv

/-- Instance of `accelerated_euler_local_error` on the parabola with `Y(t) = (t, t²)`:
the hypotheses are satisfiable. -/
theorem instance_local_error :
    (fun h : ℝ => ((0 : ℝ) + h, ((0 : ℝ) + h) ^ 2) -
        R (quadCurve (deriv (fun t : ℝ => (t, t ^ 2)) 0)
          (Pi (deriv (deriv fun t : ℝ => (t, t ^ 2)) 0)) h))
      =O[𝓝 0] fun h : ℝ => h ^ 3 := by
  have := accelerated_euler_local_error M Pi (fun x => by simp) 0 normalAccel R R_contDiff
    (fun z _ => by simp [R, M]) (by simp [R])
    (fun z hz => by rw [fderiv_R_zero]; ext <;> simp [range_Pi z hz])
    (fun z hz => by rw [deriv_deriv_R]; ext <;> simp)
    (fun t : ℝ => (t, t ^ 2)) 0 Set.univ isOpen_univ trivial
    (by fun_prop) (fun t _ => by simp [M]) (by simp)
    (by
      have : deriv (fun t : ℝ => (t, t ^ 2)) 0 = (1, 0) := by
        have := (hasDerivAt_id (0 : ℝ)).prodMk ((hasDerivAt_id (0 : ℝ)).fun_pow 2)
        simpa using this.deriv
      rw [this]; simp)
  simpa using this

end Parabola

end LeanDLRA.Literature.P2309_06125
