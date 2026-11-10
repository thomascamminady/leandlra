import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Kinetic.LowRank

/-!
# Results of arXiv 2206.09374: Robust conservative DLRA for Vlasov

This module formalizes Einkemmer–Ostermann–Scalone, *A robust and conservative dynamical low-rank
algorithm*, for the Vlasov–Poisson system itself, in every dimension `d`.  The functions are true
functions of `x ∈ ℝ^d` (periodic on `[0, L]^d` where global laws are concerned) and `v ∈ ℝ^d`, the
weight is `f₀ᵥ = exp(-v²/2)`, the moments are Lebesgue integrals and the right-hand side is
`-v·∇ₓf + E·∇ᵥf` with Fréchet derivatives.  `Alg1Step` is one step of Algorithm 1 (K-, L- and
S-step, augmentation and conservative truncation).  `mass_continuity`, `momentum_continuity` and
`energy_balance` are Theorems 1–3, pointwise in `x`.  `force_density_mem` and `force_current_mem`,
with their projector forms, are Lemmas 1–2.  `mass_conserved`, `momentum_conserved`,
`total_energy_change`, `energy_defect_le` and `total_energy_error_le` are the global statements on
the torus, derived from the Poisson equation.  `exists_tail_rank`, `tail_truncation_error` and
`tail_rule_error_le` treat the singular-value rule of Sec. 5, whereas `field_next_eq_ftil`,
`electric_energy_error_eq_zero` and `total_energy_next_eq_ftil` show that the two energy rules
cannot see the truncation.  `alg1_hypotheses_hold` shows that all hypotheses hold together.

## Relation to the abstract core

`Stability/Conservation.lean` (`consBug_euler_local_law` and its neighbours) proves the moment
law for orthogonal projectors on an inner product space.  That theorem does not apply directly
here (the low-rank functions live in no such space of the library), so `moment_law` is proved for
the actual integrals.  The content added here is the identification of the moments of the
right-hand side (`weak_vlasov`, by integration by parts in `v`), the energy identity, and the
global laws.

## Differences from the paper

* Regularity, which the paper leaves open: velocity functions are smooth with polynomially bounded
  derivatives (`Function.HasTemperateGrowth`), which is stable under the algorithm; spatial
  functions are differentiable, and `C¹` and periodic for the global statements.  Periodicity is
  our reading of the paper's requirement `∫ ∇ₓu dx = 0`.
* The hypotheses `m ≥ 1`, `m ≥ 1 + d`, `m ≥ 2 + d` are stated as `1 ∈ span U`, `vₛ ∈ span U`,
  `v² ∈ span U`.  This is weaker: nothing else about `U` is used.
* The `(·,·)ₓᵥ` integral of the S-step is an iterated integral.
* QR factorizations are recorded by their identities, see `Alg1Step`.  Orthonormality of `Xⁿ`,
  `Xᶜᵒⁿˢ`, `Xⁿ⁺¹` is not assumed (it is not needed), and `S` may be singular.
* The paper's proofs are for `d = 1`, with a remark on general `d`; here `d` is arbitrary.
* The `∇ₓXⁿ` augmentation and `Lⁿ⁺¹` are in `Alg1Step`, but Theorems 1–3 do not use them.
  Lemmas 1–2 (the separate terms `Eρ`, `E·j` lie in `span X̃`) do use `∇ₓXⁿ`.
* `O(τ)` in Theorem 3 is proved in `L¹(Ωₓ)` (`energy_defect_le`), not pointwise, since a pointwise
  bound needs elliptic regularity.  The bound is explicit:
  `∫ |Eⁿ⁺¹ - Eⁿ|²/(2τ) ≤ (τ/2) ∫ |jⁿ|²`.
* In Sec. 5, `e_l` and `ℰ_l` are read as the energies of Algorithm 1 run with `l` singular values of
  `S̃ʳᵉᵐ`.  Under this reading the energy rules give no norm control, and rule 3 can have no
  solution.

## False claim

For `d = 3` the paper's `U₅ = (v² - 1)/‖v² - 1‖` is not orthogonal to `U₁` for the weight
`exp(-v²/2)` (`fixed_function_not_orthogonal`).  The correct function is `v² - d`
(`fixedU`, `fixedU_orth`).  No theorem is affected: Theorems 1–3 only need the span conditions.

## Not formalized

The space discretization of the paper's Sec. 4 (discrete integration by parts), and general
existence of a step for arbitrary data: `alg1_hypotheses_hold` exhibits an instance, not all of
them.
-/

open Set Filter Topology Finset MeasureTheory
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2206_09374

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-- Points of `ℝ^d` (with Lebesgue measure `volume`). -/
abbrev Pt (d : ℕ) := Fin d → ℝ

variable {d : ℕ}

/-- The partial derivative `∂g/∂y_s` of `g : ℝ^d → ℝ` at `y`. -/
noncomputable def pd (s : Fin d) (g : Pt d → ℝ) (y : Pt d) : ℝ :=
  fderiv ℝ g y (Pi.single s 1)

/-- The squared speed `v² = ∑ₛ vₛ²`. -/
def vsq (v : Pt d) : ℝ := ∑ s, v s ^ 2

/-- The weight `f₀ᵥ(v) = exp(-v²/2)` of the paper. -/
noncomputable def f0 (v : Pt d) : ℝ := Real.exp (-vsq v / 2)

lemma f0_pos (v : Pt d) : 0 < f0 v := Real.exp_pos _

lemma vsq_nonneg (v : Pt d) : 0 ≤ vsq v := Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma norm_sq_le_vsq (v : Pt d) : ‖v‖ ^ 2 ≤ vsq v := by
  have h : ‖v‖ ≤ Real.sqrt (vsq v) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun s => ?_
    rw [Real.norm_eq_abs]
    exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun s => v s ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ s))
  calc ‖v‖ ^ 2 ≤ Real.sqrt (vsq v) ^ 2 := by gcongr
    _ = vsq v := Real.sq_sqrt (vsq_nonneg v)

/-- `(1 + t)^k exp(-t²/4)` is bounded. -/
lemma one_add_pow_mul_exp_le (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (1 + t) ^ k * Real.exp (-t ^ 2 / 4) ≤ k.factorial * Real.exp 2 := by
  have h1 : (1 + t) ^ k / k.factorial ≤ Real.exp (1 + t) :=
    Real.pow_div_factorial_le_exp _ (by positivity) k
  have h2 : (1 + t) ^ k ≤ k.factorial * Real.exp (1 + t) := by
    rw [div_le_iff₀ (by positivity)] at h1
    linarith
  calc (1 + t) ^ k * Real.exp (-t ^ 2 / 4)
      ≤ (k.factorial * Real.exp (1 + t)) * Real.exp (-t ^ 2 / 4) := by gcongr
    _ = k.factorial * Real.exp (1 + t + -t ^ 2 / 4) := by rw [Real.exp_add (1 + t), mul_assoc]
    _ ≤ k.factorial * Real.exp 2 := by
        gcongr
        nlinarith [sq_nonneg (t / 2 - 1)]

lemma integrable_prod_gauss : Integrable (fun v : Pt d => ∏ s, Real.exp (-(1 / 4) * v s ^ 2)) :=
  Integrable.fintype_prod (fun _ => integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4))

lemma continuous_f0 : Continuous (f0 : Pt d → ℝ) := by unfold f0 vsq; fun_prop

/-- A temperate function is integrable against the Gaussian weight. -/
lemma integrable_f0_mul {g : Pt d → ℝ} (hg : g.HasTemperateGrowth) :
    Integrable (fun v => f0 v * g v) := by
  obtain ⟨k, C, hC⟩ := hg.2 0
  have hC' : ∀ v, |g v| ≤ C * (1 + ‖v‖) ^ k := fun v => by simpa using hC v
  have hcont : Continuous g := hg.1.continuous
  refine ((integrable_prod_gauss (d := d)).const_mul (|C| * (k.factorial * Real.exp 2))).mono'
    (continuous_f0.mul hcont).aestronglyMeasurable (Eventually.of_forall fun v => ?_)
  have hprod : ∏ s, Real.exp (-(1 / 4) * v s ^ 2) = Real.exp (-vsq v / 4) := by
    rw [← Real.exp_sum, vsq]
    congr 1
    rw [← Finset.mul_sum]
    ring
  rw [hprod, Real.norm_eq_abs, abs_mul, abs_of_pos (f0_pos v)]
  set A := Real.exp (-vsq v / 4) with hA
  set B := Real.exp (-‖v‖ ^ 2 / 4) with hB
  have h1 : f0 v = A * A := by
    rw [hA, ← Real.exp_add, f0]; congr 1; ring
  have h2 : A ≤ B := by
    rw [hA, hB]
    gcongr
    exact norm_sq_le_vsq v
  have hApos : 0 < A := Real.exp_pos _
  have h3 := one_add_pow_mul_exp_le k (norm_nonneg v)
  have h4 : |g v| ≤ |C| * (1 + ‖v‖) ^ k :=
    (hC' v).trans (by gcongr; exact le_abs_self C)
  calc f0 v * |g v| ≤ (A * B) * (|C| * (1 + ‖v‖) ^ k) := by
        rw [h1]; gcongr
    _ = |C| * A * ((1 + ‖v‖) ^ k * B) := by ring
    _ ≤ |C| * A * (k.factorial * Real.exp 2) := by gcongr
    _ = |C| * (k.factorial * Real.exp 2) * A := by ring

lemma diff_of_temperate {g : Pt d → ℝ} (hg : g.HasTemperateGrowth) : Differentiable ℝ g :=
  hg.1.differentiable (by simp)

lemma temperate_pd (s : Fin d) {g : Pt d → ℝ} (hg : g.HasTemperateGrowth) :
    (pd s g).HasTemperateGrowth := by
  have h : (fderiv ℝ g).HasTemperateGrowth := by
    refine ⟨hg.1.fderiv_right (m := (⊤ : ℕ∞)) (by simp), fun n => ?_⟩
    obtain ⟨k, C, h⟩ := hg.2 (n + 1)
    exact ⟨k, C, fun x => by simpa only [norm_iteratedFDeriv_fderiv] using h x⟩
  exact (ContinuousLinearMap.apply ℝ ℝ (Pi.single s (1 : ℝ))).hasTemperateGrowth.comp h

lemma temperate_coord (s : Fin d) : (fun v : Pt d => v s).HasTemperateGrowth :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) s).hasTemperateGrowth

lemma temperate_vsq : (vsq : Pt d → ℝ).HasTemperateGrowth := by
  unfold vsq
  exact Function.HasTemperateGrowth.sum fun s _ => (temperate_coord s).pow 2

lemma temperate_const_mul (c : ℝ) {g : Pt d → ℝ} (hg : g.HasTemperateGrowth) :
    (fun v => c * g v).HasTemperateGrowth :=
  (Function.HasTemperateGrowth.const c).mul hg

lemma temperate_mul {g h : Pt d → ℝ} (hg : g.HasTemperateGrowth) (hh : h.HasTemperateGrowth) :
    (fun v => g v * h v).HasTemperateGrowth :=
  hg.mul hh

lemma temperate_add {g h : Pt d → ℝ} (hg : g.HasTemperateGrowth) (hh : h.HasTemperateGrowth) :
    (fun v => g v + h v).HasTemperateGrowth :=
  hg.add hh

lemma temperate_sum {ι : Type*} [Fintype ι] {g : ι → Pt d → ℝ}
    (hg : ∀ i, (g i).HasTemperateGrowth) : (fun v => ∑ i, g i v).HasTemperateGrowth :=
  Function.HasTemperateGrowth.sum fun i _ => hg i

lemma pd_const_mul (s : Fin d) (c : ℝ) {g : Pt d → ℝ} {y : Pt d} (hg : DifferentiableAt ℝ g y) :
    pd s (fun y => c * g y) y = c * pd s g y := by
  simp [pd, fderiv_const_mul hg]

lemma pd_mul (s : Fin d) {a b : Pt d → ℝ} {y : Pt d} (ha : DifferentiableAt ℝ a y)
    (hb : DifferentiableAt ℝ b y) :
    pd s (fun y => a y * b y) y = a y * pd s b y + b y * pd s a y := by
  simp [pd, fderiv_fun_mul ha hb]

lemma pd_sum {ι : Type*} [Fintype ι] (s : Fin d) {g : ι → Pt d → ℝ} {y : Pt d}
    (hg : ∀ i, DifferentiableAt ℝ (g i) y) :
    pd s (fun y => ∑ i, g i y) y = ∑ i, pd s (g i) y := by
  simp [pd, fderiv_fun_sum (fun i _ => hg i)]

lemma pd_add (s : Fin d) {a b : Pt d → ℝ} {y : Pt d} (ha : DifferentiableAt ℝ a y)
    (hb : DifferentiableAt ℝ b y) :
    pd s (fun y => a y + b y) y = pd s a y + pd s b y := by
  simp [pd, fderiv_fun_add ha hb]

lemma pd_sub (s : Fin d) {a b : Pt d → ℝ} {y : Pt d} (ha : DifferentiableAt ℝ a y)
    (hb : DifferentiableAt ℝ b y) :
    pd s (fun y => a y - b y) y = pd s a y - pd s b y := by
  simp [pd, fderiv_fun_sub ha hb]

lemma pd_const (s : Fin d) (c : ℝ) (y : Pt d) : pd s (fun _ => c) y = 0 := by
  simp [pd]

lemma pd_coord (r s : Fin d) (y : Pt d) :
    pd r (fun v : Pt d => v s) y = if r = s then 1 else 0 := by
  have : fderiv ℝ (fun v : Pt d => v s) y =
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) s :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) s).fderiv
  simp [pd, this, Pi.single_apply, eq_comm]

lemma differentiable_coord (s : Fin d) : Differentiable ℝ (fun v : Pt d => v s) := by fun_prop

lemma pd_vsq (r : Fin d) (y : Pt d) : pd r vsq y = 2 * y r := by
  have hd : ∀ s, DifferentiableAt ℝ (fun v : Pt d => v s ^ 2) y := fun s => by fun_prop
  have h1 : ∀ s, pd r (fun v : Pt d => v s ^ 2) y = 2 * y s * (if r = s then 1 else 0) := by
    intro s
    have : (fun v : Pt d => v s ^ 2) = fun v => v s * v s := by funext v; ring
    rw [this, pd_mul r (by fun_prop) (by fun_prop), pd_coord]
    ring
  change pd r (fun v => ∑ s, v s ^ 2) y = _
  rw [pd_sum r hd, Finset.sum_congr rfl fun s _ => h1 s]
  simp

lemma differentiable_f0 : Differentiable ℝ (f0 : Pt d → ℝ) := by
  unfold f0 vsq; fun_prop

lemma pd_f0 (s : Fin d) (v : Pt d) : pd s f0 v = -(v s * f0 v) := by
  have hv : DifferentiableAt ℝ (vsq : Pt d → ℝ) v := (diff_of_temperate temperate_vsq) v
  have hv' : DifferentiableAt ℝ (fun w : Pt d => -vsq w / 2) v := by
    unfold vsq; fun_prop
  have h : HasFDerivAt (fun w : Pt d => Real.exp (-vsq w / 2))
      (Real.exp (-vsq v / 2) • (fderiv ℝ (fun w : Pt d => -vsq w / 2) v)) v :=
    hv'.hasFDerivAt.exp
  have h2 : fderiv ℝ (fun w : Pt d => -vsq w / 2) v (Pi.single s 1) = -(v s) := by
    have := pd_const_mul s (-(1 / 2)) hv
    have e : (fun w : Pt d => -vsq w / 2) = fun w => -(1 / 2) * vsq w := by funext w; ring
    rw [e]
    change pd s (fun w => -(1 / 2) * vsq w) v = _
    rw [this, pd_vsq]; ring
  change fderiv ℝ (fun w : Pt d => Real.exp (-vsq w / 2)) v (Pi.single s 1) = _
  rw [h.fderiv]
  rw [smul_apply, smul_eq_mul, h2]
  rw [f0]; ring


lemma pd_mul_const (s : Fin d) (c : ℝ) {g : Pt d → ℝ} {y : Pt d} (hg : DifferentiableAt ℝ g y) :
    pd s (fun y => g y * c) y = pd s g y * c := by
  unfold pd
  rw [fderiv_mul_const hg]
  simp [mul_comm]

/-! ### The weighted velocity inner product and integration by parts -/

/-- The weighted velocity inner product `⟨g, h⟩ᵥ = ∫ f₀ᵥ g h dv`. -/
noncomputable def ipv (g h : Pt d → ℝ) : ℝ := ∫ v, f0 v * g v * h v

lemma integrable_ipv {g h : Pt d → ℝ} (hg : g.HasTemperateGrowth) (hh : h.HasTemperateGrowth) :
    Integrable (fun v => f0 v * g v * h v) := by
  simpa [mul_assoc] using integrable_f0_mul (hg.mul hh)

lemma ipv_comm (g h : Pt d → ℝ) : ipv g h = ipv h g := by
  unfold ipv; congr 1; funext v; ring

lemma ipv_const_mul (c : ℝ) (g h : Pt d → ℝ) : ipv g (fun v => c * h v) = c * ipv g h := by
  unfold ipv
  rw [← integral_const_mul]
  congr 1; funext v; ring

lemma ipv_sum {ι : Type*} [Fintype ι] {g : Pt d → ℝ} {h : ι → Pt d → ℝ}
    (hg : g.HasTemperateGrowth) (hh : ∀ i, (h i).HasTemperateGrowth) :
    ipv g (fun v => ∑ i, h i v) = ∑ i, ipv g (h i) := by
  unfold ipv
  rw [← integral_finsetSum _ fun i _ => integrable_ipv hg (hh i)]
  congr 1; funext v; rw [Finset.mul_sum]

lemma ipv_add {g a b : Pt d → ℝ} (hg : g.HasTemperateGrowth) (ha : a.HasTemperateGrowth)
    (hb : b.HasTemperateGrowth) : ipv g (fun v => a v + b v) = ipv g a + ipv g b := by
  unfold ipv
  rw [← integral_add (integrable_ipv hg ha) (integrable_ipv hg hb)]
  congr 1; funext v; ring

/-- The operator `g ↦ f₀ᵥ⁻¹ ∂ₛ(f₀ᵥ g) = ∂ₛ g - vₛ g`. -/
noncomputable def Aop (s : Fin d) (g : Pt d → ℝ) (v : Pt d) : ℝ := pd s g v - v s * g v

lemma temperate_Aop (s : Fin d) {g : Pt d → ℝ} (hg : g.HasTemperateGrowth) :
    (Aop s g).HasTemperateGrowth :=
  (temperate_pd s hg).sub ((temperate_coord s).mul hg)

lemma pd_f0_mul (s : Fin d) {g : Pt d → ℝ} {v : Pt d} (hg : DifferentiableAt ℝ g v) :
    pd s (fun w => f0 w * g w) v = f0 v * Aop s g v := by
  rw [pd_mul s (differentiable_f0 v) hg, pd_f0, Aop]; ring

/-- **Integration by parts in `v`**: `∫ u ∂ₛ(f₀ᵥ g) dv = -∫ (∂ₛ u) f₀ᵥ g dv`, for temperate `u, g`.
Here `f₀ᵥ Aop s g = ∂ₛ(f₀ᵥ g)`. -/
lemma ipv_Aop (s : Fin d) {u g : Pt d → ℝ} (hu : u.HasTemperateGrowth)
    (hg : g.HasTemperateGrowth) : ipv u (Aop s g) = -ipv (pd s u) g := by
  have hdg := diff_of_temperate hg
  have hdu := diff_of_temperate hu
  have hd : Differentiable ℝ (fun w => f0 w * g w) := differentiable_f0.mul hdg
  have e1 : ∀ x, fderiv ℝ (fun w => f0 w * g w) x (Pi.single s 1) = f0 x * Aop s g x :=
    fun x => pd_f0_mul s (hdg x)
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Pt d)))
    (f := u) (g := fun w => f0 w * g w) (v := Pi.single s (1 : ℝ))
    (by
      have := integrable_ipv (temperate_pd s hu) hg
      refine this.congr (Eventually.of_forall fun x => ?_)
      change f0 x * pd s u x * g x = pd s u x * (f0 x * g x)
      ring)
    (by
      have := integrable_ipv hu (temperate_Aop s hg)
      refine this.congr (Eventually.of_forall fun x => ?_)
      change f0 x * u x * Aop s g x = u x * fderiv ℝ (fun w => f0 w * g w) x (Pi.single s 1)
      rw [e1]; ring)
    (by
      have := integrable_ipv hu hg
      refine this.congr (Eventually.of_forall fun x => ?_)
      change f0 x * u x * g x = u x * (f0 x * g x)
      ring)
    (fun x _ => hdu x) (fun x _ => hd x)
  have h1 : ipv u (Aop s g) = ∫ x, u x * fderiv ℝ (fun w => f0 w * g w) x (Pi.single s 1) := by
    unfold ipv; congr 1; funext x; rw [e1]; ring
  have h2 : ipv (pd s u) g = ∫ x, fderiv ℝ u x (Pi.single s 1) * (f0 x * g x) := by
    unfold ipv; congr 1; funext x
    change f0 x * pd s u x * g x = pd s u x * (f0 x * g x)
    ring
  rw [h1, key, h2]

/-! ### Low-rank functions, moments and the Vlasov right-hand side -/

section LowRank

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The `K` factor `K_k = ∑ᵢ Xᵢ S_{ik}`. -/
noncomputable def coefK (X : ι → Pt d → ℝ) (S : Matrix ι κ ℝ) (k : κ) (x : Pt d) : ℝ :=
  ∑ i, X i x * S i k

/-- The low-rank function `f(x, v) = f₀ᵥ(v) ∑ᵢⱼ Xᵢ(x) S_{ij} Vⱼ(v)`. -/
noncomputable def lowRank (X : ι → Pt d → ℝ) (S : Matrix ι κ ℝ) (V : κ → Pt d → ℝ)
    (x v : Pt d) : ℝ :=
  f0 v * ∑ i, ∑ j, X i x * S i j * V j v

/-- The right-hand side `-v·∇ₓf + E·∇ᵥf` of the Vlasov equation `∂ₜf + v·∇ₓf - E·∇ᵥf = 0`. -/
noncomputable def vlasovRHS (f : Pt d → Pt d → ℝ) (E : Fin d → Pt d → ℝ) (x v : Pt d) : ℝ :=
  -∑ s, v s * pd s (fun y => f y v) x + ∑ s, E s x * pd s (fun w => f x w) v

/-- The velocity moment `∫ u(v) f(x, v) dv`. -/
noncomputable def mom (u : Pt d → ℝ) (f : Pt d → Pt d → ℝ) (x : Pt d) : ℝ := ∫ v, u v * f x v

variable {X : ι → Pt d → ℝ} {S : Matrix ι κ ℝ} {V : κ → Pt d → ℝ}

lemma lowRank_eq (X : ι → Pt d → ℝ) (S : Matrix ι κ ℝ) (V : κ → Pt d → ℝ) (x v : Pt d) :
    lowRank X S V x v = f0 v * ∑ j, coefK X S j x * V j v := by
  simp only [lowRank, coefK, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma pd_x_lowRank (s : Fin d) {x : Pt d} (hK : ∀ j, DifferentiableAt ℝ (coefK X S j) x)
    (v : Pt d) :
    pd s (fun y => lowRank X S V y v) x = f0 v * ∑ j, pd s (coefK X S j) x * V j v := by
  have e : (fun y => lowRank X S V y v) = fun y => f0 v * ∑ j, coefK X S j y * V j v := by
    funext y; exact lowRank_eq X S V y v
  have hm : ∀ j, DifferentiableAt ℝ (fun y => coefK X S j y * V j v) x :=
    fun j => (hK j).mul_const _
  have hs : DifferentiableAt ℝ (fun y => ∑ j, coefK X S j y * V j v) x := by
    simpa using DifferentiableAt.fun_sum (u := Finset.univ) fun j _ => hm j
  rw [e, pd_const_mul s _ hs, pd_sum s hm]
  congr 1
  exact Finset.sum_congr rfl fun j _ => pd_mul_const s _ (hK j)

lemma pd_v_lowRank (s : Fin d) (hV : ∀ j, Differentiable ℝ (V j)) (x v : Pt d) :
    pd s (fun w => lowRank X S V x w) v = ∑ j, coefK X S j x * (f0 v * Aop s (V j) v) := by
  have e : (fun w => lowRank X S V x w) = fun w => ∑ j, coefK X S j x * (f0 w * V j w) := by
    funext w
    rw [lowRank_eq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hd : ∀ j, DifferentiableAt ℝ (fun w => f0 w * V j w) v :=
    fun j => differentiable_f0 v |>.mul (hV j v)
  rw [e, pd_sum s fun j => (hd j).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pd_const_mul s _ (hd j), pd_f0_mul s (hV j v)]

/-- The Vlasov right-hand side of a low-rank function, divided by `f₀ᵥ`. -/
noncomputable def rhsCore (X : ι → Pt d → ℝ) (S : Matrix ι κ ℝ) (V : κ → Pt d → ℝ)
    (E : Fin d → Pt d → ℝ) (x v : Pt d) : ℝ :=
  ∑ s, (∑ j, -pd s (coefK X S j) x * (v s * V j v) + ∑ j, (E s x * coefK X S j x) * Aop s (V j) v)

lemma vlasovRHS_lowRank (hV : ∀ j, Differentiable ℝ (V j)) {x : Pt d}
    (hK : ∀ j, DifferentiableAt ℝ (coefK X S j) x) (E : Fin d → Pt d → ℝ) (v : Pt d) :
    vlasovRHS (lowRank X S V) E x v = f0 v * rhsCore X S V E x v := by
  unfold vlasovRHS rhsCore
  simp only [pd_x_lowRank _ hK, pd_v_lowRank _ hV]
  conv_rhs => rw [Finset.mul_sum]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  have h1 : ∑ j, -pd s (coefK X S j) x * (v s * V j v) =
      -(v s * ∑ j, pd s (coefK X S j) x * V j v) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∑ j, (E s x * coefK X S j x) * Aop s (V j) v =
      E s x * ∑ j, coefK X S j x * Aop s (V j) v := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h3 : ∑ j, coefK X S j x * (f0 v * Aop s (V j) v) =
      f0 v * ∑ j, coefK X S j x * Aop s (V j) v := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h1, h2, h3]
  ring

lemma temperate_rhsCore (hV : ∀ j, (V j).HasTemperateGrowth) (E : Fin d → Pt d → ℝ) (x : Pt d) :
    (rhsCore X S V E x).HasTemperateGrowth := by
  unfold rhsCore
  refine temperate_sum fun s =>
    temperate_add (temperate_sum fun j => ?_) (temperate_sum fun j => ?_)
  · exact temperate_const_mul _ (temperate_mul (temperate_coord s) (hV j))
  · exact temperate_const_mul _ (temperate_Aop s (hV j))

lemma temperate_comb (hV : ∀ j, (V j).HasTemperateGrowth) (c : κ → ℝ) :
    (fun v => ∑ j, c j * V j v).HasTemperateGrowth :=
  temperate_sum fun j => temperate_const_mul _ (hV j)

lemma temperate_comb' {Iu : Type*} [Fintype Iu] {Uu : Iu → Pt d → ℝ}
    (hU : ∀ a, (Uu a).HasTemperateGrowth) (c : Iu → ℝ) :
    (fun v => ∑ a, c a * Uu a v).HasTemperateGrowth :=
  temperate_sum fun a => temperate_const_mul _ (hU a)

lemma mom_lowRank {u : Pt d → ℝ} (hu : u.HasTemperateGrowth) (hV : ∀ j, (V j).HasTemperateGrowth)
    (x : Pt d) : mom u (lowRank X S V) x = ∑ j, coefK X S j x * ipv u (V j) := by
  have e : mom u (lowRank X S V) x = ipv u (fun v => ∑ j, coefK X S j x * V j v) := by
    unfold mom ipv
    congr 1; funext v; rw [lowRank_eq]; ring
  rw [e, ipv_sum hu fun j => temperate_const_mul _ (hV j)]
  exact Finset.sum_congr rfl fun j _ => ipv_const_mul _ _ _

lemma pd_mom (s : Fin d) {u : Pt d → ℝ} (hu : u.HasTemperateGrowth)
    (hV : ∀ j, (V j).HasTemperateGrowth) {x : Pt d}
    (hK : ∀ j, DifferentiableAt ℝ (coefK X S j) x) :
    pd s (mom u (lowRank X S V)) x = ∑ j, pd s (coefK X S j) x * ipv u (V j) := by
  have e : mom u (lowRank X S V) = fun y => ∑ j, coefK X S j y * ipv u (V j) := by
    funext y; exact mom_lowRank hu hV y
  rw [e, pd_sum s fun j => (hK j).mul_const _]
  exact Finset.sum_congr rfl fun j _ => pd_mul_const s _ (hK j)

/-- **Weak form of the Vlasov right-hand side** (arXiv 2206.09374, the integrations by parts in the
proofs of Theorems 1–3): for a low-rank `f` and a temperate test function `u`,
`∫ u (-v·∇ₓf + E·∇ᵥf) dv = -∇ₓ·∫ v u f dv - E·∫ (∇ᵥu) f dv`. -/
theorem weak_vlasov {u : Pt d → ℝ} (hu : u.HasTemperateGrowth)
    (hV : ∀ j, (V j).HasTemperateGrowth) {x : Pt d}
    (hK : ∀ j, DifferentiableAt ℝ (coefK X S j) x) (E : Fin d → Pt d → ℝ) :
    ∫ v, u v * vlasovRHS (lowRank X S V) E x v =
      -∑ s, pd s (mom (fun v => v s * u v) (lowRank X S V)) x -
        ∑ s, E s x * mom (pd s u) (lowRank X S V) x := by
  have hVd : ∀ j, Differentiable ℝ (V j) := fun j => diff_of_temperate (hV j)
  have e : ∫ v, u v * vlasovRHS (lowRank X S V) E x v = ipv u (rhsCore X S V E x) := by
    unfold ipv
    congr 1; funext v
    rw [vlasovRHS_lowRank hVd hK]; ring
  have hc : ∀ s, (fun v => v s * u v).HasTemperateGrowth :=
    fun s => temperate_mul (temperate_coord s) hu
  have e1 : ∀ s (j : κ), ipv u (fun v => v s * V j v) = ipv (fun v => v s * u v) (V j) := by
    intro s j
    unfold ipv; congr 1; funext v; ring
  have ht1 : ∀ s (j : κ), (fun v => -pd s (coefK X S j) x * (v s * V j v)).HasTemperateGrowth :=
    fun s j => temperate_const_mul _ (temperate_mul (temperate_coord s) (hV j))
  have ht2 : ∀ s (j : κ), (fun v => (E s x * coefK X S j x) * Aop s (V j) v).HasTemperateGrowth :=
    fun s j => temperate_const_mul _ (temperate_Aop s (hV j))
  simp only [pd_mom _ (hc _) hV hK, mom_lowRank (temperate_pd _ hu) hV]
  rw [e]
  unfold rhsCore
  rw [ipv_sum hu fun s => temperate_add (temperate_sum (ht1 s)) (temperate_sum (ht2 s)),
    ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [ipv_add hu (temperate_sum (ht1 s)) (temperate_sum (ht2 s)),
    ipv_sum hu (ht1 s), ipv_sum hu (ht2 s), sub_eq_add_neg, Finset.mul_sum,
    ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [ipv_const_mul, e1]; ring
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [ipv_const_mul, ipv_Aop s hu (hV j)]
    ring

lemma ipv_comb_left {Iu : Type*} [Fintype Iu] {Uu : Iu → Pt d → ℝ}
    (hU : ∀ a, (Uu a).HasTemperateGrowth) (c : Iu → ℝ) {g : Pt d → ℝ}
    (hg : g.HasTemperateGrowth) :
    ipv (fun v => ∑ a, c a * Uu a v) g = ∑ a, c a * ipv (Uu a) g := by
  rw [ipv_comm, ipv_sum hg fun a => temperate_const_mul _ (hU a)]
  exact Finset.sum_congr rfl fun a _ => by rw [ipv_const_mul, ipv_comm]

lemma mom_comb {Iu : Type*} [Fintype Iu] {Uu : Iu → Pt d → ℝ}
    (hU : ∀ a, (Uu a).HasTemperateGrowth) (c : Iu → ℝ) (hV : ∀ j, (V j).HasTemperateGrowth)
    (x : Pt d) :
    mom (fun v => ∑ a, c a * Uu a v) (lowRank X S V) x =
      ∑ a, c a * mom (Uu a) (lowRank X S V) x := by
  rw [mom_lowRank (temperate_comb' hU c) hV]
  simp only [mom_lowRank (hU _) hV, ipv_comb_left hU c (hV _), Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => by ring

lemma rhs_comb {Iu : Type*} [Fintype Iu] {Uu : Iu → Pt d → ℝ}
    (hU : ∀ a, (Uu a).HasTemperateGrowth) (c : Iu → ℝ) (hV : ∀ j, (V j).HasTemperateGrowth)
    {x : Pt d} (hK : ∀ j, DifferentiableAt ℝ (coefK X S j) x) (E : Fin d → Pt d → ℝ) :
    ∫ v, (∑ a, c a * Uu a v) * vlasovRHS (lowRank X S V) E x v =
      ∑ a, c a * ∫ v, Uu a v * vlasovRHS (lowRank X S V) E x v := by
  have hVd : ∀ j, Differentiable ℝ (V j) := fun j => diff_of_temperate (hV j)
  have e : ∀ {u : Pt d → ℝ}, ∫ v, u v * vlasovRHS (lowRank X S V) E x v =
      ipv u (rhsCore X S V E x) := by
    intro u
    unfold ipv
    congr 1; funext v
    rw [vlasovRHS_lowRank hVd hK]; ring
  rw [e, ipv_comb_left hU c (temperate_rhsCore hV E x)]
  simp only [e]

lemma differentiable_mom {u : Pt d → ℝ} (hu : u.HasTemperateGrowth)
    (hV : ∀ j, (V j).HasTemperateGrowth) (hK : ∀ j, Differentiable ℝ (coefK X S j)) :
    Differentiable ℝ (mom u (lowRank X S V)) := by
  have e : mom u (lowRank X S V) = fun y => ∑ j, coefK X S j y * ipv u (V j) := by
    funext y; exact mom_lowRank hu hV y
  rw [e]
  intro y
  simpa using DifferentiableAt.fun_sum (u := Finset.univ)
    fun j _ => (hK j y).mul_const (ipv u (V j))

end LowRank

/-! ### Physical moments -/

/-- The density `ρ = ∫ f dv`. -/
noncomputable def density (f : Pt d → Pt d → ℝ) (x : Pt d) : ℝ := ∫ v, f x v

/-- The current `jₛ = ∫ vₛ f dv`. -/
noncomputable def current (f : Pt d → Pt d → ℝ) (s : Fin d) (x : Pt d) : ℝ := ∫ v, v s * f x v

/-- The stress tensor `σᵣₛ = ∫ vᵣ vₛ f dv`. -/
noncomputable def stress (f : Pt d → Pt d → ℝ) (r s : Fin d) (x : Pt d) : ℝ :=
  ∫ v, v r * v s * f x v

/-- The heat flux `Qₛ = ½ ∫ vₛ v² f dv`. -/
noncomputable def heatFlux (f : Pt d → Pt d → ℝ) (s : Fin d) (x : Pt d) : ℝ :=
  (1 / 2) * ∫ v, v s * vsq v * f x v

/-- The energy density `e = ½ ∫ v² f dv + ½ E²`. -/
noncomputable def energyDensity (f : Pt d → Pt d → ℝ) (E : Fin d → Pt d → ℝ) (x : Pt d) : ℝ :=
  (1 / 2) * (∫ v, vsq v * f x v) + (1 / 2) * ∑ s, E s x ^ 2

/-! ### The spatial inner product -/

/-- The periodicity box `Ωₓ = [0, L]^d`. -/
def box (L : ℝ) : Set (Pt d) := Icc 0 (fun _ => L)

/-- The spatial inner product `⟨a, b⟩ₓ = ∫_{[0,L]^d} a b dx`. -/
noncomputable def ipx (L : ℝ) (a b : Pt d → ℝ) : ℝ := ∫ x in box L, a x * b x

lemma integrableOn_box {g : Pt d → ℝ} (hg : Continuous g) (L : ℝ) : IntegrableOn g (box L) :=
  hg.integrableOn_Icc

lemma ipx_comb {ι : Type*} [Fintype ι] {L : ℝ} {a : Pt d → ℝ} {b : ι → Pt d → ℝ}
    (ha : Continuous a) (hb : ∀ i, Continuous (b i)) (c : ι → ℝ) :
    ipx L a (fun x => ∑ i, c i * b i x) = ∑ i, c i * ipx L a (b i) := by
  unfold ipx
  simp only [← integral_const_mul]
  have hi : ∀ i, IntegrableOn (fun x => c i * (a x * b i x)) (box L) := fun i =>
    (integrableOn_box (ha.mul (hb i)) L).const_mul _
  rw [← integral_finsetSum _ fun i _ => hi i]
  congr 1; funext x
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Expansion in a spatial orthonormal system: the projector `P_x` fixes its span. -/
lemma expand_orth {Ix : Type*} [Fintype Ix] [DecidableEq Ix] {L : ℝ} {Xt : Ix → Pt d → ℝ}
    (hc : ∀ a, Continuous (Xt a)) (ho : ∀ a b, ipx L (Xt a) (Xt b) = if a = b then 1 else 0)
    {g : Pt d → ℝ} (hg : g ∈ Submodule.span ℝ (range Xt)) (x : Pt d) :
    ∑ k, Xt k x * ipx L (Xt k) g = g x := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hg
  have e : ∀ k, ipx L (Xt k) (∑ i, c i • Xt i) = c k := by
    intro k
    have : (∑ i, c i • Xt i) = fun x => ∑ i, c i * Xt i x := by
      funext y; simp
    rw [this, ipx_comb (hc k) hc]
    simp [ho]
  simp only [e]
  simp [mul_comm]

/-- Expansion in a velocity orthonormal system: the projector `P_v` fixes its span. -/
lemma expand_orth_v {Iv : Type*} [Fintype Iv] [DecidableEq Iv] {Vt : Iv → Pt d → ℝ}
    (hc : ∀ a, (Vt a).HasTemperateGrowth)
    (ho : ∀ a b, ipv (Vt a) (Vt b) = if a = b then 1 else 0)
    {g : Pt d → ℝ} (hg : g ∈ Submodule.span ℝ (range Vt)) (v : Pt d) :
    ∑ l, ipv g (Vt l) * Vt l v = g v := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hg
  have e : ∀ k, ipv (∑ i, c i • Vt i) (Vt k) = c k := by
    intro k
    have : (∑ i, c i • Vt i) = fun x => ∑ i, c i * Vt i x := by
      funext y; simp
    rw [ipv_comm, this, ipv_sum (hc k) fun i => temperate_const_mul _ (hc i)]
    simp [ipv_const_mul, ho]
  simp only [e]
  simp

/-! ### Periodic functions and integration by parts in `x` -/

/-- `g` is `L`-periodic in every coordinate. -/
def Per (L : ℝ) (g : Pt d → ℝ) : Prop := ∀ (s : Fin d) (x : Pt d), g (x + Pi.single s L) = g x

lemma continuous_pd {g : Pt d → ℝ} (hg : ContDiff ℝ 1 g) (s : Fin d) : Continuous (pd s g) :=
  (hg.continuous_fderiv (by simp)).clm_apply continuous_const

lemma integral_pd_eq_zero {L : ℝ} (hL : 0 ≤ L) {g : Pt d → ℝ} (hg : ContDiff ℝ 1 g)
    (hp : Per L g) (s : Fin d) : ∫ x in box L, pd s g x = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by have := s.pos; omega⟩
  have hd : Differentiable ℝ g := hg.differentiable (by simp)
  have hle : (0 : Pt (n + 1)) ≤ fun _ => L := fun _ => hL
  have e1 : ∀ x, ∑ i, (if i = s then fderiv ℝ g x else 0) (Pi.single i (1 : ℝ)) = pd s g x := by
    intro x
    rw [Finset.sum_eq_single s (fun i _ hi => by simp [hi]) (by simp)]
    simp [pd]
  have key := integral_divergence_of_hasFDerivAt_off_countable' (0 : Pt (n + 1)) (fun _ => L) hle
    (fun i x => if i = s then g x else 0)
    (fun i x => if i = s then fderiv ℝ g x else 0) ∅ countable_empty
    (fun i => by
      by_cases hi : i = s
      · simpa [hi] using hg.continuous.continuousOn
      · simpa [hi] using continuousOn_const)
    (fun x _ i => by
      by_cases hi : i = s
      · simpa [hi] using (hd x).hasFDerivAt
      · simpa [hi] using hasFDerivAt_const (0 : ℝ) x)
    (by
      simp only [e1]
      exact (continuous_pd hg s).integrableOn_Icc)
  simp only [e1] at key
  change ∫ x in Icc 0 (fun _ => L), pd s g x = 0
  rw [key]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i = s
  · subst hi
    simp only [ite_true]
    rw [sub_eq_zero]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have e : (i.insertNth L y : Pt (n + 1)) = i.insertNth (0 : ℝ) y + Pi.single i L := by
      ext j
      rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
      · simp
      · simp [Fin.succAbove_ne i k]
    change g (i.insertNth L y) = g (i.insertNth (0 : ℝ) y)
    rw [e, hp i]
  · simp [hi]

/-- `C¹` and `L`-periodic in every coordinate: the spatial functions on the torus. -/
structure CP (L : ℝ) (g : Pt d → ℝ) : Prop where
  smooth : ContDiff ℝ 1 g
  per : Per L g

namespace CP

variable {L : ℝ} {a b : Pt d → ℝ}

lemma differentiable (ha : CP L a) : Differentiable ℝ a := ha.1.differentiable (by simp)

lemma continuous (ha : CP L a) : Continuous a := ha.1.continuous

lemma add (ha : CP L a) (hb : CP L b) : CP L (fun x => a x + b x) :=
  ⟨ha.1.add hb.1, fun s x => by simp only [ha.2 s x, hb.2 s x]⟩

lemma sub (ha : CP L a) (hb : CP L b) : CP L (fun x => a x - b x) :=
  ⟨ha.1.sub hb.1, fun s x => by simp only [ha.2 s x, hb.2 s x]⟩

lemma mul (ha : CP L a) (hb : CP L b) : CP L (fun x => a x * b x) :=
  ⟨ha.1.mul hb.1, fun s x => by simp only [ha.2 s x, hb.2 s x]⟩

lemma const (L c : ℝ) : CP (d := d) L (fun _ => c) := ⟨contDiff_const, fun _ _ => rfl⟩

lemma const_mul (c : ℝ) (ha : CP L a) : CP L (fun x => c * a x) := (const L c).mul ha

lemma mul_const (c : ℝ) (ha : CP L a) : CP L (fun x => a x * c) := ha.mul (const L c)

lemma sum {ι : Type*} [Fintype ι] {g : ι → Pt d → ℝ} (hg : ∀ i, CP L (g i)) :
    CP L (fun x => ∑ i, g i x) :=
  ⟨ContDiff.sum fun i _ => (hg i).1, fun s x => by simp only [(hg _).2 s x]⟩

lemma neg (ha : CP L a) : CP L (fun x => -a x) :=
  ⟨ha.1.neg, fun s x => by simp only [ha.2 s x]⟩

end CP

lemma Per.pd {L : ℝ} {g : Pt d → ℝ} (hg : Per L g) (r : Fin d) : Per L (pd r g) := by
  intro s x
  have e : (fun y => g (y + Pi.single s L)) = g := funext (hg s)
  have := fderiv_comp_add_right (𝕜 := ℝ) (f := g) (x := x) (Pi.single s L)
  rw [e] at this
  simp only [P2206_09374.pd]
  rw [← this]

/-- **Integration by parts on the torus.** -/
lemma integral_mul_pd {L : ℝ} (hL : 0 ≤ L) {a b : Pt d → ℝ} (ha : CP L a) (hb : CP L b)
    (s : Fin d) : ∫ x in box L, a x * pd s b x = -∫ x in box L, pd s a x * b x := by
  have h0 := integral_pd_eq_zero hL (ha.mul hb).1 (ha.mul hb).2 s
  have e : ∀ x, pd s (fun y => a y * b y) x = a x * pd s b x + pd s a x * b x := fun x => by
    rw [pd_mul s (ha.differentiable x) (hb.differentiable x)]; ring
  simp only [e] at h0
  have i1 : IntegrableOn (fun x => a x * pd s b x) (box L) :=
    integrableOn_box (ha.continuous.mul (continuous_pd hb.1 s)) L
  have i2 : IntegrableOn (fun x => pd s a x * b x) (box L) :=
    integrableOn_box ((continuous_pd ha.1 s).mul hb.continuous) L
  rw [integral_add i1 i2] at h0
  linarith

lemma sum4 {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (t : A → B → C → D → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, t a b c e = ∑ c, ∑ e, ∑ a, ∑ b, t a b c e := by
  calc ∑ a, ∑ b, ∑ c, ∑ e, t a b c e
      = ∑ a, ∑ c, ∑ b, ∑ e, t a b c e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ e, t a b c e := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ e, ∑ b, t a b c e :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ e, ∑ a, ∑ b, t a b c e :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm

/-- Parseval for a spatial orthonormal system. -/
lemma integral_comb_sq {Ix : Type*} [Fintype Ix] [DecidableEq Ix] {L : ℝ} {X : Ix → Pt d → ℝ}
    (hc : ∀ a, Continuous (X a)) (ho : ∀ a b, ipx L (X a) (X b) = if a = b then 1 else 0)
    (a : Ix → ℝ) : ∫ x in box L, (∑ c, X c x * a c) ^ 2 = ∑ c, a c ^ 2 := by
  have hg : (fun x => ∑ c, X c x * a c) = fun x => ∑ c, a c * X c x := by
    funext x; exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  have hgc : Continuous fun x => ∑ c, a c * X c x :=
    continuous_finsetSum _ fun c _ => continuous_const.mul (hc c)
  have e1 : ∀ c, ipx L (X c) (fun x => ∑ c, a c * X c x) = a c := by
    intro c
    rw [ipx_comb (hc c) hc]
    simp [ho]
  have e2 : ipx L (fun x => ∑ c, a c * X c x) (fun x => ∑ c, a c * X c x) = ∑ c, a c ^ 2 := by
    rw [ipx_comb hgc hc]
    refine Finset.sum_congr rfl fun c _ => ?_
    have : ipx L (fun x => ∑ c, a c * X c x) (X c) = a c := by
      rw [← e1 c]
      unfold ipx
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      exact mul_comm _ _
    rw [this]; ring
  rw [← e2]
  unfold ipx
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  change (∑ c, X c x * a c) ^ 2 = (∑ c, a c * X c x) * ∑ c, a c * X c x
  rw [show ∑ c, X c x * a c = ∑ c, a c * X c x from congrFun hg x, sq]

/-- Parseval for a velocity orthonormal system. -/
lemma ipv_comb_self {Iv : Type*} [Fintype Iv] [DecidableEq Iv] {W : Iv → Pt d → ℝ}
    (hc : ∀ a, (W a).HasTemperateGrowth) (ho : ∀ a b, ipv (W a) (W b) = if a = b then 1 else 0)
    (a : Iv → ℝ) :
    ipv (fun v => ∑ q, a q * W q v) (fun v => ∑ q, a q * W q v) = ∑ q, a q ^ 2 := by
  rw [ipv_comb_left hc a (temperate_comb' hc a)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [ipv_sum (hc q) fun i => temperate_const_mul _ (hc i)]
  simp only [ipv_const_mul, ho]
  simp [sq]

/-- The Frobenius norm of `U diag(t) Wᵀ`, for matrices with orthonormal columns. -/
lemma sum_sq_svd {K Kr Rt : Type*} [Fintype K] [DecidableEq K] [Fintype Kr] [Fintype Rt]
    (Ub : Matrix Kr K ℝ) (Wb : Matrix Rt K ℝ) (hU : Ubᵀ * Ub = 1) (hW : Wbᵀ * Wb = 1)
    (t : K → ℝ) :
    ∑ c, ∑ q, (Ub * Matrix.diagonal t * Wbᵀ) c q ^ 2 = ∑ k, t k ^ 2 := by
  set A := Ub * Matrix.diagonal t * Wbᵀ with hA
  have h1 : ∑ c, ∑ q, A c q ^ 2 = Matrix.trace (A * Aᵀ) := by
    simp [Matrix.trace, Matrix.mul_apply, sq]
  have h2 : A * Aᵀ = Ub * (Matrix.diagonal t * Matrix.diagonal t) * Ubᵀ := by
    rw [hA]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose]
    calc Ub * Matrix.diagonal t * Wbᵀ * (Wb * (Matrix.diagonal t * Ubᵀ))
        = Ub * Matrix.diagonal t * (Wbᵀ * Wb) * (Matrix.diagonal t * Ubᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hW, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [h1, h2, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul,
    Matrix.diagonal_mul_diagonal]
  simp [Matrix.trace, sq]

/-- The tail `σ_{r+1}² + … + σ_{r̂}²` of the squared singular values (indices from `0` here). -/
noncomputable def tailSq {rh : ℕ} (σ : Fin rh → ℝ) (r : ℕ) : ℝ :=
  ∑ k : Fin rh with r ≤ k.val, σ k ^ 2

/-- **Rule 1 of Sec. 5 of arXiv 2206.09374 is well defined**: for every `ϑ` there is a smallest
`r ≤ r̂` with `σ_{r+1}² + … + σ_{r̂}² ≤ ϑ²`. -/
theorem exists_tail_rank {rh : ℕ} (σ : Fin rh → ℝ) (θ : ℝ) :
    ∃ r ≤ rh, tailSq σ r ≤ θ ^ 2 ∧ ∀ r' < r, θ ^ 2 < tailSq σ r' := by
  classical
  have hex : ∃ r, tailSq σ r ≤ θ ^ 2 := by
    refine ⟨rh, ?_⟩
    have : tailSq σ rh = 0 := by
      unfold tailSq
      refine Finset.sum_eq_zero fun k hk => ?_
      have := (Finset.mem_filter.1 hk).2
      omega
    rw [this]
    positivity
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex, fun r' hr' => not_le.1 (Nat.find_min hex hr')⟩
  refine Nat.find_min' hex ?_
  have : tailSq σ rh = 0 := by
    unfold tailSq
    refine Finset.sum_eq_zero fun k hk => ?_
    have := (Finset.mem_filter.1 hk).2
    omega
  rw [this]
  positivity

/-! ### The Poisson equation -/

/-- `E = -∇φ` and `∇·E = 1 - ρ` on the torus, with a `C²` periodic potential: the Poisson problem
`-Δφ = 1 - ρ` of the paper. -/
structure IsPoissonField (L : ℝ) (ρ : Pt d → ℝ) (E : Fin d → Pt d → ℝ) (φ : Pt d → ℝ) : Prop where
  smooth : ContDiff ℝ 2 φ
  per : Per L φ
  grad : ∀ s x, E s x = -pd s φ x
  div : ∀ x, ∑ s, pd s (E s) x = 1 - ρ x

namespace IsPoissonField

variable {L : ℝ} {ρ : Pt d → ℝ} {E : Fin d → Pt d → ℝ} {φ : Pt d → ℝ}

lemma cp_potential (hP : IsPoissonField L ρ E φ) : CP L φ :=
  ⟨hP.smooth.of_le (by norm_num), hP.per⟩

lemma field_eq (hP : IsPoissonField L ρ E φ) (s : Fin d) : E s = fun x => -pd s φ x :=
  funext (hP.grad s)

lemma cp_field (hP : IsPoissonField L ρ E φ) (s : Fin d) : CP L (E s) := by
  rw [hP.field_eq s]
  have h1 : ContDiff ℝ 1 (fderiv ℝ φ) := hP.smooth.fderiv_right (by norm_num)
  have h2 : ContDiff ℝ 1 (pd s φ) := h1.clm_apply contDiff_const
  exact CP.neg ⟨h2, hP.per.pd s⟩

/-- The field is curl-free: `∂ᵣ Eₛ = ∂ₛ Eᵣ`. -/
lemma curl_free (hP : IsPoissonField L ρ E φ) (r s : Fin d) (x : Pt d) :
    pd r (E s) x = pd s (E r) x := by
  have hd : Differentiable ℝ (fderiv ℝ φ) :=
    (hP.smooth.fderiv_right (m := 1) (by norm_num)).differentiable (by simp)
  have key : ∀ a b : Fin d, pd a (fun y => -P2206_09374.pd b φ y) x =
      -fderiv ℝ (fderiv ℝ φ) x (Pi.single a 1) (Pi.single b 1) := by
    intro a b
    have e : (fun y => -P2206_09374.pd b φ y) =
        fun y => -(fderiv ℝ φ y (Pi.single b 1)) := rfl
    have h3 : HasFDerivAt (fun y => fderiv ℝ φ y (Pi.single b (1 : ℝ)))
        ((fderiv ℝ (fderiv ℝ φ) x).flip (Pi.single b 1)) x :=
      (hd x).hasFDerivAt.clm_apply (hasFDerivAt_const _ _) |>.congr_fderiv (by ext; simp)
    rw [e, P2206_09374.pd, h3.fun_neg.fderiv]
    simp
  have hsym : IsSymmSndFDerivAt ℝ φ x :=
    (hP.smooth.contDiffAt).isSymmSndFDerivAt (by simp)
  rw [hP.field_eq s, hP.field_eq r, key, key, hsym.eq]

/-- `∫ E dx = 0`. -/
lemma integral_field (hP : IsPoissonField L ρ E φ) (hL : 0 ≤ L) (s : Fin d) :
    ∫ x in box L, E s x = 0 := by
  rw [hP.field_eq s, integral_neg, integral_pd_eq_zero hL hP.cp_potential.1 hP.per s, neg_zero]

/-- **The force has zero mean**: `∫ Eₛ ρ dx = 0`.  This is the integrated form of
`E(1 - ρ) = ∇·(E⊗E - ½E²)` together with `∫ E dx = 0`, used in the proof of Theorem 2 of
arXiv 2206.09374. -/
lemma integral_field_density (hP : IsPoissonField L ρ E φ) (hL : 0 ≤ L) (s : Fin d) :
    ∫ x in box L, E s x * ρ x = 0 := by
  have hρ : ∀ x, ρ x = 1 - ∑ r, pd r (E r) x := fun x => by rw [hP.div]; ring
  have hc := hP.cp_field
  have hcpd : ∀ r, Continuous (pd r (E r)) := fun r => continuous_pd (hc r).1 r
  have h1 : ∀ r, ∫ x in box L, E s x * pd r (E r) x = 0 := by
    intro r
    have h2 := integral_mul_pd hL (hc s) (hc r) r
    have h3 := integral_mul_pd hL (hc r) (hc r) s
    have h4 : ∫ x in box L, pd r (E s) x * E r x = ∫ x in box L, pd s (E r) x * E r x :=
      integral_congr_ae (Eventually.of_forall fun x => by
        simp only [hP.curl_free r s x])
    have h5 : ∫ x in box L, E r x * pd s (E r) x = ∫ x in box L, pd s (E r) x * E r x :=
      integral_congr_ae (Eventually.of_forall fun x => by simp only [mul_comm])
    rw [h2, h4]
    linarith
  have e : ∀ x, E s x * ρ x = E s x - ∑ r, E s x * pd r (E r) x := fun x => by
    rw [hρ, mul_sub, mul_one, Finset.mul_sum]
  simp only [e]
  have i1 : ∀ r, IntegrableOn (fun x => E s x * pd r (E r) x) (box L) := fun r =>
    integrableOn_box ((hc s).continuous.mul (hcpd r)) L
  have i2 : IntegrableOn (fun x => ∑ r, E s x * pd r (E r) x) (box L) :=
    integrable_finsetSum _ fun r _ => i1 r
  rw [integral_sub (integrableOn_box (hc s).continuous L) i2,
    integral_finsetSum _ fun r _ => i1 r, hP.integral_field hL s]
  simp [h1]

end IsPoissonField

/-! ### Algorithm 1 -/

section Algorithm

variable {Mc Rr Ix Rt Kr Rk : Type*} [Fintype Mc] [Fintype Rr] [Fintype Ix] [Fintype Rt]
  [Fintype Kr] [Fintype Rk] [DecidableEq Mc] [DecidableEq Rr] [DecidableEq Ix] [DecidableEq Rt]

/-- A low-rank state: spatial functions `X`, coefficient matrix `S` and the evolving velocity
functions `W`.  The velocity basis is `V = [U, W]`, with the fixed functions `U`, indexed by `Mc`
(so `m = |Mc|`). -/
structure State (Mc Rr : Type*) (d : ℕ) where
  /-- The spatial functions `Xᵢ`. -/
  X : Mc ⊕ Rr → Pt d → ℝ
  /-- The coefficient matrix. -/
  S : Matrix (Mc ⊕ Rr) (Mc ⊕ Rr) ℝ
  /-- The evolving velocity functions. -/
  W : Rr → Pt d → ℝ

/-- The velocity basis `V = [U, W]`. -/
def State.V (s : State Mc Rr d) (U : Mc → Pt d → ℝ) : Mc ⊕ Rr → Pt d → ℝ := Sum.elim U s.W

/-- The function `f = f₀ᵥ ∑ᵢⱼ Xᵢ S_{ij} Vⱼ` represented by a state. -/
noncomputable def State.f (s : State Mc Rr d) (U : Mc → Pt d → ℝ) : Pt d → Pt d → ℝ :=
  lowRank s.X s.S (s.V U)

/-- The standing assumptions on a state: the velocity functions are smooth with polynomially
bounded derivatives, `[U, W]` is orthonormal for `⟨·,·⟩ᵥ`, and the `Xᵢ` are differentiable. -/
structure State.Admissible (s : State Mc Rr d) (U : Mc → Pt d → ℝ) : Prop where
  temperate_U : ∀ a, (U a).HasTemperateGrowth
  temperate_W : ∀ q, (s.W q).HasTemperateGrowth
  orth : ∀ i j, ipv (s.V U i) (s.V U j) = if i = j then 1 else 0
  diff_X : ∀ i, Differentiable ℝ (s.X i)

/-- The right-hand side `RHS[f] = -v·∇ₓf + E(f)·∇ᵥf`, with the field `E(f) = Ef ρ(f)`. -/
noncomputable def rhsOf (Ef : (Pt d → ℝ) → Fin d → Pt d → ℝ) (f : Pt d → Pt d → ℝ) :
    Pt d → Pt d → ℝ :=
  vlasovRHS f (Ef (density f))

/-- Step 1, the explicit Euler K-step (5): `Kₖⁿ⁺¹ = Kₖⁿ + τ (Vₖⁿ, RHSⁿ)ᵥ`. -/
noncomputable def kStep (τ : ℝ) (Ef : (Pt d → ℝ) → Fin d → Pt d → ℝ) (U : Mc → Pt d → ℝ)
    (s : State Mc Rr d) (k : Mc ⊕ Rr) (x : Pt d) : ℝ :=
  coefK s.X s.S k x + τ * ∫ v, s.V U k v * rhsOf Ef (s.f U) x v

/-- Step 1, the explicit Euler L-step (6): `L_qⁿ⁺¹ = L_qⁿ + (τ/f₀ᵥ) ∑ᵢ S_{iq}⟨Xᵢ, RHSⁿ⟩ₓ
- τ ∑ᵢₗ S_{iq} (Xᵢ Vₗ, RHSⁿ)ₓᵥ Vₗ`, with `L_qⁿ = ∑ᵢₚ S_{iq} S_{ip} W_p`. -/
noncomputable def lStep (L τ : ℝ) (Ef : (Pt d → ℝ) → Fin d → Pt d → ℝ) (U : Mc → Pt d → ℝ)
    (s : State Mc Rr d) (q : Rr) (v : Pt d) : ℝ :=
  ∑ i, ∑ p : Rr, s.S i (.inr q) * s.S i (.inr p) * s.W p v +
    τ / f0 v * ∑ i, s.S i (.inr q) * (∫ x in box L, s.X i x * rhsOf Ef (s.f U) x v) -
    τ * ∑ i, ∑ l, s.S i (.inr q) *
      (∫ x in box L, ∫ w, s.X i x * s.V U l w * rhsOf Ef (s.f U) x w) * s.V U l v

/-- The matrix `M Sⁿ Nᵀ` of step 4, `M_{ki} = ⟨X̃ₖ, Xᵢⁿ⟩ₓ`, `Nᵀ_{jl} = ⟨Vⱼⁿ, Ṽₗ⟩ᵥ`. -/
noncomputable def sStart (L : ℝ) (U : Mc → Pt d → ℝ) (s : State Mc Rr d)
    (Xt : Ix → Pt d → ℝ) (Vt : Mc ⊕ Rt → Pt d → ℝ) : Matrix Ix (Mc ⊕ Rt) ℝ :=
  fun k l => ∑ i, ∑ j, ipx L (Xt k) (s.X i) * s.S i j * ipv (s.V U j) (Vt l)

/-- Step 4, the explicit Euler S-step (7): `S̃ₖₗ = (M Sⁿ Nᵀ)ₖₗ + τ (X̃ₖ Ṽₗ, RHS[f̂])ₓᵥ`, with
`f̂ = f₀ᵥ ∑ X̃ₖ (M Sⁿ Nᵀ)ₖₗ Ṽₗ`. -/
noncomputable def sStep (L τ : ℝ) (Ef : (Pt d → ℝ) → Fin d → Pt d → ℝ) (U : Mc → Pt d → ℝ)
    (s : State Mc Rr d) (Xt : Ix → Pt d → ℝ) (Vt : Mc ⊕ Rt → Pt d → ℝ) :
    Matrix Ix (Mc ⊕ Rt) ℝ :=
  fun k l => sStart L U s Xt Vt k l +
    τ * ∫ x in box L, ∫ v, Xt k x * Vt l v * rhsOf Ef (lowRank Xt (sStart L U s Xt Vt) Vt) x v

/-- One step of **Algorithm 1** of arXiv 2206.09374 from the state `s`, with all its factorizations
recorded.  Index types: `Ix` for `X̃`, `Rt` for `W̃`, `Kr` for `X̃ʳᵉᵐ`, `Rk` for the new `W`.

* Steps 1–2: `X̃` is orthonormal, and its span contains `Xⁿ`, `∇Xⁿ` and `Kⁿ⁺¹`.
* Step 3: `Ṽ = [U, W̃]` is orthonormal, and its span contains `Lⁿ⁺¹` and `Wⁿ`.
* Step 4: `S̃ = sStep ...`.
* Steps 5–7: the QR factorizations `K̃ᶜᵒⁿˢ = Xᶜᵒⁿˢ Sᶜᵒⁿˢ` and `K̃ʳᵉᵐ = X̃ʳᵉᵐ S̃ʳᵉᵐ`, of the columns
  of `K̃ = X̃ S̃`.
* Step 8: the (truncated) factors `Û Ŝ Ŵᵀ` of `S̃ʳᵉᵐ`, which may be arbitrary here: an actual
  truncated SVD is assumed in `tail_truncation_error`.
* Steps 9–11: `Wⁿ⁺¹ = W̃ Ŵ`, and the QR factorization `[Xᶜᵒⁿˢ, X̃ʳᵉᵐ Û] = Xⁿ⁺¹ R`.

Only the factorization identities are recorded for `Xᶜᵒⁿˢ`, `X̃ʳᵉᵐ` and `Xⁿ⁺¹`: their orthonormality
is not needed.  A theorem about this structure holds for the paper's algorithm because each QR
factorization `[...] = Q R` gives these span inclusions and identities. -/
structure Alg1Step (L τ : ℝ) (Ef : (Pt d → ℝ) → Fin d → Pt d → ℝ) (U : Mc → Pt d → ℝ)
    (s : State Mc Rr d) (Ix Rt Kr Rk : Type*) [Fintype Ix] [Fintype Rt] [Fintype Kr]
    [Fintype Rk] [DecidableEq Ix] [DecidableEq Rt] where
  /-- The augmented spatial basis `X̃`. -/
  Xt : Ix → Pt d → ℝ
  Xt_cont : ∀ a, Continuous (Xt a)
  Xt_orth : ∀ a b, ipx L (Xt a) (Xt b) = if a = b then 1 else 0
  mem_X : ∀ i, s.X i ∈ Submodule.span ℝ (range Xt)
  mem_dX : ∀ r i, pd r (s.X i) ∈ Submodule.span ℝ (range Xt)
  mem_K : ∀ k, kStep τ Ef U s k ∈ Submodule.span ℝ (range Xt)
  /-- The evolving part `W̃` of the augmented velocity basis. -/
  Wt : Rt → Pt d → ℝ
  Wt_temperate : ∀ q, (Wt q).HasTemperateGrowth
  Vt_orth : ∀ l l', ipv (Sum.elim U Wt l) (Sum.elim U Wt l') = if l = l' then 1 else 0
  mem_L : ∀ q, lStep L τ Ef U s q ∈ Submodule.span ℝ (range (Sum.elim U Wt))
  mem_W : ∀ q, s.W q ∈ Submodule.span ℝ (range (Sum.elim U Wt))
  /-- `Xᶜᵒⁿˢ`. -/
  Xcons : Mc → Pt d → ℝ
  /-- `Sᶜᵒⁿˢ`. -/
  Scons : Matrix Mc Mc ℝ
  qr_cons : ∀ a x, coefK Xt (sStep L τ Ef U s Xt (Sum.elim U Wt)) (.inl a) x =
    ∑ b, Xcons b x * Scons b a
  /-- `X̃ʳᵉᵐ`. -/
  XremT : Kr → Pt d → ℝ
  /-- `S̃ʳᵉᵐ`. -/
  SremT : Matrix Kr Rt ℝ
  qr_rem : ∀ q x, coefK Xt (sStep L τ Ef U s Xt (Sum.elim U Wt)) (.inr q) x =
    ∑ b, XremT b x * SremT b q
  /-- `Û`. -/
  Uh : Matrix Kr Rk ℝ
  /-- `Ŝ`. -/
  Sh : Matrix Rk Rk ℝ
  /-- `Ŵ`. -/
  Wh : Matrix Rt Rk ℝ
  /-- `Xⁿ⁺¹`. -/
  Xnew : Mc ⊕ Rk → Pt d → ℝ
  /-- The factor `R` of step 10. -/
  Rqr : Matrix (Mc ⊕ Rk) (Mc ⊕ Rk) ℝ
  qr_hat : ∀ i x, Sum.elim Xcons (fun b y => ∑ c, XremT c y * Uh c b) i x =
    ∑ k, Xnew k x * Rqr k i

namespace Alg1Step

variable {L τ : ℝ} {Ef : (Pt d → ℝ) → Fin d → Pt d → ℝ} {U : Mc → Pt d → ℝ}
  {s : State Mc Rr d} (h : Alg1Step L τ Ef U s Ix Rt Kr Rk)

/-- The augmented velocity basis `Ṽ = [U, W̃]`. -/
def Vt : Mc ⊕ Rt → Pt d → ℝ := Sum.elim U h.Wt

/-- The coefficient matrix `S̃` of step 4. -/
noncomputable def Stil : Matrix Ix (Mc ⊕ Rt) ℝ := sStep L τ Ef U s h.Xt h.Vt

/-- The untruncated function `f̃ = f₀ᵥ ∑ X̃ₖ S̃ₖₗ Ṽₗ`. -/
noncomputable def ftil : Pt d → Pt d → ℝ := lowRank h.Xt h.Stil h.Vt

/-- The new evolving velocity functions `Wⁿ⁺¹ = W̃ Ŵ`. -/
noncomputable def Wnew (b : Rk) (v : Pt d) : ℝ := ∑ q, h.Wh q b * h.Wt q v

/-- The output of Algorithm 1: `Xⁿ⁺¹`, `Sⁿ⁺¹ = R diag(Sᶜᵒⁿˢ, Ŝ)`, `Vⁿ⁺¹ = [U, Wⁿ⁺¹]`. -/
noncomputable def next : State Mc Rk d where
  X := h.Xnew
  S := h.Rqr * Matrix.fromBlocks h.Scons 0 0 h.Sh
  W := h.Wnew

lemma _root_.LeanDLRA.Literature.P2206_09374.State.Admissible.temperate_V (hs : s.Admissible U)
    (j : Mc ⊕ Rr) : (s.V U j).HasTemperateGrowth := by
  rcases j with a | q
  · exact hs.temperate_U a
  · exact hs.temperate_W q

lemma temperate_Vt (hs : s.Admissible U) (l : Mc ⊕ Rt) : (h.Vt l).HasTemperateGrowth := by
  rcases l with a | q
  · exact hs.temperate_U a
  · exact h.Wt_temperate q

lemma temperate_Wnew (b : Rk) : (h.Wnew b).HasTemperateGrowth :=
  temperate_comb h.Wt_temperate _

lemma temperate_Vnext (hs : s.Admissible U) (j : Mc ⊕ Rk) :
    (h.next.V U j).HasTemperateGrowth := by
  rcases j with a | q
  · exact hs.temperate_U a
  · exact h.temperate_Wnew q

lemma mem_V (j : Mc ⊕ Rr) : s.V U j ∈ Submodule.span ℝ (range h.Vt) := by
  rcases j with a | q
  · exact Submodule.subset_span ⟨.inl a, rfl⟩
  · exact h.mem_W q

/-- `P_{x,n+1} Xᵢⁿ = Xᵢⁿ`. -/
lemma sum_X (i : Mc ⊕ Rr) (x : Pt d) :
    ∑ k, h.Xt k x * ipx L (h.Xt k) (s.X i) = s.X i x :=
  expand_orth h.Xt_cont h.Xt_orth (h.mem_X i) x

/-- `P_{v,n+1} Vⱼⁿ = Vⱼⁿ`. -/
lemma sum_V (hs : s.Admissible U) (j : Mc ⊕ Rr) (v : Pt d) :
    ∑ l, ipv (s.V U j) (h.Vt l) * h.Vt l v = s.V U j v :=
  expand_orth_v (h.temperate_Vt hs) h.Vt_orth (h.mem_V j) v

/-- The function `f̂` of the S-step is `fⁿ`. -/
lemma fhat_eq (hs : s.Admissible U) : lowRank h.Xt (sStart L U s h.Xt h.Vt) h.Vt = s.f U := by
  funext x v
  simp only [lowRank, State.f, sStart]
  congr 1
  have e : ∀ k l, h.Xt k x *
      (∑ i, ∑ j, ipx L (h.Xt k) (s.X i) * s.S i j * ipv (s.V U j) (h.Vt l)) * h.Vt l v =
      ∑ i, ∑ j, h.Xt k x * ipx L (h.Xt k) (s.X i) * s.S i j *
        (ipv (s.V U j) (h.Vt l) * h.Vt l v) := by
    intro k l
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [e]
  rw [sum4]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← h.sum_X i x, ← h.sum_V hs j v, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]

/-- The columns `Kₐⁿ = ∑ᵢ Xᵢ S_{ia}` of the fixed functions are the moments of `fⁿ`. -/
lemma mom_U_state (hs : s.Admissible U) (a : Mc) (x : Pt d) :
    mom (U a) (s.f U) x = coefK s.X s.S (.inl a) x := by
  have e : ∀ j, ipv (U a) (s.V U j) = if Sum.inl a = j then 1 else 0 := fun j =>
    hs.orth (.inl a) j
  rw [State.f, mom_lowRank (hs.temperate_U a) hs.temperate_V]
  simp [e]

/-- The density-independent part of `K̃`: the conserved columns of `K̃ = X̃ S̃` are exactly one
explicit Euler step of the moments of `fⁿ`. -/
lemma Ktil_inl (hs : s.Admissible U) (a : Mc) (x : Pt d) :
    coefK h.Xt h.Stil (.inl a) x =
      coefK s.X s.S (.inl a) x + τ * ∫ v, U a v * rhsOf Ef (s.f U) x v := by
  set Φ : Pt d → ℝ := fun y => τ * ∫ v, U a v * rhsOf Ef (s.f U) y v with hΦ
  -- `Φ = Kⁿ⁺¹ - Kⁿ` lies in the span of `X̃`
  have hKmem : coefK s.X s.S (.inl a) ∈ Submodule.span ℝ (range h.Xt) := by
    have : coefK s.X s.S (.inl a) = ∑ i, s.S i (.inl a) • s.X i := by
      funext y; simp [coefK, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h.mem_X i)
  have hΦmem : Φ ∈ Submodule.span ℝ (range h.Xt) := by
    have : Φ = kStep τ Ef U s (.inl a) - coefK s.X s.S (.inl a) := by
      funext y
      simp [hΦ, kStep, State.V]
    rw [this]
    exact Submodule.sub_mem _ (h.mem_K _) hKmem
  have hstep : ∀ k, h.Stil k (.inl a) =
      ∑ i, ipx L (h.Xt k) (s.X i) * s.S i (.inl a) + ipx L (h.Xt k) Φ := by
    intro k
    have h1 : sStart L U s h.Xt h.Vt k (.inl a) =
        ∑ i, ipx L (h.Xt k) (s.X i) * s.S i (.inl a) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have e : ∀ j, ipv (s.V U j) (h.Vt (.inl a)) = if j = Sum.inl a then 1 else 0 := fun j =>
        hs.orth j (.inl a)
      simp [e]
    have h2 : τ * ∫ y in box L, ∫ v, h.Xt k y * h.Vt (.inl a) v *
        rhsOf Ef (lowRank h.Xt (sStart L U s h.Xt h.Vt) h.Vt) y v = ipx L (h.Xt k) Φ := by
      rw [h.fhat_eq hs, ipx, ← integral_const_mul]
      congr 1; funext y
      simp only [hΦ, ← integral_const_mul]
      congr 1; funext v
      change τ * (h.Xt k y * U a v * _) = _
      ring
    rw [Stil, sStep, h1, h2]
  have hsum : ∑ k, h.Xt k x * ∑ i, ipx L (h.Xt k) (s.X i) * s.S i (.inl a) =
      coefK s.X s.S (.inl a) x := by
    simp only [coefK, ← h.sum_X _ x, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  have hproj := expand_orth h.Xt_cont h.Xt_orth hΦmem x
  simp only [coefK, hstep, mul_add, Finset.sum_add_distrib]
  rw [hproj]
  rw [show ∑ i, s.X i x * s.S i (.inl a) = coefK s.X s.S (.inl a) x from rfl, ← hsum]

/-- `Xⁿ⁺¹ Sⁿ⁺¹ = X̂ diag(Sᶜᵒⁿˢ, Ŝ)`. -/
lemma coefK_next (j : Mc ⊕ Rk) (x : Pt d) :
    coefK h.next.X h.next.S j x =
      ∑ k, Sum.elim h.Xcons (fun b y => ∑ c, h.XremT c y * h.Uh c b) k x *
        Matrix.fromBlocks h.Scons 0 0 h.Sh k j := by
  simp only [coefK, next, Matrix.mul_apply, h.qr_hat, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring

/-- **Conservative truncation** (steps 5–12): the `U`-moments of the output are the conserved
columns of `K̃`, whatever the truncation `Û Ŝ Ŵᵀ` of the remainder. -/
lemma mom_next (hs : s.Admissible U) (c : Mc) (x : Pt d) :
    mom (U c) (h.next.f U) x = coefK h.Xt h.Stil (.inl c) x := by
  have h0 : ∀ b, ipv (U c) (h.Wnew b) = 0 := by
    intro b
    have e : h.Wnew b = fun v => ∑ q, (fun q v => h.Wh q b * h.Wt q v) q v := rfl
    rw [e, ipv_sum (hs.temperate_U c) fun q => temperate_const_mul _ (h.Wt_temperate q)]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [ipv_const_mul]
    have := h.Vt_orth (.inl c) (.inr q)
    simp only [Sum.elim_inl, Sum.elim_inr, reduceCtorEq, ite_false] at this
    rw [this, mul_zero]
  have h1 : ∀ a, ipv (U c) (U a) = if c = a then 1 else 0 := by
    intro a
    have := h.Vt_orth (.inl c) (.inl a)
    simpa using this
  have hK : ∀ a, coefK h.next.X h.next.S (.inl a) x = ∑ b, h.Xcons b x * h.Scons b a := by
    intro a
    rw [h.coefK_next, Fintype.sum_sum_type]
    simp
  rw [State.f, mom_lowRank (hs.temperate_U c) (h.temperate_Vnext hs), Fintype.sum_sum_type]
  have e2 : ∀ b, ipv (U c) (h.next.V U (.inr b)) = 0 := h0
  have e3 : ∀ a, ipv (U c) (h.next.V U (.inl a)) = if c = a then 1 else 0 := h1
  simp only [e2, e3, mul_zero, Finset.sum_const_zero, add_zero, mul_ite, mul_one]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [hK c]
  exact (h.qr_cons c x).symm

lemma _root_.LeanDLRA.Literature.P2206_09374.State.Admissible.diff_coefK (hs : s.Admissible U)
    (j : Mc ⊕ Rr) : Differentiable ℝ (coefK s.X s.S j) := by
  intro y
  exact DifferentiableAt.fun_sum (u := Finset.univ) fun i _ => (hs.diff_X i y).mul_const (s.S i j)

/-- A linear combination of the K-step results is an Euler step of the moment. -/
lemma sum_kStep (hs : s.Admissible U) (c : Mc → ℝ) (x : Pt d) :
    ∑ a, c a * kStep τ Ef U s (.inl a) x =
      mom (fun v => ∑ a, c a * U a v) (s.f U) x +
        τ * ∫ v, (∑ a, c a * U a v) * rhsOf Ef (s.f U) x v := by
  rw [State.f, mom_comb hs.temperate_U c hs.temperate_V,
    rhsOf, rhs_comb hs.temperate_U c hs.temperate_V (fun j => hs.diff_coefK j x),
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [kStep, ← mom_U_state hs a x]
  simp only [State.f, State.V, rhsOf, Sum.elim_inl]
  ring

/-- **Discrete moment law of Algorithm 1** (arXiv 2206.09374, common core of Theorems 1–3): for
every `u ∈ span U`, `∫ u fⁿ⁺¹ dv = ∫ u fⁿ dv + τ ∫ u RHSⁿ dv`, i.e. the `u`-moment of the low-rank
solution is that of the full explicit Euler step, whatever the truncation.  This is the concrete
form of `LeanDLRA.consBug_euler_local_law`.  Neither `∇ₓXⁿ` nor `Lⁿ⁺¹` is used here. -/
theorem moment_law (hs : s.Admissible U) {u : Pt d → ℝ} (hu : u ∈ Submodule.span ℝ (range U))
    (x : Pt d) :
    mom u (h.next.f U) x = mom u (s.f U) x + τ * ∫ v, u v * rhsOf Ef (s.f U) x v := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hu
  have e : (∑ a, c a • U a) = fun v => ∑ a, c a * U a v := by funext v; simp
  rw [e]
  have h2 := sum_kStep (τ := τ) (Ef := Ef) hs c x
  change mom (fun v => ∑ a, c a * U a v) (h.next.f U) x =
    mom (fun v => ∑ a, c a * U a v) (s.f U) x +
      τ * ∫ v, (∑ a, c a * U a v) * rhsOf Ef (s.f U) x v
  rw [← h2, State.f, mom_comb hs.temperate_U c (h.temperate_Vnext hs)]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h3 := h.mom_next hs a x
  rw [State.f] at h3
  rw [h3, h.Ktil_inl hs a x]
  simp only [kStep, State.V, Sum.elim_inl]

lemma temperate_of_mem (hU : ∀ a, (U a).HasTemperateGrowth) {u : Pt d → ℝ}
    (hu : u ∈ Submodule.span ℝ (range U)) : u.HasTemperateGrowth := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hu
  have e : (∑ a, c a • U a) = fun v => ∑ a, c a * U a v := by funext v; simp
  rw [e]
  exact temperate_comb' hU c

/-- The moment law of arXiv 2206.09374 with the moment of the right-hand side in weak form:
`∫ u fⁿ⁺¹ dv = ∫ u fⁿ dv - τ (∇ₓ·∫ v u fⁿ dv + Eⁿ·∫ (∇ᵥu) fⁿ dv)`. -/
theorem weak_moment_law (hs : s.Admissible U) {u : Pt d → ℝ}
    (hu : u ∈ Submodule.span ℝ (range U)) (x : Pt d) :
    mom u (h.next.f U) x = mom u (s.f U) x -
      τ * (∑ r, pd r (mom (fun v => v r * u v) (s.f U)) x +
        ∑ r, Ef (density (s.f U)) r x * mom (pd r u) (s.f U) x) := by
  rw [h.moment_law hs hu x, rhsOf, State.f,
    weak_vlasov (temperate_of_mem hs.temperate_U hu) hs.temperate_V
      (fun j => hs.diff_coefK j x)]
  ring

lemma density_next (hs : s.Admissible U) (h1 : (fun _ => (1 : ℝ)) ∈ Submodule.span ℝ (range U))
    (x : Pt d) :
    density (h.next.f U) x = density (s.f U) x - τ * ∑ r, pd r (current (s.f U) r) x := by
  have key := h.weak_moment_law hs h1 x
  have e1 : ∀ r, mom (fun v => v r * (1 : ℝ)) (s.f U) = current (s.f U) r := fun r => by
    funext y; simp [mom, current]
  have e2 : ∀ r, mom (pd r fun _ => (1 : ℝ)) (s.f U) x = 0 := fun r => by
    have : pd r (fun _ : Pt d => (1 : ℝ)) = fun _ => 0 := by funext y; exact pd_const r 1 y
    simp [this, mom]
  have e3 : ∀ f : Pt d → Pt d → ℝ, mom (fun _ => (1 : ℝ)) f x = density f x := fun f => by
    simp [mom, density]
  simpa only [e1, e2, e3, mul_zero, Finset.sum_const_zero, add_zero] using key

/-- **Theorem 1 of arXiv 2206.09374 (discrete mass continuity equation).**  If `1 ∈ span U`
(`m ≥ 1`, `U₁ = 1/‖1‖`), one step of Algorithm 1 satisfies, at every `x`,
`(ρⁿ⁺¹ - ρⁿ)/τ + ∇ₓ·jⁿ = 0`, with the true moments `ρ = ∫ f dv`, `j = ∫ v f dv` of the
Vlasov–Poisson scheme.  Differences from the paper: the velocity functions are smooth with
polynomially bounded derivatives, and the `∇ₓXⁿ` part of the augmentation is not used.  The global
statement is `mass_conserved`. -/
theorem mass_continuity (hs : s.Admissible U)
    (h1 : (fun _ => (1 : ℝ)) ∈ Submodule.span ℝ (range U)) (hτ : τ ≠ 0) (x : Pt d) :
    (density (h.next.f U) x - density (s.f U) x) / τ + ∑ r, pd r (current (s.f U) r) x = 0 := by
  rw [h.density_next hs h1 x]
  field_simp
  ring

lemma current_next (hs : s.Admissible U) {r₀ : Fin d}
    (hv : (fun v : Pt d => v r₀) ∈ Submodule.span ℝ (range U)) (x : Pt d) :
    current (h.next.f U) r₀ x = current (s.f U) r₀ x -
      τ * (∑ r, pd r (stress (s.f U) r r₀) x +
        Ef (density (s.f U)) r₀ x * density (s.f U) x) := by
  have key := h.weak_moment_law hs hv x
  have e1 : ∀ r, mom (fun v => v r * v r₀) (s.f U) = stress (s.f U) r r₀ := fun r => rfl
  have e2 : ∀ r, mom (pd r fun v : Pt d => v r₀) (s.f U) x =
      if r = r₀ then density (s.f U) x else 0 := fun r => by
    have : pd r (fun v : Pt d => v r₀) = fun _ => if r = r₀ then 1 else 0 := by
      funext y; exact pd_coord r r₀ y
    rw [this]
    by_cases hr : r = r₀ <;> simp [hr, mom, density]
  have e3 : ∀ f : Pt d → Pt d → ℝ, mom (fun v => v r₀) f x = current f r₀ x := fun f => rfl
  simpa only [e1, e2, e3, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    using key

/-- **Theorem 2 of arXiv 2206.09374 (discrete momentum continuity equation).**  If `v_{r₀} ∈ span U`
(for all `r₀` when `m ≥ 1 + d`), one step of Algorithm 1 satisfies, at every `x`,
`(j_{r₀}ⁿ⁺¹ - j_{r₀}ⁿ)/τ + ∑ᵣ ∂ᵣ σᵣᵣ₀ⁿ + E_{r₀}ⁿ ρⁿ = 0`.  The paper proves the case `d = 1` and
remarks that it holds for all `d`; here it is proved for all `d`.  Same regularity difference as
`mass_continuity`.  The global statement is `momentum_conserved`. -/
theorem momentum_continuity (hs : s.Admissible U) {r₀ : Fin d}
    (hv : (fun v : Pt d => v r₀) ∈ Submodule.span ℝ (range U)) (hτ : τ ≠ 0) (x : Pt d) :
    (current (h.next.f U) r₀ x - current (s.f U) r₀ x) / τ +
      ∑ r, pd r (stress (s.f U) r r₀) x + Ef (density (s.f U)) r₀ x * density (s.f U) x = 0 := by
  rw [h.current_next hs hv x]
  field_simp
  ring

lemma heatFlux_eq (f : Pt d → Pt d → ℝ) (r : Fin d) :
    heatFlux f r = fun y => (1 / 2) * mom (fun v => v r * vsq v) f y := rfl

lemma mom_pd_vsq (f : Pt d → Pt d → ℝ) (r : Fin d) (x : Pt d) :
    mom (pd r vsq) f x = 2 * current f r x := by
  have : pd r (vsq : Pt d → ℝ) = fun y => 2 * y r := by funext y; exact pd_vsq r y
  rw [this, mom, current, ← integral_const_mul]
  congr 1; funext v; ring

/-- The change of the energy density in one step, valid for an arbitrary new field `E₁`. -/
lemma energy_increment (hs : s.Admissible U) (he : vsq ∈ Submodule.span ℝ (range U))
    (E₁ : Fin d → Pt d → ℝ) (x : Pt d) :
    energyDensity (h.next.f U) E₁ x - energyDensity (s.f U) (Ef (density (s.f U))) x =
      -τ * ∑ r, pd r (heatFlux (s.f U) r) x +
      ∑ r, Ef (density (s.f U)) r x *
        ((E₁ r x - Ef (density (s.f U)) r x) - τ * current (s.f U) r x) +
      (1 / 2) * ∑ r, (E₁ r x - Ef (density (s.f U)) r x) ^ 2 := by
  have key := h.weak_moment_law hs he x
  set F := s.f U with hF
  set F₁ := h.next.f U with hF₁
  set E := Ef (density F) with hE
  have hdm : ∀ r, Differentiable ℝ (mom (fun v => v r * vsq v) F) := fun r =>
    differentiable_mom (temperate_mul (temperate_coord r) temperate_vsq) hs.temperate_V
      hs.diff_coefK
  have e1 : ∀ r, pd r (mom (fun v => v r * vsq v) F) x = 2 * pd r (heatFlux F r) x := fun r => by
    rw [heatFlux_eq, pd_const_mul r _ (hdm r x)]
    ring
  simp only [e1, mom_pd_vsq] at key
  have e2 : (∑ r, 2 * pd r (heatFlux F r) x) = 2 * ∑ r, pd r (heatFlux F r) x := by
    rw [Finset.mul_sum]
  have e3 : (∑ r, E r x * (2 * current F r x)) = 2 * ∑ r, E r x * current F r x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  rw [e2, e3] at key
  have e4 : (1 / 2 : ℝ) * ∑ r, E₁ r x ^ 2 - (1 / 2) * ∑ r, E r x ^ 2 =
      ∑ r, E r x * (E₁ r x - E r x) + (1 / 2) * ∑ r, (E₁ r x - E r x) ^ 2 := by
    simp only [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => by ring
  have e5 : ∑ r, E r x * ((E₁ r x - E r x) - τ * current F r x) =
      ∑ r, E r x * (E₁ r x - E r x) - τ * ∑ r, E r x * current F r x := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun r _ => by ring
  simp only [energyDensity]
  change (1 / 2) * mom vsq F₁ x + _ - ((1 / 2) * mom vsq F x + _) = _
  rw [key, e5]
  linear_combination e4

/-- **Theorem 3 of arXiv 2206.09374 (discrete energy balance).**  If `v² ∈ span U` (for `m ≥ 2 + d`
in the paper), one step of Algorithm 1 satisfies, at every `x`,
`(eⁿ⁺¹ - eⁿ)/τ + ∇ₓ·Qⁿ - Eⁿ·((Eⁿ⁺¹ - Eⁿ)/τ - jⁿ) = (Eⁿ⁺¹ - Eⁿ)²/(2τ)`, with
`e = ½∫v²f dv + ½E²`, `Q = ½∫v v²f dv`.  The identity does not use the Poisson equation.  The size
of the defect is `energy_defect_le`.  The paper proves the case `d = 1`; here it is proved for
all `d`. -/
theorem energy_balance (hs : s.Admissible U) (he : vsq ∈ Submodule.span ℝ (range U))
    (hτ : τ ≠ 0) (x : Pt d) :
    (energyDensity (h.next.f U) (Ef (density (h.next.f U))) x -
        energyDensity (s.f U) (Ef (density (s.f U))) x) / τ +
      ∑ r, pd r (heatFlux (s.f U) r) x -
      ∑ r, Ef (density (s.f U)) r x *
        ((Ef (density (h.next.f U)) r x - Ef (density (s.f U)) r x) / τ - current (s.f U) r x) =
    ∑ r, (Ef (density (h.next.f U)) r x - Ef (density (s.f U)) r x) ^ 2 / (2 * τ) := by
  rw [h.energy_increment hs he]
  set E := Ef (density (s.f U)) with hE
  set E₁ := Ef (density (h.next.f U)) with hE₁
  set F := s.f U with hF
  have e1 : ∑ r, E r x * ((E₁ r x - E r x) / τ - current F r x) =
      (∑ r, E r x * ((E₁ r x - E r x) - τ * current F r x)) / τ := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun r _ => ?_
    field_simp
  have e2 : ∑ r, (E₁ r x - E r x) ^ 2 / (2 * τ) = (1 / 2) * (∑ r, (E₁ r x - E r x) ^ 2) / τ := by
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun r _ => ?_
    field_simp
  rw [e1, e2]
  field_simp
  ring

lemma mem_coefK (j : Mc ⊕ Rr) : coefK s.X s.S j ∈ Submodule.span ℝ (range h.Xt) := by
  have : coefK s.X s.S j = ∑ i, s.S i j • s.X i := by
    funext y; simp [coefK, mul_comm]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h.mem_X i)

lemma mem_pd_coefK (hs : s.Admissible U) (r : Fin d) (j : Mc ⊕ Rr) :
    pd r (coefK s.X s.S j) ∈ Submodule.span ℝ (range h.Xt) := by
  have : pd r (coefK s.X s.S j) = ∑ i, s.S i j • pd r (s.X i) := by
    funext y
    change pd r (fun x => ∑ i, s.X i x * s.S i j) y = _
    rw [pd_sum r fun i => (hs.diff_X i y).mul_const _]
    simp only [pd_mul_const r _ (hs.diff_X _ y), Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h.mem_dX r i)

lemma mem_mom (hs : s.Admissible U) {u : Pt d → ℝ} (hu : u.HasTemperateGrowth) :
    mom u (s.f U) ∈ Submodule.span ℝ (range h.Xt) := by
  have : mom u (s.f U) = ∑ j, ipv u (s.V U j) • coefK s.X s.S j := by
    funext y
    rw [State.f, mom_lowRank hu hs.temperate_V]
    simp [mul_comm]
  rw [this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (h.mem_coefK j)

lemma mem_pd_mom (hs : s.Admissible U) (r : Fin d) {u : Pt d → ℝ} (hu : u.HasTemperateGrowth) :
    pd r (mom u (s.f U)) ∈ Submodule.span ℝ (range h.Xt) := by
  have : pd r (mom u (s.f U)) = ∑ j, ipv u (s.V U j) • pd r (coefK s.X s.S j) := by
    funext y
    rw [State.f, pd_mom r hu hs.temperate_V fun j => hs.diff_coefK j y]
    simp [mul_comm]
  rw [this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (h.mem_pd_coefK hs r j)

/-- The force part of the K-step lies in the augmented basis (arXiv 2206.09374, the argument of
Lemmas 1 and 2): for `u ∈ span U`, `∑ᵣ Eᵣ ∫ (∂ᵣu) fⁿ dv ∈ span X̃`.  This is the only place where
the `∇ₓXⁿ` augmentation is used: the transport part lies in `span ∇ₓXⁿ`, so that the force part
can be separated from it. -/
theorem force_mem (hs : s.Admissible U) (hτ : τ ≠ 0) {u : Pt d → ℝ}
    (hu : u ∈ Submodule.span ℝ (range U)) :
    (fun x => ∑ r, Ef (density (s.f U)) r x * mom (pd r u) (s.f U) x) ∈
      Submodule.span ℝ (range h.Xt) := by
  have hut := temperate_of_mem hs.temperate_U hu
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hu
  have euc : u = fun v => ∑ a, c a * U a v := by rw [← hc]; funext v; simp
  have hrc : ∀ r, (fun v => v r * u v).HasTemperateGrowth :=
    fun r => temperate_mul (temperate_coord r) hut
  have key : ∀ x, ∑ a, c a * kStep τ Ef U s (.inl a) x = mom u (s.f U) x -
      τ * (∑ r, pd r (mom (fun v => v r * u v) (s.f U)) x +
        ∑ r, Ef (density (s.f U)) r x * mom (pd r u) (s.f U) x) := by
    intro x
    have h2 := sum_kStep (τ := τ) (Ef := Ef) hs c x
    have h3 : (fun v => ∑ a, c a * U a v) = u := euc.symm
    rw [h3] at h2
    have h4 : ∫ v, (∑ a, c a * U a v) * rhsOf Ef (s.f U) x v =
        ∫ v, u v * rhsOf Ef (s.f U) x v := by
      rw [euc]
    rw [h2, h4, rhsOf, State.f, weak_vlasov hut hs.temperate_V fun j => hs.diff_coefK j x]
    ring
  have e : (fun x => ∑ r, Ef (density (s.f U)) r x * mom (pd r u) (s.f U) x) =
      τ⁻¹ • (mom u (s.f U) - ∑ a, c a • kStep τ Ef U s (.inl a)) -
        ∑ r, pd r (mom (fun v => v r * u v) (s.f U)) := by
    funext x
    have := key x
    simp only [Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, this]
    field_simp
    ring
  rw [e]
  refine Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.sub_mem _ (h.mem_mom hs hut)
    (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (h.mem_K _))))
    (Submodule.sum_mem _ fun r _ => h.mem_pd_mom hs r (hrc r))

/-- **Lemma 1 of arXiv 2206.09374**: if `v_{r₀} ∈ span U` (`m ≥ 1 + d`) and `τ ≠ 0`, then
`E_{r₀}ⁿ ρⁿ ∈ span X̃`.  This is the paper's lemma for the actual augmented basis containing
`Xⁿ`, `∇ₓXⁿ`, `Kⁿ⁺¹`. -/
theorem force_density_mem (hs : s.Admissible U) (hτ : τ ≠ 0) {r₀ : Fin d}
    (hv : (fun v : Pt d => v r₀) ∈ Submodule.span ℝ (range U)) :
    (fun x => Ef (density (s.f U)) r₀ x * density (s.f U) x) ∈
      Submodule.span ℝ (range h.Xt) := by
  have := h.force_mem hs hτ hv
  have e2 : ∀ r x, mom (pd r fun v : Pt d => v r₀) (s.f U) x =
      if r = r₀ then density (s.f U) x else 0 := fun r x => by
    have : pd r (fun v : Pt d => v r₀) = fun _ => if r = r₀ then 1 else 0 := by
      funext y; exact pd_coord r r₀ y
    rw [this]
    by_cases hr : r = r₀ <;> simp [hr, mom, density]
  simpa only [e2, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using this

/-- **Lemma 1 of arXiv 2206.09374**, projector form: `P_{x,n+1}(Eⁿρⁿ) = Eⁿρⁿ`. -/
theorem proj_force_density (hs : s.Admissible U) (hτ : τ ≠ 0) {r₀ : Fin d}
    (hv : (fun v : Pt d => v r₀) ∈ Submodule.span ℝ (range U)) (x : Pt d) :
    ∑ k, h.Xt k x * ipx L (h.Xt k) (fun y => Ef (density (s.f U)) r₀ y * density (s.f U) y) =
      Ef (density (s.f U)) r₀ x * density (s.f U) x :=
  expand_orth h.Xt_cont h.Xt_orth (h.force_density_mem hs hτ hv) x

/-- **Lemma 2 of arXiv 2206.09374**: if `v² ∈ span U` and `τ ≠ 0`, then `Eⁿ·jⁿ ∈ span X̃`. -/
theorem force_current_mem (hs : s.Admissible U) (hτ : τ ≠ 0)
    (he : vsq ∈ Submodule.span ℝ (range U)) :
    (fun x => ∑ r, Ef (density (s.f U)) r x * current (s.f U) r x) ∈
      Submodule.span ℝ (range h.Xt) := by
  have h1 := h.force_mem hs hτ he
  have e : (fun x => ∑ r, Ef (density (s.f U)) r x * current (s.f U) r x) =
      (1 / 2 : ℝ) • fun x => ∑ r, Ef (density (s.f U)) r x * mom (pd r vsq) (s.f U) x := by
    funext x
    simp only [mom_pd_vsq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  rw [e]
  exact Submodule.smul_mem _ _ h1

/-- **Lemma 2 of arXiv 2206.09374**, projector form: `P_{x,n+1}(Eⁿ·jⁿ) = Eⁿ·jⁿ`. -/
theorem proj_force_current (hs : s.Admissible U) (hτ : τ ≠ 0)
    (he : vsq ∈ Submodule.span ℝ (range U)) (x : Pt d) :
    ∑ k, h.Xt k x * ipx L (h.Xt k)
        (fun y => ∑ r, Ef (density (s.f U)) r y * current (s.f U) r y) =
      ∑ r, Ef (density (s.f U)) r x * current (s.f U) r x :=
  expand_orth h.Xt_cont h.Xt_orth (h.force_current_mem hs hτ he) x

/-! #### Global conservation -/

/-- `s.Periodic L`: the spatial functions of the state are `C¹` and `L`-periodic. -/
def _root_.LeanDLRA.Literature.P2206_09374.State.Periodic (s : State Mc Rr d) (L : ℝ) : Prop :=
  ∀ i, CP L (s.X i)

lemma cp_coefK (hp : s.Periodic L) (j : Mc ⊕ Rr) : CP L (coefK s.X s.S j) :=
  CP.sum fun i => (hp i).mul_const _

lemma cp_mom (hs : s.Admissible U) (hp : s.Periodic L) {u : Pt d → ℝ}
    (hu : u.HasTemperateGrowth) : CP L (mom u (s.f U)) := by
  have e : mom u (s.f U) = fun y => ∑ j, coefK s.X s.S j y * ipv u (s.V U j) := by
    funext y; exact mom_lowRank hu hs.temperate_V y
  rw [e]
  exact CP.sum fun j => (cp_coefK hp j).mul_const _

lemma density_eq_mom (f : Pt d → Pt d → ℝ) : density f = mom (fun _ => 1) f := by
  funext x; simp [density, mom]

lemma cp_density (hs : s.Admissible U) (hp : s.Periodic L) : CP L (density (s.f U)) := by
  rw [density_eq_mom]
  exact cp_mom hs hp (Function.HasTemperateGrowth.const 1)

lemma cp_current (hs : s.Admissible U) (hp : s.Periodic L) (r : Fin d) :
    CP L (current (s.f U) r) :=
  cp_mom hs hp (temperate_coord r)

lemma cp_stress (hs : s.Admissible U) (hp : s.Periodic L) (r r₀ : Fin d) :
    CP L (stress (s.f U) r r₀) :=
  cp_mom hs hp (temperate_mul (temperate_coord r) (temperate_coord r₀))

lemma cp_heatFlux (hs : s.Admissible U) (hp : s.Periodic L) (r : Fin d) :
    CP L (heatFlux (s.f U) r) := by
  rw [heatFlux_eq]
  exact (cp_mom hs hp (temperate_mul (temperate_coord r) temperate_vsq)).const_mul _

/-- **Mass conservation** (arXiv 2206.09374, Theorem 1, integrated in space): on the torus
`[0, L]^d`, `∫ ρⁿ⁺¹ dx = ∫ ρⁿ dx`. -/
theorem mass_conserved (hs : s.Admissible U) (hp : s.Periodic L) (hL : 0 ≤ L)
    (h1 : (fun _ => (1 : ℝ)) ∈ Submodule.span ℝ (range U)) :
    ∫ x in box L, density (h.next.f U) x = ∫ x in box L, density (s.f U) x := by
  simp only [h.density_next hs h1]
  have hc := fun r => cp_current hs hp (L := L) r (U := U)
  have i1 : ∀ r, IntegrableOn (fun x => pd r (current (s.f U) r) x) (box L) := fun r =>
    integrableOn_box (continuous_pd (hc r).1 r) L
  have i2 : IntegrableOn (fun x => ∑ r, pd r (current (s.f U) r) x) (box L) :=
    integrable_finsetSum _ fun r _ => i1 r
  rw [integral_sub (integrableOn_box (cp_density hs hp).continuous L) (i2.const_mul τ),
    integral_const_mul, integral_finsetSum _ fun r _ => i1 r]
  simp [fun r => integral_pd_eq_zero hL (hc r).1 (hc r).2 r]

/-- **Momentum conservation** (arXiv 2206.09374, Theorem 2, integrated in space): on the torus,
with the Poisson field `Eⁿ = -∇φ`, `∇·Eⁿ = 1 - ρⁿ`, one has `∫ j_{r₀}ⁿ⁺¹ dx = ∫ j_{r₀}ⁿ dx`. -/
theorem momentum_conserved (hs : s.Admissible U) (hp : s.Periodic L) (hL : 0 ≤ L) {r₀ : Fin d}
    (hv : (fun v : Pt d => v r₀) ∈ Submodule.span ℝ (range U)) {φ : Pt d → ℝ}
    (hP : IsPoissonField L (density (s.f U)) (Ef (density (s.f U))) φ) :
    ∫ x in box L, current (h.next.f U) r₀ x = ∫ x in box L, current (s.f U) r₀ x := by
  simp only [h.current_next hs hv]
  have hc := fun r => cp_stress hs hp (L := L) (U := U) r r₀
  have i1 : ∀ r, IntegrableOn (fun x => pd r (stress (s.f U) r r₀) x) (box L) := fun r =>
    integrableOn_box (continuous_pd (hc r).1 r) L
  have i2 : IntegrableOn (fun x => ∑ r, pd r (stress (s.f U) r r₀) x) (box L) :=
    integrable_finsetSum _ fun r _ => i1 r
  have i3 : IntegrableOn
      (fun x => Ef (density (s.f U)) r₀ x * density (s.f U) x) (box L) :=
    integrableOn_box ((hP.cp_field r₀).continuous.mul (cp_density hs hp).continuous) L
  have i4 : IntegrableOn (fun x => ∑ r, pd r (stress (s.f U) r r₀) x +
      Ef (density (s.f U)) r₀ x * density (s.f U) x) (box L) := i2.add i3
  rw [integral_sub (integrableOn_box (cp_current hs hp r₀).continuous L) (i4.const_mul τ),
    integral_const_mul, integral_add i2 i3, integral_finsetSum _ fun r _ => i1 r,
    hP.integral_field_density hL r₀]
  simp [fun r => integral_pd_eq_zero hL (hc r).1 (hc r).2 r]

/-- The divergence of the field increment: `∇·(Eⁿ⁺¹ - Eⁿ) = τ ∇·jⁿ`. -/
lemma div_increment (hs : s.Admissible U)
    (h1 : (fun _ => (1 : ℝ)) ∈ Submodule.span ℝ (range U)) {E E₁ : Fin d → Pt d → ℝ}
    {φ φ₁ : Pt d → ℝ} (hP : IsPoissonField L (density (s.f U)) E φ)
    (hP₁ : IsPoissonField L (density (h.next.f U)) E₁ φ₁) (x : Pt d) :
    ∑ r, pd r (fun y => E₁ r y - E r y) x = τ * ∑ r, pd r (current (s.f U) r) x := by
  have e : ∀ r, pd r (fun y => E₁ r y - E r y) x = pd r (E₁ r) x - pd r (E r) x := fun r =>
    pd_sub r ((hP₁.cp_field r).differentiable x) ((hP.cp_field r).differentiable x)
  simp only [e]
  rw [Finset.sum_sub_distrib, hP₁.div, hP.div, h.density_next hs h1 x]
  ring

/-- `∫ |Eⁿ⁺¹ - Eⁿ|² dx ≤ τ² ∫ |jⁿ|² dx`, derived from the Poisson equation and Theorem 1 of
arXiv 2206.09374.  This is what makes the defect of Theorem 3 of size `O(τ)`. -/
theorem field_increment_le (hs : s.Admissible U) (hp : s.Periodic L) (hL : 0 ≤ L)
    (h1 : (fun _ => (1 : ℝ)) ∈ Submodule.span ℝ (range U)) {φ φ₁ : Pt d → ℝ}
    (hP : IsPoissonField L (density (s.f U)) (Ef (density (s.f U))) φ)
    (hP₁ : IsPoissonField L (density (h.next.f U)) (Ef (density (h.next.f U))) φ₁) :
    ∫ x in box L, ∑ r, (Ef (density (h.next.f U)) r x - Ef (density (s.f U)) r x) ^ 2 ≤
      τ ^ 2 * ∫ x in box L, ∑ r, current (s.f U) r x ^ 2 := by
  set E := Ef (density (s.f U)) with hE
  set E₁ := Ef (density (h.next.f U)) with hE₁
  set j := current (s.f U) with hj
  set δ : Fin d → Pt d → ℝ := fun r y => E₁ r y - E r y with hδ
  set ψ : Pt d → ℝ := fun y => φ₁ y - φ y with hψ
  have cpψ : CP L ψ := hP₁.cp_potential.sub hP.cp_potential
  have cpδ : ∀ r, CP L (δ r) := fun r => (hP₁.cp_field r).sub (hP.cp_field r)
  have cpj : ∀ r, CP L (j r) := fun r => cp_current hs hp r
  have hδψ : ∀ r x, δ r x = -pd r ψ x := fun r x => by
    simp only [hδ, hψ, hP₁.grad, hP.grad]
    rw [pd_sub r (hP₁.cp_potential.differentiable x) (hP.cp_potential.differentiable x)]
    ring
  -- `∫ δᵣ gᵣ = ∫ ψ ∂ᵣ gᵣ`
  have ibp : ∀ r {g : Pt d → ℝ}, CP L g →
      ∫ x in box L, δ r x * g x = ∫ x in box L, ψ x * pd r g x := fun r g hg => by
    rw [integral_mul_pd hL cpψ hg r, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hδψ]
    ring
  have iδ : ∀ r, IntegrableOn (fun x => δ r x ^ 2) (box L) := fun r =>
    integrableOn_box ((cpδ r).continuous.pow 2) L
  have ij : ∀ r, IntegrableOn (fun x => j r x ^ 2) (box L) := fun r =>
    integrableOn_box ((cpj r).continuous.pow 2) L
  have iδj : ∀ r, IntegrableOn (fun x => δ r x * j r x) (box L) := fun r =>
    integrableOn_box ((cpδ r).continuous.mul (cpj r).continuous) L
  have iψδ : ∀ r, IntegrableOn (fun x => ψ x * pd r (δ r) x) (box L) := fun r =>
    integrableOn_box (cpψ.continuous.mul (continuous_pd (cpδ r).1 r)) L
  have iψj : ∀ r, IntegrableOn (fun x => ψ x * pd r (j r) x) (box L) := fun r =>
    integrableOn_box (cpψ.continuous.mul (continuous_pd (cpj r).1 r)) L
  have hD : ∫ x in box L, ∑ r, δ r x ^ 2 = τ * ∑ r, ∫ x in box L, δ r x * j r x := by
    calc ∫ x in box L, ∑ r, δ r x ^ 2
        = ∑ r, ∫ x in box L, δ r x * δ r x := by
          rw [integral_finsetSum _ fun r _ => iδ r]
          simp only [sq]
      _ = ∑ r, ∫ x in box L, ψ x * pd r (δ r) x :=
          Finset.sum_congr rfl fun r _ => ibp r (cpδ r)
      _ = ∫ x in box L, ψ x * ∑ r, pd r (δ r) x := by
          rw [← integral_finsetSum _ fun r _ => iψδ r]
          simp only [Finset.mul_sum]
      _ = ∫ x in box L, τ * ∑ r, ψ x * pd r (j r) x := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          change ψ x * ∑ r, pd r (δ r) x = τ * ∑ r, ψ x * pd r (j r) x
          rw [show ∑ r, pd r (δ r) x = τ * ∑ r, pd r (j r) x from h.div_increment hs h1 hP hP₁ x,
            ← Finset.mul_sum]
          ring
      _ = τ * ∑ r, ∫ x in box L, δ r x * j r x := by
          rw [integral_const_mul, integral_finsetSum _ fun r _ => iψj r]
          congr 1
          exact Finset.sum_congr rfl fun r _ => (ibp r (cpj r)).symm
  have hY : τ * ∑ r, ∫ x in box L, δ r x * j r x ≤
      (1 / 2) * (∑ r, ∫ x in box L, δ r x ^ 2) +
        (1 / 2) * τ ^ 2 * ∑ r, ∫ x in box L, j r x ^ 2 := by
    simp only [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun r _ => ?_
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
      ← integral_add ((iδ r).const_mul _) ((ij r).const_mul _)]
    refine setIntegral_mono ((iδj r).const_mul _)
      (((iδ r).const_mul _).add ((ij r).const_mul _)) fun x => ?_
    nlinarith [sq_nonneg (δ r x - τ * j r x)]
  have e1 : ∫ x in box L, ∑ r, δ r x ^ 2 = ∑ r, ∫ x in box L, δ r x ^ 2 :=
    integral_finsetSum _ fun r _ => iδ r
  have e2 : ∫ x in box L, ∑ r, j r x ^ 2 = ∑ r, ∫ x in box L, j r x ^ 2 :=
    integral_finsetSum _ fun r _ => ij r
  rw [e2]
  rw [hD] at e1
  change ∫ x in box L, ∑ r, δ r x ^ 2 ≤ _
  rw [hD]
  nlinarith

/-- The total energy `ℰ = ∫ e dx = ½ ∫∫ v² f dv dx + ½ ∫ E² dx`. -/
noncomputable def totalEnergy (L : ℝ) (f : Pt d → Pt d → ℝ) (E : Fin d → Pt d → ℝ) : ℝ :=
  ∫ x in box L, energyDensity f E x

/-- **Global energy balance** (arXiv 2206.09374, the remark before Theorem 3): on the torus, with
Poisson fields, `ℰⁿ⁺¹ - ℰⁿ = ½ ∫ |Eⁿ⁺¹ - Eⁿ|² dx`.  So Algorithm 1 does not conserve the energy,
and the error is due only to the explicit time stepping. -/
theorem total_energy_change (hs : s.Admissible U) (hp : s.Periodic L) (hL : 0 ≤ L)
    (h1 : (fun _ => (1 : ℝ)) ∈ Submodule.span ℝ (range U))
    (he : vsq ∈ Submodule.span ℝ (range U)) {φ φ₁ : Pt d → ℝ}
    (hP : IsPoissonField L (density (s.f U)) (Ef (density (s.f U))) φ)
    (hP₁ : IsPoissonField L (density (h.next.f U)) (Ef (density (h.next.f U))) φ₁) :
    totalEnergy L (h.next.f U) (Ef (density (h.next.f U))) -
        totalEnergy L (s.f U) (Ef (density (s.f U))) =
      (1 / 2) * ∫ x in box L, ∑ r,
        (Ef (density (h.next.f U)) r x - Ef (density (s.f U)) r x) ^ 2 := by
  set E := Ef (density (s.f U)) with hE
  set E₁ := Ef (density (h.next.f U)) with hE₁
  set j := current (s.f U) with hj
  set G : Fin d → Pt d → ℝ := fun r y => (E₁ r y - E r y) - τ * j r y with hG
  have cpE := hP.cp_field
  have cpE₁ := hP₁.cp_field
  have cpj : ∀ r, CP L (j r) := fun r => cp_current hs hp r
  have cpG : ∀ r, CP L (G r) := fun r => ((cpE₁ r).sub (cpE r)).sub ((cpj r).const_mul τ)
  have cpQ : ∀ r, CP L (heatFlux (s.f U) r) := fun r => cp_heatFlux hs hp r
  have hdivG : ∀ x, ∑ r, pd r (G r) x = 0 := by
    intro x
    have e : ∀ r, pd r (G r) x = pd r (fun y => E₁ r y - E r y) x - τ * pd r (j r) x := fun r => by
      rw [show G r = fun y => (fun y => E₁ r y - E r y) y - τ * j r y from rfl,
        pd_sub r (((cpE₁ r).sub (cpE r)).differentiable x)
          (((cpj r).const_mul τ).differentiable x),
        pd_const_mul r _ ((cpj r).differentiable x)]
    simp only [e]
    have h5 := h.div_increment hs h1 hP hP₁ x
    rw [Finset.sum_sub_distrib, h5, ← Finset.mul_sum]
    exact sub_self _
  have hzero : ∑ r, ∫ x in box L, E r x * G r x = 0 := by
    have e : ∀ r, ∫ x in box L, E r x * G r x = ∫ x in box L, φ x * pd r (G r) x := fun r => by
      rw [integral_mul_pd hL hP.cp_potential (cpG r) r, ← integral_neg]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      change E r x * G r x = _
      rw [hP.grad]
      ring
    simp only [e]
    have iφ : ∀ r, IntegrableOn (fun x => φ x * pd r (G r) x) (box L) := fun r =>
      integrableOn_box (hP.cp_potential.continuous.mul (continuous_pd (cpG r).1 r)) L
    rw [← integral_finsetSum _ fun r _ => iφ r]
    have : ∀ x, ∑ r, φ x * pd r (G r) x = 0 := fun x => by
      rw [← Finset.mul_sum, hdivG x, mul_zero]
    simp [this]
  have cA : Continuous fun x => ∑ r, pd r (heatFlux (s.f U) r) x :=
    continuous_finsetSum _ fun r _ => continuous_pd (cpQ r).1 r
  have cB : ∀ r, Continuous fun x => E r x * G r x := fun r =>
    (cpE r).continuous.mul (cpG r).continuous
  have cD : Continuous fun x => ∑ r, (E₁ r x - E r x) ^ 2 :=
    continuous_finsetSum _ fun r _ => ((cpE₁ r).continuous.sub (cpE r).continuous).pow 2
  have cB' : Continuous fun x => ∑ r, E r x * G r x := continuous_finsetSum _ fun r _ => cB r
  have ce : Continuous (energyDensity (s.f U) E) := by
    have : Continuous (mom vsq (s.f U)) := (cp_mom hs hp temperate_vsq).continuous
    have e : energyDensity (s.f U) E =
        fun x => (1 / 2) * mom vsq (s.f U) x + (1 / 2) * ∑ r, E r x ^ 2 := rfl
    rw [e]
    exact (continuous_const.mul this).add (continuous_const.mul
      (continuous_finsetSum _ fun r _ => (cpE r).continuous.pow 2))
  have hinc : ∀ x, energyDensity (h.next.f U) E₁ x - energyDensity (s.f U) E x =
      -τ * ∑ r, pd r (heatFlux (s.f U) r) x + ∑ r, E r x * G r x +
        (1 / 2) * ∑ r, (E₁ r x - E r x) ^ 2 := fun x => h.energy_increment hs he E₁ x
  have ce₁ : Continuous (energyDensity (h.next.f U) E₁) := by
    have e : energyDensity (h.next.f U) E₁ = fun x => energyDensity (s.f U) E x +
        (-τ * ∑ r, pd r (heatFlux (s.f U) r) x + ∑ r, E r x * G r x +
          (1 / 2) * ∑ r, (E₁ r x - E r x) ^ 2) := by
      funext x
      rw [← hinc x]
      ring
    rw [e]
    exact ce.add (((continuous_const.mul cA).add cB').add (continuous_const.mul cD))
  unfold totalEnergy
  rw [← integral_sub (integrableOn_box ce₁ L) (integrableOn_box ce L)]
  simp only [hinc]
  have iA := integrableOn_box cA L
  have iB := integrableOn_box cB' L
  have iD := integrableOn_box cD L
  have iAB : IntegrableOn (fun x => -τ * ∑ r, pd r (heatFlux (s.f U) r) x + ∑ r, E r x * G r x)
      (box L) := (iA.const_mul _).add iB
  rw [integral_add iAB (iD.const_mul _), integral_add (iA.const_mul _) iB, integral_const_mul,
    integral_const_mul, integral_finsetSum _ fun r _ => integrableOn_box (cB r) L, hzero,
    integral_finsetSum _ fun r _ => integrableOn_box (continuous_pd (cpQ r).1 r) L]
  simp [fun r => integral_pd_eq_zero hL (cpQ r).1 (cpQ r).2 r]

/-- **The defect of Theorem 3 is `O(τ)`** (arXiv 2206.09374, last equality of Theorem 3), in
`L¹(Ωₓ)` rather than pointwise: `∫ |Eⁿ⁺¹ - Eⁿ|²/(2τ) dx ≤ (τ/2) ∫ |jⁿ|² dx` for `τ > 0`. -/
theorem energy_defect_le (hs : s.Admissible U) (hp : s.Periodic L) (hL : 0 ≤ L) (hτ : 0 < τ)
    (h1 : (fun _ => (1 : ℝ)) ∈ Submodule.span ℝ (range U)) {φ φ₁ : Pt d → ℝ}
    (hP : IsPoissonField L (density (s.f U)) (Ef (density (s.f U))) φ)
    (hP₁ : IsPoissonField L (density (h.next.f U)) (Ef (density (h.next.f U))) φ₁) :
    ∫ x in box L, ∑ r,
        (Ef (density (h.next.f U)) r x - Ef (density (s.f U)) r x) ^ 2 / (2 * τ) ≤
      (τ / 2) * ∫ x in box L, ∑ r, current (s.f U) r x ^ 2 := by
  have key := h.field_increment_le hs hp hL h1 hP hP₁
  simp only [← Finset.sum_div]
  rw [integral_div, div_le_iff₀ (by positivity)]
  calc _ ≤ τ ^ 2 * ∫ x in box L, ∑ r, current (s.f U) r x ^ 2 := key
    _ = _ := by ring

/-- **The energy error per step is `O(τ²)`** (arXiv 2206.09374, the remark before Theorem 3):
`|ℰⁿ⁺¹ - ℰⁿ| ≤ (τ²/2) ∫ |jⁿ|² dx`. -/
theorem total_energy_error_le (hs : s.Admissible U) (hp : s.Periodic L) (hL : 0 ≤ L)
    (h1 : (fun _ => (1 : ℝ)) ∈ Submodule.span ℝ (range U))
    (he : vsq ∈ Submodule.span ℝ (range U)) {φ φ₁ : Pt d → ℝ}
    (hP : IsPoissonField L (density (s.f U)) (Ef (density (s.f U))) φ)
    (hP₁ : IsPoissonField L (density (h.next.f U)) (Ef (density (h.next.f U))) φ₁) :
    |totalEnergy L (h.next.f U) (Ef (density (h.next.f U))) -
        totalEnergy L (s.f U) (Ef (density (s.f U)))| ≤
      (τ ^ 2 / 2) * ∫ x in box L, ∑ r, current (s.f U) r x ^ 2 := by
  have key := h.field_increment_le hs hp hL h1 hP hP₁
  rw [h.total_energy_change hs hp hL h1 he hP hP₁]
  have h0 : 0 ≤ ∫ x in box L, ∑ r,
      (Ef (density (h.next.f U)) r x - Ef (density (s.f U)) r x) ^ 2 :=
    integral_nonneg fun x => Finset.sum_nonneg fun r _ => sq_nonneg _
  rw [abs_of_nonneg (by positivity)]
  linarith

/-! #### Section 5: rank-adaptive truncation -/

/-- The conservative truncation of arXiv 2206.09374 (Algorithm 1, steps 5–12): moments in `span U`
do not see the truncation, they agree for the output `fⁿ⁺¹` and the untruncated `f̃`. -/
theorem mom_next_eq_ftil (hs : s.Admissible U) {u : Pt d → ℝ}
    (hu : u ∈ Submodule.span ℝ (range U)) (x : Pt d) :
    mom u (h.next.f U) x = mom u h.ftil x := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hu
  have euc : u = fun v => ∑ a, c a * U a v := by rw [← hc]; funext v; simp
  rw [euc, State.f, mom_comb hs.temperate_U c (h.temperate_Vnext hs), ftil,
    mom_comb hs.temperate_U c (h.temperate_Vt hs)]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h3 := h.mom_next hs a x
  rw [State.f] at h3
  rw [h3, mom_lowRank (hs.temperate_U a) (h.temperate_Vt hs)]
  have e : ∀ l, ipv (U a) (h.Vt l) = if Sum.inl a = l then 1 else 0 := fun l =>
    h.Vt_orth (.inl a) l
  simp [e]

/-- **Rule 2 of Sec. 5 of arXiv 2206.09374 cannot react to the truncation**.  If `1 ∈ span U`, the
density and hence the electric field of the truncated function agree with those of `f̃`, for every
truncation of `S̃ʳᵉᵐ`.  So `e_l = e` for all `l`, the test `|e - e_l| ≤ ϑ` always holds, and the
rule always ends in the fallback rank.  In particular it gives no control of a norm of the
truncation error.  (Here `e_l` is read as the electric energy of Algorithm 1 with `l` singular
values of `S̃ʳᵉᵐ` kept.  This explains the paper's remark that for `l < m` the error in the
electric energy is always below the threshold.) -/
theorem field_next_eq_ftil (hs : s.Admissible U)
    (h1 : (fun _ => (1 : ℝ)) ∈ Submodule.span ℝ (range U)) :
    Ef (density (h.next.f U)) = Ef (density h.ftil) := by
  have : density (h.next.f U) = density h.ftil := by
    rw [density_eq_mom, density_eq_mom]
    exact funext (h.mom_next_eq_ftil hs h1)
  rw [this]

/-- The electric energy `½ ∫ E² dx`. -/
noncomputable def electricEnergy (L : ℝ) (E : Fin d → Pt d → ℝ) : ℝ :=
  (1 / 2) * ∫ x in box L, ∑ r, E r x ^ 2

/-- **Rule 2 of Sec. 5 of arXiv 2206.09374**: the quantity `|e - e_l|` tested by the rule vanishes,
see `field_next_eq_ftil`. -/
theorem electric_energy_error_eq_zero (hs : s.Admissible U)
    (h1 : (fun _ => (1 : ℝ)) ∈ Submodule.span ℝ (range U)) :
    |electricEnergy L (Ef (density h.ftil)) -
      electricEnergy L (Ef (density (h.next.f U)))| = 0 := by
  rw [h.field_next_eq_ftil hs h1, sub_self, abs_zero]

/-- **Rule 3 of Sec. 5 of arXiv 2206.09374 cannot react to the truncation** when `1, v² ∈ span U`
(so for `m ≥ 2 + d`): the total energy `ℰ_l` of the truncated function is that of `f̃`, for every
truncation.  So `|ℰ_l - ℰⁿ| ≤ ϑ` holds for all `l` or for none.  By `total_energy_change` the
common value is `½ ∫ |Eⁿ⁺¹ - Eⁿ|² dx`, so no `l` is admissible once `ϑ` is below it, and rule 3
is not well defined there without a fallback. -/
theorem total_energy_next_eq_ftil (hs : s.Admissible U)
    (h1 : (fun _ => (1 : ℝ)) ∈ Submodule.span ℝ (range U))
    (he : vsq ∈ Submodule.span ℝ (range U)) :
    totalEnergy L (h.next.f U) (Ef (density (h.next.f U))) =
      totalEnergy L h.ftil (Ef (density h.ftil)) := by
  rw [h.field_next_eq_ftil hs h1]
  unfold totalEnergy energyDensity
  simp only [show ∀ x, (∫ v, vsq v * h.next.f U x v) = ∫ v, vsq v * h.ftil x v from
    h.mom_next_eq_ftil hs he]

/-- The untruncated and the output function differ by the discarded part of the remainder. -/
lemma ftil_sub_next (x v : Pt d) :
    h.ftil x v - h.next.f U x v = f0 v * ∑ q, (∑ c, h.XremT c x *
      (h.SremT - h.Uh * h.Sh * h.Whᵀ) c q) * h.Wt q v := by
  have hcons : ∀ a, coefK h.next.X h.next.S (.inl a) x = coefK h.Xt h.Stil (.inl a) x := by
    intro a
    rw [h.coefK_next, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Matrix.fromBlocks_apply₁₁, Sum.elim_inr, Matrix.fromBlocks_apply₂₁,
      Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
    exact (h.qr_cons a x).symm
  have hrem : ∀ b, coefK h.next.X h.next.S (.inr b) x =
      ∑ c, h.XremT c x * (h.Uh * h.Sh) c b := by
    intro b
    rw [h.coefK_next, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Matrix.fromBlocks_apply₁₂, Sum.elim_inr, Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply, mul_zero, Finset.sum_const_zero, zero_add, Matrix.mul_apply,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b' _ => by ring
  have hmul : ∀ c q, (h.Uh * h.Sh * h.Whᵀ) c q = ∑ b, (h.Uh * h.Sh) c b * h.Wh q b :=
    fun c q => by rw [Matrix.mul_apply]; rfl
  have hdisc : ∑ b, coefK h.next.X h.next.S (.inr b) x * h.Wnew b v =
      ∑ q, (∑ c, h.XremT c x * (h.Uh * h.Sh * h.Whᵀ) c q) * h.Wt q v := by
    calc ∑ b, coefK h.next.X h.next.S (.inr b) x * h.Wnew b v
        = ∑ b, ∑ c, ∑ q, h.XremT c x * (h.Uh * h.Sh) c b * (h.Wh q b * h.Wt q v) := by
          simp only [hrem, Wnew, Finset.sum_mul_sum]
      _ = ∑ c, ∑ b, ∑ q, h.XremT c x * (h.Uh * h.Sh) c b * (h.Wh q b * h.Wt q v) :=
          Finset.sum_comm
      _ = ∑ c, ∑ q, ∑ b, h.XremT c x * (h.Uh * h.Sh) c b * (h.Wh q b * h.Wt q v) :=
          Finset.sum_congr rfl fun c _ => Finset.sum_comm
      _ = ∑ q, ∑ c, ∑ b, h.XremT c x * (h.Uh * h.Sh) c b * (h.Wh q b * h.Wt q v) :=
          Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [hmul, Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun b _ => by ring
  have hsub : ∑ q, (∑ c, h.XremT c x * (h.SremT - h.Uh * h.Sh * h.Whᵀ) c q) * h.Wt q v =
      ∑ q, (∑ c, h.XremT c x * h.SremT c q) * h.Wt q v -
        ∑ q, (∑ c, h.XremT c x * (h.Uh * h.Sh * h.Whᵀ) c q) * h.Wt q v := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← sub_mul, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.sub_apply]
    ring
  rw [ftil, State.f, lowRank_eq, lowRank_eq, ← mul_sub, Fintype.sum_sum_type,
    Fintype.sum_sum_type, hsub, ← hdisc]
  congr 1
  have e1 : ∀ q, coefK h.Xt h.Stil (.inr q) x = ∑ c, h.XremT c x * h.SremT c q :=
    fun q => h.qr_rem q x
  have e2 : ∀ a, h.next.V U (.inl a) = U a := fun _ => rfl
  have e3 : ∀ b, h.next.V U (.inr b) = h.Wnew b := fun _ => rfl
  have e4 : ∀ a, h.Vt (.inl a) = U a := fun _ => rfl
  have e5 : ∀ q, h.Vt (.inr q) = h.Wt q := fun _ => rfl
  simp only [hcons, e1, e2, e3, e4, e5]
  ring

/-- The squared `L²(f₀ᵥ⁻¹)` distance `∫∫ (f - g)²/f₀ᵥ dv dx`; for `f = f₀ᵥ ∑ X S V` with
orthonormal bases this is the squared Frobenius norm of the coefficient matrix. -/
noncomputable def distSq (L : ℝ) (f g : Pt d → Pt d → ℝ) : ℝ :=
  ∫ x in box L, ∫ v, (f x v - g x v) ^ 2 / f0 v

/-- **Rule 1 of Sec. 5 of arXiv 2206.09374**: if `S̃ʳᵉᵐ = Ū diag(σ) W̄ᵀ` is an SVD and the
truncation keeps the first `r` singular values, the conservative truncation has error exactly
`‖f̃ - fⁿ⁺¹‖² = σ_{r+1}² + … + σ_{r̂}²`.  So the moments are conserved exactly and the tolerance
controls the error in `f`, as stated in the paper.  This gives the truncation hypothesis
`‖Y₁ - Ŷ₁‖ ≤ ϑ` of `Integrators/RankAdaptiveBUG.lean`.  Here `X̃ʳᵉᵐ` is orthonormal, as in
step 7. -/
theorem tail_truncation_error [DecidableEq Kr] (hXc : ∀ c, Continuous (h.XremT c))
    (hXo : ∀ a b, ipx L (h.XremT a) (h.XremT b) = if a = b then 1 else 0) {rh r : ℕ}
    (σ : Fin rh → ℝ) (Ub : Matrix Kr (Fin rh) ℝ) (Wb : Matrix Rt (Fin rh) ℝ)
    (hUb : Ubᵀ * Ub = 1) (hWb : Wbᵀ * Wb = 1) (hsvd : h.SremT = Ub * Matrix.diagonal σ * Wbᵀ)
    (htr : h.Uh * h.Sh * h.Whᵀ =
      Ub * Matrix.diagonal (fun k : Fin rh => if k.val < r then σ k else 0) * Wbᵀ) :
    distSq L h.ftil (h.next.f U) = tailSq σ r := by
  classical
  set t : Fin rh → ℝ := fun k => σ k - if k.val < r then σ k else 0 with ht
  have hA : h.SremT - h.Uh * h.Sh * h.Whᵀ = Ub * Matrix.diagonal t * Wbᵀ := by
    rw [hsvd, htr, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]
  set A := h.SremT - h.Uh * h.Sh * h.Whᵀ with hAdef
  have hWo : ∀ a b, ipv (h.Wt a) (h.Wt b) = if a = b then 1 else 0 := fun a b => by
    have := h.Vt_orth (.inr a) (.inr b)
    simpa using this
  have hinner : ∀ x, ∫ v, (h.ftil x v - h.next.f U x v) ^ 2 / f0 v =
      ∑ q, (∑ c, h.XremT c x * A c q) ^ 2 := by
    intro x
    rw [← ipv_comb_self h.Wt_temperate hWo]
    unfold ipv
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    change (h.ftil x v - h.next.f U x v) ^ 2 / f0 v =
      f0 v * (∑ q, (∑ c, h.XremT c x * A c q) * h.Wt q v) *
        ∑ q, (∑ c, h.XremT c x * A c q) * h.Wt q v
    rw [h.ftil_sub_next]
    have := (f0_pos v).ne'
    field_simp
    rfl
  have hcq : ∀ q, Continuous fun x => (∑ c, h.XremT c x * A c q) ^ 2 := fun q =>
    (continuous_finsetSum _ fun c _ => (hXc c).mul continuous_const).pow 2
  have htail : ∑ k, t k ^ 2 = tailSq σ r := by
    unfold tailSq
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k.val < r
    · simp [ht, hk, not_le.2 hk]
    · simp [ht, hk, not_lt.1 hk]
  unfold distSq
  simp only [hinner]
  rw [integral_finsetSum _ fun q _ => integrableOn_box (hcq q) L]
  simp only [integral_comb_sq hXc hXo]
  rw [Finset.sum_comm, hA, sum_sq_svd Ub Wb hUb hWb, htail]

/-- **Rule 1 of Sec. 5 of arXiv 2206.09374**, with the tolerance: if `σ_{r+1}² + … + σ_{r̂}² ≤ ϑ²`,
then the truncation error is at most `ϑ²` (squared). -/
theorem tail_rule_error_le [DecidableEq Kr] (hXc : ∀ c, Continuous (h.XremT c))
    (hXo : ∀ a b, ipx L (h.XremT a) (h.XremT b) = if a = b then 1 else 0) {rh r : ℕ}
    (σ : Fin rh → ℝ) (Ub : Matrix Kr (Fin rh) ℝ) (Wb : Matrix Rt (Fin rh) ℝ)
    (hUb : Ubᵀ * Ub = 1) (hWb : Wbᵀ * Wb = 1) (hsvd : h.SremT = Ub * Matrix.diagonal σ * Wbᵀ)
    (htr : h.Uh * h.Sh * h.Whᵀ =
      Ub * Matrix.diagonal (fun k : Fin rh => if k.val < r then σ k else 0) * Wbᵀ)
    {θ : ℝ} (hθ : tailSq σ r ≤ θ ^ 2) : distSq L h.ftil (h.next.f U) ≤ θ ^ 2 := by
  rw [h.tail_truncation_error hXc hXo σ Ub Wb hUb hWb hsvd htr]
  exact hθ

end Alg1Step

end Algorithm

/-! ### The fixed functions -/

section FixedFunctions

/-- `Z = ‖1‖² = ∫ f₀ᵥ dv`. -/
noncomputable def gaussMass (d : ℕ) : ℝ := ∫ v : Pt d, f0 v

lemma gaussMass_pos : 0 < gaussMass d := by
  have hi : Integrable (f0 : Pt d → ℝ) := by
    simpa using integrable_f0_mul (Function.HasTemperateGrowth.const (1 : ℝ) (E := Pt d))
  refine (integral_pos_iff_support_of_nonneg (fun v => (f0_pos v).le) hi).2 ?_
  have : Function.support (f0 : Pt d → ℝ) = univ := by
    ext v; simp [(f0_pos v).ne']
  rw [this]
  exact IsOpen.measure_pos volume isOpen_univ univ_nonempty

local notation "𝟙" => (fun _ : Pt d => (1 : ℝ))

lemma temperate_one : (𝟙).HasTemperateGrowth := Function.HasTemperateGrowth.const 1

lemma ipv_one_one : ipv 𝟙 𝟙 = gaussMass d := by
  simp [ipv, gaussMass]

/-- **Stein's identity**: `∫ f₀ᵥ g vₛ dv = ∫ f₀ᵥ ∂ₛ g dv`. -/
lemma stein (s : Fin d) {g : Pt d → ℝ} (hg : g.HasTemperateGrowth) :
    ipv g (fun v => v s) = ipv (pd s g) 𝟙 := by
  have h := ipv_Aop s hg temperate_one
  have e : Aop s 𝟙 = fun v => (-1) * v s := by
    funext v
    simp [Aop, pd_const]
  rw [e, ipv_const_mul] at h
  linarith

lemma ipv_zero_left (g : Pt d → ℝ) : ipv (fun _ => 0) g = 0 := by
  simp [ipv]

lemma ipv_one_coord (s : Fin d) : ipv 𝟙 (fun v => v s) = 0 := by
  rw [stein s temperate_one]
  have : pd s 𝟙 = fun _ => 0 := by funext y; exact pd_const s 1 y
  rw [this, ipv_zero_left]

lemma ipv_coord_coord (r s : Fin d) :
    ipv (fun v => v r) (fun v => v s) = if r = s then gaussMass d else 0 := by
  rw [stein s (temperate_coord r)]
  have : pd s (fun v : Pt d => v r) = fun _ => if s = r then 1 else 0 := by
    funext y; exact pd_coord s r y
  rw [this]
  by_cases h : r = s
  · simp [h, ipv_one_one]
  · have h' : ¬ s = r := fun e => h e.symm
    simp [h, h', ipv_zero_left]

lemma vsq_eq : (vsq : Pt d → ℝ) = fun v => ∑ s, v s * v s := by
  funext v; simp [vsq, sq]

lemma ipv_vsq_right {g : Pt d → ℝ} (hg : g.HasTemperateGrowth) :
    ipv g vsq = ∑ s, ipv (fun v => g v * v s) (fun v => v s) := by
  rw [vsq_eq, ipv_sum hg fun s => temperate_mul (temperate_coord s) (temperate_coord s)]
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold ipv
  congr 1; funext v; ring

lemma ipv_one_vsq : ipv 𝟙 vsq = d * gaussMass d := by
  rw [ipv_vsq_right temperate_one]
  have : ∀ s, ipv (fun v : Pt d => v s) (fun v : Pt d => v s) = gaussMass d := fun s => by
    simpa using ipv_coord_coord s s
  simp only [one_mul, this]
  simp

lemma ipv_coord_vsq (s : Fin d) : ipv (fun v => v s) vsq = 0 := by
  rw [ipv_comm, stein s temperate_vsq]
  have : pd s (vsq : Pt d → ℝ) = fun y => 2 * y s := by funext y; exact pd_vsq s y
  rw [this, ipv_comm, ipv_const_mul, ipv_one_coord, mul_zero]

lemma ipv_vsq_vsq : ipv (vsq : Pt d → ℝ) vsq = d * (d + 2) * gaussMass d := by
  rw [ipv_vsq_right temperate_vsq]
  have key : ∀ s, ipv (fun v => vsq v * v s) (fun v : Pt d => v s) =
      (d + 2) * gaussMass d := by
    intro s
    have hm := temperate_mul (temperate_vsq (d := d)) (temperate_coord s)
    rw [stein s hm]
    have e : pd s (fun v => vsq v * v s) =
        fun y => 2 * (y s * y s) + (1 : ℝ) * vsq y := by
      funext y
      rw [pd_mul s ((diff_of_temperate temperate_vsq) y) (differentiable_coord s y), pd_vsq,
        pd_coord]
      simp
      ring
    rw [e, ipv_comm]
    have h2 := ipv_add (g := 𝟙) temperate_one
      (temperate_const_mul 2 (temperate_mul (temperate_coord s) (temperate_coord s)))
      (temperate_const_mul 1 (temperate_vsq (d := d)))
    rw [h2, ipv_const_mul, ipv_const_mul, ipv_one_vsq]
    have h3 : ipv 𝟙 (fun v : Pt d => v s * v s) = gaussMass d := by
      have := ipv_coord_coord s s
      simp only [ite_true] at this
      rw [← this]
      unfold ipv
      congr 1; funext v; ring
    rw [h3]
    ring
  simp only [key]
  simp
  ring

/-- The fixed functions: `1/‖1‖`, `vₛ/‖vₛ‖` and `(v² - d)/‖v² - d‖`.  For `d = 1` these are the
functions `U₁, U₂, U₃` of the paper.  For `d = 3` the paper writes `(v² - 1)/‖v² - 1‖`, which
is not orthogonal to `U₁`, see `fixed_function_not_orthogonal`. -/
noncomputable def fixedU (d : ℕ) : Fin d ⊕ Bool → Pt d → ℝ
  | .inl s, v => (1 / Real.sqrt (gaussMass d)) * v s
  | .inr false, _ => (1 / Real.sqrt (gaussMass d)) * 1
  | .inr true, v => (1 / Real.sqrt (2 * d * gaussMass d)) * (vsq v - d)

/-- **`(v² - 1)/‖v² - 1‖` is orthogonal to `U₁ = 1/‖1‖` only for `d = 1`**:
`⟨1, v² - 1⟩ᵥ = (d - 1) ‖1‖²`.  So the claim of Sec. 3 of arXiv 2206.09374 that
`U₅ = (v² - 1)/‖v² - 1‖` in three dimensions, together with the required
`⟨U_a, U_b⟩ᵥ = δ_{ab}`, is false for the weight `exp(-v²/2)`.  The correct function is `v² - d`,
used in `fixedU`.  Theorems 1–3 hold for it, and they only need `1, vₛ, v² ∈ span U`. -/
theorem ipv_one_vsq_sub_one : ipv 𝟙 (fun v : Pt d => vsq v - 1) = (d - 1) * gaussMass d := by
  have e : (fun v : Pt d => vsq v - 1) = fun v => vsq v + (-1) * 1 := by funext v; ring
  rw [e, ipv_add temperate_one temperate_vsq (temperate_const_mul _ temperate_one),
    ipv_one_vsq, ipv_const_mul, ipv_one_one]
  ring

/-- **False claim in Sec. 3 of arXiv 2206.09374**, see `ipv_one_vsq_sub_one`: in dimension `d = 3`,
`v² - 1` is not orthogonal to `1`, so `U₅ = (v² - 1)/‖v² - 1‖` violates `⟨U₁, U₅⟩ᵥ = 0`. -/
theorem fixed_function_not_orthogonal : ipv (fun _ => 1) (fun v : Pt 3 => vsq v - 1) ≠ 0 := by
  rw [ipv_one_vsq_sub_one]
  have := (gaussMass_pos (d := 3)).ne'
  norm_num
  exact this

lemma temperate_fixedU (a : Fin d ⊕ Bool) : (fixedU d a).HasTemperateGrowth := by
  rcases a with s | b
  · exact temperate_const_mul _ (temperate_coord s)
  · cases b
    · exact temperate_const_mul _ temperate_one
    · exact temperate_const_mul _ (temperate_vsq.sub (Function.HasTemperateGrowth.const _))

lemma ipv_smul_smul (a b : ℝ) (g h : Pt d → ℝ) :
    ipv (fun v => a * g v) (fun v => b * h v) = a * b * ipv g h := by
  rw [ipv_const_mul, ipv_comm, ipv_const_mul, ipv_comm]
  ring

/-- The function `v² - d`. -/
noncomputable def vsqSub (d : ℕ) (v : Pt d) : ℝ := vsq v - d

lemma temperate_vsqSub : (vsqSub d).HasTemperateGrowth :=
  temperate_vsq.sub (Function.HasTemperateGrowth.const _)

lemma ipv_vsqSub_right {g : Pt d → ℝ} (hg : g.HasTemperateGrowth) :
    ipv g (vsqSub d) = ipv g vsq - d * ipv g 𝟙 := by
  have e : vsqSub d = fun v => vsq v + (-(d : ℝ)) * 1 := by
    funext v; simp [vsqSub, sub_eq_add_neg]
  rw [e, ipv_add hg temperate_vsq (temperate_const_mul _ temperate_one), ipv_const_mul]
  ring

lemma ipv_one_vsqSub : ipv 𝟙 (vsqSub d) = 0 := by
  rw [ipv_vsqSub_right temperate_one, ipv_one_vsq, ipv_one_one]
  ring

lemma ipv_coord_vsqSub (s : Fin d) : ipv (fun v => v s) (vsqSub d) = 0 := by
  rw [ipv_vsqSub_right (temperate_coord s), ipv_coord_vsq, ipv_comm, ipv_one_coord]
  ring

lemma ipv_vsqSub_vsqSub : ipv (vsqSub d) (vsqSub d) = 2 * d * gaussMass d := by
  rw [ipv_vsqSub_right temperate_vsqSub, ipv_comm _ vsq, ipv_vsqSub_right temperate_vsq,
    ipv_vsq_vsq, ipv_comm vsq 𝟙, ipv_comm (vsqSub d) 𝟙, ipv_one_vsqSub, ipv_one_vsq]
  ring

/-- The fixed functions of arXiv 2206.09374, Sec. 3, with `v² - d` in place of `v² - 1`, are
orthonormal in every dimension `d ≥ 1`, as the method requires. -/
theorem fixedU_orth (hd : 0 < d) (a b : Fin d ⊕ Bool) :
    ipv (fixedU d a) (fixedU d b) = if a = b then 1 else 0 := by
  have hZ := gaussMass_pos (d := d)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  set A := 1 / Real.sqrt (gaussMass d) with hA
  set B := 1 / Real.sqrt (2 * d * gaussMass d) with hB
  have hA2 : A * A * gaussMass d = 1 := by
    rw [hA, div_mul_div_comm, Real.mul_self_sqrt hZ.le]
    field_simp
  have hB2 : B * B * (2 * d * gaussMass d) = 1 := by
    have : 0 < 2 * (d : ℝ) * gaussMass d := by positivity
    rw [hB, div_mul_div_comm, Real.mul_self_sqrt this.le]
    field_simp
  have e1 : ∀ s, fixedU d (.inl s) = fun v => A * v s := fun s => rfl
  have e2 : fixedU d (.inr false) = fun _ => A * 1 := rfl
  have e3 : fixedU d (.inr true) = fun v => B * vsqSub d v := rfl
  rcases a with r | a <;> rcases b with s | b
  · rw [e1, e1, ipv_smul_smul, ipv_coord_coord]
    by_cases h : r = s
    · simp [h, hA2]
    · simp [h]
  · cases b
    · rw [e1, e2, ipv_smul_smul, ipv_comm, ipv_one_coord]
      simp
    · rw [e1, e3, ipv_smul_smul, ipv_coord_vsqSub]
      simp
  · cases a
    · rw [e1, e2, ipv_smul_smul, ipv_one_coord]
      simp
    · rw [e1, e3, ipv_smul_smul, ipv_comm, ipv_coord_vsqSub]
      simp
  · cases a <;> cases b
    · rw [e2, ipv_smul_smul, ipv_one_one]
      simp [hA2]
    · rw [e2, e3, ipv_smul_smul, ipv_one_vsqSub]
      simp
    · rw [e2, e3, ipv_smul_smul, ipv_comm, ipv_one_vsqSub]
      simp
    · rw [e3, ipv_smul_smul, ipv_vsqSub_vsqSub]
      simp [hB2]

lemma sqrt_gaussMass_ne : Real.sqrt (gaussMass d) ≠ 0 :=
  (Real.sqrt_pos.2 gaussMass_pos).ne'

/-- `1 ∈ span U`. -/
lemma one_mem_fixedU : 𝟙 ∈ Submodule.span ℝ (range (fixedU d)) := by
  have e : 𝟙 = Real.sqrt (gaussMass d) • fixedU d (.inr false) := by
    funext v
    have := sqrt_gaussMass_ne (d := d)
    simp only [Pi.smul_apply, fixedU, smul_eq_mul]
    field_simp
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- `vₛ ∈ span U`. -/
lemma coord_mem_fixedU (s : Fin d) :
    (fun v : Pt d => v s) ∈ Submodule.span ℝ (range (fixedU d)) := by
  have e : (fun v : Pt d => v s) = Real.sqrt (gaussMass d) • fixedU d (.inl s) := by
    funext v
    have := sqrt_gaussMass_ne (d := d)
    simp only [Pi.smul_apply, fixedU, smul_eq_mul]
    field_simp
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- `v² ∈ span U`. -/
lemma vsq_mem_fixedU (hd : 0 < d) : vsq ∈ Submodule.span ℝ (range (fixedU d)) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hc : Real.sqrt (2 * d * gaussMass d) ≠ 0 :=
    (Real.sqrt_pos.2 (by have := gaussMass_pos (d := d); positivity)).ne'
  have e : vsq = Real.sqrt (2 * d * gaussMass d) • fixedU d (.inr true) +
      ((d : ℝ) • 𝟙) := by
    funext v
    simp only [Pi.add_apply, Pi.smul_apply, fixedU, smul_eq_mul]
    field_simp
    ring
  rw [e]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
    (Submodule.smul_mem _ _ one_mem_fixedU)

end FixedFunctions

/-! ### Non-vacuity -/

section Example

/-- A spatially constant state with the fixed functions only. -/
def constState (S : Matrix ((Fin d ⊕ Bool) ⊕ PEmpty.{1}) ((Fin d ⊕ Bool) ⊕ PEmpty.{1}) ℝ) :
    State (Fin d ⊕ Bool) PEmpty.{1} d :=
  ⟨fun _ _ => 1, S, fun q => q.elim⟩

variable (S : Matrix ((Fin d ⊕ Bool) ⊕ PEmpty.{1}) ((Fin d ⊕ Bool) ⊕ PEmpty.{1}) ℝ)

lemma constState_admissible (hd : 0 < d) : (constState S).Admissible (fixedU d) where
  temperate_U := temperate_fixedU
  temperate_W q := q.elim
  orth i j := by
    rcases i with a | q
    · rcases j with b | q
      · simpa [State.V, constState] using fixedU_orth hd a b
      · exact q.elim
    · exact q.elim
  diff_X _ := differentiable_const _

lemma constState_periodic (L : ℝ) : (constState S).Periodic L := fun _ => CP.const L 1

lemma rhs_constState (x v : Pt d) :
    rhsOf (fun _ _ _ => 0) ((constState S).f (fixedU d)) x v = 0 := by
  have e : (fun y => (constState S).f (fixedU d) y v) =
      fun _ => (constState S).f (fixedU d) x v := by
    funext y
    simp [State.f, lowRank, constState]
  simp [rhsOf, vlasovRHS, e, pd_const]

/-- The constant `L^{-d/2}`, the normalized constant function on the box. -/
noncomputable def constXt (L : ℝ) (d : ℕ) : Unit → Pt d → ℝ :=
  fun _ _ => 1 / Real.sqrt (L ^ d)

lemma ipx_constXt {L : ℝ} (hL : 0 < L) (a b : Unit) :
    ipx L (constXt L d a) (constXt L d b) = if a = b then 1 else 0 := by
  have hle : (0 : Pt d) ≤ fun _ => L := fun _ => hL.le
  have hvol : (volume (Icc (0 : Pt d) fun _ => L)).toReal = L ^ d := by
    rw [Real.volume_Icc_pi_toReal hle]
    simp
  have hpos : 0 < L ^ d := by positivity
  have e : 1 / Real.sqrt (L ^ d) * (1 / Real.sqrt (L ^ d)) * L ^ d = 1 := by
    rw [div_mul_div_comm, Real.mul_self_sqrt hpos.le]
    field_simp
  have h1 : ipx L (constXt L d a) (constXt L d b) =
      L ^ d * (1 / Real.sqrt (L ^ d) * (1 / Real.sqrt (L ^ d))) := by
    simp only [ipx, box, constXt]
    rw [setIntegral_const]
    simp only [Measure.real, hvol, smul_eq_mul]
  have hab : a = b := Subsingleton.elim a b
  rw [h1, ite_eq_left_iff.2 (fun hn => (hn hab).elim)]
  linarith

lemma const_mem_constXt {L : ℝ} (hL : 0 < L) (a : ℝ) :
    (fun _ => a) ∈ Submodule.span ℝ (range (constXt L d)) := by
  have hpos : 0 < L ^ d := by positivity
  have hc : Real.sqrt (L ^ d) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  have e : (fun _ : Pt d => a) = (a * Real.sqrt (L ^ d)) • constXt L d () := by
    funext x
    simp only [Pi.smul_apply, constXt, smul_eq_mul]
    field_simp
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- The empty family of functions. -/
def noFn (d : ℕ) : PEmpty.{1} → Pt d → ℝ := fun q => q.elim

/-- For a spatially constant state and `E = 0`, **Algorithm 1 can be carried out** with all
hypotheses satisfied. -/
noncomputable def constStep {L : ℝ} (hL : 0 < L) (hd : 0 < d) (τ : ℝ) :
    Alg1Step L τ (fun _ _ _ => 0) (fixedU d) (constState S) Unit PEmpty.{1} PEmpty.{1} PEmpty.{1}
    where
  Xt := constXt L d
  Xt_cont _ := continuous_const
  Xt_orth := ipx_constXt hL
  mem_X _ := const_mem_constXt hL 1
  mem_dX r i := by
    have : pd r ((constState S).X i) = fun _ => 0 := funext fun y => pd_const r 1 y
    rw [this]
    exact const_mem_constXt hL 0
  mem_K k := by
    have : kStep τ (fun _ _ _ => 0) (fixedU d) (constState S) k =
        fun _ => ∑ i, S i k := by
      funext x
      simp only [kStep, rhs_constState, mul_zero, integral_zero, add_zero]
      simp [coefK, constState]
    rw [this]
    exact const_mem_constXt hL _
  Wt := noFn d
  Wt_temperate q := q.elim
  Vt_orth l l' := by
    rcases l with a | q
    · rcases l' with b | q
      · simpa using fixedU_orth hd a b
      · exact q.elim
    · exact q.elim
  mem_L q := q.elim
  mem_W q := q.elim
  Xcons a := coefK (constXt L d) (sStep L τ (fun _ _ _ => 0) (fixedU d) (constState S)
    (constXt L d) (Sum.elim (fixedU d) (noFn d))) (.inl a)
  Scons := 1
  qr_cons a x := by simp [Matrix.one_apply]
  XremT := noFn d
  SremT q := q.elim
  qr_rem q := q.elim
  Uh q := q.elim
  Sh q := q.elim
  Wh q := q.elim
  Xnew := Sum.elim (fun a => coefK (constXt L d) (sStep L τ (fun _ _ _ => 0) (fixedU d)
    (constState S) (constXt L d) (Sum.elim (fixedU d) (noFn d))) (.inl a)) (noFn d)
  Rqr := 1
  qr_hat i x := by
    rcases i with a | q
    · simp [Matrix.one_apply]
    · exact q.elim

/-- The coefficient matrix of the Maxwellian `f = f₀ᵥ/‖1‖²`, of density `1`. -/
noncomputable def maxwellS (d : ℕ) :
    Matrix ((Fin d ⊕ Bool) ⊕ PEmpty.{1}) ((Fin d ⊕ Bool) ⊕ PEmpty.{1}) ℝ :=
  fun i j => if i = .inl (.inr false) ∧ j = .inl (.inr false) then
    1 / Real.sqrt (gaussMass d) else 0

lemma density_maxwell (hd : 0 < d) (x : Pt d) :
    density ((constState (maxwellS d)).f (fixedU d)) x = 1 := by
  have hs := constState_admissible (maxwellS d) hd
  have hZ := sqrt_gaussMass_ne (d := d)
  have e1 : ∀ a, ipv (fun _ : Pt d => (1 : ℝ)) (fixedU d a) =
      if a = .inr false then Real.sqrt (gaussMass d) else 0 := by
    intro a
    have h1 : (fun _ : Pt d => (1 : ℝ)) =
        fun v => Real.sqrt (gaussMass d) * fixedU d (.inr false) v := by
      funext v
      simp only [fixedU]
      field_simp
    rw [h1, ipv_comm, ipv_const_mul, ipv_comm, fixedU_orth hd]
    by_cases ha : a = .inr false
    · simp [ha]
    · have : ¬ (Sum.inr false = a) := fun e => ha e.symm
      simp [ha, this]
  have e2 : coefK (constState (maxwellS d)).X (constState (maxwellS d)).S
      (.inl (.inr false)) x = 1 / Real.sqrt (gaussMass d) := by
    simp [coefK, constState, maxwellS]
  rw [Alg1Step.density_eq_mom, State.f,
    mom_lowRank (Function.HasTemperateGrowth.const 1) hs.temperate_V, Fintype.sum_sum_type]
  have e3 : ∀ a, (constState (maxwellS d)).V (fixedU d) (.inl a) = fixedU d a := fun _ => rfl
  simp only [e3, e1, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, e2]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  field_simp

/-- **Non-vacuity** for arXiv 2206.09374: all hypotheses of Theorems 1–3, of the global
conservation laws and of the energy estimates hold together, for every `d ≥ 1`, `L > 0` and `τ`,
in the case of the Maxwellian `f = f₀ᵥ/‖1‖²` with density `1` and zero field (a stationary state of
the Vlasov–Poisson system, with `m = d + 2` fixed functions). -/
theorem alg1_hypotheses_hold {L : ℝ} (hL : 0 < L) (hd : 0 < d) (τ : ℝ) :
    ∃ (s : State (Fin d ⊕ Bool) PEmpty.{1} d)
      (h : Alg1Step L τ (fun _ _ _ => 0) (fixedU d) s Unit PEmpty.{1} PEmpty.{1} PEmpty.{1}),
      s.Admissible (fixedU d) ∧ s.Periodic L ∧
      (fun _ => (1 : ℝ)) ∈ Submodule.span ℝ (range (fixedU d)) ∧
      (∀ r : Fin d, (fun v : Pt d => v r) ∈ Submodule.span ℝ (range (fixedU d))) ∧
      vsq ∈ Submodule.span ℝ (range (fixedU d)) ∧
      (∀ x, density (s.f (fixedU d)) x = 1) ∧
      IsPoissonField L (density (s.f (fixedU d))) (fun _ _ => 0) (fun _ => 0) ∧
      IsPoissonField L (density (h.next.f (fixedU d))) (fun _ _ => 0) (fun _ => 0) := by
  have hs := constState_admissible (maxwellS d) hd
  have hρ := density_maxwell (d := d) hd
  have hP : ∀ ρ : Pt d → ℝ, (∀ x, ρ x = 1) →
      IsPoissonField L ρ (fun _ _ => 0) (fun _ => 0) := by
    intro ρ hρ
    refine ⟨contDiff_const, fun _ _ => rfl, fun s x => ?_, fun x => ?_⟩
    · simp [pd_const]
    · simp [pd_const, hρ]
  refine ⟨constState (maxwellS d), constStep (maxwellS d) hL hd τ, hs,
    constState_periodic _ L, one_mem_fixedU, coord_mem_fixedU, vsq_mem_fixedU hd, hρ,
    hP _ hρ, hP _ fun x => ?_⟩
  have h1 := (constStep (maxwellS d) hL hd τ).density_next hs one_mem_fixedU x
  have h2 : ∀ r, pd r (current ((constState (maxwellS d)).f (fixedU d)) r) x = 0 := by
    intro r
    have e : current ((constState (maxwellS d)).f (fixedU d)) r = fun _ =>
        current ((constState (maxwellS d)).f (fixedU d)) r x := by
      funext y
      simp [current, State.f, lowRank, constState]
    rw [e]
    exact pd_const r _ x
  simp only [h2, Finset.sum_const_zero, mul_zero, sub_zero, hρ] at h1
  exact h1

end Example

/-! ### The ansatz and the moments in the core kinetic vocabulary -/

section KineticCore

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **The ansatz through the core**: the low-rank function `f₀ᵥ ∑ᵢⱼ Xᵢ Sᵢⱼ Vⱼ` of this file is the
core `Kinetic.lowRankAnsatz` with the weight `f0`. -/
theorem lowRank_eq_lowRankAnsatz (X : ι → Pt d → ℝ) (S : Matrix ι κ ℝ) (V : κ → Pt d → ℝ) :
    lowRank X S V = Kinetic.lowRankAnsatz f0 X S V := rfl

/-- The low-rank function has separation rank at most the number of velocity basis functions. -/
theorem hasSepRankLE_lowRank (X : ι → Pt d → ℝ) (S : Matrix ι κ ℝ) (V : κ → Pt d → ℝ) :
    HasSepRankLE ℝ (lowRank X S V) (Fintype.card κ) :=
  Kinetic.hasSepRankLE_lowRankAnsatz f0 X S V

/-- **The moments through the core**: `mom u f` is the core `Kinetic.velocityMoment` of `f` for
the Lebesgue measure and the function `u`. -/
theorem mom_eq_velocityMoment (u : Pt d → ℝ) (f : Pt d → Pt d → ℝ) :
    mom u f = Kinetic.velocityMoment volume u f := rfl

/-- The density is the core velocity moment with the function `1`. -/
theorem density_eq_velocityMoment (f : Pt d → Pt d → ℝ) :
    density f = Kinetic.velocityMoment volume 1 f := by
  funext x
  simp [density, Kinetic.velocityMoment_apply]

/-- The component `s` of the current is the core velocity moment with the function `v ↦ vₛ`. -/
theorem current_eq_velocityMoment (f : Pt d → Pt d → ℝ) (s : Fin d) :
    current f s = Kinetic.velocityMoment volume (fun v => v s) f := rfl

/-- The component `(r, s)` of the stress is the core velocity moment with the function
`v ↦ vᵣ vₛ`. -/
theorem stress_eq_velocityMoment (f : Pt d → Pt d → ℝ) (r s : Fin d) :
    stress f r s = Kinetic.velocityMoment volume (fun v => v r * v s) f := rfl

/-- The heat flux is half the core velocity moment with the function `v ↦ vₛ v²`. -/
theorem heatFlux_eq_velocityMoment (f : Pt d → Pt d → ℝ) (s : Fin d) (x : Pt d) :
    heatFlux f s x = (1 / 2) * Kinetic.velocityMoment volume (fun v => v s * vsq v) f x := rfl

/-- The energy density is half the core velocity moment with the function `v²` plus the field
energy density. -/
theorem energyDensity_eq_velocityMoment (f : Pt d → Pt d → ℝ) (E : Fin d → Pt d → ℝ)
    (x : Pt d) :
    energyDensity f E x =
      (1 / 2) * Kinetic.velocityMoment volume vsq f x + (1 / 2) * ∑ s, E s x ^ 2 := rfl

/-- The bridges at nonzero data: the ansatz with `X = 2`, `S = (3)`, `V = 1` has the value `6` at
the origin, and the core moment of order zero of `f (x, v) = f₀ᵥ (v)` is the Gaussian mass, which
is positive. -/
example :
    lowRank (d := 1) (fun (_ : Fin 1) _ => 2) !![3] (fun (_ : Fin 1) _ => 1) 0 0 = 6 ∧
      Kinetic.velocityMoment volume 1 (fun _ v : Pt 1 => f0 v) 0 = gaussMass 1 ∧
      0 < gaussMass 1 := by
  refine ⟨?_, ?_, gaussMass_pos⟩
  · rw [lowRank_eq_lowRankAnsatz, Kinetic.lowRankAnsatz_apply]
    simp [f0, vsq]
    norm_num
  · rw [← density_eq_velocityMoment]
    rfl

end KineticCore

end LeanDLRA.Literature.P2206_09374
