import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.ProjectorSplitting
import LeanDLRA.Integrators.Exactness
import LeanDLRA.Foundations.Gronwall

/-!
# DLRA in optimal control: gradient errors, adjoints and time reversibility

Core file for the use of dynamical low-rank approximation inside gradient-based optimisation
(optimal control, parameter identification, training of DLRA-constrained losses).

## Main results

* OP-TR-06 ([BaumannEtAl2025b] Sec. 5, 2610.29554 Sec. 7, 2409.14938 Sec. 5):
  `abs_reducedGrad_sub_le` (time-discrete reduced gradient error, bilinear in the state and adjoint
  errors), `abs_reducedGrad_sub_le_unif` (uniform form `‖B‖ (e_f G + F e_g)`),
  `abs_param_sub_le` (parameter error `C δ / m` from a strongly monotone optimality map) and
  `abs_rayleigh_sub_le` (eigenvalue error quadratic in the eigenvector error).
* OP-TR-19 ([EinkemmerMangott2026] Sec. 3.2): `inner_pos_of_norm_sub_lt` (a perturbed gradient with
  relative error `< 1` is still an ascent direction), `inner_comp_adjoint` (the adjoint of a
  Lie–Trotter composition is the reversed composition of the adjoints).
* OP-OT-21 ([CerutiLubich2022] Sec. 1, 2608.21545 Sec. 3): `hasDerivWithinAt_Iic_of_right`
  (a continuous right derivative is also a left derivative), `odeSolution_reverse` (the time
  reversal `s ↦ y(a + b - s)` of a solution solves the reversed ODE),
  `odeSolution_eq_reverse` (uniqueness), `IsKSLStep.reverse_eq` (running the KSL substeps backward
  retraces the forward step: the time-reversed projector-splitting step is an exact inverse), and
  `ksl_fullRank_exact` (at full rank, `P₁ = Q₀ = 1`, the KSL step reproduces the exact flow of an
  autonomous field, 2608.21545 Sec. 3.2).

Further results: `abs_reducedGrad_sub_le`, `abs_param_sub_le`, `abs_rayleigh_sub_le` and
`IsKSLStep.reverse_eq`.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace

namespace LeanDLRA.AdjointDLRA

open LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### OP-TR-06: gradient and parameter errors of DLRA-based optimisation -/

/-- Bilinear perturbation bound for one time level: `|⟪B f, g⟫ - ⟪B fr, gr⟫| ≤
(‖f - fr‖ ‖gr‖ + ‖f‖ ‖g - gr‖) ‖B‖`. -/
theorem abs_inner_sub_le (B : E →L[ℝ] E) (f fr g gr : E) :
    |⟪B f, g⟫ - ⟪B fr, gr⟫| ≤ (‖f - fr‖ * ‖gr‖ + ‖f‖ * ‖g - gr‖) * ‖B‖ := by
  have hsplit : ⟪B f, g⟫ - ⟪B fr, gr⟫ = ⟪B f, g - gr⟫ + ⟪B (f - fr), gr⟫ := by
    rw [map_sub, inner_sub_right, inner_sub_left]; ring
  rw [hsplit]
  have h1 : |⟪B f, g - gr⟫| ≤ ‖f‖ * ‖g - gr‖ * ‖B‖ := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    have := B.le_opNorm f
    nlinarith [norm_nonneg (g - gr), norm_nonneg f, norm_nonneg B]
  have h2 : |⟪B (f - fr), gr⟫| ≤ ‖f - fr‖ * ‖gr‖ * ‖B‖ := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    have := B.le_opNorm (f - fr)
    nlinarith [norm_nonneg gr, norm_nonneg (f - fr), norm_nonneg B]
  calc |⟪B f, g - gr⟫ + ⟪B (f - fr), gr⟫| ≤ |⟪B f, g - gr⟫| + |⟪B (f - fr), gr⟫| :=
        abs_add_le _ _
    _ ≤ _ := by nlinarith

/-- **OP-TR-06 (reduced gradient, time-discrete state/adjoint).**  With
`∂ᵢJ = (1/(N+1)) ∑ₙ ⟪Bᵢ fⁿ, gⁿ⟫` (state `fⁿ`, adjoint `gⁿ`) and its DLRA counterpart,
`|∂ᵢJ - ∂ᵢJ_r| ≤ ∑ₙ (‖fⁿ - f_rⁿ‖ ‖g_rⁿ‖ + ‖fⁿ‖ ‖gⁿ - g_rⁿ‖) ‖Bᵢ‖ / (N+1)`.  The adjoint
representation of the gradient is the hypothesis built into the formula; inserting robust global
error bounds of state and adjoint (`bug_global_error_le`) gives `O(ε + h + nϑ)`, see
`abs_reducedGrad_sub_le_unif`. -/
theorem abs_reducedGrad_sub_le (N : ℕ) (B : E →L[ℝ] E) (f fr gg gr : ℕ → E) :
    |(∑ k ∈ range (N + 1), ⟪B (f k), gg k⟫) / (N + 1) -
        (∑ k ∈ range (N + 1), ⟪B (fr k), gr k⟫) / (N + 1)| ≤
      (∑ k ∈ range (N + 1), (‖f k - fr k‖ * ‖gr k‖ + ‖f k‖ * ‖gg k - gr k‖)) * ‖B‖ /
        (N + 1) := by
  have hN : (0 : ℝ) < N + 1 := by positivity
  rw [← sub_div, abs_div, abs_of_pos hN, ← Finset.sum_sub_distrib, Finset.sum_mul]
  gcongr
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun k _ => abs_inner_sub_le B _ _ _ _)

/-- **OP-TR-06, uniform form.**  If at every time level the state error is `≤ e_f`, the adjoint
error is `≤ e_g`, the DLRA adjoint is bounded by `G` and the state by `F`, then the reduced
gradient error is at most `‖B‖ (e_f G + F e_g)`.  With `e_f, e_g = O(ε + h + nϑ)` from the robust
BUG/KSL global error theorems this is the `O(ε + h + nϑ)` gradient error claimed in OP-TR-06; no
dependence on small singular values enters. -/
theorem abs_reducedGrad_sub_le_unif (N : ℕ) (B : E →L[ℝ] E) (f fr gg gr : ℕ → E)
    {ef eg G Fb : ℝ} (hef : ∀ k ≤ N, ‖f k - fr k‖ ≤ ef) (heg : ∀ k ≤ N, ‖gg k - gr k‖ ≤ eg)
    (hG : ∀ k ≤ N, ‖gr k‖ ≤ G) (hF : ∀ k ≤ N, ‖f k‖ ≤ Fb) :
    |(∑ k ∈ range (N + 1), ⟪B (f k), gg k⟫) / (N + 1) -
        (∑ k ∈ range (N + 1), ⟪B (fr k), gr k⟫) / (N + 1)| ≤ (ef * G + Fb * eg) * ‖B‖ := by
  refine (abs_reducedGrad_sub_le N B f fr gg gr).trans ?_
  have hN : (0 : ℝ) < N + 1 := by positivity
  rw [div_le_iff₀ hN]
  have hsum : ∑ k ∈ range (N + 1), (‖f k - fr k‖ * ‖gr k‖ + ‖f k‖ * ‖gg k - gr k‖) ≤
      ∑ _k ∈ range (N + 1), (ef * G + Fb * eg) := by
    refine Finset.sum_le_sum fun k hk => ?_
    have hk' : k ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have h1 := hef k hk'
    have h2 := heg k hk'
    have h3 := hG k hk'
    have h4 := hF k hk'
    have h0f := norm_nonneg (f k)
    have h0g := norm_nonneg (gr k)
    have h0e := norm_nonneg (f k - fr k)
    have h0e' := norm_nonneg (gg k - gr k)
    nlinarith [mul_le_mul h1 h3 h0g (h0e.trans h1), mul_le_mul h4 h2 h0e' (h0f.trans h4)]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  push_cast at hsum
  have hB := norm_nonneg B
  nlinarith [mul_le_mul_of_nonneg_right hsum hB]

omit [InnerProductSpace ℝ E] in
/-- **OP-TR-06 (parameter error).**  If the exact optimality map `k` has derivative `≥ m > 0`,
`k(α⋆) = 0`, `k_r(α_r⋆) = 0` and `|k_r - k| ≤ C ‖φ_r - φ‖ ≤ C δ` (the reduced optimality map
differs from the exact one by at most `C` times the DLRA error of the underlying state `φ`), then
`|α_r⋆ - α⋆| ≤ C δ / m`. -/
theorem abs_param_sub_le {k k' kr : ℝ → ℝ} {φ φr : ℝ → E} {m C δ αs αr : ℝ} (hm : 0 < m)
    (hk : ∀ a, HasDerivAt k (k' a) a) (hk' : ∀ a, m ≤ k' a) (hC : 0 ≤ C)
    (hkr : ∀ a, |kr a - k a| ≤ C * ‖φr a - φ a‖) (hφ : ∀ a, ‖φr a - φ a‖ ≤ δ) (h1 : k αs = 0)
    (h2 : kr αr = 0) : |αr - αs| ≤ C * δ / m := by
  have hmono : ∀ x y, x ≤ y → m * (y - x) ≤ k y - k x := by
    intro x y hxy
    rcases hxy.eq_or_lt with rfl | hlt
    · simp
    obtain ⟨c, -, hc⟩ := exists_hasDerivAt_eq_slope k k' hlt
      (fun z _ => (hk z).continuousAt.continuousWithinAt) (fun z _ => hk z)
    have hpos : 0 < y - x := sub_pos.2 hlt
    have : k y - k x = k' c * (y - x) := by rw [hc]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right (hk' c) hpos.le
  have hkα : |k αr| ≤ C * δ := by
    have := hkr αr
    rw [h2, zero_sub, abs_neg] at this
    exact this.trans (mul_le_mul_of_nonneg_left (hφ αr) hC)
  rw [le_div_iff₀ hm]
  rcases le_total αs αr with h | h
  · have := hmono αs αr h
    rw [h1, sub_zero] at this
    rw [abs_of_nonneg (sub_nonneg.2 h)]
    nlinarith [le_abs_self (k αr)]
  · have := hmono αr αs h
    rw [h1, zero_sub] at this
    rw [abs_of_nonpos (sub_nonpos.2 h)]
    nlinarith [neg_abs_le (k αr)]

/-- **OP-TR-06 (Rayleigh quotient).**  For a symmetric operator with unit eigenvector `v`
(`T v = μ v`) and unit `w`, `|⟪T w, w⟫ - μ| ≤ ‖T - μ I‖ ‖w - v‖²`: eigenvalue errors of a
reduced (e.g. DLRA-computed) eigenvector are quadratic in the eigenvector error.  The
normalisation `‖v‖ = 1` is not needed (only `‖w‖ = 1` is). -/
theorem abs_rayleigh_sub_le (T : E →L[ℝ] E) (hT : ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫) {v w : E} {μ : ℝ}
    (hv : T v = μ • v) (hw1 : ‖w‖ = 1) :
    |⟪T w, w⟫ - μ| ≤ ‖T - μ • (1 : E →L[ℝ] E)‖ * ‖w - v‖ ^ 2 := by
  set A : E →L[ℝ] E := T - μ • (1 : E →L[ℝ] E) with hA
  have hAx : ∀ x, A x = T x - μ • x := fun x => by simp [hA]
  have hAv : A v = 0 := by rw [hAx, hv, sub_self]
  have hAsymm : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫ := fun x y => by
    rw [hAx, hAx, inner_sub_left, inner_sub_right, hT, real_inner_smul_left,
      real_inner_smul_right]
  set d := w - v with hd
  have hw : w = v + d := by rw [hd]; abel
  have hww : ⟪w, w⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hw1]; norm_num
  have key : ⟪T w, w⟫ - μ = ⟪A d, d⟫ := by
    have e1 : ⟪T w, w⟫ - μ = ⟪A w, w⟫ := by
      rw [hAx, inner_sub_left, real_inner_smul_left, hww, mul_one]
    rw [e1, hw, map_add, hAv, zero_add, inner_add_right, hAsymm d v, hAv, inner_zero_right,
      zero_add]
  rw [key]
  refine (abs_real_inner_le_norm _ _).trans ?_
  have := A.le_opNorm d
  nlinarith [norm_nonneg d]

/-! ### OP-TR-19: reliability of perturbed gradients -/

/-- **OP-TR-19 (b): a perturbed gradient with relative error `< 1` is an ascent direction.**
If `‖ĝ - g‖ < ‖g‖` then `⟪ĝ, g⟫ > 0`, so `-ĝ` is still a descent direction of the loss.  Combined
with an adjoint-gradient error bound `‖ĝ - g‖ ≤ C_adj sup ‖e‖` (e.g. `abs_reducedGrad_sub_le`)
this gives the rank- and checkpoint-dependent guarantee of OP-TR-19 (b). -/
theorem inner_pos_of_norm_sub_lt {g gh : E} (h : ‖gh - g‖ < ‖g‖) : 0 < ⟪gh, g⟫ := by
  have h2 : ‖gh - g‖ ^ 2 < ‖g‖ ^ 2 := by
    have := norm_nonneg (gh - g)
    nlinarith
  rw [norm_sub_sq_real] at h2
  nlinarith [sq_nonneg ‖gh‖]

/-- **OP-TR-19 (adjoint of a Lie–Trotter composition; 2608.21545 Sec. 3).**  If `K*`, `S*`, `L*`
are adjoints of the (linearised) substep maps `K`, `S`, `L`, then the adjoint of the composition
`L ∘ S ∘ K` is `K* ∘ S* ∘ L*`: the discrete adjoint of a splitting step runs the adjoint substeps
in reverse order. -/
theorem inner_comp_adjoint {K S L Ks Ss Ls : E → E} (hK : ∀ x y, ⟪K x, y⟫ = ⟪x, Ks y⟫)
    (hS : ∀ x y, ⟪S x, y⟫ = ⟪x, Ss y⟫) (hL : ∀ x y, ⟪L x, y⟫ = ⟪x, Ls y⟫) (x y : E) :
    ⟪L (S (K x)), y⟫ = ⟪x, Ks (Ss (Ls y))⟫ := by
  rw [hL, hS, hK]

/-! ### OP-OT-21: time reversal of substeps and reversibility of projector splitting -/

section Reversal

variable {f g : ℝ → E → E} {y z : ℝ → E} {a b : ℝ}

/-- A function that is continuous on `[a, b]` and has a right derivative `g x` on `[a, b)` that
is continuous (within `[a, b]`) at `t ∈ (a, b]` also has the *left* derivative `g t` at `t`.
(Mean value inequality applied to `x ↦ f x - x • g t` on `[y, t]`.) -/
theorem hasDerivWithinAt_Iic_of_right {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {f : ℝ → E'} {g : ℝ → E'} {t : ℝ} (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (g x) (Ici x) x)
    (hg : ContinuousWithinAt g (Icc a b) t) (ht : t ∈ Ioc a b) :
    HasDerivWithinAt f (g t) (Iic t) t := by
  rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousWithinAt_iff.1 hg c hc
  have hlt : max a (t - δ) < t := max_lt ht.1 (by linarith)
  filter_upwards [Ioc_mem_nhdsLE hlt] with y hy
  have hay : a < y := (le_max_left _ _).trans_lt hy.1
  have hyδ : t - δ < y := (le_max_right _ _).trans_lt hy.1
  set φ : ℝ → E' := fun x => f x - x • g t with hφ
  have hcont : ContinuousOn φ (Icc y t) :=
    (hf.mono (Icc_subset_Icc hay.le ht.2)).sub
      ((continuous_id.smul continuous_const).continuousOn)
  have hderiv : ∀ x ∈ Ico y t, HasDerivWithinAt φ (g x - g t) (Ici x) x := by
    intro x hx
    have h1 := hf' x ⟨hay.le.trans hx.1, hx.2.trans_le ht.2⟩
    have h2 := ((hasDerivWithinAt_id x (Ici x)).smul_const (g t))
    have h3 := h1.sub h2
    rw [one_smul] at h3
    exact h3
  have hbound : ∀ x ∈ Ico y t, ‖g x - g t‖ ≤ c := by
    intro x hx
    have hxI : x ∈ Icc a b := ⟨hay.le.trans hx.1, hx.2.le.trans ht.2⟩
    have hd : dist x t < δ := by
      rw [Real.dist_eq, abs_of_neg (by linarith [hx.2])]; linarith [hx.1]
    exact (dist_eq_norm (g x) (g t) ▸ hδg hxI hd).le
  have hmvt := norm_image_sub_le_of_norm_deriv_right_le_segment hcont hderiv hbound t
    ⟨hy.2, le_rfl⟩
  have heq : f y - f t - (y - t) • g t = -(φ t - φ y) := by
    simp only [hφ, sub_smul]; abel
  rw [heq, norm_neg, Real.norm_eq_abs, abs_of_nonpos (by linarith [hy.2])]
  linarith

/-- **Time reversal of an ODE solution.**  If `y` solves `y' = f(t, y)` on `[a, b]` and the field
is jointly continuous, then `s ↦ y(a + b - s)` solves the reversed ODE
`z' = -f(a + b - s, z)` on `[a, b]` (in the right-derivative sense of `ODESolution`). -/
theorem odeSolution_reverse (hf : Continuous (Function.uncurry f)) (hy : ODESolution f y a b) :
    ODESolution (fun s x => -f (a + b - s) x) (fun s => y (a + b - s)) a b := by
  have hmaps : MapsTo (fun s => a + b - s) (Icc a b) (Icc a b) :=
    fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩
  refine ⟨hy.cont.comp (by fun_prop) hmaps, fun s hs => ?_⟩
  have ht : a + b - s ∈ Ioc a b := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hg : ContinuousWithinAt (fun x => f x (y x)) (Icc a b) (a + b - s) := by
    have hc : ContinuousWithinAt (fun x => (x, y x)) (Icc a b) (a + b - s) :=
      continuousWithinAt_id.prodMk (hy.cont _ (Ioc_subset_Icc_self ht))
    exact hf.continuousAt.comp_continuousWithinAt hc
  have H := hasDerivWithinAt_Iic_of_right hy.cont hy.deriv hg ht
  have hh : HasDerivWithinAt (fun s => a + b - s) (-1) (Ici s) s := by
    simpa using ((hasDerivAt_id s).const_sub (a + b)).hasDerivWithinAt
  have hmaps' : MapsTo (fun s => a + b - s) (Ici s) (Iic (a + b - s)) :=
    fun x hx => by simp only [Set.mem_Iic]; linarith [Set.mem_Ici.1 hx]
  have := H.scomp s hh hmaps'
  simpa [Function.comp_def] using this

omit [InnerProductSpace ℝ E] in
/-- A field agreeing with `-f(a + b - s, ·)` is `max L 0`-Lipschitz if `f` is `L`-Lipschitz. -/
lemma isLipschitzField_reverse {L : ℝ} (hL : IsLipschitzField f L)
    (hgf : ∀ s x, g s x = -f (a + b - s) x) : IsLipschitzField g (max L 0) := fun t x x' => by
  rw [hgf, hgf, neg_sub_neg, norm_sub_rev]
  exact (hL _ _ _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

/-- **Uniqueness of the time-reversed solution.**  If `y` solves `y' = f(t, y)` on `[a, b]`
(jointly continuous, Lipschitz field) and `z` solves the reversed ODE `z' = -f(a + b - s, z)`
from the end value `z a = y b`, then `z s = y(a + b - s)` on `[a, b]`: the backward run retraces
the forward trajectory exactly, in particular `z b = y a`. -/
theorem odeSolution_eq_reverse {L : ℝ} (hf : Continuous (Function.uncurry f))
    (hL : IsLipschitzField f L) (hgf : ∀ s x, g s x = -f (a + b - s) x)
    (hy : ODESolution f y a b) (hz : ODESolution g z a b) (h0 : z a = y b) :
    ∀ s ∈ Icc a b, z s = y (a + b - s) := by
  have hr := odeSolution_reverse hf hy
  have hr' : ODESolution g (fun s => y (a + b - s)) a b :=
    ⟨hr.cont, fun t ht => by rw [hgf]; exact hr.deriv t ht⟩
  intro s hs
  have := ODESolution.norm_sub_le_exp (isLipschitzField_reverse hL hgf) (le_max_right _ _) hz hr'
    s hs
  have hab : a + b - a = b := by ring
  rw [hab, h0, sub_self, norm_zero, mul_zero] at this
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

/-- Congruence of `ODESolution` in the field. -/
lemma odeSolution_congr_field (hfg : ∀ t x, f t x = g t x) (hy : ODESolution f y a b) :
    ODESolution g y a b :=
  ⟨hy.cont, fun t ht => by rw [← hfg]; exact hy.deriv t ht⟩

end Reversal

/-- **OP-OT-21 (ii): the KSL step is reversed exactly by its backward substeps** ([CerutiLubich2022]
Sec. 1; 2608.21545 Sec. 3).  Running the substeps of a KSL step backward in reverse order (L-step,
forward S-step, K-step, each with the time-reversed field and the *same* projectors) returns
exactly the starting value `Y₀`.  This is the abstract (fixed-projector) form: in the matrix
algorithm the same projectors are recovered from rank-`r` intermediate states (equal ranges give
equal projectors, `Orthonormal.lean`), which is exactly where rank deficiency breaks reversibility
(2608.21545 Thm 3.2; not formalised here). -/
theorem IsKSLStep.reverse_eq {F : ℝ → E → E} {ε L : ℝ} {P₁ Q₀ : E →L[ℝ] E} {t₀ t₁ : ℝ} {Y₀ : E}
    {YK YS YL : ℝ → E} (hs : IsKSLStep F ε P₁ Q₀ t₀ t₁ Y₀ YK YS YL) (h01 : t₀ ≤ t₁)
    (hF : IsLipschitzField F L) (hFc : Continuous (Function.uncurry F)) {ZL ZS ZK : ℝ → E}
    (hZL : ODESolution (fun s x => -P₁ (F (t₀ + t₁ - s) x)) ZL t₀ t₁) (hZL₀ : ZL t₀ = YL t₁)
    (hZS : ODESolution (fun s x => P₁ (Q₀ (F (t₀ + t₁ - s) x))) ZS t₀ t₁)
    (hZS₀ : ZS t₀ = ZL t₁)
    (hZK : ODESolution (fun s x => -Q₀ (F (t₀ + t₁ - s) x)) ZK t₀ t₁) (hZK₀ : ZK t₀ = ZS t₁) :
    ZK t₁ = Y₀ := by
  have hP := hs.projP₁
  have hQ := hs.projQ₀
  have h1 : t₁ ∈ Icc t₀ t₁ := ⟨h01, le_rfl⟩
  have hts : t₀ + t₁ - t₁ = t₀ := by ring
  -- continuity of the projected fields
  have cP : Continuous (Function.uncurry fun t x => P₁ (F t x)) := P₁.continuous.comp hFc
  have cQ : Continuous (Function.uncurry fun t x => Q₀ (F t x)) := Q₀.continuous.comp hFc
  have cS : Continuous (Function.uncurry fun t x => -P₁ (Q₀ (F t x))) :=
    (P₁.continuous.comp (Q₀.continuous.comp hFc)).neg
  have lP : IsLipschitzField (fun t x => P₁ (F t x)) L := hF.comp_contraction P₁ hP.norm_le
  have lQ : IsLipschitzField (fun t x => Q₀ (F t x)) L := hF.comp_contraction Q₀ hQ.norm_le
  have lS : IsLipschitzField (fun t x => -P₁ (Q₀ (F t x))) L := fun t x x' => by
    rw [neg_sub_neg, norm_sub_rev]
    exact (lQ.comp_contraction P₁ hP.norm_le) t x x'
  have eL := odeSolution_eq_reverse cP lP (fun s x => rfl) hs.lSol hZL hZL₀ t₁ h1
  rw [hts, hs.lStart] at eL
  have eS := odeSolution_eq_reverse cS lS (fun s x => by simp) hs.sSol hZS (hZS₀.trans eL) t₁ h1
  rw [hts, hs.sStart] at eS
  have eK := odeSolution_eq_reverse cQ lQ (fun s x => rfl) hs.kSol hZK (hZK₀.trans eS) t₁ h1
  rw [hts, hs.kStart] at eK
  exact eK

/-- **OP-OT-21 / 2608.21545 Sec. 3.2: at full rank KSL is exact for autonomous fields.**  With
`P₁ = Q₀ = 1` (full-rank bases), the K-step is the exact flow, the backward S-step (with the
autonomous field `-G`) retraces it back to `Y₀` (`odeSolution_eq_reverse`), and the L-step is the
exact flow again, so `YL t₁ = A t₁` for the exact solution `A`.  For non-autonomous fields the
backward S-step is integrated in forward time and this cancellation is not available. -/
theorem ksl_fullRank_exact {G : E → E} {L ε : ℝ} (hG : IsLipschitzField (fun _ => G) L)
    (hGc : Continuous G) {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁) {Y₀ : E} {YK YS YL A : ℝ → E}
    (hs : IsKSLStep (fun _ => G) ε 1 1 t₀ t₁ Y₀ YK YS YL)
    (hA : ODESolution (fun _ => G) A t₀ t₁) (hA₀ : A t₀ = Y₀) : YL t₁ = A t₁ := by
  have h1 : t₁ ∈ Icc t₀ t₁ := ⟨h01, le_rfl⟩
  have hL0 : 0 ≤ max L 0 := le_max_right _ _
  have hG' : IsLipschitzField (fun _ => G) (max L 0) := fun t x x' =>
    (hG t x x').trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hK : ODESolution (fun _ => G) YK t₀ t₁ :=
    odeSolution_congr_field (fun _ _ => by simp) hs.kSol
  have hL : ODESolution (fun _ => G) YL t₀ t₁ :=
    odeSolution_congr_field (fun _ _ => by simp) hs.lSol
  have hS : ODESolution (fun _ x => -G x) YS t₀ t₁ :=
    odeSolution_congr_field (fun _ _ => by simp) hs.sSol
  have hGc' : Continuous (Function.uncurry fun (_ : ℝ) => G) := hGc.comp continuous_snd
  have eS := odeSolution_eq_reverse hGc' hG (fun _ _ => rfl) hK hS hs.sStart t₁ h1
  have hts : t₀ + t₁ - t₁ = t₀ := by ring
  rw [hts, hs.kStart] at eS
  have := ODESolution.norm_sub_le_exp hG' hL0 hL hA t₁ h1
  rw [hs.lStart, eS, hA₀, sub_self, norm_zero, mul_zero] at this
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

end LeanDLRA.AdjointDLRA
