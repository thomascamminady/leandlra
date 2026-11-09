import LeanDLRA.Foundations.OneSided
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Normalized minimal-entropy closures with the Maxwell–Boltzmann entropy (arXiv 2106.09445)

Schotthöfer, Xiao, Frank and Hauck, *A structure-preserving surrogate model for the closure of
the moment system of the Boltzmann equation using convex deep neural networks* (arXiv
2106.09445).  The paper replaces the Newton solver of the minimal-entropy (`M_N`) closure by an
input convex neural network trained on normalized moments.  Its mathematical content is the
dual problem of the closure (Eqs. (12)–(14), recalled from the literature) and the two
normalization identities that let the network work on normalized, reduced moments: the zeroth
Lagrange multiplier is determined by the others (Eqs. (40)–(41)), and the multiplier of `u` is
the multiplier of `u / u₀` shifted in its zeroth entry by `ln u₀` (Eqs. (42)–(44): "`α` minimizes
the entropy functional for `u` iff it does for the normalized moment").  The neural network
results are empirical.

This module formalizes these statements on a velocity quadrature, which is how the paper's
kinetic scheme evaluates the velocity integral (Eq. (46)): `⟨g⟩ = ∑_q w_q g(v_q)` with positive
weights, a moment basis `m : V → ℝ^{n+1}` whose zeroth entry is constant, `m₀ ≡ c > 0` (the paper
uses monomials, `c = 1`; the general constant is needed for the spherical harmonics of the
follow-up papers arXiv 2402.16613 and 2404.14312, which import this module), and the
Maxwell–Boltzmann entropy, `η_*(y) = η_*'(y) = exp y` (Eqs. (28)–(31)).  The dual objective is
`ϕ(α; u) = ⟨exp(α · m)⟩ - α · u` (`dualObj`; the paper writes the equivalent maximization of
`-ϕ`), a multiplier of `u` is a minimizer of `ϕ(·; u)` (`IsMultiplier`) and the entropy is
`h(u) = -ϕ(α_u; u)` (Eq. (14)).

## Main results

* `isMultiplier_iff_moments_ansatz`: `α` is a multiplier of `u` iff the ansatz
  `f_α = exp(α · m)` reproduces the moments, `⟨m f_α⟩ = u` (the closure relation (12) and the
  first-order condition of (13); the converse direction uses only `exp y ≥ exp x + exp x (y - x)`).
* `ansatz_pos`: invariance of range, `f_α > 0` for every multiplier, in particular for the
  network prediction `α_θ` (Section III.A).
* `zerothMoment_eq_one_iff`, `alpha0_eq_neg_log_iff` (Eqs. (40)–(41)): the zeroth moment of the
  ansatz is one iff `α₀ = ϑ(α_r) = -(log c + log ⟨exp(α_r · m_r)⟩) / c`; for `c = 1` this is the
  printed `α₀ = -ln ⟨exp(α_r · m_r)⟩`.
* `dualObj_add_single`, `isMultiplier_add_single_iff`, `isMultiplier_add_single_log_iff`
  (Eqs. (42)–(44)): `ϕ(α + (ln u₀ / c) e₀; u) = u₀ ϕ(α; u / u₀) - u₀ ln u₀ / c`, hence `α` is a
  multiplier of `u / u₀` iff `α + (ln u₀ / c) e₀` is one of `u`.
* `entropy_scaling`, `entropy_scaling_one`: `h(u) = u₀ h(u / u₀) + u₀ ln u₀ / c`; for `c = 1` this
  is `h(u) = u₀ h(uⁿ) + u₀ ln u₀`, the scaling relation (48)–(51) of the companion paper
  arXiv 2201.10364.
* Connection to the core (not stated in the paper): `isOneSidedLipschitzField_dualFlow` shows that
  the gradient flow `α' = u - ⟨m exp(α · m)⟩` of the dual problem is one-sided Lipschitz with
  constant `0` (the moment map of the ansatz is monotone, i.e. `ϕ` is convex), so by the core
  stability theorem two dual gradient flows never separate (`dualFlow_norm_sub_le`).

Differences from the paper: the velocity integral is a quadrature with positive weights (the
paper's own discretization (46)); the zeroth basis function is any positive constant instead of
`1`; existence of the multiplier (realizability) is not discussed, statements are about given
multipliers.  The paper's claims on the neural network (entropy dissipation, hyperbolicity,
H-theorem of the closed system) are taken from the cited literature and are not formalized.
No claim of the paper was found to be false.
-/

open Finset
open scoped Matrix RealInnerProductSpace

namespace LeanDLRA.Literature.P2106_09445

open LeanDLRA

variable {V : Type*} [Fintype V] {n : ℕ}

/-! ### The closure on a velocity quadrature -/

/-- The velocity average `⟨g⟩ = ∑_q w_q g(v_q)` of a quadrature rule with weights `w`
(arXiv 2106.09445, Eq. (46)). -/
def avg (w : V → ℝ) (g : V → ℝ) : ℝ := ∑ v, w v * g v

/-- The Maxwell–Boltzmann entropy ansatz `f_α = η_*'(α · m) = exp(α · m)` (Eqs. (12), (31)). -/
noncomputable def ansatz (m : V → Fin (n + 1) → ℝ) (α : Fin (n + 1) → ℝ) : V → ℝ :=
  fun v => Real.exp (α ⬝ᵥ m v)

/-- The moment vector `⟨m f⟩` of a kinetic density `f` (Eq. (9)). -/
def moments (w : V → ℝ) (m : V → Fin (n + 1) → ℝ) (f : V → ℝ) : Fin (n + 1) → ℝ :=
  fun i => avg w fun v => m v i * f v

/-- The dual objective `ϕ(α; u) = ⟨η_*(α · m)⟩ - α · u = ⟨exp(α · m)⟩ - α · u` of the
minimal-entropy closure (Eq. (13) maximizes `-ϕ`). -/
noncomputable def dualObj (w : V → ℝ) (m : V → Fin (n + 1) → ℝ) (α u : Fin (n + 1) → ℝ) : ℝ :=
  avg w (ansatz m α) - α ⬝ᵥ u

/-- `α` is a **Lagrange multiplier** of the moment vector `u`: it minimizes the dual objective
`ϕ(·; u)` (Eq. (13)); the entropy is then `h(u) = -ϕ(α; u)` (Eq. (14)). -/
def IsMultiplier (w : V → ℝ) (m : V → Fin (n + 1) → ℝ) (u α : Fin (n + 1) → ℝ) : Prop :=
  ∀ β, dualObj w m α u ≤ dualObj w m β u

/-- The reduced basis `m_r = (m₁, …, m_n)` (Eq. (38) of arXiv 2201.10364; `m_#` in
arXiv 2404.14312). -/
def reducedBasis (m : V → Fin (n + 1) → ℝ) : V → Fin n → ℝ := fun v => Fin.tail (m v)

/-- The zeroth multiplier `ϑ(β) = -(log c + log ⟨exp(β · m_r)⟩) / c` that normalizes the zeroth
moment of the ansatz when `m₀ ≡ c` (Eq. (41) for `c = 1`; Eq. (40) of arXiv 2404.14312). -/
noncomputable def zerothMultiplier (w : V → ℝ) (c : ℝ) (mr : V → Fin n → ℝ) (β : Fin n → ℝ) :
    ℝ :=
  -(Real.log c + Real.log (avg w fun v => Real.exp (β ⬝ᵥ mr v))) / c

lemma avg_add (w f g : V → ℝ) : avg w (fun v => f v + g v) = avg w f + avg w g := by
  simp [avg, mul_add, sum_add_distrib]

lemma avg_const_mul (w g : V → ℝ) (a : ℝ) : avg w (fun v => a * g v) = a * avg w g := by
  simp [avg, mul_sum, mul_left_comm]

lemma avg_pos [Nonempty V] {w g : V → ℝ} (hw : ∀ v, 0 < w v) (hg : ∀ v, 0 < g v) :
    0 < avg w g :=
  sum_pos (fun v _ => mul_pos (hw v) (hg v)) univ_nonempty

lemma avg_nonneg {w g : V → ℝ} (hw : ∀ v, 0 ≤ w v) (hg : ∀ v, 0 ≤ g v) : 0 ≤ avg w g :=
  sum_nonneg fun v _ => mul_nonneg (hw v) (hg v)

omit [Fintype V] in
/-- **Invariance of range**: every ansatz `exp(α · m)`, in particular the neural network closure
`f_θ = exp(α_θ · m)`, is positive (Section III.A). -/
theorem ansatz_pos (m : V → Fin (n + 1) → ℝ) (α : Fin (n + 1) → ℝ) (v : V) :
    0 < ansatz m α v := Real.exp_pos _

/-- Splitting `α = (α₀, α_r)`: `α · m = α₀ m₀ + α_r · m_r`. -/
lemma cons_dotProduct (a : ℝ) (β : Fin n → ℝ) (x : Fin (n + 1) → ℝ) :
    (Fin.cons a β : Fin (n + 1) → ℝ) ⬝ᵥ x = a * x 0 + β ⬝ᵥ Fin.tail x := by
  simp [dotProduct, Fin.sum_univ_succ, Fin.tail]

/-! ### The multiplier is characterized by the moments of the ansatz -/

/-- The moments of the ansatz: the gradient of `⟨exp(α · m)⟩`. -/
lemma moments_ansatz_dotProduct (w : V → ℝ) (m : V → Fin (n + 1) → ℝ) (α d : Fin (n + 1) → ℝ) :
    d ⬝ᵥ moments w m (ansatz m α) = avg w fun v => (d ⬝ᵥ m v) * ansatz m α v := by
  simp only [dotProduct, moments, avg, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun v _ => ?_
  rw [sum_mul, mul_sum]
  exact sum_congr rfl fun i _ => by ring

/-- The derivative of `ϕ` along a coordinate direction. -/
lemma hasDerivAt_dualObj_line (w : V → ℝ) (m : V → Fin (n + 1) → ℝ) (α u : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (t : ℝ) :
    HasDerivAt (fun s => dualObj w m (α + s • Pi.single i 1) u)
      (moments w m (ansatz m (α + t • Pi.single i 1)) i - u i) t := by
  have hd : ∀ s : ℝ, (α + s • Pi.single i 1) ⬝ᵥ u = α ⬝ᵥ u + s * u i := by
    intro s; simp [add_dotProduct, smul_dotProduct, single_dotProduct]
  have he : ∀ (s : ℝ) (v : V), (α + s • Pi.single i 1) ⬝ᵥ m v = α ⬝ᵥ m v + s * m v i := by
    intro s v; simp [add_dotProduct, smul_dotProduct, single_dotProduct]
  simp only [dualObj, avg, ansatz, moments, hd, he]
  refine HasDerivAt.sub (HasDerivAt.fun_sum fun v _ => ?_) ?_
  · have := (((hasDerivAt_mul_const (m v i) (x := t)).const_add (α ⬝ᵥ m v)).exp).const_mul (w v)
    convert this using 1
    ring
  · simpa using ((hasDerivAt_id t).mul_const (u i)).const_add (α ⬝ᵥ u)

/-- **The multiplier reproduces the moments**: a minimizer `α` of `ϕ(·; u)` satisfies
`⟨m exp(α · m)⟩ = u`, so the closure `f_u = exp(α_u · m)` has the moments `u`
(Eq. (12); first-order condition of (13)). -/
theorem moments_ansatz_of_isMultiplier {w : V → ℝ} {m : V → Fin (n + 1) → ℝ}
    {u α : Fin (n + 1) → ℝ} (h : IsMultiplier w m u α) : moments w m (ansatz m α) = u := by
  funext i
  have hmin : IsLocalMin (fun s : ℝ => dualObj w m (α + s • Pi.single i 1) u) 0 :=
    Filter.Eventually.of_forall fun s => by simpa using h (α + s • Pi.single i 1)
  have := hmin.hasDerivAt_eq_zero (hasDerivAt_dualObj_line w m α u i 0)
  simpa [sub_eq_zero] using this

/-- **Sufficiency of the moment condition**: if the ansatz reproduces the moments,
`⟨m exp(α · m)⟩ = u`, then `α` minimizes `ϕ(·; u)` (convexity of `exp`). -/
theorem isMultiplier_of_moments_ansatz {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {m : V → Fin (n + 1) → ℝ} {u α : Fin (n + 1) → ℝ} (h : moments w m (ansatz m α) = u) :
    IsMultiplier w m u α := by
  intro β
  have key : avg w (ansatz m β) - avg w (ansatz m α) ≥ (β - α) ⬝ᵥ u := by
    rw [← h, moments_ansatz_dotProduct]
    simp only [avg, ← sum_sub_distrib]
    refine sum_le_sum fun v _ => ?_
    rw [← mul_sub]
    refine mul_le_mul_of_nonneg_left ?_ (hw v)
    have := Real.add_one_le_exp (β ⬝ᵥ m v - α ⬝ᵥ m v)
    have hx : Real.exp (β ⬝ᵥ m v) = Real.exp (α ⬝ᵥ m v) * Real.exp (β ⬝ᵥ m v - α ⬝ᵥ m v) := by
      rw [← Real.exp_add]; ring_nf
    simp only [ansatz, sub_dotProduct]
    rw [hx]
    nlinarith [Real.exp_pos (α ⬝ᵥ m v)]
  simp only [dualObj, sub_dotProduct] at key ⊢
  linarith

/-- **Characterization of the Lagrange multiplier** (Eqs. (12)–(13)): `α` minimizes the dual
objective `ϕ(·; u)` iff the ansatz `exp(α · m)` has the moments `u`. -/
theorem isMultiplier_iff_moments_ansatz {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {m : V → Fin (n + 1) → ℝ} {u α : Fin (n + 1) → ℝ} :
    IsMultiplier w m u α ↔ moments w m (ansatz m α) = u :=
  ⟨moments_ansatz_of_isMultiplier, isMultiplier_of_moments_ansatz hw⟩

/-! ### The zeroth multiplier (Eqs. (40)–(41)) -/

/-- The zeroth moment of the ansatz with `α = (a, β)` when `m₀ ≡ c`:
`⟨m₀ exp(α · m)⟩ = c exp(c a) ⟨exp(β · m_r)⟩`. -/
lemma moments_ansatz_zero {w : V → ℝ} {m : V → Fin (n + 1) → ℝ} {c : ℝ} (hm0 : ∀ v, m v 0 = c)
    (a : ℝ) (β : Fin n → ℝ) :
    moments w m (ansatz m (Fin.cons a β)) 0 =
      c * Real.exp (c * a) * avg w fun v => Real.exp (β ⬝ᵥ reducedBasis m v) := by
  simp only [moments, ansatz, cons_dotProduct, hm0, reducedBasis, avg, mul_sum]
  refine sum_congr rfl fun v _ => ?_
  rw [Real.exp_add, mul_comm a c]; ring

/-- **The zeroth multiplier is determined by the others** (Eqs. (40)–(41), for `m₀ ≡ c > 0`):
the zeroth moment of `exp(α · m)`, `α = (a, β)`, equals one iff `a = ϑ(β)`. -/
theorem zerothMoment_eq_one_iff [Nonempty V] {w : V → ℝ} (hw : ∀ v, 0 < w v)
    {m : V → Fin (n + 1) → ℝ} {c : ℝ} (hc : 0 < c) (hm0 : ∀ v, m v 0 = c) (a : ℝ)
    (β : Fin n → ℝ) :
    moments w m (ansatz m (Fin.cons a β)) 0 = 1 ↔
      a = zerothMultiplier w c (reducedBasis m) β := by
  rw [moments_ansatz_zero hm0, zerothMultiplier]
  set S := avg w fun v => Real.exp (β ⬝ᵥ reducedBasis m v)
  have hS : 0 < S := avg_pos hw fun v => Real.exp_pos _
  constructor
  · intro h
    have h' : Real.log (c * Real.exp (c * a) * S) = 0 := by rw [h, Real.log_one]
    rw [Real.log_mul (by positivity) hS.ne', Real.log_mul hc.ne' (Real.exp_pos _).ne',
      Real.log_exp] at h'
    field_simp
    linarith
  · intro h
    have hca : c * a = -(Real.log c + Real.log S) := by rw [h]; field_simp
    rw [hca, Real.exp_neg, Real.exp_add, Real.exp_log hc, Real.exp_log hS]
    field_simp

/-- **Eq. (41)** in the printed form (monomial basis, `m₀ = 1`): `⟨exp(α · m)⟩ = 1` iff
`α₀ = -ln ⟨exp(α_r · m_r)⟩`. -/
theorem alpha0_eq_neg_log_iff [Nonempty V] {w : V → ℝ} (hw : ∀ v, 0 < w v)
    {m : V → Fin (n + 1) → ℝ} (hm0 : ∀ v, m v 0 = 1) (α : Fin (n + 1) → ℝ) :
    avg w (ansatz m α) = 1 ↔
      α 0 = -Real.log (avg w fun v => Real.exp (Fin.tail α ⬝ᵥ reducedBasis m v)) := by
  have h := zerothMoment_eq_one_iff hw one_pos hm0 (α 0) (Fin.tail α)
  rw [Fin.cons_self_tail] at h
  have hmom : moments w m (ansatz m α) 0 = avg w (ansatz m α) := by
    simp [moments, hm0, avg]
  rw [hmom] at h
  rw [h, zerothMultiplier]
  simp

/-! ### Normalization of the moments (Eqs. (42)–(44)) -/

/-- **The dual objective under normalization**: with `u₀ > 0`, `m₀ ≡ c ≠ 0` and
`s = ln u₀ / c`, `ϕ(α + s e₀; u) = u₀ ϕ(α; u / u₀) - u₀ ln u₀ / c`. -/
theorem dualObj_add_single {w : V → ℝ} {m : V → Fin (n + 1) → ℝ} {c : ℝ} (hc : c ≠ 0)
    (hm0 : ∀ v, m v 0 = c) {u : Fin (n + 1) → ℝ} (hu : 0 < u 0) (α : Fin (n + 1) → ℝ) :
    dualObj w m (α + Pi.single 0 (Real.log (u 0) / c)) u =
      u 0 * dualObj w m α ((u 0)⁻¹ • u) - u 0 * Real.log (u 0) / c := by
  have hans : ansatz m (α + Pi.single 0 (Real.log (u 0) / c)) = fun v => u 0 * ansatz m α v := by
    funext v
    simp only [ansatz, add_dotProduct, single_dotProduct, hm0]
    rw [Real.exp_add, div_mul_cancel₀ _ hc, Real.exp_log hu]; ring
  rw [dualObj, dualObj, hans, avg_const_mul]
  simp only [add_dotProduct, single_dotProduct, dotProduct_smul, smul_eq_mul]
  field_simp
  ring

/-- **Normalization of the multiplier** (Eqs. (42)–(44), for `m₀ ≡ c ≠ 0`): `α` is a multiplier
of the normalized moment `u / u₀` iff `α + (ln u₀ / c) e₀` is a multiplier of `u`. -/
theorem isMultiplier_add_single_iff {w : V → ℝ} {m : V → Fin (n + 1) → ℝ} {c : ℝ} (hc : c ≠ 0)
    (hm0 : ∀ v, m v 0 = c) {u : Fin (n + 1) → ℝ} (hu : 0 < u 0) (α : Fin (n + 1) → ℝ) :
    IsMultiplier w m ((u 0)⁻¹ • u) α ↔
      IsMultiplier w m u (α + Pi.single 0 (Real.log (u 0) / c)) := by
  constructor
  · intro h β
    have hβ := h (β - Pi.single 0 (Real.log (u 0) / c))
    rw [dualObj_add_single hc hm0 hu]
    have := dualObj_add_single (w := w) hc hm0 hu (β - Pi.single 0 (Real.log (u 0) / c))
    rw [sub_add_cancel] at this
    rw [this]
    have := mul_le_mul_of_nonneg_left hβ hu.le
    linarith
  · intro h β
    have hβ := h (β + Pi.single 0 (Real.log (u 0) / c))
    rw [dualObj_add_single hc hm0 hu, dualObj_add_single hc hm0 hu] at hβ
    have : u 0 * dualObj w m α ((u 0)⁻¹ • u) ≤ u 0 * dualObj w m β ((u 0)⁻¹ • u) := by linarith
    exact le_of_mul_le_mul_left this hu

/-- **Eq. (44)** in the printed form (`m₀ = 1`): `α_θ(u) = α_θ(ū) + (ln u₀) e₀` minimizes the dual
objective for `u` iff `α_θ(ū)` minimizes it for the normalized moment `ū = u / u₀`. -/
theorem isMultiplier_add_single_log_iff {w : V → ℝ} {m : V → Fin (n + 1) → ℝ}
    (hm0 : ∀ v, m v 0 = 1) {u : Fin (n + 1) → ℝ} (hu : 0 < u 0) (α : Fin (n + 1) → ℝ) :
    IsMultiplier w m ((u 0)⁻¹ • u) α ↔ IsMultiplier w m u (α + Pi.single 0 (Real.log (u 0))) := by
  simpa using isMultiplier_add_single_iff (w := w) one_ne_zero hm0 hu α

/-- Two multipliers of the same moment give the same entropy value. -/
lemma IsMultiplier.dualObj_eq {w : V → ℝ} {m : V → Fin (n + 1) → ℝ} {u α β : Fin (n + 1) → ℝ}
    (hα : IsMultiplier w m u α) (hβ : IsMultiplier w m u β) :
    dualObj w m α u = dualObj w m β u :=
  le_antisymm (hα β) (hβ α)

/-- **Scaling of the entropy** (for `m₀ ≡ c ≠ 0`): if `α` is a multiplier of `u / u₀` and `α'` one
of `u`, then `h(u) = u₀ h(u / u₀) + u₀ ln u₀ / c` with `h = -ϕ(multiplier; ·)` (Eq. (14)). -/
theorem entropy_scaling {w : V → ℝ} {m : V → Fin (n + 1) → ℝ} {c : ℝ} (hc : c ≠ 0)
    (hm0 : ∀ v, m v 0 = c) {u α α' : Fin (n + 1) → ℝ} (hu : 0 < u 0)
    (hα : IsMultiplier w m ((u 0)⁻¹ • u) α) (hα' : IsMultiplier w m u α') :
    -dualObj w m α' u = u 0 * -dualObj w m α ((u 0)⁻¹ • u) + u 0 * Real.log (u 0) / c := by
  rw [hα'.dualObj_eq ((isMultiplier_add_single_iff hc hm0 hu α).1 hα),
    dualObj_add_single hc hm0 hu]
  ring

/-- **The scaling relation** `h(u) = u₀ h(uⁿ) + u₀ ln u₀` for the monomial basis (`m₀ = 1`),
Eqs. (48)–(51) of arXiv 2201.10364 (and the identity behind Eq. (44) here). -/
theorem entropy_scaling_one {w : V → ℝ} {m : V → Fin (n + 1) → ℝ} (hm0 : ∀ v, m v 0 = 1)
    {u α α' : Fin (n + 1) → ℝ} (hu : 0 < u 0) (hα : IsMultiplier w m ((u 0)⁻¹ • u) α)
    (hα' : IsMultiplier w m u α') :
    -dualObj w m α' u = u 0 * -dualObj w m α ((u 0)⁻¹ • u) + u 0 * Real.log (u 0) := by
  simpa using entropy_scaling one_ne_zero hm0 hu hα hα'

/-! ### Connection to the core: the dual gradient flow is dissipative -/

/-- The gradient flow `α' = -∇ϕ(α; u) = u - ⟨m exp(α · m)⟩` of the dual problem (13), as a vector
field on `ℝ^{n+1}` with the Euclidean inner product. -/
noncomputable def dualFlow (w : V → ℝ) (m : V → Fin (n + 1) → ℝ) (u : Fin (n + 1) → ℝ) :
    ℝ → EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) :=
  fun _ a => WithLp.toLp 2 (u - moments w m (ansatz m (WithLp.ofLp a)))

/-- **The dual gradient flow is one-sided Lipschitz with constant `0`** (core
`IsOneSidedLipschitzField`): the moment map `α ↦ ⟨m exp(α · m)⟩` of the ansatz is monotone,
`⟪G(α) - G(β), α - β⟫ = ⟨(exp(α · m) - exp(β · m)) ((α - β) · m)⟩ ≥ 0`. -/
theorem isOneSidedLipschitzField_dualFlow {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (m : V → Fin (n + 1) → ℝ) (u : Fin (n + 1) → ℝ) :
    IsOneSidedLipschitzField (dualFlow w m u) 0 := by
  intro t a b
  have hinner : ⟪dualFlow w m u t a - dualFlow w m u t b, a - b⟫ =
      -avg w fun v => ((WithLp.ofLp a - WithLp.ofLp b) ⬝ᵥ m v) *
        (ansatz m (WithLp.ofLp a) v - ansatz m (WithLp.ofLp b) v) := by
    have h1 : ⟪dualFlow w m u t a - dualFlow w m u t b, a - b⟫ =
        (WithLp.ofLp a - WithLp.ofLp b) ⬝ᵥ
          (moments w m (ansatz m (WithLp.ofLp b)) - moments w m (ansatz m (WithLp.ofLp a))) := by
      simp only [dualFlow, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, dotProduct]
      refine sum_congr rfl fun i _ => ?_
      simp only [PiLp.sub_apply, Pi.sub_apply]
      ring
    rw [h1, dotProduct_sub, moments_ansatz_dotProduct, moments_ansatz_dotProduct]
    simp only [avg, ← sum_sub_distrib, ← sum_neg_distrib]
    refine sum_congr rfl fun v _ => by ring
  rw [hinner, zero_mul, neg_nonpos]
  refine sum_nonneg fun v _ => mul_nonneg (hw v) ?_
  simp only [ansatz, sub_dotProduct]
  rcases le_total (WithLp.ofLp b ⬝ᵥ m v) (WithLp.ofLp a ⬝ᵥ m v) with h | h
  · exact mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 (Real.exp_le_exp.2 h))
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 h) (sub_nonpos.2 (Real.exp_le_exp.2 h))

/-- **Two dual gradient flows never separate** (core `norm_sub_le_of_oneSided_nonpos` applied to
`isOneSidedLipschitzField_dualFlow`): for solutions `α, β` of `α' = u - ⟨m exp(α · m)⟩` on
`[a, b]`, `‖α t - β t‖ ≤ ‖α a - β a‖`. -/
theorem dualFlow_norm_sub_le {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) {m : V → Fin (n + 1) → ℝ}
    {u : Fin (n + 1) → ℝ} {α β : ℝ → EuclideanSpace ℝ (Fin (n + 1))} {a b : ℝ}
    (hα : ODESolution (dualFlow w m u) α a b) (hβ : ODESolution (dualFlow w m u) β a b) :
    ∀ t ∈ Set.Icc a b, ‖α t - β t‖ ≤ ‖α a - β a‖ :=
  hα.norm_sub_le_of_oneSided_nonpos hβ (isOneSidedLipschitzField_dualFlow hw m u) le_rfl

/-- Non-vacuity: for one velocity with weight one and `m = (1)` (`n = 0`), `α = (log u₀)` is a
multiplier of every `u` with `u₀ > 0`. -/
example (u : Fin 1 → ℝ) (hu : 0 < u 0) :
    IsMultiplier (V := Unit) (fun _ => 1) (fun _ _ => 1) u (fun _ => Real.log (u 0)) := by
  refine isMultiplier_of_moments_ansatz (fun _ => zero_le_one) ?_
  funext i
  fin_cases i
  simp [moments, ansatz, avg, dotProduct, Real.exp_log hu]

end LeanDLRA.Literature.P2106_09445
