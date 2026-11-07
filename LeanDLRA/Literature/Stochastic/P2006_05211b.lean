import Mathlib

/-!
# Results of arXiv 2006.05211: Stability of projector-splitting DLR for random parabolic PDEs

This module formalizes the algebraic core of two results of arXiv 2006.05211 (Kazashi, Nobile,
Vidličková), read verbatim from the arXiv v4 PDF.

* **Lemma 5.3** (the polarization identities used in the proof of Thm 5.6). For a symmetric
  bilinear form `B` on a real vector space (the paper uses `⟨·,·⟩_{L_det}` on `V_h ⊗ L²_ρ`),
  the three identities
  `⟨v, w−v⟩ = ½(⟨w,w⟩ − ⟨v,v⟩ − ⟨w−v,w−v⟩)`,
  `⟨w, w−v⟩ = ½(⟨w,w⟩ − ⟨v,v⟩ + ⟨w−v,w−v⟩)` and
  `⟨v, w+v⟩ = ½(⟨v,v⟩ − ⟨w,w⟩ + ⟨w+v,w+v⟩)`.
  Proved here for an abstract symmetric bilinear form.
* **The step `C_det ≥ 1/2` in Prop 6.1** (random heat equation). The paper's proof reads: the
  condition `ā(x) ≥ a_stoch(x,ξ)` with `a = ā + a_stoch` gives `ā/a ≥ 1/2`, i.e. `C_det ≥ 1/2`.
  Proved here pointwise: for real `ā, s` with `0 < ā + s` and `s ≤ ā`, `½ ≤ ā/(ā+s)`; and the
  weighted form `½ (ā+s) q ≤ ā q` for `q ≥ 0`, the pointwise version of
  `⟨u,u⟩_{L_det} ≥ ½⟨u,u⟩_L` with `q = |∇u|²`. The PDE integrals are not formalized:
  the statement is the pointwise inequality, whose integration over `D × Γ` gives
  `C_det ≥ 1/2` in the sense of (68).

**Not formalized.** Theorem 5.6 (stability of the semi-implicit scheme; part 2 with `C_det ≥ 1/2`
giving the unconditional bound (71)) and Proposition 6.1 as a whole. Their proofs use the
discrete variational formulation (74), which the proof of Thm 5.6 derives from Lemmas 4.3, 4.6,
4.8 and Thm 4.14 (rank-deficient steps included), together with the inverse inequality (22) and
the stochasticity bound (69). The energy estimate (76) is then algebra on top of (74). I did not
prove (74) and did not assume it or the energy estimate as hypotheses. Part 1 (the CFL-type
bound (70)) is not formalized either.

**Library definitions.** Lemma 5.3 is stated for an abstract symmetric bilinear form rather than
for the library's `IsOrthProj`/`ODESolution`/Galerkin objects, since the paper's `⟨·,·⟩_{L_det}`
is not a core definition. No core definition is redefined: the file uses only Mathlib
(`LinearMap`, `le_div_iff₀`).
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2006_05211

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **Lemma 5.3, first identity** (arXiv 2006.05211, used in the proof of Thm 5.6).
For a symmetric bilinear form `B`, `⟨v, w−v⟩ = ½(⟨w,w⟩ − ⟨v,v⟩ − ⟨w−v,w−v⟩)`. -/
theorem symm_polarization_one (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀ x y, B x y = B y x) (v w : E) :
    B v (w - v) = (1 / 2 : ℝ) * (B w w - B v v - B (w - v) (w - v)) := by
  have h := hB v w
  simp only [map_sub, LinearMap.sub_apply]
  linarith

/-- **Lemma 5.3, second identity** (arXiv 2006.05211):
`⟨w, w−v⟩ = ½(⟨w,w⟩ − ⟨v,v⟩ + ⟨w−v,w−v⟩)`. -/
theorem symm_polarization_two (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀ x y, B x y = B y x) (v w : E) :
    B w (w - v) = (1 / 2 : ℝ) * (B w w - B v v + B (w - v) (w - v)) := by
  have h := hB v w
  simp only [map_sub, LinearMap.sub_apply]
  linarith

/-- **Lemma 5.3, third identity** (arXiv 2006.05211):
`⟨v, w+v⟩ = ½(⟨v,v⟩ − ⟨w,w⟩ + ⟨w+v,w+v⟩)`. -/
theorem symm_polarization_three (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀ x y, B x y = B y x) (v w : E) :
    B v (w + v) = (1 / 2 : ℝ) * (B v v - B w w + B (w + v) (w + v)) := by
  have h := hB v w
  simp only [map_add, LinearMap.add_apply]
  linarith

/-- Non-vacuity of Lemma 5.3: multiplication on `ℝ` is a symmetric bilinear form, so the
hypotheses of `symm_polarization_one` are satisfiable. -/
example (v w : ℝ) : v * (w - v) = (1 / 2 : ℝ) * (w * w - v * v - (w - v) * (w - v)) :=
  symm_polarization_one (LinearMap.mul ℝ ℝ) (fun x y => mul_comm x y) v w

/-- **Prop 6.1, pointwise step** (arXiv 2006.05211, proof of Prop 6.1).
If `ā(x) ≥ a_stoch(x,ξ)` and `a = ā + a_stoch > 0`, then `½ ≤ ā/a`. The paper concludes
`C_det ≥ inf_{x,ξ} ā/a ≥ ½` from this. -/
theorem half_le_div_of_stoch_le {ā s : ℝ} (ha : 0 < ā + s) (hs : s ≤ ā) :
    (1 / 2 : ℝ) ≤ ā / (ā + s) := by
  rw [le_div_iff₀ ha]
  linarith

/-- **Prop 6.1, weighted form.** For `q ≥ 0` (for example `q = |∇u|²` at a point),
`½ (ā+s) q ≤ ā q` when `s ≤ ā`. Integrating in `x` and `ξ` gives
`⟨u,u⟩_{L_det} ≥ ½⟨u,u⟩_L`, the inequality (68) with `C_det = ½`. -/
theorem half_mul_le_of_stoch_le {ā s q : ℝ} (hs : s ≤ ā) (hq : 0 ≤ q) :
    (1 / 2 : ℝ) * (ā + s) * q ≤ ā * q := by
  nlinarith [mul_nonneg hq (sub_nonneg.mpr hs)]

/-- Non-vacuity of Prop 6.1: `ā = 2`, `s = 1` satisfy `s ≤ ā` and `0 < ā + s`. -/
example : (1 / 2 : ℝ) ≤ (2 : ℝ) / (2 + 1) :=
  half_le_div_of_stoch_le (by norm_num) (by norm_num)

end LeanDLRA.Literature.P2006_05211
