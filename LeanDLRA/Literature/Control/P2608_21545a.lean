import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Control.AdjointDLRA
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Foundations.Projector

/-!
# Results of arXiv 2608.21545: Time-reversible DLRA for memory-efficient adjoints

Formalises two results of arXiv 2608.21545 (Einkemmer–Mangott) in the abstract setting of an
inner product space `E`.

* `backward_cancel_of_proj_exact` (Lemma 3.1 as printed, Sec. 3.1, p. 9). Let `z` solve the
  projected backward flow `z' = -P G(t, z)` of Eq. (20) (the paper's `K^S`), with `P` an
  orthogonal projector (`P = P_{X¹}`), and `w` the unprojected backward flow `w' = -G(t, w)` (the
  backward K-step, Eq. (17K) with a minus sign), both written in the reversed time `s = Δt - t`,
  with the same initial value. If the projection in (20) is exact along `z`, i.e.
  `G(t, z) ∈ span X¹ = range P` for all `t ∈ [0, Δt]`, then `z = w` on `[0, Δt]` (the backward
  K-step cancels the S-step).
* `backward_cancel_iff` (strengthening of Lemma 3.1). Under the further hypothesis that `G` is
  jointly continuous, the converse also holds: `z = w` on `[0, Δt]` if and only if
  `G(Δt - s, w s) ∈ range P` for every `s ∈ [0, Δt]`. Here the condition is evaluated along the
  unprojected trajectory `w`; when `z = w` this is the paper's condition. The condition on the
  closed interval is derived from the half-open one by continuity.

Deviations common to both: the paper's K- and S-step equations (Vlasov-type PDE in `x`) are
abstracted to an orthogonal projector `P` and a field `G` on a real inner product space `E`, and
`G` is assumed Lipschitz in the state uniformly in time (`IsLipschitzField`), an added hypothesis
that the paper does not state; it gives the uniqueness of the backward flows.
* `stored_field_reverse` (Sec. 4.2.3, abstract core). If a substep's field depends on the time
  through a stored quantity `σ t`, then the backward substep that reuses the stored value at the
  same physical time retraces the forward substep exactly. This is ODE uniqueness with the same
  stored field.

Core definitions used: `IsOrthProj`, `ODESolution`, `IsLipschitzField`, and the ODE uniqueness lemma
`LeanDLRA.AdjointDLRA.odeSolution_eq_reverse`. Locally added: none beyond the statements above.

Results of Sec. 3 already in the library and not duplicated here (`Control/AdjointDLRA.lean`):
`inner_comp_adjoint` (adjoint of a Lie–Trotter composition, Sec. 3), `IsKSLStep.reverse_eq`
(time-reversibility of the projector-splitting step, Sec. 3), and `ksl_fullRank_exact` (full-rank
exactness, Sec. 3.2).

Not formalised: Theorem 3.2 (the explicit counterexample `∂_t f = cos v ∂_x f` with rank-one
data and `Δt = π³/√5`). Its proof relies on a specific QR orthonormalisation choice and explicit
matrix ODEs for the Lie–Trotter substeps, so it is not part of this module. Also not formalised:
the claim that symmetric substep integrators (implicit midpoint) are reversible, which depends on
a specific discretisation.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2608_21545

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An element of the range of an orthogonal projector is a fixed point of it. -/
lemma mem_range_iff_fixed {P : E →L[ℝ] E} (hP : IsOrthProj P) (x : E) :
    x ∈ LinearMap.range (P : E →ₗ[ℝ] E) ↔ P x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact hP.idem y
  · intro h
    exact ⟨x, h⟩

/-- **Lemma 3.1 as printed (cancellation condition), 2608.21545 Sec. 3.1, p. 9.**  Let `P` be an
orthogonal projector (`P = P_{X¹}`) and `G` a field that is Lipschitz in the state (an added
hypothesis, giving uniqueness). Let `z` solve the projected backward flow `z' = -P G(t, z)` of
Eq. (20) (the paper's `K^S`) and `w` the unprojected backward flow `w' = -G(t, w)` (the backward
K-step), both written in the reversed time `s = Δt - t` on `[0, Δt]`, with the same initial
value. If the projection in (20) is exact along `z`, i.e. `G(t, z) ∈ span X¹ = range P` for all
`t ∈ [0, Δt]`, then `z = w` on `[0, Δt]`: the backward K-step cancels the S-step. -/
theorem backward_cancel_of_proj_exact {P : E →L[ℝ] E} (hP : IsOrthProj P) {G : ℝ → E → E}
    {L : ℝ} (hG : IsLipschitzField G L) {Δt : ℝ} {w z : ℝ → E}
    (hw : ODESolution (fun s x => G (Δt - s) x) w 0 Δt)
    (hz : ODESolution (fun s x => P (G (Δt - s) x)) z 0 Δt) (hz0 : z 0 = w 0)
    (hR : ∀ s ∈ Icc 0 Δt, G (Δt - s) (z s) ∈ LinearMap.range (P : E →ₗ[ℝ] E)) :
    ∀ s ∈ Icc 0 Δt, z s = w s := by
  -- along `z` the projection is exact, so `z` solves the unprojected equation
  have hz' : ODESolution (fun s x => G (Δt - s) x) z 0 Δt := by
    refine ⟨hz.cont, fun s hs => ?_⟩
    have he : P (G (Δt - s) (z s)) = G (Δt - s) (z s) :=
      (mem_range_iff_fixed hP _).1 (hR s ⟨hs.1, hs.2.le⟩)
    have h1 : HasDerivWithinAt z (P (G (Δt - s) (z s))) (Ici s) s := hz.deriv s hs
    rw [he] at h1
    exact h1
  have hGL : IsLipschitzField (fun s x => G (Δt - s) x) (max L 0) := fun t x y =>
    (hG (Δt - t) x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have key := ODESolution.norm_sub_le_exp hGL (le_max_right _ _) hz' hw
  intro s hs
  have h := key s hs
  rw [hz0, sub_self, norm_zero, mul_zero] at h
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h)

/-- **Lemma 3.1, strengthened to an equivalence (2608.21545 Sec. 3.1).**  Let `P` be an orthogonal
projector (`P = P_{X¹}`), `G` a jointly continuous field that is Lipschitz in the state (added
hypotheses), and `Δt > 0`. Let `w` solve the unprojected backward flow `w' = -G(t, w)` written in
the reversed time `s = Δt - t` on `[0, Δt]`, and `z` the projected backward flow `z' = -P G(t, z)`
with the same initial value. Then the projected backward run retraces the unprojected one (`z = w`
on `[0, Δt]`, i.e. the backward K-step cancels) if and only if
`G(Δt - s, w s) ∈ span X¹ = range P` for every `s ∈ [0, Δt]`. The paper states only the "if"
direction, with the condition along `z` (`backward_cancel_of_proj_exact`); here it is along `w`,
which is the same condition whenever `z = w`. -/
theorem backward_cancel_iff {P : E →L[ℝ] E} (hP : IsOrthProj P) {G : ℝ → E → E} {L : ℝ}
    (hG : IsLipschitzField G L) (hGc : Continuous (Function.uncurry G)) {Δt : ℝ} (hΔt : 0 < Δt)
    {w z : ℝ → E} (hw : ODESolution (fun s x => G (Δt - s) x) w 0 Δt)
    (hz : ODESolution (fun s x => P (G (Δt - s) x)) z 0 Δt) (hz0 : z 0 = w 0) :
    (∀ s ∈ Icc 0 Δt, z s = w s) ↔
      ∀ s ∈ Icc 0 Δt, G (Δt - s) (w s) ∈ LinearMap.range (P : E →ₗ[ℝ] E) := by
  simp only [mem_range_iff_fixed hP]
  constructor
  · intro hzw
    -- on the half-open interval the two right derivatives agree, which forces `P G = G`
    have hOn : ∀ s ∈ Ico 0 Δt, P (G (Δt - s) (w s)) = G (Δt - s) (w s) := by
      intro s hs
      have hev : w =ᶠ[nhdsWithin s (Ici s)] z := by
        filter_upwards [Ico_mem_nhdsGE hs.2] with u hu
        exact (hzw u ⟨hs.1.trans hu.1, hu.2.le⟩).symm
      have h1 := hz.deriv s hs
      have h2 : HasDerivWithinAt w (P (G (Δt - s) (z s))) (Ici s) s :=
        h1.congr_of_eventuallyEq hev (hzw s ⟨hs.1, hs.2.le⟩).symm
      rw [hzw s ⟨hs.1, hs.2.le⟩] at h2
      exact (uniqueDiffWithinAt_Ici s).eq_deriv _ h2 (hw.deriv s hs)
    -- continuity extends the identity from `[0, Δt)` to `[0, Δt]`
    have hGw : ContinuousOn (fun s => G (Δt - s) (w s)) (Icc 0 Δt) := by
      have h1 : ContinuousOn (fun s => (Δt - s, w s)) (Icc 0 Δt) :=
        (continuous_const.sub continuous_id).continuousOn.prodMk hw.cont
      exact hGc.comp_continuousOn h1
    have hPc : ContinuousOn (fun s => P (G (Δt - s) (w s))) (Icc 0 Δt) :=
      P.continuous.comp_continuousOn hGw
    have hEq : EqOn (fun s => P (G (Δt - s) (w s))) (fun s => G (Δt - s) (w s)) (Icc 0 Δt) :=
      EqOn.of_subset_closure hOn hPc hGw Ico_subset_Icc_self (closure_Ico hΔt.ne).symm.subset
    intro s hs
    exact hEq hs
  · intro hR
    -- the unprojected trajectory solves the projected equation, so uniqueness applies
    have hw' : ODESolution (fun s x => P (G (Δt - s) x)) w 0 Δt := by
      refine ⟨hw.cont, fun s hs => ?_⟩
      have he : P (G (Δt - s) (w s)) = G (Δt - s) (w s) := hR s ⟨hs.1, hs.2.le⟩
      change HasDerivWithinAt w (P (G (Δt - s) (w s))) (Ici s) s
      rw [he]
      exact hw.deriv s hs
    have hGL : IsLipschitzField (fun s x => G (Δt - s) x) (max L 0) := fun t x y =>
      (hG (Δt - t) x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    have hPL : IsLipschitzField (fun s x => P (G (Δt - s) x)) (max L 0) :=
      hGL.comp_contraction P hP.norm_le
    have key := ODESolution.norm_sub_le_exp hPL (le_max_right _ _) hz hw'
    intro s hs
    have h := key s hs
    rw [hz0, sub_self, norm_zero, mul_zero] at h
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h)

/-- Non-vacuity of `backward_cancel_iff`: for the zero field and `P = 0`, all hypotheses hold and
the cancellation condition is satisfied. -/
example : ∀ s ∈ Icc (0 : ℝ) 1, (fun _ : ℝ => (0 : ℝ)) s = (fun _ : ℝ => (0 : ℝ)) s := by
  have hP0 : IsOrthProj (0 : ℝ →L[ℝ] ℝ) := ⟨by simp, by simp⟩
  have hG0 : IsLipschitzField (fun (_ : ℝ) (_ : ℝ) => (0 : ℝ)) 0 := fun _ _ _ => by simp
  have hGc0 : Continuous (Function.uncurry fun (_ : ℝ) (_ : ℝ) => (0 : ℝ)) := continuous_const
  have hw0 : ODESolution (fun (_ : ℝ) (_ : ℝ) => (0 : ℝ)) (fun _ => (0 : ℝ)) 0 1 :=
    ⟨continuousOn_const, fun t _ => hasDerivWithinAt_const _ _ _⟩
  have hz0' : ODESolution (fun (s : ℝ) (x : ℝ) => (0 : ℝ →L[ℝ] ℝ) ((fun _ _ => (0 : ℝ)) (1 - s) x))
      (fun _ => (0 : ℝ)) 0 1 :=
    ⟨continuousOn_const, fun t _ => hasDerivWithinAt_const _ _ _⟩
  exact (backward_cancel_iff hP0 hG0 hGc0 one_pos hw0 hz0' rfl).2 (fun s _ => by simp)

/-- Non-vacuity of `backward_cancel_of_proj_exact`: the zero field with `P = 0`. -/
example : ∀ s ∈ Icc (0 : ℝ) 1, (fun _ : ℝ => (0 : ℝ)) s = (fun _ : ℝ => (0 : ℝ)) s := by
  have hP0 : IsOrthProj (0 : ℝ →L[ℝ] ℝ) := ⟨by simp, by simp⟩
  have hG0 : IsLipschitzField (fun (_ : ℝ) (_ : ℝ) => (0 : ℝ)) 0 := fun _ _ _ => by simp
  have hw0 : ODESolution (fun (_ : ℝ) (_ : ℝ) => (0 : ℝ)) (fun _ => (0 : ℝ)) 0 1 :=
    ⟨continuousOn_const, fun t _ => hasDerivWithinAt_const _ _ _⟩
  have hz0' : ODESolution (fun (s : ℝ) (x : ℝ) => (0 : ℝ →L[ℝ] ℝ) ((fun _ _ => (0 : ℝ)) (1 - s) x))
      (fun _ => (0 : ℝ)) 0 1 :=
    ⟨continuousOn_const, fun t _ => hasDerivWithinAt_const _ _ _⟩
  exact backward_cancel_of_proj_exact hP0 hG0 hw0 hz0' rfl (fun s _ => ⟨0, by simp⟩)

/-- **Sec. 4.2.3 (abstract core): stored fields make the backward substep retrace the forward one.**
Let a substep field be `Φ (σ t) t x`, where `σ t` is a stored quantity at time `t` (for example the
electric field `E_i`). If `y` solves the forward substep on `[a, b]` and `z` solves the backward
substep, which uses the *same* stored value `σ (a + b - s)` at the same physical time, starting from
`z a = y b`, then `z s = y (a + b - s)` on `[a, b]`. The forward and backward right-hand sides are
therefore identical, and no re-solve of the field is needed. Proved by ODE uniqueness. The paper
states this informally (Sec. 4.2.3, p. 19: reusing the stored electric fields makes the right-hand
side of the backward integration exactly the same); the Lean statement is the abstract ODE fact,
with continuity and a Lipschitz bound on the field as added hypotheses. -/
theorem stored_field_reverse {Θ : Type*} {Φ : Θ → ℝ → E → E} {σ : ℝ → Θ} {L a b : ℝ}
    {y z : ℝ → E} (hf : Continuous (Function.uncurry fun t x => Φ (σ t) t x))
    (hL : IsLipschitzField (fun t x => Φ (σ t) t x) L)
    (hy : ODESolution (fun t x => Φ (σ t) t x) y a b)
    (hz : ODESolution (fun s x => -Φ (σ (a + b - s)) (a + b - s) x) z a b) (h0 : z a = y b) :
    ∀ s ∈ Icc a b, z s = y (a + b - s) :=
  LeanDLRA.AdjointDLRA.odeSolution_eq_reverse hf hL (fun _ _ => rfl) hy hz h0

/-- Non-vacuity of `stored_field_reverse`: the zero field with a trivial stored quantity. -/
example : ∀ s ∈ Icc (0 : ℝ) 1, (fun _ : ℝ => (0 : ℝ)) s = (fun _ : ℝ => (0 : ℝ)) (0 + 1 - s) :=
  stored_field_reverse (Φ := fun (_ : Unit) (_ : ℝ) (_ : ℝ) => (0 : ℝ)) (σ := fun _ => ())
    (L := 0) continuous_const (fun _ _ _ => by simp)
    ⟨continuousOn_const, fun _ _ => hasDerivWithinAt_const _ _ _⟩
    ⟨continuousOn_const, fun _ _ => by simpa using hasDerivWithinAt_const _ _ (0 : ℝ)⟩ rfl

end LeanDLRA.Literature.P2608_21545
