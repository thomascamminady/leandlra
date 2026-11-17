import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Dynamics.ContinuousDLRA
import LeanDLRA.DLRA.DynamicallyOrthogonal
import LeanDLRA.FixedRank.TangentSpace.Curvature
import LeanDLRA.LinearAlgebra.SVD.MinMax

/-!
# Quasi-optimality of dynamical low-rank approximation for matrices

Let `A` be a curve of matrices, `X` a curve of rank-`r` matrices that are critical points of the
distance to `A` (`P(X) (A - X) = 0`, with `P(X) = tangentProjAt X`), for example best
approximations of rank `r`, and `Y` the dynamical low-rank approximation of rank `r` of
`Ȧ = F(t, A)`: `Ẏ = P(Y) F(t, Y)`. As long as the `r`-th singular value of `X` stays above
`ρ > 0` and `‖X - A‖ ≤ ρ / 4`, the distance of `Y` to `X` is bounded by the time integral of the
approximation error `‖X - A‖`, with explicit constants. All norms are Frobenius norms.

## Main results

* `norm_tangentProjAt_sub_le_of_hasDerivWithinAt`: differentiated first-order optimality,
  `‖P(X t) (A' - X')‖ ≤ 2 ρ⁻¹ ‖X'‖ ‖A t - X t‖`; with `‖A'‖ ≤ μ` and `‖X t - A t‖ ≤ ρ / 4` it
  gives `‖X'‖ ≤ 2 μ` (`norm_le_of_tangentProjAt_sub_eq_zero`) and
  `‖X' - P(X t) A'‖ ≤ 4 μ ρ⁻¹ ‖A t - X t‖`
  (`norm_sub_tangentProjAt_le_of_tangentProjAt_sub_eq_zero`).
* `dlra_norm_sub_le_integral`: for a factored solution `Y = U S Vᵀ` of
  `Ẏ = tangentProj U V F(t, Y)` with `F` `L`-Lipschitz and `‖Y a - X a‖ ≤ δ`,
  `‖Y t - X t‖ ≤ e^{(L + 6 μ/ρ)(t - a)} (δ + (L + 4 μ/ρ) ∫ₐᵗ ‖X - A‖)`.
* `dlra_norm_sub_le_add_integral`: the bound for `‖Y t - A t‖`, the matrix instance of the
  abstract `ODESolution.dlra_quasiOptimal_integral` with its hypotheses on the curvature, on the
  tangency of `Ẋ` and on the best approximation discharged.
* `IsDLRASolution.norm_sub_le_integral`: the bound for a DLRA solution of rank `r`
  (`IsDLRASolution`); `IsDLRASolution.norm_sub_le_integral_of_forall_norm_sub_le`: the same for
  a right-differentiable curve `X` of best approximations of rank at most `r`.
* `dlra_norm_sub_truncation_le_integral`: the case `F(t, Y) = Ȧ(t)`, `X t = T_r(A t)`, `Y 0 = X 0`:
  `‖Y t - X t‖ ≤ 2 β e^{β t} ∫₀ᵗ ‖X s - A s‖ ds` with `β = 8 μ / ρ`.

## Implementation notes

No smallness of `‖Y - X‖` is assumed: the Lipschitz bound of the tangent projector
(`norm_tangentProj_sub_tangentProjAt_le`) needs the lower bound `ρ` at `X` only. The derivative
of the first-order condition is bounded by a slope argument with the same Lipschitz bound, without
a Weingarten map. A bound of this kind, the distance to the best approximation against the time
integral of the best-approximation error, is in [KochLubich2007]; the constants `ρ / 4`, `6 μ / ρ`,
`4 μ / ρ` (and `ρ / 16`, `8 μ / ρ`, `2` in `dlra_norm_sub_truncation_le_integral`) are those of
these proofs.

## TODO

* Differentiability of the best approximation `t ↦ T_r(A t)` under the gap `σ_r > σ_{r+1}`: the
  theorems assume that `X` is a right-differentiable curve.
* Existence of the DLRA solution: the theorems assume a solution `Y` on `[a, b]`.
* A tube-local version, with `F` Lipschitz only near `A` (it needs a bootstrap that keeps `Y` in
  the tube).

## References

* [KochLubich2007]
-/

open Set Finset Matrix Filter
open scoped Topology

namespace LeanDLRA

section QuasiOptimal

open scoped LeanDLRA.Frobenius
open EckartYoung

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-! ### Derivatives of a curve of critical points -/

/-- **Differentiated first-order optimality.** Let `A`, `X` have the derivatives `A'`, `X'` at
`t ∈ s` within `s` (`t` an accumulation point of `s`), let `X u` have rank `r` and satisfy the
first-order condition `P(X u) (A u - X u) = 0` for `u ∈ s`, and let `0 < ρ ≤ σ_{r-1}(X t)`. Then
`‖P(X t) (A' - X')‖ ≤ 2 ρ⁻¹ ‖X'‖ ‖A t - X t‖`. -/
theorem norm_tangentProjAt_sub_le_of_hasDerivWithinAt {r : ℕ} {A X : ℝ → Matrix m n ℝ}
    {A' X' : Matrix m n ℝ} {s : Set ℝ} {t ρ : ℝ} (hA : HasDerivWithinAt A A' s t)
    (hX : HasDerivWithinAt X X' s t) (ht : t ∈ s) (hs : (𝓝[s \ {t}] t).NeBot) (hρ : 0 < ρ)
    (hrank : ∀ u ∈ s, (X u).rank = r) (hσ : ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ u ∈ s, tangentProjAt (X u) (A u - X u) = 0) :
    ‖tangentProjAt (X t) (A' - X')‖ ≤ 2 * ρ⁻¹ * ‖X'‖ * ‖A t - X t‖ := by
  have hφ : HasDerivWithinAt (fun u => tangentProjAt (X t) (A u - X u - (A t - X t)))
      (tangentProjAt (X t) (A' - X')) s t :=
    (tangentProjAt (X t)).hasFDerivAt.comp_hasDerivWithinAt t ((hA.sub hX).sub_const _)
  have hb : ∀ u ∈ s, ‖tangentProjAt (X t) (A u - X u - (A t - X t))‖ ≤
      ‖X u - X t‖ * (2 * ρ⁻¹ * ‖A u - X u‖) := fun u hu => by
    have h := norm_tangentProjAt_sub_le (hrank t ht) (hrank u hu) hρ hσ (A u - X u)
    have e : tangentProjAt (X t) (A u - X u - (A t - X t)) =
        -(tangentProjAt (X u) (A u - X u) - tangentProjAt (X t) (A u - X u)) := by
      rw [hopt u hu, map_sub (tangentProjAt (X t)) (A u - X u) (A t - X t), hopt t ht]
      simp
    rw [e, norm_neg]
    calc _ ≤ _ := h
      _ = _ := by ring
  have hg : ContinuousWithinAt (fun u => 2 * ρ⁻¹ * ‖A u - X u‖) s t :=
    continuousWithinAt_const.mul ((hA.continuousWithinAt.sub hX.continuousWithinAt).norm)
  have h := norm_deriv_le_of_norm_le_norm_sub_mul hφ hX hs (by simp) hg hb
  calc _ ≤ _ := h
    _ = _ := by ring

/-- The two estimates behind `norm_le_of_tangentProjAt_sub_eq_zero` and
`norm_sub_tangentProjAt_le_of_tangentProjAt_sub_eq_zero`. -/
private theorem deriv_bounds_of_tangentProjAt_sub_eq_zero {r : ℕ} {A X : ℝ → Matrix m n ℝ}
    {A' X' : Matrix m n ℝ} {s : Set ℝ} {t ρ μ : ℝ} (hA : HasDerivWithinAt A A' s t)
    (hX : HasDerivWithinAt X X' s t) (ht : t ∈ s) (hs : (𝓝[s \ {t}] t).NeBot) (hρ : 0 < ρ)
    (hrank : ∀ u ∈ s, (X u).rank = r)
    (hσ : ∀ u ∈ s, ρ ≤ (toEuclideanLin (X u)).singularValues (r - 1))
    (hopt : ∀ u ∈ s, tangentProjAt (X u) (A u - X u) = 0) (hμ : ‖A'‖ ≤ μ)
    (hd : ‖X t - A t‖ ≤ ρ / 4) :
    ‖X'‖ ≤ 2 * μ ∧ ‖X' - tangentProjAt (X t) A'‖ ≤ 4 * μ / ρ * ‖A t - X t‖ := by
  have htan : tangentProjAt (X t) X' = X' := tangentProjAt_eq_self_iff.mpr
    (mem_tangentSpaceAt_of_hasDerivWithinAt hX ht hs hρ hrank hσ)
  have hdef := norm_tangentProjAt_sub_le_of_hasDerivWithinAt hA hX ht hs hρ hrank (hσ t ht) hopt
  have hE : ρ⁻¹ * ‖A t - X t‖ ≤ 1 / 4 := by
    rw [inv_mul_le_iff₀ hρ, norm_sub_rev]
    linarith
  have h1 : ‖tangentProjAt (X t) A'‖ ≤ μ := ((isOrthProj_tangentProjAt _).norm_le _).trans hμ
  have hX' : ‖X'‖ ≤ 2 * μ := by
    have e : X' = tangentProjAt (X t) A' - tangentProjAt (X t) (A' - X') := by
      rw [map_sub, htan]
      abel
    have h3 : ‖X'‖ ≤ ‖tangentProjAt (X t) A'‖ + ‖tangentProjAt (X t) (A' - X')‖ := by
      conv_lhs => rw [e]
      exact norm_sub_le _ _
    have h4 : 2 * ρ⁻¹ * ‖X'‖ * ‖A t - X t‖ ≤ ‖X'‖ / 2 := by
      have := mul_le_mul_of_nonneg_left hE (norm_nonneg X')
      nlinarith
    linarith
  refine ⟨hX', ?_⟩
  have e : X' - tangentProjAt (X t) A' = -tangentProjAt (X t) (A' - X') := by
    rw [map_sub, htan]
    abel
  rw [e, norm_neg]
  refine hdef.trans ?_
  have hρ' : 0 ≤ 2 * ρ⁻¹ := by positivity
  calc 2 * ρ⁻¹ * ‖X'‖ * ‖A t - X t‖ ≤ 2 * ρ⁻¹ * (2 * μ) * ‖A t - X t‖ := by gcongr
    _ = 4 * μ / ρ * ‖A t - X t‖ := by rw [div_eq_mul_inv]; ring

/-- **Speed of a curve of critical points.** Under the hypotheses of
`norm_tangentProjAt_sub_le_of_hasDerivWithinAt`, with `ρ ≤ σ_{r-1}(X u)` on `s`, `‖A'‖ ≤ μ` and
`‖X t - A t‖ ≤ ρ / 4`: `‖X'‖ ≤ 2 μ`. -/
theorem norm_le_of_tangentProjAt_sub_eq_zero {r : ℕ} {A X : ℝ → Matrix m n ℝ}
    {A' X' : Matrix m n ℝ} {s : Set ℝ} {t ρ μ : ℝ} (hA : HasDerivWithinAt A A' s t)
    (hX : HasDerivWithinAt X X' s t) (ht : t ∈ s) (hs : (𝓝[s \ {t}] t).NeBot) (hρ : 0 < ρ)
    (hrank : ∀ u ∈ s, (X u).rank = r)
    (hσ : ∀ u ∈ s, ρ ≤ (toEuclideanLin (X u)).singularValues (r - 1))
    (hopt : ∀ u ∈ s, tangentProjAt (X u) (A u - X u) = 0) (hμ : ‖A'‖ ≤ μ)
    (hd : ‖X t - A t‖ ≤ ρ / 4) : ‖X'‖ ≤ 2 * μ :=
  (deriv_bounds_of_tangentProjAt_sub_eq_zero hA hX ht hs hρ hrank hσ hopt hμ hd).1

/-- **The velocity of a curve of critical points is the projected velocity, up to the
approximation error.** Under the hypotheses of `norm_le_of_tangentProjAt_sub_eq_zero`:
`‖X' - P(X t) A'‖ ≤ 4 μ ρ⁻¹ ‖A t - X t‖`. This is the best-approximation hypothesis `hbest` of
`ODESolution.dlra_quasiOptimal` with `c = 4 μ / ρ`. -/
theorem norm_sub_tangentProjAt_le_of_tangentProjAt_sub_eq_zero {r : ℕ}
    {A X : ℝ → Matrix m n ℝ} {A' X' : Matrix m n ℝ} {s : Set ℝ} {t ρ μ : ℝ}
    (hA : HasDerivWithinAt A A' s t) (hX : HasDerivWithinAt X X' s t) (ht : t ∈ s)
    (hs : (𝓝[s \ {t}] t).NeBot) (hρ : 0 < ρ) (hrank : ∀ u ∈ s, (X u).rank = r)
    (hσ : ∀ u ∈ s, ρ ≤ (toEuclideanLin (X u)).singularValues (r - 1))
    (hopt : ∀ u ∈ s, tangentProjAt (X u) (A u - X u) = 0) (hμ : ‖A'‖ ≤ μ)
    (hd : ‖X t - A t‖ ≤ ρ / 4) :
    ‖X' - tangentProjAt (X t) A'‖ ≤ 4 * μ / ρ * ‖A t - X t‖ :=
  (deriv_bounds_of_tangentProjAt_sub_eq_zero hA hX ht hs hρ hrank hσ hopt hμ hd).2

/-! ### Quasi-optimality along a curve of critical points -/

/-- The derivative bounds of `norm_le_of_tangentProjAt_sub_eq_zero` and
`norm_sub_tangentProjAt_le_of_tangentProjAt_sub_eq_zero` at a time `t ∈ [a, b)`, from right
derivatives on `[t, b]`, together with the tangency of `X' t`. -/
private theorem deriv_bounds_on_Ico {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {A X X' : ℝ → Matrix m n ℝ} {a b μ ρ : ℝ} (hρ : 0 < ρ) (hA : ODESolution F A a b)
    (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ)
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ t ∈ Icc a b, tangentProjAt (X t) (A t - X t) = 0)
    (hd : ∀ t ∈ Icc a b, ‖X t - A t‖ ≤ ρ / 4) {t : ℝ} (ht : t ∈ Ico a b) :
    tangentProjAt (X t) (X' t) = X' t ∧ ‖X' t‖ ≤ 2 * μ ∧
      ‖X' t - tangentProjAt (X t) (F t (A t))‖ ≤ 4 * μ / ρ * ‖A t - X t‖ := by
  have hsub : Icc t b ⊆ Icc a b := Icc_subset_Icc_left ht.1
  have hts : t ∈ Icc t b := ⟨le_rfl, ht.2.le⟩
  have hs : (𝓝[Icc t b \ {t}] t).NeBot := by
    rw [Icc_sdiff_left]
    exact left_nhdsWithin_Ioc_neBot ht.2
  have hA' := (hA.deriv t ht).mono (Icc_subset_Ici_self : Icc t b ⊆ Ici t)
  have hX' := (hX t ht).mono (Icc_subset_Ici_self : Icc t b ⊆ Ici t)
  have hrank : ∀ u ∈ Icc t b, (X u).rank = r := fun u hu => hXr u (hsub hu)
  have hσ' : ∀ u ∈ Icc t b, ρ ≤ (toEuclideanLin (X u)).singularValues (r - 1) :=
    fun u hu => hσ u (hsub hu)
  have hopt' : ∀ u ∈ Icc t b, tangentProjAt (X u) (A u - X u) = 0 := fun u hu => hopt u (hsub hu)
  exact ⟨tangentProjAt_eq_self_iff.mpr
      (mem_tangentSpaceAt_of_hasDerivWithinAt hX' hts hs hρ hrank hσ'),
    deriv_bounds_of_tangentProjAt_sub_eq_zero hA' hX' hts hs hρ hrank hσ' hopt' (hμ t ht)
      (hd t (Ico_subset_Icc_self ht))⟩

omit [DecidableEq n] in
/-- A continuous function on `ℝ` that equals `‖X s - A s‖` on `[a, b]`. -/
private theorem exists_continuous_eq_norm_sub {X A : ℝ → Matrix m n ℝ} {a b : ℝ} (hab : a ≤ b)
    (hX : ContinuousOn X (Icc a b)) (hA : ContinuousOn A (Icc a b)) :
    ∃ η : ℝ → ℝ, Continuous η ∧ ∀ s ∈ Icc a b, η s = ‖X s - A s‖ := by
  refine ⟨fun s => ‖X (projIcc a b hab s) - A (projIcc a b hab s)‖, ?_, fun s hs => by
    simp only [projIcc_of_mem _ hs]⟩
  exact (hX.sub hA).norm.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
    fun s => (projIcc a b hab s).2

/-- **Quasi-optimality of matrix DLRA along a curve of critical points.** Let `A` solve
`Ȧ = F(t, A)` on `[a, b]` with `F` `L`-Lipschitz and `‖Ȧ‖ ≤ μ`; let `X` be continuous on `[a, b]`
with right derivatives `X'`, of rank `r` with `0 < ρ ≤ σ_{r-1}(X t)`, a critical point of the
distance to `A` (`P(X t) (A t - X t) = 0`) with `‖X t - A t‖ ≤ ρ / 4`; and let `Y = U S Vᵀ`
(`r` orthonormal columns in `U`, `V`, any core `S`) solve `Ẏ = tangentProj U V F(t, Y)` with
`‖Y a - X a‖ ≤ δ`. Then for `t ∈ [a, b]`
`‖Y t - X t‖ ≤ e^{(L + 6 μ/ρ)(t - a)} (δ + (L + 4 μ/ρ) ∫ₐᵗ ‖X s - A s‖ ds)`.
No smallness of `‖Y - X‖` is assumed. A bound of this kind is in [KochLubich2007]; the constants
are those of this proof. -/
theorem dlra_norm_sub_le_integral {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {A X X' Y : ℝ → Matrix m n ℝ} {a b L μ ρ δ : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hF : IsLipschitzField F L) (hA : ODESolution F A a b)
    (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ t ∈ Icc a b, tangentProjAt (X t) (A t - X t) = 0)
    (hd : ∀ t ∈ Icc a b, ‖X t - A t‖ ≤ ρ / 4)
    {U : ℝ → Matrix m (Fin r) ℝ} {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {V : ℝ → Matrix n (Fin r) ℝ}
    (hUV : ∀ t ∈ Icc a b, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧ Y t = U t * S t * (V t)ᵀ)
    (hY : ODESolution (fun t x => tangentProj (U t) (V t) (F t x)) Y a b)
    (hδ : ‖Y a - X a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp ((L + 6 * μ / ρ) * (t - a)) * (δ + (L + 4 * μ / ρ) * ∫ s in a..t, ‖X s - A s‖) := by
  intro t0 ht0
  rcases eq_or_lt_of_le ht0.1 with h0 | hpos
  · subst h0
    simpa using hδ
  have hab : a < b := hpos.trans_le ht0.2
  have hμ0 : 0 ≤ μ := (norm_nonneg _).trans (hμ a ⟨le_rfl, hab⟩)
  have hIcc : Icc a t0 ⊆ Icc a b := Icc_subset_Icc_right ht0.2
  have hIco : ∀ s ∈ Ico a t0, s ∈ Ico a b := fun s hs => ⟨hs.1, hs.2.trans_le ht0.2⟩
  obtain ⟨ηc, hηc, hηeq⟩ := exists_continuous_eq_norm_sub hab.le hXc hA.cont
  have hb := fun s (hs : s ∈ Ico a b) => deriv_bounds_on_Ico hρ hA hμ hX hXr hσ hopt hd hs
  have hP : ∀ s ∈ Icc a b,
      IsOrthProj (tangentProj (U s) (V s) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) :=
    fun s hs => isOrthProj_tangentProj (hUV s hs).1 (hUV s hs).2.1
  have hLip : ∀ s ∈ Icc a b, ∀ B : Matrix m n ℝ,
      ‖tangentProj (U s) (V s) B - tangentProjAt (X s) B‖ ≤ 2 * ρ⁻¹ * ‖Y s - X s‖ * ‖B‖ :=
    fun s hs B => by
      obtain ⟨hU, hV, hYs⟩ := hUV s hs
      rw [hYs]
      exact norm_tangentProj_sub_tangentProjAt_le (hXr s hs) hρ (hσ s hs) hU hV (S s) B
  have h₁ : ∀ s ∈ Ico a t0, ‖tangentProj (U s) (V s) (F s (X s) - X' s)‖ ≤
      2 * μ / ρ * ‖Y s - X s‖ + (L + 4 * μ / ρ) * ηc s := fun s hs => by
    have hsb := hIco s hs
    have hsI := Ico_subset_Icc_self hsb
    obtain ⟨-, -, hbest⟩ := hb s hsb
    have hsplit : F s (X s) - X' s = (F s (X s) - F s (A s)) +
        (F s (A s) - tangentProjAt (X s) (F s (A s))) -
        (X' s - tangentProjAt (X s) (F s (A s))) := by abel
    have e1 : ‖tangentProj (U s) (V s) (F s (X s) - F s (A s))‖ ≤ L * ηc s :=
      ((hP s hsI).norm_le _).trans ((hF s _ _).trans (le_of_eq (by rw [hηeq s hsI])))
    have e2 : ‖tangentProj (U s) (V s) (F s (A s) - tangentProjAt (X s) (F s (A s)))‖ ≤
        2 * μ / ρ * ‖Y s - X s‖ := by
      have hQ0 : tangentProjAt (X s) (F s (A s) - tangentProjAt (X s) (F s (A s))) = 0 := by
        rw [map_sub, (isOrthProj_tangentProjAt _).idem, sub_self]
      have e : tangentProj (U s) (V s) (F s (A s) - tangentProjAt (X s) (F s (A s))) =
          tangentProj (U s) (V s) (F s (A s) - tangentProjAt (X s) (F s (A s))) -
            tangentProjAt (X s) (F s (A s) - tangentProjAt (X s) (F s (A s))) := by
        rw [hQ0, sub_zero]
      rw [e]
      refine (hLip s hsI _).trans ?_
      have hn : ‖F s (A s) - tangentProjAt (X s) (F s (A s))‖ ≤ μ := by
        have := (isOrthProj_tangentProjAt (X s)).compl.norm_le (F s (A s))
        simp only [sub_apply, one_apply_eq_self] at this
        exact this.trans (hμ s hsb)
      have := norm_nonneg (Y s - X s)
      calc 2 * ρ⁻¹ * ‖Y s - X s‖ * ‖F s (A s) - tangentProjAt (X s) (F s (A s))‖ ≤
          2 * ρ⁻¹ * ‖Y s - X s‖ * μ := by gcongr
        _ = 2 * μ / ρ * ‖Y s - X s‖ := by rw [div_eq_mul_inv]; ring
    have e3 : ‖tangentProj (U s) (V s) (X' s - tangentProjAt (X s) (F s (A s)))‖ ≤
        4 * μ / ρ * ηc s :=
      ((hP s hsI).norm_le _).trans (by rw [hηeq s hsI, norm_sub_rev (X s)]; exact hbest)
    rw [hsplit, map_sub, map_add]
    calc _ ≤ ‖tangentProj (U s) (V s) (F s (X s) - F s (A s))‖ +
          ‖tangentProj (U s) (V s) (F s (A s) - tangentProjAt (X s) (F s (A s)))‖ +
          ‖tangentProj (U s) (V s) (X' s - tangentProjAt (X s) (F s (A s)))‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ L * ηc s + 2 * μ / ρ * ‖Y s - X s‖ + 4 * μ / ρ * ηc s :=
          add_le_add (add_le_add e1 e2) e3
      _ = _ := by ring
  have h₂ : ∀ s ∈ Ico a t0, ‖(1 - tangentProj (U s) (V s)) (X' s)‖ ≤
      4 * μ / ρ * ‖Y s - X s‖ + (fun _ : ℝ => (0 : ℝ)) s := fun s hs => by
    have hsb := hIco s hs
    have hsI := Ico_subset_Icc_self hsb
    obtain ⟨htan, hX's, -⟩ := hb s hsb
    have e : (1 - tangentProj (U s) (V s)) (X' s) =
        -(tangentProj (U s) (V s) (X' s) - tangentProjAt (X s) (X' s)) := by
      rw [sub_apply, one_apply_eq_self, htan]
      abel
    rw [e, norm_neg, add_zero]
    refine (hLip s hsI _).trans ?_
    have := norm_nonneg (Y s - X s)
    calc 2 * ρ⁻¹ * ‖Y s - X s‖ * ‖X' s‖ ≤ 2 * ρ⁻¹ * ‖Y s - X s‖ * (2 * μ) := by gcongr
      _ = 4 * μ / ρ * ‖Y s - X s‖ := by rw [div_eq_mul_inv]; ring
  have hYsol : ODESolution (fun t x => tangentProj (U t) (V t) (F t x)) Y a t0 :=
    ⟨hY.cont.mono hIcc, fun s hs => hY.deriv s (hIco s hs)⟩
  have hcmp := ODESolution.dlra_norm_sub_le_of_comparison_integral
    (P := fun t => tangentProj (U t) (V t)) (F := F) (Y := Y) (a := a) (b := t0) (L := L)
    (κ₁ := 2 * μ / ρ) (κ₂ := 4 * μ / ρ) (δ := δ)
    (η₁ := fun s => (L + 4 * μ / ρ) * ηc s) (η₂ := fun _ => 0)
    (continuous_const.mul hηc) continuous_const hF hYsol
    (fun s hs => hP s (hIcc (Ico_subset_Icc_self hs))) (hXc.mono hIcc)
    (fun s hs => hX s (hIco s hs)) h₁ h₂ hδ t0 ⟨ht0.1, le_rfl⟩
  have hK : 0 ≤ L + 2 * μ / ρ + 4 * μ / ρ := by positivity
  have hgb := gronwallIntegralBound_le (δ := δ)
    (η := fun s => (L + 4 * μ / ρ) * ηc s + (fun _ : ℝ => (0 : ℝ)) s)
    ((continuous_const.mul hηc).add continuous_const) hK ht0.1 (fun s hs => by
      have : 0 ≤ ηc s := by rw [hηeq s (hIcc hs)]; exact norm_nonneg _
      simp only [add_zero]
      positivity)
  have hJ : ∫ s in a..t0, ((L + 4 * μ / ρ) * ηc s + (fun _ : ℝ => (0 : ℝ)) s) =
      (L + 4 * μ / ρ) * ∫ s in a..t0, ‖X s - A s‖ := by
    simp only [add_zero]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht0.1] at hs
    exact hηeq s (hIcc hs)
  have hKe : L + 2 * μ / ρ + 4 * μ / ρ = L + 6 * μ / ρ := by ring
  refine hcmp.trans (hgb.trans (le_of_eq ?_))
  rw [hJ, hKe]

/-- **Quasi-optimality of matrix DLRA, error against `A`.** Under the hypotheses of
`dlra_norm_sub_le_integral`, for `t ∈ [a, b]`
`‖Y t - A t‖ ≤ ‖X t - A t‖ + e^{(L + 6 μ/ρ)(t - a)} (δ + (L + 4 μ/ρ) ∫ₐᵗ ‖X s - A s‖ ds)`.
This is the matrix instance of the abstract `ODESolution.dlra_quasiOptimal_integral`, with its
three hypotheses discharged: the curvature bound `hcurv` (with `γ = 2 / ρ`, by
`norm_tangentProj_sub_tangentProjAt_le`), the tangency `hXtan` of `Ẋ`
(`mem_tangentSpaceAt_of_hasDerivWithinAt`) and the best-approximation property `hbest` (with
`c = 4 μ / ρ`, by `norm_sub_tangentProjAt_le_of_tangentProjAt_sub_eq_zero`). -/
theorem dlra_norm_sub_le_add_integral {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {A X X' Y : ℝ → Matrix m n ℝ} {a b L μ ρ δ : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hF : IsLipschitzField F L) (hA : ODESolution F A a b)
    (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ t ∈ Icc a b, tangentProjAt (X t) (A t - X t) = 0)
    (hd : ∀ t ∈ Icc a b, ‖X t - A t‖ ≤ ρ / 4)
    {U : ℝ → Matrix m (Fin r) ℝ} {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {V : ℝ → Matrix n (Fin r) ℝ}
    (hUV : ∀ t ∈ Icc a b, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧ Y t = U t * S t * (V t)ᵀ)
    (hY : ODESolution (fun t x => tangentProj (U t) (V t) (F t x)) Y a b)
    (hδ : ‖Y a - X a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - A t‖ ≤ ‖X t - A t‖ +
      Real.exp ((L + 6 * μ / ρ) * (t - a)) * (δ + (L + 4 * μ / ρ) * ∫ s in a..t, ‖X s - A s‖) := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · rw [← h0]
    simp only [sub_self, mul_zero, Real.exp_zero, intervalIntegral.integral_same, add_zero,
      one_mul]
    calc ‖Y a - A a‖ ≤ ‖Y a - X a‖ + ‖X a - A a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := by linarith
  have hab : a < b := hpos.trans_le ht.2
  have hμ0 : 0 ≤ μ := (norm_nonneg _).trans (hμ a ⟨le_rfl, hab⟩)
  obtain ⟨ηc, hηc, hηeq⟩ := exists_continuous_eq_norm_sub hab.le hXc hA.cont
  have hb := fun s (hs : s ∈ Ico a b) => deriv_bounds_on_Ico hρ hA hμ hX hXr hσ hopt hd hs
  have h := ODESolution.dlra_quasiOptimal_integral (P := fun t => tangentProj (U t) (V t))
    (PX := fun t => tangentProjAt (X t)) (η := ηc) (L := L) (γ := 2 * ρ⁻¹) (μ := μ)
    (μ' := 2 * μ) (c := 4 * μ / ρ) (δ := δ) hηc hF hL hY
    (fun s hs => isOrthProj_tangentProj (hUV s (Ico_subset_Icc_self hs)).1
      (hUV s (Ico_subset_Icc_self hs)).2.1)
    (fun s _ => isOrthProj_tangentProjAt _) hXc hX (fun s hs => (hb s hs).1) (by positivity)
    (fun s hs z => by
      obtain ⟨hU, hV, hYs⟩ := hUV s (Ico_subset_Icc_self hs)
      rw [sub_apply, hYs]
      exact norm_tangentProj_sub_tangentProjAt_le (hXr s (Ico_subset_Icc_self hs)) hρ
        (hσ s (Ico_subset_Icc_self hs)) hU hV (S s) z)
    (by positivity) (fun s hs => (hb s hs).2.2) hμ (fun s hs => (hb s hs).2.1)
    (fun s hs => by rw [hηeq s hs, norm_sub_rev]) hδ t ht
  have hγ : L + 2 * ρ⁻¹ * (μ + 2 * μ) = L + 6 * μ / ρ := by rw [div_eq_mul_inv]; ring
  have hI : ∫ s in a..t, ηc s = ∫ s in a..t, ‖X s - A s‖ :=
    intervalIntegral.integral_congr fun s hs => by
      rw [uIcc_of_le ht.1] at hs
      exact hηeq s ⟨hs.1, hs.2.trans ht.2⟩
  rwa [hγ, hI, hηeq t ht] at h

/-- **Quasi-optimality for a DLRA solution of rank `r`.** The bound of
`dlra_norm_sub_le_integral` for a DLRA solution `Y` of rank `r` of `Ẏ = P(Y) F(t, Y)`
(`IsDLRASolution`) in place of a factored solution:
`‖Y t - X t‖ ≤ e^{(L + 6 μ/ρ)(t - a)} (δ + (L + 4 μ/ρ) ∫ₐᵗ ‖X s - A s‖ ds)`. -/
theorem IsDLRASolution.norm_sub_le_integral {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {A X X' Y : ℝ → Matrix m n ℝ} {a b L μ ρ δ : ℝ} (hY : IsDLRASolution r F Y a b)
    (hρ : 0 < ρ) (hL : 0 ≤ L) (hF : IsLipschitzField F L) (hA : ODESolution F A a b)
    (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ t ∈ Icc a b, tangentProjAt (X t) (A t - X t) = 0)
    (hd : ∀ t ∈ Icc a b, ‖X t - A t‖ ≤ ρ / 4) (hδ : ‖Y a - X a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp ((L + 6 * μ / ρ) * (t - a)) * (δ + (L + 4 * μ / ρ) * ∫ s in a..t, ‖X s - A s‖) := by
  have hfac : ∀ t ∈ Icc a b, ∃ (U : Matrix m (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ)
      (V : Matrix n (Fin r) ℝ), Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ IsUnit S.det ∧ Y t = U * S * Vᵀ :=
    fun t ht => (SVD.rank_eq_iff_exists_factor (Y t)).1 (hY.2 t ht)
  choose! U S V hU hV hS hYeq using hfac
  have hY' : ODESolution (fun t x => tangentProj (U t) (V t) (F t x)) Y a b :=
    ⟨hY.1.cont, fun t ht => have ht' := Ico_subset_Icc_self ht
      DynamicallyOrthogonal.IsDLRASolution.hasDerivWithinAt_tangentProj hY ht (hU t ht')
        (hV t ht') (hS t ht') (hYeq t ht')⟩
  exact dlra_norm_sub_le_integral hρ hL hF hA hμ hXc hX hXr hσ hopt hd
    (fun t ht => ⟨hU t ht, hV t ht, hYeq t ht⟩) hY' hδ

/-- **Quasi-optimality of matrix DLRA for a curve of best approximations** [KochLubich2007].
Let `Y` be a DLRA solution of rank `r` of `Ẏ = P(Y) F(t, Y)` on `[a, b]` (`IsDLRASolution`),
`A` a solution of `Ȧ = F(t, A)` with `F` `L`-Lipschitz and `‖Ȧ‖ ≤ μ`, and `X` a curve of best
approximations of `A` of rank at most `r` (`‖A t - X t‖ ≤ ‖A t - Z‖` for every `Z` of rank at
most `r`) with `0 < ρ ≤ σ_{r-1}(X t)` and `‖X t - A t‖ ≤ ρ / 4`. If `‖Y a - X a‖ ≤ δ`, then
for `t ∈ [a, b]`
`‖Y t - X t‖ ≤ e^{(L + 6 μ/ρ)(t - a)} (δ + (L + 4 μ/ρ) ∫ₐᵗ ‖X s - A s‖ ds)`.
The single remaining hypothesis on `X` is that it is a curve of best approximations that is
continuous on `[a, b]` and has right derivatives on `[a, b)`; that this holds under a gap
`σ_r(A) > σ_{r+1}(A)` is not shown here. The constants are those of this proof. -/
theorem IsDLRASolution.norm_sub_le_integral_of_forall_norm_sub_le {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A X X' Y : ℝ → Matrix m n ℝ} {a b L μ ρ δ : ℝ}
    (hY : IsDLRASolution r F Y a b) (hρ : 0 < ρ) (hL : 0 ≤ L) (hF : IsLipschitzField F L)
    (hA : ODESolution F A a b) (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ)
    (hXc : ContinuousOn X (Icc a b)) (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hbest : ∀ t ∈ Icc a b, (X t).rank ≤ r ∧
      ∀ Z : Matrix m n ℝ, Z.rank ≤ r → ‖A t - X t‖ ≤ ‖A t - Z‖)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hd : ∀ t ∈ Icc a b, ‖X t - A t‖ ≤ ρ / 4) (hδ : ‖Y a - X a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp ((L + 6 * μ / ρ) * (t - a)) * (δ + (L + 4 * μ / ρ) * ∫ s in a..t, ‖X s - A s‖) := by
  have hXr : ∀ t ∈ Icc a b, (X t).rank = r := fun t ht => by
    have hpos : 0 < (toEuclideanLin (X t)).singularValues (r - 1) := hρ.trans_le (hσ t ht)
    rw [LinearMap.singularValues_pos_iff_lt_finrank_range, ← SVD.rank_eq_finrank_range] at hpos
    have := (hbest t ht).1
    omega
  exact hY.norm_sub_le_integral hρ hL hF hA hμ hXc hX hXr hσ
    (fun t ht => tangentProjAt_sub_eq_zero_of_forall_norm_sub_le (hbest t ht).1 (hbest t ht).2)
    hd hδ

/-! ### The truncated SVD -/

/-- If the `r`-th singular value of `A` is at least `ρ > 0`, then `truncation A r` is
`U diag(σ) Vᵀ` with orthonormal columns of `U` and `V` and `σ i ≥ ρ`. -/
private theorem truncation_factor {r : ℕ} (hr : 0 < r) {A : Matrix m n ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : ρ ≤ (toEuclideanLin A).singularValues (r - 1)) :
    ∃ (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) (σ : Fin r → ℝ),
      Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ (∀ i, ρ ≤ σ i) ∧ truncation A r = U * diagonal σ * Vᵀ := by
  have hd : r ≤ Module.finrank ℝ (EuclideanSpace ℝ n) := by
    have h0 : 0 < (toEuclideanLin A).singularValues (r - 1) := lt_of_lt_of_le hρ hσ
    rw [LinearMap.singularValues_pos_iff_lt_finrank_range] at h0
    have := (toEuclideanLin A).finrank_range_le_finrank
    omega
  let e : Fin r → Fin (Module.finrank ℝ (EuclideanSpace ℝ n)) := Fin.castLE hd
  let ε : Fin r ≃ {i : Fin (Module.finrank ℝ (EuclideanSpace ℝ n)) // (i : ℕ) < r} :=
    ⟨fun j => ⟨e j, j.2⟩, fun x => ⟨x.1.1, x.2⟩, fun j => rfl, fun x => rfl⟩
  let V : Matrix n (Fin r) ℝ := fun a j => rightSingularVectors A (e j) a
  have hVV : V * Vᵀ = topRightSingularVectors A r * (topRightSingularVectors A r)ᵀ := by
    ext a b
    simp only [V, Matrix.mul_apply, transpose_apply, topRightSingularVectors]
    exact Equiv.sum_comp ε (fun i => rightSingularVectors A i a * rightSingularVectors A i b)
  have hV : Vᵀ * V = 1 := by
    ext i j
    have h := orthonormal_iff_ite.mp (rightSingularVectors A).orthonormal (e i) (e j)
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial] at h
    have hij : e i = e j ↔ i = j := (Fin.castLE_injective hd).eq_iff
    simp only [hij] at h
    simp only [Matrix.one_apply]
    rw [← h, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun a _ ↦ mul_comm _ _
  let σ : Fin r → ℝ := fun j => (toEuclideanLin A).singularValues (e j)
  have hσr : ∀ j, ρ ≤ σ j := fun j =>
    hσ.trans ((toEuclideanLin A).singularValues_antitone (by simp [e, Fin.castLE]; omega))
  have hσpos : ∀ j, σ j ≠ 0 := fun j => (lt_of_lt_of_le hρ (hσr j)).ne'
  have h1 : Aᵀ * A * V = V * diagonal (fun j => σ j ^ 2) := by
    ext a j
    have h := congrFun (transpose_mul_self_mulVec_rightSingularVectors A (e j)) a
    have h' : (Aᵀ * A * V) a j =
        ((Aᵀ * A) *ᵥ WithLp.ofLp (rightSingularVectors A (e j))) a := by
      rfl
    rw [h', h, Matrix.mul_diagonal]
    simp [V, σ, mul_comm]
  let D' : Matrix (Fin r) (Fin r) ℝ := diagonal fun j => (σ j)⁻¹
  have hD : D' * diagonal σ = 1 := by
    simp only [D', diagonal_mul_diagonal]
    rw [← diagonal_one]
    congr 1
    funext j
    exact inv_mul_cancel₀ (hσpos j)
  have hD2 : D' * diagonal (fun j => σ j ^ 2) * D' = 1 := by
    simp only [D', diagonal_mul_diagonal]
    rw [← diagonal_one]
    congr 1
    funext j
    have := hσpos j
    field_simp
  refine ⟨A * V * D', V, σ, ?_, hV, hσr, ?_⟩
  · have : (A * V * D')ᵀ * (A * V * D') = D' * (Vᵀ * (Aᵀ * A * V)) * D' := by
      simp [D', Matrix.transpose_mul, Matrix.mul_assoc]
    rw [this, h1, ← Matrix.mul_assoc Vᵀ, hV, Matrix.one_mul]
    exact hD2
  · have h3 : A * V * D' * diagonal σ * Vᵀ = A * (V * Vᵀ) := by
      rw [Matrix.mul_assoc (A * V), hD, Matrix.mul_one, Matrix.mul_assoc]
    rw [h3, hVV, truncation, Matrix.mul_assoc]

/-- **Quasi-optimality of matrix DLRA.** Let `X(t) = T_r(A(t))` be a differentiable best
rank-`r` approximation with `σ_r(A(t)) ≥ ρ`, `‖X(t) - A(t)‖_F ≤ ρ/16` and `‖Ȧ‖_F ≤ μ`, and let
`Y = U S Vᵀ` solve the DLRA equation `Ẏ = P(Y) Ȧ` with `Y(0) = X(0)`. Then, for every
`t ∈ [0, T]`, `‖Y(t) - X(t)‖_F ≤ 2 β e^{β t} ∫₀ᵗ ‖X(s) - A(s)‖_F ds`, `β = 8 μ / ρ`. Neither
continuity of the derivative of `X` nor smallness of `‖Y - X‖_F` is assumed. It is the case
`F(t, Y) = Ȧ(t)` of `dlra_norm_sub_le_integral`. A bound of this kind is in [KochLubich2007]; the
constants `1/16`, `8` and `2` are those of this proof. -/
theorem dlra_norm_sub_truncation_le_integral {r : ℕ} (hr : 0 < r)
    {A A' X X' Y : ℝ → Matrix m n ℝ} {T μ ρ : ℝ} (hρ : 0 < ρ)
    (hA : ∀ t ∈ Icc 0 T, HasDerivAt A (A' t) t)
    (hμ : ∀ t ∈ Icc 0 T, ‖A' t‖ ≤ μ) (hXbest : ∀ t ∈ Icc 0 T, X t = truncation (A t) r)
    (hX : ∀ t ∈ Icc 0 T, HasDerivAt X (X' t) t)
    (hσ : ∀ t ∈ Icc 0 T, ρ ≤ (toEuclideanLin (A t)).singularValues (r - 1))
    (hd : ∀ t ∈ Icc 0 T, ‖X t - A t‖ ≤ ρ / 16)
    {U : ℝ → Matrix m (Fin r) ℝ} {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {V : ℝ → Matrix n (Fin r) ℝ}
    (hUV : ∀ t ∈ Icc 0 T, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧ Y t = U t * S t * (V t)ᵀ)
    (hY : ODESolution (fun t _ => tangentProj (U t) (V t) (A' t)) Y 0 T) (hY₀ : Y 0 = X 0) :
    ∀ t ∈ Icc 0 T, ‖Y t - X t‖ ≤
      2 * (8 * μ / ρ) * Real.exp (8 * μ / ρ * t) * ∫ s in (0 : ℝ)..t, ‖X s - A s‖ := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hμ0 : 0 ≤ μ := (norm_nonneg _).trans (hμ 0 ⟨le_rfl, hT⟩)
  have hfac : ∀ s ∈ Icc (0 : ℝ) T,
      (X s).rank = r ∧ ρ ≤ (toEuclideanLin (X s)).singularValues (r - 1) := fun s hs => by
    obtain ⟨U₀, V₀, σ₀, hU₀, hV₀, hσ₀, hXeq⟩ := truncation_factor hr hρ (hσ s hs)
    rw [← hXbest s hs] at hXeq
    refine ⟨(SVD.rank_eq_iff_exists_factor _).2 ⟨U₀, diagonal σ₀, V₀, hU₀, hV₀, ?_, hXeq⟩,
      SVD.le_singularValues_of_eq_mul hr hU₀ hV₀ hXeq
        (Curvature.diagonal_bounded_below hρ.le hσ₀)⟩
    rw [det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (lt_of_lt_of_le hρ (hσ₀ i)).ne'
  have hA' : ODESolution (fun t (_ : Matrix m n ℝ) => A' t) A 0 T :=
    ⟨fun s hs => (hA s hs).continuousAt.continuousWithinAt,
      fun s hs => (hA s (Ico_subset_Icc_self hs)).hasDerivWithinAt⟩
  have h := dlra_norm_sub_le_integral (F := fun t _ => A' t) (L := 0) (δ := 0) hρ le_rfl
    (fun t x y => by simp) hA' (fun s hs => hμ s (Ico_subset_Icc_self hs))
    (fun s hs => (hX s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hX s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (fun s hs => (hfac s hs).1) (fun s hs => (hfac s hs).2)
    (fun s hs => by rw [hXbest s hs]; exact tangentProjAt_truncation_sub_eq_zero _ _)
    (fun s hs => (hd s hs).trans (by linarith)) hUV hY (by rw [hY₀, sub_self, norm_zero]) t ht
  have hI : 0 ≤ ∫ s in (0 : ℝ)..t, ‖X s - A s‖ :=
    intervalIntegral.integral_nonneg ht.1 fun _ _ => norm_nonneg _
  have hq : 0 ≤ μ / ρ := div_nonneg hμ0 hρ.le
  have hexp : Real.exp ((0 + 6 * μ / ρ) * (t - 0)) ≤ Real.exp (8 * μ / ρ * t) := by
    refine Real.exp_le_exp.2 ?_
    have e1 : (0 + 6 * μ / ρ) * (t - 0) = 6 * (μ / ρ) * t := by ring
    have e2 : 8 * μ / ρ * t = 8 * (μ / ρ) * t := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right (by linarith) ht.1
  have hc : 0 + (0 + 4 * μ / ρ) * ∫ s in (0 : ℝ)..t, ‖X s - A s‖ ≤
      2 * (8 * μ / ρ) * ∫ s in (0 : ℝ)..t, ‖X s - A s‖ := by
    have e1 : 0 + (0 + 4 * μ / ρ) * ∫ s in (0 : ℝ)..t, ‖X s - A s‖ =
        4 * (μ / ρ) * ∫ s in (0 : ℝ)..t, ‖X s - A s‖ := by ring
    have e2 : 2 * (8 * μ / ρ) * ∫ s in (0 : ℝ)..t, ‖X s - A s‖ =
        16 * (μ / ρ) * ∫ s in (0 : ℝ)..t, ‖X s - A s‖ := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right (by linarith) hI
  calc ‖Y t - X t‖ ≤ _ := h
    _ ≤ Real.exp (8 * μ / ρ * t) * (2 * (8 * μ / ρ) * ∫ s in (0 : ℝ)..t, ‖X s - A s‖) :=
        mul_le_mul hexp hc (by positivity) (Real.exp_pos _).le
    _ = _ := by ring

end QuasiOptimal

/-! ### Examples

The namespace `QuasiOptimalityExamples` holds the facts on the rank-one matrices `c e₁ e₁ᵀ` of
`ℝ^{2×2}` that the examples of this file, of `LeanDLRA/DLRA/QuasiOptimalityTube.lean` and of
`LeanDLRA/DLRA/QuasiOptimalityGap.lean` use. -/

namespace QuasiOptimalityExamples

open scoped LeanDLRA.Frobenius

/-- The first unit column of `ℝ²` (`open QuasiOptimalityExamples` gives this notation). -/
scoped notation "e₁" => (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)

/-- The normal part `diag(0, 1/8)` of the examples. -/
local notation "N₈" => (!![0, 0; 0, 1 / 8] : Matrix (Fin 2) (Fin 2) ℝ)

/-- The curve `X t = (1 + t) e₁ e₁ᵀ` of the examples. -/
local notation "Xₑ" => fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)

/-- The curve `A t = X t + diag(0, 1/8)` of the examples. -/
local notation "Aₑ" => fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₈

/-- The field `F(t, Y) = e₁ e₁ᵀ` of the examples. -/
local notation "Fₑ" => fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => e₁ * e₁ᵀ

/-- `e₁` has an orthonormal column: `e₁ᵀ e₁ = 1`. -/
theorem e₁_transpose_mul_self : e₁ᵀ * e₁ = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- `c e₁ e₁ᵀ = e₁ (c • 1) e₁ᵀ`: a factorization with a `1 × 1` core. -/
theorem smul_e₁_mul (c : ℝ) :
    c • (e₁ * e₁ᵀ) = e₁ * (c • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * e₁ᵀ := by
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- The `1 × 1` core `c • 1` is invertible for `c ≠ 0`. -/
theorem isUnit_det_smul_one {c : ℝ} (hc : c ≠ 0) :
    IsUnit (c • (1 : Matrix (Fin 1) (Fin 1) ℝ)).det := by
  rw [det_smul, det_one, mul_one, Fintype.card_fin, pow_one]
  exact isUnit_iff_ne_zero.mpr hc

/-- `c e₁ e₁ᵀ` has rank `1` for `c ≠ 0`. -/
theorem rank_smul_e₁ {c : ℝ} (hc : c ≠ 0) : (c • (e₁ * e₁ᵀ)).rank = 1 :=
  (SVD.rank_eq_iff_exists_factor _).2 ⟨e₁, c • 1, e₁, e₁_transpose_mul_self,
    e₁_transpose_mul_self, isUnit_det_smul_one hc, smul_e₁_mul c⟩

/-- `σ₀(c e₁ e₁ᵀ) ≥ 1` for `c ≥ 1`. -/
theorem one_le_singularValues_smul_e₁ {c : ℝ} (hc : 1 ≤ c) :
    (1 : ℝ) ≤ (toEuclideanLin (c • (e₁ * e₁ᵀ))).singularValues (1 - 1) := by
  refine SVD.le_singularValues_of_eq_mul one_pos e₁_transpose_mul_self e₁_transpose_mul_self
    (smul_e₁_mul c) fun w => ?_
  rw [LinearEquiv.map_smul, toLpLin_one]
  change 1 * ‖w‖ ≤ ‖c • w‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
  nlinarith [norm_nonneg w]

/-- The tangent space projector at `c e₁ e₁ᵀ`, `c ≠ 0`, is that of the factors `e₁`, `e₁`. -/
theorem tangentProjAt_smul_e₁ {c : ℝ} (hc : c ≠ 0) :
    tangentProjAt (c • (e₁ * e₁ᵀ)) = tangentProj e₁ e₁ := by
  rw [smul_e₁_mul]
  exact tangentProjAt_eq_tangentProj e₁_transpose_mul_self e₁_transpose_mul_self
    (isUnit_det_smul_one hc)

/-- `e₁ e₁ᵀ` lies in the tangent space at `c e₁ e₁ᵀ`, `c ≠ 0`. -/
theorem tangentProjAt_smul_e₁_apply {c : ℝ} (hc : c ≠ 0) :
    tangentProjAt (c • (e₁ * e₁ᵀ)) (e₁ * e₁ᵀ) = e₁ * e₁ᵀ := by
  have h := tangentProjAt_self (c • (e₁ * e₁ᵀ))
  rw [map_smul] at h
  exact smul_right_injective _ hc h

private theorem tangentProjAt_smul_e₁_normal {c : ℝ} (hc : c ≠ 0) :
    tangentProjAt (c • (e₁ * e₁ᵀ)) N₈ = 0 := by
  have h1 : e₁ᵀ * N₈ = 0 := by
    ext i j
    fin_cases i
    fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h2 : N₈ * e₁ = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [tangentProjAt_smul_e₁ hc, tangentProj_apply, Matrix.mul_assoc e₁ e₁ᵀ N₈, h1, h2]
  simp

/-- `‖e₁ e₁ᵀ‖ ≤ 1`. -/
theorem norm_e₁_mul_le : ‖e₁ * e₁ᵀ‖ ≤ 1 := by
  have h : ‖e₁ * e₁ᵀ‖ ^ 2 = 1 := by
    rw [Curvature.frob_sq]
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  nlinarith [norm_nonneg (e₁ * e₁ᵀ)]

private theorem norm_N₈_le : ‖N₈‖ ≤ 1 / 8 := by
  have h : ‖N₈‖ ^ 2 = (1 / 8) ^ 2 := by
    rw [Curvature.frob_sq]
    norm_num [Fin.sum_univ_two]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp h.le

private theorem smul_e₁_add_eq (t : ℝ) :
    (1 + t) • (e₁ * e₁ᵀ) + N₈ = !![1 + t, 0; 0, 1 / 8] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.vecMul, dotProduct]

/-- `A t = (1 + t) • e₁ e₁ᵀ + diag(0, 1/8)` is bounded below by `1/8`. -/
private theorem norm_mul_ge (t : ℝ) (ht : 0 ≤ t) (B : Matrix (Fin 2) Unit ℝ) :
    1 / 8 * ‖B‖ ≤ ‖((1 + t) • (e₁ * e₁ᵀ) + N₈) * B‖ := by
  rw [smul_e₁_add_eq]
  have hsq : (1 / 8 * ‖B‖) ^ 2 ≤ ‖!![1 + t, 0; 0, 1 / 8] * B‖ ^ 2 := by
    rw [mul_pow, Curvature.frob_sq, Curvature.frob_sq]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    nlinarith [sq_nonneg (B 0 ()), sq_nonneg (B 1 ()), sq_nonneg t,
      mul_nonneg ht (sq_nonneg (B 0 ())), mul_nonneg (mul_nonneg ht ht) (sq_nonneg (B 0 ()))]
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp hsq

/-- `X t = (1 + t) • e₁ e₁ᵀ` is a best approximation of rank at most `1` of
`A t = X t + diag(0, 1/8)`: `‖A t - X t‖ ≤ 1/8 ≤ σ₁(A t) ≤ ‖A t - Z‖` (Eckart–Young). -/
private theorem isBest_example (t : ℝ) (ht : 0 ≤ t) (Z : Matrix (Fin 2) (Fin 2) ℝ)
    (hZ : Z.rank ≤ 1) :
    ‖(1 + t) • (e₁ * e₁ᵀ) + N₈ - (1 + t) • (e₁ * e₁ᵀ)‖ ≤
      ‖(1 + t) • (e₁ * e₁ᵀ) + N₈ - Z‖ := by
  rw [add_sub_cancel_left]
  have h2 : (1 / 8 : ℝ) ≤ (toEuclideanLin ((1 + t) • (e₁ * e₁ᵀ) + N₈)).singularValues 1 := by
    have h := (SVD.forall_mul_norm_le_iff ((1 + t) • (e₁ * e₁ᵀ) + N₈) (ρ := 1 / 8)).mp
      fun v => by
        rw [Curvature.norm_toEuclideanLin_eq_frob, Curvature.norm_eq_frob_replicateCol v]
        exact norm_mul_ge t ht _
    rw [Fintype.card_fin] at h
    exact h
  have h3 := EckartYoung.singularValues_le_specNorm_sub ((1 + t) • (e₁ * e₁ᵀ) + N₈) Z hZ
  have h4 := Curvature.specNorm_le_frob ((1 + t) • (e₁ * e₁ᵀ) + N₈ - Z)
  linarith [norm_N₈_le]

/-- The curve `t ↦ (c + t) e₁ e₁ᵀ` has the derivative `e₁ e₁ᵀ`. -/
theorem hasDerivAt_smul_e₁ (c t : ℝ) :
    HasDerivAt (fun t : ℝ => (c + t) • (e₁ * e₁ᵀ)) (e₁ * e₁ᵀ) t := by
  simpa using ((hasDerivAt_id t).const_add c).smul_const (e₁ * e₁ᵀ)

private theorem hasDerivAt_smul_e₁_add (t : ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₈) (e₁ * e₁ᵀ) t := by
  simpa using (hasDerivAt_smul_e₁ 1 t).add_const N₈

private theorem odeSolution_smul_e₁_add :
    ODESolution (fun _ _ => e₁ * e₁ᵀ) (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₈) 0 1 :=
  ⟨fun s _ => (hasDerivAt_smul_e₁_add s).continuousAt.continuousWithinAt,
    fun s _ => (hasDerivAt_smul_e₁_add s).hasDerivWithinAt⟩

private theorem hyps_smul_e₁ {t : ℝ} (ht : 0 ≤ t) :
    ((1 + t) • (e₁ * e₁ᵀ)).rank = 1 ∧
    (1 : ℝ) ≤ (toEuclideanLin ((1 + t) • (e₁ * e₁ᵀ))).singularValues (1 - 1) ∧
    tangentProjAt ((1 + t) • (e₁ * e₁ᵀ)) ((1 + t) • (e₁ * e₁ᵀ) + N₈ - (1 + t) • (e₁ * e₁ᵀ)) = 0 ∧
    ‖(1 + t) • (e₁ * e₁ᵀ) - ((1 + t) • (e₁ * e₁ᵀ) + N₈)‖ ≤ 1 / 4 ∧
    tangentProjAt ((1 + t) • (e₁ * e₁ᵀ)) (e₁ * e₁ᵀ) = e₁ * e₁ᵀ := by
  have hc : (1 + t) ≠ 0 := ne_of_gt (by linarith)
  refine ⟨rank_smul_e₁ hc, one_le_singularValues_smul_e₁ (by linarith), ?_, ?_,
    tangentProjAt_smul_e₁_apply hc⟩
  · rw [add_sub_cancel_left]
    exact tangentProjAt_smul_e₁_normal hc
  · rw [sub_add_cancel_left, norm_neg]
    linarith [norm_N₈_le]

/-- `norm_tangentProjAt_sub_le_of_hasDerivWithinAt`, `norm_le_of_tangentProjAt_sub_eq_zero` and
`norm_sub_tangentProjAt_le_of_tangentProjAt_sub_eq_zero` for the curves
`X t = (1 + t) e₁ e₁ᵀ` and `A t = X t + diag(0, 1/8)` (`r = 1`, `ρ = μ = 1`, `A ≠ X`) at `t = 0`
within `[0, 1]`. -/
example :
    ‖tangentProjAt (((1 : ℝ) + 0) • (e₁ * e₁ᵀ)) (e₁ * e₁ᵀ - e₁ * e₁ᵀ)‖ ≤
      2 * 1⁻¹ * ‖e₁ * e₁ᵀ‖ * ‖((1 : ℝ) + 0) • (e₁ * e₁ᵀ) + N₈ - ((1 : ℝ) + 0) • (e₁ * e₁ᵀ)‖ ∧
    ‖e₁ * e₁ᵀ‖ ≤ 2 * 1 ∧
    ‖e₁ * e₁ᵀ - tangentProjAt (((1 : ℝ) + 0) • (e₁ * e₁ᵀ)) (e₁ * e₁ᵀ)‖ ≤
      4 * 1 / 1 * ‖((1 : ℝ) + 0) • (e₁ * e₁ᵀ) + N₈ - ((1 : ℝ) + 0) • (e₁ * e₁ᵀ)‖ := by
  have hs : (𝓝[Set.Icc (0 : ℝ) 1 \ {0}] 0).NeBot := by
    rw [Icc_sdiff_left]
    exact left_nhdsWithin_Ioc_neBot one_pos
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hA := (hasDerivAt_smul_e₁_add 0).hasDerivWithinAt (s := Set.Icc (0 : ℝ) 1)
  have hX := (hasDerivAt_smul_e₁ 1 0).hasDerivWithinAt (s := Set.Icc (0 : ℝ) 1)
  have hr : ∀ u ∈ Set.Icc (0 : ℝ) 1, ((fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) u).rank = 1 :=
    fun u hu => (hyps_smul_e₁ hu.1).1
  have hσ : ∀ u ∈ Set.Icc (0 : ℝ) 1, (1 : ℝ) ≤
      (toEuclideanLin ((fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) u)).singularValues (1 - 1) :=
    fun u hu => (hyps_smul_e₁ hu.1).2.1
  have ho : ∀ u ∈ Set.Icc (0 : ℝ) 1, tangentProjAt ((fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) u)
      ((fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₈) u - (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) u) = 0 :=
    fun u hu => (hyps_smul_e₁ hu.1).2.2.1
  have hd := (hyps_smul_e₁ (le_refl (0 : ℝ))).2.2.2.1
  have r1 := norm_tangentProjAt_sub_le_of_hasDerivWithinAt hA hX h0 hs one_pos hr (hσ 0 h0) ho
  have r2 := norm_le_of_tangentProjAt_sub_eq_zero hA hX h0 hs one_pos hr hσ ho norm_e₁_mul_le hd
  have r3 := norm_sub_tangentProjAt_le_of_tangentProjAt_sub_eq_zero hA hX h0 hs one_pos hr hσ ho
    norm_e₁_mul_le hd
  exact ⟨r1, r2, r3⟩

/-- The hypotheses of the four quasi-optimality theorems for `X t = Y t = (1 + t) e₁ e₁ᵀ` (factors
`U = V = e₁`, `S t = 1 + t`), `A t = X t + diag(0, 1/8)` (`A ≠ X`), `F(t, Y) = e₁ e₁ᵀ` (`L = 0`),
`r = 1`, `ρ = μ = 1`, `δ = 0` on `[0, 1]`; `X t` is a best approximation of rank `1` of `A t`. -/
example :
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(1 + t) • (e₁ * e₁ᵀ) - (1 + t) • (e₁ * e₁ᵀ)‖ ≤
      Real.exp ((0 + 6 * 1 / 1) * (t - 0)) * (0 + (0 + 4 * 1 / 1) *
        ∫ s in (0 : ℝ)..t, ‖(1 + s) • (e₁ * e₁ᵀ) - ((1 + s) • (e₁ * e₁ᵀ) + N₈)‖)) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(1 + t) • (e₁ * e₁ᵀ) - ((1 + t) • (e₁ * e₁ᵀ) + N₈)‖ ≤
      ‖(1 + t) • (e₁ * e₁ᵀ) - ((1 + t) • (e₁ * e₁ᵀ) + N₈)‖ +
      Real.exp ((0 + 6 * 1 / 1) * (t - 0)) * (0 + (0 + 4 * 1 / 1) *
        ∫ s in (0 : ℝ)..t, ‖(1 + s) • (e₁ * e₁ᵀ) - ((1 + s) • (e₁ * e₁ᵀ) + N₈)‖)) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(1 + t) • (e₁ * e₁ᵀ) - (1 + t) • (e₁ * e₁ᵀ)‖ ≤
      Real.exp ((0 + 6 * 1 / 1) * (t - 0)) * (0 + (0 + 4 * 1 / 1) *
        ∫ s in (0 : ℝ)..t, ‖(1 + s) • (e₁ * e₁ᵀ) - ((1 + s) • (e₁ * e₁ᵀ) + N₈)‖)) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(1 + t) • (e₁ * e₁ᵀ) - (1 + t) • (e₁ * e₁ᵀ)‖ ≤
      Real.exp ((0 + 6 * 1 / 1) * (t - 0)) * (0 + (0 + 4 * 1 / 1) *
        ∫ s in (0 : ℝ)..t, ‖(1 + s) • (e₁ * e₁ᵀ) - ((1 + s) • (e₁ * e₁ᵀ) + N₈)‖)) := by
  have hF : IsLipschitzField (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => e₁ * e₁ᵀ) 0 :=
    fun _ _ _ => by simp
  have hμ : ∀ t ∈ Ico (0 : ℝ) 1, ‖(fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => e₁ * e₁ᵀ) t
      ((fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₈) t)‖ ≤ 1 := fun _ _ => norm_e₁_mul_le
  have hXc : ContinuousOn (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) (Set.Icc 0 1) :=
    fun s _ => (hasDerivAt_smul_e₁ 1 s).continuousAt.continuousWithinAt
  have hX : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ))
      ((fun _ : ℝ => e₁ * e₁ᵀ) t) (Ici t) t := fun s _ => (hasDerivAt_smul_e₁ 1 s).hasDerivWithinAt
  have hXr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((1 + t) • (e₁ * e₁ᵀ)).rank = 1 :=
    fun t ht => (hyps_smul_e₁ ht.1).1
  have hσ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (1 : ℝ) ≤ (toEuclideanLin ((1 + t) • (e₁ * e₁ᵀ))).singularValues (1 - 1) :=
    fun t ht => (hyps_smul_e₁ ht.1).2.1
  have ho : ∀ t ∈ Set.Icc (0 : ℝ) 1, tangentProjAt ((1 + t) • (e₁ * e₁ᵀ))
      ((1 + t) • (e₁ * e₁ᵀ) + N₈ - (1 + t) • (e₁ * e₁ᵀ)) = 0 :=
    fun t ht => (hyps_smul_e₁ ht.1).2.2.1
  have hd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(1 + t) • (e₁ * e₁ᵀ) - ((1 + t) • (e₁ * e₁ᵀ) + N₈)‖ ≤ 1 / 4 :=
    fun t ht => (hyps_smul_e₁ ht.1).2.2.2.1
  have hUV : ∀ t ∈ Set.Icc (0 : ℝ) 1, (e₁)ᵀ * e₁ = 1 ∧ (e₁)ᵀ * e₁ = 1 ∧
      (1 + t) • (e₁ * e₁ᵀ) = e₁ * ((1 + t) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * e₁ᵀ :=
    fun t _ => ⟨e₁_transpose_mul_self, e₁_transpose_mul_self, smul_e₁_mul _⟩
  have hYf : ODESolution (fun t x => tangentProj ((fun _ : ℝ => e₁) t) ((fun _ : ℝ => e₁) t)
      ((fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => e₁ * e₁ᵀ) t x))
      (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) 0 1 := by
    refine ⟨hXc, fun s hs => ?_⟩
    have h := (hasDerivAt_smul_e₁ 1 s).hasDerivWithinAt (s := Ici s)
    convert h using 1
    change tangentProj e₁ e₁ (e₁ * e₁ᵀ) = e₁ * e₁ᵀ
    rw [← tangentProjAt_smul_e₁ (ne_of_gt (by linarith [hs.1] : (0 : ℝ) < 1 + s))]
    exact (hyps_smul_e₁ hs.1).2.2.2.2
  have hYd : IsDLRASolution 1 (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => e₁ * e₁ᵀ)
      (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) 0 1 := by
    refine ⟨⟨hXc, fun s hs => ?_⟩, hXr⟩
    have h := (hasDerivAt_smul_e₁ 1 s).hasDerivWithinAt (s := Ici s)
    convert h using 1
    exact (hyps_smul_e₁ hs.1).2.2.2.2
  have hbest : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((1 + t) • (e₁ * e₁ᵀ)).rank ≤ 1 ∧
      ∀ Z : Matrix (Fin 2) (Fin 2) ℝ, Z.rank ≤ 1 →
        ‖(1 + t) • (e₁ * e₁ᵀ) + N₈ - (1 + t) • (e₁ * e₁ᵀ)‖ ≤
          ‖(1 + t) • (e₁ * e₁ᵀ) + N₈ - Z‖ :=
    fun t ht => ⟨(hXr t ht).le, isBest_example t ht.1⟩
  have h0 : ‖(fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) 0 - (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) 0‖
      ≤ 0 := by simp
  exact ⟨dlra_norm_sub_le_integral (F := Fₑ) (A := Aₑ) (X := Xₑ) (X' := fun _ => e₁ * e₁ᵀ)
      (Y := Xₑ) (U := fun _ => e₁) (S := fun t => (1 + t) • 1) (V := fun _ => e₁) one_pos le_rfl
      hF odeSolution_smul_e₁_add hμ hXc hX hXr hσ ho hd hUV hYf h0,
    dlra_norm_sub_le_add_integral (F := Fₑ) (A := Aₑ) (X := Xₑ) (X' := fun _ => e₁ * e₁ᵀ)
      (Y := Xₑ) (U := fun _ => e₁) (S := fun t => (1 + t) • 1) (V := fun _ => e₁) one_pos le_rfl
      hF odeSolution_smul_e₁_add hμ hXc hX hXr hσ ho hd hUV hYf h0,
    hYd.norm_sub_le_integral (A := Aₑ) (X := Xₑ) (X' := fun _ => e₁ * e₁ᵀ) one_pos le_rfl hF
      odeSolution_smul_e₁_add hμ hXc hX hXr hσ ho hd h0,
    hYd.norm_sub_le_integral_of_forall_norm_sub_le (A := Aₑ) (X := Xₑ)
      (X' := fun _ => e₁ * e₁ᵀ) one_pos le_rfl hF odeSolution_smul_e₁_add hμ hXc hX hbest hσ hd
      h0⟩

/-- The normal part `diag(0, 1/16)` of the truncation example. -/
local notation "N₁₆" => (!![0, 0; 0, 1 / 16] : Matrix (Fin 2) (Fin 2) ℝ)

private theorem smul_e₁_add_N₁₆ (t : ℝ) :
    (1 + t) • (e₁ * e₁ᵀ) + N₁₆ = !![1 + t, 0; 0, 1 / 16] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.vecMul, dotProduct]

private theorem smul_e₁_eq (t : ℝ) : (1 + t) • (e₁ * e₁ᵀ) = !![1 + t, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.vecMul, dotProduct]

private theorem norm_N₁₆_le : ‖N₁₆‖ ≤ 1 / 16 := by
  have h : ‖N₁₆‖ ^ 2 = (1 / 16) ^ 2 := by
    rw [Curvature.frob_sq]
    norm_num [Fin.sum_univ_two]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp h.le

/-- `σ₀(diag(c, 1/16)) ≥ c`: the matrix maps `e₁` to `c e₁`. -/
private theorem le_singularValues_diag {c : ℝ} :
    c ≤ (toEuclideanLin (!![c, 0; 0, 1 / 16] : Matrix (Fin 2) (Fin 2) ℝ)).singularValues 0 := by
  rw [← EckartYoung.specNorm_eq_singularValues_zero]
  have hs : toEuclideanLin (!![c, 0; 0, 1 / 16] : Matrix (Fin 2) (Fin 2) ℝ)
      (EuclideanSpace.single 0 1) = EuclideanSpace.single 0 c := by
    ext i
    fin_cases i <;> simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply]
  have h := Curvature.norm_toEuclideanLin_le (!![c, 0; 0, 1 / 16] : Matrix (Fin 2) (Fin 2) ℝ)
    (EuclideanSpace.single 0 1)
  rw [hs] at h
  exact (le_abs_self c).trans (by simpa using h)

/-- **The rank-one truncation of `diag(c, 1/16)`, `c ≥ 1`**, is `diag(c, 0)`: the top right
singular vector is `± e₁`, because `σ₀² ≥ c² > 1/256`. -/
private theorem truncation_diag {c : ℝ} (hc : 1 ≤ c) :
    EckartYoung.truncation (!![c, 0; 0, 1 / 16] : Matrix (Fin 2) (Fin 2) ℝ) 1 =
      !![c, 0; 0, 0] := by
  set A : Matrix (Fin 2) (Fin 2) ℝ := !![c, 0; 0, 1 / 16] with hA
  have hAA : Aᵀ * A = !![c * c, 0; 0, 1 / 256] := by
    rw [hA]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  have hσ : c ≤ (toEuclideanLin A).singularValues 0 := le_singularValues_diag
  let i0 : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))) := ⟨0, by simp⟩
  let j0 : {i : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))) // (i : ℕ) < 1} :=
    ⟨i0, Nat.zero_lt_one⟩
  have hP : EckartYoung.topRightSingularVectors A 1 *
      (EckartYoung.topRightSingularVectors A 1)ᵀ =
      Matrix.of fun a b => EckartYoung.rightSingularVectors A i0 a *
        EckartYoung.rightSingularVectors A i0 b := by
    ext a b
    rw [Matrix.mul_apply, Fintype.sum_eq_single j0]
    · rfl
    · intro x hx
      exact absurd (Subtype.ext (Fin.ext (by have := x.2; change (x.1 : ℕ) = 0; omega))) hx
  have hE := EckartYoung.transpose_mul_self_mulVec_rightSingularVectors A i0
  rw [hAA] at hE
  have hn : EckartYoung.rightSingularVectors A i0 0 ^ 2 +
      EckartYoung.rightSingularVectors A i0 1 ^ 2 = 1 := by
    have h1 := (EckartYoung.rightSingularVectors A).orthonormal.1 i0
    have h2 : ‖EckartYoung.rightSingularVectors A i0‖ ^ 2 =
        EckartYoung.rightSingularVectors A i0 0 ^ 2 +
          EckartYoung.rightSingularVectors A i0 1 ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
      simp [Real.norm_eq_abs, sq_abs]
    rw [h1] at h2
    linarith
  have h1 := congrFun hE 1
  simp only [mulVec, dotProduct, Fin.isValue, of_apply, cons_val', cons_val_fin_one,
    cons_val_one, Fin.sum_univ_two, cons_val_zero, zero_mul, zero_add, Pi.smul_apply,
    smul_eq_mul] at h1
  have hσ' : c ≤ (toEuclideanLin A).singularValues ↑i0 := hσ
  have hs2 : 1 ≤ (toEuclideanLin A).singularValues ↑i0 ^ 2 := by nlinarith
  have hx1 : EckartYoung.rightSingularVectors A i0 1 = 0 := by
    have hm : ((toEuclideanLin A).singularValues ↑i0 ^ 2 - 1 / 256) *
        EckartYoung.rightSingularVectors A i0 1 = 0 := by
      linear_combination (-1 : ℝ) * h1
    rcases mul_eq_zero.1 hm with h | h
    · linarith
    · exact h
  have hx00 : EckartYoung.rightSingularVectors A i0 0 *
      EckartYoung.rightSingularVectors A i0 0 = 1 := by
    rw [hx1] at hn
    nlinarith
  unfold EckartYoung.truncation
  rw [Matrix.mul_assoc, hP]
  generalize EckartYoung.rightSingularVectors A i0 = e at hx1 hx00 ⊢
  rw [hA]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hx1, hx00]

/-- `dlra_norm_sub_truncation_le_integral` for `2 × 2` matrices, `r = 1`,
`A t = (1 + t) e₁ e₁ᵀ + diag(0, 1/16)` on `[0, 1]` (`Ȧ = e₁ e₁ᵀ`, `μ = ρ = 1`): the truncation
`X t = T₁(A t) = (1 + t) e₁ e₁ᵀ` differs from `A t` by `‖X t - A t‖ = 1/16 = ρ/16`, so the
right-hand side is `16 e^{8t} t/16 > 0` for `t > 0`. Here `Ȧ` is tangent at `X t`, so the DLRA
solution `Y = e₁ ((1 + t) • 1) e₁ᵀ` is `X` itself and the left-hand side is `0`. -/
example : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ‖(1 + t) • (e₁ * e₁ᵀ) - (1 + t) • (e₁ * e₁ᵀ)‖ ≤
      2 * (8 * 1 / 1) * Real.exp (8 * 1 / 1 * t) * ∫ s in (0 : ℝ)..t,
        ‖(1 + s) • (e₁ * e₁ᵀ) - ((1 + s) • (e₁ * e₁ᵀ) + N₁₆)‖ := by
  have hA : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₁₆) (e₁ * e₁ᵀ) t :=
    fun t => by simpa using (hasDerivAt_smul_e₁ 1 t).add_const N₁₆
  refine dlra_norm_sub_truncation_le_integral (r := 1)
    (A := fun t => (1 + t) • (e₁ * e₁ᵀ) + N₁₆) (X := fun t => (1 + t) • (e₁ * e₁ᵀ))
    (Y := fun t => (1 + t) • (e₁ * e₁ᵀ)) (A' := fun _ => e₁ * e₁ᵀ) (X' := fun _ => e₁ * e₁ᵀ)
    (U := fun _ => e₁) (V := fun _ => e₁) (S := fun t => (1 + t) • 1) one_pos one_pos
    (fun t _ => hA t) (fun _ _ => norm_e₁_mul_le) (fun t ht => ?_)
    (fun t _ => hasDerivAt_smul_e₁ 1 t) (fun t ht => ?_) (fun t _ => ?_)
    (fun t _ => ⟨e₁_transpose_mul_self, e₁_transpose_mul_self, smul_e₁_mul _⟩)
    ⟨fun s _ => (hasDerivAt_smul_e₁ 1 s).continuousAt.continuousWithinAt, fun s hs => ?_⟩ rfl
  · rw [smul_e₁_add_N₁₆, truncation_diag (by linarith [ht.1]), smul_e₁_eq]
  · change (1 : ℝ) ≤ (toEuclideanLin ((1 + t) • (e₁ * e₁ᵀ) + N₁₆)).singularValues 0
    rw [smul_e₁_add_N₁₆]
    exact le_trans (by linarith [ht.1]) le_singularValues_diag
  · rw [sub_add_cancel_left, norm_neg]
    exact norm_N₁₆_le
  · have h := (hasDerivAt_smul_e₁ 1 s).hasDerivWithinAt (s := Ici s)
    convert h using 1
    rw [← tangentProjAt_smul_e₁ (ne_of_gt (by linarith [hs.1] : (0 : ℝ) < 1 + s))]
    exact (hyps_smul_e₁ hs.1).2.2.2.2

end QuasiOptimalityExamples

end LeanDLRA
