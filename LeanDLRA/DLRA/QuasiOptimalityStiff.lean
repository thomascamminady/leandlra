import LeanDLRA.DLRA.QuasiOptimalityNormalVelocity

/-!
# Quasi-optimality of matrix DLRA for fields with a tangential stiff part

Let `F(t, Z) = S(t, Z) + G(t, Z)`, where `S` maps every matrix of rank `r` into the tangent space
of the manifold of rank-`r` matrices at that matrix. The main case is the Sylvester operator
`S(Z) = M Z + Z N` of a discretised diffusion or transport in two variables, whose norm grows
with the mesh refinement. The tangent projector does not see `S`, so the DLRA solution solves
`Ẏ = S(t, Y) + P(Y) G(t, Y)`. This file has quasi-optimality bounds in which `S` enters only
through the one-sided Lipschitz constant `ℓ` of `F` and through the defect of the reference
curve; the Lipschitz constant and the size of `S` do not occur. With

  `k = ℓ + ν/ρ + ν/(ρ - ε) + μ ε/ρ² + L ε/ρ`,

`ν ≥ ‖(1 - P(X t)) G(t, A t)‖`, `μ ≥ ‖G(t, A t)‖`, `L` the Lipschitz constant of `G`,
`ρ ≤ σ_{r-1}(X t)` and `ε < ρ` the radius of a tube around `X` that contains `Y`,

  `‖Y t - X t‖ ≤ e^{∫ₐᵗ k} δ + ∫ₐᵗ e^{∫ₛᵗ k} (L ‖X s - A s‖ + d s) ds`,

`d ≥ ‖S(t, X t) + P(X t) G(t, A t) - Ẋ t‖`. The constant `ℓ` may be negative. All norms of
matrices are Frobenius norms.

## Main results

* `IsDLRASolution.norm_sub_le_integral_exp_integral_of_tangent_add_of_norm_sub_le`: the bound
  for a DLRA solution that stays in the tube `‖Y t - X t‖ ≤ ε t`.
* `IsDLRASolution.norm_sub_le_integral_exp_integral_of_tangent_add_of_integral_lt`: the bound
  without a hypothesis on `Y` besides the initial error, if the bound itself stays below `ε`.
* `IsDLRASolution.norm_sub_le_integral_exp_integral_of_tangent_add_self_of_integral_lt`: the
  case `A = X`, with the source `d` alone; for `S = 0` a bound for every one-sided Lipschitz
  field.
* `IsDLRASolution.norm_sub_le_integral_exp_integral_of_sylvester_add_of_integral_lt`: the case
  `F(t, Z) = M Z + Z N + G(t, Z)`.
* `norm_add_tangentProjAt_sub_le_norm_tangentProjAt_add_sub_add`: the defect `d` is at most the
  defect `‖P(X) (S(A) + G(A)) - Ẋ‖` of `X` against the whole field plus `‖P(X) (S(A) - S(X))‖`.
* `IsOrthProj.norm_apply_le_mul_of_adjoint`: for a linear `S` with adjoint `S'` and `R` normal
  to the range of an orthogonal projector `P`, `‖P S R‖ ≤ κ ‖R‖` if `‖(1 - P) S' P w‖ ≤ κ ‖w‖`.

## Implementation notes

The derivative of `Y - X` is split as

  `(F(Y) - F(X)) - (1 - P(Y)) (G(Y) - G(X)) + P(Y) (G(X) - G(A)) + (P(Y) - P(X)) G(A)`
  `+ (S(X) + P(X) G(A) - Ẋ)`.

The first term is tested with `Y - X` and gives `ℓ`; in the second term the normal component
`(1 - P(Y)) (Y - X)` is of second order, which gives `L ε/ρ`; the fourth term is the term of
`inner_sub_tangentProjAt_sub_le_of_norm_sub_lt` for the field `G` alone. The curve `A` is any
continuous curve; for `A = X` the source is the defect of `X` in the projected equation. If `A`
solves `Ȧ = F(t, A)` and `X t` is the truncated singular value decomposition of `A t`, the last
two results bound `d` by the defect of the truncation
(`norm_tangentProjAt_truncation_sub_fderiv_le_div_sub_mul_norm_pinv`) plus `κ ‖A - X‖`, where `κ`
measures how far the tangent space at `X` is from being invariant under the adjoint of `S`.

## References

* [KochLubich2007]
* [KieriVandereycken2019]
* [CarrelVandereycken2023]
-/

open Set Finset Matrix Filter
open scoped Topology RealInnerProductSpace

namespace LeanDLRA

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **An operator applied to a normal vector, projected back.** Let `P` be an orthogonal
projector, `T` a map with adjoint `T'` (`⟪T z, w⟫ = ⟪z, T' w⟫`), and `κ ≥ 0` with
`‖(1 - P) T' P w‖ ≤ κ ‖w‖` for all `w`. Then `‖P T x‖ ≤ κ ‖x‖` for every `x` with `P x = 0`:
only the part of `T'` that leads out of the range of `P` enters. -/
theorem IsOrthProj.norm_apply_le_mul_of_adjoint {P : E →L[ℝ] E} (hP : IsOrthProj P)
    {T T' : E → E} (hT : ∀ z w, ⟪T z, w⟫ = ⟪z, T' w⟫) {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : ∀ w, ‖T' (P w) - P (T' (P w))‖ ≤ κ * ‖w‖) {x : E} (hx : P x = 0) :
    ‖P (T x)‖ ≤ κ * ‖x‖ := by
  have hPw : P (P (T x)) = P (T x) := hP.idem _
  have h3 : ⟪P (T x), P (T x)⟫ = ⟪T x, P (T x)⟫ := by rw [hP.symm, hPw]
  have h2 : ⟪x, P (T' (P (P (T x))))⟫ = 0 := by rw [← hP.symm, hx, inner_zero_left]
  have h1 : ‖P (T x)‖ ^ 2 = ⟪x, T' (P (P (T x))) - P (T' (P (P (T x))))⟫ := by
    rw [inner_sub_right, h2, sub_zero, hPw, ← hT, ← h3, real_inner_self_eq_norm_sq]
  have h4 := (real_inner_le_norm x (T' (P (P (T x))) - P (T' (P (P (T x)))))).trans
    (mul_le_mul_of_nonneg_left (hκ (P (T x))) (norm_nonneg x))
  rw [← h1] at h4
  rcases eq_or_lt_of_le (norm_nonneg (P (T x))) with h0 | hpos
  · rw [← h0]
    exact mul_nonneg hκ0 (norm_nonneg x)
  · by_contra h
    rw [not_le] at h
    nlinarith [mul_lt_mul_of_pos_right h hpos]

end Abstract

section Stiff

open scoped LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- **The defect of a curve for a field with a tangential part.** If `P(X) S_X = S_X`, then for
all matrices `S_A`, `G_A`, `X'`

  `‖S_X + P(X) G_A - X'‖ ≤ ‖P(X) (S_A + G_A) - X'‖ + ‖P(X) (S_A - S_X)‖`.

With `S_X = S(X)`, `S_A = S(A)`, `G_A = G(A)`: the defect of `X` in the bounds of this file is
at most its defect against the whole field at `A` plus the tangential part of `S(A) - S(X)`. -/
theorem norm_add_tangentProjAt_sub_le_norm_tangentProjAt_add_sub_add {X SX : Matrix m n ℝ}
    (hS : tangentProjAt X SX = SX) (SA GA X' : Matrix m n ℝ) :
    ‖SX + tangentProjAt X GA - X'‖ ≤
      ‖tangentProjAt X (SA + GA) - X'‖ + ‖tangentProjAt X (SA - SX)‖ := by
  have e : SX + tangentProjAt X GA - X' =
      (tangentProjAt X (SA + GA) - X') - tangentProjAt X (SA - SX) := by
    rw [map_add, map_sub, hS]
    abel
  rw [e]
  exact norm_sub_le _ _

/-- **Quasi-optimality of matrix DLRA for a field with a tangential part, tube form.** Let
`F(t, Z) = S(t, Z) + G(t, Z)` be one-sided Lipschitz with the constant `ℓ` (of any sign) and `G`
be `L`-Lipschitz. Let `Y` be a DLRA solution of rank `r` of `Ẏ = P(Y) F(t, Y)` on `[a, b]` with
`P(Y t) S(t, Y t) = S(t, Y t)`, `A` a continuous curve and `X` a continuous curve of matrices of
rank `r` with right derivatives `X'`. Let `ρ`, `μ`, `ν`, `d`, `ε` be continuous on `[a, b]` with
`ρ t ≤ σ_{r-1}(X t)`, `‖G(t, A t)‖ ≤ μ t`, `‖(1 - P(X t)) G(t, A t)‖ ≤ ν t`,
`‖S(t, X t) + P(X t) G(t, A t) - X' t‖ ≤ d t` and `0 ≤ ε t < ρ t`. If `‖Y t - X t‖ ≤ ε t` on
`[a, b)` and `‖Y a - X a‖ ≤ δ`, then with `k = ℓ + ν/ρ + ν/(ρ - ε) + μ ε/ρ² + L ε/ρ`, for
`t ∈ [a, b]`

  `‖Y t - X t‖ ≤ e^{∫ₐᵗ k} δ + ∫ₐᵗ e^{∫ₛᵗ k} (L ‖X s - A s‖ + d s) ds`.

Neither a Lipschitz constant nor a bound of `S` enters. -/
theorem IsDLRASolution.norm_sub_le_integral_exp_integral_of_tangent_add_of_norm_sub_le {r : ℕ}
    {F S G : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A X X' Y : ℝ → Matrix m n ℝ}
    {ρ μ ν d ε : ℝ → ℝ} {a b ℓ L δ : ℝ} (hY : IsDLRASolution r F Y a b)
    (hFS : ∀ t Z, F t Z = S t Z + G t Z)
    (hS : ∀ t ∈ Ico a b, tangentProjAt (Y t) (S t (Y t)) = S t (Y t))
    (hℓ : IsOneSidedLipschitzField F ℓ) (hL : 0 ≤ L) (hG : IsLipschitzField G L)
    (hAc : ContinuousOn A (Icc a b))
    (hρc : ContinuousOn ρ (Icc a b)) (hμc : ContinuousOn μ (Icc a b))
    (hνc : ContinuousOn ν (Icc a b)) (hdc : ContinuousOn d (Icc a b))
    (hεc : ContinuousOn ε (Icc a b)) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ t ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hμ : ∀ t ∈ Ico a b, ‖G t (A t)‖ ≤ μ t)
    (hν : ∀ t ∈ Ico a b, ‖G t (A t) - tangentProjAt (X t) (G t (A t))‖ ≤ ν t)
    (hd : ∀ t ∈ Ico a b, ‖S t (X t) + tangentProjAt (X t) (G t (A t)) - X' t‖ ≤ d t)
    (hε0 : ∀ t ∈ Icc a b, 0 ≤ ε t) (hερ : ∀ t ∈ Icc a b, ε t < ρ t)
    (htube : ∀ t ∈ Ico a b, ‖Y t - X t‖ ≤ ε t) (hδ : ‖Y a - X a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp (∫ u in a..t,
        (ℓ + ν u / ρ u + ν u / (ρ u - ε u) + μ u * ε u / ρ u ^ 2 + L * ε u / ρ u)) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t,
          (ℓ + ν u / ρ u + ν u / (ρ u - ε u) + μ u * ε u / ρ u ^ 2 + L * ε u / ρ u)) *
          (L * ‖X s - A s‖ + d s) := by
  intro t0 ht0
  rcases eq_or_lt_of_le ht0.1 with h0 | hpos
  · subst h0
    simpa using hδ
  have hab : a < b := hpos.trans_le ht0.2
  have hρpos : ∀ u ∈ Icc a b, 0 < ρ u := fun u hu => (hε0 u hu).trans_lt (hερ u hu)
  have hIcc : Icc a t0 ⊆ Icc a b := Icc_subset_Icc_right ht0.2
  have hIco : ∀ s ∈ Ico a t0, s ∈ Ico a b := fun s hs => ⟨hs.1, hs.2.trans_le ht0.2⟩
  have hkOn : ContinuousOn
      (fun u => ℓ + ν u / ρ u + ν u / (ρ u - ε u) + μ u * ε u / ρ u ^ 2 + L * ε u / ρ u)
      (Icc a b) :=
    (((continuousOn_const.add (hνc.div hρc fun u hu => (hρpos u hu).ne')).add
      (hνc.div (hρc.sub hεc) fun u hu => (sub_pos.2 (hερ u hu)).ne')).add
      ((hμc.mul hεc).div (hρc.pow 2) fun u hu => (pow_pos (hρpos u hu) 2).ne')).add
      ((continuousOn_const.mul hεc).div hρc fun u hu => (hρpos u hu).ne')
  have hgOn : ContinuousOn (fun s => L * ‖X s - A s‖ + d s) (Icc a b) :=
    (continuousOn_const.mul (hXc.sub hAc).norm).add hdc
  obtain ⟨kc, hkc, hkeq⟩ : ∃ kc : ℝ → ℝ, Continuous kc ∧ ∀ s ∈ Icc a b, kc s =
      ℓ + ν s / ρ s + ν s / (ρ s - ε s) + μ s * ε s / ρ s ^ 2 + L * ε s / ρ s :=
    ⟨fun s => ℓ + ν (projIcc a b hab.le s) / ρ (projIcc a b hab.le s) +
        ν (projIcc a b hab.le s) / (ρ (projIcc a b hab.le s) - ε (projIcc a b hab.le s)) +
        μ (projIcc a b hab.le s) * ε (projIcc a b hab.le s) / ρ (projIcc a b hab.le s) ^ 2 +
        L * ε (projIcc a b hab.le s) / ρ (projIcc a b hab.le s),
      hkOn.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
        fun s => (projIcc a b hab.le s).2,
      fun s hs => by simp only [projIcc_of_mem _ hs]⟩
  obtain ⟨gc, hgc, hgeq⟩ : ∃ gc : ℝ → ℝ, Continuous gc ∧ ∀ s ∈ Icc a b, gc s =
      L * ‖X s - A s‖ + d s :=
    ⟨fun s => L * ‖X (projIcc a b hab.le s) - A (projIcc a b hab.le s)‖ +
        d (projIcc a b hab.le s),
      hgOn.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
        fun s => (projIcc a b hab.le s).2,
      fun s hs => by simp only [projIcc_of_mem _ hs]⟩
  have hg0 : ∀ s ∈ Ico a t0, 0 ≤ gc s := fun s hs => by
    rw [hgeq s (Ico_subset_Icc_self (hIco s hs))]
    exact add_nonneg (mul_nonneg hL (norm_nonneg _))
      ((norm_nonneg _).trans (hd s (hIco s hs)))
  have hbound : ∀ s ∈ Ico a t0,
      ⟪Y s - X s, tangentProjAt (Y s) (F s (Y s)) - X' s⟫ ≤
        (kc s * ‖Y s - X s‖ + gc s) * ‖Y s - X s‖ := fun s hs => by
    have hsb := hIco s hs
    have hsI := Ico_subset_Icc_self hsb
    have hρs := hρpos s hsI
    have hes := htube s hsb
    have hρε : 0 < ρ s - ε s := sub_pos.2 (hερ s hsI)
    have hν0 : 0 ≤ ν s := (norm_nonneg _).trans (hν s hsb)
    have hμ0 : 0 ≤ μ s := (norm_nonneg _).trans (hμ s hsb)
    have hPY := isOrthProj_tangentProjAt (Y s)
    have eY : tangentProjAt (Y s) (F s (Y s)) =
        S s (Y s) + tangentProjAt (Y s) (G s (Y s)) := by
      rw [hFS, map_add, hS s hsb]
    have hsplit : tangentProjAt (Y s) (F s (Y s)) - X' s =
        (F s (Y s) - F s (X s)) -
        ((G s (Y s) - G s (X s)) - tangentProjAt (Y s) (G s (Y s) - G s (X s))) +
        tangentProjAt (Y s) (G s (X s) - G s (A s)) +
        (tangentProjAt (Y s) (G s (A s)) - tangentProjAt (X s) (G s (A s))) +
        (S s (X s) + tangentProjAt (X s) (G s (A s)) - X' s) := by
      rw [eY, hFS s (Y s), hFS s (X s), map_sub, map_sub]
      abel
    have i1 : ⟪Y s - X s, F s (Y s) - F s (X s)⟫ ≤ ℓ * ‖Y s - X s‖ ^ 2 := by
      rw [real_inner_comm]
      exact hℓ s (Y s) (X s)
    have i2 : -⟪Y s - X s, (G s (Y s) - G s (X s)) -
        tangentProjAt (Y s) (G s (Y s) - G s (X s))⟫ ≤
        L * ε s / ρ s * ‖Y s - X s‖ ^ 2 := by
      have e2 : ⟪Y s - X s, (G s (Y s) - G s (X s)) -
          tangentProjAt (Y s) (G s (Y s) - G s (X s))⟫ =
          ⟪(Y s - X s) - tangentProjAt (Y s) (Y s - X s), G s (Y s) - G s (X s)⟫ := by
        rw [inner_sub_right (Y s - X s) (G s (Y s) - G s (X s)),
          inner_sub_left (Y s - X s) (tangentProjAt (Y s) (Y s - X s)),
          hPY.symm (Y s - X s) (G s (Y s) - G s (X s))]
      have hN : ‖(Y s - X s) - tangentProjAt (Y s) (Y s - X s)‖ ≤
          (ρ s)⁻¹ * ‖Y s - X s‖ ^ 2 :=
        norm_one_sub_tangentProjAt_apply_sub_le (hXr s hsI) (hY.2 s hsI) hρs (hσ s hsI)
      have hW : ‖G s (Y s) - G s (X s)‖ ≤ L * ε s :=
        (hG s (Y s) (X s)).trans (mul_le_mul_of_nonneg_left hes hL)
      rw [e2]
      calc -⟪(Y s - X s) - tangentProjAt (Y s) (Y s - X s), G s (Y s) - G s (X s)⟫
          ≤ ‖(Y s - X s) - tangentProjAt (Y s) (Y s - X s)‖ * ‖G s (Y s) - G s (X s)‖ :=
            (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
        _ ≤ (ρ s)⁻¹ * ‖Y s - X s‖ ^ 2 * (L * ε s) :=
            mul_le_mul hN hW (norm_nonneg _)
              (mul_nonneg (inv_nonneg.2 hρs.le) (sq_nonneg _))
        _ = _ := by
            rw [div_eq_mul_inv]
            ring
    have i3 : ⟪Y s - X s, tangentProjAt (Y s) (G s (X s) - G s (A s))⟫ ≤
        ‖Y s - X s‖ * (L * ‖X s - A s‖) :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
        ((hPY.norm_le _).trans (hG s _ _)) (norm_nonneg _))
    have i4 : ⟪Y s - X s, tangentProjAt (Y s) (G s (A s)) - tangentProjAt (X s) (G s (A s))⟫ ≤
        (ν s / ρ s + ν s / (ρ s - ε s) + μ s * ε s / ρ s ^ 2) * ‖Y s - X s‖ ^ 2 := by
      refine (inner_sub_tangentProjAt_sub_le_of_norm_sub_lt (hXr s hsI) (hY.2 s hsI)
        (hσ s hsI) (hes.trans_lt (hερ s hsI)) (G s (A s))).trans
        (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
      refine add_le_add (add_le_add ?_ ?_) ?_
      · exact div_le_div₀ hν0 (hν s hsb) hρs le_rfl
      · exact div_le_div₀ hν0 (hν s hsb) hρε (by linarith)
      · exact div_le_div₀ (mul_nonneg hμ0 (hε0 s hsI))
          (mul_le_mul (hμ s hsb) hes (norm_nonneg _) hμ0) (pow_pos hρs 2) le_rfl
    have i5 : ⟪Y s - X s, S s (X s) + tangentProjAt (X s) (G s (A s)) - X' s⟫ ≤
        ‖Y s - X s‖ * d s :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hd s hsb) (norm_nonneg _))
    rw [hsplit, inner_add_right, inner_add_right, inner_add_right,
      inner_sub_right (Y s - X s) (F s (Y s) - F s (X s)), hkeq s hsI, hgeq s hsI]
    calc _ ≤ ℓ * ‖Y s - X s‖ ^ 2 + L * ε s / ρ s * ‖Y s - X s‖ ^ 2 +
          ‖Y s - X s‖ * (L * ‖X s - A s‖) +
          (ν s / ρ s + ν s / (ρ s - ε s) + μ s * ε s / ρ s ^ 2) * ‖Y s - X s‖ ^ 2 +
          ‖Y s - X s‖ * d s := by linarith
      _ = _ := by ring
  have hcmp := norm_le_exp_integral_mul_add_integral_exp_integral_mul_of_inner_le
    (f := fun t => Y t - X t)
    (f' := fun t => tangentProjAt (Y t) (F t (Y t)) - X' t) (δ := δ) hkc hgc hg0
    ((hY.1.cont.sub hXc).mono hIcc)
    (fun s hs => (hY.1.deriv s (hIco s hs)).sub (hX s (hIco s hs))) hδ hbound t0
    ⟨ht0.1, le_rfl⟩
  have e1 : ∫ u in a..t0, kc u = ∫ u in a..t0,
      (ℓ + ν u / ρ u + ν u / (ρ u - ε u) + μ u * ε u / ρ u ^ 2 + L * ε u / ρ u) :=
    intervalIntegral.integral_congr fun u hu => by
      rw [uIcc_of_le ht0.1] at hu
      exact hkeq u (hIcc hu)
  have e2 : ∫ s in a..t0, Real.exp (∫ u in s..t0, kc u) * gc s =
      ∫ s in a..t0, Real.exp (∫ u in s..t0,
        (ℓ + ν u / ρ u + ν u / (ρ u - ε u) + μ u * ε u / ρ u ^ 2 + L * ε u / ρ u)) *
        (L * ‖X s - A s‖ + d s) :=
    intervalIntegral.integral_congr fun s hs => by
      rw [uIcc_of_le ht0.1] at hs
      have e3 : ∫ u in s..t0, kc u = ∫ u in s..t0,
          (ℓ + ν u / ρ u + ν u / (ρ u - ε u) + μ u * ε u / ρ u ^ 2 + L * ε u / ρ u) :=
        intervalIntegral.integral_congr fun u hu => by
          rw [uIcc_of_le hs.2] at hu
          exact hkeq u ⟨hs.1.trans hu.1, hu.2.trans ht0.2⟩
      change Real.exp (∫ u in s..t0, kc u) * gc s = _
      rw [e3, hgeq s (hIcc hs)]
  rw [e1, e2] at hcmp
  exact hcmp

/-- **Quasi-optimality for a field with a tangential part, a priori form.** Under the hypotheses
of `IsDLRASolution.norm_sub_le_integral_exp_integral_of_tangent_add_of_norm_sub_le` on `F`, `S`,
`G`, `A`, `X` and the functions `ρ`, `μ`, `ν`, `d`, `ε`, the tube condition on `Y` may be
replaced by a condition on the bound: if

  `e^{∫ₐᵗ k} δ + ∫ₐᵗ e^{∫ₛᵗ k} (L ‖X s - A s‖ + d s) ds < ε t`   on `[a, b]`,

`k = ℓ + ν/ρ + ν/(ρ - ε) + μ ε/ρ² + L ε/ρ`, then `‖Y t - X t‖` is at most the left-hand side on
`[a, b]`; in particular `Y` stays in the tube of radius `ε` around `X`. -/
theorem IsDLRASolution.norm_sub_le_integral_exp_integral_of_tangent_add_of_integral_lt {r : ℕ}
    {F S G : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A X X' Y : ℝ → Matrix m n ℝ}
    {ρ μ ν d ε : ℝ → ℝ} {a b ℓ L δ : ℝ} (hY : IsDLRASolution r F Y a b)
    (hFS : ∀ t Z, F t Z = S t Z + G t Z)
    (hS : ∀ t ∈ Ico a b, tangentProjAt (Y t) (S t (Y t)) = S t (Y t))
    (hℓ : IsOneSidedLipschitzField F ℓ) (hL : 0 ≤ L) (hG : IsLipschitzField G L)
    (hAc : ContinuousOn A (Icc a b))
    (hρc : ContinuousOn ρ (Icc a b)) (hμc : ContinuousOn μ (Icc a b))
    (hνc : ContinuousOn ν (Icc a b)) (hdc : ContinuousOn d (Icc a b))
    (hεc : ContinuousOn ε (Icc a b)) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ t ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hμ : ∀ t ∈ Ico a b, ‖G t (A t)‖ ≤ μ t)
    (hν : ∀ t ∈ Ico a b, ‖G t (A t) - tangentProjAt (X t) (G t (A t))‖ ≤ ν t)
    (hd : ∀ t ∈ Ico a b, ‖S t (X t) + tangentProjAt (X t) (G t (A t)) - X' t‖ ≤ d t)
    (hε0 : ∀ t ∈ Icc a b, 0 ≤ ε t) (hερ : ∀ t ∈ Icc a b, ε t < ρ t)
    (hδ : ‖Y a - X a‖ ≤ δ)
    (hB : ∀ t ∈ Icc a b,
      Real.exp (∫ u in a..t,
        (ℓ + ν u / ρ u + ν u / (ρ u - ε u) + μ u * ε u / ρ u ^ 2 + L * ε u / ρ u)) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t,
          (ℓ + ν u / ρ u + ν u / (ρ u - ε u) + μ u * ε u / ρ u ^ 2 + L * ε u / ρ u)) *
          (L * ‖X s - A s‖ + d s) < ε t) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp (∫ u in a..t,
        (ℓ + ν u / ρ u + ν u / (ρ u - ε u) + μ u * ε u / ρ u ^ 2 + L * ε u / ρ u)) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t,
          (ℓ + ν u / ρ u + ν u / (ρ u - ε u) + μ u * ε u / ρ u ^ 2 + L * ε u / ρ u)) *
          (L * ‖X s - A s‖ + d s) := by
  have h := bootstrap_of_continuousOn (e := fun t => ‖Y t - X t‖ - ε t)
    (β := fun t => (Real.exp (∫ u in a..t,
        (ℓ + ν u / ρ u + ν u / (ρ u - ε u) + μ u * ε u / ρ u ^ 2 + L * ε u / ρ u)) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t,
          (ℓ + ν u / ρ u + ν u / (ρ u - ε u) + μ u * ε u / ρ u ^ 2 + L * ε u / ρ u)) *
          (L * ‖X s - A s‖ + d s)) - ε t) (R := 0) ((hY.1.cont.sub hXc).norm.sub hεc)
    (fun t ht => sub_neg.2 (hB t ht)) (fun t ht hs => by
      have hIcc : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
      have hIco : ∀ s ∈ Ico a t, s ∈ Ico a b := fun s hs => ⟨hs.1, hs.2.trans_le ht.2⟩
      have hYt : IsDLRASolution r F Y a t :=
        ⟨⟨hY.1.cont.mono hIcc, fun s hs => hY.1.deriv s (hIco s hs)⟩,
          fun s hs => hY.2 s (hIcc hs)⟩
      have hm := hYt.norm_sub_le_integral_exp_integral_of_tangent_add_of_norm_sub_le hFS
        (fun s hs => hS s (hIco s hs)) hℓ hL hG
        (hAc.mono hIcc) (hρc.mono hIcc) (hμc.mono hIcc) (hνc.mono hIcc) (hdc.mono hIcc)
        (hεc.mono hIcc) (hXc.mono hIcc) (fun s hs => hX s (hIco s hs))
        (fun s hs => hXr s (hIcc hs)) (fun s hs => hσ s (hIcc hs))
        (fun s hs => hμ s (hIco s hs)) (fun s hs => hν s (hIco s hs))
        (fun s hs => hd s (hIco s hs)) (fun s hs => hε0 s (hIcc hs))
        (fun s hs => hερ s (hIcc hs)) (fun s hs' => sub_nonpos.1 (hs s hs')) hδ t
        ⟨ht.1, le_rfl⟩
      exact sub_le_sub_right hm _)
  exact fun t ht => (sub_le_sub_iff_right _).1 (h t ht)

/-- **Quasi-optimality with a one-sided Lipschitz constant, data on the reference curve.** The
case `A = X` of `IsDLRASolution.norm_sub_le_integral_exp_integral_of_tangent_add_of_integral_lt`:
with `‖G(t, X t)‖ ≤ μ t`, `‖(1 - P(X t)) G(t, X t)‖ ≤ ν t` and the defect of `X` in the projected
equation, `‖S(t, X t) + P(X t) G(t, X t) - X' t‖ ≤ d t`, the bound is

  `‖Y t - X t‖ ≤ e^{∫ₐᵗ k} δ + ∫ₐᵗ e^{∫ₛᵗ k} d s ds`,   `k = ℓ + ν/ρ + ν/(ρ - ε) + μ ε/ρ² + L ε/ρ`,

if the right-hand side stays below `ε t`. No Lipschitz term is in the source, and the Lipschitz
constant `L` of `G` is multiplied by `ε/ρ`. For `S = 0` this is a bound for every field `F = G`
that is Lipschitz and one-sided Lipschitz; `(1 - P(X)) F(X) = (1 - P(X)) G(X)` in general, so
the tangential part changes `μ` and `L` only. -/
theorem IsDLRASolution.norm_sub_le_integral_exp_integral_of_tangent_add_self_of_integral_lt
    {r : ℕ} {F S G : ℝ → Matrix m n ℝ → Matrix m n ℝ} {X X' Y : ℝ → Matrix m n ℝ}
    {ρ μ ν d ε : ℝ → ℝ} {a b ℓ L δ : ℝ} (hY : IsDLRASolution r F Y a b)
    (hFS : ∀ t Z, F t Z = S t Z + G t Z)
    (hS : ∀ t ∈ Ico a b, tangentProjAt (Y t) (S t (Y t)) = S t (Y t))
    (hℓ : IsOneSidedLipschitzField F ℓ) (hL : 0 ≤ L) (hG : IsLipschitzField G L)
    (hρc : ContinuousOn ρ (Icc a b)) (hμc : ContinuousOn μ (Icc a b))
    (hνc : ContinuousOn ν (Icc a b)) (hdc : ContinuousOn d (Icc a b))
    (hεc : ContinuousOn ε (Icc a b)) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ t ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hμ : ∀ t ∈ Ico a b, ‖G t (X t)‖ ≤ μ t)
    (hν : ∀ t ∈ Ico a b, ‖G t (X t) - tangentProjAt (X t) (G t (X t))‖ ≤ ν t)
    (hd : ∀ t ∈ Ico a b, ‖S t (X t) + tangentProjAt (X t) (G t (X t)) - X' t‖ ≤ d t)
    (hε0 : ∀ t ∈ Icc a b, 0 ≤ ε t) (hερ : ∀ t ∈ Icc a b, ε t < ρ t)
    (hδ : ‖Y a - X a‖ ≤ δ)
    (hB : ∀ t ∈ Icc a b,
      Real.exp (∫ u in a..t,
        (ℓ + ν u / ρ u + ν u / (ρ u - ε u) + μ u * ε u / ρ u ^ 2 + L * ε u / ρ u)) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t,
          (ℓ + ν u / ρ u + ν u / (ρ u - ε u) + μ u * ε u / ρ u ^ 2 + L * ε u / ρ u)) *
          d s < ε t) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp (∫ u in a..t,
        (ℓ + ν u / ρ u + ν u / (ρ u - ε u) + μ u * ε u / ρ u ^ 2 + L * ε u / ρ u)) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t,
          (ℓ + ν u / ρ u + ν u / (ρ u - ε u) + μ u * ε u / ρ u ^ 2 + L * ε u / ρ u)) *
          d s := by
  have h := hY.norm_sub_le_integral_exp_integral_of_tangent_add_of_integral_lt (A := X) hFS hS
    hℓ hL hG hXc hρc hμc hνc hdc hεc hXc hX hXr hσ hμ hν hd hε0 hερ hδ
    (by simpa only [sub_self, norm_zero, mul_zero, zero_add] using hB)
  simpa only [sub_self, norm_zero, mul_zero, zero_add] using h

/-- **Stiffness-uniform quasi-optimality of matrix DLRA for Sylvester-stiff fields.** Let
`F(t, Z) = M Z + Z N + G(t, Z)` be one-sided Lipschitz with the constant `ℓ` and `G` be
`L`-Lipschitz, `Y` a DLRA solution of rank `r` on `[a, b]`, `A` a continuous curve and `X` a
continuous curve of matrices of rank `r` with right derivatives `X'`. Let `ρ t ≤ σ_{r-1}(X t)`,
`‖G(t, A t)‖ ≤ μ t`, `‖(1 - P(X t)) G(t, A t)‖ ≤ ν t`,
`‖M X t + X t N + P(X t) G(t, A t) - X' t‖ ≤ d t` and `0 ≤ ε t < ρ t`, all continuous. If
`‖Y a - X a‖ ≤ δ` and, with `k = ℓ + ν/ρ + ν/(ρ - ε) + μ ε/ρ² + L ε/ρ`,

  `e^{∫ₐᵗ k} δ + ∫ₐᵗ e^{∫ₛᵗ k} (L ‖X s - A s‖ + d s) ds < ε t`   on `[a, b]`,

then `‖Y t - X t‖` is at most the left-hand side on `[a, b]`. The matrices `M`, `N` enter through
`ℓ` and `d` only: the Sylvester operator maps every matrix into its tangent space
[CarrelVandereycken2023, Section 2.3], and `ℓ ≤ 0 + ℓ_G` for dissipative `M`, `N`. -/
theorem IsDLRASolution.norm_sub_le_integral_exp_integral_of_sylvester_add_of_integral_lt
    {r : ℕ} {M : Matrix m m ℝ} {N : Matrix n n ℝ}
    {G : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A X X' Y : ℝ → Matrix m n ℝ}
    {ρ μ ν d ε : ℝ → ℝ} {a b ℓ L δ : ℝ}
    (hY : IsDLRASolution r (fun t Z => M * Z + Z * N + G t Z) Y a b)
    (hℓ : IsOneSidedLipschitzField (fun t Z => M * Z + Z * N + G t Z) ℓ) (hL : 0 ≤ L)
    (hG : IsLipschitzField G L) (hAc : ContinuousOn A (Icc a b))
    (hρc : ContinuousOn ρ (Icc a b)) (hμc : ContinuousOn μ (Icc a b))
    (hνc : ContinuousOn ν (Icc a b)) (hdc : ContinuousOn d (Icc a b))
    (hεc : ContinuousOn ε (Icc a b)) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ t ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hμ : ∀ t ∈ Ico a b, ‖G t (A t)‖ ≤ μ t)
    (hν : ∀ t ∈ Ico a b, ‖G t (A t) - tangentProjAt (X t) (G t (A t))‖ ≤ ν t)
    (hd : ∀ t ∈ Ico a b,
      ‖M * X t + X t * N + tangentProjAt (X t) (G t (A t)) - X' t‖ ≤ d t)
    (hε0 : ∀ t ∈ Icc a b, 0 ≤ ε t) (hερ : ∀ t ∈ Icc a b, ε t < ρ t)
    (hδ : ‖Y a - X a‖ ≤ δ)
    (hB : ∀ t ∈ Icc a b,
      Real.exp (∫ u in a..t,
        (ℓ + ν u / ρ u + ν u / (ρ u - ε u) + μ u * ε u / ρ u ^ 2 + L * ε u / ρ u)) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t,
          (ℓ + ν u / ρ u + ν u / (ρ u - ε u) + μ u * ε u / ρ u ^ 2 + L * ε u / ρ u)) *
          (L * ‖X s - A s‖ + d s) < ε t) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp (∫ u in a..t,
        (ℓ + ν u / ρ u + ν u / (ρ u - ε u) + μ u * ε u / ρ u ^ 2 + L * ε u / ρ u)) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t,
          (ℓ + ν u / ρ u + ν u / (ρ u - ε u) + μ u * ε u / ρ u ^ 2 + L * ε u / ρ u)) *
          (L * ‖X s - A s‖ + d s) :=
  hY.norm_sub_le_integral_exp_integral_of_tangent_add_of_integral_lt
    (S := fun _ Z => M * Z + Z * N) (fun _ _ => rfl)
    (fun _ _ => tangentProjAt_eq_self_iff.2 ⟨M, N, rfl⟩) hℓ hL hG hAc hρc hμc hνc hdc hεc hXc
    hX hXr hσ hμ hν hd hε0 hερ hδ hB

end Stiff

/-! ### Examples -/

namespace QuasiOptimalityStiffExamples

open scoped LeanDLRA.Frobenius
open QuasiOptimalityExamples

/-- The derivative of `X t = (1 + e^{-t}/4) e₁ e₁ᵀ`. -/
private theorem hasDerivAt_decay (t : ℝ) :
    HasDerivAt (fun t : ℝ => (1 + 1 / 4 * Real.exp (-t)) • (e₁ * e₁ᵀ))
      ((1 / 4 * (Real.exp (-t) * -1)) • (e₁ * e₁ᵀ)) t :=
  ((((hasDerivAt_neg t).exp).const_mul (1 / 4 : ℝ)).const_add 1).smul_const (e₁ * e₁ᵀ)

/-- `‖e₁ e₁ᵀ - (1 + e^{-t}/4) e₁ e₁ᵀ‖ ≤ 1/4` for `t ≥ 0`. -/
private theorem norm_sub_decay_le {t : ℝ} (ht : 0 ≤ t) :
    ‖(1 : ℝ) • (e₁ * e₁ᵀ) - (1 + 1 / 4 * Real.exp (-t)) • (e₁ * e₁ᵀ)‖ ≤ 1 / 4 := by
  have e : (1 : ℝ) • (e₁ * e₁ᵀ) - (1 + 1 / 4 * Real.exp (-t)) • (e₁ * e₁ᵀ) =
      (-(1 / 4 * Real.exp (-t))) • (e₁ * e₁ᵀ) := by module
  have hx : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hx0 := Real.exp_pos (-t)
  rw [e, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
  calc 1 / 4 * Real.exp (-t) * ‖e₁ * e₁ᵀ‖ ≤ 1 / 4 * 1 :=
        mul_le_mul (by linarith) norm_e₁_mul_le (norm_nonneg _) (by norm_num)
    _ = 1 / 4 := by norm_num

/-- The stationary state `Y = e₁ e₁ᵀ` is a DLRA solution of rank `1` of the field
`F(Z) = -Z + e₁ e₁ᵀ`. -/
private theorem isDLRASolution_stationary :
    IsDLRASolution 1 (fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) => -Z + e₁ * e₁ᵀ)
      (fun _ : ℝ => (1 : ℝ) • (e₁ * e₁ᵀ)) 0 1 := by
  refine ⟨⟨continuousOn_const, fun s _ => ?_⟩, fun _ _ => rank_smul_e₁ one_ne_zero⟩
  have h0 : tangentProjAt ((1 : ℝ) • (e₁ * e₁ᵀ)) (-((1 : ℝ) • (e₁ * e₁ᵀ)) + e₁ * e₁ᵀ) = 0 := by
    rw [one_smul, neg_add_cancel, map_zero]
  have h := hasDerivWithinAt_const s (Ici s) ((1 : ℝ) • (e₁ * e₁ᵀ))
  rw [← h0] at h
  exact h

/-- The field `F(Z) = -Z + e₁ e₁ᵀ` is one-sided Lipschitz with the constant `-1`. -/
private theorem isOneSidedLipschitzField_neg_add :
    IsOneSidedLipschitzField
      (fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) => -Z + e₁ * e₁ᵀ) (-1) := fun _ x y => by
  have e : (-x + e₁ * e₁ᵀ) - (-y + e₁ * e₁ᵀ) = -(x - y) := by abel
  change ⟪(-x + e₁ * e₁ᵀ) - (-y + e₁ * e₁ᵀ), x - y⟫ ≤ -1 * ‖x - y‖ ^ 2
  rw [e, inner_neg_left, real_inner_self_eq_norm_sq]
  linarith

/-- **Non-vacuity of
`IsDLRASolution.norm_sub_le_integral_exp_integral_of_tangent_add_of_norm_sub_le` with a
dissipative tangential part and a negative rate**: `2 × 2` matrices, `r = 1`,
`F(Z) = -Z + e₁ e₁ᵀ` with `S(Z) = -Z` and `G = e₁ e₁ᵀ` (`ℓ = -1`, `L = 0`), the stationary DLRA
solution `Y = e₁ e₁ᵀ` and the curve `A t = X t = (1 + e^{-t}/4) e₁ e₁ᵀ ≠ Y` on `[0, 1]`, with
`ρ = μ = 1`, `ν = d = 0`, `ε = 1/2`, `δ = 1/4`. The rate is `k = -1/2` and the bound is
`e^{-t/2}/4`. -/
example : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ‖(1 : ℝ) • (e₁ * e₁ᵀ) - (1 + 1 / 4 * Real.exp (-t)) • (e₁ * e₁ᵀ)‖ ≤
      Real.exp (∫ _ in (0 : ℝ)..t,
        ((-1 : ℝ) + 0 / 1 + 0 / (1 - 1 / 2) + 1 * (1 / 2) / 1 ^ 2 + 0 * (1 / 2) / 1)) *
          (1 / 4) +
        ∫ s in (0 : ℝ)..t, Real.exp (∫ _ in s..t,
          ((-1 : ℝ) + 0 / 1 + 0 / (1 - 1 / 2) + 1 * (1 / 2) / 1 ^ 2 + 0 * (1 / 2) / 1)) *
          (0 * ‖(1 + 1 / 4 * Real.exp (-s)) • (e₁ * e₁ᵀ) -
            (1 + 1 / 4 * Real.exp (-s)) • (e₁ * e₁ᵀ)‖ + 0) :=
  isDLRASolution_stationary.norm_sub_le_integral_exp_integral_of_tangent_add_of_norm_sub_le
    (S := fun _ Z => -Z) (G := fun _ _ => e₁ * e₁ᵀ)
    (A := fun t : ℝ => (1 + 1 / 4 * Real.exp (-t)) • (e₁ * e₁ᵀ))
    (X := fun t : ℝ => (1 + 1 / 4 * Real.exp (-t)) • (e₁ * e₁ᵀ))
    (X' := fun t : ℝ => (1 / 4 * (Real.exp (-t) * -1)) • (e₁ * e₁ᵀ))
    (ρ := fun _ => 1) (μ := fun _ => 1) (ν := fun _ => 0) (d := fun _ => 0)
    (ε := fun _ => 1 / 2) (ℓ := -1) (L := 0) (δ := 1 / 4) (fun _ _ => rfl)
    (fun _ _ => by simp only [map_neg, tangentProjAt_self])
    isOneSidedLipschitzField_neg_add le_rfl (fun _ _ _ => by simp)
    (fun s _ => (hasDerivAt_decay s).continuousAt.continuousWithinAt)
    continuousOn_const continuousOn_const continuousOn_const continuousOn_const
    continuousOn_const
    (fun s _ => (hasDerivAt_decay s).continuousAt.continuousWithinAt)
    (fun s _ => (hasDerivAt_decay s).hasDerivWithinAt)
    (fun t _ => rank_smul_e₁ (by positivity : (0 : ℝ) < 1 + 1 / 4 * Real.exp (-t)).ne')
    (fun t _ => one_le_singularValues_smul_e₁ (by linarith [Real.exp_pos (-t)]))
    (fun _ _ => norm_e₁_mul_le)
    (fun t _ => by
      rw [tangentProjAt_smul_e₁_apply
        (by positivity : (0 : ℝ) < 1 + 1 / 4 * Real.exp (-t)).ne', sub_self, norm_zero])
    (fun t _ => by
      rw [tangentProjAt_smul_e₁_apply
        (by positivity : (0 : ℝ) < 1 + 1 / 4 * Real.exp (-t)).ne']
      have e : -((1 + 1 / 4 * Real.exp (-t)) • (e₁ * e₁ᵀ)) + e₁ * e₁ᵀ -
          (1 / 4 * (Real.exp (-t) * -1)) • (e₁ * e₁ᵀ) = 0 := by module
      rw [e, norm_zero])
    (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    (fun t ht => (norm_sub_decay_le ht.1).trans (by norm_num)) (norm_sub_decay_le le_rfl)

/-- `Y = e₁ e₁ᵀ` is a DLRA solution of rank `1` of the Sylvester-type field
`F(Z) = (-1) Z + Z 0 + e₁ e₁ᵀ`. -/
private theorem isDLRASolution_stationary_sylvester :
    IsDLRASolution 1 (fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) =>
        (-1 : Matrix (Fin 2) (Fin 2) ℝ) * Z + Z * (0 : Matrix (Fin 2) (Fin 2) ℝ) + e₁ * e₁ᵀ)
      (fun _ : ℝ => (1 : ℝ) • (e₁ * e₁ᵀ)) 0 1 := by
  have h := isDLRASolution_stationary
  have e : (fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) =>
      (-1 : Matrix (Fin 2) (Fin 2) ℝ) * Z + Z * (0 : Matrix (Fin 2) (Fin 2) ℝ) + e₁ * e₁ᵀ) =
      fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) => -Z + e₁ * e₁ᵀ := by
    funext _ Z
    rw [Matrix.neg_mul, Matrix.one_mul, Matrix.mul_zero, add_zero]
  rw [e]
  exact h

/-- The bound `e^{-t/2}/4` of the examples stays below the tube radius `1/2`. -/
private theorem exp_integral_mul_add_lt_half {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Real.exp (∫ _ in (0 : ℝ)..t,
        ((-1 : ℝ) + 0 / 1 + 0 / (1 - 1 / 2) + 1 * (1 / 2) / 1 ^ 2 + 0 * (1 / 2) / 1)) *
          (1 / 4) +
        ∫ s in (0 : ℝ)..t, Real.exp (∫ _ in s..t,
          ((-1 : ℝ) + 0 / 1 + 0 / (1 - 1 / 2) + 1 * (1 / 2) / 1 ^ 2 + 0 * (1 / 2) / 1)) *
          (0 * ‖(1 + 1 / 4 * Real.exp (-s)) • (e₁ * e₁ᵀ) -
            (1 + 1 / 4 * Real.exp (-s)) • (e₁ * e₁ᵀ)‖ + 0) < 1 / 2 := by
  have h1 : (∫ _ in (0 : ℝ)..t,
      ((-1 : ℝ) + 0 / 1 + 0 / (1 - 1 / 2) + 1 * (1 / 2) / 1 ^ 2 + 0 * (1 / 2) / 1)) ≤ 0 := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    nlinarith [ht.1]
  have h2 := Real.exp_le_one_iff.2 h1
  simp only [zero_mul, add_zero, mul_zero, intervalIntegral.integral_zero]
  linarith

/-- **Non-vacuity of
`IsDLRASolution.norm_sub_le_integral_exp_integral_of_sylvester_add_of_integral_lt`**, and through
it of `IsDLRASolution.norm_sub_le_integral_exp_integral_of_tangent_add_of_integral_lt`, on the
data of the preceding example with `M = -1`, `N = 0`: the bound `e^{-t/2}/4` stays below
`ε = 1/2`. -/
example : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ‖(1 : ℝ) • (e₁ * e₁ᵀ) - (1 + 1 / 4 * Real.exp (-t)) • (e₁ * e₁ᵀ)‖ ≤
      Real.exp (∫ _ in (0 : ℝ)..t,
        ((-1 : ℝ) + 0 / 1 + 0 / (1 - 1 / 2) + 1 * (1 / 2) / 1 ^ 2 + 0 * (1 / 2) / 1)) *
          (1 / 4) +
        ∫ s in (0 : ℝ)..t, Real.exp (∫ _ in s..t,
          ((-1 : ℝ) + 0 / 1 + 0 / (1 - 1 / 2) + 1 * (1 / 2) / 1 ^ 2 + 0 * (1 / 2) / 1)) *
          (0 * ‖(1 + 1 / 4 * Real.exp (-s)) • (e₁ * e₁ᵀ) -
            (1 + 1 / 4 * Real.exp (-s)) • (e₁ * e₁ᵀ)‖ + 0) :=
  IsDLRASolution.norm_sub_le_integral_exp_integral_of_sylvester_add_of_integral_lt
    (A := fun t : ℝ => (1 + 1 / 4 * Real.exp (-t)) • (e₁ * e₁ᵀ))
    (X := fun t : ℝ => (1 + 1 / 4 * Real.exp (-t)) • (e₁ * e₁ᵀ))
    (X' := fun t : ℝ => (1 / 4 * (Real.exp (-t) * -1)) • (e₁ * e₁ᵀ))
    (ρ := fun _ => 1) (μ := fun _ => 1) (ν := fun _ => 0) (d := fun _ => 0)
    (ε := fun _ => 1 / 2) (ℓ := -1) (L := 0) (δ := 1 / 4)
    isDLRASolution_stationary_sylvester
    (by
      have h := isOneSidedLipschitzField_neg_add
      have e : (fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) =>
          (-1 : Matrix (Fin 2) (Fin 2) ℝ) * Z + Z * (0 : Matrix (Fin 2) (Fin 2) ℝ) +
            e₁ * e₁ᵀ) = fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) => -Z + e₁ * e₁ᵀ := by
        funext _ Z
        rw [Matrix.neg_mul, Matrix.one_mul, Matrix.mul_zero, add_zero]
      rw [e]
      exact h)
    le_rfl (fun _ _ _ => by simp)
    (fun s _ => (hasDerivAt_decay s).continuousAt.continuousWithinAt)
    continuousOn_const continuousOn_const continuousOn_const continuousOn_const
    continuousOn_const
    (fun s _ => (hasDerivAt_decay s).continuousAt.continuousWithinAt)
    (fun s _ => (hasDerivAt_decay s).hasDerivWithinAt)
    (fun t _ => rank_smul_e₁ (by positivity : (0 : ℝ) < 1 + 1 / 4 * Real.exp (-t)).ne')
    (fun t _ => one_le_singularValues_smul_e₁ (by linarith [Real.exp_pos (-t)]))
    (fun _ _ => norm_e₁_mul_le)
    (fun t _ => by
      rw [tangentProjAt_smul_e₁_apply
        (by positivity : (0 : ℝ) < 1 + 1 / 4 * Real.exp (-t)).ne', sub_self, norm_zero])
    (fun t _ => by
      rw [tangentProjAt_smul_e₁_apply
        (by positivity : (0 : ℝ) < 1 + 1 / 4 * Real.exp (-t)).ne', Matrix.neg_mul,
        Matrix.one_mul, Matrix.mul_zero, add_zero]
      have e : -((1 + 1 / 4 * Real.exp (-t)) • (e₁ * e₁ᵀ)) + e₁ * e₁ᵀ -
          (1 / 4 * (Real.exp (-t) * -1)) • (e₁ * e₁ᵀ) = 0 := by module
      rw [e, norm_zero])
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) (norm_sub_decay_le le_rfl)
    (fun _ ht => exp_integral_mul_add_lt_half ht)

/-- The bound `e^{-t/2}/4` with the source `0` stays below `1/2`. -/
private theorem exp_integral_mul_add_integral_zero_lt_half {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Real.exp (∫ _ in (0 : ℝ)..t,
        ((-1 : ℝ) + 0 / 1 + 0 / (1 - 1 / 2) + 1 * (1 / 2) / 1 ^ 2 + 0 * (1 / 2) / 1)) *
          (1 / 4) +
        ∫ s in (0 : ℝ)..t, Real.exp (∫ _ in s..t,
          ((-1 : ℝ) + 0 / 1 + 0 / (1 - 1 / 2) + 1 * (1 / 2) / 1 ^ 2 + 0 * (1 / 2) / 1)) *
          0 < 1 / 2 := by
  have h1 : (∫ _ in (0 : ℝ)..t,
      ((-1 : ℝ) + 0 / 1 + 0 / (1 - 1 / 2) + 1 * (1 / 2) / 1 ^ 2 + 0 * (1 / 2) / 1)) ≤ 0 := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    nlinarith [ht.1]
  have h2 := Real.exp_le_one_iff.2 h1
  simp only [mul_zero, intervalIntegral.integral_zero]
  linarith

/-- **Non-vacuity of
`IsDLRASolution.norm_sub_le_integral_exp_integral_of_tangent_add_self_of_integral_lt`** on the
data of the preceding examples (`S(Z) = -Z`, `G = e₁ e₁ᵀ`, `ℓ = -1`, `δ = 1/4`, `d = 0`). -/
example : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ‖(1 : ℝ) • (e₁ * e₁ᵀ) - (1 + 1 / 4 * Real.exp (-t)) • (e₁ * e₁ᵀ)‖ ≤
      Real.exp (∫ _ in (0 : ℝ)..t,
        ((-1 : ℝ) + 0 / 1 + 0 / (1 - 1 / 2) + 1 * (1 / 2) / 1 ^ 2 + 0 * (1 / 2) / 1)) *
          (1 / 4) +
        ∫ s in (0 : ℝ)..t, Real.exp (∫ _ in s..t,
          ((-1 : ℝ) + 0 / 1 + 0 / (1 - 1 / 2) + 1 * (1 / 2) / 1 ^ 2 + 0 * (1 / 2) / 1)) *
          0 :=
  IsDLRASolution.norm_sub_le_integral_exp_integral_of_tangent_add_self_of_integral_lt
    (S := fun _ Z => -Z) (G := fun _ _ => e₁ * e₁ᵀ)
    (X := fun t : ℝ => (1 + 1 / 4 * Real.exp (-t)) • (e₁ * e₁ᵀ))
    (X' := fun t : ℝ => (1 / 4 * (Real.exp (-t) * -1)) • (e₁ * e₁ᵀ))
    (ρ := fun _ => 1) (μ := fun _ => 1) (ν := fun _ => 0) (d := fun _ => 0)
    (ε := fun _ => 1 / 2) (ℓ := -1) (L := 0) (δ := 1 / 4) isDLRASolution_stationary
    (fun _ _ => rfl) (fun _ _ => by simp only [map_neg, tangentProjAt_self])
    isOneSidedLipschitzField_neg_add le_rfl (fun _ _ _ => by simp)
    continuousOn_const continuousOn_const continuousOn_const continuousOn_const
    continuousOn_const
    (fun s _ => (hasDerivAt_decay s).continuousAt.continuousWithinAt)
    (fun s _ => (hasDerivAt_decay s).hasDerivWithinAt)
    (fun t _ => rank_smul_e₁ (by positivity : (0 : ℝ) < 1 + 1 / 4 * Real.exp (-t)).ne')
    (fun t _ => one_le_singularValues_smul_e₁ (by linarith [Real.exp_pos (-t)]))
    (fun _ _ => norm_e₁_mul_le)
    (fun t _ => by
      rw [tangentProjAt_smul_e₁_apply
        (by positivity : (0 : ℝ) < 1 + 1 / 4 * Real.exp (-t)).ne', sub_self, norm_zero])
    (fun t _ => by
      rw [tangentProjAt_smul_e₁_apply
        (by positivity : (0 : ℝ) < 1 + 1 / 4 * Real.exp (-t)).ne']
      have e : -((1 + 1 / 4 * Real.exp (-t)) • (e₁ * e₁ᵀ)) + e₁ * e₁ᵀ -
          (1 / 4 * (Real.exp (-t) * -1)) • (e₁ * e₁ᵀ) = 0 := by module
      rw [e, norm_zero])
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) (norm_sub_decay_le le_rfl)
    (fun _ ht => exp_integral_mul_add_integral_zero_lt_half ht)

end QuasiOptimalityStiffExamples

end LeanDLRA
