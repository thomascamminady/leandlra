import LeanDLRA.Tensor.TT.ObliqueProjector

/-!
# Results of arXiv 2402.18721: interpolatory TT tangent projectors

Dektor, *Collocation methods for nonlinear differential equations on low-rank manifolds*. This
module states Prop. 4.1, Lemma 4.1 and Thm 4.1 of the paper in its form, as corollaries of the
core tensor layer (`Tensor/TT/ObliqueProjector.lean`, `Tensor/TT/TangentProjector.lean`). The
companion module `P2402_18721a` proves Eq. (5).

Notation. Modes are numbered `0, …, d - 1`; the paper's mode `j` is our mode `j - 1`. The paper's
`P_{≤k}` acts on our modes `< k`, its `P_{>k}` on our modes `≥ k`, its core `C_k` is our core
`k - 1`, and its term `P_{≤k-1} P_{>k}` is our `P_{≤k} P_{>k+1}` (`ttLeftObliqueProj A Xl k`,
`ttRightObliqueProj B Xr (k + 1)`). The interfaces `U_{≤k} = ttLeft A k` of left-orthogonal
cores `A` and `V_{>k} = ttRight B k` of right-orthogonal cores `B` play the role of the bases of
the orthogonal decompositions (16). The multi-index sets `I^{≤k}`, `I^{>k}` (with `r_k` elements)
are index maps `Il k : β k → (multi-indices of the modes < k)`,
`Ir k : β k → (multi-indices of the modes ≥ k)`; the selection matrices of Eq. (35) are
`(1 : Matrix _ _ ℝ).submatrix id (Il k)`, so `M_k = U_{≤k}(I^{≤k}, :)` is
`(ttLeft A k).submatrix (Il k) id` and `N_k = (ttRight B k).submatrix (Ir k) id` (Eq. (59)). The
multi-index `(I^{≤k}_α, i_{k+1}, I^{>k+1}_β)` is `assemble k hk (Il k α) c (Ir (k + 1) β)`.

## Results

* `ttObliqueTangentProj_isProjector` (**Prop. 4.1**): for any test matrices with invertible
  `X_{≤k}ᵀ U_{≤k}`, `X_{>k}ᵀ V_{>k}`, `P_Y` (Eq. (24)) is idempotent, maps into the TT tangent
  space and fixes it, i.e. it is a projector onto the tangent space. This is the core theorem
  `ttObliqueTangentProj_apply_mem` / `ttObliqueTangentProj_apply_of_mem`; with orthonormal cores
  it is moreover an oblique projector onto the range of the orthogonal projector (21) in the sense
  of `IsObliqueProj` (core: `isObliqueProj_ttObliqueTangentProj`). Deviation: the printed proof
  checks idempotence only through the factors `P_{≤k}`, `P_{>k}`, which does not suffice for
  `d ≥ 3`; the core proof uses that `P_Y` fixes every single-core variation. The tangent space is
  the span of the single-core variations (18) of the mixed canonical form (`ttTangentSpace`); that
  this span is the tangent space of the embedded manifold `M_r` of fixed TT rank is the standard
  characterization (Holtz–Rohwedder–Schneider), not proved here.
* `ttObliqueTerm_sel_apply_cross` (**Lemma 4.1**): the three cases of Eq. (39) at the cross
  multi-indices, for nested index sets (38) and invertible `M_k`, `N_k`.
* `ttObliqueTangentProj_sel_apply_cross` (**Thm 4.1**, cross interpolation (42)): a corollary of
  the core theorem `ttTangentSum_actOn_apply_eq_of_interp` and the interpolation property (37)
  (core: `ttLeftObliqueProj_sel_apply`, `ttRightObliqueProj_sel_apply`).

Finite dimensions and real tensors throughout.

## Already in the library, or left out

* Eq. (5) is `obliqueTangentProj_eq_of_mem_range` (companion module `P2402_18721a`).
* Eqs. (26)–(33) (the summands of `P_Y` are single-core variations / bond-centred tensor trains)
  are the core theorems `actOn_mul_actOn_mul_eq_tt_update` and `actOn_mul_actOn_mul_eq_ttBond`.
* Eq. (7) (CUR reconstruction of a rank-`r` matrix) is `P2408_16591.cur_eq_self_of_rank_le`, and
  the QR-stabilized form (8) follows with `P2408_16591.qr_cur_eq`; not restated here.
* Left out, not claimed: Eq. (6) (the matrix cross integrator, rows and columns evolving by
  `G`), Thm 5.1 (TT-cross-DEIM yields invertible `M_j`, `N_j`; the DEIM lemma it needs is
  `P2411_15990.det_submatrix_ne_zero_of_isDEIMSelection`), Cor. 5.1 (exact TT-cross
  representation (62); the interpolant (62) and [14, Thm 2] are not in the library), and Thm 6.1
  (exact solution of the substeps (76) by (78)–(79) with frozen projectors; the explicit
  right-hand sides are the core formulas above, but the ODE statement is not formalized).
-/

open scoped Matrix RealInnerProductSpace

namespace LeanDLRA.Literature.P2402_18721

open LeanDLRA.Tensor

section TT

variable {d : ℕ} {ι : Fin d → Type*} [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
  {β : ℕ → Type*} [∀ k, Fintype (β k)] [∀ k, DecidableEq (β k)]

/-! ### Prop. 4.1 -/

/-- **Prop. 4.1 of arXiv 2402.18721.** For test matrices `X_{≤k}`, `X_{>k}` with invertible
`X_{≤k}ᵀ U_{≤k}` and `X_{>k}ᵀ V_{>k}` (`0 < k < d`), the oblique TT tangent projector (24) is a
projector onto the TT tangent space: it is idempotent, maps into `ttTangentSpace A B` and fixes
it. Orthonormality of the cores is not needed (as remarked after the proof in the paper). The
printed proof of idempotence checks only `P_{≤k}² = P_{≤k}` and `P_{>k}² = P_{>k}`; here
idempotence follows from the core theorems `ttObliqueTangentProj_apply_mem` and
`ttObliqueTangentProj_apply_of_mem`. -/
theorem ttObliqueTangentProj_isProjector [Unique (β 0)] [Unique (β d)] {A B : TTCores ι β}
    {Xl : ∀ k : ℕ, Matrix (∀ i : {i : Fin d // i.val < k}, ι i) (β k) ℝ}
    {Xr : ∀ k : ℕ, Matrix (∀ i : {i : Fin d // ¬ i.val < k}, ι i) (β k) ℝ}
    (hXl : ∀ k, 0 < k → k < d → IsUnit ((Xl k)ᵀ * ttLeft A k).det)
    (hXr : ∀ k, 0 < k → k < d → IsUnit ((Xr k)ᵀ * ttRight B k).det) :
    (∀ Z, ttObliqueTangentProj A B Xl Xr (ttObliqueTangentProj A B Xl Xr Z) =
      ttObliqueTangentProj A B Xl Xr Z) ∧
    (∀ Z, ttObliqueTangentProj A B Xl Xr Z ∈ ttTangentSpace A B) ∧
    ∀ W ∈ ttTangentSpace A B, ttObliqueTangentProj A B Xl Xr W = W :=
  ⟨ttObliqueTangentProj_idem hXl hXr, ttObliqueTangentProj_apply_mem,
    fun _ hW => ttObliqueTangentProj_apply_of_mem hXl hXr hW⟩

/-! ### Lemma 4.1 and Theorem 4.1: cross interpolation -/

section Cross

variable (A B : TTCores ι β) (Il : ∀ k : ℕ, β k → ∀ i : {i : Fin d // i.val < k}, ι i)
  (Ir : ∀ k : ℕ, β k → ∀ i : {i : Fin d // ¬ i.val < k}, ι i)

omit [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] [∀ k, Fintype (β k)]
  [∀ k, DecidableEq (β k)] in
/-- The nested left multi-indices of a cross point: if `x_{<m} ∈ I^{≤m}` and the index sets are
nested (38), then `x_{<j} ∈ I^{≤j}` for all `j ≤ m`. -/
private lemma restrict_lt_mem_range {m : ℕ} (hm : m < d)
    (hnl : ∀ k, k + 1 < d → ∀ a, restrictLE (fun (i : Fin d) (hi : i.val < k) =>
      Nat.lt_succ_of_lt hi) (Il (k + 1) a) ∈ Set.range (Il k))
    {x : ∀ i, ι i} (hx : Subtype.restrict (fun i : Fin d => i.val < m) x ∈ Set.range (Il m)) :
    ∀ j ≤ m, Subtype.restrict (fun i : Fin d => i.val < j) x ∈ Set.range (Il j) := by
  intro j hj
  induction hj using Nat.decreasingInduction with
  | self => exact hx
  | of_succ j hjm ih =>
    obtain ⟨a, ha⟩ := ih
    have := hnl j (by omega) a
    rwa [ha, restrictLE_restrict] at this

omit [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] [∀ k, Fintype (β k)]
  [∀ k, DecidableEq (β k)] in
/-- The nested right multi-indices of a cross point: if `x_{≥m+1} ∈ I^{>m+1}` and the index sets
are nested (38), then `x_{≥j} ∈ I^{>j}` for all `m + 1 ≤ j < d`. -/
private lemma restrict_ge_mem_range {m : ℕ}
    (hnr : ∀ k, 0 < k → k + 1 < d → ∀ b, restrictLE (fun (i : Fin d) (hi : ¬ i.val < k + 1) hk =>
      hi (Nat.lt_succ_of_lt hk)) (Ir k b) ∈ Set.range (Ir (k + 1)))
    {x : ∀ i, ι i}
    (hx : Subtype.restrict (fun i : Fin d => ¬ i.val < m + 1) x ∈ Set.range (Ir (m + 1))) :
    ∀ j, m + 1 ≤ j → j < d →
      Subtype.restrict (fun i : Fin d => ¬ i.val < j) x ∈ Set.range (Ir j) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => exact fun _ => hx
  | succ j hmj ih =>
    intro hjd
    obtain ⟨b, hb⟩ := ih (by omega)
    have := hnr j (by omega) hjd b
    rwa [hb, restrictLE_restrict] at this

/-- **Lemma 4.1 of arXiv 2402.18721** (Eq. (39)). Let the index sets be nested (38) and define
interpolatory projectors (`M_k`, `N_k` invertible for `0 < k < d`). At a cross multi-index `x`
of mode `m` (`x_{<m} ∈ I^{≤m}`, `x_{>m} ∈ I^{>m+1}`; the paper's `(I^{≤j-1}, i_j, I^{>j})` with
`j = m + 1`), the term `P_{≤k} P_{>k+1}` (the paper's `P_{≤k-1} P_{>k}` for its `k + 1`) satisfies:
`[P_{≤k} P_{>k+1} Z](x) = Z(x)` if `k = m`; `= [P_{≤k+1} P_{>k+1} Z](x)` if `k < m`; and
`= [P_{≤k} P_{>k} Z](x)` if `k > m`. -/
theorem ttObliqueTerm_sel_apply_cross
    (hM : ∀ k, 0 < k → k < d → IsUnit ((ttLeft A k).submatrix (Il k) id).det)
    (hN : ∀ k, 0 < k → k < d → IsUnit ((ttRight B k).submatrix (Ir k) id).det)
    (hnl : ∀ k, k + 1 < d → ∀ a, restrictLE (fun (i : Fin d) (hi : i.val < k) =>
      Nat.lt_succ_of_lt hi) (Il (k + 1) a) ∈ Set.range (Il k))
    (hnr : ∀ k, 0 < k → k + 1 < d → ∀ b, restrictLE (fun (i : Fin d) (hi : ¬ i.val < k + 1) hk =>
      hi (Nat.lt_succ_of_lt hk)) (Ir k b) ∈ Set.range (Ir (k + 1)))
    {m : ℕ} (hm : m < d) {x : ∀ i, ι i}
    (hxl : Subtype.restrict (fun i : Fin d => i.val < m) x ∈ Set.range (Il m))
    (hxr : Subtype.restrict (fun i : Fin d => ¬ i.val < m + 1) x ∈ Set.range (Ir (m + 1)))
    (k : ℕ) (Z : Tensor ι) :
    (k = m → ttLeftObliqueProj A (fun k => (1 : Matrix _ _ ℝ).submatrix id (Il k)) k
        (ttRightObliqueProj B (fun k => (1 : Matrix _ _ ℝ).submatrix id (Ir k)) (k + 1) Z) x =
      Z x) ∧
    (k < m → ttLeftObliqueProj A (fun k => (1 : Matrix _ _ ℝ).submatrix id (Il k)) k
        (ttRightObliqueProj B (fun k => (1 : Matrix _ _ ℝ).submatrix id (Ir k)) (k + 1) Z) x =
      ttLeftObliqueProj A (fun k => (1 : Matrix _ _ ℝ).submatrix id (Il k)) (k + 1)
        (ttRightObliqueProj B (fun k => (1 : Matrix _ _ ℝ).submatrix id (Ir k)) (k + 1) Z) x) ∧
    (m < k → ttLeftObliqueProj A (fun k => (1 : Matrix _ _ ℝ).submatrix id (Il k)) k
        (ttRightObliqueProj B (fun k => (1 : Matrix _ _ ℝ).submatrix id (Ir k)) (k + 1) Z) x =
      ttLeftObliqueProj A (fun k => (1 : Matrix _ _ ℝ).submatrix id (Il k)) k
        (ttRightObliqueProj B (fun k => (1 : Matrix _ _ ℝ).submatrix id (Ir k)) k Z) x) := by
  have il : ∀ j ≤ m, ∀ W,
      ttLeftObliqueProj A (fun k => (1 : Matrix _ _ ℝ).submatrix id (Il k)) j W x = W x :=
    fun j hj W => ttLeftObliqueProj_sel_apply A Il (fun h => hM j h (by omega)) W
      (restrict_lt_mem_range Il hm hnl hxl j hj)
  have ir : ∀ j, m + 1 ≤ j → ∀ W,
      ttRightObliqueProj B (fun k => (1 : Matrix _ _ ℝ).submatrix id (Ir k)) j W x = W x := by
    intro j hj W
    by_cases hjd : j < d
    · exact ttRightObliqueProj_sel_apply B Ir (fun h => hN j (by omega) h) W
        (restrict_ge_mem_range Ir hnr hxr j hj hjd)
    · rw [ttRightObliqueProj_of_le (not_lt.mp hjd)]
      rfl
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · subst h
    rw [il k le_rfl, ir (k + 1) le_rfl]
  · rw [il k h.le, il (k + 1) h]
  · rw [ttLeftObliqueProj_comm (Nat.le_succ k), ir (k + 1) (by omega),
      ttLeftObliqueProj_comm le_rfl, ir k h]

/-- **Theorem 4.1 of arXiv 2402.18721** (cross interpolation (42)). For nested index sets (38)
defining interpolatory projectors (`M_k`, `N_k` invertible for `0 < k < d`), the oblique TT
tangent projector (24) reproduces every tensor at the cross multi-indices:
`[P_Y Z](I^{≤m}_α, i, I^{>m+1}_β) = Z(I^{≤m}_α, i, I^{>m+1}_β)` for every mode `m < d` (the
paper's `j = m + 1 = 1, …, d`). A corollary of the core theorem
`ttTangentSum_actOn_apply_eq_of_interp` and the interpolation property (37). -/
theorem ttObliqueTangentProj_sel_apply_cross
    (hM : ∀ k, 0 < k → k < d → IsUnit ((ttLeft A k).submatrix (Il k) id).det)
    (hN : ∀ k, 0 < k → k < d → IsUnit ((ttRight B k).submatrix (Ir k) id).det)
    (hnl : ∀ k, k + 1 < d → ∀ a, restrictLE (fun (i : Fin d) (hi : i.val < k) =>
      Nat.lt_succ_of_lt hi) (Il (k + 1) a) ∈ Set.range (Il k))
    (hnr : ∀ k, 0 < k → k + 1 < d → ∀ b, restrictLE (fun (i : Fin d) (hi : ¬ i.val < k + 1) hk =>
      hi (Nat.lt_succ_of_lt hk)) (Ir k b) ∈ Set.range (Ir (k + 1)))
    {m : ℕ} (hm : m < d) (a : β m) (c : ι ⟨m, hm⟩) (b : β (m + 1)) (Z : Tensor ι) :
    ttObliqueTangentProj A B (fun k => (1 : Matrix _ _ ℝ).submatrix id (Il k))
      (fun k => (1 : Matrix _ _ ℝ).submatrix id (Ir k)) Z
        (assemble m hm (Il m a) c (Ir (m + 1) b)) =
      Z (assemble m hm (Il m a) c (Ir (m + 1) b)) := by
  classical
  set Ml : ∀ k : ℕ, Matrix (∀ i : {i : Fin d // i.val < k}, ι i)
      (∀ i : {i : Fin d // i.val < k}, ι i) ℝ := fun k =>
    if 0 < k then obliqueProj (ttLeft A k) ((1 : Matrix _ _ ℝ).submatrix id (Il k)) else 1
  set Mr : ∀ k : ℕ, Matrix (∀ i : {i : Fin d // ¬ i.val < k}, ι i)
      (∀ i : {i : Fin d // ¬ i.val < k}, ι i) ℝ := fun k =>
    if k < d then obliqueProj (ttRight B k) ((1 : Matrix _ _ ℝ).submatrix id (Ir k)) else 1
  set Il' : ∀ k : ℕ, Set (∀ i : {i : Fin d // i.val < k}, ι i) := fun k =>
    if k < d then Set.range (Il k) else ∅ with hIl'
  set Ir' : ∀ k : ℕ, Set (∀ i : {i : Fin d // ¬ i.val < k}, ι i) := fun k =>
    if k = 0 then ∅ else if k < d then Set.range (Ir k) else Set.univ with hIr'
  have hl : ∀ k (W : Tensor ι) (x : ∀ i, ι i), Subtype.restrict (fun i : Fin d => i.val < k) x ∈
      Il' k → actOn (fun i : Fin d => i.val < k) (Ml k) W x = W x := by
    intro k W x hx
    by_cases hk : k < d
    · simp only [hIl', hk, ↓reduceIte] at hx
      exact ttLeftObliqueProj_sel_apply A Il (fun h => hM k h hk) W hx
    · simp [hIl', hk] at hx
  have hr : ∀ k (W : Tensor ι) (x : ∀ i, ι i), Subtype.restrict (fun i : Fin d => ¬ i.val < k) x ∈
      Ir' k → actOn (fun i : Fin d => ¬ i.val < k) (Mr k) W x = W x := by
    intro k W x hx
    by_cases hk0 : k = 0
    · simp [hIr', hk0] at hx
    · by_cases hk : k < d
      · simp only [hIr', hk0, hk, ↓reduceIte] at hx
        exact ttRightObliqueProj_sel_apply B Ir (fun h => hN k (by omega) h) W hx
      · have hMr : Mr k = 1 := by simp [Mr, hk]
        rw [hMr, actOn_one]
        rfl
  have hnl' : ∀ k y, y ∈ Il' (k + 1) →
      restrictLE (fun (i : Fin d) (hi : i.val < k) => Nat.lt_succ_of_lt hi) y ∈ Il' k := by
    intro k y hy
    by_cases hk : k + 1 < d
    · simp only [hIl', hk, ↓reduceIte] at hy
      obtain ⟨a, rfl⟩ := hy
      simp only [hIl', show k < d by omega, ↓reduceIte]
      exact hnl k hk a
    · simp [hIl', hk] at hy
  have hnr' : ∀ k y, y ∈ Ir' k → restrictLE (fun (i : Fin d) (hi : ¬ i.val < k + 1) hk =>
      hi (Nat.lt_succ_of_lt hk)) y ∈ Ir' (k + 1) := by
    intro k y hy
    by_cases hk0 : k = 0
    · simp [hIr', hk0] at hy
    · by_cases hk : k < d
      · simp only [hIr', hk0, hk, ↓reduceIte] at hy
        obtain ⟨b, rfl⟩ := hy
        by_cases hk1 : k + 1 < d
        · simp only [hIr', Nat.succ_ne_zero, hk1, ↓reduceIte]
          exact hnr k (by omega) hk1 b
        · simp [hIr', hk1]
      · simp [hIr', show ¬ k + 1 < d by omega]
  have hxl : Subtype.restrict (fun i : Fin d => i.val < m)
      (assemble m hm (Il m a) c (Ir (m + 1) b)) ∈ Il' m := by
    simp only [hIl', hm, ↓reduceIte, restrict_assemble_lt]
    exact ⟨a, rfl⟩
  have hxr : Subtype.restrict (fun i : Fin d => ¬ i.val < m + 1)
      (assemble m hm (Il m a) c (Ir (m + 1) b)) ∈ Ir' (m + 1) := by
    by_cases hm1 : m + 1 < d
    · simp only [hIr', Nat.succ_ne_zero, hm1, ↓reduceIte, restrict_assemble_gt]
      exact ⟨b, rfl⟩
    · simp [hIr', hm1]
  exact ttTangentSum_actOn_apply_eq_of_interp Ml Mr Il' Ir' hl hr hnl' hnr' hm hxl hxr Z

end Cross

end TT

end LeanDLRA.Literature.P2402_18721
