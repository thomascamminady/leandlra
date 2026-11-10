import LeanDLRA.Tensor.TT.ProjectorSplitting
import LeanDLRA.Matrix.Interpolation

/-!
# Oblique TT tangent projectors and the TT tangent space

For a tensor train with left-orthogonal cores `A` (interfaces `U_{≤k} = X_{≤k}` of `A`) and
right-orthogonal cores `B` (interfaces `V_{>k}`), this file introduces

* the **TT tangent space** `ttTangentSpace A B`, the span of the single-core variations
  `U_{≤k} δC V_{>k+1} = tt (Function.update (ttMix A B k) k δC)` (the core `δC` in position `k`
  between the left cores of `A` and the right cores of `B`, `ttCoreVarₗ`): every first-order
  variation `δY = δC₁ C₂ ⋯ C_d + ⋯ + C₁ ⋯ C_{d-1} δC_d` of a tensor train in mixed canonical form
  has this form (Dektor, arXiv 2402.18721, Eq. (18) and the proof of Prop. 4.1;
  Lubich–Oseledets–Vandereycken, arXiv 1407.2042, §3);
* the **oblique interface projectors** `P_{≤k} = Ten_k(U_{≤k} (X_{≤k}ᵀ U_{≤k})⁻¹ X_{≤k}ᵀ ·)`
  (`ttLeftObliqueProj`) and `P_{>k} = Ten_k(· X_{>k} (V_{>k}ᵀ X_{>k})⁻¹ V_{>k}ᵀ)`
  (`ttRightObliqueProj`) for arbitrary test matrices `X_{≤k}`, `X_{>k}`, with
  `P_{≤0} = P_{>d} = 1` (arXiv 2402.18721, Eqs. (22)–(23)); both are `actOn` of the core matrix
  oblique projector `obliqueProj`;
* the **oblique TT tangent projector**
  `P_Y = ∑_{k=1}^{d} P_{≤k-1} P_{>k} - ∑_{k=1}^{d-1} P_{≤k} P_{>k}` (`ttObliqueTangentProj`,
  arXiv 2402.18721, Eq. (24)), the core alternating sum `ttTangentSum` of these operators.

The main theorem is that `P_Y` is a projector **onto** the TT tangent space for every choice of
test matrices with invertible `X_{≤k}ᵀ U_{≤k}`, `X_{>k}ᵀ V_{>k}`: it maps into the tangent space
(each summand is a single-core variation or a bond-centred tensor train `ttBond`,
arXiv 2402.18721, Eqs. (29) and (31)) and it fixes every single-core variation. The latter uses
only the nesting of the interfaces `U_{≤k+1} = (U_{≤k} ⊗ I) A_k^{<l>}`,
`V_{>k} = (I ⊗ V_{>k+1}) B_k^{<r>}ᵀ` and the commutation of left and right operators, and gives
the idempotence `P_Y² = P_Y` for all `d`. (The idempotence of the factors `P_{≤k}`, `P_{>k}`,
which is what the printed proof checks, does not imply it for `d ≥ 3`; compare
`ttTangentSum_idem`, which assumes range and kernel nesting of the left operators.) With the
orthonormal interfaces as test matrices `P_Y` is the orthogonal TT tangent projector
`ttTangentProj` (bridging lemma `ttObliqueTangentProj_self`), so `P_Y` is an oblique projector
onto the range of the orthogonal one in the sense of the core structure `IsObliqueProj`, and the
range of `ttTangentProj` is `ttTangentSpace A B`.

For selection (interpolation) test matrices `X = I(:, ℐ)`, written
`(1 : Matrix _ _ ℝ).submatrix id ℐ`, the operators interpolate on the selected index sets
(arXiv 2402.18721, Eqs. (35)–(37)), which feeds the cross interpolation theorem
`ttTangentSum_actOn_apply_eq_of_interp`.

## Main definitions

* `Tensor.ttCoreVarₗ`: the single-core variation `K ↦ tt (Function.update (ttMix A B k) k K)` as
  a linear map; `Tensor.ttTangentSpace`: the TT tangent space.
* `Tensor.ttLeftObliqueProj`, `Tensor.ttRightObliqueProj`, `Tensor.ttObliqueTangentProj`.

## Main results

* `actOn_apply_eq_self_of_mul_eq`: an operator `actOn p M` with `M U = U` fixes the tensors whose
  `p`-unfolding has its columns in the range of `U`; `exists_ttLeft_eq_sum`,
  `exists_ttRight_eq_sum`: nested interfaces.
* `actOn_mul_actOn_mul_eq_tt_update`: `P_{≤m} P_{>m+1} Z = U_{≤m} δC V_{>m+1}` with the explicit
  core `δC` (arXiv 2402.18721, Eqs. (26)–(29)); `actOn_mul_actOn_mul_eq_ttBond`:
  `P_{≤k} P_{>k} Z = U_{≤k} δS V_{>k}ᵀ` (Eqs. (30)–(32)). These generalize the orthogonal
  `tt_update_ttCoreCoeff` and `ttBond_ttBondCoeff` to arbitrary test matrices.
* `ttLeftObliqueProj_eq`, `ttRightObliqueProj_eq`: `P_{≤k}`, `P_{>k}` are `actOn` of
  `obliqueProj` for every `k` (also `k = 0`, `k = d`).
* `ttObliqueTangentProj_apply_mem`: `P_Y Z ∈ ttTangentSpace A B`.
* `ttObliqueTangentProj_apply_of_mem`: `P_Y W = W` for `W ∈ ttTangentSpace A B`.
* `ttObliqueTangentProj_idem`: `P_Y` is idempotent (arXiv 2402.18721, Prop. 4.1).
* `ttObliqueTangentProj_self`: with `X_{≤k} = U_{≤k}`, `X_{>k} = V_{>k}` it is `ttTangentProj`.
* `isObliqueProj_ttObliqueTangentProj`: `IsObliqueProj P_Y (ttTangentProj A B)`;
  `ttTangentProj_apply_mem`, `ttTangentProj_apply_of_mem`.
* `obliqueProj_one_submatrix_apply_self`, `ttLeftObliqueProj_sel_apply`,
  `ttRightObliqueProj_sel_apply`: interpolation property of the interpolatory projectors.

The modes are numbered `0, …, d - 1`: the paper's `P_{≤k}` acts on our modes `< k`, its `P_{>k}`
on our modes `≥ k`, and its core `C_k` is our core `k - 1`.
-/

open scoped Matrix RealInnerProductSpace

namespace LeanDLRA.Tensor

variable {d : ℕ} {ι : Fin d → Type*} {β : ℕ → Type*} [∀ k, Fintype (β k)]

/-! ### Single-core variations and the TT tangent space -/

section CoreVar

/-- The single-core variation of the mixed canonical form: the tensor train
`tt (Function.update (ttMix A B k) k K)` with the left cores `A i` (`i < k`), the core `K` in
position `k` and the right cores `B i` (`i > k`), i.e. `U_{≤k} K V_{>k+1}`. -/
theorem tt_update_ttMix_apply (A B : TTCores ι β) (k : ℕ) (hk : k < d)
    (K : β k → ι ⟨k, hk⟩ → β (k + 1) → ℝ) (x : ∀ i, ι i) :
    tt (Function.update (ttMix A B k) ⟨k, hk⟩ K) x = ∑ a, ∑ b,
      ttLeft A k (Subtype.restrict (fun i : Fin d => i.val < k) x) a * K a (x ⟨k, hk⟩) b *
        ttRight B (k + 1) (Subtype.restrict (fun i : Fin d => ¬ i.val < k + 1) x) b := by
  rw [tt_update_apply, ttLeft_ttMix A B le_rfl, ttRight_ttMix A B (Nat.le_succ k)]

/-- The single-core variation `K ↦ U_{≤k} K V_{>k+1} = tt (Function.update (ttMix A B k) k K)`
as a linear map of the core `K` (`tt_update_add`, `tt_update_smul`); the `k`-th term
`C₁ ⋯ δC_{k+1} ⋯ C_d` of Eq. (18) of arXiv 2402.18721, in 0-based numbering. -/
noncomputable def ttCoreVarₗ (A B : TTCores ι β) (k : Fin d) :
    (β k → ι k → β (k + 1) → ℝ) →ₗ[ℝ] Tensor ι where
  toFun K := tt (Function.update (ttMix A B k) k K)
  map_add' K K' := tt_update_add (ttMix A B k) k k.isLt K K'
  map_smul' c K := tt_update_smul (ttMix A B k) k k.isLt c K

@[simp] lemma ttCoreVarₗ_apply (A B : TTCores ι β) (k : Fin d)
    (K : β k → ι k → β (k + 1) → ℝ) :
    ttCoreVarₗ A B k K = tt (Function.update (ttMix A B k) k K) := rfl

/-- The **TT tangent space** at a tensor train in mixed canonical form, with left-orthogonal
cores `A` and right-orthogonal cores `B`: the span of all single-core variations
`U_{≤k} δC V_{>k+1} = tt (Function.update (ttMix A B k) k δC)`, `k = 0, …, d - 1`
(arXiv 2402.18721, Eq. (18): every first-order variation of the cores is a sum of such terms after
absorbing the gauge into the varied core; arXiv 1407.2042, §3). That it is the tangent space of
the manifold of tensor trains of fixed TT rank at `Y` (for full-rank cores) is not proved here. -/
noncomputable def ttTangentSpace (A B : TTCores ι β) : Submodule ℝ (Tensor ι) :=
  ⨆ k : Fin d, LinearMap.range (ttCoreVarₗ A B k)

/-- Single-core variations lie in the tangent space. -/
theorem tt_update_ttMix_mem_ttTangentSpace (A B : TTCores ι β) (k : ℕ) (hk : k < d)
    (K : β k → ι ⟨k, hk⟩ → β (k + 1) → ℝ) :
    tt (Function.update (ttMix A B k) ⟨k, hk⟩ K) ∈ ttTangentSpace A B :=
  Submodule.mem_iSup_of_mem (⟨k, hk⟩ : Fin d) ⟨K, rfl⟩

/-- The bond-centred tensor trains `U_{≤k} S V_{>k}ᵀ` (`ttBond`, `k < d`) lie in the tangent
space: `S` merges into core `k` (`ttBond_eq_tt`). -/
theorem ttBond_mem_ttTangentSpace (A B : TTCores ι β) {k : ℕ} (hk : k < d)
    (S : Matrix (β k) (β k) ℝ) : ttBond A B k S ∈ ttTangentSpace A B := by
  rw [ttBond_eq_tt A B k hk S]
  exact tt_update_ttMix_mem_ttTangentSpace A B k hk _

end CoreVar

/-! ### Operators that fix tensors with a given range -/

section Fix

/-- **Range criterion for oblique operators.** If `M U = U` and
`X(x) = ∑ₐ U(x_p, a) g(a, x)` with `g(a, ·)` independent of the `p`-part of the multi-index, then
`actOn p M X = X`; this generalizes `actOn_mul_transpose_apply_eq_self_of` (where `M = U Uᵀ` and
`Uᵀ U = 1`) to oblique projectors `M = U (Sᵀ U)⁻¹ Sᵀ`. -/
theorem actOn_apply_eq_self_of_mul_eq {κ : Type*} [Fintype κ] [DecidableEq κ] {ι : κ → Type*}
    [∀ k, Fintype (ι k)] {p : κ → Prop} [DecidablePred p] {r : Type*} [Fintype r]
    {M : Matrix (∀ k : Subtype p, ι k) (∀ k : Subtype p, ι k) ℝ}
    {U : Matrix (∀ k : Subtype p, ι k) r ℝ} (hMU : M * U = U) {X : Tensor ι}
    (g : r → (∀ k, ι k) → ℝ) (hg : ∀ a x z, g a (override p x z) = g a x)
    (hX : ∀ x, X x = ∑ a, U (Subtype.restrict p x) a * g a x) : actOn p M X = X := by
  ext x
  calc actOn p M X x
      = (M *ᵥ (U *ᵥ fun a => g a x)) (Subtype.restrict p x) := by
        simp only [actOn_apply, hX, restrict_override, hg, Matrix.mulVec, dotProduct]
    _ = X x := by rw [Matrix.mulVec_mulVec, hMU, hX]; rfl

/-- **Nested left interfaces**: for `j ≤ k ≤ d`,
`X_{≤k}(x_{<k}, a) = ∑_c X_{≤j}(x_{<j}, c) H(c, x, a)` with `H` independent of the first `j`
entries of `x` (the columns of `X_{≤k}` lie in the range of `X_{≤j} ⊗ I`). -/
theorem exists_ttLeft_eq_sum (A : TTCores ι β) {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ d) :
    ∃ H : β j → (∀ i, ι i) → β k → ℝ,
      (∀ c x z a, H c (override (fun i : Fin d => i.val < j) x z) a = H c x a) ∧
      ∀ x a, ttLeft A k (Subtype.restrict (fun i : Fin d => i.val < k) x) a =
        ∑ c, ttLeft A j (Subtype.restrict (fun i : Fin d => i.val < j) x) c * H c x a := by
  classical
  induction k, hjk using Nat.le_induction with
  | base =>
    exact ⟨fun c _ a => if c = a then 1 else 0, fun _ _ _ _ => rfl, fun x a => by simp⟩
  | succ k hjk ih =>
    have h : k < d := hk
    obtain ⟨H, hH, hE⟩ := ih h.le
    refine ⟨fun c x b => ∑ a, H c x a * A ⟨k, h⟩ a (x ⟨k, h⟩) b, fun c x z b => ?_,
      fun x b => ?_⟩
    · have hx : override (fun i : Fin d => i.val < j) x z ⟨k, h⟩ = x ⟨k, h⟩ :=
        override_apply_of_not (fun i : Fin d => i.val < j) (show ¬ k < j by omega)
      simp only [hH, hx]
    · rw [ttLeft_succ A k h]
      simp only [restrictLE_restrict, Subtype.restrict_apply, hE, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
      ring

/-- **Nested right interfaces**: for `j ≤ k ≤ d`,
`X_{>j}(x_{≥j}, c) = ∑_a H(c, x, a) X_{>k}(x_{≥k}, a)` with `H` independent of the entries of
`x` in the modes `≥ k`. -/
theorem exists_ttRight_eq_sum (B : TTCores ι β) {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ d) :
    ∃ H : β j → (∀ i, ι i) → β k → ℝ,
      (∀ c x z a, H c (override (fun i : Fin d => ¬ i.val < k) x z) a = H c x a) ∧
      ∀ x c, ttRight B j (Subtype.restrict (fun i : Fin d => ¬ i.val < j) x) c =
        ∑ a, H c x a * ttRight B k (Subtype.restrict (fun i : Fin d => ¬ i.val < k) x) a := by
  classical
  induction hjk using Nat.decreasingInduction with
  | self =>
    exact ⟨fun c _ a => if c = a then 1 else 0, fun _ _ _ _ => rfl, fun x c => by simp⟩
  | of_succ j hjk ih =>
    have h : j < d := by omega
    obtain ⟨H, hH, hE⟩ := ih
    refine ⟨fun c x a => ∑ b, B ⟨j, h⟩ c (x ⟨j, h⟩) b * H b x a, fun c x z a => ?_,
      fun x c => ?_⟩
    · have hx : override (fun i : Fin d => ¬ i.val < k) x z ⟨j, h⟩ = x ⟨j, h⟩ :=
        override_apply_of_not (fun i : Fin d => ¬ i.val < k) (show ¬ ¬ j < k from
          not_not.mpr hjk)
      simp only [hH, hx]
    · rw [ttRight_of_lt B j h]
      simp only [restrictLE_restrict, Subtype.restrict_apply, hE, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring

end Fix

/-! ### Products of a left and a right operator are single-core variations -/

section Range

private lemma sum_mul_sum_eq {α γ : Type*} [Fintype α] [Fintype γ] (u : α → ℝ) (L : α → γ → ℝ)
    (G : γ → ℝ) : ∑ y, (∑ a, u a * L a y) * G y = ∑ a, u a * ∑ y, L a y * G y := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun y _ => by ring

private lemma sum_four_eq {α α' γ γ' : Type*} [Fintype α] [Fintype α'] [Fintype γ] [Fintype γ']
    (u : α → ℝ) (L : α → γ → ℝ) (v : α' → ℝ) (R : α' → γ' → ℝ) (f : γ → γ' → ℝ) :
    ∑ y, (∑ a, u a * L a y) * ∑ z, (∑ b, v b * R b z) * f y z =
      ∑ a, ∑ b, u a * (∑ y, ∑ z, L a y * R b z * f y z) * v b := by
  simp_rw [sum_mul_sum_eq v R]
  rw [sum_mul_sum_eq u L]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun y _ => ?_
  refine Finset.sum_congr rfl fun z _ => ?_
  ring

variable [∀ i, Fintype (ι i)]

omit [∀ k, Fintype (β k)] [∀ i, Fintype (ι i)] in
/-- Overriding the `p`-part and then the rest gives the merge of the two new parts. -/
lemma override_not_override {κ : Type*} {ι : κ → Type*} (p : κ → Prop) [DecidablePred p]
    (x : ∀ k, ι k) (y : ∀ k : Subtype p, ι k) (z : ∀ k : {k // ¬ p k}, ι k) :
    override (fun k => ¬ p k) (override p x y) z = merge p y z := by
  funext k
  by_cases hk : p k <;> simp [override, merge, hk]

/-- **Eqs. (26)–(29) of arXiv 2402.18721.** If the left operator acting on the modes `< m` has
the form `U_{≤m} L` and the right operator acting on the modes `> m` has the form `V_{>m+1} R`,
then `P_{≤m} P_{>m+1} Z = U_{≤m} δC V_{>m+1}` is the single-core variation of core `m` by
`δC(a, c, b) = ∑_{y,z} L(a, y) R(b, z) Z(y, c, z)`. With `L = U_{≤m}ᵀ`, `R = V_{>m+1}ᵀ` this is
the orthogonal case `tt_update_ttCoreCoeff`. -/
theorem actOn_mul_actOn_mul_eq_tt_update (A B : TTCores ι β) {m : ℕ} (hm : m < d)
    (L : Matrix (β m) (∀ i : {i : Fin d // i.val < m}, ι i) ℝ)
    (R : Matrix (β (m + 1)) (∀ i : {i : Fin d // ¬ i.val < m + 1}, ι i) ℝ) (Z : Tensor ι) :
    actOn (fun i : Fin d => i.val < m) (ttLeft A m * L)
      (actOn (fun i : Fin d => ¬ i.val < m + 1) (ttRight B (m + 1) * R) Z) =
    tt (Function.update (ttMix A B m) ⟨m, hm⟩
      fun a c b => ∑ y, ∑ z, L a y * R b z * Z (assemble m hm y c z)) := by
  ext x
  have hd : ∀ i : Fin d, i.val < m → ¬ ¬ i.val < m + 1 := fun i hi => not_not.mpr (by omega)
  rw [tt_update_ttMix_apply]
  simp only [actOn_apply, restrict_override_of_disjoint hd, override_override_eq_assemble m hm,
    Matrix.mul_apply]
  exact sum_four_eq (fun a => ttLeft A m (Subtype.restrict (fun i : Fin d => i.val < m) x) a)
    (fun a y => L a y) (fun b => ttRight B (m + 1)
      (Subtype.restrict (fun i : Fin d => ¬ i.val < m + 1) x) b) (fun b z => R b z)
    (fun y z => Z (assemble m hm y (x ⟨m, hm⟩) z))

/-- **Eqs. (30)–(32) of arXiv 2402.18721.** If the operators acting on the modes `< k` and
`≥ k` have the forms `U_{≤k} L` and `V_{>k} R`, then `P_{≤k} P_{>k} Z = U_{≤k} δS V_{>k}ᵀ` is the
bond-centred tensor train with `δS(a, b) = ∑_{y,z} L(a, y) R(b, z) Z(y, z)`. With
`L = U_{≤k}ᵀ`, `R = V_{>k}ᵀ` this is the orthogonal case `ttBond_ttBondCoeff`. -/
theorem actOn_mul_actOn_mul_eq_ttBond (A B : TTCores ι β) (k : ℕ)
    (L : Matrix (β k) (∀ i : {i : Fin d // i.val < k}, ι i) ℝ)
    (R : Matrix (β k) (∀ i : {i : Fin d // ¬ i.val < k}, ι i) ℝ) (Z : Tensor ι) :
    actOn (fun i : Fin d => i.val < k) (ttLeft A k * L)
      (actOn (fun i : Fin d => ¬ i.val < k) (ttRight B k * R) Z) =
    ttBond A B k (fun a b => ∑ y, ∑ z, L a y * R b z *
      Z (merge (fun i : Fin d => i.val < k) y z)) := by
  ext x
  have hd : ∀ i : Fin d, i.val < k → ¬ ¬ i.val < k := fun i hi => not_not.mpr hi
  simp only [actOn_apply, restrict_override_of_disjoint hd,
    override_not_override (fun i : Fin d => i.val < k), Matrix.mul_apply]
  exact sum_four_eq (fun a => ttLeft A k (Subtype.restrict (fun i : Fin d => i.val < k) x) a)
    (fun a y => L a y) (fun b => ttRight B k
      (Subtype.restrict (fun i : Fin d => ¬ i.val < k) x) b) (fun b z => R b z)
    (fun y z => Z (merge (fun i : Fin d => i.val < k) y z))

end Range

/-! ### Oblique interface projectors and the oblique TT tangent projector -/

section Oblique

variable [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] [∀ k, DecidableEq (β k)]

/-- The **oblique left interface projector** `P_{≤k} Z = Ten_k(U_{≤k} (X_{≤k}ᵀ U_{≤k})⁻¹ X_{≤k}ᵀ
Z^{⟨k⟩})` of arXiv 2402.18721, Eqs. (22)–(23), acting on the modes `< k`, with test matrices
`X k = X_{≤k}`; `P_{≤0} = 1` as in the paper. -/
noncomputable def ttLeftObliqueProj (A : TTCores ι β)
    (X : ∀ k : ℕ, Matrix (∀ i : {i : Fin d // i.val < k}, ι i) (β k) ℝ) (k : ℕ) :
    Tensor ι →L[ℝ] Tensor ι :=
  actOn (fun i : Fin d => i.val < k) (if 0 < k then obliqueProj (ttLeft A k) (X k) else 1)

/-- The **oblique right interface projector** `P_{>k} Z = Ten_k(Z^{⟨k⟩} X_{>k} (V_{>k}ᵀ
X_{>k})⁻¹ V_{>k}ᵀ)` of arXiv 2402.18721, Eqs. (22)–(23), acting on the modes `≥ k` (rows of the
transposed unfolding) through `V_{>k} (X_{>k}ᵀ V_{>k})⁻¹ X_{>k}ᵀ = obliqueProj V_{>k} X_{>k}`,
with test matrices `X k = X_{>k}`; `P_{>k} = 1` for `k ≥ d`. -/
noncomputable def ttRightObliqueProj (B : TTCores ι β)
    (X : ∀ k : ℕ, Matrix (∀ i : {i : Fin d // ¬ i.val < k}, ι i) (β k) ℝ) (k : ℕ) :
    Tensor ι →L[ℝ] Tensor ι :=
  actOn (fun i : Fin d => ¬ i.val < k) (if k < d then obliqueProj (ttRight B k) (X k) else 1)

/-- The **oblique TT tangent projector** of arXiv 2402.18721, Eq. (24),
`P_Y = ∑_{k=1}^{d} P_{≤k-1} P_{>k} - ∑_{k=1}^{d-1} P_{≤k} P_{>k}`, i.e. the core alternating sum
`ttTangentSum` of the oblique interface projectors. -/
noncomputable def ttObliqueTangentProj (A B : TTCores ι β)
    (Xl : ∀ k : ℕ, Matrix (∀ i : {i : Fin d // i.val < k}, ι i) (β k) ℝ)
    (Xr : ∀ k : ℕ, Matrix (∀ i : {i : Fin d // ¬ i.val < k}, ι i) (β k) ℝ) :
    Tensor ι →L[ℝ] Tensor ι :=
  ttTangentSum (ttLeftObliqueProj A Xl) (ttRightObliqueProj B Xr) d

variable {A B : TTCores ι β}
  {Xl : ∀ k : ℕ, Matrix (∀ i : {i : Fin d // i.val < k}, ι i) (β k) ℝ}
  {Xr : ∀ k : ℕ, Matrix (∀ i : {i : Fin d // ¬ i.val < k}, ι i) (β k) ℝ}

/-- `P_{≤0} = 1`. -/
@[simp] theorem ttLeftObliqueProj_zero : ttLeftObliqueProj A Xl 0 = 1 := by
  simp [ttLeftObliqueProj]

/-- `P_{>k} = 1` for `k ≥ d`. -/
theorem ttRightObliqueProj_of_le {k : ℕ} (hk : d ≤ k) : ttRightObliqueProj B Xr k = 1 := by
  simp [ttRightObliqueProj, not_lt.mpr hk]

/-- The entries of `P_Y Z`. -/
theorem ttObliqueTangentProj_apply (Z : Tensor ι) :
    ttObliqueTangentProj A B Xl Xr Z =
      ∑ k ∈ Finset.range d, ttLeftObliqueProj A Xl k (ttRightObliqueProj B Xr (k + 1) Z) -
        ∑ k ∈ Finset.range (d - 1),
          ttLeftObliqueProj A Xl (k + 1) (ttRightObliqueProj B Xr (k + 1) Z) := by
  simp [ttObliqueTangentProj, ttTangentSum]

/-- Left and right operators commute when they act on disjoint sets of modes (`j ≤ k`). -/
theorem ttLeftObliqueProj_comm {j k : ℕ} (hjk : j ≤ k) (Z : Tensor ι) :
    ttLeftObliqueProj A Xl j (ttRightObliqueProj B Xr k Z) =
      ttRightObliqueProj B Xr k (ttLeftObliqueProj A Xl j Z) :=
  actOn_comm_of_disjoint _ (fun (i : Fin d) (hi : i.val < j) (hk : ¬ i.val < k) => hk (by omega))
    _ _ Z

/-- The matrix of `P_{≤k}` fixes the columns of `U_{≤k}`. -/
private lemma leftMat_mul (A : TTCores ι β)
    (X : ∀ k : ℕ, Matrix (∀ i : {i : Fin d // i.val < k}, ι i) (β k) ℝ) {k : ℕ}
    (hX : 0 < k → IsUnit ((X k)ᵀ * ttLeft A k).det) :
    (if 0 < k then obliqueProj (ttLeft A k) (X k) else 1) * ttLeft A k = ttLeft A k := by
  split_ifs with hk
  · exact obliqueProj_mul_self_left (hX hk)
  · exact Matrix.one_mul _

/-- The matrix of `P_{>k}` fixes the columns of `V_{>k}`. -/
private lemma rightMat_mul (B : TTCores ι β)
    (X : ∀ k : ℕ, Matrix (∀ i : {i : Fin d // ¬ i.val < k}, ι i) (β k) ℝ) {k : ℕ}
    (hX : k < d → IsUnit ((X k)ᵀ * ttRight B k).det) :
    (if k < d then obliqueProj (ttRight B k) (X k) else 1) * ttRight B k = ttRight B k := by
  split_ifs with hk
  · exact obliqueProj_mul_self_left (hX hk)
  · exact Matrix.one_mul _

/-- The matrix of `P_{≤k}` factors as `U_{≤k} L`. -/
private lemma leftMat_eq_mul [Unique (β 0)] (A : TTCores ι β)
    (X : ∀ k : ℕ, Matrix (∀ i : {i : Fin d // i.val < k}, ι i) (β k) ℝ) (k : ℕ) :
    ∃ L : Matrix (β k) (∀ i : {i : Fin d // i.val < k}, ι i) ℝ,
      (if 0 < k then obliqueProj (ttLeft A k) (X k) else 1) = ttLeft A k * L := by
  split_ifs with hk
  · exact ⟨_, Matrix.mul_assoc _ _ _⟩
  · obtain rfl : k = 0 := by omega
    refine ⟨(ttLeft A 0)ᵀ, ?_⟩
    have : IsEmpty {i : Fin d // i.val < 0} := ⟨fun i => Nat.not_lt_zero _ i.2⟩
    ext y y'
    obtain rfl := Subsingleton.elim y y'
    rw [Matrix.mul_apply, Fintype.sum_unique, Matrix.one_apply_eq]
    exact (mul_one 1).symm

/-- The matrix of `P_{>k}` factors as `V_{>k} R` (`k ≤ d`). -/
private lemma rightMat_eq_mul [Unique (β d)] (B : TTCores ι β)
    (X : ∀ k : ℕ, Matrix (∀ i : {i : Fin d // ¬ i.val < k}, ι i) (β k) ℝ) {k : ℕ} (hk : k ≤ d) :
    ∃ R : Matrix (β k) (∀ i : {i : Fin d // ¬ i.val < k}, ι i) ℝ,
      (if k < d then obliqueProj (ttRight B k) (X k) else 1) = ttRight B k * R := by
  split_ifs with hk'
  · exact ⟨_, Matrix.mul_assoc _ _ _⟩
  · obtain rfl : k = d := by omega
    refine ⟨(ttRight B k)ᵀ, ?_⟩
    have : IsEmpty {i : Fin k // ¬ i.val < k} := ⟨fun i => i.2 i.1.2⟩
    ext y y'
    obtain rfl := Subsingleton.elim y y'
    rw [Matrix.mul_apply, Fintype.sum_unique, Matrix.one_apply_eq, Matrix.transpose_apply,
      ttRight_of_le B k le_rfl]
    norm_num

/-- With an invertible `X_{≤0}ᵀ U_{≤0}` (a `1 × 1` matrix), `P_{≤0} = 1` is also the oblique
projector of `U_{≤0}`, so `P_{≤k} = Ten_k(U_{≤k} (X_{≤k}ᵀ U_{≤k})⁻¹ X_{≤k}ᵀ ·)` for every `k`. -/
theorem ttLeftObliqueProj_eq [Unique (β 0)] (hX0 : IsUnit ((Xl 0)ᵀ * ttLeft A 0).det) (k : ℕ) :
    ttLeftObliqueProj A Xl k =
      actOn (fun i : Fin d => i.val < k) (obliqueProj (ttLeft A k) (Xl k)) := by
  by_cases hk : 0 < k
  · simp only [ttLeftObliqueProj, hk, ↓reduceIte]
  · obtain rfl : k = 0 := by omega
    rw [ttLeftObliqueProj_zero]
    have : IsEmpty {i : Fin d // i.val < 0} := ⟨fun i => Nat.not_lt_zero _ i.2⟩
    suffices h : obliqueProj (ttLeft A 0) (Xl 0) = 1 by rw [h, actOn_one]
    ext y y'
    rw [Subsingleton.elim y default, Subsingleton.elim y' default]
    have h := congrFun (congrFun (obliqueProj_mul_self_left hX0) default) default
    rw [Matrix.mul_apply, Fintype.sum_unique] at h
    rw [Matrix.one_apply_eq]
    simpa using h

/-- With an invertible `X_{>d}ᵀ V_{>d}`, `P_{>d} = 1` is also the oblique projector of `V_{>d}`,
so `P_{>k} = Ten_k(· X_{>k} (V_{>k}ᵀ X_{>k})⁻¹ V_{>k}ᵀ)` for every `k ≤ d`. -/
theorem ttRightObliqueProj_eq [Unique (β d)] (hXd : IsUnit ((Xr d)ᵀ * ttRight B d).det) {k : ℕ}
    (hk : k ≤ d) : ttRightObliqueProj B Xr k =
      actOn (fun i : Fin d => ¬ i.val < k) (obliqueProj (ttRight B k) (Xr k)) := by
  by_cases hkd : k < d
  · simp only [ttRightObliqueProj, hkd, ↓reduceIte]
  · obtain rfl : k = d := by omega
    rw [ttRightObliqueProj_of_le le_rfl]
    have : IsEmpty {i : Fin k // ¬ i.val < k} := ⟨fun i => i.2 i.1.2⟩
    suffices h : obliqueProj (ttRight B k) (Xr k) = 1 by rw [h, actOn_one]
    ext y y'
    rw [Subsingleton.elim y default, Subsingleton.elim y' default]
    have h := congrFun (congrFun (obliqueProj_mul_self_left hXd) default) default
    rw [Matrix.mul_apply, Fintype.sum_unique, ttRight_of_le B k le_rfl] at h
    rw [Matrix.one_apply_eq, ttRight_of_le B k le_rfl]
    simpa using h

/-! #### `P_Y` maps into the tangent space -/

/-- `P_{≤m} P_{>m+1} Z` is a single-core variation of core `m`. -/
theorem ttLeftObliqueProj_mul_ttRightObliqueProj_mem [Unique (β 0)] [Unique (β d)] {m : ℕ}
    (hm : m < d) (Z : Tensor ι) :
    ttLeftObliqueProj A Xl m (ttRightObliqueProj B Xr (m + 1) Z) ∈ ttTangentSpace A B := by
  obtain ⟨L, hL⟩ := leftMat_eq_mul A Xl m
  obtain ⟨R, hR⟩ := rightMat_eq_mul B Xr (k := m + 1) hm
  rw [ttLeftObliqueProj, ttRightObliqueProj, hL, hR, actOn_mul_actOn_mul_eq_tt_update A B hm]
  exact tt_update_ttMix_mem_ttTangentSpace A B m hm _

/-- `P_{≤k} P_{>k} Z` is a bond-centred tensor train, hence in the tangent space
(`0 < k < d`). -/
theorem ttLeftObliqueProj_mul_ttRightObliqueProj_self_mem {k : ℕ} (hk0 : 0 < k) (hk : k < d)
    (Z : Tensor ι) :
    ttLeftObliqueProj A Xl k (ttRightObliqueProj B Xr k Z) ∈ ttTangentSpace A B := by
  have hL : (if 0 < k then obliqueProj (ttLeft A k) (Xl k) else 1) =
      ttLeft A k * (((Xl k)ᵀ * ttLeft A k)⁻¹ * (Xl k)ᵀ) := by
    simp only [hk0, ↓reduceIte]
    rw [obliqueProj, Matrix.mul_assoc]
  have hR : (if k < d then obliqueProj (ttRight B k) (Xr k) else 1) =
      ttRight B k * (((Xr k)ᵀ * ttRight B k)⁻¹ * (Xr k)ᵀ) := by
    simp only [hk, ↓reduceIte]
    rw [obliqueProj, Matrix.mul_assoc]
  rw [ttLeftObliqueProj, ttRightObliqueProj, hL, hR, actOn_mul_actOn_mul_eq_ttBond A B k]
  exact ttBond_mem_ttTangentSpace A B hk _

/-- **`P_Y` maps into the TT tangent space** (arXiv 2402.18721, Prop. 4.1, first part; every
summand is a single-core variation, Eqs. (29) and (33)). No invertibility is needed. -/
theorem ttObliqueTangentProj_apply_mem [Unique (β 0)] [Unique (β d)] (Z : Tensor ι) :
    ttObliqueTangentProj A B Xl Xr Z ∈ ttTangentSpace A B := by
  rw [ttObliqueTangentProj_apply]
  refine Submodule.sub_mem _ (Submodule.sum_mem _ fun m hm => ?_)
    (Submodule.sum_mem _ fun m hm => ?_)
  · exact ttLeftObliqueProj_mul_ttRightObliqueProj_mem (Finset.mem_range.mp hm) Z
  · exact ttLeftObliqueProj_mul_ttRightObliqueProj_self_mem (Nat.succ_pos m)
      (by have := Finset.mem_range.mp hm; omega) Z

/-! #### `P_Y` fixes the tangent space -/

/-- `P_{≤j}` fixes every variation of a core `k ≥ j`. -/
theorem ttLeftObliqueProj_tt_update
    (hXl : ∀ k, 0 < k → k < d → IsUnit ((Xl k)ᵀ * ttLeft A k).det) {j k : ℕ} (hk : k < d)
    (hjk : j ≤ k) (K : β k → ι ⟨k, hk⟩ → β (k + 1) → ℝ) :
    ttLeftObliqueProj A Xl j (tt (Function.update (ttMix A B k) ⟨k, hk⟩ K)) =
      tt (Function.update (ttMix A B k) ⟨k, hk⟩ K) := by
  obtain ⟨H, hH, hE⟩ := exists_ttLeft_eq_sum A hjk hk.le
  refine actOn_apply_eq_self_of_mul_eq (leftMat_mul A Xl fun hj => hXl j hj (by omega))
    (fun c x => ∑ a, ∑ b, H c x a * K a (x ⟨k, hk⟩) b *
      ttRight B (k + 1) (Subtype.restrict (fun i : Fin d => ¬ i.val < k + 1) x) b)
    (fun c x z => ?_) (fun x => ?_)
  · have hxk : override (fun i : Fin d => i.val < j) x z ⟨k, hk⟩ = x ⟨k, hk⟩ :=
      override_apply_of_not (fun i : Fin d => i.val < j) (show ¬ k < j by omega)
    have hr : Subtype.restrict (fun i : Fin d => ¬ i.val < k + 1)
        (override (fun i : Fin d => i.val < j) x z) =
        Subtype.restrict (fun i : Fin d => ¬ i.val < k + 1) x :=
      restrict_override_of_disjoint (fun (i : Fin d) (hi : i.val < j) hk => hk (by omega)) x z
    simp only [hH, hxk, hr]
  · rw [tt_update_ttMix_apply]
    simp only [hE, Finset.sum_mul, Finset.mul_sum]
    conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

/-- `P_{>j}` fixes every variation of a core `k < j` (`j ≤ d`). -/
theorem ttRightObliqueProj_tt_update
    (hXr : ∀ k, 0 < k → k < d → IsUnit ((Xr k)ᵀ * ttRight B k).det) {j k : ℕ} (hk : k < d)
    (hkj : k + 1 ≤ j) (hj : j ≤ d) (K : β k → ι ⟨k, hk⟩ → β (k + 1) → ℝ) :
    ttRightObliqueProj B Xr j (tt (Function.update (ttMix A B k) ⟨k, hk⟩ K)) =
      tt (Function.update (ttMix A B k) ⟨k, hk⟩ K) := by
  obtain ⟨H, hH, hE⟩ := exists_ttRight_eq_sum B hkj hj
  refine actOn_apply_eq_self_of_mul_eq (rightMat_mul B Xr fun hj' => hXr j (by omega) hj')
    (fun c x => ∑ a, ∑ b, ttLeft A k (Subtype.restrict (fun i : Fin d => i.val < k) x) a *
      K a (x ⟨k, hk⟩) b * H b x c) (fun c x z => ?_) (fun x => ?_)
  · have hxk : override (fun i : Fin d => ¬ i.val < j) x z ⟨k, hk⟩ = x ⟨k, hk⟩ :=
      override_apply_of_not (fun i : Fin d => ¬ i.val < j)
        (show ¬ ¬ k < j from not_not.mpr (by omega))
    have hl : Subtype.restrict (fun i : Fin d => i.val < k)
        (override (fun i : Fin d => ¬ i.val < j) x z) =
        Subtype.restrict (fun i : Fin d => i.val < k) x :=
      restrict_override_of_disjoint (fun (i : Fin d) (hi : ¬ i.val < j) hk => hi (by omega)) x z
    simp only [hH, hxk, hl]
  · rw [tt_update_ttMix_apply]
    simp only [hE, Finset.mul_sum]
    conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

/-- The arithmetic of the alternating sum: if `aₖ = bₖ` for `k < m`, `a_m = z` and
`aₖ = b_{k-1}` for `m < k < d`, then `∑_{k<d} aₖ - ∑_{k<d-1} bₖ = z`. -/
private lemma sum_sub_sum_eq_of_shift {M : Type*} [AddCommGroup M] {a b : ℕ → M} {m d : ℕ}
    {z : M} (hm : m < d) (hlt : ∀ k < m, a k = b k) (heq : a m = z)
    (hgt : ∀ k, m < k → k < d → a k = b (k - 1)) :
    ∑ k ∈ Finset.range d, a k - ∑ k ∈ Finset.range (d - 1), b k = z := by
  obtain ⟨n, rfl⟩ : ∃ n, d = m + 1 + n := ⟨d - (m + 1), by omega⟩
  have e1 : ∑ k ∈ Finset.range (m + 1 + n), a k =
      ∑ k ∈ Finset.range m, b k + z + ∑ j ∈ Finset.range n, b (m + j) := by
    rw [Finset.sum_range_add, Finset.sum_range_succ,
      Finset.sum_congr rfl fun k hk => hlt k (Finset.mem_range.mp hk), heq]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hgt (m + 1 + j) (by omega) (by have := Finset.mem_range.mp hj; omega)]
    congr 1
    omega
  have e2 : ∑ k ∈ Finset.range (m + 1 + n - 1), b k =
      ∑ k ∈ Finset.range m, b k + ∑ j ∈ Finset.range n, b (m + j) := by
    rw [show m + 1 + n - 1 = m + n by omega, Finset.sum_range_add]
  rw [e1, e2]
  abel

/-- **`P_Y` fixes every single-core variation.** -/
theorem ttObliqueTangentProj_tt_update
    (hXl : ∀ k, 0 < k → k < d → IsUnit ((Xl k)ᵀ * ttLeft A k).det)
    (hXr : ∀ k, 0 < k → k < d → IsUnit ((Xr k)ᵀ * ttRight B k).det)
    {k : ℕ} (hk : k < d) (K : β k → ι ⟨k, hk⟩ → β (k + 1) → ℝ) :
    ttObliqueTangentProj A B Xl Xr (tt (Function.update (ttMix A B k) ⟨k, hk⟩ K)) =
      tt (Function.update (ttMix A B k) ⟨k, hk⟩ K) := by
  set W := tt (Function.update (ttMix A B k) ⟨k, hk⟩ K)
  have il : ∀ j, j ≤ k → ttLeftObliqueProj A Xl j W = W := fun j hj =>
    ttLeftObliqueProj_tt_update hXl hk hj K
  have ir : ∀ j, k + 1 ≤ j → j ≤ d → ttRightObliqueProj B Xr j W = W := fun j hj hjd =>
    ttRightObliqueProj_tt_update hXr hk hj hjd K
  rw [ttObliqueTangentProj_apply]
  refine sum_sub_sum_eq_of_shift hk (fun j hj => ?_) ?_ (fun j hkj hjd => ?_)
  · rw [ttLeftObliqueProj_comm (Nat.le_succ j), il j hj.le, ttLeftObliqueProj_comm le_rfl,
      il (j + 1) hj]
  · rw [ir (k + 1) le_rfl hk, il k le_rfl]
  · obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [Nat.add_sub_cancel, ir (j + 1 + 1) (by omega) (by omega), ir (j + 1) (by omega) hjd.le]

/-- **`P_Y` fixes the TT tangent space.** -/
theorem ttObliqueTangentProj_apply_of_mem
    (hXl : ∀ k, 0 < k → k < d → IsUnit ((Xl k)ᵀ * ttLeft A k).det)
    (hXr : ∀ k, 0 < k → k < d → IsUnit ((Xr k)ᵀ * ttRight B k).det)
    {W : Tensor ι} (hW : W ∈ ttTangentSpace A B) : ttObliqueTangentProj A B Xl Xr W = W := by
  refine Submodule.iSup_induction (fun k : Fin d => LinearMap.range (ttCoreVarₗ A B k))
    (motive := fun W => ttObliqueTangentProj A B Xl Xr W = W) hW (fun k W hW => ?_)
    (map_zero _) (fun W W' h h' => by rw [map_add, h, h'])
  obtain ⟨K, rfl⟩ := hW
  exact ttObliqueTangentProj_tt_update hXl hXr k.isLt K

/-- **Prop. 4.1 of arXiv 2402.18721 (idempotence)**: the oblique TT tangent projector is
idempotent, for any test matrices with invertible `X_{≤k}ᵀ U_{≤k}`, `X_{>k}ᵀ V_{>k}`
(`0 < k < d`). -/
theorem ttObliqueTangentProj_idem [Unique (β 0)] [Unique (β d)]
    (hXl : ∀ k, 0 < k → k < d → IsUnit ((Xl k)ᵀ * ttLeft A k).det)
    (hXr : ∀ k, 0 < k → k < d → IsUnit ((Xr k)ᵀ * ttRight B k).det) (Z : Tensor ι) :
    ttObliqueTangentProj A B Xl Xr (ttObliqueTangentProj A B Xl Xr Z) =
      ttObliqueTangentProj A B Xl Xr Z :=
  ttObliqueTangentProj_apply_of_mem hXl hXr (ttObliqueTangentProj_apply_mem Z)

end Oblique

/-! ### The orthogonal TT tangent projector as a special case -/

section Orthogonal

variable [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] [∀ k, DecidableEq (β k)]
  {A B : TTCores ι β}

/-- With the orthonormal interfaces as test matrices, the oblique left interface projector is the
orthogonal one: `U (Uᵀ U)⁻¹ Uᵀ = U Uᵀ`. -/
theorem ttLeftObliqueProj_self [Unique (β 0)] (hA : ∀ i, IsLeftOrth A i) {k : ℕ} (hk : k ≤ d) :
    ttLeftObliqueProj A (fun k => ttLeft A k) k = ttLeftProj A k := by
  by_cases h0 : 0 < k
  · simp only [ttLeftObliqueProj, h0, ↓reduceIte]
    rw [obliqueProj_self_of_orthonormal (ttLeft_transpose_mul_self k hk fun i _ => hA i)]
    rfl
  · obtain rfl : k = 0 := by omega
    rw [ttLeftObliqueProj_zero, ttLeftProj_zero]

/-- With the orthonormal interfaces as test matrices, the oblique right interface projector is
the orthogonal one. -/
theorem ttRightObliqueProj_self [Unique (β d)] (hB : ∀ i, IsRightOrth B i) {k : ℕ}
    (hk : k ≤ d) : ttRightObliqueProj B (fun k => ttRight B k) k = ttRightProj B k := by
  by_cases hd : k < d
  · simp only [ttRightObliqueProj, hd, ↓reduceIte]
    rw [obliqueProj_self_of_orthonormal (ttRight_transpose_mul_self k hk fun i _ => hB i)]
    rfl
  · obtain rfl : k = d := by omega
    rw [ttRightObliqueProj_of_le le_rfl, ttRightProj_self]

/-- **Bridging lemma**: with the orthonormal interfaces `X_{≤k} = U_{≤k}`, `X_{>k} = V_{>k}` as
test matrices, the oblique TT tangent projector is the orthogonal TT tangent projector
`ttTangentProj` (arXiv 2402.18721, Eq. (21) as the special case of Eq. (24)). -/
theorem ttObliqueTangentProj_self [Unique (β 0)] [Unique (β d)] (hA : ∀ i, IsLeftOrth A i)
    (hB : ∀ i, IsRightOrth B i) :
    ttObliqueTangentProj A B (fun k => ttLeft A k) (fun k => ttRight B k) = ttTangentProj A B := by
  rw [ttObliqueTangentProj, ttTangentProj, ttTangentSum, ttTangentSum]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk := Finset.mem_range.mp hk
    rw [ttLeftObliqueProj_self hA hk.le, ttRightObliqueProj_self hB hk]
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk := Finset.mem_range.mp hk
    rw [ttLeftObliqueProj_self hA (by omega), ttRightObliqueProj_self hB (by omega)]

omit [∀ i, DecidableEq (ι i)] in
/-- The orthonormal interfaces satisfy the invertibility hypotheses (`U_{≤k}ᵀ U_{≤k} = 1`). -/
theorem isUnit_det_ttLeft_transpose_mul [Unique (β 0)] (hA : ∀ i, IsLeftOrth A i) :
    ∀ k, 0 < k → k < d → IsUnit ((ttLeft A k)ᵀ * ttLeft A k).det := fun k _ hk => by
  rw [ttLeft_transpose_mul_self k hk.le fun i _ => hA i, Matrix.det_one]
  exact isUnit_one

omit [∀ i, DecidableEq (ι i)] in
/-- The orthonormal right interfaces satisfy the invertibility hypotheses. -/
theorem isUnit_det_ttRight_transpose_mul [Unique (β d)] (hB : ∀ i, IsRightOrth B i) :
    ∀ k, 0 < k → k < d → IsUnit ((ttRight B k)ᵀ * ttRight B k).det := fun k _ hk => by
  rw [ttRight_transpose_mul_self k hk.le fun i _ => hB i, Matrix.det_one]
  exact isUnit_one

omit [∀ i, DecidableEq (ι i)] in
/-- The orthogonal TT tangent projector maps into the TT tangent space. -/
theorem ttTangentProj_apply_mem [Unique (β 0)] [Unique (β d)] (hA : ∀ i, IsLeftOrth A i)
    (hB : ∀ i, IsRightOrth B i) (Z : Tensor ι) : ttTangentProj A B Z ∈ ttTangentSpace A B := by
  classical
  rw [← ttObliqueTangentProj_self hA hB]
  exact ttObliqueTangentProj_apply_mem Z

omit [∀ i, DecidableEq (ι i)] in
/-- The orthogonal TT tangent projector fixes the TT tangent space; with
`ttTangentProj_apply_mem` and `isOrthProj_ttTangentProj`, it is the orthogonal projector onto
`ttTangentSpace A B`. -/
theorem ttTangentProj_apply_of_mem [Unique (β 0)] [Unique (β d)] (hA : ∀ i, IsLeftOrth A i)
    (hB : ∀ i, IsRightOrth B i) {W : Tensor ι} (hW : W ∈ ttTangentSpace A B) :
    ttTangentProj A B W = W := by
  classical
  rw [← ttObliqueTangentProj_self hA hB]
  exact ttObliqueTangentProj_apply_of_mem (isUnit_det_ttLeft_transpose_mul hA)
    (isUnit_det_ttRight_transpose_mul hB) hW

/-- **The oblique TT tangent projector is an oblique projector onto the TT tangent space**
(arXiv 2402.18721, Prop. 4.1), in the sense of the core structure `IsObliqueProj`: it fixes the
range of the orthogonal TT tangent projector `ttTangentProj A B` and maps into it, for any test
matrices with invertible `X_{≤k}ᵀ U_{≤k}`, `X_{>k}ᵀ V_{>k}` (`0 < k < d`). Hence the generic
quasi-optimality bounds for oblique projectors (`IsObliqueProj.norm_sub_le_opNorm`) apply. -/
theorem isObliqueProj_ttObliqueTangentProj [Unique (β 0)] [Unique (β d)]
    (hA : ∀ i, IsLeftOrth A i) (hB : ∀ i, IsRightOrth B i)
    {Xl : ∀ k : ℕ, Matrix (∀ i : {i : Fin d // i.val < k}, ι i) (β k) ℝ}
    {Xr : ∀ k : ℕ, Matrix (∀ i : {i : Fin d // ¬ i.val < k}, ι i) (β k) ℝ}
    (hXl : ∀ k, 0 < k → k < d → IsUnit ((Xl k)ᵀ * ttLeft A k).det)
    (hXr : ∀ k, 0 < k → k < d → IsUnit ((Xr k)ᵀ * ttRight B k).det) :
    IsObliqueProj (ttObliqueTangentProj A B Xl Xr) (ttTangentProj A B) where
  orth := isOrthProj_ttTangentProj hA hB
  fix x := ttObliqueTangentProj_apply_of_mem hXl hXr (ttTangentProj_apply_mem hA hB x)
  range x := ttTangentProj_apply_of_mem hA hB (ttObliqueTangentProj_apply_mem x)

end Orthogonal

/-! ### Interpolatory projectors -/

section Interpolation

/-- For the selection matrix `S = I(:, ℐ)` (`(1 : Matrix m m ℝ).submatrix id ℐ`), `Sᵀ U` is the
row submatrix `U(ℐ, :)`. -/
theorem transpose_one_submatrix_mul {m r n : Type*} [Fintype m] [DecidableEq m] (I : r → m)
    (U : Matrix m n ℝ) : ((1 : Matrix m m ℝ).submatrix id I)ᵀ * U = U.submatrix I id := by
  ext a b
  simp [Matrix.mul_apply, Matrix.one_apply]

/-- **Interpolation property of the interpolatory projector** `U U(ℐ, :)⁻¹ I(:, ℐ)ᵀ`
(arXiv 2402.18721, Eq. (36)): its rows at the selected indices are unit rows. -/
theorem obliqueProj_one_submatrix_apply_self {m r : Type*} [Fintype m] [DecidableEq m]
    [Fintype r] [DecidableEq r] {U : Matrix m r ℝ} {I : r → m}
    (hU : IsUnit (U.submatrix I id).det) (a : r) (z : m) :
    obliqueProj U ((1 : Matrix m m ℝ).submatrix id I) (I a) z = (1 : Matrix m m ℝ) (I a) z := by
  have h := congrFun (congrFun (transpose_mul_obliqueProj
    (S := (1 : Matrix m m ℝ).submatrix id I) (U := U)
    (by rwa [transpose_one_submatrix_mul])) a) z
  simpa [Matrix.mul_apply, Matrix.one_apply, eq_comm] using h

variable [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] [∀ k, DecidableEq (β k)]

/-- **Interpolation of `P_{≤k}`** (arXiv 2402.18721, Eq. (37)): with the selection matrices of
index maps `Il k : β k → (multi-indices of the modes < k)` and invertible `U_{≤k}(I^{≤k}, :)`,
`[P_{≤k} Z](x) = Z(x)` whenever the first `k` entries of `x` are a selected multi-index. -/
theorem ttLeftObliqueProj_sel_apply (A : TTCores ι β)
    (Il : ∀ k : ℕ, β k → ∀ i : {i : Fin d // i.val < k}, ι i) {k : ℕ}
    (hM : 0 < k → IsUnit ((ttLeft A k).submatrix (Il k) id).det) (Z : Tensor ι) {x : ∀ i, ι i}
    (hx : Subtype.restrict (fun i : Fin d => i.val < k) x ∈ Set.range (Il k)) :
    ttLeftObliqueProj A (fun k => (1 : Matrix _ _ ℝ).submatrix id (Il k)) k Z x = Z x := by
  refine actOn_apply_eq_of_row_eq_one (I := Set.range (Il k)) ?_ Z hx
  rintro _ ⟨a, rfl⟩ z
  split_ifs with hk
  · exact obliqueProj_one_submatrix_apply_self (hM hk) a z
  · rfl

/-- **Interpolation of `P_{>k}`** (arXiv 2402.18721, Eq. (37)): with the selection matrices of
index maps `Ir k : β k → (multi-indices of the modes ≥ k)` and invertible `V_{>k}(I^{>k}, :)`,
`[P_{>k} Z](x) = Z(x)` whenever the entries of `x` in the modes `≥ k` are a selected
multi-index. -/
theorem ttRightObliqueProj_sel_apply (B : TTCores ι β)
    (Ir : ∀ k : ℕ, β k → ∀ i : {i : Fin d // ¬ i.val < k}, ι i) {k : ℕ}
    (hN : k < d → IsUnit ((ttRight B k).submatrix (Ir k) id).det) (Z : Tensor ι)
    {x : ∀ i, ι i}
    (hx : Subtype.restrict (fun i : Fin d => ¬ i.val < k) x ∈ Set.range (Ir k)) :
    ttRightObliqueProj B (fun k => (1 : Matrix _ _ ℝ).submatrix id (Ir k)) k Z x = Z x := by
  refine actOn_apply_eq_of_row_eq_one (I := Set.range (Ir k)) ?_ Z hx
  rintro _ ⟨a, rfl⟩ z
  split_ifs with hk
  · exact obliqueProj_one_submatrix_apply_self (hN hk) a z
  · rfl

end Interpolation

/-! ### Examples -/

/-- Non-vacuity of `isObliqueProj_ttObliqueTangentProj`: the rank-one tensor train with cores
`C(α, x, α') = [x = 0]` on two modes of size two, with its own interfaces as test matrices. -/
example : let C : TTCores (d := 2) (fun _ => Fin 2) (fun _ => Fin 1) :=
      fun _ _ x _ => if x = 0 then 1 else 0
    IsObliqueProj (ttObliqueTangentProj C C (fun k => ttLeft C k) (fun k => ttRight C k))
      (ttTangentProj C C) := by
  intro C
  have hA : ∀ i, IsLeftOrth C i := fun _ b b' => by
    obtain rfl := Subsingleton.elim b b'
    change ∑ _a : Fin 1, ∑ x : Fin 2, (if x = 0 then (1 : ℝ) else 0) *
      (if x = 0 then 1 else 0) = (1 : Matrix (Fin 1) (Fin 1) ℝ) b b
    simp
  have hB : ∀ i, IsRightOrth C i := fun _ a a' => by
    obtain rfl := Subsingleton.elim a a'
    change ∑ x : Fin 2, ∑ _b : Fin 1, (if x = 0 then (1 : ℝ) else 0) *
      (if x = 0 then 1 else 0) = (1 : Matrix (Fin 1) (Fin 1) ℝ) a a
    simp
  exact isObliqueProj_ttObliqueTangentProj hA hB (isUnit_det_ttLeft_transpose_mul hA)
    (isUnit_det_ttRight_transpose_mul hB)

end LeanDLRA.Tensor
