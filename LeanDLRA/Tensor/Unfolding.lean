import LeanDLRA.Tensor.Defs

/-!
# Unfoldings and linear maps acting on a set of modes

This file develops the basic algebra of the tensor layer (`LeanDLRA.Tensor.Defs`): sums over
multi-indices, the unfolding `unfold p` as an isometry onto matrices with the Frobenius inner
product, and the linear maps `actOn p M` that act on the modes in `p`. These are the facts used
everywhere in the analysis of Tucker, TT and TTN integrators: mode projectors are orthogonal
projectors, projectors acting on disjoint sets of modes commute, and a projector
`actOn p (U Uᵀ)` fixes exactly the tensors whose `p`-unfolding has its columns in the range of
`U`.

## Main results

* `sum_eq_sum_merge`: a sum over multi-indices splits into the `p`-part and the rest.
* `inner_unfold`, `norm_unfold`: the unfolding is an isometry (Frobenius norm);
  `unfold_injective`, `fold_unfold`, `unfold_fold`; `rank_unfold_add_le`: subadditivity of
  unfolding ranks.
* `unfold_actOn`: `unfold p (actOn p M X) = M * unfold p X`; `actOn_eq_fold`.
* `actOn_actOn`, `actOn_mul`, `actOn_one`, `actOn_add`, `actOn_sub`, `actOn_zero`: `actOn p` is a
  unital ring homomorphism from matrices on the `p`-part to operators.
* `actOn_comm_of_disjoint`: maps acting on disjoint sets of modes commute.
* `inner_actOn`: the adjoint of `actOn p M` is `actOn p Mᵀ`.
* `isOrthProj_actOn`, `isOrthProj_actOn_mul_transpose`: `actOn p (U Uᵀ)` is an orthogonal
  projector when `Uᵀ U = 1`.
* `actOn_mul_transpose_eq_self_iff`: it fixes `X` iff `unfold p X = U W` for some `W`;
  `actOn_mul_transpose_apply_eq_self_of` gives the pointwise sufficient condition used for nested
  bases.
* `actOn_of_forall_not`: on the empty set of modes, `actOn p M = M₀₀ • 1`.
* `modeAct_apply`, `isOrthProj_modeProj`, `modeAct_comm`: mode-wise action and mode projectors.
* `inner_tucker`, `norm_tucker`: the Tucker tensor with orthonormal basis matrices is an
  isometric image of its core; `modeProj_tucker`: it is fixed by its mode projectors.
-/

open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius

namespace LeanDLRA.Tensor

variable {κ : Type*} {ι : κ → Type*}

/-- Overriding the `p`-part of `merge p a b` by `z` gives `merge p z b`. -/
@[simp] lemma override_merge (p : κ → Prop) [DecidablePred p] (a z : ∀ k : Subtype p, ι k)
    (b : ∀ k : {k // ¬ p k}, ι k) : override p (merge p a b) z = merge p z b := by
  funext k; by_cases h : p k <;> simp [override, merge, h]

/-! ### Unfolding and folding -/

section UnfoldBasic

variable (p : κ → Prop) [DecidablePred p]

/-- The entries of the unfolding. -/
@[simp] lemma unfold_apply (X : Tensor ι) (a : ∀ k : Subtype p, ι k)
    (b : ∀ k : {k // ¬ p k}, ι k) : unfold p X a b = X (merge p a b) := rfl

/-- The entries of the tensorization. -/
@[simp] lemma fold_apply (A : Matrix (∀ k : Subtype p, ι k) (∀ k : {k // ¬ p k}, ι k) ℝ)
    (x : ∀ k, ι k) :
    fold p A x = A (Subtype.restrict p x) (Subtype.restrict (fun k => ¬ p k) x) := rfl

/-- Tensorization inverts unfolding. -/
@[simp] theorem fold_unfold (X : Tensor ι) : fold p (unfold p X) = X := by
  ext x; simp

/-- Unfolding inverts tensorization. -/
@[simp] theorem unfold_fold (A : Matrix (∀ k : Subtype p, ι k) (∀ k : {k // ¬ p k}, ι k) ℝ) :
    unfold p (fold p A) = A := by
  ext a b; simp

/-- The unfolding is injective. -/
theorem unfold_injective : Function.Injective (unfold p : Tensor ι → _) :=
  Function.LeftInverse.injective (fold_unfold p)

/-- The unfolding is additive. -/
@[simp] lemma unfold_add (X Y : Tensor ι) : unfold p (X + Y) = unfold p X + unfold p Y := rfl

/-- The unfolding commutes with subtraction. -/
@[simp] lemma unfold_sub (X Y : Tensor ι) : unfold p (X - Y) = unfold p X - unfold p Y := rfl

/-- The unfolding commutes with scalar multiplication. -/
@[simp] lemma unfold_smul (c : ℝ) (X : Tensor ι) : unfold p (c • X) = c • unfold p X := rfl

/-- The unfolding of zero is zero. -/
@[simp] lemma unfold_zero : unfold p (0 : Tensor ι) = 0 := rfl

end UnfoldBasic

variable [Fintype κ] [DecidableEq κ] [∀ k, Fintype (ι k)]

/-! ### Sums and inner products -/

/-- For a matrix `L` with orthonormal columns, `∑_y (L u)_y (L v)_y = ∑_a u_a v_a`. -/
theorem sum_mulVec_mul_mulVec_of_orthonormal {Y R : Type*} [Fintype Y] [Fintype R]
    [DecidableEq R] {L : Matrix Y R ℝ} (hL : Lᵀ * L = 1) (u v : R → ℝ) :
    ∑ y, (∑ a, L y a * u a) * (∑ a, L y a * v a) = ∑ a, u a * v a := by
  change (L *ᵥ u) ⬝ᵥ (L *ᵥ v) = u ⬝ᵥ v
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hL,
    Matrix.one_mulVec]


/-- The inner product of two tensors is the sum of the products of their entries. -/
theorem inner_eq_sum (X Y : Tensor ι) : ⟪X, Y⟫ = ∑ x, X x * Y x := by
  simp [PiLp.inner_apply, mul_comm]

section Split

variable (p : κ → Prop) [DecidablePred p]

/-- A sum over all multi-indices splits into a sum over the `p`-part and the remaining part. -/
theorem sum_eq_sum_merge (f : (∀ k, ι k) → ℝ) : ∑ x, f x = ∑ a, ∑ b, f (merge p a b) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd p ι) _ _ fun x =>
    congrArg f (merge_restrict p x).symm

/-- The change of variables `(x, z) ↦ (x with p-part z, x_p)` is an involution, so it preserves
sums. -/
theorem sum_sum_override (f : (∀ k, ι k) → (∀ k : Subtype p, ι k) → ℝ) :
    ∑ x, ∑ z, f x z = ∑ x, ∑ z, f (override p x z) (Subtype.restrict p x) := by
  have hinv : Function.Involutive fun xz : (∀ k, ι k) × (∀ k : Subtype p, ι k) =>
      (override p xz.1 xz.2, Subtype.restrict p xz.1) := fun xz => by simp
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (hinv.toPerm _) _ _ fun xz => by simp

end Split

section Unfold

variable (p : κ → Prop) [DecidablePred p]

/-- The unfolding preserves the inner product (Frobenius inner product on matrices). -/
theorem inner_unfold (X Y : Tensor ι) : ⟪unfold p X, unfold p Y⟫ = ⟪X, Y⟫ := by
  rw [inner_eq_sum, sum_eq_sum_merge p, Frobenius.inner_def]
  rfl

/-- The unfolding preserves the norm (Frobenius norm on matrices). -/
theorem norm_unfold (X : Tensor ι) : ‖unfold p X‖ = ‖X‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner (F := Tensor ι), inner_unfold]

/-- **Ranks of unfoldings are subadditive**: the `p`-rank of `X + Y` is at most the sum of the
`p`-ranks (for TT cuts: the bond dimension of a sum of tensor trains is at most the sum of the
bond dimensions, as used for augmented bases). -/
theorem rank_unfold_add_le (X Y : Tensor ι) :
    (unfold p (X + Y)).rank ≤ (unfold p X).rank + (unfold p Y).rank := by
  rw [unfold_add]
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

end Unfold

/-! ### Maps acting on a set of modes -/

section ActOn

variable (p : κ → Prop) [DecidablePred p]

/-- Acting on the modes in `p` is left multiplication of the `p`-unfolding. -/
theorem unfold_actOn (M : Matrix (∀ k : Subtype p, ι k) (∀ k : Subtype p, ι k) ℝ)
    (X : Tensor ι) : unfold p (actOn p M X) = M * unfold p X := by
  ext a b; simp [Matrix.mul_apply]

/-- `actOn p M X = Ten_p(M Mat_p(X))`. -/
theorem actOn_eq_fold (M : Matrix (∀ k : Subtype p, ι k) (∀ k : Subtype p, ι k) ℝ)
    (X : Tensor ι) : actOn p M X = fold p (M * unfold p X) := by
  rw [← unfold_actOn, fold_unfold]

/-- Composition of maps acting on the same modes multiplies their matrices. -/
theorem actOn_actOn (M N : Matrix (∀ k : Subtype p, ι k) (∀ k : Subtype p, ι k) ℝ)
    (X : Tensor ι) : actOn p M (actOn p N X) = actOn p (M * N) X := by
  refine unfold_injective p ?_
  rw [unfold_actOn, unfold_actOn, unfold_actOn, Matrix.mul_assoc]

/-- `actOn p` is multiplicative. -/
theorem actOn_mul (M N : Matrix (∀ k : Subtype p, ι k) (∀ k : Subtype p, ι k) ℝ) :
    actOn p (M * N) = actOn p M * actOn p N := by
  ext1 X; exact (actOn_actOn p M N X).symm

/-- The identity matrix acts as the identity. -/
@[simp] theorem actOn_one [∀ k, DecidableEq (ι k)] :
    actOn p (1 : Matrix _ _ ℝ) = (1 : Tensor ι →L[ℝ] Tensor ι) := by
  ext1 X; refine unfold_injective p ?_
  rw [unfold_actOn, Matrix.one_mul]; rfl

/-- `actOn p` is additive in the matrix. -/
theorem actOn_add (M N : Matrix (∀ k : Subtype p, ι k) (∀ k : Subtype p, ι k) ℝ) :
    actOn p (M + N) = actOn p M + actOn p N := by
  ext1 X; refine unfold_injective p ?_
  change unfold p (actOn p (M + N) X) = unfold p (actOn p M X + actOn p N X)
  rw [unfold_add, unfold_actOn, unfold_actOn, unfold_actOn, Matrix.add_mul]

/-- `actOn p` commutes with subtraction of matrices. -/
theorem actOn_sub (M N : Matrix (∀ k : Subtype p, ι k) (∀ k : Subtype p, ι k) ℝ) :
    actOn p (M - N) = actOn p M - actOn p N := by
  ext1 X; refine unfold_injective p ?_
  change unfold p (actOn p (M - N) X) = unfold p (actOn p M X - actOn p N X)
  rw [unfold_sub, unfold_actOn, unfold_actOn, unfold_actOn, Matrix.sub_mul]

/-- The zero matrix acts as zero. -/
@[simp] theorem actOn_zero : actOn p (0 : Matrix _ _ ℝ) = (0 : Tensor ι →L[ℝ] Tensor ι) := by
  ext1 X; refine unfold_injective p ?_
  rw [unfold_actOn, Matrix.zero_mul]; rfl

/-- **Maps acting on disjoint sets of modes commute.** -/
theorem actOn_comm_of_disjoint {q : κ → Prop} [DecidablePred q] (hpq : ∀ k, p k → ¬ q k)
    (M : Matrix (∀ k : Subtype p, ι k) (∀ k : Subtype p, ι k) ℝ)
    (N : Matrix (∀ k : Subtype q, ι k) (∀ k : Subtype q, ι k) ℝ) (X : Tensor ι) :
    actOn p M (actOn q N X) = actOn q N (actOn p M X) := by
  have hqp : ∀ k, q k → ¬ p k := fun k hq hp => hpq k hp hq
  ext x
  simp only [actOn_apply, restrict_override_of_disjoint hpq, restrict_override_of_disjoint hqp,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun z _ => ?_
  rw [override_comm_of_disjoint hpq]
  ring

/-- Operator form of `actOn_comm_of_disjoint`. -/
theorem actOn_mul_comm_of_disjoint {q : κ → Prop} [DecidablePred q] (hpq : ∀ k, p k → ¬ q k)
    (M : Matrix (∀ k : Subtype p, ι k) (∀ k : Subtype p, ι k) ℝ)
    (N : Matrix (∀ k : Subtype q, ι k) (∀ k : Subtype q, ι k) ℝ) :
    actOn p M * actOn q N = actOn q N * actOn p M := by
  ext1 X; exact actOn_comm_of_disjoint p hpq M N X

/-- The adjoint of `actOn p M` is `actOn p Mᵀ`. -/
theorem inner_actOn (M : Matrix (∀ k : Subtype p, ι k) (∀ k : Subtype p, ι k) ℝ)
    (X Y : Tensor ι) : ⟪actOn p M X, Y⟫ = ⟪X, actOn p Mᵀ Y⟫ := by
  simp only [inner_eq_sum, actOn_apply, Finset.sum_mul, Finset.mul_sum]
  rw [sum_sum_override p]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => ?_
  simp only [restrict_override, override_override, override_restrict, Matrix.transpose_apply]
  ring

/-- Expansion of a subspace projector:
`(actOn p (U Uᵀ) Z)(x) = ∑_b U(x_p, b) ∑_w U(w, b) Z(x with p-part w)`. -/
theorem actOn_mul_transpose_apply {r : Type*} [Fintype r] (U : Matrix (∀ k : Subtype p, ι k) r ℝ)
    (Z : Tensor ι) (x : ∀ k, ι k) :
    actOn p (U * Uᵀ) Z x = ∑ b, U (Subtype.restrict p x) b * ∑ w, U w b * Z (override p x w) := by
  change ((U * Uᵀ) *ᵥ fun w => Z (override p x w)) (Subtype.restrict p x) =
    (U *ᵥ (Uᵀ *ᵥ fun w => Z (override p x w))) (Subtype.restrict p x)
  rw [Matrix.mulVec_mulVec]

/-- `actOn p M` is an orthogonal projector when `M` is a symmetric idempotent matrix. -/
theorem isOrthProj_actOn {M : Matrix (∀ k : Subtype p, ι k) (∀ k : Subtype p, ι k) ℝ}
    (hidem : M * M = M) (hsymm : Mᵀ = M) : IsOrthProj (actOn p M) where
  idem X := by rw [actOn_actOn, hidem]
  symm X Y := by rw [inner_actOn, hsymm]

/-- `actOn p (U Uᵀ)` is an orthogonal projector when `U` has orthonormal columns. -/
theorem isOrthProj_actOn_mul_transpose {r : Type*} [Fintype r] [DecidableEq r]
    {U : Matrix (∀ k : Subtype p, ι k) r ℝ} (hU : Uᵀ * U = 1) :
    IsOrthProj (actOn p (U * Uᵀ)) :=
  isOrthProj_actOn p (by rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul])
    (by rw [Matrix.transpose_mul, Matrix.transpose_transpose])

/-- **Range of a subspace projector.** For `U` with orthonormal columns, `actOn p (U Uᵀ)` fixes
`X` iff the columns of the `p`-unfolding of `X` lie in the column space of `U`. -/
theorem actOn_mul_transpose_eq_self_iff {r : Type*} [Fintype r] [DecidableEq r]
    {U : Matrix (∀ k : Subtype p, ι k) r ℝ} (hU : Uᵀ * U = 1) (X : Tensor ι) :
    actOn p (U * Uᵀ) X = X ↔ ∃ W : Matrix r (∀ k : {k // ¬ p k}, ι k) ℝ, unfold p X = U * W := by
  constructor
  · intro h
    refine ⟨Uᵀ * unfold p X, ?_⟩
    rw [← Matrix.mul_assoc, ← unfold_actOn, h]
  · rintro ⟨W, hW⟩
    refine unfold_injective p ?_
    rw [unfold_actOn, hW, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul]

/-- **Pointwise range criterion.** If `X(x) = ∑ₐ U(x_p, a) g(a, x)` with `g(a, ·)` independent of
the `p`-part of the multi-index and `Uᵀ U = 1`, then `actOn p (U Uᵀ) X = X`. This is the form in
which nested bases (`X_{≤k+1} = (X_{≤k} ⊗ I) C^{<l>}`) are handled. -/
theorem actOn_mul_transpose_apply_eq_self_of {r : Type*} [Fintype r] [DecidableEq r]
    {U : Matrix (∀ k : Subtype p, ι k) r ℝ} (hU : Uᵀ * U = 1) {X : Tensor ι}
    (g : r → (∀ k, ι k) → ℝ) (hg : ∀ a x z, g a (override p x z) = g a x)
    (hX : ∀ x, X x = ∑ a, U (Subtype.restrict p x) a * g a x) :
    actOn p (U * Uᵀ) X = X := by
  ext x
  calc actOn p (U * Uᵀ) X x
      = ((U * Uᵀ) *ᵥ (U *ᵥ fun a => g a x)) (Subtype.restrict p x) := by
        simp only [actOn_apply, hX, restrict_override, hg, Matrix.mulVec, dotProduct]
    _ = (U *ᵥ fun a => g a x) (Subtype.restrict p x) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hU, Matrix.mul_one]
    _ = X x := by simp only [hX, Matrix.mulVec, dotProduct]

/-- On the empty set of modes, `actOn p M` is multiplication by the single entry of `M`. -/
theorem actOn_of_forall_not (hp : ∀ k, ¬ p k)
    (M : Matrix (∀ k : Subtype p, ι k) (∀ k : Subtype p, ι k) ℝ)
    (z₀ : ∀ k : Subtype p, ι k) : actOn p M = M z₀ z₀ • (1 : Tensor ι →L[ℝ] Tensor ι) := by
  have hz : ∀ z : ∀ k : Subtype p, ι k, z = z₀ := fun z => funext fun k => (hp k.1 k.2).elim
  ext1 X; ext x
  have hx : ∀ z, override p x z = x := fun z => funext fun k => by
    simp [override, hp k]
  simp only [actOn_apply, hx]
  rw [Fintype.sum_eq_single z₀ fun z hz' => (hz' (hz z)).elim, hz (Subtype.restrict p x)]
  simp

end ActOn

/-! ### Mode-wise action and mode projectors -/

section Mode

omit [Fintype κ] [∀ k, Fintype (ι k)] in
/-- Overriding the single mode `k` is `Function.update`. -/
lemma override_eq_update (k : κ) (x : ∀ j, ι j) (z : ∀ j : {j // j = k}, ι j) :
    override (· = k) x z = Function.update x k (modeEquiv k z) := by
  funext j
  by_cases h : j = k
  · subst h; simp [override, modeEquiv]
  · simp [override, h]

/-- `(X ×ₖ A)(x) = ∑_c A(xₖ, c) X(x with xₖ replaced by c)`. -/
theorem modeAct_apply (k : κ) (A : Matrix (ι k) (ι k) ℝ) (X : Tensor ι) (x : ∀ j, ι j) :
    modeAct k A X x = ∑ c, A (x k) c * X (Function.update x k c) := by
  simp only [modeAct, actOn_apply, Matrix.submatrix_apply, override_eq_update]
  exact Finset.sum_equiv (modeEquiv k) (fun _ => by simp) fun z _ => rfl

/-- `(X ×ₖ B) ×ₖ A = X ×ₖ (A B)`. -/
theorem modeAct_modeAct (k : κ) (A B : Matrix (ι k) (ι k) ℝ) (X : Tensor ι) :
    modeAct k A (modeAct k B X) = modeAct k (A * B) X := by
  ext x
  simp only [modeAct_apply, Function.update_self, Function.update_idem, Matrix.mul_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun c _ => ?_
  ring

/-- `modeAct k` is multiplicative. -/
theorem modeAct_mul (k : κ) (A B : Matrix (ι k) (ι k) ℝ) :
    modeAct k (A * B) = modeAct k A * modeAct (ι := ι) k B := by
  ext1 X; exact (modeAct_modeAct k A B X).symm

/-- `X ×ₖ 1 = X`. -/
@[simp] theorem modeAct_one [∀ k, DecidableEq (ι k)] (k : κ) :
    modeAct k (1 : Matrix (ι k) (ι k) ℝ) = (1 : Tensor ι →L[ℝ] Tensor ι) := by
  ext1 X; ext x
  simp [modeAct_apply, Matrix.one_apply]

/-- Maps acting on different modes commute. -/
theorem modeAct_comm {k l : κ} (hkl : k ≠ l) (A : Matrix (ι k) (ι k) ℝ)
    (B : Matrix (ι l) (ι l) ℝ) (X : Tensor ι) :
    modeAct k A (modeAct l B X) = modeAct l B (modeAct k A X) :=
  actOn_comm_of_disjoint _ (fun _ hj hj' => hkl (hj.symm.trans hj')) _ _ X

/-- The adjoint of `X ↦ X ×ₖ A` is `X ↦ X ×ₖ Aᵀ`. -/
theorem inner_modeAct (k : κ) (A : Matrix (ι k) (ι k) ℝ) (X Y : Tensor ι) :
    ⟪modeAct k A X, Y⟫ = ⟪X, modeAct k Aᵀ Y⟫ := by
  rw [modeAct, inner_actOn, Matrix.transpose_submatrix]; rfl

/-- The mode-`k` projector of a basis with orthonormal columns is an orthogonal projector. -/
theorem isOrthProj_modeProj {r : Type*} [Fintype r] [DecidableEq r] (k : κ)
    {U : Matrix (ι k) r ℝ} (hU : Uᵀ * U = 1) : IsOrthProj (modeProj (ι := ι) k U) where
  idem X := by
    rw [modeProj, modeAct_modeAct, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul]
  symm X Y := by
    rw [modeProj, inner_modeAct, Matrix.transpose_mul, Matrix.transpose_transpose]

/-- Mode projectors of different modes commute. -/
theorem modeProj_comm {k l : κ} (hkl : k ≠ l) {r s : Type*} [Fintype r] [Fintype s]
    (U : Matrix (ι k) r ℝ) (V : Matrix (ι l) s ℝ) (X : Tensor ι) :
    modeProj k U (modeProj l V X) = modeProj l V (modeProj k U X) :=
  modeAct_comm hkl _ _ X

end Mode

/-! ### Tucker tensors -/

section Tucker

variable {ρ : κ → Type*} [∀ k, Fintype (ρ k)]

omit [∀ k, Fintype (ι k)] in
/-- The entries of a Tucker tensor. -/
@[simp] lemma tucker_apply (C : Tensor ρ) (U : ∀ k, Matrix (ι k) (ρ k) ℝ) (x : ∀ k, ι k) :
    tucker C U x = ∑ y, (∏ k, U k (x k) (y k)) * C y := rfl

/-- **Tucker isometry.** If all basis matrices have orthonormal columns, then
`⟪C ×ₖ Uₖ, D ×ₖ Uₖ⟫ = ⟪C, D⟫`. -/
theorem inner_tucker [∀ k, DecidableEq (ρ k)] {U : ∀ k, Matrix (ι k) (ρ k) ℝ}
    (hU : ∀ k, (U k)ᵀ * U k = 1) (C D : Tensor ρ) : ⟪tucker C U, tucker D U⟫ = ⟪C, D⟫ := by
  have hU' : ∀ k (a b : ρ k), ∑ c, U k c a * U k c b = if a = b then 1 else 0 := fun k a b => by
    have := congrFun (congrFun (hU k) a) b
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have hprod : ∀ y y' : ∀ k, ρ k, ∑ x : ∀ k, ι k, (∏ k, U k (x k) (y k)) * ∏ k, U k (x k) (y' k)
      = if y = y' then 1 else 0 := fun y y' => by
    simp_rw [← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum (fun k c => U k c (y k) * U k c (y' k))]
    simp_rw [hU']
    by_cases h : y = y'
    · subst h; simp
    · obtain ⟨k, hk⟩ := Function.ne_iff.mp h
      rw [ite_eq_right_iff.mpr (fun h' => (h h').elim)]
      exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])
  calc ⟪tucker C U, tucker D U⟫
      = ∑ x : ∀ k, ι k, (∑ y, (∏ k, U k (x k) (y k)) * C y) *
          ∑ y', (∏ k, U k (x k) (y' k)) * D y' := inner_eq_sum _ _
    _ = ∑ x : ∀ k, ι k, ∑ y, ∑ y', ((∏ k, U k (x k) (y k)) * ∏ k, U k (x k) (y' k)) *
          (C y * D y') := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => ?_
        ring
    _ = ∑ y, ∑ y', (∑ x : ∀ k, ι k, (∏ k, U k (x k) (y k)) * ∏ k, U k (x k) (y' k)) *
          (C y * D y') := by
        conv_lhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => ?_
        conv_lhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y' _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ y, C y * D y := by
        simp only [hprod, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
          ite_true]
    _ = ⟪C, D⟫ := (inner_eq_sum C D).symm

/-- **Tucker isometry**, norm form: `‖C ×ₖ Uₖ‖ = ‖C‖` for orthonormal basis matrices. -/
theorem norm_tucker [∀ k, DecidableEq (ρ k)] {U : ∀ k, Matrix (ι k) (ρ k) ℝ}
    (hU : ∀ k, (U k)ᵀ * U k = 1) (C : Tensor ρ) : ‖tucker C U‖ = ‖C‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner (F := Tensor ρ), inner_tucker hU]

/-- A Tucker tensor is fixed by the mode projector of each of its orthonormal bases. -/
theorem modeProj_tucker [∀ k, DecidableEq (ρ k)] {U : ∀ k, Matrix (ι k) (ρ k) ℝ} (k : κ)
    (hU : (U k)ᵀ * U k = 1) (C : Tensor ρ) : modeProj k (U k) (tucker C U) = tucker C U := by
  have hU' : ∀ a b : ρ k, ∑ c, U k c a * U k c b = if a = b then 1 else 0 := fun a b => by
    have := congrFun (congrFun hU a) b
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have hsplit : ∀ (x : ∀ j, ι j) (y : ∀ j, ρ j), ∏ j, U j (x j) (y j) =
      U k (x k) (y k) * ∏ j ∈ Finset.univ.erase k, U j (x j) (y j) := fun x y =>
    (Finset.mul_prod_erase _ _ (Finset.mem_univ k)).symm
  have hupd : ∀ (x : ∀ j, ι j) (c : ι k) (y : ∀ j, ρ j),
      ∏ j ∈ Finset.univ.erase k, U j (Function.update x k c j) (y j) =
        ∏ j ∈ Finset.univ.erase k, U j (x j) (y j) := fun x c y =>
    Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  ext x
  simp only [modeProj, modeAct_apply, tucker_apply, hsplit, Function.update_self, hupd]
  set R : (∀ j, ρ j) → ℝ := fun y => (∏ j ∈ Finset.univ.erase k, U j (x j) (y j)) * C y
  calc ∑ c, (U k * (U k)ᵀ) (x k) c *
        ∑ y, U k c (y k) * (∏ j ∈ Finset.univ.erase k, U j (x j) (y j)) * C y
      = ∑ y, (∑ a, U k (x k) a * ∑ c, U k c a * U k c (y k)) * R y := by
        simp only [R, Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
        ring
    _ = ∑ y, U k (x k) (y k) * (∏ j ∈ Finset.univ.erase k, U j (x j) (y j)) * C y := by
        simp only [hU', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
          R, mul_assoc]

end Tucker

end LeanDLRA.Tensor
