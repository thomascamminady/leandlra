import Mathlib
import LeanDLRA.Foundations.ODE
import LeanDLRA.Foundations.Projector
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.KStep
import LeanDLRA.Integrators.TuckerBUG

/-!
# Results of arXiv 1906.01369: (anti-)symmetric Tucker integrator, robust error bound

Ceruti–Lubich, *Time integration of symmetric and anti-symmetric low-rank matrices and Tucker
tensors*.  This module formalizes Lemmas 3–4 and Theorem 6 (robust error bound of the
one-basis integrator for (anti-)symmetric Tucker tensors) on **concrete order-`d` tensors**
`Ten d n = EuclideanSpace ℝ (Fin d → Fin n)` with the Frobenius inner product (real entries; the
paper's tensors are complex).

* `modeMul i M` is the mode product `A ×ᵢ M`; `sigma i` is the mode transposition `(0 i)`;
  `symSpace κ` is the space of tensors with `σᵢ A = κ A` (`κ = 1`: symmetric, `κ = -1`:
  anti-symmetric).  That `modeMul i P = σᵢ (modeMul 0 P) σᵢ`, that the mode projectors are
  commuting orthogonal projectors, and that `tuckerProj P = ∏ᵢ modeMul i P` commutes with `σᵢ`
  are all proved, not assumed.
* `norm_sub_modeMul_symm` (the symmetry step in the proof of Lemma 3): the projection error of an
  (anti-)symmetric tensor is the same in every mode.
* `symmetric_capture` (the per-mode bound in the proof of Lemma 3,
  `‖A₁ ×ᵢ U₁U₁ᵀ − A₁‖ ≤ ϑ` for every `i`) and `symmetric_tucker_local_error` (Lemma 4, the local
  error; Lemma 3 itself, `‖A₁ − Π A₁‖ ≤ d ϑ`, is a step of its proof): only the mode-`0` K-step is
  performed; the capture property transfers to all modes by symmetry.  The normal-component
  hypothesis is a pointwise doubly-normal bound at the K-step endpoint, not the paper's
  condition 2 (a bound on `(I − P(Y)) F(t, Y)` near `A(t)`); the implication between them is not
  formalized.
* `symmetric_tucker_global_error` (Theorem 6): `‖Yₙ - A(tₙ)‖ ≤ c₀δ + c₁ε + c₂h`.  Symmetry of the
  iterates and of the exact local flows is *derived* (`ode_mem_of_invariant`: an ODE whose field
  maps a subspace into itself preserves it), not assumed.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P1906_01369



/-- Order-`d` real tensors with mode sizes `n`, with the Euclidean (Frobenius) inner product. -/
abbrev Ten (d n : ℕ) := EuclideanSpace ℝ (Fin d → Fin n)

variable {d n : ℕ}

/-- Mode-`i` multiplication `A ↦ A ×ᵢ M` as a linear map. -/
def modeLin (i : Fin d) (M : Matrix (Fin n) (Fin n) ℝ) : Ten d n →ₗ[ℝ] Ten d n where
  toFun A := WithLp.toLp 2 (fun idx => ∑ k, M (idx i) k * A.ofLp (Function.update idx i k))
  map_add' A B := by
    ext idx; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c A := by
    ext idx
    simp only [PiLp.smul_apply, smul_eq_mul, Real.ringHom_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

/-- Mode-`i` multiplication `A ↦ A ×ᵢ M` as a continuous linear map. -/
noncomputable def modeMul (i : Fin d) (M : Matrix (Fin n) (Fin n) ℝ) : Ten d n →L[ℝ] Ten d n :=
  LinearMap.toContinuousLinearMap (modeLin i M)

lemma modeMul_apply (i : Fin d) (M : Matrix (Fin n) (Fin n) ℝ) (A : Ten d n) (idx : Fin d → Fin n) :
    (modeMul i M A).ofLp idx = ∑ k, M (idx i) k * A.ofLp (Function.update idx i k) := rfl

/-- Transposition of modes `a` and `b`. -/
def modePerm (τ : Equiv.Perm (Fin d)) : Ten d n →ₗ[ℝ] Ten d n where
  toFun A := WithLp.toLp 2 (fun idx => A.ofLp (idx ∘ τ))
  map_add' A B := by ext idx; simp
  map_smul' c A := by ext idx; simp

lemma modePerm_apply (τ : Equiv.Perm (Fin d)) (A : Ten d n) (idx : Fin d → Fin n) :
    (modePerm τ A).ofLp idx = A.ofLp (idx ∘ τ) := rfl

lemma modePerm_modePerm (τ : Equiv.Perm (Fin d)) (hτ : τ * τ = 1) (A : Ten d n) :
    modePerm τ (modePerm τ A) = A := by
  ext idx
  simp only [modePerm_apply]
  have : (idx ∘ ⇑τ) ∘ ⇑τ = idx := by
    funext m
    have := congrArg (fun p : Equiv.Perm (Fin d) => p m) hτ
    simpa using congrArg idx this
  rw [this]

lemma norm_modePerm (τ : Equiv.Perm (Fin d)) (A : Ten d n) : ‖modePerm τ A‖ = ‖A‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp only [modePerm_apply]
  refine Fintype.sum_equiv (Equiv.arrowCongr τ.symm (Equiv.refl _)) _ _ (fun idx => ?_)
  have : (Equiv.arrowCongr τ.symm (Equiv.refl (Fin n))) idx = idx ∘ τ := by
    funext m; simp [Equiv.arrowCongr]
  rw [this]


lemma modeMul_mul (i : Fin d) (M N : Matrix (Fin n) (Fin n) ℝ) (A : Ten d n) :
    modeMul i M (modeMul i N A) = modeMul i (M * N) A := by
  ext idx
  simp only [modeMul_apply, Function.update_idem, Function.update_self, Matrix.mul_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

lemma modeMul_comm {i j : Fin d} (hij : i ≠ j) (M N : Matrix (Fin n) (Fin n) ℝ) (A : Ten d n) :
    modeMul i M (modeMul j N A) = modeMul j N (modeMul i M A) := by
  ext idx
  simp only [modeMul_apply, Function.update_of_ne hij,
    Function.update_of_ne hij.symm, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Function.update_comm hij]
  ring

lemma modeMul_inner (i : Fin d) (M : Matrix (Fin n) (Fin n) ℝ) (x y : Ten d n) :
    ⟪modeMul i M x, y⟫ = ⟪x, modeMul i M.transpose y⟫ := by
  simp only [PiLp.inner_apply, modeMul_apply, RCLike.inner_apply, conj_trivial]
  simp only [Finset.mul_sum, Finset.sum_mul, Matrix.transpose_apply]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  let e : (Fin d → Fin n) × Fin n ≃ (Fin d → Fin n) × Fin n :=
    { toFun := fun p => (Function.update p.1 i p.2, p.1 i)
      invFun := fun p => (Function.update p.1 i p.2, p.1 i)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  refine Fintype.sum_equiv e _ _ (fun p => ?_)
  simp only [e, Equiv.coe_fn_mk, Function.update_self, Function.update_idem,
    Function.update_eq_self]
  ring



/-- Helper (used for symmetry of the iterates, arXiv 1906.01369 Thm 6): a solution of a Lipschitz
ODE that starts in a linear subspace `V` stays in `V` if the field maps `V` into `V`. -/
theorem ode_mem_of_invariant {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {G : ℝ → E → E} {L : ℝ} (hG : IsLipschitzField G L)
    {y : ℝ → E} {a b : ℝ} (hy : ODESolution G y a b) (V : Submodule ℝ E)
    (hV : ∀ t, ∀ x ∈ V, G t x ∈ V) (h0 : y a ∈ V) : ∀ t ∈ Icc a b, y t ∈ V := by
  let π : E →L[ℝ] E := V.starProjection
  have hπmem : ∀ x, π x ∈ V := fun x => Submodule.starProjection_apply_mem V x
  have hπfix : ∀ x ∈ V, π x = x := fun x hx => Submodule.starProjection_eq_self_iff.2 hx
  have hπnorm : ∀ x, ‖x - π x‖ ≤ ‖x‖ := fun x => by
    have hperp : x - π x ∈ Vᗮ := Submodule.sub_starProjection_mem_orthogonal x
    have hi : inner ℝ (π x) (x - π x) = 0 := by
      rw [real_inner_comm]; exact (Submodule.mem_orthogonal' V _).1 hperp _ (hπmem x)
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (π x) (x - π x) hi
    rw [add_sub_cancel] at h
    nlinarith [norm_nonneg (x - π x), norm_nonneg x, sq_nonneg ‖π x‖]
  set g : ℝ → E := fun t => y t - π (y t) with hg
  have hgc : ContinuousOn g (Icc a b) := hy.cont.sub (π.continuous.comp_continuousOn hy.cont)
  have hgd : ∀ t ∈ Ico a b, HasDerivWithinAt g (G t (y t) - π (G t (y t))) (Ici t) t :=
    fun t ht => (hy.deriv t ht).sub (π.hasFDerivAt.comp_hasDerivWithinAt t (hy.deriv t ht))
  have hbd : ∀ t ∈ Ico a b, ‖G t (y t) - π (G t (y t))‖ ≤ L * ‖g t‖ + 0 := by
    intro t ht
    have h1 : G t (y t) - π (G t (y t)) = (G t (y t) - G t (π (y t))) -
        π (G t (y t) - G t (π (y t))) := by
      rw [map_sub, hπfix _ (hV t _ (hπmem (y t)))]; abel
    rw [h1, add_zero]
    exact (hπnorm _).trans (hG t _ _)
  have := norm_le_gronwallBound_of_norm_deriv_right_le hgc hgd (δ := 0) (K := L) (ε := 0)
    (by simp [hg, hπfix _ h0]) hbd
  intro t ht
  have h2 := this t ht
  rw [gronwallBound_ε0_δ0] at h2
  have h3 : y t - π (y t) = 0 := norm_le_zero_iff.1 h2
  have : y t = π (y t) := sub_eq_zero.1 h3
  rw [this]; exact hπmem _


lemma modePerm_modeMul (τ : Equiv.Perm (Fin d)) (hτ : τ * τ = 1) (i : Fin d)
    (M : Matrix (Fin n) (Fin n) ℝ) (A : Ten d n) :
    modePerm τ (modeMul i M (modePerm τ A)) = modeMul (τ i) M A := by
  have hττ : ∀ m, τ (τ m) = m := fun m => by
    simpa using congrArg (fun p : Equiv.Perm (Fin d) => p m) hτ
  ext idx
  simp only [modePerm_apply, modeMul_apply, Function.comp_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  have key : Function.update (idx ∘ τ) i k ∘ τ = Function.update idx (τ i) k := by
    funext m
    by_cases h : τ m = i
    · have : m = τ i := by rw [← h, hττ]
      subst this
      simp [h]
    · have hm : m ≠ τ i := fun hm => h (by rw [hm, hττ])
      simp [Function.update_of_ne h, Function.update_of_ne hm, hττ]
  rw [key]

lemma isOrthProj_modeMul (i : Fin d) {P : Matrix (Fin n) (Fin n) ℝ} (hs : P.transpose = P)
    (hi : P * P = P) : IsOrthProj (modeMul i P) where
  idem x := by rw [modeMul_mul, hi]
  symm x y := by rw [modeMul_inner, hs]

lemma modeMul_commute {i j : Fin d} (hij : i ≠ j) (M N : Matrix (Fin n) (Fin n) ℝ) :
    Commute (modeMul i M) (modeMul j N) :=
  ContinuousLinearMap.ext fun A => modeMul_comm hij M N A


section Symmetric

variable [NeZero d]

/-- The mode transposition `σᵢ` exchanging modes `0` and `i`, as a continuous linear map. -/
noncomputable def sigma (i : Fin d) : Ten d n →L[ℝ] Ten d n :=
  LinearMap.toContinuousLinearMap (modePerm (Equiv.swap 0 i))

lemma sigma_apply (i : Fin d) (A : Ten d n) : sigma i A = modePerm (Equiv.swap 0 i) A := rfl

lemma sigma_sigma (i : Fin d) (A : Ten d n) : sigma i (sigma i A) = A :=
  modePerm_modePerm _ (Equiv.swap_mul_self _ _) A

lemma norm_sigma (i : Fin d) (A : Ten d n) : ‖sigma i A‖ = ‖A‖ := norm_modePerm _ _

lemma sigma_modeMul_zero (i : Fin d) (M : Matrix (Fin n) (Fin n) ℝ) (A : Ten d n) :
    sigma i (modeMul 0 M (sigma i A)) = modeMul i M A := by
  rw [sigma_apply, sigma_apply]
  simpa using modePerm_modeMul (Equiv.swap (0 : Fin d) i) (Equiv.swap_mul_self _ _) 0 M A

/-- The Tucker projector `Π_P : A ↦ A ×₁ P ×₂ P ⋯ ×_d P` (product of the mode projectors). -/
noncomputable def tuckerProj (P : Matrix (Fin n) (Fin n) ℝ) : Ten d n →L[ℝ] Ten d n :=
  modeProd (fun i : Fin d => modeMul i P)

omit [NeZero d] in
lemma modeMul_comm' {P : Matrix (Fin n) (Fin n) ℝ} (i j : Fin d) (x : Ten d n) :
    modeMul i P (modeMul j P x) = modeMul j P (modeMul i P x) := by
  by_cases hij : i = j
  · subst hij; rfl
  · exact modeMul_comm hij P P x

omit [NeZero d] in
lemma isOrthProj_tuckerProj {P : Matrix (Fin n) (Fin n) ℝ} (hs : P.transpose = P)
    (hi : P * P = P) : IsOrthProj (tuckerProj (d := d) P) :=
  IsOrthProj.modeProd (fun i => isOrthProj_modeMul i hs hi) modeMul_comm'

lemma conj_list_prod {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] (s : E' →L[ℝ] E')
    (hs : ∀ x, s (s x) = x) (l : List (E' →L[ℝ] E')) :
    s * l.prod * s = (l.map fun a => s * a * s).prod := by
  induction l with
  | nil => ext x; simp [hs]
  | cons a l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons, ← ih]
    ext x; simp [hs]

lemma sigma_tuckerProj_sigma (j : Fin d) (P : Matrix (Fin n) (Fin n) ℝ) (x : Ten d n) :
    sigma j (tuckerProj P (sigma j x)) = tuckerProj P x := by
  have hτ : Equiv.swap (0 : Fin d) j * Equiv.swap 0 j = 1 := Equiv.swap_mul_self _ _
  have h := conj_list_prod (sigma j) (sigma_sigma j) (List.ofFn fun i : Fin d => modeMul i P)
  rw [List.map_ofFn] at h
  have hf : ((fun a => sigma j * a * sigma j) ∘ fun i : Fin d => modeMul i P) =
      (fun i : Fin d => modeMul i P) ∘ ⇑(Equiv.swap (0 : Fin d) j) := by
    funext i
    refine ContinuousLinearMap.ext fun A => ?_
    exact modePerm_modeMul (Equiv.swap (0 : Fin d) j) hτ i P A
  rw [hf] at h
  have hpair : (List.ofFn ((fun i : Fin d => modeMul i P) ∘ ⇑(Equiv.swap (0 : Fin d) j))).Pairwise
      Commute := by
    rw [List.pairwise_ofFn]
    intro a b hab
    exact modeMul_commute (fun h => hab.ne (Equiv.injective _ h)) P P
  have h2 := (Equiv.Perm.ofFn_comp_perm (Equiv.swap (0 : Fin d) j)
    (fun i : Fin d => modeMul i P)).prod_eq' hpair
  have h3 : sigma j * tuckerProj P * sigma j = tuckerProj P := by
    unfold tuckerProj modeProd; rw [h, h2]
  simpa using congrArg (fun T => T x) h3

lemma sigma_tuckerProj (j : Fin d) (P : Matrix (Fin n) (Fin n) ℝ) (x : Ten d n) :
    sigma j (tuckerProj P x) = tuckerProj P (sigma j x) := by
  simpa [sigma_sigma] using sigma_tuckerProj_sigma j P (sigma j x)

/-- The subspace of `κ`-(anti)symmetric tensors: `σᵢ A = κ A` for every transposition `(0 i)`,
`i ≠ 0`.  `κ = 1` is the symmetric and `κ = -1` the anti-symmetric case (the transpositions
`(0 i)` generate the symmetric group, and the sign character is multiplicative). -/
def symSpace (κ : ℝ) : Submodule ℝ (Ten d n) where
  carrier := {A | ∀ i : Fin d, i ≠ 0 → sigma i A = κ • A}
  add_mem' := fun {a b} ha hb i hi => by simp [ha i hi, hb i hi]
  zero_mem' := fun i _ => by simp
  smul_mem' := fun c A hA i hi => by
    have h := hA i hi
    simp only [map_smul, h, smul_comm c κ A]

lemma mem_symSpace {κ : ℝ} {A : Ten d n} : A ∈ symSpace (d := d) (n := n) κ ↔
    ∀ i : Fin d, i ≠ 0 → sigma i A = κ • A := Iff.rfl

lemma tuckerProj_mem_symSpace {κ : ℝ} (P : Matrix (Fin n) (Fin n) ℝ) {A : Ten d n}
    (hA : A ∈ symSpace (d := d) (n := n) κ) : tuckerProj P A ∈ symSpace (d := d) (n := n) κ :=
  fun i hi => by rw [sigma_tuckerProj, hA i hi, map_smul]

end Symmetric


section Main

variable [NeZero d]

/-- **The symmetry step in the proof of Lemma 3 of arXiv 1906.01369**: for a (anti-)symmetric
tensor `A` (`σᵢ A = κ A`, `κ = ±1`, for all `i ≠ 0`) and any matrix `M`, the mode-`i` projection
error equals the mode-`0` one: `‖A - A ×ᵢ M‖ = ‖A - A ×₀ M‖` (the paper's
`‖U₁U₁* Mat₁(A₁) − Mat₁(A₁)‖ = ‖U₁U₁* Matᵢ(A₁) − Matᵢ(A₁)‖`).  Proved from the explicit identity
`modeMul i M = σᵢ (modeMul 0 M) σᵢ` (`sigma_modeMul_zero`).  Modes are indexed `0, …, d-1`
(paper: `1, …, d`).  No assumption on `M`.  The bound of Lemma 3 itself is assembled in the proof
of `symmetric_tucker_local_error`. -/
theorem norm_sub_modeMul_symm {κ : ℝ} (hκ : κ = 1 ∨ κ = -1) {A : Ten d n}
    (hA : A ∈ symSpace (d := d) (n := n) κ) (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin d) :
    ‖A - modeMul i M A‖ = ‖A - modeMul 0 M A‖ := by
  by_cases hi : i = 0
  · subst hi; rfl
  have hκ2 : ‖κ‖ = 1 := by rcases hκ with rfl | rfl <;> simp
  have hσ : sigma i A = κ • A := hA i hi
  have hA' : A = κ • sigma i A := by
    have := sigma_sigma i A
    rw [hσ, map_smul, hσ, smul_smul] at this
    have hk : κ * κ = 1 := by rcases hκ with rfl | rfl <;> norm_num
    rw [hk, one_smul] at this
    rw [hσ, smul_smul, hk, one_smul]
  have e1 : modeMul i M A = κ • sigma i (modeMul 0 M A) := by
    rw [← sigma_modeMul_zero, hσ, map_smul, map_smul]
  have e2 : A - modeMul i M A = κ • sigma i (A - modeMul 0 M A) := by
    rw [e1, map_sub, smul_sub, ← hA']
  rw [e2, norm_smul, hκ2, one_mul, norm_sigma]

end Main

section Results

variable [NeZero d] {F : ℝ → Ten d n → Ten d n} {L B ε : ℝ}

/-- **Per-mode capture, the step `‖A₁ ×ᵢ U₁U₁* − A₁‖ ≤ ϑ` (`i = 1, …, d`) in the proof of
Lemma 3 of arXiv 1906.01369.**  Let `F` be
`L`-Lipschitz and bounded by `B`, `A` solve `A' = F(t, A)` on `[t₀, t₁]`, `t₁ = t₀ + h`, with
`A t₁` (anti-)symmetric.  Let `YK` be the mode-`0` K-step `YK' = Q F(t, YK)`, `YK t₀ = A t₀`
(`Q` an orthogonal projector: the co-range projector, kept abstract), `P` an orthogonal projector
matrix (the new basis `U₁U₁ᵀ`) capturing `YK t₁` in mode `0`, and the normal-component bound
`‖(1 - P₁)(1 - Q) F(t, YK t₁)‖ ≤ ε`. Then for all modes `i`:
`‖A t₁ - A t₁ ×ᵢ P‖ ≤ h (4 L B h + ε)`.
Differences: the paper obtains `ϑ = c* h (B L h + ε)` from [18, Theorem 5.1] with an unspecified
constant; here the constant is explicit, and the normal-component hypothesis is the library's
pointwise doubly-normal form at the K-step endpoint (as in `kstep_capture`) rather than the
paper's condition 2 on the tangent-space normal component near `A(t)`. -/
theorem symmetric_capture {κ : ℝ} (hκ : κ = 1 ∨ κ = -1) {P : Matrix (Fin n) (Fin n) ℝ}
    (hs : P.transpose = P) (hi : P * P = P) {Q : Ten d n →L[ℝ] Ten d n} (hQ : IsOrthProj Q)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) {t₀ t₁ h : ℝ}
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) {A YK : ℝ → Ten d n} (hA : ODESolution F A t₀ t₁)
    (hAsym : A t₁ ∈ symSpace (d := d) (n := n) κ)
    (hK : ODESolution (fun t x => Q (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = A t₀)
    (hKcap : modeMul 0 P (YK t₁) = YK t₁)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - modeMul 0 P) ((1 - Q) (F t (YK t₁)))‖ ≤ ε) (i : Fin d) :
    ‖A t₁ - modeMul i P (A t₁)‖ ≤ h * (4 * L * B * h + ε) := by
  rw [norm_sub_modeMul_symm hκ hAsym]
  have := kstep_capture hF hL hB (isOrthProj_modeMul 0 hs hi) hQ ht₁ hh hA hK hK₀ hKcap hε
  simpa using this

/-- **Lemma 4 of arXiv 1906.01369: local error of the one-basis (anti-)symmetric Tucker
integrator**, explicit form.  Under the hypotheses of
`symmetric_capture`, if `YS' = Π_P F(t, YS)` with `Π_P = ∏ᵢ (· ×ᵢ P)` and `YS t₀ = Π_P (A t₀)`
is the core step, then with `ϑ = h (4 L B h + ε)`:
`‖YS t₁ - A t₁‖ ≤ (e^{L h} - 1)(B h + d ϑ) + d ϑ`, which is of the paper's form
`ĉ h (B L h + ε)` with `ĉ` depending on `d` and a bound for `L h` (`tucker_bound_le`).  Lemma 3,
`‖A t₁ - Π_P (A t₁)‖ ≤ d ϑ`, is the first step of the proof.  Only the mode-`0` K-step is used. -/
theorem symmetric_tucker_local_error {κ : ℝ} (hκ : κ = 1 ∨ κ = -1)
    {P : Matrix (Fin n) (Fin n) ℝ}
    (hs : P.transpose = P) (hi : P * P = P) {Q : Ten d n →L[ℝ] Ten d n} (hQ : IsOrthProj Q)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) {t₀ t₁ h : ℝ}
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) {A YK YS : ℝ → Ten d n} (hA : ODESolution F A t₀ t₁)
    (hAsym : A t₁ ∈ symSpace (d := d) (n := n) κ)
    (hK : ODESolution (fun t x => Q (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = A t₀)
    (hKcap : modeMul 0 P (YK t₁) = YK t₁)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - modeMul 0 P) ((1 - Q) (F t (YK t₁)))‖ ≤ ε)
    (hS : ODESolution (fun t x => tuckerProj P (F t x)) YS t₀ t₁)
    (hS₀ : YS t₀ = tuckerProj P (A t₀)) :
    ‖YS t₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (B * h + d * (h * (4 * L * B * h + ε)))
      + d * (h * (4 * L * B * h + ε)) := by
  have hcap : ‖A t₁ - tuckerProj P (A t₁)‖ ≤ d * (h * (4 * L * B * h + ε)) := by
    refine (norm_sub_modeProd_apply_le (fun i y => (isOrthProj_modeMul i hs hi).norm_le y)
      (A t₁)).trans ?_
    calc ∑ i : Fin d, ‖A t₁ - modeMul i P (A t₁)‖ ≤ ∑ _i : Fin d, h * (4 * L * B * h + ε) :=
          Finset.sum_le_sum fun i _ =>
            symmetric_capture hκ hs hi hQ hF hL hB ht₁ hh hA hAsym hK hK₀ hKcap hε i
      _ = _ := by simp
  exact galerkin_step_error (isOrthProj_tuckerProj hs hi) hF hL hB ht₁ hh hA hS hS₀ hcap

end Results

section Global

variable [NeZero d] {F : ℝ → Ten d n → Ten d n} {L B ε : ℝ}

/-- **Theorem 6 of arXiv 1906.01369** (label `Theorem 6`): robust global error bound for the
(anti-)symmetric Tucker integrator with a single basis.  Setting: order-`d` tensors, `κ = ±1`;
`F` is `L`-Lipschitz, bounded by `B`, and maps `κ`-symmetric tensors to `κ`-symmetric tensors
(`hFsym`, as in the paper); `Y 0` is `κ`-symmetric.  Step `k < N` (`tₖ = t₀ + k h`) does a
mode-`0` K-step with co-range projector `Q k` and a new basis `P k` (an orthogonal projector
matrix) capturing it, with normal-component bound `ε`, then the Galerkin core step
`YS k' = Π_{P k} F(t, YS k)` started at `Π_{P k} (Y k)`; `Y (k+1) = YS k t_{k+1}`; `Φ k` is the
exact flow from `Y k`.  Then for `n' h ≤ T`, `h ≤ H`, `‖Y 0 - A t₀‖ ≤ δ`:
`‖Y n' - A tₙ'‖ ≤ e^{L T} δ + T e^{L T} c₁ ε + T e^{L T} c₂ h` with the explicit constants
`c₁ = tuckerC₁ d L H`, `c₂ = tuckerC₂ d L B H`, independent of small singular values.
Differences from the paper: real instead of complex tensors; constants are explicit (they also
depend on the step-size bound `H`); `ε` is the doubly-normal bound
`‖(1-P)(1-Q)F‖ ≤ ε` at the K-step endpoint, in place of the paper's condition 2 (a bound on
`(I - P(Y)) F(t, Y)` near `A(t)`; the implication is not formalized); `F` is Lipschitz and
bounded for all `t`; the paper assumes the solution `A` (anti-)symmetric, which is not needed
here; the co-range projector `Q k` is an arbitrary
orthogonal projector (not tied to the matricization); the bases are given as projectors and the
QR factorizations are not modelled; anti-symmetry is encoded as `σᵢ A = -A` for the transpositions
`(0 i)`, which generate all permutations. Symmetry of `Y k`, `YS k` and of the exact flows `Φ k`
is derived from `hFsym` and `hY0` (`ode_mem_of_invariant`). -/
theorem symmetric_tucker_global_error {κ : ℝ} (hκ : κ = 1 ∨ κ = -1)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (hε : 0 ≤ ε)
    (hFsym : ∀ t, ∀ x ∈ symSpace (d := d) (n := n) κ, F t x ∈ symSpace (d := d) (n := n) κ)
    {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ} {A : ℝ → Ten d n}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {P : ℕ → Matrix (Fin n) (Fin n) ℝ}
    (hs : ∀ k, (P k).transpose = P k) (hi : ∀ k, P k * P k = P k)
    {Q : ℕ → Ten d n →L[ℝ] Ten d n} (hQ : ∀ k, IsOrthProj (Q k)) {Y : ℕ → Ten d n}
    {YK YS Φ : ℕ → ℝ → Ten d n} (hY0 : Y 0 ∈ symSpace (d := d) (n := n) κ)
    (hK : ∀ k < N, ODESolution (fun t x => Q k (F t x)) (YK k) (t₀ + k * h) (t₀ + (k + 1) * h))
    (hK₀ : ∀ k < N, YK k (t₀ + k * h) = Y k)
    (hKcap : ∀ k < N, modeMul 0 (P k) (YK k (t₀ + (k + 1) * h)) = YK k (t₀ + (k + 1) * h))
    (hεK : ∀ k < N, ∀ t ∈ Icc (t₀ + k * h) (t₀ + (k + 1) * h),
      ‖(1 - modeMul 0 (P k)) ((1 - Q k) (F t (YK k (t₀ + (k + 1) * h))))‖ ≤ ε)
    (hS : ∀ k < N, ODESolution (fun t x => tuckerProj (P k) (F t x)) (YS k) (t₀ + k * h)
      (t₀ + (k + 1) * h))
    (hS₀ : ∀ k < N, YS k (t₀ + k * h) = tuckerProj (P k) (Y k))
    (hY : ∀ k < N, Y (k + 1) = YS k (t₀ + (k + 1) * h))
    (hΦ : ∀ k < N, ODESolution F (Φ k) (t₀ + k * h) (t₀ + (k + 1) * h))
    (hΦ₀ : ∀ k < N, Φ k (t₀ + k * h) = Y k) {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n' ≤ N, (n' : ℝ) * h ≤ T →
      ‖Y n' - A (t₀ + n' * h)‖ ≤ Real.exp (L * T) * δ
        + T * Real.exp (L * T) * tuckerC₁ d L H * ε
        + T * Real.exp (L * T) * tuckerC₂ d L B H * h := by
  have hH : 0 ≤ H := hh.trans hhH
  -- symmetry of all iterates
  have hYsym : ∀ k ≤ N, Y k ∈ symSpace (d := d) (n := n) κ := by
    intro k
    induction k with
    | zero => intro _; exact hY0
    | succ k ih =>
      intro hk
      have hk' : k < N := hk
      have hYk := ih hk'.le
      have hG : IsLipschitzField (fun t x => tuckerProj (P k) (F t x)) L :=
        hF.comp_contraction _ (isOrthProj_tuckerProj (hs k) (hi k)).norm_le
      have := ode_mem_of_invariant hG (hS k hk') (symSpace (d := d) (n := n) κ)
        (fun t x hx => tuckerProj_mem_symSpace _ (hFsym t x hx))
        (by rw [hS₀ k hk']; exact tuckerProj_mem_symSpace _ hYk)
        (t₀ + (k + 1) * h) ⟨by nlinarith, le_rfl⟩
      rw [hY k hk']; exact this
  have hloc : ∀ k < N, ‖Y (k + 1) - Φ k (t₀ + (k + 1) * h)‖ ≤
      h * (tuckerC₁ d L H * ε + tuckerC₂ d L B H * h) := by
    intro k hk
    have hΦsym := ode_mem_of_invariant hF (hΦ k hk) (symSpace (d := d) (n := n) κ) hFsym
      (by rw [hΦ₀ k hk]; exact hYsym k hk.le) (t₀ + (k + 1) * h) ⟨by nlinarith, le_rfl⟩
    rw [hY k hk]
    refine (symmetric_tucker_local_error hκ (hs k) (hi k) (hQ k) hF hL hB (by ring) hh (hΦ k hk)
      hΦsym (hK k hk) (by rw [hK₀ k hk, hΦ₀ k hk]) (hKcap k hk) (hεK k hk) (hS k hk)
      (by rw [hS₀ k hk, hΦ₀ k hk])).trans ?_
    exact tucker_bound_le hL hB.nonneg (mul_nonneg (Nat.cast_nonneg d) hε) hh hhH
  intro n' hn hT
  have hg : 0 ≤ tuckerC₁ d L H * ε + tuckerC₂ d L B H * h :=
    add_nonneg (mul_nonneg (tuckerC₁_nonneg d hL hH) hε)
      (mul_nonneg (tuckerC₂_nonneg d hL hB.nonneg hH) hh)
  have h1 := lady_windermere_of_le hF hL hh hA hΦ hΦ₀ hg hloc n' hn hT
  have h2 : Real.exp (L * T) * (‖Y 0 - A t₀‖ + T * (tuckerC₁ d L H * ε + tuckerC₂ d L B H * h))
      ≤ Real.exp (L * T) * (δ + T * (tuckerC₁ d L H * ε + tuckerC₂ d L B H * h)) :=
    mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  calc _ ≤ _ := h1.trans h2
    _ = _ := by ring

end Global

section Example

lemma modeMul_one (i : Fin d) (A : Ten d n) : modeMul i (1 : Matrix (Fin n) (Fin n) ℝ) A = A := by
  ext idx
  simp [modeMul_apply, Matrix.one_apply]

lemma tuckerProj_one : tuckerProj (d := d) (n := n) (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  have : (fun i : Fin d => modeMul i (1 : Matrix (Fin n) (Fin n) ℝ)) = fun _ => 1 :=
    funext fun i => ContinuousLinearMap.ext (modeMul_one i)
  unfold tuckerProj modeProd
  rw [this]
  simp

/-- Non-vacuity of the hypotheses of `symmetric_tucker_global_error`: the stationary problem
`F = 0` with exact solution `A ≡ v` for a symmetric tensor `v`, `P = 1`, `Q = 1`, one step of
size `1` (so all hypotheses are satisfied and the theorem applies). -/
example : ∀ n' : ℕ, n' ≤ 1 → (n' : ℝ) * 1 ≤ 1 →
    ‖(fun _ => (WithLp.toLp 2 (fun _ => (1 : ℝ)) : Ten 2 2)) n' -
      (fun _ : ℝ => (WithLp.toLp 2 (fun _ => (1 : ℝ)) : Ten 2 2)) (0 + n' * 1)‖ ≤
      Real.exp (0 * 1) * 0 + 1 * Real.exp (0 * 1) * tuckerC₁ 2 0 1 * 0
        + 1 * Real.exp (0 * 1) * tuckerC₂ 2 0 0 1 * 1 := by
  set v : Ten 2 2 := WithLp.toLp 2 (fun _ => (1 : ℝ)) with hv
  have hvs : v ∈ symSpace (d := 2) (n := 2) (1 : ℝ) := by
    intro i _
    ext idx
    simp [hv, sigma_apply, modePerm_apply]
  have hconst : ∀ (G : ℝ → Ten 2 2 → Ten 2 2) (a b : ℝ), (∀ t x, G t x = 0) →
      ODESolution G (fun _ => v) a b := fun G a b hG =>
    ⟨continuousOn_const, fun t _ => by simpa [hG] using hasDerivWithinAt_const t (Ici t) v⟩
  have h1 : (1 : Matrix (Fin 2) (Fin 2) ℝ).transpose = 1 := Matrix.transpose_one
  have h2 : (1 : Matrix (Fin 2) (Fin 2) ℝ) * 1 = 1 := mul_one _
  have h0 : IsOrthProj (1 : Ten 2 2 →L[ℝ] Ten 2 2) :=
    ⟨fun _ => rfl, fun _ _ => rfl⟩
  refine symmetric_tucker_global_error (d := 2) (n := 2) (κ := 1) (F := fun _ _ => 0) (L := 0)
    (B := 0) (ε := 0) (Or.inl rfl) (fun t x y => by simp) le_rfl (fun t x => by simp) le_rfl
    (fun t x _ => by simp) (t₀ := 0) (h := 1) (H := 1)
    zero_le_one le_rfl (N := 1) (A := fun _ => v) (hconst _ _ _ fun _ _ => rfl)
    (P := fun _ => 1) (fun _ => h1) (fun _ => h2) (Q := fun _ => 1) (fun _ => h0)
    (Y := fun _ => v) (YK := fun _ _ => v) (YS := fun _ _ => v) (Φ := fun _ _ => v) hvs
    (fun k _ => hconst _ _ _ fun _ _ => by simp) (fun _ _ => rfl)
    (fun k _ => by simp [modeMul_one]) (fun k _ t _ => by simp) 
    (fun k _ => hconst _ _ _ fun t x => by simp) (fun k _ => by simp [tuckerProj_one])
    (fun _ _ => rfl) (fun k _ => hconst _ _ _ fun _ _ => rfl) (fun _ _ => rfl)
    (δ := 0) (T := 1) (by simp)

end Example

end LeanDLRA.Literature.P1906_01369
