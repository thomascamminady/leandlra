import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.Matrix.ProjectorSplitting
import LeanDLRA.Integrators.RankAdaptiveBUG
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2112.02695: Adaptive DLRA for the nonlinear Boltzmann equation

Hu and Wang evolve `f = X S Vᵀ` on a phase-space grid by the projector-splitting integrator and
adapt the rank.  This module proves that the K-, S- and L-steps close with `r²` collision
evaluations for every bilinear `Q`, Eqs. (2.11)-(2.13) (`kField_boltzmann`, `sField_boltzmann`,
`lField_boltzmann`, `fields_eq_of_collisionTable_eq`), and that they form a step of the library's
KSL integrator (`isStep_of_closure`); the exact boundary augmentation of Sec. 3.1 (`eq3_2`,
`augmentation_exact`, `augmentation_span`, `augmentation_projectors`, `boundary_capture`,
`exists_block_qr`); the rank dropping of Sec. 3.2 with Eqs. (5.6)-(5.7) (`exists_keep`,
`droppedBases_orthonormal`, `norm_droppedState_sub_le`, `eq5_6`, `eq5_7`, `eq5_7_satisfiable`); the
factored residual Eqs. (5.3)-(5.5) with its cost (`eq5_3`, `eq5_4`, `factoredResidualCost_le`); and
the Mott-Smith profile of Sec. 4.2 for the genuine collision operator (1.2) and genuine Maxwellians
on `ℝ^d`, where `Q(M, M) = 0` and the moments are derived, not assumed (`collisionQ_maxwellian`,
`integral_cube_maxwellian`, `eq4_19`, `flux_difference`, `eq4_21`, `mottSmith_profile`,
`hasDerivAt_logistic`, `logistic_unique`, `eq4_6`, `isRankineHugoniot_of_mach`, `eq4_23`,
`massFlux_constraint`, `ansatz_tendsto`, `integrable_collisionIntegrand`, `mottSmith_satisfiable`).

**False claim.**  Eq. (5.7) (p. 15) has no side condition in the paper, but its upper bound needs
`c √(r - r') < 1`: with the paper's `c = 0.2` its right-hand side is negative for `r - r' > 25`
and undefined for `r - r' = 25`.  `eq5_7_needs_condition` gives data (with `r' = 0`) on which the
bound fails as soon as `c √r > 1`.  `eq5_7` proves it under this condition.

**Differences from the paper.**  Secs. 2, 3 and 5 are stated on the fully discrete grid of its
Sec. 2.4, with `D ℓ` any matrix for `∂_{x_ℓ}` and `Q` any bilinear map acting cell by cell in `x`
(the header's "v-local" is meant in this sense).  Quadrature weights are one: the paper's uniform
midpoint weights `h_x`, `h_v` are the case of `√h_x X`, `√h_v V`, `√(h_x h_v) f` and
`Q / √(h_x h_v)`.  `drop_tol = c err_ada` is an implicit equation, since `err_ada` depends on
`drop_tol`; `eq5_7` takes the weaker `drop_tol ≤ c err_ada`, and `eq5_7_satisfiable` solves the
equality.  QR factorizations are used only as `A = Q T`, `Qᵀ Q = 1`.  The cutoff `10⁻¹⁰` of
Sec. 3.1 is a parameter `tol`; the boundary profiles lie in the new basis up to that cutoff, and
exactly if the discarded singular values vanish (`boundary_capture`), which is the header's claim.
In Sec. 4.2 the collision integral is taken over the product `ℝ^d × S^{d-1}`, it is assumed to
converge for `Q(f_L, f_R)` and `Q(f_R, f_L)`, and this is proved for bounded kernels; the moment
equation (4.18) is the hypothesis, not the Boltzmann equation itself, which the ansatz need not
solve.
`a(x₀) = 1/2` fixes the translation, which the paper leaves implicit.

**Not formalized.**  The forward Euler scheme (2.24)-(2.26) and the boundary formula (2.20) for
`K`, the costs of Sec. 2.4, and the claim that the ansatz approximates a strong shock, which is
heuristic in the paper.  The weak-shock expansion (4.7)-(4.16) is outside this slice.  The sign of
`α` needed for `β > 0` in `ansatz_tendsto` depends on the kernel and is a hypothesis.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2112_02695

/-! ### Eqs. (2.11)-(2.13): the substeps close with `r²` collision evaluations -/

section Closure

variable {m n k e : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype e]

/-- The right-hand side of the discrete Boltzmann equation on a phase-space grid, with `f a b` the
value at the space point `a` and the velocity point `b`:
`(RHS f) a b = - ∑ ℓ, v_ℓ(b) (∂_ℓ f)(a, b) + Q(f a, f a)(b)`.
Here `D ℓ` is any matrix discretizing `∂_{x_ℓ}`, `w ℓ b` is the component `ℓ` of the velocity
point `b`, and `Q` is any bilinear map on velocity vectors.  Collisions act cell by cell in `x`. -/
def boltzmannRHS (D : e → Matrix m m ℝ) (w : e → n → ℝ)
    (Q : (n → ℝ) →ₗ[ℝ] (n → ℝ) →ₗ[ℝ] n → ℝ) (f : Matrix m n ℝ) : Matrix m n ℝ :=
  Matrix.of fun a b => -∑ ℓ, w ℓ b * (D ℓ * f) a b + Q (f a) (f a) b

/-- `⟨v_ℓ V_j V_l⟩_v`. -/
def transportCoeff (w : e → n → ℝ) (V : Matrix n k ℝ) (ℓ : e) (j l : k) : ℝ :=
  ∑ b, w ℓ b * V b j * V b l

/-- `⟨X_i ∂_ℓ X_p⟩_x`. -/
def gradCoeff (D : e → Matrix m m ℝ) (X : Matrix m k ℝ) (ℓ : e) (i p : k) : ℝ :=
  ∑ a, X a i * (D ℓ * X) a p

/-- `⟨X_i X_p X_q⟩_x`. -/
def tripleCoeff (X : Matrix m k ℝ) (i p q : k) : ℝ :=
  ∑ a, X a i * X a p * X a q

/-- The table of the `r²` collision evaluations `Q(W_p, W_q)` for the columns of `W`. -/
def collisionTable (Q : (n → ℝ) →ₗ[ℝ] (n → ℝ) →ₗ[ℝ] n → ℝ) (W : Matrix n k ℝ) (p q : k) : n → ℝ :=
  Q (fun b => W b p) (fun b => W b q)

/-- `⟨V_j τ_{pq}⟩_v`, which is `⟨V_j Q(V_p, V_q)⟩_v` for `τ = collisionTable Q V`. -/
def tableCoeff (V : Matrix n k ℝ) (τ : k → k → n → ℝ) (j p q : k) : ℝ :=
  ∑ b, V b j * τ p q b

/-- The right-hand side of Eq. (2.11), which only sees the table `τ` of collision evaluations. -/
def kRed (D : e → Matrix m m ℝ) (w : e → n → ℝ) (V : Matrix n k ℝ) (τ : k → k → n → ℝ)
    (K : Matrix m k ℝ) : Matrix m k ℝ :=
  Matrix.of fun a j => -∑ ℓ, ∑ l, transportCoeff w V ℓ j l * (D ℓ * K) a l +
    ∑ p, ∑ q, tableCoeff V τ j p q * (K a p * K a q)

/-- The right-hand side of Eq. (2.12), which only sees the table `τ` of collision evaluations. -/
def sRed (D : e → Matrix m m ℝ) (w : e → n → ℝ) (X : Matrix m k ℝ) (V : Matrix n k ℝ)
    (τ : k → k → n → ℝ) (S : Matrix k k ℝ) : Matrix k k ℝ :=
  Matrix.of fun i j => ∑ ℓ, ∑ p, ∑ l, transportCoeff w V ℓ j l * gradCoeff D X ℓ i p * S p l -
    ∑ p, ∑ l, ∑ p', ∑ q', tripleCoeff X i p l * tableCoeff V τ j p' q' * (S p p' * S l q')

/-- The right-hand side of Eq. (2.13), which only sees the table `τ` of collision evaluations.
The columns of `L` are the paper's `L_i(v)`. -/
def lRed (D : e → Matrix m m ℝ) (w : e → n → ℝ) (X : Matrix m k ℝ) (τ : k → k → n → ℝ)
    (L : Matrix n k ℝ) : Matrix n k ℝ :=
  Matrix.of fun b i => -∑ ℓ, ∑ l, w ℓ b * gradCoeff D X ℓ i l * L b l +
    ∑ p, ∑ q, tripleCoeff X i p q * τ p q b

variable (D : e → Matrix m m ℝ) (w : e → n → ℝ) (Q : (n → ℝ) →ₗ[ℝ] (n → ℝ) →ₗ[ℝ] n → ℝ)

omit [Fintype m] [Fintype n] in
/-- A row of `A Wᵀ` as a combination of the columns of `W`. -/
private lemma row_mul_transpose (A : Matrix m k ℝ) (W : Matrix n k ℝ) (a : m) :
    (A * Wᵀ) a = fun b => ∑ p, A a p * W b p := by
  ext b
  simp [Matrix.mul_apply]

omit [Fintype m] [Fintype n] in
/-- Bilinearity: the collision of two combinations of the columns of `W` is the same combination of
the entries of the collision table. -/
private lemma collision_expand (W : Matrix n k ℝ) (c c' : k → ℝ) (b : n) :
    Q (fun b => ∑ p, c p * W b p) (fun b => ∑ q, c' q * W b q) b =
      ∑ p, ∑ q, c p * c' q * collisionTable Q W p q b := by
  have h : ∀ d : k → ℝ, (fun b => ∑ p, d p * W b p) = ∑ p, d p • fun b => W b p := by
    intro d
    ext b
    simp [Finset.sum_apply]
  rw [h c, h c']
  simp only [map_sum, LinearMap.sum_apply, Finset.sum_apply, map_smul, LinearMap.smul_apply,
    Pi.smul_apply, smul_eq_mul, collisionTable, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

omit [Fintype n] in
/-- The right-hand side acting on a low-rank matrix. -/
private lemma rhs_mul_transpose (A : Matrix m k ℝ) (W : Matrix n k ℝ) (a : m) (b : n) :
    boltzmannRHS D w Q (A * Wᵀ) a b =
      -∑ ℓ, w ℓ b * ∑ l, (D ℓ * A) a l * W b l +
        ∑ p, ∑ q, A a p * A a q * collisionTable Q W p q b := by
  have h1 : ∀ ℓ, (D ℓ * (A * Wᵀ)) a b = ∑ l, (D ℓ * A) a l * W b l := by
    intro ℓ
    rw [← Matrix.mul_assoc, Matrix.mul_apply]
    simp
  simp only [boltzmannRHS, Matrix.of_apply, h1, row_mul_transpose, collision_expand]

/-- **Eq. (2.11) of arXiv 2112.02695** (K-step closure), on the fully discrete grid of the paper's
Sec. 2.4 with unit quadrature weights: for `f = K Vᵀ`,
`⟨V_j, RHS⟩_v = -∑_l ⟨v V_j V_l⟩_v · ∇K_l + ∑_{p,q} ⟨V_j Q(V_p, V_q)⟩_v K_p K_q`.
`kField` is the library's K-step field.  No orthonormality is needed. -/
theorem kField_boltzmann (V : Matrix n k ℝ) (t : ℝ) (K : Matrix m k ℝ) :
    MatrixKSL.kField V (fun _ => boltzmannRHS D w Q) t K = kRed D w V (collisionTable Q V) K := by
  ext a j
  rw [MatrixKSL.kField, Matrix.mul_apply]
  simp only [rhs_mul_transpose, kRed, Matrix.of_apply, transportCoeff, tableCoeff, add_mul,
    neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun b _ => by ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun b _ => by ring

omit [Fintype n] [Fintype k] [Fintype e] in
/-- Moving the first of three sums to the inside. -/
private lemma sum_sum_sum_rotate {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℝ) : ∑ a, ∑ b, ∑ c, f a b c = ∑ b, ∑ c, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_comm

omit [Fintype m] [Fintype n] [Fintype e] in
/-- Exchanging the first two of four sums with the last two. -/
private lemma sum_sum_sum_sum_swap (f : k → k → k → k → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d :=
        (Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := Finset.sum_congr rfl fun c _ =>
        (Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans Finset.sum_comm

/-- **Eq. (2.12) of arXiv 2112.02695** (S-step closure), on the discrete grid with unit weights: for
`f = X S Vᵀ`,
`-⟨X_i V_j, RHS⟩ = ∑_{p,l} ⟨v V_j V_l⟩_v · ⟨X_i ∇X_p⟩_x S_{pl}
  - ∑_{p,l,p',q'} ⟨X_i X_p X_l⟩_x ⟨V_j Q(V_{p'}, V_{q'})⟩_v S_{pp'} S_{lq'}`.
`sField` is the library's backward S-step field.  No orthonormality is needed. -/
theorem sField_boltzmann (X : Matrix m k ℝ) (V : Matrix n k ℝ) (t : ℝ) (S : Matrix k k ℝ) :
    MatrixKSL.sField X V (fun _ => boltzmannRHS D w Q) t S =
      sRed D w X V (collisionTable Q V) S := by
  have hk : MatrixKSL.sField X V (fun _ => boltzmannRHS D w Q) t S =
      -(Xᵀ * kRed D w V (collisionTable Q V) (X * S)) := by
    rw [← kField_boltzmann D w Q V t, MatrixKSL.sField, MatrixKSL.kField, Matrix.mul_assoc Xᵀ]
  rw [hk]
  ext i j
  have h1 : ∀ ℓ a l, (D ℓ * (X * S)) a l = ∑ p, (D ℓ * X) a p * S p l := by
    intro ℓ a l
    rw [← Matrix.mul_assoc, Matrix.mul_apply]
  have h2 : ∀ a p, (X * S) a p = ∑ c, X a c * S c p := fun a p => Matrix.mul_apply ..
  have htransport : ∀ ℓ, ∑ a, X a i * ∑ l, transportCoeff w V ℓ j l * (D ℓ * (X * S)) a l =
      ∑ p, ∑ l, transportCoeff w V ℓ j l * gradCoeff D X ℓ i p * S p l := by
    intro ℓ
    simp only [h1, gradCoeff, Finset.mul_sum, Finset.sum_mul]
    rw [sum_sum_sum_rotate, Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun a _ => by ring
  have hcoll : ∀ a, ∑ p', ∑ q', tableCoeff V (collisionTable Q V) j p' q' *
      ((X * S) a p' * (X * S) a q') =
      ∑ p, ∑ l, ∑ p', ∑ q', X a p * X a l * tableCoeff V (collisionTable Q V) j p' q' *
        (S p p' * S l q') := by
    intro a
    have h3 : ∀ p' q', (X * S) a p' * (X * S) a q' =
        ∑ p, ∑ l, X a p * S p p' * (X a l * S l q') := by
      intro p' q'
      rw [h2, h2, Finset.sum_mul_sum]
    simp only [h3, Finset.mul_sum]
    rw [sum_sum_sum_sum_swap]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun p' _ => Finset.sum_congr rfl fun q' _ => by ring
  rw [Matrix.neg_apply, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, kRed, Matrix.of_apply, sRed, hcoll, mul_add,
    Finset.sum_add_distrib, mul_neg, Finset.sum_neg_distrib, neg_add, neg_neg]
  rw [sub_eq_add_neg]
  congr 1
  · simp only [Finset.mul_sum (s := (Finset.univ : Finset e))]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun ℓ _ => htransport ℓ
  · congr 1
    simp only [tripleCoeff, Finset.sum_mul, Finset.mul_sum]
    rw [sum_sum_sum_rotate]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun l _ => ?_
    rw [sum_sum_sum_rotate]
    exact Finset.sum_congr rfl fun p' _ => Finset.sum_congr rfl fun q' _ =>
      Finset.sum_congr rfl fun a _ => by ring

omit [Fintype n] in
/-- **Eq. (2.13) of arXiv 2112.02695** (L-step closure), on the discrete grid with unit weights: for
`f = X Lᵀ`,
`⟨X_i, RHS⟩_x = -∑_l v · ⟨X_i ∇X_l⟩_x L_l + ∑_{p,q} Q(L_p, L_q) ⟨X_i X_p X_q⟩_x`.
`lField` is the library's L-step field.  No orthonormality is needed. -/
theorem lField_boltzmann (X : Matrix m k ℝ) (t : ℝ) (L : Matrix n k ℝ) :
    MatrixKSL.lField X (fun _ => boltzmannRHS D w Q) t L =
      lRed D w X (collisionTable Q L) L := by
  ext b i
  rw [MatrixKSL.lField, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, rhs_mul_transpose, lRed, Matrix.of_apply, gradCoeff,
    tripleCoeff, add_mul, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_mul,
    Finset.mul_sum]
  congr 1
  · congr 1
    rw [sum_sum_sum_rotate]
    exact Finset.sum_congr rfl fun ℓ _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun a _ => by ring
  · rw [sum_sum_sum_rotate]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
      Finset.sum_congr rfl fun a _ => by ring

omit [Fintype m] [Fintype n] [Fintype e] in
/-- **Eqs. (2.11)-(2.13) of arXiv 2112.02695**: a collision table has `r²` entries. -/
theorem card_collisionTable : Fintype.card (k × k) = Fintype.card k ^ 2 := by
  rw [Fintype.card_prod, sq]

/-- **The closure of Eqs. (2.11)-(2.13) of arXiv 2112.02695**: each substep needs `Q` only through
`r²` evaluations.  Two bilinear collision operators with the same table on the columns of `V` give
the same K- and S-fields, and with the same table on the columns of `L` the same L-field, however
fine the grid is.  This is the immediate consequence of `kField_boltzmann`, `sField_boltzmann` and
`lField_boltzmann`, whose reduced right-hand sides take the table as their only access to `Q`. -/
theorem fields_eq_of_collisionTable_eq (Q' : (n → ℝ) →ₗ[ℝ] (n → ℝ) →ₗ[ℝ] n → ℝ) (t : ℝ)
    (X : Matrix m k ℝ) (V L : Matrix n k ℝ) (K : Matrix m k ℝ) (S : Matrix k k ℝ)
    (hV : collisionTable Q V = collisionTable Q' V)
    (hL : collisionTable Q L = collisionTable Q' L) :
    MatrixKSL.kField V (fun _ => boltzmannRHS D w Q) t K =
        MatrixKSL.kField V (fun _ => boltzmannRHS D w Q') t K ∧
      MatrixKSL.sField X V (fun _ => boltzmannRHS D w Q) t S =
        MatrixKSL.sField X V (fun _ => boltzmannRHS D w Q') t S ∧
      MatrixKSL.lField X (fun _ => boltzmannRHS D w Q) t L =
        MatrixKSL.lField X (fun _ => boltzmannRHS D w Q') t L := by
  rw [kField_boltzmann, kField_boltzmann, sField_boltzmann, sField_boltzmann, lField_boltzmann,
    lField_boltzmann, hV, hL]
  exact ⟨rfl, rfl, rfl⟩

/-- **Eqs. (2.11)-(2.13) of arXiv 2112.02695 are the projector-splitting integrator**: solutions of
the three reduced systems, with the QR factorization `K(t₁) = U₁ Ŝ₁` and the matching initial
values of the first-order PSI scheme, form a step of the library's matrix KSL integrator for
`F = boltzmannRHS D w Q`.  The time discretization of the paper's Sec. 2.4 is not formalized. -/
theorem isStep_of_closure [DecidableEq k] {t₀ t₁ : ℝ} {U₀ U₁ : Matrix m k ℝ}
    {S₀ Ŝ₁ : Matrix k k ℝ} {V₀ : Matrix n k ℝ} {K : ℝ → Matrix m k ℝ} {S : ℝ → Matrix k k ℝ}
    {Lf : ℝ → Matrix n k ℝ} (hV₀ : V₀ᵀ * V₀ = 1)
    (hK : ODESolution (fun _ K => kRed D w V₀ (collisionTable Q V₀) K) K t₀ t₁)
    (hK₀ : K t₀ = U₀ * S₀) (hU₁ : U₁ᵀ * U₁ = 1) (hQR : K t₁ = U₁ * Ŝ₁)
    (hS : ODESolution (fun _ S => sRed D w U₁ V₀ (collisionTable Q V₀) S) S t₀ t₁)
    (hS₀ : S t₀ = Ŝ₁)
    (hL : ODESolution (fun _ L => lRed D w U₁ (collisionTable Q L) L) Lf t₀ t₁)
    (hL₀ : Lf t₀ = V₀ * (S t₁)ᵀ) :
    MatrixKSL.IsStep (fun _ => boltzmannRHS D w Q) t₀ t₁ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf where
  orthV₀ := hV₀
  kSol := by
    have h : MatrixKSL.kField V₀ (fun _ => boltzmannRHS D w Q) =
        fun _ K => kRed D w V₀ (collisionTable Q V₀) K := by
      funext t K
      exact kField_boltzmann D w Q V₀ t K
    rwa [h]
  kStart := hK₀
  orthU₁ := hU₁
  kQR := hQR
  sSol := by
    have h : MatrixKSL.sField U₁ V₀ (fun _ => boltzmannRHS D w Q) =
        fun _ S => sRed D w U₁ V₀ (collisionTable Q V₀) S := by
      funext t S
      exact sField_boltzmann D w Q U₁ V₀ t S
    rwa [h]
  sStart := hS₀
  lSol := by
    have h : MatrixKSL.lField U₁ (fun _ => boltzmannRHS D w Q) =
        fun _ L => lRed D w U₁ (collisionTable Q L) L := by
      funext t L
      exact lField_boltzmann D w Q U₁ t L
    rwa [h]
  lStart := hL₀

end Closure

/-! ### Truncated singular value decompositions -/

section Truncation

variable {α β : Type*} [Fintype α] [Fintype β] {p r : ℕ}

/-- `A = U diag(σ) Wᵀ` is a singular value decomposition with `p` components: orthonormal columns
and nonnegative singular values in decreasing order. -/
structure IsSVD (A : Matrix α β ℝ) (U : Matrix α (Fin p) ℝ) (σ : Fin p → ℝ)
    (W : Matrix β (Fin p) ℝ) : Prop where
  orthU : Uᵀ * U = 1
  orthW : Wᵀ * W = 1
  antitone : Antitone σ
  nonneg : ∀ i, 0 ≤ σ i
  eq : A = U * Matrix.diagonal σ * Wᵀ

/-- The first `r` columns `A(:, 1:r)` of `A`. -/
def firstCols {γ : Type*} (A : Matrix γ (Fin p) ℝ) (hr : r ≤ p) : Matrix γ (Fin r) ℝ :=
  A.submatrix id (Fin.castLE hr)

/-- The first `r` singular values. -/
def firstVals (σ : Fin p → ℝ) (hr : r ≤ p) : Fin r → ℝ := σ ∘ Fin.castLE hr

/-- The SVD truncated to its first `r` components. -/
def truncSVD (U : Matrix α (Fin p) ℝ) (σ : Fin p → ℝ) (W : Matrix β (Fin p) ℝ) (hr : r ≤ p) :
    Matrix α β ℝ :=
  firstCols U hr * Matrix.diagonal (firstVals σ hr) * (firstCols W hr)ᵀ

/-- The squared Frobenius norm `∑_{i ≥ r} σ_i²` of the discarded singular values. -/
def tailSq (σ : Fin p → ℝ) (r : ℕ) : ℝ :=
  ∑ i : Fin p, if r ≤ (i : ℕ) then σ i ^ 2 else 0

/-- Sums over the first `r` indices. -/
private lemma sum_castLE (hr : r ≤ p) (g : Fin p → ℝ) :
    ∑ i : Fin r, g (Fin.castLE hr i) = ∑ i : Fin p, if (i : ℕ) < r then g i else 0 := by
  rw [← Finset.sum_filter]
  have h : Finset.filter (fun i : Fin p => (i : ℕ) < r) Finset.univ =
      Finset.univ.map (Fin.castLEEmb hr) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Fin.castLEEmb_apply]
    constructor
    · intro hi
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact j.2
  rw [h, Finset.sum_map]
  rfl

/-- **Sec. 3.2 of arXiv 2112.02695**: the columns kept by a truncation stay orthonormal. -/
theorem firstCols_orthonormal {γ : Type*} [Fintype γ] {U : Matrix γ (Fin p) ℝ} (hU : Uᵀ * U = 1)
    (hr : r ≤ p) : (firstCols U hr)ᵀ * firstCols U hr = 1 := by
  have h : (firstCols U hr)ᵀ * firstCols U hr =
      (Uᵀ * U).submatrix (Fin.castLE hr) (Fin.castLE hr) := by
    ext i j
    simp [firstCols, Matrix.mul_apply]
  rw [h, hU]
  exact Matrix.submatrix_one _ (Fin.castLE_injective hr)

omit [Fintype α] [Fintype β] in
/-- The truncation as the SVD with the discarded singular values set to zero. -/
private lemma truncSVD_eq (U : Matrix α (Fin p) ℝ) (σ : Fin p → ℝ) (W : Matrix β (Fin p) ℝ)
    (hr : r ≤ p) :
    truncSVD U σ W hr =
      U * Matrix.diagonal (fun i : Fin p => if (i : ℕ) < r then σ i else 0) * Wᵀ := by
  ext a b
  rw [truncSVD, Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, firstCols, firstVals,
    Matrix.submatrix_apply, id, Function.comp]
  rw [sum_castLE hr (fun i => U a i * σ i * W b i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

/-- **Truncation error of an SVD** (Secs. 3.1, 3.2 of arXiv 2112.02695), exactly:
`‖A - A_r‖² = ∑_{i ≥ r} σ_i²`. -/
theorem IsSVD.norm_sub_truncSVD_sq {A : Matrix α β ℝ} {U : Matrix α (Fin p) ℝ} {σ : Fin p → ℝ}
    {W : Matrix β (Fin p) ℝ} (h : IsSVD A U σ W) (hr : r ≤ p) :
    ‖A - truncSVD U σ W hr‖ ^ 2 = tailSq σ r := by
  have hsub : A - truncSVD U σ W hr =
      U * Matrix.diagonal (fun i : Fin p => if r ≤ (i : ℕ) then σ i else 0) * Wᵀ := by
    conv_lhs => rw [h.eq]
    rw [truncSVD_eq, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]
    congr 3
    ext i
    by_cases hi : (i : ℕ) < r
    · simp [hi, not_le.mpr hi]
    · simp [hi, not_lt.mp hi]
  rw [hsub, LeanDLRA.Frobenius.norm_mul_transpose_of_orthonormal h.orthW,
    LeanDLRA.Frobenius.norm_mul_of_orthonormal h.orthU, LeanDLRA.Frobenius.norm_sq_eq_sum,
    tailSq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · by_cases hi : r ≤ (i : ℕ) <;> simp [hi]
  · intro j _ hj
    simp [Matrix.diagonal_apply_ne _ (Ne.symm hj)]
  · simp

/-- The number of discarded singular values. -/
private lemma sum_ite_le (hr : r ≤ p) :
    (∑ i : Fin p, if r ≤ (i : ℕ) then (1 : ℝ) else 0) = (p : ℝ) - r := by
  have h := sum_castLE hr (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  have h' : (∑ i : Fin p, if r ≤ (i : ℕ) then (1 : ℝ) else 0) =
      ∑ i : Fin p, (1 - if (i : ℕ) < r then (1 : ℝ) else 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : (i : ℕ) < r
    · simp [hi, not_le.mpr hi]
    · simp [hi, not_lt.mp hi]
  rw [h', Finset.sum_sub_distrib, ← h]
  simp

/-- **Sec. 3.2 of arXiv 2112.02695**: if all discarded singular values are below `tol` then
`∑_{i ≥ r} σ_i² ≤ (p - r) tol²`. -/
theorem tailSq_le {σ : Fin p → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hr : r ≤ p) {tol : ℝ}
    (htol : ∀ i : Fin p, r ≤ (i : ℕ) → σ i ≤ tol) : tailSq σ r ≤ ((p : ℝ) - r) * tol ^ 2 := by
  rw [← sum_ite_le hr, Finset.sum_mul, tailSq]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : r ≤ (i : ℕ)
  · simpa [hi] using pow_le_pow_left₀ (hσ i) (htol i hi) 2
  · simp [hi]

/-- **Secs. 3.1, 3.2 of arXiv 2112.02695**: `‖A - A_r‖ ≤ √(p - r) tol` when all discarded singular
values are below `tol`. -/
theorem IsSVD.norm_sub_truncSVD_le {A : Matrix α β ℝ} {U : Matrix α (Fin p) ℝ} {σ : Fin p → ℝ}
    {W : Matrix β (Fin p) ℝ} (h : IsSVD A U σ W) (hr : r ≤ p) {tol : ℝ} (h0 : 0 ≤ tol)
    (htol : ∀ i : Fin p, r ≤ (i : ℕ) → σ i ≤ tol) :
    ‖A - truncSVD U σ W hr‖ ≤ √((p : ℝ) - r) * tol := by
  have hp : (0 : ℝ) ≤ (p : ℝ) - r := sub_nonneg.mpr (by exact_mod_cast hr)
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [h.norm_sub_truncSVD_sq hr, mul_pow, Real.sq_sqrt hp]
  exact tailSq_le h.nonneg hr htol

/-- **The rank kept by a threshold exists**: for decreasing `σ` and any `tol` there is `r ≤ p` such
that the singular values `≥ tol` are exactly the first `r` ones (step 2 of Sec. 3.2 of
arXiv 2112.02695, and of Sec. 3.1 with `tol = 10⁻¹⁰`). -/
theorem exists_keep {σ : Fin p → ℝ} (hσ : Antitone σ) (tol : ℝ) :
    ∃ (r : ℕ), r ≤ p ∧ ∀ i : Fin p, (i : ℕ) < r ↔ tol ≤ σ i := by
  classical
  have hex : ∃ r, r ≤ p ∧ ∀ i : Fin p, r ≤ (i : ℕ) → σ i < tol :=
    ⟨p, le_rfl, fun i hi => absurd i.2 (not_lt.mpr hi)⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · by_contra hc
    have hc' : σ i < tol := not_le.mp hc
    have hm := Nat.find_min hex (m := i) hi
    refine hm ⟨i.2.le, fun j hj => lt_of_le_of_lt (hσ ?_) hc'⟩
    exact_mod_cast hj
  · by_contra hc
    exact absurd ((Nat.find_spec hex).2 i (not_lt.mp hc)) (not_lt.mpr hi)

end Truncation

/-! ### Sec. 3.2 and Eqs. (5.6)-(5.7): rank dropping with error control -/

section RankDrop

variable {m n : Type*} [Fintype m] [Fintype n] {r r' : ℕ}

/-- The state after the rank reduction of Sec. 3.2: from `f = X S Vᵀ` and the SVD
`S = U diag(σ) Wᵀ`, the bases `X̄ = X U(:, 1:r')`, `V̄ = V W(:, 1:r')` and the core `diag(σ(1:r'))`
give `f̄ = X̄ S̄ V̄ᵀ`. -/
def droppedState (X : Matrix m (Fin r) ℝ) (U : Matrix (Fin r) (Fin r) ℝ) (σ : Fin r → ℝ)
    (W : Matrix (Fin r) (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) (hr : r' ≤ r) : Matrix m n ℝ :=
  (X * firstCols U hr) * Matrix.diagonal (firstVals σ hr) * (V * firstCols W hr)ᵀ

/-- **Sec. 3.2 of arXiv 2112.02695**: an SVD of the core `S` gives an SVD of `f = X S Vᵀ`. -/
theorem IsSVD.mul {X : Matrix m (Fin r) ℝ} {V : Matrix n (Fin r) ℝ} {S : Matrix (Fin r) (Fin r) ℝ}
    {U W : Matrix (Fin r) (Fin r) ℝ} {σ : Fin r → ℝ} (hX : Xᵀ * X = 1) (hV : Vᵀ * V = 1)
    (hS : IsSVD S U σ W) : IsSVD (X * S * Vᵀ) (X * U) σ (V * W) where
  orthU := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Xᵀ, hX, Matrix.one_mul,
      hS.orthU]
  orthW := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ, hV, Matrix.one_mul,
      hS.orthW]
  antitone := hS.antitone
  nonneg := hS.nonneg
  eq := by
    conv_lhs => rw [hS.eq]
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]

omit [Fintype m] [Fintype n] in
/-- Rotating the basis and then truncating is truncating the rotated basis. -/
private lemma firstCols_mul (X : Matrix m (Fin r) ℝ) (U : Matrix (Fin r) (Fin r) ℝ)
    (hr : r' ≤ r) : firstCols (X * U) hr = X * firstCols U hr := by
  ext a i
  simp [firstCols, Matrix.mul_apply]

omit [Fintype m] [Fintype n] in
/-- `droppedState` is the truncation of the SVD of `f`. -/
private lemma droppedState_eq (X : Matrix m (Fin r) ℝ) (U : Matrix (Fin r) (Fin r) ℝ)
    (σ : Fin r → ℝ) (W : Matrix (Fin r) (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) (hr : r' ≤ r) :
    droppedState X U σ W V hr = truncSVD (X * U) σ (V * W) hr := by
  rw [droppedState, truncSVD, firstCols_mul, firstCols_mul]

/-- **Sec. 3.2 of arXiv 2112.02695, step 3**: the rotated and truncated bases are orthonormal. -/
theorem droppedBases_orthonormal {X : Matrix m (Fin r) ℝ} {V : Matrix n (Fin r) ℝ}
    {S U W : Matrix (Fin r) (Fin r) ℝ} {σ : Fin r → ℝ} (hX : Xᵀ * X = 1) (hV : Vᵀ * V = 1)
    (hS : IsSVD S U σ W) (hr : r' ≤ r) :
    (X * firstCols U hr)ᵀ * (X * firstCols U hr) = 1 ∧
      (V * firstCols W hr)ᵀ * (V * firstCols W hr) = 1 := by
  have h := IsSVD.mul hX hV hS
  rw [← firstCols_mul, ← firstCols_mul]
  exact ⟨firstCols_orthonormal h.orthU hr, firstCols_orthonormal h.orthW hr⟩

/-- **Sec. 3.2 of arXiv 2112.02695, the error of dropping**: if `f = X S Vᵀ` has orthonormal bases,
`S = U diag(σ) Wᵀ`, and the singular values kept are exactly those `≥ tol`, namely the first `r'`,
then `‖f̄ - f‖² = ∑_{i ≥ r'} σ_i²` and `‖f̄ - f‖ ≤ √(r - r') tol`.  The paper's norm is the discrete
`L²` norm, here with unit quadrature weights.  `exists_keep` gives `r'`. -/
theorem norm_droppedState_sub_le {X : Matrix m (Fin r) ℝ} {V : Matrix n (Fin r) ℝ}
    {S U W : Matrix (Fin r) (Fin r) ℝ} {σ : Fin r → ℝ} (hX : Xᵀ * X = 1) (hV : Vᵀ * V = 1)
    (hS : IsSVD S U σ W) (hr : r' ≤ r) {tol : ℝ} (h0 : 0 ≤ tol)
    (hkeep : ∀ i : Fin r, (i : ℕ) < r' ↔ tol ≤ σ i) :
    ‖droppedState X U σ W V hr - X * S * Vᵀ‖ ^ 2 = tailSq σ r' ∧
      ‖droppedState X U σ W V hr - X * S * Vᵀ‖ ≤ √((r : ℝ) - r') * tol := by
  have h := IsSVD.mul hX hV hS
  rw [droppedState_eq, norm_sub_rev]
  refine ⟨h.norm_sub_truncSVD_sq hr, h.norm_sub_truncSVD_le hr h0 fun i hi => ?_⟩
  exact (not_le.mp fun hc => absurd ((hkeep i).mpr hc) (not_lt.mpr hi)).le

/-- **Eq. (5.6) of arXiv 2112.02695**: with `err = ‖f¹ - f⁰‖`, `err_ada = ‖f̄¹ - f⁰‖`,
`|err - err_ada| ≤ ‖f̄¹ - f¹‖ ≤ √(r - r') drop_tol`, for any previous state `f⁰`. -/
theorem eq5_6 {X : Matrix m (Fin r) ℝ} {V : Matrix n (Fin r) ℝ}
    {S U W : Matrix (Fin r) (Fin r) ℝ} {σ : Fin r → ℝ} (hX : Xᵀ * X = 1) (hV : Vᵀ * V = 1)
    (hS : IsSVD S U σ W) (hr : r' ≤ r) {tol : ℝ} (h0 : 0 ≤ tol)
    (hkeep : ∀ i : Fin r, (i : ℕ) < r' ↔ tol ≤ σ i) (f₀ : Matrix m n ℝ) :
    |‖X * S * Vᵀ - f₀‖ - ‖droppedState X U σ W V hr - f₀‖| ≤
        ‖droppedState X U σ W V hr - X * S * Vᵀ‖ ∧
      ‖droppedState X U σ W V hr - X * S * Vᵀ‖ ≤ √((r : ℝ) - r') * tol := by
  refine ⟨?_, (norm_droppedState_sub_le hX hV hS hr h0 hkeep).2⟩
  have h := abs_norm_sub_norm_le (X * S * Vᵀ - f₀) (droppedState X U σ W V hr - f₀)
  rwa [sub_sub_sub_cancel_right, norm_sub_rev (X * S * Vᵀ) (droppedState X U σ W V hr)] at h

/-- **Eq. (5.7) of arXiv 2112.02695**: with `drop_tol ≤ c err_ada` (the paper takes equality, with
`c = 0.2`) and `c √(r - r') < 1`,
`err / (1 + c √(r - r')) ≤ err_ada ≤ err / (1 - c √(r - r'))`.

Difference from the paper: `c √(r - r') < 1` is not stated there, and it cannot be dropped, see
`eq5_7_needs_condition`.  `err_ada` depends on `drop_tol`, so the paper's choice is an implicit
equation; its solvability is exhibited in `eq5_7_satisfiable`. -/
theorem eq5_7 {X : Matrix m (Fin r) ℝ} {V : Matrix n (Fin r) ℝ}
    {S U W : Matrix (Fin r) (Fin r) ℝ} {σ : Fin r → ℝ} (hX : Xᵀ * X = 1) (hV : Vᵀ * V = 1)
    (hS : IsSVD S U σ W) (hr : r' ≤ r) {tol : ℝ} (h0 : 0 ≤ tol)
    (hkeep : ∀ i : Fin r, (i : ℕ) < r' ↔ tol ≤ σ i) (f₀ : Matrix m n ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hc1 : c * √((r : ℝ) - r') < 1) (htol : tol ≤ c * ‖droppedState X U σ W V hr - f₀‖) :
    ‖X * S * Vᵀ - f₀‖ / (1 + c * √((r : ℝ) - r')) ≤ ‖droppedState X U σ W V hr - f₀‖ ∧
      ‖droppedState X U σ W V hr - f₀‖ ≤ ‖X * S * Vᵀ - f₀‖ / (1 - c * √((r : ℝ) - r')) := by
  obtain ⟨h1, h2⟩ := eq5_6 hX hV hS hr h0 hkeep f₀
  set err := ‖X * S * Vᵀ - f₀‖
  set ada := ‖droppedState X U σ W V hr - f₀‖
  set s := √((r : ℝ) - r')
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hbound : |err - ada| ≤ c * s * ada := by
    calc |err - ada| ≤ s * tol := h1.trans h2
      _ ≤ s * (c * ada) := mul_le_mul_of_nonneg_left htol hs
      _ = c * s * ada := by ring
  have hab := abs_le.mp hbound
  constructor
  · rw [div_le_iff₀ (by positivity)]
    nlinarith [hab.2]
  · rw [le_div_iff₀ (by linarith)]
    nlinarith [hab.1]

omit [Fintype m] [Fintype n] in
/-- The Frobenius norm of the identity. -/
private lemma norm_one_fin : ‖(1 : Matrix (Fin r) (Fin r) ℝ)‖ = √(r : ℝ) := by
  rw [LeanDLRA.Frobenius.norm_def]
  congr 1
  simp [Matrix.one_apply, ite_pow]

/-- **The hypotheses of `eq5_7` hold with the paper's `c = 0.2` and a real drop**: for
`S = diag(1, 1/10)`, `f⁰ = 0` and `drop_tol = 1/5`, the second singular value is dropped and
`drop_tol = c err_ada`, with `c √(r - r') = 1/5 < 1`. -/
theorem eq5_7_satisfiable :
    ∃ σ : Fin 2 → ℝ,
      IsSVD (Matrix.diagonal σ) (1 : Matrix (Fin 2) (Fin 2) ℝ) σ 1 ∧
      (∀ i : Fin 2, (i : ℕ) < 1 ↔ (1 / 5 : ℝ) ≤ σ i) ∧
      (1 / 5 : ℝ) = 1 / 5 * ‖droppedState (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 σ 1
        (1 : Matrix (Fin 2) (Fin 2) ℝ) (by norm_num : 1 ≤ 2) - 0‖ ∧
      (1 / 5 : ℝ) * √(((2 : ℕ) : ℝ) - ((1 : ℕ) : ℝ)) < 1 := by
  refine ⟨![1, 1 / 10], ⟨by simp, by simp, ?_, ?_, by simp⟩, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    norm_num
  · intro i
    fin_cases i <;> simp
  · intro i
    fin_cases i <;> norm_num
  · have h : droppedState (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 ![1, 1 / 10] 1
        (1 : Matrix (Fin 2) (Fin 2) ℝ) (by norm_num : 1 ≤ 2) =
        Matrix.diagonal fun i : Fin 2 =>
          if (i : ℕ) < 1 then (![1, 1 / 10] : Fin 2 → ℝ) i else 0 := by
      rw [droppedState_eq, truncSVD_eq]
      simp
    rw [h, sub_zero, LeanDLRA.Frobenius.norm_def]
    simp [Matrix.diagonal_apply]
  · norm_num

/-- **The bound `c √(r - r') < 1` in `eq5_7` cannot be dropped**: if `c √r > 1` there are data with
`r' = 0` and `drop_tol = c err_ada` for which the upper bound of Eq. (5.7) fails, since
its right-hand side is not positive.  For the paper's `c = 0.2` this happens as soon as `r > 25`;
at `r = 25` its denominator vanishes. -/
theorem eq5_7_needs_condition {c : ℝ} (hr : 1 < c * √(r : ℝ)) :
    ∃ (σ : Fin r → ℝ) (f₀ : Matrix (Fin r) (Fin r) ℝ),
      IsSVD (Matrix.diagonal σ) (1 : Matrix (Fin r) (Fin r) ℝ) σ 1 ∧
      (∀ i : Fin r, (i : ℕ) < 0 ↔ c * ‖droppedState (1 : Matrix (Fin r) (Fin r) ℝ) 1 σ 1
        (1 : Matrix (Fin r) (Fin r) ℝ) (Nat.zero_le r) - f₀‖ ≤ σ i) ∧
      ¬ ‖droppedState (1 : Matrix (Fin r) (Fin r) ℝ) 1 σ 1 (1 : Matrix (Fin r) (Fin r) ℝ)
          (Nat.zero_le r) - f₀‖ ≤
        ‖(1 : Matrix (Fin r) (Fin r) ℝ) * Matrix.diagonal σ *
            (1 : Matrix (Fin r) (Fin r) ℝ)ᵀ - f₀‖ /
          (1 - c * √((r : ℝ) - ((0 : ℕ) : ℝ))) := by
  have hzero : droppedState (1 : Matrix (Fin r) (Fin r) ℝ) 1 (fun _ => (1 : ℝ)) 1
      (1 : Matrix (Fin r) (Fin r) ℝ) (Nat.zero_le r) = 0 := by
    ext a b
    rw [droppedState, Matrix.mul_apply]
    simp
  have hnorm : ‖(0 : Matrix (Fin r) (Fin r) ℝ) - (-1 : Matrix (Fin r) (Fin r) ℝ)‖ = √(r : ℝ) := by
    rw [zero_sub, neg_neg, norm_one_fin]
  have hs : 0 < √(r : ℝ) := by
    by_contra h
    have h0 : √(r : ℝ) = 0 := le_antisymm (not_lt.mp h) (Real.sqrt_nonneg _)
    rw [h0] at hr
    linarith
  refine ⟨fun _ => 1, -1, ⟨by simp, by simp, fun _ _ _ => le_rfl, fun _ => zero_le_one,
    by simp⟩, ?_, ?_⟩
  · intro i
    rw [hzero, hnorm]
    constructor
    · intro h
      exact absurd h (Nat.not_lt_zero _)
    · intro h
      exact absurd h (not_le.mpr hr)
  · rw [hzero, hnorm, Nat.cast_zero, sub_zero]
    exact not_le.mpr (lt_of_le_of_lt
      (div_nonpos_of_nonneg_of_nonpos (norm_nonneg _) (by linarith)) hs)

end RankDrop

/-! ### Sec. 3.1: exact augmentation with the boundary basis -/

section Augmentation

variable {m n k b c c' : Type*} [Fintype k] [Fintype b]

/-- **Eq. (3.2) of arXiv 2112.02695**: padding `X` by arbitrary (in the paper random) columns `X_h`,
`V` by arbitrary columns `Q̄_b`, and `S` by zeros leaves `f = X S Vᵀ` unchanged. -/
theorem eq3_2 (X : Matrix m k ℝ) (XH : Matrix m b ℝ) (S : Matrix k k ℝ) (V : Matrix n k ℝ)
    (Qb : Matrix n b ℝ) :
    Matrix.fromCols X XH * Matrix.fromBlocks S 0 0 (0 : Matrix b b ℝ) *
      (Matrix.fromCols V Qb)ᵀ = X * S * Vᵀ := by
  ext a d
  simp [Matrix.mul_apply, Fintype.sum_sum_type]

variable [Fintype c] [Fintype c']

/-- **Sec. 3.1 of arXiv 2112.02695, step 4**: after the QR factorizations `X̂ = X_q S_x`,
`V̂ = V_q S_v` and with `S_q = S_x Ŝ S_vᵀ`, the state `X_q S_q V_qᵀ` is still `f = X S Vᵀ`.  Only
the factorizations are used, not the triangular shape of `S_x`, `S_v`. -/
theorem augmentation_exact {X : Matrix m k ℝ} {XH : Matrix m b ℝ} {S : Matrix k k ℝ}
    {V : Matrix n k ℝ} {Qb : Matrix n b ℝ} {Xq : Matrix m c ℝ} {Sx : Matrix c (k ⊕ b) ℝ}
    {Vq : Matrix n c' ℝ} {Sv : Matrix c' (k ⊕ b) ℝ} (hX : Matrix.fromCols X XH = Xq * Sx)
    (hV : Matrix.fromCols V Qb = Vq * Sv) :
    Xq * (Sx * Matrix.fromBlocks S 0 0 (0 : Matrix b b ℝ) * Svᵀ) * Vqᵀ = X * S * Vᵀ := by
  rw [← eq3_2 X XH S V Qb, hX, hV, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

variable [Fintype m] [Fintype n] [DecidableEq c] [DecidableEq c']

/-- **The QR factorizations of Sec. 3.1 of arXiv 2112.02695 exist** as soon as the columns fit,
`r + r_b ≤ N`, also for rank-deficient blocks. -/
theorem exists_block_qr {κ : Type*} [Fintype κ] (A : Matrix m κ ℝ)
    (h : Fintype.card κ ≤ Fintype.card m) :
    ∃ (Q : Matrix m (Fin (Fintype.card κ)) ℝ) (T : Matrix (Fin (Fintype.card κ)) κ ℝ),
      Qᵀ * Q = 1 ∧ A = Q * T := by
  obtain ⟨U, hU, hcap⟩ := exists_orthonormal_capture A A.rank_le_card_width h
  exact ⟨U, Uᵀ * A, hU, by rw [← Matrix.mul_assoc, hcap]⟩

omit [Fintype k] [Fintype b] in
/-- **Sec. 3.1 of arXiv 2112.02695, the span**: `span V_q` contains the old basis and the
appended boundary vectors. -/
theorem augmentation_span {V : Matrix n k ℝ} {Qb : Matrix n b ℝ} {Vq : Matrix n c' ℝ}
    {Sv : Matrix c' (k ⊕ b) ℝ} (hVq : Vqᵀ * Vq = 1) (hV : Matrix.fromCols V Qb = Vq * Sv) :
    Vq * Vqᵀ * V = V ∧ Vq * Vqᵀ * Qb = Qb := by
  have h : Vq * Vqᵀ * Matrix.fromCols V Qb = Matrix.fromCols V Qb := by
    rw [hV, Matrix.mul_assoc, ← Matrix.mul_assoc Vqᵀ, hVq, Matrix.one_mul]
  rw [Matrix.mul_fromCols] at h
  exact Matrix.fromCols_inj.eq_iff.mp h

omit [Fintype b] in
/-- **Sec. 3.1 of arXiv 2112.02695, as enlarged projectors**: the augmentation enlarges the
projector onto the velocity basis (`Q_new Q_old = Q_old`), and both new projectors fix the state,
through the library's `aug_fix_of_comp_eq`. -/
theorem augmentation_projectors {X : Matrix m k ℝ} {XH : Matrix m b ℝ} {S : Matrix k k ℝ}
    {V : Matrix n k ℝ} {Qb : Matrix n b ℝ} {Xq : Matrix m c ℝ} {Sx : Matrix c (k ⊕ b) ℝ}
    {Vq : Matrix n c' ℝ} {Sv : Matrix c' (k ⊕ b) ℝ} [DecidableEq k] (hX₀ : Xᵀ * X = 1)
    (hV₀ : Vᵀ * V = 1) (hXq : Xqᵀ * Xq = 1) (hVq : Vqᵀ * Vq = 1)
    (hX : Matrix.fromCols X XH = Xq * Sx) (hV : Matrix.fromCols V Qb = Vq * Sv) :
    (∀ Z : Matrix m n ℝ, rightProj Vq (rightProj V Z) = rightProj V Z) ∧
      rightProj Vq (X * S * Vᵀ) = X * S * Vᵀ ∧ leftProj Xq (X * S * Vᵀ) = X * S * Vᵀ := by
  have hright := rightProj_rightProj_of_mul (m := m) (augmentation_span hVq hV).1
  have hleft := leftProj_leftProj_of_mul (n := n) (augmentation_span hXq hX).1
  refine ⟨hright, aug_fix_of_comp_eq hright (rightProj_mul_transpose hV₀ _), ?_⟩
  rw [Matrix.mul_assoc]
  exact aug_fix_of_comp_eq hleft (leftProj_mul_left hX₀ _)

omit [Fintype k] in
/-- **Sec. 3.1 of arXiv 2112.02695, the boundary profiles lie in the new basis.**  Let
`F_b = U_b diag(σ) W_bᵀ` be an SVD of the boundary data (its rows are the boundary profiles), keep
the singular values `≥ tol`, the first `r_b`, and append `W_b(:, 1:r_b)` to `V`.  Then
`‖F_b - F_b V_q V_qᵀ‖ ≤ √(p - r_b) tol`, so `K_b = F_b V_q` reproduces the data up to the cutoff
(the paper's `tol` is `10⁻¹⁰`), and exactly when the discarded singular values vanish. -/
theorem boundary_capture {e : Type*} [Fintype e] {p rb : ℕ} {Fb : Matrix e n ℝ}
    {Ub : Matrix e (Fin p) ℝ} {σ : Fin p → ℝ} {Wb : Matrix n (Fin p) ℝ} (hF : IsSVD Fb Ub σ Wb)
    (hr : rb ≤ p) {V : Matrix n k ℝ} {Vq : Matrix n c' ℝ} {Sv : Matrix c' (k ⊕ Fin rb) ℝ}
    (hVq : Vqᵀ * Vq = 1) (hV : Matrix.fromCols V (firstCols Wb hr) = Vq * Sv) :
    ‖Fb - Fb * Vq * Vqᵀ‖ ^ 2 ≤ tailSq σ rb ∧
      ((∀ i : Fin p, rb ≤ (i : ℕ) → σ i = 0) → Fb * Vq * Vqᵀ = Fb) ∧
      ∀ tol : ℝ, 0 ≤ tol → (∀ i : Fin p, (i : ℕ) < rb ↔ tol ≤ σ i) →
        ‖Fb - Fb * Vq * Vqᵀ‖ ≤ √((p : ℝ) - rb) * tol := by
  have hQ : (firstCols Wb hr)ᵀ * Vq * Vqᵀ = (firstCols Wb hr)ᵀ := by
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using
      congrArg Matrix.transpose (augmentation_span hVq hV).2
  have hT : truncSVD Ub σ Wb hr * Vq * Vqᵀ = truncSVD Ub σ Wb hr := by
    rw [truncSVD, Matrix.mul_assoc _ _ Vqᵀ, Matrix.mul_assoc _ _ (Vq * Vqᵀ),
      ← Matrix.mul_assoc _ Vq, hQ]
  have hE : Fb - Fb * Vq * Vqᵀ = (Fb - truncSVD Ub σ Wb hr) -
      rightProj Vq (Fb - truncSVD Ub σ Wb hr) := by
    rw [rightProj_apply, Matrix.sub_mul, Matrix.sub_mul, hT]
    abel
  have hle : ‖Fb - Fb * Vq * Vqᵀ‖ ≤ ‖Fb - truncSVD Ub σ Wb hr‖ := by
    rw [hE]
    exact (isOrthProj_rightProj hVq).norm_sub_le _
  have hsq : ‖Fb - Fb * Vq * Vqᵀ‖ ^ 2 ≤ tailSq σ rb := by
    rw [← hF.norm_sub_truncSVD_sq hr]
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  refine ⟨hsq, fun hzero => ?_, fun tol h0 hkeep => hle.trans ?_⟩
  · have htail : tailSq σ rb = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hi : rb ≤ (i : ℕ)
      · simp [hi, hzero i hi]
      · simp [hi]
    rw [htail] at hsq
    have h0' : ‖Fb - Fb * Vq * Vqᵀ‖ = 0 :=
      pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm hsq (by positivity))
    exact (sub_eq_zero.mp (norm_eq_zero.mp h0')).symm
  · refine hF.norm_sub_truncSVD_le hr h0 fun i hi => ?_
    exact (not_le.mp fun hc => absurd ((hkeep i).mpr hc) (not_lt.mpr hi)).le

end Augmentation

/-! ### Eqs. (5.3)-(5.5): the factored residual norm -/

section Residual

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

omit [Fintype m] [Fintype n] in
/-- **Eq. (5.3) of arXiv 2112.02695**: with `f⁰ = X⁰ S⁰ V⁰ᵀ`, `K⁰ = X⁰ S⁰`, the K-step factorization
`K¹ = X¹ S⁽¹⁾`, `L⁰ = V⁰ S⁽²⁾ᵀ` and `f¹ = X¹ L¹ᵀ`,
`f¹ - f⁰ = ΔK V⁰ᵀ + X¹ ΔS V⁰ᵀ + X¹ ΔLᵀ`.  The columns of `K`, `L` are the paper's `K_j`, `L_i`.
This is a telescoping identity; orthonormality is not used. -/
theorem eq5_3 {X₀ X₁ K₀ K₁ : Matrix m k ℝ} {S₀ S₁ S₂ : Matrix k k ℝ} {V₀ L₀ L₁ : Matrix n k ℝ}
    (hK₀ : K₀ = X₀ * S₀) (hK₁ : K₁ = X₁ * S₁) (hL₀ : L₀ = V₀ * S₂ᵀ) :
    X₁ * L₁ᵀ - X₀ * S₀ * V₀ᵀ =
      (K₁ - K₀) * V₀ᵀ + X₁ * (S₂ - S₁) * V₀ᵀ + X₁ * (L₁ - L₀)ᵀ := by
  subst hK₀ hK₁ hL₀
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.transpose_sub, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.mul_assoc]
  abel

/-- **Eqs. (5.4)-(5.5) of arXiv 2112.02695**: if `X¹` and `V⁰` have orthonormal columns then
`‖f¹ - f⁰‖² = ∑_j ⟨ΔK_j, ΔK_j⟩ + ∑_{ij} ΔS_{ij}² + ∑_i ⟨ΔL_i, ΔL_i⟩ + I + II + III`, with
`I = 2 ∑_{ij} ⟨ΔK_j, X_i⟩ ΔS_{ij}`, `II = 2 ∑_{ij} ⟨ΔL_i, V_j⟩ ΔS_{ij}`,
`III = 2 ∑_{ij} ⟨ΔK_j, X_i⟩ ⟨ΔL_i, V_j⟩`.  Everything on the right is computed from the factors;
the cost is `factoredResidualCost`. -/
theorem eq5_4 [DecidableEq k] {X₀ X₁ K₀ K₁ : Matrix m k ℝ} {S₀ S₁ S₂ : Matrix k k ℝ}
    {V₀ L₀ L₁ : Matrix n k ℝ} (hX₁ : X₁ᵀ * X₁ = 1) (hV₀ : V₀ᵀ * V₀ = 1)
    (hK₀ : K₀ = X₀ * S₀) (hK₁ : K₁ = X₁ * S₁) (hL₀ : L₀ = V₀ * S₂ᵀ) :
    ‖X₁ * L₁ᵀ - X₀ * S₀ * V₀ᵀ‖ ^ 2 =
      ∑ j, ∑ a, (K₁ - K₀) a j ^ 2 + ∑ i, ∑ j, (S₂ - S₁) i j ^ 2 + ∑ i, ∑ b, (L₁ - L₀) b i ^ 2 +
        2 * ∑ i, ∑ j, (∑ a, (K₁ - K₀) a j * X₁ a i) * (S₂ - S₁) i j +
        2 * ∑ i, ∑ j, (∑ b, (L₁ - L₀) b i * V₀ b j) * (S₂ - S₁) i j +
        2 * ∑ i, ∑ j, (∑ a, (K₁ - K₀) a j * X₁ a i) * (∑ b, (L₁ - L₀) b i * V₀ b j) := by
  rw [eq5_3 hK₀ hK₁ hL₀]
  set dK := K₁ - K₀
  set dS := S₂ - S₁
  set dL := L₁ - L₀
  have hA : ‖dK * V₀ᵀ‖ ^ 2 = ∑ j, ∑ a, dK a j ^ 2 := by
    rw [Frobenius.norm_mul_transpose_of_orthonormal hV₀, Frobenius.norm_sq_eq_sum,
      Finset.sum_comm]
  have hB : ‖X₁ * dS * V₀ᵀ‖ ^ 2 = ∑ i, ∑ j, dS i j ^ 2 := by
    rw [Frobenius.norm_mul_transpose_of_orthonormal hV₀, Frobenius.norm_mul_of_orthonormal hX₁,
      Frobenius.norm_sq_eq_sum]
  have hC : ‖X₁ * dLᵀ‖ ^ 2 = ∑ i, ∑ b, dL b i ^ 2 := by
    rw [Frobenius.norm_mul_of_orthonormal hX₁, Frobenius.norm_sq_eq_sum]
    simp
  have hAB : ⟪dK * V₀ᵀ, X₁ * dS * V₀ᵀ⟫ = ∑ i, ∑ j, (∑ a, dK a j * X₁ a i) * dS i j := by
    rw [Frobenius.inner_mul_right, Matrix.mul_assoc (X₁ * dS), Matrix.transpose_transpose, hV₀,
      Matrix.mul_one, Frobenius.inner_mul_left', Frobenius.inner_def]
    simp [Matrix.mul_apply, mul_comm]
  have hBC : ⟪X₁ * dS * V₀ᵀ, X₁ * dLᵀ⟫ = ∑ i, ∑ j, (∑ b, dL b i * V₀ b j) * dS i j := by
    rw [Matrix.mul_assoc X₁, Frobenius.inner_mul_mul_of_orthonormal hX₁, Frobenius.inner_mul_right,
      Matrix.transpose_transpose, Frobenius.inner_def]
    simp [Matrix.mul_apply, mul_comm]
  have hAC : ⟪dK * V₀ᵀ, X₁ * dLᵀ⟫ =
      ∑ i, ∑ j, (∑ a, dK a j * X₁ a i) * (∑ b, dL b i * V₀ b j) := by
    rw [Frobenius.inner_mul_left', ← Matrix.mul_assoc, Frobenius.inner_mul_right,
      Matrix.transpose_transpose, Frobenius.inner_def]
    simp [Matrix.mul_apply, mul_comm]
  have hexp : ∀ x y z : Matrix m n ℝ, ‖x + y + z‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2 +
      2 * ⟪x, y⟫ + 2 * ⟪y, z⟫ + 2 * ⟪x, z⟫ := by
    intro x y z
    rw [@norm_add_sq_real, @norm_add_sq_real, inner_add_left]
    ring
  rw [hexp, hA, hB, hC, hAB, hBC, hAC]

/-- The number of scalar multiplications in Eqs. (5.4)-(5.5) when `⟨ΔK_j, X_i⟩` and `⟨ΔL_i, V_j⟩`
are tabulated once: `r N_x` for `∑ ⟨ΔK_j, ΔK_j⟩`, `r²` for `∑ ΔS²`, `r N_v` for `∑ ⟨ΔL_i, ΔL_i⟩`,
`r² N_x` and `r² N_v` for the two tables, and `r²` for each of `I`, `II`, `III`. -/
def factoredResidualCost (r Nx Nv : ℕ) : ℕ :=
  r * Nx + r ^ 2 + r * Nv + r ^ 2 * Nx + r ^ 2 * Nv + 3 * r ^ 2

/-- **The cost `O(r² (N_x + N_v))` of evaluating Eqs. (5.4)-(5.5) of arXiv 2112.02695**, as a
count.  The paper does not print this count: it says only that (5.4)-(5.5) must be used because
reconstructing `f` costs `O(r² N_x^d N_v^d)` (Sec. 5.1).  Lean has no machine model, so this is
bookkeeping of the formula in `eq5_4`. -/
theorem factoredResidualCost_le (r : ℕ) {Nx Nv : ℕ} (hN : 1 ≤ Nx + Nv) :
    factoredResidualCost r Nx Nv ≤ 6 * r ^ 2 * (Nx + Nv) := by
  have h1 : r ≤ r ^ 2 := Nat.le_self_pow two_ne_zero r
  have h2 : r ^ 2 ≤ r ^ 2 * (Nx + Nv) := Nat.le_mul_of_pos_right _ hN
  have h3 : r * Nx ≤ r ^ 2 * Nx := Nat.mul_le_mul_right _ h1
  have h4 : r * Nv ≤ r ^ 2 * Nv := Nat.mul_le_mul_right _ h1
  unfold factoredResidualCost
  nlinarith

end Residual

/-! ### Sec. 4.2: Gaussian moments and Maxwellians -/

section Maxwellian

open MeasureTheory ProbabilityTheory
open scoped NNReal Real

section Gaussian

variable {μ : ℝ} {s : ℝ≥0}

/-- All moments of a Gaussian are finite. -/
private lemma integrable_pow_gaussian (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal μ s) := by
  cases k with
  | zero => simp
  | succ k =>
    have h := (memLp_id_gaussianReal' (μ := μ) (v := s) ((k + 1 : ℕ) : ENNReal)
      (ENNReal.natCast_ne_top _)).integrable_norm_pow (Nat.succ_ne_zero k)
    refine (integrable_norm_iff (by fun_prop)).mp ?_
    simpa [norm_pow] using h

/-- The second moment of a Gaussian. -/
private lemma gaussian_moment_two : ∫ x, x ^ 2 ∂gaussianReal μ s = μ ^ 2 + s := by
  have h := variance_eq_sub (memLp_id_gaussianReal' (μ := μ) (v := s) 2 (by simp))
  rw [variance_id_gaussianReal] at h
  simp only [id, Pi.pow_apply, integral_id_gaussianReal] at h
  have h' : ∫ x, x ^ 2 ∂gaussianReal μ s = (s : ℝ) + μ ^ 2 := by
    rw [h]
    ring
  rw [h']
  ring

/-- The third central moment of a Gaussian vanishes. -/
private lemma gaussian_centered_cube : ∫ x, (x - μ) ^ 3 ∂gaussianReal μ s = 0 := by
  have hmap : ∫ x, (x - μ) ^ 3 ∂gaussianReal μ s = ∫ y, y ^ 3 ∂gaussianReal 0 s := by
    have h := gaussianReal_map_sub_const (μ := μ) (v := s) μ
    rw [sub_self] at h
    rw [← h, integral_map (by fun_prop) (by fun_prop)]
  have hneg : ∫ y, y ^ 3 ∂gaussianReal 0 s = -∫ y, y ^ 3 ∂gaussianReal 0 s := by
    have h := gaussianReal_map_neg (μ := (0 : ℝ)) (v := s)
    rw [neg_zero] at h
    conv_lhs => rw [← h]
    rw [integral_map (by fun_prop) (by fun_prop), ← integral_neg]
    exact integral_congr_ae (ae_of_all _ fun y => by ring)
  rw [hmap]
  linarith

/-- The third moment of a Gaussian. -/
private lemma gaussian_moment_three :
    ∫ x, x ^ 3 ∂gaussianReal μ s = μ * (μ ^ 2 + 3 * s) := by
  have h3 := integrable_pow_gaussian (μ := μ) (s := s) 3
  have h2 := integrable_pow_gaussian (μ := μ) (s := s) 2
  have h1 := integrable_pow_gaussian (μ := μ) (s := s) 1
  have hexp : ∀ x : ℝ, x ^ 3 = (x - μ) ^ 3 + (3 * μ * x ^ 2 - 3 * μ ^ 2 * x ^ 1 + μ ^ 3) := by
    intro x
    ring
  have hq1 : Integrable (fun x : ℝ => 3 * μ * x ^ 2 - 3 * μ ^ 2 * x ^ 1) (gaussianReal μ s) :=
    (h2.const_mul _).sub (h1.const_mul _)
  have hq : Integrable (fun x : ℝ => 3 * μ * x ^ 2 - 3 * μ ^ 2 * x ^ 1 + μ ^ 3)
      (gaussianReal μ s) :=
    hq1.add (integrable_const _)
  have hc : Integrable (fun x : ℝ => (x - μ) ^ 3) (gaussianReal μ s) := by
    have h : (fun x : ℝ => (x - μ) ^ 3) =
        fun x => x ^ 3 - (3 * μ * x ^ 2 - 3 * μ ^ 2 * x ^ 1 + μ ^ 3) := by
      ext x
      ring
    rw [h]
    exact h3.sub hq
  have hsplit : ∫ x, (3 * μ * x ^ 2 - 3 * μ ^ 2 * x ^ 1 + μ ^ 3) ∂gaussianReal μ s =
      3 * μ * (μ ^ 2 + s) - 3 * μ ^ 2 * μ + μ ^ 3 := by
    rw [integral_add (f := fun x : ℝ => 3 * μ * x ^ 2 - 3 * μ ^ 2 * x ^ 1)
      (g := fun _ => μ ^ 3) hq1 (integrable_const _),
      integral_sub (f := fun x : ℝ => 3 * μ * x ^ 2) (g := fun x : ℝ => 3 * μ ^ 2 * x ^ 1)
        (h2.const_mul _) (h1.const_mul _),
      integral_const_mul, integral_const_mul, gaussian_moment_two]
    simp only [pow_one, integral_id_gaussianReal, integral_const, probReal_univ, smul_eq_mul,
      one_mul]
  rw [integral_congr_ae (ae_of_all _ hexp), integral_add hc hq, gaussian_centered_cube, hsplit]
  ring

/-- A moment of a Gaussian as a Lebesgue integrand. -/
private lemma integrable_pdf_mul_pow (hs : s ≠ 0) (k : ℕ) :
    Integrable (fun z : ℝ => gaussianPDFReal μ s z * z ^ k) := by
  have h := integrable_pow_gaussian (μ := μ) (s := s) k
  rw [gaussianReal_of_var_ne_zero _ hs, integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF μ s) (ae_of_all _ fun _ => gaussianPDF_lt_top)] at h
  refine h.congr (ae_of_all _ fun z => ?_)
  simp [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg μ s z)]

/-- A moment of a Gaussian as a Lebesgue integral. -/
private lemma integral_pdf_mul_pow (hs : s ≠ 0) (k : ℕ) :
    ∫ z : ℝ, gaussianPDFReal μ s z * z ^ k = ∫ z, z ^ k ∂gaussianReal μ s := by
  rw [integral_gaussianReal_eq_integral_smul hs]
  rfl

end Gaussian

variable {ι : Type*} [Fintype ι]

/-- **The Maxwellian of arXiv 2112.02695**:
`M(ρ, u, T)(v) = ρ (2 π R T)^{-d/2} exp(-|v - u|² / (2 R T))` in dimension `d = card ι`. -/
noncomputable def maxwellian (R ρ T : ℝ) (u v : EuclideanSpace ℝ ι) : ℝ :=
  ρ / (2 * π * R * T) ^ ((Fintype.card ι : ℝ) / 2) * Real.exp (-‖v - u‖ ^ 2 / (2 * R * T))

/-- A Maxwellian is a product of one-dimensional Gaussian densities. -/
private lemma maxwellian_eq_prod {R ρ T : ℝ} (hθ : 0 < R * T) (u v : EuclideanSpace ℝ ι) :
    maxwellian R ρ T u v = ρ * ∏ i, gaussianPDFReal (u i) (R * T).toNNReal (v i) := by
  have hs : (((R * T).toNNReal : ℝ≥0) : ℝ) = R * T := Real.coe_toNNReal _ hθ.le
  have h1 : (2 * π * R * T) ^ ((Fintype.card ι : ℝ) / 2) =
      √(2 * π * (R * T)) ^ Fintype.card ι := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    · ring
    · ring
  have h2 : -‖v - u‖ ^ 2 / (2 * R * T) = ∑ i, -(v i - u i) ^ 2 / (2 * (R * T)) := by
    rw [EuclideanSpace.real_norm_sq_eq, ← Finset.sum_div, ← Finset.sum_neg_distrib]
    simp only [PiLp.sub_apply]
    congr 1
    ring
  simp only [gaussianPDFReal, hs, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rw [maxwellian, h1, h2, Real.exp_sum, div_eq_mul_inv, inv_pow, mul_assoc]

/-- The density of a coordinate moment of a Maxwellian, as a product over the coordinates. -/
private lemma moment_eq_prod {R ρ T : ℝ} (hθ : 0 < R * T) (u : EuclideanSpace ℝ ι) [DecidableEq ι]
    (i₀ : ι) (k : ℕ) (v : EuclideanSpace ℝ ι) :
    v i₀ ^ k * maxwellian R ρ T u v =
      ρ * ∏ i, (gaussianPDFReal (u i) (R * T).toNNReal (v i) *
        (if i = i₀ then v i ^ k else 1)) := by
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ i₀ fun i => v i ^ k,
    maxwellian_eq_prod hθ]
  simp only [Finset.mem_univ, ite_true]
  ring

/-- **Sec. 4.2 of arXiv 2112.02695**: coordinate moments of a Maxwellian are integrable. -/
theorem integrable_moment {R T : ℝ} (hθ : 0 < R * T) (ρ : ℝ) (u : EuclideanSpace ℝ ι)
    (i₀ : ι) (k : ℕ) :
    Integrable (fun v : EuclideanSpace ℝ ι => v i₀ ^ k * maxwellian R ρ T u v) := by
  classical
  have hs : (R * T).toNNReal ≠ 0 := by simpa using hθ
  have hint : ∀ i, Integrable (fun z : ℝ => gaussianPDFReal (u i) (R * T).toNNReal z *
      (if i = i₀ then z ^ k else 1)) := by
    intro i
    by_cases hi : i = i₀
    · simpa [hi] using integrable_pdf_mul_pow (μ := u i₀) hs k
    · simpa [hi] using integrable_gaussianPDFReal (u i) (R * T).toNNReal
  have hF : Integrable (fun x : ι → ℝ => ρ * ∏ i, (gaussianPDFReal (u i) (R * T).toNNReal (x i) *
      (if i = i₀ then x i ^ k else 1))) :=
    (Integrable.fintype_prod (f := fun i z => gaussianPDFReal (u i) (R * T).toNNReal z *
      (if i = i₀ then z ^ k else 1)) hint).const_mul ρ
  have hemb := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _) |>.mpr hF
  refine hemb.congr (ae_of_all _ fun v => ?_)
  exact (moment_eq_prod hθ u i₀ k v).symm

/-- **Sec. 4.2 of arXiv 2112.02695**: a coordinate moment of a Maxwellian is one Gaussian moment. -/
theorem integral_moment {R T : ℝ} (hθ : 0 < R * T) (ρ : ℝ) (u : EuclideanSpace ℝ ι) (i₀ : ι)
    (k : ℕ) :
    ∫ v : EuclideanSpace ℝ ι, v i₀ ^ k * maxwellian R ρ T u v =
      ρ * ∫ z, z ^ k ∂gaussianReal (u i₀) (R * T).toNNReal := by
  classical
  have hs : (R * T).toNNReal ≠ 0 := by simpa using hθ
  have h1 := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι).integral_comp'
    (fun x : ι → ℝ => ρ * ∏ i, (gaussianPDFReal (u i) (R * T).toNNReal (x i) *
      (if i = i₀ then x i ^ k else 1)))
  have h2 : ∫ v : EuclideanSpace ℝ ι, v i₀ ^ k * maxwellian R ρ T u v =
      ∫ x : ι → ℝ, ρ * ∏ i, (gaussianPDFReal (u i) (R * T).toNNReal (x i) *
        (if i = i₀ then x i ^ k else 1)) := by
    rw [← h1]
    exact integral_congr_ae (ae_of_all _ fun v => moment_eq_prod hθ u i₀ k v)
  rw [h2, integral_const_mul, integral_fintype_prod_volume_eq_prod
    (fun i z => gaussianPDFReal (u i) (R * T).toNNReal z * (if i = i₀ then z ^ k else 1)),
    Finset.prod_eq_single i₀]
  · simp only [ite_true]
    rw [integral_pdf_mul_pow hs]
  · intro i _ hi
    simpa [hi] using integral_gaussianPDFReal_eq_one (u i) hs
  · simp

/-- **Sec. 4.2 of arXiv 2112.02695**: the density of a Maxwellian, `∫ M(ρ, u, T) dv = ρ`. -/
theorem integral_maxwellian {R T : ℝ} (hθ : 0 < R * T) [Nonempty ι] (ρ : ℝ)
    (u : EuclideanSpace ℝ ι) : ∫ v : EuclideanSpace ℝ ι, maxwellian R ρ T u v = ρ := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have h := integral_moment hθ ρ u i₀ 0
  simpa using h

/-- **Sec. 4.2 of arXiv 2112.02695**: the mass flux of a Maxwellian, `∫ v₁ M(ρ, u, T) dv = ρ u₁`. -/
theorem integral_flux_maxwellian {R T : ℝ} (hθ : 0 < R * T) (ρ : ℝ) (u : EuclideanSpace ℝ ι)
    (i₀ : ι) : ∫ v : EuclideanSpace ℝ ι, v i₀ * maxwellian R ρ T u v = ρ * u i₀ := by
  have h := integral_moment hθ ρ u i₀ 1
  simpa using h

/-- The third moment in Eq. (4.19) of arXiv 2112.02695:
`∫ v₁³ M(ρ, u, T) dv = ρ u₁ (u₁² + 3 R T)`. -/
theorem integral_cube_maxwellian {R T : ℝ} (hθ : 0 < R * T) (ρ : ℝ) (u : EuclideanSpace ℝ ι)
    (i₀ : ι) :
    ∫ v : EuclideanSpace ℝ ι, v i₀ ^ 3 * maxwellian R ρ T u v =
      ρ * u i₀ * (u i₀ ^ 2 + 3 * R * T) := by
  rw [integral_moment hθ ρ u i₀ 3, gaussian_moment_three, Real.coe_toNNReal _ hθ.le]
  ring


/-! ### Eq. (1.2): the collision operator, and `Q(M, M) = 0` -/

/-- The post-collisional velocity `v' = (v + v_*)/2 + |v - v_*| σ / 2`. -/
noncomputable def postVel (v w σ : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  (1 / 2 : ℝ) • (v + w) + (‖v - w‖ / 2) • σ

/-- The post-collisional velocity `v_*' = (v + v_*)/2 - |v - v_*| σ / 2`. -/
noncomputable def postVelStar (v w σ : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  (1 / 2 : ℝ) • (v + w) - (‖v - w‖ / 2) • σ

/-- The integrand `B(|v - v_*|, cos χ) (g(v_*') f(v') - g(v_*) f(v))` of Eq. (1.2) at
`z = (v_*, σ)`, with `cos χ = σ · (v - v_*) / |v - v_*|`. -/
noncomputable def collisionIntegrand (B : ℝ → ℝ → ℝ) (g f : EuclideanSpace ℝ ι → ℝ)
    (v : EuclideanSpace ℝ ι)
    (z : EuclideanSpace ℝ ι × Metric.sphere (0 : EuclideanSpace ℝ ι) 1) : ℝ :=
  B ‖v - z.1‖ (⟪(z.2 : EuclideanSpace ℝ ι), v - z.1⟫ / ‖v - z.1‖) *
    (g (postVelStar v z.1 z.2) * f (postVel v z.1 z.2) - g z.1 * f v)

/-- The measure `dv_* dσ` on `ℝ^d × S^{d-1}`. -/
noncomputable def collisionMeasure :
    Measure (EuclideanSpace ℝ ι × Metric.sphere (0 : EuclideanSpace ℝ ι) 1) :=
  (volume : Measure (EuclideanSpace ℝ ι)).prod (volume : Measure (EuclideanSpace ℝ ι)).toSphere

/-- **Eq. (1.2) of arXiv 2112.02695**: the collision operator with kernel `B`, as one integral over
`ℝ^d × S^{d-1}` (equal to the paper's iterated integral on integrable integrands). -/
noncomputable def collisionQ (B : ℝ → ℝ → ℝ) (g f : EuclideanSpace ℝ ι → ℝ)
    (v : EuclideanSpace ℝ ι) : ℝ :=
  ∫ z, collisionIntegrand B g f v z ∂collisionMeasure

/-- Collisions conserve the kinetic energy relative to any `u`. -/
private lemma post_energy (v w u : EuclideanSpace ℝ ι) {σ : EuclideanSpace ℝ ι} (hσ : ‖σ‖ = 1) :
    ‖postVelStar v w σ - u‖ ^ 2 + ‖postVel v w σ - u‖ ^ 2 = ‖w - u‖ ^ 2 + ‖v - u‖ ^ 2 := by
  set c : EuclideanSpace ℝ ι := (1 / 2 : ℝ) • (v + w) - u
  set d : EuclideanSpace ℝ ι := (‖v - w‖ / 2) • σ
  set e : EuclideanSpace ℝ ι := (1 / 2 : ℝ) • (v - w)
  have h1 : postVel v w σ - u = c + d := by
    simp only [postVel, c, d]
    abel
  have h2 : postVelStar v w σ - u = c - d := by
    simp only [postVelStar, c, d]
    abel
  have h3 : v - u = c + e := by
    simp only [c, e, smul_add, smul_sub]
    have : v = (1 / 2 : ℝ) • v + (1 / 2 : ℝ) • v := by
      rw [← add_smul]
      norm_num
    nth_rw 1 [this]
    abel
  have h4 : w - u = c - e := by
    simp only [c, e, smul_add, smul_sub]
    have : w = (1 / 2 : ℝ) • w + (1 / 2 : ℝ) • w := by
      rw [← add_smul]
      norm_num
    nth_rw 1 [this]
    abel
  have hd : ‖d‖ = ‖v - w‖ / 2 := by
    simp only [d, norm_smul, hσ, mul_one, norm_div, Real.norm_eq_abs, abs_norm]
    norm_num
  have he : ‖e‖ = ‖v - w‖ / 2 := by
    simp only [e, norm_smul, Real.norm_eq_abs]
    norm_num
    ring
  have p1 := parallelogram_law_with_norm ℝ c d
  have p2 := parallelogram_law_with_norm ℝ c e
  rw [hd] at p1
  rw [he] at p2
  rw [h1, h2, h3, h4]
  linarith

/-- **Detailed balance of a Maxwellian** (behind Eq. (4.19) of arXiv 2112.02695):
`M(v_*') M(v') = M(v_*) M(v)`. -/
theorem maxwellian_mul_post (R ρ T : ℝ) (u v w : EuclideanSpace ℝ ι) {σ : EuclideanSpace ℝ ι}
    (hσ : ‖σ‖ = 1) :
    maxwellian R ρ T u (postVelStar v w σ) * maxwellian R ρ T u (postVel v w σ) =
      maxwellian R ρ T u w * maxwellian R ρ T u v := by
  simp only [maxwellian]
  have hE := post_energy v w u hσ
  have hexp : Real.exp (-‖postVelStar v w σ - u‖ ^ 2 / (2 * R * T)) *
      Real.exp (-‖postVel v w σ - u‖ ^ 2 / (2 * R * T)) =
      Real.exp (-‖w - u‖ ^ 2 / (2 * R * T)) * Real.exp (-‖v - u‖ ^ 2 / (2 * R * T)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [← add_div, ← add_div]
    congr 1
    linarith
  calc _ = (ρ / (2 * π * R * T) ^ ((Fintype.card ι : ℝ) / 2)) ^ 2 *
        (Real.exp (-‖postVelStar v w σ - u‖ ^ 2 / (2 * R * T)) *
          Real.exp (-‖postVel v w σ - u‖ ^ 2 / (2 * R * T))) := by ring
    _ = _ := by
      rw [hexp]
      ring

/-- **`Q(M, M) = 0` for every Maxwellian and every kernel.**  The paper uses this for Eq. (4.19);
here it is derived from Eq. (1.2) and needs no integrability. -/
theorem collisionQ_maxwellian (B : ℝ → ℝ → ℝ) (R ρ T : ℝ) (u v : EuclideanSpace ℝ ι) :
    collisionQ B (maxwellian R ρ T u) (maxwellian R ρ T u) v = 0 := by
  have h : ∀ z, collisionIntegrand B (maxwellian R ρ T u) (maxwellian R ρ T u) v z = 0 := by
    intro z
    have hσ : ‖(z.2 : EuclideanSpace ℝ ι)‖ = 1 := by simp
    rw [collisionIntegrand, maxwellian_mul_post R ρ T u v z.1 hσ, sub_self, mul_zero]
  simp [collisionQ, h]

/-! ### Eqs. (4.17)-(4.21): the Mott-Smith ansatz -/

/-- **Eq. (4.17) of arXiv 2112.02695**: the bimodal ansatz
`f(x, v) = a(x) f_L(v) + (1 - a(x)) f_R(v)`, of rank two in `(x, v)`. -/
def ansatz (a : ℝ → ℝ) (fL fR : EuclideanSpace ℝ ι → ℝ) (x : ℝ) (v : EuclideanSpace ℝ ι) : ℝ :=
  a x * fL v + (1 - a x) * fR v

/-- **Eq. (4.20) of arXiv 2112.02695**: `α = ∫ v₁² (Q(f_L, f_R) + Q(f_R, f_L)) dv`. -/
noncomputable def shockAlpha (B : ℝ → ℝ → ℝ) (fL fR : EuclideanSpace ℝ ι → ℝ) (i₀ : ι) : ℝ :=
  ∫ v : EuclideanSpace ℝ ι, v i₀ ^ 2 * (collisionQ B fL fR v + collisionQ B fR fL v)

/-- **The right-hand side of Eq. (4.19) of arXiv 2112.02695**: since `Q` of (1.2) is bilinear on
convergent integrands and `Q(M, M) = 0`, the ansatz gives
`Q(f, f) = a (1 - a) (Q(f_L, f_R) + Q(f_R, f_L))`. -/
theorem collisionQ_ansatz (B : ℝ → ℝ → ℝ) {R ρL TL ρR TR : ℝ} {uL uR : EuclideanSpace ℝ ι}
    (a : ℝ → ℝ) (x : ℝ) (v : EuclideanSpace ℝ ι)
    (hLR : Integrable (collisionIntegrand B (maxwellian R ρL TL uL) (maxwellian R ρR TR uR) v)
      collisionMeasure)
    (hRL : Integrable (collisionIntegrand B (maxwellian R ρR TR uR) (maxwellian R ρL TL uL) v)
      collisionMeasure) :
    collisionQ B (ansatz a (maxwellian R ρL TL uL) (maxwellian R ρR TR uR) x)
        (ansatz a (maxwellian R ρL TL uL) (maxwellian R ρR TR uR) x) v =
      a x * (1 - a x) * (collisionQ B (maxwellian R ρL TL uL) (maxwellian R ρR TR uR) v +
        collisionQ B (maxwellian R ρR TR uR) (maxwellian R ρL TL uL) v) := by
  set fL := maxwellian R ρL TL uL with hfL
  set fR := maxwellian R ρR TR uR with hfR
  have hpt : ∀ z, collisionIntegrand B (ansatz a fL fR x) (ansatz a fL fR x) v z =
      a x * (1 - a x) * (collisionIntegrand B fL fR v z + collisionIntegrand B fR fL v z) := by
    intro z
    have hσ : ‖(z.2 : EuclideanSpace ℝ ι)‖ = 1 := by simp
    have hL := maxwellian_mul_post R ρL TL uL v z.1 hσ
    have hR := maxwellian_mul_post R ρR TR uR v z.1 hσ
    simp only [collisionIntegrand, ansatz]
    rw [← hfL] at hL
    rw [← hfR] at hR
    set bb := B ‖v - z.1‖ (⟪(z.2 : EuclideanSpace ℝ ι), v - z.1⟫ / ‖v - z.1‖)
    linear_combination bb * (a x) ^ 2 * hL + bb * (1 - a x) ^ 2 * hR
  simp only [collisionQ]
  rw [integral_congr_ae (ae_of_all _ hpt), integral_const_mul, integral_add hLR hRL]

/-- The Maxwellian `M(ρ, u e₁, T)` of a far-field state, with `e₁` the unit vector of the index
`i₀`. -/
noncomputable abbrev shockState [DecidableEq ι] (R ρ T u : ℝ) (i₀ : ι) :
    EuclideanSpace ℝ ι → ℝ :=
  maxwellian R ρ T (EuclideanSpace.single i₀ u)

/-- The transport side of the moment equation. -/
private lemma transport_moment [DecidableEq ι] {R ρL TL ρR TR uL uR : ℝ} (hL : 0 < R * TL)
    (hR : 0 < R * TR) (i₀ : ι) {a : ℝ → ℝ} {x : ℝ} (ha : DifferentiableAt ℝ a x) :
    ∫ v : EuclideanSpace ℝ ι, v i₀ ^ 2 * (v i₀ * deriv (fun y =>
        ansatz a (shockState R ρL TL uL i₀)
          (shockState R ρR TR uR i₀) y v) x) =
      deriv a x * (ρL * uL * (uL ^ 2 + 3 * R * TL) - ρR * uR * (uR ^ 2 + 3 * R * TR)) := by
  set fL := shockState R ρL TL uL i₀ with hfL
  set fR := shockState R ρR TR uR i₀ with hfR
  have hd : ∀ v, deriv (fun y => ansatz a fL fR y v) x = deriv a x * (fL v - fR v) := by
    intro v
    have h : HasDerivAt (fun y => a y * fL v + (1 - a y) * fR v)
        (deriv a x * fL v + (-deriv a x) * fR v) x :=
      (ha.hasDerivAt.mul_const _).add
        (((hasDerivAt_const x (1 : ℝ)).sub ha.hasDerivAt).mul_const _ |>.congr_deriv (by simp))
    have h' := h.deriv
    simp only [ansatz]
    rw [h']
    ring
  have h1 : Integrable (fun v : EuclideanSpace ℝ ι => v i₀ ^ 3 * fL v) :=
    integrable_moment hL ρL _ i₀ 3
  have h2 : Integrable (fun v : EuclideanSpace ℝ ι => v i₀ ^ 3 * fR v) :=
    integrable_moment hR ρR _ i₀ 3
  have hpt : ∀ v : EuclideanSpace ℝ ι, v i₀ ^ 2 * (v i₀ * deriv (fun y => ansatz a fL fR y v) x) =
      deriv a x * (v i₀ ^ 3 * fL v - v i₀ ^ 3 * fR v) := by
    intro v
    rw [hd]
    ring
  rw [integral_congr_ae (ae_of_all _ hpt), integral_const_mul, integral_sub h1 h2, hfL, hfR,
    integral_cube_maxwellian hL, integral_cube_maxwellian hR]
  simp

/-- **Eqs. (4.18)-(4.19) of arXiv 2112.02695.**  For the Maxwellian states
`f_L = M(ρ_L, u_L e₁, T_L)`, `f_R = M(ρ_R, u_R e₁, T_R)` and the collision operator (1.2) with any
kernel such that the two integrals `Q(f_L, f_R)`, `Q(f_R, f_L)` converge, the `v₁²` moment of the
steady equation `v₁ ∂ₓ f = Q(f, f)` for the ansatz is, at every `x` where `a` is differentiable,
exactly
`a' (ρ_L u_L (u_L² + 3 R T_L) - ρ_R u_R (u_R² + 3 R T_R)) = α a (1 - a)`.
The moments are computed from the Maxwellians, and `Q(M, M) = 0` from (1.2). -/
theorem eq4_19 [DecidableEq ι] (B : ℝ → ℝ → ℝ) {R ρL TL ρR TR uL uR : ℝ} (hL : 0 < R * TL)
    (hR : 0 < R * TR) (i₀ : ι)
    (hLR : ∀ v, Integrable (collisionIntegrand B
      (shockState R ρL TL uL i₀)
      (shockState R ρR TR uR i₀) v) collisionMeasure)
    (hRL : ∀ v, Integrable (collisionIntegrand B
      (shockState R ρR TR uR i₀)
      (shockState R ρL TL uL i₀) v) collisionMeasure)
    {a : ℝ → ℝ} {x : ℝ} (ha : DifferentiableAt ℝ a x) :
    (∫ v : EuclideanSpace ℝ ι, v i₀ ^ 2 * (v i₀ * deriv (fun y =>
        ansatz a (shockState R ρL TL uL i₀)
          (shockState R ρR TR uR i₀) y v) x) =
      ∫ v : EuclideanSpace ℝ ι, v i₀ ^ 2 * collisionQ B
        (ansatz a (shockState R ρL TL uL i₀)
          (shockState R ρR TR uR i₀) x)
        (ansatz a (shockState R ρL TL uL i₀)
          (shockState R ρR TR uR i₀) x) v) ↔
      deriv a x * (ρL * uL * (uL ^ 2 + 3 * R * TL) - ρR * uR * (uR ^ 2 + 3 * R * TR)) =
        shockAlpha B (shockState R ρL TL uL i₀)
          (shockState R ρR TR uR i₀) i₀ * (a x * (1 - a x)) := by
  rw [transport_moment hL hR i₀ ha]
  have hc : ∀ v : EuclideanSpace ℝ ι, v i₀ ^ 2 * collisionQ B
      (ansatz a (shockState R ρL TL uL i₀)
        (shockState R ρR TR uR i₀) x)
      (ansatz a (shockState R ρL TL uL i₀)
        (shockState R ρR TR uR i₀) x) v =
      a x * (1 - a x) * (v i₀ ^ 2 * (collisionQ B
        (shockState R ρL TL uL i₀)
        (shockState R ρR TR uR i₀) v + collisionQ B
        (shockState R ρR TR uR i₀)
        (shockState R ρL TL uL i₀) v)) := by
    intro v
    rw [collisionQ_ansatz B a x v (hLR v) (hRL v)]
    ring
  rw [integral_congr_ae (ae_of_all _ hc), integral_const_mul, shockAlpha, mul_comm (∫ _, _)]


/-! ### Eqs. (4.4), (4.6): the Rankine-Hugoniot relations -/

/-- **Eq. (4.4) of arXiv 2112.02695**: the Rankine-Hugoniot relations in dimension `d`. -/
structure IsRankineHugoniot (d R ρL uL TL ρR uR TR : ℝ) : Prop where
  mass : ρL * uL = ρR * uR
  momentum : ρL * uL ^ 2 + ρL * R * TL = ρR * uR ^ 2 + ρR * R * TR
  energy : ρL * uL * (uL ^ 2 + (d + 2) * R * TL) = ρR * uR * (uR ^ 2 + (d + 2) * R * TR)

/-- The upstream Mach number `M_L = u_L / (γ R T_L)^{1/2}` with `γ = (d + 2) / d`. -/
noncomputable def machL (d R uL TL : ℝ) : ℝ := uL / √((d + 2) / d * R * TL)

/-- The square of the Mach number. -/
private lemma machL_sq {d R uL TL : ℝ} (hd : 0 < d) (hR : 0 < R) (hT : 0 < TL) :
    machL d R uL TL ^ 2 = d * uL ^ 2 / ((d + 2) * (R * TL)) := by
  rw [machL, div_pow, Real.sq_sqrt (by positivity)]
  field_simp

/-- **The nontrivial branch of the Rankine-Hugoniot relations**, from (4.4): `(d + 1) u_L u_R` is
`u_L² + (d + 2) R T_L`, and the energy flux per unit mass is continuous. -/
private lemma IsRankineHugoniot.key {d R ρL uL TL ρR uR TR : ℝ}
    (h : IsRankineHugoniot d R ρL uL TL ρR uR TR) (hm : ρL * uL ≠ 0) (hne : uR ≠ uL) :
    (d + 1) * uL * uR = uL ^ 2 + (d + 2) * (R * TL) ∧
      uL ^ 2 + (d + 2) * (R * TL) = uR ^ 2 + (d + 2) * (R * TR) := by
  have hE : uL ^ 2 + (d + 2) * (R * TL) = uR ^ 2 + (d + 2) * (R * TR) := by
    apply mul_left_cancel₀ hm
    linear_combination h.energy - (uR ^ 2 + (d + 2) * (R * TR)) * h.mass
  have hM : ρL * uL * (uL ^ 2 * uR + R * TL * uR - uR ^ 2 * uL - R * TR * uL) = 0 := by
    linear_combination (uL * uR) * h.momentum - (uL * uR ^ 2 + uL * (R * TR)) * h.mass
  have hM' : uL ^ 2 * uR + R * TL * uR - uR ^ 2 * uL - R * TR * uL = 0 :=
    (mul_eq_zero.mp hM).resolve_left hm
  refine ⟨?_, hE⟩
  have hfac : (uR - uL) * ((d + 1) * uL * uR - (uL ^ 2 + (d + 2) * (R * TL))) = 0 := by
    linear_combination (-(d + 2)) * hM' + uL * hE
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hne))

/-- **Eq. (4.6) of arXiv 2112.02695**: on the nontrivial branch `u_R ≠ u_L` of (4.4),
`ρ_R = ρ_L (d + 1) M_L² / (M_L² + d)`, `u_R = u_L (M_L² + d) / ((d + 1) M_L²)` and
`T_R = T_L ((d + 2) M_L² - 1)(M_L² + d) / ((d + 1)² M_L²)`. -/
theorem eq4_6 {d R ρL uL TL ρR uR TR : ℝ} (hd : 0 < d) (hR : 0 < R) (hρ : 0 < ρL) (hu : uL ≠ 0)
    (hT : 0 < TL) (h : IsRankineHugoniot d R ρL uL TL ρR uR TR) (hne : uR ≠ uL) :
    ρR = ρL * ((d + 1) * machL d R uL TL ^ 2 / (machL d R uL TL ^ 2 + d)) ∧
      uR = uL * ((machL d R uL TL ^ 2 + d) / ((d + 1) * machL d R uL TL ^ 2)) ∧
      TR = TL * (((d + 2) * machL d R uL TL ^ 2 - 1) * (machL d R uL TL ^ 2 + d) /
        ((d + 1) ^ 2 * machL d R uL TL ^ 2)) := by
  have hm : ρL * uL ≠ 0 := mul_ne_zero hρ.ne' hu
  obtain ⟨hk, hE⟩ := h.key hm hne
  have hM := machL_sq (uL := uL) hd hR hT
  set m2 := machL d R uL TL ^ 2
  have hθ : 0 < R * TL := mul_pos hR hT
  have hm2 : 0 < m2 := by
    rw [hM]
    positivity
  have huR : uR = uL * ((m2 + d) / ((d + 1) * m2)) := by
    have h1 : (d + 1) * uL ≠ 0 := mul_ne_zero (by positivity) hu
    apply mul_left_cancel₀ h1
    rw [hk, hM]
    field_simp
  have huR0 : uR ≠ 0 := by
    intro h0
    apply hm
    rw [h.mass, h0, mul_zero]
  refine ⟨?_, huR, ?_⟩
  · have h1 : ρR = ρL * uL / uR := by
      rw [h.mass]
      field_simp
    rw [h1, huR]
    field_simp
  · have h1 : R * TR = (uL ^ 2 + (d + 2) * (R * TL) - uR ^ 2) / (d + 2) := by
      rw [hE]
      field_simp
      ring
    apply mul_left_cancel₀ hR.ne'
    rw [h1, huR, hM]
    field_simp
    ring

/-- **Converse of Eq. (4.6) of arXiv 2112.02695**: the states (4.6) satisfy (4.4), for every Mach
number, so the relations and the hypotheses of `eq4_6` are satisfiable.  For `M_L² ≠ 1` the branch
is nontrivial. -/
theorem isRankineHugoniot_of_mach {d R ρL uL TL : ℝ} (hd : 0 < d) (hR : 0 < R) (hu : uL ≠ 0)
    (hT : 0 < TL) (hM : machL d R uL TL ^ 2 ≠ 1) :
    IsRankineHugoniot d R ρL uL TL
        (ρL * ((d + 1) * machL d R uL TL ^ 2 / (machL d R uL TL ^ 2 + d)))
        (uL * ((machL d R uL TL ^ 2 + d) / ((d + 1) * machL d R uL TL ^ 2)))
        (TL * (((d + 2) * machL d R uL TL ^ 2 - 1) * (machL d R uL TL ^ 2 + d) /
          ((d + 1) ^ 2 * machL d R uL TL ^ 2))) ∧
      uL * ((machL d R uL TL ^ 2 + d) / ((d + 1) * machL d R uL TL ^ 2)) ≠ uL := by
  have hMs := machL_sq (uL := uL) hd hR hT
  set m2 := machL d R uL TL ^ 2 with hm2def
  have hθ : 0 < R * TL := mul_pos hR hT
  have hm2 : 0 < m2 := by
    rw [hMs]
    positivity
  have hθe : R * TL = d * uL ^ 2 / ((d + 2) * m2) := by
    rw [hMs]
    field_simp
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · field_simp
  · have hTL : TL = d * uL ^ 2 / ((d + 2) * m2) / R := by
      rw [← hθe]
      field_simp
    rw [hTL]
    field_simp
    ring
  · have hTL : TL = d * uL ^ 2 / ((d + 2) * m2) / R := by
      rw [← hθe]
      field_simp
    rw [hTL]
    field_simp
    ring
  · intro heq
    have h1 : (m2 + d) / ((d + 1) * m2) = 1 := mul_left_cancel₀ hu (by rw [heq, mul_one])
    rw [div_eq_one_iff_eq (by positivity)] at h1
    apply hM
    have : d * (m2 - 1) = 0 := by linear_combination -h1
    have h2 := (mul_eq_zero.mp this).resolve_left hd.ne'
    linarith

/-- **Eq. (4.22) of arXiv 2112.02695, well-definedness**: the temperature jump on the nontrivial
branch of (4.4) is nonzero, so `β` is well defined in dimension `d ≠ 1`. -/
theorem temperature_jump_ne_zero {d R ρL uL TL ρR uR TR : ℝ} (hd : 0 < d) (hR : 0 < R)
    (hρ : 0 < ρL) (hu : uL ≠ 0) (hT : 0 < TL) (h : IsRankineHugoniot d R ρL uL TL ρR uR TR)
    (hne : uR ≠ uL) : TL ≠ TR := by
  obtain ⟨-, hu2, hT2⟩ := eq4_6 hd hR hρ hu hT h hne
  have hMs := machL_sq (uL := uL) hd hR hT
  set m2 := machL d R uL TL ^ 2
  have hθ : 0 < R * TL := mul_pos hR hT
  have hm2 : 0 < m2 := by
    rw [hMs]
    positivity
  intro heq
  apply hne
  have h1 : ((d + 2) * m2 - 1) * (m2 + d) / ((d + 1) ^ 2 * m2) = 1 := by
    apply mul_left_cancel₀ hT.ne'
    rw [mul_one, ← hT2, heq]
  rw [div_eq_one_iff_eq (by positivity)] at h1
  have h2 : (m2 - 1) * ((d + 2) * m2 + d) = 0 := by linear_combination h1
  have h3 : m2 = 1 := by
    have := (mul_eq_zero.mp h2).resolve_right (by positivity)
    linarith
  rw [hu2, h3]
  field_simp
  ring

/-- **From Eq. (4.19) to Eq. (4.21) of arXiv 2112.02695**, by the mass and energy relations:
`ρ_L u_L (u_L² + 3 R T_L) - ρ_R u_R (u_R² + 3 R T_R) = -(d - 1) ρ_L u_L R (T_L - T_R)`. -/
theorem flux_difference {d R ρL uL TL ρR uR TR : ℝ}
    (h : IsRankineHugoniot d R ρL uL TL ρR uR TR) :
    ρL * uL * (uL ^ 2 + 3 * R * TL) - ρR * uR * (uR ^ 2 + 3 * R * TR) =
      -((d - 1) * ρL * uL * R * (TL - TR)) := by
  linear_combination h.energy - (d - 1) * R * TR * h.mass

/-! ### Eq. (4.22): the logistic profile -/

/-- **Eq. (4.22) of arXiv 2112.02695**: `a(x) = 1 / (exp(β x) + 1)`. -/
noncomputable def logistic (β x : ℝ) : ℝ := 1 / (Real.exp (β * x) + 1)

/-- **Eq. (4.22) of arXiv 2112.02695**: the profile solves the logistic equation
`a' = -β a (1 - a)`. -/
theorem hasDerivAt_logistic (β x : ℝ) :
    HasDerivAt (logistic β) (-β * (logistic β x * (1 - logistic β x))) x := by
  have hE : HasDerivAt (fun y => Real.exp (β * y) + 1) (Real.exp (β * x) * β) x := by
    have h := ((hasDerivAt_id x).const_mul β).exp
    simp only [id, mul_one] at h
    exact h.add_const 1
  have hpos : Real.exp (β * x) + 1 ≠ 0 := by positivity
  have h := (hasDerivAt_const x (1 : ℝ)).div hE hpos
  refine (h.congr_deriv ?_)
  simp only [logistic]
  field_simp
  ring

/-- **Uniqueness in Eq. (4.22) of arXiv 2112.02695**: a solution on all of `ℝ` of
`a' = -β a (1 - a)` with `a(x₀) = 1/2` is `1 / (exp(β (x - x₀)) + 1)`.  The equation is invariant
under translation, and the paper's solution is the one centered at `x₀ = 0`. -/
theorem logistic_unique {a : ℝ → ℝ} {β x₀ : ℝ}
    (ha : ∀ x, HasDerivAt a (-β * (a x * (1 - a x))) x) (h0 : a x₀ = 1 / 2) (x : ℝ) :
    a x = logistic β (x - x₀) := by
  have hcont : Continuous a :=
    continuous_iff_continuousAt.mpr fun x => (ha x).continuousAt
  have hA : ∀ y, HasDerivAt (fun u => ∫ s in x₀..u, β * a s) (β * a y) y := fun y =>
    ((continuous_const.mul hcont).integral_hasStrictDerivAt x₀ y).hasDerivAt
  have hE : ∀ y, HasDerivAt (fun y => Real.exp (β * (y - x₀)))
      (Real.exp (β * (y - x₀)) * β) y := by
    intro y
    have h := (((hasDerivAt_id y).sub_const x₀).const_mul β).exp
    simpa using h
  set h : ℝ → ℝ := fun y => (1 - a y) - Real.exp (β * (y - x₀)) * a y with hh
  have hderiv : ∀ y, HasDerivAt h (β * a y * h y) y := by
    intro y
    have h1 := ((hasDerivAt_const y (1 : ℝ)).sub (ha y)).sub ((hE y).mul (ha y))
    refine h1.congr_deriv ?_
    change _ = β * a y * ((1 - a y) - Real.exp (β * (y - x₀)) * a y)
    ring
  set G : ℝ → ℝ := fun y => h y * Real.exp (-∫ s in x₀..y, β * a s) with hG
  have hGd : ∀ y, HasDerivAt G 0 y := by
    intro y
    have h1 := (hderiv y).mul ((hA y).neg.exp)
    refine h1.congr_deriv ?_
    ring
  have hconst : G x = G x₀ :=
    is_const_of_deriv_eq_zero (fun y => (hGd y).differentiableAt) (fun y => (hGd y).deriv) x x₀
  have hG0 : G x₀ = 0 := by
    simp only [hG, hh, h0, sub_self, mul_zero, Real.exp_zero, intervalIntegral.integral_same,
      neg_zero]
    norm_num
  have hx : h x = 0 := by
    have hG1 : G x = 0 := hconst.trans hG0
    exact (mul_eq_zero.mp hG1).resolve_right (Real.exp_ne_zero _)
  have hpos : Real.exp (β * (x - x₀)) + 1 ≠ 0 := by positivity
  simp only [hh] at hx
  rw [logistic, eq_div_iff hpos]
  linear_combination -hx

/-- **Far field of Eq. (4.22) of arXiv 2112.02695** for `β > 0`: `a → 1` at `-∞`. -/
theorem logistic_tendsto_atBot {β : ℝ} (hβ : 0 < β) : Tendsto (logistic β) atBot (𝓝 1) := by
  have h : Tendsto (fun x => Real.exp (β * x)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot hβ)
  have h1 := (h.add_const 1).inv₀ (by norm_num)
  have h2 : logistic β = fun x => (Real.exp (β * x) + 1)⁻¹ := by
    ext x
    simp [logistic]
  rw [h2]
  simpa using h1

/-- **Far field of Eq. (4.22) of arXiv 2112.02695** for `β > 0`: `a → 0` at `+∞`. -/
theorem logistic_tendsto_atTop {β : ℝ} (hβ : 0 < β) : Tendsto (logistic β) atTop (𝓝 0) := by
  have h : Tendsto (fun x => Real.exp (β * x) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hβ))
  have h2 : logistic β = (fun x => Real.exp (β * x) + 1)⁻¹ := by
    ext x
    simp [logistic]
  rw [h2]
  exact h.inv_tendsto_atTop

/-! ### Eqs. (4.18)-(4.23): the Mott-Smith shock profile -/

section Profile

variable [DecidableEq ι]

/-- **Eq. (4.18) of arXiv 2112.02695**: the `v₁²` moment of the steady equation
`v₁ ∂ₓ f = Q(f, f)` holds at `x` for the ansatz with profile `a`. -/
def IsMomentSolution (B : ℝ → ℝ → ℝ) (R ρL TL uL ρR TR uR : ℝ) (i₀ : ι) (a : ℝ → ℝ) (x : ℝ) :
    Prop :=
  ∫ v : EuclideanSpace ℝ ι, v i₀ ^ 2 * (v i₀ * deriv (fun y =>
      ansatz a (shockState R ρL TL uL i₀) (shockState R ρR TR uR i₀) y v) x) =
    ∫ v : EuclideanSpace ℝ ι, v i₀ ^ 2 * collisionQ B
      (ansatz a (shockState R ρL TL uL i₀) (shockState R ρR TR uR i₀) x)
      (ansatz a (shockState R ρL TL uL i₀) (shockState R ρR TR uR i₀) x) v

/-- **Eq. (4.21) of arXiv 2112.02695**: under the Rankine-Hugoniot relations in dimension
`d = card ι`, the moment equation at `x` is exactly
`(d - 1) ρ_L u_L R (T_L - T_R) a' = -α a (1 - a)`. -/
theorem eq4_21 (B : ℝ → ℝ → ℝ) {R ρL TL ρR TR uL uR : ℝ} (hL : 0 < R * TL) (hR : 0 < R * TR)
    (i₀ : ι)
    (hRH : IsRankineHugoniot (Fintype.card ι) R ρL uL TL ρR uR TR)
    (hLR : ∀ v, Integrable (collisionIntegrand B (shockState R ρL TL uL i₀)
      (shockState R ρR TR uR i₀) v) collisionMeasure)
    (hRL : ∀ v, Integrable (collisionIntegrand B (shockState R ρR TR uR i₀)
      (shockState R ρL TL uL i₀) v) collisionMeasure)
    {a : ℝ → ℝ} {x : ℝ} (ha : DifferentiableAt ℝ a x) :
    IsMomentSolution B R ρL TL uL ρR TR uR i₀ a x ↔
      ((Fintype.card ι : ℝ) - 1) * ρL * uL * R * (TL - TR) * deriv a x =
        -(shockAlpha B (shockState R ρL TL uL i₀) (shockState R ρR TR uR i₀) i₀ *
          (a x * (1 - a x))) := by
  rw [IsMomentSolution, eq4_19 B hL hR i₀ hLR hRL ha, flux_difference hRH]
  constructor <;> intro h <;> linear_combination -h

/-- **Eqs. (4.17)-(4.22) of arXiv 2112.02695, the Mott-Smith profile.**  Let `f_L`, `f_R` be
Maxwellians joined by the nontrivial branch of the Rankine-Hugoniot relations in dimension
`d = card ι ≥ 2`, and let `Q` be the operator (1.2) with a kernel for which `Q(f_L, f_R)` and
`Q(f_R, f_L)` converge.  Then the denominator of `β = α / ((d - 1) ρ_L u_L R (T_L - T_R))` is
nonzero, the profile `a(x) = 1 / (exp(β x) + 1)` satisfies the moment equation (4.18) at every `x`,
and every differentiable solution of (4.18) on `ℝ` with `a(x₀) = 1/2` is this profile translated by
`x₀`.

The moment equation is the paper's closure, so `f` need not solve the Boltzmann equation itself:
the claim that it approximates the shock is heuristic in the paper and is not formalized. -/
theorem mottSmith_profile (B : ℝ → ℝ → ℝ) {R ρL TL ρR TR uL uR : ℝ}
    (hd : 2 ≤ Fintype.card ι) (hRpos : 0 < R) (hρ : 0 < ρL) (hu : uL ≠ 0) (hTL : 0 < TL)
    (hTR : 0 < TR) (i₀ : ι)
    (hRH : IsRankineHugoniot (Fintype.card ι) R ρL uL TL ρR uR TR) (hne : uR ≠ uL)
    (hLR : ∀ v, Integrable (collisionIntegrand B (shockState R ρL TL uL i₀)
      (shockState R ρR TR uR i₀) v) collisionMeasure)
    (hRL : ∀ v, Integrable (collisionIntegrand B (shockState R ρR TR uR i₀)
      (shockState R ρL TL uL i₀) v) collisionMeasure) :
    ((Fintype.card ι : ℝ) - 1) * ρL * uL * R * (TL - TR) ≠ 0 ∧
      (∀ x, IsMomentSolution B R ρL TL uL ρR TR uR i₀
        (logistic (shockAlpha B (shockState R ρL TL uL i₀) (shockState R ρR TR uR i₀) i₀ /
          (((Fintype.card ι : ℝ) - 1) * ρL * uL * R * (TL - TR)))) x) ∧
      ∀ a : ℝ → ℝ, Differentiable ℝ a → (∀ x, IsMomentSolution B R ρL TL uL ρR TR uR i₀ a x) →
        ∀ x₀, a x₀ = 1 / 2 → ∀ x, a x =
          logistic (shockAlpha B (shockState R ρL TL uL i₀) (shockState R ρR TR uR i₀) i₀ /
            (((Fintype.card ι : ℝ) - 1) * ρL * uL * R * (TL - TR))) (x - x₀) := by
  have hL : 0 < R * TL := mul_pos hRpos hTL
  have hR : 0 < R * TR := mul_pos hRpos hTR
  have hd1 : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < Fintype.card ι := by linarith
  have hjump := temperature_jump_ne_zero hd0 hRpos hρ hu hTL hRH hne
  have hD : ((Fintype.card ι : ℝ) - 1) * ρL * uL * R * (TL - TR) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by linarith [hd1] : _ ≠ _ ) hρ.ne') hu)
      hRpos.ne') (sub_ne_zero.mpr hjump)
  set D := ((Fintype.card ι : ℝ) - 1) * ρL * uL * R * (TL - TR)
  set α := shockAlpha B (shockState R ρL TL uL i₀) (shockState R ρR TR uR i₀) i₀
  refine ⟨hD, fun x => ?_, fun a ha hsol x₀ h0 x => ?_⟩
  · have h1 := hasDerivAt_logistic (α / D) x
    refine (eq4_21 B hL hR i₀ hRH hLR hRL h1.differentiableAt).mpr ?_
    rw [h1.deriv]
    change D * _ = -(α * _)
    field_simp
  · refine logistic_unique (fun y => ?_) h0 x
    have h1 := (ha y).hasDerivAt
    have h2 := (eq4_21 B hL hR i₀ hRH hLR hRL (ha y)).mp (hsol y)
    change D * _ = -(α * _) at h2
    have h3 : deriv a y = -(α / D) * (a y * (1 - a y)) := by
      apply mul_left_cancel₀ hD
      rw [h2]
      field_simp
    rwa [h3] at h1

/-- **Eq. (4.23) of arXiv 2112.02695**: the density profile of the ansatz with the profile (4.22)
is `ρ(x) / ρ_L = (1 + (d + 1) M_L² / (M_L² + d) exp(β x)) / (1 + exp(β x))`, for every `β`. -/
theorem eq4_23 {R ρL TL ρR TR uL uR : ℝ} (hd : 0 < Fintype.card ι) (hRpos : 0 < R) (hρ : 0 < ρL)
    (hu : uL ≠ 0) (hTL : 0 < TL) (hTR : 0 < TR) (i₀ : ι)
    (hRH : IsRankineHugoniot (Fintype.card ι) R ρL uL TL ρR uR TR) (hne : uR ≠ uL) (β x : ℝ) :
    (∫ v : EuclideanSpace ℝ ι, ansatz (logistic β) (shockState R ρL TL uL i₀)
        (shockState R ρR TR uR i₀) x v) / ρL =
      (1 + (Fintype.card ι + 1) * machL (Fintype.card ι) R uL TL ^ 2 /
          (machL (Fintype.card ι) R uL TL ^ 2 + Fintype.card ι) * Real.exp (β * x)) /
        (1 + Real.exp (β * x)) := by
  have hL : 0 < R * TL := mul_pos hRpos hTL
  have hR : 0 < R * TR := mul_pos hRpos hTR
  have hd0 : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hd
  have h1 : Integrable (shockState R ρL TL uL i₀) := by
    simpa using integrable_moment hL ρL (EuclideanSpace.single i₀ uL) i₀ 0
  have h2 : Integrable (shockState R ρR TR uR i₀) := by
    simpa using integrable_moment hR ρR (EuclideanSpace.single i₀ uR) i₀ 0
  have : Nonempty ι := ⟨i₀⟩
  have hint : ∫ v : EuclideanSpace ℝ ι, ansatz (logistic β) (shockState R ρL TL uL i₀)
      (shockState R ρR TR uR i₀) x v =
      logistic β x * ρL + (1 - logistic β x) * ρR := by
    simp only [ansatz]
    rw [integral_add (h1.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul,
      integral_maxwellian hL, integral_maxwellian hR]
  obtain ⟨hρR, -, -⟩ := eq4_6 hd0 hRpos hρ hu hTL hRH hne
  rw [hint, hρR]
  have hM := machL_sq (uL := uL) hd0 hRpos hTL
  set m2 := machL (Fintype.card ι) R uL TL ^ 2
  have hm2 : 0 < m2 := by
    rw [hM]
    have : 0 < R * TL := hL
    positivity
  simp only [logistic]
  field_simp
  ring

/-- **The constraint `a₁ + a₂ = 1` of Sec. 4.2 of arXiv 2112.02695**: the mass flux of
`a₁ f_L + a₂ f_R` is `(a₁ + a₂) ρ_L u_L`, so it equals the upstream flux `ρ_L u_L ≠ 0` exactly when
`a₁ + a₂ = 1`. -/
theorem massFlux_constraint {d R ρL TL ρR TR uL uR : ℝ} (hL : 0 < R * TL) (hR : 0 < R * TR)
    (i₀ : ι) (hRH : IsRankineHugoniot d R ρL uL TL ρR uR TR) (hm : ρL * uL ≠ 0) (a₁ a₂ : ℝ) :
    (∫ v : EuclideanSpace ℝ ι, v i₀ * (a₁ * shockState R ρL TL uL i₀ v +
        a₂ * shockState R ρR TR uR i₀ v)) = (a₁ + a₂) * (ρL * uL) ∧
      ((∫ v : EuclideanSpace ℝ ι, v i₀ * (a₁ * shockState R ρL TL uL i₀ v +
        a₂ * shockState R ρR TR uR i₀ v)) = ρL * uL ↔ a₁ + a₂ = 1) := by
  have h1 : Integrable fun v : EuclideanSpace ℝ ι => a₁ * (v i₀ * shockState R ρL TL uL i₀ v) := by
    have := (integrable_moment hL ρL (EuclideanSpace.single i₀ uL) i₀ 1).const_mul a₁
    simpa using this
  have h2 : Integrable fun v : EuclideanSpace ℝ ι => a₂ * (v i₀ * shockState R ρR TR uR i₀ v) := by
    have := (integrable_moment hR ρR (EuclideanSpace.single i₀ uR) i₀ 1).const_mul a₂
    simpa using this
  have hpt : ∀ v : EuclideanSpace ℝ ι, v i₀ * (a₁ * shockState R ρL TL uL i₀ v +
      a₂ * shockState R ρR TR uR i₀ v) =
      a₁ * (v i₀ * shockState R ρL TL uL i₀ v) + a₂ * (v i₀ * shockState R ρR TR uR i₀ v) := by
    intro v
    ring
  have hval : (∫ v : EuclideanSpace ℝ ι, v i₀ * (a₁ * shockState R ρL TL uL i₀ v +
      a₂ * shockState R ρR TR uR i₀ v)) = (a₁ + a₂) * (ρL * uL) := by
    rw [integral_congr_ae (ae_of_all _ hpt), integral_add h1 h2, integral_const_mul,
      integral_const_mul, integral_flux_maxwellian hL, integral_flux_maxwellian hR]
    simp only [PiLp.single_apply, ite_true]
    rw [← hRH.mass]
    ring
  refine ⟨hval, ?_⟩
  rw [hval]
  constructor
  · intro h
    exact mul_right_cancel₀ hm (h.trans (one_mul _).symm)
  · intro h
    rw [h, one_mul]

omit [Fintype ι] [DecidableEq ι] in
/-- **The boundary conditions of the shock in Sec. 4.2 of arXiv 2112.02695**: for the ansatz with
the profile (4.22) and `β > 0`, `f → f_L` at `-∞` and `f → f_R` at `+∞`, pointwise in `v`.  The sign
of `α`, hence of `β`, depends on the kernel and is not determined here. -/
theorem ansatz_tendsto {β : ℝ} (hβ : 0 < β) (fL fR : EuclideanSpace ℝ ι → ℝ)
    (v : EuclideanSpace ℝ ι) :
    Tendsto (fun x => ansatz (logistic β) fL fR x v) atBot (𝓝 (fL v)) ∧
      Tendsto (fun x => ansatz (logistic β) fL fR x v) atTop (𝓝 (fR v)) := by
  constructor
  · have h := ((logistic_tendsto_atBot hβ).mul_const (fL v)).add
      (((tendsto_const_nhds (x := (1 : ℝ))).sub (logistic_tendsto_atBot hβ)).mul_const (fR v))
    simpa [ansatz] using h
  · have h := ((logistic_tendsto_atTop hβ).mul_const (fL v)).add
      (((tendsto_const_nhds (x := (1 : ℝ))).sub (logistic_tendsto_atTop hβ)).mul_const (fR v))
    simpa [ansatz] using h

end Profile

/-! ### Bounded kernels: the collision integrals converge -/

/-- A Gaussian bound that is uniform in the center and the temperature. -/
private lemma gauss_bound {θ κ : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / (2 * θ))
    (a u : EuclideanSpace ℝ ι) :
    Real.exp (-‖a - u‖ ^ 2 / (2 * θ)) ≤ Real.exp (κ * ‖u‖ ^ 2) * Real.exp (-κ * ‖a‖ ^ 2 / 2) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h1 : ‖a‖ ^ 2 ≤ 2 * ‖a - u‖ ^ 2 + 2 * ‖u‖ ^ 2 := by
    have h := norm_le_norm_add_norm_sub' a u
    have hn := norm_nonneg a
    nlinarith [sq_nonneg (‖a - u‖ - ‖u‖), norm_nonneg (a - u), norm_nonneg u,
      mul_self_le_mul_self hn (h.trans (add_comm _ _).le)]
  have h2 : κ * ‖a - u‖ ^ 2 ≤ 1 / (2 * θ) * ‖a - u‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hκ (by positivity)
  have h3 : -‖a - u‖ ^ 2 / (2 * θ) = -(1 / (2 * θ) * ‖a - u‖ ^ 2) := by
    ring
  have h4 : κ * ‖a‖ ^ 2 ≤ κ * (2 * ‖a - u‖ ^ 2 + 2 * ‖u‖ ^ 2) :=
    mul_le_mul_of_nonneg_left h1 hκ0
  rw [h3]
  nlinarith

/-- Maxwellians are continuous. -/
private lemma continuous_maxwellian (R ρ T : ℝ) (u : EuclideanSpace ℝ ι) :
    Continuous (maxwellian R ρ T u) := by
  unfold maxwellian
  fun_prop

/-- **The hypotheses of `eq4_19` and `mottSmith_profile` (Sec. 4.2 of arXiv 2112.02695) hold for
bounded kernels.**  If `B` is
measurable and bounded, for instance constant, then the integrand of `Q(M₁, M₂)(v)` is integrable,
for all Maxwellians.  Kernels growing with `|v - v_*|`, such as hard spheres, are not covered
here. -/
theorem integrable_collisionIntegrand {B : ℝ → ℝ → ℝ} (hB : Measurable (Function.uncurry B))
    {C : ℝ} (hC : ∀ r c, |B r c| ≤ C) {R ρ₁ T₁ ρ₂ T₂ : ℝ} (h₁ : 0 < R * T₁) (h₂ : 0 < R * T₂)
    (u₁ u₂ v : EuclideanSpace ℝ ι) (i₀ : ι) :
    Integrable (collisionIntegrand B (maxwellian R ρ₁ T₁ u₁) (maxwellian R ρ₂ T₂ u₂) v)
      collisionMeasure := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 0)
  set c₁ := ρ₁ / (2 * π * R * T₁) ^ ((Fintype.card ι : ℝ) / 2) with hc₁
  set c₂ := ρ₂ / (2 * π * R * T₂) ^ ((Fintype.card ι : ℝ) / 2) with hc₂
  set κ := min (1 / (2 * (R * T₁))) (1 / (2 * (R * T₂))) with hκdef
  have hκ : 0 < κ := lt_min (by positivity) (by positivity)
  have hG : Integrable (fun w : EuclideanSpace ℝ ι => Real.exp (-κ * ‖w‖ ^ 2 / 2)) := by
    have h := integrable_moment (R := 1) (T := 1 / κ) (by positivity) 1
      (0 : EuclideanSpace ℝ ι) i₀ 0
    set c := (1 : ℝ) / (2 * π * 1 * (1 / κ)) ^ ((Fintype.card ι : ℝ) / 2) with hcdef
    have hc : c ≠ 0 := by
      rw [hcdef]
      positivity
    refine (h.const_mul c⁻¹).congr (ae_of_all _ fun w => ?_)
    simp only [pow_zero, one_mul, maxwellian, sub_zero]
    rw [← hcdef, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    congr 1
    field_simp
  have hM₁ : Integrable (maxwellian R ρ₁ T₁ u₁) := by
    simpa using integrable_moment h₁ ρ₁ u₁ i₀ 0
  set K := |c₁ * c₂| * Real.exp (κ * ‖u₁‖ ^ 2 + κ * ‖u₂‖ ^ 2) with hK
  have hg : Integrable (fun z : EuclideanSpace ℝ ι × Metric.sphere (0 : EuclideanSpace ℝ ι) 1 =>
      C * (K * Real.exp (-κ * ‖z.1‖ ^ 2 / 2) +
        |maxwellian R ρ₁ T₁ u₁ z.1| * |maxwellian R ρ₂ T₂ u₂ v|)) collisionMeasure :=
    (((hG.const_mul K).comp_fst _).add ((hM₁.abs.mul_const _).comp_fst _)).const_mul C
  refine hg.mono' ?_ (ae_of_all _ fun z => ?_)
  · have h1 : Measurable fun z : EuclideanSpace ℝ ι × Metric.sphere (0 : EuclideanSpace ℝ ι) 1 =>
        ‖v - z.1‖ := by fun_prop
    have h2 : Measurable fun z : EuclideanSpace ℝ ι × Metric.sphere (0 : EuclideanSpace ℝ ι) 1 =>
        ⟪(z.2 : EuclideanSpace ℝ ι), v - z.1⟫ / ‖v - z.1‖ :=
      (Continuous.measurable (by fun_prop)).div h1
    have hP : Continuous fun z : EuclideanSpace ℝ ι × Metric.sphere (0 : EuclideanSpace ℝ ι) 1 =>
        postVel v z.1 z.2 := by
      unfold postVel
      fun_prop
    have hS : Continuous fun z : EuclideanSpace ℝ ι × Metric.sphere (0 : EuclideanSpace ℝ ι) 1 =>
        postVelStar v z.1 z.2 := by
      unfold postVelStar
      fun_prop
    have hm₁ := continuous_maxwellian R ρ₁ T₁ u₁
    have hm₂ := continuous_maxwellian R ρ₂ T₂ u₂
    have hrest : Continuous fun z : EuclideanSpace ℝ ι × Metric.sphere (0 : EuclideanSpace ℝ ι) 1 =>
        maxwellian R ρ₁ T₁ u₁ (postVelStar v z.1 z.2) * maxwellian R ρ₂ T₂ u₂ (postVel v z.1 z.2) -
          maxwellian R ρ₁ T₁ u₁ z.1 * maxwellian R ρ₂ T₂ u₂ v :=
      ((hm₁.comp hS).mul (hm₂.comp hP)).sub ((hm₁.comp continuous_fst).mul continuous_const)
    exact ((hB.comp (h1.prodMk h2)).mul hrest.measurable).aestronglyMeasurable
  · have hσ : ‖(z.2 : EuclideanSpace ℝ ι)‖ = 1 := by simp
    set a := postVelStar v z.1 z.2 with ha
    set b := postVel v z.1 z.2 with hb
    have hE : ‖a‖ ^ 2 + ‖b‖ ^ 2 = ‖z.1‖ ^ 2 + ‖v‖ ^ 2 := by
      simpa using post_energy v z.1 0 hσ
    have g₁ := gauss_bound (θ := R * T₁) hκ.le (min_le_left _ _) a u₁
    have g₂ := gauss_bound (θ := R * T₂) hκ.le (min_le_right _ _) b u₂
    have hexp : Real.exp (-‖a - u₁‖ ^ 2 / (2 * (R * T₁))) *
        Real.exp (-‖b - u₂‖ ^ 2 / (2 * (R * T₂))) ≤
        Real.exp (κ * ‖u₁‖ ^ 2 + κ * ‖u₂‖ ^ 2) * Real.exp (-κ * ‖z.1‖ ^ 2 / 2) := by
      calc _ ≤ (Real.exp (κ * ‖u₁‖ ^ 2) * Real.exp (-κ * ‖a‖ ^ 2 / 2)) *
            (Real.exp (κ * ‖u₂‖ ^ 2) * Real.exp (-κ * ‖b‖ ^ 2 / 2)) :=
            mul_le_mul g₁ g₂ (Real.exp_pos _).le (by positivity)
        _ = Real.exp (κ * ‖u₁‖ ^ 2 + κ * ‖u₂‖ ^ 2) *
            Real.exp (-κ * (‖a‖ ^ 2 + ‖b‖ ^ 2) / 2) := by
            have h : -κ * (‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 = -κ * ‖a‖ ^ 2 / 2 + -κ * ‖b‖ ^ 2 / 2 := by
              ring
            rw [h, Real.exp_add, Real.exp_add]
            ring
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
            rw [hE]
            have : 0 ≤ κ * ‖v‖ ^ 2 := by positivity
            nlinarith
    have hT₁ : |maxwellian R ρ₁ T₁ u₁ a * maxwellian R ρ₂ T₂ u₂ b| ≤
        K * Real.exp (-κ * ‖z.1‖ ^ 2 / 2) := by
      have hm : maxwellian R ρ₁ T₁ u₁ a * maxwellian R ρ₂ T₂ u₂ b =
          c₁ * c₂ * (Real.exp (-‖a - u₁‖ ^ 2 / (2 * (R * T₁))) *
            Real.exp (-‖b - u₂‖ ^ 2 / (2 * (R * T₂)))) := by
        simp only [maxwellian, ← mul_assoc]
        rw [← hc₁, ← hc₂]
        ring_nf
      rw [hm, abs_mul, abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)), hK, mul_assoc]
      exact mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
    rw [Real.norm_eq_abs, collisionIntegrand, abs_mul]
    refine mul_le_mul (hC _ _) ?_ (abs_nonneg _) hC0
    refine (abs_sub _ _).trans (add_le_add hT₁ ?_)
    rw [abs_mul]

/-- **All hypotheses of `mottSmith_profile` (Sec. 4.2 of arXiv 2112.02695) are satisfiable**: for
every upstream state with `M_L > 1` and every bounded measurable kernel, the downstream state (4.6)
has positive density and temperature and satisfies them. -/
theorem mottSmith_satisfiable [DecidableEq ι] {B : ℝ → ℝ → ℝ}
    (hB : Measurable (Function.uncurry B)) {C : ℝ} (hC : ∀ r c, |B r c| ≤ C) {R ρL uL TL : ℝ}
    (hd : 0 < Fintype.card ι) (hRpos : 0 < R) (hρ : 0 < ρL) (hu : uL ≠ 0) (hTL : 0 < TL)
    (hM : 1 < machL (Fintype.card ι) R uL TL ^ 2) (i₀ : ι) :
    ∃ ρR uR TR : ℝ, 0 < ρR ∧ 0 < TR ∧
      IsRankineHugoniot (Fintype.card ι) R ρL uL TL ρR uR TR ∧ uR ≠ uL ∧
      (∀ v, Integrable (collisionIntegrand B (shockState R ρL TL uL i₀)
        (shockState R ρR TR uR i₀) v) collisionMeasure) ∧
      (∀ v, Integrable (collisionIntegrand B (shockState R ρR TR uR i₀)
        (shockState R ρL TL uL i₀) v) collisionMeasure) := by
  have hd0 : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hd
  obtain ⟨hRH, hne⟩ := isRankineHugoniot_of_mach (ρL := ρL) hd0 hRpos hu hTL hM.ne'
  set m2 := machL (Fintype.card ι) R uL TL ^ 2
  have hm2 : 0 < m2 := by linarith
  have hm3 : 0 < ((Fintype.card ι : ℝ) + 2) * m2 - 1 := by nlinarith
  have hTR : 0 < TL * ((((Fintype.card ι : ℝ) + 2) * m2 - 1) * (m2 + Fintype.card ι) /
      (((Fintype.card ι : ℝ) + 1) ^ 2 * m2)) := by positivity
  refine ⟨_, _, _, by positivity, hTR, hRH, hne, fun v => ?_, fun v => ?_⟩
  · exact integrable_collisionIntegrand hB hC (mul_pos hRpos hTL) (mul_pos hRpos hTR) _ _ v i₀
  · exact integrable_collisionIntegrand hB hC (mul_pos hRpos hTR) (mul_pos hRpos hTL) _ _ v i₀

end Maxwellian

end LeanDLRA.Literature.P2112_02695
