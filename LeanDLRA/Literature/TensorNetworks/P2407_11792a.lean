import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.Matrix.ProjectorSplitting
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2407.11792: Hierarchical DLRA for chemical master equation

**Conservation of probability** (paper Eqs. (3)–(5); `cme_mass_conserved`). The CME on the
lattice `ℤ^d` has reactions `μ` with stoichiometric vectors `ν μ` and propensities `a μ`; its
right-hand side at state `x` is `∑_μ (a_μ(x - ν_μ) P(x - ν_μ) - a_μ(x) P(x))`. For every finitely
supported distribution `P` the right-hand side sums to zero over `x`, so the total probability
`∑ P` is a linear invariant of the CME. This is the re-indexing `x ↦ x + ν_μ` in the paper. The
paper's state space `ℕ^d` is covered by extending `P` by zero to `ℤ^d`; finite support replaces
the paper's implicit summability.

**Algorithm 1, the matrix projector-splitting integrator for the CME** (Sec. 3). On the
truncated state space split into two partitions, a distribution is a matrix `P x⁰ x¹` (the core
matrix layer) and the restricted CME operator is `cmeOp` (gain propensities `α_μ(x - ν_μ)`, zero
when the predecessor leaves the truncated state space, and loss propensities `α_μ(x)`). The
paper's coordinate equations are the factor fields of the core matrix projector-splitting
integrator (`MatrixKSL.kField`, `sField`, `lField`) for this operator: Eqs. (11)–(12)
(`kField_cmeField`), (13)–(14) (`sField_cmeField`) and (15)–(16) (`lField_cmeField`).
Consequently a step of Algorithm 1 is a step `MatrixKSL.IsStep` of the core integrator
(`algorithm1_isStep`, with a non-vacuity example), so the core results (`IsStep.isKSLStep`,
`IsStep.mem_range`, the robust error bounds under their hypotheses) apply to it. The paper's
remark that reaction pathways within a partition are treated exactly is made precise: such
reactions act by left (right) multiplication (`cmeOp_eq_mul_of_left`, `cmeOp_eq_mul_of_right`)
and have zero doubly normal component (`normal_cmeOp_eq_zero_of_left`,
`normal_cmeOp_eq_zero_of_right`), so Algorithm 1 is an `IsKSLStep` with `ε = 0` for them
(`algorithm1_isKSLStep_of_left`). This precise form is ours; the paper states it informally.

**Algorithms 2–5, the tree tensor network integrator** (Sec. 4.1). At an inner node `τ` with
children `τ₀, τ₁`, the node operator `nodeField` acts on node-level functions
`Y_{iτ}(x^{τ₀}, x^{τ₁})` stored as matrices with rows `x^{τ₀}` and columns `(x^{τ₁}, iτ)`; at the
root it is the CME operator. Proved: the K-step field of the core matrix integrator for the node
operator, with the co-range basis `W^{τ₀}`, is again of the form (26) with the recursive
coefficients (27) (`kField_nodeField`), which is why the recursion of Algorithms 2–4 closes; the
S-step field gives (29)–(30) (`sField_nodeField`, via `sField_eq_neg_transpose_mul_kField` and
`neg_transpose_mul_kStepRHS`); and the Galerkin projection of the node operator onto the new
factors of both children gives (34)–(35) (`galerkin_nodeField`). These are coordinate
identities at the level of one node; the recursive bookkeeping of the tree (QR factorizations
of the connecting tensors, the sweep order) is not formalized here. The abstract recursive
integrator of the library is `IsTTNKSLStep` (Ceruti–Lubich–Walach),
with concrete node steps `DimTree.IsValid.isTuckerKSLStep`.

Not formalized: the finite state projection bound (cited from Munsky–Khammash), the relations
(36) used as unit tests, the cost analysis of Sec. 4.2 and the numerical experiments.

Core definitions used: `MatrixKSL.kField`, `MatrixKSL.sField`, `MatrixKSL.lField`,
`MatrixKSL.IsStep`, `IsKSLStep`, `leftProj`, `rightProj`, `ODESolution`. Local definitions:
`cmeRHS` (lattice CME), `cmeOp`/`cmeField` (truncated two-partition CME), `nodeField` (node
operator) and the coefficient families of Eqs. (12), (14), (16), (27), (30), (35); they are the
paper's objects and are connected to the core fields by the identities above.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2407_11792

/-- The CME right-hand side at state `x`: `∑_μ (a_μ(x - ν_μ) P(x - ν_μ) - a_μ(x) P(x))`
for reactions `μ` with stoichiometric vector `ν μ ∈ ℤ^d` and propensity `a μ`. -/
def cmeRHS {d : ℕ} {R : Type*} [Fintype R] (ν : R → Fin d → ℤ) (a : R → (Fin d → ℤ) → ℝ)
    (P : (Fin d → ℤ) → ℝ) (x : Fin d → ℤ) : ℝ :=
  ∑ μ, (a μ (x - ν μ) * P (x - ν μ) - a μ x * P x)

private theorem hasSum_shift_sub {d : ℕ} {g : (Fin d → ℤ) → ℝ} (hg : Summable g) (v : Fin d → ℤ) :
    HasSum (fun x => g (x - v) - g x) 0 := by
  have h1 : HasSum (fun x => g (x - v)) (∑' x, g x) :=
    (Equiv.subRight v).hasSum_iff.mpr hg.hasSum
  simpa using h1.sub hg.hasSum

/-- **Eqs. (3)–(5), conservation of probability** (arXiv 2407.11792). For a finitely supported
distribution `P` on `ℤ^d`, the CME right-hand side `cmeRHS ν a P` has total sum zero. Hence
`∑_x P(t, x)` is conserved by the CME: the gain and loss terms cancel after re-indexing
`x ↦ x + ν_μ`. Arbitrary propensities `a μ : ℤ^d → ℝ` are allowed. -/
theorem cme_mass_conserved {d : ℕ} {R : Type*} [Fintype R] (ν : R → Fin d → ℤ)
    (a : R → (Fin d → ℤ) → ℝ) {P : (Fin d → ℤ) → ℝ} (hP : (Function.support P).Finite) :
    HasSum (cmeRHS ν a P) 0 := by
  have hsum : ∀ μ, Summable (fun x => a μ x * P x) := fun μ => by
    refine summable_of_ne_finset_zero (s := hP.toFinset) fun x hx => ?_
    have hPx : P x = 0 := by
      by_contra h
      exact hx (hP.mem_toFinset.mpr h)
    rw [hPx, mul_zero]
  have hterm : ∀ μ, HasSum (fun x => a μ (x - ν μ) * P (x - ν μ) - a μ x * P x) 0 :=
    fun μ => hasSum_shift_sub (g := fun x => a μ x * P x) (hsum μ) (ν μ)
  have h := hasSum_sum (s := (univ : Finset R)) (fun μ (_ : μ ∈ (univ : Finset R)) => hterm μ)
  rw [Finset.sum_const_zero] at h
  exact h

/-- Non-vacuity: a single reaction with `ν = 1` and constant propensity `1`, applied to the point
mass at `0`. -/
example : HasSum (cmeRHS (d := 1) (fun _ : Unit => (![1] : Fin 1 → ℤ)) (fun _ _ => (1 : ℝ))
    (fun x => if x = 0 then 1 else 0)) 0 := by
  apply cme_mass_conserved
  refine (Set.finite_singleton (0 : Fin 1 → ℤ)).subset ?_
  intro x hx
  by_contra h
  exact hx (ite_eq_right_iff.mpr fun h' => absurd h' h)

/-! ### Sec. 3: the matrix projector-splitting integrator for the CME (Algorithm 1) -/

section Matrix

variable {R X₀ X₁ r : Type*} [Fintype R] [Fintype X₀] [Fintype X₁] [Fintype r]

/-- The **CME operator on two partitions** (Eq. (3) on the truncated state space, in the
partitioned form of Eq. (8)): a state is `x = (x⁰, x¹)`, a distribution is the matrix
`P x⁰ x¹` (rows partition 0, columns partition 1, the core matrix layer), reaction `μ` maps a
state to its predecessor `(σ₀ μ x⁰, σ₁ μ x¹) = (x⁰ - ν⁰_μ, x¹ - ν¹_μ)`, `g μ x` is the gain
propensity `α_μ(x - ν_μ)` (zero when the predecessor leaves the truncated state space) and
`a μ x` the loss propensity `α_μ(x)`:
`(F P)(x) = ∑_μ (g_μ(x) P(x - ν_μ) - a_μ(x) P(x))`. -/
def cmeOp (σ₀ : R → X₀ → X₀) (σ₁ : R → X₁ → X₁) (g a : R → X₀ → X₁ → ℝ)
    (P : Matrix X₀ X₁ ℝ) : Matrix X₀ X₁ ℝ :=
  Matrix.of fun x₀ x₁ => ∑ μ, (g μ x₀ x₁ * P (σ₀ μ x₀) (σ₁ μ x₁) - a μ x₀ x₁ * P x₀ x₁)

/-- The CME operator on two partitions as a time-independent vector field. -/
def cmeField (σ₀ : R → X₀ → X₀) (σ₁ : R → X₁ → X₁) (g a : R → X₀ → X₁ → ℝ) :
    ℝ → Matrix X₀ X₁ ℝ → Matrix X₀ X₁ ℝ :=
  fun _ P => cmeOp σ₀ σ₁ g a P

/-- The **K-step coefficients** `c⁰_{μ,ij}(x⁰) = ⟨X¹_i, α_μ(x⁰ - ν⁰_μ, · - ν¹_μ) X¹_j(· - ν¹_μ)⟩₁`
of Eq. (12), for the right low-rank factors `V = X¹₀`. -/
def coeffC0 (σ₁ : R → X₁ → X₁) (g : R → X₀ → X₁ → ℝ) (V : Matrix X₁ r ℝ) (μ : R) (x₀ : X₀)
    (i j : r) : ℝ :=
  ∑ x₁, V x₁ i * g μ x₀ x₁ * V (σ₁ μ x₁) j

/-- The K-step coefficients `d⁰_{μ,ij}(x⁰) = ⟨X¹_i, α_μ(x⁰, ·) X¹_j⟩₁` of Eq. (12). -/
def coeffD0 (a : R → X₀ → X₁ → ℝ) (V : Matrix X₁ r ℝ) (μ : R) (x₀ : X₀) (i j : r) : ℝ :=
  ∑ x₁, V x₁ i * a μ x₀ x₁ * V x₁ j

/-- The L-step coefficients `c¹_{μ,ij}(x¹) = ⟨X⁰_i, α_μ(· - ν⁰_μ, x¹ - ν¹_μ) X⁰_j(· - ν⁰_μ)⟩₀`
of Eq. (16), for the new left low-rank factors `U = X⁰₁`. -/
def coeffC1 (σ₀ : R → X₀ → X₀) (g : R → X₀ → X₁ → ℝ) (U : Matrix X₀ r ℝ) (μ : R) (x₁ : X₁)
    (i j : r) : ℝ :=
  ∑ x₀, U x₀ i * g μ x₀ x₁ * U (σ₀ μ x₀) j

/-- The L-step coefficients `d¹_{μ,ij}(x¹) = ⟨X⁰_i, α_μ(·, x¹) X⁰_j⟩₀` of Eq. (16). -/
def coeffD1 (a : R → X₀ → X₁ → ℝ) (U : Matrix X₀ r ℝ) (μ : R) (x₁ : X₁) (i j : r) : ℝ :=
  ∑ x₀, U x₀ i * a μ x₀ x₁ * U x₀ j

/-- The S-step coefficients `e_{ijkl}` of Eq. (14), a double inner product over both
partitions. -/
def coeffE (σ₀ : R → X₀ → X₀) (σ₁ : R → X₁ → X₁) (g : R → X₀ → X₁ → ℝ) (U : Matrix X₀ r ℝ)
    (V : Matrix X₁ r ℝ) (i j k l : r) : ℝ :=
  ∑ μ, ∑ x₀, ∑ x₁, U x₀ i * V x₁ j * g μ x₀ x₁ * U (σ₀ μ x₀) k * V (σ₁ μ x₁) l

/-- The S-step coefficients `f_{ijkl}` of Eq. (14). -/
def coeffF (a : R → X₀ → X₁ → ℝ) (U : Matrix X₀ r ℝ) (V : Matrix X₁ r ℝ) (i j k l : r) : ℝ :=
  ∑ μ, ∑ x₀, ∑ x₁, U x₀ i * V x₁ j * a μ x₀ x₁ * U x₀ k * V x₁ l

/-- The right-hand side of the K-step equation (11), and of the L-step equation (15) with the
roles of the partitions exchanged:
`∂ₜ K_i(x) = ∑_μ ∑_j (c_{μ,ij}(x) K_j(x - ν_μ) - d_{μ,ij}(x) K_j(x))`, for any coefficient
families `c, d` (also Eq. (26) at a node of the tree, with the coefficients (27)). -/
def kStepRHS (σ₀ : R → X₀ → X₀) (c d : R → X₀ → r → r → ℝ) (K : Matrix X₀ r ℝ) :
    Matrix X₀ r ℝ :=
  Matrix.of fun x₀ i => ∑ μ, ∑ j, (c μ x₀ i j * K (σ₀ μ x₀) j - d μ x₀ i j * K x₀ j)

/-- The right-hand side of the S-step equation (13) (and (29)):
`∂ₜ S_{ij} = -∑_{k,l} S_{kl} (e_{ijkl} - f_{ijkl})`. -/
def sStepRHS (e f : r → r → r → r → ℝ) (S : Matrix r r ℝ) : Matrix r r ℝ :=
  Matrix.of fun i j => -∑ k, ∑ l, S k l * (e i j k l - f i j k l)

omit [Fintype X₀] in
/-- **Eqs. (11)–(12)** (arXiv 2407.11792, Sec. 3): the K-step field of the core matrix
projector-splitting integrator, `K ↦ F(K V₀ᵀ) V₀` (`MatrixKSL.kField`), is for the CME operator
the right-hand side (11) with the coefficients (12). -/
theorem kField_cmeField (σ₀ : R → X₀ → X₀) (σ₁ : R → X₁ → X₁) (g a : R → X₀ → X₁ → ℝ)
    (V : Matrix X₁ r ℝ) (t : ℝ) (K : Matrix X₀ r ℝ) :
    MatrixKSL.kField V (cmeField σ₀ σ₁ g a) t K =
      kStepRHS σ₀ (coeffC0 σ₁ g V) (coeffD0 a V) K := by
  ext x₀ i
  simp only [MatrixKSL.kField, cmeField, cmeOp, kStepRHS, coeffC0, coeffD0, Matrix.mul_apply,
    Matrix.of_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x₁ _ => by ring

/-- **Eqs. (13)–(14)**: the backward S-step field of the core matrix projector-splitting
integrator, `S ↦ -U₁ᵀ F(U₁ S V₀ᵀ) V₀` (`MatrixKSL.sField`), is for the CME operator the
right-hand side (13) with the coefficients (14). -/
theorem sField_cmeField (σ₀ : R → X₀ → X₀) (σ₁ : R → X₁ → X₁) (g a : R → X₀ → X₁ → ℝ)
    (U : Matrix X₀ r ℝ) (V : Matrix X₁ r ℝ) (t : ℝ) (S : Matrix r r ℝ) :
    MatrixKSL.sField U V (cmeField σ₀ σ₁ g a) t S =
      sStepRHS (coeffE σ₀ σ₁ g U V) (coeffF a U V) S := by
  ext i j
  simp only [MatrixKSL.sField, cmeField, cmeOp, sStepRHS, coeffE, coeffF, Matrix.mul_apply,
    Matrix.of_apply, Matrix.transpose_apply, Matrix.neg_apply, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_sub_distrib, neg_inj]
  simp only [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv
    { toFun := fun p => (p.2.2.2.2, p.2.2.2.1, p.2.2.1, p.2.1, p.1)
      invFun := fun p => (p.2.2.2.2, p.2.2.2.1, p.2.2.1, p.2.1, p.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } _ _ fun p => by simp only [Equiv.coe_fn_mk]; ring

omit [Fintype X₁] in
/-- **Eqs. (15)–(16)**: the L-step field of the core matrix projector-splitting integrator,
`L ↦ F(U₁ Lᵀ)ᵀ U₁` (`MatrixKSL.lField`), is for the CME operator the right-hand side (15) with
the coefficients (16). -/
theorem lField_cmeField (σ₀ : R → X₀ → X₀) (σ₁ : R → X₁ → X₁) (g a : R → X₀ → X₁ → ℝ)
    (U : Matrix X₀ r ℝ) (t : ℝ) (L : Matrix X₁ r ℝ) :
    MatrixKSL.lField U (cmeField σ₀ σ₁ g a) t L =
      kStepRHS σ₁ (coeffC1 σ₀ g U) (coeffD1 a U) L := by
  ext x₁ i
  simp only [MatrixKSL.lField, cmeField, cmeOp, kStepRHS, coeffC1, coeffD1, Matrix.mul_apply,
    Matrix.of_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x₀ _ => by ring

/-- **Algorithm 1 is the core matrix projector-splitting step** (arXiv 2407.11792, Sec. 3,
Algorithm 1): K-step (11) from `K(0) = X⁰₀ S₀` (step 2), QR factorization
`K(Δt) = X⁰₁ S̃` (step 3; `St` stands for `S̃`), backward S-step (13) from `S̃` (step 5), and
L-step (15) from
`L(0) = X¹₀ Ŝᵀ` (step 7), with coefficients (12), (14), (16) computed from the current factors
(steps 1, 4, 6), form one step `MatrixKSL.IsStep` of the core integrator for the CME field
(`X¹₀` and `X⁰₁` orthonormal). Hence the core results for that integrator (`IsStep.isKSLStep`,
`IsStep.mem_range`, `IsStep.eq_factored` for step 8) apply to Algorithm 1. -/
theorem algorithm1_isStep [DecidableEq r] {σ₀ : R → X₀ → X₀} {σ₁ : R → X₁ → X₁}
    {g a : R → X₀ → X₁ → ℝ} {t₀ t₁ : ℝ} {X0₀ X0₁ : Matrix X₀ r ℝ} {X1₀ : Matrix X₁ r ℝ}
    {S₀ St : Matrix r r ℝ} {K : ℝ → Matrix X₀ r ℝ} {S : ℝ → Matrix r r ℝ}
    {L : ℝ → Matrix X₁ r ℝ} (hX1₀ : X1₀ᵀ * X1₀ = 1)
    (hK : ODESolution (fun _ => kStepRHS σ₀ (coeffC0 σ₁ g X1₀) (coeffD0 a X1₀)) K t₀ t₁)
    (hK₀ : K t₀ = X0₀ * S₀) (hX0₁ : X0₁ᵀ * X0₁ = 1) (hQR : K t₁ = X0₁ * St)
    (hS : ODESolution (fun _ => sStepRHS (coeffE σ₀ σ₁ g X0₁ X1₀) (coeffF a X0₁ X1₀)) S t₀ t₁)
    (hS₀ : S t₀ = St)
    (hL : ODESolution (fun _ => kStepRHS σ₁ (coeffC1 σ₀ g X0₁) (coeffD1 a X0₁)) L t₀ t₁)
    (hL₀ : L t₀ = X1₀ * (S t₁)ᵀ) :
    MatrixKSL.IsStep (cmeField σ₀ σ₁ g a) t₀ t₁ X0₀ S₀ X1₀ X0₁ St K S L where
  orthV₀ := hX1₀
  kSol := by
    have : MatrixKSL.kField X1₀ (cmeField σ₀ σ₁ g a) =
        fun _ => kStepRHS σ₀ (coeffC0 σ₁ g X1₀) (coeffD0 a X1₀) :=
      funext fun t => funext fun K => kField_cmeField σ₀ σ₁ g a X1₀ t K
    rwa [this]
  kStart := hK₀
  orthU₁ := hX0₁
  kQR := hQR
  sSol := by
    have : MatrixKSL.sField X0₁ X1₀ (cmeField σ₀ σ₁ g a) =
        fun _ => sStepRHS (coeffE σ₀ σ₁ g X0₁ X1₀) (coeffF a X0₁ X1₀) :=
      funext fun t => funext fun S => sField_cmeField σ₀ σ₁ g a X0₁ X1₀ t S
    rwa [this]
  sStart := hS₀
  lSol := by
    have : MatrixKSL.lField X0₁ (cmeField σ₀ σ₁ g a) =
        fun _ => kStepRHS σ₁ (coeffC1 σ₀ g X0₁) (coeffD1 a X0₁) :=
      funext fun t => funext fun L => lField_cmeField σ₀ σ₁ g a X0₁ t L
    rwa [this]
  lStart := hL₀

/-- Non-vacuity of `algorithm1_isStep`: a rank-one step on one-point partitions without
reactions. -/
example : MatrixKSL.IsStep (r := Unit) (cmeField (R := Fin 0) (X₀ := Unit) (X₁ := Unit)
    (fun _ => id) (fun _ => id) 0 0) 0 1 1 1 1 1 1 (fun _ => 1) (fun _ => 1) (fun _ => 1) := by
  have hc : ODESolution (fun _ (_ : Matrix Unit Unit ℝ) => (0 : Matrix Unit Unit ℝ))
      (fun _ => 1) 0 1 := by
    simpa using MatrixKSL.odeSolution_affine (1 : Matrix Unit Unit ℝ) 0 0 1
  have hk : ∀ (c d : Fin 0 → Unit → Unit → Unit → ℝ),
      (fun (_ : ℝ) => kStepRHS (fun _ => id) c d) = fun _ _ => 0 :=
    fun c d => funext fun _ => funext fun K => by ext; simp [kStepRHS]
  have hs : ∀ (e f : Unit → Unit → Unit → Unit → ℝ), (∀ i j k l, e i j k l = f i j k l) →
      (fun (_ : ℝ) => sStepRHS e f) = fun _ _ => 0 :=
    fun e f h => funext fun _ => funext fun S => by ext; simp [sStepRHS, h]
  refine algorithm1_isStep (by simp) ?_ (by simp) (by simp) (by simp) ?_ rfl ?_ (by simp)
  · rw [hk]; exact hc
  · rw [hs _ _ fun _ _ _ _ => by simp [coeffE, coeffF]]; exact hc
  · rw [hk]; exact hc

omit [Fintype X₁] in
/-- Reactions that change only partition 0 and whose propensities depend only on `x⁰` act by
left multiplication: the CME operator is `P ↦ M P`. -/
theorem cmeOp_eq_mul_of_left [DecidableEq X₀] (σ₀ : R → X₀ → X₀) (g₀ a₀ : R → X₀ → ℝ)
    (P : Matrix X₀ X₁ ℝ) :
    cmeOp σ₀ (fun _ => id) (fun μ x₀ _ => g₀ μ x₀) (fun μ x₀ _ => a₀ μ x₀) P =
      (Matrix.of fun x₀ y₀ => ∑ μ, (g₀ μ x₀ * (if σ₀ μ x₀ = y₀ then 1 else 0) -
        a₀ μ x₀ * (if x₀ = y₀ then 1 else 0))) * P := by
  ext x₀ x₁
  simp only [cmeOp, Matrix.mul_apply, Matrix.of_apply, id, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp [sub_mul, Finset.sum_sub_distrib]

omit [Fintype X₀] in
/-- Reactions that change only partition 1 and whose propensities depend only on `x¹` act by
right multiplication: the CME operator is `P ↦ P Nᵀ`. -/
theorem cmeOp_eq_mul_of_right [DecidableEq X₁] (σ₁ : R → X₁ → X₁) (g₁ a₁ : R → X₁ → ℝ)
    (P : Matrix X₀ X₁ ℝ) :
    cmeOp (fun _ => id) σ₁ (fun μ _ x₁ => g₁ μ x₁) (fun μ _ x₁ => a₁ μ x₁) P =
      P * (Matrix.of fun x₁ y₁ => ∑ μ, (g₁ μ x₁ * (if σ₁ μ x₁ = y₁ then 1 else 0) -
        a₁ μ x₁ * (if x₁ = y₁ then 1 else 0)))ᵀ := by
  ext x₀ x₁
  simp only [cmeOp, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, id,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]
  ring

/-- **Reaction pathways within a partition are treated exactly** (arXiv 2407.11792, Sec. 3:
"it is ensured that reaction pathways lying within a partition are treated exactly"): for
reactions that change only partition 0, with propensities depending only on `x⁰`, the doubly
normal component `(I - U Uᵀ) F(U S Vᵀ) (I - V Vᵀ)` of the CME operator vanishes at every
factored state with orthonormal `V`. So these reactions add nothing to the normal-component
bound `ε` of the core error analysis (`IsStep.isKSLStep`). The paper states this informally;
the precise statement is ours. -/
theorem normal_cmeOp_eq_zero_of_left [DecidableEq X₀] [DecidableEq X₁] [DecidableEq r]
    (σ₀ : R → X₀ → X₀) (g₀ a₀ : R → X₀ → ℝ) (U : Matrix X₀ r ℝ) (S : Matrix r r ℝ)
    {V : Matrix X₁ r ℝ} (hV : Vᵀ * V = 1) :
    (1 - U * Uᵀ) * cmeOp σ₀ (fun _ => id) (fun μ x₀ _ => g₀ μ x₀) (fun μ x₀ _ => a₀ μ x₀)
      (U * S * Vᵀ) * (1 - V * Vᵀ) = 0 := by
  rw [cmeOp_eq_mul_of_left]
  have : Vᵀ * (1 - V * Vᵀ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hV, Matrix.one_mul, sub_self]
  simp only [Matrix.mul_assoc, this, Matrix.mul_zero]

/-- The mirror statement for reactions that change only partition 1, with propensities depending
only on `x¹` (orthonormal `U`). -/
theorem normal_cmeOp_eq_zero_of_right [DecidableEq X₀] [DecidableEq X₁] [DecidableEq r]
    (σ₁ : R → X₁ → X₁) (g₁ a₁ : R → X₁ → ℝ) {U : Matrix X₀ r ℝ} (hU : Uᵀ * U = 1)
    (S : Matrix r r ℝ) (V : Matrix X₁ r ℝ) :
    (1 - U * Uᵀ) * cmeOp (fun _ => id) σ₁ (fun μ _ x₁ => g₁ μ x₁) (fun μ _ x₁ => a₁ μ x₁)
      (U * S * Vᵀ) * (1 - V * Vᵀ) = 0 := by
  rw [cmeOp_eq_mul_of_right]
  have : (1 - U * Uᵀ) * U = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one, sub_self]
  simp only [← Matrix.mul_assoc, this, Matrix.zero_mul]

/-- **Reactions within partition 0 add no modelling error**: with such reactions only, a step of
Algorithm 1 is an abstract projector-splitting step `IsKSLStep` with normal-component bound
`ε = 0`, so the core local error bound `IsKSLStep.local_error` reduces to its splitting part. -/
theorem algorithm1_isKSLStep_of_left [DecidableEq r] {σ₀ : R → X₀ → X₀} {g₀ a₀ : R → X₀ → ℝ}
    {t₀ t₁ : ℝ} {X0₀ X0₁ : Matrix X₀ r ℝ} {X1₀ : Matrix X₁ r ℝ} {S₀ St : Matrix r r ℝ}
    {K : ℝ → Matrix X₀ r ℝ} {S : ℝ → Matrix r r ℝ} {L : ℝ → Matrix X₁ r ℝ}
    (hs : MatrixKSL.IsStep (cmeField σ₀ (fun _ => id) (fun μ x₀ _ => g₀ μ x₀)
      (fun μ x₀ _ => a₀ μ x₀)) t₀ t₁ X0₀ S₀ X1₀ X0₁ St K S L) :
    IsKSLStep (cmeField σ₀ (fun _ => id) (fun μ x₀ _ => g₀ μ x₀) (fun μ x₀ _ => a₀ μ x₀)) 0
      (leftProj X0₁) (rightProj X1₀) t₀ t₁ (X0₀ * S₀ * X1₀ᵀ) (fun t => K t * X1₀ᵀ)
      (fun t => X0₁ * S t * X1₀ᵀ) (fun t => X0₁ * (L t)ᵀ) := by
  classical
  exact hs.isKSLStep fun t _ => by
    simp only [cmeField, normal_cmeOp_eq_zero_of_left σ₀ g₀ a₀ X0₁ St hs.orthV₀, norm_zero,
      le_refl]

end Matrix

/-! ### Sec. 4.1: the tree tensor network integrator (Algorithms 2–5) -/

section Tree

variable {R X₀ X₁ r r₀ r₁ ρ : Type*} [Fintype R] [Fintype X₀] [Fintype X₁] [Fintype r]
  [Fintype r₀] [Fintype r₁] [Fintype ρ]

/-- The **node operator** of the tree integrator at an inner node `τ` with children `τ₀, τ₁`
(the form of Eqs. (26) and (34)): it acts on node-level functions `Y_{iτ}(x^{τ₀}, x^{τ₁})`,
stored as matrices with rows `x^{τ₀}` and columns `(x^{τ₁}, iτ)` (the matricization of the node
for the child `τ₀`), by
`(A Y)_{iτ}(x) = ∑_μ ∑_{jτ} (c^τ_{μ,iτ jτ}(x) Y_{jτ}(x - ν_μ) - d^τ_{μ,iτ jτ}(x) Y_{jτ}(x))`.
At the root (`ρ` a one-element type) with `c = α_μ(· - ν_μ)`, `d = α_μ` this is the CME
operator `cmeOp`. -/
def nodeField (σ₀ : R → X₀ → X₀) (σ₁ : R → X₁ → X₁) (c d : R → X₀ → X₁ → ρ → ρ → ℝ) :
    ℝ → Matrix X₀ (X₁ × ρ) ℝ → Matrix X₀ (X₁ × ρ) ℝ :=
  fun _ Y => Matrix.of fun x₀ y => ∑ μ, ∑ j,
    (c μ x₀ y.1 y.2 j * Y (σ₀ μ x₀) (σ₁ μ y.1, j) - d μ x₀ y.1 y.2 j * Y x₀ (y.1, j))

/-- The **recursive coefficients** `c^{τ₀}_{μ,iτ₀ jτ₀}(x^{τ₀})` of Eq. (27):
`∑_{iτ, jτ} ⟨W^{τ₀}_{iτ₀ iτ}, c^τ_{μ,iτ jτ}(x^{τ₀}, ·) W^{τ₀}_{jτ₀ jτ}(· - ν^{τ₁}_μ)⟩_{τ₁}`, with
`W (x^{τ₁}, iτ) iτ₀ = W^{τ₀}_{iτ₀ iτ}(x^{τ₁})`. -/
def coeffRecC (σ₁ : R → X₁ → X₁) (c : R → X₀ → X₁ → ρ → ρ → ℝ) (W : Matrix (X₁ × ρ) r ℝ)
    (μ : R) (x₀ : X₀) (i j : r) : ℝ :=
  ∑ iτ, ∑ jτ, ∑ x₁, W (x₁, iτ) i * c μ x₀ x₁ iτ jτ * W (σ₁ μ x₁, jτ) j

/-- The recursive coefficients `d^{τ₀}_{μ,iτ₀ jτ₀}(x^{τ₀})` of Eq. (27). -/
def coeffRecD (d : R → X₀ → X₁ → ρ → ρ → ℝ) (W : Matrix (X₁ × ρ) r ℝ) (μ : R) (x₀ : X₀)
    (i j : r) : ℝ :=
  ∑ iτ, ∑ jτ, ∑ x₁, W (x₁, iτ) i * d μ x₀ x₁ iτ jτ * W (x₁, jτ) j

omit [Fintype X₀] in
/-- **Eqs. (26)–(27)** (arXiv 2407.11792, Sec. 4.1.1): the K-step field of the core matrix
projector-splitting integrator applied to the node operator with the basis `W^{τ₀}` of the
co-range of the child `τ₀` (`MatrixKSL.kField`) is again of the form (26), with the recursive
coefficients (27). So the K-step of every node is an equation of the same type as the matrix
K-step (11), which is what makes the recursion of Algorithms 2–4 close. -/
theorem kField_nodeField (σ₀ : R → X₀ → X₀) (σ₁ : R → X₁ → X₁)
    (c d : R → X₀ → X₁ → ρ → ρ → ℝ) (W : Matrix (X₁ × ρ) r ℝ) (t : ℝ) (K : Matrix X₀ r ℝ) :
    MatrixKSL.kField W (nodeField σ₀ σ₁ c d) t K =
      kStepRHS σ₀ (coeffRecC σ₁ c W) (coeffRecD d W) K := by
  ext x₀ i
  simp only [MatrixKSL.kField, nodeField, kStepRHS, coeffRecC, coeffRecD, Matrix.mul_apply,
    Matrix.of_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  simp only [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv
    { toFun := fun p => (p.2.1, p.2.2.2, p.1.2, p.2.2.1, p.1.1)
      invFun := fun p => ((p.2.2.2.2, p.2.2.1), p.1, p.2.2.2.1, p.2.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } _ _ fun p => by simp only [Equiv.coe_fn_mk]; ring

omit [Fintype R] [Fintype r₀] [Fintype r₁] [Fintype ρ] in
/-- The S-step field of the core matrix integrator is minus the Galerkin projection of the
K-step field: `sField U₁ V F S = -U₁ᵀ kField V F (U₁ S)`. -/
theorem sField_eq_neg_transpose_mul_kField (U : Matrix X₀ r ℝ) (V : Matrix X₁ r ℝ)
    (F : ℝ → Matrix X₀ X₁ ℝ → Matrix X₀ X₁ ℝ) (t : ℝ) (S : Matrix r r ℝ) :
    MatrixKSL.sField U V F t S = -(Uᵀ * MatrixKSL.kField V F t (U * S)) := by
  simp only [MatrixKSL.sField, MatrixKSL.kField, Matrix.mul_assoc]

/-- The S-step coefficients
`e^{τ₀}_{ijkl} = ∑_μ ⟨X^{τ₀}_{1,i}, c^{τ₀}_{μ,jl} X^{τ₀}_{1,k}(· - ν_μ)⟩` of Eq. (30), for any
K-step coefficients `c`. -/
def coeffSE (σ₀ : R → X₀ → X₀) (c : R → X₀ → r → r → ℝ) (U : Matrix X₀ r ℝ) (i j k l : r) :
    ℝ :=
  ∑ μ, ∑ x₀, U x₀ i * c μ x₀ j l * U (σ₀ μ x₀) k

/-- The S-step coefficients `f^{τ₀}_{ijkl} = ∑_μ ⟨X^{τ₀}_{1,i}, d^{τ₀}_{μ,jl} X^{τ₀}_{1,k}⟩` of
Eq. (30). -/
def coeffSF (d : R → X₀ → r → r → ℝ) (U : Matrix X₀ r ℝ) (i j k l : r) : ℝ :=
  ∑ μ, ∑ x₀, U x₀ i * d μ x₀ j l * U x₀ k

omit [Fintype X₁] [Fintype r₀] [Fintype r₁] [Fintype ρ] in
/-- The Galerkin projection of a K-step right-hand side of the form (26) onto new orthonormal
factors `U` is the S-step right-hand side (29) with the coefficients (30). -/
theorem neg_transpose_mul_kStepRHS (σ₀ : R → X₀ → X₀) (c d : R → X₀ → r → r → ℝ)
    (U : Matrix X₀ r ℝ) (S : Matrix r r ℝ) :
    -(Uᵀ * kStepRHS σ₀ c d (U * S)) = sStepRHS (coeffSE σ₀ c U) (coeffSF d U) S := by
  ext i j
  simp only [kStepRHS, sStepRHS, coeffSE, coeffSF, Matrix.mul_apply, Matrix.of_apply,
    Matrix.transpose_apply, Matrix.neg_apply, Finset.mul_sum, ← Finset.sum_sub_distrib,
    neg_inj]
  simp only [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv
    { toFun := fun p => (p.2.2.2, p.2.2.1, p.2.1, p.1)
      invFun := fun p => (p.2.2.2, p.2.2.1, p.2.1, p.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } _ _ fun p => by simp only [Equiv.coe_fn_mk]; ring

omit [Fintype r₀] [Fintype r₁] in
/-- **Eqs. (29)–(30)** (Sec. 4.1.1): the S-step field of the core matrix integrator for the
node operator, with the new factors `U = X^{τ₀}_1` of the child and the co-range basis
`W^{τ₀}`, is the right-hand side (29) with the coefficients (30) built from the recursive
coefficients (27). -/
theorem sField_nodeField (σ₀ : R → X₀ → X₀) (σ₁ : R → X₁ → X₁)
    (c d : R → X₀ → X₁ → ρ → ρ → ℝ) (U : Matrix X₀ r ℝ) (W : Matrix (X₁ × ρ) r ℝ) (t : ℝ)
    (S : Matrix r r ℝ) :
    MatrixKSL.sField U W (nodeField σ₀ σ₁ c d) t S =
      sStepRHS (coeffSE σ₀ (coeffRecC σ₁ c W) U) (coeffSF (coeffRecD d W) U) S := by
  rw [sField_eq_neg_transpose_mul_kField, kField_nodeField, neg_transpose_mul_kStepRHS]

/-- The node state built from the new child factors `U₀ = X^{τ₀}_1`, `U₁ = X^{τ₁}_1` and a
connecting tensor:
`Y_{iτ}(x⁰, x¹) = ∑_{j₀, j₁} C_{iτ j₀ j₁} X^{τ₀}_{1,j₀}(x⁰) X^{τ₁}_{1,j₁}(x¹)`. -/
def nodeLift (U₀ : Matrix X₀ r₀ ℝ) (U₁ : Matrix X₁ r₁ ℝ) (C : ρ → r₀ → r₁ → ℝ) :
    Matrix X₀ (X₁ × ρ) ℝ :=
  Matrix.of fun x₀ y => ∑ j₀, ∑ j₁, C y.2 j₀ j₁ * U₀ x₀ j₀ * U₁ y.1 j₁

/-- The connecting-tensor coefficients `g^τ` of Eq. (35). -/
def coeffG (σ₀ : R → X₀ → X₀) (σ₁ : R → X₁ → X₁) (c : R → X₀ → X₁ → ρ → ρ → ℝ)
    (U₀ : Matrix X₀ r₀ ℝ) (U₁ : Matrix X₁ r₁ ℝ) (iτ : ρ) (i₀ : r₀) (i₁ : r₁) (jτ : ρ) (j₀ : r₀)
    (j₁ : r₁) : ℝ :=
  ∑ μ, ∑ x₀, ∑ x₁,
    U₀ x₀ i₀ * U₁ x₁ i₁ * c μ x₀ x₁ iτ jτ * U₀ (σ₀ μ x₀) j₀ * U₁ (σ₁ μ x₁) j₁

/-- The connecting-tensor coefficients `h^τ` of Eq. (35). -/
def coeffH (d : R → X₀ → X₁ → ρ → ρ → ℝ) (U₀ : Matrix X₀ r₀ ℝ) (U₁ : Matrix X₁ r₁ ℝ) (iτ : ρ)
    (i₀ : r₀) (i₁ : r₁) (jτ : ρ) (j₀ : r₀) (j₁ : r₁) : ℝ :=
  ∑ μ, ∑ x₀, ∑ x₁, U₀ x₀ i₀ * U₁ x₁ i₁ * d μ x₀ x₁ iτ jτ * U₀ x₀ j₀ * U₁ x₁ j₁

/-- **Eqs. (34)–(35)** (Sec. 4.1.3, Algorithm 5): the Galerkin projection of the node operator
onto the new factors of both children, applied to the node state of a connecting tensor `C`, is
the right-hand side `∑_{jτ, j₀, j₁} C_{jτ j₀ j₁} (g^τ - h^τ)` of Eq. (34) with the coefficients
(35). -/
theorem galerkin_nodeField (σ₀ : R → X₀ → X₀) (σ₁ : R → X₁ → X₁)
    (c d : R → X₀ → X₁ → ρ → ρ → ℝ) (U₀ : Matrix X₀ r₀ ℝ) (U₁ : Matrix X₁ r₁ ℝ)
    (C : ρ → r₀ → r₁ → ℝ) (t : ℝ) (iτ : ρ) (i₀ : r₀) (i₁ : r₁) :
    ∑ x₀, ∑ x₁, U₀ x₀ i₀ * U₁ x₁ i₁ * nodeField σ₀ σ₁ c d t (nodeLift U₀ U₁ C) x₀ (x₁, iτ) =
      ∑ jτ, ∑ j₀, ∑ j₁, C jτ j₀ j₁ *
        (coeffG σ₀ σ₁ c U₀ U₁ iτ i₀ i₁ jτ j₀ j₁ - coeffH d U₀ U₁ iτ i₀ i₁ jτ j₀ j₁) := by
  simp only [nodeField, nodeLift, coeffG, coeffH, Matrix.of_apply, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  simp only [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv
    { toFun := fun p => (p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2, p.2.2.1, p.1, p.2.1)
      invFun := fun p => (p.2.2.2.2.1, p.2.2.2.2.2, p.2.2.2.1, p.1, p.2.1, p.2.2.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } _ _ fun p => by simp only [Equiv.coe_fn_mk]; ring

end Tree

end LeanDLRA.Literature.P2407_11792
