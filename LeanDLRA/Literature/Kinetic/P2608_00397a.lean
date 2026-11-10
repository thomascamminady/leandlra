import LeanDLRA.Integrators.BUG
import LeanDLRA.Kinetic.Defs
import LeanDLRA.Matrix.Projectors
import LeanDLRA.OpenProblems.Conservation.Part3c

/-!
# Structure-preserving DLRA for stochastic Vlasov–Poisson (arXiv 2608.00397)

Cui, Scalone, *Structure-Preserving Dynamical Low-Rank Approximations for Stochastic Vlasov--Poisson
Equations*, arXiv version 2 (7 Oct 2026).  Results and equations are cited with the numbering of
that PDF: Theorem 4.1, Lemma 4.2, Theorem 4.3, Remark 4.4, Lemma 4.5, Theorem 4.6, and equations
numbered by section.  This module writes out the fully discrete scheme on finite grids, with the
quadrature weights, the weight `f₀ᵥ`, the velocity nodes and the discrete derivatives (`Grid`), the
transport operator, the stochastic operators `S_EM` and `S_Heun` with the predictor of Eq. (3.11),
the K-step, the S-step started from the augmented state and the conservative truncation of
Section 3.3 (`AugBUGStep`, `IsStep`), for both integrators (`Integrator`), and it proves for them
Eqs. (4.4) and (4.5), the local laws of mass, momentum and energy (`local_mass`, `local_momentum`,
`local_energy`), that the increments lie in the augmented spatial basis (`momentum_increment_mem`,
`energy_increment_mem`), the conservation of the total mass (`total_mass`) and of the expected total
momentum (`expected_momentum`, `expected_momentum_poisson`), the conditional expectation of the
stochastic corrections and of the total energy (`condExp_thetaHeun`, `condExp_totalEnergy_em`,
`condExp_totalEnergy_heun`), and the generality of Remark 4.4 (`IsStep.pair_eq`,
`polynomial_balance`).  `sample_nonvacuous` and `exists_augBUGStep` show that the hypotheses can
hold.

## Differences from the paper

* Only the discrete results of Section 4 are here.  The continuous low-rank equations of Section 2
  are not.  The grids are finite types `X`, `V` and the derivatives are arbitrary linear maps: all
  that is used of them are the identities below.
* The velocity identities are hypotheses, as in the paper, but they are asked only where they are
  used, namely at `fⁿ(x, ·)` and at the Heun predictor (`FirstIds`, `SecondIds`,
  `Integrator.Admissible`), not for all profiles.  This matters: the centred stencil satisfies them
  only up to boundary terms (`central_difference_sbp` of the library), so exactly only for profiles
  that vanish near the ends of the velocity grid.  The paper requires the identities of the
  implemented operators and does not discuss these terms.  With exact identities the laws are exact.
  `sampleDv` is an operator with the identities for all profiles.  The second-order identities are
  separate hypotheses, as in the paper, and `secondIds_of_comp` derives them for `Dvv = Dv ∘ Dv`.
* `U` is any matrix with orthonormal `[U, Wⁿ]` whose columns span `1`, `vᵢ`, `|v|²`
  (`ContainsMoments`).  The modes of the paper are of this kind (`containsMoments_of_modes`).  Their
  discrete orthogonality (a symmetric velocity grid) is part of the hypothesis `V_orth`.
* `AugBUGStep` only asks what is used, so it is more general than the scheme of the paper: `X̃` must
  contain `Xⁿ` and `Kⁿ⁺¹` and `Ṽ = [U, W̃]` must contain `Wⁿ`, while the paper takes the spans to be
  equal to those of `[Xⁿ, Kⁿ⁺¹]` and `[U, Wⁿ, Lⁿ⁺¹]`.  So the L-step, Eq. (3.4), is covered and its
  formula plays no role, as in the paper's proofs.  In the truncation, `X^rem`, `Ŝ`, `Ŵ` are
  arbitrary and the factors need not be orthonormal, so no property of the QR factorizations and of
  the truncated SVD is used beyond the factorization of the first `m` columns.  The rank may change.
* The Heun predictor is represented through a map `Pr`, possibly different in the K- and in the
  S-step.  `Pr = id` is Eq. (3.11), and `Pr = Grid.vproj Vⁿ` is the implementation with Eq. (4.2);
  see `ContainsMoments.vproj_preservesMoments`.  The paper leaves the argument of `S_Heun` in the
  S-step implicit.
* The paper assumes `∫ Eⁿ ρⁿ dx = 0`.  Here `total_force_eq_zero` derives it from the discrete
  Poisson equation (with `periodic_force_eq_zero` for the second-order periodic stencils), and
  `expected_momentum_poisson` has no such assumption.
* The local laws hold for every real vector `Δβ` and every field `E`, hence pathwise.  In the
  expectation theorems the noise enters through its conditional moments, `IsNoise`.  These follow
  from independence of `𝓕ₙ` (`isNoise_of_indep`), and no Gaussianity is used.  As in the paper, the
  measurability of the discrete states and the integrability of the stochastic terms are assumed.
* `R_E` is not estimated, as in the paper.
* `consBug_rk_local_law` of `Stability/Conservation.lean` is an abstract form of the mechanism
  behind Eq. (4.5).  It is not used here: on the factors, with the weighted inner products, the
  direct computation `AugBUGStep.moment_law` is shorter than the construction of the projectors.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2608_00397

open Matrix

/-! ### The fully discrete setting -/

/-- The discretization: spatial and velocity quadrature weights, the weight `f₀ᵥ`, the velocity
nodes and the discrete derivatives. -/
structure Grid (X V : Type*) (d : ℕ) where
  /-- Spatial quadrature weights, `∫ u dx = ∑ₓ wx x * u x`. -/
  wx : X → ℝ
  /-- Velocity quadrature weights, `∫ g dv = ∑ᵥ wv v * g v`. -/
  wv : V → ℝ
  /-- The weight `f₀ᵥ` of the ansatz. -/
  f0 : V → ℝ
  /-- The components `vᵢ` of the velocity nodes. -/
  node : Fin d → V → ℝ
  /-- The discrete `∂/∂xᵢ`. -/
  Dx : Fin d → (X → ℝ) →ₗ[ℝ] X → ℝ
  /-- The discrete `∂/∂vᵢ`. -/
  Dv : Fin d → (V → ℝ) →ₗ[ℝ] V → ℝ
  /-- The discrete `∂²/∂vₗ∂vₙ`. -/
  Dvv : Fin d → Fin d → (V → ℝ) →ₗ[ℝ] V → ℝ

namespace Grid

variable {X V : Type*} {d : ℕ} [Fintype X] [Fintype V] (G : Grid X V d)

/-- The pairing `(p, g)_v = ∫ p g dv`. -/
def pair (p g : V → ℝ) : ℝ := ∑ v, G.wv v * p v * g v

/-- `|v|²` at the nodes. -/
def speed2 (v : V) : ℝ := ∑ i, G.node i v ^ 2

/-- The density `ρ(x) = ∫ f dv`. -/
def dens (f : Matrix X V ℝ) (x : X) : ℝ := G.pair 1 (f x)

/-- The current `Jᵢ(x) = ∫ vᵢ f dv`. -/
def cur (f : Matrix X V ℝ) (i : Fin d) (x : X) : ℝ := G.pair (G.node i) (f x)

/-- The stress `Πᵢⱼ(x) = ∫ vᵢ vⱼ f dv`. -/
def stress (f : Matrix X V ℝ) (i j : Fin d) (x : X) : ℝ := G.pair (G.node i * G.node j) (f x)

/-- The energy flux `Qⱼ(x) = ½ ∫ vⱼ |v|² f dv`. -/
noncomputable def heat (f : Matrix X V ℝ) (j : Fin d) (x : X) : ℝ :=
  1 / 2 * G.pair (G.node j * G.speed2) (f x)

/-- The kinetic energy density `½ ∫ |v|² f dv`. -/
noncomputable def kin (f : Matrix X V ℝ) (x : X) : ℝ := 1 / 2 * G.pair G.speed2 (f x)

/-- The discrete divergence `∇ₓ·u = ∑ᵢ ∂ₓᵢ uᵢ`. -/
def divx (u : Fin d → X → ℝ) (x : X) : ℝ := ∑ i, G.Dx i (u i) x

/-- The transport operator `D(f) = -v·∇ₓ f - E·∇ᵥ f` with frozen field `E`. -/
def transport (E : Fin d → X → ℝ) (f : Matrix X V ℝ) : Matrix X V ℝ := fun x v =>
  -∑ i, G.node i v * G.Dx i (fun y => f y v) x - ∑ i, E i x * G.Dv i (f x) v

/-- `σₛ·∇ᵥ f`, with `σ s i x` the `i`-th component of `σₛ(x)`. -/
def sigmaGrad {K : ℕ} (σ : Fin K → Fin d → X → ℝ) (s : Fin K) (f : Matrix X V ℝ) :
    Matrix X V ℝ := fun x v => ∑ i, σ s i x * G.Dv i (f x) v

/-- The matrix `A = σ σᵀ` at `x`. -/
def diffusion {K : ℕ} (σ : Fin K → Fin d → X → ℝ) (l n : Fin d) (x : X) : ℝ :=
  ∑ s, σ s l x * σ s n x

/-- The Euler–Maruyama stochastic operator (arXiv 2608.00397, Section 3.1):
`S_EM(f) = -∑ₛ (σₛ·∇ᵥ f) Δβˢ + (τ/2) ∑ₗₙ Aₗₙ ∂²f/∂vₗ∂vₙ`. -/
noncomputable def stoEM {K : ℕ} (σ : Fin K → Fin d → X → ℝ) (τ : ℝ) (Δβ : Fin K → ℝ)
    (f : Matrix X V ℝ) : Matrix X V ℝ := fun x v =>
  -∑ s, Δβ s * G.sigmaGrad σ s f x v +
    τ / 2 * ∑ l, ∑ n, diffusion σ l n x * G.Dvv l n (f x) v

/-- The Heun predictor (arXiv 2608.00397, Eq. (3.11)), `f̃ = f - Pr (∑ₛ (σₛ·∇ᵥ f) Δβˢ)`.  Here
`Pr` is how the paper's implementation represents the noise term: `Pr = id` is the exact predictor
of Eq. (3.11) and `Pr = vproj` of a velocity basis is the predictor represented in that basis. -/
def predictor {K : ℕ} (σ : Fin K → Fin d → X → ℝ) (Δβ : Fin K → ℝ)
    (Pr : (V → ℝ) →ₗ[ℝ] V → ℝ) (f : Matrix X V ℝ) : Matrix X V ℝ := fun x =>
  f x - Pr fun v => ∑ s, Δβ s * G.sigmaGrad σ s f x v

/-- The Heun stochastic operator (arXiv 2608.00397, Eq. (3.10)):
`S_Heun(f) = -½ ∑ₛ (σₛ·∇ᵥ f + σₛ·∇ᵥ f̃) Δβˢ`. -/
noncomputable def stoHeun {K : ℕ} (σ : Fin K → Fin d → X → ℝ) (Δβ : Fin K → ℝ)
    (Pr : (V → ℝ) →ₗ[ℝ] V → ℝ) (f : Matrix X V ℝ) : Matrix X V ℝ := fun x v =>
  -(1 / 2) * ∑ s, Δβ s *
    (G.sigmaGrad σ s f x v + G.sigmaGrad σ s (G.predictor σ Δβ Pr f) x v)

/-- The Euler–Maruyama increment `I_EM(f) = τ D(f) + S_EM(f)`. -/
noncomputable def incEM {K : ℕ} (σ : Fin K → Fin d → X → ℝ) (τ : ℝ) (Δβ : Fin K → ℝ)
    (E : Fin d → X → ℝ) (f : Matrix X V ℝ) : Matrix X V ℝ := fun x v =>
  τ * G.transport E f x v + G.stoEM σ τ Δβ f x v

/-- The Heun increment `I_Heun(f) = τ D(f) + S_Heun(f)`. -/
noncomputable def incHeun {K : ℕ} (σ : Fin K → Fin d → X → ℝ) (τ : ℝ) (Δβ : Fin K → ℝ)
    (E : Fin d → X → ℝ) (Pr : (V → ℝ) →ₗ[ℝ] V → ℝ) (f : Matrix X V ℝ) : Matrix X V ℝ :=
  fun x v => τ * G.transport E f x v + G.stoHeun σ Δβ Pr f x v

variable [DecidableEq X] [DecidableEq V]

/-- The spatial mass matrix: `⟨a, b⟩ₓ = aᵀ massX b`. -/
def massX : Matrix X X ℝ := diagonal G.wx

/-- The weighted velocity mass matrix: `⟨p, q⟩ᵥ = ∫ f₀ᵥ p q dv = pᵀ massV q`. -/
def massV : Matrix V V ℝ := diagonal fun v => G.wv v * G.f0 v

end Grid

/-! ### One step of the augmented BUG integrator -/

/-- A low-rank state with `r = m + p` modes: the spatial basis `Xⁿ`, the coefficients `Sⁿ` and the
moving velocity modes `Wⁿ`, so that `Vⁿ = [U, Wⁿ]`. -/
structure State (X V : Type*) (m p : ℕ) where
  /-- The spatial basis `Xⁿ`. -/
  Xb : Matrix X (Fin m ⊕ Fin p) ℝ
  /-- The coefficients `Sⁿ`. -/
  S : Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin p) ℝ
  /-- The moving velocity modes `Wⁿ`. -/
  W : Matrix V (Fin p) ℝ

section Step

variable {X V : Type*} {d m p p' k q : ℕ} [Fintype X] [Fintype V] [DecidableEq X] [DecidableEq V]

/-- The velocity basis `Vⁿ = [U, Wⁿ]`. -/
def State.Vb (U : Matrix V (Fin m) ℝ) (s : State X V m p) : Matrix V (Fin m ⊕ Fin p) ℝ :=
  fromCols U s.W

/-- The distribution `f = f₀ᵥ ∑ᵢⱼ Xᵢ Sᵢⱼ Vⱼ`. -/
def State.dist (G : Grid X V d) (U : Matrix V (Fin m) ℝ) (s : State X V m p) : Matrix X V ℝ :=
  s.Xb * s.S * (s.Vb U)ᵀ * diagonal G.f0

/-- The K-step `Kₖⁿ⁺¹ = Kₖⁿ + (Vₖⁿ, I)ᵥ`, with `Kⁿ = Xⁿ Sⁿ`. -/
def kStep (G : Grid X V d) (U : Matrix V (Fin m) ℝ) (s : State X V m p) (I : Matrix X V ℝ) :
    Matrix X (Fin m ⊕ Fin p) ℝ :=
  s.Xb * s.S + I * diagonal G.wv * s.Vb U

/-- The overlap `Mₖᵢ = ⟨X̃ₖ, Xᵢⁿ⟩ₓ`. -/
def overlapX (G : Grid X V d) (s : State X V m p) (Xa : Matrix X (Fin k) ℝ) :
    Matrix (Fin k) (Fin m ⊕ Fin p) ℝ :=
  Xaᵀ * G.massX * s.Xb

/-- The overlap `Nⱼₗ = ⟨Vⱼⁿ, Ṽₗ⟩ᵥ`. -/
def overlapV (G : Grid X V d) (U : Matrix V (Fin m) ℝ) (s : State X V m p)
    (Wa : Matrix V (Fin q) ℝ) : Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin q) ℝ :=
  (s.Vb U)ᵀ * G.massV * fromCols U Wa

/-- The augmented state `f_aug = f₀ᵥ ∑ X̃ₖ Mₖᵢ Sᵢⱼ Nⱼₗ Ṽₗ` (arXiv 2608.00397, Section 3.1,
with `M`, `N` of Eq. (3.5)). -/
def fAug (G : Grid X V d) (U : Matrix V (Fin m) ℝ) (s : State X V m p)
    (Xa : Matrix X (Fin k) ℝ) (Wa : Matrix V (Fin q) ℝ) : Matrix X V ℝ :=
  Xa * overlapX G s Xa * s.S * overlapV G U s Wa * (fromCols U Wa)ᵀ * diagonal G.f0

/-- The S-step (arXiv 2608.00397, Eq. (3.6)):
`S̃ₖₗ = ∑ᵢⱼ Mₖᵢ Sᵢⱼ Nⱼₗ + (X̃ₖ Ṽₗ, I)ₓᵥ`. -/
def sStep (G : Grid X V d) (U : Matrix V (Fin m) ℝ) (s : State X V m p)
    (Xa : Matrix X (Fin k) ℝ) (Wa : Matrix V (Fin q) ℝ) (I : Matrix X V ℝ) :
    Matrix (Fin k) (Fin m ⊕ Fin q) ℝ :=
  overlapX G s Xa * s.S * overlapV G U s Wa + Xaᵀ * G.massX * I * diagonal G.wv * fromCols U Wa

/-- One step `(Xⁿ, Sⁿ, Wⁿ) ↦ (Xⁿ⁺¹, Sⁿ⁺¹, Wⁿ⁺¹)` of the augmented BUG integrator with conservative
truncation (arXiv 2608.00397, Sections 3.1–3.3).  `IK` is the increment of the K-step and `IS` the
one of the S-step.  `X̃` contains `Xⁿ` and `Kⁿ⁺¹`, and `Ṽ = [U, W̃]` contains `Wⁿ`: the L-step of
the paper is one way to enlarge `W̃`.  The first `m` columns of `X̃ S̃` are factorized as
`X̃^cons S̃^cons`, the remainder is replaced by an arbitrary `X^rem Ŝ Ŵᵀ W̃ᵀ` (the truncated SVD of
the paper), and `[X̃^cons, X^rem] = Xⁿ⁺¹ R`, `Sⁿ⁺¹ = R diag(S̃^cons, Ŝ)`, `Wⁿ⁺¹ = W̃ Ŵ`. -/
structure AugBUGStep (G : Grid X V d) (U : Matrix V (Fin m) ℝ)
    (IK IS : Matrix X V ℝ → Matrix X V ℝ) (s : State X V m p) (s' : State X V m p') (k q : ℕ) where
  /-- The augmented spatial basis `X̃ⁿ⁺¹`. -/
  Xa : Matrix X (Fin k) ℝ
  /-- The moving part `W̃ⁿ⁺¹` of the augmented velocity basis `Ṽⁿ⁺¹ = [U, W̃ⁿ⁺¹]`. -/
  Wa : Matrix V (Fin q) ℝ
  /-- The QR factor `X̃^cons`. -/
  Xcons : Matrix X (Fin m) ℝ
  /-- The QR factor `S̃^cons`. -/
  Scons : Matrix (Fin m) (Fin m) ℝ
  /-- The remainder basis `X^rem = X̃^rem Û`. -/
  Xrem : Matrix X (Fin p') ℝ
  /-- The truncated singular values `Ŝ`. -/
  Shat : Matrix (Fin p') (Fin p') ℝ
  /-- The truncated right singular vectors `Ŵ`. -/
  What : Matrix (Fin q) (Fin p') ℝ
  /-- The last QR factor `R`. -/
  R : Matrix (Fin m ⊕ Fin p') (Fin m ⊕ Fin p') ℝ
  V_orth : (s.Vb U)ᵀ * G.massV * s.Vb U = 1
  Xa_orth : Xaᵀ * G.massX * Xa = 1
  Va_orth : (fromCols U Wa)ᵀ * G.massV * fromCols U Wa = 1
  X_le : LinearMap.range s.Xb.mulVecLin ≤ LinearMap.range Xa.mulVecLin
  K_le : LinearMap.range (kStep G U s (IK (s.dist G U))).mulVecLin ≤ LinearMap.range Xa.mulVecLin
  W_le : LinearMap.range s.W.mulVecLin ≤ LinearMap.range (fromCols U Wa).mulVecLin
  cons_qr : (Xa * sStep G U s Xa Wa (IS (fAug G U s Xa Wa))).submatrix id Sum.inl = Xcons * Scons
  new_W : s'.W = Wa * What
  new_qr : fromCols Xcons Xrem = s'.Xb * R
  new_S : s'.S = R * fromBlocks Scons 0 0 Shat

/-- arXiv 2608.00397, proof of Eq. (4.5):
`A = B C` for some `C` as soon as the columns of `A` lie in the column space of `B`. -/
theorem exists_mul_eq_of_range_le {a b c : Type*} [Fintype b] [Fintype c]
    {A : Matrix a b ℝ} {B : Matrix a c ℝ}
    (h : LinearMap.range A.mulVecLin ≤ LinearMap.range B.mulVecLin) :
    ∃ C : Matrix c b ℝ, A = B * C := by
  classical
  have hc : ∀ j : b, ∃ w : c → ℝ, ∀ i, (B *ᵥ w) i = A i j := by
    intro j
    obtain ⟨w, hw⟩ := h (LinearMap.mem_range_self A.mulVecLin (Pi.single j 1))
    refine ⟨w, fun i => ?_⟩
    have := congrFun hw i
    simpa using this
  choose w hw using hc
  refine ⟨Matrix.of fun i j => w j i, ?_⟩
  ext i j
  rw [← hw j i]
  simp [mulVec, dotProduct, Matrix.mul_apply]

/-- The block `[I; 0]`, whose product with `[A, B]` is `A`. -/
def inlBlock (m p : ℕ) : Matrix (Fin m ⊕ Fin p) (Fin m) ℝ := fromRows 1 0

omit [DecidableEq X] [Fintype X] in
/-- arXiv 2608.00397, proof of Eq. (4.5): `[A, B] [I; 0] = A`. -/
theorem fromCols_mul_inlBlock {Y : Type*} (A : Matrix Y (Fin m) ℝ) (B : Matrix Y (Fin p) ℝ) :
    fromCols A B * inlBlock m p = A := by
  rw [inlBlock, fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero]

namespace AugBUGStep

variable {G : Grid X V d} {U : Matrix V (Fin m) ℝ} {IK IS : Matrix X V ℝ → Matrix X V ℝ}
  {s : State X V m p} {s' : State X V m p'}

variable (D : AugBUGStep G U IK IS s s' k q)

include D in
/-- arXiv 2608.00397, proof of Eq. (4.5):
`Uᵀ⟂W`: the fixed block of `Vᵀ massV U`. -/
theorem V_mass_U : (s.Vb U)ᵀ * G.massV * U = inlBlock m p := by
  have h := congrArg (· * inlBlock m p) D.V_orth
  simp only [Matrix.one_mul, Matrix.mul_assoc] at h
  rwa [State.Vb, fromCols_mul_inlBlock, ← Matrix.mul_assoc, ← State.Vb] at h

/-- arXiv 2608.00397, proof of Eq. (4.5):
The augmented basis fixes the columns of every matrix in its range. -/
theorem Xa_capture {c : Type*} [Fintype c] {A : Matrix X c ℝ}
    (h : LinearMap.range A.mulVecLin ≤ LinearMap.range D.Xa.mulVecLin) :
    D.Xa * (D.Xaᵀ * G.massX * A) = A := by
  obtain ⟨C, rfl⟩ := exists_mul_eq_of_range_le h
  rw [← Matrix.mul_assoc (D.Xaᵀ * G.massX) D.Xa C, D.Xa_orth, Matrix.one_mul]

/-- arXiv 2608.00397, Eq. (4.4): `f_aug = fⁿ`. -/
theorem fAug_eq : fAug G U s D.Xa D.Wa = s.dist G U := by
  have hX : D.Xa * overlapX G s D.Xa = s.Xb := D.Xa_capture D.X_le
  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin m ⊕ Fin q) (Fin m ⊕ Fin p) ℝ,
      s.Vb U = fromCols U D.Wa * C := by
    obtain ⟨C, hC⟩ := exists_mul_eq_of_range_le D.W_le
    refine ⟨fromCols (inlBlock m q) C, ?_⟩
    rw [Matrix.mul_fromCols, fromCols_mul_inlBlock, ← hC, State.Vb]
  have hV : overlapV G U s D.Wa * (fromCols U D.Wa)ᵀ = (s.Vb U)ᵀ := by
    rw [overlapV, hC, transpose_mul, Matrix.mul_assoc Cᵀ, Matrix.mul_assoc Cᵀ, D.Va_orth,
      Matrix.mul_one]
  rw [fAug, Matrix.mul_assoc (D.Xa * _ * _) _ (fromCols U D.Wa)ᵀ, hV, hX, State.dist]

/-- arXiv 2608.00397, proof of Eq. (4.5):
`Ṽᵀ massV U` is the block `[I; 0]`. -/
theorem Va_mass_U : (fromCols U D.Wa)ᵀ * G.massV * U = inlBlock m q := by
  have h := congrArg (· * inlBlock m q) D.Va_orth
  simp only [Matrix.one_mul, Matrix.mul_assoc] at h
  rwa [fromCols_mul_inlBlock, ← Matrix.mul_assoc] at h

include D in
/-- arXiv 2608.00397, proof of Eq. (4.5):
The new moving modes are orthogonal to the fixed ones and the fixed ones are orthonormal:
`(Vⁿ⁺¹)ᵀ massV U = [I; 0]`. -/
theorem V'_mass_U : (s'.Vb U)ᵀ * G.massV * U = inlBlock m p' := by
  have h := D.Va_mass_U
  rw [transpose_fromCols, Matrix.fromRows_mul, Matrix.fromRows_mul, inlBlock,
    Matrix.fromRows_ext_iff] at h
  rw [State.Vb, transpose_fromCols, Matrix.fromRows_mul, Matrix.fromRows_mul, inlBlock, h.1,
    D.new_W, transpose_mul, Matrix.mul_assoc D.Whatᵀ, Matrix.mul_assoc D.Whatᵀ, h.2,
    Matrix.mul_zero]

omit [Fintype X] [DecidableEq X] in
/-- arXiv 2608.00397, proof of Eq. (4.5):
`diagonal f₀ᵥ * diagonal wv` is the weighted mass matrix. -/
theorem f0_mul_wv (G : Grid X V d) : diagonal G.f0 * diagonal G.wv = G.massV := by
  rw [diagonal_mul_diagonal, Grid.massV]
  congr 1
  ext v
  ring

omit [Fintype X] [DecidableEq X] in
/-- arXiv 2608.00397, proof of Eq. (4.5):
The moments of a low-rank state, `f * diagonal wv * U = X S [I; 0]`, if
`Vᵀ massV U = [I; 0]`. -/
theorem dist_moment {r : ℕ} (G : Grid X V d) (U : Matrix V (Fin m) ℝ)
    (s : State X V m r) (h : (s.Vb U)ᵀ * G.massV * U = inlBlock m r) :
    s.dist G U * diagonal G.wv * U = s.Xb * s.S * inlBlock m r := by
  rw [State.dist, Matrix.mul_assoc (_ * _ * _) _ (diagonal G.wv), f0_mul_wv, ← h]
  simp only [Matrix.mul_assoc]

/-- arXiv 2608.00397, proof of Eq. (4.5):
The moments of the new state are the first columns of `X̃ S̃`: the conservative truncation does
not touch them. -/
theorem new_moment :
    s'.dist G U * diagonal G.wv * U =
      (D.Xa * sStep G U s D.Xa D.Wa (IS (fAug G U s D.Xa D.Wa))) * inlBlock m q := by
  have h1 : (D.Xa * sStep G U s D.Xa D.Wa (IS (fAug G U s D.Xa D.Wa))) * inlBlock m q =
      (D.Xa * sStep G U s D.Xa D.Wa (IS (fAug G U s D.Xa D.Wa))).submatrix id Sum.inl := by
    ext x a
    simp [Matrix.mul_apply, inlBlock, Fintype.sum_sum_type, Matrix.one_apply]
  have h2 : fromBlocks D.Scons 0 0 D.Shat * inlBlock m p' = inlBlock m p' * D.Scons := by
    rw [inlBlock, fromBlocks_mul_fromRows, Matrix.fromRows_mul]
    simp
  rw [h1, D.cons_qr, dist_moment G U s' D.V'_mass_U, D.new_S, Matrix.mul_assoc s'.Xb,
    Matrix.mul_assoc D.R, h2, ← Matrix.mul_assoc D.R, ← Matrix.mul_assoc s'.Xb,
    ← Matrix.mul_assoc s'.Xb D.R, ← D.new_qr, fromCols_mul_inlBlock]

/-- arXiv 2608.00397, Eq. (4.5), matrix form: the moments of `X̃ S̃`. -/
theorem sStep_moment :
    (D.Xa * sStep G U s D.Xa D.Wa (IS (fAug G U s D.Xa D.Wa))) * inlBlock m q =
      s.Xb * s.S * inlBlock m p +
        D.Xa * (D.Xaᵀ * G.massX * (IS (s.dist G U) * diagonal G.wv * U)) := by
  have hN : overlapV G U s D.Wa * inlBlock m q = inlBlock m p := by
    rw [overlapV, Matrix.mul_assoc, fromCols_mul_inlBlock, D.V_mass_U]
  have hX : D.Xa * overlapX G s D.Xa = s.Xb := D.Xa_capture D.X_le
  rw [D.fAug_eq, sStep, Matrix.mul_add, Matrix.add_mul]
  congr 1
  · calc D.Xa * (overlapX G s D.Xa * s.S * overlapV G U s D.Wa) * inlBlock m q
        = (D.Xa * overlapX G s D.Xa) * s.S * (overlapV G U s D.Wa * inlBlock m q) := by
          simp only [Matrix.mul_assoc]
      _ = s.Xb * s.S * inlBlock m p := by rw [hN, hX]
  · simp only [Matrix.mul_assoc]
    rw [fromCols_mul_inlBlock]

omit [Fintype X] [DecidableEq X] in
/-- arXiv 2608.00397, proof of Eq. (4.5):
The K-step moments: `Kⁿ⁺¹ [I; 0] = Kⁿ [I; 0] + (U, I)ᵥ`. -/
theorem kStep_moment (I : Matrix X V ℝ) :
    kStep G U s I * inlBlock m p = s.Xb * s.S * inlBlock m p + I * diagonal G.wv * U := by
  rw [kStep, Matrix.add_mul, Matrix.mul_assoc (I * _), State.Vb, fromCols_mul_inlBlock]

/-- The fluxes of the K-step on the fixed modes lie in the augmented spatial basis (the mechanism
of Lemmas 4.2 and 4.5 of arXiv 2608.00397): `(U c, I)ᵥ ∈ span X̃`. -/
theorem flux_mem (c : Fin m → ℝ) :
    (IK (s.dist G U) * diagonal G.wv * U) *ᵥ c ∈ LinearMap.range D.Xa.mulVecLin := by
  obtain ⟨C₁, hC₁⟩ := exists_mul_eq_of_range_le D.K_le
  obtain ⟨C₂, hC₂⟩ := exists_mul_eq_of_range_le D.X_le
  have h := kStep_moment (G := G) (U := U) (s := s) (IK (s.dist G U))
  have h' : IK (s.dist G U) * diagonal G.wv * U =
      D.Xa * (C₁ * inlBlock m p - C₂ * s.S * inlBlock m p) := by
    rw [hC₁, hC₂] at h
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h]
    simp [Matrix.mul_assoc]
  refine ⟨(C₁ * inlBlock m p - C₂ * s.S * inlBlock m p) *ᵥ c, ?_⟩
  rw [h', mulVecLin_apply, mulVec_mulVec]

/-- arXiv 2608.00397, proof of Eq. (4.5):
The orthogonal projection onto `X̃` fixes the fluxes. -/
theorem proj_flux (c : Fin m → ℝ) :
    (D.Xa * (D.Xaᵀ * G.massX)) *ᵥ ((IK (s.dist G U) * diagonal G.wv * U) *ᵥ c) =
      (IK (s.dist G U) * diagonal G.wv * U) *ᵥ c := by
  obtain ⟨w, hw⟩ := D.flux_mem c
  rw [← hw, mulVecLin_apply, mulVec_mulVec, Matrix.mul_assoc D.Xa, D.Xa_orth, Matrix.mul_one]

include D in
/-- arXiv 2608.00397, Eq. (4.5), and the generality of Remark 4.4: on a fixed mode `U c` on which
the increments of the K- and the S-step agree, the step reproduces the increment exactly,
`(U c, fⁿ⁺¹)ᵥ = (U c, fⁿ)ᵥ + (U c, I)ᵥ`. -/
theorem moment_law (c : Fin m → ℝ)
    (hIS : (IS (s.dist G U) * diagonal G.wv * U) *ᵥ c =
      (IK (s.dist G U) * diagonal G.wv * U) *ᵥ c) :
    (s'.dist G U * diagonal G.wv * U) *ᵥ c =
      (s.dist G U * diagonal G.wv * U) *ᵥ c + (IK (s.dist G U) * diagonal G.wv * U) *ᵥ c := by
  rw [D.new_moment, D.sStep_moment, dist_moment G U s D.V_mass_U, Matrix.add_mulVec]
  congr 1
  rw [← D.proj_flux c, ← hIS]
  simp only [mulVec_mulVec, Matrix.mul_assoc]

end AugBUGStep

end Step

/-! ### The velocity identities and the moments of the increments -/

namespace Grid

variable {X V : Type*} {d K : ℕ} [Fintype V] (G : Grid X V d)

/-- arXiv 2608.00397, proofs of Theorems 4.1, 4.3 and 4.6: `(p, ·)ᵥ` is additive. -/
theorem pair_fun_add (p g h : V → ℝ) : G.pair p (fun v => g v + h v) = G.pair p g + G.pair p h := by
  simp only [pair, mul_add, Finset.sum_add_distrib]

/-- arXiv 2608.00397, proofs of Theorems 4.1, 4.3 and 4.6: `(p, ·)ᵥ` is homogeneous. -/
theorem pair_mul_left (p g : V → ℝ) (c : ℝ) : G.pair p (fun v => c * g v) = c * G.pair p g := by
  simp only [pair, Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ => by ring

/-- arXiv 2608.00397, proofs of Theorems 4.1, 4.3 and 4.6: `(p, ·)ᵥ` commutes with finite sums. -/
theorem pair_sum {ι : Type*} (t : Finset ι) (p : V → ℝ) (g : ι → V → ℝ) :
    G.pair p (fun v => ∑ i ∈ t, g i v) = ∑ i ∈ t, G.pair p (g i) := by
  simp only [pair, Finset.mul_sum]
  exact Finset.sum_comm

/-- arXiv 2608.00397, proofs of Theorems 4.1, 4.3 and 4.6: `(p, ·)ᵥ` commutes with differences. -/
theorem pair_sub (p g h : V → ℝ) : G.pair p (g - h) = G.pair p g - G.pair p h := by
  simp only [pair, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- The discrete velocity identities of arXiv 2608.00397, Section 4, at the velocity profile `g`:
`∫ ∂ᵥᵢ g dv = 0`, `∫ vⱼ ∂ᵥᵢ g dv = -δᵢⱼ ∫ g dv`, `∫ |v|² ∂ᵥᵢ g dv = -2 ∫ vᵢ g dv`. -/
structure FirstIds (g : V → ℝ) : Prop where
  div : ∀ i, G.pair 1 (G.Dv i g) = 0
  first : ∀ i j, G.pair (G.node j) (G.Dv i g) = -(if i = j then G.pair 1 g else 0)
  second : ∀ i, G.pair G.speed2 (G.Dv i g) = -2 * G.pair (G.node i) g

/-- The second-order velocity identities of arXiv 2608.00397, Section 4, at the velocity profile
`g`: `∂²ᵥₗᵥₙ g` has no mass and no momentum, and `∫ |v|² ∂²ᵥₗᵥₙ g dv = 2 δₗₙ ∫ g dv`. -/
structure SecondIds (g : V → ℝ) : Prop where
  div : ∀ l n, G.pair 1 (G.Dvv l n g) = 0
  first : ∀ l n j, G.pair (G.node j) (G.Dvv l n g) = 0
  second : ∀ l n, G.pair G.speed2 (G.Dvv l n g) = 2 * (if l = n then G.pair 1 g else 0)

/-- The maps through which the Heun predictor may be represented: those that do not change mass and
momentum.  The exact predictor has `Pr = id`. -/
def PreservesMoments (Pr : (V → ℝ) →ₗ[ℝ] V → ℝ) : Prop :=
  ∀ g, G.pair 1 (Pr g) = G.pair 1 g ∧ ∀ i, G.pair (G.node i) (Pr g) = G.pair (G.node i) g

/-- The Itô correction `Θ_EM = (τ/2) Tr(A) ρ`. -/
noncomputable def thetaEM (σ : Fin K → Fin d → X → ℝ) (τ : ℝ) (ρ : X → ℝ) (x : X) : ℝ :=
  τ / 2 * (∑ l, diffusion σ l l x) * ρ x

/-- The Heun correction `Θ_Heun = ½ ∑ₛᵣ Δβˢ Δβʳ (σₛ·σᵣ) ρ`. -/
noncomputable def thetaHeun (σ : Fin K → Fin d → X → ℝ) (Δβ : Fin K → ℝ) (ρ : X → ℝ) (x : X) : ℝ :=
  1 / 2 * ∑ s, ∑ r, Δβ s * Δβ r * (∑ i, σ s i x * σ r i x) * ρ x

/-- The force `τ E + ∑ₛ Δβˢ σₛ` of the momentum and the energy laws. -/
def force (σ : Fin K → Fin d → X → ℝ) (τ : ℝ) (Δβ : Fin K → ℝ) (E : Fin d → X → ℝ) (j : Fin d)
    (x : X) : ℝ :=
  τ * E j x + ∑ s, Δβ s * σ s j x

/-- The moments of an increment `I` that drive the three balance laws of arXiv 2608.00397. -/
structure IsBalanced (σ : Fin K → Fin d → X → ℝ) (τ : ℝ) (Δβ : Fin K → ℝ) (E : Fin d → X → ℝ)
    (f : Matrix X V ℝ) (Θ : X → ℝ) (I : Matrix X V ℝ) : Prop where
  mass : ∀ x, G.pair 1 (I x) = -τ * G.divx (G.cur f) x
  momentum : ∀ j x, G.pair (G.node j) (I x) =
    -τ * G.divx (G.stress f j) x + force σ τ Δβ E j x * G.dens f x
  energy : ∀ x, 1 / 2 * G.pair G.speed2 (I x) =
    -τ * G.divx (G.heat f) x + ∑ j, force σ τ Δβ E j x * G.cur f j x + Θ x

/-- arXiv 2608.00397, proofs of Theorems 4.1, 4.3 and 4.6:
The velocity moments of the transport operator. -/
theorem pair_transport (p : V → ℝ) (E : Fin d → X → ℝ) (f : Matrix X V ℝ) (x : X) :
    G.pair p (G.transport E f x) =
      -∑ i, G.Dx i (fun y => G.pair (p * G.node i) (f y)) x -
        ∑ i, E i x * G.pair p (G.Dv i (f x)) := by
  have hD : ∀ i, G.Dx i (fun y => G.pair (p * G.node i) (f y)) x =
      ∑ v, G.wv v * p v * (G.node i v * G.Dx i (fun y => f y v) x) := by
    intro i
    have h : (fun y => G.pair (p * G.node i) (f y)) =
        ∑ v, (G.wv v * p v * G.node i v) • fun y => f y v := by
      ext y
      simp [pair, Finset.sum_apply, mul_assoc]
    rw [h, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
    ring
  have hE : ∀ i, E i x * G.pair p (G.Dv i (f x)) =
      ∑ v, G.wv v * p v * (E i x * G.Dv i (f x) v) := by
    intro i
    rw [pair, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  simp only [hD, hE]
  simp only [pair, transport, mul_sub, mul_neg, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    Finset.mul_sum]
  rw [Finset.sum_comm (f := fun v i => G.wv v * p v * (G.node i v * G.Dx i (fun y => f y v) x)),
    Finset.sum_comm (f := fun v i => G.wv v * p v * (E i x * G.Dv i (f x) v))]

/-- arXiv 2608.00397, proofs of Theorems 4.1, 4.3 and 4.6:
The velocity moments of `σₛ·∇ᵥ f`. -/
theorem pair_sigmaGrad (p : V → ℝ) (σ : Fin K → Fin d → X → ℝ) (s : Fin K) (f : Matrix X V ℝ)
    (x : X) : G.pair p (G.sigmaGrad σ s f x) = ∑ i, σ s i x * G.pair p (G.Dv i (f x)) := by
  change G.pair p (fun v => ∑ i, σ s i x * G.Dv i (f x) v) = _
  rw [pair_sum]
  simp only [pair_mul_left]

variable {G}

/-- arXiv 2608.00397, proofs of Theorems 4.1, 4.3 and 4.6:
The moments of `σₛ·∇ᵥ h` under the velocity identities. -/
theorem pair_one_sigmaGrad {h : Matrix X V ℝ} {x : X} (hh : G.FirstIds (h x))
    (σ : Fin K → Fin d → X → ℝ) (s : Fin K) : G.pair 1 (G.sigmaGrad σ s h x) = 0 := by
  rw [pair_sigmaGrad]
  simp [hh.div]

/-- arXiv 2608.00397, proofs of Theorems 4.1, 4.3 and 4.6: `(vⱼ, σₛ·∇ᵥ h)ᵥ = -σₛⱼ ∫ h dv`. -/
theorem pair_node_sigmaGrad {h : Matrix X V ℝ} {x : X} (hh : G.FirstIds (h x))
    (σ : Fin K → Fin d → X → ℝ) (s : Fin K) (j : Fin d) :
    G.pair (G.node j) (G.sigmaGrad σ s h x) = -(σ s j x * G.pair 1 (h x)) := by
  rw [pair_sigmaGrad]
  simp [hh.first]

/-- arXiv 2608.00397, proofs of Theorems 4.1, 4.3 and 4.6: `(|v|², σₛ·∇ᵥ h)ᵥ = -2 σₛ·∫ v h dv`. -/
theorem pair_speed2_sigmaGrad {h : Matrix X V ℝ} {x : X} (hh : G.FirstIds (h x))
    (σ : Fin K → Fin d → X → ℝ) (s : Fin K) :
    G.pair G.speed2 (G.sigmaGrad σ s h x) = -2 * ∑ i, σ s i x * G.pair (G.node i) (h x) := by
  rw [pair_sigmaGrad, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hh.second]; ring

variable (G)

/-- arXiv 2608.00397, proofs of Theorems 4.1, 4.3 and 4.6:
The velocity moments of `S_EM`. -/
theorem pair_stoEM (p : V → ℝ) (σ : Fin K → Fin d → X → ℝ) (τ : ℝ) (Δβ : Fin K → ℝ)
    (f : Matrix X V ℝ) (x : X) :
    G.pair p (G.stoEM σ τ Δβ f x) =
      -∑ s, Δβ s * G.pair p (G.sigmaGrad σ s f x) +
        τ / 2 * ∑ l, ∑ n, diffusion σ l n x * G.pair p (G.Dvv l n (f x)) := by
  have h : G.stoEM σ τ Δβ f x = fun v =>
      (-1) * ∑ s, Δβ s * G.sigmaGrad σ s f x v +
        τ / 2 * ∑ l, ∑ n, diffusion σ l n x * G.Dvv l n (f x) v := by
    ext v
    simp [stoEM]
  rw [h, pair_fun_add, pair_mul_left, pair_mul_left, pair_sum, pair_sum]
  simp only [pair_sum, pair_mul_left]
  ring

/-- arXiv 2608.00397, proofs of Theorems 4.1, 4.3 and 4.6:
The velocity moments of `S_Heun`. -/
theorem pair_stoHeun (p : V → ℝ) (σ : Fin K → Fin d → X → ℝ) (Δβ : Fin K → ℝ)
    (Pr : (V → ℝ) →ₗ[ℝ] V → ℝ) (f : Matrix X V ℝ) (x : X) :
    G.pair p (G.stoHeun σ Δβ Pr f x) =
      -(1 / 2) * ∑ s, Δβ s * (G.pair p (G.sigmaGrad σ s f x) +
        G.pair p (G.sigmaGrad σ s (G.predictor σ Δβ Pr f) x)) := by
  change G.pair p (fun v => -(1 / 2) * ∑ s, Δβ s *
    (G.sigmaGrad σ s f x v + G.sigmaGrad σ s (G.predictor σ Δβ Pr f) x v)) = _
  rw [pair_mul_left, pair_sum]
  simp only [pair_mul_left, pair_fun_add]

variable {G}

/-- arXiv 2608.00397, proofs of Theorems 4.1, 4.3 and 4.6:
The mass of `τ D(f) + S`, for an `f` that satisfies the velocity identities. -/
theorem pair_one_add_transport {f : Matrix X V ℝ} {x : X} (hf : G.FirstIds (f x)) (τ : ℝ)
    (E : Fin d → X → ℝ) (S : V → ℝ) :
    G.pair 1 (fun v => τ * G.transport E f x v + S v) =
      -τ * G.divx (G.cur f) x + G.pair 1 S := by
  have hc : ∀ i, G.cur f i = fun y => G.pair (G.node i) (f y) := fun _ => rfl
  rw [pair_fun_add, pair_mul_left, pair_transport]
  simp only [hf.div, mul_zero, Finset.sum_const_zero, sub_zero, one_mul, divx, hc]
  ring

/-- arXiv 2608.00397, proofs of Theorems 4.1, 4.3 and 4.6:
The momentum of `τ D(f) + S`. -/
theorem pair_node_add_transport {f : Matrix X V ℝ} {x : X} (hf : G.FirstIds (f x)) (τ : ℝ)
    (E : Fin d → X → ℝ) (j : Fin d) (S : V → ℝ) :
    G.pair (G.node j) (fun v => τ * G.transport E f x v + S v) =
      -τ * G.divx (G.stress f j) x + τ * E j x * G.dens f x + G.pair (G.node j) S := by
  have hc : ∀ i, G.stress f j i = fun y => G.pair (G.node j * G.node i) (f y) := fun _ => rfl
  have hE : ∑ i, E i x * G.pair (G.node j) (G.Dv i (f x)) = -(E j x * G.dens f x) := by
    simp [hf.first, dens]
  rw [pair_fun_add, pair_mul_left, pair_transport, hE]
  simp only [divx, hc]
  ring

/-- arXiv 2608.00397, proofs of Theorems 4.1, 4.3 and 4.6:
The kinetic energy of `τ D(f) + S`. -/
theorem pair_speed2_add_transport {f : Matrix X V ℝ} {x : X} (hf : G.FirstIds (f x)) (τ : ℝ)
    (E : Fin d → X → ℝ) (S : V → ℝ) :
    1 / 2 * G.pair G.speed2 (fun v => τ * G.transport E f x v + S v) =
      -τ * G.divx (G.heat f) x + τ * ∑ j, E j x * G.cur f j x + 1 / 2 * G.pair G.speed2 S := by
  have hc : ∀ i, G.Dx i (G.heat f i) x =
      1 / 2 * G.Dx i (fun y => G.pair (G.speed2 * G.node i) (f y)) x := by
    intro i
    have h : G.heat f i = (1 / 2 : ℝ) • fun y => G.pair (G.speed2 * G.node i) (f y) := by
      ext y
      simp only [heat, Pi.smul_apply, smul_eq_mul, mul_comm (G.node i)]
    rw [h, map_smul, Pi.smul_apply, smul_eq_mul]
  have hE : ∑ i, E i x * G.pair G.speed2 (G.Dv i (f x)) = -2 * ∑ i, E i x * G.cur f i x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hf.second, cur]; ring
  rw [pair_fun_add, pair_mul_left, pair_transport, hE]
  simp only [divx, hc, ← Finset.mul_sum]
  ring

/-- arXiv 2608.00397, proofs of Theorems 4.1, 4.3 and 4.6:
Splitting of the force in the energy law. -/
theorem sum_force_mul (σ : Fin K → Fin d → X → ℝ) (τ : ℝ) (Δβ : Fin K → ℝ) (E : Fin d → X → ℝ)
    (J : Fin d → ℝ) (x : X) :
    ∑ j, force σ τ Δβ E j x * J j =
      τ * ∑ j, E j x * J j + ∑ s, Δβ s * ∑ j, σ s j x * J j := by
  simp only [force, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  congr 1
  · exact Finset.sum_congr rfl fun j _ => by ring
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun j _ => by ring

/-- The moments of the Euler–Maruyama increment (arXiv 2608.00397, proofs of Theorems 4.1, 4.3 and
4.6 for the Euler–Maruyama scheme). -/
theorem isBalanced_incEM {f : Matrix X V ℝ} (hf : ∀ x, G.FirstIds (f x))
    (hf2 : ∀ x, G.SecondIds (f x)) (σ : Fin K → Fin d → X → ℝ) (τ : ℝ) (Δβ : Fin K → ℝ)
    (E : Fin d → X → ℝ) :
    G.IsBalanced σ τ Δβ E f (thetaEM σ τ (G.dens f)) (G.incEM σ τ Δβ E f) where
  mass x := by
    change G.pair 1 (fun v => τ * G.transport E f x v + G.stoEM σ τ Δβ f x v) = _
    rw [pair_one_add_transport (hf x), pair_stoEM]
    simp [pair_one_sigmaGrad (hf x), (hf2 x).div]
  momentum j x := by
    change G.pair (G.node j) (fun v => τ * G.transport E f x v + G.stoEM σ τ Δβ f x v) = _
    rw [pair_node_add_transport (hf x), pair_stoEM]
    simp only [pair_node_sigmaGrad (hf x), (hf2 x).first, force, add_mul, Finset.sum_mul,
      mul_zero, Finset.sum_const_zero, add_zero, mul_neg, Finset.sum_neg_distrib, neg_neg, dens]
    simp only [mul_assoc, add_assoc]
  energy x := by
    change 1 / 2 * G.pair G.speed2 (fun v => τ * G.transport E f x v + G.stoEM σ τ Δβ f x v) = _
    rw [pair_speed2_add_transport (hf x), pair_stoEM, sum_force_mul]
    simp only [pair_speed2_sigmaGrad (hf x), (hf2 x).second, thetaEM, dens, cur]
    have h1 : ∑ l, ∑ n, diffusion σ l n x * (2 * if l = n then G.pair 1 (f x) else 0) =
        2 * (∑ l, diffusion σ l l x) * G.pair 1 (f x) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.sum_eq_single l (fun n _ hn => by simp [hn.symm]) (by simp)]
      simp only [ite_true]
      ring
    have h2 : ∑ s, Δβ s * (-2 * ∑ i, σ s i x * G.pair (G.node i) (f x)) =
        -2 * ∑ s, Δβ s * ∑ i, σ s i x * G.pair (G.node i) (f x) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [h1, h2]
    ring

/-- arXiv 2608.00397, proofs of Theorems 4.1, 4.3 and 4.6:
The density of the Heun predictor is that of `f`. -/
theorem pair_one_predictor {f : Matrix X V ℝ} {x : X} (hf : G.FirstIds (f x))
    {Pr : (V → ℝ) →ₗ[ℝ] V → ℝ} (hPr : G.PreservesMoments Pr) (σ : Fin K → Fin d → X → ℝ)
    (Δβ : Fin K → ℝ) : G.pair 1 (G.predictor σ Δβ Pr f x) = G.dens f x := by
  rw [predictor, pair_sub, (hPr _).1, pair_sum]
  simp [pair_mul_left, pair_one_sigmaGrad hf, dens]

/-- arXiv 2608.00397, proofs of Theorems 4.1, 4.3 and 4.6:
The current of the Heun predictor. -/
theorem pair_node_predictor {f : Matrix X V ℝ} {x : X} (hf : G.FirstIds (f x))
    {Pr : (V → ℝ) →ₗ[ℝ] V → ℝ} (hPr : G.PreservesMoments Pr) (σ : Fin K → Fin d → X → ℝ)
    (Δβ : Fin K → ℝ) (i : Fin d) :
    G.pair (G.node i) (G.predictor σ Δβ Pr f x) =
      G.cur f i x + (∑ s, Δβ s * σ s i x) * G.dens f x := by
  rw [predictor, pair_sub, (hPr _).2, pair_sum]
  simp only [pair_mul_left, pair_node_sigmaGrad hf, Finset.sum_mul, cur, dens]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl fun s _ => by ring

/-- The moments of the Heun increment (arXiv 2608.00397, proofs of Theorems 4.1, 4.3 and 4.6 for the
Heun scheme).  The quadratic noise term has no mass and no momentum and it gives the energy
`Θ_Heun`. -/
theorem isBalanced_incHeun {f : Matrix X V ℝ} (hf : ∀ x, G.FirstIds (f x))
    {σ : Fin K → Fin d → X → ℝ} {Δβ : Fin K → ℝ} {Pr : (V → ℝ) →ₗ[ℝ] V → ℝ}
    (hPr : G.PreservesMoments Pr) (hP : ∀ x, G.FirstIds (G.predictor σ Δβ Pr f x)) (τ : ℝ)
    (E : Fin d → X → ℝ) :
    G.IsBalanced σ τ Δβ E f (thetaHeun σ Δβ (G.dens f)) (G.incHeun σ τ Δβ E Pr f) where
  mass x := by
    change G.pair 1 (fun v => τ * G.transport E f x v + G.stoHeun σ Δβ Pr f x v) = _
    rw [pair_one_add_transport (hf x), pair_stoHeun]
    simp [pair_one_sigmaGrad (hf x), pair_one_sigmaGrad (hP x)]
  momentum j x := by
    change G.pair (G.node j) (fun v => τ * G.transport E f x v + G.stoHeun σ Δβ Pr f x v) = _
    rw [pair_node_add_transport (hf x), pair_stoHeun]
    simp only [pair_node_sigmaGrad (hf x), pair_node_sigmaGrad (hP x),
      pair_one_predictor (hf x) hPr, force, add_mul, Finset.sum_mul, dens, add_assoc]
    congr 2
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  energy x := by
    change 1 / 2 * G.pair G.speed2 (fun v => τ * G.transport E f x v + G.stoHeun σ Δβ Pr f x v) = _
    rw [pair_speed2_add_transport (hf x), pair_stoHeun, sum_force_mul]
    simp only [pair_speed2_sigmaGrad (hf x), pair_speed2_sigmaGrad (hP x),
      pair_node_predictor (hf x) hPr]
    have h : 1 / 2 * (-(1 / 2) * ∑ s, Δβ s * (-2 * ∑ i, σ s i x * G.pair (G.node i) (f x) +
          -2 * ∑ i, σ s i x * (G.cur f i x + (∑ r, Δβ r * σ r i x) * G.dens f x))) =
        ∑ s, Δβ s * ∑ j, σ s j x * G.cur f j x + thetaHeun σ Δβ (G.dens f) x := by
      have hs : ∀ s, Δβ s * (-2 * ∑ i, σ s i x * G.pair (G.node i) (f x) +
          -2 * ∑ i, σ s i x * (G.cur f i x + (∑ r, Δβ r * σ r i x) * G.dens f x)) =
          -4 * (Δβ s * ∑ j, σ s j x * G.cur f j x) -
            2 * ∑ r, Δβ s * Δβ r * (∑ i, σ s i x * σ r i x) * G.dens f x := by
        intro s
        have h1 : ∑ i, σ s i x * (G.cur f i x + (∑ r, Δβ r * σ r i x) * G.dens f x) =
            ∑ i, σ s i x * G.cur f i x +
              ∑ i, ∑ r, σ s i x * (Δβ r * σ r i x) * G.dens f x := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [mul_add, Finset.sum_mul, Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun r _ => by ring
        have h2 : Δβ s * ∑ i, ∑ r, σ s i x * (Δβ r * σ r i x) * G.dens f x =
            ∑ r, Δβ s * Δβ r * (∑ i, σ s i x * σ r i x) * G.dens f x := by
          rw [Finset.sum_comm, Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
        have h3 : ∑ i, σ s i x * G.pair (G.node i) (f x) = ∑ j, σ s j x * G.cur f j x := rfl
        rw [h1, h3, ← h2]
        ring
      simp only [hs, thetaHeun, Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    rw [h]
    ring

end Grid

/-! ### The two integrators and the local balance laws -/

/-- The two integrators of arXiv 2608.00397: Euler–Maruyama and Heun.  `heun Pr Pr'` says how the
predictor is represented in the K-step (`Pr`) and in the S-step (`Pr'`): `heun id id` is the exact
predictor of Eq. (3.11), and `Grid.vproj` gives the predictor represented in a velocity basis, as in
the paper's implementation. -/
inductive Integrator (V : Type*) where
  /-- The Euler–Maruyama scheme of Section 3.1. -/
  | em : Integrator V
  /-- The Heun scheme of Section 3.2. -/
  | heun (Pr Pr' : (V → ℝ) →ₗ[ℝ] V → ℝ) : Integrator V

namespace Integrator

variable {X V : Type*} {d K : ℕ} [Fintype V]

/-- The increment of the K-step. -/
noncomputable def incK (G : Grid X V d) (σ : Fin K → Fin d → X → ℝ) (τ : ℝ) (Δβ : Fin K → ℝ)
    (E : Fin d → X → ℝ) : Integrator V → Matrix X V ℝ → Matrix X V ℝ
  | em => G.incEM σ τ Δβ E
  | heun Pr _ => G.incHeun σ τ Δβ E Pr

/-- The increment of the S-step. -/
noncomputable def incS (G : Grid X V d) (σ : Fin K → Fin d → X → ℝ) (τ : ℝ) (Δβ : Fin K → ℝ)
    (E : Fin d → X → ℝ) : Integrator V → Matrix X V ℝ → Matrix X V ℝ
  | em => G.incEM σ τ Δβ E
  | heun _ Pr' => G.incHeun σ τ Δβ E Pr'

/-- The stochastic correction `Θ_θ` of the energy law. -/
noncomputable def theta (σ : Fin K → Fin d → X → ℝ) (τ : ℝ) (Δβ : Fin K → ℝ) :
    Integrator V → (X → ℝ) → X → ℝ
  | em => Grid.thetaEM σ τ
  | heun _ _ => Grid.thetaHeun σ Δβ

/-- The discrete velocity identities of Section 4 on the states they are applied to. -/
def Admissible (G : Grid X V d) (σ : Fin K → Fin d → X → ℝ) (Δβ : Fin K → ℝ) (f : Matrix X V ℝ) :
    Integrator V → Prop
  | em => (∀ x, G.FirstIds (f x)) ∧ ∀ x, G.SecondIds (f x)
  | heun Pr Pr' => (∀ x, G.FirstIds (f x)) ∧ G.PreservesMoments Pr ∧ G.PreservesMoments Pr' ∧
      (∀ x, G.FirstIds (G.predictor σ Δβ Pr f x)) ∧ ∀ x, G.FirstIds (G.predictor σ Δβ Pr' f x)

/-- arXiv 2608.00397, proofs of Theorems 4.1, 4.3 and 4.6: the K-step increment of both
integrators. -/
theorem Admissible.isBalanced_incK {G : Grid X V d} {σ : Fin K → Fin d → X → ℝ} {Δβ : Fin K → ℝ}
    {f : Matrix X V ℝ} {θ : Integrator V} (h : θ.Admissible G σ Δβ f) (τ : ℝ)
    (E : Fin d → X → ℝ) :
    G.IsBalanced σ τ Δβ E f (θ.theta σ τ Δβ (G.dens f)) (θ.incK G σ τ Δβ E f) := by
  cases θ with
  | em => exact Grid.isBalanced_incEM h.1 h.2 σ τ Δβ E
  | heun Pr Pr' => exact Grid.isBalanced_incHeun h.1 h.2.1 h.2.2.2.1 τ E

/-- arXiv 2608.00397, proofs of Theorems 4.1, 4.3 and 4.6: the S-step increment of both
integrators. -/
theorem Admissible.isBalanced_incS {G : Grid X V d} {σ : Fin K → Fin d → X → ℝ} {Δβ : Fin K → ℝ}
    {f : Matrix X V ℝ} {θ : Integrator V} (h : θ.Admissible G σ Δβ f) (τ : ℝ)
    (E : Fin d → X → ℝ) :
    G.IsBalanced σ τ Δβ E f (θ.theta σ τ Δβ (G.dens f)) (θ.incS G σ τ Δβ E f) := by
  cases θ with
  | em => exact Grid.isBalanced_incEM h.1 h.2 σ τ Δβ E
  | heun Pr Pr' => exact Grid.isBalanced_incHeun h.1 h.2.2.1 h.2.2.2.2 τ E

end Integrator

section Laws

variable {X V : Type*} {d K m : ℕ} [Fintype X] [Fintype V] [DecidableEq X] [DecidableEq V]

omit [Fintype X] [DecidableEq X] in
/-- arXiv 2608.00397, proof of Eq. (4.5):
`(U c, g)ᵥ` as a matrix product. -/
theorem Grid.pair_mulVec (G : Grid X V d) (U : Matrix V (Fin m) ℝ) (c : Fin m → ℝ)
    (f : Matrix X V ℝ) (x : X) :
    G.pair (U *ᵥ c) (f x) = ((f * diagonal G.wv * U) *ᵥ c) x := by
  have h : ∀ a, (f * diagonal G.wv * U) x a = ∑ v, G.wv v * U v a * f x v := fun a => by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun v _ => by rw [Matrix.mul_diagonal]; ring
  simp only [Grid.pair, mulVec, dotProduct, h, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun v _ => by ring

/-- The velocity functions `1`, `vᵢ` and `|v|²` lie in the span of the fixed modes.  The modes
`U₁ = 1/‖1‖`, `Uᵢ₊₁ = vᵢ/‖vᵢ‖`, `U_{d+2} = χ₂/‖χ₂‖` of arXiv 2608.00397 are of this kind; only this
property of them is used. -/
structure ContainsMoments (G : Grid X V d) (U : Matrix V (Fin m) ℝ) : Prop where
  one : ∃ c, U *ᵥ c = 1
  node : ∀ i, ∃ c, U *ᵥ c = G.node i
  speed2 : ∃ c, U *ᵥ c = G.speed2

omit [Fintype X] [Fintype V] [DecidableEq X] [DecidableEq V] in
/-- arXiv 2608.00397, Section 2: the fixed modes of the paper, `U₁ = 1/‖1‖`, `Uᵢ₊₁ = vᵢ/‖vᵢ‖`,
`U_{d+2} = (|v|² - α₂)/‖χ₂‖`, contain the moments.  The indices `a₀`, `a i`, `aχ` of these columns
are arbitrary. -/
theorem containsMoments_of_modes {G : Grid X V d} {U : Matrix V (Fin m) ℝ} {a₀ aχ : Fin m}
    {a : Fin d → Fin m} {c₀ cχ α : ℝ} {c : Fin d → ℝ} (h₀ : c₀ ≠ 0)
    (hc : ∀ i, c i ≠ 0) (hχ : cχ ≠ 0) (hU₀ : ∀ v, U v a₀ = 1 / c₀)
    (hUi : ∀ i v, U v (a i) = G.node i v / c i)
    (hUχ : ∀ v, U v aχ = (G.speed2 v - α) / cχ) : ContainsMoments G U where
  one := ⟨Pi.single a₀ c₀, by
    ext v
    simp [mulVec_single, hU₀, h₀]⟩
  node i := ⟨Pi.single (a i) (c i), by
    ext v
    simp [mulVec_single, hUi, hc i]⟩
  speed2 := ⟨Pi.single aχ cχ + Pi.single a₀ (α * c₀), by
    ext v
    rw [mulVec_add, Pi.add_apply]
    simp only [mulVec_single, Pi.smul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
      col_apply, hU₀, hUχ]
    field_simp
    ring⟩

/-- `f'` arises from `f` by one step of the augmented BUG integrator with conservative truncation
and with the increments `IK` in the K-step and `IS` in the S-step.  Ranks may change. -/
def IsStep (G : Grid X V d) (U : Matrix V (Fin m) ℝ) (IK IS : Matrix X V ℝ → Matrix X V ℝ)
    (f f' : Matrix X V ℝ) : Prop :=
  ∃ (p p' k q : ℕ) (s : State X V m p) (s' : State X V m p'),
    s.dist G U = f ∧ s'.dist G U = f' ∧ Nonempty (AugBUGStep G U IK IS s s' k q)

/-- One step of the integrator `θ` with increments `Δβ`, time step `τ` and frozen field `E`. -/
def Integrator.Step (θ : Integrator V) (G : Grid X V d) (U : Matrix V (Fin m) ℝ)
    (σ : Fin K → Fin d → X → ℝ) (τ : ℝ) (Δβ : Fin K → ℝ) (E : Fin d → X → ℝ)
    (f f' : Matrix X V ℝ) : Prop :=
  IsStep G U (θ.incK G σ τ Δβ E) (θ.incS G σ τ Δβ E) f f'

variable {G : Grid X V d} {U : Matrix V (Fin m) ℝ}

/-- **Generality of the conservation mechanism** (arXiv 2608.00397, Eq. (4.5) and
Remark 4.4).  If a velocity function `p` lies in the span of the fixed modes
and the K- and the S-step have the same moment of the increment against `p`, then
`(p, fⁿ⁺¹)ᵥ = (p, fⁿ)ᵥ + (p, I)ᵥ` exactly: the spatial projection of the S-step has no effect.  The
increments are arbitrary. -/
theorem IsStep.pair_eq {IK IS : Matrix X V ℝ → Matrix X V ℝ} {f f' : Matrix X V ℝ}
    (h : IsStep G U IK IS f f') {p : V → ℝ} (hp : ∃ c, U *ᵥ c = p)
    (hIS : ∀ x, G.pair p (IS f x) = G.pair p (IK f x)) (x : X) :
    G.pair p (f' x) = G.pair p (f x) + G.pair p (IK f x) := by
  obtain ⟨_, _, _, _, s, s', rfl, rfl, ⟨D⟩⟩ := h
  obtain ⟨c, rfl⟩ := hp
  have hS : (IS (s.dist G U) * diagonal G.wv * U) *ᵥ c =
      (IK (s.dist G U) * diagonal G.wv * U) *ᵥ c := by
    ext y
    rw [← G.pair_mulVec, ← G.pair_mulVec]
    exact hIS y
  have h1 := congrFun (D.moment_law c hS) x
  rw [Pi.add_apply] at h1
  rw [G.pair_mulVec, G.pair_mulVec, G.pair_mulVec, h1]

/-- The electric-field residual `R_E = ½ (|Eⁿ⁺¹|² - |Eⁿ|²) + τ Eⁿ·Jⁿ` of arXiv 2608.00397,
Theorem 4.6. -/
noncomputable def fieldResidual (τ : ℝ) (E E' J : Fin d → X → ℝ) (x : X) : ℝ :=
  1 / 2 * (∑ j, E' j x ^ 2 - ∑ j, E j x ^ 2) + τ * ∑ j, E j x * J j x

omit [Fintype X] [Fintype V] [DecidableEq X] [DecidableEq V] in
/-- The second form of the residual in arXiv 2608.00397, Theorem 4.6:
`R_E = τ Eⁿ·((Eⁿ⁺¹ - Eⁿ)/τ + Jⁿ) + ½ |Eⁿ⁺¹ - Eⁿ|²`. -/
theorem fieldResidual_eq {τ : ℝ} (hτ : τ ≠ 0) (E E' J : Fin d → X → ℝ) (x : X) :
    fieldResidual τ E E' J x =
      τ * ∑ j, E j x * ((E' j x - E j x) / τ + J j x) + 1 / 2 * ∑ j, (E' j x - E j x) ^ 2 := by
  have h : ∀ j, τ * (E j x * ((E' j x - E j x) / τ + J j x)) + 1 / 2 * (E' j x - E j x) ^ 2 =
      1 / 2 * (E' j x ^ 2 - E j x ^ 2) + τ * (E j x * J j x) := by
    intro j
    field_simp
    ring
  rw [fieldResidual, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact (Finset.sum_congr rfl fun j _ => h j).symm

/-- The energy density `e = ½ ∫ |v|² f dv + ½ |E|²`. -/
noncomputable def Grid.energy (G : Grid X V d) (f : Matrix X V ℝ) (E : Fin d → X → ℝ) (x : X) : ℝ :=
  G.kin f x + 1 / 2 * ∑ j, E j x ^ 2

variable {σ : Fin K → Fin d → X → ℝ} {τ : ℝ} {Δβ : Fin K → ℝ} {E E' : Fin d → X → ℝ}
  {θ : Integrator V} {f f' : Matrix X V ℝ}

/-- arXiv 2608.00397, proofs of Theorems 4.1, 4.3 and 4.6:
Density update of one step. -/
theorem Integrator.Step.dens_eq (h : θ.Step G U σ τ Δβ E f f') (hU : ContainsMoments G U)
    (hadm : θ.Admissible G σ Δβ f) (x : X) :
    G.dens f' x = G.dens f x - τ * G.divx (G.cur f) x := by
  have := IsStep.pair_eq h hU.one
    (fun y => by
      rw [(hadm.isBalanced_incS τ E).mass y, (hadm.isBalanced_incK τ E).mass y]) x
  rw [(hadm.isBalanced_incK τ E).mass x] at this
  rw [Grid.dens, this, Grid.dens]
  ring

/-- arXiv 2608.00397, proofs of Theorems 4.1, 4.3 and 4.6:
Current update of one step. -/
theorem Integrator.Step.cur_eq (h : θ.Step G U σ τ Δβ E f f') (hU : ContainsMoments G U)
    (hadm : θ.Admissible G σ Δβ f) (j : Fin d) (x : X) :
    G.cur f' j x = G.cur f j x - τ * G.divx (G.stress f j) x +
      Grid.force σ τ Δβ E j x * G.dens f x := by
  have := IsStep.pair_eq h (hU.node j)
    (fun y => by
      rw [(hadm.isBalanced_incS τ E).momentum j y, (hadm.isBalanced_incK τ E).momentum j y]) x
  rw [(hadm.isBalanced_incK τ E).momentum j x] at this
  rw [Grid.cur, this, Grid.cur]
  ring

/-- arXiv 2608.00397, proofs of Theorems 4.1, 4.3 and 4.6:
Kinetic energy update of one step. -/
theorem Integrator.Step.kin_eq (h : θ.Step G U σ τ Δβ E f f') (hU : ContainsMoments G U)
    (hadm : θ.Admissible G σ Δβ f) (x : X) :
    G.kin f' x = G.kin f x - τ * G.divx (G.heat f) x +
      ∑ j, Grid.force σ τ Δβ E j x * G.cur f j x + θ.theta σ τ Δβ (G.dens f) x := by
  have hK := (hadm.isBalanced_incK τ E).energy
  have hS := (hadm.isBalanced_incS τ E).energy
  have := IsStep.pair_eq h hU.speed2
    (fun y => by
      have h1 := hK y
      have h2 := hS y
      linarith) x
  have h1 := hK x
  rw [Grid.kin, this, Grid.kin]
  linarith

/-- **Theorem 4.1 of arXiv 2608.00397: local mass law.**  For
the Euler–Maruyama and the Heun augmented BUG integrator with conservative truncation,
`(ρⁿ⁺¹ - ρⁿ)/τ + ∇ₓ·Jⁿ = 0` at every grid point.  The law is pathwise: `Δβ` is an arbitrary vector
of reals, so it holds for every realization of the Brownian increments, and `E` is arbitrary. -/
theorem local_mass (hU : ContainsMoments G U) (hadm : θ.Admissible G σ Δβ f)
    (hstep : θ.Step G U σ τ Δβ E f f') (hτ : τ ≠ 0) (x : X) :
    (G.dens f' x - G.dens f x) / τ + G.divx (G.cur f) x = 0 := by
  rw [hstep.dens_eq hU hadm x]
  field_simp
  ring

/-- **Theorem 4.3 of arXiv 2608.00397: local momentum law.**
Pathwise, `Jⁿ⁺¹ - Jⁿ + τ (∇ₓ·Πⁿ - Eⁿ ρⁿ) - ∑ₛ σₛ Δβˢ ρⁿ = 0` at every grid point. -/
theorem local_momentum (hU : ContainsMoments G U) (hadm : θ.Admissible G σ Δβ f)
    (hstep : θ.Step G U σ τ Δβ E f f') (j : Fin d) (x : X) :
    G.cur f' j x - G.cur f j x + τ * (G.divx (G.stress f j) x - E j x * G.dens f x) -
      ∑ s, σ s j x * Δβ s * G.dens f x = 0 := by
  rw [hstep.cur_eq hU hadm j x, Grid.force, add_mul, Finset.sum_mul]
  have : ∑ s, Δβ s * σ s j x * G.dens f x = ∑ s, σ s j x * Δβ s * G.dens f x :=
    Finset.sum_congr rfl fun s _ => by ring
  rw [this]
  ring

/-- **Theorem 4.6 of arXiv 2608.00397: energy identity.**
Pathwise, `eⁿ⁺¹ - eⁿ + τ ∇ₓ·Qⁿ - ∑ₛ Δβˢ σₛ·Jⁿ - Θ_θⁿ - R_Eⁿ = 0` at every grid point, with
`Θ_EM = (τ/2) Tr(A) ρⁿ` and `Θ_Heun = ½ ∑ₛᵣ Δβˢ Δβʳ (σₛ·σᵣ) ρⁿ`, for arbitrary fields `E = Eⁿ`,
`E' = Eⁿ⁺¹`. -/
theorem local_energy (hU : ContainsMoments G U) (hadm : θ.Admissible G σ Δβ f)
    (hstep : θ.Step G U σ τ Δβ E f f') (E' : Fin d → X → ℝ) (x : X) :
    G.energy f' E' x - G.energy f E x + τ * G.divx (G.heat f) x -
      ∑ s, Δβ s * ∑ j, σ s j x * G.cur f j x - θ.theta σ τ Δβ (G.dens f) x -
        fieldResidual τ E E' (G.cur f) x = 0 := by
  rw [Grid.energy, Grid.energy, hstep.kin_eq hU hadm x, Grid.sum_force_mul, fieldResidual]
  ring

/-- **Lemma 4.2 of arXiv 2608.00397.**  For both integrators
`-τ (∇ₓ·Πⁿ)ⱼ + (τ Eⁿ + ∑ₛ Δβˢ σₛ)ⱼ ρⁿ` lies in the span of the augmented spatial basis `X̃ⁿ⁺¹`. -/
theorem momentum_increment_mem {p p' k q : ℕ} {s : State X V m p} {s' : State X V m p'}
    (hU : ContainsMoments G U) (hadm : θ.Admissible G σ Δβ (s.dist G U))
    (D : AugBUGStep G U (θ.incK G σ τ Δβ E) (θ.incS G σ τ Δβ E) s s' k q) (j : Fin d) :
    (fun x => -τ * G.divx (G.stress (s.dist G U) j) x +
      Grid.force σ τ Δβ E j x * G.dens (s.dist G U) x) ∈ LinearMap.range D.Xa.mulVecLin := by
  obtain ⟨c, hc⟩ := hU.node j
  convert D.flux_mem c using 1
  ext x
  rw [← G.pair_mulVec, hc, (hadm.isBalanced_incK τ E).momentum j x]

/-- **Lemma 4.5 of arXiv 2608.00397.**  For both integrators
`-τ ∇ₓ·Qⁿ + (τ Eⁿ + ∑ₛ Δβˢ σₛ)·Jⁿ + Θ_θⁿ` lies in the span of the augmented spatial basis
`X̃ⁿ⁺¹`. -/
theorem energy_increment_mem {p p' k q : ℕ} {s : State X V m p} {s' : State X V m p'}
    (hU : ContainsMoments G U) (hadm : θ.Admissible G σ Δβ (s.dist G U))
    (D : AugBUGStep G U (θ.incK G σ τ Δβ E) (θ.incS G σ τ Δβ E) s s' k q) :
    (fun x => -τ * G.divx (G.heat (s.dist G U)) x +
      ∑ j, Grid.force σ τ Δβ E j x * G.cur (s.dist G U) j x +
        θ.theta σ τ Δβ (G.dens (s.dist G U)) x) ∈ LinearMap.range D.Xa.mulVecLin := by
  obtain ⟨c, hc⟩ := hU.speed2
  convert Submodule.smul_mem _ (1 / 2 : ℝ) (D.flux_mem c) using 1
  ext x
  rw [Pi.smul_apply, ← G.pair_mulVec, hc, smul_eq_mul, (hadm.isBalanced_incK τ E).energy x]

/-- Periodic spatial cancellation (arXiv 2608.00397, Section 4): `∫ ∂ₓᵢ u dx = 0`. -/
def Grid.PeriodicX (G : Grid X V d) : Prop := ∀ i (u : X → ℝ), ∑ x, G.wx x * G.Dx i u x = 0

/-- The total mass `∫ ρ dx`. -/
noncomputable def Grid.totalMass (G : Grid X V d) (f : Matrix X V ℝ) : ℝ :=
  ∑ x, G.wx x * G.dens f x

/-- The total momentum `∫ Jⱼ dx`. -/
noncomputable def Grid.totalMomentum (G : Grid X V d) (f : Matrix X V ℝ) (j : Fin d) : ℝ :=
  ∑ x, G.wx x * G.cur f j x

/-- The total energy `∫ e dx`. -/
noncomputable def Grid.totalEnergy (G : Grid X V d) (f : Matrix X V ℝ) (E : Fin d → X → ℝ) : ℝ :=
  ∑ x, G.wx x * G.energy f E x

omit [Fintype V] [DecidableEq X] [DecidableEq V] in
/-- arXiv 2608.00397, proofs of Theorems 4.1, 4.3 and 4.6: `∫ ∇ₓ·u dx = 0`. -/
theorem Grid.PeriodicX.sum_divx (hP : G.PeriodicX) (u : Fin d → X → ℝ) :
    ∑ x, G.wx x * G.divx u x = 0 := by
  simp only [Grid.divx, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun i _ => hP i (u i)

/-- **Theorem 4.1 of arXiv 2608.00397, second assertion: total mass is conserved pathwise.** -/
theorem total_mass (hU : ContainsMoments G U) (hP : G.PeriodicX) (hadm : θ.Admissible G σ Δβ f)
    (hstep : θ.Step G U σ τ Δβ E f f') : G.totalMass f' = G.totalMass f := by
  have h : ∀ x, G.wx x * G.dens f' x =
      G.wx x * G.dens f x - τ * (G.wx x * G.divx (G.cur f) x) := fun x => by
    rw [hstep.dens_eq hU hadm x]
    ring
  simp only [Grid.totalMass, h, Finset.sum_sub_distrib, ← Finset.mul_sum, hP.sum_divx, mul_zero,
    sub_zero]

/-- The pathwise evolution of the total momentum (arXiv 2608.00397, proof of Theorem 4.3):
`∫ Jⱼⁿ⁺¹ = ∫ Jⱼⁿ + τ ∫ Eⱼⁿ ρⁿ + ∑ₛ (∫ σₛⱼ ρⁿ) Δβˢ`. -/
theorem total_momentum (hU : ContainsMoments G U) (hP : G.PeriodicX)
    (hadm : θ.Admissible G σ Δβ f) (hstep : θ.Step G U σ τ Δβ E f f') (j : Fin d) :
    G.totalMomentum f' j = G.totalMomentum f j + τ * ∑ x, G.wx x * (E j x * G.dens f x) +
      ∑ s, (∑ x, G.wx x * (σ s j x * G.dens f x)) * Δβ s := by
  have h : ∀ x, G.wx x * G.cur f' j x =
      G.wx x * G.cur f j x - τ * (G.wx x * G.divx (G.stress f j) x) +
        τ * (G.wx x * (E j x * G.dens f x)) +
          ∑ s, G.wx x * (σ s j x * G.dens f x) * Δβ s := fun x => by
    have hs : ∑ s, G.wx x * (σ s j x * G.dens f x) * Δβ s =
        G.wx x * ((∑ s, Δβ s * σ s j x) * G.dens f x) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [hstep.cur_eq hU hadm j x, Grid.force, hs]
    ring
  simp only [Grid.totalMomentum, h, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hP.sum_divx, mul_zero, sub_zero]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => by rw [Finset.sum_mul]

/-- The pathwise evolution of the total energy (arXiv 2608.00397, after Theorem 4.6):
`∫ eⁿ⁺¹ = ∫ eⁿ + ∑ₛ Δβˢ ∫ σₛ·Jⁿ + ∫ Θ_θⁿ + ∫ R_Eⁿ`. -/
theorem total_energy (hU : ContainsMoments G U) (hP : G.PeriodicX)
    (hadm : θ.Admissible G σ Δβ f) (hstep : θ.Step G U σ τ Δβ E f f') (E' : Fin d → X → ℝ) :
    G.totalEnergy f' E' = G.totalEnergy f E +
      ∑ s, Δβ s * (∑ x, G.wx x * ∑ j, σ s j x * G.cur f j x) +
        ∑ x, G.wx x * θ.theta σ τ Δβ (G.dens f) x +
          ∑ x, G.wx x * fieldResidual τ E E' (G.cur f) x := by
  have h : ∀ x, G.wx x * G.energy f' E' x =
      G.wx x * G.energy f E x - τ * (G.wx x * G.divx (G.heat f) x) +
        ∑ s, Δβ s * (G.wx x * ∑ j, σ s j x * G.cur f j x) +
          G.wx x * θ.theta σ τ Δβ (G.dens f) x +
            G.wx x * fieldResidual τ E E' (G.cur f) x := fun x => by
    have hs : ∑ s, Δβ s * (G.wx x * ∑ j, σ s j x * G.cur f j x) =
        G.wx x * ∑ s, Δβ s * ∑ j, σ s j x * G.cur f j x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [hs]
    linear_combination G.wx x * local_energy hU hadm hstep E' x
  have hsw : ∑ x, ∑ s, Δβ s * (G.wx x * ∑ j, σ s j x * G.cur f j x) =
      ∑ s, Δβ s * ∑ x, G.wx x * ∑ j, σ s j x * G.cur f j x := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => by rw [Finset.mul_sum]
  simp only [Grid.totalEnergy, h, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hP.sum_divx, mul_zero, sub_zero, hsw]

end Laws

/-! ### Expectations -/

section Expectation

open MeasureTheory

variable {X V : Type*} {d K m : ℕ} [Fintype X] [Fintype V] [DecidableEq X] [DecidableEq V]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ mΩ}

/-- The properties of the Brownian increments used in arXiv 2608.00397, Section 4.3:
`E[Δβˢ | 𝓕ₙ] = 0` and `E[Δβˢ Δβʳ | 𝓕ₙ] = τ δₛᵣ`.  See `isNoise_of_indep`: they follow from
independence of `𝓕ₙ`, zero mean and the covariance `τ δₛᵣ`. -/
structure IsNoise (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) (τ : ℝ) (Δβ : ℕ → Ω → Fin K → ℝ) :
    Prop where
  integrable : ∀ n s, Integrable (fun ω => Δβ n ω s) μ
  integrable_mul : ∀ n s r, Integrable (fun ω => Δβ n ω s * Δβ n ω r) μ
  mean : ∀ n s, μ[fun ω => Δβ n ω s | ℱ n] =ᵐ[μ] 0
  cov : ∀ n s r, μ[fun ω => Δβ n ω s * Δβ n ω r | ℱ n] =ᵐ[μ] fun _ => if s = r then τ else 0

/-- arXiv 2608.00397, Section 4.3:
Increments that are independent of the past, centered and with covariance `τ δₛᵣ` (Brownian
increments in particular) satisfy `IsNoise`. -/
theorem isNoise_of_indep {τ : ℝ} {Δβ : ℕ → Ω → Fin K → ℝ} (hm : ∀ n, Measurable (Δβ n))
    (hind : ∀ n, ProbabilityTheory.Indep (MeasurableSpace.comap (Δβ n) inferInstance) (ℱ n) μ)
    (hint : ∀ n s, Integrable (fun ω => Δβ n ω s) μ)
    (hint2 : ∀ n s r, Integrable (fun ω => Δβ n ω s * Δβ n ω r) μ)
    (hmean : ∀ n s, ∫ ω, Δβ n ω s ∂μ = 0)
    (hcov : ∀ n s r, ∫ ω, Δβ n ω s * Δβ n ω r ∂μ = if s = r then τ else 0) :
    IsNoise μ ℱ τ Δβ where
  integrable := hint
  integrable_mul := hint2
  mean n s := by
    have hs : Measurable[MeasurableSpace.comap (Δβ n) inferInstance] fun ω => Δβ n ω s :=
      (measurable_pi_apply s).comp (comap_measurable (Δβ n))
    have h := condExp_indep_eq (hm n).comap_le (ℱ.le n) hs.stronglyMeasurable (hind n)
    filter_upwards [h] with ω hω
    rw [hω, hmean n s]
    rfl
  cov n s r := by
    have h1 : Measurable[MeasurableSpace.comap (Δβ n) inferInstance] fun ω => Δβ n ω s :=
      (measurable_pi_apply s).comp (comap_measurable (Δβ n))
    have h2 : Measurable[MeasurableSpace.comap (Δβ n) inferInstance] fun ω => Δβ n ω r :=
      (measurable_pi_apply r).comp (comap_measurable (Δβ n))
    have h : μ[fun ω => Δβ n ω s * Δβ n ω r | ℱ n] =ᵐ[μ]
        fun _ => ∫ ω, Δβ n ω s * Δβ n ω r ∂μ :=
      condExp_indep_eq (hm n).comap_le (ℱ.le n) (h1.mul h2).stronglyMeasurable (hind n)
    filter_upwards [h] with ω hω
    rw [hω, hcov n s r]

omit [IsProbabilityMeasure μ] in
/-- arXiv 2608.00397, Section 4.3:
Conditional expectations of finite linear combinations. -/
theorem condExp_weighted_sum {ι : Type*} (t : Finset ι) (c : ι → ℝ) {g h : ι → Ω → ℝ}
    {m₀ : MeasurableSpace Ω} (hg : ∀ i ∈ t, Integrable (g i) μ)
    (hh : ∀ i ∈ t, μ[g i | m₀] =ᵐ[μ] h i) :
    μ[fun ω => ∑ i ∈ t, c i * g i ω | m₀] =ᵐ[μ] fun ω => ∑ i ∈ t, c i * h i ω := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have h0 : (fun ω => ∑ i ∈ (∅ : Finset ι), c i * g i ω) = 0 := by
      ext ω
      simp
    rw [h0, condExp_zero]
    exact Filter.Eventually.of_forall fun ω => by simp
  | insert a t ha ih =>
    have h1 : (fun ω => ∑ i ∈ insert a t, c i * g i ω) =
        (fun ω => c a * g a ω) + fun ω => ∑ i ∈ t, c i * g i ω := by
      ext ω
      simp [Finset.sum_insert ha]
    have hga := hg a (Finset.mem_insert_self a t)
    have hgt : ∀ i ∈ t, Integrable (g i) μ := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hsum : Integrable (fun ω => ∑ i ∈ t, c i * g i ω) μ :=
      integrable_finsetSum _ fun i hi => (hgt i hi).const_mul _
    rw [h1]
    have h2 := condExp_add (hga.const_mul (c a)) hsum m₀
    have h3 := ih hgt fun i hi => hh i (Finset.mem_insert_of_mem hi)
    have h4 : μ[fun ω => c a * g a ω | m₀] =ᵐ[μ] fun ω => c a * h a ω := by
      have h5 : μ[(c a) • g a | m₀] =ᵐ[μ] (c a) • μ[g a | m₀] := condExp_smul (c a) (g a) m₀
      have h6 := hh a (Finset.mem_insert_self a t)
      filter_upwards [h5, h6] with ω h7 h8
      change (μ[(c a) • g a | m₀]) ω = _
      rw [h7, Pi.smul_apply, h8, smul_eq_mul]
    filter_upwards [h2, h3, h4] with ω h5 h6 h7
    rw [h5, Pi.add_apply, h6, h7, Finset.sum_insert ha]

variable {τ : ℝ} {Δβ : ℕ → Ω → Fin K → ℝ}

omit [IsProbabilityMeasure μ] in
/-- arXiv 2608.00397, Section 4.3:
`E[c Δβˢ | 𝓕ₙ] = 0` for an `𝓕ₙ`-measurable `c`. -/
theorem IsNoise.condExp_mul_eq_zero (hn : IsNoise μ ℱ τ Δβ) {n : ℕ} {s : Fin K} {c : Ω → ℝ}
    (hc : StronglyMeasurable[ℱ n] c) (hi : Integrable (fun ω => c ω * Δβ n ω s) μ) :
    μ[fun ω => c ω * Δβ n ω s | ℱ n] =ᵐ[μ] 0 := by
  have h : μ[fun ω => c ω * Δβ n ω s | ℱ n] =ᵐ[μ] c * μ[fun ω => Δβ n ω s | ℱ n] :=
    condExp_mul_of_stronglyMeasurable_left hc hi (hn.integrable n s)
  filter_upwards [h, hn.mean n s] with ω h1 h2
  rw [h1, Pi.mul_apply, h2]
  simp

/-- arXiv 2608.00397, Section 4.3:
`E[c Δβˢ] = 0` for an `𝓕ₙ`-measurable `c`. -/
theorem IsNoise.integral_mul_eq_zero (hn : IsNoise μ ℱ τ Δβ) {n : ℕ} {s : Fin K} {c : Ω → ℝ}
    (hc : StronglyMeasurable[ℱ n] c) (hi : Integrable (fun ω => c ω * Δβ n ω s) μ) :
    ∫ ω, c ω * Δβ n ω s ∂μ = 0 := by
  rw [← integral_condExp (ℱ.le n)]
  exact integral_eq_zero_of_ae (hn.condExp_mul_eq_zero hc hi)

variable {G : Grid X V d} {U : Matrix V (Fin m) ℝ} {σ : Fin K → Fin d → X → ℝ}

/-- **Theorem 4.3 of arXiv 2608.00397: total momentum is
conserved in expectation**, `E 𝒫[fⁿ] = E 𝒫[f⁰]`.  The bases depend on the current increments, but
this does not matter, since the increment enters the law linearly with the `𝓕ₙ`-measurable
coefficient `∫ σₛ ρⁿ dx`.  `θ` may even vary with `n` and `ω`.  The assumptions are those of the
paper: `∫ Eⁿ ρⁿ dx = 0`, which `total_force_eq_zero` derives from the Poisson equation, the
`𝓕ₙ`-measurability of `ρⁿ`, and integrability of the stochastic terms. -/
theorem expected_momentum (hU : ContainsMoments G U) (hP : G.PeriodicX) (hn : IsNoise μ ℱ τ Δβ)
    {θ : ℕ → Ω → Integrator V} {f : ℕ → Ω → Matrix X V ℝ} {E : ℕ → Ω → Fin d → X → ℝ}
    (hstep : ∀ n, ∀ᵐ ω ∂μ, (θ n ω).Admissible G σ (Δβ n ω) (f n ω) ∧
      (θ n ω).Step G U σ τ (Δβ n ω) (E n ω) (f n ω) (f (n + 1) ω))
    (hforce : ∀ n, ∀ᵐ ω ∂μ, ∀ j, ∑ x, G.wx x * (E n ω j x * G.dens (f n ω) x) = 0)
    (hρ : ∀ n x, StronglyMeasurable[ℱ n] fun ω => G.dens (f n ω) x)
    (hint : ∀ n s x, Integrable (fun ω => G.dens (f n ω) x * Δβ n ω s) μ) {j : Fin d}
    (h0 : Integrable (fun ω => G.totalMomentum (f 0 ω) j) μ) (n : ℕ) :
    ∫ ω, G.totalMomentum (f n ω) j ∂μ = ∫ ω, G.totalMomentum (f 0 ω) j ∂μ := by
  have key : ∀ n, Integrable (fun ω => G.totalMomentum (f n ω) j) μ ∧
      ∫ ω, G.totalMomentum (f n ω) j ∂μ = ∫ ω, G.totalMomentum (f 0 ω) j ∂μ := by
    intro n
    induction n with
    | zero => exact ⟨h0, rfl⟩
    | succ n ih =>
      let c : Fin K → Ω → ℝ := fun s ω => ∑ x, G.wx x * (σ s j x * G.dens (f n ω) x)
      have hc : ∀ s, StronglyMeasurable[ℱ n] (c s) := fun s =>
        Finset.stronglyMeasurable_fun_sum _ fun x _ =>
          ((hρ n x).const_mul (σ s j x)).const_mul (G.wx x)
      have hci : ∀ s, Integrable (fun ω => c s ω * Δβ n ω s) μ := fun s => by
        have h1 : (fun ω => c s ω * Δβ n ω s) =
            fun ω => ∑ x, G.wx x * σ s j x * (G.dens (f n ω) x * Δβ n ω s) := by
          ext ω
          simp only [c, Finset.sum_mul]
          exact Finset.sum_congr rfl fun x _ => by ring
        rw [h1]
        exact integrable_finsetSum _ fun x _ => (hint n s x).const_mul _
      have hlaw : (fun ω => G.totalMomentum (f (n + 1) ω) j) =ᵐ[μ]
          fun ω => G.totalMomentum (f n ω) j + ∑ s, c s ω * Δβ n ω s := by
        filter_upwards [hstep n, hforce n] with ω h1 h2
        rw [total_momentum hU hP h1.1 h1.2 j, h2 j, mul_zero, add_zero]
      have hs : Integrable (fun ω => ∑ s, c s ω * Δβ n ω s) μ :=
        integrable_finsetSum _ fun s _ => hci s
      refine ⟨(ih.1.add hs).congr hlaw.symm, ?_⟩
      rw [integral_congr_ae hlaw, integral_add ih.1 hs, integral_finsetSum _ fun s _ => hci s,
        Finset.sum_eq_zero fun s _ => hn.integral_mul_eq_zero (hc s) (hci s), add_zero, ih.2]
  exact (key n).2

omit [Fintype X] [Fintype V] [DecidableEq X] [DecidableEq V] [IsProbabilityMeasure μ] in
/-- arXiv 2608.00397, Section 4: `Θ_Heun = ½ |∑ₛ Δβˢ σₛ|² ρ`. -/
theorem thetaHeun_eq_sq (σ : Fin K → Fin d → X → ℝ) (b : Fin K → ℝ) (ρ : X → ℝ) (x : X) :
    Grid.thetaHeun σ b ρ x = 1 / 2 * (∑ i, (∑ s, b s * σ s i x) ^ 2) * ρ x := by
  have h : ∀ i, (∑ s, b s * σ s i x) ^ 2 = ∑ s, ∑ r, b s * b r * (σ s i x * σ r i x) := by
    intro i
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => by ring
  have h2 : ∑ i, ∑ s, ∑ r, b s * b r * (σ s i x * σ r i x) =
      ∑ s, ∑ r, ∑ i, b s * b r * (σ s i x * σ r i x) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_comm
  simp only [Grid.thetaHeun, h]
  rw [h2, mul_assoc]
  congr 1
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]

omit [Fintype X] [Fintype V] [DecidableEq X] [DecidableEq V] [IsProbabilityMeasure μ] in
/-- arXiv 2608.00397, Section 4: `Θ_Heun ≥ 0` pathwise wherever `ρ ≥ 0`. -/
theorem thetaHeun_nonneg (σ : Fin K → Fin d → X → ℝ) (b : Fin K → ℝ) {ρ : X → ℝ} {x : X}
    (hρ : 0 ≤ ρ x) : 0 ≤ Grid.thetaHeun σ b ρ x := by
  rw [thetaHeun_eq_sq]
  have h : 0 ≤ ∑ i, (∑ s, b s * σ s i x) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  positivity

omit [Fintype X] [DecidableEq X] [IsProbabilityMeasure μ] in
/-- The Heun correction has the conditional expectation of the Itô correction
(arXiv 2608.00397, Section 4.3): `E[Θ_Heun | 𝓕ₙ] = (τ/2) Tr(A) ρ = Θ_EM`. -/
theorem condExp_thetaHeun (hn : IsNoise μ ℱ τ Δβ) (σ : Fin K → Fin d → X → ℝ) (n : ℕ)
    {ρ : Ω → X → ℝ} (x : X) (hρ : StronglyMeasurable[ℱ n] fun ω => ρ ω x)
    (hi : ∀ s r, Integrable (fun ω => Δβ n ω s * Δβ n ω r * ρ ω x) μ) :
    μ[fun ω => Grid.thetaHeun σ (Δβ n ω) (ρ ω) x | ℱ n] =ᵐ[μ]
      fun ω => Grid.thetaEM σ τ (ρ ω) x := by
  let g : Fin K × Fin K → Ω → ℝ := fun p ω => Δβ n ω p.1 * Δβ n ω p.2 * ρ ω x
  let c : Fin K × Fin K → ℝ := fun p => 1 / 2 * ∑ i, σ p.1 i x * σ p.2 i x
  have hth : (fun ω => Grid.thetaHeun σ (Δβ n ω) (ρ ω) x) =
      fun ω => ∑ p ∈ Finset.univ ×ˢ Finset.univ, c p * g p ω := by
    ext ω
    rw [Finset.sum_product, Grid.thetaHeun, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by simp only [c, g]; ring
  have hg : ∀ p ∈ (Finset.univ ×ˢ Finset.univ : Finset (Fin K × Fin K)),
      μ[g p | ℱ n] =ᵐ[μ] fun ω => (if p.1 = p.2 then τ else 0) * ρ ω x := by
    intro p _
    have h : μ[g p | ℱ n] =ᵐ[μ] μ[fun ω => Δβ n ω p.1 * Δβ n ω p.2 | ℱ n] * fun ω => ρ ω x :=
      condExp_mul_of_stronglyMeasurable_right hρ (hi p.1 p.2) (hn.integrable_mul n p.1 p.2)
    filter_upwards [h, hn.cov n p.1 p.2] with ω h1 h2
    rw [h1, Pi.mul_apply, h2]
  rw [hth]
  refine (condExp_weighted_sum _ c (fun p _ => hi p.1 p.2) hg).trans
    (Filter.Eventually.of_forall fun ω => ?_)
  change ∑ p ∈ Finset.univ ×ˢ Finset.univ, c p * ((if p.1 = p.2 then τ else 0) * ρ ω x) =
    Grid.thetaEM σ τ (ρ ω) x
  rw [Finset.sum_product, Grid.thetaEM]
  simp only [Grid.diffusion, c]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun l s => σ s l x * σ s l x),
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_eq_single s (fun r _ hr => by simp [hr.symm]) (by simp)]
  simp only [ite_true]
  ring

omit [IsProbabilityMeasure μ] in
/-- arXiv 2608.00397, Section 4.3:
Auxiliary: the conditional expectation of an energy increment with a noise term. -/
theorem condExp_increment (hn : IsNoise μ ℱ τ Δβ) {n : ℕ} {Γ : Fin K → Ω → ℝ} {D T R : Ω → ℝ}
    (hΓ : ∀ s, StronglyMeasurable[ℱ n] (Γ s))
    (hi : ∀ s, Integrable (fun ω => Γ s ω * Δβ n ω s) μ) (hT : Integrable T μ)
    (hR : Integrable R μ) (hD : ∀ᵐ ω ∂μ, D ω = ∑ s, Δβ n ω s * Γ s ω + T ω + R ω) :
    μ[D | ℱ n] =ᵐ[μ] μ[T | ℱ n] + μ[R | ℱ n] := by
  have hN : μ[fun ω => ∑ s ∈ Finset.univ, (1 : ℝ) * (Γ s ω * Δβ n ω s) | ℱ n] =ᵐ[μ]
      fun ω => ∑ s ∈ Finset.univ, (1 : ℝ) * (0 : Ω → ℝ) ω :=
    condExp_weighted_sum (g := fun s ω => Γ s ω * Δβ n ω s) Finset.univ (fun _ => 1)
      (fun s _ => hi s) fun s _ => hn.condExp_mul_eq_zero (hΓ s) (hi s)
  have hNi : Integrable (fun ω => ∑ s ∈ Finset.univ, (1 : ℝ) * (Γ s ω * Δβ n ω s)) μ :=
    integrable_finsetSum _ fun s _ => (hi s).const_mul _
  have hDe : D =ᵐ[μ] ((fun ω => ∑ s ∈ Finset.univ, (1 : ℝ) * (Γ s ω * Δβ n ω s)) + T) + R := by
    filter_upwards [hD] with ω hω
    simp only [Pi.add_apply, hω, one_mul, mul_comm (Γ _ ω)]
  have h1 := condExp_add (hNi.add hT) hR (ℱ n)
  have h2 := condExp_add hNi hT (ℱ n)
  filter_upwards [condExp_congr_ae (m := ℱ n) hDe, h1, h2, hN] with ω h3 h4 h5 h6
  rw [h3, h4, Pi.add_apply, h5, Pi.add_apply, h6]
  simp

/-- The noise coefficient of the total energy, `∫ σₛ·Jⁿ dx`. -/
noncomputable def noiseWork (G : Grid X V d) (σ : Fin K → Fin d → X → ℝ) (f : Matrix X V ℝ)
    (s : Fin K) : ℝ :=
  ∑ x, G.wx x * ∑ j, σ s j x * G.cur f j x

omit [DecidableEq X] [DecidableEq V] [IsProbabilityMeasure μ] in
/-- arXiv 2608.00397, Section 4.3:
Measurability of the noise work. -/
theorem noiseWork_measurable {f : Ω → Matrix X V ℝ} {n : ℕ}
    (hJ : ∀ j x, StronglyMeasurable[ℱ n] fun ω => G.cur (f ω) j x) (s : Fin K) :
    StronglyMeasurable[ℱ n] fun ω => noiseWork G σ (f ω) s :=
  Finset.stronglyMeasurable_fun_sum _ fun x _ => (Finset.stronglyMeasurable_fun_sum _ fun j _ =>
    (hJ j x).const_mul (σ s j x)).const_mul (G.wx x)

omit [DecidableEq X] [DecidableEq V] [IsProbabilityMeasure μ] in
/-- arXiv 2608.00397, Section 4.3:
Integrability of the noise work. -/
theorem noiseWork_integrable {f : Ω → Matrix X V ℝ} {b : Ω → ℝ}
    (hJi : ∀ j x, Integrable (fun ω => G.cur (f ω) j x * b ω) μ) (s : Fin K) :
    Integrable (fun ω => noiseWork G σ (f ω) s * b ω) μ := by
  have h1 : (fun ω => noiseWork G σ (f ω) s * b ω) = fun ω =>
      ∑ x, G.wx x * ∑ j, σ s j x * (G.cur (f ω) j x * b ω) := by
    ext ω
    simp only [noiseWork, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun j _ => by ring
  rw [h1]
  exact integrable_finsetSum _ fun x _ => (integrable_finsetSum _ fun j _ =>
    (hJi j x).const_mul _).const_mul _

/-- **The energy balance of the Euler–Maruyama scheme in conditional expectation** (arXiv
2608.00397, after Theorem 4.6):
`E[ℋⁿ⁺¹ - ℋⁿ | 𝓕ₙ] = (τ/2) ∫ Tr(A) ρⁿ dx + E[∫ R_Eⁿ dx | 𝓕ₙ]`.  The field residual stays in the
statement: as in the paper, it is not estimated. -/
theorem condExp_totalEnergy_em (hU : ContainsMoments G U) (hP : G.PeriodicX)
    (hn : IsNoise μ ℱ τ Δβ) {f : ℕ → Ω → Matrix X V ℝ} {E : ℕ → Ω → Fin d → X → ℝ} {n : ℕ}
    (hstep : ∀ᵐ ω ∂μ, (Integrator.em : Integrator V).Admissible G σ (Δβ n ω) (f n ω) ∧
      (Integrator.em : Integrator V).Step G U σ τ (Δβ n ω) (E n ω) (f n ω) (f (n + 1) ω))
    (hJ : ∀ j x, StronglyMeasurable[ℱ n] fun ω => G.cur (f n ω) j x)
    (hJi : ∀ s j x, Integrable (fun ω => G.cur (f n ω) j x * Δβ n ω s) μ)
    (hρ : ∀ x, StronglyMeasurable[ℱ n] fun ω => G.dens (f n ω) x)
    (hρi : ∀ x, Integrable (fun ω => G.dens (f n ω) x) μ)
    (hR : Integrable
      (fun ω => ∑ x, G.wx x * fieldResidual τ (E n ω) (E (n + 1) ω) (G.cur (f n ω)) x) μ) :
    μ[fun ω => G.totalEnergy (f (n + 1) ω) (E (n + 1) ω) - G.totalEnergy (f n ω) (E n ω) | ℱ n]
      =ᵐ[μ] fun ω => ∑ x, G.wx x * Grid.thetaEM σ τ (G.dens (f n ω)) x +
        (μ[fun ω => ∑ x, G.wx x * fieldResidual τ (E n ω) (E (n + 1) ω) (G.cur (f n ω)) x | ℱ n])
          ω := by
  have hTm : StronglyMeasurable[ℱ n] fun ω => ∑ x, G.wx x * Grid.thetaEM σ τ (G.dens (f n ω)) x :=
    Finset.stronglyMeasurable_fun_sum _ fun x _ =>
      ((hρ x).const_mul (τ / 2 * ∑ l, Grid.diffusion σ l l x)).const_mul (G.wx x)
  have hTi : Integrable (fun ω => ∑ x, G.wx x * Grid.thetaEM σ τ (G.dens (f n ω)) x) μ :=
    integrable_finsetSum _ fun x _ => ((hρi x).const_mul _).const_mul _
  have h := condExp_increment hn
    (Γ := fun s ω => noiseWork G σ (f n ω) s)
    (D := fun ω => G.totalEnergy (f (n + 1) ω) (E (n + 1) ω) - G.totalEnergy (f n ω) (E n ω))
    (fun s => noiseWork_measurable hJ s) (fun s => noiseWork_integrable (hJi s) s) hTi hR (by
      filter_upwards [hstep] with ω h1
      rw [total_energy hU hP h1.1 h1.2 (E (n + 1) ω)]
      simp only [noiseWork]
      change _ = _ + ∑ x, G.wx x * Integrator.theta σ τ (Δβ n ω) (.em : Integrator V)
        (G.dens (f n ω)) x + _
      ring)
  have hc := condExp_of_stronglyMeasurable (ℱ.le n) hTm hTi
  filter_upwards [h] with ω h1
  rw [h1, Pi.add_apply, hc]

omit [IsProbabilityMeasure μ] in
/-- **The energy balance of the Heun scheme in conditional expectation** (arXiv 2608.00397, after
Theorem 4.6).  The right-hand side is the same as in `condExp_totalEnergy_em`: the two schemes have
distinct stochastic corrections with identical conditional expectations. -/
theorem condExp_totalEnergy_heun (hU : ContainsMoments G U) (hP : G.PeriodicX)
    (hn : IsNoise μ ℱ τ Δβ) {f : ℕ → Ω → Matrix X V ℝ} {E : ℕ → Ω → Fin d → X → ℝ} {n : ℕ}
    {Pr Pr' : Ω → (V → ℝ) →ₗ[ℝ] V → ℝ}
    (hstep : ∀ᵐ ω ∂μ, (Integrator.heun (Pr ω) (Pr' ω)).Admissible G σ (Δβ n ω) (f n ω) ∧
      (Integrator.heun (Pr ω) (Pr' ω)).Step G U σ τ (Δβ n ω) (E n ω) (f n ω) (f (n + 1) ω))
    (hJ : ∀ j x, StronglyMeasurable[ℱ n] fun ω => G.cur (f n ω) j x)
    (hJi : ∀ s j x, Integrable (fun ω => G.cur (f n ω) j x * Δβ n ω s) μ)
    (hρ : ∀ x, StronglyMeasurable[ℱ n] fun ω => G.dens (f n ω) x)
    (hρi : ∀ s r x, Integrable (fun ω => Δβ n ω s * Δβ n ω r * G.dens (f n ω) x) μ)
    (hR : Integrable
      (fun ω => ∑ x, G.wx x * fieldResidual τ (E n ω) (E (n + 1) ω) (G.cur (f n ω)) x) μ) :
    μ[fun ω => G.totalEnergy (f (n + 1) ω) (E (n + 1) ω) - G.totalEnergy (f n ω) (E n ω) | ℱ n]
      =ᵐ[μ] fun ω => ∑ x, G.wx x * Grid.thetaEM σ τ (G.dens (f n ω)) x +
        (μ[fun ω => ∑ x, G.wx x * fieldResidual τ (E n ω) (E (n + 1) ω) (G.cur (f n ω)) x | ℱ n])
          ω := by
  have hΘi : ∀ x, Integrable (fun ω => Grid.thetaHeun σ (Δβ n ω) (G.dens (f n ω)) x) μ := by
    intro x
    simp only [Grid.thetaHeun]
    refine Integrable.const_mul (integrable_finsetSum _ fun s _ =>
      integrable_finsetSum _ fun r _ => ?_) _
    have h1 : (fun ω => Δβ n ω s * Δβ n ω r * (∑ i, σ s i x * σ r i x) * G.dens (f n ω) x) =
        fun ω => (∑ i, σ s i x * σ r i x) * (Δβ n ω s * Δβ n ω r * G.dens (f n ω) x) := by
      ext ω
      ring
    rw [h1]
    exact (hρi s r x).const_mul _
  have hTi : Integrable (fun ω => ∑ x, G.wx x * Grid.thetaHeun σ (Δβ n ω) (G.dens (f n ω)) x) μ :=
    integrable_finsetSum _ fun x _ => (hΘi x).const_mul _
  have h := condExp_increment hn
    (Γ := fun s ω => noiseWork G σ (f n ω) s)
    (D := fun ω => G.totalEnergy (f (n + 1) ω) (E (n + 1) ω) - G.totalEnergy (f n ω) (E n ω))
    (fun s => noiseWork_measurable hJ s) (fun s => noiseWork_integrable (hJi s) s) hTi hR (by
      filter_upwards [hstep] with ω h1
      rw [total_energy hU hP h1.1 h1.2 (E (n + 1) ω)]
      simp only [noiseWork]
      change _ = _ + ∑ x, G.wx x * Integrator.theta σ τ (Δβ n ω) (.heun (Pr ω) (Pr' ω))
        (G.dens (f n ω)) x + _
      ring)
  have hc := condExp_weighted_sum (g := fun x ω => Grid.thetaHeun σ (Δβ n ω) (G.dens (f n ω)) x)
    (h := fun x ω => Grid.thetaEM σ τ (G.dens (f n ω)) x) (m₀ := ℱ n) Finset.univ G.wx
    (fun x _ => hΘi x)
    fun x _ => condExp_thetaHeun hn σ n (ρ := fun ω => G.dens (f n ω)) x (hρ x)
      fun s r => hρi s r x
  filter_upwards [h, hc] with ω h1 h2
  rw [h1, Pi.add_apply, h2]

end Expectation

/-! ### The discrete Poisson equation gives `∫ E ρ dx = 0` -/

section Poisson

variable {X : Type*} [Fintype X]

/-- **The assumption `∫ Eⁿ ρⁿ dx = 0` of arXiv 2608.00397, Theorem 4.3, follows from the Poisson
equation.**  If `E = -grad u` and `-lap u = ρ - c`, where `grad` is skew and has mean zero, `lap` is
symmetric and they commute (all Fourier multipliers do, so this covers the FFT-based solver of the
paper), then `∫ E ρ dx = 0`.  The paper assumes the conclusion. -/
theorem total_force_eq_zero {w : X → ℝ} {grad lap : (X → ℝ) →ₗ[ℝ] X → ℝ}
    (hmean : ∀ u, ∑ x, w x * grad u x = 0)
    (hskew : ∀ a b, ∑ x, w x * (grad a x * b x) = -∑ x, w x * (a x * grad b x))
    (hsym : ∀ a b, ∑ x, w x * (lap a x * b x) = ∑ x, w x * (a x * lap b x))
    (hcomm : ∀ a, grad (lap a) = lap (grad a)) {u ρ E : X → ℝ} {c : ℝ}
    (hρ : ∀ x, -lap u x = ρ x - c) (hE : ∀ x, E x = -grad u x) :
    ∑ x, w x * (E x * ρ x) = 0 := by
  have hT : ∑ x, w x * (grad u x * lap u x) = 0 := by
    have h1 := hsym (grad u) u
    rw [← hcomm, hskew] at h1
    have h2 : ∑ x, w x * (lap u x * grad u x) = ∑ x, w x * (grad u x * lap u x) :=
      Finset.sum_congr rfl fun x _ => by ring
    rw [h2] at h1
    linarith
  have h : ∀ x, w x * (E x * ρ x) = w x * (grad u x * lap u x) - c * (w x * grad u x) := fun x => by
    have : ρ x = c - lap u x := by linarith [hρ x]
    rw [hE x, this]
    ring
  simp only [h, Finset.sum_sub_distrib, ← Finset.mul_sum, hT, hmean, mul_zero, sub_zero]

/-- arXiv 2608.00397, Theorem 4.3:
The instance of `total_force_eq_zero` for the second-order stencils on a periodic grid:
`E = -D_c φ` with the centred difference and `-D₊D₋ φ = ρ - ρ₀` give `∑ᵢ Eᵢ ρᵢ = 0`.  This uses
`periodic_sbp_identities` of the library. -/
theorem periodic_force_eq_zero {N : ℕ} [NeZero N] (φ : ZMod N → ℝ) (Δx ρ₀ : ℝ)
    {ρ E : ZMod N → ℝ} (hρ : ∀ i, -((φ (i + 1) - 2 * φ i + φ (i - 1)) / Δx ^ 2) = ρ i - ρ₀)
    (hE : ∀ i, E i = -((φ (i + 1) - φ (i - 1)) / (2 * Δx))) : ∑ i, E i * ρ i = 0 := by
  obtain ⟨h1, h2⟩ := LeanDLRA.OpenProblems.Conservation.periodic_sbp_identities φ Δx ρ₀
  have h : ∀ i, E i * ρ i =
      (φ (i + 1) - 2 * φ i + φ (i - 1)) / Δx ^ 2 * ((φ (i + 1) - φ (i - 1)) / (2 * Δx)) -
        ρ₀ * ((φ (i + 1) - φ (i - 1)) / (2 * Δx)) := fun i => by
    have : ρ i = ρ₀ - (φ (i + 1) - 2 * φ i + φ (i - 1)) / Δx ^ 2 := by linarith [hρ i]
    rw [hE i, this]
    ring
  simp only [h, Finset.sum_sub_distrib, h1, h2, sub_zero]

end Poisson

section ExpectationPoisson

open MeasureTheory

variable {X V : Type*} {d K m : ℕ} [Fintype X] [Fintype V] [DecidableEq X] [DecidableEq V]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ mΩ}

/-- **Theorem 4.3 of arXiv 2608.00397 with the electric field of
the discrete Poisson equation.**  As `expected_momentum`, but the assumption `∫ Eⁿ ρⁿ dx = 0` of the
paper is replaced by what implies it: `Eⁿ = -grad uⁿ` and `-lap uⁿ = ρⁿ - c` with a skew `grad` of
mean zero, a symmetric `lap`, and `grad lap = lap grad`. -/
theorem expected_momentum_poisson {G : Grid X V d} {U : Matrix V (Fin m) ℝ}
    {σ : Fin K → Fin d → X → ℝ} {τ : ℝ} {Δβ : ℕ → Ω → Fin K → ℝ}
    (hU : ContainsMoments G U) (hP : G.PeriodicX) (hn : IsNoise μ ℱ τ Δβ)
    {θ : ℕ → Ω → Integrator V} {f : ℕ → Ω → Matrix X V ℝ} {E : ℕ → Ω → Fin d → X → ℝ}
    (hstep : ∀ n, ∀ᵐ ω ∂μ, (θ n ω).Admissible G σ (Δβ n ω) (f n ω) ∧
      (θ n ω).Step G U σ τ (Δβ n ω) (E n ω) (f n ω) (f (n + 1) ω))
    {grad : Fin d → (X → ℝ) →ₗ[ℝ] X → ℝ} {lap : (X → ℝ) →ₗ[ℝ] X → ℝ}
    (hmean : ∀ i u, ∑ x, G.wx x * grad i u x = 0)
    (hskew : ∀ i a b, ∑ x, G.wx x * (grad i a x * b x) = -∑ x, G.wx x * (a x * grad i b x))
    (hsym : ∀ a b, ∑ x, G.wx x * (lap a x * b x) = ∑ x, G.wx x * (a x * lap b x))
    (hcomm : ∀ i a, grad i (lap a) = lap (grad i a)) {u : ℕ → Ω → X → ℝ} {c : ℝ}
    (hpoisson : ∀ n ω x, -lap (u n ω) x = G.dens (f n ω) x - c)
    (hE : ∀ n ω j x, E n ω j x = -grad j (u n ω) x)
    (hρ : ∀ n x, StronglyMeasurable[ℱ n] fun ω => G.dens (f n ω) x)
    (hint : ∀ n s x, Integrable (fun ω => G.dens (f n ω) x * Δβ n ω s) μ) {j : Fin d}
    (h0 : Integrable (fun ω => G.totalMomentum (f 0 ω) j) μ) (n : ℕ) :
    ∫ ω, G.totalMomentum (f n ω) j ∂μ = ∫ ω, G.totalMomentum (f 0 ω) j ∂μ :=
  expected_momentum hU hP hn hstep
    (fun n => Filter.Eventually.of_forall fun ω i =>
      total_force_eq_zero (hmean i) (hskew i) hsym (hcomm i) (hpoisson n ω)
        (fun x => hE n ω i x))
    hρ hint h0 n

end ExpectationPoisson

/-! ### The predictor, the second-order identities and the generality of the mechanism -/

namespace Grid

variable {X V : Type*} {d K : ℕ} [Fintype V] {G : Grid X V d}

/-- The exact predictor of arXiv 2608.00397, Eq. (3.11), is admissible. -/
theorem preservesMoments_id : G.PreservesMoments LinearMap.id :=
  fun _ => ⟨rfl, fun _ => rfl⟩

/-- If the second derivative is the composition of first derivatives, the second-order identities
follow from the first-order ones (arXiv 2608.00397 assumes them separately). -/
theorem secondIds_of_comp {g : V → ℝ} (h : G.FirstIds g) (h' : ∀ n, G.FirstIds (G.Dv n g))
    (hDvv : ∀ l n, G.Dvv l n g = G.Dv l (G.Dv n g)) : G.SecondIds g where
  div l n := by
    rw [hDvv]
    exact (h' n).div l
  first l n j := by
    rw [hDvv, (h' n).first l j, h.div n]
    simp
  second l n := by
    rw [hDvv, (h' n).second l, h.first n l]
    by_cases hln : l = n
    · subst hln
      simp
    · simp [hln, Ne.symm hln]

/-- The representation `Π_B g = f₀ᵥ ∑ⱼ Bⱼ (Bⱼ, g)ᵥ` of a density in a velocity basis `B`.  With
`Pr = vproj Vⁿ` the K-step of the Heun scheme has the quadratic term
`½ ∑ₛₕ Δβˢ Δβʰ ∑ⱼₗ (c²ₖⱼ·σₛ) (c²ⱼₗ·σₕ) Kₗ` of arXiv 2608.00397, Eq. (4.2). -/
def vproj (G : Grid X V d) {n : Type*} [Fintype n] (B : Matrix V n ℝ) : (V → ℝ) →ₗ[ℝ] V → ℝ where
  toFun g v := G.f0 v * ∑ j, B v j * G.pair (fun w => B w j) g
  map_add' g h := by
    have hp : ∀ p, G.pair p (g + h) = G.pair p g + G.pair p h := fun p => G.pair_fun_add p g h
    ext v
    simp only [hp, mul_add, Finset.sum_add_distrib, Pi.add_apply]
  map_smul' c g := by
    have hp : ∀ p, G.pair p (c • g) = c * G.pair p g := fun p => G.pair_mul_left p g c
    ext v
    simp only [hp, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

/-- arXiv 2608.00397, Section 4 (predictor in the current basis):
The representation in an orthonormal basis does not change the pairing with the basis. -/
theorem pair_vproj {n : Type*} [Fintype n] [DecidableEq n] [DecidableEq V] {B : Matrix V n ℝ}
    (hB : Bᵀ * G.massV * B = 1) (c : n → ℝ) (g : V → ℝ) :
    G.pair (B *ᵥ c) (G.vproj B g) = G.pair (B *ᵥ c) g := by
  have hE : ∀ a j, ∑ v, G.wv v * G.f0 v * B v a * B v j = if a = j then 1 else 0 := by
    intro a j
    have h := congrFun (congrFun hB a) j
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [← h]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [massV, Matrix.mul_diagonal, Matrix.transpose_apply]
    ring
  have hL : G.pair (B *ᵥ c) (G.vproj B g) =
      ∑ a, ∑ j, c a * G.pair (fun w => B w j) g * ∑ v, G.wv v * G.f0 v * B v a * B v j := by
    have h1 : ∀ v, G.wv v * (B *ᵥ c) v * G.vproj B g v =
        ∑ a, ∑ j, c a * G.pair (fun w => B w j) g * (G.wv v * G.f0 v * B v a * B v j) := by
      intro v
      change G.wv v * (∑ a, B v a * c a) *
        (G.f0 v * ∑ j, B v j * G.pair (fun w => B w j) g) = _
      rw [show ∀ u t : ℝ, G.wv v * u * (G.f0 v * t) = G.wv v * G.f0 v * (u * t) from
        fun u t => by ring, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [pair, Finset.sum_congr rfl fun v _ => h1 v, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
  have hR : G.pair (B *ᵥ c) g = ∑ a, c a * G.pair (fun w => B w a) g := by
    simp only [pair, mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun v _ => by ring
  rw [hL, hR]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a (fun j _ hj => by simp [hE, hj.symm]) (by simp), hE]
  simp

/-- arXiv 2608.00397, Section 4 (predictor in the current basis):
The representation in an orthonormal basis that contains `1` and `vᵢ` is admissible. -/
theorem vproj_preservesMoments {n : Type*} [Fintype n] [DecidableEq n] [DecidableEq V]
    {B : Matrix V n ℝ} (hB : Bᵀ * G.massV * B = 1) (h1 : ∃ c, B *ᵥ c = 1)
    (hn : ∀ i, ∃ c, B *ᵥ c = G.node i) : G.PreservesMoments (G.vproj B) := by
  intro g
  refine ⟨?_, fun i => ?_⟩
  · obtain ⟨c, hc⟩ := h1
    rw [← hc]
    exact pair_vproj hB c g
  · obtain ⟨c, hc⟩ := hn i
    rw [← hc]
    exact pair_vproj hB c g

/-- The word `σ_{s₁}·∇ᵥ ⋯ σ_{sₖ}·∇ᵥ` in the noise operators. -/
def wordOp (G : Grid X V d) (σ : Fin K → Fin d → X → ℝ) : List (Fin K) → Matrix X V ℝ → Matrix X V ℝ
  | [], f => f
  | s :: w, f => G.sigmaGrad σ s (G.wordOp σ w f)

/-- A stochastic increment polynomial in the noise operators (arXiv 2608.00397, Remark 4.4):
`τ D(f) + ∑_w a_w (σ_{s₁}·∇ᵥ ⋯ σ_{sₖ}·∇ᵥ) f`, with coefficients independent of `(x, v)`. -/
noncomputable def incPoly (G : Grid X V d) (σ : Fin K → Fin d → X → ℝ) (τ : ℝ) (E : Fin d → X → ℝ)
    (W : Finset (List (Fin K))) (a : List (Fin K) → ℝ) (f : Matrix X V ℝ) : Matrix X V ℝ :=
  fun x v => τ * G.transport E f x v + ∑ w ∈ W, a w * G.wordOp σ w f x v

/-- The momentum of the word `w`: words of length one contribute `-σₛⱼ ρ`, all others nothing. -/
noncomputable def polyMomentum (σ : Fin K → Fin d → X → ℝ) (ρ : ℝ) (j : Fin d) (x : X) :
    List (Fin K) → ℝ
  | [s] => -(σ s j x * ρ)
  | _ => 0

/-- The kinetic energy of the word `w`: words of length one contribute `-σₛ·J`, words of length two
`(σₛ·σᵣ) ρ`, all others nothing. -/
noncomputable def polyEnergy (σ : Fin K → Fin d → X → ℝ) (ρ : ℝ) (J : Fin d → ℝ) (x : X) :
    List (Fin K) → ℝ
  | [s] => -∑ i, σ s i x * J i
  | [s, r] => (∑ i, σ s i x * σ r i x) * ρ
  | _ => 0

/-- arXiv 2608.00397, Remark 4.4: a word has no mass. -/
theorem pair_one_wordOp {σ : Fin K → Fin d → X → ℝ} {f : Matrix X V ℝ}
    (hW : ∀ w x, G.FirstIds (G.wordOp σ w f x)) {w : List (Fin K)} (hw : w ≠ []) (x : X) :
    G.pair 1 (G.wordOp σ w f x) = 0 := by
  cases w with
  | nil => exact absurd rfl hw
  | cons s w => exact pair_one_sigmaGrad (hW w x) σ s

/-- arXiv 2608.00397, Remark 4.4: the momentum of a word. -/
theorem pair_node_wordOp {σ : Fin K → Fin d → X → ℝ} {f : Matrix X V ℝ}
    (hW : ∀ w x, G.FirstIds (G.wordOp σ w f x)) {w : List (Fin K)} (hw : w ≠ []) (j : Fin d)
    (x : X) : G.pair (G.node j) (G.wordOp σ w f x) = polyMomentum σ (G.dens f x) j x w := by
  match w, hw with
  | [s], _ => exact pair_node_sigmaGrad (hW [] x) σ s j
  | s :: r :: w, _ =>
    have h := pair_node_sigmaGrad (hW (r :: w) x) σ s j
    rw [pair_one_wordOp hW (by simp) x, mul_zero, neg_zero] at h
    exact h

/-- arXiv 2608.00397, Remark 4.4: the kinetic energy of a word. -/
theorem pair_speed2_wordOp {σ : Fin K → Fin d → X → ℝ} {f : Matrix X V ℝ}
    (hW : ∀ w x, G.FirstIds (G.wordOp σ w f x)) {w : List (Fin K)} (hw : w ≠ []) (x : X) :
    1 / 2 * G.pair G.speed2 (G.wordOp σ w f x) =
      polyEnergy σ (G.dens f x) (fun j => G.cur f j x) x w := by
  match w, hw with
  | [s], _ =>
    have h : G.pair G.speed2 (G.sigmaGrad σ s f x) = -2 * ∑ i, σ s i x * G.cur f i x :=
      pair_speed2_sigmaGrad (hW [] x) σ s
    change 1 / 2 * G.pair G.speed2 (G.sigmaGrad σ s f x) = -∑ i, σ s i x * G.cur f i x
    rw [h]
    ring
  | [s, r], _ =>
    have h := pair_speed2_sigmaGrad (hW [r] x) σ s
    change 1 / 2 * G.pair G.speed2 (G.sigmaGrad σ s (G.sigmaGrad σ r f) x) =
      (∑ i, σ s i x * σ r i x) * G.dens f x
    change G.pair G.speed2 (G.sigmaGrad σ s (G.sigmaGrad σ r f) x) = _ at h
    rw [h]
    have hj : ∀ i, G.pair (G.node i) (G.wordOp σ [r] f x) = -(σ r i x * G.dens f x) :=
      fun i => pair_node_wordOp hW (by simp) i x
    simp only [hj, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  | s :: r :: t :: w, _ =>
    have h := pair_speed2_sigmaGrad (hW (r :: t :: w) x) σ s
    have hj : ∀ i, G.pair (G.node i) (G.wordOp σ (r :: t :: w) f x) = 0 :=
      fun i => pair_node_wordOp hW (by simp) i x
    simp only [hj, mul_zero, Finset.sum_const_zero] at h
    change G.pair G.speed2 (G.wordOp σ (s :: r :: t :: w) f x) = 0 at h
    rw [h, mul_zero]
    rfl

end Grid

section Generality

variable {X V : Type*} {d K m : ℕ} [Fintype X] [Fintype V] [DecidableEq X] [DecidableEq V]
  {G : Grid X V d} {U : Matrix V (Fin m) ℝ}

omit [Fintype X] [DecidableEq X] in
/-- The velocity basis `[U, W]` represents the predictor admissibly: this is the variant of the
paper's implementation (arXiv 2608.00397, Section 4). -/
theorem ContainsMoments.vproj_preservesMoments {q : ℕ} (hU : ContainsMoments G U)
    {W : Matrix V (Fin q) ℝ} (h : (fromCols U W)ᵀ * G.massV * fromCols U W = 1) :
    G.PreservesMoments (G.vproj (fromCols U W)) := by
  have hc : ∀ {p : V → ℝ}, (∃ c, U *ᵥ c = p) → ∃ c, fromCols U W *ᵥ c = p := by
    rintro p ⟨c, rfl⟩
    refine ⟨Sum.elim c 0, ?_⟩
    rw [fromCols_mulVec_sumElim, mulVec_zero, add_zero]
  exact Grid.vproj_preservesMoments h (hc hU.one) fun i => hc (hU.node i)

/-- **Remark 4.4 of arXiv 2608.00397.**  Let the stochastic
increment be polynomial in the noise operators `σₛ·∇ᵥ`, without constant term and with coefficients
independent of `(x, v)`, the same in the K- and in the S-step.  Then the balance laws hold exactly:
words of length one drive the momentum and the energy, words of length two only the energy, and
words of length at least three do not enter.  So the mechanism also covers higher-order schemes. -/
theorem polynomial_balance (hU : ContainsMoments G U) {σ : Fin K → Fin d → X → ℝ} {τ : ℝ}
    {E : Fin d → X → ℝ} {W : Finset (List (Fin K))} {a : List (Fin K) → ℝ} {f f' : Matrix X V ℝ}
    (hwW : ∀ w ∈ W, w ≠ []) (hW : ∀ w x, G.FirstIds (G.wordOp σ w f x))
    (hstep : IsStep G U (G.incPoly σ τ E W a) (G.incPoly σ τ E W a) f f') :
    (∀ x, G.dens f' x = G.dens f x - τ * G.divx (G.cur f) x) ∧
    (∀ j x, G.cur f' j x = G.cur f j x - τ * G.divx (G.stress f j) x + τ * E j x * G.dens f x +
      ∑ w ∈ W, a w * Grid.polyMomentum σ (G.dens f x) j x w) ∧
    (∀ x, G.kin f' x = G.kin f x - τ * G.divx (G.heat f) x + τ * ∑ j, E j x * G.cur f j x +
      ∑ w ∈ W, a w * Grid.polyEnergy σ (G.dens f x) (fun j => G.cur f j x) x w) := by
  have hf : ∀ x, G.FirstIds (f x) := fun x => hW [] x
  have hS : ∀ (p : V → ℝ) x, G.pair p (fun v => ∑ w ∈ W, a w * G.wordOp σ w f x v) =
      ∑ w ∈ W, a w * G.pair p (G.wordOp σ w f x) := fun p x => by
    rw [Grid.pair_sum]
    exact Finset.sum_congr rfl fun w _ => G.pair_mul_left p (G.wordOp σ w f x) (a w)
  refine ⟨fun x => ?_, fun j x => ?_, fun x => ?_⟩
  · have h := hstep.pair_eq hU.one (fun _ => rfl) x
    have h1 : G.pair 1 (G.incPoly σ τ E W a f x) = -τ * G.divx (G.cur f) x := by
      change G.pair 1 (fun v => τ * G.transport E f x v + _) = _
      have h0 : ∑ w ∈ W, a w * G.pair 1 (G.wordOp σ w f x) = 0 :=
        Finset.sum_eq_zero fun w hw => by rw [Grid.pair_one_wordOp hW (hwW w hw) x, mul_zero]
      rw [Grid.pair_one_add_transport (hf x), hS, h0, add_zero]
    rw [Grid.dens, h, h1, Grid.dens]
    ring
  · have h := hstep.pair_eq (hU.node j) (fun _ => rfl) x
    have h1 : G.pair (G.node j) (G.incPoly σ τ E W a f x) =
        -τ * G.divx (G.stress f j) x + τ * E j x * G.dens f x +
          ∑ w ∈ W, a w * Grid.polyMomentum σ (G.dens f x) j x w := by
      change G.pair (G.node j) (fun v => τ * G.transport E f x v + _) = _
      rw [Grid.pair_node_add_transport (hf x), hS]
      congr 1
      exact Finset.sum_congr rfl fun w hw => by rw [Grid.pair_node_wordOp hW (hwW w hw)]
    rw [Grid.cur, h, h1, Grid.cur]
    ring
  · have h := hstep.pair_eq hU.speed2 (fun _ => rfl) x
    have h1 : 1 / 2 * G.pair G.speed2 (G.incPoly σ τ E W a f x) =
        -τ * G.divx (G.heat f) x + τ * ∑ j, E j x * G.cur f j x +
          ∑ w ∈ W, a w * Grid.polyEnergy σ (G.dens f x) (fun j => G.cur f j x) x w := by
      have h2 : 1 / 2 * G.pair G.speed2 (fun v => ∑ w ∈ W, a w * G.wordOp σ w f x v) =
          ∑ w ∈ W, a w * Grid.polyEnergy σ (G.dens f x) (fun j => G.cur f j x) x w := by
        rw [hS, Finset.mul_sum]
        refine Finset.sum_congr rfl fun w hw => ?_
        rw [← Grid.pair_speed2_wordOp hW (hwW w hw)]
        ring
      change 1 / 2 * G.pair G.speed2 (fun v => τ * G.transport E f x v + _) = _
      rw [Grid.pair_speed2_add_transport (hf x), h2]
    rw [Grid.kin, h, mul_add, h1, Grid.kin]
    ring

end Generality

/-! ### The hypotheses can hold -/

section Instance

variable {d m : ℕ}

/-- The basis `[1]` without moving modes. -/
def fullBasis (m : ℕ) : Matrix (Fin m) (Fin m ⊕ Fin 0) ℝ := fromCols 1 0

/-- arXiv 2608.00397, instance of the hypotheses: `T Tᵀ = 1`. -/
theorem fullBasis_mul_transpose : fullBasis m * (fullBasis m)ᵀ = 1 := by
  ext x y
  simp [fullBasis, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

/-- arXiv 2608.00397, instance of the hypotheses: `Tᵀ T = 1`. -/
theorem fullBasis_transpose_mul : (fullBasis m)ᵀ * fullBasis m = 1 := by
  ext (a | a) (b | b)
  · simp [fullBasis, Matrix.mul_apply, Matrix.one_apply, eq_comm]
  · exact b.elim0
  · exact a.elim0
  · exact a.elim0

/-- The state of rank `m` without moving modes and coefficients `f`. -/
def fullState (f : Matrix (Fin m) (Fin m) ℝ) : State (Fin m) (Fin m) m 0 where
  Xb := fullBasis m
  S := (fullBasis m)ᵀ * f * fullBasis m
  W := 0

/-- arXiv 2608.00397, instance of the hypotheses: the distribution of `fullState f` is `f`. -/
theorem fullState_dist {G : Grid (Fin m) (Fin m) d} (h0 : G.f0 = 1)
    (f : Matrix (Fin m) (Fin m) ℝ) : (fullState f).dist G 1 = f := by
  have hd : diagonal G.f0 = 1 := by
    rw [h0]
    exact Matrix.diagonal_one
  have hV : State.Vb (1 : Matrix (Fin m) (Fin m) ℝ) (fullState f) = fullBasis m := rfl
  rw [State.dist, hV, hd, Matrix.mul_one]
  change fullBasis m * ((fullBasis m)ᵀ * f * fullBasis m) * (fullBasis m)ᵀ = f
  calc fullBasis m * ((fullBasis m)ᵀ * f * fullBasis m) * (fullBasis m)ᵀ
      = (fullBasis m * (fullBasis m)ᵀ) * f * (fullBasis m * (fullBasis m)ᵀ) := by
        simp only [Matrix.mul_assoc]
    _ = f := by rw [fullBasis_mul_transpose, Matrix.one_mul, Matrix.mul_one]

/-- The step in full rank: on a grid with unit weights and with `U = 1`, nothing is truncated and
one step of the integrator is the step `f + I(f)` of the full scheme. -/
noncomputable def fullStep {G : Grid (Fin m) (Fin m) d} (hx : G.wx = 1) (hv : G.wv = 1)
    (h0 : G.f0 = 1) (I : Matrix (Fin m) (Fin m) ℝ → Matrix (Fin m) (Fin m) ℝ)
    (f : Matrix (Fin m) (Fin m) ℝ) :
    AugBUGStep G 1 I I (fullState f) (fullState (f + I f)) m 0 := by
  have hmx : G.massX = 1 := by
    rw [Grid.massX, hx]
    exact Matrix.diagonal_one
  have hmv : G.massV = 1 := by
    have : (fun v => G.wv v * G.f0 v) = 1 := by
      ext v
      simp [hv, h0]
    rw [Grid.massV, this]
    exact Matrix.diagonal_one
  have hw : diagonal G.wv = 1 := by
    rw [hv]
    exact Matrix.diagonal_one
  have hd : diagonal G.f0 = 1 := by
    rw [h0]
    exact Matrix.diagonal_one
  have hV : fromCols (1 : Matrix (Fin m) (Fin m) ℝ) (0 : Matrix (Fin m) (Fin 0) ℝ) = fullBasis m :=
    rfl
  have hfA : fAug G 1 (fullState f) (1 : Matrix (Fin m) (Fin m) ℝ)
      (0 : Matrix (Fin m) (Fin 0) ℝ) = f := by
    rw [fAug, overlapX, overlapV, hV, hmx, hmv, hd]
    change 1 * (1ᵀ * 1 * fullBasis m) * ((fullBasis m)ᵀ * f * fullBasis m) *
      ((fullBasis m)ᵀ * 1 * fullBasis m) * (fullBasis m)ᵀ * 1 = f
    simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, fullBasis_transpose_mul]
    calc fullBasis m * ((fullBasis m)ᵀ * f * fullBasis m) * (fullBasis m)ᵀ
        = (fullBasis m * (fullBasis m)ᵀ) * f * (fullBasis m * (fullBasis m)ᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = f := by rw [fullBasis_mul_transpose, Matrix.one_mul, Matrix.mul_one]
  have hS : sStep G 1 (fullState f) (1 : Matrix (Fin m) (Fin m) ℝ)
      (0 : Matrix (Fin m) (Fin 0) ℝ) (I (fAug G 1 (fullState f) (1 : Matrix (Fin m) (Fin m) ℝ)
        (0 : Matrix (Fin m) (Fin 0) ℝ))) = (f + I f) * fullBasis m := by
    rw [hfA, sStep, overlapX, overlapV, hV, hmx, hmv, hw]
    change (1ᵀ * 1 * fullBasis m) * ((fullBasis m)ᵀ * f * fullBasis m) *
      ((fullBasis m)ᵀ * 1 * fullBasis m) + 1ᵀ * 1 * I f * 1 * fullBasis m = _
    simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, fullBasis_transpose_mul]
    rw [Matrix.add_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, fullBasis_mul_transpose,
      Matrix.one_mul]
  have hr : LinearMap.range (1 : Matrix (Fin m) (Fin m) ℝ).mulVecLin = ⊤ := by
    rw [Matrix.mulVecLin_one, LinearMap.range_id]
  exact
    { Xa := 1
      Wa := 0
      Xcons := 1
      Scons := f + I f
      Xrem := 0
      Shat := 0
      What := 0
      R := 1
      V_orth := by
        rw [hmv, Matrix.mul_one]
        exact fullBasis_transpose_mul
      Xa_orth := by simp [hmx]
      Va_orth := by
        rw [hmv, Matrix.mul_one]
        exact fullBasis_transpose_mul
      X_le := by
        rw [hr]
        exact le_top
      K_le := by
        rw [hr]
        exact le_top
      W_le := by
        rintro _ ⟨c, rfl⟩
        have h : (fullState f).W.mulVecLin c = 0 := by
          ext x
          simp [fullState]
        rw [h]
        exact zero_mem _
      cons_qr := by
        rw [hS, Matrix.one_mul, Matrix.one_mul, fullBasis, Matrix.mul_fromCols, Matrix.mul_one]
        ext x a
        simp
      new_W := by
        ext _ a
        exact a.elim0
      new_qr := by
        change fullBasis m = fullBasis m * 1
        rw [Matrix.mul_one]
      new_S := by
        rw [Matrix.one_mul]
        ext (a | a) (b | b)
        · simp [fullState, fullBasis, Matrix.mul_apply, Matrix.one_apply]
        · exact b.elim0
        · exact a.elim0
        · exact a.elim0 }

end Instance

section Existence

variable {X V : Type*} {d m p p' : ℕ} [Fintype X] [Fintype V] [DecidableEq X] [DecidableEq V]

/-- arXiv 2608.00397 (auxiliary): a basis of the whole grid function space, orthonormal for positive
spatial weights. -/
noncomputable def spaceBasis (w : X → ℝ) : Matrix X (Fin (Fintype.card X)) ℝ :=
  fun x j => if Fintype.equivFin X x = j then 1 / Real.sqrt (w x) else 0

/-- arXiv 2608.00397 (auxiliary): `spaceBasis` is orthonormal. -/
theorem spaceBasis_orth {w : X → ℝ} (hw : ∀ x, 0 < w x) :
    (spaceBasis w)ᵀ * diagonal w * spaceBasis w = 1 := by
  ext i j
  have hs : ∀ x, 1 / Real.sqrt (w x) * w x * (1 / Real.sqrt (w x)) = 1 := fun x => by
    have h1 : Real.sqrt (w x) ≠ 0 := (Real.sqrt_pos.2 (hw x)).ne'
    have h2 : Real.sqrt (w x) ^ 2 = w x := Real.sq_sqrt (hw x).le
    field_simp
    exact h2.symm
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  rw [Finset.sum_eq_single ((Fintype.equivFin X).symm i)]
  · by_cases hij : i = j
    · subst hij
      have h := hs ((Fintype.equivFin X).symm i)
      simpa [spaceBasis, one_div] using h
    · simp [spaceBasis, hij]
  · intro x _ hx
    have : Fintype.equivFin X x ≠ i := fun h => hx (by rw [← h]; simp)
    simp [spaceBasis, this]
  · simp

omit [DecidableEq X] in
/-- arXiv 2608.00397 (auxiliary): `spaceBasis` spans all grid functions. -/
theorem spaceBasis_range {w : X → ℝ} (hw : ∀ x, 0 < w x) :
    LinearMap.range (spaceBasis w).mulVecLin = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro y
  refine ⟨fun j => Real.sqrt (w ((Fintype.equivFin X).symm j)) *
    y ((Fintype.equivFin X).symm j), ?_⟩
  ext x
  rw [mulVecLin_apply, mulVec, dotProduct, Finset.sum_eq_single (Fintype.equivFin X x)]
  · have h1 : Real.sqrt (w x) ≠ 0 := (Real.sqrt_pos.2 (hw x)).ne'
    simp only [spaceBasis, ite_true, Equiv.symm_apply_apply]
    field_simp
  · intro j _ hj
    simp [spaceBasis, hj.symm]
  · simp

/-- **The step exists at every rank** (well-posedness; the structure `AugBUGStep` of arXiv
2608.00397, Sections 3.1–3.3, has instances with moving modes).  For positive spatial weights, every
state with orthonormal `Vⁿ` and all increments have a step `AugBUGStep`, for every choice of the
truncated remainder `Xrem`, `Shat`, `What`.  Here the velocity basis is not enlarged, `Ṽ = Vⁿ`,
and `X̃` spans all of the grid functions; the factors are not orthonormalized.  If `What` has
orthonormal columns, `Vⁿ⁺¹` is orthonormal again, so the integrator can be iterated. -/
theorem exists_augBUGStep {G : Grid X V d} {U : Matrix V (Fin m) ℝ} (hwx : ∀ x, 0 < G.wx x)
    (IK IS : Matrix X V ℝ → Matrix X V ℝ) (s : State X V m p)
    (hV : (s.Vb U)ᵀ * G.massV * s.Vb U = 1) (Xrem : Matrix X (Fin p') ℝ)
    (Shat : Matrix (Fin p') (Fin p') ℝ) (What : Matrix (Fin p) (Fin p') ℝ) :
    ∃ s' : State X V m p', s'.W = s.W * What ∧
      Nonempty (AugBUGStep G U IK IS s s' (Fintype.card X) p) ∧
      (Whatᵀ * What = 1 → (s'.Vb U)ᵀ * G.massV * s'.Vb U = 1) := by
  have hr := spaceBasis_range hwx
  let Xa := spaceBasis G.wx
  let Xc : Matrix X (Fin m) ℝ :=
    (Xa * sStep G U s Xa s.W (IS (fAug G U s Xa s.W))).submatrix id Sum.inl
  let s' : State X V m p' := ⟨fromCols Xc Xrem, fromBlocks 1 0 0 Shat, s.W * What⟩
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin p') ℝ,
      B = fromBlocks 1 0 0 What := ⟨_, rfl⟩
  have hs' : s'.Vb U = s.Vb U * B := by
    rw [hB, State.Vb, State.Vb, fromCols_mul_fromBlocks]
    simp [s']
  refine ⟨s', rfl, ⟨?_⟩, fun h => ?_⟩
  · exact
      { Xa := Xa
        Wa := s.W
        Xcons := Xc
        Scons := 1
        Xrem := Xrem
        Shat := Shat
        What := What
        R := 1
        V_orth := hV
        Xa_orth := spaceBasis_orth hwx
        Va_orth := hV
        X_le := by
          change _ ≤ LinearMap.range (spaceBasis G.wx).mulVecLin
          rw [hr]
          exact le_top
        K_le := by
          change _ ≤ LinearMap.range (spaceBasis G.wx).mulVecLin
          rw [hr]
          exact le_top
        W_le := by
          rintro _ ⟨c, rfl⟩
          refine ⟨Sum.elim 0 c, ?_⟩
          rw [mulVecLin_apply, mulVecLin_apply, fromCols_mulVec_sumElim, mulVec_zero, zero_add]
        cons_qr := by
          rw [Matrix.mul_one]
        new_W := rfl
        new_qr := by
          rw [Matrix.mul_one]
        new_S := by
          rw [Matrix.one_mul] }
  · have h1 : Bᵀ * B = 1 := by
      rw [hB, fromBlocks_transpose, fromBlocks_multiply]
      simp [h, fromBlocks_one]
    calc (s'.Vb U)ᵀ * G.massV * s'.Vb U
        = Bᵀ * ((s.Vb U)ᵀ * G.massV * s.Vb U) * B := by
          rw [hs', transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hV, Matrix.mul_one, h1]

end Existence

section Instance

/-- A discrete `∂ᵥ` on three nodes `-1, 0, 1` with the velocity identities for every profile: the
negative transpose of the collocation derivative. -/
noncomputable def sampleDv : (Fin 3 → ℝ) →ₗ[ℝ] Fin 3 → ℝ where
  toFun g := ![3 / 2 * g 0 + 1 / 2 * g 1 - 1 / 2 * g 2, -2 * g 0 + 2 * g 2,
    1 / 2 * g 0 - 1 / 2 * g 1 - 3 / 2 * g 2]
  map_add' g h := by
    ext k
    fin_cases k <;> simp <;> ring
  map_smul' c g := by
    ext k
    fin_cases k <;> simp <;> ring

/-- The periodic centred difference on three points. -/
noncomputable def sampleDx : (Fin 3 → ℝ) →ₗ[ℝ] Fin 3 → ℝ where
  toFun u := ![(u 1 - u 2) / 2, (u 2 - u 0) / 2, (u 0 - u 1) / 2]
  map_add' g h := by
    ext k
    fin_cases k <;> simp <;> ring
  map_smul' c g := by
    ext k
    fin_cases k <;> simp <;> ring

/-- A grid with three spatial points, the three velocity nodes `-1, 0, 1` and unit weights. -/
noncomputable def sampleGrid : Grid (Fin 3) (Fin 3) 1 where
  wx := 1
  wv := 1
  f0 := 1
  node _ := ![-1, 0, 1]
  Dx _ := sampleDx
  Dv _ := sampleDv
  Dvv _ _ := sampleDv ∘ₗ sampleDv

/-- arXiv 2608.00397, instance of the hypotheses: `sampleGrid` has the first-order identities. -/
theorem sample_firstIds (g : Fin 3 → ℝ) : sampleGrid.FirstIds g where
  div i := by
    simp [Grid.pair, sampleGrid, sampleDv, Fin.sum_univ_three]
    ring
  first i j := by
    obtain rfl : i = j := Subsingleton.elim _ _
    simp [Grid.pair, sampleGrid, sampleDv, Fin.sum_univ_three]
    ring
  second i := by
    simp [Grid.pair, Grid.speed2, sampleGrid, sampleDv, Fin.sum_univ_three]
    ring

/-- arXiv 2608.00397, instance of the hypotheses: `sampleGrid` has the second-order identities. -/
theorem sample_secondIds (g : Fin 3 → ℝ) : sampleGrid.SecondIds g :=
  Grid.secondIds_of_comp (sample_firstIds g) (fun _ => sample_firstIds _) fun _ _ => rfl

/-- arXiv 2608.00397, instance of the hypotheses: `sampleGrid` has periodic spatial cancellation. -/
theorem sample_periodic : sampleGrid.PeriodicX := by
  intro i u
  simp [sampleGrid, sampleDx, Fin.sum_univ_three]
  ring

/-- arXiv 2608.00397, instance of the hypotheses: `U = 1` contains the moments on `sampleGrid`. -/
theorem sample_containsMoments : ContainsMoments sampleGrid (1 : Matrix (Fin 3) (Fin 3) ℝ) where
  one := ⟨1, by simp⟩
  node i := ⟨sampleGrid.node i, by simp⟩
  speed2 := ⟨sampleGrid.speed2, by simp⟩

/-- arXiv 2608.00397, instance of the hypotheses:
**The hypotheses of the balance laws can hold.**  On `sampleGrid`, with the fixed modes
`U = 1` of full rank, all assumptions of `local_mass`, `local_momentum`, `local_energy`, the total
laws and `expected_momentum` hold for both integrators, for all data and every state `f`; the step
exists, and it is the step of the full scheme. -/
theorem sample_nonvacuous {K : ℕ} (σ : Fin K → Fin 1 → Fin 3 → ℝ) (τ : ℝ) (Δβ : Fin K → ℝ)
    (E : Fin 1 → Fin 3 → ℝ) (f : Matrix (Fin 3) (Fin 3) ℝ) :
    ((Integrator.em : Integrator (Fin 3)).Admissible sampleGrid σ Δβ f ∧
      (Integrator.em : Integrator (Fin 3)).Step sampleGrid (1 : Matrix (Fin 3) (Fin 3) ℝ) σ τ Δβ E f
        (f + sampleGrid.incEM σ τ Δβ E f)) ∧
    ((Integrator.heun LinearMap.id LinearMap.id).Admissible sampleGrid σ Δβ f ∧
      (Integrator.heun LinearMap.id LinearMap.id).Step sampleGrid
        (1 : Matrix (Fin 3) (Fin 3) ℝ) σ τ Δβ E f
        (f + sampleGrid.incHeun σ τ Δβ E LinearMap.id f)) := by
  have hst : ∀ I : Matrix (Fin 3) (Fin 3) ℝ → Matrix (Fin 3) (Fin 3) ℝ,
      IsStep sampleGrid (1 : Matrix (Fin 3) (Fin 3) ℝ) I I f (f + I f) := fun I =>
    ⟨0, 0, 3, 0, fullState f, fullState (f + I f), fullState_dist rfl f,
      fullState_dist rfl (f + I f), ⟨fullStep rfl rfl rfl I f⟩⟩
  refine ⟨⟨⟨fun _ => sample_firstIds _, fun _ => sample_secondIds _⟩, hst _⟩,
    ⟨⟨fun _ => sample_firstIds _, Grid.preservesMoments_id, Grid.preservesMoments_id,
      fun _ => sample_firstIds _, fun _ => sample_firstIds _⟩, hst _⟩⟩

end Instance

/-! ### The moments and the transport operator in the core vocabulary

The moments of the grid are the core quadrature moments for the velocity weights `G.wv`, and the
transport operator with a frozen field is minus an instance of the core operator
`Kinetic.streaming`. The local definitions stay: they are the core notions at the fields of the
structure `Grid`. -/

section KineticCore

open scoped LeanDLRA.Frobenius

/-- The pairing `(p, f(x, ·))_v` is the core quadrature moment of `p` at `x`, for the velocity
weights `G.wv`. -/
theorem Grid.pair_eq_quadMoment {X V : Type*} {d : ℕ} [Fintype V] (G : Grid X V d) (p : V → ℝ)
    (f : Matrix X V ℝ) (x : X) : G.pair p (f x) = Kinetic.quadMoment G.wv p f x :=
  rfl

/-- The density of the grid is the core density for the velocity weights `G.wv`. -/
theorem Grid.dens_eq_density {X V : Type*} {d : ℕ} [Fintype V] (G : Grid X V d)
    (f : Matrix X V ℝ) : G.dens f = Kinetic.density G.wv f :=
  rfl

/-- The current `Jᵢ` is the core quadrature moment of the velocity component `vᵢ`. -/
theorem Grid.cur_eq_quadMoment {X V : Type*} {d : ℕ} [Fintype V] (G : Grid X V d)
    (f : Matrix X V ℝ) (i : Fin d) : G.cur f i = Kinetic.quadMoment G.wv (G.node i) f :=
  rfl

/-- The stress `Πᵢⱼ` is the core quadrature moment of `vᵢ vⱼ`. -/
theorem Grid.stress_eq_quadMoment {X V : Type*} {d : ℕ} [Fintype V] (G : Grid X V d)
    (f : Matrix X V ℝ) (i j : Fin d) :
    G.stress f i j = Kinetic.quadMoment G.wv (G.node i * G.node j) f :=
  rfl

/-- The kinetic energy density is half the core quadrature moment of `|v|²`. -/
theorem Grid.kin_eq_quadMoment {X V : Type*} {d : ℕ} [Fintype V] (G : Grid X V d)
    (f : Matrix X V ℝ) (x : X) : G.kin f x = 1 / 2 * Kinetic.quadMoment G.wv G.speed2 f x :=
  rfl

/-- The energy flux `Qⱼ` is half the core quadrature moment of `vⱼ |v|²`. -/
theorem Grid.heat_eq_quadMoment {X V : Type*} {d : ℕ} [Fintype V] (G : Grid X V d)
    (f : Matrix X V ℝ) (j : Fin d) (x : X) :
    G.heat f j x = 1 / 2 * Kinetic.quadMoment G.wv (G.node j * G.speed2) f x :=
  rfl

/-- **The transport operator through the core**: `D(f) = -v·∇ₓ f - E·∇ᵥ f` with a frozen field
`E` is minus the core streaming operator `Y ↦ ∑ₖ Dₖ Y Mₖ` with the `2 d` terms `(∂ₓᵢ, diag vᵢ)`
and `(diag Eᵢ, ∂ᵥᵢᵀ)`, the discrete derivatives written as matrices. -/
theorem Grid.transport_eq_neg_streaming {X V : Type*} {d : ℕ} [Fintype X] [Fintype V]
    [DecidableEq X] [DecidableEq V] (G : Grid X V d) (E : Fin d → X → ℝ) (f : Matrix X V ℝ) :
    G.transport E f = -Kinetic.streaming
      (Sum.elim (fun i => LinearMap.toMatrix' (G.Dx i)) fun i => diagonal (E i))
      (Sum.elim (fun i => diagonal (G.node i)) fun i => (LinearMap.toMatrix' (G.Dv i))ᵀ) f := by
  have hx : ∀ (i : Fin d) (x : X) (v : V),
      (LinearMap.toMatrix' (G.Dx i) * f * diagonal (G.node i)) x v
        = G.node i v * G.Dx i (fun y => f y v) x := fun i x v => by
    have h : (LinearMap.toMatrix' (G.Dx i) * f) x v = G.Dx i (fun y => f y v) x :=
      congrFun (LinearMap.toMatrix'_mulVec (G.Dx i) fun y => f y v) x
    rw [Matrix.mul_diagonal, h]
    exact mul_comm _ _
  have hv : ∀ (i : Fin d) (x : X) (v : V),
      (diagonal (E i) * f * (LinearMap.toMatrix' (G.Dv i))ᵀ) x v
        = E i x * G.Dv i (f x) v := fun i x v => by
    have h1 : (diagonal (E i) * f) x = E i x • f x :=
      funext fun v' => Matrix.diagonal_mul (E i) f x v'
    have h2 : (diagonal (E i) * f * (LinearMap.toMatrix' (G.Dv i))ᵀ) x v
        = (LinearMap.toMatrix' (G.Dv i) *ᵥ (diagonal (E i) * f) x) v :=
      congrFun (Matrix.vecMul_transpose (LinearMap.toMatrix' (G.Dv i))
        ((diagonal (E i) * f) x)) v
    rw [h2, h1, LinearMap.toMatrix'_mulVec, map_smul, Pi.smul_apply, smul_eq_mul]
  ext x v
  simp only [Kinetic.streaming_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Matrix.neg_apply, Matrix.add_apply, Matrix.sum_apply, hx, hv, Grid.transport]
  ring

/-- The moment bridges at nonzero data: on `sampleGrid` (nodes `-1, 0, 1`, unit weights) the
profile `(1, 2, 4)` has the core density `7`, the core current `3` and the core stress `5`. -/
example :
    Kinetic.density sampleGrid.wv (Matrix.of fun _ : Fin 3 => ![1, 2, 4]) 0 = 7 ∧
      Kinetic.quadMoment sampleGrid.wv (sampleGrid.node 0)
        (Matrix.of fun _ : Fin 3 => ![1, 2, 4]) 0 = 3 ∧
      Kinetic.quadMoment sampleGrid.wv (sampleGrid.node 0 * sampleGrid.node 0)
        (Matrix.of fun _ : Fin 3 => ![1, 2, 4]) 0 = 5 := by
  rw [← Grid.dens_eq_density, ← Grid.cur_eq_quadMoment, ← Grid.stress_eq_quadMoment]
  norm_num [Grid.dens, Grid.cur, Grid.stress, Grid.pair, sampleGrid, Fin.sum_univ_three,
    Matrix.of_apply]

/-- The transport bridge in use: on `sampleGrid` (nodes `-1, 0, 1`, the centred difference in
`x`) the transport operator with a frozen field is additive, because it is minus a continuous
linear map. -/
example (E : Fin 1 → Fin 3 → ℝ) (f g : Matrix (Fin 3) (Fin 3) ℝ) :
    sampleGrid.transport E (f + g) = sampleGrid.transport E f + sampleGrid.transport E g := by
  simp only [Grid.transport_eq_neg_streaming, map_add, neg_add]

end KineticCore

end LeanDLRA.Literature.P2608_00397
