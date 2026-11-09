import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Stability.Conservation

/-!
# Results of arXiv 2503.10562: DG conservative DLRA for Vlasov–Poisson

Uschmajew, Zeiser, *Discontinuous Galerkin discretization of conservative dynamical low-rank
approximation schemes for the Vlasov-Poisson equation*. A periodic mesh in any dimension is modelled
by `BrokenCalculus`: a commutative algebra of broken functions with elementwise derivatives,
elementwise and face integrals and two traces on every face, whose only analytic assumption is the
Gauss–Green formula summed over the elements. `periodicCalculus` builds it from the fundamental
theorem of calculus for a periodic mesh of an interval, `dgSpace` gives the piecewise polynomials
with a positive weight, and `phase1D` is the resulting `1 + 1`-dimensional scheme; for `d ≥ 2` no
concrete mesh is built, so there `gauss_green` is a property of the mesh that is assumed.
`BrokenCalculus.dForm` is the discrete derivative (33), `lemma_3_1` is Lemma 3.1, and `dForm_skew`
says that the central-flux derivative is skew-adjoint. `PhaseSpace.Fhat` is `F̂` acting on
`Y = f / ω ∈ 𝒱⁽ˣ⁾ ⊗ 𝒱⁽ᵛ⁾`, and `inner_Fhat_tmul` is its pairing `(F̂(f), ψ ⊗ W)_{xv}`. `IsKStep` and
`IsSStep` are the K-step (34) and the S-step (36) with their matrices, `lemma_3_2_K`, `lemma_3_2_S`,
`lemma_3_2_K_proj` and `lemma_3_2_S_proj` are Lemma 3.2, `IsConsStep` is one step of the algorithm
of Section 3.2 with the truncation (29), and `lemma_3_3` is Lemma 3.3, by the library's
`consBug_euler_local_law`. `theorem_3_4` and `mass_conservation` are Theorem 3.4, `theorem_3_5` and
`momentum_conservation` are Theorem 3.5 with the paper's support assumption of Section 3.1 made an
explicit hypothesis, and `theorem_3_4_periodic` and `theorem_3_5_periodic` write them out with
literal integrals for `d = 1`. `tangentSet_eq`,
`tangentV_inter_tangentZ`, `isOrthProj_tangentProj`, `tangentProj_eq_iff`, `velocityProj_split`,
`tangentProj_orthogonal` and `modified_steps` are Section 2.3 on two arbitrary inner product spaces.
**Theorem 3.5 and the support assumption.** The paper's velocity domain is `ℝᵈ`; Section 3.1
assumes that the computational domain contains the support of the solution in its interior (up to
machine precision) and treats it as periodic. The proof of Theorem 3.5 uses
`(d̂_{v_s} f, v_t)_v = -δ_{st} ρ`, which needs `{f}_e [v_t]_e = 0` on all faces; on a periodic
velocity mesh `v_t` jumps across the wrap-around faces (by `vol_one_eq_skel_jump` it has to), so
this is exactly where the support assumption enters. The law without that assumption is
`theorem_3_5_defect`, whose right side is `∑_s (E_s β_{st}, ψ)_x` with
`β_{st} = ∑_e ∫_e n_s {f}_e [v_t]_e dS`. The support assumption is the hypothesis `β = 0` of
`theorem_3_5`, which `bdryMoment_eq_zero` derives from the velocity factors, and
`exists_momentum_instance` shows that it holds together with all other hypotheses.
`theorem_3_5_false_on_periodic_velocity_mesh` shows that the assumption cannot be dropped: for a
concrete state that does not vanish at the velocity boundary, with its exact Poisson field, on
every periodic velocity mesh and for every positive weight (the Gaussian `gaussW` included), the
defect is nonzero. That state violates the paper's assumption, so it is not a counterexample to the
printed Theorem 3.5. (The proof prints this identity as `+δ_{s's} ρⁿ`; the sign that gives (45)
and (38) is `-`, as in `dvMomF_vel`.) Further
differences from the paper: the flux is central (`α = 1`), as in the paper's theorems, and the
upwind flux is not defined; every face is flat, with one normal; the infinite mesh of
`Ω⁽ᵛ⁾ = ℝᵈ` is not modelled, since the paper's DG section treats the computational domain as
periodic; the L-step is not used, so `Ṽ` is any orthonormal family whose span contains `V`; the
family `V` contains `U` only in span, `X` need not be orthonormal, and all bases have arbitrary
finite size; `E` is an arbitrary broken function in Theorems 3.4 and 3.5, and only
`momentum_conservation` assumes the exact Poisson solve `IsPoissonField`; each statement is about
one step `n → n + 1`, for arbitrary data, and `exists_isConsStep` shows that every state has a
step; in Section 2.3 the fixed functions `U_a` are any orthonormal family rather than
`1, v, |v|²`, and the modified K-, L- and S-steps are given by the splitting of the tangent
projector and not by their matrix equations.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix TensorProduct

namespace LeanDLRA.Literature.P2503_10562

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

/-! ### The broken calculus of a periodic mesh -/

/-- The broken calculus of a periodic mesh, in any dimension (`ι` indexes the coordinates).
`B` is a commutative algebra of broken functions, smooth on each element, and `A` holds the traces
on the faces. Every face `e` is internal, with neighbours `T⁻`, `T⁺` and a constant normal
pointing from `T⁻` to `T⁺` (arXiv 2503.10562, Section 3.1). The mesh enters only through
`gauss_green`: Gauss–Green on each element, summed over all elements, is
`∑_T ∫_T ∂_s u = ∑_e ∫_e n_s (u⁻ - u⁺) dS`. `periodicCalculus` is a concrete instance. -/
structure BrokenCalculus (ι 𝓣 𝓕 B A : Type*) [Fintype 𝓣] [Fintype 𝓕]
    [CommRing B] [Algebra ℝ B] [CommRing A] [Algebra ℝ A] where
  /-- `∫_T u`. -/
  elemInt : 𝓣 → B →ₗ[ℝ] ℝ
  /-- `∫_e a dS`. -/
  faceInt : 𝓕 → A →ₗ[ℝ] ℝ
  /-- The unit normal `n⁽ᵉ⁾`, pointing from `T⁻` to `T⁺`. -/
  normal : 𝓕 → ι → ℝ
  /-- The trace `U⁻` from the element `T⁻`. -/
  traceMinus : 𝓕 → B →ₐ[ℝ] A
  /-- The trace `U⁺` from the element `T⁺`. -/
  tracePlus : 𝓕 → B →ₐ[ℝ] A
  /-- The elementwise partial derivative `∂_s`. -/
  pd : ι → Derivation ℝ B B
  /-- Elementwise partial derivatives commute. -/
  pd_comm : ∀ s t u, pd s (pd t u) = pd t (pd s u)
  /-- Gauss–Green, summed over the elements. -/
  gauss_green : ∀ s u, ∑ T, elemInt T (pd s u) =
    ∑ e, faceInt e (normal e s • (traceMinus e u - tracePlus e u))

namespace BrokenCalculus

variable {ι 𝓣 𝓕 B A : Type*} [Fintype 𝓣] [Fintype 𝓕] [CommRing B] [Algebra ℝ B] [CommRing A]
  [Algebra ℝ A] (C : BrokenCalculus ι 𝓣 𝓕 B A)

/-- `∑_T ∫_T u`. -/
noncomputable def vol : B →ₗ[ℝ] ℝ := ∑ T, C.elemInt T

/-- `∑_e ∫_e n_s a_e dS`. -/
noncomputable def skel (s : ι) : (𝓕 → A) →ₗ[ℝ] ℝ :=
  ∑ e, (C.faceInt e) ∘ₗ (C.normal e s • (LinearMap.proj e : (𝓕 → A) →ₗ[ℝ] A))

/-- The average `{U}_e = (U⁺ + U⁻) / 2`. -/
noncomputable def avg (e : 𝓕) : B →ₗ[ℝ] A :=
  (2⁻¹ : ℝ) • ((C.tracePlus e).toLinearMap + (C.traceMinus e).toLinearMap)

/-- The jump `[U]_e = U⁻ - U⁺`. -/
noncomputable def jump (e : 𝓕) : B →ₗ[ℝ] A :=
  (C.traceMinus e).toLinearMap - (C.tracePlus e).toLinearMap

lemma vol_apply (u : B) : C.vol u = ∑ T, C.elemInt T u := by simp [vol]

lemma skel_apply (s : ι) (a : 𝓕 → A) : C.skel s a = ∑ e, C.faceInt e (C.normal e s • a e) := by
  simp [skel]

lemma avg_apply (e : 𝓕) (u : B) :
    C.avg e u = (2⁻¹ : ℝ) • (C.tracePlus e u + C.traceMinus e u) := by simp [avg]

lemma jump_apply (e : 𝓕) (u : B) : C.jump e u = C.traceMinus e u - C.tracePlus e u := by
  simp [jump]

@[simp] lemma jump_one (e : 𝓕) : C.jump e 1 = 0 := by simp [jump_apply]

@[simp] lemma avg_one (e : 𝓕) : C.avg e 1 = 1 := by
  rw [avg_apply, map_one, map_one, ← two_smul ℝ (1 : A), smul_smul]
  simp

/-- The algebraic identity `[U V] = [U]{V} + {U}[V]`. -/
lemma jump_mul (e : 𝓕) (U V : B) :
    C.jump e (U * V) = C.jump e U * C.avg e V + C.avg e U * C.jump e V := by
  simp only [jump_apply, avg_apply, map_mul, Algebra.smul_def]
  have h : algebraMap ℝ A 2⁻¹ * 2 = 1 := by
    rw [← map_ofNat (algebraMap ℝ A) 2, ← map_mul]; simp
  linear_combination
    (-(C.traceMinus e U * C.traceMinus e V - C.tracePlus e U * C.tracePlus e V)) * h

/-- The summed Gauss–Green formula. -/
lemma vol_pd (s : ι) (u : B) : C.vol (C.pd s u) = C.skel s (fun e => C.jump e u) := by
  simp only [vol_apply, skel_apply, jump_apply]
  exact C.gauss_green s u

/-- The discrete derivative of arXiv 2503.10562, Eq. (33), as a bilinear form:
`(d̂_{y_s} U, V)_y = ∑_T ∫_T ∂_s U V - ∑_e ∫_e n_s [U]_e {V}_e dS`. -/
noncomputable def dForm (s : ι) (U V : B) : ℝ :=
  C.vol (C.pd s U * V) - C.skel s (fun e => C.jump e U * C.avg e V)

/-- arXiv 2503.10562, Lemma 3.1 (discrete integration by parts):
`(d̂_{y_s} U, V)_y = -∑_T ∫_T U ∂_s V + ∑_e ∫_e n_s {U}_e [V]_e dS`, for all broken `U`, `V`. -/
theorem lemma_3_1 (s : ι) (U V : B) :
    C.dForm s U V = - C.vol (U * C.pd s V) + C.skel s (fun e => C.avg e U * C.jump e V) := by
  have h := C.vol_pd s (U * V)
  have h1 : (fun e => C.jump e (U * V)) =
      (fun e => C.jump e U * C.avg e V) + (fun e => C.avg e U * C.jump e V) := by
    funext e; simp [jump_mul]
  rw [h1, map_add, Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul] at h
  rw [dForm, mul_comm (C.pd s U) V]
  linarith

/-- arXiv 2503.10562, consequence of Lemma 3.1: the central-flux discrete derivative is
skew-adjoint, `(d̂_{y_s} U, V)_y = -(d̂_{y_s} V, U)_y`. -/
theorem dForm_skew (s : ι) (U V : B) : C.dForm s U V = - C.dForm s V U := by
  have h1 : U * C.pd s V = C.pd s V * U := mul_comm _ _
  have h2 : (fun e => C.avg e U * C.jump e V) = (fun e => C.jump e V * C.avg e U) := by
    funext e; exact mul_comm _ _
  rw [lemma_3_1, dForm, h1, h2]
  ring

end BrokenCalculus

namespace BrokenCalculus

variable {ι 𝓣 𝓕 B A : Type*} [Fintype 𝓣] [Fintype 𝓕] [CommRing B] [Algebra ℝ B] [CommRing A]
  [Algebra ℝ A] (C : BrokenCalculus ι 𝓣 𝓕 B A)

/-- The bilinear form `(U, V) ↦ ∑_T ∫_T g U V`. -/
noncomputable def mulForm (g : B) : B →ₗ[ℝ] B →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun a b => C.vol (g * a * b))
    (fun a b c => by rw [mul_add, add_mul, map_add])
    (fun r a b => by rw [mul_smul_comm, smul_mul_assoc, map_smul])
    (fun a b c => by rw [mul_add, map_add])
    (fun r a b => by rw [mul_smul_comm, map_smul])

@[simp] lemma mulForm_apply (g a b : B) : C.mulForm g a b = C.vol (g * a * b) := rfl

lemma skel_add (s : ι) {f g h : 𝓕 → A} (H : ∀ e, f e = g e + h e) :
    C.skel s f = C.skel s g + C.skel s h := by
  rw [show f = g + h from funext H, map_add]

lemma skel_smul (s : ι) (r : ℝ) {f g : 𝓕 → A} (H : ∀ e, f e = r • g e) :
    C.skel s f = r * C.skel s g := by
  rw [show f = r • g from funext H, map_smul, smul_eq_mul]

/-- The bilinear form (33). -/
noncomputable def dFormL (s : ι) : B →ₗ[ℝ] B →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (C.dForm s)
    (fun a b c => by
      have h := C.skel_add s (f := fun e => C.jump e (a + b) * C.avg e c)
        (g := fun e => C.jump e a * C.avg e c) (h := fun e => C.jump e b * C.avg e c)
        (fun e => by rw [map_add, add_mul])
      rw [dForm, dForm, dForm, h, map_add (C.pd s), add_mul, map_add C.vol]
      ring)
    (fun r a b => by
      have h := C.skel_smul s r (f := fun e => C.jump e (r • a) * C.avg e b)
        (g := fun e => C.jump e a * C.avg e b)
        (fun e => by rw [map_smul, smul_mul_assoc])
      rw [dForm, dForm, h, (C.pd s).map_smul, smul_mul_assoc, map_smul, smul_eq_mul, smul_eq_mul]
      ring)
    (fun a b c => by
      have h := C.skel_add s (f := fun e => C.jump e a * C.avg e (b + c))
        (g := fun e => C.jump e a * C.avg e b) (h := fun e => C.jump e a * C.avg e c)
        (fun e => by rw [map_add, mul_add])
      rw [dForm, dForm, dForm, h, mul_add, map_add C.vol]
      ring)
    (fun r a b => by
      have h := C.skel_smul s r (f := fun e => C.jump e a * C.avg e (r • b))
        (g := fun e => C.jump e a * C.avg e b)
        (fun e => by rw [map_smul, mul_smul_comm])
      rw [dForm, dForm, h, mul_smul_comm, map_smul, smul_eq_mul, smul_eq_mul]
      ring)

@[simp] lemma dFormL_apply (s : ι) (a b : B) : C.dFormL s a b = C.dForm s a b := rfl

lemma sum_elemInt_sum [Fintype ι] (g : ι → B) :
    ∑ T, ∑ s, C.elemInt T (g s) = ∑ s, C.vol (g s) := by
  simp only [vol_apply]
  exact Finset.sum_comm

lemma sum_elemInt (u : B) : ∑ T, C.elemInt T u = C.vol u := (C.vol_apply u).symm

/-- A function without jumps has zero mean derivative. -/
lemma vol_pd_eq_zero (s : ι) {u : B} (hu : ∀ e, C.jump e u = 0) : C.vol (C.pd s u) = 0 := by
  rw [vol_pd, show (fun e => C.jump e u) = 0 from funext hu, map_zero]

/-- A periodic mesh has no global coordinate: if `∂_t c = 1` then
`∑_T ∫_T 1 = ∑_e ∫_e n_t [c]_e dS`, so `c` jumps somewhere as soon as the domain has positive
measure. For `c = v_t` this is the term that the support assumption of Section 3.1 of
arXiv 2503.10562 removes from the proof of Theorem 3.5. -/
lemma vol_one_eq_skel_jump {t : ι} {c : B} (hc : C.pd t c = 1) :
    C.vol 1 = C.skel t (fun e => C.jump e c) := by
  rw [← hc, vol_pd]

/-- The field `E = -∇Φ` of the Poisson equation `-ΔΦ = 1 - ρ` of arXiv 2503.10562, solved exactly:
the equation holds on each element, and `Φ` and `E` have no jumps. -/
structure IsPoissonField [Fintype ι] (Ef : ι → B) (ρ Φ : B) : Prop where
  /-- `E = -∇Φ`. -/
  grad : ∀ s, Ef s = - C.pd s Φ
  /-- `-ΔΦ = 1 - ρ`. -/
  poisson : - ∑ s, C.pd s (C.pd s Φ) = 1 - ρ
  /-- `Φ` is continuous and periodic. -/
  pot_cont : ∀ e, C.jump e Φ = 0
  /-- `E` is continuous and periodic. -/
  field_cont : ∀ s e, C.jump e (Ef s) = 0

/-- arXiv 2503.10562, end of Theorem 3.5: for the exact field, `∫ E_t ρ = 0`. As in the paper,
`E (1 - ρ)` is a divergence (`∂_s (E_t E_s) - ∂_t (E_s²) / 2`) and `∫ E_t = 0`; no jump term
appears because `E` and `Φ` have no jumps. -/
theorem IsPoissonField.vol_field_mul_rho [Fintype ι] {C : BrokenCalculus ι 𝓣 𝓕 B A}
    {Ef : ι → B} {ρ Φ : B} (h : C.IsPoissonField Ef ρ Φ) (t : ι) : C.vol (Ef t * ρ) = 0 := by
  have hρ : ρ = 1 - ∑ s, C.pd s (Ef s) := by
    have := h.poisson
    simp only [h.grad, map_neg, Finset.sum_neg_distrib] at this ⊢
    linear_combination this
  have hcurl : ∀ s, C.pd s (Ef t) = C.pd t (Ef s) := by
    intro s
    rw [h.grad, h.grad, map_neg, map_neg, C.pd_comm]
  have h2 : ∀ s, (2⁻¹ : ℝ) • C.pd t (Ef s * Ef s) = Ef s * C.pd s (Ef t) := by
    intro s
    rw [Derivation.leibniz, smul_eq_mul, ← two_smul ℝ (Ef s * C.pd t (Ef s)), smul_smul, hcurl s]
    norm_num
  have h3 : ∀ s, C.pd s (Ef t * Ef s) = Ef t * C.pd s (Ef s) + Ef s * C.pd s (Ef t) := by
    intro s
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  have key : Ef t * ρ = Ef t - ∑ s, C.pd s (Ef t * Ef s) +
      ∑ s, (2⁻¹ : ℝ) • C.pd t (Ef s * Ef s) := by
    simp only [h2, h3, Finset.sum_add_distrib]
    rw [hρ, mul_sub, mul_one, Finset.mul_sum]
    ring
  have h4 : C.vol (Ef t) = 0 := by
    rw [h.grad, map_neg, C.vol_pd_eq_zero t h.pot_cont, neg_zero]
  have h5 : ∀ s, C.vol (C.pd s (Ef t * Ef s)) = 0 := fun s =>
    C.vol_pd_eq_zero s fun e => by simp [jump_mul, h.field_cont]
  have h6 : ∀ s, C.vol (C.pd t (Ef s * Ef s)) = 0 := fun s =>
    C.vol_pd_eq_zero t fun e => by simp [jump_mul, h.field_cont]
  rw [key, map_add, map_sub, map_sum, map_sum, h4]
  simp only [map_smul, h5, h6, smul_zero, Finset.sum_const_zero, sub_zero, add_zero]

/-- Exchange of the sums in the face term: `∑_e ∫_e (∑_s n_s a_s) j = ∑_s ∑_e ∫_e n_s a_s j`. -/
lemma sum_faceInt_normal [Fintype ι] (a : ι → 𝓕 → A) (j : 𝓕 → A) :
    ∑ e, C.faceInt e ((∑ s, C.normal e s • a s e) * j e) =
      ∑ s, C.skel s (fun e => a s e * j e) := by
  simp only [skel_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_mul, map_sum]
  simp only [smul_mul_assoc]

end BrokenCalculus

/-! ### Discrete spaces and Riesz representers -/

/-- A discrete space `𝒳` with inner product `∑_T ∫_T w a b`, embedded in the broken functions.
For `w = 1` this is `(·,·)_x` and for `w = ω` it is `(·,·)_{v,ω}` of arXiv 2503.10562. No polynomial
structure is needed; `dgSpace` is the space of piecewise polynomials. -/
structure DGSpace {ι 𝓣 𝓕 B A : Type*} [Fintype 𝓣] [Fintype 𝓕] [CommRing B] [Algebra ℝ B]
    [CommRing A] [Algebra ℝ A] (C : BrokenCalculus ι 𝓣 𝓕 B A) (w : B) (𝒳 : Type*)
    [NormedAddCommGroup 𝒳] [InnerProductSpace ℝ 𝒳] where
  /-- The embedding into the broken functions. -/
  emb : 𝒳 →ₗ[ℝ] B
  /-- The inner product is the weighted `L²` product. -/
  inner_eq : ∀ a b, ⟪a, b⟫ = C.vol (w * emb a * emb b)

section Riesz

variable {𝒳 : Type*} [NormedAddCommGroup 𝒳] [InnerProductSpace ℝ 𝒳] [FiniteDimensional ℝ 𝒳]

/-- The operator `T` with `⟪T a, b⟫ = β a b`, the Riesz representer of a bilinear form. -/
noncomputable def reprOp (β : 𝒳 →ₗ[ℝ] 𝒳 →ₗ[ℝ] ℝ) : 𝒳 →L[ℝ] 𝒳 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a => (InnerProductSpace.toDual ℝ 𝒳).symm (LinearMap.toContinuousLinearMap (β a))
      map_add' := fun a b => by
        rw [map_add, map_add, map_add]
      map_smul' := fun c a => by
        rw [map_smul, map_smul, RingHom.id_apply]
        simp }

lemma inner_reprOp (β : 𝒳 →ₗ[ℝ] 𝒳 →ₗ[ℝ] ℝ) (a b : 𝒳) : ⟪reprOp β a, b⟫ = β a b := by
  simp [reprOp, InnerProductSpace.toDual_symm_apply]

end Riesz

/-! ### Projectors on the tensor product -/

section Tensor

variable {𝒳 𝒴 : Type*} [NormedAddCommGroup 𝒳] [InnerProductSpace ℝ 𝒳] [NormedAddCommGroup 𝒴]
  [InnerProductSpace ℝ 𝒴]

/-- The projector `x ↦ ∑ᵢ ⟪eᵢ, x⟫ eᵢ`. -/
noncomputable def basisProj {J : Type*} [Fintype J] (e : J → 𝒳) : 𝒳 →L[ℝ] 𝒳 :=
  ∑ j, rankOneProj (e j)

lemma basisProj_apply {J : Type*} [Fintype J] (e : J → 𝒳) (x : 𝒳) :
    basisProj e x = ∑ j, ⟪e j, x⟫ • e j := by
  simp [basisProj]

lemma basisProj_of_mem {J : Type*} [Fintype J] {e : J → 𝒳} (he : Orthonormal ℝ e) {x : 𝒳}
    (hx : x ∈ Submodule.span ℝ (Set.range e)) : basisProj e x = x := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [basisProj_apply]
    simp [orthonormal_iff_ite.mp he]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

lemma basisProj_mem {J : Type*} [Fintype J] (e : J → 𝒳) (x : 𝒳) :
    basisProj e x ∈ Submodule.span ℝ (Set.range e) := by
  rw [basisProj_apply]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

lemma isOrthProj_basisProj {J : Type*} [Fintype J] {e : J → 𝒳} (he : Orthonormal ℝ e) :
    IsOrthProj (basisProj e) where
  idem x := basisProj_of_mem he (basisProj_mem e x)
  symm x y := by
    simp only [basisProj_apply, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_comm x (e j)]
    ring

lemma isOrthProj_rTensor {P : 𝒳 →L[ℝ] 𝒳} (hP : IsOrthProj P) :
    IsOrthProj (P.rTensor 𝒴) where
  idem z := by
    induction z using TensorProduct.inductionOn with
    | tmul a b => simp [hP.idem]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  symm x y := by
    induction x using TensorProduct.inductionOn with
    | add x₁ x₂ h₁ h₂ => simp only [map_add, inner_add_left, h₁, h₂]
    | tmul a b =>
      induction y using TensorProduct.inductionOn with
      | add y₁ y₂ h₁ h₂ => simp only [map_add, inner_add_right, h₁, h₂]
      | tmul c d => simp [TensorProduct.inner_tmul, hP.symm]

lemma isOrthProj_lTensor {Q : 𝒴 →L[ℝ] 𝒴} (hQ : IsOrthProj Q) :
    IsOrthProj (Q.lTensor 𝒳) where
  idem z := by
    induction z using TensorProduct.inductionOn with
    | tmul a b => simp [hQ.idem]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  symm x y := by
    induction x using TensorProduct.inductionOn with
    | add x₁ x₂ h₁ h₂ => simp only [map_add, inner_add_left, h₁, h₂]
    | tmul a b =>
      induction y using TensorProduct.inductionOn with
      | add y₁ y₂ h₁ h₂ => simp only [map_add, inner_add_right, h₁, h₂]
      | tmul c d => simp [TensorProduct.inner_tmul, hQ.symm]

lemma rTensor_lTensor_comm (P : 𝒳 →L[ℝ] 𝒳) (Q : 𝒴 →L[ℝ] 𝒴) (z : 𝒳 ⊗[ℝ] 𝒴) :
    P.rTensor 𝒴 (Q.lTensor 𝒳 z) = Q.lTensor 𝒳 (P.rTensor 𝒴 z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The contraction `a ⊗ V ↦ φ(V) a` in the velocity factor. -/
noncomputable def contr (φ : 𝒴 →ₗ[ℝ] ℝ) : (𝒳 ⊗[ℝ] 𝒴) →ₗ[ℝ] 𝒳 :=
  (TensorProduct.rid ℝ 𝒳).toLinearMap ∘ₗ (LinearMap.lTensor 𝒳 φ)

@[simp] lemma contr_tmul (φ : 𝒴 →ₗ[ℝ] ℝ) (a : 𝒳) (V : 𝒴) :
    contr φ (a ⊗ₜ[ℝ] V) = φ V • a := by
  simp [contr]

/-- The contraction `a ⊗ V ↦ φ(a) V` in the space factor. -/
noncomputable def contrL (φ : 𝒳 →ₗ[ℝ] ℝ) : (𝒳 ⊗[ℝ] 𝒴) →ₗ[ℝ] 𝒴 :=
  (TensorProduct.lid ℝ 𝒴).toLinearMap ∘ₗ (LinearMap.rTensor 𝒴 φ)

@[simp] lemma contrL_tmul (φ : 𝒳 →ₗ[ℝ] ℝ) (a : 𝒳) (V : 𝒴) :
    contrL φ (a ⊗ₜ[ℝ] V) = φ a • V := by
  simp [contrL]

/-- `⟨z, W⟩_v`: contraction with the inner product against `W`. -/
noncomputable abbrev contrV (W : 𝒴) : (𝒳 ⊗[ℝ] 𝒴) →ₗ[ℝ] 𝒳 := contr (innerₗ 𝒴 W)

lemma inner_contrV (W : 𝒴) (z : 𝒳 ⊗[ℝ] 𝒴) (ψ : 𝒳) :
    ⟪contrV W z, ψ⟫ = ⟪z, ψ ⊗ₜ[ℝ] W⟫ := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    rw [contr_tmul, real_inner_smul_left, TensorProduct.inner_tmul, innerₗ_apply_apply,
      real_inner_comm b W, mul_comm]
  | add x y hx hy => simp only [map_add, inner_add_left, hx, hy]

/-- `P_V z = ∑ⱼ ⟨z, Vⱼ⟩_v ⊗ Vⱼ`. -/
lemma lTensor_basisProj_apply {J : Type*} [Fintype J] (V : J → 𝒴) (z : 𝒳 ⊗[ℝ] 𝒴) :
    (basisProj V).lTensor 𝒳 z = ∑ j, contrV (V j) z ⊗ₜ[ℝ] V j := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [ContinuousLinearMap.lTensor_tmul, basisProj_apply, contr_tmul,
      TensorProduct.tmul_sum, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      innerₗ_apply_apply]
  | add x y hx hy =>
    simp only [map_add, hx, hy, TensorProduct.add_tmul, Finset.sum_add_distrib]

/-- `P_Z z = ∑ₚ Zₚ ⊗ ⟨Zₚ, z⟩_x`. -/
lemma rTensor_basisProj_apply {J : Type*} [Fintype J] (Z : J → 𝒳) (z : 𝒳 ⊗[ℝ] 𝒴) :
    (basisProj Z).rTensor 𝒴 z = ∑ p, Z p ⊗ₜ[ℝ] contrL (innerₗ 𝒳 (Z p)) z := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [ContinuousLinearMap.rTensor_tmul, basisProj_apply, contrL_tmul,
      TensorProduct.sum_tmul, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      innerₗ_apply_apply]
  | add x y hx hy =>
    simp only [map_add, hx, hy, TensorProduct.tmul_add, Finset.sum_add_distrib]

/-- The Galerkin projection onto `span Xa ⊗ span Va` in coordinates. -/
lemma rTensor_lTensor_basisProj {K L : Type*} [Fintype K] [Fintype L] (P : K → 𝒳) (Q : L → 𝒴)
    (z : 𝒳 ⊗[ℝ] 𝒴) :
    (basisProj P).rTensor 𝒴 ((basisProj Q).lTensor 𝒳 z) =
      ∑ k, ∑ l, ⟪z, P k ⊗ₜ[ℝ] Q l⟫ • (P k ⊗ₜ[ℝ] Q l) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    rw [ContinuousLinearMap.lTensor_tmul, ContinuousLinearMap.rTensor_tmul, basisProj_apply,
      basisProj_apply, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [TensorProduct.tmul_smul, TensorProduct.inner_tmul, ← TensorProduct.smul_tmul', smul_smul,
      real_inner_comm (P k) a, real_inner_comm (Q l) b, mul_comm]
  | add x y hx hy =>
    simp only [map_add, hx, hy, inner_add_left, add_smul, Finset.sum_add_distrib]

lemma lTensor_fix {Q P : 𝒴 →L[ℝ] 𝒴} (h : ∀ y, Q (P y) = P y) (z : 𝒳 ⊗[ℝ] 𝒴) :
    Q.lTensor 𝒳 (P.lTensor 𝒳 z) = P.lTensor 𝒳 z := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp [h]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- `⟨P_U z, W⟩_v = ⟨z, W⟩_v` for `W ∈ span U`. -/
lemma contrV_lTensor {P : 𝒴 →L[ℝ] 𝒴} (hP : IsOrthProj P) {W : 𝒴} (hW : P W = W)
    (z : 𝒳 ⊗[ℝ] 𝒴) : contrV W (P.lTensor 𝒳 z) = contrV W z := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [ContinuousLinearMap.lTensor_tmul, contr_tmul, innerₗ_apply_apply]
    rw [← hP.symm, hW]
  | add x y hx hy => simp only [map_add, hx, hy]

end Tensor

/-! ### Section 2.3: the tangent space with fixed velocity functions -/

section TangentSplit

variable {𝒳 𝒴 : Type*} [NormedAddCommGroup 𝒳] [InnerProductSpace ℝ 𝒳] [NormedAddCommGroup 𝒴]
  [InnerProductSpace ℝ 𝒴] {𝔞 𝔭 : Type*} [Fintype 𝔞] [Fintype 𝔭]

/-- The tangent space `T_f M_{r,ω}` of Section 2.2, divided by `ω`. -/
def tangentSet (U : 𝔞 → 𝒴) (W : 𝔭 → 𝒴) (X : 𝔞 ⊕ 𝔭 → 𝒳) (S : Matrix (𝔞 ⊕ 𝔭) (𝔞 ⊕ 𝔭) ℝ) :
    Set (𝒳 ⊗[ℝ] 𝒴) :=
  {w | ∃ (dX : 𝔞 ⊕ 𝔭 → 𝒳) (dS : Matrix (𝔞 ⊕ 𝔭) (𝔞 ⊕ 𝔭) ℝ) (dW : 𝔭 → 𝒴),
    (∀ p a, ⟪U a, dW p⟫ = 0) ∧
    w = ∑ i, ∑ j, (S i j • dX i + dS i j • X i) ⊗ₜ[ℝ] Sum.elim U W j +
      ∑ i, ∑ p, S i (Sum.inr p) • (X i ⊗ₜ[ℝ] dW p)}

/-- The subspace `T_{V,ω}`, divided by `ω`. -/
def tangentV (U : 𝔞 → 𝒴) (W : 𝔭 → 𝒴) : Set (𝒳 ⊗[ℝ] 𝒴) :=
  {w | ∃ ψ : 𝔞 ⊕ 𝔭 → 𝒳, w = ∑ j, ψ j ⊗ₜ[ℝ] Sum.elim U W j}

/-- The subspace `T_{Z,ω}`, divided by `ω`. -/
def tangentZ (U : 𝔞 → 𝒴) (Z : 𝔭 → 𝒳) : Set (𝒳 ⊗[ℝ] 𝒴) :=
  {w | ∃ ψ : 𝔭 → 𝒴, (∀ p a, ⟪U a, ψ p⟫ = 0) ∧ w = ∑ p, Z p ⊗ₜ[ℝ] ψ p}

/-- The subspace `T_{Z,V,ω}`, divided by `ω`. -/
def tangentZV (W : 𝔭 → 𝒴) (Z : 𝔭 → 𝒳) : Set (𝒳 ⊗[ℝ] 𝒴) :=
  {w | ∃ c : Matrix 𝔭 𝔭 ℝ, w = ∑ p, ∑ q, c p q • (Z p ⊗ₜ[ℝ] W q)}

lemma basisProj_elim (U : 𝔞 → 𝒴) (W : 𝔭 → 𝒴) (y : 𝒴) :
    basisProj (Sum.elim U W) y = basisProj U y + basisProj W y := by
  simp [basisProj_apply, Fintype.sum_sum_type]

/-- `Q = C + Q_W`: the right projector splits into the fixed and the variable part. -/
lemma lTensor_basisProj_elim (U : 𝔞 → 𝒴) (W : 𝔭 → 𝒴) (z : 𝒳 ⊗[ℝ] 𝒴) :
    (basisProj (Sum.elim U W)).lTensor 𝒳 z =
      (basisProj U).lTensor 𝒳 z + (basisProj W).lTensor 𝒳 z := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp only [ContinuousLinearMap.lTensor_tmul, basisProj_elim,
      TensorProduct.tmul_add]
  | add x y hx hy => simp only [map_add, hx, hy]; abel

/-- `C Q_W = 0`. -/
lemma lTensor_orth {U : 𝔞 → 𝒴} {W : 𝔭 → 𝒴} (hV : Orthonormal ℝ (Sum.elim U W))
    (z : 𝒳 ⊗[ℝ] 𝒴) : (basisProj U).lTensor 𝒳 ((basisProj W).lTensor 𝒳 z) = 0 := by
  have hUW : ∀ a p, ⟪U a, W p⟫ = 0 := fun a p => by
    simpa using hV.2 (i := Sum.inl a) (j := Sum.inr p) (by simp)
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [ContinuousLinearMap.lTensor_tmul, basisProj_apply (e := U), basisProj_apply (e := W)]
    have : ∑ j, ⟪U j, ∑ q, ⟪W q, b⟫ • W q⟫ • U j = 0 :=
      Finset.sum_eq_zero fun j _ => by
        simp [inner_sum, real_inner_smul_right, hUW]
    rw [this, TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

/-- The left factor `P_Z (1 - C)` of the tangent projector (the L-step). -/
noncomputable def projL (U : 𝔞 → 𝒴) (Z : 𝔭 → 𝒳) : (𝒳 ⊗[ℝ] 𝒴) →L[ℝ] (𝒳 ⊗[ℝ] 𝒴) :=
  (basisProj Z).rTensor 𝒴 * (1 - (basisProj U).lTensor 𝒳)

lemma projL_apply (U : 𝔞 → 𝒴) (Z : 𝔭 → 𝒳) (z : 𝒳 ⊗[ℝ] 𝒴) :
    projL U Z z = (basisProj Z).rTensor 𝒴 (z - (basisProj U).lTensor 𝒳 z) := rfl

lemma isOrthProj_projL {U : 𝔞 → 𝒴} {Z : 𝔭 → 𝒳} (hU : Orthonormal ℝ U) (hZ : Orthonormal ℝ Z) :
    IsOrthProj (projL U Z) :=
  (isOrthProj_rTensor (isOrthProj_basisProj hZ)).mul
    (isOrthProj_lTensor (isOrthProj_basisProj hU)).compl fun x => by
      simp only [sub_apply, one_apply_eq_self, map_sub, rTensor_lTensor_comm]

lemma orth_left {U : 𝔞 → 𝒴} {W : 𝔭 → 𝒴} (hV : Orthonormal ℝ (Sum.elim U W)) :
    Orthonormal ℝ U := by
  simpa using hV.comp Sum.inl Sum.inl_injective

lemma orth_right {U : 𝔞 → 𝒴} {W : 𝔭 → 𝒴} (hV : Orthonormal ℝ (Sum.elim U W)) :
    Orthonormal ℝ W := by
  simpa using hV.comp Sum.inr Sum.inr_injective

/-- `C Q = C`. -/
lemma C_Q {U : 𝔞 → 𝒴} {W : 𝔭 → 𝒴} (hV : Orthonormal ℝ (Sum.elim U W)) (z : 𝒳 ⊗[ℝ] 𝒴) :
    (basisProj U).lTensor 𝒳 ((basisProj (Sum.elim U W)).lTensor 𝒳 z) =
      (basisProj U).lTensor 𝒳 z := by
  rw [lTensor_basisProj_elim, map_add, lTensor_orth hV, add_zero,
    (isOrthProj_lTensor (isOrthProj_basisProj (orth_left hV))).idem]

/-- `Q C = C`. -/
lemma Q_C {U : 𝔞 → 𝒴} {W : 𝔭 → 𝒴} (hV : Orthonormal ℝ (Sum.elim U W)) (z : 𝒳 ⊗[ℝ] 𝒴) :
    (basisProj (Sum.elim U W)).lTensor 𝒳 ((basisProj U).lTensor 𝒳 z) =
      (basisProj U).lTensor 𝒳 z := by
  have hC := isOrthProj_lTensor (𝒳 := 𝒳) (isOrthProj_basisProj (orth_left hV))
  have hW := isOrthProj_lTensor (𝒳 := 𝒳) (isOrthProj_basisProj (orth_right hV))
  rw [lTensor_basisProj_elim, hC.idem, hC.comp_eq_zero_of_comp_eq_zero hW (lTensor_orth hV),
    add_zero]

lemma projL_comm {U : 𝔞 → 𝒴} {W : 𝔭 → 𝒴} (hV : Orthonormal ℝ (Sum.elim U W)) (Z : 𝔭 → 𝒳)
    (z : 𝒳 ⊗[ℝ] 𝒴) :
    projL U Z ((basisProj (Sum.elim U W)).lTensor 𝒳 z) =
      (basisProj (Sum.elim U W)).lTensor 𝒳 (projL U Z z) := by
  simp only [projL_apply, map_sub, C_Q hV, Q_C hV, rTensor_lTensor_comm]

/-- `L Q = P_Z Q_W`: the S-step part of the tangent projector. -/
lemma projL_Q {U : 𝔞 → 𝒴} {W : 𝔭 → 𝒴} (hV : Orthonormal ℝ (Sum.elim U W)) (Z : 𝔭 → 𝒳)
    (z : 𝒳 ⊗[ℝ] 𝒴) :
    projL U Z ((basisProj (Sum.elim U W)).lTensor 𝒳 z) =
      (basisProj Z).rTensor 𝒴 ((basisProj W).lTensor 𝒳 z) := by
  rw [projL_apply, C_Q hV, lTensor_basisProj_elim, add_sub_cancel_left]

lemma inner_contrL_sub {P : 𝒴 →L[ℝ] 𝒴} (hP : IsOrthProj P) {u : 𝒴} (hu : P u = u)
    (φ : 𝒳 →ₗ[ℝ] ℝ) (z : 𝒳 ⊗[ℝ] 𝒴) : ⟪u, contrL φ (z - P.lTensor 𝒳 z)⟫ = 0 := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    rw [map_sub, ContinuousLinearMap.lTensor_tmul, contrL_tmul, contrL_tmul, inner_sub_right,
      real_inner_smul_right, real_inner_smul_right, ← hP.symm, hu, sub_self]
  | add x y hx hy =>
    have : x + y - P.lTensor 𝒳 (x + y) = (x - P.lTensor 𝒳 x) + (y - P.lTensor 𝒳 y) := by
      rw [map_add]; abel
    rw [this, map_add, inner_add_right, hx, hy, add_zero]

lemma mem_tangentV_iff {U : 𝔞 → 𝒴} {W : 𝔭 → 𝒴} (hV : Orthonormal ℝ (Sum.elim U W))
    (w : 𝒳 ⊗[ℝ] 𝒴) :
    w ∈ tangentV U W ↔ (basisProj (Sum.elim U W)).lTensor 𝒳 w = w := by
  constructor
  · rintro ⟨ψ, rfl⟩
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.lTensor_tmul,
      basisProj_of_mem hV (Submodule.subset_span ⟨j, rfl⟩)]
  · intro h
    exact ⟨fun j => contrV (Sum.elim U W j) w, by rw [← lTensor_basisProj_apply, h]⟩

lemma mem_tangentZ_iff {U : 𝔞 → 𝒴} {Z : 𝔭 → 𝒳} (hU : Orthonormal ℝ U) (hZ : Orthonormal ℝ Z)
    (w : 𝒳 ⊗[ℝ] 𝒴) : w ∈ tangentZ U Z ↔ projL U Z w = w := by
  have hC := isOrthProj_basisProj hU
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    have h0 : (basisProj U).lTensor 𝒳 (∑ p, Z p ⊗ₜ[ℝ] ψ p) = 0 := by
      rw [map_sum]
      refine Finset.sum_eq_zero fun p _ => ?_
      rw [ContinuousLinearMap.lTensor_tmul, basisProj_apply]
      simp [hψ p]
    rw [projL_apply, h0, sub_zero, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [ContinuousLinearMap.rTensor_tmul,
      basisProj_of_mem hZ (Submodule.subset_span ⟨p, rfl⟩)]
  · intro h
    refine ⟨fun p => contrL (innerₗ 𝒳 (Z p)) (w - (basisProj U).lTensor 𝒳 w), fun p a => ?_, ?_⟩
    · exact inner_contrL_sub hC (basisProj_of_mem hU (Submodule.subset_span ⟨a, rfl⟩)) _ w
    · rw [← rTensor_basisProj_apply, ← projL_apply, h]

private lemma sum_block {X : 𝔞 ⊕ 𝔭 → 𝒳} {S : Matrix (𝔞 ⊕ 𝔭) (𝔞 ⊕ 𝔭) ℝ}
    (hS0 : ∀ a p, S (Sum.inl a) (Sum.inr p) = 0) (dW : 𝔭 → 𝒴) :
    ∑ i, ∑ p, S i (Sum.inr p) • (X i ⊗ₜ[ℝ] dW p) =
      ∑ q, X (Sum.inr q) ⊗ₜ[ℝ] ∑ p, S (Sum.inr q) (Sum.inr p) • dW p := by
  simp only [Fintype.sum_sum_type, hS0, zero_smul, Finset.sum_const_zero, zero_add,
    TensorProduct.tmul_sum, TensorProduct.tmul_smul]

private lemma sum_smul_sum_smul {n M : Type*} [Fintype n] [DecidableEq n] [AddCommGroup M]
    [Module ℝ M] {A B : Matrix n n ℝ} (h : A * B = 1) (φ : n → M) (q : n) :
    ∑ p, A q p • ∑ r, B p r • φ r = φ q := by
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  have h' : ∀ r, ∑ p, A q p * B p r = (1 : Matrix n n ℝ) q r := fun r => by
    rw [← h, Matrix.mul_apply]
  simp only [h', Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]

/-- arXiv 2503.10562, Section 2.3: `T_f M_{r,ω} = T_{V,ω} + T_{Z,ω}` for a block triangular
coefficient matrix (`S_{ap} = 0`, Eq. (16)–(17)) that is invertible, on two arbitrary inner product
spaces. `Z_p = X_p`, and all spaces are divided by `ω`. -/
theorem tangentSet_eq [DecidableEq 𝔞] [DecidableEq 𝔭] {U : 𝔞 → 𝒴} {W : 𝔭 → 𝒴} {X : 𝔞 ⊕ 𝔭 → 𝒳}
    {S : Matrix (𝔞 ⊕ 𝔭) (𝔞 ⊕ 𝔭) ℝ} (hS0 : ∀ a p, S (Sum.inl a) (Sum.inr p) = 0)
    (hdet : IsUnit S.det) :
    tangentSet U W X S = {w | ∃ w₁ ∈ tangentV U W, ∃ w₂ ∈ tangentZ U (fun p => X (Sum.inr p)),
      w = w₁ + w₂} := by
  ext w
  constructor
  · rintro ⟨dX, dS, dW, hdW, rfl⟩
    refine ⟨_, ⟨fun j => ∑ i, (S i j • dX i + dS i j • X i), ?_⟩, _,
      ⟨fun q => ∑ p, S (Sum.inr q) (Sum.inr p) • dW p, fun q a => ?_, sum_block hS0 dW⟩, rfl⟩
    · simp only [TensorProduct.sum_tmul]
      exact Finset.sum_comm
    · simp [inner_sum, real_inner_smul_right, hdW]
  · rintro ⟨_, ⟨ψ, rfl⟩, _, ⟨φ, hφ, rfl⟩, rfl⟩
    have hfb : S = Matrix.fromBlocks S.toBlocks₁₁ 0 S.toBlocks₂₁ S.toBlocks₂₂ := by
      conv_lhs => rw [← Matrix.fromBlocks_toBlocks S]
      congr 1
      ext a p
      exact hS0 a p
    have hdetD : IsUnit S.toBlocks₂₂.det := by
      have h := hdet
      rw [hfb, Matrix.det_fromBlocks_zero₁₂] at h
      exact isUnit_of_mul_isUnit_right h
    have hD : S.toBlocks₂₂ * S.toBlocks₂₂⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdetD
    have hSi : Sᵀ * (S⁻¹)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.transpose_one]
    refine ⟨fun i => ∑ j, S⁻¹ j i • ψ j, 0, fun p => ∑ q, S.toBlocks₂₂⁻¹ p q • φ q,
      fun p a => ?_, ?_⟩
    · simp [inner_sum, real_inner_smul_right, hφ]
    · rw [sum_block hS0]
      congr 1
      · simp only [Matrix.zero_apply, zero_smul, add_zero]
        have key : ∀ j, ∑ i, S i j • ∑ r, S⁻¹ r i • ψ r = ψ j := fun j =>
          sum_smul_sum_smul (A := Sᵀ) (B := (S⁻¹)ᵀ) hSi ψ j
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← TensorProduct.sum_tmul, key]
      · refine Finset.sum_congr rfl fun q _ => ?_
        congr 1
        exact (sum_smul_sum_smul hD φ q).symm

/-- arXiv 2503.10562, Section 2.3: the sum `T_{V,ω} + T_{Z,ω}` is not direct, its intersection is
`T_{Z,V,ω} = span Z ⊗ span W`. This is where the modified S-step lives. -/
theorem tangentV_inter_tangentZ {U : 𝔞 → 𝒴} {W : 𝔭 → 𝒴} {Z : 𝔭 → 𝒳}
    (hV : Orthonormal ℝ (Sum.elim U W)) (hZ : Orthonormal ℝ Z) :
    tangentV (𝒳 := 𝒳) U W ∩ tangentZ U Z = tangentZV W Z := by
  have hU := orth_left hV
  have hUW : ∀ a p, ⟪U a, W p⟫ = 0 := fun a p => by
    simpa using hV.2 (i := Sum.inl a) (j := Sum.inr p) (by simp)
  ext w
  constructor
  · rintro ⟨h1, h2⟩
    rw [mem_tangentV_iff hV] at h1
    rw [mem_tangentZ_iff hU hZ] at h2
    refine ⟨Matrix.of fun p q => ⟪w, Z p ⊗ₜ[ℝ] W q⟫, ?_⟩
    have := projL_Q hV Z w
    rw [h1, h2, rTensor_lTensor_basisProj] at this
    exact this
  · rintro ⟨c, rfl⟩
    refine ⟨⟨Sum.elim 0 fun q => ∑ p, c p q • Z p, ?_⟩,
      ⟨fun p => ∑ q, c p q • W q, fun p a => ?_, ?_⟩⟩
    · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
        TensorProduct.zero_tmul, Finset.sum_const_zero, zero_add, TensorProduct.sum_tmul,
        TensorProduct.smul_tmul']
      exact Finset.sum_comm.symm.symm
    · simp [inner_sum, real_inner_smul_right, hUW]
    · simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul]

/-- arXiv 2503.10562, Section 2.3: the tangent projector `L + Q - L Q`, with `Q` the right projector
on `[U, W]` and `L = P_Z (1 - C)`, is an orthogonal projector in the inner product of
`𝒳 ⊗ 𝒴`, i.e. `(f, g) ↦ (f, g / ω)_{xv}`. -/
theorem isOrthProj_tangentProj {U : 𝔞 → 𝒴} {W : 𝔭 → 𝒴} {Z : 𝔭 → 𝒳}
    (hV : Orthonormal ℝ (Sum.elim U W)) (hZ : Orthonormal ℝ Z) :
    IsOrthProj (LeanDLRA.tangent (projL U Z) ((basisProj (Sum.elim U W)).lTensor 𝒳)) :=
  (isOrthProj_projL (orth_left hV) hZ).tangent
    (isOrthProj_lTensor (isOrthProj_basisProj hV)) (projL_comm hV Z)

/-- arXiv 2503.10562, Section 2.3: the range of the tangent projector is `T_{V,ω} + T_{Z,ω}`, which
is `T_f M_{r,ω}` by `tangentSet_eq`. -/
theorem tangentProj_eq_iff {U : 𝔞 → 𝒴} {W : 𝔭 → 𝒴} {Z : 𝔭 → 𝒳}
    (hV : Orthonormal ℝ (Sum.elim U W)) (hZ : Orthonormal ℝ Z) (w : 𝒳 ⊗[ℝ] 𝒴) :
    (∃ w₁ ∈ tangentV U W, ∃ w₂ ∈ tangentZ U Z, w = w₁ + w₂) ↔
      LeanDLRA.tangent (projL U Z) ((basisProj (Sum.elim U W)).lTensor 𝒳) w = w := by
  have hU := orth_left hV
  have hQ := isOrthProj_lTensor (𝒳 := 𝒳) (isOrthProj_basisProj hV)
  have hL := isOrthProj_projL hU hZ
  constructor
  · rintro ⟨w₁, h1, w₂, h2, rfl⟩
    rw [mem_tangentV_iff hV] at h1
    rw [mem_tangentZ_iff hU hZ] at h2
    simp only [LeanDLRA.tangent_apply, map_add, h1, h2, projL_comm hV Z w₂]
    have : (basisProj (Sum.elim U W)).lTensor 𝒳 (projL U Z w₂) =
      (basisProj (Sum.elim U W)).lTensor 𝒳 w₂ := by rw [h2]
    abel
  · intro h
    refine ⟨_, (mem_tangentV_iff hV _).2 (hQ.idem w), _, (mem_tangentZ_iff hU hZ _).2
      (hL.idem (w - (basisProj (Sum.elim U W)).lTensor 𝒳 w)), ?_⟩
    rw [LeanDLRA.tangent_apply] at h
    rw [map_sub]
    nth_rewrite 1 [← h]
    abel

/-- arXiv 2503.10562, Section 2.3: the right projector splits as `Q = Q_U + Q_W`, and the sum of
the two is an orthogonal projector. -/
theorem velocityProj_split {U : 𝔞 → 𝒴} {W : 𝔭 → 𝒴} (hV : Orthonormal ℝ (Sum.elim U W)) :
    (∀ z : 𝒳 ⊗[ℝ] 𝒴, (basisProj (Sum.elim U W)).lTensor 𝒳 z =
      ((basisProj U).lTensor 𝒳 + (basisProj W).lTensor 𝒳) z) ∧
    IsOrthProj ((basisProj U).lTensor 𝒳 + (basisProj W).lTensor 𝒳 :
      (𝒳 ⊗[ℝ] 𝒴) →L[ℝ] (𝒳 ⊗[ℝ] 𝒴)) :=
  ⟨lTensor_basisProj_elim U W,
    (isOrthProj_lTensor (isOrthProj_basisProj (orth_left hV))).add_of_comp_eq_zero
      (isOrthProj_lTensor (isOrthProj_basisProj (orth_right hV))) (lTensor_orth hV)⟩

/-- arXiv 2503.10562, Section 2.3: the tangent space splits orthogonally. The tangent projector is
`Q + R` with `R = P_Z (1 - Q)` an orthogonal projector and `Q R = 0`. -/
theorem tangentProj_orthogonal {U : 𝔞 → 𝒴} {W : 𝔭 → 𝒴} {Z : 𝔭 → 𝒳}
    (hV : Orthonormal ℝ (Sum.elim U W)) (hZ : Orthonormal ℝ Z) :
    (∀ z, LeanDLRA.tangent (projL U Z) ((basisProj (Sum.elim U W)).lTensor 𝒳) z =
      (basisProj (Sum.elim U W)).lTensor 𝒳 z +
        (basisProj Z).rTensor 𝒴 (z - (basisProj (Sum.elim U W)).lTensor 𝒳 z)) ∧
    IsOrthProj ((basisProj Z).rTensor 𝒴 * (1 - (basisProj (Sum.elim U W)).lTensor 𝒳)) ∧
    (∀ z, (basisProj (Sum.elim U W)).lTensor 𝒳
      ((basisProj Z).rTensor 𝒴 (z - (basisProj (Sum.elim U W)).lTensor 𝒳 z)) = 0) := by
  have hQ := isOrthProj_lTensor (𝒳 := 𝒳) (isOrthProj_basisProj hV)
  refine ⟨fun z => ?_, ?_, fun z => ?_⟩
  · rw [LeanDLRA.tangent_apply, projL_apply, projL_apply, C_Q hV, map_sub, map_sub, map_sub]
    abel
  · exact (isOrthProj_rTensor (isOrthProj_basisProj hZ)).mul hQ.compl fun x => by
      simp only [sub_apply, one_apply_eq_self, map_sub, rTensor_lTensor_comm]
  · rw [← rTensor_lTensor_comm, map_sub, hQ.idem, sub_self, map_zero]

/-- arXiv 2503.10562, Section 2.3: the projected field splits into the modified steps,
`P_T F = Q F + P_Z (1 - C) F - P_Z Q_W F` (K-, L- and S-step), and neither the modified L-step nor
the modified S-step changes the moments `C`: only `Z ⊗ U^⊥`, respectively the block `S_{pq}`, moves.
This is the projector form of the paper's modified steps, not their matrix equations. -/
theorem modified_steps {U : 𝔞 → 𝒴} {W : 𝔭 → 𝒴} {Z : 𝔭 → 𝒳}
    (hV : Orthonormal ℝ (Sum.elim U W)) (F : 𝒳 ⊗[ℝ] 𝒴) :
    LeanDLRA.tangent (projL U Z) ((basisProj (Sum.elim U W)).lTensor 𝒳) F =
      (basisProj (Sum.elim U W)).lTensor 𝒳 F + projL U Z F -
        (basisProj Z).rTensor 𝒴 ((basisProj W).lTensor 𝒳 F) ∧
    (basisProj U).lTensor 𝒳 (projL U Z F) = 0 ∧
    (basisProj U).lTensor 𝒳 ((basisProj Z).rTensor 𝒴 ((basisProj W).lTensor 𝒳 F)) = 0 := by
  have hC := isOrthProj_lTensor (𝒳 := 𝒳) (isOrthProj_basisProj (orth_left hV))
  refine ⟨?_, ?_, ?_⟩
  · rw [LeanDLRA.tangent_apply, projL_Q hV]
    abel
  · rw [projL_apply, ← rTensor_lTensor_comm, map_sub, hC.idem, sub_self, map_zero]
  · rw [← rTensor_lTensor_comm, lTensor_orth hV, map_zero]

end TangentSplit

/-! ### The discrete phase space -/

/-- The discrete phase space of arXiv 2503.10562: meshes in `x` and `v`, the weight `ω`, the
velocity coordinates, and the spaces `𝒳 = 𝒱⁽ˣ⁾` with `(·,·)_x` and `𝒴 = 𝒱⁽ᵛ⁾` with `(·,·)_{v,ω}`.
A low-rank function is `f = ω Y` with `Y ∈ 𝒳 ⊗ 𝒴`, and `(f, g)_{xv} = ⟪Y, g⟫` for `g ∈ 𝒳 ⊗ 𝒴`. -/
structure PhaseSpace (ι 𝓣x 𝓕x Bx Ax 𝓣v 𝓕v Bv Av 𝒳 𝒴 : Type*) [Fintype 𝓣x] [Fintype 𝓕x]
    [CommRing Bx] [Algebra ℝ Bx] [CommRing Ax] [Algebra ℝ Ax] [Fintype 𝓣v] [Fintype 𝓕v]
    [CommRing Bv] [Algebra ℝ Bv] [CommRing Av] [Algebra ℝ Av]
    [NormedAddCommGroup 𝒳] [InnerProductSpace ℝ 𝒳] [NormedAddCommGroup 𝒴]
    [InnerProductSpace ℝ 𝒴] where
  /-- The spatial mesh. -/
  Cx : BrokenCalculus ι 𝓣x 𝓕x Bx Ax
  /-- The velocity mesh. -/
  Cv : BrokenCalculus ι 𝓣v 𝓕v Bv Av
  /-- The weight `ω`. -/
  ω : Bv
  /-- The velocity coordinates `v_s`. -/
  vel : ι → Bv
  /-- The space `𝒱ₕ,ₚ⁽ˣ⁾` with `(·,·)_x`. -/
  Xs : DGSpace Cx 1 𝒳
  /-- The space `𝒱ₕ,q⁽ᵛ⁾` with `(·,·)_{v,ω}`. -/
  Vs : DGSpace Cv ω 𝒴

namespace PhaseSpace

variable {ι 𝓣x 𝓕x Bx Ax 𝓣v 𝓕v Bv Av 𝒳 𝒴 : Type*} [Fintype ι] [Fintype 𝓣x] [Fintype 𝓕x]
  [CommRing Bx] [Algebra ℝ Bx] [CommRing Ax] [Algebra ℝ Ax] [Fintype 𝓣v] [Fintype 𝓕v]
  [CommRing Bv] [Algebra ℝ Bv] [CommRing Av] [Algebra ℝ Av]
  [NormedAddCommGroup 𝒳] [InnerProductSpace ℝ 𝒳] [FiniteDimensional ℝ 𝒳]
  [NormedAddCommGroup 𝒴] [InnerProductSpace ℝ 𝒴] [FiniteDimensional ℝ 𝒴]
  (D : PhaseSpace ι 𝓣x 𝓕x Bx Ax 𝓣v 𝓕v Bv Av 𝒳 𝒴) (Ef : ι → Bx)

/-- The discrete derivative `d̂_{x_s}` on `𝒱⁽ˣ⁾`, by Eq. (33). -/
noncomputable def dx (s : ι) : 𝒳 →L[ℝ] 𝒳 :=
  reprOp ((D.Cx.dFormL s).compl₁₂ D.Xs.emb D.Xs.emb)

/-- Multiplication by `E_s`, projected on `𝒱⁽ˣ⁾`. -/
noncomputable def mulE (s : ι) : 𝒳 →L[ℝ] 𝒳 :=
  reprOp ((D.Cx.mulForm (Ef s)).compl₁₂ D.Xs.emb D.Xs.emb)

/-- Multiplication by `v_s`, `ω`-projected on `𝒱⁽ᵛ⁾`. -/
noncomputable def mulV (s : ι) : 𝒴 →L[ℝ] 𝒴 :=
  reprOp ((D.Cv.mulForm (D.ω * D.vel s)).compl₁₂ D.Vs.emb D.Vs.emb)

/-- The operator `V ↦ ω⁻¹ d̂_{v_s}(ω V)`, `ω`-projected on `𝒱⁽ᵛ⁾`. -/
noncomputable def dv (s : ι) : 𝒴 →L[ℝ] 𝒴 :=
  reprOp ((D.Cv.dFormL s).compl₁₂ ((LinearMap.mulLeft ℝ D.ω) ∘ₗ D.Vs.emb) D.Vs.emb)

lemma inner_dx (s : ι) (a b : 𝒳) :
    ⟪D.dx s a, b⟫ = D.Cx.dForm s (D.Xs.emb a) (D.Xs.emb b) := by
  simp [dx, inner_reprOp]

lemma inner_mulE (s : ι) (a b : 𝒳) :
    ⟪D.mulE Ef s a, b⟫ = D.Cx.vol (Ef s * D.Xs.emb a * D.Xs.emb b) := by
  simp [mulE, inner_reprOp]

lemma inner_mulV (s : ι) (V W : 𝒴) :
    ⟪D.mulV s V, W⟫ = D.Cv.vol (D.ω * D.vel s * D.Vs.emb V * D.Vs.emb W) := by
  simp [mulV, inner_reprOp]

lemma inner_dv (s : ι) (V W : 𝒴) :
    ⟪D.dv s V, W⟫ = D.Cv.dForm s (D.ω * D.Vs.emb V) (D.Vs.emb W) := by
  simp [dv, inner_reprOp]

/-- The operator `F̂(f) = ∑_s (-v_s d̂_{x_s} f + E_s d̂_{v_s} f)` of arXiv 2503.10562, Lemma 3.2,
for `f = ω Y`, as an operator on `Y`: its Riesz representer in `𝒳 ⊗ 𝒴`, see `inner_Fhat_tmul`. -/
noncomputable def Fhat : (𝒳 ⊗[ℝ] 𝒴) →L[ℝ] (𝒳 ⊗[ℝ] 𝒴) :=
  ∑ s, (TensorProduct.mapL (D.mulE Ef s) (D.dv s) - TensorProduct.mapL (D.dx s) (D.mulV s))

/-- The pairing `(F̂(ω a ⊗ V), ψ ⊗ W)_{xv}` of arXiv 2503.10562, which defines `F̂`: it equals
`∑_s ((E_s a, ψ)_x (d̂_{v_s}(ω V), W)_v - (d̂_{x_s} a, ψ)_x (v_s ω V, W)_v)`. -/
theorem inner_Fhat_tmul (a ψ : 𝒳) (V W : 𝒴) :
    ⟪D.Fhat Ef (a ⊗ₜ[ℝ] V), ψ ⊗ₜ[ℝ] W⟫ =
      ∑ s, (D.Cx.vol (Ef s * D.Xs.emb a * D.Xs.emb ψ) *
            D.Cv.dForm s (D.ω * D.Vs.emb V) (D.Vs.emb W) -
          D.Cx.dForm s (D.Xs.emb a) (D.Xs.emb ψ) *
            D.Cv.vol (D.ω * D.vel s * D.Vs.emb V * D.Vs.emb W)) := by
  simp only [Fhat, sum_apply, sub_apply,
    TensorProduct.mapL_tmul, sum_inner, inner_sub_left, TensorProduct.inner_tmul, inner_dx,
    inner_mulE, inner_mulV, inner_dv]

/-! ### The scheme: K-step, S-step and conservative truncation -/

section Scheme

variable {I J K L 𝔞 R : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L] [Fintype 𝔞]
  [Fintype R]

/-- The function `Y = ∑ᵢⱼ Sᵢⱼ Xᵢ ⊗ Vⱼ`, i.e. `f = ω Y`. -/
noncomputable def lowRank (X : I → 𝒳) (S : Matrix I J ℝ) (V : J → 𝒴) : 𝒳 ⊗[ℝ] 𝒴 :=
  ∑ i, ∑ j, S i j • (X i ⊗ₜ[ℝ] V j)

/-- The coefficient functions `Kⱼ = ∑ᵢ Sᵢⱼ Xᵢ`. -/
noncomputable def coefK (X : I → 𝒳) (S : Matrix I J ℝ) (j : J) : 𝒳 := ∑ i, S i j • X i

lemma lowRank_eq_sum_coefK (X : I → 𝒳) (S : Matrix I J ℝ) (V : J → 𝒴) :
    lowRank X S V = ∑ j, coefK X S j ⊗ₜ[ℝ] V j := by
  simp only [lowRank, coefK, TensorProduct.sum_tmul, TensorProduct.smul_tmul']
  exact Finset.sum_comm

/-- `𝖠⁽ˣ,ˢ⁾ᵢⱼ = (v_s Vⱼ, Vᵢ)_{v,ω}`. -/
noncomputable def matA (V : J → 𝒴) (s : ι) (i j : J) : ℝ :=
  D.Cv.vol (D.ω * D.vel s * D.Vs.emb (V j) * D.Vs.emb (V i))

/-- `𝖡ₕ⁽ˣ,ˢ⁾ᵢⱼ = (d̂_{v_s}(ω Vⱼ), Vᵢ)_v`. -/
noncomputable def matB (V : J → 𝒴) (s : ι) (i j : J) : ℝ :=
  D.Cv.dForm s (D.ω * D.Vs.emb (V j)) (D.Vs.emb (V i))

/-- The `j`-th component of the central numerical flux `F*_e = A_e {K}_e`, with
`A_e = ∑_s n_s 𝖠⁽ˣ,ˢ⁾` (Eq. (31) with `α = 1`). -/
noncomputable def centralFlux (V : J → 𝒴) (Kc : J → 𝒳) (e : 𝓕x) (j : J) : Ax :=
  ∑ i, (∑ s, D.Cx.normal e s * D.matA V s j i) • D.Cx.avg e (D.Xs.emb (Kc i))

/-- The explicit Euler K-step, arXiv 2503.10562, Eq. (34), with the central flux, for every
component `j` and test function `ψ ∈ 𝒱⁽ˣ⁾`:
`(1/τ)(Kⁿ⁺¹ⱼ - Kⁿⱼ, ψ)_x + ∑_T ∑_s ∫_T (-(𝖠 Kⁿ)ⱼ ∂_s ψ - E_s (𝖡ₕ Kⁿ)ⱼ ψ)
  + ∑_e ∫_e F*_e [ψ]_e = 0`. -/
def IsKStep (τ : ℝ) (Kc Kn : J → 𝒳) (V : J → 𝒴) : Prop :=
  ∀ j ψ, (1 / τ) * ⟪Kn j - Kc j, ψ⟫ +
    ∑ T, ∑ s, D.Cx.elemInt T
      (-((∑ i, D.matA V s j i • D.Xs.emb (Kc i)) * D.Cx.pd s (D.Xs.emb ψ)) -
        Ef s * (∑ i, D.matB V s j i • D.Xs.emb (Kc i)) * D.Xs.emb ψ) +
    ∑ e, D.Cx.faceInt e (D.centralFlux V Kc e j * D.Cx.jump e (D.Xs.emb ψ)) = 0

/-- The explicit Euler S-step, arXiv 2503.10562, Eq. (36), with `S̃ⁿ = M Sⁿ Nᵀ`,
`M_{ki} = (X̃_k, X_i)_x` and `N_{lj} = (Ṽ_l, V_j)_{v,ω}`. `Xa` is `X̃`, `Va` is `Ṽ` and `Sa` is
`S̃ⁿ⁺¹`. -/
def IsSStep (τ : ℝ) (X : I → 𝒳) (S : Matrix I J ℝ) (V : J → 𝒴) (Xa : K → 𝒳) (Va : L → 𝒴)
    (Sa : Matrix K L ℝ) : Prop :=
  ∀ k l, Sa k l =
    (Matrix.of (fun k i => ⟪Xa k, X i⟫) * S * (Matrix.of (fun l j => ⟪Va l, V j⟫))ᵀ) k l -
      τ * ∑ i, ∑ j, ∑ s,
        (D.Cx.dForm s (D.Xs.emb (X i)) (D.Xs.emb (Xa k)) * S i j *
            D.Cv.vol (D.ω * D.Vs.emb (Va l) * (D.vel s * D.Vs.emb (V j))) +
          D.Cx.vol (D.Xs.emb (Xa k) * (-Ef s * D.Xs.emb (X i))) * S i j *
            D.Cv.dForm s (D.ω * D.Vs.emb (V j)) (D.Vs.emb (Va l)))

private lemma kStep_terms (V : J → 𝒴) (Kc : J → 𝒳) (j : J) (p : Bx) :
    ∑ T, ∑ s, D.Cx.elemInt T
      (-((∑ i, D.matA V s j i • D.Xs.emb (Kc i)) * D.Cx.pd s p) -
        Ef s * (∑ i, D.matB V s j i • D.Xs.emb (Kc i)) * p) +
    ∑ e, D.Cx.faceInt e (D.centralFlux V Kc e j * D.Cx.jump e p) =
    ∑ s, ∑ i, (D.matA V s j i * D.Cx.dForm s (D.Xs.emb (Kc i)) p -
      D.matB V s j i * D.Cx.vol (Ef s * D.Xs.emb (Kc i) * p)) := by
  have hflux : ∀ e, D.centralFlux V Kc e j =
      ∑ s, D.Cx.normal e s • ∑ i, D.matA V s j i • D.Cx.avg e (D.Xs.emb (Kc i)) := by
    intro e
    simp only [centralFlux, Finset.sum_smul, Finset.smul_sum, mul_smul]
    exact Finset.sum_comm
  simp only [hflux]
  rw [D.Cx.sum_elemInt_sum, D.Cx.sum_faceInt_normal, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  have h1 : (∑ i, D.matA V s j i • D.Xs.emb (Kc i)) * D.Cx.pd s p =
      ∑ i, D.matA V s j i • (D.Xs.emb (Kc i) * D.Cx.pd s p) := by
    simp only [Finset.sum_mul, smul_mul_assoc]
  have h2 : Ef s * (∑ i, D.matB V s j i • D.Xs.emb (Kc i)) * p =
      ∑ i, D.matB V s j i • (Ef s * D.Xs.emb (Kc i) * p) := by
    simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  have h3 : (fun e => (∑ i, D.matA V s j i • D.Cx.avg e (D.Xs.emb (Kc i))) * D.Cx.jump e p) =
      ∑ i, D.matA V s j i • (fun e => D.Cx.avg e (D.Xs.emb (Kc i)) * D.Cx.jump e p) := by
    funext e
    simp only [Finset.sum_mul, smul_mul_assoc, Finset.sum_apply, Pi.smul_apply]
  rw [h1, h2, h3, map_sub, map_neg, map_sum, map_sum, map_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, map_smul, D.Cx.lemma_3_1, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring

/-- `(F̂(f), ψ ⊗ Vⱼ)_{xv}` in terms of the matrices of the K-step. -/
private lemma inner_Fhat_kStep (V : J → 𝒴) (Kc : J → 𝒳) (j : J) (ψ : 𝒳) :
    ⟪D.Fhat Ef (∑ i, Kc i ⊗ₜ[ℝ] V i), ψ ⊗ₜ[ℝ] V j⟫ =
      - ∑ s, ∑ i, (D.matA V s j i * D.Cx.dForm s (D.Xs.emb (Kc i)) (D.Xs.emb ψ) -
        D.matB V s j i * D.Cx.vol (Ef s * D.Xs.emb (Kc i) * D.Xs.emb ψ)) := by
  rw [map_sum, sum_inner]
  simp only [inner_Fhat_tmul]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [matA, matB]
  ring

/-- arXiv 2503.10562, Lemma 3.2, K-step: with the central flux, Eq. (34) is equivalent to
`(Kⁿ⁺¹ⱼ, ψ)_x = (Kⁿⱼ, ψ)_x + τ (F̂(fⁿ), ψ ⊗ Vⱼ)_{xv}`. The paper states one direction. -/
theorem lemma_3_2_K {τ : ℝ} (hτ : τ ≠ 0) {V : J → 𝒴} {Kc Kn : J → 𝒳} :
    D.IsKStep Ef τ Kc Kn V ↔ ∀ j ψ,
      ⟪Kn j, ψ⟫ = ⟪Kc j, ψ⟫ + τ * ⟪D.Fhat Ef (∑ i, Kc i ⊗ₜ[ℝ] V i), ψ ⊗ₜ[ℝ] V j⟫ := by
  refine forall_congr' fun j => forall_congr' fun ψ => ?_
  rw [add_assoc, D.kStep_terms, inner_Fhat_kStep, inner_sub_left]
  constructor
  · intro h
    have h' : ⟪Kn j, ψ⟫ - ⟪Kc j, ψ⟫ = τ * (1 / τ * (⟪Kn j, ψ⟫ - ⟪Kc j, ψ⟫)) := by
      field_simp
    linear_combination h' + τ * h
  · intro h
    rw [h]
    field_simp
    ring

/-- arXiv 2503.10562, Lemma 3.2, S-step: Eq. (36) is equivalent to
`S̃ⁿ⁺¹ₖₗ = S̃ⁿₖₗ + τ (F̂(fⁿ), X̃ₖ ⊗ Ṽₗ)_{xv}`, where `S̃ⁿₖₗ = (fⁿ, X̃ₖ ⊗ Ṽₗ)_{xv}`. The paper
states one direction. -/
theorem lemma_3_2_S {τ : ℝ} {X : I → 𝒳} {S : Matrix I J ℝ} {V : J → 𝒴} {Xa : K → 𝒳}
    {Va : L → 𝒴} {Sa : Matrix K L ℝ} :
    D.IsSStep Ef τ X S V Xa Va Sa ↔ ∀ k l,
      Sa k l = ⟪lowRank X S V, Xa k ⊗ₜ[ℝ] Va l⟫ +
        τ * ⟪D.Fhat Ef (lowRank X S V), Xa k ⊗ₜ[ℝ] Va l⟫ := by
  refine forall_congr' fun k => forall_congr' fun l => ?_
  have h0 : (Matrix.of (fun k i => ⟪Xa k, X i⟫) * S * (Matrix.of (fun l j => ⟪Va l, V j⟫))ᵀ) k l =
      ⟪lowRank X S V, Xa k ⊗ₜ[ℝ] Va l⟫ := by
    simp only [lowRank, sum_inner, real_inner_smul_left, TensorProduct.inner_tmul, Matrix.mul_apply,
      Matrix.of_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_comm (X i), real_inner_comm (V j)]
    ring
  have h1 : ⟪D.Fhat Ef (lowRank X S V), Xa k ⊗ₜ[ℝ] Va l⟫ =
      - ∑ i, ∑ j, ∑ s,
        (D.Cx.dForm s (D.Xs.emb (X i)) (D.Xs.emb (Xa k)) * S i j *
            D.Cv.vol (D.ω * D.Vs.emb (Va l) * (D.vel s * D.Vs.emb (V j))) +
          D.Cx.vol (D.Xs.emb (Xa k) * (-Ef s * D.Xs.emb (X i))) * S i j *
            D.Cv.dForm s (D.ω * D.Vs.emb (V j)) (D.Vs.emb (Va l))) := by
    simp only [lowRank, map_sum, map_smul, sum_inner, real_inner_smul_left, inner_Fhat_tmul]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    have e1 : D.Xs.emb (Xa k) * (-Ef s * D.Xs.emb (X i)) =
        -(Ef s * D.Xs.emb (X i) * D.Xs.emb (Xa k)) := by ring
    have e2 : D.ω * D.Vs.emb (Va l) * (D.vel s * D.Vs.emb (V j)) =
        D.ω * D.vel s * D.Vs.emb (V j) * D.Vs.emb (Va l) := by ring
    rw [e1, e2, map_neg]
    ring
  rw [h0, h1]
  constructor <;> intro h <;> rw [h] <;> ring

private lemma kStep_sum {τ : ℝ} (hτ : τ ≠ 0) {X : I → 𝒳} {S : Matrix I J ℝ} {V : J → 𝒴}
    {Kn : J → 𝒳} (h : D.IsKStep Ef τ (coefK X S) Kn V) :
    ∑ j, Kn j ⊗ₜ[ℝ] V j = lowRank X S V +
      τ • (basisProj V).lTensor 𝒳 (D.Fhat Ef (lowRank X S V)) := by
  have hKn : ∀ j, Kn j = coefK X S j + τ • contrV (V j) (D.Fhat Ef (lowRank X S V)) := by
    intro j
    refine ext_inner_right ℝ fun ψ => ?_
    rw [(D.lemma_3_2_K Ef hτ).1 h j ψ, inner_add_left, real_inner_smul_left, inner_contrV,
      lowRank_eq_sum_coefK]
  rw [lTensor_basisProj_apply, lowRank_eq_sum_coefK, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hKn j, TensorProduct.add_tmul, TensorProduct.smul_tmul', ← lowRank_eq_sum_coefK]

/-- arXiv 2503.10562, Lemma 3.2, K-step in the full space: `Y_K = Q₀ (Y₀ + τ F̂(Y₀))`, where
`Y_K = ∑ⱼ Kⱼⁿ⁺¹ ⊗ Vⱼ` and `Q₀` is the orthogonal projector onto `𝒱⁽ˣ⁾ ⊗ span V`. -/
theorem lemma_3_2_K_proj {τ : ℝ} (hτ : τ ≠ 0) {X : I → 𝒳} {S : Matrix I J ℝ} {V : J → 𝒴}
    {Kn : J → 𝒳} (hV : Orthonormal ℝ V) (h : D.IsKStep Ef τ (coefK X S) Kn V) :
    ∑ j, Kn j ⊗ₜ[ℝ] V j = (basisProj V).lTensor 𝒳
      (lowRank X S V + τ • D.Fhat Ef (lowRank X S V)) := by
  have hfix : (basisProj V).lTensor 𝒳 (lowRank X S V) = lowRank X S V := by
    rw [lowRank_eq_sum_coefK, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.lTensor_tmul, basisProj_of_mem hV (Submodule.subset_span ⟨j, rfl⟩)]
  rw [D.kStep_sum Ef hτ h, map_add, map_smul, hfix]

/-- arXiv 2503.10562, Lemma 3.2, S-step in the full space: `Ŷ = P̂ Q̂ (Y₀ + τ F̂(Y₀))`, where
`Ŷ = ∑ₖₗ S̃ₖₗⁿ⁺¹ X̃ₖ ⊗ Ṽₗ` and `P̂ Q̂` is the orthogonal projector onto `span X̃ ⊗ span Ṽ`. -/
theorem lemma_3_2_S_proj {τ : ℝ} {X : I → 𝒳} {S : Matrix I J ℝ} {V : J → 𝒴} {Xa : K → 𝒳}
    {Va : L → 𝒴} {Sa : Matrix K L ℝ} (h : D.IsSStep Ef τ X S V Xa Va Sa) :
    lowRank Xa Sa Va = (basisProj Xa).rTensor 𝒴 ((basisProj Va).lTensor 𝒳
      (lowRank X S V + τ • D.Fhat Ef (lowRank X S V))) := by
  rw [rTensor_lTensor_basisProj, lowRank]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [inner_add_left, real_inner_smul_left, ← (D.lemma_3_2_S Ef).1 h k l]

/-- One step of the conservative scheme of arXiv 2503.10562, Section 3.2, from
`Y₀ = lowRank X S V` to `Y₁`: the K-step (34) gives `Kn`; `Xa` (`X̃`) is orthonormal and its span
contains `X` and `Kn`; `Va` (`Ṽ`) is orthonormal and its span contains `V`, which contains the
fixed functions `U`; the S-step (36) gives `Sa`, so `Ŷ = lowRank Xa Sa Va`; and the truncation (29)
keeps `∑_a K̃_a ⊗ U_a = C Ŷ` and replaces the rest by `∑_p ZK_p ⊗ ZW_p` with `ZW_p ⊥ U`. The paper's
L-step only serves to build `Ṽ`, and nothing here depends on it. -/
structure IsConsStep (τ : ℝ) (X : I → 𝒳) (S : Matrix I J ℝ) (V : J → 𝒴) (U : 𝔞 → 𝒴)
    (Kn : J → 𝒳) (Xa : K → 𝒳) (Va : L → 𝒴) (Sa : Matrix K L ℝ) (ZK : R → 𝒳) (ZW : R → 𝒴)
    (Y₁ : 𝒳 ⊗[ℝ] 𝒴) : Prop where
  /-- `V` is orthonormal in `(·,·)_{v,ω}`. -/
  orthV : Orthonormal ℝ V
  /-- The fixed functions are orthonormal. -/
  orthU : Orthonormal ℝ U
  /-- `U_a ∈ span V`. -/
  U_mem : ∀ a, U a ∈ Submodule.span ℝ (Set.range V)
  /-- The K-step (34). -/
  kstep : D.IsKStep Ef τ (coefK X S) Kn V
  /-- `X̃` is orthonormal. -/
  orthXa : Orthonormal ℝ Xa
  /-- `X ⊆ span X̃`. -/
  X_mem : ∀ i, X i ∈ Submodule.span ℝ (Set.range Xa)
  /-- `Kⁿ⁺¹ ⊆ span X̃`. -/
  K_mem : ∀ j, Kn j ∈ Submodule.span ℝ (Set.range Xa)
  /-- `Ṽ` is orthonormal. -/
  orthVa : Orthonormal ℝ Va
  /-- `V ⊆ span Ṽ`. -/
  V_mem : ∀ j, V j ∈ Submodule.span ℝ (Set.range Va)
  /-- The S-step (36). -/
  sstep : D.IsSStep Ef τ X S V Xa Va Sa
  /-- The truncated velocity functions stay orthogonal to `U`. -/
  ZW_orth : ∀ p a, ⟪U a, ZW p⟫ = 0
  /-- The conservative truncation (29). -/
  trunc : Y₁ = ∑ a, contrV (U a) (lowRank Xa Sa Va) ⊗ₜ[ℝ] U a + ∑ p, ZK p ⊗ₜ[ℝ] ZW p

variable {D Ef}
variable {τ : ℝ} {X : I → 𝒳} {S : Matrix I J ℝ} {V : J → 𝒴} {U : 𝔞 → 𝒴} {Kn : J → 𝒳}
  {Xa : K → 𝒳} {Va : L → 𝒴} {Sa : Matrix K L ℝ} {ZK : R → 𝒳} {ZW : R → 𝒴} {Y₁ : 𝒳 ⊗[ℝ] 𝒴}

/-- arXiv 2503.10562, Lemma 3.3 in the full space: one conservative step has exactly the moments of
the full explicit Euler step, `C Y₁ = C (Y₀ + τ F̂(Y₀))`. This is the library's
`consBug_euler_local_law` applied to the DG scheme. -/
theorem IsConsStep.moment_update (hτ : τ ≠ 0)
    (h : D.IsConsStep Ef τ X S V U Kn Xa Va Sa ZK ZW Y₁) :
    (basisProj U).lTensor 𝒳 Y₁ = (basisProj U).lTensor 𝒳
      (lowRank X S V + τ • D.Fhat Ef (lowRank X S V)) := by
  have hC := isOrthProj_lTensor (𝒳 := 𝒳) (isOrthProj_basisProj h.orthU)
  have hQ₀ := isOrthProj_lTensor (𝒳 := 𝒳) (isOrthProj_basisProj h.orthV)
  have hQa := isOrthProj_lTensor (𝒳 := 𝒳) (isOrthProj_basisProj h.orthVa)
  have hUV : Submodule.span ℝ (Set.range U) ≤ Submodule.span ℝ (Set.range V) :=
    Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact h.U_mem a)
  have hVVa : Submodule.span ℝ (Set.range V) ≤ Submodule.span ℝ (Set.range Va) :=
    Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact h.V_mem a)
  have hQ₀C := lTensor_fix (𝒳 := 𝒳) (Q := basisProj V) (P := basisProj U)
    (fun y => basisProj_of_mem h.orthV (hUV (basisProj_mem U y)))
  have hQaC := lTensor_fix (𝒳 := 𝒳) (Q := basisProj Va) (P := basisProj U)
    (fun y => basisProj_of_mem h.orthVa (hVVa (hUV (basisProj_mem U y))))
  have hPC := rTensor_lTensor_comm (𝒴 := 𝒴) (basisProj Xa) (basisProj U)
  have hfix : ∀ (x : 𝒳) (y : 𝒴), x ∈ Submodule.span ℝ (Set.range Xa) →
      (basisProj Xa).rTensor 𝒴 (x ⊗ₜ[ℝ] y) = x ⊗ₜ[ℝ] y := by
    intro x y hx
    rw [ContinuousLinearMap.rTensor_tmul, basisProj_of_mem h.orthXa hx]
  have hY₀ : (basisProj Xa).rTensor 𝒴 (lowRank X S V) = lowRank X S V := by
    simp only [lowRank, map_sum, map_smul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [hfix _ _ (h.X_mem i)]
  have hsum := D.kStep_sum Ef hτ h.kstep
  have hK : (basisProj Xa).rTensor 𝒴 (lowRank X S V +
      τ • (basisProj V).lTensor 𝒳 (D.Fhat Ef (lowRank X S V))) = lowRank X S V +
      τ • (basisProj V).lTensor 𝒳 (D.Fhat Ef (lowRank X S V)) := by
    rw [← hsum, map_sum]
    exact Finset.sum_congr rfl fun j _ => hfix _ _ (h.K_mem j)
  have hS : lowRank Xa Sa Va = (basisProj Xa).rTensor 𝒴 ((basisProj Va).lTensor 𝒳
      (eulerStep (D.Fhat Ef) τ (lowRank X S V))) := D.lemma_3_2_S_proj Ef h.sstep
  have hT : (basisProj U).lTensor 𝒳 (∑ p, ZK p ⊗ₜ[ℝ] ZW p) = 0 := by
    rw [map_sum]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [ContinuousLinearMap.lTensor_tmul, basisProj_apply]
    simp [h.ZW_orth p]
  have htrunc : Y₁ = consTrunc ((basisProj U).lTensor 𝒳) (fun _ => ∑ p, ZK p ⊗ₜ[ℝ] ZW p)
      (lowRank Xa Sa Va) := by
    rw [h.trunc, consTrunc, lTensor_basisProj_apply]
  have key := consBug_euler_local_law hC hQ₀ hQa hQ₀C hQaC hPC hY₀ hK
    (T := fun _ => ∑ p, ZK p ⊗ₜ[ℝ] ZW p) hT
  rw [← hS, ← htrunc] at key
  rw [key, map_add, map_smul]

/-- arXiv 2503.10562, Lemma 3.3: for `W ∈ span U`, the moment `φ_W = (f, W)_v` satisfies
`φ_W¹ = φ_W⁰ + τ (F̂(f⁰), W)_v` in `𝒱⁽ˣ⁾`, i.e. tested with every `ψ` (see `inner_contrV` and
`contrV_eq_moment`). The bases need not contain `∇X`. -/
theorem lemma_3_3 (hτ : τ ≠ 0) (h : D.IsConsStep Ef τ X S V U Kn Xa Va Sa ZK ZW Y₁) {W : 𝒴}
    (hW : W ∈ Submodule.span ℝ (Set.range U)) :
    contrV W Y₁ = contrV W (lowRank X S V) + τ • contrV W (D.Fhat Ef (lowRank X S V)) := by
  have hC := isOrthProj_basisProj h.orthU
  have hfix := basisProj_of_mem h.orthU hW
  rw [← contrV_lTensor hC hfix Y₁, h.moment_update hτ, contrV_lTensor hC hfix, map_add, map_smul]

variable (D)

/-- `V ↦ (ω V, W)_v`. -/
noncomputable def momF (W : Bv) : 𝒴 →ₗ[ℝ] ℝ := ((D.Cv.mulForm D.ω).flip W) ∘ₗ D.Vs.emb

/-- `V ↦ (d̂_{v_s}(ω V), W)_v`. -/
noncomputable def dvMomF (s : ι) (W : Bv) : 𝒴 →ₗ[ℝ] ℝ :=
  ((D.Cv.dFormL s).flip W) ∘ₗ (LinearMap.mulLeft ℝ D.ω) ∘ₗ D.Vs.emb

/-- `V ↦ ∑_e ∫_e n_s {ω V} [v_t]`. -/
noncomputable def bdryF (s t : ι) : 𝒴 →ₗ[ℝ] ℝ :=
  (D.Cv.skel s) ∘ₗ
    (LinearMap.pi fun e => (LinearMap.mulRight ℝ (D.Cv.jump e (D.vel t))) ∘ₗ D.Cv.avg e) ∘ₗ
    (LinearMap.mulLeft ℝ D.ω) ∘ₗ D.Vs.emb

/-- The velocity moment `(f, W)_v` of `f = ω Y`, an element of `𝒱⁽ˣ⁾`. -/
noncomputable def moment (W : Bv) : (𝒳 ⊗[ℝ] 𝒴) →ₗ[ℝ] 𝒳 := contr (D.momF W)

/-- The density `ρ = (f, 1)_v`. -/
noncomputable def rho : (𝒳 ⊗[ℝ] 𝒴) →ₗ[ℝ] 𝒳 := D.moment 1

/-- The current `j_t = (f, v_t)_v`. -/
noncomputable def cur (t : ι) : (𝒳 ⊗[ℝ] 𝒴) →ₗ[ℝ] 𝒳 := D.moment (D.vel t)

/-- The stress `σ_{t s} = (f, v_t v_s)_v`. -/
noncomputable def stress (t s : ι) : (𝒳 ⊗[ℝ] 𝒴) →ₗ[ℝ] 𝒳 := D.moment (D.vel t * D.vel s)

/-- The boundary moment `β_{st} = ∑_e ∫_e n_s {f}_e [v_t]_e dS`, an element of `𝒱⁽ˣ⁾`. It vanishes
under the support assumption of arXiv 2503.10562, Section 3.1, which the proof of Theorem 3.5 uses
without naming this term. -/
noncomputable def bdryMoment (s t : ι) : (𝒳 ⊗[ℝ] 𝒴) →ₗ[ℝ] 𝒳 := contr (D.bdryF s t)

lemma momF_apply (W : Bv) (V : 𝒴) : D.momF W V = D.Cv.vol (D.ω * D.Vs.emb V * W) := rfl

lemma dvMomF_apply (s : ι) (W : Bv) (V : 𝒴) :
    D.dvMomF s W V = D.Cv.dForm s (D.ω * D.Vs.emb V) W := rfl

lemma bdryF_apply (s t : ι) (V : 𝒴) : D.bdryF s t V =
    D.Cv.skel s (fun e => D.Cv.avg e (D.ω * D.Vs.emb V) * D.Cv.jump e (D.vel t)) := rfl

lemma contrV_eq_moment (W : 𝒴) (z : 𝒳 ⊗[ℝ] 𝒴) : contrV W z = D.moment (D.Vs.emb W) z := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [moment, contr_tmul, innerₗ_apply_apply, momF_apply]
    rw [D.Vs.inner_eq, mul_right_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The flux moment of arXiv 2503.10562: for `W ∈ 𝒱⁽ᵛ⁾`,
`(F̂(f), W)_v = ∑_s (E_s (d̂_{v_s} f, W)_v - d̂_{x_s} (f, v_s W)_v)`, projected on `𝒱⁽ˣ⁾`. -/
theorem contrV_Fhat (W : 𝒴) (z : 𝒳 ⊗[ℝ] 𝒴) :
    contrV W (D.Fhat Ef z) =
      ∑ s, (D.mulE Ef s (contr (D.dvMomF s (D.Vs.emb W)) z) -
        D.dx s (D.moment (D.vel s * D.Vs.emb W) z)) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    rw [Fhat, sum_apply, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [sub_apply, TensorProduct.mapL_tmul, map_sub, contr_tmul, innerₗ_apply_apply,
      moment, map_smul, dvMomF_apply, momF_apply]
    rw [real_inner_comm, inner_dv, real_inner_comm, inner_mulV]
    congr 3
    ring
  | add x y hx hy =>
    simp only [map_add, hx, hy, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    abel

lemma dvMomF_one (s : ι) : D.dvMomF s 1 = 0 := by
  ext V
  have h : (fun e => D.Cv.jump e (D.ω * D.Vs.emb V) * D.Cv.avg e 1) =
      fun e => D.Cv.jump e (D.ω * D.Vs.emb V) := by
    funext e; simp
  rw [dvMomF_apply, BrokenCalculus.dForm, h, mul_one, D.Cv.vol_pd]
  simp

lemma dvMomF_vel [DecidableEq ι] (hvel : ∀ s t, D.Cv.pd s (D.vel t) = if s = t then 1 else 0)
    (s t : ι) (V : 𝒴) :
    D.dvMomF s (D.vel t) V = - (if s = t then D.momF 1 V else 0) + D.bdryF s t V := by
  rw [dvMomF_apply, D.Cv.lemma_3_1, hvel, bdryF_apply, momF_apply]
  split_ifs <;> simp

/-- The test-function form of `contr (dvMomF ..)` for the velocity coordinates. -/
lemma contr_dvMomF_vel [DecidableEq ι]
    (hvel : ∀ s t, D.Cv.pd s (D.vel t) = if s = t then 1 else 0) (s t : ι) (z : 𝒳 ⊗[ℝ] 𝒴) :
    contr (D.dvMomF s (D.vel t)) z =
      - (if s = t then D.rho z else 0) + D.bdryMoment s t z := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [contr_tmul, D.dvMomF_vel hvel, add_smul, neg_smul, rho, moment, bdryMoment]
    split_ifs <;> simp
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    split_ifs
    · abel
    · simp only [neg_zero, zero_add]

/-- arXiv 2503.10562, Theorem 3.4 (`m ≥ 1`, i.e. `1 ∈ span U`): the discrete continuity equation
`(1/τ)(ρ¹ - ρ⁰, ψ)_x - ∑_T ∫_T j · ∇ψ + ∑_e ∫_e (n · {j}_e) [ψ]_e dS = 0` for all `ψ ∈ 𝒱⁽ˣ⁾`, where
`ρ = (f, 1)_v` and `j_s = (f, v_s)_v`, for every field `E`. It holds exactly on a periodic velocity
mesh, because `1` has no jumps. -/
theorem theorem_3_4 (hτ : τ ≠ 0) (h : D.IsConsStep Ef τ X S V U Kn Xa Va Sa ZK ZW Y₁) {one : 𝒴}
    (hone : D.Vs.emb one = 1) (hmem : one ∈ Submodule.span ℝ (Set.range U)) (ψ : 𝒳) :
    (1 / τ) * ⟪D.rho Y₁ - D.rho (lowRank X S V), ψ⟫ -
      ∑ T, D.Cx.elemInt T
        (∑ s, D.Xs.emb (D.cur s (lowRank X S V)) * D.Cx.pd s (D.Xs.emb ψ)) +
      ∑ e, D.Cx.faceInt e
        ((∑ s, D.Cx.normal e s • D.Cx.avg e (D.Xs.emb (D.cur s (lowRank X S V)))) *
          D.Cx.jump e (D.Xs.emb ψ)) = 0 := by
  set Y₀ := lowRank X S V with hY₀
  have hρ : ∀ z, D.rho z = contrV one z := fun z => by
    rw [D.contrV_eq_moment, hone, rho]
  have h3 := lemma_3_3 hτ h hmem
  have h4 : contrV one (D.Fhat Ef Y₀) = - ∑ s, D.dx s (D.cur s Y₀) := by
    rw [D.contrV_Fhat, hone, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    have : contr (D.dvMomF s (1 : Bv)) Y₀ = 0 := by
      rw [D.dvMomF_one]
      simp [contr]
    rw [this, map_zero, zero_sub, mul_one, cur]
  have h5 : D.rho Y₁ - D.rho Y₀ = τ • contrV one (D.Fhat Ef Y₀) := by
    rw [hρ, hρ, h3, add_sub_cancel_left]
  have h6 : ⟪D.rho Y₁ - D.rho Y₀, ψ⟫ = - τ * ∑ s,
      (- D.Cx.vol (D.Xs.emb (D.cur s Y₀) * D.Cx.pd s (D.Xs.emb ψ)) + D.Cx.skel s
        (fun e => D.Cx.avg e (D.Xs.emb (D.cur s Y₀)) * D.Cx.jump e (D.Xs.emb ψ))) := by
    rw [h5, h4, real_inner_smul_left, inner_neg_left, sum_inner]
    simp only [inner_dx, BrokenCalculus.lemma_3_1]
    ring
  rw [h6, D.Cx.sum_elemInt, map_sum, D.Cx.sum_faceInt_normal, Finset.sum_add_distrib,
    Finset.sum_neg_distrib]
  field_simp
  ring

/-- arXiv 2503.10562, Theorem 3.4, mass conservation: if `1 ∈ 𝒱⁽ˣ⁾`, then `∫ ρ¹ = ∫ ρ⁰`. -/
theorem mass_conservation (hτ : τ ≠ 0) (h : D.IsConsStep Ef τ X S V U Kn Xa Va Sa ZK ZW Y₁)
    {one : 𝒴} (hone : D.Vs.emb one = 1) (hmem : one ∈ Submodule.span ℝ (Set.range U))
    {oneX : 𝒳} (honeX : D.Xs.emb oneX = 1) :
    D.Cx.vol (D.Xs.emb (D.rho Y₁)) = D.Cx.vol (D.Xs.emb (D.rho (lowRank X S V))) := by
  have key := D.theorem_3_4 hτ h hone hmem oneX
  simp only [honeX, Derivation.map_one_eq_zero, BrokenCalculus.jump_one, mul_zero, map_zero,
    Finset.sum_const_zero, sub_zero, add_zero] at key
  have h2 : ⟪D.rho Y₁ - D.rho (lowRank X S V), oneX⟫ = 0 := by
    have hτ' : 1 / τ ≠ 0 := one_div_ne_zero hτ
    exact (mul_eq_zero.1 key).resolve_left hτ'
  rw [D.Xs.inner_eq, honeX, map_sub] at h2
  simpa [sub_eq_zero] using h2

/-- arXiv 2503.10562, Theorem 3.5 without the support assumption (`v_t ∈ span U`): the exact
discrete momentum equation on a periodic velocity mesh, tested with `ψ ∈ 𝒱⁽ˣ⁾`, where
`σ_{ts} = (f, v_t v_s)_v`:
`(1/τ)(j_t¹ - j_t⁰, ψ)_x + ∑_T ∫_T (-σ_t · ∇ψ + E_t ρ ψ) + ∑_e ∫_e (n · {σ_t}_e) [ψ]_e dS
  = ∑_s (E_s β_{st}, ψ)_x`.
The paper has `0` on the right: `β_{st}`, the term with `[v_t]_e`, vanishes under its support
assumption of Section 3.1 (`theorem_3_5`). Without that assumption the right side does not vanish in
general (`theorem_3_5_false_on_periodic_velocity_mesh`). -/
theorem theorem_3_5_defect [DecidableEq ι] (hτ : τ ≠ 0)
    (h : D.IsConsStep Ef τ X S V U Kn Xa Va Sa ZK ZW Y₁)
    (hvel : ∀ s t, D.Cv.pd s (D.vel t) = if s = t then 1 else 0) {t : ι} {velh : 𝒴}
    (hvelh : D.Vs.emb velh = D.vel t) (hmem : velh ∈ Submodule.span ℝ (Set.range U)) (ψ : 𝒳) :
    (1 / τ) * ⟪D.cur t Y₁ - D.cur t (lowRank X S V), ψ⟫ +
      ∑ T, D.Cx.elemInt T
        (-(∑ s, D.Xs.emb (D.stress t s (lowRank X S V)) * D.Cx.pd s (D.Xs.emb ψ)) +
          Ef t * D.Xs.emb (D.rho (lowRank X S V)) * D.Xs.emb ψ) +
      ∑ e, D.Cx.faceInt e
        ((∑ s, D.Cx.normal e s • D.Cx.avg e (D.Xs.emb (D.stress t s (lowRank X S V)))) *
          D.Cx.jump e (D.Xs.emb ψ)) =
    ∑ s, D.Cx.vol (Ef s * D.Xs.emb (D.bdryMoment s t (lowRank X S V)) * D.Xs.emb ψ) := by
  set Y₀ := lowRank X S V with hY₀
  have hc : ∀ z, D.cur t z = contrV velh z := fun z => by
    rw [D.contrV_eq_moment, hvelh, cur]
  have h3 := lemma_3_3 hτ h hmem
  have h5 : D.cur t Y₁ - D.cur t Y₀ = τ • contrV velh (D.Fhat Ef Y₀) := by
    rw [hc, hc, h3, add_sub_cancel_left]
  have hs : ∀ s, ⟪D.mulE Ef s (contr (D.dvMomF s (D.vel t)) Y₀) -
        D.dx s (D.moment (D.vel s * D.vel t) Y₀), ψ⟫ =
      - (if s = t then D.Cx.vol (Ef t * D.Xs.emb (D.rho Y₀) * D.Xs.emb ψ) else 0) +
        D.Cx.vol (Ef s * D.Xs.emb (D.bdryMoment s t Y₀) * D.Xs.emb ψ) +
        D.Cx.vol (D.Xs.emb (D.stress t s Y₀) * D.Cx.pd s (D.Xs.emb ψ)) -
        D.Cx.skel s (fun e => D.Cx.avg e (D.Xs.emb (D.stress t s Y₀)) *
          D.Cx.jump e (D.Xs.emb ψ)) := by
    intro s
    rw [inner_sub_left, inner_mulE, inner_dx, BrokenCalculus.lemma_3_1, D.contr_dvMomF_vel hvel,
      mul_comm (D.vel s) (D.vel t), ← stress, map_add, map_neg, mul_add, add_mul, map_add]
    by_cases hst : s = t
    · subst hst
      simp only [↓reduceIte, mul_neg, neg_mul, map_neg]
      ring
    · simp only [hst, ↓reduceIte, map_zero, mul_zero, zero_mul, neg_zero]
      ring
  have h6 : ⟪contrV velh (D.Fhat Ef Y₀), ψ⟫ =
      ∑ s, D.Cx.vol (Ef s * D.Xs.emb (D.bdryMoment s t Y₀) * D.Xs.emb ψ) +
      ∑ s, D.Cx.vol (D.Xs.emb (D.stress t s Y₀) * D.Cx.pd s (D.Xs.emb ψ)) -
      ∑ s, D.Cx.skel s
        (fun e => D.Cx.avg e (D.Xs.emb (D.stress t s Y₀)) * D.Cx.jump e (D.Xs.emb ψ)) -
      D.Cx.vol (Ef t * D.Xs.emb (D.rho Y₀) * D.Xs.emb ψ) := by
    rw [D.contrV_Fhat, hvelh, sum_inner]
    simp only [hs, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    ring
  rw [h5, real_inner_smul_left, h6, D.Cx.sum_elemInt, map_add, map_neg, map_sum,
    D.Cx.sum_faceInt_normal]
  field_simp
  ring

/-- arXiv 2503.10562, Theorem 3.5, Eq. (45) (`v_t ∈ span U`, i.e. `m ≥ 1 + d`). The hypothesis
`hsupp` that the boundary moments of `f` vanish is the paper's standing assumption of Section 3.1
that the computational domain contains the support of the solution (see `bdryMoment_eq_zero`). It
cannot be dropped, by `theorem_3_5_false_on_periodic_velocity_mesh`, and it can hold, by
`exists_momentum_instance`. -/
theorem theorem_3_5 [DecidableEq ι] (hτ : τ ≠ 0)
    (h : D.IsConsStep Ef τ X S V U Kn Xa Va Sa ZK ZW Y₁)
    (hvel : ∀ s t, D.Cv.pd s (D.vel t) = if s = t then 1 else 0) {t : ι} {velh : 𝒴}
    (hvelh : D.Vs.emb velh = D.vel t) (hmem : velh ∈ Submodule.span ℝ (Set.range U))
    (hsupp : ∀ s, D.bdryMoment s t (lowRank X S V) = 0) (ψ : 𝒳) :
    (1 / τ) * ⟪D.cur t Y₁ - D.cur t (lowRank X S V), ψ⟫ +
      ∑ T, D.Cx.elemInt T
        (-(∑ s, D.Xs.emb (D.stress t s (lowRank X S V)) * D.Cx.pd s (D.Xs.emb ψ)) +
          Ef t * D.Xs.emb (D.rho (lowRank X S V)) * D.Xs.emb ψ) +
      ∑ e, D.Cx.faceInt e
        ((∑ s, D.Cx.normal e s • D.Cx.avg e (D.Xs.emb (D.stress t s (lowRank X S V)))) *
          D.Cx.jump e (D.Xs.emb ψ)) = 0 := by
  rw [D.theorem_3_5_defect hτ h hvel hvelh hmem ψ]
  simp [hsupp]

/-- The support hypothesis of `theorem_3_5` for a state `∑ₖ ξₖ ⊗ Wₖ`: it holds if each `ω Wₖ` has
zero average on every face across which `v_t` jumps, i.e. if the velocity support lies inside the
computational domain. -/
lemma bdryMoment_eq_zero {M : Type*} [Fintype M] {t : ι} (ξ : M → 𝒳) (W : M → 𝒴)
    (h : ∀ k e, D.Cv.avg e (D.ω * D.Vs.emb (W k)) * D.Cv.jump e (D.vel t) = 0) (s : ι) :
    D.bdryMoment s t (∑ k, ξ k ⊗ₜ[ℝ] W k) = 0 := by
  rw [map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [bdryMoment, contr_tmul, bdryF_apply]
  simp only [h]
  rw [show (fun _ : 𝓕v => (0 : Av)) = 0 from rfl, map_zero, zero_smul]

/-- arXiv 2503.10562, Theorem 3.5, momentum conservation: under `hsupp`, with `1 ∈ 𝒱⁽ˣ⁾` and the
exact Poisson field `E` of `ρ⁰` (`hP`), `∫ j_t¹ = ∫ j_t⁰`. The paper quotes `∫ E = 0` and the
divergence form of `E (1 - ρ)`; here `IsPoissonField.vol_field_mul_rho`. -/
theorem momentum_conservation [DecidableEq ι] (hτ : τ ≠ 0)
    (h : D.IsConsStep Ef τ X S V U Kn Xa Va Sa ZK ZW Y₁)
    (hvel : ∀ s t, D.Cv.pd s (D.vel t) = if s = t then 1 else 0) {t : ι} {velh : 𝒴}
    (hvelh : D.Vs.emb velh = D.vel t) (hmem : velh ∈ Submodule.span ℝ (Set.range U))
    (hsupp : ∀ s, D.bdryMoment s t (lowRank X S V) = 0) {oneX : 𝒳} (honeX : D.Xs.emb oneX = 1)
    {Φ : Bx} (hP : D.Cx.IsPoissonField Ef (D.Xs.emb (D.rho (lowRank X S V))) Φ) :
    D.Cx.vol (D.Xs.emb (D.cur t Y₁)) = D.Cx.vol (D.Xs.emb (D.cur t (lowRank X S V))) := by
  have key := D.theorem_3_5 hτ h hvel hvelh hmem hsupp oneX
  simp only [honeX, Derivation.map_one_eq_zero, BrokenCalculus.jump_one, mul_zero, map_zero,
    Finset.sum_const_zero, add_zero, neg_zero, zero_add, mul_one, D.Cx.sum_elemInt,
    hP.vol_field_mul_rho] at key
  have h2 : ⟪D.cur t Y₁ - D.cur t (lowRank X S V), oneX⟫ = 0 :=
    (mul_eq_zero.1 key).resolve_left (one_div_ne_zero hτ)
  rw [D.Xs.inner_eq, honeX, map_sub] at h2
  simpa [sub_eq_zero] using h2

/-- Non-vacuity of `IsConsStep` (arXiv 2503.10562, Section 3.2): every low-rank state `(X, S, V)`
with `V` orthonormal and `span U ⊆ span V` has a step, here with `Ṽ = V` and no truncation. -/
theorem exists_isConsStep (hτ : τ ≠ 0) (X : I → 𝒳) (S : Matrix I J ℝ) (hV : Orthonormal ℝ V)
    (hU : Orthonormal ℝ U) (hUV : ∀ a, U a ∈ Submodule.span ℝ (Set.range V)) :
    ∃ (Kn : J → 𝒳) (n : ℕ) (Xa : Fin n → 𝒳) (Sa : Matrix (Fin n) J ℝ) (Y₁ : 𝒳 ⊗[ℝ] 𝒴),
      D.IsConsStep Ef τ X S V U Kn Xa V Sa (fun _ : Empty => 0) (fun _ : Empty => 0) Y₁ := by
  set Y₀ := lowRank X S V with hY₀
  let Kn : J → 𝒳 := fun j => coefK X S j + τ • contrV (V j) (D.Fhat Ef Y₀)
  let W : Submodule ℝ 𝒳 := Submodule.span ℝ (Set.range X ∪ Set.range Kn)
  let b := stdOrthonormalBasis ℝ W
  let Xa : Fin (Module.finrank ℝ W) → 𝒳 := fun k => (b k : 𝒳)
  have hXa : Orthonormal ℝ Xa := b.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  have hmem : ∀ x ∈ W, x ∈ Submodule.span ℝ (Set.range Xa) := by
    intro x hx
    have h := b.sum_repr' ⟨x, hx⟩
    have h' : x = ∑ k, ⟪b k, (⟨x, hx⟩ : W)⟫ • Xa k := by
      have := congrArg (Subtype.val) h
      simpa [Xa] using this.symm
    rw [h']
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  refine ⟨Kn, _, Xa, Matrix.of fun k l =>
    ⟪lowRank X S V, Xa k ⊗ₜ[ℝ] V l⟫ + τ * ⟪D.Fhat Ef (lowRank X S V), Xa k ⊗ₜ[ℝ] V l⟫, _,
    { orthV := hV
      orthU := hU
      U_mem := hUV
      kstep := (D.lemma_3_2_K Ef hτ).2 fun j ψ => ?_
      orthXa := hXa
      X_mem := fun i => hmem _ (Submodule.subset_span (Or.inl ⟨i, rfl⟩))
      K_mem := fun j => hmem _ (Submodule.subset_span (Or.inr ⟨j, rfl⟩))
      orthVa := hV
      V_mem := fun j => Submodule.subset_span ⟨j, rfl⟩
      sstep := (D.lemma_3_2_S Ef).2 fun k l => rfl
      ZW_orth := fun p => p.elim
      trunc := rfl }⟩
  simp only [Kn]
  rw [inner_add_left, real_inner_smul_left, inner_contrV, ← lowRank_eq_sum_coefK]

end Scheme

end PhaseSpace

/-! ### The concrete one-dimensional periodic mesh -/

section OneD

open scoped Polynomial

open scoped ContDiff in
/-- The algebra of smooth functions `ℝ → ℝ`. -/
def smoothFn : Subalgebra ℝ (ℝ → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f}
  mul_mem' {f g} hf hg := show ContDiff ℝ ∞ (f * g) from ContDiff.mul hf hg
  add_mem' {f g} hf hg := show ContDiff ℝ ∞ (f + g) from ContDiff.add hf hg
  algebraMap_mem' r := show ContDiff ℝ ∞ (fun _ : ℝ => r) from contDiff_const

open scoped ContDiff in
lemma smoothFn_contDiff (f : smoothFn) : ContDiff ℝ ∞ f.1 := f.2

lemma smoothFn_diff (f : smoothFn) (x : ℝ) : DifferentiableAt ℝ f.1 x :=
  (smoothFn_contDiff f).differentiable (by simp) x

lemma smoothFn_cont (f : smoothFn) : Continuous f.1 := (smoothFn_contDiff f).continuous

/-- `d/dx` on smooth functions. -/
noncomputable def derivS : Derivation ℝ smoothFn smoothFn :=
  Derivation.mk'
    { toFun := fun f => ⟨deriv f.1, (contDiff_infty_iff_deriv.1 (smoothFn_contDiff f)).2⟩
      map_add' := fun f g => Subtype.ext (funext fun x =>
        deriv_add (smoothFn_diff f x) (smoothFn_diff g x))
      map_smul' := fun c f => Subtype.ext (funext fun x =>
        deriv_const_smul c (smoothFn_diff f x)) }
    (fun f g => Subtype.ext (funext fun x => by
      have := deriv_mul (smoothFn_diff f x) (smoothFn_diff g x)
      change deriv (f.1 * g.1) x = f.1 x * deriv g.1 x + g.1 x * deriv f.1 x
      rw [this]
      ring))

/-- Broken smooth functions on `M + 1` elements: one smooth function for each element. -/
abbrev Broken (M : ℕ) : Type := Fin (M + 1) → smoothFn

variable {M : ℕ}

/-- The elementwise derivative. -/
noncomputable def pdB (M : ℕ) : Derivation ℝ (Broken M) (Broken M) :=
  Derivation.mk'
    { toFun := fun u i => derivS (u i)
      map_add' := fun u v => funext fun i => map_add derivS (u i) (v i)
      map_smul' := fun c u => funext fun i => derivS.map_smul c (u i) }
    (fun u v => funext fun i => Derivation.leibniz derivS (u i) (v i))

lemma pdB_apply (u : Broken M) (i : Fin (M + 1)) (x : ℝ) : (pdB M u i).1 x = deriv (u i).1 x := rfl

/-- Evaluation of element `i` at `x`. -/
noncomputable def evalAt (i : Fin (M + 1)) (x : ℝ) : Broken M →ₐ[ℝ] ℝ :=
  (Pi.evalAlgHom ℝ (fun _ : ℝ => ℝ) x).comp
    (smoothFn.val.comp (Pi.evalAlgHom ℝ (fun _ : Fin (M + 1) => smoothFn) i))

@[simp] lemma evalAt_apply (i : Fin (M + 1)) (x : ℝ) (u : Broken M) :
    evalAt i x u = (u i).1 x := rfl

/-- A periodic mesh of an interval with `M + 1` elements `[node i, node (i + 1)]`. The last element
is followed by the first one, across the wrap-around face. -/
structure Mesh1D (M : ℕ) where
  /-- The nodes. -/
  node : Fin (M + 2) → ℝ
  mono : StrictMono node

/-- The broken calculus of a periodic mesh of an interval, the instance of `BrokenCalculus` for
`d = 1`. Each face `e` is the right end of element `e`, its right neighbour is the next element
cyclically, and `gauss_green` is the fundamental theorem of calculus. -/
noncomputable def periodicCalculus (m : Mesh1D M) :
    BrokenCalculus Unit (Fin (M + 1)) (Fin (M + 1)) (Broken M) ℝ where
  elemInt T :=
    { toFun := fun u => ∫ x in m.node T.castSucc..m.node T.succ, (u T).1 x
      map_add' := fun u v => intervalIntegral.integral_add
        ((smoothFn_cont _).intervalIntegrable _ _) ((smoothFn_cont _).intervalIntegrable _ _)
      map_smul' := fun c u => intervalIntegral.integral_smul c _ }
  faceInt _ := LinearMap.id
  normal _ _ := 1
  traceMinus e := evalAt e (m.node e.succ)
  tracePlus e := evalAt (finRotate (M + 1) e) (m.node (finRotate (M + 1) e).castSucc)
  pd _ := pdB M
  pd_comm _ _ _ := rfl
  gauss_green _ u := by
    have h : ∀ T : Fin (M + 1), ∫ x in m.node T.castSucc..m.node T.succ, (pdB M u T).1 x =
        (u T).1 (m.node T.succ) - (u T).1 (m.node T.castSucc) := fun T =>
      intervalIntegral.integral_deriv_eq_sub (fun x _ => smoothFn_diff (u T) x)
        ((smoothFn_cont (pdB M u T)).intervalIntegrable _ _)
    have hrot := Equiv.sum_comp (finRotate (M + 1)) (fun i => (u i).1 (m.node i.castSucc))
    simp only [LinearMap.coe_mk, AddHom.coe_mk, h, Finset.sum_sub_distrib, LinearMap.id_apply,
      one_smul, evalAt_apply, hrot]

lemma vol_periodic (m : Mesh1D M) (u : Broken M) :
    (periodicCalculus m).vol u = ∑ T, ∫ x in m.node T.castSucc..m.node T.succ, (u T).1 x := by
  rw [BrokenCalculus.vol_apply]
  rfl

lemma jump_periodic (m : Mesh1D M) (e : Fin (M + 1)) (u : Broken M) :
    (periodicCalculus m).jump e u = (u e).1 (m.node e.succ) -
      (u (finRotate (M + 1) e)).1 (m.node (finRotate (M + 1) e).castSucc) := by
  rw [BrokenCalculus.jump_apply]
  rfl

lemma avg_periodic (m : Mesh1D M) (e : Fin (M + 1)) (u : Broken M) :
    (periodicCalculus m).avg e u = (2⁻¹ : ℝ) *
      ((u (finRotate (M + 1) e)).1 (m.node (finRotate (M + 1) e).castSucc) +
        (u e).1 (m.node e.succ)) := by
  rw [BrokenCalculus.avg_apply]
  rfl

lemma skel_periodic (m : Mesh1D M) (a : Fin (M + 1) → ℝ) :
    (periodicCalculus m).skel () a = ∑ e, a e := by
  rw [BrokenCalculus.skel_apply]
  simp [periodicCalculus]

/-- The piecewise polynomial coefficients: one polynomial of degree `≤ p` on each element. -/
abbrev PolyCoef (M p : ℕ) : Type := Fin (M + 1) → Polynomial.degreeLT ℝ (p + 1)

open scoped ContDiff in
/-- A polynomial as a smooth function. -/
noncomputable def polyFn (q : ℝ[X]) : smoothFn :=
  ⟨fun x => q.eval x, show ContDiff ℝ ∞ (fun x => q.eval x) by
    have := Polynomial.contDiff_aeval (𝕜 := ℝ) q ∞
    simpa only [Polynomial.coe_aeval_eq_eval] using this⟩

/-- The embedding of the DG space into the broken functions. -/
noncomputable def polyEmb (M p : ℕ) : PolyCoef M p →ₗ[ℝ] Broken M where
  toFun q i := polyFn (q i : ℝ[X])
  map_add' q r := funext fun i => Subtype.ext (funext fun x => by
    simp [polyFn])
  map_smul' c q := funext fun i => Subtype.ext (funext fun x => by
    simp [polyFn])

lemma polyEmb_apply (p : ℕ) (q : PolyCoef M p) (i : Fin (M + 1)) (x : ℝ) :
    (polyEmb M p q i).1 x = (q i : ℝ[X]).eval x := rfl

/-- A positive weight. -/
abbrev PosWeight (M : ℕ) : Type := {w : Broken M // ∀ i x, 0 < (w i).1 x}

/-- The space `𝒱ₕ,ₚ` of piecewise polynomials of degree `≤ p`, as a type of its own that carries the
inner product with the weight `w`. -/
def DGPoly (_ : Mesh1D M) (_ : PosWeight M) (p : ℕ) : Type := PolyCoef M p

variable (m : Mesh1D M) (w : PosWeight M) (p : ℕ)

noncomputable instance : AddCommGroup (DGPoly m w p) :=
  inferInstanceAs (AddCommGroup (PolyCoef M p))

noncomputable instance : Module ℝ (DGPoly m w p) := inferInstanceAs (Module ℝ (PolyCoef M p))

/-- The linear embedding for `DGPoly`. -/
noncomputable def dgEmb : DGPoly m w p →ₗ[ℝ] Broken M := polyEmb M p

lemma node_lt (T : Fin (M + 1)) : m.node T.castSucc < m.node T.succ :=
  m.mono Fin.castSucc_lt_succ

private lemma elem_nonneg (q : DGPoly m w p) (T : Fin (M + 1)) :
    0 ≤ ∫ x in m.node T.castSucc..m.node T.succ,
      ((w.1 * dgEmb m w p q * dgEmb m w p q) T).1 x := by
  refine intervalIntegral.integral_nonneg (node_lt m T).le fun x _ => ?_
  change 0 ≤ (w.1 T).1 x * (polyEmb M p q T).1 x * (polyEmb M p q T).1 x
  rw [mul_assoc]
  exact mul_nonneg (w.2 T x).le (mul_self_nonneg _)

/-- The inner product `(q, r) ↦ ∑_T ∫_T w q r` on piecewise polynomials. -/
@[reducible] noncomputable def polyCore : InnerProductSpace.Core ℝ (DGPoly m w p) where
  inner q r := (periodicCalculus m).vol (w.1 * dgEmb m w p q * dgEmb m w p r)
  conj_inner_symm q r := by
    simp only [conj_trivial]
    rw [mul_right_comm]
  re_inner_nonneg q := by
    simp only [RCLike.re_to_real]
    rw [vol_periodic]
    exact Finset.sum_nonneg fun T _ => elem_nonneg m w p q T
  add_left q r s := by
    simp only [map_add, mul_add, add_mul]
  smul_left q r c := by
    simp only [map_smul, mul_smul_comm, smul_mul_assoc, conj_trivial, smul_eq_mul]
  definite q h := by
    rw [vol_periodic] at h
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun T _ => elem_nonneg m w p q T).1 h
    refine funext fun T => Subtype.ext ?_
    have hT := h0 T (Finset.mem_univ T)
    have hroot : ∀ x ∈ Set.Icc (m.node T.castSucc) (m.node T.succ),
        ((q T : ℝ[X])).IsRoot x := by
      intro x hx
      by_contra hne
      have hpos : 0 < ((w.1 * dgEmb m w p q * dgEmb m w p q) T).1 x := by
        change 0 < (w.1 T).1 x * (q T : ℝ[X]).eval x * (q T : ℝ[X]).eval x
        rw [mul_assoc]
        exact mul_pos (w.2 T x) (mul_self_pos.2 hne)
      have := intervalIntegral.integral_pos (node_lt m T)
        (smoothFn_cont _).continuousOn (fun y _ => ?_) ⟨x, hx, hpos⟩
      · exact this.ne' hT
      · change 0 ≤ (w.1 T).1 y * (polyEmb M p q T).1 y * (polyEmb M p q T).1 y
        rw [mul_assoc]
        exact mul_nonneg (w.2 T y).le (mul_self_nonneg _)
    exact Polynomial.eq_zero_of_infinite_isRoot _
      ((Set.Icc_infinite (node_lt m T)).mono hroot)

noncomputable instance : NormedAddCommGroup (DGPoly m w p) :=
  (polyCore m w p).toNormedAddCommGroup

noncomputable instance : InnerProductSpace ℝ (DGPoly m w p) :=
  InnerProductSpace.ofCore (polyCore m w p).toCore

noncomputable instance : FiniteDimensional ℝ (DGPoly m w p) :=
  have : FiniteDimensional ℝ (Polynomial.degreeLT ℝ (p + 1)) :=
    LinearEquiv.finiteDimensional (Polynomial.degreeLTEquiv ℝ (p + 1)).symm
  inferInstanceAs (FiniteDimensional ℝ (PolyCoef M p))

/-- The space `𝒱ₕ,ₚ` of piecewise polynomials with the weight `w`. -/
noncomputable def dgSpace : DGSpace (periodicCalculus m) w.1 (DGPoly m w p) where
  emb := dgEmb m w p
  inner_eq _ _ := rfl

/-- The weight `1`. -/
noncomputable def oneW (M : ℕ) : PosWeight M :=
  ⟨1, fun _ _ => show (0 : ℝ) < 1 by norm_num⟩

open scoped ContDiff in
/-- The Gaussian weight `ω(v) = exp(-v² / 2)` of Section 2.2. -/
noncomputable def gaussW (M : ℕ) : PosWeight M :=
  ⟨fun _ => ⟨fun v => Real.exp (-v ^ 2 / 2),
    show ContDiff ℝ ∞ (fun v : ℝ => Real.exp (-v ^ 2 / 2)) by fun_prop⟩,
    fun _ _ => Real.exp_pos _⟩

/-- The coordinate function, the same on all elements. -/
noncomputable def coordB (M : ℕ) : Broken M := fun _ => polyFn Polynomial.X

@[simp] lemma coordB_apply (i : Fin (M + 1)) (x : ℝ) : (coordB M i).1 x = x := by
  simp [coordB, polyFn]

/-- The same polynomial on all elements. -/
noncomputable def polyConst (P : ℝ[X]) (hP : P ∈ Polynomial.degreeLT ℝ (p + 1)) : DGPoly m w p :=
  fun _ => ⟨P, hP⟩

lemma dgEmb_polyConst_apply (P : ℝ[X]) (hP : P ∈ Polynomial.degreeLT ℝ (p + 1))
    (i : Fin (M + 1)) (x : ℝ) : (dgEmb m w p (polyConst m w p P hP) i).1 x = P.eval x := rfl

lemma one_mem_degreeLT : (1 : ℝ[X]) ∈ Polynomial.degreeLT ℝ (p + 1) := by
  rw [Polynomial.mem_degreeLT]
  simp only [Polynomial.degree_one]
  exact_mod_cast Nat.succ_pos p

lemma X_mem_degreeLT (hp : 1 ≤ p) : (Polynomial.X : ℝ[X]) ∈ Polynomial.degreeLT ℝ (p + 1) := by
  rw [Polynomial.mem_degreeLT, Polynomial.degree_X]
  exact_mod_cast (by omega : 1 < p + 1)

lemma broken_ext {u v : Broken M} (h : ∀ i x, (u i).1 x = (v i).1 x) : u = v :=
  funext fun i => Subtype.ext (funext (h i))

lemma dgEmb_one : dgEmb m w p (polyConst m w p 1 (one_mem_degreeLT p)) = 1 :=
  broken_ext fun i x => by
    rw [dgEmb_polyConst_apply]
    simp

lemma dgEmb_X (hp : 1 ≤ p) : dgEmb m w p (polyConst m w p _ (X_mem_degreeLT p hp)) = coordB M :=
  rfl

lemma pdB_coordB : pdB M (coordB M) = 1 :=
  broken_ext fun i x => by
    rw [pdB_apply]
    change deriv (fun x : ℝ => Polynomial.eval x Polynomial.X) x = 1
    simp

/-- `[v]_e`: the coordinate only jumps across the wrap-around face. -/
lemma jump_coordB (e : Fin (M + 1)) : (periodicCalculus m).jump e (coordB M) =
    if e = Fin.last M then m.node (Fin.last (M + 1)) - m.node 0 else 0 := by
  rw [jump_periodic, coordB_apply, coordB_apply]
  split_ifs with h
  · subst h
    simp
  · have hlt : (e : ℕ) < M := by
      have := e.2
      have hne : (e : ℕ) ≠ M := fun h' => h (Fin.ext h')
      omega
    have hrot : finRotate (M + 1) e = ⟨(e : ℕ) + 1, by omega⟩ :=
      finRotate_of_lt hlt
    have hn : (finRotate (M + 1) e).castSucc = e.succ := by
      rw [hrot]
      ext
      simp
    rw [hn, sub_self]

/-- The concrete `1 + 1`-dimensional phase space of arXiv 2503.10562: periodic meshes of two
intervals, piecewise polynomials of degrees `p` in `x` and `q` in `v`, and a positive weight, for
example the paper's `gaussW`. -/
noncomputable def phase1D {Mx Mv : ℕ} (mx : Mesh1D Mx) (mv : Mesh1D Mv) (p q : ℕ)
    (ω : PosWeight Mv) :
    PhaseSpace Unit (Fin (Mx + 1)) (Fin (Mx + 1)) (Broken Mx) ℝ (Fin (Mv + 1)) (Fin (Mv + 1))
      (Broken Mv) ℝ (DGPoly mx (oneW Mx) p) (DGPoly mv ω q) where
  Cx := periodicCalculus mx
  Cv := periodicCalculus mv
  ω := ω.1
  vel _ := coordB Mv
  Xs := dgSpace mx (oneW Mx) p
  Vs := dgSpace mv ω q

lemma pdB_polyFn (q : ℝ[X]) :
    pdB M (fun _ => polyFn q) = fun _ => polyFn (Polynomial.derivative q) :=
  broken_ext fun i x => by
    rw [pdB_apply]
    exact Polynomial.deriv q

end OneD

section OneDState

open scoped Polynomial

variable {Mx Mv : ℕ} (mx : Mesh1D Mx) (mv : Mesh1D Mv) (p q : ℕ) (ω : PosWeight Mv)

lemma phase1D_hvel (s t : Unit) : (phase1D mx mv p q ω).Cv.pd s ((phase1D mx mv p q ω).vel t) =
    if s = t then 1 else 0 := by
  simp only [Subsingleton.elim s t, ↓reduceIte]
  exact pdB_coordB

/-- The boundary functional of the concrete velocity mesh: only the wrap-around face contributes. -/
lemma phase1D_bdryF (W : DGPoly mv ω q) : (phase1D mx mv p q ω).bdryF () () W =
    (periodicCalculus mv).avg (Fin.last Mv) (ω.1 * dgEmb mv ω q W) *
      (mv.node (Fin.last (Mv + 1)) - mv.node 0) := by
  rw [PhaseSpace.bdryF_apply]
  change (periodicCalculus mv).skel () (fun e => (periodicCalculus mv).avg e
    (ω.1 * dgEmb mv ω q W) * (periodicCalculus mv).jump e (coordB Mv)) = _
  rw [skel_periodic, Finset.sum_eq_single (Fin.last Mv)]
  · simp only [jump_coordB, ↓reduceIte]
  · intro e _ he
    simp only [jump_coordB, he, ↓reduceIte, mul_zero]
  · simp

lemma node_range_pos : 0 < mv.node (Fin.last (Mv + 1)) - mv.node 0 :=
  sub_pos.2 (mv.mono (Fin.last_pos))

/-- The trace average at the wrap-around face. -/
lemma avg_last (u : Broken Mv) : (periodicCalculus mv).avg (Fin.last Mv) u =
    (2⁻¹ : ℝ) * ((u 0).1 (mv.node 0) + (u (Fin.last Mv)).1 (mv.node (Fin.last (Mv + 1)))) := by
  rw [avg_periodic]
  simp

/-- The trace `U⁻` at the face `e`, from the element to its left. -/
noncomputable def traceL {M : ℕ} (m : Mesh1D M) (e : Fin (M + 1)) (u : Broken M) : ℝ :=
  (u e).1 (m.node e.succ)

/-- The trace `U⁺` at the face `e`, from the element to its right, cyclically. -/
noncomputable def traceR {M : ℕ} (m : Mesh1D M) (e : Fin (M + 1)) (u : Broken M) : ℝ :=
  (u (finRotate (M + 1) e)).1 (m.node (finRotate (M + 1) e).castSucc)

private lemma face_periodic {M : ℕ} (m : Mesh1D M) (a b : Broken M) (e : Fin (M + 1)) :
    (periodicCalculus m).faceInt e ((∑ s : Unit, (periodicCalculus m).normal e s •
      (periodicCalculus m).avg e a) * (periodicCalculus m).jump e b) =
    2⁻¹ * (traceR m e a + traceL m e a) * (traceL m e b - traceR m e b) := by
  rw [avg_periodic, jump_periodic]
  simp [periodicCalculus, traceL, traceR]

private lemma phase1D_inner (a b ψ : DGPoly mx (oneW Mx) p) :
    ⟪a - b, ψ⟫ = ∑ T, ∫ x in mx.node T.castSucc..mx.node T.succ,
      (((dgEmb mx (oneW Mx) p a) T).1 x - ((dgEmb mx (oneW Mx) p b) T).1 x) *
        ((dgEmb mx (oneW Mx) p ψ) T).1 x := by
  rw [(dgSpace mx (oneW Mx) p).inner_eq]
  change (periodicCalculus mx).vol (1 * dgEmb mx (oneW Mx) p (a - b) * dgEmb mx (oneW Mx) p ψ) = _
  rw [vol_periodic, map_sub]
  refine Finset.sum_congr rfl fun T _ => intervalIntegral.integral_congr fun x _ => ?_
  change 1 * (((dgEmb mx (oneW Mx) p a) T).1 x - ((dgEmb mx (oneW Mx) p b) T).1 x) *
    ((dgEmb mx (oneW Mx) p ψ) T).1 x = _
  rw [one_mul]

variable {I J K L 𝔞 R : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L] [Fintype 𝔞]
  [Fintype R]

/-- arXiv 2503.10562, Theorem 3.4 written out for `d = 1`: on periodic meshes of two intervals with
piecewise polynomials of degrees `p` and `q`, any positive weight (`gaussW` is the paper's) and
any field `E`, the density and the current satisfy
`(1/τ) ∑_T ∫_T (ρ¹ - ρ⁰) ψ - ∑_T ∫_T j ψ' + ∑_e {j}_e [ψ]_e = 0`. -/
theorem theorem_3_4_periodic {Ef : Unit → Broken Mx} {τ : ℝ} (hτ : τ ≠ 0)
    {X : I → DGPoly mx (oneW Mx) p}
    {S : Matrix I J ℝ} {V : J → DGPoly mv ω q} {U : 𝔞 → DGPoly mv ω q}
    {Kn : J → DGPoly mx (oneW Mx) p} {Xa : K → DGPoly mx (oneW Mx) p} {Va : L → DGPoly mv ω q}
    {Sa : Matrix K L ℝ} {ZK : R → DGPoly mx (oneW Mx) p} {ZW : R → DGPoly mv ω q}
    {Y₁ : DGPoly mx (oneW Mx) p ⊗[ℝ] DGPoly mv ω q}
    (h : (phase1D mx mv p q ω).IsConsStep Ef τ X S V U Kn Xa Va Sa ZK ZW Y₁)
    (hmem : polyConst mv ω q 1 (one_mem_degreeLT q) ∈ Submodule.span ℝ (Set.range U))
    (ψ : DGPoly mx (oneW Mx) p) (ρ₀ ρ₁ j φ : Broken Mx)
    (hρ₀ : ρ₀ = dgEmb mx (oneW Mx) p ((phase1D mx mv p q ω).rho (PhaseSpace.lowRank X S V)))
    (hρ₁ : ρ₁ = dgEmb mx (oneW Mx) p ((phase1D mx mv p q ω).rho Y₁))
    (hj : j = dgEmb mx (oneW Mx) p ((phase1D mx mv p q ω).cur () (PhaseSpace.lowRank X S V)))
    (hφ : φ = dgEmb mx (oneW Mx) p ψ) :
    (1 / τ) * (∑ T, ∫ x in mx.node T.castSucc..mx.node T.succ,
        ((ρ₁ T).1 x - (ρ₀ T).1 x) * (φ T).1 x) -
      (∑ T, ∫ x in mx.node T.castSucc..mx.node T.succ, (j T).1 x * deriv (φ T).1 x) +
      ∑ e, 2⁻¹ * (traceR mx e j + traceL mx e j) * (traceL mx e φ - traceR mx e φ) = 0 := by
  have key := (phase1D mx mv p q ω).theorem_3_4 hτ h (dgEmb_one mv ω q) hmem ψ
  subst hρ₀ hρ₁ hj hφ
  have e1 := phase1D_inner mx p ((phase1D mx mv p q ω).rho Y₁)
    ((phase1D mx mv p q ω).rho (PhaseSpace.lowRank X S V)) ψ
  have e2 : ∑ T, (phase1D mx mv p q ω).Cx.elemInt T (∑ s,
      (phase1D mx mv p q ω).Xs.emb ((phase1D mx mv p q ω).cur s (PhaseSpace.lowRank X S V)) *
        (phase1D mx mv p q ω).Cx.pd s ((phase1D mx mv p q ω).Xs.emb ψ)) =
      ∑ T, ∫ x in mx.node T.castSucc..mx.node T.succ,
        ((dgEmb mx (oneW Mx) p ((phase1D mx mv p q ω).cur () (PhaseSpace.lowRank X S V))) T).1 x *
          deriv ((dgEmb mx (oneW Mx) p ψ) T).1 x := by
    refine Finset.sum_congr rfl fun T _ => ?_
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rfl
  have e3 := Finset.sum_congr (rfl : (Finset.univ : Finset (Fin (Mx + 1))) = Finset.univ)
    fun e _ => face_periodic mx
      (dgEmb mx (oneW Mx) p ((phase1D mx mv p q ω).cur () (PhaseSpace.lowRank X S V)))
      (dgEmb mx (oneW Mx) p ψ) e
  rw [e1, e2] at key
  rw [← e3]
  exact key

/-- arXiv 2503.10562, Theorem 3.5 written out for `d = 1`, under the paper's support assumption
`hsupp`, which `theorem_3_5_false_on_periodic_velocity_mesh` shows cannot be dropped: the current
and the stress `σ = (f, v²)_v` satisfy
`(1/τ) ∑_T ∫_T (j¹ - j⁰) ψ + ∑_T ∫_T (-σ ψ' + E ρ ψ) + ∑_e {σ}_e [ψ]_e = 0`. -/
theorem theorem_3_5_periodic {Ef : Unit → Broken Mx} {τ : ℝ} (hτ : τ ≠ 0)
    {X : I → DGPoly mx (oneW Mx) p}
    {S : Matrix I J ℝ} {V : J → DGPoly mv ω q} {U : 𝔞 → DGPoly mv ω q}
    {Kn : J → DGPoly mx (oneW Mx) p} {Xa : K → DGPoly mx (oneW Mx) p} {Va : L → DGPoly mv ω q}
    {Sa : Matrix K L ℝ} {ZK : R → DGPoly mx (oneW Mx) p} {ZW : R → DGPoly mv ω q}
    {Y₁ : DGPoly mx (oneW Mx) p ⊗[ℝ] DGPoly mv ω q}
    (h : (phase1D mx mv p q ω).IsConsStep Ef τ X S V U Kn Xa Va Sa ZK ZW Y₁) (hq : 1 ≤ q)
    (hmem : polyConst mv ω q Polynomial.X (X_mem_degreeLT q hq) ∈ Submodule.span ℝ (Set.range U))
    (hsupp : ∀ s, (phase1D mx mv p q ω).bdryMoment s () (PhaseSpace.lowRank X S V) = 0)
    (ψ : DGPoly mx (oneW Mx) p) (ρ₀ j₀ j₁ σ φ : Broken Mx)
    (hρ₀ : ρ₀ = dgEmb mx (oneW Mx) p ((phase1D mx mv p q ω).rho (PhaseSpace.lowRank X S V)))
    (hj₀ : j₀ = dgEmb mx (oneW Mx) p ((phase1D mx mv p q ω).cur () (PhaseSpace.lowRank X S V)))
    (hj₁ : j₁ = dgEmb mx (oneW Mx) p ((phase1D mx mv p q ω).cur () Y₁))
    (hσ : σ = dgEmb mx (oneW Mx) p ((phase1D mx mv p q ω).stress () () (PhaseSpace.lowRank X S V)))
    (hφ : φ = dgEmb mx (oneW Mx) p ψ) :
    (1 / τ) * (∑ T, ∫ x in mx.node T.castSucc..mx.node T.succ,
        ((j₁ T).1 x - (j₀ T).1 x) * (φ T).1 x) +
      (∑ T, ∫ x in mx.node T.castSucc..mx.node T.succ,
        (-((σ T).1 x * deriv (φ T).1 x) + (Ef () T).1 x * (ρ₀ T).1 x * (φ T).1 x)) +
      ∑ e, 2⁻¹ * (traceR mx e σ + traceL mx e σ) * (traceL mx e φ - traceR mx e φ) = 0 := by
  have key := (phase1D mx mv p q ω).theorem_3_5 hτ h (phase1D_hvel mx mv p q ω) (t := ())
    (velh := polyConst mv ω q Polynomial.X (X_mem_degreeLT q hq)) rfl hmem hsupp ψ
  subst hρ₀ hj₀ hj₁ hσ hφ
  have e1 := phase1D_inner mx p ((phase1D mx mv p q ω).cur () Y₁)
    ((phase1D mx mv p q ω).cur () (PhaseSpace.lowRank X S V)) ψ
  have e2 : ∑ T, (phase1D mx mv p q ω).Cx.elemInt T
      (-(∑ s, (phase1D mx mv p q ω).Xs.emb
          ((phase1D mx mv p q ω).stress () s (PhaseSpace.lowRank X S V)) *
        (phase1D mx mv p q ω).Cx.pd s ((phase1D mx mv p q ω).Xs.emb ψ)) +
        Ef () * (phase1D mx mv p q ω).Xs.emb
          ((phase1D mx mv p q ω).rho (PhaseSpace.lowRank X S V)) *
          (phase1D mx mv p q ω).Xs.emb ψ) =
      ∑ T, ∫ x in mx.node T.castSucc..mx.node T.succ,
        (-(((dgEmb mx (oneW Mx) p ((phase1D mx mv p q ω).stress () ()
            (PhaseSpace.lowRank X S V))) T).1 x * deriv ((dgEmb mx (oneW Mx) p ψ) T).1 x) +
          (Ef () T).1 x * ((dgEmb mx (oneW Mx) p ((phase1D mx mv p q ω).rho
            (PhaseSpace.lowRank X S V))) T).1 x * ((dgEmb mx (oneW Mx) p ψ) T).1 x) := by
    refine Finset.sum_congr rfl fun T _ => ?_
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rfl
  have e3 := Finset.sum_congr (rfl : (Finset.univ : Finset (Fin (Mx + 1))) = Finset.univ)
    fun e _ => face_periodic mx
      (dgEmb mx (oneW Mx) p ((phase1D mx mv p q ω).stress () () (PhaseSpace.lowRank X S V)))
      (dgEmb mx (oneW Mx) p ψ) e
  rw [e1, e2] at key
  rw [← e3]
  exact key

end OneDState

section General

variable {𝒳 𝒴 : Type*} [NormedAddCommGroup 𝒳] [InnerProductSpace ℝ 𝒳] [NormedAddCommGroup 𝒴]
  [InnerProductSpace ℝ 𝒴] [FiniteDimensional ℝ 𝒴]

/-- Every pure tensor in `𝒳 ⊗ G` is a low-rank state over an orthonormal basis of `G`. -/
lemma exists_orthonormal_state (ξ : 𝒳) (G : Submodule ℝ 𝒴) {W₀ : 𝒴} (hW₀ : W₀ ∈ G) :
    ∃ (n : ℕ) (V : Fin n → 𝒴) (X : Fin n → 𝒳) (S : Matrix (Fin n) (Fin n) ℝ),
      Orthonormal ℝ V ∧ Submodule.span ℝ (Set.range V) = G ∧
        PhaseSpace.lowRank X S V = ξ ⊗ₜ[ℝ] W₀ := by
  let b := stdOrthonormalBasis ℝ G
  let V : Fin (Module.finrank ℝ G) → 𝒴 := fun k => (b k : 𝒴)
  have hV : Orthonormal ℝ V := b.orthonormal.comp_linearIsometry G.subtypeₗᵢ
  have hsp : Submodule.span ℝ (Set.range V) = G := by
    apply le_antisymm
    · exact Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact (b k).2)
    · intro x hx
      have h := b.sum_repr' ⟨x, hx⟩
      have h' : x = ∑ k, ⟪b k, (⟨x, hx⟩ : G)⟫ • V k := by
        have := congrArg (Subtype.val) h
        simpa [V] using this.symm
      rw [h']
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  refine ⟨_, V, fun _ => ξ, Matrix.diagonal fun j => ⟪V j, W₀⟫, hV, hsp, ?_⟩
  have hfix : basisProj V W₀ = W₀ := basisProj_of_mem hV (hsp.symm ▸ hW₀)
  simp only [PhaseSpace.lowRank, Matrix.diagonal_apply, ite_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]
  conv_rhs => rw [← hfix, basisProj_apply, TensorProduct.tmul_sum]
  simp only [TensorProduct.tmul_smul]

end General

section Counterexample

open scoped Polynomial
open Polynomial (C X)

/-- The mesh `{0, 1}` of the unit interval, with one element. -/
noncomputable def unitMesh : Mesh1D 0 where
  node i := ((i : ℕ) : ℝ)
  mono := fun i j h => show ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) from Nat.cast_lt.2 h

/-- `E(x) = x (1 - x) / 2 - 1 / 12`. -/
noncomputable def polyE : ℝ[X] := C (1 / 2) * X - C (1 / 2) * X ^ 2 - C (1 / 12)

/-- `Φ(x) = x³ / 6 - x² / 4 + x / 12`. -/
noncomputable def polyPhi : ℝ[X] := C (1 / 6) * X ^ 3 - C (1 / 4) * X ^ 2 + C (1 / 12) * X

/-- `ρ(x) = x + 1 / 2`. -/
noncomputable def polyRho : ℝ[X] := X + C (1 / 2)

lemma polyRho_mem : polyRho ∈ Polynomial.degreeLT ℝ (1 + 1) := by
  rw [Polynomial.mem_degreeLT, polyRho, Polynomial.degree_X_add_C]
  norm_num

lemma polyE_eval (x : ℝ) : polyE.eval x = x / 2 - x ^ 2 / 2 - 1 / 12 := by
  simp only [polyE, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_pow]
  ring

lemma polyPhi_eval (x : ℝ) : polyPhi.eval x = x ^ 3 / 6 - x ^ 2 / 4 + x / 12 := by
  simp only [polyPhi, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
  ring

lemma polyRho_eval (x : ℝ) : polyRho.eval x = x + 1 / 2 := by
  simp [polyRho]

lemma polyPhi_derivative_eval (x : ℝ) :
    (Polynomial.derivative polyPhi).eval x = -polyE.eval x := by
  simp only [polyPhi, polyE, Polynomial.derivative_add, Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_C, Polynomial.derivative_pow,
    Polynomial.derivative_X, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_one,
    Polynomial.eval_zero]
  norm_num
  ring

lemma polyPhi_derivative_two_eval (x : ℝ) :
    (Polynomial.derivative (Polynomial.derivative polyPhi)).eval x = polyRho.eval x - 1 := by
  simp only [polyPhi, polyRho, Polynomial.derivative_add, Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_C, Polynomial.derivative_pow,
    Polynomial.derivative_X, Polynomial.derivative_one,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_one,
    Polynomial.eval_zero]
  norm_num
  ring

/-- The integral `∫₀¹ E(x) ρ(x) x dx = -1 / 360`. -/
lemma integral_counter :
    ∫ x in (0 : ℝ)..1, polyE.eval x * polyRho.eval x * x = -1 / 360 := by
  have hF : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun x : ℝ =>
      -x ^ 5 / 10 + x ^ 4 / 16 + x ^ 3 / 18 - x ^ 2 / 48)
      (polyE.eval x * polyRho.eval x * x) x := by
    intro x _
    have h := (((((hasDerivAt_pow 5 x).neg.div_const 10).add
      ((hasDerivAt_pow 4 x).div_const 16)).add ((hasDerivAt_pow 3 x).div_const 18)).sub
      ((hasDerivAt_pow 2 x).div_const 48))
    convert h using 1
    rw [polyE_eval, polyRho_eval]
    norm_num
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (Continuous.intervalIntegrable (by
      simp only [polyE_eval, polyRho_eval]
      fun_prop) _ _)]
  norm_num

/-- The field of the counterexample. -/
noncomputable def fieldE : Unit → Broken 0 := fun _ _ => polyFn polyE

/-- The potential of the counterexample. -/
noncomputable def potPhi : Broken 0 := fun _ => polyFn polyPhi

lemma potPhi_eq : potPhi = fun _ => polyFn polyPhi := rfl

lemma jump_poly (P : ℝ[X]) (e : Fin (0 + 1)) :
    (periodicCalculus unitMesh).jump e (fun _ => polyFn P) = P.eval 1 - P.eval 0 := by
  have he : e = 0 := Fin.ext (by omega)
  have hr : finRotate (0 + 1) e = 0 := Fin.ext (by
    have := (finRotate (0 + 1) e).2
    simp only [Fin.val_zero]
    omega)
  rw [jump_periodic, hr, he]
  simp [unitMesh, polyFn]

/-- arXiv 2503.10562, Eq. (2), an exact solution used for the counterexample to Theorem 3.5: on the
periodic unit interval, `E = x (1 - x)/2 - 1/12` and `Φ = x³/6 - x²/4 + x/12` solve
`E = -Φ'`, `-Φ'' = 1 - ρ` for `ρ = x + 1/2`, and `E` and `Φ` are continuous and periodic. -/
theorem isPoissonField_counter {ρ : Broken 0} (hρ : ρ = fun _ => polyFn polyRho) :
    (periodicCalculus unitMesh).IsPoissonField fieldE ρ potPhi where
  grad _ := by
    change fieldE () = - pdB 0 potPhi
    rw [potPhi_eq, pdB_polyFn]
    exact broken_ext fun i x => by
      change polyE.eval x = -(Polynomial.derivative polyPhi).eval x
      rw [polyPhi_derivative_eval, neg_neg]
  poisson := by
    change -∑ s : Unit, pdB 0 (pdB 0 potPhi) = 1 - ρ
    rw [potPhi_eq, pdB_polyFn, pdB_polyFn, hρ]
    simp only [Finset.univ_unique, Finset.sum_singleton]
    exact broken_ext fun i x => by
      change -(Polynomial.derivative (Polynomial.derivative polyPhi)).eval x = 1 - polyRho.eval x
      rw [polyPhi_derivative_two_eval]
      ring
  pot_cont e := by
    rw [potPhi_eq, jump_poly, polyPhi_eval, polyPhi_eval]
    norm_num
  field_cont _ e := by
    rw [show fieldE _ = fun _ => polyFn polyE from rfl, jump_poly, polyE_eval, polyE_eval]
    norm_num

/-- The left side of Theorem 3.5 for the test function `ψ`. -/
noncomputable def PhaseSpace.momentumResidual {ι 𝓣x 𝓕x Bx Ax 𝓣v 𝓕v Bv Av 𝒳 𝒴 : Type*} [Fintype ι]
    [Fintype 𝓣x] [Fintype 𝓕x] [CommRing Bx] [Algebra ℝ Bx] [CommRing Ax] [Algebra ℝ Ax]
    [Fintype 𝓣v] [Fintype 𝓕v] [CommRing Bv] [Algebra ℝ Bv] [CommRing Av] [Algebra ℝ Av]
    [NormedAddCommGroup 𝒳] [InnerProductSpace ℝ 𝒳] [NormedAddCommGroup 𝒴]
    [InnerProductSpace ℝ 𝒴] (D : PhaseSpace ι 𝓣x 𝓕x Bx Ax 𝓣v 𝓕v Bv Av 𝒳 𝒴) (Ef : ι → Bx)
    (τ : ℝ) (t : ι) (Y₀ Y₁ : 𝒳 ⊗[ℝ] 𝒴) (ψ : 𝒳) : ℝ :=
  (1 / τ) * ⟪D.cur t Y₁ - D.cur t Y₀, ψ⟫ +
    ∑ T, D.Cx.elemInt T
      (-(∑ s, D.Xs.emb (D.stress t s Y₀) * D.Cx.pd s (D.Xs.emb ψ)) +
        Ef t * D.Xs.emb (D.rho Y₀) * D.Xs.emb ψ) +
    ∑ e, D.Cx.faceInt e
      ((∑ s, D.Cx.normal e s • D.Cx.avg e (D.Xs.emb (D.stress t s Y₀))) *
        D.Cx.jump e (D.Xs.emb ψ))

/-- **arXiv 2503.10562, Theorem 3.5 needs its support assumption.** Without the standing
assumption of Section 3.1 that the computational domain contains the support of the solution,
Eq. (45) fails on a periodic velocity mesh. For every periodic mesh
of a velocity interval, every positive weight `ω` (the Gaussian included) and `q ≥ 1`, take
`x ∈ [0, 1]` with one element and `p = 1`, and the positive state `f = ρ(x) ω(v) / ∫ ω` with
`ρ = x + 1/2`. Its velocity basis contains `1` and `v`, `E = x (1 - x)/2 - 1/12` is its exact
Poisson field, a conservative step exists, and the left side of Theorem 3.5 is nonzero for `ψ = x`,
whatever `τ ≠ 0`. By `theorem_3_5_defect` it equals `(E β, ψ)_x`, and `∫₀¹ E ρ x dx = -1/360`.
This state does not vanish at the ends of the velocity interval, so it violates the paper's support
assumption: it is not a counterexample to the printed theorem, and the name records only that the
identity fails on a periodic velocity mesh without that assumption. -/
theorem theorem_3_5_false_on_periodic_velocity_mesh {Mv q : ℕ} (mv : Mesh1D Mv) (ω : PosWeight Mv)
    (hq : 1 ≤ q) {τ : ℝ} (hτ : τ ≠ 0) :
    ∃ (n k : ℕ) (Xs : Fin n → DGPoly unitMesh (oneW 0) 1) (S : Matrix (Fin n) (Fin n) ℝ)
      (V : Fin n → DGPoly mv ω q) (Kn : Fin n → DGPoly unitMesh (oneW 0) 1)
      (Xa : Fin k → DGPoly unitMesh (oneW 0) 1) (Sa : Matrix (Fin k) (Fin n) ℝ)
      (Y₁ : DGPoly unitMesh (oneW 0) 1 ⊗[ℝ] DGPoly mv ω q) (ψ : DGPoly unitMesh (oneW 0) 1),
      (phase1D unitMesh mv 1 q ω).IsConsStep fieldE τ Xs S V V Kn Xa V Sa (fun _ : Empty => 0)
        (fun _ : Empty => 0) Y₁ ∧
      polyConst mv ω q 1 (one_mem_degreeLT q) ∈ Submodule.span ℝ (Set.range V) ∧
      polyConst mv ω q X (X_mem_degreeLT q hq) ∈ Submodule.span ℝ (Set.range V) ∧
      (periodicCalculus unitMesh).IsPoissonField fieldE
        (dgEmb unitMesh (oneW 0) 1
          ((phase1D unitMesh mv 1 q ω).rho (PhaseSpace.lowRank Xs S V))) potPhi ∧
      (phase1D unitMesh mv 1 q ω).momentumResidual fieldE τ ()
        (PhaseSpace.lowRank Xs S V) Y₁ ψ ≠ 0 := by
  classical
  let D := phase1D unitMesh mv 1 q ω
  let one : DGPoly mv ω q := polyConst mv ω q 1 (one_mem_degreeLT q)
  let vh : DGPoly mv ω q := polyConst mv ω q X (X_mem_degreeLT q hq)
  have hone : dgEmb mv ω q one = 1 := dgEmb_one mv ω q
  let m₀ : ℝ := (periodicCalculus mv).vol (ω.1 * dgEmb mv ω q one * 1)
  have hm₀ : 0 < m₀ := by
    have h1 : one ≠ 0 := by
      intro h
      have h2 : dgEmb mv ω q one = 0 := by rw [h, map_zero]
      rw [hone] at h2
      have h3 := congrArg (evalAt (0 : Fin (Mv + 1)) 0) h2
      simp at h3
    have h2 : (0 : ℝ) < ⟪one, one⟫ := real_inner_self_pos.2 h1
    have h3 : ⟪one, one⟫ = m₀ := by
      change (periodicCalculus mv).vol (ω.1 * dgEmb mv ω q one * dgEmb mv ω q one) = m₀
      simp only [m₀]
      rw [hone]
    rwa [h3] at h2
  let ρ₀ : DGPoly unitMesh (oneW 0) 1 := polyConst unitMesh (oneW 0) 1 polyRho polyRho_mem
  obtain ⟨n, V, Xs, S, hV, hsp, hY⟩ := exists_orthonormal_state (m₀⁻¹ • ρ₀)
    (Submodule.span ℝ {one, vh}) (W₀ := one) (Submodule.subset_span (Set.mem_insert _ _))
  obtain ⟨Kn, k, Xa, Sa, Y₁, hstep⟩ := D.exists_isConsStep (Ef := fieldE) hτ Xs S hV hV
    (fun a => Submodule.subset_span ⟨a, rfl⟩)
  have h1 : one ∈ Submodule.span ℝ (Set.range V) :=
    hsp ▸ Submodule.subset_span (Set.mem_insert _ _)
  have h2 : vh ∈ Submodule.span ℝ (Set.range V) :=
    hsp ▸ Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hrho : D.rho (PhaseSpace.lowRank Xs S V) = ρ₀ := by
    rw [hY, PhaseSpace.rho, PhaseSpace.moment, contr_tmul, PhaseSpace.momF_apply]
    change m₀ • m₀⁻¹ • ρ₀ = ρ₀
    rw [smul_smul, mul_inv_cancel₀ hm₀.ne', one_smul]
  let b : ℝ := D.bdryF () () one
  have hb : b ≠ 0 := by
    have hb' := phase1D_bdryF unitMesh mv 1 q ω one
    have hpos : 0 < (periodicCalculus mv).avg (Fin.last Mv) (ω.1 * dgEmb mv ω q one) := by
      rw [hone, mul_one, avg_last]
      have := ω.2 0 (mv.node 0)
      have := ω.2 (Fin.last Mv) (mv.node (Fin.last (Mv + 1)))
      positivity
    have := mul_pos hpos (node_range_pos mv)
    change b = _ at hb'
    rw [hb']
    exact this.ne'
  have hbd : D.bdryMoment () () (PhaseSpace.lowRank Xs S V) = (b * m₀⁻¹) • ρ₀ := by
    rw [hY, PhaseSpace.bdryMoment, contr_tmul, smul_smul]
  let ψ : DGPoly unitMesh (oneW 0) 1 :=
    polyConst unitMesh (oneW 0) 1 X (X_mem_degreeLT 1 le_rfl)
  refine ⟨n, k, Xs, S, V, Kn, Xa, Sa, Y₁, ψ, hstep, h1, h2,
    isPoissonField_counter (congrArg (dgEmb unitMesh (oneW 0) 1) hrho), ?_⟩
  have key := D.theorem_3_5_defect hτ hstep (phase1D_hvel unitMesh mv 1 q ω) (t := ())
    (velh := vh) rfl h2 ψ
  have hres : D.momentumResidual fieldE τ () (PhaseSpace.lowRank Xs S V) Y₁ ψ =
      (periodicCalculus unitMesh).vol (fieldE () *
        dgEmb unitMesh (oneW 0) 1 ((b * m₀⁻¹) • ρ₀) * dgEmb unitMesh (oneW 0) 1 ψ) := by
    rw [← hbd]
    exact key.trans (by simp; rfl)
  change D.momentumResidual fieldE τ () (PhaseSpace.lowRank Xs S V) Y₁ ψ ≠ 0
  have hvol : (periodicCalculus unitMesh).vol (fieldE () * dgEmb unitMesh (oneW 0) 1 ρ₀ *
      dgEmb unitMesh (oneW 0) 1 ψ) = -1 / 360 := by
    rw [vol_periodic, ← integral_counter]
    refine (Fin.sum_univ_one _).trans ?_
    have h0 : unitMesh.node (Fin.castSucc (0 : Fin 1)) = 0 := by simp [unitMesh]
    have h1 : unitMesh.node (Fin.succ (0 : Fin 1)) = 1 := by simp [unitMesh]
    rw [h0, h1]
    refine intervalIntegral.integral_congr fun x _ => ?_
    change polyE.eval x * polyRho.eval x * (X : ℝ[X]).eval x = _
    rw [Polynomial.eval_X]
  rw [hres, map_smul, mul_smul_comm, smul_mul_assoc, map_smul, hvol, smul_eq_mul]
  exact mul_ne_zero (mul_ne_zero hb (inv_ne_zero hm₀.ne')) (by norm_num)

lemma vol_bubble_pos {Mv q : ℕ} (mv : Mesh1D Mv) (ω : PosWeight Mv) {P : ℝ[X]}
    (hP : P ∈ Polynomial.degreeLT ℝ (q + 1))
    (hpos : ∀ x, mv.node 0 < x → x < mv.node (Fin.last (Mv + 1)) → 0 < P.eval x) :
    0 < (periodicCalculus mv).vol (ω.1 * dgEmb mv ω q (polyConst mv ω q P hP) * 1) := by
  rw [vol_periodic]
  refine Finset.sum_pos (fun T _ => ?_) Finset.univ_nonempty
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    ((smoothFn_cont _).intervalIntegrable _ _) (fun x hx => ?_) (node_lt mv T)
  have h1 : mv.node 0 < x := lt_of_le_of_lt (mv.mono.monotone (Fin.zero_le _)) hx.1
  have h2 : x < mv.node (Fin.last (Mv + 1)) :=
    lt_of_lt_of_le hx.2 (mv.mono.monotone (Fin.le_last _))
  change 0 < (ω.1 T).1 x * P.eval x * 1
  rw [mul_one]
  exact mul_pos (ω.2 T x) (hpos x h1 h2)

/-- arXiv 2503.10562, Theorem 3.5, non-vacuity: all hypotheses of `theorem_3_5` and
`momentum_conservation` hold together. On the mesh `unitMesh` with `p = 1`, on every periodic
velocity mesh with `q ≥ 2` and for every positive weight, the state
`f = ρ(x) ω(v) (v - a)(b - v) / ∫ ω (v - a)(b - v)`, which vanishes at the ends `a, b` of the
velocity interval, has a step, its velocity basis contains `1` and `v`, its boundary moments
vanish and `E` is its exact Poisson field. -/
theorem exists_momentum_instance {Mv q : ℕ} (mv : Mesh1D Mv) (ω : PosWeight Mv) (hq : 2 ≤ q)
    {τ : ℝ} (hτ : τ ≠ 0) :
    ∃ (n k : ℕ) (Xs : Fin n → DGPoly unitMesh (oneW 0) 1) (S : Matrix (Fin n) (Fin n) ℝ)
      (V : Fin n → DGPoly mv ω q) (Kn : Fin n → DGPoly unitMesh (oneW 0) 1)
      (Xa : Fin k → DGPoly unitMesh (oneW 0) 1) (Sa : Matrix (Fin k) (Fin n) ℝ)
      (Y₁ : DGPoly unitMesh (oneW 0) 1 ⊗[ℝ] DGPoly mv ω q),
      (phase1D unitMesh mv 1 q ω).IsConsStep fieldE τ Xs S V V Kn Xa V Sa (fun _ : Empty => 0)
        (fun _ : Empty => 0) Y₁ ∧
      polyConst mv ω q 1 (one_mem_degreeLT q) ∈ Submodule.span ℝ (Set.range V) ∧
      polyConst mv ω q X (X_mem_degreeLT q (by omega)) ∈ Submodule.span ℝ (Set.range V) ∧
      (∀ s, (phase1D unitMesh mv 1 q ω).bdryMoment s () (PhaseSpace.lowRank Xs S V) = 0) ∧
      (periodicCalculus unitMesh).IsPoissonField fieldE
        (dgEmb unitMesh (oneW 0) 1
          ((phase1D unitMesh mv 1 q ω).rho (PhaseSpace.lowRank Xs S V))) potPhi := by
  classical
  let D := phase1D unitMesh mv 1 q ω
  let a : ℝ := mv.node 0
  let b : ℝ := mv.node (Fin.last (Mv + 1))
  let P : ℝ[X] := (X - C a) * (C b - X)
  have hP : P ∈ Polynomial.degreeLT ℝ (q + 1) := by
    rw [Polynomial.mem_degreeLT]
    have h : P.degree ≤ 2 := by
      simp only [P]
      compute_degree
    refine lt_of_le_of_lt h ?_
    exact_mod_cast (by omega : 2 < q + 1)
  let Pc : DGPoly mv ω q := polyConst mv ω q P hP
  let one : DGPoly mv ω q := polyConst mv ω q 1 (one_mem_degreeLT q)
  let vh : DGPoly mv ω q := polyConst mv ω q X (X_mem_degreeLT q (by omega))
  let m₀ : ℝ := (periodicCalculus mv).vol (ω.1 * dgEmb mv ω q Pc * 1)
  have hm₀ : 0 < m₀ := vol_bubble_pos mv ω hP fun x h1 h2 => by
    simp only [P, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact mul_pos (sub_pos.2 h1) (sub_pos.2 h2)
  let ρ₀ : DGPoly unitMesh (oneW 0) 1 := polyConst unitMesh (oneW 0) 1 polyRho polyRho_mem
  obtain ⟨n, V, Xs, S, hV, hsp, hY⟩ := exists_orthonormal_state (m₀⁻¹ • ρ₀)
    (Submodule.span ℝ {one, vh, Pc}) (W₀ := Pc) (Submodule.subset_span
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  obtain ⟨Kn, k, Xa, Sa, Y₁, hstep⟩ := D.exists_isConsStep (Ef := fieldE) hτ Xs S hV hV
    (fun a => Submodule.subset_span ⟨a, rfl⟩)
  have hrho : D.rho (PhaseSpace.lowRank Xs S V) = ρ₀ := by
    rw [hY, PhaseSpace.rho, PhaseSpace.moment, contr_tmul, PhaseSpace.momF_apply]
    change m₀ • m₀⁻¹ • ρ₀ = ρ₀
    rw [smul_smul, mul_inv_cancel₀ hm₀.ne', one_smul]
  refine ⟨n, k, Xs, S, V, Kn, Xa, Sa, Y₁, hstep,
    hsp ▸ Submodule.subset_span (Set.mem_insert _ _),
    hsp ▸ Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _)), fun s => ?_,
    isPoissonField_counter (congrArg (dgEmb unitMesh (oneW 0) 1) hrho)⟩
  have hb : D.bdryF s () Pc = 0 := by
    have h := phase1D_bdryF unitMesh mv 1 q ω Pc
    have hzero : (periodicCalculus mv).avg (Fin.last Mv) (ω.1 * dgEmb mv ω q Pc) = 0 := by
      rw [avg_last]
      have ha : ((ω.1 * dgEmb mv ω q Pc) 0).1 (mv.node 0) =
          (ω.1 0).1 (mv.node 0) * P.eval a := rfl
      have hb' : ((ω.1 * dgEmb mv ω q Pc) (Fin.last Mv)).1 (mv.node (Fin.last (Mv + 1))) =
          (ω.1 (Fin.last Mv)).1 (mv.node (Fin.last (Mv + 1))) * P.eval b := rfl
      have hPa : P.eval a = 0 := by simp [P]
      have hPb : P.eval b = 0 := by simp [P]
      rw [ha, hb', hPa, hPb]
      simp
    rw [hzero, zero_mul] at h
    exact h
  rw [hY, PhaseSpace.bdryMoment, contr_tmul, hb, zero_smul]

end Counterexample

end LeanDLRA.Literature.P2503_10562
