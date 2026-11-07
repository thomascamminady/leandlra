import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Hermitian

/-!
# Results of arXiv 1604.05706: Dynamical model reduction for parameter-dependent systems

This module formalises Eq. (11) of Billaud-Friess and Nouy, arXiv 1604.05706 (Section 2.2,
Definition 1): the local logarithmic Lipschitz constant of an affine flux.

The paper defines, for a Lipschitz `f : X → X` on `X = ℝ^d` with its canonical inner product,
`L_X[f](v) = sup_{u ∈ X, u ≠ v} ⟨u - v, f(u) - f(v)⟩ / ‖u - v‖²`. For `f(u) = A u + g` it states
that this is independent of `v` and equals `L_X[A] = sup_{u ≠ 0} ⟨u, A u⟩ / ‖u‖²`, which is
`λ_max((A + Aᵀ)/2)`, the largest eigenvalue of the symmetric part of `A`.

Here `X = EuclideanSpace ℝ (Fin d)`, `A` is a real `d × d` matrix acting through
`Matrix.toEuclideanLin`, and `λ_max` is the greatest eigenvalue of the symmetric part, stated as
`IsGreatest` of its real eigenvalues. The supremum of Definition 1 is stated as `IsLUB` of the set
of quotients, so it is exactly the supremum.

Main results:

* `localLogLipSet_eq_range`: for an affine flux, the set of quotients at `v` is the range of the
  Rayleigh quotient of the symmetric part of `A` over nonzero vectors.
* `affine_localLogLip_eq_lambdaMax` (Eq. (11)): for every `v`, the supremum for `f(u) = A u + g`
  equals the supremum for `A` at `0`, and that common value is the largest eigenvalue of
  `(A + Aᵀ)/2`. The eigenvalue is attained, so the supremum is a maximum.

Hypothesis: `[NeZero d]`, that is `d ≥ 1`. For `d = 0` the quotient set is empty and no largest
eigenvalue exists, so the statement would be false there.

Core definitions: the local log-Lipschitz constant does not occur in `LeanDLRA/`, so the file
defines only `localLogLipSet`, the set whose supremum is `L_X[f](v)`. The file uses no core
one-sided or flux definitions. Mathlib supplies the Rayleigh-quotient supremum theorem
(`LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional`) and the matrix symmetry
correspondence (`Matrix.isSymmetric_toEuclideanLin_iff`).

Not formalised: the Lipschitz hypothesis on `f` (not used, since affine maps are Lipschitz), and
the rest of Section 2.2 (Lemma 1 and Proposition 1).
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P1604_05706

/-- The state space `X = ℝ^d` with its canonical inner product. -/
abbrev Xd (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The set of quotients `⟪u - v, f u - f v⟫ / ‖u - v‖²` over `u ≠ v`, as in Definition 1 of
arXiv 1604.05706. Its supremum is the local logarithmic Lipschitz constant `L_X[f](v)`. -/
def localLogLipSet {d : ℕ} (f : Xd d → Xd d) (v : Xd d) : Set ℝ :=
  {c | ∃ u : Xd d, u ≠ v ∧ c = ⟪u - v, f u - f v⟫ / ‖u - v‖ ^ 2}

/-- The symmetric part `(A + Aᵀ)/2` of a real matrix is Hermitian. -/
lemma symPart_isHermitian {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) :
    ((1 / 2 : ℝ) • (A + Aᵀ)).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply]
  ring

/-- For every `w`, `⟪w, A w⟫ = ⟪S w, w⟫` where `S = (A + Aᵀ)/2`. -/
lemma inner_apply_eq_symPart {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (w : Xd d) :
    ⟪w, Matrix.toEuclideanLin A w⟫ =
      ⟪Matrix.toEuclideanLin ((1 / 2 : ℝ) • (A + Aᵀ)) w, w⟫ := by
  have hT : Matrix.toEuclideanLin ((1 / 2 : ℝ) • (A + Aᵀ)) =
      (1 / 2 : ℝ) • (Matrix.toEuclideanLin A + LinearMap.adjoint (Matrix.toEuclideanLin A)) := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      Matrix.conjTranspose_eq_transpose_of_trivial]
    simp [map_smul, map_add]
  rw [hT]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, inner_smul_left, inner_add_left,
    LinearMap.adjoint_inner_left, real_inner_comm (Matrix.toEuclideanLin A w) w]
  simp only [conj_trivial]
  ring

/-- The quotient set of an affine flux `f u = A u + g` at `v` is the range of the Rayleigh
quotient of the symmetric part of `A` over nonzero vectors. -/
lemma localLogLipSet_eq_range {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (f : Xd d → Xd d) (v : Xd d)
    (hf : ∀ u, f u - f v = Matrix.toEuclideanLin A (u - v)) :
    localLogLipSet f v = Set.range (fun x : {x : Xd d // x ≠ 0} =>
      ⟪Matrix.toEuclideanLin ((1 / 2 : ℝ) • (A + Aᵀ)) (x : Xd d), (x : Xd d)⟫ /
        ‖(x : Xd d)‖ ^ 2) := by
  ext c
  constructor
  · rintro ⟨u, huv, rfl⟩
    refine ⟨⟨u - v, sub_ne_zero.2 huv⟩, ?_⟩
    simp only
    rw [hf u, inner_apply_eq_symPart]
  · rintro ⟨⟨x, hx⟩, rfl⟩
    refine ⟨x + v, fun h => hx (by simpa using h), ?_⟩
    simp only [add_sub_cancel_right]
    rw [hf (x + v), add_sub_cancel_right, inner_apply_eq_symPart]

/-- **Eq. (11) of arXiv 1604.05706.** For an affine flux `f(u) = A u + g` on `ℝ^d`, `d ≥ 1`, the
local logarithmic Lipschitz constant (the supremum of the quotients of Definition 1) does not
depend on the state `v`, equals `L_X[A]` (the supremum for `A` at `v = 0`), and this common value
is the largest eigenvalue `λ_max((A + Aᵀ)/2)` of the symmetric part of `A`. -/
theorem affine_localLogLip_eq_lambdaMax [NeZero d] (A : Matrix (Fin d) (Fin d) ℝ) (g : Xd d) :
    (∀ v : Xd d, localLogLipSet (fun u => Matrix.toEuclideanLin A u + g) v =
      localLogLipSet (fun u => Matrix.toEuclideanLin A u) 0) ∧
    ∃ μ : ℝ,
      IsGreatest {ν : ℝ | Module.End.HasEigenvalue
        (Matrix.toEuclideanLin ((1 / 2 : ℝ) • (A + Aᵀ))) ν} μ ∧
      (∀ v : Xd d, IsLUB (localLogLipSet (fun u => Matrix.toEuclideanLin A u + g) v) μ) ∧
      IsLUB (localLogLipSet (fun u => Matrix.toEuclideanLin A u) 0) μ := by
  have hsetA : ∀ v : Xd d, localLogLipSet (fun u => Matrix.toEuclideanLin A u + g) v =
      Set.range (fun x : {x : Xd d // x ≠ 0} =>
        ⟪Matrix.toEuclideanLin ((1 / 2 : ℝ) • (A + Aᵀ)) (x : Xd d), (x : Xd d)⟫ /
          ‖(x : Xd d)‖ ^ 2) := fun v =>
    localLogLipSet_eq_range A _ v (fun u => by simp only [map_sub]; abel)
  have hset0 : localLogLipSet (fun u => Matrix.toEuclideanLin A u) 0 =
      Set.range (fun x : {x : Xd d // x ≠ 0} =>
        ⟪Matrix.toEuclideanLin ((1 / 2 : ℝ) • (A + Aᵀ)) (x : Xd d), (x : Xd d)⟫ /
          ‖(x : Xd d)‖ ^ 2) :=
    localLogLipSet_eq_range A _ 0 (fun u => by simp)
  set T := Matrix.toEuclideanLin ((1 / 2 : ℝ) • (A + Aᵀ)) with hTdef
  have : Nontrivial (Xd d) := Module.nontrivial_of_finrank_pos (by
    rw [finrank_euclideanSpace_fin]; exact NeZero.pos d)
  obtain ⟨x0, hx0⟩ := exists_ne (0 : Xd d)
  have : Nonempty {x : Xd d // x ≠ 0} := ⟨⟨x0, hx0⟩⟩
  have hsym : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr (symPart_isHermitian A)
  have hEig := hsym.hasEigenvalue_iSup_of_finiteDimensional
  simp only [RCLike.re_to_real] at hEig
  set μ := ⨆ x : {x : Xd d // x ≠ 0}, ⟪T (x : Xd d), (x : Xd d)⟫ / ‖(x : Xd d)‖ ^ 2 with hμ
  have hbdd : BddAbove (Set.range (fun x : {x : Xd d // x ≠ 0} =>
      ⟪T (x : Xd d), (x : Xd d)⟫ / ‖(x : Xd d)‖ ^ 2)) := by
    obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x : Xd d, |⟪T x, x⟫| ≤ C * ‖x‖ ^ 2 := by
      refine ⟨‖LinearMap.toContinuousLinearMap T‖, fun x => ?_⟩
      have h1 : |⟪T x, x⟫| ≤ ‖T x‖ * ‖x‖ := abs_real_inner_le_norm _ _
      have h2 : ‖T x‖ ≤ ‖LinearMap.toContinuousLinearMap T‖ * ‖x‖ :=
        (LinearMap.toContinuousLinearMap T).le_opNorm x
      have h3 : ‖T x‖ * ‖x‖ ≤ ‖LinearMap.toContinuousLinearMap T‖ * ‖x‖ * ‖x‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      nlinarith [h1, h3]
    refine ⟨|C|, ?_⟩
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
    rw [div_le_iff₀ (by positivity)]
    calc _ ≤ |⟪T x, x⟫| := le_abs_self _
      _ ≤ C * ‖x‖ ^ 2 := hC x
      _ ≤ |C| * ‖x‖ ^ 2 := by gcongr; exact le_abs_self C
  have hLUB : IsLUB (Set.range (fun x : {x : Xd d // x ≠ 0} =>
      ⟪T (x : Xd d), (x : Xd d)⟫ / ‖(x : Xd d)‖ ^ 2)) μ := isLUB_ciSup hbdd
  have hgreat : IsGreatest {ν : ℝ | Module.End.HasEigenvalue T ν} μ := by
    refine ⟨hEig, fun ν hν => ?_⟩
    obtain ⟨w, hw⟩ := hν.exists_hasEigenvector
    have hw0 : (w : Xd d) ≠ 0 := hw.2
    have hval : ⟪T w, w⟫ / ‖w‖ ^ 2 = ν := by
      rw [hw.apply_eq_smul, inner_smul_left]
      simp only [conj_trivial]
      have hn : ‖w‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hw0)
      rw [real_inner_self_eq_norm_sq]
      field_simp
    rw [← hval]
    exact le_ciSup hbdd ⟨w, hw0⟩
  refine ⟨fun v => by rw [hsetA v, hset0], μ, hgreat, fun v => ?_, ?_⟩
  · rw [hsetA v]; exact hLUB
  · rw [hset0]; exact hLUB

end LeanDLRA.Literature.P1604_05706
