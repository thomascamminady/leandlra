
import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Tensor.TT.AugmentedBUG

/-!
# Results of arXiv 2603.13990: Schrödinger dynamics with rank-adaptive tensor decompositions

Petersson–Hodges-Heilmann–Günther describe the implicit midpoint rule, the tensor-train (MPS)
formats with their canonical forms, the TDVP and TDVP-2 algorithms, and the BUG integrators for
matrices, Tucker tensors and tensor trains (MPS-BUG). The tensor-train statements are proved in
the core (`Tensor/TT/`) for real tensor trains; this module proves the implicit midpoint results
(complex, §3) and the invariance of mixed canonical and bond-centred states under the local
projectors (§4.2), and records the rest against the library.

* §3, Eqs. (3.7)–(3.8), implicit midpoint rule is unitary and norm-conserving (complex):
  `implicitMidpoint_unitary`, `implicitMidpoint_norm_conserved`.
* §4, gauge invariance (after (4.3)), Eqs. (4.11), (4.13) (moving the orthogonality centre):
  `Tensor.tt_gauge`, `Tensor.ttBond_eq_tt`.
* §4, Lemma 1, Eqs. (4.9)–(4.10) (orthonormal left/right state vectors):
  `Tensor.ttLeft_transpose_mul_self`, `Tensor.ttRight_transpose_mul_self`.
* §4, Eq. (4.12) and the Schmidt rank: `Tensor.ttBond`, `Tensor.rank_unfold_ttBond`.
* §4.2, Eqs. (4.18)–(4.19), (4.28) (TDVP tangent projector, an orthogonal projector, and its
  terms): `Tensor.isOrthProj_ttTangentProj`, `Tensor.ttTangentProj_eq_sum_substeps`,
  `Tensor.isOrthProj_ttKProj`, `Tensor.isOrthProj_ttSProj`.
* §4.2, mixed canonical and bond-centred states are fixed by their local projectors:
  `mixedCanonical_leftProj`, `mixedCanonical_rightProj`, `bondCentred_proj`.
* §4.2, Eqs. (4.22)–(4.27) (core- and bond-centred contractions): `Tensor.ttCoreCoeff`,
  `Tensor.ttCoreCoeff_tt_update`, `Tensor.ttCoreCoeff_ttKProj`, `Tensor.tt_update_ttCoreCoeff`,
  `Tensor.ttBondCoeff`, `Tensor.ttBondCoeff_ttBond`, `Tensor.ttBondCoeff_ttSProj`,
  `Tensor.ttBond_ttBondCoeff`.
* §4.3, Eqs. (4.29)–(4.30) (TDVP sweep) and "TDVP conserves norm and energy":
  `Tensor.IsTTKSLStep`, `Tensor.IsTTKSLStep.norm_eq`, `Tensor.IsTTKSLStep.energy_eq`.
* §5.1, Algorithm 1 (rank-adaptive BUG for matrices): `MatrixBUG.IsRankAdaptiveStep`,
  `MatrixBUG.rankAdaptive_global_error_le` (Ceruti–Kusch–Lubich).
* §5.2, Eqs. (5.6)–(5.12) (MPS-BUG with a centre site): `Tensor.IsTTAugBUGStep` with
  `m = n + 1`, `Tensor.IsTTAugGalerkinStep.eq_tt_update`.
* Appendix A (truncated SVD): `LeanDLRA/Classical/EckartYoung.lean`.

Differences from the paper. The tensor-train statements are for real tensor trains with the
Frobenius inner product; the paper's states are complex (`ψ ∈ ℂ^{d₁ × ⋯ × d_N}`). The core is
real and complex tensor trains are not realified at the level of cores (the realification of a
complex core doubles its bonds but does not keep the one-element boundary bonds of the core
format), so Lemma 1 and the statements of §4.2 are proved only for real cores; for the
Schrödinger equation the abstract realification bridge `P2609_12848.realify_schrodinger_inner_self`
applies to the Galerkin steps. The implicit midpoint statements of §3 are complex. The MPO
representation (4.14)–(4.17), TDVP-2, the consolidation of bond dimensions in MPS-BUG ("beyond
the scope of this presentation"), the observed second order and all numerical results of §6 are
not formalized. Core definitions used: `Tensor.TTCores`, `Tensor.tt`, `Tensor.ttMix`,
`Tensor.ttBond`, `Tensor.ttLeftProj`, `Tensor.ttRightProj`.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2603_13990

variable {n : Type*} [Fintype n]

/-- The sum of squared moduli is the (complex) Hermitian square `⟪v, v⟫`. -/
private lemma sum_norm_sq_eq_star_dotProduct (v : n → ℂ) :
    ∑ i, ((‖v i‖ ^ 2 : ℝ) : ℂ) = star v ⬝ᵥ v := by
  simp [dotProduct, Complex.conj_mul']

/-- The kernel of `1 + c • H` is trivial when `star c = -c` (i.e. `c` is purely imaginary) and `H`
is Hermitian: `⟨x, x⟩ + c ⟨x, H x⟩ = 0` and its conjugate force `⟨x, x⟩ = 0`. -/
private lemma imagCoef_mulVec_injective [DecidableEq n] (H : Matrix n n ℂ)
    (hH : H.IsHermitian) (c : ℂ)
    (hc : star c = -c) (x : n → ℂ) (hx : (1 + c • H) *ᵥ x = 0) : x = 0 := by
  have e1 : star x ⬝ᵥ x + c * (star x ⬝ᵥ (H *ᵥ x)) = 0 := by
    have h' := congrArg (fun v => star x ⬝ᵥ v) hx
    simpa [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
      using h'
  have hs' : star (star x ⬝ᵥ x) = star x ⬝ᵥ x := by
    simp [dotProduct, star_sum, mul_comm]
  have e2 := congrArg star e1
  rw [star_add, star_mul, star_zero, hc, hs', hH.star_dotProduct_mulVec_comm x x] at e2
  have hs : star x ⬝ᵥ x = 0 := by linear_combination (e1 + e2) / 2
  have hr : ∑ i, ‖x i‖ ^ 2 = 0 := by
    have hc0 : ∑ i, ((‖x i‖ ^ 2 : ℝ) : ℂ) = 0 := by rw [sum_norm_sq_eq_star_dotProduct, hs]
    exact_mod_cast hc0
  have hi : ∀ i ∈ (univ : Finset n), ‖x i‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).mp hr
  funext i
  have := hi i (mem_univ i)
  simpa using this

/-- **Implicit midpoint is unitary (arXiv 2603.13990, Sec. 3).** For a Hermitian `H` and a step
`h`, the implicit midpoint rule for `y' = -i H y`, `y₁ = y₀ - (i h/2) H (y₀ + y₁)`, has a unique
solution `y₁`, and the map `y₀ ↦ y₁` is given by a unitary matrix `U` (`Uᴴ U = 1 = U Uᴴ`).

The paper (§3, after Eq. (3.6)) calls the IMR (3.7)–(3.8) "unconditionally stable,
norm-conserving and time-reversible" without stating the step map; its unitarity, with
`U = (1 + c H)⁻¹ (1 - c H)` and `c = i h/2`, is the reason for norm conservation. In (3.8) the
Hamiltonian is evaluated at the midpoint `t_k + δ/2`, a fixed Hermitian matrix in each step. -/
theorem implicitMidpoint_unitary [DecidableEq n] (H : Matrix n n ℂ) (hH : H.IsHermitian) (h : ℝ) :
    ∃ U : Matrix n n ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      ∀ y0 y1 : n → ℂ, y1 = y0 - (Complex.I * ((h / 2 : ℝ) : ℂ)) • (H *ᵥ (y0 + y1)) →
        y1 = U *ᵥ y0 := by
  set c : ℂ := Complex.I * ((h / 2 : ℝ) : ℂ) with hc_def
  have hc : star c = -c := by simp [hc_def]
  set N : Matrix n n ℂ := 1 + c • H with hN_def
  set M : Matrix n n ℂ := 1 - c • H with hM_def
  have hstar : Nᴴ = M := by
    rw [hN_def, hM_def, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
      Matrix.conjTranspose_smul, hH.eq, hc, sub_eq_add_neg, neg_smul]
  have hMH : Mᴴ = N := by rw [← hstar, Matrix.conjTranspose_conjTranspose]
  have hNM : N * M = M * N := by
    have h1 : Commute (1 : Matrix n n ℂ) (1 - c • H) := Commute.one_left _
    have h2 : Commute (c • H) (1 - c • H) :=
      Commute.sub_right (Commute.one_right _) (Commute.refl _)
    exact (Commute.add_left h1 h2).eq
  have hinj : Function.Injective (fun v => N *ᵥ v) := by
    intro a b hab
    have hab' : N *ᵥ a = N *ᵥ b := hab
    have h0 : N *ᵥ (a - b) = 0 := by
      rw [Matrix.mulVec_sub, hab', sub_self]
    exact sub_eq_zero.mp (imagCoef_mulVec_injective H hH c hc (a - b) h0)
  have hNu : IsUnit N := Matrix.mulVec_injective_iff_isUnit.mp hinj
  have hdet : IsUnit N.det := (Matrix.isUnit_iff_isUnit_det N).mp hNu
  set a : Matrix n n ℂ := N⁻¹ with ha_def
  have hNa : N * a = 1 := Matrix.mul_nonsing_inv N hdet
  have haN : a * N = 1 := Matrix.nonsing_inv_mul N hdet
  have haM : a * M = M * a := by
    calc a * M = a * M * (N * a) := by rw [hNa, mul_one]
      _ = a * (M * N) * a := by simp only [mul_assoc]
      _ = a * (N * M) * a := by rw [hNM]
      _ = (a * N) * (M * a) := by simp only [mul_assoc]
      _ = M * a := by rw [haN, one_mul]
  have haH : aᴴ * M = 1 := by
    rw [← hstar, ← Matrix.conjTranspose_mul, hNa, Matrix.conjTranspose_one]
  have hMa : M * aᴴ = 1 := mul_eq_one_comm.mp haH
  have hZM : aᴴ * a * M = a := by rw [mul_assoc, haM, ← mul_assoc, haH, one_mul]
  have hUU : (a * M)ᴴ * (a * M) = 1 := by
    calc (a * M)ᴴ * (a * M) = N * (aᴴ * a) * M := by
          rw [Matrix.conjTranspose_mul, hMH]; simp only [mul_assoc]
      _ = N * (aᴴ * a * M) := by simp only [mul_assoc]
      _ = N * a := by rw [hZM]
      _ = 1 := hNa
  refine ⟨a * M, hUU, mul_eq_one_comm.mp hUU, ?_⟩
  intro y0 y1 hy
  have h2 : H *ᵥ (y0 + y1) = H *ᵥ y0 + H *ᵥ y1 := Matrix.mulVec_add _ _ _
  have hy' : y1 + c • (H *ᵥ y1) = y0 - c • (H *ᵥ y0) := by
    rw [h2, smul_add] at hy
    linear_combination (norm := module) hy
  have hNy : N *ᵥ y1 = M *ᵥ y0 := by
    rw [hN_def, hM_def, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
    exact hy'
  rw [← Matrix.mulVec_mulVec, ← hNy, Matrix.mulVec_mulVec, haN, Matrix.one_mulVec]

/-- **Norm conservation of the implicit midpoint rule (arXiv 2603.13990, Sec. 3).** For a Hermitian
`H`, every solution `y₁` of `y₁ = y₀ - (i h/2) H (y₀ + y₁)` satisfies `‖y₁‖₂ = ‖y₀‖₂`, in the form
`∑ |y₁ᵢ|² = ∑ |y₀ᵢ|²`. This is the consequence of `implicitMidpoint_unitary`. -/
theorem implicitMidpoint_norm_conserved (H : Matrix n n ℂ) (hH : H.IsHermitian) (h : ℝ)
    (y0 y1 : n → ℂ) (hy : y1 = y0 - (Complex.I * ((h / 2 : ℝ) : ℂ)) • (H *ᵥ (y0 + y1))) :
    ∑ i, ‖y1 i‖ ^ 2 = ∑ i, ‖y0 i‖ ^ 2 := by
  classical
  obtain ⟨U, hU, _, hsol⟩ := implicitMidpoint_unitary H hH h
  have hy1 := hsol y0 y1 hy
  have hnorm : star (U *ᵥ y0) ⬝ᵥ (U *ᵥ y0) = star y0 ⬝ᵥ y0 := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  have hc : ∑ i, ((‖y1 i‖ ^ 2 : ℝ) : ℂ) = ∑ i, ((‖y0 i‖ ^ 2 : ℝ) : ℂ) := by
    rw [sum_norm_sq_eq_star_dotProduct, sum_norm_sq_eq_star_dotProduct, hy1, hnorm]
  exact_mod_cast hc

/-- Non-vacuity: the implicit midpoint hypothesis holds, e.g. for `H = 0` and `y₁ = y₀`. -/
example (y0 : Fin 2 → ℂ) :
    y0 = y0 - (Complex.I * ((1 / 2 : ℝ) : ℂ)) •
      ((0 : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ (y0 + y0)) := by
  simp

/-! ### Mixed canonical and bond-centred states (§4.2) -/

section Canonical

open LeanDLRA.Tensor

variable {d : ℕ} {ι : Fin d → Type*} [∀ i, Fintype (ι i)] {β : ℕ → Type*}
  [∀ k, Fintype (β k)] [∀ k, DecidableEq (β k)]

/-- arXiv 2603.13990, §4.2, before Eq. (4.22) (real tensor trains): a state in mixed canonical
form with orthogonality centre at core `j` (left-normalized cores `A` before `j`, centre `M`) is
fixed by the left projector `P̂^{L}_{j-1}` built from its own left cores. -/
theorem mixedCanonical_leftProj [Subsingleton (β 0)] {A B : TTCores ι β} {j : ℕ} (hj : j < d)
    (hA : ∀ i : Fin d, i.val < j → IsLeftOrth A i) (M : β j → ι ⟨j, hj⟩ → β (j + 1) → ℝ) :
    ttLeftProj A j (tt (Function.update (ttMix A B j) ⟨j, hj⟩ M)) =
      tt (Function.update (ttMix A B j) ⟨j, hj⟩ M) := by
  have e : ttLeftProj A j = ttLeftProj (Function.update (ttMix A B j) ⟨j, hj⟩ M) j := by
    simp only [ttLeftProj, ttLeft_update _ ⟨j, hj⟩ M le_rfl, ttLeft_ttMix A B le_rfl]
  rw [e]
  refine ttLeftProj_tt hj.le fun i hi => ?_
  have hne : i ≠ ⟨j, hj⟩ := fun h => by have := congrArg Fin.val h; simp at this; omega
  intro b b'
  simp only [Function.update_of_ne hne, ttMix, hi, ↓reduceIte]
  exact hA i hi b b'

/-- arXiv 2603.13990, §4.2, before Eq. (4.22) (real tensor trains): a state in mixed canonical
form with centre at core `j` (right-normalized cores `B` after `j`) is fixed by the right
projector `P̂^{R}_{j+1}` built from its own right cores. -/
theorem mixedCanonical_rightProj [Subsingleton (β d)] {A B : TTCores ι β} {j : ℕ} (hj : j < d)
    (hB : ∀ i : Fin d, j + 1 ≤ i.val → IsRightOrth B i) (M : β j → ι ⟨j, hj⟩ → β (j + 1) → ℝ) :
    ttRightProj B (j + 1) (tt (Function.update (ttMix A B j) ⟨j, hj⟩ M)) =
      tt (Function.update (ttMix A B j) ⟨j, hj⟩ M) := by
  have e : ttRightProj B (j + 1) =
      ttRightProj (Function.update (ttMix A B j) ⟨j, hj⟩ M) (j + 1) := by
    simp only [ttRightProj, ttRight_update _ ⟨j, hj⟩ M (Nat.lt_succ_self j),
      ttRight_ttMix A B (Nat.le_succ j)]
  rw [e]
  refine ttRightProj_tt hj fun i hi => ?_
  have hne : i ≠ ⟨j, hj⟩ := fun h => by have := congrArg Fin.val h; simp at this; omega
  intro a a'
  simp only [Function.update_of_ne hne, ttMix, show ¬ i.val < j by omega, ↓reduceIte]
  exact hB i hi a a'

/-- arXiv 2603.13990, §4.2, before Eq. (4.22) (real tensor trains): a state in bond-centred form
(4.12) is fixed by the left projector `P̂^{L}_{j}` and the right projector `P̂^{R}_{j+1}` of its
bond, i.e. by the second-sum terms of (4.19). -/
theorem bondCentred_proj [Subsingleton (β 0)] [Subsingleton (β d)] {A B : TTCores ι β} {j : ℕ}
    (hj : j ≤ d) (hA : ∀ i : Fin d, i.val < j → IsLeftOrth A i)
    (hB : ∀ i : Fin d, j ≤ i.val → IsRightOrth B i) (S : Matrix (β j) (β j) ℝ) :
    ttLeftProj A j (ttRightProj B j (ttBond A B j S)) = ttBond A B j S := by
  rw [← ttBond_ttBondCoeff, ttBondCoeff_ttBond hj hA hB]

end Canonical

end LeanDLRA.Literature.P2603_13990
