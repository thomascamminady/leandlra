import LeanDLRA.DLRA.Defs
import LeanDLRA.FixedRank.TangentSpace
import LeanDLRA.Matrix.GaugeODE

/-!
# Dynamically orthogonal formulations of dynamical low-rank approximation

Dynamical low-rank approximation of `Ẏ = F(t, Y)` by rank-`r` matrices `Y = U Zᵀ` can be written
in three equivalent-looking ways: as the projected equation `Ẏ = P(Y) F(t, Y)`
(`LeanDLRA.IsDLRASolution`), as the dynamically orthogonal (DO) system for the factors `(U, Z)`
with `Uᵀ U = 1`, and as the dual (DDO) system for `Y = Z Vᵀ` with `Vᵀ V = 1`; the bi-orthogonal
(BO) system uses `Zᵀ Z = 1` and `Uᵀ U` diagonal ([KochLubich2007], [MusharbashNobileZhou2015],
[ChengHouZhang2013]). This file proves, from the product rule of `Matrix/GaugeODE.lean`, that
the first two are the same thing, and that the BO system gives a DLRA solution.

## Main results

* `tangentProjAt_mul_transpose_apply`: `tangentProjAt (U Zᵀ) A = Π_U A + A Π_Z - Π_U A Π_Z` with
  the Gram projectors `Matrix.colProj` of full-rank factors.
* `hasDerivWithinAt_do_iff`, `hasDerivAt_do_iff`: pointwise, `Ẏ = P(Y) Ad` with the gauge
  `Uᵀ U̇ = 0` iff the DO system, for `Uᵀ U = 1` and `Zᵀ Z` invertible.
* `hasDerivWithinAt_ddo_iff`: the same for the DDO system.
* `doSystem_iff_isDLRASolution`, `ddoSystem_iff_isDLRASolution`: on an interval.
* `isDLRASolution_of_bo`: differentiable BO factors give a DLRA solution. The converse needs
  differentiable eigendecompositions of `Uᵀ U` and is not stated.
* `isDLRASolution_of_factorization`, `IsDLRASolution.hasDerivWithinAt_tangentProj`: relation to
  orthonormal factorizations `Y = Q S Vᵀ` and `tangentProj Q V`.

## Implementation notes

The rank hypothesis (`Zᵀ Z` invertible) places `Y` on the rank-`r` manifold, where
`tangentProjAt` is the tangent projector; the factor hypotheses are required on the closed
interval, because `IsDLRASolution` asks for rank `r` at the endpoint too. In the BO system the
diagonality of `Uᵀ U` only selects the skew matrix `Ω`; the implication to a DLRA solution uses
invertibility of `Uᵀ U` and skew-symmetry of `Ω` only.

## References

* [KochLubich2007] O. Koch, Ch. Lubich, *Dynamical low-rank approximation*.
* [MusharbashNobileZhou2015] E. Musharbash, F. Nobile, T. Zhou, *Error analysis of the
  dynamically orthogonal approximation of time dependent random PDEs*.
* [ChengHouZhang2013] M. Cheng, T. Y. Hou, Z. Zhang, *A dynamically bi-orthogonal method for
  time-dependent stochastic partial differential equations I: Derivation and algorithms*.
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace DynamicallyOrthogonal

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]

/-! ### The tangent projector at a product of full-rank factors -/

private theorem rangeProj_mul_transpose_left {U : Matrix m r ℝ} {Z : Matrix n r ℝ}
    (hU : IsUnit (Uᵀ * U).det) (hZ : IsUnit (Zᵀ * Z).det) : (U * Zᵀ).rangeProj = U.colProj := by
  rw [Matrix.colProj_eq_rangeProj hU]
  refine Matrix.rangeProj_eq_rangeProj_of_mul (C := Zᵀ) (D := Z * (Zᵀ * Z)⁻¹) rfl ?_
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Zᵀ, Matrix.mul_nonsing_inv _ hZ, Matrix.mul_one]

/-- **The column and row projectors of a product of full-rank factors.** For `U`, `Z` of full
column rank, the orthogonal projectors onto the column space and row space of `U Zᵀ` are the Gram
projectors `Matrix.colProj` of `U` and `Z`. -/
theorem rangeProj_mul_transpose {U : Matrix m r ℝ} {Z : Matrix n r ℝ}
    (hU : IsUnit (Uᵀ * U).det) (hZ : IsUnit (Zᵀ * Z).det) :
    (U * Zᵀ).rangeProj = U.colProj ∧ (U * Zᵀ)ᵀ.rangeProj = Z.colProj := by
  refine ⟨rangeProj_mul_transpose_left hU hZ, ?_⟩
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  exact rangeProj_mul_transpose_left hZ hU

/-- **The tangent projector at `Y = U Zᵀ` through full-rank factors**: `P(Y) A = Π_U A + A Π_Z -
Π_U A Π_Z` with `Π_U = U (Uᵀ U)⁻¹ Uᵀ` and `Π_Z = Z (Zᵀ Z)⁻¹ Zᵀ`. -/
theorem tangentProjAt_mul_transpose_apply {U : Matrix m r ℝ} {Z : Matrix n r ℝ}
    (hU : IsUnit (Uᵀ * U).det) (hZ : IsUnit (Zᵀ * Z).det) (A : Matrix m n ℝ) :
    tangentProjAt (U * Zᵀ) A =
      U.colProj * A + A * Z.colProj - U.colProj * A * Z.colProj := by
  rw [tangentProjAt_apply, (rangeProj_mul_transpose hU hZ).1, (rangeProj_mul_transpose hU hZ).2]

/-- The tangent projector commutes with transposition. -/
theorem tangentProjAt_transpose (Y A : Matrix m n ℝ) :
    tangentProjAt Yᵀ Aᵀ = (tangentProjAt Y A)ᵀ := by
  rw [tangentProjAt_apply, tangentProjAt_apply]
  simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_mul,
    Matrix.transpose_rangeProj, Matrix.transpose_transpose, Matrix.mul_assoc]
  abel

/-- A product of full-rank factors has rank `r`. -/
theorem rank_mul_transpose {U : Matrix m r ℝ} {Z : Matrix n r ℝ} (hU : IsUnit (Uᵀ * U).det)
    (hZ : IsUnit (Zᵀ * Z).det) : (U * Zᵀ).rank = Fintype.card r := by
  refine le_antisymm ((Matrix.rank_mul_le_left _ _).trans U.rank_le_card_width) ?_
  have h : U.gramPinv * (U * Zᵀ) * (Z * (Zᵀ * Z)⁻¹) = 1 := by
    rw [← Matrix.mul_assoc U.gramPinv U Zᵀ, Matrix.gramPinv_mul_self hU, Matrix.one_mul,
      ← Matrix.mul_assoc Zᵀ Z, Matrix.mul_nonsing_inv _ hZ]
  calc Fintype.card r = (1 : Matrix r r ℝ).rank := Matrix.rank_one.symm
    _ = (U.gramPinv * (U * Zᵀ) * (Z * (Zᵀ * Z)⁻¹)).rank := by rw [h]
    _ ≤ (U.gramPinv * (U * Zᵀ)).rank := Matrix.rank_mul_le_left _ _
    _ ≤ (U * Zᵀ).rank := Matrix.rank_mul_le_right _ _


/-! ### The dynamically orthogonal system -/

theorem do_algebra [DecidableEq m] {U U' : Matrix m r ℝ} {Z Z' : Matrix n r ℝ}
    {Ad : Matrix m n ℝ} (hU : Uᵀ * U = 1) (hG : IsUnit (Zᵀ * Z).det) :
    (U' * Zᵀ + U * Z'ᵀ = U.colProj * Ad + Ad * Z.colProj - U.colProj * Ad * Z.colProj ∧
        Uᵀ * U' = 0) ↔
      (Uᵀ * U' = 0 ∧ Z' = Adᵀ * U ∧ U' * (Zᵀ * Z) = (1 - U * Uᵀ) * Ad * Z) := by
  have hZ : Z.colProj * Z = Z := Matrix.colProj_mul_self hG
  constructor
  · rintro ⟨h, hg⟩
    have h1 : Z'ᵀ = Uᵀ * Ad := by
      have := congrArg (Uᵀ * ·) h
      simp only [Matrix.mul_add, Matrix.colProj_eq_mul_transpose hU, Matrix.mul_sub,
        ← Matrix.mul_assoc, hU, hg, Matrix.one_mul, Matrix.zero_mul, zero_add] at this
      rw [this]
      abel
    have h2 : Z' = Adᵀ * U := by
      have := congrArg Matrix.transpose h1
      simpa [Matrix.transpose_mul] using this
    refine ⟨hg, h2, ?_⟩
    have h3 : U' * Zᵀ = (1 - U * Uᵀ) * Ad * Z.colProj := by
      rw [eq_sub_of_add_eq h, h1, Matrix.colProj_eq_mul_transpose hU]
      simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      abel
    calc U' * (Zᵀ * Z) = (U' * Zᵀ) * Z := (Matrix.mul_assoc _ _ _).symm
      _ = (1 - U * Uᵀ) * Ad * Z.colProj * Z := by rw [h3]
      _ = _ := by rw [Matrix.mul_assoc _ Z.colProj, hZ]
  · rintro ⟨hg, h2, h3⟩
    refine ⟨?_, hg⟩
    have h4 : U' * Zᵀ = (1 - U * Uᵀ) * Ad * Z.colProj := by
      have : U' = (1 - U * Uᵀ) * Ad * Z * (Zᵀ * Z)⁻¹ := by
        rw [← h3, Matrix.mul_nonsing_inv_cancel_right _ _ hG]
      rw [this, Matrix.colProj_def]
      simp only [Matrix.mul_assoc]
    rw [h4, h2, Matrix.colProj_eq_mul_transpose hU, Matrix.transpose_mul,
      Matrix.transpose_transpose]
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    abel

open GaugeODE in
/-- **The dynamically orthogonal (DO) system, pointwise.** Let `U`, `Z` be differentiable at `t`
within a set on which derivatives are unique, with `Uᵀ U = 1` and `Zᵀ Z` invertible at `t`, and
let `Ad` stand for `F(t, Y(t))`. Then `Y = U Zᵀ` satisfies `Ẏ = P(Y) Ad` together with the gauge
`Uᵀ U̇ = 0` if and only if the DO system holds: `Uᵀ U̇ = 0`, `Ż = Adᵀ U` and
`U̇ (Zᵀ Z) = (1 - U Uᵀ) Ad Z` ([KochLubich2007]; [MusharbashNobileZhou2015]). The rank
hypothesis on `Z` says that `Y` lies on the rank-`r` manifold, where `P(Y)` is defined. -/
theorem hasDerivWithinAt_do_iff [DecidableEq m] {U : ℝ → Matrix m r ℝ} {Z : ℝ → Matrix n r ℝ}
    {U' : Matrix m r ℝ} {Z' : Matrix n r ℝ} {Ad : Matrix m n ℝ} {S : Set ℝ} {t : ℝ}
    (hs : UniqueDiffWithinAt ℝ S t) (hU : HasDerivWithinAt U U' S t)
    (hZ : HasDerivWithinAt Z Z' S t) (hUo : (U t)ᵀ * U t = 1)
    (hG : IsUnit ((Z t)ᵀ * Z t).det) :
    (HasDerivWithinAt (fun t => U t * (Z t)ᵀ) (tangentProjAt (U t * (Z t)ᵀ) Ad) S t ∧
        (U t)ᵀ * U' = 0) ↔
      ((U t)ᵀ * U' = 0 ∧ Z' = Adᵀ * U t ∧
        U' * ((Z t)ᵀ * Z t) = (1 - U t * (U t)ᵀ) * Ad * Z t) := by
  have hY := hasDerivWithinAt_mul hU (hasDerivWithinAt_transpose hZ)
  have hUg : IsUnit ((U t)ᵀ * U t).det := by rw [hUo]; simp
  rw [← do_algebra hUo hG, tangentProjAt_mul_transpose_apply hUg hG]
  constructor
  · rintro ⟨h, hg⟩
    exact ⟨hs.eq_deriv _ hY h, hg⟩
  · rintro ⟨h, hg⟩
    exact ⟨by rw [← h]; exact hY, hg⟩

open GaugeODE in
/-- Two-sided version of `hasDerivWithinAt_do_iff`. -/
theorem hasDerivAt_do_iff [DecidableEq m] {U : ℝ → Matrix m r ℝ} {Z : ℝ → Matrix n r ℝ}
    {U' : Matrix m r ℝ} {Z' : Matrix n r ℝ} {Ad : Matrix m n ℝ} {t : ℝ}
    (hU : HasDerivAt U U' t) (hZ : HasDerivAt Z Z' t) (hUo : (U t)ᵀ * U t = 1)
    (hG : IsUnit ((Z t)ᵀ * Z t).det) :
    (HasDerivAt (fun t => U t * (Z t)ᵀ) (tangentProjAt (U t * (Z t)ᵀ) Ad) t ∧
        (U t)ᵀ * U' = 0) ↔
      ((U t)ᵀ * U' = 0 ∧ Z' = Adᵀ * U t ∧
        U' * ((Z t)ᵀ * Z t) = (1 - U t * (U t)ᵀ) * Ad * Z t) := by
  simpa only [hasDerivWithinAt_univ] using hasDerivWithinAt_do_iff uniqueDiffWithinAt_univ
    (hasDerivWithinAt_univ.mpr hU) (hasDerivWithinAt_univ.mpr hZ) hUo hG

open GaugeODE in
theorem hasDerivWithinAt_transpose_iff {Y : ℝ → Matrix m n ℝ} {Y' : Matrix m n ℝ} {S : Set ℝ}
    {t : ℝ} : HasDerivWithinAt (fun t => (Y t)ᵀ) Y'ᵀ S t ↔ HasDerivWithinAt Y Y' S t := by
  refine ⟨fun h => ?_, hasDerivWithinAt_transpose⟩
  have h2 := hasDerivWithinAt_transpose h
  simp only [Matrix.transpose_transpose] at h2
  exact h2

/-- **The dual dynamically orthogonal (DDO) system, pointwise** (the transposed statement of
`hasDerivWithinAt_do_iff`): for `Y = Z Vᵀ` with `Vᵀ V = 1` and `Zᵀ Z` invertible,
`Ẏ = P(Y) Ad` with the gauge `Vᵀ V̇ = 0` holds if and only if `Vᵀ V̇ = 0`, `Ż = Ad V` and
`V̇ (Zᵀ Z) = (1 - V Vᵀ) Adᵀ Z`. -/
theorem hasDerivWithinAt_ddo_iff [DecidableEq n] {Z : ℝ → Matrix m r ℝ} {V : ℝ → Matrix n r ℝ}
    {Z' : Matrix m r ℝ} {V' : Matrix n r ℝ} {Ad : Matrix m n ℝ} {S : Set ℝ} {t : ℝ}
    (hs : UniqueDiffWithinAt ℝ S t) (hZ : HasDerivWithinAt Z Z' S t)
    (hV : HasDerivWithinAt V V' S t) (hVo : (V t)ᵀ * V t = 1)
    (hG : IsUnit ((Z t)ᵀ * Z t).det) :
    (HasDerivWithinAt (fun t => Z t * (V t)ᵀ) (tangentProjAt (Z t * (V t)ᵀ) Ad) S t ∧
        (V t)ᵀ * V' = 0) ↔
      ((V t)ᵀ * V' = 0 ∧ Z' = Ad * V t ∧
        V' * ((Z t)ᵀ * Z t) = (1 - V t * (V t)ᵀ) * Adᵀ * Z t) := by
  have h := hasDerivWithinAt_do_iff (Ad := Adᵀ) hs hV hZ hVo hG
  have e : HasDerivWithinAt (fun t => Z t * (V t)ᵀ) (tangentProjAt (Z t * (V t)ᵀ) Ad) S t ↔
      HasDerivWithinAt (fun t => V t * (Z t)ᵀ) (tangentProjAt (V t * (Z t)ᵀ) Adᵀ) S t := by
    have e2 : tangentProjAt (V t * (Z t)ᵀ) Adᵀ = (tangentProjAt (Z t * (V t)ᵀ) Ad)ᵀ := by
      have := tangentProjAt_transpose (Z t * (V t)ᵀ) Ad
      rwa [Matrix.transpose_mul, Matrix.transpose_transpose] at this
    rw [e2, ← hasDerivWithinAt_transpose_iff]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [e]
  simpa only [Matrix.transpose_transpose] using h

/-! ### The bi-orthogonal system -/

theorem bo_algebra [DecidableEq n] {U U' : Matrix m r ℝ} {Z Z' : Matrix n r ℝ}
    {Ω : Matrix r r ℝ} {Ad : Matrix m n ℝ} (hZo : Zᵀ * Z = 1) (hΩ : Ωᵀ = -Ω)
    (hU' : U' = Ad * Z + U * Ω)
    (hZ' : Z' = Z * Ω + (1 - Z * Zᵀ) * Adᵀ * U * (Uᵀ * U)⁻¹) :
    U' * Zᵀ + U * Z'ᵀ = U.colProj * Ad + Ad * Z.colProj - U.colProj * Ad * Z.colProj := by
  have hDs : ((Uᵀ * U)⁻¹)ᵀ = (Uᵀ * U)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [hU', hZ', Matrix.colProj_eq_mul_transpose hZo, Matrix.colProj_def U]
  simp only [Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_sub,
    Matrix.transpose_one, Matrix.transpose_transpose, hΩ, hDs]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.mul_one, Matrix.mul_assoc]
  abel

open GaugeODE in
/-- **The bi-orthogonal (BO) system gives a DLRA solution, pointwise.** Let `U`, `Z` be
differentiable at `t` within `S` with `Zᵀ Z = 1` and `Uᵀ U` invertible, and let `Ω` be
skew-symmetric. If `U̇ = Ad Z + U Ω` and `Ż = Z Ω + (1 - Z Zᵀ) Adᵀ U (Uᵀ U)⁻¹`, then `Y = U Zᵀ`
satisfies `Ẏ = P(Y) Ad`. Diagonality of `Uᵀ U` is not used: in the BO formulation it only selects
the skew matrix `Ω` ([ChengHouZhang2013]; [MusharbashNobileZhou2015]). -/
theorem hasDerivWithinAt_tangentProjAt_of_bo [DecidableEq n] {U : ℝ → Matrix m r ℝ}
    {Z : ℝ → Matrix n r ℝ} {U' : Matrix m r ℝ} {Z' : Matrix n r ℝ} {Ω : Matrix r r ℝ}
    {Ad : Matrix m n ℝ} {S : Set ℝ} {t : ℝ} (hU : HasDerivWithinAt U U' S t)
    (hZ : HasDerivWithinAt Z Z' S t) (hZo : (Z t)ᵀ * Z t = 1)
    (hD : IsUnit ((U t)ᵀ * U t).det) (hΩ : Ωᵀ = -Ω) (hU' : U' = Ad * Z t + U t * Ω)
    (hZ' : Z' = Z t * Ω + (1 - Z t * (Z t)ᵀ) * Adᵀ * U t * ((U t)ᵀ * U t)⁻¹) :
    HasDerivWithinAt (fun t => U t * (Z t)ᵀ) (tangentProjAt (U t * (Z t)ᵀ) Ad) S t := by
  have hY := hasDerivWithinAt_mul hU (hasDerivWithinAt_transpose hZ)
  have hZg : IsUnit ((Z t)ᵀ * Z t).det := by rw [hZo]; simp
  rw [tangentProjAt_mul_transpose_apply hD hZg, ← bo_algebra hZo hΩ hU' hZ']
  exact hY

/-! ### DLRA solutions through factors -/

/-- **DLRA solutions of rank `r` through full-rank factors.** If `Y t = U t (Z t)ᵀ` with `U t`,
`Z t` of full column rank on `[a, b]`, then `Y` is a DLRA solution of rank `r` if and only if it
is continuous on `[a, b]` and has right derivative `tangentProjAt (Y t) (F t (Y t))` on
`[a, b)`: the rank condition is automatic. -/
theorem isDLRASolution_iff_hasDerivWithinAt {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {a b : ℝ} {U : ℝ → Matrix m (Fin r) ℝ} {Z : ℝ → Matrix n (Fin r) ℝ}
    (hUG : ∀ t ∈ Icc a b, IsUnit ((U t)ᵀ * U t).det)
    (hZG : ∀ t ∈ Icc a b, IsUnit ((Z t)ᵀ * Z t).det) :
    IsDLRASolution r F (fun t => U t * (Z t)ᵀ) a b ↔
      ContinuousOn (fun t => U t * (Z t)ᵀ) (Icc a b) ∧ ∀ t ∈ Ico a b,
        HasDerivWithinAt (fun t => U t * (Z t)ᵀ)
          (tangentProjAt (U t * (Z t)ᵀ) (F t (U t * (Z t)ᵀ))) (Ici t) t := by
  have hrank : ∀ t ∈ Icc a b, (U t * (Z t)ᵀ).rank = r := fun t ht => by
    simpa using rank_mul_transpose (hUG t ht) (hZG t ht)
  constructor
  · rintro ⟨⟨hc, hd⟩, -⟩
    exact ⟨hc, hd⟩
  · rintro ⟨hc, hd⟩
    exact ⟨⟨hc, hd⟩, hrank⟩

/-- A DLRA solution has right derivative `tangentProj Q V (F t (Y t))` for every orthonormal
factorization `Y t = Q S Vᵀ` with invertible `S`. -/
theorem IsDLRASolution.hasDerivWithinAt_tangentProj {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {Y : ℝ → Matrix m n ℝ} {a b t : ℝ}
    (h : IsDLRASolution r F Y a b) (ht : t ∈ Ico a b) {Q : Matrix m (Fin r) ℝ}
    {S : Matrix (Fin r) (Fin r) ℝ} {V : Matrix n (Fin r) ℝ} (hQ : Qᵀ * Q = 1) (hV : Vᵀ * V = 1)
    (hS : IsUnit S.det) (hY : Y t = Q * S * Vᵀ) :
    HasDerivWithinAt Y (tangentProj Q V (F t (Y t))) (Ici t) t := by
  have h1 := h.1.deriv t ht
  rw [hY, tangentProjAt_eq_tangentProj hQ hV hS] at h1
  rwa [hY]

/-- **DLRA solutions through orthonormal factorizations.** If `Y` is continuous, has rank `r` at
`b`, and at every `t ∈ [a, b)` is `Q S Vᵀ` with orthonormal `Q`, `V`, invertible `S` and right
derivative `tangentProj Q V (F t (Y t))`, then `Y` is a DLRA solution of rank `r`. -/
theorem isDLRASolution_of_factorization {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {Y : ℝ → Matrix m n ℝ} {a b : ℝ} (hc : ContinuousOn Y (Icc a b)) (hb : (Y b).rank = r)
    (h : ∀ t ∈ Ico a b, ∃ (Q : Matrix m (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ)
      (V : Matrix n (Fin r) ℝ), Qᵀ * Q = 1 ∧ Vᵀ * V = 1 ∧ IsUnit S.det ∧ Y t = Q * S * Vᵀ ∧
        HasDerivWithinAt Y (tangentProj Q V (F t (Y t))) (Ici t) t) :
    IsDLRASolution r F Y a b := by
  refine ⟨⟨hc, fun t ht => ?_⟩, fun t ht => ?_⟩
  · obtain ⟨Q, S, V, hQ, hV, hS, hY, hd⟩ := h t ht
    rwa [hY, tangentProjAt_eq_tangentProj hQ hV hS, ← hY]
  · rcases ht.2.eq_or_lt with rfl | hlt
    · exact hb
    · obtain ⟨Q, S, V, hQ, hV, hS, hY, -⟩ := h t ⟨ht.1, hlt⟩
      have hST : IsUnit (Sᵀ).det := by rwa [Matrix.det_transpose]
      have hQg : IsUnit (Qᵀ * Q).det := by rw [hQ]; simp
      have hW : IsUnit ((V * Sᵀ)ᵀ * (V * Sᵀ)).det := by
        have e : (V * Sᵀ)ᵀ * (V * Sᵀ) = S * Sᵀ := by
          simp [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ V, hV]
        rw [e, Matrix.det_mul]
        exact hS.mul hST
      have e2 : Y t = Q * (V * Sᵀ)ᵀ := by
        rw [hY, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      rw [e2]
      simpa using rank_mul_transpose hQg hW

/-! ### Trajectory statements -/

/-- **DO formulation ⇔ DLRA solution with the gauge.** Let `U`, `Z` be continuous on `[a, b]`
with right derivatives `U̇`, `Ż` on `[a, b)`, `Uᵀ U = 1` and `Zᵀ Z` invertible on `[a, b]`. Then
the DO system `Uᵀ U̇ = 0`, `Ż = (F(t, Y))ᵀ U`, `U̇ (Zᵀ Z) = (1 - U Uᵀ) F(t, Y) Z` for `Y = U Zᵀ`
holds on `[a, b)` if and only if `Y` is a DLRA solution of rank `r` and satisfies the gauge
`Uᵀ U̇ = 0`. -/
theorem doSystem_iff_isDLRASolution [DecidableEq m] {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {a b : ℝ} {U U' : ℝ → Matrix m (Fin r) ℝ}
    {Z Z' : ℝ → Matrix n (Fin r) ℝ} (hUc : ContinuousOn U (Icc a b))
    (hZc : ContinuousOn Z (Icc a b)) (hU : ∀ t ∈ Ico a b, HasDerivWithinAt U (U' t) (Ici t) t)
    (hZ : ∀ t ∈ Ico a b, HasDerivWithinAt Z (Z' t) (Ici t) t)
    (hUo : ∀ t ∈ Icc a b, (U t)ᵀ * U t = 1) (hG : ∀ t ∈ Icc a b, IsUnit ((Z t)ᵀ * Z t).det) :
    (∀ t ∈ Ico a b, (U t)ᵀ * U' t = 0 ∧ Z' t = (F t (U t * (Z t)ᵀ))ᵀ * U t ∧
        U' t * ((Z t)ᵀ * Z t) = (1 - U t * (U t)ᵀ) * F t (U t * (Z t)ᵀ) * Z t) ↔
      IsDLRASolution r F (fun t => U t * (Z t)ᵀ) a b ∧ ∀ t ∈ Ico a b, (U t)ᵀ * U' t = 0 := by
  have hUG : ∀ t ∈ Icc a b, IsUnit ((U t)ᵀ * U t).det := fun t ht => by rw [hUo t ht]; simp
  rw [isDLRASolution_iff_hasDerivWithinAt hUG hG]
  have hc : ContinuousOn (fun t => U t * (Z t)ᵀ) (Icc a b) :=
    GaugeODE.continuousOn_mul hUc (GaugeODE.continuousOn_transpose hZc)
  constructor
  · intro h
    refine ⟨⟨hc, fun t ht => ?_⟩, fun t ht => (h t ht).1⟩
    exact ((hasDerivWithinAt_do_iff (uniqueDiffWithinAt_Ici t) (hU t ht) (hZ t ht)
      (hUo t (Ico_subset_Icc_self ht)) (hG t (Ico_subset_Icc_self ht))).mpr (h t ht)).1
  · rintro ⟨⟨-, h⟩, hg⟩ t ht
    exact (hasDerivWithinAt_do_iff (uniqueDiffWithinAt_Ici t) (hU t ht) (hZ t ht)
      (hUo t (Ico_subset_Icc_self ht)) (hG t (Ico_subset_Icc_self ht))).mp ⟨h t ht, hg t ht⟩

/-- **DDO formulation ⇔ DLRA solution with the gauge** (the mirror of
`doSystem_iff_isDLRASolution`): for `Y = Z Vᵀ` with `Vᵀ V = 1` and `Zᵀ Z` invertible on
`[a, b]`, the DDO system `Vᵀ V̇ = 0`, `Ż = F(t, Y) V`, `V̇ (Zᵀ Z) = (1 - V Vᵀ) F(t, Y)ᵀ Z` holds on
`[a, b)` if and only if `Y` is a DLRA solution of rank `r` with `Vᵀ V̇ = 0`. -/
theorem ddoSystem_iff_isDLRASolution [DecidableEq n] {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {a b : ℝ} {Z Z' : ℝ → Matrix m (Fin r) ℝ}
    {V V' : ℝ → Matrix n (Fin r) ℝ} (hZc : ContinuousOn Z (Icc a b))
    (hVc : ContinuousOn V (Icc a b)) (hZ : ∀ t ∈ Ico a b, HasDerivWithinAt Z (Z' t) (Ici t) t)
    (hV : ∀ t ∈ Ico a b, HasDerivWithinAt V (V' t) (Ici t) t)
    (hVo : ∀ t ∈ Icc a b, (V t)ᵀ * V t = 1) (hG : ∀ t ∈ Icc a b, IsUnit ((Z t)ᵀ * Z t).det) :
    (∀ t ∈ Ico a b, (V t)ᵀ * V' t = 0 ∧ Z' t = F t (Z t * (V t)ᵀ) * V t ∧
        V' t * ((Z t)ᵀ * Z t) = (1 - V t * (V t)ᵀ) * (F t (Z t * (V t)ᵀ))ᵀ * Z t) ↔
      IsDLRASolution r F (fun t => Z t * (V t)ᵀ) a b ∧ ∀ t ∈ Ico a b, (V t)ᵀ * V' t = 0 := by
  have hVG : ∀ t ∈ Icc a b, IsUnit ((V t)ᵀ * V t).det := fun t ht => by rw [hVo t ht]; simp
  rw [isDLRASolution_iff_hasDerivWithinAt hG hVG]
  have hc : ContinuousOn (fun t => Z t * (V t)ᵀ) (Icc a b) :=
    GaugeODE.continuousOn_mul hZc (GaugeODE.continuousOn_transpose hVc)
  constructor
  · intro h
    refine ⟨⟨hc, fun t ht => ?_⟩, fun t ht => (h t ht).1⟩
    exact ((hasDerivWithinAt_ddo_iff (uniqueDiffWithinAt_Ici t) (hZ t ht) (hV t ht)
      (hVo t (Ico_subset_Icc_self ht)) (hG t (Ico_subset_Icc_self ht))).mpr (h t ht)).1
  · rintro ⟨⟨-, h⟩, hg⟩ t ht
    exact (hasDerivWithinAt_ddo_iff (uniqueDiffWithinAt_Ici t) (hZ t ht) (hV t ht)
      (hVo t (Ico_subset_Icc_self ht)) (hG t (Ico_subset_Icc_self ht))).mp ⟨h t ht, hg t ht⟩

/-- **Differentiable bi-orthogonal factors give a DLRA solution.** Let `U`, `Z` be continuous on
`[a, b]` with right derivatives `U̇`, `Ż` on `[a, b)`, `Zᵀ Z = 1` and `Uᵀ U` invertible on
`[a, b]`, and let `Ω t` be skew-symmetric with `U̇ = F(t, Y) Z + U Ω` and
`Ż = Z Ω + (1 - Z Zᵀ) F(t, Y)ᵀ U (Uᵀ U)⁻¹` for `Y = U Zᵀ`. Then `Y` is a DLRA solution of
rank `r`. The converse needs differentiable eigendecompositions of `Uᵀ U` and is not stated. -/
theorem isDLRASolution_of_bo [DecidableEq n] {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {a b : ℝ} {U U' : ℝ → Matrix m (Fin r) ℝ} {Z Z' : ℝ → Matrix n (Fin r) ℝ}
    {Ω : ℝ → Matrix (Fin r) (Fin r) ℝ} (hUc : ContinuousOn U (Icc a b))
    (hZc : ContinuousOn Z (Icc a b)) (hU : ∀ t ∈ Ico a b, HasDerivWithinAt U (U' t) (Ici t) t)
    (hZ : ∀ t ∈ Ico a b, HasDerivWithinAt Z (Z' t) (Ici t) t)
    (hZo : ∀ t ∈ Icc a b, (Z t)ᵀ * Z t = 1) (hD : ∀ t ∈ Icc a b, IsUnit ((U t)ᵀ * U t).det)
    (hΩ : ∀ t ∈ Ico a b, (Ω t)ᵀ = -Ω t)
    (hU' : ∀ t ∈ Ico a b, U' t = F t (U t * (Z t)ᵀ) * Z t + U t * Ω t)
    (hZ' : ∀ t ∈ Ico a b, Z' t = Z t * Ω t +
      (1 - Z t * (Z t)ᵀ) * (F t (U t * (Z t)ᵀ))ᵀ * U t * ((U t)ᵀ * U t)⁻¹) :
    IsDLRASolution r F (fun t => U t * (Z t)ᵀ) a b := by
  have hZG : ∀ t ∈ Icc a b, IsUnit ((Z t)ᵀ * Z t).det := fun t ht => by rw [hZo t ht]; simp
  rw [isDLRASolution_iff_hasDerivWithinAt hD hZG]
  exact ⟨GaugeODE.continuousOn_mul hUc (GaugeODE.continuousOn_transpose hZc), fun t ht =>
    hasDerivWithinAt_tangentProjAt_of_bo (hU t ht) (hZ t ht) (hZo t (Ico_subset_Icc_self ht))
      (hD t (Ico_subset_Icc_self ht)) (hΩ t ht) (hU' t ht) (hZ' t ht)⟩

/-! ### Non-vacuity examples -/

section Examples

open GaugeODEExample

private theorem smul_one_gram (c : ℝ) :
    (c • (1 : Matrix (Fin 1) (Fin 1) ℝ))ᵀ * (c • 1) = (c * c) • 1 := by
  simp [Matrix.transpose_smul, smul_smul]

private theorem isUnit_det_smul_one {c : ℝ} (hc : c ≠ 0) :
    IsUnit (c • (1 : Matrix (Fin 1) (Fin 1) ℝ)).det := by
  rw [isUnit_iff_ne_zero]
  simpa [Matrix.det_smul] using hc

/-- The DO system holds along the rotating example of `GaugeODEExample` (`U` moves, `U̇ ≠ 0`,
`Z = e^t e₁`, field `F(t, Y) = Ȧ(t)`), hence `U Zᵀ` is a DLRA solution with the gauge. -/
example : IsDLRASolution 1 (fun t (_ : Matrix (Fin 2) (Fin 2) ℝ) => Adf t)
    (fun t => Uf t * (Real.exp t • V0)ᵀ) 0 1 ∧ ∀ t ∈ Ico (0 : ℝ) 1, (Uf t)ᵀ * Ud t = 0 := by
  have hZ : ∀ t, HasDerivAt (fun t => Real.exp t • V0) (Real.exp t • V0) t := fun t =>
    (Real.hasDerivAt_exp t).smul_const V0
  have hUdt : ∀ t, (Ud t)ᵀ * Uf t = 0 := fun t => by
    have := congrArg Matrix.transpose (gauge_Uf t)
    simpa [Matrix.transpose_mul] using this
  have hgram : ∀ t, (Real.exp t • V0)ᵀ * (Real.exp t • V0) =
      (Real.exp t * Real.exp t) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := fun t => by
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, orthonormal_V0, smul_smul]
  refine (doSystem_iff_isDLRASolution (F := fun t _ => Adf t) (U' := Ud)
    (Z' := fun t => Real.exp t • V0) (a := 0) (b := 1)
    (fun t _ => (hasDerivAt_Uf t).continuousAt.continuousWithinAt)
    (fun t _ => (hZ t).continuousAt.continuousWithinAt)
    (fun t _ => (hasDerivAt_Uf t).hasDerivWithinAt) (fun t _ => (hZ t).hasDerivWithinAt)
    (fun t _ => orthonormal_Uf t) (fun t _ => ?_)).mp (fun t _ => ⟨gauge_Uf t, ?_, ?_⟩)
  · rw [hgram]
    exact isUnit_det_smul_one (mul_pos (Real.exp_pos t) (Real.exp_pos t)).ne'
  · have h2 : (Uf t + Ud t)ᵀ * Uf t = 1 := by
      rw [Matrix.transpose_add, Matrix.add_mul, orthonormal_Uf t, hUdt t, add_zero]
    simp only [Adf]
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc, h2, Matrix.mul_one]
  · have h3 : (1 - Uf t * (Uf t)ᵀ) * (Uf t + Ud t) = Ud t := by
      simp [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_assoc, orthonormal_Uf t, gauge_Uf t]
    simp only [Adf]
    have h4 : (1 - Uf t * (Uf t)ᵀ) * (Real.exp t • ((Uf t + Ud t) * V0ᵀ)) * (Real.exp t • V0) =
        (Real.exp t * Real.exp t) • ((1 - Uf t * (Uf t)ᵀ) * (Uf t + Ud t)) := by
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc, orthonormal_V0,
        Matrix.mul_one]
    rw [hgram, h4, h3, Matrix.mul_smul, Matrix.mul_one]

/-- The BO system holds for `U = e^t`, `Z = 1`, `Ω = 0` and `F(t, Y) = Y` (`1 × 1` matrices), so
`U Zᵀ` is a DLRA solution of rank one. -/
example : IsDLRASolution 1 (fun _ (Y : Matrix (Fin 1) (Fin 1) ℝ) => Y)
    (fun t => (Real.exp t • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ)
    0 1 := by
  have hU : ∀ t, HasDerivAt (fun t => Real.exp t • (1 : Matrix (Fin 1) (Fin 1) ℝ))
      (Real.exp t • 1) t := fun t => (Real.hasDerivAt_exp t).smul_const 1
  refine isDLRASolution_of_bo (U := fun t => Real.exp t • 1) (U' := fun t => Real.exp t • 1)
    (Z := fun _ => 1) (Z' := fun _ => 0) (Ω := fun _ => 0)
    (fun t _ => (hU t).continuousAt.continuousWithinAt) continuousOn_const
    (fun t _ => (hU t).hasDerivWithinAt) (fun t _ => hasDerivWithinAt_const t _ _)
    (fun _ _ => by simp) (fun t _ => ?_) (fun _ _ => by simp) (fun _ _ => by simp)
    (fun _ _ => by simp)
  rw [smul_one_gram]
  exact isUnit_det_smul_one (mul_pos (Real.exp_pos t) (Real.exp_pos t)).ne'

/-- The DDO system holds for `Z = e^t`, `V = 1` and `F(t, Y) = Y` (`1 × 1` matrices), so
`Z Vᵀ` is a DLRA solution of rank one. -/
example : IsDLRASolution 1 (fun _ (Y : Matrix (Fin 1) (Fin 1) ℝ) => Y)
    (fun t => (Real.exp t • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ)
    0 1 := by
  have hZ : ∀ t, HasDerivAt (fun t => Real.exp t • (1 : Matrix (Fin 1) (Fin 1) ℝ))
      (Real.exp t • 1) t := fun t => (Real.hasDerivAt_exp t).smul_const 1
  refine ((ddoSystem_iff_isDLRASolution (F := fun _ (Y : Matrix (Fin 1) (Fin 1) ℝ) => Y)
    (Z := fun t => Real.exp t • 1) (Z' := fun t => Real.exp t • 1) (V := fun _ => 1)
    (V' := fun _ => 0) (a := 0) (b := 1)
    (fun t _ => (hZ t).continuousAt.continuousWithinAt) continuousOn_const
    (fun t _ => (hZ t).hasDerivWithinAt) (fun t _ => hasDerivWithinAt_const t _ _)
    (fun _ _ => by simp) (fun t _ => ?_)).mp (fun _ _ => ⟨by simp, by simp, by simp⟩)).1
  rw [smul_one_gram]
  exact isUnit_det_smul_one (mul_pos (Real.exp_pos t) (Real.exp_pos t)).ne'

end Examples

end DynamicallyOrthogonal

end LeanDLRA
