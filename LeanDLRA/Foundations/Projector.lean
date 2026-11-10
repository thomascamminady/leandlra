import Mathlib
import LeanDLRA.LinearAlgebra.Projection.Defs
import LeanDLRA.FixedRank.Defs

/-!
# Orthogonal projectors and the tangent-space operator calculus

Every robust integrator for dynamical low-rank approximation is built from the left projector
`P_U A = U Uᵀ A` and the right projector `P_V A = A V Vᵀ`.  On the space of matrices with the
Frobenius inner product these are *commuting orthogonal projectors*.  Almost every algebraic fact
in the DLRA literature is a statement about such a pair, so we prove them here once, for arbitrary
real inner product spaces.

The central objects are

* `tangent L R = L + R - L * R`, abstracting `P(Y) G = U Uᵀ G - U Uᵀ G V Vᵀ + G V Vᵀ`;
* `normal L R = (1 - L) * (1 - R)`, abstracting `(I - U Uᵀ) G (I - V Vᵀ)`.

The predicate `IsOrthProj` is defined in `LeanDLRA/LinearAlgebra/Projection/Defs.lean`, and
`tangent`, `normal` with their `_apply` lemmas in `LeanDLRA/FixedRank/Defs.lean`.
-/

open scoped RealInnerProductSpace

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The tangent and normal projectors always add up to the identity. -/
lemma tangent_add_normal (L R : E →L[ℝ] E) : tangent L R + normal L R = 1 := by
  ext x
  change tangent L R x + normal L R x = x
  simp only [tangent_apply, normal_apply, map_sub]
  abel

/-- The normal projector is the complement of the tangent projector. -/
lemma normal_eq_one_sub_tangent (L R : E →L[ℝ] E) : normal L R = 1 - tangent L R := by
  rw [← tangent_add_normal L R]; abel

/-- Pointwise form of `tangent_add_normal`: `tangent L R x + normal L R x = x`. -/
lemma tangent_apply_add_normal_apply (L R : E →L[ℝ] E) (x : E) :
    tangent L R x + normal L R x = x := by
  simp only [tangent_apply, normal_apply, map_sub]
  abel

namespace IsOrthProj

variable {P Q L R : E →L[ℝ] E}

/-- Idempotence as an equation of operators: `P * P = P`. -/
lemma idem' (hP : IsOrthProj P) : P * P = P := by
  ext x; simpa using hP.idem x

/-- `⟪P x, P y⟫ = ⟪P x, y⟫` for an orthogonal projector. -/
lemma inner_comp (hP : IsOrthProj P) (x y : E) : ⟪P x, P y⟫ = ⟪P x, y⟫ := by
  rw [← hP.symm, hP.idem]

/-- `⟪P x, x⟫ = ‖P x‖²` for an orthogonal projector. -/
lemma inner_self_apply (hP : IsOrthProj P) (x : E) : ⟪P x, x⟫ = ‖P x‖ ^ 2 := by
  rw [← hP.inner_comp, real_inner_self_eq_norm_sq]

/-- The range of `P` is orthogonal to the residual: `⟪P x, y - P y⟫ = 0`. -/
lemma inner_sub_self (hP : IsOrthProj P) (x y : E) : ⟪P x, y - P y⟫ = 0 := by
  rw [inner_sub_right, hP.inner_comp, sub_self]

/-- Pythagoras for an orthogonal projector. -/
lemma norm_sq_add (hP : IsOrthProj P) (x : E) : ‖P x‖ ^ 2 + ‖x - P x‖ ^ 2 = ‖x‖ ^ 2 := by
  have h := norm_add_sq_real (P x) (x - P x)
  rw [hP.inner_sub_self, add_sub_cancel] at h
  linarith

/-- An orthogonal projector does not increase the norm: `‖P x‖ ≤ ‖x‖`. -/
lemma norm_le (hP : IsOrthProj P) (x : E) : ‖P x‖ ≤ ‖x‖ := by
  have h := hP.norm_sq_add x
  have h2 : 0 ≤ ‖x - P x‖ ^ 2 := by positivity
  exact abs_le_of_sq_le_sq' (by nlinarith) (norm_nonneg x) |>.2

/-- The residual is no longer than the vector: `‖x - P x‖ ≤ ‖x‖`. -/
lemma norm_sub_le (hP : IsOrthProj P) (x : E) : ‖x - P x‖ ≤ ‖x‖ := by
  have h := hP.norm_sq_add x
  have h2 : 0 ≤ ‖P x‖ ^ 2 := by positivity
  exact abs_le_of_sq_le_sq' (by nlinarith) (norm_nonneg x) |>.2

/-- An orthogonal projector has operator norm at most one. -/
lemma opNorm_le (hP : IsOrthProj P) : ‖P‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simpa using hP.norm_le x

/-- Best-approximation property: `P x` is the closest point to `x` in the range of `P`. -/
lemma norm_sub_le_of_mem_range (hP : IsOrthProj P) (x y : E) (hy : P y = y) :
    ‖x - P x‖ ≤ ‖x - y‖ := by
  have hdecomp : x - y = (x - P x) + P (x - y) := by
    rw [map_sub, hy]; abel
  have horth : ⟪x - P x, P (x - y)⟫ = 0 := by
    rw [real_inner_comm, hP.inner_sub_self]
  have h := norm_add_sq_real (x - P x) (P (x - y))
  rw [horth, ← hdecomp] at h
  have h2 : 0 ≤ ‖P (x - y)‖ ^ 2 := by positivity
  exact abs_le_of_sq_le_sq' (by nlinarith) (norm_nonneg _) |>.2

/-- The complementary projector. -/
lemma compl (hP : IsOrthProj P) : IsOrthProj (1 - P) where
  idem x := by simp [hP.idem]
  symm x y := by simp [inner_sub_left, inner_sub_right, hP.symm]

/-- The identity is an orthogonal projector. -/
lemma one : IsOrthProj (1 : E →L[ℝ] E) where
  idem _ := rfl
  symm _ _ := rfl

/-- The zero map is an orthogonal projector. -/
lemma zero : IsOrthProj (0 : E →L[ℝ] E) where
  idem _ := by simp
  symm _ _ := by simp

/-- A product of commuting orthogonal projectors is an orthogonal projector. -/
lemma mul (hP : IsOrthProj P) (hQ : IsOrthProj Q) (hc : ∀ x, P (Q x) = Q (P x)) :
    IsOrthProj (P * Q) where
  idem x := by
    change P (Q (P (Q x))) = P (Q x)
    rw [← hc (Q x), hP.idem, hQ.idem]
  symm x y := by
    change ⟪P (Q x), y⟫ = ⟪x, P (Q y)⟫
    rw [hP.symm, hQ.symm, hc]

/-- If `Q P = P` for orthogonal projectors, then also `P Q = P`. -/
lemma comp_eq_of_comp_eq (hP : IsOrthProj P) (hQ : IsOrthProj Q) (h : ∀ x, Q (P x) = P x)
    (x : E) : P (Q x) = P x := by
  refine ext_inner_right ℝ fun y => ?_
  rw [hP.symm, hQ.symm, h, ← hP.symm]

/-- If `Q` absorbs `P` then `Q - P` is again an orthogonal projector. -/
lemma sub_of_le (hP : IsOrthProj P) (hQ : IsOrthProj Q) (h : ∀ x, Q (P x) = P x) :
    IsOrthProj (Q - P) where
  idem x := by
    have h' := hP.comp_eq_of_comp_eq hQ h
    change Q (Q x - P x) - P (Q x - P x) = Q x - P x
    simp only [map_sub, hQ.idem, h, h', hP.idem]
    abel
  symm x y := by
    change ⟪Q x - P x, y⟫ = ⟪x, Q y - P y⟫
    simp only [inner_sub_left, inner_sub_right, hP.symm, hQ.symm]

/-- For commuting orthogonal projectors the tangent projector is an orthogonal projector. -/
lemma tangent (hL : IsOrthProj L) (hR : IsOrthProj R) (hc : ∀ x, L (R x) = R (L x)) :
    IsOrthProj (LeanDLRA.tangent L R) := by
  have hn : IsOrthProj ((1 - L) * (1 - R)) :=
    hL.compl.mul hR.compl fun x => by simp [hc]; abel
  have h := hn.compl
  have heq : (1 : E →L[ℝ] E) - (1 - L) * (1 - R) = LeanDLRA.tangent L R := by
    rw [← normal, normal_eq_one_sub_tangent]; abel
  rwa [heq] at h

/-- For commuting orthogonal projectors the normal projector is an orthogonal projector. -/
lemma normal (hL : IsOrthProj L) (hR : IsOrthProj R) (hc : ∀ x, L (R x) = R (L x)) :
    IsOrthProj (LeanDLRA.normal L R) :=
  hL.compl.mul hR.compl fun x => by simp [hc]; abel

/-- Tangent and normal components are orthogonal. -/
lemma inner_tangent_normal (hL : IsOrthProj L) (hR : IsOrthProj R)
    (hc : ∀ x, L (R x) = R (L x)) (x y : E) :
    ⟪LeanDLRA.tangent L R x, LeanDLRA.normal L R y⟫ = 0 := by
  have ht := hL.tangent hR hc
  have hy : LeanDLRA.normal L R y = y - LeanDLRA.tangent L R y := by
    rw [eq_sub_iff_add_eq, add_comm]; exact tangent_apply_add_normal_apply L R y
  rw [hy, ht.inner_sub_self]

/-- Pythagoras for the tangent/normal splitting. -/
lemma norm_sq_tangent_add_normal (hL : IsOrthProj L) (hR : IsOrthProj R)
    (hc : ∀ x, L (R x) = R (L x)) (x : E) :
    ‖LeanDLRA.tangent L R x‖ ^ 2 + ‖LeanDLRA.normal L R x‖ ^ 2 = ‖x‖ ^ 2 := by
  have ht := (hL.tangent hR hc).norm_sq_add x
  have hy : LeanDLRA.normal L R x = x - LeanDLRA.tangent L R x := by
    rw [eq_sub_iff_add_eq, add_comm]; exact tangent_apply_add_normal_apply L R x
  rwa [hy]

end IsOrthProj

end LeanDLRA
