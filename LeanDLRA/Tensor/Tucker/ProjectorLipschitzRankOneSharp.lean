import LeanDLRA.Tensor.Tucker.ProjectorLipschitzRankOne

/-!
# The Lipschitz constant `√(2 (d - 1)/d)` for tensors of rank one cannot be lowered

For Tucker tensors `X`, `Y` with `d ≥ 2` modes and multilinear rank `(1, …, 1)` the tangent
projectors satisfy `‖P(Y) B - P(X) B‖ ≤ √(2 (d - 1)/d) ‖X‖⁻¹ ‖Y - X‖ ‖B‖`
(`norm_tuckerTangentProj_sub_le_of_unique`). This file shows that no constant `q` below
`√(2 (d - 1)/d)` is valid: for every `d ≥ 2` and every `q < √(2 (d - 1)/d)` there are such
tensors in `ℝ^{2 × ⋯ × 2}` and a tensor `B` with
`q ‖X‖⁻¹ ‖Y - X‖ ‖B‖ < ‖P(Y) B - P(X) B‖`.

The examples are `X = ⊗ₖ e₁`, `Y = ⊗ₖ v` with the unit vector `v = (c, s)`, and the tangent
vector `B = ∑ₖ e₁ ⊗ ⋯ ⊗ e₂ ⊗ ⋯ ⊗ e₁` at `X`. The tensor `N = X - P(Y) X` is normal at `Y`, where
`P(Y) X = cᵈ ⊗ₖ v + ∑ₖ v ⊗ ⋯ ⊗ g ⊗ ⋯ ⊗ v` with `g = cᵈ⁻¹ e₁ - cᵈ v`, so that
`‖P(Y) B - B‖ ‖N‖ ≥ |⟪B, N⟫|`. With `⟪B, N⟫ = -d (d - 1) s³ c^{2d - 3}`,
`‖N‖² = 1 - c^{2d - 2} (c² + d s²) ≤ d (d - 1)/2 s⁴`, `‖B‖² = d` and
`‖Y - X‖² = 2 - 2 cᵈ ≤ 2 d s² / (1 + c)` the quotient
`‖P(Y) B - B‖ / (‖Y - X‖ ‖B‖)` is at least `√((d - 1)/d (1 + c)) c^{2d}`, which tends to
`√(2 (d - 1)/d)` as `c → 1`.

## Main results

* `LeanDLRA.Tensor.exists_mul_lt_norm_tuckerTangentProj_sub_of_unique`: the lower bound for
  every `q < √(2 (d - 1)/d)`.
* `LeanDLRA.Tensor.sqrt_le_of_forall_norm_tuckerTangentProj_sub_le`: every constant that is
  valid for all tensors of multilinear rank `(1, …, 1)` with `d` modes is at least
  `√(2 (d - 1)/d)`.

## References

* [BachmayrEisenmannUschmajew2025, Prop. 4.2]
-/

open Matrix
open scoped Matrix RealInnerProductSpace Topology

namespace LeanDLRA

namespace Tensor

namespace TuckerProjectorSharpExamples

/-! ### Scalar inequalities -/

/-- `1 - (1 - x)ᵐ (1 + m x) ≤ m (m + 1)/2 x²` for `0 ≤ x ≤ 1`. -/
private lemma one_sub_pow_mul_le (m : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 - (1 - x) ^ m * (1 + m * x) ≤ m * (m + 1) / 2 * x ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hp1 : (1 - x) ^ m ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have h2 : (1 - x) ^ m * ((m + 1) * x ^ 2) ≤ (m + 1) * x ^ 2 :=
      mul_le_of_le_one_left (by positivity) hp1
    have e : 1 - (1 - x) ^ (m + 1) * (1 + ((m + 1 : ℕ) : ℝ) * x) =
        1 - (1 - x) ^ m * (1 + m * x) + (1 - x) ^ m * ((m + 1) * x ^ 2) := by
      push_cast
      ring
    rw [e]
    push_cast
    linarith

/-- The scalar form of the lower bound: for the angle with cosine `c` and sine `s`, the inner
product `T` of the tangent vector with the normal vector and the squared norm `Dq` of the normal
vector give `q a b < δ` if `q² d < (d - 1) (1 + c) c^{4 d}`, `d = m + 1`. -/
private lemma lower_bound_scalar {m : ℕ} (hm : 1 ≤ m) {c s u P T Dq δ a b q : ℝ} (hc0 : 0 < c)
    (hc1 : c < 1) (hs : 0 < s) (hcs : c ^ 2 + s ^ 2 = 1) (hP : P = c ^ (m + 1))
    (hu : u * c = P) (hq : q ^ 2 * (m + 1) < m * (1 + c) * (c ^ (m + 1)) ^ 4)
    (hδ : 0 ≤ δ) (ha2 : a ^ 2 = 2 - 2 * P) (hb2 : b ^ 2 = m + 1)
    (hT : T * c ^ 3 = P ^ 2 * (m + 1) * m * s * (1 - c ^ 2))
    (hD : Dq = 1 - P ^ 2 - (m + 1) * (u ^ 2 - P ^ 2)) (hTD : T ^ 2 ≤ δ ^ 2 * Dq) :
    q * (a * b) < δ := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hs2 : s ^ 2 = 1 - c ^ 2 := by linarith
  have hs21 : s ^ 2 ≤ 1 := by nlinarith
  -- the squared norm of the normal vector
  have hDq : Dq ≤ m * (m + 1) / 2 * (s ^ 2) ^ 2 := by
    have h1 := one_sub_pow_mul_le m (sq_nonneg s) hs21
    have hP2 : P ^ 2 = c ^ 2 * (c ^ 2) ^ m := by rw [hP]; ring
    have e : Dq * c ^ 2 = c ^ 2 * (1 - (1 - s ^ 2) ^ m * (1 + m * s ^ 2)) := by
      have hc2 : 1 - s ^ 2 = c ^ 2 := by linarith
      rw [hc2, hD]
      have hu2 : u ^ 2 * c ^ 2 = P ^ 2 := by rw [← hu]; ring
      linear_combination (-(m + 1 : ℝ)) * hu2 - (1 + m * s ^ 2) * hP2 + m * P ^ 2 * hcs
    have e' : Dq = 1 - (1 - s ^ 2) ^ m * (1 + m * s ^ 2) :=
      mul_right_cancel₀ (pow_pos hc0 2).ne' (e.trans (mul_comm _ _))
    rw [e']
    exact h1
  -- the inner product
  have hT2 : T ^ 2 * c ^ 6 =
      (m * (m + 1) / 2 * (s ^ 2) ^ 2) * (2 * P ^ 4 * (m + 1) * m * s ^ 2) := by
    have : T ^ 2 * c ^ 6 = (T * c ^ 3) ^ 2 := by ring
    rw [this, hT, ← hs2]
    ring
  have hc6 : c ^ 6 ≤ 1 := pow_le_one₀ hc0.le hc1.le
  have hK : 0 < (m : ℝ) * (m + 1) / 2 * (s ^ 2) ^ 2 := by positivity
  have hlow : 2 * P ^ 4 * (m + 1) * m * s ^ 2 ≤ δ ^ 2 := by
    refine le_of_mul_le_mul_left ?_ hK
    calc (m * (m + 1) / 2 * (s ^ 2) ^ 2) * (2 * P ^ 4 * (m + 1) * m * s ^ 2)
        = T ^ 2 * c ^ 6 := hT2.symm
      _ ≤ T ^ 2 * 1 := mul_le_mul_of_nonneg_left hc6 (sq_nonneg T)
      _ ≤ δ ^ 2 * Dq := by rw [mul_one]; exact hTD
      _ ≤ δ ^ 2 * (m * (m + 1) / 2 * (s ^ 2) ^ 2) := mul_le_mul_of_nonneg_left hDq (sq_nonneg δ)
      _ = _ := mul_comm _ _
  -- the distance
  have hbern : 2 - 2 * P ≤ 2 * (m + 1) * (1 - c) := by
    have h := one_add_mul_le_pow (a := c - 1) (by linarith) (m + 1)
    rw [add_sub_cancel] at h
    push_cast at h
    rw [hP]
    linarith
  have hupp : q ^ 2 * (2 - 2 * P) * (m + 1) < 2 * P ^ 4 * (m + 1) * m * s ^ 2 := by
    have h1c : (0 : ℝ) < 1 + c := by linarith
    refine lt_of_mul_lt_mul_right ?_ h1c.le
    calc q ^ 2 * (2 - 2 * P) * (m + 1) * (1 + c)
        ≤ q ^ 2 * (2 * (m + 1) * (1 - c)) * (m + 1) * (1 + c) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hbern (sq_nonneg q)) (by positivity)) h1c.le
      _ = 2 * (m + 1) * s ^ 2 * (q ^ 2 * (m + 1)) := by rw [hs2]; ring
      _ < 2 * (m + 1) * s ^ 2 * (m * (1 + c) * (c ^ (m + 1)) ^ 4) :=
          mul_lt_mul_of_pos_left hq (by positivity)
      _ = 2 * P ^ 4 * (m + 1) * m * s ^ 2 * (1 + c) := by rw [hP]; ring
  refine lt_of_pow_lt_pow_left₀ 2 hδ ?_
  calc (q * (a * b)) ^ 2 = q ^ 2 * (2 - 2 * P) * (m + 1) := by rw [← ha2, ← hb2]; ring
    _ < 2 * P ^ 4 * (m + 1) * m * s ^ 2 := hupp
    _ ≤ δ ^ 2 := hlow

/-! ### Columns with two entries -/

/-- The inner product of two columns with two entries. -/
private lemma col_mul_apply (a b : Matrix (Fin 2) (Fin 1) ℝ) :
    (aᵀ * b) default default = a 0 0 * b 0 0 + a 1 0 * b 1 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private lemma transpose_mul_self_eq_one {a : Matrix (Fin 2) (Fin 1) ℝ}
    (h : a 0 0 * a 0 0 + a 1 0 * a 1 0 = 1) : aᵀ * a = 1 := by
  ext i j
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  rw [Matrix.one_apply_eq]
  exact (col_mul_apply a a).trans h

private lemma transpose_mul_eq_zero {a b : Matrix (Fin 2) (Fin 1) ℝ}
    (h : a 0 0 * b 0 0 + a 1 0 * b 1 0 = 0) : aᵀ * b = 0 := by
  ext i j
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  rw [Matrix.zero_apply]
  exact (col_mul_apply a b).trans h

/-! ### The family of examples -/

/-- The lower bound for the angle with cosine `c` and sine `s`: `X = ⊗ₖ e₁`, `Y = ⊗ₖ v` with
`v = (c, s)`, and the tangent vector `B = ∑ₖ e₁ ⊗ ⋯ ⊗ e₂ ⊗ ⋯ ⊗ e₁` at `X`. The tensor
`X - P(Y) X` is normal at `Y`, and `P(Y) X = cᵈ ⊗ₖ v + ∑ₖ v ⊗ ⋯ ⊗ g ⊗ ⋯ ⊗ v` with the column
`g = cᵈ⁻¹ e₁ - cᵈ v`. -/
private lemma lower_bound {m : ℕ} (hm : 1 ≤ m) {c s q : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hs : 0 < s) (hcs : c ^ 2 + s ^ 2 = 1)
    (hq : q ^ 2 * (m + 1) < m * (1 + c) * (c ^ (m + 1)) ^ 4) :
    ∃ (U U' : ∀ _ : Fin (m + 1), Matrix (Fin 2) (Fin 1) ℝ)
      (C : Tensor fun _ : Fin (m + 1) => Fin 1)
      (W W' : ∀ k : Fin (m + 1), Matrix (∀ _ : {j : Fin (m + 1) // j ≠ k}, Fin 2) (Fin 1) ℝ)
      (B : Tensor fun _ : Fin (m + 1) => Fin 2),
      (∀ k, (U k)ᵀ * U k = 1) ∧
      (∀ k, actOn (· ≠ k) (W k * (W k)ᵀ) (tucker C U) = tucker C U) ∧
      (∀ k, ∃ B : Matrix _ (Fin 1) ℝ, W k = unfold (· ≠ k) (tucker C U) * B) ∧
      tucker C U ≠ 0 ∧
      (∀ k, (U' k)ᵀ * U' k = 1) ∧
      (∀ k, actOn (· ≠ k) (W' k * (W' k)ᵀ) (tucker C U') = tucker C U') ∧
      (∀ k, ∃ B : Matrix _ (Fin 1) ℝ, W' k = unfold (· ≠ k) (tucker C U') * B) ∧
      tucker C U' ≠ 0 ∧
      q * (‖tucker C U‖⁻¹ * ‖tucker C U' - tucker C U‖ * ‖B‖) <
        ‖tuckerTangentProj U' 1 W' B - tuckerTangentProj U 1 W B‖ := by
  -- the columns
  obtain ⟨e₁, h10, h11⟩ : ∃ e : Matrix (Fin 2) (Fin 1) ℝ, e 0 0 = 1 ∧ e 1 0 = 0 :=
    ⟨!![1; 0], rfl, rfl⟩
  obtain ⟨e₂, h20, h21⟩ : ∃ e : Matrix (Fin 2) (Fin 1) ℝ, e 0 0 = 0 ∧ e 1 0 = 1 :=
    ⟨!![0; 1], rfl, rfl⟩
  obtain ⟨v, hv0, hv1⟩ : ∃ e : Matrix (Fin 2) (Fin 1) ℝ, e 0 0 = c ∧ e 1 0 = s :=
    ⟨!![c; s], rfl, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = c ^ (m + 1) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = P / c := ⟨_, rfl⟩
  have huc : u * c = P := by rw [hu, div_mul_cancel₀ _ hc0.ne']
  obtain ⟨g, hg0, hg1⟩ : ∃ e : Matrix (Fin 2) (Fin 1) ℝ, e 0 0 = u - P * c ∧ e 1 0 = -(P * s) :=
    ⟨!![u - P * c; -(P * s)], rfl, rfl⟩
  have he₁ : ∀ _ : Fin (m + 1), e₁ᵀ * e₁ = 1 := fun _ =>
    transpose_mul_self_eq_one (by rw [h10, h11]; ring)
  have hv : ∀ _ : Fin (m + 1), vᵀ * v = 1 := fun _ =>
    transpose_mul_self_eq_one (by rw [hv0, hv1]; linear_combination hcs)
  have he₂ : ∀ _ : Fin (m + 1), e₁ᵀ * e₂ = 0 := fun _ =>
    transpose_mul_eq_zero (by rw [h10, h11, h20, h21]; ring)
  have hg : ∀ _ : Fin (m + 1), vᵀ * g = 0 := fun _ =>
    transpose_mul_eq_zero (by rw [hv0, hv1, hg0, hg1]; linear_combination huc - P * hcs)
  -- the cores
  obtain ⟨C, hC⟩ : ∃ C : Tensor fun _ : Fin (m + 1) => Fin 1, C default = 1 :=
    ⟨WithLp.toLp 2 fun _ => 1, rfl⟩
  obtain ⟨Cp, hCp⟩ : ∃ C : Tensor fun _ : Fin (m + 1) => Fin 1, C default = P :=
    ⟨WithLp.toLp 2 fun _ => P, rfl⟩
  have h0 : (0 : Tensor fun _ : Fin (m + 1) => Fin 1) default = 0 := rfl
  have hz : ∀ M : ∀ _ : Fin (m + 1), Matrix (Fin 2) (Fin 1) ℝ,
      tucker (0 : Tensor fun _ : Fin (m + 1) => Fin 1) M = 0 := fun M => (tuckerCLM M).map_zero
  -- the tensors
  have hnX := norm_tucker_sq_of_unique he₁ C
  have hnY := norm_tucker_sq_of_unique hv C
  rw [hC, one_pow] at hnX hnY
  have hX : tucker C (fun _ : Fin (m + 1) => e₁) ≠ 0 := fun h => by
    rw [h, norm_zero] at hnX
    norm_num at hnX
  have hY : tucker C (fun _ : Fin (m + 1) => v) ≠ 0 := fun h => by
    rw [h, norm_zero] at hnY
    norm_num at hnY
  obtain ⟨W, hWX, hWB⟩ := exists_coRange_tucker_of_unique he₁ hX
  obtain ⟨W', hWX', hWB'⟩ := exists_coRange_tucker_of_unique hv hY
  have hPX := isOrthProj_tuckerTangentProj he₁ IsOrthProj.one hWX hWB
  have hPY := isOrthProj_tuckerTangentProj hv IsOrthProj.one hWX' hWB'
  obtain ⟨B, hBdef⟩ : ∃ B : Tensor fun _ : Fin (m + 1) => Fin 2,
      B = tucker (0 : Tensor fun _ : Fin (m + 1) => Fin 1) (fun _ => e₁) +
        ∑ k, tucker C (Function.update (fun _ : Fin (m + 1) => e₁) k e₂) := ⟨_, rfl⟩
  obtain ⟨t, htdef⟩ : ∃ t : Tensor fun _ : Fin (m + 1) => Fin 2,
      t = tucker Cp (fun _ => v) +
        ∑ k, tucker C (Function.update (fun _ : Fin (m + 1) => v) k g) := ⟨_, rfl⟩
  have hBtan : tuckerTangentProj (fun _ : Fin (m + 1) => e₁) 1 W B = B :=
    (tuckerTangentProj_eq_self_iff he₁ IsOrthProj.one hWX hWB B).2
      (Submodule.subset_span ⟨0, rfl, fun _ => e₂, he₂, hBdef⟩)
  have hc' : ∀ _ : Fin (m + 1), (e₁ᵀ * v) default default ≠ 0 := fun _ => by
    rw [col_mul_apply, h10, h11, hv0]
    simpa using hc0.ne'
  have hvv' : ∀ _ : Fin (m + 1), (vᵀ * v) default default ≠ 0 := fun k => by
    rw [hv k]
    simp
  have hve' : ∀ _ : Fin (m + 1), (vᵀ * e₁) default default ≠ 0 := fun _ => by
    rw [col_mul_apply, h10, h11, hv0]
    simpa using hc0.ne'
  have hee' : ∀ _ : Fin (m + 1), (e₁ᵀ * e₁) default default ≠ 0 := fun k => by
    rw [he₁ k]
    simp
  have hXtan : tucker C (fun _ : Fin (m + 1) => e₁) = tucker C (fun _ => e₁) +
      ∑ k, tucker (0 : Tensor fun _ : Fin (m + 1) => Fin 1)
        (Function.update (fun _ : Fin (m + 1) => e₁) k e₁) := by
    simp [hz]
  -- every tangent vector at `Y` has the same inner product with `X` and with `t`
  have hkey : ∀ (Cg : Tensor fun _ : Fin (m + 1) => Fin 1)
      (D : ∀ _ : Fin (m + 1), Matrix (Fin 2) (Fin 1) ℝ), (∀ k, vᵀ * D k = 0) →
      ⟪tucker Cg (fun _ => v) + ∑ k, tucker C (Function.update (fun _ : Fin (m + 1) => v) k (D k)),
        tucker C (fun _ : Fin (m + 1) => e₁)⟫ =
      ⟪tucker Cg (fun _ => v) + ∑ k, tucker C (Function.update (fun _ : Fin (m + 1) => v) k (D k)),
        t⟫ := by
    intro Cg D hD
    have hD' : ∀ k, c * D k 0 0 + s * D k 1 0 = 0 := fun k => by
      have h := col_mul_apply v (D k)
      rw [hD k, hv0, hv1] at h
      exact h.symm
    rw [htdef, hXtan, inner_tucker_add_sum_update_of_unique _ _ _ _ _ _ _ _ hve',
      inner_tucker_add_sum_update_of_unique _ _ _ _ _ _ _ _ hvv']
    have hcc : c * c + s * s = 1 := by linear_combination hcs
    have hDv : ∀ k, D k 0 0 * c + D k 1 0 * s = 0 := fun k => by linear_combination hD' k
    have hvg : c * (u - P * c) + s * -(P * s) = 0 := by linear_combination huc - P * hcs
    have hk : ∀ k, D k 0 0 * (u - P * c) + D k 1 0 * -(P * s) = P * (D k 0 0 / c) := fun k => by
      rw [show P * (D k 0 0 / c) = u * D k 0 0 by rw [hu]; ring]
      linear_combination (-P) * hD' k
    simp only [col_mul_apply, h10, h11, hv0, hv1, hg0, hg1, hC, hCp, h0, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, ← hP, hcc, hDv, hvg, hk, mul_one, mul_zero, add_zero,
      zero_mul, one_mul, one_pow, div_one, Finset.sum_const_zero, sub_zero, ← Finset.mul_sum]
    ring
  have httan : tuckerTangentProj (fun _ : Fin (m + 1) => v) 1 W' t = t :=
    (tuckerTangentProj_eq_self_iff hv IsOrthProj.one hWX' hWB' t).2
      (Submodule.subset_span ⟨Cp, rfl, fun _ => g, hg, htdef⟩)
  -- `X - t` is orthogonal to `P(Y) B`
  obtain ⟨Cg, -, D, hD, hPB⟩ := (mem_tuckerTangentSpace_iff hv IsOrthProj.one hWX' hWB' _).1
    ((tuckerTangentProj_eq_self_iff hv IsOrthProj.one hWX' hWB' _).1 (hPY.idem B))
  have horth : ⟪tuckerTangentProj (fun _ : Fin (m + 1) => v) 1 W' B,
      tucker C (fun _ : Fin (m + 1) => e₁) - t⟫ = 0 := by
    rw [hPB, inner_sub_right, hkey Cg D hD, sub_self]
  have htX : ⟪t, tucker C (fun _ : Fin (m + 1) => e₁)⟫ = ⟪t, t⟫ := by
    have h := hkey Cp (fun _ => g) hg
    rwa [← htdef] at h
  -- norms and inner products
  have hnt : ‖t‖ ^ 2 = P ^ 2 + (m + 1) * (u ^ 2 - P ^ 2) := by
    rw [htdef, norm_sq_tucker_add_sum_update_of_unique hv hg, hCp, hC]
    simp only [col_mul_apply, hg0, hg1, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    linear_combination ((m : ℝ) + 1) * ((-2 * P) * huc + P ^ 2 * hcs)
  have hXt : ‖tucker C (fun _ : Fin (m + 1) => e₁) - t‖ ^ 2 =
      1 - P ^ 2 - (m + 1) * (u ^ 2 - P ^ 2) := by
    rw [norm_sub_sq_real, hnX, real_inner_comm t, htX, real_inner_self_eq_norm_sq, hnt]
    ring
  have hBX : ⟪B, tucker C (fun _ : Fin (m + 1) => e₁)⟫ = 0 := by
    rw [hBdef, hXtan, inner_tucker_add_sum_update_of_unique _ _ _ _ _ _ _ _ hee']
    simp only [col_mul_apply, h10, h11, h20, h21, h0, hC, mul_one, mul_zero, add_zero, zero_mul,
      zero_div, Finset.sum_const_zero, sub_zero]
  have hBt : ⟪B, t⟫ * c ^ 3 = P ^ 2 * (m + 1) * m * s * (1 - c ^ 2) := by
    rw [hBdef, htdef, inner_tucker_add_sum_update_of_unique _ _ _ _ _ _ _ _ hc']
    simp only [col_mul_apply, h10, h11, h20, h21, hv0, hv1, hg0, hg1, h0, hC, hCp,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.prod_const,
      mul_one, add_zero, zero_add, zero_mul, one_mul, ← hP]
    push_cast
    rw [hu]
    field_simp
    ring
  have hYX : ‖tucker C (fun _ : Fin (m + 1) => v) - tucker C (fun _ : Fin (m + 1) => e₁)‖ ^ 2 =
      2 - 2 * P := by
    rw [norm_sub_sq_real, hnX, hnY, inner_tucker_tucker_of_unique, hC]
    simp only [col_mul_apply, h10, h11, hv0, hv1, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, mul_one, mul_zero, add_zero, ← hP]
    ring
  have hnB : ‖B‖ ^ 2 = m + 1 := by
    rw [hBdef, norm_sq_tucker_add_sum_update_of_unique he₁ he₂, h0, hC]
    simp only [col_mul_apply, h20, h21, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    ring
  -- the Cauchy–Schwarz inequality with the normal vector `X - t`
  have he : ⟪tuckerTangentProj (fun _ : Fin (m + 1) => v) 1 W' B - B,
      tucker C (fun _ : Fin (m + 1) => e₁) - t⟫ = ⟪B, t⟫ := by
    rw [inner_sub_left, horth, inner_sub_right, hBX]
    ring
  have hCS : ⟪B, t⟫ ^ 2 ≤ ‖tuckerTangentProj (fun _ : Fin (m + 1) => v) 1 W' B - B‖ ^ 2 *
      ‖tucker C (fun _ : Fin (m + 1) => e₁) - t‖ ^ 2 := by
    have h := abs_real_inner_le_norm (tuckerTangentProj (fun _ : Fin (m + 1) => v) 1 W' B - B)
      (tucker C (fun _ : Fin (m + 1) => e₁) - t)
    rw [he] at h
    calc ⟪B, t⟫ ^ 2 = |⟪B, t⟫| ^ 2 := (sq_abs _).symm
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = _ := mul_pow _ _ 2
  have hXn : ‖tucker C (fun _ : Fin (m + 1) => e₁)‖ = 1 :=
    (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 (hnX.trans (one_pow 2).symm)
  refine ⟨_, _, C, W, W', B, he₁, hWX, hWB, hX, hv, hWX', hWB', hY, ?_⟩
  rw [hXn, inv_one, one_mul, hBtan]
  exact lower_bound_scalar hm hc0 hc1 hs hcs hP huc hq (norm_nonneg _) hYX hnB hBt hXt hCS

end TuckerProjectorSharpExamples

open TuckerProjectorSharpExamples in
/-- **The constant `√(2 (d - 1)/d)` of the Lipschitz bound of the tangent projector for tensors
of rank one cannot be lowered.** For `d ≥ 2` modes and every `q < √(2 (d - 1)/d)` there are
Tucker tensors `X = C ×ₖ Uₖ` and `Y = C ×ₖ U'ₖ` of multilinear rank `(1, …, 1)` in
`ℝ^{2 × ⋯ × 2}`, co-range bases `W`, `W'` and a tensor `B` which satisfy all hypotheses of
`norm_tuckerTangentProj_sub_le_of_unique` and
`q ‖X‖⁻¹ ‖Y - X‖ ‖B‖ < ‖P(Y) B - P(X) B‖`. -/
theorem exists_mul_lt_norm_tuckerTangentProj_sub_of_unique {d : ℕ} (hd : 2 ≤ d) {q : ℝ}
    (hq : q < √(2 * ((d : ℝ) - 1) / d)) :
    ∃ (U U' : ∀ _ : Fin d, Matrix (Fin 2) (Fin 1) ℝ) (C : Tensor fun _ : Fin d => Fin 1)
      (W W' : ∀ k : Fin d, Matrix (∀ _ : {j : Fin d // j ≠ k}, Fin 2) (Fin 1) ℝ)
      (B : Tensor fun _ : Fin d => Fin 2),
      (∀ k, (U k)ᵀ * U k = 1) ∧
      (∀ k, actOn (· ≠ k) (W k * (W k)ᵀ) (tucker C U) = tucker C U) ∧
      (∀ k, ∃ B : Matrix _ (Fin 1) ℝ, W k = unfold (· ≠ k) (tucker C U) * B) ∧
      tucker C U ≠ 0 ∧
      (∀ k, (U' k)ᵀ * U' k = 1) ∧
      (∀ k, actOn (· ≠ k) (W' k * (W' k)ᵀ) (tucker C U') = tucker C U') ∧
      (∀ k, ∃ B : Matrix _ (Fin 1) ℝ, W' k = unfold (· ≠ k) (tucker C U') * B) ∧
      tucker C U' ≠ 0 ∧
      q * (‖tucker C U‖⁻¹ * ‖tucker C U' - tucker C U‖ * ‖B‖) <
        ‖tuckerTangentProj U' 1 W' B - tuckerTangentProj U 1 W B‖ := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have e : ((m + 1 : ℕ) : ℝ) - 1 = m := by
    push_cast
    ring
  rw [e] at hq
  push_cast at hq
  have hκ : (0 : ℝ) < 2 * m / (m + 1) := by positivity
  have hq'0 : 0 ≤ max q 0 := le_max_right _ _
  have hq' : max q 0 < √(2 * m / (m + 1)) := max_lt hq (Real.sqrt_pos.2 hκ)
  have hq2 : max q 0 ^ 2 < 2 * m / (m + 1) := (Real.lt_sqrt hq'0).1 hq'
  have h1 : max q 0 ^ 2 * (m + 1) < m * (1 + 1) * ((1 : ℝ) ^ (m + 1)) ^ 4 := by
    rw [one_pow, one_pow, mul_one]
    rw [lt_div_iff₀ (by positivity)] at hq2
    linarith
  obtain ⟨c, ⟨hc0, hc1⟩, hc⟩ : ∃ c : ℝ, c ∈ Set.Ioo (0 : ℝ) 1 ∧
      max q 0 ^ 2 * (m + 1) < m * (1 + c) * (c ^ (m + 1)) ^ 4 := by
    have hcont : ContinuousAt (fun c : ℝ => (m : ℝ) * (1 + c) * (c ^ (m + 1)) ^ 4) 1 := by
      fun_prop
    have hev := hcont.eventually (lt_mem_nhds h1)
    obtain ⟨c, hc, hI⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
      (Ioo_mem_nhdsLT (zero_lt_one' ℝ))).exists
    exact ⟨c, hI, hc⟩
  obtain ⟨s, hs, hcs⟩ : ∃ s : ℝ, 0 < s ∧ c ^ 2 + s ^ 2 = 1 := by
    have h : 0 < 1 - c ^ 2 := by nlinarith
    exact ⟨√(1 - c ^ 2), Real.sqrt_pos.2 h, by rw [Real.sq_sqrt h.le]; ring⟩
  obtain ⟨U, U', C, W, W', B, a1, a2, a3, a4, a5, a6, a7, a8, hlow⟩ :=
    lower_bound hm hc0 hc1 hs hcs hc
  exact ⟨U, U', C, W, W', B, a1, a2, a3, a4, a5, a6, a7, a8,
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_left q 0) (by positivity)) hlow⟩

/-- **Every valid Lipschitz constant of the tangent projector for tensors of rank one is at
least `√(2 (d - 1)/d)`.** Let `d ≥ 2`. If `‖P(Y) B - P(X) B‖ ≤ κ ‖X‖⁻¹ ‖Y - X‖ ‖B‖` holds for
all Tucker tensors `X = C ×ₖ Uₖ ≠ 0`, `Y = C ×ₖ U'ₖ ≠ 0` in `ℝ^{2 × ⋯ × 2}` whose core has one
entry, with unit columns and co-range bases as in `norm_tuckerTangentProj_sub_le_of_unique`, and
all `B`, then `√(2 (d - 1)/d) ≤ κ`. Together with `norm_tuckerTangentProj_sub_le_of_unique` the
smallest such constant is `√(2 (d - 1)/d)`. -/
theorem sqrt_le_of_forall_norm_tuckerTangentProj_sub_le {d : ℕ} (hd : 2 ≤ d) {κ : ℝ}
    (h : ∀ (U U' : ∀ _ : Fin d, Matrix (Fin 2) (Fin 1) ℝ) (C : Tensor fun _ : Fin d => Fin 1)
      (W W' : ∀ k : Fin d, Matrix (∀ _ : {j : Fin d // j ≠ k}, Fin 2) (Fin 1) ℝ)
      (B : Tensor fun _ : Fin d => Fin 2),
      (∀ k, (U k)ᵀ * U k = 1) →
      (∀ k, actOn (· ≠ k) (W k * (W k)ᵀ) (tucker C U) = tucker C U) →
      (∀ k, ∃ B : Matrix _ (Fin 1) ℝ, W k = unfold (· ≠ k) (tucker C U) * B) →
      tucker C U ≠ 0 →
      (∀ k, (U' k)ᵀ * U' k = 1) →
      (∀ k, actOn (· ≠ k) (W' k * (W' k)ᵀ) (tucker C U') = tucker C U') →
      (∀ k, ∃ B : Matrix _ (Fin 1) ℝ, W' k = unfold (· ≠ k) (tucker C U') * B) →
      tucker C U' ≠ 0 →
      ‖tuckerTangentProj U' 1 W' B - tuckerTangentProj U 1 W B‖ ≤
        κ * (‖tucker C U‖⁻¹ * ‖tucker C U' - tucker C U‖ * ‖B‖)) :
    √(2 * ((d : ℝ) - 1) / d) ≤ κ := by
  by_contra hκ
  obtain ⟨U, U', C, W, W', B, a1, a2, a3, a4, a5, a6, a7, a8, hlow⟩ :=
    exists_mul_lt_norm_tuckerTangentProj_sub_of_unique hd (not_le.1 hκ)
  exact absurd (h U U' C W W' B a1 a2 a3 a4 a5 a6 a7 a8) (not_le.2 hlow)

/-- Non-vacuity of `sqrt_le_of_forall_norm_tuckerTangentProj_sub_le`: its hypothesis holds for
`κ = √(2 (d - 1)/d)`, by `norm_tuckerTangentProj_sub_le_of_unique`; here for three modes. -/
example : √(2 * (((3 : ℕ) : ℝ) - 1) / (3 : ℕ)) ≤ √(2 * (((3 : ℕ) : ℝ) - 1) / (3 : ℕ)) :=
  sqrt_le_of_forall_norm_tuckerTangentProj_sub_le (by norm_num)
    fun U U' C W W' B a1 a2 a3 a4 a5 a6 a7 a8 => by
      have h := norm_tuckerTangentProj_sub_le_of_unique (by norm_num) a1 a2 a3 a4 a5 a6 a7 a8 B
      calc _ ≤ _ := h
        _ = _ := by ring

end Tensor

end LeanDLRA
