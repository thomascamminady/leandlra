import LeanDLRA.Tensor.Tucker.ProjectorLowerBound

/-!
# The Lipschitz constant of the tangent projector for tensors of rank one

Let `X = C ×ₖ Uₖ` and `Y = C' ×ₖ U'ₖ` be nonzero Tucker tensors with `d ≥ 2` modes whose cores
have one entry: tensors of multilinear rank `(1, …, 1)` (elementary tensors; the manifold is the
cone over the Segre manifold). With the tangent projectors `P(X)`, `P(Y)` (`tuckerTangentProj`
with the core projector `1`, [BachmayrEisenmannUschmajew2025, Prop. 4.2]) this file shows

  `‖P(Y) B - P(X) B‖ ≤ √(2 (d - 1)/d) ‖X‖⁻¹ ‖Y - X‖ ‖B‖`

for all tensors `B`, in Frobenius norms and without a smallness condition on `‖Y - X‖`. Here
`‖X‖` is the nonzero singular value of every matricization of `X`, so this is the bound of
`norm_tuckerTangentProj_sub_le` with the constant `√(2 (d - 1)/d) < √2` in place of `√d`. For
`d = 2` the constant is `1`, the constant of the manifold of matrices of fixed rank
(`norm_tangentProjAt_sub_le_inv_mul`). The value `√(2 (d - 1)/d)` is the maximal curvature of
the geodesics of the Segre manifold in the unit sphere (Breiding–Eggleston, arXiv 2307.04224,
Thm. 1.2).

The proof has three parts.

* The distance: `(1 - ∏ₖ cₖ²) ‖X‖² ≤ ‖Y - X‖²` with the cosines `cₖ = Uₖᵀ U'ₖ` of the angles of
  the factors.
* The frames inequality: a vector `Z` tangent at `X` satisfies
  `‖Z - P(Y) Z‖² ≤ 2 (d - 1)/d (1 - ∏ₖ cₖ²) ‖Z‖²`. If some `cₖ` vanishes this is trivial.
  Otherwise the tangent vector `P(Y) Z` at `Y` is written down, the inner products of tangent
  vectors of elementary tensors are products over the modes, and with `Tₖ = tan² θₖ` the claim
  is the nonnegativity of a quadratic polynomial whose discriminant is bounded by two
  applications of the Cauchy–Schwarz inequality and the elementary inequality
  `(∑ₖ τₖ)² ≤ ∑ₖ τₖ² + ∑ₖ Tₖ nₖ + (d - 2)/d (∑ₖ Tₖ) (∑ₖ nₖ)` for `τₖ² ≤ Tₖ nₖ`.
* The difference of two orthogonal projectors is bounded by the two one-sided bounds
  (`IsOrthProj.norm_sub_apply_le_of_norm_sub_apply_le`).

## Main results

* `LeanDLRA.Tensor.norm_tucker_sq_of_unique`,
  `LeanDLRA.Tensor.inner_tucker_add_sum_update_of_unique`,
  `LeanDLRA.Tensor.norm_sq_tucker_add_sum_update_of_unique`: norms and inner products of
  elementary tensors and of their tangent vectors.
* `LeanDLRA.Tensor.one_sub_prod_sq_mul_norm_tucker_sq_le`: the distance and the angles.
* `LeanDLRA.Tensor.norm_sub_tuckerTangentProj_apply_sq_le_of_unique`: the frames inequality.
* `LeanDLRA.Tensor.norm_tuckerTangentProj_sub_le_of_unique`: the Lipschitz bound.
* `LeanDLRA.Tensor.exists_coRange_tucker_of_unique`: co-range bases of an elementary tensor.

## References

* [BachmayrEisenmannUschmajew2025, Prop. 4.2]
* P. Breiding, S. Eggleston, Reach of Segre–Veronese manifolds, arXiv 2307.04224
-/

open Matrix
open scoped Matrix RealInnerProductSpace

namespace LeanDLRA

namespace Tensor

/-! ### The frames inequality in scalar form -/

/-- A quadratic polynomial `a Z² - 2 b Z + c` with `a, c ≥ 0` and `b² ≤ a c` is nonnegative. -/
private lemma quadratic_nonneg {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (h : b ^ 2 ≤ a * c) (Z : ℝ) :
    0 ≤ a * Z ^ 2 - 2 * Z * b + c := by
  rcases ha.eq_or_lt with rfl | ha'
  · have hb : b = 0 := by
      have : b ^ 2 ≤ 0 := by simpa using h
      exact pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm this (sq_nonneg b))
    rw [hb]
    linarith
  · have h1 : 0 ≤ a * (a * Z ^ 2 - 2 * Z * b + c) := by nlinarith [sq_nonneg (a * Z - b)]
    exact nonneg_of_mul_nonneg_right h1 ha'

/-- `1 + ∑ⱼ Tⱼ ≤ ∏ⱼ (1 + Tⱼ)` for nonnegative `Tⱼ`. -/
private lemma one_add_sum_le_prod_one_add {κ : Type*} (s : Finset κ) {T : κ → ℝ}
    (hT : ∀ j, 0 ≤ T j) : 1 + ∑ j ∈ s, T j ≤ ∏ j ∈ s, (1 + T j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have h1 : 0 ≤ ∑ j ∈ s, T j := Finset.sum_nonneg fun j _ => hT j
    nlinarith [hT a, mul_nonneg (hT a) h1,
      mul_nonneg (by linarith [hT a] : (0 : ℝ) ≤ 1 + T a) (sub_nonneg.2 ih)]

/-- **The frames inequality for products of planes, in the tangents of the angles.** For
`d ≥ 2` modes with `Tⱼ = tan² θⱼ`, and `τⱼ² ≤ Tⱼ nⱼ`:
`(1 - (d-2)/d ∑ⱼ Tⱼ) ((Z - ∑ⱼ τⱼ)² + ∑ⱼ nⱼ) ≤ Z² + ∑ⱼ ((1 + Tⱼ) ((Z - τⱼ)² + nⱼ) - Z²)`. -/
private lemma frames_tan {d : ℕ} (hd : 2 ≤ d) {T τ n : Fin d → ℝ} (hT : ∀ j, 0 ≤ T j)
    (hn : ∀ j, 0 ≤ n j) (hτ : ∀ j, τ j ^ 2 ≤ T j * n j) (Z : ℝ) :
    (1 - ((d : ℝ) - 2) / d * ∑ j, T j) * ((Z - ∑ j, τ j) ^ 2 + ∑ j, n j) ≤
      Z ^ 2 + ∑ j, ((1 + T j) * ((Z - τ j) ^ 2 + n j) - Z ^ 2) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  set γ : ℝ := ((d : ℝ) - 2) / d with hγ
  have hγ0 : 0 ≤ γ := div_nonneg (by linarith) hd0.le
  have hγd : γ = 1 - 2 / d := by rw [hγ]; field_simp
  set σ := ∑ j, T j with hσ
  set q := ∑ j, τ j with hq
  set N := ∑ j, n j with hN
  set p := ∑ j, T j * τ j with hp
  set S2 := ∑ j, τ j ^ 2 with hS2
  set S3 := ∑ j, T j * τ j ^ 2 with hS3
  set S4 := ∑ j, T j * n j with hS4
  have hσ0 : 0 ≤ σ := Finset.sum_nonneg fun j _ => hT j
  have hS30 : 0 ≤ S3 := Finset.sum_nonneg fun j _ => mul_nonneg (hT j) (sq_nonneg _)
  have hexp : ∑ j, ((1 + T j) * ((Z - τ j) ^ 2 + n j) - Z ^ 2) =
      σ * Z ^ 2 - 2 * Z * (q + p) + S2 + S3 + N + S4 := by
    rw [Finset.sum_congr rfl fun j _ => (by ring : (1 + T j) * ((Z - τ j) ^ 2 + n j) - Z ^ 2 =
      T j * Z ^ 2 - 2 * Z * (τ j + T j * τ j) + τ j ^ 2 + T j * τ j ^ 2 + n j + T j * n j)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum, hσ, hq, hN, hp, hS2, hS3, hS4]
  -- Cauchy–Schwarz
  have hcs1 : p ^ 2 ≤ σ * S3 :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun j _ => hT j)
      (fun j _ => mul_nonneg (hT j) (sq_nonneg _)) fun j _ => le_of_eq (by ring)
  have hcs2 : q ^ 2 ≤ d * S2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d))) (f := τ)
    simpa using this
  have hcs3 : q ^ 2 ≤ σ * N := 
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun j _ => hT j) (fun j _ => hn j)
      fun j _ => hτ j
  have h24 : S2 ≤ S4 := Finset.sum_le_sum fun j _ => hτ j
  -- the elementary inequality `q² ≤ S2 + S4 + γ σ N`
  have helem : q ^ 2 ≤ S2 + S4 + γ * (σ * N) := by
    have h1 : q ^ 2 / d ≤ S2 := by rw [div_le_iff₀ hd0]; linarith
    have h2 : γ * q ^ 2 ≤ γ * (σ * N) := mul_le_mul_of_nonneg_left hcs3 hγ0
    have h3 : q ^ 2 = q ^ 2 / d + q ^ 2 / d + γ * q ^ 2 := by rw [hγd]; ring
    linarith
  set R := S2 + S3 + S4 + γ * σ * N - (1 - γ * σ) * q ^ 2 with hR
  have hR1 : S3 + γ * σ * q ^ 2 ≤ R := by rw [hR]; nlinarith
  have hR0 : 0 ≤ R := le_trans (add_nonneg hS30 (mul_nonneg (mul_nonneg hγ0 hσ0) (sq_nonneg q))) hR1
  have hdisc : (p + γ * σ * q) ^ 2 ≤ (1 + γ) * σ * R := by
    have e1 : (p + γ * σ * q) ^ 2 ≤ (1 + γ) * (p ^ 2 + γ * σ ^ 2 * q ^ 2) := by
      nlinarith [mul_nonneg hγ0 (sq_nonneg (p - σ * q))]
    have e2 : (1 + γ) * (p ^ 2 + γ * σ ^ 2 * q ^ 2) ≤ (1 + γ) * (σ * (S3 + γ * σ * q ^ 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      nlinarith
    have e3 : (1 + γ) * (σ * (S3 + γ * σ * q ^ 2)) ≤ (1 + γ) * (σ * R) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hR1 hσ0) (by linarith)
    calc _ ≤ _ := e1
      _ ≤ _ := e2
      _ ≤ _ := e3
      _ = _ := by ring
  have hF := quadratic_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + γ) hσ0) hR0 hdisc Z
  rw [hexp]
  have : σ * Z ^ 2 - 2 * Z * (q + p) + S2 + S3 + N + S4 + Z ^ 2 -
      (1 - γ * σ) * ((Z - q) ^ 2 + N) = (1 + γ) * σ * Z ^ 2 - 2 * Z * (p + γ * σ * q) + R := by
    rw [hR]; ring
  linarith

/-- **The frames inequality for products of planes, in the cosines of the angles.** For `d ≥ 2`
modes with cosines `cⱼ ≠ 0`, `cⱼ² ≤ 1`, and `(cⱼ τⱼ)² ≤ nⱼ (1 - cⱼ²)`, with `Z = α + ∑ⱼ τⱼ` and
`Π = ∏ⱼ cⱼ`:
`α² + ∑ⱼ nⱼ - Π² (Z² + ∑ⱼ (((Z - τⱼ)² + nⱼ) / cⱼ² - Z²)) ≤ 2 (d-1)/d (1 - Π²) (α² + ∑ⱼ nⱼ)`. -/
private lemma frames_cos {d : ℕ} (hd : 2 ≤ d) {c τ n : Fin d → ℝ} (hc0 : ∀ j, c j ≠ 0)
    (hc1 : ∀ j, c j ^ 2 ≤ 1) (hn : ∀ j, 0 ≤ n j)
    (hτ : ∀ j, (c j * τ j) ^ 2 ≤ n j * (1 - c j ^ 2)) (α : ℝ) :
    α ^ 2 + ∑ j, n j - (∏ j, c j) ^ 2 * ((α + ∑ j, τ j) ^ 2 +
        ∑ j, (((α + ∑ j, τ j - τ j) ^ 2 + n j) / c j ^ 2 - (α + ∑ j, τ j) ^ 2)) ≤
      2 * ((d : ℝ) - 1) / d * (1 - (∏ j, c j) ^ 2) * (α ^ 2 + ∑ j, n j) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hcp : ∀ j, 0 < c j ^ 2 := fun j => by have := hc0 j; positivity
  set T : Fin d → ℝ := fun j => 1 / c j ^ 2 - 1 with hTdef
  have hT : ∀ j, 0 ≤ T j := fun j => by
    rw [hTdef]
    have : 1 ≤ 1 / c j ^ 2 := by rw [le_div_iff₀ (hcp j)]; linarith [hc1 j]
    linarith
  have hτT : ∀ j, τ j ^ 2 ≤ T j * n j := fun j => by
    have h := hτ j
    rw [hTdef]
    have e : (1 / c j ^ 2 - 1) * n j = n j * (1 - c j ^ 2) / c j ^ 2 := by
      have := hc0 j
      field_simp
    rw [e, le_div_iff₀ (hcp j)]
    nlinarith
  have hM := frames_tan hd hT hn hτT (α + ∑ j, τ j)
  rw [add_sub_cancel_right] at hM
  have hterm : ∀ j, (1 + T j) * ((α + ∑ j, τ j - τ j) ^ 2 + n j) - (α + ∑ j, τ j) ^ 2 =
      ((α + ∑ j, τ j - τ j) ^ 2 + n j) / c j ^ 2 - (α + ∑ j, τ j) ^ 2 := fun j => by
    rw [hTdef]
    have := hc0 j
    field_simp
    ring
  rw [Finset.sum_congr rfl fun j _ => hterm j] at hM
  set L := (α + ∑ j, τ j) ^ 2 +
    ∑ j, (((α + ∑ j, τ j - τ j) ^ 2 + n j) / c j ^ 2 - (α + ∑ j, τ j) ^ 2) with hL
  set Ps := (∏ j, c j) ^ 2 with hPs
  set M := α ^ 2 + ∑ j, n j with hMdef
  have hM0 : 0 ≤ M := add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => hn j)
  have hPs0 : 0 < Ps := by
    rw [hPs]
    exact pow_pos (abs_pos.2 (Finset.prod_ne_zero_iff.2 fun j _ => hc0 j)) 2 |>.trans_eq
      (sq_abs _)
  have hprod : ∏ j, (1 + T j) = 1 / Ps := by
    rw [hPs, ← Finset.prod_pow, one_div, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun j _ => by rw [hTdef]; ring
  have hσ : Ps * ∑ j, T j ≤ 1 - Ps := by
    have h := one_add_sum_le_prod_one_add Finset.univ hT
    rw [hprod] at h
    have h2 : Ps * (1 + ∑ j, T j) ≤ Ps * (1 / Ps) := mul_le_mul_of_nonneg_left h hPs0.le
    rw [mul_one_div_cancel hPs0.ne'] at h2
    linarith
  set γ : ℝ := ((d : ℝ) - 2) / d with hγ
  have hγ0 : 0 ≤ γ := div_nonneg (by linarith) hd0.le
  have hκ : 2 * ((d : ℝ) - 1) / d = 1 + γ := by rw [hγ]; field_simp; ring
  rw [hκ]
  have h1 : Ps * ((1 - γ * ∑ j, T j) * M) ≤ Ps * L := mul_le_mul_of_nonneg_left hM hPs0.le
  have h2 : (Ps - γ * (1 - Ps)) * M ≤ Ps * ((1 - γ * ∑ j, T j) * M) := by
    have : (Ps - γ * (1 - Ps)) ≤ Ps * (1 - γ * ∑ j, T j) := by nlinarith
    calc (Ps - γ * (1 - Ps)) * M ≤ Ps * (1 - γ * ∑ j, T j) * M :=
          mul_le_mul_of_nonneg_right this hM0
      _ = _ := by ring
  nlinarith

/-! ### Inner products of tangent vectors of elementary tensors -/

section ColInner

variable {m ρ : Type*} [Fintype m] [Unique ρ]

/-- The inner product of two matrices with one column. -/
private def colInner (A B : Matrix m ρ ℝ) : ℝ := (Aᵀ * B) default default

private lemma colInner_eq_sum (A B : Matrix m ρ ℝ) :
    colInner A B = ∑ i, A i default * B i default := by
  simp [colInner, Matrix.mul_apply]

private lemma colInner_comm (A B : Matrix m ρ ℝ) : colInner A B = colInner B A := by
  rw [colInner_eq_sum, colInner_eq_sum]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private lemma colInner_add_right (A B B' : Matrix m ρ ℝ) :
    colInner A (B + B') = colInner A B + colInner A B' := by
  simp [colInner, Matrix.mul_add]

private lemma colInner_sub_right (A B B' : Matrix m ρ ℝ) :
    colInner A (B - B') = colInner A B - colInner A B' := by
  simp [colInner, Matrix.mul_sub]

private lemma colInner_smul_right (a : ℝ) (A B : Matrix m ρ ℝ) :
    colInner A (a • B) = a * colInner A B := by
  simp [colInner, Matrix.mul_smul]

private lemma colInner_add_left (A A' B : Matrix m ρ ℝ) :
    colInner (A + A') B = colInner A B + colInner A' B := by
  rw [colInner_comm, colInner_add_right, colInner_comm B A, colInner_comm B A']

private lemma colInner_sub_left (A A' B : Matrix m ρ ℝ) :
    colInner (A - A') B = colInner A B - colInner A' B := by
  rw [colInner_comm, colInner_sub_right, colInner_comm B A, colInner_comm B A']

private lemma colInner_smul_left (a : ℝ) (A B : Matrix m ρ ℝ) :
    colInner (a • A) B = a * colInner A B := by
  rw [colInner_comm, colInner_smul_right, colInner_comm]

private lemma colInner_self_nonneg (A : Matrix m ρ ℝ) : 0 ≤ colInner A A := by
  rw [colInner_eq_sum]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

/-- The Cauchy–Schwarz inequality for columns. -/
private lemma colInner_sq_le (A B : Matrix m ρ ℝ) :
    colInner A B ^ 2 ≤ colInner A A * colInner B B := by
  rw [colInner_eq_sum, colInner_eq_sum, colInner_eq_sum]
  simp only [← sq]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

private lemma colInner_eq_zero {A B : Matrix m ρ ℝ} (h : Aᵀ * B = 0) :
    colInner A B = 0 := by
  rw [colInner, h, Matrix.zero_apply]

private lemma colInner_eq_one [DecidableEq ρ] {A : Matrix m ρ ℝ} (h : Aᵀ * A = 1) :
    colInner A A = 1 := by
  rw [colInner, h, Matrix.one_apply_eq]

private lemma transpose_mul_eq_zero_of_colInner {A B : Matrix m ρ ℝ} (h : colInner A B = 0) :
    Aᵀ * B = 0 := by
  ext i j
  obtain rfl : i = default := Subsingleton.elim _ _
  obtain rfl : j = default := Subsingleton.elim _ _
  exact h

end ColInner

private lemma sum_tangent_algebra (P a a' b b' : ℝ) (x y w : Fin d → ℝ) :
    a * a' * P + ∑ j, a * b' * (P * y j) + (∑ k, b * a' * (P * x k) +
        ∑ k, ∑ j, b * b' * (P * (if k = j then w k else x k * y j))) =
      P * ((a + b * ∑ k, x k) * (a' + b' * ∑ j, y j) + b * b' * ∑ k, (w k - x k * y k)) := by
  have h : ∀ k, ∑ j, b * b' * (P * (if k = j then w k else x k * y j)) =
      b * b' * P * (x k * ∑ j, y j) + b * b' * P * (w k - x k * y k) := fun k => by
    have e : ∀ j, b * b' * (P * (if k = j then w k else x k * y j)) =
        b * b' * P * (x k * y j) + (if k = j then b * b' * P * (w k - x k * y k) else 0) :=
      fun j => by
        split_ifs with hkj
        · subst hkj
          ring
        · ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      ← Finset.mul_sum]
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

section Elementary

variable {d : ℕ} {ι r : Fin d → Type*} [∀ k, Fintype (ι k)] [∀ k, Unique (r k)]

private lemma prod_eq_prod_mul_prod_div (c g : Fin d → ℝ) (hc : ∀ l, c l ≠ 0) :
    ∏ l, g l = (∏ l, c l) * ∏ l, g l / c l := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun l _ => by
    have := hc l
    field_simp

/-- The product of the inner products of the factors, both elementary tensors changed in the
same mode. -/
private lemma prod_colInner_update_update_self (U V : ∀ k, Matrix (ι k) (r k) ℝ)
    (hc : ∀ l, colInner (U l) (V l) ≠ 0) (k : Fin d) (A B : Matrix (ι k) (r k) ℝ) :
    ∏ l, colInner (Function.update U k A l) (Function.update V k B l) =
      (∏ l, colInner (U l) (V l)) * (colInner A B / colInner (U k) (V k)) := by
  refine (prod_eq_prod_mul_prod_div _ _ hc).trans ?_
  congr 1
  refine (Fintype.prod_eq_single k fun l hl => ?_).trans ?_
  · simp only [Function.update_of_ne hl]
    exact div_self (hc l)
  · simp only [Function.update_self]

/-- The product of the inner products of the factors, the elementary tensors changed in two
different modes. -/
private lemma prod_colInner_update_update_of_ne (U V : ∀ k, Matrix (ι k) (r k) ℝ)
    (hc : ∀ l, colInner (U l) (V l) ≠ 0) {k j : Fin d} (hkj : k ≠ j)
    (A : Matrix (ι k) (r k) ℝ) (B : Matrix (ι j) (r j) ℝ) :
    ∏ l, colInner (Function.update U k A l) (Function.update V j B l) =
      (∏ l, colInner (U l) (V l)) *
        (colInner A (V k) / colInner (U k) (V k) * (colInner (U j) B / colInner (U j) (V j))) := by
  refine (prod_eq_prod_mul_prod_div _ _ hc).trans ?_
  congr 1
  refine (Fintype.prod_eq_mul k j hkj fun l hl => ?_).trans ?_
  · simp only [Function.update_of_ne hl.1, Function.update_of_ne hl.2]
    exact div_self (hc l)
  · simp only [Function.update_self, Function.update_of_ne hkj, Function.update_of_ne hkj.symm]

variable [∀ k, Fintype (r k)]

/-- The inner product of two elementary tensors in terms of `colInner`. -/
private lemma inner_tucker_tucker_colInner (C C' : Tensor r) (U V : ∀ k, Matrix (ι k) (r k) ℝ) :
    ⟪tucker C U, tucker C' V⟫ = C default * C' default * ∏ k, colInner (U k) (V k) :=
  inner_tucker_tucker_of_unique C C' U V

/-- **The inner product of two tangent vectors of elementary tensors.** For
`z = Ċ ×ₖ Uₖ + ∑ₖ C ×ₖ Aₖ ×_{l ≠ k} Uₗ` and `t = Ċ' ×ₖ Vₖ + ∑ₖ C' ×ₖ Bₖ ×_{l ≠ k} Vₗ` with
`cₖ = UₖᵀVₖ ≠ 0`. -/
private lemma inner_tangent_tangent (U V A B : ∀ k, Matrix (ι k) (r k) ℝ)
    (Cd C Cd' C' : Tensor r) (hc : ∀ k, colInner (U k) (V k) ≠ 0) :
    ⟪tucker Cd U + ∑ k, tucker C (Function.update U k (A k)),
        tucker Cd' V + ∑ j, tucker C' (Function.update V j (B j))⟫ =
      (∏ k, colInner (U k) (V k)) *
        ((Cd default + C default * ∑ k, colInner (A k) (V k) / colInner (U k) (V k)) *
          (Cd' default + C' default * ∑ k, colInner (U k) (B k) / colInner (U k) (V k)) +
          C default * C' default * ∑ k, (colInner (A k) (B k) / colInner (U k) (V k) -
            colInner (A k) (V k) / colInner (U k) (V k) *
              (colInner (U k) (B k) / colInner (U k) (V k)))) := by
  have h1 : ∀ j, ∏ l, colInner (U l) (Function.update V j (B j) l) =
      (∏ l, colInner (U l) (V l)) * (colInner (U j) (B j) / colInner (U j) (V j)) := fun j => by
    have h := prod_colInner_update_update_self U V hc j (U j) (B j)
    rwa [Function.update_eq_self] at h
  have h2 : ∀ k, ∏ l, colInner (Function.update U k (A k) l) (V l) =
      (∏ l, colInner (U l) (V l)) * (colInner (A k) (V k) / colInner (U k) (V k)) := fun k => by
    have h := prod_colInner_update_update_self U V hc k (A k) (V k)
    rwa [Function.update_eq_self] at h
  have h3 : ∀ k j, ∏ l, colInner (Function.update U k (A k) l) (Function.update V j (B j) l) =
      (∏ l, colInner (U l) (V l)) * (if k = j then colInner (A k) (B k) / colInner (U k) (V k)
        else colInner (A k) (V k) / colInner (U k) (V k) *
          (colInner (U j) (B j) / colInner (U j) (V j))) := fun k j => by
    by_cases hkj : k = j
    · subst hkj
      simp only [↓reduceIte]
      exact prod_colInner_update_update_self U V hc k (A k) (B k)
    · simp only [hkj, ↓reduceIte]
      exact prod_colInner_update_update_of_ne U V hc hkj (A k) (B j)
  rw [inner_add_left, inner_add_right, inner_add_right, sum_inner, sum_inner]
  simp only [inner_sum, inner_tucker_tucker_colInner, h1, h2, h3]
  exact sum_tangent_algebra _ _ _ _ _ _ _ _

variable [∀ k, DecidableEq (r k)]

/-- The squared norm of a tangent vector of an elementary tensor in the gauge `Uₖᵀ Aₖ = 0`. -/
private lemma norm_sq_tangent {U A : ∀ k, Matrix (ι k) (r k) ℝ} (hU : ∀ k, (U k)ᵀ * U k = 1)
    (hA : ∀ k, (U k)ᵀ * A k = 0) (Cd C : Tensor r) :
    ‖tucker Cd U + ∑ k, tucker C (Function.update U k (A k))‖ ^ 2 =
      Cd default ^ 2 + C default ^ 2 * ∑ k, colInner (A k) (A k) := by
  have h1 : ∀ k, colInner (U k) (U k) = 1 := fun k => colInner_eq_one (hU k)
  have h2 : ∀ k, colInner (U k) (A k) = 0 := fun k => colInner_eq_zero (hA k)
  have h3 : ∀ k, colInner (A k) (U k) = 0 := fun k => by rw [colInner_comm, h2]
  rw [← real_inner_self_eq_norm_sq,
    inner_tangent_tangent U U A A Cd C Cd C fun k => by rw [h1]; exact one_ne_zero]
  simp only [h1, h2, h3, Finset.prod_const_one, div_one, Finset.sum_const_zero, mul_zero,
    add_zero, sub_zero, one_mul]
  ring

omit [∀ k, Fintype (ι k)] [∀ k, DecidableEq (r k)] in
/-- A Tucker tensor whose core with one entry vanishes is zero. -/
private lemma tucker_eq_zero_of_default {C : Tensor r} (h : C default = 0)
    (U : ∀ k, Matrix (ι k) (r k) ℝ) : tucker C U = 0 := by
  ext x
  rw [tucker_apply_of_unique, h, mul_zero]
  rfl

omit [∀ k, Fintype (ι k)] [∀ k, Unique (r k)] [∀ k, Fintype (r k)] [∀ k, DecidableEq (r k)] in
/-- The inner products of the columns of one mode with the column of the nearest tangent
vector. -/
private lemma colInner_nearest {m ρ : Type*} [Fintype m] [Unique ρ] {U V A G : Matrix m ρ ℝ}
    {a c τ n u P Z : ℝ} (hUU : colInner U U = 1) (hVV : colInner V V = 1)
    (hUA : colInner U A = 0) (hUV : colInner U V = c) (hτ : a * colInner A V = c * τ)
    (hn : a ^ 2 * colInner A A = n) (hu : u * c = P)
    (hG : G = u • ((Z - τ) • U + a • A) - (P * Z) • V) :
    colInner V G = 0 ∧ colInner U G = u * (Z - τ) - P * Z * c ∧
      a * colInner A G = u * n - P * Z * (c * τ) ∧
      colInner G G = u ^ 2 * ((Z - τ) ^ 2 + n) - P ^ 2 * Z ^ 2 := by
  have hAU : colInner A U = 0 := by rw [colInner_comm, hUA]
  have hVU : colInner V U = c := by rw [colInner_comm, hUV]
  have hVA : colInner V A = colInner A V := colInner_comm _ _
  subst hG
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [colInner_sub_right, colInner_add_right, colInner_smul_right, hVU, hVA, hVV]
    linear_combination u * hτ + Z * hu
  · simp only [colInner_sub_right, colInner_add_right, colInner_smul_right, hUU, hUA, hUV]
    ring
  · simp only [colInner_sub_right, colInner_add_right, colInner_smul_right, hAU]
    linear_combination u * hn - P * Z * hτ
  · simp only [colInner_sub_right, colInner_add_right, colInner_smul_right, colInner_sub_left,
      colInner_add_left, colInner_smul_left, hUU, hUA, hAU, hUV, hVU, hVA, hVV]
    linear_combination u ^ 2 * hn - 2 * u * P * Z * hτ - 2 * P * Z ^ 2 * hu

/-- **A tangent vector at `Y` near a tangent vector at `X`, elementary tensors.** For a tangent
vector `z = Ċ ×ₖ Uₖ + ∑ₖ C ×ₖ Aₖ ×_{l ≠ k} Uₗ` at `X = C ×ₖ Uₖ` (`Uₖᵀ Aₖ = 0`) there is a tangent
vector `t` at `Y = C' ×ₖ Vₖ` whose squared distance to `z` is the left-hand side of the frames
inequality, with the cosines `cₖ = Uₖᵀ Vₖ ≠ 0`. -/
private lemma exists_tangent_norm_sub_sq_eq {U V A : ∀ k, Matrix (ι k) (r k) ℝ}
    (hU : ∀ k, (U k)ᵀ * U k = 1) (hV : ∀ k, (V k)ᵀ * V k = 1) (hA : ∀ k, (U k)ᵀ * A k = 0)
    (Cd C : Tensor r) {C' : Tensor r} (hC' : C' default ≠ 0) {c τ n : Fin d → ℝ}
    (hc : ∀ k, c k ≠ 0) (hcU : ∀ k, colInner (U k) (V k) = c k)
    (hτ : ∀ k, C default * colInner (A k) (V k) = c k * τ k)
    (hn : ∀ k, C default ^ 2 * colInner (A k) (A k) = n k) :
    ∃ (Cd' : Tensor r) (B : ∀ k, Matrix (ι k) (r k) ℝ), (∀ k, (V k)ᵀ * B k = 0) ∧
      ‖tucker Cd U + ∑ k, tucker C (Function.update U k (A k)) -
          (tucker Cd' V + ∑ k, tucker C' (Function.update V k (B k)))‖ ^ 2 =
        Cd default ^ 2 + ∑ k, n k - (∏ k, c k) ^ 2 * ((Cd default + ∑ k, τ k) ^ 2 +
          ∑ k, (((Cd default + ∑ k, τ k - τ k) ^ 2 + n k) / c k ^ 2 -
            (Cd default + ∑ k, τ k) ^ 2)) := by
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = ∏ k, c k := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = Cd default + ∑ k, τ k := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : Fin d → ℝ, ∀ k, u k = P / c k := ⟨_, fun _ => rfl⟩
  have huc : ∀ k, u k * c k = P := fun k => by rw [hu, div_mul_cancel₀ _ (hc k)]
  obtain ⟨G, hG⟩ : ∃ G : ∀ k, Matrix (ι k) (r k) ℝ,
      ∀ k, G k = u k • ((Z - τ k) • U k + C default • A k) - (P * Z) • V k := ⟨_, fun _ => rfl⟩
  obtain ⟨Cd', hCd'⟩ : ∃ Cd' : Tensor r, Cd' default = P * Z :=
    ⟨WithLp.toLp 2 fun _ => P * Z, rfl⟩
  have hfacts := fun k => colInner_nearest (Z := Z) (colInner_eq_one (hU k))
    (colInner_eq_one (hV k)) (colInner_eq_zero (hA k)) (hcU k) (hτ k) (hn k) (huc k) (hG k)
  have hB : ∀ k, (V k)ᵀ * ((C' default)⁻¹ • G k) = 0 := fun k =>
    transpose_mul_eq_zero_of_colInner (by rw [colInner_smul_right, (hfacts k).1, mul_zero])
  refine ⟨Cd', fun k => (C' default)⁻¹ • G k, hB, ?_⟩
  have hcU' : ∀ k, colInner (U k) (V k) ≠ 0 := fun k => by rw [hcU]; exact hc k
  rw [norm_sub_sq_real, norm_sq_tangent hU hA, norm_sq_tangent hV hB,
    inner_tangent_tangent U V A _ Cd C Cd' C' hcU']
  simp only [hcU, hCd', ← hP, ← hZ, colInner_smul_right, colInner_smul_left]
  have s0 : C default ^ 2 * ∑ k, colInner (A k) (A k) = ∑ k, n k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => hn k
  have s1 : C default * ∑ k, colInner (A k) (V k) / c k = ∑ k, τ k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by
      rw [← mul_div_assoc, hτ k, mul_div_cancel_left₀ _ (hc k)]
  have s2 : C' default * ∑ k, (C' default)⁻¹ * colInner (U k) (G k) / c k =
      ∑ k, (u k * (Z - τ k) - P * Z * c k) / c k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by
      rw [← (hfacts k).2.1]
      field_simp
  have s3 : C default * C' default * ∑ k, ((C' default)⁻¹ * colInner (A k) (G k) / c k -
      colInner (A k) (V k) / c k * ((C' default)⁻¹ * colInner (U k) (G k) / c k)) =
      ∑ k, ((u k * n k - P * Z * (c k * τ k)) / c k -
        τ k * ((u k * (Z - τ k) - P * Z * c k) / c k)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by
      have e1 : C default * C' default * ((C' default)⁻¹ * colInner (A k) (G k) / c k -
          colInner (A k) (V k) / c k * ((C' default)⁻¹ * colInner (U k) (G k) / c k)) =
          C default * colInner (A k) (G k) / c k -
            C default * colInner (A k) (V k) / c k * (colInner (U k) (G k) / c k) := by
        have := hc k
        field_simp
      rw [e1, (hfacts k).2.2.1, hτ k, (hfacts k).2.1, mul_div_cancel_left₀ _ (hc k)]
  have s4 : C' default ^ 2 * ∑ k, (C' default)⁻¹ * ((C' default)⁻¹ * colInner (G k) (G k)) =
      ∑ k, (u k ^ 2 * ((Z - τ k) ^ 2 + n k) - P ^ 2 * Z ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by
      rw [← (hfacts k).2.2.2]
      field_simp
  have hb : ∑ k, (u k ^ 2 * ((Z - τ k) ^ 2 + n k) - P ^ 2 * Z ^ 2) =
      P ^ 2 * ∑ k, (((Z - τ k) ^ 2 + n k) / c k ^ 2 - Z ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by
      have := hc k
      rw [hu k]
      field_simp
  have hef : Z * ∑ k, (u k * (Z - τ k) - P * Z * c k) / c k +
      ∑ k, ((u k * n k - P * Z * (c k * τ k)) / c k -
        τ k * ((u k * (Z - τ k) - P * Z * c k) / c k)) =
      P * ∑ k, (((Z - τ k) ^ 2 + n k) / c k ^ 2 - Z ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by
      have := hc k
      rw [hu k]
      field_simp
      ring
  rw [s0, s1, s2, s3, s4, ← hZ]
  linear_combination (-2 * P) * hef + hb

/-! ### The distance of two elementary tensors and the angles of their factors -/

variable {U U' : ∀ k, Matrix (ι k) (r k) ℝ} {C C' : Tensor r}

/-- **The norm of an elementary tensor with unit columns**: `‖C ×ₖ Uₖ‖² = C²` for a core with
one entry. -/
theorem norm_tucker_sq_of_unique (hU : ∀ k, (U k)ᵀ * U k = 1) (C : Tensor r) :
    ‖tucker C U‖ ^ 2 = C default ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_tucker_tucker_colInner,
    Finset.prod_congr rfl fun k _ => colInner_eq_one (hU k), Finset.prod_const_one]
  ring

omit [∀ k, DecidableEq (r k)] in
/-- **The inner product of two tangent vectors of elementary tensors.** For
`z = Ċ ×ₖ Uₖ + ∑ₖ C ×ₖ Aₖ ×_{l ≠ k} Uₗ` and `t = Ċ' ×ₖ Vₖ + ∑ₖ C' ×ₖ Bₖ ×_{l ≠ k} Vₗ` with cores
with one entry and `cₖ = Uₖᵀ Vₖ ≠ 0`:
`⟪z, t⟫ = (∏ₖ cₖ) ((Ċ + C ∑ₖ AₖᵀVₖ / cₖ) (Ċ' + C' ∑ₖ UₖᵀBₖ / cₖ)
  + C C' ∑ₖ (AₖᵀBₖ / cₖ - (AₖᵀVₖ / cₖ) (UₖᵀBₖ / cₖ)))`. -/
theorem inner_tucker_add_sum_update_of_unique (U V A B : ∀ k, Matrix (ι k) (r k) ℝ)
    (Cd C Cd' C' : Tensor r) (hc : ∀ k, ((U k)ᵀ * V k) default default ≠ 0) :
    ⟪tucker Cd U + ∑ k, tucker C (Function.update U k (A k)),
        tucker Cd' V + ∑ j, tucker C' (Function.update V j (B j))⟫ =
      (∏ k, ((U k)ᵀ * V k) default default) *
        ((Cd default + C default *
            ∑ k, ((A k)ᵀ * V k) default default / ((U k)ᵀ * V k) default default) *
          (Cd' default + C' default *
            ∑ k, ((U k)ᵀ * B k) default default / ((U k)ᵀ * V k) default default) +
          C default * C' default *
            ∑ k, (((A k)ᵀ * B k) default default / ((U k)ᵀ * V k) default default -
              ((A k)ᵀ * V k) default default / ((U k)ᵀ * V k) default default *
                (((U k)ᵀ * B k) default default / ((U k)ᵀ * V k) default default))) :=
  inner_tangent_tangent U V A B Cd C Cd' C' hc

/-- **The norm of a tangent vector of an elementary tensor.** For unit columns `Uₖ` and
`Uₖᵀ Aₖ = 0`: `‖Ċ ×ₖ Uₖ + ∑ₖ C ×ₖ Aₖ ×_{l ≠ k} Uₗ‖² = Ċ² + C² ∑ₖ ‖Aₖ‖²` for cores with one
entry. -/
theorem norm_sq_tucker_add_sum_update_of_unique {A : ∀ k, Matrix (ι k) (r k) ℝ}
    (hU : ∀ k, (U k)ᵀ * U k = 1) (hA : ∀ k, (U k)ᵀ * A k = 0) (Cd C : Tensor r) :
    ‖tucker Cd U + ∑ k, tucker C (Function.update U k (A k))‖ ^ 2 =
      Cd default ^ 2 + C default ^ 2 * ∑ k, ((A k)ᵀ * A k) default default :=
  norm_sq_tangent hU hA Cd C

/-- **The distance of two elementary tensors is bounded from below by the angles of their
factors.** For `X = C ×ₖ Uₖ` and `Y = C' ×ₖ U'ₖ` with cores with one entry and unit columns
`Uₖ`, `U'ₖ`: `(1 - ∏ₖ (Uₖᵀ U'ₖ)²) ‖X‖² ≤ ‖Y - X‖²`, since `Y` lies in the range of the projector
onto the line spanned by `⊗ₖ U'ₖ`. -/
theorem one_sub_prod_sq_mul_norm_tucker_sq_le (hU : ∀ k, (U k)ᵀ * U k = 1)
    (hU' : ∀ k, (U' k)ᵀ * U' k = 1) (C C' : Tensor r) :
    (1 - (∏ k, ((U k)ᵀ * U' k) default default) ^ 2) * ‖tucker C U‖ ^ 2 ≤
      ‖tucker C' U' - tucker C U‖ ^ 2 := by
  have h1 := norm_tucker_sq_of_unique hU C
  have h2 := norm_tucker_sq_of_unique hU' C'
  have h3 : ⟪tucker C' U', tucker C U⟫ =
      C' default * C default * ∏ k, colInner (U k) (U' k) := by
    rw [inner_tucker_tucker_colInner]
    exact congrArg _ (Finset.prod_congr rfl fun k _ => colInner_comm _ _)
  rw [norm_sub_sq_real, h1, h2, h3]
  change (1 - (∏ k, colInner (U k) (U' k)) ^ 2) * C default ^ 2 ≤ _
  nlinarith [sq_nonneg (C' default - C default * ∏ k, colInner (U k) (U' k))]

/-! ### The frames inequality and the Lipschitz bound -/

variable {s s' : Fin d → Type*} [∀ k, Fintype (s k)] [∀ k, Fintype (s' k)]
  {W : ∀ k, Matrix (∀ j : {j : Fin d // j ≠ k}, ι j) (s k) ℝ}
  {W' : ∀ k, Matrix (∀ j : {j : Fin d // j ≠ k}, ι j) (s' k) ℝ}

/-- **The normal component at `Y` of a tangent vector at `X`, tensors of rank one, in the
angles of the factors.** Let `X = C ×ₖ Uₖ` and `Y = C' ×ₖ U'ₖ ≠ 0` be Tucker tensors with `d ≥ 2`
modes whose cores have one entry (elementary tensors), with unit columns `Uₖ`, `U'ₖ` and co-range
bases `W`, `W'` as in `tuckerTangentProj_eq_starProjection`. If `Z` is tangent at `X`,
`P(X) Z = Z`, then `‖Z - P(Y) Z‖² ≤ 2 (d - 1)/d (1 - ∏ₖ (Uₖᵀ U'ₖ)²) ‖Z‖²`. -/
theorem norm_sub_tuckerTangentProj_apply_sq_le_of_unique (hd : 2 ≤ d)
    (hU : ∀ k, (U k)ᵀ * U k = 1)
    (hWX : ∀ k, actOn (· ≠ k) (W k * (W k)ᵀ) (tucker C U) = tucker C U)
    (hWB : ∀ k, ∃ B : Matrix _ (s k) ℝ, W k = unfold (· ≠ k) (tucker C U) * B)
    (hU' : ∀ k, (U' k)ᵀ * U' k = 1)
    (hWX' : ∀ k, actOn (· ≠ k) (W' k * (W' k)ᵀ) (tucker C' U') = tucker C' U')
    (hWB' : ∀ k, ∃ B : Matrix _ (s' k) ℝ, W' k = unfold (· ≠ k) (tucker C' U') * B)
    (hY : tucker C' U' ≠ 0) {Z : Tensor ι} (hZ : tuckerTangentProj U 1 W Z = Z) :
    ‖Z - tuckerTangentProj U' 1 W' Z‖ ^ 2 ≤
      2 * ((d : ℝ) - 1) / d * (1 - (∏ k, ((U k)ᵀ * U' k) default default) ^ 2) * ‖Z‖ ^ 2 := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hP' := isOrthProj_tuckerTangentProj hU' IsOrthProj.one hWX' hWB'
  have hC' : C' default ≠ 0 := fun h => hY (tucker_eq_zero_of_default h U')
  change _ ≤ 2 * ((d : ℝ) - 1) / d * (1 - (∏ k, colInner (U k) (U' k)) ^ 2) * ‖Z‖ ^ 2
  by_cases hc : ∀ k, colInner (U k) (U' k) ≠ 0
  · obtain ⟨Cd, -, A, hA, rfl⟩ := (mem_tuckerTangentSpace_iff hU IsOrthProj.one hWX hWB Z).1
      ((tuckerTangentProj_eq_self_iff hU IsOrthProj.one hWX hWB Z).1 hZ)
    have hc1 : ∀ k, colInner (U k) (U' k) ^ 2 ≤ 1 := fun k => by
      have := colInner_sq_le (U k) (U' k)
      rwa [colInner_eq_one (hU k), colInner_eq_one (hU' k), mul_one] at this
    have hτ : ∀ k, C default * colInner (A k) (U' k) = colInner (U k) (U' k) *
        (C default * colInner (A k) (U' k) / colInner (U k) (U' k)) := fun k => by
      have := hc k
      field_simp
    have hAU : ∀ k, colInner (A k) (U k) = 0 := fun k => by
      rw [colInner_comm, colInner_eq_zero (hA k)]
    have hcs : ∀ k, (colInner (U k) (U' k) *
        (C default * colInner (A k) (U' k) / colInner (U k) (U' k))) ^ 2 ≤
        C default ^ 2 * colInner (A k) (A k) * (1 - colInner (U k) (U' k) ^ 2) := fun k => by
      rw [← hτ k]
      have h := colInner_sq_le (A k) (U' k - colInner (U k) (U' k) • U k)
      simp only [colInner_sub_right, colInner_smul_right, colInner_sub_left, colInner_smul_left,
        hAU k, colInner_eq_one (hU k), colInner_eq_one (hU' k), colInner_comm (U' k) (U k),
        mul_zero, sub_zero, mul_one] at h
      have e : 1 - colInner (U k) (U' k) * colInner (U k) (U' k) -
          colInner (U k) (U' k) * (colInner (U k) (U' k) - colInner (U k) (U' k)) =
          1 - colInner (U k) (U' k) ^ 2 := by ring
      rw [e] at h
      calc (C default * colInner (A k) (U' k)) ^ 2
          = C default ^ 2 * colInner (A k) (U' k) ^ 2 := by ring
        _ ≤ C default ^ 2 * (colInner (A k) (A k) * (1 - colInner (U k) (U' k) ^ 2)) :=
            mul_le_mul_of_nonneg_left h (sq_nonneg _)
        _ = _ := by ring
    obtain ⟨Cd', B, hB, hnorm⟩ := exists_tangent_norm_sub_sq_eq hU hU' hA Cd C hC' hc
      (fun _ => rfl) hτ fun _ => rfl
    have ht : tuckerTangentProj U' 1 W' (tucker Cd' U' +
        ∑ k, tucker C' (Function.update U' k (B k))) =
        tucker Cd' U' + ∑ k, tucker C' (Function.update U' k (B k)) :=
      (tuckerTangentProj_eq_self_iff hU' IsOrthProj.one hWX' hWB' _).2
        (Submodule.subset_span ⟨Cd', rfl, B, hB, rfl⟩)
    have hpyth := hP'.norm_sub_apply_sq (tucker Cd U + ∑ k, tucker C (Function.update U k (A k)))
      (tucker Cd' U' + ∑ k, tucker C' (Function.update U' k (B k)))
    rw [ht, hnorm] at hpyth
    have hfr := frames_cos hd hc hc1
      (fun k => mul_nonneg (sq_nonneg _) (colInner_self_nonneg (A k))) hcs (Cd default)
    have hz : ‖tucker Cd U + ∑ k, tucker C (Function.update U k (A k))‖ ^ 2 =
        Cd default ^ 2 + ∑ k, C default ^ 2 * colInner (A k) (A k) := by
      rw [norm_sq_tangent hU hA, Finset.mul_sum]
    have h0 := sq_nonneg ‖tuckerTangentProj U' 1 W' (tucker Cd U +
      ∑ k, tucker C (Function.update U k (A k)) - (tucker Cd' U' +
      ∑ k, tucker C' (Function.update U' k (B k))))‖
    rw [hz]
    linarith
  · simp only [not_forall, not_not] at hc
    obtain ⟨k, hk⟩ := hc
    rw [Finset.prod_eq_zero (Finset.mem_univ k) hk]
    have hpyth := hP'.norm_sub_apply_sq Z 0
    simp only [map_zero, sub_zero] at hpyth
    have h1 : (1 : ℝ) ≤ 2 * ((d : ℝ) - 1) / d := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    have h2 : ‖Z - tuckerTangentProj U' 1 W' Z‖ ^ 2 ≤ ‖Z‖ ^ 2 := by
      rw [hpyth]
      exact le_add_of_nonneg_right (sq_nonneg _)
    calc ‖Z - tuckerTangentProj U' 1 W' Z‖ ^ 2 ≤ ‖Z‖ ^ 2 := h2
      _ ≤ 2 * ((d : ℝ) - 1) / d * ‖Z‖ ^ 2 := le_mul_of_one_le_left (sq_nonneg _) h1
      _ = _ := by ring

/-- **The sharp Lipschitz bound of the tangent projector for tensors of rank one.** Let
`X = C ×ₖ Uₖ ≠ 0` and `Y = C' ×ₖ U'ₖ ≠ 0` be Tucker tensors with `d ≥ 2` modes whose cores have
one entry (tensors of multilinear rank `(1, …, 1)`), with unit columns `Uₖ`, `U'ₖ` and co-range
bases `W`, `W'` as in `tuckerTangentProj_eq_starProjection`. Then for every tensor `B`:
`‖P(Y) B - P(X) B‖ ≤ √(2 (d - 1)/d) ‖X‖⁻¹ ‖Y - X‖ ‖B‖`. No smallness of `‖Y - X‖` is needed. The
norm `‖X‖` is the nonzero singular value of every matricization of `X`. -/
theorem norm_tuckerTangentProj_sub_le_of_unique (hd : 2 ≤ d) (hU : ∀ k, (U k)ᵀ * U k = 1)
    (hWX : ∀ k, actOn (· ≠ k) (W k * (W k)ᵀ) (tucker C U) = tucker C U)
    (hWB : ∀ k, ∃ B : Matrix _ (s k) ℝ, W k = unfold (· ≠ k) (tucker C U) * B)
    (hX : tucker C U ≠ 0) (hU' : ∀ k, (U' k)ᵀ * U' k = 1)
    (hWX' : ∀ k, actOn (· ≠ k) (W' k * (W' k)ᵀ) (tucker C' U') = tucker C' U')
    (hWB' : ∀ k, ∃ B : Matrix _ (s' k) ℝ, W' k = unfold (· ≠ k) (tucker C' U') * B)
    (hY : tucker C' U' ≠ 0) (B : Tensor ι) :
    ‖tuckerTangentProj U' 1 W' B - tuckerTangentProj U 1 W B‖ ≤
      √(2 * ((d : ℝ) - 1) / d) * ‖tucker C U‖⁻¹ * ‖tucker C' U' - tucker C U‖ * ‖B‖ := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hP := isOrthProj_tuckerTangentProj hU IsOrthProj.one hWX hWB
  have hP' := isOrthProj_tuckerTangentProj hU' IsOrthProj.one hWX' hWB'
  have hXn : 0 < ‖tucker C U‖ := norm_pos_iff.2 hX
  have hκ0 : 0 ≤ 2 * ((d : ℝ) - 1) / d := div_nonneg (by linarith) (by linarith)
  have hdist := one_sub_prod_sq_mul_norm_tucker_sq_le hU hU' C C'
  have hsymm : ∏ k, ((U' k)ᵀ * U k) default default = ∏ k, ((U k)ᵀ * U' k) default default :=
    Finset.prod_congr rfl fun k _ => colInner_comm (U' k) (U k)
  have hstep : ∀ a b : ℝ, 0 ≤ b →
      a ^ 2 ≤ 2 * ((d : ℝ) - 1) / d * (1 - (∏ k, ((U k)ᵀ * U' k) default default) ^ 2) * b ^ 2 →
      a ≤ √(2 * ((d : ℝ) - 1) / d) * ‖tucker C U‖⁻¹ * ‖tucker C' U' - tucker C U‖ * b := by
    intro a b hb h
    have hle : 1 - (∏ k, ((U k)ᵀ * U' k) default default) ^ 2 ≤
        ‖tucker C U‖⁻¹ ^ 2 * ‖tucker C' U' - tucker C U‖ ^ 2 := by
      rw [inv_pow, inv_mul_eq_div, le_div_iff₀ (pow_pos hXn 2)]
      exact hdist
    refine (abs_le_of_sq_le_sq' ?_ (by positivity)).2
    calc a ^ 2 ≤ 2 * ((d : ℝ) - 1) / d *
          (1 - (∏ k, ((U k)ᵀ * U' k) default default) ^ 2) * b ^ 2 := h
      _ ≤ 2 * ((d : ℝ) - 1) / d *
          (‖tucker C U‖⁻¹ ^ 2 * ‖tucker C' U' - tucker C U‖ ^ 2) * b ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hκ0) (sq_nonneg b)
      _ = _ := by
          rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hκ0]
          ring
  exact hP.norm_sub_apply_le_of_norm_sub_apply_le hP' (by positivity)
    (fun z hz => hstep _ _ (norm_nonneg z)
      (norm_sub_tuckerTangentProj_apply_sq_le_of_unique hd hU hWX hWB hU' hWX' hWB' hY hz))
    (fun z hz => hstep _ _ (norm_nonneg z) (by
      have h := norm_sub_tuckerTangentProj_apply_sq_le_of_unique hd hU' hWX' hWB' hU hWX hWB
        hX hz
      rwa [hsymm] at h)) B

/-! ### Co-range bases of elementary tensors -/

/-- The co-range basis of the elementary tensor `⊗ₖ uₖ` in mode `k`: the column `⊗_{j ≠ k} uⱼ`. -/
private def coW (u : ∀ k, Matrix (ι k) (r k) ℝ) (k : Fin d) :
    Matrix (∀ j : {j : Fin d // j ≠ k}, ι j) (Fin 1) ℝ :=
  Matrix.of fun a _ => ∏ j : {j : Fin d // j ≠ k}, u j (a j) default

/-- The row `c uₖᵀ`, indexed by the multi-indices of the complement of the modes `≠ k`. -/
private def coR (u : ∀ k, Matrix (ι k) (r k) ℝ) (c : ℝ) (k : Fin d) :
    Matrix (Fin 1) (∀ j : {j : Fin d // ¬ j ≠ k}, ι j) ℝ :=
  Matrix.of fun _ b => c * u k (compEquiv k b) default

omit [∀ k, Fintype (r k)] in
private lemma coW_transpose_mul_self {u : ∀ k, Matrix (ι k) (r k) ℝ}
    (hu : ∀ k, (u k)ᵀ * u k = 1) (k : Fin d) : (coW u k)ᵀ * coW u k = 1 := by
  ext i j
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  rw [Matrix.mul_apply, Matrix.one_apply_eq]
  simp only [Matrix.transpose_apply, coW, Matrix.of_apply, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (j : {j : Fin d // j ≠ k}) c => u j c default * u j c default)]
  exact Finset.prod_eq_one fun j _ => by
    rw [← colInner_eq_sum, colInner_eq_one (hu j)]

omit [∀ k, Fintype (r k)] in
private lemma coR_mul_transpose {u : ∀ k, Matrix (ι k) (r k) ℝ} (hu : ∀ k, (u k)ᵀ * u k = 1)
    (c c' : ℝ) (k : Fin d) :
    coR u c k * (coR u c' k)ᵀ = (c * c') • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  calc ∑ b, coR u c k 0 b * (coR u c' k)ᵀ b 0
      = ∑ a, c * c' * (u k a default * u k a default) :=
        Fintype.sum_equiv (compEquiv k) _ _ fun b => by
          simp only [Matrix.transpose_apply, coR, Matrix.of_apply]
          ring
    _ = c * c' := by
        rw [← Finset.mul_sum, ← colInner_eq_sum, colInner_eq_one (hu k), mul_one]

omit [∀ k, Fintype (ι k)] [∀ k, DecidableEq (r k)] in
/-- The unfolding of an elementary tensor with respect to the modes `≠ k` is the product of the
column `⊗_{j ≠ k} uⱼ` and the row `C uₖᵀ`. -/
private lemma unfold_tucker_of_unique (u : ∀ k, Matrix (ι k) (r k) ℝ) (C : Tensor r) (k : Fin d) :
    unfold (· ≠ k) (tucker C u) = coW u k * coR u (C default) k := by
  ext a b
  have hk : merge (· ≠ k) a b k = compEquiv k b := by simp [merge, compEquiv]
  have hj : ∀ j : {j : Fin d // j ≠ k}, merge (· ≠ k) a b j = a j := fun j => by
    simp [merge, j.2]
  have hsplit := Fintype.prod_subtype_mul_prod_subtype (fun j : Fin d => j ≠ k)
    (fun j => u j (merge (· ≠ k) a b j) default)
  have huniq : ∏ i : {x : Fin d // ¬ x ≠ k}, u i (merge (· ≠ k) a b i) default =
      u k (compEquiv k b) default := by
    rw [Fintype.prod_eq_single ⟨k, not_not.2 rfl⟩ fun x hx =>
      absurd (Subtype.ext (not_not.1 x.2)) hx]
    exact congrArg (fun t => u k t default) hk
  have hfirst : ∏ i : {x : Fin d // x ≠ k}, u i (merge (· ≠ k) a b i) default =
      ∏ i : {x : Fin d // x ≠ k}, u i (a i) default :=
    Finset.prod_congr rfl fun j _ => by rw [hj j]
  rw [unfold_apply, tucker_apply_of_unique, Matrix.mul_apply, Fin.sum_univ_one]
  change (∏ j, u j (merge (· ≠ k) a b j) default) * C default =
    (∏ j : {j : Fin d // j ≠ k}, u j (a j) default) * (C default * u k (compEquiv k b) default)
  rw [← hsplit, huniq, hfirst]
  ring

/-- **Co-range bases of an elementary tensor.** A Tucker tensor `X = C ×ₖ Uₖ ≠ 0` whose core has
one entry, with unit columns `Uₖ`, has co-range bases `W` as in
`tuckerTangentProj_eq_starProjection`: the columns `W k = ⊗_{j ≠ k} Uⱼ`. -/
theorem exists_coRange_tucker_of_unique (hU : ∀ k, (U k)ᵀ * U k = 1) (hX : tucker C U ≠ 0) :
    ∃ W : ∀ k, Matrix (∀ j : {j : Fin d // j ≠ k}, ι j) (Fin 1) ℝ,
      (∀ k, actOn (· ≠ k) (W k * (W k)ᵀ) (tucker C U) = tucker C U) ∧
      ∀ k, ∃ B : Matrix _ (Fin 1) ℝ, W k = unfold (· ≠ k) (tucker C U) * B := by
  have hC : C default ≠ 0 := fun h => hX (tucker_eq_zero_of_default h U)
  have hB : ∀ k, ∃ B : Matrix (∀ j : {j : Fin d // ¬ j ≠ k}, ι j) (Fin 1) ℝ,
      coW U k = unfold (· ≠ k) (tucker C U) * B := fun k => by
    refine ⟨(coR U (C default)⁻¹ k)ᵀ, ?_⟩
    rw [unfold_tucker_of_unique, Matrix.mul_assoc, coR_mul_transpose hU, mul_inv_cancel₀ hC,
      one_smul, Matrix.mul_one]
  refine ⟨coW U, fun k => ?_, hB⟩
  refine unfold_injective (· ≠ k) ?_
  rw [unfold_actOn, unfold_tucker_of_unique, Matrix.mul_assoc,
    ← Matrix.mul_assoc (coW U k)ᵀ (coW U k) (coR U (C default) k), coW_transpose_mul_self hU,
    Matrix.one_mul]

end Elementary

/-- Non-vacuity of `norm_tuckerTangentProj_sub_le_of_unique`: two modes of dimension two,
`X = e₁ ⊗ e₁` and `Y = e₂ ⊗ e₂`. The hypotheses hold, `X ≠ Y`, and the bound follows with the
constant `√(2 (2 - 1)/2) = 1` of the manifold of matrices of fixed rank. -/
example : ∃ (U U' : ∀ _ : Fin 2, Matrix (Fin 2) (Fin 1) ℝ) (C C' : Tensor fun _ : Fin 2 => Fin 1)
    (W W' : ∀ k : Fin 2, Matrix (∀ _ : {j : Fin 2 // j ≠ k}, Fin 2) (Fin 1) ℝ),
    tucker C' U' ≠ tucker C U ∧ ∀ B : Tensor fun _ : Fin 2 => Fin 2,
      ‖tuckerTangentProj U' 1 W' B - tuckerTangentProj U 1 W B‖ ≤
        √(2 * (((2 : ℕ) : ℝ) - 1) / (2 : ℕ)) * ‖tucker C U‖⁻¹ * ‖tucker C' U' - tucker C U‖ *
          ‖B‖ := by
  obtain ⟨U, hUdef⟩ : ∃ U : ∀ _ : Fin 2, Matrix (Fin 2) (Fin 1) ℝ, ∀ k, U k = !![1; 0] :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨U', hUdef'⟩ : ∃ U' : ∀ _ : Fin 2, Matrix (Fin 2) (Fin 1) ℝ, ∀ k, U' k = !![0; 1] :=
    ⟨_, fun _ => rfl⟩
  have h1 : ∀ k, (U k)ᵀ * U k = 1 := fun k => by
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [hUdef, Matrix.mul_apply]
  have h2 : ∀ k, (U' k)ᵀ * U' k = 1 := fun k => by
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [hUdef', Matrix.mul_apply]
  obtain ⟨C, hC⟩ : ∃ C : Tensor fun _ : Fin 2 => Fin 1, C default = 1 :=
    ⟨WithLp.toLp 2 fun _ => 1, rfl⟩
  have hn1 := norm_tucker_sq_of_unique h1 C
  have hn2 := norm_tucker_sq_of_unique h2 C
  rw [hC, one_pow] at hn1 hn2
  have hX : tucker C U ≠ 0 := fun h => by
    rw [h, norm_zero] at hn1
    norm_num at hn1
  have hY : tucker C U' ≠ 0 := fun h => by
    rw [h, norm_zero] at hn2
    norm_num at hn2
  obtain ⟨W, hWX, hWB⟩ := exists_coRange_tucker_of_unique h1 hX
  obtain ⟨W', hWX', hWB'⟩ := exists_coRange_tucker_of_unique h2 hY
  refine ⟨U, U', C, C, W, W', fun h => ?_, fun B =>
    norm_tuckerTangentProj_sub_le_of_unique le_rfl h1 hWX hWB hX h2 hWX' hWB' hY B⟩
  have h0 : ⟪tucker C U', tucker C U⟫ = 0 := by
    rw [inner_tucker_tucker_of_unique]
    simp [hUdef, hUdef', Matrix.mul_apply]
  rw [h, real_inner_self_eq_norm_sq, hn1] at h0
  norm_num at h0

end Tensor

end LeanDLRA
