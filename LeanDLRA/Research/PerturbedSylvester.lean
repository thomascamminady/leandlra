import LeanDLRA.Research.SylvesterFlows

/-!
# The rank-adaptive BUG step for a Sylvester field with a Lipschitz perturbation

## Setting

`F(Y) = 𝒜 Y + Y ℬ + G(Y)` on `m × n` matrices with constant `𝒜`, `ℬ` and a `g`-Lipschitz map
`G`, one step of the rank-adaptive BUG integrator (Ceruti–Kusch–Lubich, [CerutiKuschLubich2022];
`MatrixBUG.IsRankAdaptiveStep`) from `Y₀ = U₀ S₀ V₀ᵀ`.  For `G = 0` the Galerkin space of the
step contains the exact solution (`capture_of_sylvester_of_continuousOn`).  With `a`, `b` bounds
of the Frobenius norms of `𝒜`, `ℬ`, `γ₀` a bound of `‖G(Y₀)‖`, `B` a bound of `F` along the
exact solution and along the K- and L-step solutions, and `ε₀` a bound of the normal component
of `F(Y₀)`, the capture defect of the Galerkin space is at most

    θ = 2 h ε₀ + 4 e^{3 (a + b) h} h² (g B + (a + b) γ₀).

## Main results

* `norm_sub_leftProj_le_of_perturbedSylvester`:
  `‖A(t₁) - Û Ûᵀ A(t₁)‖ ≤ h ε₀ + 2 e^{(a + 3 b) h} h² (g B + (a + b) γ₀)`.
* `norm_sub_rightProj_le_of_perturbedSylvester`: the mirror image for the row side.
* `norm_sub_galerkinProj_le_of_perturbedSylvester`: `‖A(t₁) - Û Ûᵀ A(t₁) V̂ V̂ᵀ‖ ≤ θ`.
* `error_le_of_perturbedSylvester`: `‖Y₁ - A(t₁)‖ ≤ (e^{L h} - 1) (θ + M₂ h²) + θ + ϑ`.

So the local error is `O(h ε₀ + (g B + (a + b) γ₀) h² + h³)`.  No singular value of `S₀` enters.

## Implementation notes

The proof compares `A` with the curve `W(t) = K(t) P(t) + (t - t₀) G(Y₀) (1 - V₀ V₀ᵀ)`, where
`P` is the auxiliary flow of the Sylvester case (`exists_rightFactor_of_sylvester`).  The
difference `W - A` solves the linear equation `D' = 𝒜 D + D ℬ + ψ` with a forcing `ψ` of size
`O(t - t₀)`, and `(1 - Û Ûᵀ) W(t₁) = h (1 - Û Ûᵀ) (1 - U₀ U₀ᵀ) G(Y₀) (1 - V₀ V₀ᵀ)`.  No matrix
exponential is used.  The constants are stated for Frobenius norms of `𝒜`, `ℬ`; the exponent
`3 (a + b) h` makes the bound useless for stiff coefficients.

## References

* Ceruti–Kusch–Lubich, [CerutiKuschLubich2022] (rank-adaptive BUG integrator).
* Ceruti–Einkemmer–Kusch–Lubich, [CerutiEtAl2024b] (second-order BUG integrators; experiments in
  which the rank-adaptive BUG integrator shows order one or two).
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace AugmentationRank

section PerturbedSylvester

open MatrixBUG

/-! ### Contractions -/

section Contractions

variable {i j k : Type*} [Fintype i] [Fintype j] [Fintype k]

private theorem norm_transpose_mul_le₁ [DecidableEq k] {U : Matrix i k ℝ} (hU : Uᵀ * U = 1)
    (X : Matrix i j ℝ) : ‖Uᵀ * X‖ ≤ ‖X‖ := by
  rw [← Frobenius.norm_mul_of_orthonormal hU (Uᵀ * X), ← Matrix.mul_assoc]
  have h := (isOrthProj_leftProj (n := j) hU).norm_le X
  rwa [leftProj_apply] at h

private theorem norm_mul_le₁ [DecidableEq k] {V : Matrix j k ℝ} (hV : Vᵀ * V = 1)
    (X : Matrix i j ℝ) : ‖X * V‖ ≤ ‖X‖ := by
  rw [← Frobenius.norm_transpose, Matrix.transpose_mul, ← Frobenius.norm_transpose X]
  exact norm_transpose_mul_le₁ hV Xᵀ

private theorem norm_one_sub_mul_le₁ [DecidableEq i] [DecidableEq k] {U : Matrix i k ℝ}
    (hU : Uᵀ * U = 1) (X : Matrix i j ℝ) : ‖(1 - U * Uᵀ) * X‖ ≤ ‖X‖ := by
  have h := (isOrthProj_leftProj (n := j) hU).compl.norm_le X
  have e : (1 - leftProj (n := j) U) X = (1 - U * Uᵀ) * X := by
    rw [Matrix.sub_mul, Matrix.one_mul]
    rfl
  rwa [e] at h

private theorem norm_mul_one_sub_le₁ [DecidableEq j] [DecidableEq k] {V : Matrix j k ℝ}
    (hV : Vᵀ * V = 1) (X : Matrix i j ℝ) : ‖X * (1 - V * Vᵀ)‖ ≤ ‖X‖ := by
  have h : (X * (1 - V * Vᵀ))ᵀ = (1 - V * Vᵀ) * Xᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
      Matrix.transpose_transpose]
  rw [← Frobenius.norm_transpose, h, ← Frobenius.norm_transpose X]
  exact norm_one_sub_mul_le₁ hV Xᵀ

private theorem norm_mul_mul_le₁ (X : Matrix i j ℝ) (Y : Matrix j k ℝ) {x y : ℝ}
    (hx : ‖X‖ ≤ x) (hy : ‖Y‖ ≤ y) : ‖X * Y‖ ≤ x * y :=
  (Frobenius.norm_mul_le X Y).trans
    (mul_le_mul hx hy (norm_nonneg _) ((norm_nonneg _).trans hx))

end Contractions

/-! ### Scalar inequalities -/

/-- The Grönwall bound with rate `2 b` and source `b`, in closed form. -/
private theorem gronwallBound_two_mul_le {b : ℝ} (hb : 0 ≤ b) (x : ℝ) :
    gronwallBound 0 (2 * b) b x ≤ (Real.exp (2 * b * x) - 1) / 2 := by
  rcases hb.eq_or_lt with rfl | hb'
  · simp [gronwallBound_K0]
  · rw [gronwallBound_of_K_ne_0 (by positivity : 2 * b ≠ 0)]
    have hq : b / (2 * b) = 1 / 2 := by field_simp
    simp only [zero_mul, zero_add]
    rw [hq]
    linarith

/-- `e^x - 1 ≤ x e^x`. -/
private theorem exp_sub_one_le_mul_exp (x : ℝ) : Real.exp x - 1 ≤ x * Real.exp x := by
  have h1 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  have h2 := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
  linarith

/-- The forcing of the comparison equation against `2 h e^{2 b h} (g B + (a + b) γ₀)`. -/
private theorem forcing_scalar_le {a b g B γ₀ τ h e E : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hg : 0 ≤ g) (hB : 0 ≤ B) (hγ : 0 ≤ γ₀) (hτ : 0 ≤ τ) (hτh : τ ≤ h) (hE1 : 1 ≤ E)
    (he1 : e ≤ (E - 1) / 2) (he2 : e ≤ b * h * E) :
    g * (B * τ) * (1 + e) + γ₀ * e + g * (B * τ) + τ * ((a + b) * γ₀)
      ≤ 2 * h * E * (g * B + (a + b) * γ₀) := by
  have hh : 0 ≤ h := hτ.trans hτh
  have hgB : 0 ≤ g * B := mul_nonneg hg hB
  have hE0 : 0 ≤ E := zero_le_one.trans hE1
  have s0 : 0 ≤ g * (B * τ) := mul_nonneg hg (mul_nonneg hB hτ)
  have s1 : g * (B * τ) ≤ g * B * h := by
    have := mul_le_mul_of_nonneg_left hτh hgB
    linarith
  have s2 : 1 + e ≤ E := by linarith
  have t1 : g * (B * τ) * (1 + e) ≤ g * B * h * E := by
    rcases le_total 0 (1 + e) with h0 | h0
    · exact mul_le_mul s1 s2 h0 (mul_nonneg hgB hh)
    · exact (mul_nonpos_of_nonneg_of_nonpos s0 h0).trans
        (mul_nonneg (mul_nonneg hgB hh) hE0)
  have t2 : γ₀ * e ≤ γ₀ * (b * h * E) := mul_le_mul_of_nonneg_left he2 hγ
  have t3 : g * B * h ≤ g * B * h * E := le_mul_of_one_le_right (mul_nonneg hgB hh) hE1
  have hc : 0 ≤ (a + b) * γ₀ := mul_nonneg (add_nonneg ha hb) hγ
  have t4 : τ * ((a + b) * γ₀) ≤ h * ((a + b) * γ₀) := mul_le_mul_of_nonneg_right hτh hc
  have t5 : h * ((a + b) * γ₀) ≤ h * ((a + b) * γ₀) * E :=
    le_mul_of_one_le_right (mul_nonneg hh hc) hE1
  have t6 : 0 ≤ h * E * γ₀ * a := mul_nonneg (mul_nonneg (mul_nonneg hh hE0) hγ) ha
  linarith

/-! ### Matrix identities -/

section Identities

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq n]
  {r : ℕ} {U₀ : Matrix m (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}

omit [DecidableEq m] in
/-- The derivative of `W - A`, `W = K P + τ G₀ (1 - V₀ V₀ᵀ)`, as a linear part and a forcing. -/
private theorem defect_identity (hV₀ : V₀ᵀ * V₀ = 1) (𝒜 : Matrix m m ℝ) (ℬ : Matrix n n ℝ)
    (Kt : Matrix m (Fin r) ℝ) (Pt : Matrix (Fin r) n ℝ) (At GK GA G₀ : Matrix m n ℝ) (τ : ℝ) :
    ((𝒜 * (Kt * V₀ᵀ) + Kt * V₀ᵀ * ℬ + GK) * V₀ * Pt + Kt * (Pt * ℬ - V₀ᵀ * ℬ * V₀ * Pt)
        + G₀ * (1 - V₀ * V₀ᵀ)) - (𝒜 * At + At * ℬ + GA)
      = 𝒜 * (Kt * Pt + τ • (G₀ * (1 - V₀ * V₀ᵀ)) - At)
        + (Kt * Pt + τ • (G₀ * (1 - V₀ * V₀ᵀ)) - At) * ℬ
        + ((GK - G₀) * V₀ * Pt + G₀ * V₀ * (Pt - V₀ᵀ) + (G₀ - GA)
          - τ • (𝒜 * (G₀ * (1 - V₀ * V₀ᵀ)) + G₀ * (1 - V₀ * V₀ᵀ) * ℬ)) := by
  have hVX : ∀ X : Matrix (Fin r) n ℝ, V₀ᵀ * (V₀ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hV₀, Matrix.one_mul]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one,
    Matrix.mul_assoc, hVX, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_sub]
  abel

/-- The normal component of `𝒜 Y₀ + Y₀ ℬ + G₀` at `Y₀ = U₀ S₀ V₀ᵀ` is that of `G₀`. -/
private theorem normal_part_eq (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (𝒜 : Matrix m m ℝ)
    (ℬ : Matrix n n ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ) (G₀ : Matrix m n ℝ) :
    (1 - U₀ * U₀ᵀ) * (𝒜 * (U₀ * S₀ * V₀ᵀ) + U₀ * S₀ * V₀ᵀ * ℬ + G₀) * (1 - V₀ * V₀ᵀ)
      = (1 - U₀ * U₀ᵀ) * (G₀ * (1 - V₀ * V₀ᵀ)) := by
  have hU0 : ∀ X : Matrix (Fin r) n ℝ, (1 - U₀ * U₀ᵀ) * (U₀ * X) = 0 := fun X => by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U₀ᵀ, hU₀,
      Matrix.one_mul, sub_self]
  have hV0 : V₀ᵀ * (1 - V₀ * V₀ᵀ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hV₀, Matrix.one_mul, sub_self]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hU0, hV0, Matrix.mul_zero,
    Matrix.zero_mul, zero_add]

omit [Fintype n] [DecidableEq n] in
/-- Splitting of the left capture defect: the part of `W(t₁)` outside the range of `Û` and the
difference `W(t₁) - A(t₁)`. -/
private theorem capture_split {Ua : Matrix m k ℝ} {K₁ : Matrix m (Fin r) ℝ}
    (hcapK : Ua * Uaᵀ * K₁ = K₁) (hcapU : Ua * Uaᵀ * U₀ = U₀) (P₁ : Matrix (Fin r) n ℝ)
    (N A₁ : Matrix m n ℝ) (h : ℝ) :
    A₁ - Ua * Uaᵀ * A₁ = h • ((1 - Ua * Uaᵀ) * ((1 - U₀ * U₀ᵀ) * N))
      - (1 - Ua * Uaᵀ) * (K₁ * P₁ + h • N - A₁) := by
  have h1 : Ua * (Uaᵀ * (K₁ * P₁)) = K₁ * P₁ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hcapK]
  have h2 : Ua * (Uaᵀ * (U₀ * (U₀ᵀ * N))) = U₀ * (U₀ᵀ * N) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hcapU]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_add, Matrix.mul_smul,
    Matrix.mul_assoc, smul_sub, h1, h2]
  abel

omit [DecidableEq m] in
/-- The forcing of the comparison equation, piece by piece. -/
private theorem norm_forcing_le (hV₀ : V₀ᵀ * V₀ = 1) {𝒜 : Matrix m m ℝ} {ℬ : Matrix n n ℝ}
    {Pt : Matrix (Fin r) n ℝ} {GK GA G₀ : Matrix m n ℝ} {a b x γ₀ τ e : ℝ} (h𝒜 : ‖𝒜‖ ≤ a)
    (hℬ : ‖ℬ‖ ≤ b) (hτ : 0 ≤ τ) (hGK : ‖GK - G₀‖ ≤ x) (hGA : ‖G₀ - GA‖ ≤ x)
    (hG₀ : ‖G₀‖ ≤ γ₀) (hE : ‖Pt - V₀ᵀ‖ ≤ e) :
    ‖(GK - G₀) * V₀ * Pt + G₀ * V₀ * (Pt - V₀ᵀ) + (G₀ - GA)
        - τ • (𝒜 * (G₀ * (1 - V₀ * V₀ᵀ)) + G₀ * (1 - V₀ * V₀ᵀ) * ℬ)‖
      ≤ x * (1 + e) + γ₀ * e + x + τ * ((a + b) * γ₀) := by
  have hN : ‖G₀ * (1 - V₀ * V₀ᵀ)‖ ≤ γ₀ := (norm_mul_one_sub_le₁ hV₀ G₀).trans hG₀
  have e1 : (GK - G₀) * V₀ * Pt = (GK - G₀) * V₀ * V₀ᵀ + (GK - G₀) * V₀ * (Pt - V₀ᵀ) := by
    rw [Matrix.mul_sub]
    abel
  have p1 : ‖(GK - G₀) * V₀ * V₀ᵀ‖ ≤ x := by
    rw [Frobenius.norm_mul_transpose_of_orthonormal hV₀]
    exact (norm_mul_le₁ hV₀ _).trans hGK
  have p2 : ‖(GK - G₀) * V₀ * (Pt - V₀ᵀ)‖ ≤ x * e :=
    norm_mul_mul_le₁ _ _ ((norm_mul_le₁ hV₀ _).trans hGK) hE
  have p3 : ‖G₀ * V₀ * (Pt - V₀ᵀ)‖ ≤ γ₀ * e :=
    norm_mul_mul_le₁ _ _ ((norm_mul_le₁ hV₀ _).trans hG₀) hE
  have p4 : ‖τ • (𝒜 * (G₀ * (1 - V₀ * V₀ᵀ)) + G₀ * (1 - V₀ * V₀ᵀ) * ℬ)‖
      ≤ τ * ((a + b) * γ₀) := by
    rw [norm_smul, Real.norm_of_nonneg hτ]
    refine mul_le_mul_of_nonneg_left ?_ hτ
    have q1 := norm_mul_mul_le₁ _ _ h𝒜 hN
    have q2 := norm_mul_mul_le₁ _ _ hN hℬ
    have := norm_add_le_of_le q1 q2
    linarith
  rw [e1]
  have := norm_sub_le_of_le (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le p1 p2) p3)
    hGA) p4
  linarith

end Identities

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {𝒜 : Matrix m m ℝ} {ℬ : Matrix n n ℝ}
  {G : Matrix m n ℝ → Matrix m n ℝ} {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ}
  {V₀ : Matrix n (Fin r) ℝ} {t₀ t₁ : ℝ}

/-! ### The auxiliary flow stays near its starting value -/

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- The auxiliary flow `P' = P ℬ - (V₀ᵀ ℬ V₀) P`, `P(t₀) = V₀ᵀ` of the Sylvester case satisfies
`‖P(t) - V₀ᵀ‖ ≤ (e^{2 b (t - t₀)} - 1) / 2` when `‖ℬ‖ ≤ b`. -/
private theorem norm_rightFactor_sub_le (hV₀ : V₀ᵀ * V₀ = 1) {b : ℝ} (hℬ : ‖ℬ‖ ≤ b)
    {P : ℝ → Matrix (Fin r) n ℝ}
    (hP : ODESolution (fun _ X => X * ℬ - V₀ᵀ * ℬ * V₀ * X) P t₀ t₁) (hP₀ : P t₀ = V₀ᵀ) :
    ∀ t ∈ Icc t₀ t₁, ‖P t - V₀ᵀ‖ ≤ (Real.exp (2 * b * (t - t₀)) - 1) / 2 := by
  classical
  have hb : 0 ≤ b := (norm_nonneg _).trans hℬ
  have hM : ‖V₀ᵀ * ℬ * V₀‖ ≤ b :=
    (norm_mul_le₁ hV₀ _).trans ((norm_transpose_mul_le₁ hV₀ ℬ).trans hℬ)
  have hsrc : ‖V₀ᵀ * ℬ * (1 - V₀ * V₀ᵀ)‖ ≤ b := by
    rw [Matrix.mul_assoc]
    exact (norm_transpose_mul_le₁ hV₀ _).trans ((norm_mul_one_sub_le₁ hV₀ ℬ).trans hℬ)
  have hbound : ∀ t ∈ Ico t₀ t₁,
      ‖P t * ℬ - V₀ᵀ * ℬ * V₀ * P t‖ ≤ 2 * b * ‖P t - V₀ᵀ‖ + b := fun t _ => by
    have e : P t * ℬ - V₀ᵀ * ℬ * V₀ * P t = (P t - V₀ᵀ) * ℬ - V₀ᵀ * ℬ * V₀ * (P t - V₀ᵀ)
        + V₀ᵀ * ℬ * (1 - V₀ * V₀ᵀ) := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
      abel
    rw [e]
    have h1 := norm_mul_mul_le₁ (P t - V₀ᵀ) ℬ le_rfl hℬ
    have h2 := norm_mul_mul_le₁ (V₀ᵀ * ℬ * V₀) (P t - V₀ᵀ) hM le_rfl
    have := norm_add_le_of_le (norm_sub_le_of_le h1 h2) hsrc
    linarith
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun t => P t - V₀ᵀ)
    (f' := fun t => P t * ℬ - V₀ᵀ * ℬ * V₀ * P t) (δ := 0) (K := 2 * b) (ε := b)
    (hP.cont.sub continuousOn_const) (fun t ht => (hP.deriv t ht).sub_const V₀ᵀ)
    (by simp [hP₀]) hbound
  exact fun t ht => (hg t ht).trans (gronwallBound_two_mul_le hb _)

/-! ### The left capture defect -/

/-- **Left capture defect of the rank-adaptive BUG step for a perturbed Sylvester field.**  Let
`F(Y) = 𝒜 Y + Y ℬ + G(Y)` with `‖𝒜‖ ≤ a`, `‖ℬ‖ ≤ b` and `G` Lipschitz with constant `g`, let `A`
be the exact solution from `Y₀ = U₀ S₀ V₀ᵀ`, `K` the K-step solution, and let `Û` (`Ua`) have
orthonormal columns whose range contains those of `U₀` and `K(t₁)`.  Then

    ‖A(t₁) - Û Ûᵀ A(t₁)‖ ≤ h ε₀ + 2 e^{(a + 3 b) h} h² (g B + (a + b) γ₀),

where `ε₀` bounds the normal component `(1 - U₀ U₀ᵀ) F(Y₀) (1 - V₀ V₀ᵀ)`, `γ₀` bounds `‖G(Y₀)‖`
and `B` bounds `F` along `A` and along `K V₀ᵀ`.  No singular value of `S₀` enters, and `F`
need not be Lipschitz as a whole: only the Lipschitz constant of `G` is used. -/
theorem norm_sub_leftProj_le_of_perturbedSylvester {k : Type*} [Fintype k] [DecidableEq k]
    {g h : ℝ} (hFS : ∀ t Y, F t Y = 𝒜 * Y + Y * ℬ + G Y)
    (hG : ∀ X Y, ‖G X - G Y‖ ≤ g * ‖X - Y‖) (hg : 0 ≤ g) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) {K : ℝ → Matrix m (Fin r) ℝ}
    (hK : ODESolution (kField V₀ F) K t₀ t₁) (hK₀ : K t₀ = U₀ * S₀) {Ua : Matrix m k ℝ}
    (hUa : Uaᵀ * Ua = 1) (hcapK : Ua * Uaᵀ * K t₁ = K t₁) (hcapU : Ua * Uaᵀ * U₀ = U₀)
    {A : ℝ → Matrix m n ℝ} (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ)
    {a b B γ₀ ε₀ : ℝ} (h𝒜 : ‖𝒜‖ ≤ a) (hℬ : ‖ℬ‖ ≤ b)
    (hBA : ∀ t ∈ Ico t₀ t₁, ‖F t (A t)‖ ≤ B)
    (hBK : ∀ t ∈ Ico t₀ t₁, ‖F t (K t * V₀ᵀ)‖ ≤ B) (hγ₀ : ‖G (U₀ * S₀ * V₀ᵀ)‖ ≤ γ₀)
    (hε₀ : ‖(1 - U₀ * U₀ᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε₀) :
    ‖A t₁ - Ua * Uaᵀ * A t₁‖
      ≤ h * ε₀ + 2 * Real.exp ((a + 3 * b) * h) * h ^ 2 * (g * B + (a + b) * γ₀) := by
  rcases hh.eq_or_lt with rfl | hpos
  · have e : Ua * Uaᵀ * (U₀ * S₀ * V₀ᵀ) = U₀ * S₀ * V₀ᵀ := by
      simp only [← Matrix.mul_assoc]
      rw [hcapU]
    rw [ht₁, add_zero, hA₀, e, sub_self, norm_zero]
    simp
  have hle : t₀ ≤ t₁ := by linarith
  have hlt : t₀ < t₁ := by linarith
  have ha : 0 ≤ a := (norm_nonneg _).trans h𝒜
  have hb : 0 ≤ b := (norm_nonneg _).trans hℬ
  have hγ : 0 ≤ γ₀ := (norm_nonneg _).trans hγ₀
  have hB : 0 ≤ B := (norm_nonneg _).trans (hBA t₀ ⟨le_rfl, hlt⟩)
  -- the starting value of the perturbation, as a variable
  obtain ⟨G₀, hG₀⟩ : ∃ G₀ : Matrix m n ℝ, G₀ = G (U₀ * S₀ * V₀ᵀ) := ⟨_, rfl⟩
  rw [← hG₀] at hγ₀
  rw [hFS, ← hG₀, normal_part_eq hU₀ hV₀] at hε₀
  obtain ⟨P, hP, hP₀⟩ := exists_rightFactor_of_sylvester (ℬ := fun _ => ℬ)
    (continuousOn_const (s := Icc t₀ t₁)) hle V₀
  have hPinc := norm_rightFactor_sub_le hV₀ hℬ hP hP₀
  -- increments of the K-step solution and of the exact solution
  have hKinc : ∀ t ∈ Icc t₀ t₁, ‖K t - U₀ * S₀‖ ≤ B * (t - t₀) := by
    have := hK.norm_sub_le (B := B) fun t ht => (norm_mul_le₁ hV₀ _).trans (hBK t ht)
    rwa [hK₀] at this
  have hAinc : ∀ t ∈ Icc t₀ t₁, ‖A t - U₀ * S₀ * V₀ᵀ‖ ≤ B * (t - t₀) := by
    have := hA.norm_sub_le hBA
    rwa [hA₀] at this
  -- the difference `D = W - A` of the comparison curve and the exact solution
  set E := Real.exp (2 * b * h) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  have hDc : ContinuousOn (fun s => K s * P s + (s - t₀) • (G₀ * (1 - V₀ * V₀ᵀ)) - A s)
      (Icc t₀ t₁) :=
    ((((Frobenius.mulCLM (m := m) (l := Fin r) (n := n)).continuous.comp_continuousOn
      hK.cont).clm_apply hP.cont).add
      ((continuous_id.sub continuous_const).smul continuous_const).continuousOn).sub hA.cont
  have hDd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt
      (fun s => K s * P s + (s - t₀) • (G₀ * (1 - V₀ * V₀ᵀ)) - A s)
      (𝒜 * (K t * P t + (t - t₀) • (G₀ * (1 - V₀ * V₀ᵀ)) - A t)
        + (K t * P t + (t - t₀) • (G₀ * (1 - V₀ * V₀ᵀ)) - A t) * ℬ
        + ((G (K t * V₀ᵀ) - G₀) * V₀ * P t + G₀ * V₀ * (P t - V₀ᵀ) + (G₀ - G (A t))
          - (t - t₀) • (𝒜 * (G₀ * (1 - V₀ * V₀ᵀ)) + G₀ * (1 - V₀ * V₀ᵀ) * ℬ))) (Ici t) t := by
    intro t ht
    have hKd : HasDerivWithinAt K
        ((𝒜 * (K t * V₀ᵀ) + K t * V₀ᵀ * ℬ + G (K t * V₀ᵀ)) * V₀) (Ici t) t := by
      have := hK.deriv t ht
      rwa [kField, hFS] at this
    have hPd : HasDerivWithinAt P (P t * ℬ - V₀ᵀ * ℬ * V₀ * P t) (Ici t) t := hP.deriv t ht
    have hAd : HasDerivWithinAt A (𝒜 * A t + A t * ℬ + G (A t)) (Ici t) t := by
      have := hA.deriv t ht
      rwa [hFS] at this
    have hNd : HasDerivWithinAt (fun s : ℝ => (s - t₀) • (G₀ * (1 - V₀ * V₀ᵀ)))
        (G₀ * (1 - V₀ * V₀ᵀ)) (Ici t) t := by
      simpa using
        (((hasDerivAt_id t).sub_const t₀).smul_const (G₀ * (1 - V₀ * V₀ᵀ))).hasDerivWithinAt
    refine (((Frobenius.hasDerivWithinAt_mul hKd hPd).add hNd).sub hAd).congr_deriv ?_
    exact defect_identity hV₀ 𝒜 ℬ (K t) (P t) (A t) _ _ G₀ (t - t₀)
  have hD₀ : ‖K t₀ * P t₀ + (t₀ - t₀) • (G₀ * (1 - V₀ * V₀ᵀ)) - A t₀‖ ≤ 0 := by
    rw [hK₀, hP₀, hA₀, sub_self, zero_smul, add_zero, sub_self, norm_zero]
  have hbound : ∀ t ∈ Ico t₀ t₁,
      ‖𝒜 * (K t * P t + (t - t₀) • (G₀ * (1 - V₀ * V₀ᵀ)) - A t)
        + (K t * P t + (t - t₀) • (G₀ * (1 - V₀ * V₀ᵀ)) - A t) * ℬ
        + ((G (K t * V₀ᵀ) - G₀) * V₀ * P t + G₀ * V₀ * (P t - V₀ᵀ) + (G₀ - G (A t))
          - (t - t₀) • (𝒜 * (G₀ * (1 - V₀ * V₀ᵀ)) + G₀ * (1 - V₀ * V₀ᵀ) * ℬ))‖
      ≤ (a + b) * ‖K t * P t + (t - t₀) • (G₀ * (1 - V₀ * V₀ᵀ)) - A t‖
        + 2 * h * E * (g * B + (a + b) * γ₀) := by
    intro t ht
    have ht' : t ∈ Icc t₀ t₁ := Ico_subset_Icc_self ht
    have hτ : 0 ≤ t - t₀ := by linarith [ht.1]
    have hτh : t - t₀ ≤ h := by linarith [ht.2]
    have hGK : ‖G (K t * V₀ᵀ) - G₀‖ ≤ g * (B * (t - t₀)) := by
      rw [hG₀]
      refine (hG _ _).trans (mul_le_mul_of_nonneg_left ?_ hg)
      rw [← Matrix.sub_mul, Frobenius.norm_mul_transpose_of_orthonormal hV₀]
      exact hKinc t ht'
    have hGA : ‖G₀ - G (A t)‖ ≤ g * (B * (t - t₀)) := by
      rw [hG₀, norm_sub_rev]
      exact (hG _ _).trans (mul_le_mul_of_nonneg_left (hAinc t ht') hg)
    have hEt := hPinc t ht'
    have hmono : Real.exp (2 * b * (t - t₀)) ≤ E :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hτh (by positivity))
    have he1 : (Real.exp (2 * b * (t - t₀)) - 1) / 2 ≤ (E - 1) / 2 := by linarith
    have he2 : (Real.exp (2 * b * (t - t₀)) - 1) / 2 ≤ b * h * E := by
      have h1 := exp_sub_one_le_mul_exp (2 * b * (t - t₀))
      have h2 : 2 * b * (t - t₀) * Real.exp (2 * b * (t - t₀)) ≤ 2 * b * h * E :=
        mul_le_mul (mul_le_mul_of_nonneg_left hτh (by positivity)) hmono
          (Real.exp_pos _).le (by positivity)
      linarith
    have hψ := norm_forcing_le hV₀ h𝒜 hℬ hτ hGK hGA hγ₀ hEt
    have hsc := forcing_scalar_le ha hb hg hB hγ hτ hτh hE1 he1 he2
    have q1 := norm_mul_mul_le₁ 𝒜
      (K t * P t + (t - t₀) • (G₀ * (1 - V₀ * V₀ᵀ)) - A t) h𝒜 le_rfl
    have q2 := norm_mul_mul_le₁
      (K t * P t + (t - t₀) • (G₀ * (1 - V₀ * V₀ᵀ)) - A t) ℬ le_rfl hℬ
    have := norm_add_le_of_le (norm_add_le_of_le q1 q2) hψ
    linarith
  have hΓ : 0 ≤ 2 * h * E * (g * B + (a + b) * γ₀) := by positivity
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le hDc hDd hD₀ hbound t₁
    (right_mem_Icc.2 hle)
  have hth : t₁ - t₀ = h := by rw [ht₁]; ring
  rw [hth] at hgr
  have hgr' := hgr.trans (gronwallBound_le_exp_mul (add_nonneg ha hb) hΓ)
  -- the part of the comparison curve outside the range of `Û`
  have hout : ‖(1 - Ua * Uaᵀ) * ((1 - U₀ * U₀ᵀ) * (G₀ * (1 - V₀ * V₀ᵀ)))‖ ≤ ε₀ :=
    (norm_one_sub_mul_le₁ hUa _).trans hε₀
  have hin := norm_one_sub_mul_le₁ hUa
    (K t₁ * P t₁ + (t₁ - t₀) • (G₀ * (1 - V₀ * V₀ᵀ)) - A t₁)
  rw [hth] at hin
  rw [capture_split hcapK hcapU (P t₁) (G₀ * (1 - V₀ * V₀ᵀ)) (A t₁) h]
  have hsm : ‖h • ((1 - Ua * Uaᵀ) * ((1 - U₀ * U₀ᵀ) * (G₀ * (1 - V₀ * V₀ᵀ))))‖ ≤ h * ε₀ := by
    rw [norm_smul, Real.norm_of_nonneg hh]
    exact mul_le_mul_of_nonneg_left hout hh
  have hexp : Real.exp ((a + 3 * b) * h) = Real.exp ((a + b) * h) * E := by
    rw [hE, ← Real.exp_add]
    ring_nf
  have := norm_sub_le_of_le hsm (hin.trans hgr')
  rw [hexp]
  linarith

/-! ### The row side, by transposition -/

omit [DecidableEq m] [DecidableEq n] in
/-- Transposition maps solutions of `X' = H(t, X)` to solutions of `Xᵀ' = H'(t, Xᵀ)` when
`H'(t, Y(t)ᵀ) = H(t, Y(t))ᵀ` along the solution. -/
private theorem odeSolution_transpose₁ {H : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {H' : ℝ → Matrix n m ℝ → Matrix n m ℝ} {Y : ℝ → Matrix m n ℝ}
    (hY : ODESolution H Y t₀ t₁) (hH : ∀ t ∈ Ico t₀ t₁, H' t (Y t)ᵀ = (H t (Y t))ᵀ) :
    ODESolution H' (fun t => (Y t)ᵀ) t₀ t₁ where
  cont := (Frobenius.transposeCLM (m := m) (n := n)).continuous.comp_continuousOn hY.cont
  deriv t ht := by
    rw [hH t ht]
    exact Frobenius.hasDerivWithinAt_transpose (hY.deriv t ht)

/-- **Row capture defect of the rank-adaptive BUG step for a perturbed Sylvester field**: the
mirror image of `norm_sub_leftProj_le_of_perturbedSylvester`, obtained by transposition.  `Lf` is
the L-step solution, and `B` bounds `F` along `A` and along `U₀ Lᵀ`. -/
theorem norm_sub_rightProj_le_of_perturbedSylvester {k' : Type*} [Fintype k'] [DecidableEq k']
    {g h : ℝ} (hFS : ∀ t Y, F t Y = 𝒜 * Y + Y * ℬ + G Y)
    (hG : ∀ X Y, ‖G X - G Y‖ ≤ g * ‖X - Y‖) (hg : 0 ≤ g) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) {Lf : ℝ → Matrix n (Fin r) ℝ}
    (hLf : ODESolution (lField U₀ F) Lf t₀ t₁) (hLf₀ : Lf t₀ = V₀ * S₀ᵀ) {Va : Matrix n k' ℝ}
    (hVa : Vaᵀ * Va = 1) (hcapL : Va * Vaᵀ * Lf t₁ = Lf t₁) (hcapV : Va * Vaᵀ * V₀ = V₀)
    {A : ℝ → Matrix m n ℝ} (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ)
    {a b B γ₀ ε₀ : ℝ} (h𝒜 : ‖𝒜‖ ≤ a) (hℬ : ‖ℬ‖ ≤ b)
    (hBA : ∀ t ∈ Ico t₀ t₁, ‖F t (A t)‖ ≤ B)
    (hBL : ∀ t ∈ Ico t₀ t₁, ‖F t (U₀ * (Lf t)ᵀ)‖ ≤ B) (hγ₀ : ‖G (U₀ * S₀ * V₀ᵀ)‖ ≤ γ₀)
    (hε₀ : ‖(1 - U₀ * U₀ᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε₀) :
    ‖A t₁ - A t₁ * Va * Vaᵀ‖
      ≤ h * ε₀ + 2 * Real.exp ((b + 3 * a) * h) * h ^ 2 * (g * B + (b + a) * γ₀) := by
  have hkl : kField U₀ (fun t (X : Matrix n m ℝ) => (F t Xᵀ)ᵀ) = lField U₀ F := by
    funext t Lm
    simp only [kField, lField, Matrix.transpose_mul, Matrix.transpose_transpose]
  have e0 : (V₀ * S₀ᵀ * U₀ᵀ)ᵀ = U₀ * S₀ * V₀ᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hb := norm_sub_leftProj_le_of_perturbedSylvester
    (F := fun t (X : Matrix n m ℝ) => (F t Xᵀ)ᵀ) (𝒜 := ℬᵀ) (ℬ := 𝒜ᵀ)
    (G := fun X : Matrix n m ℝ => (G Xᵀ)ᵀ) (U₀ := V₀) (S₀ := S₀ᵀ) (V₀ := U₀) (K := Lf)
    (Ua := Va) (A := fun t => (A t)ᵀ) (a := b) (b := a) (B := B) (γ₀ := γ₀) (ε₀ := ε₀)
    (g := g) (h := h)
    (fun t X => by
      change (F t Xᵀ)ᵀ = ℬᵀ * X + X * 𝒜ᵀ + (G Xᵀ)ᵀ
      rw [hFS]
      simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose]
      abel)
    (fun X Y => by
      change ‖(G Xᵀ)ᵀ - (G Yᵀ)ᵀ‖ ≤ g * ‖X - Y‖
      rw [← Matrix.transpose_sub, Frobenius.norm_transpose]
      refine (hG _ _).trans_eq ?_
      rw [← Matrix.transpose_sub, Frobenius.norm_transpose])
    hg ht₁ hh hV₀ hU₀ (by rwa [hkl]) hLf₀ hVa hcapL hcapV
    (odeSolution_transpose₁ hA fun t _ => by simp only [Matrix.transpose_transpose])
    (by rw [hA₀]; simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc])
    (by rwa [Frobenius.norm_transpose]) (by rwa [Frobenius.norm_transpose])
    (fun t ht => by
      change ‖(F t (A t)ᵀᵀ)ᵀ‖ ≤ B
      rw [Frobenius.norm_transpose, Matrix.transpose_transpose]
      exact hBA t ht)
    (fun t ht => by
      change ‖(F t (Lf t * U₀ᵀ)ᵀ)ᵀ‖ ≤ B
      rw [Frobenius.norm_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]
      exact hBL t ht)
    (by
      change ‖(G (V₀ * S₀ᵀ * U₀ᵀ)ᵀ)ᵀ‖ ≤ γ₀
      rw [Frobenius.norm_transpose, e0]
      exact hγ₀)
    (by
      change ‖(1 - V₀ * V₀ᵀ) * (F t₀ (V₀ * S₀ᵀ * U₀ᵀ)ᵀ)ᵀ * (1 - U₀ * U₀ᵀ)‖ ≤ ε₀
      rw [e0, ← Frobenius.norm_transpose]
      convert hε₀ using 2
      simp only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.transpose_transpose, Matrix.mul_assoc])
  have e : A t₁ - A t₁ * Va * Vaᵀ = ((A t₁)ᵀ - Va * Vaᵀ * (A t₁)ᵀ)ᵀ := by
    simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc]
  rw [e, Frobenius.norm_transpose]
  exact hb

/-! ### The capture defect and the local error of the step -/

variable {k k' : Type*} [Fintype k] [Fintype k'] [DecidableEq k] [DecidableEq k']
  {Ua : Matrix m k ℝ} {Va : Matrix n k' ℝ} {K : ℝ → Matrix m (Fin r) ℝ}
  {Lf : ℝ → Matrix n (Fin r) ℝ} {Sa : ℝ → Matrix k k' ℝ} {Y₁ : Matrix m n ℝ}
  {A : ℝ → Matrix m n ℝ}

/-- **Capture defect of the rank-adaptive BUG step for a perturbed Sylvester field.**  Let
`F(Y) = 𝒜 Y + Y ℬ + G(Y)` with `‖𝒜‖ ≤ a`, `‖ℬ‖ ≤ b` (Frobenius norms) and `G` Lipschitz with
constant `g`.  For every step of the rank-adaptive BUG integrator (Ceruti–Kusch–Lubich,
[CerutiKuschLubich2022]; `MatrixBUG.IsRankAdaptiveStep`) from `Y₀ = U₀ S₀ V₀ᵀ` the exact solution
`A` satisfies

    ‖A(t₁) - Û Ûᵀ A(t₁) V̂ V̂ᵀ‖ ≤ 2 h ε₀ + 4 e^{3 (a + b) h} h² (g B + (a + b) γ₀),

where `ε₀` bounds the normal component of `F(Y₀)`, `γ₀` bounds `‖G(Y₀)‖`, and `B` bounds `F`
along the exact solution and along the K- and L-step solutions.  For `G = 0` the right-hand side
vanishes (`capture_of_sylvester_of_continuousOn`).  No singular value of `S₀` enters. -/
theorem norm_sub_galerkinProj_le_of_perturbedSylvester {ϑ g h : ℝ}
    (hFS : ∀ t Y, F t Y = 𝒜 * Y + Y * ℬ + G Y) (hG : ∀ X Y, ‖G X - G Y‖ ≤ g * ‖X - Y‖)
    (hg : 0 ≤ g) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) {a b B γ₀ ε₀ : ℝ}
    (h𝒜 : ‖𝒜‖ ≤ a) (hℬ : ‖ℬ‖ ≤ b) (hBA : ∀ t ∈ Ico t₀ t₁, ‖F t (A t)‖ ≤ B)
    (hBK : ∀ t ∈ Ico t₀ t₁, ‖F t (K t * V₀ᵀ)‖ ≤ B)
    (hBL : ∀ t ∈ Ico t₀ t₁, ‖F t (U₀ * (Lf t)ᵀ)‖ ≤ B) (hγ₀ : ‖G (U₀ * S₀ * V₀ᵀ)‖ ≤ γ₀)
    (hε₀ : ‖(1 - U₀ * U₀ᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε₀) :
    ‖A t₁ - galerkinProj Ua Va (A t₁)‖
      ≤ 2 * h * ε₀ + 4 * Real.exp (3 * (a + b) * h) * h ^ 2 * (g * B + (a + b) * γ₀) := by
  have ha : 0 ≤ a := (norm_nonneg _).trans h𝒜
  have hb : 0 ≤ b := (norm_nonneg _).trans hℬ
  have hγ : 0 ≤ γ₀ := (norm_nonneg _).trans hγ₀
  have hθL := norm_sub_leftProj_le_of_perturbedSylvester hFS hG hg ht₁ hh hs.orthU₀ hs.orthV₀
    hs.kSol hs.kStart hs.orthUa hs.kCap hs.augU hA hA₀ h𝒜 hℬ hBA hBK hγ₀ hε₀
  have hθR := norm_sub_rightProj_le_of_perturbedSylvester hFS hG hg ht₁ hh hs.orthU₀ hs.orthV₀
    hs.lSol hs.lStart hs.orthVa hs.lCap hs.augV hA hA₀ h𝒜 hℬ hBA hBL hγ₀ hε₀
  have hΓ : 0 ≤ h ^ 2 * (g * B + (a + b) * γ₀) := by
    rcases hh.eq_or_lt with rfl | hpos
    · simp
    · have hB : 0 ≤ B := (norm_nonneg _).trans (hBA t₀ ⟨le_rfl, by linarith⟩)
      positivity
  have e1 : Real.exp ((a + 3 * b) * h) ≤ Real.exp (3 * (a + b) * h) :=
    Real.exp_le_exp.2 (by nlinarith [mul_nonneg ha hh])
  have e2 : Real.exp ((b + 3 * a) * h) ≤ Real.exp (3 * (a + b) * h) :=
    Real.exp_le_exp.2 (by nlinarith [mul_nonneg hb hh])
  have m1 := mul_le_mul_of_nonneg_right e1 hΓ
  have m2 := mul_le_mul_of_nonneg_right e2 hΓ
  have e : A t₁ - galerkinProj Ua Va (A t₁)
      = (A t₁ - Ua * Uaᵀ * A t₁) + Ua * Uaᵀ * (A t₁ - A t₁ * Va * Vaᵀ) := by
    change A t₁ - leftProj Ua (rightProj Va (A t₁)) = _
    rw [leftProj_apply, rightProj_apply, Matrix.mul_sub]
    abel
  have hc2 : ‖Ua * Uaᵀ * (A t₁ - A t₁ * Va * Vaᵀ)‖ ≤ ‖A t₁ - A t₁ * Va * Vaᵀ‖ := by
    have := (isOrthProj_leftProj (n := n) hs.orthUa).norm_le (A t₁ - A t₁ * Va * Vaᵀ)
    rwa [leftProj_apply] at this
  rw [e]
  have := norm_add_le (A t₁ - Ua * Uaᵀ * A t₁) (Ua * Uaᵀ * (A t₁ - A t₁ * Va * Vaᵀ))
  linarith

/-- **Local error of the rank-adaptive BUG step for a perturbed Sylvester field.**  Let
`F(Y) = 𝒜 Y + Y ℬ + G(Y)` be `L`-Lipschitz, with `‖𝒜‖ ≤ a`, `‖ℬ‖ ≤ b` (Frobenius norms) and `G`
Lipschitz with constant `g`.  Every step of the rank-adaptive BUG integrator
(Ceruti–Kusch–Lubich, [CerutiKuschLubich2022]; `MatrixBUG.IsRankAdaptiveStep`) with truncation
tolerance `ϑ` satisfies

    ‖Y₁ - A(t₁)‖ ≤ (e^{L h} - 1) (θ + M₂ h²) + θ + ϑ,
    θ = 2 h ε₀ + 4 e^{3 (a + b) h} h² (g B + (a + b) γ₀),

with the quantities of `norm_sub_galerkinProj_le_of_perturbedSylvester` and `M₂` a bound of the
derivative of `t ↦ F(t, A(t))`.  So the local error is `O(h ε₀ + (g B + (a + b) γ₀) h² + h³)`:
of the order of a second-order method when the perturbation is of size `O(h)`, and of the order
of a first-order method otherwise.  The term `g B h²` cannot be dropped: for the field
`Examples.rowField` (`ε₀ = 0`, `γ₀ = 0`) the error is at least `h² / 2`
(`error_ge_of_isRankAdaptiveStep`).  The exponent `3 (a + b) h` makes the bound useless for
stiff `𝒜`, `ℬ`. -/
theorem error_le_of_perturbedSylvester {ϑ L g h : ℝ}
    (hFS : ∀ t Y, F t Y = 𝒜 * Y + Y * ℬ + G Y) (hG : ∀ X Y, ‖G X - G Y‖ ≤ g * ‖X - Y‖)
    (hg : 0 ≤ g) (hF : IsLipschitzField F L) (hL : 0 ≤ L) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) {a₂ : ℝ → Matrix m n ℝ} {M₂ : ℝ}
    (ha : ContinuousOn (fun t => F t (A t)) (Icc t₀ t₁))
    (ha' : ∀ s ∈ Ico t₀ t₁, HasDerivWithinAt (fun t => F t (A t)) (a₂ s) (Ici s) s)
    (hM₂ : ∀ s ∈ Ico t₀ t₁, ‖a₂ s‖ ≤ M₂) {a b B γ₀ ε₀ θ : ℝ} (h𝒜 : ‖𝒜‖ ≤ a) (hℬ : ‖ℬ‖ ≤ b)
    (hBA : ∀ t ∈ Ico t₀ t₁, ‖F t (A t)‖ ≤ B) (hBK : ∀ t ∈ Ico t₀ t₁, ‖F t (K t * V₀ᵀ)‖ ≤ B)
    (hBL : ∀ t ∈ Ico t₀ t₁, ‖F t (U₀ * (Lf t)ᵀ)‖ ≤ B) (hγ₀ : ‖G (U₀ * S₀ * V₀ᵀ)‖ ≤ γ₀)
    (hε₀ : ‖(1 - U₀ * U₀ᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε₀)
    (hθ : θ = 2 * h * ε₀ + 4 * Real.exp (3 * (a + b) * h) * h ^ 2 * (g * B + (a + b) * γ₀)) :
    ‖Y₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (θ + M₂ * h ^ 2) + θ + ϑ := by
  have hR : IsOrthProj (galerkinProj Ua Va : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) :=
    isOrthProj_galerkinProj hs.orthUa hs.orthVa
  have hcap : ‖galerkinProj Ua Va (A t₁) - A t₁‖ ≤ θ := by
    rw [norm_sub_rev, hθ]
    exact norm_sub_galerkinProj_le_of_perturbedSylvester hFS hG hg ht₁ hh hs hA hA₀ h𝒜 hℬ hBA
      hBK hBL hγ₀ hε₀
  have hRA : galerkinProj Ua Va (A t₀) = A t₀ := by
    change leftProj Ua (rightProj Va (A t₀)) = A t₀
    rw [hA₀, hs.aug_right, hs.aug_left]
  have hfix : galerkinProj Ua Va (galerkinProj Ua Va (A t₁)) = galerkinProj Ua Va (A t₁) :=
    hR.idem _
  have hYS : ODESolution (fun t x => galerkinProj Ua Va (F t x)) (fun t => Ua * Sa t * Vaᵀ)
      t₀ t₁ := odeSolution_sField hs.sSol
  have hS₀ : (fun t => Ua * Sa t * Vaᵀ) t₀ = A t₀ := hs.start_eq.trans hA₀.symm
  have hb := galerkin_error_of_predictor (E := Matrix m n ℝ) (R := galerkinProj Ua Va)
    (YS := fun t => Ua * Sa t * Vaᵀ) hR hF hL ht₁ hh hA hRA ha ha' hM₂ hfix hcap hYS hS₀
  have hb' : ‖Ua * Sa t₁ * Vaᵀ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (θ + M₂ * h ^ 2) + θ := hb
  have htri := norm_sub_le_norm_sub_add_norm_sub Y₁ (Ua * Sa t₁ * Vaᵀ) (A t₁)
  linarith [hs.trunc]

end PerturbedSylvester

/-! ### An example with a nonzero perturbation -/

namespace Examples

/-- The direction `E₃₂` of the perturbation. -/
noncomputable def pertDir : Matrix (Fin 3) (Fin 2) ℝ := !![0, 0; 0, 0; 0, 1]

/-- The perturbation `G(Y) = Y₁₁ E₃₂`: Lipschitz with constant `‖E₃₂‖`, not constant, and nonzero
at `Y₀ = e₁ e₁ᵀ`. -/
noncomputable def pertMap (Y : Matrix (Fin 3) (Fin 2) ℝ) : Matrix (Fin 3) (Fin 2) ℝ :=
  Y 0 0 • pertDir

/-- The field `F(Y) = E₂₁ Y + Y E₁₂ + Y₁₁ E₃₂`: `sylField` with the perturbation `pertMap`.  Its
normal component at `Y₀ = e₁ e₁ᵀ` is `E₃₂`. -/
noncomputable def pertField (Y : Matrix (Fin 3) (Fin 2) ℝ) : Matrix (Fin 3) (Fin 2) ℝ :=
  sylField Y + pertMap Y

/-- Coefficient of `1` in the exact solution of `A' = pertField A`, `A(0) = e₁ e₁ᵀ`. -/
private noncomputable def pertCoeff0 : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 0; 0, 0]

/-- Coefficient of `t` in that solution. -/
private noncomputable def pertCoeff1 : Matrix (Fin 3) (Fin 2) ℝ := !![0, 1; 1, 0; 0, 1]

/-- Coefficient of `t²` in that solution. -/
private noncomputable def pertCoeff2 : Matrix (Fin 3) (Fin 2) ℝ := !![0, 0; 0, 1; 0, 0]

/-- The exact solution `A(t) = [[1, t], [t, t²], [0, t]]` of `A' = pertField A`,
`A(0) = e₁ e₁ᵀ`.  Its third row is not zero, so it leaves the range of `Û = [e₁, e₂]`. -/
noncomputable def pertSolution (t : ℝ) : Matrix (Fin 3) (Fin 2) ℝ :=
  pertCoeff0 + t • pertCoeff1 + t ^ 2 • pertCoeff2

/-- A Lipschitz constant of `pertField`. -/
private noncomputable def pertLip : ℝ := ‖rowFieldLeft 0‖ + ‖rowFieldRight‖ + ‖pertDir‖

/-- A bound of `pertField` along the exact solution and the K- and L-step solutions on
`[0, h]`. -/
private noncomputable def pertBound (h : ℝ) : ℝ :=
  pertLip * (Real.exp (pertLip * h) * (‖kSolution 0‖ + ‖lSolution 0‖ + ‖pertSolution 0‖))

end Examples

section PerturbedExample

open MatrixBUG Examples

private theorem pertDir_mul_startRight : pertDir * startRight = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pertDir, startRight, Matrix.mul_apply]

private theorem transpose_pertDir_mul_startLeft : pertDirᵀ * startLeft = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pertDir, startLeft, Matrix.mul_apply, Fin.sum_univ_three]

private theorem transpose_augmentedLeft_mul_pertDir : augmentedLeftᵀ * pertDir = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pertDir, augmentedLeft, Matrix.mul_apply, Fin.sum_univ_three]

/-- The K-step fields of `pertField` and of `sylField` agree. -/
private theorem kField_pertField :
    (kField startRight fun _ : ℝ => pertField) = kField startRight fun _ => sylField := by
  funext t K
  simp only [kField, pertField, pertMap, Matrix.add_mul, Matrix.smul_mul,
    pertDir_mul_startRight, smul_zero, add_zero]

/-- The L-step fields of `pertField` and of `sylField` agree. -/
private theorem lField_pertField :
    (lField startLeft fun _ : ℝ => pertField) = lField startLeft fun _ => sylField := by
  funext t L
  simp only [lField, pertField, pertMap, Matrix.transpose_add, Matrix.transpose_smul,
    Matrix.add_mul, Matrix.smul_mul, transpose_pertDir_mul_startLeft, smul_zero, add_zero]

/-- The Galerkin fields of `pertField` and of `sylField` in the bases `Û = [e₁, e₂]`, `V̂ = I₂`
agree. -/
private theorem sField_pertField :
    (sField augmentedLeft (1 : Matrix (Fin 2) (Fin 2) ℝ) fun _ : ℝ => pertField) =
      sField augmentedLeft (1 : Matrix (Fin 2) (Fin 2) ℝ) fun _ => sylField := by
  funext t S
  simp only [sField, pertField, pertMap, Matrix.mul_add, Matrix.mul_smul,
    transpose_augmentedLeft_mul_pertDir, smul_zero, add_zero]

/-- The step of `isRankAdaptiveStep_sylField` is also a rank-adaptive BUG step for `pertField`:
the perturbation `Y₁₁ E₃₂` is invisible to the three substeps. -/
theorem isRankAdaptiveStep_pertField (h : ℝ) :
    IsRankAdaptiveStep (fun _ => pertField) 0 0 h startLeft 1 startRight augmentedLeft
      (1 : Matrix (Fin 2) (Fin 2) ℝ) kSolution lSolution galerkinSolution
      (augmentedLeft * galerkinSolution h * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ) where
  orthU₀ := startLeft_orth
  orthV₀ := startRight_orth
  kSol := by rw [kField_pertField]; exact (isRankAdaptiveStep_sylField h).kSol
  kStart := (isRankAdaptiveStep_sylField h).kStart
  lSol := by rw [lField_pertField]; exact (isRankAdaptiveStep_sylField h).lSol
  lStart := (isRankAdaptiveStep_sylField h).lStart
  orthUa := (isRankAdaptiveStep_sylField h).orthUa
  kCap := (isRankAdaptiveStep_sylField h).kCap
  augU := (isRankAdaptiveStep_sylField h).augU
  orthVa := (isRankAdaptiveStep_sylField h).orthVa
  lCap := (isRankAdaptiveStep_sylField h).lCap
  augV := (isRankAdaptiveStep_sylField h).augV
  sSol := by rw [sField_pertField]; exact (isRankAdaptiveStep_sylField h).sSol
  sStart := (isRankAdaptiveStep_sylField h).sStart
  trunc := (isRankAdaptiveStep_sylField h).trunc

/-- `pertMap` is Lipschitz with the constant `‖E₃₂‖`. -/
theorem norm_pertMap_sub_le (X Y : Matrix (Fin 3) (Fin 2) ℝ) :
    ‖pertMap X - pertMap Y‖ ≤ ‖pertDir‖ * ‖X - Y‖ := by
  rw [pertMap, pertMap, ← sub_smul, norm_smul, Real.norm_eq_abs, mul_comm]
  exact mul_le_mul_of_nonneg_left (Frobenius.abs_apply_le_norm (X - Y) 0 0) (norm_nonneg _)

/-- `pertField` is Lipschitz with the constant `‖E₂₁‖ + ‖E₁₂‖ + ‖E₃₂‖`. -/
private theorem isLipschitzField_pertField : IsLipschitzField (fun _ : ℝ => pertField) pertLip :=
  fun t X Y => by
    change ‖pertField X - pertField Y‖ ≤ pertLip * ‖X - Y‖
    have h1 : ‖sylField X - sylField Y‖ ≤ (‖rowFieldLeft 0‖ + ‖rowFieldRight‖) * ‖X - Y‖ :=
      isLipschitzField_sylField t X Y
    have h2 := norm_pertMap_sub_le X Y
    have e : pertField X - pertField Y = (sylField X - sylField Y) + (pertMap X - pertMap Y) := by
      simp only [pertField]
      abel
    rw [e, pertLip, add_mul]
    exact norm_add_le_of_le h1 h2

private theorem pertLip_nonneg : 0 ≤ pertLip := by
  rw [pertLip]
  positivity

/-- `pertField` has linear growth: it is Lipschitz and vanishes at `0`. -/
private theorem norm_pertField_le (Y : Matrix (Fin 3) (Fin 2) ℝ) :
    ‖pertField Y‖ ≤ pertLip * ‖Y‖ := by
  have h0 : pertField 0 = 0 := by simp [pertField, pertMap, sylField]
  have := isLipschitzField_pertField 0 Y 0
  simpa [h0] using this

/-- A solution of an equation with a field of linear growth grows at most exponentially. -/
private theorem norm_le_exp_mul_of_growth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E → E} {y : ℝ → E} {L h : ℝ} (hy : ODESolution f y 0 h)
    (hf : ∀ t x, ‖f t x‖ ≤ L * ‖x‖) (hL : 0 ≤ L) :
    ∀ t ∈ Icc (0 : ℝ) h, ‖y t‖ ≤ Real.exp (L * h) * ‖y 0‖ := by
  intro t ht
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le (δ := ‖y 0‖) (K := L) (ε := 0)
    hy.cont hy.deriv le_rfl (fun s _ => by rw [add_zero]; exact hf s (y s)) t ht
  have h2 := gronwallBound_le_exp_mul (δ := ‖y 0‖) (x := t - 0) hL (le_refl (0 : ℝ))
  have h3 : Real.exp (L * (t - 0)) ≤ Real.exp (L * h) :=
    Real.exp_le_exp.2 (by rw [sub_zero]; exact mul_le_mul_of_nonneg_left ht.2 hL)
  calc ‖y t‖ ≤ Real.exp (L * (t - 0)) * (‖y 0‖ + 0 * (t - 0)) := hg.trans h2
    _ = Real.exp (L * (t - 0)) * ‖y 0‖ := by ring
    _ ≤ Real.exp (L * h) * ‖y 0‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)

/-- Along `pertSolution` the field is `C₁ + 2 t C₂`. -/
private theorem pertField_pertSolution (t : ℝ) :
    pertField (pertSolution t) = pertCoeff1 + (2 * t) • pertCoeff2 := by
  ext i j
  simp only [pertField, pertMap, sylField, Matrix.add_apply, Matrix.smul_apply,
    Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [rowFieldLeft, rowFieldRight, pertSolution, pertCoeff0, pertCoeff1, pertCoeff2,
      pertDir]
  ring

private theorem hasDerivAt_pertSolution (t : ℝ) :
    HasDerivAt pertSolution (pertField (pertSolution t)) t := by
  have h1 : HasDerivAt (fun s : ℝ => s • pertCoeff1) pertCoeff1 t := by
    simpa using (hasDerivAt_id t).smul_const pertCoeff1
  have h2 : HasDerivAt (fun s : ℝ => s ^ 2 • pertCoeff2) ((2 * t) • pertCoeff2) t := by
    simpa using (hasDerivAt_pow 2 t).smul_const pertCoeff2
  rw [pertField_pertSolution]
  exact (h1.const_add pertCoeff0).add h2

/-- `pertSolution` solves `A' = pertField A` on every interval `[0, h]`. -/
theorem odeSolution_pertSolution (h : ℝ) :
    ODESolution (fun _ => pertField) pertSolution 0 h where
  cont := fun t _ => (hasDerivAt_pertSolution t).continuousAt.continuousWithinAt
  deriv := fun t _ => (hasDerivAt_pertSolution t).hasDerivWithinAt

/-- `pertSolution 0 = U₀ S₀ V₀ᵀ` with `S₀ = 1`. -/
theorem pertSolution_zero :
    pertSolution 0 = startLeft * (1 : Matrix (Fin 1) (Fin 1) ℝ) * startRightᵀ := by
  rw [Matrix.mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pertSolution, pertCoeff0, startLeft, startRight, Matrix.mul_apply]

private theorem hasDerivAt_pertField_pertSolution (s : ℝ) :
    HasDerivAt (fun t => pertField (pertSolution t)) ((2 : ℝ) • pertCoeff2) s := by
  have he : (fun t => pertField (pertSolution t)) =
      fun t => pertCoeff1 + (2 * t) • pertCoeff2 := funext pertField_pertSolution
  have h1 : HasDerivAt (fun t : ℝ => (2 * t) • pertCoeff2) ((2 : ℝ) • pertCoeff2) s := by
    simpa using ((hasDerivAt_id s).const_mul (2 : ℝ)).smul_const pertCoeff2
  rw [he]
  exact h1.const_add pertCoeff1

private theorem norm_pertField_pertSolution_le {h : ℝ} :
    ∀ t ∈ Ico (0 : ℝ) h, ‖pertField (pertSolution t)‖ ≤ pertBound h := fun t ht => by
  have h1 := norm_le_exp_mul_of_growth (odeSolution_pertSolution h)
    (fun _ x => norm_pertField_le x) pertLip_nonneg t (Ico_subset_Icc_self ht)
  have h2 : ‖pertSolution t‖
      ≤ Real.exp (pertLip * h) * (‖kSolution 0‖ + ‖lSolution 0‖ + ‖pertSolution 0‖) :=
    h1.trans (mul_le_mul_of_nonneg_left
      (by linarith [norm_nonneg (kSolution 0), norm_nonneg (lSolution 0)]) (Real.exp_pos _).le)
  exact (norm_pertField_le _).trans (mul_le_mul_of_nonneg_left h2 pertLip_nonneg)

private theorem norm_pertField_kSolution_le {h : ℝ} :
    ∀ t ∈ Ico (0 : ℝ) h, ‖pertField (kSolution t * startRightᵀ)‖ ≤ pertBound h := fun t ht => by
  have hgrow : ∀ (s : ℝ) (x : Matrix (Fin 3) (Fin 1) ℝ),
      ‖kField startRight (fun _ => pertField) s x‖ ≤ pertLip * ‖x‖ := fun s x => by
    refine (norm_mul_le₁ startRight_orth _).trans ((norm_pertField_le _).trans_eq ?_)
    rw [Frobenius.norm_mul_transpose_of_orthonormal startRight_orth]
  have h1 := norm_le_exp_mul_of_growth (isRankAdaptiveStep_pertField h).kSol hgrow
    pertLip_nonneg t (Ico_subset_Icc_self ht)
  have h2 : ‖kSolution t * startRightᵀ‖
      ≤ Real.exp (pertLip * h) * (‖kSolution 0‖ + ‖lSolution 0‖ + ‖pertSolution 0‖) := by
    rw [Frobenius.norm_mul_transpose_of_orthonormal startRight_orth]
    exact h1.trans (mul_le_mul_of_nonneg_left
      (by linarith [norm_nonneg (lSolution 0), norm_nonneg (pertSolution 0)])
      (Real.exp_pos _).le)
  exact (norm_pertField_le _).trans (mul_le_mul_of_nonneg_left h2 pertLip_nonneg)

private theorem norm_pertField_lSolution_le {h : ℝ} :
    ∀ t ∈ Ico (0 : ℝ) h, ‖pertField (startLeft * (lSolution t)ᵀ)‖ ≤ pertBound h := fun t ht => by
  have hgrow : ∀ (s : ℝ) (x : Matrix (Fin 2) (Fin 1) ℝ),
      ‖lField startLeft (fun _ => pertField) s x‖ ≤ pertLip * ‖x‖ := fun s x => by
    refine (norm_mul_le₁ startLeft_orth _).trans ?_
    rw [Frobenius.norm_transpose]
    refine (norm_pertField_le _).trans_eq ?_
    rw [Frobenius.norm_mul_of_orthonormal startLeft_orth, Frobenius.norm_transpose]
  have h1 := norm_le_exp_mul_of_growth (isRankAdaptiveStep_pertField h).lSol hgrow
    pertLip_nonneg t (Ico_subset_Icc_self ht)
  have h2 : ‖startLeft * (lSolution t)ᵀ‖
      ≤ Real.exp (pertLip * h) * (‖kSolution 0‖ + ‖lSolution 0‖ + ‖pertSolution 0‖) := by
    rw [Frobenius.norm_mul_of_orthonormal startLeft_orth, Frobenius.norm_transpose]
    exact h1.trans (mul_le_mul_of_nonneg_left
      (by linarith [norm_nonneg (kSolution 0), norm_nonneg (pertSolution 0)])
      (Real.exp_pos _).le)
  exact (norm_pertField_le _).trans (mul_le_mul_of_nonneg_left h2 pertLip_nonneg)

/-- The perturbation does not vanish at the starting value: `G(Y₀) = E₃₂`. -/
theorem pertMap_start :
    pertMap (startLeft * (1 : Matrix (Fin 1) (Fin 1) ℝ) * startRightᵀ) = pertDir := by
  rw [pertMap]
  have h : (startLeft * (1 : Matrix (Fin 1) (Fin 1) ℝ) * startRightᵀ) 0 0 = 1 := by
    simp [startLeft, startRight, Matrix.mul_apply]
  rw [h, one_smul]

/-- `E₃₂ ≠ 0`, so the Lipschitz constant `g = ‖E₃₂‖` and `γ₀ = ‖G(Y₀)‖ = ‖E₃₂‖` of the example
are not zero. -/
theorem norm_pertDir_pos : 0 < ‖pertDir‖ := by
  refine norm_pos_iff.2 fun h => ?_
  have := congrFun (congrFun h 2) 1
  simp [pertDir] at this

/-- Non-vacuity of `error_le_of_perturbedSylvester` with a perturbation that is not constant and
does not vanish at the start: the field `pertField` (`𝒜 = E₂₁`, `ℬ = E₁₂`, `G(Y) = Y₁₁ E₃₂`), the
start `Y₀ = e₁ e₁ᵀ`, the step of `isRankAdaptiveStep_pertField` and the exact solution
`pertSolution`, with `g = γ₀ = ‖E₃₂‖ ≠ 0` (`norm_pertDir_pos`, `pertMap_start`). -/
example (h : ℝ) (hh : 0 ≤ h) : ∃ B ε₀ L M₂ : ℝ,
    ‖augmentedLeft * galerkinSolution h * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ - pertSolution h‖ ≤
      (Real.exp (L * h) - 1) *
        ((2 * h * ε₀ + 4 * Real.exp (3 * (‖rowFieldLeft 0‖ + ‖rowFieldRight‖) * h) * h ^ 2 *
          (‖pertDir‖ * B + (‖rowFieldLeft 0‖ + ‖rowFieldRight‖) * ‖pertDir‖)) + M₂ * h ^ 2) +
        (2 * h * ε₀ + 4 * Real.exp (3 * (‖rowFieldLeft 0‖ + ‖rowFieldRight‖) * h) * h ^ 2 *
          (‖pertDir‖ * B + (‖rowFieldLeft 0‖ + ‖rowFieldRight‖) * ‖pertDir‖)) + 0 :=
  ⟨pertBound h, _, pertLip, ‖(2 : ℝ) • pertCoeff2‖,
    error_le_of_perturbedSylvester (F := fun _ => pertField) (𝒜 := rowFieldLeft 0)
      (ℬ := rowFieldRight) (G := pertMap) (a₂ := fun _ => (2 : ℝ) • pertCoeff2) (t₀ := 0)
      (t₁ := h) (fun _ _ => rfl) norm_pertMap_sub_le (norm_nonneg _) isLipschitzField_pertField
      pertLip_nonneg (zero_add h).symm hh (isRankAdaptiveStep_pertField h)
      (odeSolution_pertSolution h) pertSolution_zero
      (fun s _ => (hasDerivAt_pertField_pertSolution s).continuousAt.continuousWithinAt)
      (fun s _ => (hasDerivAt_pertField_pertSolution s).hasDerivWithinAt) (fun _ _ => le_rfl)
      le_rfl le_rfl norm_pertField_pertSolution_le norm_pertField_kSolution_le
      norm_pertField_lSolution_le (le_of_eq (congrArg _ pertMap_start)) le_rfl rfl⟩

end PerturbedExample

end AugmentationRank

end LeanDLRA
