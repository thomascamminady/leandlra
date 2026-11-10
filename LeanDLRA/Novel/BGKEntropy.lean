import Mathlib
import LeanDLRA.LinearAlgebra.Factorization.Defs

/-!
# The conservative `L²`-orthogonal DLRA of BGK can increase the entropy

Negative counterpart of OP-SB-52 (`NovelOpSB52`).  There the log-DLRA with the
entropy-Hessian projector inherits the H-theorem; here the `L²`-orthogonal DLRA of `f` does not,
even with the collision invariants in the velocity basis.  This turns the numerical counterexample
quoted in `NovelOpSB52` into a theorem, on a smaller grid and with exact numbers.

## Setting

Discrete BGK on `m` cells and velocities `v₁, …, vₙ` with unit quadrature weights:
`ḟ = M[f] - f`, where row `i` of `M[f]` is the discrete Maxwellian `exp (a + b v + c v²)`, `c < 0`,
with the mass, momentum and energy of row `i` of `f` (`IsMaxwellianOf`; unique by
`IsMaxwellianOf.unique`).  The entropy is `H = Σ f log f`, with rate `⟪ḟ, log f + 1⟫`
(`hasDerivAt_entropy`).  The conservative DLRA replaces the right-hand side by `P (M[f] - f)`,

  `P Z = PU Z + Z PV - PU Z PV` (`dlraField`),

where `PU` is the orthogonal projector onto the column space of `f` and `PV` the one onto
`span (rows of f, 1, v, v²)`.  This is the augmented projector of the numerical script.  It fixes
`f` and conserves the moments of every cell (`dlraField_moment`), but because of the augmentation
its range is larger than the tangent space of the rank-`r` manifold.

## The construction

Rank three is exactly what makes the moments exact: if the moment matrix of `b1, b2, b3` is
invertible, every moment vector is attained in `span (b1, b2, b3)`.  So one starts from the
Maxwellian and computes `f`, and no Newton iteration or error bound for `M[f]` is needed.

* `v ∈ {-3, …, 3}`, `m = 4`, `n = 7`, `r = 3`.
* `b1 = 2^(5 v - v²)`, `b2 = 2^(-5 v - v²)`, `b3 = 2^(-v²)`: one temperature, mean velocities
  `5/2`, `-5/2`, `0`, and every entry a power of two.
* `M₀` has rows `b1, b2, 2 b3, b3`, a rank-three matrix of discrete Maxwellians.
* `MState ε` has last row `yv ε = b3 exp (ε v)`, `fState ε` has last row `Ty (yv ε)`, the element of
  `span (b1, b2, b3)` with those moments.  The other rows agree with `M₀`, so they are Maxwellian.

Then the augmented velocity space is `w^⊥` with the fixed integer vector
`w = (-1024, 513, 2046, 0, -2046, -513, 1024)` (`augSpace_eq`), the column space is `(uvec _)^⊥`
(`colSpace_eq`), and `I - P` is the rank-one projection onto `u wᵀ` (`dlraField_hyperProj`).
With `F = M - f`, `L = log f + 1`,

  `⟪P F, L⟫ = ⟪F, L⟫ - ⟪F, u wᵀ⟫ ⟪L, u wᵀ⟫ / (‖u‖² ‖w‖²)`.

Only the last row enters, because `log` of a Maxwellian row is orthogonal to `w`.  As `ε → 0`,
`F / ε` and `(log f - log M) / ε` have rational limits, and the two rates divided by `ε²` converge
to explicit rationals (`tendsto_entropyRates`): `≈ -21.05` for BGK and `≈ +2.65` for the DLRA.

## Main results

* `tendsto_entropyRates`: the exact second-order rates along the family.
* `exists_entropy_increase_near_maxwellian`: for every `δ > 0`, a positive rank-three state within
  relative distance `δ` of `M₀` at which BGK dissipates and the conservative DLRA field, which
  conserves mass, momentum and energy, strictly increases `H`.
* `entropy_lt_of_entropyRate_pos`, `entropy_euler_step`: the entropy really grows along any curve
  with this velocity and under small explicit Euler steps.

## What this does not say

* The result is for this discretisation (four cells, seven velocities, rank three).  It is not
  shown for other grids, and the `5 × 12` instance of the script is not covered.  Here `I - P` has
  rank one, which is what makes the computation exact.
* It is an instantaneous statement about the field `P (M[f] - f)`.  Since the range of `P` is not
  tangent to the rank-three manifold, no rank-three trajectory is claimed, and the Euler step
  `f + h P (M[f] - f)` is not claimed to have rank three.
* The growth is of order `ε²`, as is the dissipation it replaces.
-/

open Filter Topology Matrix

namespace LeanDLRA.Novel.BGKEntropy

section General

variable {m n : Type*} [Fintype n]

/-- The collision invariants `1, v, v²` on a velocity grid `v`. -/
def collInv (v : n → ℝ) (k : Fin 3) : n → ℝ := fun j => v j ^ (k : ℕ)

/-- `M` is a matrix of discrete Maxwellians on the velocity grid `v`: every row is
`j ↦ exp (a + b v_j + c v_j²)` with `c < 0` (positive temperature). -/
def IsDiscreteMaxwellian (v : n → ℝ) (M : Matrix m n ℝ) : Prop :=
  ∃ a b c : m → ℝ, (∀ i, c i < 0) ∧ ∀ i j, M i j = Real.exp (a i + b i * v j + c i * v j ^ 2)

/-- `M` is the Maxwellian of `f`: a discrete Maxwellian with the cellwise mass, momentum and energy
of `f`.  It is unique when it exists, see `IsMaxwellianOf.unique`. -/
structure IsMaxwellianOf (v : n → ℝ) (f M : Matrix m n ℝ) : Prop where
  maxwellian : IsDiscreteMaxwellian v M
  moments : ∀ i k, f i ⬝ᵥ collInv v k = M i ⬝ᵥ collInv v k

private lemma mul_log_sub_nonneg {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 ≤ (x - y) * (Real.log x - Real.log y) := by
  rcases le_total x y with h | h
  · have := Real.log_le_log hx h
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  · have := Real.log_le_log hy h
    exact mul_nonneg (by linarith) (by linarith)

private lemma eq_of_mul_log_sub_eq_zero {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : (x - y) * (Real.log x - Real.log y) = 0) : x = y := by
  rcases mul_eq_zero.1 h with h | h
  · linarith
  · exact Real.log_injOn_pos (Set.mem_Ioi.2 hx) (Set.mem_Ioi.2 hy) (by linarith)

/-- The Maxwellian of `f` is unique: the BGK operator `f ↦ M[f] - f` is well defined. -/
theorem IsMaxwellianOf.unique {v : n → ℝ} {f M M' : Matrix m n ℝ} (h : IsMaxwellianOf v f M)
    (h' : IsMaxwellianOf v f M') : M = M' := by
  obtain ⟨a, b, c, -, hM⟩ := h.maxwellian
  obtain ⟨a', b', c', -, hM'⟩ := h'.maxwellian
  ext i j
  have hpos : ∀ j, 0 < M i j := fun j => by rw [hM]; exact Real.exp_pos _
  have hpos' : ∀ j, 0 < M' i j := fun j => by rw [hM']; exact Real.exp_pos _
  have hmom : ∀ k : Fin 3, ∑ j, (M i j - M' i j) * collInv v k j = 0 := fun k => by
    have := (h.moments i k).symm.trans (h'.moments i k)
    simp only [dotProduct] at this
    simp only [sub_mul, Finset.sum_sub_distrib, this, sub_self]
  have h0 := hmom 0
  have h1 := hmom 1
  have h2 := hmom 2
  simp only [collInv, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, mul_one]
    at h0 h1 h2
  have hsum : ∑ j, (M i j - M' i j) * (Real.log (M i j) - Real.log (M' i j)) = 0 := by
    have e : ∀ j, (M i j - M' i j) * (Real.log (M i j) - Real.log (M' i j))
        = (a i - a' i) * (M i j - M' i j) + (b i - b' i) * ((M i j - M' i j) * v j)
          + (c i - c' i) * ((M i j - M' i j) * v j ^ 2) := fun j => by
      rw [hM i j, hM' i j, Real.log_exp, Real.log_exp]; ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, h0, h1, h2]
    ring
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => mul_log_sub_nonneg (hpos j) (hpos' j))).1 hsum j (Finset.mem_univ j)
  exact eq_of_mul_log_sub_eq_zero (hpos j) (hpos' j) hz

variable [Fintype m]

/-- The entropy `Σ f log f` (the `H` of the H-theorem: it decreases along BGK). -/
noncomputable def entropy (f : Matrix m n ℝ) : ℝ := ∑ i, ∑ j, f i j * Real.log (f i j)

/-- The rate of change `⟪Z, log f + 1⟫` of the entropy at `f` in the direction `Z`. -/
noncomputable def entropyRate (f Z : Matrix m n ℝ) : ℝ :=
  ∑ i, ∑ j, Z i j * (Real.log (f i j) + 1)

/-- The entropy rate is the derivative of the entropy along any curve through a positive state. -/
theorem hasDerivAt_entropy {φ : ℝ → Matrix m n ℝ} {Z : Matrix m n ℝ} {t : ℝ}
    (hpos : ∀ i j, 0 < φ t i j) (h : ∀ i j, HasDerivAt (fun s => φ s i j) (Z i j) t) :
    HasDerivAt (fun s => entropy (φ s)) (entropyRate (φ t) Z) t := by
  unfold entropy entropyRate
  refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
  have := (h i j).mul ((h i j).log (hpos i j).ne')
  convert this using 1
  have := (hpos i j).ne'
  field_simp

/-- If the entropy rate along a curve is positive, the entropy strictly increases right after. -/
theorem entropy_lt_of_entropyRate_pos {φ : ℝ → Matrix m n ℝ} {Z : Matrix m n ℝ}
    (hpos : ∀ i j, 0 < φ 0 i j) (h : ∀ i j, HasDerivAt (fun s => φ s i j) (Z i j) 0)
    (hZ : 0 < entropyRate (φ 0) Z) : ∀ᶠ t in 𝓝[>] (0 : ℝ), entropy (φ 0) < entropy (φ t) := by
  have hd := hasDerivAt_iff_tendsto_slope.1 (hasDerivAt_entropy hpos h)
  have hs : ∀ᶠ t in 𝓝[≠] (0 : ℝ), 0 < slope (fun s => entropy (φ s)) 0 t :=
    hd.eventually (lt_mem_nhds hZ)
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] 0 := nhdsWithin_mono _ fun t (ht : 0 < t) => ht.ne'
  filter_upwards [hle hs, self_mem_nhdsWithin] with t ht (h0 : 0 < t)
  rw [slope_def_field, sub_zero] at ht
  have := (div_pos_iff_of_pos_right h0).1 ht
  linarith

/-- The explicit Euler step of a field with positive entropy rate increases the entropy, for
every small enough step size. -/
theorem entropy_euler_step {f Z : Matrix m n ℝ} (hf : ∀ i j, 0 < f i j)
    (hZ : 0 < entropyRate f Z) : ∀ᶠ h in 𝓝[>] (0 : ℝ), entropy f < entropy (f + h • Z) := by
  have hderiv : ∀ i j, HasDerivAt (fun s : ℝ => (f + s • Z) i j) (Z i j) 0 := fun i j => by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const (Z i j)).const_add (f i j)
    simpa using this
  have h0 : f + (0 : ℝ) • Z = f := by simp
  have := entropy_lt_of_entropyRate_pos (φ := fun s : ℝ => f + s • Z) (Z := Z)
    (by simpa [h0] using hf) hderiv (by simpa [h0] using hZ)
  simpa [h0] using this

/-- The `L²`-orthogonal projection of the direction `Z` used by DLRA: with `PU = U Uᵀ` and
`PV = V Vᵀ`, `Z ↦ U Uᵀ Z + Z V Vᵀ - U Uᵀ Z V Vᵀ`. -/
def dlraField (PU : Matrix m m ℝ) (PV : Matrix n n ℝ) (Z : Matrix m n ℝ) : Matrix m n ℝ :=
  PU * Z + Z * PV - PU * Z * PV

/-- **Conservation.**  If `φ` is in the range of `PV`, the DLRA field has the same `φ`-moments in
every cell as the direction it projects.  With `φ = 1, v, v²` this is the local conservation of
mass, momentum and energy by the augmented projector. -/
theorem dlraField_moment (PU : Matrix m m ℝ) {PV : Matrix n n ℝ} (Z : Matrix m n ℝ) {φ : n → ℝ}
    (hφ : PV *ᵥ φ = φ) (i : m) : dlraField PU PV Z i ⬝ᵥ φ = Z i ⬝ᵥ φ := by
  have : dlraField PU PV Z *ᵥ φ = Z *ᵥ φ := by
    simp only [dlraField, Matrix.sub_mulVec, Matrix.add_mulVec]
    rw [← Matrix.mulVec_mulVec φ Z PV, hφ, ← Matrix.mulVec_mulVec φ (PU * Z) PV, hφ]
    abel
  exact congrFun this i

/-- The velocity space of the conservative DLRA of `f`: the span of the rows of `f` and of the
collision invariants (basis augmentation by `1, v, v²`). -/
def augSpace (v : n → ℝ) (f : Matrix m n ℝ) : Submodule ℝ (n → ℝ) :=
  Submodule.span ℝ (Set.range (fun i => f i) ∪ Set.range (collInv v))

end General

section Projector

variable {ι : Type*} [Fintype ι]

lemma mem_hyperplane {u x : ι → ℝ} : x ∈ hyperplane u ↔ u ⬝ᵥ x = 0 := Iff.rfl

variable [DecidableEq ι]

lemma hyperProj_mulVec (u x : ι → ℝ) :
    hyperProj u *ᵥ x = x - ((u ⬝ᵥ u)⁻¹ * (u ⬝ᵥ x)) • u := by
  ext i
  simp only [hyperProj, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    vecMulVec_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op]
  ring

theorem isOrthProjOnto_hyperProj {u : ι → ℝ} (hu : u ≠ 0) :
    IsOrthProjOnto (hyperProj u) (hyperplane u) := by
  have hne : u ⬝ᵥ u ≠ 0 := fun h => hu (dotProduct_self_eq_zero.1 h)
  refine ⟨?_, fun x => ?_, fun x hx => ?_⟩
  · simp only [hyperProj, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul,
      transpose_vecMulVec]
  · rw [mem_hyperplane, hyperProj_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    field_simp
    ring
  · rw [mem_hyperplane] at hx
    rw [hyperProj_mulVec, hx]
    simp

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The DLRA field with hyperplane ranges: the projector removes exactly the rank-one normal
direction `u wᵀ`. -/
lemma dlraField_hyperProj (u : κ → ℝ) (w : ι → ℝ) (Z : Matrix κ ι ℝ) :
    dlraField (hyperProj u) (hyperProj w) Z
      = Z - ((u ⬝ᵥ u)⁻¹ * (w ⬝ᵥ w)⁻¹ * (u ⬝ᵥ Z *ᵥ w)) • vecMulVec u w := by
  have h : (u ⬝ᵥ u)⁻¹ • vecMulVec u u * Z * (w ⬝ᵥ w)⁻¹ • vecMulVec w w
      = ((u ⬝ᵥ u)⁻¹ * (w ⬝ᵥ w)⁻¹ * (u ⬝ᵥ Z *ᵥ w)) • vecMulVec u w := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul, vecMul_vecMulVec,
      smul_smul, Matrix.dotProduct_mulVec]
    ext i j
    simp only [Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [dlraField, hyperProj, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
  rw [← h]
  abel

/-- The matrix `log f + 1`. -/
noncomputable def logOne (f : Matrix κ ι ℝ) : Matrix κ ι ℝ :=
  Matrix.of fun i j => Real.log (f i j) + 1

/-- The entropy rate of the DLRA field with hyperplane ranges. -/
lemma entropyRate_dlraField_hyperProj (f Z : Matrix κ ι ℝ) (u : κ → ℝ) (w : ι → ℝ) :
    entropyRate f (dlraField (hyperProj u) (hyperProj w) Z)
      = entropyRate f Z
        - (u ⬝ᵥ u)⁻¹ * (w ⬝ᵥ w)⁻¹ * (u ⬝ᵥ Z *ᵥ w) * (u ⬝ᵥ logOne f *ᵥ w) := by
  rw [dlraField_hyperProj]
  simp only [entropyRate, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
    sub_mul, Finset.sum_sub_distrib]
  congr 1
  simp only [dotProduct, mulVec, logOne, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Projector

/-! ### The concrete family -/

section Example

/-- The velocity grid `{-3, …, 3}`, with unit quadrature weights. -/
noncomputable def vel : Fin 7 → ℝ := ![-3, -2, -1, 0, 1, 2, 3]

/-- The velocities as integers. -/
def velZ : Fin 7 → ℤ := ![-3, -2, -1, 0, 1, 2, 3]

lemma vel_eq (j : Fin 7) : vel j = (velZ j : ℝ) := by
  fin_cases j <;> simp [vel, velZ]

/-- The Maxwellian `2^(5 v - v²)`. -/
noncomputable def b1 : Fin 7 → ℝ := ![1 / 2 ^ 24, 1 / 2 ^ 14, 1 / 2 ^ 6, 1, 2 ^ 4, 2 ^ 6, 2 ^ 6]

/-- The Maxwellian `2^(-5 v - v²)`, the mirror image of `b1`. -/
noncomputable def b2 : Fin 7 → ℝ := ![2 ^ 6, 2 ^ 6, 2 ^ 4, 1, 1 / 2 ^ 6, 1 / 2 ^ 14, 1 / 2 ^ 24]

/-- The Maxwellian `2^(-v²)`. -/
noncomputable def b3 : Fin 7 → ℝ := ![1 / 2 ^ 9, 1 / 2 ^ 4, 1 / 2, 1, 1 / 2, 1 / 2 ^ 4, 1 / 2 ^ 9]

/-- The normal vector of the augmented velocity space. -/
noncomputable def w : Fin 7 → ℝ := ![-1024, 513, 2046, 0, -2046, -513, 1024]

private lemma exp_eq_two_zpow (k : ℤ) (x : ℝ) (hx : x = k * Real.log 2) :
    Real.exp x = 2 ^ k := by
  rw [hx, mul_comm, ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_intCast]

lemma b1_eq (j : Fin 7) :
    b1 j = Real.exp (0 + 5 * Real.log 2 * vel j + -Real.log 2 * vel j ^ 2) := by
  rw [exp_eq_two_zpow (5 * velZ j - velZ j ^ 2) _ (by rw [vel_eq]; push_cast; ring)]
  fin_cases j <;> norm_num [b1, velZ]

lemma b2_eq (j : Fin 7) :
    b2 j = Real.exp (0 + -(5 * Real.log 2) * vel j + -Real.log 2 * vel j ^ 2) := by
  rw [exp_eq_two_zpow (-5 * velZ j - velZ j ^ 2) _ (by rw [vel_eq]; push_cast; ring)]
  fin_cases j <;> norm_num [b2, velZ]

lemma b3_eq (j : Fin 7) : b3 j = Real.exp (0 + 0 * vel j + -Real.log 2 * vel j ^ 2) := by
  rw [exp_eq_two_zpow (-velZ j ^ 2) _ (by rw [vel_eq]; push_cast; ring)]
  fin_cases j <;> norm_num [b3, velZ]

lemma two_b3_eq (j : Fin 7) :
    2 * b3 j = Real.exp (Real.log 2 + 0 * vel j + -Real.log 2 * vel j ^ 2) := by
  rw [exp_eq_two_zpow (1 - velZ j ^ 2) _ (by rw [vel_eq]; push_cast; ring)]
  fin_cases j <;> norm_num [b3, velZ]

lemma b1_pos (j : Fin 7) : 0 < b1 j := by rw [b1_eq]; exact Real.exp_pos _

lemma b2_pos (j : Fin 7) : 0 < b2 j := by rw [b2_eq]; exact Real.exp_pos _

lemma b3_pos (j : Fin 7) : 0 < b3 j := by rw [b3_eq]; exact Real.exp_pos _

lemma log_two_pos' : 0 < Real.log 2 := Real.log_pos (by norm_num)

/-- The Maxwellians in the last row: `2^(-v²)` with momentum shift `ε`. -/
noncomputable def yv (ε : ℝ) (j : Fin 7) : ℝ :=
  Real.exp (0 + ε * vel j + -Real.log 2 * vel j ^ 2)

lemma yv_zero : yv 0 = b3 := by
  funext j
  rw [b3_eq, yv]

lemma yv_pos (ε : ℝ) (j : Fin 7) : 0 < yv ε j := Real.exp_pos _

/-- The dual functional of `b1` on the moments. -/
noncomputable def k1 : Fin 7 → ℝ :=
  ![14207510709796864 / 12875707186027923853, -29786282015850496 / 38627121558083771559,
    -50238158614298624 / 38627121558083771559, -103022592 / 212429692909,
    64728900829184000 / 38627121558083771559, 200147836871114752 / 38627121558083771559,
    129174570153279488 / 12875707186027923853]

/-- The dual functional of `b2` on the moments. -/
noncomputable def k2 : Fin 7 → ℝ :=
  ![129174570153279488 / 12875707186027923853, 200147836871114752 / 38627121558083771559,
    64728900829184000 / 38627121558083771559, -103022592 / 212429692909,
    -50238158614298624 / 38627121558083771559, -29786282015850496 / 38627121558083771559,
    14207510709796864 / 12875707186027923853]

/-- The dual functional of `b3` on the moments. -/
noncomputable def k3 : Fin 7 → ℝ :=
  ![-61354319872 / 212429692909, 35964059688 / 212429692909, 94355087424 / 212429692909,
    113818763336 / 212429692909, 94355087424 / 212429692909, 35964059688 / 212429692909,
    -61354319872 / 212429692909]

/-- The unique element of `span (b1, b2, b3)` with the mass, momentum and energy of `y`. -/
noncomputable def Ty (y : Fin 7 → ℝ) (j : Fin 7) : ℝ :=
  (k1 ⬝ᵥ y) * b1 j + (k2 ⬝ᵥ y) * b2 j + (k3 ⬝ᵥ y) * b3 j

lemma Ty_moment (y : Fin 7 → ℝ) (k : Fin 3) : Ty y ⬝ᵥ collInv vel k = y ⬝ᵥ collInv vel k := by
  fin_cases k <;>
  · simp only [dotProduct, Fin.sum_univ_seven, Ty, collInv, k1, k2, k3, b1, b2, b3, vel]
    simp
    ring

lemma Ty_b3 : Ty b3 = b3 := by
  have h1 : k1 ⬝ᵥ b3 = 0 := by
    simp only [dotProduct, Fin.sum_univ_seven, k1, b3]; norm_num
  have h2 : k2 ⬝ᵥ b3 = 0 := by
    simp only [dotProduct, Fin.sum_univ_seven, k2, b3]; norm_num
  have h3 : k3 ⬝ᵥ b3 = 1 := by
    simp only [dotProduct, Fin.sum_univ_seven, k3, b3]; norm_num
  funext j
  simp [Ty, h1, h2, h3]


/-- The `4 × 7` matrix with rows `b1`, `b2`, `2 b3` and `r`. -/
noncomputable def mkMat (r : Fin 7 → ℝ) : Matrix (Fin 4) (Fin 7) ℝ :=
  Matrix.of ![b1, b2, fun j => 2 * b3 j, r]

@[simp] lemma mkMat_zero (r : Fin 7 → ℝ) (j : Fin 7) : mkMat r 0 j = b1 j := rfl

@[simp] lemma mkMat_one (r : Fin 7 → ℝ) (j : Fin 7) : mkMat r 1 j = b2 j := rfl

@[simp] lemma mkMat_two (r : Fin 7 → ℝ) (j : Fin 7) : mkMat r 2 j = 2 * b3 j := rfl

@[simp] lemma mkMat_three (r : Fin 7 → ℝ) (j : Fin 7) : mkMat r 3 j = r j := rfl

/-- The base state: rows `b1`, `b2`, `2 b3`, `b3`, three distinct discrete Maxwellians, so
`rank M₀ = 3` (`rank_M₀`). -/
noncomputable def M₀ : Matrix (Fin 4) (Fin 7) ℝ := mkMat b3

theorem isDiscreteMaxwellian_mkMat (ε : ℝ) : IsDiscreteMaxwellian vel (mkMat (yv ε)) := by
  refine ⟨![0, 0, Real.log 2, 0], ![5 * Real.log 2, -(5 * Real.log 2), 0, ε],
    fun _ => -Real.log 2, fun _ => neg_lt_zero.2 log_two_pos', fun i j => ?_⟩
  fin_cases i
  · exact b1_eq j
  · exact b2_eq j
  · exact two_b3_eq j
  · rfl

/-- `M₀` is a matrix of discrete Maxwellians. -/
theorem isDiscreteMaxwellian_M₀ : IsDiscreteMaxwellian vel M₀ := by
  have := isDiscreteMaxwellian_mkMat 0
  rwa [yv_zero] at this

/-- Right inverse of the rows `b1`, `b2`, `2 b3`. -/
noncomputable def Hm : Matrix (Fin 7) (Fin 3) ℝ :=
  !![0, 0, 0; 0, 0, 0; 64 / 31713, 2048 / 31713, -32 / 961; -32 / 961, -32 / 961, 1025 / 1922;
    2048 / 31713, 64 / 31713, -32 / 961; 0, 0, 0; 0, 0, 0]

lemma b1_Hm (c : Fin 3 → ℝ) : b1 ⬝ᵥ (Hm *ᵥ c) = c 0 := by
  simp only [dotProduct, Fin.sum_univ_seven, Hm, mulVec, Fin.sum_univ_three, b1]
  simp
  ring

lemma b2_Hm (c : Fin 3 → ℝ) : b2 ⬝ᵥ (Hm *ᵥ c) = c 1 := by
  simp only [dotProduct, Fin.sum_univ_seven, Hm, mulVec, Fin.sum_univ_three, b2]
  simp
  ring

lemma b3_Hm (c : Fin 3 → ℝ) : b3 ⬝ᵥ (Hm *ᵥ c) = c 2 / 2 := by
  simp only [dotProduct, Fin.sum_univ_seven, Hm, mulVec, Fin.sum_univ_three, b3]
  simp
  ring

lemma Ty_dot (y z : Fin 7 → ℝ) :
    Ty y ⬝ᵥ z = (k1 ⬝ᵥ y) * (b1 ⬝ᵥ z) + (k2 ⬝ᵥ y) * (b2 ⬝ᵥ z) + (k3 ⬝ᵥ y) * (b3 ⬝ᵥ z) := by
  have : Ty y = (k1 ⬝ᵥ y) • b1 + (k2 ⬝ᵥ y) • b2 + (k3 ⬝ᵥ y) • b3 := by
    funext j
    simp [Ty]
  rw [this, add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, smul_dotProduct]
  simp only [smul_eq_mul]

/-- The normal vector of the column space of the matrix with last row `Ty y`. -/
noncomputable def uvec (y : Fin 7 → ℝ) : Fin 4 → ℝ := ![k1 ⬝ᵥ y, k2 ⬝ᵥ y, (k3 ⬝ᵥ y) / 2, -1]

lemma uvec_ne_zero (y : Fin 7 → ℝ) : uvec y ≠ 0 := fun h => by
  have := congrFun h 3
  simp [uvec] at this

lemma two_b3_dot (z : Fin 7 → ℝ) : (fun j => 2 * b3 j) ⬝ᵥ z = 2 * (b3 ⬝ᵥ z) := by
  simp only [dotProduct, Finset.mul_sum, mul_assoc]

lemma uvec_dot (y : Fin 7 → ℝ) (x : Fin 4 → ℝ) :
    uvec y ⬝ᵥ x = (k1 ⬝ᵥ y) * x 0 + (k2 ⬝ᵥ y) * x 1 + (k3 ⬝ᵥ y) / 2 * x 2 - x 3 := by
  simp only [dotProduct, Fin.sum_univ_four, uvec]
  simp
  ring

/-- The column space of the rank-three state is the hyperplane `(uvec y)^⊥`. -/
theorem colSpace_eq (y : Fin 7 → ℝ) : colSpace (mkMat (Ty y)) = hyperplane (uvec y) := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    rw [mem_hyperplane, uvec_dot]
    have h0 : (mkMat (Ty y)).mulVecLin z 0 = b1 ⬝ᵥ z := rfl
    have h1 : (mkMat (Ty y)).mulVecLin z 1 = b2 ⬝ᵥ z := rfl
    have h2 : (mkMat (Ty y)).mulVecLin z 2 = 2 * (b3 ⬝ᵥ z) := two_b3_dot z
    have h3 : (mkMat (Ty y)).mulVecLin z 3 = Ty y ⬝ᵥ z := rfl
    rw [h0, h1, h2, h3, Ty_dot]
    ring
  · intro x hx
    rw [mem_hyperplane, uvec_dot] at hx
    refine ⟨Hm *ᵥ ![x 0, x 1, x 2], ?_⟩
    funext i
    have h2 : (2 * b3 ⬝ᵥ (Hm *ᵥ ![x 0, x 1, x 2])) = x 2 := by
      rw [b3_Hm]
      change 2 * (x 2 / 2) = x 2
      ring
    fin_cases i
    · exact (b1_Hm _).trans (by simp)
    · exact (b2_Hm _).trans (by simp)
    · exact (two_b3_dot _).trans h2
    · change Ty y ⬝ᵥ (Hm *ᵥ ![x 0, x 1, x 2]) = x 3
      rw [Ty_dot, b1_Hm, b2_Hm, b3_Hm]
      simp
      linarith

/-- The first factor of the rank factorization. -/
noncomputable def Am (y : Fin 7 → ℝ) : Matrix (Fin 4) (Fin 3) ℝ :=
  !![1, 0, 0; 0, 1, 0; 0, 0, 2; k1 ⬝ᵥ y, k2 ⬝ᵥ y, k3 ⬝ᵥ y]

/-- The second factor of the rank factorization. -/
noncomputable def Bm : Matrix (Fin 3) (Fin 7) ℝ := Matrix.of ![b1, b2, b3]

lemma mkMat_factor (y : Fin 7 → ℝ) : mkMat (Ty y) = Am y * Bm := by
  ext i j
  fin_cases i <;> simp [Am, Bm, Matrix.mul_apply, Fin.sum_univ_three, Ty]

/-- Left inverse of the first three rows. -/
def Gm : Matrix (Fin 3) (Fin 4) ℝ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0]

lemma Gm_mkMat_Hm (r : Fin 7 → ℝ) : Gm * mkMat r * Hm = 1 := by
  ext i l
  fin_cases i <;> fin_cases l <;>
  · simp only [Matrix.mul_apply, Fin.sum_univ_seven, Fin.sum_univ_four, Gm, Hm]
    norm_num [b1, b2, b3]

/-- The state with last row `Ty y` has rank three. -/
theorem rank_mkMat (y : Fin 7 → ℝ) : (mkMat (Ty y)).rank = 3 := by
  apply le_antisymm
  · rw [mkMat_factor]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)
  · have h := Matrix.rank_one (R := ℝ) (n := Fin 3)
    rw [← Gm_mkMat_Hm (Ty y)] at h
    simp only [Fintype.card_fin] at h
    rw [← h]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- The base state has rank three. -/
theorem rank_M₀ : M₀.rank = 3 := by
  have := rank_mkMat b3
  rwa [Ty_b3] at this

/-- The coefficient of `b1` in `decomp_of_dot_w`. -/
noncomputable def d0 : Fin 7 → ℝ :=
  ![0, 1803894784 / 1663313519637, -28465135616 / 4989940558911, 538443776 / 23875313679,
    -73643425792 / 1663313519637, 191058427904 / 4989940558911, -285212672 / 23875313679]

/-- The coefficient of `b2` in `decomp_of_dot_w`. -/
noncomputable def d1 : Fin 7 → ℝ :=
  ![0, 161195491328 / 4989940558911, -113344249856 / 1663313519637, 538443776 / 23875313679,
    90637336576 / 4989940558911, 11758206976 / 1663313519637, -285212672 / 23875313679]

/-- The coefficient of `2 b3` in `decomp_of_dot_w`. -/
noncomputable def d2 : Fin 7 → ℝ :=
  ![0, 55605248 / 294756959, -247007864 / 294756959, 397553512 / 294756959,
    -266665832 / 294756959, 50676344 / 294756959, 9838592 / 294756959]

/-- The coefficient of `1` in `decomp_of_dot_w`. -/
noncomputable def d3 : Fin 7 → ℝ :=
  ![0, -10203136 / 24844239, 43473904 / 24844239, -43293697 / 24844239, 45601744 / 24844239,
    -9669616 / 24844239, -1064960 / 24844239]

/-- The coefficient of `v` in `decomp_of_dot_w`. -/
noncomputable def d4 : Fin 7 → ℝ := ![0, 128 / 513, -1025 / 1026, 0, 1025 / 1026, -128 / 513, 0]

/-- The coefficient of `v²` in `decomp_of_dot_w`. -/
noncomputable def d5 : Fin 7 → ℝ :=
  ![0, -53632 / 1183059, 424739 / 2366118, 38645 / 1183059, -524605 / 2366118,
    -172648 / 1183059, 237568 / 1183059]

/-- Every vector orthogonal to `w` is a combination of `b1`, `b2`, `2 b3`, `1`, `v`, `v²`. -/
lemma decomp_of_dot_w {z : Fin 7 → ℝ} (hz : w ⬝ᵥ z = 0) (j : Fin 7) :
    z j = (d0 ⬝ᵥ z) * b1 j + (d1 ⬝ᵥ z) * b2 j + (d2 ⬝ᵥ z) * (2 * b3 j) + (d3 ⬝ᵥ z) * 1
      + (d4 ⬝ᵥ z) * vel j + (d5 ⬝ᵥ z) * vel j ^ 2 := by
  simp only [dotProduct, Fin.sum_univ_seven, w, d0, d1, d2, d3, d4, d5, Matrix.cons_val,
    Fin.isValue] at hz ⊢
  fin_cases j
  · simp only [b1, b2, b3, vel, Fin.zero_eta, Fin.isValue, Matrix.cons_val]
    linear_combination (-1 / 1024) * hz
  all_goals
    simp [b1, b2, b3, vel]
    ring

lemma w_dot_b1 : w ⬝ᵥ b1 = 0 := by
  simp only [dotProduct, Fin.sum_univ_seven, w, b1]
  norm_num

lemma w_dot_b2 : w ⬝ᵥ b2 = 0 := by
  simp only [dotProduct, Fin.sum_univ_seven, w, b2]
  norm_num

lemma w_dot_b3 : w ⬝ᵥ b3 = 0 := by
  simp only [dotProduct, Fin.sum_univ_seven, w, b3]
  norm_num

lemma w_dot_collInv (k : Fin 3) : w ⬝ᵥ collInv vel k = 0 := by
  fin_cases k <;> norm_num [dotProduct, Fin.sum_univ_seven, w, collInv, vel]

lemma w_dot_Ty (y : Fin 7 → ℝ) : w ⬝ᵥ Ty y = 0 := by
  rw [dotProduct_comm, Ty_dot, dotProduct_comm b1, dotProduct_comm b2, dotProduct_comm b3,
    w_dot_b1, w_dot_b2, w_dot_b3]
  ring

/-- The augmented velocity space is the hyperplane `w^⊥`. -/
theorem augSpace_eq (y : Fin 7 → ℝ) : augSpace vel (mkMat (Ty y)) = hyperplane w := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ (⟨i, rfl⟩ | ⟨k, rfl⟩)
    · fin_cases i
      · exact w_dot_b1
      · exact w_dot_b2
      · change w ⬝ᵥ (fun j => 2 * b3 j) = 0
        rw [dotProduct_comm, two_b3_dot, dotProduct_comm, w_dot_b3, mul_zero]
      · exact w_dot_Ty y
    · exact w_dot_collInv k
  · intro z hz
    rw [mem_hyperplane] at hz
    have hrow : ∀ i, mkMat (Ty y) i ∈ augSpace vel (mkMat (Ty y)) := fun i =>
      Submodule.subset_span (Or.inl ⟨i, rfl⟩)
    have hcoll : ∀ k, collInv vel k ∈ augSpace vel (mkMat (Ty y)) := fun k =>
      Submodule.subset_span (Or.inr ⟨k, rfl⟩)
    have hz' : z = (d0 ⬝ᵥ z) • mkMat (Ty y) 0 + (d1 ⬝ᵥ z) • mkMat (Ty y) 1
        + (d2 ⬝ᵥ z) • mkMat (Ty y) 2 + (d3 ⬝ᵥ z) • collInv vel 0
        + (d4 ⬝ᵥ z) • collInv vel 1 + (d5 ⬝ᵥ z) • collInv vel 2 := by
      funext j
      simpa [collInv] using decomp_of_dot_w hz j
    rw [hz']
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.add_mem _ (Submodule.smul_mem _ _ (hrow 0)) (Submodule.smul_mem _ _ (hrow 1)))
      (Submodule.smul_mem _ _ (hrow 2))) (Submodule.smul_mem _ _ (hcoll 0)))
      (Submodule.smul_mem _ _ (hcoll 1))) (Submodule.smul_mem _ _ (hcoll 2))


/-! ### The entropy rate along the family -/

/-- The defect `M[f] - f` in the last row. -/
noncomputable def Fe (ε : ℝ) (j : Fin 7) : ℝ := yv ε j - Ty (yv ε) j

/-- The log-ratio `log (f / M[f])` in the last row. -/
noncomputable def Le (ε : ℝ) (j : Fin 7) : ℝ := Real.log (Ty (yv ε) j) - Real.log (yv ε j)

/-- The normalisation of the rank-one normal direction. -/
noncomputable def alphaE (ε : ℝ) : ℝ := (uvec (yv ε) ⬝ᵥ uvec (yv ε))⁻¹ * (w ⬝ᵥ w)⁻¹

lemma poly_dot_w (a b c : ℝ) : ∑ j, (a + b * vel j + c * vel j ^ 2) * w j = 0 := by
  simp only [Fin.sum_univ_seven, vel, w]
  simp
  ring

lemma Fe_moment (ε a b c : ℝ) : ∑ j, Fe ε j * (a + b * vel j + c * vel j ^ 2) = 0 := by
  have h0 := Ty_moment (yv ε) 0
  have h1 := Ty_moment (yv ε) 1
  have h2 := Ty_moment (yv ε) 2
  simp only [dotProduct, collInv, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one,
    mul_one] at h0 h1 h2
  have e : ∀ j, Fe ε j * (a + b * vel j + c * vel j ^ 2)
      = a * (yv ε j - Ty (yv ε) j) + b * (yv ε j * vel j - Ty (yv ε) j * vel j)
        + c * (yv ε j * vel j ^ 2 - Ty (yv ε) j * vel j ^ 2) := fun j => by
    simp only [Fe]
    ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, h0, h1, h2,
    sub_self, mul_zero, add_zero]

lemma log_yv (ε : ℝ) (j : Fin 7) :
    Real.log (yv ε j) + 1 = 1 + ε * vel j + -Real.log 2 * vel j ^ 2 := by
  rw [yv, Real.log_exp]
  ring

lemma mkMat_sub_apply_zero (r r' : Fin 7 → ℝ) (j : Fin 7) : (mkMat r - mkMat r') 0 j = 0 := by
  simp

lemma mkMat_sub_apply_one (r r' : Fin 7 → ℝ) (j : Fin 7) : (mkMat r - mkMat r') 1 j = 0 := by
  simp

lemma mkMat_sub_apply_two (r r' : Fin 7 → ℝ) (j : Fin 7) : (mkMat r - mkMat r') 2 j = 0 := by
  simp

lemma mkMat_sub_apply_three (r r' : Fin 7 → ℝ) (j : Fin 7) :
    (mkMat r - mkMat r') 3 j = r j - r' j := by
  simp

/-- The entropy rate of the full BGK operator along the family. -/
lemma entropyRate_full (ε : ℝ) :
    entropyRate (mkMat (Ty (yv ε))) (mkMat (yv ε) - mkMat (Ty (yv ε)))
      = ∑ j, Fe ε j * Le ε j := by
  simp only [entropyRate, Fin.sum_univ_four, mkMat_sub_apply_zero, mkMat_sub_apply_one,
    mkMat_sub_apply_two, mkMat_sub_apply_three, zero_mul, Finset.sum_const_zero, zero_add]
  have e : ∀ j, (yv ε j - Ty (yv ε) j) * (Real.log (mkMat (Ty (yv ε)) 3 j) + 1)
      = Fe ε j * Le ε j + Fe ε j * (1 + ε * vel j + -Real.log 2 * vel j ^ 2) := fun j => by
    rw [← log_yv, mkMat_three, Fe, Le]
    ring
  simp only [e, Finset.sum_add_distrib, Fe_moment, add_zero]

lemma uvec_Z_w (ε : ℝ) :
    uvec (yv ε) ⬝ᵥ (mkMat (yv ε) - mkMat (Ty (yv ε))) *ᵥ w = -∑ j, Fe ε j * w j := by
  rw [uvec_dot]
  simp only [mulVec, dotProduct, mkMat_sub_apply_zero, mkMat_sub_apply_one,
    mkMat_sub_apply_two, mkMat_sub_apply_three, zero_mul, Finset.sum_const_zero, mul_zero,
    add_zero, zero_sub, Fe]

lemma uvec_L_w (ε : ℝ) :
    uvec (yv ε) ⬝ᵥ logOne (mkMat (Ty (yv ε))) *ᵥ w = -∑ j, Le ε j * w j := by
  rw [uvec_dot]
  have h0 : (logOne (mkMat (Ty (yv ε))) *ᵥ w) 0 = 0 := by
    have e : ∀ j, (Real.log (b1 j) + 1) * w j
        = (1 + 5 * Real.log 2 * vel j + -Real.log 2 * vel j ^ 2) * w j := fun j => by
      rw [b1_eq, Real.log_exp]
      ring
    simpa only [mulVec, dotProduct, logOne, Matrix.of_apply, mkMat_zero, mul_comm (w _) _, e]
      using poly_dot_w 1 (5 * Real.log 2) (-Real.log 2)
  have h1 : (logOne (mkMat (Ty (yv ε))) *ᵥ w) 1 = 0 := by
    have e : ∀ j, (Real.log (b2 j) + 1) * w j
        = (1 + -(5 * Real.log 2) * vel j + -Real.log 2 * vel j ^ 2) * w j := fun j => by
      rw [b2_eq, Real.log_exp]
      ring
    simpa only [mulVec, dotProduct, logOne, Matrix.of_apply, mkMat_one, mul_comm (w _) _, e]
      using poly_dot_w 1 (-(5 * Real.log 2)) (-Real.log 2)
  have h2 : (logOne (mkMat (Ty (yv ε))) *ᵥ w) 2 = 0 := by
    have e : ∀ j, (Real.log (2 * b3 j) + 1) * w j
        = ((1 + Real.log 2) + 0 * vel j + -Real.log 2 * vel j ^ 2) * w j := fun j => by
      rw [two_b3_eq, Real.log_exp]
      ring
    simpa only [mulVec, dotProduct, logOne, Matrix.of_apply, mkMat_two, mul_comm (w _) _, e]
      using poly_dot_w (1 + Real.log 2) 0 (-Real.log 2)
  have h3 : (logOne (mkMat (Ty (yv ε))) *ᵥ w) 3 = ∑ j, Le ε j * w j := by
    have e : ∀ j, (Real.log (Ty (yv ε) j) + 1) * w j
        = Le ε j * w j + (1 + ε * vel j + -Real.log 2 * vel j ^ 2) * w j := fun j => by
      rw [← log_yv, Le]
      ring
    simp only [mulVec, dotProduct, logOne, Matrix.of_apply, mkMat_three, e,
      Finset.sum_add_distrib, poly_dot_w, add_zero]
  rw [h0, h1, h2, h3]
  ring

/-- The entropy rate of the conservative DLRA field along the family. -/
lemma entropyRate_dlra (ε : ℝ) :
    entropyRate (mkMat (Ty (yv ε))) (dlraField (hyperProj (uvec (yv ε))) (hyperProj w)
        (mkMat (yv ε) - mkMat (Ty (yv ε))))
      = ∑ j, Fe ε j * Le ε j - alphaE ε * (∑ j, Fe ε j * w j) * ∑ j, Le ε j * w j := by
  rw [entropyRate_dlraField_hyperProj, entropyRate_full, uvec_Z_w, uvec_L_w, alphaE]
  ring

/-! ### The limit `ε → 0` -/

/-- The derivative of the last Maxwellian at `ε = 0`. -/
noncomputable def hv (j : Fin 7) : ℝ := b3 j * vel j

/-- The derivative of the defect `M[f] - f` at `ε = 0`. -/
noncomputable def Fp : Fin 7 → ℝ :=
  ![3093459 / 22040588, 935053 / 44081176, -5107715 / 11020294, 0, 5107715 / 11020294,
    -935053 / 44081176, -3093459 / 22040588]

/-- The derivative of the log-ratio at `ε = 0`. -/
noncomputable def Lp (j : Fin 7) : ℝ := -Fp j / b3 j

lemma hasDerivAt_yv (j : Fin 7) : HasDerivAt (fun ε => yv ε j) (hv j) 0 := by
  have h : HasDerivAt (fun ε : ℝ => 0 + ε * vel j + -Real.log 2 * vel j ^ 2) (vel j) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const (vel j)).const_add 0).add_const
      (-Real.log 2 * vel j ^ 2)
  have := h.exp
  rw [hv, b3_eq]
  exact this

lemma hasDerivAt_dot (κ : Fin 7 → ℝ) : HasDerivAt (fun ε => κ ⬝ᵥ yv ε) (κ ⬝ᵥ hv) 0 := by
  simp only [dotProduct]
  exact HasDerivAt.fun_sum fun j _ => (hasDerivAt_yv j).const_mul (κ j)

lemma hasDerivAt_Ty (j : Fin 7) : HasDerivAt (fun ε => Ty (yv ε) j) (Ty hv j) 0 := by
  simp only [Ty]
  exact (((hasDerivAt_dot k1).mul_const _).add ((hasDerivAt_dot k2).mul_const _)).add
    ((hasDerivAt_dot k3).mul_const _)

lemma k1_hv : k1 ⬝ᵥ hv = 4292608 / 1878960127 := by
  simp only [dotProduct, Fin.sum_univ_seven, k1, hv, b3, vel]
  norm_num

lemma k2_hv : k2 ⬝ᵥ hv = -4292608 / 1878960127 := by
  simp only [dotProduct, Fin.sum_univ_seven, k2, hv, b3, vel]
  norm_num

lemma k3_hv : k3 ⬝ᵥ hv = 0 := by
  simp only [dotProduct, Fin.sum_univ_seven, k3, hv, b3, vel]
  norm_num

lemma hv_sub_Ty (j : Fin 7) : hv j - Ty hv j = Fp j := by
  simp only [Ty, k1_hv, k2_hv, k3_hv]
  fin_cases j <;> norm_num [hv, Fp, b1, b2, b3, vel]

lemma hasDerivAt_Fe (j : Fin 7) : HasDerivAt (fun ε => Fe ε j) (Fp j) 0 := by
  rw [← hv_sub_Ty]
  exact (hasDerivAt_yv j).sub (hasDerivAt_Ty j)

lemma Ty_yv_zero (j : Fin 7) : Ty (yv 0) j = b3 j := by rw [yv_zero, Ty_b3]

lemma hasDerivAt_Le (j : Fin 7) : HasDerivAt (fun ε => Le ε j) (Lp j) 0 := by
  have hne := (b3_pos j).ne'
  have h1 := (hasDerivAt_Ty j).log (by rw [Ty_yv_zero]; exact hne)
  have h2 := (hasDerivAt_yv j).log (yv_pos 0 j).ne'
  have h := h1.sub h2
  have e : Ty hv j / Ty (yv 0) j - hv j / yv 0 j = Lp j := by
    rw [Ty_yv_zero, yv_zero, Lp, ← hv_sub_Ty]
    field_simp
    ring
  rw [e] at h
  exact h

lemma Fe_zero (j : Fin 7) : Fe 0 j = 0 := by
  rw [Fe, Ty_yv_zero, yv_zero, sub_self]

lemma Le_zero (j : Fin 7) : Le 0 j = 0 := by
  rw [Le, Ty_yv_zero, yv_zero, sub_self]

private lemma tendsto_div_of_hasDerivAt {g : ℝ → ℝ} {g' : ℝ} (hg : HasDerivAt g g' 0)
    (h0 : g 0 = 0) : Tendsto (fun ε => g ε / ε) (𝓝[≠] 0) (𝓝 g') :=
  (hasDerivAt_iff_tendsto_slope.1 hg).congr fun ε => by
    rw [slope_def_field, h0, sub_zero, sub_zero]

lemma uvec_self (y : Fin 7 → ℝ) :
    uvec y ⬝ᵥ uvec y = (k1 ⬝ᵥ y) ^ 2 + (k2 ⬝ᵥ y) ^ 2 + (k3 ⬝ᵥ y) ^ 2 / 4 + 1 := by
  rw [uvec_dot]
  simp only [uvec]
  simp
  ring

lemma k1_yv_zero : k1 ⬝ᵥ yv 0 = 0 := by
  rw [yv_zero]
  simp only [dotProduct, Fin.sum_univ_seven, k1, b3]
  norm_num

lemma k2_yv_zero : k2 ⬝ᵥ yv 0 = 0 := by
  rw [yv_zero]
  simp only [dotProduct, Fin.sum_univ_seven, k2, b3]
  norm_num

lemma k3_yv_zero : k3 ⬝ᵥ yv 0 = 1 := by
  rw [yv_zero]
  simp only [dotProduct, Fin.sum_univ_seven, k3, b3]
  norm_num

/-- The limit of the normalisation: `‖u‖² → 5/4`, the row weights of the two parallel rows. -/
lemma tendsto_alphaE : Tendsto alphaE (𝓝[≠] 0) (𝓝 ((5 / 4 : ℝ)⁻¹ * (w ⬝ᵥ w)⁻¹)) := by
  have h1 := (hasDerivAt_dot k1).continuousAt
  have h2 := (hasDerivAt_dot k2).continuousAt
  have h3 := (hasDerivAt_dot k3).continuousAt
  have h : ContinuousAt (fun ε => (k1 ⬝ᵥ yv ε) ^ 2 + (k2 ⬝ᵥ yv ε) ^ 2 + (k3 ⬝ᵥ yv ε) ^ 2 / 4 + 1)
      0 := ((h1.pow 2).add (h2.pow 2)).add ((h3.pow 2).div_const 4) |>.add continuousAt_const
  have ht := h.tendsto
  simp only [k1_yv_zero, k2_yv_zero, k3_yv_zero] at ht
  have e : ((0 : ℝ) ^ 2 + 0 ^ 2 + 1 ^ 2 / 4 + 1) = 5 / 4 := by norm_num
  rw [e] at ht
  have hi := (ht.inv₀ (by norm_num)).mul_const (w ⬝ᵥ w)⁻¹
  refine (hi.mono_left nhdsWithin_le_nhds).congr fun ε => ?_
  rw [alphaE, uvec_self]

/-- The rate of the full BGK operator is `-ε² Σ F'² / b3 + o(ε²)`. -/
theorem tendsto_rate_full :
    Tendsto (fun ε => (∑ j, Fe ε j * Le ε j) / ε ^ 2) (𝓝[≠] 0) (𝓝 (∑ j, Fp j * Lp j)) := by
  have hF := fun j => tendsto_div_of_hasDerivAt (hasDerivAt_Fe j) (Fe_zero j)
  have hL := fun j => tendsto_div_of_hasDerivAt (hasDerivAt_Le j) (Le_zero j)
  have h := tendsto_finsetSum Finset.univ fun j _ => (hF j).mul (hL j)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : ε ≠ 0)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  field_simp

/-- The rate of the conservative DLRA is `ε² (…) + o(ε²)`. -/
theorem tendsto_rate_dlra :
    Tendsto (fun ε => (∑ j, Fe ε j * Le ε j
        - alphaE ε * (∑ j, Fe ε j * w j) * ∑ j, Le ε j * w j) / ε ^ 2) (𝓝[≠] 0)
      (𝓝 (∑ j, Fp j * Lp j
        - (5 / 4 : ℝ)⁻¹ * (w ⬝ᵥ w)⁻¹ * (∑ j, Fp j * w j) * ∑ j, Lp j * w j)) := by
  have hF := fun j => tendsto_div_of_hasDerivAt (hasDerivAt_Fe j) (Fe_zero j)
  have hL := fun j => tendsto_div_of_hasDerivAt (hasDerivAt_Le j) (Le_zero j)
  have h1 := tendsto_finsetSum Finset.univ fun j _ => (hF j).mul_const (w j)
  have h2 := tendsto_finsetSum Finset.univ fun j _ => (hL j).mul_const (w j)
  have h := tendsto_rate_full.sub ((tendsto_alphaE.mul h1).mul h2)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : ε ≠ 0)
  have e1 : ∑ j, Fe ε j / ε * w j = (∑ j, Fe ε j * w j) / ε := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∑ j, Le ε j / ε * w j = (∑ j, Le ε j * w j) / ε := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2]
  field_simp

/-- The exact value of the limit of the full rate. -/
lemma limit_full : ∑ j, Fp j * Lp j = -1277946367994427 / 60723439923218 := by
  simp only [Fin.sum_univ_seven, Lp, Fp, b3]
  norm_num

lemma w_dot_self : w ⬝ᵥ w = 10995722 := by
  simp only [dotProduct, Fin.sum_univ_seven, w]
  norm_num

/-- The exact value of the limit of the conservative DLRA rate: it is positive. -/
lemma limit_dlra :
    ∑ j, Fp j * Lp j - (5 / 4 : ℝ)⁻¹ * (w ⬝ᵥ w)⁻¹ * (∑ j, Fp j * w j) * ∑ j, Lp j * w j
      = 884311876314530067225 / 333849032139703236698 := by
  rw [limit_full, w_dot_self]
  simp only [Fin.sum_univ_seven, Lp, Fp, b3, w]
  norm_num


/-! ### The theorem -/

lemma mkMat_pos {r : Fin 7 → ℝ} (hr : ∀ j, 0 < r j) (i : Fin 4) (j : Fin 7) : 0 < mkMat r i j := by
  fin_cases i
  · exact b1_pos j
  · exact b2_pos j
  · exact mul_pos two_pos (b3_pos j)
  · exact hr j

/-- `f = mkMat (Ty (yv ε))` and its Maxwellian: the moments of the two matrices agree. -/
theorem isMaxwellianOf_family (ε : ℝ) :
    IsMaxwellianOf vel (mkMat (Ty (yv ε))) (mkMat (yv ε)) := by
  refine ⟨isDiscreteMaxwellian_mkMat ε, fun i k => ?_⟩
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact Ty_moment (yv ε) k

/-- The orthogonal projectors of the conservative DLRA at the state of the family. -/
theorem isOrthProjOnto_family (ε : ℝ) :
    IsOrthProjOnto (hyperProj (uvec (yv ε))) (colSpace (mkMat (Ty (yv ε)))) ∧
      IsOrthProjOnto (hyperProj w) (augSpace vel (mkMat (Ty (yv ε)))) := by
  have hw : w ≠ 0 := fun h => by
    have := w_dot_self
    rw [h] at this
    simp at this
  rw [colSpace_eq, augSpace_eq]
  exact ⟨isOrthProjOnto_hyperProj (uvec_ne_zero _), isOrthProjOnto_hyperProj hw⟩

lemma eventually_pos : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), ∀ j, 0 < Ty (yv ε) j := by
  refine eventually_all.2 fun j => ?_
  have h : Tendsto (fun ε => Ty (yv ε) j) (𝓝[≠] 0) (𝓝 (b3 j)) := by
    have := (hasDerivAt_Ty j).continuousAt.tendsto
    rw [Ty_yv_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact h.eventually (lt_mem_nhds (b3_pos j))

lemma eventually_near {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ε in 𝓝[≠] (0 : ℝ), ∀ j,
      |Ty (yv ε) j - b3 j| ≤ δ * b3 j ∧ |yv ε j - b3 j| ≤ δ * b3 j := by
  refine eventually_all.2 fun j => ?_
  have hb := mul_pos hδ (b3_pos j)
  have h1 : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), |Ty (yv ε) j - b3 j| < δ * b3 j := by
    have h := (hasDerivAt_Ty j).continuousAt.tendsto
    rw [Ty_yv_zero] at h
    have h' := ((h.sub_const (b3 j)).abs).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    rw [sub_self, abs_zero] at h'
    exact h'.eventually (gt_mem_nhds hb)
  have h2 : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), |yv ε j - b3 j| < δ * b3 j := by
    have h := (hasDerivAt_yv j).continuousAt.tendsto
    rw [yv_zero] at h
    have h' := ((h.sub_const (b3 j)).abs).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    rw [sub_self, abs_zero] at h'
    exact h'.eventually (gt_mem_nhds hb)
  filter_upwards [h1, h2] with ε h1 h2
  exact ⟨h1.le, h2.le⟩

lemma eventually_rate :
    ∀ᶠ ε in 𝓝[≠] (0 : ℝ),
      (∑ j, Fe ε j * Le ε j) < 0 ∧
      0 < ∑ j, Fe ε j * Le ε j - alphaE ε * (∑ j, Fe ε j * w j) * ∑ j, Le ε j * w j := by
  have h1 : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), (∑ j, Fe ε j * Le ε j) / ε ^ 2 < 0 := by
    refine tendsto_rate_full.eventually (gt_mem_nhds ?_)
    rw [limit_full]
    norm_num
  have h2 : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), 0 < (∑ j, Fe ε j * Le ε j
      - alphaE ε * (∑ j, Fe ε j * w j) * ∑ j, Le ε j * w j) / ε ^ 2 := by
    refine tendsto_rate_dlra.eventually (lt_mem_nhds ?_)
    rw [limit_dlra]
    norm_num
  filter_upwards [h1, h2, self_mem_nhdsWithin] with ε h1 h2 (hε : ε ≠ 0)
  have hsq : 0 < ε ^ 2 := by positivity
  refine ⟨?_, (div_pos_iff_of_pos_right hsq).1 h2⟩
  have := mul_neg_of_neg_of_pos h1 hsq
  rwa [div_mul_cancel₀ _ hsq.ne'] at this


/-- The rank-three states of the family. -/
noncomputable def fState (ε : ℝ) : Matrix (Fin 4) (Fin 7) ℝ := mkMat (Ty (yv ε))

/-- The Maxwellians of the family, `M[fState ε] = MState ε` by `isMaxwellianOf_family`. -/
noncomputable def MState (ε : ℝ) : Matrix (Fin 4) (Fin 7) ℝ := mkMat (yv ε)

/-- The family starts at the rank-three Maxwellian `M₀`. -/
theorem fState_zero : fState 0 = M₀ := by
  rw [fState, yv_zero, Ty_b3, M₀]

/-- **Exact entropy rates along the family.**  At `f = fState ε`, `M = MState ε = M[f]`, with `P`
the `L²`-orthogonal projector with column space `col f` and velocity space
`span (rows of f, 1, v, v²)`, as `ε → 0`:

  `⟪M - f, log f + 1⟫ / ε² → -1277946367994427/60723439923218 ≈ -21.05`,
  `⟪P (M - f), log f + 1⟫ / ε² → 884311876314530067225/333849032139703236698 ≈ +2.65`.

The H-theorem of the full model (`discrete_H_theorem` of OP-SB-52) keeps its sign; the projection
reverses it at the leading order.  The limits are exact rationals. -/
theorem tendsto_entropyRates :
    Tendsto (fun ε => entropyRate (fState ε) (MState ε - fState ε) / ε ^ 2) (𝓝[≠] 0)
        (𝓝 (-1277946367994427 / 60723439923218)) ∧
      Tendsto (fun ε => entropyRate (fState ε) (dlraField (hyperProj (uvec (yv ε))) (hyperProj w)
          (MState ε - fState ε)) / ε ^ 2) (𝓝[≠] 0)
        (𝓝 (884311876314530067225 / 333849032139703236698)) := by
  constructor
  · rw [← limit_full]
    simpa only [fState, MState, entropyRate_full] using tendsto_rate_full
  · rw [← limit_dlra]
    simpa only [fState, MState, entropyRate_dlra] using tendsto_rate_dlra

/-- **The conservative `L²`-orthogonal DLRA of BGK violates the H-theorem arbitrarily close to a
rank-three Maxwellian** (OP-SB-52; this formalises the numerical counterexample
quoted in `NovelOpSB52`, on a smaller grid).  In the discretisation with four cells and the seven
velocities `-3, …, 3`, for every `δ > 0` there is a positive state `f` of rank exactly three whose
entries are within relative distance `δ` of those of the rank-three Maxwellian `M₀`, with
Maxwellian `M = M[f]` (equally close), such that, with `PU`, `PV` the orthogonal projectors onto the
column space of `f` and onto `span (rows of f, 1, v, v²)`,

* the full BGK flow dissipates, `⟪M - f, log f + 1⟫ < 0`;
* the projected field `ḟ = PU F + F PV - PU F PV`, `F = M - f`, conserves mass, momentum and energy
  in every cell;
* the projected field *produces* `H`: `⟪PU F + F PV - PU F PV, log f + 1⟫ > 0`, so that `Σ f log f`
  increases along every curve with this velocity (`entropy_lt_of_entropyRate_pos`), in particular
  under every small enough explicit Euler step.

Basis augmentation repairs the conservation laws but not the H-theorem.  This is a statement about
this discretisation (`m = 4`, `n = 7`, `r = 3`), not about all grids.  The log-DLRA with the
entropy-Hessian projector of OP-SB-52 (`logDLRA_BGK_entropy_antitone`) is the positive
counterpart. -/
theorem exists_entropy_increase_near_maxwellian {δ : ℝ} (hδ : 0 < δ) :
    ∃ (f M : Matrix (Fin 4) (Fin 7) ℝ) (PU : Matrix (Fin 4) (Fin 4) ℝ)
      (PV : Matrix (Fin 7) (Fin 7) ℝ),
      (∀ i j, 0 < f i j) ∧ f.rank = 3 ∧
      (∀ i j, |f i j - M₀ i j| ≤ δ * M₀ i j) ∧ (∀ i j, |M i j - M₀ i j| ≤ δ * M₀ i j) ∧
      IsMaxwellianOf vel f M ∧
      IsOrthProjOnto PU (colSpace f) ∧ IsOrthProjOnto PV (augSpace vel f) ∧
      (∀ i k, dlraField PU PV (M - f) i ⬝ᵥ collInv vel k = 0) ∧
      entropyRate f (M - f) < 0 ∧
      0 < entropyRate f (dlraField PU PV (M - f)) ∧
      ∀ᶠ h in 𝓝[>] (0 : ℝ), entropy f < entropy (f + h • dlraField PU PV (M - f)) := by
  obtain ⟨ε, hpos, hnear, hfull, hrate⟩ :=
    (eventually_pos.and ((eventually_near hδ).and eventually_rate)).exists
  obtain ⟨hPU, hPV⟩ := isOrthProjOnto_family ε
  have hf : ∀ i j, 0 < fState ε i j := mkMat_pos hpos
  have hmax : IsMaxwellianOf vel (fState ε) (MState ε) := isMaxwellianOf_family ε
  have hrate' : 0 < entropyRate (fState ε) (dlraField (hyperProj (uvec (yv ε))) (hyperProj w)
      (MState ε - fState ε)) := by
    simpa only [fState, MState, entropyRate_dlra] using hrate
  refine ⟨fState ε, MState ε, _, _, hf, rank_mkMat _, ?_, ?_, hmax, hPU, hPV, ?_, ?_, hrate',
    entropy_euler_step hf hrate'⟩
  · intro i j
    fin_cases i
    · simpa [fState, M₀] using (mul_pos hδ (b1_pos j)).le
    · simpa [fState, M₀] using (mul_pos hδ (b2_pos j)).le
    · simpa [fState, M₀] using (mul_pos hδ (mul_pos two_pos (b3_pos j))).le
    · exact (hnear j).1
  · intro i j
    fin_cases i
    · simpa [MState, M₀] using (mul_pos hδ (b1_pos j)).le
    · simpa [MState, M₀] using (mul_pos hδ (b2_pos j)).le
    · simpa [MState, M₀] using (mul_pos hδ (mul_pos two_pos (b3_pos j))).le
    · exact (hnear j).2
  · intro i k
    have hfix : hyperProj w *ᵥ collInv vel k = collInv vel k :=
      hPV.fix _ (Submodule.subset_span (Or.inr ⟨k, rfl⟩))
    rw [dlraField_moment _ _ hfix]
    have := hmax.moments i k
    simp only [dotProduct, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib] at this ⊢
    linarith
  · simpa only [fState, MState, entropyRate_full] using hfull

end Example

end LeanDLRA.Novel.BGKEntropy
