import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.LowRankDistance
import LeanDLRA.Classical.EckartYoung

/-!
# When is free streaming low rank?  Spatial modes, shear times and recurrence

Open problem OP-OT-61 of `docs/survey/open-problems.json` ("when are kinetic solutions
approximately low rank?").  `LeanDLRA/Novel/EpsRank.lean` treats the
diffusive scaling.  This file treats the opposite, collisionless end: free streaming and, more
generally, every linear scheme on a periodic spatial grid that commutes with the spatial shift.

## Setting

`F ∈ ℝ^{X × V}` with `X = ZMod N` (periodic grid `x_i = 2π i / N`) and an arbitrary finite
velocity index `V`.  A **spatial mode** of frequency `k` is `modeMat θ_k p q = cos(i θ_k) ⊗ p +
sin(i θ_k) ⊗ q`, `θ_k = 2π k / N`; it has rank at most two (one for `k = 0`).  Data with `2K+1`
real spatial Fourier modes is `F₀ = ∑_{k ≤ K} G_k`.  `shift` is the cyclic shift in `x`.

## Main results

* **Upper bound, all times, no limit** (`rank_pow_sum_le`, `rank_pow_sum_le'`).  If `S` is linear
  and commutes with `shift` (`IsTranslationInvariant`), then `rank (Sⁿ F₀) ≤ ∑_{k ∈ K} (1 if k = 0
  else 2) ≤ 2 |K|` for every `n`.  The mechanism is `IsMode.map`: on the pair of a mode and its
  conjugate the shift is a rotation, and `S` preserves the resulting first-order recursion along
  the grid.  Nothing is assumed on `V`, on the time step, on stability or on the Knudsen number:
  upwind, Lax–Wendroff, semi-Lagrangian or spectral transport, BGK and linear Boltzmann with
  `x`-independent cross section, and the linearisation of Vlasov–Poisson at a homogeneous
  equilibrium all commute with the shift.  Multiplication by an `x`-dependent cross section does
  not, which is where the gradual rank growth reported for non-constant scattering comes from.
* **Time-uniform `ε`-rank bound** (`distLR_pow_sum_le`, `epsRank_pow_sum_le`).  If moreover
  `‖S F‖_F ≤ ‖F‖_F` and all modes are below the Nyquist limit (`2k < N`), then for every `K' ⊆ K`
  `dist(Sⁿ F₀, M_{≤ budget K'}) ≤ (∑_{k ∈ K ∖ K'} ‖G_k‖²)^{1/2}` for all `n`, with constant one:
  distinct modes are Frobenius-orthogonal (`inner_modeMat_eq_zero`).
* **Free streaming** `F(t)_{ij} = g(x_i - v_j t)` for a trigonometric polynomial `g` of degree
  `K` and the uniform grid `v_j = v₀ + j Δv`, `j < M` (`freeStream`).  `F(0)` has rank one.
  - `rank_freeStream_le`: `rank F(t) ≤ 2K + 1` for all `t`.
  - `norm_sq_freeStream_sub`: the spectral tail is **exactly** time independent,
    `‖F(t) - F_{K'}(t)‖²_F = N M ∑_{k ∉ K'} w_k`, `w_0 = a_0²`, `w_k = (a_k² + b_k²)/2`;
    hence `distLR_freeStream_le`, `epsRank_freeStream_le` for all `t`.  Filamentation in `v`
    costs no rank; only the spatial spectrum of the data matters.
  - `freeStream_recurrence`, `rank_freeStream_recurrence`: at `t Δv ∈ 2π ℤ` (the recurrence time
    `T_R = 2π / Δv` of the velocity grid) the solution is rank one again.
  - **Lower bound at shear times** (`le_distLR_freeStream_shear`, `lt_epsRank_freeStream_shear`,
    `rank_freeStream_shear`).  At `t Δv = 2π p / M` with `M ∤ m p` for `0 < m ≤ 2K`
    (`ShearCondition`; for instance `p` coprime to `M` and `2K < M`, the first such time being
    `t₁ = 2π / (M Δv) = L / (v_max - v_min + Δv)`), `F(t)` is a sum of `2K + 1` rank-one terms
    with pairwise orthogonal spatial and pairwise orthogonal velocity factors
    (`uVec_orthogonal`, `wVec_orthogonal`), that is, a singular value decomposition with singular
    values `√(N M) |a_0|` and twice `√(N M) (a_k² + b_k²)^{1/2} / 2`, `1 ≤ k ≤ K`
    (`uVec_wVec_sq`).  So `dist(F(t), M_{≤ r}) ≥ c` whenever more than `r` of these exceed `c`,
    the `ε`-rank is at least the number of singular values above `ε`, and the rank is exactly
    `2K + 1` when all modes of `g` are present.  The upper bounds are attained: no bound in terms
    of the velocity resolution can be better, and low rank fails exactly when the spatial
    spectrum of the data is not short.

## Tools

`le_distLR_sum_vecMulVec` is an SVD-free lower bound for the distance to the rank-`r` matrices
of a matrix given as `∑ u_l w_lᵀ` with orthogonal families `u`, `w`: a rank-`r` matrix has a
kernel vector in the span of `r + 1` of the `w_l`.  `sum_cos_sin_eq_zero`, `sum_wave_mul_wave`
are the discrete orthogonality relations of waves on uniform grids, over `ℝ`, via a geometric
sum of roots of unity.

## Not covered

Lower bounds at times other than the shear times (they need the conditioning of Vandermonde
matrices with unit-circle nodes), non-uniform velocity grids, the nonlinear Vlasov coupling and
`x`-dependent cross sections (both break translation invariance; here only the mechanism is
identified, not the rate), and the continuous problem.  Everything is stated for actual matrices
with explicit constants.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Novel.OpOT61

open LeanDLRA LeanDLRA.Frobenius

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-! ### Sums of rank-one matrices with orthogonal factors -/

section RankOne

variable {m n ι : Type*} [Fintype m] [Fintype n] [Fintype ι]

/-- A sum of `|s|` rank-one matrices has rank at most `|s|`. -/
theorem rank_sum_vecMulVec_le (s : Finset ι) (u : ι → m → ℝ) (w : ι → n → ℝ) :
    (∑ l ∈ s, Matrix.vecMulVec (u l) (w l)).rank ≤ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    calc (Matrix.vecMulVec (u a) (w a) + ∑ l ∈ s, Matrix.vecMulVec (u l) (w l)).rank
        ≤ (Matrix.vecMulVec (u a) (w a)).rank + (∑ l ∈ s, Matrix.vecMulVec (u l) (w l)).rank :=
          EckartYoung.rank_add_le _ _
      _ ≤ 1 + s.card := add_le_add (Matrix.rank_vecMulVec_le _ _) ih
      _ = s.card + 1 := add_comm _ _

/-- The Frobenius inner product of two rank-one matrices is the product of the inner products
of the factors. -/
theorem inner_vecMulVec (u u' : m → ℝ) (w w' : n → ℝ) :
    ⟪Matrix.vecMulVec u w, Matrix.vecMulVec u' w'⟫ = (∑ i, u i * u' i) * ∑ j, w j * w' j := by
  rw [inner_def, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.vecMulVec_apply]; ring

/-- **Pythagoras for a sum of rank-one matrices with orthogonal left factors.** -/
theorem norm_sq_sum_vecMulVec (s : Finset ι) (u : ι → m → ℝ) (w : ι → n → ℝ)
    (hu : ∀ l ∈ s, ∀ l' ∈ s, l ≠ l' → ∑ i, u l i * u l' i = 0) :
    ‖∑ l ∈ s, Matrix.vecMulVec (u l) (w l)‖ ^ 2 =
      ∑ l ∈ s, (∑ i, u l i ^ 2) * ∑ j, w l j ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [inner_sum, Finset.sum_eq_single l]
  · rw [inner_vecMulVec]; simp only [sq]
  · intro l' hl' hne
    rw [inner_vecMulVec, hu l hl l' hl' (Ne.symm hne), zero_mul]
  · intro h; exact absurd hl h

/-- The action of a sum of rank-one matrices on a vector. -/
theorem sum_vecMulVec_mulVec (s : Finset ι) (u : ι → m → ℝ) (w : ι → n → ℝ) (x : n → ℝ) :
    (∑ l ∈ s, Matrix.vecMulVec (u l) (w l)) *ᵥ x = ∑ l ∈ s, (∑ j, w l j * x j) • u l := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Matrix.vecMulVec_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Lower bound for the distance to the rank-`r` matrices, without the SVD.**  If
`F = ∑ u_l w_lᵀ` with pairwise orthogonal `u_l` and pairwise orthogonal `w_l`, and
`‖u_l‖ ‖w_l‖ ≥ c` for all `l` in a set `s` with `|s| > r`, then `dist(F, M_{≤ r}) ≥ c`.  This is
the Eckart–Young lower bound `σ_{r+1} ≤ dist(F, M_{≤ r})` for a matrix given in diagonal form,
proved directly: a rank-`r` matrix has a kernel vector in the span of `{w_l : l ∈ s}`. -/
theorem le_distLR_sum_vecMulVec (s : Finset ι) (u : ι → m → ℝ) (w : ι → n → ℝ)
    (hu : ∀ l l', l ≠ l' → ∑ i, u l i * u l' i = 0)
    (hw : ∀ l l', l ≠ l' → ∑ j, w l j * w l' j = 0)
    {c : ℝ} (hc : 0 ≤ c) (hcs : ∀ l ∈ s, c ^ 2 ≤ (∑ i, u l i ^ 2) * ∑ j, w l j ^ 2)
    {r : ℕ} (hr : r < s.card) :
    c ≤ distLR r (∑ l, Matrix.vecMulVec (u l) (w l)) := by
  classical
  rcases hc.lt_or_eq with hc | hc
  swap; · rw [← hc]; exact distLR_nonneg
  rw [le_distLR_iff]
  intro Z hZ
  -- the matrix whose columns are the `w_l`, `l ∈ s`
  set W : Matrix n s ℝ := Matrix.of fun j (l : s) => w l j with hW
  have hrank : (Z * W).rank < Fintype.card s := by
    rw [Fintype.card_coe]
    exact lt_of_le_of_lt (Matrix.rank_mul_le_left _ _) (lt_of_le_of_lt hZ hr)
  obtain ⟨α, hα0, hZα⟩ := exists_mulVec_eq_zero_of_rank_lt hrank
  -- the coefficients, extended by zero outside `s`
  set β : ι → ℝ := fun l => if h : l ∈ s then α ⟨l, h⟩ else 0 with hβ
  have hβs : ∀ l, l ∉ s → β l = 0 := fun l hl => by simp [hβ, hl]
  have hβ0 : ∃ l, β l ≠ 0 := by
    obtain ⟨l, hl⟩ := Function.ne_iff.mp hα0
    exact ⟨l, by simpa [hβ, l.2] using hl⟩
  set x : n → ℝ := W *ᵥ α with hx
  have hZx : Z *ᵥ x = 0 := by rw [hx, Matrix.mulVec_mulVec, hZα]
  -- `x = ∑_l β_l w_l`
  have hxj : ∀ j, x j = ∑ l, β l * w l j := by
    intro j
    rw [← Finset.sum_subset (Finset.subset_univ s) (fun l _ hl => by rw [hβs l hl, zero_mul]),
      ← Finset.sum_coe_sort]
    simp only [hx, Matrix.mulVec, dotProduct, hW, Matrix.of_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [hβ, l.2, mul_comm]
  -- `⟨w_l, x⟩ = β_l ‖w_l‖²`
  have hdot : ∀ l, ∑ j, w l j * x j = β l * ∑ j, w l j ^ 2 := by
    intro l
    simp only [hxj, Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_eq_single l]
    · refine Finset.sum_congr rfl fun j _ => ?_; ring
    · intro l' _ hne
      calc ∑ j, w l j * (β l' * w l' j) = β l' * ∑ j, w l j * w l' j := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
        _ = 0 := by rw [hw l l' (Ne.symm hne), mul_zero]
    · intro h; exact absurd (Finset.mem_univ l) h
  -- the squares of the `w_l` are positive on `s`
  have hwpos : ∀ l ∈ s, 0 < ∑ j, w l j ^ 2 := by
    intro l hl
    have h1 := hcs l hl
    have h2 : 0 < c ^ 2 := by positivity
    by_contra h
    push Not at h
    have h3 : ∑ j, w l j ^ 2 = 0 :=
      le_antisymm h (Finset.sum_nonneg fun j _ => sq_nonneg _)
    rw [h3, mul_zero] at h1; linarith
  -- `‖x‖² = ∑ β_l² ‖w_l‖²`
  have hxsq : ∑ j, x j ^ 2 = ∑ l, β l ^ 2 * ∑ j, w l j ^ 2 := by
    calc ∑ j, x j ^ 2 = ∑ j, ∑ l, β l * (w l j * x j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          have e : x j ^ 2 = (∑ l, β l * w l j) * x j := by rw [← hxj j, sq]
          rw [e, Finset.sum_mul]
          refine Finset.sum_congr rfl fun l _ => ?_; ring
      _ = ∑ l, β l * ∑ j, w l j * x j := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ l, β l ^ 2 * ∑ j, w l j ^ 2 := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hdot l]; ring
  -- `x ≠ 0`
  have hxpos : 0 < ∑ j, x j ^ 2 := by
    rw [hxsq]
    obtain ⟨l, hl⟩ := hβ0
    have hls : l ∈ s := by by_contra h; exact hl (hβs l h)
    have h1 : 0 < β l ^ 2 * ∑ j, w l j ^ 2 :=
      mul_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hl))) (hwpos l hls)
    exact lt_of_lt_of_le h1 (Finset.single_le_sum (f := fun l => β l ^ 2 * ∑ j, w l j ^ 2)
      (fun l _ => mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _))
      (Finset.mem_univ l))
  -- `F x = ∑_l β_l ‖w_l‖² u_l`
  have hFx : (∑ l, Matrix.vecMulVec (u l) (w l)) *ᵥ x = ∑ l, (β l * ∑ j, w l j ^ 2) • u l := by
    rw [sum_vecMulVec_mulVec]; simp_rw [hdot]
  -- `‖F x‖² ≥ c² ‖x‖²`
  have hFxsq : c ^ 2 * ∑ j, x j ^ 2 ≤
      ∑ i, ((∑ l, Matrix.vecMulVec (u l) (w l)) *ᵥ x) i ^ 2 := by
    rw [hFx, hxsq, Finset.mul_sum]
    have : ∀ i, (∑ l, (β l * ∑ j, w l j ^ 2) • u l) i ^ 2 =
        ∑ l, ∑ l', (β l * ∑ j, w l j ^ 2) * (β l' * ∑ j, w l' j ^ 2) * (u l i * u l' i) := by
      intro i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_; ring
    simp_rw [this]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [Finset.sum_comm, Finset.sum_eq_single l]
    · rw [← Finset.mul_sum]
      have h4 : ∑ i, u l i * u l i = ∑ i, u l i ^ 2 := by simp [sq]
      rw [h4]
      by_cases hls : l ∈ s
      · have h5 : β l ^ 2 * (∑ j, w l j ^ 2) * c ^ 2 ≤
            β l ^ 2 * (∑ j, w l j ^ 2) * ((∑ i, u l i ^ 2) * ∑ j, w l j ^ 2) :=
          mul_le_mul_of_nonneg_left (hcs l hls)
            (mul_nonneg (sq_nonneg (β l)) (Finset.sum_nonneg fun j _ => sq_nonneg (w l j)))
        calc c ^ 2 * (β l ^ 2 * ∑ j, w l j ^ 2) = β l ^ 2 * (∑ j, w l j ^ 2) * c ^ 2 := by ring
          _ ≤ β l ^ 2 * (∑ j, w l j ^ 2) * ((∑ i, u l i ^ 2) * ∑ j, w l j ^ 2) := h5
          _ = (β l * ∑ j, w l j ^ 2) * (β l * ∑ j, w l j ^ 2) * ∑ i, u l i ^ 2 := by ring
      · rw [hβs l hls]; simp
    · intro l' _ hne
      rw [← Finset.mul_sum, hu l l' (Ne.symm hne), mul_zero]
    · intro h; exact absurd (Finset.mem_univ l) h
  -- conclude with Cauchy–Schwarz
  have h1 : (∑ l, Matrix.vecMulVec (u l) (w l) - Z) *ᵥ x =
      (∑ l, Matrix.vecMulVec (u l) (w l)) *ᵥ x := by
    rw [Matrix.sub_mulVec, hZx, sub_zero]
  have h2 := sum_sq_mulVec_le (∑ l, Matrix.vecMulVec (u l) (w l) - Z) x
  rw [h1] at h2
  have h3 : c ^ 2 ≤ ‖∑ l, Matrix.vecMulVec (u l) (w l) - Z‖ ^ 2 :=
    le_of_mul_le_mul_right (hFxsq.trans h2) hxpos
  exact (pow_le_pow_iff_left₀ hc.le (norm_nonneg _) two_ne_zero).mp h3

end RankOne

/-! ### Trigonometric sums on uniform grids -/

section TrigSums

open Real

/-- `∑_{j<M} exp((θ + j α) i) = 0` when `exp(α i)` is a nontrivial `M`-th root of unity; in real
terms, the cosine and sine sums both vanish. -/
theorem sum_cos_sin_eq_zero {M : ℕ} {θ α : ℝ} (h1 : Complex.exp (α * Complex.I) ^ M = 1)
    (h2 : Complex.exp (α * Complex.I) ≠ 1) :
    ∑ j ∈ range M, cos (θ + j * α) = 0 ∧ ∑ j ∈ range M, sin (θ + j * α) = 0 := by
  have key : ∑ j ∈ range M, Complex.exp (((θ + j * α : ℝ) : ℂ) * Complex.I) = 0 := by
    have : ∀ j : ℕ, Complex.exp (((θ + j * α : ℝ) : ℂ) * Complex.I) =
        Complex.exp (θ * Complex.I) * Complex.exp (α * Complex.I) ^ j := by
      intro j
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1; push_cast; ring
    simp_rw [this, ← Finset.mul_sum]
    rw [geom_sum_eq h2, h1, sub_self, zero_div, mul_zero]
  constructor
  · have := congrArg Complex.re key
    simp only [Complex.re_sum, Complex.exp_ofReal_mul_I_re, Complex.zero_re] at this
    exact this
  · have := congrArg Complex.im key
    simp only [Complex.im_sum, Complex.exp_ofReal_mul_I_im, Complex.zero_im] at this
    exact this

/-- The grid case: `α = 2π m / q` with `q ∣ M` and `q ∤ m` gives a nontrivial `M`-th root of
unity. -/
theorem sum_cos_sin_grid_eq_zero {M q : ℕ} {m : ℤ} (hq : q ∣ M) (hm : ¬ (q : ℤ) ∣ m)
    (θ : ℝ) :
    ∑ j ∈ range M, cos (θ + j * (2 * π * m / q)) = 0 ∧
      ∑ j ∈ range M, sin (θ + j * (2 * π * m / q)) = 0 := by
  rcases Nat.eq_zero_or_pos q with rfl | hqpos
  · rw [zero_dvd_iff] at hq; subst hq; simp
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hqpos.ne'
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hqpos.ne'
  obtain ⟨d, hd⟩ := hq
  apply sum_cos_sin_eq_zero
  · rw [← Complex.exp_nat_mul, hd]
    have : ((q * d : ℕ) : ℂ) * (((2 * π * m / q : ℝ) : ℂ) * Complex.I) =
        ((m * d : ℤ) : ℂ) * (2 * π * Complex.I) := by
      push_cast
      field_simp
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  · intro h
    rw [Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    have h3 : ((2 * π * m / q : ℝ) : ℂ) * Complex.I = ((n * (2 * π) : ℝ) : ℂ) * Complex.I := by
      rw [hn]; push_cast; ring
    have h4 : (2 * π * m / q : ℝ) = n * (2 * π) := by
      exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero h3
    rw [div_eq_iff hq0] at h4
    have hpi : (2 * π : ℝ) ≠ 0 := by positivity
    have h5 : (2 * π) * (m : ℝ) = (2 * π) * (q * n) := by linear_combination h4
    have h6 : (m : ℝ) = q * n := mul_left_cancel₀ hpi h5
    exact hm ⟨n, by exact_mod_cast h6⟩

/-- **Product of two waves on a grid.**  The bilinear expansion of
`∑_j (A cos φ_j + B sin φ_j)(A' cos ψ_j + B' sin ψ_j)` in terms of the sums of `cos`, `sin` of
`φ_j ∓ ψ_j`, for `φ_j = θ₁ + j α₁`, `ψ_j = θ₂ + j α₂`. -/
theorem sum_wave_mul_wave (M : ℕ) (A B A' B' θ₁ α₁ θ₂ α₂ : ℝ) :
    ∑ j ∈ range M, (A * cos (θ₁ + j * α₁) + B * sin (θ₁ + j * α₁)) *
        (A' * cos (θ₂ + j * α₂) + B' * sin (θ₂ + j * α₂)) =
      ((A * A' + B * B') * ∑ j ∈ range M, cos ((θ₁ - θ₂) + j * (α₁ - α₂)) +
        (A * A' - B * B') * ∑ j ∈ range M, cos ((θ₁ + θ₂) + j * (α₁ + α₂)) +
        (B * A' - A * B') * ∑ j ∈ range M, sin ((θ₁ - θ₂) + j * (α₁ - α₂)) +
        (A * B' + B * A') * ∑ j ∈ range M, sin ((θ₁ + θ₂) + j * (α₁ + α₂))) / 2 := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : (θ₁ - θ₂) + j * (α₁ - α₂) = (θ₁ + j * α₁) - (θ₂ + j * α₂) := by ring
  have e2 : (θ₁ + θ₂) + j * (α₁ + α₂) = (θ₁ + j * α₁) + (θ₂ + j * α₂) := by ring
  rw [e1, e2, cos_sub (θ₁ + j * α₁) (θ₂ + j * α₂), cos_add (θ₁ + j * α₁) (θ₂ + j * α₂),
    sin_sub (θ₁ + j * α₁) (θ₂ + j * α₂), sin_add (θ₁ + j * α₁) (θ₂ + j * α₂)]
  ring

end TrigSums

/-! ### Spatial modes on a periodic grid and translation-invariant schemes -/

section Modes

open Real

variable {N : ℕ} [NeZero N] {V : Type*} [Fintype V]

/-- Sums over `ZMod N` of a function of the value are sums over `range N`. -/
theorem sum_zmod_val (f : ℕ → ℝ) : ∑ i : ZMod N, f i.val = ∑ i ∈ range N, f i := by
  have himg : (Finset.univ : Finset (ZMod N)).image ZMod.val = range N := by
    ext a
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨i, rfl⟩; exact ZMod.val_lt i
    · intro ha; exact ⟨a, ZMod.val_cast_of_lt ha⟩
  rw [← himg, Finset.sum_image (fun i _ j _ h => ZMod.val_injective N h)]

/-- `sum_zmod_val` with the summand given pointwise. -/
theorem sum_zmod_val' (g : ZMod N → ℝ) (f : ℕ → ℝ) (h : ∀ i, g i = f i.val) :
    ∑ i, g i = ∑ i ∈ range N, f i := by
  rw [← sum_zmod_val]; exact Finset.sum_congr rfl fun i _ => h i

/-- The cyclic shift in space, `(T F)_{i, v} = F_{i-1, v}`. -/
def shift : Matrix (ZMod N) V ℝ →ₗ[ℝ] Matrix (ZMod N) V ℝ where
  toFun F := Matrix.of fun i j => F (i - 1) j
  map_add' F G := by ext i j; simp
  map_smul' c F := by ext i j; simp

@[simp] theorem shift_apply (F : Matrix (ZMod N) V ℝ) (i : ZMod N) (j : V) :
    shift F i j = F (i - 1) j := rfl

/-- A **spatial mode** of angle `θ` on the grid: `cos(i θ) ⊗ p + sin(i θ) ⊗ q`. -/
noncomputable def modeMat (θ : ℝ) (p q : V → ℝ) : Matrix (ZMod N) V ℝ :=
  Matrix.of fun i j => cos (i.val * θ) * p j + sin (i.val * θ) * q j

@[simp] theorem modeMat_apply (θ : ℝ) (p q : V → ℝ) (i : ZMod N) (j : V) :
    modeMat θ p q i j = cos (i.val * θ) * p j + sin (i.val * θ) * q j := rfl

theorem modeMat_eq_add (θ : ℝ) (p q : V → ℝ) :
    (modeMat θ p q : Matrix (ZMod N) V ℝ) =
      Matrix.vecMulVec (fun i : ZMod N => cos (i.val * θ)) p +
        Matrix.vecMulVec (fun i : ZMod N => sin (i.val * θ)) q := by
  ext i j; simp [Matrix.vecMulVec_apply]

/-- A mode has rank at most two. -/
theorem rank_modeMat_le (θ : ℝ) (p q : V → ℝ) :
    (modeMat θ p q : Matrix (ZMod N) V ℝ).rank ≤ 2 := by
  rw [modeMat_eq_add]
  exact (EckartYoung.rank_add_le _ _).trans
    (add_le_add (Matrix.rank_vecMulVec_le _ _) (Matrix.rank_vecMulVec_le _ _))

/-- The mode of angle zero is isotropic in space and has rank at most one. -/
theorem rank_modeMat_zero_le (p q : V → ℝ) :
    (modeMat 0 p q : Matrix (ZMod N) V ℝ).rank ≤ 1 := by
  have : (modeMat 0 p q : Matrix (ZMod N) V ℝ) = Matrix.vecMulVec (fun _ => 1) p := by
    ext i j; simp [Matrix.vecMulVec_apply]
  rw [this]; exact Matrix.rank_vecMulVec_le _ _

/-- `θ` is a grid angle if `N θ ∈ 2π ℤ`. -/
def IsGridAngle (N : ℕ) (θ : ℝ) : Prop := ∃ k : ℤ, (N : ℝ) * θ = k * (2 * π)

/-- The angle `2π k / N` of the `k`-th Fourier mode. -/
noncomputable def modeAngle (N k : ℕ) : ℝ := 2 * π * k / N

theorem isGridAngle_modeAngle (k : ℕ) : IsGridAngle N (modeAngle N k) := by
  refine ⟨k, ?_⟩
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  unfold modeAngle; field_simp; norm_cast

@[simp] theorem modeAngle_zero : modeAngle N 0 = 0 := by simp [modeAngle]

/-- The value of `i - 1` in `ZMod N`. -/
theorem val_sub_one (i : ZMod N) :
    ((i - 1).val : ℝ) = if i = 0 then (N : ℝ) - 1 else (i.val : ℝ) - 1 := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  split_ifs with h
  · subst h
    have h1 : (0 - 1 : ZMod N) = ((N - 1 : ℕ) : ZMod N) := by
      rw [Nat.cast_sub hN, ZMod.natCast_self, Nat.cast_one]
    rw [h1, ZMod.val_cast_of_lt (by omega), Nat.cast_sub hN, Nat.cast_one]
  · have hv : 0 < i.val := Nat.pos_of_ne_zero (fun h' => h ((ZMod.val_eq_zero i).mp h'))
    have h1 : i - 1 = ((i.val - 1 : ℕ) : ZMod N) := by
      rw [Nat.cast_sub hv, ZMod.natCast_zmod_val, Nat.cast_one]
    rw [h1, ZMod.val_cast_of_lt (by have := ZMod.val_lt i; omega), Nat.cast_sub hv, Nat.cast_one]

/-- For a grid angle, the shift acts on the wave `i ↦ (cos(iθ), sin(iθ))` as the rotation by
`-θ`, including across the periodic boundary. -/
theorem cos_sin_val_sub_one {θ : ℝ} (hθ : IsGridAngle N θ) (i : ZMod N) :
    cos ((i - 1).val * θ) = cos (i.val * θ - θ) ∧
      sin ((i - 1).val * θ) = sin (i.val * θ - θ) := by
  obtain ⟨k, hk⟩ := hθ
  rw [val_sub_one]
  split_ifs with h
  · subst h
    have : ((N : ℝ) - 1) * θ = k * (2 * π) - θ := by rw [← hk]; ring
    rw [this, cos_int_mul_two_pi_sub, sin_int_mul_two_pi_sub]
    simp
  · constructor <;> congr 1 <;> ring

theorem shift_modeMat {θ : ℝ} (hθ : IsGridAngle N θ) (p q : V → ℝ) :
    shift (modeMat θ p q : Matrix (ZMod N) V ℝ) =
      modeMat θ (cos θ • p - sin θ • q) (sin θ • p + cos θ • q) := by
  ext i j
  obtain ⟨hc, hs⟩ := cos_sin_val_sub_one hθ i
  simp only [shift_apply, modeMat_apply, hc, hs, cos_sub, sin_sub, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- `F` is a spatial mode of angle `θ`. -/
def IsMode (θ : ℝ) (F : Matrix (ZMod N) V ℝ) : Prop := ∃ p q : V → ℝ, F = modeMat θ p q

theorem isMode_modeMat (θ : ℝ) (p q : V → ℝ) : IsMode θ (modeMat θ p q : Matrix (ZMod N) V ℝ) :=
  ⟨p, q, rfl⟩

theorem IsMode.rank_le {θ : ℝ} {F : Matrix (ZMod N) V ℝ} (hF : IsMode θ F) : F.rank ≤ 2 := by
  obtain ⟨p, q, rfl⟩ := hF; exact rank_modeMat_le θ p q

theorem IsMode.rank_le_one {F : Matrix (ZMod N) V ℝ} (hF : IsMode 0 F) : F.rank ≤ 1 := by
  obtain ⟨p, q, rfl⟩ := hF; exact rank_modeMat_zero_le p q

/-- A linear map on `X × V` matrices is **translation invariant** if it commutes with the cyclic
shift in space.  Every finite-difference, semi-Lagrangian or spectral transport step on a periodic
grid with `x`-independent coefficients, and every collision operator with `x`-independent
parameters, has this property; multiplication by an `x`-dependent cross section does not. -/
def IsTranslationInvariant (S : Matrix (ZMod N) V ℝ →ₗ[ℝ] Matrix (ZMod N) V ℝ) : Prop :=
  ∀ F, S (shift F) = shift (S F)

/-- **Translation-invariant linear maps preserve each spatial mode.**  The mechanism: on the
two-dimensional space of waves `(cos(iθ), sin(iθ))` the shift is the rotation by `-θ`, and the
pair `G = S X`, `G' = S (J X)` of images of a mode and its conjugate satisfies the same first-order
recursion in `i`, which has only the mode solutions. -/
theorem IsMode.map {S : Matrix (ZMod N) V ℝ →ₗ[ℝ] Matrix (ZMod N) V ℝ}
    (hS : IsTranslationInvariant S) {θ : ℝ} (hθ : IsGridAngle N θ) {X : Matrix (ZMod N) V ℝ}
    (hX : IsMode θ X) : IsMode θ (S X) := by
  obtain ⟨p, q, rfl⟩ := hX
  set G := S (modeMat θ p q) with hG
  set G' := S (modeMat θ q (-p)) with hG'
  -- the shifted pair
  have h1 : shift G = cos θ • G - sin θ • G' := by
    rw [hG, ← hS, shift_modeMat hθ, hG', ← map_smul, ← map_smul, ← map_sub]
    refine congrArg S ?_
    ext i j; simp only [modeMat_apply, Matrix.sub_apply, Matrix.smul_apply, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]; ring
  have h2 : shift G' = cos θ • G' + sin θ • G := by
    rw [hG', ← hS, shift_modeMat hθ, hG, ← map_smul, ← map_smul, ← map_add]
    refine congrArg S ?_
    ext i j; simp only [modeMat_apply, Matrix.add_apply, Matrix.smul_apply, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]; ring
  -- the recursion along the grid
  have key : ∀ n : ℕ, ∀ j, G (n : ZMod N) j = cos (n * θ) * G 0 j + sin (n * θ) * G' 0 j ∧
      G' (n : ZMod N) j = cos (n * θ) * G' 0 j - sin (n * θ) * G 0 j := by
    intro n
    induction n with
    | zero => intro j; simp
    | succ n ih =>
      intro j
      obtain ⟨ih1, ih2⟩ := ih j
      have e1 := congrFun (congrFun h1 ((n + 1 : ℕ) : ZMod N)) j
      have e2 := congrFun (congrFun h2 ((n + 1 : ℕ) : ZMod N)) j
      simp only [shift_apply, Nat.cast_succ, add_sub_cancel_right, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at e1 e2
      have pyth := cos_sq_add_sin_sq θ
      have f1 : G ((n : ZMod N) + 1) j = cos θ * G n j + sin θ * G' n j := by
        linear_combination (-cos θ) * e1 + (-sin θ) * e2 + (-G ((n : ZMod N) + 1) j) * pyth
      have f2 : G' ((n : ZMod N) + 1) j = cos θ * G' n j - sin θ * G n j := by
        linear_combination (sin θ) * e1 + (-cos θ) * e2 + (-G' ((n : ZMod N) + 1) j) * pyth
      rw [Nat.cast_succ, f1, f2, ih1, ih2]
      push_cast
      rw [add_mul, one_mul, cos_add, sin_add]
      constructor <;> ring
  refine ⟨fun j => G 0 j, fun j => G' 0 j, ?_⟩
  ext i j
  have := (key i.val j).1
  rw [ZMod.natCast_zmod_val] at this
  simpa [modeMat_apply] using this

/-- Iterates of a translation-invariant map preserve each spatial mode. -/
theorem IsMode.pow {S : Matrix (ZMod N) V ℝ →ₗ[ℝ] Matrix (ZMod N) V ℝ}
    (hS : IsTranslationInvariant S) {θ : ℝ} (hθ : IsGridAngle N θ) {X : Matrix (ZMod N) V ℝ}
    (hX : IsMode θ X) (n : ℕ) : IsMode θ ((S ^ n) X) := by
  induction n with
  | zero => simpa using hX
  | succ n ih => rw [pow_succ', mul_apply_eq_comp]; exact ih.map hS hθ

/-- The rank of a sum is at most the sum of the ranks. -/
theorem rank_sum_le {ι : Type*} (s : Finset ι) (A : ι → Matrix (ZMod N) V ℝ) :
    (∑ k ∈ s, A k).rank ≤ ∑ k ∈ s, (A k).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (EckartYoung.rank_add_le _ _).trans (add_le_add le_rfl ih)

/-- The rank budget of the mode set `K`: one for the isotropic mode, two for every other. -/
def modeBudget (K : Finset ℕ) : ℕ := ∑ k ∈ K, if k = 0 then 1 else 2

theorem modeBudget_le (K : Finset ℕ) : modeBudget K ≤ 2 * K.card := by
  unfold modeBudget
  calc ∑ k ∈ K, (if k = 0 then 1 else 2) ≤ ∑ _k ∈ K, 2 :=
        Finset.sum_le_sum fun k _ => by split_ifs <;> omega
    _ = 2 * K.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

theorem modeBudget_range (K : ℕ) : modeBudget (range (K + 1)) = 2 * K + 1 := by
  unfold modeBudget
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ, ih]; simp; ring

/-- **The spatial mode count bounds the rank for all times.**  If `F₀ = ∑_{k ∈ K} G_k` with `G_k` a
spatial mode of frequency `k`, then for every translation-invariant linear scheme `S` and every
number of steps `n`, `rank (Sⁿ F₀) ≤ ∑_{k ∈ K} (1 if k = 0 else 2) ≤ 2 |K|`.  No stability,
no smallness, no limit is used: free streaming, upwind or spectral transport, BGK or linear
Boltzmann with `x`-independent cross section, and linearised Vlasov–Poisson all qualify, at every
Knudsen number and every time step.  See OP-OT-61. -/
theorem rank_pow_sum_le {S : Matrix (ZMod N) V ℝ →ₗ[ℝ] Matrix (ZMod N) V ℝ}
    (hS : IsTranslationInvariant S) {K : Finset ℕ} {G : ℕ → Matrix (ZMod N) V ℝ}
    (hG : ∀ k ∈ K, IsMode (modeAngle N k) (G k)) (n : ℕ) :
    ((S ^ n) (∑ k ∈ K, G k)).rank ≤ modeBudget K := by
  rw [map_sum]
  refine (rank_sum_le K _).trans (Finset.sum_le_sum fun k hk => ?_)
  have hk' := (hG k hk).pow hS (isGridAngle_modeAngle k) n
  split_ifs with h0
  · subst h0; rw [modeAngle_zero] at hk'; exact hk'.rank_le_one
  · exact hk'.rank_le

theorem rank_pow_sum_le' {S : Matrix (ZMod N) V ℝ →ₗ[ℝ] Matrix (ZMod N) V ℝ}
    (hS : IsTranslationInvariant S) {K : Finset ℕ} {G : ℕ → Matrix (ZMod N) V ℝ}
    (hG : ∀ k ∈ K, IsMode (modeAngle N k) (G k)) (n : ℕ) :
    ((S ^ n) (∑ k ∈ K, G k)).rank ≤ 2 * K.card :=
  (rank_pow_sum_le hS hG n).trans (modeBudget_le K)

end Modes

/-! ### Orthogonality of distinct modes, and the time-uniform `ε`-rank bound -/

section Orthogonality

open Real

variable {N : ℕ} [NeZero N] {V : Type*} [Fintype V]

/-- Pythagoras for a finite family of pairwise orthogonal vectors. -/
theorem norm_sq_sum_of_pairwise_orthogonal {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (s : Finset ι) (A : ι → E)
    (h : ∀ k ∈ s, ∀ k' ∈ s, k ≠ k' → ⟪A k, A k'⟫ = 0) :
    ‖∑ k ∈ s, A k‖ ^ 2 = ∑ k ∈ s, ‖A k‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [inner_sum, Finset.sum_eq_single k]
  · exact real_inner_self_eq_norm_sq _
  · intro k' hk' hne; exact h k hk k' hk' (Ne.symm hne)
  · intro h'; exact absurd hk h'

/-- Grid sums of a nontrivial frequency vanish: `∑_{i<N} cos(2π i m / N) = 0` for `N ∤ m`. -/
theorem grid_sum_eq_zero {m : ℤ} (hm : ¬ (N : ℤ) ∣ m) :
    ∑ i ∈ range N, cos (i * (2 * π * m / N)) = 0 ∧
      ∑ i ∈ range N, sin (i * (2 * π * m / N)) = 0 := by
  have := sum_cos_sin_grid_eq_zero (M := N) (q := N) (m := m) dvd_rfl hm 0
  simpa using this

/-- `sum_wave_mul_wave` with zero phases. -/
theorem sum_wave_mul_wave_zero (M : ℕ) (A B A' B' α₁ α₂ : ℝ) :
    ∑ j ∈ range M, (A * cos (j * α₁) + B * sin (j * α₁)) *
        (A' * cos (j * α₂) + B' * sin (j * α₂)) =
      ((A * A' + B * B') * ∑ j ∈ range M, cos (j * (α₁ - α₂)) +
        (A * A' - B * B') * ∑ j ∈ range M, cos (j * (α₁ + α₂)) +
        (B * A' - A * B') * ∑ j ∈ range M, sin (j * (α₁ - α₂)) +
        (A * B' + B * A') * ∑ j ∈ range M, sin (j * (α₁ + α₂))) / 2 := by
  have := sum_wave_mul_wave M A B A' B' 0 α₁ 0 α₂
  simpa using this

theorem modeAngle_sub (k k' : ℕ) :
    modeAngle N k - modeAngle N k' = 2 * π * (((k : ℤ) - k' : ℤ) : ℝ) / N := by
  unfold modeAngle; push_cast; ring

theorem modeAngle_add (k k' : ℕ) :
    modeAngle N k + modeAngle N k' = 2 * π * (((k : ℤ) + k' : ℤ) : ℝ) / N := by
  unfold modeAngle; push_cast; ring

theorem not_dvd_of_lt {m : ℤ} (h0 : m ≠ 0) (h : |m| < N) : ¬ (N : ℤ) ∣ m :=
  fun hd => h0 (Int.eq_zero_of_abs_lt_dvd hd h)

/-- **Waves of distinct frequencies below the Nyquist limit are orthogonal on the grid.** -/
theorem sum_xwave_mul_eq_zero {k k' : ℕ} (hk : 2 * k < N) (hk' : 2 * k' < N) (hne : k ≠ k')
    (A B A' B' : ℝ) :
    ∑ i ∈ range N, (A * cos (i * modeAngle N k) + B * sin (i * modeAngle N k)) *
      (A' * cos (i * modeAngle N k') + B' * sin (i * modeAngle N k')) = 0 := by
  rw [sum_wave_mul_wave_zero, modeAngle_sub, modeAngle_add]
  have h1 := grid_sum_eq_zero (N := N) (m := (k : ℤ) - k')
    (not_dvd_of_lt (by omega) (by rw [abs_lt]; constructor <;> omega))
  have h2 := grid_sum_eq_zero (N := N) (m := (k : ℤ) + k')
    (not_dvd_of_lt (by omega) (by rw [abs_lt]; constructor <;> omega))
  rw [h1.1, h1.2, h2.1, h2.2]; ring

/-- **The Gram matrix of one wave below the Nyquist limit**: `∑_i cos² = ∑_i sin² = N/2`,
`∑_i cos sin = 0`, in one formula. -/
theorem sum_xwave_mul_same {k : ℕ} (hk0 : 0 < k) (hk : 2 * k < N) (A B A' B' : ℝ) :
    ∑ i ∈ range N, (A * cos (i * modeAngle N k) + B * sin (i * modeAngle N k)) *
      (A' * cos (i * modeAngle N k) + B' * sin (i * modeAngle N k)) =
      N * (A * A' + B * B') / 2 := by
  rw [sum_wave_mul_wave_zero, modeAngle_add, sub_self]
  have h2 := grid_sum_eq_zero (N := N) (m := (k : ℤ) + k)
    (not_dvd_of_lt (by omega) (by rw [abs_lt]; constructor <;> omega))
  rw [h2.1, h2.2]
  simp only [mul_zero, cos_zero, sin_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one]
  ring

/-- The Frobenius inner product of two modes as a sum over the velocity index of grid sums. -/
theorem inner_modeMat (θ θ' : ℝ) (p q p' q' : V → ℝ) :
    ⟪(modeMat θ p q : Matrix (ZMod N) V ℝ), modeMat θ' p' q'⟫ =
      ∑ j, ∑ i ∈ range N, (p j * cos (i * θ) + q j * sin (i * θ)) *
        (p' j * cos (i * θ') + q' j * sin (i * θ')) := by
  rw [inner_def, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← sum_zmod_val (fun i => (p j * cos (i * θ) + q j * sin (i * θ)) *
    (p' j * cos (i * θ') + q' j * sin (i * θ')))]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [modeMat_apply]; ring

/-- **Distinct modes below the Nyquist limit are Frobenius-orthogonal.** -/
theorem inner_modeMat_eq_zero {k k' : ℕ} (hk : 2 * k < N) (hk' : 2 * k' < N) (hne : k ≠ k')
    (p q p' q' : V → ℝ) :
    ⟪(modeMat (modeAngle N k) p q : Matrix (ZMod N) V ℝ), modeMat (modeAngle N k') p' q'⟫ = 0 := by
  rw [inner_modeMat]
  exact Finset.sum_eq_zero fun j _ => sum_xwave_mul_eq_zero hk hk' hne _ _ _ _

/-- The Frobenius norm of a mode below the Nyquist limit: `‖C ⊗ p + S ⊗ q‖² = N (‖p‖² + ‖q‖²)/2`. -/
theorem norm_sq_modeMat {k : ℕ} (hk0 : 0 < k) (hk : 2 * k < N) (p q : V → ℝ) :
    ‖(modeMat (modeAngle N k) p q : Matrix (ZMod N) V ℝ)‖ ^ 2 =
      N * (∑ j, p j ^ 2 + ∑ j, q j ^ 2) / 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_modeMat]
  simp_rw [sum_xwave_mul_same hk0 hk]
  rw [← Finset.sum_div, ← Finset.mul_sum, Finset.sum_add_distrib]
  simp only [sq]

theorem norm_sq_modeMat_zero (p q : V → ℝ) :
    ‖(modeMat 0 p q : Matrix (ZMod N) V ℝ)‖ ^ 2 = N * ∑ j, p j ^ 2 := by
  rw [norm_sq_eq_sum]
  simp only [modeMat_apply, mul_zero, cos_zero, sin_zero, one_mul, zero_mul, add_zero,
    Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]

/-- Iterates of a Frobenius contraction are contractions. -/
theorem norm_pow_apply_le {S : Matrix (ZMod N) V ℝ →ₗ[ℝ] Matrix (ZMod N) V ℝ}
    (hS1 : ∀ F, ‖S F‖ ≤ ‖F‖) (n : ℕ) (F : Matrix (ZMod N) V ℝ) : ‖(S ^ n) F‖ ≤ ‖F‖ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_apply_eq_comp]; exact (hS1 _).trans ih

/-- **Time-uniform `ε`-rank bound for stable translation-invariant schemes.**  If `S` commutes with
the spatial shift and does not increase the Frobenius norm, and `F₀ = ∑_{k ∈ K} G_k` is a sum of
spatial modes below the Nyquist limit, then for every subset `K' ⊆ K` and every `n`,
`dist(Sⁿ F₀, M_{≤ budget K'}) ≤ (∑_{k ∈ K ∖ K'} ‖G_k‖²)^{1/2}`: the distance to low rank never
exceeds the spatial spectral tail of the initial data, at any time, with constant one.  See
OP-OT-61. -/
theorem distLR_pow_sum_le {S : Matrix (ZMod N) V ℝ →ₗ[ℝ] Matrix (ZMod N) V ℝ}
    (hS : IsTranslationInvariant S) (hS1 : ∀ F, ‖S F‖ ≤ ‖F‖) {K K' : Finset ℕ} (hK' : K' ⊆ K)
    (hN : ∀ k ∈ K, 2 * k < N) {G : ℕ → Matrix (ZMod N) V ℝ}
    (hG : ∀ k ∈ K, IsMode (modeAngle N k) (G k)) (n : ℕ) :
    distLR (modeBudget K') ((S ^ n) (∑ k ∈ K, G k)) ≤ √(∑ k ∈ K \ K', ‖G k‖ ^ 2) := by
  classical
  have hsplit : (S ^ n) (∑ k ∈ K, G k) =
      (S ^ n) (∑ k ∈ K', G k) + ∑ k ∈ K \ K', (S ^ n) (G k) := by
    rw [← map_sum, ← map_add, add_comm, Finset.sum_sdiff hK']
  have hZ : ((S ^ n) (∑ k ∈ K', G k)).rank ≤ modeBudget K' :=
    rank_pow_sum_le hS (fun k hk => hG k (hK' hk)) n
  refine (distLR_le_norm_sub hZ).trans ?_
  rw [hsplit, add_sub_cancel_left]
  have hmode : ∀ k ∈ K \ K', IsMode (modeAngle N k) ((S ^ n) (G k)) := fun k hk =>
    (hG k (Finset.mem_sdiff.mp hk).1).pow hS (isGridAngle_modeAngle k) n
  have horth : ∀ k ∈ K \ K', ∀ k' ∈ K \ K', k ≠ k' →
      ⟪(S ^ n) (G k), (S ^ n) (G k')⟫ = 0 := by
    intro k hk k' hk' hne
    obtain ⟨p, q, hpq⟩ := hmode k hk
    obtain ⟨p', q', hpq'⟩ := hmode k' hk'
    rw [hpq, hpq']
    exact inner_modeMat_eq_zero (hN k (Finset.mem_sdiff.mp hk).1)
      (hN k' (Finset.mem_sdiff.mp hk').1) hne p q p' q'
  have hsq : ‖∑ k ∈ K \ K', (S ^ n) (G k)‖ ^ 2 ≤ ∑ k ∈ K \ K', ‖G k‖ ^ 2 := by
    rw [norm_sq_sum_of_pairwise_orthogonal _ _ horth]
    exact Finset.sum_le_sum fun k _ =>
      pow_le_pow_left₀ (norm_nonneg _) (norm_pow_apply_le hS1 n (G k)) 2
  calc ‖∑ k ∈ K \ K', (S ^ n) (G k)‖ = √(‖∑ k ∈ K \ K', (S ^ n) (G k)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ √(∑ k ∈ K \ K', ‖G k‖ ^ 2) := Real.sqrt_le_sqrt hsq

/-- The `ε`-rank form of `distLR_pow_sum_le`. -/
theorem epsRank_pow_sum_le {S : Matrix (ZMod N) V ℝ →ₗ[ℝ] Matrix (ZMod N) V ℝ}
    (hS : IsTranslationInvariant S) (hS1 : ∀ F, ‖S F‖ ≤ ‖F‖) {K K' : Finset ℕ} (hK' : K' ⊆ K)
    (hN : ∀ k ∈ K, 2 * k < N) {G : ℕ → Matrix (ZMod N) V ℝ}
    (hG : ∀ k ∈ K, IsMode (modeAngle N k) (G k)) {ε : ℝ}
    (hε : √(∑ k ∈ K \ K', ‖G k‖ ^ 2) ≤ ε) (n : ℕ) :
    epsRank ε ((S ^ n) (∑ k ∈ K, G k)) ≤ modeBudget K' :=
  epsRank_le_of_distLR_le ((distLR_pow_sum_le hS hS1 hK' hN hG n).trans hε)

end Orthogonality

/-! ### Free streaming of a band-limited profile on a uniform velocity grid -/

section FreeStreaming

open Real

variable {N M : ℕ} [NeZero N]

/-- A real trigonometric polynomial of degree `≤ K`,
`g(x) = ∑_{k ≤ K} (a_k cos(k x) + b_k sin(k x))`; `b 0` plays no role. -/
noncomputable def trigPoly (K : ℕ) (a b : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (K + 1), (a k * cos (k * x) + b k * sin (k * x))

/-- The periodic spatial grid `x_i = 2π i / N`. -/
noncomputable def xGrid (N : ℕ) (i : ZMod N) : ℝ := 2 * π * i.val / N

/-- The uniform velocity grid `v_j = v₀ + j Δv`. -/
noncomputable def vGrid (v₀ Δv : ℝ) (j : Fin M) : ℝ := v₀ + j.val * Δv

/-- **The free-streaming solution on the grid**: `F(t)_{ij} = g(x_i - v_j t)`, the exact solution
of `∂_t f + v ∂_x f = 0` with data `f(0, x, v) = g(x)` (rank one), sampled on the grid. -/
noncomputable def freeStream (K : ℕ) (a b : ℕ → ℝ) (v₀ Δv t : ℝ) : Matrix (ZMod N) (Fin M) ℝ :=
  Matrix.of fun i j => trigPoly K a b (xGrid N i - vGrid v₀ Δv j * t)

/-- The velocity factor of the cosine part of mode `k` at time `t`. -/
noncomputable def pVec (k : ℕ) (a b : ℕ → ℝ) (v₀ Δv t : ℝ) : Fin M → ℝ := fun j =>
  a k * cos (k * (vGrid v₀ Δv j * t)) - b k * sin (k * (vGrid v₀ Δv j * t))

/-- The velocity factor of the sine part of mode `k` at time `t`. -/
noncomputable def qVec (k : ℕ) (a b : ℕ → ℝ) (v₀ Δv t : ℝ) : Fin M → ℝ := fun j =>
  a k * sin (k * (vGrid v₀ Δv j * t)) + b k * cos (k * (vGrid v₀ Δv j * t))

/-- **Free streaming is a sum of spatial modes with time-dependent velocity factors.** -/
theorem freeStream_eq_sum_modeMat (K : ℕ) (a b : ℕ → ℝ) (v₀ Δv t : ℝ) :
    (freeStream K a b v₀ Δv t : Matrix (ZMod N) (Fin M) ℝ) =
      ∑ k ∈ range (K + 1), modeMat (modeAngle N k) (pVec k a b v₀ Δv t) (qVec k a b v₀ Δv t) := by
  ext i j
  simp only [freeStream, Matrix.of_apply, trigPoly, Matrix.sum_apply, modeMat_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : (k : ℝ) * (xGrid N i - vGrid v₀ Δv j * t) =
      i.val * modeAngle N k - k * (vGrid v₀ Δv j * t) := by
    unfold xGrid modeAngle; ring
  rw [e, cos_sub, sin_sub]
  simp only [pVec, qVec]; ring

/-- **Upper bound: the rank of free streaming never exceeds `2K + 1`**, the number of real
spatial Fourier modes of the data, for every `t`, every velocity grid and every `N`. -/
theorem rank_freeStream_le (K : ℕ) (a b : ℕ → ℝ) (v₀ Δv t : ℝ) :
    (freeStream K a b v₀ Δv t : Matrix (ZMod N) (Fin M) ℝ).rank ≤ 2 * K + 1 := by
  rw [freeStream_eq_sum_modeMat, ← modeBudget_range K]
  refine (rank_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  split_ifs with h
  · subst h; rw [modeAngle_zero]; exact rank_modeMat_zero_le _ _
  · exact rank_modeMat_le _ _ _

/-- The weight of mode `k` in `‖F(t)‖²_F / (N M)`: `a_0²` for `k = 0`, `(a_k² + b_k²)/2` else. -/
noncomputable def modeWeight (a b : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then a 0 ^ 2 else (a k ^ 2 + b k ^ 2) / 2

theorem pVec_sq_add_qVec_sq (k : ℕ) (a b : ℕ → ℝ) (v₀ Δv t : ℝ) (j : Fin M) :
    pVec k a b v₀ Δv t j ^ 2 + qVec k a b v₀ Δv t j ^ 2 = a k ^ 2 + b k ^ 2 := by
  simp only [pVec, qVec]
  have := cos_sq_add_sin_sq (k * (vGrid v₀ Δv j * t))
  linear_combination (a k ^ 2 + b k ^ 2) * this

/-- The Frobenius norm of each mode of the free-streaming solution is **independent of time**. -/
theorem norm_sq_modeMat_freeStream {k : ℕ} (hk : 2 * k < N) (a b : ℕ → ℝ) (v₀ Δv t : ℝ) :
    ‖(modeMat (modeAngle N k) (pVec k a b v₀ Δv t) (qVec k a b v₀ Δv t) :
        Matrix (ZMod N) (Fin M) ℝ)‖ ^ 2 = N * M * modeWeight a b k := by
  unfold modeWeight
  split_ifs with h
  · subst h
    rw [modeAngle_zero, norm_sq_modeMat_zero]
    simp only [pVec, Nat.cast_zero, zero_mul, cos_zero, sin_zero, mul_one, mul_zero, sub_zero,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  · rw [norm_sq_modeMat (Nat.pos_of_ne_zero h) hk, ← Finset.sum_add_distrib]
    simp_rw [pVec_sq_add_qVec_sq]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

/-- **The spectral tail of free streaming is exactly time independent.**  For `2K < N` and any
set `K'` of retained modes, `‖F(t) - F_{K'}(t)‖²_F = N M ∑_{k ∉ K'} w_k` for all `t`, where
`F_{K'}(t)` is the sum of the retained modes (rank `≤ budget K'`). -/
theorem norm_sq_freeStream_sub (hN : 2 * K < N) (a b : ℕ → ℝ) (v₀ Δv t : ℝ) {K' : Finset ℕ}
    (hK' : K' ⊆ range (K + 1)) :
    ‖(freeStream K a b v₀ Δv t : Matrix (ZMod N) (Fin M) ℝ) -
        ∑ k ∈ K', modeMat (modeAngle N k) (pVec k a b v₀ Δv t) (qVec k a b v₀ Δv t)‖ ^ 2 =
      N * M * ∑ k ∈ range (K + 1) \ K', modeWeight a b k := by
  classical
  have hlt : ∀ k ∈ range (K + 1), 2 * k < N := fun k hk => by
    rw [Finset.mem_range] at hk; omega
  rw [freeStream_eq_sum_modeMat, ← Finset.sum_sdiff hK', add_sub_cancel_right,
    norm_sq_sum_of_pairwise_orthogonal, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun k hk => ?_
    exact norm_sq_modeMat_freeStream (hlt k (Finset.mem_sdiff.mp hk).1) a b v₀ Δv t
  · intro k hk k' hk' hne
    exact inner_modeMat_eq_zero (hlt k (Finset.mem_sdiff.mp hk).1)
      (hlt k' (Finset.mem_sdiff.mp hk').1) hne _ _ _ _

/-- **Time-uniform `ε`-rank bound for free streaming.**  For all `t`,
`dist(F(t), M_{≤ budget K'}) ≤ (N M ∑_{k ∉ K'} w_k)^{1/2}`: free streaming of a profile with
`2K + 1` real Fourier modes is `ε`-close to rank `2|K'|` forever as soon as the spectral tail of
the data outside `K'` is below `ε`.  Filamentation in `v` costs no rank. -/
theorem distLR_freeStream_le (hN : 2 * K < N) (a b : ℕ → ℝ) (v₀ Δv t : ℝ) {K' : Finset ℕ}
    (hK' : K' ⊆ range (K + 1)) :
    distLR (modeBudget K') (freeStream K a b v₀ Δv t : Matrix (ZMod N) (Fin M) ℝ) ≤
      √(N * M * ∑ k ∈ range (K + 1) \ K', modeWeight a b k) := by
  have hZ : (∑ k ∈ K', modeMat (modeAngle N k) (pVec k a b v₀ Δv t) (qVec k a b v₀ Δv t) :
      Matrix (ZMod N) (Fin M) ℝ).rank ≤ modeBudget K' := by
    refine (rank_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    split_ifs with h
    · subst h; rw [modeAngle_zero]; exact rank_modeMat_zero_le _ _
    · exact rank_modeMat_le _ _ _
  refine (distLR_le_norm_sub hZ).trans ?_
  rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_freeStream_sub hN a b v₀ Δv t hK']

theorem epsRank_freeStream_le (hN : 2 * K < N) (a b : ℕ → ℝ) (v₀ Δv t : ℝ) {K' : Finset ℕ}
    (hK' : K' ⊆ range (K + 1)) {ε : ℝ}
    (hε : √(N * M * ∑ k ∈ range (K + 1) \ K', modeWeight a b k) ≤ ε) :
    epsRank ε (freeStream K a b v₀ Δv t : Matrix (ZMod N) (Fin M) ℝ) ≤ modeBudget K' :=
  epsRank_le_of_distLR_le ((distLR_freeStream_le hN a b v₀ Δv t hK').trans hε)

/-- **Recurrence.**  When `t Δv ∈ 2π ℤ` (in particular at the recurrence time `T_R = 2π / Δv`),
the discrete free-streaming solution is the translated profile `g(x_i - v₀ t)` for every `j`:
rank one again. -/
theorem freeStream_recurrence (K : ℕ) (a b : ℕ → ℝ) (v₀ Δv t : ℝ) {p : ℤ}
    (h : t * Δv = p * (2 * π)) :
    (freeStream K a b v₀ Δv t : Matrix (ZMod N) (Fin M) ℝ) =
      Matrix.vecMulVec (fun i => trigPoly K a b (xGrid N i - v₀ * t)) (fun _ => 1) := by
  ext i j
  simp only [freeStream, Matrix.of_apply, Matrix.vecMulVec_apply, mul_one, trigPoly]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : (k : ℝ) * (xGrid N i - vGrid v₀ Δv j * t) =
      k * (xGrid N i - v₀ * t) - ((k * j.val * p : ℤ) : ℝ) * (2 * π) := by
    unfold vGrid; push_cast
    linear_combination (-(k : ℝ) * j.val) * h
  rw [e, cos_sub_int_mul_two_pi, sin_sub_int_mul_two_pi]

theorem rank_freeStream_recurrence (K : ℕ) (a b : ℕ → ℝ) (v₀ Δv t : ℝ) {p : ℤ}
    (h : t * Δv = p * (2 * π)) :
    (freeStream K a b v₀ Δv t : Matrix (ZMod N) (Fin M) ℝ).rank ≤ 1 := by
  rw [freeStream_recurrence K a b v₀ Δv t h]; exact Matrix.rank_vecMulVec_le _ _

end FreeStreaming

/-! ### Shear times: the lower bound, and the exact rank -/

section Shear

open Real

variable {N M K : ℕ} [NeZero N]

/-- The **shear condition** at time `t`: `t Δv = 2π p / M` with `M ∤ m p` for `0 < m ≤ 2K`.  It
holds for `p` coprime to `M` when `2K < M` (`shear_condition_of_coprime`); the first such time is
`t₁ = 2π / (M Δv)`, the time at which the fastest and the slowest particles have separated by one
period. -/
def ShearCondition (M K : ℕ) (p : ℤ) : Prop := ∀ m : ℤ, 0 < m → m ≤ 2 * K → ¬ (M : ℤ) ∣ m * p

theorem shear_condition_of_coprime {p : ℤ} (hpM : Int.gcd (M : ℤ) p = 1) (hKM : 2 * K < M) :
    ShearCondition M K p := by
  intro m hm1 hm2 h
  have h1 := Int.dvd_of_dvd_mul_left_of_gcd_one h hpM
  have h2 := Int.le_of_dvd hm1 h1
  omega

/-- The first shear time `t₁ = 2π / (M Δv)`, `p = 1`, satisfies the shear condition as soon as
`2K < M`. -/
theorem shear_condition_one (hKM : 2 * K < M) : ShearCondition M K 1 :=
  shear_condition_of_coprime (by simp) hKM

/-- Along the uniform velocity grid at a time with `t Δv = 2π p / M`, the phase of mode `k` is an
arithmetic progression with step `2π k p / M`. -/
theorem mul_vGrid_mul (k : ℕ) (v₀ Δv t : ℝ) {p : ℤ} (ht : t * Δv = 2 * π * p / M)
    (j : Fin M) :
    (k : ℝ) * (vGrid v₀ Δv j * t) = k * v₀ * t + j.val * (2 * π * (((k : ℤ) * p : ℤ) : ℝ) / M) := by
  unfold vGrid; push_cast
  linear_combination ((k : ℝ) * j.val) * ht

theorem not_dvd_mul_of_shear (hp : ShearCondition M K p) {m : ℤ} (hm0 : m ≠ 0) (hm : |m| ≤ 2 * K) :
    ¬ (M : ℤ) ∣ m * p := by
  rcases lt_or_gt_of_ne hm0 with h | h
  · intro hd
    have : (M : ℤ) ∣ (-m) * p := by rw [neg_mul]; exact (dvd_neg).mpr hd
    exact hp (-m) (by omega) (by rw [abs_of_neg h] at hm; exact hm) this
  · exact hp m h (by rw [abs_of_pos h] at hm; exact hm)

/-- **Velocity factors of distinct modes are orthogonal at shear times.** -/
theorem sum_vwave_mul_eq_zero (v₀ Δv t : ℝ) {p : ℤ} (ht : t * Δv = 2 * π * p / M)
    (hp : ShearCondition M K p) {k k' : ℕ} (hk : k ≤ K) (hk' : k' ≤ K) (hne : k ≠ k')
    (A B A' B' : ℝ) :
    ∑ j : Fin M, (A * cos (k * (vGrid v₀ Δv j * t)) + B * sin (k * (vGrid v₀ Δv j * t))) *
      (A' * cos (k' * (vGrid v₀ Δv j * t)) + B' * sin (k' * (vGrid v₀ Δv j * t))) = 0 := by
  simp_rw [mul_vGrid_mul _ v₀ Δv t ht]
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ =>
    (A * cos (k * v₀ * t + n * (2 * π * (((k : ℤ) * p : ℤ) : ℝ) / M)) +
      B * sin (k * v₀ * t + n * (2 * π * (((k : ℤ) * p : ℤ) : ℝ) / M))) *
    (A' * cos (k' * v₀ * t + n * (2 * π * (((k' : ℤ) * p : ℤ) : ℝ) / M)) +
      B' * sin (k' * v₀ * t + n * (2 * π * (((k' : ℤ) * p : ℤ) : ℝ) / M)))) M]
  rw [sum_wave_mul_wave]
  have e1 : 2 * π * (((k : ℤ) * p : ℤ) : ℝ) / M - 2 * π * (((k' : ℤ) * p : ℤ) : ℝ) / M =
      2 * π * ((((k : ℤ) - k') * p : ℤ) : ℝ) / M := by push_cast; ring
  have e2 : 2 * π * (((k : ℤ) * p : ℤ) : ℝ) / M + 2 * π * (((k' : ℤ) * p : ℤ) : ℝ) / M =
      2 * π * ((((k : ℤ) + k') * p : ℤ) : ℝ) / M := by push_cast; ring
  rw [e1, e2]
  have h1 := sum_cos_sin_grid_eq_zero (M := M) (q := M) dvd_rfl
    (not_dvd_mul_of_shear hp (m := (k : ℤ) - k') (by omega)
      (by rw [abs_le]; constructor <;> omega)) (k * v₀ * t - k' * v₀ * t)
  have h2 := sum_cos_sin_grid_eq_zero (M := M) (q := M) dvd_rfl
    (not_dvd_mul_of_shear hp (m := (k : ℤ) + k') (by omega)
      (by rw [abs_le]; constructor <;> omega)) (k * v₀ * t + k' * v₀ * t)
  rw [h1.1, h1.2, h2.1, h2.2]; ring

/-- **The Gram matrix of the velocity factors of one mode at a shear time.** -/
theorem sum_vwave_mul_same (v₀ Δv t : ℝ) {p : ℤ} (ht : t * Δv = 2 * π * p / M)
    (hp : ShearCondition M K p) {k : ℕ} (hk0 : 0 < k) (hk : k ≤ K) (A B A' B' : ℝ) :
    ∑ j : Fin M, (A * cos (k * (vGrid v₀ Δv j * t)) + B * sin (k * (vGrid v₀ Δv j * t))) *
      (A' * cos (k * (vGrid v₀ Δv j * t)) + B' * sin (k * (vGrid v₀ Δv j * t))) =
      M * (A * A' + B * B') / 2 := by
  simp_rw [mul_vGrid_mul _ v₀ Δv t ht]
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ =>
    (A * cos (k * v₀ * t + n * (2 * π * (((k : ℤ) * p : ℤ) : ℝ) / M)) +
      B * sin (k * v₀ * t + n * (2 * π * (((k : ℤ) * p : ℤ) : ℝ) / M))) *
    (A' * cos (k * v₀ * t + n * (2 * π * (((k : ℤ) * p : ℤ) : ℝ) / M)) +
      B' * sin (k * v₀ * t + n * (2 * π * (((k : ℤ) * p : ℤ) : ℝ) / M)))) M]
  rw [sum_wave_mul_wave, sub_self, sub_self]
  have e2 : 2 * π * (((k : ℤ) * p : ℤ) : ℝ) / M + 2 * π * (((k : ℤ) * p : ℤ) : ℝ) / M =
      2 * π * ((((k : ℤ) + k) * p : ℤ) : ℝ) / M := by push_cast; ring
  rw [e2]
  have h2 := sum_cos_sin_grid_eq_zero (M := M) (q := M) dvd_rfl
    (not_dvd_mul_of_shear hp (m := (k : ℤ) + k) (by omega)
      (by rw [abs_le]; constructor <;> omega)) (k * v₀ * t + k * v₀ * t)
  rw [h2.1, h2.2]
  simp only [mul_zero, add_zero, cos_zero, sin_zero, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one]
  ring

/-- The rank-one terms of free streaming are indexed by a mode `k ≤ K` and a cosine/sine flag. -/
abbrev TermIdx (K : ℕ) := Fin (K + 1) × Bool

/-- The spatial factor of a term: `cos(i θ_k)` or `sin(i θ_k)`. -/
noncomputable def uVec (N K : ℕ) (l : TermIdx K) : ZMod N → ℝ := fun i =>
  if l.2 then cos (i.val * modeAngle N l.1) else sin (i.val * modeAngle N l.1)

/-- The velocity factor of a term: `pVec k` or `qVec k`. -/
noncomputable def wVec (M K : ℕ) (a b : ℕ → ℝ) (v₀ Δv t : ℝ) (l : TermIdx K) : Fin M → ℝ :=
  if l.2 then pVec l.1 a b v₀ Δv t else qVec l.1 a b v₀ Δv t

/-- The squared singular value of a term at a shear time: `N M a_0²` for the isotropic term,
`N M (a_k² + b_k²) / 4` for each of the two terms of mode `k ≥ 1`. -/
noncomputable def termSq (N M : ℕ) (a b : ℕ → ℝ) (l : TermIdx K) : ℝ :=
  if (l.1 : ℕ) = 0 then (if l.2 then N * M * a 0 ^ 2 else 0)
  else N * M * (a l.1 ^ 2 + b l.1 ^ 2) / 4

theorem freeStream_eq_sum_terms (K : ℕ) (a b : ℕ → ℝ) (v₀ Δv t : ℝ) :
    (freeStream K a b v₀ Δv t : Matrix (ZMod N) (Fin M) ℝ) =
      ∑ l : TermIdx K, Matrix.vecMulVec (uVec N K l) (wVec M K a b v₀ Δv t l) := by
  rw [freeStream_eq_sum_modeMat, Fintype.sum_prod_type, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_bool, modeMat_eq_add]
  congr 1

/-- Wave coefficients of the spatial factors. -/
def cA (l : TermIdx K) : ℝ := if l.2 then 1 else 0
def cB (l : TermIdx K) : ℝ := if l.2 then 0 else 1

theorem uVec_apply (l : TermIdx K) (i : ZMod N) :
    uVec N K l i = cA l * cos (i.val * modeAngle N l.1) + cB l * sin (i.val * modeAngle N l.1) := by
  obtain ⟨k, b⟩ := l; cases b <;> simp [uVec, cA, cB]

theorem cA_mul_cA_add (l : TermIdx K) : cA l * cA l + cB l * cB l = 1 := by
  obtain ⟨k, b⟩ := l; cases b <;> simp [cA, cB]

theorem cA_mul_cA_add_of_ne (l l' : TermIdx K) (h : l.2 ≠ l'.2) :
    cA l * cA l' + cB l * cB l' = 0 := by
  obtain ⟨k, b⟩ := l; obtain ⟨k', b'⟩ := l'; cases b <;> cases b' <;> simp_all [cA, cB]

theorem cA_mul_cA_of_ne (l l' : TermIdx K) (h : l.2 ≠ l'.2) : cA l * cA l' = 0 := by
  obtain ⟨k, b⟩ := l; obtain ⟨k', b'⟩ := l'; cases b <;> cases b' <;> simp_all [cA]

/-- Wave coefficients of the velocity factors. -/
noncomputable def dA (a b : ℕ → ℝ) (l : TermIdx K) : ℝ := if l.2 then a l.1 else b l.1
noncomputable def dB (a b : ℕ → ℝ) (l : TermIdx K) : ℝ := if l.2 then -b l.1 else a l.1

theorem wVec_apply (a b : ℕ → ℝ) (v₀ Δv t : ℝ) (l : TermIdx K) (j : Fin M) :
    wVec M K a b v₀ Δv t l j = dA a b l * cos (l.1 * (vGrid v₀ Δv j * t)) +
      dB a b l * sin (l.1 * (vGrid v₀ Δv j * t)) := by
  obtain ⟨k, b'⟩ := l; cases b' <;> simp [wVec, dA, dB, pVec, qVec] <;> ring

theorem dA_mul_dA_add (a b : ℕ → ℝ) (l : TermIdx K) :
    dA a b l * dA a b l + dB a b l * dB a b l = a l.1 ^ 2 + b l.1 ^ 2 := by
  obtain ⟨k, b'⟩ := l; cases b' <;> simp [dA, dB] <;> ring

theorem dA_mul_dA_add_of_ne (a b : ℕ → ℝ) (l l' : TermIdx K) (hk : (l.1 : ℕ) = l'.1)
    (h : l.2 ≠ l'.2) : dA a b l * dA a b l' + dB a b l * dB a b l' = 0 := by
  obtain ⟨k, b₁⟩ := l; obtain ⟨k', b₂⟩ := l'
  simp only at hk h
  cases b₁ <;> cases b₂ <;> simp_all [dA, dB] <;> ring

theorem dA_mul_dA_of_zero (a b : ℕ → ℝ) (hb0 : b 0 = 0) (l l' : TermIdx K)
    (hk : (l.1 : ℕ) = 0) (hk' : (l'.1 : ℕ) = 0) (h : l.2 ≠ l'.2) : dA a b l * dA a b l' = 0 := by
  obtain ⟨k, b₁⟩ := l; obtain ⟨k', b₂⟩ := l'
  simp only at hk hk' h
  cases b₁ <;> cases b₂ <;> simp_all [dA]

/-- The spatial factors are pairwise orthogonal for `2K < N`. -/
theorem uVec_orthogonal (hN : 2 * K < N) (l l' : TermIdx K) (hne : l ≠ l') :
    ∑ i, uVec N K l i * uVec N K l' i = 0 := by
  have hl : 2 * (l.1 : ℕ) < N := by have := l.1.isLt; omega
  have hl' : 2 * (l'.1 : ℕ) < N := by have := l'.1.isLt; omega
  rw [sum_zmod_val' _ (fun n : ℕ =>
    (cA l * cos (n * modeAngle N l.1) + cB l * sin (n * modeAngle N l.1)) *
    (cA l' * cos (n * modeAngle N l'.1) + cB l' * sin (n * modeAngle N l'.1)))
    (fun i => by rw [uVec_apply, uVec_apply])]
  by_cases hk : (l.1 : ℕ) = l'.1
  · have hb : l.2 ≠ l'.2 := fun h => hne (Prod.ext (Fin.ext hk) h)
    rw [hk]
    by_cases hk0 : (l'.1 : ℕ) = 0
    · rw [hk0, modeAngle_zero]
      simp only [mul_zero, cos_zero, sin_zero, mul_one, add_zero, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, cA_mul_cA_of_ne l l' hb]
    · rw [sum_xwave_mul_same (Nat.pos_of_ne_zero hk0) hl', cA_mul_cA_add_of_ne l l' hb]; ring
  · exact sum_xwave_mul_eq_zero hl hl' hk _ _ _ _

/-- The velocity factors are pairwise orthogonal at shear times (with `b 0 = 0`). -/
theorem wVec_orthogonal (a b : ℕ → ℝ) (hb0 : b 0 = 0) (v₀ Δv t : ℝ) {p : ℤ}
    (ht : t * Δv = 2 * π * p / M) (hp : ShearCondition M K p) (l l' : TermIdx K) (hne : l ≠ l') :
    ∑ j, wVec M K a b v₀ Δv t l j * wVec M K a b v₀ Δv t l' j = 0 := by
  have hl : (l.1 : ℕ) ≤ K := by have := l.1.isLt; omega
  have hl' : (l'.1 : ℕ) ≤ K := by have := l'.1.isLt; omega
  simp_rw [wVec_apply]
  by_cases hk : (l.1 : ℕ) = l'.1
  · have hb : l.2 ≠ l'.2 := fun h => hne (Prod.ext (Fin.ext hk) h)
    rw [hk]
    by_cases hk0 : (l'.1 : ℕ) = 0
    · rw [hk0]
      simp only [Nat.cast_zero, zero_mul, cos_zero, sin_zero, mul_one, mul_zero, add_zero,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        dA_mul_dA_of_zero a b hb0 l l' (hk.trans hk0) hk0 hb]
    · rw [sum_vwave_mul_same v₀ Δv t ht hp (Nat.pos_of_ne_zero hk0) hl',
        dA_mul_dA_add_of_ne a b l l' hk hb]; ring
  · exact sum_vwave_mul_eq_zero v₀ Δv t ht hp hl hl' hk _ _ _ _

/-- The product of the squared norms of the two factors of a term is `termSq`. -/
theorem uVec_wVec_sq (hN : 2 * K < N) (a b : ℕ → ℝ) (v₀ Δv t : ℝ) {p : ℤ}
    (ht : t * Δv = 2 * π * p / M) (hp : ShearCondition M K p) (l : TermIdx K) :
    (∑ i, uVec N K l i ^ 2) * ∑ j, wVec M K a b v₀ Δv t l j ^ 2 = termSq N M a b l := by
  have hl : 2 * (l.1 : ℕ) < N := by have := l.1.isLt; omega
  have hlK : (l.1 : ℕ) ≤ K := by have := l.1.isLt; omega
  rw [sum_zmod_val' _ (fun n : ℕ =>
    (cA l * cos (n * modeAngle N l.1) + cB l * sin (n * modeAngle N l.1)) *
    (cA l * cos (n * modeAngle N l.1) + cB l * sin (n * modeAngle N l.1)))
    (fun i => by rw [sq, uVec_apply])]
  simp_rw [wVec_apply, sq]
  unfold termSq
  by_cases hk0 : (l.1 : ℕ) = 0
  · simp only [hk0, ↓reduceIte, modeAngle_zero]
    simp only [mul_zero, cos_zero, sin_zero, mul_one, add_zero, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, Nat.cast_zero, zero_mul, Finset.card_univ,
      Fintype.card_fin]
    obtain ⟨k, b'⟩ := l
    simp only at hk0
    (cases b' <;> simp [cA, dA, hk0]); ring
  · simp only [hk0, ↓reduceIte]
    rw [sum_xwave_mul_same (Nat.pos_of_ne_zero hk0) hl,
      sum_vwave_mul_same v₀ Δv t ht hp (Nat.pos_of_ne_zero hk0) hlK, cA_mul_cA_add,
      dA_mul_dA_add]
    ring

/-- **Lower bound at shear times.**  At a time with `t Δv = 2π p / M` satisfying the shear
condition, and for `2K < N`, the free-streaming matrix is a sum of `2K + 1` rank-one terms with
pairwise orthogonal spatial factors and pairwise orthogonal velocity factors: a singular value
decomposition with singular values `√(termSq l)`, namely `√(N M) |a_0|` and, twice each,
`√(N M) (a_k² + b_k²)^{1/2} / 2` for `1 ≤ k ≤ K`.  Hence for any set `s` of terms with `|s| > r`
and `c² ≤ termSq l` on `s`, `dist(F(t), M_{≤ r}) ≥ c`: the time-uniform upper bound
`distLR_freeStream_le` is attained, and no rank below the number of spatial modes above the
tolerance suffices.  See OP-OT-61. -/
theorem le_distLR_freeStream_shear (hN : 2 * K < N) (a b : ℕ → ℝ) (hb0 : b 0 = 0)
    (v₀ Δv t : ℝ) {p : ℤ} (ht : t * Δv = 2 * π * p / M) (hp : ShearCondition M K p)
    (s : Finset (TermIdx K)) {c : ℝ} (hc : 0 ≤ c) (hcs : ∀ l ∈ s, c ^ 2 ≤ termSq N M a b l)
    {r : ℕ} (hr : r < s.card) :
    c ≤ distLR r (freeStream K a b v₀ Δv t : Matrix (ZMod N) (Fin M) ℝ) := by
  rw [freeStream_eq_sum_terms]
  refine le_distLR_sum_vecMulVec s _ _ (uVec_orthogonal hN) (wVec_orthogonal a b hb0 v₀ Δv t ht hp)
    hc (fun l hl => ?_) hr
  rw [uVec_wVec_sq hN a b v₀ Δv t ht hp l]; exact hcs l hl

/-- The `ε`-rank at a shear time exceeds the number of terms whose singular value exceeds `ε`. -/
theorem lt_epsRank_freeStream_shear (hN : 2 * K < N) (a b : ℕ → ℝ) (hb0 : b 0 = 0)
    (v₀ Δv t : ℝ) {p : ℤ} (ht : t * Δv = 2 * π * p / M) (hp : ShearCondition M K p)
    (s : Finset (TermIdx K)) {ε : ℝ} (hε : 0 ≤ ε) (hs : ∀ l ∈ s, ε ^ 2 < termSq N M a b l)
    {r : ℕ} (hr : r < s.card) :
    r < epsRank ε (freeStream K a b v₀ Δv t : Matrix (ZMod N) (Fin M) ℝ) := by
  classical
  by_contra h
  push Not at h
  have h1 := (epsRank_le_iff hε).mp h
  -- choose `c` strictly between `ε` and the smallest singular value on `s`
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨l₀, hl₀, hmin⟩ := Finset.exists_min_image s (termSq N M a b) hne
  have hε2 : ε ^ 2 < termSq N M a b l₀ := hs l₀ hl₀
  set c := √(termSq N M a b l₀) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hcsq : c ^ 2 = termSq N M a b l₀ := Real.sq_sqrt (by linarith [sq_nonneg ε])
  have h2 : c ≤ distLR r (freeStream K a b v₀ Δv t : Matrix (ZMod N) (Fin M) ℝ) :=
    le_distLR_freeStream_shear hN a b hb0 v₀ Δv t ht hp s hc0
      (fun l hl => by rw [hcsq]; exact hmin l hl) hr
  have h3 : ε < c := by
    rw [hc]; exact Real.lt_sqrt_of_sq_lt hε2
  linarith

/-- The set of nonzero terms: every term except the sine part of the isotropic mode. -/
def activeTerms (K : ℕ) : Finset (TermIdx K) := Finset.univ.erase (0, false)

theorem card_activeTerms (K : ℕ) : (activeTerms K).card = 2 * K + 1 := by
  rw [activeTerms, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  omega

/-- **The rank bound is attained.**  If every mode `0 ≤ k ≤ K` of the data is present
(`a_0 ≠ 0`, `(a_k, b_k) ≠ 0`), the free-streaming matrix has rank exactly `2K + 1` at every
shear time: the rank-one data `g ⊗ 1` has reached the maximal rank allowed by its spatial
bandwidth. -/
theorem rank_freeStream_shear (hN : 2 * K < N) (a b : ℕ → ℝ) (hb0 : b 0 = 0)
    (ha0 : a 0 ≠ 0) (hab : ∀ k, 0 < k → k ≤ K → 0 < a k ^ 2 + b k ^ 2)
    (v₀ Δv t : ℝ) {p : ℤ} (ht : t * Δv = 2 * π * p / M) (hp : ShearCondition M K p)
    (hM : 0 < M) :
    (freeStream K a b v₀ Δv t : Matrix (ZMod N) (Fin M) ℝ).rank = 2 * K + 1 := by
  classical
  refine le_antisymm (rank_freeStream_le K a b v₀ Δv t) ?_
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hpos : ∀ l ∈ activeTerms K, 0 < termSq N M a b l := by
    intro l hl
    simp only [activeTerms, Finset.mem_erase, Finset.mem_univ, and_true] at hl
    simp only [termSq]
    split_ifs with h1 h2
    · positivity
    · exact absurd (Prod.ext (Fin.ext h1) (by simpa using h2)) hl
    · have := hab l.1 (Nat.pos_of_ne_zero h1) (by have := l.1.isLt; omega)
      positivity
  have h := lt_epsRank_freeStream_shear hN a b hb0 v₀ Δv t ht hp (activeTerms K) le_rfl
    (fun l hl => by simpa using hpos l hl) (r := 2 * K) (by rw [card_activeTerms]; omega)
  rw [epsRank_zero] at h
  exact h

end Shear

end LeanDLRA.Novel.OpOT61
