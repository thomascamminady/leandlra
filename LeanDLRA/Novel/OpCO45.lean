import Mathlib
import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Classical.SVD
import LeanDLRA.Matrix.Frobenius

/-!
# High-order positivity-preserving and TVD/TVB low-rank methods

Open problem OP-CO-45 of `docs/survey/open-problems.json`.  The
survey entry says that no low-order positivity-preserving low-rank scheme exists to limit towards,
that truncation destroys monotonicity, and proposes as base scheme step-and-truncate forward Euler
followed by the convex positivity projection, with SSP-RK combinations on top.  This file makes
those statements precise, shows where each is right and where it can be repaired, and proves the
following. In the sections on schemes `‖·‖` is the maximum-entry norm (a local instance).

## Barriers at fixed rank

* `no_monotone_retraction`: for `1 ≤ r < min (m, n)` no map into rank `≤ r` that fixes the
  nonnegative matrices of rank `≤ r` is order preserving.  This holds for all compressions, not only
  the SVD.
* `barrier_rank_lower`, `barrier_rank_approx`, `barrier_sharp`: for `A_t = !![1,1,0; 0,1,t; t,0,0] ⊕
  1` of size `r + 1`, `r ≥ 2`, the entrywise distance to rank `≤ r` is at most `t²`, while the
  distance to *nonnegative* rank `≤ r` matrices lies between `t / (64 r)` and `t`.  So exact
  positivity at fixed rank can cost a square root of the approximation error, and no
  quasi-optimality constant exists.
* `no_consistent_nonneg_lowRank`: consequently, for an explicit monotone conservative generator
  (`gen`: upwind transport plus scattering in one cell) and an explicit nonnegative `X₀` of rank `r`
  with vacuum, *no* family of nonnegative matrices of rank `≤ r` satisfies `G h = X₀ + h gen X₀ +
  o(h)`, of any order, however it is computed.  Without the sign constraint such a family exists
  (`exists_consistent_lowRank`).  This is the precise content of "no low-order positivity-preserving
  low-rank scheme exists": it is true at fixed rank `r ≥ 2`, at vacuum.
* `truncation_has_negative_entry`: the SVD truncation of `A_t` has a negative entry.
* `positivePart_rank`: the convex positivity projection of a rank-two matrix can have rank `n - 1`,
  so the candidate base scheme of the survey entry is positive but not low rank.
* `exists_nonneg_rankOne_closer`: at `r = 1` nothing is lost, in every monotone norm.

## One extra rank removes the barrier

* `exists_nonneg_rank_succ`: if `A ≥ 0` is within `d` of rank `≤ r`, it is within `2 d` of a
  nonnegative matrix of rank `≤ r + 1`.  The constant reference matrix is the low-rank state to
  limit towards.
* `limiter_spec`, `tvStage_spec`: a scaling limiter about the mean returns `c + θ Z`, keeps every
  band `[a, b]`, the mean, and (second stage) any seminorm budget, at a perturbation proportional to
  the truncation error.
* `limited_scheme_aposteriori`, `kinetic_limited_scheme`: for every monotone scheme, in particular
  SSP Runge-Kutta for the upwind discretization of a linear kinetic equation with heterogeneous
  isotropic scattering: exact positivity, mass conservation, rank `≤ r + 2`, and distance to the
  full solution at most `K` times the *sum* of the truncation errors, with no assumption on the
  solution.
* `limited_scheme`, `limited_scheme_tv`: order `p` against a reference sequence
  `Y (n+1) = G n Y n H n`, with the quasi-optimality constants entering only in `exp (K Ks T)`.
* `advection_second_order`, `advection_tvd`: unconditional instances for two-dimensional periodic
  upwind advection: rank `≤ r + 2`, exact band and mass, for `advection_tvd` also exactly
  nonincreasing periodic total variation, and `O(h²)` distance from the full SSP solution for
  arbitrary, also discontinuous, data with fluctuation of rank `≤ r`.

## What is not proved

* `limited_scheme` needs the comparison matrices `G n, H n`.  They hide `1 / σ_r` for non-Sylvester
  dynamics such as free streaming; only the Sylvester case is an unconditional instance.
* Order means order in `h` at a fixed spatial mesh.  The constants grow as the mesh is refined, the
  total-variation stage by a factor `m n`.  A linear monotone `Φ` stays subject to Godunov's
  barrier.
* Smallness of the truncation errors of `kinetic_limited_scheme` is not derived.
* Numerics (not part of the proofs): `dist(A_t, nonnegative rank 2) ≈ t / 3`; second order on smooth
  low-rank data touching vacuum with the limiter inactive; for under-resolved discontinuities the
  scaling limiter is global, hence diffusive (total scaling `≈ 0.5` at rank `4`, `0.996` at rank
  `16` on a box initial value), while the positive part has essentially full rank.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Novel.OpCO45

open Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

section Basics

variable {ι κ : Type*}

/-- Entrywise nonnegativity. -/
def IsNonneg (X : Matrix ι κ ℝ) : Prop := ∀ i j, 0 ≤ X i j

/-- A matrix with injective `mulVec` has rank equal to its number of columns. -/
lemma rank_eq_card_of_inj [Fintype κ] {B : Matrix ι κ ℝ}
    (h : ∀ w : κ → ℝ, B *ᵥ w = 0 → w = 0) : B.rank = Fintype.card κ := by
  classical
  have hinj : Function.Injective B.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    exact h w (by simpa using hw)
  rw [Matrix.rank, LinearMap.finrank_range_of_inj hinj]
  simp

/-- **Rank one is free of charge.**  If `A ≥ 0` and `rank B ≤ 1` then the entrywise modulus `|B|` is
nonnegative, has rank `≤ 1` and is entrywise at least as close to `A` as `B` is.  Hence for `r = 1`
the nonnegativity constraint costs nothing, in every monotone norm, which is the barrier-free case:
it is the elementary form of the Perron-Frobenius fact that a nonnegative matrix has a nonnegative
best rank-one approximation. -/
theorem exists_nonneg_rankOne_closer [Finite ι] [Fintype κ] {A B : Matrix ι κ ℝ} (hA : IsNonneg A)
    (hB : B.rank ≤ 1) :
    ∃ B' : Matrix ι κ ℝ, IsNonneg B' ∧ B'.rank ≤ 1 ∧
      ∀ i j, |A i j - B' i j| ≤ |A i j - B i j| := by
  classical
  have := Fintype.ofFinite ι
  refine ⟨fun i j => |B i j|, fun i j => abs_nonneg _, ?_, fun i j => ?_⟩
  · obtain h0 | h1 : B.rank = 0 ∨ B.rank = 1 := by omega
    · obtain ⟨U, S, V, -, -, -, hX⟩ := (LeanDLRA.SVD.rank_eq_iff_exists_factor B).mp h0
      have hzero : B = 0 := by
        rw [hX]
        ext i j
        simp [Matrix.mul_apply]
      subst hzero
      simp only [Matrix.zero_apply, abs_zero]
      have : (fun (_ : ι) (_ : κ) => (0 : ℝ)) = (0 : Matrix ι κ ℝ) := rfl
      rw [this, Matrix.rank_zero]
      omega
    · obtain ⟨U, S, V, -, -, -, hX⟩ := (LeanDLRA.SVD.rank_eq_iff_exists_factor B).mp h1
      have hent : ∀ i j, B i j = U i 0 * S 0 0 * V j 0 := by
        intro i j
        rw [hX]
        simp [Matrix.mul_apply]
      have : (fun i j => |B i j|) =
          Matrix.vecMulVec (fun i => |U i 0 * S 0 0|) (fun j => |V j 0|) := by
        ext i j
        simp [Matrix.vecMulVec_apply, hent, abs_mul]
      rw [this]
      exact Matrix.rank_vecMulVec_le _ _
  · have h := abs_abs_sub_abs_le_abs_sub (A i j) (B i j)
    rwa [abs_of_nonneg (hA i j)] at h

/-- **The convex positivity projection does not stay low rank.**  For every `m` there is a matrix
`Y ∈ ℝ^{(m+1) × (m+1)}` of rank at most `2`, namely `Y i j = i - j`, whose entrywise positive part
has rank at least `m`.  The positive part is the metric projection onto the nonnegative cone used in
the candidate scheme of OP-CO-45; this is why `limiter` scales instead of clipping. -/
theorem positivePart_rank (m : ℕ) :
    ∃ Y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ, Y.rank ≤ 2 ∧
      m ≤ (Y.map fun x => max x 0).rank := by
  classical
  set Y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := fun i j => ((i : ℕ) : ℝ) - ((j : ℕ) : ℝ) with hY
  refine ⟨Y, ?_, ?_⟩
  · have hdec : Y = Matrix.vecMulVec (fun i : Fin (m + 1) => ((i : ℕ) : ℝ)) (fun _ => 1) +
        Matrix.vecMulVec (fun _ => 1) (fun j : Fin (m + 1) => -((j : ℕ) : ℝ)) := by
      ext i j
      simp [hY, Matrix.vecMulVec_apply, sub_eq_add_neg]
    rw [hdec]
    refine (LeanDLRA.EckartYoung.rank_add_le _ _).trans ?_
    have h1 := Matrix.rank_vecMulVec_le (fun i : Fin (m + 1) => ((i : ℕ) : ℝ))
      (fun _ : Fin (m + 1) => (1 : ℝ))
    have h2 := Matrix.rank_vecMulVec_le (fun _ : Fin (m + 1) => (1 : ℝ))
      (fun j : Fin (m + 1) => -((j : ℕ) : ℝ))
    omega
  · set P := Y.map fun x => max x 0 with hP
    set M : Matrix (Fin m) (Fin m) ℝ := P.submatrix Fin.succ Fin.castSucc with hM
    have hent : ∀ i j, M i j = max (((i : ℕ) : ℝ) + 1 - ((j : ℕ) : ℝ)) 0 := by
      intro i j
      have h1 : Y i.succ j.castSucc = ((i : ℕ) : ℝ) + 1 - ((j : ℕ) : ℝ) := by
        simp [hY]
      change max (Y i.succ j.castSucc) 0 = _
      rw [h1]
    have htri : M.BlockTriangular OrderDual.toDual := by
      intro i j hij
      have hlt : i < j := hij
      rw [hent]
      have h1 : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by
        exact_mod_cast Fin.lt_def.mp hlt
      exact max_eq_right (by linarith)
    have hdet : M.det = 1 := by
      rw [Matrix.det_of_isLowerTriangular M htri]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [hent]
      simp
    have hunit : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr (by rw [hdet]; exact isUnit_one)
    have hr : M.rank = m := by
      rw [Matrix.rank_of_isUnit M hunit, Fintype.card_fin]
    calc m = M.rank := hr.symm
      _ ≤ P.rank := Matrix.rank_submatrix_le _ _ _

end Basics

section Real

/-- The determinant lower bound behind the barrier. -/
lemma det_lower {a b p q c d e u g t ε : ℝ} (ht : 0 < t) (hε0 : 0 ≤ ε) (hεt : ε ≤ t / 64)
    (hε1 : ε ≤ 1 / 64) (pa : 0 ≤ a) (pp : 0 ≤ p) (pq : 0 ≤ q) (pc : 0 ≤ c) (pd : 0 ≤ d)
    (pe : 0 ≤ e) (pu : 0 ≤ u) (pg : 0 ≤ g)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 3 / 2) (hb1 : 1 / 2 ≤ b) (hb2 : b ≤ 3 / 2)
    (hc1 : 1 / 2 ≤ c) (hc2 : c ≤ 3 / 2) (hd1 : t / 2 ≤ d) (hd2 : d ≤ 3 * t / 2)
    (he1 : t / 2 ≤ e) (he2 : e ≤ 3 * t / 2) (h02 : p ≤ ε) (h10 : q ≤ ε) (h21 : u ≤ ε) :
    7 / 128 * t ^ 2 ≤ a * (c * g - d * u) - b * (q * g - d * e) + p * (q * u - c * e) := by
  have pb : 0 ≤ b := by linarith
  have h1 : t / 2 * (t / 2) * (1 / 2) ≤ b * d * e := by
    have : t / 2 * (t / 2) ≤ d * e := mul_le_mul hd1 he1 (by positivity) pd
    calc t / 2 * (t / 2) * (1 / 2) ≤ d * e * b :=
          mul_le_mul this hb1 (by norm_num) (mul_nonneg pd pe)
      _ = b * d * e := by ring
  have h2 : a * d * u ≤ 3 / 2 * (3 * t / 2) * ε :=
    mul_le_mul (mul_le_mul ha2 hd2 pd (by norm_num)) h21 pu (by positivity)
  have h3 : p * c * e ≤ ε * (3 / 2) * (3 * t / 2) :=
    mul_le_mul (mul_le_mul h02 hc2 pc hε0) he2 pe (by positivity)
  have h4 : 0 ≤ g * (a * c - b * q) := by
    refine mul_nonneg pg ?_
    have h41 : (1 / 2 : ℝ) * (1 / 2) ≤ a * c := mul_le_mul ha1 hc1 (by norm_num) pa
    have h42 : b * q ≤ 3 / 2 * ε := mul_le_mul hb2 h10 pq (by norm_num)
    linarith
  have h5 : 0 ≤ p * q * u := by positivity
  have h7 : t * ε ≤ t * (t / 64) := mul_le_mul_of_nonneg_left hεt ht.le
  have h6 : a * (c * g - d * u) - b * (q * g - d * e) + p * (q * u - c * e) =
      g * (a * c - b * q) + b * d * e - a * d * u - p * c * e + p * q * u := by ring
  rw [h6]
  linarith

/-- A `2 × 2` cofactor of entries in `[0, 3/2]` is at most `9/4`. -/
lemma cof_le {s₁ s₂ s₃ s₄ : ℝ} (h1 : 0 ≤ s₁) (h1' : s₁ ≤ 3 / 2) (h2 : 0 ≤ s₂) (h2' : s₂ ≤ 3 / 2)
    (h3 : 0 ≤ s₃) (h3' : s₃ ≤ 3 / 2) (h4 : 0 ≤ s₄) (h4' : s₄ ≤ 3 / 2) :
    |s₁ * s₂ - s₃ * s₄| ≤ 9 / 4 := by
  have h5 : s₁ * s₂ ≤ 3 / 2 * (3 / 2) := mul_le_mul h1' h2' h2 (by norm_num)
  have h6 : s₃ * s₄ ≤ 3 / 2 * (3 / 2) := mul_le_mul h3' h4' h4 (by norm_num)
  have h7 : 0 ≤ s₁ * s₂ := mul_nonneg h1 h2
  have h8 : 0 ≤ s₃ * s₄ := mul_nonneg h3 h4
  rw [abs_le]
  constructor <;> linarith

/-- The triangle inequality for a cofactor expansion. -/
lemma cramer_tri {k₀ k₁ k₂ r₀ r₁ r₂ ρ : ℝ} (h0 : |k₀| ≤ 9 / 4) (h1 : |k₁| ≤ 9 / 4)
    (h2 : |k₂| ≤ 9 / 4) (h3 : |r₀| ≤ ρ) (h4 : |r₁| ≤ ρ) (h5 : |r₂| ≤ ρ) :
    |k₀ * r₀ - k₁ * r₁ + k₂ * r₂| ≤ 27 / 4 * ρ := by
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans h3
  have m0 : |k₀ * r₀| ≤ 9 / 4 * ρ := by
    rw [abs_mul]; exact mul_le_mul h0 h3 (abs_nonneg _) (by norm_num)
  have m1 : |k₁ * r₁| ≤ 9 / 4 * ρ := by
    rw [abs_mul]; exact mul_le_mul h1 h4 (abs_nonneg _) (by norm_num)
  have m2 : |k₂ * r₂| ≤ 9 / 4 * ρ := by
    rw [abs_mul]; exact mul_le_mul h2 h5 (abs_nonneg _) (by norm_num)
  have h6 := abs_add_le (k₀ * r₀ - k₁ * r₁) (k₂ * r₂)
  have h7 := abs_sub (k₀ * r₀) (k₁ * r₁)
  linarith

/-- Cramer's rule for a `3 × 3` system with entries in `[0, 3/2]`. -/
lemma cramer_sum {a b p q c d e u g x₀ x₁ x₂ r₀ r₁ r₂ ρ : ℝ} (pa : 0 ≤ a) (pb : 0 ≤ b)
    (pp : 0 ≤ p) (pq : 0 ≤ q) (pc : 0 ≤ c) (pd : 0 ≤ d) (pe : 0 ≤ e) (pu : 0 ≤ u) (pg : 0 ≤ g)
    (ba : a ≤ 3 / 2) (bb : b ≤ 3 / 2) (bp : p ≤ 3 / 2) (bq : q ≤ 3 / 2) (bc : c ≤ 3 / 2)
    (bd : d ≤ 3 / 2) (be : e ≤ 3 / 2) (bu : u ≤ 3 / 2) (bg : g ≤ 3 / 2)
    (hD : 0 < a * (c * g - d * u) - b * (q * g - d * e) + p * (q * u - c * e))
    (e0 : a * x₀ + b * x₁ + p * x₂ = r₀) (e1 : q * x₀ + c * x₁ + d * x₂ = r₁)
    (e2 : e * x₀ + u * x₁ + g * x₂ = r₂) (h0 : |r₀| ≤ ρ) (h1 : |r₁| ≤ ρ) (h2 : |r₂| ≤ ρ) :
    (a * (c * g - d * u) - b * (q * g - d * e) + p * (q * u - c * e)) * (|x₀| + |x₁| + |x₂|) ≤
      81 / 4 * ρ := by
  set D : ℝ := a * (c * g - d * u) - b * (q * g - d * e) + p * (q * u - c * e) with hDdef
  have c0 : D * x₀ = (c * g - d * u) * r₀ - (b * g - p * u) * r₁ + (b * d - p * c) * r₂ := by
    rw [← e0, ← e1, ← e2, hDdef]; ring
  have c1 : D * x₁ = (d * e - q * g) * r₀ - (p * e - a * g) * r₁ + (p * q - a * d) * r₂ := by
    rw [← e0, ← e1, ← e2, hDdef]; ring
  have c2 : D * x₂ = (q * u - c * e) * r₀ - (a * u - b * e) * r₁ + (a * c - b * q) * r₂ := by
    rw [← e0, ← e1, ← e2, hDdef]; ring
  have d0 : D * |x₀| ≤ 27 / 4 * ρ := by
    have : |D * x₀| = D * |x₀| := by rw [abs_mul, abs_of_pos hD]
    rw [← this, c0]
    exact cramer_tri (cof_le pc bc pg bg pd bd pu bu) (cof_le pb bb pg bg pp bp pu bu)
      (cof_le pb bb pd bd pp bp pc bc) h0 h1 h2
  have d1 : D * |x₁| ≤ 27 / 4 * ρ := by
    have : |D * x₁| = D * |x₁| := by rw [abs_mul, abs_of_pos hD]
    rw [← this, c1]
    exact cramer_tri (cof_le pd bd pe be pq bq pg bg) (cof_le pp bp pe be pa ba pg bg)
      (cof_le pp bp pq bq pa ba pd bd) h0 h1 h2
  have d2 : D * |x₂| ≤ 27 / 4 * ρ := by
    have : |D * x₂| = D * |x₂| := by rw [abs_mul, abs_of_pos hD]
    rw [← this, c2]
    exact cramer_tri (cof_le pq bq pu bu pc bc pe be) (cof_le pa ba pu bu pb bb pe be)
      (cof_le pa ba pc bc pb bb pq bq) h0 h1 h2
  have : D * (|x₀| + |x₁| + |x₂|) = D * |x₀| + D * |x₁| + D * |x₂| := by ring
  rw [this]
  linarith

end Real

section Barrier

open Sum

variable {κ : Type*} [Fintype κ]

/-- The core of the barrier: a nonnegative matrix close to `barrier` on the indicated entries has
trivial kernel. -/
lemma barrier_core {t ε : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hε0 : 0 ≤ ε)
    (hε : 64 * ((Fintype.card κ : ℝ) + 1) * ε ≤ t)
    {B : Matrix (Fin 3 ⊕ κ) (Fin 3 ⊕ κ) ℝ} (hB : IsNonneg B)
    (h00 : B (inl 0) (inl 0) ∈ Icc (1 / 2 : ℝ) (3 / 2))
    (h01 : B (inl 0) (inl 1) ∈ Icc (1 / 2 : ℝ) (3 / 2))
    (h11 : B (inl 1) (inl 1) ∈ Icc (1 / 2 : ℝ) (3 / 2))
    (h12 : B (inl 1) (inl 2) ∈ Icc (t / 2) (3 * t / 2))
    (h20 : B (inl 2) (inl 0) ∈ Icc (t / 2) (3 * t / 2))
    (h02 : B (inl 0) (inl 2) ≤ ε) (h10 : B (inl 1) (inl 0) ≤ ε)
    (h21 : B (inl 2) (inl 1) ≤ ε) (h22 : B (inl 2) (inl 2) ≤ ε)
    (hkk : ∀ k, 1 / 2 ≤ B (inr k) (inr k))
    (hki : ∀ k i, B (inr k) (inl i) ≤ ε) (hik : ∀ i k, B (inl i) (inr k) ≤ ε)
    (hkl : ∀ k l, k ≠ l → B (inr k) (inr l) ≤ ε)
    {w : Fin 3 ⊕ κ → ℝ} (hw : B *ᵥ w = 0) : w = 0 := by
  classical
  set N : ℝ := (Fintype.card κ : ℝ) with hN
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hεt : ε ≤ t / 64 := by nlinarith
  have hNε : N * ε ≤ t / 64 := by nlinarith
  have hε1 : ε ≤ 1 / 64 := by linarith
  set x : Fin 3 → ℝ := fun i => w (inl i) with hx
  set z : κ → ℝ := fun k => w (inr k) with hz
  set S : ℝ := ∑ k, |z k| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set Xs : ℝ := |x 0| + |x 1| + |x 2| with hXs
  have hXs0 : 0 ≤ Xs := by positivity
  have hrow : ∀ a, ∑ i : Fin 3, B a (inl i) * x i + ∑ k, B a (inr k) * z k = 0 := by
    intro a
    have := congrFun hw a
    simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type] using this
  -- the rows of the identity block
  have hzk : ∀ k, (1 / 2 : ℝ) * |z k| ≤ ε * Xs + ε * S := by
    intro k
    have h := hrow (inr k)
    have hsplit : ∑ l, B (inr k) (inr l) * z l =
        B (inr k) (inr k) * z k + ∑ l ∈ Finset.univ.erase k, B (inr k) (inr l) * z l :=
      (Finset.add_sum_erase Finset.univ (fun l => B (inr k) (inr l) * z l)
        (Finset.mem_univ k)).symm
    rw [hsplit, Fin.sum_univ_three] at h
    have hsum : |∑ l ∈ Finset.univ.erase k, B (inr k) (inr l) * z l| ≤ ε * S := by
      calc |∑ l ∈ Finset.univ.erase k, B (inr k) (inr l) * z l|
          ≤ ∑ l ∈ Finset.univ.erase k, |B (inr k) (inr l) * z l| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ l ∈ Finset.univ.erase k, ε * |z l| := by
            refine Finset.sum_le_sum fun l hl => ?_
            have hne : k ≠ l := (Finset.ne_of_mem_erase hl).symm
            rw [abs_mul, abs_of_nonneg (hB _ _)]
            exact mul_le_mul_of_nonneg_right (hkl k l hne) (abs_nonneg _)
        _ ≤ ∑ l, ε * |z l| := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun _ _ _ => ?_
            positivity
        _ = ε * S := by rw [hS, Finset.mul_sum]
    have hti : ∀ i, |B (inr k) (inl i) * x i| ≤ ε * |x i| := by
      intro i
      rw [abs_mul, abs_of_nonneg (hB _ _)]
      exact mul_le_mul_of_nonneg_right (hki k i) (abs_nonneg _)
    have hmain : B (inr k) (inr k) * z k = -(B (inr k) (inl 0) * x 0 + B (inr k) (inl 1) * x 1 +
        B (inr k) (inl 2) * x 2 + ∑ l ∈ Finset.univ.erase k, B (inr k) (inr l) * z l) := by
      linarith
    have habs : B (inr k) (inr k) * |z k| ≤ ε * Xs + ε * S := by
      have : |B (inr k) (inr k) * z k| = B (inr k) (inr k) * |z k| := by
        rw [abs_mul, abs_of_nonneg (hB _ _)]
      rw [← this, hmain, abs_neg]
      refine (abs_add_le _ _).trans ?_
      refine add_le_add ?_ hsum
      refine (abs_add_le _ _).trans ?_
      have h0 := hti 0
      have h1 := hti 1
      have h2 := hti 2
      have := abs_add_le (B (inr k) (inl 0) * x 0) (B (inr k) (inl 1) * x 1)
      rw [hXs]
      linarith
    have : (1 / 2 : ℝ) * |z k| ≤ B (inr k) (inr k) * |z k| :=
      mul_le_mul_of_nonneg_right (hkk k) (abs_nonneg _)
    linarith
  -- summing over the identity block
  have hSbound : S ≤ 4 * (N * ε) * Xs := by
    have hsum : (1 / 2 : ℝ) * S ≤ N * (ε * Xs + ε * S) := by
      calc (1 / 2 : ℝ) * S = ∑ k, (1 / 2 : ℝ) * |z k| := by rw [hS, Finset.mul_sum]
        _ ≤ ∑ _k : κ, (ε * Xs + ε * S) := Finset.sum_le_sum fun k _ => hzk k
        _ = N * (ε * Xs + ε * S) := by simp [hN, Finset.card_univ]; ring
    have hq : N * ε ≤ 1 / 4 := by linarith
    have hS' : (N * ε) * S ≤ 1 / 4 * S := mul_le_mul_of_nonneg_right hq hS0
    have : N * (ε * Xs + ε * S) = (N * ε) * Xs + (N * ε) * S := by ring
    linarith
  -- the right-hand sides of the `3 × 3` system
  have hri : ∀ i : Fin 3, |∑ k, B (inl i) (inr k) * z k| ≤ ε * S := by
    intro i
    calc |∑ k, B (inl i) (inr k) * z k| ≤ ∑ k, |B (inl i) (inr k) * z k| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, ε * |z k| := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul, abs_of_nonneg (hB _ _)]
          exact mul_le_mul_of_nonneg_right (hik i k) (abs_nonneg _)
      _ = ε * S := by rw [hS, Finset.mul_sum]
  have hre : ∀ i : Fin 3, B (inl i) (inl 0) * x 0 + B (inl i) (inl 1) * x 1 +
      B (inl i) (inl 2) * x 2 = -∑ k, B (inl i) (inr k) * z k := by
    intro i
    have h := hrow (inl i)
    rw [Fin.sum_univ_three] at h
    linarith
  have hD := det_lower (a := B (inl 0) (inl 0)) (b := B (inl 0) (inl 1)) (p := B (inl 0) (inl 2))
    (q := B (inl 1) (inl 0)) (c := B (inl 1) (inl 1)) (d := B (inl 1) (inl 2))
    (e := B (inl 2) (inl 0)) (u := B (inl 2) (inl 1)) (g := B (inl 2) (inl 2)) ht hε0 hεt hε1
    (hB _ _) (hB _ _) (hB _ _) (hB _ _) (hB _ _) (hB _ _) (hB _ _) (hB _ _)
    h00.1 h00.2 h01.1 h01.2 h11.1 h11.2 h12.1 h12.2 h20.1 h20.2 h02 h10 h21
  have htpos : 0 < t ^ 2 := by positivity
  have hDpos := lt_of_lt_of_le (by positivity : 0 < 7 / 128 * t ^ 2) hD
  have hfinal := cramer_sum (ρ := ε * S) (hB (inl 0) (inl 0)) (hB (inl 0) (inl 1))
    (hB (inl 0) (inl 2)) (hB (inl 1) (inl 0)) (hB (inl 1) (inl 1)) (hB (inl 1) (inl 2))
    (hB (inl 2) (inl 0)) (hB (inl 2) (inl 1)) (hB (inl 2) (inl 2)) h00.2 h01.2 (by linarith)
    (by linarith) h11.2
    (by linarith [h12.2]) (by linarith [h20.2]) (by linarith) (by linarith) hDpos
    (hre 0) (hre 1) (hre 2) (by rw [abs_neg]; exact hri 0) (by rw [abs_neg]; exact hri 1)
    (by rw [abs_neg]; exact hri 2)
  have hXzero : Xs = 0 := by
    by_contra hne
    have hpos : 0 < Xs := lt_of_le_of_ne hXs0 (Ne.symm hne)
    have h1 : ε * S ≤ ε * (4 * (N * ε) * Xs) := mul_le_mul_of_nonneg_left hSbound hε0
    have h2 : ε * (N * ε) ≤ t / 64 * (t / 64) := mul_le_mul hεt hNε (by positivity) (by positivity)
    have h3 : 7 / 128 * t ^ 2 * Xs ≤ 81 * (t / 64 * (t / 64)) * Xs := by
      calc 7 / 128 * t ^ 2 * Xs ≤ _ := mul_le_mul_of_nonneg_right hD hXs0
        _ ≤ 81 / 4 * (ε * S) := hfinal
        _ ≤ 81 / 4 * (ε * (4 * (N * ε) * Xs)) := by linarith
        _ = 81 * (ε * (N * ε)) * Xs := by ring
        _ ≤ 81 * (t / 64 * (t / 64)) * Xs :=
            mul_le_mul_of_nonneg_right (by linarith) hpos.le
    have h4 : 7 / 128 * t ^ 2 ≤ 81 * (t / 64 * (t / 64)) := le_of_mul_le_mul_right h3 hpos
    have h5 : 81 * (t / 64 * (t / 64)) = 81 / 4096 * t ^ 2 := by ring
    rw [h5] at h4
    linarith
  have hx0 : ∀ i, x i = 0 := by
    have h0 := abs_nonneg (x 0)
    have h1 := abs_nonneg (x 1)
    have h2 := abs_nonneg (x 2)
    have hz' : |x 0| + |x 1| + |x 2| = 0 := hXzero
    intro i
    fin_cases i
    · exact abs_eq_zero.mp (by simp only [Fin.zero_eta]; linarith)
    · exact abs_eq_zero.mp (by simp only [Fin.mk_one]; linarith)
    · exact abs_eq_zero.mp (by simp only [Fin.reduceFinMk]; linarith)
  have hSzero : S = 0 := by
    have : S ≤ 0 := by rw [hXzero] at hSbound; simpa using hSbound
    linarith
  have hz0 : ∀ k, z k = 0 := by
    intro k
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => abs_nonneg _)).mp hSzero k
      (Finset.mem_univ k)
    exact abs_eq_zero.mp h
  funext s
  cases s with
  | inl i => exact hx0 i
  | inr k => exact hz0 k

variable [DecidableEq κ]

variable (κ) in
/-- The family `A_{s,t} = !![1-s,1,0; 0,1-s,t; t,0,0] ⊕ 1`.  The matrix of the barrier is
`barrierMat κ 0 t`; the forward Euler step of `gen` from `X₀` is `barrierMat κ h h`. -/
def barrierMat (s t : ℝ) : Matrix (Fin 3 ⊕ κ) (Fin 3 ⊕ κ) ℝ :=
  fromBlocks !![1 - s, 1, 0; 0, 1 - s, t; t, 0, 0] 0 0 1

/-- If row `2` of `P` is a combination of rows `0` and `1`, then `P ⊕ 1` has rank at most
`2 + card κ`. -/
lemma rank_block_le {P : Matrix (Fin 3) (Fin 3) ℝ} {α β : ℝ}
    (h0 : P 2 0 = α * P 0 0 + β * P 1 0) (h1 : P 2 1 = α * P 0 1 + β * P 1 1)
    (h2 : P 2 2 = α * P 0 2 + β * P 1 2) :
    (fromBlocks P 0 0 (1 : Matrix κ κ ℝ)).rank ≤ 2 + Fintype.card κ := by
  have h : ∀ j, P 2 j = α * P 0 j + β * P 1 j := by
    intro j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
  let C : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 1; α, β]
  let D : Matrix (Fin 2) (Fin 3) ℝ := !![P 0 0, P 0 1, P 0 2; P 1 0, P 1 1, P 1 2]
  have hP : P = C * D := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [C, D, Matrix.mul_apply, Fin.sum_univ_succ, h]
  have hfac : fromBlocks P 0 0 (1 : Matrix κ κ ℝ) =
      fromBlocks C 0 0 (1 : Matrix κ κ ℝ) * fromBlocks D 0 0 (1 : Matrix κ κ ℝ) := by
    rw [fromBlocks_multiply]
    simp [hP]
  rw [hfac]
  calc _ ≤ (fromBlocks C 0 0 (1 : Matrix κ κ ℝ)).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin 2 ⊕ κ) := Matrix.rank_le_card_width _
    _ = 2 + Fintype.card κ := by simp

/-- **Lower bound of the barrier.**  Let `0 ≤ s ≤ 1/4`, `0 < t ≤ 1`, `64 (card κ + 1) ε ≤ t`.  A
matrix `B` (of any size) that is nonnegative and whose restriction to some rows `f` and columns `g`
is `ε`-close to `A_{s,t} = barrierMat κ s t` has rank at least `3 + card κ`.  This matters because
it gives a distance `≥ t / (64 (card κ + 1))` to nonnegative matrices of rank `≤ 2 + card κ`,
compared to `barrier_rank_approx`.  For `r = 2` such matrices have nonnegative factorizations
(Cohen-Rothblum), so this is also a statement about nonnegative matrix factorization; the mechanism
is the nonconvex tangent cone of the nonnegative rank-`r` matrices at a matrix with zero entries. -/
theorem barrier_rank_lower {ι ι' : Type*} [Fintype ι'] {s t ε : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1 / 4)
    (ht : 0 < t) (ht1 : t ≤ 1) (hε0 : 0 ≤ ε) (hε : 64 * ((Fintype.card κ : ℝ) + 1) * ε ≤ t)
    (f : Fin 3 ⊕ κ → ι) (g : Fin 3 ⊕ κ → ι') {B : Matrix ι ι' ℝ} (hB : IsNonneg B)
    (hclose : ∀ a b, |B (f a) (g b) - barrierMat κ s t a b| ≤ ε) :
    3 + Fintype.card κ ≤ B.rank := by
  have hN0 : (0 : ℝ) ≤ (Fintype.card κ : ℝ) := Nat.cast_nonneg _
  have hεt : ε ≤ t / 64 := by nlinarith
  have hε1 : ε ≤ 1 / 64 := by linarith
  set B' : Matrix (Fin 3 ⊕ κ) (Fin 3 ⊕ κ) ℝ := B.submatrix f g with hB'
  have hle : B'.rank ≤ B.rank := Matrix.rank_submatrix_le _ _ _
  have hnn : IsNonneg B' := fun a b => hB _ _
  have hcl : ∀ a b, B' a b ∈ Icc (barrierMat κ s t a b - ε) (barrierMat κ s t a b + ε) := by
    intro a b
    have := abs_le.mp (hclose a b)
    exact ⟨by simp only [hB', submatrix_apply]; linarith [this.1],
      by simp only [hB', submatrix_apply]; linarith [this.2]⟩
  have e00 : B' (Sum.inl 0) (Sum.inl 0) ∈ Icc (1 - s - ε) (1 - s + ε) := by
    simpa [barrierMat] using hcl (Sum.inl 0) (Sum.inl 0)
  have e01 : B' (Sum.inl 0) (Sum.inl 1) ∈ Icc (1 - ε) (1 + ε) := by
    simpa [barrierMat] using hcl (Sum.inl 0) (Sum.inl 1)
  have e02 : B' (Sum.inl 0) (Sum.inl 2) ∈ Icc (0 - ε) (0 + ε) := by
    simpa [barrierMat] using hcl (Sum.inl 0) (Sum.inl 2)
  have e10 : B' (Sum.inl 1) (Sum.inl 0) ∈ Icc (0 - ε) (0 + ε) := by
    simpa [barrierMat] using hcl (Sum.inl 1) (Sum.inl 0)
  have e11 : B' (Sum.inl 1) (Sum.inl 1) ∈ Icc (1 - s - ε) (1 - s + ε) := by
    simpa [barrierMat] using hcl (Sum.inl 1) (Sum.inl 1)
  have e12 : B' (Sum.inl 1) (Sum.inl 2) ∈ Icc (t - ε) (t + ε) := by
    simpa [barrierMat] using hcl (Sum.inl 1) (Sum.inl 2)
  have e20 : B' (Sum.inl 2) (Sum.inl 0) ∈ Icc (t - ε) (t + ε) := by
    simpa [barrierMat] using hcl (Sum.inl 2) (Sum.inl 0)
  have e21 : B' (Sum.inl 2) (Sum.inl 1) ∈ Icc (0 - ε) (0 + ε) := by
    simpa [barrierMat] using hcl (Sum.inl 2) (Sum.inl 1)
  have e22 : B' (Sum.inl 2) (Sum.inl 2) ∈ Icc (0 - ε) (0 + ε) := by
    simpa [barrierMat] using hcl (Sum.inl 2) (Sum.inl 2)
  have hinj : ∀ w : Fin 3 ⊕ κ → ℝ, B' *ᵥ w = 0 → w = 0 := by
    intro w hw
    refine barrier_core ht ht1 hε0 hε hnn ⟨?_, ?_⟩ ⟨?_, ?_⟩ ⟨?_, ?_⟩ ⟨?_, ?_⟩ ⟨?_, ?_⟩
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hw
    · linarith [e00.1]
    · linarith [e00.2]
    · linarith [e01.1]
    · linarith [e01.2]
    · linarith [e11.1]
    · linarith [e11.2]
    · linarith [e12.1]
    · linarith [e12.2]
    · linarith [e20.1]
    · linarith [e20.2]
    · linarith [e02.2]
    · linarith [e10.2]
    · linarith [e21.2]
    · linarith [e22.2]
    · intro k
      have : B' (Sum.inr k) (Sum.inr k) ∈ Icc (1 - ε) (1 + ε) := by
        simpa [barrierMat] using hcl (Sum.inr k) (Sum.inr k)
      linarith [this.1]
    · intro k i
      have : B' (Sum.inr k) (Sum.inl i) ∈ Icc (0 - ε) (0 + ε) := by
        simpa [barrierMat] using hcl (Sum.inr k) (Sum.inl i)
      linarith [this.2]
    · intro i k
      have : B' (Sum.inl i) (Sum.inr k) ∈ Icc (0 - ε) (0 + ε) := by
        simpa [barrierMat] using hcl (Sum.inl i) (Sum.inr k)
      linarith [this.2]
    · intro k l hkl
      have : B' (Sum.inr k) (Sum.inr l) ∈ Icc (0 - ε) (0 + ε) := by
        simpa [barrierMat, hkl] using hcl (Sum.inr k) (Sum.inr l)
      linarith [this.2]
  have hr := rank_eq_card_of_inj hinj
  simp only [Fintype.card_sum, Fintype.card_fin] at hr
  omega

/-- **Upper bound for the unconstrained problem.**  `A_{s,t}` is within `(t/(1-s))²` (entrywise) of
a matrix of rank at most `2 + card κ`. -/
theorem barrier_rank_approx {s t : ℝ} (hs' : s ≤ 1 / 4) :
    ∃ Y : Matrix (Fin 3 ⊕ κ) (Fin 3 ⊕ κ) ℝ, Y.rank ≤ 2 + Fintype.card κ ∧
      ∀ a b, |barrierMat κ s t a b - Y a b| ≤ (t / (1 - s)) ^ 2 := by
  have h1s : 1 - s ≠ 0 := by intro h; linarith
  refine ⟨fromBlocks !![1 - s, 1, 0; 0, 1 - s, t; t, 0, -(t / (1 - s)) ^ 2] 0 0 1, ?_, ?_⟩
  · have r0 : t = t / (1 - s) * (1 - s) + -t / (1 - s) ^ 2 * 0 := by field_simp; ring
    have r1 : (0 : ℝ) = t / (1 - s) * 1 + -t / (1 - s) ^ 2 * (1 - s) := by field_simp; ring
    have r2 : -(t / (1 - s)) ^ 2 = t / (1 - s) * 0 + -t / (1 - s) ^ 2 * t := by field_simp; ring
    exact rank_block_le (α := t / (1 - s)) (β := -t / (1 - s) ^ 2) r0 r1 r2
  · intro a b
    have hp : 0 ≤ (t / (1 - s)) ^ 2 := by positivity
    rcases a with a | a <;> rcases b with b | b
    · fin_cases a <;> fin_cases b <;> simp [barrierMat, hp]
    · simp [barrierMat, hp]
    · simp [barrierMat, hp]
    · simp [barrierMat, hp]

/-- **Sharpness of the barrier.**  For `0 ≤ s ≤ 1/4` and `t ≥ 0` the matrix `A_{s,t}` is within
`t/(1-s)` of a nonnegative matrix of rank at most `2 + card κ`. -/
theorem barrier_sharp {s t : ℝ} (hs' : s ≤ 1 / 4) (ht : 0 ≤ t) :
    ∃ B : Matrix (Fin 3 ⊕ κ) (Fin 3 ⊕ κ) ℝ, IsNonneg B ∧ B.rank ≤ 2 + Fintype.card κ ∧
      ∀ a b, |barrierMat κ s t a b - B a b| ≤ t / (1 - s) := by
  have h1s : 1 - s ≠ 0 := by intro h; linarith
  have h1p : 0 < 1 - s := by linarith
  have hp : 0 ≤ t / (1 - s) := by positivity
  refine ⟨fromBlocks !![1 - s, 1, t / (1 - s); 0, 1 - s, t; t, 0, 0] 0 0 1, ?_, ?_, ?_⟩
  · intro a b
    rcases a with a | a <;> rcases b with b | b
    · fin_cases a <;> fin_cases b <;> simp [hp, ht, h1p.le]
    · simp
    · simp
    · simp [Matrix.one_apply]; split_ifs <;> norm_num
  · have r0 : t = t / (1 - s) * (1 - s) + -t / (1 - s) ^ 2 * 0 := by field_simp; ring
    have r1 : (0 : ℝ) = t / (1 - s) * 1 + -t / (1 - s) ^ 2 * (1 - s) := by field_simp; ring
    have r2 : (0 : ℝ) = t / (1 - s) * (t / (1 - s)) + -t / (1 - s) ^ 2 * t := by
      field_simp; ring
    exact rank_block_le (α := t / (1 - s)) (β := -t / (1 - s) ^ 2) r0 r1 r2
  · intro a b
    rcases a with a | a <;> rcases b with b | b
    · fin_cases a <;> fin_cases b <;> simp [barrierMat, hp, abs_of_nonneg]
    · simp [barrierMat, hp]
    · simp [barrierMat, hp]
    · simp [barrierMat, hp]

/-- The generator of a monotone conservative kinetic scheme on three cells (rows) and three
velocities (columns): the first velocity is advected upwind along the periodic cell order
`0 → 2 → 1 → 0`, and in cell `1` particles of velocity `1` scatter into velocity `2`. -/
def gen3 (X : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![X 1 0 - X 0 0, 0, 0; X 2 0 - X 1 0, -X 1 1, X 1 1; X 0 0 - X 2 0, 0, 0]

variable (κ) in
/-- `gen3` on the block `Fin 3`, zero on the additional cells and velocities `κ`. -/
def gen (X : Matrix (Fin 3 ⊕ κ) (Fin 3 ⊕ κ) ℝ) : Matrix (Fin 3 ⊕ κ) (Fin 3 ⊕ κ) ℝ :=
  fromBlocks (gen3 X.toBlocks₁₁) 0 0 0

variable (κ) in
/-- The initial value `X₀ = !![1,1,0; 0,1,0; 0,0,0] ⊕ 1`, of rank `2 + card κ`. -/
def X₀ : Matrix (Fin 3 ⊕ κ) (Fin 3 ⊕ κ) ℝ := barrierMat κ 0 0

/-- The forward Euler step of `gen` from `X₀` is `A_{h,h}`. -/
lemma euler_X₀ (h : ℝ) : X₀ κ + h • gen κ (X₀ κ) = barrierMat κ h h := by
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · fin_cases a <;> fin_cases b <;> simp [X₀, barrierMat, gen, gen3, Matrix.add_apply] <;> ring
  · simp [X₀, barrierMat, gen]
  · simp [X₀, barrierMat, gen]
  · simp [X₀, barrierMat, gen]

set_option linter.flexible false in
/-- `gen` is the generator of a monotone scheme: forward Euler with step `h ≤ 1` preserves
nonnegativity (and, being linear, the order). -/
theorem gen_euler_nonneg {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) {X : Matrix (Fin 3 ⊕ κ) (Fin 3 ⊕ κ) ℝ}
    (hX : IsNonneg X) : IsNonneg (X + h • gen κ X) := by
  have hh : 0 ≤ 1 - h := by linarith
  intro a b
  rcases a with a | a <;> rcases b with b | b
  · have h00 := hX (Sum.inl 0) (Sum.inl 0)
    have h10 := hX (Sum.inl 1) (Sum.inl 0)
    have h20 := hX (Sum.inl 2) (Sum.inl 0)
    have h11 := hX (Sum.inl 1) (Sum.inl 1)
    fin_cases a <;> fin_cases b <;>
      simp only [gen, gen3, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, fromBlocks_apply₁₁,
        toBlocks₁₁, Matrix.of_apply] <;> simp
    · nlinarith [mul_nonneg hh h00, mul_nonneg h0 h10]
    · exact hX _ _
    · exact hX _ _
    · nlinarith [mul_nonneg hh h10, mul_nonneg h0 h20]
    · nlinarith [mul_nonneg hh h11]
    · nlinarith [mul_nonneg h0 h11, hX (Sum.inl 1) (Sum.inl 2)]
    · nlinarith [mul_nonneg hh h20, mul_nonneg h0 h00]
    · exact hX _ _
    · exact hX _ _
  · simpa [gen] using hX _ _
  · simpa [gen] using hX _ _
  · simpa [gen] using hX _ _

/-- `gen` is conservative: the entries of `gen X` sum to zero. -/
theorem gen_mass (X : Matrix (Fin 3 ⊕ κ) (Fin 3 ⊕ κ) ℝ) : ∑ a, ∑ b, gen κ X a b = 0 := by
  simp [gen, gen3, Fintype.sum_sum_type, Fin.sum_univ_three]

/-- **No consistent nonnegative method of rank `2 + card κ`.**  There is no family `G h` of
nonnegative matrices of rank at most `2 + card κ` (the rank of `X₀`) with `G h = X₀ + h gen X₀ +
o(h)` as `h ↓ 0`, although `X₀` is nonnegative of that rank and `gen` generates a monotone
conservative scheme.  See the module docstring. -/
theorem no_consistent_nonneg_lowRank (G : ℝ → Matrix (Fin 3 ⊕ κ) (Fin 3 ⊕ κ) ℝ)
    (hG : ∀ᶠ h in 𝓝[>] (0 : ℝ), IsNonneg (G h) ∧ (G h).rank ≤ 2 + Fintype.card κ)
    (hcons : ∀ c : ℝ, 0 < c → ∀ᶠ h in 𝓝[>] (0 : ℝ),
      ∀ a b, |G h a b - (X₀ κ + h • gen κ (X₀ κ)) a b| ≤ c * h) : False := by
  have hN : (0 : ℝ) < 64 * ((Fintype.card κ : ℝ) + 1) := by positivity
  set c : ℝ := 1 / (64 * ((Fintype.card κ : ℝ) + 1)) with hc
  have hcpos : 0 < c := by positivity
  have hsmall : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Ioo (0 : ℝ) (1 / 4) := Ioo_mem_nhdsGT (by norm_num)
  obtain ⟨h, ⟨hnn, hrk⟩, hcl, hmem⟩ := (hG.and ((hcons c hcpos).and hsmall)).exists
  rw [euler_X₀] at hcl
  have hbound := barrier_rank_lower (ε := c * h) (s := h) (t := h) hmem.1.le hmem.2.le hmem.1
    (by linarith [hmem.2]) (by have := hmem.1; positivity)
    (by
      have : 64 * ((Fintype.card κ : ℝ) + 1) * (c * h) = h := by
        rw [hc]; field_simp
      exact this.le) id id hnn hcl
  omega

/-- The obstruction is the combination of positivity and rank: without the sign constraint there are
matrices of rank `2 + card κ` that are second-order close to the Euler step. -/
theorem exists_consistent_lowRank {h : ℝ} (hh : 0 ≤ h) (hh' : h ≤ 1 / 4) :
    ∃ Y : Matrix (Fin 3 ⊕ κ) (Fin 3 ⊕ κ) ℝ, Y.rank ≤ 2 + Fintype.card κ ∧
      ∀ a b, |Y a b - (X₀ κ + h • gen κ (X₀ κ)) a b| ≤ 2 * h ^ 2 := by
  obtain ⟨Y, hY, hbd⟩ := barrier_rank_approx (κ := κ) (s := h) (t := h) hh'
  refine ⟨Y, hY, fun a b => ?_⟩
  rw [euler_X₀, abs_sub_comm]
  refine (hbd a b).trans ?_
  have h1 : 0 < 1 - h := by linarith
  have h2 : h / (1 - h) ≤ 4 / 3 * h := by
    rw [div_le_iff₀ h1]
    nlinarith
  have h3 : 0 ≤ h / (1 - h) := by positivity
  calc (h / (1 - h)) ^ 2 ≤ (4 / 3 * h) ^ 2 := by gcongr
    _ ≤ 2 * h ^ 2 := by nlinarith [sq_nonneg h]

end Barrier

section NoMonotone

variable {ι ι' : Type*} [Fintype ι] [Fintype ι']

/-- A square matrix with a nontrivial kernel has rank below the size. -/
lemma rank_le_of_kernel {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℝ} {r : ℕ}
    (hn : Fintype.card n = r + 1) {v : n → ℝ} (hv : v ≠ 0) (hM : M *ᵥ v = 0) : M.rank ≤ r := by
  by_contra hcon
  have hle : M.rank ≤ Fintype.card n := Matrix.rank_le_card_width M
  have heq : M.rank = Fintype.card n := by omega
  have hsurj : LinearMap.range M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa [Matrix.rank] using heq
  have hs : Function.Surjective M.mulVecLin := LinearMap.range_eq_top.mp hsurj
  have hinj : Function.Injective M.mulVecLin := LinearMap.injective_iff_surjective.mpr hs
  exact hv (hinj (by simpa using hM))

/-- **No monotone low-rank compression exists.**  Let `1 ≤ r` be smaller than both dimensions.
There is no map `Q` on nonnegative matrices with values of rank at most `r` that fixes every
nonnegative matrix of rank at most `r` and is order preserving.  This makes "truncation destroys
monotonicity" precise for all truncations at once, not only the SVD: order preservation is the
property from which Crandall-Majda and Harten derive their TVD results, so it cannot be inherited
through a compression. -/
theorem no_monotone_retraction [DecidableEq ι] [DecidableEq ι'] {r : ℕ} (hr : 1 ≤ r)
    (hm : r < Fintype.card ι) (hn : r < Fintype.card ι')
    (Q : Matrix ι ι' ℝ → Matrix ι ι' ℝ)
    (hrank : ∀ X, IsNonneg X → (Q X).rank ≤ r)
    (hfix : ∀ X, IsNonneg X → X.rank ≤ r → Q X = X)
    (hmono : ∀ X X', IsNonneg X → (∀ i j, X i j ≤ X' i j) → ∀ i j, Q X i j ≤ Q X' i j) : False := by
  classical
  obtain ⟨f⟩ : Nonempty (Fin (r + 1) ↪ ι) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hm)
  obtain ⟨g⟩ : Nonempty (Fin (r + 1) ↪ ι') :=
    Function.Embedding.nonempty_of_card_le (by simpa using hn)
  let n := Fin (r + 1)
  let Cf : Matrix ι n ℝ := fun i a => if i = f a then 1 else 0
  let Cg : Matrix n ι' ℝ := fun a j => if j = g a then 1 else 0
  let pad : Matrix n n ℝ → Matrix ι ι' ℝ := fun M => Cf * M * Cg
  have hpad_entry : ∀ M i j, pad M i j =
      ∑ a, ∑ b, (if i = f a then 1 else 0) * M a b * (if j = g b then 1 else 0) := by
    intro M i j
    have h : pad M i j = ∑ b, ∑ a, Cf i a * M a b * Cg b j := by
      simp only [pad, Matrix.mul_apply, Finset.sum_mul]
    rw [h, Finset.sum_comm]
  have hpad_block : ∀ M a b, pad M (f a) (g b) = M a b := by
    intro M a b
    rw [hpad_entry, Finset.sum_eq_single a, Finset.sum_eq_single b]
    · simp
    · intro b' _ hb
      have : g b ≠ g b' := fun h => hb (g.injective h).symm
      simp [this]
    · simp
    · intro a' _ ha
      have : f a ≠ f a' := fun h => ha (f.injective h).symm
      simp [this]
    · simp
  have hpad_mono : ∀ M M' : Matrix n n ℝ, (∀ a b, M a b ≤ M' a b) →
      ∀ i j, pad M i j ≤ pad M' i j := by
    intro M M' h i j
    rw [hpad_entry, hpad_entry]
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
    have h1 : (0 : ℝ) ≤ if i = f a then 1 else 0 := by split_ifs <;> norm_num
    have h2 : (0 : ℝ) ≤ if j = g b then 1 else 0 := by split_ifs <;> norm_num
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (h a b) h1) h2
  have hpad_nonneg : ∀ M : Matrix n n ℝ, (∀ a b, 0 ≤ M a b) → IsNonneg (pad M) := by
    intro M h i j
    have := hpad_mono 0 M (by simpa using h) i j
    simpa [pad] using this
  have hpad_rank : ∀ M : Matrix n n ℝ, (pad M).rank ≤ M.rank := by
    intro M
    calc (pad M).rank ≤ (Cf * M).rank := Matrix.rank_mul_le_left _ _
      _ ≤ M.rank := Matrix.rank_mul_le_right _ _
  have hcard : Fintype.card n = r + 1 := by simp [n]
  have hone : ∀ a b : n, (0 : ℝ) ≤ (1 : Matrix n n ℝ) a b := by
    intro a b
    rw [Matrix.one_apply]
    split_ifs <;> norm_num
  set A : Matrix ι ι' ℝ := pad 1 with hA
  have hAnn : IsNonneg A := hpad_nonneg 1 hone
  -- lower bounds
  let Dl : n → Matrix n n ℝ := fun a => Matrix.diagonal fun c => if c = a then 0 else 1
  have hDl_nn : ∀ a c d, 0 ≤ Dl a c d := by
    intro a c d
    simp only [Dl, Matrix.diagonal_apply]
    split_ifs <;> norm_num
  have hDl_rank : ∀ a, (Dl a).rank ≤ r := by
    intro a
    refine rank_le_of_kernel hcard (v := Pi.single a 1) ?_ ?_
    · intro h
      have := congrFun h a
      simp at this
    · funext c
      simp only [Dl, Matrix.mulVec_diagonal, Pi.zero_apply]
      by_cases hc : c = a <;> simp [hc]
  have hlow : ∀ (a' c d : n), Dl a' c d ≤ Q A (f c) (g d) := by
    intro a' c d
    have h1 : ∀ i j, pad (Dl a') i j ≤ A i j := by
      refine hpad_mono _ _ fun c' d' => ?_
      simp only [Dl, Matrix.diagonal_apply, Matrix.one_apply]
      split_ifs <;> norm_num
    have h2 := hmono _ _ (hpad_nonneg _ (hDl_nn a')) h1 (f c) (g d)
    rw [hfix _ (hpad_nonneg _ (hDl_nn a')) ((hpad_rank _).trans (hDl_rank a')), hpad_block] at h2
    exact h2
  -- upper bounds
  let Yb : n → n → ℝ → Matrix n n ℝ := fun a b s c d =>
    if c = d then 1 else if c = a ∧ d = b then s else if c = b ∧ d = a then s⁻¹ else 0
  have hYb_nn : ∀ a b s, 0 < s → ∀ c d, 0 ≤ Yb a b s c d := by
    intro a b s hs c d
    simp only [Yb]
    split_ifs <;>
      first
        | exact zero_le_one
        | exact hs.le
        | exact (inv_pos.mpr hs).le
        | exact le_rfl
  have hYb_rank : ∀ a b s, a ≠ b → 0 < s → (Yb a b s).rank ≤ r := by
    intro a b s hab hs
    refine rank_le_of_kernel hcard (v := s • Pi.single a 1 - Pi.single b 1) ?_ ?_
    · intro h
      have := congrFun h b
      simp [hab.symm] at this
    · funext c
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_single_one,
        Matrix.col_apply, Pi.zero_apply]
      simp only [Yb]
      by_cases hca : c = a
      · subst hca; simp [hab]
      · by_cases hcb : c = b
        · subst hcb; simp [Ne.symm hca, hca, hs.ne']
        · simp [hca, hcb]
  have hup : ∀ a b s, a ≠ b → 0 < s → ∀ c d, Q A (f c) (g d) ≤ Yb a b s c d := by
    intro a b s hab hs c d
    have h1 : ∀ i j, A i j ≤ pad (Yb a b s) i j := by
      refine hpad_mono _ _ fun c' d' => ?_
      by_cases hcd : c' = d'
      · subst hcd
        simp [Yb]
      · rw [Matrix.one_apply_ne hcd]
        exact hYb_nn a b s hs c' d'
    have h2 := hmono _ _ hAnn h1 (f c) (g d)
    rw [hfix _ (hpad_nonneg _ (hYb_nn a b s hs)) ((hpad_rank _).trans (hYb_rank a b s hab hs)),
      hpad_block] at h2
    exact h2
  have hne : ∀ a : n, ∃ a' : n, a' ≠ a := by
    intro a
    have : Nontrivial n := Fin.nontrivial_iff_two_le.mpr (by omega)
    exact exists_ne a
  -- the block of `Q A` is the identity
  have hblock : (Q A).submatrix f g = 1 := by
    ext c d
    rw [Matrix.submatrix_apply]
    by_cases hcd : c = d
    · subst hcd
      obtain ⟨a', ha'⟩ := hne c
      have h1 := hlow a' c c
      have h2 := hup c a' 1 ha'.symm one_pos c c
      simp only [Dl, Matrix.diagonal_apply, Yb] at h1 h2
      simp [ha'.symm] at h1 h2
      simpa using le_antisymm h2 h1
    · rw [Matrix.one_apply_ne hcd]
      obtain ⟨a', ha'⟩ := hne c
      have h0 := hlow a' c d
      have h1 : 0 ≤ Q A (f c) (g d) := by
        refine le_trans ?_ h0
        exact hDl_nn a' c d
      refine le_antisymm ?_ h1
      refine le_of_forall_pos_le_add fun s hs => ?_
      have h2 := hup c d s hcd hs c d
      simp only [Yb, hcd, ite_false, and_self, ite_true] at h2
      simpa using h2
  have h1 := hrank A hAnn
  have h2 : (1 : Matrix n n ℝ).rank ≤ (Q A).rank := by
    rw [← hblock]
    exact Matrix.rank_submatrix_le _ _ _
  rw [Matrix.rank_one] at h2
  simp [n] at h2
  omega

end NoMonotone

section PriceOfPositivity

variable {ι ι' : Type*} [Fintype ι] [Fintype ι']

/-- **One extra rank removes the barrier, with a universal constant.**  If `A ≥ 0` is within `d`
(entrywise) of a matrix of rank at most `r`, then `A` is within `2 d` of a *nonnegative* matrix of
rank at most `r + 1`.  Compare `no_consistent_nonneg_lowRank` and `barrier_rank_lower`: at the same
rank no constant exists. -/
theorem exists_nonneg_rank_succ {A Y : Matrix ι ι' ℝ} {r : ℕ} {d : ℝ} (hA : IsNonneg A)
    (hY : Y.rank ≤ r) (h : ∀ i j, |A i j - Y i j| ≤ d) :
    ∃ B : Matrix ι ι' ℝ, IsNonneg B ∧ B.rank ≤ r + 1 ∧ ∀ i j, |A i j - B i j| ≤ 2 * d := by
  classical
  refine ⟨Y + Matrix.vecMulVec (fun _ => d) (fun _ => 1), fun i j => ?_, ?_, fun i j => ?_⟩
  · have := abs_le.mp (h i j)
    simp only [Matrix.add_apply, Matrix.vecMulVec_apply, mul_one]
    linarith [hA i j, this.2]
  · refine (LeanDLRA.EckartYoung.rank_add_le _ _).trans ?_
    have := Matrix.rank_vecMulVec_le (fun _ : ι => d) (fun _ : ι' => (1 : ℝ))
    omega
  · have := abs_le.mp (h i j)
    simp only [Matrix.add_apply, Matrix.vecMulVec_apply, mul_one]
    rw [abs_le]
    constructor <;> linarith [this.1, this.2]

end PriceOfPositivity

section Gronwall

/-- Discrete Gronwall. -/
lemma gronwall_discrete {e : ℕ → ℝ} {B D h : ℝ} (hB : 0 ≤ B) (hh : 0 ≤ h) (hD : 0 ≤ D)
    (he : ∀ n, 0 ≤ e n) (hstep : ∀ n, e (n + 1) ≤ (1 + B * h) * e n + D) (N : ℕ) :
    e N ≤ Real.exp (B * h * N) * (e 0 + N * D) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hBh : 0 ≤ B * h := mul_nonneg hB hh
    have h1 : 1 + B * h ≤ Real.exp (B * h) := by
      linarith [Real.add_one_le_exp (B * h)]
    have hsum : 0 ≤ e 0 + N * D := add_nonneg (he 0) (mul_nonneg (Nat.cast_nonneg _) hD)
    have h2 : (1 + B * h) * e N ≤ Real.exp (B * h) * (Real.exp (B * h * N) * (e 0 + N * D)) :=
      mul_le_mul h1 ih (he N) (Real.exp_pos _).le
    have h3 : (1 : ℝ) ≤ Real.exp (B * h * ((N + 1 : ℕ) : ℝ)) :=
      Real.one_le_exp (mul_nonneg hBh (Nat.cast_nonneg _))
    have h4 : Real.exp (B * h * ((N + 1 : ℕ) : ℝ)) =
        Real.exp (B * h) * Real.exp (B * h * N) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    calc e (N + 1) ≤ (1 + B * h) * e N + D := hstep N
      _ ≤ Real.exp (B * h) * (Real.exp (B * h * N) * (e 0 + N * D)) + 1 * D := by
          rw [one_mul]; exact add_le_add h2 le_rfl
      _ ≤ Real.exp (B * h) * (Real.exp (B * h * N) * (e 0 + N * D)) +
          Real.exp (B * h * ((N + 1 : ℕ) : ℝ)) * D := by
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_right h3 hD)
      _ = Real.exp (B * h * ((N + 1 : ℕ) : ℝ)) * (e 0 + ((N + 1 : ℕ) : ℝ) * D) := by
          rw [h4]
          push_cast
          ring

/-- **Abstract order theorem for a compressed one-step method.**  `Φ` is a one-step map (Lipschitz
with constant `1 + L h`), `X (n+1)` is a quasi-best approximation of `Φ (X n)` from a set `𝓜` with
constant `Kq`.  `Y` is a reference sequence with local error `C h^(p+1)` for `Φ`, generated by maps
`S n` that keep `X n` in `𝓜` and differ from `Φ` by `O(h)` in the Lipschitz sense.  Then the error
of `X` is of order `p`.  The point: the quasi-optimality factor `Kq` enters only through `Kq Ks h`,
not as a factor `Kq` per step, because the comparison element `S n (X n)` has distance `O(h) · error
+ O(h^(p+1))` from `Φ (X n)`. -/
theorem global_order {E : Type*} [SeminormedAddCommGroup E] {X Y : ℕ → E} {Φ : E → E} {𝓜 : Set E}
    {S : ℕ → E → E} {h L Kq Ks C : ℝ} {p : ℕ} (hh : 0 ≤ h) (hL : 0 ≤ L) (hKq : 0 ≤ Kq)
    (hKs : 0 ≤ Ks) (hC : 0 ≤ C)
    (hΦ : ∀ a b, ‖Φ a - Φ b‖ ≤ (1 + L * h) * ‖a - b‖)
    (hstep : ∀ n V, V ∈ 𝓜 → ‖X (n + 1) - Φ (X n)‖ ≤ Kq * ‖V - Φ (X n)‖)
    (hSmem : ∀ n, S n (X n) ∈ 𝓜) (hSY : ∀ n, S n (Y n) = Y (n + 1))
    (hSΦ : ∀ n a b, ‖(S n a - Φ a) - (S n b - Φ b)‖ ≤ Ks * h * ‖a - b‖)
    (hcons : ∀ n, ‖Φ (Y n) - Y (n + 1)‖ ≤ C * h ^ (p + 1)) (N : ℕ) :
    ‖X N - Y N‖ ≤ Real.exp ((L + Kq * Ks) * h * N) *
      (‖X 0 - Y 0‖ + (1 + Kq) * C * h ^ p * (N * h)) := by
  have hD : 0 ≤ (1 + Kq) * (C * h ^ (p + 1)) := by positivity
  have hrec : ∀ n, ‖X (n + 1) - Y (n + 1)‖ ≤ (1 + (L + Kq * Ks) * h) * ‖X n - Y n‖ +
      (1 + Kq) * (C * h ^ (p + 1)) := by
    intro n
    set e := ‖X n - Y n‖ with he
    have h1 : ‖S n (X n) - Φ (X n)‖ ≤ Ks * h * e + C * h ^ (p + 1) := by
      have h2 := hSΦ n (X n) (Y n)
      have h3 : ‖S n (Y n) - Φ (Y n)‖ ≤ C * h ^ (p + 1) := by
        rw [hSY, norm_sub_rev]; exact hcons n
      calc ‖S n (X n) - Φ (X n)‖
          = ‖((S n (X n) - Φ (X n)) - (S n (Y n) - Φ (Y n))) + (S n (Y n) - Φ (Y n))‖ := by
            congr 1; abel
        _ ≤ _ := norm_add_le _ _
        _ ≤ _ := add_le_add h2 h3
    have h4 := hstep n _ (hSmem n)
    have h5 := hΦ (X n) (Y n)
    have h6 := hcons n
    calc ‖X (n + 1) - Y (n + 1)‖
        = ‖(X (n + 1) - Φ (X n)) + (Φ (X n) - Φ (Y n)) + (Φ (Y n) - Y (n + 1))‖ := by
          congr 1; abel
      _ ≤ ‖X (n + 1) - Φ (X n)‖ + ‖Φ (X n) - Φ (Y n)‖ + ‖Φ (Y n) - Y (n + 1)‖ :=
          norm_add₃_le
      _ ≤ Kq * (Ks * h * e + C * h ^ (p + 1)) + (1 + L * h) * e + C * h ^ (p + 1) := by
          refine add_le_add (add_le_add (h4.trans ?_) h5) h6
          exact mul_le_mul_of_nonneg_left h1 hKq
      _ = (1 + (L + Kq * Ks) * h) * e + (1 + Kq) * (C * h ^ (p + 1)) := by ring
  have hB : 0 ≤ L + Kq * Ks := by positivity
  have hmain := gronwall_discrete (e := fun n => ‖X n - Y n‖) hB hh hD
    (fun _ => norm_nonneg _) hrec N
  have heq : (N : ℝ) * ((1 + Kq) * (C * h ^ (p + 1))) = (1 + Kq) * C * h ^ p * (N * h) := by
    rw [pow_succ]; ring
  rw [heq] at hmain
  exact hmain

end Gronwall

section Truncation

variable {ι ι' : Type*} [Fintype ι] [Fintype ι']

open scoped LeanDLRA.Frobenius in
/-- The truncated SVD is quasi-optimal in the maximum norm with constant `√(m n)`. -/
lemma abs_sub_truncation_le [DecidableEq ι'] {A B : Matrix ι ι' ℝ} {r : ℕ} (hB : B.rank ≤ r) {d : ℝ}
    (hd : 0 ≤ d) (h : ∀ i j, |A i j - B i j| ≤ d) (i : ι) (j : ι') :
    |(A - LeanDLRA.EckartYoung.truncation A r) i j| ≤
      √((Fintype.card ι : ℝ) * Fintype.card ι') * d := by
  have h1 := LeanDLRA.Frobenius.abs_apply_le_norm (A - LeanDLRA.EckartYoung.truncation A r) i j
  have h2 := LeanDLRA.EckartYoung.norm_sub_truncation_le A hB
  have h3 : ‖A - B‖ ≤ √((Fintype.card ι : ℝ) * Fintype.card ι') * d := by
    rw [LeanDLRA.Frobenius.norm_def]
    have h4 : ∑ i, ∑ j, (A - B) i j ^ 2 ≤ (Fintype.card ι : ℝ) * Fintype.card ι' * d ^ 2 := by
      calc ∑ i, ∑ j, (A - B) i j ^ 2 ≤ ∑ _i : ι, ∑ _j : ι', d ^ 2 := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
            rw [Matrix.sub_apply, ← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (h i j) 2
        _ = (Fintype.card ι : ℝ) * Fintype.card ι' * d ^ 2 := by
            simp [Finset.card_univ]; ring
    calc √(∑ i, ∑ j, (A - B) i j ^ 2) ≤ √((Fintype.card ι : ℝ) * Fintype.card ι' * d ^ 2) :=
          Real.sqrt_le_sqrt h4
      _ = √((Fintype.card ι : ℝ) * Fintype.card ι') * d := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hd]
  linarith

variable (ι) in
/-- The matrix `𝟙 𝟙ᵀ`. -/
def onesMat : Matrix ι ι ℝ := fun _ _ => 1

variable (ι) in
/-- The centering projector `1 - 𝟙 𝟙ᵀ / m`. -/
noncomputable def centerMat [DecidableEq ι] : Matrix ι ι ℝ :=
  1 - (Fintype.card ι : ℝ)⁻¹ • onesMat ι

lemma centerMat_apply [DecidableEq ι] (i k : ι) :
    centerMat ι i k = (if i = k then 1 else 0) - (Fintype.card ι : ℝ)⁻¹ := by
  simp [centerMat, Matrix.sub_apply, Matrix.smul_apply, onesMat, Matrix.one_apply]

lemma card_inv_sum [Nonempty ι] : ∑ _k : ι, (Fintype.card ι : ℝ)⁻¹ = 1 := by
  have h : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [Finset.card_univ, h]

lemma center_row_sum [DecidableEq ι] [Nonempty ι] (i : ι) : ∑ k, centerMat ι i k = 0 := by
  simp only [centerMat_apply, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    card_inv_sum, sub_self]

lemma center_col_sum [DecidableEq ι] [Nonempty ι] (k : ι) : ∑ i, centerMat ι i k = 0 := by
  simp only [centerMat_apply, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    card_inv_sum, sub_self]

lemma center_mul_ones [DecidableEq ι] [Nonempty ι] : centerMat ι * onesMat ι = 0 := by
  ext i j
  simp [Matrix.mul_apply, onesMat, center_row_sum]

lemma ones_mul_center [DecidableEq ι] [Nonempty ι] : onesMat ι * centerMat ι = 0 := by
  ext i j
  simp [Matrix.mul_apply, onesMat, center_col_sum]

lemma center_idem [DecidableEq ι] [Nonempty ι] : centerMat ι * centerMat ι = centerMat ι := by
  have h : centerMat ι = 1 - (Fintype.card ι : ℝ)⁻¹ • onesMat ι := rfl
  nth_rewrite 2 [h]
  rw [Matrix.mul_sub, Matrix.mul_smul, center_mul_ones]
  simp

lemma one_sub_center [DecidableEq ι] :
    1 - centerMat ι = (Fintype.card ι : ℝ)⁻¹ • onesMat ι := by
  simp [centerMat]

lemma center_l1 [DecidableEq ι] [Nonempty ι] (i : ι) : ∑ k, |centerMat ι i k| ≤ 2 := by
  have hinv : (0 : ℝ) ≤ (Fintype.card ι : ℝ)⁻¹ := by positivity
  calc ∑ k, |centerMat ι i k|
      ≤ ∑ k, ((if i = k then (1 : ℝ) else 0) + (Fintype.card ι : ℝ)⁻¹) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [centerMat_apply]
        refine (abs_sub _ _).trans ?_
        rw [abs_of_nonneg hinv]
        split_ifs <;> simp
    _ = 2 := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
          card_inv_sum]
        norm_num

lemma center_l1' [DecidableEq ι] [Nonempty ι] (k : ι) : ∑ i, |centerMat ι i k| ≤ 2 := by
  have hinv : (0 : ℝ) ≤ (Fintype.card ι : ℝ)⁻¹ := by positivity
  calc ∑ i, |centerMat ι i k|
      ≤ ∑ i, ((if i = k then (1 : ℝ) else 0) + (Fintype.card ι : ℝ)⁻¹) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [centerMat_apply]
        refine (abs_sub _ _).trans ?_
        rw [abs_of_nonneg hinv]
        split_ifs <;> simp
    _ = 2 := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
          card_inv_sum]
        norm_num

variable [DecidableEq ι] [DecidableEq ι']

/-- Double centering `X ↦ P X P'`: removes the row and column means.  The kernel of `dc` consists of
the matrices `a 𝟙ᵀ + 𝟙 bᵀ`, the fluctuation `dc X` is what the truncation acts on. -/
noncomputable def dc (X : Matrix ι ι' ℝ) : Matrix ι ι' ℝ := centerMat ι * X * centerMat ι'

/-- The structure-preserving truncation: keep `X - dc X` (row and column means) exactly, truncate
the double-centered part by the SVD. -/
noncomputable def truncDC (r : ℕ) (W : Matrix ι ι' ℝ) : Matrix ι ι' ℝ :=
  (W - dc W) + LeanDLRA.EckartYoung.truncation (dc W) r

lemma dc_add (X Y : Matrix ι ι' ℝ) : dc (X + Y) = dc X + dc Y := by
  simp [dc, Matrix.mul_add, Matrix.add_mul]

lemma dc_sub (X Y : Matrix ι ι' ℝ) : dc (X - Y) = dc X - dc Y := by
  simp [dc, Matrix.mul_sub, Matrix.sub_mul]

lemma dc_smul (c : ℝ) (X : Matrix ι ι' ℝ) : dc (c • X) = c • dc X := by
  simp [dc, Matrix.mul_smul, Matrix.smul_mul]

lemma rank_dc_le (X : Matrix ι ι' ℝ) : (dc X).rank ≤ X.rank :=
  (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

lemma dc_dc [Nonempty ι] [Nonempty ι'] (X : Matrix ι ι' ℝ) : dc (dc X) = dc X := by
  have h1 : centerMat ι * (centerMat ι * X * centerMat ι') * centerMat ι' =
      (centerMat ι * centerMat ι) * X * (centerMat ι' * centerMat ι') := by
    simp only [Matrix.mul_assoc]
  simp only [dc]
  rw [h1, center_idem, center_idem]

lemma rank_smul_le' (c : ℝ) (M : Matrix ι ι' ℝ) : (c • M).rank ≤ M.rank := by
  have : c • M = (c • (1 : Matrix ι ι ℝ)) * M := by simp [Matrix.smul_mul]
  rw [this]
  exact Matrix.rank_mul_le_right _ _

lemma rank_dc_truncDC [Nonempty ι] [Nonempty ι'] (r : ℕ) (W : Matrix ι ι' ℝ) :
    (dc (truncDC r W)).rank ≤ r := by
  have h : dc (truncDC r W) = dc (LeanDLRA.EckartYoung.truncation (dc W) r) := by
    rw [truncDC, dc_add, dc_sub, dc_dc, sub_self, zero_add]
  rw [h]
  exact (rank_dc_le _).trans (LeanDLRA.EckartYoung.rank_truncation_le _ _)

lemma rank_ones_le : (onesMat ι).rank ≤ 1 := by
  have : onesMat ι = Matrix.vecMulVec (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) := by
    ext i j
    simp [onesMat, Matrix.vecMulVec_apply]
  rw [this]
  exact Matrix.rank_vecMulVec_le _ _

/-- A matrix whose fluctuation has rank at most `r` has rank at most `r + 2`. -/
lemma rank_le_add_two [Nonempty ι] [Nonempty ι'] {X : Matrix ι ι' ℝ} {r : ℕ}
    (hX : (dc X).rank ≤ r) : X.rank ≤ r + 2 := by
  have hdec : X = dc X + ((1 - centerMat ι) * X + centerMat ι * X * (1 - centerMat ι')) := by
    simp only [dc, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    abel
  have h1 : ((1 - centerMat ι) * X).rank ≤ 1 := by
    rw [one_sub_center]
    refine (Matrix.rank_mul_le_left _ _).trans ?_
    exact (rank_smul_le' _ _).trans rank_ones_le
  have h2 : (centerMat ι * X * (1 - centerMat ι')).rank ≤ 1 := by
    rw [one_sub_center]
    refine (Matrix.rank_mul_le_right _ _).trans ?_
    exact (rank_smul_le' _ _).trans rank_ones_le
  rw [hdec]
  refine (LeanDLRA.EckartYoung.rank_add_le _ _).trans ?_
  have := LeanDLRA.EckartYoung.rank_add_le ((1 - centerMat ι) * X)
    (centerMat ι * X * (1 - centerMat ι'))
  omega

/-- If the rows of `G` sum to one and the columns of `H` sum to one, then `X ↦ G X H` does not
increase the rank of the fluctuation. -/
lemma rank_dc_mul [Nonempty ι] [Nonempty ι'] {G : Matrix ι ι ℝ} {H : Matrix ι' ι' ℝ}
    (hG : ∀ i, ∑ k, G i k = 1) (hH : ∀ j, ∑ l, H l j = 1) (X : Matrix ι ι' ℝ) :
    (dc (G * X * H)).rank ≤ (dc X).rank := by
  have hGJ : G * onesMat ι = onesMat ι := by
    ext i j
    simp [Matrix.mul_apply, onesMat, hG]
  have hJH : onesMat ι' * H = onesMat ι' := by
    ext i j
    simp [Matrix.mul_apply, onesMat, hH]
  have h1 : centerMat ι * G * (1 - centerMat ι) = 0 := by
    rw [one_sub_center, Matrix.mul_smul, Matrix.mul_assoc, hGJ, center_mul_ones, smul_zero]
  have h2 : (1 - centerMat ι') * H * centerMat ι' = 0 := by
    rw [one_sub_center, Matrix.smul_mul, Matrix.smul_mul, hJH, ones_mul_center, smul_zero]
  have hdec : X = dc X + ((1 - centerMat ι) * X + centerMat ι * X * (1 - centerMat ι')) := by
    simp only [dc, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    abel
  have hkey : dc (G * X * H) = dc (G * dc X * H) := by
    have e1 : dc (G * ((1 - centerMat ι) * X) * H) = 0 := by
      have : dc (G * ((1 - centerMat ι) * X) * H) =
          (centerMat ι * G * (1 - centerMat ι)) * X * H * centerMat ι' := by
        simp only [dc, Matrix.mul_assoc]
      rw [this, h1]
      simp
    have e2 : dc (G * (centerMat ι * X * (1 - centerMat ι')) * H) = 0 := by
      have : dc (G * (centerMat ι * X * (1 - centerMat ι')) * H) =
          centerMat ι * G * centerMat ι * X * ((1 - centerMat ι') * H * centerMat ι') := by
        simp only [dc, Matrix.mul_assoc]
      rw [this, h2]
      simp
    conv_lhs => rw [hdec]
    simp only [Matrix.mul_add, Matrix.add_mul, dc_add, e1, e2, add_zero]
  rw [hkey]
  calc (dc (G * dc X * H)).rank ≤ (G * dc X * H).rank := rank_dc_le _
    _ ≤ (G * dc X).rank := Matrix.rank_mul_le_left _ _
    _ ≤ (dc X).rank := Matrix.rank_mul_le_right _ _

end Truncation

section NegativeTruncation

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **The SVD truncation of a nonnegative matrix need not be nonnegative, and is never nonnegative
along the barrier family.**  For `0 < t` small the truncated SVD of rank `2 + card κ` of the
nonnegative matrix `A_t = barrierMat κ 0 t` has a negative entry.  Rank-one truncation behaves
differently, see `exists_nonneg_rankOne_closer`. -/
theorem truncation_has_negative_entry {t : ℝ} (ht : 0 < t)
    (hsmall : 64 * ((Fintype.card κ : ℝ) + 1) * ((Fintype.card κ : ℝ) + 3) * t ≤ 1) :
    ¬ IsNonneg (LeanDLRA.EckartYoung.truncation (barrierMat κ 0 t) (2 + Fintype.card κ)) := by
  intro hnn
  set N : ℝ := (Fintype.card κ : ℝ) with hN
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have ht1 : t ≤ 1 := by
    have h3 : (3 : ℝ) ≤ (N + 1) * (N + 3) := by nlinarith
    have h4 : 64 * 3 * t ≤ 64 * ((N + 1) * (N + 3)) * t :=
      mul_le_mul_of_nonneg_right (by linarith) ht.le
    have h5 : 64 * ((N + 1) * (N + 3)) * t = 64 * (N + 1) * (N + 3) * t := by ring
    linarith
  set A := barrierMat κ 0 t with hA
  set T := LeanDLRA.EckartYoung.truncation A (2 + Fintype.card κ) with hT
  obtain ⟨Y, hY, hbd⟩ := barrier_rank_approx (κ := κ) (s := 0) (t := t) (by norm_num)
  have hsq : (t / (1 - 0)) ^ 2 = t ^ 2 := by simp
  rw [hsq] at hbd
  have hcard : ((Fintype.card (Fin 3 ⊕ κ) : ℕ) : ℝ) = N + 3 := by
    simp [hN]
    ring
  have hsqrt :
      √(((Fintype.card (Fin 3 ⊕ κ) : ℕ) : ℝ) * (Fintype.card (Fin 3 ⊕ κ) : ℕ)) = N + 3 := by
    rw [hcard, Real.sqrt_mul_self (by positivity)]
  have hclose : ∀ a b, |T a b - A a b| ≤ (N + 3) * t ^ 2 := by
    intro a b
    have h := abs_sub_truncation_le (r := 2 + Fintype.card κ) hY (by positivity) hbd a b
    rw [hsqrt] at h
    rw [abs_sub_comm]
    simpa [Matrix.sub_apply] using h
  have hε : 64 * (N + 1) * ((N + 3) * t ^ 2) ≤ t := by
    have : 64 * (N + 1) * ((N + 3) * t ^ 2) = (64 * (N + 1) * (N + 3) * t) * t := by ring
    rw [this]
    calc _ ≤ 1 * t := mul_le_mul_of_nonneg_right hsmall ht.le
      _ = t := one_mul t
  have h1 := barrier_rank_lower (s := 0) (t := t) (ε := (N + 3) * t ^ 2) le_rfl (by norm_num) ht ht1
    (by positivity) hε id id hnn hclose
  have h2 : T.rank ≤ 2 + Fintype.card κ := LeanDLRA.EckartYoung.rank_truncation_le _ _
  omega

end NegativeTruncation

section Limiter

attribute [local instance] Matrix.seminormedAddCommGroup Matrix.normedAddCommGroup
  Matrix.normedSpace

variable {ι ι' : Type*} [Fintype ι] [Fintype ι'] [Nonempty ι] [Nonempty ι']

local notation "Mat" => Matrix ι ι' ℝ

/-- The constant matrix. -/
def cst (c : ℝ) : Matrix ι ι' ℝ := fun _ _ => c

/-- The mean of all entries. -/
noncomputable def avg (X : Matrix ι ι' ℝ) : ℝ :=
  (∑ i, ∑ j, X i j) / ((Fintype.card ι : ℝ) * Fintype.card ι')

/-- All entries lie in `[a, b]` (a discrete maximum principle; `a = 0` is positivity). -/
def InBand (a b : ℝ) (X : Matrix ι ι' ℝ) : Prop := ∀ i j, X i j ∈ Icc a b

@[simp] lemma cst_apply (c : ℝ) (i : ι) (j : ι') : cst c i j = c := rfl

lemma card_ne : (Fintype.card ι : ℝ) * Fintype.card ι' ≠ 0 := by
  have h1 : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h2 : (Fintype.card ι' : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact mul_ne_zero h1 h2

lemma avg_add (X Y : Mat) : avg (X + Y) = avg X + avg Y := by
  simp only [avg, Matrix.add_apply, Finset.sum_add_distrib, add_div]

lemma avg_smul (c : ℝ) (X : Mat) : avg (c • X) = c * avg X := by
  simp only [avg, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_div_assoc]

lemma avg_sub (X Y : Mat) : avg (X - Y) = avg X - avg Y := by
  simp only [avg, Matrix.sub_apply, Finset.sum_sub_distrib, sub_div]

lemma avg_cst (c : ℝ) : avg (cst c : Mat) = c := by
  have h := card_ne (ι := ι) (ι' := ι')
  simp only [avg, cst, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

lemma abs_entry_le (X : Mat) (i : ι) (j : ι') : |X i j| ≤ ‖X‖ := by
  simpa [Real.norm_eq_abs] using Matrix.norm_apply_le_norm (A := X) (i := i) (j := j)

lemma norm_le_of_entry {X : Mat} {d : ℝ} (hd : 0 ≤ d) (h : ∀ i j, |X i j| ≤ d) : ‖X‖ ≤ d :=
  (Matrix.norm_le_iff hd).mpr fun i j => by simpa [Real.norm_eq_abs] using h i j

lemma abs_avg_le (X : Mat) : |avg X| ≤ ‖X‖ := by
  have hc := card_ne (ι := ι) (ι' := ι')
  have hpos : 0 < (Fintype.card ι : ℝ) * Fintype.card ι' := by positivity
  rw [avg, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  calc |∑ i, ∑ j, X i j| ≤ ∑ i, |∑ j, X i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |X i j| := Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, ∑ _j : ι', ‖X‖ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => abs_entry_le X i j
    _ = ‖X‖ * ((Fintype.card ι : ℝ) * Fintype.card ι') := by
        simp [Finset.card_univ]; ring

/-- Scaling of the fluctuation about `μ`. -/
def contract (μ θ : ℝ) (Y : Mat) : Mat := cst μ + θ • (Y - cst μ)

lemma contract_apply (μ θ : ℝ) (Y : Mat) (i : ι) (j : ι') :
    contract μ θ Y i j = μ + θ * (Y i j - μ) := by
  simp [contract, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply]

lemma avg_contract (μ θ : ℝ) (Y : Mat) : avg (contract μ θ Y) = μ + θ * (avg Y - μ) := by
  rw [contract, avg_add, avg_smul, avg_sub, avg_cst]

/-- A contraction about a point of the band stays in the band. -/
lemma contract_inBand {a b μ θ : ℝ} {Y : Mat} (hμ : μ ∈ Icc a b) (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (hY : InBand a b Y) : InBand a b (contract μ θ Y) := by
  intro i j
  rw [contract_apply]
  obtain ⟨h2, h3⟩ := hY i j
  obtain ⟨h4, h5⟩ := hμ
  constructor <;> nlinarith [mul_nonneg h0 (sub_nonneg.mpr h2), mul_nonneg h0 (sub_nonneg.mpr h3),
    mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h4),
    mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h5)]

/-- The clipping of a real number to `[a, b]`. -/
def clip (a b x : ℝ) : ℝ := max a (min x b)

lemma clip_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) : clip a b x ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩

lemma clip_of_mem {a b x : ℝ} (hx : x ∈ Icc a b) : clip a b x = x := by
  rw [clip, min_eq_left hx.2, max_eq_right hx.1]

/-- Clipping moves `x` by no more than the distance to any point of the interval. -/
lemma abs_sub_clip_le {a b x w : ℝ} (hw : w ∈ Icc a b) : |x - clip a b x| ≤ |x - w| := by
  obtain ⟨h1, h2⟩ := hw
  simp only [clip]
  rcases le_total x b with h3 | h3 <;> rcases le_total a x with h4 | h4
  · rw [min_eq_left h3, max_eq_right h4]
    simp [abs_nonneg]
  · rw [min_eq_left h3, max_eq_left h4]
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · have : a ≤ b := h1.trans h2
    rw [min_eq_right h3, max_eq_right this]
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · have : a ≤ b := h1.trans h2
    rw [min_eq_right h3, max_eq_right this]
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

/-- The sup distance of `Y` to the band `[a, b]`. -/
noncomputable def bandExcess (a b : ℝ) (Y : Mat) : ℝ := ‖Y - Y.map (clip a b)‖

lemma bandExcess_nonneg (a b : ℝ) (Y : Mat) : 0 ≤ bandExcess a b Y := norm_nonneg _

lemma mem_of_bandExcess {a b : ℝ} (hab : a ≤ b) (Y : Mat) (i : ι) (j : ι') :
    a - bandExcess a b Y ≤ Y i j ∧ Y i j ≤ b + bandExcess a b Y := by
  have h1 := abs_le.mp (abs_entry_le (Y - Y.map (clip a b)) i j)
  obtain ⟨h2, h3⟩ := clip_mem hab (Y i j)
  simp only [Matrix.sub_apply, Matrix.map_apply] at h1
  exact ⟨by rw [bandExcess]; linarith [h1.2], by rw [bandExcess]; linarith [h1.1]⟩

lemma bandExcess_le {a b d : ℝ} {Y W : Mat} (hd : 0 ≤ d) (hW : InBand a b W)
    (h : ∀ i j, |Y i j - W i j| ≤ d) : bandExcess a b Y ≤ d := by
  refine norm_le_of_entry hd fun i j => ?_
  simp only [Matrix.sub_apply, Matrix.map_apply]
  exact (abs_sub_clip_le (hW i j)).trans (h i j)

lemma bandExcess_eq_zero {a b : ℝ} {Y : Mat} (hY : InBand a b Y) : bandExcess a b Y = 0 := by
  refine le_antisymm ?_ (bandExcess_nonneg a b Y)
  exact bandExcess_le le_rfl hY fun i j => by simp

/-- The scaling limiter.  `W` is the (admissible) target, `Z` an inadmissible approximation of it,
e.g. a truncation.  The mean of `Z` is corrected to that of `W`, and the fluctuation is scaled about
the mean by the factor `θ = ρ / (ρ + δ)`, where `δ` is the sup distance to the band and `ρ` the
distance of the mean to the ends of the band. -/
noncomputable def limiter (a b : ℝ) (W Z : Mat) : Mat :=
  let μ := avg W
  let Y := Z + cst (μ - avg Z)
  let ρ := min (μ - a) (b - μ)
  contract μ (ρ / (ρ + bandExcess a b Y)) Y

/-- The band radius of the mean of `W`. -/
noncomputable def radius (a b : ℝ) (W : Mat) : ℝ := min (avg W - a) (b - avg W)

/-- **The scaling limiter.**  Let `W` take values in `[a, b]`, and let its mean have distance `ρ >
0` to the ends.  For every `Z`, `limiter a b W Z` takes values in `[a, b]`, has the mean of `W`, has
the form `c + θ Z` with `0 ≤ θ ≤ 1` (so, unlike the entrywise positive part, it adds at most one to
the rank) and satisfies `‖limiter a b W Z - W‖ ≤ (4 + 2 (b - a) / ρ) ‖Z - W‖` in the maximum norm.
It returns the mean-corrected `Z` when this is admissible.  This is the Zhang-Shu scaling limiter
with the global mean as reference (Zhang-Shu use local cell means, which are not low rank); the
constant is uniform for data with zero entries, since the reference is positive whatever `W` does.
It is what replaces the rank-destroying positive part in `positivePart_rank`. -/
theorem limiter_spec {a b : ℝ} {W : Mat} (Z : Mat) (hW : InBand a b W) (hρ : 0 < radius a b W) :
    InBand a b (limiter a b W Z) ∧ avg (limiter a b W Z) = avg W ∧
    (∃ c θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ limiter a b W Z = cst c + θ • Z) ∧
    ‖limiter a b W Z - W‖ ≤ (4 + 2 * (b - a) / radius a b W) * ‖Z - W‖ ∧
    (InBand a b (Z + cst (avg W - avg Z)) → limiter a b W Z = Z + cst (avg W - avg Z)) := by
  set μ := avg W with hμ
  set ρ := radius a b W with hρdef
  set Y : Mat := Z + cst (μ - avg Z) with hY
  set δ := bandExcess a b Y with hδ
  set τ := ‖Z - W‖ with hτ
  have hρa : ρ ≤ μ - a := min_le_left _ _
  have hρb : ρ ≤ b - μ := min_le_right _ _
  have hab : a ≤ b := by linarith
  have hμmem : μ ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hτ0 : 0 ≤ τ := norm_nonneg _
  have hδ0 : 0 ≤ δ := bandExcess_nonneg _ _ _
  have hlim : limiter a b W Z = contract μ (ρ / (ρ + δ)) Y := rfl
  have hden : 0 < ρ + δ := by linarith
  set θ := ρ / (ρ + δ) with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hden]; linarith
  have hθρ : θ * (ρ + δ) = ρ := by rw [hθ]; field_simp
  -- closeness of `Y` to `W`
  have hmean : |μ - avg Z| ≤ τ := by
    have h := abs_avg_le (Z - W)
    rw [avg_sub, abs_sub_comm] at h
    exact h
  have hYW : ∀ i j, |Y i j - W i j| ≤ 2 * τ := by
    intro i j
    have h1 := abs_entry_le (Z - W) i j
    have h2 : Y i j - W i j = (Z - W) i j + (μ - avg Z) := by
      simp [hY, Matrix.add_apply, Matrix.sub_apply]; ring
    rw [h2]
    calc _ ≤ |(Z - W) i j| + |μ - avg Z| := abs_add_le _ _
      _ ≤ 2 * τ := by linarith
  have hδτ : δ ≤ 2 * τ := bandExcess_le (by positivity) hW hYW
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- band
    rw [hlim]
    intro i j
    rw [contract_apply]
    obtain ⟨h1, h2⟩ := mem_of_bandExcess hab Y i j
    rw [← hδ] at h1 h2
    constructor
    · have h3 : θ * (Y i j - μ) ≥ θ * (a - δ - μ) :=
        mul_le_mul_of_nonneg_left (by linarith) hθ0
      have h4 : θ * (μ - a + δ) ≤ μ - a := by
        have h5 : θ * (μ - a + δ) = θ * (ρ + δ) + θ * (μ - a - ρ) := by ring
        have h6 : θ * (μ - a - ρ) ≤ 1 * (μ - a - ρ) :=
          mul_le_mul_of_nonneg_right hθ1 (by linarith)
        rw [h5, hθρ]
        linarith
      nlinarith
    · have h3 : θ * (Y i j - μ) ≤ θ * (b + δ - μ) :=
        mul_le_mul_of_nonneg_left (by linarith) hθ0
      have h4 : θ * (b - μ + δ) ≤ b - μ := by
        have h5 : θ * (b - μ + δ) = θ * (ρ + δ) + θ * (b - μ - ρ) := by ring
        have h6 : θ * (b - μ - ρ) ≤ 1 * (b - μ - ρ) :=
          mul_le_mul_of_nonneg_right hθ1 (by linarith)
        rw [h5, hθρ]
        linarith
      nlinarith
  · -- mean
    rw [hlim, avg_contract, hY, avg_add, avg_cst]
    ring
  · -- form
    refine ⟨μ + θ * (μ - avg Z - μ), θ, hθ0, hθ1, ?_⟩
    rw [hlim]
    ext i j
    rw [contract_apply]
    simp [hY, Matrix.add_apply, Matrix.smul_apply]
    ring
  · -- perturbation
    rw [hlim]
    have hbaρ : 0 ≤ (b - a) / ρ := div_nonneg (by linarith) hρ.le
    have hmain : 0 ≤ (4 + 2 * (b - a) / ρ) * τ := by
      have : 2 * (b - a) / ρ = 2 * ((b - a) / ρ) := by ring
      rw [this]
      positivity
    refine norm_le_of_entry hmain fun i j => ?_
    rw [Matrix.sub_apply, contract_apply]
    have h1 := abs_le.mp (hYW i j)
    have hWi := hW i j
    have h2 : |Y i j - μ| ≤ 2 * τ + (b - a) := by
      rw [abs_le]
      constructor <;> linarith [hWi.1, hWi.2, hμmem.1, hμmem.2, h1.1, h1.2]
    have h3 : 1 - θ = δ / (ρ + δ) := by
      rw [hθ]; field_simp; ring
    have h30 : 0 ≤ 1 - θ := by linarith
    have h4 : 1 - θ ≤ 2 * τ / ρ := by
      rw [h3]
      calc δ / (ρ + δ) ≤ δ / ρ := div_le_div_of_nonneg_left hδ0 hρ (by linarith)
        _ ≤ 2 * τ / ρ := div_le_div_of_nonneg_right hδτ hρ.le
    have h5 : |(1 - θ) * (Y i j - μ)| ≤ 2 * τ + 2 * τ * ((b - a) / ρ) := by
      rw [abs_mul, abs_of_nonneg h30]
      calc (1 - θ) * |Y i j - μ| ≤ (1 - θ) * (2 * τ + (b - a)) :=
            mul_le_mul_of_nonneg_left h2 h30
        _ = (1 - θ) * (2 * τ) + (1 - θ) * (b - a) := by ring
        _ ≤ 1 * (2 * τ) + 2 * τ / ρ * (b - a) := by
            refine add_le_add (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) ?_
            exact mul_le_mul_of_nonneg_right h4 (by linarith)
        _ = 2 * τ + 2 * τ * ((b - a) / ρ) := by ring
    have h6 : μ + θ * (Y i j - μ) - W i j = (Y i j - W i j) - (1 - θ) * (Y i j - μ) := by ring
    rw [h6]
    calc _ ≤ |Y i j - W i j| + |(1 - θ) * (Y i j - μ)| := abs_sub _ _
      _ ≤ 2 * τ + (2 * τ + 2 * τ * ((b - a) / ρ)) := add_le_add (hYW i j) h5
      _ = (4 + 2 * (b - a) / ρ) * τ := by ring
  · -- inactive
    intro hin
    have h0 : δ = 0 := bandExcess_eq_zero hin
    have hθ' : θ = 1 := by rw [hθ, h0, add_zero, div_self hρ.ne']
    rw [hlim, hθ']
    ext i j
    rw [contract_apply]
    ring

/-- A seminorm vanishing on constants, e.g. a total variation. -/
structure IsVariation (p : Mat → ℝ) : Prop where
  add_le : ∀ X Y, p (X + Y) ≤ p X + p Y
  smul : ∀ (c : ℝ) (X : Mat), p (c • X) = |c| * p X
  cst : ∀ c : ℝ, p (cst c : Mat) = 0

lemma IsVariation.sub_le {p : Mat → ℝ} (hp : IsVariation p) (X Y : Mat) :
    p (X - Y) ≤ p X + p Y := by
  have h := hp.add_le X ((-1 : ℝ) • Y)
  rw [hp.smul] at h
  simpa [sub_eq_add_neg] using h

lemma IsVariation.nonneg {p : Mat → ℝ} (hp : IsVariation p) (X : Mat) : 0 ≤ p X := by
  have h := hp.sub_le X X
  rw [sub_self] at h
  have h0 : p (0 : Mat) = 0 := by
    have := hp.smul 0 X
    simpa using this
  linarith

/-- The second limiter stage: if `p Y` exceeds the budget `ℓ`, scale the fluctuation of `Y` about
its mean down to meet the budget exactly. -/
noncomputable def tvStage (p : Mat → ℝ) (ℓ : ℝ) (Y : Mat) : Mat :=
  contract (avg Y) (if p Y ≤ ℓ then 1 else ℓ / p Y) Y

lemma contract_one (μ : ℝ) (Y : Mat) : contract μ 1 Y = Y := by
  ext i j
  rw [contract_apply]
  ring

/-- **The total-variation stage.**  For a seminorm `p` vanishing on constants, `tvStage p ℓ Y` obeys
`p ≤ ℓ`, keeps the mean, and is a contraction of `Y` about its mean, so it preserves every band
containing `Y`.  If an admissible `W` with `p W ≤ ℓ` is near `Y`, and `‖Y - mean‖ ≤ c p Y`, the
change is at most `c ‖p‖ ‖Y - W‖`. -/
theorem tvStage_spec {p : Mat → ℝ} (hp : IsVariation p) {ℓ c Λ : ℝ} (hℓ : 0 ≤ ℓ) {Y W : Mat}
    (hW : p W ≤ ℓ) (hc : 0 ≤ c) (hP : ‖Y - cst (avg Y)‖ ≤ c * p Y)
    (hΛ : p (Y - W) ≤ Λ * ‖Y - W‖) :
    p (tvStage p ℓ Y) ≤ ℓ ∧ avg (tvStage p ℓ Y) = avg Y ∧
    (∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ tvStage p ℓ Y = contract (avg Y) θ Y) ∧
    ‖tvStage p ℓ Y - Y‖ ≤ c * Λ * ‖Y - W‖ := by
  have hΛ0 : 0 ≤ c * Λ * ‖Y - W‖ := by
    have : 0 ≤ c * (Λ * ‖Y - W‖) := mul_nonneg hc ((hp.nonneg _).trans hΛ)
    calc _ ≤ c * (Λ * ‖Y - W‖) := this
      _ = c * Λ * ‖Y - W‖ := by ring
  by_cases hle : p Y ≤ ℓ
  · have ht : tvStage p ℓ Y = Y := by
      simp only [tvStage, hle, ↓reduceIte]
      exact contract_one _ _
    rw [ht, sub_self, norm_zero]
    exact ⟨hle, rfl, ⟨1, zero_le_one, le_rfl, (contract_one _ _).symm⟩, hΛ0⟩
  · have hlt : ℓ < p Y := not_le.mp hle
    have hpos : 0 < p Y := by linarith
    set θ := ℓ / p Y with hθ
    have hθ0 : 0 ≤ θ := by positivity
    have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hpos]; exact hlt.le
    have ht : tvStage p ℓ Y = contract (avg Y) θ Y := by
      simp only [tvStage, hle, ↓reduceIte, hθ]
    have hbudget : p (tvStage p ℓ Y) ≤ ℓ := by
      rw [ht, contract]
      have h1 := hp.add_le (cst (avg Y)) (θ • (Y - cst (avg Y)))
      rw [hp.cst, hp.smul, abs_of_nonneg hθ0, zero_add] at h1
      have h2 := hp.sub_le Y (cst (avg Y))
      rw [hp.cst, add_zero] at h2
      have h3 : θ * p Y = ℓ := by rw [hθ]; field_simp
      calc _ ≤ θ * p (Y - cst (avg Y)) := h1
        _ ≤ θ * p Y := mul_le_mul_of_nonneg_left h2 hθ0
        _ = ℓ := h3
    refine ⟨hbudget, ?_, ⟨θ, hθ0, hθ1, ht⟩, ?_⟩
    · rw [ht, avg_contract]
      ring
    · have h1 : tvStage p ℓ Y - Y = (θ - 1) • (Y - cst (avg Y)) := by
        rw [ht]
        ext i j
        rw [Matrix.sub_apply, contract_apply]
        simp [Matrix.smul_apply, Matrix.sub_apply]
        ring
      rw [h1, norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      have h2 : (1 - θ) * p Y = p Y - ℓ := by
        rw [hθ]; field_simp
      have h3 : p Y ≤ ℓ + p (Y - W) := by
        have := hp.add_le (Y - W) W
        rw [sub_add_cancel] at this
        linarith
      have h30 : 0 ≤ 1 - θ := by linarith
      calc -(θ - 1) * ‖Y - cst (avg Y)‖ = (1 - θ) * ‖Y - cst (avg Y)‖ := by ring
        _ ≤ (1 - θ) * (c * p Y) := mul_le_mul_of_nonneg_left hP h30
        _ = c * ((1 - θ) * p Y) := by ring
        _ = c * (p Y - ℓ) := by rw [h2]
        _ ≤ c * (Λ * ‖Y - W‖) := mul_le_mul_of_nonneg_left (by linarith) hc
        _ = c * Λ * ‖Y - W‖ := by ring

/-- A one-step map of a monotone, conservative scheme: linear, positive, constant preserving and
mean preserving. -/
structure IsMonotoneStep (E : Mat →ₗ[ℝ] Mat) : Prop where
  nonneg : ∀ X, IsNonneg X → IsNonneg (E X)
  const : ∀ c : ℝ, E (cst c) = cst c
  mass : ∀ X, avg (E X) = avg X

/-- A monotone step preserves every band: the discrete maximum principle. -/
theorem IsMonotoneStep.inBand {E : Mat →ₗ[ℝ] Mat} (hE : IsMonotoneStep E) {a b : ℝ} {X : Mat}
    (hX : InBand a b X) : InBand a b (E X) := by
  intro i j
  have h1 : IsNonneg (X - cst a) := fun k l => by
    simpa [Matrix.sub_apply] using (hX k l).1
  have h2 : IsNonneg (cst b - X) := fun k l => by
    simpa [Matrix.sub_apply] using (hX k l).2
  have h3 := hE.nonneg _ h1 i j
  have h4 := hE.nonneg _ h2 i j
  rw [map_sub, hE.const] at h3 h4
  simp only [Matrix.sub_apply, cst_apply] at h3 h4
  exact ⟨by linarith, by linarith⟩

/-- A monotone step is a contraction of the maximum norm. -/
theorem IsMonotoneStep.norm_le {E : Mat →ₗ[ℝ] Mat} (hE : IsMonotoneStep E) (X : Mat) :
    ‖E X‖ ≤ ‖X‖ := by
  have hb : InBand (-‖X‖) ‖X‖ X := fun i j => abs_le.mp (abs_entry_le X i j)
  exact norm_le_of_entry (norm_nonneg _) fun i j => abs_le.mpr (hE.inBand hb i j)

/-- Compositions of monotone steps are monotone steps. -/
theorem IsMonotoneStep.comp {E F : Mat →ₗ[ℝ] Mat} (hE : IsMonotoneStep E)
    (hF : IsMonotoneStep F) : IsMonotoneStep (E ∘ₗ F) where
  nonneg X hX := hE.nonneg _ (hF.nonneg _ hX)
  const c := by simp [hE.const, hF.const]
  mass X := by simp [hE.mass, hF.mass]

/-- **SSP combinations.**  Convex combinations of monotone steps are monotone steps; together with
`IsMonotoneStep.comp` this is the convexity argument behind the SSP methods of Gottlieb-Shu-Tadmor.
-/
theorem IsMonotoneStep.convex {E F : Mat →ₗ[ℝ] Mat} (hE : IsMonotoneStep E)
    (hF : IsMonotoneStep F) {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    IsMonotoneStep (c • E + (1 - c) • F) where
  nonneg X hX i j := by
    have h2 := hE.nonneg X hX i j
    have h3 := hF.nonneg X hX i j
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul]
    have : 0 ≤ 1 - c := by linarith
    positivity
  const c' := by
    simp only [LinearMap.add_apply, LinearMap.smul_apply, hE.const, hF.const]
    ext i j
    simp [Matrix.add_apply, Matrix.smul_apply]
    ring
  mass X := by
    simp only [LinearMap.add_apply, LinearMap.smul_apply, avg_add, avg_smul, hE.mass, hF.mass]
    ring

/-- The identity is a monotone step. -/
theorem isMonotoneStep_id : IsMonotoneStep (LinearMap.id : Mat →ₗ[ℝ] Mat) where
  nonneg _ hX := hX
  const _ := rfl
  mass _ := rfl

/-- The second-order SSP Runge-Kutta method (Heun) of a step `E`. -/
noncomputable def heun (E : Mat →ₗ[ℝ] Mat) : Mat →ₗ[ℝ] Mat :=
  (1 / 2 : ℝ) • LinearMap.id + (1 - 1 / 2 : ℝ) • (E ∘ₗ E)

theorem IsMonotoneStep.heun {E : Mat →ₗ[ℝ] Mat} (hE : IsMonotoneStep E) :
    IsMonotoneStep (heun E) :=
  isMonotoneStep_id.convex (hE.comp hE) (by norm_num) (by norm_num)

section Centered

variable [DecidableEq ι] [DecidableEq ι']

lemma norm_mul_left_le {A : Matrix ι ι ℝ} {α : ℝ} (hα : ∀ i, ∑ k, |A i k| ≤ α) (Y : Mat) :
    ‖A * Y‖ ≤ α * ‖Y‖ := by
  have hα0 : 0 ≤ α := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact (Finset.sum_nonneg fun _ _ => abs_nonneg _).trans (hα i)
  refine norm_le_of_entry (by positivity) fun i j => ?_
  rw [Matrix.mul_apply]
  calc |∑ k, A i k * Y k j| ≤ ∑ k, |A i k * Y k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, |A i k| * ‖Y‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_entry_le Y k j) (abs_nonneg _)
    _ = (∑ k, |A i k|) * ‖Y‖ := by rw [Finset.sum_mul]
    _ ≤ α * ‖Y‖ := mul_le_mul_of_nonneg_right (hα i) (norm_nonneg _)

lemma norm_mul_right_le {B : Matrix ι' ι' ℝ} {β : ℝ} (hβ : ∀ j, ∑ l, |B l j| ≤ β) (Y : Mat) :
    ‖Y * B‖ ≤ β * ‖Y‖ := by
  have hβ0 : 0 ≤ β := by
    obtain ⟨j⟩ := ‹Nonempty ι'›
    exact (Finset.sum_nonneg fun _ _ => abs_nonneg _).trans (hβ j)
  refine norm_le_of_entry (by positivity) fun i j => ?_
  rw [Matrix.mul_apply]
  calc |∑ l, Y i l * B l j| ≤ ∑ l, |Y i l * B l j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l, |B l j| * ‖Y‖ := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_left (abs_entry_le Y i l) (abs_nonneg _)
    _ = (∑ l, |B l j|) * ‖Y‖ := by rw [Finset.sum_mul]
    _ ≤ β * ‖Y‖ := mul_le_mul_of_nonneg_right (hβ j) (norm_nonneg _)

lemma norm_dc_le (Y : Mat) : ‖dc Y‖ ≤ 4 * ‖Y‖ := by
  have h1 := norm_mul_right_le (Y := centerMat ι * Y) (center_l1' (ι := ι'))
  have h2 := norm_mul_left_le (Y := Y) (center_l1 (ι := ι))
  calc ‖dc Y‖ ≤ 2 * ‖centerMat ι * Y‖ := h1
    _ ≤ 2 * (2 * ‖Y‖) := by linarith
    _ = 4 * ‖Y‖ := by ring

lemma dc_cst (c : ℝ) : dc (cst c : Mat) = 0 := by
  have h : centerMat ι * (cst c : Mat) = 0 := by
    ext i j
    simp only [Matrix.mul_apply, cst_apply, ← Finset.sum_mul, center_row_sum, zero_mul,
      Matrix.zero_apply]
  simp [dc, h]

/-- The structure-preserving truncation is quasi-optimal in the maximum norm on the class of
matrices whose fluctuation has rank at most `r`, with constant `4 √(m n)`.  (By Eckart-Young.) -/
theorem norm_truncDC_sub_le {r : ℕ} (W : Mat) {V : Mat} (hV : (dc V).rank ≤ r) :
    ‖truncDC r W - W‖ ≤ 4 * √((Fintype.card ι : ℝ) * Fintype.card ι') * ‖V - W‖ := by
  have hd : 0 ≤ 4 * ‖V - W‖ := by positivity
  have hclose : ∀ i j, |dc W i j - dc V i j| ≤ 4 * ‖V - W‖ := by
    intro i j
    have h1 := abs_entry_le (dc (W - V)) i j
    rw [dc_sub, Matrix.sub_apply] at h1
    have h2 := norm_dc_le (W - V)
    rw [dc_sub] at h2
    rw [norm_sub_rev V W]
    linarith
  refine norm_le_of_entry (by positivity) fun i j => ?_
  have h3 := abs_sub_truncation_le hV hd hclose i j
  have h4 : (truncDC r W - W) i j =
      -(dc W - LeanDLRA.EckartYoung.truncation (dc W) r) i j := by
    simp only [truncDC, Matrix.sub_apply, Matrix.add_apply]
    ring
  rw [h4, abs_neg]
  calc _ ≤ _ := h3
    _ = 4 * √((Fintype.card ι : ℝ) * Fintype.card ι') * ‖V - W‖ := by ring

/-- **Core of the error analysis of limited low-rank schemes.**  `Φ` is a monotone step.  Each step
of `X` applies the truncation `truncDC r` to `Φ (X n)` and a limiter that keeps the band `[a, b]`
and the mean, returns `c + θ Z`, and is quasi-optimal with constant `K`.  Then all invariants hold,
and if the reference `Y (n+1) = G n * Y n * H n` has local error `C h^(p+1)` for `Φ`, the error is
of order `p`. -/
theorem scheme_core {a b K h Ks C : ℝ} {r p : ℕ} {Φ : Mat →ₗ[ℝ] Mat} (hΦ : IsMonotoneStep Φ)
    {X Y : ℕ → Mat} {G : ℕ → Matrix ι ι ℝ} {H : ℕ → Matrix ι' ι' ℝ}
    (hK : 0 ≤ K) (hh : 0 ≤ h) (hKs : 0 ≤ Ks) (hC : 0 ≤ C)
    (hX0 : InBand a b (X 0)) (hX0r : (dc (X 0)).rank ≤ r)
    (hstep : ∀ n, InBand a b (X n) → avg (X n) = avg (X 0) →
      InBand a b (X (n + 1)) ∧ avg (X (n + 1)) = avg (Φ (X n)) ∧
      (∃ c θ : ℝ, X (n + 1) = cst c + θ • truncDC r (Φ (X n))) ∧
      ‖X (n + 1) - Φ (X n)‖ ≤ K * ‖truncDC r (Φ (X n)) - Φ (X n)‖)
    (hGs : ∀ n i, ∑ k, G n i k = 1) (hHs : ∀ n j, ∑ l, H n l j = 1)
    (hY : ∀ n, Y (n + 1) = G n * Y n * H n)
    (hSΦ : ∀ n Z, ‖G n * Z * H n - Φ Z‖ ≤ Ks * h * ‖Z‖)
    (hcons : ∀ n, ‖Φ (Y n) - Y (n + 1)‖ ≤ C * h ^ (p + 1)) :
    (∀ n, InBand a b (X n) ∧ avg (X n) = avg (X 0) ∧ (dc (X n)).rank ≤ r ∧ (X n).rank ≤ r + 2) ∧
    ∀ N : ℕ, ‖X N - Y N‖ ≤
      Real.exp ((K * (4 * √((Fintype.card ι : ℝ) * Fintype.card ι')) * Ks) * h * N) *
      (‖X 0 - Y 0‖ +
        (1 + K * (4 * √((Fintype.card ι : ℝ) * Fintype.card ι'))) * C * h ^ p * (N * h)) := by
  have hinv : ∀ n, InBand a b (X n) ∧ avg (X n) = avg (X 0) ∧ (dc (X n)).rank ≤ r := by
    intro n
    induction n with
    | zero => exact ⟨hX0, rfl, hX0r⟩
    | succ n ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      obtain ⟨h4, h5, ⟨c, θ, h6⟩, -⟩ := hstep n h1 h2
      refine ⟨h4, h5.trans ((hΦ.mass _).trans h2), ?_⟩
      rw [h6, dc_add, dc_cst, zero_add, dc_smul]
      exact (rank_smul_le' _ _).trans (rank_dc_truncDC r _)
  refine ⟨fun n => ⟨(hinv n).1, (hinv n).2.1, (hinv n).2.2, rank_le_add_two (hinv n).2.2⟩,
    fun N => ?_⟩
  set Λ := 4 * √((Fintype.card ι : ℝ) * Fintype.card ι') with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  have hmain := global_order (X := X) (Y := Y) (Φ := fun Z => Φ Z)
    (𝓜 := {V : Mat | (dc V).rank ≤ r}) (S := fun n Z => G n * Z * H n) (h := h) (L := 0)
    (Kq := K * Λ) (Ks := Ks) (C := C) (p := p) hh le_rfl (by positivity) hKs hC
    (fun A B => by
      have : Φ A - Φ B = Φ (A - B) := (map_sub Φ A B).symm
      rw [this]
      simpa using hΦ.norm_le (A - B))
    (fun n V hV => by
      obtain ⟨h1, h2, h3⟩ := hinv n
      obtain ⟨-, -, -, h4⟩ := hstep n h1 h2
      have h5 := norm_truncDC_sub_le (Φ (X n)) hV
      calc _ ≤ K * ‖truncDC r (Φ (X n)) - Φ (X n)‖ := h4
        _ ≤ K * (Λ * ‖V - Φ (X n)‖) := mul_le_mul_of_nonneg_left h5 hK
        _ = K * Λ * ‖V - Φ (X n)‖ := by ring)
    (fun n => (rank_dc_mul (hGs n) (hHs n) (X n)).trans (hinv n).2.2)
    (fun n => (hY n).symm)
    (fun n A B => by
      have heq : (G n * A * H n - Φ A) - (G n * B * H n - Φ B) =
          G n * (A - B) * H n - Φ (A - B) := by
        rw [map_sub, Matrix.mul_sub, Matrix.sub_mul]
        abel
      rw [heq]
      exact hSΦ n _)
    hcons N
  simpa using hmain

/-- The constant of the scaling limiter for a mean of band radius `ρ`. -/
noncomputable def limK (a b ρ : ℝ) : ℝ := 4 + 2 * (b - a) / ρ

lemma radius_step {a b : ℝ} {W X₀ : Mat} (h : avg W = avg X₀) : radius a b W = radius a b X₀ := by
  simp only [radius, h]

/-- **The limited low-rank scheme: positivity, conservation, low rank, order.**  `Φ` is a monotone
step (for instance an SSP Runge-Kutta combination of forward Euler steps of a monotone scheme,
`IsMonotoneStep.convex`), and `X (n+1) = limiter a b (Φ (X n)) (truncDC r (Φ (X n)))`. Then every `X
n` lies in the band `[a, b]` (positivity for `a = 0`), has the mean of `X 0` and has rank at most `r
+ 2`.  If moreover `Y (n+1) = G n * Y n * H n` has local error `C h^(p+1)` for `Φ`, and `G n, H n`
are `O(h)` perturbations of `Φ` (rows of `G n` and columns of `H n` summing to one), the error is
`O(h^p)`.  `Y` need not be smooth: only the maximum norm enters, so discontinuous data are allowed,
at a fixed spatial mesh; the constants grow with the mesh size through `√(m n)` and the rates of
`Φ`.  Note that `K Λ Ks` hides the conditioning of `G n, H n`, and that order refers to time
integration and compression: a linear monotone `Φ` remains subject to Godunov's order barrier in
space. -/
theorem limited_scheme {a b h Ks C : ℝ} {r p : ℕ} {Φ : Mat →ₗ[ℝ] Mat} (hΦ : IsMonotoneStep Φ)
    {X Y : ℕ → Mat} {G : ℕ → Matrix ι ι ℝ} {H : ℕ → Matrix ι' ι' ℝ}
    (hh : 0 ≤ h) (hKs : 0 ≤ Ks) (hC : 0 ≤ C)
    (hX0 : InBand a b (X 0)) (hX0r : (dc (X 0)).rank ≤ r) (hρ : 0 < radius a b (X 0))
    (hX : ∀ n, X (n + 1) = limiter a b (Φ (X n)) (truncDC r (Φ (X n))))
    (hGs : ∀ n i, ∑ k, G n i k = 1) (hHs : ∀ n j, ∑ l, H n l j = 1)
    (hY : ∀ n, Y (n + 1) = G n * Y n * H n)
    (hSΦ : ∀ n Z, ‖G n * Z * H n - Φ Z‖ ≤ Ks * h * ‖Z‖)
    (hcons : ∀ n, ‖Φ (Y n) - Y (n + 1)‖ ≤ C * h ^ (p + 1)) :
    (∀ n, InBand a b (X n) ∧ avg (X n) = avg (X 0) ∧ (dc (X n)).rank ≤ r ∧ (X n).rank ≤ r + 2) ∧
    ∀ N : ℕ, ‖X N - Y N‖ ≤
      Real.exp ((limK a b (radius a b (X 0)) * (4 * √((Fintype.card ι : ℝ) * Fintype.card ι')) *
        Ks) * h * N) *
      (‖X 0 - Y 0‖ + (1 + limK a b (radius a b (X 0)) *
        (4 * √((Fintype.card ι : ℝ) * Fintype.card ι'))) * C * h ^ p * (N * h)) := by
  have hab : 0 ≤ b - a := by
    have h1 : radius a b (X 0) ≤ avg (X 0) - a := min_le_left _ _
    have h2 : radius a b (X 0) ≤ b - avg (X 0) := min_le_right _ _
    linarith
  have hK : 0 ≤ limK a b (radius a b (X 0)) := by
    rw [limK]
    positivity
  refine scheme_core hΦ hK hh hKs hC hX0 hX0r (fun n h1 h2 => ?_) hGs hHs hY hSΦ hcons
  have hrad : radius a b (Φ (X n)) = radius a b (X 0) := radius_step ((hΦ.mass _).trans h2)
  obtain ⟨h3, h4, ⟨c, θ, -, -, h5⟩, h6, -⟩ :=
    limiter_spec (truncDC r (Φ (X n))) (hΦ.inBand h1) (by rw [hrad]; exact hρ)
  rw [← hX n] at h3 h4 h5 h6
  rw [hrad] at h6
  exact ⟨h3, h4, ⟨c, θ, h5⟩, h6⟩

/-- **The limited scheme with exact total variation control.**  With an additional scaling stage the
scheme of `limited_scheme` satisfies `v (X (n+1)) ≤ v (X n)` exactly for a seminorm `v` that
vanishes on constants, is not increased by `Φ`, satisfies a Poincaré inequality `‖Y - mean‖ ≤ c v Y`
and is bounded by `Λ` times the maximum norm.  The price of the second stage is the factor `1 + c Λ`
in the quasi-optimality constant, which is mesh dependent for a total variation. -/
theorem limited_scheme_tv {a b h Ks C c Λ : ℝ} {r p : ℕ} {Φ : Mat →ₗ[ℝ] Mat}
    (hΦ : IsMonotoneStep Φ) {v : Mat → ℝ} (hv : IsVariation v) (hc : 0 ≤ c) (hΛ0 : 0 ≤ Λ)
    (hP : ∀ Y : Mat, ‖Y - cst (avg Y)‖ ≤ c * v Y) (hΛ : ∀ Y : Mat, v Y ≤ Λ * ‖Y‖)
    (hvΦ : ∀ Z, v (Φ Z) ≤ v Z)
    {X Y : ℕ → Mat} {G : ℕ → Matrix ι ι ℝ} {H : ℕ → Matrix ι' ι' ℝ}
    (hh : 0 ≤ h) (hKs : 0 ≤ Ks) (hC : 0 ≤ C)
    (hX0 : InBand a b (X 0)) (hX0r : (dc (X 0)).rank ≤ r) (hρ : 0 < radius a b (X 0))
    (hX : ∀ n, X (n + 1) = tvStage v (v (X n)) (limiter a b (Φ (X n)) (truncDC r (Φ (X n)))))
    (hGs : ∀ n i, ∑ k, G n i k = 1) (hHs : ∀ n j, ∑ l, H n l j = 1)
    (hY : ∀ n, Y (n + 1) = G n * Y n * H n)
    (hSΦ : ∀ n Z, ‖G n * Z * H n - Φ Z‖ ≤ Ks * h * ‖Z‖)
    (hcons : ∀ n, ‖Φ (Y n) - Y (n + 1)‖ ≤ C * h ^ (p + 1)) :
    (∀ n, InBand a b (X n) ∧ avg (X n) = avg (X 0) ∧ (dc (X n)).rank ≤ r ∧ (X n).rank ≤ r + 2) ∧
    (∀ n, v (X (n + 1)) ≤ v (X n)) ∧
    ∀ N : ℕ, ‖X N - Y N‖ ≤
      Real.exp (((1 + c * Λ) * limK a b (radius a b (X 0)) *
        (4 * √((Fintype.card ι : ℝ) * Fintype.card ι')) * Ks) * h * N) *
      (‖X 0 - Y 0‖ + (1 + (1 + c * Λ) * limK a b (radius a b (X 0)) *
        (4 * √((Fintype.card ι : ℝ) * Fintype.card ι'))) * C * h ^ p * (N * h)) := by
  have hab : 0 ≤ b - a := by
    have h1 : radius a b (X 0) ≤ avg (X 0) - a := min_le_left _ _
    have h2 : radius a b (X 0) ≤ b - avg (X 0) := min_le_right _ _
    linarith
  have hK : 0 ≤ limK a b (radius a b (X 0)) := by
    rw [limK]
    positivity
  have hK' : 0 ≤ (1 + c * Λ) * limK a b (radius a b (X 0)) := by positivity
  have hvd : ∀ n, v (X (n + 1)) ≤ v (X n) := by
    intro n
    rw [hX n]
    exact (tvStage_spec hv (hv.nonneg _) (hvΦ (X n)) hc (hP _) (hΛ _)).1
  have hcore := scheme_core (K := (1 + c * Λ) * limK a b (radius a b (X 0))) hΦ hK' hh hKs hC
    (X := X) hX0 hX0r (r := r) (Φ := Φ) ?_ hGs hHs hY hSΦ hcons
  · exact ⟨hcore.1, hvd, hcore.2⟩
  · intro n h1 h2
    have hrad : radius a b (Φ (X n)) = radius a b (X 0) := radius_step ((hΦ.mass _).trans h2)
    obtain ⟨h3, h4, ⟨c₀, θ₀, -, -, h5⟩, h6, -⟩ :=
      limiter_spec (truncDC r (Φ (X n))) (hΦ.inBand h1) (by rw [hrad]; exact hρ)
    rw [hrad] at h6
    set W := Φ (X n) with hW
    set Z := truncDC r W with hZ
    set L := limiter a b W Z with hL
    obtain ⟨-, h8, ⟨θ, hθ0, hθ1, h9⟩, h10⟩ :=
      tvStage_spec hv (hv.nonneg _) (hvΦ (X n)) hc (hP L) (hΛ (L - W))
    have hout : X (n + 1) = tvStage v (v (X n)) L := hX n
    have hμ : avg L ∈ Icc a b := by
      have e1 : radius a b W ≤ avg W - a := min_le_left _ _
      have e2 : radius a b W ≤ b - avg W := min_le_right _ _
      rw [hrad] at e1 e2
      rw [h4]
      exact ⟨by linarith, by linarith⟩
    refine ⟨?_, ?_, ⟨avg L + θ * (c₀ - avg L), θ * θ₀, ?_⟩, ?_⟩
    · rw [hout, h9]
      exact contract_inBand hμ hθ0 hθ1 h3
    · rw [hout, h8, h4]
    · rw [hout, h9]
      ext i j
      rw [contract_apply, h5]
      simp [Matrix.add_apply, Matrix.smul_apply]
      ring
    · rw [hout]
      calc ‖tvStage v (v (X n)) L - W‖
          = ‖(tvStage v (v (X n)) L - L) + (L - W)‖ := by congr 1; abel
        _ ≤ ‖tvStage v (v (X n)) L - L‖ + ‖L - W‖ := norm_add_le _ _
        _ ≤ c * Λ * ‖L - W‖ + ‖L - W‖ := by linarith
        _ = (1 + c * Λ) * ‖L - W‖ := by ring
        _ ≤ (1 + c * Λ) * (limK a b (radius a b (X 0)) * ‖Z - W‖) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact h6
        _ = (1 + c * Λ) * limK a b (radius a b (X 0)) * ‖Z - W‖ := by ring

/-- **A posteriori bound for every monotone scheme, without any assumption on the solution.**  For
every monotone step `Φ` the limited scheme stays in the band, conserves the mean, has rank at most
`r + 2` after the first step, and `‖X N - Φ^N (X 0)‖ ≤ K ∑_{n < N} ‖truncDC r (Φ (X n)) - Φ (X n)‖`
with the maximum norm and `K = 4 + 2 (b - a) / ρ`: the truncation errors add up with the factor `K`
only once, they do not get amplified.  The reason is that `Φ` is a contraction and that the
undershoot of the truncation at step `n` is bounded by the truncation error of step `n` alone, since
`Φ (X n)` is admissible.  This covers discontinuous solutions; the sum is computable from the
discarded singular values.  It is a bound relative to the full scheme, and it is sharp only as far
as `K` is. -/
theorem limited_scheme_aposteriori {a b : ℝ} {r : ℕ} {Φ : Mat →ₗ[ℝ] Mat} (hΦ : IsMonotoneStep Φ)
    {X : ℕ → Mat} (hX0 : InBand a b (X 0)) (hρ : 0 < radius a b (X 0))
    (hX : ∀ n, X (n + 1) = limiter a b (Φ (X n)) (truncDC r (Φ (X n)))) :
    (∀ n, InBand a b (X n) ∧ avg (X n) = avg (X 0)) ∧ (∀ n, (X (n + 1)).rank ≤ r + 2) ∧
    ∀ N : ℕ, ‖X N - (Φ ^ N) (X 0)‖ ≤ limK a b (radius a b (X 0)) *
      ∑ n ∈ Finset.range N, ‖truncDC r (Φ (X n)) - Φ (X n)‖ := by
  have hinv : ∀ n, InBand a b (X n) ∧ avg (X n) = avg (X 0) := by
    intro n
    induction n with
    | zero => exact ⟨hX0, rfl⟩
    | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      have hrad : radius a b (Φ (X n)) = radius a b (X 0) := radius_step ((hΦ.mass _).trans h2)
      obtain ⟨h3, h4, -, -, -⟩ :=
        limiter_spec (truncDC r (Φ (X n))) (hΦ.inBand h1) (by rw [hrad]; exact hρ)
      rw [← hX n] at h3 h4
      exact ⟨h3, h4.trans ((hΦ.mass _).trans h2)⟩
  have hlocal : ∀ n, (∃ c θ : ℝ, X (n + 1) = cst c + θ • truncDC r (Φ (X n))) ∧
      ‖X (n + 1) - Φ (X n)‖ ≤ limK a b (radius a b (X 0)) * ‖truncDC r (Φ (X n)) - Φ (X n)‖ := by
    intro n
    obtain ⟨h1, h2⟩ := hinv n
    have hrad : radius a b (Φ (X n)) = radius a b (X 0) := radius_step ((hΦ.mass _).trans h2)
    obtain ⟨-, -, ⟨c, θ, -, -, h5⟩, h6, -⟩ :=
      limiter_spec (truncDC r (Φ (X n))) (hΦ.inBand h1) (by rw [hrad]; exact hρ)
    rw [← hX n] at h5 h6
    rw [hrad] at h6
    exact ⟨⟨c, θ, h5⟩, h6⟩
  refine ⟨hinv, fun n => ?_, fun N => ?_⟩
  · obtain ⟨⟨c, θ, h5⟩, -⟩ := hlocal n
    refine rank_le_add_two ?_
    rw [h5, dc_add, dc_cst, zero_add, dc_smul]
    exact (rank_smul_le' _ _).trans (rank_dc_truncDC r _)
  · induction N with
    | zero => simp
    | succ N ih =>
      have e1 : (Φ ^ (N + 1)) (X 0) = Φ ((Φ ^ N) (X 0)) := by
        rw [pow_succ', mul_apply_eq_comp]
      have e2 := hΦ.norm_le (X N - (Φ ^ N) (X 0))
      rw [map_sub] at e2
      have e3 := (hlocal N).2
      rw [Finset.sum_range_succ, mul_add, e1]
      calc ‖X (N + 1) - Φ ((Φ ^ N) (X 0))‖
          = ‖(X (N + 1) - Φ (X N)) + (Φ (X N) - Φ ((Φ ^ N) (X 0)))‖ := by
            congr 1; abel
        _ ≤ ‖X (N + 1) - Φ (X N)‖ + ‖Φ (X N) - Φ ((Φ ^ N) (X 0))‖ := norm_add_le _ _
        _ ≤ _ := by linarith

end Centered

section Advection

variable [DecidableEq ι] [DecidableEq ι']

/-- The second-order expansion `1 + M + M²/2`. -/
noncomputable def taylor2 {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) :
    Matrix n n ℝ := 1 + M + (1 / 2 : ℝ) • (M * M)

/-- **Defect of Heun's method against a rank-preserving step.**  If `E Z = Z + A Z + Z B` then
Heun's method `heun E` differs from the rank-preserving map `Z ↦ taylor2 A * Z * taylor2 B` by cubic
terms.  This is what makes the rank-preserving reference second-order consistent with the SSP method
in the Sylvester case. -/
theorem heun_sylvester {A : Matrix ι ι ℝ} {B : Matrix ι' ι' ℝ} {E : Mat →ₗ[ℝ] Mat}
    (hE : ∀ Z, E Z = Z + A * Z + Z * B) {α β : ℝ} (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β)
    (hα : ∀ Z : Mat, ‖A * Z‖ ≤ α * ‖Z‖) (hβ : ∀ Z : Mat, ‖Z * B‖ ≤ β * ‖Z‖) (Z : Mat) :
    ‖taylor2 A * Z * taylor2 B - heun E Z‖ ≤
      (α ^ 2 * β / 2 + α * β ^ 2 / 2 + α ^ 2 * β ^ 2 / 4) * ‖Z‖ := by
  have hheun : heun E Z = (1 / 2 : ℝ) • Z + (1 / 2 : ℝ) • E (E Z) := by
    simp only [heun, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.comp_apply]
    norm_num
  have hid : taylor2 A * Z * taylor2 B - heun E Z =
      (1 / 2 : ℝ) • (A * (A * Z) * B) + (1 / 2 : ℝ) • (A * Z * (B * B)) +
        (1 / 4 : ℝ) • (A * (A * Z) * (B * B)) := by
    rw [hheun, hE (E Z), hE Z]
    simp only [taylor2, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, smul_add, smul_smul]
    module
  have h1 : ‖A * (A * Z)‖ ≤ α ^ 2 * ‖Z‖ := by
    calc _ ≤ α * ‖A * Z‖ := hα _
      _ ≤ α * (α * ‖Z‖) := mul_le_mul_of_nonneg_left (hα _) hα0
      _ = α ^ 2 * ‖Z‖ := by ring
  have h2 : ∀ W : Mat, ‖W * (B * B)‖ ≤ β ^ 2 * ‖W‖ := by
    intro W
    rw [← Matrix.mul_assoc]
    calc _ ≤ β * ‖W * B‖ := hβ _
      _ ≤ β * (β * ‖W‖) := mul_le_mul_of_nonneg_left (hβ _) hβ0
      _ = β ^ 2 * ‖W‖ := by ring
  have t1 : ‖A * (A * Z) * B‖ ≤ α ^ 2 * β * ‖Z‖ := by
    calc _ ≤ β * ‖A * (A * Z)‖ := hβ _
      _ ≤ β * (α ^ 2 * ‖Z‖) := mul_le_mul_of_nonneg_left h1 hβ0
      _ = α ^ 2 * β * ‖Z‖ := by ring
  have t2 : ‖A * Z * (B * B)‖ ≤ α * β ^ 2 * ‖Z‖ := by
    calc _ ≤ β ^ 2 * ‖A * Z‖ := h2 _
      _ ≤ β ^ 2 * (α * ‖Z‖) := mul_le_mul_of_nonneg_left (hα _) (by positivity)
      _ = α * β ^ 2 * ‖Z‖ := by ring
  have t3 : ‖A * (A * Z) * (B * B)‖ ≤ α ^ 2 * β ^ 2 * ‖Z‖ := by
    calc _ ≤ β ^ 2 * ‖A * (A * Z)‖ := h2 _
      _ ≤ β ^ 2 * (α ^ 2 * ‖Z‖) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = α ^ 2 * β ^ 2 * ‖Z‖ := by ring
  rw [hid]
  have n1 := norm_smul (1 / 2 : ℝ) (A * (A * Z) * B)
  have n2 := norm_smul (1 / 2 : ℝ) (A * Z * (B * B))
  have n3 := norm_smul (1 / 4 : ℝ) (A * (A * Z) * (B * B))
  have r1 : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
  have r2 : ‖(1 / 4 : ℝ)‖ = 1 / 4 := by norm_num
  rw [r1] at n1 n2
  rw [r2] at n3
  calc _ ≤ ‖(1 / 2 : ℝ) • (A * (A * Z) * B)‖ + ‖(1 / 2 : ℝ) • (A * Z * (B * B))‖ +
        ‖(1 / 4 : ℝ) • (A * (A * Z) * (B * B))‖ := norm_add₃_le
    _ ≤ (α ^ 2 * β / 2 + α * β ^ 2 / 2 + α ^ 2 * β ^ 2 / 4) * ‖Z‖ := by
        rw [n1, n2, n3]
        nlinarith

/-- The upwind step for two-dimensional periodic advection with CFL numbers `c₁`, `c₂`: entries are
convex combinations of the entry and its two upwind neighbours along the permutations `σ`, `σ'`. -/
noncomputable def shiftStep (σ : Equiv.Perm ι) (σ' : Equiv.Perm ι') (c₁ c₂ : ℝ) :
    Mat →ₗ[ℝ] Mat where
  toFun X := fun i j => (1 - c₁ - c₂) * X i j + c₁ * X (σ i) j + c₂ * X i (σ' j)
  map_add' X Y := by
    ext i j
    change (1 - c₁ - c₂) * (X + Y) i j + c₁ * (X + Y) (σ i) j + c₂ * (X + Y) i (σ' j) =
      ((1 - c₁ - c₂) * X i j + c₁ * X (σ i) j + c₂ * X i (σ' j)) +
        ((1 - c₁ - c₂) * Y i j + c₁ * Y (σ i) j + c₂ * Y i (σ' j))
    simp only [Matrix.add_apply]
    ring
  map_smul' c X := by
    ext i j
    change (1 - c₁ - c₂) * (c • X) i j + c₁ * (c • X) (σ i) j + c₂ * (c • X) i (σ' j) =
      c * ((1 - c₁ - c₂) * X i j + c₁ * X (σ i) j + c₂ * X i (σ' j))
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring

lemma shiftStep_apply (σ : Equiv.Perm ι) (σ' : Equiv.Perm ι') (c₁ c₂ : ℝ) (X : Mat) (i : ι)
    (j : ι') : shiftStep σ σ' c₁ c₂ X i j =
      (1 - c₁ - c₂) * X i j + c₁ * X (σ i) j + c₂ * X i (σ' j) := rfl

/-- The upwind step is a monotone step under the CFL condition. -/
theorem isMonotoneStep_shiftStep (σ : Equiv.Perm ι) (σ' : Equiv.Perm ι') {c₁ c₂ : ℝ}
    (h1 : 0 ≤ c₁) (h2 : 0 ≤ c₂) (h3 : c₁ + c₂ ≤ 1) : IsMonotoneStep (shiftStep σ σ' c₁ c₂) where
  nonneg X hX i j := by
    rw [shiftStep_apply]
    have h4 : 0 ≤ 1 - c₁ - c₂ := by linarith
    have := hX i j
    have := hX (σ i) j
    have := hX i (σ' j)
    positivity
  const c := by
    ext i j
    rw [shiftStep_apply]
    simp only [cst_apply]
    ring
  mass X := by
    have hs1 : ∑ i, ∑ j, X (σ i) j = ∑ i, ∑ j, X i j :=
      Equiv.sum_comp σ fun i => ∑ j, X i j
    have hs2 : ∑ i, ∑ j, X i (σ' j) = ∑ i, ∑ j, X i j :=
      Finset.sum_congr rfl fun i _ => Equiv.sum_comp σ' fun j => X i j
    have hsum : ∑ i, ∑ j, shiftStep σ σ' c₁ c₂ X i j =
        (1 - c₁ - c₂) * ∑ i, ∑ j, X i j + c₁ * ∑ i, ∑ j, X (σ i) j +
          c₂ * ∑ i, ∑ j, X i (σ' j) := by
      simp only [shiftStep_apply, Finset.sum_add_distrib, Finset.mul_sum]
    rw [avg, hsum, hs1, hs2, avg]
    congr 1
    ring

/-- The left shift matrix `(P X) i j = X (σ i) j`. -/
def shiftL (σ : Equiv.Perm ι) : Matrix ι ι ℝ := fun i k => if k = σ i then 1 else 0

/-- The right shift matrix `(X Q) i j = X i (σ' j)`. -/
def shiftR (σ' : Equiv.Perm ι') : Matrix ι' ι' ℝ := fun l j => if l = σ' j then 1 else 0

lemma shiftL_mul (σ : Equiv.Perm ι) (X : Mat) (i : ι) (j : ι') :
    (shiftL σ * X) i j = X (σ i) j := by
  simp [Matrix.mul_apply, shiftL]

lemma mul_shiftR (σ' : Equiv.Perm ι') (X : Mat) (i : ι) (j : ι') :
    (X * shiftR σ') i j = X i (σ' j) := by
  simp [Matrix.mul_apply, shiftR]

/-- The advection generator on the left, `A = c₁ (P - 1)`. -/
def genL (σ : Equiv.Perm ι) (c : ℝ) : Matrix ι ι ℝ := c • (shiftL σ - 1)

/-- The advection generator on the right, `B = c₂ (Q - 1)`. -/
def genR (σ' : Equiv.Perm ι') (c : ℝ) : Matrix ι' ι' ℝ := c • (shiftR σ' - 1)

lemma shiftStep_eq (σ : Equiv.Perm ι) (σ' : Equiv.Perm ι') (c₁ c₂ : ℝ) (Z : Mat) :
    shiftStep σ σ' c₁ c₂ Z = Z + genL σ c₁ * Z + Z * genR σ' c₂ := by
  ext i j
  simp only [genL, genR, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    shiftL_mul, mul_shiftR, shiftStep_apply, smul_eq_mul]
  ring

lemma genL_row_sum (σ : Equiv.Perm ι) (c : ℝ) (i : ι) : ∑ k, genL σ c i k = 0 := by
  simp [genL, shiftL, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
    Finset.sum_sub_distrib, ← Finset.mul_sum]

lemma genR_col_sum (σ' : Equiv.Perm ι') (c : ℝ) (j : ι') : ∑ l, genR σ' c l j = 0 := by
  simp [genR, shiftR, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
    Finset.sum_sub_distrib, ← Finset.mul_sum]

lemma genL_l1 (σ : Equiv.Perm ι) {c : ℝ} (hc : 0 ≤ c) (i : ι) : ∑ k, |genL σ c i k| ≤ 2 * c := by
  calc ∑ k, |genL σ c i k|
      ≤ ∑ k, (c * (if k = σ i then 1 else 0) + c * (if i = k then 1 else 0)) := by
        refine Finset.sum_le_sum fun k _ => ?_
        simp only [genL, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, shiftL, Matrix.one_apply,
          abs_mul, abs_of_nonneg hc, ← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ hc
        split_ifs <;> norm_num
    _ = 2 * c := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq, Finset.sum_ite_eq',
          Finset.mem_univ, ite_true]
        ring

lemma genR_l1 (σ' : Equiv.Perm ι') {c : ℝ} (hc : 0 ≤ c) (j : ι') :
    ∑ l, |genR σ' c l j| ≤ 2 * c := by
  calc ∑ l, |genR σ' c l j|
      ≤ ∑ l, (c * (if l = σ' j then 1 else 0) + c * (if l = j then 1 else 0)) := by
        refine Finset.sum_le_sum fun l _ => ?_
        simp only [genR, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, shiftR, Matrix.one_apply,
          abs_mul, abs_of_nonneg hc, ← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ hc
        split_ifs <;> norm_num
    _ = 2 * c := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
          Finset.mem_univ, ite_true]
        ring

lemma taylor2_row_sum {A : Matrix ι ι ℝ} (hA : ∀ i, ∑ k, A i k = 0) (i : ι) :
    ∑ k, taylor2 A i k = 1 := by
  have h : ∑ k, (A * A) i k = 0 := by
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hA, mul_zero, Finset.sum_const_zero]
  simp only [taylor2, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, h, hA, Matrix.one_apply, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  norm_num

lemma taylor2_col_sum {B : Matrix ι' ι' ℝ} (hB : ∀ j, ∑ l, B l j = 0) (j : ι') :
    ∑ l, taylor2 B l j = 1 := by
  have h : ∑ l, (B * B) l j = 0 := by
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hB, zero_mul, Finset.sum_const_zero]
  simp only [taylor2, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, h, hB, Matrix.one_apply, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  norm_num

/-- `Z ↦ taylor2 A * Z` is Heun's method of the step `Z ↦ Z + A Z`. -/
lemma taylor2_mul_contract (σ : Equiv.Perm ι) (σ' : Equiv.Perm ι') {c : ℝ} (h0 : 0 ≤ c)
    (h1 : c ≤ 1) (Z : Mat) : ‖taylor2 (genL σ c) * Z‖ ≤ ‖Z‖ := by
  have hm := (isMonotoneStep_shiftStep σ σ' h0 le_rfl (by linarith)).heun
  have heq : taylor2 (genL σ c) * Z = heun (shiftStep σ σ' c 0) Z := by
    have hE : ∀ W : Mat, shiftStep σ σ' c 0 W = W + genL σ c * W := by
      intro W
      rw [shiftStep_eq]
      simp [genR]
    simp only [heun, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.comp_apply, hE, taylor2, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.smul_mul, Matrix.mul_assoc]
    module
  rw [heq]
  exact hm.norm_le Z

/-- `Z ↦ Z * taylor2 B` is Heun's method of the step `Z ↦ Z + Z B`. -/
lemma mul_taylor2_contract (σ : Equiv.Perm ι) (σ' : Equiv.Perm ι') {c : ℝ} (h0 : 0 ≤ c)
    (h1 : c ≤ 1) (Z : Mat) : ‖Z * taylor2 (genR σ' c)‖ ≤ ‖Z‖ := by
  have hm := (isMonotoneStep_shiftStep σ σ' le_rfl h0 (by linarith)).heun
  have heq : Z * taylor2 (genR σ' c) = heun (shiftStep σ σ' 0 c) Z := by
    have hE : ∀ W : Mat, shiftStep σ σ' 0 c W = W + W * genR σ' c := by
      intro W
      rw [shiftStep_eq]
      simp [genL]
    simp only [heun, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.comp_apply, hE, taylor2, Matrix.add_mul, Matrix.mul_add, Matrix.mul_one,
      Matrix.mul_smul, Matrix.mul_assoc]
    module
  rw [heq]
  exact hm.norm_le Z

/-- The reference solution: a rank-preserving second-order step `Y (n+1) = G Y n H`, its defect
against Heun's method, and its distance to the full-rank solution. -/
theorem advection_reference (σ : Equiv.Perm ι) (σ' : Equiv.Perm ι') {a₁ a₂ h : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hh : 0 ≤ h) (hcfl : h * a₁ + h * a₂ ≤ 1) (Y₀ : Mat) :
    ∃ Y : ℕ → Mat, Y 0 = Y₀ ∧
      (∀ n, Y (n + 1) = taylor2 (genL σ (h * a₁)) * Y n * taylor2 (genR σ' (h * a₂))) ∧
      (∀ Z : Mat, ‖taylor2 (genL σ (h * a₁)) * Z * taylor2 (genR σ' (h * a₂)) -
        heun (shiftStep σ σ' (h * a₁) (h * a₂)) Z‖ ≤ (8 * a₁ * a₂ * (a₁ + a₂) * h ^ 2) * h * ‖Z‖) ∧
      (∀ n, ‖heun (shiftStep σ σ' (h * a₁) (h * a₂)) (Y n) - Y (n + 1)‖ ≤
        (8 * a₁ * a₂ * (a₁ + a₂) * ‖Y₀‖) * h ^ (2 + 1)) ∧
      ∀ n : ℕ, ‖Y n - (heun (shiftStep σ σ' (h * a₁) (h * a₂)) ^ n) Y₀‖ ≤
        8 * a₁ * a₂ * (a₁ + a₂) * ‖Y₀‖ * h ^ 2 * (n * h) := by
  set c₁ := h * a₁ with hc₁
  set c₂ := h * a₂ with hc₂
  have hc₁0 : 0 ≤ c₁ := mul_nonneg hh ha₁
  have hc₂0 : 0 ≤ c₂ := mul_nonneg hh ha₂
  have hc₁1 : c₁ ≤ 1 := by linarith
  have hc₂1 : c₂ ≤ 1 := by linarith
  set E := shiftStep σ σ' c₁ c₂ with hE
  set Φ := heun E with hΦdef
  have hΦ : IsMonotoneStep Φ := (isMonotoneStep_shiftStep σ σ' hc₁0 hc₂0 hcfl).heun
  set A := genL σ c₁ with hA
  set B := genR σ' c₂ with hB
  set G := taylor2 A with hG
  set H := taylor2 B with hH
  set C₀ : ℝ := 8 * a₁ * a₂ * (a₁ + a₂) with hC₀
  have hC₀0 : 0 ≤ C₀ := by positivity
  have hαZ : ∀ Z : Mat, ‖A * Z‖ ≤ 2 * c₁ * ‖Z‖ := fun Z => norm_mul_left_le (genL_l1 σ hc₁0) Z
  have hβZ : ∀ Z : Mat, ‖Z * B‖ ≤ 2 * c₂ * ‖Z‖ := fun Z => norm_mul_right_le (genR_l1 σ' hc₂0) Z
  have hdefect : ∀ Z : Mat, ‖G * Z * H - Φ Z‖ ≤ C₀ * h ^ 3 * ‖Z‖ := by
    intro Z
    have h1 := heun_sylvester (shiftStep_eq σ σ' c₁ c₂) (by positivity) (by positivity) hαZ hβZ Z
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have h2 : c₁ * c₂ ^ 2 * c₁ ≤ c₁ * c₂ ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hc₁1 (by positivity)
    have h3 : C₀ * h ^ 3 = 8 * c₁ * c₂ * (c₁ + c₂) := by
      rw [hC₀, hc₁, hc₂]; ring
    rw [h3]
    nlinarith [mul_nonneg (mul_nonneg hc₁0 hc₁0) hc₂0]
  let Y : ℕ → Mat := fun n => Nat.rec Y₀ (fun _ Yn => G * Yn * H) n
  have hYs : ∀ n, Y (n + 1) = G * Y n * H := fun _ => rfl
  have hY0 : Y 0 = Y₀ := rfl
  have hYb : ∀ n, ‖Y n‖ ≤ ‖Y₀‖ := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [hYs]
      calc ‖G * Y n * H‖ ≤ ‖G * Y n‖ := mul_taylor2_contract σ σ' hc₂0 hc₂1 _
        _ ≤ ‖Y n‖ := taylor2_mul_contract σ σ' hc₁0 hc₁1 _
        _ ≤ ‖Y₀‖ := ih
  have hcons : ∀ n, ‖Φ (Y n) - Y (n + 1)‖ ≤ (C₀ * ‖Y₀‖) * h ^ (2 + 1) := by
    intro n
    rw [hYs, norm_sub_rev]
    refine (hdefect _).trans ?_
    calc C₀ * h ^ 3 * ‖Y n‖ ≤ C₀ * h ^ 3 * ‖Y₀‖ :=
          mul_le_mul_of_nonneg_left (hYb n) (by positivity)
      _ = C₀ * ‖Y₀‖ * h ^ (2 + 1) := by ring
  refine ⟨Y, hY0, hYs, fun Z => ?_, hcons, fun n => ?_⟩
  · calc _ ≤ _ := hdefect Z
      _ = C₀ * h ^ 2 * h * ‖Z‖ := by ring
  · induction n with
    | zero => simp [hY0]
    | succ n ih =>
      have e1 : (Φ ^ (n + 1)) Y₀ = Φ ((Φ ^ n) Y₀) := by
        rw [pow_succ', mul_apply_eq_comp]
      have e2 := hΦ.norm_le (Y n - (Φ ^ n) Y₀)
      rw [map_sub] at e2
      have e3 := hcons n
      rw [norm_sub_rev] at e3
      calc ‖Y (n + 1) - (Φ ^ (n + 1)) Y₀‖
          = ‖(Y (n + 1) - Φ (Y n)) + (Φ (Y n) - Φ ((Φ ^ n) Y₀))‖ := by
            rw [e1]; congr 1; abel
        _ ≤ ‖Y (n + 1) - Φ (Y n)‖ + ‖Φ (Y n) - Φ ((Φ ^ n) Y₀)‖ := norm_add_le _ _
        _ ≤ C₀ * ‖Y₀‖ * h ^ (2 + 1) + C₀ * ‖Y₀‖ * h ^ 2 * (n * h) := by linarith
        _ = C₀ * ‖Y₀‖ * h ^ 2 * (((n + 1 : ℕ) : ℝ) * h) := by push_cast; ring

/-- **Instance: two-dimensional periodic upwind advection, second order, arbitrary low-rank data.**
Let `E` be the upwind step with CFL numbers `h a₁`, `h a₂`, `Φ` its second-order SSP Runge-Kutta
method, and let `Y₀` take values in `[a, b]` with fluctuation of rank at most `r`.  The limited
scheme started at `Y₀` stays in `[a, b]`, conserves the mean, has rank at most `r + 2`, and after
`N` steps it is within `O(h²)` of the full-rank solution `Φ^N Y₀`, uniformly in the regularity of
`Y₀` (only `‖Y₀‖` enters; `a₁`, `a₂` are fixed, i.e. the spatial mesh is fixed).  Here the exact
generator preserves the rank while `Φ` does not, which is why `truncDC` is needed. -/
theorem advection_second_order (σ : Equiv.Perm ι) (σ' : Equiv.Perm ι') {a₁ a₂ h a b : ℝ} {r : ℕ}
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hh : 0 ≤ h) (hcfl : h * a₁ + h * a₂ ≤ 1) {Y₀ : Mat}
    (hY₀ : InBand a b Y₀) (hrk : (dc Y₀).rank ≤ r) (hρ : 0 < radius a b Y₀) {X : ℕ → Mat}
    (hX0 : X 0 = Y₀)
    (hX : ∀ n, X (n + 1) = limiter a b (heun (shiftStep σ σ' (h * a₁) (h * a₂)) (X n))
      (truncDC r (heun (shiftStep σ σ' (h * a₁) (h * a₂)) (X n)))) :
    (∀ n, InBand a b (X n) ∧ avg (X n) = avg Y₀ ∧ (X n).rank ≤ r + 2) ∧
    ∀ N : ℕ, ‖X N - (heun (shiftStep σ σ' (h * a₁) (h * a₂)) ^ N) Y₀‖ ≤
      (Real.exp ((limK a b (radius a b Y₀) * (4 * √((Fintype.card ι : ℝ) * Fintype.card ι')) *
        (8 * a₁ * a₂ * (a₁ + a₂) * h ^ 2)) * h * N) *
      ((1 + limK a b (radius a b Y₀) * (4 * √((Fintype.card ι : ℝ) * Fintype.card ι'))) *
        (8 * a₁ * a₂ * (a₁ + a₂) * ‖Y₀‖) * h ^ 2 * (N * h)) +
      8 * a₁ * a₂ * (a₁ + a₂) * ‖Y₀‖ * h ^ 2 * (N * h)) := by
  have hΦ : IsMonotoneStep (heun (shiftStep σ σ' (h * a₁) (h * a₂))) :=
    (isMonotoneStep_shiftStep σ σ' (mul_nonneg hh ha₁) (mul_nonneg hh ha₂) hcfl).heun
  obtain ⟨Y, hY0, hYs, hdef, hcons, hfull⟩ := advection_reference σ σ' ha₁ ha₂ hh hcfl Y₀
  have hC₀0 : 0 ≤ 8 * a₁ * a₂ * (a₁ + a₂) := by positivity
  have hmain := limited_scheme (a := a) (b := b) (h := h) (Ks := 8 * a₁ * a₂ * (a₁ + a₂) * h ^ 2)
    (C := 8 * a₁ * a₂ * (a₁ + a₂) * ‖Y₀‖) (r := r) (p := 2) hΦ (X := X) (Y := Y)
    (G := fun _ => taylor2 (genL σ (h * a₁))) (H := fun _ => taylor2 (genR σ' (h * a₂)))
    hh (by positivity) (by positivity)
    (by rw [hX0]; exact hY₀) (by rw [hX0]; exact hrk) (by rw [hX0]; exact hρ) hX
    (fun _ i => taylor2_row_sum (genL_row_sum σ _) i)
    (fun _ j => taylor2_col_sum (genR_col_sum σ' _) j) hYs (fun _ Z => hdef Z) hcons
  rw [hX0] at hmain
  refine ⟨fun n => ?_, fun N => ?_⟩
  · obtain ⟨h1, h2, -, h3⟩ := hmain.1 n
    exact ⟨h1, h2, h3⟩
  · have h1 := hmain.2 N
    rw [show Y₀ - Y 0 = 0 by rw [hY0, sub_self], norm_zero, zero_add] at h1
    calc _ = ‖(X N - Y N) + (Y N - (heun (shiftStep σ σ' (h * a₁) (h * a₂)) ^ N) Y₀)‖ := by
          congr 1; abel
      _ ≤ ‖X N - Y N‖ + ‖Y N - (heun (shiftStep σ σ' (h * a₁) (h * a₂)) ^ N) Y₀‖ :=
          norm_add_le _ _
      _ ≤ _ := add_le_add h1 (hfull N)

/-- The periodic total variation along the permutations `σ`, `σ'`. -/
noncomputable def tvPer (σ : Equiv.Perm ι) (σ' : Equiv.Perm ι') (X : Mat) : ℝ :=
  ∑ i, ∑ j, (|X (σ i) j - X i j| + |X i (σ' j) - X i j|)

theorem isVariation_tvPer (σ : Equiv.Perm ι) (σ' : Equiv.Perm ι') :
    IsVariation (tvPer σ σ' : Mat → ℝ) where
  add_le X Y := by
    simp only [tvPer, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    simp only [Matrix.add_apply]
    have h1 := abs_add_le (X (σ i) j - X i j) (Y (σ i) j - Y i j)
    have h2 := abs_add_le (X i (σ' j) - X i j) (Y i (σ' j) - Y i j)
    rw [show X (σ i) j + Y (σ i) j - (X i j + Y i j) = X (σ i) j - X i j + (Y (σ i) j - Y i j) by
      ring, show X i (σ' j) + Y i (σ' j) - (X i j + Y i j) =
        X i (σ' j) - X i j + (Y i (σ' j) - Y i j) by ring]
    linarith
  smul c X := by
    simp only [tvPer, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_sub, abs_mul, mul_add]
  cst c := by
    simp [tvPer]

lemma tvPer_eq (σ : Equiv.Perm ι) (σ' : Equiv.Perm ι') (X : Mat) :
    tvPer σ σ' X = ∑ i, ∑ j, |X (σ i) j - X i j| + ∑ i, ∑ j, |X i (σ' j) - X i j| := by
  simp only [tvPer, Finset.sum_add_distrib]

/-- The upwind step does not increase the periodic total variation. -/
theorem tvPer_shiftStep_le (σ : Equiv.Perm ι) (σ' : Equiv.Perm ι') {c₁ c₂ : ℝ} (h1 : 0 ≤ c₁)
    (h2 : 0 ≤ c₂) (h3 : c₁ + c₂ ≤ 1) (X : Mat) :
    tvPer σ σ' (shiftStep σ σ' c₁ c₂ X) ≤ tvPer σ σ' X := by
  have hs : 0 ≤ 1 - c₁ - c₂ := by linarith
  set s := 1 - c₁ - c₂ with hsdef
  have T1a : ∑ i, ∑ j, |X (σ (σ i)) j - X (σ i) j| = ∑ i, ∑ j, |X (σ i) j - X i j| :=
    Equiv.sum_comp σ fun i => ∑ j, |X (σ i) j - X i j|
  have T1b : ∑ i, ∑ j, |X (σ i) (σ' j) - X i (σ' j)| = ∑ i, ∑ j, |X (σ i) j - X i j| :=
    Finset.sum_congr rfl fun i _ => Equiv.sum_comp σ' fun j => |X (σ i) j - X i j|
  have T2a : ∑ i, ∑ j, |X (σ i) (σ' j) - X (σ i) j| = ∑ i, ∑ j, |X i (σ' j) - X i j| :=
    Equiv.sum_comp σ fun i => ∑ j, |X i (σ' j) - X i j|
  have T2b : ∑ i, ∑ j, |X i (σ' (σ' j)) - X i (σ' j)| = ∑ i, ∑ j, |X i (σ' j) - X i j| :=
    Finset.sum_congr rfl fun i _ => Equiv.sum_comp σ' fun j => |X i (σ' j) - X i j|
  have hconv : ∀ a b d : ℝ, |s * a + c₁ * b + c₂ * d| ≤ s * |a| + c₁ * |b| + c₂ * |d| := by
    intro a b d
    calc _ ≤ |s * a + c₁ * b| + |c₂ * d| := abs_add_le _ _
      _ ≤ |s * a| + |c₁ * b| + |c₂ * d| := by linarith [abs_add_le (s * a) (c₁ * b)]
      _ = _ := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg h1, abs_of_nonneg h2]
  rw [tvPer_eq, tvPer_eq]
  have B1 : ∑ i, ∑ j, |shiftStep σ σ' c₁ c₂ X (σ i) j - shiftStep σ σ' c₁ c₂ X i j| ≤
      ∑ i, ∑ j, |X (σ i) j - X i j| := by
    calc _ ≤ ∑ i, ∑ j, (s * |X (σ i) j - X i j| + c₁ * |X (σ (σ i)) j - X (σ i) j| +
          c₂ * |X (σ i) (σ' j) - X i (σ' j)|) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          simp only [shiftStep_apply]
          rw [← hsdef]
          refine le_trans (le_of_eq ?_) (hconv _ _ _)
          congr 1
          ring
      _ = (s + c₁ + c₂) * ∑ i, ∑ j, |X (σ i) j - X i j| := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, T1a, T1b]
          ring
      _ = ∑ i, ∑ j, |X (σ i) j - X i j| := by rw [hsdef]; ring
  have B2 : ∑ i, ∑ j, |shiftStep σ σ' c₁ c₂ X i (σ' j) - shiftStep σ σ' c₁ c₂ X i j| ≤
      ∑ i, ∑ j, |X i (σ' j) - X i j| := by
    calc _ ≤ ∑ i, ∑ j, (s * |X i (σ' j) - X i j| + c₁ * |X (σ i) (σ' j) - X (σ i) j| +
          c₂ * |X i (σ' (σ' j)) - X i (σ' j)|) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          simp only [shiftStep_apply]
          rw [← hsdef]
          refine le_trans (le_of_eq ?_) (hconv _ _ _)
          congr 1
          ring
      _ = (s + c₁ + c₂) * ∑ i, ∑ j, |X i (σ' j) - X i j| := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, T2a, T2b]
          ring
      _ = ∑ i, ∑ j, |X i (σ' j) - X i j| := by rw [hsdef]; ring
  exact add_le_add B1 B2

/-- Heun's method does not increase a seminorm that its base step does not increase. -/
theorem heun_variation_le {E : Mat →ₗ[ℝ] Mat} {v : Mat → ℝ} (hv : IsVariation v)
    (hE : ∀ Z, v (E Z) ≤ v Z) (X : Mat) : v (heun E X) ≤ v X := by
  have h1 : heun E X = (1 / 2 : ℝ) • X + (1 - 1 / 2 : ℝ) • E (E X) := by
    simp [heun]
  rw [h1]
  refine (hv.add_le _ _).trans ?_
  rw [hv.smul, hv.smul]
  have h2 := (hE (E X)).trans (hE X)
  have h3 : |(1 / 2 : ℝ)| = 1 / 2 := abs_of_pos (by norm_num)
  have h4 : |(1 - 1 / 2 : ℝ)| = 1 / 2 := by norm_num [abs_of_pos]
  rw [h3, h4]
  linarith

/-- Along a transitive permutation, the difference of two values of a function is bounded by the sum
of the increments. -/
lemma abs_sub_le_sum_incr {n : Type*} [Fintype n] [DecidableEq n] {σ : Equiv.Perm n}
    (hσ : ∀ i k : n, ∃ t : ℕ, (σ ^ t) i = k) (f : n → ℝ) (i k : n) :
    |f k - f i| ≤ ∑ l, |f (σ l) - f l| := by
  classical
  have ex := hσ i k
  set t := Nat.find ex with ht
  have hspec : (σ ^ t) i = k := Nat.find_spec ex
  have hmin : ∀ m < t, (σ ^ m) i ≠ k := fun m hm => Nat.find_min ex hm
  have hsucc : ∀ m, (σ ^ (m + 1)) i = σ ((σ ^ m) i) := by
    intro m
    rw [pow_succ', Equiv.Perm.mul_apply]
  have hadd : ∀ a b : ℕ, (σ ^ (a + b)) i = (σ ^ a) ((σ ^ b) i) := by
    intro a b
    rw [pow_add, Equiv.Perm.mul_apply]
  have hinj : Set.InjOn (fun m => (σ ^ m) i) (Finset.range t : Set ℕ) := by
    have key : ∀ a b : ℕ, a < b → b < t → (σ ^ a) i ≠ (σ ^ b) i := by
      intro a b hab hb heq
      obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
      have h1 : (σ ^ d) i = i := by
        have h2 : (σ ^ a) ((σ ^ d) i) = (σ ^ a) i := by
          rw [← hadd]; exact heq.symm
        exact (σ ^ a).injective h2
      have h3 : (σ ^ (t - d)) i = k := by
        have h4 : t = (t - d) + d := by omega
        rw [h4, hadd, h1] at hspec
        simpa using hspec
      exact hmin (t - d) (by omega) h3
    intro a ha b hb heq
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    rcases lt_trichotomy a b with h | h | h
    · exact absurd heq (key a b h hb)
    · exact h
    · exact absurd heq.symm (key b a h ha)
  have htel : f k - f i = ∑ m ∈ Finset.range t, (f ((σ ^ (m + 1)) i) - f ((σ ^ m) i)) := by
    rw [Finset.sum_range_sub (fun m => f ((σ ^ m) i)), hspec]
    simp
  rw [htel]
  calc |∑ m ∈ Finset.range t, (f ((σ ^ (m + 1)) i) - f ((σ ^ m) i))|
      ≤ ∑ m ∈ Finset.range t, |f ((σ ^ (m + 1)) i) - f ((σ ^ m) i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ m ∈ Finset.range t, |f (σ ((σ ^ m) i)) - f ((σ ^ m) i)| := by
        simp only [hsucc]
    _ = ∑ l ∈ (Finset.range t).image (fun m => (σ ^ m) i), |f (σ l) - f l| := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ l, |f (σ l) - f l| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => abs_nonneg _

lemma avg_mem_of_bounds {Y : Mat} {l u : ℝ} (h : ∀ i j, Y i j ∈ Icc l u) : avg Y ∈ Icc l u := by
  have hc := card_ne (ι := ι) (ι' := ι')
  have hpos : 0 < (Fintype.card ι : ℝ) * Fintype.card ι' := by positivity
  have hcount : ∀ c : ℝ, ∑ _i : ι, ∑ _j : ι', c = c * ((Fintype.card ι : ℝ) * Fintype.card ι') := by
    intro c
    simp [Finset.card_univ]
    ring
  constructor
  · rw [avg, le_div_iff₀ hpos, ← hcount]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => (h i j).1
  · rw [avg, div_le_iff₀ hpos, ← hcount]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => (h i j).2

/-- A discrete Poincaré inequality: for transitive `σ`, `σ'` the maximum norm of the fluctuation is
bounded by the periodic total variation. -/
theorem tvPer_poincare {σ : Equiv.Perm ι} {σ' : Equiv.Perm ι'}
    (hσ : ∀ i k : ι, ∃ t : ℕ, (σ ^ t) i = k) (hσ' : ∀ j l : ι', ∃ t : ℕ, (σ' ^ t) j = l) (Y : Mat) :
    ‖Y - cst (avg Y)‖ ≤ 1 * tvPer σ σ' Y := by
  rw [one_mul]
  have hT : 0 ≤ tvPer σ σ' Y := (isVariation_tvPer σ σ').nonneg Y
  have hpair : ∀ i j k l, |Y k l - Y i j| ≤ tvPer σ σ' Y := by
    intro i j k l
    have h1 : |Y k j - Y i j| ≤ ∑ a, ∑ b, |Y (σ a) b - Y a b| := by
      refine (abs_sub_le_sum_incr hσ (fun a => Y a j) i k).trans ?_
      exact Finset.sum_le_sum fun a _ =>
        Finset.single_le_sum (f := fun b => |Y (σ a) b - Y a b|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    have h2 : |Y k l - Y k j| ≤ ∑ a, ∑ b, |Y a (σ' b) - Y a b| := by
      refine (abs_sub_le_sum_incr hσ' (fun b => Y k b) j l).trans ?_
      exact Finset.single_le_sum (f := fun a => ∑ b, |Y a (σ' b) - Y a b|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    rw [tvPer_eq]
    calc |Y k l - Y i j| = |(Y k l - Y k j) + (Y k j - Y i j)| := by congr 1; ring
      _ ≤ |Y k l - Y k j| + |Y k j - Y i j| := abs_add_le _ _
      _ ≤ _ := by linarith
  refine norm_le_of_entry hT fun i j => ?_
  have hb : avg Y ∈ Icc (Y i j - tvPer σ σ' Y) (Y i j + tvPer σ σ' Y) := by
    refine avg_mem_of_bounds fun k l => ?_
    have := abs_le.mp (hpair i j k l)
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  rw [Matrix.sub_apply, cst_apply, abs_le]
  exact ⟨by linarith [hb.2], by linarith [hb.1]⟩

lemma tvPer_le (σ : Equiv.Perm ι) (σ' : Equiv.Perm ι') (Y : Mat) :
    tvPer σ σ' Y ≤ 4 * ((Fintype.card ι : ℝ) * Fintype.card ι') * ‖Y‖ := by
  have hb : ∀ a b c d, |Y a b - Y c d| ≤ 2 * ‖Y‖ := by
    intro a b c d
    have h1 := abs_entry_le Y a b
    have h2 := abs_entry_le Y c d
    calc _ ≤ |Y a b| + |Y c d| := abs_sub _ _
      _ ≤ 2 * ‖Y‖ := by linarith
  calc tvPer σ σ' Y ≤ ∑ _i : ι, ∑ _j : ι', (2 * ‖Y‖ + 2 * ‖Y‖) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          add_le_add (hb _ _ _ _) (hb _ _ _ _)
    _ = 4 * ((Fintype.card ι : ℝ) * Fintype.card ι') * ‖Y‖ := by
        simp [Finset.card_univ]
        ring

/-- **Instance with exact TVD.**  The scheme of `advection_second_order` with the additional scaling
stage for the periodic total variation (`σ`, `σ'` transitive) has `TV (X (n+1)) ≤ TV (X n)`, stays
in `[a, b]`, conserves the mean, has rank at most `r + 2`, and is within `O(h²)` of the full
solution at fixed mesh.  The constant now contains the mesh factor `1 + 4 m n`. -/
theorem advection_tvd {σ : Equiv.Perm ι} {σ' : Equiv.Perm ι'}
    (hσ : ∀ i k : ι, ∃ t : ℕ, (σ ^ t) i = k) (hσ' : ∀ j l : ι', ∃ t : ℕ, (σ' ^ t) j = l)
    {a₁ a₂ h a b : ℝ} {r : ℕ}
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hh : 0 ≤ h) (hcfl : h * a₁ + h * a₂ ≤ 1) {Y₀ : Mat}
    (hY₀ : InBand a b Y₀) (hrk : (dc Y₀).rank ≤ r) (hρ : 0 < radius a b Y₀) {X : ℕ → Mat}
    (hX0 : X 0 = Y₀)
    (hX : ∀ n, X (n + 1) = tvStage (tvPer σ σ') (tvPer σ σ' (X n))
      (limiter a b (heun (shiftStep σ σ' (h * a₁) (h * a₂)) (X n))
        (truncDC r (heun (shiftStep σ σ' (h * a₁) (h * a₂)) (X n))))) :
    (∀ n, InBand a b (X n) ∧ avg (X n) = avg Y₀ ∧ (X n).rank ≤ r + 2) ∧
    (∀ n, tvPer σ σ' (X (n + 1)) ≤ tvPer σ σ' (X n)) ∧
    ∀ N : ℕ, ‖X N - (heun (shiftStep σ σ' (h * a₁) (h * a₂)) ^ N) Y₀‖ ≤
      (Real.exp (((1 + 1 * (4 * ((Fintype.card ι : ℝ) * Fintype.card ι'))) *
        limK a b (radius a b Y₀) * (4 * √((Fintype.card ι : ℝ) * Fintype.card ι')) *
        (8 * a₁ * a₂ * (a₁ + a₂) * h ^ 2)) * h * N) *
      ((1 + (1 + 1 * (4 * ((Fintype.card ι : ℝ) * Fintype.card ι'))) *
        limK a b (radius a b Y₀) * (4 * √((Fintype.card ι : ℝ) * Fintype.card ι'))) *
        (8 * a₁ * a₂ * (a₁ + a₂) * ‖Y₀‖) * h ^ 2 * (N * h)) +
      8 * a₁ * a₂ * (a₁ + a₂) * ‖Y₀‖ * h ^ 2 * (N * h)) := by
  have hc₁ := mul_nonneg hh ha₁
  have hc₂ := mul_nonneg hh ha₂
  have hΦ : IsMonotoneStep (heun (shiftStep σ σ' (h * a₁) (h * a₂))) :=
    (isMonotoneStep_shiftStep σ σ' hc₁ hc₂ hcfl).heun
  obtain ⟨Y, hY0, hYs, hdef, hcons, hfull⟩ := advection_reference σ σ' ha₁ ha₂ hh hcfl Y₀
  have hC₀0 : 0 ≤ 8 * a₁ * a₂ * (a₁ + a₂) := by positivity
  have hmain := limited_scheme_tv (a := a) (b := b) (h := h)
    (Ks := 8 * a₁ * a₂ * (a₁ + a₂) * h ^ 2) (C := 8 * a₁ * a₂ * (a₁ + a₂) * ‖Y₀‖)
    (c := 1) (Λ := 4 * ((Fintype.card ι : ℝ) * Fintype.card ι')) (r := r) (p := 2) hΦ
    (isVariation_tvPer σ σ') zero_le_one (by positivity) (tvPer_poincare hσ hσ') (tvPer_le σ σ')
    (heun_variation_le (isVariation_tvPer σ σ') (tvPer_shiftStep_le σ σ' hc₁ hc₂ hcfl))
    (X := X) (Y := Y)
    (G := fun _ => taylor2 (genL σ (h * a₁))) (H := fun _ => taylor2 (genR σ' (h * a₂)))
    hh (by positivity) (by positivity)
    (by rw [hX0]; exact hY₀) (by rw [hX0]; exact hrk) (by rw [hX0]; exact hρ) hX
    (fun _ i => taylor2_row_sum (genL_row_sum σ _) i)
    (fun _ j => taylor2_col_sum (genR_col_sum σ' _) j) hYs (fun _ Z => hdef Z) hcons
  rw [hX0] at hmain
  refine ⟨fun n => ?_, hmain.2.1, fun N => ?_⟩
  · obtain ⟨h1, h2, -, h3⟩ := hmain.1 n
    exact ⟨h1, h2, h3⟩
  · have h1 := hmain.2.2 N
    rw [show Y₀ - Y 0 = 0 by rw [hY0, sub_self], norm_zero, zero_add] at h1
    calc _ = ‖(X N - Y N) + (Y N - (heun (shiftStep σ σ' (h * a₁) (h * a₂)) ^ N) Y₀)‖ := by
          congr 1; abel
      _ ≤ ‖X N - Y N‖ + ‖Y N - (heun (shiftStep σ σ' (h * a₁) (h * a₂)) ^ N) Y₀‖ :=
          norm_add_le _ _
      _ ≤ _ := add_le_add h1 (hfull N)

/-- One forward Euler step of the upwind discretization of a linear kinetic equation with isotropic
scattering: rows are cells, columns are velocities, `νp j`, `νm j` are the CFL numbers of velocity
`j` in the two directions along the periodic cell order `σ`, and `s i` is the scattering rate in
cell `i` (so heterogeneous media are included).  The velocity average is taken over the columns. -/
noncomputable def kineticStep (σ : Equiv.Perm ι) (νp νm : ι' → ℝ) (s : ι → ℝ) : Mat →ₗ[ℝ] Mat where
  toFun X := fun i j => (1 - νp j - νm j - s i) * X i j + νp j * X (σ i) j + νm j * X (σ.symm i) j +
    s i * ((Fintype.card ι' : ℝ)⁻¹ * ∑ l, X i l)
  map_add' X Y := by
    ext i j
    change (1 - νp j - νm j - s i) * (X + Y) i j + νp j * (X + Y) (σ i) j +
        νm j * (X + Y) (σ.symm i) j + s i * ((Fintype.card ι' : ℝ)⁻¹ * ∑ l, (X + Y) i l) =
      ((1 - νp j - νm j - s i) * X i j + νp j * X (σ i) j + νm j * X (σ.symm i) j +
        s i * ((Fintype.card ι' : ℝ)⁻¹ * ∑ l, X i l)) +
      ((1 - νp j - νm j - s i) * Y i j + νp j * Y (σ i) j + νm j * Y (σ.symm i) j +
        s i * ((Fintype.card ι' : ℝ)⁻¹ * ∑ l, Y i l))
    simp only [Matrix.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' c X := by
    ext i j
    change (1 - νp j - νm j - s i) * (c • X) i j + νp j * (c • X) (σ i) j +
        νm j * (c • X) (σ.symm i) j + s i * ((Fintype.card ι' : ℝ)⁻¹ * ∑ l, (c • X) i l) =
      c * ((1 - νp j - νm j - s i) * X i j + νp j * X (σ i) j + νm j * X (σ.symm i) j +
        s i * ((Fintype.card ι' : ℝ)⁻¹ * ∑ l, X i l))
    simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    ring

lemma kineticStep_apply (σ : Equiv.Perm ι) (νp νm : ι' → ℝ) (s : ι → ℝ) (X : Mat) (i : ι)
    (j : ι') : kineticStep σ νp νm s X i j =
      (1 - νp j - νm j - s i) * X i j + νp j * X (σ i) j + νm j * X (σ.symm i) j +
        s i * ((Fintype.card ι' : ℝ)⁻¹ * ∑ l, X i l) := rfl

/-- The kinetic upwind step is a monotone step under the CFL condition. -/
theorem isMonotoneStep_kineticStep (σ : Equiv.Perm ι) {νp νm : ι' → ℝ} {s : ι → ℝ}
    (hp : ∀ j, 0 ≤ νp j) (hm : ∀ j, 0 ≤ νm j) (hs : ∀ i, 0 ≤ s i)
    (hcfl : ∀ i j, νp j + νm j + s i ≤ 1) : IsMonotoneStep (kineticStep σ νp νm s) where
  nonneg X hX i j := by
    rw [kineticStep_apply]
    have h1 : 0 ≤ 1 - νp j - νm j - s i := by linarith [hcfl i j]
    have h2 := hX i j
    have h3 := hX (σ i) j
    have h4 := hX (σ.symm i) j
    have h5 : 0 ≤ ∑ l, X i l := Finset.sum_nonneg fun l _ => hX i l
    have h6 := hp j
    have h7 := hm j
    have h8 := hs i
    positivity
  const c := by
    ext i j
    have hn : (Fintype.card ι' : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have hsum : (Fintype.card ι' : ℝ)⁻¹ * ∑ _l : ι', c = c := by
      simp [Finset.card_univ, hn]
    rw [kineticStep_apply]
    simp only [cst_apply]
    rw [hsum]
    ring
  mass X := by
    have hn : (Fintype.card ι' : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have hs1 : ∀ j, ∑ i, X (σ i) j = ∑ i, X i j := fun j => Equiv.sum_comp σ fun i => X i j
    have hs2 : ∀ j, ∑ i, X (σ.symm i) j = ∑ i, X i j :=
      fun j => Equiv.sum_comp σ.symm fun i => X i j
    have hcol : ∀ j, ∑ i, kineticStep σ νp νm s X i j =
        ∑ i, X i j - ∑ i, s i * X i j + ∑ i, s i * ((Fintype.card ι' : ℝ)⁻¹ * ∑ l, X i l) := by
      intro j
      have a1 : ∑ i, (1 - νp j - νm j - s i) * X i j =
          (1 - νp j - νm j) * ∑ i, X i j - ∑ i, s i * X i j := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      have a2 : ∑ i, νp j * X (σ i) j = νp j * ∑ i, X i j := by
        rw [← Finset.mul_sum, hs1]
      have a3 : ∑ i, νm j * X (σ.symm i) j = νm j * ∑ i, X i j := by
        rw [← Finset.mul_sum, hs2]
      simp only [kineticStep_apply, Finset.sum_add_distrib]
      rw [a1, a2, a3]
      ring
    have hscat : ∑ j : ι', ∑ i, s i * ((Fintype.card ι' : ℝ)⁻¹ * ∑ l, X i l) =
        ∑ j, ∑ i, s i * X i j := by
      rw [Finset.sum_comm, Finset.sum_comm (f := fun j i => s i * X i j)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
      field_simp
    have htotal : ∑ i, ∑ j, kineticStep σ νp νm s X i j = ∑ i, ∑ j, X i j := by
      calc ∑ i, ∑ j, kineticStep σ νp νm s X i j
          = ∑ j, ∑ i, kineticStep σ νp νm s X i j := Finset.sum_comm
        _ = ∑ j, (∑ i, X i j - ∑ i, s i * X i j +
              ∑ i, s i * ((Fintype.card ι' : ℝ)⁻¹ * ∑ l, X i l)) :=
            Finset.sum_congr rfl fun j _ => hcol j
        _ = ∑ j, ∑ i, X i j - ∑ j, ∑ i, s i * X i j +
              ∑ j : ι', ∑ i, s i * ((Fintype.card ι' : ℝ)⁻¹ * ∑ l, X i l) := by
            simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        _ = ∑ j, ∑ i, X i j := by rw [hscat]; ring
        _ = ∑ i, ∑ j, X i j := Finset.sum_comm
    rw [avg, avg, htotal]

/-- **Instance: the linear kinetic equation.**  For the second-order SSP Runge-Kutta method of the
upwind step of a linear kinetic equation with isotropic scattering, the limited low-rank scheme is
exactly positive (take `a = 0`), conserves the mass, has rank at most `r + 2`, and its distance from
the full solution is bounded by the sum of the truncation errors times `K`, with no assumption on
the regularity or the rank of the solution.  What is not shown is that the truncation errors are
small: that is the usual modelling assumption of low-rank methods. -/
theorem kinetic_limited_scheme (σ : Equiv.Perm ι) {νp νm : ι' → ℝ} {s : ι → ℝ}
    (hp : ∀ j, 0 ≤ νp j) (hm : ∀ j, 0 ≤ νm j) (hs : ∀ i, 0 ≤ s i)
    (hcfl : ∀ i j, νp j + νm j + s i ≤ 1) {b : ℝ} {r : ℕ} {X : ℕ → Mat}
    (hX0 : InBand 0 b (X 0)) (hρ : 0 < radius 0 b (X 0))
    (hX : ∀ n, X (n + 1) = limiter 0 b (heun (kineticStep σ νp νm s) (X n))
      (truncDC r (heun (kineticStep σ νp νm s) (X n)))) :
    (∀ n, InBand 0 b (X n) ∧ avg (X n) = avg (X 0)) ∧ (∀ n, (X (n + 1)).rank ≤ r + 2) ∧
    ∀ N : ℕ, ‖X N - (heun (kineticStep σ νp νm s) ^ N) (X 0)‖ ≤ limK 0 b (radius 0 b (X 0)) *
      ∑ n ∈ Finset.range N, ‖truncDC r (heun (kineticStep σ νp νm s) (X n)) -
        heun (kineticStep σ νp νm s) (X n)‖ :=
  limited_scheme_aposteriori (isMonotoneStep_kineticStep σ hp hm hs hcfl).heun hX0 hρ hX

end Advection

end Limiter

end LeanDLRA.Novel.OpCO45
