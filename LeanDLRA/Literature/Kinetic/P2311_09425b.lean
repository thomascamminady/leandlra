import Mathlib
import LeanDLRA.Integrators.BUG
import LeanDLRA.LinearAlgebra.Factorization.Defs
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Kinetic.LowRank

/-!
# arXiv 2311.09425: the second-order conservative low-rank integrator (Theorem 3.2, Corollary 3.3)

Coughlin, Hu, Shumlak, *Robust and conservative dynamical low-rank methods for the Vlasov equation
via a novel macro-micro decomposition*. This module writes out the second-order integrator of
Section 3.3 in full and proves its conservation laws from the scheme itself. The velocity setting is
`MomentBasis μ`: a measure `μ` (the paper's `w dv`; Hermite, Legendre or a discrete velocity grid)
with finite polynomial moments and orthonormal polynomials `p₀, …, p₃`. A profile `f = w h` is
stored as `h ∈ L²(μ)`, an isometric picture of the paper's `L²(w⁻¹ dv)`, so `⟨f, q⟩_v = ∫ q h dμ` is
a true integral. The constants `aₙ, bₙ, cᵢⱼ, dᵢⱼ` are defined as integrals, and the relations that
the paper takes as their definition are theorems (`rec₀`, `rec₁`, `rec₂`, `one_eq`, `X_eq`,
`half_sq_eq`, `deriv₁`, `deriv₂`), as are the identities the conservation proof needs (`c_one_zero`,
`c_one_one`, `c_one_zero'`, `c_one_one'`, `half_cube_eq`). `IsSecondOrderStep` is Steps 1-9: the
half step of the moments, Ampère's law, K, S, L, L, S, K each with one SSPRK2 step of the frozen
right-hand side `P_Φ^⊥ D[E^{n+1/2}, N^{n+1/2}, ·]` with QR after the K and L steps (`w p` prepended
in the L steps, `IsVQR`), and the full step of the moments. **Theorem 3.2** is `theorem_3_2` (local
laws) and `theorem_3_2_total` (their integral over a period); **Corollary 3.3** is `corollary_3_3`
(arbitrary numerical fluxes on a periodic grid: local laws in flux form and constant totals) and
`corollary_3_3_linear` (linear fluxes: the local laws take the form of Theorem 3.2). Nothing is
assumed about the moments of the micro part: that `g` carries no charge, current or kinetic energy
follows from `V⁰ ⊥ Φ` and the QR steps (`IsVQR.perp`, `charge_eq`, `current_eq`, `kinetic_eq`), and
`IsMicroStep.exact` shows that the L steps stay in `Φ^⊥`, so the prepended QR commits no error.
Differences from the paper: the operator `D` is arbitrary, which covers the Vlasov operator with any
collision term and any discretization of `∂ₓ, ∂ᵥ`, so the velocity boundary condition on `g` plays
no role; the QR factorizations are relations, for any factorization, not necessarily triangular; the
matrix after an L step satisfies `Lᵢ = ∑ⱼ S'ᵢⱼ V'ⱼ`, which is `S'ᵢⱼ = R_{j+3,i+3}`, while the paper
prints `R_{i+3,j+3}`; the substep length in Steps 3-8 is taken as `Δt / 2`, which Section 3.3 does
not state explicitly and which the conservation proofs do not use; the spatial inner product is any
measure `ν`; differentiability of the midpoint moments is an explicit hypothesis of `theorem_3_2`,
and `C¹` and periodicity of `theorem_3_2_total`; only `p₀, …, p₃` are required, not a full
orthogonal sequence. In `corollary_3_3` the numerical flux at step `n` is a function of the flux
vector only, but it may change with `n`, so it may depend on the rest of the state. Second-order
accuracy is not treated. The scheme is not vacuous: `exists_run` and `exists_run_grid` run it for
every `D`, every spatial operator and every initial state with `V⁰ ⊥ Φ` whenever the QR
factorizations exist, in particular on a finite grid with room for the rank; `stationary_run` is a
run with the exact `∂ₓ` on the line; and `fourPointBasis` is an explicit `MomentBasis`, with
`rational_run` running the discrete scheme on it.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2311_09425

open MeasureTheory Polynomial

/-! ### Velocity: the weight and its orthonormal polynomials -/

/-- The velocity setting of arXiv 2311.09425 §2: a measure `μ` (the paper's `dμ = w(v) dv`, the
Hermite or Legendre weight; a discrete velocity grid with quadrature weights is allowed too) with
all polynomial moments finite, and orthonormal polynomials `p₀, …, p₃` with `deg pₖ = k`.
Only the polynomials up to degree three occur in the scheme. -/
structure MomentBasis (μ : Measure ℝ) where
  /-- The orthonormal polynomials `p₀, …, p₃`. -/
  p : Fin 4 → ℝ[X]
  integrable : ∀ q : ℝ[X], Integrable (fun v => q.eval v) μ
  natDegree_eq : ∀ k, (p k).natDegree = k
  orthonormal : ∀ i j, ∫ v, (p i * p j).eval v ∂μ = if i = j then 1 else 0

namespace MomentBasis

variable {μ : Measure ℝ} (B : MomentBasis μ)

/-- The integral `∫ q dμ` of a polynomial. -/
noncomputable def ell (_B : MomentBasis μ) (q : ℝ[X]) : ℝ := ∫ v, q.eval v ∂μ

/-- `∫ (q + r) dμ` splits (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem ell_add (q r : ℝ[X]) : B.ell (q + r) = B.ell q + B.ell r := by
  simp only [ell, eval_add]
  exact integral_add (B.integrable q) (B.integrable r)

/-- `∫ α q dμ = α ∫ q dμ` (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem ell_C_mul (α : ℝ) (q : ℝ[X]) : B.ell (C α * q) = α * B.ell q := by
  simp only [ell, eval_mul, eval_C]
  exact integral_const_mul _ _

/-- `∫ · dμ` commutes with finite sums (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem ell_sum {κ : Type*} (t : Finset κ) (f : κ → ℝ[X]) :
    B.ell (∑ k ∈ t, f k) = ∑ k ∈ t, B.ell (f k) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [ell]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, B.ell_add, ih]

/-- Orthonormality in terms of `ell` (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem ell_pp (i j : Fin 4) : B.ell (B.p i * B.p j) = if i = j then 1 else 0 :=
  B.orthonormal i j

/-- The combination `∑ₖ αₖ pₖ`. -/
noncomputable def comb (α : Fin 4 → ℝ) : ℝ[X] := ∑ k, C (α k) * B.p k

/-- The coefficients of a combination of the `pₖ` are recovered by integration (auxiliary for
Theorem 3.2 of arXiv 2311.09425). -/
theorem ell_comb_mul (α : Fin 4 → ℝ) (j : Fin 4) : B.ell (B.comb α * B.p j) = α j := by
  simp only [comb, Finset.sum_mul, mul_assoc]
  rw [B.ell_sum]
  simp only [B.ell_C_mul, B.ell_pp, mul_ite, mul_one, mul_zero]
  simp

/-- Division of a polynomial of degree `≤ n + 1` by one of degree exactly `n + 1`. -/
theorem exists_natDegree_sub_le {q r : ℝ[X]} {n : ℕ} (hr : r.natDegree = n + 1)
    (hq : q.natDegree ≤ n + 1) : ∃ α : ℝ, (q - C α * r).natDegree ≤ n := by
  have hr0 : r.coeff (n + 1) ≠ 0 := by
    have : r ≠ 0 := by rintro rfl; simp at hr
    rw [← hr]; exact leadingCoeff_ne_zero.mpr this
  refine ⟨q.coeff (n + 1) / r.coeff (n + 1), ?_⟩
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_sub, coeff_C_mul]
  obtain rfl | h := eq_or_lt_of_le (Nat.succ_le_of_lt hN)
  · field_simp
    simp
  · have h' : n + 1 < N := h
    rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hq h'),
      coeff_eq_zero_of_natDegree_lt (by omega : r.natDegree < N)]
    simp

/-- A polynomial of degree at most `m ≤ 3` is a combination of `p₀, …, pₘ` (auxiliary for Theorem
3.2 of arXiv 2311.09425). -/
theorem exists_comb (m : ℕ) (hm : m ≤ 3) (q : ℝ[X]) (hq : q.natDegree ≤ m) :
    ∃ α : Fin 4 → ℝ, q = B.comb α ∧ ∀ k : Fin 4, m < k → α k = 0 := by
  induction m generalizing q with
  | zero =>
    have h0 : B.p 0 ≠ 0 := by
      intro h
      have := B.ell_pp 0 0
      simp [h, ell] at this
    obtain ⟨a, rfl⟩ : ∃ a, q = C a := ⟨_, eq_C_of_natDegree_le_zero hq⟩
    obtain ⟨b, hb⟩ : ∃ b, B.p 0 = C b :=
      ⟨_, eq_C_of_natDegree_le_zero (by simpa using (B.natDegree_eq 0).le)⟩
    have hb0 : b ≠ 0 := by rintro rfl; simp [hb] at h0
    refine ⟨fun k => if k = 0 then a / b else 0, ?_, ?_⟩
    · simp [comb, Fin.sum_univ_four, hb, ← C_mul, hb0]
    · intro k hk
      have : k ≠ 0 := by rintro rfl; simp at hk
      simp [this]
  | succ m ih =>
    have hm' : m + 1 < 4 := by omega
    obtain ⟨β, hβ⟩ := exists_natDegree_sub_le (q := q) (r := B.p ⟨m + 1, hm'⟩)
      (B.natDegree_eq ⟨m + 1, hm'⟩) hq
    obtain ⟨α, hα, hα0⟩ := ih (by omega) _ hβ
    refine ⟨fun k => α k + if k = ⟨m + 1, hm'⟩ then β else 0, ?_, ?_⟩
    · have : q = B.comb α + C β * B.p ⟨m + 1, hm'⟩ := by rw [← hα]; ring
      rw [this]
      simp only [comb, C_add, add_mul, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single (⟨m + 1, hm'⟩ : Fin 4)]
      · simp
      · intro k _ hk; simp [hk]
      · simp
    · intro k hk
      have h1 : k ≠ ⟨m + 1, hm'⟩ := by
        rintro rfl; simp at hk
      simp only [h1, ite_false, add_zero]
      exact hα0 k (by omega)

/-- Expansion in the orthonormal polynomials (degree at most three). -/
theorem expand {q : ℝ[X]} (m : ℕ) (hm : m ≤ 3) (hq : q.natDegree ≤ m) :
    q = ∑ k, C (B.ell (q * B.p k)) * B.p k := by
  obtain ⟨α, hα, -⟩ := B.exists_comb m hm q hq
  conv_lhs => rw [hα]
  conv_rhs => rw [hα]
  simp only [B.ell_comb_mul]
  rfl

/-- `pₖ` is orthogonal to the polynomials of degree below `k` (auxiliary for Theorem 3.2 of arXiv
2311.09425). -/
theorem ell_mul_eq_zero {q : ℝ[X]} (m : ℕ) (hm : m ≤ 3) (hq : q.natDegree ≤ m) (k : Fin 4)
    (hk : m < k) : B.ell (q * B.p k) = 0 := by
  obtain ⟨α, hα, h0⟩ := B.exists_comb m hm q hq
  rw [hα, B.ell_comb_mul, h0 k hk]

/-- Multiplication by `X` raises the degree by at most one (auxiliary for Theorem 3.2 of arXiv
2311.09425). -/
theorem natDegree_X_mul {q : ℝ[X]} {n : ℕ} (h : q.natDegree ≤ n) : (X * q).natDegree ≤ n + 1 := by
  refine natDegree_mul_le.trans ?_
  rw [natDegree_X]
  omega

/-- Expansion of a polynomial of degree zero (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem expand₀ {q : ℝ[X]} (hq : q.natDegree ≤ 0) : q = C (B.ell (q * B.p 0)) * B.p 0 := by
  have h := B.expand 0 (by norm_num) hq
  rw [Fin.sum_univ_four, B.ell_mul_eq_zero 0 (by norm_num) hq 1 (by simp),
    B.ell_mul_eq_zero 0 (by norm_num) hq 2 (by simp),
    B.ell_mul_eq_zero 0 (by norm_num) hq 3 (by simp)] at h
  simpa using h

/-- Expansion of a polynomial of degree at most one (auxiliary for Theorem 3.2 of arXiv 2311.09425).
-/
theorem expand₁ {q : ℝ[X]} (hq : q.natDegree ≤ 1) :
    q = C (B.ell (q * B.p 0)) * B.p 0 + C (B.ell (q * B.p 1)) * B.p 1 := by
  have h := B.expand 1 (by norm_num) hq
  rw [Fin.sum_univ_four, B.ell_mul_eq_zero 1 (by norm_num) hq 2 (by simp),
    B.ell_mul_eq_zero 1 (by norm_num) hq 3 (by simp)] at h
  simpa using h

/-- Expansion of a polynomial of degree at most two (auxiliary for Theorem 3.2 of arXiv 2311.09425).
-/
theorem expand₂ {q : ℝ[X]} (hq : q.natDegree ≤ 2) :
    q = C (B.ell (q * B.p 0)) * B.p 0 + C (B.ell (q * B.p 1)) * B.p 1
      + C (B.ell (q * B.p 2)) * B.p 2 := by
  have h := B.expand 2 (by norm_num) hq
  rw [Fin.sum_univ_four, B.ell_mul_eq_zero 2 (by norm_num) hq 3 (by simp)] at h
  simpa using h

/-- Expansion of a polynomial of degree at most three (auxiliary for Theorem 3.2 of arXiv
2311.09425). -/
theorem expand₃ {q : ℝ[X]} (hq : q.natDegree ≤ 3) :
    q = C (B.ell (q * B.p 0)) * B.p 0 + C (B.ell (q * B.p 1)) * B.p 1
      + C (B.ell (q * B.p 2)) * B.p 2 + C (B.ell (q * B.p 3)) * B.p 3 := by
  have h := B.expand 3 (by norm_num) hq
  rwa [Fin.sum_univ_four] at h

/-- The recurrence coefficient `aₙ = ∫ v pₙ pₙ₊₁ dμ` of `v pₙ = aₙ pₙ₊₁ + bₙ pₙ + aₙ₋₁ pₙ₋₁`
(see `rec₀`, `rec₁`, `rec₂`). -/
noncomputable def a (n : Fin 3) : ℝ := B.ell (X * B.p n.castSucc * B.p n.succ)

/-- The recurrence coefficient `bₙ = ∫ v pₙ² dμ`. -/
noncomputable def b (n : Fin 3) : ℝ := B.ell (X * B.p n.castSucc * B.p n.castSucc)

/-- The collision invariants `φ = (1, v, v²/2)`. -/
noncomputable def φ : Fin 3 → ℝ[X] := ![1, X, C (1 / 2) * X ^ 2]

/-- The entries of the lower triangular matrix `C` of `φ = C p` (see `one_eq`, `X_eq`,
`half_sq_eq`). -/
noncomputable def c (i j : Fin 3) : ℝ := B.ell (φ i * B.p j.castSucc)

/-- The derivative coefficients of `p₁' = d₁₀ p₀`, `p₂' = d₂₀ p₀ + d₂₁ p₁` (see `deriv₁`,
`deriv₂`). -/
noncomputable def d (i j : Fin 3) : ℝ := B.ell (derivative (B.p i.castSucc) * B.p j.castSucc)

/-- Degree bound for `pₖ` (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem natDegree_p_le (k : Fin 4) {n : ℕ} (h : (k : ℕ) ≤ n) : (B.p k).natDegree ≤ n := by
  rw [B.natDegree_eq]; exact h

/-- The three-term recurrence for `n = 0`: `v p₀ = a₀ p₁ + b₀ p₀`, derived from orthonormality
(auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem rec₀ : X * B.p 0 = C (B.b 0) * B.p 0 + C (B.a 0) * B.p 1 :=
  B.expand₁ (natDegree_X_mul (B.natDegree_p_le 0 (by simp)))

/-- The three-term recurrence for `n = 1`: `v p₁ = a₁ p₂ + b₁ p₁ + a₀ p₀`, derived from
orthonormality (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem rec₁ : X * B.p 1 = C (B.a 0) * B.p 0 + C (B.b 1) * B.p 1 + C (B.a 1) * B.p 2 := by
  have h := B.expand₂ (natDegree_X_mul (B.natDegree_p_le 1 (by simp)))
  have h0 : B.ell (X * B.p 1 * B.p 0) = B.a 0 := by
    simp only [a]; congr 1; simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one]; ring
  rw [h0] at h
  exact h

/-- The three-term recurrence for `n = 2`: `v p₂ = a₂ p₃ + b₂ p₂ + a₁ p₁`, derived from
orthonormality (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem rec₂ : X * B.p 2 = C (B.a 1) * B.p 1 + C (B.b 2) * B.p 2 + C (B.a 2) * B.p 3 := by
  have h := B.expand₃ (natDegree_X_mul (B.natDegree_p_le 2 (by simp)))
  have h0 : B.ell (X * B.p 2 * B.p 0) = 0 := by
    have := B.ell_mul_eq_zero (q := X * B.p 0) 1 (by norm_num)
      (natDegree_X_mul (B.natDegree_p_le 0 (by simp))) 2 (by simp)
    rw [← this]; congr 1; ring
  have h1 : B.ell (X * B.p 2 * B.p 1) = B.a 1 := by
    have : B.a 1 = B.ell (X * B.p 1 * B.p 2) := rfl
    rw [this]; congr 1; ring
  have h2 : B.ell (X * B.p 2 * B.p 2) = B.b 2 := rfl
  have h3 : B.ell (X * B.p 2 * B.p 3) = B.a 2 := rfl
  rw [h0, h1, h2, h3] at h
  simpa using h

/-- First row of `φ = C p`: `1 = c₀₀ p₀` (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem one_eq : (1 : ℝ[X]) = C (B.c 0 0) * B.p 0 := by
  have h := B.expand₀ (q := 1) (by simp)
  exact h

/-- Second row of `φ = C p`: `v = c₁₀ p₀ + c₁₁ p₁` (auxiliary for Theorem 3.2 of arXiv 2311.09425).
-/
theorem X_eq : (X : ℝ[X]) = C (B.c 1 0) * B.p 0 + C (B.c 1 1) * B.p 1 :=
  B.expand₁ (q := X) (by simp)

/-- Third row of `φ = C p`: `v²/2 = c₂₀ p₀ + c₂₁ p₁ + c₂₂ p₂` (auxiliary for Theorem 3.2 of arXiv
2311.09425). -/
theorem half_sq_eq :
    (C (1 / 2) * X ^ 2 : ℝ[X]) = C (B.c 2 0) * B.p 0 + C (B.c 2 1) * B.p 1 + C (B.c 2 2) * B.p 2 :=
  B.expand₂ (q := C (1 / 2) * X ^ 2) (natDegree_C_mul_X_pow_le _ _)

/-- `p₁' = d₁₀ p₀`, derived from orthonormality (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem deriv₁ : derivative (B.p 1) = C (B.d 1 0) * B.p 0 := by
  refine B.expand₀ (q := derivative (B.p 1)) ?_
  refine (natDegree_derivative_le _).trans ?_
  rw [B.natDegree_eq]; simp

/-- `p₂' = d₂₀ p₀ + d₂₁ p₁`, derived from orthonormality (auxiliary for Theorem 3.2 of arXiv
2311.09425). -/
theorem deriv₂ : derivative (B.p 2) = C (B.d 2 0) * B.p 0 + C (B.d 2 1) * B.p 1 := by
  refine B.expand₁ (q := derivative (B.p 2)) ?_
  refine (natDegree_derivative_le _).trans ?_
  rw [B.natDegree_eq]; simp

/-- The `p₀` coefficient of a combination of `p₀, p₁` (auxiliary for Theorem 3.2 of arXiv
2311.09425). -/
theorem ell_lin₀ (α β : ℝ) : B.ell ((C α * B.p 0 + C β * B.p 1) * B.p 0) = α := by
  simp [add_mul, mul_assoc, B.ell_add, B.ell_C_mul, B.ell_pp]

/-- The `p₁` coefficient of a combination of `p₀, p₁` (auxiliary for Theorem 3.2 of arXiv
2311.09425). -/
theorem ell_lin₁ (α β : ℝ) : B.ell ((C α * B.p 0 + C β * B.p 1) * B.p 1) = β := by
  simp [add_mul, mul_assoc, B.ell_add, B.ell_C_mul, B.ell_pp]

/-- `v = c₀₀ (b₀ p₀ + a₀ p₁)`, from `1 = c₀₀ p₀` and the recurrence (auxiliary for Theorem 3.2 of
arXiv 2311.09425). -/
theorem X_eq' : (X : ℝ[X]) = C (B.c 0 0 * B.b 0) * B.p 0 + C (B.c 0 0 * B.a 0) * B.p 1 := by
  calc (X : ℝ[X]) = C (B.c 0 0) * (X * B.p 0) := by
        linear_combination (X : ℝ[X]) * B.one_eq
    _ = _ := by rw [B.rec₀, C_mul, C_mul]; ring

/-- `c₁₀ = c₀₀ b₀`. -/
theorem c_one_zero : B.c 1 0 = B.c 0 0 * B.b 0 := by
  have h := B.ell_lin₀ (B.c 0 0 * B.b 0) (B.c 0 0 * B.a 0)
  rw [← B.X_eq'] at h
  exact h

/-- `c₁₁ = c₀₀ a₀`. -/
theorem c_one_one : B.c 1 1 = B.c 0 0 * B.a 0 := by
  have h := B.ell_lin₁ (B.c 0 0 * B.b 0) (B.c 0 0 * B.a 0)
  rw [← B.X_eq'] at h
  exact h

/-- `v = (c₂₁ d₁₀ + c₂₂ d₂₀) p₀ + c₂₂ d₂₁ p₁`, the derivative of `v²/2 = c₂₀ p₀ + c₂₁ p₁ + c₂₂ p₂`
(auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem X_eq'' : (X : ℝ[X]) = C (B.c 2 1 * B.d 1 0 + B.c 2 2 * B.d 2 0) * B.p 0
    + C (B.c 2 2 * B.d 2 1) * B.p 1 := by
  have h := congrArg derivative B.half_sq_eq
  have h1 : derivative (B.p 0) = 0 := by
    apply derivative_of_natDegree_zero
    exact B.natDegree_eq 0
  have h2 : derivative (C (1 / 2) * X ^ 2 : ℝ[X]) = X := by
    simp only [derivative_C_mul, derivative_X_pow]
    rw [show ((2 : ℕ) - 1) = 1 from rfl, pow_one, ← mul_assoc]
    have : (C (1 / 2 : ℝ) : ℝ[X]) * (C ((2 : ℕ) : ℝ) : ℝ[X]) = 1 := by
      rw [← C_mul]; norm_num
    simp only [Nat.cast_ofNat, map_ofNat] at this ⊢
    rw [this, one_mul]
  rw [h2] at h
  simp only [derivative_add, derivative_C_mul, h1, B.deriv₁, B.deriv₂, C_add, C_mul] at h ⊢
  rw [h]; ring

/-- `c₁₀ = c₂₁ d₁₀ + c₂₂ d₂₀`: the coefficient that turns the electric source into `E J`. -/
theorem c_one_zero' : B.c 1 0 = B.c 2 1 * B.d 1 0 + B.c 2 2 * B.d 2 0 := by
  have h := B.ell_lin₀ (B.c 2 1 * B.d 1 0 + B.c 2 2 * B.d 2 0) (B.c 2 2 * B.d 2 1)
  rw [← B.X_eq''] at h
  exact h

/-- `c₁₁ = c₂₂ d₂₁`. -/
theorem c_one_one' : B.c 1 1 = B.c 2 2 * B.d 2 1 := by
  have h := B.ell_lin₁ (B.c 2 1 * B.d 1 0 + B.c 2 2 * B.d 2 0) (B.c 2 2 * B.d 2 1)
  rw [← B.X_eq''] at h
  exact h

/-- The expansion of `v³/2`, which is the identity behind the energy flux. -/
theorem half_cube_eq : (C (1 / 2) * X ^ 3 : ℝ[X]) =
    C (B.c 2 0 * B.b 0 + B.c 2 1 * B.a 0) * B.p 0
    + C (B.c 2 0 * B.a 0 + B.c 2 1 * B.b 1 + B.c 2 2 * B.a 1) * B.p 1
    + C (B.c 2 1 * B.a 1 + B.c 2 2 * B.b 2) * B.p 2
    + C (B.c 2 2 * B.a 2) * B.p 3 := by
  calc (C (1 / 2) * X ^ 3 : ℝ[X]) = X * (C (1 / 2) * X ^ 2) := by ring
    _ = C (B.c 2 0) * (X * B.p 0) + C (B.c 2 1) * (X * B.p 1) + C (B.c 2 2) * (X * B.p 2) := by
        rw [B.half_sq_eq]; ring
    _ = _ := by
        rw [B.rec₀, B.rec₁, B.rec₂]
        simp only [C_add, C_mul]
        ring

/-! ### The velocity Hilbert space -/

/-- Polynomials lie in `L²(μ)` (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem memLp (B : MomentBasis μ) (q : ℝ[X]) : MemLp (fun v => q.eval v) 2 μ := by
  refine (memLp_two_iff_integrable_sq q.continuous.aestronglyMeasurable).2 ?_
  simpa [pow_two] using B.integrable (q * q)

/-- The class of the polynomial `q` in `L²(μ)`, which represents `w q` in the paper's
`L²(w⁻¹ dv)`: the map `f ↦ f / w` is an isometry from `L²(w⁻¹ dv)` onto `L²(μ)`. -/
noncomputable def emb (q : ℝ[X]) : Lp ℝ 2 μ := (B.memLp q).toLp _

/-- `emb` is additive (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem emb_add (q r : ℝ[X]) : B.emb (q + r) = B.emb q + B.emb r := by
  ext1
  filter_upwards [(B.memLp (q + r)).coeFn_toLp, (B.memLp q).coeFn_toLp, (B.memLp r).coeFn_toLp,
    Lp.coeFn_add (B.emb q) (B.emb r)] with v h1 h2 h3 h4
  simp only [emb] at h4 ⊢
  rw [h1, h4, Pi.add_apply, h2, h3, eval_add]

/-- `emb` is homogeneous (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem emb_C_mul (α : ℝ) (q : ℝ[X]) : B.emb (C α * q) = α • B.emb q := by
  ext1
  filter_upwards [(B.memLp (C α * q)).coeFn_toLp, (B.memLp q).coeFn_toLp,
    Lp.coeFn_smul α (B.emb q)] with v h1 h2 h3
  simp only [emb] at h3 ⊢
  rw [h1, h3, Pi.smul_apply, h2, eval_mul, eval_C, smul_eq_mul]

/-- The inner product with `emb q` is the moment `∫ q h dμ` (auxiliary for Theorem 3.2 of arXiv
2311.09425). -/
theorem inner_emb (q : ℝ[X]) (h : Lp ℝ 2 μ) : ⟪B.emb q, h⟫ = ∫ v, q.eval v * h v ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(B.memLp q).coeFn_toLp] with v hv
  simp only [emb]
  rw [hv, real_inner_comm]
  simp

/-- The inner product of two polynomials (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem inner_emb_emb (q r : ℝ[X]) : ⟪B.emb q, B.emb r⟫ = B.ell (q * r) := by
  rw [B.inner_emb]
  refine integral_congr_ae ?_
  filter_upwards [(B.memLp r).coeFn_toLp] with v hv
  simp only [emb]
  rw [hv, eval_mul]

/-- The vector `w pₖ`. -/
noncomputable def wp (k : Fin 4) : Lp ℝ 2 μ := B.emb (B.p k)

/-- `w p₀, …, w p₃` are orthonormal (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem inner_wp_wp (i j : Fin 4) : ⟪B.wp i, B.wp j⟫ = if i = j then 1 else 0 := by
  rw [wp, wp, B.inner_emb_emb, B.ell_pp]

/-- The moment `⟨q h⟩_v = ∫ q(v) h(v) dμ(v)`, the paper's `⟨q f⟩_v` for `f = w h`. -/
noncomputable def mom (_B : MomentBasis μ) (q : ℝ[X]) (h : Lp ℝ 2 μ) : ℝ :=
  ∫ v, q.eval v * h v ∂μ

/-- The moment is an inner product (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem mom_eq (q : ℝ[X]) (h : Lp ℝ 2 μ) : B.mom q h = ⟪B.emb q, h⟫ := (B.inner_emb q h).symm

/-- The orthogonal complement `Φ^⊥` of `Φ = span{w, v w, v² w / 2} = span{w p₀, w p₁, w p₂}`. -/
def Φperp : Submodule ℝ (Lp ℝ 2 μ) where
  carrier := {h | ⟪B.wp 0, h⟫ = 0 ∧ ⟪B.wp 1, h⟫ = 0 ∧ ⟪B.wp 2, h⟫ = 0}
  add_mem' := by
    rintro a b ⟨h0, h1, h2⟩ ⟨k0, k1, k2⟩
    simp [inner_add_right, h0, h1, h2, k0, k1, k2]
  zero_mem' := by simp
  smul_mem' := by
    rintro c a ⟨h0, h1, h2⟩
    simp [inner_smul_right, h0, h1, h2]

/-- Membership in `Φ^⊥` (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem mem_Φperp {h : Lp ℝ 2 μ} :
    h ∈ B.Φperp ↔ ⟪B.wp 0, h⟫ = 0 ∧ ⟪B.wp 1, h⟫ = 0 ∧ ⟪B.wp 2, h⟫ = 0 := Iff.rfl

/-- `P_Φ^⊥ = I - P_Φ` with `P_Φ h = w pᵀ ⟨p h⟩_v` (paper (2.10)). -/
noncomputable def Pperp (h : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  h - (B.mom (B.p 0) h • B.wp 0 + B.mom (B.p 1) h • B.wp 1 + B.mom (B.p 2) h • B.wp 2)

/-- `P_Φ^⊥` maps into `Φ^⊥` (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem Pperp_mem (h : Lp ℝ 2 μ) : B.Pperp h ∈ B.Φperp := by
  have e : ∀ k, B.mom (B.p k) h = ⟪B.wp k, h⟫ := fun k => B.mom_eq _ _
  simp only [Pperp, e]
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [inner_sub_right, inner_add_right, inner_smul_right, B.inner_wp_wp]
    simp

end MomentBasis

/-! ### The second-order integrator -/

/-- One SSPRK2 step (paper (3.36)): `q* = q + τ F(q)`, `q⁺ = q / 2 + (q* + τ F(q*)) / 2`. -/
noncomputable def ssprk2 {Q : Type*} [AddCommGroup Q] [Module ℝ Q] (F : Q → Q) (τ : ℝ) (q : Q) :
    Q :=
  (1 / 2 : ℝ) • q + (1 / 2 : ℝ) • ((q + τ • F q) + τ • F (q + τ • F q))

/-- SSPRK2 preserves a subspace that contains the right-hand side (auxiliary for Theorem 3.2 of
arXiv 2311.09425). -/
theorem ssprk2_mem {ι H : Type*} [AddCommGroup H] [Module ℝ H] (W : Submodule ℝ H)
    {F : (ι → H) → (ι → H)} (hF : ∀ q i, F q i ∈ W) {q : ι → H} (hq : ∀ i, q i ∈ W) (τ : ℝ)
    (i : ι) : ssprk2 F τ q i ∈ W := by
  simp only [ssprk2, Pi.add_apply, Pi.smul_apply]
  exact W.add_mem (W.smul_mem _ (hq i)) (W.smul_mem _ (W.add_mem
    (W.add_mem (hq i) (W.smul_mem _ (hF _ i))) (W.smul_mem _ (hF _ i))))

/-- The data of the scheme at one time level, integer or half-integer: the moments
`(f₀, f₁, f₂)`, the electric field `E` and the low-rank factors `(X, S, V)` of the micro part.
A velocity profile `f = w h` is stored as `h ∈ L²(μ)` (see `MomentBasis.emb`). -/
structure State (μ : Measure ℝ) (𝕏 ι : Type*) where
  /-- The moment `f₀`. -/
  f₀ : 𝕏 → ℝ
  /-- The moment `f₁`. -/
  f₁ : 𝕏 → ℝ
  /-- The moment `f₂`. -/
  f₂ : 𝕏 → ℝ
  /-- The electric field. -/
  E : 𝕏 → ℝ
  /-- The spatial basis. -/
  X : ι → 𝕏 → ℝ
  /-- The coefficient matrix. -/
  S : Matrix ι ι ℝ
  /-- The velocity basis. -/
  V : ι → Lp ℝ 2 μ

section Scheme

variable {μ : Measure ℝ} {𝕏 ι : Type*} [Fintype ι]

/-- The low-rank function `g = ∑ᵢⱼ Xᵢ Sᵢⱼ Vⱼ` (paper (3.1)). -/
noncomputable def lowRank (X : ι → 𝕏 → ℝ) (S : Matrix ι ι ℝ) (V : ι → Lp ℝ 2 μ) (x : 𝕏) :
    Lp ℝ 2 μ :=
  ∑ i, ∑ j, (X i x * S i j) • V j

/-- The inner product with a low-rank function (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem inner_lowRank (X : ι → 𝕏 → ℝ) (S : Matrix ι ι ℝ) (V : ι → Lp ℝ 2 μ) (x : 𝕏)
    (u : Lp ℝ 2 μ) : ⟪u, lowRank X S V x⟫ = ∑ i, ∑ j, X i x * S i j * ⟪u, V j⟫ := by
  simp only [lowRank, inner_sum, inner_smul_right]

/-- The right-hand side of the K equation `∂ₜKⱼ = ⟨Vⱼ, G(∑ₗ Kₗ Vₗ)⟩`, with the velocity basis
frozen. -/
noncomputable def kField (G : (𝕏 → Lp ℝ 2 μ) → 𝕏 → Lp ℝ 2 μ) (V : ι → Lp ℝ 2 μ)
    (K : ι → 𝕏 → ℝ) : ι → 𝕏 → ℝ :=
  fun j x => ⟪V j, G (fun y => ∑ l, K l y • V l) x⟫

/-- The right-hand side of the S equation `∂ₜSᵢⱼ = -⟨Xᵢ Vⱼ, G(∑ₖₗ Xₖ Sₖₗ Vₗ)⟩`. -/
noncomputable def sField [MeasurableSpace 𝕏] (ν : Measure 𝕏)
    (G : (𝕏 → Lp ℝ 2 μ) → 𝕏 → Lp ℝ 2 μ) (X : ι → 𝕏 → ℝ) (V : ι → Lp ℝ 2 μ)
    (S : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => -∫ x, X i x * ⟪V j, G (lowRank X S V) x⟫ ∂ν

/-- The right-hand side of the L equation `∂ₜLᵢ = ⟨Xᵢ, G(∑ₖ Xₖ Lₖ)⟩ₓ`, a Bochner integral in
`L²(μ)`. -/
noncomputable def lField [MeasurableSpace 𝕏] (ν : Measure 𝕏)
    (G : (𝕏 → Lp ℝ 2 μ) → 𝕏 → Lp ℝ 2 μ) (X : ι → 𝕏 → ℝ) (L : ι → Lp ℝ 2 μ) : ι → Lp ℝ 2 μ :=
  fun i => ∫ x, X i x • G (fun y => ∑ k, X k y • L k) x ∂ν

/-- The initial value `Kⱼ = ∑ᵢ Xᵢ Sᵢⱼ` of a K step. -/
def kInit (X : ι → 𝕏 → ℝ) (S : Matrix ι ι ℝ) : ι → 𝕏 → ℝ := fun j x => ∑ i, X i x * S i j

/-- The initial value `Lᵢ = ∑ⱼ Sᵢⱼ Vⱼ` of an L step. -/
noncomputable def lInit (S : Matrix ι ι ℝ) (V : ι → Lp ℝ 2 μ) : ι → Lp ℝ 2 μ :=
  fun i => ∑ j, S i j • V j

/-- The QR factorization `K = X' S'` after a K step: `X'` is orthonormal in `L²(ν)`.  The theorems
hold for every such factorization; `S'` need not be triangular. -/
structure IsXQR [DecidableEq ι] [MeasurableSpace 𝕏] (ν : Measure 𝕏) (K X' : ι → 𝕏 → ℝ)
    (S' : Matrix ι ι ℝ) : Prop where
  orthonormal : ∀ i j, ∫ x, X' i x * X' j x ∂ν = if i = j then 1 else 0
  factor : ∀ j x, K j x = ∑ i, X' i x * S' i j

namespace MomentBasis

variable (B : MomentBasis μ)

/-- The first three vectors `w p₀, w p₁, w p₂`, which are prepended in the QR factorization. -/
noncomputable def wpΦ : Fin 3 → Lp ℝ 2 μ := fun k => B.wp k.castSucc

/-- The QR factorization (paper (3.20)) after an L step, with `w p₀, w p₁, w p₂` prepended:
`[w p, V'] R = [w p, L]`, and `S'` is the block of `R` with `Lᵢ = ∑ⱼ S'ᵢⱼ V'ⱼ` (the paper's
`S'ᵢⱼ = R_{i+3,j+3}` up to the transposition that this equation needs).  The theorems hold for
every such factorization; `R` need not be triangular. -/
structure IsVQR (L V' : ι → Lp ℝ 2 μ) (S' : Matrix ι ι ℝ) : Prop where
  orthonormal : Orthonormal ℝ (Sum.elim B.wpΦ V')
  factor : ∃ R : Matrix (Fin 3 ⊕ ι) (Fin 3 ⊕ ι) ℝ,
    (∀ j, Sum.elim B.wpΦ L j = ∑ k, R k j • Sum.elim B.wpΦ V' k) ∧
      ∀ i j, S' i j = R (Sum.inr j) (Sum.inr i)

/-- Steps 3-8 of the scheme: K, S, L, L, S, K, each advanced by one SSPRK2 step of length `τ`
with the right-hand side `G` frozen (`G` contains `N^{n+1/2}` and `E^{n+1/2}`), from `(X₀, S₀, V₀)`
through the midpoint `(Xm, Sm, Vm)` to `(X₁, S₁, V₁)`.  The matrices `S¹, S², S³, S⁴` of the paper
are `Sa, Sb, Sc, Sd`. -/
structure IsMicroStep [DecidableEq ι] [MeasurableSpace 𝕏] (ν : Measure 𝕏)
    (G : (𝕏 → Lp ℝ 2 μ) → 𝕏 → Lp ℝ 2 μ) (τ : ℝ) (X₀ Xm X₁ : ι → 𝕏 → ℝ)
    (S₀ Sa Sb Sm Sc Sd S₁ : Matrix ι ι ℝ) (V₀ Vm V₁ : ι → Lp ℝ 2 μ) : Prop where
  step3 : IsXQR ν (ssprk2 (kField G V₀) τ (kInit X₀ S₀)) Xm Sa
  step4 : Sb = ssprk2 (sField ν G Xm V₀) τ Sa
  step5 : B.IsVQR (ssprk2 (lField ν G Xm) τ (lInit Sb V₀)) Vm Sm
  step6 : B.IsVQR (ssprk2 (lField ν G Xm) τ (lInit Sm Vm)) V₁ Sc
  step7 : Sd = ssprk2 (sField ν G Xm V₁) τ Sc
  step8 : IsXQR ν (ssprk2 (kField G V₁) τ (kInit Xm Sd)) X₁ S₁

/-- The macro part `N = w (p₀ f₀ + p₁ f₁ + p₂ f₂)` (paper (2.11)). -/
noncomputable def macroPart (s : State μ 𝕏 ι) (x : 𝕏) : Lp ℝ 2 μ :=
  s.f₀ x • B.wp 0 + s.f₁ x • B.wp 1 + s.f₂ x • B.wp 2

/-- The distribution function `f = N + g`. -/
noncomputable def dist (s : State μ 𝕏 ι) (x : 𝕏) : Lp ℝ 2 μ :=
  B.macroPart s x + lowRank s.X s.S s.V x

/-- The closure `f₃ = ∑ᵢⱼ Xᵢ Sᵢⱼ ⟨p₃ Vⱼ⟩_v` (paper (3.16)). -/
noncomputable def f₃ (s : State μ 𝕏 ι) (x : 𝕏) : ℝ :=
  ∑ i, ∑ j, s.X i x * s.S i j * B.mom (B.p 3) (s.V j)

/-- The charge density `ρ = ⟨f, 1⟩_v`. -/
noncomputable def charge (s : State μ 𝕏 ι) (x : 𝕏) : ℝ := ∫ v, B.dist s x v ∂μ

/-- The current `J = ⟨f, v⟩_v`. -/
noncomputable def current (s : State μ 𝕏 ι) (x : 𝕏) : ℝ := ∫ v, v * B.dist s x v ∂μ

/-- The kinetic energy density `κ = ⟨f, v²/2⟩_v`. -/
noncomputable def kinetic (s : State μ 𝕏 ι) (x : 𝕏) : ℝ := ∫ v, v ^ 2 / 2 * B.dist s x v ∂μ

/-- The total energy density `e = κ + |E|²/2`. -/
noncomputable def energy (s : State μ 𝕏 ι) (x : 𝕏) : ℝ := B.kinetic s x + s.E x ^ 2 / 2

/-- The energy flux `⟨f, v³/2⟩_v`. -/
noncomputable def heatFlux (s : State μ 𝕏 ι) (x : 𝕏) : ℝ := ∫ v, v ^ 3 / 2 * B.dist s x v ∂μ

/-- The flux vector of the moment equations, with the signs of (3.29)-(3.31):
`(-b₀ f₀ - a₀ f₁, -a₁ f₂ - b₁ f₁ - a₀ f₀, -a₂ f₃ - b₂ f₂ - a₁ f₁)`. -/
noncomputable def flux (s : State μ 𝕏 ι) : Fin 3 → 𝕏 → ℝ :=
  ![fun x => -B.b 0 * s.f₀ x - B.a 0 * s.f₁ x,
    fun x => -B.a 1 * s.f₂ x - B.b 1 * s.f₁ x - B.a 0 * s.f₀ x,
    fun x => -B.a 2 * B.f₃ s x - B.b 2 * s.f₂ x - B.a 1 * s.f₁ x]

/-- The projected right-hand side `G(g) = P_Φ^⊥ D[E, N, g]` of Steps 3-8, frozen at the midpoint
state `m`. -/
noncomputable def frozen (D : (𝕏 → ℝ) → (𝕏 → Lp ℝ 2 μ) → (𝕏 → Lp ℝ 2 μ) → 𝕏 → Lp ℝ 2 μ)
    (m : State μ 𝕏 ι) : (𝕏 → Lp ℝ 2 μ) → 𝕏 → Lp ℝ 2 μ :=
  fun g x => B.Pperp (D m.E (B.macroPart m) g x)

/-- One step of the second-order integrator of arXiv 2311.09425 §3.3 from `s` (level `n`) through
`m` (level `n + 1/2`) to `s'` (level `n + 1`).

* Steps 1, 9 are (3.29)-(3.31) and (3.33)-(3.35), with `∂ₓ` replaced by a map `Dₓ` acting on the
  flux vector.  For `Dₓ F k = deriv (F k)` these are the equations of the paper; a conservative
  spatial discretization is `Dₓ = fluxDiff _ _`.
* Step 2 is Ampère's law (3.32) with the midpoint field `E^{n+1/2} = (E^{n+1} + Eⁿ) / 2`.
* Steps 3-8 are `IsMicroStep` with `τ = Δt / 2`.  The operator `D` is arbitrary, so this covers
  the Vlasov operator `D[E, N, g] = -(v ∂ₓ N + E ∂ᵥ N + v ∂ₓ g + E ∂ᵥ g) + Q(N + g)` for any
  collision operator and any discretization of `∂ₓ` and `∂ᵥ`. -/
structure IsSecondOrderStep [DecidableEq ι] [MeasurableSpace 𝕏] (ν : Measure 𝕏)
    (D : (𝕏 → ℝ) → (𝕏 → Lp ℝ 2 μ) → (𝕏 → Lp ℝ 2 μ) → 𝕏 → Lp ℝ 2 μ)
    (Dₓ : (Fin 3 → 𝕏 → ℝ) → Fin 3 → 𝕏 → ℝ) (Δt : ℝ) (s m s' : State μ 𝕏 ι) : Prop where
  half₀ : ∀ x, (m.f₀ x - s.f₀ x) / (Δt / 2) = Dₓ (B.flux s) 0 x
  half₁ : ∀ x, (m.f₁ x - s.f₁ x) / (Δt / 2) = Dₓ (B.flux s) 1 x + s.E x * (B.d 1 0 * s.f₀ x)
  half₂ : ∀ x, (m.f₂ x - s.f₂ x) / (Δt / 2) =
    Dₓ (B.flux s) 2 x + s.E x * (B.d 2 0 * s.f₀ x + B.d 2 1 * s.f₁ x)
  ampere : ∀ x, (s'.E x - s.E x) / Δt = -(B.c 1 0 * m.f₀ x + B.c 1 1 * m.f₁ x)
  midE : ∀ x, m.E x = (s'.E x + s.E x) / 2
  micro : ∃ Sa Sb Sc Sd, B.IsMicroStep ν (B.frozen D m) (Δt / 2) s.X m.X s'.X s.S Sa Sb m.S Sc Sd
    s'.S s.V m.V s'.V
  full₀ : ∀ x, (s'.f₀ x - s.f₀ x) / Δt = Dₓ (B.flux m) 0 x
  full₁ : ∀ x, (s'.f₁ x - s.f₁ x) / Δt = Dₓ (B.flux m) 1 x + m.E x * (B.d 1 0 * m.f₀ x)
  full₂ : ∀ x, (s'.f₂ x - s.f₂ x) / Δt =
    Dₓ (B.flux m) 2 x + m.E x * (B.d 2 0 * m.f₀ x + B.d 2 1 * m.f₁ x)

/-! ### The velocity basis stays orthogonal to `Φ` -/

variable {B}

/-- The QR factorization (3.20) produces a basis orthogonal to `Φ` (auxiliary for Theorem 3.2 of
arXiv 2311.09425). -/
theorem IsVQR.perp {L V' : ι → Lp ℝ 2 μ} {S' : Matrix ι ι ℝ} (h : B.IsVQR L V' S') (j : ι) :
    V' j ∈ B.Φperp := by
  have key : ∀ k : Fin 3, ⟪B.wpΦ k, V' j⟫ = 0 := fun k => by
    simpa using h.orthonormal.2 (Sum.inl_ne_inr (a := k) (b := j))
  exact ⟨key 0, key 1, key 2⟩

/-- The QR factorization with `w p` prepended commits no error on `Φ^⊥`: the blocks of `R` that
couple `Φ` and `L` vanish (the role of (3.20) and Proposition 3.1 of arXiv 2311.09425). -/
theorem IsVQR.eq_lInit {L V' : ι → Lp ℝ 2 μ} {S' : Matrix ι ι ℝ} (h : B.IsVQR L V' S')
    (hL : ∀ i, L i ∈ B.Φperp) (i : ι) : L i = lInit S' V' i := by
  obtain ⟨R, hR, hS⟩ := h.factor
  have hi := hR (Sum.inr i)
  simp only [Sum.elim_inr, Fintype.sum_sum_type, Sum.elim_inl] at hi
  have h0 : ∀ a : Fin 3, R (Sum.inl a) (Sum.inr i) = 0 := fun a => by
    have e : ⟪B.wpΦ a, L i⟫ = 0 := by
      have := hL i
      fin_cases a
      · exact this.1
      · exact this.2.1
      · exact this.2.2
    rw [hi, inner_add_right, inner_sum, inner_sum] at e
    simp only [inner_smul_right] at e
    have e1 : ∀ b : Fin 3, ⟪B.wpΦ a, B.wpΦ b⟫ = if a = b then 1 else 0 := fun b => by
      simp only [wpΦ, B.inner_wp_wp, Fin.castSucc_inj]
    have e2 : ∀ j : ι, ⟪B.wpΦ a, V' j⟫ = 0 := fun j => by
      simpa using h.orthonormal.2 (Sum.inl_ne_inr (a := a) (b := j))
    simpa [e1, e2] using e
  rw [hi]
  simp only [h0, zero_smul, Finset.sum_const_zero, zero_add, lInit, hS]

/-- The L right-hand side lies in `Φ^⊥`. -/
theorem lField_mem [MeasurableSpace 𝕏] (ν : Measure 𝕏) {G : (𝕏 → Lp ℝ 2 μ) → 𝕏 → Lp ℝ 2 μ}
    (hG : ∀ g x, G g x ∈ B.Φperp) (X : ι → 𝕏 → ℝ) (L : ι → Lp ℝ 2 μ) (i : ι) :
    lField ν G X L i ∈ B.Φperp := by
  have key : ∀ k : Fin 4, (∀ h ∈ B.Φperp, ⟪B.wp k, h⟫ = 0) →
      ⟪B.wp k, lField ν G X L i⟫ = 0 := by
    intro k hk
    simp only [lField]
    by_cases hint : Integrable (fun x => X i x • G (fun y => ∑ k, X k y • L k) x) ν
    · rw [← integral_inner hint]
      simp [inner_smul_right, hk _ (hG _ _)]
    · rw [integral_undef hint, inner_zero_right]
  exact ⟨key 0 fun h hh => hh.1, key 1 fun h hh => hh.2.1, key 2 fun h hh => hh.2.2⟩

/-- The L initial value lies in `Φ^⊥` (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem lInit_mem {S : Matrix ι ι ℝ} {V : ι → Lp ℝ 2 μ} (hV : ∀ j, V j ∈ B.Φperp) (i : ι) :
    lInit S V i ∈ B.Φperp :=
  B.Φperp.sum_mem fun j _ => B.Φperp.smul_mem _ (hV j)

/-- Steps 5 and 6 of the scheme stay in `Φ^⊥`, so that their QR factorizations commit no error:
`lInit Sm Vm` is exactly the output of the SSPRK2 step of Step 5, and `lInit Sc V₁` that of
Step 6. -/
theorem IsMicroStep.exact [DecidableEq ι] [MeasurableSpace 𝕏] {ν : Measure 𝕏}
    {G : (𝕏 → Lp ℝ 2 μ) → 𝕏 → Lp ℝ 2 μ} {τ : ℝ} {X₀ Xm X₁ : ι → 𝕏 → ℝ}
    {S₀ Sa Sb Sm Sc Sd S₁ : Matrix ι ι ℝ} {V₀ Vm V₁ : ι → Lp ℝ 2 μ}
    (h : B.IsMicroStep ν G τ X₀ Xm X₁ S₀ Sa Sb Sm Sc Sd S₁ V₀ Vm V₁)
    (hG : ∀ g x, G g x ∈ B.Φperp) (hV₀ : ∀ j, V₀ j ∈ B.Φperp) :
    ssprk2 (lField ν G Xm) τ (lInit Sb V₀) = lInit Sm Vm ∧
      ssprk2 (lField ν G Xm) τ (lInit Sm Vm) = lInit Sc V₁ := by
  have hF := lField_mem (B := B) ν hG Xm
  exact ⟨funext (h.step5.eq_lInit (ssprk2_mem B.Φperp hF (lInit_mem hV₀) τ)),
    funext (h.step6.eq_lInit (ssprk2_mem B.Φperp hF (lInit_mem h.step5.perp) τ))⟩

/-! ### The moments of the distribution function -/

variable (B)

/-- `1` in terms of `w p₀` (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem emb_one : B.emb 1 = B.c 0 0 • B.wp 0 := by
  conv_lhs => rw [B.one_eq, B.emb_C_mul]
  rfl

/-- `v` in terms of `w p₀, w p₁` (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem emb_X : B.emb X = B.c 1 0 • B.wp 0 + B.c 1 1 • B.wp 1 := by
  conv_lhs => rw [B.X_eq, B.emb_add, B.emb_C_mul, B.emb_C_mul]
  rfl

/-- `v²/2` in terms of `w p₀, w p₁, w p₂` (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem emb_half_sq : B.emb (C (1 / 2) * X ^ 2) =
    B.c 2 0 • B.wp 0 + B.c 2 1 • B.wp 1 + B.c 2 2 • B.wp 2 := by
  rw [B.half_sq_eq, B.emb_add, B.emb_add, B.emb_C_mul, B.emb_C_mul, B.emb_C_mul]
  rfl

/-- `v³/2` in terms of `w p₀, …, w p₃` (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem emb_half_cube : B.emb (C (1 / 2) * X ^ 3) =
    (B.c 2 0 * B.b 0 + B.c 2 1 * B.a 0) • B.wp 0
    + (B.c 2 0 * B.a 0 + B.c 2 1 * B.b 1 + B.c 2 2 * B.a 1) • B.wp 1
    + (B.c 2 1 * B.a 1 + B.c 2 2 * B.b 2) • B.wp 2
    + (B.c 2 2 * B.a 2) • B.wp 3 := by
  rw [B.half_cube_eq, B.emb_add, B.emb_add, B.emb_add, B.emb_C_mul, B.emb_C_mul, B.emb_C_mul,
    B.emb_C_mul]
  rfl

/-- `ρ` as an inner product (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem charge_eq_inner (s : State μ 𝕏 ι) (x : 𝕏) : B.charge s x = ⟪B.emb 1, B.dist s x⟫ := by
  rw [B.inner_emb, charge]
  simp

/-- `J` as an inner product (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem current_eq_inner (s : State μ 𝕏 ι) (x : 𝕏) : B.current s x = ⟪B.emb X, B.dist s x⟫ := by
  rw [B.inner_emb, current]
  simp

/-- `κ` as an inner product (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem kinetic_eq_inner (s : State μ 𝕏 ι) (x : 𝕏) :
    B.kinetic s x = ⟪B.emb (C (1 / 2) * X ^ 2), B.dist s x⟫ := by
  rw [B.inner_emb, kinetic]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  ring

/-- The energy flux as an inner product (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem heatFlux_eq_inner (s : State μ 𝕏 ι) (x : 𝕏) :
    B.heatFlux s x = ⟪B.emb (C (1 / 2) * X ^ 3), B.dist s x⟫ := by
  rw [B.inner_emb, heatFlux]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  ring

variable {B}

section Moments

variable {s : State μ 𝕏 ι} (hV : ∀ j, s.V j ∈ B.Φperp) (x : 𝕏)

include hV

/-- The moment `⟨p₀ f⟩_v` is `f₀` (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem moment₀ : ⟪B.wp 0, B.dist s x⟫ = s.f₀ x := by
  simp only [dist, macroPart, inner_add_right, inner_smul_right, B.inner_wp_wp, inner_lowRank,
    (hV _).1]
  simp

/-- The moment `⟨p₁ f⟩_v` is `f₁` (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem moment₁ : ⟪B.wp 1, B.dist s x⟫ = s.f₁ x := by
  simp only [dist, macroPart, inner_add_right, inner_smul_right, B.inner_wp_wp, inner_lowRank,
    (hV _).2.1]
  simp

/-- The moment `⟨p₂ f⟩_v` is `f₂` (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem moment₂ : ⟪B.wp 2, B.dist s x⟫ = s.f₂ x := by
  simp only [dist, macroPart, inner_add_right, inner_smul_right, B.inner_wp_wp, inner_lowRank,
    (hV _).2.2]
  simp

omit hV in
/-- The moment `⟨p₃ f⟩_v` is the closure `f₃` (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem moment₃ : ⟪B.wp 3, B.dist s x⟫ = B.f₃ s x := by
  have e : ∀ h, B.mom (B.p 3) h = ⟪B.wp 3, h⟫ := fun h => B.mom_eq _ _
  simp only [dist, macroPart, inner_add_right, inner_smul_right, B.inner_wp_wp, inner_lowRank, f₃,
    e]
  simp

/-- `ρ = c₀₀ f₀`: the micro part carries no charge. -/
theorem charge_eq : B.charge s x = B.c 0 0 * s.f₀ x := by
  rw [B.charge_eq_inner, B.emb_one, real_inner_smul_left, moment₀ hV]

/-- `J = c₁₀ f₀ + c₁₁ f₁`: the micro part carries no current. -/
theorem current_eq : B.current s x = B.c 1 0 * s.f₀ x + B.c 1 1 * s.f₁ x := by
  rw [B.current_eq_inner, B.emb_X, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    moment₀ hV, moment₁ hV]

/-- `κ = c₂₀ f₀ + c₂₁ f₁ + c₂₂ f₂`: the micro part carries no kinetic energy. -/
theorem kinetic_eq :
    B.kinetic s x = B.c 2 0 * s.f₀ x + B.c 2 1 * s.f₁ x + B.c 2 2 * s.f₂ x := by
  rw [B.kinetic_eq_inner, B.emb_half_sq, inner_add_left, inner_add_left, real_inner_smul_left,
    real_inner_smul_left, real_inner_smul_left, moment₀ hV, moment₁ hV, moment₂ hV]

/-- The energy flux in terms of `f₀, f₁, f₂, f₃`. -/
theorem heatFlux_eq : B.heatFlux s x = (B.c 2 0 * B.b 0 + B.c 2 1 * B.a 0) * s.f₀ x
    + (B.c 2 0 * B.a 0 + B.c 2 1 * B.b 1 + B.c 2 2 * B.a 1) * s.f₁ x
    + (B.c 2 1 * B.a 1 + B.c 2 2 * B.b 2) * s.f₂ x + (B.c 2 2 * B.a 2) * B.f₃ s x := by
  rw [B.heatFlux_eq_inner, B.emb_half_cube, inner_add_left, inner_add_left, inner_add_left,
    real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
    moment₀ hV, moment₁ hV, moment₂ hV, moment₃]

/-- The first flux component is minus the current, up to the factor `c₀₀`. -/
theorem flux_charge : B.c 0 0 * B.flux s 0 x = -B.current s x := by
  rw [current_eq hV, B.c_one_zero, B.c_one_one]
  change B.c 0 0 * (-B.b 0 * s.f₀ x - B.a 0 * s.f₁ x) = _
  ring

/-- The flux combination in the energy balance is minus the energy flux. -/
theorem flux_energy : B.c 2 0 * B.flux s 0 x + B.c 2 1 * B.flux s 1 x + B.c 2 2 * B.flux s 2 x =
    -B.heatFlux s x := by
  rw [heatFlux_eq hV]
  change B.c 2 0 * (-B.b 0 * s.f₀ x - B.a 0 * s.f₁ x)
    + B.c 2 1 * (-B.a 1 * s.f₂ x - B.b 1 * s.f₁ x - B.a 0 * s.f₀ x)
    + B.c 2 2 * (-B.a 2 * B.f₃ s x - B.b 2 * s.f₂ x - B.a 1 * s.f₁ x) = _
  ring

end Moments

/-! ### The balance laws of one step -/

section Balance

variable [DecidableEq ι] [MeasurableSpace 𝕏] {ν : Measure 𝕏}
  {D : (𝕏 → ℝ) → (𝕏 → Lp ℝ 2 μ) → (𝕏 → Lp ℝ 2 μ) → 𝕏 → Lp ℝ 2 μ}
  {Dₓ : (Fin 3 → 𝕏 → ℝ) → Fin 3 → 𝕏 → ℝ} {Δt : ℝ} {s m s' : State μ 𝕏 ι}

/-- The midpoint basis is orthogonal to `Φ`. -/
theorem IsSecondOrderStep.perp_mid (h : B.IsSecondOrderStep ν D Dₓ Δt s m s') (j : ι) :
    m.V j ∈ B.Φperp := by
  obtain ⟨_, _, _, _, hm⟩ := h.micro
  exact hm.step5.perp j

/-- The new basis is orthogonal to `Φ`. -/
theorem IsSecondOrderStep.perp_next (h : B.IsSecondOrderStep ν D Dₓ Δt s m s') (j : ι) :
    s'.V j ∈ B.Φperp := by
  obtain ⟨_, _, _, _, hm⟩ := h.micro
  exact hm.step6.perp j

/-- Charge balance of one step, for any spatial operator `Dₓ`. -/
theorem IsSecondOrderStep.charge_balance (h : B.IsSecondOrderStep ν D Dₓ Δt s m s')
    (hV : ∀ j, s.V j ∈ B.Φperp) (x : 𝕏) :
    (B.charge s' x - B.charge s x) / Δt = B.c 0 0 * Dₓ (B.flux m) 0 x := by
  rw [charge_eq h.perp_next, charge_eq hV, ← h.full₀ x]
  ring

/-- Total energy balance of one step, for any spatial operator `Dₓ`. -/
theorem IsSecondOrderStep.energy_balance (h : B.IsSecondOrderStep ν D Dₓ Δt s m s')
    (hV : ∀ j, s.V j ∈ B.Φperp) (hΔt : Δt ≠ 0) (x : 𝕏) :
    (B.energy s' x - B.energy s x) / Δt = B.c 2 0 * Dₓ (B.flux m) 0 x
      + B.c 2 1 * Dₓ (B.flux m) 1 x + B.c 2 2 * Dₓ (B.flux m) 2 x := by
  have e0 := h.full₀ x
  have e1 := h.full₁ x
  have e2 := h.full₂ x
  have ea := h.ampere x
  have em := h.midE x
  have h10 := B.c_one_zero'
  have h11 := B.c_one_one'
  rw [div_eq_iff hΔt] at e0 e1 e2 ea ⊢
  simp only [energy, kinetic_eq hV, kinetic_eq h.perp_next]
  linear_combination B.c 2 0 * e0 + B.c 2 1 * e1 + B.c 2 2 * e2 + m.E x * ea
    - (s'.E x - s.E x) * em - Δt * m.E x * m.f₀ x * h10 - Δt * m.E x * m.f₁ x * h11

end Balance

end MomentBasis

end Scheme

/-! ### Theorem 3.2: continuous in `x` -/

section Continuous

open MomentBasis

variable {μ : Measure ℝ} {ι : Type*} [Fintype ι]

/-- The spatial operator of the semi-discrete scheme: `∂ₓ` on each component. -/
noncomputable def derivₓ (F : Fin 3 → ℝ → ℝ) : Fin 3 → ℝ → ℝ := fun k => deriv (F k)

/-- Differentiability at `x` of the moments of a midpoint state. -/
structure MomentBasis.IsRegularAt (B : MomentBasis μ) (s : State μ ℝ ι) (x : ℝ) : Prop where
  f₀ : DifferentiableAt ℝ s.f₀ x
  f₁ : DifferentiableAt ℝ s.f₁ x
  f₂ : DifferentiableAt ℝ s.f₂ x
  f₃ : DifferentiableAt ℝ (B.f₃ s) x

variable {B : MomentBasis μ}

/-- The flux components are differentiable at a regular point (auxiliary for Theorem 3.2 of arXiv
2311.09425). -/
theorem MomentBasis.IsRegularAt.hasDerivAt {s : State μ ℝ ι} {x : ℝ} (h : B.IsRegularAt s x)
    (k : Fin 3) : HasDerivAt (B.flux s k) (deriv (B.flux s k) x) x := by
  refine DifferentiableAt.hasDerivAt ?_
  fin_cases k
  · exact ((h.f₀.const_mul _).sub (h.f₁.const_mul _))
  · exact (((h.f₂.const_mul _).sub (h.f₁.const_mul _)).sub (h.f₀.const_mul _))
  · exact (((h.f₃.const_mul _).sub (h.f₂.const_mul _)).sub (h.f₁.const_mul _))

/-- `∂ₓ J` in terms of the flux vector (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem deriv_current {s : State μ ℝ ι} (hV : ∀ j, s.V j ∈ B.Φperp) {x : ℝ}
    (h : B.IsRegularAt s x) : deriv (B.current s) x = -(B.c 0 0 * deriv (B.flux s 0) x) := by
  have e : B.current s = fun y => -(B.c 0 0 * B.flux s 0 y) := by
    funext y; rw [flux_charge hV, neg_neg]
  rw [e]
  exact ((h.hasDerivAt 0).const_mul _).neg.deriv

/-- `∂ₓ` of the energy flux in terms of the flux vector (auxiliary for Theorem 3.2 of arXiv
2311.09425). -/
theorem deriv_heatFlux {s : State μ ℝ ι} (hV : ∀ j, s.V j ∈ B.Φperp) {x : ℝ}
    (h : B.IsRegularAt s x) : deriv (B.heatFlux s) x =
      -(B.c 2 0 * deriv (B.flux s 0) x + B.c 2 1 * deriv (B.flux s 1) x
        + B.c 2 2 * deriv (B.flux s 2) x) := by
  have e : B.heatFlux s = fun y => -(B.c 2 0 * B.flux s 0 y + B.c 2 1 * B.flux s 1 y
      + B.c 2 2 * B.flux s 2 y) := by
    funext y; rw [flux_energy hV, neg_neg]
  rw [e]
  exact (((h.hasDerivAt 0).const_mul _).add ((h.hasDerivAt 1).const_mul _)).add
    ((h.hasDerivAt 2).const_mul _) |>.neg.deriv

variable [DecidableEq ι] {ν : Measure ℝ}
  {D : (ℝ → ℝ) → (ℝ → Lp ℝ 2 μ) → (ℝ → Lp ℝ 2 μ) → ℝ → Lp ℝ 2 μ} {Δt : ℝ}
  {s m : ℕ → State μ ℝ ι}

/-- Along a run of the scheme all integer-level velocity bases are orthogonal to `Φ`. -/
theorem perp_run {Dₓ : (Fin 3 → ℝ → ℝ) → Fin 3 → ℝ → ℝ}
    (h0 : ∀ j, (s 0).V j ∈ B.Φperp)
    (hstep : ∀ n, B.IsSecondOrderStep ν D Dₓ Δt (s n) (m n) (s (n + 1))) (n : ℕ) (j : ι) :
    (s n).V j ∈ B.Φperp := by
  cases n with
  | zero => exact h0 j
  | succ n => exact (hstep n).perp_next j

/-- **Theorem 3.2** of arXiv 2311.09425: local conservation of charge and total energy of the
second-order integrator, on a run of `IsSecondOrderStep` with the exact `∂ₓ`, starting from a
velocity basis orthogonal to `Φ`:
`(ρⁿ⁺¹ - ρⁿ) / Δt + ∂ₓ J^{n+1/2} = 0`, `(eⁿ⁺¹ - eⁿ) / Δt + ∂ₓ ⟨v³/2, f^{n+1/2}⟩_v = 0`.

The densities are the actual velocity integrals of `f = N + g`.  That the micro part does not
contribute is derived, not assumed.  The rate of the scheme is not claimed.  Differentiability of
the midpoint moments at `x` is assumed, as `∂ₓ` occurs in the scheme; the paper leaves this
implicit. -/
theorem theorem_3_2 (hΔt : Δt ≠ 0) (h0 : ∀ j, (s 0).V j ∈ B.Φperp)
    (hstep : ∀ n, B.IsSecondOrderStep ν D derivₓ Δt (s n) (m n) (s (n + 1))) (n : ℕ) (x : ℝ)
    (hreg : B.IsRegularAt (m n) x) :
    (B.charge (s (n + 1)) x - B.charge (s n) x) / Δt + deriv (B.current (m n)) x = 0 ∧
      (B.energy (s (n + 1)) x - B.energy (s n) x) / Δt + deriv (B.heatFlux (m n)) x = 0 := by
  have hV := perp_run h0 hstep n
  constructor
  · rw [(hstep n).charge_balance hV, deriv_current (hstep n).perp_mid hreg]
    simp [derivₓ]
  · rw [(hstep n).energy_balance hV hΔt, deriv_heatFlux (hstep n).perp_mid hreg]
    simp [derivₓ]

/-- Integration of a balance law over a period. -/
theorem integral_step {ρ ρ' J : ℝ → ℝ} {L Δt : ℝ} (hΔt : Δt ≠ 0)
    (h : ∀ x, (ρ' x - ρ x) / Δt + deriv J x = 0) (hJ : ContDiff ℝ 1 J)
    (hP : Function.Periodic J L) (hI : IntervalIntegrable ρ volume 0 L) :
    IntervalIntegrable ρ' volume 0 L ∧ ∫ x in (0 : ℝ)..L, ρ' x = ∫ x in (0 : ℝ)..L, ρ x := by
  have hd : Continuous (deriv J) := hJ.continuous_deriv le_rfl
  have hdi : IntervalIntegrable (deriv J) volume 0 L := hd.intervalIntegrable _ _
  have e : ρ' = fun x => ρ x - Δt * deriv J x := by
    funext x
    have := h x
    field_simp at this
    linarith
  rw [e]
  refine ⟨hI.sub (hdi.const_mul Δt), ?_⟩
  rw [intervalIntegral.integral_sub hI (hdi.const_mul Δt), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_deriv_eq_sub
      (fun x _ => hJ.differentiable (by norm_num) x) hdi]
  have := hP 0
  simp only [zero_add] at this
  rw [this]
  simp

/-- `C¹` regularity and `L`-periodicity of the moments of a midpoint state. -/
structure MomentBasis.IsPeriodicC1 (B : MomentBasis μ) (s : State μ ℝ ι) (L : ℝ) : Prop where
  f₀ : ContDiff ℝ 1 s.f₀
  f₁ : ContDiff ℝ 1 s.f₁
  f₂ : ContDiff ℝ 1 s.f₂
  f₃ : ContDiff ℝ 1 (B.f₃ s)
  per₀ : Function.Periodic s.f₀ L
  per₁ : Function.Periodic s.f₁ L
  per₂ : Function.Periodic s.f₂ L
  per₃ : Function.Periodic (B.f₃ s) L

omit [DecidableEq ι] in
/-- `C¹` moments are differentiable (auxiliary for Theorem 3.2 of arXiv 2311.09425). -/
theorem MomentBasis.IsPeriodicC1.isRegularAt {s : State μ ℝ ι} {L : ℝ} (h : B.IsPeriodicC1 s L)
    (x : ℝ) : B.IsRegularAt s x :=
  ⟨h.f₀.differentiable (by norm_num) x, h.f₁.differentiable (by norm_num) x,
    h.f₂.differentiable (by norm_num) x, h.f₃.differentiable (by norm_num) x⟩

omit [DecidableEq ι] in
/-- The current inherits regularity and periodicity from the moments (auxiliary for Theorem 3.2 of
arXiv 2311.09425). -/
theorem MomentBasis.IsPeriodicC1.current {s : State μ ℝ ι} {L : ℝ} (h : B.IsPeriodicC1 s L)
    (hV : ∀ j, s.V j ∈ B.Φperp) :
    ContDiff ℝ 1 (B.current s) ∧ Function.Periodic (B.current s) L := by
  have e : B.current s = fun y => B.c 1 0 * s.f₀ y + B.c 1 1 * s.f₁ y := funext (current_eq hV)
  rw [e]
  refine ⟨(contDiff_const.mul h.f₀).add (contDiff_const.mul h.f₁), fun x => ?_⟩
  simp only [h.per₀ x, h.per₁ x]

omit [DecidableEq ι] in
/-- The energy flux inherits regularity and periodicity from the moments (auxiliary for Theorem 3.2
of arXiv 2311.09425). -/
theorem MomentBasis.IsPeriodicC1.heatFlux {s : State μ ℝ ι} {L : ℝ} (h : B.IsPeriodicC1 s L)
    (hV : ∀ j, s.V j ∈ B.Φperp) :
    ContDiff ℝ 1 (B.heatFlux s) ∧ Function.Periodic (B.heatFlux s) L := by
  have e := funext (heatFlux_eq hV)
  rw [e]
  refine ⟨((((contDiff_const.mul h.f₀).add (contDiff_const.mul h.f₁)).add
    (contDiff_const.mul h.f₂)).add (contDiff_const.mul h.f₃)), fun x => ?_⟩
  simp only [h.per₀ x, h.per₁ x, h.per₂ x, h.per₃ x]

/-- **Theorem 3.2, total form** (arXiv 2311.09425): on an `L`-periodic domain with `C¹` midpoint
moments the integrals of the charge and of the total energy over a period are constant along a run
of the scheme.  The paper states the local laws (`theorem_3_2`); this is their integral over a
period. -/
theorem theorem_3_2_total {L : ℝ} (hΔt : Δt ≠ 0) (h0 : ∀ j, (s 0).V j ∈ B.Φperp)
    (hstep : ∀ n, B.IsSecondOrderStep ν D derivₓ Δt (s n) (m n) (s (n + 1)))
    (hreg : ∀ n, B.IsPeriodicC1 (m n) L)
    (hρ : IntervalIntegrable (B.charge (s 0)) volume 0 L)
    (he : IntervalIntegrable (B.energy (s 0)) volume 0 L) (n : ℕ) :
    ∫ x in (0 : ℝ)..L, B.charge (s n) x = ∫ x in (0 : ℝ)..L, B.charge (s 0) x ∧
      ∫ x in (0 : ℝ)..L, B.energy (s n) x = ∫ x in (0 : ℝ)..L, B.energy (s 0) x := by
  suffices h : (IntervalIntegrable (B.charge (s n)) volume 0 L ∧
      ∫ x in (0 : ℝ)..L, B.charge (s n) x = ∫ x in (0 : ℝ)..L, B.charge (s 0) x) ∧
      (IntervalIntegrable (B.energy (s n)) volume 0 L ∧
      ∫ x in (0 : ℝ)..L, B.energy (s n) x = ∫ x in (0 : ℝ)..L, B.energy (s 0) x) from
    ⟨h.1.2, h.2.2⟩
  induction n with
  | zero => exact ⟨⟨hρ, rfl⟩, ⟨he, rfl⟩⟩
  | succ n ih =>
    have hm := (hstep n).perp_mid
    have hlaw := fun x => theorem_3_2 hΔt h0 hstep n x ((hreg n).isRegularAt x)
    have h1 := integral_step hΔt (fun x => (hlaw x).1) ((hreg n).current hm).1
      ((hreg n).current hm).2 ih.1.1
    have h2 := integral_step hΔt (fun x => (hlaw x).2) ((hreg n).heatFlux hm).1
      ((hreg n).heatFlux hm).2 ih.2.1
    exact ⟨⟨h1.1, h1.2.trans ih.1.2⟩, ⟨h2.1, h2.2.trans ih.2.2⟩⟩

end Continuous

/-! ### Corollary 3.3: a conservative spatial discretization -/

section Discrete

open MomentBasis

variable {μ : Measure ℝ} {ι : Type*} [Fintype ι] {N : ℕ} [NeZero N]

/-- A conservative spatial discretization on the periodic grid `ZMod N`: the `k`-th component of
`∂ₓ F` at cell `i` is `(F̂ₖ,ᵢ₊₁/₂ - F̂ₖ,ᵢ₋₁/₂) / Δx`, with `F̂ₖ,ᵢ₊₁/₂ = Fhat F k i`.  The numerical
flux `Fhat` is an arbitrary map, so nonlinear limiters and flux splitting are allowed. -/
noncomputable def fluxDiff (Fhat : (Fin 3 → ZMod N → ℝ) → Fin 3 → ZMod N → ℝ) (Δx : ℝ) :
    (Fin 3 → ZMod N → ℝ) → Fin 3 → ZMod N → ℝ :=
  fun F k i => (Fhat F k i - Fhat F k (i - 1)) / Δx

/-- The numerical charge flux induced by a numerical flux vector. -/
noncomputable def MomentBasis.chargeFlux (B : MomentBasis μ) (Ĝ : Fin 3 → ZMod N → ℝ) (i : ZMod N) :
    ℝ := -(B.c 0 0 * Ĝ 0 i)

/-- The numerical energy flux induced by a numerical flux vector. -/
noncomputable def MomentBasis.energyFlux (B : MomentBasis μ) (Ĝ : Fin 3 → ZMod N → ℝ) (i : ZMod N) :
    ℝ := -(B.c 2 0 * Ĝ 0 i + B.c 2 1 * Ĝ 1 i + B.c 2 2 * Ĝ 2 i)

/-- Telescoping on the periodic grid (auxiliary for Corollary 3.3 of arXiv 2311.09425). -/
theorem sum_sub_shift (Y : ZMod N → ℝ) (Δx : ℝ) : ∑ i, (Y i - Y (i - 1)) / Δx = 0 := by
  have h : ∑ i, Y (i - 1) = ∑ i, Y i := Equiv.sum_comp (Equiv.subRight (1 : ZMod N)) Y
  rw [← Finset.sum_div, Finset.sum_sub_distrib, h, sub_self, zero_div]

/-- A discrete balance law in flux form conserves the sum over the periodic grid (auxiliary for
Corollary 3.3 of arXiv 2311.09425). -/
theorem sum_eq_of_balance {ρ ρ' Y : ZMod N → ℝ} {Δt Δx : ℝ} (hΔt : Δt ≠ 0)
    (h : ∀ i, (ρ' i - ρ i) / Δt + (Y i - Y (i - 1)) / Δx = 0) : ∑ i, ρ' i = ∑ i, ρ i := by
  have h1 : ∑ i, (ρ' i - ρ i) / Δt = 0 := by
    have := Finset.sum_congr (rfl : (Finset.univ : Finset (ZMod N)) = _) fun i _ =>
      eq_neg_of_add_eq_zero_left (h i)
    rw [this, Finset.sum_neg_distrib, sum_sub_shift, neg_zero]
  rw [← Finset.sum_div, div_eq_zero_iff, or_iff_left hΔt, Finset.sum_sub_distrib] at h1
  linarith

variable [DecidableEq ι] [MeasurableSpace (ZMod N)] {B : MomentBasis μ} {ν : Measure (ZMod N)}
  {D : (ZMod N → ℝ) → (ZMod N → Lp ℝ 2 μ) → (ZMod N → Lp ℝ 2 μ) → ZMod N → Lp ℝ 2 μ} {Δt Δx : ℝ}
  {s m : ℕ → State μ (ZMod N) ι}

/-- **Corollary 3.3** of arXiv 2311.09425: for a conservative discretization of `∂ₓ` in
(3.29)-(3.31) and (3.33)-(3.35), with numerical fluxes that may be nonlinear and may change from
step to step, the scheme satisfies exact local discrete balance laws for the charge and the total
energy in flux form, and the totals over the periodic grid are constant along a run. The paper does
not specify the spatial inner product of the low-rank steps; here `ν` is any measure on the grid. -/
theorem corollary_3_3 (Fhat : ℕ → (Fin 3 → ZMod N → ℝ) → Fin 3 → ZMod N → ℝ)
    (hΔt : Δt ≠ 0) (h0 : ∀ j, (s 0).V j ∈ B.Φperp)
    (hstep : ∀ n, B.IsSecondOrderStep ν D (fluxDiff (Fhat n) Δx) Δt (s n) (m n) (s (n + 1)))
    (n : ℕ) :
    (∀ i, (B.charge (s (n + 1)) i - B.charge (s n) i) / Δt
        + (B.chargeFlux (Fhat n (B.flux (m n))) i - B.chargeFlux (Fhat n (B.flux (m n))) (i - 1))
          / Δx = 0) ∧
      (∀ i, (B.energy (s (n + 1)) i - B.energy (s n) i) / Δt
        + (B.energyFlux (Fhat n (B.flux (m n))) i - B.energyFlux (Fhat n (B.flux (m n))) (i - 1))
          / Δx = 0) ∧
      ∑ i, B.charge (s n) i = ∑ i, B.charge (s 0) i ∧
      ∑ i, B.energy (s n) i = ∑ i, B.energy (s 0) i := by
  have hV : ∀ n j, (s n).V j ∈ B.Φperp := fun n j => by
    cases n with
    | zero => exact h0 j
    | succ n => exact (hstep n).perp_next j
  have law₁ : ∀ n i, (B.charge (s (n + 1)) i - B.charge (s n) i) / Δt
      + (B.chargeFlux (Fhat n (B.flux (m n))) i - B.chargeFlux (Fhat n (B.flux (m n))) (i - 1))
        / Δx = 0 := fun n i => by
    rw [(hstep n).charge_balance (hV n)]
    simp only [fluxDiff, chargeFlux]
    ring
  have law₂ : ∀ n i, (B.energy (s (n + 1)) i - B.energy (s n) i) / Δt
      + (B.energyFlux (Fhat n (B.flux (m n))) i - B.energyFlux (Fhat n (B.flux (m n))) (i - 1))
        / Δx = 0 := fun n i => by
    rw [(hstep n).energy_balance (hV n) hΔt]
    simp only [fluxDiff, energyFlux]
    ring
  refine ⟨law₁ n, law₂ n, ?_, ?_⟩
  · induction n with
    | zero => rfl
    | succ n ih => rw [sum_eq_of_balance hΔt (law₁ n), ih]
  · induction n with
    | zero => rfl
    | succ n ih => rw [sum_eq_of_balance hΔt (law₂ n), ih]

/-- **Corollary 3.3, linear numerical fluxes** (arXiv 2311.09425): if the numerical flux is one
linear map `A` applied to each component, the discrete balance laws have the form of Theorem 3.2
with `∂ₓ` replaced by `δₓ u i = ((A u) i - (A u) (i - 1)) / Δx`:
`(ρⁿ⁺¹ - ρⁿ) / Δt + δₓ J^{n+1/2} = 0` and `(eⁿ⁺¹ - eⁿ) / Δt + δₓ ⟨v³/2, f^{n+1/2}⟩_v = 0`. -/
theorem corollary_3_3_linear (A : (ZMod N → ℝ) →ₗ[ℝ] (ZMod N → ℝ))
    (hΔt : Δt ≠ 0) (h0 : ∀ j, (s 0).V j ∈ B.Φperp)
    (hstep : ∀ n, B.IsSecondOrderStep ν D (fluxDiff (fun F k => A (F k)) Δx) Δt (s n) (m n)
      (s (n + 1))) (n : ℕ) (i : ZMod N) :
    (B.charge (s (n + 1)) i - B.charge (s n) i) / Δt
        + (A (B.current (m n)) i - A (B.current (m n)) (i - 1)) / Δx = 0 ∧
      (B.energy (s (n + 1)) i - B.energy (s n) i) / Δt
        + (A (B.heatFlux (m n)) i - A (B.heatFlux (m n)) (i - 1)) / Δx = 0 := by
  obtain ⟨h₁, h₂, -, -⟩ := corollary_3_3 (fun _ F k => A (F k)) hΔt h0 hstep n
  have hm := (hstep n).perp_mid
  have e₁ : B.chargeFlux (fun k => A (B.flux (m n) k)) = A (B.current (m n)) := by
    have : B.current (m n) = -(B.c 0 0 • B.flux (m n) 0) := by
      funext y
      simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
      rw [flux_charge hm, neg_neg]
    rw [this, map_neg, map_smul]
    funext y
    simp [chargeFlux]
  have e₂ : B.energyFlux (fun k => A (B.flux (m n) k)) = A (B.heatFlux (m n)) := by
    have : B.heatFlux (m n) = -(B.c 2 0 • B.flux (m n) 0 + B.c 2 1 • B.flux (m n) 1
        + B.c 2 2 • B.flux (m n) 2) := by
      funext y
      simp only [Pi.neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [flux_energy hm, neg_neg]
    rw [this, map_neg, map_add, map_add, map_smul, map_smul, map_smul]
    funext y
    simp [energyFlux]
  have h₁' := h₁ i
  have h₂' := h₂ i
  rw [e₁] at h₁'
  rw [e₂] at h₂'
  exact ⟨h₁', h₂'⟩

end Discrete

/-! ### The scheme can be run -/

section Existence

open MomentBasis

variable {μ : Measure ℝ} {𝕏 ι : Type*} [Fintype ι]

/-- QR factorization in a finite-dimensional space with room for the columns (auxiliary for the
non-vacuity of Theorem 3.2 of arXiv 2311.09425). -/
theorem exists_orthonormal_factor_of_finrank {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (u : ι → F)
    (hcard : Fintype.card ι ≤ Module.finrank ℝ F) :
    ∃ (Q : ι → F) (R : Matrix ι ι ℝ), Orthonormal ℝ Q ∧ ∀ j, u j = ∑ i, R i j • Q i := by
  classical
  let U : Submodule ℝ F := Submodule.span ℝ (Set.range u)
  let b := stdOrthonormalBasis ℝ U
  let v : Fin (Module.finrank ℝ U) → F := fun i => (b i : F)
  have hv : Orthonormal ℝ v := b.orthonormal.comp_linearIsometry U.subtypeₗᵢ
  have hv' : Orthonormal ℝ ((↑) : Set.range v → F) :=
    (orthonormal_subtype_range hv.linearIndependent.injective).2 hv
  obtain ⟨t, T, hst, hT⟩ := hv'.exists_orthonormalBasis_extension
  have hd : Module.finrank ℝ U ≤ Fintype.card ι := finrank_range_le_card u
  have ht : t.card = Module.finrank ℝ F := by
    rw [Module.finrank_eq_card_basis T.toBasis, Fintype.card_coe]
  let S : Finset F := Finset.univ.image v
  have hSt : S ⊆ t := by
    intro y hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
    exact hst ⟨i, rfl⟩
  have hS : S.card ≤ Fintype.card ι :=
    Finset.card_image_le.trans (by simpa using hd)
  obtain ⟨t', hSt', ht't, ht'⟩ := Finset.exists_subsuperset_card_eq hSt hS (ht ▸ hcard)
  let e : ι ≃ t' := Fintype.equivOfCardEq (by simp [ht'])
  let f : ι → t := fun i => ⟨e i, ht't (e i).2⟩
  have hf : Function.Injective f := fun i j h =>
    e.injective (Subtype.ext (congrArg (fun y : t => (y : F)) h))
  have hO : Orthonormal ℝ ((↑) : t → F) := hT ▸ T.orthonormal
  let Q : ι → F := fun i => (e i : F)
  have hQ : Orthonormal ℝ Q := hO.comp f hf
  have hmem : ∀ j, u j ∈ Submodule.span ℝ (Set.range Q) := fun j => by
    have h1 : u j ∈ U := Submodule.subset_span ⟨j, rfl⟩
    have h2 : (u j : F) = ∑ i, ⟪(b i : U), ⟨u j, h1⟩⟫ • v i := by
      have := congrArg (Subtype.val) (b.sum_repr' ⟨u j, h1⟩)
      simpa [Submodule.coe_sum] using this.symm
    rw [h2]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    have : v i ∈ t' := hSt' (Finset.mem_image_of_mem v (Finset.mem_univ i))
    exact ⟨e.symm ⟨v i, this⟩, by simp [Q]⟩
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hmem j)
  exact ⟨Q, Matrix.of fun i j => c j i, hQ, fun j => by simpa using (hc j).symm⟩

/-- QR factorization inside a subspace `W` that contains as many orthonormal vectors as there are
columns (auxiliary for the non-vacuity of Theorem 3.2 of arXiv 2311.09425). -/
theorem exists_orthonormal_factor {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {W : Submodule ℝ E} {u e : ι → E} (hu : ∀ i, u i ∈ W) (he : Orthonormal ℝ e)
    (he' : ∀ i, e i ∈ W) :
    ∃ (Q : ι → E) (R : Matrix ι ι ℝ), Orthonormal ℝ Q ∧ (∀ i, Q i ∈ W) ∧
      ∀ j, u j = ∑ i, R i j • Q i := by
  classical
  let T : Submodule ℝ E := Submodule.span ℝ (Set.range u ∪ Set.range e)
  have : FiniteDimensional ℝ T :=
    FiniteDimensional.span_of_finite ℝ ((Set.finite_range u).union (Set.finite_range e))
  have hTW : T ≤ W := Submodule.span_le.2 (by
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact hu i
    · exact he' i)
  let e' : ι → T := fun i => ⟨e i, Submodule.subset_span (Or.inr ⟨i, rfl⟩)⟩
  have hli : LinearIndependent ℝ e' :=
    LinearIndependent.of_comp T.subtype he.linearIndependent
  obtain ⟨Q, R, hQ, hR⟩ := exists_orthonormal_factor_of_finrank
    (fun i => (⟨u i, Submodule.subset_span (Or.inl ⟨i, rfl⟩)⟩ : T)) hli.fintype_card_le_finrank
  refine ⟨fun i => Q i, R, hQ.comp_linearIsometry T.subtypeₗᵢ, fun i => hTW (Q i).2, fun j => ?_⟩
  have := congrArg Subtype.val (hR j)
  simpa [Submodule.coe_sum] using this

/-- The first three vectors are orthonormal (auxiliary for the non-vacuity of Theorem 3.2 of
arXiv 2311.09425). -/
theorem MomentBasis.orthonormal_wpΦ (B : MomentBasis μ) : Orthonormal ℝ B.wpΦ := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  simp only [wpΦ, B.inner_wp_wp, Fin.castSucc_inj]

/-- A factorization by an orthonormal family in `Φ^⊥` is a QR factorization (3.20) (auxiliary for
the non-vacuity of Theorem 3.2 of arXiv 2311.09425). -/
theorem MomentBasis.isVQR_of_factor (B : MomentBasis μ) {L Q : ι → Lp ℝ 2 μ} {R : Matrix ι ι ℝ}
    (hQ : Orthonormal ℝ Q) (hQW : ∀ i, Q i ∈ B.Φperp) (hR : ∀ j, L j = ∑ i, R i j • Q i) :
    B.IsVQR L Q Rᵀ := by
  classical
  have hw : ∀ (a : Fin 3) (j : ι), ⟪B.wpΦ a, Q j⟫ = 0 := fun a j => by
    have := hQW j
    fin_cases a
    · exact this.1
    · exact this.2.1
    · exact this.2.2
  refine ⟨?_, Matrix.fromBlocks 1 0 0 R, ?_, fun i j => by simp⟩
  · rw [orthonormal_iff_ite]
    rintro (a | i) (b | j)
    · simpa using (orthonormal_iff_ite.1 B.orthonormal_wpΦ) a b
    · simpa using hw a j
    · simpa [real_inner_comm] using hw b i
    · simpa using (orthonormal_iff_ite.1 hQ) i j
  · rintro (a | j)
    · simp [Fintype.sum_sum_type, Matrix.one_apply]
    · simpa [Fintype.sum_sum_type] using hR j

/-- The QR factorization (3.20) exists when `Φ^⊥` has room for the rank (auxiliary for the
non-vacuity of Theorem 3.2 of arXiv 2311.09425). -/
theorem MomentBasis.exists_isVQR (B : MomentBasis μ) {e : ι → Lp ℝ 2 μ} (he : Orthonormal ℝ e)
    (he' : ∀ i, e i ∈ B.Φperp) {L : ι → Lp ℝ 2 μ} (hL : ∀ i, L i ∈ B.Φperp) :
    ∃ V' S', B.IsVQR L V' S' := by
  obtain ⟨Q, R, hQ, hQW, hR⟩ := exists_orthonormal_factor hL he he'
  exact ⟨Q, _, B.isVQR_of_factor hQ hQW hR⟩

variable [DecidableEq ι]

/-- On a finite grid with the counting measure and at least as many points as the rank, the spatial
QR factorization exists (auxiliary for the non-vacuity of Corollary 3.3 of arXiv 2311.09425). -/
theorem exists_isXQR [Fintype 𝕏] [MeasurableSpace 𝕏] [MeasurableSingletonClass 𝕏]
    (hcard : Fintype.card ι ≤ Fintype.card 𝕏) (K : ι → 𝕏 → ℝ) :
    ∃ X' S', IsXQR Measure.count K X' S' := by
  classical
  obtain ⟨Q, R, hQ, hR⟩ := exists_orthonormal_factor_of_finrank (F := EuclideanSpace ℝ 𝕏)
    (fun j => WithLp.toLp 2 (K j)) (by simpa using hcard)
  refine ⟨fun i x => Q i x, R, ⟨fun i j => ?_, fun j x => ?_⟩⟩
  · have := (orthonormal_iff_ite.1 hQ) i j
    rw [PiLp.inner_apply] at this
    rw [← this, integral_count]
    simp [mul_comm]
  · have := congrArg (fun y : EuclideanSpace ℝ 𝕏 => y x) (hR j)
    simpa [mul_comm] using this

/-- **Bridge to the core frames.** On a finite grid with the counting measure, the spatial QR
factorization `IsXQR` is the factorization `K̃ = X̃ S'` of the grid matrices `K̃ x j = K j x`,
`X̃ x i = X' i x` with orthonormal columns `X̃ᵀ X̃ = 1`. (For a general measure `ν` it is the same
statement in `L²(ν)`, a different carrier.) -/
theorem isXQR_count_iff [Fintype 𝕏] [MeasurableSpace 𝕏] [MeasurableSingletonClass 𝕏]
    {K X' : ι → 𝕏 → ℝ} {S' : Matrix ι ι ℝ} :
    IsXQR Measure.count K X' S' ↔
      (Matrix.of fun x i => X' i x)ᵀ * Matrix.of (fun x i => X' i x) = 1 ∧
        Matrix.of (fun x j => K j x) = Matrix.of (fun x i => X' i x) * S' := by
  constructor
  · rintro ⟨horth, hfac⟩
    refine ⟨?_, ?_⟩
    · ext i j
      rw [Matrix.one_apply, ← horth i j, integral_count]
      simp [Matrix.mul_apply]
    · ext x j
      simp [Matrix.mul_apply, hfac j x]
  · rintro ⟨horth, hfac⟩
    refine ⟨fun i j => ?_, fun j x => ?_⟩
    · have := congrFun (congrFun horth i) j
      rw [integral_count]
      simpa [Matrix.mul_apply, Matrix.one_apply] using this
    · have := congrFun (congrFun hfac x) j
      simpa [Matrix.mul_apply] using this

/-- On a finite grid with the counting measure, the orthonormal factor of `IsXQR` is an orthonormal
frame capturing the grid matrix of `K` (the core `Matrix.IsOrthCapture`). -/
theorem IsXQR.isOrthCapture_count [Fintype 𝕏] [MeasurableSpace 𝕏] [MeasurableSingletonClass 𝕏]
    {K X' : ι → 𝕏 → ℝ} {S' : Matrix ι ι ℝ} (h : IsXQR Measure.count K X' S') :
    Matrix.IsOrthCapture (Matrix.of fun x i => X' i x) (Matrix.of fun x j => K j x) :=
  Matrix.isOrthCapture_iff.2 ⟨(isXQR_count_iff.1 h).1, S', (isXQR_count_iff.1 h).2⟩

variable [MeasurableSpace 𝕏] {ν : Measure 𝕏}

/-- One step of the second-order integrator exists for every `D`, every spatial operator and every
state whose basis is orthogonal to `Φ`, as soon as the QR factorizations exist (non-vacuity of
Theorem 3.2 and Corollary 3.3 of arXiv 2311.09425). -/
theorem MomentBasis.exists_secondOrderStep (B : MomentBasis μ)
    (D : (𝕏 → ℝ) → (𝕏 → Lp ℝ 2 μ) → (𝕏 → Lp ℝ 2 μ) → 𝕏 → Lp ℝ 2 μ)
    (Dₓ : (Fin 3 → 𝕏 → ℝ) → Fin 3 → 𝕏 → ℝ) {Δt : ℝ} (hΔt : Δt ≠ 0)
    (hx : ∀ K : ι → 𝕏 → ℝ, ∃ X' S', IsXQR ν K X' S')
    (hv : ∀ L : ι → Lp ℝ 2 μ, (∀ i, L i ∈ B.Φperp) → ∃ V' S', B.IsVQR L V' S')
    (s : State μ 𝕏 ι) (hV : ∀ j, s.V j ∈ B.Φperp) :
    ∃ m s', B.IsSecondOrderStep ν D Dₓ Δt s m s' := by
  let f₀m : 𝕏 → ℝ := fun x => s.f₀ x + Δt / 2 * Dₓ (B.flux s) 0 x
  let f₁m : 𝕏 → ℝ := fun x => s.f₁ x + Δt / 2 * (Dₓ (B.flux s) 1 x + s.E x * (B.d 1 0 * s.f₀ x))
  let f₂m : 𝕏 → ℝ := fun x => s.f₂ x +
    Δt / 2 * (Dₓ (B.flux s) 2 x + s.E x * (B.d 2 0 * s.f₀ x + B.d 2 1 * s.f₁ x))
  let E₁ : 𝕏 → ℝ := fun x => s.E x - Δt * (B.c 1 0 * f₀m x + B.c 1 1 * f₁m x)
  let Em : 𝕏 → ℝ := fun x => (E₁ x + s.E x) / 2
  let G := B.frozen D (⟨f₀m, f₁m, f₂m, Em, s.X, s.S, s.V⟩ : State μ 𝕏 ι)
  have hG : ∀ g x, G g x ∈ B.Φperp := fun g x => B.Pperp_mem _
  obtain ⟨Xm, Sa, h3⟩ := hx (ssprk2 (kField G s.V) (Δt / 2) (kInit s.X s.S))
  let Sb := ssprk2 (sField ν G Xm s.V) (Δt / 2) Sa
  have hF := lField_mem (B := B) ν hG Xm
  obtain ⟨Vm, Sm, h5⟩ := hv (ssprk2 (lField ν G Xm) (Δt / 2) (lInit Sb s.V))
    (ssprk2_mem B.Φperp hF (lInit_mem hV) _)
  obtain ⟨V₁, Sc, h6⟩ := hv (ssprk2 (lField ν G Xm) (Δt / 2) (lInit Sm Vm))
    (ssprk2_mem B.Φperp hF (lInit_mem h5.perp) _)
  let Sd := ssprk2 (sField ν G Xm V₁) (Δt / 2) Sc
  obtain ⟨X₁, S₁, h8⟩ := hx (ssprk2 (kField G V₁) (Δt / 2) (kInit Xm Sd))
  let m : State μ 𝕏 ι := ⟨f₀m, f₁m, f₂m, Em, Xm, Sm, Vm⟩
  let s' : State μ 𝕏 ι :=
    ⟨fun x => s.f₀ x + Δt * Dₓ (B.flux m) 0 x,
      fun x => s.f₁ x + Δt * (Dₓ (B.flux m) 1 x + m.E x * (B.d 1 0 * m.f₀ x)),
      fun x => s.f₂ x +
        Δt * (Dₓ (B.flux m) 2 x + m.E x * (B.d 2 0 * m.f₀ x + B.d 2 1 * m.f₁ x)),
      E₁, X₁, S₁, V₁⟩
  refine ⟨m, s', ⟨fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_, fun x => rfl,
    ⟨Sa, Sb, Sc, Sd, ⟨h3, rfl, h5, h6, rfl, h8⟩⟩, fun x => ?_, fun x => ?_, fun x => ?_⟩⟩
  · change (s.f₀ x + Δt / 2 * Dₓ (B.flux s) 0 x - s.f₀ x) / (Δt / 2) = _
    field_simp
    ring
  · change (s.f₁ x + Δt / 2 * (Dₓ (B.flux s) 1 x + s.E x * (B.d 1 0 * s.f₀ x)) - s.f₁ x)
      / (Δt / 2) = _
    field_simp
    ring
  · change (s.f₂ x + Δt / 2 * (Dₓ (B.flux s) 2 x + s.E x * (B.d 2 0 * s.f₀ x + B.d 2 1 * s.f₁ x))
      - s.f₂ x) / (Δt / 2) = _
    field_simp
    ring
  · change (s.E x - Δt * (B.c 1 0 * f₀m x + B.c 1 1 * f₁m x) - s.E x) / Δt = _
    field_simp
    ring
  · change (s.f₀ x + Δt * Dₓ (B.flux m) 0 x - s.f₀ x) / Δt = _
    field_simp
    ring
  · change (s.f₁ x + Δt * (Dₓ (B.flux m) 1 x + m.E x * (B.d 1 0 * m.f₀ x)) - s.f₁ x) / Δt = _
    field_simp
    ring
  · change (s.f₂ x + Δt * (Dₓ (B.flux m) 2 x + m.E x * (B.d 2 0 * m.f₀ x + B.d 2 1 * m.f₁ x))
      - s.f₂ x) / Δt = _
    field_simp
    ring

/-- A whole run of the second-order integrator exists from every initial state whose basis is
orthogonal to `Φ`, as soon as the QR factorizations exist (non-vacuity of Theorem 3.2 and Corollary
3.3 of arXiv 2311.09425). -/
theorem MomentBasis.exists_run (B : MomentBasis μ)
    (D : (𝕏 → ℝ) → (𝕏 → Lp ℝ 2 μ) → (𝕏 → Lp ℝ 2 μ) → 𝕏 → Lp ℝ 2 μ)
    (Dₓ : (Fin 3 → 𝕏 → ℝ) → Fin 3 → 𝕏 → ℝ) {Δt : ℝ} (hΔt : Δt ≠ 0)
    (hx : ∀ K : ι → 𝕏 → ℝ, ∃ X' S', IsXQR ν K X' S')
    (hv : ∀ L : ι → Lp ℝ 2 μ, (∀ i, L i ∈ B.Φperp) → ∃ V' S', B.IsVQR L V' S')
    (s₀ : State μ 𝕏 ι) (h₀ : ∀ j, s₀.V j ∈ B.Φperp) :
    ∃ s m : ℕ → State μ 𝕏 ι, s 0 = s₀ ∧
      ∀ n, B.IsSecondOrderStep ν D Dₓ Δt (s n) (m n) (s (n + 1)) := by
  let T := {s : State μ 𝕏 ι // ∀ j, s.V j ∈ B.Φperp}
  have h : ∀ t : T, ∃ p : State μ 𝕏 ι × State μ 𝕏 ι,
      B.IsSecondOrderStep ν D Dₓ Δt t.1 p.1 p.2 := fun t => by
    obtain ⟨m, s', h⟩ := B.exists_secondOrderStep D Dₓ hΔt hx hv t.1 t.2
    exact ⟨(m, s'), h⟩
  choose p hp using h
  let next : T → T := fun t => ⟨(p t).2, (hp t).perp_next⟩
  let u : ℕ → T := fun n => Nat.rec ⟨s₀, h₀⟩ (fun _ t => next t) n
  exact ⟨fun n => (u n).1, fun n => (p (u n)).1, rfl, fun n => hp (u n)⟩

/-- **Non-vacuity of Corollary 3.3** of arXiv 2311.09425 (any rank): on a finite grid with at least
as many points as the rank, and if `Φ^⊥` contains as many orthonormal vectors as the rank, the
scheme runs for every `D`, every spatial operator and every admissible initial state. -/
theorem MomentBasis.exists_run_grid [Fintype 𝕏] [MeasurableSingletonClass 𝕏] (B : MomentBasis μ)
    (D : (𝕏 → ℝ) → (𝕏 → Lp ℝ 2 μ) → (𝕏 → Lp ℝ 2 μ) → 𝕏 → Lp ℝ 2 μ)
    (Dₓ : (Fin 3 → 𝕏 → ℝ) → Fin 3 → 𝕏 → ℝ) {Δt : ℝ} (hΔt : Δt ≠ 0)
    (hcard : Fintype.card ι ≤ Fintype.card 𝕏) {e : ι → Lp ℝ 2 μ} (he : Orthonormal ℝ e)
    (he' : ∀ i, e i ∈ B.Φperp) (s₀ : State μ 𝕏 ι) (h₀ : ∀ j, s₀.V j ∈ B.Φperp) :
    ∃ s m : ℕ → State μ 𝕏 ι, s 0 = s₀ ∧
      ∀ n, B.IsSecondOrderStep Measure.count D Dₓ Δt (s n) (m n) (s (n + 1)) :=
  B.exists_run D Dₓ hΔt (exists_isXQR hcard) (fun _ hL => B.exists_isVQR he he' hL) s₀ h₀

end Existence

/-! ### Instances -/

section Instances

open MomentBasis

/-- A four-point velocity measure (nodes `±1`, `±4`, weights `2/5`, `1/10`) whose orthonormal
polynomials have rational coefficients (auxiliary for the non-vacuity of Theorem 3.2 of arXiv
2311.09425). -/
noncomputable def fourPoint : Measure ℝ :=
  ENNReal.ofReal (2 / 5) • (Measure.dirac 1 + Measure.dirac (-1))
    + ENNReal.ofReal (1 / 10) • (Measure.dirac 4 + Measure.dirac (-4))

/-- Polynomials are integrable for `fourPoint` (auxiliary for the non-vacuity of Theorem 3.2 of
arXiv 2311.09425). -/
theorem integrable_fourPoint (q : ℝ[X]) : Integrable (fun v => q.eval v) fourPoint := by
  have h : ∀ a : ℝ, Integrable (fun v => q.eval v) (Measure.dirac a) := fun a =>
    integrable_dirac (by simp)
  exact (((h 1).add_measure (h (-1))).smul_measure ENNReal.ofReal_ne_top).add_measure
    (((h 4).add_measure (h (-4))).smul_measure ENNReal.ofReal_ne_top)

/-- The integral for `fourPoint` (auxiliary for the non-vacuity of Theorem 3.2 of arXiv
2311.09425). -/
theorem integral_fourPoint (q : ℝ[X]) : ∫ v, q.eval v ∂fourPoint =
    2 / 5 * (q.eval 1 + q.eval (-1)) + 1 / 10 * (q.eval 4 + q.eval (-4)) := by
  have h : ∀ a : ℝ, Integrable (fun v => q.eval v) (Measure.dirac a) := fun a =>
    integrable_dirac (by simp)
  rw [fourPoint, integral_add_measure
    (((h 1).add_measure (h (-1))).smul_measure ENNReal.ofReal_ne_top)
    (((h 4).add_measure (h (-4))).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_add_measure (h 1) (h (-1)),
    integral_add_measure (h 4) (h (-4)), integral_dirac, integral_dirac, integral_dirac,
    integral_dirac]
  simp only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2 / 5),
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 10), smul_eq_mul]

/-- `MomentBasis` is inhabited: the orthonormal polynomials `1`, `v / 2`, `(v² - 4) / 6`,
`(v³ - 13 v) / 12` of `fourPoint` (non-vacuity of Theorem 3.2 of arXiv 2311.09425). -/
noncomputable def fourPointBasis : MomentBasis fourPoint where
  p := ![1, C (1 / 2) * X, C (1 / 6) * (X ^ 2 - C 4), C (1 / 12) * (X ^ 3 - C 13 * X)]
  integrable := integrable_fourPoint
  natDegree_eq := by
    intro k
    fin_cases k
    · simp
    · change (C (1 / 2 : ℝ) * X : ℝ[X]).natDegree = 1
      exact natDegree_C_mul_X _ (by norm_num)
    · change (C (1 / 6 : ℝ) * (X ^ 2 - C 4) : ℝ[X]).natDegree = 2
      compute_degree!
    · change (C (1 / 12 : ℝ) * (X ^ 3 - C 13 * X) : ℝ[X]).natDegree = 3
      compute_degree!
  orthonormal := by
    intro i j
    rw [integral_fourPoint]
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]

variable {μ : Measure ℝ}

/-- `w p₃` lies in `Φ^⊥` (auxiliary for the non-vacuity of Theorem 3.2 of arXiv 2311.09425). -/
theorem MomentBasis.wp_three_mem (B : MomentBasis μ) : B.wp 3 ∈ B.Φperp := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [B.inner_wp_wp]; simp

/-- `w p₃` is a unit vector (auxiliary for the non-vacuity of Theorem 3.2 of arXiv 2311.09425). -/
theorem MomentBasis.orthonormal_wp_three (B : MomentBasis μ) :
    Orthonormal ℝ (fun _ : Unit => B.wp 3) := by
  rw [orthonormal_iff_ite]
  rintro ⟨⟩ ⟨⟩
  rw [B.inner_wp_wp]
  simp

/-- With a vanishing right-hand side SSPRK2 is the identity (auxiliary for the non-vacuity of
Theorem 3.2 of arXiv 2311.09425). -/
theorem ssprk2_zero {Q : Type*} [AddCommGroup Q] [Module ℝ Q] {F : Q → Q} (hF : ∀ q, F q = 0)
    (τ : ℝ) (q : Q) : ssprk2 F τ q = q := by
  simp only [ssprk2, hF, smul_zero, add_zero]
  rw [← add_smul]
  norm_num

/-- **Non-vacuity of Theorem 3.2** of arXiv 2311.09425, on the continuous line: for `D = 0` the
state with `f₀ = f₁ = E = 0`, constant `f₂ = c` and rank-one micro part `g = a w p₃` is a stationary
run of the scheme with the exact `∂ₓ`, and all of its moments are differentiable. The spatial inner
product is the point mass at `0`, and `X₁ = 1`. -/
theorem MomentBasis.stationary_run (B : MomentBasis μ) (a c Δt : ℝ) :
    ∃ s : State μ ℝ Unit, (∀ j, s.V j ∈ B.Φperp) ∧
      B.IsSecondOrderStep (Measure.dirac 0) (fun _ _ _ _ => 0) derivₓ Δt s s s ∧
      (∀ x, B.IsRegularAt s x) ∧ ∀ x, lowRank s.X s.S s.V x = a • B.wp 3 := by
  let s : State μ ℝ Unit :=
    ⟨fun _ => 0, fun _ => 0, fun _ => c, fun _ => 0, fun _ _ => 1, fun _ _ => a, fun _ => B.wp 3⟩
  have hV : ∀ j, s.V j ∈ B.Φperp := fun _ => B.wp_three_mem
  have hP : B.Pperp 0 = 0 := by
    simp [Pperp, B.mom_eq]
  have hG : ∀ g x, B.frozen (fun _ _ _ _ => 0) s g x = 0 := fun g x => hP
  have hk : ∀ (V : Unit → Lp ℝ 2 μ) (K : Unit → ℝ → ℝ),
      kField (B.frozen (fun _ _ _ _ => 0) s) V K = 0 := fun V K => by
    funext j x
    simp [kField, hG]
  have hs : ∀ (X : Unit → ℝ → ℝ) (V : Unit → Lp ℝ 2 μ) (S : Matrix Unit Unit ℝ),
      sField (Measure.dirac 0) (B.frozen (fun _ _ _ _ => 0) s) X V S = 0 := fun X V S => by
    funext i j
    simp [sField, hG]
  have hl : ∀ (X : Unit → ℝ → ℝ) (L : Unit → Lp ℝ 2 μ),
      lField (Measure.dirac 0) (B.frozen (fun _ _ _ _ => 0) s) X L = 0 := fun X L => by
    funext i
    simp [lField, hG]
  have hf : ∀ k y, derivₓ (B.flux s) k y = 0 := by
    intro k y
    fin_cases k <;> simp [derivₓ, flux, f₃, s]
  have hx : IsXQR (Measure.dirac 0) (ssprk2 (kField (B.frozen (fun _ _ _ _ => 0) s) s.V)
      (Δt / 2) (kInit s.X s.S)) s.X s.S := by
    rw [ssprk2_zero (hk s.V)]
    exact ⟨fun _ _ => by simp [s], fun _ _ => rfl⟩
  have hv : B.IsVQR (ssprk2 (lField (Measure.dirac 0) (B.frozen (fun _ _ _ _ => 0) s) s.X)
      (Δt / 2) (lInit s.S s.V)) s.V s.S := by
    rw [ssprk2_zero (hl s.X)]
    exact B.isVQR_of_factor (R := s.Sᵀ) B.orthonormal_wp_three hV
      (fun j => by simp [lInit])
  refine ⟨s, hV, ⟨fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_,
    ⟨s.S, s.S, s.S, s.S, ⟨hx, ?_, hv, hv, ?_, hx⟩⟩, fun x => ?_, fun x => ?_, fun x => ?_⟩,
    fun x => ⟨differentiableAt_const _, differentiableAt_const _, differentiableAt_const _,
      differentiableAt_const (B.f₃ s 0)⟩, fun x => ?_⟩
  · rw [hf]; simp
  · rw [hf]; simp [s]
  · rw [hf]; simp [s]
  · simp [s]
  · simp [s]
  · exact (ssprk2_zero (hs _ _) _ _).symm
  · exact (ssprk2_zero (hs _ _) _ _).symm
  · rw [hf]; simp
  · rw [hf]; simp [s]
  · rw [hf]; simp [s]
  · simp [lowRank, s]

/-- **Non-vacuity of Corollary 3.3** of arXiv 2311.09425, concretely: for the explicit basis
`fourPointBasis`, rank one, any periodic grid, every `D`, every numerical flux and every initial
state with `V⁰ ⊥ Φ`, the fully discrete scheme runs. -/
theorem rational_run {N : ℕ} [NeZero N] [MeasurableSpace (ZMod N)]
    [MeasurableSingletonClass (ZMod N)]
    (D : (ZMod N → ℝ) → (ZMod N → Lp ℝ 2 fourPoint) → (ZMod N → Lp ℝ 2 fourPoint) → ZMod N →
      Lp ℝ 2 fourPoint)
    (Fhat : (Fin 3 → ZMod N → ℝ) → Fin 3 → ZMod N → ℝ) (Δx : ℝ) {Δt : ℝ} (hΔt : Δt ≠ 0)
    (s₀ : State fourPoint (ZMod N) Unit) (h₀ : ∀ j, s₀.V j ∈ fourPointBasis.Φperp) :
    ∃ s m : ℕ → State fourPoint (ZMod N) Unit, s 0 = s₀ ∧
      ∀ n, fourPointBasis.IsSecondOrderStep Measure.count D (fluxDiff Fhat Δx) Δt (s n) (m n)
        (s (n + 1)) :=
  fourPointBasis.exists_run_grid D _ hΔt
    (by simpa [ZMod.card] using Nat.one_le_iff_ne_zero.2 (NeZero.ne N))
    fourPointBasis.orthonormal_wp_three (fun _ => fourPointBasis.wp_three_mem) s₀ h₀

end Instances

/-! ### The ansatz and the moments in the core kinetic vocabulary -/

section KineticCore

variable {μ : Measure ℝ} {𝕏 ι : Type*} [Fintype ι]

/-- **The ansatz through the core, almost everywhere**: for every `x` the `L²(μ)`-valued low-rank
function `∑ᵢⱼ Xᵢ(x) Sᵢⱼ Vⱼ` of this file is represented by the core `Kinetic.lowRankAnsatz` (weight
`1`) of the representatives of the `V j`.  The two are not equal as definitions: this one takes
values in `L²(μ)`, the core one is a function of `x` and `v`. -/
theorem coeFn_lowRank (X : ι → 𝕏 → ℝ) (S : Matrix ι ι ℝ) (V : ι → Lp ℝ 2 μ) (x : 𝕏) :
    ⇑(lowRank X S V x) =ᵐ[μ] Kinetic.lowRankAnsatz 1 X S (fun j => ⇑(V j)) x := by
  have h2 : ∀ i, ⇑(∑ j, (X i x * S i j) • V j) =ᵐ[μ] ∑ j, (X i x * S i j) • ⇑(V j) := fun i =>
    (Lp.coeFn_finsetSum _ _).trans (eventuallyEq_sum fun j _ => Lp.coeFn_smul _ _)
  have h1 : ⇑(lowRank X S V x) =ᵐ[μ] ∑ i, ∑ j, (X i x * S i j) • ⇑(V j) :=
    (Lp.coeFn_finsetSum _ _).trans (eventuallyEq_sum fun i _ => h2 i)
  refine h1.trans (Filter.Eventually.of_forall fun v => ?_)
  simp [Kinetic.lowRankAnsatz_apply, Finset.sum_apply]

namespace MomentBasis

variable (B : MomentBasis μ)

/-- **The charge density through the core**: `ρ` is the core `Kinetic.velocityMoment` of the
distribution function with the function `1`. -/
theorem charge_eq_velocityMoment (s : State μ 𝕏 ι) :
    B.charge s = Kinetic.velocityMoment μ 1 (fun x => ⇑(B.dist s x)) := by
  funext x
  simp [charge, Kinetic.velocityMoment_apply]

/-- The current is the core velocity moment with the function `v`. -/
theorem current_eq_velocityMoment (s : State μ 𝕏 ι) :
    B.current s = Kinetic.velocityMoment μ (fun v => v) (fun x => ⇑(B.dist s x)) := rfl

/-- The kinetic energy density is the core velocity moment with the function `v² / 2`. -/
theorem kinetic_eq_velocityMoment (s : State μ 𝕏 ι) :
    B.kinetic s = Kinetic.velocityMoment μ (fun v => v ^ 2 / 2) (fun x => ⇑(B.dist s x)) := rfl

/-- The energy flux is the core velocity moment with the function `v³ / 2`. -/
theorem heatFlux_eq_velocityMoment (s : State μ 𝕏 ι) :
    B.heatFlux s = Kinetic.velocityMoment μ (fun v => v ^ 3 / 2) (fun x => ⇑(B.dist s x)) := rfl

end MomentBasis

/-- The bridge at nonzero data: with `X = 2` and `S = (3)` the low-rank function is represented by
`6 V₀`. -/
example (V : Fin 1 → Lp ℝ 2 μ) :
    ⇑(lowRank (fun (_ : Fin 1) (_ : ℝ) => 2) !![3] V 0) =ᵐ[μ] fun v => 6 * V 0 v := by
  refine (coeFn_lowRank _ _ V 0).trans (Filter.Eventually.of_forall fun v => ?_)
  simp [Kinetic.lowRankAnsatz_apply]
  norm_num

end KineticCore

end LeanDLRA.Literature.P2311_09425
