import LeanDLRA.Novel.OpOT61

/-!
# Rank versus angular resolution at equal memory in transport

Open problem OP-OT-58 of `docs/catalogue/survey/open-problems.json` ("rank-`r` DLR with many angles
beats full-rank `S_N` with `N ~ r` at equal memory; no theorem compares the two").
This file proves a sharp instance in one-dimensional slab geometry, with the actual matrices.

## Setting

`m` periodic cells `x_i = 2π i / m`, angular variable `v ∈ [-1, 1]` with the uniform measure,
`N` midpoint ordinates `v_j = -1 + (2j+1)/N` (`midV₀`, `midΔv`).  The data is isotropic,
`g ⊗ 1`, with `g` a real trigonometric polynomial of degree `K` (`trigPoly`, from OpOT61).  The
discrete-ordinates solution of free streaming `∂_t f + v ∂_x f = 0` is `snSol m N K a b t`,
`F(t)_{ij} = g(x_i - v_j t)` (exact along each ordinate), its scalar flux is the midpoint rule
`flux F = (1/N) ∑_j F_{·j}`, and the exact scalar flux is
`exactFlux K a b t x = ½ ∫_{-1}^{1} g(x - v t) dv = ∑_k (a_k cos kx + b_k sin kx) sinc(k t)`
(`exactFlux_eq_integral`).  A rank-`r` DLRA on `n` angles stores `r (m + n)` numbers
(`dlraMemory`), the full `S_N` solution stores `m N` (`snMemory`); `affordableAngles m N r =
⌊m N / r⌋ - m` is the angular grid a rank-`r` method can afford at the memory of `S_N`.

## Main results (free streaming, ray effects as recurrence)

* `flux_snSol`: the `S_N` flux of mode `k` is the mode times `midAvgCos N (k t) =
  sin(k t) / (N sin(k t / N))` (Dirichlet kernel, `sum_cos_odd_mul_sin`, `midAvgCos_mul_sin`),
  where the exact factor is `sinc(k t)`.
* `abs_flux_sub_exactFlux_le` (**rate**): for `0 < t ≤ N π / (2K)`,
  `|ρ_N - ρ| ≤ (∑_k (|a_k| + |b_k|) k) · π t / (12 N²)` pointwise.
* `flux_snSol_recur`, `exactFlux_recur`, `sum_sq_err_recur_eq`, `le_sum_sq_err_recur`
  (**lower bound for the full method at given memory**): at the recurrence time `t_N = N π / k`
  all `N` ordinates recombine coherently, `ρ_N(t_N) = (-1)^{N+1} cos(k x)` while `ρ(t_N) = 0`:
  the `l²` error equals the `l²` norm of the initial flux (relative error one), for every `N` and
  `m`; with other modes present the squared error is still `≥ (m/2)(a_k² + b_k²)`
  (`sum_sq_flux_sub_exact`, a discrete Parseval identity).  With memory `m N`, the full method
  fails at a time linear in `N = memory / m`.
* `rank_snSol_le`, `rank_snSol_pi`, `rank_snSol_pureMode_le` (**rank**): the `n`-ordinate
  solution has rank `≤ 2K + 1` for every `n` and `t`, exactly `2K + 1` at `t = π` (OpOT61), and
  `≤ 2` for a single mode.  So the rank-`(2K+1)` DLRA on `n` angles reproduces the `n`-ordinate
  solution (the integrators are exact on the rank manifold, `LeanDLRA.Integrators.Exactness`), and
  its only error is the angular quadrature error of the fine grid.
* `flux_snSol_fine_recur`: any finer grid `n > N` is **exact** at `t_N` (`sin(Nπ) = 0`,
  `sin(Nπ/n) ≠ 0`).
* `equal_memory_free_streaming`, `equal_memory_free_streaming'`, `equal_memory_modes`,
  `affordable_modes` (**the comparison**): at `(2K+1)(m + n) ≤ m N` with `n > N`, at the time
  `t_N` where `S_N` has lost a whole mode, the DLRA flux error is zero for that mode and at most
  `(∑ (|a_k| + |b_k|) k) π t / (12 n²)` in total before `t = n π / (2K)`; with
  `n ≈ m N / (2K+1)` this is smaller by the factor `(2K+1)² / m²` at equal time, and the
  failure time is later by the factor `n / N ≈ m / (2K+1)`.

## Scattering-dominated limit

`csStep` is one collide–stream step: free flight for `Δt` followed by complete re-isotropisation
(`σ Δt → ∞`); `trigPoly_csStep` shows it is the relaxed flux of `snSol`.  `abs_cs_sub_exact_le`:
the `S_N` error after `j` steps is at most `(∑ (|a_k| + |b_k|) k) π (j Δt) / (12 N²)` for all
`j`, with `K Δt ≤ N π / 2`: the same per-step quadrature error as in free streaming, but no
coherent recombination, so no recurrence; the solution is isotropic (rank one) after each step.

## What is not proved

The comparison for finite scattering `0 < σ < ∞` (the `S_N` flux error of the kinetic equation
with scattering), two-dimensional ray effects from a localised source, and data that is not
band-limited (where the rank of free streaming grows with `t`, see OpOT61) remain open.  Nothing
here is a statement about a particular DLRA integrator; the DLRA side is the exact rank-`r`
solution on the fine angular grid.

Prior work: arXiv 1912.07522 (Peng, McClarren, Hauck), 2011.06072, 2206.14404 observe the
phenomenon numerically; the recurrence of uniform velocity grids is classical in Vlasov
simulation (recurrence time `2π / (k Δv)`), and ray effects go back to Lathrop (1968).
-/

open Set Filter Topology Finset Real
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Novel.OpOT58

open LeanDLRA LeanDLRA.Frobenius LeanDLRA.Novel.OpOT61

/-! ### The Dirichlet kernel identity -/

section Dirichlet

/-- `∑_{j<N} cos(α - (2j+1)θ) · sin θ = cos(α - Nθ) · sin(Nθ)`. -/
theorem sum_cos_odd_mul_sin (α θ : ℝ) (N : ℕ) :
    (∑ j ∈ range N, cos (α - (2 * j + 1) * θ)) * sin θ = cos (α - N * θ) * sin (N * θ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, add_mul, ih]
    have key : ∀ u φ : ℝ, cos u * sin φ + cos (u - φ - θ) * sin θ = cos (u - θ) * sin (φ + θ) := by
      intro u φ
      rw [cos_sub (u - φ) θ, cos_sub u φ, sin_sub u φ, cos_sub u θ, sin_add φ θ]
      linear_combination (-(cos u * sin φ)) * sin_sq_add_cos_sq θ
    have e1 : α - ((N : ℝ) + 1) * θ = (α - N * θ) - θ := by ring
    have e2 : ((N : ℝ) + 1) * θ = N * θ + θ := by ring
    have e3 : α - (2 * (N : ℝ) + 1) * θ = (α - N * θ) - N * θ - θ := by ring
    push_cast
    rw [e1, e2, e3]
    exact key _ _

end Dirichlet

/-! ### The midpoint quadrature of the cosine -/

section Midpoint

/-- Offset of the `N`-point midpoint grid on `[-1, 1]`: `v₀ = -1 + 1/N`. -/
noncomputable def midV₀ (N : ℕ) : ℝ := -1 + 1 / N

/-- Spacing of the `N`-point midpoint grid on `[-1, 1]`: `Δv = 2/N`. -/
noncomputable def midΔv (N : ℕ) : ℝ := 2 / N

theorem vGrid_mid (N : ℕ) (j : Fin N) :
    vGrid (midV₀ N) (midΔv N) j = -1 + (2 * j.val + 1) / N := by
  unfold vGrid midV₀ midΔv; ring

theorem vGrid_mid_rev (N : ℕ) (j : Fin N) :
    vGrid (midV₀ N) (midΔv N) (Fin.rev j) = -vGrid (midV₀ N) (midΔv N) j := by
  have hN : (N : ℝ) ≠ 0 := by
    have := j.isLt; exact_mod_cast (by omega : N ≠ 0)
  rw [vGrid_mid, vGrid_mid, Fin.val_rev, Nat.cast_sub (by have := j.isLt; omega)]
  push_cast
  field_simp
  ring

/-- The `N`-point midpoint rule for `½ ∫_{-1}^{1} cos(s v) dv`: `(1/N) ∑_j cos(s v_j)`. -/
noncomputable def midAvgCos (N : ℕ) (s : ℝ) : ℝ :=
  (∑ j : Fin N, cos (s * vGrid (midV₀ N) (midΔv N) j)) / N

/-- The midpoint rule for `½ ∫_{-1}^{1} sin(s v) dv` vanishes by symmetry. -/
theorem sum_sin_mid (N : ℕ) (s : ℝ) : ∑ j : Fin N, sin (s * vGrid (midV₀ N) (midΔv N) j) = 0 := by
  have h : ∑ j : Fin N, sin (s * vGrid (midV₀ N) (midΔv N) j) =
      ∑ j : Fin N, sin (s * vGrid (midV₀ N) (midΔv N) (Fin.rev j)) :=
    (Equiv.sum_comp Fin.revPerm (fun j => sin (s * vGrid (midV₀ N) (midΔv N) j))).symm
  simp_rw [vGrid_mid_rev, mul_neg, sin_neg] at h
  rw [sum_neg_distrib] at h
  linarith

/-- **Closed form of the midpoint rule**: `midAvgCos N s · sin(s/N) = sin(s)/N`
(the Dirichlet kernel). -/
theorem midAvgCos_mul_sin (N : ℕ) (hN : N ≠ 0) (s : ℝ) :
    midAvgCos N s * sin (s / N) = sin s / N := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have h := sum_cos_odd_mul_sin (N * (s / N)) (s / N) N
  rw [sub_self, cos_zero, one_mul, mul_div_cancel₀ _ hN'] at h
  have hsum : ∑ j : Fin N, cos (s * vGrid (midV₀ N) (midΔv N) j) =
      ∑ j ∈ range N, cos (s - (2 * j + 1) * (s / N)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ => cos (s - (2 * j + 1) * (s / N))) N]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [vGrid_mid, ← cos_neg]
    congr 1
    field_simp
    ring
  unfold midAvgCos
  rw [hsum, div_mul_eq_mul_div, h]

theorem midAvgCos_eq (N : ℕ) (hN : N ≠ 0) {s : ℝ} (hs : sin (s / N) ≠ 0) :
    midAvgCos N s = sin s / (N * sin (s / N)) := by
  have h := midAvgCos_mul_sin N hN s
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  rw [eq_div_iff hN'] at h
  rw [eq_div_iff (mul_ne_zero hN' hs)]
  linear_combination h

theorem midAvgCos_zero (N : ℕ) (hN : N ≠ 0) : midAvgCos N 0 = 1 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  simp [midAvgCos, hN']

/-- **Recurrence**: at `s = Nπ` every node contributes `(-1)^{N+1}`, so the midpoint rule
returns `(-1)^{N+1}` while the exact average `sin(s)/s` vanishes. -/
theorem midAvgCos_recur (N : ℕ) (hN : N ≠ 0) : midAvgCos N (N * π) = (-1) ^ (N + 1) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  unfold midAvgCos
  have h : ∀ j : Fin N, cos (N * π * vGrid (midV₀ N) (midΔv N) j) = (-1) ^ (N + 1) := by
    intro j
    rw [vGrid_mid]
    have e : (N : ℝ) * π * (-1 + (2 * j.val + 1) / N) = ((2 * j.val + 1 : ℕ) : ℝ) * π - N * π := by
      push_cast; field_simp; ring
    rw [e, cos_sub_nat_mul_pi, cos_nat_mul_pi]
    rw [pow_succ, pow_succ, pow_mul]; norm_num
  simp_rw [h]
  simp [hN']

theorem midAvgCos_eq_zero (N : ℕ) (hN : N ≠ 0) {s : ℝ} (h : sin s = 0) (hs : sin (s / N) ≠ 0) :
    midAvgCos N s = 0 := by
  rw [midAvgCos_eq N hN hs, h, zero_div]

/-- The normalised sine `sin(s)/s`, the exact value `½ ∫_{-1}^{1} cos(s v) dv`. -/
noncomputable def sinc (s : ℝ) : ℝ := if s = 0 then 1 else sin s / s

theorem sinc_zero : sinc 0 = 1 := by simp [sinc]

theorem sinc_of_ne {s : ℝ} (hs : s ≠ 0) : sinc s = sin s / s := by simp [sinc, hs]

theorem sinc_nat_mul_pi {N : ℕ} (hN : N ≠ 0) : sinc (N * π) = 0 := by
  have : (N : ℝ) * π ≠ 0 := mul_ne_zero (by exact_mod_cast hN) pi_ne_zero
  rw [sinc_of_ne this, sin_nat_mul_pi, zero_div]

/-- Elementary: `1/sin θ - 1/θ ≤ π θ / 12` on `(0, π/2]`, from `sin θ ≥ 2θ/π` and
`sin θ ≥ θ - θ³/6`. -/
theorem inv_sin_sub_inv_le {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ π / 2) :
    1 / sin θ - 1 / θ ≤ π * θ / 12 := by
  have h1 : 2 / π * θ ≤ sin θ := mul_le_sin h0.le hπ
  have h2 : θ - θ ^ 3 / 6 < sin θ := sin_gt_sub_cube h0
  have hs : 0 < sin θ := lt_of_lt_of_le (by positivity) h1
  rw [div_sub_div _ _ hs.ne' h0.ne', div_le_div_iff₀ (by positivity) (by norm_num)]
  have h3 : θ ^ 2 * (2 / π) ≤ θ * sin θ := by
    have := mul_le_mul_of_nonneg_left h1 h0.le
    nlinarith
  have hπ0 : 0 < π := pi_pos
  have h4 : π * θ * (θ ^ 2 * (2 / π)) = 2 * θ ^ 3 := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ π * θ), h4, h2]

theorem one_div_le_one_div_sin {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ π / 2) :
    1 / θ ≤ 1 / sin θ := by
  have h1 : 2 / π * θ ≤ sin θ := mul_le_sin h0.le hπ
  have hs : 0 < sin θ := lt_of_lt_of_le (by positivity) h1
  exact one_div_le_one_div_of_le hs (sin_le h0.le)

/-- **Rate of the midpoint rule before recurrence.**  For `0 < s ≤ Nπ/2`,
`|midAvgCos N s - sinc s| ≤ π s / (12 N²)`. -/
theorem abs_midAvgCos_sub_sinc_le (N : ℕ) (hN : N ≠ 0) {s : ℝ} (hs : 0 < s)
    (hsN : s ≤ N * π / 2) :
    |midAvgCos N s - sinc s| ≤ π * s / (12 * N ^ 2) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  set θ := s / N with hθ
  have hθ0 : 0 < θ := div_pos hs hN'
  have hθπ : θ ≤ π / 2 := by
    rw [hθ, div_le_iff₀ hN']; linarith
  have hsθ : s = N * θ := by rw [hθ]; field_simp
  have hsin : sin θ ≠ 0 := by
    have h1 : 2 / π * θ ≤ sin θ := mul_le_sin hθ0.le hθπ
    exact (lt_of_lt_of_le (by positivity) h1).ne'
  rw [midAvgCos_eq N hN hsin, sinc_of_ne hs.ne']
  have e : sin s / (N * sin θ) - sin s / s = sin s / N * (1 / sin θ - 1 / θ) := by
    rw [hsθ]; field_simp
  rw [e, abs_mul, abs_div, abs_of_pos hN']
  have hge : 0 ≤ 1 / sin θ - 1 / θ := by
    linarith [one_div_le_one_div_sin hθ0 hθπ]
  rw [abs_of_nonneg hge]
  have hb := inv_sin_sub_inv_le hθ0 hθπ
  have hsin1 : |sin s| ≤ 1 := abs_sin_le_one s
  calc |sin s| / N * (1 / sin θ - 1 / θ) ≤ 1 / N * (π * θ / 12) := by
        gcongr
      _ = π * s / (12 * N ^ 2) := by rw [hsθ]; field_simp

end Midpoint

/-! ### The exact scalar flux -/

section Exact

theorem integral_cos_mul_const (c : ℝ) : ∫ v in (-1 : ℝ)..1, cos (c * v) = 2 * sinc c := by
  by_cases hc : c = 0
  · subst hc; simp [sinc_zero]; norm_num
  · rw [intervalIntegral.integral_comp_mul_left (fun v => cos v) hc, integral_cos, sinc_of_ne hc]
    rw [mul_neg_one, sin_neg, smul_eq_mul]
    field_simp
    ring

theorem integral_sin_mul_const (c : ℝ) : ∫ v in (-1 : ℝ)..1, sin (c * v) = 0 := by
  by_cases hc : c = 0
  · subst hc; simp
  · rw [intervalIntegral.integral_comp_mul_left (fun v => sin v) hc, integral_sin]
    rw [mul_neg_one, mul_one, cos_neg, sub_self, smul_zero]

/-- **The exact scalar flux** of free streaming with isotropic data `g ⊗ 1` and the uniform
angular measure on `[-1, 1]`: `ρ(t, x) = ½ ∫_{-1}^{1} g(x - v t) dv = ∑_k (a_k cos kx + b_k sin kx)
sinc(k t)`, the phase-mixed (Landau-damped) flux, decaying like `1/(k t)`. -/
noncomputable def exactFlux (K : ℕ) (a b : ℕ → ℝ) (t x : ℝ) : ℝ :=
  ∑ k ∈ range (K + 1), (a k * cos (k * x) + b k * sin (k * x)) * sinc (k * t)

/-- One mode under the angular integral. -/
theorem integral_mode (a b k x t : ℝ) :
    ∫ v in (-1 : ℝ)..1, (a * cos (k * (x - v * t)) + b * sin (k * (x - v * t))) =
      2 * (a * cos (k * x) + b * sin (k * x)) * sinc (k * t) := by
  have e : ∀ v : ℝ, a * cos (k * (x - v * t)) + b * sin (k * (x - v * t)) =
      (a * cos (k * x) + b * sin (k * x)) * cos ((k * t) * v) +
        (a * sin (k * x) - b * cos (k * x)) * sin ((k * t) * v) := by
    intro v
    rw [show k * (x - v * t) = k * x - (k * t) * v by ring, cos_sub, sin_sub]
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_cos_mul_const, integral_sin_mul_const]
  · ring
  · exact (by fun_prop : Continuous fun v : ℝ =>
      (a * cos (k * x) + b * sin (k * x)) * cos ((k * t) * v)).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun v : ℝ =>
      (a * sin (k * x) - b * cos (k * x)) * sin ((k * t) * v)).intervalIntegrable _ _

/-- `exactFlux` is the angular average of the free-streaming solution. -/
theorem exactFlux_eq_integral (K : ℕ) (a b : ℕ → ℝ) (t x : ℝ) :
    exactFlux K a b t x = (1 / 2) * ∫ v in (-1 : ℝ)..1, trigPoly K a b (x - v * t) := by
  unfold trigPoly
  rw [intervalIntegral.integral_finsetSum (fun k _ => (by fun_prop : Continuous fun v : ℝ =>
      a k * cos (k * (x - v * t)) + b k * sin (k * (x - v * t))).intervalIntegrable _ _)]
  unfold exactFlux
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_mode]; ring

end Exact

/-! ### The `S_N` solution and its scalar flux -/

section Transport

variable {m N : ℕ} [NeZero m]

/-- **The discrete-ordinates free-streaming solution**: `m` periodic cells `x_i = 2π i/m`, `N`
midpoint ordinates `v_j = -1 + (2j+1)/N`, data `g ⊗ 1` with `g` a trigonometric polynomial of
degree `K`; `F(t)_{ij} = g(x_i - v_j t)`, exact in space and time along each ordinate.  Both the
`S_N` method (`N` small) and the angular grid of a DLRA (`N = n` large) are instances. -/
noncomputable def snSol (m N : ℕ) [NeZero m] (K : ℕ) (a b : ℕ → ℝ) (t : ℝ) :
    Matrix (ZMod m) (Fin N) ℝ :=
  freeStream K a b (midV₀ N) (midΔv N) t

/-- The scalar flux by the `N`-point midpoint rule, `ρ_i = (1/N) ∑_j F_{ij}`. -/
noncomputable def flux (F : Matrix (ZMod m) (Fin N) ℝ) : ZMod m → ℝ := fun i => (∑ j, F i j) / N

/-- **Closed form of the `S_N` scalar flux**: every spatial mode is multiplied by the midpoint
average `midAvgCos N (k t)` of `cos(k t v)`; the sine averages vanish by symmetry. -/
theorem flux_snSol (hN : N ≠ 0) (K : ℕ) (a b : ℕ → ℝ) (t : ℝ) (i : ZMod m) :
    flux (snSol m N K a b t) i =
      ∑ k ∈ range (K + 1), (a k * cos (k * xGrid m i) + b k * sin (k * xGrid m i)) *
        midAvgCos N (k * t) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  unfold flux snSol freeStream trigPoly
  simp only [Matrix.of_apply]
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : ∀ j : Fin N, a k * cos (k * (xGrid m i - vGrid (midV₀ N) (midΔv N) j * t)) +
      b k * sin (k * (xGrid m i - vGrid (midV₀ N) (midΔv N) j * t)) =
      (a k * cos (k * xGrid m i) + b k * sin (k * xGrid m i)) *
        cos ((k * t) * vGrid (midV₀ N) (midΔv N) j) +
      (a k * sin (k * xGrid m i) - b k * cos (k * xGrid m i)) *
        sin ((k * t) * vGrid (midV₀ N) (midΔv N) j) := by
    intro j
    rw [show (k : ℝ) * (xGrid m i - vGrid (midV₀ N) (midΔv N) j * t) =
      k * xGrid m i - (k * t) * vGrid (midV₀ N) (midΔv N) j by ring, cos_sub, sin_sub]
    ring
  simp_rw [e]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_sin_mid, mul_zero, add_zero]
  unfold midAvgCos
  ring

/-- **Rate before recurrence.**  For `0 < t` with `K t ≤ N π / 2` the `S_N` flux differs from
the exact flux by at most `(∑_k (|a_k| + |b_k|) k) · π t / (12 N²)`: second order in the angular
spacing, growing linearly in time. -/
theorem abs_flux_sub_exactFlux_le (hN : N ≠ 0) (K : ℕ) (a b : ℕ → ℝ) {t : ℝ} (ht : 0 < t)
    (hKt : K * t ≤ N * π / 2) (i : ZMod m) :
    |flux (snSol m N K a b t) i - exactFlux K a b t (xGrid m i)| ≤
      (∑ k ∈ range (K + 1), (|a k| + |b k|) * k) * (π * t / (12 * N ^ 2)) := by
  rw [flux_snSol hN, exactFlux, ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  rw [← mul_sub, abs_mul]
  have hk : (k : ℝ) ≤ K := by
    have := Finset.mem_range.mp hk; exact_mod_cast (by omega : k ≤ K)
  have h1 : |a k * cos (k * xGrid m i) + b k * sin (k * xGrid m i)| ≤ |a k| + |b k| :=
    (abs_add_le _ _).trans (add_le_add
      (by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _))
      (by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (abs_sin_le_one _)))
  have h2 : |midAvgCos N (k * t) - sinc (k * t)| ≤ k * (π * t / (12 * N ^ 2)) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0; simp [midAvgCos_zero N hN, sinc_zero]
    · have hkt : 0 < (k : ℝ) * t := mul_pos (by exact_mod_cast hk0) ht
      have hkt' : (k : ℝ) * t ≤ N * π / 2 :=
        le_trans (mul_le_mul_of_nonneg_right hk ht.le) hKt
      refine (abs_midAvgCos_sub_sinc_le N hN hkt hkt').trans (le_of_eq ?_)
      ring
  calc |a k * cos (k * xGrid m i) + b k * sin (k * xGrid m i)| *
        |midAvgCos N (k * t) - sinc (k * t)| ≤ (|a k| + |b k|) * (k * (π * t / (12 * N ^ 2))) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = (|a k| + |b k|) * k * (π * t / (12 * N ^ 2)) := by ring

end Transport

/-! ### Rank of the angular-grid solution -/

section Rank

variable {m N : ℕ} [NeZero m]

/-- **Upper bound on the rank** (OpOT61): the solution on any number `N` of ordinates has rank at
most `2K + 1`, the number of real spatial modes of the data, for all `t`. -/
theorem rank_snSol_le (K : ℕ) (a b : ℕ → ℝ) (t : ℝ) :
    (snSol m N K a b t).rank ≤ 2 * K + 1 :=
  rank_freeStream_le K a b _ _ t

/-- **The bound is attained at `t = π`** (OpOT61, first shear time of the midpoint grid): with all
modes present and `2K < m`, `2K < N`, the rank is exactly `2K + 1`.  No rank below the spatial
bandwidth reproduces the `N`-ordinate solution. -/
theorem rank_snSol_pi (hK : 2 * K < m) (hKN : 2 * K < N) (hN : 0 < N) (a b : ℕ → ℝ)
    (hb0 : b 0 = 0) (ha0 : a 0 ≠ 0) (hab : ∀ k, 0 < k → k ≤ K → 0 < a k ^ 2 + b k ^ 2) :
    (snSol m N K a b π).rank = 2 * K + 1 := by
  refine rank_freeStream_shear hK a b hb0 ha0 hab (midV₀ N) (midΔv N) π (p := 1) ?_
    (shear_condition_one hKN) hN
  unfold midΔv; push_cast; ring

end Rank

/-! ### A single mode: recurrence of `S_N` -/

section Recurrence

variable {m N n k : ℕ} [NeZero m]

/-- The pure mode `g(x) = cos(k x)`: coefficients `a = e_k`, `b = 0`. -/
def pureMode (k : ℕ) : ℕ → ℝ := fun k' => if k' = k then 1 else 0

theorem trigPoly_pureMode (k : ℕ) (x : ℝ) :
    trigPoly k (pureMode k) (fun _ => 0) x = cos (k * x) := by
  unfold trigPoly pureMode
  simp [Finset.sum_ite_eq', Finset.mem_range]

theorem snSol_pureMode_apply (N k : ℕ) (t : ℝ) (i : ZMod m) (j : Fin N) :
    snSol m N k (pureMode k) (fun _ => 0) t i j =
      cos (k * (xGrid m i - vGrid (midV₀ N) (midΔv N) j * t)) := by
  unfold snSol freeStream
  simp only [Matrix.of_apply]
  exact trigPoly_pureMode k _

/-- The flux of the pure mode: `cos(k x_i) · midAvgCos N (k t)`. -/
theorem flux_snSol_pureMode (hN : N ≠ 0) (k : ℕ) (t : ℝ) (i : ZMod m) :
    flux (snSol m N k (pureMode k) (fun _ => 0) t) i =
      cos (k * xGrid m i) * midAvgCos N (k * t) := by
  rw [flux_snSol hN]
  unfold pureMode
  simp [Finset.sum_ite_eq', Finset.mem_range]

theorem exactFlux_pureMode (k : ℕ) (t x : ℝ) :
    exactFlux k (pureMode k) (fun _ => 0) t x = cos (k * x) * sinc (k * t) := by
  unfold exactFlux pureMode
  simp [Finset.sum_ite_eq', Finset.mem_range]

/-- A pure mode has rank at most two on every angular grid, for all `t`. -/
theorem rank_snSol_pureMode_le (N k : ℕ) (t : ℝ) :
    (snSol m N k (pureMode k) (fun _ => 0) t).rank ≤ 2 := by
  unfold snSol
  rw [freeStream_eq_sum_modeMat, Finset.sum_eq_single k]
  · exact rank_modeMat_le _ _ _
  · intro k' _ hk'
    ext i j
    simp [modeMat_apply, pVec, qVec, pureMode, hk']
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- **The recurrence time** of `N` uniformly spaced ordinates for mode `k`: `t_N = N π / k`,
the time at which `k t Δv = 2π`. -/
noncomputable def recurTime (N k : ℕ) : ℝ := N * π / k

theorem k_mul_recurTime (hk : k ≠ 0) : (k : ℝ) * recurTime N k = N * π := by
  have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  unfold recurTime; field_simp

/-- **`S_N` at its recurrence time returns the full initial mode** (up to sign): all `N` ordinates
have travelled an integer number of half periods and recombine coherently. -/
theorem flux_snSol_recur (hN : N ≠ 0) (hk : k ≠ 0) (i : ZMod m) :
    flux (snSol m N k (pureMode k) (fun _ => 0) (recurTime N k)) i =
      (-1) ^ (N + 1) * cos (k * xGrid m i) := by
  rw [flux_snSol_pureMode hN, k_mul_recurTime hk, midAvgCos_recur N hN]; ring

/-- **The exact flux vanishes at the recurrence time**: `sinc(N π) = 0`. -/
theorem exactFlux_recur (hN : N ≠ 0) (hk : k ≠ 0) (x : ℝ) :
    exactFlux k (pureMode k) (fun _ => 0) (recurTime N k) x = 0 := by
  rw [exactFlux_pureMode, k_mul_recurTime hk, sinc_nat_mul_pi hN, mul_zero]

/-- **Any finer grid is exact at the coarse recurrence time**: for `N < n` the `n`-ordinate flux
vanishes at `t_N`, because `sin(N π) = 0` while `sin(N π / n) ≠ 0`. -/
theorem flux_snSol_fine_recur (hN : N ≠ 0) (hNn : N < n) (hk : k ≠ 0) (i : ZMod m) :
    flux (snSol m n k (pureMode k) (fun _ => 0) (recurTime N k)) i = 0 := by
  have hn : n ≠ 0 := by omega
  rw [flux_snSol_pureMode hn, k_mul_recurTime hk, midAvgCos_eq_zero n hn (sin_nat_mul_pi N),
    mul_zero]
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hNn' : (N : ℝ) < n := by exact_mod_cast hNn
  refine (sin_pos_of_pos_of_lt_pi (by positivity) ?_).ne'
  rw [div_lt_iff₀ hn']
  nlinarith [pi_pos]

/-- The grid `l²` norm of the mode below the Nyquist limit: `∑_i cos²(k x_i) = m/2`. -/
theorem sum_sq_cos_grid (hk0 : 0 < k) (hk : 2 * k < m) :
    ∑ i : ZMod m, cos (k * xGrid m i) ^ 2 = m / 2 := by
  have h := sum_xwave_mul_same (N := m) hk0 hk 1 0 1 0
  simp only [one_mul, zero_mul, add_zero, mul_one, mul_zero] at h
  rw [sum_zmod_val' _ (fun i : ℕ => cos (i * modeAngle m k) * cos (i * modeAngle m k)) ?_, h]
  intro i
  rw [sq]
  congr 2 <;> (unfold xGrid modeAngle; ring)

/-- The initial scalar flux is the mode itself. -/
theorem flux_snSol_pureMode_zero (hN : N ≠ 0) (k : ℕ) (i : ZMod m) :
    flux (snSol m N k (pureMode k) (fun _ => 0) 0) i = cos (k * xGrid m i) := by
  rw [flux_snSol_pureMode hN, mul_zero, midAvgCos_zero N hN, mul_one]

/-- **Complete failure of `S_N` at its recurrence time**: the `l²` error of its scalar flux equals
the `l²` norm of the initial flux (relative error exactly one), for every `N`, independently of
the spatial resolution `m`. -/
theorem sum_sq_err_recur (hk0 : 0 < k) (hN : N ≠ 0) :
    ∑ i : ZMod m, (flux (snSol m N k (pureMode k) (fun _ => 0) (recurTime N k)) i -
        exactFlux k (pureMode k) (fun _ => 0) (recurTime N k) (xGrid m i)) ^ 2 =
      ∑ i : ZMod m, (flux (snSol m N k (pureMode k) (fun _ => 0) 0) i) ^ 2 := by
  have hk' : k ≠ 0 := by omega
  simp_rw [flux_snSol_recur hN hk', exactFlux_recur hN hk', flux_snSol_pureMode_zero hN, sub_zero,
    mul_pow]
  rw [← pow_mul, pow_mul', pow_succ]
  simp

/-- The value of both sides of `sum_sq_err_recur` below the Nyquist limit: `m / 2`. -/
theorem sum_sq_err_recur_eq (hk0 : 0 < k) (hk : 2 * k < m) (hN : N ≠ 0) :
    ∑ i : ZMod m, (flux (snSol m N k (pureMode k) (fun _ => 0) (recurTime N k)) i -
        exactFlux k (pureMode k) (fun _ => 0) (recurTime N k) (xGrid m i)) ^ 2 = m / 2 := by
  rw [sum_sq_err_recur hk0 hN]
  simp_rw [flux_snSol_pureMode_zero hN]
  exact sum_sq_cos_grid hk0 hk

/-- **Discrete Parseval below the Nyquist limit**: for `2K < m`,
`∑_i g(x_i)² = m a_0² + (m/2) ∑_{k=1}^{K} (a_k² + b_k²)`. -/
theorem sum_sq_trigPoly_grid {K : ℕ} (hK : 2 * K < m) (a b : ℕ → ℝ) :
    ∑ i : ZMod m, trigPoly K a b (xGrid m i) ^ 2 =
      ∑ k ∈ range (K + 1), (if k = 0 then m * a 0 ^ 2 else m * (a k ^ 2 + b k ^ 2) / 2) := by
  set w : ℕ → ℕ → ℝ := fun k i => a k * cos (i * modeAngle m k) + b k * sin (i * modeAngle m k)
    with hw
  have h1 : ∀ i : ZMod m, trigPoly K a b (xGrid m i) ^ 2 =
      ∑ k ∈ range (K + 1), ∑ k' ∈ range (K + 1), w k i.val * w k' i.val := by
    intro i
    unfold trigPoly
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
    simp only [hw]
    have e : ∀ k : ℕ, (k : ℝ) * xGrid m i = i.val * modeAngle m k := by
      intro k; unfold xGrid modeAngle; ring
    rw [e k, e k']
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.sum_comm]
  have hkK : k ≤ K := by have := Finset.mem_range.mp hk; omega
  rw [Finset.sum_eq_single k]
  · rw [sum_zmod_val' _ (fun i => w k i * w k i) (fun _ => rfl)]
    split_ifs with h0
    · subst h0
      simp [hw, modeAngle_zero, sq]
    · have h := sum_xwave_mul_same (N := m) (Nat.pos_of_ne_zero h0) (by omega)
        (a k) (b k) (a k) (b k)
      simp only [hw]
      rw [h]; ring
  · intro k' hk' hne
    rw [sum_zmod_val' _ (fun i => w k i * w k' i) (fun _ => rfl)]
    exact sum_xwave_mul_eq_zero (N := m) (by omega) (by have := Finset.mem_range.mp hk'; omega)
      (Ne.symm hne) (a k) (b k) (a k') (b k')
  · intro h; exact absurd hk h

/-- **Parseval for the flux error**: the squared grid `l²` error of the `S_N` scalar flux is
`(m/2) ∑_k (a_k² + b_k²) (midAvgCos N (k t) - sinc(k t))²`, mode by mode. -/
theorem sum_sq_flux_sub_exact (hN : N ≠ 0) {K : ℕ} (hK : 2 * K < m) (a b : ℕ → ℝ) (t : ℝ) :
    ∑ i : ZMod m, (flux (snSol m N K a b t) i - exactFlux K a b t (xGrid m i)) ^ 2 =
      ∑ k ∈ range (K + 1),
        m * (a k ^ 2 + b k ^ 2) / 2 * (midAvgCos N (k * t) - sinc (k * t)) ^ 2 := by
  have h1 : ∀ i : ZMod m, flux (snSol m N K a b t) i - exactFlux K a b t (xGrid m i) =
      trigPoly K (fun k => a k * (midAvgCos N (k * t) - sinc (k * t)))
        (fun k => b k * (midAvgCos N (k * t) - sinc (k * t))) (xGrid m i) := by
    intro i
    rw [flux_snSol hN, exactFlux]
    unfold trigPoly
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp_rw [h1]
  rw [sum_sq_trigPoly_grid hK]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with h0
  · subst h0
    simp [midAvgCos_zero N hN, sinc_zero]
  · ring

/-- **Lower bound for `S_N` at given memory, general data.**  Whatever the other modes do, at the
recurrence time `t = N π / k` of a mode `1 ≤ k ≤ K` present in the data, the squared `l²` error
of the `S_N` flux is at least `(m/2)(a_k² + b_k²)`, the squared norm of that mode's initial
flux.  The time of failure `N π / k` is linear in the memory `m N` per cell. -/
theorem le_sum_sq_err_recur (hN : N ≠ 0) {K : ℕ} (hK : 2 * K < m) (a b : ℕ → ℝ) (hk0 : 0 < k)
    (hkK : k ≤ K) :
    m * (a k ^ 2 + b k ^ 2) / 2 ≤
      ∑ i : ZMod m, (flux (snSol m N K a b (recurTime N k)) i -
        exactFlux K a b (recurTime N k) (xGrid m i)) ^ 2 := by
  rw [sum_sq_flux_sub_exact hN hK]
  have hterm : m * (a k ^ 2 + b k ^ 2) / 2 *
      (midAvgCos N (k * recurTime N k) - sinc (k * recurTime N k)) ^ 2 =
      m * (a k ^ 2 + b k ^ 2) / 2 := by
    rw [k_mul_recurTime (by omega), midAvgCos_recur N hN, sinc_nat_mul_pi hN, sub_zero, ← pow_mul,
      mul_comm (N + 1) 2, pow_mul]
    simp
  rw [← hterm]
  exact Finset.single_le_sum (f := fun k' => m * (a k' ^ 2 + b k' ^ 2) / 2 *
    (midAvgCos N (k' * recurTime N k) - sinc (k' * recurTime N k)) ^ 2)
    (fun k' _ => by positivity) (Finset.mem_range.mpr (by omega : k < K + 1))

end Recurrence

/-! ### Equal memory -/

section Memory

/-- Memory of a rank-`r` factorisation `U S Vᵀ` on `m` cells and `n` angles: `r (m + n)`. -/
def dlraMemory (r m n : ℕ) : ℕ := r * (m + n)

/-- Memory of the full discrete-ordinates solution on `m` cells and `N` angles: `m N`. -/
def snMemory (m N : ℕ) : ℕ := m * N

/-- The number of angles a rank-`r` DLRA can afford at the memory of `S_N`: `⌊m N / r⌋ - m`. -/
def affordableAngles (m N r : ℕ) : ℕ := m * N / r - m

theorem dlraMemory_affordable_le {m N r : ℕ} (hr : 0 < r) (hrN : r ≤ N) :
    dlraMemory r m (affordableAngles m N r) ≤ snMemory m N := by
  unfold dlraMemory snMemory affordableAngles
  have h1 : m ≤ m * N / r := by
    rw [Nat.le_div_iff_mul_le hr]; exact Nat.mul_le_mul_left m hrN
  rw [Nat.add_sub_cancel' h1]
  exact Nat.mul_div_le (m * N) r

/-- For `N ≥ 2r + 1` angles and `m ≥ 2r` cells, rank `r` affords more than `N` angles. -/
theorem lt_affordableAngles {m N r : ℕ} (hr : 0 < r) (hm : 2 * r ≤ m) (hN : 2 * r + 1 ≤ N) :
    N < affordableAngles m N r := by
  unfold affordableAngles
  have h : N + m + 1 ≤ m * N / r := by
    rw [Nat.le_div_iff_mul_le hr]
    have h1 : (2 * r : ℤ) ≤ m := by exact_mod_cast hm
    have h2 : (2 * r + 1 : ℤ) ≤ N := by exact_mod_cast hN
    have h3 : (0 : ℤ) ≤ r := by exact_mod_cast hr.le
    have : ((N : ℤ) + m + 1) * r ≤ m * N := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2),
        mul_nonneg h3 (sub_nonneg.mpr h1)]
    exact_mod_cast this
  omega

variable {m N n k : ℕ} [NeZero m]

/-- **Rank versus angular resolution at equal memory, free streaming.**  Data `cos(k x) ⊗ 1`
with `2k < m`.  Let `N ≥ 1` ordinates be the full method and `n > N` the angular grid of the
rank-two DLRA.  Then, for all `t`, the `n`-ordinate solution has rank `≤ 2` (so the rank-two
DLRA with `n` angles is exact and costs `2(m + n)`), and at the recurrence time `t_N = N π / k`
of the full method: (i) the `l²` error of the `S_N` scalar flux equals the `l²` norm of the
initial flux (relative error one); (ii) the DLRA scalar flux equals the exact flux; (iii) before
its own recurrence, `0 < t ≤ n π / (2k)`, the DLRA flux error is at most `π k t / (12 n²)`.
OP-OT-58. -/
theorem equal_memory_free_streaming (hk0 : 0 < k) (hk : 2 * k < m) (hN : N ≠ 0) (hNn : N < n) :
    (∀ t : ℝ, (snSol m n k (pureMode k) (fun _ => 0) t).rank ≤ 2) ∧
    (∑ i : ZMod m, (flux (snSol m N k (pureMode k) (fun _ => 0) (recurTime N k)) i -
        exactFlux k (pureMode k) (fun _ => 0) (recurTime N k) (xGrid m i)) ^ 2 = m / 2 ∧
      ∑ i : ZMod m, (flux (snSol m N k (pureMode k) (fun _ => 0) 0) i) ^ 2 = m / 2) ∧
    (∀ i : ZMod m, flux (snSol m n k (pureMode k) (fun _ => 0) (recurTime N k)) i =
      exactFlux k (pureMode k) (fun _ => 0) (recurTime N k) (xGrid m i)) ∧
    (∀ t : ℝ, 0 < t → k * t ≤ n * π / 2 → ∀ i : ZMod m,
      |flux (snSol m n k (pureMode k) (fun _ => 0) t) i -
        exactFlux k (pureMode k) (fun _ => 0) t (xGrid m i)| ≤ π * k * t / (12 * n ^ 2)) := by
  have hk' : k ≠ 0 := by omega
  have hn : n ≠ 0 := by omega
  refine ⟨fun t => rank_snSol_pureMode_le n k t, ⟨sum_sq_err_recur_eq hk0 hk hN, ?_⟩, fun i => ?_,
    fun t ht hkt i => ?_⟩
  · simp_rw [flux_snSol_pureMode_zero hN]
    exact sum_sq_cos_grid hk0 hk
  · rw [flux_snSol_fine_recur hN hNn hk', exactFlux_recur hN hk']
  · refine (abs_flux_sub_exactFlux_le hn k (pureMode k) (fun _ => 0) ht hkt i).trans (le_of_eq ?_)
    have hsum : ∑ k' ∈ range (k + 1), (|pureMode k k'| + |(fun _ : ℕ => (0 : ℝ)) k'|) * k' = k := by
      rw [Finset.sum_eq_single k]
      · simp [pureMode]
      · intro k' _ hk'; simp [pureMode, hk']
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    rw [hsum]
    ring

/-- `equal_memory_free_streaming` with the affordable number of angles `n = ⌊m N / 2⌋ - m`, for
`N ≥ 5` and `m ≥ 4`: the DLRA uses no more memory than `S_N`. -/
theorem equal_memory_free_streaming' (hk0 : 0 < k) (hk : 2 * k < m) (hN : 5 ≤ N)
    (hm : 4 ≤ m) :
    dlraMemory 2 m (affordableAngles m N 2) ≤ snMemory m N ∧
    (∀ t : ℝ, (snSol m (affordableAngles m N 2) k (pureMode k) (fun _ => 0) t).rank ≤ 2) ∧
    (∑ i : ZMod m, (flux (snSol m N k (pureMode k) (fun _ => 0) (recurTime N k)) i -
        exactFlux k (pureMode k) (fun _ => 0) (recurTime N k) (xGrid m i)) ^ 2 = m / 2 ∧
      ∑ i : ZMod m, (flux (snSol m N k (pureMode k) (fun _ => 0) 0) i) ^ 2 = m / 2) ∧
    (∀ i : ZMod m, flux (snSol m (affordableAngles m N 2) k (pureMode k) (fun _ => 0)
        (recurTime N k)) i =
      exactFlux k (pureMode k) (fun _ => 0) (recurTime N k) (xGrid m i)) := by
  obtain ⟨h1, h2, h3, _⟩ := equal_memory_free_streaming (n := affordableAngles m N 2) hk0 hk
    (by omega) (lt_affordableAngles (by norm_num) hm hN)
  exact ⟨dlraMemory_affordable_le (by norm_num) (by omega), h1, h2, h3⟩

/-- **Rank versus angular resolution at equal memory, general band-limited data.**  Data `g ⊗ 1`
with `K` spatial modes, `2K < m`; `N ≥ 1` ordinates for the full method, `n > N` for the angular
grid of the rank-`(2K+1)` DLRA.  Then (i) the `n`-ordinate solution has rank `≤ 2K + 1` for all
`t` (exactly `2K + 1` at `t = π` when all modes are present, `rank_snSol_pi`); (ii) at the
recurrence time `N π / k` of any mode `1 ≤ k ≤ K`, the squared `l²` error of the `S_N` flux is at
least `(m/2)(a_k² + b_k²)`; (iii) before its own recurrence, `0 < t ≤ n π / (2K)`, the DLRA flux
error is at most `(∑_k (|a_k| + |b_k|) k) π t / (12 n²)` pointwise; (iv) at `N π / k` the mode `k`
drops out of the DLRA error altogether.  `affordable_modes` gives `n` with
`(2K+1)(m+n) ≤ m N` and `n > N`.  OP-OT-58. -/
theorem equal_memory_modes {K : ℕ} (hK : 2 * K < m) (hN : N ≠ 0) (hNn : N < n) (a b : ℕ → ℝ) :
    (∀ t : ℝ, (snSol m n K a b t).rank ≤ 2 * K + 1) ∧
    (∀ k, 0 < k → k ≤ K → m * (a k ^ 2 + b k ^ 2) / 2 ≤
      ∑ i : ZMod m, (flux (snSol m N K a b (recurTime N k)) i -
        exactFlux K a b (recurTime N k) (xGrid m i)) ^ 2) ∧
    (∀ t : ℝ, 0 < t → K * t ≤ n * π / 2 → ∀ i : ZMod m,
      |flux (snSol m n K a b t) i - exactFlux K a b t (xGrid m i)| ≤
        (∑ k ∈ range (K + 1), (|a k| + |b k|) * k) * (π * t / (12 * n ^ 2))) ∧
    (∀ k, 0 < k → k ≤ K →
      ∑ i : ZMod m, (flux (snSol m n K a b (recurTime N k)) i -
        exactFlux K a b (recurTime N k) (xGrid m i)) ^ 2 =
      ∑ k' ∈ (range (K + 1)).erase k, m * (a k' ^ 2 + b k' ^ 2) / 2 *
        (midAvgCos n (k' * recurTime N k) - sinc (k' * recurTime N k)) ^ 2) := by
  have hn : n ≠ 0 := by omega
  refine ⟨fun t => rank_snSol_le K a b t, fun k hk0 hkK => le_sum_sq_err_recur hN hK a b hk0 hkK,
    fun t ht hKt i => abs_flux_sub_exactFlux_le hn K a b ht hKt i, fun k hk0 hkK => ?_⟩
  rw [sum_sq_flux_sub_exact hn hK]
  refine (Finset.sum_erase _ ?_).symm
  have hk' : k ≠ 0 := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hNn' : (N : ℝ) < n := by exact_mod_cast hNn
  have hsin : sin ((N : ℝ) * π / n) ≠ 0 := by
    refine (sin_pos_of_pos_of_lt_pi (by positivity) ?_).ne'
    rw [div_lt_iff₀ hn']
    nlinarith [pi_pos]
  rw [k_mul_recurTime hk', midAvgCos_eq_zero n hn (sin_nat_mul_pi N) hsin, sinc_nat_mul_pi hN]
  ring

/-- The affordable angle count for rank `2K + 1`: for `m ≥ 4K + 2` cells and `N ≥ 4K + 3`
ordinates, `n = ⌊m N / (2K+1)⌋ - m` satisfies `(2K+1)(m + n) ≤ m N` and `n > N`. -/
theorem affordable_modes {m N K : ℕ} (hm : 4 * K + 2 ≤ m) (hN : 4 * K + 3 ≤ N) :
    dlraMemory (2 * K + 1) m (affordableAngles m N (2 * K + 1)) ≤ snMemory m N ∧
      N < affordableAngles m N (2 * K + 1) :=
  ⟨dlraMemory_affordable_le (by omega) (by omega),
    lt_affordableAngles (by omega) (by omega) (by omega)⟩

end Memory

/-! ### The scattering-dominated limit: collide–stream -/

section Scattering

variable {m N : ℕ} [NeZero m]

/-- **One collide–stream step on the Fourier coefficients.**  Isotropic data `g ⊗ 1` with
`g = ∑_k a_k cos kx + b_k sin kx` streams freely for a time `Δt` (the matrix `snSol m N K a b Δt`)
and is then fully re-isotropised (`σ Δt → ∞`): the new data is `flux(snSol) ⊗ 1`, whose
coefficients are `a_k c_k, b_k c_k` with `c_k = midAvgCos N (k Δt)`. -/
noncomputable def csStep (N : ℕ) (Δt : ℝ) (ab : (ℕ → ℝ) × (ℕ → ℝ)) : (ℕ → ℝ) × (ℕ → ℝ) :=
  (fun k => ab.1 k * midAvgCos N (k * Δt), fun k => ab.2 k * midAvgCos N (k * Δt))

/-- The same step with the exact angular average `sinc(k Δt)` in place of the midpoint rule. -/
noncomputable def csStepExact (Δt : ℝ) (ab : (ℕ → ℝ) × (ℕ → ℝ)) : (ℕ → ℝ) × (ℕ → ℝ) :=
  (fun k => ab.1 k * sinc (k * Δt), fun k => ab.2 k * sinc (k * Δt))

/-- The coefficient step is the relaxed flux of the streamed matrix: `csStep` *is* the
collide–stream scheme on the grid. -/
theorem trigPoly_csStep (hN : N ≠ 0) (K : ℕ) (a b : ℕ → ℝ) (Δt : ℝ) (i : ZMod m) :
    trigPoly K (csStep N Δt (a, b)).1 (csStep N Δt (a, b)).2 (xGrid m i) =
      flux (snSol m N K a b Δt) i := by
  rw [flux_snSol hN]
  unfold trigPoly csStep
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- The exact step is the exact angular average of the streamed data. -/
theorem trigPoly_csStepExact (K : ℕ) (a b : ℕ → ℝ) (Δt x : ℝ) :
    trigPoly K (csStepExact Δt (a, b)).1 (csStepExact Δt (a, b)).2 x = exactFlux K a b Δt x := by
  unfold trigPoly csStepExact exactFlux
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem csStep_iterate (N : ℕ) (Δt : ℝ) (ab : (ℕ → ℝ) × (ℕ → ℝ)) (j : ℕ) :
    (csStep N Δt)^[j] ab =
      (fun k => ab.1 k * midAvgCos N (k * Δt) ^ j, fun k => ab.2 k * midAvgCos N (k * Δt) ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    unfold csStep
    simp only [pow_succ, mul_assoc]

theorem csStepExact_iterate (Δt : ℝ) (ab : (ℕ → ℝ) × (ℕ → ℝ)) (j : ℕ) :
    (csStepExact Δt)^[j] ab =
      (fun k => ab.1 k * sinc (k * Δt) ^ j, fun k => ab.2 k * sinc (k * Δt) ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    unfold csStepExact
    simp only [pow_succ, mul_assoc]

theorem abs_midAvgCos_le_one (N : ℕ) (s : ℝ) : |midAvgCos N s| ≤ 1 := by
  unfold midAvgCos
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [abs_div, abs_of_pos hN', div_le_one hN']
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j : Fin N, |cos (s * vGrid (midV₀ N) (midΔv N) j)| ≤ ∑ _j : Fin N, (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => abs_cos_le_one _
    _ = N := by simp

theorem abs_sinc_le_one (s : ℝ) : |sinc s| ≤ 1 := by
  by_cases hs : s = 0
  · subst hs; simp [sinc_zero]
  · rw [sinc_of_ne hs, abs_div, div_le_one (abs_pos.mpr hs)]
    exact abs_sin_le_abs

theorem abs_pow_sub_pow_le {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (j : ℕ) :
    |x ^ j - y ^ j| ≤ j * |x - y| := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : x ^ (j + 1) - y ^ (j + 1) = (x ^ j - y ^ j) * x + y ^ j * (x - y) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_pow]
    have h1 : |x ^ j - y ^ j| * |x| ≤ j * |x - y| :=
      (mul_le_of_le_one_right (abs_nonneg _) hx).trans ih
    have h2 : |y| ^ j * |x - y| ≤ |x - y| :=
      mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hy)
    push_cast
    linarith

omit [NeZero m] in
/-- **Scattering removes the recurrence.**  In the collide–stream scheme with step `Δt` and
`K Δt ≤ N π / 2`, the `S_N` scalar flux after `j` steps differs from the exact one by at most
`(∑_k (|a_k| + |b_k|) k) · π (j Δt) / (12 N²)` for **every** `j`: the per-step quadrature error is
the same as in free streaming, but the errors add instead of recombining coherently, and the
free-streaming failure at `t = N π / k` (`sum_sq_err_recur`) does not occur.  The solution is
isotropic after each step, so rank one is exact and the memory question is void. -/
theorem abs_cs_sub_exact_le (hN : N ≠ 0) (K : ℕ) (a b : ℕ → ℝ) {Δt : ℝ} (hΔt : 0 < Δt)
    (hKΔt : K * Δt ≤ N * π / 2) (j : ℕ) (i : ZMod m) :
    |trigPoly K ((csStep N Δt)^[j] (a, b)).1 ((csStep N Δt)^[j] (a, b)).2 (xGrid m i) -
      trigPoly K ((csStepExact Δt)^[j] (a, b)).1 ((csStepExact Δt)^[j] (a, b)).2 (xGrid m i)| ≤
      (∑ k ∈ range (K + 1), (|a k| + |b k|) * k) * (π * (j * Δt) / (12 * N ^ 2)) := by
  rw [csStep_iterate, csStepExact_iterate]
  unfold trigPoly
  simp only
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  have hk : (k : ℝ) ≤ K := by
    have := Finset.mem_range.mp hk; exact_mod_cast (by omega : k ≤ K)
  have e : a k * midAvgCos N (k * Δt) ^ j * cos (k * xGrid m i) +
      b k * midAvgCos N (k * Δt) ^ j * sin (k * xGrid m i) -
      (a k * sinc (k * Δt) ^ j * cos (k * xGrid m i) +
        b k * sinc (k * Δt) ^ j * sin (k * xGrid m i)) =
      (a k * cos (k * xGrid m i) + b k * sin (k * xGrid m i)) *
        (midAvgCos N (k * Δt) ^ j - sinc (k * Δt) ^ j) := by ring
  rw [e, abs_mul]
  have h1 : |a k * cos (k * xGrid m i) + b k * sin (k * xGrid m i)| ≤ |a k| + |b k| :=
    (abs_add_le _ _).trans (add_le_add
      (by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _))
      (by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (abs_sin_le_one _)))
  have h2 : |midAvgCos N (k * Δt) ^ j - sinc (k * Δt) ^ j| ≤ k * (π * (j * Δt) / (12 * N ^ 2)) := by
    refine (abs_pow_sub_pow_le (abs_midAvgCos_le_one N _) (abs_sinc_le_one _) j).trans ?_
    have h3 : |midAvgCos N (k * Δt) - sinc (k * Δt)| ≤ k * (π * Δt / (12 * N ^ 2)) := by
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0; simp [midAvgCos_zero N hN, sinc_zero]
      · have hkt : 0 < (k : ℝ) * Δt := mul_pos (by exact_mod_cast hk0) hΔt
        have hkt' : (k : ℝ) * Δt ≤ N * π / 2 :=
          le_trans (mul_le_mul_of_nonneg_right hk hΔt.le) hKΔt
        refine (abs_midAvgCos_sub_sinc_le N hN hkt hkt').trans (le_of_eq ?_)
        ring
    calc (j : ℝ) * |midAvgCos N (k * Δt) - sinc (k * Δt)| ≤ j * (k * (π * Δt / (12 * N ^ 2))) :=
          mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg j)
      _ = k * (π * (j * Δt) / (12 * N ^ 2)) := by ring
  calc |a k * cos (k * xGrid m i) + b k * sin (k * xGrid m i)| *
        |midAvgCos N (k * Δt) ^ j - sinc (k * Δt) ^ j| ≤
        (|a k| + |b k|) * (k * (π * (j * Δt) / (12 * N ^ 2))) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = (|a k| + |b k|) * k * (π * (j * Δt) / (12 * N ^ 2)) := by ring

end Scattering





end LeanDLRA.Novel.OpOT58
