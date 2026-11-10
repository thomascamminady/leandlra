import LeanDLRA.Foundations.Projector
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Kinetic.Defs

/-!
# Results of arXiv 2601.11900: Separable AP DLR method for Vlasov–Poisson–Fokker–Planck

This module formalizes Sections 3 and 5 of Zhang and Hu for the actual 1D1V discretization, not an
abstract core: the grid (`Grid`), the normalized discrete Maxwellian (`maxw`) and the flux form
(3.2)–(3.3) of the Fokker–Planck operator (`Lh`), with its separable stencil (`sqrt_maxw_div`,
`Lh_stencil`, `Lh_eq_tensor`), its mass conservation and kernel (`density_Lh`, `Lh_rhoM`), the
discrete coercivity with the sharp constant `γ_h` (`coercivity`, Prop. 5.1, resting on the sharp
Neumann Poincaré inequality `neumann_poincare`), the bound on the normal component
(`fluctuation_bound`, Prop. 5.2), and the AP estimates (`ap_property`, Thm 5.3, and
`ap_constant_field`, Remark 5.4).  One step of Algorithm 1 is the predicate `IsIMEXStep`, with the
factored K-, S- and L-steps (4.4)–(4.6), the density prediction (4.3) and a Poisson map; for it we
prove the AP estimates (`IsIMEXStep.ap`) and the exact cancellation of the stiff term by the
explicit S-step (`IsIMEXStep.stiff_cancel`).  Further: the separable projections (3.7)–(3.9)
(`kProjection_separable`, `sProjection_separable`, `lProjection_separable`) and the density update
(4.2) (`density_imex`).

## Differences from the paper

* **The constant quoted for Thm 5.3 in the list this slice started from is false.**  That list has
  `√(M_max L_v)` where the paper, in both arXiv versions, has `M_max √L_v`.  The paper's statement
  is true and is `ap_property`.  The quoted one holds for `L_v ≥ 1` (`ap_property_header`) and fails
  in general (`header_constant_false`).  The paper's constant can be improved to `√M_max`
  (`ap_property_sharp`).  No claim of the paper itself was found to be false.
* Indices: velocity nodes are `0, …, N_v - 1`, so `G.v q` is the paper's `v_{q+1}` and `alpha G i`
  is the coefficient between the nodes `i` and `i + 1`.  Grid functions are matrices with rows
  indexed by position, and basis functions are columns, so `f = X S Vᵀ` and `β ⊗ 𝒯` is
  `f ↦ diag(β) f 𝒯ᵀ`.
* `M` is normalized by (5.1), as the paper assumes; the factor `(2π)^{-1/2}` of (1.4) is replaced by
  that normalization.  The zero-flux boundary, implicit in the printed stencils, is explicit in
  `flux`, `Talpha`, `TalphaInv`.
* Hypotheses left implicit in the paper are stated: `N_x ≥ 1` and `N_v ≥ 2` (so that the minima over
  the interfaces exist).
* Thm 5.3 takes the existence of `f^{n+1}` from the paper's wording, "the low-rank solution": the
  L-step is a hypothesis (`IsLStep`), as are the K-step and the S-step in `IsIMEXStep`.  The
  solvability of the linear systems in the K- and L-steps is not proved, and it is not obvious,
  because `ℒ_h` is not dissipative for the unweighted inner product (`Lh_not_dissipative`).
* `𝒜_h` is an arbitrary map, the Poisson solve an arbitrary map from densities to fields, and the
  QR factorizations are factorizations with orthonormal factors.  The estimates of Thm 5.3 hold for
  every value of `‖G^{n+1}‖`; that this is `𝒪(1)` is the paper's formal assumption and is not
  proved here, nor is the coupled Vlasov–Poisson analysis, which Remark 5.5 leaves open.
* Not formalized: the second-order Algorithm 2 and the higher-dimensional case, neither of which is
  listed for this slice, and a stability theorem for Algorithm 1 with the true operator `ℒ_h`, which
  the paper does not claim.  The library's abstract `hybridKSL_norm_le_perturbed` covers dissipative
  operators, and that hypothesis fails for `ℒ_h`.

Non-vacuity: `exists_isIMEXStep` for Algorithm 1 and `header_constant_false`, which contains an
instance of all hypotheses of Thm 5.3 with a nonconstant field.  The library contained no earlier
proof of a listed result; it has abstract statements citing this paper only.

## Core vocabulary

`Grid.toPhaseGrid` is the grid as a core `Kinetic.PhaseGrid` of `LeanDLRA/Kinetic/Defs.lean` (the
cell sizes `Δx`, `Δv` as weights; the velocity weights have total mass `L_v`, not one), and
`density_eq_kinetic` writes the density of this file as the core `Kinetic.density` with the
weights `Δv`. The weighted inner products `ipX`, `ipV`, `ipXV` are definitions of this file.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2601_11900

/-- Abel summation for a flux vanishing at the left boundary. -/
lemma sum_flux_mul (J w : ℕ → ℝ) (h0 : J 0 = 0) (n : ℕ) :
    ∑ q ∈ range (n + 1), (J (q + 1) - J q) * w q
      = J (n + 1) * w n - ∑ i ∈ range n, J (i + 1) * (w (i + 1) - w i) := by
  induction n with
  | zero => simp [h0]
  | succ n ih => rw [sum_range_succ, ih, sum_range_succ]; ring

/-- arXiv 2601.11900, the discrete Poincaré inequality used in Prop. 5.1, first step: the discrete
Wirtinger inequality with Dirichlet ends, by the ground-state (Picone) substitution
`φ k = sin (k π / N)`.  The paper takes the inequality as known. -/
theorem wirtinger_dirichlet {N : ℕ} (hN : 0 < N) (y : ℕ → ℝ) (h0 : y 0 = 0) (hNy : y N = 0) :
    (2 - 2 * Real.cos (Real.pi / N)) * ∑ i ∈ range N, y i ^ 2
      ≤ ∑ i ∈ range N, (y (i + 1) - y i) ^ 2 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set θ : ℝ := Real.pi / N with hθ
  set c : ℝ := 2 - 2 * Real.cos θ with hc
  set φ : ℕ → ℝ := fun k => Real.sin (k * θ) with hφdef
  have hφ0 : φ 0 = 0 := by simp [hφdef]
  have hφN : φ N = 0 := by
    simp only [hφdef, hθ]
    rw [mul_div_cancel₀ _ hNR.ne', Real.sin_pi]
  have hφpos : ∀ k, 0 < k → k < N → 0 < φ k := by
    intro k hk hkN
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have hkN' : (k : ℝ) < N := by exact_mod_cast hkN
    apply Real.sin_pos_of_pos_of_lt_pi (mul_pos hk' (div_pos Real.pi_pos hNR))
    rw [← mul_div_assoc, div_lt_iff₀ hNR]
    nlinarith [Real.pi_pos]
  have hrec : ∀ k : ℕ, φ (k + 2) + φ k = 2 * Real.cos θ * φ (k + 1) := by
    intro k
    simp only [hφdef]
    have e1 : ((k + 2 : ℕ) : ℝ) * θ = ((k + 1 : ℕ) : ℝ) * θ + θ := by push_cast; ring
    have e2 : (k : ℝ) * θ = ((k + 1 : ℕ) : ℝ) * θ - θ := by push_cast; ring
    rw [e1, e2, Real.sin_add, Real.sin_sub]
    ring
  have key : ∀ m : ℕ, m + 1 < N →
      (1 - φ m / φ (m + 1)) * y (m + 1) ^ 2
        ≤ ∑ i ∈ range (m + 1), (y (i + 1) - y i) ^ 2 - c * ∑ i ∈ range (m + 1), y i ^ 2 := by
    intro m
    induction m with
    | zero =>
      intro _
      simp [hφ0, h0]
    | succ m ih =>
      intro hm
      have ih' := ih (by omega)
      have hp1 : 0 < φ (m + 1) := hφpos _ (by omega) (by omega)
      have hp2 : 0 < φ (m + 2) := hφpos _ (by omega) (by omega)
      rw [sum_range_succ _ (m + 1), sum_range_succ _ (m + 1)]
      set a := y (m + 1) with ha
      set b := y (m + 2) with hb
      have hr : φ m / φ (m + 1) = 2 * Real.cos θ - φ (m + 2) / φ (m + 1) := by
        have := hrec m
        field_simp
        linarith
      rw [hr] at ih'
      have hsq : 0 ≤ (φ (m + 2) * a - φ (m + 1) * b) ^ 2 / (φ (m + 1) * φ (m + 2)) := by
        positivity
      have hid : (φ (m + 2) * a - φ (m + 1) * b) ^ 2 / (φ (m + 1) * φ (m + 2))
          = φ (m + 2) / φ (m + 1) * a ^ 2 - 2 * a * b + φ (m + 1) / φ (m + 2) * b ^ 2 := by
        field_simp
        ring
      rw [hid] at hsq
      have hsplit : (1 - φ (m + 1) / φ (m + 2)) * b ^ 2 ≤
          ∑ x ∈ range (m + 1), (y (x + 1) - y x) ^ 2 + (b - a) ^ 2 -
            c * (∑ x ∈ range (m + 1), y x ^ 2 + a ^ 2) := by
        simp only [hc] at ih' ⊢
        nlinarith [ih', hsq]
      exact hsplit
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  cases n with
  | zero => simp [h0, hNy]
  | succ m =>
    have hk := key m (by omega)
    have hp1 : 0 < φ (m + 1) := hφpos _ (by omega) (by omega)
    have hr : φ m / φ (m + 1) = 2 * Real.cos θ := by
      have := hrec m
      rw [hφN] at this
      field_simp
      linarith
    rw [hr] at hk
    rw [sum_range_succ _ (m + 1), sum_range_succ _ (m + 1), hNy]
    simp only [hc] at hk ⊢
    nlinarith [hk]

/-- arXiv 2601.11900, the discrete Poincaré inequality `𝒟(u) ≥ λ_N ‖u - ū‖²` used in Prop. 5.1, in
the sharp form: `4 sin² (π / 2N)` is the first nonzero eigenvalue of the Laplacian of the path with
`N` nodes.  The paper takes the inequality as known.  The proof passes to the partial sums of
`w - w̄`, which vanish at both ends, and applies `wirtinger_dirichlet`. -/
theorem neumann_poincare {N : ℕ} (hN : 0 < N) (w : ℕ → ℝ) :
    4 * Real.sin (Real.pi / (2 * N)) ^ 2 *
        ∑ q ∈ range N, (w q - (∑ q ∈ range N, w q) / N) ^ 2
      ≤ ∑ i ∈ range (N - 1), (w (i + 1) - w i) ^ 2 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set wbar : ℝ := (∑ q ∈ range N, w q) / N with hwbar
  set z : ℕ → ℝ := fun q => w q - wbar with hz
  set y : ℕ → ℝ := fun k => ∑ q ∈ range k, z q with hy
  have hsum : ∑ q ∈ range N, z q = 0 := by
    simp only [hz, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, hwbar]
    field_simp
    ring
  have hy0 : y 0 = 0 := by simp [hy]
  have hyN : y N = 0 := hsum
  have hdiff : ∀ i, y (i + 1) - y i = z i := by
    intro i
    simp [hy, sum_range_succ]
  have hmu : 2 - 2 * Real.cos (Real.pi / N) = 4 * Real.sin (Real.pi / (2 * N)) ^ 2 := by
    have : Real.pi / N = 2 * (Real.pi / (2 * N)) := by field_simp
    rw [this, Real.cos_two_mul, Real.cos_sq']
    ring
  have hW := wirtinger_dirichlet hN y hy0 hyN
  rw [hmu] at hW
  simp only [hdiff] at hW
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  -- summation by parts
  have hparts : ∑ q ∈ range (n + 1), z q ^ 2 = - ∑ i ∈ range n, y (i + 1) * (z (i + 1) - z i) := by
    have := sum_flux_mul y z hy0 n
    rw [hyN] at this
    simp only [hdiff, zero_mul, zero_sub] at this
    rw [← this]
    exact sum_congr rfl fun q _ => by ring
  set Z := ∑ q ∈ range (n + 1), z q ^ 2 with hZ
  set D := ∑ i ∈ range n, (w (i + 1) - w i) ^ 2 with hD
  set Y := ∑ i ∈ range (n + 1), y i ^ 2 with hYdef
  set μ := 4 * Real.sin (Real.pi / (2 * ((n + 1 : ℕ) : ℝ))) ^ 2 with hμ
  have hDz : ∀ i, z (i + 1) - z i = w (i + 1) - w i := by
    intro i
    simp only [hz]
    ring
  have hμ0 : 0 ≤ μ := by positivity
  have hZ0 : 0 ≤ Z := sum_nonneg fun _ _ => sq_nonneg _
  have hD0 : 0 ≤ D := sum_nonneg fun _ _ => sq_nonneg _
  have hY1 : ∑ i ∈ range n, y (i + 1) ^ 2 ≤ Y := by
    rw [hYdef, sum_range_succ']
    have : 0 ≤ y 0 ^ 2 := sq_nonneg _
    linarith
  have hCS : Z ^ 2 ≤ Y * D := by
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq (range n) (fun i => y (i + 1))
      (fun i => w (i + 1) - w i)
    have h2 : Z = - ∑ i ∈ range n, y (i + 1) * (w (i + 1) - w i) := by
      rw [hparts]; simp only [hDz]
    calc Z ^ 2 = (∑ i ∈ range n, y (i + 1) * (w (i + 1) - w i)) ^ 2 := by rw [h2]; ring
      _ ≤ (∑ i ∈ range n, y (i + 1) ^ 2) * D := h1
      _ ≤ Y * D := by gcongr
  by_cases hZpos : Z = 0
  · rw [hZpos]
    simpa using hD0
  · have hZp : 0 < Z := lt_of_le_of_ne hZ0 (Ne.symm hZpos)
    have : Z * (μ * Z) ≤ Z * D := by
      calc Z * (μ * Z) = μ * Z ^ 2 := by ring
        _ ≤ μ * (Y * D) := by gcongr
        _ = (μ * Y) * D := by ring
        _ ≤ Z * D := by gcongr
    exact le_of_mul_le_mul_left this hZp

/-! ### The discrete setting of §3 -/

/-- The 1D1V phase-space grid of §3: `x_p = x_min + (p - 1/2) Δx`, `v_q = v_min + (q - 1/2) Δv`. -/
structure Grid (Nx Nv : ℕ) where
  /-- left end of the spatial domain -/
  xmin : ℝ
  /-- right end of the spatial domain -/
  xmax : ℝ
  /-- left end of the velocity domain -/
  vmin : ℝ
  /-- right end of the velocity domain -/
  vmax : ℝ
  x_lt : xmin < xmax
  v_lt : vmin < vmax

/-- Phase-space grid functions `f_{p,q}`. Rows are positions, columns are velocities. -/
abbrev Phase (Nx Nv : ℕ) := Matrix (Fin Nx) (Fin Nv) ℝ

namespace Grid

variable {Nx Nv : ℕ} (G : Grid Nx Nv)

/-- `Δx = (x_max - x_min) / N_x`. -/
noncomputable def dx : ℝ := (G.xmax - G.xmin) / Nx

/-- `Δv = (v_max - v_min) / N_v`. -/
noncomputable def dv : ℝ := (G.vmax - G.vmin) / Nv

/-- `L_v = v_max - v_min`. -/
def Lv : ℝ := G.vmax - G.vmin

/-- The velocity node `v_q`, with the index shifted by one: `G.v q` is the paper's `v_{q+1}`. -/
noncomputable def v (q : ℕ) : ℝ := G.vmin + ((q : ℝ) + 1 / 2) * G.dv

end Grid

section Definitions

variable {Nx Nv : ℕ} (G : Grid Nx Nv)

/-- `⟨φ, ψ⟩ₓʰ = ∑_p φ_p ψ_p Δx`. -/
noncomputable def ipX (φ ψ : Fin Nx → ℝ) : ℝ := ∑ p, φ p * ψ p * G.dx

/-- `⟨φ, ψ⟩ᵥʰ = ∑_q φ_q ψ_q Δv`. -/
noncomputable def ipV (φ ψ : Fin Nv → ℝ) : ℝ := ∑ q, φ q * ψ q * G.dv

/-- `⟨φ, ψ⟩ₓᵥʰ = ∑_{p,q} φ_{p,q} ψ_{p,q} Δx Δv`. -/
noncomputable def ipXV (φ ψ : Phase Nx Nv) : ℝ := ∑ p, ∑ q, φ p q * ψ p q * G.dx * G.dv

/-- `‖ρ‖ₓʰ`. -/
noncomputable def normX (ρ : Fin Nx → ℝ) : ℝ := Real.sqrt (ipX G ρ ρ)

/-- `‖f‖ₓᵥʰ`. -/
noncomputable def normXV (f : Phase Nx Nv) : ℝ := Real.sqrt (ipXV G f f)

/-- The density `ρ = ⟨f, 1⟩ᵥʰ`, a spatial grid function. -/
noncomputable def density (f : Phase Nx Nv) : Fin Nx → ℝ := fun p => ipV G (f p) 1

/-- The unnormalized Maxwellian `exp (-(v_q - E_p)² / 2)` of (1.4), (3.5). -/
noncomputable def gauss (E : Fin Nx → ℝ) (p : Fin Nx) (q : ℕ) : ℝ :=
  Real.exp (-(G.v q - E p) ^ 2 / 2)

/-- The discrete Maxwellian `M_{p,q}`, normalized on the velocity grid as in (5.1). -/
noncomputable def maxw (E : Fin Nx → ℝ) (p : Fin Nx) (q : ℕ) : ℝ :=
  gauss G E p q / ∑ q' : Fin Nv, gauss G E p q' * G.dv

/-- The geometric-mean interpolation `M_{p,q+1/2} = √(M_{p,q} M_{p,q+1})` of (3.3). -/
noncomputable def maxwMid (E : Fin Nx → ℝ) (p : Fin Nx) (q : ℕ) : ℝ :=
  Real.sqrt (maxw G E p q * maxw G E p (q + 1))

/-- A velocity grid function extended by zero to all of `ℕ`. -/
def extV {Nv : ℕ} (w : Fin Nv → ℝ) (q : ℕ) : ℝ := if h : q < Nv then w ⟨q, h⟩ else 0

/-- The flux of (3.3) through the interface with index `i`: interface `i + 1` separates the nodes
`i` and `i + 1`, and the interfaces `0` and `N_v` are the velocity boundary, where the flux is zero
(zero-flux boundary condition). -/
noncomputable def flux (E : Fin Nx → ℝ) (f : Phase Nx Nv) (p : Fin Nx) : ℕ → ℝ
  | 0 => 0
  | i + 1 => if i + 1 < Nv then
      maxwMid G E p i * (extV (f p) (i + 1) / maxw G E p (i + 1) - extV (f p) i / maxw G E p i) /
        G.dv
    else 0

/-- The discrete Fokker–Planck operator (3.2)–(3.3):
`[ℒ_h f]_{p,q} = (𝒥_{p,q+1/2} - 𝒥_{p,q-1/2}) / Δv`. -/
noncomputable def Lh (E : Fin Nx → ℝ) (f : Phase Nx Nv) : Phase Nx Nv :=
  Matrix.of fun p q => (flux G E f p (q + 1) - flux G E f p q) / G.dv

/-- `α_{q+1/2} = exp (Δv (v_q + v_{q+1}) / 4)` of (3.5), with the index shifted by one. -/
noncomputable def alpha (i : ℕ) : ℝ := Real.exp (G.dv * (G.v i + G.v (i + 1)) / 4)

/-- `β_p = exp (-Δv E_p / 2)` of (3.5). -/
noncomputable def beta (E : Fin Nx → ℝ) (p : Fin Nx) : ℝ := Real.exp (-(G.dv / 2 * E p))

/-- The coefficient `α_{q+1/2}` at the right interface of node `q`, zero at the boundary. -/
noncomputable def alphaR (q : ℕ) : ℝ := if q + 1 < Nv then alpha G q else 0

/-- The coefficient `α_{q-1/2}` at the left interface of node `q`, zero at the boundary. -/
noncomputable def alphaL (q : ℕ) : ℝ := if 0 < q then alpha G (q - 1) else 0

/-- The velocity operator `(𝒯^{(α)} w)_q = (α_{q+1/2} w_{q+1} - α_{q-1/2} w_q) / Δv²` of the proof
of Prop. 5.2, as a matrix.  At the boundary the terms across the boundary are absent. -/
noncomputable def Talpha : Matrix (Fin Nv) (Fin Nv) ℝ :=
  Matrix.of fun q q' =>
    ((if (q' : ℕ) = q + 1 then alphaR G q else 0) - (if (q' : ℕ) = q then alphaL G q else 0)) /
      G.dv ^ 2

/-- The velocity operator `(𝒯^{(1/α)} w)_q = (α_{q-1/2}⁻¹ w_{q-1} - α_{q+1/2}⁻¹ w_q) / Δv²` of the
proof of Prop. 5.2, as a matrix.  At the boundary the terms across the boundary are absent, which
the convention `0⁻¹ = 0` does automatically. -/
noncomputable def TalphaInv : Matrix (Fin Nv) (Fin Nv) ℝ :=
  Matrix.of fun q q' =>
    ((if (q' : ℕ) = q - 1 then (alphaL G q)⁻¹ else 0) -
      (if (q' : ℕ) = q then (alphaR G q)⁻¹ else 0)) / G.dv ^ 2

end Definitions

section Stencil

variable {Nx Nv : ℕ} (G : Grid Nx Nv) (E : Fin Nx → ℝ)

lemma dv_pos (hNv : 0 < Nv) : 0 < G.dv := by
  have : (0 : ℝ) < Nv := by exact_mod_cast hNv
  exact div_pos (sub_pos.2 G.v_lt) this

lemma dx_pos (hNx : 0 < Nx) : 0 < G.dx := by
  have : (0 : ℝ) < Nx := by exact_mod_cast hNx
  exact div_pos (sub_pos.2 G.x_lt) this

lemma Lv_pos : 0 < G.Lv := sub_pos.2 G.v_lt

lemma Lv_eq (hNv : 0 < Nv) : G.Lv = Nv * G.dv := by
  have : (Nv : ℝ) ≠ 0 := by exact_mod_cast hNv.ne'
  simp only [Grid.Lv, Grid.dv]
  field_simp

lemma v_succ (q : ℕ) : G.v (q + 1) = G.v q + G.dv := by
  simp only [Grid.v]
  push_cast
  ring

lemma gauss_pos (p : Fin Nx) (q : ℕ) : 0 < gauss G E p q := Real.exp_pos _

lemma normalizer_pos (hNv : 0 < Nv) (p : Fin Nx) : 0 < ∑ q' : Fin Nv, gauss G E p q' * G.dv := by
  have : Nonempty (Fin Nv) := ⟨⟨0, hNv⟩⟩
  exact Finset.sum_pos (fun q _ => mul_pos (gauss_pos G E p q) (dv_pos G hNv)) Finset.univ_nonempty

lemma maxw_pos (hNv : 0 < Nv) (p : Fin Nx) (q : ℕ) : 0 < maxw G E p q :=
  div_pos (gauss_pos G E p q) (normalizer_pos G E hNv p)

lemma alpha_pos (i : ℕ) : 0 < alpha G i := Real.exp_pos _

lemma beta_pos (p : Fin Nx) : 0 < beta G E p := Real.exp_pos _

/-- arXiv 2601.11900, the normalization (5.1) `⟨M, 1⟩ᵥʰ = 1`, which holds by the definition of
`maxw`. -/
theorem sum_maxw (hNv : 0 < Nv) (p : Fin Nx) : ∑ q : Fin Nv, maxw G E p q * G.dv = 1 := by
  have h := (normalizer_pos G E hNv p).ne'
  simp only [maxw, div_mul_eq_mul_div, ← Finset.sum_div]
  exact div_self h

/-- The computation behind (3.5): `M_{p,q} = (α_{q+1/2} β_p)² M_{p,q+1}`. -/
lemma maxw_ratio (p : Fin Nx) (q : ℕ) :
    maxw G E p q = (alpha G q * beta G E p) ^ 2 * maxw G E p (q + 1) := by
  have hexp : ∀ a b c : ℝ,
      (Real.exp a * Real.exp b) ^ 2 * Real.exp c = Real.exp (a + b + (a + b) + c) := by
    intro a b c
    rw [Real.exp_add (a + b + (a + b)), Real.exp_add (a + b), Real.exp_add a b]
    ring
  simp only [maxw, gauss, alpha, beta]
  rw [← mul_div_assoc, hexp]
  congr 2
  rw [v_succ]
  ring

/-- arXiv 2601.11900, (3.5): `√(M_{p,q} / M_{p,q+1}) = α_{q+1/2} β_p`. -/
theorem sqrt_maxw_div (hNv : 0 < Nv) (p : Fin Nx) (q : ℕ) :
    Real.sqrt (maxw G E p q / maxw G E p (q + 1)) = alpha G q * beta G E p := by
  have h := (maxw_pos G E hNv p (q + 1)).ne'
  rw [maxw_ratio G E p q, mul_div_assoc, div_self h, mul_one,
    Real.sqrt_sq (mul_pos (alpha_pos G q) (beta_pos G E p)).le]

lemma maxwMid_div_right (hNv : 0 < Nv) (p : Fin Nx) (q : ℕ) :
    maxwMid G E p q / maxw G E p (q + 1) = alpha G q * beta G E p := by
  have hM := maxw_pos G E hNv p (q + 1)
  have hab := mul_pos (alpha_pos G q) (beta_pos G E p)
  rw [maxwMid, maxw_ratio G E p q, show (alpha G q * beta G E p) ^ 2 * maxw G E p (q + 1) *
      maxw G E p (q + 1) = (alpha G q * beta G E p * maxw G E p (q + 1)) ^ 2 by ring,
    Real.sqrt_sq (mul_pos hab hM).le, mul_div_assoc, div_self hM.ne', mul_one]

lemma maxwMid_div_left (hNv : 0 < Nv) (p : Fin Nx) (q : ℕ) :
    maxwMid G E p q / maxw G E p q = (alpha G q * beta G E p)⁻¹ := by
  have hM := maxw_pos G E hNv p (q + 1)
  have hab := mul_pos (alpha_pos G q) (beta_pos G E p)
  have h := maxwMid_div_right G E hNv p q
  have hmid : maxwMid G E p q = alpha G q * beta G E p * maxw G E p (q + 1) := by
    rw [← h]; field_simp
  rw [hmid, maxw_ratio G E p q]
  field_simp

lemma extV_coe (w : Fin Nv → ℝ) (q : Fin Nv) : extV w q = w q := by
  simp [extV]

lemma extV_of_le (w : Fin Nv → ℝ) {q : ℕ} (h : Nv ≤ q) : extV w q = 0 := by
  simp [extV, not_lt.2 h]

/-- The right flux in stencil form. -/
lemma flux_succ (hNv : 0 < Nv) (f : Phase Nx Nv) (p : Fin Nx) (q : ℕ) :
    flux G E f p (q + 1) = (alphaR G q * beta G E p * extV (f p) (q + 1)
      - (alphaR G q * beta G E p)⁻¹ * extV (f p) q) / G.dv := by
  simp only [flux, alphaR]
  split_ifs with h
  · have hL := maxwMid_div_left G E hNv p q
    have hR := maxwMid_div_right G E hNv p q
    rw [mul_sub, ← hL, ← hR]
    congr 1
    ring
  · simp

/-- The left flux in stencil form. -/
lemma flux_self (hNv : 0 < Nv) (f : Phase Nx Nv) (p : Fin Nx) {q : ℕ} (hq : q < Nv) :
    flux G E f p q = (alphaL G q * beta G E p * extV (f p) q
      - (alphaL G q * beta G E p)⁻¹ * extV (f p) (q - 1)) / G.dv := by
  cases q with
  | zero => simp [flux, alphaL]
  | succ i =>
    rw [flux_succ G E hNv]
    have h1 : alphaR G i = alpha G i := by simp [alphaR, hq]
    have h2 : alphaL G (i + 1) = alpha G i := by simp [alphaL]
    rw [h1, h2]
    simp

/-- arXiv 2601.11900, the separable stencil (3.6), with the terms across the velocity boundary
absent. -/
theorem Lh_stencil (hNv : 0 < Nv) (f : Phase Nx Nv) (p : Fin Nx) (q : Fin Nv) :
    Lh G E f p q =
      (alphaR G q * beta G E p * extV (f p) (q + 1)
        - ((alphaR G q * beta G E p)⁻¹ + alphaL G q * beta G E p) * f p q
        + (alphaL G q * beta G E p)⁻¹ * extV (f p) (q - 1)) / G.dv ^ 2 := by
  have h := extV_coe (f p) q
  simp only [Lh, Matrix.of_apply]
  rw [flux_succ G E hNv, flux_self G E hNv f p q.2, h, ← sub_div, div_div, ← sq]
  congr 1
  ring

/-- `∑_{q'} w_{q'} c_{q'} = w_k c` when `c` is supported at the index `k`. -/
lemma sum_mul_ite (w : Fin Nv → ℝ) (k : ℕ) (c : ℝ) :
    ∑ q' : Fin Nv, w q' * (if (q' : ℕ) = k then c else 0) = extV w k * c := by
  by_cases h : k < Nv
  · rw [Finset.sum_eq_single ⟨k, h⟩]
    · simp [extV, h]
    · intro b _ hb
      have : (b : ℕ) ≠ k := fun e => hb (Fin.ext e)
      simp [this]
    · simp
  · rw [extV_of_le w (not_lt.1 h), zero_mul]
    refine Finset.sum_eq_zero fun b _ => ?_
    have : (b : ℕ) ≠ k := by have := b.2; omega
    simp [this]

lemma mul_Talpha_apply (f : Phase Nx Nv) (p : Fin Nx) (q : Fin Nv) :
    (f * (Talpha G)ᵀ) p q =
      (extV (f p) (q + 1) * alphaR G q - f p q * alphaL G q) / G.dv ^ 2 := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Talpha, Matrix.of_apply, mul_div_assoc',
    mul_sub, ← Finset.sum_div, Finset.sum_sub_distrib, sum_mul_ite, extV_coe]

lemma mul_TalphaInv_apply (f : Phase Nx Nv) (p : Fin Nx) (q : Fin Nv) :
    (f * (TalphaInv G)ᵀ) p q =
      (extV (f p) (q - 1) * (alphaL G q)⁻¹ - f p q * (alphaR G q)⁻¹) / G.dv ^ 2 := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, TalphaInv, Matrix.of_apply, mul_div_assoc',
    mul_sub, ← Finset.sum_div, Finset.sum_sub_distrib, sum_mul_ite, extV_coe]

/-- **Sec. 3.1, the separable form** of arXiv 2601.11900: `ℒ_h = β ⊗ 𝒯^{(α)} + β⁻¹ ⊗ 𝒯^{(1/α)}`.
A phase-space grid function is a matrix with rows indexed by position, so `β ⊗ 𝒯` acts as
`f ↦ diag(β) f 𝒯ᵀ`.  The operator `ℒ_h` on the left is the flux form (3.2)–(3.3) with the
geometric-mean Maxwellian and the zero-flux boundary condition. -/
theorem Lh_eq_tensor (hNv : 0 < Nv) (f : Phase Nx Nv) :
    Lh G E f = Matrix.diagonal (beta G E) * f * (Talpha G)ᵀ
      + Matrix.diagonal (fun p => (beta G E p)⁻¹) * f * (TalphaInv G)ᵀ := by
  ext p q
  rw [Matrix.add_apply, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.diagonal_mul,
    Matrix.diagonal_mul, mul_Talpha_apply, mul_TalphaInv_apply, Lh_stencil G E hNv, mul_inv,
    mul_inv]
  ring

/-- **Sec. 3.1, mass conservation** of arXiv 2601.11900: `⟨ℒ_h f, 1⟩ᵥʰ = 0` at every position. -/
theorem density_Lh (hNv : 0 < Nv) (f : Phase Nx Nv) : density G (Lh G E f) = 0 := by
  funext p
  have hdv := (dv_pos G hNv).ne'
  have h : ∀ q : Fin Nv, Lh G E f p q * (1 : Fin Nv → ℝ) q * G.dv
      = flux G E f p (q + 1) - flux G E f p q := by
    intro q
    simp only [Lh, Matrix.of_apply, Pi.one_apply, mul_one]
    field_simp
  simp only [density, ipV, Pi.zero_apply, h]
  rw [Fin.sum_univ_eq_sum_range (fun q => flux G E f p (q + 1) - flux G E f p q) Nv,
    Finset.sum_range_sub]
  obtain ⟨n, rfl⟩ : ∃ n, Nv = n + 1 := ⟨Nv - 1, by omega⟩
  simp [flux]

/-- The local equilibrium `ρ M` (row-wise scaling, §5.1). -/
noncomputable def rhoM (ρ : Fin Nx → ℝ) : Phase Nx Nv :=
  Matrix.of fun p q => ρ p * maxw G E p q

/-- arXiv 2601.11900, proof of Prop. 5.1: `ℒ_h (ρ M) = 0`, the local Maxwellians lie in the kernel.
-/
theorem Lh_rhoM (hNv : 0 < Nv) (ρ : Fin Nx → ℝ) : Lh G E (rhoM G E ρ) = 0 := by
  have hflux : ∀ p i, flux G E (rhoM G E ρ) p i = 0 := by
    intro p i
    cases i with
    | zero => rfl
    | succ i =>
      simp only [flux]
      split_ifs with h
      · have h1 : extV (rhoM G E ρ p) (i + 1) = ρ p * maxw G E p (i + 1) := by
          simp [extV, h, rhoM]
        have h2 : extV (rhoM G E ρ p) i = ρ p * maxw G E p i := by
          simp [extV, show i < Nv by omega, rhoM]
        rw [h1, h2, mul_div_cancel_right₀ _ (maxw_pos G E hNv p (i + 1)).ne',
          mul_div_cancel_right₀ _ (maxw_pos G E hNv p i).ne']
        simp
      · rfl
  ext p q
  simp [Lh, hflux]

end Stencil

/-! ### Norms -/

section Norms

variable {Nx Nv : ℕ} (G : Grid Nx Nv)

lemma ipXV_eq (φ ψ : Phase Nx Nv) : ipXV G φ ψ = G.dx * G.dv * ⟪φ, ψ⟫ := by
  simp only [ipXV, LeanDLRA.Frobenius.inner_def, Finset.mul_sum]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

lemma normXV_eq (hNx : 0 < Nx) (hNv : 0 < Nv) (f : Phase Nx Nv) :
    normXV G f = Real.sqrt (G.dx * G.dv) * ‖f‖ := by
  have h := (mul_pos (dx_pos G hNx) (dv_pos G hNv)).le
  rw [normXV, ipXV_eq, real_inner_self_eq_norm_sq, Real.sqrt_mul h, Real.sqrt_sq (norm_nonneg f)]

lemma normXV_nonneg (f : Phase Nx Nv) : 0 ≤ normXV G f := Real.sqrt_nonneg _

lemma ipXV_self_eq (hNx : 0 < Nx) (hNv : 0 < Nv) (f : Phase Nx Nv) :
    ipXV G f f = normXV G f ^ 2 := by
  have h : 0 ≤ ipXV G f f := by
    rw [ipXV_eq, real_inner_self_eq_norm_sq]
    have := mul_pos (dx_pos G hNx) (dv_pos G hNv)
    positivity
  rw [normXV, Real.sq_sqrt h]

lemma ipXV_le (hNx : 0 < Nx) (hNv : 0 < Nv) (φ ψ : Phase Nx Nv) :
    ipXV G φ ψ ≤ normXV G φ * normXV G ψ := by
  have h := mul_pos (dx_pos G hNx) (dv_pos G hNv)
  rw [ipXV_eq, normXV_eq G hNx hNv, normXV_eq G hNx hNv]
  have h1 := real_inner_le_norm φ ψ
  have h2 : Real.sqrt (G.dx * G.dv) * Real.sqrt (G.dx * G.dv) = G.dx * G.dv :=
    Real.mul_self_sqrt h.le
  calc G.dx * G.dv * ⟪φ, ψ⟫ ≤ G.dx * G.dv * (‖φ‖ * ‖ψ‖) := by gcongr
    _ = _ := by
      rw [show Real.sqrt (G.dx * G.dv) * ‖φ‖ * (Real.sqrt (G.dx * G.dv) * ‖ψ‖)
        = Real.sqrt (G.dx * G.dv) * Real.sqrt (G.dx * G.dv) * (‖φ‖ * ‖ψ‖) by ring, h2]

lemma normXV_add_le (hNx : 0 < Nx) (hNv : 0 < Nv) (φ ψ : Phase Nx Nv) :
    normXV G (φ + ψ) ≤ normXV G φ + normXV G ψ := by
  simp only [normXV_eq G hNx hNv]
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_add_le φ ψ) (Real.sqrt_nonneg _)

lemma normXV_smul (hNx : 0 < Nx) (hNv : 0 < Nv) {c : ℝ} (hc : 0 ≤ c) (φ : Phase Nx Nv) :
    normXV G (c • φ) = c * normXV G φ := by
  simp only [normXV_eq G hNx hNv, norm_smul, Real.norm_of_nonneg hc]
  ring

/-- A matrix bounded row by row against `f` is bounded in Frobenius norm. -/
lemma norm_le_of_rows {Q f : Phase Nx Nv} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ p, ∑ q, Q p q ^ 2 ≤ C ^ 2 * ∑ q, f p q ^ 2) : ‖Q‖ ≤ C * ‖f‖ := by
  have h1 : ‖Q‖ ^ 2 ≤ (C * ‖f‖) ^ 2 := by
    rw [mul_pow, LeanDLRA.Frobenius.norm_sq_eq_sum, LeanDLRA.Frobenius.norm_sq_eq_sum, mul_sum]
    exact sum_le_sum fun p _ => h p
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h1

/-- Multiplication by a bounded spatial weight. -/
lemma norm_diagonal_mul_le (d : Fin Nx → ℝ) {C : ℝ} (hC : 0 ≤ C) (hd : ∀ p, |d p| ≤ C)
    (f : Phase Nx Nv) : ‖Matrix.diagonal d * f‖ ≤ C * ‖f‖ := by
  refine norm_le_of_rows hC fun p => ?_
  simp only [Matrix.diagonal_mul]
  rw [mul_sum]
  refine sum_le_sum fun q _ => ?_
  rw [mul_pow]
  have : d p ^ 2 ≤ C ^ 2 := sq_le_sq' (by linarith [abs_le.1 (hd p)]) (abs_le.1 (hd p)).2
  exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

end Norms

/-! ### Prop. 5.1: discrete coercivity -/

section Coercivity

variable {Nx Nv : ℕ} (G : Grid Nx Nv) (E : Fin Nx → ℝ)

/-- `M_min = min_{p,q} M_{p,q+1/2}`, the minimum over the `N_v - 1` interior interfaces. -/
noncomputable def Mmin : ℝ := ⨅ i : Fin Nx × Fin (Nv - 1), maxwMid G E i.1 i.2

/-- `M_max = max { max_{p,q} M_{p,q}, max_{p,q} M_{p,q+1/2} }`. -/
noncomputable def Mmax : ℝ :=
  max (⨆ i : Fin Nx × Fin Nv, maxw G E i.1 i.2) (⨆ i : Fin Nx × Fin (Nv - 1), maxwMid G E i.1 i.2)

/-- `λ_N = (4 / Δv²) sin² (π / (2 N_v))` of (5.7). -/
noncomputable def lambdaN : ℝ := 4 / G.dv ^ 2 * Real.sin (Real.pi / (2 * Nv)) ^ 2

/-- `γ_h = M_min λ_N / (1 + √(L_v M_max))²` of (5.7). -/
noncomputable def gammaH : ℝ :=
  Mmin G E * lambdaN G / (1 + Real.sqrt (G.Lv * Mmax G E)) ^ 2

lemma Mmin_le (p : Fin Nx) {i : ℕ} (hi : i + 1 < Nv) : Mmin G E ≤ maxwMid G E p i :=
  ciInf_le (Set.finite_range _).bddBelow (p, (⟨i, by omega⟩ : Fin (Nv - 1)))

lemma maxw_le_Mmax (p : Fin Nx) {q : ℕ} (hq : q < Nv) : maxw G E p q ≤ Mmax G E :=
  le_trans (le_ciSup (Set.finite_range fun i : Fin Nx × Fin Nv => maxw G E i.1 i.2).bddAbove
    (p, ⟨q, hq⟩)) (le_max_left _ _)

lemma maxwMid_pos (hNv : 0 < Nv) (p : Fin Nx) (q : ℕ) : 0 < maxwMid G E p q :=
  Real.sqrt_pos.2 (mul_pos (maxw_pos G E hNv p q) (maxw_pos G E hNv p (q + 1)))

lemma Mmin_pos (hNx : 0 < Nx) (hNv : 2 ≤ Nv) : 0 < Mmin G E := by
  have h1 : Nonempty (Fin Nx) := ⟨⟨0, hNx⟩⟩
  have h2 : Nonempty (Fin (Nv - 1)) := ⟨⟨0, by omega⟩⟩
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite
    (f := fun i : Fin Nx × Fin (Nv - 1) => maxwMid G E i.1 i.2)
  rw [Mmin, ← hi]
  exact maxwMid_pos G E (by omega) _ _

lemma Mmax_pos (hNx : 0 < Nx) (hNv : 0 < Nv) : 0 < Mmax G E :=
  lt_of_lt_of_le (maxw_pos G E hNv ⟨0, hNx⟩ 0) (maxw_le_Mmax G E ⟨0, hNx⟩ hNv)

lemma lambdaN_pos (hNv : 0 < Nv) : 0 < lambdaN G := by
  have hdv := dv_pos G hNv
  have hN : (0 : ℝ) < Nv := by exact_mod_cast hNv
  have h1 : (1 : ℝ) ≤ Nv := by exact_mod_cast hNv
  have hs : 0 < Real.sin (Real.pi / (2 * Nv)) := by
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  rw [lambdaN]
  positivity

lemma gammaH_pos (hNx : 0 < Nx) (hNv : 2 ≤ Nv) : 0 < gammaH G E := by
  have h1 := Mmin_pos G E hNx hNv
  have h2 := lambdaN_pos G (show 0 < Nv by omega)
  rw [gammaH]
  positivity

/-- The fluctuation `g = f - ρ M` of the micro-macro decomposition (5.2), `ρ = ⟨f, 1⟩ᵥʰ`. -/
noncomputable def micro (f : Phase Nx Nv) : Phase Nx Nv := f - rhoM G E (density G f)

/-- The relative fluctuation `u = g / M`. -/
noncomputable def relFluct (f : Phase Nx Nv) : Phase Nx Nv :=
  Matrix.of fun p q => micro G E f p q / maxw G E p q

/-- arXiv 2601.11900, (5.3): the fluctuation has zero velocity moment. -/
theorem density_micro (hNv : 0 < Nv) (f : Phase Nx Nv) : density G (micro G E f) = 0 := by
  funext p
  have h := sum_maxw G E hNv p
  simp only [density, ipV, micro, rhoM, Matrix.sub_apply, Matrix.of_apply, Pi.one_apply, mul_one,
    sub_mul, Finset.sum_sub_distrib, Pi.zero_apply, mul_assoc]
  rw [← Finset.mul_sum, h]
  ring

/-- Coercivity on the velocity grid, for one position: the steps of the proof of Prop. 5.1 between
the discrete Poincaré inequality and the triangle inequality. -/
lemma velocity_coercivity {N : ℕ} (hN : 0 < N) {dv Mh : ℝ} (hdv : 0 < dv) (m u : ℕ → ℝ)
    (hm0 : ∀ q ∈ range N, 0 ≤ m q) (hmax : ∀ q ∈ range N, m q ≤ Mh)
    (hmass : ∑ q ∈ range N, m q * dv = 1) (hzero : ∑ q ∈ range N, u q * m q * dv = 0) :
    (4 / dv ^ 2 * Real.sin (Real.pi / (2 * N)) ^ 2) * ∑ q ∈ range N, u q ^ 2 * dv
      ≤ (1 + Real.sqrt (N * dv * Mh)) ^ 2 *
        (1 / dv * ∑ i ∈ range (N - 1), (u (i + 1) - u i) ^ 2) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hPoi := neumann_poincare hN u
  set ub : ℝ := (∑ q ∈ range N, u q) / N with hub
  set S2 := ∑ q ∈ range N, (u q - ub) ^ 2 with hS2
  set D := ∑ i ∈ range (N - 1), (u (i + 1) - u i) ^ 2 with hD
  set s := Real.sin (Real.pi / (2 * (N : ℝ))) ^ 2 with hs
  have hs0 : 0 ≤ s := sq_nonneg _
  have hS20 : 0 ≤ S2 := sum_nonneg fun _ _ => sq_nonneg _
  have hSum : ∑ q ∈ range N, u q = ub * N := by rw [hub]; field_simp
  -- `‖u‖² = ‖u - ū‖² + ū² L`
  have hdecomp : ∑ q ∈ range N, u q ^ 2 * dv = S2 * dv + ub ^ 2 * (N * dv) := by
    have : S2 = ∑ q ∈ range N, u q ^ 2 - 2 * ub * ∑ q ∈ range N, u q + N * ub ^ 2 := by
      simp only [hS2, sub_sq, sum_add_distrib, sum_sub_distrib, sum_const, card_range,
        nsmul_eq_mul, mul_sum]
      congr 1
      refine congrArg _ (sum_congr rfl fun _ _ => by ring)
    rw [← sum_mul, this, hSum]
    ring
  -- `ū = -⟨u - ū, M⟩`
  have hneg : ∑ q ∈ range N, (u q - ub) * m q * dv = -ub := by
    have : ∀ q, (u q - ub) * m q * dv = u q * m q * dv - ub * (m q * dv) := fun q => by ring
    simp only [this, sum_sub_distrib, ← mul_sum, hzero, hmass]
    ring
  have hsd : Real.sqrt dv * Real.sqrt dv = dv := Real.mul_self_sqrt hdv.le
  -- Cauchy–Schwarz
  have hCS : ub ^ 2 ≤ S2 * dv * Mh := by
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq (range N) (fun q => (u q - ub) * Real.sqrt dv)
      (fun q => m q * Real.sqrt dv)
    have e1 : ∑ q ∈ range N, (u q - ub) * Real.sqrt dv * (m q * Real.sqrt dv) = -ub := by
      rw [← hneg]
      refine sum_congr rfl fun q _ => ?_
      rw [show (u q - ub) * Real.sqrt dv * (m q * Real.sqrt dv)
        = (u q - ub) * m q * (Real.sqrt dv * Real.sqrt dv) by ring, hsd]
    have e2 : ∑ q ∈ range N, ((u q - ub) * Real.sqrt dv) ^ 2 = S2 * dv := by
      rw [hS2, sum_mul]
      refine sum_congr rfl fun q _ => ?_
      rw [mul_pow, Real.sq_sqrt hdv.le]
    have e3 : ∑ q ∈ range N, (m q * Real.sqrt dv) ^ 2 ≤ Mh := by
      calc ∑ q ∈ range N, (m q * Real.sqrt dv) ^ 2
          ≤ ∑ q ∈ range N, Mh * (m q * dv) := by
            refine sum_le_sum fun q hq => ?_
            rw [mul_pow, Real.sq_sqrt hdv.le]
            have := hmax q hq
            have h0 := hm0 q hq
            nlinarith [mul_nonneg h0 hdv.le]
        _ = Mh := by rw [← mul_sum, hmass, mul_one]
    rw [e1, e2] at h1
    calc ub ^ 2 = (-ub) ^ 2 := by ring
      _ ≤ S2 * dv * ∑ q ∈ range N, (m q * Real.sqrt dv) ^ 2 := h1
      _ ≤ S2 * dv * Mh := by gcongr
  have hMh : 0 ≤ Mh := by
    by_cases hzero' : S2 * dv = 0
    · have : Mh * 1 = ∑ q ∈ range N, Mh * (m q * dv) := by rw [← hmass, mul_sum]
      rw [mul_one] at this
      rw [this]
      refine sum_nonneg fun q hq => ?_
      have h0 := hm0 q hq
      have h1 := hmax q hq
      exact mul_nonneg (h0.trans h1) (mul_nonneg h0 hdv.le)
    · have h0 : 0 < S2 * dv := lt_of_le_of_ne (by positivity) (Ne.symm hzero')
      by_contra hneg'
      have hlt : S2 * dv * Mh < 0 := mul_neg_of_pos_of_neg h0 (not_le.1 hneg')
      nlinarith [sq_nonneg ub]
  have hLM : 0 ≤ N * dv * Mh := by positivity
  set r := Real.sqrt (N * dv * Mh) with hr
  have hr2 : r ^ 2 = N * dv * Mh := Real.sq_sqrt hLM
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hkey : ∑ q ∈ range N, u q ^ 2 * dv ≤ S2 * dv * (1 + r) ^ 2 := by
    rw [hdecomp]
    have hN1 : ub ^ 2 * (N * dv) ≤ S2 * dv * Mh * (N * dv) := by gcongr
    have hE : S2 * dv * (1 + r) ^ 2 = S2 * dv + S2 * dv * (N * dv * Mh) + S2 * dv * (2 * r) := by
      rw [← hr2]; ring
    have h3 : 0 ≤ S2 * dv * (2 * r) := by positivity
    nlinarith
  calc (4 / dv ^ 2 * s) * ∑ q ∈ range N, u q ^ 2 * dv
      ≤ (4 / dv ^ 2 * s) * (S2 * dv * (1 + r) ^ 2) := by gcongr
    _ = (1 + r) ^ 2 * (1 / dv * (4 * s * S2)) := by field_simp
    _ ≤ (1 + r) ^ 2 * (1 / dv * D) := by gcongr

/-- The dissipation identity in the proof of Prop. 5.1, at one position. -/
lemma dissipation_row (hNv : 0 < Nv) (f : Phase Nx Nv) (p : Fin Nx) :
    ∑ q, Lh G E f p q * relFluct G E f p q * G.dx * G.dv
      = -(G.dx / G.dv * ∑ i ∈ range (Nv - 1), maxwMid G E p i *
          (extV (relFluct G E f p) (i + 1) - extV (relFluct G E f p) i) ^ 2) := by
  have hdv := (dv_pos G hNv).ne'
  set u : ℕ → ℝ := extV (relFluct G E f p) with hu
  set J : ℕ → ℝ := flux G E f p with hJ
  have hrel : ∀ q, q < Nv → extV (f p) q / maxw G E p q = density G f p + u q := by
    intro q hq
    have hM := (maxw_pos G E hNv p q).ne'
    have e1 : extV (f p) q = f p ⟨q, hq⟩ := by simp [extV, hq]
    have e2 : u q = relFluct G E f p ⟨q, hq⟩ := by simp [hu, extV, hq]
    rw [e1, e2]
    simp only [relFluct, micro, rhoM, Matrix.of_apply, Matrix.sub_apply]
    field_simp
    ring
  have h1 : ∀ q : Fin Nv, Lh G E f p q * relFluct G E f p q * G.dx * G.dv
      = G.dx * ((J (q + 1) - J q) * u q) := by
    intro q
    have : relFluct G E f p q = u q := (extV_coe _ q).symm
    simp only [Lh, Matrix.of_apply, this]
    field_simp
    ring
  simp only [h1]
  rw [← mul_sum, Fin.sum_univ_eq_sum_range (fun q => (J (q + 1) - J q) * u q) Nv]
  obtain ⟨n, rfl⟩ : ∃ n, Nv = n + 1 := ⟨Nv - 1, by omega⟩
  rw [sum_flux_mul J u rfl n]
  have hJ1 : J (n + 1) = 0 := by simp [hJ, flux]
  have hJ2 : ∀ i ∈ range n, J (i + 1) * (u (i + 1) - u i)
      = maxwMid G E p i * (u (i + 1) - u i) ^ 2 / G.dv := by
    intro i hi
    have hi' : i < n := Finset.mem_range.1 hi
    have e : J (i + 1) = maxwMid G E p i * (u (i + 1) - u i) / G.dv := by
      simp only [hJ, flux, show i + 1 < n + 1 by omega, ↓reduceIte]
      rw [hrel (i + 1) (by omega), hrel i (by omega)]
      congr 2
      ring
    rw [e]
    ring
  rw [hJ1, zero_mul, zero_sub, sum_congr rfl hJ2, ← sum_div, Nat.add_sub_cancel]
  ring

/-- arXiv 2601.11900, the global dissipation relation in the proof of Prop. 5.1:
`⟨ℒ_h f, u⟩ₓᵥʰ = -(Δx/Δv) ∑_{p,q} M_{p,q+1/2} (u_{p,q+1} - u_{p,q})²` with `u = g / M`. -/
theorem dissipation_identity (hNv : 0 < Nv) (f : Phase Nx Nv) :
    ipXV G (Lh G E f) (relFluct G E f)
      = -(G.dx / G.dv * ∑ p, ∑ i ∈ range (Nv - 1), maxwMid G E p i *
          (extV (relFluct G E f p) (i + 1) - extV (relFluct G E f p) i) ^ 2) := by
  simp only [ipXV, dissipation_row G E hNv, Finset.sum_neg_distrib, Finset.mul_sum]

/-- **Prop. 5.1 (discrete coercivity)** of arXiv 2601.11900.  For every phase-space grid function
`f`, with `ρ = ⟨f, 1⟩ᵥʰ`, `g = f - ρ M` and the sharp constant
`γ_h = M_min λ_N / (1 + √(L_v M_max))²`, `λ_N = (4 / Δv²) sin² (π / (2 N_v))`:
`-⟨ℒ_h f, g / M⟩ₓᵥʰ ≥ γ_h ‖g / M‖²`.  No difference from the paper; the assumptions `N_x ≥ 1` and
`N_v ≥ 2` make the minima in `M_min`, `M_max` meaningful.  The discrete Poincaré inequality, which
the paper takes as known, is `neumann_poincare`. -/
theorem coercivity (hNx : 0 < Nx) (hNv : 2 ≤ Nv) (f : Phase Nx Nv) :
    gammaH G E * normXV G (relFluct G E f) ^ 2 ≤ -ipXV G (Lh G E f) (relFluct G E f) := by
  have hNv0 : 0 < Nv := by omega
  have hdv := dv_pos G hNv0
  have hdx := dx_pos G hNx
  have hM := Mmin_pos G E hNx hNv
  rw [← ipXV_self_eq G hNx hNv0, dissipation_identity G E hNv0, neg_neg]
  simp only [ipXV]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine sum_le_sum fun p _ => ?_
  set u : ℕ → ℝ := extV (relFluct G E f p) with hu
  have hrow : ∑ q : Fin Nv, relFluct G E f p q * relFluct G E f p q * G.dx * G.dv
      = G.dx * ∑ q ∈ range Nv, u q ^ 2 * G.dv := by
    rw [← Fin.sum_univ_eq_sum_range (fun q => u q ^ 2 * G.dv) Nv, Finset.mul_sum]
    refine sum_congr rfl fun q _ => ?_
    have : u q = relFluct G E f p q := extV_coe _ q
    rw [this]
    ring
  have hmass : ∑ q ∈ range Nv, maxw G E p q * G.dv = 1 := by
    rw [← Fin.sum_univ_eq_sum_range (fun q => maxw G E p q * G.dv) Nv]
    exact sum_maxw G E hNv0 p
  have hzero : ∑ q ∈ range Nv, u q * maxw G E p q * G.dv = 0 := by
    rw [← Fin.sum_univ_eq_sum_range (fun q => u q * maxw G E p q * G.dv) Nv]
    have h0 := congrFun (density_micro G E hNv0 f) p
    simp only [density, ipV, Pi.one_apply, mul_one, Pi.zero_apply] at h0
    rw [← h0]
    refine sum_congr rfl fun q _ => ?_
    have : u q = relFluct G E f p q := extV_coe _ q
    have hMq := (maxw_pos G E hNv0 p q).ne'
    rw [this]
    simp only [relFluct, Matrix.of_apply]
    field_simp
  have hvc := velocity_coercivity hNv0 hdv (maxw G E p) u
    (fun q _ => (maxw_pos G E hNv0 p q).le)
    (fun q hq => maxw_le_Mmax G E p (Finset.mem_range.1 hq)) hmass hzero
  rw [← Lv_eq G hNv0] at hvc
  set r := Real.sqrt (G.Lv * Mmax G E) with hr
  have hr0 : 0 < (1 + r) ^ 2 := by have := Real.sqrt_nonneg (G.Lv * Mmax G E); positivity
  set D := ∑ i ∈ range (Nv - 1), (u (i + 1) - u i) ^ 2 with hD
  have hlow : Mmin G E * D ≤ ∑ i ∈ range (Nv - 1), maxwMid G E p i * (u (i + 1) - u i) ^ 2 := by
    rw [hD, mul_sum]
    refine sum_le_sum fun i hi => ?_
    have hi' : i < Nv - 1 := Finset.mem_range.1 hi
    exact mul_le_mul_of_nonneg_right (Mmin_le G E p (by omega)) (sq_nonneg _)
  rw [hrow]
  have hstep : gammaH G E * ∑ q ∈ range Nv, u q ^ 2 * G.dv ≤ Mmin G E * (1 / G.dv * D) := by
    have hg : gammaH G E = Mmin G E * lambdaN G / (1 + r) ^ 2 := rfl
    rw [hg, div_mul_eq_mul_div, div_le_iff₀ hr0, mul_assoc]
    calc Mmin G E * (lambdaN G * ∑ q ∈ range Nv, u q ^ 2 * G.dv)
        ≤ Mmin G E * ((1 + r) ^ 2 * (1 / G.dv * D)) := by
          apply mul_le_mul_of_nonneg_left _ hM.le
          exact hvc
      _ = _ := by ring
  calc gammaH G E * (G.dx * ∑ q ∈ range Nv, u q ^ 2 * G.dv)
      = G.dx * (gammaH G E * ∑ q ∈ range Nv, u q ^ 2 * G.dv) := by ring
    _ ≤ G.dx * (Mmin G E * (1 / G.dv * D)) := by gcongr
    _ = G.dx / G.dv * (Mmin G E * D) := by field_simp
    _ ≤ _ := by gcongr

end Coercivity

/-! ### Prop. 5.2: the normal component -/

section Fluctuation

variable {Nx Nv : ℕ} (G : Grid Nx Nv) (E : Fin Nx → ℝ)
variable {R : Type*} [Fintype R] [DecidableEq R]

/-- The spatial arithmetic mean `β̄` of the weights `β_p`. -/
noncomputable def betaBar : ℝ := (∑ p, beta G E p) / Nx

/-- `‖δβ‖_∞ = max_p |β_p - β̄|`. -/
noncomputable def deltaBeta : ℝ := ⨆ p, |beta G E p - betaBar G E|

/-- `C_β = max_p (β_p β̄)⁻¹`. -/
noncomputable def Cbeta : ℝ := ⨆ p, (beta G E p * betaBar G E)⁻¹

/-- `α_max`, the maximum of `α_{q+1/2}` over the interior interfaces. -/
noncomputable def alphaMax : ℝ := ⨆ i : Fin (Nv - 1), alpha G i

/-- `α_min`, the minimum of `α_{q+1/2}` over the interior interfaces. -/
noncomputable def alphaMin : ℝ := ⨅ i : Fin (Nv - 1), alpha G i

/-- `κ_h = ‖δβ‖_∞ (2 α_max / Δv² + C_β 2 / (α_min Δv²))` of (5.10). -/
noncomputable def kappaH : ℝ :=
  deltaBeta G E * (2 * alphaMax G / G.dv ^ 2 + Cbeta G E * (2 / (alphaMin G * G.dv ^ 2)))

/-- The spatial projector `(P_X ⊗ I) f = ∑_i X_i ⟨f, X_i⟩ₓʰ`.  The columns of `X` are the basis
functions `X_i`, orthonormal for `⟨·,·⟩ₓʰ` means `Δx Xᵀ X = 1`. -/
noncomputable def projX (X : Matrix (Fin Nx) R ℝ) (f : Phase Nx Nv) : Phase Nx Nv :=
  G.dx • (X * Xᵀ * f)

omit [DecidableEq R] in
/-- Sec. 3.1: velocity operators `I ⊗ 𝒯` commute with `P_X ⊗ I`. -/
lemma projX_mul (X : Matrix (Fin Nx) R ℝ) (f : Phase Nx Nv) (T : Matrix (Fin Nv) (Fin Nv) ℝ) :
    projX G X (f * T) = projX G X f * T := by
  simp only [projX, Matrix.smul_mul, Matrix.mul_assoc]

omit [DecidableEq R] in
lemma projX_add (X : Matrix (Fin Nx) R ℝ) (f g : Phase Nx Nv) :
    projX G X (f + g) = projX G X f + projX G X g := by
  simp only [projX, Matrix.mul_add, smul_add]

omit [DecidableEq R] in
lemma projX_sub (X : Matrix (Fin Nx) R ℝ) (f g : Phase Nx Nv) :
    projX G X (f - g) = projX G X f - projX G X g := by
  simp only [projX, Matrix.mul_sub, smul_sub]

omit [DecidableEq R] in
lemma projX_smul (X : Matrix (Fin Nx) R ℝ) (c : ℝ) (f : Phase Nx Nv) :
    projX G X (c • f) = c • projX G X f := by
  simp only [projX, Matrix.mul_smul, smul_comm G.dx c]

omit [DecidableEq R] in
lemma projX_eq_leftProj (hNx : 0 < Nx) (X : Matrix (Fin Nx) R ℝ) (f : Phase Nx Nv) :
    projX G X f = leftProj (Real.sqrt G.dx • X) f := by
  have h := Real.mul_self_sqrt (dx_pos G hNx).le
  simp only [projX, leftProj_apply, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, h]

lemma isOrthProj_projX (hNx : 0 < Nx) {X : Matrix (Fin Nx) R ℝ} (hX : G.dx • (Xᵀ * X) = 1) :
    IsOrthProj (leftProj (n := Fin Nv) (Real.sqrt G.dx • X)) := by
  apply isOrthProj_leftProj
  have h := Real.mul_self_sqrt (dx_pos G hNx).le
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h]
  exact hX

/-- arXiv 2601.11900, an abstract form of Prop. 5.2: if an orthogonal projector `P` commutes with
`B` and fixes `f`, then `‖(I - P) A B f‖ ≤ ‖A - c I‖ ‖B f‖` for every scalar `c`. -/
theorem norm_normal_le {𝓔 : Type*} [NormedAddCommGroup 𝓔] [InnerProductSpace ℝ 𝓔]
    {P A B : 𝓔 →L[ℝ] 𝓔} (hP : IsOrthProj P) (hB : ∀ x, P (B x) = B (P x)) {f : 𝓔} (hf : P f = f)
    (c : ℝ) : ‖A (B f) - P (A (B f))‖ ≤ ‖A - c • 1‖ * ‖B f‖ := by
  have hy : P (c • B f) = c • B f := by rw [map_smul, hB, hf]
  calc ‖A (B f) - P (A (B f))‖ ≤ ‖A (B f) - c • B f‖ := hP.norm_sub_le_of_mem_range _ _ hy
    _ = ‖(A - c • 1) (B f)‖ := by simp
    _ ≤ _ := ContinuousLinearMap.le_opNorm _ _

lemma alpha_le_max {i : ℕ} (hi : i + 1 < Nv) : alpha G i ≤ alphaMax G :=
  le_ciSup (f := fun i : Fin (Nv - 1) => alpha G i) (Set.finite_range _).bddAbove ⟨i, by omega⟩

lemma alphaMin_le {i : ℕ} (hi : i + 1 < Nv) : alphaMin G ≤ alpha G i :=
  ciInf_le (f := fun i : Fin (Nv - 1) => alpha G i) (Set.finite_range _).bddBelow ⟨i, by omega⟩

lemma alphaMin_pos (hNv : 2 ≤ Nv) : 0 < alphaMin G := by
  have h2 : Nonempty (Fin (Nv - 1)) := ⟨⟨0, by omega⟩⟩
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun i : Fin (Nv - 1) => alpha G i)
  rw [alphaMin, ← hi]
  exact alpha_pos G _

lemma alphaMax_pos (hNv : 2 ≤ Nv) : 0 < alphaMax G :=
  lt_of_lt_of_le (alpha_pos G 0) (alpha_le_max G (i := 0) (by omega))

lemma abs_alphaR_le (hNv : 2 ≤ Nv) (q : ℕ) : |alphaR G q| ≤ alphaMax G := by
  have h := alphaMax_pos G hNv
  simp only [alphaR]
  split_ifs with hq
  · rw [abs_of_pos (alpha_pos G q)]
    exact alpha_le_max G hq
  · simpa using h.le

lemma abs_alphaL_le (hNv : 2 ≤ Nv) {q : ℕ} (hq : q < Nv) : |alphaL G q| ≤ alphaMax G := by
  have h := alphaMax_pos G hNv
  simp only [alphaL]
  split_ifs with h0
  · rw [abs_of_pos (alpha_pos G _)]
    exact alpha_le_max G (by omega)
  · simpa using h.le

lemma abs_inv_alpha_le (hNv : 2 ≤ Nv) {i : ℕ} (hi : i + 1 < Nv) :
    |(alpha G i)⁻¹| ≤ (alphaMin G)⁻¹ := by
  rw [abs_of_pos (inv_pos.2 (alpha_pos G i))]
  exact inv_anti₀ (alphaMin_pos G hNv) (alphaMin_le G hi)

lemma abs_inv_alphaR_le (hNv : 2 ≤ Nv) (q : ℕ) : |(alphaR G q)⁻¹| ≤ (alphaMin G)⁻¹ := by
  have h := inv_pos.2 (alphaMin_pos G hNv)
  simp only [alphaR]
  split_ifs with hq
  · exact abs_inv_alpha_le G hNv hq
  · simpa using h.le

lemma abs_inv_alphaL_le (hNv : 2 ≤ Nv) {q : ℕ} (hq : q < Nv) :
    |(alphaL G q)⁻¹| ≤ (alphaMin G)⁻¹ := by
  have h := inv_pos.2 (alphaMin_pos G hNv)
  simp only [alphaL]
  split_ifs with h0
  · exact abs_inv_alpha_le G hNv (by omega)
  · simpa using h.le

lemma sq_le_of_abs_le {a C : ℝ} (h : |a| ≤ C) : a ^ 2 ≤ C ^ 2 :=
  sq_le_sq' (by linarith [abs_le.1 h]) (abs_le.1 h).2

lemma sum_sq_extV (w : Fin Nv → ℝ) :
    ∑ q ∈ range Nv, extV w q ^ 2 = ∑ q, w q ^ 2 := by
  rw [← Fin.sum_univ_eq_sum_range (fun q => extV w q ^ 2) Nv]
  exact sum_congr rfl fun q _ => by rw [extV_coe]

/-- The shift to the right does not increase the `ℓ²` norm. -/
lemma sum_shift_up_le (w : Fin Nv → ℝ) (c : ℕ → ℝ) {C : ℝ} (hc : ∀ q, |c q| ≤ C) :
    ∑ q : Fin Nv, (extV w (q + 1) * c q) ^ 2 ≤ C ^ 2 * ∑ q, w q ^ 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun q => (extV w (q + 1) * c q) ^ 2) Nv, ← sum_sq_extV, mul_sum]
  have h1 : ∑ q ∈ range Nv, (extV w (q + 1) * c q) ^ 2
      ≤ ∑ q ∈ range Nv, C ^ 2 * extV w (q + 1) ^ 2 := by
    refine sum_le_sum fun q _ => ?_
    rw [mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (sq_le_of_abs_le (hc q)) (sq_nonneg _)
  refine h1.trans ?_
  rw [← mul_sum, ← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  have e := sum_range_succ (fun q => extV w q ^ 2) Nv
  rw [sum_range_succ'] at e
  rw [extV_of_le w le_rfl] at e
  have := sq_nonneg (extV w 0)
  nlinarith

/-- The shift to the left does not increase the `ℓ²` norm; `c 0 = 0` removes the boundary term. -/
lemma sum_shift_down_le (hNv : 0 < Nv) (w : Fin Nv → ℝ) (c : ℕ → ℝ) {C : ℝ} (h0 : c 0 = 0)
    (hc : ∀ q, q < Nv → |c q| ≤ C) :
    ∑ q : Fin Nv, (extV w (q - 1) * c q) ^ 2 ≤ C ^ 2 * ∑ q, w q ^ 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun q => (extV w (q - 1) * c q) ^ 2) Nv, ← sum_sq_extV]
  obtain ⟨n, rfl⟩ : ∃ n, Nv = n + 1 := ⟨Nv - 1, by omega⟩
  rw [sum_range_succ', h0, sum_range_succ _ n]
  simp only [mul_zero, Nat.add_sub_cancel]
  have h1 : ∑ i ∈ range n, (extV w i * c (i + 1)) ^ 2 ≤ C ^ 2 * ∑ i ∈ range n, extV w i ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun i hi => ?_
    rw [mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right
      (sq_le_of_abs_le (hc _ (by have := Finset.mem_range.1 hi; omega))) (sq_nonneg _)
  have h2 : 0 ≤ C ^ 2 * extV w n ^ 2 := by positivity
  have h3 : (0 : ℝ) ^ 2 = 0 := by norm_num
  rw [h3, add_zero, mul_add]
  linarith

lemma norm_mul_Talpha_le (hNv : 2 ≤ Nv) (f : Phase Nx Nv) :
    ‖f * (Talpha G)ᵀ‖ ≤ 2 * alphaMax G / G.dv ^ 2 * ‖f‖ := by
  have hNv0 : 0 < Nv := by omega
  have hA := (alphaMax_pos G hNv).le
  have hd := dv_pos G hNv0
  set S1 : Phase Nx Nv := Matrix.of fun p q => extV (f p) (q + 1) * alphaR G q with hS1
  set S2 : Phase Nx Nv := Matrix.of fun p q => f p q * alphaL G q with hS2
  have hf : f * (Talpha G)ᵀ = (1 / G.dv ^ 2) • (S1 - S2) := by
    ext p q
    rw [mul_Talpha_apply]
    simp only [hS1, hS2, Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply, smul_eq_mul]
    ring
  have h1 : ‖S1‖ ≤ alphaMax G * ‖f‖ :=
    norm_le_of_rows hA fun p => sum_shift_up_le (f p) _ (abs_alphaR_le G hNv)
  have h2 : ‖S2‖ ≤ alphaMax G * ‖f‖ := by
    refine norm_le_of_rows hA fun p => ?_
    rw [mul_sum]
    refine sum_le_sum fun q _ => ?_
    simp only [hS2, Matrix.of_apply]
    rw [mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (sq_le_of_abs_le (abs_alphaL_le G hNv q.2)) (sq_nonneg _)
  rw [hf, norm_smul, Real.norm_of_nonneg (by positivity)]
  calc 1 / G.dv ^ 2 * ‖S1 - S2‖ ≤ 1 / G.dv ^ 2 * (‖S1‖ + ‖S2‖) := by gcongr; exact norm_sub_le _ _
    _ ≤ 1 / G.dv ^ 2 * (alphaMax G * ‖f‖ + alphaMax G * ‖f‖) := by gcongr
    _ = _ := by ring

lemma norm_mul_TalphaInv_le (hNv : 2 ≤ Nv) (f : Phase Nx Nv) :
    ‖f * (TalphaInv G)ᵀ‖ ≤ 2 / (alphaMin G * G.dv ^ 2) * ‖f‖ := by
  have hNv0 : 0 < Nv := by omega
  have hA := alphaMin_pos G hNv
  have hAi := (inv_pos.2 hA).le
  have hd := dv_pos G hNv0
  set S1 : Phase Nx Nv := Matrix.of fun p q => extV (f p) (q - 1) * (alphaL G q)⁻¹ with hS1
  set S2 : Phase Nx Nv := Matrix.of fun p q => f p q * (alphaR G q)⁻¹ with hS2
  have hf : f * (TalphaInv G)ᵀ = (1 / G.dv ^ 2) • (S1 - S2) := by
    ext p q
    rw [mul_TalphaInv_apply]
    simp only [hS1, hS2, Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply, smul_eq_mul]
    ring
  have h1 : ‖S1‖ ≤ (alphaMin G)⁻¹ * ‖f‖ :=
    norm_le_of_rows hAi fun p => sum_shift_down_le hNv0 (f p) _ (by simp [alphaL])
      (fun q hq => abs_inv_alphaL_le G hNv hq)
  have h2 : ‖S2‖ ≤ (alphaMin G)⁻¹ * ‖f‖ := by
    refine norm_le_of_rows hAi fun p => ?_
    rw [mul_sum]
    refine sum_le_sum fun q _ => ?_
    simp only [hS2, Matrix.of_apply]
    rw [mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (sq_le_of_abs_le (abs_inv_alphaR_le G hNv q)) (sq_nonneg _)
  rw [hf, norm_smul, Real.norm_of_nonneg (by positivity)]
  calc 1 / G.dv ^ 2 * ‖S1 - S2‖ ≤ 1 / G.dv ^ 2 * (‖S1‖ + ‖S2‖) := by gcongr; exact norm_sub_le _ _
    _ ≤ 1 / G.dv ^ 2 * ((alphaMin G)⁻¹ * ‖f‖ + (alphaMin G)⁻¹ * ‖f‖) := by gcongr
    _ = _ := by field_simp; ring

lemma betaBar_pos (hNx : 0 < Nx) : 0 < betaBar G E := by
  have hN : (0 : ℝ) < Nx := by exact_mod_cast hNx
  have : Nonempty (Fin Nx) := ⟨⟨0, hNx⟩⟩
  exact div_pos (Finset.sum_pos (fun p _ => beta_pos G E p) Finset.univ_nonempty) hN

lemma abs_sub_betaBar_le (p : Fin Nx) : |beta G E p - betaBar G E| ≤ deltaBeta G E :=
  le_ciSup (f := fun p => |beta G E p - betaBar G E|) (Set.finite_range _).bddAbove p

lemma deltaBeta_nonneg : 0 ≤ deltaBeta G E :=
  Real.iSup_nonneg fun _ => abs_nonneg _

lemma inv_le_Cbeta (p : Fin Nx) : (beta G E p * betaBar G E)⁻¹ ≤ Cbeta G E :=
  le_ciSup (f := fun p => (beta G E p * betaBar G E)⁻¹) (Set.finite_range _).bddAbove p

lemma Cbeta_nonneg (hNx : 0 < Nx) : 0 ≤ Cbeta G E :=
  Real.iSup_nonneg fun p =>
    (inv_pos.2 (mul_pos (beta_pos G E p) (betaBar_pos G E hNx))).le

lemma kappaH_nonneg (hNx : 0 < Nx) (hNv : 2 ≤ Nv) : 0 ≤ kappaH G E := by
  have h1 := deltaBeta_nonneg G E
  have h2 := Cbeta_nonneg G E hNx
  have h3 := alphaMax_pos G hNv
  have h4 := alphaMin_pos G hNv
  rw [kappaH]
  positivity

/-- **Prop. 5.2 (normal component)** of arXiv 2601.11900.  If `f` lies in the range of `P_X ⊗ I`
for a basis `X` orthonormal in `⟨·,·⟩ₓʰ`, then `‖(I - P_X) ℒ_h f‖ₓᵥʰ ≤ κ_h ‖f‖ₓᵥʰ` with
`κ_h = ‖δβ‖_∞ (2 α_max / Δv² + C_β 2 / (α_min Δv²))`.  No difference from the paper.  The reason is
that `(I - P_X) (β̄ 𝒯 f) = 0`; the abstract form of this step is `norm_normal_le`. -/
theorem fluctuation_bound (hNx : 0 < Nx) (hNv : 2 ≤ Nv) {X : Matrix (Fin Nx) R ℝ}
    (hX : G.dx • (Xᵀ * X) = 1) {f : Phase Nx Nv} (hf : projX G X f = f) :
    normXV G (Lh G E f - projX G X (Lh G E f)) ≤ kappaH G E * normXV G f := by
  have hNv0 : 0 < Nv := by omega
  have hb := betaBar_pos G E hNx
  set b := betaBar G E with hbdef
  set f1 := f * (Talpha G)ᵀ with hf1
  set f2 := f * (TalphaInv G)ᵀ with hf2
  have hL : Lh G E f = Matrix.diagonal (beta G E) * f1
      + Matrix.diagonal (fun p => (beta G E p)⁻¹) * f2 := by
    rw [Lh_eq_tensor G E hNv0, Matrix.mul_assoc, Matrix.mul_assoc]
  set y : Phase Nx Nv := b • f1 + b⁻¹ • f2 with hy
  have hP := isOrthProj_projX G hNx hX
  have hPf1 : projX G X f1 = f1 := by rw [hf1, projX_mul, hf]
  have hPf2 : projX G X f2 = f2 := by rw [hf2, projX_mul, hf]
  have hPy : leftProj (Real.sqrt G.dx • X) y = y := by
    have h : projX G X y = b • projX G X f1 + b⁻¹ • projX G X f2 := by
      simp only [hy, projX, Matrix.mul_add, Matrix.mul_smul, smul_add, smul_comm G.dx]
    rw [← projX_eq_leftProj G hNx, h, hPf1, hPf2]
  have hbest := hP.norm_sub_le_of_mem_range (Lh G E f) y hPy
  rw [← projX_eq_leftProj G hNx] at hbest
  have hdiff : Lh G E f - y = Matrix.diagonal (fun p => beta G E p - b) * f1
      + Matrix.diagonal (fun p => (beta G E p)⁻¹ - b⁻¹) * f2 := by
    ext p q
    rw [hL]
    simp only [hy, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_mul,
      smul_eq_mul]
    ring
  have hδ := deltaBeta_nonneg G E
  have hC := Cbeta_nonneg G E hNx
  have h1 : ‖Matrix.diagonal (fun p => beta G E p - b) * f1‖ ≤ deltaBeta G E * ‖f1‖ :=
    norm_diagonal_mul_le _ hδ (abs_sub_betaBar_le G E) _
  have h2 : ‖Matrix.diagonal (fun p => (beta G E p)⁻¹ - b⁻¹) * f2‖
      ≤ (Cbeta G E * deltaBeta G E) * ‖f2‖ := by
    refine norm_diagonal_mul_le _ (by positivity) (fun p => ?_) _
    have hbp := beta_pos G E p
    have e : (beta G E p)⁻¹ - b⁻¹ = -((beta G E p * b)⁻¹ * (beta G E p - b)) := by
      field_simp
      ring
    rw [e, abs_neg, abs_mul, abs_of_pos (inv_pos.2 (mul_pos hbp hb))]
    exact mul_le_mul (inv_le_Cbeta G E p) (abs_sub_betaBar_le G E p) (abs_nonneg _) hC
  have h3 := norm_mul_Talpha_le G hNv f
  have h4 := norm_mul_TalphaInv_le G hNv f
  have hmain : ‖Lh G E f - projX G X (Lh G E f)‖ ≤ kappaH G E * ‖f‖ := by
    calc ‖Lh G E f - projX G X (Lh G E f)‖ ≤ ‖Lh G E f - y‖ := hbest
      _ ≤ deltaBeta G E * ‖f1‖ + (Cbeta G E * deltaBeta G E) * ‖f2‖ := by
        rw [hdiff]
        exact (norm_add_le _ _).trans (add_le_add h1 h2)
      _ ≤ deltaBeta G E * (2 * alphaMax G / G.dv ^ 2 * ‖f‖)
          + (Cbeta G E * deltaBeta G E) * (2 / (alphaMin G * G.dv ^ 2) * ‖f‖) := by gcongr
      _ = _ := by rw [kappaH]; ring
  rw [normXV_eq G hNx hNv0, normXV_eq G hNx hNv0]
  calc Real.sqrt (G.dx * G.dv) * ‖Lh G E f - projX G X (Lh G E f)‖
      ≤ Real.sqrt (G.dx * G.dv) * (kappaH G E * ‖f‖) := by gcongr
    _ = _ := by ring

end Fluctuation

/-! ### Thm 5.3: the AP property up to the field fluctuation -/

section AP

variable {Nx Nv : ℕ} (G : Grid Nx Nv) (E : Fin Nx → ℝ)
variable {R : Type*} [Fintype R] [DecidableEq R]

/-- `Θ = γ_h / (γ_h - κ_h M_max)` of Thm 5.3. -/
noncomputable def thetaH : ℝ := gammaH G E / (gammaH G E - kappaH G E * Mmax G E)

lemma one_le_thetaH (hNx : 0 < Nx) (hNv : 2 ≤ Nv) (hκ : kappaH G E * Mmax G E < gammaH G E) :
    1 ≤ thetaH G E := by
  have h1 := kappaH_nonneg G E hNx hNv
  have h2 := Mmax_pos G E hNx (show 0 < Nv by omega)
  have h3 : 0 < gammaH G E - kappaH G E * Mmax G E := by linarith
  rw [thetaH, one_le_div h3]
  nlinarith [mul_nonneg h1 h2.le]

/-- The absorption argument of the proof of Thm 5.3, on the level of the norms. -/
lemma ap_absorption {a b k F g u m r γ : ℝ} (hk : 0 ≤ k) (hm : 0 < m) (hkm : k * m < γ)
    (hγ : 0 < γ) (hb : 0 ≤ b) (hr : 0 ≤ r) (hu : 0 ≤ u) (h1 : a ≤ b + k * F) (h2 : F ≤ r + g)
    (h3 : g ≤ m * u) (h4 : γ * u ^ 2 ≤ a * u) :
    a ≤ γ / (γ - k * m) * (b + k * r) ∧ g ≤ m / γ * (γ / (γ - k * m)) * (b + k * r) := by
  have hd : 0 < γ - k * m := by linarith
  have hB : 0 ≤ b + k * r := by positivity
  have hkF : k * F ≤ k * r + k * g := by nlinarith
  have hkg : k * g ≤ k * (m * u) := by nlinarith
  have hu2 : (γ - k * m) * u ≤ b + k * r := by
    rcases hu.eq_or_lt with h0 | h0
    · rw [← h0, mul_zero]
      exact hB
    · have : γ * u ≤ a := by
        have : u * (γ * u) ≤ u * a := by nlinarith
        exact le_of_mul_le_mul_left this h0
      nlinarith
  have hu3 : u ≤ (b + k * r) / (γ - k * m) := (le_div_iff₀ hd).2 (by linarith)
  have hg : g ≤ m * ((b + k * r) / (γ - k * m)) := h3.trans (by gcongr)
  have hkg' : k * g ≤ k * (m * ((b + k * r) / (γ - k * m))) := by gcongr
  constructor
  · have e : γ / (γ - k * m) * (b + k * r)
        = b + k * r + k * (m * ((b + k * r) / (γ - k * m))) := by
      field_simp
      ring
    rw [e]
    linarith
  · have e : m / γ * (γ / (γ - k * m)) * (b + k * r) = m * ((b + k * r) / (γ - k * m)) := by
      field_simp
    rw [e]
    exact hg

/-- `1 ≤ L_v M_max`, a consequence of the normalization (5.1). -/
lemma one_le_Lv_mul_Mmax (hNx : 0 < Nx) (hNv : 0 < Nv) : 1 ≤ G.Lv * Mmax G E := by
  have h := sum_maxw G E hNv ⟨0, hNx⟩
  have hd := dv_pos G hNv
  rw [Lv_eq G hNv, ← h]
  calc ∑ q : Fin Nv, maxw G E ⟨0, hNx⟩ q * G.dv ≤ ∑ _q : Fin Nv, Mmax G E * G.dv := by
        refine sum_le_sum fun q _ => ?_
        exact mul_le_mul_of_nonneg_right (maxw_le_Mmax G E _ q.2) hd.le
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- arXiv 2601.11900: `‖ρ M‖ₓᵥʰ ≤ √M_max ‖ρ‖ₓʰ`, a sharper form of the bound in the proof of
Thm 5.3, which follows from (5.1). -/
theorem normXV_rhoM_le (hNx : 0 < Nx) (hNv : 0 < Nv) (ρ : Fin Nx → ℝ) :
    normXV G (rhoM G E ρ) ≤ Real.sqrt (Mmax G E) * normX G ρ := by
  have hd := dv_pos G hNv
  have hx := dx_pos G hNx
  have hMp := Mmax_pos G E hNx hNv
  rw [normX, ← Real.sqrt_mul hMp.le, normXV]
  apply Real.sqrt_le_sqrt
  simp only [ipXV, ipX, rhoM, Matrix.of_apply, Finset.mul_sum]
  refine sum_le_sum fun p _ => ?_
  have hrow : ∑ q : Fin Nv, maxw G E p q ^ 2 * G.dv ≤ Mmax G E := by
    calc ∑ q : Fin Nv, maxw G E p q ^ 2 * G.dv
        ≤ ∑ q : Fin Nv, Mmax G E * (maxw G E p q * G.dv) := by
          refine sum_le_sum fun q _ => ?_
          have h0 := (maxw_pos G E hNv p q).le
          have h1 := maxw_le_Mmax G E p q.2
          nlinarith [mul_nonneg h0 hd.le]
      _ = Mmax G E := by rw [← mul_sum, sum_maxw G E hNv p, mul_one]
  calc ∑ q : Fin Nv, ρ p * maxw G E p q * (ρ p * maxw G E p q) * G.dx * G.dv
      = ρ p * ρ p * G.dx * ∑ q : Fin Nv, maxw G E p q ^ 2 * G.dv := by
        rw [mul_sum]
        exact sum_congr rfl fun q _ => by ring
    _ ≤ ρ p * ρ p * G.dx * Mmax G E := by
        apply mul_le_mul_of_nonneg_left hrow
        have := mul_self_nonneg (ρ p)
        positivity
    _ = _ := by ring

/-- `√M_max ≤ M_max √L_v`: the sharper form of `normXV_rhoM_le` implies the paper's bound. -/
lemma sqrt_Mmax_le (hNx : 0 < Nx) (hNv : 0 < Nv) :
    Real.sqrt (Mmax G E) ≤ Mmax G E * Real.sqrt G.Lv := by
  have hMp := Mmax_pos G E hNx hNv
  have h1 := one_le_Lv_mul_Mmax G E hNx hNv
  have hL := Lv_pos G
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt hL.le]
  nlinarith

/-- arXiv 2601.11900: the bound `‖ρ M‖ₓᵥʰ ≤ M_max √L_v ‖ρ‖ₓʰ` of the proof of Thm 5.3. -/
theorem normXV_rhoM_le_paper (hNx : 0 < Nx) (hNv : 0 < Nv) (ρ : Fin Nx → ℝ) :
    normXV G (rhoM G E ρ) ≤ Mmax G E * Real.sqrt G.Lv * normX G ρ :=
  (normXV_rhoM_le G E hNx hNv ρ).trans
    (mul_le_mul_of_nonneg_right (sqrt_Mmax_le G E hNx hNv) (Real.sqrt_nonneg _))

lemma normXV_micro_le (hNx : 0 < Nx) (hNv : 0 < Nv) (f : Phase Nx Nv) :
    normXV G (micro G E f) ≤ Mmax G E * normXV G (relFluct G E f) := by
  have hMp := Mmax_pos G E hNx hNv
  have hmain : ‖micro G E f‖ ≤ Mmax G E * ‖relFluct G E f‖ := by
    refine norm_le_of_rows hMp.le fun p => ?_
    rw [mul_sum]
    refine sum_le_sum fun q _ => ?_
    have h0 := maxw_pos G E hNv p q
    have h1 := maxw_le_Mmax G E p q.2
    have e : micro G E f p q = maxw G E p q * relFluct G E f p q := by
      simp only [relFluct, Matrix.of_apply]
      field_simp
    rw [e, mul_pow]
    have : maxw G E p (q : ℕ) ^ 2 ≤ Mmax G E ^ 2 := by gcongr
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  rw [normXV_eq G hNx hNv, normXV_eq G hNx hNv]
  calc Real.sqrt (G.dx * G.dv) * ‖micro G E f‖
      ≤ Real.sqrt (G.dx * G.dv) * (Mmax G E * ‖relFluct G E f‖) := by gcongr
    _ = _ := by ring

lemma f_eq_rhoM_add_micro (f : Phase Nx Nv) :
    f = rhoM G E (density G f) + micro G E f := by
  simp [micro]

lemma neg_ipXV_le (hNx : 0 < Nx) (hNv : 0 < Nv) (φ ψ : Phase Nx Nv) :
    -ipXV G φ ψ ≤ normXV G φ * normXV G ψ := by
  have h := ipXV_le G hNx hNv (-φ) ψ
  have e1 : ipXV G (-φ) ψ = -ipXV G φ ψ := by
    simp only [ipXV, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib]
  have e2 : normXV G (-φ) = normXV G φ := by
    simp only [normXV_eq G hNx hNv, norm_neg]
  rwa [e1, e2] at h

/-- arXiv 2601.11900, the core of Thm 5.3: `f` in the range of `P_X ⊗ I` with `P_X ℒ_h f = ε Gn`,
and any bound `‖ρ M‖ₓᵥʰ ≤ c ‖ρ‖ₓʰ`. -/
theorem ap_bound (hNx : 0 < Nx) (hNv : 2 ≤ Nv) {X : Matrix (Fin Nx) R ℝ}
    (hX : G.dx • (Xᵀ * X) = 1) {f Gn : Phase Nx Nv} {ε c : ℝ} (hε : 0 ≤ ε) (hc : 0 ≤ c)
    (hf : projX G X f = f) (hPL : projX G X (Lh G E f) = ε • Gn)
    (hκ : kappaH G E * Mmax G E < gammaH G E)
    (hcρ : normXV G (rhoM G E (density G f)) ≤ c * normX G (density G f)) :
    normXV G (Lh G E f) ≤
        thetaH G E * (ε * normXV G Gn + kappaH G E * c * normX G (density G f)) ∧
      normXV G (f - rhoM G E (density G f)) ≤
        Mmax G E / gammaH G E * thetaH G E *
          (ε * normXV G Gn + kappaH G E * c * normX G (density G f)) := by
  have hNv0 : 0 < Nv := by omega
  have hγ := gammaH_pos G E hNx hNv
  have hk := kappaH_nonneg G E hNx hNv
  have hm := Mmax_pos G E hNx hNv0
  set ρ := density G f with hρ
  have hnρ : 0 ≤ normX G ρ := Real.sqrt_nonneg _
  have hdec : Lh G E f = projX G X (Lh G E f) + (Lh G E f - projX G X (Lh G E f)) :=
    (add_sub_cancel _ _).symm
  have h1 : normXV G (Lh G E f) ≤ ε * normXV G Gn + kappaH G E * normXV G f := by
    calc normXV G (Lh G E f)
        = normXV G (projX G X (Lh G E f) + (Lh G E f - projX G X (Lh G E f))) := by rw [← hdec]
      _ ≤ normXV G (projX G X (Lh G E f)) + normXV G (Lh G E f - projX G X (Lh G E f)) :=
        normXV_add_le G hNx hNv0 _ _
      _ ≤ ε * normXV G Gn + kappaH G E * normXV G f := by
        have h5 := fluctuation_bound G E hNx hNv hX hf
        have h6 : normXV G (projX G X (Lh G E f)) = ε * normXV G Gn := by
          rw [hPL, normXV_smul G hNx hNv0 hε]
        linarith
  have h2 : normXV G f ≤ c * normX G ρ + normXV G (micro G E f) := by
    calc normXV G f = normXV G (rhoM G E ρ + micro G E f) := by
          rw [hρ, ← f_eq_rhoM_add_micro]
      _ ≤ normXV G (rhoM G E ρ) + normXV G (micro G E f) := normXV_add_le G hNx hNv0 _ _
      _ ≤ _ := by gcongr
  have h3 := normXV_micro_le G E hNx hNv0 f
  have h4 : gammaH G E * normXV G (relFluct G E f) ^ 2
      ≤ normXV G (Lh G E f) * normXV G (relFluct G E f) :=
    (coercivity G E hNx hNv f).trans (neg_ipXV_le G hNx hNv0 _ _)
  have hb : 0 ≤ ε * normXV G Gn := mul_nonneg hε (normXV_nonneg G _)
  have hr : 0 ≤ c * normX G ρ := by positivity
  have := ap_absorption hk hm hκ hγ hb hr (normXV_nonneg G _) h1 h2 h3 h4
  simpa only [thetaH, mul_assoc, micro] using this

/-- The residual `G^{n+1} = (f^{n+1} - f^{(2)}) / Δt - P_X 𝒜_h f^{(2)}` of (5.14). -/
noncomputable def residual (A : Phase Nx Nv → Phase Nx Nv) (Δt : ℝ) (X : Matrix (Fin Nx) R ℝ)
    (f f₂ : Phase Nx Nv) : Phase Nx Nv :=
  (1 / Δt) • (f - f₂) - projX G X (A f₂)

/-- The L-step (4.6) in matrix form.  The columns of `L₂`, `L₃` are `L_i^{(2)}`, `L_i^{n+1}`, so
`f^{(2)} = X L₂ᵀ`, `f^{n+1} = X L₃ᵀ`, and `⟨w, X_i⟩ₓʰ` is the `i`-th column of `Δx wᵀ X`. -/
def IsLStep (A : Phase Nx Nv → Phase Nx Nv) (ε Δt : ℝ) (X : Matrix (Fin Nx) R ℝ)
    (L₂ L₃ : Matrix (Fin Nv) R ℝ) : Prop :=
  (1 / Δt) • (L₃ - L₂) =
    G.dx • ((A (X * L₂ᵀ))ᵀ * X) + (1 / ε) • G.dx • ((Lh G E (X * L₃ᵀ))ᵀ * X)

omit [DecidableEq R] in
/-- arXiv 2601.11900, (5.14): the L-step gives `P_X ℒ_h f^{n+1} = ε G^{n+1}`. -/
theorem IsLStep.proj_Lh_eq {A : Phase Nx Nv → Phase Nx Nv} {ε Δt : ℝ} (hε : 0 < ε)
    {X : Matrix (Fin Nx) R ℝ} {L₂ L₃ : Matrix (Fin Nv) R ℝ} (h : IsLStep G E A ε Δt X L₂ L₃) :
    projX G X (Lh G E (X * L₃ᵀ)) = ε • residual G A Δt X (X * L₃ᵀ) (X * L₂ᵀ) := by
  have h1 := congrArg (fun M => X * Mᵀ) h
  simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_sub, Matrix.mul_add, Matrix.mul_smul,
    Matrix.mul_sub] at h1
  have hf : (1 / Δt) • (X * L₃ᵀ - X * L₂ᵀ)
      = projX G X (A (X * L₂ᵀ)) + (1 / ε) • projX G X (Lh G E (X * L₃ᵀ)) := by
    simp only [projX, ← Matrix.mul_assoc] at h1 ⊢
    exact h1
  simp only [residual]
  rw [hf, add_sub_cancel_left, smul_smul, mul_one_div_cancel hε.ne', one_smul]

lemma projX_mul_self {X : Matrix (Fin Nx) R ℝ} (hX : G.dx • (Xᵀ * X) = 1)
    (L : Matrix (Fin Nv) R ℝ) : projX G X (X * Lᵀ) = X * Lᵀ := by
  have h : projX G X (X * Lᵀ) = X * ((G.dx • (Xᵀ * X)) * Lᵀ) := by
    simp only [projX, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  rw [h, hX, Matrix.one_mul]

/-- **Thm 5.3 (AP property up to the field fluctuation)** of arXiv 2601.11900.  Let `X` be
orthonormal in `⟨·,·⟩ₓʰ`, let `f^{n+1} = X L₃ᵀ` be the result of the L-step (4.6) from
`f^{(2)} = X L₂ᵀ`, with any discrete advection operator `𝒜_h` (no structure on it is used) and any
field `E`, and let `ρ = ⟨f^{n+1}, 1⟩ᵥʰ`, `G^{n+1}` the residual (5.14).  If `κ_h M_max < γ_h`
(Assumption 5.1), then `Θ = γ_h / (γ_h - κ_h M_max) ≥ 1` and

* (5.12) `‖ℒ_h f^{n+1}‖ₓᵥʰ ≤ Θ (ε ‖G^{n+1}‖ₓᵥʰ + κ_h M_max √L_v ‖ρ‖ₓʰ)`,
* (5.13) `‖f^{n+1} - ρ M‖ₓᵥʰ ≤ (M_max / γ_h) Θ (ε ‖G^{n+1}‖ₓᵥʰ + κ_h M_max √L_v ‖ρ‖ₓʰ)`.

No difference from the paper.  The constant is the paper's `M_max √L_v`; the variant
`√(M_max L_v)` is false, see `header_constant_false`.  The paper's formal assumption
`‖G^{n+1}‖ = 𝒪(1)` is not needed for these two inequalities, and the case `g = 0`, which the proof
in the paper excludes, is covered. -/
theorem ap_property (hNx : 0 < Nx) (hNv : 2 ≤ Nv) {X : Matrix (Fin Nx) R ℝ}
    (hX : G.dx • (Xᵀ * X) = 1) {A : Phase Nx Nv → Phase Nx Nv} {ε Δt : ℝ} (hε : 0 < ε)
    {L₂ L₃ : Matrix (Fin Nv) R ℝ} (hL : IsLStep G E A ε Δt X L₂ L₃)
    (hκ : kappaH G E * Mmax G E < gammaH G E) {f f₂ : Phase Nx Nv} (hf : f = X * L₃ᵀ)
    (hf₂ : f₂ = X * L₂ᵀ) :
    1 ≤ thetaH G E ∧
      normXV G (Lh G E f) ≤ thetaH G E *
        (ε * normXV G (residual G A Δt X f f₂)
          + kappaH G E * Mmax G E * Real.sqrt G.Lv * normX G (density G f)) ∧
      normXV G (f - rhoM G E (density G f)) ≤ Mmax G E / gammaH G E * thetaH G E *
        (ε * normXV G (residual G A Δt X f f₂)
          + kappaH G E * Mmax G E * Real.sqrt G.Lv * normX G (density G f)) := by
  subst hf hf₂
  have hNv0 : 0 < Nv := by omega
  have hc : 0 ≤ Mmax G E * Real.sqrt G.Lv :=
    mul_nonneg (Mmax_pos G E hNx hNv0).le (Real.sqrt_nonneg _)
  have := ap_bound G E hNx hNv hX hε.le hc (projX_mul_self G hX L₃) (hL.proj_Lh_eq G E hε) hκ
    (normXV_rhoM_le_paper G E hNx hNv0 _)
  simp only [mul_assoc] at this ⊢
  exact ⟨one_le_thetaH G E hNx hNv hκ, this⟩

/-- arXiv 2601.11900, a sharper form of Thm 5.3: by the normalization (5.1) the factor `M_max √L_v`
of the paper can be replaced by the smaller `√M_max`. -/
theorem ap_property_sharp (hNx : 0 < Nx) (hNv : 2 ≤ Nv) {X : Matrix (Fin Nx) R ℝ}
    (hX : G.dx • (Xᵀ * X) = 1) {A : Phase Nx Nv → Phase Nx Nv} {ε Δt : ℝ} (hε : 0 < ε)
    {L₂ L₃ : Matrix (Fin Nv) R ℝ} (hL : IsLStep G E A ε Δt X L₂ L₃)
    (hκ : kappaH G E * Mmax G E < gammaH G E) {f f₂ : Phase Nx Nv} (hf : f = X * L₃ᵀ)
    (hf₂ : f₂ = X * L₂ᵀ) :
    normXV G (Lh G E f) ≤ thetaH G E *
        (ε * normXV G (residual G A Δt X f f₂)
          + kappaH G E * Real.sqrt (Mmax G E) * normX G (density G f)) ∧
      normXV G (f - rhoM G E (density G f)) ≤ Mmax G E / gammaH G E * thetaH G E *
        (ε * normXV G (residual G A Δt X f f₂)
          + kappaH G E * Real.sqrt (Mmax G E) * normX G (density G f)) := by
  subst hf hf₂
  exact ap_bound G E hNx hNv hX hε.le (Real.sqrt_nonneg _) (projX_mul_self G hX L₃)
    (hL.proj_Lh_eq G E hε) hκ (normXV_rhoM_le G E hNx (by omega) _)

/-- arXiv 2601.11900, the variant of (5.13) with `√(M_max L_v)` in place of the paper's
`M_max √L_v`.  It holds for `L_v ≥ 1`, in particular for the domain `[-6, 6]` of the paper's
experiments, and it fails in general (`header_constant_false`). -/
theorem ap_property_header (hNx : 0 < Nx) (hNv : 2 ≤ Nv) (hLv : 1 ≤ G.Lv)
    {X : Matrix (Fin Nx) R ℝ} (hX : G.dx • (Xᵀ * X) = 1) {A : Phase Nx Nv → Phase Nx Nv}
    {ε Δt : ℝ} (hε : 0 < ε) {L₂ L₃ : Matrix (Fin Nv) R ℝ} (hL : IsLStep G E A ε Δt X L₂ L₃)
    (hκ : kappaH G E * Mmax G E < gammaH G E) {f f₂ : Phase Nx Nv} (hf : f = X * L₃ᵀ)
    (hf₂ : f₂ = X * L₂ᵀ) :
    normXV G (f - rhoM G E (density G f)) ≤ Mmax G E / gammaH G E * thetaH G E *
      (ε * normXV G (residual G A Δt X f f₂)
        + kappaH G E * Real.sqrt (Mmax G E * G.Lv) * normX G (density G f)) := by
  subst hf hf₂
  have hNv0 : 0 < Nv := by omega
  have hm := Mmax_pos G E hNx hNv0
  have h : Real.sqrt (Mmax G E) ≤ Real.sqrt (Mmax G E * G.Lv) :=
    Real.sqrt_le_sqrt (le_mul_of_one_le_right hm.le hLv)
  exact (ap_bound G E hNx hNv hX hε.le (Real.sqrt_nonneg _) (projX_mul_self G hX L₃)
    (hL.proj_Lh_eq G E hε) hκ
    ((normXV_rhoM_le G E hNx hNv0 _).trans
      (mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg _)))).2

/-- A spatially constant field has `κ_h = 0`, see Remark 5.4. -/
lemma kappaH_eq_zero_of_const (hNx : 0 < Nx) {e : ℝ} (hE : ∀ p, E p = e) : kappaH G E = 0 := by
  have hN : (Nx : ℝ) ≠ 0 := by exact_mod_cast hNx.ne'
  have hb : ∀ p, beta G E p = Real.exp (-(G.dv / 2 * e)) := fun p => by simp [beta, hE]
  have hbar : betaBar G E = Real.exp (-(G.dv / 2 * e)) := by
    simp only [betaBar, hb, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hδ : deltaBeta G E = 0 := by
    simp [deltaBeta, hbar, hb]
  rw [kappaH, hδ, zero_mul]

/-- **Remark 5.4** of arXiv 2601.11900: for a spatially constant field, even a large one, `κ_h = 0`
and the L-step satisfies the strong AP estimates `‖ℒ_h f^{n+1}‖ ≤ ε ‖G^{n+1}‖` and
`‖f^{n+1} - ρ M‖ ≤ (M_max / γ_h) ε ‖G^{n+1}‖`. -/
theorem ap_constant_field (hNx : 0 < Nx) (hNv : 2 ≤ Nv) {e : ℝ} (hE : ∀ p, E p = e)
    {X : Matrix (Fin Nx) R ℝ} (hX : G.dx • (Xᵀ * X) = 1) {A : Phase Nx Nv → Phase Nx Nv}
    {ε Δt : ℝ} (hε : 0 < ε) {L₂ L₃ : Matrix (Fin Nv) R ℝ} (hL : IsLStep G E A ε Δt X L₂ L₃)
    {f f₂ : Phase Nx Nv} (hf : f = X * L₃ᵀ) (hf₂ : f₂ = X * L₂ᵀ) :
    normXV G (Lh G E f) ≤ ε * normXV G (residual G A Δt X f f₂) ∧
      normXV G (f - rhoM G E (density G f)) ≤
        Mmax G E / gammaH G E * (ε * normXV G (residual G A Δt X f f₂)) := by
  have hγ := gammaH_pos G E hNx hNv
  have hk := kappaH_eq_zero_of_const G E hNx hE
  have hκ : kappaH G E * Mmax G E < gammaH G E := by rwa [hk, zero_mul]
  have hΘ : thetaH G E = 1 := by
    rw [thetaH, hk, zero_mul, sub_zero, div_self hγ.ne']
  obtain ⟨-, h1, h2⟩ := ap_property G E hNx hNv hX hε hL hκ hf hf₂
  simpa only [hk, hΘ, zero_mul, add_zero, one_mul, mul_one] using And.intro h1 h2

end AP

/-! ### The projected operators and Algorithm 1 -/

section Algorithm

variable {Nx Nv : ℕ} (G : Grid Nx Nv) (E : Fin Nx → ℝ)
variable {R : Type*} [Fintype R] [DecidableEq R]

omit [DecidableEq R] in
/-- (3.7), the K-step projection of arXiv 2601.11900: `⟨ℒ_h (K Vᵀ), V_j⟩ᵥʰ` needs the `r × r`
velocity matrices `⟨𝒯 V_ℓ, V_j⟩ᵥʰ` only.  The columns of `K`, `V` are `K_ℓ`, `V_ℓ`. -/
theorem kProjection_separable (hNv : 0 < Nv) (K : Matrix (Fin Nx) R ℝ)
    (V : Matrix (Fin Nv) R ℝ) :
    G.dv • (Lh G E (K * Vᵀ) * V) =
      Matrix.diagonal (beta G E) * K * (G.dv • (Vᵀ * (Talpha G)ᵀ * V))
        + Matrix.diagonal (fun p => (beta G E p)⁻¹) * K * (G.dv • (Vᵀ * (TalphaInv G)ᵀ * V)) := by
  rw [Lh_eq_tensor G E hNv]
  simp only [Matrix.add_mul, Matrix.mul_smul, Matrix.mul_assoc, smul_add]

omit [DecidableEq R] in
/-- (3.8), the S-step projection of arXiv 2601.11900: `⟨ℒ_h (X S Vᵀ), X_i V_j⟩ₓᵥʰ` is a sum of two
products of `r × r` spatial and velocity matrices. -/
theorem sProjection_separable (hNv : 0 < Nv) (X : Matrix (Fin Nx) R ℝ) (S : Matrix R R ℝ)
    (V : Matrix (Fin Nv) R ℝ) :
    (G.dx * G.dv) • (Xᵀ * Lh G E (X * S * Vᵀ) * V) =
      (G.dx • (Xᵀ * Matrix.diagonal (beta G E) * X)) * S *
          (G.dv • (Vᵀ * (Talpha G)ᵀ * V))
        + (G.dx • (Xᵀ * Matrix.diagonal (fun p => (beta G E p)⁻¹) * X)) * S *
          (G.dv • (Vᵀ * (TalphaInv G)ᵀ * V)) := by
  rw [Lh_eq_tensor G E hNv]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
    smul_add, smul_smul, mul_comm G.dx G.dv]

omit [DecidableEq R] in
/-- (3.9), the L-step projection of arXiv 2601.11900: `⟨ℒ_h (X Lᵀ), X_i⟩ₓʰ` needs the `r × r`
spatial matrices `⟨β X_k, X_i⟩ₓʰ`, `⟨β⁻¹ X_k, X_i⟩ₓʰ` only. -/
theorem lProjection_separable (hNv : 0 < Nv) (X : Matrix (Fin Nx) R ℝ)
    (L : Matrix (Fin Nv) R ℝ) :
    G.dx • ((Lh G E (X * Lᵀ))ᵀ * X) =
      Talpha G * L * (G.dx • (Xᵀ * Matrix.diagonal (beta G E) * X))
        + TalphaInv G * L *
          (G.dx • (Xᵀ * Matrix.diagonal (fun p => (beta G E p)⁻¹) * X)) := by
  rw [Lh_eq_tensor G E hNv]
  simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.diagonal_transpose, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_assoc, smul_add]

/-- (4.2) of arXiv 2601.11900: the zeroth moment of the full-tensor IMEX scheme (4.1) is explicit,
because `ℒ_h` conserves mass.  This is why the field `E^{n+1}` can be computed first. -/
theorem density_imex (hNv : 0 < Nv) {A : Phase Nx Nv → Phase Nx Nv} {ε Δt : ℝ} (hΔt : 0 < Δt)
    {f₀ f₁ : Phase Nx Nv} (h : (1 / Δt) • (f₁ - f₀) = A f₀ + (1 / ε) • Lh G E f₁) :
    density G f₁ = density G f₀ + Δt • density G (A f₀) := by
  have hdens : ∀ (a b : Phase Nx Nv) (c : ℝ),
      density G (a + c • b) = density G a + c • density G b := by
    intro a b c
    funext p
    simp only [density, ipV, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Pi.add_apply,
      Pi.smul_apply, Pi.one_apply, mul_one, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
      mul_assoc]
  have hf : f₁ = f₀ + Δt • (A f₀ + (1 / ε) • Lh G E f₁) := by
    rw [← h, smul_smul, mul_one_div_cancel hΔt.ne', one_smul]
    exact (add_sub_cancel _ _).symm
  have h1 : density G (A f₀ + (1 / ε) • Lh G E f₁) = density G (A f₀) := by
    rw [hdens, density_Lh G E hNv]
    simp
  conv_lhs => rw [hf]
  rw [hdens, h1]

/-- `(I ⊗ P_V) f = ∑_j ⟨f, V_j⟩ᵥʰ V_j`.  The columns of `V` are the basis functions `V_j`. -/
noncomputable def projV (V : Matrix (Fin Nv) R ℝ) (f : Phase Nx Nv) : Phase Nx Nv :=
  G.dv • (f * V * Vᵀ)

/-- One step of **Algorithm 1** of arXiv 2601.11900 (the first-order low-rank IMEX scheme), with
`f^n = X₀ S₀ V₀ᵀ`: the density prediction (4.3) and the Poisson solve, here any map `poisson` from
densities to fields, the K-step (4.4) with QR factorization `K₁ = X₁ S₁`, the explicit S-step (4.5),
the L-step (4.6), and the QR factorization `L₃ = V₁ S₃ᵀ`.  The advection operator `A` is arbitrary.
-/
structure IsIMEXStep (poisson : (Fin Nx → ℝ) → Fin Nx → ℝ) (A : Phase Nx Nv → Phase Nx Nv)
    (ε Δt : ℝ) (X₀ X₁ : Matrix (Fin Nx) R ℝ) (V₀ V₁ : Matrix (Fin Nv) R ℝ)
    (S₀ S₁ S₂ S₃ : Matrix R R ℝ) (K₁ : Matrix (Fin Nx) R ℝ) (L₃ : Matrix (Fin Nv) R ℝ)
    (E : Fin Nx → ℝ) : Prop where
  orthX₀ : G.dx • (X₀ᵀ * X₀) = 1
  orthV₀ : G.dv • (V₀ᵀ * V₀) = 1
  orthX₁ : G.dx • (X₁ᵀ * X₁) = 1
  orthV₁ : G.dv • (V₁ᵀ * V₁) = 1
  field : E = poisson (density G (X₀ * S₀ * V₀ᵀ) + Δt • density G (A (X₀ * S₀ * V₀ᵀ)))
  kStep : (1 / Δt) • (K₁ - X₀ * S₀) =
    G.dv • (A (X₀ * S₀ * V₀ᵀ) * V₀) + (1 / ε) • G.dv • (Lh G E (K₁ * V₀ᵀ) * V₀)
  qrK : K₁ = X₁ * S₁
  sStep : (1 / Δt) • (S₂ - S₁) =
    -((G.dx * G.dv) • (X₁ᵀ * A (X₁ * S₁ * V₀ᵀ) * V₀))
      - (1 / ε) • (G.dx * G.dv) • (X₁ᵀ * Lh G E (X₁ * S₁ * V₀ᵀ) * V₀)
  lStep : IsLStep G E A ε Δt X₁ (V₀ * S₂ᵀ) L₃
  qrL : L₃ = V₁ * S₃ᵀ

/-- **Algorithm 1, the explicit S-step cancels the stiff term** of arXiv 2601.11900.  After the
implicit K-step and the explicit backward S-step the operator `ℒ_h` has disappeared exactly, for
every `ε`:
`f^{(2)} = P_X^{n+1} f^n + Δt P_X^{n+1} P_V^n (𝒜_h f^n - 𝒜_h f^{(1)})`.
This is not stated in the paper as an identity.  It is the concrete form of the mechanism behind
the hybrid K/S/L structure, which the library has for a dissipative operator as
`hybridKSL_norm_le_perturbed`; here `ℒ_h` is the discrete operator, which is not dissipative for the
unweighted inner product (`Lh_not_dissipative`), and the S-step advects `f^{(1)}`, as in (4.5). -/
theorem IsIMEXStep.stiff_cancel {poisson : (Fin Nx → ℝ) → Fin Nx → ℝ}
    {A : Phase Nx Nv → Phase Nx Nv} {ε Δt : ℝ} (hΔt : 0 < Δt)
    {X₀ X₁ : Matrix (Fin Nx) R ℝ} {V₀ V₁ : Matrix (Fin Nv) R ℝ} {S₀ S₁ S₂ S₃ : Matrix R R ℝ}
    {K₁ : Matrix (Fin Nx) R ℝ} {L₃ : Matrix (Fin Nv) R ℝ} {E : Fin Nx → ℝ}
    (h : IsIMEXStep G poisson A ε Δt X₀ X₁ V₀ V₁ S₀ S₁ S₂ S₃ K₁ L₃ E) :
    X₁ * S₂ * V₀ᵀ = projX G X₁ (X₀ * S₀ * V₀ᵀ) +
      Δt • projX G X₁ (projV G V₀ (A (X₀ * S₀ * V₀ᵀ) - A (X₁ * S₁ * V₀ᵀ))) := by
  set f₀ := X₀ * S₀ * V₀ᵀ with hf₀
  set f₁ := X₁ * S₁ * V₀ᵀ with hf₁
  set f₂ := X₁ * S₂ * V₀ᵀ with hf₂
  set a := projX G X₁ (projV G V₀ (A f₀)) with ha
  set b := projX G X₁ (projV G V₀ (A f₁)) with hb
  set c := projX G X₁ (projV G V₀ (Lh G E f₁)) with hc
  have hsub : projX G X₁ (projV G V₀ (A f₀ - A f₁)) = a - b := by
    simp only [ha, hb, projX, projV, Matrix.sub_mul, Matrix.mul_sub, smul_sub]
  have hPf₁ : projX G X₁ f₁ = f₁ := by
    have := projX_mul_self G h.orthX₁ (V₀ * S₁ᵀ)
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, hf₁, Matrix.mul_assoc] using this
  -- the K-step in phase space
  have hK : (1 / Δt) • (f₁ - f₀) = projV G V₀ (A f₀) + (1 / ε) • projV G V₀ (Lh G E f₁) := by
    have h1 := congrArg (fun M => M * V₀ᵀ) h.kStep
    simp only [h.qrK, Matrix.add_mul, Matrix.smul_mul, Matrix.sub_mul] at h1
    simpa only [projV, smul_sub, hf₀, hf₁] using h1
  -- the K-step after applying `P_X^{n+1}`
  have hK' : (1 / Δt) • (f₁ - projX G X₁ f₀) = a + (1 / ε) • c := by
    have h1 := congrArg (projX G X₁) hK
    rwa [projX_smul, projX_sub, projX_add, projX_smul, hPf₁] at h1
  -- the S-step in phase space
  have hS : (1 / Δt) • (f₂ - f₁) = -b - (1 / ε) • c := by
    have h1 := congrArg (fun M => X₁ * M * V₀ᵀ) h.sStep
    simp only [Matrix.mul_sub, Matrix.mul_neg, Matrix.mul_smul, Matrix.sub_mul, Matrix.neg_mul,
      Matrix.smul_mul] at h1
    simpa only [hb, hc, hf₂, hf₁, projX, projV, Matrix.mul_smul, smul_smul, mul_comm G.dx G.dv,
      Matrix.mul_assoc, smul_sub] using h1
  have e1 : f₁ - projX G X₁ f₀ = Δt • (a + (1 / ε) • c) := by
    rw [← hK', smul_smul, mul_one_div_cancel hΔt.ne', one_smul]
  have e2 : f₂ - f₁ = Δt • (-b - (1 / ε) • c) := by
    rw [← hS, smul_smul, mul_one_div_cancel hΔt.ne', one_smul]
  have e3 : f₂ = (f₂ - f₁) + (f₁ - projX G X₁ f₀) + projX G X₁ f₀ := by abel
  rw [e3, e1, e2, hsub]
  simp only [smul_sub, smul_add, smul_neg]
  abel

/-- arXiv 2601.11900, **Thm 5.3 for Algorithm 1**: the output `f^{n+1} = X₁ S₃ V₁ᵀ` of one step of
the scheme satisfies (5.12) and (5.13), with the field `E^{n+1}` that the step has computed. -/
theorem IsIMEXStep.ap {poisson : (Fin Nx → ℝ) → Fin Nx → ℝ}
    {A : Phase Nx Nv → Phase Nx Nv} {ε Δt : ℝ} (hε : 0 < ε) (hNx : 0 < Nx) (hNv : 2 ≤ Nv)
    {X₀ X₁ : Matrix (Fin Nx) R ℝ} {V₀ V₁ : Matrix (Fin Nv) R ℝ} {S₀ S₁ S₂ S₃ : Matrix R R ℝ}
    {K₁ : Matrix (Fin Nx) R ℝ} {L₃ : Matrix (Fin Nv) R ℝ} {E : Fin Nx → ℝ}
    (h : IsIMEXStep G poisson A ε Δt X₀ X₁ V₀ V₁ S₀ S₁ S₂ S₃ K₁ L₃ E)
    (hκ : kappaH G E * Mmax G E < gammaH G E) {f f₂ : Phase Nx Nv}
    (hf : f = X₁ * S₃ * V₁ᵀ) (hf₂ : f₂ = X₁ * S₂ * V₀ᵀ) :
    normXV G (Lh G E f) ≤ thetaH G E *
        (ε * normXV G (residual G A Δt X₁ f f₂)
          + kappaH G E * Mmax G E * Real.sqrt G.Lv * normX G (density G f)) ∧
      normXV G (f - rhoM G E (density G f)) ≤ Mmax G E / gammaH G E * thetaH G E *
        (ε * normXV G (residual G A Δt X₁ f f₂)
          + kappaH G E * Mmax G E * Real.sqrt G.Lv * normX G (density G f)) := by
  have e1 : f = X₁ * L₃ᵀ := by
    rw [hf, h.qrL, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have e2 : f₂ = X₁ * (V₀ * S₂ᵀ)ᵀ := by
    rw [hf₂, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  exact (ap_property G E hNx hNv h.orthX₁ hε h.lStep hκ e1 e2).2

end Algorithm

/-! ### Non-vacuity and the false constant of the header -/

section NonVacuity

/-- arXiv 2601.11900, Algorithm 1, non-vacuity: the scheme has nonzero steps, on every grid and for
all `ε`, `Δt`: with `𝒜_h = 0`, the field `E = 0` and `f^n` a global Maxwellian of rank one, nothing
changes. -/
theorem exists_isIMEXStep {Nx Nv : ℕ} (G : Grid Nx Nv) (hNx : 0 < Nx) (hNv : 0 < Nv) (ε Δt : ℝ) :
    ∃ (X₀ X₁ : Matrix (Fin Nx) (Fin 1) ℝ) (V₀ V₁ : Matrix (Fin Nv) (Fin 1) ℝ)
      (S₀ S₁ S₂ S₃ : Matrix (Fin 1) (Fin 1) ℝ) (K₁ : Matrix (Fin Nx) (Fin 1) ℝ)
      (L₃ : Matrix (Fin Nv) (Fin 1) ℝ),
      IsIMEXStep G (fun _ _ => 0) (fun _ => 0) ε Δt X₀ X₁ V₀ V₁ S₀ S₁ S₂ S₃ K₁ L₃ (fun _ => 0) ∧
        X₀ * S₀ * V₀ᵀ ≠ 0 := by
  set E : Fin Nx → ℝ := fun _ => 0 with hE
  set p₀ : Fin Nx := ⟨0, hNx⟩ with hp₀
  set m : Fin Nv → ℝ := fun q => maxw G E p₀ q with hm
  have hmp : ∀ q, 0 < m q := fun q => maxw_pos G E hNv p₀ q
  have hdv := dv_pos G hNv
  have hdx := dx_pos G hNx
  have hNxR : (0 : ℝ) < Nx := by exact_mod_cast hNx
  have hsum : 0 < ∑ q, m q ^ 2 * G.dv := by
    have : Nonempty (Fin Nv) := ⟨⟨0, hNv⟩⟩
    exact Finset.sum_pos (fun q _ => mul_pos (pow_pos (hmp q) 2) hdv) Finset.univ_nonempty
  set n : ℝ := Real.sqrt (∑ q, m q ^ 2 * G.dv) with hn
  have hn0 : 0 < n := Real.sqrt_pos.2 hsum
  have hn2 : n ^ 2 = ∑ q, m q ^ 2 * G.dv := Real.sq_sqrt hsum.le
  set c : ℝ := 1 / Real.sqrt (Nx * G.dx) with hc
  have hc0 : 0 < c := div_pos one_pos (Real.sqrt_pos.2 (mul_pos hNxR hdx))
  have hc2 : c ^ 2 * (Nx * G.dx) = 1 := by
    have h1 := Real.sq_sqrt (mul_pos hNxR hdx).le
    have h2 := (Real.sqrt_pos.2 (mul_pos hNxR hdx)).ne'
    rw [hc, div_pow, one_pow, h1]
    field_simp
  set X : Matrix (Fin Nx) (Fin 1) ℝ := Matrix.of fun _ _ => c with hX
  set V : Matrix (Fin Nv) (Fin 1) ℝ := Matrix.of fun q _ => m q / n with hV
  have hmaxw : ∀ p (q : ℕ), maxw G E p q = maxw G E p₀ q := fun _ _ => rfl
  have hXV : X * Vᵀ = rhoM G E (fun _ => c / n) := by
    ext p q
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hX, hV, Matrix.of_apply,
      Fin.sum_univ_one, rhoM, hm, hmaxw p]
    ring
  have hL : Lh G E (X * Vᵀ) = 0 := by rw [hXV]; exact Lh_rhoM G E hNv _
  have hoX : G.dx • (Xᵀ * X) = 1 := by
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst hi hj
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply, hX, Matrix.of_apply,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul,
      Matrix.one_apply_eq]
    linear_combination hc2
  have hoV : G.dv • (Vᵀ * V) = 1 := by
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst hi hj
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply, hV, Matrix.of_apply,
      smul_eq_mul, Matrix.one_apply_eq]
    rw [Finset.mul_sum]
    have : ∑ q, G.dv * (m q / n * (m q / n)) = (∑ q, m q ^ 2 * G.dv) / n ^ 2 := by
      rw [Finset.sum_div]
      exact sum_congr rfl fun q _ => by field_simp
    rw [this, ← hn2]
    exact div_self (pow_pos hn0 2).ne'
  refine ⟨X, X, V, V, 1, 1, 1, 1, X, V, ?_, ?_⟩
  · refine ⟨hoX, hoV, hoX, hoV, rfl, ?_, by simp, ?_, ?_, by simp⟩
    · simp [hL]
    · simp [hL]
    · simp only [IsLStep, Matrix.transpose_one, Matrix.mul_one, hL]
      simp
  · intro h0
    have h1 := congrFun (congrFun h0 p₀) ⟨0, hNv⟩
    simp only [Matrix.mul_one, Matrix.mul_apply, Matrix.transpose_apply, hX, hV, Matrix.of_apply,
      Fin.sum_univ_one, Matrix.zero_apply] at h1
    exact (mul_pos hc0 (div_pos (hmp _) hn0)).ne' h1

end NonVacuity

section Counterexample

/-- The grid of `header_constant_false`: `Δx = 1/2`, `Δv = 1/3200`, `L_v = 1/1600`. -/
noncomputable def cxGrid : Grid 2 2 where
  xmin := 0
  xmax := 1
  vmin := -(1 / 3200)
  vmax := 1 / 3200
  x_lt := by norm_num
  v_lt := by norm_num

/-- The weights `β_p` of `header_constant_false`. -/
noncomputable def cxBeta : Fin 2 → ℝ := ![101 / 100, 99 / 100]

/-- The field of `header_constant_false`, for which `β_p = cxBeta p`. -/
noncomputable def cxE : Fin 2 → ℝ := fun p => -(6400 * Real.log (cxBeta p))

lemma cx_dx : cxGrid.dx = 1 / 2 := by norm_num [Grid.dx, cxGrid]

lemma cx_dv : cxGrid.dv = 1 / 3200 := by norm_num [Grid.dv, cxGrid]

lemma cx_Lv : cxGrid.Lv = 1 / 1600 := by norm_num [Grid.Lv, cxGrid]

lemma cx_beta0 : cxBeta 0 = 101 / 100 := by simp [cxBeta]

lemma cx_beta1 : cxBeta 1 = 99 / 100 := by simp [cxBeta]

lemma cx_beta_pos (p : Fin 2) : 0 < cxBeta p := by
  fin_cases p
  · simp [cxBeta]
  · simp [cxBeta]

lemma cx_alpha : alpha cxGrid 0 = 1 := by
  have h : cxGrid.v 0 + cxGrid.v (0 + 1) = 0 := by
    simp only [Grid.v, cx_dv]
    norm_num [cxGrid]
  simp only [alpha]
  rw [h]
  simp

lemma cx_beta (p : Fin 2) : beta cxGrid cxE p = cxBeta p := by
  simp only [beta, cxE, cx_dv]
  rw [show -(1 / 3200 / 2 * -(6400 * Real.log (cxBeta p))) = Real.log (cxBeta p) by ring,
    Real.exp_log (cx_beta_pos p)]

lemma cx_ratio (p : Fin 2) :
    maxw cxGrid cxE p 0 = cxBeta p ^ 2 * maxw cxGrid cxE p 1 := by
  have h := maxw_ratio cxGrid cxE p 0
  rwa [cx_alpha, cx_beta, one_mul] at h

lemma cx_sum (p : Fin 2) : maxw cxGrid cxE p 0 + maxw cxGrid cxE p 1 = 3200 := by
  have h := sum_maxw cxGrid cxE (by norm_num) p
  rw [Fin.sum_univ_two, cx_dv] at h
  simp only [Fin.val_zero, Fin.val_one] at h
  linarith

lemma cx_mid (p : Fin 2) : maxwMid cxGrid cxE p 0 = cxBeta p * maxw cxGrid cxE p 1 := by
  have h := maxwMid_div_right cxGrid cxE (by norm_num) p 0
  rw [cx_alpha, cx_beta, one_mul, div_eq_iff (maxw_pos cxGrid cxE (by norm_num) p _).ne'] at h
  exact h

lemma cx_M00 : 16159 / 10 ≤ maxw cxGrid cxE 0 0 ∧ maxw cxGrid cxE 0 0 ≤ 1617 := by
  have h1 := cx_ratio 0
  have h2 := cx_sum 0
  rw [cx_beta0] at h1
  constructor <;> linarith

lemma cx_M01 : maxw cxGrid cxE 0 1 ≤ 1585 ∧ 1584 ≤ maxw cxGrid cxE 0 1 := by
  have h1 := cx_ratio 0
  have h2 := cx_sum 0
  rw [cx_beta0] at h1
  constructor <;> linarith

lemma cx_M10 : maxw cxGrid cxE 1 0 ≤ 1617 := by
  have h1 := cx_ratio 1
  have h2 := cx_sum 1
  rw [cx_beta1] at h1
  linarith

lemma cx_M11 : 1616 ≤ maxw cxGrid cxE 1 1 ∧ maxw cxGrid cxE 1 1 ≤ 1617 := by
  have h1 := cx_ratio 1
  have h2 := cx_sum 1
  rw [cx_beta1] at h1
  constructor <;> linarith

lemma cx_mid_bounds (p : Fin 2) :
    1599 ≤ maxwMid cxGrid cxE p 0 ∧ maxwMid cxGrid cxE p 0 ≤ 1617 := by
  rw [cx_mid]
  fin_cases p
  · have := cx_M01
    simp only [Fin.zero_eta, cx_beta0]
    constructor <;> linarith [this.1, this.2]
  · have := cx_M11
    simp only [Fin.mk_one, cx_beta1]
    constructor <;> linarith [this.1, this.2]

lemma cx_Mmax : Mmax cxGrid cxE ≤ 1617 := by
  refine max_le (ciSup_le ?_) (ciSup_le ?_)
  · rintro ⟨p, q⟩
    fin_cases p <;> fin_cases q
    · exact cx_M00.2
    · exact cx_M01.1.trans (by norm_num)
    · exact cx_M10
    · exact cx_M11.2
  · rintro ⟨p, i⟩
    have hi : (i : ℕ) = 0 := by have := i.2; omega
    simp only [hi]
    exact (cx_mid_bounds p).2

lemma cx_Mmin : 1599 ≤ Mmin cxGrid cxE := by
  have : Nonempty (Fin 2 × Fin (2 - 1)) := ⟨(0, ⟨0, by norm_num⟩)⟩
  refine le_ciInf ?_
  rintro ⟨p, i⟩
  have hi : (i : ℕ) = 0 := by have := i.2; omega
  simp only [hi]
  exact (cx_mid_bounds p).1

lemma cx_lambda : lambdaN cxGrid = 20480000 := by
  have h : Real.pi / (2 * ((2 : ℕ) : ℝ)) = Real.pi / 4 := by norm_num
  have hs : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [lambdaN, cx_dv, h, Real.sin_pi_div_four, hs]
  norm_num

lemma cx_alphaMax : alphaMax cxGrid ≤ 1 := by
  have : Nonempty (Fin (2 - 1)) := ⟨⟨0, by norm_num⟩⟩
  refine ciSup_le fun i => ?_
  have hi : (i : ℕ) = 0 := by have := i.2; omega
  rw [hi, cx_alpha]

lemma cx_alphaMin : 1 ≤ alphaMin cxGrid := by
  have : Nonempty (Fin (2 - 1)) := ⟨⟨0, by norm_num⟩⟩
  refine le_ciInf fun i => ?_
  have hi : (i : ℕ) = 0 := by have := i.2; omega
  rw [hi, cx_alpha]

lemma cx_betaBar : betaBar cxGrid cxE = 1 := by
  simp only [betaBar, cx_beta, Fin.sum_univ_two, cx_beta0, cx_beta1]
  norm_num

lemma cx_deltaBeta : deltaBeta cxGrid cxE ≤ 1 / 100 := by
  refine ciSup_le fun p => ?_
  rw [cx_betaBar, cx_beta]
  fin_cases p
  · simp only [Fin.zero_eta, cx_beta0]
    norm_num [abs_le]
  · simp only [Fin.mk_one, cx_beta1]
    rw [abs_le]
    norm_num

lemma cx_Cbeta : Cbeta cxGrid cxE ≤ 10102 / 10000 := by
  refine ciSup_le fun p => ?_
  rw [cx_betaBar, cx_beta, mul_one]
  fin_cases p
  · simp only [Fin.zero_eta, cx_beta0]
    norm_num
  · simp only [Fin.mk_one, cx_beta1]
    norm_num

lemma cx_kappa : kappaH cxGrid cxE ≤ 411700 := by
  have h0 := deltaBeta_nonneg cxGrid cxE
  have h1 := Cbeta_nonneg cxGrid cxE (by norm_num)
  have h2 := alphaMax_pos cxGrid (le_refl 2)
  have h3 := cx_alphaMax
  have h4 := cx_alphaMin
  have h5 := cx_deltaBeta
  have h6 := cx_Cbeta
  have h7 : 2 / (alphaMin cxGrid * (1 / 3200 : ℝ) ^ 2) ≤ 20480000 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have h8 : 2 * alphaMax cxGrid / (1 / 3200 : ℝ) ^ 2 ≤ 20480000 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  rw [kappaH, cx_dv]
  calc deltaBeta cxGrid cxE * (2 * alphaMax cxGrid / (1 / 3200) ^ 2
        + Cbeta cxGrid cxE * (2 / (alphaMin cxGrid * (1 / 3200) ^ 2)))
      ≤ (1 / 100) * (20480000 + 10102 / 10000 * 20480000) := by gcongr
    _ ≤ 411700 := by norm_num

/-- The sharper bound of `Mmax * Lv` used for the root in `gammaH`. -/
lemma cx_sqrt {x : ℝ} (hx : x = Mmax cxGrid cxE * cxGrid.Lv) : Real.sqrt x ≤ 10054 / 10000 := by
  have h := cx_Mmax
  apply Real.sqrt_le_iff.2
  refine ⟨by norm_num, ?_⟩
  rw [hx, cx_Lv]
  nlinarith

lemma cx_gamma : 8100000000 ≤ gammaH cxGrid cxE := by
  have h1 := cx_Mmin
  have h2 : Real.sqrt (cxGrid.Lv * Mmax cxGrid cxE) ≤ 10054 / 10000 := cx_sqrt (mul_comm _ _)
  have h3 := Real.sqrt_nonneg (cxGrid.Lv * Mmax cxGrid cxE)
  rw [gammaH, cx_lambda, le_div_iff₀ (by positivity)]
  have h4 : (1 + Real.sqrt (cxGrid.Lv * Mmax cxGrid cxE)) ^ 2 ≤ (20054 / 10000) ^ 2 := by
    gcongr
    linarith
  calc 8100000000 * (1 + Real.sqrt (cxGrid.Lv * Mmax cxGrid cxE)) ^ 2
      ≤ 8100000000 * (20054 / 10000) ^ 2 := by gcongr
    _ ≤ 1599 * 20480000 := by norm_num
    _ ≤ _ := by gcongr

/-- The spatial basis of `header_constant_false`, orthonormal for `Δx = 1/2`. -/
def cxX : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of fun _ _ => 1

/-- The velocity factor of `header_constant_false`. -/
noncomputable def cxL : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of fun q _ => ![9999 / 10000, 1] q

lemma cx_f (p q : Fin 2) : (cxX * cxLᵀ) p q = ![9999 / 10000, 1] q := by
  simp [Matrix.mul_apply, cxX, cxL]

lemma cx_alphaR0 : alphaR cxGrid 0 = 1 := by simp [alphaR, cx_alpha]

lemma cx_alphaR1 : alphaR cxGrid 1 = 0 := by simp [alphaR]

lemma cx_alphaL0 : alphaL cxGrid 0 = 0 := by simp [alphaL]

lemma cx_alphaL1 : alphaL cxGrid 1 = 1 := by simp [alphaL, cx_alpha]

lemma cx_Lh0' (f : Phase 2 2) (p : Fin 2) : Lh cxGrid cxE f p 0
    = (cxBeta p * f p 1 - (cxBeta p)⁻¹ * f p 0) / (1 / 3200) ^ 2 := by
  rw [Lh_stencil cxGrid cxE (by norm_num), cx_dv]
  have h1 : extV (f p) (0 + 1) = f p 1 := by simp [extV]
  simp only [Fin.val_zero, cx_alphaR0, cx_alphaL0, cx_beta, h1]
  simp

lemma cx_Lh1' (f : Phase 2 2) (p : Fin 2) : Lh cxGrid cxE f p 1
    = -((cxBeta p * f p 1 - (cxBeta p)⁻¹ * f p 0) / (1 / 3200) ^ 2) := by
  rw [Lh_stencil cxGrid cxE (by norm_num), cx_dv]
  have h1 : extV (f p) (1 - 1) = f p 0 := by simp [extV]
  simp only [Fin.val_one, cx_alphaR1, cx_alphaL1, cx_beta, h1]
  simp
  ring

lemma cx_Lh0 (p : Fin 2) : Lh cxGrid cxE (cxX * cxLᵀ) p 0
    = (cxBeta p - (cxBeta p)⁻¹ * (9999 / 10000)) / (1 / 3200) ^ 2 := by
  rw [cx_Lh0', cx_f, cx_f]
  simp

lemma cx_Lh1 (p : Fin 2) : Lh cxGrid cxE (cxX * cxLᵀ) p 1
    = -((cxBeta p - (cxBeta p)⁻¹ * (9999 / 10000)) / (1 / 3200) ^ 2) := by
  rw [cx_Lh1', cx_f, cx_f]
  simp

lemma cx_proj : (Lh cxGrid cxE (cxX * cxLᵀ))ᵀ * cxX = 0 := by
  have h : cxBeta 0 - (cxBeta 0)⁻¹ * (9999 / 10000)
      + (cxBeta 1 - (cxBeta 1)⁻¹ * (9999 / 10000)) = 0 := by
    rw [cx_beta0, cx_beta1]
    norm_num
  have h0 : Lh cxGrid cxE (cxX * cxLᵀ) 0 0 + Lh cxGrid cxE (cxX * cxLᵀ) 1 0 = 0 := by
    rw [cx_Lh0, cx_Lh0, ← add_div, h, zero_div]
  have h1 : Lh cxGrid cxE (cxX * cxLᵀ) 0 1 + Lh cxGrid cxE (cxX * cxLᵀ) 1 1 = 0 := by
    rw [cx_Lh1, cx_Lh1, ← neg_add, ← add_div, h, zero_div, neg_zero]
  have hX : ∀ p i, cxX p i = 1 := fun _ _ => rfl
  ext q i
  simp only [Matrix.mul_apply, Matrix.transpose_apply, hX, mul_one, Fin.sum_univ_two,
    Matrix.zero_apply]
  fin_cases q
  · exact h0
  · exact h1

lemma cx_density : density cxGrid (cxX * cxLᵀ) = fun _ => 19999 / 10000 / 3200 := by
  funext p
  simp only [density, ipV, Pi.one_apply, mul_one, Fin.sum_univ_two, cx_f, cx_dv]
  norm_num

lemma cx_normX : normX cxGrid (fun _ => (19999 : ℝ) / 10000 / 3200) = 19999 / 10000 / 3200 := by
  have : ipX cxGrid (fun _ => (19999 : ℝ) / 10000 / 3200) (fun _ => (19999 : ℝ) / 10000 / 3200)
      = (19999 / 10000 / 3200) ^ 2 := by
    simp only [ipX, Fin.sum_univ_two, cx_dx]
    ring
  rw [normX, this, Real.sqrt_sq (by norm_num)]

lemma cx_lhs : 99 / 800000 ≤ normXV cxGrid
    (cxX * cxLᵀ - rhoM cxGrid cxE (density cxGrid (cxX * cxLᵀ))) := by
  set g := cxX * cxLᵀ - rhoM cxGrid cxE (density cxGrid (cxX * cxLᵀ)) with hg
  have h00 : g 0 0 ≤ -(99 / 10000) := by
    have h := cx_M00.1
    simp only [hg, Matrix.sub_apply, cx_f, rhoM, Matrix.of_apply, cx_density]
    simp only [Fin.val_zero, Matrix.cons_val_zero]
    nlinarith
  apply Real.le_sqrt_of_sq_le
  simp only [ipXV, Fin.sum_univ_two, cx_dx, cx_dv]
  nlinarith [mul_self_nonneg (g 0 1), mul_self_nonneg (g 1 0), mul_self_nonneg (g 1 1)]

/-- arXiv 2601.11900, Thm 5.3: **the constant in the list this slice started from is false.**  That
list states (5.13) with the factor `√(M_max L_v)`; the paper, in both arXiv versions, has
`M_max √L_v` (`ap_property`).  Since `√(M_max L_v)` is smaller when `M_max > 1`, the quoted
inequality is a stronger claim, and it fails on a concrete instance: two spatial and two velocity
cells, `L_v = 1/1600`, a nonconstant field, `r = 1`, `𝒜_h = 0`, `f^{(2)} = f^{n+1}`, `ε = Δt = 1`,
with Assumption 5.1 satisfied.  Here `‖f - ρ M‖ ≈ 2.5 ⋅ 10⁻⁴` and the quoted right-hand side is
about `5.6 ⋅ 10⁻⁵`.  For `L_v ≥ 1` the quoted inequality does hold (`ap_property_header`).  This
also shows that the hypotheses of Thm 5.3 can hold for a nonconstant field. -/
theorem header_constant_false :
    ∃ (G : Grid 2 2) (E : Fin 2 → ℝ) (X : Matrix (Fin 2) (Fin 1) ℝ) (A : Phase 2 2 → Phase 2 2)
      (ε Δt : ℝ) (L₂ L₃ : Matrix (Fin 2) (Fin 1) ℝ),
      0 < ε ∧ 0 < Δt ∧ G.dx • (Xᵀ * X) = 1 ∧ IsLStep G E A ε Δt X L₂ L₃ ∧ E 0 ≠ E 1 ∧
        kappaH G E * Mmax G E < gammaH G E ∧
        ¬ normXV G (X * L₃ᵀ - rhoM G E (density G (X * L₃ᵀ))) ≤
          Mmax G E / gammaH G E * thetaH G E *
            (ε * normXV G (residual G A Δt X (X * L₃ᵀ) (X * L₂ᵀ))
              + kappaH G E * Real.sqrt (Mmax G E * G.Lv) * normX G (density G (X * L₃ᵀ))) := by
  have hNv : (2 : ℕ) ≤ 2 := le_rfl
  have hγ := gammaH_pos cxGrid cxE (by norm_num) hNv
  have hm0 := Mmax_pos cxGrid cxE (by norm_num) (by norm_num)
  have hk0 := kappaH_nonneg cxGrid cxE (by norm_num) hNv
  have hm := cx_Mmax
  have hk := cx_kappa
  have hg := cx_gamma
  have hkm : kappaH cxGrid cxE * Mmax cxGrid cxE ≤ 411700 * 1617 := by gcongr
  have hκ : kappaH cxGrid cxE * Mmax cxGrid cxE < gammaH cxGrid cxE := by
    norm_num at hkm
    linarith
  have hE : cxE 0 ≠ cxE 1 := by
    intro h
    have h1 := cx_beta 0
    rw [beta, h, ← beta, cx_beta, cx_beta0, cx_beta1] at h1
    norm_num at h1
  refine ⟨cxGrid, cxE, cxX, fun _ => 0, 1, 1, cxL, cxL, one_pos, one_pos, ?_, ?_, hE, hκ, ?_⟩
  · ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst hi hj
    simp [Matrix.mul_apply, cxX, cx_dx]
  · simp only [IsLStep, cx_proj]
    simp
  · intro hcontra
    have hres :
        normXV cxGrid (residual cxGrid (fun _ => 0) 1 cxX (cxX * cxLᵀ) (cxX * cxLᵀ)) = 0 := by
      have : residual cxGrid (fun _ => (0 : Phase 2 2)) 1 cxX (cxX * cxLᵀ) (cxX * cxLᵀ) = 0 := by
        simp [residual, projX]
      rw [this]
      simp [normXV, ipXV]
    rw [hres, cx_density, cx_normX, mul_zero, zero_add] at hcontra
    set s := Real.sqrt (Mmax cxGrid cxE * cxGrid.Lv) with hs
    have hs1 : s ≤ 10054 / 10000 := cx_sqrt rfl
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hD : 0 < gammaH cxGrid cxE - kappaH cxGrid cxE * Mmax cxGrid cxE := by linarith
    have hrhs : Mmax cxGrid cxE / gammaH cxGrid cxE * thetaH cxGrid cxE *
        (kappaH cxGrid cxE * s * (19999 / 10000 / 3200)) ≤ 1 / 10000 := by
      have e : Mmax cxGrid cxE / gammaH cxGrid cxE * thetaH cxGrid cxE *
          (kappaH cxGrid cxE * s * (19999 / 10000 / 3200))
          = Mmax cxGrid cxE * (kappaH cxGrid cxE * s * (19999 / 10000 / 3200)) /
            (gammaH cxGrid cxE - kappaH cxGrid cxE * Mmax cxGrid cxE) := by
        rw [thetaH]
        field_simp
      rw [e, div_le_iff₀ hD]
      have h1 : Mmax cxGrid cxE * (kappaH cxGrid cxE * s * (19999 / 10000 / 3200))
          ≤ 1617 * (411700 * (10054 / 10000) * (19999 / 10000 / 3200)) := by gcongr
      have h2 : (411700 : ℝ) * 1617 = 665718900 := by norm_num
      nlinarith
    have hlhs := cx_lhs
    rw [cx_density] at hlhs
    linarith [hcontra.trans hrhs, (by norm_num : (1 : ℝ) / 10000 < 99 / 800000)]

/-- arXiv 2601.11900, a caveat on the stability of Algorithm 1: `ℒ_h` is not dissipative for the
unweighted inner product `⟨·,·⟩ₓᵥʰ`, in which `P_X` and `P_V` are orthogonal, as soon as the field
is nonzero.  It is dissipative for the `1/M`-weighted product only (`dissipation_identity`), and
that product depends on `(x, v)`.  So the hypothesis `⟪A x, x⟫ ≤ 0` of the library's abstract
`hybridKSL_norm_le_perturbed` fails for `A = ℒ_h`, and that theorem does not give the stability of
Algorithm 1.  The paper does not claim such a stability theorem. -/
theorem Lh_not_dissipative :
    ∃ (G : Grid 2 2) (E : Fin 2 → ℝ) (f : Phase 2 2), 0 < ipXV G (Lh G E f) f := by
  refine ⟨cxGrid, cxE, Matrix.of fun p q => if p = 0 then ![20402 / 10000, 20201 / 10000] q else 0,
    ?_⟩
  simp only [ipXV, Fin.sum_univ_two, cx_Lh0', cx_Lh1', cx_dx, cx_dv, cx_beta0, cx_beta1]
  simp
  norm_num

end Counterexample

/-! ### The grid in the core kinetic vocabulary -/

section KineticCore

variable {Nx Nv : ℕ} (G : Grid Nx Nv)

/-- **The grid as a core phase grid**: the cell sizes `Δx` and `Δv` as weights of a
`Kinetic.PhaseGrid`. The velocity weights have total mass `L_v` (`Lv_eq`), not one, so they are
not a `Kinetic.Quadrature` without dividing by `L_v`. -/
noncomputable def Grid.toPhaseGrid : Kinetic.PhaseGrid (Fin Nx) (Fin Nv) where
  wx := fun _ => G.dx
  wv := fun _ => G.dv
  wx_pos := fun p => dx_pos G p.pos
  wv_pos := fun q => dv_pos G q.pos

/-- The density `ρ = ⟨f, 1⟩ᵥʰ = ∑_q f_{pq} Δv` is the core `Kinetic.density` with the velocity
weights `Δv` of the grid. -/
theorem density_eq_kinetic (f : Phase Nx Nv) :
    density G f = Kinetic.density G.toPhaseGrid.wv f := by
  funext p
  simp [density, ipV, Kinetic.density_apply, Grid.toPhaseGrid, mul_comm]

@[simp] lemma Grid.toPhaseGrid_wx (p : Fin Nx) : G.toPhaseGrid.wx p = G.dx := rfl

@[simp] lemma Grid.toPhaseGrid_wv (q : Fin Nv) : G.toPhaseGrid.wv q = G.dv := rfl

/-- The bridge at the grid of the counterexample, with `Δv = 1 / 3200`. -/
example (f : Phase 2 2) :
    cxGrid.toPhaseGrid.wv 0 = 1 / 3200 ∧
      density cxGrid f = Kinetic.density cxGrid.toPhaseGrid.wv f :=
  ⟨cx_dv, density_eq_kinetic cxGrid f⟩

end KineticCore

end LeanDLRA.Literature.P2601_11900
