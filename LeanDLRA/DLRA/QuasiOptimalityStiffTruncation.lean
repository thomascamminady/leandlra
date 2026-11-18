import LeanDLRA.DLRA.QuasiOptimalityStiff
import LeanDLRA.DLRA.QuasiOptimalityDefect
import LeanDLRA.Matrix.Frobenius

/-!
# Quasi-optimality against the truncated SVD for fields with a tangential stiff part

Let `F(t, Z) = S(t, Z) + G(t, Z)` with `S` tangential on the matrices of rank `r` (main case
`S(Z) = M Z + Z N`), `A` a solution of `Ȧ = F(t, A)` with a gap `σ_r(A) < σ_{r-1}(A)` and
`T = T_r(A)` its truncated singular value decomposition, with the tail `R = A - T`. This file
assembles the bounds of `LeanDLRA/DLRA/QuasiOptimalityStiff.lean` for the reference curve `T`:
with `ρ = σ_{r-1}(A)`, `τ = σ_r(A)` and

  `k = ℓ + ν/ρ + ν/(ρ - ε) + μ ε/ρ² + L ε/ρ`,

a DLRA solution `Y` of rank `r` satisfies

  `‖Y t - T t‖ ≤ e^{∫ₐᵗ k} δ + ∫ₐᵗ e^{∫ₛᵗ k} (L ‖T s - A s‖ + ρ/(ρ - τ) ω s + c s) ds`.

Here `ℓ` is the one-sided Lipschitz constant of `F`, `L` the Lipschitz constant of `G`,
`μ ≥ ‖G(A)‖`, `ν ≥ ‖(1 - P(T)) G(A)‖`, `ω ≥ ‖(T⁺)ᵀ Zᵀ R + R Zᵀ (T⁺)ᵀ‖` for `Z = F(A)` (the
Weingarten map of the velocity, which sees only the mixed blocks of `Z`) and
`c ≥ ‖P(T) (S(A) - S(T))‖`. For a linear `S` with adjoint `S'` one may take `c = κ ‖A - T‖` with
`‖(1 - P(T)) S' P(T) w‖ ≤ κ ‖w‖`: the stiff part enters the source through the failure of the
tangent space at `T` to be invariant under `S'`, and not through its norm. All norms of matrices
are Frobenius norms.

## Main results

* `IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_tangent_add_of_norm_pinv_le`:
  the bound with the number `c`.
* `IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_tangent_add_of_adjoint`: the
  bound with `c = κ ‖T - A‖` for a linear tangential part with an adjoint.
* `IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_sylvester_add`: the case
  `F(t, Z) = M Z + Z N + G(t, Z)`, where `S' W = Mᵀ W + W Nᵀ`.

## References

* [KochLubich2007]
* [KieriVandereycken2019]
* [CarrelVandereycken2023]
-/

open Set Finset Matrix Filter
open scoped Topology RealInnerProductSpace

namespace LeanDLRA

section Truncation

open scoped LeanDLRA.Frobenius
open EckartYoung

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **Quasi-optimality against the truncated SVD for a field with a tangential part.** Let
`F = S + G` be one-sided Lipschitz with the constant `ℓ`, `G` be `L`-Lipschitz, `S` map `Y t` and
`T t = T_r(A t)` into their tangent spaces, `A` solve `Ȧ = F(t, A)` on `[a, b]` with the gap
`σ_r(A t) < σ_{r-1}(A t)`, and `Y` be a DLRA solution of rank `r`. Write `R = A - T`,
`Z t = F(t, A t)`, `ρ = σ_{r-1}(A ·)`, `τ = σ_r(A ·)`. Let `μ`, `ν`, `ω`, `c`, `ε` be continuous
with `‖G(t, A t)‖ ≤ μ t`, `‖(1 - P(T t)) G(t, A t)‖ ≤ ν t`,

  `‖(T⁺)ᵀ Zᵀ R + R Zᵀ (T⁺)ᵀ‖ ≤ ω t`,   `‖P(T t) (S(t, A t) - S(t, T t))‖ ≤ c t`

and `0 ≤ ε t < ρ t`. With `k = ℓ + ν/ρ + ν/(ρ - ε) + μ ε/ρ² + L ε/ρ`: if `‖Y a - T a‖ ≤ δ` and

  `e^{∫ₐᵗ k} δ + ∫ₐᵗ e^{∫ₛᵗ k} (L ‖T s - A s‖ + (ρ s/(ρ s - τ s) ω s + c s)) ds < ε t`

on `[a, b]`, then `‖Y t - T t‖` is at most the left-hand side on `[a, b]`. Neither a Lipschitz
constant nor a bound of `S` occurs. -/
theorem IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_tangent_add_of_norm_pinv_le
    {r : ℕ} {F S G : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A Y : ℝ → Matrix m n ℝ}
    {μ ν ω c ε : ℝ → ℝ} {a b ℓ L δ : ℝ} (hY : IsDLRASolution r F Y a b)
    (hFS : ∀ t Z, F t Z = S t Z + G t Z)
    (hS : ∀ t ∈ Ico a b, tangentProjAt (Y t) (S t (Y t)) = S t (Y t))
    (hST : ∀ t ∈ Ico a b, tangentProjAt (truncation (A t) r) (S t (truncation (A t) r)) =
      S t (truncation (A t) r))
    (hℓ : IsOneSidedLipschitzField F ℓ) (hL : 0 ≤ L) (hG : IsLipschitzField G L)
    (hA : ODESolution F A a b) (hμc : ContinuousOn μ (Icc a b))
    (hνc : ContinuousOn ν (Icc a b)) (hωc : ContinuousOn ω (Icc a b))
    (hcc : ContinuousOn c (Icc a b)) (hεc : ContinuousOn ε (Icc a b))
    (hμ : ∀ t ∈ Ico a b, ‖G t (A t)‖ ≤ μ t)
    (hν : ∀ t ∈ Ico a b,
      ‖G t (A t) - tangentProjAt (truncation (A t) r) (G t (A t))‖ ≤ ν t)
    (hω : ∀ t ∈ Ico a b,
      ‖(truncation (A t) r).pinvᵀ * (F t (A t))ᵀ * (A t - truncation (A t) r) +
        (A t - truncation (A t) r) * (F t (A t))ᵀ * (truncation (A t) r).pinvᵀ‖ ≤ ω t)
    (hc : ∀ t ∈ Ico a b,
      ‖tangentProjAt (truncation (A t) r) (S t (A t) - S t (truncation (A t) r))‖ ≤ c t)
    (hgap : ∀ t ∈ Icc a b, (toEuclideanLin (A t)).singularValues r <
      (toEuclideanLin (A t)).singularValues (r - 1))
    (hε0 : ∀ t ∈ Icc a b, 0 ≤ ε t)
    (hερ : ∀ t ∈ Icc a b, ε t < (toEuclideanLin (A t)).singularValues (r - 1))
    (hδ : ‖Y a - truncation (A a) r‖ ≤ δ)
    (hB : ∀ t ∈ Icc a b,
      Real.exp (∫ u in a..t, (ℓ + ν u / (toEuclideanLin (A u)).singularValues (r - 1) +
        ν u / ((toEuclideanLin (A u)).singularValues (r - 1) - ε u) +
        μ u * ε u / (toEuclideanLin (A u)).singularValues (r - 1) ^ 2 +
        L * ε u / (toEuclideanLin (A u)).singularValues (r - 1))) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t,
          (ℓ + ν u / (toEuclideanLin (A u)).singularValues (r - 1) +
          ν u / ((toEuclideanLin (A u)).singularValues (r - 1) - ε u) +
          μ u * ε u / (toEuclideanLin (A u)).singularValues (r - 1) ^ 2 +
          L * ε u / (toEuclideanLin (A u)).singularValues (r - 1))) *
          (L * ‖truncation (A s) r - A s‖ +
            ((toEuclideanLin (A s)).singularValues (r - 1) /
              ((toEuclideanLin (A s)).singularValues (r - 1) -
                (toEuclideanLin (A s)).singularValues r) * ω s + c s)) < ε t) :
    ∀ t ∈ Icc a b, ‖Y t - truncation (A t) r‖ ≤
      Real.exp (∫ u in a..t, (ℓ + ν u / (toEuclideanLin (A u)).singularValues (r - 1) +
        ν u / ((toEuclideanLin (A u)).singularValues (r - 1) - ε u) +
        μ u * ε u / (toEuclideanLin (A u)).singularValues (r - 1) ^ 2 +
        L * ε u / (toEuclideanLin (A u)).singularValues (r - 1))) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t,
          (ℓ + ν u / (toEuclideanLin (A u)).singularValues (r - 1) +
          ν u / ((toEuclideanLin (A u)).singularValues (r - 1) - ε u) +
          μ u * ε u / (toEuclideanLin (A u)).singularValues (r - 1) ^ 2 +
          L * ε u / (toEuclideanLin (A u)).singularValues (r - 1))) *
          (L * ‖truncation (A s) r - A s‖ +
            ((toEuclideanLin (A s)).singularValues (r - 1) /
              ((toEuclideanLin (A s)).singularValues (r - 1) -
                (toEuclideanLin (A s)).singularValues r) * ω s + c s)) := by
  intro t ht
  have hab : a ≤ b := ht.1.trans ht.2
  have hr : 0 < r := Nat.pos_of_ne_zero fun h0 => by
    subst h0
    exact lt_irrefl _ (hgap a ⟨le_rfl, hab⟩)
  have hσpos : ∀ s ∈ Icc a b, 0 < (toEuclideanLin (A s)).singularValues (r - 1) :=
    fun s hs => ((toEuclideanLin (A s)).singularValues_nonneg r).trans_lt (hgap s hs)
  have hσc' : ∀ i : ℕ, Continuous fun Z : Matrix m n ℝ => (toEuclideanLin Z).singularValues i :=
    fun i => (LipschitzWith.of_dist_le_mul (K := 1) fun Z Z' => by
      rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
      exact WeylSingular.abs_singularValues_sub_le_frobenius Z Z' i).continuous
  have hσc : ∀ i : ℕ, ContinuousOn (fun t => (toEuclideanLin (A t)).singularValues i)
      (Icc a b) := fun i => (hσc' i).comp_continuousOn hA.cont
  have hρc := hσc (r - 1)
  have hτc := hσc r
  refine hY.norm_sub_le_integral_exp_integral_of_tangent_add_of_integral_lt (A := A)
    (X := fun t => truncation (A t) r)
    (X' := fun t => fderiv ℝ (fun B => truncation B r) (A t) (F t (A t)))
    (ρ := fun t => (toEuclideanLin (A t)).singularValues (r - 1)) (μ := μ) (ν := ν)
    (d := fun s => (toEuclideanLin (A s)).singularValues (r - 1) /
      ((toEuclideanLin (A s)).singularValues (r - 1) -
        (toEuclideanLin (A s)).singularValues r) * ω s + c s)
    (ε := ε) hFS hS hℓ hL hG hA.cont hρc hμc hνc
    (((hρc.div (hρc.sub hτc) fun u hu => (sub_pos.2 (hgap u hu)).ne').mul hωc).add hcc) hεc
    (fun s hs => (continuousAt_truncation (hgap s hs)).comp_continuousWithinAt (hA.cont s hs))
    (fun s hs => hasDerivWithinAt_truncation (hA.deriv s hs) (hgap s (Ico_subset_Icc_self hs)))
    (fun s hs => rank_truncation_of_le_singularValues (hσpos s hs) le_rfl)
    (fun s hs => le_singularValues_truncation hr (hσpos s hs) le_rfl) hμ hν
    (fun s hsb => ?_) hε0 hερ hδ hB t ht
  have hsI := Ico_subset_Icc_self hsb
  have h1 := norm_add_tangentProjAt_sub_le_norm_tangentProjAt_add_sub_add (hST s hsb)
    (S s (A s)) (G s (A s)) (fderiv ℝ (fun B => truncation B r) (A s) (F s (A s)))
  rw [← hFS] at h1
  exact h1.trans (add_le_add
    ((norm_tangentProjAt_truncation_sub_fderiv_le_div_sub_mul_norm_pinv hA hgap hsb).trans
      (mul_le_mul_of_nonneg_left (hω s hsb)
        (div_nonneg (hσpos s hsI).le (sub_pos.2 (hgap s hsI)).le))) (hc s hsb))

/-- **Quasi-optimality against the truncated SVD for a linear tangential part with an adjoint.**
In `IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_tangent_add_of_norm_pinv_le`
let `S(t, ·)` be additive with an adjoint `S'(t, ·)` (`⟪S Z, W⟫ = ⟪Z, S' W⟫`), and let `κ` be
continuous and nonnegative with

  `‖(1 - P(T t)) S'(t, P(T t) W)‖ ≤ κ t ‖W‖`   for all `W`.

Then `c = κ ‖T - A‖` is admissible: the source is

  `L ‖T s - A s‖ + ρ s/(ρ s - τ s) ω s + κ s ‖T s - A s‖`.

The number `κ` measures how far the tangent space at `T` is from being invariant under `S'`; it
vanishes if `S'` maps this tangent space into itself. -/
theorem IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_tangent_add_of_adjoint
    {r : ℕ} {F S S' G : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A Y : ℝ → Matrix m n ℝ}
    {μ ν ω κ ε : ℝ → ℝ} {a b ℓ L δ : ℝ} (hY : IsDLRASolution r F Y a b)
    (hFS : ∀ t Z, F t Z = S t Z + G t Z)
    (hS : ∀ t ∈ Ico a b, tangentProjAt (Y t) (S t (Y t)) = S t (Y t))
    (hST : ∀ t ∈ Ico a b, tangentProjAt (truncation (A t) r) (S t (truncation (A t) r)) =
      S t (truncation (A t) r))
    (hSsub : ∀ t Z W, S t (Z - W) = S t Z - S t W)
    (hadj : ∀ t Z W, ⟪S t Z, W⟫ = ⟪Z, S' t W⟫)
    (hℓ : IsOneSidedLipschitzField F ℓ) (hL : 0 ≤ L) (hG : IsLipschitzField G L)
    (hA : ODESolution F A a b) (hμc : ContinuousOn μ (Icc a b))
    (hνc : ContinuousOn ν (Icc a b)) (hωc : ContinuousOn ω (Icc a b))
    (hκc : ContinuousOn κ (Icc a b)) (hεc : ContinuousOn ε (Icc a b))
    (hμ : ∀ t ∈ Ico a b, ‖G t (A t)‖ ≤ μ t)
    (hν : ∀ t ∈ Ico a b,
      ‖G t (A t) - tangentProjAt (truncation (A t) r) (G t (A t))‖ ≤ ν t)
    (hω : ∀ t ∈ Ico a b,
      ‖(truncation (A t) r).pinvᵀ * (F t (A t))ᵀ * (A t - truncation (A t) r) +
        (A t - truncation (A t) r) * (F t (A t))ᵀ * (truncation (A t) r).pinvᵀ‖ ≤ ω t)
    (hκ0 : ∀ t ∈ Ico a b, 0 ≤ κ t)
    (hκ : ∀ t ∈ Ico a b, ∀ W,
      ‖S' t (tangentProjAt (truncation (A t) r) W) -
        tangentProjAt (truncation (A t) r) (S' t (tangentProjAt (truncation (A t) r) W))‖ ≤
        κ t * ‖W‖)
    (hgap : ∀ t ∈ Icc a b, (toEuclideanLin (A t)).singularValues r <
      (toEuclideanLin (A t)).singularValues (r - 1))
    (hε0 : ∀ t ∈ Icc a b, 0 ≤ ε t)
    (hερ : ∀ t ∈ Icc a b, ε t < (toEuclideanLin (A t)).singularValues (r - 1))
    (hδ : ‖Y a - truncation (A a) r‖ ≤ δ)
    (hB : ∀ t ∈ Icc a b,
      Real.exp (∫ u in a..t, (ℓ + ν u / (toEuclideanLin (A u)).singularValues (r - 1) +
        ν u / ((toEuclideanLin (A u)).singularValues (r - 1) - ε u) +
        μ u * ε u / (toEuclideanLin (A u)).singularValues (r - 1) ^ 2 +
        L * ε u / (toEuclideanLin (A u)).singularValues (r - 1))) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t,
          (ℓ + ν u / (toEuclideanLin (A u)).singularValues (r - 1) +
          ν u / ((toEuclideanLin (A u)).singularValues (r - 1) - ε u) +
          μ u * ε u / (toEuclideanLin (A u)).singularValues (r - 1) ^ 2 +
          L * ε u / (toEuclideanLin (A u)).singularValues (r - 1))) *
          (L * ‖truncation (A s) r - A s‖ +
            ((toEuclideanLin (A s)).singularValues (r - 1) /
              ((toEuclideanLin (A s)).singularValues (r - 1) -
                (toEuclideanLin (A s)).singularValues r) * ω s +
              κ s * ‖truncation (A s) r - A s‖)) < ε t) :
    ∀ t ∈ Icc a b, ‖Y t - truncation (A t) r‖ ≤
      Real.exp (∫ u in a..t, (ℓ + ν u / (toEuclideanLin (A u)).singularValues (r - 1) +
        ν u / ((toEuclideanLin (A u)).singularValues (r - 1) - ε u) +
        μ u * ε u / (toEuclideanLin (A u)).singularValues (r - 1) ^ 2 +
        L * ε u / (toEuclideanLin (A u)).singularValues (r - 1))) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t,
          (ℓ + ν u / (toEuclideanLin (A u)).singularValues (r - 1) +
          ν u / ((toEuclideanLin (A u)).singularValues (r - 1) - ε u) +
          μ u * ε u / (toEuclideanLin (A u)).singularValues (r - 1) ^ 2 +
          L * ε u / (toEuclideanLin (A u)).singularValues (r - 1))) *
          (L * ‖truncation (A s) r - A s‖ +
            ((toEuclideanLin (A s)).singularValues (r - 1) /
              ((toEuclideanLin (A s)).singularValues (r - 1) -
                (toEuclideanLin (A s)).singularValues r) * ω s +
              κ s * ‖truncation (A s) r - A s‖)) := by
  have hTc : ContinuousOn (fun s => truncation (A s) r) (Icc a b) := fun s hs =>
    (continuousAt_truncation (hgap s hs)).comp_continuousWithinAt (hA.cont s hs)
  refine hY.norm_sub_truncation_le_integral_exp_integral_of_tangent_add_of_norm_pinv_le
    (c := fun s => κ s * ‖truncation (A s) r - A s‖) hFS hS hST hℓ hL hG hA hμc hνc hωc
    (hκc.mul (hTc.sub hA.cont).norm) hεc hμ hν hω (fun s hsb => ?_) hgap hε0 hερ hδ hB
  rw [← hSsub, norm_sub_rev (truncation (A s) r) (A s)]
  exact (isOrthProj_tangentProjAt (truncation (A s) r)).norm_apply_le_mul_of_adjoint
    (hadj s) (hκ0 s hsb) (hκ s hsb) (tangentProjAt_truncation_sub_eq_zero (A s) r)

/-- **Stiffness-uniform quasi-optimality against the truncated SVD for Sylvester-stiff fields.**
Let `F(t, Z) = M Z + Z N + G(t, Z)` be one-sided Lipschitz with the constant `ℓ`, `G` be
`L`-Lipschitz, `A` solve `Ȧ = F(t, A)` on `[a, b]` with the gap `σ_r(A t) < σ_{r-1}(A t)`,
`T t = T_r(A t)`, and `Y` be a DLRA solution of rank `r`. With `μ`, `ν`, `ω`, `ε` as in
`IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_tangent_add_of_norm_pinv_le`
and a continuous `κ ≥ 0` with

  `‖(1 - P(T t)) (Mᵀ W' + W' Nᵀ)‖ ≤ κ t ‖W‖`,   `W' = P(T t) W`,   for all `W`,

the bound holds with the source `L ‖T - A‖ + ρ/(ρ - τ) ω + κ ‖T - A‖`. The matrices `M`, `N`
enter through `ℓ`, through the mixed blocks of `F(t, A t)` in `ω`, and through `κ`, which is
the size of the blocks of `Mᵀ` and `Nᵀ` that lead out of the dominant singular subspaces. -/
theorem IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_sylvester_add
    {r : ℕ} {M : Matrix m m ℝ} {N : Matrix n n ℝ}
    {G : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A Y : ℝ → Matrix m n ℝ}
    {μ ν ω κ ε : ℝ → ℝ} {a b ℓ L δ : ℝ}
    (hY : IsDLRASolution r (fun t Z => M * Z + Z * N + G t Z) Y a b)
    (hℓ : IsOneSidedLipschitzField (fun t Z => M * Z + Z * N + G t Z) ℓ) (hL : 0 ≤ L)
    (hG : IsLipschitzField G L)
    (hA : ODESolution (fun t Z => M * Z + Z * N + G t Z) A a b)
    (hμc : ContinuousOn μ (Icc a b)) (hνc : ContinuousOn ν (Icc a b))
    (hωc : ContinuousOn ω (Icc a b)) (hκc : ContinuousOn κ (Icc a b))
    (hεc : ContinuousOn ε (Icc a b)) (hμ : ∀ t ∈ Ico a b, ‖G t (A t)‖ ≤ μ t)
    (hν : ∀ t ∈ Ico a b,
      ‖G t (A t) - tangentProjAt (truncation (A t) r) (G t (A t))‖ ≤ ν t)
    (hω : ∀ t ∈ Ico a b,
      ‖(truncation (A t) r).pinvᵀ * (M * A t + A t * N + G t (A t))ᵀ *
          (A t - truncation (A t) r) +
        (A t - truncation (A t) r) * (M * A t + A t * N + G t (A t))ᵀ *
          (truncation (A t) r).pinvᵀ‖ ≤ ω t)
    (hκ0 : ∀ t ∈ Ico a b, 0 ≤ κ t)
    (hκ : ∀ t ∈ Ico a b, ∀ W,
      ‖Mᵀ * tangentProjAt (truncation (A t) r) W +
          tangentProjAt (truncation (A t) r) W * Nᵀ -
        tangentProjAt (truncation (A t) r) (Mᵀ * tangentProjAt (truncation (A t) r) W +
          tangentProjAt (truncation (A t) r) W * Nᵀ)‖ ≤ κ t * ‖W‖)
    (hgap : ∀ t ∈ Icc a b, (toEuclideanLin (A t)).singularValues r <
      (toEuclideanLin (A t)).singularValues (r - 1))
    (hε0 : ∀ t ∈ Icc a b, 0 ≤ ε t)
    (hερ : ∀ t ∈ Icc a b, ε t < (toEuclideanLin (A t)).singularValues (r - 1))
    (hδ : ‖Y a - truncation (A a) r‖ ≤ δ)
    (hB : ∀ t ∈ Icc a b,
      Real.exp (∫ u in a..t, (ℓ + ν u / (toEuclideanLin (A u)).singularValues (r - 1) +
        ν u / ((toEuclideanLin (A u)).singularValues (r - 1) - ε u) +
        μ u * ε u / (toEuclideanLin (A u)).singularValues (r - 1) ^ 2 +
        L * ε u / (toEuclideanLin (A u)).singularValues (r - 1))) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t,
          (ℓ + ν u / (toEuclideanLin (A u)).singularValues (r - 1) +
          ν u / ((toEuclideanLin (A u)).singularValues (r - 1) - ε u) +
          μ u * ε u / (toEuclideanLin (A u)).singularValues (r - 1) ^ 2 +
          L * ε u / (toEuclideanLin (A u)).singularValues (r - 1))) *
          (L * ‖truncation (A s) r - A s‖ +
            ((toEuclideanLin (A s)).singularValues (r - 1) /
              ((toEuclideanLin (A s)).singularValues (r - 1) -
                (toEuclideanLin (A s)).singularValues r) * ω s +
              κ s * ‖truncation (A s) r - A s‖)) < ε t) :
    ∀ t ∈ Icc a b, ‖Y t - truncation (A t) r‖ ≤
      Real.exp (∫ u in a..t, (ℓ + ν u / (toEuclideanLin (A u)).singularValues (r - 1) +
        ν u / ((toEuclideanLin (A u)).singularValues (r - 1) - ε u) +
        μ u * ε u / (toEuclideanLin (A u)).singularValues (r - 1) ^ 2 +
        L * ε u / (toEuclideanLin (A u)).singularValues (r - 1))) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t,
          (ℓ + ν u / (toEuclideanLin (A u)).singularValues (r - 1) +
          ν u / ((toEuclideanLin (A u)).singularValues (r - 1) - ε u) +
          μ u * ε u / (toEuclideanLin (A u)).singularValues (r - 1) ^ 2 +
          L * ε u / (toEuclideanLin (A u)).singularValues (r - 1))) *
          (L * ‖truncation (A s) r - A s‖ +
            ((toEuclideanLin (A s)).singularValues (r - 1) /
              ((toEuclideanLin (A s)).singularValues (r - 1) -
                (toEuclideanLin (A s)).singularValues r) * ω s +
              κ s * ‖truncation (A s) r - A s‖)) :=
  hY.norm_sub_truncation_le_integral_exp_integral_of_tangent_add_of_adjoint
    (S := fun _ Z => M * Z + Z * N) (S' := fun _ W => Mᵀ * W + W * Nᵀ) (fun _ _ => rfl)
    (fun _ _ => tangentProjAt_eq_self_iff.2 ⟨M, N, rfl⟩)
    (fun _ _ => tangentProjAt_eq_self_iff.2 ⟨M, N, rfl⟩)
    (fun _ Z W => by rw [Matrix.mul_sub, Matrix.sub_mul]; abel)
    (fun _ Z W => by
      rw [inner_add_left, inner_add_right, Frobenius.inner_mul_left, Frobenius.inner_mul_right])
    hℓ hL hG hA hμc hνc hωc hκc hεc hμ hν hω hκ0 hκ hgap hε0 hερ hδ hB

end Truncation

/-! ### Examples -/

namespace QuasiOptimalityStiffTruncationExamples

open scoped LeanDLRA.Frobenius
open QuasiOptimalityExamples EckartYoung

/-- The stiff matrix `diag(0, -lam)` of the example. -/
local notation "Mₛ" lam => (!![0, 0; 0, -lam] : Matrix (Fin 2) (Fin 2) ℝ)

private theorem stiff_mul_e₁ (lam : ℝ) : (Mₛ lam) * (e₁ * e₁ᵀ) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem stiff_transpose_mul_e₁ (lam : ℝ) : (Mₛ lam)ᵀ * (e₁ * e₁ᵀ) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem inner_stiff_mul_nonpos {lam : ℝ} (hlam : 0 ≤ lam)
    (z : Matrix (Fin 2) (Fin 2) ℝ) : ⟪(Mₛ lam) * z, z⟫ ≤ 0 := by
  have e : ⟪(Mₛ lam) * z, z⟫ = -(lam * (z 1 0 ^ 2 + z 1 1 ^ 2)) := by
    simp [Frobenius.inner_def, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    ring
  rw [e]
  nlinarith [sq_nonneg (z 1 0), sq_nonneg (z 1 1)]

/-- The field `F(Z) = diag(0, -lam) Z + Z 0 + e₁ e₁ᵀ` at `c e₁ e₁ᵀ` is `e₁ e₁ᵀ`. -/
private theorem field_smul_e₁ (lam c : ℝ) :
    (Mₛ lam) * (c • (e₁ * e₁ᵀ)) + c • (e₁ * e₁ᵀ) * (0 : Matrix (Fin 2) (Fin 2) ℝ) + e₁ * e₁ᵀ =
      e₁ * e₁ᵀ := by
  rw [Matrix.mul_smul, stiff_mul_e₁, smul_zero, Matrix.mul_zero, zero_add, zero_add]

private theorem truncation_smul_e₁ (c : ℝ) :
    truncation (c • (e₁ * e₁ᵀ)) 1 = c • (e₁ * e₁ᵀ) := by
  refine truncation_eq_self ?_
  rw [smul_e₁_mul]
  exact (rank_mul_le_right _ _).trans (by simpa using rank_le_card_height e₁ᵀ)

private theorem singularValues_one_smul_e₁_le (c : ℝ) :
    (toEuclideanLin (c • (e₁ * e₁ᵀ))).singularValues 1 ≤ 0 := by
  have h := singularValues_le_specNorm_sub (c • (e₁ * e₁ᵀ)) (c • (e₁ * e₁ᵀ)) (r := 1) (by
    rw [smul_e₁_mul]
    exact (rank_mul_le_right _ _).trans (by simpa using rank_le_card_height e₁ᵀ))
  rw [sub_self] at h
  exact h.trans ((Curvature.specNorm_le_frob 0).trans_eq norm_zero)

private theorem exp_half_lt_two : Real.exp (1 / 2) < 2 := by
  have h : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 / 2 : ℝ)]

/-- **Non-vacuity of
`IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_sylvester_add`**, and through it
of the two more general forms, with an arbitrarily large stiff part: `2 × 2` matrices, `r = 1`,
`F(Z) = diag(0, -lam) Z + Z 0 + e₁ e₁ᵀ` for any `lam ≥ 0` (`ℓ = 0`, `L = 0`), the solution
`A t = (1 + t) e₁ e₁ᵀ = T₁(A t)` and the DLRA solution `Y t = (5/4 + t) e₁ e₁ᵀ ≠ A t` on `[0, 1]`,
with `μ = 1`, `ν = ω = κ = 0`, `ε = 1/2`, `δ = 1/4`. The rate is at most `1/2` and the bound at
most `e^{1/2}/4 < 1/2`, for every `lam`: no constant depends on the stiff part. -/
example {lam : ℝ} (hlam : 0 ≤ lam) : ∃ B : ℝ → ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ‖(5 / 4 + t) • (e₁ * e₁ᵀ) - truncation ((1 + t) • (e₁ * e₁ᵀ)) 1‖ ≤ B t := by
  have hpos : ∀ t : ℝ, 0 ≤ t → (1 + t) ≠ 0 := fun t ht => ne_of_gt (by linarith)
  have hσ : ∀ t : ℝ, 0 ≤ t →
      (1 : ℝ) ≤ (toEuclideanLin ((1 + t) • (e₁ * e₁ᵀ))).singularValues (1 - 1) :=
    fun t ht => one_le_singularValues_smul_e₁ (by linarith)
  refine ⟨_, IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_sylvester_add
    (M := Mₛ lam) (N := 0) (G := fun _ _ => e₁ * e₁ᵀ)
    (A := fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) (Y := fun t : ℝ => (5 / 4 + t) • (e₁ * e₁ᵀ))
    (μ := fun _ => 1) (ν := fun _ => 0) (ω := fun _ => 0) (κ := fun _ => 0)
    (ε := fun _ => 1 / 2) (a := 0) (b := 1) (ℓ := 0) (L := 0) (δ := 1 / 4)
    ?_ ?_ le_rfl (fun _ _ _ => by simp) ?_ continuousOn_const continuousOn_const
    continuousOn_const continuousOn_const continuousOn_const (fun _ _ => norm_e₁_mul_le)
    (fun t ht => ?_) (fun t ht => ?_) (fun _ _ => le_rfl) (fun t ht W => ?_)
    (fun t ht => ?_) (fun _ _ => by norm_num) (fun t ht => ?_) ?_ (fun t ht => ?_)⟩
  · refine ⟨⟨fun s _ => (hasDerivAt_smul_e₁ (5 / 4) s).continuousAt.continuousWithinAt,
      fun s hs => ?_⟩, fun t ht => rank_smul_e₁ (ne_of_gt (by linarith [ht.1]))⟩
    have h := (hasDerivAt_smul_e₁ (5 / 4) s).hasDerivWithinAt (s := Ici s)
    convert h using 1
    change tangentProjAt ((5 / 4 + s) • (e₁ * e₁ᵀ)) ((Mₛ lam) * ((5 / 4 + s) • (e₁ * e₁ᵀ)) +
      (5 / 4 + s) • (e₁ * e₁ᵀ) * (0 : Matrix (Fin 2) (Fin 2) ℝ) + e₁ * e₁ᵀ) = e₁ * e₁ᵀ
    rw [field_smul_e₁]
    exact tangentProjAt_smul_e₁_apply (ne_of_gt (by linarith [hs.1]))
  · intro _ x y
    have e : (Mₛ lam) * x + x * (0 : Matrix (Fin 2) (Fin 2) ℝ) + e₁ * e₁ᵀ -
        ((Mₛ lam) * y + y * (0 : Matrix (Fin 2) (Fin 2) ℝ) + e₁ * e₁ᵀ) =
        (Mₛ lam) * (x - y) := by
      rw [Matrix.mul_zero, Matrix.mul_zero, Matrix.mul_sub]
      abel
    change ⟪(Mₛ lam) * x + x * (0 : Matrix (Fin 2) (Fin 2) ℝ) + e₁ * e₁ᵀ -
      ((Mₛ lam) * y + y * (0 : Matrix (Fin 2) (Fin 2) ℝ) + e₁ * e₁ᵀ), x - y⟫ ≤
      0 * ‖x - y‖ ^ 2
    rw [e, zero_mul]
    exact inner_stiff_mul_nonpos hlam _
  · refine ⟨fun s _ => (hasDerivAt_smul_e₁ 1 s).continuousAt.continuousWithinAt, fun s _ => ?_⟩
    have h := (hasDerivAt_smul_e₁ 1 s).hasDerivWithinAt (s := Ici s)
    convert h using 1
    exact field_smul_e₁ lam (1 + s)
  · rw [truncation_smul_e₁, tangentProjAt_smul_e₁_apply (hpos t ht.1), sub_self, norm_zero]
  · rw [truncation_smul_e₁, sub_self]
    simp
  · rw [truncation_smul_e₁, zero_mul]
    obtain ⟨M₁, N₁, h⟩ := tangentProjAt_eq_self_iff.1
      ((isOrthProj_tangentProjAt ((1 + t) • (e₁ * e₁ᵀ))).idem W)
    have h2 : (Mₛ lam)ᵀ * tangentProjAt ((1 + t) • (e₁ * e₁ᵀ)) W +
        tangentProjAt ((1 + t) • (e₁ * e₁ᵀ)) W * (0 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ =
        (Mₛ lam)ᵀ * M₁ * ((1 + t) • (e₁ * e₁ᵀ)) + (1 + t) • (e₁ * e₁ᵀ) * 0 := by
      have h3 : (Mₛ lam)ᵀ * ((1 + t) • (e₁ * e₁ᵀ)) = 0 := by
        rw [Matrix.mul_smul, stiff_transpose_mul_e₁, smul_zero]
      rw [h, Matrix.transpose_zero, Matrix.mul_zero, Matrix.mul_zero, add_zero, add_zero,
        Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc (Mₛ lam)ᵀ _ N₁, h3,
        Matrix.zero_mul, add_zero]
    rw [h2, tangentProjAt_eq_self_iff.2 ⟨_, _, rfl⟩, sub_self, norm_zero]
  · exact (singularValues_one_smul_e₁_le _).trans_lt (lt_of_lt_of_le one_pos (hσ t ht.1))
  · exact lt_of_lt_of_le (by norm_num) (hσ t ht.1)
  · rw [truncation_smul_e₁]
    have e : (5 / 4 + (0 : ℝ)) • (e₁ * e₁ᵀ) - (1 + (0 : ℝ)) • (e₁ * e₁ᵀ) =
        (1 / 4 : ℝ) • (e₁ * e₁ᵀ) := by module
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    nlinarith [norm_e₁_mul_le, norm_nonneg (e₁ * e₁ᵀ)]
  · simp only [zero_mul, zero_div, add_zero, zero_add, mul_zero,
      intervalIntegral.integral_zero, one_mul]
    have hI : ∫ u in (0 : ℝ)..t,
        1 / 2 / (toEuclideanLin ((1 + u) • (e₁ * e₁ᵀ))).singularValues (1 - 1) ^ 2 ≤ 1 / 2 := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := t)
        (C := 1 / 2)
        (f := fun u => 1 / 2 / (toEuclideanLin ((1 + u) • (e₁ * e₁ᵀ))).singularValues
          (1 - 1) ^ 2) (fun u hu => by
          rw [uIoc_of_le ht.1] at hu
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact div_le_self (by norm_num) (one_le_pow₀ (hσ u hu.1.le)))
      rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] at h
      nlinarith [le_abs_self (∫ u in (0 : ℝ)..t,
        1 / 2 / (toEuclideanLin ((1 + u) • (e₁ * e₁ᵀ))).singularValues (1 - 1) ^ 2), ht.2]
    have h2 := (Real.exp_le_exp.2 hI).trans_lt exp_half_lt_two
    linarith

end QuasiOptimalityStiffTruncationExamples

end LeanDLRA
