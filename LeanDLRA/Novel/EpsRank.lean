import LeanDLRA.Classical.WeylSingular
import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.LowRankDistance
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Kinetic.Defs

/-!
# Rank decay in the diffusive scaling

This module proves in discrete form that solutions of linear
transport in the diffusive scaling have `σ_{k+1}(f) ≲ ε^k`, with an explicit constant, and this
gives a rank schedule.

## Setting

`f ∈ ℝ^{X × V}` holds values at space points `i ∈ X` and velocity nodes `v ∈ V`.  The velocity
quadrature `q` has nodes `μ_v`, positive weights `w_v` with `∑ w_v = 1`, and `|μ_v| ≤ m`; `D` is a
spatial derivative matrix.  The equation is `∂_t f + ε⁻¹ D f diag(μ) = σ ε⁻² (⟨f⟩ ⊗ 1 - f)`.
`IsImplicitEuler` is the fully implicit Euler scheme, `IsIMEXEuler` has explicit transport.
Norms and singular values are those of `weighted q f = f diag(√w)`, as in Conjecture J.

## Main results

* `exists_moment_approx`, `distLR_le`, `singularValues_le`: for skew-symmetric `D` and
  well-prepared data `F₀ = ρ₀ ⊗ 1`, for all `ε, σ, τ > 0` and all `n, k`,
  `σ_{k+1}(F_n) ≤ dist(F_n, M_{≤ k}) ≤ (ε m / σ)^k ‖D^k ρ₀‖₂`, and the approximant has its rows
  in the fixed space `span {1, μ, …, μ^{k-1}}`.
* `exists_moment_approx_implicit`, `distLR_implicit_le`: arbitrary data, with an explicit initial
  layer `O(ε^{2n})`.
* `distLR_imex_uniform`: IMEX Euler, for any `D`, when `⟨μ⟩ = 0`, with a constant growing in `n`;
  `imex_unstable_of_mean_ne_zero`: `⟨μ⟩ = 0` cannot be dropped there;
  `exists_moment_approx_of_bound`, `distLR_imex_le`: a posteriori form, for any `D`.
* `distLR_flow_le`: the same bound for the exact flow in time, all `t ≥ 0`.
* `epsRank_le_of_le`, `epsRank_schedule`, `epsRank_ideas_formula`: the rank schedule.
* `telegraph_distLR` (exact value), `three_sharp_two`: the exponents `1` and `2`, and the constant
  in the case `k = 1`, cannot be improved. `ideas_formula_fails`: the schedule `⌈log tol / log ε⌉ +
  1` is false without a condition on `ε ‖D‖ / σ`.
* `existsUnique_implicitEuler`, `exists_imexEuler`, `exists_flow`, `centralDiff_skew`: the
  objects exist, and periodic central differences satisfy the hypothesis on `D`.

## Method

No Hilbert expansion, Neumann series, or smallness of `ε` is used.  The scheme reads
`F = S + c Ψ F`, with `c = -ε/σ`, `S` isotropic for well-prepared data, and `Ψ` the transport term
followed by a discrete low-pass filter (`filt`) in time.  Hence
`F = ∑_{j<k} c^j Ψ^j S + c^k Ψ^k F` (`decomposition`).
`Ψ^j S` has velocity degree exactly `j` (`psi_pow_mon`), and the filter is a contraction that
commutes with `D`, so the remainder is at most `(ε m / σ)^k` times the sup in time of `‖D^k F‖`,
which energy stability bounds by `‖D^k F₀‖` (`norm_pow_mul_le`).

The truncated Hilbert expansion is not formalised.  The hypothesis `⟨μ⟩ = 0` that
it needs is not used for the implicit scheme, and is used for IMEX Euler.  The formula
`⌈log tol / log ε⌉ + 1` holds only under a condition (`epsRank_ideas_formula`);
the parameter is `ε ‖D‖ / σ`, not `ε`.

The velocity quadratures `Quadrature` are defined in `LeanDLRA/Kinetic/Defs.lean`.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Novel.EpsRank

/-! ### The discrete low-pass filter -/

section Filter

variable {E E' : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']

/-- The discrete low-pass filter `y_{n+1} = b y_n + a z_{n+1-ℓ}`, `y_0 = 0`.  For `a + b = 1`,
`a, b ≥ 0` it averages the history of `z`, with memory `b`. -/
def filt (a b : ℝ) (l : ℕ) (z : ℕ → E) : ℕ → E
  | 0 => 0
  | n + 1 => b • filt a b l z n + a • z (n + 1 - l)

@[simp] theorem filt_zero (a b : ℝ) (l : ℕ) (z : ℕ → E) : filt a b l z 0 = 0 := rfl

theorem filt_succ (a b : ℝ) (l : ℕ) (z : ℕ → E) (n : ℕ) :
    filt a b l z (n + 1) = b • filt a b l z n + a • z (n + 1 - l) := rfl

/-- Linear maps commute with the filter. -/
theorem map_filt (a b : ℝ) (l : ℕ) (L : E →ₗ[ℝ] E') (z : ℕ → E) (n : ℕ) :
    L (filt a b l z n) = filt a b l (fun m => L (z m)) n := by
  induction n with
  | zero => simp
  | succ n ih => simp [filt_succ, ih]

/-- The filter as a linear map on sequences. -/
def filtL (a b : ℝ) (l : ℕ) : (ℕ → E) →ₗ[ℝ] (ℕ → E) where
  toFun z := filt a b l z
  map_add' x y := by
    funext n
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [filt_succ, Pi.add_apply] at ih ⊢
      rw [ih]; module
  map_smul' r x := by
    funext n
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [filt_succ, Pi.smul_apply, RingHom.id_apply] at ih ⊢
      rw [ih]; module

@[simp] theorem filtL_apply (a b : ℝ) (l : ℕ) (z : ℕ → E) : filtL a b l z = filt a b l z := rfl

/-- The filter is a causal contraction for the supremum norm in time. -/
theorem norm_filt_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {a b C : ℝ} {l N : ℕ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hC : 0 ≤ C) {z : ℕ → F}
    (hz : ∀ m ≤ N, ‖z m‖ ≤ C) : ∀ n ≤ N, ‖filt a b l z n‖ ≤ C := by
  intro n
  induction n with
  | zero => intro _; simpa using hC
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have h2 := hz (n + 1 - l) (by omega)
    calc ‖filt a b l z (n + 1)‖ ≤ ‖b • filt a b l z n‖ + ‖a • z (n + 1 - l)‖ := norm_add_le _ _
      _ = b * ‖filt a b l z n‖ + a * ‖z (n + 1 - l)‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ b * C + a * C := by gcongr
      _ = C := by rw [← add_mul, add_comm, hab, one_mul]

/-- Summing a geometric series: `x = s + c P x` gives
`x = ∑_{j<k} c^j P^j s + c^k P^k x`. -/
theorem eq_geom {M : Type*} [AddCommGroup M] [Module ℝ M] (P : M →ₗ[ℝ] M) (c : ℝ) {x s : M}
    (h : x = s + c • P x) (k : ℕ) :
    x = ∑ j ∈ Finset.range k, c ^ j • (P ^ j) s + c ^ k • (P ^ k) x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : (P ^ k) x = (P ^ k) s + c • (P ^ (k + 1)) x := by
      conv_lhs => rw [h]
      rw [map_add, map_smul, pow_succ, Module.End.mul_apply]
    rw [Finset.sum_range_succ, add_assoc]
    conv_lhs => rw [ih, h1]
    rw [smul_add, smul_smul, pow_succ c k]

end Filter

/-! ### The scheme -/

section Scheme

variable {X V : Type*} [Fintype X] [Fintype V]

/-- The velocity average `⟨f⟩_i = ∑_v w_v f_{iv}`. -/
def avg (q : Quadrature V) (f : Matrix X V ℝ) : X → ℝ := fun i => ∑ v, q.w v * f i v

/-- The monomial matrix `u ⊗ μ^j`, entries `u_i μ_v^j`. -/
def mon (q : Quadrature V) (j : ℕ) (u : X → ℝ) : Matrix X V ℝ :=
  Matrix.of fun i v => u i * q.μ v ^ j

/-- The isotropic matrix `ρ ⊗ 1`, entries `ρ_i`. -/
def iso (ρ : X → ℝ) : Matrix X V ℝ := Matrix.of fun i _ => ρ i

/-- The transport term `D f diag(μ)`, entries `μ_v (D f)_{iv}`. -/
def transport (D : Matrix X X ℝ) (q : Quadrature V) (f : Matrix X V ℝ) : Matrix X V ℝ :=
  Matrix.of fun i v => q.μ v * (D * f) i v

/-- The quadrature-weighted matrix `f diag(√w)`, whose singular values are those of the `x`–`v`
expansion of `f` in `L²(w)`. -/
noncomputable def weighted (q : Quadrature V) (f : Matrix X V ℝ) : Matrix X V ℝ :=
  Matrix.of fun i v => √(q.w v) * f i v

/-- The linear map version of `mon`. -/
def monL (q : Quadrature V) (j : ℕ) : (X → ℝ) →ₗ[ℝ] Matrix X V ℝ where
  toFun := mon q j
  map_add' x y := by ext i v; simp [mon, add_mul]
  map_smul' r x := by ext i v; simp [mon, mul_assoc]

/-- The linear map version of `transport`. -/
def transportL (D : Matrix X X ℝ) (q : Quadrature V) : Matrix X V ℝ →ₗ[ℝ] Matrix X V ℝ where
  toFun := transport D q
  map_add' x y := by ext i v; simp [transport, Matrix.mul_add, mul_add]
  map_smul' r x := by ext i v; simp [transport, Matrix.mul_smul]; ring

@[simp] theorem transportL_apply (D : Matrix X X ℝ) (q : Quadrature V) (f : Matrix X V ℝ) :
    transportL D q f = transport D q f := rfl

/-- The linear map version of `weighted`. -/
noncomputable def weightedL (q : Quadrature V) : Matrix X V ℝ →ₗ[ℝ] Matrix X V ℝ where
  toFun := weighted q
  map_add' x y := by ext i v; simp [weighted, mul_add]
  map_smul' r x := by ext i v; simp [weighted]; ring

omit [Fintype X] in
theorem iso_eq_mon (q : Quadrature V) (ρ : X → ℝ) : (iso ρ : Matrix X V ℝ) = mon q 0 ρ := by
  ext i v; simp [iso, mon]

theorem transport_mon (D : Matrix X X ℝ) (q : Quadrature V) (j : ℕ) (u : X → ℝ) :
    transport D q (mon q j u) = mon q (j + 1) (D.mulVec u) := by
  ext i v
  simp only [transport, mon, Matrix.of_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    pow_succ, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- One step of the time discretisation of `∂_t f + ε⁻¹ D f diag(μ) = σ ε⁻² (⟨f⟩ - f)`, with step
size `τ`, old iterate `f`, new iterate `p`, and the transport term evaluated at `g`. -/
def IsStep (D : Matrix X X ℝ) (q : Quadrature V) (ε σ τ : ℝ) (g f p : Matrix X V ℝ) : Prop :=
  τ⁻¹ • (p - f) + ε⁻¹ • transport D q g = (σ / ε ^ 2) • (iso (avg q p) - p)

/-- The fully implicit Euler scheme. -/
def IsImplicitEuler (D : Matrix X X ℝ) (q : Quadrature V) (ε σ τ : ℝ)
    (F : ℕ → Matrix X V ℝ) : Prop :=
  ∀ n, IsStep D q ε σ τ (F (n + 1)) (F n) (F (n + 1))

/-- The IMEX Euler scheme: explicit transport, implicit scattering. -/
def IsIMEXEuler (D : Matrix X X ℝ) (q : Quadrature V) (ε σ τ : ℝ)
    (F : ℕ → Matrix X V ℝ) : Prop :=
  ∀ n, IsStep D q ε σ τ (F n) (F n) (F (n + 1))

/-- The solved form of a step. -/
theorem IsStep.eq {D : Matrix X X ℝ} {q : Quadrature V} {ε σ τ : ℝ} {g f p : Matrix X V ℝ}
    (hε : 0 < ε) (hσ : 0 < σ) (hτ : 0 < τ) (h : IsStep D q ε σ τ g f p) :
    p = ((ε ^ 2 / τ) / (σ + ε ^ 2 / τ)) • f + (σ / (σ + ε ^ 2 / τ)) • iso (avg q p) +
      ((σ / (σ + ε ^ 2 / τ)) * (-ε / σ)) • transport D q g := by
  ext i v
  have h1 := congrFun (congrFun h i) v
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, iso,
    Matrix.of_apply] at h1 ⊢
  have hs : σ + ε ^ 2 / τ ≠ 0 := by positivity
  have hs' : σ * τ + ε ^ 2 ≠ 0 := by positivity
  field_simp at h1 ⊢
  linear_combination h1

end Scheme

/-! ### The exact decomposition -/

section Decomposition

variable {X V : Type*} [Fintype X] [Fintype V]

/-- The sequence operator `Ψ z = (filter of T z)`, with `T` the transport term. -/
def psi (D : Matrix X X ℝ) (q : Quadrature V) (a b : ℝ) (l : ℕ) :
    (ℕ → Matrix X V ℝ) →ₗ[ℝ] (ℕ → Matrix X V ℝ) :=
  filtL a b l ∘ₗ LinearMap.compLeft (transportL D q) ℕ

theorem psi_apply (D : Matrix X X ℝ) (q : Quadrature V) (a b : ℝ) (l : ℕ)
    (z : ℕ → Matrix X V ℝ) (n : ℕ) :
    psi D q a b l z n = filt a b l (fun m => transport D q (z m)) n := rfl

/-- `Ψ^j` raises the velocity degree by exactly `j`: applied to isotropic sequences it gives
`u_n ⊗ μ^j`. -/
theorem psi_pow_mon (D : Matrix X X ℝ) (q : Quadrature V) (a b : ℝ) (l j : ℕ)
    (φ : ℕ → X → ℝ) :
    ∃ u : ℕ → X → ℝ, ∀ n, (psi D q a b l ^ j) (fun m => mon q 0 (φ m)) n = mon q j (u n) := by
  induction j with
  | zero => exact ⟨φ, fun n => rfl⟩
  | succ j ih =>
    obtain ⟨u, hu⟩ := ih
    refine ⟨fun n => filt a b l (fun m => D.mulVec (u m)) n, fun n => ?_⟩
    rw [pow_succ', Module.End.mul_apply, psi_apply]
    have h1 : (fun m => transport D q ((psi D q a b l ^ j) (fun m => mon q 0 (φ m)) m)) =
        fun m => monL q (j + 1) (D.mulVec (u m)) := by
      funext m
      rw [hu m, transport_mon]
      rfl
    rw [h1, ← map_filt]
    rfl

/-- The Vandermonde matrix `(μ_v^j)_{j<k, v}`. -/
def vand (q : Quadrature V) (k : ℕ) : Matrix (Fin k) V ℝ := Matrix.of fun j v => q.μ v ^ (j : ℕ)

omit [Fintype X] in
theorem exists_sum_mon_eq (q : Quadrature V) (c : ℝ) (k : ℕ) (u : ℕ → X → ℝ) :
    ∃ A : Matrix X (Fin k) ℝ,
      ∑ j ∈ Finset.range k, c ^ j • mon q j (u j) = A * vand q k := by
  refine ⟨Matrix.of fun i j => c ^ (j : ℕ) * u j i, ?_⟩
  ext i v
  rw [Matrix.sum_apply, Matrix.mul_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, mon, vand, Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun j => c ^ j * u j i * q.μ v ^ j) k]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The exact decomposition.**  If `F_{n+1} = b F_n + a ρ_{n+1} ⊗ 1 + a c T F_{n+1-l}` with
`F_0 = ρ₀ ⊗ 1 + g₀`, then `F_n` is a matrix with rows in `span {1, μ, …, μ^{k-1}}`, plus the
remainder `c^k Ψ^k F`, plus the initial layer generated by `g₀`.  No hypothesis on `D`, `ρ`, or
the size of `c`. -/
theorem decomposition {D : Matrix X X ℝ} {q : Quadrature V} {a b c : ℝ} {l : ℕ}
    {ρ : ℕ → X → ℝ} {ρ₀ : X → ℝ} {g₀ : Matrix X V ℝ} {F : ℕ → Matrix X V ℝ}
    (hF : ∀ n, F (n + 1) = b • F n + a • iso (ρ (n + 1)) +
      (a * c) • transport D q (F (n + 1 - l)))
    (h0 : F 0 = iso ρ₀ + g₀) (k n : ℕ) :
    ∃ A : Matrix X (Fin k) ℝ, F n - A * vand q k =
      ∑ j ∈ Finset.range k, c ^ j • (psi D q a b l ^ j) (fun m => b ^ m • g₀) n +
        c ^ k • (psi D q a b l ^ k) F n := by
  set φ : ℕ → X → ℝ := fun n => b ^ n • ρ₀ + filt a b 0 ρ n with hφ
  have key : F = (fun m => mon q 0 (φ m)) + (fun m => b ^ m • g₀) + c • psi D q a b l F := by
    funext n
    induction n with
    | zero =>
      simp only [Pi.add_apply, Pi.smul_apply, psi_apply, filt_zero, smul_zero, add_zero, hφ,
        pow_zero, one_smul, h0, iso_eq_mon q]
    | succ n ih =>
      simp only [Pi.add_apply, Pi.smul_apply, psi_apply] at ih ⊢
      rw [hF n, filt_succ, ih]
      have h2 : mon q 0 (φ (n + 1)) = b • mon q 0 (φ n) + a • iso (ρ (n + 1)) := by
        have h3 : φ (n + 1) = b • φ n + a • ρ (n + 1) := by
          simp only [hφ, filt_succ, Nat.sub_zero, pow_succ]
          module
        rw [h3, iso_eq_mon q]
        exact (monL q 0).map_add _ _ |>.trans (by simp [monL])
      rw [h2]
      simp only [mul_smul, pow_succ]
      module
  have h3 := eq_geom (psi D q a b l) c key k
  have h4 : ∑ j ∈ Finset.range k, c ^ j • (psi D q a b l ^ j)
        ((fun m => mon q 0 (φ m)) + fun m => b ^ m • g₀) =
      ∑ j ∈ Finset.range k, c ^ j • (psi D q a b l ^ j) (fun m => mon q 0 (φ m)) +
      ∑ j ∈ Finset.range k, c ^ j • (psi D q a b l ^ j) (fun m => b ^ m • g₀) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [map_add, smul_add]
  choose u hu using fun j => psi_pow_mon D q a b l j φ
  obtain ⟨A, hA⟩ := exists_sum_mon_eq q c k (fun j => u j n)
  refine ⟨A, ?_⟩
  have h5 := congrFun h3 n
  rw [h4] at h5
  simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply] at h5
  have h6 : ∑ j ∈ Finset.range k, c ^ j • (psi D q a b l ^ j) (fun m => mon q 0 (φ m)) n =
      A * vand q k := by
    rw [← hA]
    exact Finset.sum_congr rfl fun j _ => by rw [hu j n]
  rw [h6] at h5
  rw [sub_eq_iff_eq_add, h5]
  abel

end Decomposition

/-! ### Weighted norms -/

section Norms

variable {X V : Type*} [Fintype X] [Fintype V]

/-- The Euclidean norm of a vector. -/
noncomputable def l2 (u : X → ℝ) : ℝ := √(∑ i, u i ^ 2)

theorem l2_nonneg (u : X → ℝ) : 0 ≤ l2 u := Real.sqrt_nonneg _

theorem sq_norm_weighted (q : Quadrature V) (f : Matrix X V ℝ) :
    ‖weighted q f‖ ^ 2 = ∑ i, ∑ v, q.w v * f i v ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun v _ => ?_
  simp only [weighted, Matrix.of_apply, mul_pow, Real.sq_sqrt (q.w_pos v).le]

theorem norm_weighted_iso (q : Quadrature V) (u : X → ℝ) :
    ‖weighted q (iso u : Matrix X V ℝ)‖ = l2 u := by
  have h : ‖weighted q (iso u : Matrix X V ℝ)‖ ^ 2 = ∑ i, u i ^ 2 := by
    rw [sq_norm_weighted]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [iso, Matrix.of_apply]
    rw [← Finset.sum_mul, q.sum_w, one_mul]
  rw [l2, ← h, Real.sqrt_sq (norm_nonneg _)]

theorem norm_weighted_scale (q : Quadrature V) {s : V → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hs : ∀ v, |s v| ≤ C) (f : Matrix X V ℝ) :
    ‖weighted q (Matrix.of fun i v => s v * f i v)‖ ≤ C * ‖weighted q f‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  rw [mul_pow, sq_norm_weighted, sq_norm_weighted, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  simp only [Matrix.of_apply, mul_pow]
  have h1 : s v ^ 2 ≤ C ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hs v) 2
  have h2 := (q.w_pos v).le
  have h3 := sq_nonneg (f i v)
  nlinarith [mul_nonneg h2 h3]

omit [Fintype X] in
theorem weighted_eq_mul [DecidableEq V] (q : Quadrature V) (f : Matrix X V ℝ) :
    weighted q f = f * Matrix.diagonal fun v => √(q.w v) := by
  ext i v
  simp [weighted, Matrix.mul_diagonal, mul_comm]

omit [Fintype X] in
theorem rank_weighted_le [Finite X] (q : Quadrature V) (f : Matrix X V ℝ) :
    (weighted q f).rank ≤ f.rank := by
  classical
  rw [weighted_eq_mul]
  exact Matrix.rank_mul_le_left _ _

omit [Fintype X] in
theorem eq_zero_of_weighted (q : Quadrature V) {f : Matrix X V ℝ} (h : weighted q f = 0) :
    f = 0 := by
  ext i v
  have h1 := congrFun (congrFun h i) v
  simp only [weighted, Matrix.of_apply, Matrix.zero_apply, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact absurd h1 (Real.sqrt_pos.mpr (q.w_pos v)).ne'
  · exact h1

variable [DecidableEq X]

/-- Left multiplication as a linear map. -/
def leftL (B : Matrix X X ℝ) : Matrix X V ℝ →ₗ[ℝ] Matrix X V ℝ where
  toFun f := B * f
  map_add' := Matrix.mul_add B
  map_smul' r f := Matrix.mul_smul B r f

omit [DecidableEq X] in
theorem mul_transport (D B : Matrix X X ℝ) (q : Quadrature V) (f : Matrix X V ℝ) :
    B * transport D q f = Matrix.of fun i v => q.μ v * (B * (D * f)) i v := by
  ext i v
  rw [Matrix.of_apply, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [transport, Matrix.of_apply]
  ring

/-- **The remainder bound**: with `|μ| ≤ m`, `‖Ψ^k z‖ ≤ m^k C` as soon as `‖D^k z‖ ≤ C` on the
history. -/
theorem norm_psi_pow_le {D : Matrix X X ℝ} {q : Quadrature V} {a b m : ℝ} {l : ℕ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hm0 : 0 ≤ m) (hm : ∀ v, |q.μ v| ≤ m) (k : ℕ) :
    ∀ (z : ℕ → Matrix X V ℝ) (C : ℝ) (N : ℕ), 0 ≤ C →
      (∀ i ≤ N, ‖weighted q ((D ^ k) * z i)‖ ≤ C) →
      ∀ n ≤ N, ‖weighted q ((psi D q a b l ^ k) z n)‖ ≤ m ^ k * C := by
  induction k with
  | zero =>
    intro z C N _ hz n hn
    simpa using hz n hn
  | succ k ih =>
    intro z C N hC hz n hn
    rw [pow_succ, Module.End.mul_apply]
    have h1 := ih (psi D q a b l z) (m * C) N (by positivity) ?_ n hn
    · calc _ ≤ m ^ k * (m * C) := h1
        _ = m ^ (k + 1) * C := by ring
    · intro i hi
      have h2 : weighted q (D ^ k * psi D q a b l z i) =
          filt a b l (fun j => weighted q (D ^ k * transport D q (z j))) i := by
        have := map_filt a b l (weightedL q ∘ₗ leftL (D ^ k)) (fun j => transport D q (z j)) i
        exact this
      rw [h2]
      refine norm_filt_le ha hb hab (by positivity) (fun j hj => ?_) i hi
      rw [mul_transport]
      refine (norm_weighted_scale q hm0 hm _).trans ?_
      have h3 : D ^ k * (D * z j) = D ^ (k + 1) * z j := by rw [pow_succ, Matrix.mul_assoc]
      rw [h3]
      exact mul_le_mul_of_nonneg_left (hz j hj) hm0

end Norms

/-! ### Energy stability and well-posedness -/

section Energy

variable {X V : Type*} [Fintype X] [Fintype V]

omit [Fintype V] in
theorem skew_quad {D : Matrix X X ℝ} (hD : D.transpose = -D) (x : X → ℝ) :
    ∑ i, x i * D.mulVec x i = 0 := by
  have h1 : ∑ i, x i * D.mulVec x i = -∑ i, x i * D.mulVec x i := by
    have h2 : ∀ i l, D i l = -D l i := fun i l => by
      have := congrFun (congrFun hD l) i
      simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
      linarith
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [h2 l i]
    ring
  linarith

omit [Fintype X] in
theorem sum_w_mul_avg_sub_le (q : Quadrature V) (f : Matrix X V ℝ) (i : X) :
    ∑ v, q.w v * f i v * (avg q f i - f i v) ≤ 0 := by
  have h0 : 0 ≤ ∑ v, q.w v * (f i v - avg q f i) ^ 2 :=
    Finset.sum_nonneg fun v _ => mul_nonneg (q.w_pos v).le (sq_nonneg _)
  have h1 : ∑ v, q.w v * (f i v - avg q f i) ^ 2 =
      ∑ v, q.w v * f i v ^ 2 - 2 * avg q f i * ∑ v, q.w v * f i v +
        avg q f i ^ 2 * ∑ v, q.w v := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  have h2 : ∑ v, q.w v * f i v * (avg q f i - f i v) =
      avg q f i * ∑ v, q.w v * f i v - ∑ v, q.w v * f i v ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  have h3 : ∑ v, q.w v * f i v = avg q f i := rfl
  rw [q.sum_w, h3] at h1
  rw [h2, h3]
  nlinarith

/-- **Energy stability** of the implicit step, for skew-symmetric `D` and any `ε, σ, τ > 0`. -/
theorem IsStep.norm_le {D : Matrix X X ℝ} {q : Quadrature V} {ε σ τ : ℝ} {f p : Matrix X V ℝ}
    (hD : D.transpose = -D) (hε : 0 < ε) (hσ : 0 < σ) (hτ : 0 < τ)
    (h : IsStep D q ε σ τ p f p) : ‖weighted q p‖ ≤ ‖weighted q f‖ := by
  have entry : ∀ i v, τ⁻¹ * (p i v - f i v) + ε⁻¹ * (q.μ v * (D * p) i v) =
      (σ / ε ^ 2) * (avg q p i - p i v) := fun i v => by
    have h1 := congrFun (congrFun h i) v
    simpa [transport, iso] using h1
  set S1 := ∑ i, ∑ v, q.w v * p i v * (p i v - f i v) with hS1
  set S3 := ∑ i, ∑ v, q.w v * p i v * (avg q p i - p i v) with hS3
  have hS2 : ∑ i, ∑ v, q.w v * p i v * (q.μ v * (D * p) i v) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun v _ => ?_
    have h1 := skew_quad hD (fun i => p i v)
    have h2 : ∀ i, (D * p) i v = D.mulVec (fun i => p i v) i := fun i => by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    calc ∑ i, q.w v * p i v * (q.μ v * (D * p) i v)
        = (q.w v * q.μ v) * ∑ i, p i v * D.mulVec (fun i => p i v) i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [h2 i]; ring
      _ = 0 := by rw [h1, mul_zero]
  have hbal : τ⁻¹ * S1 = (σ / ε ^ 2) * S3 := by
    have h1 : ∑ i, ∑ v, q.w v * p i v *
        (τ⁻¹ * (p i v - f i v) + ε⁻¹ * (q.μ v * (D * p) i v)) =
        τ⁻¹ * S1 + ε⁻¹ * ∑ i, ∑ v, q.w v * p i v * (q.μ v * (D * p) i v) := by
      rw [hS1, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun v _ => by ring
    have h2 : ∑ i, ∑ v, q.w v * p i v *
        (τ⁻¹ * (p i v - f i v) + ε⁻¹ * (q.μ v * (D * p) i v)) = (σ / ε ^ 2) * S3 := by
      rw [hS3, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => by rw [entry i v]; ring
    rw [hS2, mul_zero, add_zero] at h1
    rw [← h1, h2]
  have hS3le : S3 ≤ 0 := Finset.sum_nonpos fun i _ => sum_w_mul_avg_sub_le q p i
  have hS1le : S1 ≤ 0 := by
    have h1 : τ⁻¹ * S1 ≤ 0 := by
      rw [hbal]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hS3le
    have h2 : 0 < τ⁻¹ := inv_pos.mpr hτ
    by_contra hc
    exact absurd h1 (not_le.mpr (mul_pos h2 (not_le.mp hc)))
  have hE : ‖weighted q p‖ ^ 2 ≤ ‖weighted q f‖ ^ 2 := by
    rw [sq_norm_weighted, sq_norm_weighted]
    have h0 : 0 ≤ ∑ i, ∑ v, q.w v * (p i v - f i v) ^ 2 :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun v _ =>
        mul_nonneg (q.w_pos v).le (sq_nonneg _)
    have h1 : ∑ i, ∑ v, q.w v * (p i v - f i v) ^ 2 =
        ∑ i, ∑ v, q.w v * f i v ^ 2 - ∑ i, ∑ v, q.w v * p i v ^ 2 + 2 * S1 := by
      rw [hS1, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun v _ => by ring
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hE

theorem avg_mul (B : Matrix X X ℝ) (q : Quadrature V) (f : Matrix X V ℝ) :
    avg q (B * f) = B.mulVec (avg q f) := by
  funext i
  simp only [avg, Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun v _ => by ring

omit [Fintype V] in
theorem mul_iso (B : Matrix X X ℝ) (u : X → ℝ) :
    B * (iso u : Matrix X V ℝ) = iso (B.mulVec u) := by
  ext i v
  simp [iso, Matrix.mul_apply, Matrix.mulVec, dotProduct]

omit [Fintype V] in
theorem mul_of_scale (B : Matrix X X ℝ) (s : V → ℝ) (x : Matrix X V ℝ) :
    B * (Matrix.of fun i v => s v * x i v) = Matrix.of fun i v => s v * (B * x) i v := by
  ext i v
  simp only [Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- Anything commuting with `D` maps solutions of a step to solutions. -/
theorem IsStep.mul_left {D B : Matrix X X ℝ} {q : Quadrature V} {ε σ τ : ℝ}
    {g f p : Matrix X V ℝ} (hB : B * D = D * B) (h : IsStep D q ε σ τ g f p) :
    IsStep D q ε σ τ (B * g) (B * f) (B * p) := by
  have h1 := congrArg (fun x => B * x) h
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_sub, mul_iso] at h1
  rw [IsStep, avg_mul]
  have h2 : B * transport D q g = transport D q (B * g) := by
    rw [mul_transport]
    ext i v
    simp only [transport, Matrix.of_apply, ← Matrix.mul_assoc, hB]
  rw [← h2]
  simpa only [Matrix.mul_sub] using h1

/-- `‖D^k F_n‖` is non-increasing along the implicit scheme, for skew-symmetric `D`. -/
theorem norm_pow_mul_le [DecidableEq X] {D : Matrix X X ℝ} {q : Quadrature V} {ε σ τ : ℝ}
    {F : ℕ → Matrix X V ℝ} (hD : D.transpose = -D) (hε : 0 < ε) (hσ : 0 < σ) (hτ : 0 < τ)
    (hF : IsImplicitEuler D q ε σ τ F) (k n : ℕ) :
    ‖weighted q (D ^ k * F n)‖ ≤ ‖weighted q (D ^ k * F 0)‖ := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have h1 : D ^ k * D = D * D ^ k := (Commute.pow_left (Commute.refl D) k).eq
    exact ((hF n).mul_left h1 |>.norm_le hD hε hσ hτ).trans ih

omit [Fintype X] in
theorem avg_add (q : Quadrature V) (x y : Matrix X V ℝ) : avg q (x + y) = avg q x + avg q y := by
  funext i
  simp [avg, mul_add, Finset.sum_add_distrib]

omit [Fintype X] in
theorem avg_smul (q : Quadrature V) (r : ℝ) (x : Matrix X V ℝ) : avg q (r • x) = r • avg q x := by
  funext i
  simp only [avg, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ => by ring

omit [Fintype X] [Fintype V] in
theorem iso_add (x y : X → ℝ) : (iso (x + y) : Matrix X V ℝ) = iso x + iso y := by
  ext i v; simp [iso]

omit [Fintype X] [Fintype V] in
theorem iso_smul (r : ℝ) (x : X → ℝ) : (iso (r • x) : Matrix X V ℝ) = r • iso x := by
  ext i v; simp [iso]

/-- The operator of the implicit step. -/
noncomputable def stepOp (D : Matrix X X ℝ) (q : Quadrature V) (ε σ τ : ℝ) :
    Matrix X V ℝ →ₗ[ℝ] Matrix X V ℝ where
  toFun p := τ⁻¹ • p + ε⁻¹ • transport D q p - (σ / ε ^ 2) • (iso (avg q p) - p)
  map_add' x y := by
    have h := (transportL D q).map_add x y
    simp only [transportL_apply] at h
    rw [avg_add, iso_add, h]
    module
  map_smul' r x := by
    have h := (transportL D q).map_smul r x
    simp only [transportL_apply] at h
    rw [avg_smul, iso_smul, h, RingHom.id_apply]
    module

theorem isStep_iff_stepOp {D : Matrix X X ℝ} {q : Quadrature V} {ε σ τ : ℝ}
    {f p : Matrix X V ℝ} :
    IsStep D q ε σ τ p f p ↔ stepOp D q ε σ τ p = τ⁻¹ • f := by
  change τ⁻¹ • (p - f) + ε⁻¹ • transport D q p = (σ / ε ^ 2) • (iso (avg q p) - p) ↔
    τ⁻¹ • p + ε⁻¹ • transport D q p - (σ / ε ^ 2) • (iso (avg q p) - p) = τ⁻¹ • f
  constructor
  · intro h
    linear_combination (norm := module) h
  · intro h
    linear_combination (norm := module) h

/-- **Well-posedness of one step**: for skew-symmetric `D` the implicit equation has exactly one
solution, for all `ε, σ, τ > 0`. -/
theorem existsUnique_step {D : Matrix X X ℝ} {q : Quadrature V} {ε σ τ : ℝ}
    (hD : D.transpose = -D) (hε : 0 < ε) (hσ : 0 < σ) (hτ : 0 < τ) (f : Matrix X V ℝ) :
    ∃! p, IsStep D q ε σ τ p f p := by
  have inj : Function.Injective (stepOp D q ε σ τ) := by
    refine (injective_iff_map_eq_zero _).2 fun p hp => ?_
    have h1 : IsStep D q ε σ τ p 0 p := isStep_iff_stepOp.2 (by rw [hp, smul_zero])
    have h2 := h1.norm_le hD hε hσ hτ
    have h3 : weighted q (0 : Matrix X V ℝ) = 0 := (weightedL q).map_zero
    rw [h3, norm_zero] at h2
    exact eq_zero_of_weighted q (norm_le_zero_iff.mp h2)
  obtain ⟨p, hp⟩ := LinearMap.injective_iff_surjective.1 inj (τ⁻¹ • f)
  exact ⟨p, isStep_iff_stepOp.2 hp, fun p' hp' => inj ((isStep_iff_stepOp.1 hp').trans hp.symm)⟩

/-- **Well-posedness of the scheme**: every initial value has exactly one implicit Euler
trajectory. -/
theorem existsUnique_implicitEuler {D : Matrix X X ℝ} {q : Quadrature V} {ε σ τ : ℝ}
    (hD : D.transpose = -D) (hε : 0 < ε) (hσ : 0 < σ) (hτ : 0 < τ) (f₀ : Matrix X V ℝ) :
    ∃! F : ℕ → Matrix X V ℝ, F 0 = f₀ ∧ IsImplicitEuler D q ε σ τ F := by
  choose S hS using fun f => (existsUnique_step (q := q) hD hε hσ hτ f).exists
  refine ⟨fun n => Nat.rec f₀ (fun _ y => S y) n, ⟨rfl, fun n => hS _⟩, ?_⟩
  rintro G ⟨h0, hG⟩
  funext n
  induction n with
  | zero => exact h0
  | succ n ih =>
    have h1 := hG n
    rw [ih] at h1
    exact (existsUnique_step (q := q) hD hε hσ hτ _).unique h1 (hS _)

end Energy

/-! ### The rank bounds -/

section Main

variable {X V : Type*} [Fintype X] [Fintype V]

/-- The relaxation weight `a = σ / (σ + ε²/τ)` of one step. -/
noncomputable def relaxA (ε σ τ : ℝ) : ℝ := σ / (σ + ε ^ 2 / τ)

/-- The memory `b = (ε²/τ) / (σ + ε²/τ) = ε² / (ε² + σ τ)` of one step: the initial layer is
damped by `b` per step. -/
noncomputable def relaxB (ε σ τ : ℝ) : ℝ := (ε ^ 2 / τ) / (σ + ε ^ 2 / τ)

theorem relaxA_nonneg {ε σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) : 0 ≤ relaxA ε σ τ := by
  unfold relaxA; positivity

theorem relaxB_nonneg {ε σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) : 0 ≤ relaxB ε σ τ := by
  unfold relaxB; positivity

theorem relaxA_add_relaxB {ε σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) :
    relaxA ε σ τ + relaxB ε σ τ = 1 := by
  unfold relaxA relaxB
  have : σ + ε ^ 2 / τ ≠ 0 := by positivity
  field_simp

/-- `b ≤ ε² / (σ τ)`, which makes the initial layer `O(ε^{2n})`. -/
theorem relaxB_le {ε σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) : relaxB ε σ τ ≤ ε ^ 2 / (σ * τ) := by
  unfold relaxB
  have h1 : 0 ≤ ε ^ 2 / τ := by positivity
  calc ε ^ 2 / τ / (σ + ε ^ 2 / τ) ≤ ε ^ 2 / τ / σ := by
        apply div_le_div_of_nonneg_left h1 hσ
        linarith
    _ = ε ^ 2 / (σ * τ) := by field_simp

theorem relaxA_le_one {ε σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) : relaxA ε σ τ ≤ 1 := by
  have := relaxA_add_relaxB (ε := ε) hσ hτ
  have := relaxB_nonneg (ε := ε) hσ hτ
  linarith

theorem IsStep.eq' {D : Matrix X X ℝ} {q : Quadrature V} {ε σ τ : ℝ} {g f p : Matrix X V ℝ}
    (hε : 0 < ε) (hσ : 0 < σ) (hτ : 0 < τ) (h : IsStep D q ε σ τ g f p) :
    p = relaxB ε σ τ • f + relaxA ε σ τ • iso (avg q p) +
      (relaxA ε σ τ * (-ε / σ)) • transport D q g :=
  h.eq hε hσ hτ

theorem distLR_weighted_le (q : Quadrature V) (f : Matrix X V ℝ) {k : ℕ} {Y : Matrix X V ℝ}
    (hY : Y.rank ≤ k) : distLR k (weighted q f) ≤ ‖weighted q (f - Y)‖ := by
  have h1 : weighted q (f - Y) = weighted q f - weighted q Y := (weightedL q).map_sub f Y
  rw [h1]
  exact distLR_le_norm_sub ((rank_weighted_le q Y).trans hY)

omit [Fintype X] in
theorem rank_mul_vand_le [Finite X] (q : Quadrature V) {k : ℕ} (A : Matrix X (Fin k) ℝ) :
    (A * vand q k).rank ≤ k :=
  (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width A).trans (by simp))

/-- Lower-order term of the initial layer, `C(n+j-1, j) a^j b^n`. -/
noncomputable def layerCoeff (a b : ℝ) (n j : ℕ) : ℝ := ((n + j - 1).choose j : ℝ) * a ^ j * b ^ n

theorem filt_layerCoeff (a b : ℝ) (j n : ℕ) :
    filt a b 0 (fun m => layerCoeff a b m j) n = layerCoeff a b n (j + 1) := by
  induction n with
  | zero => simp [layerCoeff, Nat.choose_succ_self]
  | succ n ih =>
    rw [filt_succ, ih]
    simp only [layerCoeff, smul_eq_mul, Nat.sub_zero]
    have h1 : n + (j + 1) - 1 = n + j := by omega
    have h2 : n + 1 + j - 1 = n + j := by omega
    have h3 : n + 1 + (j + 1) - 1 = n + j + 1 := by omega
    rw [h1, h2, h3, Nat.choose_succ_succ]
    push_cast
    ring

variable [DecidableEq X]

omit [DecidableEq X] in
theorem filt_smul_const {E : Type*} [AddCommGroup E] [Module ℝ E] (a b : ℝ) (l : ℕ) (s : ℕ → ℝ)
    (G : E) (n : ℕ) : filt a b l (fun m => s m • G) n = filt a b l s n • G :=
  (map_filt a b l (LinearMap.toSpanSingleton ℝ E G) s n).symm

theorem transportL_pow (D : Matrix X X ℝ) (q : Quadrature V) (j : ℕ) (G : Matrix X V ℝ) :
    (transportL D q ^ j) G = Matrix.of fun i v => q.μ v ^ j * (D ^ j * G) i v := by
  induction j with
  | zero => ext i v; simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    ext i v
    simp only [transportL_apply, transport, Matrix.of_apply]
    rw [mul_of_scale, Matrix.of_apply, pow_succ', ← Matrix.mul_assoc, pow_succ']
    ring

omit [DecidableEq X] in
theorem psi_pow_layer (D : Matrix X X ℝ) (q : Quadrature V) (a b : ℝ) (G : Matrix X V ℝ) (j : ℕ) :
    ∀ n, (psi D q a b 0 ^ j) (fun m => b ^ m • G) n =
      layerCoeff a b n j • (transportL D q ^ j) G := by
  induction j with
  | zero => intro n; simp [layerCoeff]
  | succ j ih =>
    intro n
    rw [pow_succ', Module.End.mul_apply, psi_apply]
    have h1 : (fun m => transport D q ((psi D q a b 0 ^ j) (fun m => b ^ m • G) m)) =
        fun m => layerCoeff a b m j • (transportL D q ^ (j + 1)) G := by
      funext m
      rw [ih m, pow_succ', Module.End.mul_apply, ← transportL_apply, map_smul]
    rw [h1, filt_smul_const, filt_layerCoeff]

theorem norm_transport_pow_le {D : Matrix X X ℝ} {q : Quadrature V} {m : ℝ} (hm0 : 0 ≤ m)
    (hm : ∀ v, |q.μ v| ≤ m) (j : ℕ) (G : Matrix X V ℝ) :
    ‖weighted q ((transportL D q ^ j) G)‖ ≤ m ^ j * ‖weighted q (D ^ j * G)‖ := by
  rw [transportL_pow]
  refine norm_weighted_scale q (by positivity) (fun v => ?_) _
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hm v) j

/-- **A posteriori bound, arbitrary `D`, implicit or explicit transport.**  For well-prepared
data `F₀ = ρ₀ ⊗ 1`, and any `l`, a scheme whose transport term is lagged by `l` steps
(`l = 0`: implicit Euler; `l = 1`: IMEX Euler) has `F_n` within `(ε m / σ)^k C` of a matrix with
rows in `span {1, μ, …, μ^{k-1}}`, where `C` bounds `‖D^k F_i‖` on the history.  Nothing is
assumed on `D`: stability enters only through the actual values of `‖D^k F_i‖`, which a solver
can compute.1 for the discrete statement this replaces. -/
theorem exists_moment_approx_of_bound {D : Matrix X X ℝ} {q : Quadrature V} {ε σ τ m C : ℝ}
    {l : ℕ} {F : ℕ → Matrix X V ℝ} {ρ₀ : X → ℝ} (hε : 0 < ε) (hσ : 0 < σ) (hτ : 0 < τ)
    (hm0 : 0 ≤ m) (hm : ∀ v, |q.μ v| ≤ m)
    (hF : ∀ n, IsStep D q ε σ τ (F (n + 1 - l)) (F n) (F (n + 1)))
    (h0 : F 0 = iso ρ₀) (k n : ℕ) (hC : ∀ i ≤ n, ‖weighted q (D ^ k * F i)‖ ≤ C) :
    ∃ A : Matrix X (Fin k) ℝ, ‖weighted q (F n - A * vand q k)‖ ≤ (ε * m / σ) ^ k * C := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (Nat.zero_le n))
  have hF' := fun n => (hF n).eq' hε hσ hτ
  obtain ⟨A, hA⟩ := decomposition (ρ := fun n => avg q (F n)) (ρ₀ := ρ₀) (g₀ := 0) hF'
    (by rw [h0, add_zero]) k n
  refine ⟨A, ?_⟩
  have ha := relaxA_nonneg (ε := ε) hσ hτ
  have hb := relaxB_nonneg (ε := ε) hσ hτ
  have hab := relaxA_add_relaxB (ε := ε) hσ hτ
  have h1 : ∀ j, (psi D q (relaxA ε σ τ) (relaxB ε σ τ) l ^ j)
      (fun _ : ℕ => (0 : Matrix X V ℝ)) = 0 := fun j => map_zero _
  simp only [smul_zero, h1, Pi.zero_apply, Finset.sum_const_zero, zero_add] at hA
  rw [hA]
  have h2 := norm_psi_pow_le (l := l) ha hb hab hm0 hm k F C n hC0 hC n le_rfl
  have h3 : weighted q ((-ε / σ) ^ k • (psi D q (relaxA ε σ τ) (relaxB ε σ τ) l ^ k) F n) =
      (-ε / σ) ^ k • weighted q ((psi D q (relaxA ε σ τ) (relaxB ε σ τ) l ^ k) F n) :=
    (weightedL q).map_smul _ _
  rw [h3, norm_smul, norm_pow, Real.norm_eq_abs]
  have h4 : |(-ε / σ)| = ε / σ := by
    rw [abs_div, abs_neg, abs_of_pos hε, abs_of_pos hσ]
  rw [h4]
  calc (ε / σ) ^ k * _ ≤ (ε / σ) ^ k * (m ^ k * C) := by gcongr
    _ = (ε * m / σ) ^ k * C := by
      rw [← mul_assoc, ← mul_pow]
      congr 2
      ring

/-- **Implicit Euler, arbitrary initial data.**  With `F₀ = ρ₀ ⊗ 1 + g₀`, `D` skew-symmetric and
`|μ| ≤ m`, the iterate `F_n` is within
`∑_{j<k} C(n+j-1,j) (a ε m/σ)^j b^n ‖D^j g₀‖ + (ε m/σ)^k ‖D^k F₀‖`
of a matrix with rows in `span {1, μ, …, μ^{k-1}}`.  The first sum is the initial layer: since
`b ≤ ε²/(σ τ)` it is `O(ε^{2n})`, so `σ_{k+1} = O(ε^k)` for ill-prepared data after `n ≥ k/2`
steps.

It matters because it shows how many steps a solver must wait before the schedule applies.  It is
the discrete form of the requirement `t ≥ t₀` in Conjecture J, whose layer of
width `ε²` appears here as the factor `b^n = (1 + σ τ / ε²)^{-n}`. -/
theorem exists_moment_approx_implicit {D : Matrix X X ℝ} {q : Quadrature V} {ε σ τ m : ℝ}
    {F : ℕ → Matrix X V ℝ} {ρ₀ : X → ℝ} {g₀ : Matrix X V ℝ}
    (hD : D.transpose = -D) (hε : 0 < ε) (hσ : 0 < σ) (hτ : 0 < τ)
    (hm0 : 0 ≤ m) (hm : ∀ v, |q.μ v| ≤ m) (hF : IsImplicitEuler D q ε σ τ F)
    (h0 : F 0 = iso ρ₀ + g₀) (k n : ℕ) :
    ∃ A : Matrix X (Fin k) ℝ, ‖weighted q (F n - A * vand q k)‖ ≤
      ∑ j ∈ Finset.range k, ((n + j - 1).choose j : ℝ) * (relaxA ε σ τ * (ε * m / σ)) ^ j *
          relaxB ε σ τ ^ n * ‖weighted q (D ^ j * g₀)‖ +
        (ε * m / σ) ^ k * ‖weighted q (D ^ k * F 0)‖ := by
  have hF' := fun n => (hF n).eq' hε hσ hτ
  obtain ⟨A, hA⟩ := decomposition (l := 0) (ρ := fun n => avg q (F n)) hF' h0 k n
  refine ⟨A, ?_⟩
  have ha := relaxA_nonneg (ε := ε) hσ hτ
  have hb := relaxB_nonneg (ε := ε) hσ hτ
  have hab := relaxA_add_relaxB (ε := ε) hσ hτ
  have hcabs : |(-ε / σ)| = ε / σ := by
    rw [abs_div, abs_neg, abs_of_pos hε, abs_of_pos hσ]
  have hc0 : 0 ≤ ε / σ := by positivity
  rw [hA]
  have h1 : weighted q (∑ j ∈ Finset.range k, (-ε / σ) ^ j •
        (psi D q (relaxA ε σ τ) (relaxB ε σ τ) 0 ^ j)
          (fun m => relaxB ε σ τ ^ m • g₀) n +
      (-ε / σ) ^ k • (psi D q (relaxA ε σ τ) (relaxB ε σ τ) 0 ^ k) F n) =
      ∑ j ∈ Finset.range k, (-ε / σ) ^ j • weighted q
        ((psi D q (relaxA ε σ τ) (relaxB ε σ τ) 0 ^ j)
          (fun m => relaxB ε σ τ ^ m • g₀) n) +
      (-ε / σ) ^ k • weighted q ((psi D q (relaxA ε σ τ) (relaxB ε σ τ) 0 ^ k) F n) := by
    have := (weightedL q).map_add
      (∑ j ∈ Finset.range k, (-ε / σ) ^ j • (psi D q (relaxA ε σ τ) (relaxB ε σ τ) 0 ^ j)
        (fun m => relaxB ε σ τ ^ m • g₀) n)
      ((-ε / σ) ^ k • (psi D q (relaxA ε σ τ) (relaxB ε σ τ) 0 ^ k) F n)
    rw [map_sum, map_smul] at this
    simp only [map_smul] at this
    exact this
  rw [h1]
  refine (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans
    (Finset.sum_le_sum fun j _ => ?_)) ?_)
  · rw [norm_smul, norm_pow, Real.norm_eq_abs, hcabs, psi_pow_layer]
    have h2 : weighted q (layerCoeff (relaxA ε σ τ) (relaxB ε σ τ) n j •
        (transportL D q ^ j) g₀) = layerCoeff (relaxA ε σ τ) (relaxB ε σ τ) n j •
        weighted q ((transportL D q ^ j) g₀) := (weightedL q).map_smul _ _
    have hl : 0 ≤ layerCoeff (relaxA ε σ τ) (relaxB ε σ τ) n j := by
      unfold layerCoeff; positivity
    rw [h2, norm_smul, Real.norm_of_nonneg hl]
    calc (ε / σ) ^ j * (layerCoeff (relaxA ε σ τ) (relaxB ε σ τ) n j *
          ‖weighted q ((transportL D q ^ j) g₀)‖)
        ≤ (ε / σ) ^ j * (layerCoeff (relaxA ε σ τ) (relaxB ε σ τ) n j *
          (m ^ j * ‖weighted q (D ^ j * g₀)‖)) := by
          gcongr
          exact norm_transport_pow_le hm0 hm j g₀
      _ = _ := by
          simp only [layerCoeff, mul_pow, div_pow]
          ring
  · rw [norm_smul, norm_pow, Real.norm_eq_abs, hcabs]
    have h2 := norm_psi_pow_le (l := 0) (D := D) ha hb hab hm0 hm k F
      ‖weighted q (D ^ k * F 0)‖ n (norm_nonneg _)
      (fun i _ => norm_pow_mul_le hD hε hσ hτ hF k i) n le_rfl
    calc (ε / σ) ^ k * _ ≤ (ε / σ) ^ k * (m ^ k * ‖weighted q (D ^ k * F 0)‖) := by gcongr
      _ = (ε * m / σ) ^ k * ‖weighted q (D ^ k * F 0)‖ := by
        rw [← mul_assoc, ← mul_pow]
        congr 2
        ring

/-- **Main theorem: well-prepared data, the fully implicit scheme.**  For skew-symmetric `D`,
`|μ| ≤ m` and `F₀ = ρ₀ ⊗ 1`, for every `ε, σ, τ > 0` and all `n, k`, the iterate `F_n` is within
`(ε m / σ)^k ‖D^k ρ₀‖₂` in `L²(w)` of a matrix with rows in the fixed space
`span {1, μ, …, μ^{k-1}}`.

It matters because it gives a rank and a velocity basis in advance, with a constant uniform in
`n` and `τ`, and uniform in the mesh when `‖D^k ρ₀‖₂` is.  It is the discrete version of
Conjecture J; the case `k = 1`, `ε → 0` is the rank-one limit of
Einkemmer–Hu–Wang (arXiv 2005.06571, Prop. 3.1) and Ding–Einkemmer–Li (arXiv 1907.04247), and
the polynomial structure is that of the Hilbert expansion of Bardos–Santos–Sentis, which is not
used here. -/
theorem exists_moment_approx {D : Matrix X X ℝ} {q : Quadrature V} {ε σ τ m : ℝ}
    {F : ℕ → Matrix X V ℝ} {ρ₀ : X → ℝ}
    (hD : D.transpose = -D) (hε : 0 < ε) (hσ : 0 < σ) (hτ : 0 < τ)
    (hm0 : 0 ≤ m) (hm : ∀ v, |q.μ v| ≤ m) (hF : IsImplicitEuler D q ε σ τ F)
    (h0 : F 0 = iso ρ₀) (k n : ℕ) :
    ∃ A : Matrix X (Fin k) ℝ, ‖weighted q (F n - A * vand q k)‖ ≤
      (ε * m / σ) ^ k * l2 ((D ^ k).mulVec ρ₀) := by
  have hb : ∀ i ≤ n, ‖weighted q (D ^ k * F i)‖ ≤ l2 ((D ^ k).mulVec ρ₀) := fun i _ => by
    have h1 := norm_pow_mul_le hD hε hσ hτ hF k i
    rwa [h0, mul_iso, norm_weighted_iso] at h1
  exact exists_moment_approx_of_bound (l := 0) hε hσ hτ hm0 hm hF h0 k n hb

/-- The distance form of the main theorem: `dist(F_n, M_{≤ k}) ≤ (ε m / σ)^k ‖D^k ρ₀‖₂`, for the
quadrature-weighted matrix.  This is the form that feeds `epsRank`. -/
theorem distLR_le {D : Matrix X X ℝ} {q : Quadrature V} {ε σ τ m : ℝ}
    {F : ℕ → Matrix X V ℝ} {ρ₀ : X → ℝ}
    (hD : D.transpose = -D) (hε : 0 < ε) (hσ : 0 < σ) (hτ : 0 < τ)
    (hm0 : 0 ≤ m) (hm : ∀ v, |q.μ v| ≤ m) (hF : IsImplicitEuler D q ε σ τ F)
    (h0 : F 0 = iso ρ₀) (k n : ℕ) :
    distLR k (weighted q (F n)) ≤ (ε * m / σ) ^ k * l2 ((D ^ k).mulVec ρ₀) := by
  obtain ⟨A, hA⟩ := exists_moment_approx hD hε hσ hτ hm0 hm hF h0 k n
  exact (distLR_weighted_le q _ (rank_mul_vand_le q A)).trans hA

/-- **Implicit Euler, arbitrary data, explicit in `ε`.**  With `F₀ = ρ₀ ⊗ 1 + g₀`, the distance
`dist(F_n, M_{≤ k})` is at most `(ε m / σ)^k ‖D^k F₀‖` plus the layer
`(ε² / (σ τ))^n ∑_{j<k} C(n+j-1,j) (ε m / σ)^j ‖D^j g₀‖`, so that
`σ_{k+1}(F_n) = O(ε^k + ε^{2n})` for fixed `σ, τ, D`.  The rank bound of Conjecture J for
ill-prepared data holds after `n ≥ k/2` steps. -/
theorem distLR_implicit_le {D : Matrix X X ℝ} {q : Quadrature V} {ε σ τ m : ℝ}
    {F : ℕ → Matrix X V ℝ} {ρ₀ : X → ℝ} {g₀ : Matrix X V ℝ}
    (hD : D.transpose = -D) (hε : 0 < ε) (hσ : 0 < σ) (hτ : 0 < τ)
    (hm0 : 0 ≤ m) (hm : ∀ v, |q.μ v| ≤ m) (hF : IsImplicitEuler D q ε σ τ F)
    (h0 : F 0 = iso ρ₀ + g₀) (k n : ℕ) :
    distLR k (weighted q (F n)) ≤ (ε * m / σ) ^ k * ‖weighted q (D ^ k * F 0)‖ +
      (ε ^ 2 / (σ * τ)) ^ n * ∑ j ∈ Finset.range k, ((n + j - 1).choose j : ℝ) *
        (ε * m / σ) ^ j * ‖weighted q (D ^ j * g₀)‖ := by
  obtain ⟨A, hA⟩ := exists_moment_approx_implicit hD hε hσ hτ hm0 hm hF h0 k n
  refine (distLR_weighted_le q _ (rank_mul_vand_le q A)).trans (hA.trans ?_)
  rw [add_comm, Finset.mul_sum]
  refine add_le_add_right (Finset.sum_le_sum fun j _ => ?_) _
  have ha := relaxA_nonneg (ε := ε) hσ hτ
  have ha1 := relaxA_le_one (ε := ε) hσ hτ
  have hb := relaxB_nonneg (ε := ε) hσ hτ
  have hb1 := relaxB_le (ε := ε) hσ hτ
  have hκ : 0 ≤ ε * m / σ := by positivity
  have h1 : (relaxA ε σ τ * (ε * m / σ)) ^ j ≤ (ε * m / σ) ^ j := by
    rw [mul_pow]
    have : relaxA ε σ τ ^ j ≤ 1 := pow_le_one₀ ha ha1
    have h2 : 0 ≤ (ε * m / σ) ^ j := by positivity
    nlinarith
  have h2 : relaxB ε σ τ ^ n ≤ (ε ^ 2 / (σ * τ)) ^ n := pow_le_pow_left₀ hb hb1 n
  calc ((n + j - 1).choose j : ℝ) * (relaxA ε σ τ * (ε * m / σ)) ^ j * relaxB ε σ τ ^ n *
        ‖weighted q (D ^ j * g₀)‖
      ≤ ((n + j - 1).choose j : ℝ) * (ε * m / σ) ^ j * (ε ^ 2 / (σ * τ)) ^ n *
        ‖weighted q (D ^ j * g₀)‖ := by gcongr
    _ = _ := by ring

end Main

/-! ### Singular values and the rank schedule -/

section Schedule

variable {X V : Type*} [Fintype X] [Fintype V] [DecidableEq V]

open Matrix in
/-- `σ_{k+1}(A) ≤ dist_F(A, M_{≤ k})` (`σ` is zero-indexed). -/
theorem singularValues_le_distLR (A : Matrix X V ℝ) (k : ℕ) :
    (toEuclideanLin A).singularValues k ≤ distLR k A := by
  have h1 : distLR k A = √(∑ i ∈ Finset.Ico k (Fintype.card V),
      (toEuclideanLin A).singularValues i ^ 2) := EckartYoung.infDist_setOf_rank_le A k
  by_cases hk : k < Fintype.card V
  · rw [h1]
    refine Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun i => (toEuclideanLin A).singularValues i ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_Ico.mpr ⟨le_rfl, hk⟩)
  · have h2 : (toEuclideanLin A).singularValues k = 0 := by
      apply LinearMap.singularValues_of_finrank_le
      simpa using not_lt.mp hk
    rw [h2]
    exact distLR_nonneg

variable [DecidableEq X]

/-- The singular-value form of the main theorem: `σ_{k+1}(F_n) ≤ (ε m / σ)^k ‖D^k ρ₀‖₂` for the
quadrature-weighted matrix (`singularValues` is zero-indexed).  This is the inequality of
Conjecture J, with `‖ρ₀‖` in place of `‖ρ(t)‖` and an explicit `C_k`. -/
theorem singularValues_le {D : Matrix X X ℝ} {q : Quadrature V} {ε σ τ m : ℝ}
    {F : ℕ → Matrix X V ℝ} {ρ₀ : X → ℝ}
    (hD : D.transpose = -D) (hε : 0 < ε) (hσ : 0 < σ) (hτ : 0 < τ)
    (hm0 : 0 ≤ m) (hm : ∀ v, |q.μ v| ≤ m) (hF : IsImplicitEuler D q ε σ τ F)
    (h0 : F 0 = iso ρ₀) (k n : ℕ) :
    (Matrix.toEuclideanLin (weighted q (F n))).singularValues k ≤
      (ε * m / σ) ^ k * l2 ((D ^ k).mulVec ρ₀) :=
  (singularValues_le_distLR _ k).trans (distLR_le hD hε hσ hτ hm0 hm hF h0 k n)

omit [DecidableEq V] [DecidableEq X] in
/-- `‖D x‖₂ ≤ ‖D‖_F ‖x‖₂`. -/
theorem l2_mulVec_le (D : Matrix X X ℝ) (x : X → ℝ) : l2 (D.mulVec x) ≤ ‖D‖ * l2 x := by
  rw [l2, l2, ← Real.sqrt_sq (norm_nonneg D), ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt (sum_sq_mulVec_le D x)

omit [DecidableEq V] in
/-- Every vector has `‖D^j ρ‖₂ ≤ K^j ‖ρ‖₂` with `K = ‖D‖_F`.  The mesh-dependent worst case of
the bandwidth hypothesis of `epsRank_schedule`; smooth data has a mesh-independent `K`. -/
theorem l2_pow_mulVec_le (D : Matrix X X ℝ) (ρ : X → ℝ) (j : ℕ) :
    l2 ((D ^ j).mulVec ρ) ≤ ‖D‖ ^ j * l2 ρ := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    calc l2 (D.mulVec ((D ^ j).mulVec ρ)) ≤ ‖D‖ * l2 ((D ^ j).mulVec ρ) := l2_mulVec_le _ _
      _ ≤ ‖D‖ * (‖D‖ ^ j * l2 ρ) := by gcongr
      _ = ‖D‖ ^ (j + 1) * l2 ρ := by ring

omit [DecidableEq V] in
/-- **Rank schedule, general form.**  If `(ε m / σ)^k ‖D^k ρ₀‖₂ ≤ tol` then
`rank_tol(F_n) ≤ k` for every `n`. -/
theorem epsRank_le_of_le {D : Matrix X X ℝ} {q : Quadrature V} {ε σ τ m tol : ℝ}
    {F : ℕ → Matrix X V ℝ} {ρ₀ : X → ℝ}
    (hD : D.transpose = -D) (hε : 0 < ε) (hσ : 0 < σ) (hτ : 0 < τ)
    (hm0 : 0 ≤ m) (hm : ∀ v, |q.μ v| ≤ m) (hF : IsImplicitEuler D q ε σ τ F)
    (h0 : F 0 = iso ρ₀) {k : ℕ} (hk : (ε * m / σ) ^ k * l2 ((D ^ k).mulVec ρ₀) ≤ tol) (n : ℕ) :
    epsRank tol (weighted q (F n)) ≤ k :=
  epsRank_le_of_distLR_le ((distLR_le hD hε hσ hτ hm0 hm hF h0 k n).trans hk)

omit [DecidableEq V] [Fintype X] [DecidableEq X] in
theorem pow_ceil_le {κ tol : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) (htol : 0 < tol) :
    κ ^ ⌈Real.log tol / Real.log κ⌉₊ ≤ tol := by
  have hlog : Real.log κ < 0 := Real.log_neg hκ0 hκ1
  have h1 : Real.log tol / Real.log κ ≤ ⌈Real.log tol / Real.log κ⌉₊ := Nat.le_ceil _
  have h2 := (div_le_iff_of_neg hlog).1 h1
  have h3 : Real.log (κ ^ ⌈Real.log tol / Real.log κ⌉₊) ≤ Real.log tol := by
    rw [Real.log_pow]
    exact h2
  exact (Real.log_le_log_iff (pow_pos hκ0 _) htol).1 h3

omit [DecidableEq V] in
/-- **Rank schedule, closed form.**  Let `K` be a bandwidth of the data,
`‖D^j ρ₀‖₂ ≤ K^j ‖ρ₀‖₂`, and let `κ = ε m K / σ < 1` be the effective expansion parameter.  Then
`F_n` has `(tol ‖ρ₀‖₂)`-rank at most `⌈log tol / log κ⌉`, for all `n` and `τ`, and the rank is
independent of the mesh when `K` is.  It matters because a rank-adaptive solver can then fix the
rank from `ε`, `σ`, and the smoothness of the data, without trial truncation.  It replaces the
formula `⌈log tol / log ε⌉ + 1`, which this gives only under a condition
(`epsRank_ideas_formula`) and which is false in general (`ideas_formula_fails`).  It gives the
mesh independence observed in OP-ST-41 for smooth data only. -/
theorem epsRank_schedule {D : Matrix X X ℝ} {q : Quadrature V} {ε σ τ m K tol : ℝ}
    {F : ℕ → Matrix X V ℝ} {ρ₀ : X → ℝ}
    (hD : D.transpose = -D) (hε : 0 < ε) (hσ : 0 < σ) (hτ : 0 < τ)
    (hm0 : 0 ≤ m) (hm : ∀ v, |q.μ v| ≤ m) (hF : IsImplicitEuler D q ε σ τ F)
    (h0 : F 0 = iso ρ₀) (hK : ∀ j, l2 ((D ^ j).mulVec ρ₀) ≤ K ^ j * l2 ρ₀)
    (hκ0 : 0 < ε * m * K / σ) (hκ1 : ε * m * K / σ < 1) (htol : 0 < tol) (n : ℕ) :
    epsRank (tol * l2 ρ₀) (weighted q (F n)) ≤
      ⌈Real.log tol / Real.log (ε * m * K / σ)⌉₊ := by
  refine epsRank_le_of_le hD hε hσ hτ hm0 hm hF h0 ?_ n
  set r := ⌈Real.log tol / Real.log (ε * m * K / σ)⌉₊
  have h1 := pow_ceil_le hκ0 hκ1 htol
  calc (ε * m / σ) ^ r * l2 ((D ^ r).mulVec ρ₀) ≤ (ε * m / σ) ^ r * (K ^ r * l2 ρ₀) := by
        gcongr
        exact hK r
    _ = (ε * m * K / σ) ^ r * l2 ρ₀ := by
        rw [← mul_assoc, ← mul_pow]
        congr 2
        ring
    _ ≤ tol * l2 ρ₀ := mul_le_mul_of_nonneg_right h1 (l2_nonneg ρ₀)

omit [DecidableEq V] in
/-- **When the formula `⌈log tol / log ε⌉ + 1` is right.**  With `r = ⌈log tol / log ε⌉ + 1` and
bandwidth `K`, the `(tol ‖ρ₀‖₂)`-rank of `F_n` is at most `r` as soon as
`(m K / σ)^r ε ≤ 1`, in particular whenever `m K ≤ σ` and `ε ≤ 1`.  The counterexample
`ideas_formula_fails` shows this condition cannot be dropped. -/
theorem epsRank_ideas_formula {D : Matrix X X ℝ} {q : Quadrature V} {ε σ τ m K tol : ℝ}
    {F : ℕ → Matrix X V ℝ} {ρ₀ : X → ℝ}
    (hD : D.transpose = -D) (hε : 0 < ε) (hε1 : ε < 1) (hσ : 0 < σ) (hτ : 0 < τ)
    (hm0 : 0 ≤ m) (hm : ∀ v, |q.μ v| ≤ m) (hF : IsImplicitEuler D q ε σ τ F)
    (h0 : F 0 = iso ρ₀) (hK : ∀ j, l2 ((D ^ j).mulVec ρ₀) ≤ K ^ j * l2 ρ₀) (htol : 0 < tol)
    (hC : (m * K / σ) ^ (⌈Real.log tol / Real.log ε⌉₊ + 1) * ε ≤ 1) (n : ℕ) :
    epsRank (tol * l2 ρ₀) (weighted q (F n)) ≤ ⌈Real.log tol / Real.log ε⌉₊ + 1 := by
  refine epsRank_le_of_le hD hε hσ hτ hm0 hm hF h0 ?_ n
  set r := ⌈Real.log tol / Real.log ε⌉₊
  have h1 : ε ^ r ≤ tol := pow_ceil_le hε hε1 htol
  have h2 : 0 ≤ l2 ρ₀ := l2_nonneg ρ₀
  calc (ε * m / σ) ^ (r + 1) * l2 ((D ^ (r + 1)).mulVec ρ₀)
      ≤ (ε * m / σ) ^ (r + 1) * (K ^ (r + 1) * l2 ρ₀) := by
        gcongr
        exact hK (r + 1)
    _ = ((m * K / σ) ^ (r + 1) * ε) * ε ^ r * l2 ρ₀ := by
        rw [← mul_assoc, ← mul_pow, show ε * m / σ * K = (m * K / σ) * ε by ring, mul_pow,
          pow_succ ε r]
        ring
    _ ≤ 1 * ε ^ r * l2 ρ₀ := by gcongr
    _ ≤ tol * l2 ρ₀ := by rw [one_mul]; gcongr

omit [DecidableEq V] in
/-- **IMEX Euler** (explicit transport, implicit scattering), well-prepared data: the rank bound
holds with `C` any bound for `‖D^k F_i‖` on the history, for arbitrary `D`.  Unlike the implicit
scheme, `C` is not controlled here: uniform-in-`ε` stability of the IMEX scheme is not proved. -/
theorem distLR_imex_le {D : Matrix X X ℝ} {q : Quadrature V} {ε σ τ m C : ℝ}
    {F : ℕ → Matrix X V ℝ} {ρ₀ : X → ℝ} (hε : 0 < ε) (hσ : 0 < σ) (hτ : 0 < τ)
    (hm0 : 0 ≤ m) (hm : ∀ v, |q.μ v| ≤ m) (hF : IsIMEXEuler D q ε σ τ F)
    (h0 : F 0 = iso ρ₀) (k n : ℕ) (hC : ∀ i ≤ n, ‖weighted q (D ^ k * F i)‖ ≤ C) :
    distLR k (weighted q (F n)) ≤ (ε * m / σ) ^ k * C := by
  obtain ⟨A, hA⟩ := exists_moment_approx_of_bound (l := 1) hε hσ hτ hm0 hm hF h0 k n hC
  exact (distLR_weighted_le q _ (rank_mul_vand_le q A)).trans hA

/-- Periodic central differences on `N` points with mesh width `h`. -/
noncomputable def centralDiff (N : ℕ) [NeZero N] (h : ℝ) : Matrix (ZMod N) (ZMod N) ℝ :=
  Matrix.of fun i j => ((if j = i + 1 then 1 else 0) - (if j = i - 1 then 1 else 0)) / (2 * h)

omit [DecidableEq V] in
/-- Periodic central differences satisfy the skew-symmetry hypothesis of the main theorem, so
the hypothesis holds for the standard discretisation. -/
theorem centralDiff_skew (N : ℕ) [NeZero N] (h : ℝ) :
    (centralDiff N h).transpose = -centralDiff N h := by
  ext i j
  simp only [centralDiff, Matrix.transpose_apply, Matrix.of_apply, Matrix.neg_apply]
  have h1 : (i = j + 1) ↔ (j = i - 1) := by
    constructor
    · rintro rfl; ring
    · rintro rfl; ring
  have h2 : (i = j - 1) ↔ (j = i + 1) := by
    constructor
    · rintro rfl; ring
    · rintro rfl; ring
  simp only [h1, h2]
  ring

end Schedule

/-! ### Sharpness -/

section Sharpness

theorem isStep_iso_iff {X V : Type*} [Fintype X] [Fintype V] {D : Matrix X X ℝ} {q : Quadrature V}
    {ε σ τ : ℝ} {g p : Matrix X V ℝ} {ρ : X → ℝ} :
    IsStep D q ε σ τ g (iso ρ) p ↔ ∀ i v, τ⁻¹ * (p i v - ρ i) + ε⁻¹ * (q.μ v * (D * g) i v) =
      (σ / ε ^ 2) * (avg q p i - p i v) := by
  rw [IsStep, ← Matrix.ext_iff]
  rfl

/-- For equal weights the weighted matrix is a multiple of the matrix. -/
theorem sum_sq_weighted_mulVec {X V : Type*} [Fintype X] [Fintype V] {q : Quadrature V} {c : ℝ}
    (hc : 0 ≤ c) (hw : ∀ v, q.w v = c) (f : Matrix X V ℝ) (x : V → ℝ) :
    ∑ i, ((weighted q f).mulVec x) i ^ 2 = c * ∑ i, (f.mulVec x) i ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (weighted q f).mulVec x i = √c * f.mulVec x i := by
    simp only [Matrix.mulVec, dotProduct, weighted, Matrix.of_apply, hw, Finset.mul_sum, mul_assoc]
  rw [h1, mul_pow, Real.sq_sqrt hc]

theorem rank_iso_le {X V : Type*} [Finite X] [Fintype V] (q : Quadrature V) (u : X → ℝ) :
    (iso u : Matrix X V ℝ).rank ≤ 1 := by
  obtain ⟨A, hA⟩ := exists_sum_mon_eq q 1 1 (fun _ => u)
  have h1 : (iso u : Matrix X V ℝ) = A * vand q 1 := by
    rw [← hA, iso_eq_mon q]
    simp
  rw [h1]
  exact rank_mul_vand_le q A

/-- Two velocities `±1` with equal weights: the telegraph model. -/
noncomputable def telegraph : Quadrature (Fin 2) where
  μ := ![1, -1]
  w := ![1 / 2, 1 / 2]
  w_pos := by intro v; fin_cases v <;> norm_num
  sum_w := by simp [Fin.sum_univ_two]; norm_num

/-- One Fourier mode with wave number `K`: the skew-symmetric block `[[0, K], [-K, 0]]`. -/
def rot (K : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, K; -K, 0]

theorem rot_skew (K : ℝ) : (rot K).transpose = -rot K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rot]

/-- The exact first iterate of the telegraph model. -/
def teleSol (r s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![r, r; r * s, -(r * s)]

theorem teleSol_step {ε σ τ K : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (hτ : 0 < τ) :
    IsStep (rot K) telegraph ε σ τ
      (teleSol ((σ + ε ^ 2 / τ) / (σ + ε ^ 2 / τ + τ * K ^ 2)) (ε * K / (σ + ε ^ 2 / τ)))
      (iso ![1, 0])
      (teleSol ((σ + ε ^ 2 / τ) / (σ + ε ^ 2 / τ + τ * K ^ 2)) (ε * K / (σ + ε ^ 2 / τ))) := by
  have h1 : σ + ε ^ 2 / τ + τ * K ^ 2 ≠ 0 := by positivity
  have h2 : σ + ε ^ 2 / τ ≠ 0 := by positivity
  rw [isStep_iso_iff]
  simp only [Fin.forall_fin_two]
  simp only [teleSol, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, telegraph, one_div, rot, Matrix.mul_apply, Fin.sum_univ_two, zero_mul,
    Matrix.cons_val_one, zero_add, one_mul, avg, mul_neg, neg_mul, neg_neg, and_self, sub_zero,
    add_zero, add_neg_cancel, zero_sub, neg_zero, sub_neg_eq_add]
  have h3 : σ * τ + ε ^ 2 ≠ 0 := by positivity
  have h4 : σ * τ + ε ^ 2 + τ ^ 2 * K ^ 2 ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

theorem distLR_teleSol {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    distLR 1 (weighted telegraph (teleSol r s)) = r * s := by
  have hw : ∀ v, telegraph.w v = 1 / 2 := by
    intro v; fin_cases v <;> simp [telegraph]
  apply le_antisymm
  · refine (distLR_weighted_le telegraph _ (rank_iso_le telegraph ![r, 0])).trans ?_
    have h1 : ‖weighted telegraph (teleSol r s - iso ![r, 0])‖ ^ 2 = (r * s) ^ 2 := by
      rw [sq_norm_weighted]
      simp [Fin.sum_univ_two, hw, teleSol, iso]
      ring
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h1.le
  · refine le_distLR_of_le_mulVec (by simp) (by positivity) fun x => ?_
    rw [sum_sq_weighted_mulVec (by norm_num) hw]
    simp only [Fin.sum_univ_two, Matrix.mulVec, dotProduct, teleSol]
    simp
    have h1 : s ^ 2 ≤ 1 := by nlinarith
    have h2 := sq_nonneg (x 0 + x 1)
    have h3 := mul_nonneg (sq_nonneg r) (mul_nonneg (sub_nonneg.2 h1) h2)
    nlinarith

/-- **Sharpness for `k = 1`: exact value in the telegraph model.**  Two velocities `±1`, one
Fourier mode of wave number `K`, data `ρ₀ = e₁`: `dist(F₁, M_{≤ 1}) = ε K / (σ + ε²/τ + τ K²)`,
while the main theorem gives `ε K / σ`.  So the power of `ε`, the factor `‖D ρ₀‖₂ = K`, and the
constant `1` of `distLR_le` are all attained in the limit `ε²/τ + τ K² ≪ σ`.  Mesh-independent
bounds in terms of `‖ρ₀‖₂` alone therefore do not hold. -/
theorem telegraph_distLR {ε σ τ K : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (hτ : 0 < τ) (hK : 0 ≤ K)
    (hs : ε * K ≤ σ + ε ^ 2 / τ) {F : ℕ → Matrix (Fin 2) (Fin 2) ℝ}
    (hF : IsImplicitEuler (rot K) telegraph ε σ τ F) (h0 : F 0 = iso ![1, 0]) :
    distLR 1 (weighted telegraph (F 1)) = ε * K / (σ + ε ^ 2 / τ + τ * K ^ 2) := by
  have h1 : F 1 = teleSol ((σ + ε ^ 2 / τ) / (σ + ε ^ 2 / τ + τ * K ^ 2))
      (ε * K / (σ + ε ^ 2 / τ)) := by
    refine (existsUnique_step (rot_skew K) hε hσ hτ (F 0)).unique (hF 0) ?_
    rw [h0]
    exact teleSol_step hε hσ hτ
  have h2 : 0 < σ + ε ^ 2 / τ := by positivity
  rw [h1, distLR_teleSol (by positivity) (by positivity) ((div_le_one h2).2 hs)]
  have h3 : σ + ε ^ 2 / τ + τ * K ^ 2 ≠ 0 := by positivity
  field_simp

/-! The three-velocity family -/

/-- Three velocities `-1, 0, 1` with equal weights. -/
noncomputable def threeV : Quadrature (Fin 3) where
  μ := ![-1, 0, 1]
  w := ![1 / 3, 1 / 3, 1 / 3]
  w_pos := by intro v; fin_cases v <;> norm_num
  sum_w := by simp [Fin.sum_univ_three]; norm_num

/-- The mean mode plus one Fourier mode of wave number `K`. -/
def rot3 (K : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 0, 0, K; 0, -K, 0]

theorem rot3_skew (K : ℝ) : (rot3 K).transpose = -rot3 K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rot3]

/-- The exact first iterate in the three-velocity family. -/
noncomputable def sol3 (h t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 1, 1; h / (1 + t ^ 2), h, h / (1 + t ^ 2);
    -(t * h / (1 + t ^ 2)), 0, t * h / (1 + t ^ 2)]

theorem sol3_step {ε σ τ t : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (hτ : 0 < τ) :
    IsStep (rot3 (t * (σ + ε ^ 2 / τ) / ε)) threeV ε σ τ
      (sol3 ((ε ^ 2 / τ) / (ε ^ 2 / τ + 2 * σ / 3 * (t ^ 2 / (1 + t ^ 2)))) t)
      (iso ![1, 1, 0])
      (sol3 ((ε ^ 2 / τ) / (ε ^ 2 / τ + 2 * σ / 3 * (t ^ 2 / (1 + t ^ 2)))) t) := by
  have ht : 1 + t ^ 2 ≠ 0 := by positivity
  have h3 : ε ^ 2 * (1 + t ^ 2) * 3 + 2 * σ * τ * t ^ 2 ≠ 0 := by positivity
  have h4 : ε ^ 2 / τ + 2 * σ / 3 * (t ^ 2 / (1 + t ^ 2)) ≠ 0 := by positivity
  rw [isStep_iso_iff]
  simp only [Fin.forall_fin_succ]
  simp only [sol3, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, sub_self, mul_zero, threeV, one_div, rot3, Matrix.mul_apply,
    Fin.sum_univ_three, mul_one, Matrix.cons_val_one, zero_mul, add_zero, Matrix.cons_val, mul_neg,
    neg_zero, avg, zero_eq_mul, div_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    pow_eq_zero_iff, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.cons_val_succ,
    IsEmpty.forall_iff, and_true, and_self, zero_add, neg_mul, one_mul, neg_neg, sub_zero,
    neg_add_cancel, sub_neg_eq_add, zero_sub, true_and]
  refine ⟨Or.inr (by norm_num), ⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> field_simp <;> ring

theorem threeV_w (v : Fin 3) : threeV.w v = 1 / 3 := by
  fin_cases v <;> simp [threeV]

theorem threeV_mu (v : Fin 3) : |threeV.μ v| ≤ 1 := by
  fin_cases v <;> simp [threeV]

/-- The squared Euclidean norm of `sol3 h t x`. -/
theorem sum_sq_sol3 (h t : ℝ) (x : Fin 3 → ℝ) :
    ∑ i, ((sol3 h t).mulVec x) i ^ 2 =
      (x 0 + x 1 + x 2) ^ 2 + (h * ((1 + t ^ 2)⁻¹ * (x 0 + x 2) + x 1)) ^ 2 +
        (t * h * (1 + t ^ 2)⁻¹ * (x 2 - x 0)) ^ 2 := by
  simp [Fin.sum_univ_three, Matrix.mulVec, dotProduct, sol3]
  ring

/-- The elementary inequality behind `le_distLR_sol3`. -/
theorem sol3_ineq {a h t α u e d : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (ht1 : t ^ 2 ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ha : a = h * (t ^ 2 * α)) (hs : t ^ 2 * α = 1 - α) :
    (a / 5) ^ 2 * (e ^ 2 + (u ^ 2 + d ^ 2) / 2) ≤
      1 / 3 * ((u + e) ^ 2 + (h * (α * u + e)) ^ 2 + (t * h * α * d) ^ 2) := by
  have hA : (a * u) ^ 2 ≤ 2 * (u + e) ^ 2 + 2 * (h * (α * u + e)) ^ 2 := by
    have h1 : a * u = h * (u + e) - h * (α * u + e) := by
      rw [ha, hs]; ring
    have h2 : h ^ 2 ≤ 1 := by nlinarith
    rw [h1]
    nlinarith [sq_nonneg (h * (u + e) + h * (α * u + e)),
      mul_nonneg (sub_nonneg.2 h2) (sq_nonneg (u + e))]
  have hB : (a * d) ^ 2 ≤ (t * h * α * d) ^ 2 := by
    have h1 : a * d = t * (t * h * α * d) := by rw [ha]; ring
    rw [h1, mul_pow]
    nlinarith [mul_nonneg (sub_nonneg.2 ht1) (sq_nonneg (t * h * α * d))]
  have hC : (a * e) ^ 2 ≤ 2 * (u + e) ^ 2 + 2 * (a * u) ^ 2 := by
    have h1 : a * e = a * (u + e) - a * u := by ring
    have h2 : a ^ 2 ≤ 1 := by nlinarith
    rw [h1]
    nlinarith [sq_nonneg (a * (u + e) + a * u), mul_nonneg (sub_nonneg.2 h2) (sq_nonneg (u + e))]
  have h1 : (a / 5) ^ 2 * (e ^ 2 + (u ^ 2 + d ^ 2) / 2) =
      ((a * e) ^ 2 + (a * u) ^ 2 / 2 + (a * d) ^ 2 / 2) / 25 := by ring
  rw [h1]
  have h2 := sq_nonneg (u + e)
  have h3 := sq_nonneg (h * (α * u + e))
  have h4 := sq_nonneg (t * h * α * d)
  linarith

/-- Lower bound for the smallest singular value in the three-velocity family. -/
theorem le_distLR_sol3 {h t : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    h * (t ^ 2 / (1 + t ^ 2)) / 5 ≤ distLR 2 (weighted threeV (sol3 h t)) := by
  have hpos : 0 < 1 + t ^ 2 := by positivity
  have hαe : (1 + t ^ 2)⁻¹ * (1 + t ^ 2) = 1 := inv_mul_cancel₀ hpos.ne'
  have hs : t ^ 2 / (1 + t ^ 2) = t ^ 2 * (1 + t ^ 2)⁻¹ := div_eq_mul_inv _ _
  have hs1 : t ^ 2 * (1 + t ^ 2)⁻¹ = 1 - (1 + t ^ 2)⁻¹ := by linarith
  have hα0 : 0 < (1 + t ^ 2)⁻¹ := inv_pos.mpr hpos
  rw [hs]
  have ha0 : 0 ≤ h * (t ^ 2 * (1 + t ^ 2)⁻¹) := by positivity
  have ha1 : h * (t ^ 2 * (1 + t ^ 2)⁻¹) ≤ 1 := by
    have h1 : t ^ 2 * (1 + t ^ 2)⁻¹ ≤ 1 := by rw [hs1]; linarith
    calc h * (t ^ 2 * (1 + t ^ 2)⁻¹) ≤ 1 * 1 := by gcongr
      _ = 1 := by norm_num
  refine le_distLR_of_le_mulVec (by simp) (by positivity) fun x => ?_
  rw [sum_sq_weighted_mulVec (by norm_num) threeV_w, sum_sq_sol3]
  simp only [Fin.sum_univ_three]
  have key := sol3_ineq (u := x 0 + x 2) (e := x 1) (d := x 2 - x 0) hh0 hh1
    (by nlinarith : t ^ 2 ≤ 1) ha0 ha1 rfl hs1
  have e1 : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 =
      x 1 ^ 2 + ((x 0 + x 2) ^ 2 + (x 2 - x 0) ^ 2) / 2 := by ring
  have e2 : x 0 + x 1 + x 2 = x 0 + x 2 + x 1 := by ring
  rw [e1, e2]
  exact key

/-- **Sharpness for `k = 2`.**  With three velocities, one Fourier mode plus the mean, and
`σ = τ = 1`: `(3/200) ε² ≤ dist(F₁, M_{≤ 2}) ≤ ε²` for all `ε ∈ (0, 1]`.  So the exponent `2` in
`distLR_le` cannot be improved. -/
theorem three_sharp_two {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {F : ℕ → Matrix (Fin 3) (Fin 3) ℝ}
    (hF : IsImplicitEuler (rot3 1) threeV ε 1 1 F) (h0 : F 0 = iso ![1, 1, 0]) :
    3 / 200 * ε ^ 2 ≤ distLR 2 (weighted threeV (F 1)) ∧
      distLR 2 (weighted threeV (F 1)) ≤ ε ^ 2 := by
  constructor
  · set t := ε / (1 + ε ^ 2) with ht
    have hK : t * ((1 : ℝ) + ε ^ 2 / 1) / ε = 1 := by
      rw [ht]; field_simp
    have hstep := sol3_step (t := t) hε one_pos one_pos
    rw [hK] at hstep
    have h1 : F 1 = _ := (existsUnique_step (rot3_skew 1) hε one_pos one_pos (F 0)).unique (hF 0)
      (by rw [h0]; exact hstep)
    rw [h1]
    have hpos : 0 < 1 + ε ^ 2 := by positivity
    have ht0 : 0 < t := by positivity
    have ht2 : ε / 2 ≤ t := by
      rw [ht, div_le_div_iff₀ (by norm_num) hpos]
      nlinarith
    have ht1 : t ≤ ε := by
      rw [ht, div_le_iff₀ hpos]
      nlinarith [sq_nonneg ε]
    have ht1' : t ≤ 1 := ht1.trans hε1
    set s := t ^ 2 / (1 + t ^ 2) with hs
    have hs0 : 0 ≤ s := by positivity
    have hs1 : s ≤ ε ^ 2 := by
      rw [hs, div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg t, sq_nonneg ε, mul_nonneg ht0.le ht0.le]
    have hs2 : ε ^ 2 / 8 ≤ s := by
      rw [hs, le_div_iff₀ (by positivity)]
      have h1 : ε ^ 2 / 4 ≤ t ^ 2 := by nlinarith
      have h2 : t ^ 2 ≤ 1 := by nlinarith
      nlinarith [mul_nonneg (sq_nonneg ε) (sub_nonneg.2 h2)]
    set h := ε ^ 2 / 1 / (ε ^ 2 / 1 + 2 * 1 / 3 * s) with hh
    have hden : 0 < ε ^ 2 / 1 + 2 * 1 / 3 * s := by positivity
    have hh1 : h ≤ 1 := by
      rw [hh, div_le_one hden]
      linarith
    have hh2 : 3 / 5 ≤ h := by
      rw [hh, le_div_iff₀ hden]
      linarith
    have h2 := le_distLR_sol3 (by linarith : (0 : ℝ) ≤ h) hh1 ht0.le ht1'
    refine le_trans ?_ h2
    have h3 : 3 / 5 * (ε ^ 2 / 8) ≤ h * s := by gcongr
    linarith
  · have h1 := distLR_le (m := 1) (rot3_skew 1) hε one_pos one_pos zero_le_one threeV_mu hF h0 2 1
    have h2 : l2 ((rot3 1 ^ 2).mulVec ![1, 1, 0]) = 1 := by
      simp [l2, pow_two, rot3, Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.mul_apply]
    rw [h2] at h1
    simpa using h1

/-- **The formula `⌈log tol / log ε⌉ + 1` is false as stated.**  For every `ε ≤ 1/10` the formula
`r(ε, tol) = ⌈log tol / log ε⌉ + 1` at `tol = ε` gives `r = 2`, but in the three-velocity family
with `σ = 1`, `τ = ε²` and wave number `K = 2/ε` the iterate `F₁` has `(ε ‖ρ₀‖₂)`-rank at least
`3`: the same matrix `sol3 (3/4) 1` occurs for every `ε`.  The effective parameter is
`ε ‖D‖ / σ`, not `ε` (`epsRank_schedule`).  The trajectory exists and is unique by
`existsUnique_implicitEuler`. -/
theorem ideas_formula_fails {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 10)
    {F : ℕ → Matrix (Fin 3) (Fin 3) ℝ}
    (hF : IsImplicitEuler (rot3 (2 / ε)) threeV ε 1 (ε ^ 2) F) (h0 : F 0 = iso ![1, 1, 0]) :
    ⌈Real.log ε / Real.log ε⌉₊ + 1 <
      epsRank (ε * l2 (![1, 1, 0] : Fin 3 → ℝ)) (weighted threeV (F 1)) := by
  have hτ : 0 < ε ^ 2 := by positivity
  have hK : (1 : ℝ) * (1 + ε ^ 2 / ε ^ 2) / ε = 2 / ε := by
    rw [div_self hτ.ne']; norm_num
  have hstep := sol3_step (t := 1) hε one_pos hτ
  rw [hK] at hstep
  have h1 : F 1 = _ := (existsUnique_step (rot3_skew (2 / ε)) hε one_pos hτ (F 0)).unique (hF 0)
    (by rw [h0]; exact hstep)
  have hh : ε ^ 2 / ε ^ 2 / (ε ^ 2 / ε ^ 2 + 2 * 1 / 3 * (1 ^ 2 / (1 + 1 ^ 2))) = (3 / 4 : ℝ) := by
    rw [div_self hτ.ne']; norm_num
  rw [hh] at h1
  have hlow : (3 / 20 : ℝ) ≤ distLR 2 (weighted threeV (F 1)) := by
    rw [h1]
    refine le_distLR_of_le_mulVec (by simp) (by norm_num) fun x => ?_
    rw [sum_sq_weighted_mulVec (by norm_num) threeV_w, sum_sq_sol3]
    simp only [Fin.sum_univ_three]
    nlinarith [sq_nonneg (x 0 + x 2 + 22 / 19 * x 1), sq_nonneg (x 2 - x 0), sq_nonneg (x 1)]
  have hlog : Real.log ε ≠ 0 := (Real.log_neg hε (by linarith)).ne
  have hr : ⌈Real.log ε / Real.log ε⌉₊ + 1 = 2 := by
    rw [div_self hlog]; simp
  have hl2 : l2 (![1, 1, 0] : Fin 3 → ℝ) < 3 / 2 := by
    have : l2 (![1, 1, 0] : Fin 3 → ℝ) = √2 := by
      simp [l2, Fin.sum_univ_three]
      norm_num
    rw [this, Real.sqrt_lt' (by norm_num)]
    norm_num
  have htol : ε * l2 (![1, 1, 0] : Fin 3 → ℝ) < 3 / 20 := by
    have h2 := l2_nonneg (![1, 1, 0] : Fin 3 → ℝ)
    nlinarith
  rw [hr]
  by_contra hc
  have h2 := (epsRank_le_iff (mul_nonneg hε.le (l2_nonneg _))).1 (not_lt.mp hc)
  linarith

end Sharpness

/-! ### Uniform stability of the IMEX scheme -/

section IMEX

variable {X V : Type*} [Fintype X] [Fintype V]

omit [Fintype X] in
theorem avg_sub (q : Quadrature V) (x y : Matrix X V ℝ) : avg q (x - y) = avg q x - avg q y := by
  funext i
  simp [avg, mul_sub, Finset.sum_sub_distrib]

omit [Fintype X] in
theorem avg_iso (q : Quadrature V) (u : X → ℝ) : avg q (iso u : Matrix X V ℝ) = u := by
  funext i
  simp only [avg, iso, Matrix.of_apply]
  rw [← Finset.sum_mul, q.sum_w, one_mul]

/-- The matrix `f diag(μ)`, entries `μ_v f_{iv}`. -/
def scaleMu (q : Quadrature V) (f : Matrix X V ℝ) : Matrix X V ℝ :=
  Matrix.of fun i v => q.μ v * f i v

theorem transport_eq_mul (D : Matrix X X ℝ) (q : Quadrature V) (f : Matrix X V ℝ) :
    transport D q f = D * scaleMu q f := by
  rw [scaleMu, mul_of_scale]
  rfl

/-- The average of a step: `⟨p⟩ = ⟨f⟩ - (τ/ε) D ⟨μ g⟩`.  Scattering conserves the average. -/
theorem IsStep.avg_eq {D : Matrix X X ℝ} {q : Quadrature V} {ε σ τ : ℝ} {g f p : Matrix X V ℝ}
    (hε : 0 < ε) (hτ : 0 < τ) (h : IsStep D q ε σ τ g f p) :
    avg q p = avg q f - (τ / ε) • D.mulVec (avg q (scaleMu q g)) := by
  have h1 := congrArg (avg q) h
  rw [avg_add, avg_smul, avg_smul, avg_smul, avg_sub, avg_sub, avg_iso, sub_self, smul_zero,
    transport_eq_mul, avg_mul] at h1
  funext i
  have h2 := congrFun h1 i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, smul_eq_mul] at h2 ⊢
  field_simp at h2 ⊢
  linarith

omit [Fintype X] in
theorem sq_avg_le (q : Quadrature V) (f : Matrix X V ℝ) (i : X) :
    avg q f i ^ 2 ≤ ∑ v, q.w v * f i v ^ 2 := by
  have h1 := sum_w_mul_avg_sub_le q f i
  have h2 : ∑ v, q.w v * f i v * (avg q f i - f i v) =
      avg q f i ^ 2 - ∑ v, q.w v * f i v ^ 2 := by
    have h3 : avg q f i ^ 2 = avg q f i * ∑ v, q.w v * f i v := by
      rw [pow_two]; rfl
    rw [h3, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  linarith

theorem l2_avg_le (q : Quadrature V) (f : Matrix X V ℝ) : l2 (avg q f) ≤ ‖weighted q f‖ := by
  rw [l2, ← Real.sqrt_sq (norm_nonneg (weighted q f)), sq_norm_weighted]
  exact Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => sq_avg_le q f i)

theorem weighted_mul (D : Matrix X X ℝ) (q : Quadrature V) (f : Matrix X V ℝ) :
    weighted q (D * f) = D * weighted q f := by
  exact mul_of_scale D (fun v => √(q.w v)) f |>.symm

theorem norm_weighted_mul_le (D : Matrix X X ℝ) (q : Quadrature V) (f : Matrix X V ℝ) :
    ‖weighted q (D * f)‖ ≤ ‖D‖ * ‖weighted q f‖ := by
  rw [weighted_mul]
  exact Frobenius.norm_mul_le D _

theorem l2_add_le (q : Quadrature V) (u w : X → ℝ) : l2 (u + w) ≤ l2 u + l2 w := by
  rw [← norm_weighted_iso q u, ← norm_weighted_iso q w, ← norm_weighted_iso q (u + w), iso_add]
  have h : weighted q ((iso u : Matrix X V ℝ) + iso w) = weighted q (iso u) + weighted q (iso w) :=
    (weightedL q).map_add _ _
  rw [h]
  exact norm_add_le _ _

theorem l2_smul (r : ℝ) (u : X → ℝ) : l2 (r • u) = |r| * l2 u := by
  simp only [l2, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs]

omit [Fintype X] in
theorem scaleMu_sub (q : Quadrature V) (x y : Matrix X V ℝ) :
    scaleMu q (x - y) = scaleMu q x - scaleMu q y := by
  ext i v
  simp [scaleMu, mul_sub]

theorem norm_weighted_scaleMu_le {q : Quadrature V} {m : ℝ} (hm0 : 0 ≤ m) (hm : ∀ v, |q.μ v| ≤ m)
    (f : Matrix X V ℝ) : ‖weighted q (scaleMu q f)‖ ≤ m * ‖weighted q f‖ :=
  norm_weighted_scale q hm0 hm f

variable [DecidableEq X]

omit [DecidableEq X] in
/-- IMEX Euler is explicit in the transport term, so a trajectory exists for all `ε, σ, τ > 0`
and every `D`. -/
theorem exists_imexEuler (D : Matrix X X ℝ) (q : Quadrature V) {ε σ τ : ℝ} (hε : 0 < ε)
    (hσ : 0 < σ) (hτ : 0 < τ) (f₀ : Matrix X V ℝ) :
    ∃ F : ℕ → Matrix X V ℝ, F 0 = f₀ ∧ IsIMEXEuler D q ε σ τ F := by
  have key : ∀ f : Matrix X V ℝ, ∃ p, IsStep D q ε σ τ f f p := fun f => by
    set r := avg q f - (τ / ε) • avg q (transport D q f) with hr
    set p := relaxB ε σ τ • f + relaxA ε σ τ • (iso r : Matrix X V ℝ) +
      (relaxA ε σ τ * (-ε / σ)) • transport D q f with hp
    have hab := relaxA_add_relaxB (ε := ε) hσ hτ
    have hcoef : relaxA ε σ τ * (-ε / σ) = -(relaxB ε σ τ * (τ / ε)) := by
      unfold relaxA relaxB
      field_simp
    have havg : avg q p = r := by
      rw [hp, avg_add, avg_add, avg_smul, avg_smul, avg_smul, avg_iso, hcoef]
      funext i
      simp only [hr, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      have h1 : relaxA ε σ τ = 1 - relaxB ε σ τ := by linarith
      rw [h1]
      ring
    refine ⟨p, ?_⟩
    rw [IsStep, havg]
    ext i v
    simp only [hp, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    generalize (iso r : Matrix X V ℝ) i v = y
    generalize transport D q f i v = t
    generalize f i v = x
    have h1 : σ + ε ^ 2 / τ ≠ 0 := by positivity
    have h2 : σ * τ + ε ^ 2 ≠ 0 := by positivity
    unfold relaxA relaxB
    field_simp
    ring
  choose S hS using key
  exact ⟨fun n => Nat.rec f₀ (fun _ y => S y) n, rfl, fun n => hS _⟩

/-- The growth factor of the IMEX scheme per step: `1 + β + √β / 2` with `β = τ A² / σ`. -/
noncomputable def imexGrowth (τ σ A : ℝ) : ℝ := 1 + τ * A ^ 2 / σ + √(τ * A ^ 2 / σ) / 2

omit [Fintype X] [Fintype V] [DecidableEq X] in
theorem one_le_imexGrowth {τ σ A : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) : 1 ≤ imexGrowth τ σ A := by
  unfold imexGrowth
  have h1 : 0 ≤ τ * A ^ 2 / σ := by positivity
  have h2 := Real.sqrt_nonneg (τ * A ^ 2 / σ)
  linarith

omit [Fintype X] [Fintype V] [DecidableEq X] in
theorem relax_coeff_le {ε σ τ A : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (hτ : 0 < τ) :
    relaxA ε σ τ * (ε / σ) * A ≤ √(τ * A ^ 2 / σ) / 2 := by
  have hL : 0 < σ + ε ^ 2 / τ := by positivity
  have h1 : relaxA ε σ τ * (ε / σ) * A = ε * A / (σ + ε ^ 2 / τ) := by
    unfold relaxA; field_simp
  rw [h1, le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  refine Real.le_sqrt_of_sq_le ?_
  rw [div_mul_eq_mul_div, div_pow, div_le_iff₀ (by positivity)]
  set L := ε ^ 2 / τ with hLdef
  have h2 : ε ^ 2 = τ * L := by rw [hLdef]; field_simp
  have h3 : (ε * A * 2) ^ 2 = 4 * (τ * L) * A ^ 2 := by rw [← h2]; ring
  have h4 : τ * A ^ 2 / σ * (σ + L) ^ 2 = τ * A ^ 2 * ((σ + L) ^ 2 / σ) := by ring
  rw [h3, h4]
  have h5 : 4 * L ≤ (σ + L) ^ 2 / σ := by
    rw [le_div_iff₀ hσ]
    nlinarith [sq_nonneg (σ - L)]
  have h6 : 0 ≤ τ * A ^ 2 := by positivity
  nlinarith

omit [DecidableEq X] in
/-- One step of the stability estimate for IMEX Euler.  The term `ε⁻¹ ⟨μ F⟩` of the mass balance
looks singular; the rank-one bound of `exists_moment_approx_of_bound` shows it is bounded, because
`⟨μ⟩ = 0`. -/
theorem imex_step_le {D : Matrix X X ℝ} {q : Quadrature V} {ε σ τ m Y : ℝ}
    {F : ℕ → Matrix X V ℝ} {ρ₀ : X → ℝ} (hμ : ∑ v, q.w v * q.μ v = 0)
    (hε : 0 < ε) (hσ : 0 < σ) (hτ : 0 < τ) (hm0 : 0 ≤ m) (hm : ∀ v, |q.μ v| ≤ m)
    (hF : IsIMEXEuler D q ε σ τ F) (h0 : F 0 = iso ρ₀) (n : ℕ)
    (hY : ∀ i ≤ n, ‖weighted q (F i)‖ ≤ Y) :
    ‖weighted q (F (n + 1))‖ ≤ imexGrowth τ σ (m * ‖D‖) * Y := by
  classical
  have hY0 : 0 ≤ Y := (norm_nonneg _).trans (hY 0 (Nat.zero_le n))
  have hDY : ∀ i ≤ n, ‖weighted q (D ^ 1 * F i)‖ ≤ ‖D‖ * Y := fun i hi => by
    rw [pow_one]
    exact (norm_weighted_mul_le D q _).trans (by gcongr; exact hY i hi)
  obtain ⟨A, hA⟩ := exists_moment_approx_of_bound (l := 1) hε hσ hτ hm0 hm hF h0 1 n hDY
  rw [pow_one] at hA
  -- the flux only sees the part of `F n` of degree `≥ 1`
  have hflux : avg q (scaleMu q (F n)) = avg q (scaleMu q (F n - A * vand q 1)) := by
    rw [scaleMu_sub, avg_sub]
    have h1 : avg q (scaleMu q (A * vand q 1)) = 0 := by
      funext i
      have h2 : ∀ v, (A * vand q 1) i v = A i 0 := fun v => by
        simp [Matrix.mul_apply, vand]
      simp only [avg, scaleMu, Matrix.of_apply, h2, Pi.zero_apply]
      have h3 : ∑ v, q.w v * (q.μ v * A i 0) = (∑ v, q.w v * q.μ v) * A i 0 := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun v _ => by ring
      rw [h3, hμ, zero_mul]
    rw [h1, sub_zero]
  have hfl2 : l2 (avg q (scaleMu q (F n))) ≤ m * (ε * m / σ * (‖D‖ * Y)) := by
    rw [hflux]
    refine (l2_avg_le q _).trans ((norm_weighted_scaleMu_le hm0 hm _).trans ?_)
    gcongr
  -- the mass balance
  have hρ : l2 (avg q (F (n + 1))) ≤ (1 + τ * (m * ‖D‖) ^ 2 / σ) * Y := by
    rw [(hF n).avg_eq hε hτ, sub_eq_add_neg, ← neg_smul]
    refine (l2_add_le q _ _).trans ?_
    rw [l2_smul, abs_neg, abs_of_pos (by positivity : 0 < τ / ε)]
    have h1 : l2 (avg q (F n)) ≤ Y := (l2_avg_le q _).trans (hY n le_rfl)
    have h2 : l2 (D.mulVec (avg q (scaleMu q (F n)))) ≤ ‖D‖ * (m * (ε * m / σ * (‖D‖ * Y))) :=
      (l2_mulVec_le D _).trans (by gcongr)
    calc l2 (avg q (F n)) + τ / ε * l2 (D.mulVec (avg q (scaleMu q (F n))))
        ≤ Y + τ / ε * (‖D‖ * (m * (ε * m / σ * (‖D‖ * Y)))) := by gcongr
      _ = (1 + τ * (m * ‖D‖) ^ 2 / σ) * Y := by field_simp
  -- the update
  have ha := relaxA_nonneg (ε := ε) hσ hτ
  have hb := relaxB_nonneg (ε := ε) hσ hτ
  have hab := relaxA_add_relaxB (ε := ε) hσ hτ
  have hupd := (hF n).eq' hε hσ hτ
  have hw : weighted q (F (n + 1)) = relaxB ε σ τ • weighted q (F n) +
      relaxA ε σ τ • weighted q (iso (avg q (F (n + 1)))) +
      (relaxA ε σ τ * (-ε / σ)) • weighted q (transport D q (F n)) := by
    conv_lhs => rw [hupd]
    change weightedL q (relaxB ε σ τ • F n + relaxA ε σ τ • iso (avg q (F (n + 1))) +
      (relaxA ε σ τ * (-ε / σ)) • transport D q (F n)) = _
    rw [map_add, map_add, map_smul, map_smul, map_smul]
    rfl
  have hT : ‖weighted q (transport D q (F n))‖ ≤ m * ‖D‖ * Y := by
    rw [transport_eq_mul]
    refine (norm_weighted_mul_le D q _).trans ?_
    have h1 : ‖weighted q (scaleMu q (F n))‖ ≤ m * Y :=
      (norm_weighted_scaleMu_le hm0 hm (F n)).trans
        (mul_le_mul_of_nonneg_left (hY n le_rfl) hm0)
    calc ‖D‖ * ‖weighted q (scaleMu q (F n))‖ ≤ ‖D‖ * (m * Y) := by gcongr
      _ = m * ‖D‖ * Y := by ring
  have hcabs : |relaxA ε σ τ * (-ε / σ)| = relaxA ε σ τ * (ε / σ) := by
    rw [abs_mul, abs_of_nonneg ha, abs_div, abs_neg, abs_of_pos hε, abs_of_pos hσ]
  have hc0 : 0 ≤ relaxA ε σ τ * (ε / σ) := by positivity
  have hA1 := relax_coeff_le (A := m * ‖D‖) hε hσ hτ
  rw [hw]
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  rw [norm_smul, norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb,
    Real.norm_eq_abs, hcabs, norm_weighted_iso]
  have h1 : relaxB ε σ τ * ‖weighted q (F n)‖ ≤ relaxB ε σ τ * Y := by
    gcongr; exact hY n le_rfl
  have h2 : relaxA ε σ τ * l2 (avg q (F (n + 1))) ≤
      relaxA ε σ τ * ((1 + τ * (m * ‖D‖) ^ 2 / σ) * Y) := by gcongr
  have h3 : relaxA ε σ τ * (ε / σ) * ‖weighted q (transport D q (F n))‖ ≤
      relaxA ε σ τ * (ε / σ) * (m * ‖D‖ * Y) := by gcongr
  have h4 : relaxA ε σ τ * (ε / σ) * (m * ‖D‖) * Y ≤
      √(τ * (m * ‖D‖) ^ 2 / σ) / 2 * Y := by gcongr
  have h5 : 0 ≤ τ * (m * ‖D‖) ^ 2 / σ * Y := by positivity
  have h6 : relaxA ε σ τ * (τ * (m * ‖D‖) ^ 2 / σ * Y) ≤ τ * (m * ‖D‖) ^ 2 / σ * Y := by
    have := relaxA_le_one (ε := ε) hσ hτ
    nlinarith
  unfold imexGrowth
  nlinarith

omit [DecidableEq X] in
/-- **Stability of IMEX Euler, uniform in `ε`.**  For well-prepared data and a quadrature with
`⟨μ⟩ = 0`, `‖F_i‖ ≤ Θ^n ‖ρ₀‖₂` for `i ≤ n`, with `Θ = 1 + β + √β/2`, `β = τ m² ‖D‖_F² / σ`, for
any `D` and every `ε > 0`.  The constant is mesh dependent and grows with `n`. -/
theorem imex_stable {D : Matrix X X ℝ} {q : Quadrature V} {ε σ τ m : ℝ}
    {F : ℕ → Matrix X V ℝ} {ρ₀ : X → ℝ} (hμ : ∑ v, q.w v * q.μ v = 0)
    (hε : 0 < ε) (hσ : 0 < σ) (hτ : 0 < τ) (hm0 : 0 ≤ m) (hm : ∀ v, |q.μ v| ≤ m)
    (hF : IsIMEXEuler D q ε σ τ F) (h0 : F 0 = iso ρ₀) (n : ℕ) :
    ∀ i ≤ n, ‖weighted q (F i)‖ ≤ imexGrowth τ σ (m * ‖D‖) ^ n * l2 ρ₀ := by
  have hΘ := one_le_imexGrowth (A := m * ‖D‖) hσ hτ
  have hl := l2_nonneg ρ₀
  induction n with
  | zero =>
    intro i hi
    obtain rfl : i = 0 := by omega
    rw [h0, norm_weighted_iso, pow_zero, one_mul]
  | succ n ih =>
    intro i hi
    rcases Nat.lt_or_ge i (n + 1) with h | h
    · refine (ih i (by omega)).trans ?_
      rw [pow_succ]
      nlinarith [mul_nonneg (pow_nonneg (by linarith : 0 ≤ imexGrowth τ σ (m * ‖D‖)) n) hl]
    · obtain rfl : i = n + 1 := by omega
      have h1 := imex_step_le hμ hε hσ hτ hm0 hm hF h0 n ih
      calc _ ≤ _ := h1
        _ = _ := by rw [pow_succ]; ring

/-- **IMEX Euler, unconditional.**  For well-prepared data and a quadrature with `⟨μ⟩ = 0`,
`dist(F_n, M_{≤ k}) ≤ (ε m / σ)^k Θ^n ‖D^k ρ₀‖₂`, for every `D` and every `ε > 0`.  This is the
IMEX part of the discrete statement.  Unlike the implicit scheme it needs
`⟨μ⟩ = 0`, and the constant depends on `n` and on the mesh. -/
theorem distLR_imex_uniform {D : Matrix X X ℝ} {q : Quadrature V} {ε σ τ m : ℝ}
    {F : ℕ → Matrix X V ℝ} {ρ₀ : X → ℝ} (hμ : ∑ v, q.w v * q.μ v = 0)
    (hε : 0 < ε) (hσ : 0 < σ) (hτ : 0 < τ) (hm0 : 0 ≤ m) (hm : ∀ v, |q.μ v| ≤ m)
    (hF : IsIMEXEuler D q ε σ τ F) (h0 : F 0 = iso ρ₀) (k n : ℕ) :
    distLR k (weighted q (F n)) ≤
      (ε * m / σ) ^ k * (imexGrowth τ σ (m * ‖D‖) ^ n * l2 ((D ^ k).mulVec ρ₀)) := by
  have hG : IsIMEXEuler D q ε σ τ (fun i => D ^ k * F i) := fun i =>
    (hF i).mul_left (Commute.pow_left (Commute.refl D) k).eq
  have hG0 : D ^ k * F 0 = iso ((D ^ k).mulVec ρ₀) := by rw [h0, mul_iso]
  exact distLR_imex_le hε hσ hτ hm0 hm hF h0 k n (imex_stable hμ hε hσ hτ hm0 hm hG hG0 n)

/-- One velocity with `μ = 1`, so that `⟨μ⟩ = 1`: pure drift. -/
noncomputable def drift : Quadrature (Fin 1) where
  μ := fun _ => 1
  w := fun _ => 1
  w_pos := fun _ => one_pos
  sum_w := by simp

/-- **`⟨μ⟩ = 0` cannot be dropped in `imex_stable`.**  For pure drift, `σ = τ = 1`, `D = rot 1`,
and well-prepared data of norm `1`, the first IMEX iterate has norm at least `1 / ε`, while the
bound of `imex_stable` does not depend on `ε`. -/
theorem imex_unstable_of_mean_ne_zero {ε : ℝ} (hε : 0 < ε)
    {F : ℕ → Matrix (Fin 2) (Fin 1) ℝ} (hF : IsIMEXEuler (rot 1) drift ε 1 1 F)
    (h0 : F 0 = iso ![1, 0]) :
    1 / ε ≤ ‖weighted drift (F 1)‖ := by
  refine le_trans ?_ (l2_avg_le drift (F 1))
  have h1 := (hF 0).avg_eq hε one_pos
  have h2 : scaleMu drift (F 0) = F 0 := by
    ext i v
    simp [scaleMu, drift]
  rw [h2, h0, avg_iso] at h1
  have h3 : avg drift (F 1) 1 = 1 / ε := by
    rw [h1]
    simp [rot]
  have h4 : (1 / ε) ^ 2 ≤ ∑ i, avg drift (F 1) i ^ 2 := by
    rw [← h3]
    exact Finset.single_le_sum (f := fun i => avg drift (F 1) i ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ 1)
  exact Real.le_sqrt_of_sq_le h4

end IMEX

/-! ### The exact flow in time -/

section Flow

variable {X V : Type*} [Fintype X] [Fintype V]

/-- The generator `-ε⁻¹ D f diag(μ) + σ ε⁻² (⟨f⟩ - f)` of the semi-discrete equation. -/
noncomputable def genL (D : Matrix X X ℝ) (q : Quadrature V) (ε σ : ℝ) :
    Matrix X V ℝ →ₗ[ℝ] Matrix X V ℝ where
  toFun f := (σ / ε ^ 2) • (iso (avg q f) - f) - ε⁻¹ • transport D q f
  map_add' x y := by
    have h := (transportL D q).map_add x y
    simp only [transportL_apply] at h
    rw [avg_add, iso_add, h]
    module
  map_smul' r x := by
    have h := (transportL D q).map_smul r x
    simp only [transportL_apply] at h
    rw [avg_smul, iso_smul, h, RingHom.id_apply]
    module

/-- The generator as a continuous linear map. -/
noncomputable def genC (D : Matrix X X ℝ) (q : Quadrature V) (ε σ : ℝ) :
    Matrix X V ℝ →L[ℝ] Matrix X V ℝ := LinearMap.toContinuousLinearMap (genL D q ε σ)

/-- `weighted` as a continuous linear map. -/
noncomputable def weightedC (q : Quadrature V) : Matrix X V ℝ →L[ℝ] Matrix X V ℝ :=
  LinearMap.toContinuousLinearMap (weightedL q)

/-- The semi-discrete equation has a solution for every initial value. -/
theorem exists_flow (D : Matrix X X ℝ) (q : Quadrature V) (ε σ : ℝ) (f₀ : Matrix X V ℝ) :
    ∃ y : ℝ → Matrix X V ℝ, y 0 = f₀ ∧ ∀ s, HasDerivAt y (genL D q ε σ (y s)) s := by
  have : CompleteSpace (Matrix X V ℝ) := FiniteDimensional.complete ℝ _
  refine ⟨fun s => NormedSpace.exp (s • genC D q ε σ) f₀, by simp, fun s => ?_⟩
  have h := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (genC D q ε σ) s).clm_apply
    (hasDerivAt_const s f₀)
  have h2 : HasDerivAt (fun s => NormedSpace.exp (s • genC D q ε σ) f₀)
      (genC D q ε σ (NormedSpace.exp (s • genC D q ε σ) f₀)) s := by
    simpa using h
  exact h2

/-- Consistency of implicit Euler with the flow: `y(v) - (v - u) y'(v) - y(u) = O((v - u)²)`, in
the weighted norm and uniformly on `[0, t]`. -/
theorem flow_defect_le (D : Matrix X X ℝ) (q : Quadrature V) (ε σ : ℝ) {y : ℝ → Matrix X V ℝ}
    (hy : ∀ s, HasDerivAt y (genL D q ε σ (y s)) s) (t : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ t →
      ‖weighted q (y v - (v - u) • genL D q ε σ (y v) - y u)‖ ≤ L * (v - u) ^ 2 := by
  set W := weightedC (X := X) q with hW
  set A := genC D q ε σ with hAdef
  have hy' : ∀ s, HasDerivAt y (A (y s)) s := hy
  have hcont : Continuous y := continuous_iff_continuousAt.2 fun s => (hy' s).continuousAt
  have hA : ∀ s, HasDerivAt (fun s => A (y s)) (A (A (y s))) s := fun s =>
    A.hasFDerivAt.comp_hasDerivAt s (hy' s)
  have hWA : ∀ s, HasDerivAt (fun s => W (A (y s))) (W (A (A (y s)))) s := fun s =>
    W.hasFDerivAt.comp_hasDerivAt s (hA s)
  have hc2 : Continuous fun s => W (A (A (y s))) := by fun_prop
  obtain ⟨L₀, hL₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn
    hc2.continuousOn
  refine ⟨max L₀ 0, le_max_right _ _, fun u v hu huv hv => ?_⟩
  set L := max L₀ 0 with hL
  have hL0 : 0 ≤ L := le_max_right _ _
  have hbound : ∀ s ∈ Set.Icc u v, ‖W (A (A (y s)))‖ ≤ L := fun s hs =>
    (hL₀ s ⟨hu.trans hs.1, hs.2.trans hv⟩).trans (le_max_left _ _)
  have lip : ∀ s ∈ Set.Icc u v, ‖W (A (y s)) - W (A (y v))‖ ≤ L * (v - u) := fun s hs => by
    have h1 := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := Set.Icc u v)
      (f := fun s => W (A (y s))) (fun x _ => (hWA x).hasDerivWithinAt) hbound
      (convex_Icc u v) (Set.right_mem_Icc.2 huv) hs
    refine h1.trans ?_
    rw [Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (by linarith [hs.2])]
    exact mul_le_mul_of_nonneg_left (by linarith [hs.1]) hL0
  have hh : ∀ s, HasDerivAt (fun s => W (y s) - s • W (A (y v)))
      (W (A (y s)) - W (A (y v))) s := fun s => by
    have h1 := W.hasFDerivAt.comp_hasDerivAt s (hy' s)
    have h2 := ((hasDerivAt_id s).smul_const (W (A (y v))))
    have h3 : HasDerivAt (fun s => W (y s) - s • W (A (y v)))
        (W (A (y s)) - (1 : ℝ) • W (A (y v))) s := h1.sub h2
    rwa [one_smul] at h3
  have h3 := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := Set.Icc u v)
    (fun x _ => (hh x).hasDerivWithinAt) lip (convex_Icc u v) (Set.left_mem_Icc.2 huv)
    (Set.right_mem_Icc.2 huv)
  have h4 : weighted q (y v - (v - u) • genL D q ε σ (y v) - y u) =
      W (y v) - v • W (A (y v)) - (W (y u) - u • W (A (y v))) := by
    have h5 : weighted q (y v - (v - u) • genL D q ε σ (y v) - y u) =
        W (y v) - (v - u) • W (A (y v)) - W (y u) := by
      change W _ = _
      rw [map_sub, map_sub, map_smul]
      rfl
    rw [h5]
    module
  rw [h4]
  refine h3.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  ring

theorem stepOp_eq (D : Matrix X X ℝ) (q : Quadrature V) (ε σ τ : ℝ) (p : Matrix X V ℝ) :
    stepOp D q ε σ τ p = τ⁻¹ • p - genL D q ε σ p := by
  change τ⁻¹ • p + ε⁻¹ • transport D q p - (σ / ε ^ 2) • (iso (avg q p) - p) =
    τ⁻¹ • p - ((σ / ε ^ 2) • (iso (avg q p) - p) - ε⁻¹ • transport D q p)
  module

/-- **Convergence of implicit Euler to the flow**, in the weighted norm: first order in `τ`. -/
theorem implicitEuler_error {D : Matrix X X ℝ} {q : Quadrature V} {ε σ : ℝ}
    (hD : D.transpose = -D) (hε : 0 < ε) (hσ : 0 < σ) {y : ℝ → Matrix X V ℝ}
    (hy : ∀ s, HasDerivAt y (genL D q ε σ (y s)) s) {t : ℝ} (ht : 0 < t) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (N : ℕ), 0 < N → ∀ F : ℕ → Matrix X V ℝ, F 0 = y 0 →
      IsImplicitEuler D q ε σ (t / N) F → ‖weighted q (y t - F N)‖ ≤ L * t ^ 2 / N := by
  obtain ⟨L, hL0, hL⟩ := flow_defect_le D q ε σ hy t
  refine ⟨L, hL0, fun N hN F hF0 hF => ?_⟩
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set τ := t / N with hτdef
  have hτ : 0 < τ := by positivity
  have key : ∀ n : ℕ, n ≤ N → ‖weighted q (y (n * τ) - F n)‖ ≤ n * (L * τ ^ 2) := by
    intro n
    induction n with
    | zero =>
      intro _
      have h0 : weighted q ((0 : Matrix X V ℝ)) = 0 := (weightedL q).map_zero
      simp [hF0, h0]
    | succ n ih =>
      intro hn
      have hle : ((n : ℝ) + 1) * τ ≤ t := by
        have h1 : ((n : ℝ) + 1) ≤ N := by exact_mod_cast hn
        calc ((n : ℝ) + 1) * τ ≤ N * τ := by gcongr
          _ = t := by rw [hτdef]; field_simp
      set p := y (((n + 1 : ℕ) : ℝ) * τ) with hp
      set f := y ((n : ℝ) * τ) with hf
      set δ := p - τ • genL D q ε σ p - f with hδ
      have hδb : ‖weighted q δ‖ ≤ L * τ ^ 2 := by
        have h1 := hL ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ) (by positivity)
          (by push_cast; nlinarith) (by push_cast; exact hle)
        have h2 : ((n + 1 : ℕ) : ℝ) * τ - (n : ℝ) * τ = τ := by push_cast; ring
        rwa [h2] at h1
      have hstep : IsStep D q ε σ τ (p - F (n + 1)) (f + δ - F n) (p - F (n + 1)) := by
        rw [isStep_iff_stepOp, map_sub, isStep_iff_stepOp.1 (hF n), stepOp_eq]
        have h1 : f + δ = p - τ • genL D q ε σ p := by rw [hδ]; abel
        rw [h1, smul_sub, smul_sub, smul_smul, inv_mul_cancel₀ hτ.ne', one_smul]
      have h2 := hstep.norm_le hD hε hσ hτ
      have h3 : weighted q (f + δ - F n) = weighted q (f - F n) + weighted q δ := by
        have h4 : f + δ - F n = (f - F n) + δ := by abel
        rw [h4]
        exact (weightedL q).map_add _ _
      rw [h3] at h2
      have h4 := ih (by omega)
      calc ‖weighted q (p - F (n + 1))‖ ≤ ‖weighted q (f - F n) + weighted q δ‖ := h2
        _ ≤ ‖weighted q (f - F n)‖ + ‖weighted q δ‖ := norm_add_le _ _
        _ ≤ n * (L * τ ^ 2) + L * τ ^ 2 := add_le_add h4 hδb
        _ = ((n + 1 : ℕ) : ℝ) * (L * τ ^ 2) := by push_cast; ring
  have h1 := key N le_rfl
  have h2 : (N : ℝ) * τ = t := by rw [hτdef]; field_simp
  rw [h2] at h1
  refine h1.trans (le_of_eq ?_)
  rw [hτdef]
  field_simp

variable [DecidableEq X]

/-- **The exact flow in time.**  The semi-discrete equation
`∂_t f + ε⁻¹ D f diag(μ) = σ ε⁻² (⟨f⟩ - f)` on any skew-symmetric `D`, with well-prepared data,
satisfies `dist(f(t), M_{≤ k}) ≤ (ε m / σ)^k ‖D^k ρ₀‖₂` for all `t ≥ 0`.  This is the
time-continuous version of `distLR_le`, obtained from it by `τ → 0`, because its constant does
not depend on `τ`.  It matters because it needs no time discretisation at all.  It is the form of
Conjecture J for discrete `x` and `v`, with `ρ₀` in place of `ρ(t)`; this covers
trigonometric-polynomial data in `x` with discrete velocities, where `D` is exact differentiation
on a finite-dimensional invariant space. -/
theorem distLR_flow_le {D : Matrix X X ℝ} {q : Quadrature V} {ε σ m : ℝ} {ρ₀ : X → ℝ}
    (hD : D.transpose = -D) (hε : 0 < ε) (hσ : 0 < σ) (hm0 : 0 ≤ m) (hm : ∀ v, |q.μ v| ≤ m)
    {y : ℝ → Matrix X V ℝ} (hy : ∀ s, HasDerivAt y (genL D q ε σ (y s)) s)
    (h0 : y 0 = iso ρ₀) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    distLR k (weighted q (y t)) ≤ (ε * m / σ) ^ k * l2 ((D ^ k).mulVec ρ₀) := by
  rcases ht.eq_or_lt with rfl | ht
  · obtain ⟨F, ⟨hF0, hF⟩, -⟩ := existsUnique_implicitEuler (q := q) hD hε hσ one_pos (iso ρ₀)
    have h1 := distLR_le hD hε hσ one_pos hm0 hm hF hF0 k 0
    rwa [hF0, ← h0] at h1
  · obtain ⟨L, hL0, hL⟩ := implicitEuler_error hD hε hσ hy ht
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    obtain ⟨N, hN⟩ := exists_nat_gt (L * t ^ 2 / δ + 1)
    have hN1 : (1 : ℝ) < N := by
      have : 0 ≤ L * t ^ 2 / δ := by positivity
      linarith
    have hN0 : 0 < N := by
      have : (0 : ℝ) < N := by linarith
      exact_mod_cast this
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN0
    have hτ : 0 < t / N := by positivity
    obtain ⟨F, ⟨hF0, hF⟩, -⟩ := existsUnique_implicitEuler (q := q) hD hε hσ hτ (y 0)
    have h1 := hL N hN0 F hF0 hF
    have h2 := distLR_le hD hε hσ hτ hm0 hm hF (hF0.trans h0) k N
    have h3 := distLR_le_add (r := k) (weighted q (y t)) (weighted q (F N))
    have h4 : weighted q (y t) - weighted q (F N) = weighted q (y t - F N) :=
      ((weightedL q).map_sub _ _).symm
    rw [h4] at h3
    have h5 : L * t ^ 2 / N ≤ δ := by
      rw [div_le_iff₀ hN']
      have h6 : L * t ^ 2 / δ < N := by linarith
      rw [div_lt_iff₀ hδ] at h6
      nlinarith
    linarith

end Flow

end LeanDLRA.Novel.EpsRank
