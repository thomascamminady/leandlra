import LeanDLRA.Research.StiffOrderReduction

/-!
# No stiffness-uniform global bound for the rank-adaptive BUG integrator when the forcing may
vary on the scale of the step

The rank-adaptive BUG integrator (`MatrixBUG.IsRankAdaptiveStep`, truncation tolerance zero) is
applied with step size `h` to the stiff linear problem `Y' = Y N + G(t)` on `2 × 2` matrices,
`N = -diag(0, λ)`, where the forcing is piecewise constant in time with period `3 h`: in step
`k` it is `cycleForcing … (k mod 3)`. The step size is therefore part of the data.

One cycle of three steps, from the state `σ w vᵀ` of rank one (`w = e₁`, `v = (c, s)`):

* *active step* (forcing `u eᵀ` with `u = e₂`, `e = e₁`): the order reduction of
  `StiffOrderReduction`. The added content is damped with `μ = λ s²`; the result is
  `(σ w + α u) vᵀ` with `α = g(h) c`, where the exact solution gains `h u eᵀ`;
* *free step*: both augmented bases span everything, the step is the exact flow, and the state
  gets rank two;
* *return step* (forcing `-(α c / h) u eᵀ`): the start has rank two, the step is the exact flow,
  and it ends on `σ w vᵀ`.

The numerical solution is `3 h`-periodic (`exists_cycle`). The exact solution gains `h - α c`
in the entry `(u, e)` in every cycle (`exists_exact_cycle`), and that entry is not damped. For
`λ s² h ≥ 2` the error after `J` cycles is at least `J h / 2` (`half_le_norm_sub_exactState`):
one sixth of the elapsed time `3 J h`.

## Which hypotheses of a bound `C (h (1 + |log h|) + ε + n ϑ)` hold for the family

* The forcing does not depend on the solution (Lipschitz constant zero).
* It is bounded: `‖G‖² = (σ λ s)² + p² + q²` (`norm_sq_forcing`) with `|p| ≤ 1`
  (`abs_gain_mul_div_le`) and `|q| ≤ |s|` (`abs_kill_le`); for `σ λ ≤ 1` this is at most
  `1 + 2 s²`.
* `N` is symmetric negative semidefinite, so the smoothing estimates of arXiv 1803.10473,
  Assumption 1(a), hold with `ω = 0` and a constant independent of `λ`.
* The normal component of the forcing at the start of the active step is `|s|`
  (`norm_normal_forcing_active`); the return step starts from a state of full rank, where it
  vanishes.
* The truncation tolerance is zero.
* **Not satisfied:** regularity of the forcing in time that is uniform in `h`. The forcing jumps
  at the grid points by about one, so its variation over a time interval of length one is of
  size `1 / h`.

So `not_exists_uniform_global_bound` excludes a bound `K (h (1 + |log h|) + s)` only for forcing
that may vary on the scale of the step. It says nothing about forcing whose regularity in time
is bounded independently of `h`.
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace StiffGlobalCycle

open MatrixBUG StiffOrderReduction

/-! ### Data -/

/-- The stiff operator `N = -diag(0, λ)`. -/
def N (lam : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, -lam]

/-- The left basis `w = e₁` of the start of a cycle. -/
def U₀ : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

/-- A `1 × 1` coefficient matrix. -/
def S₀ (σ : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := !![σ]

/-- The right basis `v = (c, s)`. -/
def V₀ (c s : ℝ) : Matrix (Fin 2) (Fin 1) ℝ := !![c; s]

/-- A unit vector `(a, b)` as a left basis. -/
def U₁ (a b : ℝ) : Matrix (Fin 2) (Fin 1) ℝ := !![a; b]

/-- The state with rows `σ v` and `(a, b)`. The start of a cycle is
`state c s σ 0 0 = σ w vᵀ`. -/
def state (c s σ a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![σ * c, σ * s; a, b]

/-- The forcing with lower row `(p, q)`. Its upper row keeps `σ w vᵀ` stationary. -/
def forcing (s lam σ p q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, σ * lam * s; p, q]

/-- `α = g(h) c` with `g = damp (λ s²)`: what the active step produces in the direction
`u vᵀ`. -/
noncomputable def gain (c s lam h : ℝ) : ℝ := damp (lam * s ^ 2) h * c

/-- The forcing in the entry `(u, f)` during the free step; it brings that entry to zero. -/
noncomputable def kill (c s lam h : ℝ) : ℝ :=
  lam * (gain c s lam h * s) - gain c s lam h * s / damp lam h

/-- **The forcing of the cycle**: step `k` of the integration uses `cycleForcing … (k mod 3)`.
It depends on the step size `h`. -/
noncomputable def cycleForcing (c s lam σ h : ℝ) : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ :=
  ![forcing s lam σ 1 0, forcing s lam σ 0 (kill c s lam h),
    forcing s lam σ (-(gain c s lam h * c / h)) 0]

/-- The solution of `X' = X N + forcing … p q` that starts at `state c s σ a₀ b₀`. -/
noncomputable def rowTraj (c s lam σ p q a₀ b₀ t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  state c s σ a₀ b₀ + (t • !![0, 0; p, 0] + damp lam t • !![0, 0; 0, q - lam * b₀])

/-- The entry `(u, f)` after a step of size `h` with forcing `q` in that entry. -/
noncomputable def rowEnd (lam h q b₀ : ℝ) : ℝ := b₀ + (q - lam * b₀) * damp lam h

/-- Entrywise evaluation of an identity between small explicit matrices. -/
local macro "entries" : tactic =>
  `(tactic| (ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Fin.sum_univ_one, Matrix.vecHead, Matrix.vecTail, Matrix.transpose_apply,
      N, U₀, S₀, V₀, U₁, state, forcing, rowTraj] <;>
    first | ring1 | (left; ring1) | skip))

variable {c s lam σ h : ℝ}

lemma damp_pos {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) : 0 < damp μ t := by
  unfold damp
  have h1 : Real.exp (-(μ * t)) < 1 := by
    have h2 := Real.exp_lt_exp.2 (show -(μ * t) < 0 by nlinarith)
    rwa [Real.exp_zero] at h2
  exact div_pos (by linarith) hμ

lemma rowTraj_zero (c s lam σ p q a₀ b₀ : ℝ) :
    rowTraj c s lam σ p q a₀ b₀ 0 = state c s σ a₀ b₀ := by
  simp [rowTraj]

lemma rowTraj_end (c s lam σ p q a₀ b₀ t : ℝ) :
    rowTraj c s lam σ p q a₀ b₀ t = state c s σ (a₀ + t * p) (rowEnd lam t q b₀) := by
  unfold rowEnd
  entries

/-- The field along `rowTraj`. -/
lemma field_rowTraj (hl : lam ≠ 0) (p q a₀ b₀ t : ℝ) :
    field (N lam) (forcing s lam σ p q) t (rowTraj c s lam σ p q a₀ b₀ t)
      = (1 : ℝ) • !![0, 0; p, 0] + Real.exp (-(lam * t)) • !![0, 0; 0, q - lam * b₀] := by
  rw [← one_sub_mul_damp hl t]
  simp only [field]
  entries

/-- **The exact flow**: `rowTraj` solves `X' = X N + forcing … p q`. -/
theorem odeSolution_rowTraj (hl : lam ≠ 0) (p q a₀ b₀ a b : ℝ) :
    ODESolution (field (N lam) (forcing s lam σ p q)) (rowTraj c s lam σ p q a₀ b₀) a b := by
  refine ODESolution.of_hasDerivAt (fun t => ?_) a b
  rw [field_rowTraj hl]
  exact (((hasDerivAt_id t).smul_const _).add
    ((hasDerivAt_damp hl t).smul_const _)).const_add _

/-! ### The active step -/

/-- The derivative `u eᵀ` of the exact solution in the active step. -/
def D : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]

/-- The active step satisfies the hypotheses of `StiffOrderReduction.Data` with `μ = λ s²`. -/
theorem data (hcs : c ^ 2 + s ^ 2 = 1) (hl : 0 < lam) (hs : s ≠ 0) :
    Data U₀ (S₀ σ) (V₀ c s) (N lam) (forcing s lam σ 1 0) D (lam * s ^ 2) where
  orthU₀ := by entries
  orthV₀ := by
    entries
    linear_combination hcs
  pos := by positivity
  compr := by entries
  deriv := by
    simp only [D]
    entries
  ker := by
    simp only [D]
    entries

lemma orthV₀ (hcs : c ^ 2 + s ^ 2 = 1) : (V₀ c s)ᵀ * V₀ c s = 1 := by
  entries
  linear_combination hcs

/-- The result of the active step is `(σ w + α u) vᵀ`. -/
lemma active_result (hcs : c ^ 2 + s ^ 2 = 1) :
    (1 : Matrix (Fin 2) (Fin 2) ℝ) * ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *
        xTraj (V₀ c s) U₀ (S₀ σ) (V₀ c s) D (lam * s ^ 2) h) * (V₀ c s)ᵀ
      = state c s σ (gain c s lam h * c) (gain c s lam h * s) := by
  rw [xTraj, orthV₀ hcs, kTraj]
  simp only [Matrix.mul_one, sub_self, Matrix.mul_zero, smul_zero, add_zero]
  simp only [D, gain]
  entries

/-- **The active step** is a rank-adaptive BUG step from `σ w vᵀ` to `(σ w + α u) vᵀ`, with the
augmented left basis the whole space and the augmented right basis `v` (the L-step is
stationary). -/
theorem isRankAdaptiveStep_active (hcs : c ^ 2 + s ^ 2 = 1) (hl : 0 < lam) (hs : s ≠ 0)
    (h : ℝ) :
    IsRankAdaptiveStep (field (N lam) (cycleForcing c s lam σ h 0)) 0 0 h U₀ (S₀ σ) (V₀ c s)
      (1 : Matrix (Fin 2) (Fin 2) ℝ) (V₀ c s)
      (kTraj U₀ (S₀ σ) (V₀ c s) D (lam * s ^ 2)) (lTraj U₀ (S₀ σ) (V₀ c s) D)
      (fun t => (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *
        xTraj (V₀ c s) U₀ (S₀ σ) (V₀ c s) D (lam * s ^ 2) t)
      (state c s σ (gain c s lam h * c) (gain c s lam h * s)) := by
  have hd := data (σ := σ) hcs hl hs
  have hleft : Dᵀ * U₀ = 0 := by
    simp only [D]
    entries
  rw [← active_result hcs]
  exact StiffOrderReduction.isRankAdaptiveStep hd
    (hd.bases_self hleft (by simp) (by simp)) (by simp)

/-- The start of the active step is `σ w vᵀ`. -/
lemma start_eq : U₀ * S₀ σ * (V₀ c s)ᵀ = state c s σ 0 0 := by
  entries

/-! ### The free step -/

/-- The K-step of the free step. -/
noncomputable def kFree (s lam σ α r t : ℝ) : Matrix (Fin 2) (Fin 1) ℝ :=
  !![σ; α] + damp (lam * s ^ 2) t • !![0; r * s - lam * s ^ 2 * α]

/-- The L-step of the free step. -/
noncomputable def lFree (c s lam σ r a b ρ t : ℝ) : Matrix (Fin 2) (Fin 1) ℝ :=
  !![ρ * c; ρ * s] + damp lam t • !![0; σ * lam * s * a + r * b - lam * (ρ * s)]

lemma kField_kFree (hμ : lam * s ^ 2 ≠ 0) (α r t : ℝ) :
    kField (V₀ c s) (field (N lam) (forcing s lam σ 0 r)) t (kFree s lam σ α r t)
      = Real.exp (-(lam * s ^ 2 * t)) • !![0; r * s - lam * s ^ 2 * α] := by
  rw [← one_sub_mul_damp hμ t]
  simp only [kField, field, kFree]
  entries

lemma lField_lFree (hl : lam ≠ 0) {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) (r ρ t : ℝ) :
    lField (U₁ a b) (field (N lam) (forcing s lam σ 0 r)) t (lFree c s lam σ r a b ρ t)
      = Real.exp (-(lam * t)) • !![0; σ * lam * s * a + r * b - lam * (ρ * s)] := by
  rw [← one_sub_mul_damp hl t]
  simp only [lField, field, lFree]
  entries
  linear_combination
    (-(lam * (ρ * s + damp lam t * (σ * lam * s * a + r * b - lam * (ρ * s))))) * hab

lemma sField_one (F : ℝ → Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) :
    sField (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ) F = F := by
  funext t S
  simp [sField]

/-- The free step in terms of the factors `(a, b)`, `ρ` of its start `ρ (a, b)ᵀ vᵀ`. -/
lemma isRankAdaptiveStep_free_aux (hcs : c ^ 2 + s ^ 2 = 1) (hl : lam ≠ 0)
    (hμ : lam * s ^ 2 ≠ 0) {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) (ρ r h : ℝ) :
    IsRankAdaptiveStep (field (N lam) (forcing s lam (ρ * a) 0 r)) 0 0 h (U₁ a b) (S₀ ρ)
      (V₀ c s) (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (kFree s lam (ρ * a) (ρ * b) r) (lFree c s lam (ρ * a) r a b ρ)
      (rowTraj c s lam (ρ * a) 0 r (ρ * b * c) (ρ * b * s))
      (rowTraj c s lam (ρ * a) 0 r (ρ * b * c) (ρ * b * s) h) where
  orthU₀ := by
    entries
    linear_combination hab
  orthV₀ := orthV₀ hcs
  kSol := by
    refine ODESolution.of_hasDerivAt (fun t => ?_) 0 h
    rw [kField_kFree hμ]
    exact ((hasDerivAt_damp hμ t).smul_const _).const_add _
  kStart := by
    simp only [kFree, damp_zero, zero_smul, add_zero]
    entries
  lSol := by
    refine ODESolution.of_hasDerivAt (fun t => ?_) 0 h
    rw [lField_lFree hl hab]
    exact ((hasDerivAt_damp hl t).smul_const _).const_add _
  lStart := by
    simp only [lFree, damp_zero, zero_smul, add_zero]
    entries
  orthUa := by simp
  kCap := by simp
  augU := by simp
  orthVa := by simp
  lCap := by simp
  augV := by simp
  sSol := by
    rw [sField_one]
    exact odeSolution_rowTraj hl _ _ _ _ 0 h
  sStart := by
    rw [rowTraj_zero]
    entries
  trunc := by simp

/-- The end of the free step: the entry `(u, f)` is zero. -/
lemma rowEnd_kill (hd : damp lam h ≠ 0) (α : ℝ) :
    rowEnd lam h (lam * (α * s) - α * s / damp lam h) (α * s) = 0 := by
  unfold rowEnd
  field_simp
  ring

/-- **The free step** is a rank-adaptive BUG step from `(σ w + α u) vᵀ = ρ (a, b)ᵀ vᵀ` to the
state with second row `(α c, 0)`; both augmented bases are the whole space. -/
theorem isRankAdaptiveStep_free (hcs : c ^ 2 + s ^ 2 = 1) (hl : lam ≠ 0)
    (hμ : lam * s ^ 2 ≠ 0) (hd : damp lam h ≠ 0) {a b ρ : ℝ} (hab : a ^ 2 + b ^ 2 = 1)
    (hρa : ρ * a = σ) (hρb : ρ * b = gain c s lam h) :
    IsRankAdaptiveStep (field (N lam) (cycleForcing c s lam σ h 1)) 0 0 h (U₁ a b) (S₀ ρ)
      (V₀ c s) (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (kFree s lam σ (gain c s lam h) (kill c s lam h))
      (lFree c s lam σ (kill c s lam h) a b ρ)
      (rowTraj c s lam σ 0 (kill c s lam h) (gain c s lam h * c) (gain c s lam h * s))
      (state c s σ (gain c s lam h * c) 0) := by
  have key := isRankAdaptiveStep_free_aux hcs hl hμ hab ρ (kill c s lam h) h
  rw [hρa, hρb] at key
  have e : rowTraj c s lam σ 0 (kill c s lam h) (gain c s lam h * c) (gain c s lam h * s) h
      = state c s σ (gain c s lam h * c) 0 := by
    rw [rowTraj_end, mul_zero, add_zero]
    unfold kill
    rw [rowEnd_kill hd]
  rw [e] at key
  simpa [cycleForcing] using key

/-- The start of the free step is the result of the active step. -/
lemma free_start {a b ρ : ℝ} (hρa : ρ * a = σ) (hρb : ρ * b = gain c s lam h) :
    U₁ a b * S₀ ρ * (V₀ c s)ᵀ = state c s σ (gain c s lam h * c) (gain c s lam h * s) := by
  rw [← hρa, ← hρb]
  entries

/-! ### The return step -/

/-- The return step: all three substeps are the exact flow `t ↦ state + t p u eᵀ`. -/
def retTraj (c s σ a₀ p t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  state c s σ a₀ 0 + t • !![0, 0; p, 0]

/-- The L-step of the return step, the transpose of `retTraj`. -/
def lRet (c s σ a₀ p t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (state c s σ a₀ 0)ᵀ + t • !![0, p; 0, 0]

lemma field_retTraj (a₀ p t : ℝ) :
    field (N lam) (forcing s lam σ p 0) t (retTraj c s σ a₀ p t) = !![0, 0; p, 0] := by
  simp only [field, retTraj]
  entries

lemma odeSolution_retTraj (a₀ p a b : ℝ) :
    ODESolution (field (N lam) (forcing s lam σ p 0)) (retTraj c s σ a₀ p) a b := by
  refine ODESolution.of_hasDerivAt (fun t => ?_) a b
  rw [field_retTraj]
  have h1 : HasDerivAt (fun x : ℝ => state c s σ a₀ 0 + x • !![0, 0; p, 0])
      ((1 : ℝ) • !![0, 0; p, 0]) t := ((hasDerivAt_id t).smul_const _).const_add _
  rw [one_smul] at h1
  exact h1

lemma lField_lRet (a₀ p t : ℝ) :
    lField (1 : Matrix (Fin 2) (Fin 2) ℝ) (field (N lam) (forcing s lam σ p 0)) t
      (lRet c s σ a₀ p t) = !![0, p; 0, 0] := by
  simp only [lField, field, lRet]
  entries

lemma retTraj_end (hh : h ≠ 0) (a₀ : ℝ) :
    retTraj c s σ a₀ (-(a₀ / h)) h = state c s σ 0 0 := by
  have e : a₀ + h * (-(a₀ / h)) = 0 := by
    field_simp
    ring
  simp only [retTraj]
  entries
  linarith [e]

/-- **The return step** is a rank-adaptive BUG step from the state with second row `(α c, 0)`
(taken with the identity as both bases) to `σ w vᵀ`; every substep is the exact flow. -/
theorem isRankAdaptiveStep_return (hh : h ≠ 0) :
    IsRankAdaptiveStep (field (N lam) (cycleForcing c s lam σ h 2)) 0 0 h
      (1 : Matrix (Fin 2) (Fin 2) ℝ) (state c s σ (gain c s lam h * c) 0)
      (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (retTraj c s σ (gain c s lam h * c) (-(gain c s lam h * c / h)))
      (lRet c s σ (gain c s lam h * c) (-(gain c s lam h * c / h)))
      (retTraj c s σ (gain c s lam h * c) (-(gain c s lam h * c / h)))
      (state c s σ 0 0) := by
  have hF : cycleForcing c s lam σ h 2 = forcing s lam σ (-(gain c s lam h * c / h)) 0 := by
    simp [cycleForcing]
  rw [hF]
  exact
    { orthU₀ := by simp
      orthV₀ := by simp
      kSol := by
        have e : kField (1 : Matrix (Fin 2) (Fin 2) ℝ)
            (field (N lam) (forcing s lam σ (-(gain c s lam h * c / h)) 0))
            = field (N lam) (forcing s lam σ (-(gain c s lam h * c / h)) 0) := by
          funext t K
          simp [kField]
        rw [e]
        exact odeSolution_retTraj _ _ 0 h
      kStart := by simp [retTraj]
      lSol := by
        refine ODESolution.of_hasDerivAt (fun t => ?_) 0 h
        rw [lField_lRet]
        have h1 : HasDerivAt (fun x : ℝ => (state c s σ (gain c s lam h * c) 0)ᵀ
              + x • !![0, -(gain c s lam h * c / h); 0, 0])
            ((1 : ℝ) • !![0, -(gain c s lam h * c / h); 0, 0]) t :=
          ((hasDerivAt_id t).smul_const _).const_add _
        rw [one_smul] at h1
        exact h1
      lStart := by simp [lRet]
      orthUa := by simp
      kCap := by simp
      augU := by simp
      orthVa := by simp
      lCap := by simp
      augV := by simp
      sSol := by
        rw [sField_one]
        exact odeSolution_retTraj _ _ 0 h
      sStart := by simp [retTraj]
      trunc := by
        rw [retTraj_end hh]
        simp }

/-! ### One cycle of the integrator -/

/-- **The numerical solution is periodic.** For `σ ≠ 0` the three steps of a cycle are
rank-adaptive BUG steps with truncation tolerance zero that lead from `σ w vᵀ` back to
`σ w vᵀ`. Every step starts from a factorisation of the previous result with an invertible
coefficient matrix: `ρ ≠ 0` for the free step, and the return step starts from the identity
bases, with a coefficient matrix of nonzero determinant when `c`, `s` and the gain are not
zero. -/
theorem exists_cycle (hcs : c ^ 2 + s ^ 2 = 1) (hl : 0 < lam) (hs : s ≠ 0) (hσ : σ ≠ 0)
    (hh : 0 < h) :
    ∃ (a b ρ : ℝ) (K₁ L₁ Sa₁ K₂ L₂ : ℝ → Matrix (Fin 2) (Fin 1) ℝ)
      (Sa₂ K₃ L₃ Sa₃ : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (Y₁ Y₂ : Matrix (Fin 2) (Fin 2) ℝ),
      IsRankAdaptiveStep (field (N lam) (cycleForcing c s lam σ h 0)) 0 0 h U₀ (S₀ σ) (V₀ c s)
        (1 : Matrix (Fin 2) (Fin 2) ℝ) (V₀ c s) K₁ L₁ Sa₁ Y₁ ∧
      U₁ a b * S₀ ρ * (V₀ c s)ᵀ = Y₁ ∧ ρ ≠ 0 ∧
      IsRankAdaptiveStep (field (N lam) (cycleForcing c s lam σ h 1)) 0 0 h (U₁ a b) (S₀ ρ)
        (V₀ c s) (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ) K₂ L₂ Sa₂ Y₂ ∧
      Y₂.det = -(σ * s * (gain c s lam h * c)) ∧
      IsRankAdaptiveStep (field (N lam) (cycleForcing c s lam σ h 2)) 0 0 h
        (1 : Matrix (Fin 2) (Fin 2) ℝ) Y₂ (1 : Matrix (Fin 2) (Fin 2) ℝ)
        (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ) K₃ L₃ Sa₃
        (U₀ * S₀ σ * (V₀ c s)ᵀ) := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = Real.sqrt (σ ^ 2 + gain c s lam h ^ 2) := ⟨_, rfl⟩
  have hpos : 0 < σ ^ 2 + gain c s lam h ^ 2 := by positivity
  have hρ0 : 0 < ρ := by
    rw [hρ]
    exact Real.sqrt_pos.2 hpos
  have hρ2 : ρ ^ 2 = σ ^ 2 + gain c s lam h ^ 2 := by
    rw [hρ, Real.sq_sqrt hpos.le]
  have hab : (σ / ρ) ^ 2 + (gain c s lam h / ρ) ^ 2 = 1 := by
    rw [div_pow, div_pow, ← add_div, ← hρ2]
    exact div_self (pow_ne_zero 2 hρ0.ne')
  have hρa : ρ * (σ / ρ) = σ := mul_div_cancel₀ σ hρ0.ne'
  have hρb : ρ * (gain c s lam h / ρ) = gain c s lam h := mul_div_cancel₀ _ hρ0.ne'
  have hμ : lam * s ^ 2 ≠ 0 := by positivity
  refine ⟨σ / ρ, gain c s lam h / ρ, ρ, kTraj U₀ (S₀ σ) (V₀ c s) D (lam * s ^ 2),
    lTraj U₀ (S₀ σ) (V₀ c s) D,
    fun t => (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *
      xTraj (V₀ c s) U₀ (S₀ σ) (V₀ c s) D (lam * s ^ 2) t,
    kFree s lam σ (gain c s lam h) (kill c s lam h),
    lFree c s lam σ (kill c s lam h) (σ / ρ) (gain c s lam h / ρ) ρ,
    rowTraj c s lam σ 0 (kill c s lam h) (gain c s lam h * c) (gain c s lam h * s),
    retTraj c s σ (gain c s lam h * c) (-(gain c s lam h * c / h)),
    lRet c s σ (gain c s lam h * c) (-(gain c s lam h * c / h)),
    retTraj c s σ (gain c s lam h * c) (-(gain c s lam h * c / h)),
    state c s σ (gain c s lam h * c) (gain c s lam h * s), state c s σ (gain c s lam h * c) 0,
    isRankAdaptiveStep_active hcs hl hs h, free_start hρa hρb, hρ0.ne',
    isRankAdaptiveStep_free hcs hl.ne' hμ (damp_pos hl hh).ne' hab hρa hρb, ?_, ?_⟩
  · simp [state, Matrix.det_fin_two]
  · rw [start_eq]
    exact isRankAdaptiveStep_return hh.ne'

/-! ### The exact solution -/

/-- The entry `(u, e)` of the exact solution after `j` cycles. -/
noncomputable def exactE (c s lam h : ℝ) (j : ℕ) : ℝ := j * (h - gain c s lam h * c)

/-- The entry `(u, f)` of the exact solution after `j` cycles. -/
noncomputable def exactF (c s lam h : ℝ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => rowEnd lam h 0 (rowEnd lam h (kill c s lam h) (rowEnd lam h 0 (exactF c s lam h j)))

/-- The exact solution after `j` cycles, started at `σ w vᵀ`. -/
noncomputable def exactState (c s lam σ h : ℝ) (j : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  state c s σ (exactE c s lam h j) (exactF c s lam h j)

lemma exactState_zero : exactState c s lam σ h 0 = state c s σ 0 0 := by
  simp [exactState, exactE, exactF]

/-- **The exact solution over one cycle**: three solutions of `X' = X N + G` with the forcings
of the cycle, each starting where the previous one ends, lead from `exactState j` to
`exactState (j + 1)`. -/
theorem exists_exact_cycle (hl : lam ≠ 0) (hh : h ≠ 0) (j : ℕ) :
    ∃ X₀ X₁ X₂ : ℝ → Matrix (Fin 2) (Fin 2) ℝ,
      ODESolution (field (N lam) (cycleForcing c s lam σ h 0)) X₀ 0 h ∧
      X₀ 0 = exactState c s lam σ h j ∧
      ODESolution (field (N lam) (cycleForcing c s lam σ h 1)) X₁ 0 h ∧ X₁ 0 = X₀ h ∧
      ODESolution (field (N lam) (cycleForcing c s lam σ h 2)) X₂ 0 h ∧ X₂ 0 = X₁ h ∧
      X₂ h = exactState c s lam σ h (j + 1) := by
  have e : h * (-(gain c s lam h * c / h)) = -(gain c s lam h * c) := by
    field_simp
  refine ⟨rowTraj c s lam σ 1 0 (exactE c s lam h j) (exactF c s lam h j),
    rowTraj c s lam σ 0 (kill c s lam h) (exactE c s lam h j + h * 1)
      (rowEnd lam h 0 (exactF c s lam h j)),
    rowTraj c s lam σ (-(gain c s lam h * c / h)) 0 (exactE c s lam h j + h * 1 + h * 0)
      (rowEnd lam h (kill c s lam h) (rowEnd lam h 0 (exactF c s lam h j))),
    ?_, rowTraj_zero _ _ _ _ _ _ _ _, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [cycleForcing] using
      odeSolution_rowTraj (c := c) (s := s) (σ := σ) hl 1 0 (exactE c s lam h j)
        (exactF c s lam h j) 0 h
  · simpa [cycleForcing] using
      odeSolution_rowTraj (c := c) (s := s) (σ := σ) hl 0 (kill c s lam h)
        (exactE c s lam h j + h * 1) (rowEnd lam h 0 (exactF c s lam h j)) 0 h
  · rw [rowTraj_zero, rowTraj_end]
  · simpa [cycleForcing] using
      odeSolution_rowTraj (c := c) (s := s) (σ := σ) hl (-(gain c s lam h * c / h)) 0
        (exactE c s lam h j + h * 1 + h * 0)
        (rowEnd lam h (kill c s lam h) (rowEnd lam h 0 (exactF c s lam h j))) 0 h
  · rw [rowTraj_zero, rowTraj_end]
  · rw [rowTraj_end, e]
    simp only [exactState, exactE, exactF]
    congr 1
    push_cast
    ring

/-! ### The error -/

lemma abs_le_norm_state_sub (a b : ℝ) : |a| ≤ ‖state c s σ 0 0 - state c s σ a b‖ := by
  refine abs_le_of_sq_le_sq ?_ (norm_nonneg _)
  rw [Frobenius.norm_sq_eq_sum]
  simp only [state, Fin.sum_univ_two, Matrix.sub_apply, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, sub_self]
  nlinarith [sq_nonneg b, sq_nonneg a]

/-- What the active step produces is at most half of what the exact solution gains, if
`λ s² h ≥ 2`. -/
lemma gain_mul_le (hcs : c ^ 2 + s ^ 2 = 1) (hl : 0 < lam) (hs : s ≠ 0)
    (hx : 2 ≤ lam * s ^ 2 * h) : gain c s lam h * c ≤ h / 2 := by
  have hμ : 0 < lam * s ^ 2 := by positivity
  have hc2 : c ^ 2 ≤ 1 := by nlinarith [sq_nonneg s]
  have h1 : damp (lam * s ^ 2) h ≤ 1 / (lam * s ^ 2) := damp_le_inv hμ h
  have h2 : 1 / (lam * s ^ 2) ≤ h / 2 := by
    rw [div_le_iff₀ hμ]
    linarith
  have h3 : damp (lam * s ^ 2) h * c ^ 2 ≤ 1 / (lam * s ^ 2) * c ^ 2 :=
    mul_le_mul_of_nonneg_right h1 (sq_nonneg c)
  have h4 : 1 / (lam * s ^ 2) * c ^ 2 ≤ 1 / (lam * s ^ 2) := by
    have := mul_le_mul_of_nonneg_left hc2 (one_div_pos.2 hμ).le
    simpa using this
  have h5 : gain c s lam h * c = damp (lam * s ^ 2) h * c ^ 2 := by
    unfold gain
    ring
  linarith

/-- **The global error.** If `λ s² h ≥ 2`, then after `J` cycles (`3 J` steps, time `3 J h`) the
numerical solution, which is back at `σ w vᵀ`, differs from the exact solution by at least
`J h / 2`. -/
theorem half_le_norm_sub_exactState (hcs : c ^ 2 + s ^ 2 = 1) (hl : 0 < lam) (hs : s ≠ 0)
    (hx : 2 ≤ lam * s ^ 2 * h) (J : ℕ) :
    J * h / 2 ≤ ‖state c s σ 0 0 - exactState c s lam σ h J‖ := by
  have h1 := gain_mul_le hcs hl hs hx
  have h2 : (J : ℝ) * h / 2 ≤ exactE c s lam h J := by
    unfold exactE
    have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    nlinarith [mul_nonneg hJ (sub_nonneg.2 h1)]
  exact h2.trans ((le_abs_self _).trans (abs_le_norm_state_sub _ _))

/-! ### The data are bounded and nearly tangent -/

/-- The Frobenius norm of the forcing. -/
theorem norm_sq_forcing (s lam σ p q : ℝ) :
    ‖forcing s lam σ p q‖ ^ 2 = (σ * lam * s) ^ 2 + p ^ 2 + q ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum]
  simp only [forcing, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- The forcing of the return step is bounded by one. -/
theorem abs_gain_mul_div_le (hcs : c ^ 2 + s ^ 2 = 1) (hl : 0 < lam) (hs : s ≠ 0)
    (hh : 0 < h) : |gain c s lam h * c / h| ≤ 1 := by
  have hμ : 0 < lam * s ^ 2 := by positivity
  have hc2 : c ^ 2 ≤ 1 := by nlinarith [sq_nonneg s]
  have h0 : 0 ≤ damp (lam * s ^ 2) h := (damp_pos hμ hh).le
  have h1 : damp (lam * s ^ 2) h ≤ h := damp_le_self hμ h
  have h5 : gain c s lam h * c = damp (lam * s ^ 2) h * c ^ 2 := by
    unfold gain
    ring
  rw [h5, abs_div, abs_of_pos hh, div_le_one hh, abs_of_nonneg (mul_nonneg h0 (sq_nonneg c))]
  nlinarith [mul_nonneg h0 (sub_nonneg.2 hc2)]

/-- The forcing of the free step in the entry `(u, f)` is bounded by `|s|`. -/
theorem abs_kill_le (hcs : c ^ 2 + s ^ 2 = 1) (hl : 0 < lam) (hs : s ≠ 0) (hh : 0 < h) :
    |kill c s lam h| ≤ |s| := by
  have hμ : 0 < lam * s ^ 2 := by positivity
  have hd : 0 < damp lam h := damp_pos hl hh
  have hE : Real.exp (-(lam * h)) * (1 + lam * h) ≤ 1 := by
    have h1 := Real.add_one_le_exp (lam * h)
    have h2 : Real.exp (-(lam * h)) * Real.exp (lam * h) = 1 := by
      rw [← Real.exp_add]
      simp
    have h3 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-(lam * h))).le
    linarith
  have hEd : h * Real.exp (-(lam * h)) ≤ damp lam h := by
    have := one_sub_mul_damp hl.ne' h
    have h4 : lam * (h * Real.exp (-(lam * h))) ≤ lam * damp lam h := by nlinarith
    exact le_of_mul_le_mul_left h4 hl
  have hg : |gain c s lam h| ≤ h := by
    unfold gain
    have hc1 : |c| ≤ 1 := by
      refine abs_le_of_sq_le_sq ?_ zero_le_one
      nlinarith [sq_nonneg s]
    have h0 : 0 ≤ damp (lam * s ^ 2) h := (damp_pos hμ hh).le
    rw [abs_mul, abs_of_nonneg h0]
    calc damp (lam * s ^ 2) h * |c| ≤ damp (lam * s ^ 2) h * 1 :=
          mul_le_mul_of_nonneg_left hc1 h0
      _ ≤ h := by
          rw [mul_one]
          exact damp_le_self hμ h
  have hk : kill c s lam h * damp lam h
      = -(gain c s lam h * s * Real.exp (-(lam * h))) := by
    rw [← one_sub_mul_damp hl.ne' h]
    unfold kill
    field_simp
    ring
  have h6 : |kill c s lam h| * damp lam h ≤ |s| * damp lam h := by
    rw [← abs_of_pos hd, ← abs_mul, hk, abs_neg, abs_mul, abs_mul,
      abs_of_pos (Real.exp_pos _), abs_of_pos hd]
    calc |gain c s lam h| * |s| * Real.exp (-(lam * h))
        ≤ h * |s| * Real.exp (-(lam * h)) := by gcongr
      _ = |s| * (h * Real.exp (-(lam * h))) := by ring
      _ ≤ |s| * damp lam h := mul_le_mul_of_nonneg_left hEd (abs_nonneg s)
  exact le_of_mul_le_mul_right h6 hd

lemma normal_forcing_active :
    forcing s lam σ 1 0 - rightProj (V₀ c s) (forcing s lam σ 1 0)
        - leftProj U₀ (forcing s lam σ 1 0 - rightProj (V₀ c s) (forcing s lam σ 1 0))
      = !![0, 0; 1 - c * c, -(c * s)] := by
  rw [rightProj_apply, leftProj_apply]
  entries

/-- **The normal component of the forcing at the start of the active step is `|s|`.** The
stiff part `Y N` of the field is tangent at `Y`, so this is the normal component of the field. -/
theorem norm_normal_forcing_active (hcs : c ^ 2 + s ^ 2 = 1) :
    ‖forcing s lam σ 1 0 - rightProj (V₀ c s) (forcing s lam σ 1 0)
        - leftProj U₀ (forcing s lam σ 1 0 - rightProj (V₀ c s) (forcing s lam σ 1 0))‖
      = |s| := by
  rw [normal_forcing_active]
  have h2 : ‖(!![0, 0; 1 - c * c, -(c * s)] : Matrix (Fin 2) (Fin 2) ℝ)‖ ^ 2 = s ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum]
    simp only [Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination (c ^ 2 - 1) * hcs
  have h3 := (sq_eq_sq_iff_abs_eq_abs _ _).1 h2
  rwa [abs_norm] at h3

/-! ### No uniform global bound -/

/-- **No stiffness-uniform global bound for forcing that may vary on the scale of the step.**
There is no constant `K` such that, for all admissible parameters of the family, all step sizes
`h`, and all numbers `J` of cycles with final time `3 J h ≤ 1`, the error of the rank-adaptive
BUG integrator after `3 J` steps is at most `K (h (1 + |log h|) + s)`.

Here the forcing of step `k` is `cycleForcing c s λ σ h (k mod 3)`: piecewise constant in time
with jumps at the grid points, so it depends on `h`. The numerical solution after `3 J` steps is
`state c s σ 0 0` (`exists_cycle`), the exact solution is `exactState c s λ σ h J`
(`exists_exact_cycle`). The forcing does not depend on the solution, is bounded
(`norm_sq_forcing`, `abs_gain_mul_div_le`, `abs_kill_le`), its normal component at the start of
the active step is `|s|` (`norm_normal_forcing_active`), the truncation tolerance is zero and
`N` is symmetric negative semidefinite. Only `‖N‖ = λ` is unbounded over the family; in the
proof `s = h`, `λ = 2 / h³`, `3 J h = 1` and the error is at least `1 / 6`.

The statement does not exclude a bound of this form for forcing whose regularity in time is
bounded independently of `h`. -/
theorem not_exists_uniform_global_bound :
    ¬ ∃ K : ℝ, ∀ (c s lam σ h : ℝ) (J : ℕ), c ^ 2 + s ^ 2 = 1 → 0 < lam → 0 < s → 0 < h →
      2 ≤ lam * s ^ 2 * h → 3 * (J : ℝ) * h ≤ 1 →
      ‖state c s σ 0 0 - exactState c s lam σ h J‖ ≤ K * (h * (1 + |Real.log h|) + s) := by
  rintro ⟨K, hK⟩
  obtain ⟨m, hm⟩ := exists_nat_gt (12 * |K| + 1)
  have hK0 : 0 ≤ |K| := abs_nonneg K
  have hx1 : (1 : ℝ) < m := by linarith
  have hx0 : (0 : ℝ) < m := by linarith
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = (3 * (m : ℝ) ^ 2)⁻¹ := ⟨_, rfl⟩
  have h3m : (0 : ℝ) < 3 * (m : ℝ) ^ 2 := by positivity
  have h0 : 0 < h := by
    rw [hh]
    exact inv_pos.2 h3m
  have hmh : 3 * (m : ℝ) ^ 2 * h = 1 := by
    rw [hh]
    exact mul_inv_cancel₀ h3m.ne'
  have hh1 : h ≤ 1 / 3 := by nlinarith
  have hsq : 0 ≤ 1 - h ^ 2 := by nlinarith
  have hcs : Real.sqrt (1 - h ^ 2) ^ 2 + h ^ 2 = 1 := by
    rw [Real.sq_sqrt hsq]
    ring
  have hl : 0 < 2 / h ^ 3 := by positivity
  have hx : 2 ≤ 2 / h ^ 3 * h ^ 2 * h := by
    have : 2 / h ^ 3 * h ^ 2 * h = 2 := by
      field_simp
    rw [this]
  have hJ : 3 * ((m ^ 2 : ℕ) : ℝ) * h ≤ 1 := by
    push_cast
    exact hmh.le
  have hlow := half_le_norm_sub_exactState (σ := 1) hcs hl h0.ne' hx (m ^ 2)
  have hup := hK _ h (2 / h ^ 3) 1 h (m ^ 2) hcs hl h0 h0 hx hJ
  have hlow' : (1 : ℝ) / 6 ≤ ((m ^ 2 : ℕ) : ℝ) * h / 2 := by
    push_cast
    linarith
  -- the logarithm
  have hlog : |Real.log h| ≤ 2 * m := by
    have e1 : Real.log h = -Real.log (3 * (m : ℝ) ^ 2) := by
      rw [hh, Real.log_inv]
    have e2 : Real.log (3 * (m : ℝ) ^ 2) = Real.log 3 + 2 * Real.log m := by
      rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hx0.ne'), Real.log_pow]
      push_cast
      ring
    have e3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
    have e4 : Real.log m ≤ m - 1 := Real.log_le_sub_one_of_pos hx0
    have e5 : 0 ≤ Real.log m := Real.log_nonneg hx1.le
    have e6 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    rw [e1, abs_neg, e2, abs_of_nonneg (by linarith)]
    linarith
  have hb : h * (1 + |Real.log h|) + h ≤ 4 * (m * h) := by
    have : h * |Real.log h| ≤ h * (2 * m) := mul_le_mul_of_nonneg_left hlog h0.le
    nlinarith
  have hb0 : 0 ≤ h * (1 + |Real.log h|) + h := by
    have := abs_nonneg (Real.log h)
    positivity
  have h7 : (1 : ℝ) / 6 ≤ |K| * (4 * (m * h)) :=
    calc (1 : ℝ) / 6 ≤ _ := hlow'
      _ ≤ _ := hlow
      _ ≤ _ := hup
      _ ≤ |K| * (h * (1 + |Real.log h|) + h) := mul_le_mul_of_nonneg_right (le_abs_self K) hb0
      _ ≤ |K| * (4 * (m * h)) := mul_le_mul_of_nonneg_left hb hK0
  have h8 : (m : ℝ) * h * (3 * m) = 1 := by
    rw [← hmh]
    ring
  have h9 : (1 : ℝ) / 6 * (3 * m) ≤ |K| * (4 * (m * h)) * (3 * m) :=
    mul_le_mul_of_nonneg_right h7 (by positivity)
  have h10 : |K| * (4 * (m * h)) * (3 * m) = 4 * |K| := by
    calc |K| * (4 * (m * h)) * (3 * m) = 4 * |K| * (m * h * (3 * m)) := by ring
      _ = 4 * |K| := by rw [h8, mul_one]
  linarith

/-- The hypotheses of `half_le_norm_sub_exactState` and the conditions on the parameters in
`not_exists_uniform_global_bound` can hold: `c = 3/5`, `s = 4/5`, `λ = 25`, `h = 1/8`, one
cycle; the error is at least `1/16`. -/
example :
    (1 : ℝ) / 16 ≤ ‖state (3 / 5) (4 / 5) 1 0 0 - exactState (3 / 5) (4 / 5) 25 1 (1 / 8) 1‖ := by
  have key := half_le_norm_sub_exactState (c := 3 / 5) (s := 4 / 5) (lam := 25) (σ := 1)
    (h := 1 / 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1
  norm_num at key
  linarith

end StiffGlobalCycle

end LeanDLRA
