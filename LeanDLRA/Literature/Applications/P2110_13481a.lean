import Mathlib

/-!
# Results of arXiv 2110.13481: Ensign, efficient 6D Vlasov DLRA

Cassini, Einkemmer, *Efficient 6D Vlasov simulation using the dynamical low-rank framework Ensign*.
The paper states no theorems. This module formalizes the one exact claim of Section 4 about the
K-substep: after a Fourier transform in `x` and a diagonalization of the symmetric velocity
coefficient `C_{1,v} = Ṽᵀ diag(ω) Ṽ`, the one-direction K-equations (14)–(15), in the Fourier
form (17)–(18), are solved exactly by pointwise operations, so no CFL restriction arises.

Results:

* `coeff_isSymm`: `C_{1,v} = Ṽᵀ diag(ω) Ṽ` is symmetric (the paper: "symmetric by construction").
* `exists_orthogonal_diagonalisation`: a real symmetric `A` satisfies `T A Tᵀ = diag D` with `T`
  orthogonal (the diagonalization used in Sec. 4; proved from Mathlib's spectral theorem, the same
  statement as `LeanDLRA.Literature.P1801_01103.exists_orthogonal_diagonalisation`, not imported).
* `fourierFlow`: the explicit solution `M(t)_{jm} = exp(-t a_j d_m) M₀_{jm}` of
  `∂ₜ M = -diag(a) M diag(d)`.
* `fourier_kstep_exact`: for every complex Fourier symbol `a` (the paper's diagonal `D_x^F`, here an
  arbitrary complex vector, which includes the paper's purely imaginary symbol) and every initial
  value `K̂₀`, there is `K̂ : ℝ → Matrix` with `K̂ 0 = K̂₀` and `∂ₜ K̂(t) = -diag(a) K̂(t) C_{1,v}`
  entrywise for every `t ∈ ℝ`. The solution is `K̂(t) = F(t) T` with
  `F(t) = fourierFlow a d (K̂₀ Tᵀ) t` and `C_{1,v} = Tᵀ diag(d) T`, so it exists for all times
  and the step size is unrestricted.

The paper's `C_{1,v}` is `Ṽᵀ diag(ω) Ṽ` with real factors `Ṽ` and real quadrature weights `ω`; the
statement is over `ℝ` for these and over `ℂ` for `K̂`. The paper's equation (14)–(15) is the
one-direction form; the `ℂ`-valued ODE is stated entrywise because matrices of `ℂ` carry no norm.

Not formalized, and why: the full `d = 3` equation (16) and its electric-field term; the
exponential Runge–Kutta treatment of (19); the Lie and Strang splittings of Algorithms 1 and 2
(the paper gives no error or convergence bound for them); the claim that the scheme is CFL-free
in practice, which is numerical; and the complexity statements `O(r nᵈ)`, `O(r² nᵈ)`.

Core definitions used: none. The file works with `Matrix` and `HasDerivAt` directly.
-/

open Matrix

namespace LeanDLRA.Literature.P2110_13481

variable {m r n : ℕ}

/-- **Sec. 3 (below (9)–(11)), arXiv 2110.13481.** The velocity coefficient
`C_{1,v} = Ṽᵀ diag(ω) Ṽ` is symmetric for real factors `Ṽ` and real quadrature weights `ω`;
the paper states that the `C_{1,v_i}` are symmetric by construction. -/
theorem coeff_isSymm (V : Matrix (Fin m) (Fin r) ℝ) (ω : Fin m → ℝ) :
    (Vᵀ * diagonal ω * V).IsSymm := by
  unfold Matrix.IsSymm
  simp [transpose_mul, diagonal_transpose, Matrix.mul_assoc]

/-- **Sec. 4, diagonalization of the symmetric `C_{1,v}`.** A real symmetric matrix has an
orthogonal `T` with `T A Tᵀ = diag D` (Mathlib's spectral theorem). -/
theorem exists_orthogonal_diagonalisation {A : Matrix (Fin r) (Fin r) ℝ} (hA : A.IsSymm) :
    ∃ (T : Matrix (Fin r) (Fin r) ℝ) (D : Fin r → ℝ), Tᵀ * T = 1 ∧ T * A * Tᵀ = diagonal D := by
  have hH : A.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact hA
  set U : Matrix (Fin r) (Fin r) ℝ := (hH.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℝ) with hU
  have hU1 : Uᵀ * U = 1 := by
    have := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hU2 : U * Uᵀ = 1 := mul_eq_one_comm.mp hU1
  have hs := hH.spectral_theorem
  have hA' : A = U * diagonal hH.eigenvalues * Uᵀ := by
    simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hs
  refine ⟨Uᵀ, hH.eigenvalues, by rw [Matrix.transpose_transpose]; exact hU2, ?_⟩
  rw [Matrix.transpose_transpose]
  calc Uᵀ * A * U = Uᵀ * (U * diagonal hH.eigenvalues * Uᵀ) * U :=
        congrArg (fun B => Uᵀ * B * U) hA'
    _ = (Uᵀ * U) * diagonal hH.eigenvalues * (Uᵀ * U) := by
        simp only [Matrix.mul_assoc]
    _ = diagonal hH.eigenvalues := by rw [hU1, Matrix.one_mul, Matrix.mul_one]

/-- The fundamental solution of the diagonal Fourier-space K-flow `∂ₜ M = -diag(a) M diag(d)`:
its entry `(j, m)` is `exp(-t a_j d_m) M₀ j m`. -/
noncomputable def fourierFlow (a : Fin n → ℂ) (d : Fin r → ℝ) (M₀ : Matrix (Fin n) (Fin r) ℂ)
    (t : ℝ) : Matrix (Fin n) (Fin r) ℂ :=
  Matrix.of fun j m => Complex.exp (-(t : ℂ) * a j * (d m : ℂ)) * M₀ j m

lemma hasDerivAt_fourierFlow (a : Fin n → ℂ) (d : Fin r → ℝ) (M₀ : Matrix (Fin n) (Fin r) ℂ)
    (t : ℝ) (j : Fin n) (m : Fin r) :
    HasDerivAt (fun s => fourierFlow a d M₀ s j m)
      (-(a j * (d m : ℂ)) * fourierFlow a d M₀ t j m) t := by
  have h1 : HasDerivAt (fun s : ℝ => -(s : ℂ) * a j * (d m : ℂ)) (-1 * a j * (d m : ℂ)) t :=
    (((hasDerivAt_id' t).ofReal_comp).neg.mul_const (a j)).mul_const (d m : ℂ)
  have h2 := (h1.cexp).mul_const (M₀ j m)
  unfold fourierFlow
  simp only [Matrix.of_apply]
  convert h2 using 1
  ring

/-- **Sec. 4, Eqs. (14)–(15), (17)–(18), arXiv 2110.13481: exact Fourier K-substep.**
Let `C = Ṽᵀ diag(ω) Ṽ` be the real symmetric velocity coefficient (`coeff_isSymm`) and let
`a : Fin n → ℂ` be any Fourier symbol. For every initial value `K̂₀` there is a function
`K̂ : ℝ → Matrix` with `K̂(0) = K̂₀` solving `∂ₜ K̂(t) = -diag(a) K̂(t) C` (entrywise, for every
`t ∈ ℝ`). The solution is explicit and exists for all times, so the step size is unrestricted.
The paper's `K̂ᵢ` equation has `C^T` on the right; `C` is symmetric, so this is the same. -/
theorem fourier_kstep_exact (V : Matrix (Fin m) (Fin r) ℝ) (ω : Fin m → ℝ) (a : Fin n → ℂ)
    (K₀ : Matrix (Fin n) (Fin r) ℂ) :
    ∃ K : ℝ → Matrix (Fin n) (Fin r) ℂ, K 0 = K₀ ∧
      ∀ t : ℝ, ∀ j l,
        HasDerivAt (fun s => K s j l)
          (-((diagonal a * K t * (Vᵀ * diagonal ω * V).map (fun x : ℝ => (x : ℂ))) j l)) t := by
  classical
  -- Spectral decomposition `C = Tᵀ diag(D) T` with `T` real orthogonal (Sec. 4, diagonalization).
  obtain ⟨T, D, hTT, hTCT⟩ := exists_orthogonal_diagonalisation (coeff_isSymm V ω)
  have hTT' : T * Tᵀ = 1 := mul_eq_one_comm.mp hTT
  have hCeq : Vᵀ * diagonal ω * V = Tᵀ * diagonal D * T := by
    calc Vᵀ * diagonal ω * V = (Tᵀ * T) * (Vᵀ * diagonal ω * V) * (Tᵀ * T) := by
          rw [hTT, one_mul, mul_one]
      _ = Tᵀ * (T * (Vᵀ * diagonal ω * V) * Tᵀ) * T := by simp only [Matrix.mul_assoc]
      _ = Tᵀ * diagonal D * T := by rw [hTCT]
  -- Complex copies of the real orthogonal factor and of the coefficient.
  have hcast : ∀ M N : Matrix (Fin r) (Fin r) ℝ,
      (M * N).map (fun x : ℝ => (x : ℂ)) =
        M.map (fun x : ℝ => (x : ℂ)) * N.map (fun x : ℝ => (x : ℂ)) := by
    intro M N; ext i j; simp [Matrix.mul_apply]
  have hTcTc : (T.map (fun x : ℝ => (x : ℂ)))ᵀ * T.map (fun x : ℝ => (x : ℂ)) = 1 := by
    have h := congrArg (fun M : Matrix (Fin r) (Fin r) ℝ => M.map (fun x : ℝ => (x : ℂ))) hTT
    simpa [hcast, Matrix.transpose_map] using h
  have hTcTc' : T.map (fun x : ℝ => (x : ℂ)) * (T.map (fun x : ℝ => (x : ℂ)))ᵀ = 1 := by
    have h := congrArg (fun M : Matrix (Fin r) (Fin r) ℝ => M.map (fun x : ℝ => (x : ℂ))) hTT'
    simpa [hcast, Matrix.transpose_map] using h
  have hCc : (Vᵀ * diagonal ω * V).map (fun x : ℝ => (x : ℂ)) =
      (T.map (fun x : ℝ => (x : ℂ)))ᵀ * diagonal (fun l => (D l : ℂ)) *
        T.map (fun x : ℝ => (x : ℂ)) := by
    rw [hCeq]
    ext i j
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply, Finset.sum_ite_eq']
  -- The solution: `K̂(t) = F(t) T` with `F(t)_{jm} = exp(-t a_j D_m) (K̂₀ T̃ᵀ)_{jm}`.
  refine ⟨fun s => fourierFlow a D (K₀ * (T.map (fun x : ℝ => (x : ℂ)))ᵀ) s *
    T.map (fun x : ℝ => (x : ℂ)), ?_, ?_⟩
  · have h0 : fourierFlow a D (K₀ * (T.map (fun x : ℝ => (x : ℂ)))ᵀ) 0 =
        K₀ * (T.map (fun x : ℝ => (x : ℂ)))ᵀ := by
      ext j m; simp [fourierFlow]
    simp only [h0]
    rw [Matrix.mul_assoc, hTcTc, Matrix.mul_one]
  · intro t j l
    set Tc : Matrix (Fin r) (Fin r) ℂ := T.map (fun x : ℝ => (x : ℂ)) with hTc
    have hkey : fourierFlow a D (K₀ * Tcᵀ) t * Tc * (Tcᵀ * diagonal (fun l => (D l : ℂ)) * Tc) =
        fourierFlow a D (K₀ * Tcᵀ) t * diagonal (fun l => (D l : ℂ)) * Tc := by
      calc fourierFlow a D (K₀ * Tcᵀ) t * Tc * (Tcᵀ * diagonal (fun l => (D l : ℂ)) * Tc)
          = fourierFlow a D (K₀ * Tcᵀ) t * (Tc * Tcᵀ) * diagonal (fun l => (D l : ℂ)) * Tc := by
            simp only [Matrix.mul_assoc]
        _ = fourierFlow a D (K₀ * Tcᵀ) t * diagonal (fun l => (D l : ℂ)) * Tc := by
            rw [hTcTc']; simp
    have hsum : HasDerivAt (fun s => ∑ m, fourierFlow a D (K₀ * Tcᵀ) s j m * Tc m l)
        (∑ m, -(a j * (D m : ℂ)) * fourierFlow a D (K₀ * Tcᵀ) t j m * Tc m l) t := by
      apply HasDerivAt.fun_sum
      intro m _
      exact (hasDerivAt_fourierFlow a D (K₀ * Tcᵀ) t j m).mul_const (Tc m l)
    convert hsum using 1
    · funext s
      simp [Matrix.mul_apply]
    · rw [hCc, Matrix.mul_assoc, hkey, Matrix.diagonal_mul, Matrix.mul_apply, Finset.mul_sum,
        ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [Matrix.mul_diagonal]
      ring

end LeanDLRA.Literature.P2110_13481
