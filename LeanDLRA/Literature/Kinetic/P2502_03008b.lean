import LeanDLRA.Integrators.BUG
import LeanDLRA.LinearAlgebra.Factorization.Defs
import LeanDLRA.Matrix.Projectors
import LeanDLRA.OpenProblems.Curated.Classicala

/-!
# Local mass conservation of the multiplicative DLRA scheme for Su–Olson (arXiv 2502.03008)

Baumann, Einkemmer, Klingenberg, Kusch, *An energy stable and conservative multiplicative dynamical
low-rank discretization for the Su-Olson problem*, version 2.  This module writes out the whole
fully discrete low-rank scheme, namely the K-, L- and S-steps (19a), (19c), (19e), the basis
augmentations (19b), (19d), the coupled update (19f), (19g) of the zeroth moment and the energy,
the transformation (19h), the augmentation (19i), the adjustment (19j) and the conservative
truncation of Section 5.4 (`IsConsTruncation`), as one predicate `IsSuOlsonDLRAStep`.  It proves
Theorem 4 (`theorem_4`: the discrete local conservation law for `ρ_j = √2 B_j Φ_j + B_j`), the
total mass conservation that follows for the periodic stencils (`total_mass_conservation`), and
that the scheme is well posed (`exists_isSuOlsonDLRAStep`: all QR, SVD and implicit solves exist for
all data with `4 r + 1 ≤ Nx, Nμ` as long as the new energy stays positive, and any target rank
`r₁ ≤ 4 r` can be chosen), so that the theorem is not vacuous.

## Differences from the paper

* `D^x`, `D^xx`, `A`, `|A|`, `σ ≥ 0` are arbitrary in `theorem_4`: the local law uses no property of
  them.  In particular `A` need not be the Legendre matrix `∫ μ P_k P_ℓ`.  The periodic stencils of
  the paper are `stencilCentred`, `stencilStab`, and only the total mass needs them (their columns
  sum to zero).  `X₀`, `V₀` need not be orthonormal.  `B₀ > 0` is assumed: the paper divides by
  `B₀` without saying so.
* `qr` is taken with nonnegative diagonal of `R` (`IsGSQR`), and this convention is needed.  Step 5
  of Section 5.4 writes `e₁` instead of the first column of `V̂̂¹`, and that column is `+e₁` only
  with this convention (`IsGSQR.first_column`).  With `R₀₀ = -1` the truncated zeroth moment would
  be `-v¹₀`.  All QR factors may come from rank-deficient matrices, and the scheme then needs
  `4 r + 1 ≤ Nx, Nμ` for the columns to fit.
* The paper uses `K*` both for the result of (19a) and in (19h).  In (19h) we read it as
  `K* = X̂̂* Ŝ̂*`, the only reading for which the sizes in (19i), (19j) match.
* (19c) is printed with `D^x_{ij}` and `D^xx_{ij}`, while the paper's own L-step
  `L̇ = F(X₀ Lᵀ)ᵀ X₀` gives `D^x_{ji}`, which has the opposite sign for the skew `D^x`.  `massLStep`
  uses `D_{ji}`.  The law does not depend on this: `IsSuOlsonDLRACore.local_mass_conservation`
  holds for arbitrary `K*`, `L*`, `Ŝ̂*`, so it covers the printed version as well.
* After truncation the factors have `r₁ + 1` columns: the `r₁` kept singular values and the
  conserved column.  The paper writes `r₁` for the range of the sums in `Φ¹`.
* If the first column of `K̂̂¹` vanishes, step 2 of Section 5.4 divides by zero.  Lean's `x / 0 = 0`
  gives the sensible result, and the theorem covers this case.
* The widths are `r + r` and `r + r + r + r` for the paper's `2 r` and `4 r`.
* Not here: Theorems 1, 2, 3 of the paper (see the companion file `P2502_03008a`).  The conservation
  is one-step; iterating it over many steps only adds bookkeeping for the changing rank.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2502_03008

/-! ### QR factorizations and concatenation of columns -/

section QR

variable {κ : Type*} [Fintype κ] {n a b : ℕ}

/-- The operation `qr` of arXiv 2502.03008, (19b), (19d), (19i): a thin QR factorization `M = Q R`
with `Qᵀ Q = 1` and `R` upper triangular with nonnegative diagonal, as produced by Gram–Schmidt.
Rank-deficient `M` are allowed, and then `Q` is not determined by `M`. It is the core QR
factorization `Matrix.IsQR M Q R` (`IsGSQR.toIsQR`) with the Gram–Schmidt sign convention
`R c c ≥ 0`, which Step 5 of Theorem 4 needs (unification batch C4). -/
structure IsGSQR (M Q : Matrix κ (Fin n) ℝ) (R : Matrix (Fin n) (Fin n) ℝ) : Prop
    extends Matrix.IsQR M Q R where
  /-- The Gram–Schmidt sign convention: the diagonal of `R` is nonnegative. -/
  diag_nonneg : ∀ c, 0 ≤ R c c

/-- The matrix `[P₁, P₂]` whose columns are those of `P₁` followed by those of `P₂`. -/
def colAppend (P₁ : Matrix κ (Fin a) ℝ) (P₂ : Matrix κ (Fin b) ℝ) : Matrix κ (Fin (a + b)) ℝ :=
  fun j => Fin.append (P₁ j) (P₂ j)

/-- The matrix `[c, P]` with first column `c`, followed by the columns of `P`. -/
def colCons (c : κ → ℝ) (P : Matrix κ (Fin n) ℝ) : Matrix κ (Fin (n + 1)) ℝ :=
  fun j => Fin.cons (c j) (P j)

/-- arXiv 2502.03008, proof of Theorem 4: the columns of `M` lie in the range of its QR factor
`Q`, that is `Q Qᵀ M = M`. -/
theorem IsGSQR.capture {M Q : Matrix κ (Fin n) ℝ} {R : Matrix (Fin n) (Fin n) ℝ}
    (h : IsGSQR M Q R) : Q * Qᵀ * M = M := by
  rw [h.eq, Matrix.mul_assoc, ← Matrix.mul_assoc Qᵀ, h.orth, Matrix.one_mul]

/-- arXiv 2502.03008, proof of Theorem 4: a matrix fixing `[P₁, P₂]` fixes `P₁`. -/
theorem capture_colAppend_left {T : Matrix κ κ ℝ} {P₁ : Matrix κ (Fin a) ℝ}
    {P₂ : Matrix κ (Fin b) ℝ} (h : T * colAppend P₁ P₂ = colAppend P₁ P₂) : T * P₁ = P₁ := by
  ext j c
  have := congrFun (congrFun h j) (Fin.castAdd b c)
  simpa [Matrix.mul_apply, colAppend] using this

/-- arXiv 2502.03008, proof of Theorem 4: a matrix fixing `[P₁, P₂]` fixes `P₂`. -/
theorem capture_colAppend_right {T : Matrix κ κ ℝ} {P₁ : Matrix κ (Fin a) ℝ}
    {P₂ : Matrix κ (Fin b) ℝ} (h : T * colAppend P₁ P₂ = colAppend P₁ P₂) : T * P₂ = P₂ := by
  ext j c
  have := congrFun (congrFun h j) (Fin.natAdd a c)
  simpa [Matrix.mul_apply, colAppend] using this

/-- arXiv 2502.03008, proof of Theorem 4: a matrix fixing `[c, P]` fixes `c`. -/
theorem capture_colCons {T : Matrix κ κ ℝ} {c : κ → ℝ} {P : Matrix κ (Fin n) ℝ}
    (h : T * colCons c P = colCons c P) (j : κ) : ∑ i, T j i * c i = c j := by
  have := congrFun (congrFun h j) 0
  simpa [Matrix.mul_apply, colCons] using this

/-- arXiv 2502.03008, (19i): the QR factor of `[e₁, W]` has first column `e₁`, and hence its other
columns have a vanishing entry `0`.  The nonnegative diagonal of `R` is used here: it excludes the
first column `-e₁`. -/
theorem IsGSQR.first_column {Nμ : ℕ} [NeZero Nμ] {W : Matrix (Fin Nμ) (Fin n) ℝ}
    {Q : Matrix (Fin Nμ) (Fin (n + 1)) ℝ} {R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (h : IsGSQR (colCons (Pi.single 0 1) W) Q R) :
    (∀ k, Q k 0 = (Pi.single 0 1 : Fin Nμ → ℝ) k) ∧ ∀ c : Fin n, Q 0 c.succ = 0 := by
  have hcol : ∀ k, (Pi.single 0 1 : Fin Nμ → ℝ) k = Q k 0 * R 0 0 := by
    intro k
    have h1 := congrFun (congrFun h.eq k) 0
    have hR : ∀ c : Fin (n + 1), c ≠ 0 → R c 0 = 0 := fun c hc =>
      h.upper (by simpa [Fin.pos_iff_ne_zero] using hc)
    rw [Matrix.mul_apply, Finset.sum_eq_single 0 (fun c _ hc => by rw [hR c hc, mul_zero])
      (by simp)] at h1
    simpa [colCons] using h1
  have hnorm : ∑ k, Q k 0 * Q k 0 = 1 := by
    have := congrFun (congrFun h.orth 0) 0
    simpa [Matrix.mul_apply] using this
  have hρ : R 0 0 = 1 := by
    have h1 : ∑ k, (Pi.single 0 1 : Fin Nμ → ℝ) k * (Pi.single 0 1 : Fin Nμ → ℝ) k = 1 := by
      rw [Finset.sum_eq_single 0 (fun k _ hk => by simp [hk]) (by simp)]; simp
    have hsq : (R 0 0) ^ 2 = 1 := by
      calc (R 0 0) ^ 2 = (R 0 0) ^ 2 * ∑ k, Q k 0 * Q k 0 := by rw [hnorm, mul_one]
        _ = ∑ k, (Q k 0 * R 0 0) * (Q k 0 * R 0 0) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        _ = 1 := by simp_rw [← hcol]; exact h1
    nlinarith [h.diag_nonneg 0]
  have hfirst : ∀ k, Q k 0 = (Pi.single 0 1 : Fin Nμ → ℝ) k := fun k => by
    rw [hcol k, hρ, mul_one]
  refine ⟨hfirst, fun c => ?_⟩
  have h0 := congrFun (congrFun h.orth 0) c.succ
  have hne : (0 : Fin (n + 1)) ≠ c.succ := (Fin.succ_ne_zero c).symm
  simp only [Matrix.mul_apply, Matrix.transpose_apply, hfirst, Matrix.one_apply_ne hne] at h0
  rw [Finset.sum_eq_single 0 (fun k _ hk => by simp [hk]) (by simp)] at h0
  simpa using h0

/-- Auxiliary for `exists_isGSQR`: a matrix with fewer columns than rows has a unit vector
orthogonal to all columns (used by arXiv 2502.03008 implicitly, for rank-deficient `qr`). -/
theorem exists_unit_orthogonal (Q : Matrix κ (Fin n) ℝ) (hn : n < Fintype.card κ) :
    ∃ x : κ → ℝ, Qᵀ *ᵥ x = 0 ∧ x ⬝ᵥ x = 1 := by
  classical
  have hker : LinearMap.ker Qᵀ.mulVecLin ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hn)
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hker
  have hQx : Qᵀ *ᵥ x = 0 := LinearMap.mem_ker.mp hx
  have hpos : 0 < x ⬝ᵥ x := by
    have : x ⬝ᵥ x ≠ 0 := by simpa using hx0
    exact lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg _) this.symm
  refine ⟨(√(x ⬝ᵥ x))⁻¹ • x, ?_, ?_⟩
  · rw [Matrix.mulVec_smul, hQx, smul_zero]
  · rw [dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    have hs : √(x ⬝ᵥ x) * √(x ⬝ᵥ x) = x ⬝ᵥ x := Real.mul_self_sqrt hpos.le
    have hs0 : √(x ⬝ᵥ x) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    field_simp
    nlinarith

/-- **The operation `qr` of arXiv 2502.03008 is well defined**: every `M` with at most as many
columns as rows, also rank-deficient, has a thin QR factorization with nonnegative diagonal
(Gram–Schmidt, completing with an arbitrary orthogonal unit vector at a dependent column). -/
theorem exists_isGSQR : ∀ {n : ℕ} (M : Matrix κ (Fin n) ℝ), n ≤ Fintype.card κ →
    ∃ (Q : Matrix κ (Fin n) ℝ) (R : Matrix (Fin n) (Fin n) ℝ), IsGSQR M Q R := by
  intro n
  induction n with
  | zero =>
    intro M _
    refine ⟨M, 1, ⟨⟨by simp, ?_, fun a => a.elim0⟩, fun a => a.elim0⟩⟩
    ext a
    exact a.elim0
  | succ n ih =>
    intro M hn
    obtain ⟨Q', R', h'⟩ := ih (fun j c => M j c.castSucc) (by omega)
    set c : κ → ℝ := fun j => M j (Fin.last n) with hc
    set α : Fin n → ℝ := Q'ᵀ *ᵥ c with hα
    set p : κ → ℝ := c - Q' *ᵥ α with hp
    have hp0 : Q'ᵀ *ᵥ p = 0 := by
      rw [hp, Matrix.mulVec_sub, Matrix.mulVec_mulVec, h'.orth, Matrix.one_mulVec, ← hα, sub_self]
    obtain ⟨q, ν, hν, hq0, hqq, hpq⟩ : ∃ (q : κ → ℝ) (ν : ℝ), 0 ≤ ν ∧ Q'ᵀ *ᵥ q = 0 ∧
        q ⬝ᵥ q = 1 ∧ p = ν • q := by
      by_cases hz : p = 0
      · obtain ⟨x, hx, hxx⟩ := exists_unit_orthogonal Q' (by omega)
        exact ⟨x, 0, le_rfl, hx, hxx, by simp [hz]⟩
      · have hpos : 0 < p ⬝ᵥ p := by
          have : p ⬝ᵥ p ≠ 0 := by simpa using hz
          exact lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg _) this.symm
        have hs : √(p ⬝ᵥ p) * √(p ⬝ᵥ p) = p ⬝ᵥ p := Real.mul_self_sqrt hpos.le
        have hs0 : √(p ⬝ᵥ p) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
        refine ⟨(√(p ⬝ᵥ p))⁻¹ • p, √(p ⬝ᵥ p), Real.sqrt_nonneg _, ?_, ?_, ?_⟩
        · rw [Matrix.mulVec_smul, hp0, smul_zero]
        · rw [dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
          field_simp
          nlinarith
        · rw [smul_smul, mul_inv_cancel₀ hs0, one_smul]
    let Q : Matrix κ (Fin (n + 1)) ℝ := fun j => Fin.snoc (α := fun _ => ℝ) (Q' j) (q j)
    let R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Fin.snoc (α := fun _ => Fin (n + 1) → ℝ)
      (fun a => Fin.snoc (α := fun _ => ℝ) (R' a) (α a))
      (Fin.snoc (α := fun _ => ℝ) 0 ν)
    have hQc : ∀ j a, Q j (Fin.castSucc a) = Q' j a := fun j a => by simp [Q]
    have hQl : ∀ j, Q j (Fin.last n) = q j := fun j => by simp [Q]
    have hRcc : ∀ a b, R (Fin.castSucc a) (Fin.castSucc b) = R' a b := fun a b => by simp [R]
    have hRcl : ∀ a, R (Fin.castSucc a) (Fin.last n) = α a := fun a => by simp [R]
    have hRlc : ∀ b, R (Fin.last n) (Fin.castSucc b) = 0 := fun b => by simp [R]
    have hRll : R (Fin.last n) (Fin.last n) = ν := by simp [R]
    refine ⟨Q, R, ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
    · ext j b
      rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
      induction b using Fin.lastCases with
      | last =>
        simp only [hQc, hRcl, hQl, hRll]
        have h1 := congrFun hpq j
        have h2 : p j = c j - ∑ a, Q' j a * α a := by
          simp [hp, Matrix.mulVec, dotProduct]
        simp only [Pi.smul_apply, smul_eq_mul] at h1
        change c j = _
        linarith
      | cast b =>
        simp only [hQc, hRcc, hQl, hRlc, mul_zero, add_zero]
        rw [← Matrix.mul_apply, ← h'.eq]
    · ext a b
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
      induction a using Fin.lastCases with
      | last =>
        induction b using Fin.lastCases with
        | last =>
          simp only [hQl, Matrix.one_apply_eq]
          exact hqq
        | cast b =>
          have := congrFun hq0 b
          simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at this
          simp only [hQl, hQc]
          rw [Matrix.one_apply_ne (Fin.castSucc_lt_last b).ne']
          rw [← this]
          exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      | cast a =>
        induction b using Fin.lastCases with
        | last =>
          have := congrFun hq0 a
          simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at this
          simp only [hQl, hQc]
          rw [Matrix.one_apply_ne (Fin.castSucc_lt_last a).ne, this]
        | cast b =>
          have := congrFun (congrFun h'.orth a) b
          simp only [Matrix.mul_apply, Matrix.transpose_apply] at this
          simp only [hQc, this]
          by_cases hab : a = b
          · subst hab; simp
          · rw [Matrix.one_apply_ne hab,
              Matrix.one_apply_ne (fun h => hab (Fin.castSucc_injective _ h))]
    · intro a b hab
      induction a using Fin.lastCases with
      | last =>
        induction b using Fin.lastCases with
        | last => exact absurd hab (lt_irrefl _)
        | cast b => exact hRlc b
      | cast a =>
        induction b using Fin.lastCases with
        | last => exact absurd hab (not_lt.mpr (Fin.castSucc_lt_last a).le)
        | cast b => rw [hRcc]; exact h'.upper (by simpa using hab)
    · intro a
      induction a using Fin.lastCases with
      | last => rw [hRll]; exact hν
      | cast a => rw [hRcc]; exact h'.diag_nonneg a

/-- The SVD of step 4 of Section 5.4 of arXiv 2502.03008 exists: a full SVD of a square matrix with
orthogonal factors and nonnegative singular values in decreasing order. -/
theorem exists_square_svd {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ (P Q : Matrix (Fin n) (Fin n) ℝ) (s : Fin n → ℝ), Pᵀ * P = 1 ∧ Qᵀ * Q = 1 ∧
      (∀ a, 0 ≤ s a) ∧ Antitone s ∧ A = P * Matrix.diagonal s * Qᵀ := by
  obtain ⟨U, V, em, en, hU, hV, hA⟩ := SVD.exists_full_svd A
  set T := Matrix.toEuclideanLin A with hT
  let c : Fin (Fintype.card (Fin n)) ≃ Fin n := finCongr (Fintype.card_fin n)
  let e₁ : Fin n ≃ Fin n := em.trans c
  let e₂ : Fin n ≃ Fin n := en.trans c
  let s : Fin n → ℝ := fun a => T.singularValues (a : ℕ)
  let P : Matrix (Fin n) (Fin n) ℝ := U.submatrix id e₁.symm
  let Q : Matrix (Fin n) (Fin n) ℝ := V.submatrix id e₂.symm
  refine ⟨P, Q, s, ?_, ?_, fun a => T.singularValues_nonneg _, ?_, ?_⟩
  · have : Pᵀ * P = (Uᵀ * U).submatrix e₁.symm e₁.symm := by
      ext a b; simp [P, Matrix.mul_apply]
    rw [this, hU, Matrix.submatrix_one_equiv]
  · have : Qᵀ * Q = (Vᵀ * V).submatrix e₂.symm e₂.symm := by
      ext a b; simp [Q, Matrix.mul_apply]
    rw [this, hV, Matrix.submatrix_one_equiv]
  · intro a b hab
    exact T.singularValues_antitone hab
  · have hDg : (Matrix.of fun i j => if ((em i : ℕ) = en j) then T.singularValues (en j) else 0) =
        (Matrix.diagonal s).submatrix e₁ e₂ := by
      ext i j
      by_cases h : (em i : ℕ) = en j
      · have h' : e₁ i = e₂ j := Fin.ext (by simpa [e₁, e₂, c] using h)
        simp [h, h', s, e₂, c]
      · have h' : e₁ i ≠ e₂ j := fun h'' => h (by simpa [e₁, e₂, c] using congrArg Fin.val h'')
        simp [h, h']
    have hU' : U = P.submatrix id e₁ := by ext a b; simp [P]
    have hV' : Vᵀ = Qᵀ.submatrix e₂ id := by ext a b; simp [Q]
    rw [hA, hDg, hU', hV', Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    rfl

end QR

/-! ### The scheme -/

section Scheme

variable {Nx Nμ r r₁ n : ℕ}

/-- The fixed data of one time step: the stencils `D^x`, `D^xx`, the matrices `A`, `|A|`, the
opacity `σ` and the time step `Δt`. -/
structure SuOlsonFixedData (Nx Nμ : ℕ) where
  /-- The centred stencil `D^x`. -/
  Dx : Matrix (Fin Nx) (Fin Nx) ℝ
  /-- The stabilisation `D^xx`. -/
  Dxx : Matrix (Fin Nx) (Fin Nx) ℝ
  /-- The angular coupling matrix `A`. -/
  A : Matrix (Fin Nμ) (Fin Nμ) ℝ
  /-- The matrix `|A|`. -/
  absA : Matrix (Fin Nμ) (Fin Nμ) ℝ
  /-- The opacity `σ`. -/
  σ : ℝ
  /-- The time step `Δt`. -/
  Δt : ℝ

/-- The entry `∑_{m,n} X_{jm} S_{mn} V_{kn}` of the low-rank factorization `X S Vᵀ`. -/
def factorEntry {a b : ℕ} (X : Matrix (Fin Nx) (Fin a) ℝ) (S : Matrix (Fin a) (Fin b) ℝ)
    (V : Matrix (Fin Nμ) (Fin b) ℝ) (j : Fin Nx) (k : Fin Nμ) : ℝ :=
  ∑ m, ∑ n, X j m * S m n * V k n

/-- `factorEntry` computes the entries of `X S Vᵀ` (notation of arXiv 2502.03008, Theorem 4). -/
theorem factorEntry_eq {a b : ℕ} (X : Matrix (Fin Nx) (Fin a) ℝ) (S : Matrix (Fin a) (Fin b) ℝ)
    (V : Matrix (Fin Nμ) (Fin b) ℝ) (j : Fin Nx) (k : Fin Nμ) :
    factorEntry X S V j k = (X * S * Vᵀ) j k := by
  simp only [factorEntry, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The discrete mass density `ρ_j = √2 B_j Φ_j + B_j` of Definition 4, where
`Φ_j = ∑_{m,n} X_{jm} S_{mn} V_{0n}` is the zeroth moment of the low-rank factors. -/
noncomputable def massDensity [NeZero Nμ] {a b : ℕ} (B : Fin Nx → ℝ)
    (X : Matrix (Fin Nx) (Fin a) ℝ) (S : Matrix (Fin a) (Fin b) ℝ)
    (V : Matrix (Fin Nμ) (Fin b) ℝ) (j : Fin Nx) : ℝ :=
  √2 * B j * factorEntry X S V j 0 + B j

/-- The K-step (19a) of arXiv 2502.03008, with `K₀ = X₀ S₀`: the matrix `K*` of (19a). -/
noncomputable def massKStep (P : SuOlsonFixedData Nx Nμ) (B₀ : Fin Nx → ℝ)
    (X₀ : Matrix (Fin Nx) (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ)
    (V₀ : Matrix (Fin Nμ) (Fin r) ℝ) : Matrix (Fin Nx) (Fin r) ℝ := fun j p =>
  1 / (1 + P.σ * P.Δt) * (X₀ * S₀) j p
    - P.Δt / (1 + P.σ * P.Δt) * (1 / B₀ j) * ∑ i, P.Dx j i * B₀ i * ∑ n, (X₀ * S₀) i n *
        ∑ k, ∑ ℓ, V₀ ℓ n * P.A k ℓ * V₀ k p
    + P.Δt / (1 + P.σ * P.Δt) * (1 / B₀ j) * ∑ i, P.Dxx j i * B₀ i * ∑ n, (X₀ * S₀) i n *
        ∑ k, ∑ ℓ, V₀ ℓ n * P.absA k ℓ * V₀ k p

/-- The L-step (19c) of arXiv 2502.03008 with `L₀ = V₀ S₀ᵀ`.  The paper prints `D_{ij}` where we
write `D_{ji}`: see the module docstring. -/
noncomputable def massLStep (P : SuOlsonFixedData Nx Nμ) (B₀ : Fin Nx → ℝ)
    (X₀ : Matrix (Fin Nx) (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ)
    (V₀ : Matrix (Fin Nμ) (Fin r) ℝ) : Matrix (Fin Nμ) (Fin r) ℝ := fun k p =>
  1 / (1 + P.σ * P.Δt) * (V₀ * S₀ᵀ) k p
    - P.Δt / (1 + P.σ * P.Δt) * ∑ ℓ, ∑ m, P.A ℓ k * (V₀ * S₀ᵀ) ℓ m *
        ∑ i, X₀ i m * B₀ i * ∑ j, P.Dx j i * (1 / B₀ j) * X₀ j p
    + P.Δt / (1 + P.σ * P.Δt) * ∑ ℓ, ∑ m, P.absA ℓ k * (V₀ * S₀ᵀ) ℓ m *
        ∑ i, X₀ i m * B₀ i * ∑ j, P.Dxx j i * (1 / B₀ j) * X₀ j p

/-- The extra augmentation `(1 / B₀) ⊙ D (B₀ ⊙ X₀)` of (19b) of arXiv 2502.03008. -/
noncomputable def massWeightedStencil (D : Matrix (Fin Nx) (Fin Nx) ℝ) (B₀ : Fin Nx → ℝ)
    (X₀ : Matrix (Fin Nx) (Fin r) ℝ) : Matrix (Fin Nx) (Fin r) ℝ := fun j c =>
  1 / B₀ j * ∑ i, D j i * (B₀ i * X₀ i c)

/-- The projected initial value `S̃₀ = M̂̂ S₀ N̂̂ᵀ` of (19e), `M̂̂ = X̂̂*ᵀ X₀`, `N̂̂ = V̂̂*ᵀ V₀`. -/
def massSTilde {q : ℕ} (Xhh : Matrix (Fin Nx) (Fin q) ℝ) (Vhh : Matrix (Fin Nμ) (Fin q) ℝ)
    (X₀ : Matrix (Fin Nx) (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ)
    (V₀ : Matrix (Fin Nμ) (Fin r) ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  (Xhhᵀ * X₀) * S₀ * (Vhhᵀ * V₀)ᵀ

/-- The S-step (19e) of arXiv 2502.03008: the matrix `Ŝ̂*`, for `St = S̃₀`. -/
noncomputable def massSStep {q : ℕ} (P : SuOlsonFixedData Nx Nμ) (B₀ : Fin Nx → ℝ)
    (Xhh : Matrix (Fin Nx) (Fin q) ℝ) (Vhh : Matrix (Fin Nμ) (Fin q) ℝ)
    (St : Matrix (Fin q) (Fin q) ℝ) : Matrix (Fin q) (Fin q) ℝ := fun a p =>
  1 / (1 + P.σ * P.Δt) * St a p
    - P.Δt / (1 + P.σ * P.Δt) * ∑ j, Xhh j a * (1 / B₀ j) * ∑ i, P.Dx j i * B₀ i *
        ∑ m, ∑ n, Xhh i m * St m n * ∑ k, ∑ ℓ, Vhh ℓ n * P.A k ℓ * Vhh k p
    + P.Δt / (1 + P.σ * P.Δt) * ∑ j, Xhh j a * (1 / B₀ j) * ∑ i, P.Dxx j i * B₀ i *
        ∑ m, ∑ n, Xhh i m * St m n * ∑ k, ∑ ℓ, Vhh ℓ n * P.absA k ℓ * Vhh k p

/-- The coefficient adjustment (19j) of arXiv 2502.03008: the matrix `Ŝ̂¹`. -/
noncomputable def massAdjustedS [NeZero Nμ] {q : ℕ} (Xa : Matrix (Fin Nx) (Fin (q + 1)) ℝ)
    (Xtr : Matrix (Fin Nx) (Fin q) ℝ) (Str : Matrix (Fin q) (Fin q) ℝ)
    (Vhh : Matrix (Fin Nμ) (Fin q) ℝ) (v₁ : Fin Nx → ℝ)
    (Va : Matrix (Fin Nμ) (Fin (q + 1)) ℝ) : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ :=
  Xaᵀ * Xtr * Str * Vhhᵀ *
      (1 - Matrix.vecMulVec (Pi.single 0 1 : Fin Nμ → ℝ) (Pi.single 0 1 : Fin Nμ → ℝ)) * Va
    + Xaᵀ * Matrix.vecMulVec v₁ (Pi.single 0 1 : Fin Nμ → ℝ) * Va

/-- The factors computed by the conservative truncation of Section 5.4 of arXiv 2502.03008. -/
structure ConsTruncData (Nx Nμ n r₁ : ℕ) where
  /-- `X̂^{1,cons}`. -/
  Xcons : Fin Nx → ℝ
  /-- `Ŝ^{1,cons}`. -/
  Scons : ℝ
  /-- `X̂^{1,rem}`. -/
  Xrem : Matrix (Fin Nx) (Fin n) ℝ
  /-- `Ŝ^{1,rem}`. -/
  Srem : Matrix (Fin n) (Fin n) ℝ
  /-- `P̂`. -/
  Pm : Matrix (Fin n) (Fin n) ℝ
  /-- `Q̂`. -/
  Qm : Matrix (Fin n) (Fin n) ℝ
  /-- The singular values. -/
  sv : Fin n → ℝ
  /-- `X¹`. -/
  X₁ : Matrix (Fin Nx) (Fin (r₁ + 1)) ℝ
  /-- `R¹`. -/
  R₁ : Matrix (Fin (r₁ + 1)) (Fin (r₁ + 1)) ℝ
  /-- `V¹`. -/
  V₁ : Matrix (Fin Nμ) (Fin (r₁ + 1)) ℝ
  /-- `R²`. -/
  R₂ : Matrix (Fin (r₁ + 1)) (Fin (r₁ + 1)) ℝ
  /-- `S¹`. -/
  S₁ : Matrix (Fin (r₁ + 1)) (Fin (r₁ + 1)) ℝ

/-- The conservative truncation of Section 5.4 of arXiv 2502.03008, applied to `Xa = X̂̂¹`,
`Sa = Ŝ̂¹`, `Va = V̂̂¹` of width `n + 1`, with target rank `r₁ ≤ n` and tolerance `ϑ`.  Step 1 is
the split of `K̂̂¹ = Xa Sa` and of `Va` into the first column and the remaining `n` columns. -/
structure IsConsTruncation [NeZero Nμ] (hr₁ : r₁ ≤ n) (ϑ : ℝ)
    (Xa : Matrix (Fin Nx) (Fin (n + 1)) ℝ) (Sa : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Va : Matrix (Fin Nμ) (Fin (n + 1)) ℝ) (T : ConsTruncData Nx Nμ n r₁) : Prop where
  /-- Step 2. -/
  scons_eq : T.Scons = √(∑ j, ((Xa * Sa) j 0) ^ 2)
  /-- Step 2. -/
  xcons_eq : ∀ j, T.Xcons j = (Xa * Sa) j 0 / T.Scons
  /-- Step 3. -/
  qr_rem : IsGSQR (fun j c => (Xa * Sa) j (Fin.succ c)) T.Xrem T.Srem
  /-- Step 4. -/
  svd_eq : T.Srem = T.Pm * Matrix.diagonal T.sv * T.Qmᵀ
  /-- Step 4. -/
  pm_orth : T.Pmᵀ * T.Pm = 1
  /-- Step 4. -/
  qm_orth : T.Qmᵀ * T.Qm = 1
  /-- Step 4. -/
  sv_nonneg : ∀ a, 0 ≤ T.sv a
  /-- Step 4. -/
  sv_antitone : Antitone T.sv
  /-- Step 4. -/
  tail_le : √(∑ a ∈ Finset.univ.filter (fun a : Fin n => r₁ ≤ a.val), T.sv a ^ 2) ≤ ϑ
  /-- Step 5. -/
  qr_x : IsGSQR (colCons T.Xcons fun j c => ∑ a, T.Xrem j a * T.Pm a (Fin.castLE hr₁ c)) T.X₁ T.R₁
  /-- Step 5. -/
  qr_v : IsGSQR
    (colCons (Pi.single 0 1) fun k c => ∑ a, Va k (Fin.succ a) * T.Qm a (Fin.castLE hr₁ c))
    T.V₁ T.R₂
  /-- Step 6. -/
  s₁_eq : T.S₁ = T.R₁ * Matrix.diagonal (Fin.cons T.Scons fun c => T.sv (Fin.castLE hr₁ c)) * T.R₂ᵀ

/-- The factors computed in one step (19a)–(19j) of the scheme of arXiv 2502.03008. -/
structure SuOlsonStepFactors (Nx Nμ r r₁ : ℕ) where
  /-- `X̂*`. -/
  Xh : Matrix (Fin Nx) (Fin (r + r)) ℝ
  /-- The triangular factor of `X̂*`. -/
  RXh : Matrix (Fin (r + r)) (Fin (r + r)) ℝ
  /-- `X̂̂*`. -/
  Xhh : Matrix (Fin Nx) (Fin (r + r + r + r)) ℝ
  /-- The triangular factor of `X̂̂*`. -/
  RXhh : Matrix (Fin (r + r + r + r)) (Fin (r + r + r + r)) ℝ
  /-- `V̂*`. -/
  Vh : Matrix (Fin Nμ) (Fin (r + r)) ℝ
  /-- The triangular factor of `V̂*`. -/
  RVh : Matrix (Fin (r + r)) (Fin (r + r)) ℝ
  /-- `V̂̂*`. -/
  Vhh : Matrix (Fin Nμ) (Fin (r + r + r + r)) ℝ
  /-- The triangular factor of `V̂̂*`. -/
  RVhh : Matrix (Fin (r + r + r + r)) (Fin (r + r + r + r)) ℝ
  /-- The new energy `B¹`. -/
  B₁ : Fin Nx → ℝ
  /-- The new zeroth moment `v¹₀`. -/
  v₁ : Fin Nx → ℝ
  /-- `X̂̂^{*,trans}`. -/
  Xtr : Matrix (Fin Nx) (Fin (r + r + r + r)) ℝ
  /-- `Ŝ̂^{*,trans}`. -/
  Str : Matrix (Fin (r + r + r + r)) (Fin (r + r + r + r)) ℝ
  /-- `X̂̂¹`. -/
  Xa : Matrix (Fin Nx) (Fin (r + r + r + r + 1)) ℝ
  /-- The triangular factor of `X̂̂¹`. -/
  RXa : Matrix (Fin (r + r + r + r + 1)) (Fin (r + r + r + r + 1)) ℝ
  /-- `V̂̂¹`. -/
  Va : Matrix (Fin Nμ) (Fin (r + r + r + r + 1)) ℝ
  /-- The triangular factor of `V̂̂¹`. -/
  RVa : Matrix (Fin (r + r + r + r + 1)) (Fin (r + r + r + r + 1)) ℝ
  /-- The conservative truncation. -/
  trunc : ConsTruncData Nx Nμ (r + r + r + r) r₁

/-- The scheme (19a)–(19j) of arXiv 2502.03008 with the truncation of Section 5.4, where the
matrices `Kst = K*` of (19a), `Lst = L*` of (19c) and `Sst = Ŝ̂*` of (19e) are left arbitrary. -/
structure IsSuOlsonDLRACore [NeZero Nμ] (P : SuOlsonFixedData Nx Nμ) (B₀ : Fin Nx → ℝ)
    (X₀ : Matrix (Fin Nx) (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ)
    (V₀ : Matrix (Fin Nμ) (Fin r) ℝ) (ϑ : ℝ) (hr₁ : r₁ ≤ r + r + r + r)
    (Kst : Matrix (Fin Nx) (Fin r) ℝ) (Lst : Matrix (Fin Nμ) (Fin r) ℝ)
    (Sst : Matrix (Fin (r + r + r + r)) (Fin (r + r + r + r)) ℝ)
    (D : SuOlsonStepFactors Nx Nμ r r₁) : Prop where
  /-- (19b), first augmentation. -/
  qr_k : IsGSQR (colAppend Kst X₀) D.Xh D.RXh
  /-- (19b), second augmentation. -/
  aug_x : IsGSQR
    (colAppend (colAppend D.Xh (massWeightedStencil P.Dx B₀ X₀)) (massWeightedStencil P.Dxx B₀ X₀))
    D.Xhh D.RXhh
  /-- (19d), first augmentation. -/
  qr_l : IsGSQR (colAppend Lst V₀) D.Vh D.RVh
  /-- (19d), second augmentation. -/
  aug_v : IsGSQR (colAppend (colAppend D.Vh (P.Aᵀ * V₀)) (P.absAᵀ * V₀)) D.Vhh D.RVhh
  /-- (19f). -/
  moment_eq : ∀ j, D.B₁ j / B₀ j * D.v₁ j =
    1 / (1 + P.σ * P.Δt) * factorEntry X₀ S₀ V₀ j 0
      - P.Δt / (1 + P.σ * P.Δt) * ∑ i, ∑ ℓ, 1 / B₀ j * P.Dx j i * B₀ i *
          factorEntry D.Xhh (massSTilde D.Xhh D.Vhh X₀ S₀ V₀) D.Vhh i ℓ * P.A 0 ℓ
      + P.Δt / (1 + P.σ * P.Δt) * ∑ i, ∑ ℓ, 1 / B₀ j * P.Dxx j i * B₀ i *
          factorEntry D.Xhh (massSTilde D.Xhh D.Vhh X₀ S₀ V₀) D.Vhh i ℓ * P.absA 0 ℓ
      + √2 * P.σ * P.Δt / (1 + P.σ * P.Δt) * (D.B₁ j / B₀ j)
  /-- (19g). -/
  energy_eq : ∀ j, D.B₁ j / B₀ j =
    1 + P.σ * P.Δt * (D.B₁ j / B₀ j) * (√2 * D.v₁ j - 2)
  /-- (19h) with the QR step following it. -/
  qr_trans : IsGSQR (fun j p => B₀ j / D.B₁ j * (D.Xhh * Sst) j p) D.Xtr D.Str
  /-- (19i), space. -/
  qr_xa : IsGSQR (colCons D.v₁ D.Xtr) D.Xa D.RXa
  /-- (19i), direction. -/
  qr_va : IsGSQR (colCons (Pi.single 0 1) D.Vhh) D.Va D.RVa
  /-- Section 5.4 applied to (19j). -/
  trunc : IsConsTruncation hr₁ ϑ D.Xa (massAdjustedS D.Xa D.Xtr D.Str D.Vhh D.v₁ D.Va) D.Va D.trunc

/-- **One step of the scheme of arXiv 2502.03008**, (19a)–(19j) with the conservative truncation of
Section 5.4, from `(B₀, X₀ S₀ V₀ᵀ)` to `(D.B₁, D.trunc.X₁ D.trunc.S₁ D.trunc.V₁ᵀ)`. -/
def IsSuOlsonDLRAStep [NeZero Nμ] (P : SuOlsonFixedData Nx Nμ) (B₀ : Fin Nx → ℝ)
    (X₀ : Matrix (Fin Nx) (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ)
    (V₀ : Matrix (Fin Nμ) (Fin r) ℝ) (ϑ : ℝ) (hr₁ : r₁ ≤ r + r + r + r)
    (D : SuOlsonStepFactors Nx Nμ r r₁) : Prop :=
  IsSuOlsonDLRACore P B₀ X₀ S₀ V₀ ϑ hr₁ (massKStep P B₀ X₀ S₀ V₀) (massLStep P B₀ X₀ S₀ V₀)
    (massSStep P B₀ D.Xhh D.Vhh (massSTilde D.Xhh D.Vhh X₀ S₀ V₀)) D

/-! ### Zeroth moment -/

/-- arXiv 2502.03008, Section 5.4 and proof of Theorem 4: the conservative truncation does not
change the zeroth moment, provided the row `0` of the remaining columns of `Va` vanishes. -/
theorem IsConsTruncation.zeroth_moment [NeZero Nμ] {hr₁ : r₁ ≤ n} {ϑ : ℝ}
    {Xa : Matrix (Fin Nx) (Fin (n + 1)) ℝ} {Sa : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {Va : Matrix (Fin Nμ) (Fin (n + 1)) ℝ} {T : ConsTruncData Nx Nμ n r₁}
    (h : IsConsTruncation hr₁ ϑ Xa Sa Va T) (hV : ∀ c : Fin n, Va 0 c.succ = 0) (j : Fin Nx) :
    factorEntry T.X₁ T.S₁ T.V₁ j 0 = (Xa * Sa) j 0 := by
  set d : Fin (r₁ + 1) → ℝ := Fin.cons T.Scons fun c => T.sv (Fin.castLE hr₁ c) with hd
  have hprod : T.X₁ * T.S₁ * T.V₁ᵀ =
      colCons T.Xcons (fun j c => ∑ a, T.Xrem j a * T.Pm a (Fin.castLE hr₁ c)) *
        Matrix.diagonal d *
        (colCons (Pi.single 0 1) fun k c =>
          ∑ a, Va k (Fin.succ a) * T.Qm a (Fin.castLE hr₁ c))ᵀ := by
    rw [h.qr_x.eq, h.qr_v.eq, h.s₁_eq, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc, hd]
  rw [factorEntry_eq, hprod]
  have hrest : ∀ c : Fin r₁,
      colCons (Pi.single 0 1 : Fin Nμ → ℝ)
        (fun k c => ∑ a, Va k (Fin.succ a) * T.Qm a (Fin.castLE hr₁ c)) 0 c.succ = 0 := by
    intro c
    simp [colCons, hV]
  have hcons_eq : T.Xcons j * T.Scons = (Xa * Sa) j 0 := by
    by_cases h0 : T.Scons = 0
    · have hsum : ∑ i, ((Xa * Sa) i 0) ^ 2 = 0 := by
        have h1 := h.scons_eq
        rw [h0] at h1
        have hnn : 0 ≤ ∑ i, ((Xa * Sa) i 0) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
        exact (Real.sqrt_eq_zero hnn).mp h1.symm
      have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).mp hsum j
        (Finset.mem_univ j)
      rw [h0, mul_zero, pow_eq_zero_iff two_ne_zero |>.mp this]
    · rw [h.xcons_eq, div_mul_cancel₀ _ h0]
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  rw [Fin.sum_univ_succ]
  simp only [hrest, mul_zero, Finset.sum_const_zero, add_zero]
  rw [Finset.sum_eq_single 0 (fun c _ hc => by simp [Matrix.diagonal_apply_ne, hc]) (by simp)]
  rw [← Matrix.mul_apply, ← hcons_eq]
  simp [colCons, hd]

/-- arXiv 2502.03008, proof of Theorem 4: since the augmented bases contain `X₀` and `V₀`, we have
`∑_{m,n} X̂̂*_{im} S̃₀_{mn} V̂̂*_{ℓn} = v₀_{iℓ}`.  This is derived from the QR steps. -/
theorem factorEntry_massSTilde {k w₁ w₂ : ℕ} {X₀ : Matrix (Fin Nx) (Fin r) ℝ}
    {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix (Fin Nμ) (Fin r) ℝ}
    {Kst : Matrix (Fin Nx) (Fin k) ℝ} {Lst : Matrix (Fin Nμ) (Fin k) ℝ}
    {Xh : Matrix (Fin Nx) (Fin (k + r)) ℝ} {RXh : Matrix (Fin (k + r)) (Fin (k + r)) ℝ}
    {Vh : Matrix (Fin Nμ) (Fin (k + r)) ℝ} {RVh : Matrix (Fin (k + r)) (Fin (k + r)) ℝ}
    {WX₁ : Matrix (Fin Nx) (Fin w₁) ℝ} {WX₂ : Matrix (Fin Nx) (Fin w₂) ℝ}
    {WV₁ : Matrix (Fin Nμ) (Fin w₁) ℝ} {WV₂ : Matrix (Fin Nμ) (Fin w₂) ℝ}
    {Xhh : Matrix (Fin Nx) (Fin (k + r + w₁ + w₂)) ℝ}
    {Vhh : Matrix (Fin Nμ) (Fin (k + r + w₁ + w₂)) ℝ}
    {RXhh RVhh : Matrix (Fin (k + r + w₁ + w₂)) (Fin (k + r + w₁ + w₂)) ℝ}
    (hK : IsGSQR (colAppend Kst X₀) Xh RXh)
    (hX : IsGSQR (colAppend (colAppend Xh WX₁) WX₂) Xhh RXhh)
    (hL : IsGSQR (colAppend Lst V₀) Vh RVh)
    (hV : IsGSQR (colAppend (colAppend Vh WV₁) WV₂) Vhh RVhh)
    (i : Fin Nx) (ℓ : Fin Nμ) :
    factorEntry Xhh (massSTilde Xhh Vhh X₀ S₀ V₀) Vhh i ℓ = factorEntry X₀ S₀ V₀ i ℓ := by
  have hXh : Xh * Xhᵀ * X₀ = X₀ := capture_colAppend_right hK.capture
  have hVh : Vh * Vhᵀ * V₀ = V₀ := capture_colAppend_right hL.capture
  have hXhh : Xhh * Xhhᵀ * Xh = Xh := capture_colAppend_left (capture_colAppend_left hX.capture)
  have hVhh : Vhh * Vhhᵀ * Vh = Vh := capture_colAppend_left (capture_colAppend_left hV.capture)
  have hX₀ : Xhh * Xhhᵀ * X₀ = X₀ := by
    rw [← hXh, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hXhh]
  have hV₀ : Vhh * Vhhᵀ * V₀ = V₀ := by
    rw [← hVh, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hVhh]
  have hprod : Xhh * massSTilde Xhh Vhh X₀ S₀ V₀ * Vhhᵀ = X₀ * S₀ * V₀ᵀ := by
    conv_rhs => rw [← hX₀]
    nth_rw 2 [← hV₀]
    simp only [massSTilde, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [factorEntry_eq, factorEntry_eq, hprod]

/-- arXiv 2502.03008, proof of Theorem 4: `Φ¹_j = v¹_{j0}`, the zeroth moment of the new low-rank
factors is the solution of (19f), (19g).  This is derived from (19i), (19j) and Section 5.4. -/
theorem IsSuOlsonDLRACore.moment_new [NeZero Nμ] {P : SuOlsonFixedData Nx Nμ} {B₀ : Fin Nx → ℝ}
    {X₀ : Matrix (Fin Nx) (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ}
    {V₀ : Matrix (Fin Nμ) (Fin r) ℝ} {ϑ : ℝ} {hr₁ : r₁ ≤ r + r + r + r}
    {Kst : Matrix (Fin Nx) (Fin r) ℝ} {Lst : Matrix (Fin Nμ) (Fin r) ℝ}
    {Sst : Matrix (Fin (r + r + r + r)) (Fin (r + r + r + r)) ℝ}
    {D : SuOlsonStepFactors Nx Nμ r r₁} (h : IsSuOlsonDLRACore P B₀ X₀ S₀ V₀ ϑ hr₁ Kst Lst Sst D)
    (j : Fin Nx) : factorEntry D.trunc.X₁ D.trunc.S₁ D.trunc.V₁ j 0 = D.v₁ j := by
  obtain ⟨hfirst, hrow⟩ := h.qr_va.first_column
  rw [h.trunc.zeroth_moment hrow j]
  set e : Fin Nμ → ℝ := Pi.single 0 1 with he
  have hee : e ⬝ᵥ e = 1 := by simp [he]
  have hcol : ∀ (M : Matrix (Fin (r + r + r + r + 1)) (Fin Nμ) ℝ) a,
      (M * D.Va) a 0 = (M *ᵥ e) a := by
    intro M a
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, hfirst]
  have hproj : (1 - Matrix.vecMulVec e e) *ᵥ e = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, hee]
    simp
  have hvv : Matrix.vecMulVec D.v₁ e *ᵥ e = D.v₁ := by
    rw [Matrix.vecMulVec_mulVec, hee]
    simp
  have hS : ∀ a, massAdjustedS D.Xa D.Xtr D.Str D.Vhh D.v₁ D.Va a 0 = (D.Xaᵀ *ᵥ D.v₁) a := by
    intro a
    have h₁ : ∀ T : Matrix (Fin (r + r + r + r + 1)) (Fin Nμ) ℝ,
        (T * (1 - Matrix.vecMulVec e e)) *ᵥ e = 0 := fun T => by
      rw [← Matrix.mulVec_mulVec, hproj, Matrix.mulVec_zero]
    have h₂ : (D.Xaᵀ * Matrix.vecMulVec D.v₁ e) *ᵥ e = D.Xaᵀ *ᵥ D.v₁ := by
      rw [← Matrix.mulVec_mulVec, hvv]
    rw [massAdjustedS, Matrix.add_apply, hcol, hcol, h₁, h₂]
    simp
  have hcap := capture_colCons h.qr_xa.capture j
  rw [← hcap, Matrix.mul_apply]
  simp only [hS, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => by ring

/-- arXiv 2502.03008, Theorem 4, for arbitrary `K*`, `L*`, `Ŝ̂*`: the proof of the local law does
not use (19a), (19c), (19e). -/
theorem IsSuOlsonDLRACore.local_mass_conservation [NeZero Nμ] {P : SuOlsonFixedData Nx Nμ}
    {B₀ : Fin Nx → ℝ} {X₀ : Matrix (Fin Nx) (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ}
    {V₀ : Matrix (Fin Nμ) (Fin r) ℝ} {ϑ : ℝ} {hr₁ : r₁ ≤ r + r + r + r}
    {Kst : Matrix (Fin Nx) (Fin r) ℝ} {Lst : Matrix (Fin Nμ) (Fin r) ℝ}
    {Sst : Matrix (Fin (r + r + r + r)) (Fin (r + r + r + r)) ℝ}
    {D : SuOlsonStepFactors Nx Nμ r r₁} (h : IsSuOlsonDLRACore P B₀ X₀ S₀ V₀ ϑ hr₁ Kst Lst Sst D)
    (hΔt : 0 < P.Δt) (hσ : 0 ≤ P.σ) (hB : ∀ j, 0 < B₀ j) (j : Fin Nx) :
    1 / P.Δt * (massDensity D.B₁ D.trunc.X₁ D.trunc.S₁ D.trunc.V₁ j
        - massDensity B₀ X₀ S₀ V₀ j) =
      -√2 * ∑ i, ∑ ℓ, P.Dx j i * B₀ i * factorEntry X₀ S₀ V₀ i ℓ * P.A 0 ℓ
        + √2 * ∑ i, ∑ ℓ, P.Dxx j i * B₀ i * factorEntry X₀ S₀ V₀ i ℓ * P.absA 0 ℓ := by
  have hb : B₀ j ≠ 0 := (hB j).ne'
  have hτ : 1 + P.σ * P.Δt ≠ 0 := by positivity
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hm := h.moment_eq j
  have he := h.energy_eq j
  simp only [factorEntry_massSTilde h.qr_k h.aug_x h.qr_l h.aug_v] at hm
  rw [massDensity, massDensity, h.moment_new j]
  set T₁ := ∑ i, ∑ ℓ, P.Dx j i * B₀ i * factorEntry X₀ S₀ V₀ i ℓ * P.A 0 ℓ with hT₁
  set T₂ := ∑ i, ∑ ℓ, P.Dxx j i * B₀ i * factorEntry X₀ S₀ V₀ i ℓ * P.absA 0 ℓ with hT₂
  have h₁ : ∑ i, ∑ ℓ, 1 / B₀ j * P.Dx j i * B₀ i * factorEntry X₀ S₀ V₀ i ℓ * P.A 0 ℓ =
      1 / B₀ j * T₁ := by
    rw [hT₁, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ℓ _ => by ring
  have h₂ : ∑ i, ∑ ℓ, 1 / B₀ j * P.Dxx j i * B₀ i * factorEntry X₀ S₀ V₀ i ℓ * P.absA 0 ℓ =
      1 / B₀ j * T₂ := by
    rw [hT₂, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ℓ _ => by ring
  rw [h₁, h₂] at hm
  set φ := factorEntry X₀ S₀ V₀ j 0 with hφ
  set b₁ := D.B₁ j
  set v := D.v₁ j
  have hm' : (1 + P.σ * P.Δt) * b₁ * v =
      φ * B₀ j - P.Δt * T₁ + P.Δt * T₂ + √2 * P.σ * P.Δt * b₁ := by
    field_simp at hm
    linear_combination hm
  have he' : b₁ = B₀ j + P.σ * P.Δt * b₁ * (√2 * v - 2) := by
    field_simp at he
    linear_combination he
  have hkey : (√2 * b₁ * v + b₁) - (√2 * B₀ j * φ + B₀ j) =
      P.Δt * (-√2 * T₁ + √2 * T₂) := by
    linear_combination √2 * hm' + he' + (P.σ * P.Δt * b₁) * hs
  rw [hkey]
  field_simp

/-- **Theorem 4 of arXiv 2502.03008 (local mass conservation).**  One step of the scheme with the
conservative truncation satisfies, with `v₀ = X₀ S₀ V₀ᵀ` and `Φ = ∑_{m,n} X_{jm} S_{mn} V_{0n}`,
`(1 / Δt) ((√2 B¹_j Φ¹_j + B¹_j) - (√2 B⁰_j Φ⁰_j + B⁰_j)) =`
`-√2 ∑_i ∑_ℓ D^x_{ji} B⁰_i v⁰_{iℓ} A_{0ℓ} + √2 ∑_i ∑_ℓ D^xx_{ji} B⁰_i v⁰_{iℓ} |A|_{0ℓ}`.
`D^x`, `D^xx`, `A`, `|A|` may be arbitrary.  Assumed beyond the paper: `B₀ > 0`, implicit there. -/
theorem theorem_4 [NeZero Nμ] {P : SuOlsonFixedData Nx Nμ}
    {B₀ : Fin Nx → ℝ} {X₀ : Matrix (Fin Nx) (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ}
    {V₀ : Matrix (Fin Nμ) (Fin r) ℝ} {ϑ : ℝ} {hr₁ : r₁ ≤ r + r + r + r}
    {D : SuOlsonStepFactors Nx Nμ r r₁} (h : IsSuOlsonDLRAStep P B₀ X₀ S₀ V₀ ϑ hr₁ D)
    (hΔt : 0 < P.Δt) (hσ : 0 ≤ P.σ) (hB : ∀ j, 0 < B₀ j) (j : Fin Nx) :
    1 / P.Δt * (massDensity D.B₁ D.trunc.X₁ D.trunc.S₁ D.trunc.V₁ j
        - massDensity B₀ X₀ S₀ V₀ j) =
      -√2 * ∑ i, ∑ ℓ, P.Dx j i * B₀ i * factorEntry X₀ S₀ V₀ i ℓ * P.A 0 ℓ
        + √2 * ∑ i, ∑ ℓ, P.Dxx j i * B₀ i * factorEntry X₀ S₀ V₀ i ℓ * P.absA 0 ℓ :=
  IsSuOlsonDLRACore.local_mass_conservation h hΔt hσ hB j


/-! ### Periodic stencils and total mass -/

/-- The periodic centred stencil `D^x` of arXiv 2502.03008 on `Nx` cells with
`Δx = 1 / Nx`: `D^x_{j,j±1} = ±1 / (2 Δx)`, indices modulo `Nx`.  For `Nx ≥ 3` the entries are
those of the paper. -/
noncomputable def stencilCentred (Nx : ℕ) [NeZero Nx] : Matrix (Fin Nx) (Fin Nx) ℝ := fun j i =>
  (if i = j + 1 then (Nx : ℝ) / 2 else 0) - (if i = j - 1 then (Nx : ℝ) / 2 else 0)

/-- The periodic stabilisation stencil `D^xx` of arXiv 2502.03008 on `Nx` cells with
`Δx = 1 / Nx`: `D^xx_{j,j} = -1 / Δx`, `D^xx_{j,j±1} = 1 / (2 Δx)`, indices modulo `Nx`. -/
noncomputable def stencilStab (Nx : ℕ) [NeZero Nx] : Matrix (Fin Nx) (Fin Nx) ℝ := fun j i =>
  (if i = j then -(Nx : ℝ) else 0) + (if i = j + 1 then (Nx : ℝ) / 2 else 0)
    + (if i = j - 1 then (Nx : ℝ) / 2 else 0)

/-- Each cell has exactly one left neighbour (arXiv 2502.03008, periodic stencils). -/
private theorem sum_ite_succ [NeZero Nx] (i : Fin Nx) (c : ℝ) :
    ∑ j : Fin Nx, (if i = j + 1 then c else 0) = c := by
  have h : ∀ j : Fin Nx, (i = j + 1) ↔ (j = i - 1) := fun j => by
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Each cell has exactly one right neighbour (arXiv 2502.03008, periodic stencils). -/
private theorem sum_ite_pred [NeZero Nx] (i : Fin Nx) (c : ℝ) :
    ∑ j : Fin Nx, (if i = j - 1 then c else 0) = c := by
  have h : ∀ j : Fin Nx, (i = j - 1) ↔ (j = i + 1) := fun j => by
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The columns of the periodic `D^x` of arXiv 2502.03008 sum to zero. -/
theorem sum_stencilCentred [NeZero Nx] (i : Fin Nx) : ∑ j, stencilCentred Nx j i = 0 := by
  simp only [stencilCentred, Finset.sum_sub_distrib, sum_ite_succ, sum_ite_pred, sub_self]

/-- The columns of the periodic `D^xx` of arXiv 2502.03008 sum to zero. -/
theorem sum_stencilStab [NeZero Nx] (i : Fin Nx) : ∑ j, stencilStab Nx j i = 0 := by
  simp only [stencilStab, Finset.sum_add_distrib, sum_ite_succ, sum_ite_pred]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-- The total mass `m = Δx ∑_j (√2 B_j Φ_j + B_j)` of the numerical section of arXiv 2502.03008,
with `Δx = 1 / Nx`. -/
noncomputable def totalMass [NeZero Nμ] {a b : ℕ} (B : Fin Nx → ℝ) (X : Matrix (Fin Nx) (Fin a) ℝ)
    (S : Matrix (Fin a) (Fin b) ℝ) (V : Matrix (Fin Nμ) (Fin b) ℝ) : ℝ :=
  1 / (Nx : ℝ) * ∑ j, massDensity B X S V j

/-- Stencils with vanishing column sums give a telescoping flux (arXiv 2502.03008, Theorem 4). -/
private theorem sum_flux_eq_zero {D : Matrix (Fin Nx) (Fin Nx) ℝ} (hD : ∀ i, ∑ j, D j i = 0)
    (B : Fin Nx → ℝ) (v : Fin Nx → Fin Nμ → ℝ) (c : Fin Nμ → ℝ) :
    ∑ j, ∑ i, ∑ ℓ, D j i * B i * v i ℓ * c ℓ = 0 := by
  have h : ∀ j i, ∑ ℓ, D j i * B i * v i ℓ * c ℓ = D j i * ∑ ℓ, B i * v i ℓ * c ℓ := fun j i => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ℓ _ => by ring
  simp only [h]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, hD, zero_mul, Finset.sum_const_zero]

/-- **Total mass conservation** (arXiv 2502.03008, Theorem 4 summed over the cells; the paper
states the local law and observes the total mass numerically): for the periodic stencils and no
source, one step of the scheme conserves `m = Δx ∑_j (√2 B_j Φ_j + B_j)`. -/
theorem total_mass_conservation [NeZero Nx] [NeZero Nμ] {P : SuOlsonFixedData Nx Nμ}
    {B₀ : Fin Nx → ℝ} {X₀ : Matrix (Fin Nx) (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ}
    {V₀ : Matrix (Fin Nμ) (Fin r) ℝ} {ϑ : ℝ} {hr₁ : r₁ ≤ r + r + r + r}
    {D : SuOlsonStepFactors Nx Nμ r r₁} (h : IsSuOlsonDLRAStep P B₀ X₀ S₀ V₀ ϑ hr₁ D)
    (hDx : P.Dx = stencilCentred Nx) (hDxx : P.Dxx = stencilStab Nx)
    (hΔt : 0 < P.Δt) (hσ : 0 ≤ P.σ) (hB : ∀ j, 0 < B₀ j) :
    totalMass D.B₁ D.trunc.X₁ D.trunc.S₁ D.trunc.V₁ = totalMass B₀ X₀ S₀ V₀ := by
  have hlaw := theorem_4 h hΔt hσ hB
  have hsum : ∑ j, (1 / P.Δt * (massDensity D.B₁ D.trunc.X₁ D.trunc.S₁ D.trunc.V₁ j
      - massDensity B₀ X₀ S₀ V₀ j)) = 0 := by
    simp only [hlaw]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      sum_flux_eq_zero (by rw [hDx]; exact sum_stencilCentred) B₀ (factorEntry X₀ S₀ V₀) (P.A 0),
      sum_flux_eq_zero (by rw [hDxx]; exact sum_stencilStab) B₀ (factorEntry X₀ S₀ V₀) (P.absA 0)]
    simp
  rw [← Finset.mul_sum, Finset.sum_sub_distrib] at hsum
  have hne : 1 / P.Δt ≠ 0 := by positivity
  have := (mul_eq_zero.mp hsum).resolve_left hne
  rw [totalMass, totalMass, sub_eq_zero.mp this]

/-! ### Well-posedness -/

/-- Well-posedness of Section 5.4 of arXiv 2502.03008: the conservative truncation exists for every
target rank `r₁ ≤ n` and every tolerance above the discarded tail `ϑ₀`, and `ϑ₀ = 0` when nothing
is discarded. -/
theorem exists_isConsTruncation [NeZero Nμ] (hr₁ : r₁ ≤ n) (hx : n + 1 ≤ Nx) (hμ : n + 1 ≤ Nμ)
    (Xa : Matrix (Fin Nx) (Fin (n + 1)) ℝ) (Sa : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Va : Matrix (Fin Nμ) (Fin (n + 1)) ℝ) :
    ∃ (ϑ₀ : ℝ) (T : ConsTruncData Nx Nμ n r₁), (r₁ = n → ϑ₀ = 0) ∧
      ∀ ϑ, ϑ₀ ≤ ϑ → IsConsTruncation hr₁ ϑ Xa Sa Va T := by
  set Scons := √(∑ j, ((Xa * Sa) j 0) ^ 2) with hScons
  let Xcons : Fin Nx → ℝ := fun j => (Xa * Sa) j 0 / Scons
  obtain ⟨Xrem, Srem, h₃⟩ := exists_isGSQR (fun j c => (Xa * Sa) j (Fin.succ c))
    (by simp only [Fintype.card_fin]; omega)
  obtain ⟨Pm, Qm, sv, hP, hQ, hnn, hanti, hsvd⟩ := exists_square_svd Srem
  obtain ⟨X₁, R₁, hX⟩ := exists_isGSQR
    (colCons Xcons fun j c => ∑ a, Xrem j a * Pm a (Fin.castLE hr₁ c))
    (by simp only [Fintype.card_fin]; omega)
  obtain ⟨V₁, R₂, hV⟩ := exists_isGSQR
    (colCons (Pi.single 0 1) fun k c => ∑ a, Va k (Fin.succ a) * Qm a (Fin.castLE hr₁ c))
    (by simp only [Fintype.card_fin]; omega)
  refine ⟨√(∑ a ∈ Finset.univ.filter (fun a : Fin n => r₁ ≤ a.val), sv a ^ 2),
    ⟨Xcons, Scons, Xrem, Srem, Pm, Qm, sv, X₁, R₁, V₁, R₂,
      R₁ * Matrix.diagonal (Fin.cons Scons fun c => sv (Fin.castLE hr₁ c)) * R₂ᵀ⟩, ?_,
    fun ϑ hϑ => ⟨rfl, fun _ => rfl, h₃, hsvd, hP, hQ, hnn, hanti, hϑ, hX, hV, rfl⟩⟩
  rintro rfl
  have hempty : Finset.univ.filter (fun a : Fin r₁ => r₁ ≤ a.val) = ∅ := by
    ext a
    simp
  simp [hempty]

/-- The right side of (19f) of arXiv 2502.03008 without the source term, in terms of `v₀`. -/
noncomputable def momentExplicit [NeZero Nμ] (P : SuOlsonFixedData Nx Nμ) (B₀ : Fin Nx → ℝ)
    (X₀ : Matrix (Fin Nx) (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ)
    (V₀ : Matrix (Fin Nμ) (Fin r) ℝ) (j : Fin Nx) : ℝ :=
  1 / (1 + P.σ * P.Δt) * factorEntry X₀ S₀ V₀ j 0
    - P.Δt / (1 + P.σ * P.Δt) * ∑ i, ∑ ℓ, 1 / B₀ j * P.Dx j i * B₀ i *
        factorEntry X₀ S₀ V₀ i ℓ * P.A 0 ℓ
    + P.Δt / (1 + P.σ * P.Δt) * ∑ i, ∑ ℓ, 1 / B₀ j * P.Dxx j i * B₀ i *
        factorEntry X₀ S₀ V₀ i ℓ * P.absA 0 ℓ

/-- The closed form of the solution of the coupled system (19f), (19g). -/
private theorem coupled_solution {s τ R : ℝ} (hs : s * s = 2) (hτ : 0 ≤ τ)
    (hA : 0 < 1 + s * τ * R) {w : ℝ} (hw : w = (1 + s * τ * R) * (1 + τ) / (1 + 3 * τ)) :
    0 < w ∧ w = 1 + τ * w * (s * (R / w + s * τ / (1 + τ)) - 2) := by
  have hτ₁ : 0 < 1 + τ := by positivity
  have hτ₃ : 0 < 1 + 3 * τ := by positivity
  have hpos : 0 < w := by rw [hw]; positivity
  refine ⟨hpos, ?_⟩
  have h₁ : τ * w * (s * (R / w + s * τ / (1 + τ)) - 2) =
      s * τ * R + τ * w * (2 * τ / (1 + τ) - 2) := by
    have hc : s * (s * τ / (1 + τ)) = 2 * τ / (1 + τ) := by
      rw [← mul_div_assoc, ← mul_assoc, hs]
    rw [mul_add, hc]
    field_simp
    ring
  rw [h₁, hw]
  field_simp
  ring

/-- **The scheme of arXiv 2502.03008 is well posed** (not stated in the paper, needed for
non-vacuity): for all data with `4 r + 1 ≤ Nx, Nμ`, a step with target rank `r₁ ≤ 4 r` exists for
every tolerance above the discarded tail `ϑ₀`.  The condition `hsolv` says that (19f), (19g) have a
solution with `B¹ > 0`: their solution has `B¹ / B⁰ = (1 + √2 σ Δt R) (1 + σ Δt) / (1 + 3 σ Δt)`,
and this is positive at least for `σ = 0`, see the example below. -/
theorem exists_isSuOlsonDLRAStep [NeZero Nμ] (P : SuOlsonFixedData Nx Nμ) (B₀ : Fin Nx → ℝ)
    (X₀ : Matrix (Fin Nx) (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ)
    (V₀ : Matrix (Fin Nμ) (Fin r) ℝ) (hr₁ : r₁ ≤ r + r + r + r) (hΔt : 0 < P.Δt) (hσ : 0 ≤ P.σ)
    (hB : ∀ j, 0 < B₀ j) (hx : r + r + r + r + 1 ≤ Nx) (hμ : r + r + r + r + 1 ≤ Nμ)
    (hsolv : ∀ j, 0 < 1 + √2 * (P.σ * P.Δt) * momentExplicit P B₀ X₀ S₀ V₀ j) :
    ∃ (ϑ₀ : ℝ) (D : SuOlsonStepFactors Nx Nμ r r₁), (r₁ = r + r + r + r → ϑ₀ = 0) ∧
      (∀ ϑ, ϑ₀ ≤ ϑ → IsSuOlsonDLRAStep P B₀ X₀ S₀ V₀ ϑ hr₁ D) ∧ ∀ j, 0 < D.B₁ j := by
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hτ : 0 ≤ P.σ * P.Δt := by positivity
  have hcx : ∀ m, m ≤ Nx → m ≤ Fintype.card (Fin Nx) := fun m hm => by simpa using hm
  have hcμ : ∀ m, m ≤ Nμ → m ≤ Fintype.card (Fin Nμ) := fun m hm => by simpa using hm
  obtain ⟨Xh, RXh, h₁⟩ := exists_isGSQR (colAppend (massKStep P B₀ X₀ S₀ V₀) X₀) (hcx _ (by omega))
  obtain ⟨Xhh, RXhh, h₂⟩ := exists_isGSQR
    (colAppend (colAppend Xh (massWeightedStencil P.Dx B₀ X₀)) (massWeightedStencil P.Dxx B₀ X₀))
    (hcx _ (by omega))
  obtain ⟨Vh, RVh, h₃⟩ := exists_isGSQR (colAppend (massLStep P B₀ X₀ S₀ V₀) V₀) (hcμ _ (by omega))
  obtain ⟨Vhh, RVhh, h₄⟩ := exists_isGSQR
    (colAppend (colAppend Vh (P.Aᵀ * V₀)) (P.absAᵀ * V₀)) (hcμ _ (by omega))
  set R := momentExplicit P B₀ X₀ S₀ V₀ with hR
  let w : Fin Nx → ℝ := fun j =>
    (1 + √2 * (P.σ * P.Δt) * R j) * (1 + P.σ * P.Δt) / (1 + 3 * (P.σ * P.Δt))
  have hw : ∀ j, 0 < w j ∧ w j = 1 + P.σ * P.Δt * w j *
      (√2 * (R j / w j + √2 * (P.σ * P.Δt) / (1 + P.σ * P.Δt)) - 2) := fun j =>
    coupled_solution hs hτ (hsolv j) rfl
  let B₁ : Fin Nx → ℝ := fun j => B₀ j * w j
  let v₁ : Fin Nx → ℝ := fun j => R j / w j + √2 * (P.σ * P.Δt) / (1 + P.σ * P.Δt)
  have hratio : ∀ j, B₁ j / B₀ j = w j := fun j => by
    have := (hB j).ne'
    simp only [B₁]
    field_simp
  obtain ⟨Xtr, Str, h₅⟩ := exists_isGSQR
    (fun j p => B₀ j / B₁ j * (Xhh * massSStep P B₀ Xhh Vhh (massSTilde Xhh Vhh X₀ S₀ V₀)) j p)
    (hcx _ (by omega))
  obtain ⟨Xa, RXa, h₆⟩ := exists_isGSQR (colCons v₁ Xtr) (hcx _ hx)
  obtain ⟨Va, RVa, h₇⟩ := exists_isGSQR (colCons (Pi.single 0 1) Vhh) (hcμ _ hμ)
  obtain ⟨ϑ₀, T, hϑ₀, h₈⟩ :=
    exists_isConsTruncation hr₁ hx hμ Xa (massAdjustedS Xa Xtr Str Vhh v₁ Va) Va
  refine ⟨ϑ₀, ⟨Xh, RXh, Xhh, RXhh, Vh, RVh, Vhh, RVhh, B₁, v₁, Xtr, Str, Xa, RXa, Va, RVa, T⟩, hϑ₀,
    fun ϑ hϑ => ⟨h₁, h₂, h₃, h₄, ?_, ?_, h₅, h₆, h₇, h₈ ϑ hϑ⟩, fun j => mul_pos (hB j) (hw j).1⟩
  · intro j
    simp only [factorEntry_massSTilde h₁ h₂ h₃ h₄]
    rw [hratio j]
    have hne := (hw j).1.ne'
    have hRj : R j = 1 / (1 + P.σ * P.Δt) * factorEntry X₀ S₀ V₀ j 0
        - P.Δt / (1 + P.σ * P.Δt) * ∑ i, ∑ ℓ, 1 / B₀ j * P.Dx j i * B₀ i *
            factorEntry X₀ S₀ V₀ i ℓ * P.A 0 ℓ
        + P.Δt / (1 + P.σ * P.Δt) * ∑ i, ∑ ℓ, 1 / B₀ j * P.Dxx j i * B₀ i *
            factorEntry X₀ S₀ V₀ i ℓ * P.absA 0 ℓ := rfl
    rw [← hRj]
    simp only [v₁]
    field_simp
  · intro j
    change B₁ j / B₀ j = 1 + P.σ * P.Δt * (B₁ j / B₀ j) * (√2 * v₁ j - 2)
    rw [hratio j]
    exact (hw j).2

/-- Non-vacuity of `exists_isSuOlsonDLRAStep`, arXiv 2502.03008: for `σ = 0` the condition `hsolv`
holds for all data. -/
example [NeZero Nμ] (P : SuOlsonFixedData Nx Nμ) (B₀ : Fin Nx → ℝ)
    (X₀ : Matrix (Fin Nx) (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ)
    (V₀ : Matrix (Fin Nμ) (Fin r) ℝ) (hΔt : 0 < P.Δt) (hσ : P.σ = 0)
    (hB : ∀ j, 0 < B₀ j) (hx : r + r + r + r + 1 ≤ Nx) (hμ : r + r + r + r + 1 ≤ Nμ) :
    ∃ D : SuOlsonStepFactors Nx Nμ r (r + r + r + r),
      IsSuOlsonDLRAStep P B₀ X₀ S₀ V₀ 0 le_rfl D ∧ ∀ j, 0 < D.B₁ j := by
  obtain ⟨ϑ₀, D, h₀, hD, hpos⟩ := exists_isSuOlsonDLRAStep P B₀ X₀ S₀ V₀ le_rfl hΔt hσ.ge hB hx hμ
    (fun j => by simp [hσ])
  exact ⟨D, hD 0 (h₀ rfl).le, hpos⟩

end Scheme

end LeanDLRA.Literature.P2502_03008
