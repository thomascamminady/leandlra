import LeanDLRA.Integrators.BUG
import LeanDLRA.Literature.Kinetic.P2502_03008b
import LeanDLRA.Matrix.Projectors

/-!
# Local mass conservation of the energy-stable DLRA scheme for Su–Olson (arXiv 2307.07538)

Baumann, Einkemmer, Klingenberg, Kusch, *Energy stable and conservative dynamical low-rank
approximation for the Su-Olson problem*, version 2.  This module writes out the whole fully discrete
low-rank scheme of the paper as one predicate `IsConservativeStep`, not an abstract core of it:
the K- and L-steps (16a), (16b), the augmentations `X⋆ R = [K⋆, X⁰]`, `V⋆ R̃ = [L⋆, V⁰]`, the S-step
(16c), the implicitly coupled update (16d), (16e) of the zeroth moment and the internal energy, the
opacity update (16f), the augmentation (16g), the coefficient correction (16h) and the conservative
truncation of Section 6.  It proves Theorem 4 (`theorem_4`: the discrete local conservation laws
(24a), (24b) for the scalar flux `Φ_j = X_{jℓ} S_{ℓm} V_{0m}` and the energy `B_j`), its
consequence in divergence form (`theorem_4_divergence_form`), the conservation of the total mass
`m = Δx ∑_j (u_{j0} + B_j)` for the periodic stencils of the paper (`total_mass_conservation`), and
that the scheme is well posed (`exists_isConservativeStep`: all QR, SVD and implicit solves exist
for all data with `2 r + 1 ≤ Nx, Nμ` and `σ Δt ≥ 0`, for every target rank `r₁ ≤ 2 r`), so that
Theorem 4 is not vacuous.  QR factorizations, the truncation of Section 6 and the correction (16h)
are those of `P2502_03008b`, where the same algorithm is used for the multiplicative scheme:
`IsGSQR`, `IsConsTruncation` (with `IsConsTruncation.zeroth_moment`) and `massAdjustedS`.  The
abstract `consBug_euler_moment` of `Stability/Conservation.lean` is the analogue for an explicit
Euler step; it does not cover the implicit coupling of the zeroth moment to `B`, which is why the
proof here is carried out on the factors of the scheme itself.

## Differences from the paper

* `D^x`, `D^xx`, `A`, `|A|`, `σ`, `Δt` are arbitrary in `theorem_4`: the local laws use no property
  of them, so `A` need not be the Legendre matrix `⟨P_m, μ P_n⟩`.  `A_{0ℓ}` is the printed index
  order, also for non-symmetric `A`.  The periodic stencils of the paper are
  `periodicCentredStencil`, `periodicStabStencil`, and only the total mass needs them (their columns
  sum to zero, `sum_periodicCentredStencil`, `sum_periodicStabStencil`).  `X⁰`, `V⁰` need not be
  orthonormal.
* `qr` is taken with nonnegative diagonal of `R` (`IsGSQR`), and this convention is needed: step 5
  of Section 6 writes `e₁` instead of the first column of `Ṽ¹`, and that column is `+e₁` only with
  this convention (`IsGSQR.first_column`).  With `R₀₀ = -1` the truncated zeroth moment would be
  `-û¹₀`, and (24) would fail whenever `û¹₀ ≠ 0` (a hand computation, not formalized here).  QR
  factors may come from rank-deficient matrices.
* The left side of (16a) is printed `K⋆_{pk}` with `p` summed on the right; we read `K⋆_{qk}`.
* (16f) is printed `L^{⋆,scat}_{mk} = L_{mk} / (1 + Δt σ)` for `k ≠ 0` with `L = V⋆ S⋆`, while `m`
  is the moment index in (16b) and the factorization after (16f) reads
  `V^{⋆,scat} S^{⋆,scat,ᵀ} = L^{⋆,scat}`.  `IsConservativeStep` reads `L = V⋆ S⋆ᵀ` and scales the
  moments `m ≠ 0` (`opacityUpdate`), which is what the implicit absorption of the nonzero moments
  gives.  The reading does not matter: (16h) removes the zeroth row, and
  `IsConservativeCore.local_conservation` holds for an arbitrary `L^{⋆,scat}`, hence for every
  reading of (16f), and for arbitrary `K⋆`, `L⋆`.
* The S-step (16c) enters the conservation law only through `L^{⋆,scat}`, so it is not used in the
  proof, as in the paper.
* Step 4 of Section 6 chooses `r₁ ≤ 2 r` minimal with `(∑_{j > r₁} σ_j²)^{1/2} ≤ ϑ`.  Minimality is
  not assumed (`IsConsTruncation` only asks for the tolerance), so the theorem is stronger.  After
  truncation the factors have `r₁ + 1` columns: the `r₁` kept singular values and the conserved
  column.
* If the first column of `K̃` vanishes, step 2 of Section 6 divides by zero.  Lean's `x / 0 = 0`
  gives the sensible result, and the theorem covers this case.
* The widths are `r + r` and `r + r + 1` for the paper's `2 r` and `2 r + 1`.  The angular index
  `Fin Nμ` starts at `0` as in the paper, and `Pi.single 0 1` is the paper's `e₁`.
* The total mass is not a statement of the paper, which states the local law and reports the mass
  error numerically; `total_mass_conservation` is the sum of (24a), (24b) over the cells, without
  the source term of the Su–Olson test case.  The conservation is one-step; iterating it over many
  steps only adds bookkeeping for the changing rank.
* Not here: the energy stability results of the paper, which are the sibling slice `P2307_07538a`.

No claim of the paper was found to be false.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2307_07538

open LeanDLRA.Literature.P2502_03008 (ConsTruncData IsConsTruncation IsGSQR SuOlsonFixedData
  capture_colAppend_right capture_colCons colAppend colCons exists_isConsTruncation exists_isGSQR
  factorEntry factorEntry_eq massAdjustedS massSTilde)

/-! ### The scheme -/

section Scheme

variable {Nx Nμ r r₁ : ℕ}

/-- The K-step (16a) of arXiv 2307.07538, with `K⁰ = X⁰ S⁰`:
`K⋆_{qk} = K⁰_{qk} - Δt D^x_{qp} K⁰_{pj} V⁰_{nj} A_{mn} V⁰_{mk}`
`+ Δt D^xx_{qp} K⁰_{pj} V⁰_{nj} |A|_{mn} V⁰_{mk}`.  The paper prints `K⋆_{pk}` on the left. -/
noncomputable def conservativeKStep (P : SuOlsonFixedData Nx Nμ) (X₀ : Matrix (Fin Nx) (Fin r) ℝ)
    (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix (Fin Nμ) (Fin r) ℝ) :
    Matrix (Fin Nx) (Fin r) ℝ := fun q k =>
  (X₀ * S₀) q k
    - P.Δt * ∑ p, ∑ j, ∑ n, ∑ m, P.Dx q p * (X₀ * S₀) p j * V₀ n j * P.A m n * V₀ m k
    + P.Δt * ∑ p, ∑ j, ∑ n, ∑ m, P.Dxx q p * (X₀ * S₀) p j * V₀ n j * P.absA m n * V₀ m k

/-- The L-step (16b) of arXiv 2307.07538, with `L⁰ = V⁰ S⁰ᵀ`:
`L⋆_{mk} = L⁰_{mk} - Δt X⁰_{qk} D^x_{qp} X⁰_{pi} L⁰_{ni} A_{mn}`
`+ Δt X⁰_{qk} D^xx_{qp} X⁰_{pi} L⁰_{ni} |A|_{mn}`. -/
noncomputable def conservativeLStep (P : SuOlsonFixedData Nx Nμ) (X₀ : Matrix (Fin Nx) (Fin r) ℝ)
    (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix (Fin Nμ) (Fin r) ℝ) :
    Matrix (Fin Nμ) (Fin r) ℝ := fun m k =>
  (V₀ * S₀ᵀ) m k
    - P.Δt * ∑ q, ∑ p, ∑ i, ∑ n, X₀ q k * P.Dx q p * X₀ p i * (V₀ * S₀ᵀ) n i * P.A m n
    + P.Δt * ∑ q, ∑ p, ∑ i, ∑ n, X₀ q k * P.Dxx q p * X₀ p i * (V₀ * S₀ᵀ) n i * P.absA m n

/-- The S-step (16c) of arXiv 2307.07538, for `St = S̃⁰`:
`S⋆_{αβ} = S̃⁰_{αβ} - Δt X⋆_{pα} D^x_{pq} X⋆_{qi} S̃⁰_{ij} V⋆_{nj} A_{mn} V⋆_{mβ}`
`+ Δt X⋆_{pα} D^xx_{pq} X⋆_{qi} S̃⁰_{ij} V⋆_{nj} |A|_{mn} V⋆_{mβ}`. -/
noncomputable def conservativeSStep {w : ℕ} (P : SuOlsonFixedData Nx Nμ)
    (Xs : Matrix (Fin Nx) (Fin w) ℝ) (Vs : Matrix (Fin Nμ) (Fin w) ℝ)
    (St : Matrix (Fin w) (Fin w) ℝ) : Matrix (Fin w) (Fin w) ℝ := fun α β =>
  St α β
    - P.Δt * ∑ p, ∑ q, ∑ i, ∑ j, ∑ n, ∑ m,
        Xs p α * P.Dx p q * Xs q i * St i j * Vs n j * P.A m n * Vs m β
    + P.Δt * ∑ p, ∑ q, ∑ i, ∑ j, ∑ n, ∑ m,
        Xs p α * P.Dxx p q * Xs q i * St i j * Vs n j * P.absA m n * Vs m β

/-- The opacity update (16f) of arXiv 2307.07538, in the reading explained in the module docstring:
the nonzero moments of `L = V⋆ S⋆ᵀ` are divided by `1 + Δt σ`.  The zeroth row stays as it is;
(16h) removes it in any case. -/
noncomputable def opacityUpdate [NeZero Nμ] {w : ℕ} (P : SuOlsonFixedData Nx Nμ)
    (L : Matrix (Fin Nμ) (Fin w) ℝ) : Matrix (Fin Nμ) (Fin w) ℝ := fun m k =>
  if m = 0 then L m k else 1 / (1 + P.Δt * P.σ) * L m k

/-- The factors computed in one step (16a)–(16h) of the scheme of arXiv 2307.07538, followed by the
conservative truncation of its Section 6. -/
structure ConservativeStepFactors (Nx Nμ r r₁ : ℕ) where
  /-- `X⋆`. -/
  Xs : Matrix (Fin Nx) (Fin (r + r)) ℝ
  /-- The triangular factor `R` of `X⋆`. -/
  RX : Matrix (Fin (r + r)) (Fin (r + r)) ℝ
  /-- `V⋆`. -/
  Vs : Matrix (Fin Nμ) (Fin (r + r)) ℝ
  /-- The triangular factor `R̃` of `V⋆`. -/
  RV : Matrix (Fin (r + r)) (Fin (r + r)) ℝ
  /-- The new zeroth moment `û¹₀`. -/
  u₁ : Fin Nx → ℝ
  /-- The new internal energy `B¹`. -/
  B₁ : Fin Nx → ℝ
  /-- `V^{⋆,scat}`. -/
  Vsc : Matrix (Fin Nμ) (Fin (r + r)) ℝ
  /-- `S^{⋆,scat}`. -/
  Ssc : Matrix (Fin (r + r)) (Fin (r + r)) ℝ
  /-- `X̃¹`. -/
  Xa : Matrix (Fin Nx) (Fin (r + r + 1)) ℝ
  /-- The triangular factor of `X̃¹`. -/
  RXa : Matrix (Fin (r + r + 1)) (Fin (r + r + 1)) ℝ
  /-- `Ṽ¹`. -/
  Va : Matrix (Fin Nμ) (Fin (r + r + 1)) ℝ
  /-- The triangular factor of `Ṽ¹`. -/
  RVa : Matrix (Fin (r + r + 1)) (Fin (r + r + 1)) ℝ
  /-- The conservative truncation, with the new factors `X¹`, `S¹`, `V¹`. -/
  trunc : ConsTruncData Nx Nμ (r + r) r₁

/-- The scheme (16) of arXiv 2307.07538 with the truncation of its Section 6, where the matrices
`Kst = K⋆` of (16a), `Lst = L⋆` of (16b) and `Lsc = L^{⋆,scat}` of (16f) are left arbitrary. -/
structure IsConservativeCore [NeZero Nμ] (P : SuOlsonFixedData Nx Nμ) (B₀ : Fin Nx → ℝ)
    (X₀ : Matrix (Fin Nx) (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ)
    (V₀ : Matrix (Fin Nμ) (Fin r) ℝ) (ϑ : ℝ) (hr₁ : r₁ ≤ r + r)
    (Kst : Matrix (Fin Nx) (Fin r) ℝ) (Lst : Matrix (Fin Nμ) (Fin r) ℝ)
    (Lsc : Matrix (Fin Nμ) (Fin (r + r)) ℝ) (D : ConservativeStepFactors Nx Nμ r r₁) : Prop where
  /-- The augmentation `X⋆ R = [K⋆, X⁰]`. -/
  qr_k : IsGSQR (colAppend Kst X₀) D.Xs D.RX
  /-- The augmentation `V⋆ R̃ = [L⋆, V⁰]`. -/
  qr_l : IsGSQR (colAppend Lst V₀) D.Vs D.RV
  /-- (16d), where `S̃⁰ = X⋆ᵀ X⁰ S⁰ V⁰ᵀ V⋆`. -/
  moment_eq : ∀ j, D.u₁ j = factorEntry X₀ S₀ V₀ j 0
    - P.Δt * ∑ i, ∑ ℓ, P.Dx j i *
        factorEntry D.Xs (massSTilde D.Xs D.Vs X₀ S₀ V₀) D.Vs i ℓ * P.A 0 ℓ
    + P.Δt * ∑ i, ∑ ℓ, P.Dxx j i *
        factorEntry D.Xs (massSTilde D.Xs D.Vs X₀ S₀ V₀) D.Vs i ℓ * P.absA 0 ℓ
    + P.σ * P.Δt * (D.B₁ j - D.u₁ j)
  /-- (16e). -/
  energy_eq : ∀ j, D.B₁ j = B₀ j + P.σ * P.Δt * (D.u₁ j - D.B₁ j)
  /-- The QR step after (16f): `V^{⋆,scat} S^{⋆,scat,ᵀ} = L^{⋆,scat}`. -/
  qr_scat : IsGSQR Lsc D.Vsc D.Sscᵀ
  /-- (16g), space. -/
  qr_xa : IsGSQR (colCons D.u₁ D.Xs) D.Xa D.RXa
  /-- (16g), direction. -/
  qr_va : IsGSQR (colCons (Pi.single 0 1) D.Vsc) D.Va D.RVa
  /-- Section 6 applied to `S̃¹` of (16h), which is `massAdjustedS`. -/
  trunc : IsConsTruncation hr₁ ϑ D.Xa (massAdjustedS D.Xa D.Xs D.Ssc D.Vsc D.u₁ D.Va) D.Va D.trunc

/-- **One step of the scheme of arXiv 2307.07538**, (16a)–(16h) with the conservative truncation of
Section 6, from `(B⁰, X⁰ S⁰ V⁰ᵀ)` to `(D.B₁, D.trunc.X₁ D.trunc.S₁ D.trunc.V₁ᵀ)`, with target rank
`r₁ ≤ 2 r` and tolerance `ϑ`. -/
def IsConservativeStep [NeZero Nμ] (P : SuOlsonFixedData Nx Nμ) (B₀ : Fin Nx → ℝ)
    (X₀ : Matrix (Fin Nx) (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ)
    (V₀ : Matrix (Fin Nμ) (Fin r) ℝ) (ϑ : ℝ) (hr₁ : r₁ ≤ r + r)
    (D : ConservativeStepFactors Nx Nμ r r₁) : Prop :=
  IsConservativeCore P B₀ X₀ S₀ V₀ ϑ hr₁ (conservativeKStep P X₀ S₀ V₀)
    (conservativeLStep P X₀ S₀ V₀)
    (opacityUpdate P
      (D.Vs * (conservativeSStep P D.Xs D.Vs (massSTilde D.Xs D.Vs X₀ S₀ V₀))ᵀ)) D

/-! ### The zeroth moment -/

/-- arXiv 2307.07538, proof of Theorem 4: since `X⋆` and `V⋆` contain `X⁰` and `V⁰`, we have
`X⋆_{in} S̃⁰_{nm} V⋆_{ℓm} = u⁰_{iℓ}`.  This is derived from the QR steps, for arbitrary `K⋆`,
`L⋆`. -/
theorem factorEntry_sTilde {k : ℕ} {X₀ : Matrix (Fin Nx) (Fin r) ℝ}
    {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix (Fin Nμ) (Fin r) ℝ}
    {Kst : Matrix (Fin Nx) (Fin k) ℝ} {Lst : Matrix (Fin Nμ) (Fin k) ℝ}
    {Xs : Matrix (Fin Nx) (Fin (k + r)) ℝ} {RX : Matrix (Fin (k + r)) (Fin (k + r)) ℝ}
    {Vs : Matrix (Fin Nμ) (Fin (k + r)) ℝ} {RV : Matrix (Fin (k + r)) (Fin (k + r)) ℝ}
    (hK : IsGSQR (colAppend Kst X₀) Xs RX) (hL : IsGSQR (colAppend Lst V₀) Vs RV)
    (i : Fin Nx) (ℓ : Fin Nμ) :
    factorEntry Xs (massSTilde Xs Vs X₀ S₀ V₀) Vs i ℓ = factorEntry X₀ S₀ V₀ i ℓ := by
  have hX₀ : Xs * Xsᵀ * X₀ = X₀ := capture_colAppend_right hK.capture
  have hV₀ : Vs * Vsᵀ * V₀ = V₀ := capture_colAppend_right hL.capture
  have hprod : Xs * massSTilde Xs Vs X₀ S₀ V₀ * Vsᵀ = X₀ * S₀ * V₀ᵀ := by
    conv_rhs => rw [← hX₀]
    nth_rw 2 [← hV₀]
    simp only [massSTilde, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [factorEntry_eq, factorEntry_eq, hprod]

/-- arXiv 2307.07538, proof of Theorem 4: `Φ¹_j = û¹_{j0}`, the zeroth moment of the new low-rank
factors is the solution of (16d), (16e).  This is derived from (16g), (16h) and Section 6, and holds
for arbitrary `L^{⋆,scat}`. -/
theorem IsConservativeCore.moment_new [NeZero Nμ] {P : SuOlsonFixedData Nx Nμ} {B₀ : Fin Nx → ℝ}
    {X₀ : Matrix (Fin Nx) (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ}
    {V₀ : Matrix (Fin Nμ) (Fin r) ℝ} {ϑ : ℝ} {hr₁ : r₁ ≤ r + r}
    {Kst : Matrix (Fin Nx) (Fin r) ℝ} {Lst : Matrix (Fin Nμ) (Fin r) ℝ}
    {Lsc : Matrix (Fin Nμ) (Fin (r + r)) ℝ} {D : ConservativeStepFactors Nx Nμ r r₁}
    (h : IsConservativeCore P B₀ X₀ S₀ V₀ ϑ hr₁ Kst Lst Lsc D) (j : Fin Nx) :
    factorEntry D.trunc.X₁ D.trunc.S₁ D.trunc.V₁ j 0 = D.u₁ j := by
  obtain ⟨hfirst, hrow⟩ := h.qr_va.first_column
  rw [h.trunc.zeroth_moment hrow j]
  set e : Fin Nμ → ℝ := Pi.single 0 1 with he
  have hee : e ⬝ᵥ e = 1 := by simp [he]
  have hcol : ∀ (M : Matrix (Fin (r + r + 1)) (Fin Nμ) ℝ) a,
      (M * D.Va) a 0 = (M *ᵥ e) a := by
    intro M a
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, hfirst]
  have hproj : (1 - Matrix.vecMulVec e e) *ᵥ e = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, hee]
    simp
  have hvv : Matrix.vecMulVec D.u₁ e *ᵥ e = D.u₁ := by
    rw [Matrix.vecMulVec_mulVec, hee]
    simp
  have hS : ∀ a, massAdjustedS D.Xa D.Xs D.Ssc D.Vsc D.u₁ D.Va a 0 = (D.Xaᵀ *ᵥ D.u₁) a := by
    intro a
    have h₁ : ∀ T : Matrix (Fin (r + r + 1)) (Fin Nμ) ℝ,
        (T * (1 - Matrix.vecMulVec e e)) *ᵥ e = 0 := fun T => by
      rw [← Matrix.mulVec_mulVec, hproj, Matrix.mulVec_zero]
    have h₂ : (D.Xaᵀ * Matrix.vecMulVec D.u₁ e) *ᵥ e = D.Xaᵀ *ᵥ D.u₁ := by
      rw [← Matrix.mulVec_mulVec, hvv]
    rw [massAdjustedS, Matrix.add_apply, hcol, hcol, h₁, h₂]
    simp
  have hcap := capture_colCons h.qr_xa.capture j
  rw [← hcap, Matrix.mul_apply]
  simp only [hS, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => by ring

/-! ### Theorem 4 -/

/-- arXiv 2307.07538, Theorem 4, for arbitrary `K⋆`, `L⋆`, `L^{⋆,scat}`: the local laws (24a), (24b)
do not use (16a), (16b), (16c), (16f), so they hold for every reading of the misprinted (16f). -/
theorem IsConservativeCore.local_conservation [NeZero Nμ] {P : SuOlsonFixedData Nx Nμ}
    {B₀ : Fin Nx → ℝ} {X₀ : Matrix (Fin Nx) (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ}
    {V₀ : Matrix (Fin Nμ) (Fin r) ℝ} {ϑ : ℝ} {hr₁ : r₁ ≤ r + r}
    {Kst : Matrix (Fin Nx) (Fin r) ℝ} {Lst : Matrix (Fin Nμ) (Fin r) ℝ}
    {Lsc : Matrix (Fin Nμ) (Fin (r + r)) ℝ} {D : ConservativeStepFactors Nx Nμ r r₁}
    (h : IsConservativeCore P B₀ X₀ S₀ V₀ ϑ hr₁ Kst Lst Lsc D) (j : Fin Nx) :
    factorEntry D.trunc.X₁ D.trunc.S₁ D.trunc.V₁ j 0 = factorEntry X₀ S₀ V₀ j 0
        - P.Δt * ∑ i, ∑ ℓ, P.Dx j i * factorEntry X₀ S₀ V₀ i ℓ * P.A 0 ℓ
        + P.Δt * ∑ i, ∑ ℓ, P.Dxx j i * factorEntry X₀ S₀ V₀ i ℓ * P.absA 0 ℓ
        + P.σ * P.Δt * (D.B₁ j - factorEntry D.trunc.X₁ D.trunc.S₁ D.trunc.V₁ j 0) ∧
      D.B₁ j = B₀ j + P.σ * P.Δt *
        (factorEntry D.trunc.X₁ D.trunc.S₁ D.trunc.V₁ j 0 - D.B₁ j) := by
  have hm := h.moment_eq j
  simp only [factorEntry_sTilde h.qr_k h.qr_l] at hm
  rw [h.moment_new j]
  exact ⟨hm, h.energy_eq j⟩

/-- **Theorem 4 of arXiv 2307.07538 (local mass conservation).**  One step of the scheme (16) with
the conservative truncation of Section 6 satisfies, with `u⁰ = X⁰ S⁰ V⁰ᵀ` and the scalar flux
`Φⁿ_j = Xⁿ_{jℓ} Sⁿ_{ℓm} Vⁿ_{0m}`, in every cell `j`, the laws
`(24a) Φ¹_j = Φ⁰_j - Δt D^x_{ji} u⁰_{iℓ} A_{0ℓ} + Δt D^xx_{ji} u⁰_{iℓ} |A|_{0ℓ}`
`+ σ Δt (B¹_j - Φ¹_j)`,
`(24b) B¹_j = B⁰_j + σ Δt (Φ¹_j - B¹_j)`.
`D^x`, `D^xx`, `A`, `|A|`, `σ`, `Δt` may be arbitrary, and `qr` is taken with nonnegative diagonal
of `R`, which the theorem needs (see the module docstring).  The conclusion is the paper's: the
hypothesis only says that `D` is one step of the scheme, and everything used in the proof (that the
augmented bases reproduce `u⁰`, that `Ṽ¹` starts with `e₁`, that (16h) and the truncation keep
the first column) is derived from the QR steps.  See `exists_isConservativeStep` for non-vacuity. -/
theorem theorem_4 [NeZero Nμ] {P : SuOlsonFixedData Nx Nμ} {B₀ : Fin Nx → ℝ}
    {X₀ : Matrix (Fin Nx) (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ}
    {V₀ : Matrix (Fin Nμ) (Fin r) ℝ} {ϑ : ℝ} {hr₁ : r₁ ≤ r + r}
    {D : ConservativeStepFactors Nx Nμ r r₁} (h : IsConservativeStep P B₀ X₀ S₀ V₀ ϑ hr₁ D)
    (j : Fin Nx) :
    factorEntry D.trunc.X₁ D.trunc.S₁ D.trunc.V₁ j 0 = factorEntry X₀ S₀ V₀ j 0
        - P.Δt * ∑ i, ∑ ℓ, P.Dx j i * factorEntry X₀ S₀ V₀ i ℓ * P.A 0 ℓ
        + P.Δt * ∑ i, ∑ ℓ, P.Dxx j i * factorEntry X₀ S₀ V₀ i ℓ * P.absA 0 ℓ
        + P.σ * P.Δt * (D.B₁ j - factorEntry D.trunc.X₁ D.trunc.S₁ D.trunc.V₁ j 0) ∧
      D.B₁ j = B₀ j + P.σ * P.Δt *
        (factorEntry D.trunc.X₁ D.trunc.S₁ D.trunc.V₁ j 0 - D.B₁ j) :=
  IsConservativeCore.local_conservation h j

/-- arXiv 2307.07538, Theorem 4 in divergence form: adding (24a) and (24b) cancels the absorption
terms, so the change of `Φ_j + B_j` in a cell is exactly the discrete flux of `u⁰`.  This is the
reason why (24) is called a conservation law. -/
theorem theorem_4_divergence_form [NeZero Nμ] {P : SuOlsonFixedData Nx Nμ} {B₀ : Fin Nx → ℝ}
    {X₀ : Matrix (Fin Nx) (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ}
    {V₀ : Matrix (Fin Nμ) (Fin r) ℝ} {ϑ : ℝ} {hr₁ : r₁ ≤ r + r}
    {D : ConservativeStepFactors Nx Nμ r r₁} (h : IsConservativeStep P B₀ X₀ S₀ V₀ ϑ hr₁ D)
    (j : Fin Nx) :
    (factorEntry D.trunc.X₁ D.trunc.S₁ D.trunc.V₁ j 0 + D.B₁ j)
        - (factorEntry X₀ S₀ V₀ j 0 + B₀ j) =
      - P.Δt * ∑ i, ∑ ℓ, P.Dx j i * factorEntry X₀ S₀ V₀ i ℓ * P.A 0 ℓ
        + P.Δt * ∑ i, ∑ ℓ, P.Dxx j i * factorEntry X₀ S₀ V₀ i ℓ * P.absA 0 ℓ := by
  obtain ⟨h₁, h₂⟩ := theorem_4 h j
  linear_combination h₁ + h₂

/-! ### Periodic stencils and total mass -/

/-- The periodic centred stencil `D^x` of arXiv 2307.07538 on `Nx` cells of width `Δx`:
`D^x_{p,p±1} = ±1 / (2 Δx)`, indices modulo `Nx`.  The two contributions are added, which only
matters for `Nx ≤ 2`, where `p + 1 = p - 1`. -/
noncomputable def periodicCentredStencil (Nx : ℕ) [NeZero Nx] (Δx : ℝ) :
    Matrix (Fin Nx) (Fin Nx) ℝ := fun p q =>
  (if q = p + 1 then 1 / (2 * Δx) else 0) - (if q = p - 1 then 1 / (2 * Δx) else 0)

/-- The periodic stabilisation stencil `D^xx` of arXiv 2307.07538 on `Nx` cells of width `Δx`:
`D^xx_{p,p} = -1 / Δx`, `D^xx_{p,p±1} = 1 / (2 Δx)`, indices modulo `Nx`. -/
noncomputable def periodicStabStencil (Nx : ℕ) [NeZero Nx] (Δx : ℝ) :
    Matrix (Fin Nx) (Fin Nx) ℝ := fun p q =>
  (if q = p then -(1 / Δx) else 0) + (if q = p + 1 then 1 / (2 * Δx) else 0)
    + (if q = p - 1 then 1 / (2 * Δx) else 0)

/-- Each cell has exactly one left neighbour on the periodic grid of arXiv 2307.07538. -/
private theorem sum_ite_succ [NeZero Nx] (i : Fin Nx) (c : ℝ) :
    ∑ j : Fin Nx, (if i = j + 1 then c else 0) = c := by
  have h : ∀ j : Fin Nx, (i = j + 1) ↔ (j = i - 1) := fun j => by
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Each cell has exactly one right neighbour on the periodic grid of arXiv 2307.07538. -/
private theorem sum_ite_pred [NeZero Nx] (i : Fin Nx) (c : ℝ) :
    ∑ j : Fin Nx, (if i = j - 1 then c else 0) = c := by
  have h : ∀ j : Fin Nx, (i = j - 1) ↔ (j = i + 1) := fun j => by
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The columns of the periodic `D^x` of arXiv 2307.07538 sum to zero. -/
theorem sum_periodicCentredStencil [NeZero Nx] (Δx : ℝ) (i : Fin Nx) :
    ∑ j, periodicCentredStencil Nx Δx j i = 0 := by
  simp only [periodicCentredStencil, Finset.sum_sub_distrib, sum_ite_succ, sum_ite_pred, sub_self]

/-- The columns of the periodic `D^xx` of arXiv 2307.07538 sum to zero. -/
theorem sum_periodicStabStencil [NeZero Nx] (Δx : ℝ) (i : Fin Nx) :
    ∑ j, periodicStabStencil Nx Δx j i = 0 := by
  simp only [periodicStabStencil, Finset.sum_add_distrib, sum_ite_succ, sum_ite_pred]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-- The total mass `mⁿ = Δx ∑_j (uⁿ_{j0} + Bⁿ_j)` of the numerical section of arXiv 2307.07538. -/
noncomputable def conservativeMass [NeZero Nμ] {a b : ℕ} (Δx : ℝ) (B : Fin Nx → ℝ)
    (X : Matrix (Fin Nx) (Fin a) ℝ) (S : Matrix (Fin a) (Fin b) ℝ)
    (V : Matrix (Fin Nμ) (Fin b) ℝ) : ℝ :=
  Δx * ∑ j, (factorEntry X S V j 0 + B j)

/-- Stencils with vanishing column sums give a telescoping flux (arXiv 2307.07538, Theorem 4). -/
private theorem sum_flux_eq_zero {D : Matrix (Fin Nx) (Fin Nx) ℝ} (hD : ∀ i, ∑ j, D j i = 0)
    (v : Fin Nx → Fin Nμ → ℝ) (c : Fin Nμ → ℝ) :
    ∑ j, ∑ i, ∑ ℓ, D j i * v i ℓ * c ℓ = 0 := by
  have h : ∀ j i, ∑ ℓ, D j i * v i ℓ * c ℓ = D j i * ∑ ℓ, v i ℓ * c ℓ := fun j i => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ℓ _ => by ring
  simp only [h]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, hD, zero_mul, Finset.sum_const_zero]

/-- **Total mass conservation** (arXiv 2307.07538, Theorem 4 summed over the cells; the paper states
the local law and observes the total mass numerically): for stencils whose columns sum to zero and
without a source, one step of the scheme conserves `m = Δx ∑_j (u_{j0} + B_j)`. -/
theorem total_mass_conservation_of_sum_eq_zero [NeZero Nμ] {P : SuOlsonFixedData Nx Nμ}
    {B₀ : Fin Nx → ℝ} {X₀ : Matrix (Fin Nx) (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ}
    {V₀ : Matrix (Fin Nμ) (Fin r) ℝ} {ϑ : ℝ} {hr₁ : r₁ ≤ r + r}
    {D : ConservativeStepFactors Nx Nμ r r₁} (h : IsConservativeStep P B₀ X₀ S₀ V₀ ϑ hr₁ D)
    (hDx : ∀ i, ∑ j, P.Dx j i = 0) (hDxx : ∀ i, ∑ j, P.Dxx j i = 0) (Δx : ℝ) :
    conservativeMass Δx D.B₁ D.trunc.X₁ D.trunc.S₁ D.trunc.V₁ =
      conservativeMass Δx B₀ X₀ S₀ V₀ := by
  have hsum : ∑ j, ((factorEntry D.trunc.X₁ D.trunc.S₁ D.trunc.V₁ j 0 + D.B₁ j)
      - (factorEntry X₀ S₀ V₀ j 0 + B₀ j)) = 0 := by
    simp only [theorem_4_divergence_form h]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      sum_flux_eq_zero hDx (factorEntry X₀ S₀ V₀) (P.A 0),
      sum_flux_eq_zero hDxx (factorEntry X₀ S₀ V₀) (P.absA 0)]
    simp
  rw [Finset.sum_sub_distrib] at hsum
  rw [conservativeMass, conservativeMass, sub_eq_zero.mp hsum]

/-- **Total mass conservation for the periodic stencils of arXiv 2307.07538** (Theorem 4 summed over
the cells, without source): `m¹ = m⁰` for `m = Δx ∑_j (u_{j0} + B_j)`. -/
theorem total_mass_conservation [NeZero Nx] [NeZero Nμ] {P : SuOlsonFixedData Nx Nμ}
    {B₀ : Fin Nx → ℝ} {X₀ : Matrix (Fin Nx) (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ}
    {V₀ : Matrix (Fin Nμ) (Fin r) ℝ} {ϑ : ℝ} {hr₁ : r₁ ≤ r + r}
    {D : ConservativeStepFactors Nx Nμ r r₁} (h : IsConservativeStep P B₀ X₀ S₀ V₀ ϑ hr₁ D)
    {Δx : ℝ} (hDx : P.Dx = periodicCentredStencil Nx Δx)
    (hDxx : P.Dxx = periodicStabStencil Nx Δx) :
    conservativeMass Δx D.B₁ D.trunc.X₁ D.trunc.S₁ D.trunc.V₁ =
      conservativeMass Δx B₀ X₀ S₀ V₀ :=
  total_mass_conservation_of_sum_eq_zero h
    (by rw [hDx]; exact sum_periodicCentredStencil Δx)
    (by rw [hDxx]; exact sum_periodicStabStencil Δx) Δx

/-! ### Well-posedness -/

/-- The part of (16d) of arXiv 2307.07538 that is known before the implicit solve. -/
noncomputable def explicitMoment [NeZero Nμ] (P : SuOlsonFixedData Nx Nμ)
    (X₀ : Matrix (Fin Nx) (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ)
    (V₀ : Matrix (Fin Nμ) (Fin r) ℝ) (j : Fin Nx) : ℝ :=
  factorEntry X₀ S₀ V₀ j 0
    - P.Δt * ∑ i, ∑ ℓ, P.Dx j i * factorEntry X₀ S₀ V₀ i ℓ * P.A 0 ℓ
    + P.Δt * ∑ i, ∑ ℓ, P.Dxx j i * factorEntry X₀ S₀ V₀ i ℓ * P.absA 0 ℓ

/-- The implicit solve (16d), (16e) of arXiv 2307.07538 in one cell: for `τ = σ Δt ≥ 0` the system
`u = R + τ (B - u)`, `B = b + τ (u - B)` has the solution below, its determinant being `1 + 2 τ`. -/
private theorem implicit_solution {τ R b : ℝ} (hτ : 0 ≤ τ) :
    let u := ((1 + τ) * R + τ * b) / (1 + 2 * τ)
    let B := (τ * R + (1 + τ) * b) / (1 + 2 * τ)
    u = R + τ * (B - u) ∧ B = b + τ * (u - B) := by
  have h : 1 + 2 * τ ≠ 0 := by positivity
  intro u B
  constructor <;> simp only [u, B] <;> field_simp <;> ring

/-- **The scheme of arXiv 2307.07538 is well posed** (not stated in the paper, needed for
non-vacuity): for all data with `2 r + 1 ≤ Nx, Nμ` and `σ Δt ≥ 0`, a step with any target rank
`r₁ ≤ 2 r` exists for every tolerance above the discarded tail `ϑ₀`, and `ϑ₀ = 0` when nothing is
discarded.  No assumption on `D^x`, `D^xx`, `A`, `|A|`, `X⁰`, `S⁰`, `V⁰`, `B⁰` is needed; the
implicit system (16d), (16e) has determinant `1 + 2 σ Δt`. -/
theorem exists_isConservativeStep [NeZero Nμ] (P : SuOlsonFixedData Nx Nμ) (B₀ : Fin Nx → ℝ)
    (X₀ : Matrix (Fin Nx) (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ)
    (V₀ : Matrix (Fin Nμ) (Fin r) ℝ) (hr₁ : r₁ ≤ r + r) (hτ : 0 ≤ P.σ * P.Δt)
    (hx : r + r + 1 ≤ Nx) (hμ : r + r + 1 ≤ Nμ) :
    ∃ (ϑ₀ : ℝ) (D : ConservativeStepFactors Nx Nμ r r₁), (r₁ = r + r → ϑ₀ = 0) ∧
      ∀ ϑ, ϑ₀ ≤ ϑ → IsConservativeStep P B₀ X₀ S₀ V₀ ϑ hr₁ D := by
  have hcx : ∀ m, m ≤ Nx → m ≤ Fintype.card (Fin Nx) := fun m hm => by simpa using hm
  have hcμ : ∀ m, m ≤ Nμ → m ≤ Fintype.card (Fin Nμ) := fun m hm => by simpa using hm
  obtain ⟨Xs, RX, h₁⟩ := exists_isGSQR (colAppend (conservativeKStep P X₀ S₀ V₀) X₀)
    (hcx _ (by omega))
  obtain ⟨Vs, RV, h₂⟩ := exists_isGSQR (colAppend (conservativeLStep P X₀ S₀ V₀) V₀)
    (hcμ _ (by omega))
  set τ := P.σ * P.Δt with hτdef
  set R := explicitMoment P X₀ S₀ V₀ with hR
  let u₁ : Fin Nx → ℝ := fun j => ((1 + τ) * R j + τ * B₀ j) / (1 + 2 * τ)
  let B₁ : Fin Nx → ℝ := fun j => (τ * R j + (1 + τ) * B₀ j) / (1 + 2 * τ)
  have hsolve : ∀ j, u₁ j = R j + τ * (B₁ j - u₁ j) ∧ B₁ j = B₀ j + τ * (u₁ j - B₁ j) :=
    fun j => implicit_solution hτ
  obtain ⟨Vsc, Rsc, h₃⟩ := exists_isGSQR
    (opacityUpdate P (Vs * (conservativeSStep P Xs Vs (massSTilde Xs Vs X₀ S₀ V₀))ᵀ))
    (hcμ _ (by omega))
  obtain ⟨Xa, RXa, h₄⟩ := exists_isGSQR (colCons u₁ Xs) (hcx _ hx)
  obtain ⟨Va, RVa, h₅⟩ := exists_isGSQR (colCons (Pi.single 0 1) Vsc) (hcμ _ hμ)
  obtain ⟨ϑ₀, T, hϑ₀, h₆⟩ := exists_isConsTruncation hr₁ hx hμ Xa
    (massAdjustedS Xa Xs Rscᵀ Vsc u₁ Va) Va
  refine ⟨ϑ₀, ⟨Xs, RX, Vs, RV, u₁, B₁, Vsc, Rscᵀ, Xa, RXa, Va, RVa, T⟩, hϑ₀, fun ϑ hϑ =>
    ⟨h₁, h₂, ?_, fun j => (hsolve j).2, ?_, h₄, h₅, h₆ ϑ hϑ⟩⟩
  · intro j
    simp only [factorEntry_sTilde h₁ h₂]
    exact (hsolve j).1
  · simpa using h₃

/-- Non-vacuity of arXiv 2307.07538, Theorem 4: without truncation (`r₁ = 2 r`, `ϑ = 0`) the
hypothesis of `theorem_4` holds for all data, whatever the stencils, as soon as the factors fit. -/
example [NeZero Nμ] (P : SuOlsonFixedData Nx Nμ) (B₀ : Fin Nx → ℝ)
    (X₀ : Matrix (Fin Nx) (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ)
    (V₀ : Matrix (Fin Nμ) (Fin r) ℝ) (hτ : 0 ≤ P.σ * P.Δt) (hx : r + r + 1 ≤ Nx)
    (hμ : r + r + 1 ≤ Nμ) :
    ∃ D : ConservativeStepFactors Nx Nμ r (r + r),
      IsConservativeStep P B₀ X₀ S₀ V₀ 0 le_rfl D := by
  obtain ⟨ϑ₀, D, h₀, hD⟩ := exists_isConservativeStep P B₀ X₀ S₀ V₀ le_rfl hτ hx hμ
  exact ⟨D, hD 0 (h₀ rfl).le⟩

end Scheme

end LeanDLRA.Literature.P2307_07538
