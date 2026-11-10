import LeanDLRA.OpenProblems.TensorNetworks.Part2Defs
import LeanDLRA.Tensor.TT.TangentProjector
import LeanDLRA.Integrators.TuckerBUG
import LeanDLRA.Integrators.Exactness
import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.Matrix.LowRankDistance
import LeanDLRA.Stability.Energy
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Open problems OP-TN-10, OP-TN-11, OP-TN-12, OP-TN-15
-/

open Set Finset
open scoped RealInnerProductSpace

universe u

namespace LeanDLRA.OpenProblems.TensorNetworks

open LeanDLRA

section Training

open scoped Matrix LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n]

end Training

section TrainingAbstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end TrainingAbstract

section Transfer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F : ℝ → E → E} {ε t₀ t₁ : ℝ} {d : ℕ}

end Transfer

section RankAdaptive

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- OP-TN-10 (i) (source: arXiv 2104.05247, §4.2), exactness of the rank-adaptive Tucker BUG
integrator including truncation.  If `F = Ȧ`, `A(t₀) = Y₀` is fixed by the `K`-step projectors,
`A(t₁)` is recoverable from every mode-`i` `K`-step projection, and the truncation is by mode
projectors `R i` that are best approximations from sets `Mᵢ ∋ A(t₁)` (tensors of mode-`i` rank
`≤ rᵢ`), then the truncated result equals `A(t₁)`. -/
theorem aug_tucker_exact_trunc {d : ℕ} {F : ℝ → E → E} {A : ℝ → E} {ε t₀ t₁ : ℝ}
    (ht : t₀ ≤ t₁) (hA : IsDerivRHS F A t₀ t₁) {Q₀ P₁ : Fin d → E →L[ℝ] E}
    {YK : Fin d → ℝ → E} {YS : ℝ → E} (hs : IsAugTuckerBUGStep F ε Q₀ P₁ t₀ t₁ (A t₀) YK YS)
    (hQ : ∀ i, Q₀ i (A t₀) = A t₀) {𝓛 : Fin d → Set (E →L[ℝ] E)} (h𝓛 : ∀ i, P₁ i ∈ 𝓛 i)
    (hrec : ∀ i, Exactness.IsRecoverable (𝓛 i) (Q₀ i) (A t₁)) {R : Fin d → E →L[ℝ] E}
    (hR : ∀ i, IsOrthProj (R i)) {Mi : Fin d → Set E} (hAM : ∀ i, A t₁ ∈ Mi i)
    (hopt : ∀ i, ‖YS t₁ - R i (YS t₁)‖ ≤ Metric.infDist (YS t₁) (Mi i)) :
    modeProd R (YS t₁) = A t₁ := by
  have _ := hR
  have hst : YS t₀ = A t₀ := hs.start
  have h0 : YS t₀ = (List.ofFn P₁).prod (A t₀) := by
    have := modeProd_apply_eq_self (P := P₁) hs.augment
    exact hst.trans this.symm
  have hex : YS t₁ = A t₁ := by
    have hy : ODESolution (fun t Y => (List.ofFn P₁).prod (F t Y)) YS t₀ t₁ := hs.sSol
    exact Exactness.tucker_exact_abstract (E := E) ht hA (d := d) (P := P₁) (Q := Q₀) (YK := YK)
      hs.kSol hs.kStart hQ hs.kCap h𝓛 hrec hy h0
  rw [hex]
  refine modeProd_apply_eq_self fun i => ?_
  have h1 := hopt i
  rw [hex, Metric.infDist_zero_of_mem (hAM i)] at h1
  exact (sub_eq_zero.mp (norm_le_zero_iff.mp (h1.trans_eq rfl) )).symm

open scoped LeanDLRA.Frobenius in
/-- OP-TN-10 (i) (source: arXiv 2104.05247, §4.2), matrix truncation layer: the truncated SVD
leaves a matrix of rank `≤ r` unchanged, so the rank-adaptive BUG integrator with SVD truncation
to rank `r` is exact for rank-`r` data. -/
theorem truncation_eq_self_of_rank_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {r : ℕ} {X : Matrix m n ℝ} (hX : X.rank ≤ r) : EckartYoung.truncation X r = X := by
  have h := EckartYoung.norm_sub_truncation_le X hX
  rw [sub_self, norm_zero] at h
  exact (sub_eq_zero.mp (norm_le_zero_iff.mp h)).symm

end RankAdaptive

section TTTangent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- OP-TN-11 (source: arXiv 2402.18721, Prop. 4.1, idempotence paragraph; arXiv 2510.19518,
§6).  The oblique (interpolatory) TT tangent projector is idempotent provided the oblique
interface projectors satisfy **range and kernel nesting** (`P_{≤k} P_{≤k+1} = P_{≤k+1}`,
`P_{≤k+1} P_{≤k} = P_{≤k+1}`, and the mirrored relations for `P_{>k}`) and left/right projectors
on disjoint mode sets commute.  (The published proof uses only idempotence of the factors, which
does not suffice for `d ≥ 3`; for `d = 2` the claim is `IsObliqueProj.tangent`.)  The proof
is `Tensor.ttTangentSum_idem` of the core, which does not need `hl0`, `hrr` and `hrk`. -/
theorem ttTangentSum_idem {Pl Pr : ℕ → E →L[ℝ] E} {d : ℕ}
    (hPl : ∀ k, Pl k * Pl k = Pl k) (hPr : ∀ k, Pr k * Pr k = Pr k) (hl0 : Pl 0 = 1)
    (hrd : Pr d = 1) (hcomm : ∀ j k, j ≤ k → Pl j * Pr k = Pr k * Pl j)
    (hlr : ∀ k, Pl k * Pl (k + 1) = Pl (k + 1)) (hlk : ∀ k, Pl (k + 1) * Pl k = Pl (k + 1))
    (hrr : ∀ k, Pr (k + 1) * Pr k = Pr k) (hrk : ∀ k, Pr k * Pr (k + 1) = Pr k) :
    ttTangentSum Pl Pr d * ttTangentSum Pl Pr d = ttTangentSum Pl Pr d := by
  have _ := And.intro hl0 (And.intro hrr hrk)
  rw [ttTangentSum_eq_tensor]
  exact Tensor.ttTangentSum_idem hPl hPr hrd hcomm hlr hlk

/-- OP-TN-11 (source: arXiv 2510.19518 §6), quasi-optimality of interpolatory TT-DLRA: under
the hypotheses of `ttTangentSum_idem`, if the oblique interface projectors have the same ranges
as orthogonal ones `Ql k`, `Qr k` (`Pl k Ql k = Ql k`, `Ql k Pl k = Pl k`, and likewise on the
right) satisfying the same nesting and commutation relations, then the oblique TT tangent
projector is an oblique projector onto the orthogonal TT tangent projector
(`IsObliqueProj (ttTangentSum Pl Pr d) (ttTangentSum Ql Qr d)`); the generic bounds
`IsObliqueProj.norm_sub_le_opNorm` then give quasi-optimality with constant `‖P_Y‖`.  The
proof is `Tensor.ttTangentSum_isObliqueProj` of the core, which does not need `hPl`, `hPr`,
`hl0`, `hlr`, `hlk`, `hrr`, `hrk` and `hql0`. -/
theorem ttTangentSum_isObliqueProj {Pl Pr Ql Qr : ℕ → E →L[ℝ] E} {d : ℕ}
    (hPl : ∀ k, Pl k * Pl k = Pl k) (hPr : ∀ k, Pr k * Pr k = Pr k) (hl0 : Pl 0 = 1)
    (hrd : Pr d = 1) (hcomm : ∀ j k, j ≤ k → Pl j * Pr k = Pr k * Pl j)
    (hlr : ∀ k, Pl k * Pl (k + 1) = Pl (k + 1)) (hlk : ∀ k, Pl (k + 1) * Pl k = Pl (k + 1))
    (hrr : ∀ k, Pr (k + 1) * Pr k = Pr k) (hrk : ∀ k, Pr k * Pr (k + 1) = Pr k)
    (hQl : ∀ k, IsOrthProj (Ql k)) (hQr : ∀ k, IsOrthProj (Qr k)) (hql0 : Ql 0 = 1)
    (hqrd : Qr d = 1) (hqcomm : ∀ j k, j ≤ k → Ql j * Qr k = Qr k * Ql j)
    (hqlr : ∀ k, Ql k * Ql (k + 1) = Ql (k + 1)) (hqrr : ∀ k, Qr (k + 1) * Qr k = Qr k)
    (hPQl : ∀ k, Pl k * Ql k = Ql k) (hQPl : ∀ k, Ql k * Pl k = Pl k)
    (hPQr : ∀ k, Pr k * Qr k = Qr k) (hQPr : ∀ k, Qr k * Pr k = Pr k)
    (hmix : ∀ j k, j ≤ k → Pl j * Qr k = Qr k * Pl j ∧ Ql j * Pr k = Pr k * Ql j) :
    IsObliqueProj (ttTangentSum Pl Pr d) (ttTangentSum Ql Qr d) := by
  have _ := And.intro hl0 (And.intro hql0 (And.intro hlk (And.intro hrr hrk)))
  have _ := And.intro hPl (And.intro hPr hlr)
  rw [ttTangentSum_eq_tensor Pl Pr d, ttTangentSum_eq_tensor Ql Qr d]
  exact Tensor.ttTangentSum_isObliqueProj hrd hcomm hQl hQr hqrd hqcomm hqlr hqrr hPQl hQPl hPQr
    hQPr hmix

/-- OP-TN-15 (source: arXiv 2002.11392, Introduction; TT case: Lubich–Oseledets–Vandereycken,
arXiv 1407.2042, Thm 3.1), TT warm-up of the CLW conjecture: for orthogonal interface
projectors with nested ranges (`P_{≤k} P_{≤k+1} = P_{≤k+1}`, `P_{>k+1} P_{>k} = P_{>k}`) that
commute across disjoint mode sets, the alternating sum `ttTangentSum` is an **orthogonal**
projector (the TT tangent projector), whose summands `± P_{≤k-1} P_{>k}`, `± P_{≤k} P_{>k}` are
the substep projectors of the TT projector-splitting integrator.  The tree version (alternating
sum of nested prolongated subprojections of a TTN) and the identification of the recursive TTN
integrator with the Lie–Trotter splitting of `Ẏ = P(Y) F(t, Y)` remain open.  The proof is
`Tensor.ttTangentSum_isOrthProj` of the core, which does not need `hl0` and `hrr`. -/
theorem ttTangentSum_isOrthProj {Ql Qr : ℕ → E →L[ℝ] E} {d : ℕ}
    (hQl : ∀ k, IsOrthProj (Ql k)) (hQr : ∀ k, IsOrthProj (Qr k)) (hl0 : Ql 0 = 1)
    (hrd : Qr d = 1) (hcomm : ∀ j k, j ≤ k → Ql j * Qr k = Qr k * Ql j)
    (hlr : ∀ k, Ql k * Ql (k + 1) = Ql (k + 1)) (hrr : ∀ k, Qr (k + 1) * Qr k = Qr k) :
    IsOrthProj (ttTangentSum Ql Qr d) := by
  have _ := And.intro hl0 hrr
  rw [ttTangentSum_eq_tensor]
  exact Tensor.ttTangentSum_isOrthProj hQl hQr hrd hcomm hlr

end TTTangent

section Schmidt

open scoped Matrix LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n]

/-- OP-TN-12 (source: arXiv 2309.08252 §1; arXiv 2501.04157 §1, §3.1), rank growth: applying a
generator of operator Schmidt rank `s` multiplies the rank by at most `s`, so
`rank (Lʲ P₀) ≤ sʲ rank P₀`. -/
theorem rank_schmidtOp_pow_le {s : ℕ} (B : Fin s → Matrix m m ℝ) (C : Fin s → Matrix n n ℝ)
    (P₀ : Matrix m n ℝ) (j : ℕ) : ((schmidtOp B C)^[j] P₀).rank ≤ s ^ j * P₀.rank := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    set Y := (schmidtOp B C)^[j] P₀
    have hY : schmidtOp B C Y = ∑ k, B k * Y * (C k)ᵀ := by
      simp [schmidtOp, Matrix.mul_assoc]
    rw [hY]
    have hsum : ∀ T : Finset (Fin s), (∑ k ∈ T, B k * Y * (C k)ᵀ).rank ≤ T.card * Y.rank := by
      intro T
      induction T using Finset.induction_on with
      | empty => simp
      | insert a T ha ih2 =>
        rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
        calc _ ≤ (B a * Y * (C a)ᵀ).rank + (∑ k ∈ T, B k * Y * (C k)ᵀ).rank :=
              EckartYoung.rank_add_le _ _
          _ ≤ Y.rank + T.card * Y.rank := by
              gcongr
              exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
          _ = _ := by ring
    calc _ ≤ (Finset.univ : Finset (Fin s)).card * Y.rank := hsum _
      _ = s * Y.rank := by simp
      _ ≤ s * (s ^ j * P₀.rank) := Nat.mul_le_mul_left _ ih
      _ = _ := by ring

end Schmidt

section Hybrid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Hybrid

section Stiff

open scoped Matrix

end Stiff

end LeanDLRA.OpenProblems.TensorNetworks
