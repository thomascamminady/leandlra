import LeanDLRA.Kinetic.Defs
import LeanDLRA.LinearAlgebra.LowRank.SepRank

/-!
# Separation rank of the kinetic low-rank ansatz

The low-rank ansatz `f(x, v) = w(v) ∑ᵢⱼ Xᵢ(x) Sᵢⱼ Vⱼ(v)` of `LeanDLRA/Kinetic/Defs.lean`
(`LeanDLRA.Kinetic.lowRankAnsatz`) and the separation rank of
`LeanDLRA/LinearAlgebra/LowRank/SepRank.lean` (`LeanDLRA.HasSepRankLE`) describe the same
functions: the ansatz has separation rank at most the number of its basis functions in either
variable, and separation rank at most `r` is the ansatz with `r` terms, unit weight and unit core.
On a finite phase grid the ansatz is a matrix of rank at most the number of basis functions.

## Main statements

* `LeanDLRA.Kinetic.hasSepRankLE_lowRankAnsatz`, `hasSepRankLE_lowRankAnsatz_left`: the ansatz
  has separation rank at most the number of velocity, respectively spatial, basis functions.
* `LeanDLRA.Kinetic.hasSepRankLE_iff_exists_lowRankAnsatz`:
  `HasSepRankLE ℝ f r ↔ ∃ X V, f = lowRankAnsatz 1 X 1 V` with `r` basis functions.
* `LeanDLRA.Kinetic.rank_lowRankAnsatz_le`: on finite index types the matrix of the ansatz has
  rank at most `min (card ι) (card κ)`.
-/

open Finset

namespace LeanDLRA.Kinetic

variable {𝒳 𝒱 ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The low-rank ansatz has separation rank at most the number of velocity basis functions: the
core and the spatial basis are collected in `K_j = ∑ᵢ Xᵢ Sᵢⱼ`, the weight goes to `V_j`. -/
theorem hasSepRankLE_lowRankAnsatz (w : 𝒱 → ℝ) (X : ι → 𝒳 → ℝ) (S : Matrix ι κ ℝ)
    (V : κ → 𝒱 → ℝ) : HasSepRankLE ℝ (lowRankAnsatz w X S V) (Fintype.card κ) :=
  HasSepRankLE.of_sum (fun j x => ∑ i, X i x * S i j) (fun j v => w v * V j v)
    (fun x v => by
      rw [lowRankAnsatz_apply, Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring) le_rfl

/-- The low-rank ansatz has separation rank at most the number of spatial basis functions: the
core, the weight and the velocity basis are collected in `L_i = w ∑ⱼ Sᵢⱼ Vⱼ`. -/
theorem hasSepRankLE_lowRankAnsatz_left (w : 𝒱 → ℝ) (X : ι → 𝒳 → ℝ) (S : Matrix ι κ ℝ)
    (V : κ → 𝒱 → ℝ) : HasSepRankLE ℝ (lowRankAnsatz w X S V) (Fintype.card ι) :=
  HasSepRankLE.of_sum X (fun i v => w v * ∑ j, S i j * V j v)
    (fun x v => by
      rw [lowRankAnsatz_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring) le_rfl

/-- **Separation rank is the low-rank ansatz.** A real function of two variables has separation
rank at most `r` if and only if it is a low-rank ansatz with `r` basis functions in each variable,
unit weight and unit core. -/
theorem hasSepRankLE_iff_exists_lowRankAnsatz (f : 𝒳 → 𝒱 → ℝ) (r : ℕ) :
    HasSepRankLE ℝ f r ↔
      ∃ (X : Fin r → 𝒳 → ℝ) (V : Fin r → 𝒱 → ℝ), f = lowRankAnsatz 1 X 1 V := by
  refine exists_congr fun X => exists_congr fun V => ?_
  simp only [funext_iff, lowRankAnsatz_one_one]

/-- On finite index types the matrix of the low-rank ansatz has rank at most the number of basis
functions in either variable. -/
theorem rank_lowRankAnsatz_le [Finite 𝒳] [Fintype 𝒱] (w : 𝒱 → ℝ) (X : ι → 𝒳 → ℝ)
    (S : Matrix ι κ ℝ) (V : κ → 𝒱 → ℝ) :
    (Matrix.of (lowRankAnsatz w X S V)).rank ≤ min (Fintype.card ι) (Fintype.card κ) :=
  le_min ((hasSepRankLE_lowRankAnsatz_left w X S V).rank_le id id)
    ((hasSepRankLE_lowRankAnsatz w X S V).rank_le id id)

/-- An ansatz with two basis functions in each variable, the weight `v + 2` and a core with the
entries `1, 2, 3, 4` has separation rank at most two. -/
example : HasSepRankLE ℝ (lowRankAnsatz (fun v : ℝ => v + 2) ![fun x : ℝ => x, fun _ => 1]
    !![1, 2; 3, 4] ![fun v : ℝ => v, fun v => v ^ 2]) 2 := by
  simpa using hasSepRankLE_lowRankAnsatz (fun v : ℝ => v + 2) ![fun x : ℝ => x, fun _ => 1]
    !![1, 2; 3, 4] ![fun v : ℝ => v, fun v => v ^ 2]

/-- On a `5 × 7` grid, an ansatz with two spatial and three velocity basis functions is a matrix
of rank at most two. -/
example (w : Fin 7 → ℝ) (X : Fin 2 → Fin 5 → ℝ) (S : Matrix (Fin 2) (Fin 3) ℝ)
    (V : Fin 3 → Fin 7 → ℝ) : (Matrix.of (lowRankAnsatz w X S V)).rank ≤ 2 := by
  simpa using rank_lowRankAnsatz_le w X S V

/-- The function `x v + 1` is a low-rank ansatz with two terms. -/
example : ∃ (X : Fin 2 → ℝ → ℝ) (V : Fin 2 → ℝ → ℝ),
    (fun x v : ℝ => x * v + 1) = lowRankAnsatz 1 X 1 V :=
  (hasSepRankLE_iff_exists_lowRankAnsatz _ 2).1
    ⟨![fun x => x, fun _ => 1], ![fun v => v, fun _ => 1], fun x v => by
      simp [Fin.sum_univ_two]⟩

end LeanDLRA.Kinetic
