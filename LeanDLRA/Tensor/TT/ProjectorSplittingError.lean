import LeanDLRA.Tensor.TT.ProjectorSplittingExactness
import LeanDLRA.Foundations.Existence

/-!
# Robust error bound of the tensor-train projector-splitting integrator

The tensor-train (TT) projector-splitting integrator `IsTTKSLStep`
([LubichOseledetsVandereycken2015], §4) is robust: its local error is `O(h (h + ε))` and its global
error `O(δ + ε + h)`, with constants that depend on the number `d` of cores, the Lipschitz
constant `L` and the bound `B` of the field, the final time and a bound of the step size, but not
on singular values. Only the normal bounds `ε` at the forward substep values enter.

## The recursion

From core `k` on, the sweep (forward substep of core `k`, backward substep of bond `k + 1`, then
the sweep from core `k + 1`) is one step of the matrix projector-splitting integrator for the
field `G_k = P_{≤k} F` with `Q₀ = P_{>k+1}` and `P₁ = P_{≤k+1}`, whose L-step
`ẏ = P_{≤k+1} F(t, y)` is solved inexactly, namely by the sweep from core `k + 1`. The bound of
the matrix integrator with inexact substeps (`IsInexactKSLStep.local_error`; cf.
[KieriLubichWalach2016], §2.6.3, as quoted in arXiv 2010.02022) gives, for the error `η_k` of the
sweep from core `k` against the exact flow of `G_k`,
`η_k ≤ h (11 L B h + ε) + (2 + 3 L h) η_{k+1}` and `η_{d-1} = 0`. Since `P_{≤0} = 1`, the local
error is `η_0 ≤ c_d(h) h (11 L B h + ε)` with `c_d(h) = ∑_{j<d-1} (2 + 3 L h)^j`. For `d = 2`
(`c_2 = 1`) this is the bound of the matrix integrator (`IsTTKSLStep.isKSLStep`,
`IsKSLStep.local_error`).

The constant `c_d` grows like `2^{d-1}`: it is the constant of this proof. "Robust" refers to the
independence of singular values, not to the dependence on `d`.

## Main results

* `IsTTKSLStep.local_error`: `‖Y₁ - A(t₁)‖ ≤ c_d(h) h (11 L B h + ε)`.
* `tt_ksl_global_error`: for `h ≤ H` and `n h ≤ T`,
  `‖Yₙ - A(tₙ)‖ ≤ e^{LT} δ + T e^{LT} c_d ε + 11 L B T e^{LT} c_d h` with
  `c_d = ∑_{j<d-1} (2 + 3 L H)^j` (for `d = 2` the constants of `ksl_global_error_le`).

## Implementation notes

The field is Lipschitz, bounded and continuous in time on the whole space; continuity in time is
used only for the existence of the exact flows of the intermediate fields `P_{≤k} F` and of `F`
from the numerical values (`exists_ODESolution`). The normal bound is required at the forward
substep values `YK k t₁`, in the form `‖(1 - P_{≤k+1}) (1 - P_{>k+1}) F(t, YK k t₁)‖ ≤ ε`, the
form of `IsTTKSLStep.isKSLStep` for two cores. The TT step is not a step of the tree tensor
network integrator on the linear tree (`IsTTNKSLStep`): there every inner node has an additional
backward substep and a core step, so the error bound of `Tensor/TTN/ProjectorSplitting.lean` does
not apply directly.

## References

* [LubichOseledetsVandereycken2015]
* [KieriLubichWalach2016]
-/

open Set

namespace LeanDLRA.Tensor

variable {d : ℕ} {ι : Fin d → Type*} [∀ i, Fintype (ι i)] {β : ℕ → Type*} [∀ k, Fintype (β k)]
  [∀ k, DecidableEq (β k)] [Unique (β 0)] [Unique (β d)]

namespace IsTTKSLStep

variable {F : ℝ → Tensor ι → Tensor ι} {U V : TTCores ι β} {t₀ t₁ : ℝ} {Y₀ : Tensor ι}
  {YK YS : ℕ → ℝ → Tensor ι}

/-- The sweep from core `k` on against the exact flow `Φ` of `ẏ = P_{≤k} F(t, y)` from
`YK k t₀`, with `k + 1 + m = d`: the error is at most `(∑_{j<m} (2 + 3 L h)^j) h (11 L B h + ε)`. -/
private theorem norm_sub_le_aux (hs : IsTTKSLStep F U V t₀ t₁ Y₀ YK YS) {L B ε h : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hcont : ∀ x, Continuous fun t => F t x)
    (hε : ∀ k, k + 1 < d → ∀ t ∈ Icc t₀ t₁,
      ‖(1 - ttLeftProj U (k + 1)) ((1 - ttRightProj V (k + 1)) (F t (YK k t₁)))‖ ≤ ε)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) :
    ∀ m k, k + 1 + m = d → ∀ Φ : ℝ → Tensor ι,
      ODESolution (fun t x => ttLeftProj U k (F t x)) Φ t₀ t₁ → Φ t₀ = YK k t₀ →
      ‖YK (d - 1) t₁ - Φ t₁‖ ≤
        (∑ j ∈ Finset.range m, (2 + 3 * L * h) ^ j) * (h * (11 * L * B * h + ε)) := by
  have h01 : t₀ ≤ t₁ := by rw [ht₁]; linarith
  have hLk : ∀ k, k < d → IsOrthProj (ttLeftProj U k) := fun k hk =>
    isOrthProj_ttLeftProj hk.le fun i hi => hs.leftOrth i (by omega)
  intro m
  induction m with
  | zero =>
    intro k hkd Φ hΦ hΦ₀
    have hd : 0 < d := by omega
    have hk : k = d - 1 := by omega
    subst hk
    have hK : ODESolution (fun t x => ttLeftProj U (d - 1) (F t x)) (YK (d - 1)) t₀ t₁ :=
      ⟨(hs.kSol (d - 1) (by omega)).cont, fun t ht =>
        ((hs.kSol (d - 1) (by omega)).deriv t ht).congr_deriv (by
          simp only [ttKProj, mul_apply_eq_comp, Nat.sub_add_cancel hd, ttRightProj_self,
            one_apply_eq_self])⟩
    have heq := hK.eqOn hΦ (hF.comp_contraction _ (hLk (d - 1) (by omega)).norm_le) hL
      hΦ₀.symm ⟨h01, le_rfl⟩
    rw [heq, sub_self, norm_zero, Finset.sum_range_zero, zero_mul]
  | succ m ih =>
    intro k hkd Φ hΦ hΦ₀
    have hk : k + 1 < d := by omega
    obtain ⟨Ψ, hΨ, hΨ₀⟩ :=
      exists_ODESolution_clm hF hB hcont (ttLeftProj U (k + 1)) h01 (YS k t₁)
    have hη := ih (k + 1) (by omega) Ψ hΨ (hΨ₀.trans (hs.kStart k hk).symm)
    have hP := hLk (k + 1) hk
    have hPk := hLk k (by omega)
    have hLL : ∀ x, ttLeftProj U k (ttLeftProj U (k + 1) x) = ttLeftProj U (k + 1) x :=
      fun x => congrArg (fun T : Tensor ι →L[ℝ] Tensor ι => T x)
        (ttLeftProj_mul_succ fun i hi => hs.leftOrth i (by omega))
    have hLL' : ∀ x, ttLeftProj U (k + 1) (ttLeftProj U k x) = ttLeftProj U (k + 1) x :=
      hP.comp_eq_of_comp_eq hPk hLL
    have hLR : ∀ x, ttLeftProj U k (ttRightProj V (k + 1) x) =
        ttRightProj V (k + 1) (ttLeftProj U k x) := fun x =>
      congrArg (fun T : Tensor ι →L[ℝ] Tensor ι => T x)
        (ttLeftProj_comm_ttRightProj U V (Nat.le_succ k))
    have hstep : IsInexactKSLStep (fun t x => ttLeftProj U k (F t x)) ε 0 0
        ((∑ j ∈ Finset.range m, (2 + 3 * L * h) ^ j) * (h * (11 * L * B * h + ε)))
        (ttLeftProj U (k + 1)) (ttRightProj V (k + 1)) t₀ t₁ (YK k t₀) (YK k t₁) (YS k t₁)
        (YK (d - 1) t₁) (YK k) (YS k) Ψ :=
      { projP₁ := hP
        projQ₀ := isOrthProj_ttRightProj hk.le fun i hi => hs.rightOrth i (by omega)
        kSol := ⟨(hs.kSol k (by omega)).cont, fun t ht =>
          ((hs.kSol k (by omega)).deriv t ht).congr_deriv (by
            simp only [ttKProj, mul_apply_eq_comp, hLR])⟩
        kStart := rfl
        kErr := by simp
        kCap := hs.kCap k hk
        kNormal t ht := by
          have e : (1 - ttLeftProj U (k + 1)) ((1 - ttRightProj V (k + 1))
              (ttLeftProj U k (F t (YK k t₁)))) = ttLeftProj U k ((1 - ttLeftProj U (k + 1))
                ((1 - ttRightProj V (k + 1)) (F t (YK k t₁)))) := by
            simp only [_root_.sub_apply, one_apply_eq_self, map_sub, ← hLR, hLL, hLL']
          have h2 := (hPk.norm_le _).trans (hε k hk t ht)
          rw [← e] at h2
          exact h2
        sSol := ⟨(hs.sSol k hk).cont, fun t ht =>
          ((hs.sSol k hk).deriv t ht).congr_deriv (by
            simp only [ttSProj, mul_apply_eq_comp, ← hLR, hLL'])⟩
        sStart := hs.sStart k hk
        sErr := by simp
        lSol := ⟨hΨ.cont, fun t ht => (hΨ.deriv t ht).congr_deriv (hLL' _).symm⟩
        lStart := hΨ₀
        lErr := hη }
    have hloc := hstep.local_error (hF.comp_contraction _ hPk.norm_le) hL
      (hB.comp_contraction _ hPk.norm_le) ht₁ hh hΦ hΦ₀
    refine hloc.trans (le_of_eq ?_)
    rw [geom_sum_succ]
    ring

/-- **Robust local error of the TT projector-splitting integrator.** Let `F` be `L`-Lipschitz,
bounded by `B` and continuous in time, and let the doubly-normal component of `F` at every
forward substep value be at most `ε`:
`‖(1 - P_{≤k+1}) (1 - P_{>k+1}) F(t, YK k t₁)‖ ≤ ε` for every inner bond `k + 1`. For a step of
size `h` from `Y₀ = A(t₀)`, with `A` the exact solution,

  `‖Y₁ - A(t₁)‖ ≤ (∑_{j<d-1} (2 + 3 L h)^j) h (11 L B h + ε)`.

The constant is that of this proof (by recursion over the cores with the inexact-substep bound
of the matrix integrator, see the module docstring); it does not depend on singular values, and
it grows like `2^{d-1}` with the number `d` of cores. For `d = 2` it is the bound
`h (11 L B h + ε)` of the matrix integrator. -/
theorem local_error (hs : IsTTKSLStep F U V t₀ t₁ Y₀ YK YS) {L B ε h : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hcont : ∀ x, Continuous fun t => F t x)
    (hε : ∀ k, k + 1 < d → ∀ t ∈ Icc t₀ t₁,
      ‖(1 - ttLeftProj U (k + 1)) ((1 - ttRightProj V (k + 1)) (F t (YK k t₁)))‖ ≤ ε)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) {A : ℝ → Tensor ι} (hA : ODESolution F A t₀ t₁)
    (hA₀ : A t₀ = Y₀) (hd : 0 < d) :
    ‖YK (d - 1) t₁ - A t₁‖ ≤
      (∑ j ∈ Finset.range (d - 1), (2 + 3 * L * h) ^ j) * (h * (11 * L * B * h + ε)) :=
  norm_sub_le_aux hs hF hL hB hcont hε ht₁ hh (d - 1) 0 (by omega) A
    ⟨hA.cont, fun t ht => (hA.deriv t ht).congr_deriv (by
      rw [ttLeftProj_zero, one_apply_eq_self])⟩ (hA₀.trans hs.kStart₀.symm)

end IsTTKSLStep

/-- **Robust global error bound of the TT projector-splitting integrator.** Let `F` be
`L`-Lipschitz (`L ≥ 0`), bounded by `B` and continuous in time, let `A` solve `A' = F(t, A)` on
`[t₀, t₀ + N h]` with `0 ≤ h ≤ H`, and for `n < N` let step `n` of the integrator (cores
`U n`, `V n`) go from `Y n` at `tₙ = t₀ + n h` to `Y (n + 1)`, with doubly-normal bound `ε ≥ 0`
at the forward substep values. If `‖Y 0 - A t₀‖ ≤ δ`, then for `n ≤ N` with `n h ≤ T`

  `‖Y n - A tₙ‖ ≤ e^{L T} δ + T e^{L T} c_d ε + 11 L B T e^{L T} c_d h`,

`c_d = ∑_{j<d-1} (2 + 3 L H)^j`. The constants are those of this proof: they do not depend on
singular values, and `c_d` grows like `2^{d-1}` with the number `d` of cores. For `d = 2`
(`c_2 = 1`) they are the constants of `ksl_global_error_le`. -/
theorem tt_ksl_global_error {F : ℝ → Tensor ι → Tensor ι} {L B ε : ℝ} (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hB : IsBoundedField F B) (hcont : ∀ x, Continuous fun t => F t x)
    (hε₀ : 0 ≤ ε) {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ} {A : ℝ → Tensor ι}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {U V : ℕ → TTCores ι β} {Y : ℕ → Tensor ι}
    {YK YS : ℕ → ℕ → ℝ → Tensor ι}
    (hstep : ∀ n < N, IsTTKSLStep F (U n) (V n) (t₀ + n * h) (t₀ + (n + 1) * h) (Y n) (YK n)
      (YS n))
    (hY : ∀ n < N, Y (n + 1) = YK n (d - 1) (t₀ + (n + 1) * h))
    (hε : ∀ n < N, ∀ k, k + 1 < d → ∀ t ∈ Icc (t₀ + n * h) (t₀ + (n + 1) * h),
      ‖(1 - ttLeftProj (U n) (k + 1)) ((1 - ttRightProj (V n) (k + 1))
        (F t (YK n k (t₀ + (n + 1) * h))))‖ ≤ ε)
    {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) (hd : 0 < d) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ +
        T * Real.exp (L * T) * (∑ j ∈ Finset.range (d - 1), (2 + 3 * L * H) ^ j) * ε +
        11 * L * B * T * Real.exp (L * T) * (∑ j ∈ Finset.range (d - 1), (2 + 3 * L * H) ^ j) *
          h := by
  set C := ∑ j ∈ Finset.range (d - 1), (2 + 3 * L * H) ^ j with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun j _ => pow_nonneg (by nlinarith) j
  have hB0 := hB.nonneg
  have hg0 : 0 ≤ 11 * L * B * h + ε := by positivity
  have hex : ∀ n : ℕ, ∃ Φ : ℝ → Tensor ι,
      ODESolution F Φ (t₀ + n * h) (t₀ + (n + 1) * h) ∧ Φ (t₀ + n * h) = Y n := fun n =>
    exists_ODESolution hF hB hcont (by nlinarith) (Y n)
  choose Φ hΦ hΦ₀ using hex
  have hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤
      h * (C * (11 * L * B * h + ε)) := by
    intro n hn
    rw [hY n hn]
    have h1 := (hstep n hn).local_error hF hL hB hcont (hε n hn) (by ring) hh (hΦ n) (hΦ₀ n) hd
    have h2 : ∑ j ∈ Finset.range (d - 1), (2 + 3 * L * h) ^ j ≤ C :=
      Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (by nlinarith) (by nlinarith) j
    calc _ ≤ _ := h1
      _ ≤ C * (h * (11 * L * B * h + ε)) :=
        mul_le_mul_of_nonneg_right h2 (mul_nonneg hh hg0)
      _ = h * (C * (11 * L * B * h + ε)) := by ring
  intro n hn hT
  have h1 := lady_windermere_of_le hF hL hh hA (fun n _ => hΦ n) (fun n _ => hΦ₀ n)
    (mul_nonneg hC0 hg0) hloc n hn hT
  calc _ ≤ _ := h1
    _ ≤ Real.exp (L * T) * (δ + T * (C * (11 * L * B * h + ε))) := by gcongr
    _ = _ := by ring

/-! ### Examples -/

section Examples

open TTKSLExample

/-- Non-vacuity of `IsTTKSLStep.local_error`: three cores, the constant field `c ≠ 0`
(`L = 1`, `B = ‖c‖`, `ε = 1`), one step of size `1` from `c`. -/
example : ‖((1 : ℝ) • c 3 + (1 : ℝ) • c 3) - ((1 : ℝ) • c 3 + (1 : ℝ) • c 3)‖ ≤
    (∑ j ∈ Finset.range (3 - 1), (2 + 3 * 1 * 1 : ℝ) ^ j) * (1 * (11 * 1 * ‖c 3‖ * 1 + 1)) :=
  (isTTKSLStep (d := 3) (by norm_num) 1 0 1).local_error (L := 1) (B := ‖c 3‖) (ε := 1)
    (A := fun t : ℝ => (1 : ℝ) • c 3 + t • c 3)
    (fun _ _ _ => by simp) zero_le_one (fun _ _ => le_rfl) (fun _ => continuous_const)
    (fun k hk _ _ => by simp [ttRightProj_c (show k + 1 ≤ 3 by omega)]) (by norm_num)
    zero_le_one (Exactness.odeSolution_add_smul_of_const (fun _ _ => rfl) _ 0 1) rfl
    (by norm_num)

/-- Non-vacuity of `tt_ksl_global_error`: two steps of size `1` with the data of the example
above, `Y n = c + n c`, and `δ = 1`. -/
example : ∀ n : ℕ, n ≤ 2 → (n : ℝ) * 1 ≤ 2 →
    ‖((1 : ℝ) • c 3 + (0 + (n : ℝ) * 1) • c 3) - ((1 : ℝ) • c 3 + (0 + (n : ℝ) * 1) • c 3)‖ ≤
      Real.exp (1 * 2) * 1 +
        2 * Real.exp (1 * 2) * (∑ j ∈ Finset.range (3 - 1), (2 + 3 * 1 * 1 : ℝ) ^ j) * 1 +
        11 * 1 * ‖c 3‖ * 2 * Real.exp (1 * 2) *
          (∑ j ∈ Finset.range (3 - 1), (2 + 3 * 1 * 1 : ℝ) ^ j) * 1 :=
  tt_ksl_global_error (F := fun _ _ => c 3) (L := 1) (B := ‖c 3‖) (ε := 1) (t₀ := 0) (h := 1)
    (H := 1) (N := 2) (δ := 1) (T := 2) (A := fun t : ℝ => (1 : ℝ) • c 3 + t • c 3)
    (U := fun _ => cores 3) (V := fun _ => cores 3)
    (Y := fun n : ℕ => (1 : ℝ) • c 3 + (0 + (n : ℝ) * 1) • c 3)
    (YK := fun _ _ t => (1 : ℝ) • c 3 + t • c 3)
    (YS := fun n _ t => ((1 : ℝ) • c 3 + (0 + ((n : ℝ) + 1) * 1) • c 3 +
      (0 + (n : ℝ) * 1) • c 3) + t • -c 3)
    (fun _ _ _ => by simp) zero_le_one (fun _ _ => le_rfl) (fun _ => continuous_const)
    zero_le_one zero_le_one le_rfl (Exactness.odeSolution_add_smul_of_const (fun _ _ => rfl) _ _ _)
    (fun n _ => isTTKSLStep (by norm_num) 1 _ _)
    (fun n _ => by simp only [Nat.cast_succ])
    (fun _ _ k hk _ _ => by simp [ttRightProj_c (show k + 1 ≤ 3 by omega)]) (by simp)
    (by norm_num)

end Examples

end LeanDLRA.Tensor
