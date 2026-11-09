import LeanDLRA.Foundations.ODE
import LeanDLRA.Foundations.Projector
import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2608.27749: High-order robust BUG integrators (Lemmas 3-5, parallel BUG-p)

Robust error analysis of the order-`p` *parallel* BUG integrator of Hauck-Kusch-Schotthoefer,
Section 5: the pre-augmented bases `Û₀ = Û^{(s-1)}`, `V̂₀` (built from the stages of an explicit
`s`-stage Runge-Kutta method of order `p`) make the auxiliary Runge-Kutta stages of the K-, L- and
S-steps agree with the full-rank and the projected Runge-Kutta stages up to `O(ε_r)` (Lemmas 3 and
4: `stage_bound`, `lemma3_Kstep`, `lemma3_Lstep`, `lemma4_Sstep`), and the augmented bases
`Û = [Û₀, Ũ₂]`, `V̂` capture the exact solution up to `c₁ h^{p+1} + c₂ h ε_r` (Lemma 5:
`capture_bound`, `lemma5`, `lemma5_paper_form`).  Everything is proved for matrices with the
Frobenius norm (the paper's setting), with explicit constants; `capture_bound` and `stage_bound`
are the underlying statements on an abstract inner product space.  The Runge-Kutta order
conditions used by the paper ("the method is of order `p`") enter as local-error hypotheses, and
the basis-containment facts of Lemma 1 enter as range-inclusion hypotheses: Lemmas 3-5 here are
**conditional on** these consequences of Lemma 1 (proved in the paper for its bases).
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2608_27749

open LeanDLRA

section Generic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {s : ℕ}

/-- Lipschitz estimate for a Runge-Kutta stage argument. -/
lemma lip_sum {F : ℝ → E → E} {L h t : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hh : 0 ≤ h) (Y₀ : E) (a : Fin s → ℝ) (X X' : Fin s → E) (e : Fin s → ℝ)
    (he : ∀ l, a l ≠ 0 → ‖X l - X' l‖ ≤ e l) :
    ‖F t (Y₀ + h • ∑ l, a l • X l) - F t (Y₀ + h • ∑ l, a l • X' l)‖ ≤
      L * h * ∑ l, |a l| * e l := by
  refine (hF t _ _).trans ?_
  have h1 : (Y₀ + h • ∑ l, a l • X l) - (Y₀ + h • ∑ l, a l • X' l) =
      h • ∑ l, a l • (X l - X' l) := by
    simp only [smul_sub, Finset.sum_sub_distrib]; abel
  rw [h1, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hL
  rw [norm_smul, Real.norm_of_nonneg hh]
  refine mul_le_mul_of_nonneg_left ?_ hh
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  by_cases hl : a l = 0
  · simp [hl]
  · exact mul_le_mul_of_nonneg_left (he l hl) (abs_nonneg _)

/-- Solving the stage recursion `e j ≤ δ + x ∑ₗ |aⱼₗ| eₗ` for an explicit tableau. -/
lemma rec_bound {a : Fin s → Fin s → ℝ} (ha : ∀ j l, j ≤ l → a j l = 0) {α x δ : ℝ}
    (hα : ∀ j, ∑ l, |a j l| ≤ α) (hx : 0 ≤ x) (hδ : 0 ≤ δ) (N : ℕ) (e : Fin s → ℝ)
    (he : ∀ j, j.val < N → e j ≤ δ + x * ∑ l, |a j l| * e l) :
    ∀ j : Fin s, j.val < N → e j ≤ δ * (1 + x * α) ^ j.val := by
  have key : ∀ n : ℕ, ∀ j : Fin s, j.val = n → j.val < N → e j ≤ δ * (1 + x * α) ^ j.val := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro j hjn hjN
      have hα0 : 0 ≤ α := (Finset.sum_nonneg fun l _ => abs_nonneg _).trans (hα j)
      have hy : 0 ≤ x * α := mul_nonneg hx hα0
      have hej := he j hjN
      rcases Nat.eq_zero_or_pos j.val with h0 | hpos
      · have : ∑ l, |a j l| * e l = 0 := Finset.sum_eq_zero fun l _ => by
          rw [ha j l (by change j.val ≤ l.val; omega)]; simp
        rw [this] at hej; rw [h0]; simpa using hej
      · obtain ⟨k, hk⟩ : ∃ k, j.val = k + 1 := ⟨j.val - 1, by omega⟩
        have hsum : ∑ l, |a j l| * e l ≤ α * (δ * (1 + x * α) ^ k) := by
          calc ∑ l, |a j l| * e l ≤ ∑ l, |a j l| * (δ * (1 + x * α) ^ k) := by
                refine Finset.sum_le_sum fun l _ => ?_
                by_cases hl : a j l = 0
                · simp [hl]
                · have hlj : l < j := by
                    by_contra hc; exact hl (ha j l (not_lt.mp hc))
                  have hlj' : l.val < j.val := hlj
                  have := ih l.val (by omega) l rfl (by omega)
                  refine mul_le_mul_of_nonneg_left (this.trans ?_) (abs_nonneg _)
                  exact mul_le_mul_of_nonneg_left
                    (pow_le_pow_right₀ (by linarith) (by omega)) hδ
            _ = (∑ l, |a j l|) * (δ * (1 + x * α) ^ k) := by rw [← Finset.sum_mul]
            _ ≤ α * (δ * (1 + x * α) ^ k) :=
                mul_le_mul_of_nonneg_right (hα j) (mul_nonneg hδ (pow_nonneg (by linarith) _))
        have hp : (1 : ℝ) ≤ (1 + x * α) ^ k := one_le_pow₀ (by linarith)
        rw [hk]
        calc e j ≤ δ + x * (α * (δ * (1 + x * α) ^ k)) :=
              hej.trans (add_le_add_right (mul_le_mul_of_nonneg_left hsum hx) _)
          _ ≤ δ * (1 + x * α) ^ (k + 1) := by
              rw [pow_succ]
              nlinarith [mul_nonneg hδ hy, mul_nonneg (mul_nonneg hδ hy) (sub_nonneg.2 hp),
                mul_nonneg hδ (sub_nonneg.2 hp)]
  exact fun j hj => key j.val j rfl hj

/-- **Lemmas 3 and 4 of arXiv 2608.27749, abstract core (stage comparison).**
Let `Z` be the stages of the full explicit Runge-Kutta method `Zⱼ = F(t₀ + cⱼ h, Y₀ + h ∑ₗ aⱼₗ Zₗ)`,
`Zb` the projected stages, which satisfy A3 at the stage points `Y j`
(`‖F(tⱼ, Yⱼ) - Z̄ⱼ‖ ≤ ε`), where `Yⱼ` differs from `Y₀ + h ∑ₗ aⱼₗ Z̄ₗ` by at most `η`, and `Zt`
the auxiliary stages `Z̃ⱼ = M F(tⱼ, Y₀ + h ∑ₗ aⱼₗ Z̃ₗ)` for an orthogonal projector `M` that fixes
`Z̄ⱼ` for the stages `j ≤ s - 1` (one-based; `j.val + 1 < s`).  `F` is `L`-Lipschitz (A1) and
`∑ₗ |aⱼₗ| ≤ α`.  With `δ = ε + L η` and `x = L h α`:
`‖Z̄ⱼ - Zⱼ‖ ≤ δ (1 + x)^j`, `‖Z̃ⱼ - Z̄ⱼ‖ ≤ δ (1 + x)^j` and `‖Z̃ⱼ - Zⱼ‖ ≤ 2 δ (1 + x)^j`,
i.e. `Z̃ⱼ = Zⱼ + O(ε) = Z̄ⱼ + O(ε)` (eq. (17)-(18)), with explicit constants.
Difference from the paper: the paper's induction identifies `Y_(j)` with `Y₀ + h ∑ₗ aⱼₗ Z̄ₗ`
(i.e. `η = 0`); the truncation defect `η` is carried here (take `η = 0` for the paper's bound).
Assumption A2 is not needed. -/
theorem stage_bound {F : ℝ → E → E} {L ε η h t₀ α : ℝ} {a : Fin s → Fin s → ℝ} {c : Fin s → ℝ}
    (ha : ∀ j l, j ≤ l → a j l = 0) (hα : ∀ j, ∑ l, |a j l| ≤ α)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hh : 0 ≤ h) (hε : 0 ≤ ε) (hη0 : 0 ≤ η)
    {Y₀ : E} {Z Zb Zt Y : Fin s → E} {M : E →L[ℝ] E} (hM : IsOrthProj M)
    (hZ : ∀ j, Z j = F (t₀ + c j * h) (Y₀ + h • ∑ l, a j l • Z l))
    (hZt : ∀ j, Zt j = M (F (t₀ + c j * h) (Y₀ + h • ∑ l, a j l • Zt l)))
    (hA3 : ∀ j, ‖F (t₀ + c j * h) (Y j) - Zb j‖ ≤ ε)
    (hY : ∀ j, ‖Y j - (Y₀ + h • ∑ l, a j l • Zb l)‖ ≤ η)
    (hspan : ∀ j : Fin s, j.val + 1 < s → M (Zb j) = Zb j) :
    (∀ j : Fin s, ‖Zb j - Z j‖ ≤ (ε + L * η) * (1 + L * h * α) ^ j.val) ∧
    (∀ j : Fin s, j.val + 1 < s → ‖Zt j - Zb j‖ ≤ (ε + L * η) * (1 + L * h * α) ^ j.val) ∧
    (∀ j : Fin s, j.val + 1 < s →
      ‖Zt j - Z j‖ ≤ 2 * ((ε + L * η) * (1 + L * h * α) ^ j.val)) := by
  have hx : 0 ≤ L * h := mul_nonneg hL hh
  have hδ : 0 ≤ ε + L * η := add_nonneg hε (mul_nonneg hL hη0)
  -- the common link between the low-rank stage point and the stage argument
  have hlink : ∀ j, ‖F (t₀ + c j * h) (Y j) -
      F (t₀ + c j * h) (Y₀ + h • ∑ l, a j l • Zb l)‖ ≤ L * η := fun j =>
    (hF _ _ _).trans (mul_le_mul_of_nonneg_left (hY j) hL)
  have h1 : ∀ j : Fin s, ‖Zb j - Z j‖ ≤
      (ε + L * η) + (L * h) * ∑ l, |a j l| * ‖Zb l - Z l‖ := by
    intro j
    have hd := lip_sum (t := t₀ + c j * h) hF hL hh Y₀ (a j) Zb Z (fun l => ‖Zb l - Z l‖)
      (fun l _ => le_rfl)
    rw [← hZ j] at hd
    calc ‖Zb j - Z j‖
        ≤ ‖Zb j - F (t₀ + c j * h) (Y j)‖ + ‖F (t₀ + c j * h) (Y j) -
            F (t₀ + c j * h) (Y₀ + h • ∑ l, a j l • Zb l)‖ +
          ‖F (t₀ + c j * h) (Y₀ + h • ∑ l, a j l • Zb l) - Z j‖ := by
          have := norm_sub_le_norm_sub_add_norm_sub (Zb j) (F (t₀ + c j * h) (Y j)) (Z j)
          have h2 := norm_sub_le_norm_sub_add_norm_sub (F (t₀ + c j * h) (Y j))
            (F (t₀ + c j * h) (Y₀ + h • ∑ l, a j l • Zb l)) (Z j)
          linarith
      _ ≤ ε + L * η + (L * h) * ∑ l, |a j l| * ‖Zb l - Z l‖ := by
          rw [norm_sub_rev (Zb j)]
          have := hA3 j
          have := hlink j
          nlinarith
  have b1 := rec_bound ha hα hx hδ s (fun l => ‖Zb l - Z l‖) (fun j _ => h1 j)
  have h2 : ∀ j : Fin s, j.val + 1 < s → ‖Zt j - Zb j‖ ≤
      (ε + L * η) + (L * h) * ∑ l, |a j l| * ‖Zt l - Zb l‖ := by
    intro j hj
    have hd := lip_sum (t := t₀ + c j * h) hF hL hh Y₀ (a j) Zt Zb (fun l => ‖Zt l - Zb l‖)
      (fun l _ => le_rfl)
    have hZj : Zt j - Zb j = M (F (t₀ + c j * h) (Y₀ + h • ∑ l, a j l • Zt l) - Zb j) := by
      rw [map_sub, ← hZt j, hspan j hj]
    rw [hZj]
    refine (hM.norm_le _).trans ?_
    calc ‖F (t₀ + c j * h) (Y₀ + h • ∑ l, a j l • Zt l) - Zb j‖
        ≤ ‖F (t₀ + c j * h) (Y₀ + h • ∑ l, a j l • Zt l) -
            F (t₀ + c j * h) (Y₀ + h • ∑ l, a j l • Zb l)‖ +
          ‖F (t₀ + c j * h) (Y₀ + h • ∑ l, a j l • Zb l) - F (t₀ + c j * h) (Y j)‖ +
          ‖F (t₀ + c j * h) (Y j) - Zb j‖ := by
          have := norm_sub_le_norm_sub_add_norm_sub
            (F (t₀ + c j * h) (Y₀ + h • ∑ l, a j l • Zt l))
            (F (t₀ + c j * h) (Y₀ + h • ∑ l, a j l • Zb l)) (Zb j)
          have h3 := norm_sub_le_norm_sub_add_norm_sub
            (F (t₀ + c j * h) (Y₀ + h • ∑ l, a j l • Zb l))
            (F (t₀ + c j * h) (Y j)) (Zb j)
          linarith
      _ ≤ (ε + L * η) + (L * h) * ∑ l, |a j l| * ‖Zt l - Zb l‖ := by
          rw [norm_sub_rev (F (t₀ + c j * h) (Y₀ + h • ∑ l, a j l • Zb l))]
          have := hA3 j
          have := hlink j
          nlinarith
  have b2 := rec_bound ha hα hx hδ (s - 1) (fun l => ‖Zt l - Zb l‖)
    (fun j hj => h2 j (by omega))
  refine ⟨fun j => b1 j (by omega), fun j hj => b2 j (by omega), fun j hj => ?_⟩
  have e1 := b1 j (by omega)
  have e2 := b2 j (by omega)
  calc ‖Zt j - Z j‖ ≤ ‖Zt j - Zb j‖ + ‖Zb j - Z j‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by linarith

/-- **Lemma 5 of arXiv 2608.27749, abstract core (the augmented basis captures `A(t₁)`).**
Same stage data as `stage_bound`.  `N` is the orthogonal projector of the augmented basis
(`Û Ûᵀ`), `M` the mask of the auxiliary stages (`V̂₀ V̂₀ᵀ`).  Assume that the last projected stage
satisfies `(1 - N)(1 - M) Z̄ₛ = 0` (the spans of `U_(s)`, `V_(s)`), that `N` fixes the exact
end value `Kend` of the K-step flow, that the full Runge-Kutta method has local error
`CA h^{p+1}` (`‖A(t₁) - A₁‖`, the paper's "order `p` of the Runge-Kutta method") and that the
Runge-Kutta method for the K-step has local error `CK h^{p+1}` (`‖Y₁⁽ᴷ⁾ - K(t₁)V̂₀ᵀ‖`).  Then
`‖(1 - N) A(t₁)‖ ≤ (CA + CK) h^{p+1} + β h (ε + L η) (1 + x)^s (2 + 3 x)`, `x = L h α`,
`β ≥ ∑ |bᵢ|`.  This is the first half of the proof of Lemma 5; the second half (`A(t₁)(I - V̂V̂ᵀ)`)
is the same statement with the roles of left and right exchanged ("analogously"). Differences:
as in `stage_bound`, a truncation defect `η` is carried (`η = 0` in the paper). -/
theorem capture_bound {F : ℝ → E → E} {L ε η h t₀ α β : ℝ} {a : Fin s → Fin s → ℝ}
    {b c : Fin s → ℝ} (ha : ∀ j l, j ≤ l → a j l = 0) (hα : ∀ j, ∑ l, |a j l| ≤ α)
    (hβ : ∑ i, |b i| ≤ β) (hα0 : 0 ≤ α)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hh : 0 ≤ h) (hε : 0 ≤ ε) (hη0 : 0 ≤ η)
    {Y₀ : E} {Z Zb Zt Y : Fin s → E} {M N : E →L[ℝ] E} (hM : IsOrthProj M)
    (hN : IsOrthProj N)
    (hZ : ∀ j, Z j = F (t₀ + c j * h) (Y₀ + h • ∑ l, a j l • Z l))
    (hZt : ∀ j, Zt j = M (F (t₀ + c j * h) (Y₀ + h • ∑ l, a j l • Zt l)))
    (hA3 : ∀ j, ‖F (t₀ + c j * h) (Y j) - Zb j‖ ≤ ε)
    (hY : ∀ j, ‖Y j - (Y₀ + h • ∑ l, a j l • Zb l)‖ ≤ η)
    (hspan : ∀ j : Fin s, j.val + 1 < s → M (Zb j) = Zb j)
    (hlast : ∀ j : Fin s, ¬ (j.val + 1 < s) → (1 - N) ((1 - M) (Zb j)) = 0)
    {A₁ Y₁ Kend Aend : E} (hA₁ : A₁ = Y₀ + h • ∑ i, b i • Z i)
    (hY₁ : Y₁ = Y₀ + h • ∑ i, b i • Zt i) {p : ℕ} {CA CK : ℝ}
    (hRK : ‖Aend - A₁‖ ≤ CA * h ^ (p + 1)) (hK : ‖Y₁ - Kend‖ ≤ CK * h ^ (p + 1))
    (hNK : N Kend = Kend) :
    ‖Aend - N Aend‖ ≤ (CA + CK) * h ^ (p + 1) +
      β * (h * (ε + L * η)) * ((1 + L * h * α) ^ s * (2 + 3 * (L * h * α))) := by
  obtain ⟨b1, b2, b3⟩ := stage_bound ha hα hF hL hh hε hη0 hM hZ hZt hA3 hY hspan
  have hx : 0 ≤ L * h * α := mul_nonneg (mul_nonneg hL hh) hα0
  set δ : ℝ := ε + L * η with hδdef
  have hδ : 0 ≤ δ := add_nonneg hε (mul_nonneg hL hη0)
  set κ : ℝ := (1 + L * h * α) ^ s with hκ
  have hκ1 : 1 ≤ κ := one_le_pow₀ (by linarith)
  have hpow : ∀ l : Fin s, (1 + L * h * α) ^ l.val ≤ κ := fun l =>
    pow_le_pow_right₀ (by linarith) l.isLt.le
  have hD : 0 ≤ δ * κ * (2 + 3 * (L * h * α)) :=
    mul_nonneg (mul_nonneg hδ (by linarith)) (by linarith)
  have hNc : IsOrthProj (1 - N) := hN.compl
  have hMc : IsOrthProj (1 - M) := hM.compl
  -- each stage is captured up to `D`
  have hstage : ∀ i : Fin s, ‖(1 - N) (Z i - Zt i)‖ ≤ δ * κ * (2 + 3 * (L * h * α)) := by
    intro i
    by_cases hi : i.val + 1 < s
    · refine (hNc.norm_le _).trans ?_
      rw [norm_sub_rev]
      refine (b3 i hi).trans ?_
      have := mul_le_mul_of_nonneg_left (hpow i) hδ
      nlinarith
    · -- last stage
      have hl : ∀ l : Fin s, a i l ≠ 0 → l.val + 1 < s := by
        intro l hl
        have hli : l < i := by
          by_contra hc; exact hl (ha i l (not_lt.mp hc))
        have : l.val < i.val := hli
        have := i.isLt
        omega
      set W : E := Y₀ + h • ∑ l, a i l • Z l with hW
      set Wt : E := Y₀ + h • ∑ l, a i l • Zt l with hWt
      set Wb : E := Y₀ + h • ∑ l, a i l • Zb l with hWb
      set t := t₀ + c i * h with ht
      have d1 : ‖F t W - F t Wt‖ ≤ L * h * (α * (2 * (δ * κ))) := by
        have := lip_sum (t := t) hF hL hh Y₀ (a i) Z Zt (fun _ => 2 * (δ * κ)) (by
          intro l hl'
          have hl2 := hl l hl'
          rw [norm_sub_rev]
          refine (b3 l hl2).trans ?_
          have := mul_le_mul_of_nonneg_left (hpow l) hδ
          linarith)
        refine this.trans ?_
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hα i)
          (by positivity)) (mul_nonneg hL hh)
      have d2 : ‖F t Wt - F t Wb‖ ≤ L * h * (α * (δ * κ)) := by
        have := lip_sum (t := t) hF hL hh Y₀ (a i) Zt Zb (fun _ => δ * κ) (by
          intro l hl'
          have hl2 := hl l hl'
          refine (b2 l hl2).trans ?_
          exact mul_le_mul_of_nonneg_left (hpow l) hδ)
        refine this.trans ?_
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hα i)
          (mul_nonneg hδ (by linarith))) (mul_nonneg hL hh)
      have d3 : ‖F t Wb - F t (Y i)‖ ≤ L * η := by
        refine (hF _ _ _).trans (mul_le_mul_of_nonneg_left ?_ hL)
        rw [norm_sub_rev]; exact hY i
      have d4 := hA3 i
      have e1 : Z i - Zt i = (F t W - F t Wt) + (1 - M) (F t Wt) := by
        rw [hZ i, hZt i]; simp [hW, hWt, ht]
      have e2 : (1 - N) ((1 - M) (F t Wt)) = (1 - N) ((1 - M) (F t Wt - Zb i)) := by
        rw [map_sub, map_sub, hlast i hi, sub_zero]
      have e3 : ‖(1 - N) ((1 - M) (F t Wt - Zb i))‖ ≤ ‖F t Wt - Zb i‖ :=
        (hNc.norm_le _).trans (hMc.norm_le _)
      have e4 : ‖F t Wt - Zb i‖ ≤ ‖F t Wt - F t Wb‖ + ‖F t Wb - F t (Y i)‖ +
          ‖F t (Y i) - Zb i‖ := by
        have h5 := norm_sub_le_norm_sub_add_norm_sub (F t Wt) (F t Wb) (Zb i)
        have h6 := norm_sub_le_norm_sub_add_norm_sub (F t Wb) (F t (Y i)) (Zb i)
        linarith
      rw [e1, map_add]
      refine (norm_add_le _ _).trans ?_
      have e5 : ‖(1 - N) (F t W - F t Wt)‖ ≤ ‖F t W - F t Wt‖ := hNc.norm_le _
      have e6 : ‖(1 - N) ((1 - M) (F t Wt))‖ ≤ ‖F t Wt - Zb i‖ := by
        rw [e2]; exact e3
      have hxx : L * h * (α * (2 * (δ * κ))) = 2 * (L * h * α) * (δ * κ) := by ring
      have hxy : L * h * (α * (δ * κ)) = (L * h * α) * (δ * κ) := by ring
      have hδκ : δ ≤ δ * κ := by nlinarith
      have hLη : L * η + ε = δ := by rw [hδdef]; ring
      nlinarith [hδκ]
  -- assemble
  have hsum : ‖(1 - N) (A₁ - Y₁)‖ ≤ h * (β * (δ * κ * (2 + 3 * (L * h * α)))) := by
    have : A₁ - Y₁ = h • ∑ i, b i • (Z i - Zt i) := by
      rw [hA₁, hY₁]; simp only [smul_sub, Finset.sum_sub_distrib]; abel
    rw [this, map_smul, map_sum]
    simp only [map_smul]
    rw [norm_smul, Real.norm_of_nonneg hh]
    refine mul_le_mul_of_nonneg_left ?_ hh
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖b i • (1 - N) (Z i - Zt i)‖ ≤ ∑ i, |b i| * (δ * κ * (2 + 3 * (L * h * α))) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hstage i) (abs_nonneg _)
      _ = (∑ i, |b i|) * (δ * κ * (2 + 3 * (L * h * α))) := by rw [← Finset.sum_mul]
      _ ≤ β * _ := mul_le_mul_of_nonneg_right hβ hD
  have hsplit : (1 - N) Aend =
      (1 - N) (Aend - A₁) + (1 - N) (A₁ - Y₁) + (1 - N) (Y₁ - Kend) := by
    have hK0 : (1 - N) Kend = 0 := by simp [hNK]
    have : (1 - N) (Aend - A₁) + (1 - N) (A₁ - Y₁) + (1 - N) (Y₁ - Kend) =
        (1 - N) Aend - (1 - N) Kend := by
      simp only [← map_add, ← map_sub]; congr 1; abel
    rw [this, hK0, sub_zero]
  have hAe : Aend - N Aend = (1 - N) Aend := by simp
  rw [hAe, hsplit]
  calc ‖(1 - N) (Aend - A₁) + (1 - N) (A₁ - Y₁) + (1 - N) (Y₁ - Kend)‖
      ≤ ‖(1 - N) (Aend - A₁)‖ + ‖(1 - N) (A₁ - Y₁)‖ + ‖(1 - N) (Y₁ - Kend)‖ :=
        (norm_add₃_le)
    _ ≤ CA * h ^ (p + 1) + h * (β * (δ * κ * (2 + 3 * (L * h * α)))) + CK * h ^ (p + 1) :=
        add_le_add (add_le_add ((hNc.norm_le _).trans hRK) hsum) ((hNc.norm_le _).trans hK)
    _ = _ := by ring

end Generic

section MatrixAlgebra

open scoped LeanDLRA.Frobenius

/-- `Q = V̂ V̂ᵀ` with `Q V = V` gives `Vᵀ Q = Vᵀ`. -/
lemma transpose_fix {n r : Type*} [Fintype n] {A : Matrix n n ℝ} (hA : Aᵀ = A)
    {V : Matrix n r ℝ} (h : A * V = V) : Vᵀ * A = Vᵀ := by
  have := congrArg Matrix.transpose h
  rwa [Matrix.transpose_mul, hA] at this

/-- The right projector fixes the tangent-space image `P(Y) G` when its range contains the row
space of `Y` and the row space of `Uᵀ G`. -/
lemma rightProj_tangentProj_fix {m n r v : Type*} [Fintype m] [Fintype n] [Fintype r]
    [Fintype v] {Vh : Matrix n v ℝ} {U : Matrix m r ℝ} {V : Matrix n r ℝ}
    {G : Matrix m n ℝ} (hV : Vh * Vhᵀ * V = V) (hG : Vh * Vhᵀ * (Gᵀ * U) = Gᵀ * U) :
    rightProj Vh (tangentProj U V G) = tangentProj U V G := by
  have hQ : (Vh * Vhᵀ)ᵀ = Vh * Vhᵀ := by simp [Matrix.transpose_mul]
  have h1 : Vᵀ * (Vh * Vhᵀ) = Vᵀ := transpose_fix hQ hV
  have h2 : Uᵀ * G * (Vh * Vhᵀ) = Uᵀ * G := by
    simpa [Matrix.transpose_mul] using transpose_fix hQ hG
  rw [rightProj_apply', tangentProj_apply]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc] at h2 ⊢
  rw [h1, h2]

/-- The left projector fixes the tangent-space image `P(Y) G` when its range contains the column
space of `Y` and the column space of `G V`. -/
lemma leftProj_tangentProj_fix {m n r u : Type*} [Fintype m] [Fintype n] [Fintype r]
    [Fintype u] {Uh : Matrix m u ℝ} {U : Matrix m r ℝ} {V : Matrix n r ℝ}
    {G : Matrix m n ℝ} (hU : Uh * Uhᵀ * U = U) (hG : Uh * Uhᵀ * (G * V) = G * V) :
    leftProj Uh (tangentProj U V G) = tangentProj U V G := by
  have hU2 : ∀ X : Matrix r n ℝ, Uh * Uhᵀ * (U * X) = U * X := fun X => by
    rw [← Matrix.mul_assoc, hU]
  have hG2 : ∀ X : Matrix r n ℝ, Uh * Uhᵀ * (G * (V * X)) = G * (V * X) := fun X => by
    rw [← Matrix.mul_assoc G V X, ← Matrix.mul_assoc _ (G * V) X, hG]
  rw [leftProj_apply, tangentProj_apply]
  generalize Uh * Uhᵀ = P at hU2 hG2 ⊢
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_assoc] at hU2 hG2 ⊢
  rw [hU2, hG2, hU2]

/-- Vanishing of the doubly-normal part of a tangent vector when the complementary projectors
kill `U` from the left and `V` from the right. -/
lemma normal_tangentProj_eq_zero {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
    [DecidableEq m] [DecidableEq n] {P : Matrix m m ℝ} {Q : Matrix n n ℝ}
    {U : Matrix m r ℝ} {V : Matrix n r ℝ} (G : Matrix m n ℝ) (hU : P * U = U)
    (hV : Vᵀ * Q = Vᵀ) : (1 - P) * (tangentProj U V G * (1 - Q)) = 0 := by
  have hz : Vᵀ * (1 - Q) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hV, sub_self]
  have e : tangentProj U V G * (1 - Q) = U * (Uᵀ * (G * (1 - Q))) := by
    rw [tangentProj_apply]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, hz, Matrix.mul_zero]
    simp
  rw [e, ← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hU, sub_self, Matrix.zero_mul]

/-- If `P` fixes the range of `P₀` and `P₀` fixes `U`, then `P` fixes `U`. -/
lemma comp_fix {m r : Type*} [Fintype m] {P P₀ : Matrix m m ℝ} {U : Matrix m r ℝ}
    (h₁ : P * P₀ = P₀) (h₂ : P₀ * U = U) : P * U = U := by
  rw [← h₂, ← Matrix.mul_assoc, h₁]

/-- `Û Ûᵀ Û₀ = Û₀` gives `Û Ûᵀ (Û₀ Û₀ᵀ) = Û₀ Û₀ᵀ`. -/
lemma aug_fix {m u w : Type*} [Fintype m] [Fintype u] [Fintype w] {Uh : Matrix m u ℝ}
    {Uh₀ : Matrix m w ℝ} (h : Uh * Uhᵀ * Uh₀ = Uh₀) :
    Uh * Uhᵀ * (Uh₀ * Uh₀ᵀ) = Uh₀ * Uh₀ᵀ := by
  rw [← Matrix.mul_assoc, h]

/-- A matrix whose component in the old range is kept and whose new component is captured is
fixed by the augmented left projector. -/
lemma aug_fix_left {m n : Type*} [Fintype m] [DecidableEq m] {P P₀ : Matrix m m ℝ}
    {K : Matrix m n ℝ} (h₁ : P * P₀ = P₀) (h₂ : P * ((1 - P₀) * K) = (1 - P₀) * K) :
    P * K = K := by
  have hK : K = P₀ * K + (1 - P₀) * K := by rw [Matrix.sub_mul, Matrix.one_mul]; abel
  conv_lhs => rw [hK]
  rw [Matrix.mul_add, h₂, ← Matrix.mul_assoc, h₁]
  conv_rhs => rw [hK]

/-- Right-handed version of `aug_fix_left`. -/
lemma aug_fix_right {m n : Type*} [Fintype n] [DecidableEq n] {Q Q₀ : Matrix n n ℝ}
    {K : Matrix m n ℝ} (h₁ : Q₀ * Q = Q₀) (h₂ : K * (1 - Q₀) * Q = K * (1 - Q₀)) :
    K * Q = K := by
  have hK : K = K * Q₀ + K * (1 - Q₀) := by rw [Matrix.mul_sub, Matrix.mul_one]; abel
  conv_lhs => rw [hK]
  rw [Matrix.add_mul, h₂, Matrix.mul_assoc, h₁]
  conv_rhs => rw [hK]

end MatrixAlgebra

section Parallel

open scoped LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {s : ℕ}

/-- **Stage data of the order-`p` parallel BUG analysis** (arXiv 2608.27749, Sec. 3 and 5).
For an explicit Runge-Kutta tableau `(a, c)` with `s` stages it records

* the stages `Z j` of the full-rank Runge-Kutta method (eq. before Lemma 3),
  `Zⱼ = F(t₀ + cⱼ h, Y₀ + h ∑ₗ aⱼₗ Zₗ)`;
* rank-`r` stage points `Y j = U j S Vᵀ` (represented only through the column/row bases `U j`,
  `V j` of the stage factorizations `Y_(j) = U_(j) S_(j) V_(j)ᵀ`), at which the normal component
  of `F` is `ε`-small (assumption A3, `‖(I - U Uᵀ) F (I - V Vᵀ)‖ ≤ ε`);
* the projected Runge-Kutta stages `Zb j = P(Y_(j)) F(t_(j), Y_(j))` (eq. (3d)), with `P` the
  tangent-space projector `tangentProj`;
* the stage truncation defect: `Y_(j)` is the rank-`r` truncation of
  `Y₀ + h ∑ₗ aⱼₗ Z̄ₗ` (eq. (3b)); the proof of Lemma 3 identifies the two (`η = 0`), and the
  slack `η` is carried explicitly here. -/
structure StageData (r : Type*) [Fintype r] (F : ℝ → Matrix m n ℝ → Matrix m n ℝ)
    (a : Fin s → Fin s → ℝ) (c : Fin s → ℝ) (Y₀ : Matrix m n ℝ) (t₀ h ε η : ℝ) where
  /-- Full Runge-Kutta stages. -/
  Z : Fin s → Matrix m n ℝ
  /-- Left bases of the rank-`r` stage points. -/
  U : Fin s → Matrix m r ℝ
  /-- Right bases of the rank-`r` stage points. -/
  V : Fin s → Matrix n r ℝ
  /-- Rank-`r` stage points. -/
  Y : Fin s → Matrix m n ℝ
  /-- Projected Runge-Kutta stages. -/
  Zb : Fin s → Matrix m n ℝ
  hZ : ∀ j, Z j = F (t₀ + c j * h) (Y₀ + h • ∑ l, a j l • Z l)
  hZb : ∀ j, Zb j = tangentProj (U j) (V j) (F (t₀ + c j * h) (Y j))
  hA3 : ∀ j, ‖(1 - U j * (U j)ᵀ) * F (t₀ + c j * h) (Y j) * (1 - V j * (V j)ᵀ)‖ ≤ ε
  hY : ∀ j, ‖Y j - (Y₀ + h • ∑ l, a j l • Zb l)‖ ≤ η

namespace StageData

variable {r : Type*} [Fintype r] {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
  {a : Fin s → Fin s → ℝ} {c : Fin s → ℝ} {Y₀ : Matrix m n ℝ} {t₀ h ε η : ℝ}

/-- Assumption A3 in the form used in the proofs: `‖F(t_(j), Y_(j)) - Z̄ⱼ‖ ≤ ε`. -/
lemma norm_F_sub_le (D : StageData r F a c Y₀ t₀ h ε η) (j : Fin s) :
    ‖F (t₀ + c j * h) (D.Y j) - D.Zb j‖ ≤ ε := by
  have h1 := tangentProj_add_normal (D.U j) (D.V j) (F (t₀ + c j * h) (D.Y j))
  have h2 : F (t₀ + c j * h) (D.Y j) - D.Zb j =
      (1 - D.U j * (D.U j)ᵀ) * F (t₀ + c j * h) (D.Y j) * (1 - D.V j * (D.V j)ᵀ) := by
    rw [D.hZb j]; exact sub_eq_iff_eq_add'.2 h1.symm
  rw [h2]; exact D.hA3 j

end StageData

/-- **Lemma 3 of arXiv 2608.27749 (K-step stages).**  Matrix form of `stage_bound` for the
auxiliary K-step Runge-Kutta stages `Z̃ⱼ = F(t₀ + cⱼ h, Y₀ + h ∑ₗ aⱼₗ Z̃ₗ) V̂₀ V̂₀ᵀ` (eq. (15a))
with `V̂₀` of orthonormal columns.  For the stages `j ≤ s - 1` (`j.val + 1 < s`):
`Z̃ⱼ = Zⱼ + O(ε) = Z̄ⱼ + O(ε)` with the explicit constants of `stage_bound`
(`δ = ε + L η`, `x = L h α`).  **Conditional on** the basis information of Lemma 1, which enters
as hypotheses: `hV` (the column space of `V_(j)` lies in `range V̂₀`) and `hFU`
(`range F_(j)ᵀ U_(j) ⊆ range V̂₀`, for `j ≤ s - 1`); these give `Z̄ⱼ V̂₀ V̂₀ᵀ = Z̄ⱼ`.
Differences from the paper: explicit constants; the truncation defect `η` of the stage points
(`η = 0` in the paper); orthonormality of the stage bases `U_(j)`, `V_(j)` is not needed; A2
(boundedness of `F`) is not needed. -/
theorem lemma3_Kstep {r kv : Type*} [Fintype r] [Fintype kv] [DecidableEq kv]
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L ε η h t₀ α : ℝ} {a : Fin s → Fin s → ℝ}
    {c : Fin s → ℝ} (ha : ∀ j l, j ≤ l → a j l = 0) (hα : ∀ j, ∑ l, |a j l| ≤ α)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hh : 0 ≤ h) (hε : 0 ≤ ε) (hη : 0 ≤ η)
    {Y₀ : Matrix m n ℝ} (D : StageData r F a c Y₀ t₀ h ε η)
    {Vh₀ : Matrix n kv ℝ} (hVh₀ : Vh₀ᵀ * Vh₀ = 1)
    (hV : ∀ j, Vh₀ * Vh₀ᵀ * D.V j = D.V j)
    (hFU : ∀ j : Fin s, j.val + 1 < s →
      Vh₀ * Vh₀ᵀ * ((F (t₀ + c j * h) (D.Y j))ᵀ * D.U j) = (F (t₀ + c j * h) (D.Y j))ᵀ * D.U j)
    {Zt : Fin s → Matrix m n ℝ}
    (hZt : ∀ j, Zt j = F (t₀ + c j * h) (Y₀ + h • ∑ l, a j l • Zt l) * Vh₀ * Vh₀ᵀ) :
    (∀ j : Fin s, ‖D.Zb j - D.Z j‖ ≤ (ε + L * η) * (1 + L * h * α) ^ j.val) ∧
    (∀ j : Fin s, j.val + 1 < s →
      ‖Zt j - D.Zb j‖ ≤ (ε + L * η) * (1 + L * h * α) ^ j.val) ∧
    (∀ j : Fin s, j.val + 1 < s →
      ‖Zt j - D.Z j‖ ≤ 2 * ((ε + L * η) * (1 + L * h * α) ^ j.val)) := by
  refine stage_bound ha hα hF hL hh hε hη (isOrthProj_rightProj (m := m) hVh₀) D.hZ
    (fun j => (hZt j).trans (rightProj_apply _ _).symm) D.norm_F_sub_le D.hY ?_
  intro j hj
  rw [D.hZb j]
  exact rightProj_tangentProj_fix (hV j) (hFU j hj)

/-- **Lemma 3 of arXiv 2608.27749, L-step version** (used by Lemma 5 for `A(t₁)(I - V̂V̂ᵀ)`).
The same statement as `lemma3_Kstep` for the auxiliary stages
`Z̃ⱼ = Û₀ Û₀ᵀ F(t₀ + cⱼ h, Y₀ + h ∑ₗ aⱼₗ Z̃ₗ)` of the Runge-Kutta method on the L-step
`L̇ = F(t, Û₀ Lᵀ)ᵀ Û₀` (left projector instead of right projector; `hU`, `hFV` instead of
`hV`, `hFU`).  **Conditional on** Lemma 1 and with the differences from the paper as for
`lemma3_Kstep`. -/
theorem lemma3_Lstep {r ku : Type*} [Fintype r] [Fintype ku] [DecidableEq ku]
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L ε η h t₀ α : ℝ} {a : Fin s → Fin s → ℝ}
    {c : Fin s → ℝ} (ha : ∀ j l, j ≤ l → a j l = 0) (hα : ∀ j, ∑ l, |a j l| ≤ α)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hh : 0 ≤ h) (hε : 0 ≤ ε) (hη : 0 ≤ η)
    {Y₀ : Matrix m n ℝ} (D : StageData r F a c Y₀ t₀ h ε η)
    {Uh₀ : Matrix m ku ℝ} (hUh₀ : Uh₀ᵀ * Uh₀ = 1)
    (hU : ∀ j, Uh₀ * Uh₀ᵀ * D.U j = D.U j)
    (hFV : ∀ j : Fin s, j.val + 1 < s →
      Uh₀ * Uh₀ᵀ * (F (t₀ + c j * h) (D.Y j) * D.V j) = F (t₀ + c j * h) (D.Y j) * D.V j)
    {Zl : Fin s → Matrix m n ℝ}
    (hZl : ∀ j, Zl j = Uh₀ * Uh₀ᵀ * F (t₀ + c j * h) (Y₀ + h • ∑ l, a j l • Zl l)) :
    (∀ j : Fin s, ‖D.Zb j - D.Z j‖ ≤ (ε + L * η) * (1 + L * h * α) ^ j.val) ∧
    (∀ j : Fin s, j.val + 1 < s →
      ‖Zl j - D.Zb j‖ ≤ (ε + L * η) * (1 + L * h * α) ^ j.val) ∧
    (∀ j : Fin s, j.val + 1 < s →
      ‖Zl j - D.Z j‖ ≤ 2 * ((ε + L * η) * (1 + L * h * α) ^ j.val)) := by
  refine stage_bound ha hα hF hL hh hε hη (isOrthProj_leftProj (n := n) hUh₀) D.hZ
    (fun j => (hZl j).trans (leftProj_apply _ _).symm) D.norm_F_sub_le D.hY ?_
  intro j hj
  rw [D.hZb j]
  exact leftProj_tangentProj_fix (hU j) (hFV j hj)

/-- **Lemma 4 of arXiv 2608.27749 (S-step stages).**  For the auxiliary Runge-Kutta stages of
the S-step, `Z̃ⱼ⁽ˢ⁾ = Û₀ Û₀ᵀ F(t₀ + cⱼ h, Y₀ + h ∑ₗ aⱼₗ Z̃ₗ⁽ˢ⁾) V̂₀ V̂₀ᵀ` (eq. (16a), written in the
full space), and `j ≤ s - 1` (`j.val + 1 < s`):
`Z̃ⱼ⁽ˢ⁾ = Zⱼ + O(ε) = Z̄ⱼ + O(ε)` with the explicit constants of `stage_bound`.  Both bases
`Û₀`, `V̂₀` have orthonormal columns and, **conditional on** Lemma 1, contain its stage information
(hypotheses `hU`, `hV`, `hFV`, `hFU`).  The proof is the same as for Lemma 3 with the Galerkin
projector `Û₀Û₀ᵀ (·) V̂₀V̂₀ᵀ` as mask.  Differences as for `lemma3_Kstep`. -/
theorem lemma4_Sstep {r ku kv : Type*} [Fintype r] [Fintype ku] [DecidableEq ku] [Fintype kv]
    [DecidableEq kv] {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L ε η h t₀ α : ℝ}
    {a : Fin s → Fin s → ℝ} {c : Fin s → ℝ} (ha : ∀ j l, j ≤ l → a j l = 0)
    (hα : ∀ j, ∑ l, |a j l| ≤ α)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hh : 0 ≤ h) (hε : 0 ≤ ε) (hη : 0 ≤ η)
    {Y₀ : Matrix m n ℝ} (D : StageData r F a c Y₀ t₀ h ε η)
    {Uh₀ : Matrix m ku ℝ} {Vh₀ : Matrix n kv ℝ} (hUh₀ : Uh₀ᵀ * Uh₀ = 1)
    (hVh₀ : Vh₀ᵀ * Vh₀ = 1)
    (hU : ∀ j, Uh₀ * Uh₀ᵀ * D.U j = D.U j) (hV : ∀ j, Vh₀ * Vh₀ᵀ * D.V j = D.V j)
    (hFV : ∀ j : Fin s, j.val + 1 < s →
      Uh₀ * Uh₀ᵀ * (F (t₀ + c j * h) (D.Y j) * D.V j) = F (t₀ + c j * h) (D.Y j) * D.V j)
    (hFU : ∀ j : Fin s, j.val + 1 < s →
      Vh₀ * Vh₀ᵀ * ((F (t₀ + c j * h) (D.Y j))ᵀ * D.U j) = (F (t₀ + c j * h) (D.Y j))ᵀ * D.U j)
    {Zs : Fin s → Matrix m n ℝ}
    (hZs : ∀ j, Zs j =
      Uh₀ * Uh₀ᵀ * F (t₀ + c j * h) (Y₀ + h • ∑ l, a j l • Zs l) * Vh₀ * Vh₀ᵀ) :
    (∀ j : Fin s, ‖D.Zb j - D.Z j‖ ≤ (ε + L * η) * (1 + L * h * α) ^ j.val) ∧
    (∀ j : Fin s, j.val + 1 < s →
      ‖Zs j - D.Zb j‖ ≤ (ε + L * η) * (1 + L * h * α) ^ j.val) ∧
    (∀ j : Fin s, j.val + 1 < s →
      ‖Zs j - D.Z j‖ ≤ 2 * ((ε + L * η) * (1 + L * h * α) ^ j.val)) := by
  refine stage_bound ha hα hF hL hh hε hη
    (isOrthProj_leftProj_mul_rightProj hUh₀ hVh₀) D.hZ
    (fun j => by rw [hZs j]; simp [Matrix.mul_assoc]) D.norm_F_sub_le D.hY ?_
  intro j hj
  rw [D.hZb j, mul_apply_eq_comp,
    rightProj_tangentProj_fix (hV j) (hFU j hj), leftProj_tangentProj_fix (hU j) (hFV j hj)]

/-- **Lemma 5 of arXiv 2608.27749 (the augmented parallel bases capture the exact solution).**
Let `Û = [Û₀, Ũ₂]`, `V̂ = [V̂₀, Ṽ₂]` be the augmented bases of the parallel BUG-p integrator
(orthonormal columns; `hUaug`, `hVaug`: they contain `Û₀`, `V̂₀`), where `Ũ₂`, `Ṽ₂` come from the
exact end values of the K- and L-step flows, `Kend = K(t₁)V̂₀ᵀ` and `Lend = Û₀ L(t₁)ᵀ`:
`hKend` says `Û Ûᵀ` fixes `(I - Û₀Û₀ᵀ) Kend`, `hLend` says `V̂ V̂ᵀ` fixes the rows of
`Lend (I - V̂₀V̂₀ᵀ)`.  The stages satisfy the hypotheses of Lemmas 3-4 (A1, A3, and, **conditional
on** Lemma 1, the basis containments `hU`, `hV`, `hFV`, `hFU`).  The order
`p` of the Runge-Kutta method is used exactly as in the paper: `hRK` is the local error
`‖A(t₁) - A₁‖ ≤ CA h^{p+1}` of the full method `A₁ = Y₀ + h ∑ bᵢ Zᵢ`, `hK`/`hL'` those of the
Runge-Kutta method applied to the K- and L-step (`Y₁⁽ᴷ⁾ - K(t₁)V̂₀ᵀ = O(h^{p+1})`).  Then
`‖A(t₁) - Û Ûᵀ A(t₁) V̂ V̂ᵀ‖ ≤ (2CA + CK + CL) h^{p+1} + 2 β h (ε + L η)(1 + x)^s (2 + 3x)`,
with `x = L h α`, `β ≥ ∑ |bᵢ|`: `c₁ h^{p+1} + c₂ h ε_r` of the paper (see `lemma5_paper_form`
for `η = 0` and `h ≤ H`).  Differences: explicit constants; the truncation defect `η` of the stage
points (`η = 0` in the paper); the constants `CA, CK, CL` of the order-`p` property are
hypotheses (they depend on bounds on derivatives, which the paper hides in `O(h^{p+1})`);
A2 is not needed. -/
theorem lemma5 {r ku kv wu wv : Type*} [Fintype r] [Fintype ku] [DecidableEq ku] [Fintype kv]
    [DecidableEq kv] [Fintype wu] [DecidableEq wu] [Fintype wv] [DecidableEq wv]
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L ε η h t₀ α β : ℝ}
    {a : Fin s → Fin s → ℝ} {b c : Fin s → ℝ} (ha : ∀ j l, j ≤ l → a j l = 0)
    (hα : ∀ j, ∑ l, |a j l| ≤ α) (hα0 : 0 ≤ α) (hβ : ∑ i, |b i| ≤ β)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hh : 0 ≤ h) (hε : 0 ≤ ε) (hη : 0 ≤ η)
    {Y₀ : Matrix m n ℝ} (D : StageData r F a c Y₀ t₀ h ε η)
    {Uh₀ : Matrix m ku ℝ} {Vh₀ : Matrix n kv ℝ} {Uh : Matrix m wu ℝ} {Vh : Matrix n wv ℝ}
    (hUh₀ : Uh₀ᵀ * Uh₀ = 1) (hVh₀ : Vh₀ᵀ * Vh₀ = 1) (hUh : Uhᵀ * Uh = 1)
    (hVh : Vhᵀ * Vh = 1)
    (hU : ∀ j, Uh₀ * Uh₀ᵀ * D.U j = D.U j) (hV : ∀ j, Vh₀ * Vh₀ᵀ * D.V j = D.V j)
    (hFV : ∀ j : Fin s, j.val + 1 < s →
      Uh₀ * Uh₀ᵀ * (F (t₀ + c j * h) (D.Y j) * D.V j) = F (t₀ + c j * h) (D.Y j) * D.V j)
    (hFU : ∀ j : Fin s, j.val + 1 < s →
      Vh₀ * Vh₀ᵀ * ((F (t₀ + c j * h) (D.Y j))ᵀ * D.U j) = (F (t₀ + c j * h) (D.Y j))ᵀ * D.U j)
    (hUaug : Uh * Uhᵀ * Uh₀ = Uh₀) (hVaug : Vh * Vhᵀ * Vh₀ = Vh₀)
    {Zt Zl : Fin s → Matrix m n ℝ}
    (hZt : ∀ j, Zt j = F (t₀ + c j * h) (Y₀ + h • ∑ l, a j l • Zt l) * Vh₀ * Vh₀ᵀ)
    (hZl : ∀ j, Zl j = Uh₀ * Uh₀ᵀ * F (t₀ + c j * h) (Y₀ + h • ∑ l, a j l • Zl l))
    {Kend Lend Aend : Matrix m n ℝ}
    (hKend : Uh * Uhᵀ * ((1 - Uh₀ * Uh₀ᵀ) * Kend) = (1 - Uh₀ * Uh₀ᵀ) * Kend)
    (hLend : Lend * (1 - Vh₀ * Vh₀ᵀ) * (Vh * Vhᵀ) = Lend * (1 - Vh₀ * Vh₀ᵀ))
    {p : ℕ} {CA CK CL : ℝ}
    (hRK : ‖Aend - (Y₀ + h • ∑ i, b i • D.Z i)‖ ≤ CA * h ^ (p + 1))
    (hK : ‖(Y₀ + h • ∑ i, b i • Zt i) - Kend‖ ≤ CK * h ^ (p + 1))
    (hL' : ‖(Y₀ + h • ∑ i, b i • Zl i) - Lend‖ ≤ CL * h ^ (p + 1)) :
    ‖Aend - Uh * Uhᵀ * Aend * Vh * Vhᵀ‖ ≤ (2 * CA + CK + CL) * h ^ (p + 1) +
      2 * (β * (h * (ε + L * η)) * ((1 + L * h * α) ^ s * (2 + 3 * (L * h * α)))) := by
  have sV₀ : (Vh₀ * Vh₀ᵀ)ᵀ = Vh₀ * Vh₀ᵀ := by simp [Matrix.transpose_mul]
  have sV : (Vh * Vhᵀ)ᵀ = Vh * Vhᵀ := by simp [Matrix.transpose_mul]
  -- the K-branch: measure `(1 - Û Ûᵀ)` against the right mask `V̂₀ V̂₀ᵀ`
  have PU : ∀ j, Uh * Uhᵀ * D.U j = D.U j := fun j => comp_fix (aug_fix hUaug) (hU j)
  have hQV₀ : ∀ j, (D.V j)ᵀ * (Vh₀ * Vh₀ᵀ) = (D.V j)ᵀ := fun j => transpose_fix sV₀ (hV j)
  have hKfix : leftProj Uh Kend = Kend := by
    rw [leftProj_apply]; exact aug_fix_left (aug_fix hUaug) hKend
  have hlastK : ∀ j : Fin s, ¬ (j.val + 1 < s) →
      (1 - leftProj Uh) ((1 - rightProj Vh₀) (D.Zb j)) = 0 := by
    intro j _
    rw [one_sub_rightProj_apply, one_sub_leftProj_apply, D.hZb j]
    exact normal_tangentProj_eq_zero _ (PU j) (hQV₀ j)
  have B1 := capture_bound (M := rightProj Vh₀) (N := leftProj Uh) ha hα hβ hα0 hF hL hh hε hη
    (isOrthProj_rightProj (m := m) hVh₀) (isOrthProj_leftProj (n := n) hUh) D.hZ
    (fun j => (hZt j).trans (rightProj_apply _ _).symm) D.norm_F_sub_le D.hY
    (fun j hj => by rw [D.hZb j]; exact rightProj_tangentProj_fix (hV j) (hFU j hj))
    hlastK rfl rfl hRK hK hKfix
  -- the L-branch: measure `(1 - V̂ V̂ᵀ)` against the left mask `Û₀ Û₀ᵀ`
  have QV : ∀ j, Vh * Vhᵀ * D.V j = D.V j := fun j => comp_fix (aug_fix hVaug) (hV j)
  have hVQ : ∀ j, (D.V j)ᵀ * (Vh * Vhᵀ) = (D.V j)ᵀ := fun j => transpose_fix sV (QV j)
  have hLfix : rightProj Vh Lend = Lend := by
    rw [rightProj_apply']
    exact aug_fix_right (by rw [Matrix.mul_assoc, transpose_fix sV hVaug]) hLend
  have hlastL : ∀ j : Fin s, ¬ (j.val + 1 < s) →
      (1 - rightProj Vh) ((1 - leftProj Uh₀) (D.Zb j)) = 0 := by
    intro j _
    rw [one_sub_leftProj_apply, one_sub_rightProj_apply, Matrix.mul_assoc, D.hZb j]
    exact normal_tangentProj_eq_zero _ (hU j) (hVQ j)
  have B2 := capture_bound (M := leftProj Uh₀) (N := rightProj Vh) ha hα hβ hα0 hF hL hh hε hη
    (isOrthProj_leftProj (n := n) hUh₀) (isOrthProj_rightProj (m := m) hVh) D.hZ
    (fun j => (hZl j).trans (leftProj_apply _ _).symm) D.norm_F_sub_le D.hY
    (fun j hj => by rw [D.hZb j]; exact leftProj_tangentProj_fix (hU j) (hFV j hj))
    hlastL rfl rfl hRK hL' hLfix
  have hsplit : Aend - Uh * Uhᵀ * Aend * Vh * Vhᵀ =
      (Aend - leftProj Uh Aend) + leftProj Uh (Aend - rightProj Vh Aend) := by
    simp only [leftProj_apply, rightProj_apply, Matrix.mul_sub, Matrix.mul_assoc]; abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have := (isOrthProj_leftProj (n := n) hUh).norm_le (Aend - rightProj Vh Aend)
  linarith

/-- **Lemma 5 of arXiv 2608.27749, in the paper's form** `c₁ h^{p+1} + c₂ h ε_r`.  Exactly
`lemma5` with `η = 0` (the paper's identification `Y_(j) = Y₀ + h ∑ aⱼₗ Z̄ₗ`) and `0 ≤ h ≤ H`:
the constant `c₂ = 2 β (1 + L H α)^s (2 + 3 L H α)` does not depend on `h`, and
`c₁ = 2 CA + CK + CL`. -/
theorem lemma5_paper_form {r ku kv wu wv : Type*} [Fintype r] [Fintype ku] [DecidableEq ku]
    [Fintype kv] [DecidableEq kv] [Fintype wu] [DecidableEq wu] [Fintype wv] [DecidableEq wv]
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L ε h H t₀ α β : ℝ}
    {a : Fin s → Fin s → ℝ} {b c : Fin s → ℝ} (ha : ∀ j l, j ≤ l → a j l = 0)
    (hα : ∀ j, ∑ l, |a j l| ≤ α) (hα0 : 0 ≤ α) (hβ : ∑ i, |b i| ≤ β) (hβ0 : 0 ≤ β)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hh : 0 ≤ h) (hH : h ≤ H) (hε : 0 ≤ ε)
    {Y₀ : Matrix m n ℝ} (D : StageData r F a c Y₀ t₀ h ε 0)
    {Uh₀ : Matrix m ku ℝ} {Vh₀ : Matrix n kv ℝ} {Uh : Matrix m wu ℝ} {Vh : Matrix n wv ℝ}
    (hUh₀ : Uh₀ᵀ * Uh₀ = 1) (hVh₀ : Vh₀ᵀ * Vh₀ = 1) (hUh : Uhᵀ * Uh = 1)
    (hVh : Vhᵀ * Vh = 1)
    (hU : ∀ j, Uh₀ * Uh₀ᵀ * D.U j = D.U j) (hV : ∀ j, Vh₀ * Vh₀ᵀ * D.V j = D.V j)
    (hFV : ∀ j : Fin s, j.val + 1 < s →
      Uh₀ * Uh₀ᵀ * (F (t₀ + c j * h) (D.Y j) * D.V j) = F (t₀ + c j * h) (D.Y j) * D.V j)
    (hFU : ∀ j : Fin s, j.val + 1 < s →
      Vh₀ * Vh₀ᵀ * ((F (t₀ + c j * h) (D.Y j))ᵀ * D.U j) = (F (t₀ + c j * h) (D.Y j))ᵀ * D.U j)
    (hUaug : Uh * Uhᵀ * Uh₀ = Uh₀) (hVaug : Vh * Vhᵀ * Vh₀ = Vh₀)
    {Zt Zl : Fin s → Matrix m n ℝ}
    (hZt : ∀ j, Zt j = F (t₀ + c j * h) (Y₀ + h • ∑ l, a j l • Zt l) * Vh₀ * Vh₀ᵀ)
    (hZl : ∀ j, Zl j = Uh₀ * Uh₀ᵀ * F (t₀ + c j * h) (Y₀ + h • ∑ l, a j l • Zl l))
    {Kend Lend Aend : Matrix m n ℝ}
    (hKend : Uh * Uhᵀ * ((1 - Uh₀ * Uh₀ᵀ) * Kend) = (1 - Uh₀ * Uh₀ᵀ) * Kend)
    (hLend : Lend * (1 - Vh₀ * Vh₀ᵀ) * (Vh * Vhᵀ) = Lend * (1 - Vh₀ * Vh₀ᵀ))
    {p : ℕ} {CA CK CL : ℝ}
    (hRK : ‖Aend - (Y₀ + h • ∑ i, b i • D.Z i)‖ ≤ CA * h ^ (p + 1))
    (hK : ‖(Y₀ + h • ∑ i, b i • Zt i) - Kend‖ ≤ CK * h ^ (p + 1))
    (hL' : ‖(Y₀ + h • ∑ i, b i • Zl i) - Lend‖ ≤ CL * h ^ (p + 1)) :
    ‖Aend - Uh * Uhᵀ * Aend * Vh * Vhᵀ‖ ≤ (2 * CA + CK + CL) * h ^ (p + 1) +
      (2 * β * ((1 + L * H * α) ^ s * (2 + 3 * (L * H * α)))) * (h * ε) := by
  refine (lemma5 ha hα hα0 hβ hF hL hh hε le_rfl D hUh₀ hVh₀ hUh hVh hU hV hFV hFU hUaug hVaug
    hZt hZl hKend hLend hRK hK hL').trans ?_
  have hLα : 0 ≤ L * α := mul_nonneg hL hα0
  have h1 : (1 + L * h * α) ^ s ≤ (1 + L * H * α) ^ s := by
    refine pow_le_pow_left₀ (by nlinarith) ?_ s
    nlinarith
  have h2 : 2 + 3 * (L * h * α) ≤ 2 + 3 * (L * H * α) := by nlinarith
  have h3 : (1 + L * h * α) ^ s * (2 + 3 * (L * h * α)) ≤
      (1 + L * H * α) ^ s * (2 + 3 * (L * H * α)) :=
    mul_le_mul h1 h2 (by nlinarith) (pow_nonneg (by nlinarith) s)
  have h4 : 0 ≤ β * (h * ε) := mul_nonneg hβ0 (mul_nonneg hh hε)
  have h5 := mul_le_mul_of_nonneg_left h3 h4
  simp only [mul_zero, add_zero]
  nlinarith [h5]

end Parallel

section Example

open scoped LeanDLRA.Frobenius

/-- **Non-vacuity of `lemma5`.**  A scalar (`1 × 1`) instance with `F ≡ 1`, explicit Euler
(`s = 1`), all bases equal to `1`: every hypothesis of `lemma5` (orthonormal bases, range
inclusions, A1, A3, order conditions, the K- and L-step stage equations) holds with
`ε = η = 0`, so the theorem applies and yields the (here exact) capture bound. -/
example (t₀ h : ℝ) (hh : 0 ≤ h) :
    ‖(h • 1 : Matrix (Fin 1) (Fin 1) ℝ) - 1 * 1ᵀ * (h • 1) * 1 * 1ᵀ‖ ≤
      (2 * 0 + 0 + 0) * h ^ (1 + 1) +
      2 * (1 * (h * (0 + 0 * 0)) * ((1 + 0 * h * 0) ^ 1 * (2 + 3 * (0 * h * 0)))) := by
  let F : ℝ → Matrix (Fin 1) (Fin 1) ℝ → Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => 1
  let D : StageData (s := 1) (Fin 1) F (fun _ _ => (0 : ℝ)) (fun _ => (0 : ℝ)) 0 t₀ h 0 0 :=
    { Z := fun _ => 1
      U := fun _ => 1
      V := fun _ => 1
      Y := fun _ => 0
      Zb := fun _ => 1
      hZ := fun _ => rfl
      hZb := fun _ => by simp [F, tangentProj_apply]
      hA3 := fun _ => by simp
      hY := fun _ => by simp }
  have hF : IsLipschitzField F 0 := fun t x y => by simp [F]
  have := lemma5 (F := F) (L := 0) (ε := 0) (η := 0) (h := h) (t₀ := t₀) (α := 0) (β := 1)
    (a := fun _ _ => 0) (b := fun _ => 1) (c := fun _ => 0) (s := 1)
    (fun j l _ => rfl) (fun j => by simp) le_rfl (by simp) hF le_rfl hh le_rfl le_rfl D
    (Uh₀ := (1 : Matrix (Fin 1) (Fin 1) ℝ)) (Vh₀ := (1 : Matrix (Fin 1) (Fin 1) ℝ))
    (Uh := (1 : Matrix (Fin 1) (Fin 1) ℝ)) (Vh := (1 : Matrix (Fin 1) (Fin 1) ℝ))
    (by simp) (by simp) (by simp) (by simp)
    (fun j => by simp [D]) (fun j => by simp [D]) (fun j _ => by simp [F, D])
    (fun j _ => by simp [F, D]) (by simp) (by simp)
    (Zt := fun _ => 1) (Zl := fun _ => 1) (fun j => by simp [F])
    (fun j => by simp [F]) (Kend := (h • 1 : Matrix (Fin 1) (Fin 1) ℝ))
    (Lend := (h • 1 : Matrix (Fin 1) (Fin 1) ℝ))
    (Aend := (h • 1 : Matrix (Fin 1) (Fin 1) ℝ)) (by simp) (by simp)
    (p := 1) (CA := 0) (CK := 0) (CL := 0) (by simp [D]) (by simp) (by simp)
  exact this

end Example




end LeanDLRA.Literature.P2608_27749
