import LeanDLRA.Integrators.RankAdaptiveBUG
import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Classical.BestApproximation
import LeanDLRA.Dynamics.ContinuousDLRA

/-!
# Growth of the distance to the matrices of rank at most `r` along the exact flow

`distLR r X` is the Frobenius distance of `X` to the matrices of rank at most `r`. For an
`L`-Lipschitz, bounded field whose normal part at factored matrices of rank `r` is at most `ε`
(`MatrixBUG.FactoredNormalBound F r ε`), this distance satisfies along every exact solution a bound
of Grönwall type with the constant one in front of `ε`, without a condition on the rank of the
starting value.

## Main results

* `distLR_flow_le_exp_mul_add`: for an exact solution `A` on `[t₀, t₁]`,
  `distLR r (A t) ≤ e^{L (t - t₀)} distLR r (A t₀) + ε (t - t₀) e^{L (t - t₀)}`.
* `distLR_flow_le_sharp`: the same statement with the additional hypothesis that the field is
  continuous in time.

## Implementation notes

The bound is an upper bound, and continuity of the field in time is not needed for it. For a
start of rank at most `r` it gives `h ε e^{L h}` after time `h`, half of the bound
`2 h ε e^{L h}` of `distLR_flow_le_exp`. That the constant in front of `ε` cannot be lowered is
not proved here: for the constant field `F ≡ [[0, 1], [1, 0]]` (`L = 0`, `r = 1`) the library
certifies the lower bound `t / 3` for the distance of `A t = t F` (`le_distLR_cx`), not its
exact value. The smaller expression `ε (e^{L τ} - 1) / L` in the place of `ε τ e^{L τ}` is not
proved here; the form stated needs no separate case `L = 0`.
-/

open Set Finset Matrix

namespace LeanDLRA

section Truncation

open scoped LeanDLRA.Frobenius
open EckartYoung

variable {m n : Type*} [Fintype m] [Fintype n]

end Truncation

section Tie

open EckartYoung

end Tie

section Distance

open scoped LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L B ε t₀ t₁ : ℝ} {A : ℝ → Matrix m n ℝ}

omit [DecidableEq m] [DecidableEq n] in
/-- A nearest point at positive distance has full rank: otherwise adding one entry of the residual
would give a strictly better approximation of rank `≤ r`. -/
private theorem le_rank_of_best {X Z : Matrix m n ℝ} (hXZ : ‖X - Z‖ = distLR r X)
    (hpos : 0 < distLR r X) : r ≤ Z.rank := by
  classical
  by_contra hlt
  have hlt' : Z.rank + 1 ≤ r := by omega
  have hW : X - Z ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hXZ
    linarith
  obtain ⟨i, j, hij⟩ : ∃ i j, (X - Z) i j ≠ 0 := by
    by_contra hall
    exact hW (Matrix.ext fun i j => by
      by_contra hij
      exact hall ⟨i, j, hij⟩)
  set c := (X - Z) i j with hcdef
  set E : Matrix m n ℝ := Matrix.vecMulVec (Pi.single i c) (Pi.single j 1) with hE
  have hEapply : ∀ k l, E k l = if k = i then (if l = j then c else 0) else 0 := by
    intro k l
    by_cases hk : k = i <;> by_cases hl : l = j <;>
      simp [hE, Matrix.vecMulVec_apply, hk, hl]
  have hErank : E.rank ≤ 1 := Matrix.rank_vecMulVec_le _ _
  have hZ' : (Z + E).rank ≤ r := (EckartYoung.rank_add_le _ _).trans (by omega)
  have h1 := distLR_le_norm_sub (X := X) hZ'
  have h2 : ‖X - (Z + E)‖ ^ 2 = ‖X - Z‖ ^ 2 - c ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum, Frobenius.norm_sq_eq_sum]
    have hpt : ∀ k l, (X - (Z + E)) k l ^ 2 =
        (X - Z) k l ^ 2 - (if k = i then (if l = j then c ^ 2 else 0) else 0) := by
      intro k l
      have : (X - (Z + E)) k l = (X - Z) k l - E k l := by
        simp only [Matrix.sub_apply, Matrix.add_apply]; ring
      rw [this, hEapply]
      by_cases hk : k = i
      · by_cases hl : l = j
        · subst hk hl
          simp only [ite_true, ← hcdef]
          ring
        · simp [hk, hl]
      · simp [hk]
    simp only [hpt, Finset.sum_sub_distrib]
    simp
  have hc2 : 0 < c ^ 2 := by positivity
  have h3 : ‖X - (Z + E)‖ ^ 2 < ‖X - Z‖ ^ 2 := by linarith
  have h4 : ‖X - (Z + E)‖ < ‖X - Z‖ := lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h3
  linarith

omit [DecidableEq m] [DecidableEq n] in
/-- A matrix of rank exactly `r` is `U S Vᵀ` with orthonormal `U`, `V` and invertible `S`. -/
private theorem exists_factor_of_rank_eq {Z : Matrix m n ℝ} (hZ : Z.rank = r)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) :
    ∃ (U : Matrix m (Fin r) ℝ) (S T : Matrix (Fin r) (Fin r) ℝ) (V : Matrix n (Fin r) ℝ),
      Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ Z = U * S * Vᵀ ∧ S * T = 1 ∧ T * S = 1 := by
  obtain ⟨U, S, V, hU, hV, hZf⟩ := exists_factor_of_rank_le hZ.le hrm hrn
  have hrS : r ≤ S.rank := by
    have h : Z.rank ≤ S.rank := by
      rw [hZf]
      exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
    omega
  have hcard : S.rank = Fintype.card (Fin r) := by
    rw [Fintype.card_fin]
    exact le_antisymm (by simpa using S.rank_le_card_width) hrS
  have hunit : IsUnit S :=
    Matrix.mulVec_surjective_iff_isUnit.1 (Matrix.mulVec_surjective_iff_rank_eq_card.2 hcard)
  refine ⟨U, S, S⁻¹, V, hU, hV, hZf, ?_, ?_⟩
  · exact Matrix.mul_nonsing_inv S ((Matrix.isUnit_iff_isUnit_det S).1 hunit)
  · exact Matrix.nonsing_inv_mul S ((Matrix.isUnit_iff_isUnit_det S).1 hunit)

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- A product through `Fin r` has rank at most `r`. -/
private theorem rank_mul_fin_le (X : Matrix m (Fin r) ℝ) (Y : Matrix (Fin r) n ℝ) :
    (X * Y).rank ≤ r := by
  have h := (Matrix.rank_mul_le_left X Y).trans X.rank_le_card_width
  rwa [Fintype.card_fin] at h

/-- Expansion of the rank-`≤ r` curve `(U S + τ G V) T (S Vᵀ + τ Uᵀ G (1 - V Vᵀ))`, `T = S⁻¹`, whose
velocity at `τ = 0` is the tangential part `G - (1 - U Uᵀ) G (1 - V Vᵀ)` of `G`. -/
private theorem curve_expand (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ)
    (S T : Matrix (Fin r) (Fin r) ℝ) (G : Matrix m n ℝ) (hST : S * T = 1) (hTS : T * S = 1)
    (τ : ℝ) :
    (U * S + τ • (G * V)) * T * (S * Vᵀ + τ • (Uᵀ * G * (1 - V * Vᵀ))) =
      U * S * Vᵀ + τ • (G - (1 - U * Uᵀ) * G * (1 - V * Vᵀ)) +
        τ ^ 2 • (G * V * T * (Uᵀ * G * (1 - V * Vᵀ))) := by
  set R := Uᵀ * G * (1 - V * Vᵀ) with hR
  have h1 : (U * S + τ • (G * V)) * T = U + τ • (G * V * T) := by
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc U S T, hST, Matrix.mul_one]
  have h2 : G * V * T * (S * Vᵀ) = G * V * Vᵀ := by
    rw [Matrix.mul_assoc (G * V) T, ← Matrix.mul_assoc T S, hTS, Matrix.one_mul]
  have h3 : G - (1 - U * Uᵀ) * G * (1 - V * Vᵀ) = U * R + G * V * Vᵀ := by
    rw [hR, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.mul_one, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
    abel
  rw [h1, h3, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_smul, h2, Matrix.mul_assoc U S, sq, mul_smul, smul_add]
  abel

/-- **Right Dini bound at a point of positive distance**: if `0 < d(a) = dist(A(a), M_{≤ r})`, a
nearest point has rank exactly `r`, and comparing `A` with a curve through it inside `M_{≤ r}`
whose velocity is the tangential part of `F` there gives `D₊ d(a) ≤ L d(a) + ε`. -/
private theorem frequently_slope_distLR_lt (hF : IsLipschitzField F L)
    (hε : MatrixBUG.FactoredNormalBound F r ε) (hA : ODESolution F A t₀ t₁) {a ρ : ℝ}
    (ha : a ∈ Ico t₀ t₁) (hpos : 0 < distLR r (A a)) (hρ : L * distLR r (A a) + ε < ρ) :
    ∃ᶠ z in nhdsWithin a (Ioi a), slope (fun t => distLR r (A t)) a z < ρ := by
  obtain ⟨Z, hZ, hXZ⟩ := exists_best_approx r (A a)
  have hZr : Z.rank = r := le_antisymm hZ (le_rank_of_best hXZ hpos)
  have hr : r < (A a).rank := distLR_pos_iff.1 hpos
  obtain ⟨U, S, T, V, hU, hV, hZf, hST, hTS⟩ := exists_factor_of_rank_eq hZr
    (hr.le.trans (A a).rank_le_card_height) (hr.le.trans (A a).rank_le_card_width)
  set G := F a Z with hG
  set N := (1 - U * Uᵀ) * G * (1 - V * Vᵀ) with hN
  set R := Uᵀ * G * (1 - V * Vᵀ) with hR
  set Q := G * V * T * R with hQ
  have hNε : ‖N‖ ≤ ε := by
    rw [hN, hG, hZf]
    exact hε a U V S hU hV
  set c : ℝ → Matrix m n ℝ := fun z => A z - (Z + (z - a) • (G - N) + (z - a) ^ 2 • Q) with hc
  have hca : c a = A a - Z := by simp [hc]
  have hcurve : HasDerivAt (fun z : ℝ => Z + (z - a) • (G - N) + (z - a) ^ 2 • Q) (G - N) a := by
    have h1 : HasDerivAt (fun z : ℝ => z - a) 1 a := (hasDerivAt_id a).sub_const a
    have h2 : HasDerivAt (fun z : ℝ => (z - a) • (G - N)) ((1 : ℝ) • (G - N)) a :=
      h1.smul_const _
    have h3 : HasDerivAt (fun z : ℝ => (z - a) ^ 2) (((2 : ℕ) : ℝ) * (a - a) ^ (2 - 1) * 1) a :=
      h1.pow 2
    have h4 := (h2.const_add Z).fun_add (h3.smul_const Q)
    have e : (1 : ℝ) • (G - N) + (((2 : ℕ) : ℝ) * (a - a) ^ (2 - 1) * 1) • Q = G - N := by simp
    rwa [e] at h4
  have hderiv : HasDerivWithinAt c (F a (A a) - (G - N)) (Ici a) a :=
    (hA.deriv a ha).sub hcurve.hasDerivWithinAt
  have hnorm : ‖F a (A a) - (G - N)‖ < ρ := by
    have e : F a (A a) - (G - N) = (F a (A a) - G) + N := by abel
    rw [e]
    refine lt_of_le_of_lt ((norm_add_le _ _).trans (add_le_add (hF a _ _) hNε)) ?_
    rwa [hXZ]
  refine (hderiv.liminf_right_slope_norm_le hnorm).mp ?_
  filter_upwards [self_mem_nhdsWithin] with z hz hslope
  have hz0 : 0 < z - a := sub_pos.2 hz
  have hrank : (Z + (z - a) • (G - N) + (z - a) ^ 2 • Q).rank ≤ r := by
    have e := curve_expand U V S T G hST hTS (z - a)
    rw [← hZf, ← hN, ← hR, ← hQ] at e
    rw [← e]
    exact rank_mul_fin_le _ _
  have hle : distLR r (A z) ≤ ‖c z‖ := distLR_le_norm_sub hrank
  rw [hca, hXZ] at hslope
  rw [slope_def_field]
  have hinv : 0 < (z - a)⁻¹ := inv_pos.2 hz0
  calc (distLR r (A z) - distLR r (A a)) / (z - a)
      = (z - a)⁻¹ * (distLR r (A z) - distLR r (A a)) := by rw [div_eq_inv_mul]
    _ ≤ (z - a)⁻¹ * (‖c z‖ - distLR r (A a)) :=
        mul_le_mul_of_nonneg_left (by linarith) hinv.le
    _ < ρ := hslope

omit [DecidableEq m] [DecidableEq n] in
/-- The distance is `B`-Lipschitz along the flow, in the form of a right Dini bound. -/
private theorem frequently_slope_distLR_lt_of_bounded (hB : IsBoundedField F B)
    (hA : ODESolution F A t₀ t₁) {a ρ : ℝ} (ha : a ∈ Ico t₀ t₁) (hρ : B < ρ) :
    ∃ᶠ z in nhdsWithin a (Ioi a), slope (fun t => distLR r (A t)) a z < ρ := by
  have hderiv : HasDerivWithinAt (fun z => A z - A a) (F a (A a)) (Ici a) a :=
    (hA.deriv a ha).sub_const _
  refine (hderiv.liminf_right_slope_norm_le ((hB a _).trans_lt hρ)).mp ?_
  filter_upwards [self_mem_nhdsWithin] with z hz hslope
  have hz0 : 0 < z - a := sub_pos.2 hz
  have hle := distLR_le_add (r := r) (A z) (A a)
  simp only [sub_self, norm_zero, sub_zero] at hslope
  rw [slope_def_field]
  have hinv : 0 < (z - a)⁻¹ := inv_pos.2 hz0
  calc (distLR r (A z) - distLR r (A a)) / (z - a)
      = (z - a)⁻¹ * (distLR r (A z) - distLR r (A a)) := by rw [div_eq_inv_mul]
    _ ≤ (z - a)⁻¹ * ‖A z - A a‖ := mul_le_mul_of_nonneg_left (by linarith) hinv.le
    _ < ρ := hslope

/-- **Growth of the distance to `M_{≤ r}` along the exact flow, without continuity in time**
(the statement of `distLR_flow_le_sharp` without the hypothesis that the field is continuous in
time). For an `L`-Lipschitz field bounded by `B` with the factored normal-component bound `ε`,
along every exact solution, starting anywhere,
`dist(A(t), M_{≤ r}) ≤ e^{L(t - t₀)} dist(A(t₀), M_{≤ r}) + ε (t - t₀) e^{L(t - t₀)}`. This is
an upper bound; that the constant in front of `ε` is optimal is not proved. -/
theorem distLR_flow_le_exp_mul_add (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hε0 : 0 ≤ ε) (hε : MatrixBUG.FactoredNormalBound F r ε)
    (hA : ODESolution F A t₀ t₁) :
    ∀ t ∈ Icc t₀ t₁, distLR r (A t) ≤
      Real.exp (L * (t - t₀)) * distLR r (A t₀) + ε * (t - t₀) * Real.exp (L * (t - t₀)) := by
  intro t ht
  set d : ℝ → ℝ := fun s => distLR r (A s) with hd
  have hcont : ContinuousOn d (Icc t₀ t₁) :=
    (lipschitzWith_distLR r).continuous.comp_continuousOn hA.cont
  have hd0 : 0 ≤ d t₀ := distLR_nonneg
  have key : ∀ δ : ℝ, 0 < δ →
      d t ≤ Real.exp (L * (t - t₀)) * (d t₀ + δ + (ε + δ) * (t - t₀)) := by
    intro δ hδ
    set u : ℝ → ℝ := fun s => Real.exp (L * (s - t₀)) * (d t₀ + δ + (ε + δ) * (s - t₀)) with hu
    set u' : ℝ → ℝ := fun s => L * u s + Real.exp (L * (s - t₀)) * (ε + δ) with hu'
    set f' : ℝ → ℝ := fun s => if 0 < d s then L * d s + ε else B with hf'
    have hderiv : ∀ s, HasDerivAt u (u' s) s := by
      intro s
      have h1 : HasDerivAt (fun x : ℝ => L * (x - t₀)) L s := by
        simpa using ((hasDerivAt_id s).sub_const t₀).const_mul L
      have h2 : HasDerivAt (fun x : ℝ => d t₀ + δ + (ε + δ) * (x - t₀)) (ε + δ) s := by
        simpa using (((hasDerivAt_id s).sub_const t₀).const_mul (ε + δ)).const_add (d t₀ + δ)
      have h3 := h1.exp.mul h2
      convert h3 using 1
      simp only [hu', hu]
      ring
    refine image_le_of_liminf_slope_right_lt_deriv_boundary' (f := d) (f' := f') (B := u)
      (B' := u') hcont ?_ ?_ ?_ (fun s _ => (hderiv s).hasDerivWithinAt) ?_ ht
    · intro x hx ρ hρ
      by_cases hx0 : 0 < d x
      · have hρ' : L * d x + ε < ρ := by simpa only [hf', hx0, ↓reduceIte] using hρ
        exact frequently_slope_distLR_lt hF hε hA hx hx0 hρ'
      · have hρ' : B < ρ := by simpa only [hf', hx0, ↓reduceIte] using hρ
        exact frequently_slope_distLR_lt_of_bounded hB hA hx hρ'
    · simp only [hu, sub_self, mul_zero, Real.exp_zero, one_mul, add_zero]
      linarith
    · exact fun s _ => (hderiv s).continuousAt.continuousWithinAt
    · intro x hx hdx
      have hx0 : 0 ≤ x - t₀ := sub_nonneg.2 hx.1
      have hexp : 1 ≤ Real.exp (L * (x - t₀)) := Real.one_le_exp (mul_nonneg hL hx0)
      have hu0 : 0 < u x := by
        have : 0 < d t₀ + δ + (ε + δ) * (x - t₀) := by positivity
        exact mul_pos (Real.exp_pos _) this
      have hfx : f' x = L * u x + ε := by simp only [hf', hdx, hu0, ↓reduceIte]
      have : ε < Real.exp (L * (x - t₀)) * (ε + δ) := by nlinarith
      simp only [hfx, hu']
      linarith
  have ht0 : 0 ≤ t - t₀ := sub_nonneg.2 ht.1
  apply le_of_forall_pos_le_add
  intro η hη
  set K := Real.exp (L * (t - t₀)) * (1 + (t - t₀)) with hK
  have hKpos : 0 < K := mul_pos (Real.exp_pos _) (by linarith)
  have h := key (η / K) (by positivity)
  have e : Real.exp (L * (t - t₀)) * (d t₀ + η / K + (ε + η / K) * (t - t₀)) =
      Real.exp (L * (t - t₀)) * d t₀ + ε * (t - t₀) * Real.exp (L * (t - t₀)) + η := by
    have e' : η = K * (η / K) := by field_simp
    calc Real.exp (L * (t - t₀)) * (d t₀ + η / K + (ε + η / K) * (t - t₀))
        = Real.exp (L * (t - t₀)) * d t₀ + ε * (t - t₀) * Real.exp (L * (t - t₀)) +
            K * (η / K) := by rw [hK]; ring
      _ = _ := by rw [← e']
  rw [e] at h
  exact h

/-- **Growth of the distance to `M_{≤ r}` with the constant one in front of `ε`.** Along every
exact solution, starting anywhere,
`dist(A(t), M_{≤ r}) ≤ e^{L(t - t₀)} dist(A(t₀), M_{≤ r}) + ε (t - t₀) e^{L(t - t₀)}`, with `ε`
the factored normal-component bound. This is an upper bound. For `F ≡ [[0,1],[1,0]]` (`L = 0`,
`r = 1`) and the solution `A(t) = t F` from `0`, `le_distLR_cx` with `δ = 0` certifies the lower
bound `t/3` for the distance to `M_{≤ 1}`; its exact value is not formalised, so the constant is
not proved to be optimal. The smaller expression `ε (e^{L τ} - 1)/L` is not proved here; the
form stated needs no separate case `L = 0`.
This is the recorded form of the statement, with the redundant hypothesis that the field is
continuous in time; `distLR_flow_le_exp_mul_add` is the same statement without it. -/
theorem distLR_flow_le_sharp (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hc : ∀ Y, Continuous fun t => F t Y) (hε0 : 0 ≤ ε) (hε : MatrixBUG.FactoredNormalBound F r ε)
    (hA : ODESolution F A t₀ t₁) :
    ∀ t ∈ Icc t₀ t₁, distLR r (A t) ≤
      Real.exp (L * (t - t₀)) * distLR r (A t₀) + ε * (t - t₀) * Real.exp (L * (t - t₀)) := by
  have _ := hc
  exact distLR_flow_le_exp_mul_add hF hL hB hε0 hε hA

/-- The hypotheses of `distLR_flow_le_exp_mul_add` hold for the constant field
`F ≡ [[0, 1], [1, 0]]` (`L = 0`, `B = ε = ‖F‖`, `r = 1`) and the solution `A t = Y₀ + t F` from
`Y₀ = diag(δ, 0)`. -/
example (δ h : ℝ) : ∀ t ∈ Icc (0 : ℝ) h,
    distLR 1 (cxY₀ δ + (t - 0) • swapMat) ≤
      Real.exp (0 * (t - 0)) * distLR 1 (cxY₀ δ + ((0 : ℝ) - 0) • swapMat) +
        ‖swapMat‖ * (t - 0) * Real.exp (0 * (t - 0)) := by
  have hA : ODESolution (fun _ _ => swapMat) (fun t => cxY₀ δ + (t - 0) • swapMat) 0 h :=
    MatrixBUG.odeSolution_affine (cxY₀ δ) swapMat 0 h
  have hFL : IsLipschitzField (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => swapMat) 0 :=
    fun _ _ _ => by simp
  have hFB : IsBoundedField (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => swapMat) ‖swapMat‖ :=
    fun _ _ => le_rfl
  have hε : MatrixBUG.FactoredNormalBound
      (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => swapMat) 1 ‖swapMat‖ :=
    MatrixBUG.factoredNormalBound_const swapMat 1
  have key := distLR_flow_le_exp_mul_add hFL le_rfl hFB (norm_nonneg _) hε hA
  exact key

end Distance

section Galerkin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {F : ℝ → E → E} {L t₀ t₁ : ℝ} {A : ℝ → E}

end Galerkin

section RankAdaptive

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {F : ℝ → E → E} {L B ε : ℝ}

end RankAdaptive

section QuasiOptimal

open scoped LeanDLRA.Frobenius
open EckartYoung

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

end QuasiOptimal

end LeanDLRA
