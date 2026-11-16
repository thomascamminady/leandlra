import LeanDLRA.OpenProblems.RankAdaptivity.MainDefs
import LeanDLRA.Integrators.RankAdaptiveBUG
import LeanDLRA.Integrators.ParallelBUG
import LeanDLRA.Integrators.Matrix.BUG
import LeanDLRA.Matrix.LowRankDistance
import LeanDLRA.Classical.WeylSingular
import LeanDLRA.Classical.SVD
import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Classical.BestApproximation
import LeanDLRA.Stability.Conservation
import LeanDLRA.Training.Descent
import LeanDLRA.Foundations.OneSided
import LeanDLRA.Foundations.Gronwall

/-!
# `distLR_flow_le_dini_local`
-/

open Set Finset Matrix
open scoped RealInnerProductSpace

namespace LeanDLRA.OpenProblems.RankAdaptivity

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Abstract

section Counting

end Counting

section Matrices

open scoped LeanDLRA.Frobenius
open EckartYoung WeylSingular Curvature MatrixBUG

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Away from the low-rank set a nearest point has rank exactly `r`: otherwise, adding the single
matrix entry of `X - Z` at a position where it does not vanish costs one rank and gets closer. -/
private theorem rank_eq_of_nearest {r : ℕ} {X Z : Matrix m n ℝ} (hZ : Z.rank ≤ r)
    (hXZ : ‖X - Z‖ = distLR r X) (hpos : 0 < distLR r X) : Z.rank = r := by
  classical
  by_contra hne
  have hlt : Z.rank < r := lt_of_le_of_ne hZ hne
  have hE0 : X - Z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hXZ
    linarith
  obtain ⟨i, j, hij⟩ : ∃ i j, (X - Z) i j ≠ 0 := by
    by_contra! hall
    exact hE0 (Matrix.ext hall)
  set E := X - Z with hE
  set c := E i j with hc
  set T : Matrix m n ℝ := Matrix.vecMulVec (Pi.single i c) (Pi.single j 1) with hT
  have hTr : T.rank ≤ 1 := Matrix.rank_vecMulVec_le _ _
  have hYr : (Z + T).rank ≤ r := (rank_add_le Z T).trans (by omega)
  have h1 : distLR r X ≤ ‖X - (Z + T)‖ := distLR_le_norm_sub hYr
  have hent : ∀ a b, (X - (Z + T)) a b ^ 2 =
      E a b ^ 2 - (if a = i then (if b = j then c ^ 2 else 0) else 0) := by
    intro a b
    have hab : (X - (Z + T)) a b = E a b - T a b := by
      simp only [hE, Matrix.sub_apply, Matrix.add_apply]
      ring
    rw [hab]
    by_cases ha : a = i
    · subst ha
      by_cases hb : b = j
      · subst hb
        simp [hT, Matrix.vecMulVec_apply, hc]
      · simp [hT, Matrix.vecMulVec_apply, hb]
    · simp [hT, Matrix.vecMulVec_apply, ha]
  have h2 : ‖X - (Z + T)‖ ^ 2 = ‖E‖ ^ 2 - c ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum, Frobenius.norm_sq_eq_sum]
    simp only [hent, Finset.sum_sub_distrib]
    simp
  have h3 : 0 < c ^ 2 := by positivity
  rw [← hXZ] at h1
  have h4 := pow_le_pow_left₀ (norm_nonneg E) h1 2
  linarith

/-- **The rank-preserving curve.**  For `Z = U S Vᵀ` with invertible `S` and every `W`, the curve
`(1 + τ B) Z (1 + τ C)` with `B = (1 - UUᵀ) W Z⁺`, `C = Z⁺ W` has velocity
`W - (1 - UUᵀ) W (1 - VVᵀ)` at `τ = 0`, is a quadratic polynomial in `τ`, and stays of rank at most
`rank Z`, whatever the size of the singular values of `S` is. -/
private theorem exists_rank_curve [DecidableEq m] [DecidableEq n] {r : ℕ}
    {U : Matrix m (Fin r) ℝ} {V : Matrix n (Fin r) ℝ} {S : Matrix (Fin r) (Fin r) ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hS : IsUnit S.det) (W : Matrix m n ℝ) :
    ∃ G : Matrix m n ℝ, ∀ τ : ℝ,
      (U * S * Vᵀ + τ • (W - (1 - U * Uᵀ) * W * (1 - V * Vᵀ)) + τ ^ 2 • G).rank ≤
        (U * S * Vᵀ).rank := by
  set Z := U * S * Vᵀ with hZ
  set Zp : Matrix n m ℝ := V * S⁻¹ * Uᵀ with hZp
  set P : Matrix m m ℝ := U * Uᵀ with hP
  set Q : Matrix n n ℝ := V * Vᵀ with hQ
  have hZZp : Z * Zp = P := by
    calc Z * Zp = U * S * (Vᵀ * V) * S⁻¹ * Uᵀ := by simp only [hZ, hZp, Matrix.mul_assoc]
      _ = U * (S * S⁻¹) * Uᵀ := by rw [hV, Matrix.mul_one, Matrix.mul_assoc U]
      _ = P := by rw [Matrix.mul_nonsing_inv _ hS, Matrix.mul_one]
  have hZpZ : Zp * Z = Q := by
    calc Zp * Z = V * S⁻¹ * (Uᵀ * U) * S * Vᵀ := by simp only [hZ, hZp, Matrix.mul_assoc]
      _ = V * (S⁻¹ * S) * Vᵀ := by rw [hU, Matrix.mul_one, Matrix.mul_assoc V]
      _ = Q := by rw [Matrix.nonsing_inv_mul _ hS, Matrix.mul_one]
  set B : Matrix m m ℝ := (1 - P) * W * Zp with hB
  set C : Matrix n n ℝ := Zp * W with hC
  have hBZ : B * Z = (1 - P) * W * Q := by
    rw [hB, Matrix.mul_assoc, hZpZ]
  have hZC : Z * C = P * W := by
    rw [hC, ← Matrix.mul_assoc, hZZp]
  refine ⟨B * Z * C, fun τ => ?_⟩
  have hsplit : W - (1 - P) * W * (1 - Q) = (1 - P) * W * Q + P * W := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    abel
  have heq : Z + τ • (W - (1 - P) * W * (1 - Q)) + τ ^ 2 • (B * Z * C) =
      (1 + τ • B) * Z * (1 + τ • C) := by
    rw [hsplit, ← hBZ, ← hZC]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, smul_add, Matrix.mul_assoc]
    rw [show τ * τ = τ ^ 2 by ring]
    abel
  rw [heq]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- A right Dini comparison in which the slope bound is only needed at the contact points
`f x = B x` (Mathlib's `image_le_of_liminf_slope_right_lt_deriv_boundary'` asks for it
everywhere). -/
private theorem image_le_of_slope_at_contact {f B B' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (ha : f a ≤ B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, f x = B x → ∃ c < B' x,
      ∀ᶠ z in nhdsWithin x (Ioi x), slope f x z < c) :
    ∀ x ∈ Icc a b, f x ≤ B x := by
  have hsub : Icc a b ⊆ {x | f x ≤ B x} := by
    have hA : ContinuousOn (fun x => (f x, B x)) (Icc a b) := hf.prodMk hB
    have hclosed : IsClosed ({x | f x ≤ B x} ∩ Icc a b) := by
      simp only [inter_comm]
      exact hA.preimage_isClosed_of_isClosed isClosed_Icc OrderClosedTopology.isClosed_le'
    apply hclosed.Icc_subset_of_forall_exists_gt ha
    rintro x ⟨hxB, xab⟩ y hy
    rcases (show f x ≤ B x from hxB).lt_or_eq with hlt | heq
    · refine Filter.nonempty_of_mem (Filter.inter_mem ?_ (Ioc_mem_nhdsGT hy))
      have h1 : ∀ᶠ z in nhdsWithin x (Icc a b), f z < B z :=
        hA x (Ico_subset_Icc_self xab)
          (IsOpen.mem_nhds (isOpen_lt continuous_fst continuous_snd) hlt)
      have h2 : ∀ᶠ z in nhdsWithin x (Ioi x), f z < B z :=
        nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem xab) h1
      exact h2.mono fun _ h => le_of_lt h
    · obtain ⟨c, hcB, hfc⟩ := bound x xab heq
      have HB : ∀ᶠ z in nhdsWithin x (Ioi x), c < slope B x z :=
        (hasDerivWithinAt_iff_tendsto_slope' <| lt_irrefl x).1 (hB' x xab).Ioi_of_Ici
          (Ioi_mem_nhds hcB)
      obtain ⟨z, hfz, hzB, hz⟩ : ∃ z, slope f x z < c ∧ c < slope B x z ∧ z ∈ Ioc x y :=
        (hfc.and (HB.and (Ioc_mem_nhdsGT hy))).exists
      refine ⟨z, ?_, hz⟩
      have hle := (hfz.trans hzB).le
      rwa [slope_def_field, slope_def_field, div_le_div_iff_of_pos_right (sub_pos.2 hz.1), heq,
        sub_le_sub_iff_right] at hle
  exact fun x hx => hsub hx

/-- **The first-order estimate.**  Where `0 < dist(A(x), M_{≤ r}) ≤ ρ`, the right Dini derivative of
the distance is at most `L dist(A(x), M_{≤ r}) + ε`. -/
private theorem distLR_slope_lt [DecidableEq m] [DecidableEq n] {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L ε ρ x c : ℝ} (hF : IsLipschitzField F L)
    {A : ℝ → Matrix m n ℝ} (hd : HasDerivWithinAt A (F x (A x)) (Ici x) x)
    (hpos : 0 < distLR r (A x)) (hρ : distLR r (A x) ≤ ρ)
    (hε : ∀ (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ),
      Uᵀ * U = 1 → Vᵀ * V = 1 → ‖U * S * Vᵀ - A x‖ ≤ ρ →
        ‖(1 - U * Uᵀ) * F x (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε)
    (hc : L * distLR r (A x) + ε < c) :
    ∀ᶠ z in nhdsWithin x (Ioi x), slope (fun t => distLR r (A t)) x z < c := by
  obtain ⟨Z, hZ, hdist⟩ := exists_best_approx r (A x)
  have hZr : Z.rank = r := rank_eq_of_nearest hZ hdist hpos
  obtain ⟨U, S, V, hU, hV, hSunit, hZeq⟩ := (SVD.rank_eq_iff_exists_factor Z).1 hZr
  obtain ⟨G, hG⟩ := exists_rank_curve hU hV hSunit (F x Z)
  rw [← hZeq] at hG
  set d := distLR r (A x) with hd'
  set N : Matrix m n ℝ := (1 - U * Uᵀ) * F x Z * (1 - V * Vᵀ) with hN
  have hNε : ‖N‖ ≤ ε := by
    have h := hε U V S hU hV (by rw [← hZeq, norm_sub_rev, hdist]; exact hρ)
    rwa [← hZeq] at h
  have hWZ : ‖F x (A x) - F x Z‖ ≤ L * d := by
    have h := hF x (A x) Z
    rwa [hdist] at h
  set η := (c - (L * d + ε)) / 3 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  have hlo := (hasDerivWithinAt_iff_isLittleO.1 hd.Ioi_of_Ici).def hη0
  have hquot : 0 < η / (‖G‖ + 1) := by positivity
  have hsmall : ∀ᶠ z in nhdsWithin x (Ioi x), z < x + η / (‖G‖ + 1) :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by linarith))
  filter_upwards [hlo, hsmall, self_mem_nhdsWithin] with z hz1 hz2 hz3
  have hτ : 0 < z - x := sub_pos.2 hz3
  rw [Real.norm_of_nonneg hτ.le] at hz1
  have hrank : (Z + (z - x) • (F x Z - N) + (z - x) ^ 2 • G).rank ≤ r := (hG (z - x)).trans hZ
  have h1 := distLR_le_norm_sub (X := A z) hrank
  have hsplit : A z - (Z + (z - x) • (F x Z - N) + (z - x) ^ 2 • G) =
      (A z - A x - (z - x) • F x (A x)) + (A x - Z) + (z - x) • (F x (A x) - F x Z) +
        (z - x) • N - (z - x) ^ 2 • G := by
    simp only [smul_sub]
    abel
  have h2 : ‖A z - (Z + (z - x) • (F x Z - N) + (z - x) ^ 2 • G)‖ ≤
      η * (z - x) + d + (z - x) * (L * d) + (z - x) * ε + (z - x) ^ 2 * ‖G‖ := by
    rw [hsplit]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
        (add_le_add ((norm_add_le _ _).trans (add_le_add hz1 hdist.le)) ?_)) ?_)
      · rw [norm_smul, Real.norm_of_nonneg hτ.le]
        exact mul_le_mul_of_nonneg_left hWZ hτ.le
      · rw [norm_smul, Real.norm_of_nonneg hτ.le]
        exact mul_le_mul_of_nonneg_left hNε hτ.le
    · rw [norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
  have h3 : (z - x) * ‖G‖ ≤ η := by
    have h4 : z - x < η / (‖G‖ + 1) := by linarith
    rw [lt_div_iff₀ (by positivity)] at h4
    nlinarith
  rw [slope_def_field, div_lt_iff₀ hτ]
  change distLR r (A z) - d < c * (z - x)
  have h5 : c = L * d + ε + 3 * η := by rw [hη]; ring
  have h6 : (z - x) ^ 2 * ‖G‖ ≤ (z - x) * η := by
    calc (z - x) ^ 2 * ‖G‖ = (z - x) * ((z - x) * ‖G‖) := by ring
      _ ≤ (z - x) * η := mul_le_mul_of_nonneg_left h3 hτ.le
  rw [h5]
  nlinarith

/-- **OP-RA-07: sharp robust distance bound with a normal component controlled only near the
exact solution.**  If `rank A(t₀) ≤ r` and the factored normal component is `≤ ε` at all rank-`r`
points within `ρ` of `A(t)` (with `ρ` larger than the bound below), then
`dist(A(t), M_{≤ r}) ≤ ε (e^{L (t - t₀)} - 1) / L`: the Dini-derivative bound of the catalogue
(under the global factored assumption and a bound on `F`, `LeanDLRA.distLR_flow_le_exp` gives
`h ε e^{L h}`, also for `L = 0`). -/
theorem distLR_flow_le_dini_local [DecidableEq m] [DecidableEq n] {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L : ℝ} (hF : IsLipschitzField F L) (hL : 0 < L)
    {A : ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} (hA : ODESolution F A t₀ t₁)
    (hrank : (A t₀).rank ≤ r) {ε ρ : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ t ∈ Icc t₀ t₁, ∀ (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ)
      (S : Matrix (Fin r) (Fin r) ℝ), Uᵀ * U = 1 → Vᵀ * V = 1 → ‖U * S * Vᵀ - A t‖ ≤ ρ →
        ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε)
    (hρ : ε * (Real.exp (L * (t₁ - t₀)) - 1) / L < ρ) :
    ∀ t ∈ Icc t₀ t₁, distLR r (A t) ≤ ε * (Real.exp (L * (t - t₀)) - 1) / L := by
  intro t ht
  have h01 : t₀ ≤ t₁ := ht.1.trans ht.2
  set f : ℝ → ℝ := fun s => distLR r (A s) with hf
  have hfc : ContinuousOn f (Icc t₀ t₁) :=
    (lipschitzWith_distLR r).continuous.comp_continuousOn hA.cont
  set e : ℝ → ℝ := fun s => Real.exp (L * (s - t₀)) with he
  have he1 : ∀ s, t₀ ≤ s → 1 ≤ e s := fun s hs =>
    Real.one_le_exp (mul_nonneg hL.le (sub_nonneg.2 hs))
  have hemono : ∀ s, s ≤ t₁ → e s ≤ e t₁ := fun s hs =>
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (sub_le_sub_right hs _) hL.le)
  have he' : ∀ x, HasDerivAt e (L * e x) x := fun x => by
    have h := (((hasDerivAt_id x).sub_const t₀).const_mul L).exp
    simpa [he, mul_comm] using h
  set B : ℝ → ℝ → ℝ := fun η s => (ε + η) * (e s - 1) / L + η * e s with hB
  have key : ∀ η, 0 < η → B η t₁ < ρ → ∀ s ∈ Icc t₀ t₁, f s ≤ B η s := by
    intro η hη hηρ
    have hBd : ∀ x, HasDerivAt (B η) ((ε + η) * (L * e x) / L + η * (L * e x)) x := fun x =>
      ((((he' x).sub_const 1).const_mul (ε + η)).div_const L).add ((he' x).const_mul η)
    refine image_le_of_slope_at_contact (B' := fun x => (ε + η) * (L * e x) / L + η * (L * e x))
      hfc ?_ (fun x _ => (hBd x).continuousAt.continuousWithinAt)
      (fun x _ => (hBd x).hasDerivWithinAt) ?_
    · have hft₀ : f t₀ = 0 := distLR_eq_zero_of_rank_le hrank
      have het₀ : e t₀ = 1 := by simp [he]
      simp only [hft₀, hB, het₀]
      simp [hη.le]
    · intro x hx hfx
      have hx' : x ∈ Icc t₀ t₁ := Ico_subset_Icc_self hx
      have hex : 1 ≤ e x := he1 x hx.1
      have hext : e x ≤ e t₁ := hemono x hx.2.le
      have hεη : 0 ≤ ε + η := by linarith
      have hBpos : 0 < B η x := by
        have h1 : 0 ≤ (ε + η) * (e x - 1) / L :=
          div_nonneg (mul_nonneg hεη (by linarith)) hL.le
        have h2 : 0 < η * e x := by positivity
        simp only [hB]
        linarith
      have hBle : B η x ≤ B η t₁ := by
        simp only [hB]
        have h1 : (ε + η) * (e x - 1) / L ≤ (ε + η) * (e t₁ - 1) / L := by
          gcongr
        have h2 : η * e x ≤ η * e t₁ := by gcongr
        linarith
      refine ⟨L * f x + ε + η / 2, ?_, ?_⟩
      · rw [hfx]
        simp only [hB]
        have hL0 : L ≠ 0 := hL.ne'
        have h1 : L * ((ε + η) * (e x - 1) / L + η * e x) =
            (ε + η) * (e x - 1) + L * (η * e x) := by
          field_simp
        have h2 : (ε + η) * (L * e x) / L = (ε + η) * e x := by
          field_simp
        rw [h1, h2]
        nlinarith
      · refine distLR_slope_lt hF (hA.deriv x hx) (by change 0 < f x; rw [hfx]; exact hBpos)
          (by change f x ≤ ρ; rw [hfx]; exact (hBle.trans_lt hηρ).le)
          (fun U V S hU hV h => hε x hx' U V S hU hV h) ?_
        change L * f x + ε < L * f x + ε + η / 2
        linarith
  have hE : 0 ≤ e t₁ - 1 := by linarith [he1 t₁ h01]
  have hK1 : 1 ≤ e t₁ := he1 t₁ h01
  set K := (e t₁ - 1) / L + e t₁ with hK
  have hKpos : 0 < K := by
    have h : 0 ≤ (e t₁ - 1) / L := div_nonneg hE hL.le
    rw [hK]
    linarith
  have hgap : 0 < ρ - ε * (e t₁ - 1) / L := by linarith
  have hBη : ∀ η s, B η s = ε * (e s - 1) / L + η * ((e s - 1) / L + e s) := by
    intro η s
    simp only [hB]
    ring
  change f t ≤ ε * (e t - 1) / L
  apply le_of_forall_pos_le_add
  intro δ hδ
  set η := min (δ / K) ((ρ - ε * (e t₁ - 1) / L) / (2 * K)) with hηdef
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have h1 : η * K ≤ δ := by
    have h := min_le_left (δ / K) ((ρ - ε * (e t₁ - 1) / L) / (2 * K))
    rw [← hηdef, le_div_iff₀ hKpos] at h
    exact h
  have h2 : η * K ≤ (ρ - ε * (e t₁ - 1) / L) / 2 := by
    have h := min_le_right (δ / K) ((ρ - ε * (e t₁ - 1) / L) / (2 * K))
    rw [← hηdef, le_div_iff₀ (by positivity)] at h
    linarith
  have hρη : B η t₁ < ρ := by
    rw [hBη]
    linarith
  have hkey := key η hη hρη t ht
  rw [hBη] at hkey
  have h3 : η * ((e t - 1) / L + e t) ≤ η * K := by
    have hext := hemono t ht.2
    rw [hK]
    gcongr
  linarith

end Matrices

end LeanDLRA.OpenProblems.RankAdaptivity
