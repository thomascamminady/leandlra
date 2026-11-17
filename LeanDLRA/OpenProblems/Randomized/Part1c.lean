import LeanDLRA.OpenProblems.Randomized.Part1Defs
import LeanDLRA.Matrix.Interpolation
import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.ProjectorSplitting

/-!
# Open problems OP-RS-08, OP-RS-09
-/

open Set
open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius

universe u

namespace LeanDLRA.OpenProblems.Randomized

open LeanDLRA.Curvature

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Abstract

-- OP-RS-05: the statement `sketchedBUG_isBUGStep` is proved in
-- `LeanDLRA/Randomized/ObliqueBUG.lean` (namespace `LeanDLRA.ObliqueBUG`).

/-- **OP-RS-08 (a), explicit example** (arXiv 2607.03402, §4.2 and the Vlasov–Poisson experiment):
for `m = n = 2`, `r = 1`, `Y = e₁ e₁ᵀ` and the purely normal field value `N = e₂ e₂ᵀ`
(`P_Y N = 0`, so DLRA gives `Ẏ = 0`), there are invertible sketches `Θ`, `Ω` with
sketch-orthonormal bases for which the oblique sketch DLRA velocity `P^{Θ,Ω}_Y N` is nonzero.
Meaning: oblique sketch DLRA drifts where DLRA is exact. -/
theorem exists_obliqueSketch_drift :
    ∃ (Θ Ω : Matrix (Fin 2) (Fin 2) ℝ) (R R' : Matrix (Fin 1) (Fin 1) ℝ),
      IsUnit Θ.det ∧ IsUnit Ω.det ∧
      (Θ * (sketchE₁ * R))ᵀ * (Θ * (sketchE₁ * R)) = 1 ∧
      (Ω * (sketchE₁ * R'))ᵀ * (Ω * (sketchE₁ * R')) = 1 ∧
      tangentProj sketchE₁ sketchE₁ sketchN = 0 ∧
      sketchTangentProj Θ Ω (sketchE₁ * R) (sketchE₁ * R') sketchN ≠ 0 := by
  have hE : sketchE₁ᵀ * sketchE₁ = 1 := by
    ext i j; fin_cases i; fin_cases j
    simp [sketchE₁, Matrix.mul_apply]
  have hΘ : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) * sketchE₁ = sketchE₁ := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [sketchE₁, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨!![1, 1; 0, 1], 1, 1, 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Matrix.det_fin_two_of]
  · simp
  · rw [Matrix.mul_one, hΘ]; exact hE
  · rw [Matrix.mul_one, Matrix.one_mul]; exact hE
  · rw [tangentProj_apply]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [sketchE₁, sketchN, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct,
          Function.swap, Matrix.vecHead, Matrix.vecTail]
  · intro h
    have h1 := congrFun (congrFun h 0) 1
    simp only [sketchTangentProj, obliqueTangentProj_apply, obliqueProj] at h1
    simp [Matrix.mul_apply, sketchE₁, sketchN, Fin.sum_univ_two, Matrix.vecMul, dotProduct] at h1

private theorem spectral_real {m : Type*} [Fintype m] [DecidableEq m] (G : Matrix m m ℝ)
    (hG : G.PosSemidef) :
    ∃ (E : Matrix m m ℝ) (d : m → ℝ), Eᵀ * E = 1 ∧ E * Eᵀ = 1 ∧
      G = E * Matrix.diagonal d * Eᵀ ∧ (∀ i, 0 ≤ d i) ∧
      Fintype.card {i // d i ≠ 0} = G.rank := by
  have hH : G.IsHermitian := hG.isHermitian
  refine ⟨(hH.eigenvectorUnitary : Matrix m m ℝ), hH.eigenvalues, ?_, ?_, ?_,
    hG.eigenvalues_nonneg, (hH.rank_eq_card_non_zero_eigs).symm⟩
  · have := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  · have := Unitary.coe_mul_star_self hH.eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  · have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this


private theorem select_data {m k : Type*} [Fintype m] [Fintype k]
    (d : m → ℝ) (hnc : ∃ i j, d i ≠ d j) (hk : 0 < Fintype.card k)
    (hkm : Fintype.card k < Fintype.card m)
    (hrank : Fintype.card k ≤ Fintype.card {i // d i ≠ 0}) :
    ∃ (i₀ j₀ : m) (f : k → m) (c₀ : k), d i₀ ≠ 0 ∧ d i₀ ≠ d j₀ ∧ Function.Injective f ∧
      f c₀ = i₀ ∧ (∀ c, f c ≠ j₀) ∧ (∀ c, d (f c) ≠ 0) := by
  classical
  obtain ⟨c₀⟩ := Fintype.card_pos_iff.1 hk
  have key : ∃ i₀ j₀ : m, d i₀ ≠ 0 ∧ d i₀ ≠ d j₀ ∧
      Fintype.card k ≤ Fintype.card {a : m // a ≠ j₀ ∧ d a ≠ 0} := by
    by_cases hz : ∃ z, d z = 0
    · obtain ⟨z, hz⟩ := hz
      obtain ⟨i, j, hij⟩ := hnc
      have : ∃ i₀, d i₀ ≠ 0 := by
        by_cases hi : d i = 0
        · exact ⟨j, fun hj => hij (hi.trans hj.symm)⟩
        · exact ⟨i, hi⟩
      obtain ⟨i₀, hi₀⟩ := this
      refine ⟨i₀, z, hi₀, by rw [hz]; exact hi₀, ?_⟩
      refine hrank.trans (Fintype.card_le_of_injective (fun a => ⟨a.1, ?_, a.2⟩) ?_)
      · rintro rfl; exact a.2 hz
      · intro a b h
        simp only [Subtype.mk.injEq] at h
        exact Subtype.ext h
    · push Not at hz
      obtain ⟨i, j, hij⟩ := hnc
      refine ⟨i, j, hz i, hij, ?_⟩
      rw [Fintype.card_subtype]
      have h1 : Finset.univ.filter (fun a : m => a ≠ j ∧ d a ≠ 0) = Finset.univ.erase j := by
        ext a; simp [hz a]
      rw [h1, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      omega
  obtain ⟨i₀, j₀, hi₀, hij, hT⟩ := key
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hT
  have hne : i₀ ≠ j₀ := fun h => hij (by rw [h])
  let t₀ : {a : m // a ≠ j₀ ∧ d a ≠ 0} := ⟨i₀, hne, hi₀⟩
  let f : k → m := fun c => (Equiv.swap (g c₀) t₀ (g c)).1
  refine ⟨i₀, j₀, f, c₀, hi₀, hij, ?_, ?_, ?_, ?_⟩
  · intro a b h
    exact g.injective ((Equiv.swap (g c₀) t₀).injective (Subtype.ext h))
  · simp [f, t₀, Equiv.swap_apply_left]
  · intro c; exact (Equiv.swap (g c₀) t₀ (g c)).2.1
  · intro c; exact (Equiv.swap (g c₀) t₀ (g c)).2.2


private theorem gram_Q {m k : Type*} [Fintype m] [DecidableEq m] [DecidableEq k]
    (i₀ j₀ : m) (f : k → m) (c₀ : k) (hne : i₀ ≠ j₀) (hf : Function.Injective f)
    (hfc : f c₀ = i₀) (hfj : ∀ c, f c ≠ j₀) (s : m → ℝ) :
    (Matrix.of fun (i : m) (c : k) => if c = c₀ then
        (if i = i₀ then (3 / 5 : ℝ) else 0) + (if i = j₀ then 4 / 5 else 0)
      else if i = f c then 1 else 0)ᵀ * Matrix.diagonal s *
    (Matrix.of fun (i : m) (c : k) => if c = c₀ then
        (if i = i₀ then (3 / 5 : ℝ) else 0) + (if i = j₀ then 4 / 5 else 0)
      else if i = f c then 1 else 0) =
    Matrix.diagonal (fun c => if c = c₀ then 9 / 25 * s i₀ + 16 / 25 * s j₀ else s (f c)) := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.of_apply, Matrix.diagonal_apply]
  have hfi : ∀ c, c ≠ c₀ → f c ≠ i₀ := fun c hc h => hc (hf (h.trans hfc.symm))
  by_cases ha : a = c₀ <;> by_cases hb : b = c₀
  · subst ha; subst hb
    simp [mul_add, add_mul, Finset.sum_add_distrib, hne, hne.symm]
    ring
  · subst ha
    simp [hb, Ne.symm hb, add_mul, hfi b hb, hfj b]
  · subst hb
    simp [ha, mul_add, Finset.sum_add_distrib, (hfi a ha).symm, (hfj a).symm]
  · by_cases hab : a = b
    · subst hab
      simp [ha]
    · have : f a ≠ f b := fun h => hab (hf h)
      simp [ha, hb, hab, this.symm]


private theorem build_basis {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m]
    [DecidableEq k] (E : Matrix m m ℝ) (d : m → ℝ) (hE : Eᵀ * E = 1) (hd : ∀ i, 0 ≤ d i)
    (i₀ j₀ : m) (f : k → m) (c₀ : k) (h0 : d i₀ ≠ 0) (hij : d i₀ ≠ d j₀)
    (hf : Function.Injective f) (hfc : f c₀ = i₀) (hfj : ∀ c, f c ≠ j₀)
    (hfd : ∀ c, d (f c) ≠ 0) :
    ∃ (U : Matrix m k ℝ) (R : Matrix k k ℝ) (cw : Matrix m Unit ℝ),
      Uᵀ * U = 1 ∧ Rᵀ * (Uᵀ * (E * Matrix.diagonal d * Eᵀ) * U) * R = 1 ∧ Uᵀ * cw = 0 ∧
        Uᵀ * (E * Matrix.diagonal d * Eᵀ) * cw ≠ 0 := by
  have hne : i₀ ≠ j₀ := fun h => hij (by rw [h])
  have e : ∀ X : Matrix m k ℝ, Eᵀ * (E * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hE, Matrix.one_mul]
  have eU : ∀ X : Matrix m Unit ℝ, Eᵀ * (E * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hE, Matrix.one_mul]
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix m k ℝ, Q = Matrix.of fun (i : m) (c : k) => if c = c₀ then
        (if i = i₀ then (3 / 5 : ℝ) else 0) + (if i = j₀ then 4 / 5 else 0)
      else if i = f c then 1 else 0 := ⟨_, rfl⟩
  have hgram : ∀ s : m → ℝ, Qᵀ * Matrix.diagonal s * Q =
      Matrix.diagonal (fun c => if c = c₀ then 9 / 25 * s i₀ + 16 / 25 * s j₀ else s (f c)) := by
    intro s
    rw [hQdef]
    exact gram_Q i₀ j₀ f c₀ hne hf hfc hfj s
  have hQ1 : Qᵀ * Q = 1 := by
    have := hgram (fun _ => 1)
    rw [Matrix.diagonal_one, Matrix.mul_one] at this
    rw [this, ← Matrix.diagonal_one]
    congr 1
    funext c
    split_ifs <;> norm_num
  set d' : k → ℝ := fun c => if c = c₀ then 9 / 25 * d i₀ + 16 / 25 * d j₀ else d (f c) with hd'
  have hd'pos : ∀ c, 0 < d' c := by
    intro c
    have hi := lt_of_le_of_ne (hd i₀) (Ne.symm h0)
    have hj := hd j₀
    by_cases hc : c = c₀
    · simp only [hd', hc, ite_true]; positivity
    · simp only [hd', hc, ite_false]
      exact lt_of_le_of_ne (hd _) (Ne.symm (hfd c))
  obtain ⟨y, hy⟩ : ∃ y : Matrix m Unit ℝ, y = Matrix.of fun (i : m) (_ : Unit) =>
      (if i = i₀ then (4 / 5 : ℝ) else 0) - (if i = j₀ then 3 / 5 else 0) := ⟨_, rfl⟩
  have hQy : Qᵀ * y = 0 := by
    ext c u
    rw [hQdef, hy]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    by_cases hc : c = c₀
    · subst hc
      simp [mul_sub, add_mul, hne, hne.symm]
      norm_num
    · have h1 : f c ≠ i₀ := fun h => hc (hf (h.trans hfc.symm))
      simp [hc, h1, hfj c]
  have hQDy : Qᵀ * Matrix.diagonal d * y ≠ 0 := by
    intro h
    have h' := congrFun (congrFun h c₀) ()
    rw [hQdef, hy] at h'
    rw [Matrix.mul_apply] at h'
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.of_apply,
      Matrix.zero_apply] at h'
    simp [mul_sub, add_mul, hne, hne.symm] at h'
    exact hij (by linarith)
  refine ⟨E * Q, Matrix.diagonal (fun c => (Real.sqrt (d' c))⁻¹), E * y, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.mul_assoc, e, hQ1]
  · have hG : (E * Q)ᵀ * (E * Matrix.diagonal d * Eᵀ) * (E * Q) = Matrix.diagonal d' := by
      rw [← hgram d]
      simp only [Matrix.transpose_mul, Matrix.mul_assoc, e]
    rw [hG, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext c
    have hs := Real.sqrt_pos.2 (hd'pos c)
    have hsq := Real.sq_sqrt (hd'pos c).le
    field_simp
    linarith
  · rw [Matrix.transpose_mul, Matrix.mul_assoc, eU, hQy]
  · intro h
    apply hQDy
    rw [← h]
    simp only [Matrix.transpose_mul, Matrix.mul_assoc, eU]

private theorem eq_zero_of_mul_row {m n : Type*} (M : Matrix m Unit ℝ)
    (rv : Matrix Unit n ℝ) (hrv : rv ≠ 0) (h : M * rv = 0) : M = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, rv () j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hrv (Matrix.ext fun u j => by cases u; exact hc j)
  ext i u
  cases u
  have := congrFun (congrFun h i) j
  rw [Matrix.mul_apply, Fintype.sum_unique, Matrix.zero_apply] at this
  exact (mul_eq_zero.1 this).resolve_right hj

private theorem drift_assembly {m n k l p : Type*} [Fintype m] [Fintype n] [Fintype k]
    [Fintype l] [Fintype p] [DecidableEq n] [DecidableEq k] [DecidableEq l]
    (Θ : Matrix p m ℝ) (U : Matrix m k ℝ) (V : Matrix n l ℝ) (R : Matrix k k ℝ)
    (cw : Matrix m Unit ℝ) (rv : Matrix Unit n ℝ)
    (hV : Vᵀ * V = 1) (hP : (Θ * (U * R))ᵀ * (Θ * (U * R)) = 1)
    (hw : Uᵀ * cw = 0) (hv : rv * V = 0) (hrv : rv ≠ 0)
    (hGw : Uᵀ * (Θᵀ * Θ) * cw ≠ 0) :
    tangentProj U V (cw * rv) = 0 ∧
      sketchTangentProj Θ (1 : Matrix n n ℝ) (U * R) (V * (1 : Matrix l l ℝ)) (cw * rv) ≠ 0 := by
  have h1 : Uᵀ * (cw * rv) = 0 := by rw [← Matrix.mul_assoc, hw, Matrix.zero_mul]
  refine ⟨?_, ?_⟩
  · rw [tangentProj_apply]
    simp [Matrix.mul_assoc, hv, h1]
  · intro h
    obtain ⟨hR, hSU⟩ := isUnit_det_of_sketch_orthonormal hP
    have hPV : obliqueProj (V * (1 : Matrix l l ℝ))
        ((1 : Matrix n n ℝ)ᵀ * 1 * (V * (1 : Matrix l l ℝ))) = V * Vᵀ := by
      simp [obliqueProj, hV]
    rw [sketchTangentProj, obliqueTangentProj_apply, hPV] at h
    have h2 : rv * (V * Vᵀ)ᵀ = 0 := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc, hv,
        Matrix.zero_mul]
    simp only [Matrix.mul_assoc, h2, Matrix.mul_zero, add_zero, sub_zero] at h
    rw [← Matrix.mul_assoc] at h
    have h3 := eq_zero_of_mul_row _ rv hrv h
    rw [obliqueProj_mul_right hR, ← Matrix.mul_assoc Θᵀ Θ (U * R)] at h3
    have h4 := transpose_mul_obliqueProj_mul hSU cw
    rw [h3, Matrix.mul_zero] at h4
    have hRt : IsUnit Rᵀ.det := by rwa [Matrix.det_transpose]
    have e : (Θᵀ * Θ * (U * R))ᵀ * cw = Rᵀ * (Uᵀ * (Θᵀ * Θ) * cw) := by
      simp [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e] at h4
    apply hGw
    calc Uᵀ * (Θᵀ * Θ) * cw = (Rᵀ)⁻¹ * (Rᵀ * (Uᵀ * (Θᵀ * Θ) * cw)) := by
          rw [← Matrix.mul_assoc Rᵀ⁻¹ Rᵀ, Matrix.nonsing_inv_mul _ hRt, Matrix.one_mul]
      _ = 0 := by rw [← h4, Matrix.mul_zero]


/-- **OP-RS-08 (b), every non-isotropic sketch** (arXiv 2607.03402, Prop. 4.4 and Remark 4.6):
if the Gram matrix `ΘᵀΘ` of the left sketch is not a multiple of the identity (e.g. any
compressive `Θ`, `ℓ < m`) and `rank Θ ≥ r`, `0 < r < m`, `0 < r' < n`, there are orthonormal
bases `U`, `V` (with `ΘU` injective, sketch-orthonormalized by `R`) and a purely normal `N`
(`P_Y N = 0`) whose oblique sketch velocity is nonzero (right sketch `Ω = I`).  Meaning: enlarging
the sketch within the low-rank budget cannot remove the drift. -/
theorem exists_obliqueSketch_drift_of_not_scalar {m n k l p : Type*} [Fintype m] [Fintype n]
    [Fintype k] [Fintype l] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq k]
    [DecidableEq l] (Θ : Matrix p m ℝ) (hΘ : ∀ c : ℝ, Θᵀ * Θ ≠ c • (1 : Matrix m m ℝ))
    (hk : 0 < Fintype.card k) (hkm : Fintype.card k < Fintype.card m)
    (hrk : Fintype.card k ≤ Θ.rank) (hl : 0 < Fintype.card l)
    (hln : Fintype.card l < Fintype.card n) :
    ∃ (U : Matrix m k ℝ) (V : Matrix n l ℝ) (R : Matrix k k ℝ) (N : Matrix m n ℝ),
      Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ (Θ * (U * R))ᵀ * (Θ * (U * R)) = 1 ∧
      tangentProj U V N = 0 ∧
      sketchTangentProj Θ (1 : Matrix n n ℝ) (U * R) (V * (1 : Matrix l l ℝ)) N ≠ 0 := by
  have _ := hl
  have hG : (Θᵀ * Θ).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self Θ
  obtain ⟨E, d, hE1, hE2, hGeq, hd, hcard⟩ := spectral_real (Θᵀ * Θ) hG
  have hnc : ∃ i j, d i ≠ d j := by
    by_contra hcon
    push Not at hcon
    obtain ⟨i₀⟩ : Nonempty m := Fintype.card_pos_iff.1 (hk.trans hkm)
    apply hΘ (d i₀)
    have hdiag : (Matrix.diagonal d : Matrix m m ℝ) = d i₀ • 1 := by
      ext a b
      simp [Matrix.diagonal_apply, Matrix.one_apply, hcon a i₀]
    rw [hGeq, hdiag, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hE2]
  have hrank : Fintype.card k ≤ Fintype.card {i // d i ≠ 0} := by
    rw [hcard, Matrix.rank_transpose_mul_self]; exact hrk
  obtain ⟨i₀, j₀, f, c₀, h0, hij, hf, hfc, hfj, hfd⟩ := select_data d hnc hk hkm hrank
  obtain ⟨U, R, cw, hU, hRU, hw, hGw⟩ :=
    build_basis E d hE1 hd i₀ j₀ f c₀ h0 hij hf hfc hfj hfd
  rw [← hGeq] at hRU hGw
  -- the right basis
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hln.le
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, ∀ c, g c ≠ n₀ := by
    by_contra hcon
    push Not at hcon
    have := Fintype.card_le_of_surjective g.1 hcon
    omega
  have hV : (Matrix.of fun (i : n) (c : l) => if i = g c then (1 : ℝ) else 0)ᵀ *
      (Matrix.of fun (i : n) (c : l) => if i = g c then (1 : ℝ) else 0) = 1 := by
    ext a b
    simp [Matrix.mul_apply, Matrix.one_apply, g.injective.eq_iff, eq_comm, Function.swap]
  have hrv : (Matrix.of fun (_ : Unit) (j : n) => if j = n₀ then (1 : ℝ) else 0) *
      (Matrix.of fun (i : n) (c : l) => if i = g c then (1 : ℝ) else 0) = 0 := by
    ext u c
    simp [Matrix.mul_apply, hn₀ c]
  have hrv0 : (Matrix.of fun (_ : Unit) (j : n) => if j = n₀ then (1 : ℝ) else 0) ≠ 0 := by
    intro h
    have := congrFun (congrFun h ()) n₀
    simp at this
  have hP : (Θ * (U * R))ᵀ * (Θ * (U * R)) = 1 := by
    rw [← hRU]
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  obtain ⟨h1, h2⟩ := drift_assembly Θ U _ R cw _ hV hP hw hrv hrv0 hGw
  exact ⟨U, _, R, _, hU, hV, hP, h1, h2⟩

private theorem vec_lower_of_frob {k p : Type*} [Fintype k] [Fintype p] [DecidableEq k]
    {B : Matrix p k ℝ} {c : ℝ}
    (hσ : ∀ X : Matrix k k ℝ, c * ‖X‖ ≤ ‖B * X‖) (v : EuclideanSpace ℝ k) :
    c * ‖v‖ ≤ ‖Matrix.toEuclideanLin B v‖ := by
  rcases isEmpty_or_nonempty k with hk | ⟨⟨j0⟩⟩
  · have : v = 0 := Subsingleton.elim _ _
    simp [this]
  · have h := hσ (Matrix.of fun i j => if j = j0 then v i else 0)
    have h1 : ‖(Matrix.of fun i j => if j = j0 then v i else 0 : Matrix k k ℝ)‖ = ‖v‖ := by
      have e : ‖(Matrix.of fun i j => if j = j0 then v i else 0 : Matrix k k ℝ)‖ ^ 2 =
          ‖v‖ ^ 2 := by
        rw [frob_sq, EuclideanSpace.norm_sq_eq]
        simp [Finset.sum_ite_eq']
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 e
    have h2 : ‖B * (Matrix.of fun i j => if j = j0 then v i else 0 : Matrix k k ℝ)‖ =
        ‖Matrix.toEuclideanLin B v‖ := by
      have e : ‖B * (Matrix.of fun i j => if j = j0 then v i else 0 : Matrix k k ℝ)‖ ^ 2 =
          ‖Matrix.toEuclideanLin B v‖ ^ 2 := by
        rw [frob_sq, EuclideanSpace.norm_sq_eq]
        simp [Matrix.mul_apply, Finset.sum_ite_eq', Matrix.toLpLin_apply, Matrix.mulVec,
          dotProduct]
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 e
    rwa [h1, h2] at h

private theorem inner_toEuclideanLin_transpose {k p : Type*} [Fintype k] [Fintype p]
    [DecidableEq k] [DecidableEq p] (B : Matrix p k ℝ) (v : EuclideanSpace ℝ k)
    (w : EuclideanSpace ℝ p) :
    ⟪v, Matrix.toEuclideanLin Bᵀ w⟫ = ⟪Matrix.toEuclideanLin B v, w⟫ := by
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact LinearMap.adjoint_inner_right _ _ _

private theorem gram_aux {k p : Type*} [Fintype k] [Fintype p] [DecidableEq k] [DecidableEq p]
    {B : Matrix p k ℝ} {c : ℝ} (hc : 0 < c)
    (hB : ∀ v : EuclideanSpace ℝ k, c * ‖v‖ ≤ ‖Matrix.toEuclideanLin B v‖) :
    IsUnit (Bᵀ * B).det ∧ specNorm ((Bᵀ * B)⁻¹ * Bᵀ) ≤ 1 / c := by
  have hm : ∀ x, Matrix.toEuclideanLin (Bᵀ * B) x =
      Matrix.toEuclideanLin Bᵀ (Matrix.toEuclideanLin B x) := fun x => by
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same]
  have hsq : ∀ v : EuclideanSpace ℝ k,
      ‖Matrix.toEuclideanLin B v‖ ^ 2 = ⟪v, Matrix.toEuclideanLin (Bᵀ * B) v⟫ := by
    intro v
    rw [hm, inner_toEuclideanLin_transpose, real_inner_self_eq_norm_sq]
  have hunit : IsUnit (Bᵀ * B).det := by
    refine isUnit_det_of_bounded_below (ρ := c ^ 2) (by positivity) fun v => ?_
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    have h1 : (c * ‖v‖) ^ 2 ≤ ‖Matrix.toEuclideanLin B v‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) (hB v) 2
    have h2 := hsq v
    have h3 : ⟪v, Matrix.toEuclideanLin (Bᵀ * B) v⟫ ≤
        ‖v‖ * ‖Matrix.toEuclideanLin (Bᵀ * B) v‖ := real_inner_le_norm _ _
    have hv0 : 0 < ‖v‖ := norm_pos_iff.2 hv
    nlinarith
  refine ⟨hunit, specNorm_le_of (by positivity) fun w => ?_⟩
  set v : EuclideanSpace ℝ k := Matrix.toEuclideanLin ((Bᵀ * B)⁻¹ * Bᵀ) w with hvdef
  have hGv : Matrix.toEuclideanLin (Bᵀ * B) v = Matrix.toEuclideanLin Bᵀ w := by
    rw [hvdef, ← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hunit, Matrix.one_mul]
  have h1 : ‖Matrix.toEuclideanLin B v‖ ^ 2 ≤ ‖Matrix.toEuclideanLin B v‖ * ‖w‖ := by
    rw [hsq v, hGv, inner_toEuclideanLin_transpose]
    exact real_inner_le_norm _ _
  have h2 : ‖Matrix.toEuclideanLin B v‖ ≤ ‖w‖ := by
    rcases (norm_nonneg (Matrix.toEuclideanLin B v)).eq_or_lt with h0 | h0
    · rw [← h0]; exact norm_nonneg _
    · nlinarith
  have h3 := hB v
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hc]
  nlinarith


private theorem oversampled_eq {m k p : Type*} [Fintype m] [Fintype k] [Fintype p]
    [DecidableEq k] (U : Matrix m k ℝ) (S : Matrix m p ℝ) :
    ((S * Sᵀ * U)ᵀ * U = (Sᵀ * U)ᵀ * (Sᵀ * U)) ∧
    obliqueProj U (S * Sᵀ * U) = U * (((Sᵀ * U)ᵀ * (Sᵀ * U))⁻¹ * (Sᵀ * U)ᵀ) * Sᵀ := by
  have h1 : (S * Sᵀ * U)ᵀ * U = (Sᵀ * U)ᵀ * (Sᵀ * U) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  refine ⟨h1, ?_⟩
  have h2 : (S * Sᵀ * U)ᵀ = (Sᵀ * U)ᵀ * Sᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [obliqueProj, h1, h2]
  simp only [Matrix.mul_assoc]

/-- **OP-RS-09 (a)** (E-DEIM / GappyPOD+E; oversampled least-squares interpolation): for an
orthonormal selection `S ∈ ℝ^{m × p}` (`p ≥ r` rows) with `σ_min(Sᵀ U) ≥ c > 0` (expressed as
`c ‖X‖_F ≤ ‖Sᵀ U X‖_F`), the oversampled projector
`U (Uᵀ S Sᵀ U)⁻¹ Uᵀ S Sᵀ = obliqueProj U (S Sᵀ U)`
is well defined and `‖·‖₂ ≤ 1/c`.  Meaning: the Lebesgue constant of oversampled interpolation is
`1/σ_min(SᵀU)`. -/
theorem specNorm_obliqueProj_oversampled_le {m k p : Type*} [Fintype m] [Fintype k] [Fintype p]
    [DecidableEq m] [DecidableEq k] [DecidableEq p] {U : Matrix m k ℝ} {S : Matrix m p ℝ} {c : ℝ}
    (hU : Uᵀ * U = 1) (hS : Sᵀ * S = 1) (hc : 0 < c)
    (hσ : ∀ X : Matrix k k ℝ, c * ‖X‖ ≤ ‖Sᵀ * U * X‖) :
    IsUnit ((S * Sᵀ * U)ᵀ * U).det ∧ specNorm (obliqueProj U (S * Sᵀ * U)) ≤ 1 / c := by
  obtain ⟨h1, h2⟩ := oversampled_eq U S
  obtain ⟨hunit, hnorm⟩ := gram_aux hc (vec_lower_of_frob hσ)
  refine ⟨by rw [h1]; exact hunit, ?_⟩
  rw [h2]
  have hU1 := specNorm_le_one_of_orthonormal hU
  have hS1 : specNorm Sᵀ ≤ 1 := by rw [specNorm_transpose]; exact specNorm_le_one_of_orthonormal hS
  have e1 := specNorm_mul_le (U * (((Sᵀ * U)ᵀ * (Sᵀ * U))⁻¹ * (Sᵀ * U)ᵀ)) Sᵀ
  have e2 := specNorm_mul_le U (((Sᵀ * U)ᵀ * (Sᵀ * U))⁻¹ * (Sᵀ * U)ᵀ)
  have := specNorm_nonneg U
  have := specNorm_nonneg Sᵀ
  have := specNorm_nonneg (((Sᵀ * U)ᵀ * (Sᵀ * U))⁻¹ * (Sᵀ * U)ᵀ)
  have := specNorm_nonneg (U * (((Sᵀ * U)ᵀ * (Sᵀ * U))⁻¹ * (Sᵀ * U)ᵀ))
  have hc1 : 0 ≤ 1 / c := by positivity
  calc _ ≤ _ := e1
    _ ≤ (specNorm U * specNorm (((Sᵀ * U)ᵀ * (Sᵀ * U))⁻¹ * (Sᵀ * U)ᵀ)) * specNorm Sᵀ := by gcongr
    _ ≤ (1 * (1 / c)) * 1 := by gcongr
    _ = 1 / c := by ring



private theorem norm_fromCols_transpose_mul_ge {m k q n : Type*} [Fintype m] [Fintype k]
    [Fintype q] [Fintype n] (S₁ : Matrix m k ℝ) (S₂ : Matrix m q ℝ) (M : Matrix m n ℝ) :
    ‖S₁ᵀ * M‖ ≤ ‖(Matrix.fromCols S₁ S₂)ᵀ * M‖ := by
  have h : (Matrix.fromCols S₁ S₂)ᵀ * M = Matrix.fromRows (S₁ᵀ * M) (S₂ᵀ * M) := by
    rw [Matrix.transpose_fromCols, Matrix.fromRows_mul]
  rw [h]
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [frob_sq, frob_sq, Fintype.sum_sum_type]
  simp only [Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr]
  have : 0 ≤ ∑ i, ∑ j, (S₂ᵀ * M) i j ^ 2 := by positivity
  linarith

/-- **OP-RS-09 (b)** (oversampling never hurts): if the selection `[S₁, S₂]` extends the square
selection `S₁` (orthonormal columns), the Lebesgue constant of the oversampled projector is at most
that of the square DEIM projector built from `S₁`: `‖obliqueProj U (S Sᵀ U)‖₂ ≤ ‖(S₁ᵀ U)⁻¹‖₂`.
Meaning: E-DEIM / GappyPOD+E is never worse than any of its square sub-selections. -/
theorem specNorm_obliqueProj_oversampled_le_square {m k q : Type*} [Fintype m] [Fintype k]
    [Fintype q] [DecidableEq m] [DecidableEq k] [DecidableEq q] {U S₁ : Matrix m k ℝ}
    {S₂ : Matrix m q ℝ}
    (hU : Uᵀ * U = 1) (hS : (Matrix.fromCols S₁ S₂)ᵀ * Matrix.fromCols S₁ S₂ = 1)
    (hSU : IsUnit (S₁ᵀ * U).det) :
    specNorm (obliqueProj U (Matrix.fromCols S₁ S₂ * (Matrix.fromCols S₁ S₂)ᵀ * U)) ≤
      specNorm (S₁ᵀ * U)⁻¹ := by
  rcases isEmpty_or_nonempty k with hk | hk
  · have : obliqueProj U (Matrix.fromCols S₁ S₂ * (Matrix.fromCols S₁ S₂)ᵀ * U) = 0 := by
      ext i j
      simp [obliqueProj, Matrix.mul_apply]
    rw [this]
    have h0 : specNorm (0 : Matrix m m ℝ) = 0 := by
      refine le_antisymm (specNorm_le_of le_rfl fun x => by simp) (specNorm_nonneg _)
    rw [h0]
    exact specNorm_nonneg _
  set C := specNorm (S₁ᵀ * U)⁻¹ with hC
  have hX : ∀ X : Matrix k k ℝ,
      ‖X‖ ≤ C * ‖(Matrix.fromCols S₁ S₂)ᵀ * U * X‖ := by
    intro X
    have e : X = (S₁ᵀ * U)⁻¹ * (S₁ᵀ * U * X) := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hSU, Matrix.one_mul]
    calc ‖X‖ = ‖(S₁ᵀ * U)⁻¹ * (S₁ᵀ * U * X)‖ := by rw [← e]
      _ ≤ C * ‖S₁ᵀ * U * X‖ := frob_mul_le _ _
      _ ≤ C * ‖(Matrix.fromCols S₁ S₂)ᵀ * U * X‖ := by
        have := norm_fromCols_transpose_mul_ge S₁ S₂ (U * X)
        simp only [← Matrix.mul_assoc] at this
        exact mul_le_mul_of_nonneg_left this (specNorm_nonneg _)
  have hCpos : 0 < C := by
    have h1 := hX 1
    have h2 : 0 < ‖(1 : Matrix k k ℝ)‖ := norm_pos_iff.2 one_ne_zero
    rcases (specNorm_nonneg (S₁ᵀ * U)⁻¹).eq_or_lt with h0 | h0
    · rw [hC, ← h0] at h1
      linarith
    · exact h0
  have hmain := (specNorm_obliqueProj_oversampled_le (S := Matrix.fromCols S₁ S₂) (c := C⁻¹) hU hS
    (inv_pos.2 hCpos) (fun X => by
      have := hX X
      rw [Matrix.mul_assoc] at this ⊢
      rw [inv_mul_le_iff₀ hCpos]
      exact this)).2
  rwa [one_div, inv_inv] at hmain

end LeanDLRA.OpenProblems.Randomized
