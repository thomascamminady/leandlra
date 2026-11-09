import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2401.04249: DEIM Tucker tensor cross for DLRA

This module adds no new declarations. The following results of the paper are already in the
library, so they are not duplicated here:

* **Eqs. (17a)–(17b) (DLRA-DEIM-FS)**: the DLRA with a computed field `G` that is `δ`-close to `F`
  along the trajectory is `LeanDLRA.PerturbedField.hyper_dlra_norm_sub_le`
  (`Integrators/PerturbedField.lean`). Its error bound is `gronwallBound δ₀ L (ε + δ) (t - a)`,
  with `L` the Lipschitz constant of the exact field `F` only; `G` (the DEIM fibre-sampled field)
  needs no regularity. The file docstring of `PerturbedField.lean` names this as the instance
  for 2401.04249.
* **Eq. (12) for two modes (DEIM-FS core, `d = 2`)**: the interpolation identity
  `Sᵀ (𝒫_U X 𝒫_Vᵀ) S = Sᵀ X S` is `LeanDLRA.transpose_mul_obliqueProj_mul_mul`, and the error
  bound with selection matrices is `LeanDLRA.norm_sub_obliqueProj_mul_mul_le_of_orthonormal`
  (`Matrix/Interpolation.lean`), where `𝒫_U = obliqueProj U S_U = U (S_Uᵀ U)⁻¹ S_Uᵀ`.
* **Eq. (12), mode-wise interpolation for `d` modes** (in particular the three-mode case of
  Algorithm 1): if every mode matrix `Aᵢ` has unit rows at the sampled indices `pᵢ` (as the
  interpolatory projectors `𝒫ᵢ = U⁽ⁱ⁾ (U⁽ⁱ⁾(pᵢ, :))⁻¹ I(:, pᵢ)ᵀ` do,
  `LeanDLRA.transpose_mul_obliqueProj`), then `F ×₁ A₁ ⋯ ×_d A_d` agrees with `F` at every
  sampled multi-index: this is the core theorem `LeanDLRA.Tensor.modeProd_modeAct_apply_eq`
  (`Tensor/Tucker/Basic.lean`).

Left out (not claimed):

* The identification of the core formula (12)–(13) with the oblique mode products, i.e.
  `F̂ = (W ×ᵢ U⁽ⁱ⁾(pᵢ, :)⁻¹) ×ᵢ U⁽ⁱ⁾ = F ×ᵢ 𝒫ᵢ` (composition of Tucker products); hence Remark 1
  (`F̂(p₁, p₂, p₃) = F(p₁, p₂, p₃)` for `r' = r`) is not stated in the form (12)–(13).
* The least-squares case `r' > r` of Eq. (12) (`S_F` minimizes `‖W - S ×ᵢ U⁽ⁱ⁾(pᵢ, :)‖_F`, with
  the pseudo-inverse).
* Eqs. (6a)–(6b), the Tucker gauge ODEs `Ṡ = F ×_i U⁽ⁱ⁾ᵀ`,
  `U̇⁽ⁱ⁾ = (I − U⁽ⁱ⁾U⁽ⁱ⁾ᵀ)[F ×_{k≠i} U⁽ᵏ⁾ᵀ]₍ᵢ₎ S₍ᵢ₎†`: the library has Tucker tensors, mode
  products and unfoldings (`Tensor/Tucker/Basic.lean`, `Tensor/Unfolding.lean`), but not the
  differentiation of Tucker tensors with time-dependent factors; `GaugeODE.lean` covers the
  matrix case.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2401_04249

end LeanDLRA.Literature.P2401_04249
