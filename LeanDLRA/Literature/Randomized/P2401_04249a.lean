import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2401.04249: DEIM Tucker tensor cross for DLRA

This module adds no new declarations. The three listed results of the paper are already in the
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

Left out:

* The three-mode case of Eq. (12) with `F̂ = F ×₁Π₁ ×₂Π₂ ×₃Π₃`: the library has no tensor type
  or mode product, so this needs new infrastructure.
* The least-squares case `r' > r` (pseudo-inverse) of Eq. (12).
* Eqs. (6a)–(6b), the Tucker gauge ODEs `Ṡ = F ×_i U⁽ⁱ⁾ᵀ`,
  `U̇⁽ⁱ⁾ = (I − U⁽ⁱ⁾U⁽ⁱ⁾ᵀ)[F ×_{k≠i} U⁽ᵏ⁾ᵀ]₍ᵢ₎ S₍ᵢ₎†`: they need a Tucker tensor type,
  matricization and the pseudo-inverse. `GaugeODE.lean` covers only the matrix case.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2401_04249

end LeanDLRA.Literature.P2401_04249
