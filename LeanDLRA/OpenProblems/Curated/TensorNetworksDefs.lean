import LeanDLRA.Integrators.TuckerBUG
import LeanDLRA.Integrators.Exactness
import LeanDLRA.Classical.CommutingProjectorTelescoping
import LeanDLRA.Tensor.Defs
import LeanDLRA.Tensor.Steps

/-!
# Definitions for TensorNetworks

This module only imports. The step predicates `IsTTNBUGStep`, `IsAugTTNBUGStep`,
`IsParTTNBUGStep`, the recoverability condition `IsTTNRecoverable` and the abstract
`tuckerTangentProj` are defined in `LeanDLRA/Tensor/Steps.lean`; the frames `TTNFrame`, the bound
`ttnErrBound` and the augmented recoverability `IsAugRecoverable`, `IsTTNAugRecoverable` in
`LeanDLRA/Tensor/Defs.lean`.
-/
