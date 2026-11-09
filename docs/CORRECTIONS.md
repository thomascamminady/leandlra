# Corrections

Published statements that are false as printed, with a machine-checked counterexample or a precise
reason. Each entry was read in the printed PDF. "Loose" entries are slips a reader repairs at once, or
true statements with a wrong intermediate step. Corrected forms are in the same Lean file unless noted.

## False as printed

| Paper | Location | What fails | Lean |
|---|---|---|---|
| Lubich, Oseledets, [1301.1058](https://arxiv.org/abs/1301.1058) | Thm 4.1 | Exactness of projector splitting without an overlap condition, if Step 1 may return any valid factorization | `Exactness.RankOneExample.not_exact_of_degenerate` |
| Billaud-Friess, Falcó, Nouy, [2001.08599](https://arxiv.org/abs/2001.08599) | Prop 3.12 | Same gap, through the same argument | `prop_3_12_literal_false` |
| Ceruti, Lubich, [2010.02022](https://arxiv.org/abs/2010.02022) | Thm 6 | Tucker exactness for d ≥ 3 when some K_i(t₁) is rank-deficient | `Counterexample.theorem6_false` |
| Schotthöfer, Laiu, [2406.17887](https://arxiv.org/abs/2406.17887) | Thm 2 | Needs more than L-smoothness in its standard meaning | `theorem2_false_of_smooth_only` |
| Schotthöfer, Laiu, [2406.17887](https://arxiv.org/abs/2406.17887) | Thm 3 | Stated range of λ too wide | `theorem3_false_of_small_lr` |
| Schotthöfer, Laiu, [2406.17887](https://arxiv.org/abs/2406.17887) | Thm 4, Cor 1 | Bound fails; corrected forms proved | `theorem4_false`, `theorem4_corrected`, `corollary1_corrected` |
| Zangrando, Sutti, Tudisco, [2609.21039](https://arxiv.org/abs/2609.21039) | Thm 4.2 | Regret bound fails | `theorem_4_2_false`, `theorem_4_2_false_factorized` |
| Zangrando, Sutti, Tudisco, [2609.21039](https://arxiv.org/abs/2609.21039) | Prop 4.3, first claim | Fails on the paper's own loss | `proposition_4_3_first_claim_false` |
| Nguyen et al., [2401.03748](https://arxiv.org/abs/2401.03748) | Prop D.1 | Bound fails; needs a fourth-moment hypothesis | `propD1_counterexample`, `propD1_biasTerm_counterexample`, `propD1` |
| Xu et al., [2609.32615](https://arxiv.org/abs/2609.32615) | eq. (26) | Contraction factor γ < 1 from monotonicity of projections; monotonicity gives only γ = 1 | `compensation_no_contraction` |
| Thomas, [2607.05872](https://arxiv.org/abs/2607.05872) | Prop 4 | E[γ_g] is not the spectral mass; only the ratio of means is | `expected_energyFraction_ne_spectral_mass`, `coverage_eq_spectral_mass` |
| Sui et al., [2401.10341](https://arxiv.org/abs/2401.10341) | Eq. (7) | Flop reduction formula fails for downsampling layers | `eq7_false_for_downsampling`, `flops_reduction_eq_eq7` |
| Schotthöfer et al., [2410.18720](https://arxiv.org/abs/2410.18720) | Thm 1 | Factor 1 − Lλ²/2 and the truncation term | `geoLoRA_bound_false`, `geoLoRA_bound_false_mainText`, `descent_estimate` |
| Schotthöfer et al., [2410.18720](https://arxiv.org/abs/2410.18720) | Thm 2 | liminf of the stochastic gradient norm | `stochastic_conclusion_false` |
| Schotthöfer et al., [2410.18720](https://arxiv.org/abs/2410.18720) | Thm 3 | Constants cannot be independent of the final time | `not_uniformErrorBound`, `error_bound` |
| Schotthöfer, Klein, Kusch, [2506.17475](https://arxiv.org/abs/2506.17475) | Thm 1 | Heavy-ball flow bounded below need not converge | `heavyBall_not_convergent`, `heavyBall_limit_stationary` |
| Schotthöfer, Klein, Kusch, [2506.17475](https://arxiv.org/abs/2506.17475) | Thm 3 | Fails for the printed damping 1 − γ; with 1 − λγ the proof needs the normal momentum, shown with a gradient bounded only along the trajectories | `lowRankHeavyBall_printedDamping_false`, `lowRankHeavyBall_needs_normalMomentum`, `lowRankHeavyBall_error` |
| Matveeva, Katrutsa, Frolov, [2508.21106](https://arxiv.org/abs/2508.21106) | Thm 1 | False if the Cholesky factor is triangular; true for the recursive factor | `theorem_one_false_for_triangular_cholesky`, `theorem_one` |
| Kusch, Schotthöfer, Walter, [2502.03006](https://arxiv.org/abs/2502.03006) | Thm 5.6 | Coefficient 1 on ε | `abcPsi_literal_bound_false`, `abcPsi_global_error_le` |
| Schotthöfer et al., [2205.13571](https://arxiv.org/abs/2205.13571) | Thm 1 | Constants depending only on C₁, C₂; they grow with the final time | `dlrt_constants_depend_on_time`, `dlrt_approximation` |
| Schotthöfer et al., [2205.13571](https://arxiv.org/abs/2205.13571) | Thm 2 | Decrease with α independent of t and η | `dlrt_no_uniform_descent`, `dlrt_descent` |
| Savostianova et al., [2306.01485](https://arxiv.org/abs/2306.01485) | Thm 1 | Bound 3λη after k steps | `theorem1_false_gradient_flow`, `theorem1_false_many_steps`, `theorem1_steps` |
| Savostianova et al., [2306.01485](https://arxiv.org/abs/2306.01485) | Prop 1 | With cond(W) = ‖W‖‖W⁺‖, and entrywise activation bounds | `proposition1_false_with_pinv`, `entrywise_activations_eq_top`, `condOn_layerNet_lowRank_le` |
| Baumann et al., [2411.06844](https://arxiv.org/abs/2411.06844) | Thm 3 | Energy stability of scheme (15) | `theorem3_false`, `dlra_stable_of_invariant` |
| Einkemmer, Hu, Kusch, [2212.12012](https://arxiv.org/abs/2212.12012) | Thm 4.1 | AP with no hypothesis; fails on special data, and the invertibility used in the proof fails for r ≥ 2. AP holds generically, under aᵀVⁿ ≠ 0 and ⟨∂ₓρⁿ, Xⁿ⟩ ≠ 0 | `theorem_4_1_printed_false`, `theorem_4_1`, `printed_hypothesis_not_uniform` |
| Einkemmer, Hu, Kusch, [2212.12012](https://arxiv.org/abs/2212.12012) | Lemma 3.4, (3.11), Lemma 3.6, Thm 5.1 | Slips in the identities and in the rate | `lemma_3_4_printed_false`, `lemma_3_5_printed_false`, `lemma_3_6_printed_false`, `theorem_5_1_printed_false` |
| Einkemmer, Hu, Wang, [2005.06571](https://arxiv.org/abs/2005.06571) | Prop 3.1 | Fails for special QR completions, when the components are dependent | `prop_3_1_false_without_independence`, `prop_3_1` |
| Kusch, Einkemmer, Ceruti, [2107.07282](https://arxiv.org/abs/2107.07282) | Thms 2, 3 | CFL with λ_max(Ã); both hold with λ_max(A) | `scheme31_literal_false`, `scheme35_literal_false`, `scheme31_stable`, `scheme35_stable` |
| Ceruti, Crouseilles, Einkemmer, [2505.19929](https://arxiv.org/abs/2505.19929) | Thm 4.2 | AP of GAP with no hypothesis; fails for all time when X ⊥ ∂ₓρ. Holds when the two parts of the L-limit are independent | `theorem_4_2_false`, `gap_ap_run` |
| Einkemmer, Hu, Ying, [2101.07104](https://arxiv.org/abs/2101.07104) | Remark 4.2, §7 | Viscous stress of the isothermal model is ∇u + (∇u)ᵀ, not σ(u) of (2.10) | `remark_4_2_false`, `chapmanEnskog_stress` |
| Einkemmer, Kormann, Kusch, McClarren, Qiu, [2412.05912](https://arxiv.org/abs/2412.05912) | §2 | "At most rank r + 1" misquotes [61], which gives m + 1 for m Fourier modes; the example has rank 3, not 2 | `linearized_rank_claim_false`, `linearized_example_rank_eq_three`, `full_rank_le_five` |
| Patwardhan, Kusch, [2502.20883](https://arxiv.org/abs/2502.20883) | Lemma 7 | False for the order-two product rule; Thm 3 holds | `lemma_7_counterexample`, `lemma_7_iff`, `moment_sq_le`, `theorem_3` |
| Einkemmer, Hu, Zhang, [2502.08951](https://arxiv.org/abs/2502.08951) | Thm 2.2 | Exactness stated for Ȧ = F(t, A); holds only for F(t, Y) = Ȧ(t) | `Counterexample.theorem_2_2_false_for_state_dependent_field`, `theorem_2_2` |
| Patwardhan, Frank, Kusch, [2402.16746](https://arxiv.org/abs/2402.16746) | Lemmas 4, 6 | The slips of Lemmas 3.4, 3.6 of 2212.12012, quoted; Thms 2 and 7 hold | `lemma_4_false`, `lemma_6_false`, `Params.theorem_2`, `theorem_7` |
| Kusch, Sulz, [2610.11747](https://arxiv.org/abs/2610.11747) | Thm 5.3, §5.1.4 | Parallel TTN integrator with the printed block C̃¹_τ is not second order; holds with the assembled child value | `soLit_counterexample`, `soParTTN_global_error` |
| Kusch, Stammer, [2111.07160](https://arxiv.org/abs/2111.07160) | Thms 1, 2 | L²-stability under the CFL with ρ_min fails for variable density; holds for constant density | `theorem1_false_of_variable_density`, `theorem2_false_of_variable_density`, `theorem1` |
| Kusch, [2403.02834](https://arxiv.org/abs/2403.02834) | Thm 5.1 | Second term not divided by ‖Y₁‖ + ‖Y₀‖, so C depends on the solution; the squared-norm bound holds | `theorem_5_1_counterexample`, `theorem_5_1_variant2` |
| Yang, Yi, Yin, [2501.06145](https://arxiv.org/abs/2501.06145) | §2, C_g; Lemma 2.4 | C_g = ½ is false, since \|g′(0)\| = 1 + τ/2; with it Lemma 2.4 fails at τ = 2 | `not_Cg_half`, `lemma_2_4_fails_of_Cg_half`, `lemma_2_4`, `lemma_2_4_classical` |
| Ceruti, Kusch, Lubich, [2104.05247](https://arxiv.org/abs/2104.05247) | Thm 3, skew case | The truncation can cut a pair of equal singular values, so Y₁ has odd rank and is not skew-symmetric; holds with a gap at the cut | `Symmetry.augBug_trunc_not_skew`, `Symmetry.augBug_isTwistSymm`, `augBug_truncated_skew` |
| Appelö, Cheng, [2402.05347](https://arxiv.org/abs/2402.05347) | Thm 3.2 | Growth factor e^{αΔt}; the proof gives (1 − αΔt)⁻¹, which is attained | `implicitGalerkin_linear_counterexample`, `galerkin_implicitEuler_norm_le` |
| Snyder, Yang, Schnake, Schotthöfer, [2601.08882](https://arxiv.org/abs/2601.08882) | §2, Convergence, Error control | Thms 1-3 of 2410.18720, quoted: factor 1 − Lλ²/2, descent and stationarity with the batch gradient, constants independent of time | `printed_coefficient_false`, `fresh_batch_descent_false`, `not_stationarity_of_batch_gradient`, `not_timeUniform_error`, `expected_loss_descent` |
| Hesthaven, Pagliantini, Ripamonti, [2007.13153](https://arxiv.org/abs/2007.13153) | Lemma 5.2 | The "only if" fails when the velocity vanishes; the "if" holds | `lemma_5_2_converse_fails`, `lemma_5_2` |
| Bonnabel, Lambert, Bach, [2407.03373](https://arxiv.org/abs/2407.03373) | Prop 8 | Residual formula drops a projector; it overestimates by ‖UUᵀH(I − UUᵀ)‖² | `prop8_printed_false`, `prop8_corrected` |
| Naderi, Akhavan, Babaee, [2408.16591](https://arxiv.org/abs/2408.16591) | §3.3.1 | CUR step equivalent to residual collocation; the residual vanishes on the columns, not on the rows | `cur_residual_row_ne_zero`, `cur_residual_cols_eq_zero`, `cur_residual_eq_zero` |
| Meng, Appelö, Cheng, [2410.07465](https://arxiv.org/abs/2410.07465) | Thm 4.1 | Stability ‖Xⁿ‖ ≤ C‖X⁰‖ with a source term G; holds for G = 0 and with a source term added | `midpoint_forcing_counterexample`, `midpoint_forcing_global` |

## Loose

| Paper | Location | What is imprecise | Lean |
|---|---|---|---|
| Chertkov et al., [2509.15113](https://arxiv.org/abs/2509.15113) | eq. (4), Alg. 1 line 16 | Missing normalization by the number of probes | `matE_probeEst_ne`, `matE_probeEst_normalized` |
| Schotthöfer, Yang, Schnake, [2505.08022](https://arxiv.org/abs/2505.08022) | §5 | R(USVᵀ) = R(S) used for non-square U, V | `robustR_mul_mul_ne`, `robustR_mul_mul_eq` |
| Kamalakara et al., [2209.13569](https://arxiv.org/abs/2209.13569) | eq. (1) | Quadratic term of the factor update | `factorGD_paper_formula_false`, `factorGD_product` |
| Séguin, Ceruti, Kressner, [2309.06125](https://arxiv.org/abs/2309.06125) | eqs. (13)-(14) | Forward Euler substeps differ from the printed retraction form | `eulerKSL_ne_kslRetr`, `eulerKLS_ne_klsRetr` |
| Thomas, [2607.05872](https://arxiv.org/abs/2607.05872) | App. A, Thm 1 | √(2r) is the maximum of the chordal, not the raw, distance; v* needs uncorrelated coordinates | `raw_distance_exceeds_ceiling`, `vStar_requires_uncorrelated` |
| Schotthöfer, Klein, Kusch, [2506.17475](https://arxiv.org/abs/2506.17475) | Thm 4, proof | Statement true, proof's stationarity claim wrong | `naiveFlow_failure`, `naiveFlow_not_stationary` |
| Matveeva, Katrutsa, Frolov, [2508.21106](https://arxiv.org/abs/2508.21106) | eq. (4) | Exponent must be −1/2 | `eq_four_false_as_printed`, `eq_four_corrected` |
| Gural et al., [2009.03887](https://arxiv.org/abs/2009.03887) | App. A.2 | Sign of s₂ in the minimum variance | `appA2_min_variance_formula_false` |
| Zangrando et al., [2305.19059](https://arxiv.org/abs/2305.19059) | Lemma G.3, Thm 2.1 | Lemma G.3 holds for a basis fixed before the batch; the proof of Thm 3.2 uses it for a batch-dependent basis, where it fails. The proof of Thm 2.1 freezes Qᵢ, which needs Qᵢᵀ Q̇ᵢ = 0 | `lemma_G_3`, `lemma_G_3_counterexample`, `K_eq_iff`, `thm_2_1` |
| Kusch, Schotthöfer, Walter, [2502.03006](https://arxiv.org/abs/2502.03006) | Thm 5.9, proof | Identity P_Û∇ℓ = P(Y)∇ℓ fails; the conclusion holds for exact gradients | `exists_leftProj_ne_tangentProj_of_capture`, `abcPsi_liminf_tangentGrad_eq_zero` |
| Schotthöfer et al., [2205.13571](https://arxiv.org/abs/2205.13571) | Thm 2, fixed rank | Scope of the statement | `fixedRank_loss_increases` |
| Savostianova et al., [2306.01485](https://arxiv.org/abs/2306.01485) | App. B | Leaky ReLU and hard tanh values | `condOn_leakyReLU_lt_appendix`, `condOn_hardTanh_ne_appendix` |
| Einkemmer, Ostermann, Scalone, [2206.09374](https://arxiv.org/abs/2206.09374) | §3 | 3D basis function U₅ should be v² − 3 | `fixed_function_not_orthogonal` |
| Olikier, Uschmajew, Vandereycken, [2306.00897](https://arxiv.org/abs/2306.00897) | (3.29), min-max | Holds from half-step 1, fails at ℓ = 0 | `als_counterexample`, `als_convergence` |
| Kormann, Nazarov, Wen, [2606.31662](https://arxiv.org/abs/2606.31662) | eq. (3.7) | Sign of the primal | `printed_formula_3_7_false`, `prop_3_2` |
| Hu, Wang, [2112.02695](https://arxiv.org/abs/2112.02695) | eq. (5.7) | Needs c√(r − r′) < 1 | `eq5_7_needs_condition`, `eq5_7` |
| Baumann et al., [2411.06844](https://arxiv.org/abs/2411.06844) | Lemma 2 | Needs the unlisted quadrature normalization | `lemma2_fails_gaussHermite`, `lemma2_normalized` |
| Ghosh, Nguyen, Kümmerle, [2511.04485](https://arxiv.org/abs/2511.04485) | §4.1 | Limit of the reweighting | `not_tendsto_reweight_zero`, `tendsto_reweight` |
| Peng, McClarren, [2011.06072](https://arxiv.org/abs/2011.06072) | (22)-(24), (25), (28) | Misprints | `LOData.isFluxStep_iff` |
| Peng, McClarren, Frank, [1912.07522](https://arxiv.org/abs/1912.07522) | (13), (17), §2 | Index misprint; the evolution need not stay in ℳ_r | `eq13_printed_false`, `RankDropExample.rank_drop` |
| Ding, Einkemmer, Li, [1907.04247](https://arxiv.org/abs/1907.04247) | Thm 3.2 | Needs invertibility of I + (Δt/d)𝓛 | `theorem_3_2_counterexample`, `theorem_3_2` |
| Einkemmer, [1804.04561](https://arxiv.org/abs/1804.04561) | (23), (25), §4 | Signs; constants; the backward S-step diverges, so the constraint is not enforced there | `eq23_printed_false`, `eq25_printed_false`, `lConstraint_printed_false`, `sConstraint_printed_false`, `sStep_diverges` |
| Einkemmer, Hu, Wang, [2005.06571](https://arxiv.org/abs/2005.06571) | §3.3, (3.45) | Orderings beginning with L or S-L; (3.45) is a two-step scheme | `sec_3_3_false_without_rank`, `sec_3_4_sub_midpoint` |
| Einkemmer, Lubich, [1807.02338](https://arxiv.org/abs/1807.02338) | (3.14) | Sign of Eρ | `printed_3_14_false` |
| Baumann, Einkemmer, Klingenberg, Kusch, [2307.07538](https://arxiv.org/abs/2307.07538) | Thm 1, proof | Rate called strictly negative; it vanishes at equilibrium | `energy_rate_eq_zero_at_equilibrium` |
| Li, Jiang, Zhang, Xiong, [2602.12337](https://arxiv.org/abs/2602.12337) | §4.2 | Range claims need (Vⁿ)ᵀMQˣ1 ≠ 0 and (Xⁿ)ᵀD^{x,+}ρ ≠ 0 | `ap_fails_of_degenerate_right`, `ap_fails_of_degenerate_left`, `formal_ap` |
| Einkemmer, Hu, Ying, [2101.07104](https://arxiv.org/abs/2101.07104) | (4.19) | Missing factor Δt | `printed_update_iff`, `forwardEuler_momentum` |
| Einkemmer, Lubich, [1807.02338](https://arxiv.org/abs/1807.02338) | §4, example | ⟨X₁¹, F(f)⟩ is −⟨X₁¹, ∇X₂¹⟩S₂₂β₂; the example needs S₂₂ ≠ 0 | `printed_identity_iff`, `sec4_counterexample`, `compatible_of_S₂₂_eq_zero` |
| Einkemmer, Ostermann, Piazzola, [1902.00424](https://arxiv.org/abs/1902.00424) | (2), (16), §6 | Sign of j; index of d³; sign of the spectral Poisson solve | `gauss_not_propagated`, `predictor_gauss_of_continuity`, `sStep_printed_false`, `poisson_printed_false`, `spectral_poisson` |
| Patwardhan, Frank, Kusch, [2402.16746](https://arxiv.org/abs/2402.16746) | Thms 3, 6, proofs | Invertibility assumed in Thm 3 impossible for r ≥ 2; Lemma 1 in Thm 6 inverts Ŝ^rem = 0 | `Params.theorem_3_invertible_rank_le_one`, `Params.IsAdaptiveStep.Sr_eq_zero`, `Params.theorem_3`, `Params.theorem_6` |
| Koellermeier, Krah, Kusch, [2302.01391](https://arxiv.org/abs/2302.01391) | §5.1 E_cum, (15) | Unsquared norms; shifted indices make G₁ anti-dissipative | `Ecum_printed_false`, `Ecum_eq`, `G₁printed_singular` |
| Einkemmer, Joseph, [2101.12571](https://arxiv.org/abs/2101.12571) | (15), §6.1 | Transposed index of S⁻¹; exact integration by parts in v holds only up to boundary terms | `eq15_as_printed_iff`, `not_velIBP_const` |
| Coughlin, Hu, Shumlak, [2311.09425](https://arxiv.org/abs/2311.09425) | Prop 4.1, proof | "Strictly hyperbolic" should be "hyperbolic" | `fluxMatrix_not_strictlyHyperbolic`, `VelocitySetup.fluxMatrix_hyperbolic` |
| Ceruti, Einkemmer, Kusch, Lubich, [2402.08607](https://arxiv.org/abs/2402.08607) | Remark 4 | Constant 1 in front of hε_r; holds with 2e^{Lh} | `remark4_constant_false`, `norm_bestTrunc_near_le` |
| Li, Jiang, Cheng, [2412.09400](https://arxiv.org/abs/2412.09400) | §2.1 | The hard-threshold argmax need not exist | `hardThreshold_argmax_counterexample`, `norm_sub_hardThreshold_le` |
| Li, Jiang, Zhang, Xiong, [2607.27736](https://arxiv.org/abs/2607.27736) | Lemma 10, (25) | Constant 1/3 needs ∑ wⱼvⱼ² ≤ 1/3, not only normalized weights; Prop 1 holds | `lemma10_third_needs_moment`, `prop1` |
| Sui et al., [2401.10341](https://arxiv.org/abs/2401.10341) | §4, SO vs DSO | DSO = 2·SO + const, so the stated advantage of DSO is one of weight | `doubleSoftOrth_eq` |
| Kazashi, Marzouk, Nobile, Zoccolan, [2607.27432](https://arxiv.org/abs/2607.27432) | (38), (40) | AᵀC for CAᵀ | `printed40_not_hasDerivAt` |

## Unresolved

| Paper | Location | Status |
|---|---|---|
| Carrel, Gander, Vandereycken, [2203.08455](https://arxiv.org/abs/2203.08455) | Thm 3.5, eq. (21) | Signed product for n ≤ k; the truncated reading is proved (`thm_3_5`); the signed form does not follow from (15) at n = 1, k = 2 (example in the same file), no counterexample for the algorithm |
| Chertkov et al., [2509.15113](https://arxiv.org/abs/2509.15113) | Thm 1 | Unclear whether the bound is for one run or for the mean; the mean is proved (`theorem_1`) |
| Xu et al., [2609.32615](https://arxiv.org/abs/2609.32615) | Thm 3.3, gain | Compares two upper bounds; the actual errors go the other way on an example (`sdlrt_worse_than_dlrt`) |
| Zangrando et al., [2305.19059](https://arxiv.org/abs/2305.19059) | Thm 3.2 | Proved with a fresh batch for the core step (`thm_3_2`); open for a shared batch |
| Kusch, Schotthöfer, Walter, [2502.03006](https://arxiv.org/abs/2502.03006) | Thm 5.9, stochastic | Proved for exact gradients only |
| Olikier, Uschmajew, Vandereycken, [2306.00897](https://arxiv.org/abs/2306.00897) | Thms 3.7, 3.8 | Exact line search argument; proved with bounded steps (`riemBlockDescent_linear_rate`) |
| Baumann, Einkemmer, Klingenberg, Kusch, [2307.07538](https://arxiv.org/abs/2307.07538) | Thm 3 | Proof needs e₀ ∈ range V⁰ at the first step; proved with it (`theorem3`); fails for the sharp CFL without it (`not_energy_stable_without_e₀`); printed CFL open |
| Einkemmer, Joseph, [2101.12571](https://arxiv.org/abs/2101.12571) | §6.2, robustness | True as "no inverse of S" (`Grid.exists_step`); false as error bounds independent of small singular values (`rob_no_uniform_bound`); the paper does not define the term |
| Pagliantini, Vismara, [2308.16547](https://arxiv.org/abs/2308.16547) | Prop 3, hyper-reduced flow | Proved for the reduced flow (`proposition_3`); hand counterexample for the hyper-reduced flow, not formalized |
| Zangrando et al., [2305.19059](https://arxiv.org/abs/2305.19059) | Thm 3.1 | Stated informally; α > 0 fails at stationary points by hand; proved with α depending on the gradient at W(0) (`thm_3_1_uniform`) |
| Xu, Yaras, Asato, Qu, Balzano, [2602.06208](https://arxiv.org/abs/2602.06208) | Lemma D.9, proof | Positivity of the denominator derived only for G₃ ≥ 1 − φ′(0)/2; D.9, D.10 proved under it (`Net.lemma_D_9`, `Net.lemma_D_10`) |
| Hauck, Kusch, Schotthöfer, [2608.27749](https://arxiv.org/abs/2608.27749) | Lemma 3, proof | Ignores the truncation in the stage points (3b); proved with the truncation defect carried (`lemma3_Kstep`) |

## Statements of the open-problem catalogue that were false

These were conjectured targets of this project, not published claims. The original statements are
recorded here because they were false; the corrected forms are in `LeanDLRA/Corrections/`.

| Target | Counterexample | Corrected form |
|---|---|---|
| `tucker_dlrt_euler_local_error` | `tucker_dlrt_euler_local_error_counterexample` | `tucker_dlrt_euler_local_error_of_nonneg` |
| `ksl_constField_increment` | `ksl_constField_increment_counterexample` | `ksl_constField_increment_of_comm` |
| `simpsonIncrement_error` | `simpsonIncrement_error_counterexample` | `simpsonIncrement_error_of_endpoint` |
| `oneSided_lower_of_rankOne` | `oneSided_lower_of_rankOne_counterexample` | `oneSided_lower_of_rankOne_of_two_le` |
| `drb_energy_uniform` | `drb_energy_uniform_counterexample` | `drb_energy_uniform_of_nonneg` |
| `distLR_two_mul_le` | `distLR_two_mul_le_counterexample` | `distLR_two_mul_le_of_nonneg` |
| `normal_lowerRank_le` | `normal_lowerRank_le_counterexample` | `normal_lowerRank_le_of_lt` |
