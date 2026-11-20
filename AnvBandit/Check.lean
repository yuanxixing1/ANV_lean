import AnvBandit

open scoped BigOperators

#print axioms AnvBandit.psi_anti
#print axioms AnvBandit.psi_tendsto
#print axioms AnvBandit.DecayModel.prefix_bounds
#print axioms AnvBandit.DecayModel.Phi_tail_bound
#print axioms AnvBandit.DecayModel.DeltaMin_pos
#print axioms AnvBandit.batch_inequality
#print axioms AnvBandit.DecayModel.syncAlloc_sub_serialAlloc_le
#print axioms AnvBandit.Hxi_bracket
#print axioms AnvBandit.two_rdelta_lt
#print axioms AnvBandit.DecayModel.lemma_A2
#print axioms AnvBandit.DecayModel.not_selected_of_ge_mk
#print axioms AnvBandit.theorem_4_1
#print axioms AnvBandit.corollary_4_2
#print axioms AnvBandit.proposition_A_5
#print axioms AnvBandit.theorem_4_1_timeorder_Hxi
#print axioms AnvBandit.theorem_C_4
#print axioms AnvBandit.proposition_C_5
#print axioms AnvBandit.lemma_B_3
#print axioms AnvBandit.subgaussian_centered
#print axioms AnvBandit.hoeffding_dev
#print axioms AnvBandit.measure_bad_le
#print axioms AnvBandit.union_bound_arith
#print axioms AnvBandit.concentration_event
#print axioms AnvBandit.DecayModel.theorem_4_1_explicit
#print axioms AnvBandit.LdeltaStar_eq
#print axioms AnvBandit.DecayModel.deltaStar_mul_le
#print axioms AnvBandit.proposition_B_1
#print axioms AnvBandit.DecayModel.Jlam_nonneg
#print axioms AnvBandit.combine_timeorder_bounds
#print axioms AnvBandit.proposition_A_4
#print axioms AnvBandit.expBench_le_greedyVal
#print axioms AnvBandit.greedyVal_le_expBench
#print axioms AnvBandit.exists_sched_with_counts
#print axioms AnvBandit.syncExpVal_eq_sum
#print axioms AnvBandit.occ_image_eq_range
#print axioms AnvBandit.measure_adaptive_sum_ge_le
#print axioms AnvBandit.measure_adaptive_abs_le
#print axioms AnvBandit.measure_adaptive_abs_le_sampled
#print axioms AnvBandit.hasCondSubgaussianMGF_neg
#print axioms AnvBandit.proposition_A_5_traj0
#print axioms AnvBandit.proposition_A_5_traj1
#print axioms AnvBandit.rho_sum_le
#print axioms AnvBandit.regret_conversion_lambda0
#print axioms AnvBandit.regret_conversion_lambda1
#print axioms AnvBandit.J0_eq_serial
#print axioms AnvBandit.J1_eq_sync
#print axioms AnvBandit.Vstar0_le
#print axioms AnvBandit.Vstar1_le
#print axioms AnvBandit.lemma_B_3
#print axioms AnvBandit.dF_gt_point_one
#print axioms AnvBandit.Inform_eq_univ_of_increasing
#print axioms AnvBandit.subset_Inform
#print axioms AnvBandit.Vstar1_le_Vser
#print axioms AnvBandit.Vser_le_Fkstar_add_Db
#print axioms AnvBandit.le_Vser
#print axioms AnvBandit.measure_tau_gt_le
#print axioms AnvBandit.integral_rpow_tau_le
#print axioms AnvBandit.measure_complete_gt_le
#print axioms AnvBandit.measure_tau_gt_real_le
#print axioms AnvBandit.ReachData.ofIrreducible
#print axioms AnvBandit.gen_saturate
#print axioms AnvBandit.blockState_univ
#print axioms AnvBandit.blockDist_blockEvent_ge
#print axioms AnvBandit.Inform_unblock
#print axioms AnvBandit.lemma_B_4
#print axioms AnvBandit.measurable_tau_real

#print axioms AnvBandit.integral_rpow_tau_le
#print axioms AnvBandit.EtauPow_le
#print axioms AnvBandit.M1_le
#print axioms AnvBandit.DP_bounds
#print axioms AnvBandit.Pbeta_le
#print axioms AnvBandit.EminTS_le_Pbeta
#print axioms AnvBandit.Abeta_le
#print axioms AnvBandit.lemma_B_5
#print axioms AnvBandit.permSet_disjoint
#print axioms AnvBandit.sum_permSet
#print axioms AnvBandit.sum_le_Wkappa
#print axioms AnvBandit.GoodRun.pair_budget
#print axioms AnvBandit.GoodRun.N_lt_mk
#print axioms AnvBandit.terminal_budget
#print axioms AnvBandit.lemma_C_1
#print axioms AnvBandit.lemma_C_1_count
#print axioms AnvBandit.GoodRun.AplusCount_le_mk
#print axioms AnvBandit.batch_divergence_ge
#print axioms AnvBandit.batch_divergence_le
#print axioms AnvBandit.GoodRun.team_pos_budget
#print axioms AnvBandit.node_selection_bound
#print axioms AnvBandit.subset_selection_bound
#print axioms AnvBandit.proposition_A_6
#print axioms AnvBandit.lemma_C_2_traj
#print axioms AnvBandit.lemma_C_2
#print axioms AnvBandit.abel_bound
#print axioms AnvBandit.lemma_C_3
#print axioms AnvBandit.topArg_max
#print axioms AnvBandit.lemma_B_5_stable
#print axioms AnvBandit.lemma_B_5_all
#print axioms AnvBandit.Kbeta_summable
#print axioms AnvBandit.summable_shifted_pow_geometric

#print axioms AnvBandit.measure_Complete_compl_eq_zero
#print axioms AnvBandit.measure_Complete_eq_one
#print axioms AnvBandit.sigmaFrom_le_sigmaStep
#print axioms AnvBandit.min_sigmaFrom_anti
#print axioms AnvBandit.Vpot_singleton
#print axioms AnvBandit.Vpot_univ
#print axioms AnvBandit.Vpot_le_M1
#print axioms AnvBandit.Vpot_anti
#print axioms AnvBandit.card_sdiff_le_Vpot
#print axioms AnvBandit.RunModel.holds_forever

#print axioms AnvBandit.infinitePiNat_map_headTail
#print axioms AnvBandit.stepMeasure_headTail
#print axioms AnvBandit.unblock_measure
#print axioms AnvBandit.unblock_preimage
#print axioms AnvBandit.prod_mod_fiber
#print axioms AnvBandit.pi_stepDist_pi
#print axioms AnvBandit.stepMeasure_complete_compl_eq_zero
#print axioms AnvBandit.sigmaAll_stepE
#print axioms AnvBandit.sigmaAllE_of_nonempty
#print axioms AnvBandit.Nat.sInf_succ_shift
#print axioms AnvBandit.VpotE_recursion

#print AnvBandit.combine_timeorder_bounds
#print axioms AnvBandit.DecayModel.hkappa_exact_le_coarse
#print axioms AnvBandit.DecayModel.sum_mk_le_hkappa
#print AnvBandit.DecayModel.HKappa

#print AnvBandit.DecayModel.ofPositiveCurves
#print axioms AnvBandit.extendPositiveCurve_antitone
#print axioms AnvBandit.extendPositiveCurve_tendsto

#print axioms AnvBandit.Ldelta_pos
#print axioms AnvBandit.legal_Hxi
#print axioms AnvBandit.nonneg_subset_budget_iff_exact

#print axioms AnvBandit.rH_eq_last_short_phase
#print axioms AnvBandit.reliable_phase_exact_budget

-- Exact two-element budget for weights 10,1,1 is 11, not the coarse bound 20.
example : (({0, 1, 2} : Finset ℕ).powersetCard 2).sup
    (fun F => ∑ k ∈ F, if k = 0 then 10 else 1) = 11 := by decide

-- Regression: the corrected time-order domain permits H=1<T.
example {β : ℝ} {R : ℕ → ℕ → ℝ} (h : AnvBandit.TimeOrder β R) :
    ∃ C : ℝ, 0 ≤ C ∧ R 5 1 ≤ C *
      ((1 : ℝ) + (Real.log 6) ^ (β / (β - 1)) /
        ((1 : ℝ) ^ (β / (β - 1) - 1)) + Real.log 6 + 1) := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C, hC, ?_⟩
  have hb := hbound 5 1 (by omega) (by omega)
  norm_num at hb ⊢
  exact hb

#print axioms AnvBandit.DecayModel.Bschedule_le_coarse

#print AnvBandit.ContactMatrix.ofStochasticIrreducible
#print axioms AnvBandit.ContactMatrix.ofStochasticIrreducible
#print AnvBandit.ContactMatrix.ofStochasticIrreducible_pmin_attained
#print axioms AnvBandit.ContactMatrix.ofStochasticIrreducible_pmin_attained

-- New verified modules: complete signatures matter in addition to axiom lists.
#print AnvBandit.ObservedPrefix.measure_good_compl_le_finite
#print axioms AnvBandit.ObservedPrefix.measure_good_compl_le_finite
#print AnvBandit.Execution.Params
#print AnvBandit.Execution.LocalState
#print AnvBandit.GoodRunOn
#print AnvBandit.Execution.run_congr
#print axioms AnvBandit.Execution.run_congr
#print AnvBandit.GoodRunOn.global_wait_cost
#print axioms AnvBandit.GoodRunOn.global_wait_cost
#print AnvBandit.IsExponential
#print AnvBandit.ExponentialDP.proposition_A_4_full
#print AnvBandit.ExponentialDP.greedy_policy_attains
#print axioms AnvBandit.ExponentialDP.proposition_A_4_full
#print axioms AnvBandit.ExponentialDP.greedy_policy_attains
#print AnvBandit.Vstar0_eq_n_Vser
#print AnvBandit.benchmark_public_sandwich
#print AnvBandit.Vser_eq_greedy_policy
#print axioms AnvBandit.Vstar0_eq_n_Vser
#print axioms AnvBandit.benchmark_public_sandwich
#print axioms AnvBandit.Vser_eq_greedy_policy
#print AnvBandit.PublicDP.W_eq_Vstar1
#print AnvBandit.PublicDP.W_batch
#print axioms AnvBandit.PublicDP.W_eq_Vstar1
#print axioms AnvBandit.PublicDP.W_batch
#print AnvBandit.Vpot_recursion_of_irreducible
#print axioms AnvBandit.Vpot_recursion_of_irreducible

-- Final original-model endpoints and their exact constructed analysis quantities.
#print AnvBandit.Main.actualCaps
#print AnvBandit.Main.actualEcost
#print AnvBandit.Main.canonicalContact
#print AnvBandit.Main.theorem_C_4
#print AnvBandit.Main.theorem_4_1
#print AnvBandit.Main.theorem_4_1_canonical
#print AnvBandit.ObservedRegret.original_theorem_4_1
#print AnvBandit.ObservedRegret.original_theorem_C_4
#print axioms AnvBandit.Main.theorem_C_4
#print axioms AnvBandit.Main.theorem_4_1
#print axioms AnvBandit.Main.theorem_4_1_canonical
#print axioms AnvBandit.ObservedRegret.original_theorem_4_1
#print axioms AnvBandit.ObservedRegret.original_theorem_C_4
#print AnvBandit.ActualExplicitRegret.actual_explicit_canonical
#print AnvBandit.ActualExplicitRegret.actual_time_order
#print AnvBandit.ActualExplicitRegret.actual_Hxi_order
#print AnvBandit.ActualExplicitRegret.actual_fixed_h_log_order
#print AnvBandit.ActualExplicitRegret.actual_sublinear
#print axioms AnvBandit.ActualExplicitRegret.actual_explicit_canonical
#print axioms AnvBandit.ActualExplicitRegret.actual_time_order
#print axioms AnvBandit.ActualExplicitRegret.actual_Hxi_order
#print axioms AnvBandit.ActualExplicitRegret.actual_fixed_h_log_order
#print axioms AnvBandit.ActualExplicitRegret.actual_sublinear
#print AnvBandit.BaselineRealizedReward.original_realized_regret_bound
#print AnvBandit.BaselineComparison.corollary_4_2
#print axioms AnvBandit.BaselineRealizedReward.original_realized_regret_bound
#print axioms AnvBandit.BaselineComparison.corollary_4_2
#print AnvBandit.ExecutionUCB.cooperative_choose_eq_min_argmax
#print AnvBandit.ExecutionUCB.baseline_choose_eq_min_argmax
#print axioms AnvBandit.ExecutionUCB.cooperative_choose_eq_min_argmax
#print axioms AnvBandit.ExecutionUCB.baseline_choose_eq_min_argmax
#print AnvBandit.GlobalRegret.goodLoss_global_paper
#print AnvBandit.ActualNodeExpectation.goodLoss_node
#print AnvBandit.Absorbing.weighted_loss_potential_branch
#print axioms AnvBandit.GlobalRegret.goodLoss_global_paper
#print axioms AnvBandit.ActualNodeExpectation.goodLoss_node
#print axioms AnvBandit.Absorbing.weighted_loss_potential_branch
#print AnvBandit.concreteKbeta_summable
#print axioms AnvBandit.concreteKbeta_summable
